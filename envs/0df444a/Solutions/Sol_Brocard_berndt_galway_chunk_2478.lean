-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2478
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T06:49:48.525321+00:00
-- url     : https://prove2.me/submissions/81eae9e2-a348-4278-9dc1-399adf7a46cc

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 445503597 ≤ n < 445683453 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 445504847 1250 445503597 445503599
    0x5030402040506010c022205130c032307060c02031b21030d02040603050708070905010c0b071205010609050102150f18030403060c09031703131103011509050708130c 73
    0x85440e80000f98040018586407011640030f9002c645041020540756542c000b85256680540c80e1a100d4141d103d404107581140c60b1405484070150103a0502010707000d0420b16240c00103141045840a003c0b0341110304aa80700c503603542c002031002e421144100d02c03178000c038040c8a41019410810010816008260240c1006000401031800600b0039a02c0f06500040c020b40003450654806000105a6500c000c1010b01d0841402812690000e14483c20f0100c41c1c00c0c1481580d03440b44055403480e40c0001507a48a445005050b5078201700c00b00c0b134001c06424040045511a80000c0660840b4001e03001c440f032103901034512014a0304e08841c009495108070340007440c241051804440c0e905410401d0341d01d407035260b448220035034050207282c0c0042056410308104001c0300c0038030700d401044d22011160542c104000d4409000c002c48201510b0010220305001040d5002e6115200015685085401070781d982d0035003501801c0102c401c2400320f40030700b000a803004c43d458401c40c180c56020010640d41 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 445506097 1250 445504847 445504849
    0xc0607090509090d0f02150408120f0f06040f0b0405091f140c341e0503031801180f050616051215040905030702310e0a0501051008061605030402 64
    0x40440c0f00320b40d07002c52041112011440340051320940c007560240c80d06507500d29240390543cadaa042c010f40315000301c4401c00b040201c501c041586942d0410012980805c800d80000800c0c0040c010505c3c0c2d49501c00e180009011750355a0015080718082d41d903a640300c5007110407007020340c22200010242c1c0b40a4100c00c0000b100300101d20024000d40a900c3d4400e0344401503400103001030144ca0100e8030000c038140140e901845105000300c04408400960900c8118066903900d40720b000103044a14076644c0c0c0c1c44d5906480c602034020072032101c941c480c41c0107440118181034504801c1448250742c90b000d4600410107802a50491003100d8000b529690700d0701011200d0904018801460314101c044032505004040c2d580380a08890b05000c0c50007944c445046004204c3c2508a16011603c00507a4482d41180002912070741039001d801600002581101880518240103100c00020401d5181c0030030000c1d0880d8000d9180c040d07881d23440c212500c079641d00d0f40200d0082c0403580e914012400c01d20000b001 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 445507347 1250 445506097 445506107
    0xa0b090127020408010e030c0f190305160209071710050d0210030f090804090b0405041119051002061006020708150a0f06090b0f060306100309170c0607090509090d 72
    0x102035510340c0d0043c079081e60f07424401d01310745054500340d02076040000c2c03508400303508000c0301c140c40904502401ca04100340c20f84910901c081100101800808078080c800c43e15130300d14040302284c0251603031555107082036004012660001031001c0b20038049000c615015000d0787c00030180d0320080d01c1c1400100d41a0200705004280d0600340040503250703500702c1c52941141c000c0c01100d5101c0d400854466080030601419202c60701e25441c0600d107072008100c0031441700703e446200d040302030710b080001540800d9140e0038005103401140e000300c4802050740000f5070006030140301c0d880300740d0071503003247d242d0ba0120380f41c814074410000709501c10380303070010f2110310050015000009218000b17162024a940c10059590b40d6004140c1c540c0e031a01000150705000555402c04c0c24201c0e03c0b5803031464804009401da031308084a0204040d618410f0104002d2600703040c40d50807003400700c1d40e038a8013a001c0c4900c0d640e5008403480d00014201010008042c10b003c03c119000360359402c060a102c0d08100c004440c = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 445508597 1250 445507347 445507409
    0x30e060906010b220e0f150901150504030c0b0d2702061812100b030703080708090303070c08010e070b0f191404080c1e09070305070c02060d050a0b0901 67
    0x2200e43d4040c0404042e0010044c140005201c8410101d90a1410083c84d0210440042a06040c2d5808102c54220b958496200c241954018200e001c0185e0703e014040340e880c00b807608010f0006075100404100c40b5142d801904508a01450910149110f62055000010103151070040030f031044411100618101c00a402c4561030104030301500d42044d0005040781c0e40000182500c0c0c0c10824200c080c40030103000350005200d00b6002007580e18610340e503080b51032058400c050309422000c64030300100d82e0144220f4020a41000348d00401c6912095483d0080406551410302d074820040c00003001d0b0401c030252204100d1084240381055034504100e55401207101e020003c110701d0540c9800345001c1c80c00030780080d00d801c1d40184541e5100c01c09000807c1d481600d440b640e1152006202100c0d0f0710500340c6584a001460041125250410b095440d00318204000390702440103d21020b481039607a024030b12440fa0f8800c1888030440380b100780042040203000385050304400b005090400d0010300c08a070 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 445509847 1250 445508597 445508617
    0x2619020c280804090e010c0905210f01020f0d0c090f051201060e0720062505090a0909020f0d1707050c040207060c170c04050906010e031c030e060906010b 68
    0x8041880d591400c0b46640b054004107407160361038881541204d824840c140350714502c2d04040410360308220005503840700e84607410380d044c2d480e0f501502e800c500070300221040041203c000d40d01c90b00b649000b075800d41c0100290142e05850310044100c60b5101c2c500c60011110b10886220407070b420711003405820101104042d400f50b403a504001120592070f00d10b5441221702c0d598520b1100244500030303d00403621580b0345526840001072000c0080d001c560128090a081120f50f8002d04811080c0d540d401000c84450307106103441000111026141c1000708201d1080b030358010040c0d9640704000c2e401101442c044c1082d40645d038209515101c4800400c03015004000b00d6031946400780c00582664001e1804a03001900c6101d0225165005a80c03040c0780f8400c84000100e600d004070601c50180170364032849102d0301d00d10001c145164020081400c2d154005000e455010290410312040107024400d0710300028a8a000c4501070080407603082d008814250180031664684a290380d1181c00c1006e9135 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 445511097 1250 445509847 445509913
    0x90105010e031528051603021b030c030a0807030920130603080d110703020615121b0f010c0206190908150601020c0604051c032619020c 60
    0xd922980080310020310a20081381e40074902a90031030080c12120000d40101e4007035040c401809130740c4032a0310000e600303091030346001030701ca80d65640c00442c5040480101c11071400002110202e10728044002e061030a00b07500c1d94040b80c0c441e0801141291401000504010440071030744001e0f148038000c800822000402c01010341d07003240c484c2e40403108243c0c07048900100010380504282014042c103600c4405003071102c0d0908490f44c5000c3d440c0c4a008001c202c808046c804400010354444094100c1c2d034961404460840076020f0041e000400c500c0c181c1b510600480030540c02541c4250701d00900c00303034054425410000d0040d501d842d00c1504101c1c08040c82518400490404003c200d40d09402c04011022803403410440006030410852070500f5025190420040c4003985401d143d00500441c00801d011520302c150608035202c0c907a801071104064000588198004107404150340501003000507448500450100d18040b48107109035400170780c000c0f0040c0000c00c400e42040000740d150000d41 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 445512347 1250 445511097 445511113
    0xc090c09011d1e090f0402150a0201020d090b04050c0603010f06080604020408030a05070605070305150906130509010c0e0409030906080a020d02030c0409051003081801030204080a0308010501021b090105010e03 92
    0x150405007110f6188a448440302e5002071074a01403600c5504103200039103901c1c56051907004075010191460006190120001c0d215411901c01d40c1213801050110310100320003d268070b006145a0800c0e5000e66891050503260743c00c500d408000c4904a4500e8103507034a10600d00f1409690b1001c0043c03090b58415403c2c00300045110050004004903109035032829560580352821030101c3e0405401ca0040600c1c0904200302608044d01d5100440000c454100e5560b480c4130004021a0040505503140d0b401c2a09001c074540c0150800c802da9840e80d1600488602000b040c0310886607a8400900055400f4a00b0480305003e4051550010545040945032035040c203d131009980c01901c000c50542d8002908200140044c0305480c0c125981c13030707004481c891460300d07900340d076004022207250034651200100c010390b07001354115801081c6060907030304290424280604845070901c5111701601030724142c10580c4100f101040c082c000018075003a20341c3d003000c004403604c03a01880030a0f014495002 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 445513597 1250 445512347 445512349
    0xe040f060503280209130309080106080c1c060f0f06080102130608040c0e07050a080601180603020313020312070302010e07080a030c020d050f0105011a1608070c05100e030c090c09011d 81
    0x2c5c605101e08100310780780391444020318009100104950104105034906039050112100100d500c042e1903208898540e414481c0214000200c281c40800401051420f00d007600203120350b070040000307501e21410800410b0791351a074690030703807154641d042101c61402e401404224001c4825070341150080744803052583d141c0600c2d41034a8816602000030440200740b00b8003095010b541d03964448401c0c45c100c403600d910f010800c19800c4490192000349a0040006040c4418001080100070303001012103e0700c01c0c0712008140c840e8050141036006500700f004060b201030b4005035520484400c0c40c001c2208010702d4900301e50280707228400305d80c030150420b5180041041004240040c1c1d250100010b400d524209450002401080c4000c0c50300e0b0003444048590501281e4840015400c1240282e039140d003860045c00b0304845030441a07008008400c24140e13968020000c0142500640072550802802410080b0010045511404e5080200070354852948144403003250829004901410300311804 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 445514847 1250 445513597 445513609
    0xa270305070c06092601110a0315090e070608040204020f2b060b0a18050402030f0403080604060b160c0e01080d0914010206071812030e040f0605032802 67
    0x1500000c801082450a0014042880d030061072141810f81106140503144044500d01508a8810a84034003039140711032429001094a4041070702402e9845506030703400b4009105002d8060026074409001082c041e0081c8103030b07048401c01c4002441e80514000c01100c41000041040f6007054017030201403002013214003e071101e51340341303004060001035174048801050484118850001c1c14403000300f000711141c1d030454601070140d01d030104601042d9010b1031034185955101d01e410a20010801800c020b0350500d01d4007840c801c0d50342d0310303854580ca82000240c80c064001da001c00d010411007000d0120303586025030255032154920307074021a175400522840e030b20240c0c4461040d401c90b0030440c2c42d00768024940d1020308110019241d8480d4a100000d50740c04008000c602846158240d42c0310015917210050010b1243c03d0f02444418001c0c0b5004205d0b1602e401d95a010300d040400c1c0c1441d03144039000300e03010f8030320207001440081120004040c2c03652040e1082d4003044c60501405000d40c03214 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 445516097 1250 445514847 445514921
    0x70602070b04020405090a1e050c0a08061b0712030507110607030f1811060f0c101b1e030b0d050a050f0f0601080d1206050d060c020d05040605030a 65
    0x88074001c600b071500c0d0040c0026540020904080d540250103444001050002c002d13244040842c48000081898036245207480c5040d00015480080d508000541c01000100c07188503409400250f000b602c03038048400c070180a8a20010460900c07441700440042c0300394081c540c0030045107070850f81c00480056960900c1016141e482c0040d4071100d501006482c00c3c014072400000381c56003510144415110141802c0170404158801d074800107852041c0f41032a0155041c00c00300009941c4102c041ca80320714000c22101e000e02a54241980900c00031500036004541041d00c00b440c400c040e60102d4408030014000340d0003081e030058005c11030f180815420004502124814002801800c543e2004d1514280b40120012090341c04a801400008808181216841d90904102040803003250190000d0302076070b0806900280c0c0358a201060000c01d4010502d1403006400303803042622542d0040703425200300d02a0f000450b9040001c07800d0003d0075481840c45e58010041c2d4802115100c459161040e49 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 445517347 1250 445516097 445516103
    0x1c081302120c1e1e15040f031a010605032e0b07150509030a032a0e040e01050603030a050d060302030d11240403030b0a030c090c1d010c080f07060207 66
    0x300000c103441c0c1029901c1043d200098241da0710040f42890005500c41c401c1c00d00141c0b80b4071250791000454680400a078108800c929005441e0394582020702c0b01c0c00b41512041e43d0058002c1884164401e001200724161681640c41914655034044441e5030351411681f104140300c07152801c4e0000d84e241e519001d0103841d42c18200707650b07409142414204a124014441c0d0301c40d1800d006c5c41410b00c0c000049580001440c180851010341c580f140d81098401201c150722181c0c91803200003020703980302d4003890780038500700d1382007041312a10401c903400c0f200b04a03105501a401080f0000f5154080c2000d8101100540d80105405072241d022a0608200002c1000411029248a01c1c004014003508070700950507014503403804004107900d41002c9000c0d00240030b06a07541c07541d651585a1241d410701070760304100d089856603a10544030303005020508003000000c014080380e403500c440002c5070311000c10f0140e4805000d02c05946074110264000d443c0e22054900410643c800114a8000340c0034140c0 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 445518597 1250 445517347 445517353
    0x30a0804140f06120712060e0106032307080121150b0307090e0a06020c0319051309090803010302010513210606060c0b19020d090b01030309081c08130212 68
    0x5000a10030b442c0005034030b15119000510100003180c8400300629806103003464803600010202c1800e000910094001d40c00f0949402d00200351960107070400c1d5003112184ac4c01054a501c2c4003640b51007007105550719000500d030903004000c500d01e00d664440202e21240a44005903009548031600e0005107403086c0c90302610b82e07112000b0752905010148c01000708070000d000110b00c0c90101a220005c3e90740081c00c459010030341c0c0b010700c0410019260341e4040507151000400c0ea8140150580d0008403441254126448001c1031081d12802682c10160f482428241164256401556590031601c0c217001d20b102c0c08280090302c1915141d01c2954080d02403050b4900c070916050250507148217400800910014108503070004000160242d840614880314070032164501c05054040c1c0300380c030f102d54003c1c1e0800101c0003d0003041d00d6024100c901c40e4940d0902c6a070744050598449601d03c42001201a0510303460900301d0048000640c080c40c1981c00031418049a400034030460382050b0780b2101c0758 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 445519847 1250 445518597 445518629
    0x6090507080a08040603020a050f0a0e090606090102030d052a0c060709050d0212010b1809011413200d06020304260a0c02060421210914030a0804 64
    0x115040c88a10068002207000d01071105a076164250244601c0c03041d4010160f0010320f1004180c0f03d40d00f55081100d00d1002d5a584400441c002490304004101d6140716000105c040b074000d1406000711b444030041a00950300b0400208441d00003001c0051003400c010020321800d60281504600c1c2c041403000301e004894a90000c2c0001034076040000740000188418040e0611443c2c0c0e6034001c21129950449600c804030240000c280c0c00362907000306242c0c201041a000400d4440c4050385140b24404140003001050781c100d4900d0b078003520a88224801300c0564000c41c010a4080c051034a00c050404980b18400203000701040155080f00000c0e5a459804030a100401507408801c0260303a0508001040300c011350302c0c180481d03101700071405090014042d69001151500310941d0010300264a91200d07102e415602603c04010f248011150900124425588086070204c4210f03440401c0d5110801c082c108400c4184044400b0380055151040503803540002c1e00c10001800900884c0d1801c000304 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 445521097 1250 445519847 445519853
    0x1208040f0620030405090118091b1701050606070b040614010e070e0901030b1305151e0912031605070203061f060c020607080a05070606060f080a150311041103040609 73
    0x488108039400180e4101300030801040d170300d407188035055500c0d102c5a0118008480e040c01c00506a50305d0051202d44d01102c0b642060141d044054200d070168014071144500c62040c0340d00700d0340d080b600303103a1040f000c4c04014041008030310002d6000e4400d50001582d0406803c0c0c1d011925026485003038020780e02d00420220550041a001c0078000554008029506554519041140c02808400404110400f0a040c4502040100340b9251303601902442801d0100c00c4d181d820500c089409000215840842c0e46000009441050b50701540243c909540714410040354041d62078102008220301488002c02607601800914040c0c00d050b408044007180082004074107004e150b00020601414404400258440500319034101d41c0c80509580d840c08000ca003910382d40151304026003c5031406102050035138000c40700e2a41d41610f03407555081036072081c00130b4040d1030703c49401c50110030081030708000142c060040d01c184e460000308041180c1ca200c43d00400650001c1f2815180161140e8032032040c = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 445522347 1250 445521097 445521137
    0x306040e03070201020a1106130b0d150f260610030b0105010309020f13110a030204090501230d020a1a030609072607090f06050c060108161208040f06 66
    0x92160140c051401d00c2071070b8001070f40b1034034088009020712915810351030f0141c2e5100100d94003c01038444d28442c0701d84030010f101240d0000645140b030540742c50707203820913810820701102c1101d040c00e1000303010300c0c02c02e083e4a140c4801664240094120050001c140c4803040c45442d00c02d900508820342003034a18100700d120382206901c404d052503d011020000b5031901006c00b00d42090980d80300c90031840321042d4500410f100880b1403101a00032545015482c0d05400500448107802c03c1444a643c980018a07070f60448004c80006130040b51000007000c0c1821184402c609000614113491140d40c0e41005801c000d051440c0c0c0c3d04044000100010741c50589d0a503a0041c646d49441340300c404102504028200b049544645101d14000015240c98410103140024005511040b400190303504006889500805401243c6010b41030012881d803e00068112200d000c0c00c0400980a01d803004184298a000409444007401040045041d08400c1007190084c041d40d600d8003051169400e070408 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 445523597 1250 445522347 445522361
    0x1802010f0908030f03100b0a121b050405091b0a0c03090906050d0f1104022107080415020a12020c0d02060a15030605070216080c0a050102031306082208030604 70
    0xc18040000340034408071800000f42c0b140101d20b00c038010b96079202c0841d0908150700359805550b0102001425490150b84558194071800842005100406a10329107850198040c41d041000400611081280d03160a09035950400301a04041d904905003800b03041c0190322510501011a450104800415511010b1340c0000c02005104000b4141044001128691011170252000c0540b13042d180502c01c1803002011256801081150348407100c1c44100180d05e0031000281e1b80c804440300040320a4020120944a15070201009081c002d0110010000750407880c2c40504012182e585000880b0304c510042c0000038548c4020311042101e0707900285819802408002d0f80d60500850001500f02da083e10f2082d0307540310358081065503451408034a030080020851507489850300000498000104d0200d82150f800e4801200c2d40c0d072500016a503074407400c40c250310b90f00d1004000b0000396204800203500080140c050b20000340610130039240e076404104041c0c0b00c000d0000180080b519161180300 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 445524847 1250 445523597 445523627
    0x5180f090411010908060c030109090206121003060b01020a02100813050f03040905010b0c0307022716030507020127050a080408060901050703480306030506070801030c17030706180201 81
    0x241b5180150140035280010311400c11429200c100a030115a602415181404011642003880e031501e00520f8100301c82511040c2c405a15101042aaa504c00b00307008807096000303025810300140c510b10417210018000c1004520162560880002030814014000750032910030003107440e0750800703414100b100c206900c04007000f542080703207951804000c800d40395425011101044516086010240700d001000726032001d00e041300e820010b41001a400030b00c21850039960420107691614802d070308950740404404481000c1907180c6503d00c0541c4501124035124009a4018030150340e84d09007644c025401031084d54000e8030405c4141b1800348615a40f0001d90b00e000d11100c584911860b0322800d020b130011180d00324400306510f16030b212510b168aa130174540c0c20300502c40480314004000b0003040c0001c9406d4007803c40460540e901c51001281aa03400000c1030184078644440040d904200f82615421408180300320008170b483d611800401c102513214070454030140340700042c8130041c156208 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 445526097 1250 445524847 445524853
    0x21070906091a12070314070509040602181c17040e070807110307031d0102070b0d0905061015051b1005090610060f05130e090705091605180f090411010908 68
    0x4104000300000c4c2c050112900100361512290070300342c1d07850501c2c120790032031500010208184020080540d00520206404101c44442034120705c0801c00601e0424414241001d4050150004208055181e080303a260000c1c3d40d078030f401d0340c070494140c41d20021501000407e00120030062442d8100d82d8910381030340a00069890201c0301d6901401130358000e080d100070240c1c1203034100c8542e4000c00110010705030341d910340c6460b07080c165142c40103000394100454050041074049071140203034065420940b2040a180d40c1c401d100381108540580140005004915a004207049401020b0105000040d40c1c0d5501003050b240c0340108a150120182c1100401c4240c072200b0045680d00254240d20100e4500d819980d844038100014020a01900004a00b44941c814003d0500d40015000d00b00d50040d03421a0241d69050b1000c054420704003659004900308010a680403c0d0b100b400714444000200800e07107100b044800700382000403c9a08588000080345112003d45e00004c1140040843c0001 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 445527347 1250 445526097 445526119
    0x90c17010b04031707020409051219091a0304021503040623040506010303030c090e10050111190b06061c050f2409070c05030310050103180221070906091a 68
    0x142e885184d4074844441d0300e400d01043c10703c2107541c1c5800180001c0c1e0407004603003070100e00c01c07505074255000300c04000c0f110002101c0701580c00c0c010201c0c4030444215540d0398072a0f5000a4580d0000da000510491b8090811583d6a40c0c09201001440c00741c1e0180c1310001d5140f510800c1e00c0c0d01140180490b8413480c82000405c0001640011a0f5041d00d40c149400b00d42c18031000402d854100d082e4000320760340800305040000d40b040e80618081143c1003642e1740252038500d0080d031030300c494041410503465510000c40c2d8002c140718141d0130784c01c01c00c00352100c0d00d41a0410034100320807444c200380141003a2550b06001900071071601554101045190a2039040d40100403001018080c2480c4c40c0034826580004003458002c0000320103064020090340d40d60310303280c4089012020f80f0300400d40407910380103000c14006460000c8880c5140d010f0700d4a031640003109040840007010038460001c91007080c1010a1250083c09250000c0100e80c0c00400c028403018122802c20b0b480c001d10030b02500540340 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 445528597 1250 445527347 445527353
    0xb0a0906030f231005060f0d0b0c090f15180114120a23040506090307120804020316090b0a0806090c060a031407110d0e0307050415090c17010b0403 65
    0x160b0b50505680c0071209807a0388400c0c1010043d0041900ea04150b18002c9404440e0481e0554000710f1044c041141d00b01c024132111020040c041c4400600501000705401c0041c4170b00c02c25000070a0701d40030042610790000303d1000003481d9010610003034480c092010a07502018a41e0099651409009080440e101d0f01d10b051b0080c001d0007030010f00191000140003042c141511a407141da0440c001803600e60708116483d040482007078064604585070321a110000d030f021940441515025580524080b040307030b01c2510100c696103405001070764103007c1d5210000c01102140101e1004005890000ca01544400304028205849a02240b0b15400481c2048011180030542180c6444100c03030740ca450303520481c1c04400508601403c0c000d003075495018031000070b4101034000c0030498400c086610b04c020020003103545d144407401341505644020018003c0303190035040b00801c20f004510400e655552100e0010640d0304e0b2041500c00b09424048000c80301c1c0e00402040d000d00280c4000d1464685156 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 445529847 1250 445528597 445528613
    0x40e090d0518060403060f09032019030203090310240302060a0c0804030606060206180c0d020105031b03151009030506010306020f090907030e060109090302070312140a030b0a090603 80
    0x140582d0707510042c16600039659801d040c0c901541d0080e03000c028245500320998014555040c00b50007040b800400c0f400100010741401640e90440303000b91880f100d400a801d00034919508044040d8081403005100c55181001003502d0741da4018800302e100307800340980d50031051440d89101015a1407207420700158440d00215000032000c0c4c504003184440c0c1d030408141d107000c2da8100034034003800e01100003510f55000a10900880c2c3c1e084007200b00c440c0e411100b0341d8502d200d24035070b90410403080c030780d001560041e0043c660040c101c00d4034101d6203104142034034140c0d204031650040c182c080c8001c54100d09200301c040b4812344103400c1c200140760941e20b5950ba40d000500c0000c0c006500050082121141d22060341c0010394081d114410700c0c1081000900504140d00c40071000d480340100001d0001c1060142d00038048e00358001c0c0c5006d82c00e507101c81c0091060010300301c00344801e82001880e40010003008200c0c0850076580007a4281080d01008040c0c2c0c40e9074052600d007420100c051010550350 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 445531097 1250 445529847 445529857
    0x60e070e160306270606030905060f180f071401020f071e030c03060507030509061b210106050a0305010b0a090b2d071a15060d0b0604060302040e090d05 67
    0x40726102120071950124040c1c0703c5034000050f151100c0102201541d4030841c2c1d118001c0c01130400780905030306c0792030440441da2880c0c8064419400403002c1618028a903001d035401a0500c0d2070741016094110485140001040c108100e41e07100010410041c03100c003008020010091002c0c140d0071602c140c000c3c0d55400349000e04410901c019407500001126142c13001c1c001d551100080b401c3d0b640c0da0a0544c0244421200c01020074284800200d100c500440e4051003038031102c0b00003401550780c0200c001c140d08050400e041045644103000c0d2a100e038500c00707034001c19850799032907501e0402007402021780701e043e40b000610400901030445011b4200040405641c004192262142c001e0305c1142a0103210310301282c01c1c0700d4003150341c2d10445e03030880090810364011080c200240c0741c8102144240d450071900a00c0003d0398128a81d96481e142e8010195581c0580c400f241e0300c5043c50005909138000c1d440000420387c0010100045c50490300c059511849010141240c241890700280051140c = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 445532347 1250 445531097 445531111
    0x5030c0628020a02030114070201051003030219150e010504050d0903030c171c050105030d09052404030501021602010806010e090406021312060207030e0303070f02100302040b030a09060e070e 84
    0x4080800500c0d10300c2042008120f0b0b80080003407203040807204e1114040001681c032800103500f030000040100d40383c91071000499906500518501aa80d0a0248a14828002103c08582c000d103820310404180c01000260079200c03000142da030030300b440d102e803170b103400f50300000c0501403c08810404250000c010408282d0041d0141002444000541ca2684903040c50843c1034405403036511403080003640868141c52007a4101c0300003031002c0c40c0940d010316052141a520900b410341c502d03400310400c80c140c105460300d000a20b0900b52280d4440342aa0400221003403003c907a80e021074159a404600c494101c4c40a00300205c4400c4101c0102c0d59034100200090200713a00082c0340300070030050b09500380c01412091101002d040322450f2040c040e6020840503030001c0d10f01488400c0c01d28022003154809648405201c190907166400c0c81a1541e03242008018035609010001d40450010019031080e24111000542c2124500d0580c0c121071003080c500e181075000e242c0903c10300c1483d03d101600202 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 445533597 1250 445532347 445532407
    0x1d040204110d020d0c08011d012d03060c03060f03120c030917060414030f160c090515090109020901020c120109080a0512091b040f06050604080705030c06 68
    0x1103101e161000c2d202d100030141102e8400129090391503502d03070003850300c1c3c0e2966507200b0030359a80b011305d5481100c0d011034003140951104010000c1c0c8400711680c2c40f070710010751030380004403041035540b0804c51019802518401c0d02e88401418081e4144130715000b5084280c21846080c0c00d50700e480c0c80703100da0714264a05120060510005250088031148020508550004010005801031a07100e02090b20300711807108443d1104020b2035804816111101003442c0511300b4491148411198040448001d8541c0034440c0340c00b103100c1583d4007400b4803548008090300c80c0742100d0b10600000070307016440075403240d10610507280d16030303070208210442c0398049420302d81164001e4109401000e14000050010380001014485150003a014000c4018105100061035540e8030310300e6140e1101c40840c103204000f103c100803072464240c1c040340801034507040001b400e07a15100820450761198003c901c2c1a448400e00300041e250400c10880c0e40c060564140b420224030700c0c03001054200524181010710 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 445534847 1250 445533597 445533611
    0x7080a0c020a09021303050115080a0b040c08011415030714040911030a03110601080d02060703050702030c25050409023003030709050a1221052a071d040204 69
    0x55520a4602c000d40308400c821076403024140440d140081480c80202ca055091802813800b10b0310416540342122104809443c5515140d5540c1e000c06ea001041150200c45e05000420890000d00c03403080802201101503259007090038142003981d800341100f40c80381e0b000c000e0a0007030441d00d00c082e080c541c0e8190780c0444c0015451400c50f04c0410b1440249425124074103023a8145540800803903030311003802040d5420350340c8075114281c0305c0c400c2041c8480542c1c07119000c1803203107100c1d600003a03109507217105880c1800510303503045061150341d902800102440707648000d801041c0d41400c6006107002c9508000c040c0b2644d0102d280c200c04001c0581c41f0180c16450303000303400080102030000c00082030540341e0720315001e070018082c1801c40c06071901030746407001d0101c1c0000e45810b103221110f4108003969206103000039890302d80c2201d82c00c076030b0802c201800341c403a01805412001100300d040c0102c02e21000c240d100c1240c81c1c40740c9a800040c0d41c04a0380440c10400040d41d480d96006501610085059 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 445536097 1250 445534847 445534849
    0x4031b03020c0907030f021c051006020a08030a061e0503121e130f09090605060603010803090d141005160203041a03090106050603040503031006030e0d03320703050c07080a0c02 78
    0x50a4604d00281814000103002c0908044803023a072a080e15940000c20241e20b035021112003000081c001c00016070b0001d100d50300403440d050042c60784940d400c040401d60316110025000350168000c016507207030001c5042800715140621400c12400b40041c0818141103021900b680c00c80a080401d60b0304c224006030019a56aa0800482c040c000110f151001e4070b5669280b800180108401507811901d4100400c12600d401011a8100c0c0d00c0c1900641c01c00d8250002c02900d034034111801c542d00e6a0f0361040c0004428203102c00fa4641d403050340d0004840c54940b800703d801e0310002c41d40c00210b41042005000c0010004149050358030a441c909480b5515540c42c07500400c0c050700305550010021041008015001006504c2000b1103a03281c0c446954a602c181d003580c000c0311840310103401c00c8405410180c4241d1000604080c107440340e1389060b031280006a551400000034034100600070341040300700c07a014040c1c5a0004400c0c03040c1441c240341600e580501c1c4c00782c0d0040307104000c003008251040d = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 445537347 1250 445536097 445536101
    0xf0e0108040804080f030309010b010804030e01030f1b020a0b10030309030803041e060209040f061436010317030903030118021e03060109050604150e030a120804031b03020c090703 79
    0x4d04550003c40e5280c034180c80c0380c0c81ea40d0700b00b29840843c40d82056070682d101e51040b9001802203a15407aaa1600780314200198041e06444110704411940e996144612610121303070505001c4658016001e501e03117605100401c0480244041c0000f4441d000810000754401940d07012203400c22100c036142d840c0c80ca4040c030364054281140c4100340300031811206011071a401008980c604440802000c00d0b102c00050958038075108017601a60071a0540c2810300300100c25400b08c05c1c01482d0891110302c00c154854140e0f20030300d02c08170002c4281d0f00500410040c3c070001400000000e441c47c0c03e42c0780601220350f59200c140a03c05080c0201d02107480300d103d4603010380e516500e10030410703921041520300158041d0030845030300e170001c1c0c01001e000881c0c0c1400001ca405a520a041480c28960303210300580b01c4502c0c600d003582c4c05100f10212840440c500d0b511000040c00c2d96a94042c2a040030b09008003403022000030030008403c0d410b45030000036000144174000c000c007940c41d440d503030f40c0c1d914051380 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 445538597 1250 445537347 445537349
    0x3180c090a02030711071e0914040314131d07050412030c0c150c050c0d08041a1312020406050f1c02060c030c100609020f0703050904061a0306040c0f0e0108040804 72
    0x4c5100f00a404184446007405e81145220742000047c21107075100700000c2500d0320002c01c0803140c54000c2c04640401e114411036070901c0605500d19140205000450381011441d80c402d84c40844a0f0303c03000c1e1300d240d00c511a542c1100c4079140041c04d00e4180301442a502411080060074018000400f400308450016400010100c01c0c2c0201c101c2070507601c019002d003003200d204072141d0060b0054540e55150111030700e4002c1d0b401c01c00350b60909050038400c0d056980d91019568658505100141403010700d40b03061800b40c911403030340d8008400701d4410b01003501c2d5550880c1c1c1c03003420720510b0071402e51140090034040381c180e1034510190b60203900201340e02d40304080e804102800000f803a02c84074000090891800600c000d81040a26590440c120072405212817401400404012103000b00e4401c3c00072380158280103000180d49580c55070584509600405004900c03000071003000b0903490603104a404584442c2840b4142400d40d034002044998284030080c103224207000031409120510041d24 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 445539847 1250 445538597 445538627
    0x3090608100e09031b06090a02040f0e06040309031104050c031f0b3001030302060103120912030f1706090a0207030e06030a0b1c0503040b070614070503180c090a020307 74
    0x41c028100fa04210b9100d92101840102000c40352440d00342c0c102c000200280b2401500c03004e84000c1615a080001900d103d580e144007154940004128200e0700340015070040d0301c81d48034200d68618500c0d01000b100c0c180f4022a100d2407400b03042041c00140c0c8001c03203502c1f4002602505010480030f01c0301e6660000e540002c0a4220041032f101c0d40301c3e071356030019004111034549801c4038803400c504052041909000080050b00309030010030003c3e110120141d8881c841d4106944125101d401043d184940500d0075000102c0303e0070400451504034524014540c405002d140c9a850080041005400080c054400c0d465002800b901414480d007080c030350805000703200076900d061401c41600a400074400340c03807050344802c500c04c43c0c4c0c00c09042041001540140075504042c9481418005a00094003d540094460201041120102943c0ba00c100300e130b92100c94030b900b0070401c452200341e812a03418050341e00c0240d500f0000c2e07940015083d0300c40c61040380507a8075591614100c0e6501e110460b14 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 445541097 1250 445539847 445539869
    0x201050c1609060f050d02150c1e030a1e02151f1d010509100603110702060a080f180601030602090604030b010902030402010f0905181b0c1b0301090309060810 70
    0x2049101c07150f0080030455441100f21002c00e40ca54007000042c8240720030095102c9248584280d0407100c440c090007092117054103071501e1f1802c0c803404882000700215180c5c240e4000199400c0c0c810b42007480c0c1e0101c00840140c1a84608144901070b60f0340c08140d198280100f003000000d0711101c2c00405403064081c0c0c40006418450356500380c07046440e0045118800da1070341c0000850f0905042d044c103441011414100010645813007804c2c0c004201c2c403030f000c03544000100321410140e03c03600000c0c244141907650780103440c5841d54a412851340c1c0a07000c8075000c0c0440000d0342040100091090640380c200c00d0040c3d41d00d10000003d0443d1041c0d92004000b1a0310600005001c42c856000d90b100b54000c3e21000f007000d1006100301d0f4619000e0241329030252221264110700700d0649061503001510468201c46203540b010b10740995000faa00589895100c2d1008000c2560285a0041440030a030001e0100c5002690b020b81010b420340600c004020b182d0300021401c1c042c0140c00c20081c0300b84903030 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 445542347 1250 445541097 445541099
    0x60e070612061208030f0919050a03090e0702070611031905030a050601030b091501033b0313050d0302150a09030e101b0804080f0f06010603020f03040201050c16 71
    0x2518070500312071030100c6186000c8000a00b0030300710030401c080c240e2054925155a480d0f40107900d680304050010303502e9108201c0707400d00108411030301d03110a9005070000c024038103007454002d00c021403a4128403825601700081c403070015000a121015030b121410203081c0c00317540c0c1048524500440c80c0380403050b003e005180b01b500f0b03000f02c0118041c01c13090310188655900c0d0f03001902514081229240c0192050002030300440c1a280c1c40030f000a0149804541007901d0100c2200071441d00c40c1301e004152845c1e288615041080701414406001c05000d141000741c0c10760203080851180c483c90703000c3e01c1c107001d0210030144203001e20088905030707012001c81400c0600710700e00145501c3d5400c50105600f48402022490140c11000c48000c180da100c802802e00004548101881c07403904440780082400301141d0b9030028407503c420a0718243c010000c2c19100b1280518000c0181d1195090500c10040744043c0c5003420112030b80a41c080c00c01564904408200610300042011b00320500c05034428 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 445543597 1250 445542347 445542359
    0x9020a061e030e0717031b1c02060c0304060506030304030c03321216050109050309090c04030314091503090c040e010e0c130e030d0c020d0305150409060e07 69
    0x101c46030010340712036442480740c000488103500321504161800d02070307404010304000000c440366a03084a10780301d00a0300e0030505440341d5640140480c180401c10740d00b21084048038149004001c010704204ea100910745800c204c1d0341c222070f610005d000500040e480310005015500c08000b11001581d0201040140c55981e081c152229204a0200b015010a1032441e80c94021a52400b981607807504028150304940c2e0301e1011a42c2d8405094800c007183c000d40b400010034428820342c0e00d01070240014513500c4000004000c10550000d004803241c00e420701c000d0020075404100500c40005c11003226959542010005484000d4001707070341800c28000040100141c00800e14200d2050180c030140409100449100d003600c0c400030b070084041e80101c96000040c5000d480100c5605890030380024501e090143c0941140c0c082d072540e4002c25210100c4ac0742c1154100310399405100d10b0324040120382003003504800810001100c042c030494481220400788110780d4403d694001c0c101084481da40d907144 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 445544847 1250 445543597 445543607
    0xe040f05010b1c0b070809031c200d05010b0408100c0311071a06011d06030402040207060c05030709050a060c0209042f040609050106020604021c06050c0301031101020c031b0409020a06 81
    0x110040755410044c2c0c0202c2d50082c0280104c5020306c120b0005181082000744141007041c0409164001140d1115514807c662014001d20748c020340c0e4010880e030f28016100414260b500c182d101c80e940b9501008100400c0501007500031001070f80341000305a95129000c00c034040d00500c0b60b04100190002040360411881f40c0f00c0101141d500f00070f0300c69698844d001502c124038408001d1560001410801c180d83c41c003113008540c420300c0140010704003046904c40204903204081c8080201d00c0000c00e008115030800c40810003428129424803440d824100c0040030b10010050003400ba40d00e4002250820042400d1055644020805030564020040c80e250341d84103001c841c280510300d400c5011480c21000d029690698003280c004200c130791030b40e41c28000d10341404403000303011401d0064081c0005e00d0a0240c28011420481c0041d01c80d411814442e140400100d0100c0c1503511401d0201800d46002c0b6032060002145501110100d102201081c040c002160000358454440e08001c0b414035000 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 445546097 1250 445544847 445544899
    0x3121302090a06081b090601030c09120804080601151b11040905031e191b050f1b04021201090e07030b09030a020c090c09101110240e040f05010b 64
    0x1421905c4000c00d40b9442c1c141d044c004822540c00051580010709554042c2d004441211041c1c80e1541c000c6035a504800c2c015140300c442294a801c0004003000707144d50810005001d406007040100d48070b002d800d40030f002c80c2440340030361640c0b1003080c0c000024042000c694108500340a0700901011455181040e125070081403400091101c521407009410320b410241c404107045500d294580656240c01030380c00ea234005003c0543c140d2020500d100081040c003600c800103401000901c400001050f110380e1580d001034040340510310501c0350f00303540e011007082a41120310245e0001a101001380c2d80e00c1c1005500d030005092070791081d05022500600000410201042c3d030700b600c01820f001007c000c00c001013030700d4000461400344a581218038111082104011403820072203800d00001c40c001d414901d05008204a0301c0e40d07044a81c9400700f0400d01c040c012075441e42e2400c40ca5080450f110810500504017400d442c0c0d03c43c2c84641040300960040c410b6180c004c1020001d841d5100c5004040208 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 445547347 1250 445546097 445546109
    0x4080a0b0f15030a0f061104060f09062f0717160905190c0306090504110301060f1a07050c04060b03010f0f2103020a0819031404030203121302090a06 66
    0x681d0000488100b0846540d6148030b2000b4003402d60480d6a40380c400440000000c00d8440c0b035a2000c003481c0d42c03400040240000d020039107414481c4802410043e148041030380c001c60a1003032711284d601c0510701e450300c0c1100c0c3c203907840446200240000001c0d4030b08203081d00440141246800e102c002d003500000c00d40788444841d00d00d850ba998070350018000760350f0182c40030410380d80c8640320b005c3c8800d07a640100380440a41d260000300241e54090340016107006070740649601c4403100c01c0302e655080030700440c1c4c0540200f141001035140b4101b51900d242c01c0c0c0c020342c0700a00c1c2c80480d158080000501411400000c000d10510655848102e240001d1340b0a100b81e6502241c000030008076403804041680442c0d20310741c440098518511580106c200c00c1100c21804c50103600c0303018000030801e4024240c0c0c0580312005856510700760902404482c010081d801740442c81408010019070f0010489044c014020016881034440010500b80340200301030095210790b8217401c01c07404e40c1c0160b01c04001c45075 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 445548597 1250 445547347 445547371
    0x221b090b041109010207062a0b0603010b01030b100e0301020c0106060816020a0312021804050106030506182203180602030d0501050904021813150603050c0a230604080a0b 75
    0x40580320400892149002084c0940c00c2140e003084258041d000401d400c1000e00c3c403c0c0c0781206124600c030000c5510080440329182070717806003c19800c4c240f060449440007070a041014070500000503013030721410b0401108000808440905503142901a00c01e00700d0520300900849469a5010740412011204d5200414284900c070113070510000c0e40d017107100c0e010303210300c0c1203030720755020007130282d4020192804010f0001258032290348072441498020459980c1c002098200031041090100303030080e01d400e41503d0001400001c11504045460761805018025000405858256902e4080007007420600c035640790700050494003c401450058101c0c0700c00c0100d80e0301c1d4020001c5105040d81c000e5005110503072a082c80e50b4803010f4558000b802440c400840f44125aa00344034110034a01444109446840c1002001020010400e4445040342c0c96185c0d01d05008058402c00c0380742c3c20300740700803541d4205511281c6a1508a6002d0a418021b94009034142d06050301c403d0341c2036601c20350f520 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 445549847 1250 445548597 445548611
    0x302060903031b090f03030a030606030f0c092619030315080c01110309030a23150703090c030206120403080a0209030c13020d020c0d0801090203221b090b04 69
    0x940c000c41181d10039600d1000428068032002c0800c1400d030001c200c40c0341c0182213002180d4a59804201a0920241980c0c000c182e040c2440d0008080e1201c5004210141d0300f4102d1615003250031030726800c01d4607003610308803403000b081d90b040c120050a145ca41034881d005010019141c0c075080c0d940c42c01e4190090b01c05000b0214504020012407046100c1c103101500840e810249075803181a1409041400d0411a41440301440029041034401c2c04101c440d51003000010807250300000c0301d00401c0398200090810396146207121458200018250420150341d03d81200c100040845c0c254099500500501d842d00d00c691050322003140b040e41c06901003031108000504681c5a402200c2c00c1280c0940a000036140000a0141990602d10360308007850b02800301e00990b8045102030b11444440c800286030b00084040003400419040c0c0142c41c00d64010810000e9500c044200c808040c07400700303948103c2e8100f03800d01030211001d00030b195000400704500000c00c0c910b04d800090300100105c4042140c4 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 445551097 1250 445549847 445549861
    0x62a0c090b01170609250f120e0706050d02040e04150e0a0201021c030f0905011d0c01080f040303020c0610090c0801120308091c0810090b0a05061e0403050a030206 72
    0xc80b00f1100710540c1c84041c0000a6854200706800a40020007558143c2e511032003c820701142414170802c580007c0e440e41c0b040c00580d46d2011287c82c0e81701015400f0000300c90410704168076070100d0701a001c03d00c0700c002070100b0480307903030b6040f90300074160b54042c0c9086081c0780c549500b0a5000c102203140032810141503004940d07010504418056058000b0200c000b030b883c0c4045c10001e43d8484510034595a41020003010746180240312005208000000e071120700801c500c00010b180b40025400c541c808015081c007640c000101039040303426001400403999661404801030701c14031104442d140117400601122003040040201550315051007441000c0100d802124106424412094200d10180350040805e00403641241c2154525060f1084200340200e50188110101000f1002980d01010400c8581c40004035001a1040940510100d141c08000854403001030003a0341c4600c80000f01e401c0c03540f07000d5000c1c50b0f14802e81d046140d00e8981d079082c560781b43d001c0c2c01c009801500a00c0b0000b248 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 445552347 1250 445551097 445551107
    0x3080d02030a24150309020405090c030d080112030c1e0c03060b0612150a080a08030f0a02030601120b03010204050a0807051018030b060607020607121d0604062a0c090b01 75
    0x4550001c035062450307240a030305400380d1004083c44d00c00d0541c1e9241c2e290140e1241d00915118164030300c0103201c1c03000c2d403c06140c505550303a141001000015001800045601414035003031581501e0441c0c112086814601c12a00701d100c01032445000c2100c4e11020400304005181c1181d020b11001c001c00003900b000d0092921034a54003410301d0407020005184815406811195402e002e001d50525548840702a450301e01458019110000040100151408004d41c03455100074100b1080d421030030f040b0700203044540c94000683d002502c0d2114840691025419140100402012a0700c6180c3c1c4501058990006020380c0340504600e070071205040f405110754141120b41c4c80c00051101d4510380390300c4115030003d0501a4002e2040064201603030702c0e40050040c09019240d6035070915490640039003000c098044aa44002c800f41c41810b550f60b681041c1d5085641508010501205103042c03503c9060b905841842c0b1303240c00d05200c0c0240301e000704c0070b003081d100510800c12041e19121300540d0 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 445553597 1250 445552347 445552391
    0xa1508030414010c0f05010626070302180a0b040507050c100204030206040b0c070306090b1e01030b0a0b040f060f060f1706040c03020702032b11061f03080d02030a 72
    0x1c0242c85841500915403103100d40c40c0c902409038a00280c00013150340d61909485441c0e0210101c0c0703011401038032030402d420a00c4444802420001c0402c039103075501040001d8440ba400c80e80d00086600000da1500107908080b0500d48022f00802c264505500c0c090840e40201c1101e007800e2080240c03c03146940d440c8201c4094940051510342024600000851164403840201105004843d030010000d28280240d04a90b44161404ea8461034404103d820303040c1994810b2840d60019401000400c99060fa240c0d0001e2082d5804104803000c540490040d051840c405441780d4030705000018031002d030f14188030a4030010b50314608c00103840081200c82c01b0031140302180325250b1001103402d42c035140d80a400c0342c801030b040242c01d1441580000e81810540d07102c40d10a04a0900c0380342d0b81c0c0c2c0c00c011382003a901e03241d130411071b206501e11800c6958a8400404641d103080007601c56003002c000c040c10030310081d540030321980d0707503201c05a900002941013911030001e01350900c42d024096000d0044145 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 445554847 1250 445553597 445553609
    0x4091a01320402070807050114190c120507022508011b090b07020a180501060306091e0b120601230a03020f040c03060909080702030d050c070326030a15080304 70
    0x1c1402484641000029400031030112580a01001003000103442030040582203030b0440c010040901e041e1016078480c2e404650031010851401d8000b401290b0404561a100c0400a43c0002c03d5556003509900d001c2d002c5103400c0c08086a00310846007403141005420548401d28001d0041c1010b01d0580805a44030b50405008280c51140900100b42d0b00d90182110b9030004106545690351418002481c4c0d00001000c0500c43e01e620050140386d4040c02100f000f0711340200204205610440410804c100c52114954100d0712007000042558031031004650394841c400c00d4944a50752001200d06600300d40d180301d040404c561902034581e2429405c4a0100e0390090645403101c2040000c00008011138180388003455030740d02c004038403c0c1c1c9621900407000d20a000190340d41405004240c94103640c2600082042010480c202c02c5500102e514412698015000e00c562805001c00e0300003041581401c04001c0b13008401c1000c1e64602c2d42181d82c185c401d08141d41721564882d03042c20b880e03102d180205 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 445556097 1250 445554847 445554929
    0x120201020a060504030516060b090601180b0304020303090613080d0e010504030809031f140609060607031101090203060717060102062211060d060302011707080c070204091a01 77
    0x94408030b10981c004580c414460310380705252203038901c0880080d550302a01584c1555650700a294142003e000d15500240b09003841c280760160710060020381c0481f07024070600340d0000300c0490b045490400030781e006510020400d0703881c1e001841c0315040600c050b100b4003442d407007007440d000d042c1030081000a10300881039450a00e801e08644640307000c1e9218921442d01032140c1c0307142210b0300c2d030442c0c02c403419055900c0d0041050000700490720f4100001400d070b40d100700f80705402e01c59207545140464985070707130608100264524080b01c160040c200003070040e415001d01c2c0100301c1c04a03808004482811040c940f40650364842c02c00480c0e56807421100402c0502d22100744808811104c1d400e90301c054441c00c034001c040005070300817550341c0c3c01200285c02c0550329008280115a00f20312003881c0300710501032112091a20410040146a014211000c2c61f04c0003d1000b00355242d0760443d01d411034114190100000c900303003502c06900740074420382d0050185504600442107800c6402c140541c403207801 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 445557347 1250 445556097 445556113
    0x12130b180409020f0a0303030e01111602010806010207030f06021b010203060d061a0301020705100606020d09090903050c01020309150c04062f120403031205191d030f0d0612020102 79
    0x50100810080c003040e6130183c58500321002c5551038044202c040c5109a0f0040b6040030000310050170368860403400c5400b08010300102e1541500c15050885d21a02440c100034240c131007400503401c0200540000c1c0464240704d203040309000c0c00390020125081a01d1104500c40500000d4a00f03e0000340c0700e4582c03008030141014040385d26500490703680b8050051003d89500010700080c03c90748030240c22030b85038100003208030f50200d1a1007084002c1216001422a0034000740c0d00400c003205c0f601514510a03520071842050500c69030540d075a841810008543d42c2c248190300641e60b0071170003441c1c11000070703142c002440460041c058a08480f03460729070119080741100703420140e070704d45e09070070880a584029001070301c4020400c2410480103120307000d033380d9411800c000b0041840130744002d02140c04e12040c0036921100c51008a0485140e80380050100d816200110340c040c40146030950031320011070071000c0c0020607030040400e5000f0f02e2040009a40d9400c00b6070a0030060f01000c0c2c050307001000 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 445558597 1250 445557347 445557349
    0x27080607091805090c040f141e01150c02040f0902030d1817160e0106080f01030309060e0a0b18010815010f080c04031a061201050c16031112130b18 65
    0x1540d0850044d03030036200c4150841000c40d080310b090384403104040d51503985d00000d9111407440c080c0c000070700340c840d108a11007102d203048005d0b4062140304904103003e0006906580b0800e2040c007800e900070b0041c880045401c250102a2410b0701081e8424022401131a41d0280a607140d000e446000e5450b9281551400032a24540320242113021400c2c002c2c09028040071000109140150030100c25200d51541004d8004041002c010007200d0795084800041c030102c1d80018a0808075141032400e01d00c04e20141021031008076190748850200400803940d01c0d8059401d914131084150b081e40c44004640d5007084050003003c8622409000c91101406c0b80d01c0184120b465a13403005240c00031b6403034190b4076503819600c07803210b80201480b03800301c10038001c09180100314200131b0090f000081c0086d0921000e41d4140d40301d020042072031001c4154103501050b000303501c441c0349000c1801c180e0f6078500f58240441500d52082e81d00f20140070000c00c1c0030441a4041041c4c4d48c040070002e18202014802c40 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 445559847 1250 445558597 445558601
    0x1030c060e011206080601030507060206152214010501110c060d0c110a051b0f150a020a0c14040b100801060c020a0806070f0305010f0321270806070918 67
    0x145201d41042071401c0d02c140040c1c960f00a01d03005111140c0102010f615601f002e43c200f4074550040c5045403c9107051080d518942c4805140302d10302112080d0000d0020414145a100d1050900c80900c0c100100140030080310000716048500a888014003100c6045442d510380c0f089400351075200f003080c070140500606544c40240c002d03040d030800c0381e550310000c4601c0b071501e403000000703d495601c02a40b645414804800c41c98000e1400d4541200055042d40055188803d10318281e0010304003088500441d8401c010500b00c0540229602e40f100d900e4039071411110403031030309090244d404e0100006140c10700b185200c0380004130740d9809010340d08010741200c81410f60b080a0303a000b070b000b1801103890801031000c2801180691100f0107464140308000d025220141d0001024000140d010000b0170400715070001d102030b040400c107010390040b40041d216202c01140007900d10071200440718010040240c40e0041d280c1aa007120010f80c0c50031801c850103807090040d81002c0808480c01c0d040107000f6 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 445561097 1250 445559847 445559867
    0x1902180604110403060902100809100f0f020a02160e01150e04200d060b0c0a0b0a09170a030e120f1303121701050409030c08030a11030109090b060901030c06 69
    0x1800803881001c101d4800e10076803c00d03002540c81e540c0d2400d0036000c40c034145901844005075400d01e49005d150583d0101d8403211208004180242c031288190101103003503003c07a0085600010031900c45080c00002942d911100c018910a4070540001040c0d03c104100664101c908048416090081150045070034140c0c000056821071307100c00a030104841d009144004094811201c50f8840c0c0c104940d440c207895440d880302880300030801c255001c0a101007041d00086400c0300c4586048d44030304541c10300030049020058400c0965510000001d030b10078000f0280d648850b5002d01c1a10101000244c40b050507074400100c00e1000c100b4404200740050241c0304036010340744401c0081d592604c0d1059101188280c2d1400140039202c2c0b8070311b1920700807000307025040c10341d420080b80441d0b1b517000d07206000f56503001c0c00f501c0c00480060500144c070780140f803600d03030040401610b03943e442c58014080c01e0340c01d00468a458012000074241e051003425181244c7d00441050f48040c54604142e4140b15a = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 445562347 1250 445561097 445561099
    0x9020d062121091508090d21020a0c08040306060512070509040212010e10020c0f0a0804060818011e0513030e0108100b0408070302011806090e0c0d0e0a0519021806 72
    0x1d400021004e8850b050030800303070155103489000e4500010340606115009044500744006400001d2030269101d109600c41c10900c440141d544200c01000c1d99a072807050f10040022a000801004211441e002601218000d1760f000c100600d2480010f0b4480d0400c0c06629041300d40d040001300545001c28100550003100303400015455005100c69040006074003981e0045600042c1005a00703404000c410168141c60703024059480c090b655646040c852441004100100d0102141e24001440d050f000003801b01070081102c00200c0f004c100e12210704d0741c07050560070301c2c0c0400201d81c0e600c0404004155641a175582c03c031416514019280301c2c402400c40405d071160f01d4004288500d60348001d001510800c3e0007040c119145100050000c0742082100890030b640303007010803455400c440d9940540782458000d040f565212020008140242c9040760340282c02c02c421407440d42c10104880308418081c3c020755140290b01e03c0015584c18901c0340007500503900c0e80d030700d45c0551820910182c020070 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 445563597 1250 445562347 445562357
    0x1302090a023903042102151321030203030402100306090c0206060a060201020f0403060c0c020405070c020906090c180a08030c0d09150e04020a030609020d062121 71
    0x2a03041e96640c0c4003010100207510012074440240b8110158181044050385000452600d820000c00503e036016003041c003c00402900f0b4404119540d41d059800607281100c2030b942c4a07400c1001205108100340308910607a40961102080c0d081c0b203040d0039114503095002145151901d078207114003460018900020550303078a0340421030080ca4002c801201c4071503030085c0580d040c45000c0040400041d40304501350780c41008001068000c03601030720126900440c000513180305070303402039503142c591030f034002d42c46490f0404000000d0342068a40c00701c1802911090380543c0c80d42e0510402c0c0d0826202c22440000900041d5054071107038401300042e4030007501180041d9650300e5080c0ca550445031200d401b903040300850102c0564043c000000910701c01c80507808188405002a0004145c41800c030b02036500069520100c81c000c3c0c1100c0000e00d04001d0441d85e03044503500c200300400710fa0041c000c0c0d02d051050b01d40c503007038401c8101c00c0310745030030500302c00200314210056035000c0425003941c03003404 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 445564847 1250 445563597 445563607
    0x6090302010c23030c0c180906010e090f0d031a0d0c0b07170304060b090a050c03012c18070626040309091e0b03030a0f12111b070501081302090a02 65
    0x20188050304114203010010f15004a000c0c0030408410040c0c444e6031010707a00b1104218608d440001e41c40c2c1105d070310911841721900c40120003801c0c20f248880c4030840c0c0c425114400314030b50341070703001010007030310450310489416600c030400c0140c00d0b4442c8007030181281148184000ca520900030079006110b5804010b90710104002900c2130780084405a4406a40b0301d042c06d02800c00c0780701b5541c842e0045900f0003092031303e4021403090b40810301450a4140c2c901c0010f500e011081d84941c0203180c410341d4800d00a1034a00e00000c4100102c0103d00614064064002042e0b400340d40f211001200c0c1d001e0750382c88031011484c40348112034014410307000c01c80c10301000502070b81c0358442c0849840084400851004001d50000c0603a010000d24074002e600811001c50f1203640507100ca070506825160003500c0c0c0c840c0d030304961702500841094500e408030010702c43d044020762051160b0fa0142410640c0d0300c1d581e070b03200190341d0468102d4160030443c1e01c42c13452000520b00720a81716030144002c00014180 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 445566097 1250 445564847 445564913
    0xc0a0b1602010203310b15040b0d200a120c051e091302040b0a0f030203011109010c02040b0a0b0408030301030b090a200607150c1e09050904020f06030702030a0906090302010c 77
    0x4404155051092003102c1d8103403040c1f0b424a0300914040703d801b0b85640030170340c00c5550350269001035104c0000c4a2540c002c0114115039441a81074000c16808000c074510020390304207400208142c1c0301e40c0344a46000030003050034440406031101e00842c024a005416a04c4d06d480700e06881c003c09049a0155070b45800c160035640350794000000d0320140f910080703094218810302d0302b1143c0340c0741d03000c411030424040c0750416a4800c0303500c4e1032240d050f203000c1000c2d4004408510519045c1d00900e08003100440c003c41c1690000020b181201d009800480c0310340c9829070041d86513507495101404550048601030142030310703100e1070884400040c044500d04010394a51103c0d0074880e16071810215142c140040c682c99021041501110208102000c800104503000e800601c01d0b03c1101d00500b1242c000905540c1e801716407081d42880500f0181e568a00004001e4070f81d84030300d00040c0811034942011444030b01c100c1030079003504c2e13040e1251600e128983e120034882070800000ca1985082d000240800 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 445567347 1250 445566097 445566113
    0x7090605220e0103050706020601150302070f020a0b131706160e03060a020406020c040b0f040c0c05030f190c0f141f0606021209030a1101050c0a0b160201020331 71
    0x20141260085843c1d4198070f00681080070326481070b01198841001400b1041c1030106c02e107524003107802c0c0140c0e628583c2c5484012116151000395000d01d51403000645d02c0c00c0c40e4002c1c145003900b0312025038416104c08070104503c61a01c5a01c00c0f80d03002200080441d0b64005416065101504114041404920009140c0807046500e0706456802103020494a901000b945d40001c900320b80520458642c8000b00d8000a102040644643c1d00c9070034101901c0d015560704030b40260000140c0c0c2d90340809001200c0d00758068190f5600d03020700b850540c0151442000401280d5a121580c000800100d0712307020000c0e041c58000c00070034011416801403400d000e501c052103000343c80c172022030024a444d40207802e028508244800104040001840320f03a000b090710791209500203000144080c841b401242c16019441c51364889210f49440075090280403925681b207a1465400e002d014002418204e090340801c1d241c44225440c9011004414018140003d2000d07200101090300c10b0a1030b03c510395 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 445568597 1250 445567347 445567349
    0x1a31061503090519081b030c06040303200f04050f010801030819090816140f060d11070221280b0714040608090106050a0501140904060e0106120e060709060522 70
    0x45e90420005203410492071090b41003010254820140d41040903200b000342e21440010001070401d41d441c080c501c1028020034440d04200c040c00c105589801030000c44541a034000e00401d48240d80041d070103800c03503204e00b680d03505880e03010b140300d030600320318002c1031110174100041c00041c41010403000c10903100030044685032025845080b0911032911080e1000601d4011051b40207a1141c00d20040710b440f881704440e00110b400b5000181501c00e011010000c0c010741c1c10080d800070030707000a400d04c142c0c0c0715800ca04220381001a1b07083e651131008101841c1c60000c101d008110182000f04004c81c20300709440b988200c0c1424401c00d600301d610b101107441c0d44150001408180c0d840c0a10580041c00d00c142c8000c0c0500b41c0c0d03440c04035414170b40042d003844420b482a0484260000d1041d181e034a45400000003803103180f40450301d039610340101414040440c869081c00d10725100c0e209010a0740014000d00030182501c41a50881c1014021141940280440408801196040c00c800600c110a0754 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 445569847 1250 445568597 445568603
    0x3060f0b06120a0c020c060a12020906070f050f1603020f040b04020c0a0b0606040e0c03071e0c1e0c050607110303040f06080a1109041a31061503090519 67
    0x500d080d043c180100e807021401c000c11507214100342c070b000751240070468440c20315505005d064000580d220728041d00c20b0000e66a04a640803902c00100050381d43d503900c03202e1141c070071340324691000c003803080e5900b4625959108a4a4503001000542230080100c1000d94002d000851b208100c200810103a80c080c0920b00d089a0104603403509015883d4009600400102c0d06603103000d2804400641e4a84090301020080300e000020400d0340303000c0c508100c0d4907400b4400e08002c0600120016200c15031041c002d440c1301c00300d60001322410301248580358005a11062116070542130100780421508814000c031500320408980ea9550b81d81000035100911180740782091007824210000d10501002d48505401811301d800d5035020016107090b6074070203805a0b40020140564500449101c0424040c503400141c1483c004510034400c0d07a82c000150308000001200303c41110b040001c8602c039106511000180c6486030303410724402e40059600c43c0c0650704444289280410b45030780c102c0780d06021 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 445571097 1250 445569847 445569877
    0x40b12070308180603010b0919030f15050708270a0b1009110307050301090b010e10090806011502070e0a1b030501030b070c0f121e020102040314120403060f0b06 71
    0x5a0f640807600c3e00a52245102514081e003154980b9050307480601900360041d100c0c0d00078181c0a07160301d02480780b40700119000280c8081001446c2801908415110a1200385604000001d070b0729074000c1106034015800202040c6240080960f092000d010013403104005014000c50320b0082540c0c25440c034040e10310f81e044407020603d0440040210380140b03050740701c605001d00400080315041415641101e03c0000c01203160a285401202c130080d15040d4568841c0f00303104000811948149000162403c0b281120016601d60070819011400a0303416401a40311074400d100010008100e41d81220302c1900c0403c003000d101c014100c01a01c81c07010710b00026660700041003440709010000e40c00c1400f40c02d20f01030541c402e840d401d0340c4c03248e170740400340c4071503410402c04508500c9526445030705106514a032080403508000207010b03602520080c0c0340700064503280f401c000000709103510300071400072000b46032038a5a0780754009040e424900c00c0301190b8500201a0341e48071030006240312030b94400a = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 445572347 1250 445571097 445571107
    0x708150d150b010c150b03120d1a011e0318120c030810030b0403080702120309160b0a2106050301060f0e1003020a06121d0f061b0702040b12070308 65
    0x15a00c102c4400444031410000c1382c00c0c120010400401c2c80301c0d19412180c5020404500203030110f454072130001005206080b0000c1d81c000d410171964000c8111440b0071341410301349440311004507140e404010003d594521184c9070814001e0087d8022070819901031400349201c02c09840c0d00d010618060050030114030b68094900030141e2295240d640310a00c080c041941a0131529440c080280c020001001d101030701d804680d940c1c1c000c00400041352544c0300207580e640f4099501c20340380c862030180c04c01603a0307034450041141d04c0e050044d110b0701d00c0d1554541202824402e50b40c0c1802c40d0018140b80c40c195a40c10120f140d031021300804c0054685910301c101e0715450550403605c4890300030284000044419001c0c4010307541c6030b203014112452441c01c1d03007643c0c25010050300140541054100c80c161959080024040e004c05e103a003020061405845455403000450707a0781c2d08455414032000c1800b00410b20040c40c140d8000b040d1201e0107440341714500c110094070f5103810f14a030010340781000e011032 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 445573597 1250 445572347 445572383
    0x912030f0a17070c0b15090a0c1407080307200105010323011a0f040605041814030a0f121d0a170f0301050d020d05030706050403090504050f0708150d 66
    0x6000728076220190b00d0b01d8201d103450103008103407440b10607000300490b0500000c500d0703580c81c50b8a034100d140001040413950341005007070140100f17444218040440c0c1e2007265500c092040c2d80542d0082604081d440c1d1450352400b50864400c82004042401000c40103020585400c00b4802e084c01b8500c07070441c41590003444403001b6101c0c95070410480c180d03814003201180b1010305109001c688481655000f1207111280001800307007105410075500a46040d001034800d403200342c030034aa401c3c000c0c80d072213070045c10010102d40c60f4401e1031080c1e8041188141c104d90b0b02c5120307101c0300e10404214100001e503040c4100d1121241c03980307105a000158400c00e0202c0602c4542c1186000300c0c90081c0c4040c0ca410f10418000503540014403400c0d00ca00c0c8810081002c0d500c5004200410302d9002082d80c0d80c0340b05504d010001030805890543c0010481b030fa001c6200c1c1418480c0e140107508845513001c25545504003114040e20042600e030b40c0244045115940352034000007842c000348981140744122420306 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 445574847 1250 445573597 445573607
    0x15020105071b02030a12030225020a1a25020a0303110c0306011409060d060203130b0604200702010c02040c0c03020f07141002010b060304200f0303030c0912030f0a 72
    0x42a0b01060320350502c0e41c100580c0d00240e81d031000d03540440740c1c66400060040640080c05a042104909407903040c50900c44450416400d01952080300d240680f581c03141040030040e80c0c110349024600d00100041030038a440c245c0010001060412416100c054940c082559210654011800b00f0581d0305a2a6810414000700c0c00c02c40c0294020704080d8984400d807051010350040d40d1780510158800b0811035111510141c4503650000e0b801e655030305001030614100d072001c400036680c100c5020003007406864640074806041c082d46560705152208103104840b0740e401440200d051120b2180f1010068031a400b965003524111740fa00c61403803081c0d007030190800000e803480c00d1458100c80c4040c0440b40b9410410b1006c0c1600b44ea04441880d607000050380105141c4400391741c00300000c02080304000c0c0360080c071000026a4052901448078080c03d001d032607414520865410b402c10320000b408402e8000c040c04a817000102000259580c4031490750030346d8003462801034140e9000421101454000f = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 445576097 1250 445574847 445574867
    0x21305091303050d110d05010b0a0807020304030321090209040303020c0d053109020c010615030b0108070503060a031505100f27020c010c0f2c060705071502010507 72
    0x203418801d81c4000385940c020301d184210f0990f02002e80d914028502030400c440c0a5504d00403802404004650311840b112001e41c1110514800003851500010079091020003950120b0382d1540340e24030a1441c0c0c10100c803a40c0b46580080d00040d03036a011000260391890081401903000f5100141e591074010b24140c18071004900d140700380202006007400c5030015007800c11003500a0042c00b00048041c181c04810b0725a1648401c1c0c0080c00424101115401075006600311125074100001c50a04203000f503081e02d00345402035012624400001d0541f40c0184002c6921501c0200025925501c0b40c2c0c1c0c200304400300d0309100d000300b551001040b4911018903135007405040081c2d200c0030054074bc00c3c088160701903c0020201c100c1c9540144c18403c00b140e4040c2c034081807807400240702030064014001c002d45103900380000048c4951000ca08106c404410f518280480402070f405051a440c080c0407955201c1401102c8620403810002000d0102075290310308010707298000701302d50900040c0286a0586 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 445577347 1250 445576097 445576111
    0x501030b060d0203060f0a0b030a030e01090e01180504020105090307080a11030303280209100c0516050105041710060b12010608070c120314010f06080c0304240f02130509 75
    0x70414000000d6135001604540c0f01402d50b43c0b02030b944d0342c1d10f140035002d0100044440c0e0548916440041055002000c01000708400c2e0317600c2c001250340e24042d40903000288100c21141c4c0c0304070310740e0081c100c10350400c0c1e90203801810700510b043c00041c00319183ca00c5c542d02c001d4190304000d03264420050203501020300c6c0001100198110b00b021644150700001118000000c203082504007214100b0b290180d4455580c0100b5a5030500c0c00e01c0340c09040c1d1120381804940038042c0300d910354107904008401105540b41a900c0c5410281000d040200a80350300c1a48d0b0f4141c46459210001c1c504640030f20405083e500b0702d10b944038410310100b24141c1030f060304030000340300080d01040401907000c81503441498000c40c07500183d100c4401c05800a00010881c0000144079100201e002d10034002000103c032019030f41c2144a6540010841290100f03660080940302040c444803482080040c082503140308200f00061800744084600c0100e900500c10f114815806141c204460315018106a074466a = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 445578597 1250 445577347 445577359
    0x7020d082406031005030102040e610e010207060302030405101a09090610050a15050c120d0f240b130513060305060108120703030f02070609060501030b06 68
    0x1c0250010070403240200300d0603001c2c603000300c0090000301001d8070241c000c0c20f01500845d0b94503101d031001c0c1c0c80e900341101c00e0340300c0301c0c02c0301855200c0c00b20b0f48600c0e40c8a0300c1c601c20710303030440740034112009860100015400180c0d00b03000207200d0004005604d8009011190300c030740410346101c50019081400d10f5100000b818414810000480c00108100d21901102c0100181c103880300d1401c4848410050390858004003400c04204164000042e00c50060640c1c0308030900315540d9508208406003103020324082a41c544461740310039401340c0050a031305080b84040d02c2443c60b15411604503504842c505400d2180c07659501c82d4015024401c6225480142030315042d4501c2c0c281075000030020a00c160303a40c503000090907101d500f11902c4144050f013001440d041c007510600c0004005840706002c195180c1c0110b400001e80810000f8080d82c502c01000359850030551140c82c107800516803040a14031054082096800080d13031441000c038454071405000a0b60750540c2005520940000e0410340119 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 445579847 1250 445578597 445578631
    0x9090a080909040f080c0604110a0303020c12070305061006031a031f0f090309030b0c09011d01140a020102031609050f06090a09090c1404142d07020d08 67
    0x42140c021030700c4100c01a00d240340c40351260310340403281e02c90301034010303100120101d0f18403084900131460728000ea0080d841600c1c0c904024041103524005444014050b03070105000103806e041c010105d08075200b00d0401d40303061613900d4a82c00e0512208544000340da01042c3c4080c02801c1d0140b040000c108404002d07400983c07940ca01281e5900a52180c134640c0e82c1c5901c0015044031010f810000e035501d03048c081800815910714019181002c41d0108403a1030250304005011408960203684036228140c0d034040000e00d0030010400442d10310101a410030200d10f40d40701d0007500030070041092003100d900050b600d01d4008003880d07202954078140010070010f0300040240e0303901d8145034050000c040f5120703517490761440300050020b51594803005c40c981c1865140c80c14403100560504c115805008000714503440d80341003208884800d0307805408031000101040da801d52118105036030001c140d0140c04040079104648ca00424101c1e410300c010792002c4031000140b9803010000740c115200d02007200303d41e = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 445581097 1250 445579847 445579853
    0x21140403020a030209040f0519020f030f06010e0408040306230601030c020706030c3608120d23040c061106060d0b0603031c06060e09090c060901031d010b09090a 71
    0x11140c44081d204081810211b0180000c051101c0c1745954031001f250550f02c1492103010340183e4800e400e0b0302c21402c1d040e82c849039007004102049005800000b4040503800c0006105030448040c100750303014642404040700103011841074825000e441800744100869007141c0440d60350b0000c000904260a1101c00e1100c585c001954906403070203401d02280d4041c0040084500148a50321b5500b0131010310403000000381e24201075056101d518042c000115100c0e03034407a44d1880c01c00340e90130b103401c02001800b91000b0700e40e01c011090000380c041d45003100240721060703e0581c4140c800f45c0e100c0201da801040019080382d8000e04145a0901800e914989030002414060702c4903000343c229212140060a00e9909004580c0748100c02c400c00d8800701c00b01040e80f401003c060041da404511240c8020b09a0b24042e4401441804180e0090000014800c14171010790020301c900381c149034403a04074022180d40014482d206014038000051000c80301401c000700c01c84003510210403504116072030008 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 445582347 1250 445581097 445581109
    0xc0503151903240501030812100b16020d0203100525050f0703090e070c03031404020f0d060f090506060414040206180109030b0a05150a0803160f2114040302 69
    0x110ba030040403030070f42081001e00d910320386a5041c2c0c21185052070f00001104004940d000b0304003a0340024021079082ea00e000803145030007418060b50001540a00504102c181200c50416180344007809a48402c030456010074a400440c859000c14942c07904208101048a04a10010083c0003003618410f42140030001e80603202d810282c036903028001894500b854091032903030008000d000301440244c034214400400c42070303d503a000c4000905001c0c50b2412145041103081c01150010404103034440034404000340120401703001c403409502d400042a01441500c20a16010b008030b0280c80e2615000c000c0004a4503580003143d0456111010b000c0540c407203400359140b400c50032814002000c3d00800594030340405a000801f415941c8040000e51241c80c0c001d130340141045c41641500d04070703820070403480301e40500030004564800d010441c0307090040d10031410032070300403810203c1501c281c0d2030b03800c40104440d80e0000b100c1009031459001580c0000200c00f03103003440c81c0880c20300307096900050b8 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 445583597 1250 445582347 445582349
    0x702100504050d03140c0304030311060901050408030a0207170408150108120306120a061a040b01020f0d18090c05040302012606090c0c0f0f070f0f09050c07060c05031519 75
    0x2081107550310350000b05e100c03807034110b0380710f9400306003280c3d1265924035004040402000e20f01e0788a01a0401040403074005026035401203502011503401d5985100d0400c00942110000f0b031a031000258040d55404505001040640030f0707080503141c000d030340400314042a0740690124a582c5d01c0000d00c1282c65107454103403904248102c0301e01c0c144010744891280380c1800c441b07001d01428a0131462a014021402410090030400c0d1014440780781c10b9070043e601d44900143c0d0f9060b54101b00d003101a0030344200800808044440402d8100c10f0321f80d10f40c042210f1a000188001c0303172002a05105540c8c010010140303044000b07183c1c0c514802144c01da00781000b40a002140200d41c034402041c0c980d0018030035a074041d400202210a0a4032000e40b140ea111402c0d0880f0055002e100300101d02580d41800072000d0b22800006860324510b40341110000b0400208040b10440c0144038032000680c00d8081d59403c564280c0c1c440da128189140c0704504501c0000c8168404c48a00e0000320791550503410f204 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 445584847 1250 445583597 445583603
    0x1905090a020c0307120903212a0803041a06031b010309030504050d0f261b070b040602010501241b060b0604090203040b07080403091a0f03010b0702100504050d 70
    0x2680390b0407070481041c80c1d4054080010044070902030703c1414554016045012a4081c52505818102600e1003034064182c00303580394002007403521035214040a103055070012441c0c02e42518601515501c5e410100d400640d0201c81001510704001025003e200110380c1098045003e04a0305410515507e41c0c0d03155500c1030303414103458008a409050060003a0360003480041c1503240740092514100074144200e2001711341c03000c0e1610340c546180d41c0e00d110300c00d03144e011a060185000c848014807949081d140d070030400b5a00c180d0001140c07030020340303010b000100030680010815504003200d40018020403982e007115401181508070010b80e100c070052a04841c0b1612081511100313040800103026060307409078118400103000150a8030702c1d40250b21550080e0780300c0790243c513000001c80340c8070400e86d8003500099170341c2401c0c031016520484090142296868081c44d1100d82c00c0401b400f90026440300541c0c2070041450000d6003041e0081070300520b21458214a45030901c4001868071040350009 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 445586097 1250 445584847 445584851
    0x18030d080709060c05150106020a1a010f03060b0301020408030c03040f060203030402060f1606110904150e16030b030604060618140705130503070b0a0909050105010c0206090f0d050304051905090a 86
    0x3807045c480207005144c0a940c030000a515070350b03110f00000e50344031407103030f8101ca100f0340d41a19100100c1e00b01800c2c0e816142d020700100343c10340c915141d40c400b070700c90142c01c1541954200000164180c080004048051191001d140c0b143d1403c0181c42c02c031742c102d0b842001503401c108108030044c2d90307010032100c405084000d0182c03180141c03962501024841d4600400040c034103441024501e494001514030b08030212818099401e20107100c90f02001d03148039402c1b04000050120f000382e440d14107242080c6201e440d000a544060a00007417428034241c17010795480355140400d1001c07409600d00e403518000c41c60424004a01511045241c0d0301d401018101000808a01210600510713448030700248001800c0b11201521000400c569900881f00d10300421351803440041c40d803940303000311412194161034001c05034040760248122640076100325948411111a0400b0700d59a0a00300860b840c01080216240c6041c2018450018070400007402c4521900104201350340c0e400940e80d51249040c500 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 445587347 1250 445586097 445586117
    0x6030a1508011508030403050a022205010306200a080115020c04154101050d140f150904080c031b0610050604050907030b030708010218030d08070906 66
    0x18600402845962188641060000107a801c01c15000845202407002e107001c0d5280d51460680d40d82d03c40d6100c01006900007103500b0b00507184c06030181003860244061280c031010648802c03404c607a026041101c0e269a1101500042035070074071080002c81c0445c80385450f02205000103003012505104040030b01980e000d030085580e02c00d115411070480003400c00e0190a900c40055030a001c12030240c07040300a000049500d05482c500c207920001c10756808040741c3c0b0026802101003104036606100d05000d810480420881000e10032042c81914042d803850300307814291010890500040e2800805041b40c02110301e5642e10b070b804c1160001e621062041d42c545070300306034074154000c03400001000b08070240141fa00010100e841c42c41410742c4020f18070400c4d100c80070001c0d40c0c02240030b40c5400030f000f0703030004150741d011740d01c44030400c0d8000381242c001c80e40c0d4400860036a40300741ea451285001003181c1324106d0a00b041840355510440c242042e0910301444021309100d83c07486004104140244 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 445588597 1250 445587347 445587361
    0x8040212010b36040b010b0a050f0a020d0914100e03120a0801060f0c0b0c070f02040203070905040e0d0807050706150e010512010b0a171c0305040b07110a020603 71
    0xb00042c07000c10003600b44900c1d169405986040f490b0540d428000381000381c01600454664000298070071640030006814130f0342000302c41d4449030007840c00141070010802c83c00280c4415500607000c5030035181e00910070840003c400a115503500c0e8004d05400c4103601d0310020560b0360901c0c0c24502e55003454507095652000c03001030701e4040e1003090b580c001c2c10009002071201d87c1c4544001e050301c01c1c03900c44954914101c441192028603148002c2d2140f0140001304508005a00c014404a4041c800c451813170200e44e00020100e920a580c01c4000c108109401c07c03035814640900800b036194040684051443d150000d0400d045c0245044100040010402c1c00c0200b02e500c03200d40703110000ca9850b0a40e031180707245a03a1070000c1c010746200d4144039450080082c814040c089202d02c020305844030709442e0450138001c0e10346441456040c0c0c014003070007200c000204000192034011a0783c0204a600709070a013041154000340c980c404111062114645180740014030000c1682e05544480d640e1791a03030 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 445589847 1250 445588597 445588601
    0x301020d0207080301060801140102060f040807060608030d110403050601090915060b0301051c210908150604060e010b0f09061b1b040b0a23030d020a150504030804021201 75
    0x990000c292600c08a2080d0501031114051130503030310b5a446146c45641c071030000600104020804078016030011001075103002c806d4102a4000b4030401009040c2089552030100780c1c1d00c0c581000c1c075294008658911105142d01489903034165400b0105d103440c0c1182c4a4a8448005003e40ca401c1a00c40c0010b504102800c0e420b104503100c1c0700c0f82044403948400441c90507500070710501f4030582400300e030300c40042d180360740d1120f4050b404600c0c0d05801781740014410580c44505240301c01c0c0110300100041d04003040c071070341442d58130f035203205980c1f460301c00200300440b070306a0007507081070005d403005115080d490f03000c4966102042c1e010b50b4450200c08009545071140000a5610043c003196280c203e103000540c000b0304980e00700000020040210074402160182c03000d40b0341c0305100d42c004009040207101450103070b0401510240300c550000c0042454034000d00d07030000060b40100c1a4800f88a280310f403038400050103400030700130790030503407001030030400050000391143e2030380110116011025 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 445591097 1250 445589847 445589857
    0x30905180c0a0c020a170d030501140103090203100e01061509030506010e090102160308040201030506090c09061804110a0207060f0f180302040c05120c0306010804080c07050904142514030102 84
    0x2018807124a0300d404070340001c82c04c0341b500100c003441000f881c0704159029010b801d041e14040c40c8036050081250780110007400c0000410303a0140101d0b2056404041e0602825291341c4240d8008580c05c0c0c5400d4240d21255803002c1550100112011f0034400507202041c41d6046908031003414220341c440c0c0b06840c0c0203100e030401c1040d98104c5252150109a0040a110b20950003602c04012694942040c86814034080743c5240713100c60204898030301490010f000d082035145039a54402e40840d070402040032900d1886400d90741c144c000c640002c039260704010103805098240350904400782c01039800707481c803a0480c40c03000500c060147c1c0700d688030040c80c7d2240021a0000c00c18841004100005007941d8484002d419080c107140c00011009085a821a40100c906170746501c0c1c1580c6503100c00340b844d042200c50b041e203030264180020b0300f603484107076450040740600c40410710000149a031602c1d0801da00b0b070b504031040c640041488240324a41c01c100440e036204c00401c0d00101c061000900910070 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 445592347 1250 445591097 445591099
    0x10e0c0f070c0602010b04110a05070c05270a0b011b02240d0b09040f0308090a060f3809180313050103051b040308250b04030905180c0a0c02 62
    0x1c50280305118071040c504088032001d8008221044021040c0800d40f05820000801c00b07200b080b0b41c0e24054442d00043c600c8a0162203480701403a10b460004000007008107504d6001c8076125440001194110b401642001c40c1c14810449090f1303041c0068103040129114140c5401e841c0c0c2c0c18015521845c014070b0044000480312407116101030395825440e0401007880281c18600398650010307044c1610035500840d009030403e156519190313411141000002c118030400e0151084000005500b401000c14000303d000000c600c0301c4081d039030628010030400745440501040000c42d018902010020012041c040d16499415900e032071141c040c9180382c021101482c40005a02d01c640c01888a0384d50035030303800b49c0c0c050155444401c18818140e0303105080d05104a03007044100f0004d80f020000f00174000c3c500c4040582c0340c035500140b02511545031001e0703c0440c94101000704042c0c0c0116110003904e02169200c800105001c1e041c00000002403021a44400010f01c00d00a00d01940030b9000c0c0c20f0b4 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 445593597 1250 445592347 445592377
    0x18050a03140d020a032705060609090109052a220908040f03030c0204060b0a210b09010e160201051b18060f0715062414270405070503010e0c 62
    0x426a13100030001d014a003c910b0300f00d1650f0780354504c0c456244a003800c0c1581c1040c001c255940700c0300c040244001e400340284042d0365a5104940000c0c0c01032007003c0342005c04030740700c4140d04910071341d202d0380c0c841c20010503108449640418403962003000500c030356030500d0800010080d03220f1078000000d00c40d90308142e4030301081c0d8200200301544004004587c5100796424403100d6514000061b050041d4000034002c1b903891705c01c01201c1c0c00e04401e411031018610704003151a8038980003180d0001c0081c1c00105000001e2420841c0c2021642601c10140704148001c00c958035000038400c2c5e400d5080040312294250024070080d078641665004560004028078050f030703c10300d4900242d4564840d600450f20b1000b15554031599011034411502100d070303e00f05640400b00b600244040f9801000341040500030803920b01040d0a001e280a044ca40424002a5030900d01d0445024168400d0940c070911560810081103003944d800710589044805020000255032036242005005005051892130210 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 445594847 1250 445593597 445593607
    0x501210e0615212503060c081e10180b0307060f021504020307090207031b0c080111030103170c03070516050111030c070308091c0f0201020118050a03140d02 69
    0x518030707115282c840100300c4001d52040400d022150030342c40c803209240d0071074125214004030a00e80600710360700704008400a0304a1512a0785050458210b0f03104400050100801c0040100700c11070164140e030000c41c64249940703840c4416003151241400f501d2a8001701200600407015540c00c941c03040c500082c29580900e441d084024900d0590360b4142005114444200c44000050072045015a802402030801203003000720b138030069808070408501300495089100800c601c40010340030594842c1048016030b03860111100d00752208411000303d440b50400040000900409400c264003020311000c1d6114803440d656142140034401d07000d020307030280a44022442d0a08400d2005507402601d8012086106030300d034a98a01454207030a986510100041c00850401c0000c1c061400d0b000f0410400d2201c2a00480010986500204e80501c01504a2000c40d80c081c01040744001800034440c58400740c1e0b485440da83c07200d480c005000e0045000d030819410811400b01c030f2401d40c280c0015941d603 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 445596097 1250 445594847 445594861
    0x1e14011403010b031017032215020601060f02030c03031305070b0d0b09010f03020d061a120601080c0f030a03031e18062004030b1005090907060e04060501210e06 71
    0x383e03101311640300d403c0104640c046840c00c030310340c06d03c040c1e050040019403c0864411040d03915640c0508007081c0017030000c00000f0f892444003400412266240d0180026500d05907016050b0140040f0103c2950030034460507042c00400810740703510580ca524610300c54692828483d0618949400c40542c0c0701001400d0f980308103454102c0c44038010155808040350782d0321414038a4440c61404000d50140c0a16a64008034007190029030f11159103a103003188000021000441c5896440c07900c4403150003080040010740030600c80740d031107030b6819540d0204880324400005d8070f84500b110700809050383d81581ca16286614420480c4030502c880c020000e50340100c01090602c118032404903101030800c00a840c000404a83c129422800d000081d13081609507076850108180040040369880700046001825030780341c03c002402885c0c5840a02010743c1001c0005001012040155000b41d01342001004645d90080f081402c8080b882d0820300c1180050798807901510410300580b03c03610890092042d4 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 445597347 1250 445596097 445596119
    0x80901020a2a06050c0307020f1606030e010605040c1716050f0d020c0105040812160504050f060702040c03020408060c0720030c030115090f0e06070c17041e1e1401140301 75
    0x47c0030b10b80886260a64500220740d076400d11203a190070000502204002d414040d410050680a140d00040f4520b510349010508239501e488401c0c00140b40c20381c150951810001c80e15810040300b00d040e08442045070703c0540a40700d040710a0392500400990b2030602020b80e815503040f80315201c0203200d18101410090306641140e696200948203030008100c0401c100108440483d1507610303954242468001003104030300c4002a46900140200100c000503030f1a8030a600075015142c03030060f2680c0c20104a207180c214000c00806030300c1e0041226a0204c1c1c0400b0210b000610100c3c5222512400000464206014104040c0d0958240b14140702100c80d00b25500003686c0e8020300c01c005c002180a510025a80340c14003100803504070074081140107100302d205120050168411080b494250380b001c0d20b00ea80158001c0c03403101d00d442d001c1000340c05031642c0d400040c00074000c02c0100c1402c0e40b180041d03c0c101031156501c0c0c080d100003141c407076034020404001c06034035070001d480d169a074618580744 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 445598597 1250 445597347 445597351
    0x5150c0f0601030f03080108150a110702210c031b090604060302030321070e130203042d0308060f0931050106080f15070c020f04020c0d080901020a2a06050c03 70
    0x10900e10000030600b8480000c414070003c14260440149e070700d5100c0803038010000100c00e0a9180410170910015845a00c03082c990034000e841c406400e80170908010f403e0000142d0030354403035002403036090040b08507038545001c100c4040300d45140e540c4031000001e0090a9540c4020741600002c282c9194103c2e48540ca2940c8523019a6441055501c400c1d0480c2e49a070201580e0340e014054424102c2040b070300f0703806564000e02c00c0d0000e045e03031881190030707042030509400314034600c1a500b80c0c20401c142d40401c00c3e07030b000042a207141079035510780000a030a20ba0001c20001403a2444c1e036100540310003c410301e200ca075490700090400121a410304a0103000e0500400e0718034418180c040782d4400300002d400140c1902d00e01d000d0b901d46c881d460100d484400100341641d110156000948082d5220f1006042c03e100d8040103001034420407502824000c00240349002070392040c0840c00740391350403250f030420321178440c1c041c4040004054131aa007085242103015103880d10340030820182d41e050f040114 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 445599847 1250 445598597 445598603
    0x703050403030609110708070804050603010f1505090f0910030209090d0e060f07150e030f0720030c0d0303140f040c24030c0210290a05150c0f0601030f 67
    0xc002c0f01d859002c68002e603030b00c20b080540b440c1000c200d40380105242e10040c1203442e1084110034a0f01c0e070750300f00080340c6400030b8010040c4403000280c100540c0911030107004000f201810310504050a01e00007402d0b40e440b10840d01e000f17062000020750b00750442000200a0355000b4031000c1d1380d081410980d036070750b910b030a05880030601c01c5283c02c0152030210203484954030800032013441e20343c9984c2c03260b031403400048034043c1650711030304107504400c424005064988090f10f029515483c8074241003070307805403101c8243c15102690801c110584c40101d06040c11035015500c0740341005843c54200e006100c00c40d40c03c80040c4e00d01741803010201c2086940c501441c00f4000d0000000c0d22103d5a2440d102c6140700031003100e081003e204201da0082e0001d5409250900545103094008500441a80d0909200b40e02011445980c00c250354900b0f41c10108520040d281c80c40501d0804c40030a1405100e0780001c1c0058402080e0148070a030104180c1e118628117009440381940c2d24500b0f443c0b8034140210031 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 445601097 1250 445599847 445599851
    0x905010e011a130216020d050a0b01081f0203070e06220902090406080f0a110111060a061e0608010b18060a03050f07030b18060102030c031b1506010f180905070305040303 75
    0x800a00e002600a440e494860722172800200c5a0645c2040660345100c1d0703048500f402140140c4020460110041c5d0007004e0750409444100c000c80c00071110302400d003030801c0750344e8418414080d6103130380040394046030041607a071140d031040001d008001403410000f0940c821441e0f1880401c440004c1d401034400030f03809035001e0203026241e00000d901d40b00082742c5d9240707561080b10444003003024900810800d01045c1480d95040c0c080e00c00700e50600f0003c4507504501921000d0800401540d00c4030b05000c44000940161850b0805100034075060707042c814150941c0d000314264030810a28402c61102200091055039110000903020b00a00400c0ba61490071060200000f01c40c64003d00500890f0140144144500b082c1c0d512115400710700600110f0440c8010702100c068448104002c100500c40144028400b002003086140b80064101c15422406c800e48144407881e44c000e1110225501c1e00e00b8104410307904031001002140c069404801128103120130301c060386070142d10882c062806907400b = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 445602347 1250 445601097 445601119
    0x5070e0903040e19020405040f140c131a09030a0317010e0c040302040e010e030d060503060c1315031503080d0e0d0806010c02040e060f010e011d0a0905010e011a 71
    0xc881e100e0141d4810f40000054031000900c42040c0d4514003114080768540040c20503807a80b000c6811200c8002921810710781d645d1040140c100d4058019a00c01e14181b108d034601043d502e02c1c3d0003448464480c0c403d038480200394069154940d54240c0c0c00343d02001d000c0310307010303031032410020010151a40c926600482541c00883c04549a5402d03070722442c050601c061424bc6103500b403000030030b07035080f60300c80365565000311007420001400180030402e542c0c072010880301c0c10310003094104013000d808400c441004001c103414010320b51a54604951458100303100240c0402c1e000c4d0080e20102451340301c14107002c2004010058050007824016240c948100500100c40d4111030361005001041e00c0465245000240b113580f0500001f10300d148041c0001c03030b5803c000858649020010766401d69100103440060106180c580e081c0c0c1d00410000e90041044107400148104d581c002a142c00c0f0786a81b601c0c015000c1c00400d42080c0c5030051140c00030400c480660320ba0b00c0890108920062040310074040c = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 445603597 1250 445602347 445602361
    0xe0f10080109170c0a0609060f0c031503020f06040906030804140105070b0a050a0605060309071406120705030a140a051504020a0203030604020c0703050f060f0109060308030412051605070e 83
    0x1003603021043e44070103180e010344085a5000303456005100599070511a20700c1203000152180204242d1920448010030308607201c008080941ea003c04429007054030b4070701490900003020300a441103c0c0c061750f2002100c000e01c0007103165845260400b42c0341c203042050010030032410744000c20850b0702400303002041c4a08900110707207034844c8a4000c5d1502200001142104800d5800603811801c1504001b500302d80d204003285141d0000c656014880d040b80408211101e24015100c0c80c881d01240d00c0d925201101e00c07400741554015000004204012000171880c015941c00703c00e030050410328551041c54603450300e802801c011660b4061882d215a50100941824020b0b162402c406802850030350380c510062000070b40003980034060500c030305880000894014032441c0c0d1808410006085985014a002d03881e80d6010303031142980e40c1ca00030382040401c6000044c2d94019900c1329181c0703804040880308640074024070001030146031003a000d000402400051980440f007482c0380c8110385030382c0c583e = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 445604847 1250 445603597 445603601
    0x18010212040605030415061203090f170304273308030d02030406060f030b1005032b0c1e031d15070507090203101811090d05070e0f100801 61
    0x4401c48000c1442440803600080900b85030240c6a10206e0002965070f9444844105e00503440c00160040307103190106001003a40320075280c0140c00d441d50303c12444048100840c0d640e1245120344102d039104451142200c02c02701c050b800018103440340a004003184200101d02000401d103c00c000e41d450305c40c003110107078910034054040710310250240d421b05c2d00d00d44004002c0d601c020401c41e2103598415000c03844002030f403181800342d40184040b20f01882c1805a501200d030179034019a229034170904029070103001c0780302440e0514200800b104008034550f5410b0b5000c4442807401007060f440000041070071380d0000036003403005000744d40c4d584090040c1000b04604002c40c81d10a50800e4502c403100d0280000b80380200b141a100d032085032006641c4140e008120f8006641c40700095044d2075080120082007071029207070030707a90704040198508841c0c8050341441a0142c0703500a101c035180a805101e0240080c80041c8903100c414042407600d201d010084110488006d882000750381c10203d4155414 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 445606097 1250 445604847 445604849
    0x110a0318030f0e060c0f01140c0c03030402060f09150a02150f01030b13150903030c030506030607120908070605040309060c03091a0c0a06290f040b01141801021204 72
    0x16107446500018a0340c049508155440c90203400500420080c1c8036140c0070071041180351403100001544641c000184255148080c0000162000c18407500c46c4a2b0700c04800c69030080d5044401940d100d04640322040c0c94080d140c20240d2142c0c00034070618009208400a14042440c2e50988004074108203001c41640015514200f6007900c550045c40019030901c00b480d00540c480d21200000c540650f140311002c090141c030f80410540740e000e80002c060300b41c000c01c0b410f000c01781028003003450060b0101c0d607607460080901c010440c1301c0561050030394055100c1101aa00302070801d5607400c4500304503010f1305058800300d001840c501c9000808912035551440d241340c2c1079540c544001c0c034100c102070406c0d0740e45090550740402000882c6c0080d07010010340712043c0c82680701040c508016948001100025041a4144e01e4140d602c003000c0d07038903074407845103400d4100c40000312480880012100740f2280142e2580600000071601155030000038030101c00340c000da003242c22030403900c0b060031614025 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 445607347 1250 445606097 445606103
    0x121f0209012f0607321c06080706050705030306090601031803200d0804110112090308040312020c0d2003040f170a031706041e02220f0621110a0318 65
    0x2c405c200254012050184602040e1007411850500703a1842580c0b007001043d6466a01899a40008000d240c0061001e180241900e00313003542004900d031141d6417a0320009000c0c40c4942c0b03541d000262a68060344c803030210100301802c2c6400c0e807141442c0242030f02e0041320100d01e40120501862034103c8002880c5003000169584031080c40c1c645036104e003c00c140c1040003a060284004583c4100902d81c456420000e000766180702c0c8509003810080c0821440c0208200c02500401c121903040e00d002a050984000350320b46050340207406c1900d840318281d40c480700342040c00006000200c90300c0c3c1c0002c102c250303128082100c98604820310216950b11582000a01041a599156541030301403458241d01c094041c20100d494182e03164000c0100d11088003210003640d000c201c0e1000c2c3c16441c045e5280040700840944c0a681c00c020401500070280e105400803c07800c0c14424864110701129440b4802c1908018000b40e5000b242d151f2285d0005142c0d00002481c0409180e0145c511485059074650 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 445608597 1250 445607347 445607387
    0xb09010f0f1202030408040303110a0c05100309051c09060503011202090402130c052d0706020c1612060b04020a090e060a0305030f09121f0209012f0607 67
    0x440321005a41c1030344020307482402d1124020740b460090219000540c891842042015611800c51502030000c10140441e1100c07940103018410002d0404011361068600c1103507948202003103501d00b00c01038062030000400d40e018503c07054100c01d1112100000110113911001c3c030760764441d00212000d00091180340b00143c2101e9150015003400e92450760480d00140c1000d0000b00303254210010b071504680d1030000210006801060241e490128000c02c100719071303074080c5500003201c11241e1409000b40113082107030300180e084010071040281c0d0302c02540c1c0d94844101030340d6411b00d030102c184040500b0b5884900302042420f01c0d14152080380c140040315180c4c00801414035014a0b401300005000c9500400074000100104001300301511030b03c400d031001c403a511a00e11080c40801d01d12003400844540c03200c41d64005452082c41c0700e040c0442d40000c016290046d40c00100c0300b8100022121240140030301e80350201d01803ca00040307032180c441045402c0c41c3c440d42c0c800c956007640f482c00b00080c10 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 445609847 1250 445608597 445608617
    0x61314041a16050d0e030a08070806030309010203030619080a03020d0206011d0712060503070b13090204050102060a150e01060305041406130816020a0b0414010e06090409050f0102040f0e010b0901 86
    0x43c0660090034818411540000711400c1090046203942c0c0500c02c0c440209607080c08100d4001d034070041c0383c0d03480f541c158003850920300e01c080003039501e0001400e60b9200342e07407074810070365000c00061200c801040ca4408650342940b02d400c01944400c0c0f407045500041c0540000481c8080c482d2980b82c2100c1e540a2001440b5a11240c04a45c8070a07918601042d0340d031902e06c00141c5070741c10040c0c1f101800181c038913030b540c03030b0400e03000343c403120303005500c590100b0b40140702c00c20040e80c000c110700760300c400e0090020401c002580f0081102c0c400b990024100c8081210004c10040d0345503110921403449030103581409c0d4010041b440d40d1351030803500309210300905189040014014809803000c00306808003100e560405d135000070b5503c0020f40100310813180114040200c1d2400e8880c03035101d0102801c3c41001030442d000411528440c0d181c1186c0240d0b00c0d10700c540c00704182084001c58800c000300007107403200d44901080301000031504c00e60351250554070010400a0000c021034418001c140c55040307800c = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 445611097 1250 445609847 445609891
    0x30b1005151b060c04081b01020c12010908032503060b03012601090503090114180402160f05030301080c090108071505040b1c050a091208061314041a 66
    0x95030114001c182c150300703808164400300d5400c10909028070440e666050700c071400d1001c400e2810000e42c05103912100080c0140b503050b40c010071601145d039030a4a240303258052440065005d00011400104004000010003c1e0300460150007442551401002d8a000c007107600220140c0315070b80070b08407805804100401c10182c90301c1b44284c01c04044000c0c9500b02c00c40049890840c4c56510007900d043d00001800c503419a0300800307000254400c1c01c181400d181440032003070303014010801441d00803a4009001442211a101400c5000d5441440a401d02caa07600c6c0c182d03201e40080c070410b00701d4070840b251f98241e49801c01105068904c000c2c010407140c0c0c0341c082d5046100e2098443d040038014100f001040785804c643c000c0580c00301080191544a00780300c03200c3d044440042c040801c051400c4481000101d887d16811101d60340c03890300c090603403a000c001a0180c10f81018220001c9c0c40d01258444500c1c451000600c1603006014201228044000d030003081e010845106030312820040e680304c0381d = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 445612347 1250 445611097 445611139
    0x504020c010623010306170705040209042d06050a0317030601140406050c07050d1211070512010b030c0d0305040911070c03050c040b1c150e01090b01030b1005 70
    0xea032a00c180003040300c40e5208510389050f4440f00800700740140036008041c244d42c050042e8802003503407080006585401e4800c25840701c002d8003585204540004810311150f81c0ca42120344c00c0e0300c042e008040d00020000c01901d00501111403c0d0310341c0d040190000d40c0d80b4285080404494000e80340740c03403200340b149024a0580c001080d460600020204001b0441c04c8500a403010301042d484159076610703058407144c5069417035030149205420b08200280040e03100050709000f60b0003800c040042d2801120f401c0d050040b65005560440f040b08041c0603200b01c15000b1004130581541038400012484080c842841a145c1b8080c01050f000c220801184141e030b031000c4001e44035224801e0074800c007581d503642c022003240e0041d00d483d80728294540007850b20340700d150744540046481503480440007003612a00c10307142c0000f80c450011181c0d500c142640c40d03000609940703000c20003000790020034640b540d01c0f0361003804166241c0403a100014110010503601c241519402003d03c142280f07124501c1032 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 445613597 1250 445612347 445612357
    0x606011706060c070b030f2a0703030605090c07060b0a0f05090403020a05010c050703020c0108011a0f0c0d020307051006081207111306061112030f07050712031a0402090a050402 78
    0x1400c800c00f004200c0300410b05016400140401d2a05107a807410207407d4281100380192201012440356150301c945203421604031f540000510068581300c0040b41419802030080358496038011500320104080c01da020b40042002c144902c204200035040b139400c0c094030354101d004800307401310b0034801030129142014400d0381c804d10a1044800c1c0f0841c541c0e801d0300759040c2000341c402240011070420101601131200c0b0659510038646202c1c1585000c1800220341c5081a940c403040c440040c0100b00d1001e030004481c0c580c01d030301c01190751100340050006e589a01c0940180c410340100403803002c4400e910b000b101c04440203c00144402807006c505a215030f0b118020031660110050b50500a6499003001403110010703000001491034505035024145004250485e1a41d8000d01c0b5078214100011080e01e070000460201d404071580c07020f00c181c3d40b0b84110800640710030600041d00722030f40c1e0300d80c211740c030b00c5060007d660f42426020414401a4003480310300a40c80111088107000e01d003000d40c0940 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 445614847 1250 445613597 445613599
    0x90a140d03200a030e09010905071e0306030b0108061506030403090510052106030105010603090b160908030d02180409050a060c0918050a0b0906010207060f1701080609010b030606011706 82
    0x4414110b805145000307440310f0110041400071500d1141032403e60002070040080c940148414540300b14000c080d1802044100c002e0040544030b556400e10a40c007240113154003203060704041d61500c0b0501e1344c1e01c20460f60940024a03082c01e001c024280f0400750f03802258940c4a50000e00c0c1408208a1001d4004410504000c802d005580301d00780050b2802c02e04140310a00e0074894140b284c20705003900c0301604104d06041c100002070000031803d032440c41c3e015203207217404a2100f024000407181e0600e00d521482c01c911020401c0040907030b40d0340c01490b09000d2911050410000c05050005440c0b808201801d250041084075000c034206422400c0390440c40d00e41401d101d6191b40c41d00c031a002c089522205e015070744004200c0342c0d200f54481c24410301d0049800c24524608400000e6844c03c29004160412608049907401203008181c0740c02107088040e900603580da1112a01c981e01c0c4401c581030403043d801d241030324016080101c0c0b0b07140a010b041c3e485504d14000205c400c1c0482c44040d0241d = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 445616097 1250 445614847 445614887
    0x1e10170f0c0d11090f03011e0905030910021006060c0b0412031b0203090a0b092202130e06101e0e0f0d050102030103140c030307030e040f050903090a140d03 69
    0xb0350500ea82d14440c804080c0a52128192100914414003202e98032014001d402a8900104900c1c01d13550426428000d03c074205e00441c0b00c408919150703066008030507029400c4007113481503128030780e0003050428449010351020032404c0e644180403110000410805050a139041d0046000308804100c50326404805080214070314401711281a10882d20b4070001e00160404160300d102ca03d4074045c8000141141483c140c102101c140000d0000a0102e058005400600038038000340b06c2643c0548002000800310340c1e042641e10004c02c00c8181048178002e209040714038400d28182d02400c070071525207806500000a065008600b614140c00e0741503000d9110181200792003483d034491100081d130610480c005600e9516500d0702c10071640c0080c960666941182c542c0c03822585000099900b126054580002ca544180020500400c10314624040b420b04000810480d010004010450840c0c19640044203c0d070760308040018548441190350700032460030705040800e228452001040d4034080b50 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 445617347 1250 445616097 445616107
    0x130c0e0405270607110708030a030b010c0c0905040204061d0103061508011b090501050a050921030316020c0111070e09120301060c0204060e0106080714091e10170f0c 73
    0x2031541000e0744441e03820b0603801401081080340d840313420040302103140001461454200380080fa12800b40610700e000b00369a8515001d250b030320030781e81c494905401001d0518643e4880749400b024001c00c035400d80c0544d081c040c00213000520b0030a02d0403400144c206840080e400e42d13440d0809090344401c0c3e41803122001c0c3d80466480000c0c400c081c2c001201466489031000d000c4400344c41140b890344180e050090038400160700a8200044a02030b2074116040f510070401042c04016080c00c3d940224800c2c44080100301c00100c81c2c1c548500c046405808032451154204011107041184c0e0751415290703004900104040c6180405035030b080800c14060321820000404041c1060f00300743e0012001420180314101581001c3c45008060310340040c082420390704003080900b800d0005402901004050541d405401e428441900d18240c001406614515030802d0014000c108086400c1e01c5031a2203005890708a00443c0c021020304c14070b07517070a405580e4840c1a840042c00080003400c00301d10401c2 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 445618597 1250 445617347 445617391
    0xc020c041a0d060c03050c0f0d0906061e142d01020703080a0e010228020108090a02030102030403080f100b0412030c0210020c040e0102120613061d09150c0301090207020a0801050106080402130c0e0405 88
    0x503000d4dc0c0856409114141502d0402c1c005614117101040c140204100d844402d081056070108680c8000a044007406080c02c08004074509000c80c1c0c0007405082c008600600d40c01d034083d030394904000c1c0980c05c0b1078101004e03117642400b021592000c9000701c04000340d82c030015401560300c01e074001b44031410b0741c4008245801090076a4400c540480000f07000c42c04014036000055501c68000c9440869600d44a080010130b0746180700d43d010700440c4002e0582c2c41c0d4201841b440ac40200d16a02030003180b22004d0414004e959501085e4045e442a810045040c002210502c26940981a1101d1085881d01c032981440fa10040300040c0b032070040d864003004116080c0344101c2c03c00500c2d105494203414a00300f43c0c030500305064400300300c03500742c6a0018401480060026641500c56064005a89402610001c1d80010171275200f503180f5401c0900000e0384076084541030303100305c3c0207a41c07501390040001c0442c822207009020400100b00b00c0080b080036414980d0000790300000080c11141080c1040b0 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 445619847 1250 445618597 445618619
    0x7081b030c0a0f0f1e050f060c010914010b04020c33071e050304050c011b05060c0717030f04110d02040e010905100c020c041a0d060c03050c0f0d090606 67
    0x1822580b590400018100041480034a00c03400a201c100c02000d10000c00e8540301c0c5c203210513441500d104030030b009501802a5030b09000c407001486028006c100b010a1303403a06982d01c140b040c034030102c294a48071405145050600031141444200c9010b488050722001400702e03010301c080002d02088540d803625103000001511075034040c413070750381328140c540c050a80f19604140c0f90a812000300403051003488002140094a02a444400d013402146156a002100d205881d1007201400078401c440511201c50043c1004080b82030007075203030303000c00e4400d801322038a40c0c803054800500c40e07056140003e020030031004401d00c080500a007162130241e61500010103441e03001200c400140d554110040c2001420041c107410b0a1020409200e4103001001c0030b51035110581e01c0714003445d01c50054007012500341d00c0d140501507000b1b118610202c0a41030400003000e2540150011a2403c0081840100c08005a4030940c22810307610b0700d000380c2280748801403c00240129222a1100c1c00850411081 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 445621097 1250 445619847 445619849
    0x1302180a06020c0a050604050907030e240103150903120f090204020705011d060105060a0c0f022e030605060a0c0317240409020306060910030210090311010207081b030c0a 75
    0x2640c020700c0e40d00302c0402000486407896000758861b010070002004692035001c11198041e016003400503010741800e401c00c0c03d001c2d003188080207241e1080381c41800c502c80003000c0d034141c80c040d540d05144900211841011141b05050240104030000030451000e401078226a1070180c450202240c09405130780828180d80068000300c916944a0100010904000e03802d00f1800765018010310995142002082071803085610503420003c880d0034440600820500b0000010380c060001c085c50702121062070780a414a40046c480103c40320040c002c0c140c864000c001c142d4030014003151820542c40003e44410031442d1080b0244141e081003208050905203d06115002c20b49078082a9004807428000030503015042e80c0c451454009010090385001502550109042c0d500e040b0303617125489241d03103201071035000a502808130b0f80e000e0b0910f5484000034007140d00c507940d40304480ea40603006a8582203540208440350f030104c100114503000800c0101700d081c101800741e801c1c811041c004550b80d100c1c1 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 445622347 1250 445621097 445621109
    0x9051b091e13020a1b030909021612080402090a0603170a0c06140114030a080412020a09180c050f03120307181e0e0411090604060b280203091302180a 66
    0x40030412815050704883d1440d090743c10701d8181105170700940d40281c014516401041640c5501082030310808060b41640914560405030000400a070804000c04141d42210201d0144050101280702d100460103a181a031b6444100f041140000c20b241d520385410100301202009003142299000c40c101c0d108880c0c90750065503400380c15606101c0d034000c1e0113803c032400300d0003a445411400c0128000e0f0382070341c00303a401744e0040c0c0082d00068000220034603003681018810300e14000300c010481e40081066144944286401c40c0703030603505c03002c020219035161003030780d00b54200748030400d00d00700210000c40e1f000107030381420007594036440680105182e05820074400c200456034201203040180300424010440d03418070241e14501561140e2000c0c4101510b2801031429502240c0c5c1542c0b50781041c000340c46d071400c210341c0341d140590440d11100750089542c03107440d440244150f04030f4070100442d1917508001d0680c80700f00c1d9850040c04002e6206400c070a4200560141612890355000c0940c401030007 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 445623597 1250 445622347 445622351
    0x201050307120f090b090d090b1602031b010311030c1207050c07030c03050609030c19051c03020d061401020d0c050a080c060702060a0c090e0702012409051b091e13 72
    0x35407417034070b08014032015007040c0c800e034040500d0b83d0300158080c1e03c01c41500e82c0d2a03022030b100e04200c50748105040d0041c500031b5040c0220680030b218120400c6100d0340c401c0d000d9a048c0580c0c0d00740c409420b2140300c01d54a03401288410031065184040584800390000c1c0d44d032904625059280a1244c00c024040c0c004558400314607134200203004081202a8201109001540c6860000b00380a6a141900600c442900e113240481c41c003404820300c4a10f4413503201c0002d64000e1101402c00900951012000101051030075002080c0c281d486801c2411914040e001080d0a062114003a102100c07800d204403080c3c030440018000048074503000c1d000d080240c1c401081c82e4180000c0c042c0c20480b0041894001510f80f11244120aa01c084070f20100c0d01150060784043d220400c00302d024003241400541e000301070100b010a13080c0c120102800315001c810b010480d0391103e1842c0341252100a51001205106002d100542d14210341d41c18840d140342c4070000100c1d403030304020545105888944100740c43d = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 445624847 1250 445623597 445623611
    0x2313120c0312020a0801120c0e07030615110309012d0e1002010b031504080c0f0d03141005060906040e0708040606080c1f0201020906070b042d0201050307120f 70
    0xd504482c04158050440e4815820306030348801c001d0a8800510404180c4140800224140004010f601d03003e8401d0300c0c4400034a00e0400405005054a07100e6495801080031024200d90722590140c4903000075040514940b41b040d0b001100c1540300400f0040700c4ca4000d1003041403103201d5106101340307003455448000e2030180200403c1170706c04034202c0b02400c2d641810140c03c840d0303601080c06003078801c007400e03070001507200c60403c2d800038020b07114111441c0c8103120900c4e40600d0002003c162102d070aa07000d01046a40841c007101441c4250740d000254440e001060009281850103083c1421000d0400760805581e0700300c00034560002c0d00e034000403c0d03080d0140018001140a040d0180c8000760080c10304c041c208005c2441e001c100d0818010818040c44500d840034400c0d0100d41d1075810040c940e41d114000740c1401c03d191503017030798200c80c4036012b00c0130315040d075201a1494045000c3c41c0580c1c0d071552026001900c0710303132000700040108107051500940e00f020034070a400c05080e80c1c407400a000b07 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 445626097 1250 445624847 445624853
    0x501120b2d12100504140d09030516080c13140403050301150c0b1501031e0e0f010b01020d1d0402040305010213230d050c1f122313120c 60
    0x10000038076080c0106011031038003800321400105004812240d9800081c6566030f810041010f44030b1648040d602e0241080d10032103280d00c1480e4509403409802641c01e158580f41e00300d0712030559480b9880382e50b00503400d00881c40c90012a102001943d500340031903183c961101510001c03200b264202c0108030080014891540d507100428548203c6d402c00c400301d040c4645849100c0740004000c864640540003000c81d15910a03001900031000c6400c0d0742807804030b65140507010b0952404038092910607440780b01c840440501800c0d0001c101a0007074031070340030b0500080b107900441c141820356842c034070741d0100b205495910050005500400006803125404825000b16500030b80c01580c1010007038280c2414440303d2001110404030454172440c1d900e0303c600c0c1107800e0260001170207038030124030a000c543c51001d0302d8404c2c404102503920310031000364080e9803404a524003c01006080c1180142a0110003003004450f040b03864030711081001c059584d20b1a0500c4401d0050300001420049901e0070 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 445627347 1250 445626097 445626169
    0x3070206040510051005040515030d26060105031303140d0c0e3a050604080a0f050301030c0605091c120201060608011a07080c010c0206060909160501120b 68
    0x3c001d982c802d22150615a2504404503011300581e40320b180e13141c01081148085204010344c40e070010301034450982050344050700780b00c0c41e030300b11503082c1e425072011810020800740001c1c490001611018195101c40c00c0340348031916400c50880a100c0d56680e5109804408006020410b00300c000104038034144000c000c100189165040d4080d5400b02e081080740c3c040c45110100e402075055030b0780d85044014100400c884127083c40a02140910024003082c4034040006044c50141503d8101d4482003222080703880b84401d00c400307071030365400040600419100720001d05214000614090089000c0101e40285a094007011200381240243d41d03000160280150b000034100d071700b080d01c182d44c5032408500b85078040b00d81d04400c2c2c000c0080c904007002a00f4054405d810b408d400200300440c100d08c1c02955512090f80e4680c0f081e442030b0300180441c5000501e0a5204101d03600030030301c052404005540502903030007514021501c0d907500e11040c2d264040d40d00389840b8030315070001c0e88200c8c503811209 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 445628597 1250 445627347 445627363
    0xb0415080601020d0f23070209060102152215090303150b0415050f12090606040504020102030a140906070803010504050703060305061504140c0d0b0a0f0608100b030702060405 77
    0x910410340208441e0780c0c0c01091420f240c82c25070505c041c005c3e02c0440110f4402040143c1640000c8a2a08407820b0030b00c10005485507a109856100c0e664403001d00680c0d0712180c00182c3c40c2190829000619440c1c004000c1c82d0403171800d6801e03c6842d902ca81c4d0b50a0000141b40c0c0400792003681d0740040800c0c9075043c02810030710800d070708010300d9284c20600346000070701c12402082d1180c002c200040111611490031510b132012245051600c40701c0e0701040340034000c000c0d501e456882c45648042070075843e003445902d0059605130001c500e0808003100c103817003600b802a48001c544d4000c0c422882561614001401998400e980c05036803903041404100c110741d00a8a02c1c01014544403050002501c000343c0143c01c50004000d194107803d10600090282082e01c1000c01c2041c14801807140c91000400502a014143e800a1003d001e00c60b0030301c0303510703011480740708200c6a4000b410007129028045454004c1d1456040c002030a8031150144080d03031058031104010f9000000b000f0500038140540c130 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 445629847 1250 445628597 445628639
    0x2a06090b10121b0801020406020f070b0a0c0209180f010204060224010b03130f0606091a0604090b0d050d0c02090106171815100518040c09150305070b04 67
    0x30080742800e0101c1c5034601e0040c8000d160600d0f114003140c48002000c9014014952000255911074a40400039100c42c1d0081d40440c1d07621a091012400040c8502915040740203a540c00c01c4400b529002c02032500c202402d44040040d16041c034440042040c082031400080010000d6a124903043c0001e19000020300784070103c040103010340504200c1d0100d4681162000c0c1d1055849864642c941444108090340040010800350000403c01042e90041011500d209030b08000450703000c1780040c00071704107200e615030105082200f8000141c02e0307071100c903107138a000c2e0450a0100c420780c4c0f035900e80304100c1c02090210b4201a0400218603181d0205c030b01401883c5006c01404850035260704071601e01911510380812601e1707280005107010009102200d4100c40000b5240c10300340c40001201c0000c1c05050b00804460a1010740d040e51890035a00440c0c0c04585800100d140840c16001070203203407410005081c1c40d507400404a8001c20100000c1e14041030036641d194500325101e110585410400 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 445631097 1250 445629847 445629871
    0x3060f060206191d032a1c08150402220b0c030304030e153408070b060109030804030b0f060d0f02280e1b030105090103032a06090b 58
    0xc250951a01e407118800410b00c040807440707065a50084c0355107540001d60b032400340f1020640030b400300d030811030310425424000003c8040c12000f800e0700d9192903800c0031040d40c0c04081e0714000d215510505059910445003c80b0391a101c0801000605a92003c00c0749964840c0c003840b1403006003800008a030040c00d200710390381d00c0c03c2006400c840d00c9000041000c0d00740a00c0e0710f4004020307103d11808490041c8150f801036a1030a01400303031050f08480c044440c4c1d200450340340c03c444c8a00401120501c1c581c06c040301904020440e40e07002c600d040300514040c1000b207a65800000a82c0d04005440550701c00e200c0d41e0b80d10329020b55803401c0e01c800100500d2203110120840030101d201d00603030090498058035524905502039804002d0001e4461301c0381d20b00d25840100180b511042480180144103808003040104190a40800da07800f0a02a40754003183c0800100001790082071051800d40328008184410126101008409001000143c07001c0b40c84264440411124800c466807100500c548 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 445632347 1250 445631097 445631101
    0x207030b0a060e0408070503041203050d0608071211030109020a06020f01051b070209070309140115090c0e01200d0e130509030f09210a15050708040f03110d03060f060206 75
    0x40c03a9043c00350003d0b110200c00182102440428402c4074007030540201799840d04000c40c64020055405241e808030018505280800c06c078001280000032074a0960009a032050360362152012103054a81076170f031640d618071002300141c64a001860007000e10350041e01184c1e0031008d00038251000141120402000c0f00c621180500485d010f85060b540c05840384403040c1c1e1501030030790040800c8034002e4a42000d41c0711044941005410401801103104140d5409544c0c840f040c10540f0001e4400f400481c0740c00b0040c0905521035525480b030340c89039a014220b070340030100c5480d0401214004d480d0010b008004080d10303504003801d4102041c0300300e030340801031481d2407103d141c0c0b42d014503441740c0020308c000500c002d626074500048002e030740955060100a01003008250345e039502e40c0c28023181c161000b8188030600300d0b018420b1368801e5810b80c0b200019542c50f9030b1707445044c8d02c4030071741101800381c2d4500c10303240d0507403c111b216051241c5480006036542411048039040411343e10101c119880281 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 445633597 1250 445632347 445632359
    0x1a0703020d030f090204060e07030f0b0a031205040f090203010e0c0a020c01030b0d0b130b0c04031a061807021b03010b0105091207080f1606030c0e010f030e010c0207030b0a06 77
    0x40d11041107101450005210700702041018003505986a01941c01820108081510080c000e032850084026032802c12010b06106041c0068404107407025500034240801040070a00c111003d506041d41450814685504d401e00c11220400e03a4014480040d404801440320200d81d84075960031115000c1c000c0d0400c0401840256640803002100b4100364132015401000d80301c070a2419451548822140341c0ca1404215150440d41c1d50351090b1103208429000c9244482240c007110150b90b0840302c00c41c003d00401d20080d00c5d00b81c1c060220f42c0c1004150740315198003811000c0c400c1c091040740c0d0140203944070009130710302101e01080400340b10303900d00b400041803681c20004592004406a802c3c45144d1480c0b8216400d1840b5688840c0103405003c000140151000c24070040000004e2801066551905011001c444403580d0200110740c4440102c40e0960085200814403609842d0209054894844c000d080d100f40c19040f2001da402500184104481855070540c408000b240400c602403401d0 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 445634847 1250 445633597 445633603
    0x109140105060d0e070503030a03020d05100b07030e1c2102010608031b030706020f120f19021602190302011101020307090312090803070b1504051b0901021c091a070302 74
    0x7441c003100e15544e0710201a0580030600014000381402410b80e44c0341c0b0305280c000b4019600c40c3c036074002413500d0600010f040480101510382520740308882c26013440c255a03000e0300c02d1141c20400340da12850324454244544a8000c45421035485861146440c880c2540710301c0003144402000e40559041910a00034950000f0650f000502003140d0590245c010300d0303000341144200d5501074026030000480034a0304041c1402010035217800d05110b140346d525a900c005d800081500c0c04c00040c1003d001d05001d070002900541110601100c116400f1103ca9000401d01b440f801d817082a60146a40c040040d50303000701401c6555410701009500c1c0d03141041008040c0c0c1d150740802020540c0004004009511404445002c1d00302401202d40e01c5c900d43c180070b1442041102c285203985640d0440d5412810b141c0a020b000340c4846021a02c841250700c1d910b00307075030040300c0c00c00c1c11449080c1520381c3d2113a05801c41000c000894860540b9641408803034404004522080a02c036a420009400026800 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 445636097 1250 445634847 445634857
    0x510021b1509120303060a060f0203030c030601030b041a0102161a0a091716090b0109050402030c0f030f180604050619061e0824040b06010e060c06010914010506 71
    0x1200c28890600c00814001c0c458014075103041e8000d186680c4000e40640300200030b40c040d130301c111034040c074050360346408407a400002c0c642540103800038004a600068000042c2d50042c005040c00f04500351610080340807154500301c0c4a80100c2c0d8040ba008482d40c0501000320542c4480c030040f0394031400d00702c01d07454000c100380800340c0e51140092401100c521401440001d4064a4a201c10141b120913400340e40f40003801c010150810b01c01b100040010b0240b20f00c03980d0795010b845161000e8603200400000b50801444a01040c200300002c0c0c1c00801070310000d61140300344552100302410040700c1e03428a407489840e400f903540e00c003000b400003041002906c2c65200550800060202c3d4810f0340c1e00001e005140d20001180da51144045440d110400104041e20300900440d20300c07124007482405542c0008250421050362403003c00c3c0459051076002d503214206040c03100c0a940d41c9004640580d06c08a188461500401e00500030003000740100b0880350b044452001541d410140040c90074452 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 445637347 1250 445636097 445636099
    0x905100306080a080d15120c17060a0c050d1e050105090f0411060d0c05121605040501110a020d0309090c030b09190902060a020d1202130506030705120c040510021b 72
    0x40460380e058440c0f034580020007500f50000c61b07011160794541c601c10302945042d408030b403070204044010030040c54840001088110030300060015407508032040300180807140c00642040410002d1824041803406409004040c4041d0154104410042c41c170807184103030450791041c0380d90003e10812540348055240c0080c0c1100d07a10b0003003440340000600910809180392685400d0084403000160054003411030840340c817100820302d980b000c4001545152048000e008500140b205201a500c00c5290500800001c0c003207940c10f20560300010b243c0172070500d013280020a01c1c541844820158060b00f4005c4d021800c0a01ca002540f00009010207401083c2d0300b04907001c6a100d469800540e080a816030390007801700b03640c400304060000c1d12540c04051100c0464803110034040030740268400c135004164040148801c0500b45000c0114075480500b4a208114050100c0e00840061818040c0201250445140d641d403518040c40144200c01c0f80d5030080d50081e003c0c8640f0380300c1c40380c40520301500c = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 445638597 1250 445637347 445637363
    0x30612080a05031f030b060103051e1f180c11060f431b0804091d060c0904050109050f04170408060907051206040512031909030905100306080a 63
    0x1682d0781100d10b201e060444800c66003000c943c4c000051040900c0340364064403080e81c00b480143d6414441104038a14010081003400c4450009610030741c4207240000941c0c0701d68610098039640b04c007440c1c08000b000c41c6e00741c110303a603d600300c0100390740100c0740380910800c001c090300061402a1040700700c043e0080030801d039113440d403002a5080e0b8423000110300f20031b84821b0900c014005100100c5070401c1c0b042d81c890203e03524051f9002901036100034a6207845d80055032603d010b0408078142e0140c40c50201075510001e1512528038442e4040c040c41c1d20440c010740e0000e0320b0f090880304020a40b201a0720100b9402d15103803d03c081181c02400b07075a40b0a420080c1e0b01c1601d1000c0303501900b02c5c45503601c51040342c0250400d2040d00b02c40481c540c01150403c86200036a6040881629129141035400800c254800741a104941010401a40d48044401e9290305240042a0400b094800c180022000248200803c4c00940741800040c240000e00340b800704085800c01c69010342c0da1499240c09403003d4 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 445639847 1250 445638597 445638601
    0x12150a150e040f03091703031b090a0315050703050105030a110111010609060e07020309010c0f020a050d030206040b0f071704020d0c1e08030f0409090c0308030c0a030612080a0503 79
    0x1000c2505210010040032011084a00e07190910300180002850120002980c1240014122255040c40c0103040d502402442ca10385684040e0240001403010441e61a2000c1c080403203181d0f00c0003034541c01103010f403920310780f01c03900c1c1d000801c00c50f44010010350505142034014480c44e2400154030100340c1e07000054075101d42480c00140e8418000082d401c0302c079801c005011074209d00c1038000c542103400341c0e1282c050503192440140d881e03015014266001900510301d14020480c850801c0c0ca1031400545000a06500c0c0c40106e425840c984c40f0170350150b84554284020443d480600a0340858208144032007030a09020080401c5042141e160030130340c10034086019955504114460190300644511149079a13210850740ea0580180302403148002d01000900a00c005c0b040302c26110988242615103800c0004004c0240f44246041e12059007864000c0001442e02008501a1544022868645100e042d005068500941003030300c0c81641202e00b00c0009448105071100e490450410320f40b80c2d = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 445641097 1250 445639847 445639871
    0xc040c0f0f021c0302070204110405010f0503150d060905060906060306010512031b01060e0c0a05070b1302030f0c0f1503180a0c0e0a05060103020306130f021b01060512150a 76
    0x11103c140d22002d4800440360040b081c0c1d0154014081540b01359130a10007414564000501c80c081d6118aa000c100c0d8036006080703403803103000116030090b00100c415000c0c0300510b01040b00c60042d802c08841031030707445c030302d08041c4042080410360042050b00201510b1070443c000c00c0d11024103104160262094190502030301d041031003603c0c983c01c004180600c0340380d1440100e9010344005d201b504004418403000c1280d251066007143c6000805441e024035140b000c0d664101040c90003003580c0e0256289080349001070b9014801e0030160056500102070aa1055040107501000c51400c288502c8460075000507034807420003500d0384016264094151201000840360500800c0b0000034224480d020012400240b10701c0070601034fd10100f02080f803655402c006404921042d12401d9000d0700041c903140301d0840c07a4020300c070896007800c800350600405a04604409a0034280729103565100c04040c4898148a1900441c02030300e070000345840c3c1000d14080704891006003124200f544c60311052081 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 445642347 1250 445641097 445641103
    0x3070504031b050907050c0a080a0903081c06080c1309030e0307060302070501110f090f0112021b010c0201290109030206030403200f190606260c040c0f0f02 69
    0xe41d0880000d10b2064591010048060200d008142c40780780d030400841e800a100d01c1c1a07503988a0036000802e00191035448800c10b50b0007e244074401c1001000c0f010000842c42c40c05405916022151141480002c1200c0d8060b1070140e001422203074046103c0c0c4806545200c468005120308400002c0c00c03100a0400b01c07802c8603200c050a40600c54135038001600750741580240000d9000d0b00080240e4003002881ca007192150321251350a048081c800c002191400c4112408560414100000640217142c41c500680e0003a82581301c444605607a4214218020300440402001c584000c015441d0b5400f986134400b00d0f261f880e003104e034144158140d80c0d41d01035810704020716001402c4a40300e00d8285001460307409120380c825006032a407203080b1211000000c1d0410301500b03c0c0c001c0c003514520441d481c00e40e0404124140da0054860700001f031a0175890283c100748020070364844009030818658549000414028540181d1512004040700e0380e200002c006421411329050514608194007245 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 445643597 1250 445642347 445642349
    0x30d020d05040501120912020a0501050a1b0315260c0409080319060504050f09010b0a0b03011503061203021c0905090c0705011d06061c05030306090c040f030516090e070b03070504 79
    0x1104840c0c0747c1381d00686400086590b400b601c200000e00c101c2e03843c6000101035851100640e4003515000501c0c102c031700d00a0300100c211600a030460140719540b54034400c0c050355408d15880a13400040181904c4020500c81024103031411782c2d0a00001c8290741d9042e15a1000400940c0e000e210707000c842c14811400d8000a0040c90014400d00550a0046100f407001c2403c0c0d0790000950f20b4400c584280d0b0074100c00102c2100c00070103c00e07045030b03c0d05200c800302c41c002c81500002c0594600000c9420b100b403119000381c2034000c2d03005020540c4014910140902340b001d1040500030749070410800d40e038400081c1d83c2d000c0d4103e940b5688481c003d14116001d01011550b1001c600c1103c5850b0b03414a40000d4294811441100e08048009844110b08882120340b407000e0056001080015410304040c24141c0c1c21010031101d079440c26940d00081410030b00b654101f12101d800919441882a40740600e00001e84100001005a0f01000c61400d41c0c8003c188a209904800807000a1b0004e0141040d14 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 445644847 1250 445643597 445643603
    0xb0f0c0a0b15090f060906090907050310020406032004091a040f0902010e0d020f120a0f0303020d0b15030a0f0209041d0f0706021b030313060203030402030d020d050405011209 77
    0x400c54141212000b0701900422401805421002c00203042d4481c0290041d00900010b040c4010701e072207070b000384140100c0050005046100c1d4070000a60381e24200640390f00c0341000c0c0c2c0010b807a103041030b6008095640c0804241e42400000711b400c05a14040300c1250102d4101c0310000621801c409014110701c0e0111041c0d0740c1c81440d05041240810b0b55070041c10101d8400d0341e035001d20300b035030408100d9249011240030b0b40112411084001a0034151618107806e0b01d407100311080e4980c2540c035112425805d84d030840019030003103084441e00c807240c0510501a00222020403007101408450450303030200070300c0c41e400f150311100e500c0b02c3c4010590481d408401c015006100e00c00c440b400300c1c0440f80a03d840310610380b10320760041d0440c00006c26100261034540d40540070400e2001000d180c240c41c0c441c20140d02d80010418107519140542140004180c250055078503440c00d4010141000c0b03900f00c03000c00390340200c40342440a990007000ca405980007401d150202da40054010801040800d1000b = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 445646097 1250 445644847 445644863
    0xc03110a0302070210051309051801091406010f1a090a050310020a090b0309030301230405071e02070e0714120c1209070e06010c020414041407060206010b0f0c0a 71
    0x440e1140d074580c00504103d40283c8604203c02c56140007142d651145020006001d100308009000210203500015041078200f41c00c07010015201000e24216440c5940898220700e20521000c404081031140d2030041038076030032070b811003071408881840c3c50089072030f0081406000500d4240780c1e076459407840007034800036040741c181115120009009500c0b0602240106514070000120b540c8403034212403144c0c07040e20186007581d00e0224006181c80303101c040341140d841d0441c020003094403203100c1c0b54801c1020365500b4400c1000d0350111031101030071034001011034000d04014800c6508012106401c400b1078039043c1c0c1d8083d48050914500d0268820141241281c0c100348020303101900003500740f1200240c800215619480c1450359142105c2c410903500080d800002410b42d801013220211050000c2e01c041500ca01d04a45200c00c450100e904440b00e041b00b0300f010000201c100300e140d02070070039400105019414025084241d01400c3c640130031495000880c212460418088005e54035440014 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 445647347 1250 445646097 445646107
    0x30c0a1e0b04060618051003060b060f0c011a01050c0a110102030d0f0507020d02071d06011b050703110a05150d02070b090304050102010c0507031b05010b0307031109011403060a0c0311 81
    0x1001c805013680348150301c0345941c01184800c0004070f074855140516980c4a00124480c9980e8680b0040d00c10b0041c503503404003003400800c804103500c000a10300c4020031400090444515017000c010005400c00d06810410140110b0500341c3c0000f54004075030342c00114108549071944c0040389140318040c29600b8460415030b0b00401c141031038000501031a02602500c0c1164400501242e88030458840e03526050803894092000c0e075101c11305503030041418903007003c84040341700b250b0041d900300110071038099004800030000d0000c10098103001c1c1104035581c691300791404001410780c60390812002c503002000a0030382c3c4101602da0443d410f0f80c1d403012240b4010302e0501805034481e0482c0c0705043c00355080c0f110402c6064407820071a9005a810307212100c0103003001000c0da9034280000310440300356503600d2a10342c05a608011001c000c600ca481c0100e40e00c41c00c1d03001e12070007503030682c48064440c14110222400c2d40d4081942e9521003003400f00000c81c104422411409006608010782e10b40e940065 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 445648597 1250 445647347 445647353
    0x609040618060b0906011e080903281d030c0103180b042406030c090507110318040b0a0302090403080915040305031807061b050a0501020a05030117030c0a1e0b04 71
    0x1003c10b030401103c0324400303a9141001940c21111503944030356011101c4c0d402c1c3d070510703000e0540d281e00404a401101c1c00e0a0f1400c0403e080c3c0d1040384840c4030100820016401c03540d50141e2002c400740100c00b8070020008028000c41d40d10011915642d06042e1103081c00d07008001c0080488020f15000b028006403800c150814001c0c0b0041e0f882040b10b4844500c02d02480d14009006200499070700680100c5c001e45050301040c0200030150800007000f03c4d160410301d07c024100090801001c0e42a603c01070309854000b080b0444541d12600d174042c2e0524442000540c0e034904516030301640500b441c0041c1d540d0514401e082102c2d8044540ca1041903905000a156100000d0342c852249540010184c41443c1092981c640c2184200350020340c0b4002d0006800c044042d264030328038800c00460310070919550740d5600b60307008907050307900240d400700c01004030040c0d0100204c50204804051340c900b440000e401a1101c6005201408501020f40c121085850b84400d000107a60042002640c42c1083e02e = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 445649847 1250 445648597 445648601
    0x30c03040b0112020901090c1b05010213080f060a02160b0c03060913021e0112020c010b011b120302090d120201051f050d020904061b03060614030f060904061806 71
    0x358098a0500c84038001103018010811240030054000b00009200c2e86009002c4020306000e00c0e61600308204030035082c0f002c68200044d600442c1c8908009030b1201391050702c5070300c0c40c00315a02004003a800703038240d101107040204920343c101e000940b01590f20803400f0844141c1044104008116600c0d0070100610300031307800080c50007501c084901600c1500d4640d4500102020700d50080d50101c640d0398410201420079000d400c0c81c03601810012341c0e0b81e0300b50350300f1003c981040e41c8003d40e81c1d454103442c58003581d10852429904a03e1600b81e0194500d42e10340d8801a802c403110a030603d540000d0708001c030741c0d580144d864000d41c445c1d6050688105c0c02030081c0a050b0945440e001001c416400c0c00c000520784003200300359203010b400040300c560035400f0404035401c050406e4448664401011407440251000600380f610315850100c0d4035445e114000b80014908540c0172919a01441404900c00d0028411600032408540f006c80c42e40300c604000c0020012407018012046400300e08004100141d = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 445651097 1250 445649847 445649851
    0x30c08010e06060109030b070e21060402150f04121a0c0a080a0606140d0608010912020709050c07060207050c060d0f050606180d0302010618020d18080f09010e0402030c03 75
    0x400305682c200e071584401910b2818031130000030400f0324884000382c0d0951142d0b510880c0440c0041c000c08458001d02c5103c184035600d804400c81d150001c00420085d814524404071048400c9014546003964006903004540558010602801c100305401010b10030400c0c0301c550600000c5040380c600d0301f0600c101c81a140d00001c80b92002c40d05200c00940240075a110740310441d449a2203410b49290b2048944038a9444030440c80c0380581c4e5000c000c107550000340f041951051103003500d000740d80623001c0007928000380c56124a110606001c1040402c0b00300405030386e5440c1e0b10403005a00e540c1d19260807800c0c00182c001c03c50304460042082030070a64140c104259400c840c0310100010348610b014000716200d2100b503417000c110002d541e16032504003032001415007402840002241074561501c0d150078400341140310072258002c0384031115020241315028100c500f08020f40365020440d43c0c7d007400ca004104852100d900d01044e0580664000c102079280710760014001c560303a01d0700c580f50314101d42003 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 445652347 1250 445651097 445651121
    0x6030a0c0f02120a0c0c03082109030301051c0317070206010617090312090a06050133021c0e0307030804090606020307030c11010e040504030f0201111c15030c0801 72
    0x8200007500d0140007186884202c01d00748201d81c40c002c4001c00030707038002444240498030745810a0f0300201040c0008040e0064200e02041803e83c4070119001c54600080078011170819041000100200ea48070306904d1040170070418805400001410295000341010390002941c01140040100695022403510305136003141e1950801c869032100002503140e81126002c02c0d540c800c0160506240c04040320b1640300c040c8408844848050303030303915400c0d54000e0740025506440d80c466403c5504072403240403070302c1d01074107039a00840b41b03041d82c003d541c0c4d980b0701c46c41004081c1a10111b05000d03c2840b0304030781c448020701210320160752482d000805500c540b04520b241850301501040451002c02250f824035010381d40e40c00a031446440c0c80c0f5080e01411030315414010280c1d095035a90315580a854811402901d0b401000c44409030040e0a550703294080181d4030340200100140c00c441002d1048460326030703020005030070950105201c1d1820a50f000035010100c5280c00140050054100e01c02c0014 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 445653597 1250 445652347 445652357
    0x15050c03070b16020f1207140a0f02090a11090f060408071410111c0309060501180c08010620010e070e07120c0f030b03011401090603050f030c0705010c1106030a0c 72
    0x90054040740c840c038011160340b40a400c030321b20012030318100b0400b80600600404012160120403615140b920303d811604440c4451409406000c0d458803043c40c0d0742c070682d0705a00b800f40d4810f05284440e68800d440c0c010384900b801c4040700c91385440b0041600e0140115204a0740c0058030340c15047e40c6030b02c2000619106e00c05110506811510410b924800010901c0007480038501c2103040000310002004101c04141d5207010000200e4040d00529008180c446800c01c0708100c5031030443c080d0b03602000a08140f00c4000010424030f54020003000000220304041c21103003030b0603008075006d0700d000818551540308066011600c4040040f172103000f4185511a6074121164072000307021303070380e0000c040000b140401d034100c03404a0098012200f49440240001802c582030a03681040c01000c0c1c00000600ba520f40c0c0034020000c08004c0180c9e5140084011030804142480302940c640e6a0b0003984d04111002d6010701c00c01291800401201c04c00400d82a02da01d00641246c0042c070644100e480020 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 445654847 1250 445653597 445653631
    0x1020414030106051807021f0b03010c14042d03051c08040807140309040905030c010b0102010b0d1112010207080702270106030b03031b06040b0f0c030115050c03070b 73
    0xc030701407240300200c4001510160390aa45125204152040200484150700408035074a40480703a140001e10100250900050800010000e050840c0e90380c0c580b4605100c4655444d03188040110103440c101c83c1d0410f241102d08040790040d80b4036907000000292503460102c4080108000801d000c1215030175070325580e0794411042c0086502c400152000b811400c3c04002e2280803442441c0c03410344080440d02268034112117480400e0132074950b4982a42c6540001c14404d4400c00c080c024840000c200340700a00000c54844005141201a06401000100c25000e10081a154140024a50000c2380000c41d1a500f40381014001e5a210b07040c200c0c070400c81203091703650b00016807000000803009800030115036800d10406078010405420540d40c5440144001a80307800c0800701d0009040b40078001d0140c40c00c191824032003008011342155040024403013044403071075a072070669045410f102c0d01c50702d2a904804054840e0320419001c119140000070b0b050051007100901103000b169410f42c030010703117 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 445656097 1250 445654847 445654849
    0x20303121b160312020919030606170309040e2a090a02160b0a060807030302070f050402160813091a1806030d0804020a09050915060f010801090f0b0301020c01020414 73
    0x10b44140c0e2100401d001180b8000e4001c0b81c8901070f8000d0300d0016032401881c15444400003085c02000c40b00340c0500300c114641c2401000000e004000051003041d107811000c1042c0054641c0b64004c4042180c001c5070340e40c4030940002d9040200341c0880104c410280a0a83c507206100a200304400e4218003401d0701c0c601089600d410f40c801c40b01c440400507504075007041d40b07a0b2000c5800720040d040a29068851a000c250003506011441c0114030039001400700514101e0b0b0980700d4441940004c2c8203030701c14070699807070342c68603524002d8443c0c0c46110315a0729040e0b01102101e100007500181c0602c0d24008551010303a0504018050300f0f501214a030940d000b80a40b4541512812948240c140d0058618034045900540713485400c203100078008086251038086800440380210340c01c041543c4004079103848880d0018200d6000740c0141d034040b10300380c071074000a060b101040c426841039035030394040000d0605142e0702062158000400955890b004e40310f5850203074025005029100000c0442030f68a = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 445657347 1250 445656097 445656151
    0x6051e07020d030c171912060617072c01180b1611090901020405010f02060609180a0210180504091509020d14071410121802030312 58
    0x141d802000285610a1564100d0710401c40301c208130380e44c0d11401c03144103200c0070a00182940d114601d2648480340304405004042103e5004002e0580b842c0039820301c81181d021410210000c0c00d103448007580c0d183c00d54201d03240c903401102e21214034215100d182c0441c5c03030141220752540c002daa5444030720340c0c3c850b00100b200e425441482040607080100d40e1044a148032001c440318050841404181c8892002c1aa10002143d0101c1941d50024043c09190b8201c840e64208a0403480200003031310344880403510144000e4100800032f0141e00d000c8091610820600001c5580580580c082d4030307050001030002036401d4072105034407080060102d1b89040600c03030080165002080300301c24100b0308146800404101c4400c1c0c1c2c01074841d00022001c100396140040d903980e40e12005014840c80c000c5402a120500f5001d02d2103006000d00c0b01d5511540a51481c2c040008858009120050082106411244c2443c02034043c00003054070f000c00800840c1c0f2602c51050003051401c809141017031444 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 445658597 1250 445657347 445657357
    0xd0804020a1a040302010824100203210406062702180316090516020a12260603060a0b011706130c02030318030703120c030f0f091a1b160c06051e 64
    0x10308c0240c0304100460a191182c801500422140140e0b4a0118446030746001c0690743d840300c0c04501c0b100c4060108102080c0705500c000c2105140300c0410044401d151418060300140c0284007640100d20442c2004559000e0042240010101c1e110803c0710b640c01d0500c000c041c411804480e107010f00180e040f8101c500680720065440d4060512456240e41c0c04a000e40302091380700070815627040c0c0140728518504001040c005000300701850703180003020589440002080c031070100b8144420042c0310f98020001d05c124111280689000b6540d05020031900140c1c600302c110164241203892500a401000a500405940314403840822800b440d0365070764814820000c0024101400c010740642c0c0356404100381d95040c0c13801080c0404d8151200043d81c2210a1402c0e0450b62000150100006441c5485d18424140c803107845030310701031850b00f008183d41c10321030700d45010000340c01e400d012168615210300780d8821114a01940c6494004099400481c0c540c0d20b410344080e10300c00302d1320480c02952 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 445659847 1250 445658597 445658641
    0x10917030703180f0f15020304030308011403120d020d050609090d12063c0f0b0f0c031201031217061c0b010303030f0b040204080d0804020a1a0403020108 68
    0x1514020346650121a4110000b00d0b0040c0500b0300c420115628969501c204d0090986140054820f41445544880752203000e0b078800565000300001c00019030081c0d85541100c0000c072002c914050746202003824240160000d45007880c0002c3c7d0285d180207550301410882081000400056542c141848080c043c2920342880e03a070300241d030310120184200032405200102e544003050003991006101141e512241703114000031009424501840f82c61558001c100510000e2001c00e14074050003c40c2d01d510601600c13904032800200c080c00c01919204441c940c03800401160742d20303143c510f2220040300080c0400c84500c0d04d2889044503c0c0c0c46210710110b0780411031100402a103403203082049402d14807a0300700b01d401090190601080100780b00e0f9000b0341c001d46001c540d4880c0a8804411504030203500d030310461052005129041e4001a1b004995900c0d08000d901500c1f11300015815074500c4d44600f04058810b02c0c0c03103840500480140c01107070310030303211201d850b21014240e59035000040450 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 445661097 1250 445659847 445659853
    0xd0906290f0d0f0519060f02031005040b012d080708041a1312110f030f070b0703110c0c1f0e091f0b03042603180705120c010917 57
    0x10380041c542071144800c00e038821006903c1920844c0c0d50a41402105907092900f005004030f03500900c00396010b00104454030f2001103184d032818a1103440d44072091b001e1180a16912855521240d0041c1d0b81182c907804000762917603040310f0f42801204180c0c0f02c802d1460009140704042103000e40601040c41c010341e4010b00c1c1100c0c450f500305c002e02c04c0e0180108420b544803100314182001c103100d13018420b000c000c1781e500c0700c0036040100951031411505240345030b55030340104001d5414201c40c20942d0344250307018210381c0146d01e0344030045014010840e0460400000018400032406000a661900400648008581440c00b090b1019001d900e20041008100d850140c015285003c20702540c1c40703055058250507001e54408400b05800c03c603048005a0007000042c0b000740404d404195828068110984100b05820030001e100c60002405006841480c0e080084052106002d40c0015200c0908454280c6840191065a40905900541c0880d404100110340204414201c245010b440002 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 445662347 1250 445661097 445661119
    0xa0507080304030302090d1109011e0605030c0c0706080103031202040b0f0714030c070302120109050304050d11090a09140a110f0604050a080307171219020d090629 72
    0x509401a80014011004c1550800030704000d030380c440c801011204d000b00824001c40400c081844107d86042e04943c0d89500e100303510101c0001142001405d81c0c80901d070141e00ca0702d40d85c8036102c03240110410560b150042d103a002ca11a540001c06074100e03030007aa1030354010322000200c942240700d2405100c04000c41006802c605900038001811010710a0013040e1111011854103800c0d508801c900f000160040c5004005510345001104080a0160001c02243c0c2040c1d660380d070f84c0e10591154074000e40c640c030400c0d02881300d1801103a41648020300313580024078103030710584000e101110f07040303c04141c3c414441e0a64480016803242c0300e90b0058070341130b2400380d5008104261103160806a4808010000031580c0e46a031840040145180402141c640d2004c0c901840401c2d00800c2114401e44240107142070b002c003030410b007a0030029107034100c80c1e03040c484005000079202c0c1291306245182010f841100f000304543c4803031240a9400d02c01c4800d00500c109031320725140800405c980c04410202 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 445663597 1250 445662347 445662353
    0x150408031e090c06180d05010b0a05011103180109080106150f0201150e060f0301020c0601080f06090a0809012a0c06030606050f0306030705130905010609090b07031e1802030705060a0507 82
    0x40100021829140551503401c9050005900c6d20b080c1c440c1107950b80d445140c0c8070900c0c02c0c2061404094802402e00d550341030071800125540e070191003540c10f0501407450a0b090b40ba4012890315026180840007071000e140c9914141c1e40f03200c00301c000ca10020710461107058590f0b106104050b0ba000700c0120b00050513180c0302c60340841c03100103400fe55104034125000304a543e03092009080b04807240d170107003626616080245003400c05245006100da0440340c01c0050402c0040b4801e4800d65210300050380b110260001289d051714860542c10240d5464102d82400a1662803188015031240003903526003500c4900480c1940ea65100c1e0b030b004583d00b8001c20190003942806107503c008041d00310341580d940d0b0710001e00c0c41107407207060160780340d40c0b2103a6070705100d000c0c000ea00c040c1660090a1000710060f0f0364100e24100001d1501c010195581c040846403080d080061b10480c0d0b40140611828a8151082c0301a070610041240310344030b01100042e090628200741c2d900981c0540301c903400d200040e1 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 445664847 1250 445663597 445663609
    0x2d02060d110d020711030601172107060c030e0607030e0d110102070204020a0f12060f030201081e0106020f15060307180b04060f182c150408031e090c 66
    0x10000c40070500c88580c46401520240c400d09009035080d10300418003c041c14100401a013010001c400098032801600b00d00013424884000c1914440c41d2000d06a41c1e054034034090003034014421030800c00c2415610f5807542117000004003640a6a40c2510f5a0380c0c160200c0d050312018045035009004240e007620f02a40482002e038078494000f41c1791440302c0c7d001600701e0348a00000000300320230710168290143d00021010207848440b008001550508940c0000d42066103c0203041010385400100c3c400c0c014060120500b407023244900301942c44090180d1111241d01000e000303841360803034415000c01c090010500690015020704481c0382003405109811782c6003648204141e0316001001059140d900c1403270f000b03000091014440c00d003019140b01100807030642942ea0315091405500212a13011960502030400034403048400390202d10b510f0900602c1c1c400c0803020144901004180004240110320452580143e001c055107c12170484c0741100540e008602a4000c421003c00385c1400303 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 445666097 1250 445664847 445664861
    0x5130203072610020a1b03050f030c2b1401050d080c030c0d03020307030f020306151602060403060212090a0c03021030051e060904020414042d02060d 66
    0x1681d1048442c01401d0242481c0c058072000543e0f48690001c0c0b00000300c2d6020801c03034000a01c0c904001e05880d09510000c05c240602d05082480340d00c00000f140442e50b2600403039205481e00b455188040c000b500d4004566409000c089640a04107148100c4800b4100307086070594100400740003450205803510341d440c0c0c000c1c6a01c110380e4842001042c0b81118100500455203819070303070150340c078601540000e05480c02100260b07441030041c41403103070319502c15000c402e0a40a0040b441e44903842c0c15014041b0201d40040a508048002000310600030240c004011010394804008615182c0300c204c3d0350303216000c1c4406031072404914024001403805001c0304007071500c0c52500300780704110300007051203131000c0707030882c104000c0d0002c060060013841e130064940c01280c2496600d04030003080854101c44000034020b521507503400c2e000604554950317101c0728640d03014503040580307860a45400b51003c40b072a40307000c210300314004040980c0128021200b510541c0a400d181c28080c034054104054262 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 445667347 1250 445666097 445666139
    0xa150b040e06091b2407020306010f052412040201050904020c030d0e0601060906050a02030405041806060b03010b0403020d0c0b12010f1202100305040f290105100203041a210a0513020307 82
    0x400c00054007d41d40412126001e4400a08203800891801c010000c00781281e038860b1003039501c3e03020f00c000c00e081c140701501c1100f4a1251400260782d140c2c40125140d04c1081c00881c0e0180c1b004c104100000b0001025141c4450503d000f00400e03400f01001c2c0365545424420940080e0301c0750780a00829100f41c0141c984140c80d801201c0c03c0c19100c80004081d18500749500d041d042c00c40c0012070500156002ea64002c051281045186504280220b82c03a40305900010340210825007801e803c100000c1007a60051035400c542d80e03190700381111503c90450082c41010005103902c0303800316000c3c804c00800c00c421039004050600d114410030095000d000014010b5a0340f10040c02260b002ca1100c010640d0084800071180d60f05c0c114004a4100400c01a005680117144807080c07800e11070313000002c450980300b2000c40c1d10101c001d44506072809100b032000f02c107884881c1c03415101201244014450140003080c0b42403095a03a08440380307450f4505254085c1d4184d200b0030041005680c0f0312614520750311 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 445668597 1250 445667347 445667419
    0x9100803090613090f02073f02100f060314070b0a03090f02030d02030c01200301060809032709010e04020f0f030709050c070204050106110a150b040e06091b 69
    0x15039000340750103d0307011556080385c450300024450100400040030060304804912032124901e040c0d0054003a449408507844061b4880c40c0000700d1881c000c111a003594041300c2c0f0240039051148036150090000c0d44006c480300c0c030382e82603058640d0401140100650703508450050030300c401280220301403c0108001c0d40d2140010700308401686040c02420402c4800d074005603601d05244070322608451107a01c04100c1c42492005031440f80084a003143c2c11111586040801501c0f00300c02c450551162007005945007208030070a174444002411400b06100c42100d240c03034240e80c0c3e000106005c0104440080d801030610320080320a01e0640c0c10010f41a00140881d445507032101c04040440d0012369000700441300c00301c0c403801140340a0081c640504190724000f07404608107881181d0342c0c007010348014200d52a0074048059000541c0c403119803002d00070002d1060300c807007882058071172800351040b10103030181c010200c604248038076031520701600113008480060b103829408000110f441840400142d = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 445669847 1250 445668597 445668599
    0x6120209180901050631020901030b0a12030801090b0d0201180f060504030b090c0d0b131a04050f030418090204020d0e0d09051509010c140708030909100803090613 72
    0x5200c1c210140728030300b0803000240034100b0001b04056290702c4540480e1084a1180b0070b012503001079594542221111005a190006100140c000e0000362580e03d41208507420000741c40b44501d4107594415000c1e803640d2007680d072914510400e0f2441240c0b02074000cc038428030740f8011b5100303036000e03e440d00c90440703d071090580f1b030712080d2070081c405c0e4407420020300040350034024800720190480d040960400100440450800071460702c02c180ca4026001c0103008000030071542c80040b4054070164840c0400791610400c2e08548041041a60207813458466104003c4080394000122030954020801d07109031003440e454800c01034090303200c0403038000c0c0d0248080d6860f045280106050310140c14044c00f125102810000d0015101d980300f240306201c10b03401000c0f03c031400411540c0d0783c01c0c03e02e0420345a0800d418201190340d0003048100f6144500c100c0001c5548012016007a40c02d0100d40070a50b649807010301007940d00e018011043c044d002080201d14510700003005001c00444806e0320500c50f = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 445671097 1250 445669847 445669879
    0xb0601090f06031d030702010905120703080a112a06130b3004020109030809042301060f020c130506030a14060106030c03051501030203150a091d0706120209 69
    0x401da80e200a0100c0e40b6a0010000009040510001c61118500a6040c0b40313058000800f0800300d40b14541c0501010f8880c800b18010500c2410061a040003116647d00c0340910020316200d0101c0c02c5440c41e00070608040980c2205e02e48401c20003030079126940c40003c0c0002080300700c1e402241302101d0b91010344030029101e500b08000d80440c20070082c90b200d50f44c503c0c0300803c1e0400507451002100c50340380ea0070480142e030005045415250044100b81e00c07000d506001c01c00810040300000200c01c0c26407400c6904401c070880850680740140d640b40922902d441d0b0507640c0e0507041407180e0b80007581c0381003009054a95400b0f190310001c000d08440c440540e64451040f038000e0317601080b07020f40146005000443d051302801101802c00d16081059140c248800503c00301c10080290405070000041741d61800803802c4421214002405c0c03040e22565000004010300301500d0141d403036220b8070a48080170401040000440d01d9035240d155141c0d444290030030080d4880c0c0314955000b041c0c516020700c5 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 445672347 1250 445671097 445671119
    0xa020907051e03040201140a09120c03020d0b010503160305060c0a09180e06070906050d0b0103060b0c071406030f150a0e090114090c0a0303080a0b030a120807080609040b060109 78
    0x51500e02d1980d80e0f04060000415a03106005c0041c01c2e00400c204518260f0f078007103509411248524001070007848140742c4240c54010560001e9800580c0880d03c4003070003c00d24100b412078104400303c40b0a010f6140091a02054511000d0080d030403240c00a406160200d004011801051410001403501e81216130603c1c002c10049010441d610140f03804600380810006401c0b05490508109030751034044020041e11502080902041d00c03212070900e10703400380d0001801b0300800705801d500e0b41220788a5a40d08c005078410528040b0440d440d00b44207041010889000f05280000c4250694541e50b80350640d007009415030b900100d1043c40020b6a004c0b6405050082840c04004104024180700440340c0700c2e4080c01054a9801645003825590340d06a1171008403603050a02040907518000e004004244d481c070300c2c941602440c0b801a00b0011500600e0303405140c0350301d554603030b61501403045504150448040b90460703c041d000c140070a0100e091243e10801c14540081c0e0191a0200625 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 445673597 1250 445672347 445672387
    0x90106360e06190b04050f0a0c0e22060e04080405060f04090906020306040b010e01120e070f03050606010206070c020f09060d120806150304120c210504061e020a02090705 75
    0x104507201d4a0050f11030718901d00400310f2a001c01c5400b030042c0e00f4510094038001c00050500c01155956514032110b560180c10041c0e00300b800185000c040c0ca24540311050100400c65000c21868a0404007245440c80030b8403d038081d81d040281907052600b0711091108952110b07403e181b2509083c040000d01704143e000d1460f091744141c0000d40ca0341002820700c003c1c0c42c1c4140440341401200030f02041540d0740040e000040030788520001c01c1440e4040001400c108403034100c0c0020100c2048044180440001c070103000d0042a4205c55031907590302c60440341d40010b01c4000b940210901030123071013841c00b0340010340c002d02c1c01405000044004e60701e0b90700341d41c0781300d80d05400b14001c20100900307860442e51800e040c0008590b11840c62a10b541d5000320b24400501900520809200d910144a84c542031100c0310040c580c200501d515840c0310290041d0403038860407000a400302440030b11490341d5110400d0b4050141c00601158035240d00b0800030b00d8000b0005401c20000f0301182c01958800d900f110 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 445674847 1250 445673597 445673611
    0x31104260a0c03030e0f0405060d15090203030f0a0e090c0901030c121e201213080f09090a0e0d0309080c12070605090114071809050f090106360e06 65
    0x3817004c0d080c22044c803101d8038908a186114034a000200030b03d544902c008441101e0340410742512030718102d10140000c040d40340c00650107100100d5108060605880180484100c87d1111401540c000c810042100021a011b800c1c0200c2441241600d500a8101e0030218805081c4461036040356000002102c0005031203846102c0003940861600810344141e00d440c0074180d114059180381c140544101d8030a03803441d01400402c4034001040c12908100301c01e101ca80c86003207941d88214500c800e110303d4104030040c07071207000c070708020420100c8184a0505440392000c00fa10441c2440b40d816001010441e000b51a0b00c002004001900001840340c3d2403042107414501b0740721030749400c004041310801410310a0716890107030501b801140c85030271281d0101042c034141841185690f600785c0f00707842c550312113110b00b42001d00b405070791390903141440d1080b07101c0310080001030382d0303a180102c0224001c200e1401c4001b12030104015800301481e00140111040320105403e40720f401c405140c524103d40b04 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 445676097 1250 445674847 445674857
    0x20309120102070629061812150906070f2d03020c070b0708040302121f0b090709030809100e03030d2408330403020d031104260a0c0303 60
    0x100700285403141201c0a00e800718204d005560443c840c03451001000c108900c9400f0101d440000300404401c85002c81c035010b404481040010603c5a07912500c0740c109d080320310700e07040c00511800310000d0814031882e03055840114012a1002c20750701141c64103500c2401d4000003c1040d20020000c0c40d0012103016640c1c0180d0700e1101d04481f50a240241d00544400c0104006200c0030034000e00c2550207032a0115200704403000d00d8551549420b00d404461040e08070004034290320100d259101014000094031044045c0d581c110085030b15042500006043c00c2c0c3c2032140800c0d0382415260750001c42003500305076aa40b030070300002a1650300301c0503040b41d150340c03180c60840300036122694458504040040c0300c0300c941d080c06595612040ba031918103200c8030090700d20300d412900900041d0b5030114080800300c02c0d410035050094030350181c030703c1c01d0011900701016110301c4421030b030880e803c8900300d4000a4000e011586410136038030b440c40052860f40700e0440ea00010858449000d0000c1d4400d46038 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 445677347 1250 445676097 445676107
    0x1b02180415060e151005121501030b01020102090a0e061903150e211303080a0c35090303040b042409060c11240d0f05010b07060903020309120102 64
    0x1000e442c00c83c2c0042c2c11603002c0c0014442d001c4540c5402a4400000704d545a055600d0080112411f02802260b8100d404503002070091002e1181d0003009040001e90b024456065141c005a00b40e20559080315080006110108204000d440c0c42c1500120003c2088140b0401a41c40d0340304c0308019001a0b034100f000c0608048001400c1c8940051008400e019000190740c1d00d03c02001110f50104806032014001340c105400051100ba52000d554003003044e9803112664000140036140b802c6c1d0840d0505450003459166022008078030f0700880c61100c0042c13007250701e42c06010032030b007107031110580502c4280000f1a00e5000341001c1c1014182680ca240001158105400385114a03850114180451010188481648000303880c3c90740f50461440c901d04039200000c02c40488100c0c0400ca02d010b0314491407000803401100a002008100328103000b0400c01d40b000404444c0e084c4a1926503200420412000402640003181c81c1802401500e05007403140d000b00382000340d0034500c440c540e50b0002d2 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 445678597 1250 445677347 445677383
    0x90b0f190521011a0109030b06040615020307030801140f0418020315100905041208040c0819061109061207020307050105010f06180501020d0c05100f0e0607050a1b021804 75
    0x4180f401400038041d590350b45000c4d040010300f00c41e004d030201815100800700010600d0b1500d40106000b4034a401034944046000f050081d10303070300503e0303040b40044c43d8480000340320f1013234941c07528032114000c010104a014440402004001c4031900b106400611100c00f00940d030280046400071a40b2540c1400341d1400040c0041d04030382c15004448418070b0001404085440050f0b40001419607080806040d101c60074042d281d40c1207a8450b030f0992188001d00318600310300a0191022903c558404d12188507194180f404e140113800303110360880d100344103040d244071240c0c02040d040701c111700550f0702e0301c1c0081d2112802c0d25005d80080351100041d11080200c01c0d0300042110640807500e001300c030014241070000f5143c0c482401290b0400c00800710145c18032a0501542c207607406410010061140e00242c2c0300e0180140246001007801030000003400750340214200c5100c03950b180c0d900c17020805a0180036080702d074008000c0c0c0e00148000c0b0f0380c280003c0c1924445000340d0290040300c2000c11540 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 445679847 1250 445678597 445678601
    0x12030702030712031b110a09060609080106080a0f15060f1401050a0f082701270f0312090501050718120b0f07030b0d1b090b0f19052101 60
    0xd4040c6898a48100d05840070035408503215445171540a41e6008403035090405414004c5a5004680e005819910000d08507419601110880715a600c075698041d03079504880342251150b00c1051031a80007050400005884080e01c102120712498010507085141c00380801102c5031170304042e011000c0b03000b043c84101103006008150300400d290017841c1030409000201380c00080c11200052028803400b140003900a541c1a580240c00103501d140f1840e07d0052090291443e0100403803040d45190486038200c0e440c0d841c603010503420901c000b000b500c02e654100e80c00240607070010f51050b0b4500d0131100050003030040318004c00c425581d403450301d040f008040d019411683d004400c0391313207c0d950400010b12071102c0c10f0b510070b14608a90b803403540d4110b4150094008050244d52105a031a078070020010100b00601301d4003c0888606840c90b20395540000711303044440c0f010391001030041006402c0c5820b90200007071220088442500c55a1200803448803000c094007681803050754051501036440034 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 445681097 1250 445679847 445679849
    0xd0e1c0207050402070203030d0b031e01090c0506130605130b030a090c0803040602070902030a0905060103051606080c07020409020f031902090603060105060a050a0201200d14160509040b120307020307 88
    0x111404c6160102560000340d0702d1040810101105480704540d54007039030288901d010f8421482e86804117081c907207003007900030710440c40100d45890151384042860305010090751000100503080808a03810960f080c2d0b4650089104480c49262a6201040c5031140201650140e04800b4020400b038032203180c0500d248131190403060310b99101f80804c00915500040d901d007100d4407070070700680d80c0d12001100d002a00c00160b000e8180e214940c000010410006280303804680142c002070051501c071602110303440e000380ca60010280c01401400b015144c940d0040e222544001c00824110085501280c100700201038001d03d0050785500e00d00c1942004220294440d0080b000b910380c135810400000c0203030140c050f00c80108000031424411180c000d60294a00d004407051916100c9032a10122009070701c4081891812420204100e68244041c00c3e00c0b07000e007103207010300d4800c840d6000c000c440c03d030024010160302c1500d40c15450480d84410b000788600003030010142d41e50780754500600d484c00082d = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 445682347 1250 445681097 445681099
    0x80a0921020102034e070905090103080c0a3c0b0c0f0c0303090a29062205090304030302070b0a080c0a09080f0d08010803040602120d0e1c020705 64
    0x41556010050fa8088115011950304103840c60041c0b07a80304503507499070f208144200c25002600e103440b410520240c1c0c242079003c5842c0c0200c86580d64000700f25007814880c030070b19400500100040c4001521071000d01404100c4004991401c2c0464646450b01c0051101c0722840c1c200380c82c10324152003200030b403800200034028aa0102c020041d03807403812080c0000c1c038003241000046140249040c02400f1a464a0140c404694981c2000c1803d25100e0f07000000480b110348405000b200308000341c004c05280d070864508005d03040d41d1154107014000d85032040000e08000c02102d040110501c0e44071309405203404800940d20f503411480c000c0e03d00361080d04071059105042c408801000d0340140801d600c2201c0c0d42c1da860b00c413940d50f2000e813820019508607035114051051407122229001660601c5541b5540d6181a184da072500c0080d141d01c518010340d00160866a500059401c85400070304000704c0f000c0c00010203e003004695418051199060401c10380b50041e0754604e00e50402a98002d454 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 445683453 1106 445682347 445682399
    0x703030b06070309050a05090403051b1606120e060c040314030d0603080d1109031009020f0a0e0106020c0f0109090b0315100612050601020d08090a080a09 68
    0x142c1d90191500900c210040011f6614200c6034441c06640c03d515441d00e450300800300d100012241e0f0240301803600c01ca45c0c40c1d0314040c0c90300c1500c0000340003031380d605281210a61408025244031350444840c603403200060000040542c8101ca0460768800705403a050580001041c2c158029040019000d40c64690b000050041c0d200042c8540310481c00304100380740d8040c58080c86070082080c0a901540134501e041641ca0b441c4c1d006411040c0001c0c01c6c8681c4903020030001d107001d003240e00b1090300804000010407050383c0402c00b4501c01d060450f01404080702c20f9000a00c9003840b44100c0c051a42c5818a00d101c03501c0c107001848500f80c94400e032094902e0480420300075032030300744250800030f0f410360501d40303000038544100c90103464141d014086003041100101c070050800342c10310030103000744074041001440c25001030441071032586544010606d0020003880c1c20b98220f8403100801 = true := by decide +kernel

theorem cover : BRFrame.Cov 445503597 445683453 := by
  have h0 := BRFrame.cov_init 445503597
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445503597 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445503597 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445503597 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445503597 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445503597 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445503597 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445503597 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445503597 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445503597 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445503597 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445503597 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445503597 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445503597 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445503597 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445503597 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445503597 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445503597 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445503597 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445503597 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445503597 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445503597 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445503597 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445503597 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445503597 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445503597 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445503597 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445503597 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445503597 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445503597 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445503597 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445503597 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445503597 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445503597 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445503597 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445503597 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445503597 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445503597 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445503597 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445503597 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445503597 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445503597 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445503597 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445503597 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445503597 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445503597 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445503597 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445503597 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445503597 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445503597 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445503597 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445503597 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445503597 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445503597 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445503597 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445503597 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445503597 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445503597 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445503597 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445503597 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445503597 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445503597 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445503597 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445503597 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445503597 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445503597 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445503597 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445503597 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445503597 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445503597 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445503597 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445503597 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445503597 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445503597 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445503597 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445503597 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445503597 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445503597 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445503597 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445503597 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445503597 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445503597 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445503597 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445503597 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445503597 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445503597 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445503597 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445503597 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445503597 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445503597 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445503597 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445503597 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445503597 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445503597 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445503597 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445503597 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445503597 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445503597 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445503597 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445503597 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445503597 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445503597 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445503597 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445503597 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445503597 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445503597 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445503597 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445503597 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445503597 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445503597 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445503597 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445503597 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445503597 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445503597 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445503597 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445503597 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445503597 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445503597 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445503597 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445503597 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445503597 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445503597 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445503597 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445503597 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445503597 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445503597 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445503597 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445503597 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445503597 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445503597 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445503597 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445503597 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445503597 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445503597 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445503597 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445503597 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445503597 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445503597 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445503597 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445503597 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445503597 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445503597 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445503597 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445503597 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445503597 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 445503597 ≤ n) (h2 : n < 445683453) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
