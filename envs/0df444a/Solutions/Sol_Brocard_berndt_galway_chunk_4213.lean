-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4213
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T11:53:57.173098+00:00
-- url     : https://prove2.me/submissions/eb88d25b-4808-43ca-8f63-d046a2252e54

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 757553956 ≤ n < 757733812 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 757555206 1250 757553956 757553999
    0xf06130b090703020f06030c0d06080d09050d0c0e1003060912030e0f0a120507021504260a260310230d0b180607050702190b160302010f0903020a020406 67
    0x30784110161704104558000400102c040300c02407100a880a049000340e400400410024184084125200078198201d51708024081c2406400e298005034034842c1890450705c407050250100d480c0c452140ea426034241c0e0011704094280440c0c1c0301804102400006100529141002032103d880e10440d261480b04d0a004029081b495404010481c100640c114241140c5401440c1030015030001d500850302c01500301c401c44020070140040302100c0e1584900b00d0713044219451480303802060b1075803072a2080008203134503544044c010740c40b0500355625024080442046803203150a107565140254240305080b0f0054825008404440d0400f01c01c91038040d0180c0841c00d4100c03141c0310050803442c0502540303010044600c805c3c00949051040da0301801c6a03580352a603034440c034010024401e01d8010841c0780782c5040c0380c04100c5100c4c10000c9580441a4034901000402c440c00e047e401041c601626000d4542425030342d104044d17001c2149003030740e44211070400040e40c899080d551450301a10422 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 757556456 1250 757555206 757555219
    0x1118010303210e070b040306060e04050714130504030804020a05060c0d051e0a020304060806060306011b0c030c0f0e010b0c07051203090316090506220b01020f06130b09070302 77
    0x500c000c0710300e2040740078100c50a00c0081003c005041100d882c4c20200d45c0114090704010400b071082090701d0050030b0082c0303000d1060f5082418142c0b21540c46100300d2051218181c0ca042c0b02d00c417980c0b24500c00001ca401041000c02440c5014140031b44a503004680491144520034804280c0b40740c01d1050b0380c5c2070001d12000b0251b6008140d800d4038107074000454013100000d170f04180321003403083c0001482d40080d154040c40d216850028042c00f19040946075600c0703500103104005090340d01c10392003a2900c0908521004074581410840f803500788076080503003420042c01c40401c2c9840743c2190b0404480030000150f8440e80e94009454480c0108605c07040d00350000c4804200a207441450100c42485203000e40c3d15100c58900003d02d00318404079003881d650907040040003401c0140c400d0f9640b103030b02910310785030740301d00c4481143d100d00c0802d01c030307100040c0c0c0c0382e0007002603074030070001c45100e501c0100440d0355605142c0005042c801c05541c00301c8180041c4000a1010100401c0c3d40c0c040301e9002c2e228 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 757557706 1250 757556456 757556477
    0x2c040503090f12010501091b030216030f0c021807020d050301080601050906030708010509100f020c0c040519050f100f030506160311071b140d1707050a1118010303 72
    0x2c0103460880d050415a0001d090300000b40181028840d01e40203007400d100c00140021080103507648000c5500c01441454810720412150310401e80800741400d43c14071300300908403070400e01540c040758400d00194108003501858444040301c5410b42d80510443d8088803082440440c045030030744024000c1d17100740e03007108004100c1400d000da01282c0154005065461294441c400c1030700f11039048030101d84551000c0d0803e80001d0b41441242944115840c040d442c10000034400340d540c04200703481e5805144c3d2000061802107850b081488103003500300c8144a076041514243c0948502504e800400d8440f044002910460034032445084a81c000040c091a1f5070b00e003180c031000d03a220240c000a15494030b114440541c130700401003952a10840d1101e103003502d4000d00303020003041608030707060b070b440e807050554050341d1107640c80301455612071014a01c1442035000000a4002c3c060010598450404e00310104400742d9100300700c003001640c1e81c00c02c1210351300e03070115000c40078400030340440d117061f00 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 757558956 1250 757557706 757557709
    0x1120906050723120406292716020c0301090501020909090304030c03030503150d080c0d0809033c0304060e07030b0f0417030702031b0706090501050a0212042c04050309 74
    0x90484d880340c01b54100240444000c410110b8a0036100d4048940300c1c0c0303035a0012007a15005c00c3c010740700c0b00b8001d580119140c035003454000c840406407600d483d407009a00310300d40c114801c124400007180c01030021f00c00442070f8a40b2070b010350000f00a5620940880d40004e900340000010b0b20100ca40040c08130580f5071031a102595030b5800031b401040100d503081074030001902d45152448981d4481d8440e0f036981c0110a02c100d0500d8960320a6201f0407c4800a0101e095000010754a0030301c5050b8051070000c80d40400100341070900c101c485950306240000380c0b464203d04000d548103c3c0104418400c480c0c0080c2c481d900e500b440d000061082c4901d0006c210003803200a4141e074040c1c4514150040201c44072031010b42900202e883d6001617200284150414186584111140b07400b40d004040407424003d014140007103038040d00c0e04025010070b0a11245100b0491602c500c03c603a54490354907a201c466069902048400c9070540d0168414240c0166a690101d00d21854002c40550706100f070410 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 757560206 1250 757558956 757558987
    0x15070b10050a030b18010506031c09091b090b09060406030914060a02090a08010b090601230705160503030a09150203040305060f060a0b0f1801120906050723 69
    0x820040e6a140821804216511555000e8000e180200c481d032609191031a0722a21107040c1c1940710700103034180000c0c81480c0d100003c48100b400d040c3d00305528800c1c0310f1007040b1001017060780000303081820501d0f503104d40c0c030702e058140c03e0420095882114a9881e00e039109400c0c481e80c02d203546c0003c002c10041000d01e100354003180c0360344c0c4254051240e1071404602145002000d032144036850354001618103040c9000c000c00001810701da0028092aa01c00d800902107da00800160511102200c0c90102590045000d84107a002014654840e00941030aaaa440340341440795000702c03201c00082041c3c5000400d441c5040007139a120b104142c01c06400201d01c09002d0790210540c4401c1c4004030000d0003c5c840c0920400c0c5400840f100e0b8a8035404215640b1141c0d07001c1c1c44010003c002510700c0d00700070000c03642c1507074140703440006030700000d070040b00d0303d075401060001d8240c07038140b100d0100512078101c0350245c1240da80702c804010740d5074060058803086482075244000c00308804185c0303c0200 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 757561456 1250 757560206 757560211
    0xf04120c030203040911190216050d050703060f02091e04061d0402010f09092a03050603030f07032a110609030318041508101a0a061b0503190e15070b 66
    0x1d02403030500c0c7d800d1104000250750200300c1d00c0540c1154522081ca031a054003c00d00404007202d1160f507680d25a11001c0d101e10480c0409080d00d520741541c08085251601102d116a80250407003010020003540c074804003400c3c1d062036124a090070400104401504482404030035200361001e66502c2da80d00540e40c8000012022060010400c00054043d01d2413140b00074850a002c0c80007004081c100c4511103040b5218017407018989003906000342d94600000356500003d0308008559100c980b401c00740c854017806556100c4002c03d00901204c0c0c1c5101c2442c40500e180314122070074455061504120041c0115800503425501c01d00c4040c02c01c5041001848210101034000507034030a605244080d03400c1c05801210b1790768004000710712141454070468407000b80a01a1040401604001031b4503170599106103c108a80e40c05248441c584040142c084554842c04483d9030390f00c0d540345901c1c980d40f0614850080313008080c281b140c0b4100000b0744003022543c20f022602d0301c40e0650701d030030505a02 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 757562706 1250 757561456 757561481
    0x603010f060b0403020a0b0304030509060714030409020705011505100f030b060a050c100c05030c0c030912010e0c0d0b010608070c05010e150c070c05150f030f04120c0302030409 78
    0x2990440c508010062189001421240c512283d58500718010300240c007075240e01c50500c5140070000c10003c42e5022055910400080301d909960b1030050500010131251144485030318080000d00042130f03841c5500410645100c0d000a1203008207050742c1c5c402d00b121500c50140c001d000040d034107100b54481c2103940c0c40e02049090000e0711200c803002054890b009654400c0114100182004c43d0070801c0100341c40980b0261014031183c440c8160051807800007400f625030322940810308803100724007403041d510b901c1d6024002d0365400c81d014151501a00b071410606644e80105443e003441414444080b0b581290461450b0319542d103808002c07500c4020082c0124201b0041e00110070000e01c0a010f104180c07500303680108551401544c0e00104c440c0060140051034008200000008040c90145021140101d43c100b04007008003032182070b2031041c0f1400000220780001000b00500e42e10303c0c0b090045000d0700682251680303c0c030703003514180303100303900600503078000e00007000303400c41903009400b00c141c1 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 757563956 1250 757562706 757562711
    0x308030916050d231e0f010528020a09030203060a050a1a010c02060c150c07033009260c010608010b0904110102070e04050d08070906140d0b060301170c030105100e060301 75
    0xa0b41000195281124000203070190006c40c0c4d00058410240103050b080201d108210b16600005100074034034070a501c4958194540110300280e002c4c0c000e4a001c4011600501511600c0c1340c02101d50000309822203480076654075202d101e202c0c080860b107102c5e1000304103844910b00d031003d6400704405a0020484514507200e0b15910b440501c124000607400b4002043c0956100e5846140141100c4064440d248506e40f6205501c0b04112007215400c2c5943c25034000001e0240d040d00301a0041070408048504200303140880c0d4403084103460003826502c00d400020000c1d65250200d15003a945a0780340389034400c1154000c01e001c41c01c1242c08200c5000140115407405584250020910744100c0b0305031900d03009842442462500090700b1540008079140c602000d6041c200041c194004401c0b16585410010803610b04030700c0954403a40c900040180455200e6030b59144d12503040d0502000001d040c09503a031650b51504050003464000d1001e40750240d90b80781842c980390100d0380004c080c642d0564 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 757565206 1250 757563956 757563973
    0x1b02120c07030c17012306040c11060705130504060b0906130e071d0a0b0d020a0509060d0209010906031b0f020c0d06050612151b040308030916050d23 66
    0x210303240c010800601c2202e0130b400201600b00d81103070844440000c6020400d40020000500080e514503072035210204881c0002c0e0801c100500715803076011207807103d03914440d03281440034242d0004080c04518000181c50081c90740c130b40c0103200c143d4126110b4250301c240c3c24030248030585441ea0282c0301032944203a07801c281a5456001615501007664080c010403444103440103070a8040070320041c0d800041d00d03958030152030711402c4201d0348200c0b05903013001e9a001c60110b10141c850f40455401c60002026661651080c0c440c0300000c0d40042d520030f000c59150140058118083e006003203440140c00d00c030855102241c942030b18181d03103c4466104501503481031010542d10403401c40c410a000d41c00c009002d181c41003e100101516055400341c07130340107502056060450303011695001c400e14a2002c0c0440400000413000d02803504010008d550200030448200000624080d840030381d0001c0300c1d4160354620920016141511014007200f1221240562910725003643c0d22030100741208640c01d02 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 757566456 1250 757565206 757565213
    0x3050c0a50150f180303060d06050601180905070306061b0809041d10060b07050604140a0c090b090a1a01140d0e060a05060406210f0c09050a1b02120c0703 68
    0x502203c04400080c0d89806000202c140c03c0288194020020011032450030010300140e01c5c0c400c5404020565907d07480015180e074071880840304503103101d10900d80442c1c0c4840c00180949811241e10700041d03d403450008078075108580491010380110ba8192440c581a00c441e5800da028a40c2550031686440d02036802084451640e0181c0c3c072110050f00110100300c22000c1a92506e600130420202d0500c000008100041800c035001548510301c0e9100d2103039403103010308007101c49501900c440b4901d800054101d91342d4001020407102190f50712100c4d50303045186821106117100e1203124104600e801d02203075000709804246111140415402c0041004100d001e6500300281d80c195134020a083c44030140203406440d40000040b9030900c140b0f800d2411002030074108000030701c5129901012542802902c001444415800c83c52504003503031a00c1142000e07003019a40468034130b2401c0c05005500c400c110070f09110301c0c40c55010300740031f850b800020540360308140382c190702c0c1d4081c204000000 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 757567706 1250 757566456 757566493
    0x4020105190302130603020c010608160b1b150103030809030a12051503011803030b0f0913080c06070c140a0b190b1002071706090307060903050c0a50 66
    0x504841c6d0b40542e490000d8020a825070300c555114803250f50005c04d00900e1072451a28240c151840b908010b522124103094802a000c16401c4500c081d0117200441c01c4030503124010641664003c1d140c000c410b443e00390700075650744249100000041c0c803503a4105401446c60b004160008000781194034a00e00307000000c0c0c00c480107000c1d9201a1400c0000d02c1d000c040c1c15014011850381e040704c81c0712030065040c0c0031841005005010804498080e045141041707907180a4544004541e0200c07a4189800d10000d01008160380b07003602c03101c2e05141c0040200c00000342002e0403507400466180d051310340d080009805c0c0d5800d00d524072956180d148144140c0c98075514000f46040ca9401044141d280c003000000c0001c0e842c0250101c0e81102d010091505800000c035610194804000202c0210b50f050445180c01600d00d8170405009045503071051081c181022143c00c8042003000c05680c0515244400c0661a1040c00750103d40096071074100604c54490500340c0d84410741510050342a00020399131 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 757568956 1250 757567706 757567709
    0xd021305070e0103061815030c0b07031209020120030c0a0503040e071716260118140f0402011e0807090e04080304022407080d140402010519030213 65
    0x1011580c0d402081105507004000c065401000e080c10080d450070100d504407203c40048003000010385a540d14044c020312000c4810082d504003030382e10b02040e240c00d99288194480c010503030000d2042c401883d580d1904c0e11860300400c0d0305844800c2c001d0018440b903101c0344003900360301ca0140030034851600410428050245494491030184d940c1e0380c10007000e10f070141d10140c200010403042d400d5842084143c50b6243d50070142840002160300015481101e003040460340d0601d2045003050300361041c81107190b186051301c11203c980c02c115200c811458003103079a028540003101781201c0104205d442c22100e036503005801031400080348080c1d60000c01107900940510000a201402007144182d440306100004d000b0b485501d8506081c180ca40c2c0c400f50101500181c400c0230101c2400c0056208000c200342030003c02c0b2030f240d072550350070300b070102c10703500071013419010a820b02558056003000040d0040c85164141c40c0d8a041003c40101551030b2003505018009150f82080140520041a00c1c1d510 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 757570206 1250 757568956 757568989
    0xd020a0306050a0e1e100308070b0601140f07150e01050f010f05030102041a0c0705041a010806060a0206010b03090c0306040f290a020906090d0b011d0112020f0d02 72
    0x407140d00e05030030f0107034281c565030044d8001c113a500e0a2105071030000d080c4a8111030440d481e5042d40d2984140b9000012542d4401400b03940300050031410013080c240d189220b4402625024031140704c200852403284243c105201c1e8070302081000100040e50569580c03403041d8084170000d5203000d500302c0f89085483c26a90403140e0401c240041061100b2700f20010041c2c101600250300b018036180c54200034010740d0303480d0400500c001c0b4500c103184604100c0c18000313020041050120b441404610481c04940c801e0311030008032480006060f500f044812101c12450075801480a07030310b0040311100f02c0c1c001a10312b4040b4002c01e49000c0c0c0036a001c0004078000c0340181c01d010308920b03103440c10b0350040017480980d002ca00e000132100d00e4100d04006045600424151015a86884220005c3c0319445003954043d44110203541100612810015081c103880030310341c40418a00c04000c070682c41076003d210f07480d11a0349024007100141800180c0140116002d41002c100c0c400d40e9002030351010b0045c00700e8 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 757571456 1250 757570206 757570211
    0x20c010c03030b15190c0218060609090c0c010e12030a0c05040806010f0e071d090603032b0c080405072105030a0f09060905180c1e0909060a0e060f060d020a03 70
    0x1e01c056160204c0d1000c00031740900b000340502c01c1d683e000c510965848821400c0d901194000030780182c48000c121241100003c2c684043d910380310300518041e8110028281141d0300e80344402140d408005138460280303180302011400e5035601e02d400c2c00074000c0c40c04c4210402005003c000341040080200038080c10b003903030700d1110a43c14034045036084600200a0303802c02001200d1020400251625034200c0c500c195041346441e5540310200349580300d03503c0303003000c40b40e44a4403981d803000982600985e144001d8030140800b520010080740c1454054402525135003000b20304109082d01403540c081030380881ca0702c4a03d03081564413401d05603003200007590301181792030104061040e8003982c00c40c05020641000075415007400d003c01c0b80314024070610703051612a00040b85400022006440361400b00710103003120414500286030b856040800142d00500501000c2959854150400000c1c0c8800c0c100a2502d642c5510803c0b620200e082015134000c4420000c01130815110300082c5141101900c02 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 757572706 1250 757571456 757571467
    0x30c0706090e072a080c15151008010e04060902060d0f050108010e030a080c070b2d01150f0909180203070515030402061b0d12051501020c010c03030b15 67
    0x42e8001807000f0620002c004084d105080740d02c41c50b4603070102040490010003044681450061514412020100200e104000203203100036130700c8070280e118502522a2084902e8810300b4040754104420614000c100c00d800140100c140820100c0d82c403900034400492100b000303070046481ca6019460009443c0c0d116082d00703031038032054000c075801055120000c0080345070101d06161a40200c141c02c07010002d807800403c08128003981039031400b5801041d825410304140119031040c02c101c900030529408001044200c40e82d107090428100ea040341c802c500700310040c50040320364001c1ca4900f0024800d44400205410000e4880ea18055000c01e216111030011401010316220603580302505c5180d0005008113003050540a0b2a00558180c92442d2541a06040256102d10082a40c04540b2a40c07015848241e40981d400601843d5070703804000e0358548001012010312808062405071740720302c1a840b150b51240c0c400ca850203009140010314a8100000a013002c4810f0404942140c0e01045 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 757573956 1250 757572706 757572719
    0xf0210050c0a0f0c2001050d0203010914090102031e06060c0d0801090b060f04030602071707031d0306060307050112151502070503070e2202031020120414030c070609 73
    0x6000e1809400c1c0c00d00b013882050300e80e640b82003100340541d03070001008403e031343e031043d0707405541520704601c1c0e100800d54407076840f042110000c0c410440109011550200815003140040c404c82c2c0c000c0640780b0381c1103105d0011403400c01102e40b01400040d000038003000104068481402425050112955603d4555141c1006a01070325802200d152103500100442845041d0103c112000c40341d002c18050f840e185241000800c45d00301700500140144001030130b808041e84500130350008141070202840c080c1112043c5513030b5000403140d140d01035005580c144815030003083c1b000700c03c20100750049040341c2d80703120300e03c01d00c0c03031031b134444100c0c0808a03901a40b40d40d0188031800140006400400510307240a0360607403003500140c14045915100d019202030851b0f001c1d072000c00c0139000350448416004480406000b03028441e0703890048196480c0390b0806440c20800c0755440c208000713070201365842c0e540300d0580380011000e0655140c03004005041421800b800300400404140d1a0217000918115 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 757575206 1250 757573956 757573967
    0x2031e090f06160806090a1401060e0108100e0402150d06030804080708011116060906050c090907080601020a0b1f1806060c02060f070203120d020c0f0a0203030a0f0210050c0a 77
    0x601c40d510400d001440b00c083c4079803280700281e110500b02c074051250f80b5410440d10060410041c255072a6040360004580c0c01c4c0c10903142c0310400700a030b03541142a0ba1303480455440500314019611210005404140545012001c070b400120310344d1f50691400112000200484403550310403100d01c04007080420070010705111040081210400130300c0a002803c00c0080300e44500c00c180054080100032080034045558805103c1d1503004104128a00301403a07824030035041580800d01c104000380000b0125449108424056101070700102840b0340d10359118205901e00a10807041101b0040002c85800d540d556540d0007000c100440c3d860034203030820800c0c246d804640054090128109a004c01600c44008440e84440403002c00e68480303026200080c1000c41e908000c0325100e0000c039141c1c1c2030344480e5000b015068403a40803500d5081d00203000c01e817594007494004e58180c006000d40c1c000113005081c003165240951041c1c44405140c2d121460883d00185e4203904a01c001007080e101c0c064101 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 757576456 1250 757575206 757575211
    0x181409060307050906060304210915110316050c0d12021b063a06060207050103090f0620070b010e0f040b011701090f06020c160e0a02031e090f06 64
    0xaa002d80145400c2801042d41054013a00a03409130b00000001014003821031000718460b91012801000310340780c2040108115407a0203034404400e040c502d290346460003a00620103a812010180d803c040d140703003076820719101c416802d541c50f014504003028a42e4400286a640d03911800d803030344501c103000307100a2801840d00540c1d90300811032500002103544841c143c6020701c0c26505600c8915541a0b450b05054100c0d107280303608085030340d82e1512444001e402c044180e549590888848980e0b4000440c00e40343ca074900a0300d010514124100072954903000402d00c15146403483e40f880c000300340032400f2544041c0341600d40b070410b8001800f2080070134900c5134002d4510060000c042c00c080d19040d551700410f00c0307500d50709801160400c1400c00290882e2030300581004034030700d07090443d05015011394450340304401c00f40198110410b504032034484c490165501841074207400c2d81c641e5241802507102038003c1c0115000c80d400c0e19280c03100c84000d54840c840240161080d412501d046034a000c802 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 757577706 1250 757576456 757576459
    0x3040c12052d060906040b0702070e130f0c0f03061a010225122003030f0d090c0506030a020705060a0b06070314041706101d06040c18140906 62
    0xc0101100110781d00164068649001c1c0c01c0c074290000d540c414112000110a00c8030420f402500200001d890000c20600e02c1640038034005511a0f41e21481207807604114003813000989502008251404801c043d02003030680b003280c0421804545440750303e06a030480d4003034402d915072441c0500400042e401400810b01000d00c429480c11a1000043d441e031102e501c1c01c82d1504039000d802c280c07410070400980010040c80c5c003500c0c88050141003070310110401c500f0402c1110f030340780e080062a040004c21030308130321070544815044c606003440e00000340c800f00702c2c2a5104861204042030720354820300118010a8003180044c1d5404a92401a003000401001e54a0a62400c0016001911018126800c0c00d50605d0207000d00480305880b01c040f8000c940010319490b501da0040342c6011400030b9031a000c1c4091140480d0490740c2da0411959000c0c54084031070624003544081500c50400350000d00c041901410910f0102402a07400c991541c0c1d11f0740418045003102261840f02d00300b80510f00d030030520 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 757578956 1250 757577706 757577729
    0x30c140d03030905150c0a091a030f0414060a1e060b1e12070e18041a09010f11030a150b0a140d0e0a0210030227010e090108010203040c 60
    0x9500004a454004500c0039040c1a02d07411800100310050054800303403500c110312041c860625070750400c216044800420045206104080740c06480c8440710000305211001491550f503c0c00c2422498500c044c00407100d9490460704614040c00034009548100b41d03885000692800c814080803101d401c40c03558600861034220244105d87c002c50858003110708180c4e41c0081170b0704a034440c1b1028405c070b03004008580040703001c1c001c0c060b600003590241194211a05401003e042c11040c05816095800030708450752005108001407115041030342c0032076070f00000501600464128010703200380c500c02e0300032104008108041d4030b06038880c142c0080740c05020712800d10704207c181c2c1e4203072107604202c0f000d00c003002c215401c0d560090401c82d02e84012300300051100c0149034140380c0c0d0714041800c0480c030865102c2054240d5910a1082d500c0c20030404103411402004904800411030644107268100300503c4a852903640350941141e0081102000041e940e10745800d1030380d82a03200390081d21540703c = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 757580206 1250 757578956 757578989
    0x60103060b031918060609050a0509120703030b150a020a0501110f0f03040c03150c030f0e03030a050903090a030507140307050901060e01170702030702090609131e0c0f030c 76
    0x1e401010a0b40380314030343c40005000d5007003001c41ca41d6030040800092160781002d102140b45220b54000c035018461100041c0055201c1d10442600e8402c07011031560072503814032442c80820f100303410142100d400503100241265544180d010f1540c05140c20304050b07405442ca59041120910504440541c0c0143d441d003010310200a402091180c0caa0007480c911012002c10140042c008c82e4070001e56204d084003407590550000b02c00502072440c0c485001c0303841c15107070004d0481140141051281e55a0141d45140c0e250039858000b02005002528640700520802c0d4281c4c840d10780f502c1c06180a5070040052510705411b007040c01881010341d0b4000e4000407400c04c602e84400d0306190655503641040312603450703140012500e20401d4454410b00d0300c4a03009002803150080000c00500b0700a448040041d43c0b07a03418424000000d0300c43c0d95000b8251818407000c60004100b800c0c40510040710381130381c118980c46d80401201640c0000c0385d0041554020401c20514810302c0d80180f840f818483c1454 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 757581456 1250 757580206 757580221
    0x3130b07090620031902250308030402100e040e1e1207120c02030d050a020606011e0c02030a05030711011b050618010b190f0e04050703080903160608060103060b03 72
    0x14034124075020303031008581d00d42c110100b000d00079144096807075603e020104c010707500029a5007400c030750b0710a0170032055030f0340c90480d01f01207442005603a0010049481c40d191907080c0aa02c03d4100088801c110f99030345040300719540c90050022a015101c010641a2601c0e44001c0162301c0e01581c505090703012908080c185400c03201500c0b51950043e1124001d07800108043e6403001c0c804400035458040e40007940c03a001d4000740600011f820175401c841244e650071006490910449455645035440200ca0300c490510403000540c031144007a0503a4500911540c4013071464100342c0e8101c80e003001c500704d103200a5a101c03141c0c0c00e8118203042d00d071f030309144551241602e40f1400b61000651780020101031f403a4580035000303180900b0327000d0542100c0c04d0b205c0c002244a03502034028000341c520220000031f9040c1c0956200d60213681c104000e0907446140d5542e120151340700d005407980501521034081e44020420603070310002c0020707448403201d6180110004088036282d400c860000e5800344107000c1c15 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 757582706 1250 757581456 757581467
    0x170d03050f040201030902033d0203100302040f1e05060108130b0708100312020d09050d0201020606100318060905011104080613150e0f010c080c1e07020603130b070906 74
    0x25028280026846a0303030010070304140215500b55094401d0300d204c050058a0608091032728010a120b82d03685016000d5800180d110a50b181550400e0050041c005490a9440036181403042d0200042e0b14a9070142c560101241c08103000c4041d07072703032410840956082800c5643c480004902c3d5204c0065a80d244e0544100107003c14003008038880000d215820104405005141c020703815000c1d46508210095a1b818810000000280700722400038850412000c9501150740c140c001d0700c296030b603140c28840ca0f40120519001007507212032000051450b0703240c0c0c0700c1c0401e000e05800715600710309040103829034480c1007520442c131008210420044a000c6040b50b0001020041290710101c0d504055000c1e0340b41c1102a813140f86482d907503400f00c02e400165180c000320400028010a01c0b20320099900200032180380c0c1e02c4940800440f0318050038007860170101a45074000c81c3c10180507402160003a001112101c400f0303400034110310144030880d41c1c2280d00c465240f814001c401d042c400014030 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 757583956 1250 757582706 757582711
    0x327160815040213020c10020f090406050324060418030801061704020612060112020d1a03010c050f070f060c050909060301050601090b181f110106060905120a0606170d03050f 77
    0x860703000c954035a021500340f22100b004140c1003000d47d02c49c1c41c410340108103540031030304161107a450300c4000112814003003449280f01c00684210001410021240d007a4850014065984242d40b500c0301c41c100141305104503d854041d9a90141e00c0d81490030213041c0e41300004005840700088420000107030b840034110f41600c40c1c0448449000d8035043d0042c0c2d09410000400e0040074004a00e80b049108285d010f50b4008100d620031105c2052400e080c03508030f41700b00040340001141004a03081c0c180c0e00d03100400502d88501c64074007107810680c86400441d040000350303d000400014a0010310b1410f0a10303180c01c000124000c101c07509064001a0501c170b82d6224000d43d00708081118504103045400c600007550028049401c000c441c1ca10401080c10102c103100d008ca4000c0d40e0070742000e10144030340c0050310701c00d0306c9060340d40b070a10041105012a02144035003521850300740390009a1503006030702c000c20140f07020b5884000c18031401800c0242004c0000b080602c1d25041000000300312001a4 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 757585206 1250 757583956 757583989
    0x14040305040f060507081c09150c091e290a1d060a0215070306120b040317010e010b07062903010e030a0207030f02151908071403271608150402 63
    0x50b04881c3d40f185847c041c02d180d0318050f001b80b00d1441403401c4101c01c0d402100741e0145541e18081c19540b80c0074044200905240c10815814011105110f81e081e0359064143c9621a0180100e460018400544c0303e940801684400250000c0c0501001c860300112480c1803541219194200400141c0081d0307104402100341c0f0442001102013500b8034040d60150016003220712813007d10518034280b6900364001941c044000911070303100f641106035070841d105d060b162001000900d41c0d207022212603141e0030050060360440c1d0713120145003481c03100d00d02e6000210020213992030041e0f0410101421070707104045420301034108000ca01c0d00247d02080c20000c0d250720007101e80e9048591b00200c0c194800d00d003c7d1030304944001030341841c002c0316200b800ca42000030340d03160f008a036200d4804441c132110100c900c0d59503403014800700d201c68110300840840b40503180401c8030000d4031540c200f844d00140c001c43e000400c5640c84240903200303007070101d40e00070750000f14079814504096002c110000c01d50394100 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 757586456 1250 757585206 757585237
    0x1060509060a0522020f0c0318090c16030e06120f0105150906070c03023a03050a08150901062607020c1522170a03020303071214040305040f06050708 66
    0xa214032440d411b4503050300300d805000f6102c0014944165903984484225112045c0340403003422030b45040c3c08428402d0040307100550920810f03002615008009a4046092001141e0907442648030712010700300b042d180300e5402c20359040002d2100e0080d5030603006540034544002d86200030354134050031903500b01d030b081d91b8841e910030b0a800d1000b0a9146500300a50068881030400c031030050600d4130714201e50000210091100b0b040142120588645100030b0100d0700c14421081000d0084528a6004600d81d10603049800480c00040160101340c1100000c2001c040c00b1840e4041e074070316500c262500221803400b07241849100a540c84210781a11031052074103005841d001c0540105a504580f0b00c0c4c1340021905901c0255601c0294503402610903080192086440003800040c5860b815a010b402962a60300c4464044400c0d10070050100316407a00c84068141030b00c0382e505424801c5019940da00d469034142425494500500c0d03000d0310410106000d44d40104000038101d4002c4c08144100c1d = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 757587706 1250 757586456 757586509
    0x40b160810052421091b090717040501050a0b0109081504050a0c0909060f150e06150c0a1a100b03041113090b0702030f12061507030201060509060a05 66
    0x14030410f040041003040d4040000310b940310301c5908092210316007482d0703a29561601e07a60144540d603104a1006501d68003141c0d00f0100da814200601e680d070300302034285440e40d0b41920b550085d040008065508a409070341d03800801241d61100e1081003800502464210a014a8041c2060340c455840b80300003c00d5180e0000b150800100b00400b408503a408052100c416940f140b68500515003914141d44440c1040002120003426200d4400a803603024540c1c100c4504150800c500b0340d02c000c150940041a414004d003d40200701c01414461901c10002d0020503228900001106042e0000903001c0f51190b00f40161a820705410070240d9502460030341e00c03507880342003812401500f0030006410034420246180003850a03000323185414050100281c080e1180c80c8101e80d02c0c441e4100b0445852028011603000c600240161500000011b12508014821800e01881c1303a03c440c40403070150b95200000c004070304040324496406481206d0110155151201041844a6920344a40b003038524001 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 757588956 1250 757587706 757587739
    0x11109060415111606021e031617040b0d060e0403050f07051c02060703060b090f010309060902040c11010e0a080703030b030a05060903120606090d08070c0e040b16081005 75
    0x4004003c0e42c064411101d001074001c0207403484d81c40e18000c0800502440c907501d003100411041802a1345001d00c021441c040d4480201c0006501b84031003102c00048200a640307200c0200f06c0640040c007070340000c465540484405100441e01c81382d004d103000002150411000c40e4104e401c0e120302c0101c10340d5403a501c0c41707245881030800e039000480c40014044900000065030380060005e102d100c06440c20454181c40750090011030040c90f012907441b0b015a240222654403c0d08140246480f640000c01d09140303c2c2d0000d4181e842080151001400600b03c0061601c401d00400080e01c074a2030113455411440e0312109060701c2040e00103024584c44a007844481d460030440c1251894020095407140d003880003006459922800d5181c1b141307840400440c03202c1c90400d04541c1201d0005020540c0c2040d0340ea968600307070700f0201d41a914074640f0341002419618500c205031141e4401c44c0c0482e801c1c944a0410140204016a0f00c8204100d04081203e12000441d03050309680d01100c1404000c030030b246 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 757590206 1250 757588956 757588967
    0x140a0e131a0c0a0f0c210309080a081f08031e07020301050906060a0f080a060e1203010f050117040c05061b1e070b0a08220f0b0603011109060415 64
    0x1201c80d94400151400c122202c88002d01410f5048616550340340c00784103424048a41c1e191100001e49078074101240c01c604d00700d0030720400403c0c007814180810b072080c0030f8030f440040b03410240708030300458044010040301d10012160711200b50000001001c01174145044595203014041a60000900c0d035240e50b00703080c5002007a1240c00380d00900074841d0b440d120388010f894240640da428000c2d40c0500003c03c401001958030350603200190002e250550441e02c0e4a800740000201c4412a8014001240314140ca45801180a4105000c0c00386805140800045c003840c4c582c0041c0b40701c014903a0034403000400e04008207044410031900c560305c0f83c005900e02e400036801032404000900c5841100051001d0181092958655501c15900136594625001d89944908030100000600040c00030f0313a070f07030348800544000030702003003510350f2400f1295a641040003c04400362246007103c010001d143c07800f4041c006501f50810307512410700d140080411120301a50240318001c0944103070040c08584140f = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 757591456 1250 757590206 757590233
    0x3070302090d02130603030e030a0201050306130603020d080c1506060715020c0102270306010503100207480f0909050a0204182a120317010b04140a0e13 67
    0x2803413140320000b0040c02c180200641d110032004902c050f20582800d07d0302081440c00503070107071249440c41d5074210400c102820410071202e5035642d199000b00158660000d0440391900c54007506641d030080341200c0c0d15114513400b1205084680c0e904004290f1920010381d0115944119888200070805001c3d6001e0b024400c41403d9941c808590f68410080c0b858851280388004107500c10303c01940703000d15856900034050b164046c0d016520b6a00fa080c002da0092052900450b81960b079203001000d885490f1035814031340081114442c210541030040420702e4085e4040c9101c070740022070b02e4050340e41000d40c8607102d089042d9603602d2203070f020b126050040058403640100100a0000108802002e4420342d94082d00c0401c0e1003040d9030640c40520301c0b41280a2120442c0c154a240340502d42c92908c10601000c40400c4100c404680c00c00003040c0086003e041803001c0b10b512681011002c07901d1700c04540041d442100368603030030419101a520403a8010744c8620050070071204a007054060360842 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 757592706 1250 757591456 757591459
    0xf020414090313090603030203030613020c0318030c040c0e04020c0708030316140a09170a15020d1113060f140f040302100815060a0311131e0b03070302090d02 70
    0x34803040040d03020380800203140c3c2003041502041c41c1d0391624138250031903110780001005a0320400125501c0d1500d108001043c100c48078001d4038041c0400c9000d0308503082004030f2043c0c4000c80610b01084d150504c02007200c00d00a540801c0049040b40c0014401e03404614081c0c050b42d8002011820a601170151101804840c000c0381d0340c0e030038584a441c0050980e480350400042181c0403011010462000300d52480825540c0d42d10020309204080c000407a080e5000c13007152003412060385c009070342e0050507030607184500c0c40103850340541007a40099075810300a07030003805403c010764a0000b01008200b001c0c1c1e0300030b00e00a1940c098038074040c0c0b01d003200d464212907071190124141c160180361500034400c0c0c900c01c0c0c1e02156107a41c0c00c003040c1c0d04030030103580003d034080504142c00350508103100504810702c4c07032f4500852011840b01c3c046146520640788001c4c5c0003402c10b02400542c031000007226410107181c07000720906e45050030740c0840d030001521030000c054002410144035920711503109100c0e81c0 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 757593956 1250 757592706 757592741
    0x414030d2a170a0f050408071a0702130f0b041814010e060901050103050d0309021c150e0105010906050d150e0309180907240e13020c061b09010c0f0204 67
    0xc00901240d5500421075400000d0034013082d00d80c5851180c0156012180301070010002c450a10681d1204004612048204090188019800b5070fa48000303480111000b91350010392200701c00480f1003902c242440b154042c03820180405040100740741c2940070540c0001007138810b94a0003100e42e014041000002c14140700d80010700926034010750000d0b0480e4414030443d080e82c54800305c26020b803001e100d0048d41c4003200310561000c80c08110104203c8601ca9048500b8840b0174410340c80c00c485242c0b5600d0400ea65400c018803130f01c90188200b6000c0d000031901039000300c0d03056031000303500c1481c500d076509519100c444080303102c54200281c5030f007540e009004010341c8c43d50428141a03684229080384041c03040d120002204168038285ca030500504520080d03500ba228681039885034030a4907410780115810400030b8490419101130805151890701a02090800484402c43c814800c41c401c1c80b001c1c02000320034150782e0490311b0100750710b5024680c841d100c0480e000003001400304e81e048074000032 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 757595206 1250 757593956 757593983
    0x3060406080a12080a05010b0403081305091e0603010b24190528021b0609030706090501090e0f06040f1803030e1005040803060103090c0801110414030d2a 68
    0x921621940f24016940d903030812561030140c2041618000e00c00c11124000400c010700210b04100d005018030452083e0f200260750341d480128500f9a0100c5034212400168400490b80919001c0641d0700311304220003d111030f4285400103560001c0121108800d41c402c0e0310111b03489004001941d030300d07440038003560003490070345240035000781c2c0060000d03078800c03054581e0720600c4042001e03c4007401c2c80319401011468203450540003c1002564215403004080c48003541d00e9401300f2811019203001ea5501e81b01d80c0c5401d001508845580e0000b44040d01030504001c450850340e098541d01400840b00855682d901d208444010060505c0d034920b200c0300207240e5000e068158002d09044000001144c09020b500e00b180707003c0721410750b4000d00c00441003001c50101e621903000f400c3d24a00031112620515643c10000c1e0841c3d000904100f0460710114081068a0520950300540c1505401900458207440801048220300c800781c0703850801ca001c81210500180c6c0b010342200b5a0048403604e2a6 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 757596456 1250 757595206 757595213
    0x6012601050114191203080609010b2113021f0315150c0804051206062b06091109040b01050a060c02100c111005071403040e011503020d05130606050102010615030203060406080a 78
    0xc280807200c2a009d415a46d00004203130042004a4042804503e0004100c0c4228482c011116101410388213600c11040c060340003580c1c801e40315841c090780c2c00744200f04c0c0400050000d010f072860700f42d065101407144d00b410000008500c60404214071030f450543c485420364580281580190b8114a8101d00541c842d01d044072000280e0a00401c0b0407543300c078404904c40002c040c0e0345520455a070100804012080008400c0e4122201c210712076010740958560720800700c2e0004508460035501d0b05408001000a403c0805245025003c207207000326039400240c011860166114a4020400c541c410b02641880760503199200e40c1440185110340c2c520001e0001090368010040c15110b18030390000c2d4001e02c1c2d90010031038046a403011903000150b880e0641041043c0e0320209004145502000743d81c0c014401c0307201d154842c2900680940c0e0b18105400c00100720341c016084103065a00d0000c3c24402600c0706c8034106107080e55850056500e0b035404002c1000342c2a154484070083c800c5103090400c0 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 757597706 1250 757596456 757596467
    0x30f0201020d0c0513050a1d0612010509100c0519080a150902040306051806010e0924011d0c0316110f2514090702010e06012601050114191203 63
    0x10004440500c07040700f41c8950411080b087ca5109492000342d0188618030102c0c40c0d01112584a00001c0c8013103d0520081c8a00b0300303541085421030b0840c0c02007040600200f1082c420042252114030b0f0090810590606000944000e0b1110740e050000d0140020b4101146030404801780002081e46e003000c41ea034640c090080c0d0864081101d0302800d0100141c8106008005e0102c454180002458180d00c0c080000382074140107483c40405008146582c0d555a40920301c4600d0850700085401c040d6142c40c1001c9460240c195440da98203400b40280714190f0140400e503a00701c40751503040100d540c41c81c1003c1c0c407003030030350044e174201760082d0115041000c60114600701c0400d803100d031501c03002c0c0d004440702202401c140206480710131500c0340320030103003480d01780d46900520030b00001031541c4540001d1841c0c05d400b40d00c41641a010240807940d20203000c9500d84a60114000a00c0594146143c0c10f200f10302c011541805490207201c0303000d901074295091001000c1d194410140c01100e070600034174 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 757598956 1250 757597706 757597717
    0x309221e0203180606030c010507021c05071406030f0a0e0a0f05070512030a0f0c06060e0a09030e01021605240c030c390f04020f0d1401030b04030f0201020d0c05 71
    0x80f4902c001c2c00209500b004c108180b00d288002c0203415003038190001501c003038014410990304010354100300303000c00b80a150b507480000d00400c01000c905107480c0a000c003040c00504001c4c0281010300c18400703820108582e440c0c00c10031256000c0b5014000c441d18910340b441d2004003611550190040c803040c0500840d5840030f41c1d10695410030100315060b44107a4070720a444401000519442c04000c07845c4c03199500200b030717138410724000c100340307030b60314400d2000c41c80645000c00b40070740d00d0003000e08042d0406052884080c003070014001c10720980001141c1c0f40c06910605004030a014040c038240b400c0c3c881d401d213224012041c1d4a0310760500e4104503a894000041410360340c820301d850105d00350780c3e82c284240106400c0350010540180036442400b101c001025940d0809102c6003d041a562240081e0030714403800c00030591150b00101500b4159000107600b48240750315000140040b90004a0380da0380590941800c1c901e0b581d030f000080740248642400310700c1e014944509418101d82c000700504 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 757600206 1250 757598956 757598971
    0x30302030109050c0405030601030308060a0b0a050a03051b1c02090901030b2a190c05030307020d090b04060804030819061404051602031603050913021306020309221e0203 75
    0xf5590309045029184118001c1d640c2c503a00c48001000000e10454069900074406810154019035841118000c1d410002144004c01c42c0850b00d410000c1c2c0c1440f80355407101c0d0350340d5078840c0440010b01000c2e003441010710f400380c0014209991405c451554044414048005c1d101d082e1560f92401d08012500c4182c9510360440d804168014000042c51048040402409d15951130000740d040c13084030720a5034030000d405000c00b45500101146052000d10310a0407070303802410300d00003156401449030415400c10b990381c00d01071005010069210006076880703070b0306060000c1142c07911003401c0170f03e42c074110b039144c40c040c00d100e070210303100031000d19200314840252814419030716400c1c0903d428112a4070030100580c02405820450103a5580000d03119009003001441c6c503001d03102240151041c071010801c1c0a03000644844481610700b03810008110600c003a5040c1030a000006a01492414801005c5002c1c6100040000040d5114040c1f035601c0c0d01031010403841c40d00c00c04002c0c2d0011103008 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 757601456 1250 757600206 757600211
    0x106030213050f24120706020d0c0c050f130615032f03060a0b0309071406070807060b1f0f20070512031b07090501050f1e030c0d030302030109 63
    0x41940c048075014481c00340008010199095641030100800754001c040c44d11441c04512802810b07540f28002d24801d00805c1d4009880c0041c108080039241c003e00359104000c10440029000208049151013800d5a07411100010f01410410015403000214588120b1451918400103a0440c0351041c480740f60003180c400340080900098211914161844151900d004004000028006040046a112000500108015448010410040e0400c54135402c19a00c1400b003406982914220341d6004003088070420319202c0c80c0d65030301600c1d00600c5001880951141102c00940d910044029040400c440d03070003117a01e00c101c00040c041c0343c1060918000c00c4541a14140c50703d003048074030b0031042e00f85004000b41403030081485900c01c0402040030b1140024812a2100c40d104040d425982e44d04500a02400d4148041b1108540d41a442140701d0044064915184e440d24881c1e6107503816030f58886c3c035031002c0c5480031a0030140440006a0b00a820000d06001c1582550285043e00d0100e00c04 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 757602706 1250 757601456 757601479
    0x2071e0b0f040206030f06040f09031d0613150c021e01030b03030c030403030c08070b130605071b1119090906140408090603150a03030c120c030e3001060302 69
    0x30401c00c81c500391406500003c003000050401c3c69514102ca40002c00a40005280218581e840048403035a040403000245852030a900008500f00100503d41080310014584411810000e60618551241c40f01d070403048207503412800d01910b40d82c60b40701d80291503240c800080c0c10681e1241401c000025000c40c0c035001600280c1e050000940384601e030440c00440c6080d007151010b41e81030f644180215403955041002d100010784001909024a041c8820074141401d2442c06000791580141a8002c000c0342903d21400c0d203604030403094042e50485110340103501100040380b009610f2400303070503401e007041c000060040b800c0c2d4401c0c4a0300d80112007c10041043d08075071070240605581c0038211000520038001c051901070001c5400c0045c9445082c4821042d01c00300394160500e90050700412200013540050115500078504514010300c2e2442110f00d00e81d80c0030f080c030410a0100750041c10700345565921166a00d00f031100c112150446210600a40d0031003d0107400240012401941a0307001c = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 757603956 1250 757602706 757602721
    0x10617010f09020f040902040e0f0309010f05030f1315050106020d090f0e061c0b040b040320060711071a09121908030705040b0d1d070501051c02071e0b 67
    0x14882c1c115402480c01e0582c1c807002082001038801984160b03801641c94507030040c221001c1101803540c854000c043c0d5140c80d4442d001410010702c0a08050174881d04200704424590041e04c4c5662011180c1032072841145c3c0c030300b0b01e07030301044e585908000260b02c1c007400440d506e500000c1244c01d410083e070350200101d842e05810a0026803d00c143c900c43c40c4150007240e15458440c1010303041c0c00741408440e001d01055100c06c0c840410944e000e64030780c1c00740f0040c0000c0c10785c07280c0494810701241c0e904401012682c10800e54400c0f004144a00f0003180d0491036104404c1400070070001c14000398460245e41202000d192142e201d142220320070294070b00d20403015180031421528010030000346410744041d80e00e51481300d82c0002c2c40c0380100482000f0102d0725410314800743c42d091182900c00108000465034800d00300c2c02c440c800181d141e000c0e00c41082030340c1e884011102c8840368038070310024480b00f001041c0064054880d0040c001c58102c802030403214401020074170342a000b110000641d448028 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 757605206 1250 757603956 757603961
    0x30405071a04061e1110050406060f050105030f0a0e0a05030306090a060e011707030c180c051c020c16030b090d0c0215031e010b09030c090c0406110f010617010f 71
    0x820f4102260030302810610040c2d14444650003000785040c0f20020540c2091517074281354082c211400e00e25640c80501041c41441e00c1000c016000110208611b0746c200000078010f40802800b091807440204002012103409402c41e100014a400c2164000c0c840361420946a80040b9403040c0601ca40c880058220780b19400b5942c1103510282c01c0050366401c0228039030b00e601c040f04c181000c0f88542c0c900000020600d250810050003444820340e82e06070b51918180545600c0108007040200c1031043c02e10f0000103040e041c1c4484281030700141d440191800302800c0075513074201c41ca481d81c501c110000034003012402d150722a0000c0c10076a41c400c803501034144da9140500d030001c0d4104418031a00100908844002c640008482d0410801a00c3c404015120a802600320762100390000c10200f5050030104488081e0603022100c2c10907519110007643d44501607449030500b0010ba4000c2003c20041c1405611560b10500700240001921603425420b500010000f00180d5880c01114000c41110751 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 757606456 1250 757605206 757605209
    0x303080a02090108010b07140712031116090b030a1a040209180a030c031209061d060c1e120703150b0a0c080a0201020903010216030f140913020c03030405071a04 71
    0x141c44d80c1c0c10703690800000d440d854105c2d100403100440003034900d00100d10208248030043c10303003047c24208a480e0b4580181207040003426904c10350701c200c06810300c40d075100b50183c6c29a03201002c00102e0314409070000c0c0c42c22009207070261a090003803d403400001c0c81c288a20f0710a50080c3c4664069803104e8968848881d100d15115000786c2010901c1c500091250f0204412103009241ca50000c015402442048803017020080712003a550f5021b44110541c2520030542680f0750f0406010180307007180190b0100d2199000b000c89100403991a120181c40304800d440030019024242404c03480c2c20b480280061501c40421340c2d02134040306000a0b1003000000302c0300c135134100340c0c1c42180082c039a50311301c0056000364544506554017032005500a48092024060101d54400c02c0c2042e65441d08010344035401c88110403003003040131042c1103080a0070b03104841d00c8a9041e110035a44103019100d09000b030003500001075917404000706000c1030010025000d029a80f20f091144100e451629100c04540f185 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 757607706 1250 757606456 757606459
    0x30a05030403020409030c060e070f0f0e06060f1c0e011a03030a1206050d031e020a02010c0b06061c05070e09060310090807060e03040e09010207152c070303080a0209 73
    0x700700510041c2055080705404510074188005205207642d203c2c4283c4415214180b6150b001100400100003194154402410382c01000b07101c160038244180c0410600910881c09a100011030b48440440001100c10107026080ea451021080c0c003002000b500c013440500300a0740c2010102c00011154080612200000078000c51801c0d12080b4181e50729040481400702203035840c440010551030700000030f80341070b101390380b90722010b0009084030314100e01c480c0c07014085512003805080180d8100d009055400d4004491900595800c000a0080e108100d1000010200c4040c24420020f998215074095912a11078045d128460010f010704200f0403202d41c1c0d4194042c118141c1d00103002d5002c80120350266904518000260319070f2000d4686c03010a08219030300018041002c088480c0070b15400400401c000e624059051300e0f0340600081d004038100c0c1e0789554244003041502c9068014651581181980840c40010080552103c1540c4402d801060680c4005800c03d495482100c0400b0350 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 757608956 1250 757607706 757607713
    0x1a03010b0d0504020f10110712020a0501051c29090f0a020d0209060f03010807060c0510050c09031002031501090f03030c05032712030c1209060f030a0b01080105030a05 74
    0x1601c040100142102520a0fa04008168210380341600da09191304150f00107910b0350f10707840c0141d042c554600502d5500c100400d018100011005a0b00c4540f6401118424641142c84070010200780720001c0c4c05202d41c00b2a00c0ca4a018083e045c1100030400340503a04284160307200e0300581090003911401100e2030306c200445a8002001184e03640e02404018480c0d1b400142040340c1000440c03070f20741c03004888070001c440c04001040303002410810000602070b1032400798041c418544e202c3c1c0d40c0d052900e94001009848400044c0800d00300400d554204c0d000800b1624202c01c0442d41d10020350065078652002c0982c017805044650160744148200d6610406841c0d900d40382d0b4034100c80790400d109040700c0f180800c2003403c8903031402d04070034040803281010f04800301c4140010400d00c0c040c1300d600201d80e0340050151100c4594003103401d080d07001403041419501c200e884c000900610440051402032000842441803000c5031b0782c03010352180b00a881d03111042c1d803500205503841c00e241d08001c00035130 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 757610206 1250 757608956 757608967
    0x7270302040c170414010207021302030103140a08091e1003090b011e030b0601020c09040507080c150706110d0606030b030c040204050a1509030f031106180a020108092103011a03010b 80
    0x1440317a01581ca1a10514000505110300d9070700060200320700d000840e120540110060040c05094050191b00703101c1c0038010101000707150f403221101c0c0501740d60340784208007801c0c140a00c1c41c00501d41c18003282e0002d0804004421b02c1c40d016006080d81c200541c4e0342508100089403207214598400d440304038440b42114007034a560780d009940303403000b0f001c0e81c110701800380441d0150315020781a070300541c441c2024041060412142c280340424440aa902c26000700e16001c0c003445c01c509c2114980780d0842c2001c9403c00e913001074a1035a20490b01465640ca213071a5000070500d92580c041c2d80c1d00f05085060b070302d00f04198010032050740118052254800c4070020100898805803000511414103810701a001d5076407503c4205000700341d2a070940200b03001540c42c9499240078090b140c3d20a1203003102039a075164480699550369070b500002410701a0140c003282c030031803081080c40280614400441165480c10607019080c0d0020b120711070b09840d41c90f04014240321050245c0781070310f007902100760511 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 757611456 1250 757610206 757610213
    0x1204030209090114090a030f03090201090510030b091801140f070f120c05040518280e07120b011719110406061d0612010b0307270302040c1704 63
    0x201c0024007440701940d83c9908400c09039814540071803040611801401c8503d0341820041c00881c810415401018036203000000140e0300003013940c06581c002d0324102860b1800890582c0100140c1c81082d6000030a0801c00c811801c07d5129060908007090003805100d0010700d01103640e103025259624036410080015070900d200d58414001d4584500d405040301d4100404001103618084186001070b40c001000d1045040001c0d5a28a90000400e42d0489191229111166004d0103605079045800f0780140700075402503401c10850881c00e4000c5c0c41c13aa50796900040c0044240060031140501d69200010324240780001138070002d12440c0107407481c1e502c042080344800780081021201c0c1da11300c1e20424020740700d620be0360000d40a1900d0f05c103104d9230345034000c600000459080d5840b41070101300c2c6a840380108665581118410302d645030b160f4071503a00c01e80e482c40b0346a0011003001d500c4240b001d500b410181902040780e00a0780c01304080044503504550745141001101603c2c0f12110115001 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 757612706 1250 757611456 757611469
    0x10140f040c09030b0f0a0b010203030601020a060b060f0f12090604030801090b060f13050102011104061209030504050d0f06180f1103160906030512030f0406050604020d020a030905060912040302 85
    0x18824914180d8001922130780c400756040c0c030560300c00b10307009400010001050780300c0c072842112040c240003c5013140341c0480001c0d900e102a0b8030041a064403442c0c242000e8a6010685061416031a052501c60104811001654101c10303280340644240902140c840c00d008070700c05d8002c68243d56107072410784c00c141800014022020780640c00000810581e00c45248900240080c00161031604d40524a040002400d60392030502110a008040004002c0903030480b00d19001254201030126920440d400e054420340a107030710441d0030079540e401080403c030008bd4103030600d030711a810400c40210039403014002c0001c0300340020b0075030f03c03040010f1004c154041ca201c80006001012036504c44071814a5140130b0455500822041c1d0300d62009104000d014800308403495401c40c061815454030100345d080020f0050006441c0356611004a0b120741c6413038040300c1c54001d4031303407040d56581c03901d8000400078007035800c090310180541c001140c50070348040303140030202e19024a400d090034190340070442d0 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 757613956 1250 757612706 757612721
    0x90305031305070306020a0e0306011a1210030812040c0609050a0303030f0e07062001050c16030e090403080a0b0d11040b1804120f02070803030109020714060f10140f04 74
    0x10b061003001c0f00080040c5180c002404405500ea4542d048115401c0c1414500101a041701401d2000c0c1070a60201002070000e548210100900d0006203466580c226010581903400160080400140200c85e082c0300720901ca014520512780d1040040da0b900c2d0032685100355014881c1e1109445c0d1040001c01d120b0340140d4807440280000269011801300c40303130310b044c81701d41c05080440d41030f0000f01031001b071107051240d104010034002c4c0300c00d207030009011074688520f4051642208101c0900300515116040d030085c2040d006c0c5c6201c0345400c3ca8280030703104002c103c07110700030542805200c0300107080102003903a00307561280d0111654411007040102801c090811a90001c2c00b000040c0906010314554601450042803a86044003000c0030040090580e0301640f407e55109240030010400c0001c203c030304482035241c0040e100e1486140c00d00400c22441c507110081e00c20742040c00100d200103150140200e51313000c08150000c3e544c20300030410203420503072507500406101e09844c00e0b04203074010f0310 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 757615206 1250 757613956 757613963
    0x215031f05010e120c1216050402131e08070608100501030c080103021c08070c08190c03030c03050d0510050418020105070209090a051c03060911160305040b22090903050313 76
    0x122580200780c00704040070b00c2c024141b000f40d8404034114214102d40300c5010090182550151b291550400740c00103403e40c5d1344520005465060b0038040050303442c0540300c000e4403110096560003a9581002852200141c07101c0600003800200041c03650302074414a02143e00c140c8401c10207a02c0c40d0200640060070501c2041c1c540444002c0ca40082e6020005200c40b61003400117030b00700c40c00c16840300d14099040742100042c2682c01951004241c520000b80c0859525140030036040c209454111100e024a8441c0e031441070500041c0b184403c503422406084d10400d4504011011101c0d44110300e150b80200c000e800b1a004001c5070000d4103080c0c81d029400301040c000c95980030f00f50341e40d6030304e40048488210340207810450100300260345030007103600609442e2024885024030803000c69591180000070b00303a0202e03c40c01703070301058014411fa0740100130000a080c1c0707441c90362142d41c02401140811a910003c2c00c000850009400e1040403092505642c6617415a07032191400b11403c5d0203050181c = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 757616456 1250 757615206 757615213
    0x12030b0a052d120f1e06010b070302010207020a150f02030301210203030906070503120f061309020f09070504060305010803031b0d0f020706020c1e030a0507030c0215031f05010e12 79
    0x48085031542c810f804900d900d081c0041180b401d41c9000581450361400c13440440c00045440094650710004489055a4000000701d9031082a80780c1a40280303d101f400030340001d411381d00000d0075002c046004001118903110245c0116a42c4c10490310380c48240107108100301201604031a0b21001c8015903010342c4050122403410088100140725500304440c122103036880000c1401c442c000d51407601da00041d00e002d000065052420000d00c3d445031040c024110199541e04803815544c917010812503491000c0c00b40c2c8001d06100340d00034159406030085001182c20140002501240042124800c5040c206074000c56040d40d0707841c0040e80c0c00381070107142183e2101c03800e600b803e40340d1009200f01c0d03110740c0c80103a0750f1000c035050505204007696041242000d00b0006454900701108071080403c83c3d01d0966610211460151218000c0d440069003120018880720001045200214001c0514445a12024901c0d0342d00d800e130010a409540c3c00a004241c10b541c050070003510b01e40c000f0142900b83e = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 757617706 1250 757616456 757616539
    0x6102a050105101505070503041503090c062a0209060904051f0219020309031209040204091107050c1912030e031c08101a03040c1212030b0a05 63
    0x34282552802d5070b002c2c0f01c0007030548080103051100d808140e03250b03050b418407500303021581d00c03095241c0c02644100341400005401d405141440b0781d1100c001250b00c000015402c5845160007819a41410814525030300c190340115458075100e50980d50f542d5000346403081580c2e4401c144006501c02400486091242c0889103402c00c1c00c2009440d40781d41a500c0050311140d80080d91180c81e11200c007008159002007101920a44000c505400301790030000000c3d903124080c001280c0248207980c00480e0040c41c0030841201c00300620001d008050155048441d01c240301820010103000b5614008410030814030100400e051161010014900a04000c1ea0007030906001c0380c1000d00210300c03d2510103032280050082ca41141c2101c1e00104054809407a16007130000c01140052240b2544a002d50080001001c10000440b88009880b14080135004441d807072070900b02c000d00b0805604007190509440f2000d50a01c054a41c088420060841202451040303605410040d00c0300c2c0c420240c80c15810 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 757618956 1250 757617706 757617713
    0xf080705070b060d0206090d05010b130603030206070e13060308090a05100c1401230618060a05060d150308030f13170c01090203160915051807020a020405041202010506102a 76
    0x904481e003038049d07070010844055440c00c1012205030300e1404240b96140500074008a41d0014140e940140e035802d16074003084000307001901d01c1c00420740d181c07401d5007403200110400c0b0b07689010b0714501c00161081581e0340d442d0340800140c00f800854880000b02c803948030101148690780c4072480d02075454000201b81110450403101206111500710b44002000c090000e07078182280200810700000d00c004600f424086d000031400300b407600c942445041d02054644400c0f1840d40403003030740305829003150b585c9a56441c10401c2a04116591050b120100780066082ca51480d4082107070365121282d02d100207000c0300400d19642064070380c4012036607541600700050710100321800c01060b1040c2460312081c035182e0000300f900c04243c03c15001d0140540100000d486020075040002c0c080c00c07420351517640f151401c030300c0c0c148a0b40d0003a41c03250a0406200600140c04200e86d032044069000340a01da030b8030400d204e42c80ca6070b11a00800075000d00d84060000a50148041562160240d8802c0c0d103500e90701d = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 757620206 1250 757618956 757618969
    0x7050d06031101020d02011b0f02240106020f0a050a0609060e01051f0812070b180102030c040e0705031509072312090d1403060a150f080705070b060d020609 69
    0x420407100d18910410300010b6680400016056841c984024005d12403007140b01024003042030b2a21042c884607124040302c090003800500800b0140500d00c1e03d105280803440d06130381d03c0a10903d00940038a4108031a16540400c803007140541000c003d1402104640d1104011311030b4400a5403d540e40d2003d46e003402d02c0a00803039005420589038400980e4200442c000c20f10015070203091161b22204000404004450540325200d411455841c442e58540042c465110501c54103240e1070b520000410a15042c8100035009440c042c9c03040d145560b0315000e0644480c4400d0340e58658034994030541940e146409640541d10001514040c007c81c08143c107050b0a40303051780702c00200f481000c1459032854071403420b00c540c400c0b081c00090900c0030f482500540203424800500313b000c08000009456a04d4000b058001403003a42c0e05094600300f590801080d400012003582d0005140038041484548100c081d100181c0e04002030981503281d8908015840e802d0a42c220b0300f0640c04c0c4040f0541341d4409 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 757621456 1250 757620206 757620209
    0x8060406200705250324061a03060d061113051002010203060d15090206031608010b13091e05011503050a0c08150d121710120201050307050d06 63
    0x3a4404282003802032100500d0800c840300c00100078109216190200381c0000303291510070111244882510940c84010034511032903000500f00110301e80e4000303048000b040d510300e644001c0da04c2c04c00403107440c1c41c2c811401c00c41181603040e01120138800f1540f285001c4411485075031180400007400c0c0c91030a0722000c2078125410784903240311862800c0001e4180b00f040304940b0591b6100031451490120005025504101000b40107032510080c4003081c84030b103500c030300c00b495001800c0607280d141000f0345501e003000b0241c00c01c0c0060350441c000140007205000352000c0e0304c105016107410074180040c0d68001c040b01940c1c0d840405442d00080e94103802c91099a020b480f81040c8004021f500c4034014040d14006400580304618018040701d40703681c007050301a0028540b50700010100f11910024800d914600405080c8079418000c01d54507680140c40800028041c0da10103800c7c1d0303201d44440060040a108030442d0603280c44507880150721038001141d0100c4107040040c01c4c01c1c83d903031103c0f0888049 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 757622706 1250 757621456 757621463
    0x311120708030a0905060a0c030804110a14120105010b0906130b0d0207050f0a0819120f061d09120c0a1707020a0e090a1217040c050901080f15060a080604 68
    0x400da01c3c101e50102ca8500030300815a01c0707529024030700000a003201180170019003002422404a010040043c0d1510b00002c80201884025500c5d148504207103101d480c0944d1040e1560400c0000340c5038180501c504035109003070484d04241c58a4240b160076030010030300802d5101540304c08210700b6100c402505024411304d60041c0c0f1040d062a1480c030300142d003682d01d803d5921100350039001900c841c00710303600c1d01807108680c000001c0100003a03441c040d29113201d007189414461100c49400e41a482002200e4099a01028040910190000940d4283e0b0502016009403002c141c1120801c0e0040c9104003040c0215507820f03406403500c00400c43c04528210ba00b0304005607110951078050706800190010001d04504c41c108607210301c0c6d4450816900a1a405c0c1e907480204940e40648224107815088042d40c9803280351074a041e20301c642c1a802040e200742001c40c00454078140024401c0c8481c0360380d42c0104010800d200c02c201e07864500030710030b581c04100032401159207102401910f029030312 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 757623956 1250 757622706 757622713
    0x706110901020105090714131e0e0106150215130804090504120509130e12130f0902090105041a31051f1b06021615060509010311120708 60
    0x411100090941300302904545031544158424070083c0d804410f007034600300084604e26403842c0b04030504005001c00528094200301c40d20b119010070b0039250008900b0518200c020010541c5984004000c03803403031003101005911aa015030010380c05d0024058001c1c0b2a050001c98009007561011015885034001240349521142070108101e40c03a1540000d4120324240346090020400219014074001108100402d4480d5004c010908050200f80c81c202d01101c034030b0303960355840407400d003440009216000c5140b4803400d0024030f0000030720132b4844c3c2000580d21a031616251030390f186c2200d8104c2199484003030081151590200410b00041c5001d040300050078066511034909c948001d4090b4442303406914031043c2c01c0d8001c0a01418501820100c1c148240820151441450820080301c0010540b41c0b000078460103001d418030f0610101c038130810588218407880d039000c00a0703848a01c9080d400c10551401800000d6003000344c1c500c40440501040c801143d0950000d1401007a60b200c1d981c20341 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 757625206 1250 757623956 757623967
    0x11130602100e0a020d0201050d0e250911091905060307080106320d060b0427060806040b06040b0301090c1406120720010c08010906120c03060b06070611 67
    0x141030150802e82400000503240580c601d8001c00c540240c080c000a040040001d865990350019501c4070525000e0a01115080c41540d40009556004000d4121615116040c0040c401c031076030244651030310a007800d19042075038640500601884966480d520100c40120114654036058040e5200750007643d102d27002d95251003800350840c60320141d610034099100b103000014022040c11b24086a102c0e640c819590141580200c005042d03603004100c83d05030001c1d0010708080d0303088100340c110300030030303008054081d090b01000116000b40c401c040894100703400240210b90110001544028080c1001c20102085000642100c46001044501703100300b8500b40180503084100c0d80601c0c4060700c10b1441c1c00000d034800b00010b00001c0c411030411508100407030801d0b02100409510a0704c24009002042d985040540440f07802d015840e41c041c030348480060070310b40e81240d0705030750340d008418490300604580b1003402500354a5000c0317800036010026440000e05621900145071051010242c070780 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 757626456 1250 757625206 757625233
    0xf02010c050d08100504021602130e03070f0c06020714100c0204050a090b09010b0904260a020105010e3306040b16050c240309070312260907060311130602 68
    0x48541000b4001c2e44148405006a0300e40688c0c050580c0d011281041c1130a034084809003e0a803a030132102d11800085440820011559000b4100a00c0b88681311000d5803102d1049a6910240c4078510f03000603412440b280604003a4007a01120f003079898981105403441c0c02040039600300390b52005640f41d891039034405100f144032180e504280008020301c0582c801d40e001400099019002420701c0300342e45002d801201901080c0f80074900c401d540141ca500c21808068000c000074440d0f6000b590380c800002e00f0800d1407145104070710780c1140d5121001c02c44400280c9202c1d050103e0b05400031000c001c00304a140424011b850f07103d000c0e0030000c141280500c2c00900348007030380c13503598000c0c185860705a4090000000048903078015074219a141d40d5100b65451070300c241c40d807019006040c2964450314840d44036442641d0651141903081d0007940b041c0b0250b000d44021641140240c0240c0307014410144250010911030b110b0343c0c4103904000c80e040c0c6082204c4466408200580d1210781d040d40354 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 757627706 1250 757626456 757626481
    0x106031a06041d150a140d0203010c02100c05041a0d060512010917120117010212070e090714160201091d010519120314120103050f010e03090d0f02010c050d08 70
    0x460b00104c6140031135804000c54041c2c50702c0d0291841c410b450084404d00c68480014106440e41c00600a01004000c40c01c041d4440386038800045a0b1814081009081800369007214112400003480c100e03180418815400c40d5004450b101c0d4405845200003d0b8036922411200707403003100d5000016a08001d032921039030348031162100c1141c5120034040300c070140f02c241000314115903030fa0101c202d1500c0a80c05260091142c8820703250004460301c2070000940e8032111010309544181c2d00600c440e250740d00c003034822400011040240c90400c002c516180007400f4100c070007803441810a55205070702c070403905600840123070030121031803102030040146c0d290990042c8404441d20010b21171082c1081c511300c8070702c6840b10002e4103100c0140c020700340d010203e10272614500f40075443c403030055071030349070184c0c82e1a25180706a5456003840d0b840781d0030640c0417003194a41c00c40205840110b29141e6a07100029510600c140d051016100d40344003c100f09201198206440d543c0703000307051602180e00c0b4074 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 757628956 1250 757627706 757627711
    0x3050d06060e060f13231e0306060f0d0b040521040803070b070c060c091701360b07050c01060b03010303020303041403091302070204140408030106031a06041d 70
    0x1007102ca00015030142d11041d080310a10140300f45226502c801858494030110000c2d40000512540c180ca00f00710102c0c00e03200e01e07101d41c1040b00c40040d0b40036458a034030900041d24030599416040200070505c149055074003072602c80000341030400c182c0d4280e150455044ca0485003900c3c01d03040301c13440602c10102c6c540d41100e40c080b044c0c1d040c0c0c14581003030180c43ea2070042400c024520006480840c0701c0e00d00440c40701c1d00c0b4030381c428014440b21941c100c2c018000007141c41600c280403214030b401464080103004080340840c080c9018000e450051094403c9204039240564041c000031064a02103590804564132540781c54a66940d00c03024460201d0840c2c0c1291b1000300c141600780014000a44d010080320f80281d045104907591209143c103482c2188200d41345164004400d41c0946149083c039006081c6c464000c40d0100019030f401d2281031341c08502150020051081080103121040c0280d00402d0148141441c2608440040e03010800581c403d401448140c41490f92000c20f03501300d044130702da = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 757630206 1250 757628956 757628969
    0xf13050a1b020a12050c12030a0209060406021b040515040207021318030908070308042d0f140904021014091801080d02010606120b01170a061d070503151c03050d06 72
    0x14500006c00c0c140701c6d100c12880e050303412586400808500b4500c402d0701a034810140c01846242da5540d100e10182d0b9130f500000c0f4407442c06180003065500d034a8944600385c0b240d50b8500341d4040500c030400402c002540204c00481e400142131282c079112080074440e00c0c65482c13000ba40c10b09413003494100501251415884504582d020b4002407000842060030ba40456841e181c42c6490500d00d40792600380c200014094245074518041c0002d8001c01c0c202c1e1a1080b26032003040c01e10100580410300141c0720040700c029402254643c000d00d00d10b031013a8100c00c07001411403851410038141e000000d0b008641a2051600b50207030358010300c4621020f00450500c0340c1f050000300891440d042c0d020300940303040703009a1100e42d030310090711245901411094440d21486030041105240441e80900145190300800705c01b04882d04198ac1c0e814203500250340a581941c94603411541c07079101d050349074081c5801c2560806281a0220302c0c111068400050070352281e26503940392080140020212200c0b030740441c = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 757631456 1250 757630206 757630217
    0x1030c03230309012f01050a0b040b0a051c060e010f0b2d01020f100926041802090d03020a05060601020a020d120201110304150b0f13050a1b020a12 65
    0x1c51107400000226070742480203090a084540c0301a0492480700c510b00200c0002c801030414600386100d040d40550700c00c40b20715500b0000b504542e802e02c8100c032325a410558201d561078105105a1a0070444421040390300b03100d89940102994510007620100170384211643e460700c10324a441c5010340110114548162464101040c05c504141800e00601c0605a50010400780004003a4400e11814001e5011a421141e40314a0980440c0c004c1548100640d040d42402848070f0a24003071541074079180980d042c0090500f41080e143c008002147c01520f04001d500308141c114603210078510f0b0b01118000c1e00602141d642c242009400c01c00d00a10260442d0411101600140c0d0342c0c1800d80d03210354106081e050105418502640101052400c0c0302200e2408820082005a1510004902c5540600a210784040c1009011001c012030803032035808170307007080002c1c1c07544559841035510440c802008240e41d540c1901c0902303480720500d1900010380155401e2414000c1034401a1030098491411 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 757632706 1250 757631456 757631513
    0xa02010207020f18070e030118031713030504180912180902030601020706050309190f0302070602010b33040b071b0602030306060d15060807020f060601020c01050a120501030c03 78
    0x1100380420b0000c2c0428140306e0403040d1001d494900758842030416000307a80c0100070070030504000e010b001012400d01011440c05000455041502e040d4040e086d0307158807241d007498200004001d6600000ea00101c101c0e80d12603070280403d0380203103040c064643e00e44600e580c0e080c0303c40e101981e03246a900804401b070700410038020f269900241502c202c40071450303c01d440e40c44a00c011820465402d040d900c031904081480c0061144250450422502ca5003c40710201c1d5107140c203909171040b071408130707a00500000313400100ca43c5140301e8403005c96885043d400700c80c0c0d4040c407080003500640c0000000b9080414a4401c0041620018030344580351b11390503440d140340900003580c91100800040c06210045800700802c256604034040087d409055040e00b103440d4400241032080484098005209200007150480c0300420024004e940603800781c0b6034034243c4001510160b00c07605019042104201a8044031129441180d010b1885250030a034078500d9410013001e141c07003064072041c640d0205400c = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 757633956 1250 757632706 757632739
    0x100f0506103504060b1c0c15021507091e03020f0f060c0129010c050606010f050903070f03050c150306190909051c02070f0323030a02010207020f 64
    0x100054006021480e102c0c205650000d5250900c118180c2c080603906982404108035264000b140340507415a6030325011060101c244c5a1000c40c0a80a80b031000c8a020520605151100b600000300a50045800d030315841d18032804194400c4801000103034100d0402d024042c13202d00003000150000c810640c40c20f0541e00040c0065014a41c05c500c10302e414000b00d4001e45410044d1030400328014001c200c0b0385486120729065002c0e188075005035403440f8000200729809220090a065045001040c0f940e50300c8006480203001003000d5014402c05104240d420354040240e240603100170100341001524511300b051070802034140d81480303180107841c01c20300c4604113070a6a60048080f42c80c0000350082c101450b040200c9600807083c00b80c24207610b07001b84100000c6a220402013880a00c0108508803412603e803000c6004184000c80d1025080011030081d4417148400c400d0148218003d06901079168596440712401c0b00150b50041240340961500306a138603640d200580b41050140d41200 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 757635206 1250 757633956 757633967
    0x8060409030210051f0b03071205010e0a1d070b0426100b060d1802030607030615031a0a06020d030e0607140d1104090e01050c16170705100f050610 65
    0x2d83c3c02080b60381d07520003d250b020005400341080942030f602105100d4072003130080c2065000303e44503404200091901001000305129903412911000c180c3c0303050b070311845d1290000e002198000e0700842c411183c01114140107124603030040c526009007558662906940c0038040c15110b00c070340c65001c004070300e440c078000b00816103000c10700401c00b000a20351041400510203028406004010500d803c810603400f60485089020b094001c900b1500142c1e1102801c07429206075009940c001010300018000003406074000b10800d640039908403000c040088003140364898554000343c0141d108298591141d5094030901a01600030009441a03250915010340100d4403c13050591159001605010080303590788942081074449043c0c0d580c1c0da41d14500034000e489481030792aa5035103400f002c01d01e01c00100d001c61310208101c0004020f5806c454450600d041d03920020b40107140001c110010002c0c03018442c21012006001c000180e1003608020341c0c044410003030071507000e04030842040c110290001e = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 757636456 1250 757635206 757635223
    0x203090f120a02060c010906021201170d090b0d0f09060506090106033b010515011706091305071a03040314030f040803150307080703061416030c051204050607080604090302 76
    0x16940103603036205c041000c40c010400101c010700034501c040381d40e0285003022007000d4101c03148540880046440354041c0c4d0344881c0e0138280f11300400c4080740100203141200f40039010418000d840001e0011441d819001078444a9408031000c035134070010800da9140c1480d0b00d80c050880c0c0e00e410440b480015010708840c04214041401c6140c00c08207800041240980200ea03042040e4000c0c0070b103081c4411241c5800c440015020301041d01d908070803003188045540c2c00d204142c01031030101107486003c2e070146660000f010681d26400f80300b40102e48440145000c50f2840011112650380303240c20308005000d0005464000ca004a04009210171880e003046050f03001500841e5403552600c801c00c0000188032114440360300341c0034840000910301004030701102120300072034042c080c0200c4150000000c040455599045003050045c05295a20a038002082600103042807031030680650044080010101c400300d03810382c022000c1106070b0707030b1200b141034001e0410b9409200404032540c1c046e489071900d = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 757637706 1250 757636456 757636459
    0xe0f0a020915040c0809010e0f10020a020705060414100804030e0f040e0d080406051b0406080903070f0f05070608070c02121e03190504030b07120f0501060203090f120a02 75
    0x241c001c100c100110401004035210010010003c5012401000d803200104881008841d4a400c800e551030000c042001090041240050512a101144c0c50b2009411108100046118000000c5495107800d4000d101038050401540354030241c0c4c100704044010040c0400c420010b0b103000b40400130350010300c1c00c1c1c40d0050403500d0001002086021400400c4080c030340e0001823262854021055400403003690055002d03030000e10596807090f091810868003521210b1041d1800c000400010b072040c03080030b40003141c04054916007e110b03110314410304803142080c1d84a40b01520a034040020420518004007442c0c00d00c1d0401c0d144c100340290009614070806406921000121140540c0500945002808041c040c0b640d140f50690090750320b41240d429500c0c280300e200d0720381c24040d02400a9a04581d405070106030246e450075422200140c00d109420721a40d1210791401c14417034a40103543c00b1303100c2c0303500468031138840703400b00608112210341c054091256011100d540240200700c91082540 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 757638956 1250 757637706 757637719
    0x180c0e0f091801051e0f040302060720011a0f0a3005030c060f0f010302060a300203100f0b250b16090e071e0e060c010903030e0f0a02 59
    0x240c1d80d16594964500304014081540b07440104040c0007032401d82145d803880084816682c90f581c0d400410f2204070190b030041c001d03134045000182081e10441200c0d5408180e21242e80f038004001c000c807400c0d81e84c0658481645040c2c2020a115420280c281e1a0000c008a070b1400c0918580401150a501c1008050140411004030316a608102c0c0360b0f0380740010341c4601169a2a040c4c400310701c1e1900c10984e405140a01e158000c50403916a0075026030590b500140114503015903d203066030742959041c041d00384441003041300005182d071030281c01c51100c1109405039030307403826451018549281d0b8108100a00321240244441001c080c1603d00440240403980104110302c05031403100b81621900600618000c000c000256400b4804050056201e466622030180c84a03114410808121341d1040042d94041000c544080c3c00504900702c0e0145052299003d400c0c0000300f8050341c4020080d5545a44070035052040582c58420900108580310141140620f180b0360907868032186c40007e407107002c = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 757640206 1250 757638956 757638961
    0x80105060d1401031505181b0d080d09050715091802040e190b01050a0e0f0a080a082205011704060b04020408011b030c2313180c0e0f09 60
    0x245a5209a00c00c440218030002d80e0760b075910f04401074074000c0d00c0c0344000908000100ba407480e14205418000302e880005000780398640716220560300845008107511a000604080211b1156030052034410700e1000045002e44d07890a14500c2e144150740039580360310000c02c289007030980c0001b11b1810f0713505c11242603059000c0784d01e9450103030155030007040020b012401440001c440e0440c46440b4000b03ca407042c02104404001920036002d4603421030081080703994203482c0f46c58a6410101070500082c00c03811000d4842425a140644d1540211120040060341c40d0941010501d0070140d081005814442c2c00d081100081c41c1c90007078440c1800000540f0017103000c1044980182e11b0342840030304210344035561004502d020303000000340c0070002038007d0a50f060a40c8a409013040c80c0d03066490310503800f01d243d040143c070a1382c1725004a02816091200b0020a07260606400c000d1070020100c141c90f121001041d01240c0107000700102707011280c54811503d80303840810005c145822500300c030495 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 757641456 1250 757640206 757640227
    0x30b0a0605030609072328090c050c07080c01020a201302072a2309040b0405101a01080402010309050f070932060303070609120f03050708010506 64
    0x6054681003070741c0c1030050380100080500c0002d020411255440d00001c091400c6a00701c03070ba0360400c2c50260307802c04030035040e00031001c48405a101005000e903c1a80f951595540d1900440e041984c281d8000303880000c001d040d500040200f207000c0d01e4040041d25284141900103903070b5001100005021070358080075090302003e040d80302c0c1c1110300050a51101d503405090814000d601c008412070754094483c00c066601d0340304ca4214541045562000300d505400c1c103a915044658000e080080740881600e00c41c82c54540d01152030040c1e1003110007010505040ca07100d41420760142641c4a00b0746805403510001c3c01480301c40c000e580d003e00b07004207141c8642c0012001b0700122200030f403d6201c0c0d071816105032031002842c1c00c221a1240410030810501c0d086100041d900512014103001d9030a80e05545410a01d04441d00507500404803460075410f0b560341c0058500607481034406007007080403010959045580d20400030007a1400300014508010b0103400c450040c000e242c00740e070021802d40d101 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 757642706 1250 757641456 757641461
    0x5120f100e09030a090e070e011d040e030301030605090a080a0f11030c100f1e020904020715060320180405011e0204050a0504051b0f16050a0b010e070504030b0a 71
    0x94070248281640c603103812030740680d50b40d028001943c0044e800c1c4800140480100d04441d0140e42955a00d0b00070300c1142e801116400038040c4561861603641c9100121542c8a02c10319401e40c4211001d10780b2076155050440c22114000c3c60142e03a034000a6a810000300c200080307600c01c40141c20044003140500000300c03000540c0212042d224880095041454580005e40055020300b00700d00703210b440380031103100d070540e11032100c40c00c888540240b06920803100d40e0040c200071440600014203000098450080d00c140c1c8004442400d07983d5a0240244004a010310748150180300d04010b05c2280d0002250110743c0804503003001802441c08181004420b4118661414003800010021200403006034029030180c80b42c0c0d4480d5460f070700b00081504103801894840d03407018000e9244164514100b40d1a40d011111000d520081088040001c511407011012200e001d080180fa1000c51454246082c43d0306070014424075007000308125200f90711800b120140ca9001221008a488056000d4007 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 757643956 1250 757642706 757642709
    0x3050702040c020c09181b040209040c080106031a1005090d080d060f121106030a20040e130503040b0a020a050109080a091a03043008100605120f10 65
    0x1401410000c4000e02d05034009202c00d41c044040311080710703d841d1000c0103000c05c411000001125044007103200844499001c0d12008010040c0025140035094030028080f5a4032100784004100544014081e6a5042c4100d8000d448405003a00c1007807180c1e400140e43e1078664050704100301300016000f190351601c040c0220a2580312030400e8840704d6100c10040030302014002d5001001180d000040d456030b11020500d10550400c10b41c0b0f00c1140300c00180f00140d030000381044821600c8907401c03000c482801c070030403a02c0802080401d07100d0b81003100c042a16400034000240d0b1203003500690f40030a60100c00c9800f00c070580728130265501c1d80c4410503401d040341040d001e40103500c1d080c0300b241072210380401044200583d95030f00c03081e581c440d0b0b1400d1a0104a5810000c01c04007480040d0025000722401d401481c41c04020800300c24840544100c10701c0c0308004c9400041d802e5041c41748121921600d00003600342c0b41001410640d1032046c2c0d0800701d000070109080700b001100400c011040150f188030 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 757645206 1250 757643956 757643959
    0x30809010c0605190b01051216020f1c2007140a0302130209040c09030515041505190b010221090607050a03030b031506010e0d06060b0a32031303050702 67
    0x8124540f14400589900c407a8200b400105e042104840c4c880d0321600449940455082154480d80c4038000c20440c011541c0084005511810300001c4078484100302c004200348140c900c10402005510b8001d1288411002e82404040c006001c41c0c0d00060108145081c3c8203e00da911800014103400202a07003445d90019410407000101801b0700b5400360010000e001c2c0548080c80119807010044400354a10300c80031b421600032400c4042e5100c22140015081030003882e401c0008a400c40303800d02160015603015141d010401401081c08803140502d415910090001e0800c0843d94004000c410600000702200f1600002e40280300da074500c000d40e420940c00c40d0071252030011070b140103001460380503103041c824490000c081c98001407c4c01c3d1300b40301e048180d6800010072004414000b008101031011229162112070218002030b007100a0200c035015980c0c3d40c0e01072203501e080004502d1544084201194941d103020424101420481c0e0708201d00b0507001c03c101d036081c08d00710740300e0141c2d10009 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 757646456 1250 757645206 757645211
    0x118020619180315061202060d050421020a020a080f0322090606050a0810150806031015050a0905010b030412030917040305010e0a051b0102070b0a02010c1103090307030809010c06 79
    0x2000340480c40514504e08128140100301480d2103020720030f40b040320800000c0d41b0142c10003140050f442c45401040d0010310500610440b8100c0c181149400001781c40c159006a01010300c2c40c0542c54500c080c40c1c01001494003400e0000e0300610101c0c0c8038031039005007910200c1d40c205a2012151096050001003212100801442d0f80b030303d400a04c01e070300800380440050031000c04034900704540c542d200c0456980c2c10941246042c00003054401000040045505000c1c00055145580e11400f4010b283d40050210504c101c0c240001c008421081d90001c071501464a8018091740800d44112900140c0251114001c0c1d080b250084010f40180c501c0144100245e0040b4400c0c052907101502c103507840703000240540540c2405460b941c015101d009000c40e488005c1c404409540c40d48074048031801032055030b41c09500c074816a103c0b580550f00e1840143c1d550303511079010944c0304420400d0f052204c1c0c0514580441d40000a55071035540c0005000c54000203600c414907805104503a200e00c1d4801b205 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 757647706 1250 757646456 757646459
    0xe0616050105070f02030c03040504050c0c0115080f0102071a1b0c010f060603090203072d0305030304020a0501090311040c17040f1106120a0504020604180b03011802061918 76
    0x80d029002c161665404200146504003489002005490480004a00560800785080b08210142402501950a0201c00c10100390200c1e0280124022200c201c80c48800b5a480c1c071003c0d41c5098164944404140d10502003040001c1549006c02820510340136083c04603140c1c200c1c0c0380c0c00c2d90354015010241090018500202d6101900b10940c050500d410070480700f552404190143d03038441000a5240d0010368060000090035600c1000f42520010f00d410300b030710410400020014690401d462603170001c820041149807240014015040030710301082a03614660300e00b0524008030b012a03100c1c80c1c0380d00d44464a035105540040311680448652505801c0c00d0505454200200c1402d403800070341440310310407d0410400300c03460104204881c1103035507190103410009003005001282d10110070400042c800280c22040100d51406140000700900144205821201c0380b1415501c41e1012040307803009661044142d81200c46001c40e41c20302c0018030b070011542804412110341c03152500820 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 757648956 1250 757647706 757647713
    0x1501031e06140d0206180105210403020c0126190c0e0a050a1a161e15110d0e010906140a150302010e06030702070506030c1e04150c03022a09160504060e0616 69
    0x9815001c4e034000d40a440206107200011030b28002c044d80030810085070043c0c203441c404c65080115503c441090710840362501d4000250060b52211c1c6041800140c03d00600042481c0000b0000002d110031135841d03203190710303184903e0804904103450040ca84404201060851076480704803500c25401504880e4005030002801c000c46607816050780c03180c503d43c1d1040c501504900c507d0828000404400341400d401c076414078058a001d09545c200b654070b403464940021003d019002c002c100c0d140100c0042d00d4008691011520105144051151071000c10030250360048001701400380c09072640c650701d585650b400d81c030b010100d92080307030864800002c200d10502c0316800307031504105082d14030214a12000c06000340e80035a0154408141c072840e801d242041c012281c050195103c0e00540c1c400c1e082d00c01464900302000c1c00c4030b040c0560098041d1203149000340d0684e82c00200d2410391001d424070b59030010010701179400380c4014801090071280446d0303070307000566003910ba80309142d03a44441c1524 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 757650206 1250 757648956 757649017
    0x6060d06150915030b031b01030f02030c03160c0201360b090a06260709080316060605100c02041505131b08010e1501031e06140d0206180105 62
    0x1c50645910020410300745060710178002c000d40004020020429201050507108141110041c5241410341e1400710141850450000c0c620440c40f0f1000a6183e1500380c0b07812200059069103030080000485540f0010b07031b005040c4da50003190b0f00070b2080d0040c0041c1e8840c0c401454034041e24000f000c903103070005850329000c8002d100d800015110303c6240c03603441600b916070012016011008149420101c11034824160700c2c0c03a40f01269280800d41e89079030307943d400d0456000d01720700c1c00403441003041042030004d5406020000c00b000d0300d122034000c12900004200c5080fa8000921840c4c54488014000904c24510b1024083c020903200030103419203000740040485280c609042c0c0201011001d1072401104040e0481d500d1002100700c07559440141c0311180820320900741415034941d80320b02d1ba2543c107564180001c01c440c200040d12030902d041c10358100b0f0f561b400c0a115820b80c004440050b101d4900381c2c3c48455800740845265008100180d800740210031100303400186905000400e2520030 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 757651456 1250 757650206 757650209
    0x60c090411070605041e1133090406240f051c0b03010b03030405060a05070507170a0b151e040f02030c070c2111030f0607051206040204030b06060d061509 68
    0x1d4082c5a030101031b50360155400040715802034041c0e81015104c5010f401c002e0050003c00d1840c4400915032840842d02c2c810f502e4080c1c00a910407c004298100181410300c02c22018201c8885442c400c2e1102004580308410180c806004110201c10890101402002079400208d16010000080e03c2e58030041c400170a14006281d02c69070a007404500c03241004012202070700c0c4080c00407072505050101c162410b50040100311498440c40340000340c0c2442d00c0440c054810843c0d0042c051821040c24003c03100800603007003074070b10384038240070210690302c15488a1000e0b0b085170701c3c0340052042000150041c080d00c4024003043c1e00010030040c3c003801e084000d082c030a1140c10f0703603820b50b40c8801601c4c024100345a038006100d252558080003103500c0d0404800c2a1000034200c80c4549180c00360941031074010380e2404041035010801c4440e141211480f0f580c008800e58045007400d10310303103482c1c400c48006040c2c02c1c00b41c540010500c510710300c1361f0050703806001c10102070b41403000c203c40d0052181a05 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 757652706 1250 757651456 757651463
    0x21602010513080607020a1b053d05090306060415051002010b120c01090b040e04060f020921150408030a0c020f1221042001020c12010608071205060c09041107060504 73
    0x6611024490b40c44c0f10750050300361a0003514105014045016984181e10300c410355852540100044200040d818ac0703600440c1c0125070745048d00d4442c0d42c1d05240c40d221000d008030388600c0c1031502d8085d5005000940d0000c41c1c4041b0350b44003010222950a034018010007038116040ba082181d510455100090b00d642d200800381e88000315984d440c1f18030741150103140141c80e403210751100410081030380c0340c0004101c6c11510800501c0c0008a2002600080240d41541039818460a0161280720140b0904100c070712410151182803500f0b0362080001e200080040000541d19484072901620801000703030196000011140d41e07038031010101106402c4030a44802800e6448400000c0c049403240a5004030780c8000300568103481e014a070160342240f00300b203d046116055034044aa9103405010b0036104130705000141c0c1e1418002c882d13080100981010740e0708541080031f8000541c00183e60f551005041420740d84903502c1030300040103082c1d585182c840003035011440005011455000314040ca21 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 757653956 1250 757652706 757652723
    0x3060801050f041a0118091509111005070803130311100222080c100e0406032003011b030510050402220f050f010c06090f0804090f021602010513080607020a 69
    0x880c048100d00c04c4500340940700700e020030340341c5140e0480240e400c40c00c1e09510408130b0342410040761182c0000c0718106e44040d5440507100d240c4000c0d6080400001404e84201d2030706a141050603110742a291001034008086003841e00d8108007858800d5840301071a642003020703075044144e40e1280f54040d401200a22000d03416541c00c11616902e403184c0c0c0c1d0100c0b03900c10040e1000c181c0007002c1060b10301c01010f0001c24404189075a1400d640c40348200006035121b0400148007100720340020300c252541204141c0641c1c501100605a0414400300d01c44840140c5030101d0355668031010395640c451b5a5101d00c0e0800c0c0042104054001070100405413000000409030149640c2d003031424048400d4400e00c0d808c4480e05c19810f403154498a016042c007405031002095100f8030307030345c3d0b070744003158102c4207603207810000c501484136070860302030861021020301c0b056044c06500300711216100c6801034001e05004000580c5c0f50940703640c0300741600401010064507030343d2a008001a4440783d00c210f0480e100c10 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 757655206 1250 757653956 757653983
    0xb03040501061d071d03011d010f061d07020c030d0504030b0f070504060e0d020d0311060a021305040b0d0f0308070908030414060c0f060c04030b010e190c03060801050f04 75
    0x280610700030224110311403510f002615140000c1d00d240c0e0303001d54812060f040c802c00b14140c40c0c50034050b0101d980c1004105220500080b0440d070300311051804203405c018101340b402c100c01c0114002d000e03003111b8408503003000d58490312016031500060a03440e54050180400d02d03840150080003400840340a42c1c00f64030030760b41c1d0505105207070000725503a0021032030500c81800350740d1040c0d40c18208034001400014480c03c99800082440848100460003d6149005070302504000e100050700984401b10070350400d04140041f221452286c040e05000b5556102d403010a5070301c1c0080c0c00318a80c4c000c58503220006c050f04000300b2032035048603040040b07150220b0001d0001c100004030f500f21003482c1042a8258480d1041142c5070b888114500c08bc2d01c5488034040f10b0000c288a0b10b03000301135403006907135500d1451a081100a41c164442e0840b01035010030094008000303440704007072030181c00c00002d400c8050142540100f48541207000d06d9803034401042030444161010314040c07030254400c0c29001 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 757656456 1250 757655206 757655219
    0x1051003110616111917010c0906120f020d02120604050912040e04020105130902040602070f08030304030f0513090501210224071505060a0603110a081e010b0304050106 74
    0x10f03c82d090012814499900f66240071658000318a80d0303a80d4000c0280103488055424440e400b20301d0b403ca01003084800790010700d400006d2041c0420903c6034141f801c402450444080d0004070000c601d0300c1c06c1615007182c40707070365821541121030310320309035000b10344480f00c1c2c5100c1e9900080480e820b41c0128a8a8003240c000280021004030301820940c006241a05103a1740390351003a4080c104a05004017440074540c480200070450016200e00000140c40d640340c110002e1401d0201da00c80c0c1100000702c6030501200c8400303c01c40f5485a0903080242d0a401010703c06c540f0740c410240440b20200c40e440021401c4100c50704900e0481c0d03400c9004408094646c1c00d016441002400d00a500548501402c02c100704044d40c2c0c080c03500041040d003802c04041e900d41041041540000c0b2090a5591081158a1800d1001c0350040c18039464104002e803c40144840b00703100303880850081c031822500042034a811181d108070741500c1248020803d5070f40f1031141e40c4907001902c00712141c1d402d005011501 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 757657706 1250 757656456 757656469
    0x219020f070f0b0906070c030218040606050a45060513060510080910050a0c11070621020408070834062a0b1b0c030a030c050c0105100311 61
    0xa0310310400b43c5030b160400f40c40130440c0d5a8010203088928070301d07070713040040540c0e142e500b640e8141c180100b401c2041d140c00e14049085511907000584200c0c0a03002c14061148103010b09143c9100001410b03c02040100d003d450f5440c6c2c112184aa204131160703007407101d403210381002c002c4407800e40d4040c1440c420007000200307403001c40c000d141d00080c444150315411441204003d80100b103400641e1014002c2d10f605600b0789800320307500c83d4425200c00100403d943d00200107090f08100b0005000400e05000d402440c0a4684a622030600d05407148400101c01641c1110010b2110404540d4070994544501b03454041c500c20102e8a064090351714107000c003038440603106d007032240d034490b000c2103050603400e17121414046075030154606481074800490219244450b08a409a0759032000c9251117080aa038180301c140c00803000038401e110703019100800006842d000341c082c4c10301050380030348200107c40c20700854100000642c2814144111400b200100798141c84c05a02c918030070780f802c8000d0104 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 757658956 1250 757657706 757657709
    0xf0a06240b0f030c120a02090111190605180604060c111216030c050a11100504120f24230f04110a05060c0303150102070305030712030219020f070f 65
    0x1e0800b000030340d8a0030030b820000c580c8000010300c190300300805606405078400088072280c035030a90015001e40d40c0c2d0703080340d84480307505a1500204082030042c00034085201c440f17400103082580384d801080f0301d603d5942c1c000b082c070b42170442104c80601c0e080c02c200e00a812201400d8001c200040d14003540c9550220b49002000900a86207150a17400c6009507101d81006200b60b040103d00b103602400542e06000c03410125005040080c0110200b004004800300b1010341c000c10321800700402c0000302d0040300600212030308038541c0d81e5050714a040c041010201c07031034082c55601070302c020700c0d28901c3ca07130344a9405001d41000d00d002c00b00408055614200007034490441c044841c80000300020000b81c00d007070341c0d81c501800000e682951380380821902d40040e28045031503040030081100c43c17419081e0004103208244002d01c2040d1075078130703110f45a200d4004050400340391540c0c0c40c80054042d4044031200500d440d0040d004101d65a402526508030f0569141e0754060244005400c0b03042c030b00a0380 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 757660206 1250 757658956 757658969
    0x11031b030708040b0a060906030b04032d05074e120c0e190501120504080f13120c09050a050c0418060509040f020909030a020303180f0a0624 62
    0x4410f0f85464680c10650302004201c48500d98842c05c01280c0c02901d03025a4004600c03440f0f0080300703030400703140250400600e44146c40071584400d04103100c51608100202c0202d80c1418000c2d030340c904c0c90030040e54a0000c0e042005010301c40b040c01110a49480f84071901e0007440a140012070102110200305103a40724074043e0001740c65580d200134003604e50b400703101c0007115402d1009031084070308045003816600c01456801c002c0381d11740c1040107503040440c0107180c000340c44041145142550b20100c00c1c2c05940c2c90b0181918020802d004201c0f800d40152001d0320a05028041c030780c400d4900b401d0462602e01030b510f0017605210100740c0c0035001d405140d0160000c0c003012400c1c42d0401c0740c80340b0340c000440600102c2ca500d40c00c0004103601c0b0014501c3c090f42c000c003403c60069a040c0107100f070000c0c010b41010865030040180300d04099001c000d5035000900340303081280402d018042071303140c131006004102090045240003000c0000c00e41c00506c03203801007c0261110040740208003020140c41c032466 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 757661456 1250 757660206 757660217
    0x10b1b011509050720011d0c09010902130b04030f110d0201080103140703060e07061e0207030807060e030d09050c100e04020307030e06010f060e060301261011031b0307 74
    0xd1040000c0340d000f00380d10030144e01c0d084104401d81c1400321a240d1005070300581907551550304180008a003144640882c001200a04040108201050340da150501c00c07480801d41c0030034003401040b8075030220001004030f1140c0303a80302c981700c0c142001c43e460f4056040300c80601000008000d0700b080c01050b12899016100c0000b1071f8a590ac40f0405d0201e81081d030b580038000c1070350210004080b440740d42101000440185807140c1007940262030b2108010300080e8100a4410307003811943e0000f5030b8010340394000101c40d140d20451810f440580607034441407032180400714400306001c150340c0c0700b030104500aa00711412014460148480208505000700000f021401074140381e040540007180c2000c0e0900d000904110605100d508001007a0840b42105408440400050781c0c42910000112800c8800500d154507003412181c40e50008550030486800500c0780f14030b0307803009103e01c62040c0c4004405006c1c00001d00803041080d0b208179003624a11b651000c2c00c00210f6444c07000d40b4414185610340 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 757662706 1250 757661456 757661459
    0x40527010e0f040f24140703060323120f03040c140a0303053007120213140d0206041404050a11070209100f06030207060b240918010b1b0115 62
    0x10121403064090094a0401c40441c045108840d9007001700c04102407600300050f000f110a04d400f0f003502c000b90800c1e08044c1850000c4c80030580ca103091002d14000d10700034855100500f0702d03003801c0ae096a62844014400800c0b12000c40201ca0010f5209078894038a49007400e4030344104642902c0042031890304001001010310000340150002c114110b00798002140c5070388980c0c02a0301d0120a03894010140c20040c0500c0101074002e800300a84641410f41035043c40018240704806d100144030b0140615100c070086401515007842c80090650040c0c0b101b991151203980c2c4070041208000e041780107501c0d010020711440024400c4102c400d0344240050711300200d54081000320a0013038000040b07035a041c400040c1c03a00d4084441001000b50340c402507152041400d2030000c03a030000ca5094020100600781042142c05c0c1c0d0040b4020310440c0c0302c4142c41c3c05102e0007154400e0b018000210505010b1000850640710710030182018450009580184110f16002a4240c40001c4d80410f07455408040 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 757663956 1250 757662706 757662713
    0x90c111c0c11090403050a021203060108060d080c0105010e061203070b040f1a0708040606140a15091208040e060303210406140a090c060f05041a040527010e0f04 71
    0x1000d8050b000d01c8110755071a45400025000310b1042d501140403500014440c0c000c2c60701400500803221500422600b1483e1040000c1d00c2e5820082c16940f0610150443d40100030161042d1544115543d000f0050741da19100b04a4243e04152519845000050107030441600000100c80d440e42d4050b2842d00707203449503a521070b130303c1c0c0c4124030072226078601100b510700013640820014480d007107960f580c8060741004d040100c00c9a149801c90304914000903c02d0341c10b921407604420444e4580c40c28052030307485000d0110303206080d54000320088010081c030070307040c46005005001522a20301c1e1254042d11200e04059403441807800554141502401106408441207852030f402030040002140040b4074014050582d81d04a4a42c071919585070200e50070b0201040844000d0900707814015021134051101502c00e004607c1611001c802080625110384081c1d01620000c0801030007070301140c58180c40c2080c071003031060b207207103840428080005444d5001c1c104e500d0190b052405211900d8940d600e = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 757665206 1250 757663956 757663967
    0x105030f0d0e060c0106030f030909060b0c1b01050409060e04020a090c090b091309140c01051614160321020a0201051603030b120c130203040b0f070908030301090c111c 74
    0x80e04c0b9441e5503642e0001000c5804040d560036118420380d6080922030800c074081044400c00d4122003000b5009000e072641101c400145451540956066560600304000040314603220700d03041480f80c0c9003000c00c0081da482800314441d0040d0b100302e0f0385a003201e460750340f44030488841035403c00000d00105000c10405200c60028100c541c0c001d00944e25800b100041101a240c02c840b046070700b40d06102480d030b9100400d021110b040942444c04915103852011003224100c90b140025140070350429010500503400c110014200b848400c2c0d020201d5900d0801d81d69220f045c52400281c0d5075800c8030a13074000d00c00700b4640e0445505840321030600f00c00070f2085408140d4420120145551000b214046030742ea4800c441705600c03404024080c01c031180e41806208042902c080c80101c0c018403e000019046003a030b41d80c080c3c41c0e038a8100041c1c0e110a81100c00c0e5040342d001c2080ca02000001141000858004904070034260300c1d406194040483d840d0303a40c069120070b0107003d01403038540c03140700c0b80720b00c = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 757666456 1250 757665206 757665217
    0x21e1509010908180f0103090b0718050307060807020f07030210030f0e121b06060d0206072603180a120e0f0604080a050d050309150613050f0105030f0d0e06 69
    0x90002424820340d0380d8004141d40807030310610704c2d00c4540340640c90038900010025000f007020310742805100000d0751041c0c003680c8064a00d800b0b10a00581030302604610303801c50802420002d0440e07603999584ca2000e001c6000540d0403070011b0050895003120948002022012240d001c0d2413140c1c4102c0f1070b07400703c0081244441140100740c95072100e1600150401024550702403821415a03107000650300042200c1120328092083e400850030050140da81c0b41200401d2074050320516500c82261514150000326142c2c0e03480380352407030b202401c101e125901c0698452910402c0083c0e15003c02c102c020790303500b0548001444400b000c2240c072070f0b0303d108210110b03010f207000d0903440c2c144184000045454002d5048102c596000c0c0307800303d003441820080b074080810b690905515608010702c689445155910350500c07000b840c000802c0464a503502c00c1d0740b4890f203034681000b5078105640215408242032040302d10911885101c0b0211a2012488200c107a050f03498a4840010036801c0c008141c000 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 757667706 1250 757666456 757666471
    0xe1c080f090405040c080d020d0e1e0607030509131811030c060d14060f130c12060e1009150603091e03020721080306010503280606021e15 61
    0x207010a2009841d2405100e002e580b1079181c000c509400c1c8034001e031601540c0080d180856120000916401e500010500a10641a507810300f00d6000102c0301c460f00e103400d88040d9004000043d408040c994041d0280080303020807952103e9410f60b8612803029951070200104246d00715000440000741490a21049031001a0035112400c19510019003550014021040c000b500c924016000092030101141c2c0074800311501e0401580d540040307031402886074091020300380c0c0c0700c01c0c54080038020010300c1d112000502051004a0302c6d0159186032050a54080c0c0a07902c860310f0215201d2040e0007419405071034041100302081c903084086028000088040d515402c0c0000e07201c424280101d4142122400313030b0002e1600a16200e4500380a5086802c0411083c0e01542e030880028100f0046130341224091801542b079449124070b4100204100401180d603000300c401d00809603c00750004800c4884a03002d8a4150368500e2414807031108154441c0120f400c801c0d40840602c0340c0200c45500300a0 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 757668956 1250 757667706 757667737
    0x70c0902090d0606090903020c030601060203040b031009020a0c05012009041d011107030f0e030726010c0809161404090512070303142d07021515010e1c08 68
    0x120b9803503400880b2116003008605581306c200082c103058040180c5820075070244c0040c00036600d0140000e40300d0143e40910718031454000301140e070200c0c030051201c002d4069880d08558a0182c20800351203440d18400890f03640d4240b07000403030380d021410550f2072024442c068031031800330b40c00304110040c01c04404250003103601020601d20803509100701c2140d01d4506240960311000d0b03080140180101240346010017401003084a00c1362000300c2c51100311100d00300900d40e660b20949009071101116420046198030301180785501603800100f16006103403050039160031001184c0400b6524509000e880304035106c0c015000c44504003540147e21040c091030590b0070070303480c0b000080c049900021003a0700003a20b60001505507a444085643c000300046020f1035500c0400c8e9403c0c2030070f64940e121401000c41c1e0700020303109500a10100250308088403550b5102d103450640d84410703d40da46d00741390010710300350010511030515070300d500b60980814881c680400c04517a10385245034400d881e80c0c1f0322602d = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 757670206 1250 757668956 757668979
    0x310303050c07030f151116030f03091a070912020f0f01030207020603040b0906071b0b1f0e0a06050f18190504030f02010e0106050f120703300203070c090209 69
    0x2c018544201c02d90784500380c003400617500402900c0076101904044000a0020400c00c1500600c0a02c0c40c00940e0b8103007040c1401400c9984194002c2160703c80107071200ca00b5459440c000000713018070a202e480d0540341e090040752503854812080c80c0c201d400a41100c144070002c24186001681106003101c145400742c0762540c01d501243c4180c10507a002c0b10070070092414001860b04c14800c44c5d41c05a801d140c040300c0342c8022101010080503484014124000c85c001107603a031111144081000c0301c805c4003900446507a26000842c0e241c044980609180c60058042142e1400f41c0c10403940000041c2a000c10220541c00402004030183c07500b240700c4d100480d042e88840c0d080c003440d48214000e480e20aa00c2a458001070f01f910820100d020301079141890500143d900e51212407280c8a003540d0801c503c89860491074a0600e56420191031021a05030366070107010300085001201c2000d041690b1640140c40007a41c0c0ca000300c51009207a0200160280240d040e2603010782000c0300b00a180800c5032 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 757671456 1250 757670206 757670213
    0x50d061b05070c0b070b041b030b13110a031a0a06030c0e0a0c0c0209070c15060906050109231e1306060306080312010614120c310303050c0703 63
    0x804619500404a080842d92205205030038401c1c1d0002c1a440b0103943c03401c50640c1e600c99403100c0c020303c0141001d4400c0c0e20303680c240035424010b030060355105244401f10700305110310350050aa118801ca8040c10101d80244040c1484420707001265840a000c022413a05540c1c01103602c2002405140b02650700e80000001c0307408104001d000788802613551925091800804043d1105c8003030000c1400b90030086680183c0f00c400b030035130b44081c50386814241c4560718074040c42110340d400040c2d0340403801c02001240c1e01420364422421920700740c88030351025588070605516084003400f4900301c04200a40c1144900701141c0340e0a0071040c41040b001102504d80001d01340d0108c1069502072107656400503c0020742510540c0050080710f4001d50800c180302040240700501405550100082a141409240d2810050b0742001420b01480c19041c500f0700c6001565400030710140000740008040b40004c0480c004e405800c2000400107018000d00b1030b10199072641c00082e00c940d440c8150340000010 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 757672706 1250 757671456 757671491
    0xf051c12260103030f0c0f0b070c060501082d0304030b0408040506120609070203070b19020720130501030f171b030403050c0a0605031906150302091305090304050d06 73
    0x30010740d40c1c585989075040d8140204402ea0052820007442914280c000214000a61000400f80c0c0540410240d40d0b0704a8215000f500e440c0c001030401d81007100200d40a040800c42895070b10402c20080600200c080000c0d444185520b100d9415400821081c00483c030005078881c1c0c06805400224900365031400803458990024a290712080450024001c0918004188039007000081c0700039400c2492503200c1100c000c00140801c6c03188044105644081201501a2103145030040020b100100e002008170880880e4004418806c60303115401d0b00c6a401c06102c1c59050701c1d0050308000c0d01c110107039640507201d580d9003045604040140244091074a508954081042c2c00034084d43d00d480c99460010311301900424107a01c11106080c040c0171480d8014141e907400414035880d03828040401080400405241d048a060b6403440c14000c1c0055802d40c0003001241c1e0141e13002080245881c055400b02d92090714845041d8204010400440c6080c04c40b40501d1402107800150100345580513000c1c = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 757673956 1250 757672706 757672757
    0x210111030c190e130f2705010b0105030c03130201020c060a021b060309120f07080a0305070e040504021e0a080703050a05070f060e060a030e060a060f051c12 69
    0x1814001031102e81c815022203640c034a0650600300308a60f0412040020000800000005030706a502c550b2080826a80c2d005045858180020351a9a80c2c0c1e50003200041050104203540725030900d4080c400c40c3d4030035004c881c80b030300d541d03009241551110720240040d0a450301042c0e04501c11040e61422503030320840103003a505090340083c88241e00500d0607159032a58001414881c00040c01000001d40c4080346444004500815880c0c0d40c0924048403140c9001c0d100001e040c01d440414030009454042d440301d07010b194641c44414403007450303608204c241c4504a400a42101c05411683c511170a80c101c20180d0150003020150b4481e10742205601c0d0132000d41c0166469400139581e03506021080c05060064980380d003031040c40b01d00b00f4801a0417402d00344040c0340900c07000119038041d2031007030313200c01c0003191120162a220704008442d40301520582c0662500c1c5101c2010008440ca013008903509440218a0096641c4078580c603401c120751b4a4204d140c007442116281800103407428841001d = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 757675206 1250 757673956 757673971
    0x9092f0309071406090f0315190b030a030c06021b01020d051501050414091308160203070504020a120906090203030d0903030524120c120f15040221011103 68
    0x1500c030300e07081c03091910300002580103041c10040708800e26003035121081102c00c002ca0680d0594281e020050200e45000f65082d440f9882c1102c1c8030600617080009104aa282d808520052040c480e1002c00c0603107034514020020040703545175500c900003130225000b800c0000900e41c1030f22701e103410550001d42640d0094800322030351a80c4108100008005c4072a200c40703000c080c6419400c00c0c0c208498041c00320040342d406880303415440005404204d0a0314112401ca0f440400c4030341b00d82102003d0350b22080e40c00000c0348070303002d50100419942002e00c20303101540e07030690700e80c064254542c0c0a031000b0007442c10300751000b40e1122100b00250300c0c2040242030034000c0c09070000300c08606040040c01c80d20302828144100d10400300e0381302031a0080c0504c02c00c1000c21505280403808402c0c200e480e2124040e100394011884ca803401a07240d80100f04403a954070b40f030042d10002c00c2402c090443c05141203034002d60015030f40c10a172460690021b10000041c1c4070b83c0c00055a60f1115003084129002192800c = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 757676456 1250 757675206 757675301
    0xa0303110f04030312150b03010e04020f0406030b0f011e0501030510150f1115040b06030a140a0203061806010b0a09094b20030a0e1b010909 62
    0x20a402c0c81e9407041e0004121500c3c903000c2001d00f440e4000f0348620040c44ac050a503070090000c1005e540c0c0c1c4e40c191169402006000300040341e0360380352038042ca10b011258074030503021000000414441881c5a404050354401c0380c2c5645500380741c01940240800750682c484441e5514010031042d40003003146180348203070385072414200c40c601002448021200c900201da07030807041704940b039403000c003040750b0b001644641410503550752400171a1078502c5500380070301880d02101e850141034201003034014900b4001d806442e80d9036a07101180302e0100290040340c0075070740214010010b44100001a0860520b20300e85059490381d07074102c85041c0c1c1c04040f440c401000c14041142d42d003103008115415902008c00560b41e4800911111706600400382c9a0364000503200c00000064075030450000090104280d80d0603180c0c2000552a0005e00d030861901c1114403030074015018a8410500501960505030360380204c4504150307050b80504800a0341a40301141c110741300000070003c10f804003003010042c510 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 757677706 1250 757676456 757676477
    0x19030917070e07110d211104080d09030c0506031003050102131401030c080a050a1e0c02070e041203111204110a050f0a032907030203060102011d0a0303110f040303 72
    0x2c0100c1e90401900c0c09092120303c0303021403250040800e126040d2035850401180003809440c0514200d03640c861102c4005281503169500560b0103400381042d2180e00d0211101101c007001c090b0380807400b600004e081440c1407a0b04004504c2e11030300560b0300805000c4030a194961b00d5071481d00b6a04003280d000691000c5500034032040002d0300150b0008002480c003802110000304010381032820141c04068119110000a200421395401040d008904502c0185a85142c130045c24010310903000000d006000b52000040e204c03410f00400d03401035400607005080700e00b441e1001e4008214005158540304c3c000e03c4005004000030001e68860b90161210f6100403040e00304002400010341c11441c0304402a04011205482c0c507492241602c0d40241ea580042d5074110940000709040f0028400605d0044100712076a44e06401540c0625800e03002030241c2e1418400c8001d44643c02d01c05907100340e001050f208003081c400e402c03882d1200c1d00d8145c40e514002ca008030306480360f80150016804120200c11 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 757678956 1250 757677706 757677719
    0xd0206041703041a0a0204051203090a09060b0a0e0301090b040530070609150203133305180f030423060f0a05040b0412020108090a051903091707 64
    0x10701014808480ca1514a1450240e075407160200c14118480d040b0302c51480040d6071103900380c0c1102d0103440f0040503c0300c20103800008994030382c070010841c0e010701e260203800074844480780512401c0c0d40100842c2c034200311440d0800c40c0c80494032041541c2c0b640d21101884081001640300754080c5003e9000352140e1a07000103180500369440d103400d4401040c08140d07000103030340c5c0404d5a510640c03041020078044e81904103c50030103482c40101003082c0c0f00105000c0b940c0d220000244809214148a00303000030741102d6039030640311503003520304000348141351000d6848959001c246c1c070601d006902261002c4120b4614608101c2443c041849c0c1e10014084c04900c0d84210300d00101e100c02c100a04442c40e1681c00720f2254003500008505040d00420301c4200180600c00f40c03006404005038441d1a0340c0e503413401c1d8a004100800c01c0c0c1c00309064030f02148008201007800601c00d508200104040903885c482c450740f00010003401d40401280500c045003c0d40861000302000d2090001020510f05080 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 757680206 1250 757678956 757678973
    0x1e03070314040b0105010c1a010e07110316081b010e030d0b040603050d140c2406060702010e060d140c04050108160f080a0603050f070f1a03180f0d020604 68
    0x240c40000701c03010581004001011030305240e054820078649280010200c3c5040c9090450f40740e209002e4070882400070510801e030b552110322504656503590b0801c80f080100503120720a036185031000202c4d440002010544030002421402d5120111404040850382c201e401c48a450108000c150030004149500c08114000e101e03824108807030401500e4510b03030354580d841010003621028800c01820801d13074001d00000740e5141d80c1c034480542d00103401c41004418044104010161003900c3c1c94007103105400d18100f07607115198180c50b80b0414a400351304110303058208400c1420701c00d4480000c200355000810603140109410468640c41d10308000000d03010043c000d11040c40d00c2c3d2074080c80c013034840d41310982109a903403a00b407540e0f040e01d03800110005080303e600081c00500c510000b00b22000c03400241d540880f034580d00b403006a20384810000c80007414426115084034000c0c0049403c0f0080c14030300c0d90503900b25500721908401010b190500b40305045e01d00c50b015800c6002004207110018 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 757681456 1250 757680206 757680221
    0xe09070f09060503030d0b010504030b01080f0d090627050301111812060403080709030f080d06090509030d0f06170a03021002030c030103030e0a08071502010b0f06071203021e030703 80
    0x24402d031414240400d580780034140a441c1d285803542d5403000c09034095012a005035802c4642c4418540c0c41e4500e0f507a685da9031400f042803038071032400240c40d40d6106080f000c042d10400d80e11203843c1c403041c88244042000e100000d5900541064000505a03400d2003000240507500c014252541d40d8600d51400c2c1d90004034100740110030310803040d11043c90128800340d2060303041c00e1540541d102e004040381c100c3d000740c00c0100891400510501488038080c007034010f840c8418002d2201541368000402582c0f4262420601907005102000440d10550085800080030f03720000d00745a0300c0319050001810340b04019016001825400107042e030510089011042c41032066145003030a054080e0988030500c4003508001d912030b01c8250a56402e4034081c000c060b01000c07180c0c246d850b5070043c0d141004100400005d0740c41d180f04e60340c00b401e01060004221400070585410300700c5584400f41c940644c01040020103908004914131a004490078440d850120101b07182c4901c4c00c0702000c3c0444402 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 757682706 1250 757681456 757681469
    0xb0c0318101a030606090403120b0a03080c0c0d02210f162102010c02060a0314040b18120403120908010f0504110d021005181206040c0605210705040e09070f 69
    0x15010030117651540d058142d0403035418034040c40215100e20351140100441c800302580f01030146c1000082c046aa4041c1c11510001e00503100190807400803c20b01020203003000303400030305049102c10000481400788102610070800d44d101c14041c070700d00c0c3e8107210150303200c0070500c030301c0150502c242d441d001d4000100f50180740c031503544c00080d500041c081c0c406a40000340708a500240400d100c6102e504041d40708048000e60740201d0405182002101c0b80c1101c80540718042959101441500001d140140320350850031035160a0450300c0e51800b11681802640510030780c07050000f00000d092144284000007041c0000341070820b407070208c144112000740244a0078401c03c4c1c06025984040000e001c0b00d45508211382d94071081041085014040140940e02c640100984c43d580f08021902d184910311400000401a840d00700c1541c840c060500840ea030b6880e500292008510001507160704030142d8101142056034684400d0b003609004c4413102841c5d000b45030200424040389007484081c180 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 757683956 1250 757682706 757682713
    0x2061605040b0906160b09011a014508010b0607120305060103060b0d14010e090a140c090a0c0e01030b01231201080f060901090b0c0318101a03 63
    0x418280050080c003903070003200341e02e07107000880d0009951107108503107901c0040403070b07000c0850040c00c090724103e108558007100c1d542800044100440260391001d903d9005031a0340e081005440324044804004040c40d050020148004160140b42d4980500391880f89840100e00e40d82402003090a41e40350034662801501c09006010002d040c1e14440d0aa031111031400250640d59000100c0c0a040c060340440c0d6902000111901c0801640c0c208000488001c0c802c0c43d5180d90303604021086520845010390a5003141a0400008030300070340b551805403d11044a03030210780d200002e41c11000c10350b1401859903944884010140c0c203d101c04801c03403001d082c1040390034540b000103020582c82c000000c4040c0c0002080921700510348090300c0c0f001c4142c1444840d5580c440c04142c0c0e58008141501d40309201c2c0c440014a51b40050181c482c0150f4094640d2403a40c50384500c00040b504043c0151001c906080c07020100444200034403001c072100b0b50000700c3c0c10181c50300425081600959030380e02942 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 757685206 1250 757683956 757683991
    0x4050d0506160311070b0405010b090a0c1404030f201009060e0909030322050f030a08010906050a09050702190c051215150316150318030e010e040f15060206 69
    0x41d504c4140c800654200e0480d601075912444d003a801800b24a5074164460002810320413005110340c40003050303090715116507102c906c9594030300c1c0180c0500d22005045020018650300040d200038182071040710b95507100c020071600f40000494040080d0490300000750301e02c000b0030a00b40c0c80407140c01c02d180241d50101c003909003080b203540c492000908a413040b401a8104455404080c001c2d5841c05030088280c40f10000c00001c031729101c0e0301201921000965520011410612078071440c000c03503100805a003d00ca10f4000e010001d050010008015401004440103e9034400c0b08003000442c400c403a5400d4031270515081060050501c41440382d1640400c40b070f401001d0308100100c3c7c2000c1c113034061000400b50340c0c000a00d081325040100b0942c60180d0000520350720348224400d645001d5840c18042280c2140c82c0c00244014400054006240e80c61584c501b540a406000c0c5400300140010800c50079000100c015218030b0b102a8003000b4a00c5820483c6680c14091290400c0b4026481076618 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 757686456 1250 757685206 757685231
    0x309021813061b0c1e0f06090b06010f0203070209101d010f0b0c0703060e03040503030a03020c0607031b120b15091002010507021c050d1103090d0302090a1a04050d05061603 76
    0x5503140c00504400300c3d844900c229030744c2245180140da40c4800c00341c543e80c086c0d1400708040e10b020a01110160b00c9480071a07d03079801505000440c0007203600950500c180c0780c00b00b20a030b880107009880003150001c00814203504445590000394809180c3c003261f54074004c0719a01c503403260392000c188544140940980404085101d4003180c3d0000340200311840d0a100541c01c40c030860b403140c1d0345440b00080e140d0f107182d016006003100020b21400d07140c0039501c1e51010390607101c60303034038000c1240604100c2440440c040c2d200545464200c2500158405800c0c01142d80480c0e07014840b4100e80001c5019041864458000c200100c100d2009100a007803102c400b035550504e14000541000f00614404140ca01c9074042e00c4040302d0400041c0440750301e0803800410b40d4070a4940040500a84251840d074600038001c40343e01c01e00140003459840d18129000242e2190125800d240150401000465070350721203d04102c513024038003400d214105252035010007a403c049103403e1604110307900410 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 757687706 1250 757686456 757686467
    0x604030303091a19020c0c04051003030206060603060d060c03061a1215030c010507151b1e0e010507031b060b1c0b011401020307050d02031c02040509070309021813061b 74
    0x2244c41820000da143d00500070454208048035000c143c0182c40d04e0100090200c08102540880b8065002d42c0c2e1551110400d0040340d00c81124520f07041203180344190001100341d0310903508580a031400203031803900c0b0582e0407174030500d07545007060814004c18401d0f07244019509494000f406122400300c086d8801700801e4592140c1310400b0706211000c1160418012041e94245041c4441070b000c000d508841b960104c502c102c0500024001108000b01445035100b62100c0707001c0b8482501c844585582000044996070702201045003088142e0089007140c400345950910010f00c25500400c00090316401c0c4440c3c01e1028442010110468950601040c1290903c034107441401806900100c080700060345903200e5000010b02c60300c100011700518a50110180522056010710410b4020f01c200000090303005901a081c2d01c0140400442c0b03085009500110000784060940d000000b428440091b201e141158448103210440c0700d110204015449200710341301503a42c02a0841c200028000d05 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 757688956 1250 757687706 757687741
    0x405070509041505010312090e0712180f080d05100b07061503050321070207051e0a1503060503070509191e02160b01080d02060c0a09050604030303091a 67
    0x2146880c01140074444885403c0b211001c0c011810701c00c55070740345400c3d2402100c0f0004040001c00d141c101003840c9545900e42401151942d54144c51403484140301da00500c40b54442e4200d01d002454180b002404200c4900919801006810f84900d055001d20044d102e005000c654901d9605c1c0c003c2c090801100c0a440d003098000308000381a4449072900096400c0a4001500c244004540e95a002919403034070200f952022460381010340710303c8003da0b511032160041c658400b0441c4140418060017500d000c10b0542d0003810b1a0b8440d554031000382406003150510320001e501c80000344400e0a04001420040900351011241031600c2001c01c1c454403103450340c0c0c000e49500c1d0081000c0c440c417840d065950034444001d00310b58841400143c4c0310646000c0700101c0789002d1500000508402c0030031241340c0d1091680140050340e03106940b1070700c694007080c404810310020500218040c1c8070030020700081d503c40d4900041d00c82075410442c0c402c072850b1545101e40d5010f04100515500041da400c034 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 757690206 1250 757688956 757688959
    0x4030b0408030c04050a0305030306010207230603060d0804060c030f0f1d0411040603090b0105150717040f06080916081c02070509130b070309210e0307030311070e04050705 76
    0x54580c0c86a0035a140c1900c42c603171280d903004401800200078003001100031402140d00740c085898a0b96540141c0c168003442c542030000b9072203806103109282c1004401907500c034100034030201c5e142056980e585820b40280e0081c0c000a002c44484504240d001034941441c0407160601290007004803030300621040c90202c20b5219403007800000365080c2c03500d80040344484540301d1801d8489803556001401440da08174196000060310700001782e6410300441ca0402c807007080c4801032505506848890040c64900e81d8042c94140c20000022200d140002c51310140005544002e19424101e051030300d0994600054044030b028141c040214000c0041c002410600002c85155100c0b107410703082e07050100d030350f000c41d80001e1102c041060b020582104668221300c51441c501c42511403480403001c4606882c1e004062450f21010b0f030b0341c001c8842c0780c8034800400070300d0300c0714001e00710101090600340c056200303e02040c542840c2440381e600a100000240611864056032403802c0e8542c41d5503840c1c54803480d13 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 757691456 1250 757690206 757690223
    0x21b1c030512090c040f020906040b03180106090212092b1808100c09030f080d0f0c02010c230d15230f040903052a1204091104030b04 59
    0x41003014018029210054102c100c1007450303107070040d6100c0d207440341960000d108625040c05507140036a5482920443c5030042e01203401c0500301001c1103035551026100c0c010b01d10170503421040f041800d001e00e0000c2e2160403805600c0c0c09400e02e0b1180c885102509800c1e054100681159410340030403040c018044007a81d51800701001e040054502d589151421590100403a001080d01c40001070841d0314804d0201c4200200660020202c94101c828080200101c407140701e02d0300406c441001400346500c0110b40012020314480d5002c007160244c6041c0300150b5114108100c0c0713160401a2003e0b0032041549010706d00c2442040010039209100d04078190030754503482604180f183d40380800107031010048484001c001c822480103d0320900f81000d00c90003d175101a100d0b401c1501402c012280c0c0b50b11405c0c1130804488005c000b41e03d24440c812000f20f00c007900e9450012040100d0200e41680e4441c4030b039224205410001a599600020064803104010400004040700143c50307005802111390b = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 757692706 1250 757691456 757691509
    0x10339030f020703020f19081e040b07030c020a090513021917060f070e010e010528031d0102030c03070f140304031d0f03030405010e0628021b 63
    0xa03401894994224441140701160000c01c1540000e511404602120300702ea4814150761741425044500107001041d03048103101d0a04050403001c951a01001a07183e09401c0645842514105400164003640041d04140c141015410181c4c1188040c158004080c0058034003001c0d1070301502d548441c02405520445002d522441c100c80d0882d003d4079032000751a806240c051002d40d66403c01303803100320b81400040080ba076107a0149080c2c5099000c1030312480100c40d1203030300650b410341141850140c41140c0c5c2c80200306281c4102015041c00042d51400103605281202c4111004000303903a0103100e80c410818044c0d0b402c0568152980186c00d403400a54201c0800402c5903480b4031003034070707001882000c400e203c2050382003d44000c1070f40b0340c031502505a10561007001084122100c800746c2503001044144403551161007860058000130300350915003a051440c0e0516003000306018000b00c06414084821aa070610006d449102000300030f004142111001640d4111207900744400034031507c41 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 757693956 1250 757692706 757692821
    0x6070309050a090509060906010326120106030501180e060f06030a0506270d091e0e0a0b090619141c0b070f17040b131403090103 57
    0x521402034800075201282e829640d840c18000f404040e180d01c1c1d410700464000415800e0002070b071904982c0c0214410010320195100001095608000b00c03041d40f10801402d00c1e07182c00014594024036446e03500103034941c90300c0582110040c4200c20341102c02d042440307010000700d0020380c0a8114030300020701031242e00e402000034070740240040d00400c24040c0508010382c0e1034100b24029500681901c907282d529003c441742d039480f20041e800e408003059228038244a200280c46c2041c584c1c030301440b00900303019100c13480366141d44000c0ba040c0c0012902c0c0d450707841650030000d801d0f83d045002924111310a80680c450244662154000c0007601300c1d846103545090381e99499075008401c0880d0354120400c8071402d2407180c0302e02c101d84640c0800c41d01000e64061901c205500b50210000000018860f2110303640d140361200c000c1e041c000c810100c0c0d80c0b90804214410b41140f6004000d074011031340d034103103400054181e440141000080300c0d007102e045202d1b1950124202094203200d2240c0e96032032480303203 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 757695206 1250 757693956 757693967
    0x70b040806150427030801051518031e06100b0906030a0b01090306050406021b06061806030c0604151d1c02150c0d0e0d0f021203041212180f05060703 66
    0x14809207050002503c4c4030040e541e200a070442c01d001c0d59601440c2e03030b01c031001c0c441c080c55400c48860381498200290001d03000c001e0018024194000c083d1620310900000c28000118207030100d83e030b079400c103030240302d02440321140c000000d01c02e02c030109040c10710715400219113000040841000b40d0f1074a40e2141c0d036038490310001001d958030603020041ea0038203043c102e0013504074030781c50b414290441081035840200054001d1040790001c003160b400041400f40c009a0920240c1825058440c001c40c8412a54030741000d48090b140010803213031b280c203808500901c280b04800500607a0001e45024034582c0d140c00c0400f5004030071003100c01d0801c00c41440450050344440060301c02c81140440e540803c1040800c0b02d52068040356610070903036800d042040b610790100080100403469110303404c80181010056410081a40ca0aa0f82042d17915040c43c003c0c2d22030b184044171010401c42c02d90072a9174008111100c42c0c0503840800c0e01c1d81e42455050829280180a02881000d0101d07a0008142c4542c = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 757696456 1250 757695206 757695221
    0x9030f0f020a170c0f0a02031902060d09080a020d09030203060c0705030c070f1505040b031503100e0303010603140412030b030f01020d02031b0c03040612141503070b0408061504 78
    0x1040444083c5034004000b1079030f040080704e054180901d140c841d44c211000140071003003e070018060400c5194080027401d041c44060783c100c0e0004414840907811220030310841d441540901c0400740d4603452540020304015007240154240042006d040c030141c0c400092041d1b0069504c007090b5551111810702c24914003c0b407104042521401d0004503a62240590030310441c0c0500d21340c101c5503040103a081e200340c056801000a421410700000c0c20880014070b000c120038101500382c2c0c0c94009444c5441054480c03a401c54802580000010000f843d4944142d52180007403020600090409950b0054402010107048040644500000302c1d146da0921040da0340741030300f030000c640d070340403410010380a50011030704522082c10500410b0546502e28003210385040406000d14074050038000d05960313440c000c0c0b44030010340e9a1200080205144444043e000304c1c850514001c04c529230204061809480d9003103c01592001e0000304803c8500003403058100b024254a51414208a0085001024070 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 757697706 1250 757696456 757696463
    0x804030f031b0c020406080d2309032b05040510030b04060f030b0108010b120a0308070909110712021f09080f0f041404020a0f0f0309021e031009030f0f020a 69
    0xc00c01189507242c0c0004140508031301c01d40341441890340d5a408aa103841d44800844003081c2c00452220054402458036000e075400e540c02c190030402100c0110385007503284080c501d0602c8003400078043e800e81005800d5501c143c02e1409030701d400e0070030b40440e042e000c02090a82c141611a002d010b203556554004001a143c40040c81c00d28a5030307402d040f000d03d8000e2045000e59441c001c00a0f1090400c0034407101c403e00f092006200b40f4000d643c081391b01070b4005002c6820171105131408690746406001d207048441c0b0900780a80c4600c1b0508010792000c0d180600d840541d4055200c43c07041c8a80d444000c0c50100f11a180020300400b1420070703010a100320b100d443c1c0c03000400110280d10045c0ca0003d0015034825411065842030b4904c11320080740b10b14103c02d00419401900021780728890104281c1090540c070300070901c4502c0d0790105141d0082500c45008029100940000750b06040161098140c2c1d00307131082c88136981c284c0340980a00c01040d0142c0400c002108400c2240e8001c204091004e50b0 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 757698956 1250 757697706 757697741
    0x80405040b1f0203070606090b06070b091f0207030f03050118150e07110d1107031104150f0501030b0a120303200a02010603111f08060120010203060a0e070804030f03 73
    0x480302c10081d02e075408500c085a01d01d2820101042010040c85208001c1a000e004149011080d48800101031402050307451140b080821035080041e140c01641e4211440020140e110702d2075141c050000d00f48100440d00b09407400004205060720201c5101c00200002e0001451240f2103190f22848001038000c0100102e4681c24080f081e035003c00c01e420078288800680c0d00c50042d0308412181001c0c80c81c0c8030f901e66401080705002140744c0300d10390310711035a000b04009012203140030340340e080a2950b48004038010002104018958040c055009480c0703044500703a00d840e050ac050680c131000069009401c26554400d103115054610500d0340c981c00101c0701e09074854411100090180c80d8a00085402c0c0740c407440c00c130b035481c2440d08101400c0c190b0150302505483d10a01c003201c806200030842c904201282d0b401203881459040002c062164050000d656440c0ad142400100310481d80580682c8a8110800c400d4a074000219034200e40d15290142a0980501d411405041d00551001c1e9106 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 757700206 1250 757698956 757699009
    0x3080c070f14100903030e0118051c0b0705040302061608040b0c01060603061401020337020312011203080406150306020412030f1b02010c0203070e0123030109080405040b 75
    0x4003954070a6400c498100ca51801c05841d0b0700080300c104e0810b110003000305c0c4039802c1d95240703503024028404508800c17448450105075100005081c0104210070ba680088480e0050021b01541841881e4408200e003000c5203000d00d0750380895028400c01503500f40c451009020b441c100540b00e0110b400074200310100540350340e08840c4490017455144110300c0403a00d001c0c400104039946a01140c4a5001600036508104400392510302040307030b5038000006000c000000060b0550445e41e0440412002d500450310b4240d010407001440c076041e000320398103c0e8a0814000020f0340700350702650090f4402e901181d0315420b00c0b40100d4582441d00b0041c4013074004070b408110038000c80e514410181c02680c4040380060212001d403004210800c0c42100c4a000d40d03554030240d4010074410740150b102400315a8030580c0d0307200d1240b02482c01e8119802070f16000450f489200c005415040384000d044008020341400c03540c507110170348124440c142c001c50300c03144040065911140d20512035a07090b2071404065 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 757701456 1250 757700206 757700219
    0x180b0f0f070e131b091e060c060c11030d0b040e0613080f0c150f06091006051606052a0408030307260a0b0a0e060d142401091103090703080c070f 64
    0x410b55028100800c480300720703d8562541d580d2001411120a42c5a08d940482075031901c501520f403d40104062241141d009518140c0c2040103000201c3c500c4c40c000f9a55940301c0c1000281c0740701d1050b401080c0e101c03401b4090300b03503c4162081d010343d0344181503960301d00112401349118001d030b03001045113000d2240380181182c00340d859603104900100421030300b66607075000c009500c0000d0b9422034080c0c100b403a05000320f2340210014000b04101061520a18800380d58220594070201c81402450982c401c10082c1100078810f034201c10300880341128203017070074090415902d00000741800b003040316900c2c0c0a01200d40c80d0030590494000401c1c181d8807490800d02050103065034840d1103020300b900c0500007841003541c40072180a0f0710000c0980c09004030588039440000000d0b0300480380b6006021041c0000403012502e03011014415605c0390040d0300d0203401100302d84480e00400f040000400030894124030118004041c0c980c4800c40540f1b40c440120018a000c3c4140c11503200105640c0012411 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 757702706 1250 757701456 757701467
    0xb150c03070c050d030e0f03010b06070501060e182d0d1707050f120424060501020c0f100c05071809020f010f0212070501180b0f0f070e131b 62
    0x1624001d0301c0c40c0340200d41da40c082c0110b40004c3d0001a000480001040c3d00318540042c19400c0058020f0011170903061000c0007071142e61024200301d880c1d030355a04080001c9155041c02c264803102d03c40203543c0403046c40c00d03c15199004030149186500f80101104500000085108802c81c00e420031101c42d841e441d04060a150047c0e805048002c101e1000545000d03c604211050b1011b00400c150030800c1c003141c94022084c0140088541d0140c0c58802c120a0080071032600800c0c04000c03000c82c45a1501001a06041c01050450301a2085084607503143e11410b54404604080389051280e01c00c0f54246581090a15001406192080b0304030b0580307250030360000c0741a54000c541400034009400019074501c44190000005a0013140c1800c207040600c801828100b80903c001040385002769030050b070326400b0300108035000c55041051010001c0c0445c0200e600034108841180c060130000c0c00600910030707801803144a17045021200d00b84038000e400c040a50025111014402010220042e10 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 757703956 1250 757702706 757702717
    0x2030703120c2102030414030a02100819060509060d0201110304120201170403090b0f040302060a0f120b061902031611010206070914060703021906150e0105090601030b150c03 77
    0x183d0052051100821100b03034603024540c100780d60015441e052500e044512014250080e0716031500503400c82d1005a1a0340000b00b01c0b0b10955600e1403c03030700e003120307400000105404d010702038149401420302007a22403000c3d55030042002c41d94500b0070007862004070f44000d20a003120007180030104001541060070394010001c4c61003602ca000d40d00b281e618400300042c00854001e030001e0b07841d510420030181c11000608039014541c948914068481d0085140b95010741254000907503400081d0400660040f0100002c0310700700070a00602c3d1803080010100d00411400444108072081035000d200e00800850349480000003203800c044d84541410003c4141c0e031a6128090700610002542c018842c4203680103a0300351400d09140c2d00e02d51030606c032098010900440a41c0320f916030040e441c1440465012401e44202008a0001543c106100c030703801c5281e0101d1040d007040ca0045c031080c0e80c0c0d07007a016800602032900103110f0044000250418141c0c0f2049460040700107541c20f54200084001e00 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 757705206 1250 757703956 757703963
    0x304050717190b3c0405030705010908040e012102041d0708100b09071d0a080610091a010203040b070602120f04060b1c061e0633120902030703120c 65
    0x30355800c0103018411100c070181000000d80416401e101306040d0700d51840c6500940100112420140c207680e40d1402c41350b88003825032f90848007040410450b03910f00001d6002d4291680d00042c446400340040e1071440c6d0900d0000c0c4542d44940300c0741280000d507480300300301c000312600f11049140d4601000e51039140d0320380f12000700c5007042800b03207030340c18045640c41c0511140c0c1d0f1111202c0c44881d0a1ba51000100340300103078444807d00001840c92010081d2038064000d00d4038451486141c04010400c4911500c41c88030094614800481183c0c0c01000b41c5080b520b190300c5142d034401d46c40c580340000b440351901d0603482c0e02481d020f12940c60f0000c09103134441c6115441c00c100b01040d49040102201420080c0790035507804990082c00600c00341c012001c010840201c001d144003420500e40c050ba2101e4010800c01c45030511140070305150702503c0074510350030240407444c104c07110100422124443c10000343c0c65460313401d0001152401c11400c4015508a03403900007000384444018140c500156064 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 757706456 1250 757705206 757705231
    0x5100215090c0d380115020c040c021c09080d14090d0c14031b060c0f0d050c1c08160e27090d0e12120406170c0304050717190b 56
    0x20400740d50b03100700000844c400c402c1d440d00d0341c1c0c604034914000c100c440981e501180543c60141a0584903401015054070381500500190b000c00c1d0030001c0010001c0110703404000f60040c00704407400020883c048010081c1c07030440c0000c5e0780603041c91003d10580c2c506540003401e440c0c000f020301100d141d843d416154031003c01800c0001c10801c06035500c0401030000c889118040009045240c0701c0020054040b500080c4c4500610803e803460804500700e54030f00100c0c2d400140100c40c1842030240c0001222032501d108181c1482400c010185c81c030050050764001c0b0748020020303c45004546621809100408150000c58000c09907002030f135041c030000307180303007071540100c2c1401c4c0c80030440c4102c0950326680c40a00f04501c004021310344000801100160055440440415036044010b01c0507010b80d0704c0b12080f00e4000d07036038620f14400040649400300e0080c000d0100188011440000302c078458070b040d001c516100d141090414000541c603420083c0030441030010048103000300b234490306c3c00d80c800 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 757707706 1250 757706456 757706513
    0x3080d060e130c060f0e0a0b18040917030606070507090213080105091203060d2a050a0f15031b1808070515070309050607030806090105100215090c0d 66
    0xe291480b09100e4020804403100d03800740601d901c11000450b8003e2580f07003221850741d02c0000f00d820442ca0b41c0002c840140c0010f580340c8881c00350030310030f010f0450958040107402882e8407000c04040c0c1d00c05c0e00c82840c0c1800804a1400d07038651003604c00300b41c0c204058410842d070340d02800000358414000c820001c007004d0b0300010804018820b05204051100c06858149416040466076074401090070340d00c1805000d500021900c01c0d03c02162810f80303403040110300c41d29030300051900c490a5200302d104202090f010b0141c0d810034440c040445500d061060f00f40c0889103c2030300900f00800400381a00500340103195240d070310030b20582e040740002e8601000c40ba1581d21083c0c561001d4040d550b04034000c825102401c906180c010401d2038041c0c5801e55580c0d84450001d9a2035020003070980003e000b140c04d000480c074007410000c1c0101801c4a08010300202c40901a41b078181a0200d840f481d9010000140d58800c2804a01c0000800614140380b403460752400008e2480d004031000c0358000100700 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 757708956 1250 757707706 757707721
    0xc050f0a030e070e04120e0301061d01140f0d20221a010c02061c1107060b01022407020f0708031803071a13030b0a05070206130206041a0403080d060e 66
    0x10013900540d00b0201400090706081015034800000000701d94241d96034540009950300390304803405404074513107002080c95144c040308011745c20401d0180d520a1900c2c1040900d5591142c070031054459005401d400030710b0405644100c814024001190014201681110f60041d84080c40801402c00007041050458513a003020f00c00140c403403d2404181c503036000b0300c0980351103000b9006042c40074440745031001d0710b03801030003c1e1403944030006400750020441b50100000c5001d100c05c0312000707200800b410002042541c98007158090300d200c0480860011511080c07080c0419440581400c0c119070f07115030703550300c0a40d0701d90200d00d194801c012901040c02c043c0c80e011a0100464104511644494000034002c04044c3e108080f030903110b0103911800400240340c0c0705240d00c80c020707448001496150480003e400d026008007640401651001510010703511b103403c3e20140d0344034442460702c0c29140d2844014601c126040900403000200e03031400b01c01d8598001c00d003691201c0c0310a180c03540714880f = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 757710206 1250 757708956 757708979
    0x1d06070f02122e061e060f050f0901050f09030706021e0c030c01030e0312040503040e0f1b0307050412060f060b04060c110411120103020913050a02040c050f0a030e07 73
    0x1800f401212265880d69050307039545258501d41c54041a000442e255540381003080a40030b10810807035695400740c10814150410100800f004a905000e460500411070b081654400c1040c601c2c14040042286038030302c0f08090641d45002e9000d011500700a842d0000a5522007880701c0805c2c600851030340031804108040781c0d124640f5006001496021100c00041d805040040c088140b20710081c480e07101425581c403d07c0c0c0c000c9009802541da0b1328101100641c035400010310845040102c7d0003031181d000c5c0184100075410009070982516500c4800b021107151160354403040308004106014000e00065500000d000e0b103d4460411041e83d071880b00071114041d5202d42c102003400c00ca00d02021600207074107140b01d401c0042000a08200c01c521408450b004141f105a4101d0500010300842c103103c803c00b9040014001700721038100700c0ba6101c60b030f1001801c0000303002c1c6403605800309189000380261841528050403480d260380920a0040c002c210031044200035101d800400600c07040d0340c4 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 757711456 1250 757710206 757710223
    0x11a0301022818030c0302100f051804020d06091e1e020706090b010801020a11060c07031227030f0c08091e030d050a111209011d06070f0212 62
    0x100801ca4020500e4008041c114002e0696041400700c101054104454802421005075108145007034600b8258010700084000e8440039409001880040400454001c0d0540300108040e802504d81c104140f800309000c3d004040d1140346403030030440d01140c40a00c680102c682403245c040f01d011507800c41d1000da0161100e9504500e50650400541d00e5881d0b6103800401d002c500445001c502084c2035a5501d030001000d83c00281280d5002c03420b8030074658488030605640110400a10081c1850742c03d01d40b15109061009042c03102d0b10095612510302504802c041070311109086120b883c849003c00050a8283c074220000385c040d94554034080d0141d189541c003142c1042209081c840b82006104900c075202c071400300c0261200401d40b4140d9802c0066036941030969032030b140c858054039405403034a20180c5402a4a40100c0b0150007d0090601500c84109092078142740c0501001a080254225030900316005000015201c081c06104a1418030140c42a1240c06c401c0395203092540c1c0b00c9281 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 757712706 1250 757711456 757711477
    0x1a0a2a05030f0405011b2d090b07050115080a02150406140304060209150d0b030307120f21090b07080412050901110a050d081e0c071e0302011a030102 66
    0x5101064548000c041c506a005209500004106c89a41241156010300200a8001540840c414030300d600c84079021a240c82e070050060f0303411102651014158403043c1c040d61802000c0411514244142500580000c0401035011100035488003a02d079101ea85902d01a40505107015100c3c40f01483c00080360115803440c0e40b2a001c1200c9200c0081a55001510a4860580034401040150b0b28032185040910040100507640d406820654068940d5828a14441c2c7c0091241001151162620307580304c0d8050b00c6c1a000305421801c0603915620001e51580d440c180011807641425440c1d03001221090058550317403083c1d0340c0e4844c00c442c40e080c200c1d8010482c45040302211000da02400290404c80c005052000c000140d0702036040c9032240905090341c2650001d00c20200c0d060300300241940100c0c00e840708d926001c100081e0200da13014094044500a040001c0e40c41c00d010a4100008bc111031140d00710140b2601380c01c0c000c0c003134060314402c00030095185071900000d250510803110040203 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 757713956 1250 757712706 757712717
    0x92c030a020d140405040216120e10110c090a1d060a0506041107030c11060c01060f0509160e011b120f02070f050d020f15071a0f01121a0a2a 62
    0x43c0411b220180d00700446d03007031100c10141c04040000d6410041e44c51440700c01d41e1100034000d040070400501420401c4814107219060000603031603400860400340706802601c1e4600e840c0c07602c803070860013000313102e030780d00c0d0491107114580f03182c00710202e0746500072800c541092281e070b155201080225143d60640c500140030401040c800207000f9800b410006000304001c2074404100c0380800c585030b00c0a0381002144c0d642e80303400d0102e6888d450803840900010343d52004246400541c031100d44405941034814095100054040340e841880190b102d0302c034241500c3e04410292400d00c044a01c40c85801010448624200c0d903400c0c800180c4000b00c1d40988950781c001807414050009010101c1401e80e004500da20040015841d035910b1651103800c2c140c0080c3e640d402c141403a0001d141180340480c41480c2c0d000502c0080c01443c40043d042d113044550b001d00c00e5a440c58001c121b9000c00042c1c0101189080c10000c09000607440b41c00c815050150480440c0240c00301c6801085c100c50a8402154 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 757715206 1250 757713956 757713959
    0x30f05010e070b16060f1a190b040519090903030b0907080c03270102040305030c070e06031f14091f020301241101020403050303041106070b01092c030a020d1404 71
    0x10700004580409500449001440f940c4c91403000781951401c41c0c2911500f804c03001c101f046420881c140c000b5a05c9030889540c0414108039140401d031203a4407a16100b104a540c4410b07a0101080d450001000001401c2121402d240303400f4000d00b8a00024900c00c030605800112102c1c000d40c81d003445102490203262a59452040c044ca00b01c0040e190564a94480e0b040082c480c0d03400d00c010006140600010f6840f4501400c60515140340340c0c000900e0314001106001a0352400542548002000b40b41800888902428100200801c4020702401e010000c1409500781740800c00512040140008401c04182912140b050784002e2203030f032a0f1511400c560f03612032100082000f40444251030400460104503400750300761f8000d1b4100b0750707aa8000006000c204600000100b03000300c81030307801c0c0d42091520b80385c0f425075290506c40d918000c1e44031540c00c2c03035905611a2082e820144400c4840c52000300c0051207079030381c20081c81e810261140c107001200c2d1900904c044510f50003502c192a180a = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 757716456 1250 757715206 757715227
    0x70b071121120c1203010e0109061a04090c270503010e0a02010207030f03020c06030a0b100e09040b18070305061b12041b090e011b050a1202090d0c030f05010e070b 72
    0x1d40c00310091103c64080c2d1030405000c421800010742c02041104000180c0b5410910410204d4610341d208501c022100c8042e4030f181c50b0750509590031140102000512440e0004050340d030b48402c5410061049032312241d215006c000070706401c050341c1e4250700030400c9007409450941d4400d003100c0042c0c00759002000030070004000598080040d4484c0c0705846800380e21030b02003041a04180c41c5403864980343c0030f00b5086401c2030030120110f01d59070300d40310b410a5001da000c1600300b080a00040c010300340720320019184850100b40c2000e02650841103c96a0b40d40c3c0c14850f0311042c0540b0603602d081d84090720b24880c3e4900744107440103140c564440c1095510f582e42e500c000c5d4098a40003004510740e40e1fa00049410582c81005440081c02c0b0010910080d03151080b528117111418040a0041c01c1c000601790741c5e03018250300a44090b00d000140e45030700440004030301d841401001080703501041d0020040003010000706071183c1c444c20083c1302110b04c40c4605525000b59006010b11030310f051202c800714 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 757717706 1250 757716456 757716493
    0xb0406060e04200703020a051630020a06120b0a0803190210060f031a01080714060f0a09031a04030203071217090c12010b0a0314070b071121 62
    0x8440c80c40f1101c0c00002c00f5100c045059401101050300541c04c42c200d00d0050220500801d035a00c0881e4680410781d41c06c00d00c0000c6801181400092290302001c060b142c01c0384003240300d010840d00100407007d101c0d0340303040013016002d0040000f07034041e003803405a100d2800c001e0b2400065544040c003541c00c041ea1458914411540700071038404510540d08070512050f0b491160b800540424401a1403c5095081441c034014000409001205491b00100184c00000c500741c42695800c1440764400308410f40014841d0160400a80c0301f400300181700300c05503820000c1c150031030b407040070011401c022403680e2500c1e8000071a4043d0241c3c20800c000800241400d1041e11250810308004000380300e00107644120450865201c805980080314101d01840c00040c41d002e0f060755040244182102400800c0c00e45d1102e100c0101400341002c5038500030003041c4080c10141281c1001962211414200b00421204100010340181d40e02c50744640042200c3c24160b48480e96200101502281d820301c5101 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 757718956 1250 757717706 757717721
    0x3031b070c270f0f0b010c031d0a03061d07050111030f1b1014090c010c020d0503070816060c0507081b07120312060e010807150311030112060b0406060e04 68
    0xb45185844002404826144507400204241010018043d0000050700d8100c800c032844e140e042c481055190300000c0d5010a945d030014902614a11030070310003001084800300d03a500014001420201c0006509142a801b071020701114002c41d9942030b5242c005480080f91250402207030b07002040180c0404003100014124050000f003146d080414903840181049000c080c08604144c071010b44503d140203482580360044515000342040c07041d4000060030754492040002d0040c1102102c6506000c1c0500603100d845400070710103584d60ba03c41280324118140342400b180c044d4501035606030118803c4095072480359010f1055843c2240c581084490000e0240001c1140d100c0c0f0135000c19011002d03060440682d109498444240003c01801000da5217260800300c100261880100103140000850004542100c0c00403070b050103883c03100320050203031131104440545000000003403004180b5944005030340658010800090300030100801d5450350321415000a080201e10b00091600d54480752 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 757720206 1250 757718956 757718999
    0x3030a0203090712150b060306030a031209080714190b010909020d020a1d010b07050304030201112b021b0307180e06070305040c090621030e0d0503031b070c 69
    0x40d1503c0d5580c105401003162204101c60007103c1c0080310445c0d099078024102da14074101d800c1030541c60a94003203542c075406014083d007045500c0c0c60100e103000665102c010200d40120b006941d4100d142800c14a00074698500c89240c0b08414140c101c1e1140308020b051029400400c0091992910006001408100d81c06982c0141d12010f0a001650b5144031007004001e000c0c0c00050b00c031002c1c86c40c4442e103641640030200564080040c02c2c001a8040111820349a09081008a1010301110580b81901504880310700400808a03404200c200d03880c0000c00112a03403c450400094241101c52000710200c09505648949400d12080c0c8104103181020fa10740b080020303680c0c001e4041d041c03809000b55640c4c008255500b0a22041c0b085214091001d450449000c3c090b6501c0c25240c0c000d60100e00344030202000c1440004010503114105401001c2c00c000c2641518080f01e04140751a9842611450054018a40710600e440c01074004d850b58075030056051400c240c508201c4030003000038050020f = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 757721456 1250 757720206 757720213
    0x80a170f070e01170108010519060b0924070501320115020a0c0b0c0c06040612020d09061407030c030c05030a090c05060d0c02010b0117060d170f180901030503030a020309 75
    0x3020f44c40300074009680240103a00000c58a03043c50144816028070b0314101c104c615040442c1480b03121071030b508581c1c6d003040035140c194400c15403013140c00d20400e9000280c40380c1c9600041e04130900105411072491071004201d5070340c2d010361042900c1007c01141c50b4107414074003460010404200300190381c191030744490054542841041c1d45010800085810a02e038500010504004201e0100504d00707012206980715403074242814000352001c2da85010350300b066600050440d86600d884d07000790000650009041c00244140b036000c40c031070740c1d0844154000900d08409210340922900480c58805d0003034803154034603180c0c1c0c003a00000c3c1c012038009503019112114001480e850b524000c00902e00f80001c000f80050b03d10f44001e0039501c815401038100901d001455410300c694102d81508614102e4200b0550090b900d01510f501c4121a039865418802244405030f0050340d00c020012000680807690307243c0071401c01c03c0302c41030302800090203d6000303000140001c07486900540d0003001d0320084 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 757722706 1250 757721456 757721477
    0x3020d02150c0a0b011d0f180712050109060b100f0804051c080708070f142107051b150c0310030b01121b05060a030209040f020304080a170f070e01 65
    0x1c092404103d04000c48405201500400101c000320041d032104c0d440c4500c54102c2c60500303a244240405014005032219034081303c0c001e074501c6081090700c0007840c14611018200b809401c02c0c50003045c881e14140c039920308007412111075103400b0640944640e01c0d40c50b5000f10400081c1d0840348408020021039540c850044070f0028070700f00c045d48000c00c8110ba41ca05203e8035241e50f005024980c0580f68005020301114041e030140d81100080d6807072500c84000710f89403a22060b00720f0541040b02c1d0544084019401400070040d0b2001c01807814060b98000b02482c041152106035407100e100d41b01c0410042118045034800003c4802550014011a100e000003034607601c500002c500280c6c4503641c00924202101c042054001401032105580f0030b50070001442c11012070301c6d031312541d9a1041090f6002500c41c10310381e00c0f41d02a80c01e030016420115107c3c5028544402c1a0b44660401c0b004034214205403803011240d10741240c81060a401000c0c10340d224000150f03211500542c003d414015040c0c0d1 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 757723956 1250 757722706 757722727
    0x316060e04410f070210090b0c0913051801060f08032d190e0d0506040204050a060b0403110103150614030621071a0703140c0c0d0308070305010f03020d0215 69
    0xc1d4680180303d1402c0518581c20005000380c03900c5c01c0564140d0150703090483d51000724110700d402030b601401c201c07a078543d0707000e200000413940c4401070b000e0798009203404180305100a41c51418010410600000c200d51500c0700982041c3c44080d01c100180c2d079008101034120118118100241e120b20300f201c9810611088640b59402d8014000c2901510201d28400c010760f6400b44000b03401c0c900550300c1803c1c4001984503580c542e030780240041d0003140c480c0c000c100c150301e544c1e000200621030180760fa41c5031526490002c496601c941012800a410b102c689205a540700c4094802c07140151519080c0c030960280e180016040107040680c807400e0f1f14451000d00b2a10140d600d00d44c10810042d00300c440c2451149415502c08188801d040c240071300011000030741103c1303030340c1160901000181d00c403804110018600008420042d402041a08401c42003580080d200d6020310403c0c1c81c00c1c80143c1c0c84590328184025039200281d4400f403c10025009402e100c00c040401c005445e98642ca4510402e4 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 757725206 1250 757723956 757724081
    0x1302130303030c080a050103030c0b1f06020f01060803030609150a05062802030406020c190b1308011a18131407030c0506070b1807050316060e04 64
    0x500c1a00801d40b0381407070301510350f8800c29141d80f01100c100c0c204000d50464900038028018040010240080c100200350241c2d0082083c03010380c080b602506a84988802e8020f450b10009c8444100c25805d040e40440e039440044181c80c8141c1740a8020b00d40caa41d05a0145985d61400c03031541d0304113180003000314180d205c07000140510a0001031140302004d031101d0000a04c400d007400001150410b00081c044682e0201e0440c650000480d030f401c02c0e201c81c000700b00040107078a81c04204c00240c0040c150145c0340308c5006a00884900e50f00811000000040c0c250a00030145805540415045401c07d228054010056004003401e140c0040ea40d449548500c09042083c4000c803032139002e401c08008200883c041403001c3c100c02c0d00e0b5a8101241d99a811480c21400b900c11441c407d820410090750510070003034400100401004c0351078881e03111142c0d2200640d5070181500186d04c1803181143c50a05004000342d05500450f420392002042544000d002001d62042480b502d4400038034046339540c4 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 757726456 1250 757725206 757725209
    0x1314010f0209010e03060c1b010b1002010c0906140a0825030b120129031c090f0501021c050c0102131409010e0115050319090309031104020403050705130213 69
    0x8080c0140d441090b60000742080543d0f5492500c40d601420400452010b050161604100d40030f0340008a441c0c01a80310703001d0f10f0070030803032600b1a47c000030f5048101ea054118010304009031b1036005007985c8a007021a400f050dd80b0500c41d445a0401014404030310074401558000c1d0001d081c00031080e518001c0c800b020314040f070201c0000b501c1c1c00c127414444c609402c182c138070300803504020003500040303201e544100240240c0b00c8100c81d0340c64240c001c054509100e1201002190b0742803003000820030b0805006a030300385c011314440c00c510180100d429400021034910750320720030f008016420050401150f06038401c0284a0047d5000c0c0070074a000d14070003025001a1800034000031483c1c0c5082d00784540b40d80144c2c0202550304051004200c49141e0021400e07810f02d030307441e12070f959980740c9440c0ca8008410071403120000e4a0010300304149a80641c0c81005c5e644180070032000b2084250400c400da000d5404081d042c0e41014a00f001103150808440025600740c00001d41080c00740d01d0140742c42a04d130b = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 757727706 1250 757726456 757726481
    0x3040318030b1306110c0a020f01020312070c1e0506310302030d050a060b0d09050316060c0824041806050414210703030b130c09080c090f131401 64
    0x3d003041006021300030325000c0408400e145080c80c61021540355030721100384000c1d010303592045c040c0103207074030074011201309550418070350a060504041c0182240c4200c007040d01c20704084a5a642d451510f0030702c0001c5181c011001313021030b440b40c1c500c80280003802408940328011a060b20002c1c014402c4620120a0103500510b40324104071452005450004150080d039a1403d1428001400c0031410303503400c04402607002642d01c4a920700a451440303682003099011007000e031074030100072264014007144d410954a00b4004e45611500d16501100d03402c1408915240d29180002400d09a211800c4000d0102c0040c1d09040c2c0f0f41c0f10541121010b490a503101d02030f2180c40300f0f0551081085044011003c2c2c95598403c807102c2840d0240c0c0601030307004042540343c16145a81e0750b22500340c40501203400c403041048504140010708019500d100d402c802d40568002130340c2501e042c8a01754443c20300d20306042c855640f040c066034100d0b20190b1045400e03501080034114038181c24450607500910 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 757728956 1250 757727706 757727731
    0x60307050a1d06090106140f0f0304060f0e1b121002030702030903210f1b01150f0608190903020a1b140d110f0406091404020a0e0c03040318030b 64
    0x2c030000200c0481c40c024420f901600d04100108042c680c00b0480f058406070070300309162540203c8202d0000703031160400e010740d001c0c000700901c000c1c1305c010341c045245401c0011b01000320410180c88180c0310710186120303c44032804030a00c601d440c14a95120b110201800064804010340040042c04980041d90050b0041e80301190314600c50400300402c50480c0d03c01d070009551103003201c010541900c10481d0107a0702c0e80021400031904070b150b4100311807941c0c5850007070003da10580150525a034181c440d0b041b201ea100e082c00224035004084050240910b00ca1074002c05010908040c09842d1030700048003148108800032010511000b10b910b40c1c21300c100011442c5610301a418007030340503100b00c0b5921480500700694006901041d481500510988078450505900300005009245139481000706a0800d44403070709800d0140d008501ca5882142e4015280d900c0703060158000c0c1301110040e03012002000498080380c080d6641c2d141070007104407103002d280e40b0307903072400d40d0300100351104c4c3c44551 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 757730206 1250 757728956 757728989
    0xf140301140a08190807030e03100c0806060405060912120409050108012009100e0a0303050301170708120319020a030e010b010e0a0611070b16030f0318030305060307050a 75
    0x151a0b95148014200702c03005060418100c0464054801e2030b40c0b0040030340c103001800404250140105d185a814010140d4074172001d0403400d034004d03015603814070000a10b0070000511900d41340d003d990640d6030140c207032810706c8058414001d00c0300200b60000d03140c0c8030340c40c50703034020030300d9203000300b010382030400b408912940b40168031401d403160f000e0101c04007194030707080c0201c1e4103003030094074011700080b101c0c09180700d10b034041a54052407e030303010350f0415510f510100c10f054101004604841c0c8051003080314a40c14030846403200d41034010071030b954015201d881c88140c4460069604030200c841480e085803032401c402d400301e0b8006145000403a491301e1264407244000e20408002c03003c2824110200079845002850123003a038080e40703052010101080241c02c20030081c0d030300a030003501001e40c4d03100c0304401ca071041c2c9208d030203040700000c0c14100003d907070350300ca800f603c601e00c5541c0d00300c140400507560b82a0082d00c0000c144980500c01c00038002860380c1d5020500c03005008145100b0b001c1c6 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 757731456 1250 757730206 757730209
    0x5070e0c130603020f0f07020a031b0303090b03060306010e0a0f0906060810060b0d020a03020705010903020a1502040e070305060303090a060914040908040506160b010609050901240f14030114 84
    0x4079110350003601803520600040c3c84c0c4041c203134121103048180c1c85030f4940c1c8003505c0c4005404824507400103004400c0d400200e0a0a500c0c2503901000d6a009440d0301600b81da41700e02c840e00d80e1000f02d60158042d04100c004009500f02c0200c1e00e031700960002004202d80b141001c2d82004c80e040a03009444541e1034606c02c000c030040502050141e0001804180311207410b0804041c00c07441141040d088213039000424002003032103941555100359008000340012881c0d820003d42e6800780b180140c0380c4811000d08602c10b009180700700d404540394101c4c4c50040380e40380f00c0c00341d0040038014409a09400308100c220180e6845050140291041d61603030740d00c0506225001c01902c8a03c10074500803840c0c101c0034000b080140060fa0300300c90040b11019601c845506a00001c0841c03040d004101c141c910b0004a00a030b044680007081c0d84042d50324030300c142c1e80c54403e85000001440a203251880c9900e4001c078241c4a10011001e003000e904000c030318014010304480301a0b200340c0c0180c19588956900c00441d = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 757732706 1250 757731456 757731487
    0x706020304030f031514041116110d0f0f0c170601060206070c02033a030228081902040f170d0c022110020403030f090807080c060705070e0c 62
    0x400e0404e01d010070010030a02025003100c4454000d0346085280042c90140e56a1103170040d10706503070900c0f001074558510500d509803103a0315440446a4080380403000801d418480c840115054102c481c100300c29110b921455060703c0840010b55903443c58080124001500c1e410004091045400070038141d854520003c1c02c2103000307041c640400c0705a10210016980014181c450b440181d640c60101204401c8000d2801c80c040e50304010402440302e078110640c0e010340c00741c0300004000303042c003185901800340c0440403c0c0f40701810020070444004500d1000c01058070f0320349100b104100529080d11502c581040103c40c0e485800c40701d4007a000459000420b1007510070208590510000c60300da00d50029022000030219400b52031008400d02c070800340e0802001106100c2d002c1c046580715100c0c01d0081041541e030001e0030206007540c0000659060004440084503004ea0141488060410400900350701c0180d003902d0034401c00602003001c0940354001c82c09400d1000082c0d50300d02185081955 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 757733812 1106 757732706 757732727
    0x50604020918040c0e0f07050a20070f090c0509060c121303020f0d050309011413080a020108150a090b04021204140f190308060114070602030403 64
    0x201d6040302049026500411100e6080c1d501d0f01700b803a06000b416105d00301d452104030300181a5a1081c0050003000c201391600040c00c4035550b034180701d40f1140e21080d001ca82c2151001304403050f400114600203200c1100e0034820741d511034001810343d00641c41e0b11806900c000604c1d00141c10140046a840c160300e0240c540c0f100c10600d114186064607010490141c901d5644203000e52a00c05065002c003581300f801586041803500c01141c0540c180c1c200c641c5c2e24001440000800540f445200001d00740950003045208110b000050220f00094990419120413a1007070080344c40303800220003502d9071050042401d10300f03040850020300c9552448002c5074404000c0c401000380e008010701c00c101980040701c10603c01582216144c02a0742c030703c0c4610702e480040110009000e410441d41c40201414800c07100c002c45000000307140d00c00b0380b04456059002041108043e00402d8010 = true := by decide +kernel

theorem cover : BRFrame.Cov 757553956 757733812 := by
  have h0 := BRFrame.cov_init 757553956
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757553956 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757553956 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757553956 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757553956 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757553956 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757553956 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757553956 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757553956 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757553956 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757553956 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757553956 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757553956 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757553956 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757553956 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757553956 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757553956 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757553956 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757553956 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757553956 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757553956 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757553956 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757553956 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757553956 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757553956 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757553956 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757553956 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757553956 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757553956 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757553956 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757553956 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757553956 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757553956 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757553956 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757553956 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757553956 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757553956 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757553956 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757553956 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757553956 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757553956 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757553956 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757553956 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757553956 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757553956 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757553956 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757553956 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757553956 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757553956 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757553956 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757553956 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757553956 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757553956 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757553956 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757553956 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757553956 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757553956 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757553956 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757553956 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757553956 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757553956 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757553956 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757553956 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757553956 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757553956 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757553956 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757553956 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757553956 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757553956 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757553956 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757553956 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757553956 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757553956 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757553956 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757553956 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757553956 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757553956 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757553956 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757553956 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757553956 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757553956 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757553956 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757553956 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757553956 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757553956 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757553956 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757553956 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757553956 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757553956 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757553956 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757553956 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757553956 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757553956 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757553956 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757553956 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757553956 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757553956 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757553956 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757553956 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757553956 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757553956 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757553956 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757553956 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757553956 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757553956 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757553956 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757553956 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757553956 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757553956 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757553956 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757553956 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757553956 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757553956 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757553956 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757553956 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757553956 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757553956 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757553956 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757553956 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757553956 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757553956 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757553956 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757553956 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757553956 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757553956 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757553956 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757553956 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757553956 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757553956 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757553956 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757553956 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757553956 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757553956 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757553956 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757553956 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757553956 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757553956 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757553956 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757553956 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757553956 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757553956 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757553956 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757553956 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757553956 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757553956 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 757553956 ≤ n) (h2 : n < 757733812) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
