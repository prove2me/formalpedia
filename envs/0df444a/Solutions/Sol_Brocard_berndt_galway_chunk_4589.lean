-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4589
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T13:06:32.086906+00:00
-- url     : https://prove2.me/submissions/d5ee002b-f435-49de-b44e-718399eeefe2

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 825179856 ≤ n < 825359712 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 825181106 1250 825179856 825179867
    0xb120a0c29090d0f0c1205060c040f050108070c080f45011206030506090d050c1b0d1208011502010504110603060111030301080a140624060d060906060e01 68
    0x58100a041c030324580740802d01003101c400c4030078004070ba071800b2961030741000c00c41040700702d0010302000c3c4c113000c4109001e190007828000014005881341c0401e002c00d101d07074105600c14100340c034005c1c2011003654841c03940039246c04280700001881010f00240440010305000c1c058484800780c00042c41d00880480440c08841d201285021900f021841ea840061112404040441001810400c5001c00c600046070191410f982042e07803d940f00c00103200880e0300030040c3d291850302524145003400210781d0980d854804503042442e1082c80c10b6001b01c441e42d83c5a00b5488419484107c1100045c0300c18005005888248034a032090003441c41103c1d070b164018040c2c2d521460744807142c012081444010007105c1c0e00003400701e6040001c220300c80c0d10850ba0410040d030280a0050041041044c645000e0000f52100314000c0c40390740100342403040c0081c40d0b0313484050f62003091910121500001c808502e02d0b005a40300007042a091034000030b140282540000c0c207443e42581d41308040030030384005503070 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 825182356 1250 825181106 825181169
    0x911011e0c0602030735090f070b0913050a052505090607140a11030c010f1704050309030a030504050f04020f180f060f09040509060c0d0b120a0c 64
    0x3003080401c040e00000d015034011070b4000360f1070426492034101c2e41001ca0391198001080c01c0e2420014004d4004000c2d0880c09540c031601100c000c00b517905800c80b100303440305000d00c619510482c1c0480c1c480c0455a80b02c19201c2000c6814604112600e403588900000d00320a0b203020112081c1c40c0443e28985120f540a004030102d29190030b0700d401034003010320110ba80185400e84031041c1c4294442c1c503880051104030f24003030180c0c8540f10301c501120704140c1040d21203e80f0714148001c01c801c80700800c0c0c2181501d100a2031000604940340d98508026045105d912411540b50007890403410406402c2400f52040d105c040e100d002c8203204e05014031040344254105010340740c4060007070036560084020600c41e03045000c0e0802c0308409001c030100320550003402035215016404a816192800e0070f11400c1e42c094040c0c4001c1c6414184401441550301c20102d1820380b00340c0b1200b40001946030071000b080341d03a8002c42112115400c40c2840242e5445c2030041d126000c0828004101c810010011000c = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 825183606 1250 825182356 825182417
    0x1a04060b0f03040f0204090b04030306120b2e080d0809060c03160201021c0605180708160c150e06010b0405130b0d0f060b03210d0e030409091101 64
    0x103151003640360640d41c4a4100500407100301e2192081c1000507212400340354120340c45404a5030490130a454040c040e5200c5800c1451481c030013070102c90110749850a4650401c0c0c8001500360100d03c2c0c40322981e01d04180c02045070303c009182c140090700d0380000841e03080c0380c242a0348614590320ac1401e41c40d1100b805607410000d124040c030105214030796110b0380244802403400010300e030a40c0d00c00e04820b800c28400002002035900c42c0100164100a90194002c5500301162000362505680160104034090116005d95000100c0403a4050203207501c0110b2980151340800400c1040c0d03a154081e100e29011040c1c1c40c0900b034000106901e2050554040e40d02c02005e0b40ca00c2c030161441c43e80100303148003c4075400f83e5800000b1000c2030025011b24012405070402041c4441948203051401031782101038541a41ca0940040c0c000074181c068507003905094401150b180030030404549035006580104c0d900600d807101d07600401c015080044400c50003070301d13072500d2040e40000c1710000140811a20 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 825184856 1250 825183606 825183629
    0x5070b0105090c0403150501060e0d03120f0207020a090209040b0109030b011a0d0f090c06090609180e16030215040e040b06060c030705010501080712170304051c031a0406 75
    0x41c0000d1030200a0700d98003850184189040558946800d1350940410341203444840d661070060200581c440200b00d1071000517162049040e03450f940040c10001d41054403d141c039520318200390f200000383c0440f00c0c115001403108221603101c6a9281c020f42c408400c8901c074600d00701805243c1c0d4000c0c0b031040c0460780c01501e0140e160b0300e0028920b0038500703000d940152016003080003800100d4035100311f10041454103800901c407040f80c90000b210451a40003c07041c0200040100000d0b54080d0400382500c5a80881d001c61204011340b100240c06147c9030645940030b8200c42c031415100c070341c1000c0201da000b20740d18030542d21114030b02c0e00c09219900901081c40b86c000001808a244d4280990b00400d026001c68541705003070001e14255041038070300300e40c56519000100111001040042e018040c8000100e50000c0e2580d030700700e0880d2640d00071701300c80704001c0002810f002044c4201032011103000642e850b41c10f00d0800040051080200c0c1710042e0b444101403480703a0030248600c509842402400703 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 825186106 1250 825184856 825184859
    0x1c050303070f0201020d0603141204150c050712210e01080f07140d150905011419090216120f08180a020607060b2d01050a030219051905070b01 63
    0x302d990300c0eaa103107642c0079503400b000340c0030490305144a4070000f0350045440f00e0052010b00c09032070501c4010384120118500610061100704030b5a160b45594640c5400c1002c0ca100c070034039080307081c14503591100b800c0bc02150b10080c24001c100c45030f001250040100c1c0e42c8940841070381607488402c0303001401d00103078110001400e05014a462a900107010b030030f1000c1403608851120465611001c01c04140549a805151003214100c83c81006060980018009036041514a03402e44410142c0548950640f9021803221082d10b501c03007002e403154200540d07841441302141096014440ca0444d070b401c1e000c1a00b032002600c5151141060300a42c1e4542c074958480003030703404510f142c5222881c0725000f10200b040060356101d0040901610502c0c000c107050b043d01c0d0030083d06030559945400710500013404407030205c81c0c512480701d285200342040d40d12107402c010304030028042d00c146003888030305d81c0c1401114a0f400802500c510014024001c21166410f0022555030192038001805001c902c2c00 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 825187356 1250 825186106 825186121
    0xe0f0c100504030b010e060d0606180c080c0702040c140a092c061003111206011e0804060c0504120b011a04080309060c28210e0d060b030d05091c050303 67
    0xf031031f0455001800000303105800c1d120601107501a0344400840710803c0300080c0c2c000303194090300e50312507000c3c01c0c520b0803807510805d403a160348214a030003071042c1d035501d1104281031b01604891030800b80144a44c3c2e210704494001424880c003501444920a1074400a02420651162803200701c0a050504281e1515110305000c2c0c1d401c00158050240354940f8440c0c00300b52002c0c0040c145012102c24283e01604240001400560191490b40100f00004000306690b50b0050012a00658000d20000c0c1c00c01025804581c1405240c102c282d80020f0b07c500345082c84030420358a4161040ca10328101c4241721801a102584114410410b00c0e0304140801515868040302070612000f04005172461030403114094268120034141d46401250065242e1081c0700004c1b401e54480140c100c2c4a01c00030094410103440901401c003428880d0315989081d4003000440d40100c030004002030101e51002001a201030560307000350070118042c1444c01a807419846112104003145074011002e1451034450b0340 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 825188606 1250 825187356 825187379
    0x50a061211060d110d050a0e1e0a1509050c09090c040b0a090204080d02010b04090c050f01021f1a19060c060e0a0b1e06031207060e0f0c100504030b01 66
    0x40c101540040d0610250304100030600070441500131500d0102c2d5100c0600d28540704440c0c2c05080e1100c3d080c80c01c80214043d0000244202a00c02602d402c4100b21085050b29450010039a0700109050803640201d0111855600010300181c03140d820b80e007070405105c082c000e1910049070200300f0344d40482246802c504141e031200a444501425480b40d454035414275400741d90003a840781c04664001e0300200341d010781c288100c0e025131801f02c0e424000481141c07141e4800c1c1545009491140d10301013400011a0700030040303e00e00703220207800002700300309010b003041c010006c0031740c220f0b003502c0d486a00d08181d1501010521a225069003c40c0a5a041c142c04403202d50b901c007001c540441d55054203856206040004d040c0136840348004807902c4c0780c0803010741d180030804402c14418565000521000d540c000c07500128a064038103a0a845010904048020f80b02082004040d4010000c0c0701584d802e000c251459003001c2a224804011140f40d001c842c0d42c42a480098988926800184444074014 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 825189856 1250 825188606 825188633
    0xc02010b04110a141b0309120c090c09060d050a0e0c0a1d0603070b04140f0405090a02091e0a06060e0306090d0315080607020a060e0c03070e09011d0303060301050a0612 74
    0x41322603505200340d00801501c00d1055030000f12507a84007064a07902880c06c40070610042d1106400380c074400b070105001c1078160502030075400400c10041480f11041d101c01c4280c0c1e07000504107009014030705083d80080c00400030048110501d0040341d10046490400c0700d10401100c1144003c0c241c03032110026103000e594009440c031540b50041440000f0f4007035a242c081d1010b44030351004649401915030400136021240b0400030b0045080c0001c1002503600404d01390803180d0140c0f140a041c0d13131010240503910306246058103208030620240620a040ca43c00f40099800c20348175540b2050824040554401d01120307a988546c3c415203840780640d1081c0c110740f13180c071511590030f44030b1074aa815541c28418100c9080005902002140c8140311a50003a0000004181e001c0e001c2080404042600d60b50710380150192044070030b000c00c0805400f580801c0c200182001c0400e10000300742c203c80d40300c0c3e2003960300e18480e608000120307860399400e00c07601003114818022500325800740d50300c03a02030b80e540 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 825191106 1250 825189856 825189887
    0xb0a060f0608150d050f0312070906020a02010c050718051b030c0421080309010e1002310806040506010608060108160c150608030417060603070308070503070203010f0c02010b04110a 80
    0x11503d0300001d041048000650380c0043d0155172a4458654800c40e408c50040c015010840c059404210527030300403510025541e02841c080e80c3c1c0d1502400d01c2e91800f07a20f03602901718049080007600300075116912032401903110714a1451034044551404c012804203590303403c2000d2080008002c0d1801088a0f5030040d032038107114049490180d00c91031201d8100312401c021994454a1040d605402808510420b20401000310b04000c000984800f01c03a0b008881031600918481c1c000e049030845c0010f05c0010300621084602a00e050b14000c2e40310a030a200c0c07000451728801c0400c03070b0356005003e501d200304503420f8104100000e48600b1102c946a0104c143d4141c01650221601d04075640075100180c0344803002156920302d0918003011f1201c02c1d601e41c00e2650042401d104442d5404682c503130890340c1101446440b040030f41080c0782075210701c03080203505600e403800c0c81e2080c000d1900840e404859a070002c10441c9003000900c01a58160381504452082c104020307800e8602601803060344088 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 825192356 1250 825191106 825191119
    0x406080f070806060715291f0315080f0706080c030f0c03060609040501032102071401111006060207050a08011515021908190923010c0f0b0a060f060815 67
    0x203500b401c007088495440ca00410201614064060035181184107044011f00f0348085040b10106441c0e0f291101000484004042d10389007914401004d00025a000c1e000c808181c640c90355041d954070381c0c0e0ba8182d00c52580411410000500d40345c01c41c0041ea0302c02c401d1140e143c4078903580c098140259910007405680c2c418000c0c00101d045403528810a40a07502c180d0480210004200192103c00b004007080b40440d07000030024426048034221a105100c070a00385003c00c0f83c0316031619800c04180d80d03500940d4902d06000001c4a60340040c00c8800c4032000c1c7c815000303d90f2201c0c4031509950f00031103014400382000004000c103208990502e0000ca02e5403040e41c2003076180b100d290280340c101c580142d80340c041c089005170380c40c0c103100ea91100300307211801c00c3c25a01d03187c082c090605681c0118941c3d154801c1201020580e4040c940c03074085140e202084056418052800041c103520964a614480d440d01402107020028624808151400c1d9160040d4569036603003898109411441b915420a2 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 825193606 1250 825192356 825192383
    0x10080d0c08160602030a06140f01020309150c060702010212010b0906070f06020d090f12090503060f070302040e09060a060b09030c0f03010b100503070e030a170a0e06040b0406080f0708060607 84
    0x15071034400355000707860003603000c07c13064a00038040311340107030300d071850b91203181140003a801c96a0004115440140103498486c03508901e0010034903240551744920301140643c130300300f19030302d03038194020801c400448081801e0b50b40c0390600150540200391943d50030090030400391001c21100744040b00d54512540000d450681c2d01b06401d8180c034403024084843c198103050300800c025800d4005000f4480d10302d044000d82c1c0c50600040c0d501e50019040c06040c10950005c108102c0c403035012a000f80112010f10f11243c207002042c65034500080b201490060700d0a00d000c580710701d600c011a24400e900600400500017000101304641021010490340b5640e03401a6000680b64041e104000040b2074440c1522072504030b401601c051070481005120350800a03c81002410540da100150030009030713240e07101c080301d080540302c400c00202c07069030020300898009159170f216001003080d04d08613a0f500c061521001d002e500044030640360701d00801d03a1030700080e4040c2044000340102c0c03409800f0390f40c01c2d80c = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 825194856 1250 825193606 825193613
    0x230f030118020f040b2407051c082a0a09080d0302120c0a0507060203130b1005040c0809190f0c0b0301090b180708090f060f10080d0c0816 61
    0x11aa0200351400801c02104a00c007507203400c0b00310588141c825603041c40710a80140004104404051400c110b20840c03002c1d00301c06850a4042da41340c154072000b260312106d03108100d08011244070180e1400240b40000007031000d441001051900091100f4500350000800c0c0389150580000100000b00440840e0000d40d002c810031131031600d41d02a80300180e4502101103149103640e40180121641d22080050041c0741c1c0c0c0c044121865207400c9440140c603503c40c082c010240002c200d8003c1d05d07440c0500305200341a11032008080444100321410000400414819a400d8100b141c42c4e04154100e030104103070614100c10014070140c4240700c80c400036040340d03442d5541d40415801c505402580400140202c64803481031080c007013021102900540380031921480050f0005068108000d1003c0100c1c0c030302c0800300188007040400e10182c03500ca140c90307070300701c50180001c0b50049030900e2440000281445c020174103080e078007075950310b02c48a24003075110792515030b00c10201d8011290350070140b04c010 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 825196106 1250 825194856 825194861
    0x18140c09010f050906030f060f060607061b3c03230105011404150e0310090602070210031b03021c020a0e030d1b140307080f0a0216230f0301 62
    0x280101500340c0842c40e0410061002460005003001e01940c0600744150680768005101a440140300002d00303480d0b42c801003c00c502e8065540020461801c6c03060008060612110305c42c0643e03041d075540e02c403c102c04218048040d80180c08406032000d1a2440c0c183d520400c0700e03030a1420311908020890703e8100700f502e21841f508203044402012808010301082d0b901044e4040d0a038240b1260500b032604003e0404c0c002d04d1034403940b405201c1c5120482c009500c081c028850b8528500c3c0082011075440d00b440c4020350701c9103104a200b940341c0000036202d24028815210b5a000ca81c004a00d03400034590150001d5101d03036102c60160030102c120851000c56030004186411080c1e50740c4241c20329003024945842c02108615061000040c501c03c001c01c07400543c2c0c6c00a5400c10304009110381003201d00da080d0301c81c480014100320800220f03a03050082d05401003128260176800c41f003000201c50f02170312021070320b0301030444640140441c100384500006030850400b8001000e11404424000002e0308 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 825197356 1250 825196106 825196109
    0x10912061d07080d0801060215060d03180801090b0108061e091c05360d03170a0b1801050d06270302100c08040f080703051c02130918140c0901 63
    0x580e80c005008070013210350080700341e40103081c1e500040100d0481a0f804120100e40100a40d020740c60500c03c1e481803510482a20741b80c0442c0080c03071400b031622000d0090203850108000d030341b420302240000500c3c1c1c0780090100d01c02c082060007240e1100000c0325111401001900c0c6092922070074100c500441046241480e47d82c009840b1242e40d00e000c000d11020b406c003100d034582004009180c81c0c865840500103d40150807040351140c140c000b841c0f44c140c0318042840c100b0b58449003010204080a0016800720320301103812645440700806203416183c40e21002d00542d600802c01c0c25104001130002d40004100310480310401000d0034001808940f86400c3c0c01c0c007500160701c9661a143e202c3c040b449502c2d00d030368481c075000e102d81c502902d44401d04240160000d210000c00541401494818026940321481c24155098042c2e4ac4c0c0c800540a03402c01455451900c1007102c2c0000c24420038801c0007a0340f20529610411403c82c3d4580401880a1040e07190040c040c10405401c1950752100150 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 825198606 1250 825197356 825197369
    0x21516080307020625083c060a12050c0d02060f030a0b010906020d09120606050604080a05120702130b1c06050901111e0c0304090c050304020906010912061d07 70
    0x166290152031124020144d8540c0300c1d0390920151200c05e55684104001c0d4001034040c0703d9500e0f008a000312503500b4815640380908070700c2000440381000c444a0580d4016a4100c0c0d400401c40e840c1c0310212904110a00b00070701d940d100002040b0581040b80700d8200b168002000207081000551103100a03910845074494156618440250350750780100301d000151103148018600c0300c42c003103c0902142c2c2580a4100c042468046507002c004c103d030081c80c05080050070b01c948450380c500741c0c40d03a54102280b08a4146c056a401903001c01c1a500540c0c034200c0d001031140c20344202520a41c0b00409450040035049403d800d40d00c044a03401c10340146070548500b00000c0c0390f14191240074210b414100641445401c200041050708420b901c080b0740b48034511140e2503072006081801071951140b03901c80706203941440020020f96801c100a50722550003510750603001d50303d403401159154201d00902018034a244040b40100b60140c0c854508000701c8140c1c514140278142006150400551082 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 825199856 1250 825198606 825198613
    0xa110a1101060e01031a01080d05040504020f0d060312141206120c030105071205010e1512280302010507030507090902070302190c05130e071a0913050901150302151608030702 77
    0x9418558280f0000e0780148862406000c004002a4008005215a100306c503c203580108002c0c00fc14104001c8818035101e10108000c136960b686800f010b030744418a40140402d646801104000280303404a603118030080042038010340d10340c010412402000505801c0512655403009100c0c0c8017445120700450b01c030b84030900200c65404a90301590070580061201022850600a0200c1f5445000b108000e04844103203440c06200046840c101d403041c2600d03480300104108100e1300c40c00c80b11846010340250700901440d5a890b80540564109540800000700102010880318403a0b40c06032009502c6803041c0d0b4090300d04100301e0001072007220020359076590950003c0100d443c02024510003820b001000303005d0001030007000303602e0b92031a21074528000c02c4130741001808400c10044862015000b41441802c205101030000141805c8480104940c6040300d244032618618a0b0032040300e50050200d1858020203400c4856900409460140d4940a072a548001582000a14411502e50b03004 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 825201106 1250 825199856 825199883
    0x309050609030d0e0c060a080916031208150901090e03130b0c070e0411090c1207020a030206060102071215061203050c1002033d09060302090a110a1101060e0103 71
    0x110f01110790455480140b90b22020304c203000c94a82800303a03100800541040451551040072444c104004078110001c0c82c40702b030302c0100420000031495195440d566881e411143d40f21840350500040404416a024441500401c1400140e4116809075400d000590f81011111707200052220010f401a00c0b2005000c5080f4440e09004c00000300102801a8940300c5030500342c03668442d00800c004124041c03003540e00003400b4203e60703400b102d40d00684541c2150083c5080000252180d1189004a00600900001c904290304c00901001520b050424105000c109035803000280414413100a98241d182e0300001a6410490260060140280ca485a035a19110402400c1491008001425501c18820300c80d00c500c00c01c00066a20241911019110b074940d0704030410308040001c8401200200c0c08086a20621900300c503049910942e00700c07942d6100e141050003503890002511070741140500104403420b200d2816050344070348103c00010241d1f03c4688000006609800940320748080101 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 825202356 1250 825201106 825201127
    0x6070f060b0f1806032401090f06030f0809030601080607050d09062d06050d082b05011409010815040b1005040f0506010e01090b0f0d02040506070606030203100c02070e0403030905060903 82
    0x14a048181e50403c1c11b004005850b15000d070440c811300690a1a51303a620115100381c1450b440b81015540000100b4608002458031018540c0003684c458003c1c003440d0000140300400090041c000c1ca8591145410302d019090320314000c0c1240c08040e10f14a40f40c0be00000e03052800100f80c0c1d90001802505c59600561426001c00e4500c00da200c68002c031035012000c07010820305005e5880b07201002100030685004610300c0246001241045644280791000000d2810303d00030001e81c01d68026251212141e90b5454143d0316002c11000c803410810149000400042402825a50003503800404a44207902da001140864844002c8409056503460038400caa40e00a040501d5078102442d100b07070324134203006d80c101c0e0a0050001c821541c2101055405074041107405450141c103000d41500e849052070b04040c00a498584000c1e4003030b014405145070b47c24142c1c0101d202040e210b80040c18014502076220f582104014829000c0560b01d2017840009241480111b002d0a40c903401941c031192080c8 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 825203606 1250 825202356 825202363
    0xa0c1110080603071d0103080a0e031b0a050105090d02060a11010905034b0c1b0118120209040213020a030912031e0908090909030304030e06070f060b0f180603 70
    0x200201d490038110030b00c022001e1a541019415603038008c0040f900e68100800c00e4801000600311150705000b5003d40b0703410071a010004610f4020100c13602c01e405561398006403454880c129000d0303000305001c50041c02500388040201055882483c045030f00c017043c07540b07990854541c1601164142c00c00250401c01340d50034070301c01b9407400c007000c1e10000d06492050181a20340915210300c10b9003103042c0395844405c600b4010f0b504120501801e5a07510250034440c0121400c020060a020460045149650440d400c00c074a040d00d6480c3c00007078268110b80c0800280050040040b0303405035500c9131092540105001900040c0110f481c0404d0a20700c40c5814000c603203c000240c2c0800d49820f00c03504490400c0030341d424404560400001c1c0c0f003011814610150300c103911844e6004080300301400314402000000350322441c040e03900c0e030b004110104100402885a103a01424200144495401003406540840303802e003802419540700c542e4803008903c0104080c0c09610b00072000800700601400d052 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 825204856 1250 825203606 825203609
    0x50406060906151808070803121501051b030417010504060b0312070f110402040f0e13030504090506010c021c0302240117030d06090f0b010f02030a0c111008060307 72
    0x80e03000e021060400107000708403c440e00c1c2940c01c0041e51134182c60401c1605010302e000d854080266010b654a413a402542c0758018041d8140501540300050007040701c50b00290100a416075800b403419110030030b007501d86611200d40200c140410400003821070b407500803071a0741d50401c07000855140307024249502294a03458a140c060b402910041d03140001001c22942e10315403141502c041420341d4200480941c56203c0b90355040761002801094514240003284111b98444464114540d07440514081542c1300d01401000714000340b006100f420915000aa84000c040c90303c50003000325900000c80902d125800b0b58209400110504249503040c024107545034440900d45070a121100800b1030000c6051050264640d440c00c009200044144100c0743c0d8000d2000c42400307410340710381c00759004056105600d43e00a1600d0030402d02c5d9405135001c032901c900706801460038000b17604400d41c0d20f42d01070702e011110310706441d80310801035880c600380b110081c5065440000b50b01d420f900341807824985 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 825206106 1250 825204856 825204869
    0x70225091506180612231e090a0201020601061b0c030303020a0e010305010312051606090501050105090609040528060501080c01031401140d06320c0412021c0803070305040606 77
    0x200d0f081c0603480d00030100040d01d42002400140100b082d01008082c4c3c1c100305c85d0a00148180010b2011442d00d0031030b140d040c50715102d5942c0c503c0d1980d2401031303682c400c0c0000c001e01680003000100b2211780549449a60406401582c8045184c19540d800c3d442e5a1501308a0120f80d0200e00481c40981c80400c1c906460400c0c2010422941192280d40d40841442100300030840001000d034224580441700503680c80d8000030a020000071842c090b806800240100c90140003448000782580ca802d403951801030390480c2c00341030341c03081d00d03004803542d0000c6510034811071541414103c00030748144502c03030003040c4c810060600a8940c3c0001403d42d00b84400e540020803403c00107000d036803100000071806102c1140c40400175045031620901070700176503c0340c86100c00c003c440700200a40c2d003045603d0004112205c1150390380c40d2411092a8096806602100f0300e43c0e020110041c00e05940003c5810440b19040f100d5440603a10450150b004031102c000081d210300a020800c40c0078090100604030 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 825207356 1250 825206106 825206147
    0xe030a03060306052206272d0f0609020111030406050c0709060513050613020a0c06050603071a1b0105012d0e06041a060a050a1205070225091506 64
    0x1201e40c500b03d200c02d040140525a0720301003480e140143c0031b20403000064181c05075086030f0050410071100023000b54410950004a0905051902255401c0c41e984c3c1e40310f00c0c548035619079034481c00c2c01480000d5049044c410b140c1590b280c84801000a40020001540c81d030b6600c0001c001910705103c4643e008100b40381c1014410f0159688003000d030502e10881103000203542c0e540500055a1071005d007001c0c9949480082c42405180e4401084c88003280184d8040c003168444005060740d8181030b110700a105910385c44403040a55900008000300f091403840451440800500c2c0c9084075002c1c2d00c00300700804110031186034480d10860000d041c4401d42c504007002071900c1254002000010066071007a0740e1044c400c0e900365055500c44d1036030103000d030190b5120060380030080d045500c4a0b0901e03021484020303604420103110300410b40704000a0b03000d0240c0054503807090120030305544c8600075440f0001004540780625101c4e588241d05c80000b404180340c0340110203841e070740b04408114002003 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 825208606 1250 825207356 825207391
    0x2d03060a0221010b1c0b04110a1824030b03030307080f01090626030706090c1a03010305070303110a240e0d3f020d0b031f0f0e030a0306030605 63
    0x5040400d8a0403400b0000a40c3c0e40d03200c45d801c3e00e10050000044c0540d10600d4802d002d40c031841004050885034200391101c46110341540710b0302c85113900503c41c008403000d042040403030390b0034002d10351400a4030509002c541e60644034002403d5400c00c64103600015120390410043d01b0361144140c0c0104490361042000380c0c00d000e0840944034001c003010320101c0500342000c0c100741040040303445003500040b04101d08080303864a2aa0700307109201d482218a40554002030400702d4108a074100e81c1d0110080611620f1581c06840c1001580300c440003501510342010b0120303039400724040041060b410f8400e9000e00600070102102e02d61010032585500408010030000d0700191402c3c055484e003100d07030780b06c1d841f802640704071340503640310700d0541880745050f00108207440d030007a220715003030840280500c00500043c95035440030b00c1d0056508040001d0102107460b01d035400340b4555072802d00c000c11012000f001c290325607400b52451100281c1e540c01c0800611890b4421303184c01c098003440038a00e00 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 825209856 1250 825208606 825208619
    0x705060703090501350601020105070306050109090b0415030503192f010204080304090204030507050316121505010e0609010509060303123c07020105062d03060a022101 74
    0x40800d0080d24184800e0b0703010100c1e03410020144160245e4854159644550520304002d8142410345886000d0341c02c1c5000b01344154028011542640c0040e07440102091400e0311050103480504100c42d0840c0e41d03842c203448110300742c180b00805180140300075961241003041003441c1240b440251000c101c1c0f490320440180901c001d4400100e0f01c0c02940750120ba024044041c0244150b5000e940c0902c000a400a01e980c051707005081100d001c1d4080e9004d465407a0240340d01d0301c0010113400c9003004010414020304004000120440e401100e5068012441c10100070447d00280c01a14804071020304125040c0350411a1038050321040d40d40c547e203030519a0110340d6074040c1a0881382106034920004024a21000004240c1a6090491450311001c2d550030301c598030032109910304038000140003559041c01401820702031300014041107615451040003210941481c6100b141d01c0034980d45190240c1c0d410840180918962240140d03103500030f0111010441594141d0f03440b48c9580b80040040 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 825211106 1250 825209856 825209867
    0x206060a0b0906090f03072c010f1a04030506040303270b07030c0e0a0b0406080907051014090d0b160e0d020d141f140613020f0409060311030705060703 67
    0x42c0c00c020307038020381c40784600400598401e4520007010b402d845103601c00180c501c901c0140c1810300c541414060f0303640c1d00c49010112840000d014422030300c144031004100d101e40c002c030490040c1e851013107858181034580d56040d0825106a0741500002c0c0c40700d03010500341004071803e03002520418160044121540c0d40d4211149000b40a00700389a42d0f007400c424401d0141d01080c100c800300030701410307105440e40006030b016007250040000040c0b003d00050901c00380061100c3c01e07500014800c10300032031131403001c9490589511811250020a011000041c1c6820f8440e0b83c4d654462100d401403407074031b02e1a55051010000d03d03241044480d0403c5080750300c98100202911f43c064071842691041c60508000700040c0303200300891482041d441c4e091030f41036503051401c82d2450903020700c081d00261001c00c12000701600c2241e400300c0c2c201110380c0d2b0700c46d5690060550400380602d00782016a41d40002007103810641c4140d0701c80075211098071144c601885000d024080c21036400781005040d480051a = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 825212356 1250 825211106 825211117
    0x140a0c0212030601090b30100302130e060709090c0302090105030118111204061b0e010807020f030d06090b0102061003080705150a0c02120901170604020d0e0a030206060a0b 76
    0x102044000003044960b485a0317042400707810480180e65a8243c5001e44403401081c0040d1508940418000c901040701c0c0504010702908024940022180c02d50b0204103005140042c480350050780e4009c0f2002091f018040644210800c3d180e6045161800c030790b020a6500d1031214908262041003101900c0ea004000d0300c0c191a940c84403078585060700350700200101a070020300c0110031008030f042e074240c6207240540ca10480c1305031001c0c08048000c881d251201402e000c0b21a002c80c800310700620700da5109440c055805669841101c1c0c00c2e0318a18142811603102118461902d9102c020074400c400490090750041e4000b071008040600d80114074031030b0000c42d030200500d07410340054120207201c010400c552414907c18203800c0e060501c50780c520000c085900c00000507003da000d0710741c00010100159941080d043c0c54851103e481c05004046c0020010301695100d1760912401d003030031049103c1d144034480c00000074494403102d803d001c1c1c50840d004003540e21500d90f07004144143e6204009881 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 825213606 1250 825212356 825212383
    0x61d060301180f09080c1f1103040308040c090c0215090705010507020d0f15381c0503130e0906150d051e01020d0c030e03030424020409140a0c02 64
    0x243c010810080003003c0d1004d10000352181801042c01b0400c91700100e080040d5040c035440710003455840c0d100c640d084c2d4400c90343c454003030310081c400280400d0081b103c956010b03203d01002042181c4900e00720b03043764050800c000059200d40217185503d12030b140680d03000180d55004004952a14000a2042c071510304002c0c01001e40c21400400c02540510407111190300403000c89000300340454040003054040140301d070812260301d070300020b04c0340c07858401d00711a20000d4100c0e0010422060198180101306000206a0030410760404103030180043c04004011502c55180c00c0c0c90041d03115685400500a620345410802c01d0040504036403d429120700d03000d580380210740d80c590506038180a0b007d501405080d01304545468080710641c0140344c4c4070f500c080304104982903040300300c04490361001400150340c41000401d000c00c803680c2c400600c3c1109031180c4040c00c48080e94400c183d03006035008420b0152922803c250720071140e90f8169218001c10000c0182a46500000756204030340503862 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 825214856 1250 825213606 825213611
    0x30b101d0f0a060f022a010306050919110903010908090906090c19050c0609010f29060318030d06050103110f0d051f140a05010e09010e060301020d06061d06030118 72
    0x14002d40e0080c0140800c0b4881210032a408910301b05010800050410b003d41c0024030f4004081a5840d150401602030100850300c0403000741d03031028100c003c2401500c540302100050101032a2558240981c2c15490300c02c414868032a51a00e062014a1401801c07080c0300341107000030400e002d21a1020b94228840c0c41a090380340d800080009e4950740304e038200704540c2d80120b000300480003105401400c18500300710010041075420401c0401019004004101070b031410903010480b45c07804401440e0020142d40c1d085469039094041d061540c0e00c81c130005034185442e103104000a40e0180b190b98000c14503141c14620782005040e6002c0c1c2c0b88120141c1070310456544011030b4150540320b00c1c00000c24842c50300055002c3d1100c3d41076200b006011066403059070703c0f440100b040d502c40d40c4402c1905201920343e42440e4200a848801e62030000e01d07064043d9801e011a0020b4103d5000308802000d0715210485c40300e08124070b987c035000c000680301d405500208010040080d84211550030342882d036400 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 825216106 1250 825214856 825214877
    0x5010f030c030b0a081e01020408030906090a0803070b04051b090402090a0605510c010b04050c040e070c1e05070b0f03071e0207120201030b101d0f0a06 67
    0x54008003c000b02458000300f8414021485060005101ca0714018241e1240072009000003214280d1190f8054900da9800601c40741c089800c2c040701604178098020610300016448400103072540c0c02000096a0340d600300420b200071b000301480f500030818503c21002c140c0b00c040001180b031416000c0c00082c01181484002010500168042c3c1c0141c000207200c41c0821192403ca00f4407000c0110040003854100344d44034004501241c44440f81310400c80d0304000c480da24420480040d044901d180c1c249549891100355513075510722071103100310800007406442e5802c0004810072020000c105405001034030401101040c8000f509481240001072411400459440c01038200540ca0b8000c082c804004180c24000702c108101841c81307a003050741c4091140e14150203003000c9030741c28802d01001da0031221302400440852903101048a006040100c0e451000e603011510380142c5d0402c0fa00010004d03001c14040c000d00412501c10f071030701105c402080c0d003601c03400507581c10b10610419080c072440b504c1 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 825217356 1250 825216106 825216131
    0x7020105180303130b1e01031b0509011404110c0703080a1119060507170c03040204050c1903020f1b0703050105072c01021203040f1a070503130c05030f070302180105010f03 76
    0x4d0070168a00107000c2509948d4911b081032002c4041c0c4c815213688080d5440c081281c2c2418014641241c010400c41700080101c03c05000040c00000c400c49140b2030300f00800e00e04c07981c08000d1280110300c01d074486a0f4405a4901c02044200355600c49051504210041421341740c0d00c1c10f403082d080c0e401500028841e1a048401d507902006019846600d00141040004e06015080a903102e14026203003445259207000042000d8445c10306c0002000765001c0c0410503540c0709a010300882d000000c00c00e49804016a2000000d4280e0382c580850356001c4c0a0500400ca001c1c054150800101d0400c0100b0841c42c0b602c44080c410208c91140a2404020106525038400c00c6003840b542802c4080940d00c1c05c0c1410705011101c00c010040e121520107180c45141c03c0d48001043d8400d150390764130641141c5842d404d500c0d070308d008000e00340c0e0340d2440c10030081100e9a050210a01c500103d20080259a146105001380010b480489070806500c50b0010811a45c201e680c10081035442e1500040b0240e1416 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 825218606 1250 825217356 825217381
    0x50f06010807030c180b04140402032211130504140105090c010c020a0b04080703200d0b060a0e01150207080109110105030a090c03031d040506010e0105070c080607020105180303130b 80
    0x1030f01500d21744040c40c00901000003900a00c20b0325100461007402c50280024001a88010341c0e8030001ca8901c5a903404c05200ca200029005900c10941c0d45c0181d04100300040000d43c6441032200c2b01551001400f00304002e082101014040200081c405450310704121501c4020b940055410b002c1200d01d080d0071540c0e001c01c9034014200841c8425211511450010f55a140c1e0703010454403c028a0b000d0340c0c588140e4220000d240e9001000a07901c000303c2d50311405c0200700544020f0b080032021601182404641032558041c2441c040a4150a810060000c0c034001e00c0b42d00100c4664508031071003020440c0b06581e8402c0603001e08125640f9268580c03810300900d202e22028050a444002c04000c01d98822950703209030080031041d50b41b40d070f845820401110400d40724640400c881403c000740715401a000b50480038060620b140d40386640c4e0341074909040c0c08a4503080140d540701c042060300010544048541d61180000b141036103402065055860355400000d400900c101d00014140d007141d8 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 825219856 1250 825218606 825218627
    0x105150f040801090c0b0702060714010b120f071a0a20010906090c0b09091611030c06070f080403230f210604020a0e0f06220504050f06010807030c 65
    0x15018569281c0c2d07141c899074020030080c00200c5000098150014406824006640000b81c00a180350300e021f0495403641da104c3c8d00c0c2d44e003400055403182a000050307610034440805003180700f8050002101c0d96040c190400e141c40d085520311038641200351007550805802e0700c90950707040c1011040c4042100000c5071980d6000c10301800d542c28010b44004000c00c4d038100c005100e00c68204249801c2e245c04402e002030080d403820541200e110310001341040c030f410080f441101010308104583c42e00c101951400e6a202103241141980203009202145138410b800d050113150602c0c0219036402c143d80e00910107501c5180c002965000401d40100d0500041e00b2144104a0154002da80d20709a101582e120400d4191000d1540d482000041160405008650014265980d2518040100e500704012950f1706007626402103024003035800509150304481040060f018040a0000d26000420041d198003c1c44e520200c4240003d100f001d9810960781600310b0510300f0302056003110007008031051001c2 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 825221106 1250 825219856 825219877
    0xd1a030a031d060301031109070302090d0807110315012304020d0b010917030f071a040312050903180105091f0507060b030f0a03080a090f0308090f01090209010515 72
    0x600c00c0100816400800704400103405100100840400b001040b580c0c0c0800d00c4045e01c40d8414441d624254900680c8803a403041042c02c00505090300c2d240840d11440343c0b030004a461110000c4c004060011200700101200c40441c0144031019100041202011046c4101410342c5107503100001c3c200d0000c45162500c07000500115124138414070302c60702078910400c00034081060b0910106008190340307032440401da01750b8003c629000c04c000782100d00e035100c0b42043c0d805c2d00021940410b1384841c50500e9004034026580c02c10815400e656200c1110706c060400780d40b56008115a0003140e84d0031200d15058042420000d8a80c1259000304031300440c034507040c4185400001c0582d40a5400101030181031f4040c01d400c20401104606141c0c1d608044c001414407a400781ba190000030307100c0e110540e4003001404010a0802803130759461014120042c045000c1001d10b02000a8003400300040001010341000a100d8000260042182031a040c001c1e9805529480c0e80e030251000c400c2d00700e8045514 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 825222356 1250 825221106 825221113
    0x903060a022802060115120e01020301031703010305150408090d05010617150c16200108060907091e0806130209070203030702071e05040f0608210d1a03 67
    0x340025140025486032032009003508034010380700900801e8144684140c1519001400d00780d003816481c0652100c41a1440c0400141116020780746030345029004140d00f405001580ba5410f618000f920187e1070000c080012a06000410109100117401552080d00256107915501c031401e20301040c1c410007030010b81040401512008000e81540140200d0342c100c0545201100f0810883e5111007400b00e00c134203e1040403000c146401e400100401c80341c0100c0c541c2c003104000c82e5442c0031020b40201c104c07050040c1009523040c0390f035801c41000da0f800401181c0f656420302d00344001525600302c41c00386030390300ea0340750485000e680040701c0b0702006800b5010483c0c540c1e00e4010001001e002080c00100c2c000c5040c1c0c408103446c24000801d0ba030007410580c0290941500705030404034000240080049104058400095a0341340d5100390381c842c40461401143d101c2c103121403d844d01c2c001c2100240354100703520340010a00a00c41c02c2d18540c2803119404680442100fa00308240140ca80c401c503170500 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 825223606 1250 825222356 825222361
    0x6010c0f15090f0b060f0415050405060109080f030306040c0c03120b060c010e0715110618100f0c0215073018030e090103020a060f02070b0315010207050301060302010c1502090306 79
    0x84d002001031140b80f01700c07240d490040760740c418841520000310a1401c070003810304050105e0319050304229032050040c07410046a59940f03100038a4480c0e40f40020748143c00000c00d00003141014000d00484100f28100b4520200d840d9a0082180030103d103800070f030725a175041046090761207104450391040244000d100900039600e2960b1030b180a4411316541035020b040d44024a0701480c45108100120006401595211001201103006007101300c68140200ba200c8540021300e445200311381c2c0c117030f1000007541c1280ca500c00391619121262003024440e0300313420003428907805420386006000c8103e290b1030340c0741e103154071007151003200700380041007802c5c940100082d598109042410314004c2e503846a00710300100a10030480b0080c00042c4d04003140000c02d2000ea030060a20480c0140c6034412a0020341d62600580840d03082551018150b452181200f40e1560741046800e0185c58110020030000345150f0019140d40640b09006218025025000a00c080c0b1507060780d0341017002070282c0329180b = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 825224856 1250 825223606 825223613
    0x602220f050325050d050c13090506072318060705030a0801091a28081c09080c01140c07121a1e090a080714010506010c0f15090f 57
    0x40c9124000e0324000d00c9482a4003000aa41c4080c840fa03c1007500b0404105508107801d008407020300b0401036074144200901e04481b034a030004101650403680c1030004000949207402820414090040410002884160410494400c0307508080c14070440d051540ea41800b1074280300300c28000d03285c0ba48040c01243c0d0805000c8080010205082e1a40c0c3d91001031780c8601c4a8000c5a4080030940d040d0743d148100c1e5034aa040140c21040c00c4d00c80c1170454185000c001e50340e1042c024050308a1070040e0448155402c2c0000da540703602c2a07a00b00ca003024540c41b814100b2969a8810300001c0030304104900100214000201d01110f51003980c0605a03403660b0b450303803210101047d0b21141200c628145a40b4407549003000e01880707026104820b0305a840400d01d10705145503840c05072581d81c40340038182c1c4400015450348024400613206030300e00317414a01c0400c10f40b82101d000801da40d050002485078000001c00490fa03403510241d12841e4500c1c5480007950840083c01145401841860622a640d043c13 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 825226106 1250 825224856 825224879
    0x130c0c06150509090703050a081e03090d031508192301090c060e01050901210e06061c0f06091502070501020c010e01021312050a1a070801060c0c03060222 68
    0x2502e100751011101501e4a80005a4505003448080c00507007000c0000300c0000c14050081c20004649440c4000405134040c002c6095407003641c0ca580310740e101071001005960540210440c0d542100000c40510703180003e2607448501c590b80e030340000604082c0380402c1110565418405d43c401d500400c81c0d1a103075000841c007c06049500b510900f07691500050410312074900700c4010b1a0681d602070500d041d540041d1024a42c40c851000d00622451518031010200e220314404840040010011420003c060001c8100100c4400d0783d68500e007410040840d01c0c00080d8803d9591020000070f1280e1a82042c10048094460140d070b0140001400824400150090a12a0082c4008008485011412501700d1107a107510f40c0e00c8041400081050048841091312000d0140c029070300c24a00966802c050303041039111129104a40b00148464240d001820a000d01070504100e01c0155940d1107001c1c2102141c030009101035000201c0c500c01001f4454500008030b000c40c0444502501d03600840e11 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 825227356 1250 825226106 825226109
    0xd080a091809150b1201050705070c14030c100c020a320109090c050f0a0302030f0112020102190f0506040b1902071e0215030a0c09060203030402130c0c0615 69
    0x240c080c07105504841d40c6215500725294000240300c0320340d0400200c00042c040310244c0c982e20280300c07a60148199402e0080070f22a100d65580d080c0c0e02c00351403501800e1554039402c039421440105038004401d8030005052000c110003111007100d00184400101ea00210400009402199461f0002440c406101307414110030015010920300001d12049074850030020741a1600040c1e07000d000700149a070503446010044068540246445003144600707000e98000710a900000b60300200b0802800c0c9108030603400342c807444003038025400340c5d600003e685254000c40d152921061511010400c40001255180c0c954044182c51781480e041c11308000d540c00441d052083d8240002d902181039040f4422130b5002540440c0c05040d80c40049410101904103d130304a0f00540b014120900d0440400c018500c038904040c2d004c505125445070082429001e80d001c403065520500c188001039880003001c4c030b200c6050013000202c425491104850101844901520380e51802a1580c0e5518004d1440d40 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 825228606 1250 825227356 825227369
    0x706091b0603230f04020609061210080706050f07080306120d0806030606010903051f021b07031a010302090402091b0a0507141225021e03010c0503010b070f020d080a09 74
    0xb584a40f5036803141a484004540c00071411829034000b60040c90000302801660070060700c460308100d20050103000802064882201c501c050942c02c200710181000614094042d514206041140ca400c4860b00c500442500030141d000c0400000d001e621100403003900080d05c082101c910340e100b4207024000d00d0007981e080d4020b0090300009149940103542c03076000c0300c0c4d000d4000d24503407a5144000f0906800418015aa29020080f220f1404103540c3d0031902188402d015001c03031880c52601549031271303032058020208564000100090790b24500c82c9540b1540550b40c400030341d0b0380c90601580c0d245800c01c0440700800040355040c0345551210207000094031820a900480070300d6042c003960b44042c1140821070302400c1004808502031120000c40c4000c07000c0c04050340d1089a80080c524200c043c0c0d160381d04ca1001e501449452409009501d0070072460308009117994100110032203144119500070f0a00d140894a40003151580641051013a41107695680c840760000340080000071944140c8 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 825229856 1250 825228606 825228641
    0x1c02010905030d0e040905070510120f180303020c0f2406041109060c1c05070b060f010203091225060f020f0309040c180902130902040b0706091b0603 66
    0x440d0798100010324030243c0040381c4964480040300d20030070000c0c10901c0c2d000c81d000c2c02006000a8680c40b00841c0300b21707078105030700c407260803041101d0118112800b0254000e079113410029036541d2004003180d4103154a13090314002da916140c0070742e19480c2c03e040280c88005849041e82c02100100d0300c0034411110860b2520782a41c64403044c08000944400f1000041c510504122045d243e00c1c00d4402011201110b00a8500165042c10228440e040440494000c110002000c20030840d88403402c0d0b078001380413550801c00300c041000003583c034010744080a006140d01141d50103802010800306000049103c9942074084000c4a21000580340b8070a940100301840c01d14900d483c0003107280390364801024019030a00c444101080083c00500b2507a40a114417141003061100d01640e81c08054110010301581c0c1c3e80c001c184110420a050f400745800d0340c07041c0024040c2d0b00241c1d0841d8440358010802180c01103540c01c09200f08600109a1840d80c060300030f00084580d0140c0014808902882c2ca0 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 825231106 1250 825229856 825229859
    0x6120c0302090f06160606240f0e13020409020d1b080103152c0115050d020607140102090310060e0106110c0915040905011e020c060c07030c021c020109 67
    0x5500342c0c0904030749150f1020003140b0801e024100b10000c0c00b1120540c0111394190107640d116101295a10f0300400018800caa01441125400202502000f0070344d290205581c182c07100000c00740346454003020710038407075078104011079030003901550040c0c5207403281156242040e85820340140141d526081041000c0340c0420305017401070103217078100e1340c0144c1041d04070305c4064154401000000e01d6000100441c4031160914450600300c0c0490004040c00042c5440d4081030909105280d42c3c009071180e6110600c640058843c1c60696141543c00f807544040d84400310f9810b40a80a5005125058800c0b49074103401402c8a40160080b951485091142641c07181d0381164099144003401005901071003120450303051100465601107000742c0341c92410180040050140d49811a007554242e4407003040c0745c0c42c012201024418006880d0301103151413604804151120b600405800f61600d01203040400e240c001e03070741d1010072030b4010140c6210001b03140242d201a80d4103142a40007030741c103450 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 825232356 1250 825231106 825231131
    0xd11041b0507020436021504120b010905091b04141e090a020607350403030e270705070c150210140c07030309080705010e060708040308010605071b0612 67
    0xd03c0c3c5905440c081703500d0180d20940c2190312101000b0001242c00401c240718a5007484102c202900241070700a43c1005180c02d6820010190001071300402c11840c606400d100c4a52000640d00c02e03024107580340580034410740c0340018006c089600401c06030b0062a010840101c501d101c440c8410309211051000c00d44442086540e03a0003020402034102c442008280e000c2604003454981d0700c04891480060450980f074040701482c02817030841d4130300d0400700cac082c000c0582005210311800400d032400e4002e03050420701d540004000c04e601e020210110008076403154854011561000d400209000c0a9035540420200215900300c03840c005018900f0700c4c9101114034021585102d006254a0500d80c45034111100d050b4480c2d40100d0905039034034900c90024541c40302400c59a4000c3c070002a40d0b401e48203920b401d1240c0142000100304480d41048002900070080e42e040d500d09190140d03e0303c00c94039104d1070504003042c0c0910a00421074000070020703400119010880301d114014030030fa100948 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 825233606 1250 825232356 825232391
    0x204110c1908040902031503010f1505040b1c0825020906011b03031d0f0601090b01140a1d0916110f03041403031908010609050d020d11041b05070204 66
    0x100010300c0c00000b08000c001e5209139402440d040810000041c209440c914006403c4807136801000000c07a480d020b07404150012400008010403003600c041c8600c019038070002e4058440a4003588052005181d0f1009001e04442605d55100040142001c2c04500c0b00d20282c0200360b00d00d0032842404030b400060110b503c11164091b00801d00401590800c5056906401800ca2600034080814400d0281e1587c000100000003140c00c00740c002d00b0403035040010101c1075a000a0000d41406031f4020070076002007400b800c81e1b4000e02585881580c40d2100d1180c0e4a50b84038203003130250301c90300403400d000b52004a0007224610300c4403178489510b05540107000c180c0300d101d9064055001d800c2030104002050114524020b0b401005042c0ca00d81900c80c0302c040203c54810f01448000303515400148501d5400102000285c071045403c0b04094480384d000030025402300c44000e0807a010100e1140003034489800050600a400703024444601e01140c000b07100360059003003a4400d509018609a290460f107 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 825234856 1250 825233606 825233653
    0x3150409050a030c03110a03030912020307120e031005090c130c09091d060103030503070206011a040603090f02270f0106020d0c0302120415020f0705010f0e04090204110c 75
    0x11000d0302c4210303030b0380d2416540e03a00d60b91000c2d018001d20024050719100c1c10700412050b98480d440c001207100440c10700990040d0011580025544104107210219080031504500d541071450441c101c0c44c81e07c40403030b04101c10400402482410a000d001034404082b4b62000501c60658804285240005050b0255030b5108502c501084100c0d00502801080d600250702401c1c02d8868940e80740c031045243c41c0707000070036401074001a00c0801884802ca905000e664018a465003010401c84114440c20429104038483e19082c07540e030b52512800c04c41c088211104003038000b050802c61224104104041b125080001c0c3c1342074024070000384107001c500c02018143c41981d401003160089030b920944060751140416019845408200400e620704603005001801041518194101c610000a440e10904503912200340c0c0107a441440940d80c02140000800f20501c0e00912801c0c070740c000b1400410003000c02030b400a041c80201700380394140d00010903ea419803c220ba0700d414548110080740c00c1c80b03 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 825236106 1250 825234856 825234863
    0x21c0b041118040207140c090c090a090209010e0a03030201050709170d0507030c050316120521060f03010e0d081e07050a1707090609080d0507060c03150b03150409 72
    0x90100e5403089003030341601d080e01c00003e0401450844507854002540318219407104880d0f0040d48241003d0600200d803035003280e03c0304402c0d4104454400081d061082900414003840d6010070005d0590f072142c5005c0d400305002601d03081c0005e8403814024040c00d02154200d0100740f8401000541400c0032100080605003100600164031400c2c6045510b40e020003000d0341003060740c2405901240060005000300144000060001c207100d240000c1c00c03050080030001808014085180981001640318800711318203401d15545941d400001203503103031380e05c401d00d0f0103629017005100c00f03080001304007903031840a84864805590740010444415114072683d088e03840c0c12800314404601510142285001c1810090034100000344000b95110b42111201c00041074442d040000903040f440074805032070018003401d0071898010b4080c1041c801d582c8020a51390340c44110403030691217a03008210648108007000380c101e80e5030668032803541040d581600741b101c000c01005114546441400d040550 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 825237356 1250 825236106 825236141
    0x3141807081908070f0206030114010e12031204020114121f051302070303020702180402040c09230303070507080610140d0318030c091a0307030f150b04021c0b04 71
    0x3103640c480003d600041c10031035034050020041001690b4075006540038000590308074083c0340309040010902a00300288a010311410020000e2500b004022038004a00600b01c01800761206e10040394880a95680e1500d400004181050f0380c03409820144e005c0c0b2030010f0142079812001c0c400074a010454442d60303605c00500b03c11940305110a801910016011703003001814030016401213803800708501c1c0050b440d515001d00f08821490305106030201c41c40c2500c3d1034680c40381000341b441400d141103556603030348c2e40040c46030880ea6607080084900c1b440e400410380c1c00d01c41d40c0350b182c5aa900c0040ea650180111610008100040c40d007006e000b00d180004d107203402c0e440003900c0980d5a40540310603030482003100d1201101185900710914020a84407000050310926410500030032402301c24613030b04c280c1029208101060303007402c2c140d502580107140740c004441c06100c0c140052034a810b9140d0440d0001c50301c200c500d8035032120303e40d00a003600000c0c0000103c03901000f007150140d0319554580315 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 825238606 1250 825237356 825237403
    0x140306010b0a08190f0f0f090c091d010c02010b030d020a051209061306050a0908031206010311040806130c06021c030e01150b090406050109060c02010309030314180708 74
    0x5201d05450f40d04094016070504a9030a0b840103081900d080040640c0e8071515075111070170b0101c40b0310030384c0d0118803024020031207511207580d0300910051900c190307549541c440d800c0044d00d10640c0c6030b506001c0542d2008110f102000d820180c040c01003024018420b01036415040807043c00890790703261070350f4020003400136070440d20601d941a4001d440da294100e04203100e2080e92a10130503210004c0d110035180c1a484100c100070060040f0125001282190028031410641090145160380c00010900b40803900c0300703010700c101840d80503592042c1d25a204440612003d804025140741180b400341c0500301441d5164041640e680850a003180d807612945603030100214843c3d070120010140750400410120520188603031041166080b904004a00191030071003441d1903c100001000282000c4403414940540034212070062a0041c0c181606c0e60070079810141f19500003081c03844548061042c03400c11a02c0b0044041030300060780e501d442841e50115241c41c00191245070040c50742c07450420b24 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 825239856 1250 825238606 825238627
    0xa02040908070f0b0a05070504031502031e070e101e121d0c040c081b07020d120804020103060906050f190b19030615140306120313140306010b 63
    0x10991a4029903081c941801800c0000301c0e10321000348154055400a281401e0a1310450b048443c0070740310505005080208000041100300a5083d003005050016201d5881e2501215000b0040240900c6555003208002500c0d070000c402c00382100056038101464140381d44280c07190311106c210f26401e0620605640d0100d0711894401442d078800000101d0880d00f0030354070003a0000040c40d845d0403508560036821950416101d9405c000e41c4924000c074450074030300d00c80d0342000c034991244c10091200149500035902d540e0002054540d000c04400c01e500c080d0f14004103102c005940c00c900107409c0190005403094a80901e00a40d10010481610050940100089512122055160740320580d00020782e0040b054050006140030704452018594032003002421a11107410101d4000b0004404156156100410b200b504803014110b07036494a840c1c00040c000c50541400c2c0c1c00501c000640c02602102411200c01201e030307280c11100314056a00101a00c4010900030640c0078401440b80e030403103 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 825241106 1250 825239856 825239861
    0x60b130c02031909030f1101030902090702150f0106081609120b04030809061014040f0e060702071a03060607030e0405010311030d09030b040b060d0c031a15030c041e020c0703230a0204 81
    0x7c814180091000300c1e41c0c0c045007007003404944050142c3c00240ea101e404411850783d01d036010000d08094070096042890240203428043c2c903a405844015602948403409840c0341e101420f40d01c182c1c88065605450715602251007220f0480002d01e02c00003103005140c0002c3c2084c0200c50320140e0032415810806000300080603112026409174481ba03213840d105003148a00d101e41950b003c003402c81c924100c60041e20f00102a401218015585540c4010303a900311815660030400481d0800c0e80c41c45036003400c80b520221058041d0340646414000000c20201c800c1101c1b1000c400d50030748140000100c030039215400c0d90310000c0c003c1961580002e0001d101c0420080d40420010440801d4900b03039110720780748180541040f10244001040b092090b584004115440b034910220708901d2004140420340f141007e04030f19018a448000c1111120740e52503102c522054401c00c21074592992030b19483c1d40d182603202c00d071418006000c00502d2000c10348822240c51628000820700300c61190b007400300 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 825242356 1250 825241106 825241133
    0x901050105090f15030402010e030d0e060706230919173006010315080d0809010b22050a0606170601020703120c0b010602060112060b130c02031909030f 67
    0xf841100e0718000700d9542c0c2c1d1300c0d50840200c0103c041d416124030301440003419420408000c1c0f0301c242c1c402119410b81c103910030848a0000003d0350020307200c00084c0f5042c00038040529990540340d48400c0020740b1404040c40e000d00c03807070590046900040840c41d8203104a44a460085e0011610941c041c3c41406103000400c0000484100c0d807211121515007020580411702c03100100c2000c9106001c460b40c5c0c50301600c1030308058448080c0000385030005003a5503009009415003070017110000a0035112003903220080218020b801c2d0034409040708480b40040e000318480c407641f40d107480b002c500001038501c61541614099103850044e84010b58a03004400c500414842c1188a40280480058a15903508800c000c0704d031949445e0860030714010303101d110160808003c42d808000100480189000380308013854107e03000050000e50200822100c003e561941c1600500f402c8820b180c96034000024100443c2c404010200101000d04c125070307071040c910014003080d40214040300441c152045448 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 825243606 1250 825242356 825242359
    0x303110c0a1a160b160e01140f091306060507110a0b030a05090c030d183c0f0b040e07170c090307030206072d02151c15080106050103180b0c0c060103060c030b0609090105010509 78
    0x100341c99001d2f0002c02c00c0c0d588540086000840218200040200c90390002e01c1c1c07040b08407110011030703081200c03034540d50000829403070340c081d243c50200780700180a0260b0340034000082d082e1082040380324400340c40258402001107151048070000130b94803220045030b40100b40c1a0200043c802d151028040318601c82400c103000c02c2c21105000140c00e000c5034a048000c12910742090744403450180f050400f94001041e820501003c054041510400f00a15551040107201c201d5200d03a002c0c0040b0b860110943c2000b50000700018014090200c00000300c3c8003641400050f4042400040c1003540d500c445480c000d4102038805211520008013078050100b200b0881c40e5080750700c55504844045c1c400340803442ca951003089406102c43c0310280282c1010b0042800c1c02c1c031100d0010382c48201030058400340501400c00402c00b0900c0340c8405c50071114651804c3d000c0310315958490610307400901c44400c9801c00310385001540b500c9801c1a10503100c00301e40041018540d81e10704401501d00d0341c0400310b01e6 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 825244856 1250 825243606 825243619
    0x40b0103030f021c080105270612031c0516020f06040f0303180609050c0303042103140304060213060804050d180b040303110c0a1a160b160e01140f09 66
    0x1002d81302c4056901e890b254503d03035409610354508018080c076010040800401d0150396400810301400154000d0b421203000c0c2c07030000c07610141c0d8403070f2400c5001d401b0440340800b0003840000d032551302070341082d0700840310a00502d08880c00b40105a03940e40407a440800550000700004d8081120950380c00d40c0b487c024140805e040c0d400d014101c0e10307052549d808440f002d58601d400c1c803d00c08204070310000c1c000f06400540c40e140c1002140c40740d0a95402c0c14050141140184808040c401d545015084802c0d40485841c0c0c2424a4014083c2d0407420b40100011120900061201e2154018a01894010001d0034000c45021008c1f11800d04202050b14070841d0040005071036080c643c000c00c0214025079a403400c11140022050611030100300303841c46000110f106002d8142441240b0046e84010100300da42d030700b00c44c1c03103001c03241200341c0b001750610340c211007040824ee081a00244021943d81c1e181a92245c060b00150b414110172928070704540c0c4140851881141c0d4000103205c0c296006152 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 825246106 1250 825244856 825244873
    0x906060c1c030f050118110903100e0309150d110a170601030b2101051b04050621040807050609010509030405150d060b040e0711030a0807030e06100617040b0103030f02 74
    0x203c0083c0c0700300380d000c0340001d002c41940e1003000e00c0038843c0d45038510304402040d150a4a10b00040c0e0303035245000800c0321141c1c0d1188400c255100c10412145241c1016040100c01410a0441d0410390880100b05400c5400c4c04009800c0030f195a0448030b0681d600c2c1c071403101115a02440e6454040000e1000741816a03a00c040300035592210450a03400100b0134991491507200040c1609480d0050304042940c9100040b6081f8060325074241e4003500d005690494441d41c109a84c4a000a0719624001140880d0030a000c1402940d4004002d0b183c01042244c0301616001101801c9400445d101107aa4200b80301c207005a103030a000f40301201c42407011250801901030402c404031161640400f85140c1d001504000000744090419444902428440b0400b80014042c2e0344a00c02c2183c2030b403c1201801c0005e100074001c0d40110740c1007a1220440b03103189003403902d4108550315401600003240c040c00c2840c034011000200b00c3d114640c003901c410b003164a0356078180e4445d94211030010541c02012403 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 825247356 1250 825246106 825246131
    0xb03010f0213050d050607210516030b190e0703110c010213121502090105220e0a02090604090e030903150f0105040212061009080a030c020906060c1c03 67
    0x1464030003440029006a946070711280740084030419034002805503070420002004640046034140e03200805040200040000c00c0000a91205000f01c00056614110038001c6c50b145020350802d030464513403820000c403005041001030340c8604000305151143d04990038000061a103a01c150008420300340481d0f444c4100385106000d42100b1800417081e0350102c0c0c141d00000011020038000c0203841c025011401c070b01d4840042c01d0403120040402c19800091181c2c06034465402c80d491421403541100d00200e080300c1804500071135100d102e2042d0040c7d03000c60700c044107034401c8030501e590040400d49824030340322006014011204607c3d24600080c014004652030a00030010030803841d200706d0701d05103003c0413201e2040b103040c0c0103d40070f9441400050305203d0214030f002d402202c111115542e04983c884122011807440d01f1201aa01580443c14101500000240074071031007101c15010f1641c400c4140023090207244c4055400340d12081285180950111005260010740e18000c41d104a4588 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 825248606 1250 825247356 825247361
    0x1e0111040902180114030c07021c051501060f090509040809040204030516080c010f0e0a050a14010806040207170d060f06050403061401030c15030212090a030207060201021e09040b0301 81
    0x5104444031500010074002003d0b64071503240100d0400d09016001d5242d40b4007200766408018807022084000041c200103664071004000c1a408403171003902101c04851400645604a4941c81c40441d41040300200d4014095003021141d01d1590b59910a000d2402080081204010300190b6484204026519094480b40000e00155001311b00400d081100211054079a006540c41702c0341e9230300001c41c484940d80c0e0080c118941c0c0b141602c0c201c000060a040010f00c64600f5500060b07021170b29200005810001c00c400845040d42601c42c0900d603030710b583c14130092f4801c0d84130007000d500d51161010400d20360a409000c0c680c080b50000a00b0036200c00300b04016207101e41095000c90400b090400401590380580151074102201142207549941c0e145001149c10b405202d44805a03461a250312500c00c0c1c1c143c03848003000c000c0c054600c0c00c24407041501c40e4082d410540c014055140041250303401402101d1303840f030310500f561504003c42c05810040350440c0b030141e40d0191f11a103e41300555806d0 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 825249856 1250 825248606 825248609
    0x901030f0e060103081312020a09020a02010f0e0f010b0303030118200a0302070b1e040b060409051b0910080303010905060609100305250912050c100909060f05031e011104 75
    0x314005c83e0b4484100d004040486081ea000c02c1e81200300354607402c0181c0b6120400c2c1d00715600b02c0302c0540c0310122041d05034054015210034400383e91502c0051487e1400001d050002010380400801070b5650711414542c892109015402c0c03943e044001c0884075040b00c0d8070081d054000c520080d04852030b50034007070205078480340b15440025000302e443c90070300ca082201075400003010322000c00c1c5025650421850388400910181210345603000140705511290008609107a00600750b4400c51060b44883e0000328816201d58000c0403180001400701e424800343c802a41d03a608015070460f807800081c000074203030083c40b26070410780511001d25a0748491104801c09042c070f40740401c003840d01c0100101022880140070038540f00c80e8202d101c006800c00b800b803003035a40b5100d0307440aa070542d080c450b18050000c00d90680150b5021804203210b07601c05400d80542d0081c600c10301c80c1e00d50380c400c0c1c0c00d01ca410764018954180c21a0403090411240800701c041e82d040c840001046000d00d01403400a0750b0044d = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 825251106 1250 825249856 825249863
    0x306030c0303120b0607020102100f0609060807090f020313060905070b0a050a1d0a090b0f06070f060b0f0a050f0a0b03010f090b090f07080c07150e0f0a080901030f0e060103 76
    0x65010f6000a42810b02a0880c1c0b040c0507030748a4103010694000079900c0321902001d10310260b0380d440b043c00d03020880d004900580b045500078409995a0211295611114480ea80505240030a50b100c84081c5001320380c090300280c01030418440013920b4290003001c04400888040c0302d40c800004000d0340301c4019055a4606449060f1140c00404002c1c00d000030a604518816440d0b040030340c4240d0b0352000345ca00341e0310a8900058903889101c08a100850101c22f0140d00841c0800d422041140410311400f196100700c1013401144c0303440d1300317011420250f40c0b4119404840b0307030400d11441c24504103103c01003c00925103030104d40d035400c502c060759000782c01ca00381c40010b040d024403425036613024005800d841030791001d00230b140110307250304d01030b0010b03060b40100076160002c200e00b80100c00c00da5981c65000410594048003a440240042c14201d500318800e02a040c110315111801083d40003005400020b0545440c4001e001103000380307504d400c4511219038801807403d00034400c214584c0030b50720 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 825252356 1250 825251106 825251117
    0xb0c0904140103020405100602071413020c03070203070f0311120c0d0501240b030105040209010c060203072303060d02010807030f0509100e12040b13081b1c031e0306030c0303 77
    0x1180148411b03604020200d1b40180c17040c1c90204580b950014854080b141059038070b02c4c16980600026072a101c0401000d00c00b240007007801e0707a03410000700c02400103038400c50850309841d0342d90211280c1000c2c2c44c80054105203440c1c2003a0381c0350070040a11081c0d2f00304103064a282801d810f001500701c6d00d0704082942e050b9500c6030007056031907040c8050f050420b00e06804800907071030401c00150f240301c1406044d002c0c03074001c04d90980c01c0e405841600e007040d81c030039000e545a01d8004001416800201941200a80300000b0101507070420341c100ca008000160890900345811f40040d00c901802500040c2010340c0d0f49034011200103280304e82806003010074003500300710407503244010544014150356241d0780c001d07400c4100790301c070a003007203030212070040f2030450301c4010402d0500c030000d8440c0e010002c180030780300c5911104140d8004031a40403000700d8080342d080384000c40003550110301c5000200410440111581d0b8034550380254515148249408119241c0b6552120780207030090344110080b80 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 825253606 1250 825252356 825252359
    0x123f0204051807020c0d0803042006070b070e010504080309150d09061a03161502030f1911010605010c0213060824011d060405041103011d0609010b06070b0c09041401 73
    0x183e06000317031100b400085603030401d05401512035400511001e03000500e407090001100c1c0c822a900d02201e8400740f00103084513200c1119040800400804480440005001a41e141141e6000750706841c01d94200702c000b141410012814403201240c45507420000200a00c40004100201e000d8024031900c03564012034082241601c00150b10044030b507032413007600124500310704451794001c40000c981a2034115190b9507040b1038160b0640c0b081c0d500303103c00d003030000403006801d95042c0b403550600601566201b00003410125550b0807201c40b405040e0000300048105000762a00b2081105445610a00083c405e86e4035040e5a143c40842411000240180c5605101e54000720b060380c0c0c0180294201d810002001d072038050300200740101140c1c45035070380f04003290901c05280403d401c1e84c4000380c0204070071080c4180c203480c00100b1483c0034501c1d100d0075000400301c403010f0080c8100d41e030f00500302038248120307030f600c1c40c24007200245a102407410901c010b10312907649000f10190018204175008103035 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 825254856 1250 825253606 825253621
    0x1d0d020c0310051506030c070209042409030f1103160609170a0203092206081606030e0d030b060c01020d05010e01060e0904080d060506030103123f02040518 69
    0x1103540b94a1a541900c0e000c20000c0440d88000001d0504504032030305952513075502040381c10741c0960341000c1d401075a0b4500304410804a04401e0b0710080c01c40c08078200780e40191001e10151005048020700081480d000e21030700c1405081c564502030780010550381012015904e214a88102c0c0406455064466007203805020720300841030524894001c60034540728040501070354038844c0e1b2100501500340310b0168610784000042d9032201050691f4203100459551200d00e9984078000650200d01d00000c900186207030080c8282e40903207400901514a4000c0c3c0704043d0000d241c21000640c1003001004000c0810701c080c0f008042c4031101c0c0070005425414508117140c24101608904140038445c800442280d41c0c444029a2245d8001142a503614440b09140061305903940011340102002c000401049481103104248200c140c0d94441c042d01c2005005614000c4031440e1194605025545540c818000080e0040306007251310152500c8d649402054407030118a41d401850040002403000304e = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 825256106 1250 825254856 825254863
    0x260f010905060607030e01050904020906030403030506040507090f0e06061909030507050d1a04020a0504061701150b0d0c09120822051c05070b03071e211d0d020c03 72
    0x2002c1e05452407410003500da1340281c540310018030164140240840c040b5516940e6804858a0300b0f0b0140040f6100d003014907028020309000c1c0c03001c0c0e02c0b4508040001d042c40c0e20031a580021100d0706134184000d01e140050a2201071806813400790080400c2001a010711007d41c01c280482100d995803044017403450030500e040018a4003c0e51241882921440200d244100464100103007901c0986150310741d44006002030f03d241d8400c40d08941012800241d02a1280c0c150b04015032040080c4884010603140030607040c02400b4880403a581445200600c84407035000c0081d070340c054180000c049454060b07019102545590441e10000005003038090015215002c0d00c2d071044c4080c3c0d006040c0e0800000a150b62031000610703107544100c0f10200e00380001080000002d000140c0f0320b9969040a0800406007100c3e80316a4440b002c0103541c0301e0941e80f003088291240500651200000007044c80e114018207a5090680440d11421191155124051041c214180d200381c00410061343d404060505 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 825257356 1250 825256106 825256111
    0xc030c0501032306120d0c0303180507030b040807020d0819020106180c14030f1605090907050a030e100e0c030a080f070f0c09060501080108030c07030201260f010905 73
    0x105810f010480450524240203290600b8010065035520f40d03811011841c0f2407070107442d640880c85840e00740d031500c0e5005101d5018660080d5010310091025460900c03509050501c02849544440000c00106814480340c45c3c0080c80380b044540390001c50b80010700e4940100009071082140020145001e42d0280ea0500c0354080f240001c7c0b00b4503143c07402d0035602258ac407800ca03078500c1d110795103d5002c512442d056044440c03c102d035240c6a09003401c0c4885d00310b000b00c907041c7d43c030341c41d09030030904081c05041a10b01403039004081142503610164104c41a420212100040c56141c0801030f0700c06200f40603200215010850000c1e41d41ca8280c81c452516580041c0d0901a0b088081101d000c84d0740c1008444a0b1a41103281540d188001d160080302c8000c412009024640700180102d64103aa50704054100d800c240d8070130080c2e0b42c90343c0a0036143c2c07003121000401d03540919020030043d4051004198420010540007115650200350422100821a05000141c0e403074001401304034428803403e46c = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 825258606 1250 825257356 825257359
    0x3030203071b0f0b06060d02040b0408071a3f240f0910120c030636030e030f01050405011a030714030a02150a0e040510062a0c030c05 59
    0x1a4034080c42e16282400c0c401c3c3c2c44043c10f60000c1c4d40000702c4a40710f042c00c0b6002c40d80601340442d0780b01d41c0d904ea001090b402a001e030b0303031003400780f0314001560701d921200c8070544100311040d15142031310114000e200314400758508103140c60303130b80f03003825011100b040700c0c0301044031402c0500c003545482c402c1d1408000c003000d1511000c0011500c0c0d2007003510b941154a4240d4401e44804816488401d4000d0349540e0943c0440c0d480c2842401a00404c02000c0090044902c1800103000d286569240d40d12484010340303000203808503106000400e1485039580c400b426000c1e082400341510660080b07802c0c4103141c03e425440d40e44030f40522081003800d1080708250844460000204001c6a002079112480e070f100301c030204080e151050170150b9050210840c0c8640c010040c0705460401d41c68003c0c1c41d04010000e0000c20501e407824906400c140c0121840740c07443c9000c1082580c100001500d0303002650011060300a9800d40440844020404444140d4003031940740c520341d8070390710b08034107401541d82219 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 825259856 1250 825258606 825258647
    0x30b1506031b1b0a0548040603020604140a050f0904080c070b071a0a0507020c010c03030f06030f020a0603020913090821061c17031803070303020307 66
    0x440703031814014414088400084241d9910010043e03083da10070b0450146224070700410120104201c0300241d035042880c8503d1402144145001d844181c0046090302c4482d680c041c907041c00c030341030705000000b0320311240204000713126074a0b0380200e83c40340c100e90440d402c000000b0a00316240c0c60106003004c0108421904541c0c41500b9102103207075090041c00040040001084207910307000c0070301a55010703120440303100340c07150490709140ba00340784800c405181d440000f202062103400071740222031040f03040f50002c2049045032401103441100c50181a420540c0d00c1007010400c10242c0200e40c01980952015034402c4e52034010405a02c015a1002003171510410200c00310b0b4a64200c034542800d4107400008043c2c005d0304124074980704080035820a0101c0703041c002c55800e401b4011a00440040d12a1020304902c0038100a440c071300000090010010f04141c000c0120030306005544c000038010a185102d12141500c81c910b0f00700311030490109402000300000b459001a00e030407003286c501d035403 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 825261106 1250 825259856 825259861
    0x207060e190303030b0d080c01090b16082a22060503130809040f0f0507110c1e0312040f060e0603040b070c020301110c0f060f07090b22030b150603 65
    0x34089074405440001c05260321026a0740c542da95a03085842c4154101816682e00d000c2105224020464880104d4004521401185003204614510100ca9a90b80c50f100b0340350f1580020460960f016103840d8206503800528000c3c40700503c8060425855980090107214858128040c1e003440c05402800403c00c0c01d10402144484003d0682e0045800c4a02e0950301e00c94503011074085c04008281c1e40c4c0c407a003040c890400c1014107601c01c0d40300b941c481c0d6861800701049640079803101641c80c04254070032a025810039110b82e201105649110004084610020410200d50303000d420541c4030a009c140503c0003008599003102e01f0181d04901102c86074610b1402d581d8140e00c48030050320600c10480313000c10000c11902e00b50b00900039601520032040d02c0300c14a0010701c2d41c600441203801d1841c002c01340450410703100803a4450003860580c60300f5a61600f0f000000c0c0c4150400703aa42500f945515a480c55400c06004040700554025140c0c0d864030720f0440903400c0050340042d030a901440e4200304 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 825262356 1250 825261106 825261139
    0x20f12090a06050d0f051302040614010c151b02031c02070c0b0705070509012303010c0f0c1b03060c0318020105030a0b06070503040b04080f0102030601090e0402060705010c0207060e 80
    0x300c5205070b5506081c074035100d090900c0404000c0070a500c083c2203d520349818041c1b0b02c100704842d800d580348200c41c00d0080c0754948070001000c0700039122071400308803514001c000248101e0b00400e09a0b08801000401c0403103008000c000246444514001d85c00c005134115204124540f100c28240c05a00d041d441c1000590722400d07034500500ca1140d070f100300426400704210041c0003c00c024040105280f1903541c551401e943c1c09034002e0740030280d000d8016040e0380c10b03040c10b015681d040c81039600c6841840a610750243d980c0e00b00d03000b04542c44aa060240d09410000118050246010352000610050b02c4e800280c200c41c8100004105002406403210043c0e920004882c1d0010007210b010030b690701440e01080d401c0c01108001401d9010200b004641001460094011036802030221a000d02200300c545080784410f4403014005030308003600b03000b0102507010301c80e00280302401c1c542c500003280d00d400d030840e901e00070f014005802000040155560015110441c04e008954407002900003c1 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 825263606 1250 825262356 825262369
    0x1050a09090305160c3206070c08060703230f1b0717030a050106050708030c03181506010f09080c0d0303060e0415050a020403050a0311030d060303020f1209 69
    0x10540c840903460305014020140302d1803d44442010034405000c200c641483e01601e030300300b2030080c02d24810110424101d40c00b00d1200d10816800d10001c000490b05544040c400c01d0740c0105030540e880386408030006814002040f84910a0203e66000202c00060500f0010880144080038004039410b0042c448600121091070707801041002d2086400c907480c2c074010410b80a1220043c0c0800e084144085002003d000298890702407140100701503a283c44098500707024150025211182c20300000300382c015404010740d04421900c41c00060100d0000303500d40351884119003260032203150b409228035942c012805005084942c03d010110354205090b090f602e817500598244102e80d00e0138003e00345800780d4440e0010f0320380d00e820303080c6030b180608000c0c0048091581c6008450301d0580004c044032118803d80381030702d070703c840600f01d0110780703440488045d030f180e55550001d0300042148081c0c0303e44510480009612a4000c0c080a141a1081174100440000c40d08100102001910385640e81e45 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 825264856 1250 825263606 825263609
    0xc04060e10030b06070506040b06060408100c0507020a140a0e060d03080411101707021519110319050a09050c15130909020415050a0902090d0803010617010e01050a 72
    0x350382055164603070740340890260410b0a5141e821804c0059104140100421a10312441c001d250032500c645441d01446494440ca21a40200d60842c0b00306000311102c0c0d800c01400308106140039820300c0440e030001800078603264000d0381c0e10102c4c41c2c0c458113070b4242120004002c00306030004407400c0c43c0100203d440c92410020080802c8509000901042400f40844507540405451203542c0815040302500084d4400b096118407610b020004d01503030f10020f01c8200492560f03880c0c0c0c841e038072034885546541d2a03082e40030911a44070010280100200c02c0a54403400c2604110072402c3c0c20b4400d000d04445c00540034504003030800c1306110205400080c07080003200140ea50024403c541462031900f4002c5001501020303440c50700006c0c1082c03c54110448643c000c844c10000346e540c0880c88a4400e03001d1052940208561000300980300407513000c1c080d8a840507104070860111503443c440654401d030400b0002c50550342440c444045090501c501401007002c0d0304040d035041a0005130101c859 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 825266106 1250 825264856 825264859
    0xc211504020a11030c03130e13082b05150109420206060a080105070e040507030b0a0b03220302100902130e150903040f1a070c0902120c04060e 63
    0x980106120310840c0420103440c0003e058a4546489605e240d84a5100c04402c103550720481e01c01180b2000500d45139401884601620712001c0b86590741c0b288150022020b00c0c408030b100c40d400301a0b0b55522038a00800c030b0108140082e50b46001c1e5a00c040a4419038403680c1004080c0a06001509860380041688100e07001e032200d090440c000502103845500e10f800700c0e0f41b03002c1224a02810b800184582c09808225004a41c5d107807075425003822918210348150010320100a050020b0415034046600403805150200e07051154602140688449a008030748048001040002c0b444c44407800000703034034002c40610b80c10007150310001e5440c0c1540b110100480d0f500e06000c8115910413020324000ea8003401c05104400d4010741e021b45548500d0300705400c180080f0002200320b10044206c400741e0b89104c1c080b000329800e0079083c40c0c00d80c3d401d4120115440c420440040468608185800184011680540c0d900b002c1e80c4894144034018016402c403034010322040c0940303034011081c12000f400 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 825267356 1250 825266106 825266111
    0x405071719020915060d0e01050c0a1b14030f090406091503060506011b05010b0906120a140a0602040f15050f04170a0605150306180c06071a0c211504 66
    0x104c40390740c1040c4540c420180d541c810700000741030240c14081c2d00014003500860000b001250744010b052030091040c0480d01c000200140450f0a5611106c0e843c0c050050081001d010300b644849191861588004511500c0c540c0220b41d0810502d0035000c0c0c10301804142c02d06000c0015003403011032000301c00d07000042441d40c492000900d05c0e403080c00c40c6407001c4010311080940f0b12013401c040d8020402e00c440030340039000719400030f01c071030400200004030310054030000c0c404202c4075203450015800e50301660480340611032149000c20302d140090409040c02d40080c030310191400400f84100f140c01c43d4000c3c10b001c0180003500e060102e1b80300381c4045a11a501070300100e61102c030403504005840d40300030009031820040c824441c25100805c45031803029411240d5680701d440e00580103580020b5805050350000c0b640544a04110000e00704103480b41d1b01c2e2502c403603910038035036190340700c04c84042c0c214030000700700c0c1c1450f144600099a14a42c211a10340514140320404142a41c03080070103078003864 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 825268606 1250 825267356 825267361
    0xc320a08070b0c250e0a1119020c041a01080709080c120f0d1d030111180109030b090604120e0a0603020a0212070803090c100210050604060e04050717190209 69
    0x703028804440031800601c0003100784840c61001c0c00300d0135614012054510545400207110708030314813072012401b2074107042d9402c00300c0e01e84211160b151552000300441c0604136802035952a1801400210640241d2070b1440420000c001030688400408400c10809054001c00450b02d000c101009007000070b80c0c2c4401155801710f8894544001c07a8042e05180c803ea071100c406a5621044240c6103000c103040064003a07480c82c00305402d903000c0b403070144c2c040d01041005541110088a85490300034040c1000090030b55039444208a505044520014980000c2e0400c010042c1d031050048010701941818982d91400d400480e12140850080009250340011502d010500801040344103c2003441c04642c0c0b102c841c07401c3d0740103030000d8a41d103100740f00b8540313460202d150100b552443c48801d58014807a070055040342d14083d00014040310f402558035980070550780f040350040d40c810380c010300c01003000c1480e00125800c0310b010200f42d0b4440e900b0198002d46c603420360340450341565804032845c49894 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 825269856 1250 825268606 825268627
    0x2010c08070510061e03201c050d080a1406090a1b050c0c0904021305060604030c080c1816080901021204050d11280c320a08070b 57
    0x1446100c101400500c110700c140050100b184d08641c003550840303440706507407172074810381d444111420b40030040001c43e0581c2401c9210880442c05851349034020854506802600ca042070000341d00c0e00c00341ca107604056095050399400c200340641000301554108607040e042034100c1a1404064040c9109141080c0401d03240000c07900b00c0c00d50851320441c14044040d120304047d190340d1003454510351034010300c42004514500781c010b00d4400d94003d400c103a40510002d41c08401048001c0000c1d50100c828000400412043e103c0000079080e000c00034a05062904200140442c04169401803000520204042c00800703410074401140203080c603c103140c503414440e5000e4018081644002080401040280070000800d03103541c807819211408034000340e1013110f0b00c034591040d2843c0c1070142c80c208503448982094000d6155030061584901c000e480c2d003002114100030640030500051a00c0a04084204550f03034188c0450088400002d100d2505c52880d803244e080344140014100c0219510210 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 825271106 1250 825269856 825269873
    0x20a05130f1a150436060303050a0e0915040b0d1a01050109061419021501030b1f03171e0c1b0607030905040f0f110406020d0c0c0302010c 61
    0x3007098030075003804440100314040d100503800c2c01c0103612a0344429410061014020121402e0b2100c0c034502d101e1181e8030030784007042800c2e4082c05044070281d0518908411603544102c001561103540c48aa07619012400106004849050b152140c04901f00740428802241ca6044804130152004141000000001030304031804043c0945111800c0c031500d043d03030030104181030580300c090f2103503da89074403440200c810782d814080c100241070040054141c2d420200d12240d044e20881d02c101c0d51020450030140e4184002a0b004846a1002009211504403210002c000d02000d004003048014510386035030301402c3d0311034618000006c00080007030b0301c03144100c44003454400d568099aaa000720988182c2d980501e0507010b103985c102d41e022040280360030001c6841403178040d038400c0e00d0641041d00b004000c24400b449041115924000740c110111035020b00d8405c11040001c5688a524141c800b1741014081a400d108110070310031400b00007404c80d40108140c1b070702031824400c402028a801c807038 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 825272356 1250 825271106 825271121
    0x5040905040503030a0c051201030305090a08010e16050607020a140a030b070809010b0d021f0201020c010f02041e060c06052d0a1a011d030106030602070309031a04020a0513 76
    0x105040c00104814410000011406031011000c00c021440d040481142d140c0a005a1221140d01da500100301007403141001d070200000040140d403103560344000ea40d0844041440c4011280c00c442c0c0c240b403250102142100040c1029904070b8030b46803c0b076002561440381800f5001020740290b0000c0486e403503421031100519440b111500300360500f180c3c0907002000440700c1074003030740c03d1851940140c203101ca04525002c1d0f02401402106210481103041c43d0302006005045660034001e0340c458000c03d0080284003203141c040180d031a81410481c84150726070794640d054a54000904000f5181e11403c036500460b00b203038001940780c884402c019644211100040c1c1c5030f007550118140c0d02c3c0701100341c090140001d01002c000c80301411000d00c550103140c104c143d0108003da0304032010040002007506070803200400000c0d8a644a564070b10072a0032410702170300092503102d000d0040144a6005050403000000c00c1c0e0094075103540099a034150502640d4003e40060380c2c8050405240d411004 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 825273606 1250 825272356 825272369
    0x1f09021303050f1b03010605150304050f06070903051c0203041802070203062e051e040b03190311010902030c1e09010b0c0d050c070e0c070b07050307201c0504 70
    0x4a0700c2c20f107451010b5650750b4091000203180b480c0c2204100710701c0c1c140b19940c102c403001f510849648050404111042e00000e10a80c0c40340104600c0320040035080c0610752103040c440d02c0f07074800c050031801c0207440c186038103040c40c4146110040429041c0e17000403c0e60708560901c019040d00c41c40c3c241c1d07400c01901400200075014071800080c008846000001602e00c0d200c54116100302042e03450010394142c2c0c0c144145500002c100490395082d0191410f046c1d0403402c0984040751100b6501c02003450421074003110415100c0b0410140100b543c402c0740403c180c107000000340801c00041d00002c2d100c90400080038801e501031219030070803140341e440180c10054010720368103035581d482100e00c40300c1d4030240145145001d480d040c604258010400e841e04042c00c4001810410b0400041040245016003580c60043e000c0c000c480005000c5109103106000d1642d4084c0c50b410b00300300c041c00710100b0108a444080d00b0018550380c0020000e00c40302d03000c035001c1084a01c940c401c4c000799400d210b250000d0 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 825274856 1250 825273606 825273613
    0x302030d020a030f0c0806012705060f0310051807050711041a0114040605220803220b190e0a0f171b030615030c09010306050f1f0902130305 62
    0x24001980650105031850402d00c000c2c050302224600882d1941c40c101c47c2d840c085840802d012000b00d160000400601c0600c0d283c00840320307224400102d20781c114946405511100200300440c810790742810500a0500b81c1385120304d031107001d0206015900081c00d9404014021941d001402a1401c200d128180b01420401065469081c085a500f2426110b45c0c04a06001c0078200000c00c070f40101c500710b41407641d4032402e000040c0042000d2002450010803c003203800808035100c0c80034002407210600c20b10246c2c0700c00c01da4031408c9218050b240e21802c00f0f00004d20149242c0e002c1003600d0260040c00d8500455451020000698105c00c5038002a40201124401154882c01c049403000c1c09c03201c2c00300300c034545c1c498503482c2507019260f00e44403601074100a02186240885c1040d080c0f10b4a8000c0c140c50306501420007140f00d121099100361111502c56040c400103600c0e600b01240c00032003005100c580f141e6046072050f603150080c410320916590000d02104890500e40380003000d164030000303a = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 825276106 1250 825274856 825274867
    0x705010b09270316020f360912090d05210403051903090510141603030b0411041403070b030c0a09060302042102010521090f0105220302030d02 63
    0x300034125118540e840900362950102540340302c008103070782d00c03251800c107980c2500d02c041d0b00b80a1612003d08000760403500e0711101810382c100c14294420b001c40514105c5403a8004506004d14a0801800c10b803a2038011801c00342c40092221f0864003801c40030b4810100002580c600359140540c0400340c010100501d08a4024661002d8000d0080360b0244040300c00007441c1130080031050100314401008a4601d007020003a41c05c01c1d507441c140b1502c42d41004510500c1010f010306543e0701240f1940002c1e112440d070b02080680610401c44004c0090b00c0c100070403010034000b0101c5115038000c1d03d020303402c01000d501072a50100b0202010702480b10f0706907104c1c189961484880d800000c40c0d503020a51021004c00c12a1003413003600e04661030300c0a4580400c20005401202140743c88090381084410040345900801100d80764030b40c02c00d006588283c2c0c1c03074202c00560070000f01c2840c0b4451a41040700b80701000c0d030300000504418030702e5940214440d10900d020303842d42c820b640000c84114000307e44c = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 825277356 1250 825276106 825276121
    0x4020d0f0303050619050d2a030c06082202090a0b061303020f060703020d1202070f1208070309230a0b0a0c08070f080a0c050417030d140c030c0705010b09 68
    0x78a016071000c3d914001c2035800d00490703c1701c4030501d010350358000203080652004502c1e80c10049008014011758001c018081c905210842e91050300291000061a04100201381d0300080031540002554441d480d40350314459032040003015080064400c14102e03000c24041a25070340089080040101240d54425a1040311814500e4520099106410142241d4050706100084803081d5074564042c058490480300d003502d581440c50200183c0c19801c1c8030503000101219803031809a4003846021440c408104070007044094000c1c130600403d800c0140d0000051031000106109210603c00b07818032248100030795181900100c0003038055014038051011409a591100203c0001c0b540d508525a0340d048081d00c10f2141c2003100f200242d80400095034480c3d80782c1c000c0b070010b00149071043c81c01e551880c400803502555440002c0b29040002caa940c070300114825038084001c0218025641e20300810008142d000041c8020030f0802c0010744c0c00e0402401303602c0003180c2c620003081c080c0e59050800 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 825278606 1250 825277356 825277361
    0x70e01230a1d01090e0a05060a0e070302090708270706110102130e041106090d031b061509061d1b0408070e040b06370807080a1b061704020d0f0303 65
    0x1302d0244003914200b5440313480c58000c01c2c1c40800603044002441e964460b14407402c010840080f01041ca405014004401640e0389031009028101542c0c41a105044c4002d101380c0044140c0750146092808810300c3c00c081c0780100301c24084031301c242003d040013001e50000034064454513452080c809884140402c102600510441c0540c0c014600403882c5441380f401c3c04050b01c01c0d074000c83d0b4403160440e010300000f4842d0700c103183c01c2000101841040c111650704e00c001e4a600344180109003035280c2e42402004c04620515004181010002c1448403610136080d01041002d49003012580301200001d400304580f5003100e000b082d4207000c60b800c080d80c5900400c506042a00c0454221100d400401c0c901e02e031012031880f0315024502601d24501502e2490000700c010304c11321070305c000c190281c0020340c61024030111009003214bd007d06114400d9141803006482c01c440204d245a180d010240301440d0300a00d50b000d04507154140e04480d03140c500005550341e5107580020001c3d10911980810543d054 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 825279856 1250 825278606 825278609
    0x908101b031406040203090a0506040c091401121407030c0305030a0e19420806180708070309050d0c02011103120a0f060f060e03070e01230a1d01 64
    0x3030150405094140340c084082c2d840e0342c991141c00b081d030308010031840e2609500035130300701c0e01780703821203020b0170959442174200b1400310b9058949460094041086000c3c60007030f8108900f440c90710306070a6060090041c9030b91141d02029200c10b191600088411100b0020103000c0c54100180b8414181d0b42c0c0f03021a0b495004200e550001040c08101c0340281c20180d02041d100c1752401c206044031406c0442c005000c800c1c2849808495903000000c074030705805c0e100c0102540f05640c666102c54009204040d25406003e00414014a410041503104004444890341c00116503e4845050344903041c08074094501c08101502d1b0b40a440b134500155030308204aa80164401c2c0c850307003500080c0b141001d489002d10820302460811810014103491481d600510050481c1c10000400b503444520034200420140c10200114140303a000003028a401c01600c0300409078050301d0380300c83d8142841110410200034424900304001c45130001d43d6500c1c110b1a02c06441054006182d8880804089006200030b = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 825281106 1250 825279856 825279881
    0x80706232805070c03031a120703060b01020f03030121120203030f18030412061b05071b050f06161221020406080606130302040f1d0c1f090810 63
    0x411a0401900380d004452040315140c0f02e21301c0000c110344099021300551645054000700a10f00000c02e556500c10070300200f8107410061500f1030841c600407084841d41150300c3c0c107550024001d251407443c0042240d06580800c61900c094040c2c0141d1040c1c0d030000c6402c001c240307801c503007041001035a0002c05107105046071003072110192140c0c003000c5015100302c200084240c00800003030205091003006003002911490000850a103001000110700810018000c009100050035000b0300002440a1403880028140d520059141400241c805094403e034180a170001007200c2e0800307040100841107954022204105070410303000001c241100c3d10144213500f81440d05100407942542c401e640a41e040e0b520f0310a490b440b10010040543c00181014502e0b103003881c804001078071240195400210b9211000c981411840044150004600060b440c580d11841a01d14965900b10350003e005042540081290002c0c600840c0d0300309031508060114030440c1000340780c1014503403042908889 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 825282356 1250 825281106 825281161
    0x60a0f150203270414090d03020a0e03070e06010215151e0301050106031b0903080901050306030f150103140f150a020c0f0a020103060e130602090d02040c0e090106030908070623 78
    0x1041200e00e07074101c0b03040c6e5000c100c1f680864000d0b413205000f07900812000d03003141401c60701c607410400000d00d4403586400c011550340d54170003403000e1135030108102040d004000076042940d10f40661a444181c0480600320312804000c040b0004070400000780c0150540302500a0026685880015000c1c2c070310890181c1400045222280e58184210b100340d050380d41c03014416160403144001161150400f0f4030b8554140a5111500400c1d07000b0001040e0006940d01200c10341e40c5142070000540075040c000c56a0364100c0300d40d580003024080707500d1b0040307001000da0400c02c0d00c0d4840300d04024040c4107140c001034419903180d00110a00000e01c40407440c801d99003800300c907803241090002c40e1742c180d45000f0300c8c0110104440000342246c0103050303205006080110180b040e40c0009050714000c00e03050740442e1031204001c5141c10b25088250161000b070805004a240503503a148451140d1080030b090300d580c1d0300d54602030644c1d0703400c0070340c100000083c0300030141040c004030b0100c1143c90205030103070f66 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 825283606 1250 825282356 825282371
    0x306042a0908030c030403020d1e110f0109180c0e03030f04031b0e071124100b18040e0f1507020607090f06030903020f01110a08060a0f1502032704 65
    0x40000448402d04d480c1c1c03000d141000c1c510307403d20a828600ca40d0443c2d8018502c144010040885505052101d00800d00c20440c40042c40a22000500e0443c03a01e040241c000c506008003407c400c0040390000d010180020500c640800882e030f00011070030740985c54080020111900d004d00b030054015240a134403c54150a080b40c908940b0f1a02403043c5820700c45000d0000d40010301031003112160489650964044003601080070080011441c80c0c003807000500d2091010099000d12040040c10700b540c2168500804000d8809000b000e4070325130352055440396444161000d050190ba04010701c00070485106444030115100100c07401c036600c8005222b081c2c0000c003214441c44800317040340d84d0241800703070300c90030705074110040e1841c84800d03815841001c10f8103081301001d215600800130034002043d195034003640014520304010b410720303102c2d40c0511700c1800300c00f005035016801c0703842010741b422000590850607400c500404007100050b4500e01c02d1502c480144c203512500c2490121001c2201c034 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 825284856 1250 825283606 825283619
    0x40c0c03090506070c170c0904030c050d031a06090604180902011107050916051b0d171b160501060e190527010b06040314010c02030a02030901050306042a09 69
    0x1401403100240800d640340308100310b040c410700301000e0340351504007c0e1010300b91184e0110306c110105039402c40005c1c4066482c2d01c03d006007402030040980d0b40d480c3c103009000210250380c92440154903c944164000201c400c215038900080794004d14070706040c01502e14040c01408001c048103070003680442d0b00c00449070034041d0042203000c2603a600404e08500c6888510075000011800301021090040801000340d00000138904207528421220060206049808005000c000b54605510b8001404030a11801103041d411740480980f4419809880d030a100d10400b0300881d04c11030180c429481c210010401c03040b64070b4514882d042503200b15400e00348000048045410841c1c540c13144664144c400141920070080066080c41c0e400004034190305c0c007a0002d04140e11692044032846ca4021042ca4514000e000b00b0454503224009141003280c0c80d00080c0d2a40311704180c40d8108040080002e0325a40c070341c0c1c46124040100f4115840c5584504c885102c4108061000c2000c100c0350400011796 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 825286106 1250 825284856 825284869
    0x9050f12060c040623040608060d020316031202030405010207030b0603030f04180b01141b0309031209030c04090305160606090c020a0c051c0b06040b060c071a1218010b040c0c030905 80
    0x2c64080c08101d446d145c0340c58800c0300c04810183c0311a5000c216a142407000d0f03038041008a0b03120707c8540b00da644171499442d10080c204641c003a40b00654000784410056681c000c64204216500070030074103003554580c00081e065100340307061510503401c0441c010400044908418541005410007080f40440030f400640352501c13030251700c00709171908101580ca00c02d4080f028041c4d0886540490b4140040400003e0400390201000490288045a400c145240802000c87d2240d02550100010780007901c1c0206248103460f85881c0e1004804848010010107500c17400c01406030803810020940301c0c0c00c0080d12245192025030b2051613405010609280484040d069502c04100009200e06142e0701c004940000600b4194400d40c1c0340404511500d50000400b000300102000d80103003400c182540c1c121420860b00d55040007000c0c08143e03d400da809030078070380040004e0100c0d030003060080c001a0142c0041c10803250018104982c3d103201d00d800100701c2c1f500c10300c83e4440312100350b281da060000 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 825287356 1250 825286106 825286157
    0x6100803031b070c17010b13050609010e221110020606010203190309020a0b0306030f0a02030607120915020d0606020606150a05122404090309050f12060c0406 70
    0x462644004458103204000c001e1003a20f03c140c4852813078956501640082408041c0303e10300c0e59464400c03514607441c2c8400001a44806803004002070b0070800041405c118050082d03d1040030320304041901c04035070600c1e00e002c04500c4106a0f603860710342c1c85d16980c3d2501c181c4030b49000387e100e0400618500c5c00420325505c07800b41a40114200101c8403c1c81c580482e0560070b1106041d41c07080901c0158480c6000d400140030002401992810888207052404090881701103c40c2c001c00341000059070301240346608107846103003c20800c10100c4002000703101406005014002900d101c0c0f0098509402400354604101300820a16548000982e00c03840100c0c0d40562000913043c2d42c5900c40f80c0340307014101d049000c0c50320504028100c90303640301065050303c5070002c0703000e600040d01010045045050948000740c2d400e003c80f0407955400740192405004183c804c442c15040c07800c09840c0c910041c40c01c030b00960100d1319181891041c0c8659940140241c07000909070446144501c2d404515144 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 825288606 1250 825287356 825287371
    0xa23040e06240f2116090303081f0e130203161a030901020909010602070806013816111002070806010303080c0d0c02010e070f1d0a0e010203090610080303 68
    0x10b40c1c0c1e6040070a00c80860380009803114a000050007058042c040d403000c0090700035a030300d50802660920b48162a4022041c11820302000000b24050000030b500c02e46040d0098098034100e070141c8030444001c00c1000301034010303d222440748404c0100314280051070ba080d4500a4040d1a03503086591040c070580c0506018588440036030300c2d044d110b60307690b003001594070000c80400141032210078400641e00500070307802400140e02c10f8600388803a00050205034014100484c00d60101200c1901001d810a4000c4412b031401150021524940f009601240d40201081100c4140225285010031840b074100c082ca60040d0301c2c0c40000c0d0f80160000840f082910b43d00d10040100da880d50340c0445005c1c20003040d0108240e420700051000403290f00800d0091314540e00040b0b000e0441c02031140c80d084180d4051101c8061180c0200080c4851001c0b40114039065240d03002151750b04400040602000c06401e4610740c8004200b01208401250240c09100030031360182042e0b5039560400e40d64007050f82c218 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 825289856 1250 825288606 825288649
    0xa03110f090f030307020306040c03061119200106060c05100b0d1202011104260a11010e060906041706130210030b01020c0a03060605010e0102030c0a06020a23040e06 73
    0x10507652400c8400800000c100404503460320605601003401c1c4442510f04480400300b5240520410110b4000c0b4159002c518502e241022a110080c1c02c1e140040c20b01d00c41030000e4890180442104260345a00a141140c000d02845550b110002d1113124140006c2c0d5050244600800c9c1d440c4441c014140300e0034009000f803078000c01c1c41c0c8030034135140000480c1c0d506640d81c0d1948050703d415010064801482443c0950034640350070b0b0310912100d030b200080ca52154010600741030000d60b0280901440c00001c1c40c04401c0414000c1c0424118802e80644070380c000710100d00082d400c1c16a80281034200c8000054901c103403980b40c00f482c581c0700d0b4450001d61003440300460808440c403981c00121110070502c12602204400d40128040a040340c000f502c003161950014003055802c001e50b410304c18020701c001c500e45460304218640350000114001c01ca590005507038030b2454071a4400181e05404054413500c10640500b00e00015807061040b000c802c42d907200000c102d45030421421381900010880c1 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 825291106 1250 825289856 825289867
    0x5040c110a060b0d050106060f030501090902090117011118040b0306070e0f0f06181e090f07260103060f0204080d03090302030c030c070f09050c0a1407170a03110f 72
    0x2840301030103401583c40d4002d41c2e4410709801150090060600905084d00d48030000100c600c00107050b164141c00c0103440b5804d1856500050b200c1c080b4080c11500c4c600051a14200941c0806000d0711200070840580c1c0400700d00c60300754403846040440c181ca0221400c1000301403039003e00d80c8410048541d200482c101d020301c0a41410301c80700e84114648010b00c101218801c2c42c001583c0c44d008008000d4050310030f1801c108140c1810945c2d082140300302c940744800b15082c0c500141c401c4c00000c2414004c0c00b4000041481180203c4510007184144106007030842d507660403084242c1c000348010707203a050402d1103c00500001d403007104e06890b0101d0191020307400240c420380242c01d9151701182188403c12903902da450051010b040c0c10b080030350103058024074020b8241008089a00103d812500d45001c0c45505541107085a64040d42403d26034080c20300b515100384a409852000b4005501460000528415030001060310441588042080c44420f81d41450079000c3d0000400181600300003 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 825292356 1250 825291106 825291113
    0x715050a020109230606032116050a0803100f120b130b0907240f081302040207080d05150303040501140c07030b06031b01020a030c02041b0905040c110a 67
    0x5000400c140d0001149101041d07964282c510640c4540340307181c0c401c9150070804580103000031a0401c108034024001d40c010348400361075a8807003550168401c03000061100218201d07041c000901c6402a0907140143c0c840e09020255500032100c0e040c1d40004c400c4040b84d2608076021a40c1981c850345021601a040c139910b04000943c060102c40362080e102c09400e0005804102051140140c4400fa00e07119140003172502400401040032900c00c43c00350140a00365900a0f400c80d10780d012460400103035201d0100c0ca50f80f05030f00e520007941040c0001400300c1803143e00340051010404005040003039540720300c00c28510354494070010758180c01c1007000700001c1d0301c106e01d2005190040344c1103501d48645c4a055030700d081e2241e441200d00c00c80c02405c0210074501803004a0b8a402401144c80e00c00482c1c1b00000d49030522034200400b840321429800741507403034070b81c040481c8070b40036070f0142c1e40d2501e8a0b00c00f802400007885024860b038100304401d041c1c10b12801c0034800d0a901e0500a0003003c201f0368 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 825293606 1250 825292356 825292367
    0x50604032007060c03030209040609020a1409060306092502070303200d050f09130e01150b0307230a0207030c06020a0c0e0a020f040b030a050a0614010c0204021b0303090601080715 79
    0x1e805e800301034081c030000c14295114480d01d0f0003015180b0300140c0e95102400d010300110740d049901d09450400f4021001103454450440780d10030f40440702c0c80856503651400001400b40441012801010544110f00054000640d502602d0082e120482440c0100070500301c06d842c0d0b008c950315141c011540e007055060280c800f03480ca08000c001d00905080d041c00100780d0200030009030441305522214100720300340f030a00ca001c549d00b100c800700e5442c960502550300600e22020f45070344100441c011219a0714600f0075141c843c245c1c0440d000680c4e68900202c0203658415902050302c1003034101200191003400000e112441c4ca62054400c2c102520342a8034122080c001000180c07195000c00003a818003907450003d00c0940b400352507240e100c0c01e140c50390200b298001042c0b01800d40c41e0401c00d1001040d60036003007003802002d1030010301320034441c03000c80d002c3d0042c59101c4050120303982000c1010400030003e98031808500048400b140e80e101807941d03680c860b600c503980c500e00d102d004000c001c5100703d = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 825294856 1250 825293606 825293627
    0x50408120a0608030a05280c1106070624150c032006010602100609140c0d0f020301060518060304020906010f03270203010c0815010c020f0d05060403200706 69
    0xc0e44001002da6403044440e055600038000c030b10005d40c000a05442170900410002810000d100c802100f820303003c807010f041d181704000040c08210308018200c485a40d080b003242c2c100703940401c0902c103020940d0f1100d61038a84012400c2c0400808407000704040a02c988220300b40d803035560312800b603003045403025180b012001404980c504240d46400340400010000320740241810790003000c0c8240640f1408c0c0441d80e241e00b000207002d08203c0d0909a04000004103078000f070081800f50b42e50604060050000d1030844100101c582c008400050b20b0340d0408060f00003001c2ca00c0f001241292030400708182c030b10040314001d622080d80d2001c0b400651051500601e01140ba0800041541c20b501120885c8446d126403210540e0304901110110b007020300400d80e0041040c14000d02c04c0c03c12588458210000020b2181004400310949041d5030713580e0f003080e2110780b0140c1508050a02c80c05c1c2a902d44104403000e03004a00c2c08001080349103100b501c4600130800f141d014125441c20450200c9810100 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 825296106 1250 825294856 825294871
    0x80304321510150905040e03220302010f0302030c0c150105011b02060a0305190608011505010203030f0a1a04090b06150a05040306091518121407060b0a1208031905040812 75
    0x132280042000d072594030694420002c1d0400854541e42186403484c0ea104529056903900c0d8040c45d01000140d802010681248445e810050385079070721103011310a580200c001001042c400c200b40034200081154445058074000c0e0b880795001504c0d1844128141450320000390404000c2000f0685103101b64041d0390000700700c3d00700c44040f580c4c4134041c00548000e0b070001c2206955031540320300088022844a00100400c0c000380d0300754030b03101c40106100c4c54020050030740b1644500182c80c403081c4420081c880410024420000403415003000d65501c1c3c0129030b418020b003050480a10020007030b1040c1c6196440319030303405203040d080d656040c0c06854240f6080340c1502c484a01e00944400f0790007054041f161203000355024549a04044195440800140c820f00240002404141c150f1208030342d04550405400f041451a5601043d00d1499030f50140c0f0101c9416185181004aa1402035000d4814400c4d80e9400d29400e140c3c0300201c58040d100248040c030108030100070f08981c0000590b21040 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 825297356 1250 825296106 825296117
    0x7360906210501020f030a0b0f010e060d0b03070510170a1422080d0209040b190b070f05120d0b0108100e0a060302061804050f07020a08030432151015 66
    0x80841480032500182d039107818a544a803079241c1c00b41000c1080527446042481c0c44500c1d01e50315004289030740300f0701130038112440c3c50300740907503450710300300322010041c50090b0101c034108000c0c400084c400856090411070b620181c00200380030358114061b00a00311005180e9900d251144201e0011200c502a14007000ca00302c4d8035100040b40301140a002c0307681c00a035025036903c00f040100411501e50710390b0300d0311071440b2008082c0c40041d96030100c410f42d081c4c101801d07592103180c1021140312080c003500500c28400c194840400886881c0035044623020540148440c40940005495107c02110b19842009004008001c80c0d0103004441c2d4000300c0d1924002480b81c2c07a1307004159180e000e41004101c1d613585810800e45800c2c54407032036a104e9800181003030709040c00319000b5121040500050b00041000c0049400d104402005143e2100544240c0c0300078007400714081c1c580480040c03006240c1c00b0b020444010a60604000c4dc4078030654441c5210107410070200031040c009841602c1c04112 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 825298606 1250 825297356 825297367
    0x8010b03210a180b1c0603080f0c0f030301120b1605031612050408030601120207050c0f0a120308062b02061b0a0c08010e0f150736090621050102 64
    0xf48100000f0042c1c0329150035a55500090081d000407240048203a0400500e0034104201192400701503070f1741c8483d016161990340620864252030700c198044000007a010010000032083c0c005140c0c00f10842c0319a03890805940e4602a240114900380c0358803000c502c0410000700c94054096124000d030400b818140b1019000004c1107048a00841e002c0b60900760010a028196800c07001c40e680001c204c040030752030404159070f100d460303c5000142e035000700c440d5840044103076201c0308030070080d0203c08070070111041d00c0c0c01c00400b2900140c81807401510b65540c019003004032807038005003005e084002402c4103005030b400c0c450207920100c82d04804171600000c01c0303c00c100c1071042590660181394840f07842810880c1c01c1d401c4a4003e040040940c1c88100f0980504001003900b100005417480a50311941d03c074081507803044408880d407004c0c0074070410007404030980000c0c00304400000300c004080301915211880201d0300340b07001d52101404182c108050b15461b06000551142c801c100150812 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 825299856 1250 825298606 825298637
    0x1080d091e03051605030c1c0f031103070606090c050903060610110d081503070e0712061502010c0905120c06031f0f090b0d0209060618060d0608010b03210a 69
    0x2841d007050007405128002401c0105203010407140c00c801c0011100710114040d81d40007800002050000100070147c652070249c1818000c1d4424a074507040c03802903903901c0c502468204001c3c80d2a0060948942c03516400c03240a40c40b4205a4400220280042101d45c403043d0030444003c0c0b220b00381c02c007004101500c000074908144013000c41d904c41032301c4003581410400c4001014070182c0a0450007030340230a108020142d543e61520f90031102d40e0410f64601407200d02000040d1002c0e4003c00000d000d00040c2c101082d9055220039644040b80ea16845031948400810003401444204608660f11448105c00103180420065400221210401481e5482d0803074494024100b0340c08600900d24003c4100001607490080d03aaa81c0d8044648200c0c2c000103a000940c144070250101d801510b0104056202c03030006040364205000060909071140c0c02d0380b0025000d0206801080259420300350048024180092981031100c2c2c40d458031101220500351240d60ba400880c00c1504104103125001a40c = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 825301106 1250 825299856 825299863
    0x4031b0b07230a0903020a081b012105010f06030b0307080705040e030705060f0907090501120314090301153002040225050114010b031b03060102031213020901080d091e0305 76
    0x620700c1e84c541c1d4010500d075004200b1041110380c00b030149608224610f624103540210a00010602420200d03103c03548411081075048172103819130503031443c1c900045a14020240658200c035a603680500402c490380c4249030f2101414400c5c3c405130361003a00c2c140038034640350304455020410030040360f08000f00390325440c2c42d0103020385e803031201c8008801c2070201c03600c000d02089020341002c4100380400c2d454031040550540240d10041d080001703d100d0290441d508400301c03419008006d0081c46105005101c0c014107a2561262005c00040e0042c030000c20707030880c0c0f001c50440a00381c1502c0d007408540c2d024040030b50f0295140c4070150316001d1800a82c1c1844086048030726000d48000204042c1070007005030310001c10313084190a4081071003001140c1200c120201c500c02d03801702c0705035202c0d210039006074038500402c49000d61984604041182410b0002c00482c41c040c000c4401c100e50342d0340c0740e4266460f41c03e80c041a00008441480601810100c042100b003c520405040740245503640c407030905 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 825302356 1250 825301106 825301117
    0x60f0406030803090f1605150408012d1a0d110607080c0115080a150b0a08010e07090b18040326090105100b041e0503010c0804031b0b0723 61
    0x1000100841403044c118810001a140070881c0c000070440004040085040b551284c454140300c0c0c80a80d1070141c40d141050190f82c01840c00e14001d200500d160a0503c6200142e01240c150031615010b4aa02403021402429512800e01100a005403825003d10070b04a44108041d071390440b034600032209988490005104290040200b1034a860061502034250342103100c034018050400c603000e001c0c0c0d00d4081a030b0081240c1c4588050798001000e10008058031011825552148488000090030701c0b06410541c00f0606d84000d40d01520744038240038084450203007080f50030075400c400180c41640c550008070b402501909184248003106042c1c858083c003041c8a00203040044400d01c9482e1000340152074108900c65905840241482c140c1c000d05c6c00346103c2d412614030009046001c41040315000e0b40a0b08000c0c00900c002e425400002d04106001d076421030004075034511104c114040040401140c80c0d101c191006103459002040f2001c500c4960440300d0364852140185895210000404 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 825303606 1250 825302356 825302363
    0x30609100501150801090b04060312050901031b0f180503030a030f0b101e14070c06020f010203131202011e0e0717061b04151205180601030308060f040603 68
    0x2592000c501100410307524181d0107a500d04403441ca0054415400c40b000030705540d608000010003607004c00c0010090310555201030b040003c074240f11161154000c004081401c2c080c1c03400e101030041c0131881c42e100c0c405954004001819400100c01ea644151015104003c40500380d886031030b01d402c0043c0c115071000001c00d0100c0d0382d41803164031000c070b58000c03607411410888104001d29031a40340500684180c1d03002c2d8031a494095a091981c82c0110741e0302c6da5403000080f810713494151a1415404001080c081c50025208a00d00381720010014000c59120748450700070300c0b000310791503507522064402d00c000441c255500d940c1a00818009030550089040700303650f0100360100e02000c00390030700c4640d401401e01844440d40641221000003216500a102d0714984a13a144015104503540d005940003415048103103041c3c0000c00c1e501071381041000402d50400c01c102c1d1105500444c0034060415101c0741900002e00410110707024800c81984510094443c035844250316000030200c03503080c0c0046 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 825304856 1250 825303606 825303613
    0x402090c190e12010c0e0103021e03090303151c12050c060a151202151806030c07030e010504061d010207080a15050a05061f120507030c0e010f050d0b0a05030609 71
    0x1540d240140d0f0340b4411a0703000001700721000744190001d25010800000320b05168000800010601c0307008482a620031040228070303101d040c108103581c1c8030750060301d0384909400c14207181d54041c500080c480301c0c00a4040c8880c40c00000070398400c021807480320301c18030034083e0501810180319001c0c031000c0e2040031580800a2204400803c1780d84284044c1c00c8400e1040c40150303208010f0311816a50b445808048020a0316520042061000f0110040001e40c00c00700200c1480701c04140800501400d42c400c1c2ca400380001c90180045550340158810310000034800150411002440c0030306960400061050301c8a094440d0039141c5064443c0d001110020498500d043d0003520605c11650044c81e070840902050070000c00250240503901401018020800e0030540118024603000c092007007a54828011840c001402130000c0c6000c4c00e142010401700d4015140300d42c0301e0382c11080030050903195030741440900c0180200904100c4582c0750014001e00012526a800b0001e00d40f0861002008 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 825306106 1250 825304856 825304877
    0x100e01020607020f03070204020f090a0f0f0801110f1e0c031216050a1206030b0a1b0e091317030405010b12030c0a080315120c010f0e090402090c19 65
    0x2498910700610500c00c54109a414075a400000301c11a400150102d9000d0303205c01c007081303244440c0d104001d641076104141c11000100112100d020400301c0d022056003240700e6030765003802030980e8590504c41c5402c21040010381400070344e05020708910740e814003054180070141e5800b08229030100022840540c00411840c032014a00744555600880b8401c07c0c1810343c0e1030081c064014018011002d05010640740e0302d00d241300565020303400454020b0540c610034140030340514000c10500d600780300360090032602c10501c6400768203610f00380c40d4041e080314029600c01d4420041814580c3c81111604040c880d00084c0b103401d000914051030290000090400303041007007014080c58203034030b092260014003180d505000007285810740b203900000020790b0b82d0340704044400782e103180c10100c42e4000c1000f10001d900c0000050000c00600d03003030f00e480b488003112a000740c50940ca11254903a0012100001500505012906541180300c1903c094240400000c00f0081151a52059130004007240c20 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 825307356 1250 825306106 825306109
    0x50c0c0c0a05092a07060b1804021305060114190e090112120509120c040b1905040903020a0c0603090c05040603031205061203041404060503011401030f030e100e 71
    0x6640c0d2561003180e140880c0c030b00c0c18022881800000b4011804021310b00208507070f5812104407104c54010750319034076070b603081185000c400030319004500a0103506500d87d200003080400c65084c4c062a001071141b0315104d030241e0310740c01506004101504100d41e00c1a103409550300400542104a0a0044203154014201d0003d000d4180d080c140c6215110002c010040c13640c0000c03c0340580b03030300009942400b1140752004e54241c4175290145401c242500f810103680040400d0074803207280304840a00c0f16440e0001005070b081d05141e891000040c0240c410412480c040c0c0c80906554403c0c01940c2d00101c1a0f2135241ba011510b50048001c243c0320440581001282c1c155a4040c0404807420420380e415500c00505445040e41c880c81a81d64440100b00d05640342d0800550340c00c00182140d40e696201d800d0040048584641a0700903030070141d0101d05440c041c028201083c54105690469a01e1604e07048500301501c4429014012400d4028150391608083c4101c22045500c07207084941c0c4190 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 825308606 1250 825307356 825307363
    0x50d080a0c030e1e1606050c0c06070f0f1b060804060c110c0111011401030c06030c0305160f0207030b0109021206100f140c01020d1e05010608070c030504330203120103020409080d050c0c 82
    0x9c100502c128020041900003a00780c0c81d40c1483c0540044680b21039114503c1c004c10000031001d501c1c49140d01c0901c00183d048d51055040784214485c482c00c1c000c800f458041980c3c0c18a84000e090b0803038220602e04c1c00e081d442104c4195610034054004111034401812541c0d804100b80c100307590b541b61000080c80030a80500030120308031107a140802c0185031030b06032000d01d030304030040c900d080001c40300050400303610800c4980040d42d0046c0000d607155a48420020096100008481c0e07030040d444000f40642c030b031014107185d1010094071074107035000003060200d500c444541d1003081640e600744034902140b0703400d2020741017034610943c0018804208020701d1340b401e551150404440c1f400c040052008540c0804095004800e5003880c80c50718180f441e09803024000e40e0080b640034500d00e1018203078200d0038411070f10f0002084a01c10000703419044120303245d103d411305012840094000400042c10030750320154409014541d003d040001680600003900c40c00d42d552106c902d8045081c00d0355100c1030 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 825309856 1250 825308606 825308623
    0x1c0603030906021203012603070b0a021b070f1a0412050c0405130c0506090301020c03180108060102060f0f130516180207021e0409050d080a0c030e1e1606050c 70
    0x10019941075615042802200d4215021f88401078411403040000820b07041043c0d0307040d070780c0c80f5800421528056405c900207402441401e080700490055000c1064804158402501d00500046804a0802041154011540c3d8907190300550403c00040c0322003840c20f4801260b446000170300044088401000251a00580381840200e0f50030304200001d40c401c580302c1d00300c0c0c100b510069101ca92002c00a0b0090207015491750640c000099101640356221001c0d43c4d800000343c80750403581c0c5503403004981d6a40111035401d003a01c640b40100b04500907407840c01e540f1200e00b0303645110010a61380c1d000d00b000384110341c84041001c60788040c440a00720f50020401003d910b4000c505102c15900080d0f1005040041000504180024100603446e150800c440300c68016046416814100c04010710b810030850f0200b1780c152418810011580c0700e1300494101ea45003800400c1448900412080c00e510b40a10904081c42200b2090301c101140010703060040035140c540345d440c2c0649004050401c0d114 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 825311106 1250 825309856 825309883
    0xa03060905060f0409030311040b0c060a0c1d0303070f110102121e090406050a1d0c03072f0d050703031d07171204031101020f0c0a06051c060303090602 67
    0x104400c201054030b0b6040c03c405121000c56012a911305241000d80c020304000c8000140000c0002e00450318651000003080c040c8125821148143c1e50b03011000215041024407000054141c0110000b2041c0542030f0220858004e068a00e810080e42d5021840c040110040700c100520b030341208510340c1c05012030ba076811000703081e4520701140380240c00c0c801c0c104580048400903001c5519012507c45038001005080c029164001251b05d80074135203600400c80c41076101d60240f1100042000d03140406590142c856622122030221001808040100d43d80407074030f000c6503118141d00d40361882003014400700c48164131495515015810024280c84440300342100b03820f607000d1100e000c0d9100003a17481c02c4501d1812502080f040222806041c100c181b1341ea5031200c2c0700031a0120a22602408168003c4400d8084401020091000ca0340728031749034403c990301103003481741001201d0207030000307080100402d1213401640d01400803241c2140c52581042c3d0008421500c180f003a15010418070007110030 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 825312356 1250 825311106 825311111
    0x1a0301032003031b0123180a0c080a05070f032d02100315080115091d2a0409050c09090c0306160908060f06040b04060b0a08090d0302040b1821030a030609 68
    0x1588441104411010781071f895052000e080c0e0080905080c07080000d05540000d0000041d0303929070405580350038290b07007903440d4042d442000511001d1005503004a0341d104004070700034240818041880c01c02c0c0c140c070355a201784800181c4d006980b00051403100f21816140090350007440d240c855041111500003039126031510034003540c1c0001c1e950720300e803c851070005c02240071074483d1a40c0c510074a0031780603c13165101e0003c165400c0c4c8602c4000d43d6010410025031005810607404000c2503507202c49000e04180c008290416040c1001c11050341d010100078200d406050105c0080380c90701d00c04a80049411000c4444808210b9204000074024007200000b80300078280500c004d190b03818090806c40c4607566580400ca010b40312900400020030012040135200c410001014040180032200c620303280c0143c0b020b00b00054002c1c42900d042d00d000031a030501746510810310712402c3d40000c000c1503004541c481b078103181d207884c00142002d58109a000d50f803a41d136800d0020307041da40f0300d4011510660 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 825313606 1250 825312356 825312401
    0xa0e061306110a0818060c1506010e1005090d08090a030305090f0301090b0f040203150c070201090f0f0302010e040905010204080a0b0618043302070506011a0301032003031b01 77
    0xd507240292005140080d40700101c1c401440000346c541e2080700d420404500564a02c143c101910a08151260b0001c0e02c2d41c44904040204102000c00b040c00070030046074040c070081c0441d00b00f002020301d2039446020079034079240100300041c214004550044000a0001a000c1301031b080001404c03007407000580003400704604903034605120030307001800e458043c004500040c0c20341d64100498000f101c00001461510304004040d0340703c55001f1131059010501e5480b000a00d5806e03418182c086401c20a2038081329401c40d40110b900405e403201099101d600d640a42d40451800c0c030051000b408440000c0240070401c1c036003081428001814a03100b13099140d40303101284484554584c0c4140c3c0907042d2240c0780c1c0e44454180c41c0c000301c40400d0b444114a1322521202c00481d9004046550051003110040e030b9840c4950035407000705401d850203109052004000140000c0706001c0032241c3c4001d041d081e0b06c0c035803000c24515049003013448142c42d22002c00e80c250700828400c0307048580c0b8100c4003000c1034 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 825314856 1250 825313606 825313613
    0x801020418060f03020a03020d0623010e0f010e15030312010b1e0a02060103031b0c0e0118020915070507081605040b031c181206150f060903080a0e061306110a 70
    0x40300f5071f21000e03000d0640e808207031041103801e5110b500d08a00d40100801c40c079407440b41d00200d90800740165207207100ba40010586e1015203280c41030498981014003941c0b44d071641035203100b00380d81c020100e81606c018003525410080480880380a48050107a19442d5054a808182c5000c00c6803021b221900301009481416a80455800d0640f83c05081c007040904d80191f03210040480803401034008020060040307103918480144c54101d0b01400c100c0da29484803401e200c0c2c103c0c8070b003401280d4400604c151540d00c104203840901102d6000e88c054410f1b8550724194141440006e0360041c031607400103e414400c519007482003a4607050700350001d00d400101070960601d2540d200c0703044801e00090410b1300e034806d8079507825040944082d440d2800044d08030f2400501808913070a040121881440c00424a114004a20000c6650a07520306000528688404100340e000300908810001c40c00c0761950f05898034170081c40c0c58164a000c05000b1031810400800c80100350a0007941c3d50440040b00010 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 825316106 1250 825314856 825314869
    0x6040617060103030f0e090a0b0405090705030a0b280c02010c080103110d0206190810050f0105030703020c031b030d111819030f080706060501050702100f02070801020418060f0302 79
    0x55031380c181011143c0348082a0140d600121a1003402c1e03104540f00f00704406c88040d40c0191440f0300c4291024001a04ca844c03da645804850081035003682c06100e011000c41d0307a07041c0154001503018a202e00c2915100e00c241d00f400c04003540855088d8840340f00103001982440b0703410f072043c0d8620f09401c1c0c550469480308200340310042000e205984400c011340c00d65803807404443c0001c15032004d070040303040f105034081e0407520116544001040ca180d00002d40c0e00701001c51008a140583d14581307160707643c2d10300f0b80081d00000883d07103580c40280003034000030a103041e00b4045c03122000010754a5080c03a96601d810fa42142404102620042c88030051090500110f0241000c003101c1c0c164510140c5042a641741402c2c0c0d10241071940c801490000f44041c0c40c004040781030150754180515500d400042d1410f00c1150b8000b900110b0301e10f0066501c9101e803030754450140052041d2486143d862440b1400c2e41c0103500204001251003008034581046403003000020919401034000c501d1554001440 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 825317356 1250 825316106 825316109
    0x21201121a070906050a12050a09020117060f01050d0204050d080c0607030c0921050a0b0f0a0204143d09090b060a0513030c0906031a0420031e06060406170601 70
    0x1071017000b00348510070a00840c952910641400d004100703500c1d16130010000f600c10004168042254444490f4105121249591182d0f0340034081d4046c075079942c001111031350b00100c13580000550a100105142d51103c013000c0860703008000560300c5681050006050000191090050524202c0e241c0c50340c54000c19410b085820701110300d5801c540c1102400c860115042c002025402654100001c001080003214090602c1d50402e400e650342e002c00c240102d2141d4000c1c80020b50030764018000b6490168806500c940c44003091503034040018040910000c40c0c6040c5101c3c01c4103084110181980c8452544c000b481c2e002030610030000f030880400c0c01846404501010081c0000303002103d4006045004000d503440442501c03c242d986050304003d03c400e0108039402c00c0410040da030301e010604403550041d5000600c2c4040c1c1009244281d441c010424030b5903030140941d0840010f41d02c04072a0b01c86400c0980c9010740f1303030340c64100304200880380182c02c44100215201650502c1c0c03080001d0203030 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 825318606 1250 825317356 825317369
    0x8040902210c090d030516080d1a06131a12041101020f010b150d15030302030717031905060406080d090e09060405030a051e1b100b180406021201121a0709 68
    0x390303150b41c107030030040c042c07020081c001c0c141950000314801c40680e241d024100c0e000c4549803e03c105842c0350300300021833007000a00c40e07001e102504203201c54656407544161013010740820900e001c0b9211200100c80701c04440507541200b605900c41c036196014401d00100144010081003e05490030020360032800e04a400062644082202c1c041c2d01c00980c40041d620302c40d40100111507503a850006c0d5290300c00c07201111820300c01c8a020040c04042816240910f03c010a0140e1842010058100404004121541c00780c0c0320400021101c1f018071880d02782031a180e0303501d0f070001e050014400015402414400e11684003070104404103001000740d0704e11101924081d55901c4082800d8603400302c20498481c0414000145240d440c0c0b1004c2810451001d400309845c8a140c070320020a08542d01c0802994001c00742e81040b83c0d07030b40000880b855200e84a8240103040c15101044428042030903040341400c41c04488801d001e001c20300002c0341da509800404c644282c548560004e2410110744a90b5 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 825319856 1250 825318606 825318617
    0x306050901060906030b091c05030106030b030726070807050603070c060e1c030c080123180c070215090102030d111209102306090408040902210c090d03 67
    0x420000c020b421440040c0702d0000240034a80e20b83c144401a85000d4481580c3d600c01c03c11840c40f8481c85820500c4540355036112075003140e01e445030070307406403481801c0c556050042c40404211486c609110b100c41600c1003810301c003c0d00220704494940412074120300c3c075076441158200819640c240450358001c50740d2400110301c500500d414400341452214900d01402041d600070450034500c04400d400406039a03042c400a058244140d68201d0207010392400b801c03045815095040f210000d8510016000c5e240b00c1c21455105840036140d0010390703000100860010715101585040c90b01d14822440f08050285001c0072480042d5881c45220300d004501038452252848004420099803500c0d01001200301007482c044040f107841e40c0340200040705643c40d10b49403c81107005500d850107080b5460852101c2915558100440ca183c000c0007142e100c0410800070a85a0460028092511188444481c0500040c181244006000303103503220100b030a101803000c1e0b6032088074110303403d034150421 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 825321106 1250 825319856 825319861
    0x9080702210d020a02040b090402030a061a030f21030c0423030d090e011a0d0b0a050a0801321828050705010903120806030a0c09141f030605 62
    0x1100d80d203074001220049503001d8a2160a0300c590041201260244211410004e00c0140401c11460030740c2035030b0294250740300b901c185002540c198460014081141100d042c0940c503000040c0c50140100c40203c1c3c10341248658004940d641d480301390481c2034007002d0742c0c00e5160050b04046140214132442403544404003105501d040303000700d42031a1007405400d442c2d00d4103034040090841086481030030840a5010300016040146156031800703480e58161440c50584c003481488080c11014101c00d6200390070b0100000c0c1680d81e2080348000346a41030001c10200b80c400003215040000014503150072600d96a038081035582110003503030008074402a0000c035007040b68000d2500e16031400f01d520b0788042050382c003c0403142841c051951441031080381d08080d200c000440b0341a400e48002400204200407070203441e40102c0c481a40108080c08554812503903484550500501d54044807030159946010303c84901841201c41d404440b1407000b6940d1155541c1e140010503151102914103a0345201 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 825322356 1250 825321106 825321139
    0x6070206010e040f08070b1e0606030105010c020409060e0312070201110f090904061113080f0f0d0c0311030310090b0a080303131a1602250608130b0f070e030109080702 74
    0x20345a051f40c00243d6054030b40b50410b06550400000c03d40d21140144040004141d40b9182044070306a90041c1e5940080742e4507682403002500110b2805c0700c0b1142c440380030b203401c00810005031006182c000c01c83d2943c1d00b811440a400c4400d81c04100e840540100100016500c50408503907500209440c2071101d940d942c01c1410091242d410a80b04d902c2c0d00180500b08103d20440c0d0f001601c0048040e20030700c410075070721541c0e02d00d9120307146012500300b50601740741c190144503800d00d01c60090400c0144002e030a4261400c6910850f0203c028002000d400d0160030310501c00d51030122400c0d5501c4c01c8a45c189109140d43e404024400100422445030b102c041103007890158040182c042d52003011402d00920200401d07080060f0140148200d002480c07409401070040c81d1041350f002c1c1e040d1030343d50800300c08844102c0014019044c3c018110f04660019000995003131180307101c00040c1005003442c200c0113002884e10341c005c034401d0b81008460804200c00e0000c5401c1294100c80170750800e0f09000 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 825323606 1250 825322356 825322373
    0x1b0c012c060f1207030c021501050a0b0a050712050301030c0605132715080105070c12080a1b080f070c030206060603040201090302060c060601200c0409030203160c03020306070206010e040f 83
    0x602c3c0100102d0742414403540c1c581540008107102c1094099030514045000e20818140c400d00c2403c3c2e101c07040c0301003084480900c0c0014403203400d003403402e07d2400107103480380e007140b003450710151001a0000004205000690302d0560150083c1c0c40c0031407525103103610f02c030602c182138060802403002c9591070719891101100b000c00a4188540c0903ca4a9018416408a01020320461855500344400030b24003a125110100810f0740c05001629440c0c0c28070030860326010b00410201003a55162074040003074412030b4840369000300d10303911a042c518007040100c0e84514041d29400c14442d80314140f400082e000b08449611102c269011900c07650b032030004039070309203407540040d4000300c0001d841140d0030004101540306260a0302d84030419003140704284031580500c001041581c10010100c0030510342600004460340c001d204890420101100f01c1c080000c21000c00c8070a409010010000c6090900000b03038852070b9400541120742c54400f22a00e01540140000c000c5800070010204003e40007 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 825324856 1250 825323606 825323617
    0x12030117191a07033809040503040303050c0c1e041d210d060b0423010e0103090609060e10150e070f11070f05030c0409020a0b0c01021b0c012c060f 65
    0x5c0385003010fa42c244403000441c14201040f079010003418106180030b81040c00c0b00b1070103150710000451409245803421102a0000d040f1004180114a0751403034966035207091a8044039500303002c82ca254440030801048400b29424408800001e4026004d4502c02203403100340b080c00c81540e403c00075191268402e2504c00d41103c1000e691415001040801c2d15102600540d021004112460790000f49208294000c0c840594001001d800020380c8652280c2c005a090922910003c90b424005903034035425120581c1442c01d0990080500c0c082910b840c0c0201e2a258590b18107070740103142070417440300c001c660040c1b0890074081646019504644034006000542c5550b43c1a11900d41d00d502d004006900e091264030302c60310909001ca201e502c0d01d4800c0c4094a80e008052120701752901000600a80080c14101c0f0903550a0141000314403210714846001c8038101d01800d500031845002402c401440c0352194214255050b983c138500001c0e032828101d200c0c044070840e480d450450403e031054800c8 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 825326106 1250 825324856 825324881
    0x4120e041505041e14060306011a03042a18060e0103050604030c0201050d180b0c0a09050f040e0a060f060b130302040213090903230a05030c0c12030117191a0703 71
    0x10459519020054003405d2130041000320140c0724141da81d40313058050481109008402070b0020008540024120f1000d000d000c0c18a800c4140c803680c181444074500321643c2d20003041d89800221140f1701b60390794891a405080040b1402d0015419926800e42e40ea2000340000c080c0041d02520a065a0240703041d41c24022040c6400d100e4480c41b2200080030003028202152a5000c40d1f007c0341c0b00c16010010f452007180c4654070b0209030b03490136003080b9004445a84c199002503590604020340d41007031004130b64143c001c4001060200c3c90080c2081150242c0c1e01820070345000703011814070110302c111400d003240d8040703c0160700d90340ca20070b00700040961680300c0e0702214030701488201010b8019100800907409040e02800710680d0850440700c5128000b641070006104000285c000c2d05400040c1851340002012520781100d095580211a8000e800c91594909080100c5000003010420304420380c0c001c110100b6030010301d51313440b8170300d4051801c40c03000c0c0a948070000704058840e50154403170317060 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 825327356 1250 825326106 825326111
    0x30206092e020304020a03350f071101141809130201080f19020301080616030b03070506070f0804170d090e0c03130b130506090c0619120504120e041505041e 69
    0x80d0107201450103001801601d16140003201402d000708e0000c00f5940e0316150443c40d50702d04001503403030292101460543d6818001740c000c421a40c1079120b00544200c2c040414202113410041c01001a1000300800c1742000080c100c00020040c0d81c00081c0da5001400702c540741e07039640c0f0344140c030440448040061480d094400b00000601c8400003a00c14024581035040100c146203070f92080707090b544070201036501a44840070821441c00e201e0024500c030b6004003640d984400c426aa0385040340e006c1d510440d6805410f41c1241801e41041c0303d10b080d4400c0b50305181c0f045611b00000030144100083c0000001c0c00040300041e542c0d01c94000d64100d50360700c452040064a044a8040c1e0780d16441d0505803043c3c031512000500c20000050707880d0040000901d0207003000a2100c000d0764107111644803000b006003e003200302d640c03d004e0050740d01451151080da403a2140308d50000b8254000c070003c00b4480c03400d1006007200303032801824203000d0b25415940400c044001001e1000190301200d8a40200791 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 825328606 1250 825327356 825327383
    0x3031b090e092407030c0c02033a0c0506070f020c0108061c06051b130e06030313030b061206060f01120905070e011d0106020c09040c0e04030206092e020304020a03 72
    0x440c3c080c066071150030182c80410662500e0f00307041701c4615002c0c40c0290141c1c0320013001c0c001c50740e94803848580400d6204504102062107041840060b482c5072030000030581d0340715031208000051000a42c07240f954582158500c0307090b2002503071403020110884c180424640491010b1701d840da008803004000d00c80d00c5070118458075240008041c202c904922001c400f100c440085007500013100c0c5104407120540842c40d091100c0144841d401400480d4144004c10050b20407076030708420000254004da07905c50319441c2c01c80520440340c0e070a045280c82c940202c020800103665008852100c80320070b01e40402c014041c41c2e02c0200030581024041c05502c42da881c005106800b568006041e20031f541c18000b480c0301803080c400d20161080c05440301680040000c0400760171700d000314590140c0034400360744000e0360304c1e0311800b40d40d40c3c140c400341c4c010f810a00070007408188c100004005980a5040130071a840c1c00600030306000300082c03e003001d43d900000840c00b590b452141c01d0014542000151642c01d = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 825329856 1250 825328606 825328663
    0xc05010c0206180111031902040e1509061f1101021b0615060405150c010b060c010e07060905061606021b1f020708090907170702030703031b090e09 65
    0x50300c08545072000962810303c00a40340d0018003840c0d207190030345a1294250303100c80400c001c08075000d41c1805460b0b5402c0c40001440800d203400e0781d01038107100c011500c01e14040340c2400491040100424041c811219014401640e40320b018441c10350a0324010300c40e0225160b2050180c4100242100070010314260b607003003440003148181c001e00d004441d40c01c04c400c4e54424030841d8000c078403441d075204072007903500007050840c03c000f002040300640001482008410001d01c0a801c1a150300328a69541c402d0013030700110030018600071300071504180c0c0c029464200002c80c103104612007800c410180524040c1088a540c060b00e401017400041c100c00001003e22855648940004880900340b03400c040a06000f90391084801c001e40082003140b81c20024820b00403400e10180900d0f0402000194203a40e0205190ba06805440141d000d16503440c410b00340182aa82c0480d0004058221558084000b680128140c4210f4494066181c4035070340702d5000d1420081e103001070b40803004480d0001c3d0f252 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 825331106 1250 825329856 825329863
    0x10020f0d0e03060a06030804060507050111040b0306190302090a1107050a050c090106090f4506060809030a0305060d0507080303100b0304051b031e01020a1403040b160c05010c02 78
    0x28070301c0a81c00c80e00f840e61902180800c0c1c40c141d21000d840d0001c1003005104040c403c4c80200050323070045e0b00204c0c000e0f01014141140d07902c1580010031842000c001d00c5840d181101d400540c4a010405050480e41036400082c0842c201805c645201940d412101c81480459419250103540050681d42244081c0c2400c0741c07203c0e401c20b0820721501d201400800d07400d014038880300580b4030041c01e8510441c01c00320300500140c816488103040079011a8034010041202081c172104484919000142c540c10710004401e940c881d820180074054008100484500000203440c40d440c1146000311b4103407102004500c4002410501501c14018501d001c5421107001004502442004801c1017025540c2d01600b030807800142c90003480350b04203d038080c4507480d540950b160816402000d68100c03100341d4892003502584031031454540e94010810301c10301c4d0381000f03002200710b03031642c0440c1ca14981641c50340352080780103010099040d003c90054080034070030700c0200e1006901c2002000007180d10b02c8040d41d03 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 825332356 1250 825331106 825331127
    0x140c030709031e023d05190306050a06050f0f0706020c3f1e0f0c011a0f01140f09150705160f030305030a0e070f15080c0910020f0d 58
    0xa8002c92411403d1440b140c50360001140e9031085c0c0c0b040300c0c24901e40864094007444a82c02042418403203102d038603c0b001100300b03103188182c9002030141d10703141c02d000c01e4103401d070300070000e116060100d0144c0758540c1e002c461091600c0c1040717580e02c01d068030f0084000c0c003a940721031120307209038007a0240c00f01c000d51a02c0503400c29004d130303641e1640c00014406903090003c000310003100400d00001e83e40503003150803604c903000c03403401160810009043c0c220540d0061114040309030344400382a50343c00c016050242e840581500c449503140883d0001034102003003010315030748169001455640b8801040e00341c440071b1341d0081400c2000311141000c02e080740c01a10007601c450186c0000203004000c4002c1000440340032020b5034211a03c1c51314180c41d40d4000030300400b5802e071900044c541d406400c0c0304040103420110581480e544c00c241284004003040120740c0203104007403042c0142d07142540f050f1000080125070340701c14107295030000c030f0401c00c048100240c1d5100301c201060030310b0f030030448024 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 825333606 1250 825332356 825332359
    0x50607030b0d1a072a03110615060a0201020c030a1d01090e1306090203030f1c020f09040b040b09010b03012306030a110f03090c0f04140c030709031e02 67
    0x1c46200703581c040201201092500501102d40030700000916200d040304030f0703884a1103080000091604040381c0c070256050050314036103511384080e003204240d004100c1d503200c0c40400b0f005090516040100325000c20140134000c2c4640b40c08641035600b18801d404440f540c50000303050320344408103040082d0005c2c2e001066040208210100c0310440e521460b4680212141508500603580b0b0300780701024098109041600c2054980c1c54000141c0c03000c0009000303140340480c580760b49000c8108170411980c000d80c8000103503030041160043c4a02d03c0d105881d1a10303811280001e00c0e10316540003900070440c074060b483d00140a0000043c101c15054040c0d4101c540034141701482c40004003a0003417000102c05142d5220034103002040210380281e00c41410b11020859091400640b0080b00007240c01c1101d00c00c0003940300e00100f80f60307820f182d1116503890b407064400b403029504445040209070001018102100000700015212500c0340c811170000b141c12070b000329000030a5900210010b1021501079 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 825334856 1250 825333606 825333611
    0x60206100e0403080114030709090b0702010b0a030c030222051603110a080109020306010207031a1510020a12090f0803030406050601080603100c0c0c0602242403071205060703 77
    0x503007042072491040c4500c1c1d05640d03143c80f507800c00d0001c1480142000b61650141305000b00414000f045101c1d445880780200d13010700d400d251081009083d106d10059260281c2030703408041001541401848095981c100d4508242c4501020b1300c818180e50000d1f5020f6a9040600340504002d080d0204841024150341c02d00040b010700080c4085489038a40e4071000914040040002c40a950301440d0080c2052069039032855a9440e4450030920071448072000001403010f00104510349a042c506a000c20b40b00074524140c4c0d80006034a40c107001001030100340c500d582040e01c90340324401100203400148c03000c08100c1e84495946035642c00444044428500c2d0070046842036010b8502c803803007210000c0091035041044003d28001c1d052008441082c0440055010000b80c0001e11340009800c46900400707420b010305d40c0011580581080103101240c58000b4004035840c1c00c100724418032203520180d042c0b0340e4070320702180c6405100d6208003410703000d0354012420000c012035124014040355a06 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 825336106 1250 825334856 825334859
    0xd03080a0e0712020f06040b0f19030c0512090a0203030301060f0e1c12180909111e040c02190302011d16030609020f0301050703050a1104031a040203070b0406020610 73
    0x2076a406a074003c0c55861800300343c00c500180750107403c1d1621004c016008a003043e50341c100d0b940d41d035000003210601d107900100b0b4441c542d011040318605074004914050209016104020307220748a05007143c225036000e080096400c110030041361440550150880c0d85e65030350381200030003030030441825400013036036041440513502d4419900103260750407810841c81c10b0050354078080c90900d604ca059081c844c1c010700c540e1503038202c502d54000528600c100800e03c000742d46484008800309a18051041e05010031501c80007202e91000102054181c0e000a030300c003113444c000d030324058441151402c0e044074039098608150307040d0004068424241c084038018450b059006454803101c080102d20014020300410110b00250009070186001409001e046c0310030001007425a00200c58840109855070203001403c0d003039201e152032a0700f02035032081c00c0505645d103604403c0035040f400b40c000505500403030295030702801098002c152000001e503450795600c0020751034801c00c490100d100c0209000 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 825337356 1250 825336106 825336131
    0xf120c0f06010b04060c1703011409090d08010e06120f07050f030f100f0e01021909060c02090a020d24061b050606041a120106181107110d020d03080a 66
    0x84403410b940d03e401c0042c0c14207050040c00ca0352001e400d001581c00c503481e950b00103006058a00218068041c0380e0541c443c86403500c040c06a0820040c01494440e8011110a03400f01d510007205810355110b0609984140c55080005224a106281c1280d05001e000d01c80444808009400703021640150759013900c803c1580c042507200c2c02040580368040c0c12840d1354400c0101c1c581d000c0c101c0b1110041e0009001d03c0d0780320100d42260011643d03003141504125400311801c0c5c005820b28014046843c000031500c0c2503502085110f078000d000301c1c03951900844c0400050410740c0080c2d02c1c83d50481c0311110042c085260000401560f4840c000204100c1701720206440e2800350800c02e03c1e5005802070100e0f0721110240402070151348025040c0311441d00080e01d45940308603118040056030800401c86604101c808080803403101b1326000301c0c514040400041002076400e03240901d070013140343e22810070300f07102203030510303a40c040c00940c001c2c4c0400103101007540040c1c141c1e01038000b01d80204001c09441e170 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 825338606 1250 825337356 825337363
    0x2401090203010608071101060b040605070501062705040c03060905030a17061c1113020c0616230d050c190807090506070201050c0f0303091911060c0f120c0f 69
    0xd03d40000c0d1886000481c403501031200180715a050000008005a0710303c19055150096007003900040e00005031801880302c24081c850250086020304600303840c90020740b940304002d107070107100401c1e1540001800c1c002113404660017540c101e241070040d2915494030b65141c0c0d03c010284004160b10405078800700c00c00080075441990082c081945c0880191044040c400c0b0700001241e80480c916000d4016840b21170080c0c001d40381c1000c0158550007110481ea0903d28000d0507602007040c000d510792000c1c0d5104412480300703140c440c0c1480044d52414041c540501c12010211a02410300c0c0070700c605040f0700c0f40100003c001041c1080006c179546d4004803940324058690900203541075005000a14000d8024081c0c41e20504002c0e14028035074194904100711a0445142030708084208900d85030700744507201d210700c40004121030483d800e41c0c0d0701252901185840d40113030000318400130145003c00c1a071400f06403100c110341d40d04405000d043c030701d58804140c1180030b0042400400c65a44c000 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 825339856 1250 825338606 825338609
    0x2106070314071d220e1e0307050d0810170a03030b09060d06020f0903060a0b030724030203151c0c0902090105070809180907030b0f0106081611240109020301 69
    0x10801011a04030f01800c1064103040701d4505000035503503000040941e100d901c182443c0c0545c190160850b02e800804040d0541c190600618003034108009010024401040c210300d00c078094101102c0d81d0300c5107241601c0341180c40c2c0110102c81418103e020040034001010700d1054071a58003841400d11400a01000c1e94060724119000b070203c141d038200092203500034142211843e20311504104842000900c0c0c0b0505981061140e0b981d10402459400c0c00d010b4440a000d402c00c03c0001050440241c4104540c40100740d4101940440425030701c0d1042001030321070180c0144a81030500115200040010032104100c600d80501070000451aa0724001c3e180310391b1058545e142085110344550000d98000040750b0761203115403d42803407120058090310b001303417548001880001c1c00c510b0018800440a0042180a000000104242130740701e80b0450740312050034400002c46a1b400419214183c841a40c1c4105024482e40030986480c0c0c0140602980244096020240d90f10228602203100c01e = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 825341106 1250 825339856 825339887
    0x10506090303070b090330090c0315091606050307180810270b1b090a15030e0105010602030c010f0903200304030206120a050a05010b0405210607031407 67
    0x20f01c00000800c1600201c1a408031004050300d14140c0c4654003c0189440600803205911410003908001e450b9041030f0b66220b00b4500051140200100000e540d5a82e500040a030341d0684400144106609108c0d00381e0500140309503801064039413001410341d810440d45003001a400c031101000b40398002d0f07190012640e615011346000946820074001a194103080300d07007071000c02c1e804505424800b42e541030a40c0d0007854054194140240c50041c100c800c202c0c00c103074845050010005c0365983c101000c00b01c4615801d0f040d1101d0700042c05401a180b0110a03200c030394603080000074815000b20041810901400003080045c0c500075240040702d10240000c0d000600c00822411444003002000c582c04004104480c01c7c82d50307a5000400c140d11200c008000c1d12044018052860000d0103900e421580c0002e051100d5810315201250500a522925201d49403404103000c810010170350005c40c4400390b809031540e074039045601902510030001d5615481c07940d07c002036041071250800b180300d04e94 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 825342356 1250 825341106 825341113
    0x702011a010816111b13050103230c0d200303070c06031812030603150905060c1602090103080a0801240f032702120a03050306120a020d030809060105060903 69
    0xf59502a407403038205049011060142941e101c100304001081503941880c2c610f00840030740c0c080320060100307050520304540541401c000c0180b001031402c1c900341c0791603000c641c000302d0181c1401050501d4440744007855600011049401d0f003d00102c125801d0605104160705c0034101200001c0c560307240300e180303000b41a0b84203d034410b000e035612a400000641e00400400d0841c0d60b41501d9955115401c114504040395458408000304030410311500c520101c007a008102c0b081098980503100c003001407403e1800300d80050483c401d480c0703801040342000e40140481c0f442c1c0da140c3c0b900d0101a480980b84101061542000140e00b10000090140c107400c0038100006c1d10002810584402102c080c03090140f580302d10003000038038107404c0800f00081d09820071604002090050210041c0149144c1a480d086078000c500400d40003021207801c08000d44149204040016441d400d044030401c00035400b0084407400001d2507030103c01d09008407810801d0b140e10fa641d4a0030010300d84078050b081b6030140c0 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 825343606 1250 825342356 825342361
    0x506060a2f16060e01090311010819020c060103051615050904060b0f0a0314060315060d0f050a03030f1401170705030d12060806060a0b0d02040b120702011a0108 71
    0x109484240050700e0314001d24100310301c415941e50350030700703541c000c001110841c084010425150300103071841003d402070801e204006e003551101002070b48410f4000341803202400116000600e0b0584100040200d2101191030b942880800fa8031844e0a10090710b46100c0c40e0703440703101e0710b42c0b515480d0f003141d0140700d50114003d12144103903980d400c541a6254026625900011005807036401070004c002c1000c070300c981c2e03108103080281c2115000c0700184001c12300482080940c0d00c0010781005414911152103d080d520500000c1580740110700043c441c032040311020041080004590307004510907101031100e01040e41810b411164280d24442c0301d040c0340c4004015000e00700101b0400c030320442055440c00c0741c5800c0803900d0244082c1110f00002c45091a42407000b52500c41d84010b480798074060b08990800d08005494041a03018120b001440003908036078100a40c2d04032030040c41c501502d41d0b110590000c0710b0104200842e00100554205404006d40d10401060b07440703424016124440741d41c = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 825344856 1250 825343606 825343637
    0x807230a120209130203030304030309121e1b02281a12180f1f1404110a0e042102060720010e030c100c020703150203071b050c040506060a 61
    0x160004d040c0c1c1c02000c0a07940d03040c0140c0c40910003544103500a03100841c072180d0500d09034500c0108103450000700b100100c0e500504038014601118011030500d0042c2d901c401004082d030b152080e181c0b000f03502590210250304140440303130f1200c84940c0486045400582d0b290a0011419030320035802103503d17030070014813035414181064507410000c0070100402c00d02020102500e00035460500c80307060b912a000c543c92404400e401885500039408090200641080d0000b02c800b101074070040c8034000406032030b28140c40d40745901e001085580182402801c09040c0400310000742c0c1200c182c0d0501005418511030700004500e1301403d032960311800100311011010304031950811400d030341c075501ca03200303544005803c0001d4003064250030094403030700444010102c2254640281c1c0d5080d504680e80400c0031821005070313003d10152140c000350741c0c1d649001c03041310701c1500d94a50702c881001c00c0d500c000c1131050024004007503d0f003d880c00c2002c0d444010800105004001010f800507501558407a05c4 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 825346106 1250 825344856 825344869
    0x2071806080106050d11060a260a0b240702060705030f1c020901051b010605130506030d18060c1e030c02010305090105190e0a0602120f0c13090e070807230a1202 71
    0x7541007518109e000104203c485952034400d031014601c060711000203121003900c2074840c1400b880300c00c03590050025860107020138010201c556011803200003080080564580808461140780c0c05800d0300c1d07803180b02c10704411854108950003881444940b034519034200e214803c07100b5082c0305071200b80c10a207249409010000c1650311500340d5549840c8001001d0721010746038198811041c001140d24a400b00606181c002400c600c002041604004c45000d0445122490180c880528200b03038004c2e41414608030402c4000d01d040e00c00e0b24841c00e08001e06038416812900d182c801d0b0b80521040c0c41328020642a508246d4101d01c507924002a00307031a101596221b072010851640584160f0034080d200c01d400c0760000d00c2a0040030303141d501041016550600400e500143c2e1140c61401c03d21041002c00d5221464013a0504565039800d1101803018100201d000421010045981030340d1250104500b02001c14210700804e070060204c00c8141c50b100d0110001e462075141c140e00e4070090364003040030 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 825347356 1250 825346106 825346117
    0x30f05030c161a010b0a120212043f0314010605090f0a031e0219081507031805101406150a050f030109090308070201230702071806080106050d1106 65
    0x241c20302c0f003404007041c412100ca01c56000700310b031002c00b0b51103690304a000f80c11a50800c0b640340001e8410040702440800000040d0380244e0050840c103154407182e80700d008284410b104440401d2000c0b4440240d4050314030703415082610964050210303000a00b50b540c1c1642080c0140d201140082c801c41e127817820070550460703080340010715548241d5602e882e2101900305181c42410001040501401582010001c525051100204c4610070516041890740c4030081d4102c103805600c400d6020a030b00c1071198100000e62a10720404229082e09881c1c8076a80f01450600c0322805404c0440704161b044c0f20340c024920900001d007441c2c1d103070b171201300b40750005034003a051490130702c1000e000d00400501904003071400790083c039100245d510720703c1c10041c1120340300034021011a8103280381300c442c030182e0344030f00e0010f107140303190011554480c038400781c0c10302005070440c180b1043c0b14629071501c3d1540c0e8114504036840c00c0000c104854940b024040714140c0500d0190550540890b03405203400c2c034200074117 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 825348606 1250 825347356 825347363
    0x1104320613030803310807030804080415020c190302031905070b0a0203040807210f0309090c0c0c06090b0f0d0b060703020d12020c0c04110d0513030f05030c16 70
    0x181c15100c2da83c101d8640c1003901c26080d81c54140400410480b80b00d40700c1c120788040d0440d200c0804405a0300c0020500c00c40b10028200500c190203e4204100481030398050607020501194034088034400030356503a5241005441000940c1004c0900c1485001640c1a6070300070300074155011002a0f070401c80410007000300c07600c0c0700d00c01303002800f18040c81c0034094400080d03020b10340c2c0c2d0f4589101e00d0300c0c10200d500f25400e034058803000c88005c82c085540145d0115072000601000c5641400d00b95000d040070341c0001e40313081c1803080e0383c00c25a0788085107030107281c4036806600e00c058680c0d03001c6504100e180200b0ba90b24904001c0e007110880c2c080007030461404c900c0e8000c10201801d4000c15995004824202c1c0542d1120628021841d040140750301d801d40f002030214101541da08240d559480400412401295030300b2801d04540880b6089034601c20400105000504200d03100c40c04600940c2d1090f0001035402c8004a28148120200ca010b400120360884c14008544030110203180c901c00200c = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 825349856 1250 825348606 825348637
    0x6122a030911190911040609090b040f0501090b0307151b05010e19141b04180204021602030607020d0905010806120106321003180611043206 62
    0x441583d0702c0c031800f0210140020a800c0d0f4052524840740d0640d1004c0340201130040302440103200c25644101c0401c1100c84185010a4811314100880d0013403000020039a41a42841f0001c07803007039440e801201014000380d04403801c459880c8600784d00001321058581c0002d0030220b03030b41c00a43c5a182c100301e201c0d0141d40001071000e42c40c080d071440c00c203040c2e4a65101c640ae25440d130092003409a80c1010102001d00a0803081030610101e68040510b04500d503c6107680780c0b00d03000346140c0c515030131070303e20750203042199100031440700d80c50041c0d02c8000482c440d100d103030b0018000520105201c1c0400c0e496465a085d9141010300560342208010001e03034006041c00764010701601d09010340c0c80245061340b01140054202c0380700b5002d40740d0521601503140312074898101191100c003800c4440c10309a1070300150140d82c24884200d444200703040644424100b200440c0300101a40c010400c598ad880c0c0c0c03100c0401d82a007000d00c041c20307a504055005104214080c503075810b212009280006451220 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 825351106 1250 825349856 825349883
    0x1908100518010e180102070b040312090f0821090703060c1403040f03050f0d052409041112032106010311030a0c12090c0807170304140402090a06122a0309 68
    0x4c1074220f820000c0c00752100f509480a000c10f040e081b0341610850f01c0d40150a006d04501d944a010a88911032002840c03844006034450418028400c25144015803240c07041d0581012200d05030b60301d046000a40750b0b1841d200010f004c140c011240c200280c20302c95500c604564858480d050407020b0300e0760503028448204102c0402a6901006100c0c030001a440040c40d41004250390010000c0c007020300744420404107003a0116680c040381168420781c4040307600380f1080810b012506100003840c10b244e00f03220108091a95200c2000da40b200c002042c520302030a540c985004405407003460801d12010f0100b0030129194074190341000c00104110300340362058040522100b07088414116050b20074160015051006034024800305008010380709561001042d59081e181d00c0c3e120f10f20980148110032003400c880c0307231515016181d59000090580c0c008a03a1036002610304c442c90000000f00700c0c58030300008130445181358041c2002c0082c5185107a0101c00b40c806400030302c00704d42c054591b524180d41 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 825352356 1250 825351106 825351151
    0x10031e020a0605070b0604231b070309180504030509091f0902131401020721020409030806030f0d0207061808010203012405032a1908100518010e 64
    0x44000240440e6482580d50020307814403058800000e450681f0581c24004000144202c0968841c0d20003444081c001054807200006c420603a02c444001c0d0300081c1c040343c0340050540004100c1e00f200c030085089880390500f032031000c0c00c0b502e080301c00402040c001c0c042c1c50150b003400c254041d80b18070759182800343e00e52103074154180f0004907484a000f11b500011140a002c50700800c0c403000302496510301d902210b2900001c0d4840074035000700d0108001a21841c000030300d60b9401b942b62280c000d0020404034a031414000d0038036408031401e90080c40b0b08203401390000000600151407038145d60140400a040c0b082c2207a42ca210104c03108001c0f01003e0001c5800c3c4400c1c40190b000746000007040070b00b900c2003c1c54040080d070300400780f010320000740100000c07031a000d240c404070b084020360b5603400100201d607000524020707030301e40c40b054066207401d200106402112440c01b45401c2180c080c0d0040e0345008001054841540750100c10f0f9141004000d41c80400c040d66030800602039039009a80012030 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 825353606 1250 825352356 825352369
    0x10030509031c14240d081801090e331003050702010b04022d18010e1516031101110d050403021c210509030910111608100510031e02 58
    0xd0354246400302d94810900111401c503840b401d140410f075411600581340346c40e02c1c0318600641c042c4120b1101c03110302c80c244580c45600a00050124540c0c0f00000d41001c0603a01704100100c40b14101482d100100c01c1000703a8421100881e4100c0104041c98664141170111301401014000c541550340300c00f205039060707903140060001c41e0007400161201c40c4100c41982510418040400c555000411200c46aa840304e2868146a00c00b802c040c241d41040c0004140320604002c15540c4204012901ea244d0f04070101c0522483c40c083ea503101581c02c01070680c1400c982c40c2c7d00c515403500e2010003502540050b10b801c0641c1c400c1c043c0c0141c40c0340e14031450000100c0c0300f1800f41080014070111b07560500c901011080046101c5410042000d46011a1031039034a20801e0352061141c428403000014181c8200450014041c190041c0c9100102141c040200c038400ea002e0070001c2d010b14004600352481c14030500344240f03901800c420000f03185480d03c1c00300800e5900100803000d8422084405601c501c2f = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 825354856 1250 825353606 825353611
    0x605040e160306172103040507090c05070f052b1d06041e0e150a091d010e01060305011427120a0e030c01020604020f130609060603020910030509031c14 67
    0x4000f030541d8862403c045c3e08003e912510704043c82e82c0500500010400c0050040d007902c45040d4005142206d000051380c250048690081c0301e0440412084204503021401c0b03c041c08003140e440020b444600003a004501900040c0000a11558a403000701048002640005100070303201d5881d049e00c1e0710740c0035811828104d83d8243e446a03032004110f000407036403200358098404040010000c00b00800601d100315a44182c101840c1c5407001044805031070300700c2090004c55a002002010080320700c0c60701030085407109440951078512244a1000b15002c4a8400c5080820071b0000003400095060190143d81400b88144110428243d9000741400140060b2000ba100c0025210030502010710340403681140310b045402000c02e03c170040e1988500300814200c115600c1c084946002641001840c1d25400703512054102007000071176030b406034010515003505455010b064217036424107070162481550b20305460b0b482008070303c48a00b0804072004c442e90101e40081015085000c415007aa2000e = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 825356106 1250 825354856 825354899
    0x1091713210506090601080303010b0306030c0406060216060c02060a0813060f06140d03020d05032a0304170a020d05090a0518010609080d0507120e0904080904060605040e160306 78
    0x30041c4200340030040007826403084046004005541c1018046616130106102d05031820071b0100102d491650184006080a0805001000700c2582c0b0381c0000c0d82c07144024030a807205a55034501150343e03480307000c4080c14150040c000d90700d00314104504540b4244014a0f080301e000220b82c00e40300194a41c0504a484190300b880860500e041180e94524100391504d5a8460703180300c2e43c1000040c0c1c02041c0090401d2880c2010340e104d42e079040049031551610443c4058000c0c0900d0340200c20140781001d035010700e006104180017016002c958818622540c004840581c0c440f015440405102c0c80062140d420081c2a91807010f41d00c801084207480741ca00060324918240f80180002540f114090f0028100b8400404034220540b5028026104020001d082002d503242c0d4a004036004010801041002501c076000f18609402e048049030041d03400a44a0350030b12000255051044080c1c8041e11071001010f40d01d6240d0300404184000614441400e0641341c850000d48260400343c015018a903 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 825357356 1250 825356106 825356159
    0x2030325060c0e0d0303050c04080a0c140f03030301210602161704060e091b04061d0f0a060309050a0b130201180f05011d03070909031101091713 64
    0x600e10307240c0c00362669816604104003200034083c5407a80d030101040000354060800185903283c0d000c2000107071023160001412489a00c14800802c40c1403039035101140c00140700c0d0014000000100301b013092480c24040d5255100740014040c899018444003600e6a09008540b6203a0035942c2d00810790f049500e15451024003111450180040d04084004903208c2c1c03100c1134503050401c1e0014001c600c0d60050700d40500c00510004840342d1085c0c0c00241c113120140003050316141e44040042000713144510404070f0042c00b1074901000c0c1469510b110301c402c401070101800a080210440040100f614159101d10401110402142502a106008140704040142e881c049800050040c0c280d642145c402c0320001d5030308000036000041840c05031202440c03d03000c0104010360151480c0c111942940c1d050003003850003c3c401e0700030361240c1c1040e4402d4894240e884a401d80c95800c81c0d10140c80a800500000c0c00d2920158210008001d02c0e582215400c1070207444184411007031000e035444a640c1c21 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 825358606 1250 825357356 825357427
    0x90f020309100b03120d0b1306030309080706020d2d02060105150c0d030b190e0a0608010c020601090f090506131e030c020d020a0e1306050a0e0c0607020303 69
    0x2407060120b00c02c40151032000f405022070710700c0426652042a843c003038200502140b0098901441d410000414200400b411560740716041c0a0001b01078a00c41100441c0e044400080c0302e2030049010402c42d209600130340300040f41d00c072040d501c40c3e100e02da41661124003d40b06134100c5200c0100040d40b8010365009050941c1024140245a28110480541d80341c041c844900482c1001460045000d102c0c580410117510002c08107098925102d90504040541000840d80c050340e90092445074045150511120f03990b8a61907003203404200c4034030300503003126005002c0101c0caa040b88060013007240c0c2c000707910303286500e44508004003614541c1d41e41074042000e0f0f040c400001c0e110b40c1045203481030241d19400a6a0103491b03890121030090060318a0354820066558000d03050b0018804002c0c40b5902e441c2c502103015010360820300c1110381270700d09000700c1c0840c03142c0d108010b800c015001c02042c02010040c10401e0343d400c1001c00b2a03041c0f104004403685580314940f4500c000300030064650940c07 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 825359712 1106 825358606 825358621
    0xa050c0604050c0102060c0702010c0b041b0605031501020f0a0303110f0a0f171303030e07120804080c0f0a090c110303090d030615050f030a06090f0203 67
    0x5004080400042c0400400c01006043c001d078292007444e81d4412410b0490700800402038001282c0c00d404000040038040c0303441d0440d0107288a603803181410156000070111035001640050004400d005c000500e49100032120f282c01d0001e4050782c034914600958801507510040c0401d40c42e0750321300026010060490741261a484601981c80e014810058107180900c0814800211101c180c100800e00460006008402c0c1c850452070380750954074100c018150948003a01d0502448d0800103001c4142001c500b241442200030a03140c3d46000150f60821851070780703083c060304061545206070b42d03403440a0015994005000101241c98a0302103840078000b03040084144800014050514400900707104129495a0b042c1704107911440c004842030000104031012800034848035050408000185510000d181d90014101d07944003410010396010828401407107034000248000d2 = true := by decide +kernel

theorem cover : BRFrame.Cov 825179856 825359712 := by
  have h0 := BRFrame.cov_init 825179856
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825179856 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825179856 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825179856 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825179856 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825179856 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825179856 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825179856 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825179856 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825179856 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825179856 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825179856 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825179856 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825179856 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825179856 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825179856 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825179856 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825179856 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825179856 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825179856 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825179856 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825179856 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825179856 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825179856 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825179856 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825179856 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825179856 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825179856 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825179856 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825179856 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825179856 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825179856 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825179856 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825179856 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825179856 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825179856 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825179856 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825179856 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825179856 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825179856 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825179856 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825179856 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825179856 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825179856 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825179856 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825179856 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825179856 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825179856 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825179856 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825179856 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825179856 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825179856 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825179856 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825179856 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825179856 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825179856 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825179856 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825179856 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825179856 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825179856 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825179856 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825179856 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825179856 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825179856 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825179856 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825179856 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825179856 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825179856 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825179856 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825179856 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825179856 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825179856 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825179856 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825179856 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825179856 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825179856 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825179856 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825179856 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825179856 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825179856 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825179856 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825179856 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825179856 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825179856 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825179856 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825179856 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825179856 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825179856 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825179856 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825179856 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825179856 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825179856 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825179856 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825179856 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825179856 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825179856 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825179856 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825179856 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825179856 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825179856 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825179856 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825179856 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825179856 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825179856 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825179856 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825179856 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825179856 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825179856 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825179856 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825179856 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825179856 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825179856 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825179856 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825179856 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825179856 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825179856 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825179856 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825179856 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825179856 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825179856 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825179856 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825179856 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825179856 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825179856 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825179856 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825179856 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825179856 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825179856 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825179856 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825179856 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825179856 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825179856 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825179856 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825179856 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825179856 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825179856 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825179856 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825179856 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825179856 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825179856 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825179856 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825179856 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825179856 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825179856 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825179856 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 825179856 ≤ n) (h2 : n < 825359712) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
