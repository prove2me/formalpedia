-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0738
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T22:30:41.004773+00:00
-- url     : https://prove2.me/submissions/cc0b31f8-4644-4cb2-afb5-fc7ffc35b8f1

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 132553956 ≤ n < 132733812 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 132555206 1250 132553956 132553961
    0x10824010504021e03100906050a050a2d0e06040f141b0c070303031d0304062a1a010906120c0306020f1606060609090b030703231b04050c0403120c0305040306 70
    0x19480030704401010407c0048803528440d01c406444155515843e1508002c041070043c1a540309c1d001a0581d200d95600c0c100800f4039080107900075203031245494680e13480781c6900c4a417090760842e219078501800305c08071450301d103c5c10206041100c41413200343d4546c01c01d01e0700b120b403d0703055008105040101070740609040c000d003009540300e80c500040d406000754a900b4820103000e51401d8903402003000f400016045031100600c80340302d02c02d051040c207120300010122403000c070009004135000000c040305200c000c10428181d80300c81e02c0801c44c040d9505002000011403640c051700c1005810703428008104140c00500c1801d1041070031524204181500000211111400b940d5a5075510b00912149521441031320080102c45818402c2080e0007002035120385591100500148903810041011024085070186142d20402a140107200490064004020802220340711708d1a201c00220240310840036241500d0300601c01d4bc0804981e01d1095030240a03100082c1c09100c414400000090780342d0 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 132556456 1250 132555206 132555211
    0x30e0109031502031005010804080412060204030506240301060b0f0f09120f060606030f150f0d05061006050304080d020a0c022206140d0206030a0b04050906010824010504021e03 78
    0x1080044e5a071918240d040411040c0d9002103041041c0d0364103110124500c2c42c1903606492001c4841c510116151400c50001d12580c0d00052080c040c210820000c4001108103a0816040d4100e0401c5a240307241003600300c3d403040c003074407040060510801055030740701c40c06008908003281c0d0720341c5050f00388030005024035008042458598401b25201c40707025428451560003000545106045040080015880a4004041d800443e228404410301076440f42184074107000007408041c81481d450800544826044070b404130040b10b01c140014089214804a900c11500024a2800e180c09510414042d6110784055010007100d07001130700140c1e070b070810381041c0c100840030f000f01c068850040e00c1050301e80640c80609842d20501600d4401d84991480d40d04813907040390b42554035038610080d00c00401c10340382c006d904a0310340010032580c0a40015507506036240d11040340d40c2c1c6014070525030410031810390910759003507050004120a08154000d04600a000011000b80d0400c0344e04a11407078008 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 132557706 1250 132556456 132556493
    0x50306090a050706080709030210020703081b060f071403090c10110c030d020c0f060d050916231c02180601030b040b15070807050102191e0c030e010903 67
    0x203031801000410030003c4001e100b2803c0c065200e04c0c01200190070b02c0e2891001034040c3c000d40f42000b01c40f91081c071400014542c491320302900c90082e80ca40200141144001d03800600c80c0d500880e2800310040708481c4213524554800402e4080140340f0f0000740c1014224286a110341006464640d0303500007880f55501c2190380310b0401c032049000c454038003429155160300070b8000103090035440c0d50100e01d00309607000c1a200d00501014002c00305079075104001c4888000d516103001d100e002a4003080c000344890324460200c654540311690000501d03903420b0644022015031410a909003000408180d9202142032000504076080c2c0100e2100740049002118040c4041d00f04545580c062090300c0003a101510104a0403000d90003064451404404040c0c013110081003070030070010040200d031000ea138004001d540b100c1c0c81450311080c000c0803030050008510403018000d03501c040107810b682516010f90340c46683e01c415071070545050300801c55050411008010100c013140341c1c2d1510400d0780300c0c07 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 132558956 1250 132557706 132557713
    0x30901080114010e01080c0c03040b07050c15180619080106020f0a03120e0f12030603060a1406090402190303090503060c0403080315061606050601080a061809020a05030609 76
    0x4540018000030050b004940040e29482d4501400e0b40e210544c2000030308203080411464640380d81e186214010000d200445210004011a0010107180940081c51080044500711600f800410a03108242484a6244102480200a401c080d5084070f240100c000d81101e2404071441c10b600c3e05032090b111044082846080100031040d8100051014410607202400d0140207542e03009011042030744401d8043c54075a10369441d529001d003d264500080702007203844491940c4e000040b160400c94015110340030302000905452442d0142d0058461181110201643d40310b0030000c06142c00350040e41c1024017106c00580441c409201507025501945500301328610b007508051400030300070800d10507004184000c00015214905480c2c00004d501c2d400d41c0e02d13081010124903240140c0492240740d000d100000c0e410f00105074010f43c000e120a9844501d5075840b0104e08065840510641c1e600c1d42008520340700c90840b030303805482c02c6440100302180700c5944d40002031a005040d10500148d07003 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 132560206 1250 132558956 132558967
    0x4090f08180301050601020c040e010b0913030206091f090609150603060b12060609090309040504080405010f0f0503070c030e060d0516030506030c061b0d050913020702030a060e07150203 82
    0x1e21541001c1005101103009005a16010000039241d82d40d5140312400760b5240c90026121140a422104601501828220291074002c00c1c030410710181403810b0b405402140d02180441101280080440030b0200546100008200c130307a83c000c2c214001c0698405580e01c400c100041c5030320003154416100e40d0740100d121303825400d25504076008109110f100310320003440071000d440c0100303c00f90301c404201d500081c59514507426500310311524640301c0d4030900d444200801c100c0c0c1ca01c0038100b80c0c0c10a80e6072085400b2400781c291800011407210201007001400020142da12500c4040c0380c4030b04c42c0c40d0451005c079144000c00c00d41c1c0c01040c051031140361900c0412080f007006081c2c5005860492400307022030b090927030110740c90b10911341c04035004190000d5113580821044040341e5081182c04200c42103850743c0f000003080783d046510050720036401c441c000f020070710443c0203503003000703070002c000d8140c03625566a040010580304848005601400d1000074040346074409901c64845150080c0d0303a20b4 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 132561456 1250 132560206 132560227
    0x5060714100501150e01030605090c03040c080307060f0b01110a0b0702100204090506100c0b07050714030c0c01020d021515010c1502031909051c0306090c0504030b0c04080d050904090f08 82
    0x5e5207885114101440c2143c1004141d0354151304640045283d0b6543d40e0ba5151030408031102d044d2500721542c540f00001784042007154503404901800c004410420802c910400112000340011704000801d611503503a440c0419a0b11008582000381ca0048401120441d01c1200c241d800c180e02000416594404000da5070a00030a00342a407440d51038141940c40c059a03c004150030f01410360020400c0c0030482c4010802041098191905560b08a0f0380b64584122280c0c0e46040c21300c0d03558014000c03424116140380c000a41145141d000700c100748455660f1021101c24070b81c50792100e504014104d12003001164804040b4880300c0e0b0202e401507078a2511000c3d030090a0684a03180007140d02d0f00301088081407020070020002c8520715048000800500d0b01103014004580002e003407240741c0a080c2801580040050044038400c80e003200455461a40341e00f914010740c840d0f1281500404114441548a00d00030804140c009000003840a419103e6140711a1035402c01c40e1003a40024046048 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 132562706 1250 132561456 132561467
    0x4030501060b0313030c080405041802040605030309100c15050106050c0111210601030f0204090b090f0708010b0c071d09010e07050303090d0c1701050414070506071410050115 77
    0x41c002d250711951442c28101410840300d038a900d406070810100f500250700300842802210300070007000700240410010300384049011070a060081348168a0240000340508011041d2401c0560050601c641446a081d090380c800b01d12100450380581400e80d9030480406512615018002c240d640540b01e656600c0111308403500b41d01079004051090050a24011000c0480c4d4a009400011006c46840340d00c0140c01070700c6040016003c590011502180280c5143d1228030080301c1294a500c0720744500c0e003074240b80c01003500c090000440180050040141390002040c075581407900700c585886e9145141510103250ba440d02ca900c803801d00620954030070034000c12051443c128003501d5428546000a03076a031040010182c001c0e80752400340002c1c840d40212020041003100c50f40e618a007408844640240012a800c55007504030071100c05420000199480540303a02074040751500a8503161101e4900c4100c44d042d04600c102002d2203443c010501409000309600080310002803102030b0003511 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 132563956 1250 132562706 132562709
    0x90f0b041407050d12021609050a141b0f0c07060306030312020a020615010c0501020d0c09120f0204020304060204031b091d0a0807060605060406080105030606040b030c09091606050403050106 84
    0x101d9444000284031541d07804440e01c00c01c95100c42c1d96404c040c55810280d08118504d524949495410000000c941c40c26800c00d520035807110394104202283c420031000382ca08291581aa00140e8004403600d1183e542d00410995944500d198200450009210b1905195400510010303860708410020190000040034030010b8911095081c80b403032001c029a40d0600a0220030290054008400715900868034200c200360000025540c80349205800c034040c1403007a03106800540049000210800344600d0b8001030b40d031001040c03c0c20a0240c0800c00a9003000d401518510303400c000000c001456803a00300ca0702012030f07440c01d4800f8507140800040740c5407903480c0985a00c40c407124820820001c6410a401da50000c40759481d05007500345140200317516003110b50055800100440ea86401002141c100c0d80120b08036590359454000b0310007520b951026030b64042c1c1c002c9164990328503080c10a9903100302d10004480440c10080c442000d014202e61103400801c1380000c042c400c2c400203004400 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 132565206 1250 132563956 132563993
    0xd0f03030b01030c0c0308180d18050a030201020607050d0b0901060309170301080d050c120a0203030a230708041518020307050a12020d060e030301090b0f0a030213020c01090f0b04 79
    0x1541c2e100540245c003403011703842d009041000c0c00000400e0751410140d040d411220f8a0100c4500458100f800380032413213040745141d1030640b45c0400054919201c076420080c1d0b0340c10b0780940345944a000054495030015188418556110b403807110164a03100602802040660341c0802c241c260f42c2045138000c0e0010f0305c16184014204014025240009103000c0c0c500b002c1d203400c541d030b0000500803900705122104c03980300400001482d4440c0320b600002450084064000401c6590100c15002c40c50800c400710640c0c1230030121001031a1030f8000c00c40194700600440300110310b41c41030303400b19049600703041048548080d0b0082d0681541800c01c183e0002e02815240d8401c0b80b420318009a400181000700244945120740c0607804100d0650007000c1c80000141c220780d01d03035846094440141401e004201d0040800b41c08802e8180f410f00801e60499401900250280703011001d464040c0d8411142c8515964a51000c90300007003801036482d24290251180d56001e080070300d01044080210340200c2d = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 132566456 1250 132565206 132565211
    0x15060303121401050d031101020415111b040c030b0901090507030e060f01031218151d010807050c0708150a0b010c030f0c020a030b100602061f0506070807020d0f03030b0103 76
    0x1091502c0c0540d40160544004440821286046240448241d408402c10640550002c6000901c600540280c50025100368455100c03480600302416a1002100818003404c02e41601c1785205080aa00c400341c00006454003003181c0c0070040205403000ca0a0340300001c900d80e1002000410b56040c401c046804003003402403e0030f42846076001e20740c620706001c06844980b005180030006401045610240c1d4070984039002007941c1c50a514544049028600000c240d0043d500480e0703200e01d040300d0f404020142c4611000e40c85690b0215079a0300724a2103002c292041400c04651214104503030742c07404811003800821403601040d0700d4180e4240c501140d0500800c80e81840020360004484281d00da21450b00d0021141e9900024101ca8901e50000c1c2c41c0503584024062583c0042e060042901c0342c0750207c406c50740750101c00722030300b80c40b44290344d641c02e4000905002c545010801040c3c0c0718050b5202604100d8250006100d0002000c4203e46031403001e200791007003640500440d524140d090808 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 132567706 1250 132566456 132566471
    0x50d1508010e2e06030c0b1801030506100c050f030f09100f1d030703080c0a030806010e0d0b0c1902030a081f09020304141605011d1810031506030312 66
    0xd481030914030035800a83c21500c0500440260820b5210200643d00f04120200841d560030804d10b01341c0c0078490440c8070780c050022041d0554046d008090050300b01504400c07905410b0031084441d0129802d00302c81034019034140501c03080b410000b800c0b00922000095a0310301444007000b1450700b05044480c113225148000c0c1c40010303003002401c2c034034244981c02c804504880d240080e0920072a600000c2c0185c0021401540319200060f0600d100c2e44a900c600d42c0f580c50b140c1c01500c2c101641d1810366070064848012100141e05090004d41098a020005042605400e034680303100050f0090b0800585c00030660309200d5610050494000d42c1c41c14801900654450791055440350500801c0801e40c2c00002003401c105032032042c20514080c441c10ba5206410740c0c0b052951480040c801c09000409111038062006190340d840402d90701c004050455000c0320342c2002280f22401442c00f02a202e4020001001c900b02c90340c1d6189a5051201c0002c40d1402c614002d400d000e407010040542926001e02e = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 132568956 1250 132567706 132567733
    0x2180106200a050d11030909010308040e1003081e0c0607020f060a05010b03072106090608010f02030f13020d0506010303090f060804031d0f130903020d0f0504090b01050d1508010e 79
    0x8010b07032070028916180d41c5c41282004164034500c030380030900e074010006030000828423000e81d0140003a00c1d40012000d0850319040b0800f02e000766540005000b030541000311900145555180320b100c60410700806043c150b020f00310b0360509004031200805a00312051050880d5010300902d5400841a0f1040100354100a60a421800010484028005180340d0a000300c4425503003c00380c1c4102d10000d21150b6240d02c1d940740a0991445107900e59803c2240c54075191400d80266446030010301d80041040c0d4900006003e1901040780581e00720517150001c002280e401d07c100350280d8007070f40b00e07041307410b00d807801d181c0d1410b0742c542c0180c0800081e0020b0200080d800b0850810303000380c003180c80104e00f0111000404010350b500c030880c3d002c14500c2d45155079844079001180c00500940035101c2e4132183d000207403007a00740c404240d80000c0f000c01c400d000300c0c0100c1e0b004500c520740c10302d086400c0c20715140c1c9401c12070b004001071340c0700c08241c0d0000b080081d02c24014400031850001c01f91451205404 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 132570206 1250 132568956 132568963
    0x90503090906011e08060d0b0907050a090926090a09050601020706141204031206090f0c02060f0a090f06050f0609010f0510030506040207051207061107080307080402180106200a05 79
    0x1425410401740e10003140080d03817443d092015290300145091001e003170031a10a581c0316100e01c0b50074000e5001c4600000da0b0505481001c41c03481d080301d04659102c1c9158150f01e00410b4408440103c840144101c0405484407000390000c2c20000710005501d04040001900d4092190700003810017195000901d44260b060b01901c9420f0385904440b40507450f1454181c9102000801102703085d8500940080c0703c4905421400c020341d16820308201c00041020101d840e2034084034241e5018014002181c01d0007003550010300b020f4003880802c00c100341d00f5038641c0d060fa4420b40d070389a0301203644000e2121501c2c007500824014000800382001300c3d85844040385c0382e54800703890f1074203042e40d400010b0a01c2d201c0350125201c0d0344c1d00c18156200c20444030455003d0f500900000d407146894001b92400c5983d0310800c413440180c00101032801e503526a8030440c2c10180c0100220703000b00003030700d403085001042107205000c3c00315905e521011500c0b5591814048146c0c24031010a80c2c80180120007045010 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 132571456 1250 132570206 132570257
    0xb040606052d04200702150a0f0c03031b0507051b13020901090f0e100e0907050f011809020301060e090c19090b0d060509180d0f1209050309090601 65
    0x40031000c012602c0703001a0040a501180180c40c1c040d800b0341c00104501480280f0712148211003a5030540810805602c882c040d00114802150218a224010a005200c001003251213868041b442c4d00d94a40c5250781d0b416030301e00540100344040780407420480240301c00e00c100102c590719505040074510010b910907611600603003038543d0000f1600d600364814040304000c2e1194418a00c52541d0f80c1581818051044a0b00741c0340b04041c2001003070584453302494060b54065000309512801c1204010034003841c0c59203141880222010700c842c81080042d803800a140d1844010303220b42c0340042c0540445190000e1500c215101d204110140c000c6000355454040110035480c10b40c038404a0a6500406582146014100109084e00c007000150091815200d0603180d206440c0c80f00710146152003610241540c5c3e42e0403401024104c24807a040c0320701c044276076150811010200f9000d1034101c0b596035109907142e400005600b012030034004d900a0300540286401c58a040110641c1c3c901005c54 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 132572706 1250 132571456 132571519
    0x50703020402090604090513050d02060702060402130219030f0506010504030812060102070314030c1e10050604110d0906150b03010303050309150106020d021e03091c0b040b04060605 80
    0x10900b20441e1301c42c0b4007501e0160a2021080199080a80200c400c0d48007080040b50213220703825001748045d00c04110786009180b41e4000300303e40d840343c2d0308100b801da02042005002c25401d009141c1e8100d080c10100c1c24800c0a0348000400707448144102c1c0c180c41006105505000040104000186040040750624100031180301460385607040104d09080c95540054900300c0d900400245c41c06000c4000d080314114402190703072040114120809548100551003040c0d08021a8010303c1c0030250003c9900c1030005000203028540c22114500c6500500440c5030781c5076a070400e120401400b4400c0c81c40d148084801031000e9807601903104010300c0140401410080b021000c40c0d5684401c010740840d41061054035811581c44070002541e4500c01c1c182e87d001846645448900d944151502c001c2c25800308010313616080300d50040c0004800000c1d404c01e40403003001c0341c1c5804198081c000500951188140c4071050800341800400d0b207145030041d0f88078101145040340d0104030090034004a046 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 132573956 1250 132572706 132572711
    0x10c0516030c080d02041701051005210705130c02010b06071110020c0603040609050c0d052a04110a02060114010207060813050f0717060103020d1e0507060801051c0507030204 77
    0x710303d8010b050340180d8507000c0300340d400441d0100d900000001c11161076442003000b00550b81e10103003520340500c1d981c0b00305a0412381501c1c0e003502d0500300c2c03540e102d4500407107003c5417031460f528804070b85142000e996046002c7d1352400110841c950a000c0c050003a00120703034680c20803206031102c202810003038038421700c140d00b80340071016900d00070700c680100740d84000c0c4000d450303240c9420f101001d48902c3c10111414014038154540514001004002d05900800100481c02e091444c00201d0303c040c0280c02010281c0340310103105070b5110b0042c11030011200001f20780f81c0303042e001e000c0c0c80c082040e0001c440401044002801c0360368005802d0003182c1d2985810700c001e44541c000c036a044245041c01030400d000c1c106501c0c1000c000018400e04965420710a41c48001d03c0341c1c0000c0d140c10f000e000003907004200807201408100c0200d007204054034240c002c40c0030100a9a03c2c00d151601360b50040000c91080c00c0100454600480b14007102008200d40000021081d91b40c035827200b100d804001e21569 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 132575206 1250 132573956 132573977
    0x210c1603110919050112030f052701030b130c0314011a03250c03080a02120c030c0c0601030515010f03030516050c030304081b03030703021b0418110102010c051603 72
    0x2d54a64040403801900f0808100d1940c403194640c50183c00b8513800c0d4003048401615500e000d105a00b1141c0481d296009404a01e0582a258480e41c00f01c848882c10103490301c0402040b030761080101014582410000200742030810009026611000900410f47c000e110041100c00c2e10019441d00b0044819202e680c1c0c1da59941101c00500c6560720f9580a0101001c40b1410310354002d15180e420314041c1d2100420707569540941400e0b48610325200d0503944090010407034030302c480c801541c2c0016014500c1810000103920141c0341c0381e801da0003968941d008540d42084007004980040c00340ca14407542504443c11501c01514a110302103040c610705004008034030a0107010301841d0003085d0010300f41c03a5620342d42e11055a59220103190f0000040c140c0802042c2850000100e0710501d0703040d0046e0801071500402884000800000d040d000354072954260700c0c8002c0550010038261040000043c1c44c400340000908482c4e00c480c1e01c0003845010080ca80e0480d038070018000b0010760614010b51101d = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 132576456 1250 132575206 132575221
    0xb040f05190812010503120a08060f090907030b0f040c0618053c0108040201120219031b020a020306150409050d0905150f040314210c16031109 63
    0x390624001c40a5045141906820014908024549025000040f0859981320010103447d8080b500003601714140c100107803045030340078601d0664000c41c000d2007071024040c20408162440f00c1201d48041d00c0c1c11500090040040726a00700f50482c64688103040e01f86041c3e52030b00c8400310140106030512000881455111030702e004506d0240c180a4002d88034280312910010385125803021645c10901001001100a90400341c0d8804e1502c0503519074100352100d4005455003109102c0a40300c054080014146070034000c0c01d081d116818a41e40024200051554064009045c001c080115048608070030056500010040d410442078509c0190801c21300c0c000500400d8207202c024054060700072542426500400440112350041e02c200710f00616412001e0024403c810169411480600051020031210182e0308194440e14040310742c0e1005083c0b03580d0b00d0f1200c040f0b001e641d001c0f00190300b003103803c800e1102031128141c590f12802d40d9419648c0d824000403c4640d0396010340c0702c060001e4001d = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 132577706 1250 132576456 132576463
    0x150a060f12080d0905100b090c0d0e0304170c09010501170109180507080a0c060c03020712020f03060f012435090c09010f080606240406080f0a090b040f05 68
    0x10750305900f08000c80b004c14544207444074280e121101c40d051602102c00e4540c18001d403858455040c4e54a864908030410000b00002e002e03c0002e0b1009100612003c01c81c080b81014070700520040c400100000e100b00810401107401c1600700324104075403d5400b0410454255503030741500c982c1070703001ca07281c0840d103440c40f02e00c41d1817030002d0500d10501c000000c1c0c1c0c8001046d1056002e000303072442145940c880800740d80c1950300701d1000300164002c070010040c1e2500000f001040e076100620350030842c03482e07400091030f00105551040c010403100004001c03020311061101140d480c00c9840482842c54548060244012000c00e4107040c400c500101c1c4840c403c0c9415040d107400d00004500f014104598025070366210400da140c02085250300105d0035803080c400c0b40c001c0303403c140020040c569840c0240021203010100703010012001c2105001e80e9010a0080c2000c0c00180d03503410903c1c40d0241c0404078451003d80406055031a1170100e801152200e0a01d50f440f541010203280c3d8082c00c0d1070140d14 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 132578956 1250 132577706 132577717
    0xf03031207050d2a030209010c0f05070b12060102100c0c0f0c0506030705030103060f1a210303010b07021309020102060c0f0702030604060222050120010b0909150a060f1208 76
    0x40901d0185540107040120320000d10505468840c000e904c0f00c460001d80c1288110003040307020402a0076030301d0000c1c0c088000107503c544680c0a8660469480e2148000ba8210703d81e4086134190007030400800756810450b03014035181480e41801200c40c41c00010703100c030910480c094240b01e00104440140200b02c00c80c0b100404019100a949251034600100190421f00044810340e090011902800360755004408640380107182d4640049810303c1048180c0184011241c184e418654174003460710401d002a42c028451100c0d02079403504103204002880c2141242040c0c210b180c0402c0002603680000c0f1545d0102ca400c032025078584400300181c049000341140250315100e00e408120030000550080c1c4142c0f07201c0e840014010401017100d1300d06a055000705800204056098103040c80400c4e101c7c03a10340e45c1203000040014090000c030350710420894404059078081c42d805502092440f90203507004503242c40c208a854180750b002003c450b0a0b111b102112485003480c8014059175004403038 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 132580206 1250 132578956 132578977
    0x10e070f140a08041e20030a0204090c050112020c07060c03051207020307060506031c030513021810230f04060909110a050f01020303060405041b080a060b0f0303120705 74
    0x782c4030149078900900c1c8100440f0b04032500c5140703410701519507500000301c20405170710200f120100021406010302d10000b2140c3c0f503515200b480d204c3e0001d41c44c0d910504e420341d8040e070f11040c0d44504090014021548111080d08c0d600d2040000b80c503440b901086000941d565881d145142d00460f0404940c0c1c2d005490f80410707511400414046030680000040c003200344a01c1e0148a0b40e84d4041c10103407110b811003c03515100c0c0300c0d002d0b0350403040d1180e4001944003011030300c00b912108060700403e00b1108030140c08005030160006020b6803446100750304004140c2c031220072040ba180b0350521030301e0080542d400340c0541c643c150204840d41d04c0d6000200540f5030380e5400c01c500012400d1114001c0310582a03940590305442c00814a8241f40700c4000c0220410703001181307140c44200900c0001c04009009851303141880030f20b000703040035604518000305000d10003054903840c00d00b0102d04466440191610a407144040000a80c6010040d600101000c0c03069403425640c0300019030313561161034405e4 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 132581456 1250 132580206 132580247
    0x5040b0102340b07030c170408030d0209120c0d030f03020d0203190b0105040807030b041e030804050c041407080a060509010f0f0e0615070305040902070602040518010e070f 76
    0xb12500c980c4505030070001c209071090500c0301603072450300e0718440c403c40390301800090148081e6004188449961074840c000c0b040c01d54605603803882003c0c1107411a446654256400007000c00c00e03841c084078002c1511424002601d1042c41030f0300001c80c0031402440c02028070400b0300240440b280a98142e502400fa00c0c282507650745410b860001c0c0c102e601b07010201c069480e0003544141c55201e881641c0556000d8002003904c07a0450300c0342034400c02c2c02042202c43c0d2900100070116500c02004115103a0320984880829081a00c4e089042c54203030144c0500680c60042507094144113441d449404c10340b141440404c6481d42e03400040900100e0700031035004450350340005512290110f61004403440c1c804241074090f110281c0703007035045c0251241c81d0300090b0500400e1403500000020000f840c802d00b080d500d0035645494076410380c1c002e04001c4d02e01903408682008507090035003448428031071001100340e5a6051160716040144083d103600c0411043e903003009051130187c900361500410203541e2 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 132582706 1250 132581456 132581503
    0x801090e1c05090d110907110607110307120201021c02120106050705190503130611030403020f0a080105042102010203251803050604050705030724200c15120105040b0102 75
    0x241c2ca810207050324640186c14150020354080c1c03041e00c25410700200b86000d08496202c0080c2111812860601004140020084000080e00408058003000c00035000580c94405400ca11f101c01081041c800b0b0445004000054055660001c52410b507002c506015489008c2400c00c40e203891044aa40858402d000b615001481400409407004040d0f0052491009451311421598072040e0106074466034000e21082c030041c580a00c28110800c00030308094840c550f20f0456500b521703019281640c0196100540c0e40e020a007854a59160b908140020b614605060300400d141c250b403c00000b03000c004002c01c0441ca944944107000403e000680c00c0000a9181c3c1485a1900400e940c02c55062040c00c200181a043c0890728034102c42e132202990600901031000304015441102c0c4420401040b1240c0008526171012401201c08042c0020100c0e50001d006104001304440880c647d051400d10580100003805d405690545000392004914003800c0e100503132178000c0b001000012070708442007 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 132583956 1250 132582706 132582713
    0x140405040c030902030d0203090f06090114120403020114060603040212030903010c03021903140406020c100c0f020c04050c0417010212040f03180605030c1b070b04060801090e1c05090d 81
    0xf214502d18000c4080d107480880481c01a640c9204d8044a50340094061410000915040019100094041c1099007600803405060300b6142d0043d071168650101c14070901003896424450003143c440741d8851825607081ca500019183e02009000034070030b0801000082c6000c50510076901074880142c002e20801d480800b000c1e020b5007082d0f82c0716006001c0c821040710750340e10074050300d00d40d031202c4000d101e125260794030340c2d401039445003460000c06d00c01c401d900e4010100d43d02c40c000c0d815606654068482d005050f0003400e101a003c2080d02c580e0805043c0030b00803281e801180d0494298880c06a1800300e628942800380c002d0f0840e80e40280310b00703810030090046000c04440c5051190741ca20b807000503ca0201c0c41818114041c1c200001c1c0240000b5071568003000003082d41144001e00800c05580302a0400d280c03407041d42040000d0700002c902000715903080304200b409003401d204184503014030b2205145c1d403280c40506840710020300400c800c116901038400c980d008480500500340000c82401e = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 132585206 1250 132583956 132583961
    0x3030301080c011106060a060c03050c12030406050708060112150305031303021816031812031e060b07060504170301030b0f070f0c1202122a07060906140405040c03 72
    0x44070b140c0072401e00c242415154001140592003034000078480c3c1200c50030011304480c040044e150803401e000c0d0802c1071b40402c113030030032036600d4144504c10080d0380c0f49014a0300f5403c2da00003828110510540e00300744140790386c0015200d04050186680040c0341c101c0c0c90304040a803203240d40050858000000c420591801c0028071000380c900a0b03071045aa280c0d00c4540c0c1c800d8041c01c8610040d01c5144150b50014584203410a0040074400c2424000c90381c91500d5106d003810b060300c00140443e507a030000d24031541c5141c1000311301801c84401041401c0c034024401e0346038071503003400810702541d8100003004c100800d140c048400e90149040c54032980c480c5003601b06980c041c3c40e0406220000720000781e1252180c2d030a00c28000c0b090391020406c01656881b00c00c4925422241c400354010b00f4910000c1e907588601601e10f80044420204c00d072501581d81da45400c54525211540b50401013043c000341d41c0040100f41111107624026103181c03030b040c3d00c03d141c6000c0c2e60042c42d803003400c0240c540d460030b81c582c = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 132586456 1250 132585206 132585223
    0x130905180706080604021b06150406050d02090609070512040302012304020d0b070e0607060902040b030334020409030e0a05040b24070807050a0309050102030403080f0c010b0303030108 81
    0x300c90440e000d0001500c1507640d03044501c9404002000100007515a00306600508030741034822180c0c6164240300ea00c61800e000c0c00b151602200d503849a155150380c5001d0190b20001d080c25a010032103412103802143d0f1401b4000e2100303020341403070800300e682d252145c01214000c04071030300960001d06140c54028060150030814075000c098602000c2d040407021008540240c0d401000101001e1856494500c02c0400400e100180801500141301070740311003000f002018400e035000501c0301413520402c802c940200005a000351300510441c6610741c00500c501c1e200004c11190781801c900e100d8441c4002d0301d01d250009400c54200a0510105030704840f15180c1810211450340d529a1120240801c5440c0c5888a03075002003000b45081d0743c1b491166a203080b05100301d420303600c3c00807607485000269104120441d1706030302c11800e80060641c0034403010302030300e800d20280d0311700b80c5191245400d42c0540319005442d01d000007021002c2c46425840690031410243c160b90301e0f90ba42c5ea071001c1d181c4424 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 132587706 1250 132586456 132586471
    0xc0c07170705041e050906010605040302130b060a090f08060f070c06090503120108151b07030216031202240115020a05070306020405040e070806070302070c0b040b090114070b0c0a05130905 83
    0x1740008605e46c0b101c0403a103541a00c0140d56000d0503d8610340030030440006602c0e2031040c9503507944a94816440e84002048560f01a440d07480c8894902881c46242c86125031010308950402014007158596403481c654000c1541c0ca00304410003880e091540003031040000042c414480028a843c0c00c1e07280780b07001c5040306d07021070649820742d4146448141c8000100c481084901c6a0400709401445940282a110303009104407000303070075134648600c01107045c0e820684103000d00e00b1180103c580d040220801403100107208507249001d244050300f0010041c0240340c0b450400c003151511061003000052541e54001d000c03203080981d20308164000354460301544c0c2c020340c1481e50000b00b040c2e00140c4401122240002413180d50780c3c0172012402034108400444403203045190005041909001800140852501d80e0769680042c00015105400151903000020424031103003020410801055074420f144600a90b581d00462500300c6683c41081440b03008841a08008600c10b28a68401c502c503108 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 132588956 1250 132587706 132587711
    0x109110a060e011e0215010308070b09122704020a11070f03080d0b040b060d050105040501060c050a02010e1201020d0e070e0910020903070308160b0c0c07170705041e 73
    0x71180d408880740d8031000700780e6021988042050000368210441000724984510580d00f206c2d0f0f000c0345070718608000381e0040d00d0442004c1500028045840a9a50000d1145008244098071207081000310b00900d001c8141c058001082d0080080c03440c80c1035150304000500456451050510150001484165886040c481d5582c0030541e48036070407008042d04e802840c1c0300c4c18041c0781c3d5005005450b0311229650019209d0b00041001c0e11804040e000e07031046034802090640c140f505110441e00141c1c4484200108043c2d160041400030407030160445e021720f0840b080a55610201d1000c5c0241d0a5188056100160f80780329150654042c4045424030300a85c1c0c034440d175983c20b80e482c5050030b84041c075454200c0301c00005004a10307801400380c04406010b5501e140d541e5154814690002007010380700d0340510280404100c01900d1155100c00c046812034200300255848580e03800807801031043c1c0c0000754001000f031110400441c00100801801401060403011280b803480d0100507420020a0 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 132590206 1250 132588956 132588959
    0x1605030a0807021f05030f070e01052d071a090c0a090902040b0909010e100903050a2a060c02010c18050d0204060906060e130212150612180f010b060409110c0109110a 73
    0x24401c0c9e032042c00b0400c059640c00e0500a1808091003a0103511348110842c0b80c0c00e08008100301c1500340a010b03443c2c011809524035844084411588607001418075a09802c007224155403075590a030300b9001c1c0c0f00b0904c4000355011007071010034014882e51194943c440007481c100600c070141500714110060141043c0c814689010b0030003426145131050082c01305106010144482d4403405d900c5001c0c5154111408050082c1c8840000f09007602d4400c5e100180c440030001078030b030b8090280544e1706506240070050516100720020010380d05005d1180b060020264503020340d41d0300e4000c0405071032400010840c4c55500c0c4400744c160000d5003007545c0500203c0b0382d1909504010320070f4546440c132a0000d103007203035284160090720005a5000300e6004200b8801c3e1443c81c040509403a202d4008440110380c0d0520042340c0c80c0c509401010600c82d16070416014150726181c40042d28121940c540000c034401d0084510700a8501850301c42c00c400f5841c0c01c2c41c440a100358540811a880d00640e020848030f07 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 132591456 1250 132590206 132590221
    0x1b0708011d120702040209010c0f0803010504060e0403021507050c01060b09040b06041d04020103021606060e0c2502030a0206160213020309030a080619030809031605030a0807021f05030f 82
    0x150502c40c80703048200750910011000d810190020324201c1c1052415a0081101d90b035503148190190600351810400071005101d9424103101c0c2c070002e0494038550249516055030001c3d0f640084072143c00c0c61042d58130201d00348a010b601038800c50f400c40e2009201c0603896412440e187c1d00b2203550244107604203c4032083d1400c0c80130840c0c0c240ca0342005c0c05400d6541082e484107080001810803410140d00300031004060940d0076002400d1880f864001c990b291501c1c103142d00741000a000b080f92205c0812080b1180c1900300e403e032150700321049000c01c2501c0304d400003905003441003802030b4000c0c3c40000e0002200011454108440d0302c00c440302d0302c140356a0400e1108900003220100c015500400040c500700b40550001a40610700400a100e000c1100c4810781c0000c005034800c591035075020072160a546400d05c0100c00d0762460303010002d401c80c50f000000b40d40d00b040781806080810001946c0066445020450010352514544d0301408040b42d500180705900844900c80c0980c034030030100d140b5 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 132592706 1250 132591456 132591463
    0xa0c150204150f02030403081207022e090f020904080a1b03050a0e0a031e23070e0703110a081602070b1c02040302030d020d08070f020601030303021b0708011d 70
    0x81e9400040004420421000243c42c460301c952101420362005010000000e00c40900a01000d00c00055102c090300703210901915165400b219901d00134000080c5515951800351031181d00d00703200d03a0200c0c0d0006103040c000507800a100b800ba410280c440200018000020002d1076240650307550072071070482d0b10380c03401e410044100780100002c404108440c16513204100c0c0e204621702c003d1101d50860360f6580c0c0d105903410703220442c591102451a101d02800100c208824582c10500010104101e0424220ba1500024080c103521030003c4004a1215403280d400000003140d0513a80e00d03074414003101c011304441c10848001641003981e064501c0c1c0c291011520340100d030400f040c910b081c40340d0402071103e849000e4003151a1240d003800000050781c1c0c100001c0501c0b5074150007030101c0f0072046500070180040100f44401780078016407210002903000580702d04503a01885c0060300d9070344014086900c6900c50a02403204d115040010a1000c03040d03210824004042076281200000000200d45 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 132593956 1250 132592706 132592709
    0x20c09070f0801171e06090c060c070512030c06240103360605010b07020a050a080d0c0204021605070602010510060206010314010b090406050a0b040204030503030a09060e030a0c150204 81
    0x34601400400030b040001c844e03502c54100c0380d4140c0300c400620b001703004c2e000f60510818400725409181440314006051001003201d2006032500c92800403101003a560320305e5030344031300c6014400c0e607452152206400d0003540c4050315a80142d541c5d50404203c0c2d070340a00f000e00e688500ca00c00340036500c0300d80d6010344100107265543d015940300c000603075160120310244900d02140c000703504010410004030588120760103414a4184141c8030240c1c3e0060000000b4150407560045050f0301c0240041580024010300705801417400340000d140c2440810043d0090343c2c0c0310406552000700c1c010030031002244040c10b0751140d50003005a075a4004014000c140c00d03102e42c10268002c00c005101140180d10a0383c56214664008140a0b100708082403000da0122820355072140e954081c0a5107003994003407480003540459042d070406055444080e103900c07002e800103581031307920000c2c1420001e40da0070010603001c0d40401d40303807140100700740038048080700d441c219203079406001110b0002a140c070a450 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 132595206 1250 132593956 132593987
    0x90b0f06090406050705160c0e09011e05040201120f02030601021b0f0108040218010f061103030601120b0d0c09020d1404030801050d03140703030902010813033c020c0907 75
    0x207031291101d494450042101034030b410b0822400700404d4004241c2040040d10f00c602c18805038241500e4081d100c0c071400c4000d0070344007884e41040d1010b94901d54003640d8002c0c104141e00700080680351440140d030018000124492401d082601407062501c507903019620500003030302074400d8000400c036458180d0b80048003156100310400c3c040000ca504ca4106030364003d10203065a08034403290b80441c541c00278240c0c0644180031000304e060144a80c003e80c200841a07130b40c00190b0030b500b030090010300340c1012145c18050b03041e511260070b0003541d60303845a00c004517044004281007a441e1f04225002c0d501440000240ea401e002c540e100c07180c10a00360300e10554041c0e0303810105909240c2000240100c0f00019010000350404080c034410824000344442403003514001030317040c4144005451f07807600900220480820720f01c0394000c2070308010543c001006c1c0c0c148000e1303000407400c0f8044000d80509214124140c80424440a850700042c8614010008641600c87c030341d01c0d0041251484051038080 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 132596456 1250 132595206 132595219
    0x801080303190b06120709080601030809010c1b06050405041a1503072a170a0807030c1809061d04050c01080402120a05070f05040e07030206071a0901090b0f06 70
    0x482c041c0180503a015403441d02800400c4615075000040c0c070795000818051900c0b01c0207414410501c0e082002500148445e03005428198550344a0340054024070414505100000b18054200500b01c00a50780e444568090311050769220f150080c103d401c58010707140114904090400c6035855840c503401e004400411400c652241301c8110b801c40d0304058034040900050194421035030341407803101c84542805c480c03401ea5600c99420041c4413550041d41d640d5141000b000f6201e00a9440b000c1154090808d040c041340c0b21004140c1200c2a1034021450748020884500110700c3c0c42c02074108900b240ca54a0440b403561104200030b04240b2010744000300181d0100d50b140c00694018940a03901c80d0000b030440e01030103000b196003410115030020486040d00301c06004c3c41440a0600e40c0c4001c0c0400f95001c114040c4580c1c0c0c0569102d09a000c042d00c2000d0120740d18081091101644400c41c2c44001c203944641800c08240e406000f0080b003c444070040000000c43c0201d5440d03205200e080c005128 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 132597706 1250 132596456 132596461
    0x609010b040e101104030506130203100603121821050c03010c09290304060902010206090606060d0906110a051804110301030209090a080c240112120c06110d05070801080303 76
    0x5410080212134480f544440c018480080410350030320105109091160000b500c001c41032040508102504003071004507842c005091001c5403a0000c1c8125032441820082e0600000011080d030b100132982c0410454101c0e4a214000c8400d0b40102c242e02c1440b0b5021103000d5039401003014260358030b03603c104000424520081004e200540700d594403a030000313044074880104071480f40c10b89900454054031140c2d281c0c00d41c0c00455070b040001560003002e03038001c0d01250800b0781c0080e203984218000d41d101c1c55200e81c101d8040c8115644440e1705032191840d100d66070592070501401c1a0041000015002c9040079005000c0c105406603404450f80900d007a40f442e800d40e0f08005d400f00d0007404011162250b40d203581d0011713521030001c2c41da51350350704010701d01c07201d00600029401a440c070703060b02c0984410004100074181801200c0507582d1000c14100c01084400044603950541800076000b81c1c101000c603402c00b1304c210001c02c00c46445c2881400b50390b1300c00b40c007078a00300420712070003a46a008000 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 132598956 1250 132597706 132597733
    0x6030102070506241003060501081f060509030102120106080117032a030705010f020c070512030a0c02011818060509070c080f070803040803010e01210204090f02120609010b040e 78
    0x1000413804802c54016002c044000000ca02002c1502000d8800700c3d685d03100038040c540e04920801d500c115102c8014883d40c0349512000c1036007102e0312030042800004039400301a580d081d0141c602d004a500b01c215904d695620000308029000c0c810000000354825280312807040100848648490080f43e44c0c0d00400031004280381d24004c1c02a200c9280420701841001070802c4c05801036a038450500903884942d070124031400d02c42d040c2e0186228074140c1007499248440070040d1094140e050030724100e40446800140c82c0300760410a02c400c0c595a14070041100900303180c007031104845418041010586500134030200707401c1900d2540200740b08628450001e00c4410080a003c42a03034003560520025076200c110982040d03508541801020005000740740f8014000c40c014000088400390004400204141c60ba2108001a000c0c0340c443e28038005114807401052011503003d800703404058207000361161541c0741a43c1440d559400c0c4151440d451415010f4156001140f001410150100f4003 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 132600206 1250 132598956 132598981
    0xe041e0e030703080601051c1e0b01020705031f060b0c1c0c050c09070908070303051b070e1503010b13021902160b0c0c030d020703060c09140904060e01180b06030102070506 76
    0x80705230300001110201c250a0100d10b014203804102c41c94480c41c0c00308050701120064900030083d0504642c840d580c20400fa60340003444001c1c40d0700007800907602d130354034403c030502424050f0001400da641c00034020829400009000e2076491301d0100005940340c2d4484111242c1c100601c000e02680d001c6445480c0d00e280c03e0912680007800d5080c0350030100c0c0e0b52801181032043c3c6030710a602188011800c0c592076013601c1e117144006a80300019248050034400303040f90402c406842040812510201c040c4075442c258000e1508585c01080788070207d040c482c4803400782d4402a071301811000c01610514a20340006846071700a00d00c80c01d200d804a0400c210050382c1e801620380c00300584600300f4100d4264030f091004514443c0c6c26400760002c00d0460a0075820b54984036405810400f5040e8200800d405140341044441c42c1122601455102c40c01c20750060000c8103031081e00c0307500c1c04651180d13841400e210b402c0d1492280c0d2101380181d8440c4101401c03406411006081c5800003c002a00d034074000303 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 132601456 1250 132600206 132600217
    0x2090601020f0f03120c0a050a110a0209011202041a01050d0e01090209040803041407050105120903071b0510021504120507061a0a091802040b010e041e0e03070308060105 75
    0x1881181c5a500942c10410f250000f000015540740c0c1001501703204001085c0c540551042d10312541d01c1c41c201d1143e0005103280b0035020702e11b04200003240c084d0f11071001401149200c6400803e1855256110385212100c5809084c0807481b0b5850001a5a4522001c5200c4070750010140c49807401c000c00d000094024141107001e507007007556200744103c01a074548040c03030300590040207115140c1c64540f608000c01303460058100c03026407000341d0400c05a07900c1021114003040510204c10340f521809001c80c994090394000034200c1c850140076600b0303a20889400303011103900716007426110001c900282d031584a295825041401c03000001800310345004000c1c0030003801e07440c01c189011000d4179103004950034014528804401400c0259852a00996107030180ca480001004100741c1b002c0a2403001c10341d00b000900481e103c1c8582d880c160302401d0701c4110b55101803c10302041c1e1006501001074440825501e03110f0b4502941c1511841d03000050302c0e4020781c581c4540a160701d84400550341034014 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 132602706 1250 132601456 132601459
    0xc030c12110705011103070207050a03050616090e04110f0f0603042003100c0915120f0b0607080319020306102304120c0501020d090509061c03050d0f02090904020906 73
    0x420070b000002e0300920525600c541c540c0c01140e22420050002803c20105038446403088681340d0302480428400704800da0041b8001e41a5083d0300003410040c0c40c65507659100d803026a540804120a111080c840055001801c840707514096050804002d5000802c880058001c03105000003000114085250901d1f5000c61602c1384440848a000a2030082001c8490401a8039502c0d142e01c2d0a40007601c12014001c10b17655007181001c6032000400c02051039450b8049070b52522182c0122000f154440722610001404907960303042d45040c090810b41c406d952900e83d8081c41c480c040c61145480c42624050305004204091103050008105d0300d0103624100c81810030301140315001c405031520014030003084054801109400507080c01142e0f00c03400c2c1c0c0014107541180c01400039150b8082130442c1901c3d412102040c841d110000811041c0d54a1a103132034a01107406c15010525030401702612000401c84400c0c411241c0c00d80e600810b81c003c004029801c41344100c04100146030001615501c00c80 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 132603956 1250 132602706 132602741
    0x140706021c02040f23060a0c0c08030a0c05070503070f050d03140d050103030e01020d120e0a060c09080601140d020621040c152c031006180c030c12 65
    0x14602040d070407a03115902804140c103003100c1c01c020126140070112100f000130030408654148910200381e00d4856890481c080101d0b80b080d182c00c00c080f41074414041c150360b400701c036210103c18102401802e00f140c0151400d11919a000405140015240041d1110900c1c0300d141d480c030b0031051282c1d03c85000c01c21018400c40380a5100300d0324601b00a040700d074120305800300e4039504d9810301030b041d07160881c5505d0440d0041c0000004140d000034070010003901c0c5c410006001256500c1d000d0030134406036002030800b81020707810401654402e00e40c000b541e0600c420349585076620207018542c02c0301113030700c1c940101d070034040c120152520102410256004240c000300407035103945000e10010301214102d038901d02516082c40700141083c015882c0c1c03140341c200b0391301000c2c40c40ba1000e400c01d1814480d03510780360290185c41060302c050098136104038624105211647c2c890071065000c0714140008015a481d00e240786409510901400600d40c25a03244e0714640303a0004c401201500012054454122 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 132605206 1250 132603956 132603997
    0x2a0c0a08120c0f060a0204030308010b160b0c09060d0c081303020a1b1512050601030b060301090203090307140a1b0e06040c05040f080105010512010608030f0307090306060b0706060614070602 84
    0x50013401e00c165420f00005036118114900540b01c05010f800c4150865800d01122010f4950201007205150b000100d40e004c6d0f540d90200c1d40384030303c01c015801d900a20082904800041a13401040c000c01c1c154440c04456501e4200f42c2c821908501000f50060380544900310110b40d4030807034098000c000655801c03100d901c07001108a080c621101210001d42c2d14400d0500d00c0400f440751075000103091038140611010000000e00500060060b001c190340d000001c200d81e05810000ca80302e01c1e5004050200c0d0003035083d402a1102d079034090039526020000c0814002d0707513a045100c0295020b0020f20106500c548042c80300414001c0c02d09420300c50f04010110746021094003060052070004000300e210b6040005200c0301c000140d61102a0f681826403d1000460100a50321444400e56010f40c80fa41c03007100865400d9181d03071021f00b28600e40400461844880c40040c50201e00420052040990f940c2c0e0403144400350200c0510000c038288111030009115400502c42c854940c0a49035100 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 132606456 1250 132605206 132605233
    0x62c06131a0108060a0b0a0f090e071e06020d08160305060a091a01020f0706020307031416060608010b010c0b06130e010501060507030908070f030807082a0c0a08120c 73
    0x81c6030a801c1561598800c3e010004605001e02650303445460076280c9500c020b15192140d14031086600605c01078903100c1e0710f0b8107001c090030000c83c0c00804404580c600712000c4c2600c5002031056a01448006000d1301c0700c201c404c42d00650380540030b0141c0c05041c460800d40c28000b1001080b0190003a0b5109078540b00001c0c00c1001c034000c0002e0b41d1141b029100412000c0000a0724160541040c0401c580040000b001070b6078020064a14a54240c03c00141c0b00da8540080662071144030300480f40c0c1d00c0380e05204e505000c020303440740c8151400030008100000b0050300541d180c04442d000100301502010010700941003400b00000d001e4102800400e845604451603420f40e0000d03000000001d1010404005050f03200d680e100060081c140078060460070302c0710004a1036440c0c000500004400107402d4100044442243e4680c452041d0012080381c00184c408000d03240e0601000e02031041c1000311b0301514140002c402114510401031007041b01c0300c0c1e040740d031580102c240c3c02094020f4190214a5 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 132607706 1250 132606456 132606503
    0x140706330302040b0d0b07050d060e060901170f03040806071416140c0409051c090e0a021605061501260604050703200a02061510030902030c03010603062c0613 70
    0x52047c1d0721880e031642c5041c08143d0450300e40707030301008140b00c00d40244041e940b03c440c1894192039107100340c0c0d420500100c00052501c000305101c07400300d200001d000a1404000302d80d40d80142d4481e41c840d505401f00e1240b00116005008200e4840314141c6003500010b48000f04d4148100c20300300945100b4104480001d0446400c0d40080d43c1c03e0b04140101c008212905502401d02d0702541040b480150620120b5190203c00514007000da030750008118154800001000703c2147d400070440d0468030b40361280d98038180d84200c1c0d45000c41c0f0114200e40d0407000000300c0c503d40c650807042c07010280d52560200009404050503a005050342e49080d02ca1000c00000c507a1918003070b040403036a444c3c07081b142c0246001c20003000000c440c0f10500c0342c61030070754807510710143c00700292501141010007400000d08100182d029183d2540c60004004100011034000305440d58081c101e4485141605401c489002500390840040307802403000030305215070b4034025010090003030a03070706803005101c0600c0d00b4 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 132608956 1250 132607706 132607711
    0x617190204030c15020a0302070905090c060a02030a0306091b030b04110a020a031205220219090b120102040e07120902040204060804110f0102030a0f140706330302040b0d0b 76
    0x20b445003803c200703001d8403901c40064000e007074031480200b542da555038030001d456101e14064000c125071a40007160b4108820080c0d18070400c4000c000d2580d807003280101965a5101d205c1420110703086c054002140c09161003035690900c000540c007002101c030040101d00428550010315441036540c0320b543ca454601e20080e0141c0c43c175075001030100c00d000c0c0c24007502003500344038401d01150905082080e0004402900000799078407042c0c04a410740b280c800600900030305031584141d501840c400040a00003074000c2000038109403036241030030358101c81850a03441580500151201d001d004640c0440c030581c5040d44032070a40070700060380089c03a4006402d0741c3c0507620040000e600780c2d00780410b1111025008019000844903000301703e1031200081e49038043c42c0ca50708117200d4403c079071f908900d020311840008102100e020700d5a50b40c0d54609440200001c54180c450300340040881180f800084680c10b40e190748025112814134516802c00020742801c0210310740041d5a0462500000c0d8075918150 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 132610206 1250 132608956 132608963
    0x2509090507050a2103030207080702090f070f020601030b010e10030f0506040204050a0b090a0c020a0f0f03170f0412050f0d0501080606031b120a051603060b0a061719020403 76
    0x21001d45444200500309100360407262255070207101c40e194020f040c1c100380c1c4c034071941400c001d038071104075050560690050a6001c0d40005401003000060325207881428030402e03050319106900307000018100da44a2003400010800d08400005021200c141400a64404001e014100c07400b81c40e50341c0c4899880640c1c008440036401641400114901400303020b5100d0810b4504201000200c1c1c00901d240c0e60180c24040310030754031a08105007034420700210101e9034010300c10840554891034112049081904182c00154015444881c43e0911855050048001000b0b6064a80f2640c46003040085c05100034014003404202c403171180f80d40c01026020321085400b001a540d803600c0380640c10308130300030081e501c01d40114010000410200c18154842ca0080c1e401c04603c081c0880c80a18241340340c40080c000340305400c160f22001105042c1d03501543e02c6500c083c0460b6906000340000c1503454040d090104800d6254805120020b44585034030501c00d1030b00284019110b0310200c102c0e8415002034 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 132611456 1250 132610206 132610213
    0x612030a02030a0e010e011d0109230301050604020a0c03050306061b03030601030e010b010504030f0f061103150f0f131b03090201020708121b03250317060325090905 73
    0x780f25030ba82188048203030540038240749603055010360009100c0003113a50903101803c503020150070103911400c00b07640034069814070b4100c0c084010500e04440502600094402d60030000000c140381014000c0d0785107001551900d07590140b0325070342075801c0c3d0401028607400c9802480202d101046580064000025000203550342e4100000010709031804c041102c05940e0501c00c00e00000c1e42d1143c00c490803641c02ca003604070310001c0ca250854590421440140480d4204440303219211501e03c01180600103080100b00700b80c106174180300005032003d0205900c03503440300a540041c00c0c6a01400d1702050280d0b40011f40344100084840e00910f00c003001d4000940d01c060390403c40d43c0400c403000c040c0808200409030306241e00c041c00501d20460100200d4500a0030500301002d008205403172851402d04100e40d044654a0814801001555001d03400514625104000810f05842060084001a028240c0f0002c04c1c10b42c10340c0c00a0a00d208041c070480c1e100300091040e098424a010b052145002c3c = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 132612706 1250 132611456 132611467
    0x7323006130b0f04320708030405120a03020d080702010209041508010e0102030f01060507020a03050102040902070605010e090a061805061e090607050403061802040e01060602120708040e0612030a0203 88
    0x149a40c40c801002d1240d084142d50034000410090071400920028240b9011030210400c1e080c00300f211206401c60011b0700c40e0500114010001102501c10b6410954403401a2580c0d003510310b55558282a0190141e003100a2100304240304036100b56020034035000161070300340301d64040303411138401d0170b001103c00d05009000e20092200b8043c480501c610701000b03508500f440139048001c25010320444040c4040050550210744807013031808011600032008540380c550341d81c1c40202961001d50100c580341c2c82c0c8000801d80319074841c0e58a000f1400700c00104000512075945030000c0142000c554190508070702e4040c000303a01005220320940001e142440d800c1c072801e140801d155409043d0f07036403517004102049803840c2d10070113031800c694001e503010a080c00d48440d202810b4038210360103500030b41003628040d580e80741508880129401d1340d08032018504405600b001e58065440c0042c010581000200718002007410281e81000000302600d00c800f1908094600d994030589050001d40c101080e0b = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 132613956 1250 132612706 132612713
    0x3081303021c03080f04030207030819090b040605031f08100e0106050906061c0b04020d14071b0204050a0f020307020706030605030d1e0e030732300613 67
    0x401c4034500c42c403618001440250b40d6010304880401000e02c0b4000281400141c00c0c50310030403d08000b50b8120341003d9a071119110000354103015145d4040105544220000c0d40e1000c58040340d00f190038a44e166800c41d12048010f03500301c6040304100c92010000f01001c04e0491007401541c16183d402840050384900319801075081d1080b583c8107503c030720b41f040204001500c81500325010f00705801080c2c00c440301a5058000104241d801080c4c001c1e10204840050340c060350b021402000d0799a070500c0b07085e55240340445844c084440300d030394960401d8500c000141004d81090360441c1c0c00260100d0761040030101d40d8101d800481e10100140c1c0041c508001094261140401070702c0c0a401802583d5000032011301415841401c0844080c503035410010034a1090030000c10300c440003810388005c0d81e41d44601c05145208616800316011a03c4c0d0000395888000d295104140c1c4042c20541c3e0000c071400b104c5905142c0305180388521010264141814403061246c60b100312175010100c40c420a4605 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 132615206 1250 132613956 132613969
    0x90a0b031e010b0c250e07090501080f09190302010905012315011d1c0b0a0f05100e0915011503050f15040c11010203090f010b01050a08010b130308130302 68
    0x3800403c2d01e030300c10044450520000300e224402502c440340c1c00c510084600c3e00c0e0540d18011580030791569058030082c054040e0307000542800b00e500984c2c91440a0b1620010303000103201c261414005603104661401c4200c48038940b00b03a00500a000008007002c0301d460b401c0c2502c100c60500c03007050380f01746008000c5a03062450180c02643c4180704079071121007070340007070124042c041034007030014215005828142d8605001414800700414540c40700304580c0341252180c00c040d82c48101d02401c00c1c0300083d1104071441460f100d15400c980800219242000050b141800a450412540140040025600407810100e4001c0c9030000d441070b02080e4001e8000c04a4001030000c443d10a040c1051000040400319200002c180031200051400017440c8191036211794400e8042c0d5550001c010000100300200d504103094084000902185001c5001100c882c4120290b803801b25017260014488030a884000e010402d007440d0400d810030b0313200d844d1514590425200340401c0007503c00140114100350 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 132616456 1250 132615206 132615209
    0xe0402070b01080a2d03080a060b0a030f06120c050d03090b030705040302030c060414040c02010b121018030507060b0a0b16050c0111031608190929040506090a0b031e01 74
    0x2826044c125503000e02103030a900505c50000d41003101840c00b0171180c1280f45d02c100e00400140c2c00d425582d120f4150b014024125080000485a01d8244006070714000b9804400e2042d03130200400340502d00300b20810982c110b00503420350400c9203102001c0b50448034000114002c81c4961a640c0e103d51440c03040500d4070300700d064224010318040c807040020b00460741502a80100071200070506078080641240100307143c3c10041e07031214281441e466140c0010908080c076140030642482115041000c010600c0d461a1005000446c1005440e0101e046d40d88001c00213030f001030606200d540c0d42c2c010580b03580c0047c420380300c1103507040c400041003040400104a40034004e0910b000315648040380301d500c80c003554017586007003821908000f0420107180202c5071500c043c2c890013041807283d0780740102180d131385008040c40402005034844016100c520f56000e0f804030142c40c0341c909801d00d0144965074100b402c1942d000705d000980402c011050344d025510035024070004d2003154001c90140350503460103 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 132617706 1250 132616456 132616493
    0x303010f06030c050f0c0f06130b010b18010c03020f06100e06010c05030a0513051c0c14090a0e0a1205090406050f100327030509121603030e0402070b01080a 69
    0x18905010f4840750070900f95010304e10420304680e00c034021020702c50308142000340307200e05600454080005a030a215502c1100e180501c82d02181c9030780702d540c800e82a1040c6c8100000307450715070030049a9903214001c01c2c508544640b06840700d851104034582d1403c00c0a403120540000b104c0424800a200007080e29405402460700841809854640907124070032000c4d13100c100300000542c401c01c40500303200440280400b911030703800d41d1261140f602400520b036600f00c46041c00d9490010360401055403041c507070381d0000d00400071a19880061801040030010958072809000da0701000714207110780d0701e0303841d040a0300c4003036540c0c5040e001c00085130500d03000789114a0003182400e4060300d071071009107d0b624007400e00088102d01400c400c100c01d1140c8103540d0130926440000030806902078081d0030b030441c05480c2020004a4141800d1700d40d40c4400d01000c28072041c00e001c0000c6840358520b440c41e00f4024100624168090303c1e05c0700c500e44260040e201650002492404120002a281c00c58004 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 132618956 1250 132617706 132617711
    0x6021b04140c03100b07051e0a0309090c03180308070219080d0507090b040f03170f0306012d030e12030405030301060806041508060a06080708030d05130b01080303010f0603 76
    0x105402072a0281e40e014041d81070001000c000500140240c540450203003140701035071620f44d50580b41290361180e0005002442d00000c0c59820701c2c005c0000b800301c0c4680e515480303810740c035802c0c010704800412407002c0c9141019151206401c0c003003c016541601035000382e50302481d6242c1014080d18140416400501d0b58801d5064480840c16107000d8030310a0800000c0800c0780d4407880c0b0211821034150300080801c1c900090006000c1e030315061140d04a903c1050780101c1030380e0150000c240350040c08804000c8460410001d201503228020a054003d402c0c2030142c1581c41519100558481c58000700d0b011a554100c1e007400900f01b00520348038000700480c01ca15615255454548a010621602007849a2440032a0007651141c100c541ca08007440410000750395900d01c59a641c100c00d803600590a450400c01058481e00410420144c45a910045140945400c1040c009150007810b8240d01ca10728400d1400040414000c1e6000308a054015030701e0b5410242c00c0104a0300640c808001c3c1071 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 132620206 1250 132618956 132618971
    0x1e0711030316030e0d0b0f090d030b01140a0324050f0405130b091203071d100915031509020c15070e01052b020301060e09100e06130606021b04 63
    0x15160021021600d616280007021800c40c9001704001c00c03000c10005066000034401c01202d0740031080c86a10510f0454200c0c4d09102d04040290112050111080c2c0000c0c6000440d9100c041c44000500465066160001c1e070702490701d118241040c950a5880c1041e49000c0b410040e070303e000094101c010030201d0b0100428200207074500706076422000c008282c54031540002d05165020f0007521a100100ca40c1d40c0c0c3d591814040080c204450255a0990380b1000940c196450528030b010f082d420002c0d07114104018100b0301e061803880d07040d50f114000c05031070702d1440b0180090040248002c00c1410b4015848100580001e401d2a4400000d542c0400c5080304010b4000e500174401040d042081c01c01c0f0740d607000340490300004540c80c1c00c12840110500c046401d0542c00960045040b200e80740c0d41c9551111805040159103413003558070011103c0c0082d01071103941000080c2540016000f45040e0300c04000d0304106041e03c041e90300240150308516100c80c0c500c00c0030100099000012101000780b41d = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 132621456 1250 132620206 132620227
    0x10060f031113022805030f0a11040305030c0304050102060606190c11040e07030b18030405041109032509050f190e010e06041203060b190201021e07110303 68
    0x911001d80002010342011081d512003250b50000101c062038199581d100700c1c900700c806030500002c0c070b03041da02c4c09031905000302d0f2040341900e000303000110f1090503a4603404410340103004880050301c10100200000000150208020240780b88807801445e101d519200000e400c000004102d103008000030011000c0b000c0f010054990000724508090f2440c0b2218200140b064401e200500c4e041841e10b640c2e11040d9200060420441c0c0c460303500c11407940d403050511a0162079418104081d98030602c424801c92034260002106092080f92a40c240404080080d00d084103482e40c1d0f410b200700003015092009000b40c0d480c4054000080c0502080c10b0542c1d880c1380300c0000034001030b94210003e80c100780a94480d001a900e480850000384040c485402407903841d01d105807030480e41d50750743c40501c104050090040d00115068154400c0c00c1003500c00c021900610141101d0f011954204141c1c030030001180c8125841c00345250915480d44454501700602c261030700c0f0030030300c45c3c3d1042c0480e1007403 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 132622706 1250 132621456 132621479
    0x70906050a030c0911160f0b090d0203040608190501030305030f130c0b1b010204091a0409021005030a0207060c050c0d1106060d0204141509130308070809100504060e1006 75
    0x2250402c000000e81551608081708040c05500c50006040a0030340c048001d02001c1c00410724100d0080c4405600d42c0c0360503c01c01d5640c0088030700b180158000b44010440700e80505005039006000306020244c4240200e0030104446003604100e0200d403001c02404145408410703526445001001c1e41c482024240d1540a481d141901c20899141800a1191103107801400c81c4c08000301141e000755191525070001d0b03000341008141001e1043c1d600c1c504216680341c5030041100c11034010302150740e4519040b008941c60343c0000e1424a100d5020404c0d0030010f442440307028091500d0303a40340b03916009000c0d01e60341821243d9010000700a941031030030260381c401007644d40d0454412038801c030b40d4080520101c1c0181000611010701c0c282d50070104440010201345079922100e080702d42c9042c0d41d555018004620b00e505001800160690002490048c01200040c0e00203030700da001c4907640d855400c0c1d05000c0e00d004407411216242c41d03403104138a660041000543d00c3d0300342401442140d0170070031044031 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 132623956 1250 132622706 132622709
    0x2040f060c0f2003070825050603010b03040302120a0c030f020604110118080118020f1e090604060503160317160f080708030103080c120f03041b0512070906050a030c 73
    0x140148010300c4045041c10401840e683c940502520050359031900610f84511450750b200c41068151040d403045400010300f0b900c02c2c2c540080203035003580d09100050410b42c0008104a056103e80b0105000b54051940070b80783c1481181c2c3c42e42020002c40c90014444807144104006544c01769090000054108030b015401c10800c0c81c255003058040c0e21103400c20000c40e405200103500c4c0000720f501c1180442c607c3c4828030b00a803001a104007400c41407081085142c0281c0451604080307d0303104914000c07940d030341c00150092022503500e845d01d0001e410f0042c10070f140c0316002d002c00302c1001003021030304440c070480c980101082d003000408002405000e2031450010301098868015400b04003803c1e0a880300ea40c0c21010300d41d125038491914400301e51090408940c10320810524030b440620701d070f040b140c0441e0b11070380203400c0d41c44581d40d45020100320400711201c580c1180000c105512141141c4405050000090040520705205030013100d08981100340195941c4009201180c8032018100 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 132625206 1250 132623956 132623963
    0xb0306011b05100204081b01170a050c09040f020304061103010f050904050f0d09060e0402091302070f0213140609090d052107030f0b0d0b1b04051302040f060c0f 71
    0x80501d01203241160500303201640f800105880402c01155903000058001010041092660302a08020006603454103000c20f1000c00742c18240c0004021200607041aa0480100313034034181401d440708006015100645032004c034095021040006003d52409610f82c81000b814800d840c65040102842060810f03005c1e503030003900e259000c00e0410504111210500001c034068440c00225954000d00c14821071040c00e0000d16030082e002400e14003071084912501c801040001205508409200039410801003074446d80961000580582c4030a04040c10300e0b01030b034400045616001c4400d0361881c00c05003034507000d40419020004112000181950110b625051090b100e40213205040f1030b210b401c0c44052051041c080c00d202c8c496030141c0120211414400381840040c030302105001400050841c0984100e03050000700d92860b14000d8004002c0903401c0c40f141c685501d610200d901078191100301c880f111303070008e800c016416900080d000030b0011481d140484e61f4180d10b401d000c8019003040034 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 132626456 1250 132625206 132625247
    0x70c090b040f060b0a0e030307050102040906030201020f0303070207150e0405010303210506090a02160614190b0306070f0201020f030c03040b010f03031e030608060a0504110105040315110909040602090102070b030601 95
    0x184080d1f45c2c20401d40b03440d10b6000009550720750f220850000580010f2204901510403110b0703481049401200f928401e0303445500600d461458813081c02003562407426680e05001c48450b502d0210384071030140c02e021307501a44604a03e20340d0008501801c04100c5c10703c42c2301e0361815052005030343d201d190854024241140158581040400322543d40e041d0a600800c0d6516103176041d10603400e43e4425521409600780031301180c2d5041861002902d80d4a492554150442c4000440c1207000303105800b07030785003a840010f0405548490b1410702da881903402c402d01c54004020001088440c2030481c5c09011001725a450a500d1940d01410103500345140c1e00e140044403119149a07446030340414000c244201c220b640031309002c0c1074240102010380c2c080e00e1444400c140c3c60525405042120b04690340450706025401032a001c09004200342d02c0d001c07900d50810042030b00c841e0385241816000301d00920780141d94004880002e894039078154098042c0203005d00400c2126a041000190a005200b51b0b0 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 132627706 1250 132626456 132626477
    0x705010518060c160602010b01170f0903040f090204090b24030406090f0b0601030515010504030318080319021501060504050f031f061a2a03070c090b040f060b0a 71
    0x190362030140111565051080182095603543c07000fa08104171003080d0002c11543c0314090045a80c66403042c00749a0410440000c204c0b0610094181c0342c0c08440003045e80e0a1039101c2c030001040d8012640802402500030a0901c0310850718419060074150441c0c0360314225105190400e0800c0d0b4003204040c03441c1011001500740701880d040600b820340d01600f54141c14840303140c4a0302400b815540300740024070300340c0003414200c2d4070140728003440d105844803402c1518554040342c210460f089407805045d040da40000d00d4100c100080d00c6030f2080341c40401d010751f81c00710000746400d86450207600c00c4010704004214590304030007200c003a520140d074542200d00d0400c000c06d18212a11541d0340100104103480d80b01012140c2c414000d98400090b0413043c1c0c1c80005030710425014072038103821110380100160918020aa00144001c607110b0243d0703041a420740c9540001d49141d501c01c06030036442d0001800030f460300740b240d2115118030b101c00700700013030411011a034603001d40b512080512002014 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 132628956 1250 132627706 132627709
    0x53607060f020f01020a030618060e06060c011b0c031403010e04110607120e100c050c010305071707050d0501210305030a02040506070f0b011505090121050702010614030705010518 79
    0x2150f022003400c0096540e0314844000500514180c816550024101a2100c00e1024603004800442d060040e100b11161205000c01899510560303943c2d000e99a00d9450700d00713001c0740800090040140ea2516800d6030740a090140c10513020111460b000c003130800060141903034094556401582144980017101c00c0480800d85500c901d55010b002102c921b80080c103440d030b00c1700ba0134851910586180700f6120503060141e6000d294200014a207030841007417900705500ca94030403944403400303252865400054188100344078805403080c5001403400100040f0a1425003c1ca5004217100400d4a041c0d06ca0142e0341640c9a10340c034002010400000042040d500d2150180d4025001c001c12107980c5140d1850310002c58031135813608842142c81d050000039006203210300e2901e009413544881c0d282010383c20045030ba8140104242d44c03d055464501c10440c19603116851017500113030000100c035800d280d0349000c030403401d52038588a5030108005000590f8044c05032402c0c44001203142c0e1440d201b010 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 132630206 1250 132628956 132628963
    0x14010305210f130302030c060a121104170c01090e091c020c1504080c10080f06030a0f0503030702070b040f0618120516290702030f01053607060f02 65
    0x600d1082c00008240e40d507191501c0c001910841740b00318101c4418061603403d010550040466500c041240032441c1c044189044d00440004100783d140039240c16190120b05040c0e0345c3c0342800f11003651011364458a1560032820507000f07844104a082940e00d00048407a40e2140c4415192221087c96501007480070700810206540540017084100341900a484649660300184a00b002e0b0f449640d41000c0141014082d51084a205039981c60031665140d0b100d840b024005030000b40c0601c2170b0143c1601080b403c021100314a846232029640ea810f000000a18010887e0801030380a407080208000d0038421400d888121002820800c2d20307070645001c88120b02d40c8a610030384000c907850f0101801c00c04042a101c200c07050074000754141030303100e01d00c0b04504000c004406d5120001a118403a41825003009045410310041c01ca601c2d08100d4244c050941e03500380c8000380f60b03403000340641525811010346100c442c2c4a07290300041c40c80e803841c0e0a030b03990481840f900090051600100103000d10a0 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 132631456 1250 132630206 132630217
    0x206030a0b0112110703090b0f190e03010f0e1605100c14032101060e0105070b040821070e03030c0a03180f0315050601020c10030213080105010305010903031401030521 74
    0x410b02005544000c490020103980205d1040b0001980202d001c1800103500307007a564944a2a50744070f05001441c149800440825a4010140b044403d00c2007007555090240e98121305600d42d012944507100c0718400e1800c10380b9600040c0300350558409200743e072918440c01c0d140c5801840e0002d0096181d082c0025807101015083c401404001510704c16180000b106c00e0314400d010740c0c902c0c0e082e81d840e0303422190700442c00740b818000f5908001ca8401f00340b00349240c1c0d41050049022905c0e105c07500c03280103495100303144070078490506201004005904103000c4205200b05502561038110808286921110042001410311070200c0f10070001e040070400d90f41c05816000c500407030464507824141c040c1e11500541041813401c22002507029440030900d070700e4001019110800c24060080d0507000703900505c0d2640c6050000c0d201c00110042d0034014640203502030390000880541c6802c006080d600402120b0141400f42d500400c00540c1c0002c0003100034020941400c0a441c04681c10407241c80341 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 132632706 1250 132631456 132631487
    0x20a03031503051002120106090f0e070504050303030a0e060a0c0806060a030b060a02060405070b160b250903110607020a09110904050403080702060a0509100509010207020a0f03030306120206030a0b01 88
    0x3181c00c03100c010b071080c3c3c1c01003400080060310840c0310380e030f204e60441c0c2010312740c0a00a09041205c40030044026883c12aa801522904000d070034a03171105c4c0401e2454000319000c031501030711781240c5605800c0c01e018080e00b05030048828400e401508201402c0d801c1c0203400640204c2c00003c2001c0051712036071020314078180c01000155507440c00c1d4002543d034082036900780c8840c094514000742985200040b9240c064640c0740c200300000c016207503602022801803201e00c00403603910316414181c850301a06031042c200c03600d4201c04542135003001d8174440c0d02a011a80150010840c070b01c0540c0e503888280b0100c85480748003180c44580242d000410b4010103413029041800c11090204040e04080c8483c4100d078142d08071410f9036546640f070401c1d80c1043d919203045810041301d800101c1d506030004c0d0b51010020002500d810200c5d400f044107581107900696400c2c900782003d000300340d4140500c50040c404882c2c0d4840c51030983e00011107512002d0702048002d0350710700d000d10700c40c0d01414030155032055 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 132633956 1250 132632706 132632713
    0x4050a0c1d04151701060e01120305090f2805270702071d0601030f14160c020307061e03020a0203040b030a0902041505010315030b04030f0507080d0605010e030d020a0303150305 78
    0x242c415444c180c070028040c014495500f000d8003c036041b81809083c504841c1041c01200c51a10345840a880c0d50b4480007076680c00102c240c2521003240c940348a50302c00b040040404420110380c0380c20908142c4225000240700315200540c540804801104c2e4251440b0081c0c64000706864070a0281d25107495507020344082c100c048090004002c82c002803e1041c0380a0700e06002548030106c0c00d50491ba0108400c12000070400007149142241c2448100414550300b04403143d2030f031a0300000d1030419140e201c1c000285682064403500d445100d03d601e060310b42410300f54141003a821001c0e49900640c0116101030f5004000203000c00f00301c2e00039004154002e8401c12204c00c020000c024001c0c0c841c01602d0100f403e008180300d00794035a0407543c00312a00301120521684403941c00300c0700c60005650020801400340304542c00b08254400511601e0360b50000041d80c0c919110002d44405003020103a0322035041350701130807401c54000c9000c1c40307607990515000410400c00c0c4601c2650030b04540000c2c00c01e12 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 132635206 1250 132633956 132633959
    0x608060f19090c1802030f0103080903070321030605030f030d0c03060302061b1e060c0a020307120c1109010803030f0403050c0a0302060406140402030d0e060909130204050a0c1d0415 80
    0x20f4210f600741c050f900c03012a00720099010141c03010a034402501e10b410240b03c50001000412700a4018114100f0014251b42510391b40791200b10040a03200705140100c40d104080c400c5554061280c08018001900a4054981d40181c55902c81c01a040401c80c013a40320f030071717110b031041c0300780d1203080a5a40244040d80318440d0360304046034041000c155145078811192408900580c400228409032002c400500b02130f0b075143c0d200d03142030300100c103210158441840360300c0000c3c0002c14660142c0320150754840e060841801d00d00314000c8510070391806014854014440520080100c030f602030442c203c5d03c0950307119403a0840f07081c480c0d040c403611103000d410300c050101940440c45901940c096441402400301f15403091380b10b900c003918000d6269002c503880301d4a290240745404d1800790020103079414580750001250a644040309e0b502d81000345020f210003145014407a003a0050304c1c2d070b03104201e0003540b050068503002508090071400c15000c00d000c0055901c0b074021050380021012242c1ca4079 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 132636456 1250 132635206 132635213
    0x4110c03070b010522020d060504020c03070605060d230705060c0c0a08010b0d02270103060c02060906010608061507060f060305210a2708030912010608060f1909 71
    0x98005401c22215411110000103091811982c1103d500d0b42c5007503503141140368240c0c00c90007580150910006c098844100280ca552507102a01140744558051641d42d0070501e486000c446004091a20400c41c01c80c22002143d150071100503800e03404c40309140c00c520012045883d00d0b01e43d0388120303417040300001c034042c3c501c101117000900120b054030300c0c41c400d03030311010500e0903650801d69071380d0441c26562089001d440c0c01100f0710038200e203c6a0740003101d402d00d181c029281509030429200c044d20740029254480d0b041080c5540b0804007005041c0ca5410412300502d801d00240400d81305a10040d03201c81100e580314111000c541c0d00c80001c004580c294070100d4090704141c88292224010020261304502c401900303113002a1072207010302d1030803041c03403816105440483d4072a900c0740c03020907101401107101040d0801600c400c000071a107400e04041003010401c40030100380111b904000b0200320001c0c00049943c0c0101456100d46842e03074030060311401060078103019402c0705d8203052041092 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 132637706 1250 132636456 132636463
    0x604020706050a020901030b01020705130c12091b0b070c0e0c0c19050601050a0b0a0302030c0c1621030801050d11030a030807120618090809100513080c1e04110c 71
    0x2030002071f00d00f070200085040069031280001d220751a0400d1400003a074114102d5540120059900b5003008281c2c0e09902d60803034119041d10204031042513603c0902242c281030215068010142d540307229203028010780e2526001c0c004c520178051200382c10404242480d00304000d030340200c110601185c80180b2010801c00f00c480c10440240c58a002d1403002040900742806a582910302e1210098a0b1201d811401c40007944002e0000c1000c0809008001412005110200824090410380d8105c2c2e07080441c030400c11071500c44100c103450089a10240066005030300181140c1085514070302c544c100b401c14038404130380081c1ca10ba0500907001d01c101015044512507008146030f0ba41c1070344030100200680e017181d1041c041e0640c0c2144110001000c101c0e503400075130601d881001d006043c00035880c0827441061402800101051022034410400900c3e8003900004121920040000c00d99240104451648895201c04096a0201010200c0d2180e402c010547c645400210f503580204c2c54003140c4 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 132638956 1250 132637706 132637717
    0x216050c1201020903032d0d0213060201060501090501050702150f0703020c010309031b2607050f0c101103090616060c0806030d030207030306080a140609030a12050604020706050a02 80
    0x71481500701840e14524051094034000800a4019803524040240c0c1040341c4c0003981020150842c51820a510102a08090b01610311485005a12404003043c0018541159000300085a02d84481002280c0e48403500740c01711442030800329a61001400410340c1100383c1038100400072000074150300d4203c54032005002d0203000703038203881d44100380c10011030070360700b1100c000340000d000c10b56002c0740c3d200d01d88c8a810805204015000181140300c1c00091259031b448071b091800c40d400b2401d10244001030060105212081000d04044102c0790b00160400c000318891008101015920280d0704d90204111481da9200030300c401d07103607070520a0304c4c01c0d6541c0004084910307500f0540e810003c603024080d90ba004006c0180a031010584d00b810440083d0411a401d404040d00d4180c00100b8040a00103101094013401030001307044850001180343c82c401030010982d070340c0100400c0001a80c0204a0951410000000310b02e032f03114200001c000c1e000b0b000b00608501d140100348882d01c1e405a00030070 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 132640206 1250 132638956 132638959
    0x40201090603111b03071a1603090c090c0903050115091407020601031401060e01030b0a0606050f0a0c060b10031d070605070807021f0f0315030809130216050c 70
    0x1600107884140803020f6031000c1d03036188010382040c0319806207a100240104694680c08084a0500d000da844030f000c515041080c407042c0200d900288030031500d040c611001100601d00b0107001d5100341e9035851402c29060300c114400d203555180003001561044210000030354201c4002c1c011080181c40d403034031f40e49552080c880749502d07020984000080c49540c80d80b107648250054400b1f0f80c0b8584803002c031040a120800c689560300d19020400ca01c850386403e0181d4001c03052401c2d1450404640c1e012a100c640050007445002d0100030601032500d0b0440f400400146402180311010346071100191000940f40b5a102c2034502281218546c50750080c000055203010420015020303107169900c44056004e09000110100007100110f19150000d00307003544060017103880c210200c000030100c001c600c100c240000300c2c0052045e0006a06001b0304030040303d143d040301442c0c0e14651303c01d642489441c21041c010f005600d000b84800c030396a03040d01c81e22820204c00301c0b24071610345007194a0b030b110f82d119035 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 132641456 1250 132640206 132640217
    0xf010c0801050d08031303140d1d030c1b06040b0c010c0e060306011205180607200105060109052e0e030f0a0b010e100801181e03050d1a06040b03040201 67
    0xb524600200720f00d841d1600244070503d161500703151146c800701013000a41c00d110040341604990309020000f4120742d03102c200c0000e24800082d4803c502c0702c15130700038a00103034024030411b01603110100d0b421007850044500700c000424070401180c890701032540710304100000400d0000400070190081c1564400700d543c0d1110b151810020086c56010035207120f80012141c101142809001e81d2186d50030007402c12004d00e070403449010882c40c0040403203003000090f1040000d8040015802038000849881c90004d10a40c6840c40c0000c0201c58141708061141c1d491014585081d84002555501d4050700c21510900002050001d044011300403105800fa02c1040c0151060000c041180c5145592000e02c40306103074030b84004800002d80181460124410f50800004c025109102c0c07040e8000b8800b95400d840809800c14040f80511801c1008440000320340345c50019511004460052114803800984e1044610b1102d5501500b681216040b0074009400b0542620394000746204510076a00c0 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 132642706 1250 132641456 132641459
    0x20a0305060f042c160308040501090e0603030a3203011e08071502030408012306030a0b0402130e03030405030403061d0703020105090d0204180b181b0604080f010c0801 74
    0x1840104c8000012030104214000200d812121300e40041100000041045489880b00510349071340d414115402260180c0c03002030304000c9941c0200c0104010210019108a149400404a03440e03205140c0660104141070403010303455445449840300c0381841c00206038049660400c4000e544d4020b000d41d19811420100508408801c955203500303171441c0c01c0140c60072524041c0150700e908040303403145042d0f000a10003c55a5a400d04c2640b00c03039050405c050700c000070341481d80c2d9031030701024003c18025006100d1600100b00f80190081c0c00680c16255048060203005500000f0001d501d100070f041c0c0800418002032200001c083c200340c0c1e0246008019600044119030824003020600520a8211380c10404c059070080c00644141000540700c0c40c0b244889a0006084075084030326040a031608081150030300030406452503110a007041100f0004c3c81c0b1000742548c81843c01502e012018603c0991140394072000d0544004240c0c0d181103c3c8010303801c0c0038490180013426003160019500e01c00 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 132643956 1250 132642706 132642709
    0x304110d1202150c0a1706061b07090b0105040837060212010602070e04120905040207051b0906010e04090c1212170402152d0c0c0901050a2601020a0305060f 69
    0x11514052911b80b90400036640c2428150480ba6000744140c0d4406002c0c0f104001c50b50402440b4402822000090301241d07080441c00c404540b651103c11341000b01c20300040c4108000021700400b0010b40c1c03d640c40000d031b004400503c07178407116605222001100c02e803100400919402400034411014820711841c2c3e2038900807070361401e1921403400070f901400c011802092202201d10001c800900e0140d88032903c41d0003083c180e0380031040c01ca4080e80a1880205080451090100c0b49481101d041c4550704210300001c0c01c4001c02d0819a2080b959105c0600c00c10640301d00c02e4004102100121001851a0034040a02d441000350383c00480e0240312086140b8071030b0103105101d41e5008080e50301e1140741c00e080b40641e80142c0d1058001c9001480c4001d004180c11500c801007412101c8610754400d4241551810010380c503007074a004040401c01840075964010724030b020760b902c00c89550991222401c49a5100700981460344a6520005240054541c50703080310303120740400c0c1c070b8840c0c0c034000010 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 132645206 1250 132643956 132643981
    0x512011e0c09031401060503071203030515010e1507020a0e0f0106030651020d08041707021909090309083403021203040f0f06050304110d120215 64
    0x1241d440010100382080c00050b210030440d0000210324400000d04a89442c003007442c10764503402c965036142030b2508400070140c0c94007a0aa220842503c2060b4041403503002030400c20300800d12034030030300b880941c40402c1e5521806680005800a024403000d5654500f040c2c261601035446085543c100d030004144280280140700403a240b5118100c205401c001400c8006024449030b0b00690309030106040c0b070b921201c103081143c41640c2c412000c0f00b518481c0d01a183c00c90b0480c2800900c070070b00c4104004101c00c000c2d584102c00401038070381da641c5042d200040c183c448440e01c1045010260342c0100d0145005e40c01254614483d45174040102d0712481130903602c100b8413405424800d0030861001c1030740c0203039400c218005070b00001b04601c03548a600140038007405d184500d40d076900c00b003010440b601692582100801c14010381c0150b036401c0450040c00707444001c1028058451070b801480158644038012209035030045400d040849141c48000c1d107a103c4000240110900d82c004120007041d8503 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 132646456 1250 132645206 132645221
    0x60e030408032203050a1101030b03150a0c05040e1303020c040911040b060409140a0c0e06030109020a09031a09010c03020f09090a0207140a030f030207120e04060512011e 75
    0x1d0011414100181c21003c09407103190304078a50341c10303003020000000c1d8041041200c120300c1000801400c00310000010219410075136164030981c0580307a00bd00c45103c1552294001c080c03e4408103d28103442c60580741882907070320008008030803404020f04902200c0100c20454400c5d800ea4540700c0c0789404020650f2082d54000d0710408800c04000c4044c900b0f544070501034400945564105940c402c10700c000c98540c10240c60492150307504014400c80c3c030740310b00c000000c030034142441c0110b0f941001c01c09038041406074401056000074036001c0c207409a8030202c010340d1b100343c910b40d5008070303150301c00c20308101138075240015070900307100705609402030080c1c440702030107641c8090030405010200b020a07240900030100c41c0c0d600704054401700c0d105400b90000003040d20b00800080c0404d00d001003414208001c40403c040c414081d8070000340209051804a020501d05800d00c0c4640768000b8000b081e9650107981c1c0021111551b407009541900300c0c1d40d9000510070300768102c031800e00c509020390f040e0 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 132647706 1250 132646456 132646469
    0x110f010507050904093e030607020a080c1c09080c01021f151a07020a09090210030507021c0206090709060317070807150b04050c09030c1012020d0207060e0304 70
    0x748540080b0b1306296211480c01805017003140a00171075102018201c0503644d00008840d10102a12903072448200401801c010b02035005011510308194000d45841e42600020442200006c1450301c5101c20080403180103010001c07000d2016003a00c001c0c1c1880258414294540100c0d05551003940c00441c0060ba44004146040074111a00100b10002c0c818001d403071700303035104a01c000300d00d11003014070419083e440c0b039824941c9d85003207004100e811a00d552000882031700303140382c4400680f50310b1031410410440781000300d1640c0750908203a040c60300c20342d48411000d8481100d003032140c0d03002402502038014881a1a00e46032903108a2056407268000504120985104090041c4181006107503150007003b22600b02242592400d00144100003121400c6454209020312403500f481180d13008040c4d4019103140a06900c0802c0d110204030840500c218203c00010849074040d14100307114a043e03042c1155101c20314204030703009400461042e5841468200b10075180f19000040302d0680703d6 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 132648956 1250 132647706 132647717
    0xb0601031a01030c020f070807060e06030c1c0603080c01060302120312011502010e0304090207060501091e051f08060114010807090b0c0309040905100e0601050105040608091903110f010507 83
    0x401e03005501030700203200b81000f1072117804170302160414148074103005011140090000107107000402801000c400f406d65105031810024010b2101206048a2804400e44c4410165050941b405c000501e55580701034088100002c041d2414a0190710070010380b442110317040750803114a08103c2e96400380c03135428405c0300b625000500c6016414846802400400c1c40042041c0c07185041060461f0020b901000c18541c000c40c1210800416000da140500000c0c01e040049121040e0011000d40c1d2140000810030780c1c80c00402c4c81c1c1c9550b4a1109100428800c03000720382d96441a41c241d481c0824440c2c640d0301f116407084541c8640c0b10f00c06142c010042991442a198241401c82c00b0b039030b0100d40917400600c000c000090700c2d41c0b01c50261012241c00350018003c0c00300303e408840b013640d112141201454000d9001800243e030400b00352002e4440c103180c50880359a40480e003d1420f240c2080b0001064052800181010743c03040207100156079610640364441c0701100c6090036a20180c0f0b0b48404140c = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 132650206 1250 132648956 132649001
    0x1090b030a08090411071a091f2c1f090201020c1009030203011401090e0a0308070309110915270411010302071403031e0f040303091a0703090b060103 66
    0x74800c2c0040e120512000388009141030703c6803140c12250307008074401c681c4490b1024501d0031000820151a502050304406084a03506840c204c17940f20380801045184039a840c200009240c0d070f403813400040034203a49880c0454042e4003082e15943d07171200d00d01d0f0f030542e41006008941c1e0742d1a40a015041a13040e002040480e400d4000c00940c0064200b844c01005804600040580c0d030900030300b03c842c002600d0f81e00040d41041c01440903180003100b00c29095006040c0f000010b07602c80c200c15806000d5180018490305a80b0341000c04c132035540441980582c000301403010500c00b041780441041800c551800c0903900583d0305400c60705020040d1440110042d00017404524802c140e01280201454014549407003030f998480381040da0b090303841e001c0d8000300400c0300140c0400140703034150784041009001c40c900010b610900c44402403004003010313100c281c09c804020710258512152a8808060301280c50702d010010004d140f80700042e560b402c035410204202c0e50191056040c1004c28118200261 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 132651456 1250 132650206 132650213
    0x506070209040f05030d1a09070f1b15020d0c0c0807030e0414040b090606030714210d030b2e0c0201021c1205070806010804060902060405100e0901090b030a 69
    0x180000b4020354440414040c0280010b405100800181c844280f00003284180081d104070b000500040290103101024280100650058921507000905103032010f20704500c00c9050203800004640100281140807000340100c800750041d00108000d120100617078041104115800320b0790702001f802c500403c20404020074071031700500303090010141c0f011820720400b01d10038900d140102c6050754079104c88014024a02402d00042d80c0003501100146038050411118007800e00300d580400b4401c0024030f81c0d400700e580218141d03004405001c402c3e901400c0c40f07a0b0000c1c0c003a1140707080e0944104400129004a4841e9140340340c5204101c003548203070321109045c140d5151482c0007059040d4400e44100100b8210705005650032501e05584006180000e000d503402528001b820080600210804020301c03664000145584290403010105d1b8202c503038008106940719680026811040300002824443d800480e0800600420750303800076160313624201030044800c140d060640c1a041044c0f4100030 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 132652706 1250 132651456 132651469
    0xa06080406060e091c140912160b0a020607140a0f030b09010807080c03030703020a1b031a06031603030905270103031709061e04140d2705060702 64
    0x1c1c8100c20020760107031039100d600400700d804c484840d10382e404451080f030100780d0090340003201141c50400580703001060321140b5060250307503216400340000d2400150f002c00100700e40f810f411a01c6282200e0281c41d01250041d07503000903c048050f20940020a443d14810401040244140b006241c144580c5d440c00312111000c1011040030140c46044c180c00340d03614138503001d000380034240051408924280702d40e42000702c101519071281e00188224004a0380204000d81c210341d00099410400d880718842c1c0b808004a5003002d0160701d0f104603001030241000e8450760143c13408404550b820b08001c160403410101d00c1c08002c1c001603e61300708201c80e04089056407502412181d0300b800c0030707240c0c62001d810360000b64010ba0002e20102c0406120545019501c3e4000920101403d951301c0e200e152641c18069201800c040242e030080010184030b040380000d03e07509030201c1520441c1d041c0c000000c0c0700c025960070a00c4000d00d01d81c0c0d48107820004410712011903038094081400c205460302003101 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 132653956 1250 132652706 132652711
    0x708070309050706050904060e06060a0503071103160b01080a051f06030510050a06050324180109030c1b0e15060c0316060c08060108060d050c27070306050a0608 71
    0x61507264034080c000194140320280191856039105512030902d10308210680c2d0b400c1c0e02c6403000008141c240446500c038034084403005078250810503600c2c0ca9280044034441121048400785000115540c00e566180360101c042250107000e4810303443e6201c07083d050309c0d0310031940014459401102d120030801442491130704d140447c090006451956074a410b41070624a10490700115920020454039510503c42c1501030031095000b000d4904003c00c0062080e1704000d600301082c0e40060009075000d2120752408004101c2000031b02c0041254035011b1700e8990410411107040c08803071710019610610403014012984282841c0f44161103031805c4581c1c5100000342250400b004001140128804000400c1e69214050035551065981d060034030445d1208030100f81000141c0d024015140e92000c2c1c0309030421070072204880203100c54500786260015510f80c8a8100700c544170414145003200c6810001c0c03140c030500349030241c1da92050440c111000c0b0b0241070b1b070107010b115051061601c644002039 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 132655206 1250 132653956 132653971
    0x30607030b0112020a030f0f02190309060204091b02010b010518062206110c010c02010906181a0c010e1606050a02120310032108010b21090106030203060112020102060708 75
    0x11805060310f0b108009a910100b490b101103a202c80e00207081c95500d10440c00c09003d07001d000c504000c4c1c01b400030045c507000400c030402010b44509159090107003960403100186001c0c030301003186800740745c2c070181c5408c0c500c102d14026501e00017160040e0b50054084410b8484190144994210ba8408205154015120003c000002060b08a031040c64407428400034010f152207035529004170000451420750882c131071a04110849008000603600f1051880964841c3d08000b02003404003e880704c000c2c0004c1d4484410003216008000600814600400300214420300038450380401800503680d84012001d14000302004c00d40401c04184108040e03c002a5544103440c2208501c40303d10590b504290b070240441c0342c1c1113030708200b0890744010b0600078000c3c00d12400421110b01001030948041440b07250060500007480443e2205aa01000c00500c00611340203d0790902c0381c4410700030302c1c060208030302a210b0786c0004602c4088c081090100954140d00504480c1d892078030403107100001038180b8 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 132656456 1250 132655206 132655217
    0x19052a0d06080f0d110606040c0e0d0303060906082409100606020c181303030e0a0b040f0506061813030e06070605070801060f170709050d0605061e030607030b01 71
    0x21261a060150030018031240e0024503e640103c0503450801d181e040004045c03004c0c8402400245002141207940302c0004c40300004c1c101c05415041e600744005c8500c9960001c072441040c1d04150701a03015106450111500300b041c1c1e03440d02681d65650f03030b02c1e500c440710a08284e00c01901d2050b000810035480b0303418000f640e10f013428540303101003680e603150021000342c0c2284103801c0090070070140b03070741c075444019210095608110301031130714949400740003400701500e030201c1c0c03000d1800c104180d901059100c14290300034a00741c01c0054000720704a10480e075a0081101190071403400c0241e0503502d040f41030455409072901d212141260451315400c8082c0402d000710050b840d510b803006890100d0140c0303008540c03481e05950040060300705801c44814888000d00e45451150b0040804618010b05280b810035911030b501c09035005203103070740210781c08440c180d403a504001c2e030b40d045103001d010162803248240d00003900000111a015400d203030107030700c42e00000c0c044620a4020f1602240f040c10310 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 132657706 1250 132656456 132656467
    0x5010504090203100b04030605010e240d03021c03020903070602070312050c0a020a0608070f030c020703020409080c01020c100605040203010506032701020a09050f0607020102031b010e0a0b19052a 86
    0x64845d500076510658155548000400030640e88104032544540303802007400f0705200000200c1081a0040206805403513000c00040c10913000b041624015800d0640c5151071040e9000c0c010302951107611502c0c001c2c041c6c01c0d40010418000941401540d41c041100a0b5005450301c0444081c1c05c444105d03102403007840469809a19240c200300040e1615a41c0d030038041c83c040c0400751895004602c1c00080514205d60a40b1003540440d44005a940c100c1c6d01281854013410601001e0140e00a01c00241d4400101c040c0c3e12000061400c80c82d4181c45410311201d40d4035020081240002d210312034000c101003001900a01c002a0303007118205200b008902c95000c8409900d08a0f08a40607071000700301024018001864600d1071000090f004031070441c54214142e00003512401003050a008018100615980c0e45100390020f40302c200c3e030f03402200c3c000000d40c107183c1908082614000a81d078002e002150040380c142c02000e1044250004591030b65903004a220080d10501d0000d01045000740305 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 132658956 1250 132657706 132657719
    0x160309090903090608061206060607030c1a01060908010c0903081b070b09120109051b0d0b0f0106080c090109050609150d020c19030e090606040902190206100501050409020310 77
    0x94604410b02070340d20388407601c1c03c1460180c92040007404a41c40b80e140c0700031400520b00300061455000006840464881845250603586542e44020041030401200c40d2444a0840a00c0403812644695101d0705201e41d0390341100d013204e034003484402c0000c4001a0074004034554000030b121900c9030030360310020740041c008941c0c14074003182c0250f907150900051b07038041454082141c1d640d140340c00008025442d0541d590755034560180b0540b100c00108880750400603a00e601f041e8400503040700307902d8154a03100108200102c001d00810001c22010000b1070a581c2040d010340f641c0c001e042c0c40381400b41c1d051604001140d004080c920341e111000d14031440030b01400501a20103041503c41c00350321506a844800d0034150594458041444030454100100c0c0d0b101c2a8440800800e43e85500c0c0358864801081141c410303900012182130002400c9007040c0718010090b01d202d112942520b080b80c44581c42c075101c1000307034801c0c01c0c0026030500c814040310784a07900841c0c1207010210003008840c2e4403c3c = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 132660206 1250 132658956 132658961
    0x3021b0112021611060f030415060f0909060606090302030c04050a0209061303050c090c07060b0a05060f0a02070608060a1806170714010305060916020a0818011701060516030909 78
    0x89080070000c03040f9107840800c41c0b03c012030326440d00304446082c20000c400c03221011a0000030405052006100c1c0b0b140768464140c0c0c814405040b60080804000751101c4249000d03141c1c81e6402c0390494a0074100068691143c0c1d101001d4031350040c0a8800201180c040101800018002483c015802c11000780c181d520745008008210b0034504191000c0c0c038605082c0c0c14030101c0385403030f4018420507080141402440c81158001980074000258450f201008100b0303030f29060f085503401800000f54400540190703005441c0030701c442e500725401f0036181e0008550201c015034007960020f4402505010a40c20182c0e220b4001e1501c2d980042c60a0b03a40301c4e0303048426000401e61840750454501400303141841c030380360002d40c1800e003414092424070700003244005030010201c402510080e10984240c0c2d01c24840710840940000046071524040c240c14100140c0b4015100d01107495500310b07001c0b400324486014101c80765500c0305820080c3c4102e020b03046001c888011400c10519000c007259510003417 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 132661456 1250 132660206 132660217
    0x905090a02010206010e0c03010302060d06090504080301140d120c0215220b0f070209040501090b0108030a03140c07060507170901060906090e07150c1403070b07080403021b011202 79
    0x42005180c581514000a810000180c010401da841c45a080180d010000b01c02c490440394140c0703083e03a56a0040e00307680b00900c82a040101010b05010500c0240849403000d035041c0c0c0d05050903280501c0c40342040003900d181500c1c1c01490700002c542c144a03454001c00c3c4e101b050b0390000d00100180415101102c030b107030f171200c3e14103083c007050400c00d43c0b0706018518220f4060030300107600034640461100e0442290140a600030711400e24400000d040200a41040320090b5000038021050f58550380b1141d283d4101101da007002078903210548145605011800c0d018048400761030b41b401401e9102c04015020051002090004990820311518100c40016100f8201e071000000c07800e0030f00300d400d4166006d0b540718034021030801105005012010a94004880c40c00c120340f1100d42d03c80d0015640c82111080c0a040c0150840304680c00e01004001041003520401c1c0c60005569048415140200305440140041c0e010720b596a2240c07100040c5210400d01c14104841f81540101540c0d041e40d015 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 132662706 1250 132661456 132661471
    0x1b020705150d02220e01030321020c010914011109010c080304030c0203030d0207051203040308190b040606020109050c0108040b042405010303020d020f010501150e041409030304031112030601050d060905 89
    0x244c500c1a031640035001c0c169020702464501c0541951468800420030111464124000c00c00c03081141501d000c0e81d8121070b00c58804c04001d0181c6546414000c0310b0b00c0d480e03c02d140c0b0550802e010b80641412041c03c076200e01c5030503141e18080e24196110b11000da00020022400c1c03103e01c14298015030b8040000d45454842d02d400540d0300d03c01c900d050340c00c10402410000e003c3c001841032100007904031700d8140e44003015a00d20540d0072504440040074040201040d078005103007076004150250b06400107410b59000704101e400030b1380301341e0046424800807180645603021400225000652100b0380340c000c40b01b0140c0455038045020703000c1b811200280e01c1140564464550843c1958041c00203041c3c0c10380180c02040158900007142c82010780c20034001c0104004d2000380105542c440d40255066243c2001c44c40715443c0150702c0700d543e91300a540503804900a402c00b2048400009186211064030405107415525420015516070700305d200346103030b0180c45400110f0b00d00410f104032446100c4 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 132663956 1250 132662706 132662737
    0x1151208040305120d0e12070201030f06051c0605060a05010c03050c03040518041a0403080703110c030a02010209150c03070602070f05010f0c0e01030209090f04140601120201031b020705150d02 85
    0x403100e00c0b03a000c4030408600f0344121f40081020796251041d10b002d07101419028200842d20720782c01c031102c4005202d43c0e0030241d40111440758901500e0000381910200e42d100c5d0000708202d480d1442040500013181c491140051540294a40024410005411201100e804036820242c5840c00540c000158114940071590b400040009000c1001290050070358507481c0644107007881e0301c0042c08000010100030505450301500609908014110b42112403c070f81030782e0302c0f1031018038002d0207076214411a41c407400b288816009404074840448040c000200c006514000b000d030748100c042c0d0031000060710400d50b00039000c0040340085c010354501e0900800c0000310b0a150720400b4100301d14244034076041500c140303c2c18595444100a158204900c07240c898038903580c1707192101204150b01451003990003407000000f00d41d4803454904640c07a100762809d10a03003181c0e510700c080f01549916000d005a1200008201c98105603131000300c8540043c4803030385084601c007050001c0e6841081c00561480 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 132665206 1250 132663956 132663967
    0x705010b0a090b01200a0813050a051f350609010906030209010b0304061e0516110d08090c12061806040302030f0f040504090807050f0115120804030512 67
    0x35190041c200a003082400c1004503c005a0000b441d107210302d0184c0003003180e40c80781c1c6204d0b520100300030250b242d44031400e039a0b40d95801016500c0c1004500c580c42c00740d26888000301c0c0380d00e0305120a9006450300649103016004841c021a5401e1341c0c0301c4400e5003542d0416172154864511038071110f002150311103c0205082c0310381400003003903059000c024501e2910f803007172005030703104000c1c1c40c1160752070b28041d82c4030f48032800d00d41d001b007100000c08161110340d0442c0714800005900b1051184600d0501c03110301511041c8191503101c0f240c0312003081c0360030911242400c00c2c0100350258000082078111070242d12804081102009800c110316040ea1007001041000301d0001e403081c2e0b41000100140c0154206070350041d682c0d00500d50109169480400e81c100c0b101e2035602560020100101700303024101c1d190800d42490f0740060420340e00c40c0146094030a01d1003050043c600301c0b2000c0004030320024a8440360704240a680baa08651450082000001060040041c000920707010a105a80d54 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 132666456 1250 132665206 132665209
    0xf090b16090803130905150604120303050c070c05011115010b0d0e1b060f0712030605090a090b010b07060f0609050612010c0203120c0c10020315090105060901031e020705010b 77
    0x1003150358000c0b6034550040107250020091208454100c0e844e00d58040b840340c44414a00c140001c00c6083c9503044203000c2400141002c800da00700b0003550203500c1c10000382c0c54001a00e1003c0c0705110025110142ca4002002154410400e1417a20b00c4040145c960501550490a641c000280d010400c600304c041f41000401c0ba080c825011085804c800410b00104500303090002d81d900c41c00420301c9500b01060341d503416221042121180e99000e034040c03802206052000d00144428080c96000304607400000784803141071320400c101581c1003004410141e20744542c0035803c0e8800c2c4022200d03030351202234041980486004803400303840c50001c003203440d1a1640074400204014144417442c0d0317041000040e213040d000b0049a415542c0c100d1130840d1a42c8801a1580520502060110505c90a0304840185450350f01031405a44015243c600340c0d03401004001c81c40c40300307000c0d10f50302400401c8030071340a41c0aa40034031100c18001e1100002124080e80810890708101c0781601d613a51103070001002d9 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 132667706 1250 132666456 132666467
    0x5071103240c0333030d0e19030b0c0c030c0304030f031407050604060507020309040e1c02060f060f040b12100506060703120c09080a030c02150c19150c050409050105010306060c03030f090b16 84
    0x1800c9000851803041851619402503020001d4101240a5800290043c0330780d0140110303281c0c044120200d80c0d4035a902c0c03801c4601c104003110b080d0001340e010f202151405000c4400c0b107021503000780c02407110b0349880c1c0381c0394001c1501034013690540c4002c011400c1c0c1e907101c3c0c0c000d0184e4005240d003d481604041c08451502960104209045410160070800303a1006000742580025080d9010302d6024220b40c00310303006001c02d0f4142680003601c040d1042c140400002c0d0300032181b80c030260600080d22180c0502c00203010b1604000e0100d002858140c40c2c1000302e5004980404d82803904071004c0d0b5a40c201d150401d4110102600042c0c1580b01d04010f6081c0122440242c0354907005007490321410745409a02c03540c0403191082011002c2c9003820a000011500032141c1080350300801c4201c0c3c1c0480e0183c51540944161030105080c031000003a0b56020b0710074038088542c4c0d61203001c2c000c8280d5038214010702a100955250580c1d80001501080050014610071041000010403180d10710001500 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 132668956 1250 132667706 132667729
    0x100b031f0e010c030b030a03031e06090f0b040216030302030c0708070308070e011706010c03021203070203070c1202030618010204180f0f0603110105071103240c0333030d0e 76
    0x18117040c2003840d00c10362000580300710115054500050269603141c07076000100e5000c0301240d00f440c105000400c803115a640840c404100200c000c2181041d0707041400203074002e14824001071014610f1280120b4041d400941d884080c1c030000320b2400c1c240c0d94900d08181c01002e815000280141d0401031225003010002c4501c03802400d021400e201079103031082101c03000400c070704c1c1001301c0341000d9010507000b080740560002551660580b00e19000700020b54070341000c030307065511404074040095815440d40c1d98035072081d0050042d1484da03a0f5a100040305401d084240825590f003007100040c101000c91070045400c02d01c01e008100c40000215071015030b6101c1908560151900c14104002205441d140d0540442070070640c4d10303994181082d00c034508a004a49402d0b0042100140b5101c0780740f0502800d43e502c062800d1041c0c0c807041c51350280d600040300d6040b400c0741d21080301c1000000c040d0b80e00030860302400800b4070003600301000c00d003072070150581c3c000460a004445c6031503143c560020b08 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 132670206 1250 132668956 132668981
    0x10112a07090501050d111809010b030c1e0910030c0906030b0a020316030b03030d11070209070f0905061b150406061d0c031003020612150d05100b031f0e01 68
    0x20f9410b05001030b484401ca55070040c00404441502000fa860780005107404da4014140442d07189002c52105002e0310300a0341d85403107406040404546460003018400d4003061208018142080391010300150307410290070900c5200341e0303e000100040c0d407004480081d00340d0181c040340d10361862814201030030303018081e100d1560041c020800525000040900c5844080ca00131a0040c19900480d0440c071840e0f200c05581400e00d180c001c103500603003005200d42482541c0942e503d039282c00b8100c610946510400c170015110f2041000360f0310305039025280d0200b07103030000b143c02c1359800019032502c284241d011000d030501d0300800c000d01990f0304c51900202100414030554260110054105081c01884444030900200100d100302822000d150042e50340034003619505d8140c2000302c01c11030380449a03030f240300351103071403004c900d05290305107802c0f4603400780c000e021880a40981401800382d0f203890036010310078001021000c14081018108601d504a00043c0340040e050403917080d101000f6080 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 132671456 1250 132670206 132670211
    0xc030c01180302102406080612150c071a090a060c050c030d05040f0512030a050105032b030f020a0f030b03070e0402090a021c0b090609040510112a0709 67
    0x200042500890240146901d407040001d20170000c08811109051040740c0a8101540c03c0010402e03d03040b00b102c6000e0082210580c80c19031680d4030142e560034075203415410a070b0074030011542004075000a404954400c009510800100104001740c020b0102e40c00c01c1c040e4043d58555091040c81d01c80c1c1d540c1c4140390300e030152900f100f4012283d0381744114080b1020b49641c510002d1b00340007000030403506082d0b000d01034844090403406515407a170016174007440d40f24544000010703140741c00940e00d81c0f1185144043d07100700f1f680840c6004010740c05803c4005140d290314001c0b8400306280300418462080e43c4801b013426904a400408075844c0b26041c2d07000f60b1000c01e090040b40415104254804e504503591007550b0b5820040300080d014032910120000050b071000d07c41541030703400140d07078040f0554101d242595940c042020160341a00c0c003800e00d822019110b210404260802408540500c01e054039204514240d14545601e098200c00458101040380309090818490b104c0200001d40c400d = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 132672706 1250 132671456 132671501
    0x1092301060b04170304080601080d0809150a090812093306060a05122701091a060a050d0c030501110c070e0a0612050706030c0f2c060c030c01 63
    0xc40c100c3d1240d80581807400804400021135000300300103c0b0081e040401c20380f20b49503511b194240d951444520008041912000041c000303140c00500c2c85542036940e4502c081c141c07a10a00100100441a07055592610030800728034225146000280108048401005103643e17014107005070400d501c0344900d19031344100c594046180350f2810340d60003410848115581c3c1d0300e541801d4030b41d4401d070030520321080101c0b07003082442030080c8070f40504841005040c0f1f0290100c265581d08070340da2100010440c650720066003000010644480c1e503c00700151003001c2e829111000114003001404040b103410050640c00c0c41040001c1c01001054003540c83d04608003d420a84140c854019000c1c0e20056490390f0001006269140c000100402d4541490546810350741001611044c5174041c201c0441e0515a40305040c41c81807449281c0000d640c0d8400407c034031242c40170075420704400e10b040030725140c0044081441e9101c1d4000e0242c07840d040c009540c0d40011071090750070350750000400c80405400501 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 132673956 1250 132672706 132672719
    0x90a0308090a2109030b07090f0e160804020406120f020a060c0c1205010f06090f050c030106050405040504060b150c1204030308070305091006080706030b0604050604050904030509030109230106 85
    0x1800b401c0b01c0002000c0c201e00429045503005455400600040781442c24001f459420141c00070695045103101001c1d6034807070f02201a43c00c001d861000e100d240398000039150b14440c4242c603801a10081000c01d0360b59561907140750049500800b542c202d90280403504c1185001c007103007070040080e400c0c16402c039521303601c5a804011051181c55544000000e450080000c00e6100100c9207614032030821440ba00d42c03100c1f5004015025503a40b8035403508000c40d1032540b0007400d580c121003c0b84d03101c0d4905400e00060101404002c1c004440341e544400c155000307940c607800101d010300b000d000c2e038503150001c50011901c0c0c100c4031409900011000c01c01072010a0f40515207992000c0c01d42030119440d103602d1030b91490805603045d8003180381d10b4094081094100422450211038030380d603040c484019107008005140c425403003090342c0400104000c2220b410a403110340c1e84140a401d24505020105000c2401d680095000b22544075000c903003540b8044006409000d55400c00300200321240c20300c3c0 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 132675206 1250 132673956 132673973
    0x170108030a05160b16120e06010521010c0c0c090b130c0e030d02032106101110021603030615020607030e0708030d022802030901120204090203090a0308090a 69
    0x781000c104140041d403a020b101c6000501e9201c3d580c04003a4500c0ca10340000710300c00450f40c0b0030340d4a002501401500003039a106000d640701da1110b18014010741d0b440e0004001c488a041a11100103088100e8141d0030014280301d91200007030300d91a110a80c2034186801ea000240720780060319014a0100001e5082d1200c042c14046805d130340000040284c200a01502d12603807040340560f05102d400c850a00b0a0790120190505505a0b80c820030405044880f112502c03804507516900544034800c0161010312480b8924400b01c0000c0685070b05140c080c020400b640c7c4041c11803520455115848000c0580c5482800000c02c00c00610010301440800300035150030024203020101030b190200b6503101c007401d000900003002c44404a17030359500224090000703500041c000d021041525074401c44503900c1d10208402a99203a0302652810034420015611200301c010510140d41c1d0900010544041e0392000b51300904c0410000c140c4d00d4483d1400421010005007070024540007254540c00040b01007 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 132676456 1250 132675206 132675217
    0xa020d0e060c090d0c08010c0f0801060c03050d02030c1204030903020f01090b090f30061503120d02041203021c0914062101230a1409151306050117010803 68
    0x1c4038006000d4050381031100c00170300c454103d0120b035440c1500244001e40c1000909001403006e4588109982c1d99240958410b10068009030102d03008021030481e040c000d500440d444010b030590035042259104c4031418402c82103030304030701088a51071b09006502d000050b0040c0c0540901e0a9841c0700d0402c15140d00d40e025500040303010b100110035620309540c0d41c2454454514503840d200d051780e501c600406034926140001c00c07410740205004250150070f01c640c4d203055608060018a90b114080704c8403400341d13000b55021804280d00b480f02088402c503c400044071507005c0c1e0f00070b24440d014004215840040d2103c40783c2404405001009603809400c00f10380f0054086806548558030304440480308000c440c0e000c042c8200c20303c004030300c0140300c80410244200040207201e40740340e140f060103070030000c1d4011401d0b15080f020261003a45828008aa440201c001c02e2075081a10318010a01840d103540c2801c0465484e030205110f02c2d40d10500482d01c0340280400d015055142600711034070792103075 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 132677706 1250 132676456 132676459
    0x301050d1103070911041a07050316030306080601060c11010305060a1509180e0d05120f042a09111303020d020118030b040b1509070807020a08030a020d0e060c09 71
    0x161070701c0c08903502842450010078000c1c0c818081400b0300650080103901030300038101c4102400c400703030044011200581d8030040d803120066181c00304a107852110005070031021404c00d52110720100b6180c10512225008201d03c1d250b400c0b04c0001e0349009112000c85011490402d031410302008001c3c0c0e42c1a18100485a5030840f110007045581c0048511200300e4004000040000c440a42218500e900030f140b030780c0755402901d804098250040f105486210070614016000801290f010348582082c01e0b0000c0c41010101c880c0a10030100c100c20b800d50000400b0b07400c514000c204480c0c0450702515542d040d0054030586444000b0345000006101c40c000a4050b08031400c0f4082103901a0610008120500b0004142d40d0340d00d141c0440c008004071401c599810010b000301c2c82050301940c51888081c00201481555500d143c03003101c207520010042c604601c034191641001c038500100540c02140c007000050307682d920340310b480c0091b140f07480002400365001c101044140740030390f019105a580c0 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 132678956 1250 132677706 132677723
    0x10f140402010c080f0c06010308040f0b03010317090d0203010c030f0606020a03140307051303080a0e0109031e0809041a0909030a020607050d06091a011211040b09040912050a030e030301050d 84
    0x2c08403095028090052004040e10031f001c004000c0c8031012010f40115100d01c43c40310f440c1901c44d40d84001500003803000604500492070f9024100d44c0c00c0000e02002e04010707010740d030f050390b203600000d0030345010303414040100743e440144901e0741440d0300600001d400d240c001002c1030740441e42d0080486000c481c440100b940b011000c18031943c401c0e0111031003034944002c0c0c000e40ca9240e00740b03120a580030030780e050041541d403203a0002d2940a83c2180c8200d81c0c001c0b042c022500031680300c1d0903280030744207401c0310310725820442d014482e0382c1c40c403d552000c40f00300c00f02005c1080d41c0e401c1c00003402c0060600821680300b402580500f560004c0c0084d4018850b1412640352000400a40701078100e03078211010403400d1505256101c0040c5019130205a0300340c1c0e40050410f41916450101ea50010701c088280000300414040036030b071031008101e000c0d0301034000a4207100c161294038181c0c2000c5000000100d000485402071649409529070355400d40010354503651505e00022903011030400d00904011 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 132680206 1250 132678956 132678967
    0x1140d020126010806010f050907050901080402032107050c0306040f17210603010c03140123060703020624100f0c0c0603020901121e0506150c010f140402010c08 71
    0x60300c09603824054000d00b03098145561a100599101c8000740506e03c98100d401e000003686282601e0942d00441160722503503d0100403d00450f28000d00420698240c8a10000010780301104244a00305003a80e43d541510b8a05a00e01360f800e00d444010720910950108081c800440d1100ba0360b80e00381da1340705507081588094640e410006000d07040b443c1005c0e5403002207007580d10001000191040313808400070004462044819001c50310b0b02c103030001420360400014055100c0011f2030b40e24035009085840e01c2c0c8002e010005080b0390294a040340141c21240911400034071910b04240da4404400603400c101c0b0302c2c1404100101d690303011071001c00c41481c0c10360704d04034050304c0000116074220174801d003015180c61001e4003a5010952281c00140105010183e184281c882c62558400c21036044940301544101003004d403001519190f40442e00c0c01402030700311184002000480c0301c141c00410070a50780078a840c122049540c2c1c441c4481c04245c100001030b0385c400300c614506640184900c3e200c2 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 132681456 1250 132680206 132680237
    0xa0504090212010509011d0303071e0203090d060903020d0c150209040f0207060c090f06020615031c080106030506040506010e01110304080d1808010209060f0f13091401140d0201 78
    0x1082c800c1d2808095440d00c400c0c45800001900803121001e00d404821120810084030070f0341d42e20040710140c0004251507c0c01d030503011410200c112105151048030b0070040361400040c40410f07081d0003210342d20345c1c845005003056010b01c402c01c40301d0214102162000790980328900c0d40046180020046030380020710309119a904e034006400440307100003c64440c1d001e4540b01008010f404010404030320351040009050a020703068000356211a4094103043d1505424000306618842e007950b4103009280c4280d6145c41c64058154100d00b03a6524039420f5490302c00c018044504c081e0240340190305007000c221850b41c0010007400099020b281c03c100c2905982c80c2c0608502480d00402101c1c003078004241d0515502180f016940c14001038006105a910a581400c0781f1400000582054040c40349107640c4022134050020750408808813458564484802c9210748550340041d0342c8180e4955141520b6021240b4a6025114a00040343c00c501d00d100007554210a414000341042848425030000 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 132682706 1250 132681456 132681469
    0xa120305040b070b0f01150c0611041a13140901121505090d030e0d02061605040806010e070e221a0402070b1905010302090402010305042609010912020a05040902 71
    0x1000000c04550f00c91501d454801034148044e1161081c6040386030004c90f00112072103106400d00c2d41a1500e031606441991000b0180000c0075010712608002c1c04000f40b180640c91050900b02c051004950303840700140402e0116842c2900200c2c1001900c07070f0480d80648031302c2c1000c1c2c1500d485101300101e40840e8900001004408a02100d41a00306014042e05510001e1040b820b0101c2d9107060010390b241d224015070341c44041074008016402400415240801000910f8100120303281c00d03450142c9400e0498034051081e03000d540344c0700c4200301b046522503008c0d0750280c0310401150a00081140840090700701c403800a14051290799031117030b012200e58022044001008003500943d2251a0750500002c05a01100d4010f41448203142c81511301e0342c1c0b449118145c03a030090241c981034885030011402881e000b0f0088600988013072000750b4501c0e03600030180c0c0d55100c0303101190f500d41311240010f00045c101d80c070070340c00d201c146004000169039581c000f034190b84065a00050054160000641 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 132683956 1250 132682706 132682709
    0x60e0c1210150503190c03020301210c0b09011413060e061201060e03030c070306090b010b0f1611041d0f011107060e1507030b090105060a050d0c140c1506040b0a12030504 75
    0x84103146c44040031981c0d406402550480313015601075a00360140c4c94041e1081e40c6850350051240e40700850511400150901070481c0355418900008a041c1c0546c1e1f000480d4001242c010001101000811045501202c01000792109071034542c104002003012121241040c0251020b01940361004085602e003002030301c1d050b403640380803605050b40d00d0074040020080700205444480810001094644900040380c231405681c00c04a881d100d00320681325001e5209140407034082c242c0714051b01040c1c2c2d80c0e000d00c0e007000c1c14030f151076000060071090b19850704029107100310042e4141034121559081c00d9064850090308070714007141201d143d1920394240f10344422440020104a4240f0000541c103a226082110060f40c607501d503641c031502008050300412160b040011002c02103098506181d400040c400341d0f490510703100080320120016000d80000c00500c000d036118640080d03500c0380116484d90040ca0a603010003a002040011424808907030264a0320076184928480c04c040c880c134100e40 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 132685206 1250 132683956 132684001
    0x181504020715051b120f1e070c060f060602100b1009050f03030c161a07080403230613030201051f030b10050a0603380f04060e0c1210150503 62
    0x41c0e440e82c00d05c41d01d4a11034004d4443c4500001744100150000c0104803505460504100e45411182d880800449a208a0700c80c215456601c485500706116210b0060b880541080d40140c01c120b152912a01c0441c2c17501c1c0e02c00351260402c403240f40107030358110b0f00920a540099840f80007400c3c80c100403e03d140b1400c442c00b1010b22410307403280030001d103500c1904d00741c1d280e040070141c2036019000c14150a0080c184041c10344d5200f004208005a148501c405c10342c01840c1c204416140e44c803c1c4035003071003821154070380700003442c0300104101903081c0701e040d8bc400000a46107070031880030200140250054040103006140c90303c0401d121508010b858401084010b00031900310385ca44800901901240010050400350a214040100a0444d100d080d16080c0501c647c1415101405c00040003c22040710303401c55500c01c004500d0702a2403070224400c0c10910005503684400054204050b02c00611180003a80c5e4604140482c110801034030f0014206807524688a440b8070200015103403000b408030 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 132686456 1250 132685206 132685261
    0xf07030303060302030706020601150c03110601030305041d01030506060121060b0a09060518100e0a0b030603060702060f040204051005030a150f0207020a210218150402071505 77
    0x2015407681103a020341e48281c0540e00345955030364059aa6910a008200c0941d125000f0407e54609c10f11255000501a160280c01c20008503001c0d8103211080e0010b40002d1000942400780d104581502c914003d0380310781c0054158516210680c844101400e41c5041004041d103030152a540081c40c0708504084800811640baa0b41e03d00303044c2d582c401e088820220f41504c0000038014000c0c1d0649181808021821068140200400c000d400c040010780d000c2c401e405508052640f40e0220440c081c00003074000b180d803814810105407400034010711a504561100301000152690044101d80040c0c0c15240480c00d91502039085c0d0f401481c0d5005941c1502c54990140c090000d10300d480400404d001208001d1140602984400c1c0c0c8201c2001940240041004001e0320760586801a84200c59001c2d04800103003a40c005000c410001c08420384051480042c09105240f2803801200080111411031601c40543d03240308000410216004600342e6450000340a0400210b14058444442100 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 132687706 1250 132686456 132686459
    0x150d0207050d0804030e09070219080408030c01050117072105030702100305040201090e1612061205030408010b0a060c0209100812070308060603060d080f1603090602010507090f170f07 81
    0x20803d681c12141a40000c03601c803005070390f80c02c0950b041030103030460f603010707040000c44404802d220740940c03a030464847c4400c02c00000c02501c240064103200224200210340e5514020324481c0641d2407071a03000c0260441c140402403801541c0e5881030b2101440c0b00859251703050308180b402c601482001a40081e02240305035021a4036a10035442a13100762140240c1c1a01c54040c1c0ca280c031000c840360454000412032102c42e40313002d1a280281641c541e0004175a0706e40b11030810300740915103441141d00f80e1011070b050100d54400e015020f0320000998281007840c1c40c3c004010440c5104000103800b40c0c0c0340c44041541d2059052b1400007400b201001ca5120301c200c0026040150700c900300071380001340c0700404180c051a085080341e00807000100103128881407a100c0c01c02030750200e0101a480d210810207842c9480e041e04900b41414020380b106090f5a18141000c1c0c01c2d200001c0c00034040001d50002800110010428081615003800006078184c0c8400e400924065289501140710301c14081c0 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 132688956 1250 132687706 132687733
    0xf0408090907050a08090c24090a030b01060908010e03090411120106090807050105030f040227090703031205060d06050702010605060c0309120d0504140a0b0c010b040605010e150d020705 82
    0x2480d40407603075914080d0399030300c445005e51280081016254007050350000c0c0d08140308c1c005060200800ba800203680b4003d101c0c40011401199a88202c0d4466101d00042010300c2d0003405140c0103021400080c041a0b604805007031306c0b03208822415204540d5030500d5002c4404602c16900c0030b060000c0300495070750319040041c01c40700c0300d441452803034131440e40040390b80e500c188142c078013552541c031031562140c0340d82c1c1c2000450980c402050490100e41411a158282030240d014014402d0714080e00240c2d0441c00e00900440c1c803074000001c014109401d106050312040c21b81801c03030350090f000113a95228560100c0c0549000e90043c0c0d80301c3c0b80070483e5201d804006c00144080d040448a00d00c03816010308005440d021450a03500105405000c02c11414130101410240c4a10041124140b6512500750504903040507000581c1c503075446011100070300700fa202e0000580400d00b0003001c0e241d95500020b80c03882e800c070a008507000022801408040058055a0744d003a40502582c501d41c1810380c = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 132690206 1250 132688956 132688967
    0x80c07030c08010e0703060e120708190c02030a030f0905120f010606030501061b0c03020607060e010c020705060f13031202030d0b09041a15060309070501090e0f0f0408090907 77
    0x1030368408204400016007842c14840c690100c0d0380440038000311444c40e1a90001020804c0e21408140100210044200301f22002002018422031300141c8421000142c04a4035074030000e0341050110034140000940e4001031b0400c842545031810708503e900808003110103044d198000c40e000703049441440c0e402c08010590081424910000700b168070b9a613901281130760020b01c00c24021a0420800392529183d00c110079480c03d000e1008510965507943c04941c05600184041d40c10310f0f51054298011034080c0210286009984000c04280c2d00f04000075501f80b15966001d41204400610b0b5041e40d520b8a402c0fa0085400c000713200c0b16480308400203520795003c20602241145000800041403502c0201d150083c1d401c10491100d2220705d0100514601000d40344540d02505261070480e159184001541704143e4076000d4100c840c43c0200140c0741416541144c14400c459400300419021511142c5503c00c0541480c2a0305889a007801800c40c421002541c0c0c2281001040150180c0c011 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 132691456 1250 132690206 132690209
    0x30a0603140708011109100c0302010626011a03120706060b030903031f030519050a0c140a0801021222050304030c0f1e06030518060109061d090601061803080c07 71
    0x1100034040c1510764441c603001c600c106c02c01568080b0351603001400481c400d041c2605883d200380000150030343c882e12180c48400031440e403ea981252a044a041c25200780200120140750310100c81446a6600c002901e4a40e441c9011001120116130748051041d6508110000e00d5400c1c965a62030a0406103035883c0e90088130410884030f60b0320f10300070099502000d4401100d41100142011100a4119010f1103100c18001d907001e00c2060303c60350205484e10440c00040000c1c10380303010f41150103010b06c17844d400190301c24502a4414420403070420180e14440e0781c080c10900c000e010f01c072240c1004070303114030b214403014185210200b4048104000044468259002142c2d80c142d140c0e43c40d0401c401d18040090720302c01030031800400700b050764007039000903401070051420b4600c50381040300c2e1103251401c26031290784c100d9150401084000719108071005691007094500030703c0d18100b058285c0d42c142c18031911040040d002112514006a0a21714019550001210f03030340705080c426083e981e0856 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 132692706 1250 132691456 132691469
    0xd020d050a140a0803071d0907020c0406050303040b07020d0302030705060a05041a070f0f0905060a0302120705070c0e040303020d050f0f0c1306050f040801021903051501080c030a06031407 83
    0x4054103082c07080009003804020303a01001c03d41c51690b414030202c969036441c2c0c01290340310f8010b950300362190369000700307080c4202e140fa07000309810b11900040105607400303a80300d140290820030090026082c0c10080754460358041d1800c10700d6414900d0105d2035482041e03005002c0e4040c09d01404041e0240750000c03800356009509504400740f00090440010a05540c5c407004516546000700c900360044400c882c0d0581c4600701901d50300e41e5540400c929500c042d1000001980c001020315140380e5084031203400c4500b134580f02d410107110350b448403c65442070044000c60410300e17001604140c86a0100c40d00ca00002c60140401d00f00000c2030320031100141c89440c0c4021055001a5004030041c1c1a5041c2c01c0d0f64010106905182c000c05880551007601585e1640b0000c000c04100035500b40000d003005411806504030398914454001e01700e032809810046805041d4074039000c0c07a86d008460b550405240c49940d0f60b6070301d50030704082c0107050540c0010000ba0340b400c001801082f0108041040310113 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 132693956 1250 132692706 132692723
    0x20604050d0305041706240d1403220305150a06030f0c030201110c03060a09140109051501090209060301050f0607021002060619081b0a08010e0c0f09090a02040b0d020d050a 76
    0x28902a143c1e40121400c10b0881041203d6189200d186d0387c20307850606c00038066070081c400030f0700c9403050103540040162a65000144000c1c440859665501e86001e11101c0840d0a80c11035650b030340c60702c885006403241c1515210224000d022030340e0102d03008507482a488500580541390071340c0810140e11003680032629604100d1150304000c1000042e011006004e003255540f55900c80006120181056512501c500b0b4985400d440901c100c00303c0c64020001403130460703106494904410707016041003541a0041c000c606040d1903250680f81900c01c01c6600e40140107107031010a44901908030040e502080841054124075004280711740200350aa41400d43c80524400c140c18001c8130b40f044044540c00b42e00854145085421031140c04032009145032038041e0788076001802d41d4411084660b141d000340c0c900846910b00300495400d401000c0d80c03000110328211400640700c030340380000640078a4444c03021900716582c5119201e1040d03402083d10003c0c00701e03402d1803907842c10821012030b18040c = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 132695206 1250 132693956 132693989
    0x6040b1819060c1b080a11100b030c010f02070603021c0903080919050c040506010513030308010510080708060409031101020a050702090105040615050c0a0212061902030907060309020604050d030504 87
    0x34480c074101e134482c210484080fa8043d1695840000d20340c4201034010400250b6044603215200134015421400303820344000c100140c0080405050a4604030303164140f202c1902d0901e411600880d0760720440701281401621074541101000041800c480380c181214641102c2908141d04241481c0c064005c40c01290000c1c640d459481c100050500d401500d10b50000e03805000c41e140c180c0200c0c3e88040185405824000b128003070345a00d402c40d410131070104080741c0c018000c6060400080702c45204038903048040d4102294007804000001d45024003441e100c01181701418000c480c00b4000c24a050021550360114a40041054000c0c010407403190f1341d04000040c103480c05005c0c0c58140c4811101400400b440c0303a5041c0d503581d100b14036813905070040501b03c5001d641c2e8003005400120f501030140c081c91819402500d070b03540c000d611051205105205001501c580000c81e0429155a03007000165601c26000051003401217030b001030390159424804070101940710b0003420883c1c0e50b4006800155 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 132696456 1250 132695206 132695231
    0xe07090509010503030f030c070c08060a1a01120e07030803090c0301051b1207031413140105010324020c060a1b080105100e060d05040501051f0806040b181906 70
    0x41c0801e2146950551090026800d000940002150004046d0001610b004540d5a484c00001200e074803469080d000300f4200004a50613000d40c030001c9281d5510210710000c0d100000c1c2001d501c0082a1840030fa441840700e9102e4401c000c146c018641050485031640703042c1000640e900003001c0554002d50900d000305050f03240c0707003240d80c8a90758000340e05800d11005c004042d000d0f5500900d81e508140c0c48501d001d81a0b590040031a00641114520a0316a05a0300741200300c120380500030f0070380e40e26200041010413044800500b1000001c400108801112aa0701c0068041d00c1c400904a004050074080820356a82c00900c100f07400002000c0c0c0e5001c0c0d8542510341d00d0342441504c0c0c02500e144d84101e03030300740b1852044e0b402041c001c0c081e1f42421b44111005007114001c603402c840a82d55081482500d54000c4004083c80307410b800d210341303498100080030351550805000104155001001301d00e4024000020b0f1580201d003000303c921b4840212440c0115003079080d81516054500362110198 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 132697706 1250 132696456 132696469
    0x7090c020a05030417071e03060b010e030606060d0b090f07020607022406010306090c02060f01050418110a030506070207052d010c0302010f06060302210103051203070c0c0e070905 79
    0x72542c00c500514202071034981251103440010240c1d00960148070004601c17110b41403001c00ca11000701c00750540180c00e40ca0204116041d2105684c1400b11080320007617141e030009403a5521030010748615880d48a005646c502408607010b505620242c5001000804401c40c5685807040d441075081b6001030700c0b40e1750281c1c0c8407071020400f04410010b842084c18400b4145c103400d50006410b24000032407665904556080700c204141c0e02d801a00301a090048042d641d01405000d000211740400c210f0780001c01241d804440140d00500c1a4002040c903640c5594005410300150b801c507064510a18240c0c20080d00c40d0264000d043c0300c0c3c0030380821601d21080018401c020300300203441501514201c8001510050190403041782103640b80c0a1f40034014100d0b004403001054503860258170343c5901d0a015140150305182d03080c101e12140f0041021401c00940e100c9075100c0111020b076a9140d06000302e509080308407000d813000d03048120006680c40e68080a510a54403540c40e000000c0e2542c080042 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 132698956 1250 132697706 132697723
    0x10c0c020607110114040305100c02010c21090804060215090a24060810020d0b0301090201090e150303030403110606220e0f0a06060314010c0918021b07090c02 70
    0x4100c0710600030440021449002c05548050504044581521414800380d140c2d0194204607000d4100c0445403801e40460700032003203802242e000a121030814988000d1030316803100301b084042c0807500640c41d60380a080d4040703019140c000407070940e07441c2c40d640040d5640200c60b101030100303d03041000900e040400302c0d0080003a548055001203e840c00380a181211000c6a004d10f1416650315001030f106008122003449000f1249001d41c44d038401800708411149024800da001e41d0500d0301060050b03911244d03020585004441c0301e1910f883c0d08407403042e01400088820341601c00001480145500180951101440704044038a180c0e80c01040c0000500c000c003d02c0c2c614403104080c16003000b541d41000c504c60380e8040407520350b003104100b828902641400e058815940d1020140103000340e0603003003c415544c1c00d00901078200600f1004050b084a032050455a90207890403212890b01030b0102d840d4640d4094a00c030340e1103040702c080c81c4c030b440c0c0c144034064a09182908002c0340d01d00110f01c025 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 132700206 1250 132698956 132698959
    0x4090c0810152607030e070911031b0408060103050102040906120c05090c07060615021c0509040902010507061e1d060a0213030803070801030c0501050c0a02010e0301110c060405010c0c02 82
    0x280088808800d4458110f40d0415803040003c82d04030881044150006074465002a81e02043e001c1e1000710840c1003c219070010381d0100c0c02c020b102c8075030382c003030104507a08455045112101244a400f0034682401039400101090003140000003e00c0815000303081a214043d00c1042680e544642030744126400480c02445c117103140900b004245000700c4183c3d400f9540d45801481c10402e945c4410480b0325607000b02005e011210640d550703050741002190050444882c401e107820440c0c55024205000d1488020701c2945c44210080031644074000340e450351a0700c00310a1003464518415100c13182c0d4854011404a45041420140411403044c022049800c141c050209a2614800c002c0130350b000c075081058950140700c0001c001015074004502c00d012a031b440d031130b02d9410b40c9880c0340f40b090181e00550403c4070a00c02010702000c08194400300c55424240700e8800844e1802090145c50300c101d4005801038080340d01c40c145580407505034030503481000204000f010449042d200381c003413214040e = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 132701456 1250 132700206 132700229
    0xa0207050a1409041509030804050c0d0b0f0618012402011b0c05070e0408070b010602010c05030117120a03150911030402060304030201140408070209071103270604090c0810 76
    0x802c0341d0a02d107640c140c0260041c80c004940c20507921282d4252101050201d00044007a41000113101c0d0600c44ca0346420030883d1145259151074940d0021004040c040000c0a400d900104038142d5030340c2d0301d035041c2c1b0503102c207555032540e91098880c400314000d010040c0c0c14044a03043c00d00c03403441031050009142c9141000e140c042000c140803154851b1904040707849105001c000300300c0812507030b520762107584141401569aa0359140107608042c1c180c0c002d6055a0401140010503900300b800d49040d0f0742c8440e030181d00039180c922140c0c40c100441c0301070414402c2c0015022040c66041e081200c41540385803404030060b42d07a0108070200d400718820300c02c0200e01071022900510380b041c000c0d41c02c14020320000c80c40d08101540d0b0803441c0e038203840c00c4400001c001000800c5081c90665545e10070300c5400c1003c0b0032a52130796120307201e2054007154104160440c102d40c006400b041e0b8004c0c00004050415074a032a2103682500c010445840082c011840410029901c00010f00b02041980d0952141 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 132702706 1250 132701456 132701489
    0x60d03020304150207171f09120c080702091801150b04060e150d050a0b0f300616030605100203040303050304230a020a060e010e0f240a0207050a 64
    0x10603164800500f00c000460281001c0041c016041d410100d8010705180301805000001100100020709101004074480341464024404107081410b030075007160b61818030307140e11541c40c5843c602e54800c10400a52007148102482500010010001003810b401b1000b0402c54003642d800c441111018403e80d45103110401c4107002641c860b091040c0c03103d01c083c20070000c7c810601556245034200b81c815410082da1a001c01034080703001c0c0113103d0322420959125800200c8000801e18000f219600b04000440c100030f078000c1d800089400c0da020340e0301982580d5442c1094448040030411f8091402c1c002400c1010201c1e80d03190800170039006001036001145040e20310355007507400381c1000f4000e86049a03882d04200035814421400781e0a403140001400b50851948100000d104542d008141040704581c0d0240c521398020b040b030313411b0394130461703401d24541510760010340c81c06d011040103c50512060b408807090003d00029210105540e002e40e044683c480c000d0118070036503441038240f000c222650 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 132703956 1250 132702706 132702719
    0x60f0b0a02010615020f0709020315090603120a03050f091f05100b070303020a0f080601050f0c120708070c1a180103060b1914040f0b0d1401120308060d03020304 71
    0x18003009180340004600c45640e41e1492640028003050301003da00019984480d100d8180082e001a20b0b00e04000c60071810b0019079807500054080d90b2744d01078110000400c130b0741e5600304180e68501d82080d4695903500031000000b00138120a4400c1080c40c011080030912546020950a80070007503107440101e908041302802d0040e0801030511005c0c620101c1000c40c00e144020001e15015009403030140c2d4a51180324010314080025949a040080440070f220a580c0c1c8042110b00e0904103008854603003a01c00c0d800390404810304d109219070a40020003004200040c00a007007a01c2c011921894440d90b1a03200c0050041034440071030b041401004034003150900603c07a21610f00061500081e030759110303149850b56500807200181d024280c1e1007100c140355030001a4100040c0390300b40040c01c0c20301d00001c2c5040004d07071340108a0081804503a02415541c07692210140c49520070348a9060750b503d8030140d290600c400c03003e400083c4a040040c0c50f908003003d203001041d0741580110700c2c1a00c0c00d80c = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 132705206 1250 132703956 132703979
    0x20108160309020409080301030218010f05190506040603060f0902360306040b18010e0a0825060203010311030c0f040c020f0f062226090909010605030d03060f 70
    0x205540a2550711030302c50340943c0ba40d101c0c2458007446a2041a642c1d4110b0040043c900d000d80c1200c285801d81c10014440003c0d81c68040c4100c1e6015101600203842040113220189880e801c03058000002160000740c056158101e41c045505900c2c0d50600c02e034640755210241d20800450038150903441103e00c06041e00d520081d8003020800c1c8601542071a0440001e090000644040d600044003100b40300283c00c24203841816164050000c000440383e80d00c01540710344400300080d200d06008513100c495000a002c898401d003280c0d4021010f071078281e140000094000380020380e841904941c0d804914100014800001d800082580680000920800000d40b4038000203c0442c090304c3c5440903223480811440040101020141a107460010001000f051052800c9014034200f030001a01081c030703840b000501c00d1025500d8081e0001d6040b640c002c40c0c41840c25540c1c2140708041042a4030b0011b501030f1060302c104a003a54052030204900300c0c241d6525010b00384808407440703001c102160006 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 132706456 1250 132705206 132705241
    0x6170a080d09150c03050a15090903090b030c04080105010e01030b04060c110f150f0f0a050604150314061506040504050912190806221a030118061107020108 69
    0x24400302c2c6000050342d81082c00d00b0003625544030741c1e4803161000100e540501a0382c0d4000c40544040100440c5407500181030103079481400d841c140c2d29001d110a00d8812101c44002e0903c5881040d40d0b41041d180c440159446403249021a518200020801c40c21103806a4100d80d04112415010740300c83c2c850300010503082c00c100e0107111907034400018814050041c1d6071130713141a0001d032802c06190260070901035401444521508944410007550721480e84015400c9503444100040d0f9035100c0010800800702800754404504888000004000c0e460a03815210b19480b02500c85540361188100d44001c004507455504c030400780804c1c026070400f50f020550104c844801c59010500c03544140d4410b900c14041603110400a14000e04241d81003410301e90054000c1c3d810078280b00104040a5406040410442801d0f4480c03400c1c3c0700380a40c0100340403602c0030050080080c03441c40a119440c007910b116040314414100756803d6011980c000c292060301d80c068503105202d0355202c0e5400d90b103c816 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 132707706 1250 132706456 132706477
    0x905070903030f030605040c030b031912050310050a03060219110d05090301060e040f03090b0f0409091a0a150f0828050a0f0201080a09030c1103030c15060406170a08 73
    0x705c0d40c0011341561240030b40c4a401c88161000929806800207140c10101110851080035014a4104000030714810300d04405401d107190040d140d0316010050008900a54040d60740008082d2010050190703950040a861a0792184040c5a4440c1032050300c50b0301020490b48030741d8100d82d04c846c49281c0504000c011b854002000080c80341d46038180400300c0b28058809440c2c0c003900f1030040c4101600681000c000d4040191581c1c10300742460380300d680c03520890107034100c03464490b0185000c120701c1071402d00704114401c03951905403401a04060090a03412038842401c00c02004c00940000d102031942c0665800c8400303014005400c0c00120400f81d42c0411110114608005a10101c0d40031320191101c20321403a09400302ca003041c0001011903002402c600b40c01c84c031b42401c54002940041450200540c018074032a900310075000040d085000340c0b11350581e00d00401292400c8030b0078400ea1244108e104490420a681e100c044c40703000082d02c020040119071021042e100460310312409810044403 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 132708956 1250 132707706 132707711
    0x2010305180102040b190504030b0121020414100f05060706020310030f08040602160806070827011d01050108121e0705030306120f0a080d060e100f0905070903030f03 73
    0x5024201d1802c981c8030b640903042900e0007040d00390710700200e2030309400460700514040c0e0401c1e0960703d81044050061203201240100c0c4551054400040c00c645100c4c3ca80080c000c00204940542c024034500d41140c120100c2c00607000081060543c0d11502800c2da04007502c001c1c2850360b140d6414000350300103440c500000080c8140040000e450300380ca108050310446580b80c80c0c2e458054043c3c40c010a01d011214a51840c0006000d00800007500951008043c40c00242d5501d03501c1c0f8203401c1041d030440150b0030203078100d100d0500150541000c0051001c0c8401d5a4101580689007802c80d1340030301600c0025001200c1c5000410000d034042c2c45141d010640c2c1034520034400c190140a035101420841e03903504003104100440c82d05601780d011104143e80901000f0030502411500c80030544401010b02c0404210031002040c1c80d40302102030650703520000c0031400e1003000054030050b60700c80e01c040303486444004640b0401038000c0b1809039001d915501d84103400c42d1f034203480000c0400440010541e = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 132710206 1250 132708956 132708991
    0x8070c08210903040f0f0501051c110c07060801050301020306011e140703031b030605030d052506240e0708060103020705060708090c041112061306061701090903020a02010305 77
    0x102001030a0140032030100031030703031036117050701540c0a110303140d000000d0040070750300400c0641d82001c00c442c1c44184820710040240700416281e00140035000c01c0707401148011821b08a44007000541d00d06460b140d403103940643c0ea0740c80426090340b0085036110f00082281400001002c911221006906c50714205089146156240001c260f045070303d0070382c0000c0e210002540e0340e0803090429031071180d00f80780c1441410305040120380e41b07c1c1e2420b105001c00c2b8000444100413045181301c01e102d100d80800d680c2c401c62007810100007a00ba048041c80314002d60781c400c0c80c90b00c2402c0d803086040301c001c1d180c400c00742d076501c0704183d80d0408014141d6043c95002c2000000190042c0080c1c0d03c51082d544940d0101c2c1040803c80d480c103410301070003a004030318003401c06402c10814410b80308007549445e9202c3c00340c0c3d03c1030f01003105040403505440465041c10b0b8003052560b00107400c10346800520b4506412683c2c3c03400e180c0c0c181c400503580038003d41c106500c503074090751082d00300c20ba00c42c0f0300c0d00c410480d00 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 132711456 1250 132710206 132710257
    0x20c030409090503030f0f0402030a080d06050402070b100509090a02040c0c0501020c010e0d05072109080304030b07080a0908030402040504260301090c0201060f090c0e060307050705070608070c08 86
    0x8404400c003ca843c1e820000401c01081c40308a03d440d00301e1010100340d00286071950103c0c1c0e6881d240080a007900401180c078820500c99504a00c0103071001030700030b40d181d00e02031404012101040c0c0310f07400d003100c4054021441d4104080b11520501d885801000c086200760240002007440078201c504000708009010080f401c24001001c030810700d0300c000100c103148842054244035003100702d141003100810019000c00c074845041c201003020350b02d1483e044c040780705066620300e003182e02a110314040401c0000601c104845001d03c0b80c1055103e2843c1c0740c2d9080481011100741e204c00400c0038600380041070250400d940003907481481402030450483c0192000403030035010400f02c0301c0d0000008010b000c9591701d401440f8401540340001d211250070807140c806140300c140180b46140d9031f502d0701110003610501101c2072081020b0f0449603a0b040c8041c0c000e1580e13102010540302c80c4141c2000003a414451000075100700c81a90390126a9103d55070b50a02941c0000f620210103040b80f003c03660207 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 132712706 1250 132711456 132711461
    0xc0b0c070309150201151401090b0309072c040c0e090a0c0b0d0b090903040302040e060609161412150901060504050f030a0c0b0c0d080c04050909031306020c1e0f04020c030409 77
    0x508000050180040382947c0018818126504500d484190034030510101c03000001e04542030392920145410b1001040b410703008404106035601c42000b00c20010702c400d0001100050f416600300d210080250750f81c0000460b580c01c03122600421040d2141d90401580e12404040c007864000d031030340811140f1000c0000f0b105504180e0308501c56410001d0108110b00d014424602c0f4401c60201070405d624202000900b104402800040755042d0b09091140b0188155021807407401c8168003c0e484121743e5010b259035800c00c0350400d0019560588050742d03850312903c40790480f01c040d642e02c0e2400c0e0400007845074414801ca142d035058400c41904030b0005800c990711a001d00a48070b021038440d111144210700e80208a4181418800424280a2a4051081114195813090b541039841d0303100c408025240d446100001504c0d1a03141ca00452202e07400b01d4000182c7c801101c25220307001903080b040c2c1c1010300d040391056000008100803c22414503401034861401e040301600d007031030307940c684110a = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 132713956 1250 132712706 132712709
    0x30f0711010b03070f0906061e0f2001090b0c03090c130e06010e0a1113090504020f180709060e0904150605130e060f010b031f0f060c0b0c07030915020115 68
    0x850203003d1340c06001040d81c6d446000000c246c207141c1081c15000030742002d0024001e440e00714003008074040c4442086030003200c4100c4a452820900c004001d008100705001341119102200c0000022002c542412031131310680e402141110003804540c4403600c101304440400d1002c50101d552600c2c40804045c209120807402800b501d11459000e203800401c0c03900f00e805000101125450034070010440c0078020360800309440c501c640c0001d0907211400001c517440d030301100c01540003c0c003007403480001c07003102001c50141840d6103c3c100350688415081d22a090400815034102c204d04000174003107040030761061264158060700080042c0c581010850400b9140144001c09844281114980b0310810a00360f100b001101201003550600175507089a01c400b50140340b2580c6c45000048000a8a81109005110107070326140a6a900d02014002c0c0c1312044050310013900200020701e15076040b00c01c54287c01d5140d650030b19054100000c21400040f402000310443d03507100b110030031000680c100c010 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 132715206 1250 132713956 132713969
    0x50402031c02010515041b08060d060f0c0f0306061409060c01110712030b0d02060919080f1606080c07050705030106061106090c060f0f09151e030f0711010b0307 71
    0x950340c82e1a00a0131703000e001421943d4062890301020f400000380d101040f5148480302d244c907445940316100015203a03124103c2c0a8455032030402480c442488652100e003640a103a1a4459515110f5100f80d08031005031040e02c0100d00a000030b400307000a070400500000c10002c000d5030031302d04884e0b41942154000348040513a00000200101400080c031284d00c03400d14140303024080c00d807417100401e500080781c41d0000e0103000c0116840840303a54035a07100c11481c0c0b012100150055580c00d007180d58100001407008103000d0080507007240d030149001c0d141a00e0294803004090344901c16141120b134460f55041d281c13806902c01c04581d558081c0034202c010301003a0394021815003034240c02030074035501404114041e88007132001002a02c4030b00a0f03a000c3d4100c0b07a80540c8400e490300081c042c0d445040c0000c0d40c4180048602000400f5003405000b090980103800c3c1d000e400038180b10b82e0584419070310313560b4240c0200001282240f0601d0303044481766124001241480c12007022030304c1c1c00141d4000c0c5 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 132716456 1250 132715206 132715211
    0x91407080a14011506080a140f010f090504020303070f0203071d0402040608030307080403050c0a020a030602030f0f010b271008042a0306020703050403022d12030a03050402031c0201 80
    0x81042c80003480350103000584150080040036138461141504503503034894801802008000110701110030760055050020006c0c000500c2d18108140d000216424010904140e00705000801c0004007840740c0f034401e5a001d00110300d0207640f61145501b44d100c00c1c40480e454400d81901060203e02c0060030a40401402a04482800d1902c100010380c0c916400c049219841441000a590750140c01d10380c1081c0c0505040d03030307a0b0001c000d40ca4107142d880703c1d003c0d4000c07148035000030401680b03034000c0d48070755101c14440040352a011061462244288a5012405024004140200110406582a40c06404030f1078440004c02020451811841c040080442c50000812061080b40c00e0b0f0040d00c112506002d02c80920340c00304041850905000140009601041036400c250180e800c440103190000d000d000c40645c289140804520308121245500c4200c0c00b10011605181d4120022601c100b4051401c1c2032800750100d005080c007d005903854416a180d113451056005502c0c51814400e5001 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 132717706 1250 132716456 132716473
    0x1c020d0501050108011b1e0212040e01080d0201090510020315040603050606180105060403060906020c06090715020307080405090a090b090703030206010b07051c0c0804060509240d09140708 83
    0xb098215a90300e42440c0e040c0442003807a1242c00d42c0040040c0045a18510111f00000c06c0d101c120705e8816064140d001c0040c0000300440d86005108a140c103d402c0c03002150680500c00710124240c42c2114002082940f26210940205225802469101c1065104205048501d200140aa030350f030741d0043e41c0c25003102c01440801c0c100700a5032042058250075158965140001092142c403072440080d180954070000b10080000c01e804541c407103041c1c41e017220b07800d0506003c02c9894000c0d510079404101c03039041204c02d40c64008405d8980d00d0382c0001c00c20713040c03500e01000d214202d440140300b140500d41c0c40e03019100103244040c6680c028a40300c001072401c14150325011b8a460b8060300f00044612042c01080c0010b000002d0b10702422000780c0030011841055030b0280c13814442543c0052016102040100320145c0c800b0103000c05500c1160240090056140d40c0084105a04100100104c007000071050001c40303900072080701c9108888510914901d080d03031604201c81d80d005104c03150000380c02c = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 132718956 1250 132717706 132717719
    0x50304031b032105090c06090d060507050318010605060414011b080306030f0f0d0f110601090f05010909050d0e0105130305010204050405090d0503060d020f0301050a05070305010909111c020d05010501 88
    0x341c04100c1082a0b07000c04c0142464406240e4816621680c80d01c14600011691080c2d1200103d00c41111b034041000e0000d814100c2000c0d10390780080799103903954016424442a000014090312080f1000900b4a070710381400e00c160440130740341c0c6041c0d1078140700b54130310441b10580301c080c00000504d0041d65030302d46a00700f4004150926100c444001c40592042c40454400d483c041044801003c00381413407804400c80d0358050340d07560014081900c0310b001c1e50000043d0300c1350035000402c0740020b4650420150383c96204e03000455041c0e883c00303085070340706035a4041002d00807006040c00c1d0a05051480c204100301e45400d0101c240381d0411103459401040c104200d0070140281600404e0300310203004c030003114900060107030000a0004e81305e24010700041d400e41d143c80c810158032180113802070029252600528024250541d0a58002442c000000403004101e110700c4880d81c1d031208100c205020290100074001c0700100100c248030000000d0080180d56070600700400b0307441100003096540c503182c3c = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 132720206 1250 132718956 132718997
    0x9060408032209060501120509190302010504020310050c030414120f180405010302150f0f0a020a050c010807021f020c0d0c0302071a04030209070e0a0603060f0902040b030601050304031b03 83
    0x140404101410604188046c1c0c1e08840340c403400014903000028141d59103241586019021718500000d1014100e4010034103a040d00024030443c02075048940072303d058805032040343c2044824841030001030002c5000581e007104189010590002180e04a62030300005015650151110110300500052040c6039400c0c0125501000c1104407810003640d80340d074000c10108001d034615801010310000e0420b0050b02d214050b29180080b81302c0c41500c0d8102e100703019546a8140f80d0a65040c89100f89040840d88101c0c0c1c00e6206141c81d48c080c00c500c2c9003103003c4080f5118014030300703e0007540034000e081803940100203003d40031543c2d6940031100091828007034104040c5030001190215040164405c0501c0302d8100d0741100e9056a200c0d00680e10218221002d6440d0000294401580e00000417500c0c0e2580206040c0c0b1000460110a140d5030140e0004911a40c800e00c00101c0302800020003941c0650042c562142c001e00741145c107202d06441e60201c550380120110041040b40f080600c15020b0751 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 132721456 1250 132720206 132720209
    0x15040515040e0f03031603020c0d050c010b0a060509040905010b060a0507140606010e220905011514090417120c130503010b0d1506050306041104140417090604080322 73
    0x1805820716103d040c120300c0d2240b000820580d404031406200007515407003981118080d6600009039851640b041c50000d00d6503110403201c900b1503090603030365000c5181c4041c0c03000c219000c90301c680f1320b0034405409100c00743ca07909505035002d55850040d00d803a925030400074040c0c3c070a284e4aa070398961840c904241031200090780c04d03c483e4080700070014140d81100c0000e5407070100311800041860361210b140b1120407446500c0b03100e45d00340242e81c0204501500802007013003001400d078000380d45402c00340d100b0322144440168481d40350b0000c00d01155401c0303510090301d801c60a06134607110143d4500550a8416101e0340304440001550000381901c5c2600304010b020218001d0000e00100f00001d0341d5898100009041d0342e10050040040019070307072210b001003038007070107840d5640b0702800c10b00c1210051008503030285090407000300c080c0c450805940d205a44c04155002200407a4107031209a41002c89041d4100e403040101180040040008e0705005256400c0400010802480122012143d = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 132722706 1250 132721456 132721481
    0x604141216110409030f020c0303070c120606030f0c0305010606090501020607030e0f0d0206060901050f030a14030913052e0b03060d060e10050906100e1504051504 72
    0xc00385031218840c00d00100c03007103800701d02403258085045060040070b020b200b1409039406403401c0c019104050708101c0e1001c2070310042d020744802503450014140c880c41408001031990f1046203042c880c04d551112000304850203003000144540e129500c3d820070304102c900c1a02c00b40f500307403001c00c2000400d0290030007422040c903101e0285450880043d43d1420084c1c40301c024940c8810003010112800c11245001c5210001101c50013841c80d030020b07403114000d0382c0840c0078000f041c0001c1a13038103045400c0d2003800d9002c0c0003050140c006898407035030581520801000b50204100d60303031044e5515022295000354404000801e41401d0b0012609503c03107001d00912500c03a0940100c0c801c1000d0f071080304a48a414840343e803603444d03000081d43c2180b1898010202450420071000c207910000d10010070a10000042001d40c0f1100780950380d03050100c0703c480e03040358104000c5c440d81d401e480003940c000c44000206900c00e01114000b8003519011600084050303028503280c5c41d03600d070500541c00320710007 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 132723956 1250 132722706 132722713
    0x110705060603030708030c07050c090703143d050d060b180708071103090603011d0c0702032a030703050d200c0616050d1d0402030f0703111308060414 66
    0x3c030341e171855110f004c01003414560020104140042c0f2805212403040840c000b00360072241e1a200202070002d280c4401d80e4050408813500003065120a003c024401c0c44100a50031110b65001109602d03141e0a080c0d4000c0c8500c9001000640b45c84a216143c0c50038425000403c1c80b400c000140031a40c2040c107499182429402d09210605801c010b40d26085500e41c60035940130000c1c0e5114925612035000400c2d0400341c0000001405555040541c070100c0c0460f200000b07688400290003040e015000d40a5417640011102c1c500741468041d01c0d1340035080d5030740c00d2102c921000000030309005265006540580141c0e11608800303034490780e00c40561144805001f400ca140e60b003410740e10100707991894050744d00080c500c448030014805041c0ca9640c04011100713541000d2100501e50f11800c0c140103007200c0001c04000442c60f00d4002c2d60b01c600c0000058100c15603030002e04501030803503070130300c48620b01d02000455500548046401c2c09420003000411341402c0034a0704510380400c540b41c0100b55003 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 132725206 1250 132723956 132723967
    0x150e09090624011418030c060a050414040f020d06062003030105040c020309030303010f050114030405100903030608030d050402090108010603080703050a1806180f05030a0f08070611070506060303 86
    0x981d10802c0400c24602c5818081c685104100181c420003a52914040076070004906030400c1c0444002004010354103400b80c80e4007029003c240001e42c00f80440311400f0413814042404038051070884c2e54083c440080000c40c03400241d400f03140032a80042990400d00d0f0316110144480d50b0800c1003001b01135141d10b003004946103110f050365268001070103240c0c480c0740c86070100300b102482001a501c890308004c0540307613079507501e040b807109001c1c6521549000c1031464540ea00c5d000f1444d400d50380310303d400c0310141407002594041d103401000100c40072014541c1d50940031510b41d101300301402810030011070000702400c040c010403a000300141e1003508140e04101080c4006020701d81580c5103558142031241e1504011041500c805903207100304180200e01c401e00080700c03540005075692029095020004041c0c83d090011001c6242d4040c564040d4048490f00d8005201d07451803600c21805480a1410001e007959001c007566060002040031200200e1440c00303000c03060141540120b8110002c51501e03 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 132726456 1250 132725206 132725221
    0x160306022101120b0613021306030c0302031015180602250b040303120b0907120c0e0a06051b01050106030203010f0608070e01080c0c0a0501020c010b0a0f05060a09150e090906 77
    0x300f054a00c0284100c841d03401084807501d500301442c074503240716902503455086e400c10f01c0001003001e1143c280040d09003480b12102e14040c1c07088a0003004040f10040308a410440382c00d80454088111170208010381c841581d0507200c1d40300040c003900c6158080e00d18400150014405061010411011030790382c150304100c01c03001401128100c0354581400c00301c2c078000740444801000710740e50705500301d039610302002501540011400820b26400744100000e0302c00e40e008a43d8011440748841d001442c0c003400703005082c02040a041e011006145174070700c003c01b084c03100d401e6400170b92111001c0b0ba0044014884a00522801d03800741125291a5201e07180450f001072038200c0806496060014003800300e130b204910001259403c44500040320810313105490180e0007540300020003c8035529110458070140390014801c81107404815030254107904090800402d46d108402c3c9a06209803240001141500c11440c181522a030b901c64440380a001d500707100c004580100300c01182d0308010200300c01c5 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 132727706 1250 132726456 132726479
    0x503030a030c120f050109141003031d190806090607050d05040204090807051f020906040306051503061303140301080a110a1d060f180f0405160306022101 68
    0x1558a501c0e0200e681c144110b401c0e00e204002d008021442400d20024105030340c401d0b00494103da4440200300704e140c00001030900c4800741640c00c14544000810104003013446003601008007000000080c4882c0341000001d0440d0300803c165880180c1d51200402c0598018011181c1c03260190024102d9032030b0200d0300801d5440b07a60070901101d07540310302103010741d1120b43c8806110356000c6a407070b42c4d403c12030400f60317605c0700d40030384503a0002c02e40b00303813a903091007036009564540c000508000d050605541e212405020001c1488200646c982c201c3c00086c2e80070020b031802100c1544840d07098060605008000c5170812044d00390001e410070041140103400100440101d0b04000901c41c0c225843c40081c010701400d238070440d5080d0242007141040d200c0c02c480079005010484116420030022400d01c910b1151203c0c03060441c1c921100021041d00281c00b002c1c3d88a1700c1642a1824a41c2c0b1001d003502540d000c2c1c006880060703000c0b80c806030044020000312a51502805519115031418990000 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 132728956 1250 132727706 132727717
    0x40b011a030a05040c0e04030509031209030d120f020304080304120302040e040f06110f04061b02090106080a060e0705030a05070206040210110304090908070201080f010609151707080a15050303 85
    0xb6034640e1100040c0902c140900e424010300384512103003400d41040d04000740039810001000d84280924101c4007100084082114170008000e030240c03407a1003002d202602c0d00e080c050050303040b02d41c403418007000c05052440110b00c07030340c42000b0090322400d141c109000c903c0d04030032188051600c100b00038480254204130107a4010f6001c60111400446481d043e0086d200c00110b0008a00001c90800380400d1504041d00c259100381da103d000d2100c1422065220031850f010280d00040d651006210141c403a5005690003125200c021444a907141c0454a0803407080340d1030800201d0110a00001c10b440d03000b1681c00038034a200400f1542410b4001444a0100c50300520a202410b03100160307010003070042d54010402e9030420000014641003104003030b03001d048100d0015003100000360040010002c0c41d410b0740c3c800e581d4103040d642401d1040d21074824415015003849941182c2d0320b201d1181c0d840c4540b00d02816aa02515400e00e04d0380384090304e00540c00b02da07101042d0003050020780c03000411b1702c0 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 132730206 1250 132728956 132728971
    0x4030b130807060518160320010207080307030903030801270213090905070303020f031c02131211190311040510080d0302070506010603090809010e040221040b011a03 73
    0x80300008515080d803551003914801010a0309160400002052050244a003d0000404c1d03424404110403c0503521809000007490720349880509015007408000d50101c507401801100c0c0400d0b185e40d2254615080300b842203000403c03450081c801c041e80110980c1c014511400c03101c3c42c3e05038084a04192400b40c2e0341ca03c050b0b07a0301040209502c609500003200900e26510100044501810032644542c0d007400107038003500c15001e14240c1c0c22000000c8507600c0c0e00c18880c10310100b02c411a144041c0d40410f0a1421032110288049007862000c81031060041c814400503098a0302c0006208003002c0200f42d10311600010807003000895000da842c80c44941c030849001031179586003481d82844007035542020780c2500c944e01190880c160142d0080c80710b54001c01c111401a0f80c0c605045054070400310780200780c40c0c000d000c8180207500413161955441001403000d41030034801e0301d0b1440c5c2c10f4442d10301c86010185000601040c8046054280d025200100311030403c100001e05800d4030703100c00380c03400 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 132731456 1250 132730206 132730231
    0x201020a06090602090a090f050601020f06040b100b0d1b030e030f0306030f121804061206020309070b1611040207030903080a14070b06030105070f09060e06090d03090608070504030b 80
    0x2d07081207020350468a2103000240382d02082a250306580000700603002c56034100c035150101007070040d8000203141c2107080c0850010441ca0780ca5943d80008880c001d02034070305548400754003007110030b404000350400100c01070300099068506c440f240b070307602800301d000d90034113140950820340c80c0e10100494110110562603d51b983d01c411010a151070076142805005002d03030843d070b0b01022141c1e40100810450aa00030b00035a0b0810704100031500140b02c1d04d904003c0d40f0103100e00042107500910790080c2580e082d65500355a5010030380c0c455002e100c120f41912900e0b5401c0040010b023242c80e07070506800369021400e004060f5009811650503010140c075040300844d488074160312510301c1c00c0f400d002030340e60300f907c40b03090b440c0804410308c05030f074214421b500f0710700081d42441c03103000081ca40c52013a9840130659403401c40155040604080c0454218204105048198a0b03501e4007008076403081e900d031081c0c0c0d454010024030703200014011204001c400c02040010402043d2550781040980660 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 132732706 1250 132731456 132731471
    0x3080414010c0605010603020306090c030c0a0f050c1605010929161203360b0a060b0f0c07060903081207031d0c0306070302070f11010207030b01032406030201020a06 73
    0x140d500c0c542d9104028052401d00d400401c516901d42c010b0760145030241c030440c21689a040b40c800090008503403002c05241d0070301001c1b41e403a01c2220024400c0c0203034101503142c0070001c40943d0601c0031000d060034400c82403217010442c13941d000e148480280080740007980e03102505031036418182150b86080e80c40300400b0035030300041d103001c0b0100300079503030b104d99400580741c01c034140034019040341220401041c00c0900301f80110741c40760000b55015079494410010742c07941b966407402002d40c0600580359060765080040744590803440204410238030031089985645a2400700703460501c03a0b0b0008410080d030720b141000017a183c202900c0d4001241100d01400b0750303030803004400030712880e52100c803d1440c5a00310401e4070000700320494112000e400b074aa4a90719401c00b07805078840d88800a0000140e00e0801e400310303415820400c1c04400c14410b0340c614603565190000c40d6403003030300181c640301e084030200442400000d00051000419400600c10740e80380d500081e449448240004d4180381c1c82d0801c = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 132733812 1106 132732706 132732709
    0x2070e0405060601120f020703020a0b0a06030f0807030e1e03011b05090f0f0d080c0c0906010c110a0504060902120c0c060c1c0c0c050c04050103080414 67
    0x18920b684445004461209a40c030b14000000d69842500903c81d82e84d00080090900944c001c06042800d401c0842175100301801d0030b0503a603d4400204002a51030f244000316640140034651a034000d07040546118500320042c50340204032130360b4802d2100001600b0022800242d00800c14601e220030084409003a50501c00b000c00c81c00e000688491601c400d50940000740500b040d0000032a100105043e4881100201c0f4041004141a00514002c20061442020481c0c07003d50b2418004000f038112405401d01402401c100c00d418181078a80c06081d01c01440060810403070740d40d0310410080250040304044803600781c2400840c3d442240c1800b6603802000c410701400d46521503092804056000981e41d03030000c0304004506d0300303484683c490380341401c906403592041103071149015030500340886102d62040c0d15060040c80452124810345041c0c4030114941061040941d0 = true := by decide +kernel

theorem cover : BRFrame.Cov 132553956 132733812 := by
  have h0 := BRFrame.cov_init 132553956
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132553956 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132553956 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132553956 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132553956 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132553956 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132553956 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132553956 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132553956 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132553956 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132553956 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132553956 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132553956 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132553956 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132553956 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132553956 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132553956 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132553956 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132553956 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132553956 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132553956 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132553956 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132553956 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132553956 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132553956 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132553956 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132553956 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132553956 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132553956 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132553956 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132553956 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132553956 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132553956 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132553956 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132553956 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132553956 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132553956 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132553956 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132553956 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132553956 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132553956 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132553956 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132553956 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132553956 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132553956 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132553956 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132553956 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132553956 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132553956 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132553956 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132553956 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132553956 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132553956 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132553956 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132553956 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132553956 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132553956 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132553956 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132553956 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132553956 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132553956 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132553956 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132553956 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132553956 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132553956 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132553956 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132553956 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132553956 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132553956 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132553956 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132553956 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132553956 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132553956 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132553956 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132553956 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132553956 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132553956 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132553956 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132553956 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132553956 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132553956 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132553956 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132553956 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132553956 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132553956 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132553956 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132553956 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132553956 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132553956 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132553956 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132553956 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132553956 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132553956 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132553956 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132553956 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132553956 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132553956 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132553956 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132553956 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132553956 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132553956 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132553956 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132553956 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132553956 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132553956 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132553956 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132553956 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132553956 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132553956 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132553956 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132553956 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132553956 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132553956 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132553956 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132553956 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132553956 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132553956 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132553956 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132553956 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132553956 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132553956 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132553956 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132553956 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132553956 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132553956 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132553956 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132553956 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132553956 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132553956 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132553956 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132553956 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132553956 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132553956 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132553956 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132553956 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132553956 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132553956 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132553956 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132553956 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132553956 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132553956 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132553956 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132553956 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132553956 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132553956 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 132553956 ≤ n) (h2 : n < 132733812) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
