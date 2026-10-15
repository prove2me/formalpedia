-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4625
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T13:13:15.784139+00:00
-- url     : https://prove2.me/submissions/824c1725-2fe7-4c0d-b79b-4f2c58ce23c0

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 831654676 ≤ n < 831834532 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 831655926 1250 831654676 831654689
    0xb0a140d1209090e03120c0a020c06070c081504150e010209040501090501170115030f0201020a0b2a2106150f031603050621070b180f030610030615 65
    0x301c101082400051000000f809030041641c074001284148200c0002030340d0041190104601058903402d2120525400105036001188110040903c1c9601e5400c0500843d40c030410703402e10030506044410b814124407000100a107080c0e0420040841c00c91040c4008041c4070000c00075201200e00b44650180c0b00e034151954210b41042c0c00018110400d5000c0e60495803100715482c8502204030703865098546140c005440181c4d44001800401d0704240d14901c0c2c644140100c890f82c01aa81c2c45400c1000c0849500e001002c440c0e85400000300c6072909542e00e40c54040100b860f090f500c007e02c1c064a001e0b1021103003515043d0740060301035160f46480321080c501c10000c282d1901d0102d00b1440495100320340c00a0020705880c81e100e440c8e80203001c0c4034010807000380103054201c9800c1d00c0e20181100191211482d100b4640c00083d40751030302c001807040c010f841403058541400741d0140190078040c554000c0c02580540c0c10042c1078050314202c803095039801800400c800b600600081d005010719041003 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 831657176 1250 831655926 831655943
    0x140304080a05071e060c15021207180503160e13050a0b04050706080c07020d2301050906060a1a0703050928080111040b0304052d0708010b0a140d 64
    0x7205102002504108551800e400c0c82208405110540c03803655043c41440b0106100030380450010390f880c00b840e0f0b00405008001420580d500941003014074081c1c0d240c02c04500c00b040c5440c030f08222404400302401040d0010603d4405802c050240e140e41c034803411010410703150108181c18a800270f559401500002190344240403410309090080c810740b070071502031164032000074501c0d0059401d02c1c1700318119032304642020141e400f4015101c040d100100c818101c0c00364031420420307000c25803a401644000000070540746c50ba04240c40c14001514480c841d0030050b030100300e1011640b100201001e11041484d03101e074491f00c0c1c02e480320700440f000103034424181640c0d00105a207074800b4501c015440554100c080780d5900f0100e080307950b210207d00f881c600400080c0308103d5048003c40e04644150106c41c12110007400105086c404186c1c0e401c0014075040c403102e0300480400500000c0e103600c400821000411500040703144034144104c54080300d00032030082d00d941c0c80344400c100c801c0d049101e1 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 831658426 1250 831657176 831657193
    0x240d0b0321031e010f060810050a06230d0e01051803191704060b03100e03090402090604170102040608090f070e06030307050d0f120209060301090213120605060f0103140414030408 79
    0x80305d00070703460043c81c000a2020300003486211080c002d80c000c4030005420a4815810214200d0300c8025a01806d044100c1d010003c104000804006004000e80c4000010300015803250581c00d4980c0680200300ca8214a8130740110300c040030040364060041400c1d0101138200d45841038514842d842e542007902860f0408010600045802c200c011039002c40644001490074400c1c48200ca00d45540000319610a100240050400b0303070080060070001020142400c1c1d44000380d542c0c1003c3c002481040782d401090800c0b02c80c3d005010540c0145e42140031b0914032071040741050307031000d8612501088400240c0403a038242c5042c000c48260302d801c00240c650b001b450910242408122140392000201100c8044080c455940300f500c644220042c6860703d941d10300501a4041e42140c40704083d400906c50000440440407800d0304012449680302003920300c1c190040002c25400185100c0c181404d044c9151000040423006a030f010b648644003850100380070099520790300607500030000c3c9100b001c1c0b6 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 831659676 1250 831658426 831658439
    0xf0105130c0b16080d060503071401030c0801080303060919141911030f0403020f07030507030b160503390c0706050406021902240d0b0321031e01 64
    0x2995032a5a0055414503805903881c0d5403a05544151007282203000c0f4003510000008079103100400c1c1c1c0741c800403c04100c860302c60001a0a01d192544001840781101301417844035600350240a1748640c0c1d6080000030303589003418080c1c880c880103024500c0385004c10001595071a10f440400b9082040b40310821103080041e0240072000816030b484490704400145104008141c0d0246921729001c94140701d0850310742a81b64041503030003a104500b0b41c0211145803540c03d004204040056020304004e052841c03850801d62625a409010201414020010b0361280e981090840e600030070400030701c1780000190b4200201c030900e0b018901540804100f0171010a004613409809010050020766294039655002500c0078410352003800050380102d1820300c42142c0c03640701d00188600181048091040d4030750785051040e6201c0c00721078280000300307040818070814131900c1140101a03000f0110101039007020382c3d1024090103122980f41700040068182e0328000c00116100d5403034101d440c5035584800 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 831660926 1250 831659676 831659701
    0xa0c0e09100f0207150c02030706110403171206061204020d170301060f121a01080c12010e070f030509030906090301090204050702151003150e011803090518060604050d050f0105 78
    0x1d44c02d44400c4000d00ba1900b103441d041c4a01c1080000340e400441c0f41c0005a901ea0740604484240420308001c10b00001000c540b00b0b0800000b442c40258586a0358005410b282180c110042c08842c003898050190540b10950300c2d4640350001d80450b0b824940243c98039040005148005410780c0e040c20100c00040c2c0e4075006400c24100703420320b45904032004840c4c00c1882c11904003451403d603030300e02118601e046500036668580c01092a58080d4903003000030f80281c1c07070600c00fa8000450303e1189002c101e11240e104411a00d004a28502440b440c1017450800da070780d0040a402c9403151200060754100d65074254010b014032603010300140034600d000c41e000307500c801090b00214641c030380304400200340411205c0700c3c0d02900d034003401030681000d00c00b07840002420f228031000d0f841c0d0750f110004d000501d51120b851a4040c0f01e50f480303030f03e241d0408082c004403801c0c5120001c8030083c44400c0c00466543d050645041d2542954200a0600320342003e03440c04200c08102c09140d480c103000d2120560844 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 831662176 1250 831660926 831660937
    0x14190f020c0105070206070809060d1802011e090b0d090f060b0906030a0c090b04020706050f0601030c0f050d090203030918150603011202041a030d051b0a0c0e09100f02 74
    0x35029114058041801500c462241110095204200700031610020ba4844041c2104510140c00a0b0512070849406c0080b0380440200c02000c4403100f01d64011903074080e01c00010050303200c1820800c40c0c0e0001020b00071a00d2401a005c00d4200410a819020b045611000c01c0540110074001d41819a0800000824400340442d000311400303070004105060002d180b00e501c0380c0c4840c000d8a86c034540520341005002041103560300035001c0180e0306c041001c50081074061621120341c05d88905020002402701c0b400000c54400b4442aa0042d600d4a038001054559418103403201007524411440082e0840c0300710106150700c084405503891400c640040540e00c245d01b41c110b00441300c0512000c00c66140007d204144489032148408030060500d03070440c0740362480314481c2d06240c1701084000f03401c1c1000c4804d480e001030000f0030f1040f10354402000c1c54100c0c40310100a4034005070f5644400130095400d0080c81074603602d070408910115030411030601e40b80f10284042080700441460b070300103907014 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 831663426 1250 831662176 831662207
    0x18090123151212030a1d12070c0302121510051e04090803010608010f27021602030322051c03050f0909012402011413030905030f070317040302060a1419 67
    0xe003041010b20070340c807003031b02060741140d030340148450003c254000d000b81d4003d003001c8840c2e4410709400401a01c40b5410002070310002d40140c4505100d4403c03501c49280001c200b07a030800c070715035001c00c000e0b03d500d0b02c0c0d00840002d504c0c01401e90405180810040c1018440c0104101000800050096448941d45058511004030305054a0340c81c101e003c43d1b00c0080c1d086158500c444d903529500c075080340c0e004260b400280c80200c00000310a800080c1540c000000c03041000070280140d030000b003045503c0c05c02500044500d2408146480748180c0d0701640c0c108010103000c400201d4440d5001e1060550b042ba0300010105040b40d82c4030381c09080d000007654010030400d000007440105003030040c0501c00c04480541042c50301d030b685810a42c8800c025681c8164140040f505003c109078a050040480c402e552000500c6880d1a501e0a00f02d4800e00503c0c111840b14244001d00040c2d50b448100c0f03c0b40a007500c0c02181841a0320b4020807288580900c0c0e1556090b21284041e6080d0041540c0110408 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 831664676 1250 831663426 831663431
    0x360c030a0507030b130804090b030a050f0c240708030c0d060f0512031602190909060203040209090d0f0f09150306081606090e070e18090123151212030a 67
    0x42d400c90440317110160a4008000590601c810b001441907a480b240c484840101100e6403443c098503642d080248201d4054010381018a0300c0650381484a101c240e00d081070806044455943d40302e80c0c4041c042e8440c0100100c00000226640800e10740036100e440213540340800c05256517030a1030380116039031f10030580503d190b194040c0ca00c0e02e010040e07138400440c03800c40c0d800048180c0c0c2040320016010b440301d514040039030310100f50245070f03200d1a0000c0d841500010ba41c0d08082c0108400454000c2c80c003411a440205112406644007070441d2021000b410703c2c0000c5020350700242c0d405c986075080301c00c07684c060040c0489025859000f40044881260a48441440030b6550800c07040702809104040340c1d03107030707020041c1c0c04069503480e0b44580c00d45040d240c21080100042da903411321061100be0b8103183c40510001c0942841007031416483e061140c64515041002c0e8000d14000421f040c5900c441c1c60001205900d41c0d501400c01c502040301610480d103460f121071a82900f0a4170004151407 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 831665926 1250 831664676 831664681
    0x60c1903030c030902010c02010e010302040801290d08040902090f040e0a0c0905070f110f070f061202120a0518030a0507060b030c010215150d0308070305360c030a0507030b 76
    0x83c064032a800c4130030307010707510400e03250059001960f0001e2103120b400d04256080000080c00b403420b1040224100d0b5044d8440010000082c43c07200403d503404415108940c525078507000070304000304682c00c176042d42a000da1500103a07030000d44051044413525400c14100300740781e5003031a4040798844c10f551186400400030381e1a800c8490484008496003408207800131502e500c190300500841c0b145a0181084480402c20001c100b030514201707034419482003400c0b003000c2c05807030f80008400c00c640c61215421420f00c10b140c0c80001c0106005011000c02c117646e4008a4441c03101c51215240c2d16042c0b030103c0340e90f0002c2c020024040da2191000307031405441c1c20400078480c500825040318040c0140e00900d0404995018030b01e00303032009041d0307000c003d102d12049441c988804425001c4140280c40c2e03003c4070700e007070314011f000c0d144000e02c079480700d0f1000d0203c103050515120031160000b50b580d00c1720101c1040c51001910f00482c030341e442941f61103891021020000c0005441040c0c034403801c9000c000c0d8 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 831667176 1250 831665926 831665951
    0x90d1401330501050904020f07061b020f030c072304110306030d02070e0606090d0b01062633210c03030304050309040c05091216060516060209060c190303 68
    0x1550a02600d80003e04c1003000c2a010710b0326401611024000500d5503160001c0d641d929021640c0600700c0a04406a590300c00c5d6540d6010300c5004101c000c158091031416500058181d15500103000c0c2c6120003500c10b10024026014034070304242c2ea000a40300300510b000080b2000e10361b400843e903040c460b00c641002c112103076201180c03442c21a0441d429205454585070700300700207170300980c4c110745d000142080e42d90301040c0c10710489802402140c45901c0c40030300c0c2c1c2459481c400c0c054200305800d01029010300201c284241d036508404d0f49036560640340707200700c040705108022513449015130000b0807200b00b010341000c0d5000d50200f8a051001c6540080c0c4800605031640030480d00945203400501035510715050039000722008003020f1914600d001c04a4001402039001e9404550a9901803c43d00804248600e4031101801d0306052441c00c249101d030f0070741c9400070010402000c0a170041441140360b141c030010b40328052079260070340f00c5641d800d8101d005607145410054002906110a40629 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 831668426 1250 831667176 831667271
    0x92803081816051e030c0d0f020a12020103060e04030e0919110415032003091c0309060b03070515090d020d050a110a050a060e1203030907030c0515090d1401 69
    0x10714202070041c0c6002001c11081040c0d0003047e00f01601c202481c0100000181c0d50540034001910100b054501586034600006049501540014541003512001d00000c66002048448074aa04172500021644c43c2d001d1004244080f0101d440058182100d02900c0200400500306607040040d0001009150700c0045050f500d440064485840342084225400d90f40791005503408022a07048920781d4440c1480d4005403046e00d481540000c1d0740c1e990240c20850f0b20b004c0d072600c00808074002d0000904040018030340485103000c0991010002503000029110018000d03041600145001c2074006182000c1382c42e80700c0c0c03040c1150420f480003501e01c428a8110720181c2aa000a091048100c1c102441601d00101d00c0030500d920040c10010010035aa08100451241e0506000b80c00c205140d8589507445034450f4002034440c8048000e001d40052038182942d003034030300c00c80f00721461a50a0030000b006040d4040c10041550a200c0c0201c0350030b69105c482e4100c400d110070b5000c1140307000320070501e4 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 831669676 1250 831668426 831668479
    0x1223100501140a210e0d08150d110409021f08100602010e0307031d040912031103190504030c0803070915021501051e06030f09280308181605 62
    0x4940144d05003910b4002141801051050103940040c42d80d0700d146046290801c1c2c03c0103840000e11513010400103050100c407202d4801c030145c03a440045501581c40300100703100f5011352409541d0b548040000d540d150410055031114071131685c06045410030005004500c104c1e681c103200c00001400040c501e205114a000c0d02d41040043c500700829594124cd094201010340011030b80450050501c80da00c51060200443c8512603104498249503006000d5444491030551143c200b8010807e0050b034240400074502d070b0400700024141d546250130340e6148030a05000d81018070104c00c200342d460b084003034103054520329207005000701e0514a00300d17070303607040903078400120700d00e03c8010040e44c00c00b030703d08010002d002c02000301c11081d8a804207215400c100d506010201600003170181c0001e003032000e100c0310444007000c0b407050440e00c880b00b034180c00c407030701d00404026002e4000380e00d42d0420182000c48400050680b0580422101da0010210090090300d01c60000d90581b4501200c00602011 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 831670926 1250 831669676 831669697
    0x82104110402030703110a021501060302071109040f05030d021216050a0f0e12150a0501050307030f081b0a420f092402030601122310050114 62
    0x2000c02400401c0c4400303900007900718000d240e1035080b6600d1358101e50016000c85681c07035004140c055581b01d00b00300008010380c0041c05051040083e88080380b02080046a035000c2569145031030b840301c0c43d1000d141f00c141c4602070032600000c40c040c0384001064000b0318081120b05103c484580310f01d000a92030703e60840d80840840d1042004010407400380948040d203040c10304140700c115103090049030a1803048140c00c03c05400100c807000c00f4182c030444540d00131240600030090f80d0f0511020907038400c19404050710340d10310306225908216949044441200071803581c01000c1c3e030100119070355268080c004031841410624000c007088181007035001c14880706040340701c0b80c41d40b240801400c9017020184180f05510360b00c0e2800703072041ca4000c002c515845503944451700400707090702e841c00c1407034210380c455824010401c0c4059681c0c004071344150f2003c00400050755050070040c0940c3c4c06010307000c0209002c041010801998600000d500407100281c8070026044511270841031944200d07a03660 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 831672176 1250 831670926 831670943
    0x8010605100507021908060c070515090717030f040e0f0a2a021e030c0d0c03021203060117091c1106180a1a1b07020d0201050c010f0207082104 63
    0x40001d0300e03000703095161009040c0245c0c1d0220380c40d41811824079004035400d0304503040000c5e0321010440304000d01c41d03582c0900c03102c1e0111410041160b50f22542c6500c05c9850f4810064403000b13041c1340a00c1180d1801d084014040c1c1e9565a89254980c0d98400f00d4190b082e103618040003c0030340d01d40e4054181003030044182e05204002d0307140c500b05500d100b1551642140b2820841c0800548840740d51400c0d82001002183c03104000350401d032900d8040b4807a0b01c2005410b601d1700c00000d80000c3c14060310041c00c4a05130b120350302c5100484416080122800004407220144106000b012408020200c0320301034200d2040c08010341034600100300d1068020540c411b10005800c2006820180c0c01c1002d4542560400708140d1202c5202880f00b07001c1d40c0003070548500340304000c1800604d0340001c0360325040103810001ca030b400040380f1028041b0040d050003400107803010050000c0d4440d060201d21111304540711102c60034408616004080310203203081c0e24594010f81c1c030b8600c641551045900c103c00303 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 831673426 1250 831672176 831672187
    0x317150603191107170408030a121e06030312020c0c100201090b040605010f230d0c0b0a050d0b090c0403150b100f121107031b0804030309080106051005 67
    0xc0c400268801440c01031090b150010102a5815034040d804503604140092911100c1070700f044504001d900c0043c05601004000800c165140841600d204510324144900c0100c94401c00078003030900b44641004140c08000e881302c60190070341c000004d0724001d0b501c0c038140072910350462080b0300c00c5070b07030038a21039004c0b0302061018640412801c0e10355426100110701640c403552403011007181640c0803505140c441005000c4080c4405410004040a204001c904403070822a08542c001c5030b007209010302100a025810b2040d0300002074018140303c034000340c1d10240d5600c020301c20340201c03001508031420100352240d18500705040c0740c010401c6103001032a16187d41d80b100e041c1d08000c05004e2541d0389503060070705c0d00c0d03540150011030700f001615030380d49040b01380c00010075415005040072091460080c0f01c000303a82c0c81c401501c0416615080c803100341c40900b2029000f10040c1d280080698000080200030554412414403c03100101d000303005403502c900800100c40c03041c0c20318a0006506200 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 831674676 1250 831673426 831673429
    0x30c030e0714180c030411011b03180b0f120a090c1e080d030e0105250e0409050106090903140a0509040222090515010e030705060a0921031715 63
    0x340140040008210059003884840c9030b500f04002102c41040c1501d0100412050059190700c0c810f03a4031003441d011140e940d1100d01028002c00e0404040c0802c4206d0003822032821a400040002d080503420154031440d80718510f02d444d80c8950501c00051148201080e11100d01d0700500c0c540c1580031001003d501d0600c008040745940b02551702840241c51640000c03c00000d100c2152001c40f10b83c0c0208441d80204203903801e40e480a049080c4c48112a071000e1225110314800e0300c5040494a401040c8002d0038000401502c2c007588003505551914400081045036580a210200d01c20b0300c03400d218009041036401d040c02162002d41c08694104031a10481c942540145010400403221150700d80303543c400441050724079000341203560350340c10502121000020380914411401d2030b05011407101103000c42d8898080744240d41c000d02010921801e0305000d1410003002d0120000ca910f041410083c0005420b20340030300030303000704200c01c1d41b4008400c07603011040e210303580c8400c1900c0800c007000c0 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 831675926 1250 831674676 831674699
    0x6090e0604020d1e06090606050f19170f0f0f1203010f060509010c12031e060b04050913022206211b0906060908010b121b040612030f030c030e07 64
    0x4251128410342c41c10b130015a00c0e124813000c032030041a00041550420b000c0c480c1c0380009504c418400c810004004031803d10f00c540581c10381e04601002205000c040b4078840c5084196180303841d160080c040c902c488440700180c110814a5442c0459140090b078611b615103e21085c0501c04441d02c5044c020b05ca014000da0040c9550b103818501000101d12507103507003c0703e00064500c10000307500c461082c1284c0c6102c0080444031600d80b101001524500000c56095100720712420340500201030000784d070f03440e84d4000075004030f07005000307100300051030480d01c89035043c45082404004c0c98281d011840c24001450080000e00f180100720003090070b40c82d00c0603000d03450030b440c04240300d652001241401d06401101c0041809032074402020782462030940c01d41d507641c46201e0295060191440c00f4401c0080d00c01009500110100e40c481d02040102e0083c12481d0040c0c2c444c030820010801c10103500c003102051001441ea410011985e45a6046007901c4480d03507030490b29807001d0070034080b071540748 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 831677176 1250 831675926 831675953
    0xb07021804110904110a060e01020c010e13020c1c0804030e06070615060f030e030304050606010c112101140108030d1a0405040c0501080106050a2c03060a06090e0604020d 75
    0xb0740c02252090b100000007a4901e000312822100c1c501c89801a888504008000b0f00180c007460501421802052000075612480e00d24510304000200b4104010f41c3c490000004240342c21103c19035550f504080b4942d030343d020100516401070b40c1d40c0c0e4040040352180d800d40780a1a410395442110740101010020349070010031042d6600c1c0d80d00e5903041c0100c070086040500610481e224404184403888020b812903901e02c0c103040341c0350410020080026070125600f9440030342403d083d03c0840081c02c219180c021014545070b0400c03c0040d00c4255400d031000f0002844210340000d2042d00d003500e047d900910310a2261400350b43c003c0c040061840c0382074121b00500541050407002e921a490001011303907006032415280c40d903c2202c280141d5a000f0109409013000781081c529000e15510028001d0280e032030b202090210a80b43d15280b8012612a48500180181150a542001d0707071500000c210a11845030414074240d000544d40c107011440c103206540092080e141d00750f068440f00040c1e10700 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 831678426 1250 831677176 831677183
    0x5030406030e10051017150a1e05090a021c03020c100c170403051204140d020d020301090c050405010602070b12090c030f0f12040b0d0c05090406140a0b07021804 71
    0x8000101c110f0362924424148501300c0711250404140c500920110b500100800c400116045400300907141d01c5040c102d603400500702c40340000d000f4101070340c18000000c00c21000c84c0d99810721007480911500059180d10090080b00d5400d450300710440c001190100c080c0300100903030401c0c100554146081200031084032000c5c205a80322451940c2c4901c404603912803200407410000c5001d000b03002c400c010901510b000d0400e50780c40c0c14142200f0081ea014000012882400c0d4840f009007151640c00001003020760240080c02050014a44944501403078090039000c0d034a0310000040c040c2c400942c40088819149040c0c3c41c0c140103060344940c40f0b0780101004801d02c1074040e82c1300991800c011646058009170302421544254642d8076061a010b09180214218140414042482d508003240c410b00c00d94240002c400360000015515400b03040e0b00305d58030501e8020000b404407107074030303000107800012162070041c40c2d252a03c0010700c0c01400c0c8042e4006550700b148130b0b4040c007020a0190420300 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 831679676 1250 831678426 831678433
    0x80a0b01091502101103040203190f0b07050d140705090d050f03030c0d05130c0501050d0f0e10050c0a0813170a050a0305060919020a111c021905030406030e 69
    0x121951024070705000c000c482e400691150704080d0f2154103d100e81000ca0034100c1c03420703103142004e400103a6036000100080559400800d401801c22060f800d0a0345c410b03601204101c0c00c0d2034466000b4200e03030050280c121825080100c2c060b030725106511b180780305003420386a00d41051981030030f01031b400031421002c8030320b8803407480d1000180300200051803040618a0080d035641c0c01d18242c040550300044c0803020340ca8240350070030b4006010f801c01c60099400138604292641d80080100d4041e010303013100c185a0500d0070807000882000401c0c054145065600c1c1400b00e621200c1c20000c041c883d00d0901c4000881d170314042990390402c20079000c0c0c2c0034050700d80700107218401038195505502004c00e03000492000905511000d806003e21a0300a03003c5035812541c1c9080e240c80c1d0182c1c51040380c0e50001e0740c0c0c001010105240668103050502600720300f140d400180e40c0b107080d188000d240601c0f8002d4400c80c0f031030004c6100d00c48000348100cbd0b40300d0050f5041603d0320105038040c22070b080354601c5500 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 831680926 1250 831679676 831679679
    0x150b030118051618230406020717040b040e0405191b06020726070308030c0d0c0c0302060414150c030702160807030308061c1a13111005040b27010f080a0b0109 70
    0x8a144420341d0246004580041c0c1d109d100b803411088440c404410070030220814030080103440b04810a44003280e444400514150352946811030a01841106410704800002c00041c00c0c0000c2610f100d5905902c1c80c402c00750f0503100e2606903034810251240c01000d07441e03000008440d9048150217007810400e5021030340091b44070b0741d50484030b820844421410350008940348010602078001d568016a40c0d0414200c00502510001c1d211100248007034556262010203800102c0100f003028146140304045c69986c2c10304c00180b1840f9801600e0000040c4545040c111050001841107030460b81540c008181c0c00d4956038042e55031620047c0900d0380500c01e0020f00c502b035481c1f0803046ca01644a0751000c241200061032500d924200a0418070b55455102c0c440310008122200c0d0b003a0015048036844001280180f04668620554105c0c03502d4143c0408d05450000b4070b1442001100040c00e0000120345804004480302c040c040318100005401c1c2000c1654403101d940a407000450624109016030f = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 831682176 1250 831680926 831680981
    0xb0f1b060901110304050303151f02010203161404030b2809020a080729070210080a0c08040209010605031b040602030c160e04150b030118051618 64
    0x6141810408a5900000100324022900788030744403211110030240d5045040c01c1d1550b99403400010302c08001819803810043e4150b8800366250752105409840c0c2104038030042000740030303400a0390100548032580761403400140c0103101c070410310704261011505162950325890a8002d000d401e5052180321100014a40c0c00511316000c44255482e4011840400714810301c0340d00c0c921540f0810035504040d009100c0e03617009045580070a6000c000074580c80d4904100010039110b07408001b50b10854a900c002e03411500320403100d210b450500b10810603508002005d5076041012100203511044101c01481802d00400140d50800c03400708074598013a950b8500b42d201e0b030303106400a02c0980e00c04164078420a0381000360000d2089406124441c4501d407a43e41d00e000080070308028001e03020106143c02002c0e05078818141500014020320113003506554102c1d22010300340c001c2d54035008000e20b942050300014004412100d00300030b81d40010f03940c2009a070050504203009954031100e40c1a00120 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 831683426 1250 831682176 831682207
    0x50d0f0e03010612051506060412020f060a03050f07080402090f040f12050301090f060830040e0a060b09030a1e05100e0123130f12030b0301150e010b0f 67
    0x13600d941210118004641e040c50761800140142d0b1040e2000e04108010b03690719954140e80441c1d61a001d28100300910340b001482d0004d0a0505075000b010104648003101e40c1078100c079010b0030940000707102548031628110f0301440d04840107900003808402242c0007800700c03002981d0040c0600030701d9188807100c1d0749428015a55a5543d030003d40c0101c0140a5030307900b40701c2c1b0250701610010400c1014608000d951310384d101c25900d0100c5a4440c0d0500d4218248058217003000ea0024074040d545503200c2038403150b0507400b80c540381d09036841e0050114441140d101141c0c16640d0080007041d9440f99031361030356201d00d0041c140007400008800342400040040000d803d41c0740300c8403030101d0202c000c40892804c4503d105400d12111501003081c0c080444107625254001e1000c1c20016440c1849080c025104080000018140c5c00c90315401c90440d03a040c1c2c451006910304034024040d003810288a015819694040e0a2005d54010300420503002c10700c0040c032044d80303c5140309080000c60250480c0c2c = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 831684676 1250 831683426 831683429
    0x60723030f240310201603090e0606030604050a0b040c0207211211160902130915060318050303280c2f0f01021e0403050d0f0e030106 59
    0x10480c1e8040144245aa0840380b02000c0800c1d48101c2201c07000c0040009a941d070440300701c401c0240d9a411850590000c1301360308100c0600001c01e01d5661602c10701c21802c91484d031601038000402c9100e0200d603112403140e100c0e0098074020b061b1801c5486010400c4002e0034054002414a40d82c2e98801d052910b550194a0000c21660007410790302e0315100c40d84040004001c2006108204c550701c03140020b080155100341407496113080d642c08001c4c40380c1c1524040b001120703e00300031026140000d80f0700c96900104913175407160140c0054140d4407154107042e40d40220741c1c07030054120014144600f5210344e210311005500005481ea0f00140c0f92103c5080d5030054810115082035940c9000c4528002e8020307035540c005140c006c0109800c500e1000706a1184201d1954181c800203882c40b003036800b07a840b802d031258103000a0700d0001e0b8040070004c0c002d50041c08045001304082944800d00c50380c98056504882c0c00402400e8a00d070900b60441d0f41c0c8071504060004d21000325951055a2401d03c034150 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 831685926 1250 831684676 831684691
    0xa030201030b0f040f020705060a0c1707230403060b0d08040b0904090b04051513021014070c09050105030709141b0d0203090102182d030a050319170906072303 70
    0x11f83c0d54005060082c1040401441c0c0c41ca01410140d1070383c1501e42c0041c2d0800e81609150209038540c80e0428203e94100001e0319005c030400c5e600715145400001e21000f4021030303114840402030403011205000240f40352010140000c6800c0c0020070581c031201006042d4040001d00006070b030305150b541c08050400a0710103643c4c039480300300e103400d2229000d204190003060308d42c81043d69007000e5000507540656080b10b8801c0103e0740e100205101980c0e400d82d0780d41a8050700e03c29049481c4c03018440241001d1190f148203200e50038001891a015115a41400c1014808030820380d4620f2008010211074a2440302c04810401190300c0c42115440a10b008646810001d643c0e42d13071100e40400f0038008500da0904c5062200001c0120b8003051512a60480080134803110301100d2100083c109100040040e29a010015010001c9000a406070404581c0341d15000e20000b1092802c01201d60b0440ea0110350f07038845000b04d100240a10301c281c041900900c40242c8008007441c40680e603802c20384288 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 831687176 1250 831685926 831685931
    0xb040b090f2701151a0403020402340507050f09161b050d0f080f1b0c070f081005012616030303020310080610091a0306011511010203060a030201030b0f040f 69
    0x4801041c1104c00300c001000e1118882144001016040c00c0605c00c610000b842140c0c00904101c4125081c401100303040d40240c0c20042c282401841c8086070510340f1400c58160040f0100400d651030b01c0d40c50400d460801406203400d5580e034440003074080d55841c2a00c0140440001c0c1250b6641440c1840d00c4541d201c2e0300a01290080c0343c0c0c000c2c001091740e0351800c050020040400401c582020142a8403405401144840c07c0e42c541072458148655601e10100e4040d191001c21289008c00442040303401010407030700c0e04010345a4070005c0354001c1c000c0703031882c42200f005902000701c80e800c1c4107010303103a07072044d07564200c1ca0103800d078001d00803603100301c02007500030003006903804506000e2402820408064902d81c601030796151440007150040001d441d59401d030390f0f05c6010f404400d011060801404a03030203544c640b103007107601e031300d003640600000351000390341d074281440600989014080242500e282c9e40c0c116401134000d4225004651b8004200300c0c0505059500c5018102e040b41129000 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 831688426 1250 831687176 831687191
    0x1110414040e010e062706150d020f040615090b07081909120308011403070506040b0d0204030501181b060206150303071a07030c0e03060103030e0a0b0c01050a0b040b090f2701 77
    0x980c2c40c01e406c81c5604a03080d0042c01c03c008140b140c00203411202c2400316000a944415480000d40c0102c0313460440d41c000b4501140428284000e00c4c4401003a5440e071034000010340d0306c10342001075109904005215801c180006a004e0480b5000559407400d14140101e0f01610741443c0d8114254a41d000d0b000180803000400100f4801820820825816000b8010003800d180101c4c00038440c602c01c0a081c0e06d000220980600b040e0340c141d4016680c010028400001049140340d03003004c00c10019105064200c40d00750306042c403041802d08580141c1c025008070399800388440c2d410340d03100700b400750540010041c800015a0751045409052060127644205e414032050050468060b2004003042c00030f1016280010b980024901e070449506242050224007a50b0124274440a5603024190302c0c030740812a01039250301034021510415807000c0400c95080807a0400003038506c100d00d03a0b81c00c454038038040742840203042c991a42c044500144210310002c2c10785080f9032042050380f000c1459561f24107 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 831689676 1250 831688426 831688471
    0x14040c05150711090712151715070509061b0d08011e150c05011b0e03030a120b030c0d050312060a2301020f0f061f06080c07051204090e01110414040e010e06 69
    0x8c081500c8200003080342040060403c42c040740b01a007581c2c00c0c0034010074014443d54412045800203c1c00710305148180005000043c3d540c43e428058002158004001281030700b0200b01660f103000c47c0ca040126124500781b09142d4486da541030341c008100303002a000c03000c074500f40507440c03111070818640903620b070340706800500040103481124840c1d00100007661109500007089501c0c2031401400282040d1a0700020740391041054110f03030010034410880c1d040c1304010000d40b844111400703d210050f9100020040383e50101e0040020030a00704142c6003811095080010490406004031002251801001032400442d00c440d41c100780c0c050020007416081488240024980080c20014130358204680601071001c010940c0000d000013107030764406d20404011142036841c0403104103907150b480e002604050070312101c20900755800c000c01c0d0000c0e5002c010403a4122408941c09061002515013004003509090940e16070564072110300c004a820309104d541c1c0204062600724216074035914 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 831690926 1250 831689676 831689699
    0x415021608160507140f09062103030f0c070c14040b040203010f05030c0603011514040b04060305091b0303160c0b040b1306031e0c0314040c0515071109071215 70
    0x1000174100d041d505214910f5904c1d4a0f6405624030001ca401108a0b82ca01004c55420319240e1200303499459072546a00514001200a50003031802c17a203024a250f9919040d8686441024401412001820802c0000b4004841c2d9079200c0039000304003140c1003aa000c0080c0c260382003a04100b641c140a030400304614501000148003400081d00e07000c7c04c42d0716056410040c028040b065800380700c081000500e51803030102c01c503000703401e02420789030300d654a900d0000c0c0108011a524045441074030410364604a070f0324403150307d40700c00900440c90151010103442c1d1145015608460a0020940204039800c122025102501c24800442d4407201c1d1040d13100f0b0300c0141544850181441c0480c1411030242c0c048a01e0440c4007540f40104000c488448201c0007858400d04038101e0820305000c0c0800c11156080c88002c41d02c0448201102c00000000700e0014440c44000030440d14003d03801d5000b5080a10501d548110241403603080105043c0d031400984030307121301c0c0100145c0204410700c003000885 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 831692176 1250 831690926 831690929
    0x216080304080d081b030c0705010c0e100810141801030506040b1614071e051c1d1c08030c0d0f0b030307020409021c0503040306060504050415021608160507 69
    0x1031074001c0b041d051841188100303569094114175008800400180550320b40421203203895072200c001c010720940c440000381341580012a00b8400c2586080c4004058402c0da0054003a60521030b24480c101e20b411480c4505000c414485a0855102e15440c0c02001140085034000d6000318098000d520b05880d06001010000701142001010901c038152056444490740e49c03510200300043d0f5403840a400c01a1292422059a1210041c2040f0381c04c100800440c44030b108a14910f100380100151180554002c4240d03072030b0301130304070203507e0151076403420580224040c0d41061820684c55060f80304c00000d54000c485003800c03510005040e1540c2c1006120314000402641000c104200d8907400082e02c078421400003038401c076224190201075503560aa04000403040304000301e22021240b41560b1aa00a8402503e405242040000b150b003042d0081300e10896001840000107031031800144025001941185020f0030740301a0307000040c0daa0340c020704030041040180c890203005c81c030381185012203d = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 831693426 1250 831692176 831692203
    0x50604150e04080a17041416060f05031306022205040218010804051609090b060a030507030b15190306050601020703080d1d0102130302030714060d0c021608030408 72
    0x16035500300310200e01c10034002c0d00300354003840c800d9079100308020468616102d00d01040c1d03403c003090107200410840480c000741c0002800d003130741ca41d80c014110a0600c60960f1207400003045003184050085880764001355804072020215045c440415220401242c00c16180b604485088082000c1c08000301900680100b400b01c60a514080700b03035001c141c045100700c180b1810721007000c2c04101004010f001a50302040e007901e8008801c3c3c2e40c2e2000d203002d0400b0345401d6078208480c4020949604004802e0429690007000900740507107142c0d1400508000103295442054035000702428590b54055030b5840c0242c000590394000d41141056400c6410162246040d0750021504100051411080e51200c81c2b0703202002508540345068031596070300c4206210102d510010740c1440f60541412543c1c1524000d4045498450300ca800b401c1c540180c40e09500e9000c40300340a040e040041907008019205102e105882e400803071b214444c50300b801c543c1c002d01e0300c9420110381408512001c00c08800758161 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 831694676 1250 831693426 831693461
    0x103080910022a0108090325110312180301020c03031605040305011112011707090f060503100204092712140d1b02120403021504031b091a030c010807021e01050604 72
    0x2811401e203540b5003440c0c0030400031f1b580d184101c205210480c5202101e6560207000da8542c0f00040420f0324be242e0100d4a801d80410300c110701c90b0b915090500c2942d030344281d48401507245886803a99400d000c08203000c82c1e01003050030171000c0700141003070007200d60041451501e1911807000703901202c12024140c001b107089200e080070440c6d2860000400800f01d95a050002820b802c41d03040f81e0010f001960044c9170144144440c50304840e440360700070801c6402042e03041101c01000182c1c120408454003581c8407503484280000c0200c0c4d01e200d24085400c1181c00c0820591070804400070403074100d031041880455407245240903d1443d101500324003042071025280032800d42c5816031183c0142d003c064080c06280c0110700c1a494280c0445010b550003246030702d584103816807010140304a41c016020b20f5814021114140c03082917582c2e15600c0300080240c07042a50080c0110f681d02c000030f2a01c401c5202c4c02c00d103015022100240510010b520300b0011a803480c0000034001942c818113042c0d1100075 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 831695926 1250 831694676 831694687
    0x3003030108060a0b0d260408060a0f0204060f052a03030717130f17030412140a0801030602070624030c0509010b03010b030a020717030a0b04050103080910022a01080903 74
    0x60303502442440d03d5501c800f002240564810f07881d2004000d0800b1b1a105200024000ca448800000c03424401c2080203030074460404180c0c0403c05a0149100305d10200e01240c2007203c2c030740d000382c020300702c1e0828250b0340025680c031484440a650550540900003030700000184440558881e151404e40700e8207010894180c203000d100582c04400b92000900f2200c01081240f00b0007007184480c0710101c0c51364161503224203142c00c112406011034014000402c08840c0070825160180050b0382c454010760b22010003d0f840d540324100a503100e4070040301c0c0e4554880035207260340040304452a145600000750312480b41035140551142d0712a8115a1241c241300c40104080c0e4000800c8074190b032900c108681d12500c81201e42e801034058120000c161003020103061210285480182d40f18007041d10060095060307110070f00040351028000646505e13010800003005080c21850415444418812110140000030100c403031886851400c5500d403c0702d120f00f06c036a607880070750290031402c0d0340095031510 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 831697176 1250 831695926 831695929
    0x8030403200a051009060f0c0e030714130c0e03060c1b061504020a0903121d012309030a0b090703020117150904081c0b010807020d09053003030108060a0b 68
    0x142e070765451144d84030b034450401c041008400d03000041c40503541c1006000d098410031020740310341d000028141c02845050302c00110350b80c8400d10303010b20000c080c200d4442d0752607109280d0081d00c0e05030044802d101d000d415510927078800f0402c0911510b00c14001c2c1d51101a0700c2400103890b07140301c0c0000d195600500611134400c460044803451202e08035401a0707111400d80c0700362251065036001802d0030f141038100c01d00d4140c11103625070a00f4560310702c035100390b441030380191a400c400c13200340100b85151100d03005d903458000c0d008100f15100141214a5109541d85054840d10304444548240c2c0001c1000c10440d40c0044203041607a0708020452914034091407002243d83c0c464034002e10441992011400f40302012003101c03515440381d0701c0c1c010a00c40c03140f0b0f00006002e050350403034001000c03040050000b5201160f460b0101066641d400c4041c0c0c605802c100d2083c070720310000c1c1d49034441c40201e1110403103861100d0706500c0c4150043c44e10b87d8540001703142444401040c40d40303075504185401049 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 831698426 1250 831697176 831697183
    0x105010e101709070305150a1d0a061d1f05010504090b190b090708160206100b0f0d0905071e0b03010e04030c0506070c020f04020f0405120a08030403200a05 69
    0x700b003440180e0b038100d40e01c195545240c428a0390002d0014066502544115171900100501c603400c500000e002012050b0340006040780b88065000c1d5030740110481c03c00150894020b558501d11001d01c0d030030702c088171310491420060062003402080000408200101c820303805481c0c0104000c4604103d04c92180c0c85202180d000141002852441890440c4032045a64060240420f0240000e000c034500f03035402811082090341e5845504080c0c0901c7da55852000400510846659501d040c18a01e4140710b000070b50051030900450080038400107000c5116842600e9815008000401c03201c0c1c07030140c0da0503400c6441c40d5aa0b40405203a00140801a0307500226411070708000780608542d50f441c1401ca40c1007842c00300c018614015601031040c1607038404100e00110f8000c640c00c11103400070008100480c0f18030f0080c440e1150050100700030078680b061042d03105d01403030001d807400301885503512103050380111400c5010880426000c200140c20406c0000044e62100040101c2880c5440e060754 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 831699676 1250 831698426 831698447
    0x1a030d0f0201090602040603060305060f011404090507031502040f14060a0507020f041a010909090c03030e0307080604210c05150c0d0207140f07030c0e040611120105010e10 76
    0x9100c203100c501003a0510035400182c01c030390003032000c540710368075840c0003400b8000c50301c400d43c3d03207109070340c00325604401c003651a5049901a480c4c12200349660301c1800054401c1400640d8507015081c0004040385c4500820b204070b0000420059881d401d11041d2864100180c0269114610040d0788001381c1d1245812581444c7c0a0304145468900300d200107551110032a490b56002400d180114940001c40304050038417078001d8a40302441a200c0e2403480c00c49034600c4002d441d19407000001c20100780aa561074075590005020340c0c0d8540c0c0c8400b4070307510b00390043d00c0032911401c1a1515403d50709071a064803a0030101868900d4083c26203841c1d407942c1d1852611380b000d4002a11003c0340c00490280c0480300074442c2e41200f0b54454106041c10f09006c420549600600d0060684032503100c880402c0c0a401c0e69030103682c080e0014101041c070b402083c001402210403940d14802e0b04210385500010f40070b8025902c0000c07210398100000148540240940c030360250484140840c1043d401000290 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 831700926 1250 831699676 831699703
    0x60f05030f0411031b240415020114070905091e07030b13060618050409024b010e030706050906030402031507080414120909150901080708011a03 64
    0xc40c0c549503810320000904490b40d03c543d15206240780110300c40d0f02e00750125803018046a174050043d000184400c084500b0010040200d10108801e100c81c0c00c286000125508151000003060a0300114080e2032107000d0300c00c400400d0b13100c07074100054600480c0b0580d01a144410000040d50b140c0d07003034414094003a2503c010f164403204a1107540d1103249a2840a40b9405800e200d003a98030750002c0c103501c9020311a107010f88506440818241010700641e46030540c0503004c0c103049510343c5080c500046000041d94418020500c0c036101d04045001801c080d00541c1481c4602c9100750300c005003255030485003440c02034000c108200a001d4104096640c099000e4905583c2e84d511440000c2c1088110140c900101281000348a044c560181140d84154420180d2134a032a0840310303038a50b40d0652400141c201c900400c0042020300348119550340004240c18003074a06070745080041c8400000740c0100c40e641e4402c540402207107000b4003c40fa04085c52a03048420b802446e004aa140c03621000590b = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 831702176 1250 831700926 831700951
    0x3012d050907050a020c0303130905161e031404060605011e0f1b05070801050912040305031606200a14070c0e040302070807090b0a050316030318051f09060f0503 71
    0x2039075117402441860075041c2d00078103482d40c5e90420034103e8560b5025010f032018042c5040005001c0d140e0b19124091a41c0c86500d074488540269049407800090500c214000c0507243e030161020744028049030380c0540e00c03a0b03c0200d04170303080c07900041118550500d2180c11a41042c40001b00c80e400242e090404411880d04403c5603800d403814202804010310001e0240c41080800a28290117602c801e0007061081c00b034580c203074a0f4000b918403034043c1c0e00018105400400200c4100760414810f0104148514008a1300f00b05040454812603551400c4603030a000026a40c41320a44c800c5c59400c2c85425004514200796041d21451812a441d0003500c1e25690200c011400303040c02004100c00600e401000c8441680d01c0712504c001a14200c031860b406034120100c041018036010444201040c07032610500c40803403554404603101c0709100450403904010460100380358881605080c107100003901c842c180540000070040c907102d9180c2c004c100300b00621800700200d80d80001200d4029078040041c = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 831703426 1250 831702176 831702187
    0x51b1b0609270402040c05040f2106020c06060118080615031513050705060f030a0b040216030818030c0a080309101a010201050108011e180803012d05090705 69
    0xc200b000c140041c020728901c2100c21003400b01e00701d540407a48a28801d540500070781d4a212010380f1503021300c6c0a8281d000c81d0074001800281c65050b0405030001c01e2044140b0b81d0f00040d00c0b42d50481e0300403e00c040d8107400480c20458907582094001005000151500c6812481c10406684448000d04402c00391000d162850354070b83c2d02080100d00e1107191320b031240900e0400e41c84103103e41c00c074018125481e00030f01c0e90000d8540b82076001d95040302541c1c807403580b8503581c41d02e20800501d45000c045620560902c00c14082614030300c0f2062505100741c48103031480c204080030b40c0850781c0038031001ea81e41c0d10401144e00d500801190080c5056400304200d91281c6905070401d0901845001c0b02400707520300305030f016014000101c2c1600ca200203130000c20843c2d80355210385d42a05c441c24800c1c080303c83c02c0f03061055000c0065004442c80f00740c80480050018083d501ea104590082e8451000c132418a00100e07400c1030314081400719400c5038401604100d203090041911582c00600d0403040c4200440c0 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 831704676 1250 831703426 831703429
    0x703110606150f07140a032703030c0f12050406020f0a020d0f06110a0801031a16120e070608040c0803090d0308061207030302010c0e0d050c0904050319051b1b0609 72
    0x1510b0045a009241034800c1d0901103140d5500c080c20481580040c2840906904186690228801c828840030408507294254ac41c05e444080b0140e41c11a0028286900100800e41d903140c64003000750296100d568039854054000e01d00040e151508038a60020041c1c6c100595600c4080c405031a4401c040c0004801d0b43c0c285000100140b9a1959100000040100d95580d005015905880c441c0d070800519103900164481c1d5584111099504034000301040401280616043c41030301d0414440483d05040c54012541800100d40c4908003044200003413208010550310003a0140448800550410241000048140c02a8070700035040c00805404104a501c405800039125900352040f03451b80d964900d002402800c641d6081c500095100c411130500749014010380d12485c2e041001010700b24107010401025103006042220039220801c0401102d100050000300c0030039142d1903141e260282801e5030786103c60203500d000800e03002100d1066031450004803503508040140c03a0070342c40b11000c60 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 831705926 1250 831704676 831704707
    0x8060a0e10030b13060c0320070218220f0c0501140a03020f0403050604050c010e2d0a170f0d0906020307032102070f05070b09030a11010215010605070311060615 71
    0xf035014005c035040018003084140c254000c4600d044000044040311140c0c0441e42e680380c050340304025801600e41e03000021490704081c6150f04407241055030208118000d90182d0108100c000445031840ca1155503030a200350a00e481000340400c3c00c181d086018502d4111a19124021100b41410350100c2c030707803840361884420343c0c0246074400210b461310301f410305141d607544001d0000e15000408903e0300c80c070311781445443c030010048040107249010043c8200159411620300419030000550080061400f9a0302c00050404000c080902003074001310708480c0c103148c4070b1081d41c0d0620940e0341040140700e50000864049030741515080c01c40301041d40000d80072000c4071140d46042c0d030000c0350040510208419202e445071003482120135203940c4034002c9030703240142c0d41141d501d500314104041c0401e018450303030952040144140d0301d4040384548041030710300b82030700413400041010407803404064000e0140e440300b00300f1200501152400d0700010f414180044201413542030082540d0100e042043d = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 831707176 1250 831705926 831705961
    0x40b040c170105160504060c060b0607060219110309010e06090d120203090117010806190e01050103060e0c0406030506271c1202130302061b010c08060a0e10030b 71
    0x14100704210016004040b4003a000075a2075038a1181020303ea8101c40740a08111401c917030081c1c40c0c05041203015142c40c00200102c0d500950400c0b001c02079440000c09901c01001c12245030790281c4401041c20900504070030340c2c003004813119801000060781c1070f0303041007034182840b40450701107607030315803040209580401d849802800740c0c0c2580d42c207080081c0c0200150100c08000c0c1d0750011024103140241c60240f1082c410440740c3d400003400f084500c8480354100c081d41a0304000844c403864014003c60031503400b64420798625aa07841200e0408030140101c81103503400b2141400030500f580c90316611082c0140c18064004003c4603075011740c00810403e81e0340020303014140d03081800c0320710102005001a1800d00c000400750300308810500c3c918030079103900304010040c100c902400c5d030f400d00c110751b845468100f010741c21082000901d0603090041310303215040781d42e6100d00c5080440c203101005800e40c105c5425072107000300300070545040001000c02c4a4100c84c06d01100d441d080603041914040 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 831708426 1250 831707176 831707189
    0x50c03070602010b0f041e0e280204060801051b0a020c041508010608070f0902130503100905062a180a0b0307080f060105120a112a03030c03040b040c 66
    0x112400054a1a010b601c40c440700c2e08162058031800d86250200403ca404580c0d07c03050302e45c00d003041482c00d1100b681c0459131120400b401c648501c1110440b40810000c00c0c1150400f0034038810703c620850907d070080707400518204c0000e0000e810401240403c001e0581010041030501041e082c035524800c002c00c04000c2c001800c10020b000c00944007224441c520302a00009609103080002c4543c030000313a45040725180d03040c0001550400200d40c02940c01004081c05524110302d011640740c0c1c0c02d01048003c40515480050358070580e103000b038105030300106484d2014100340c1c0c002c020881d07648a000304070624420404d550f1a2105400400500c0143c000f40e0003a00822000c200100108020b40c0134503120749590b4040e03641c4080c080000c4408440e01400a00e0502c44401c0340217818551701d40082c0c2c00315001c100c0f4822400c002c0b1f500e03044440c404600d203031200a2b10340c10950807a888900107140c0c1014500d1803400e4220344401d40f00140004102140580c0002c00b4410000d0060000d0840f = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 831709676 1250 831708426 831708433
    0x30b061603141206041805060c070606090507020a200f19031403120609011401030905102c0633031207060b09160f0201060315050f0703020309060103020904050c03 72
    0x64240b82000300010813039195004030720b840c0150042d41120010b80a01c603038404003d001c1e03035403510400b880a0700080e208070341050b1070b4031001c50a03604038015181320700b440354000c0414060501f1b1120400b48914a201c510900000d102c080702d0b01c1c2c211203040406402c0e0740552a4000800f030052101d076181d03002038540c00481c00b02820b6841c002c80103110307408880403400c00f180c40b9a010810392803001e1240004407860003e5140c01e035400780d001002030a0040301503d520100c01c134502d2040c0d880c0325602e408401c05031486c40041c1821141310003542400c0701c0090038545801c0e518011900220a81c1e00000d0303000d4002d55589001600044940e000c3c080c083d584218080d41c0b4214407074201d42011502d0505285070b104080c00d24a038118410a00303128000b0040070402c0043c6c40c0c4c0c40a141460007107540742c403004401300b81d86400c1084800d81448001800e032070030710040480054044c0001d420103004000780412498009020740c191b03501114199000e40f1503140c00c501e880c0704010b91640600 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 831710926 1250 831709676 831709687
    0xc02190308040518090703061d010903081b03010e040809151c0e03190f1412010f0503070602070501120b12070509073e030c010b010906030b06160314 66
    0x5214000d40308440081c2d4104d0102844044000d5243c8400c481c0c1800c2c42d0720103c0100081401c0350070000600c1c402d15101002e0a0025091509449202209a01040e090418800b40c840882003203908510088903403030840d418074840f240504170162000c0e244030000f1940c103610740c1e121000700000c407850300d8030240d68807040a0107491641e0b00c4869052010700d0903c0300290f4941c00b208a0703c0b85007284a10002d00d00c41c804082e90700e625421744a8081008031724086410324500c60040604001c50401d40d2129807400c00c482c044007802d03400950094000c41e804000c01600041c0e20020342d0001d0a1072800c14414642220080c0000180b4541c400034010240610b0303d40403490301c2c05c0c1d490507110a206130b0354940c8107490141114441c0340c143e40f80c607040c20714180d074661a000c80d100164002e603140003074030090751441d41c2c1210f100784849035905c030300100745513810604120082c082403c060281440b0100012118001d140c4541800008241aa001c05200e079940803045004400c8160300ea0 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 831712176 1250 831710926 831710933
    0x20a0e0703050901060b070b1b0d020c1507030606050a080705130914071407020904060f140108060609061806130c05130b1207050c0a020405241905010c021903 70
    0x420090f10041010b52800e400030034848403032411030301019042040c00c4200c0e01e80401c010303025151100c00318609401807107000207501076400289030ba990340d1f070020300c5492503040041c0c0d54004094100390605113810820040300e07804c5801d030342c6034504030b05000141c0c0d612101d007640c40b40720b00f0082d590721400d0104003050200c3d0660001c030300030070482d8007200583e5503010103503000c41c280c01e01d0034980001402044010b00d0704869666019200d0100401c0302c55180740c10300c050707694080300a0010a6501c0040c4580c0d681046807a51240e400c42d2840050304100f0040342184181c2c81007500d1181032030000954685810034081c903d00d403102820818018400c1008009070403070a0000c5040d090000c0005600038202c054401c101000385406405440303401050b100c40e030242e04007038194007503160740781d000d41d5540c40f030705102e0508029035120210a5148541c1d0509450344070b18481d0300d405500030301c0c405140205006484081c04c186404203030600010341c541c9a02164080044034905010041 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 831713426 1250 831712176 831712181
    0x27031203041e032d05030117070b0a030212070201060509060409020f03100e010b040509030a030e160e0708010819060c1103030a06060305341e11190519020a0e0703 72
    0x1980460007101040b40002c613050b501401001d1a940040c00900c01880300100034000c5c11440e1681808449440e035641c8609401508400070300300100764040340d103060200700c21040580c80308092000b00315032420040000c15150016120078000c40e61114100215204c00e02000d422030340060441e04048240e07101c010241002d02241c131050350908041e003456052a0107414024a14080510f0406040180890040100b4803802c00584500c81640700003242d003610319000350041012402c1646001031024201c01ca060340031f800c0c151b00006068080f5102410344040e510340c010700115a860003840216003180c4440c00d02c00b00d40c00004113100140d80c0c9507120b1307021100c2d1354605104640e2000c900c000b166520000005006400004548103910700149800a00c890f9050120200c240b1090b660f00c1c1e071045115003130100e01310810000680004010032082c051059551560039441035868a03202c0d0307203501a0703030848001e203030a080456413025403c8025208003d40100313a440d1a80d0300031f01 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 831714676 1250 831713426 831713447
    0x4062c042904060f1802040b16120801240207083304150b0a0f080f0c190302131805150f070516020117090327031203041e03 55
    0x1d41841095103503030075080030b00400c022107a9000310111031901d03012003103248140c00c09400300459070810005c2a000c0502c005000b0204207208040d200650310f1a0250854071305644a50030312404030010010000c10480a100c200b14010110008000624043c0e00d004aaa04041c146001da040300031440f50354010009506014082140b00c1c14101c108207589100059038064200f81403101200d0802c0311981004805100141a2100e1540e4401c41001288190b41155116030806030501c00486030030803a0301074403c0f046460540703526000003015a10510b030b00c8024000c2400c400d00f03110380d0740c89510800d250728039803041c095003101c03c3c80e10030340b64140324442960ba0220b01000c00c550010080140388600c0803903ca491905a4144c4488018102c0315000c9040000c0313640a04d43c10350302910b626024207014030041d40c641c4094a80d4603405615022031041309002010711629a0307500080581d1030001980700f02e642da44450910210501c4040f0782c80d4626540d03000c2c850201540100c0c0c02c0ca = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 831715926 1250 831714676 831714731
    0x120106090507170133110d030608010b041116150203010b0417060708010608180703120306050f09060f010c08070818010804030f320a0f0504062c04 65
    0x4403260380313500d1010403400c0381c094040360748020020801e10b10000c0c11080e00c0c50f0034050600f60103800d0206c91603403030b052081040c04006900e8250802c43d0150901403030901000440302032028502c43ca0610500f4064140b15205c4101991070410500600030700440c03643c1080b20b07083d503480d07858084200d060742c054468070744000b01680d0281c1d02e0b01004650350b03016880982c0d9002840e440c0500c1154502000b40c000c141043e85820aa09049c0302080030400440c402c9500c0d0003401c12050b0045c049035020340c03046d40124161a08030704580d440c4001150321000c204ca46108207510040100c0c0c400c80c003804010003481000a16000340501c2c0f10241079881c6828814058600f1440300440340c0072019070b0014041640104000040c50140b009685403244880249141c1c081106200c0b401124a00507a040362400040c00e0700d401e40e01400c00000c6040754200786161503e801d1008001503401c0d4112800382c01040480743c0840554219072021207801881400740008072130f1442e18800703103040b4070b1 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 831717176 1250 831715926 831715967
    0x301032108010e010504021e071101020f0c0d0b07140d090c0504020c1009140a03030603151e050912030145050a20040603150e06120106090507 63
    0x29a01078464010a416120310420080c451303481c242c1404080d4001480c5201e203540101c0415804000d03030006000c8031400744040c00c2c0281c20320760002e401d1560817030744101381e43c000d0700f490920b6441d4108408201c0754041250145540c40d09812589032003041c0010544040009500004001036040240024000e40b65603002d595100100000c0b13102e0003040c071400e41c0080043d45481249030b44240e4010f0700400c01c0d040c101000c070406c070342000e0b140c4004a010036a901d03801e105210744c00c0403010036040c060208020381d83c01e5208240d45010307014640d00c0815205c0d00003c200d49414000e82c0380c040403001150b0303100c0d610f940c0d03200325190411a00103096003510b20100c601c1e00c9854840000f440c4031420410b651004810090003411008018032603290711002d1606042800182c09980c84003c40c5a1039210b900701301000b000c1d170311100041488048040342c24440c12909400300d6402c02005c03140c03a00405c2000c14468058440d641c084078415281000f005250394021480b00358403401d8038501e = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 831718426 1250 831717176 831717233
    0x304031205160c0b0424020c070509070e12071203080906070c0c23090408090102060730090c09020901090504021c0203190606020309010905010f0e01051e030103 71
    0x49100301c081c03492182c0012102902900414104024240c003d4000c9003070220b170304054940080761020309038581503017680c0040c200007080c10610221020701000c54601000382004e1100400030390380c3c0200c0c14411542d8500c50302843e0001c00202c0d00400c00c913078140c21500581c0c2006440640d00725002c11030390040b00005000940b140b810503007619030003443e0740b403038070305040854071071031066484404203c180d200c1c542880c0d03951071440d41c400c52080c06642d95550b0004002410810050078075014044144218800386021400c1c46030015068a40c00074488940249040504a0207101800342e0b035000304081201403035034004110801082c1c0f50011a039030790b2002d2004134400c080b003208083d1036210340070300c95460b583c0007503801012420301103014012802c20041110746650204002d41d0000801029558101049100802c82420b04228178480c1d901e010f0444080e410109040140009141d64002070350320703020304611403d00c80251651307180d02c0d055000d82c1410418012110034200c0 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 831719676 1250 831718426 831718441
    0xb0103021e01120b01090302040e1c050313030e040b040c080601020705180105101e0309060b1005030708100f030b010512010c091206091205130f05030a030c0203010605060304031205 80
    0x750521a5006039076103409481c211004000808401841c0c40c1001290701001000d80c1c0d480c0140c11103035006101402002c0d0009036034220f9203405072142000e1020a008000b000f80c0024140c03240207806050604d12406000c0001c0e004114104127158440d24001031050303000d40c0704504901c100d200782c00f1110350307940f10340402035511203800d000c00004030320a0050001d4101080c041d003046045050001303018600c01016405801032440303100000307658011401c2806154061801d442c1c50503580171110390700c5080300a190380300081400043c051007001080d01c107000f503038024005181d5007680301141c54170f034a42924000d0080c03203128440e11000b41480c01408046c42541d124000c00c2d00c817211480d1400b1412502c3d2903034503000741c0307205075a50058008201d2000039004d48001640e100b555880e0064004200c0d10100c2d08148003a846013407050020b0f40b40011071508054150508489072842e074400a0701500c0950846600300700c010050004054000c10586015003444c40f00b40b01c0c0756180803 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 831720926 1250 831719676 831719719
    0xa0e070501020c06070f02030a0203010501032d02060304030305130c1403060c090a030b070908100207031d090a0f27050f0a0503190519050d06050105090f061606090b010302 76
    0x44244d60080d01041081c0000d03542592840f4070300c1c405070a82e05009103e40004e400c45e1800d90094914941281941644114450400c41d07642d0a0950004e0064080d40224807a030000403c014145540d90000c0b4a91034402594944050340c0300c06002d000503111042400803007141c1ca00d56001c2d01c41d54000c54200d102001c260b81e0001d02c05410b950406155448946a4890281440301400390700e1700e002c500c0d14400d0040108141100c48050795030403991400501c480d4400a01c040e0785400c81003440e5940e9203c6000036000201030b070010174010070002c9014001c1c214412040e0f2011b0783d00290380002c0c0074902c420705440d40200c06a40d25121848035240c0c4901e4090740c02410342d0401c1103050700e411003511640995190700c0c5411803c000004141e82401606201c2c81404030301d0100c1c4020203035000c0d006100c043c4c8000e192140c142000704020801011101850314424180031410000c03043c0e0501d8240380c400d80000c014440c040003030070410741c200801c2c00181d004048000b0001910a2000f = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 831722176 1250 831720926 831720943
    0x6061407020d0303020912030c01051e0405070e2805010f0806070c0f060e151602010e1c1b0b060310110307030911060403061506090602030d020904020f030a0e07050102 74
    0xc0d000c00300b0700e800e40d5011402588002c00305a8000620303007004010b80010006800100000e000005650400801000c011082d00d5001c020009400d410400020004101c03c4100c7d20302902c56107158035004040c010503c0e41200c480d00700419079442d40e24505603600614101e0b88a2050318602c15141c440451300d402307088520201140e41c10f659100051010307041d0a503200d004080000d04030340085811420221840120085d2040d080180640540080ca9122045616000810600d0b40009081d03448502590300e8064003c000038851fa03605005100e011402500c080c84020300c9049482c20002a10050303e0580c0244245415242102954404c1e24144440c41c1a9241142e039402011000340110203012940c1c4049201121103d031903044c050400355204020214400c3c4211901902ca282294003105c06c00604590400026030044200d94482e9100040940e550740580b0209000e07103d103803002c220a107000820030080309080e50015032500da000d41903a002079600c1004a82d92200c0 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 831723426 1250 831722176 831722179
    0x21c0c02070b120604060905090c040c1d0607021338010801170f010e0c0909061308180a06120f1509020d0e0a030801170a0c06050a0203070c0303030606140702 70
    0x810400b812102c0d008a2181c2c0013000501c0030800644681c000d4040c0e0740e054880043c1c1da8011540c0c8841752402c3d01031160b00142c0f915104110003080310810b9100061015000d010310700000f403d0042d13440d08101608a8100e110050140c41080c00c00d0505868002031f1004400c04901d000c0719440d80c80038a0351401c010160b4910a0030390800c0005140a00401c600f1100ca1042074030400441c2c4003801030300d1500084501500908082c0c1e0140705c01c0c040002d1201c212908803070700300610440504800750640703400c07009691b00c4c0ca0032103200000c8407400c1c0072107650004001000080f01c075032040b01c1485400c0e89d600244468032020300e0200030381b41c10f550b010303105407451002444442c0c03181c0c2c0901842a003d030070100382c14058148150070080d8098042d0006640c40e0010301010280301c0c00ca0511101090082c2160811070f168581700550034010b400c10002e0000d01e0181652082048d200d41680015030001005d5903454087d0090090b40f142801052211044540e220304090544100540 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 831724676 1250 831723426 831723449
    0x201230319021e130911030112031709060103060c08070c02011101060f031109160837090605010b0c0a021c0f0b0402041107050d140d021c0c0207 64
    0x251001d501021030992058000055800c0c4010020750b0180d100f1180000c03a00f41c0e4032980c507a241030040140c4a01c0d82c2006000c0741c140700503444405445811681100c440402d0504001110324086451640c032034900625881c0e00c40900c00800703001b0610302d0499220704420030180498040c01d43d0203070380490313a03000490003c2c2c2c1c40c0809940100c104444041182c4000903202d40c44159212030303001c0a80060b92a4080c2c1280020542400c80d101500984400000014803072182001400e0000040c0102d41c00180b05000b040c03041c00301c10070503455003103101c1200a00f510344031504000b081e4051007036501780d0030900001504042d0301c00b1030345180a201e000d1700038802c0365024407060400c3c00101d07055034a00091441c002c00d002c114480c00403071203010402641c0c1854010041600d221520448005074100010030024500154040100b406420703c2441140414560b412500032904081c9605000068a140840844000d1a00300140003401c103c40100f0f0a001c99588403503000740c809195 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 831725926 1250 831724676 831724681
    0x161106040f140d030912082403070b0301030501090605061f08041a0c0a0206010b0f0d0944040e18030403120c12030e06060f040b10090302012303 64
    0xe4003481100c0826010b9003100d41c810108070b99541c98820140d5009000039a81c0c04008100611407000d0300c02c19081e441d1a400c141402c3d40b444a03203010b229a8890359100f84a402d540e00e0702d0501c00762000b403a401d1140f07034a969403400d03c1c9002c0c01c2c00a0007113403007520302070026141c1e10340402c4050380d01e0642109000c0c00d410400b025150800c019200340c8940324a800140011f41d1500c032018491000b49902903152458200f005e85000c4068110810101081c0145e02d9030300d40c500c05a550b48200c901000c07400001600306090007581188002e200c0c1442c40302008079000003811010211160b10400e003660042d100022000c1c3d0083c0e01448081031034450201d0078070904407d08200007410102075a152a650342e41e203945205c22040d800703010844c000783c40010711800581ca00404015800c007800642d042c00841a2036803401410503105501388001a031041e02e0300e070311480340c5240150501c1c11503d540d4402070304210b87ca100c102e001416414110f00c0801e0365040c1180c0100003245100d0554 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 831727176 1250 831725926 831725933
    0x30f04031e051b07030f030c0c090608030d0b010c1703060f04060302091807080f06070e0301020703090e0c0f0d0b030d17070c080c010914010e0c0d1203060f06020616110604 76
    0x1240701c0c03043c1099807107184004004141c04002d21045c02c1e00c65200c01058600ca840c082003100116844900705500d00079003006011400b1080300c11922034408009598600c000050b2114000040090403400d02d0300c01100181c1ca51100039401130758200ea40f040c1030305001080109803511400002d401419400c003042030403810288140311042140150f40c5030548520708107142008110071a011607000c0414410866080090700308040c13400e030020f40c40c000150702d010704215014883c01f42d03001401d0001501c03402c0040143c032040c80750031b000a9920190322001502600e000301100303209009000c6000244c3d4003511303540203042c442c20620704190790f4651060303e48075848842958020360401c443e01c0021000c2c800c1300d440074807640b0300c07003c1c50040c0480c00c1e08403100c2d48040409913100260b070344034643d91002c040035815882540180040d01155044000d800d0a6000940f500d0030842c01040d016004501315102d1510f58501d1000d42c01110f00032551001d130850032a603035801c22070100700071 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 831728426 1250 831727176 831727207
    0x2090405010902180a0b01090303020a0b09070b0703030618051e0406110304030c060606231806071203150302151608030112030e0d08120a0f02030f04031e05 69
    0x250103400000740d200c08940109405080b049142107000e048401000103801d150f110340f002e081c0e000c0c03901e90714070390842d078010b50740d55144107025050410210002d00480003c01c500d00c042c200e4001c0c441c0d00c5103614900940904614052500e080d48001440c68140300c03581704041c4100d042c484170701c09190881e0005610a6400f41007510480d4482d108400b4000d0305100840c0518426512403001414500300001200c415400801c200085c00300c056020000f40643d820200351107559546d540c2991007524030850300d0b1044c446130059408101c441c180900014a403484050300e1700c09114a40c0700c15029900840e103808000e5001034501c410000040143c40a01111030704504041c04110480d12030301d10390303002640588140c09a08440c3c20416a00003050b20f500d0809441d140d00303114555549600d180a1600800c0540c40368400061000c08182c111078100c11405c1d0f01159603040000c4a006041c10856003900030541d030260a807040000c00504220300342c03903030362042d0414045030050307000d = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 831729676 1250 831728426 831728431
    0xf0b030f241002100f2a0215010e0a0b03010903050a050a0201090506010e04031403071d0f09040b071d031e0a062f09010f120e1b041104120807080705060a051519030209 74
    0x4512501070541c1c0601043c00e0614081c025602041c07002d84bc1240741300050342e46920103680641d050a8004002a4015003030340c1203803025080280c7c031030b9200c00c4220b004166503040a4024451070000240d070410800c086401180a07545503200160010060102c1d0700c01682c0f1000001d42004500c807045208481c0d80561400007040b18240d008440c0005280ca5020b03902600d8038a0007105002d004c64002c1083c0c80c07010480c91810216000300320000362201130350f0580044115107480041540f000900003048120b9001004025009504500c0c10044107071f8170031001328080c0050821605803ca50035580343c1c0c0c505944000601103060000c5031560842283d050780d0540701c619941d890042408141ca480c0281c40c160144842c07441c00304810340d000034581c00c040920400092060043d185911a21203410000c015030743d0007640390038031003032141120141290280b002486801d003610740286010740e0040d14000e000400d8a4200281004110040d011010f191801040181000e45040703a = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 831730926 1250 831729676 831729761
    0x503010b0f3603120409150b07050d0305070c051e03160602070c0f12030c02060f0309011d030315010c17130f0b030f241002100f 57
    0x18104100c03110006000c40c0c64440b01c80c14105088540d094100c0c407040045103040b01180100440b00c4010030f160381e64480ea0003810380454903000c11500c1600c860048400900104040726038030202401d203a91500e282100d9900000d0800c004070381054480c5000700500d9402802824221040300c0c0103400300e09940f580080346000c2405025100c0d03212814989809000d410013613a1a4110b141190070130359a41c003c000103c555600c140000c0c07d0304007078041e102d40d250030000305400c42c80c00005c07860300400912070007050000040254012042d00145003031017411602c00108551425200c1e128001282c0c166100b198030b10281c1e03aa5071141c885562114040e1803185002409200c40345040e80c815240784003c2d2b20894802c02000d40018000d40c01000d5a00c0050300b1418010440914220090654a280c01e80c003c1c0000b0205050f07544c540c41c580001300140e400c866091006503c038801200d1070300b10186402d40301c2741403c1d036034062604000c800201680313003107420301c080b107134000198506034 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 831732176 1250 831730926 831730957
    0x81f02090d1506080f060106020a020d150504112e18030803071e0207061b02120d021b0a03021c05101a15120609090c090f0a1b0503010b 60
    0x10002c2802c1d5942c101841c412070354007084076418100f0491500c4124a4203003126401880100403030f80e40414014241541100c41401341c551504020030304442c00d1102c2840c491a04051200300180c580c9054261103081e50f402c80c401c1e00804512504034804802030000e001e100401c80f4000b0300c1003459024007076030401c1c840704271071302c80c1c5400105800c200e542c1c0d008912020320549100c49100d01c1d50003541c00318401010035071f0400100924081a4524100300c00302403542c071200f1903490300c680c0200b5030700761001c407070440c8000c5100130350310316944201c02002004104a21807a040078100e800a0701d030013814004100000ea142d50326880601c04081e078031801a1144038031a182e4501a49045d040d14050007400501032008110710b2000c24810440340314000c0200d810068850060294840012500e580055881d964800d0410703e02094259020041c001048500c07040404594000c0d51019410803045031844000d820000b030320210000861002e100411210a0146c000d2003c10080f4001 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 831733426 1250 831732176 831732199
    0xa0b03010212041203150b0a030f1d010603030f05090612040204090507032001031e111e042c0c070813030f0203011401120602070204020405150310081f0209 69
    0x10110205401da0701114824401c4103164813440d81401044890703000c1181c0c8071031061801c1a003036058440d640f002d00905459904124461031141d02c0340d5041e40c005d00c04100c1c40304440507001e000b8031700f900046010079224060070000c0b520034400d170f0742218405004103140178481c04001c6501c1400600490b4060348030040340d40043c40c28861071001350300c14036035416902011284c4c040c501e4010600c0310304151070015500c240460b10170120705080e02c80307100010301107010445147d81c1d100e641050040780888151422140a58000410495a80c00c01500402840300b00816500c0034941184828001040100d050500309000404580b4490a507242c5000c81c8107a4910b180100b82c1e0007622030070040c0c0c81600035030800b8000c0d0046d0700004506a8580d60500504003e45010518094040c680c04205d001c1152181e0341286d0180c500141820100405403925008580c411260030014211903203000442600001d1440c4010410020100180b2014001f00d4000c2d0400c10345181d00004c6002d0 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 831734676 1250 831733426 831733447
    0x31b0705011107050d0e010216031b151d06040e011e0807060c02030606030d02060c09130608210f0301140d1205250209070c141b04180b0a0b030102 65
    0x340702c0c0701d22035070140000560170359000d05446160740045e415904500da00380586010143c005040e03070350240a0203c4c4040e40038980c9894102e6400038450f0703200c002000b400c0340d40c1209000030400300d40d107031200407607a40600380301c01801180b091803000442c410040c440c4803408070089031403041e030b2034046000c0b503600c40700f01e842d000d4143c1c024000708080b20407000640c1424031103650700082c2a0001c040e00c10181000958611000b41001c210f503901050441003940c40c00c44555408034800004e10480c1e442c1c0a02e2500c50301046400f8014200d8010705a40c4207120906903810b4041803000c01e41140e01e1300100355502c400d441c0c1016403009020701e00074001640009400c01f413003c10b40d42d064072140034118031500d04004e880c0240165141103800e10060303a4101219a01220038504091400003c2c42c1031460801540c90500c100c0c001c00803d41000e20514034490031112080360248000c0c0c0040c4102a00d42c0003080004c0d003d5001100014031110060300641501c000240c0014504840c041 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 831735926 1250 831734676 831734711
    0x92012070203071e12081e06010203120a1a150904020310030206030f0703052206020c0a0c0608041a06031b22020405150a080f04030201061721031b070501 68
    0x48103101c0e0880d10404da00600100c2c9110480807201c6040889040c2820b500d0071014100241d400e00411042c8000250140d10034015604c5408030031a0308031050901a211402501c41a00e42100e0300790308a140c03800f14500080c005806940000c01c03d894502c03100c0901029510040a1500341da0000304000010380307482000314402d100344d02c3e01c2001402c007604014140c03400900100b10852250110102d4407842800d02c0491a9002a00681d03490039465458141001040302a1a050b91782030700090954114800314481c5200d2004c1208064100d000e983d82d4401c12b40317039550550f10502094003102170005a02c8490301e0010032010005040761102030383c8070406600c0b17040703840e00451304102906001801000240e021059907050400e1114010140d1400520030354003042a40041401d240c000e40c0702501821207451607640c07495101c032103603541d0001e042004c54490011001910070081c0350040e28014180d090714074180c0740500c0860703a0140c12940c4182c44655075003480401068682 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 831737176 1250 831735926 831735953
    0x31e0a05030f130b04350a08100504050106200d3c0306050f0405130305161a0712050c0405010f1806020c01021605010e06030403031409030409201207020307 69
    0xa60f01c030207004800c1c08902c51b14804000b0250501040c460300c40c0c1e031010500090b80e800101d2841c100e801503482151042c0210780310745c840780d0001d241c5400441d80e65480705c40e0401503911113030b42011043c03019400c3e42c0c0d1040b80040e40c900140442c060414149a41c0366004402814041000d5070b4415007001c40e43c100d04044e410001080c1d03100d01c100042d090a400f8a07034503d404407000c0065140500121040c3c540c001e000408116000078000f8180d041d1035101d40c64940c10804500c0c15070403140301d03600070302e100340da4660100d480415403044030314281c000c1d60f1064090381c0406007050310389401942e5142410300c1c2c6000303102e000814404c3c240400c207114402030040b58000c0100034030b54000682051010b0100c03007030072501c1c9a030510075030341c200000d0240c400045c0d4055070f4955460404400900e8605500b4070b007403400a081c09802140040500141c0d16501802c000300c41007854070349800da41601d204601c141d070522032503010300c64921200c3e9203c1800d00550746130401d0b0395100b512200a8 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 831738426 1250 831737176 831737183
    0x51e070e0a0609030804210c080a0204050a05150f1c080318061005061804181b08060a0506030a0803010f06080610020c0f040209040e031e0a05030f130b04 68
    0x400d6480303409141044101c002440da038244000c40c070b819074036000e419120b0b9028112000000c7c6140300703120440c0c00100b100d07043e0803151003810180c40c0c0c1c114a8594101a20982c03055050002061003ca0940705050042e001201490300d01d5103420203003c03030202410310706640888001012043c0080600c29140880e1240c0b00c05c560340d1030062241010f2528105140103268001802c003c05120480843e9081d80c2080312003c0e2900084520030048040036041c0b10b81107414001c907440078450071118421024440c0e5014903085410351140e04004119200e0004540e00c1000400c40605080c0d00075504500d000d030503100822070302d44a034a015403081e0700ca003c010100300c008200c5507500203a07107034110030221181d1080d090403500003940c4041d2142c005100e82401e40729500700b95a40d03411070300178080c05481444400200b004c0187c894025480348951420780d0100854010303401c0088a00700200b07516500d0650701c8042e01d00d00080301c02000344040f401a590b6042c08500040d09441c400d912 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 831739676 1250 831738426 831738437
    0xc2b080726040512040e0f280207060605060a0c06021b010501030305031f0b090112061e06020106140916020a0812090d0e06040b0a030209040f0e160e0604051e07 71
    0x9152405902c1c004c1822118071030b8000c144401d12401c1c1000348440d8000d007204010041c1c2c1d4554245480d8a502207107218204400c24024650707130125980c0140604d1805140200703d00c3e0350741d4080c0032003807041c00207034030002c2c0c1000d03500000070369540d000d4080014813036242d140141d2131072505803c403442a0000d0b030100e0b80200402c801015402d09109541c80c01001200101c1d1504034810300750300940e00824140486500f20300380309119503100340000c080c0349048180c140c0f451140740c1244c1030b0302c1c0104401035003030410101d640d210f1240e0002074101c000d0400c0c101941d40b00d014a03001c1051000602c1180180c25001001c24064406856580201c07100e201c42800d100d03000c0e601e090090608a41446959609002165500800c0c0d50071103a411030340035620202c900c3c045000340308010509900c503262082500404241e035200c085e0041c8040120358050000102c1c041d004420307403080d4804040030b0400590700d030034541c100d41d8010380312001c0c400100e02d5a00301440640c00031503101f00001ea = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 831740926 1250 831739676 831739681
    0x20d020a21060b040e090f01090c0f0f050f150403080406170703051303030203090115090f0506120c010e040204050d060504020312070507121e0303020c2b080726 71
    0x50094000c56800580312070100001850100a280a800386100e11140043c40e0000695201428041c101300303040c404008200240e00d45ca1b00c11202201d80c0500c0b0b48100e286070b03001c1a001400b1204005a440007001018040d07120003c0180201202d491000f500b0000d200c00030014000e000070b03001610058441c0e051108000d011000c040c4801407a49003014181020302921480400864a5090300740c500581d130395640704802400b400469001d1202c8078059080014120318950081e0b10343c030f20440090159846c0c00d41003104a170003961008460380c11409000c0d00075809401c03902c0d000800500054141952071000030300009850800f600e41d1a100c1c0104411403806000c00485c0c59072400d106030030710555403070b5076641c1e0040b030190903100d030060b000e07040070b00410902c43c28a0640c112460400e080f05880d00402035000005448100d200320142c1d1a00d10400122440403002c44070f108041140c3c00403c00c948040000d8003030014461554102203011001c1d0515204008200600c0030031030 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 831742176 1250 831740926 831740957
    0x80106090b040212070c050c0d060e0d0f0212070c050604090f1b0e04090804030209161e17070e1f02060a0501120227240103200706020d020a 62
    0x3035065a4560340b05510400802d81e00c0012444455008100351809240d101820b107030003441c0001e40b02071f2541c03054100b107001081203c190020452025960143d90f42c840c40c503c01a65030031600c040c0d03a00075070440340d035040204c000300c8041c00c01e0718091180c25413210340d280e012800e164416007000c001070b0f40303c1c0c0034130718114950b006040044030102d100104002c1600f00091645420300885031185483e4442142400000030a89004e160024140d03030940c244003003061400c4840c030030403c01080c0c80b15444c5032a11402c04581c8080000703901c0741040c5400d1400810440c6500a004009000303c0d6a980c50b02e68a84c0100c00c2480030010803d15050300c401c1c080a460441c0041c46030f000e0b030b0b040100510001e000324a100e8078140c0d055405205008000249411003285c0c503504002032418001041203510101d0b0511000c960b00440030703205842004011002d40300c070180000711054508546d618401c0b002c000624442c0d009503001400c00c2041000135090303138080403003c0c0010303a1078110103544 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 831743426 1250 831742176 831742181
    0x20d081e041e0509150310060608040c2702071e0c0620100c021504080d0c020606210c0409050705011803030f14070503070f12030c0815180108010609 66
    0x80003602c107000d8a6403800d400203e02c0480104212031603061041407070041e440401000c8201c0e0304524080c0a441d440310b038020701d9640308a4042ea40540d41d0000040c1104d0344144002d504804115018094110041d440c03000e5488241c0c100c0b004450900114500c05171001000700251045561115061030208000d1002c2a8034241c5e54050794a40c4032144490360015412620440c1000e0120302610100300c142e05003000004603160003202582000b04010043c40200010701842d5420001c0642d2130208903901d600c21030b15a604560703006180644130b5185480d124003408039408407099490030360082000d54210400031500740d40f154030700b07001a43c1c00c1010090b030314051100000c0d00394030f03549000300448603800340c0c003007030020304a0300b0144103185a003111002500201125074995403850b00d103c110003040002c1d2440400c80b8a400d070464402d0003100d041103000d42d10380100d0b840e14248801420002c6618540c001c024500240600c401110800d00030540c3ca0000100d240c1340c950b02605 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 831744676 1250 831743426 831743459
    0x6090a0b010f060219030212030a020c161815080111030a050121150f0615020c0901080a03120902030a0308011d102d1401110307050a020d081e04 64
    0x92402c40c000700b40301c1c0c140d00003a20148554260000283d1004500f010f030b09020541d44089484440001006010582c2c0d400504070000e003402201d0511030b50b202030413121041806900c40812816560b00440d140e26007040400800700c40950142c00c0e03454a94908507000f00004202e1100301104005c055031891282e580186105000d0000114143c401108079441d003003001012460300f682d10440340c50040d0302941000d158000c04004403911151042d00c010b440c00f20f9640103114021840c141424612403c41c12680c4480042401915565003507442d076840b0280d02d040c0c2a5289416009a1703800c01607400d099010f0346a40b220f03175050005800101802c41c1910200e007040b0307018040c242c1442c0c0e04403002c40f05112211040b200020140580c80c003c5411fa40d24001e000d030a0104600c40c40d40c13a00c0d82c0e100800d0f29000c00034180481d01c15124018994007400a030403600142c00941040d00021182e41c2c8074000c1030f454901072980b038480001148404188224000c601400303078500c413445100 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 831745926 1250 831744676 831744689
    0xb0307050d121b02030d08040b070f020d03020a050d1d07120308071d0a0308030619140d0c080105071d0405040b1b042d121e110306090a0b01 62
    0x1d4541110703214240410812111141000418039410688800340d54040501c1039000f001d6400300c0c495084003c1c400c0000751410341303001001e0404a0361440c0a00811100d4100540282c00c04890b0700c44150025007002e000501404020403540d440520603104881034551610301892103d20414041850260550441e1440380c03a01c1b11080042a04448410fa101d041d034903040c3e544050b03402001c2610018880025004540b01001004101200d00038502ca01015030340d0b000d8180b003920180180150b6803069207954400c0030f410003090b04282c2c0c07007001114020ba45407004580e5898040e401c4a1302140d07a0000511a54142c0032400d40380d13940d9032402c46040310144051308083e11042c050301d40281c403000d01c040c654800c0c018059032070800c0e00c1c028401c920b03081f01e025060050741c1040e0b85101d1004841d021202030b01045a06446010100164100007000e040c030812a400740310800b581d00c42615a1090f1005005255404000304d5104000481c0602005001031070004010001a000b06 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 831747176 1250 831745926 831745939
    0xe060a0e120a1704110414040b0705161e0f15060f0b030a0e1f0b1f020709050903070204230a0b1014070b011203020f011404031808060a0b030705 64
    0x5800d0348a50030300f003403542d24080c043c4952030380c0c50411074801020403c03541050030140e0800400701d020341c040303100c0d602a1110b4100c954814000712010320031204082888404409501c010030710b40f81c0c55076040251456445031130001c81c2c5a0381c0d203036030b031401c4e08030788d0014880d100304490541409a800206030b01e5541c10661410700380d141500380401880e800c2900d0ba208621070840c1010484031016030802e04107000d12590b0502c120014000200c16540118080144080301002c01d9151020644280e4041e002c094280101080175000141c1400300301e1005000c0b03600940c1d668030944800f400d81c0107409403c0201079501c2900010000c004080c6140390003c50040e5880350340761404204900c0c40e04088024040001100701d000f6070002400c1c1d2807201c40041640f0b10380c4200c040d5424081d4080b40d07550b08034280c00030700b031300e400c0420428401080004140001c0c058030180051841880811201070740741e00080b4600407007203a103011040d844024011050505010003006008180c0c0c03003 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 831748426 1250 831747176 831747187
    0x607092405070302120c01290907140d060906061b050303161b080912010207020307030b180610170f06010b0702030f060f180c0102070b0d0e060a0e12 66
    0x900244400344065062000008108041610a1091003100d110b01040180c60780342c6403400314000e02044004000c603107400d06500d14000380c0099000c28032480200780350000d0765003250446150300800c254240c026814040706110131800e010302c101508000c4400200c2ca03141c518004c14111841c4100300030780000c100914003041d00841100e0380514071702054a16041b002c1012104c4c03e02803161943c9041c0200303248810000120700810302440202c80d0300c0c00c252401071405080f4411000f0096240c3c0c8009810070008141d41c0b08203a01500c0001184070410700d860440c3d04140d0110307100c1e2200180880240300484003000407a03404203044c40200700d0501100d4034075940740c0381130081d001c0b0324401045106c00c6540c20002140444640801e0322582c0c140b5100805180748140c0c2c00040f071442001e03000500d0080090f8000b00984141d00500f070f0300f450200035038942d900c5103400c0e0120685400307407941c0c120300402c0312038010b0310442800902d0617400710b42213081008800c84a40d00d070f44104407 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 831749676 1250 831748426 831748469
    0xa05061c0b0a2013080d140901030903050c240c040b1c0219020607140c0a140f01110c0f0c0a2106090819080603030a03090501090203060108060709 65
    0x1482d60050041a00160f607000000c1128441e01c001ea40744480d064001034243c10429100c0c1e002c604581000b1304581d1018100c407019a81a144003904071110751080c00790b0242580710350030840540e402810007500d04624444824203025107034200f220390721020f4490780d40c0c52003103004141d406040340d201c250900d4209648549076205d60035007500710300c0305108080501d6556904445440c0d280021b00d4480e1705442e00b01a407507030710071500e803800324030440d101d040442c1364201140d402072443c902130201c1160541c4c039500c0d00d078441851440c291181c01d20400400c0750920540c8440740c00a0545612000d8080070b980c41c01c43c44d10402520b9400582101046841d4694001c003034803503a03400321311900000e1a4040d8120354040c009030800381442401420700101400a09035800e1100e02c80840030030401041d41c88190503251550035510400c556620140700e5488080d03c0c0348035000104404c0309513000a482c0074001e801091640d004807091102c81078019480e8001009041d912090701408840c = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 831750926 1250 831749676 831749693
    0x130902040b13140c0906122d0907060f2c03030a02101d070b0f071203020301060e04090804060309020a05060a02012a0203030601260a020405040c020105130206210a05061c 75
    0x5050010750000800030030060f012203c0410450303000a00301d640c403503070000301032301040c01d058403940141c0c0600007001c2034442c851400c0014298054a41d001c8030103842401100301c18411a6141c680014481001240d607402c0c00101441c2000303600070700310f07a400a0840c1003241d1008803056010030800c55000e01c508800308041084071080c034142611100c500c80c0c240000c0c412804020480c002e280e0711101c18942580c003450584407113030384001b001c0100c10144400c0300c800420203801d6540c1808104040ba1103a0483c50400d4405000c11101e00d40c0d40c800b03d081600214103d0001d81d4492941b0300b2105501c0c15020390030041f400c40ca541e0f00c0200c0101a490b4030016107807030b0410102d25801503d60300e81e800d8180700d9500106440030b0310302d81840d4800094100c0c2c024a40300d5800c040c003450409205000300c9000e0000c2b02c8801c1801d0030b8a0f0b080001c254805965031541d0003001600002c1c0c5150350010510a0b1200b46021416140182c10002d00b0750f183c178141481da207a13101c0b500780800c6840 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 831752176 1250 831750926 831750937
    0x1a0906010318060203011509050102010e12090d020a080606180c04060f03140f041b081f0603080a05031b1c0c14040902040305010c02030306130902040b13140c0906 72
    0x303080009491601203114440b200501d00301034116800000001240c4004c0b2600c038610000d55a24808102e07282d000486c01c1c0c4207494200700e03450b4800306020361817003809001420000c000505030107184034658081360310f2000c0c03070b07004200540140d01004000d040420818200129102c0f600f485031600c005442c0641c012030096104001956484514250081e0f1041400d808248402d03041442c06502448804c6021901110b11030882032040d416040d4066002d03081d03480c8100a01180c1040d0094010007900640c410007115468500001c00304185c0401001801c01c1940d03042da90380703030401011000c68030544ca0320f04829400c00888260385034551046691506031600410f501002800c00c8034580c90395509070900b0440000d000500c6a0150b000b4801ca92060b4000c0c0410791138003c00f640c40740000c903a01a004060381e2071418013020f45038003000c001d910090001601081b8800414089880c0c6a410008107030350300400c5000008000045510000311151340f0701d44003610f404520b540c041c0 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 831753426 1250 831752176 831752179
    0x10c0507021806040906141506041203050310090c0507031805010903060b030c030f0309040501050a05030a0f06020f18041503080f1605061f0806040b0f0606070c06050d1a0906 77
    0x980000c03a4044d543e81d00f1860045421032001e101d0241c004103092803d074402c0c0c0c2e1507007034040030a8201c540c41c1400c405407004c84080b04240c05546003d030701c00740d449610080940640c0c003800c160119086171944a10300c0321f141d01c0e0780d4503900c400b10f0b480c02801012070f1030020603405004801c01c111076a44031548006a075440540070404112000103e440d00c0c00d840c080b00e50501541ca100b40d0604400405007244500480c0c06001c541d03030b11020310075805c3e000e0040c180c0541011050704045203203070700040cbd03003076200b150018907102c405504440c407070f00b01c0840074540401541003040186440c0c002c0303c44600002401c1c0240c580f645e61011828842ca00500314210000f0441b054080020a1003009040e0400191086440d0940c0003c15602841c41c04020700d41200b000824982000100d80d0b104030b910940d054460f8a96040807081131500034107465022100b000f04600040400111000a20742c51300c59a4a504201d00040185c4010500c0e50a41070b4109000da2101d41c2c40c0f00344560003880 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 831754676 1250 831753426 831753469
    0x210f0d0b01020c0d051f051b03090a1b09050903190f050903060a0e06010e040f061a0d15050112020a030b04030c240501091407030c02100f0e010c050702 67
    0x8000d00181d040c024007010440d8481012189142803010100b101841c200186000c0d120040900840d2800c540098824448081c002c420091507419101c0041da0070021107002c6a2010f40542c1d42c001c80e5076051100a620b1030040d400c00c000041d80d5020701c64009a1174400795050100845405002c80c0922405808004084080d00b01540c0110126080840c000d420b4800a2402c902d0b108041c01603104c2081041c8264030002514144107481613000740c3d800707113214000030941d49030302001e800c0103803040c040c0c6103244184078015503c0104c11101c1500c6900d02c6a2840c0943c00a50110748050740401c00a00e01a40100e0042c0d039009100ca0903640c0c032400081c40c80d01e41d42000c8442405640000300b81c003550f5018603104103141c0080b00c0704e400c1006000c1c041ca03070720b8200741025503c08284500e06114600e000c03034407081c02500b01055103800e82c81140e00114050351982d0030790384c814201d14409503580a034550300030402e00038a59038509038207107540b4140113070b80411000e0a15200f02c1d085071a = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 831755926 1250 831754676 831754691
    0xc020f06041a0403021206010503030a080c090406080f0c030f0a0326040f0b070203070f0818040c030c110304060507030f1209060608010b010c021e060d020c210f0d 72
    0x955500a071009080b074451014001090070150720280d40c00f502099200e5884400c000003001c0300018040e050b82c802030041c5090540c80e50050b070301800301522017112030f04140110030181d222441180003c2c0b28180050401c0c0c0e400540e02410724103150742960094114400380c11800d14001210302c101c80c0c0c545441d0100c00400074040501001103044007542d0b00c0c4580a210500200884c1006405c0c0500282403071a01c803010181d0340ca21800340001c003599042c2c95003e002c1490080941800310390b01c19140da40681002c00102181c1714110700f400031a039510200c0c22096444007031038031f040c2041c2d4021890700c0d01b0310102400e94094500028108650302c450940843e20070f16401e68007110900c002e01c10305c4041e00c1c00c2c802134070480c0100c0a20b1341c030780355048203c0c0d071183c0004099590041c2440032454489046800300c010300622050300003004000154912841d840203160010f03840c00500741100d0baa44d040d0180844032a407180c42000c0a122103402001404103c40d03c52214400008800c0d = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 831757176 1250 831755926 831755929
    0xa060303080711030909041109150d0f0809040f020c011107050c0f01021e1c0804020d020103020a1413050a0b070804260d02070503010501121a04020103060b0f19050403030c020f 78
    0x188118561700307402c031000c0b02c01c0c401048a003075100c84d14106e040710f00741e50b40d83e5840d60302072081580003503841d0b0001d0011240c0c8085002c54220500c114010102e82d8508003030500804c003604c1428040002540d40041c01040058082c8290042d0307800e20004186418490348885954280a24074680f050344081051400c682c020004800501e13000c0072040d54131110003032416214181401402601c0004001440c02a440354844610559008060295000581d00110000e4001d40e200340144180010144140300280c40078150300e01d2549502080c135407d01d0144020341550760b00558820a040c0408000101c05000381c2e020b95212404144002c100008200e00812401d202040c044c012980c081054a90126090003612010f400070702141c3d07039400e01c502c04181c1c0490090025140b00c4c01080c030008000b005140c1040c0140b402140c55621000014815404400c0710042c0c07505c001502c1c1e054040e84881c11008900f203007002c0e410315180d0340700940030f05402d40e00280308201c00341c4061240d = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 831758426 1250 831757176 831757183
    0x10320901061206020903100c02031902031614190323210f15030a061a0a12050105010e10271a09010801061d100510050d050a060303080711 61
    0x602c955080214070b0405410120001d501c201c1306a402409404c0381c078100c0b5403480c06648a40f480c640c2c029440c152040b50412400009100f8490450004201c280200301403000003e0105003d25020541226088420381c03a22500d404480b0107840c5510b201c04c0440d0300400c5000044000c4655901f01004095013000d080c07181c1c2968a68000800340749020142ca00c6400500c5140c801e2007444035501d40155100d004042640103661582c0700c4144040000d850b6040380c428a224024520101e03100400001c1509620b50028940c000e01c9413418004d000f07003400342c0d600400c4c500c0f802e488503081c024965250340c00d00c0e00843d0b5101d000103410141e01013005888007002004588100709500c950039541000003d1020614459192240007003024070041c415402107481092910140e00d02119140750340071030040880390403154001001406403140c0105203120403541d034400740d841c01031003440b42c101e40300600b900005034074212007070000030b0701310380100c1d000219404c00c02003103900030180515 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 831759676 1250 831758426 831758429
    0x20c2101091406070c020913140607030c090b030c0d0c020c1f170c1605070b0c0705131401061404082a0315011e090e1032090106 57
    0x8980d881c280035a001c0c00401107588049151003002c2d00d1050322035101c200c43c46034074484043d40c000381c8039002ca001182a001c1000364140300780c0d1051000b07200d00140c0d5082410071560f002c0429290090142510740c40b6071a0005000250406420360a204040550b50300440503160302d450307540d000d5004054020001d21000d220300408404102800500181d00031000e1504400469484d8151001465401c0f182c0381c883c1181d10399250500c01064070240c054804450151504d000d82c07040440d5920b1480020316000b40b2190040108a140c4002c1c00006510500b02c2c1c0d00603890020003504600d0306020150441d40e462507d1520121050000c0c20a8070a0780d00c000c007240f1422854916060400704d2006458005e955501ca44406140505442c1c0848101e00c0d40000c1401c0b0051010388440b0b289280c4c100c405100e00c40895840340d00c03040450710240e61aa12507442030180d05012071940c010016040540d5400415108080309040c0031003503035a60b1a060b501c0e00c0c80024404210940c031000 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 831760926 1250 831759676 831759739
    0x121201410d050d12060b0d051513090308060603090d110705100207050301050a110415031b080f06031f050a0b060406120f0212191b2d020c 61
    0x441c0300c00c9482d0141d40c807000d8500d1600410b01c80800a0b400109a1040000b26084a12180d180c1100300040100410004100f001541440c80d444210740d10b500040380f446408010000800c040c250401821085d4020142e62050300e04104001054802084c8c1c0314810205003001094410381d400c2d22130130503000e5000150000c40b9640044441c580c0040c2c050120345003a402009607482d0181c0c22410b5402c100b902103101031041100308440003056507100e16034005868001890142c0c00501e440d074055030154440010160b034240f000d0002e0107e001030300103900f200101482c001d06c3c21038210b000190705254914654510010b03030321824981012a0704a0002c1125990702d445010192000300044404c4c203c4500c0d01c254200320039207910840c2d0080300c11504103e00ea907142c40d50200d05c59406c2c515034034210b881d0700303801c0400041c100039983c0c40300c503544441c0c841081c8640b1512000d901680c0a07508006104a01900c994010420091214055410304908507440240411000c18800e420 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 831762176 1250 831760926 831760939
    0xb03031611030f0f031308010213060f02010f050a060512011e0b06070803010303020106260307080703050d060306060602010c050414010c02060c0d0305061503041505060f0312120141 80
    0x5072a0480040006c051443d180740105000c2502c810100c0d00301d010340f05400c00105204581485507901502c400002c2010b20b10000c01c1e100c1c00300d003504c800d840060321185a0b960b243c010500ac0c5180410340c050300b080004008200c04013140d58801e0305d1b0309c010f90031711803040d030780ea4021301c01c5803034003021a480300c1d070450120b6540b07503520f150090083c004c521038482000300d120901406210540c0b201602014428029810030305d45840b0340c00d01d03a00135013048050042c02c06c040c00781c1d403a0601401000750b000d040300007501c51401c0000307030a41e4092421201080804c11080c41803441c1c1254039400d2000178a0300a840e0821440801d050340303d80300c049813240c0300707d44003200390710ba045d002244224401d0b165520b0305841405d08513814081a02c005015401920388802d184940d036010f542d01c0900140300d110750b4000310300440d09000c14009910100c15000440000071012101c0b0036004014529400400340481c41c040e01042c8e04294a5070403c002180d0b003213000031010007149007508402000c0 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 831763426 1250 831762176 831762193
    0xc040e190c092318010b06120a0e0304060c20100e1e0d23030d060302180702031b0313080703111203030c030408040906140109060306180b0a030605190b03031611030f 73
    0x340301c0812082700d100101504206144500c10004015179007141e62540342d98104940030741c3d50450190403003c0910500d40c5183d40c0c15150303030720f010a401c075034001a11002c00249403401409180060802648003a03155003200e403495446954046541513000600650084505c80c0300c00e810860010141005100c00b20f1402d0300000240d100c3d900320780c0300700c80d803004900010712840f81d002c102b2125040517030400d0003548000c001d100c4201910203911001e583c50140f408144030883c91290300140e0300741d030040c0c105104000c0f0311302e41c40b90302e004100c403850b200c240003103c00f66403803000901c00000030b54080080350400c160384c01590301400b9101002c0c0601500c401804400125200280340051900e10300002c0380d50092003450241c4500c1400d200c00c818420f0503000c0035080318103030a81c10903c2020000007180461007403d0080d4148401305031420702c0c10b9804000e84508141c1c503417003038000b001401071820343c201d544625580d00050b00d2030b1115822001078103100e0f12030007101150164196 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 831764676 1250 831763426 831763447
    0x40b060d0e06180a030e040e0a0c080706110f190f02030601062a050c010e03211c0608030913020c0d05130608090c040e190c092318010b06 61
    0x524901c07801041d54480f10850509507541e90701c2ca1008406008101d10002e2403840c1e00f0150490a0041207141c12242104526500d070140103601e40c3c44541e2030b80005400b40714084c0c0c010041c21040090800401c05086111806a1030701b9000d01800300401e4012040020801c0368104196240e800406030354070b40d0703500c0c180500040700070101165001002030b843e82a214000010880c11500200281080d107507134001541c00741210000268184074212802c50703021101000709240d0480c401560b5107680c0003203070a1072107603024010800500d05101003030024840c00070589002040480b4480100025078842c24000d126403181c403130352030045d04841c0340c9641e0000000c0010f000701100070300c8096640e0204462002040d24195496000182c24100a04e425048034400f02c140030b0039a041c0075940d400c84001e1152000088590788103c12041281c08161320442103082d200094100030284480c0c5d580c08000c0004000c030034814240c410100d6150401d5201c00d0304014098585a0b59070a0b122 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 831765926 1250 831764676 831764683
    0x1808010623040203160f0e06031008120c03030a0209130213240518030f150601020105162f01020d0203041104060b121b07060207120e0a05040b060d0e 66
    0x80e0701e801c49a4024480c08120b0401c1d2007102d1261034983c03c40d884404401c00d0858220381d0000d40b100406c51101e046d043c8645d50314004601800c603101c20401c6091a108415003040f800d0600520300207801e1001080300c0030040100ea50103d02d001d0010f9856560400040045980b520b1441d405440414810a00d09424074048241c0340300c1d80344100c05420090030036014002a822800c001343c01031024510500820120345008500201171b103c1c3c1d07203900c42000f03142c54a484402021000d040013880955602031007013a0300174001f041601e08a1100480c00f8014501155003090035810f820380d40031003084811b1a2143d204c0c1500c009660301c401030000c00019400a440503114032010303604642c100c0c174080c850141164019a01d96040c60f05041c807419903c08004c0c904682c0f20f450f48605114400b42c0c07002800310a10400005842e07013500c3c1403540014991003001c00600408462096260340d9184045040f140101e8020503030f25940404a0040d004000b00c00080a0030302803404624400030 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 831767176 1250 831765926 831765959
    0x30905071703090f0604080a060f061e060f0507020117070201060801020313060b060301050a291c0b010309170a02010e01020f22030305030c07141f0b030f0d18080106 73
    0x482d113100d0340501950070400b0f10321a902c10030f1011380c44608504000350a5030080e14229245e800d000800d80e0b5116003141310801c04104540c060041034509004003500040c00b080b00c0c0348186041e50906125900107048040300541225a8004090010398103038800d40010014004100080d5103d0600001e444c400307044900d001c0b0703110343c148500d001d50381c1050000d40741203400081801c00c0c100c1c648981e2040ea484202d5902c0e411118680d41030041d04c02c24002008010041429210340c5091409500f08403000c0c1c0180e141003604001c440d00221346c403040603031860000c00700e09030390300c402611080e03005200350b50400c080c03075002040300a010741c0c844014110a000701110120b0390b40e8203044c9910001c0d124040140850310620204104101d2074010301250b902c40c66440ca040c1e0580c42c074251800b203c1c0d0900100641040c1c10403508245240294550b00d4416001050007200b12014203890f103662038441c8040003008000700c00300a460f91101401400360034000c004441d2184141c0d03107031454a = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 831768426 1250 831767176 831767179
    0x31b0c12010516180e040312060b120618040602090a170f1c0c030c030c020d0f12030902010509060c070f0f090b06041409190609020301080c03060f040303090507170309 74
    0x1180c500c42c4116024012134000034038903c0c8105a02814060181201c900c05402682003010440640580182500ca140042d2200b90492522080800d006098120b00142000c1c040c2044461280c0c507440c0c8504c05540007a84400c02607240c18a04000c41e80e6801d8aa0043d0401450030680e071319140e5001c40c84003623003c0e4003010703030f0402100b070301c8207171049888803042c28001b803020346484021a22980780200340c07034460316103540c0382c1c8440d40005240c1d01002400783c540c0c0e05000544020800280071390031a07070303210341410700c140701182c0c001905c240100800c4502450700001c03002101d030806d0003440c01500082000d5000c40343c0b03a03241900c04c0c602c18002c400e01c2c1440c0546c5500c01e8500803069800b202c005d007010200462011041c0088008042c008080c610207050042c10000c00c80e014100281100c00d40044e107a41c0344c0750700e50b450080404101030081d00004d00b44120000041c825542c000d415003001b040d401039503d0686e2425107150f12440030200b2401000420001c048003c0400c002d0 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 831769676 1250 831768426 831768451
    0x60703020c0309091f03230c010206150105040b0309030c0f1b010e03190813060305060d0807110306011203090b0a050412112d0108090d120b03010f09120809031b0c120105 75
    0x11f030108465031301c1c9040007030540581d20010000f1800352210461400303152040c540b0900381681c0e400c0383e405941080d540c0341c2c000e4101045803c0d40d4001001100401e03100340c0024250010301202500a03a11a011194104402c81e156200191000c0000c1d02c841c416003100341300140c02604181b02560003142e600302844ca03603004001100f610a000d16809100001c00100c0348804e165245038440d40143c10494504016030400b190310355083c44994020520b4001c080301c01d200301d01c3d0040100c980c5422201003000c080c44403d11195021042d5800d59150511400c40200c050070692410011100101d03030081e0380449458000100d015410917280d01c440500200240c40380040d90724800460326448164400b40100141501c1810300c40c1d62092408800101c29000c0f002190a4891900c1a854550307203071305400f010440e150002102c0f99485140c0f003c01c42c20502c40b0641c4038810300c1c000380c01a685542c0c0f4102d070101e06000e0600010300041c0031032685070b07094403001e010340422120f00ca101078 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 831770926 1250 831769676 831769733
    0x30201060f090b1c1e0506011a030f06100507080708040f060201180809190902031806070c0f020f0612010f05040903091e0f0314060703020c0309091f03 67
    0x25450b00500000b0200100040069490140660310b09044c480707082c1c0d00c558081410503008121440c40048150107034001e422190f04044081e4a1078885041542006c14200308020014041d03840b0603400910454001403080c0d480c0d00b0407180360064400252041c800000c00c002040100d070010f1045860074004414215580c110607800c0b0303500d801021007404800050400010f20b40f8008000304c0c00001c010040b80c40907441c60400c0c00c1025040041c07044d5000041c03103800d418a030555040d040b0300341c0003480356140501e0300505d441542213000380340015003801c2c4021542c42d48001c0b4490100074100c192514200024810182c60a1140b91031914a004000c52241054002c140e4002d0b01515410010b901c2d004c0080f02081c50f1202c515900c0c00b40c0e030340108140c50b070001040000c5005801070300c0001514070301d20b410100c000e80b107030b010700d403040040d84503000d404025071711101e000315541e0341190ba9184002c03c0f00e1a2414004040c84c660b010040f0820141e0345611400b030049401c5450581c = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 831772176 1250 831770926 831770939
    0xf0d0504050c04060302030d03050907090e0a0507050307060c0b041502030703020d0f060b1803010207080a090303110d0804030809160909050c15161104060f05010e0406060534030201060f 82
    0x310384d2400065010307013000710300010042c000c0d0440c3d60800350080869020359592841c0c002298001d00b1102d0703c07504180084014843c2c10400d00029102c21800340200074503022019140d100400c800825202c401000101400200b0088454410000300306540c0c03445c000c02c2c002c00035480b070b6054940f6a0302e00300618140340e5052103400107488009800c646060406010000c122a1001e0426415034081101800041080300503041e03101c0760340c464180450541c0390190151760805400c001e5076202c6112510b42d540d010340381c02d40150301414502c00e5030301c0352610542440015010781035440300000c000140c2d005940d00c11000b06014034160385200c11888100404201e940029a91902050010751181e20404000d072000c98441c20180003450394110109064800c19803198202d8040a001006076582221a40b02c1d0090129020042c09080000180482c02103d4001030003030213404400c17418540604008118440051383d8941410440c58003c0c0a031546006514007c0103030074000405 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 831773426 1250 831772176 831772181
    0x201031b02030a0507050705031005060907081909060b190f05040623060409090606050114030402030a030807050714011a03071d070302071509020405061c080a050f0d0504050c04 78
    0x180e5075805180b400d08400030889003a00224130a81ea10b00520343c0000d60381e60708004041c1211102c10000c102031902d2010010500d400130b00d00400d0006c0130080050341440c940f010007910b00068800a004855410990b006102312400f00e90000c1c80411103184a686408003801114107495404000c9601e5000b44001d07601248a6201d840c07211840259540c007011401c0c0c1503100001d0b0140f81415580c281010a0303414070f0202380e0301543d40c0c01c818000703540d00c002840b5901c900862281e00d10708103a40481c2d600c903400d00000e41048030490200f00101e120383e044800070754021800300c42c062100d000250003001c2d80c1120302a00e80c040c10150801d0304000c10948115548000500e0044803401d01814a0f400020860010190300b000b07410000740e421045144480801c0780001200039403841844110b6101800c03892061518140c1416030041131741060017041d07400744502d03440b071010600c25150b0f8044d00d64403420003400400e03465042c100c41d600c45442a4040c40841d020760755000144001c = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 831774676 1250 831773426 831773471
    0x8010903080a020d18060b10080103020f0f03030c0a0606090c09030f0b0606130e07090f0b0f0d11032d0f011509050a0803090a090b030601050907090e0c07020103 71
    0x460110300c00203425041c250f010b00402c606404010a1148000030268411300c3c450008466503951001075101d6424041c2580b502c40351a41800340ca254116000150102d09030202c0520440303814032010031586003802501c1d1307d1480e204c1154084030140c980f20340601407030f024400080c6d2034440d125500e03d10400d00081104d400100000a1710582c1d00c6020008000402c0385800c4041001b29840c030f010b4191540000341282e0104002c94200688002c150f40002da1040c19407801014003480180d400340b0445260400401d20299506e10381906540500079801e1994010300b03010040210b206550111034140b0f441a51401ca81c40e03101d08074083c6400c2c42952141c0700404448014003004c031001000d04040d00071341c1003034264130340c0c1d0303100180070740c1a5030b0091403054001003602c0129060680051003d03110b292414440c1c80c0d14400030035551031051096511407020100460440c60003440d000024040d102c1014100345051294848103a001000480c0000c1c0342c0035000384e801440885604 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 831775926 1250 831774676 831774683
    0x12050912030f1806010b0304060b0a0501050a1d040221070f0207050d08071401201e03040206160605071103120103021012051915060507020415030f1b080109 69
    0x141035403520400c2d80702003000140740e0740e0015401480d089440100b002980c0c02040840822603491500d46081c0c000d03605610034990040c0384d040300030700c403607a0807009862401c1c0143c500826500b0b0400c802c1c0745200c14990110340c00900c001002118800d110720607458405001242000c2c070346400c901150030301d02d051030080050700501020f1002d0f1900d08010300f60940281e01a608089064441030943d81251044107001e83d5102010b82c402c0300d010350740c01e19140c498044281030240d0b103101802c40c2e0506400402100e100040060215070310042910240c010007a15600e80a43c1c910740fa00003480140c940a0100b21200f04141c90404000100c41030007d0500c5038116903403840c2c0c01d004202011441e1002403005c1200e00c030303030300003060b10a0500c2440c1011340700c9010722a02d00864111484400403400c00781304081c0a0190907006000c61b60f145905031000200b0722060301400320340000c1a0802400e20542e8a00032044c8505030490a000e0911004003400403603481601c14229001e00380002d = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 831777176 1250 831775926 831775963
    0x142706040305030604020a0e060309070e090c061c1107060c120608100914030a08040c05060307080106110304030f0510150f03030c050109140d0201390c020a06120509 73
    0x44e11818546c0182c808214141000300042613440c1c00070741e03603401c02c0b640c1c3e1280750300c910001c00c14541e001c28115001700c004070160160301e181e0b8011604610945880c03800c640807000fa0030900c5155944200c2e2005030340340200b03485240b941743c02405408080c494000099400c400c1d2000c0118a1040c0012242c20380e00400422860840b1000a000e0070001640c491115101801c0380b184140003d261102c8182e51b81d5038039140610700b8100010107604910301070013080c000c0000f0680c014180d01c1c191174060030201c60008203074030f02d0383ca5849280c10082000d10010f8500c0c041120005006903503404d0800144440d80161a140000c0040c0b440740d1240140011380c1040801c1c0299413050501e8050b80c0081000c2455450311030121380b01614056240c2c6c0108841c09040d0b5081c8a41903651080d400e002424000341c0c101440c85130702c41032810800b141c1c10700454109074010107050803400e9010348212140d9640d644013810311031021920148203820400059407000001c24420404080c01092 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 831778426 1250 831777176 831777181
    0x1005070302090d140a0605150406080a051e030c121c1119090b0a0804120e030705060f22061211070305160f050d110c01140a0314270604030503 63
    0x1801407241955115500f0741c0200400305c00481c99030300505100361400188044500383c4441031208403022548424410f410014040d0002003000c0f4080401841403081d50b802c2c41c40440f44c00b4114425081e20045522403e00c0703021034600340304050106960540907080c2045070b0180c40300c0903901005200c44c1101c8003081039080e1440204298a43e1141e285499107980e03031141c0c04416260b020b0300034070010500b2002000100030942c054440f85109901c3e00400980c0d048003c41d54405190051b680b00c1c002c046010f40350000074100352007624811128140f00312940741c02841658140e80a44e40000390201e0010445280705d000c0c66402103007114501e480e006454500b1a00303900060200d40c42c801d0035000c104081848022400160350250010b010254103c42019004034040c1080c8070b241d80001074a80196a044045000130780d070362614071a65800ca03600100d008000400740d04820145d60303014041a051409140350140d03608859040801400c140c102e6500c1d031040b0380003000200b04000 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 831779676 1250 831778426 831778433
    0x80c1c090e15220b06041820040b0315130518070305030909072006150a05031f180b0405060a0204150c1b060521010b16110a03051005070302090d 64
    0xf4a0b011840d070348034000452060700c900046803548298403600c0400400300740ca07005004544190308606850428200e542a44112828801d010314840c540a0b0440807000480c010544101c40400d00340050114030700c3c4640915180040400b59400001042141504c2040d610000341c00019203420000440c00c040e001e1080000c07084004010000300710806c04845201c00c12a541c110703c0c41034410280400c0e01d80b080c5001c1405d4034a400350b905c1183c1e40c80c0100044c1e10080780c056084100100c0d0700c8012002000450050607a01000f40c070740340c03803d4405205120100300748074001ca200381c040d40d00f96101d09640340e01782c0c0581c2c0540e0b14615440c50103500c2c2140200040440e8900c0740b080000810301c2400b41d401143c025500c0480402c13070001d05107016000d032485100300011400720750a03055040485503d40c90048140080c90b680c0c400382ca000034010355400000718000018011601a5160715203d07464078584c1010b2091242400b000c10700d494043c0c001d0318107100d00030300242020b480545 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 831780926 1250 831779676 831779719
    0x5040509100b13110a030b0301090312050717070509120a020102061306090b010b04090c02070305060c130302120f07080c010c02010c030509041104060e031603080c1c090e15 76
    0x41c2c44541c0301c00e00140b0854450114000c038404102400c42c410386a409002018058032060303030400744643d15007044240025001000c0ca170800c80102800200b80d0f86060007610070080880501d03030741211400801050aa00c04000c0411540940c0d0380495a4446481603650f5900341344024096000800024030318400342c11101c14841c041c01d004078a47c402e9484114000c0c0b03080c0c001e040d2000d40040c090052840c140105461168544000e15070185903441c0c1c15182d10014142c500300f1400040c007401066142c1086030083c5800620003903410000c200b0007640c2e12105d20100c6c08034000c140c00092180c40c00f0078428040b20f01a1180c0d1111484c65004548085039543c044090100034064a0b8058540d4481c0b0030307141101103c1155a2410000090113116580d51000d1213a404000b1b840745988105c000034088070780c048003440e21030301c0a81c0c0c464101807074003582850050008051114060303108400c0350480d0070b0242c11000c00d880f10721a0900c0c20301076801c140e800c420b075012500510001c41 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 831782176 1250 831780926 831780941
    0x20040207120e181006080f27100608030306150a0e15070b070806011101060b1c060509040f0c060c0b13062d06060201090c0b130909120206010504050910 67
    0x201024041001c0344500c00f6442d078140d941401108140c581440718036004508036030081220745620401c4c0c544200072250034105180d2180344210320348004103d0a40030060f10080304130401c0280041034480da032080da01c1c0c01c100c84051241850100c01000b42060380c08488241c84940e8a500d80700e040342c024800200c099500c503c20114041000b800400e102c0d01d15036008101a036a00030950604800041950140307000701e40b1a44d14094041001d030720a20700700e800050b010305100e500c5102d608120b20042105a106c150020300791030400007080f230300301c3d04600c155220f441c207a00344640f5040201d41800a1800082c1080c00500c0810b1a80d40c8141068200302c1c07242c0c0300840c2e1084007032418408002905040c484842c0d0440342c0504140903401f8080c00b4207054030080042200503240c034124880c040c811000142000a000c1403d208000c88000180085100c1800840420321f0301c810040c0c00c00c0000e40c0140a40f80c00400d041c6844d0041902488540300140710503580a01c0060050050 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 831783426 1250 831782176 831782179
    0x50c07020a0e07170403030911010206130b040203010e0d080106091d060d021311071a060f1002010f0c0908010c020d0e1203090409080a02070e06010f0f0c050a20040207120e 76
    0x4d680b030b05180c3d1044540d035205a00c030740d6010669403860310708483d1114103050240e056421a40400c9005042681581c140940010b0001e0700c0380c13924000309006018400c4000344a0140c03c20f6005c00607041130341076040b0b92040d5213000b6a40c0c2e8501c806d40003240007106010301c0e40783c100d000c5642841c109603e100098002031881542c0c0c9513031000c0c5011100d04444141003c600815100c00703102c1d00e0301d0b020345012a409441495454400c001824110441194a20405044d245030500601c00d52010494030f202e4802040301540c5200d02800304041d030700c03400e5040c0d8248503080c0b202e82e1001c0340c80302c0d4203607550700c80d80901c002410400c480e00100307000d00c000f1403000307001c11551a07440340260841e86010789200c0d5690070f40204000c0c181303110754110203043e64401e82171140c1da0740d1141c909950442245481c08044034880d03001c482d48020131001070498802c1d40d10010074403003002000e6040030b00412000712a100d403502440f00360b01940402925071081d401e028060f0b503000d60b86850040c4d00 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 831784676 1250 831783426 831783437
    0xc090108150405280b0319140714040c030b09190e160302090f0f0a1a130606120c09050f010212040807030515090d20150604050c07020a0e07 62
    0x4841010500302c41c01240c140180303004e507402e0341d95904490400c80b00c01404040b0140458203403032021a50b00d400c11034080c4440d428000804d010300c980480d41c401c940360300000340c409181d81d817010341d0140005039078030134440d03450a441468428001d124140000001401c5600617070782d400c103444000d0080102151041e03841e03004500075a2803d10018403c043c800c0004c86800e4150300600c5440c1800600c0d1f006003102140a100001c040c1c0c0d0000f0364001d10046011030742c600600c011102c003081d0440c14a40100f11168104c1d8000e81a800a8003680c405942c0c1580500c3c005006400740c1d802c070041c81c008504031000500041c140710655070302c0c14806004407040d5a82100c181401c1d40d015910112031a00008000d00400c9020b000c031030701d203559145c000802b6040c8044104d444130302c080a194140a8902c1810588034034801d4180243d20301e450903182e8500d00d1240c1c1e06c02500044034001d10452074a40058190042d18060f50002a00a40804031481c2010b0841c0480741c0c0c0130f0820001d004 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 831785926 1250 831784676 831784711
    0x6051f030f060b1815070b060a0e011202030f0106180e0c0d2f090606030a0f050703020a09050904080406080a0612061b0801230d0803101701050c090108 67
    0x41440c01190700801e01800f800b40e440b4450b200035100c2054100d2054072410440d0700011906041006443c0481c1d0414a140d03910b0300c40d080019455000342c0e00103001a0f80140002510110781d4400038140c5000380c00f92404203805150703060882c0d0003401460600822800400c0745108141c0c000344018410b102102c0581d045180040e104030300c09413080311620910391003a00e04c4801c00103502c0c0300317802e9003008240000c1c2040000301c0081c4010a060301400000c000a84441c0040d0440e4101d040c0c0c0364410081401e0454001f000ba603c140010740105104210006107820000383c0c1030700c600d410900190070030741011021070300e0301b2014219401d025107400c00442d851700c0890103807800e14840d8100040d000004812650fa0b4480c9005000138018803c004010b640304905030340061401c00c1c1000109039000300c0002c1d42009042c1d0000c0c02c40306001c41007140c0c814522920304c085d60b040f0b00c0b00011009080108600b603e4007101c1c22100709c02d040c03010ba10f19500a000d600d030045088500d200706813 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 831787176 1250 831785926 831785951
    0xa0b040b041506020d020705030303070c03020a0f080c0c1807081b04080714031b100201020d0212061203250c09051005010e030d02330a0207051006051f03 68
    0xca40d18210240ba080c0c442104102240e0100105280d585a9001502200d89804000b9449000003010403041c440c40c00d07420001c02d442400003007176050b400310110ba9146801e05100e8659000207600d25610b100b524031000c1d03e4504510709048e21506101018440d1340da40000300c48100c0060306548207640407204101071304011201400141800343e0090005900e05101c000103108400b020030700070b800c090348031610944000d0410702491019500580e00c080a4070040b0300a100f41401100158404100c061076503201c6079540e801079804641a240e070750404c00c4400d8803481071a208000401e02024000503502019098000c018090703c40c03480220740d0ba101203003d56400310350021040c100c00900703004035a00904d40320300c0c2240a400034982d01c1c80e0303c03001959414049907218890f10300c000d0098101d030141e040000c00200d0441c1c045020b4144505020086c1d008401c0440e100c0c00340e8005454031002c140304490403158020205042c50701e088400140b0191504280810551141e46140c010b = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 831788426 1250 831787176 831787181
    0xa0f060e010c02332a181804020d0f03021e1005100b1c061d0601020d0f201e060406201c0b04060f1d040b37020406110703020303030a0b040b04 63
    0x110110040c120f1b00c910140d20070000344044962010207014021004e100150300c50390490800c0356842140c04810310a142000c0e840c00503144284d07510380e4031490108420100101e0790740c244d0000d078042845661110440c40240b841035015245a410043c801c0b2344500810104500b0044400100015807580301c9210003000e022981e005516030340704c0800d002040d41e0401c100d0340c2682c1e451500403c00c0c460744078000c11100001201031000420011040a25032041c0000b10328800951090064400030303441464807510100d41c00e6030300078604010450501051030a281c001102100650b18103c1c41021441441d01c3c036140c2445450b543c0c030320748045034945100b6000a40041550015814030b020700204000c04800c80002104048606200004040391042c07a0094440900b200904880c1c6540c549048010341c8940642c41004100a6501c40e09074014400e40320305907508071014030b00c04545c0c0e6031101140b00094040e482080014116201c9a10074050904e0041000c0380c484090f2001a0a = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 831789676 1250 831788426 831788437
    0x906060303080603191106220f0303020f0109050705060a0507151b03021c0b060f0d060509060609090a02031b030103060b030c010c050a0f060e010c02332a 68
    0x100701e42d041400b89902c1c013003140c1d00502c14240498240140c2d650340300c405800486a0340c60050700c0c0800c500d07425070728501c10300149145010640c9040e030f5440c0c0c5400b01d030184c5031009801600600100800d004418044c1888840e008401020ba9a24000a0005643c00003c0100c1000010f00c5514001100104d0441501c000c1141c003103070100d0051a442006441100484e0038940304001412440a0f00c28590032110f141e2840010700e03000e92000324149101c0e141da128000d403c005100c52190140f540201d05860741a2010f0710965108018010a44100c0302081c1c0d0055140d00040d6844003c2d400650703021106a49542517000742d20400500c0c1d4100b84c008030741c0c20385c403590320031401d00b010081124000000d00e010f00c415015600e0b030940350011084080d11400300b0120280504c0030a402542081e1041002040051040e000013915080707500072280105582c0903000310455048400d445107101404e100750700e551201a0440e0210082400300b28a010b00400c610286058003c043d29 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 831790926 1250 831789676 831789683
    0x9060d14190f060509040b070201021b0304030b010f180e0c041d060709180c03090f03080403080108010c050a030b0a0506030c1c0603081605011506050703020114090c060d09060603 79
    0x44809194405480503501c40072020082c040c40c0107001c001507680d010086401c10380208200d12142c8a200307007240644a0001070540748004402a0801240000002c1080728041c01003203400741d8a50100e120401424440c0007056209841ca1405010240d4005280803a404e401c0300c0c03051815a000c82c054480150400c4025012659041038030380e018490f040d030008031490811890307400d10307015400320280c1402400059036540680705189010307510010200ba005400c04040c0f090501d002410a01e0884040b000202c004000003400c40050086540344c810a4907143d08200d40b00904030010311403554800d9100c40c01ca50001120380702e03400218000c1c00d1075001c1c035580b1905d441e9200245000944010444c82c60880100046071515080d80c0300030104003d4960b82d0b1744c46050141c003501c506000b100d00840901d00010700c3c140c0100c0240345c5503110703800900104090b40d0300240405011249001c0c07070b8000d4019642640780244c02064540c0e002000051902016100d4400b00c51450700101c = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 831792176 1250 831790926 831790951
    0x30c02010e060c0d14010305120a09030f080910020d021902011814030f0a02030a0809010c0c060207150e0f01080403050f03091e060717060a081912090b09060d14 71
    0x800050130f09004554020403203c00c59071143d4915661150f6954078001c005d07031003aa01007040795405100e451000000c5030808e1415191100506107803007990b02071030400d8440d03212034015a0202e030011502000c02000c68010304a0300d2281c014082c1c18081c1008101c0c100171480c070007003400c20608072080b0050802071004c01c01e01c2070f8440c01e25160850341c2da2100500d6000840140c0140d5000581780c04d419805010340d51141001030050303c0b07046007004020820108034801140d12540015010100d9003804904025124908025143c1e002038841864104842e15030b032120a500800d120f0340c00c00c0c407030b1901c0f078509a041040c24805801c140c40c505116003009030000e035842c0304041e0070302101000b1006010341d03040210028110858081454000b0158400054010b43c2e0305035914001701403250941c5e4244003580c25001c056200c1b00300881e80c1d0350420140700e01e12407056860704203864440203c0c0e45091a00c1081190f10380003410036450480c2c03540d4481d41e01100d290302850003071104501c80d = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 831793426 1250 831792176 831792187
    0x10e150601020d022125050a0302060a0207151107050a0606140a0e06190503010603030c02040e030708030a0504051c020313082d030c060c0301030c1406070201030c02010e060c 77
    0x80c1402e1002c0020f034219840914203001841030300310340369a101c8681e28081d85d140240c40c1003402d458110518041e82c640450019001e021022800ca9802446a4243e404130f81d11603203908100c1c011590b000c1c00c0300c1041c1d040c040d030036003136a4001da07442d868070802d85092200c1d42d59580d14082581d802192069210282000080702644a19040c1c14040b10820b80580c10302c1000310012400800b22481782074513426051040c400c907207425010b000c1c00b030000d10802e83c880c2005085054128001c038044c600d4000452903030040070082e03e051950005055140d9182c1080741809800007500c15500c1d40525144c1450840460749855248051034010359124840700c41c2850021103242c3c030101c6580c001040040e00009004401c080203a001e09a0300031a13410303010b1f03032851409181540300f2544280c06c240300c2c15002282c0654101da210b021180c100f80c0e00c404100c9800d900f140e000381c0d08003505220703500040d8087d4003d502e00e002e103072000241c02c118031680d940ca0100190342c80041c0c0400040c8 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 831794676 1250 831793426 831793429
    0x260708070311010207030e040b13060602150109090201080f0417160b100f06050c1606020c19060c03031d0d1119020a0911190513270509010e1506 64
    0x80c820400b41640b802103081c420292000b80c860240010b9052040360313143c5080030380341d586c104030822a400106082144c580c4800c0c000c1d540309c452040c4411858000000094000c5c0c040c02030346982607040c1e446901c0740c0c4985480c01c3e2152409031084414880c61081c0c0006020804c0182144003911840942a00c02d241441003041e040075000741000701c80400180400ca01c441c445504440b12480c00070340d03801421005604002c0c7c0721011401c854011140050b84c2540010410303481141160220f5412196204007000030100344101c3c000325180646c2000864000d0344100140c20301c05490040210000e10351905210b40c4a044001140b103405035004105030800510000c001900c071001703c00c02c0e0302d80001d051460b113403041522940e140c1c43c01c2899880c06606441825065002030608082010700180184e003020440071520f00b44120006803402a209456044644c030303602180304444507012140c0075140c010620080396482e4200e01182c0d040400210720100a0080345803407608201c1c0 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 831795926 1250 831794676 831794687
    0x216380c160e1302221a030c06190e01030b030604120315030807120207031403070b07050f0706090606080d080a0e010606120504030201060b03040803040323072607080703 75
    0x2004051401c42c090708000d140b22400c0241d124640d011210340781d00d19692401c80140d030505a010480040c1480d5183c01c0b0300c000103807103082100301101514040990b82007880078900940320306020703108900360700540302070041920740d18031003041c90b000c0b43e400c150700301003807800b501510110f07448294480c01d8440c890303161080c0d0703041c1e00d498907024010034603548816006008610700509622310010183c118130740200f00d03090055501103511a102002e900011b61079410103801031701c02c4418240001d4105214002300c0d801d0304114a0303981c0c100321454a40c1002003407038050444c0c00030b1307035007501160000c5d00700302610010a84d5a42d40d21a4a0b100558100752140384140c4119681801d01c180090303604a80c04016800d20610002182c0e44c40382412400b60106601c4404400c800100348001c0c00b5200e4011441180251100d4900500c0d00250b5060030415016401c2c41440900804000440301000c1141d050950b1890003076540c2010000c41031a4001364049a0082002480008054208 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 831797176 1250 831795926 831795929
    0xb060a080c0604030b0c130e0f0c031608041704170709060f031403090607080a0f0f08010504020a05250317040b2d07030c0216380c16 59
    0x84024094800140010421502813070000a00c480d500000007a211000e410640c1c00100e01021459282659130800318000001541c400c0969420140080e44010440d400c03640039118203e8151080094001d0440d640d50010388100d03114032983c0e910218000440d00904040c2401a04070aa0f02451000782454400d055101c071201a08241c0f0400ca08050030028604681c0c21165424400c0f041900c058298490a2503a581c40310010a09605204a50024003034213420b58840f00d8481c3d1034460142d501d07402d001c2502c0e001602250060155003405e0700035100c01c00c0d1505100b800c00142028104000d00048440c0715140283d854030400e042d80b00c10060041171602500740c1c16414a521400701d18100100060081d841504d000317400045002842e4400d80482010b20740181484100140503082401ba80001486078460500340794299500e409c040364800d40034584400e0b446403071020152008030041355070b040b140d82c4145500b02c3d01030090070359482c5103002c1c0c07000700c1141c004007248a031035 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 831798426 1250 831797176 831797189
    0x2120c0f2a1522080c030310030b060d0210030e210705012901030b061909050a05181321020f0d03050115110102041d060f060a0206130305070b040b060a 67
    0x182e07010311140e81c8440c280103081c885a025a000500b0745800c000c01284038488100c6944e100003c100aa007042d450546001c2d130788900301c0040b03145c684401b0021440c60f4404c0280d4440603401103051068080e0f40f01404646207031065401010b80c07a030031269894209807254105040c00101c1c5402c1000a01c100c03c0b080b2261001203c4040140e030110303c01c0681c03a8480ca05059890145000542c0c1e0001503605440f044194050301e82d04070140180300c0c20051084a006a54042022840303203032036101c03041d0030103505503464607039901d000300541c00341700d180c009894542c0354140803155140502a00c84039140c1c107400030081000e501090714a007403400d030b0303222041515040050100d054400607440124080745084c04290704614102070080c0f04680c401181511a41d50007a00c4418011186210b100d00310303000c400f105112400d0001901c42d92044100503000700000404542d0b000b1a001295406880c1003400c0c407640340d40d40c1c00f00710720949003520404908030403c00f46141c447e031101e014041c0d = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 831799676 1250 831798426 831798463
    0x703021519110a06061410020d12020706020c0105041a01120c0909030e0a060f2304170c060a030f180201050d020f0705150402100302120c0f2a 63
    0x1089245100d02100c006803100030031440ba0540d1640c80001c00c420886107030051400c101040e69114824610801c40346018011002c442140520f10700204120380750140c103480340c05000e8181d89290000350b000040c101d820340d0342070000340f6a1074024858188914070415a00c14130480502d00300000c1c0344160310402e0113620050301ca20014500885000449080350004100d08026150503074034010300c05401c40d0441d580d5072001800c40d0740300f0981da40d0460940c80e480307070340e8101e00116900704211100701c211454042100300316544c00c2509820b80260087d060310001d0000c603001602c00d80c0804009400241c41d04920710540b08a44650280a00d0b15040070300100580e5001804901455412505051703010908140c40c0c0001c0080340c802951040664005c072041180022078a00c0694042e801809445081490103019100f107452038022402e02400c2d59a9502d206402e40d44507040c03150302a8810300c0302e10f0024404206400441d40040358103c201d51100e120503250003404c00c1102a00345 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 831800926 1250 831799676 831799687
    0x40b040806191e090203010e01091b061803030f02030d050f0a180f0201110a020a09230112021012020d06060210110919050a0b030105100c0537030207030215 69
    0x4981c0fa0801d8810f09600780007066010503400045c0c018140405c041c1281d50070308c0c9011040010000762138000702d0600003024420ba4403135004a900d800d503629142c0a402d2800c105001080c0030f02500c0a580f600d600c1202d00c0d005003403e000c03040e2441a200135221a00380c10038000b101e807603130084540c0035040040c0d60b2350780a070310385a08509162400c03010703040c004603924003944603506200204d5101d401030500007401d503491a00c0c0c0d000700202810612403001c20642440a00f00207110503040b100d0b00d10b0240f0404107990204800442104d00740014840907003030f55840c5410318005440e0203119040c001805925094000e400d1401b25800c0040007403404604403a07103100c40058910448041d030342c0e07503816041c840c0c00c5605448940c01c055400070064070700103145540c0d800214182c4409440d80c04010010707040c107643c0003084030740041041d00280d82c1210b080c6000c054550042070344050381c1e03c150008480417000300b01c61031419030060300305440a20a508050380c804038000c0034070b4415403900 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 831802176 1250 831800926 831800951
    0x120408120918100f060c0506091504080c07090504050a020907020d050d110702040e060403091d070f031d030d060b210c070204181103150a020a05040b04080619 70
    0x1496441d15140025000008102c040010207030341c4004e05100065400119101c02000d020074550f00021540f9109050005058082c04612000c0400000c4044070054990780d4400d011901f0050084402d4070400d80006041c0345c50b070140301e008074001e001404a0482c6d9005010004a008084c4015036001811201c40300c1d6105040320104491608001200d402c448210201071140e070034040d5101c1d0403c0080141c001c00840c206000d1031003503c8034031046031f8400058801462080a020300c41c40824005060703e801600e03c0d00044e000c500d8001070560244dc8003c011148468440b2405c0e440030444003029645480384d41d0242507019441800d005d6552480302c0c4c0d03050741d0420700b9142c0d00000c000c03c81020300a030549020690003002800500790600006200300740010045d40d01c3c60300c1001498485c07d02081c40c108003503014080d180c035941d503100150701075070000c140c000410404001c0000c0003901000600081c006810103480981803484d04007a02c40140c0190028941c548400301052 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 831803426 1250 831802176 831802189
    0x3070c0f0b0115020f06150d0c03140f0705010806130912050c0f0c0d1202070b0309150a0207030225030819080711030412060b061206010f030603020102120306060403051204081209 79
    0x80111003040052940002c0408c0e04101800001003040c0115203020081010f00f131900104118100110f548409401c0b6025035030b83d000388555804504020045080ba0034a42080c1190700c1d41d8080200d403001581c3d48549c0201d880580e10400642d01007a10811024280400248407400307200800000e8010343c00203601500f10000140032011074104402201d0091252200800c5180d141c01e4592810005c45601c0b9a02d00442200044010002924840c85482669032154156000f030210000d10090481c2600b5480c0c074007501c94032490800800107103140c000b0007600c0c0c0d4607005d1585015441c24050300328000135110600348941c41148481548000003520101da0012450310075400550030441d00800d4140f0850742c1080b40040c00c8003840e00d003072120601504080ea90400c503030404041c00c40803a020b900000b0300680040d02d111240340036a001440d04180010612481c00c0d070749685191810411600348010341724085001c000400040c40203c0c55007810002d401c2c682040342c800200d8 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 831804676 1250 831803426 831803431
    0x60619022b120903140d090b01051503040b043f080103052e0e010b03070501091203030f1107050d110d090b031503031c060f06050702010503070c0f0b0115020f06 71
    0xb981ea02e032000000e0611451035403000302280003210782d5440090350aa0050504130f04250b0b00e01404000018036800c151601082d00724405410701d055032103c0c2ea9121880b9405041a01e0500000946105a46014950203840c07010b15120210329040e4848400d900082c482000081c03051040040011640110ba10484c0c644903030040c54a540324002400a070788104d1103020001440c000071070356171210541c001c5d0700d108421404c86e14000c0c2d8400044418000310700807600c003032405a0881c40040e0198008040528150b5404500ca20400304401d28036088100191481da01c0360240300c200a40012a1200c948001c001400d0302c4400000c010740660720f02d1080c0001090b00000246d110a03c0301c107400c40380c0c407004044c0d90341d4010400c840207801c0000039540312858a00030002a010b01045502c5040b1003017a144d4504284940d00152400d8200401c0d440a010401002000081801450f440c880e0b106500710b0b0119414001082e030055020303444007041d0341c840c44d2002d2042d00005100395 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 831805926 1250 831804676 831804707
    0x20405151f031b0c03020f060c090415030b09031c18030c080d050109060f060203040509060118080d02030712020c09010e090111030f06191a03060619022b 68
    0x1403035844807404400400c0480741a0b0748514848820000b556841881956494002e03805c4802c0465841c5c0300d15250101a40c2005030044100850302032420503800c114443c0b128006020101c0c0d680340c80303012021000300d0314a2100e4200150710080012001e1f1080c1600c10050801c00c20400d80c0c1c11a40701c190072280004e410b000b400d200740800c000141040b5081e0144000c030a000550f0746090420241040340903169050107016000308140384004161411500c0080c10700055407101801590044840d1641c482c3c9000d400a0100b01d480b82005030a120350740b61303802995682083d003801d001c4403007540c90000841d084100621080d0359204681c40c155200c10300d01035116240c142405005002a148070301ca00076010081103015090f11410310f10582c801d1310f4985440810b11984044122203010341041d140c01c4417581403403000c0c4c20018541c00200a4a06450030b804000e91058401d098044c86005030302c020040030340100c1c3c03044600390010002c80e40c2d0740094426000036100590a840d000c = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 831807176 1250 831805926 831805969
    0x30c04050405100816150e090c0d090210050705010f09050c220e0619150b1e0f130f0513050a201b0607080411010c05060a0902040515 59
    0x22000066640070710001d000a40031520785c803100d0f091201d40900e2a2007050485525001e5000c2e545002c0c401d240d803240c00080c00d04940d980c82c51210300a54002c218000da24940c0d8076000c8005803140c0000742420340307a0f41c4401e9103c040c14078185095420780000c10803e94208900540011000103c0c0b130b030002c00440e41d0f07807440c6680442a1607804076842540005500f84040c0451158000c03da040c0150b22010070314081da0031a40d8803006680420401b445001c544060400180510740c0282030003600c0c40820740b50b107001002800d00c02e5048400c08080da02d0b03001800745210141d81c080030000340600c03007290307298903c2c20000401c2402c003210300448242d01c0d14005031030307080303958001c0340240441440b440d000b69a1980c9900715400c0240940312070309800d86a4000d1090004400d84200000d40d50113902d81d0b1283d903803c2c0c0340c2170b11201e504d05004400c180c6e040021018408540b0840b28144c1c0003032081614010403096950180c030b80d03035003461007000000d0307141c0300c442c103e00800721280390740c = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 831808426 1250 831807176 831807181
    0x130e06010e1813150b0301061403150408131512360210050316080108070b090102100c030e1504020a090209030a0c06350612010b0402040f0e0705030c04050405 70
    0x6590b481c0c041d20008008040d11040c0305940d42481e1722000401400f58000c004003510307032203448001404911007592607800b441401c48480c0d40b01082c1c66000e44108041d5043c0b1302104e0940c0300d002102d412200f0a4100c0c0d8040342c850b550b00c04103c04010708949000c1c01811180d0380c4800e0418040d07032014007603400702400c0b4070b1514901514502e04580c050300590383c119814800030016002036a0007800803014825802000b4440c83e003140c140c0c0d21282c05011010b2400c0f40301d500710f9014405d038a0543c000c001408844001c24440e590712840c0e152008100074042415680c10000400d640061184401c0c092001585891100c4416502283c0006980300205400a40751507040702c1c006111880c00003000c42c1c071030307400701d2800c403c140400b0301501002c4016800080e101ca012000442c440016070006880d89008181c02800700c0c04400001210003442e80401c0680c0d200ba0400014404000c0c0708201c14121482250b074031082e1894a02d06500389603c007040311380b25910900348116200d101 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 831809676 1250 831808426 831808441
    0x5120d09060e010c05030d0c090e0108070506091c0c060909270503090d080a03150e0415200702150406050301181506030f0f110a0c0512130e06010e18 66
    0x200b981c10701d4100e0f0850351100015a80301d4094251070301c500c030015101d030703034000b44080c0d410ad1541d044e01e1701c1e000a0618181010f080c4011a00040f20056101c0100000c00c4080a034a03908c070b4503502d002c0d200b009981424000040c1c0205400c0d0300400d081c03403500c0c02e909040343c20110501c01003050010000c110b48103609116165000d055100b50b40181a00410402c001001e4024070103103600d51018801034000407000300bc200e08600c590000d1100440000300010350308000e24030728103000c55000032840d115103d03210f660342840e42400011500003c0711015464003180345541024500329040c90581442001000c0340010b205842418402100d81e0840d01103d07040f101c10021001888121f1559a190040180084c0c0c00c5036040145444e10781801c0703484a0045c01c2401c002501c4070b030314010b40018115944103050400740c4081c0070300a108450000b0b407500401090310a440040540360a00c0701d840c49200c0058520b038140024040c150109031100303c4603045020850949420340d995100 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 831810926 1250 831809676 831809687
    0x13090c0503030a08100f120204090f0c1814060d080309100228090f0501121803110f0106080706050f090a09060815041e0c0801021305120d09060e01 65
    0x30881a494003011807607000d02a03100800c2071086001d142200040ba40d681d49411441d0018041e80041100d07001211015041a8001c0d54240348a0050000d0b480c4031604c5503400c80034140c00100ba4801d1105146074480c4080c040d4200700361a02d03610051904046002842081300c946005080c24800700c00910071000034000e09a03820544001595104400c1402201441c0201d19021410078440380100d5050311030b003600810f541074040c00e1903c142c209001580c1c1c1c00d41c0c0e05903c0b0350b1940c0b900343d02c0100452a8103d4101984261a52851480d240e42201c0c04d000020558119036850844200000b2500140e590b0444019040c01955140c400601c0308042c4200c0032895080942401d00040c0d0b0481503104030f085462400640b2490031ba030008241c10300c1415100500003400221802e2044c1284ca02a0207200e0311990380c1d003a070a03070b480031968266004804164030001618404100500f864a07010701001083c0000e0003002d80b030300b2006010400c4900402d0700f08629681c8015459016a = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 831812176 1250 831810926 831810929
    0xa0c0807050105070206010609080f1506030709060b040e0903210709051905030105150d02040b03011803030506040b272a0304060b010903020307060e1302040909020f030c13090c 78
    0x4003d100c0340c81c0611019640d40001e12030000021190400000c44680104040c180d0a1441c4080c02c0101014040b150360000040c2180d64140190b4000003402101442104020314524079010786a500d042808028910001c0015075541c00801c00590801c89449200d04d04014890380782e9056124004212817440c0581c0000360403800300245083c20040205152080342d10840c000c1c4110342d6040140104c04c1034043e90326420070403203074100c0010b1800c6d402c038180000015000181341d40101d10034200c0aa6407100980111f540c074000d1128600b4640101b48500009a41c04144071041c92041c400900030180034000074404240450010a2010b41c514071240341401c1100d0492401e032041241d66105440803070b00b5a292002c00c94403075025440020449400a000e04820752905000b81e4000010f42041e5500842c110300d1403221244510241c0060320804400203440251881400a500200080c0394440e5001c1660039400e644c0324028481c00692124020038050324901c0d1888001445 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 831813426 1250 831812176 831812183
    0x80a090204090602120702031e0904091a10081605041806060b180306090d11031909050102010c031a0f060c34030f12020f0f0d030b0f060a0c0807 64
    0x820034240b0034043e29401800c4004031251103840340b80c543d0a8180ea0f24030443da11101d60400400c06d1113420002d03100904030122014001258801d0b41d603540143d01c3c41c581005180326070800e02441114600318588034003400c0e50800508080340c40e035132400351030313856403040a1040381c076070020410805040480e07901da01d0740003c0500000340c8800925169410501016801c6e00e007078940c01c4103a1a000488600802c0d04901908401058070412140c55520b403a00321124801041564807060850001b000c004400760369101006050800081c00d541840c0d03410b00c02c2505190050704691403010340d542000703104446082a6408990100d4054003540b001d6045070b005d410800500c195510000c25101c0140c0144107500b200100c408003010486800080c1c03c110380d1a81ea100000d040241c0102c00c00091300460350707039103440f2a1040c608000581030040301c0e084441c644400d19014002c08a03c1a011160644020400320100d0000e0181c011460100510f408402d0140b040340300403100026003 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 831814676 1250 831813426 831813431
    0xd060f0c2003040e0a0e0a12090509010605181c06180203011116060510030209040f05010f110f130e010b0301030c2301080c090d0c05040c05090102030a080a090204 72
    0x420340103011a100c0720414030010040c0075a284800c20048110b9059514141500041d91508218000282407010521041d8841c044001d0042042c5030a076040c070f800b50303139148070800d4145000d108903d44c060f4480c0d01480401e20224405c0c0250400c028108171041d148083c00a00950106200d103d410dc40a0201c44c60101c0005a80c000f0b1001243d2240c003d40080c400c04091114900f0746100d529001440d40761108194400075001c0d8110a8000b040306601d01c480c81c0e100d40025080b81d034240c500f1150262552646030030000c0c207001e011010060b07038008128580f0000048808c612420301300c0320414000107444600b07030002442c0e26000c0c200c0820101119030715155090b5040c0c1c000e00056030020041c0f0000104800d44011805840c0910b113029000c1880c107800651301544060160511400180140002034503a590344403101d5000d06240c0c3d54992500c000c0c441280c4c1180460010098208030342d2031507076000011240d028095141001c001d650340e407401d01c0101424000294000d0 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 831815926 1250 831814676 831814691
    0x1501050414070f0e06041710060803030c1b03120a0510091107170c031b01051005010c0b131e03270312091505040303030b0a0f180f0c020a05160f050d060f 68
    0x80000a08238080030640d0070800c2500e886a07003503030b41ca00044078040705142c402c1142ca403101d10501180035000e9492011a410440848242075000c40b04861080082c1c0d0380d9010000e240c01c1d000408801004003280c00c10044a0f2000340061710710076140b01510040003035500400342106041295880c521000a50340ca681032008140c2e041800d070307041031201d9820320300070421030720020811070100d0b030050b12085603200c1d45035603010754004000c01e482118140c2803041e01c0807811107141a80355108a031080300c44401d0624000c0c00d8140510059045040c110040d108103502c0d082082064035040100d2500c52800c01c1d10407030340d03003006030424031210214032107a1040542010180096034400d031014850310006d04188001a00c1610030004402c12400041004400d004840c0c189250034641c0425143c49d4400c010081e5401c1c06101d9005078070480702d510500c80107100354103d07070001440c1c8041c001d28050622490909502a480c41503000d041f00d1010400d40703502c001d4111070110780911001 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 831817176 1250 831815926 831815969
    0x70212060702060402031605010c030e04090c06390b130c12060608061306050c0919050a061e08070c0537080f1b1501050414070f0e0604 60
    0x30f0400b5602280030740300c1e034400035245124100400c3c06540e01a07456800300d981c280c6084445030703078520144d42c01030354bd4035021001c42c0101c40d403d00030341115102c0c588100b4141420820760003894144500c480b602c00008195003d801181c2030040b0307009a414089a00d07a010f84800c21800c08900404004c0c5240000680002c20410640186d02404042000950f218040c03522007000302c521046071b850480004000900d168011600040003100450805201c0703800705005228080407034011205040040050340340011035003018041c1450640c02d00c1e0301d24003610b00e102030101d10034818800d001002a4074503100d1118490490f8100301204d40750031094421202030b500c03c602c10900311b4840c00d954503d00e1445244039210a034461300982c60640001c50040071038002c030350080708502071030011004203d400c2210491180c040e050844041d4580300c100000c071481c081118089072046401c000085821850440c2040d02d5814031445503050703080020524841c2d50400700700808020780000d400b = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 831818426 1250 831817176 831817183
    0x405032d150601260f090f070906030510060f1502030702061605151009020c161517040b010b1c0501091d120912030408030711270606070212060702 65
    0xd0351081c0c9503ca144c000c800800e0418252015103400081d9030100800c0114141030012035020700d0040a803180707240c41c2c006460824505034801240144c542d402030050207000e0201040040720180100151840c0590070304580060744601c1040100e450112040c00c2d00074802c4404080d401040f1540d102494400c00c4070340424060150707124030654a90160880c2802d002901031032001740d400c40c0f040e103002501c034065400801a505a4020390403007444101110b000c43c0b000e003d01c3e12503091000b1544100500c1043d02502511020a02b0340901010801c54a1a01c0c15143c0e0b001d00035503520903041c0c03800b00c0c2d40c4040a0711381c0468a02000022507005503480b02582c04400031081d002d10020748403041e501c2d03495000d01c00e409042008844c141d03250041d844509124040241e0341065030300c158150071900500c106441401daa031854000ca468901840d2603001800c02c00740310f40b00a1000441d80002c030060241e802001d001441209550380c221803800c1c1040e00604440d03161400c490000d45 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 831819676 1250 831818426 831818431
    0x11040b0301090510062c06030126010c0906140912010606021b13230903091f021f06081c0e062503030609141501050405032d15 56
    0x4110b803400c1d0102d02c6406404d54864200d44240d42e41045492001210700b202c5282c0c0410a203c20341600780c800c080d0f0b103941001e9402400c0240c09200314699012001110125a0380c40a21b503034901031401400c0c0d50001e40c3e0034281c413441d00d4545e8486600312000101e621580302c0c495400380b450781c03100d010ba84054000d5400e40d07502c0c1d420388040d014482185d80713001c0c0c2c245214030342c80010700540c00074401403580051070070750207012402a00c0400d444900c500c00010741e060340941c0c00001d8090928248507000c8401c0320300003800204100d0308410001c0d2150a4001c000034403004900c0c0900400d022504580040c20001c0d0a641c041e50302c10510184c03101100e00e1113004284140132042c00b52030104151810000d00c00046082148003810603000c070320f1024802c80c1410343c1d60701d0120310640c3d01c0c0f1503905001800c503030321062818221000d450f15402100ca050411a0130003090016131030214440e8000b501841401021003441802d660f051710204001440d1842410455240601e40301142e90 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 831820926 1250 831819676 831819689
    0x40312050409022803090c09050604091b05030106151707020c03030f0d15030b0f070201090b0a090c09020c070506090d120206010315060302010509090406090210020a1a07140c0111040b0301 83
    0x100c000142c07601601940d1006c8000b0300741904d00329040103807083c9074010301e0340007000410008041d041c640d80d804410b4404031495080c140a5242840030341001d100d10006000c0c0440110b0000000340c3c401005188003d081050b0540d620f8040780890703008210b10582c182e070040c20b07292503107610b07030b400907042e0003201c1442080f0381004540c00001c0c500b59a500c050301e4101c0e519000303540d01d00c51041c030050006817050302190340c0d41403140046810850014055409541c01140400f5075080659843c0603d4101c031086601c1008480f908950001e00c05080341c0042e2405500ca0f807401d0000707040206000009418070500103c0260103039408114141a2480744044808419100c04090102d40b01c1380802070101390200041c038103d2038840744850b40140b0980c00800c03401c3c007507800700350814841d42442015a011002903400c11481102d091644004410644060715109000408040444816404802c0c00140100180d0029002101c92144000d4400c0e030f00c69951400d0007455109200b04d8 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 831822176 1250 831820926 831820987
    0x2040608030d24080307030c03140304080a021c0f210908040501120911010e0f04090506070f2606010c1a06040b0f03100510050901080f01051b04031205040902 70
    0x440340104401c3e10380d82a21401c000441c14610190b500365000a03200001360240000310411f0300701c5444010056225900c00c0840c140c66109821000c0d02d03020020314200b4410361840c40009403ea842040030380355041a1800d154030024400c44034003250402d21000740041c1c1801c0b80b450501c003c600040048030000c0c0d0303850103111004c102e000704803004d04000800c941c181d50b80c071069a611542000000039001410080000c25002c0000c0c115403400108540c42d401032820480362641001314422407640b0790505c0c088000031215050b0181e1021095640a01c00c424007207002641f244406042050f4440340003521fa6040000000c1a820101d43c0648528100402d40704182810101d0044440d0058000d100c091440380200e000b404005009000c01c07000a44000f4856440100090080141601402400c0010b1030f0b054203440c4000d18001d02050000001c1d06801d00041c104c1f011039400100802040101c3c040407503843c466a4407402c4201d0021564414043d8801c03607a160945240554 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 831823426 1250 831822176 831822221
    0xf1b060603030f07060507030f0207050a1b03020303070f0317100810140f0603100c0306030b0a02120406020c10050403020c01020708060c180a050d0308150117040201030902040608030d 81
    0xc05a90b84078240e0300a00c240e5091144c0c0000405e160011500290305d030030042070404000001c80d04031307041400705440a034480c5a41178184420214007910500141000851507030075500442c0d900d20406400400c0c170f4032075810000a0605c10689401040c10805402902741000e45480090844030b000302c041c0c501130654006082480f61142010440b00410450000d6441c21a1079510004c0244800d80500a440c00c0c0b1320254428490004810815100051000e0039418040d80e4224000e2051800d82e10411001c01c1c01c020f01140c0c5d1740d009900513400360343c4110010f0200d01b0035090381c4001003c0c0f410f040a01040680201c1c0d05000041d0a0b401c8692003959541030300d580301003d03191260300750402c201c0c0340c07504001002811000710015010210041e60741d00803d95007071124a080e4009040e81082c0036a89904052010100a0900c0d10710003500032000b61084800029000905040d60303242d0b10001c42d04c03035402503c01880031f02c056035103454403482120094040116a05039102c01c0e031a0 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 831824676 1250 831823426 831823429
    0x81308070f0803160618050d02161a03060d03090e0106030506190e180703080406030b030d08013b04050309190e130309080106060504090b0d02011e050f1b0606 70
    0x399040c6401030507544e000c502d1240c40d071400070045d01910141007140c280440c4042542080a080b1601c41503004080341d210403000c24021070030f50341046034917509d4035100320343d5820004d007580e0700110112a14580440f039407409465514039507025803c0318a035a80005041a0142d2026120f21026180c0420850072401c0f041309a00341c40c003e0088143c40c0a0100705d0a1044000b142c0704205036608980c02207440b501c41c1041da03007003580704000003525000001200d003003c1c000040001401e080041d05541421b544481c122440240101120540215056030410014040421a401044409203401c040c10280c0e2640d201c034081c0380c05002e1450f12014440c007044c01800450350600d031000103079224021007a12403141110250100140c03010b020030726071b50a01c2000000c04c11a100d8640e41c03454030f4482c00980e898881d000e445168184071810150740c014400420068100c805c0e4030395900c1101d026a0140141c01220700e211201085180302500d0745102080300e10140400c48039107658040 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 831825926 1250 831824676 831824683
    0x70825050d05071502240601111606080c0f0706050a11130905090c0a0b0310090209011b08300901180602091f0519050301050303070201050304081308070f08 69
    0x1400184568014401041034030703504103010130503101d07030300c140c640030355600a0700301c0c1040c2c000c0841200010380005000071980c02030402c1818900250140100240900700440106541d100c0c500600c0f028000140d45582c03004200e07420400035140c4c080d100c05207820840010682110044130842c544400450300c4100e50040d10f10020801510701c2015040c9501c030405404040d02c0d81c0e9152003510510348a0b0365070400d101e0080c101e030140c10780c0c07240391900340c480381a8400e900209089104106030302c040e903403002410300d41000d815819001440741386050301003840b03901440800b07000740400e9030002c00102d00306442000d600001c080081d071540a51242200d0907103001101c8010305006d188000b442c50b40140c111140004e16285030304801c104108041d00d002c01d0a68001580040d40c001915041030744405901e1107441c2c868150740c1000003103544c034802c03444040d051000100025040003c84011101c541c9501e5580c034280550b1760200654505d070b6030042c1d01c4104080d2001294180c03000 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 831827176 1250 831825926 831825949
    0x405030307031d120d060305061303030f02090f09070c061e0b090702061b070b18011503080d0e01060b0c010b010f021f0c0c050a03050a0e060316030e07082505 70
    0x11029010713910b150b20741c6480d01d501c0b48100e01a4140c9446000020030303c28003d147c442c0c48020320180c078141003440d000b0201c0c0c94038004000110701c14003144075a5218407443c00a8400c054640b0000d54940100940d52011065801003000b8205000d030344424400328a03071410083d00c2442844058106020800304d10011a12800140e0190300000c606001c01c804034406424101e242c54a800c2a40d1038540000d40100c581110707413a8440072080440700244201d620103240c1000706144d1074119524010944144003803600e40315110304014420030400c1d40040024508601115650071019003003c0c080d020060721039011902500e48662500d0020270480d501c585034080750ba64a10b018511340c802040340100b160100802c512018000550801103d40018080c0c2c4449031034413130f5043e008241c8070281000a005d00c0302402800749001e1841030130440c0c1142406c01107070b4030b50b070010114030349011580501e425100e18a4981c118014400440b0194810002079600050710f035818010b012040 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 831828426 1250 831827176 831827231
    0x100206010b22030f03021f023f0f1e0906070c0f06050a1e020a05030402131113210302030a0e0307050d05010b0907081012080909040503030703 63
    0x2008a44076071020007207540b20072912025288a01a101d03280c031181c26403541030071400b41e40001585403d0f216100840103108441c454190315180c00c0b250400d40000b4032242144074a0300d42144504807201540a80d0020540d1105002c40c0e4945204402c000d00400e4072400000313008085404000601c407840c41307202e403a00d074000b88400d0f151144110b5030f030900840166a01408602150001000c5004040c01031501075000304d081044034205000e5202003046080b81e1600c1005403440c010740040a49901c20380441c1d000c4007018424003000301a102e4480004000200069001e104400380d41c008819a80700c648a80b41d00401f03000500c000303948000300a8050f074024010b5804241c4200d401c0501c00401034140d80c200340c0c0e80c42c0414200c40500d0800c6980e6515030f4840780d65801c5c070707400e01517106050780340040d680e08250788420009c0156028150f05034030305c9401c450130302042d00204c0e10420300250042606140c9428000d44a400940b500c800113424000c0f405440d001911901001d8101c = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 831829676 1250 831828426 831828449
    0x209060f0a06080408041701050907081902190509040f06061203120f0b1e09061c02060a0e06032d04080423030708070305060a060b090f03031303030e10020601 70
    0x800a0643d05030000070000c8400c030030100030118502e0f2003c0e40384000e9242d07a41c004162814074a490a05211141c2c05c940c01c40c2d403040300c103206442c005400400400d034058821180b01c0c01c030701548010615180d00300b45e4000280400380402c0151004620070003500030b44040005070784039245420b0764030003030b44040d00250502041440440343c6505c10903029119001c000360402c40d420208440c1140b4824040118102c860607030680c1c1421001598000030444940c00a010303461040034902e120108003901a070400704042210b00c1c041c1e2240c0c0301e6454010310207038032403625541403407030341700e0044110b10350020a00c806400c0c40303140174195004031b1b0b11010f81824141402c01e00f081d0100b60b080d106850403050031540099841c1400038402401000014000c00d60031800c1c01c6140442c0030388440841441c000e8104807400700502510581c050807207414207c405144002445d41c09a80451070002a0108000080540010114002c0902030b500d4002101800030280c1e2642c1d02480391445150 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 831830926 1250 831829676 831829679
    0x6060a0e102312030c010c03151707030519021206040b1501090512031206010206070207090903030f0f1d0a1e02030a050a0507091a061905190302070209060f0a 70
    0x2042c1e48580b81404490000180710704a0500004084840d462008120364000040210125000b8045d140f1100d019080c140305401000c89007907522901803180300c15a01c0e0602d949032400c0414020100290b4100382111a1002a20300741c01c000944c00070201e11078801d0317400b0484001d001180e06071103503810a5400721255a58942441524200e404950420440c03440228042c2c0c0c5458500f04050000d200664680072541004c80703452030301070891030541d031004c13041062070366002030550143c3c0d15064000c84c0403411072a081c2c4c0502220180000490700700000101000b0302a40403014000700820b5912030055450181c50b1100480c240c0038112000700c1e052215281c200c800440941880030f421101d180c04291070715410070050300400c907216044454200415142409000201d16000c213400b00d100ea24040000e80c54070498205480140403a01d01203440e60041c13050354007659a041299404c050b0070f2034010000d500001080f4031810091001c0341580c200200d001514000140000c0440c5 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 831832176 1250 831830926 831830939
    0x10e1e091504060608190b06072012010f2f031308070305131a1219020a0c171801051c14070215100501050a02070803030906060a0e10 59
    0x48024008a6010040c01c03142180392124820301e4000c1030240e0354001c0743d0910740e903885c40200c0c110021440c9030b41024103800c0c03142e40c0c1c203007281d80e01e036031003008c207150218079050000a80c0c007084e0103c0c0d803001c503429007140ca101741134020f0348490f151044200b10b00104001d44246a145580a5507000e0690712103609c100741001c0c00441d049164104400c13860142c42d51040c0c001c0c1d010550480c006070b130100d028103c4460520440c0098007440300c100c107102104a02c0b183c518042c008520846100c10000b10700101b01c540c10540302d280a100055645144003c8043c02c40840c011049030280c00300031025205c0d05816060b521841c407090041d08c03c0c50700041c011102c94001000d19859091752b095041a009968443d031450301c06241040700151901c82400b03401c0a070094403480c03083c04454104080c10302142121803d071030090804580b110b0804070200d00d4648035410415641c0b0001051001c1c89000050340340c030a02044801d10040f40d110040d205030000305a4a1900755002c80a052055 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 831833426 1250 831832176 831832189
    0x1050a02010b060327060411130b0d24061a0a030e01020f1e0c1f090b070206090721060506010212130e0c090a0302041a06180a1508060d060f051e090706080606160507060e010e1e 78
    0x420455103000715184075150703214740c01c9070710030800003541e030500095080d070f10a00303182403c0c81a020300d680c0e0b5003401c4403816101d445040b5484a0504a240b00c10000d1003c50568468004160001007203081480d2048019560f5882618107040c68804d84800103005440048400307400c0103030151502d520705035552500e001d440050b10307482c10341c002d00c0c3d00213200250490280c8030320140e105041161a1800c4404c0c86280340190103005004c800b0080d000c1a0744582494404803641038600107980c0c3c00212042d00110386c42c030841c0d54802c00c002011a40203e00e051103012041c0102c4283c1e012a5482d8809000340c1001a0008042801040001e80d07a00d0009060910300c1c1c0185000705a0030540d1100b0821070310100c071030090918005400c0340ca40540d0700002640076062000610045007000b0028004140080c5114801e07140000c80e0b100c0c0407034007101c95a03103640c40350485803015151840034101030410003031503000864000803054946494030072018040b54042c149a0a0045141030008 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 831834532 1106 831833426 831833437
    0x60e0d0c020414040807110111030c0102031b071713121202010c0908281a071205011401050a02010b060327060411130b0d24061a 57
    0x240c5c44a0494411175002883c06c1140514480100c45002c0000d580d04124000410039184120301500510b001742c507200e00003070754482005c101b8403050107101c030050802d880b460140004003206600800c914141c03280c0d000c0b940c60302d800ea4103920b80c444030000c03100000c51146069200d43c1c28402c1400412592810084a916001540f030344c070b8800c00e00148880e00e9111141e40c60307001801000c4541c0e0303441042c00052203240303000a0040c02c0c049542002182d4454000000c200d0248100350582e8020031781085050410700044a5503006590301e82d05540d682c00d400c12030707039658001540c07180c442c9201c8490411442d4071003003101c5040b1200864250f00640500c00051144501c0c91f040400c02d4070807024803c0d19000660203445403a441a8002c1102c4021005100011403450952840c9000702c1503d103401c2c00100d4100d0701507100c1c10326940440b00b000301241e00100c000300f5 = true := by decide +kernel

theorem cover : BRFrame.Cov 831654676 831834532 := by
  have h0 := BRFrame.cov_init 831654676
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831654676 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831654676 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831654676 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831654676 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831654676 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831654676 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831654676 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831654676 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831654676 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831654676 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831654676 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831654676 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831654676 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831654676 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831654676 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831654676 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831654676 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831654676 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831654676 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831654676 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831654676 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831654676 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831654676 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831654676 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831654676 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831654676 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831654676 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831654676 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831654676 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831654676 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831654676 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831654676 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831654676 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831654676 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831654676 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831654676 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831654676 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831654676 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831654676 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831654676 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831654676 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831654676 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831654676 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831654676 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831654676 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831654676 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831654676 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831654676 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831654676 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831654676 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831654676 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831654676 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831654676 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831654676 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831654676 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831654676 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831654676 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831654676 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831654676 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831654676 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831654676 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831654676 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831654676 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831654676 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831654676 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831654676 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831654676 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831654676 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831654676 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831654676 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831654676 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831654676 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831654676 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831654676 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831654676 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831654676 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831654676 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831654676 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831654676 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831654676 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831654676 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831654676 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831654676 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831654676 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831654676 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831654676 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831654676 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831654676 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831654676 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831654676 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831654676 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831654676 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831654676 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831654676 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831654676 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831654676 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831654676 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831654676 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831654676 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831654676 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831654676 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831654676 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831654676 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831654676 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831654676 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831654676 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831654676 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831654676 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831654676 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831654676 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831654676 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831654676 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831654676 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831654676 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831654676 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831654676 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831654676 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831654676 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831654676 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831654676 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831654676 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831654676 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831654676 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831654676 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831654676 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831654676 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831654676 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831654676 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831654676 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831654676 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831654676 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831654676 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831654676 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831654676 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831654676 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831654676 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831654676 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831654676 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831654676 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831654676 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831654676 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831654676 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831654676 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831654676 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 831654676 ≤ n) (h2 : n < 831834532) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
