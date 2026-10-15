-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4029
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T11:22:29.814578+00:00
-- url     : https://prove2.me/submissions/53f29d75-3911-42a6-b75a-521c9e438a2b

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 724460431 ≤ n < 724640287 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 724461681 1250 724460431 724460441
    0x9050d12180809041b020a0f06110c010509010c0c0b1506070203060a050411040504111504150c050c01170411180c0c0c060f071709040629040506040306 67
    0x211412900c84807aa1200030140300380703864480c42060407985440045007480308464042622032174126072841c20f10f40241e00010301c14a840d5010360204d51000241c50000c024080c102811400a480031910340b4080506410844c400e03858030307001300100d00c2c1182044071004840390001d0f2969a02201140010640d02c100e41c0119a0280140c1e10b00300151b40402d282c000212440b4a429580da07040c0410468500400e040d0090221000c0c00305041035140c4040c200c0c3c402640e00e10441046599625918030b42c1c0030f8030014071010400e0313075055405040150101c2c0c0d20764002c440c3c90080319074041fa1907000e1121034000c0280c0042c050003540d00e07603641d01400d11010742c2c441d0f4171140220301040c072692190f801c135100d6802610900d80b44e202c1c2c401003514064060040601c00c00040c064044015141804c1d80c19240d0846003c00d58000d00c448561028400c2020b1241c01c58148000440d0b03021903c0480300c6980200c3d8407081000d00c600c2e044004c6070080d400b54541c4101c00300407c0002c02d07296000 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 724462931 1250 724461681 724461707
    0x1710021c021803070e01030b0603010203060117040c05190303030e070614070309030204020d09050f15070f0e0916080c16030804022805211e0f1605120109050d 70
    0x140c80b40d015094000b91408609911864000000200601c10052105031650300030200350029070440c148480080c04080f900751070510150001300c0042c05010600820100400d409800b003185202001c6807109010707040e01056001c40d00380352502c404c039103001403403904888040d031300c0c100003400c8040350115550240c0c8003a41008411000400940d803640300401840c10216030004038030985291913818503013000c50300003031a000701e8000d420f00100691025808143e07450b20b82d420600485040e98104108140107070041c1d0110100714021685000c0010480e0b03194640102603515248640c6685c400c1207042e80b40c14113541807980009004540041c4c00910050010072401c080800c3d240d01d140540c0510700e15101c01172002c2026041211142c510702c1185c00c0020000b0401d080b5285da107000e0290840190500158200e0010406002100060748240143c1d4042e451000c00c4221400d080e004040c0315640469810019440c144200e603078482e13002d4040c003042150b07004250740318075912907 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 724464181 1250 724462931 724462957
    0x30c0403060e0a14190b0901090503070614010f150302030a02190c0209060406060804110103020702030f011b05030f070f030b04060b1306030b0a0b0a181710021c02 72
    0x400400007416a000e410b854003000c0008103e01903203402c040c4580d401e141d07151402d6800400491582c101c40007035102c0712640082e22811540c960794810303401400812409000e50102040080c100209a042203040020a00f1119040c1e42c9943e05410b110515224105820318245031184000c2e000e50080c6501c072610708401410400e000b00d0703c042101c002e13044080020340b000030301d0045103800c0d402c0a41040c1c05807010440c0c1c6040c82e1002c0c0020b04080d00140150080310700303480b2160311940403513242c0b9901400380c0d00300e500707450710480c0030300002e007551900c1c0b034418900701ea4074620031400c4d039100c1d9588080300f0050f500c070352000f61038914040040c0001c160311814180110340303075401040c000300b00b5a03401c1c543c0e6030f5120100000040294024001705400d015076500b25544204495060f941100c8102d070740c07a9200300c0203076115811101c990304070780122000002c0c0921002e403100068003200054032681544880000128443c503100c80105500070711080c03654114690282c103500d5400c2c2 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 724465431 1250 724464181 724464187
    0x8031e0a360311030706030b03071205010219090e0112170309250f0b04030c2c0c03090c030105040c060e150c0606010f1107030609020105130312020c0a031205030c 72
    0x1001d052014032003034100303864070010100f420f51a81400c01c8064020100303440e007040742d0001c1500090301c90314948103001c003010075441841c1c00e121013907048400ca10b01c211091984001c000c08049c11141d00c900c906480d2900400000130300d0f0602c403808010701c0b540184d03580c039507001d014406191508007802110661040c0f102da01c40515030f6200c2c10103400080a182c140716032501c40040e4a4290344d17040300c84006000c0c48200000384910300c010f800c4e01c1440d4542600d440390819451428041815072000c8900c5030424010038a054000a5004407800c80030386440c0544038042c0f509844040c2d600034520300c1b240c202009403901c242c046e64415a40103109034424281d543c04a0542d40240314160760b29040501800032039a0040c07c41d00310610039081c003003546004030702c1d01a1544680e21024158035125110b4104581c03240f41155902031901104145041e1213041039658440c0004208000d8860440180c106203051551041260342c001a2040030b07401e0803408079100e410207800d1034240d036024 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 724466681 1250 724465431 724465517
    0x7020406270b092703070f2915010c0510050f0106090605073008010f050111060103060b06070506090120040e18030c010608031e0a 58
    0x14051100240485240380d40d00a07410001d0000103203600d011149041d103480d000c09615243e84401c1ca1384100545192145525110b03142c1c0b00e94440390550307407218013000a48204102c80c00a01c043c129024030762100d440643c12a8036411050400c0300300288140040005040395160b280030508164185880001140c03070b80e4440303107091910f0010b24400c0d0b0b2560100140c410321043d03e64014080ca1401c1c2004500d080381c041d1151181e400080c164138a81140000d01e07405160410004001e00404950039001901e0003e15030042801071103900320400c0c000203960741c4100401403030068000080d100d140d285070b40fa00005e00d06007655a0704420706200c080041581032203418450f041450021070004025144511743d0980c000580e4910282070006000d03407100c40040030b03801b0f20443c08810400f208040214918080c00b01c80c24a20341c2003041c08100c0c0840480039040181000c08a03104141008080102c85e00540c001030002900c40c800500c912500f405844d80c22640c018241d14a900171 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 724467931 1250 724466681 724466689
    0x20d03060605090d03110115031b030f06230117010e0c06120603070308040e0106020f0a0309170c152802031608040503420106121e0507020f0303090703170702 70
    0x11b0230b0200b06000700300c440c1c20810701007480b010361995010f0000c0820401d05595814644800281000e0030076942c880700a1048000718a444c1010403003183c2d0404150b03500d4132000c0c5014185504038006500b8038011888810001840c800c544100401403418201244034500300280010015941442449000004108005e0040000d0102100e00b90159030408401a15143c2a01101c2c0b41e036900c0142c0c44804203038001e0204003075554a0403801050030f1140d041528017844248850752003d02c015081807404950390042164040700c007103460303410120001c02c0c40f180716003051440250308208002102c0b004201108820103115000590403c3d480720003081c64008440d40c030320000d803603401107110401ca5407031080c0345101d90740c80240113258620340d07031101a450602ca203009001c0e043c000b81c0c00e001e03010341010840c0d6620107103074406000122405800b4000030348190b03004d40a403110041d80741341c1c0401201d1040c124100200310700ba1640e900c4100030a14241d028014290601c82c04006030f031 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 724469181 1250 724467931 724467941
    0xa03061701090b0108070506030a090f120e0418051507141c0605190b0c031204060911010504080d08041103011e050903090f06090d021f020d03060605090d031101 71
    0x180d08400002e42d0030480c03500d0600c107030f0103800c000b41c0d07584180c204100703a80da040202ca5101007400300118404c2d2003072501d5111405106001440024281c1811803240c2c3d210049917044d1808440031301200503040c2c40800501e1040c50082d099400c00702010454000c0079002980041551802110002c807900c030802158000310048001e640070070a0f02240e001a901519002c2c0034102c0d41114441c0351700704e081d800000b0f18418012600750100b00500c20305000c1c020780e522843c0c3c1007901203c0c1d03c0c0c82d1400c00d009000c4c3e981e048404100045040c1243d510a0042d101510510001400a444404400d68020f24020030889110000c0140c0d41580d441c00e012b808801d00c0c08144080e10720502100d50340070b8440003010401e1691003401810120f40c1c44540102d403150301070302d105940b0039107140418074801c88220302a41000c6210390345070030300031070100340c05402e0000e0b400d032102c42c0140700c0200d003900c40d02d00c40d4100080b41441071070064588114100d98140c42418018480c401d003010003400d4603 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 724470431 1250 724469181 724469219
    0x31207140f060a0515060904050a02042105070602030a08010611070506070b07080a020a140f0c0f07090c032c010f0f0914060403051b010b031b01180e010501050a0306 73
    0x900640c00380050141c05000c0c090f00300030354214110011741010f0100b030b028000c900035a407003039454001145500c000c80d412103020b4940b0402d9414076085403000d04c0761020014004403010b12a841c0001400c51010043c0c9044108a0741d40144913440c00342e0403210b501408080030558004c1d0345001a1550b2550700820165120301e91750122480c0000d00039007a801c00500c00f505090041011442d8a5400b00c0582680740c0003222454543c01000c00d00c0100b400742d00d04040c4240304030309445c840810000f41c4ca00840340890000d024041c0582e10403000d442d44051a8590b4220340d80c0e4111614032581914098151410300000c0e030041a050100b040d220140b091144296039101da81080c002021060052292400000c00c0d0504196070024841e2040900342c1d090080101c0310701603003004c2908903180b60303600181240c030401c81100c15400c0300c01e1031082040c08100070203201c0c91440216040c0104031003229400e881c1d644c2c80c00c2c006407002c0d4010002a810582c1d107a0f008981d40b00c104031609152 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 724471681 1250 724470431 724470433
    0x601090b0d0f181b0b0d0c0203070f08271806040b1008010f12050303070e03030c01090b0105011d013911090106111c03060503030a1106010b0405031207140f 69
    0x43c16680c1000306041d0083c0749400d002a14040041c0100d865480031105040080c02d80010300c0101031104070b0541c02425001406420211042001d0100303400240c807243d20311050314004448170011709181d10140115168108002094140700c00082c4110298010005040456209500b81c0000c0d0442c120004440200700110010303c84102c520b1403050240405000165800f0703d5519050340d6408020010344c2040042d00340728209440602c1680c40c07030b50f003140c001d100840072498511031118007401091700041e01800c020f003e1462402500400c0310741a103a0301050440281602018010441450408500200c540048c800e0462010300014001c044103109001007400300440740006070b0000c4204a035813803402c240004003003a258450501420980c0c001a10303417105034003514040e406154980008901c0010894000c030b8042040c850031415110180c1e219605251180520300403540c1641c005010f0b18800c108540090050360f015088502210b00b680c0351131850329080e10790110076 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 724472931 1250 724471681 724471721
    0x1d0d02010e091003033c09080a20040c05120709080d080f070c030818010906021903060b0f0a081905010314010b2718060702011e050601090b0d0f 64
    0x50640c03011065a0501507006e030b0510300030b80e50101c00d00001942c2c040303da22543c1c0300c20565005001c3c1c1d0214005112200076103d0810340c5007000c011034441d070341e8181c0340411000e400018a2402c4d03c81c042c0200540e88030f5a0510f403840c0b02c0d1000c814030040061007400880030000c203212900b00446900050959984046481c1401040d43c40403800b0f000c42003130010036040a00003d80002543c0da002803000c09404124405089850243c48440360203400315100050583c038900b00001e50b408002d046440c244040390340e0340070042d002c0c462009200031901d001d2280d114040d21400c01160881d264490566228038402c442c041110420790044680b080308603082d1800c04403e010b850f131214000c545e4002c003081c0b80c2d01105a524444164200f03202d40c14400690701d40280700040f1000445134013100d0391443e011002a0003030003010403031008200d4540b510700084100780100c91081e9410317929034140903c1c19800307440c00e03002005800680c0e40c070340700084403081c07280c0b007041c29002902c041c03008 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 724474181 1250 724472931 724472933
    0x80d0201060f03081b0a061a091303080112021203030a06030c0f03241b02071d0108030d020c0a0b040813050904110609210f06071d0d02010e091003 65
    0x1003103950a0788404402c0030302100400115a80e4001c1c0c58030032464580341004c00800721540c3d410189054801030842d8a802d4041808001c1a6021503d54409403007000c0320751500c8101100c0a48100c1c401000070f55604014032030350f04200c47c00950b151024100d01320881d5000556070460f00202c81e6003415995654040090110002c141c0f401843d244094016060540c0c071a000e0504060900c801c05e074000e40b450820001d101e5100a404094040b08000c0391214810025103030740c4d45202d590958003020141d443d40c0009000350790304035210780f030003103240800e05c1d80315101030341000302c04001c1802881d48044c00703c0c900203040351007144213503001070395100c00243c45000184650050360180c0c0e0b00404100000d07003011003a00c001d400860f8580d031114040000220f01a40342c002c0c00303061140b56602d00c1c600d40c2d00042e40c4091104003074305403055596020720840740e10342000d0700b891040041d0340c04444c041c140080c1c540800c500601d00140071203024000f0030f5584005481c40c2991110f1003400300 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 724475431 1250 724474181 724474183
    0x509120606280504050402010e030a0b04030e19142404051804050309010c0204062d060215010303080a11072301050c040e06030a050619110901080f0a090c080d02 71
    0x90482e1150340030400120300c0720011015104094020a07000f140d80b40b01103001d582c0109081045000c0c010f0440780c4518081c0b03480c440d10706065800300d000c10000522114540380c070056030b40aa0841700c441e0b240c02440d00440400d1002c0781060b00303401450f2442c42128803a850703e4803110302600041c04d603a65624190070302080b5030844000c4560652402c00348000148040122140a8424607041e06402080d0001800a110550000c40b40c104140c4480e0034902e5081d840401e016403010340f440826586800a070b803585c00858202e0a1a0580c0d40140000303800340480580000c10400001a03040c2c14240040c9254000341003580c900455039880c01d5000d0010030b940380c511958100902040c00c0010a078060b07809103003d15a0300702d01c08000a84180c80400006880e140c00204640300c078200b0900202c0111188407541482e9803d0449a41190110340c080320300ca59810303520003030503540b404011101400c001c0e0601212980f900031070000b08134400c800c900030b032001d4400341c600308400c07400103 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 724476681 1250 724475431 724475449
    0x806090606060304030e0f12030c0705090a153c0e070e03032d0318070602030306030c0d0618030503011508011503050624030f01050f130b010509120606 67
    0x265200706810010040000c0c0d06c0300c0042100d050039949403108002da01c001580041c00d9040a020758480803441d8078925400084500c02c642055944c0c030b183e40c54101c0792130103840d2070407001c480250300c02d8020000e07012035288254071488000104070b400440e420801e010005800803103a1440030485041c0b0000e0304a452135034003d02c003030a10418840698012a840b409034042a44d141c03030141c00326840207240341f501140240420018030342d8a2901080e5100d035900d00c044903a04903c01ea41010541e240000101d03401b50000030b00a01c10711410f8420091a5078942c00229810340d25460b08640d40c8902d08070300c203a018401e440d09900e03903043c103102c0c03080e00480c03c6181d01000b05a0004000500340c00000381001c0100c0e1070041500c0e80e030300000c20300c0d00c80d01010740d810b4a00c1c44c9010071880d1f00f003035020b940101690850307250140d03620b10800c04082080081c0540c4114003d0440305251070b20703802083c1640060500b40d003051202400074442403800744100309180c00100400041c3e18000c105 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 724477931 1250 724476681 724476691
    0x180106080f06060c0d120f060b0d0c090b070f020d0614060906030c1c11060d060f0f2d2105071502060c03090c0d08070c092009040905060108060906 65
    0x243c1d90500d19070343e402669540920000750207001c10041c810f4015800d0b5082041e034610001000e1120342e50b1401e08807442ea009042c00007205203484260007000e803041360b00307200303c0d20201161802c00310b0a0b201c03e821100c109001301d030710801e00d03081c1c2d00000d05507001d41d440c40a4032848612062403c00140907038464010483c501c02d81010900724a070b130f84e90310b00214103480380c0c985001c079a8a151030172000300f08485944603071085000ca400c1a6401a980011041c1d030460021002e545a031800d000b200c5a005001d0800901805480c2d22500105805010212081120013681d15651103100c0da10302030003103400020844900e002c03001446010840d17040280310030910700402c2ca4200c80b000b034462002402c80e6842d80340000100b1240e0320200070b01400c06100074024075501c10b1529000500740d2201304119900f0780a02c40020300e10301c1910038803009a80c0b2207000d2201d84034000401000c0d41c4054009644a55240e81030800708104200c441c0c040e088404c0141801c0c10b08030b4240d841c2c4080145 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 724479181 1250 724477931 724477939
    0x305010e0709060e0f0409080c0f070b0a0c060f020a0c06180305030609150310020703121b0c0206070c09021e07020a090c020a170a1206050915180106080f06 69
    0x1444407107a808a500c00440f0250325040b00000d201800080e1003200c2c0301c0c6242d5100382451420703000c1c0903150004110100109086402440c41c801985403030300e5280c4a141030840c020b01c60503105d03601400030f00c0c0c4402d200b8080000d400200038420400c070781280d203691001030049e50381c107010070085100c0c0d00e031030002c0d184608086c4c0d9541d9500a009100007030026010309144400718081620000041c060341d1002801d48030751403446001c900c002c0d00300060076000a00b000d4203801c48110b1030302c40d03401cad0451303400c0300d141c20741d80680e10980317042ea5403c004a0300008104640c2001c21501d81441c8042c210b9000e01581c0c038006104201040c1804403044480404e003000070600603a207103d10103003250078400b404680e4901c4500c0681c03c0200803200948020824030032190780c90200001030820b4180c0c0d07212502440540044502265524020035400107203850218030715280744121402840382c02844c01802d1007000484002c228020781c0010003140c82c100500144100c80004141d010700159 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 724480431 1250 724479181 724479209
    0x32713090818030a12030c0306061d010f021015030302070b120a050a0605030a030c050105010b0c070e0a060b0c1f090203031206151b0f03030403090902090406050d060c030501 77
    0x626040076501c03542d048242401d89829044070350303450a1094484281d04401c00d40c245240710a8050043e155240b0080c0c0000d141c100003140560181c00d6040c0c500c2010000000b40c0c1d4600401500c42c428201c030004150b01c40c4165201c070785100c0e409091400002000d0101402c0d145240c064a0081c0b2a0000120300e44c003408003030340c1c4960004441d98400f1140002003142d0311003045c0e060040000782c000c10340601070140d58009160f000745118100600c074000800c82603903987c40700c480501503040618026009036000300851141c0d41741058020680800004040d5940c1d42207107090f030b00c074604003180b9800440d440b45007140e145c9410035400c0d80450050120204c0c035800030f0386a01c00c8400e22a40c14540c04007240c15500d501150145202c030498001e070ba1130240b00041c40e003081820012400c503104455140f0910000030060728082c56058a41c6400c00303080c8058040a900b2485031143c1140e84c074680041c5941c1c40c488200350481c0101c800143d03141c40c07a40001c2c199070b0160010700e1410846 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 724481681 1250 724480431 724480433
    0x40e01270c0e280b0904291b030901060f030b011a03100b070f0c08031201121e030e1801090b030d0504150905041401150804032003271309 61
    0x1049480c40c1400071501040c014208840b94040100713040d078512a00042c2c5030b8100400c1202d45840d160030b07020103601c2c0a98030307140507480420101084503031008501c00c81811609049580018681021900340085400d98035810304600103403843e40300303442c030851304401003094280a00806641c0c901482080f072543c03811159904040610b0721034000c0e0300500151784018070440444c0000c001c2d03400f089868520743e49030310b1142c6d660058410f4001e402905000018030416402e07032585407542c4031003802500248103c50302e41d9195040410740901102c2c500140265540406400300001030320a1034001d941400c018004464403158103502903440742c240b05250307540203c156011148050039406050b00440001c4811100303e6011503009802c2c00b182c002d008415107040e50607684030b00c0314003882d1400d4450484007403505850140210304c10580c103040014441c100c0f24a0820351104aa241035a1218074114900300e42910811030424000411583e181501326110000e0003d4410f100c403205c9 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 724482931 1250 724481681 724481701
    0x70203100c08190905071203021510171f09081b0a0b0f071e0c020d0501020d150e07200f0a021306060503130f0b01030b01061e0509040e01270c0e 64
    0x1d47c00380145518420720f80808040c420001000720071240e0203007079407508020200b050034400902502002d1440d0130300f4410240c600003031515101462500748101a410529100d005040c7c14000791280030040090081c0351031481c1000c0c11042a0f94010300081c48181845000c081d000380a092428054205101c0426801150841c4036100101c01651a4501900540f111051102d0094000101150090a2003019030252406d1003a0805c01d2102900a0b805035a074410240030306074072140340350301080341c15100e1018030320010b0100b00204101c0034921140c501d49282544040c10781c2c1d2044021000b1420510141481d642860074184070140c1400000790407030000401004000414540344814003010034000c028254200e86224102d5840781400d06541001740181404a201940c0c03802c162443c00301c0c00242804143e403220b04005010040002070103d000d54036207030359203d0b089003115820088502401503165220050a90040d103821202064103501007200b010300002045041d8007 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 724484181 1250 724482931 724482943
    0xb0114010e060315030f07030813050402030601020316050a0b09063c06150a05040801050709030c05090403090f230405060306071101062103020118020a0902070203100c08190905 78
    0x54010840c1060185000200e071405d4002e1012203e0781c07052800020a0200027401801d4600c170440c28601c001c1c0d200c0c8281300c240c1c4130954000d40183c0c020072001c04440b2200b42d00300c040301d110f070040d29200a81911200e201301d13401d031a44147d0b900000107100c0f200b60110416082410340b010840c8140603101c41000e200c0e0304024001c2c00700845000000c4480e42c0300d28201d8186110707107080765200c0505040051280d0424040e20344990302e440c01051187d801201e07014112a445a01c1e00107050400e001d01c0304601020308110240711940c1c00c08155101082d6109029111210707154481c0031054189007000148030140c41d005a1a2401f030003086d840100f0010b0380040380303007000c59aa03204c0459450041000d0b030711090321403041c10103084480c00c1810321058064005d500030b0109411400c04000d14410048000358084079400040002c08400d030040c0c90500c0c001011b41c2c41e40000c004110090f96154040b14000030303009400c00c0406440e50043c00b0024080c0041000044980e070b0310349684078 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 724485431 1250 724484181 724484191
    0x50105010e240f09040b0a0e181906050105100c080f1c0e03030a0f05040b130f060906150605191206170303040c0b0c070302040b0604170601051003020a1b110d0b0114010e0603 77
    0xa900b0b080c0c05403411300200102c4ac034459603451420101040c0c0e05280e00180000e01900d885505d80c2c4a090125a2250511464494211034a14500002450b1160071640941081d44000000710401080103405209a09020110350090b581d2840c0031803d0008864281040c3c00484d4603201c14400400d60040110348c0c08800f070b481c1e28200321414100001c030500b0650000b0556800e02240300c0400515401c0303640d115900d1030701d04000d00e480c0c0d101170301c3c01e0040b0141c00c41b4041c80d40729107000840c42070709002800884090300103111500c82d810304010300c00da03544000300d0703600002c244010031102c0c0c0b2110005081d0001941d00700b41400304070b90303203405083c40007900c99601c81c00040015a91041100c3c001c080e2410540d04191648040a48680091292902c101d0707490f400c04203030501a000701c902c010001d5861448440440c44120b40c3e002048500340c4001520941a0a140d220640342d00840c030b014101e840050341c91b18540b030038440e590a0581c0e0400c1240310003d11a6110407007a01e80203 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 724486681 1250 724485431 724485451
    0xb220e28030e0a0b070201030501090c12051b0f090a050a030c0e0411130515030c0a030206070c0b040618240507050a170913050105010e240f09040b0a0e 67
    0x440e5060807600241c0c005074403070784030009000000e81268194010000c2c54400e0300d003444283e0340d817aa610100c800121824001c1024180c0703001e00c4240302c0d800154000c0e0b80101001c1e141d00764504026071900101820b12003140c00043c020326078a01003041d00c0090508503a1020501d081d5605c04a180c480e40c4100c4440c5000003010408000712014100000000505600d0288017401e0300000580310907542484c0c01c0ba61000003680354100800c803a080580040e0440500798030359401d00001d80e0141038280c402094111b80070590b49541002000200081d1361000220213595100b20507281d0254400390742d41c01e4182c1c1300c0d22030052984800d60403841c0b60030b100d40c0764200e43c2071071030414003050401056420621054295010f40001400d01c01800f5140c050399140e00c00d403241304a0740280141404600d60089800c00741c42c04035004d00341c1051005944080d5041d0351860f03015900a007d9000405a0100e0b00083c40d00b054860280b00c0309007126866001441e2030844a2409006045079000d = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 724487931 1250 724486681 724486753
    0xc030f031b101b080a090b0c0a200a03080c1c0905241503010b030613020616030503010303080c090904110d020d0c140a061b03030b220e 60
    0xa81c5006108030001c0c000140802c0c485500590044004820307110b10b07110100d010000868111070852066900c13840c0d10482e400043e444807404141d443d00f109034080100a46065072070401e010400c00c14402c142c0760f4004094048480c43c01820071800104102c200800a00490701c00665842912450074180138001400d091035080860800201c0340c11145c40d0b00010404903891022405a00e114030314814109001d001d401081609807080e61004942c076601100100e0000c5c0c107503034403402d8440e00c000c0030145016603441401241480901c001c2d40410004001081899003000710541d20840c4109280e10b0481c102d8001101e1540c0030b03001501e1402070342c60300201626071118441c00690005c1034815001c000345401c60b00c0a0150240070143c541c51003004180e410300810322000d40c0e00640f10008000d805e001385540f1460340780d000760105521010180000e4544103d41c019801104041c40080142c1340d400105440352807040c0310307003a03005850400c03442503505861111844c6c0c841540175 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 724489181 1250 724487931 724487977
    0x501050f1b0c012309151b06010f0909020102060a0b010c0b012309070c121101150302030c01050c0a080306040b0a080f0d1e050309010b04020a0c1208040b15040f020a09080c030f03 79
    0x106c80c000e0703064518a20140740d0921505500c0054a02d0483e200414001ca1150b16454400d0079102d450b01e00902503402080480ca01b50354542014501103410326014003000090744541c4501402070380310341907610580041e414030241044185021507015280c40d05181021080107005855682d4080d0840e203849840b4071916115200045803040c2c1c6000070302130700e6a04d41e50010f4004103817200b24880c1c420300941041030350290046d58031000261000c1c0000c0d8105031076100c241d6000400f080d500070750f07035900b0700034554905502c00094414080102400c003242c5000c103180c9220a21600d040c0010076402c1d89181c02c00800402001d0454505030b500e9803500f803051800751902c044000d40c014000701c4c400c034099502c140780b10025802010141e001d42c1c5c60400a540078207054601030694414200050418140100d07d406091409000000d408038000c0b042422604083c860300000380d0000d40130040d4483c1004160064501140604200e0342c0121000e07175203200d1400816034002007029169 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 724490431 1250 724489181 724489219
    0x8100b09010e060318100c05040509071107030803190b130b0316081c0503070c03030e0a02091f09050c25080703091802030702070501050f1b0c012309 66
    0x805408007402c0d1940328180a030803466250881401007210f845050f10800e01170519010301c07004121f00d511400c1c80c1c03505000501148020007000b8405000c1d840d4207a03210440c0030011500194040d0601544030300b81030724420140e900300404407200b941000900b084a0351104004540c4205028000038071050000100c0d0400801044086606d008030a0002d41d448020070207140710104000c1d0004c44503590042034940f8001038400c5400141c0750700007540003d000381e010480105800080320b0700056107600107446004105c0761000b80c0700306500ea030074160324003902c080c0141c180300406001c60303e807010b061503950180c405054051a10900c07910700141c5076030601060180c10031581ca56070801428060038031007903881030310ba640718110703424074162100d44252070040703015901500300945072900460315508003a0800c03400260030443c00f80380d90b03040301501c1c20124610021382588031150001614541100080400320803c8100215020300000112a0100000c4442980d002c81c2d500d800c0e = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 724491681 1250 724490431 724490447
    0x121203070c05060c03270c1011010e0c01020106050102010b0f06070804120614010905040b18071503091e0b19020d11031b09030304030b0c0d060f1508100b0901 70
    0x1405a0140700f0034011900460303401144944041c03500b11209400201c40b61151038824040b916207a0402da038810340c54507140d0007402c103101080c54052107000c2c01100a508445014480504a62100d0180c09071540c082c0115001000c00340001c12010001101007100110881500d9220f041e00040324003c025030b88003904c010300902942c803103928495144c410020240403010103501400b20000140d192020b0090910a40e4402541451500d50084c5660000c3c00503000d10294000c0810104100c601c000e100301511010f9600410f8000380d50230f00003000284100715a1b680c0390210354030320120340c1d0744d00140e40000d2110301002500c001598198002c0c011027110a441d80e04014141e007041e6885800b40d40101c510200a1141d810780384030019161041542464054100740002c00124400c66040740d4400c3c04400c0d186d261400b03c81c0803d013111002d8101e81901500399105000c1c4200b450303040c401c00380040c10003a02a04000c2c541f150711131014420300070407000025000b51564443c07110 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 724492931 1250 724491681 724491683
    0x1d0f0a0306140f0f0403090302010e030106051002070e1012240612110a03051b1f02060417040501050f0d0f09060209011116120f0807060b0f121203070c 67
    0x802c000440680398280142003068804005a032142c10114482d83c4c014404903000703c0c0e240e1038142181e40366a00646030301410342f00ca640d26550b101c00000b82c13500d865000c0c4001c04003c0d40a051340c035082ca0001d68055101802800703107410051401d01c444034051945815160700250241c0280c0d10380b14070100841700701d07000c0c800d0b41820403c0009140c800e1007170f404102803003030003c060500000418024030090b18400607095510182108001081c4400700e0418040c0103050b501007200c050300100100340038981030100585c4050100414040007075140a980e507490b6902c545041e103800c00080c51030040b4111a0082c801c0010b021040d01e2466000003400400420107200c4404141000350081d0032501603d404250050b414582410b4045021303410002c0300c68400700b00d01d0602c00e198000d080f80c00400c4410b85e2181074048080344010001d0481184200c1001c54407071003400510540c1301510341240d001e020080d011000c51080401c00120181c40d5486281d26a51801800c0300c045003203100c = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 724494181 1250 724492931 724492943
    0x2100513150f030c02011806110405030f0a11031204031b090f0b010306060306050a170f03030903040609050a0e2a040801290603040308040204090206120709061d0f0a03 74
    0x44512260340c00c031108041c0340a050303d0400041918060a900783c0d510364508045000e0b03036003c0366000404079481410080b010403042c07401c2c5622600400d1034000341842d04181940a0700b100010013100907003802c0b220209802030000440d01c10a42c048030700550000800501c0c29013007059a41c0041541c80b00101003a45080c44004e101c00d48010080c0107483d1100e001a082c68804502107000703001e9102220b00c050218840d03540790082079040f4951105583d82c440c02505a51002060100302442c0118800009103565610f4210050402001d590050b4041d81404100700f0038a0800302420b03030310154544401d41c0b0b8401e0841103001c91600240117120000d000710f004070309940c0540c0080300031210089054032026158541d024100f4010040070351100e410000500041c1c800e054190b00984058000f1840380030560002d04250046110300b440106058100112070f030b88149001d00800d44c505140010f240308030341340c00034a042011010700450840d0900d509a80700d50160364002c640081c = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 724495431 1250 724494181 724494209
    0x103809150d1b08090607030618110d06030305030114010e0114070c150c06050c18060c03130e0703050a0e06071805040501060f110f0c04050c0903060a0b01020d0c02100513 75
    0x284001e00f200c0d1055844407814480c510020380060b000e03104841c195944070181a1500b22080180400380070000c001070340500003030011801c50039240c00750501552294950071b407650b0602e48031400203060a54002d042020600e560781599030410400c000030100c03a07050503a039602c64241601d030801c8540c8441d0144020059004255901013100401c480c8144402d0015454040e0400c0765402034401c1e00740c0c0740824a18801a5140010042020081410550b070074195500c0310100c00241e81e07845a0400c501000811003a10792521880e6403010324040100300e0380902100c0240d603200010000d0062020b2202c12242450460a10780018031004000f0b0019607100d02c0c006040425840f203040c003064800d0610015880c001c10f91107104000103005046440b00380341040081c01c006031100030005000c2043c07142648003804030034424003500302d01241c06044072000a00c1e00f58905160b10801c07800b80100d0f401a5242c40306248649004d10700107803100e034482d507503d80050340c5034080b44058080d5 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 724496681 1250 724495431 724495481
    0x20f0f2206050c0d0836010f09030e03010c12020c0a06020c0106060809030c060c0d060801090302010605190b07060903020c121c0306031a103809150d 66
    0x110300240004044a001d0300c1c130440f0389480c141c4100b03406075903100c04d581422005061001040c80100201e103800c030514821100580c0701282146c103403c8407801419125040d48003850f0b04007000301c10b101810b60003001005ca0030381c4010f00ca10781c07110044100d0350300007800300000358040107030311103151f00004119511500c951405000b41854420341012400c1c0078009600c2c1171011059898030f502d2031003e04085e991784001d141c040c0d440400d0a2240c00c2e900c04002c12a02424492007038480d2294000044160411080105a070500200c2d12175043c0e00e907500307000d501c035654191000c0560107680850040c8051400b40e0500c4070702c02106030040d403003041a1100810000d003803110301c2121510950200d564007411015500e41e800b0240087c40d51301400e01c840c07034880c06101d07031118801c0d412203001511540e03803c030b07621807403840030558040c681584492a00c407418043c3d01da21151a005c0d151411440201d40b20a0610410505034980400d02240290150f0000d403240c06820110740404801 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 724497931 1250 724496681 724496687
    0x824040f0e0706020105090307030c020d0b04060906063f0f0f060e01090308040f030e06130e090109110d060e011803020f0703110f0d0803070819020f0f2206 69
    0x40341c1d503a01c03092149850001e065030061041e203008a0b00b51018515100803038905858007a02c1000c1241c02031141c0c80b505003c038140d03d0342c181c0102d03c00d01c008140e04c141e500780300c0159441c68002400c4050043c00390100700180000c9002261101d00d61101d441c0410300d55145001070101c4080c003500c5030025150100030b0107044401d6058850042044007030f6002410380d0885400d22001008684800080b50220b0b828154030f1460134424070700200910100070100b040f6400c800080c001012841c001031010300c400308450b6921091584c001c005032503040e01e070700d103020816042c020300901031480501c081c0042c0d90800243c0c0032410f40248041070300555071070722040c4515000d80044c00f80b21003131410780501182005c201c1e50019540039101c2014002c200001055030103095203c012036440c3c0f800600c5c1407020318801c1280b030301d8800300c2d03151103070400310140e000c100003414283c030411841e0140628030058940c4002004070b095107401c0400c4101d15100f80c1d0301003042085001840024061394 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 724499181 1250 724497931 724497941
    0x1207080405120309010507081b0a050c1203032505041a0306010e01211a0a0f06081e070c08040509160905101e03060f080f15070824040f 60
    0x502550b4155000b00c8101d05280c0700d00a440300b0a002500410500b0007041c0640050304c0351001422550300401c0c41e003040d27945441c07a40c2d141143c0ca600070707054104141c83c250301891100c02940d400307186503190641c04e080d140c803003401580f8204800744108800040c400c1041e500904000602e07029109000d40d1107181603041202d10328005490006031f0f00980d441461254441c1c1e500d2042c0000da11408030440c03016000981540e09080107420b42d0070b03a990342e03400e545001045411ba611594608280c0c005107008001041c0a4040104410b44030800e000b04003141e51000c3c441c0340c01c88195280f4606070207240704a520055000101a0a003d602e4020b04007002d5076032415221118142c0d038031801d02c500900080f0000010895038000004003540042c10700070713102e0503403400044050301c60102840703401e1141c0042c4000c0d48065840a0303218001c01600301e000944c0f035600c241c40c0c9040c0701e000304a01402082800b10b02095292064200c01c0040c40c3c50250784020b1041c030080b9414800100204 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 724500431 1250 724499181 724499189
    0x3030406091a07021309020402090a031a0105010206160c0809150306130c14070c030215191704080c010f182003190c080a0b09061006020601060f0212070804 69
    0x181802603611410340c02d402141e084981c0601142140005913081800400c08020141d0308107408201e044c08554035030801c2c402440c8108441c51140800c44100515840c0581240e4195030119083c00480a00c48050001c0c108152803c0c00e484c1b9010b01d0000103a01070503071299001020030901e05040e1000c2c1014510903407003135952080810413191180196440b002c1103401040c154544800300888820080c01058001c040404e10203980742e001c161000d02028061542e5070011840c3c0826503540c1e4400c081084151500e10a011490a0100c008100c05040104403601c00180035080a034203421480448001d1941000313110104654050300303018452040700d114a9031007984d40413550030742c2060320081014005040782c0c8084140700d117900555002c141c480a03204140000d01003010807400341c80c0340c81400072030040e040c01300b201403810001502003500d040c5420700a0010560003c0d00702d0440e01c2c03a00c0e200400b0031100b80141d05000c800c3c10f0356112200300140700300510400100900840e = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 724501681 1250 724500431 724500449
    0x512160b060109032d02031002030f18060106110a14071a0327071509060917100203070c0c1d1006090302010e04060801020d0e0f0d120e0c0303040609 66
    0x103640708001100c40c0000c03408020560031000d06008042080c0d2003000e0300d18544003100d108a02455000686000410070000646079000000c00c0315203440301201a42001904102118079107500540343d8070341074140200c00800c8086180d60303090800070424819240c0d08030440ca2400e0380c00300010743c0c5440c1356001340f0704002000856911030044000c100c910074078042484407480c012815116048001041000d1300034030507040003048091b114840445411913030b4841459503407402c6409001c04806e0760281c8541d0f807960400408036040490344440a000803c80180c0d647c1e1001d43c103441c004a003e40c0071b8006032a008003c103c0080903102100c41c507401241e41d03080360342c0d41031964075540a80d00403031000442c07140c01080194000c8512046822008001140301510b606e2000d00320b03045004211103644d1180340b03000ca0240140302407009030304420007800d069030606001805600480380d29011041e41d4580b07680b6038000a00202209110040550b681d580e5610401400410240104264 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 724502931 1250 724501681 724501703
    0x50d0609111915020717060a05010b0a0e1918140903091f23090f030f0c0909010e01060b0a0806040b010f0804061d1b090f010b07051216 60
    0x481ca401c20b021000e12540741401404a03007000c0c2c2080001000500490641c4140100130442e400350203495000b030780c0750300010300d803a140000142c03081e95010713480312114038010403240c070140350310007600d1143c2c0f031003654240d034030304405150380e07111406a40c024140e842803515416012103150f0800042081d00c50039202160700c1e02c104103a224403580381184d6220103600507640c0d003441c02c40902982d103d40c5043c0a801940a11000c00c011001352100261010000a41a42901d40400148400d0409900504985101c07c82d80c80e034418203601510310490350320001803c0c1400941021006050f440c00a01ca49070baa00030045190708030340c0c100700200c1c501a00007012810144030724414224169a40782d90302e04c07100d006031a03104002d0b105441154407100d141c004484501410401050307a4401007180f40070214010b85011400c642480c41507803501c0500070040c540a00d2507040d11415513455944104600d0030900c1c00d5010050140c510700046040b4070100e4a5014000c6140c2c050500156 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 724504181 1250 724502931 724502963
    0xe130f0f0605060328090501020a080612011422060e0610090e0307060b01200f010c050903070302060f1306120609090f0822030813060912110a050d0609 67
    0x10f07075400211448415040c214003030500100f41d4244d80503001039400c00010307032242581c4035282aa4082c440c8107001ca2a0f10741402043d0a100d040c03804401c01d500c0080112a2400300b6041d0350038006440f20741e40e14000e0b00c041c40c83c02c0c4803c0d03c081125510103020000c1d00d6040c0e58607504c50340212001110813080c0140081e00d80c605014040b8000000b42c003440c54031203940e0f5640001c00c100303407907a41004410703402e11400a40d0801c8007502c04031004014a000342400b0880d900751440c01d000030080000c04e03c40b0700c2a03a10001807503001d9a03811100c007501d4040e011502c07611405030859040390071100d0900003400c541c100030403181198940206005c0c450310351a0110580340040c90080800132641e0380c040210f01c1d160007905003100083c01c0105105e40110b0000310082e000e41040c0c0d103401e4001140341182d90460100c500506060400c005000c2c50b20166101a0408100c064a0001d1803000d81115030f462010900103480c00800510054070a0308000c401029038403003c85144e1124140c0d21 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 724505431 1250 724504181 724504189
    0x806010203041206022109010527190228050a06030501210c1502030c010c090e01030b15061602280308130e2a0a050a0e130f0f0605 58
    0xb41510701c1c009074111410307802d40d2840025032104040b400f600864140440102d920040c045000d0300c1114000b060314241083c0c1074060300d03400e0311007090400702a0200000f04001061101e60700c0f1150f00750f0f01011403c0e001081d181208080b0034110240b0030310641114800c01013040c01a0782d019a8070f40c21103a200c25007a4112842030007854a1035000e240c072102c910aa03141200c1220f449512a0480317143d90740e1a80f07103804144d240d04c0c4050b030000300d110302240109110b1032034864042e15014800741c0c0381040c4034801c180103010241005205c01d0000308201c0d002c04d6544900394004d051b90360f403031104014a20081c202c101089128054100c80c01500c410443c802c9c10130041e2001c1150212859a036440e1907c1c0d0005580c860465944500020794040c070000a51058081540904a203900040b15212002500034000c40d80e2a0a00a1200e05941720094034146402030030400280d01d5048009040886086210f01c40b25040951044030324016400c000c0c4070840c40303032082c801592524108 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 724506681 1250 724505431 724505437
    0x807080613150203100905010626010302010f110307020a0b0301090e1516020c0d030c050609060f150f1207170f0309010804170408070302011101021810021014070806010203 76
    0x20b8010038882c203407402056500c1e4021600807225488a08040d50b41d40e92140c1500e000740c1c00780c0e002c10a40d45000075607021200c007002ca91000d000c0c101750150304550001c1c08400c81c1941a0f410480c6102c188841e00c0340030000c481d085600200aa00412743e01c9142c090694400d001c3c1041842c01c18103c0082090300148840585040081003483d664030701c0b903644502d8110010310021881030082641320b584400c2c1c3c0804d9518026510143c0c1803407141030091510501811403600e69210340f01304002d0f0005105070940218100d51500f900200407400101050a8445200d038080041240780e0745108001035182e08a1f00c0b0340311130a04c48184100456180ea06c03080b4032078002c0e001088145032640c4145c00f4503501c1849648080c4030034041e85904c0d18541c00dd9004940c0316441951709109568004814003882e08000000358509820682030801c001c4108450b54000c421603a1010110782c024070160304042141601001282680c4907c6904507030151080000720b0b4812011481e194404821 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 724507931 1250 724506681 724506683
    0x110a0b01140306061008091f06090b180403051b0d0f0206100b09060a051b0f01060b03152112070b1003050d05090a030204020414010e04020c070303140f040807080613 73
    0x2141140703070305c0322400d5541601c0101510304a000307064034411000030416580025010726100040c0c45420129503104036821600581d1280c402d800e9400050084501390b5a481545441c0c441e860300c5080c0daa07940c0c5074210b14200303040c60090341500e0807101e0340810b101c410344900b40c3c01c07528240c5403410303010002c0c445400b030f07001088001c03c46205541030040c0144900c141c13a02c0c0c07951030410603403003540c0303024480f020130701d16074108403400c0501c0c4009000e11005088480916859030501001e011442c003881c29001c0e000d00001540d500301d260520766003032440c0e0030f4103050314020a00032250780016440310b00c0488a100c3d2090100d034141e000303010301d072042d039500400030b0125030820402031b02c090700a101da0580c030580d241c401200588660015000a281c00f44141403c0044d95002502d01810221114002c3d84103010398a81c0d80000030350842140d8140c20110181200441d0440030b07031140048074030303d90f080080c00182412000450704103c4415401b524030b907440780b031482903509400c804 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 724509181 1250 724507931 724507939
    0x618051f0309050703020301140723030411030a0204050c0c0105010b040308070219031b081e0309060d0923060702011401090e030714011b020313090507110a0b0114030606 75
    0x600c1040d5806a84040141c500403401c1329049590385d40000e01307459030811003c410403590340078450120340200a200042003102040380039071110102c065600e020090001d013101c0d01079442d554070742e101032100740849500a00184030302c0c5480d10049190307071300c140121801980f0385400000c0816070b060942d400d49501040492400b00140c0800c1005240c030110340a012100720400800101e14044600c90b0080c003100001e242483d1000b4142444600a45030342d524501e11503003400018040121030302160b048541c40d4460140f440820000e181488006240e20440001d4401c00240c2400800342c400b1000f04507030311543c035810120300381d880e0402c43d40d00c048078240050050500c1500300c940c000c5800001ca81c01d02c0c5203611500c209003c00001c645041e590346400164035601c01e41aa0000e07140360004501e42824500c1c94800d80030180300707204489581e000455143c03803250031000b001442560481d8041c03140c03402e180e440c00c0c90a00c208410341c0c084110200483c100810400e10640d0024 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 724510431 1250 724509181 724509229
    0xe0d09080307060203100906120b06030f070905071101052e18020304020f030313080d020a0804032a03060b0420090d110a060201061701020f0418060b0301061805 71
    0x140c0d40790301a4001500d002c05501b6012400310780000350b4450b080041c07100c45040e041c3c0c49002c0c00d14602c6031b00e001c0e001c00d020b900103100c03c454480f0006501403c440d0b030783c4c40006440c0e030341e031404039220340e04411a41c190354200401d1285041c400e242005a2000101d01640b084509904a05a0f1074840c1704150703610810a801000340001a4051075005001900d024030351401a00044c0c1185d0145c8460003000c00b80110612000c507081003a4921341d003142c001042e6164103a25840024001c51200400c4070380b0900030800c1e40d01030009025210041290b42940c0e07942c80e0720b00f20010780160f40a840c0940e2503c00c3c1a0022a02c0252196095510940c0a482c110100040c040040da60420039502c4221752a4072451a0322800301c40300040c04d0306e0b400082c004e4106420107040d840041c0c440c5042d83e006010303005003203416038116003c03500c000e240c40c0243c00e11000018040d2503143d01c05503600801000008140c3d82000c0b12402080c403c0d00c0d02100c040d102d904001c244190f121000490302c3e094 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 724511681 1250 724510431 724510433
    0x30801150e1c0503040b0703080a050f01080a062a1d0f0f0d1a130204050c120121051209030105091204050402071a04050705030607080708370e0d09080307 68
    0x2d090914100740140c3c01d485c94152180b550642c2940403280880c0092400810050102d10361310070349030080e1400011541c40d51401d40540d03078400908a025180c681e84a06810840c04902075a84818600742d05503400c804961500bd171038240044a20018045e1628540c1050b10300807130f0342e40300d038640180360151003190171081c0038040100302c1c01141d8030340c1d401304a0300c52111a00c00c0c00f442680565a078412881880c0b0511003680c0c001350901b0140141070044161810641207500c1c10743c0c2c1c4468050403261307185201c800320140414006403841c000c01a0303c2403404201001001c140f01d01740d009000365210341c1d000720360301c000980003008c0d4641d051005014030b04e40782e0010700c5400c1c0245110400c48604644440d440da805035000c07202a4483c00040110b400c05002c51907008005040181c82480c0458024000c007100900c446105244e00e803402041c5500c25500c0040c0c2d00b144151100c110703045200c201c00508070443c0e5000c892107038070316452005209625020a45443c170000c1c40c107040e91 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 724512931 1250 724511681 724511719
    0x1009060e0c0d020d0e0706172401090b0d06030b15010c140f030d0609050f15240a020f0c03070f090509190c0306060b280219030801150e 60
    0x400c114000d50b40d0204500c0e15030020b1801040341c031070f1920014000051500c1e00242090307142491505172004528108410440755800007550740b10700070340d141101080000121803402064201c039042a101064290407410030364008810b50340310b00b01103e00e549421100e9698008070094190000d0f2440c4101400511070b07414141d0301c00c12002c11502040c2c500c1d08158107541202048410f5aa40c901080110305c6640c0035540c2c00c58043d40b2007110038240191550310f0000b66004050080030582e1340750311240c48044e4a100f030b100d4444c10003901c0345840c44000307484000d80314180c0c1302441070b41c507605550b02e0b0210701c1c0000c80d400d900040d40d450340f5000710309021b000003c1c14003450780034400c13602c8844c0006c041142c203042d05c50200c001240e403c51a02d101210300c80c1d000b001d108101480b01000d011008094401010400d40c0200c01030a9004000c030f00c0d00c1740303098104c880c83c582806244201a040390070103068407114040c0303082c01404424100c940000c249a0207a101a40b48003804507461 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 724514181 1250 724512931 724512937
    0x708070209193602031f2406140c03070f050d0f0f121505101707090e0f060d02030f010230070507060e1504060b030105010332151009060e0c 62
    0x840030b003c0e240c0003d108070f200682200c00c0d2201d00403840e07c0380800c0e40c0b14095801d0302e096104028402c00c12090400400509465403400360b8959401c000900d400450b20400507a00071980c03006501910400780d1500307a0b1219409040f050109148807500c0c070f1010301a45d03c5804101d0b0540e12039502c0c892000304400a885120041c0e40c05074014640401c15455160502c0a2281c4944a880b48072980110a21203070500a19910070807060300000d00c9050304444c860f83e003184071080f41680c0d030381300e410004c2d0041007040270003581489400b01b40103c2c0030040d0082c200314680c041900144076141300d1220a402141040c00d4100090000018035a034058409010003600032180000d5007004d45228507d0041020541400302c0e401d04c04020420230940030b6040524010b4009102651642e92802c4140c03103040703505494180408150132040d00602c0890300148a84011110701040044850f691500300366141e103507210a4040215001001c0e0260303901716103c05552803242e58441c80030007031a070 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 724515431 1250 724514181 724514183
    0x9060a050616061d0c01020d020f060a0c110a060c090f0515030705130602150105030f0d1d0a030602120105030d0801030615030f0b0105032401090207080702091936 72
    0x41d994140003ca03111501010419284c50300004004e1100343d00e001a1034550071a05034400c541c001c0042c40c0b1414404251b0315000703011a02c0c0810807402e080000c0d140c1d04480703070704590b10b885059403010901500317400a190b5403089860b0442c1803512256800710440c802d00485420051181c5005082e125a900640e440003003440c0c01810308540c1c1c0703520040c0152035400440140e10141b16030740100300f40040640102400c40040080b01c813441d0115848400750307803140042c0021000b02014928015040301c200703020040451340030f65100d02d8404000d400201c107101d001d0800200118090600180c030160503040c580710381c40c041e8a9540c500b0007502444443c086841c1c2d100c040040024141501080068400c0348118199070600040c5032400f0480307092440301000f00f000d2800c1c2444400c8105055568900004d6620051405c0845180c400c1084c002d400403030040401103007d900881050420307070031348010301100c4c41d400e44420080011f01c8040c0301c44003140148500c140240c101035a642 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 724516681 1250 724515431 724515443
    0x616170f04150e0a241115191e0f020408060c03060604030206071208070518060f0c0f03031509150910090e01090209010905010305061303031104120209060a050616 72
    0x4030082c3c0c0045a4103c0a9512102e6168140d001c060300301c0c00071400707000d0183c45a181c400c81c10f20b40400055a40d01c12060046030100400d00454410380c01100c2c0c0c202204031022090000050100c2804d0203405035108420055140c0f0044000c815054000c450480c1e07038a0005090b561219108441c0ca0351015083c5580440c04000000060b26180d02500c5128000c081000803145001005044500010440300c1000307003c0100c8001c800c031010071031440000a84042d0317201c0403840c00c074042070b03c03030307a010504181315001140170080c40002c011031243c10600b000b5001c59031054244000540103032000000742800c130b1101902c904104801613402107425044401180d0348503147c00854415041c0c0311001d035103400414065090603240e00f070051220310b40c00c00c610341c5141c03a003584500c1c028180c1888911500c1d50b0005151003038218001c0000e00041240d515a81c8695100c03642480141c22405054124002035007454034a81c450304a450107007038186080050602c0c0c1803440c90f810021240 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 724517931 1250 724516681 724516697
    0x301030b22060b030c0a05100509040b042f0703020c010e040f05041b0503060f0610050705160329071101060801140124050a08040f020616170f0415 65
    0x8141a481d000450140c0100000944000040c0501d41071494103003c180c052184102e0401c034549070a4421780c002000b901e8000e40302da46030800100035103034262800d98002e0410310f6425000251030034640300e040d240048032400129070320007030030305016618000d00903800c00140740c04254020a810415040002c00002d081c08035030080500b224001c4d141076440c005411b4418a0840c0c920300e00a0140108a004040c90701d40110354290030880102038a004080a040c41d82a5034000e500303030b40c40c065200c0d0680700180082c51040000c50064403054584010110500d1303285411204114130313103d285503914845968105081c0c0d083d42c86040304e61001d658400001501040a01c01c61b042000c1c9944c0c1c9484a5150245000c044d000c040c2012070a4803022000410160f0410100c40319035500e4100440f4564807400c00400d0031888410107504450001070b0503a11050b0014225030540c8200522100307a1704040303080045009014014210309030800041c850400c1043c0094400025171400c191 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 724519181 1250 724517931 724517971
    0x10c02010504030b10060201050601030b060304062703021506040c080412050f0a05070c0e190b0a0b040b090a0e07020c12030c01091a01080307031706040605030f0d1103030106050301030b 82
    0x244c91182203420340c4215120002c1484075a5080c014140c2110003403034180b01c00c1c1089400a074091001400c01014940d541c8002420307202d084185c680e1000c01809050004015818080e4690004070f103580c0e4080704500001e07000d480c0520400b91401c0090b682c00c042c5030f80b2903650801c01702d5a041c85c03000b800018000c115241d0110303001000d80c0c0800756246a1142c0752494064240303055a00b201240d0303240c2c80c04104001c0d00401414940c4e09040c3c10100d0102000c0010601465103500311169155002a003c10007680303040040000305c00949071015030319039680696001220070b490200058011201040b0301d851300404295018100100352031901a210510600f15562550111290255180b0000c034000c01042c003c0c3c0100160800b5524222050350010070075018804440c0d401c0410b41e01050007521658800710142c076000e800ca03214450311400c0541d80f12111118000091120034025034403c0e00441540e0403105951102d40c01d60342950f90300c2211201c000d203000700301075010360090 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 724520431 1250 724519181 724519193
    0x6080a1523030c030d030c11070303020c1c0533010b0306040e070e0112021201020a0c060914101505040911040b12031612032f041a0d0605120c010c0201050403 70
    0x8a00d801d070b01c2c00150b0140c8404003078008e0300388600c2440710303800484040000ca500442c05182840040b552500c00b0300b011018201d80c00c490700e01c050701c0b9114900005010030a404100c0c8103040051240c240301801032401524000824052a282e003d001d0004c6800740c246a009426421180c005860071203455092903a400c0b14240d02807124980d0840d0340c9004d509007a042000c00038241002945040c2103d51301a107004254940103040c290f8640c0358206000e100c0a0300b00604440d00152604a0303000303501000580001200b4a44c40240d0a00014161500b4400c4128555000807203880c1d142c9603008200040c007254020707503041441064142c03940c0780240000d00b0203408000400c0884505400c0c00c05189202c08580401c0c107107800b000403044d00500011179461110100713210b0600300f0601d0900f040d4000d0b9402900d0200c00c0b00118202c85142802074048044a00c2e001c100f042e40d076008000c61351040010402c015084004600c0d400c0d445403460869090040c1489c0d07203820794940c1c843c = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 724521681 1250 724520431 724520443
    0x11d0d060212091912110f071a0a08040f0501060e04050f010b0a08060610051903020414040c200705101e081e06031606080a1523030c03 60
    0x100e5850307a000450820420056560903040314645000b04103101e941e10488501042804001e4a54003001c10380524861192006040e2003101c0c4082c4d07180807401d000b01607074980c11806480000c43c22911800400c0c0a00c0045e1004072600e82c0c0c1c0c2c5019516213441c0c1c6043c100211000355040c3d5242c52010441d0301200800900880c07140340100612005d2000480c21070320b80581607485101211010002403000103040e9400c0704045845008101c0540c00c00d5403e48079084c0e0141c0401800e0400740800e80d055030240007181c002d400d501c00069034140c204000c65010705101c1c4d0115080e9441c50441c4009550b000d28030494440440f0b000716102d070001907000f0f101100e810000385841010031680703c4140d00c80400000c50f030808880c0c4d41032800c01004200140e1080598143d00c03034000988990b001c0150801c40c4406000c240c01854a40c00b0003400128100d84000220b810f103001d10f800000000b00e854100c59501101c60052440405169202500f125138a54544910080c00b8440e550901003 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 724522931 1250 724521681 724521683
    0xb040c0c170316210207050307060e01060f03030513050405090c03070e09120a180f090e010905120c010b0619020613030504140402280e090f0103020108090307050a0c0f0902090f011d0d 81
    0x2192907883d4ad1401c482a128102c00c01d01080c0d0400100308482da40c41200c42c419250f040c02e0890300d1320780c84049220341c8255644010b9005003081c050200002011542101944040c0c0507150346a44812a0307801a00c0309441322a12588511040036040203041c02520207024140380c0b0b0141c001c3c003884103015000313160304040481c52440c0d0003007242e00194407034070700c1541840001f800081910340341c190703c130138418481e9050140c00060b203640076403013988142161000103108070744071803e001c0b420860b00c600c085d400001d0321a11010400d0083c805030303004601a810b44c0e545142500700298489030321004040c40313411580910202c000c0041440f00300307080d0074140d80d01c0381080c450a1370080c80c800710001d482d8040c1100f04180144030440300d581ca17040d2034080c280034129440701c0030001d24521074424080d019014030107a030020070050300101e40443d0003816400880d19140c4a46208a2180b40c940f550300c12044000c8400550103480d2901c1c6d4407042c005e00080824006010400356180c0c508 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 724524181 1250 724522931 724522933
    0x703060e070609080a02031b030f0601080a03110f0a02040c1419030b180c0c070e090a0501050601110a0605060105271c0f060905010b040c0c17031621020705 69
    0x51000c40da00c540490004e00708400102a98000e5801103605da946541a000009041c000c20100c140c40400c94100034540e4801140c405680d0f440c561902d076050440101e002644c20315013a00070100014101c2da451080380e004d0000118a90b003004010221500a00140700240c00c205c440e454078031000d0300004519400b449800d101058005080729061b0307111500c1015820140266440701e001c9503644501440d081e603aa0f1924010494a0000568021507150300c5c0b5004001203000003040003520f951258000744404d4a400d0019611012035000e02a03155109010500114549400c40b40e040f00c41030412915012481218a4080b035016621000d0101c21440014060809803006540322a182d0880440d070b1f2001d980701040032540a901604064485001e502032020a5105c031510420040003003013010b10f540e20280030010070035400e50b001080b81d85081340f050903000841e44115052111000035480c0e00b2015241210f842080b40740300b00c81c0341800074601c1114402401200c4c0104 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 724525431 1250 724524181 724524193
    0x30903020a1a0604060b1317030708072103060b0f0901090e0903180f0f12121902010b010c030f1809050403210c2109020a030605061302090f010c050703060e 69
    0x8010b20082e41c89036403241d080c04d06c04001c3e45041c90317812081101070316103940140c0c44000c100c94081c0d1940c012918060500c8c0d0000800c14200036452100c2c0f4810ad950b01130300e0401483c1da0700142e08803082c40c8074491490000700314650000c0908001090210014141a0003076030301c0f85d0320006d80440807900841107610004200c10411800f11b080c056845003103e049d10b0100440010503613404012040c0f60281c0d1800110036030300c1105200f86c006502d070141310241c882900e1000080c5460050640030095407074180162401d51054040407103450300f41d2038110f06100407040c1242d54032942c1001104030140a100462150ba542c000e460040d4040c1d910302c210741c04c040000c0880740f01001d00d822641740c41d059070f0031200d0f504032151038034018800d21403a0310f002d80410000c000e4a07540c24002c1d4012400b00002c810010550701c064003512068030f059102007282d0342c5032022481206062507012007440b40040309913100c0c40fa8180002d21a40640e4034031640c0765201d90079662620401c0e90560064 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 724526681 1250 724525431 724525441
    0xb18030d0e060a24051012020c031215210a02090c07050634051603080411010c0b0408030c12101e15030f0b030703050703021f020d030903020a1a 64
    0x43d018020314443e11500c00e403018029840c04c210300202d00c0c1701d401e003c0c0741c50007144c21846015030f5112070040303502c0c0c0781599510f1410041c19126800700b510144851104008a08285410320000c17020860181221004d032504000d15880e620207040075845502ca16040a03006072142c6440c2806a184011f440b40c0701c100500e0298280711001303003445500d9030741c038500c10406115104481103040400511680a00c0009004c40f018816242d00040c2100c5a5104c1c100301580801c5882c4a01d01450848101041e07110045503404030300c0c54041c4c18110241c02080c00310300000001d6421180c44c1240c03501c1d0203201d814220701c00e10304944020300443c1070304082245c0542e1102c0d0b541030303203507a003111405903080c203091142e03c2d903082d0b0a01f400c042e6100f110402140f142ea01c8002c0c0010003c0c02c03619003590340e15040750340e0701f0036000403070081414105278912101020340b4640e030f002c4660083c003241010190114014001d1281c290304511442182d41c3c007040203112140d04580c1c60034120815417400e = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 724527931 1250 724526681 724526701
    0x60727090608070e0717130206070b09163006061203030b040c0522030204110d0b032b0c0602030f06100c021c0f1a180105040b18030d0e06 61
    0x286500c01040e0750349940400617038640c000301c0c8a80300c100004a811058a81243d580e00304a01188000d4102c800020144180b10610b46010712a41d40c0004403031401c800c401011300d5552480c41098211404a04002040307100400103440041104500c0340d02d02400d0344510098545070307405000c001c204403081c0c44c14154103000318007a156094809220b004040340f00142079104040e000030304010604040e040c0110508030080007160002c0c8240101080c1c5c035901c1d080b56000300d00c2c85000900c1e02014a50500f40400d09803618201440d05040501c00000303070740b403501c550900c0c1c11704020b080307041e0800166680c4003541c06200030091039182c6142c00300c144605c10a45400c10800c0c08818000710b40143d42d81d80100a101886802d0303000d0b480c0c143c0c80c000084a034000e40c011b04060903160f05052290401d138806114100d07004061200d04010b0502c20b080343d100743c41c00350500032940c0001d50780c1d01c0f11034006000c0d4040f00c402c52340b42080320210b0000310b5525800c0c3c50304079007000d0180511090 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 724529181 1250 724527931 724527943
    0x506151903021233090105120f0609100608071503052806060806011b030e011b0609110a180b060d0507092301050d0e0712052409060727090608 63
    0x408444c2c00d01508008034005180d408051060038411400d0b0860f0841003401400301d01d010300b19210407180c1900f400700002d44c8a402c1001099840f91410b0301c0014400400103e40040354510400500090651081200500002000001c0d9502903500e20015060325540c80c4481c00b03030740d90b00010714a0902100410341100907103ca410040040450081c89021008140c650781d4036040c801495044580142c500103042121001d0324501c03006c5d00001c0c0002a007007500c40c144a0080140003079005410010324000c03e0043c113000d60040c14030302c070b410f007802e03848034808003801409c2d5810300350b07400041003d41d002200d28000040340b442d0104203218861210500c4c1880c2110700130034192038000001c1850041004109106441d001c2030b25144005000345409086040741400030749030241040766890f8141032180c44124460211104146881460780d400b0310250030117400315886113242118000d07503542e00c1c00d007413942922003c101c100c1e04c1c0c85043d00900c03101002207815071512414a00b000 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 724530431 1250 724529181 724529251
    0x6090a090f0c03151a040c0e060c010e0f030f04060f0516050c0f010201020906070605060402161208060301020301050d0b060a0803040906050a08160317070501020d090605061519030212 81
    0x513062906441710050640e504600e070100c195000074040d1301c1c0b10390403030340c1d101c2c04d01c1d00351740041c00001e20614512043d00300142030041801250201100b00c40119600c3c031039001c5810b18500140000d004030303845000e44082c800c6040c40d00500303086d0054205c940c0b0003030181084407d40c1c0409401c855908000102c0b01c000d050900003141004644400f00d101c91081700e4008000580e103400151866550380d0580d180e240c4c0036013013401d2a000728a40000110340c60804100822000400100319107014001c982c1614005401c0c051046000c2ea280643c0120240c20542c1c002c1b0070382400f28101c00208050401042100c002080d590302d02800d01035441043c1d045072040d50800c0c00c0e07888104100d40c4803582100e40c4541404043c07010802020041e01800e00014440d50000405611318540341d007006000c1c9008074410450f84c1c4803901044070300544410056100b80c0180580b2800000313a0006000c3c250381410054580381c090210528104c00c21585400c109803221a5613114907000320120f0126 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 724531681 1250 724530431 724530473
    0x16020c010f050a0302090301090c0602061902070f02040f0b030f061e0f0c091906051e1608310603060b040803090d060f090b190207020906090a090f0c03 67
    0x5a03480324020b0842c0308550240040c1500068188090744017584180012a00247c080b8a010b0700d4803002900c469003565040040f800d001a0f281d0b2003541032088852041d0311402e84010300320342d5402e200280149100310044142d80310241581c0b5101403001d8542c82603560302900f501d10307014011000c0a412900075285210004003008003500c20208030542010348905683e48840882000426410520850001c40b8104c4600043e04a401a02920b64a000110a517a0340100405005d104e400f41d07215208050507404001e10100b42c000c0000d0030465183c2060f110310b6201008801d43c121030310b00c030034050000514010024550715101d00d6015184a07544c03180b40925004a940d42c901400005911840803c0d072218100001ca074005103410b080c101c001e0000f072245040c29280c1e800300b107480c064043c00046007080006064401c55248660050151740f05448540500903100d100070b090350708965440f0510400f10b01c003044031b500b1003442904464101400c6151140c80303400741c44004541 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 724532931 1250 724531681 724531697
    0xb010801090f0f2405090721030c1106070b061806150a09090c030515120a030507020315090604060c0e0906040e0c0603010602030405030c0f010e120a06020316020c01 73
    0xc1e0b03880489840e074030b4002404001451407420240d681d1000b6481540b01d104085101e158130050981100e440703180520150388210b540c45824400601c42c0b006251264001c001c24900040d00880145074003074016a00741d42c07002d0b101e40203d81e0304e82c000b580c10b668080d0f0000400690740f9209a2901d810050310100701501d06203207010030400f45c1148500d2aa01c0800315401d40c0c05845584640010b000b00388040c42101885100640102402c0d6a1054074039804101e0309224107240d80c013034035090000c0c0014a074425136038500325520b401c95002280d040c040d6003440041000740c0304d6a04c2c099400301010700160f05081c50030100b1541007100c00c0301440901e6155401d642d94000341c03180d201c082990301080300c900822034582403403c00a81290701032000b200120760303aa800400342c4207448050302100e50008001c170805c12400300d060003890009001e0051001c85040814202c9060700d089400c445650001d80d40744c105a810844154aa24200002c10070344a0b07410040c4422008080c00c2ca002 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 724534181 1250 724532931 724532933
    0x20c100f0b100f020a020901030605160206010b0913060e0901051812040303080c0d0c0509040c0519030e0f010504030c0204060b0a0804031805090414070e09030703080402010c0209130b01080109 85
    0x49115100c2c2e40b002c06004401c3c0e04882654028001c12885d030354000c1a0680641c1c582c5800b400900741030301c0104411f04100f1840d03000303500008172030b41680d40c00c1c40c0d0700b0300740000e590801c0103101681c075100c40c00d10b894110014003107084503840c6004154200000c1880d24000d80740c009000c40f40e6602050641c800b204d514400c0540c5421201aa40c0502c0d00030b050750748405009096206148940198510b810310150242c1d41c040041d0150030421113040c0810340759003000b01d4003400f41040c030380024614000081111400f990007590306809440c280d582c00c0c02c65854103800c651084034241c01044203030882100b1446c00e071243e400a0269108800d007800e10081c00144000f20041c0000d040c8000200e012901004050040b030003010001c2030280d041c606031038820402010034502c1080c9100f01600440c0400c0f1065070103200e40500001142412000c0e2411181c078117000d4826814062070014001c00350b1194400c50f4170440c030300e010301c0680e40402d00e0a1160400140c1c040e004591500e00360300 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 724535431 1250 724534181 724534189
    0x5100e0703030905090c0c031218070302010e120a0507060c050c0402030115080c1c021c0c0206040f30140901090b0f090303120709080718021309020c100f0b 69
    0x1084e43c00c00c0c0e03010041e0780c2d225401d072249841134010b0000c4034400820341c00e8021030a090064848c052405c1240c1d52040e40040160b039a5402d400024042030ba1a4094055400c2154050a500d24500f00b104d8810610b0b865850034aa0207401100000d403400900c0410310104002152a0300380690b000c500e91340c500035103142c4071413001e10000100444403000c22080e80d0b400b41a0b81151040c0c01240030060035800c0c00e000203501880130880d10785005041055100041c0c402c3d00c41d1781d009500a0709465850b030b600c2c81d4214052a4013254070546900c0c29040044024404490040c00782c080c26400102880c800340051084120a4551600c02c11401c4511f90f4425060021100c001d413041d0f803160015506803000b4003030b441d8450303050301c0003203100c0c0d05650303440c2e20713003800b582440c0c5501040c00c1d00c13100350f5070300d8003110300850282942c64020f03540000c00f1075008140ca45809210742c211507842c1c403650001c0e40c0c4002c001081c540c1c0503500501000015214960041c5183c0004108500e0503030081 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 724536681 1250 724535431 724535447
    0x601080f060925030204030c09020301060c12050c192112271a011202180a090510020d0c030e07050405270114070c020d06050c0f040305100e070303 65
    0x140e004001d1100464160390009101c031240e600300c0102d0f166100f080b048001c000b1340003880140e0356008200c0f00080e5583c824401c480c140d070540c4e0f542034251607a0307440e03035000304c918040da4100300a810000310900107001e00c40007081e030155100005c0405c00701e040c4124061140014075060100c503800074441150000340154580c006444089940e030340e810a8424411070541c4100c50081141ba90081000ba24030440c2c415500c00819004250b40c98401c0880c554241039402500030b100c020b0203000e007800405140fa4001c51808001c0360065140e82c072282015103c1a440341156000301e2032843c014024010141744c0140c502c0c0c200040d040701e038005a5220024401c02d0301441d524804503003204241c428401c4480854903041090075481943d907402400c4a800c1e03e0300303507200c140c040b80f0103520900101103860b03001014903e4005c40b82c1c031075400504014040030250783d4108400e0501d213041074050300c02103015101502030320f5284071080081d01e40380400030455404c40c4005200182d08081c107 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 724537931 1250 724536681 724536691
    0xb011815050c01051501110d020d1805060d1a2224060903060b090c0714010b0d0b0f0f041203020903070512010b0a0e13140c06030f010303080601080f 66
    0x4049800d1191034003a54280314640ca11041542860100025a00d030300c10100c842590a0740d03000d20310000d15442c992035074000c14604c0010380110450040441c441d15030a020120a0b00300c91a855650700006845a071000003607001c8180c54820740c400d401502d0031041303982003041e02d5684035246401e1111403100f42d181d006011113540e44203000d00307600d1007801c022000c40c8410703240c0c01529115607010f040f08260344411607030141007440c1c120b00360a055170311500644a04154608203581d5948404505550f100144035079981c0b171b841454680d40710701c0c05807042402440741c2070180c02d215014130420b903070080c02e56003452448010300c000034448407504140301c0d0f240c3c5001600c6014000c0080d041103000e51007030360300180721608240f07424019400414040002c6846003003c030f65480c40700d12810411100c1d1560110321750702101c007140883c8680b01c2d400030b4441c2aa410a190100003842c5130b00140e448016003d0044010f104042d0056040c50300000242007041070782c0b4009548521340c0b0b8008007 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 724539181 1250 724537931 724537949
    0x6090604061a0f160b09010c02010c090311010c0b01090b0a08010c02250518010e0601030c12020a030908040f0501021009020303160317040b060a0b04050a0b07020d2001030b0118 78
    0x451081c84070410013910030b80500d11052100f03842c1d1a080c8101074660907103020303900b94a46009000550700500c00c4492401d5a5110f50007105d203561900544603058139002810702543c1700c034070000602c0c007842c218041c2c280710718001000c05a50003807085040b0243c200c84003507072402c54101c1e62a50001682d20700c00380074112224440c2c048078000503401030641d0115030454001c10303c40743c0031240620000c0c1618080200c0054a81e2100d004400392545d4084000100f03a2044d070701252803090b81c0041083c40e0b12810041000c50440e0f440006c1a0b0041d41314010300d07006190305005941e4180011840c0018802c1d05000702102038002a880744501c1242e0b8000322110805401094002c0b192800d8280b4a00100e220b280391038101600398910490301c541c41100380c1076020442c450b4803000c1c1d8055907409000146d425003400c0301c03244540c0c8880c80a0741e12056410030900007075488a1140602c0b152011851200045000058146c2c0c1203180c00074140080741c0d0020700c200014540b1081140c0d0115 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 724540431 1250 724539181 724539187
    0x110d050f040e09070e0a091104050f0109202808040c0506071104050f0718180e0a02031b03010b04140406050a1104080604051c090e09070f0303030506090604061a 71
    0x34526181604581c40015010100010030945100c55401180824088c10500400b511000200412550300325003034080f000503a8010301170300e1101d50242c4c1181c06c0d82e1030182400c0340146c1950324140c2040307080d00640c2c0f20700e9030408580f08200d408001e01d03039454107003035007942131a6542102210850060703d00900d03000c100032060005502031481d0405d0003402c02c1144d410621400d4501c0d2104403162070120302040178060a101601600004448450301c140390b510000d903011402070108492158883c1c41001c1031032016030b8041c49840c4601c90803000e0f9402c3c403140b04042c107095422800341a071242d483d01c41c14161841242e03001b01d5005078803010004840ea280307000b80300288260041d48143d2140420081001c1754001070440c0614000c03400c4450140428185201c00d40b90307540c429000464405040060b0840c1d141d403d03400c010b21200b41d03184907480318040c1c0c001903495801680041d4851080c400700d13051502c0700300c3c0c2014090f201801030743e04004012803001d100e0032008020321400 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 724541681 1250 724540431 724540441
    0xa0e180304050618150706021801020304060e09042603180d0507080a021519050c03040f02010f1e030606030f0b0f011d040c020d1b20130c110d050f040e 67
    0x3043e40036a072010559503403105080d01f0258000c0d04424019a01c03c11107142c40e40a42d07000009403021500c03e9503442c03d10980345414060580000740c0200d854400074038501040e5070ba1501e041c05100d02c1c25010b01d8a0303140601035009900c403c2c1e00c07961a1600100014005203030300008a0300350035000f815290b070b44d0b081400200c0c40c00c4105010018184d1421081c041014007540940341480c88188092000da1910b4465414501c800c1d1001013844910701089001075001c1c25029062180350300708007040564440b00c3c40d1040c02400b600c0380001c0ea403458144040360301031060b0459000201b400300920398000e000700d081341491440c441d060120114012101c480107017040000d80f01e0242c814802c00824460195680070341c004030304045080000c00803e0a0250308103071461907004014828010b01c65580c0e01e1009411421850300444c0540049040c000980280c64100029946d10002904503134100340c148500407e8170820040c08011245440410f013007540c0c2038032448000007007642c5039 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 724542931 1250 724541681 724541689
    0x919080d02210106051b122d0d06150f09030605280510061d0103020a030209120c0a06032003070504080a11010909050408070b04050c0a0e180304050618 67
    0x1256030b001210110b08000070510907032010260501c80d202d480380421038a4805489501c1d0840e4420666030810300740302c00c3c01504250403190039072861005085052001802c0c3c100b4440d40300e2541401c10503180c45082248448001c031440324100c1c10303d009982c1e1840d03507000514900d1284800780106031143d0102d00714800512081110320b000185c0c4002c90354880041c50040c100403500340c014150756800004a4500443c01c0c120341d06000d200d08519840a640150f0080d0408500c0ca010540c0c2400091055101d490286141442446c000d1000002040c204440e0529a800400c00c040c185802d440c64406494544c10001c003400c0001a1642d450b210212024011a884071225106540b1500c090040010380300003040c00c2a6500f0a040e41c461201400340d030341c142d500034601c940800030480401c00881c40e180d0020300c01c405803010070340c503000005e04d1201c00e6002855500036507001d01c5a600140c3c48509400c10203107019506207417a040020b1610f005e5051800000c0c108080030519581d1 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 724544181 1250 724542931 724542967
    0x3070209040606050a060c060605030303010f090f020405060301170106060311181305040c14040603200a0e070f0206061c080304081c020a020f0703230102210919080d02 74
    0xf0010f49851501742d036880c8020452200c0002c240d60b030900d4050041442c0c10080103c83c141c9815015502c00c0301d141401160080c07201c41d0024003107690034000420b29985040080d4000c010602003803070340302840c1d10205e003103961550020f000c1c036181c83c502d2100c1c0995030055510328056903010f1504601988042500003002030058143d0a140800700010011445014001d0319103540d0003140b420404002e000c2125028000034020800014901400c0341c440131010300080c002500d41d6010903a038200801d0a00e20a42e08140030506481103502000c0e0b04000e0715034022000c070744000d08524220f902919180c55500b0107040c00300000000390a1103030382c004032808148000c21038109840c42c0c01d040002500205151001405601620040340d00005a0070003529007104103401c0540008081d260084004039a54880395000e010380302d080da00c2d10b2003c90021080d070400e0a80382c42d00c08044c46c1020481d05c0302c00c104240c0d0a00f030002045098013038a214420714540140c1e0741051aa5402001c4 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 724545431 1250 724544181 724544189
    0x3a11040216030f050304080f031807030b1e1b0304030c0c080604021f080606030703061d04170406020d050a1e122913060503060a050610050c03070209040606 69
    0x5000207a08001040946a189075081c0030ba950910702514041003100c40e0700c410b1300c018100c64801d1103018040e40201006640207070103110711011610909805906041241c2c0c4191180c0004608100240e42d5400c40c80540c0304441c01428007074501054101440750200d40c40b2040700c2004000182014010403a030128660092070503c44035640d40d040554802d8100d030220700803000748902040702c0040c0c0344201d18070b030201d0703d039003100d0360303425041c081c00740c0008052400b056110000011710b408080110b10392801c548003080420302d05414a040030310030304850070041d04420401004110f5000c100c800c090060362410319034400484034100e035818a400906050304d032441485c0313800365030000702d803401c0700e48203c20a2103480e100529001c0900c04141503502c075040d0881d0100b40e1440d103401c0c44031440f800042c0025145880d41c0119141c814100c419a1100c2c4d030360400e006c00c610344212840d400610324680b0341c4c41c1c240c502e0b04490326801920707802401140848089000c002158000c80060 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 724546681 1250 724545431 724545439
    0xe030f120a1808070b060a090e0105160905060a031a041404060b03031305010810030611070302070e040f0813230a291803070b093a11 59
    0xa045800620004108181d5805141d01e152070140314002d042000d800c0c5200f50808540c41c200703821138451001400006188940c803007541c102c0440c82c05103e104401003604400000902440e1241d00045014070410fa15402c2c0540740d60200407503661441154203481541c079000c80d521112100400c8010100d100180e13105041140c54120140c6000031148070303601130b00051054001d000141a02c074882d000e0b070380018030000c0106100f40e501072440300390080b43c5894201740440d0380b52500c0e801c4802080d00302c0002040001c10409060741000010050880084c1d450058200341e55404d06069900b4401000514040750852a00c40c11203000c80050014541c1224400d080d40c0c00c503a0408444a042c80c0318081c107080110742c0404107100f030704000304482c19412203d40800c4d41522160003039a6036034149170b030001e44440d07162400e00946004043c202c030000c2d00c407001c4008000146c00d1504e5030a265220303a14100c0c102c12142c0f407060480c1503802e401b400603003016007411114605001101030704 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 724547931 1250 724546681 724546687
    0x5101b050109080a0e01080f0105060c150a092102030406030c0c0506270f0c0d050a17091f0f03020a020106080a08070501050702031215460f090e030f 66
    0x10301c030b006002000c4c003825594860503908900342c011340d002c0f0001d40c1d1004000703400ba070050105041c400010b0072581c014200315180300039540500c0822403001c488000b001354560703000d1010400b034a12044584100181c114a14001e2410025524043c52007000d04068482e0f01c1041c41d00e0142d80e800c0d4207190094140c84a5182500d07410034542006d1051400c0e503404501d2107100303004d002c106820040c00007400703454070105180070010038410707640c0140c640340030343c4a0802c001000c0c068622640b8951a40f200d8440c2a401c04002c10b4134010345901d440c03441e480003221041584422155844284c3c0d050040e1180e441901c1280144000e80050450344101d0300e000d0240402c0c02e0150181c144904001c1c00a40d44d41c1404903100d00071170b00540347c0f55000c0b9000c00c0f0040c2c03000b100182c00c1c0c000508194071142203100440c035907810244005426800c1c0c01030000c00310452000b1b201c1980e2400030366461141c60020500c0c2c0700070782c501c40c008050342c3d50302086909084c14000c49007989180390907261 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 724549181 1250 724547931 724547933
    0x8030d0c050a121512030e0a0902071707060e030307030504020102330a063501022a0a08160b0108010e030a1101060b0403050718050601090302130e010c02030d140105101b050109 78
    0x1c41c1d10047e040007032281c0304900d0000b540c501e090080354000c0e41e1147e12440054001740c40101a508070903c104d420a4513089140c26440e4208041e5100300440c3da0042550b040900019041c4000e114050301c064044248a20510902581c00c08410a450041e540d8a40d15202048014440c9400181000074509220054040514105045035107010f1842010800e50074509080f4401c80ca03081d9010143c10030820100d81c49225806c00540c915401c1d200f0142d80c0366110b607040c0e4001d5010200d0000038440001c18001c1011005002d0200307a07008101c0a0411080f5030341e240103828060702000161003824082810a401030310040c03c1c401c81f02a2100e4072440c12030b4894205015035440c5010810044000584c60b008007409840103840781e404443c11074090040c40a441360190f144940c9401c02071119800074410b401d07103205160301546d1074003180e4001005407000f5950610062048500611066070b44000b01c0b4490962400d101e545514070300428954185e00401c041c0a951802500078 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 724550431 1250 724549181 724549187
    0xe040b090a0603020112020a0905090a0605030313090e01110d02070507081207020916090605090607020d08130609030b0c0918010b07110108190b0d060608030d0c050a12151203 77
    0x1003d076407007600c1e807802031094502c0c0c4100302c1c014070340341c0000501503000800043c105030ba081c03600031281d640c02140443c1c40d003010038070350b90001da10a07041e001140c800300300c42c3c0c400d48541c2c503c40d19190000e00a95194141d028014056450000699039000a0076000c00c502041000c0c01800b005042e43c0070400c01c0d031070441d080d03000741c1016070240020000103500d80d0807000101e2034828080e01d84000b02c0d818880c003100c6541040c03a009030001c6c803c110340c0e00503035200d94030350312540d02c68040d484d60b42040380c001c3e40c000c000d95030185c0240001e0340820700c00101c5800349941c0c03141c08482034603129500b000c0050b02050701c444036000c5221302200081141d000701402413440758004c1e0307091050058103a00450300441c048401a6240f02e50300311000c2c082c092600400e0020300002c2a6410118164440204403842d42d0300c078040950002030710080251075030052443c2c110442c24003504004501e84061b0994003a0380e482046241d407001d00c4c100080b040b00a0201404446003942548070a030715010b = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 724551681 1250 724550431 724550441
    0x20a141605120c061602190303090515060f04110d0b030c130c08160215090715030b0a051005030a020a0210020316110715120f140708010509040b01060e040b090a 71
    0x2262240207800c001508201d00c602e0385100c0c590251b00412581440035407511030303d980103d00301c08143e103804503080459400c00c0701c6404401441d1f00346905082000403c84840000140f8600990406c50110000b0300ca00301a0381010307503010800721707a038a070040c002401c00418200380c81d40b00b6038001d0341e4075181c1c14980c092280d0b19030303507201c2e1442516404845480c0024040c03500300141d20001030030614598102c182da0b0071007500c5c0102c500468648001c20032100700e664404c80001e903140c0501204c3d2404049a80003004240c41c040602100f0401c010803521000344840300480d00020905140c034420030045a1281c41070b041152282000c254006d10600c0a0b0f1004001541394041d0b11003144000c141e0400312040156004a20412650183c0f5014220918650076564806580b58284081d028183d2074881044103d525481c100b03401610280c0103030031a42c0070f890040100300024150305181c50542c0e0481c10054440403040c000a000761001490841e00010118240300c001e041c02d800c1 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 724552931 1250 724551681 724551697
    0x91614040b0324130f0f020f0406080c04150819030c1e02030f010605130c14030103140d0801030201140f0d060b030a060e061804031106090c010f03020a14160512 71
    0xc07a840c5032613a842070f241d041120900a0001c000650141e00001c00440081c3c21745c51000c0c2c0315214520664000504480300303644819943c0e085140103440618142c130a030304481c4901e54880b440c02d820410602d03a00c00c0f00c9500035607030001500a01c4c091601419400c020307603a11201c1020310050744c0050f41441d40441c8070072070003886030201059444406010750004d03a80c000c0c0c8803542c81c00c401c2c013500024090480f910400c1c091003200c0c20a000d000400150302031800340180351200340000030f2031440d10b00341030b002000f040900401440143e9010094440d850480c00015444603480048918070740f040c0003030958614641240010010340810183d48602d541c03150801c1010350b581c0203041c0a58003101c0e1260b005550b2400c80240700020400030750043d0080c81c1122038402c03501c290f5490a5020307512844503500015028404e5a8404c1c1504541c45446c641541449805840641800301c1c3c42c401302a2401c1c08180380c07940d035202c4541e800f151600141114014801c0da00ca8500030750000036 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 724554181 1250 724552931 724552993
    0x40f0b07171801030b10080a180c03060207030824060307031806090b060117040f050703050f0709150602061506130605040e0105040605030706111f0c0206091614040b03 74
    0x183e804090b26102d8040c0d80246c1031902c0799100c5581e80416100101802c50680c42d241c0080c0a5803000701e0a0550740b040903610035280160768844178100900714480c0100340c0107407202c0d4038519520b041540800400500d5003500c0e1740d6107980380e1850941c06403080c4407004580030001d1280005001007a0408004140910b10013000c64031280e00440e407401c030108001071401f48200c04134000481c605180ba00c1d1502903015030366143d441355a41070401d44290100351003079006d0f060600c0302c0300301845803410b140e400608144941e0b25040300a51900300081c11000d64040c120b40c0c01c0f0064841108807000ba0003400c1c1d0745181a034851a0142241d001030044150f04903c8500203c2c040c1003600c80c1d41d003540d88c02401441e074a441d0002c108c0305036003408002c2c1958080d240800c0c0802c04900701ca45951150300002052001104000a282000c002c001c11002c0d444104450313084100000d01c5070607035180044216072000860049000303042808600d540500c2000410440288044006111545000 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 724555431 1250 724554181 724554191
    0x1b030d090f06060e0c040b0f0c03120a0f0b0d02040b040e06070c0b011707031410020d0903080a1e092301200a02060c09011701062102040f0b0717180103 67
    0x55035044c3c484070304070341c030f03a691040c100414481d0b90750b107401402c00a120420414648500502c04606682000d600300d20a0100002804051802801440c20381c0004401c20060446240d001545212020034046e01482d9070340f81c1c10105440d541c005508541c003040072642e0300d00341800010860810090180c0d840020300c400818001e02807841450000a20b800070b210060075070b00c440c840d81c2d5150040416a12070759440403154070080c009400c0303040342d400000640404c40d080180410500604105665280c05405060120b241840d03020100d543c000002d0458464640804024040661042c01c02094800010700c1141508041c90f8000c1b50f500a050501c00d0108013040c40c000c07d10b081000d80c02c0900000d21601c409005081010b0051401d030400e40b01c413800c442034522003a0402e10000711540302005400344000700c08000104450000c5241510300000d00c0031340115405a16500900040d40600b8043e440c00d60b02902c0d4060403c0750760b10401101c09424640191440c280440c0c245 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 724556681 1250 724555431 724555439
    0x90c0d080306061b1006051804020d1401020405120c01140301080303160918050405070b070f020d0201030e1903120c08190e030a020309130b0102031b030d090f0606 72
    0x2521854a45035000580ca42180c9680b010000079400049449104c0e51a8800050600c24100074a0980380d400e03d000141083c1008180203804000e0a0034400041204040c480145c868a002051850f00812940d80e0301c1081c11302280607105540c009680100c10324503e1018180210340c20701445404d0700d1341a110b602402c0c400180303000c2482520003d80042c40010b100759400807001c0d80c2c5000c60318069401e5600c0d4650802c000e0302040b800030500303039500c0c01c0104210082007950302412403e182a400d140955454101403420000c00a0161100c00d02132011640241c101d034842100c0c00d003e0b901850303030701d94400104161207081a000074000800200d10541c20b4427a0051aa00c140d4402c1029a102407088110006c0080285000781e0391b0144801e20001c18030107001c00203000e074050343c2e4550044041110440260282d030f8081840c00344650113986e000821940ca56102d030701510000c003802ca0247e819402100903202c0031a081480c04001c00000e0702d0840c0d8064801e02c0c08000c20f03034603 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 724557931 1250 724556681 724556689
    0x90f0905090705091603050a06050d030c05070605090a0504020706090c0b130905160309030c02030313090e030c0a0f0318090f050f01210203071503020910030b2b0b0f090c 75
    0x815150045e00f04008111500000e109400213a402544144d0200700b00340d55602180002025200543c00145580c04402c100601808441c008001718034051b4181070311400040e005c0324031403044611659000a1070b808111458120342241c0760441603560a1554030300c1c1c1e16440780d2114010703d0300c1b030310081c0c0c2c085006803042c40b4070343c018460142d5183c10f1424605017600144800c0c0b030141c0511103034609282c0180c7d010070081ca030b880d60303007002e0458007450644020b05440058003441002d40062102070003407480010600c1419810950521445515080c1901c481d810b9111103920701000306ca01041499080c1c03c507000e1486603440811181d601c2e030849198164080c0210f080d11040d2181275074091103000d02800e411070008050b2a581c0742d882c0203900110f003c001c40c1c14082900883c48004d039181018030081c8100d80341c202442501c0d8503100203110500f0400200c104004088800b00c40400c0c0400140b00d1640e11858400c1c9a00b041104400c103508100d84850107403090140c01511828 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 724559181 1250 724557931 724557949
    0x80f060115120f02090301051009060e040f080a05070503120714090904030e03030c01051501022104210506040620120417070b0f01091d061303090f0905090705 70
    0x1101d82d01c0c1420034420040081c05000032900b005406502440f10401c1c90f5820310030300740192031155072001d580e403402c034484084d03600a611280a4910220070071010962101089000301d41c80030b01a03940e000020000c1d24540a408405442c612001c101600305a520002850050f6100d4546490a072014a41c429861141030602ea410080c07020200780028010648d208540b40010706480c20300721102c1c0920f00716078080f102c00707000c0d1105183d440559601440380c450200046034142c203002070700801e580c8892181c0d1044a080c01c0442c511600350162000901410a5014042d140c10317041509019020309203040301260315050220301c0740d4404044604640e0110210f8001c01d10036030355911070300c84840c101264185105005c02c5228000346030300e03184034070a000d035600c810354950501f03510b401145d40400d049811030340150388840340b40c0b100191080d0300041d0191001b0003210b052800f115025825404185000c1c0000c030042241142030700583e106450240032100e03455a920300f0008508 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 724560431 1250 724559181 724559219
    0x702031e011d060105130b030601060f0c020909010e010c0f090603021b03030c0d15140d03020a0b070c061103100315090b13031206060509100306080106080f0601 71
    0x1038003600140c038084644a400305004035040300009202505155066812460401c0b000d669410410061081d8a0030001c84203650390701c480c080020180384d001003a070303941040c040c41c1c0030310042c2032100051901c5000c40c207541e540d01405200c547d04002403181e0180c116880310010030b50030b001c030b40c90080c0d01c80d07220750450008a690b003613900d40c540b200c1600290f110030403201141a0800c1e181411000400086002c0c8200b0710301d0302d503258008140e61040301e88803011501c4041c000e02d0704200100c00c25080018486049820002c030000381c1c541a4580400c0714001403051400400300803409812110b07046096000702418002c41d8020324001900f440100d07a00b08004200280c10310201c0c07a4540804284145080005000a4035403501c5044d0704040702c2100d00700a41003c44820158000b03c54203264500d400300f4040a8100400600745000d503c003c0d80c040e8a200c103001890f180300390400320003400800000c00001e030701d4020140d211500200f103c0000c0c45100000180400210340e940240 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 724561681 1250 724560431 724560433
    0x608130c09020c070504022d0403050d08060301140103030207050111030c0607050f0c0a050106181e050703240e16080402060a09231c05061306110c030c010b0402070203 74
    0x2900300031032000207400200c1c5200b45071003454404641900c4c2c6e84001d100300d090403100c201281d40c0c500c0010010781c0078080040100b2a051004200003070001540c04100d0f5024148000d141d80ca04020070700601c0f01701516604000c50b80c0000041c1500850000180c8800303aa03000c039800407141c2656924880c4d034900f80031760b030b00c414006041544541e02401c0290003040d01e030b1303141c0310b0300340055454144001c8081d1056517403200c08101c0d0320b55552010111040f4407409100c6074091611180e42c50080706016286c0a8607040015000c03480703a070008040011041c031050300c08400c50008002c1d00214084c1c0f003d02c02e000c00210380141c80c0000580c1c8208202e41c1c590000381e85175070a107d0f00d504001c1241041c4030f0102d1000c42c1d60951090040e42c000401041364484c06d00800800030540c80700700c1100b904460480303080c030220f403010645550112000718a2480d0018518107200140183c100201488201258408560002100800400400d50028081e00c81c601c0200800c070303c07800070001c2d81 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 724562931 1250 724561681 724561703
    0x1b0f050c101a09070f081003030503070e01110304080601140306090601060521010b0316050405010207050108060307050d050f0c012d11011e11090a03080f04080313060813 75
    0x2000d81141c2040b03201c00141030300d8829224081e0045803a40409503220b2010803c8030502451040d4012090303030303100d2560300d4100e401600d542c502030810311028000b2410420700c40310120359139000300b0000601d1561081165510760391404a03d0312030f0800c2c0100640080100d1054169280020384c26002304d0001003e8039013646800400c1e9185d0303101c00e8840808000000b4507054550700c9030341d214024040c210510750b407440d00c4001c602064003c00c4122052000600c41402143d0380020840195035007803c01640c580c8800c00000d1400d000c1c0d0780315503403111014110700c04002010581c0700e10400c890301100c20b8000600b0054800d000117420380b4030102490000c00c400e001240c82a040780000604026407141f110401050a446200007400400c0c2c80046100984036264407507440320002403240319040000c03050014104a89920000d801035901080341d0743c0035001c9030b080728000d21203403003125a101110440303100390345110f2060101287d607401c00140f2034642130300349640041e4000c89a0315 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 724564181 1250 724562931 724562953
    0x6130503040e0a090807030f110708060703020a11010c020d181202130f090c050a09060f050d080f030f16050306010c1e0f050f0706050a0215070309061b0f050c 70
    0x224042c004008440c11900c80c3c94090100e12500000d08015002c0c0c0e944c0380f0204040f1401070084061140f0007801c43e400184100800040420a280c11080c980741c090b944885c007510499100d04130852459032540380403061174505030000342c08902070742d10b03441d1403400c07040b6498120381640c0c40d40711360244484101ca44c00300502d40035050b0141e03020790380000942e91042401104c1100c0620340119001140c1e0310041c007540c94007c00c07410007072a1659042c0101c41c108921001140c0381c40c4580390280c5001840e0074100090b41e01542d0b1109144501103849207410102c90b101510252490040540318982002d802c03403155040380d10501e01078541c0300301e441300d598448400200944440d00c00d0410350041c2000211300083d039403c618081e400400714101d0b0200200d041c540294000000c8c042c040004c00c040f250049501e0b540c40c0c02802110040340e440c00c10503000b400541c00c0092006180182c41d104d1840100314403d1300540503130b6072500c0030b2410101940c031403040c0c490798444c0d54002c1c08010 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 724565431 1250 724564181 724564199
    0x2030304060902011e120e1b061e0a030902040b0a05060a12020f180a0e0603120a0215180114071d040207050a050708010b030a080414030a12110613050304 68
    0x9240c18418981215074800e40f000700301d0b68522201c0b04800103045402403000e00c00c0c8602803880030074503030300151250108d240300040310300302c0eaa02c0d0107010341c0340842e100c8240c0c0c0600707080b188022070300c0c079410313075030340c8401800034001d0560100481c03080780761580c09089801e1400d062015998054285480c12012031310540d000b0101c07042c0001926001c200c03070340c038050300c120142c0001c900f07282600301480451010001d00302c0e029042038014060800401c40d0550b0002464101c0d419155240c50340c440100d0012410001000280407003261085c0520074009000c8a01c40e1175a45120000c001224041000d610510801c0d2401c0d4001a2180c1c1203a8807040e01e2080c07170f41c4c108001400103152000030366640d82002d0300074005540d44e4201c10303010070510400303000e02c580c1000e0840180601d50340b1660b07586aa4040e038006d05103024010000070010b601d01700400550310f40c2203007071582c0d05110414001c0c41210780360300454550046002081c10305001c0701d11380304603c0d8020055814982080106 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 724566681 1250 724565431 724565441
    0xb150402040e0403020616081f081b1519050f22080607021c03020a0207120602030f01060906021b18090322030c031e0b240603060307030201031a03010e03090f100203030406 76
    0x81c9c07070005038031000051034034801c00c440011f094a800c030340030503a003541d0108803a02c001025003080d056010841d03002058007a42084d03c01f0b191030300748603480c4c0700b8141100092380240403201207002600742c0da012240044901400454240800b20b8482e9034404100300d07126000e0340c0a0b8030b40c0002e41d0b200c0c80590f50094014156003c0c5600c111b03078005a9401c01c000941003600f00c2603c80ea80d000090221408921901c0d5015200f5401e001c030080b454000025035801c0912641c0340d16400d07143d601d540f251303a046044496401192074a50850602c54682601c0b90701c6030790f840400f291100c1034000c103100254070300d00480c0d800c4217420a0091850325606204102494403c9401b21407146020015104041c1135005400c0440700712580182040d207500c1d4107135950500c501c5000b060040204a44e0001500c5080d039a080c80e0120b20741803400710851240f090b55000d140e1550070034010321003200000001d4403009408070340c1c3c3d2485148400c140000d014001085100680080001501144141d004 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 724567931 1250 724566681 724566721
    0x2121f030c06033821061603110309100209041b1e0c020f040c030e070f18090b0a09080d090602090918070611070b0403080c06010f0f030b150402040e040302061608 72
    0x4251041c00301c5c217a640c18000125401c6007460074003600184500c0d8036126200c510605090480e2540c1020b12a1543c0e584a640c505080d083d0002a562b03402d442d182c100c402e80900502c5009404501e001e0702611502c070b43c26000e000a0502060b001c4071901c9000c0e034484441e00600031201c08000601488058805c580504080c1038490f110a0640a405c01902000b80f00e540740510545041103d0301003085c051060760f01c0350b541049020310201340c424102d2500b11803000000074044455280405d024000c03640305060f060320300030f55402800469001002c0da481e00300c8081d0301550701d5001d40c00710039214000042890348402010b00c071a81c010204442130003000c00c02c44e40301ea981c9000941c01a807141d00111107840021443c130000840400000b40035003d0410200e003080d04000e500503103034480d0710018189040020120f00304007410007031000410f03800313003082d035413140c98800f84110802c0981d0100c0c018404e400014011488088907040c240a2580e82c3e42c4071621003030004030381c941c0b01e005 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 724569181 1250 724567931 724567969
    0x1a010503090a0f083c071103031b0606030a0308061e090c040312030606050a0507021302040f2412050705121005031002121f030c060338 60
    0x40d02080006078002c6485116880f20381d0b5800500314030351800303141c030840c292001c0c1d60340e205d25000d244545000803020700c10008013500c42200c0d0170420300809644a4282c1c15000008050218010016010710032250f58030440d400e50702d6040515a60384118030014000400d044085442860100270a070314650b8141d0300500001e020b80001401f40c2c00507606416540c200180410410103090300c01c0c405581d00d42002c101062505e60080c20178401c105401d4104100050b81c2000c5594207001451170b00c140820441d1250b03102c2c0443c0c0c0c2e0100c0745000f003000030981b4500d0960010030300c030409500c5a031146d84000802403040b042901070900034201c001440381c144289490083d00001147c41410500750000c1c0161414062500708a030181d9510b44050040100200c4050700032012a023200b503d121484e408060403104445080481e00010b00c1540c24407000280994035402c406000c40f070340002d50350026a1001d0300b0348805541c4003000e16003c400b040d003525a10301b003182007641c11210f030 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 724570431 1250 724569181 724569193
    0x20609130507020a022d101103030c0a0e0a0b2502180f01140d11010e310605130e0f160f080a0b0117010f110a080a1a01050309 56
    0x14104140c03802156070304011380c0520011000d500d00520621388424520380f002c030400c0c9001c045151480b0794031203828018070000b07074134084032031041504523030001018040e2034803400d04050f50701d1980e0041081d0000103103801c403d006035103804042c600454444091903407802d105070034420605000140482c980006622041c0d0240e2140c0e00c050820910803845043e0034a4043c249881c2c050040c1c1100101607440c030803e800c561038840c482502e80f604481010240d0803903d0040b909000c0c070a14190304401c03050f02c210b4001007061843c28424200c08103603d00c00900792a04000c07205284030340d0380d02209544406c2031050b095408420101140002c0e5404048001c400c0d41c41e0243d0f00030303810694140c1e404c01b007005000080c402c02c05810820090b28040800352694850941c060150700707541058420300440c3d810003588110a070144040c0c0c00e200b0341c00c101201000c1c136080309009001044c040400500780c1e002610820b4141c02d0f4255001e072083c0d480c44011200d540001b420022540b00e40303 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 724571681 1250 724570431 724570459
    0x15010e10020330070f2a0c06030509120306030a0c0608041401090305091320040801050105060c060f180601030812100b270607050303240901030f1a010e01091d0703020609 75
    0x28541c0a0848540141c02c0e50301450113247c0041050503551040c02054500010710150140126000a0364030800184c19200d03103c0c2d00000e41028503148d00205008000c02002032055000303028903115074010381100d110704040309012402d0700ca030306000400141c400c118030300051900c0c000c00082c90104a50000d20114507001e152599042d4002c134002c0004003260400c00e0181c00d0281501610064809604003c0d4060301d45a58040190400c3e840001c508000b404004d401082102c0030340b01030048427555652410312050551100344018000b01c900400580703030300d201002c20811135a282c0c004c2842c0809140b11800d003e021080140400c040101c2c1c1030003190b55044c0500805070040014580e20309140350603000c3ea14400148262200051160b801c0700d6444030740341030440740c1002e6055402451450031444440d490322003841c826500300004101800041015070507070742030600422034200040001c0e203560381041280001035004280900050400c8000317014920f6001d042e81c403c046c14 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 724572931 1250 724571681 724571717
    0x604150e1918060b07060507051207090303030c020d140c01090c0906090b0913020603070e040c080414120f13051003020706051e15010e10020330070f 66
    0x71002152201500102092082e00c022000950210704240001c01c0340e9071900e074103522540101e40300602040d0f03807180080c2241d40078908444140259140d100080d1410700000351030b08031a8001980000c0c40c0c80780740c8000d1400001d22991038101601c07070007403032446038840252541c44040ba00446549030454000010340605a4201a001740000410554241401d420460349a001045d200311541800d00105d0050b6406000341a50180e407196642d6641101c01d8445c104104d4055410618021403507800c1580f1400a1707009521034030406072a01070f41043c890342c078540d04c0305140c02e0000030040f0904060020b0024203a15406503545001107a4680025516080418294010a4000400104004041c8203070390b0301502101d2590303e101003000c80c5948400d8010b00c0000412030700ea02800301c0b68010030950300f000c1d20040c0020002840030100a40f0780c1c000600880070b8000f01c029000e403444000c41e40c2452854030710540ca07038036620401c00315a0340a00c4801e1100f40101c0e0507405041c494 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 724574181 1250 724572931 724572949
    0xc0806240c03120a0c1704030329040b09072a050109080a14191209020603100501031503120818060c0304150608060703150b03011e140604150e 63
    0x281e03000341d81c440c0c0700b51803550007620008220000091901c043c000040744c005122001801e03418482101a40d29454140d00908450740907505540c040c9461482029480c3d890106408090f41c050210020500c18084d401c00c0603190000410041c8003060846060130b1143d00d20a003002c45000320020b416206e040c00c5070074520307055a106200141c4008001e0b080000c07841c0c1203070b40000c00e40c50413005080c101c0011084001a204010480b000d03003d071940307190004440356800410165881c1810b8110f000f80c072344188600d602007414054921603c801d00750914007207980000b102c1c82869090303c011250801c005210252041c0d000c06414070401080144503c100d0040c40344603924101420f01942403070074042c80060702410a4030a01221001280c259040303641c0b03080108001414203601101d100603030b042503c40c42000300002031030a2001801c154001c0e4001103040c080b6442d44401d0b070100120000094012a04100c00c00202c0799250201e01a0011351030039000d003121907000110400 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 724575431 1250 724574181 724574197
    0x100309080307050310080607051206010519090503010c110c150c0703060b09131703060303070807050102030f0108070303091404020c0f0601030b07110714060c0601061707030c080624 80
    0x8002000704001100d42c2ca0105c4003900100740244510700e010040102a8415840f0401c604640034001c952143d0045090303c4410710b030050502c00101c5180d40042005415200e0345100e50308041c203041d40c15000b0004150503040c2c40003e0000c140401c42803000380c014003041000120000c005402d2407840901940d005940b0408000c125001c51008024911f0f401034560f00c071001c2040f80220005001c041c602020401c0c0041c00c3d5103a60702c20000038114020742901403c0c10368006280001c010065004600c1144032040c00c1503244d03240c540080c3daa90403400010041080d1920511900b440e20680200c1c0c164020805403030b020304032549500340410b8a1001049030300420041c03040089080c44254040c4d17451400d03050003002512565a600141e106000002d0802707001600c1545405044426004d0240103c501d1540d42e401d004118001d08003800140510041c003240e155442409180a03000e4540e8a4654a48a410400c0601c0007410015190321000400c804411009500584180c0c = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 724576681 1250 724575431 724575437
    0x40b0409050f0105060c030307080c16060b041107020a0605031b0a030b040b0402030603280c120606051008040b0a09050613050f0105090d0f2a02031603030905100309080307 76
    0x42e0030b01c40d145100b12041a0052481100c09106085560000105603030740029185081e14003911100542c602d00d11940c0804600726064900c0355050002e42e4025203210041030b030701048003c40302484d28005028281000f94040040c020800c00d040c880c00c080c58001075180c004211880e140d001504040d40600d1000700030035250450309160340780600c04d51940c01d505071001d5140d0718082e0002515500c03041048081d1501c591882994407541c620840e140ca035000b520329086548407903240444a4030030300d0444019007000310208060800d202d004040b00c49545882805031510703614a1001c850040c051000a5980c0103041301080d810003140e402442102c0600c5000c005500740107090220501030169144e0602c0140650406c0000e5484111f4001d8544040300342d0034180115107520854400002c0000c0900302042828007580401c42414401c034210340701701d405003240f849003451500c0b0181c0032910540c001c02450502c000300c0100c3e4011480d0014007050f255030340c4500c0c2d800589544d800 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 724577931 1250 724576681 724576691
    0xc010609050603010f050c09010c0305070f0c050909070602060f19050c13090902030a0204240e061201140a0216020a03080c16080a02010f090e1f17030f090303040b0409 74
    0x2e141405c0c8210b94040d14000c4043c40315141001004a40f440b0b191900da0400540c1d01881040c5807048080d15440d0354802490000c0109505118000080b46d0003003512403184000482c05841d0005201000c81301203401400d4180c0d1100048142c0007001480308000d00300b000c001d007400300400e2080b140b145120410490301c3c0d400390030261241e514075400c001c031b006250140c0c00e009070361300280e50320350703150304580105030090000f1000209040340c1c039500404030359952000c01c11143c500030a41c81203000780c80400304180400c2c907040c240e403000f03659030080404034004250f02480036001000100404401003045411030790200d40c4111180c0c0c401d461402000c5140c0003440800d008208800001d074036404046400d20306820b40f18030100b44000d050000d407408000c0302a001d5445a4010816548030070740301c2c0341842d24503e40a184040d918144290117101040072881c6254000702240000011424503500028803d2a0752040e00c0c900c0e41440141310000701c03800c1280003800a8000480040380e = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 724579181 1250 724577931 724577941
    0x504050315150109030c21170a031a090403081b0406050c011d031611040e03030609091603030c1707032a0308060f0d05030f090a051002071701020c01060905 69
    0x440400380d02c00d604110402804002054109141200703443e001c83c2c3c107500329101c0c01c6074000900c500c050300810003001c42041c3c0000500c045d016021200103902c003801030703c48207032808889007104514070380d1002c803080c00706d40864450034980c0c1c4d02080b402540c4106400581da005143d80060b40000000307040001d901d48003060a02400982100c0040310841c5640b164040707684a0190080e07298008207041340d54014003880b0442900d842c50040c0080000e131251400041d1a688115489405a50759101003007154600144450f540c01e00c054030000c4807815664120b440b51070303444080c0c1d04110150600849080058020706800c2d2003511901c24200008102c400b00400c4400f64154000100e030142c0c01103900048801d92091007100c04c0401c49590000195600302c4004014015100203e00d0100c03440c2c000c4010030340e5070012100080b849588500708408008044c0f103080058110703642c20445d412052140d07401c002490000035040c1960a8102c908450103588180d01003622041804 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 724580431 1250 724579181 724579201
    0x203150a050d210306030605011d061f0f0509090c21010e01030303020705150109020c010e0c03031b07030f06090605060d02030d0e0409080f0406090806040f02100504050315 76
    0x500a28090700e80a0b07003550252100f035a200700000c0000000c0c401c030030803000641e1190344800c0c083d40d0300c92010815942c403028600d06030040500391000302c400f00c1012070b506103861481d000900c1d8a0308101c0175240e096803012121a4003140004017840003e0165058513501d140c242c610843c03c0354104c0352100604c4440800880003840800182c8180000601c000c010000403035040d00d40605001d43d0710100707450442d241142c00d103a00440b42c8a240004590000325800424100e801480241f0101c540e200036152503440444a140d0f03d076108000c0350342c144001518540401d640e900039161150b0756034580c0751034102c492030100e03401903458441da402c12001e40309107500644117540310b04a809007036001c2a5070705001e1454501b484846291100302d923036507400959a455009181503191685140001415001401480b001c10041c50021038100300000c0d0144c400e54219507072200c003081070303001d01c500d0118840000081040400c8003240030344081010100010f4000d40394103240c0b81c000a44 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 724581681 1250 724580431 724580449
    0x2040308212202060d0c02010605030d03060b030a0b1203370c1506120f060507030938090a020a0f150822081207080417090d06020315 59
    0x503900311010314284000100961000d2060b10340c03054480e50070201034000202c0f54064184c4030040182018a03030543c246e41034120000300e4400b5805c0b5950480000d01c15020fa407524000e5003408101880007a1924010b40c02442c100b46024041c50500150900b491342542d00c4134020f0307a01c825146124100c00043e0945604030713200050802917200c00485401019559800f01c00361801014500f050080000d41e480403000704564000b2640e4030b101440d1801480c1c1091b2001c2c0c61503071030b000000d034005d40a4003030840f11a0384000d03840c80c2c145810100c1c0100050150159041850500c030103030300041c1c62208140900924402000b500200380304005c407080490300044d40c542c0144500308900e0031404d118810105480c104544540d84100300080c801c0c80d401c800700c06030b480d402c00b040d0500c00988005c0075004040985504035994440e000c0c0d400303c10544005040e0f028460140c2014103944d03000c5d041d1003130020f16401100d0155102c0c00240d80017603d1580c130410b45c1d9011081146840418 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 724582931 1250 724581681 724581727
    0x70803072102160803040c0801050108100615020c0d060f06090e100b101b050307080408070602060c070f0203160e150f060406081e07020606090108013b0102040308 72
    0x70a40c034002c20f4280c120807069500c080140313000f1020000c20204545000050090401180208076030760750340f4900c540e11000f050800c0c0320039242400c0842d041c280c2c075064040c814199001010128010b9040c020440b040309002c0d20407a607140081c021450b4207000304401859040000300d032007030441d41e20324148040c0401c5200c10f075103042d070810315588666407a818a103440d41031510001d450005802003181c1d1160f0300034454003000417000204200ca402920035215014200d40950b0340f280b00c181d9840c64295000c0400f0030050081030300140c20089060001340c0b020701035441c004440c5543e11021503550300245944141c100802084011030000703030880c2c1004a691280d20840700012500074403407405000c00300319001d00020903000b1341802c201c1a1000e1003842c131405241c0441b0081d00c410040d14061711901e078076000011208014012050040c1c502400000c0c000d1206020192003c820010061481c20000e107034007010200f807001e00002c40c0141903e643c1e401903062141c0600d000506 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 724584181 1250 724582931 724582997
    0x1002011e022a0d0e030703030509151902010c1805010e0f210a02010801050627210c030105010b0c06010314011104030320011e020d0207080307 63
    0x50450140140141050101034a0a001659194180c00c0881e84444008801d45a50901c0340100712100c4005000c110344078080c1c1d00e00c00ca04004004040d1184103d100190005400780000081407a1080e101c0da5001c072140b1040c0e28100b56175107000b4013400c440b0650000350350f580c2000d2040300d800001d03580389400e1070146040e010f070411001802c90000c2c507401601400101110068588894110103100c420102821403c960076014169654132807160803400114800000507842c00c0140075104410203824a6940140f0f00582112038240c02a240d00e03805003203d035862001900007240c040800800308050002000c00b5030a00d420f445069120740c2d618481044401070003200856801d041d40e600200740781c10a100d24080c0d90143ca08900c82c3c802d05100080c0001c1056001000c55000d401c020040d003149000074440c2030b00700c8001c032011544099030039000c1018003601b54010180400c90a81c01410b140d000d85400e012600704035a9140415030081600c3c0102c1c10300c80108030032511f610 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 724585431 1250 724584181 724584191
    0x312020f0115170a0b0f150f090402040905010b33070f0b09070b0d020307030c020c010e010c0c0b07110111010608120a0e03011127100807021614100201 67
    0x2607006807549140e00c035040200c003041010000c0da41040c000102d01d9031708480c00c128181060301210780d4008060307965908031103050b900c0000c2820080708e070949490004020034041c2e07903240c0031700025220300e10084039555038132088402e495844c00440304900084605540010600e8128042560016000b070f0001103c1842148001080d98210500e11640410102d183e070319422500e80ca000507580000f40901d90100c4c2d10350748202607130f0107580302d04c200c3c2e60107000301c40d001d00c020707a250055082d4140c001014035000380302650158001c0006c89210340384036441640d65452030941380d00880310460341c90040314209803d17036900c2413500d0007028148008201081ca003404082e9190310080c50203141e002d0116500200e64050401e8400132a00070f000ad0012103203508070301103d0b81c030000580c91074400301c0c1c030300801c0c0b0800e5084042c0d203004040c0842881004409080c1c48511008105000318881c10b50b1502c4005400403200740140340b40a4454001706401080181001c9540002c8045a2400c = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 724586681 1250 724585431 724585451
    0xb0904080415050f161a33030102030a0204030302010e151b1b1f090b060d050c1003050f0a050432010c080f060f10050c0102070c0312020f01 62
    0x200e0031034045408903034408184026054054595001c1e02113041c001a0011a000580e8502400c04a02443c07040c1c200200b0050910314183c02d803001a02c40b556040049011948040701003581003882004107443c94035400b160100007400e90f44109e8850007005c0d0041010020107409004101d0b8900707420303018280e86032080b4050345891100070304034060110100d010b281c0005107842150070b414000c49107004034402d400a42690341200c025011444076046100301080c555510800058660111100a40d6183c0038100b00480742c16160540391805107003550307101540c0d10250100c1e00503840d20042050307c0d0900840856810003400030003e00d092004000c005842c01454120060010205004294031028404000c0c00c007071140c5a103030761034401d44111282e0801c88a512941040c1d83c0b10603079aa0313200901002c203001c00001c60300440201320f02c81600d4062406009004001c50005042c882141c40300031000d440d07580140d5040c0c035140360010b80140c4c140a900070350300502000f40000010 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 724587931 1250 724586681 724586693
    0x8030f0a080717010b03100f120204020304060f090b070801050108060904033609110c150a022b1401080607050c030c06012607050102030d020c16030b060102010b0904 73
    0x202815401084036180c0010285401254882c043d42c46407190b030b601c00c0da100c1e8440489075000fa03400c0e20340e9004141780082c140d10070070180e40541e044a44c501d500f00b01560300380b10103500068800c070350094590802c03079560002d038410108054090021614281170501d0007401d4a603041e002541000440c1d010403007907450b40403960303030010b60602e00258840c0d45440703450641040000304550101b544008002c02e104020244820380d441d40320104408040d42052480600c07076884003c840d41c20180143ca03805411303040c0e4584c031515021001d807038100e401d5440c0e213002d00b1801010300e40d032420120680d402519845907404405104600c1150765041002c8103039640c0000b00150100040090b40040810003407042e607580c0304445046644550f1a44c1d040007840d0301c1f40b410070054a0101103410041c140000c4c0c900d08641c1d048c2c01462510318090040c40296021040341801172007181150518030320070036002c8000b14010b044899032070801d000021b081d1340300c3d050500d12841800c0180008140 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 724589181 1250 724587931 724587937
    0x1b05040e040b0903120c0d180507140a0b0a021c0e2b0807050a11010519050703111b09010909020a0509060d050708060601080703022811010f0608010608030f 69
    0xb8000c1c0303241c015580e40c00c08840c9103200f21aa46444401741d00306029243c2c40140140844c95003032001840f40c28030090344682c0440e5030280180c181c0e80140380800403d42a01030001114401034a00d00065880d034200d0481039224518800050748985901a0821011078820b2445456490205140354405c0300141d042c407d2800014021071022484a40402134803038003151403640510000d8840c1c8042c10181c2d12422041c0301520000c0480517454042c1d807081c81101c10f0355011254000701d000002200703c5042d084950200d00744888000142880ca0041100440301541c228100f01c0920514040c488061b0060b402032810500700202d0100581e01c8640d41410b9600958201c0030fa40d40d0080042c030462070b041c0d005010390240da0301c0400c5042c000304c2c2e403500c220800e88618120751203030300b801c030100e00c03441c00070061440c0d0440c2c0c0d80b2401c03d0103101c00e483c54140303450041c04d01141c1d03078001800c45001085451406981d00b808121004c4207018000c010308070100034500f80610445000c81501c = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 724590431 1250 724589181 724589183
    0xa050c1b010507031d0d0506010302030712200a270b010e010509400c021b010e01200304060215100e0c130605090108060d0c0620060a1b05040e04 64
    0x3062500c0714004070040211703082403c040050601c88480c2d9a810940d0702c1d070302d00703002c20385c082d001d20301001c1000c040b84c10158011540c0140f43d0030a02015282d0601401a10602a541701040500004078135260544101100d802842806020342c4140c40c164200c40210030480c1c148071181080071003903a080750507246150011b07600d075100c7d0003945640e0a0525a001c0010800304a031414000701c030205400304401004c606c0d0010808507080740c40130f80ea1401d2070045910b9440368000403096551040244101c2e418040c144210000201e02d081c07400092106011183c035840400d0400c18650304200060420399003042294407420b2003015020480300d1405500c0f405449a004920f01203122022509910b000c24412842541c85550062655110880881c0068010800304546246c0b24030b00d00c21180d40001c0302611580740c4102603031407408115020b06501d40d41d040701480e500c020302070035100e09004500001d0701e0310b130040071108481c10583c00381c0070090140000d022143c450b1003001e41007 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 724591681 1250 724590431 724590437
    0x301140106022a03030c011e0b09072a140d2a0302120c03030105011205190e01020903070f09150e1b070203030a0903020f03010e030f0a030605060a050c1b01050703 72
    0x404601d407502c007169000c101c2909848001141c280b074030301c113501200d1100411045c0711a61948c480710710f01a10001ca0806911405480104003814064041d00401c0721010030001c800010003a203038032424400340341c1074841c602c008444070000303442801045403454007801d0003914484040c1d81c500401504202442400b0356010025040c180200501e008900540c00314a036074110804401d9101d0b08203124541c0860202c0c1d4841903640e5942c061140f06150a03503006484184000d150320280c155900e0030350040d50f0030401c1081030340f404d1020308c1c041c0c000f080c00342c19a00c1ca0500d20000721101c941c54030001c400d400c402807003540c40310644140c000e0300061140c0641d03500b05161410b130744218a0001c1d4036102c000341a004294002c08444122402110b501502c00e440301d040c54241c4107440506501d80c1c004000c07c0c0400e001b03250103000c50800034a0000b42850311074000c81c0e816440000e075000803c0d40428440300e91102007050325041403406204507002604a400a4281e00503890002c0074 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 724592931 1250 724591681 724591723
    0x606011115011211031002120703060602150406021605030301080607111b0a0e07201b0909010f05011d070c03080a0e0124081c052203060c0e030114010602 68
    0xb40f00e80449200d1301020000c00340c0d1442d00304008031038001d6209881c10898042d04000007811680284216400c0f18419005050b4a5011119002c0304500080c81218829428803012050b4070301265900d036814403a50065030740b941040880b070315000c0014100c00403c0020b030410b90301c82101151902307104034182c42c4c580c0c5d100c900d1400100c1c250000d1f0800209400c01e40100010700f548654170318060b500c00e8984901110ba4548070780e46442da214001c00c15211900420285414610301480d80050b48200006c0c080480072a058140c40e4280d1200690075500412607000260000d400c6070405406d0414072610072203950060f0101000070010080d007951012003105444080d0800342445440300740030302c00d40f00083d04802800e0000c1c02105040c0c17281203800d40c0f0080311050789040064081c1c407203038200040401c080340a05002c0c883e07000b40c00c42840c00000007a800e80150913600809031a80700d03d01903220180b508680215202880c90108000100f01403074011401c400c904081c803201c401 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 724594181 1250 724592931 724592933
    0x6040e0a14040f030e1002030a0c051f0b011101050712020906070f21020102031324051014010c150f090c0806070813080405010c0c0b0c06060111150112 67
    0xc018000d100040014010300000c00c01082801d050f0305000780c1c031079110941021000c5003407001142c500312500002d40e1003000000c480c0c5001d995000925071150b030464141e07007403c0121f41440900d40c40301002040e1140d0070803d1a603008042c04a994400078001c02243c64030982c01415021002a41601c40307034005421120b6881c0c100c01c551036140c10000621042d55a8540303d19880309152100b1515001401070703180152060080380c1c00340303904417280c09102c0c1850b10303440d044510103000c10441043c1008681f10304107503800340d1032203210b541414902d220f01d00064003203800f510304000b40c100042190818001140d62408032805000d400c2c1c002511a2006961001807649a10145c40c600078248000313000c001c005003542c461051551081390740d494000e10300c0c00345010b10100400942040c041401203510611503c500613014850691035240d0701c01044100307601c0380740c1c140f1141c1c10a90800210703503008000c458814003114000c21440c00030a41000303075841c06015105c0e12000d0601400 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 724595431 1250 724594181 724594201
    0x90e0d090b0a021216050d0e1003020a0206150d12050c071413091401021b010605040c051605030906041d010f1404021c0e1e0d0903120903050123011406040e 69
    0x1140c0994020700302c911f04480c0d01e001425900380360300094481c800005030980d00c0c174802e0080d210090354540040850b521019040461045070460940d0014040c003980c001141c070003229481d0050a64562586e00c0d1400c4030040c0c1800e4079034112614040d80c1c601c4855081d105d0080d40d92842c0b942c4c400000702d05282e4541803664401e4100e42055030741c0041b0704000040401548041c56000440080100d03a82c1c0c0c105102c20340d4072070b01360500800c2007404000b160314100b008a10226105905403860104050000f51080e0030680000081400c8800c0300d9100c05004102c5074007401071010150300d07044c80c005100340c4c06403009401c1da000701d401007031180000300d4401d017070742d04e000d880c030401d01000e40b0181c01c240d9035440d903000c2910f0030341c0a10f10f401c0c040340b0041450007064035035a8640b59290b044d0384500e6003c0b040080c40038100080d511001000c62020b224000752030b0b4101514403008101c02019410203841070f00680000f06052140c05c5280e81c544e41140d00301c862181035054980d48807030401d = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 724596681 1250 724595431 724595467
    0x201060504020a0203210c04050d032a060e011a010e04062102030d03061508091e0d0f080603070501110304090603060204031a060d020415090e0d090b0a0212 69
    0x6641c005002050007035840e9000700c00741c250000c2600c20320200c541020072611000405a40d0154001c1d03040106008a0030103e9490040b24040c0c105496a0030140c10f000d400c20400800220090a110050301c00308000ca000741c8100202490003880980c0302d101a03000e4007080e5401490612031035142d0740080e5141d94001c4001080100a0064520351780d00b0221070500d00a54120b100b4010010f812006a0083c0700700c509450712000401c0290748100ba0580d00c1d640050701d2200c0030710403052480054070180c9003080b000400710028080c50340052a02610800683d003c42d802c0c403e95a01300602d0361000250070045400034a0701c05c0c0102032900c5201c1c01d62103941c000c0d03a281810140301000340480758005200716403140310040707035030061140c080310446401d17103c0a81c01a14004100301514254020140c2c455103070080c034003041e55943d85101151780340d04c0d581009403c0070b440c4600c016080300e004802018100e10851400d003450100a4a9280241002d10600790100e000507076070b0701403408 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 724597931 1250 724596681 724596689
    0xd090e06030f01141b040e070e0a05030f0a1b0b0304150e0604120f05030411090601020c04090f02040e07050d060e011e0b040522020114130e010e1303080705070201020106 75
    0x2c2042801c00c4900798003010b01141c2e00100881107100b02c0170200e0300042110102c8101c444207840b42d0304c60b407904541c45030710068a503a101859038404100c40d601030104680201c01d0500038022200d0302d19210b041402841d4002c011042c00a808200c040400422240d210380e202030402d08071440201c2e10001451040061350a1f0320425040208009415101031440c10740c51721038203d82484410102d03001e02c001c64004000f20080503075241c5038181481c0302030704403c050042c3c400307000004000c44d0480d0815031042d17903071b00e169104950a40c1004d10400041c41041d0b00508017031030074000416005109054002c00c881c2da00d001c020140c001c20360048000d44070401c540c04039540020502d2028200e41000f0610075454140841c4485a940104801d0750398000401001440345400644411103410400008024100301411841111a080720090651000c8c0a001941806003080d21040b0051040d0075000443d294030012940001c0c149620202d2850700c69070344c000c2403004074007500d00c2d070380 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 724599181 1250 724597931 724597933
    0x1090c03050d030e0304050f120a021c0b0c070206030f10030503030103060504061a0319110910150e090412110a05030307030f1802060702121911030d090e06030f 71
    0x240402006000315030110500515603003440201444e055141d240d20982c0b1503241c2c00b150603000d00c080c5050040581c4100b410711002d0f110840003075008220107900f07240b5040d00d0b1100366003962080180c0c400a1580120b0400e90444c01c18481d98046102c13803002520100d00e10880c480002d038107522181021000c0c550090540c1d4907940e40b490b0010107007409a0f0300b104c00604007071440c07100c0310390386031030b03004020000700103010a2041c3d0700481c5000b400c2040030746440351022f50b4252240ca40300101030141c4400194405800c1c0340c40703006100c070100c45044504010f4101c0141206640e81401503411942004405800d0012100145e500d280355489801d4903015044040c024402e012003c6c5106581e0354400340302c2203550b54030000c12207070803035040007400212402030b50160501d4409044418030140040e07154041c3d0036515850703c80b4900314400508000c0c400041001a0b42030b14400c0004e0650041c0041402010041c201e0509802441180e5402c07900148035964200311007112b11100308 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 724600431 1250 724599181 724599203
    0x1d0a02090c0d14060418030f030f0b06040f060f0507150b010905040504030906020c0f0109090e0111040308090102120415030c14070f1a010f090905031b0a0204050a0e03040302040b030109 82
    0x30910f61802602218440d10132031404c80700910074002d0601300d104103a03240c3d43c0c00400b0411164150300900d21100c0c0703c1d070102d41d6100c41118035200c40c0000c0c0301402d80001c44096403440c0560040201c4e01d040c080204001c414020040000c1c0c0c60391080894810046000c40c903240d50200407140c00074075074003171a0300c2400d050501042c107070440520400e40718160700f0f4664400d10f075000e00c181d5481c011032603400602108010800442c1980c82102d620340354800108500a10040198140e00190000d448241000400152035030b0104014808522100e03641030600e450180300d0342405d00f110142809040c1c5806249034070170311840000285041c80c1c0b0b40581c039810346040a035000c00201604444800b0740b842186a2000324990752412281c4c4685001440d5043c0032451018018007003080368a48000c1c02003100420301100f00040c116901c40040607120b410340104001d5407406416684e04a1600c2010608403101004a03400d90b50191004600c0321402400300b8010891140040e024400303030 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 724601681 1250 724600431 724600451
    0xc1b0809151209150903121003050a080406030605010306050f0f0103110d0b0414061c031b11010e010c08032404150e10080a150f0f02030a1d0a02090c0d 67
    0x100340702034080c000581c1104c400c54607402d68002c030b2140543c0d01d240f81e030f4028417500004079000d60b52070382c1c001c10701d0300d02e2450640d1361380d9048d00c0c0002d00c08046030b41c1c0d0004134051100d1a490b00c1103400420092909010091030040403820850f0740f5003080e8081c0060450520199020313811a101c071a184085242d66503a8404842c1c00406108814521550510501c4031400c541986c02031b0040500400305102100c000321210314407202400c0480c02e0080203d840040103549003180080350303005000c401c0811b030303407400010a11002203044905100c0d2102100c40482c20840540f41d200041400150100c40c000580402c490524603540f03a0281c20100e0a01020b002901b118040b20340b01d914107001a1108405080342c882140105035603544014000d1005c0b0300c0001d00d907030781c2d250f1104000030224a8421008203580003200551030040c4c001080c00680012803241405840d1000c0200100c142c43c032000c143c03504d0000402030f12a000d21008038506c00d246000711034080d50b06003820040c00c408 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 724602931 1250 724601681 724601707
    0x51011100204080c060405132007030201060f08060403090b180628080c0316032304020102120a1b080f070c050109150e151b060a0c1b080915 62
    0x10f400f400100b0b004804001c011414200156416108010158000036801510300380041ca40d80c244451070f80ea018142140052030200200640b901950000c100b442c1807004a10070800f1941c0300b521a81c2c0080f04000210340e000d2281c000340c1d4501d030aa40d9031001405218417121914a070750a5000d9400186206811103540c01010300c0410b481c013207200e0007254103054034805402c0729411000ca0007000002c1c0c00c00f45410b010401c01c0b43d00d0400045581c4400f00c05030b014060b0703ea5150720307141207806000542d0780400c4110362215030000f1803407514044d02c400500c02000302c0b02200e40c2d280d8001282003004000001c0d02c480740034200100391160428104103e14001d07600c6080e0100380c1c9000040342c01d4031074462040e80e0701c5180d00c440644040307290a100381020f07510f0640300c0e101d0301801100d0300c4491208446040f210701700300600c894100008801e0417109000c0c01e180030302254006030600c5215018600d070360143c00c88a81038803800060045012a06840d12000d520240051070f10801d0b00 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 724604181 1250 724602931 724602937
    0x80d0c091d0a05180d0f0c0803010e04201c0203070b0a200d0507020d0f02090a0e060606041505030405012403031b0c180f0603030806030f0109020a0510111002 70
    0x1030350300280709903111805040c4405100c82e80a146903000000941000b900881c180e1596191b035241ca8040c8940503111180107410070b030007c038248a4210140014000200b00d03907007008044840e40041440c032580011b102d0445060300c1a503c0f00c00c0501d8009540d020301c9030070000c0c0b415102170350f5990540d00300141200c030002c0e00c625603280300c2c00c1141d07006000000c60044218450302e5035031502800d80c003001392150040f141102d00240080707017400181c40b4094000c0c041c601120011030741c00b0806c4452404c120340102071901681d810701040000c0c88080c100d80011100c1410020380ea501e0324240720707000d09404500050707030500b800e84030000c1c044900c50078004c907802079540000100c6040f0411184d0100a0740c00342c0701c031203281001d1040c1c2ea1003182041c203c502c20340f000a041541801002c0c02d13a000d507072080d00403401480070028141400c1c0703c21201094140e008020800203540011011006401030030b0140251136014611035004950303500c00407a4070400c40303c01e5515410710300c000e54 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 724605431 1250 724604181 724604191
    0x60204060f18031401020702031f11033606091507020609070b090303040806090a03030b1002030a1209021806011103130311060909070e180103080d0c091d 68
    0x8948220311180c180c803424920400c20401880c2ca001070f4078544800e00410588644003c055508210040c011303501007181e45000c044480d10070107000c46d8000207000f00c504807034016080038010010071480e22049105040302015081031180c898803409a01802c859000314032103090320548080c0601c0000005444085c0841015640703125510404100e071502e10a880c000260360142c00140009030b40d130800b4129821000e001c4904060351030384070514220066441c0380240d04064214424160f040c00358440c401800d8600b210f00101515000b55203110f415024002c0201c80241000300f40010b402400001b42c0041a040d003145c0c0c807a4500b0440042500d145000c0341007181d0a008020700401a038100c40602990507106921715219541d0980c4090380082d80324004200301c111070750f1403118486c05a001c07903441040400c20407050210541d515081180809400b400400004506004a0b070818078081c5020910f2081c10b00c0c00d4542002542001c4100c00100002d0301d500100b01c45542c1c418 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 724606681 1250 724605431 724605437
    0x13120609050c0d0302030304031d03071d0a0b01080403030203070903080408032206020c0609120303010b0c0d03091104021b0d2111040b250804060806150d0b03070503030706020406 79
    0x14030b6000c820014031500c850030060240e0020700014001c64010140001d4007e0984240c801840304000045d00703004058102c6031011502c107207084c49a40c040d030320866000310710034401c110803c05407001900c030840040c8024101074000002903079003849002c285004640c84442142c07100d89501d1041d459400c00380d051a0341c00040aa2111980d150102c00021940300f0f402034404242090240900d0b0b0f48000034094001703010000710040100b08100841c000c00b0706441c00f1b51114500f451403400d182a458000007054145040c090101d8805030a10111040c2280c0060b1b50f03407120407006141c9002d0031040001790250145d100703981a0080b600743c0b281c81d000d000c044245042e400d141c10444103c0c0403a0900540c0900040c011a08580010540d4207400380e04407510030142c00c41c211449040901c200c8520102240c1042440d0300b002946820200488280d4100709802260b0400c0340191290b403100551140c2c4051650344090004002500b03014054a03507a0040f800c014000e90310500ca01000 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 724607931 1250 724606681 724606693
    0x70503040803130507150e010e220e060405060108160f17010906050a0b012a0206161e02130c0e041e1a0906180c0d0b130504051e070b1312060905 64
    0xb01d9881043e89ca1100c1e81c00400c00142005001c0c000341c503003010b040d001c3c1d510703a0340c5880d90407002ca010010944114032410040c0386540c148820b117400c040e6a401401807030240740c50140f00d9160164050401c0d11419800d00d04945d028154003405482c640d1005401341d407906003031020125081e048145030314800e880b4440c0c1100143c03200e4035a0700308241c442d04a00f118641c08801031810303c0080240701140044101700c3c0410303803100d82018030b20704440140d031441c0400107021800e04840305824800380d05000c014001c2d000d103002d007100c4101b40145102c4e550b5484c82811100d10406000d1407209040700411a02140fa16241d00b2407512002d0709101e00441400544c6078030304000200803070600e40c80328080320340740c03501402550b0300718000b030b00c0100e62a466070710190b0711001c005040f00b000007a00070503642000e042413820501081844014a00c54040d0384641e120000350400407100c1c21440d5659518002016810500c620b401c00d50b51209095092024406544c10107551a4012415110 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 724609181 1250 724607931 724607957
    0xe04050f1503030c060402061b070806010e100e130303110a030204080114070c110607120c0224090d14070b07050601050a06120c0c12030e010509030307050304080313050715 76
    0x39072030248901c0c20340c04da4043c50001d40141030400c0070740400600c80542e1000f80719121075090600510b90070071512548040d004008800c14045500e40104603511040e010398101605034002500007000b0b2103400e41c0b402101c40030580b080c0d10010f454036212402c1c0d5100c5d00d00e103c009000c1d50141c40751001c50340c284074100c0101c00d405290320f4081c80240e182e000d0340e000e459030350151801d0301149480d8405020b0007007802084120801c0090408030383c5d504100d00300d00f0304c104519686120200c0340e00c000300d080748001a103c200e088505486080398002c2e110b150510308100e9480d040ca1030ba0400d8007510744009550030040e8058144184911300b03540c1c1c0780ea00d8038288404080702d44120000203c0c4d00260014201303842e0720034181203103185402e102892558958400c1e201c0c4101388080041da03907009000710440d0a10030070f50070281b003902452941c280200010600c5c080a04083c092800010100d2140c0a290400d640600d50040a55a946980301c25000d00d00d0600d94a00b004a403480074051 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 724610431 1250 724609181 724609183
    0x32514040c02061b1c02210601120b061b070f09020a020c010c0305070210110709110306120a0c030503130b07020a090b0612040c0312170f070e04050f1503 68
    0x400c420001d0b4002c200c0c59807400650a1107100c090007070b22810000300080ca0300c0e12464580c0740100c4816030b1025a4440e0044e06a1011202001a00440c20742c60018480c050780d0004601080080300303030001c03401d143c001000800034400c0381040d04540000f960000c0b04c40102045c00003c403582d28100100305030391401504c3c181d1003008100401a0481c41d007990305036000745814100c03540685410360a180ca0340d1b000c200b40c0080c2448550103d003052084503010031080141202a08001005100984215540700154013026200b0b0344152800c11024690641c1000400691500b1001c054800d03a07503402c207940c07681d110030901625074580c90804190701c001c2600321000280d005c0c0c405604179203018290001842e846485c1c0b1380c000c20030456450140c0400614a0203540202c0e01d001a09185140108205040450703240600c03c00d080c1d0408000e9006a4240d40892483c6210f115030384c0704003084503043d103260b10b15603000340b41c403050014044240500e1441949a1066075000c0d011042c105 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 724611681 1250 724610431 724610441
    0x20909130614130807211116120b221203050f060f0d081b070504051003170a021912020f0616111903050d0b0d110f03251404 55
    0xc000c4500f800c0c3c0d1000700051580c0d00401e03c1c5405130701c0c1441c05540d501e0500040030310a4925000040e1980603012030428140b0003070380c00b2002001181c0031145000185050307425218405030010107014002190341c2e20705000f0b40c0510200155480741444c40d442c110006e4480c0b070700c5280000780741c200094401e40b21640164002d140c0100701c5510300c0408000c00460441880044a550704184608070300089001a550342c0001c4400150141e103040c1f03c03d0004a540041801c02d24114030141000818801c901c0e5101086403440a01c0d55034084280507032806c000c0c88003016002d04c042c00454117000e92180c000301064003d60950380c3c030074004086140da5042c144d4a00d810034020340001a011401381e09401800c0d40354030207071118840e585803600c071400310f03074542503010800003c2d00e00741c00f801138841c00003560760486201c41c1184143e01d802802c5090040c2c010b0060604094441c4290740030400fa44038420300507404085840d0003111500040143d20070402e000e20401e5036001586041c0c062 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 724612931 1250 724611681 724611691
    0xb010605180f13050406090203061302041401050d03110703081809060307030b241903050706090f030b060d021e01020c0301110d050601110304060201020a08010605091012020909130614 81
    0x1a00380d0a07001c0300d515000416028000f206c0315a41c0d10b4070b080058800b0b02035a40700f80140352100303109611034014007050b29600815018080c030250018080c41c5d031100c01c50652690540b030101c03603903511024114035081c0960800f805540000ca0800e402039904102645a80401c3e141401c0d15100c580901d5660301090100600384400c1400060f03c40c134a40030058408034085041005208000022620003441c403825860705041c108000d105018080108070014005443d08078001468078900429100f030740e00006213424140c0c4c01003111a81e5030b4514410b41030300284030b0300800f07020f500c0100398151031101a42c054003034481e0000c280c2c541846154441e120465034140b8100c01da40903600102001086141400f8405c1d0540e241500e003003001d031024088540006980707140c051400782401105030300440400904103c41d400c26125041c0f411480c8986042100300c0b207002104900c0a800ba10311501d030006110400c0040c020340442104a005000700d40420007002010426000e200c41154 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 724614181 1250 724612931 724612939
    0x60e0a0231050a02090d05010b040e070e0c1c0e1e0111030109050603120705150610021509100911040606080915250806010f0306210f0b010605180f 65
    0x51450520315a0342c2107194071a002c2d02c40185800c1c1040f00052280f10702d44000c1d18141e55405110750141003500c03c000c1441a0a001048190325002c4003040b00400240072006103031003c01e9112404a801d03441e9580150301d16001c2c0300414481c1605956400743d403a02c3d14541803080e000d1800402c061056515078107200c00352900d16800c040042014000140030241c0506c2903800c43d440d4280b08201030a40c403032041c809010307070b2000020314041d1200090005441031005000560b20207400046000a485440c0109080c580c1c0d15082c0900344641c00b60307503607082030a22103c6001c100705201c1c0d045020004440401c005d54031840e007100c10900440c0d00300c0b801d501001c00d131101800940f62075603010908404150207201116040c0c0700c0f544100441c040410092070a0028668005507401500682e80c5400c200c003515049180c06580400c0108044022040d45500c0a00c800c04c5460b0541341d0304065000010f50351035400415591020b61014030a444009504081d0b250030441c4003001c41c0018 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 724615431 1250 724614181 724614259
    0x90609031106040b04060903050d02010b06070f0c0503030417060a0b01211113051f020706110a0602030f06030f0d0801050f04230610020a051b0607060e0a02 69
    0x940d4940c06800030414480d80030314180000180c2000c3e0800030009458660341f60034800385145049860002d030800c22600790f9041011928150301e4070020384002640001e80c004d0403225604280f601c260850308040d805000000700030940301c21022005060300e0b0200100c488039529528400304a0328070090b164001405100301000c1423024411400402c41d0541c40004c60a40c000454000c0b40e206140301c610480c0d806604100b18500502d4440404800105407050310050080080d1285c03401c0c01510140404524400c0c94010100040d5a4150744500115541d05111902402c14082200c0c0c0300e10074411000d40e42030345175001c00e108130701804580b42c1e40d4981c0d082c10108401d20b001c400c401d542240d030303417585107110305500720106948000c0607202d002c01d424114140301300c410704810034009640c0a100240002403001624940514041012030b09085840c0000f41c014031610902805460a01241d000d1003c4003141c2118214400c0307403031108000341d01c1075119540c9400500342e441400c200c = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 724616681 1250 724615431 724615433
    0x30c0e0103052a0f131418061003141021170901030f0218010e06040b09040903170a06150c080909060109080109050615061303060e07030b18070609060903 68
    0xc0d0310743c010704030b600030090704000d103040801005400c050300c1c2110041c0782000070405620a409000a41070050b034102481601144612440c0f440182240f8001c0001c02c9900802a00c654400c44080d0000b03150282c0d2070814600c10341102295002c1c40701415202c030600040b5001c0300b60b0401d40d4503401301103020313420710b90130b41c00c2d01c590041e5000605050301c034103004280010500c01030507031041d107040060150343d132070000400030042236100900803042000144000c0c03c0890560702003403c115000b18544445107004c80c1d183c2c0100981c420f9130b0241c0c0d0180401c076240c50300904140c444e080304130902d1017802c3c4070031507800400300704c05040c2da08100400c10031401c1040f001e5070300080c18100112680d550704180303800c41e002d50900b45e4160b00001c0a101034015110055001e9903002c0700d5140c205030a14100541407070880c8030062000740d4400410658a5003402058021500007072400c9540c0780403000c110130340100180d4203159018094002c03883c280240e603c0c0c81910403a0355021051811 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 724617931 1250 724616681 724616731
    0x6190c03090f0602011d030a1b060906050f09190b01030605060307170706090503010c0f0c11030d0503042a0b070309080f0106150806030c130b10030c0e010305 70
    0x401001a01000700461012903615a4610208010a0b4550001030341c030004030340801041800c8101480c10303400c10032890229650020701090306031511046a0f034400024501000105100343c2d00400d035034104420020f0003010208030502c100c43d50000c0d90032066a213000d0020400c004030009110311811001440803600c1d59010942c0700d00d000e42290345598488001d4107000c0d64249120105030700100c0c2c14455644d000480d400180029402800401900c8902400c8904160f500e8002c018441c0789420501640101521400300c01078240e54100340100d5008200da8000c41c0c00780e4080f10881c89526943e0f081541c22902d03041058100c1820b50700782080c00300c540e40b20020030f8040088401d40442d0040d8240441c481c1b183d051000003d08600c0d001403d10180c0c5200c65200910100c1070420a0a4401090036105c070801181c2904140c811a40c40c1c000800c40b4010585d00322010303940c60802540c0540c015102c4090641300c0030b01c1075400320011000d850b000c03100c03c0f203900522010311924103c = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 724619181 1250 724617931 724617947
    0x105061207020109230f0708070b130f09050f010506070215090303070503030a090201020f03250c0b0c0a0b09030c0a020607030e1c2108040210090f0f090501050619 72
    0x701d920001c1900d04c40c80d100d4100c06240900205502c282014803000603150070032108072a040e00340040e000440c90403441c10388600942c0325040c0c1c40c0c0000601480106d5140c0074100240210000300d1185a071190341260042504840c01980700381c0003c004502441d043c1c080d9201c07a540113041c807800511014001019403c0351180c1e6825220501c6000f0000d0000d101031486051740e02e100107201c5501e03000080c641152034800300396a400400c180608030000000700d43d41b40095650404400c0803030310b4255140c02c1607a1124108410126179203217107680110b43d94110500030582c4001c50f0729107105840d220302c04c8020f000141d610078503a16005007801c002800ca064001d003884100d43d80c80354041540d041c0b2040340d1503080010490701401b00b1600d0f207009040308030070450300d020903107018002600449024001034403984000740d0410f03035144030b0b40368040984103486212148031b40c1d80f842070f20946030f14020000c840342000004200341c100f07a03007074070558449041f0440400d034000c0d8055400c2c076 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 724620431 1250 724619181 724619191
    0x30d05070329040f1e0501060503240d14060a0b0609010e0d06091b1707120f02040f020d0b0f060c06460b0f030309040f02040e13050f010501050612 65
    0x2030b214008841d048805102c0c5280302012085c4d04c25200c0340f010294411944160030a505005040c024080e58016018079224500c2c040070b40b6448140d00500092520030300d04000603e156452000546000408100103009034165501800001044000c201e1180038504100e400182c10110b490901c2c0b8100910440d003500807040003a6008031a21a203400c0038800312600d03c50b6818641c02c128014000764003200502c0c40b5405018035a080030f564890075007403814060420f51010300e105056542d00d0380045c203641e011100c110341d0fa01c540c00945010742034002d0b0013841203804010b000b910707080030021600286851005064180d85000c000d10f2031001c20114442e42c0819901044a400b4400c83e40540012001020030f0340800c26006a00507121442c0c08240a03024060406149842c00020740703032041c40407180483c0703c0c030700c28250034001d0060303600c1071111504901c10b000300080b8001c03420440500130000e44d0386160a05400038240c480a208a0f50405006c200314401541200c030415000 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 724621681 1250 724620431 724620439
    0x2010518040e070306150b03090309060912011d0f0106030503030601111006030606050406080109050601050631062703150207021305011806120204050a0b060408030d05070329 77
    0x502d80d40c00041c503002c00340d04226440d035070b2820700d500b4264a400180d0000e003c4d0314212481c5140482c0400c1d1039010740805c0c035000b101c000c180c0c50b206984600d22201c0c3c6050300c8008028031108104050358400400d45040000d016030300007241441818020002600d8004008519540700c000c01101e614100a2021026000d00c0d51091096401d5004100c0258043d8038046095428a0100811030b1896440b02e04a43c2c0741010030350024001103412411030705c0480700349850f8220030416a2091010071486981c009240c4403620b0360400c4000500280c0d1000d40d129141c1f150107140c10064656810189816107515000810014800762038008200d400c103040541000880d6000c908003100c200703d580d00c2c0da51076100512201c1c0107003102d50b0a045c200c040038410f203850011104200c0341d0900c0041e000b0341c1c0f02e000080c040da0842c3c0064070b4035900a007a0903926603652052030345a800c041c1c505d1428130b003004080340c011071181c040d280c220101d59102c202000300440c0c1301c0e17040b001d00d00803050300 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 724622931 1250 724621681 724621691
    0x20c060402240703050309060a020705060a050613060605041a13031202032a01200a05090427140715031a120307020109050d03170a1b0e031501030201051804 69
    0x500d5282c1c400351031254481d4445544904010030b00c4d82c10301e200180780001c02803050005401113800002e08030703009040380c0400100f945860780842ca01c40014140e42c1425030034484000b42c0b00790300c0320081c8112030302103084600b211700d6005503101c540f0034010200000a8803490510224100550101d100801d0303004480c42c4c140c2c213640e11000c6140000c0d4240301c1410b6220b101c3d2003001c080c069440d00c3c03661080b43d9a00340a849104a01038080c46030140100500403445200c0c0340c961307071b01101c13402071010b40c20440840d0303001c076081000031944422540c18071400704c030004017100015400291488030798013802c6410401c1d422002444400003c9192584917020007540d502c4001e440a22240440051a070703031903031400003501c8001680c0c4071074003075030401e801c0b480800d501504040386400c50030310b00710950b250450242d0191842c14013444101540c10b080c00c01ca03680046804082003001da00b542c1907540c5514141640b11424071020b40480c000704560045403a6110700329007100002403000032 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 724624181 1250 724622931 724622989
    0x20a060c03140f01060930050618030405060403081c0c020d030e062205070308220e04050607081815040317010602250902210901020c060402 62
    0x8203945000c280382000c6036540c45200201e02c0340d001c240341e0041c03400b90030b1030f1654900000148a500c0611480c045d00c0300c80c40c20a001071700c1384240510101201e5201c42c0342100103041c940c0e110242560141c55103003101050481c183d501000340c0f001c880004001c503060600c2c43d1a1408a035015441e203080c0c0c010702c0b2600419810052051b034a07214800d60007088800c80e00d030809001c0b00c1c0c47c034801840f0303640003804216914001c2020030071034014555148031881c0103440c040746080d8841d0802004580301154191940c0381076200780d450300300b000b9140e840040d41c0380c4201200c0c01c0250b502901d140c00c403034000341c00035000e0801c070b80d0815a030010039207084050081160070003803400303041c03c02e4040003070a00c0b0a1550001042214514005003031020b5458480065540c180844030201044990021220030303814a12900004100d00e540641d0f46c3c644662001203507000c0c24100401421081c004a2011041442a2034101c40311000401c45a01c031074080109044801c289110b403148401c0f9125 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 724625431 1250 724624181 724624193
    0x203030a020109050c0d0b06121f0c03110705060609090c0a0b12091603030309060609020a0309332708120708040f2a0b07060b060f040e07020a 63
    0x512105035500000c3c50305458503185050401e03140b42e052062104000580100f1005540d0941160b41100c41e00140311946d00070303a05022101844545070b04490885240d00d00382038114641604040c0d604006681c11046003d8480c0200c0d40003800f0303640700c20000703032503030030020001500036030000e00302d40d68008102c000400e2011660041e8000b000c011030a501c80e02468070850f60081f90407009081403103c00366071441c5456040c4000740406441d0b81d0701c4003c1c00311300c2c0c3c882d00140003400b0081d55603010383c68000e4090180070304104d441492a10701000100440f050b40080d450180c11112803d010501c1000c000d400080c128445c8043d082c00d40300305074042c2d04240550644034501c40b94540d081c140a5000c10314006080701b042c09100030400001034604100d42490f560b00030034a02c2910202154052000c244902041c0348103145403010420880480107006da0600c54402844106070700d0301400300c03600501007a100c004000388000d02a490408900c2c5903c0f100740c0c411201996566200e00c = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 724626681 1250 724625431 724625437
    0xf091305071d0607030806130e0615090f06060301060513213c06091506090b03030712051c05010308030a0b060901170612031306110703051b0607020303 67
    0x10030003180d2009007918552200440b60804460101c444505081c0c0a88010703100d800c0040c6454424030f91040311104036541076005240e852001001c50b100d51415001c61071002551080c0b040c46083e2f2940012408014521294401d074005440e00d03040d41d00e84403084d1060f8010781d1040c48944110074010882c0340c115080364041c224611501d60b42310f141800c090011300d80c07840b120b40e15015000351042022206501c00c1c0207030303035112031200700803c0e0509140004100000e0000d082102183d1680807800c901d801c91001da0700414410001311013120101592417090710070003070602e002c0c003c0b1048014001c00140610899050b43e0002250510060600310342c401d80080300d50b8040401408541ca8042c41030090020040d188a0301d03190b26500007808a050305030381010746629420015000380c80f03400e1001c03045d42d0700d50300b00c0c1c0e10b8000c1030b030f004020024640106800501a0041009800000600003046a07040b42c0540320070415281c50b00280c08000710740f83d4200800b0014440183c03010001 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 724627931 1250 724626681 724626691
    0x11010f050907140607120e040e01052509050a05060a0e0607050a0308061008040b04020103110a0c0215040303320f0a0e0603160e030f0105012405030c0f091305 70
    0x501080b9007456000d6410740500044a40030781018008031000403422a503010b1084154180841c409a0700f01c00100941408482030915500741000d104d0481d01d00b0010681c0c1c0000344a00c60720b0707080500011035113160507100c0c1035400200404100250b041240050200701d8061921a1901c281040070600301d90040f80c01311096445114001d040c903a00441c2281c020301d003210120b6000340f119100410481014101401c0c40300b1041c042030440e03020342d001a80c03043c0c0c20400705807500702d06070700641031078800c0405a01a889850b20f03600390f000361004490503258180c8808001c0800c41d1016100c8112042c001c4204070b400c048421001d9840c207000e4180c907080d03407150660b03d02e00080020aa954860320041c0181400d0050001004412803201c0844080d0702d00702c030107054101c000a140c03152055030440c82c0d500c0d02c030002c1030380c2d110303011810980d40300492003c2c005890803004036400d1001300d802048106007401030510100d5008028505010000d03c4500f903000d103043c04800304d40040e50 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 724629181 1250 724627931 724627933
    0x30f0601090c0e1f0309020316031401090b070503070e152104231014010305120c030403030e0d12050903010608011e051305160e13030f11010f0509 65
    0x200400101d5064011422000014070385600010001000300d910036903105180498412421042600e0a100382d004c5080075800604451030002e400d00621024026808250b0f145011040b0300018081e050069000e16503000505900d50b56a2100841d110703000a0310110401c128908015040da440c0070102180300440c00745195940c410504103080200030a441c807080071201420040420440180c404990b070846074504038100a80550908190181301c02c490030310720f0418014680804400d0b0181070f42e12800483d0709484a213201e0004602807284055a0359108120610000f0b00c141045820701c04041c01c803c1d4203520682e190740740200d0014031400007e00c045081e551b2840c00740500c800900e000310080200724401f000c1070394182e554980c3c141003e43c803403001c110450200c004d030701c0c05950000d0644070100c3e02140b900e0034045c034600c1040614100140482c0200e038240d61030083c0c8640c90748805400148190043c1c450340a101246031455603100980390203400a409103520030440e4030 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 724630431 1250 724629181 724629193
    0xc0c0824010509040f080a091707061106010e010302150903030309010e0c01090315111306031e1e090303180605100b030f0c07110d0f150b0f040515030f 67
    0x48140e1501000581c021071144442505000100c0c00d00096140100d420000040e62695800c401f601c04c100b107640030343c2c0011802c5250a0b00f50740003155400948044c3c1d514800b140d20104025560b41c1000e004846194040400400c014a010f80540a808406650b27030340c18460554002415070304111001041e03a51103007400340d100389003030185502c0c0c0d10b000d0034070f02c56060442d00c600c0701d803110014441e1101551342000f5100c52405009131250002102c601c61803032516401c1c020050036481c005924a00e00c580301d00742402c46076004030a04024a55694081001c0144011010340b82484054080c5643c54074801d031003a10041220644070b00901000c1007900b00070081e0350840c01158418280303c0f00c01e02c10310600074240390805412180c213124468032a1030354100303443c1c000076403500d041c0d2142e080000d0703400b000498060400580e0151120101c41109800c680c0d0a0380d18208110754401e40d2030314101440d00d082da0245130400c10740c4d1900b00b5a0050708010170b2400310f500351610741c01c1d4404 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 724631681 1250 724630431 724630483
    0x80d020309102c010603050a0f1101090b090d150614032401051e0301060314190302060c07030519051e070b13210e010207050301050105030d0c0c08 65
    0x401028078200342040040081e90030070b0800c500702c2600e0f48401c0100b42002c0c2c10441c140c3c4001d40002d4091a008000d8031000f04240c0b4001e00054800d1400b12040c04011201c42042c2d0700078020304040315400010309180041081c00c01c80700101044041759011000b011000d80031a0b01d1143e9030280900401101100c884201058604600030002008400106440040e26411984801e0468601f9507140061540e442e0000d02032000c1260300680661801000005000720317628458100c408510039610802000042034429015040000c1e000d03030b00500c082042e0540b2503004241310350192800b1410809a02807074100f4200340a0400c001450204e680b08051130805181e0034001505001c007850031904d07698103045a04000c1c01c0d0b420b950401c144500c10300000500154031038201d070640455150301c050000d040c1e842e0704215580144256880410242414440c440c10390310010020039100019034012501ca40c00c0e24411219000888400212250b0400840c05c2818501c41511402c100c0 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 724632931 1250 724631681 724631683
    0x303010e071b1119140405090709020a03050f06030a03020a14120d0e07120c0302090c09040e011a01260c04050a03060504060b060703080a0f06050d2303090306010918080d020309 78
    0x107084c291103600c10501c800c018000e12100c0e007074140c581c01e40c0d0228860b0350700e0554500b40391956100740b80c03e43c000280040482c0d413690001c1c1c0700701e4102d2000c022945031181072564409035500018003580c00400c034180824000c00c0c002d00500c900e00c0445060700b9022900b00b1141c1c0000207841c20603070301c404459002c000188041c602030210842c4880140325181c444d00140901444080d0040c00c001c40800d206816010441d1300e145006002400340d004001c6025000305107034101c211301d80e40003104000456200d0384d15000b00041381c1c42c00e601039012803800a491700d0703000380c84c00b40d015000f0400019652604d00c047e10065010341c100180c0c61400381003a10543e07101d18034691203050300300b0072032000a4201c80c0551b004282c071040019800c59414040005088542041d680a00f88a8071170b401c0082c0b044880c0745040c00d09050303d40c41112068200c0e5240903002d02c0c542c4c1070700070701c006200c180002c1c0e000e8240d42c09030001c00c034040035140c1c40e0320420341d002d821003001c4140c00104000780c1c058 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 724634181 1250 724632931 724632949
    0xf030b0a0903020d030507030603021e0f15090f030c12150106030b0a030f031116061b0b0c1303150603120807051c1b021c110303010e071b11 62
    0xd11000305000c2100550341c002c1d19119401301c00028566100302040c40d00d07100c1c4d030098010f10b501500004101414841203a14001c2e403c8020384214404107981c40036090038652991661005440c542c14070b22404100440c02903c185000d40511890070080340c0703a81d0b0003103161188501d6034045c1008403188103510034585016002a818141801c4036010f45450f03403402c0504032a0850410b0813000b40c140780c2107502104201c81d80c203941c072404030401d442e080a5038542c0110703041c0c4d458810000306103074902400c24880358405040c10f000340300016400350234100106422030701c401c0b40c2280e45031261358851071032502c42604480c0740d0380c5400900401030382070008804010302d801e081c0c00c41d203401704004105200300003500c2035040c001600c04004480c142c0040600704404408012101d010f48002903407600011000c4414a0705c12100b114983d010346a01c9001ca8501e402446c035503820401d83d0382d4040307000380488023000303104085c5804008140414110051049007012660100c407010040124 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 724635431 1250 724634181 724634191
    0x7270f1119050c070e0604020c0109140c120303040221010c0815061206060f131503050c04031a040c03050604050d09360605060a09090c080f1306150f030b 68
    0x100070400c43d00450030020f002c070200c2e21610050240340d5501c001180103405166030208641d0700317101c080f40400003084603840c0d00c24000021213801420304400c000240340c280c40f11900503002007011501509000100c407020308a0003040100036403d84400500b140c1144c0002000140e80c0d209000900b00b540e40c1550040104485041c02c040c52485207a001c9040034110310710640002480c440054114070650b0481607008030000d446560351403200009074007404c20b030030000c1d24040001c0c0b400d85030343c1d0aa4064a0b008402082d5076803a180ba501200600940f058840c041c0c262000070008004004983c0305502c14400340c00020315404001e841d81e8480e81109000071254090101461622a0010103110242c080580d8490114144a0041a2582085801c9000000d0b05001142c1040c0700404848101c6010414510307440801c452200b81654600d0f12403003010702180000301441c1c00200110700031280081c8091003500c01e43e40b54140c9a000140e841c60030b94040040c40f440c21807860380a = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 724636681 1250 724635431 724635437
    0x703110108150d0c18020408121e070215030901020c0c09091506040f06060f020c0a060f050d0b060d0905160609030b1f1211010207270f1119 62
    0x80c00c200c0b0400c182c5241c0b0114940c050400100400c050021030381d05640280400320440544082a580840181d809800b4940540c89504a403d481000180031200a801d5103800034001c0100c15425040d035a01c004c1c002d81c0c0c401c040c0c01c020520b0442150045020310840c10005a40382ea11107685410700c15860314092145925000304806c000d00841c114041c181040c40d80222030741c426000400400008090b040301519010010035081d4100000810791403070343e000c66128081110400c03400f8400c500680000450014441c000c01c2d0041001c0e00b50228865004603605030000080740032a0000d00340c008821740c07100d0007241445001d00c0909420f808410761103141c0313400c1420140c034200540c4002803000d0f96440000d041342d1103ca5100031822070100645c09901c0e9524042401920404815140d4021031000301d0055070001500d48120303448000301800650080ca10503050075100c1c688a0f41554403041905d0b6043c40b54425100076407441d010b06503c5502c3d081c84d03034100480b454601c0c818 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 724637931 1250 724636681 724636697
    0xf19020c04060f050d030309050d0e03070b0a0f0f0c050109051f06030503090d02030703211103090904020420220b0c030f0a140705010e010507090b0403060506030a02060c07031101 79
    0x103012542c110b0340050b1002a51100311003956440c0c01c400a15034144090030b980640030b003150002f80c0c0b29640c200301d1b5000310129883c1c640c071007110040034811900304402146034130a1003800c0601a42090184a03518100184c1000030394881030300b5120440c070200d034150080c0b00d6070040324118440c1030840880003c400c10005040d0359501c1d66074450028060721565490002d202190750402034100515402107030700c0304012000d030007645444103602c1d09038041410869040f0400e03074004142e030a420030081180b5000d8a958091200400c0107070481c030025116080740901009545006118584149114200c08400c4090b00d4011602541003144500c2041003000001c80c000004c1e20601009200d41942d601c0d084e100a8a142160b0310103000c99010101d00720b402d0050640c4100b00380141b410080c4160b0f42c40b001c003103528030080c2c09000c01d14042400140089006913100ca98080c2e006000ca80b07460308280c001540e2500302c050b00c1c2c0c1040d0f000c09410b0042080303010705104407e100782810301d8 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 724639181 1250 724637931 724637939
    0x40e0c0102062e0303030204080105060d031e14040b03010305150402090c2a010e06060a060c0f0503040801063b0f07030b060a0c02040e0304030206040b030c0f19020c0406 75
    0x2403100e802030400180c0b483e81c03c0d40c600780398032070030318440034041402440d010301a500e24018000c0d400c9480b42d42e1481d40303020b00049003800c02184044913164503030364400490b10844c4a10f040002086041404c1103610a43d80c0704000103c00203201406280018a88075807461401500e000201140712194100070390502005880301607115800c2180f00d40c036180c8502c56641c01c480071001d03641d8000c1e03c10780f01d185464541e04041d0b200e4840400c03000b060751025a40c480500c5101c11152064400142c60004c0400c0418200302003446107600c81d41c150303440c143c0e44581003400e60b1250340040c0440d21410f00c2104651040d201c03242c3e40d201200c0944a06004024402d040c2180010441031442550030000750600344240d000c20710502c0001c00c980e80f00c00c0300c40c0c8001d00c030350840e1004074012803410301ca1400201001043d60104c039402070070240b500e400d0048824050300050a0030320808000e010b45010901e414015183d920700c0c01c6468009031145a40013441c2010b0702c541c440c011403510b2401c0c0 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 724640287 1106 724639181 724639183
    0x2090103060906051302030c040c11150105191203120b09010b0408010c051e0703110f031e1602100207091b03050718060315170c040e0c0102 62
    0x3080c0d46081c5585444401c085000c7d40c180d011002038101454140c000c6000081e0b20f284c180b80c0700440c407140600c0c2801d0042c0301c500c803400b14070050141d400d00c0103d2101c3c1035494052250118074004080740e10225101d409400c01c10641c0b00320014560503041405c1c0381c80060a410655030351194a2140794000b401001a40c2d402c006140035214810750076104000590881054104501210b412466102c3c0c0001c500740200d5804440140c0300a000001030740c1e5401c80038617600c2480703c07035080303080c41d03c44180c03c3d01042c1402348164070014103102d41030700369042d6180240584c69240503440c00300759a200c0c0100f00c0c20b042542c1c0d00454807400d40340c0c0c691420307107041c00140c9a03c00c0c1603a00469144090340043c3e00761504115041c07183e00b085a29007800c050102066403621030070540d0700c1c007440300c44820b40d020001d2000941003612481c81801020340c060082912003000007 = true := by decide +kernel

theorem cover : BRFrame.Cov 724460431 724640287 := by
  have h0 := BRFrame.cov_init 724460431
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724460431 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724460431 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724460431 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724460431 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724460431 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724460431 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724460431 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724460431 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724460431 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724460431 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724460431 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724460431 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724460431 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724460431 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724460431 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724460431 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724460431 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724460431 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724460431 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724460431 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724460431 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724460431 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724460431 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724460431 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724460431 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724460431 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724460431 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724460431 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724460431 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724460431 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724460431 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724460431 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724460431 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724460431 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724460431 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724460431 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724460431 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724460431 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724460431 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724460431 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724460431 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724460431 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724460431 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724460431 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724460431 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724460431 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724460431 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724460431 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724460431 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724460431 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724460431 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724460431 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724460431 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724460431 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724460431 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724460431 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724460431 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724460431 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724460431 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724460431 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724460431 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724460431 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724460431 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724460431 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724460431 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724460431 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724460431 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724460431 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724460431 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724460431 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724460431 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724460431 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724460431 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724460431 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724460431 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724460431 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724460431 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724460431 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724460431 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724460431 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724460431 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724460431 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724460431 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724460431 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724460431 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724460431 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724460431 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724460431 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724460431 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724460431 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724460431 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724460431 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724460431 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724460431 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724460431 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724460431 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724460431 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724460431 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724460431 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724460431 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724460431 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724460431 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724460431 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724460431 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724460431 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724460431 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724460431 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724460431 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724460431 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724460431 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724460431 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724460431 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724460431 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724460431 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724460431 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724460431 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724460431 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724460431 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724460431 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724460431 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724460431 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724460431 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724460431 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724460431 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724460431 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724460431 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724460431 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724460431 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724460431 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724460431 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724460431 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724460431 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724460431 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724460431 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724460431 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724460431 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724460431 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724460431 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724460431 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724460431 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724460431 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724460431 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724460431 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724460431 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 724460431 ≤ n) (h2 : n < 724640287) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
