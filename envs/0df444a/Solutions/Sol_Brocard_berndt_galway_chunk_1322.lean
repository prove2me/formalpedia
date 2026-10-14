-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1322
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T02:22:04.518658+00:00
-- url     : https://prove2.me/submissions/99c2df15-ccca-44ba-a17a-0894605c667d

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 237589928 ≤ n < 237769784 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 237591178 1250 237589928 237589939
    0x406200901030b0a261b0607060c11070f0512070302030a080d230402040b0f010e0105070c03050601080d021005060901030809041404050102030915010f03081b01290915 74
    0x1082e254891314401c20040403c040c080585035106000c03d50b010451259000f00c074062aa4201d440c908030f40107880007848003900c450b00e0308801c1d442d0f41008090000c082170401411000e0070086441c2080138101820440180c80c01103880e2504101003403408400840303007508100001c00240e60702042030700348140c000c00b0550b07036009000042c800800b804200042d811128040e07010a600c50210014031452007075804000c41c454803020008000d0325002c0a500080050388030105c1ea5104801501d009032103074504070680c1da01d0766146030504a09030092500303503018145074212550304110030400c030016120104140c3c200030000c503603225014000a000f4480c0065000005d0f15958072900e50076419080b0b40b4294141490304a010b50300540b0002c407a8890081d0389802d043d16602c0e41812542034a1a011140e81b541d80d900c82e0980054540c901c82002d0590004225070003070180d1050003c421044083c078085820841025034038050245024042c44410400100c49202075901341c003034100e50 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 237592428 1250 237591178 237591191
    0x40507150215160912120906081603020a0e0301021207021203090705010c15050906011a0408100504030201021303030f031506120b0a0f0902070209010b07030c110a030209040b040620090103 83
    0xc15503903135030b0130303401001d15a28119a4100380001c4206499601e2851342d1000700207070f9500421901c2100c05e549000e9445100552000c403503000c7d500400c01050141011403d0082d0030b80003c0c00c90f0026004c44030800c00d80001c1059840d414041005c1c464210f10700c40d411410160a455511142c034000d076414805110b0101003801880b807554200020665030501103813800410858460800303208100d40b10403c41d02c14084801c803402600c003611411001406c40d0040d441100d0043e203006041034056550030050a2aa07200302038100700518085c0e20f601081601e4020000c08441c10481c030b0030020106218188222a4045e100a60a001a00000c5041c0d060704002403410b5240d640580d020b00a40d00002520135550b070007800c0d0f8507008030b454201d1030303991b1114000740b4030490800500103070308260904001041c00010b0100701c0e0001d40fa0a003015125400310b050b600003940c1c1520800c05110412042080500501c0c020003480c5101e01d00c1c040050700040740a00812502038140350f214403 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 237593678 1250 237592428 237592471
    0x20c1e0a090f2d15050a0303110d0201021c0f0207060203010f140a030b04030c0501060e0129070f0f0804030203150f16020d030f0b0303030a0903081509060607020f09040507150215 79
    0x1c403003400b0b0000241b1038402255a80b4014082c400003030a02841800341600c40c507412070040c03082d2203404001c150b84031541c5051000c030342c008002c4290496102982400300c0e0020030418409580600850003050b07089506207100d03d402e0080c1c0d40800d602c41d00010700c00380300245c841c000301d030340007503144c18484841a6107180c5180034000c103400c4907103450b8940c0000034656091078805804041900c010540c84a6000b0159040e031242c9000078203084001100840050042c2c090b0100b003901901449090035200e5000905140f040f6000c04107090102d420b02c6034030026184d00d550021101840c0c81d00020001c54007035281d0842194001c24503a468402d0744820741c55401c4400048801800ea0f45e4920f00110b0007002040c0c0c9a00950000c1e00d940d00080b45080d4146082c0104680104541140e589910400509074400e4100f2a00b040641e6104601900c0b017540047c0603a00c2070020300000d504009085800e90341103441502154008103c001802204041e440d810005a2a0704c0d414900d400 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 237594928 1250 237593678 237593711
    0x90402160b1510090305030313020a0b040305010903090902090f04020c0a0618030809120f1818162a02030703080a02070f060f020c1e0a090f2d 63
    0x4160240019401d4000c00400464004426210081c111060900e11980c820119100426404010a598802c10210f0f040200074480540359510042c4444d58281c4c49610005607a00103a200311103c1c0c0d1644a000101070308200c004010340004082182800420000512041e20840005000303680c001803054542c001400901d402c182c00c404280400c0545440321114a000d4540943c0002c0c1c0b05c4001c150312900c0803c0e01604170108001850600c2c0c811407805003c4e42c49005007403c944040000406261921000e5170001140f80210ba602031411268488100c00c290200408101608100c0300034a502030050003100c8502440b0010010000d00c0420314000b111f40000c0c190031000324042c0d0201d40d000601e141504c1100710110611541d0b01000d40d003d41c0c10484010260700035072130380c105506200c42d00c000c0490312010400b00c0440c001c004294200c40940189850343d0f1100200e07606c2d071559004038042c0c0301c009d140c44081da41c10401c46c800c5143c030302240b00f441252074aa000300f0b080ba44 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 237596178 1250 237594928 237594967
    0x1b071a030a0b0f2d0405010f0b28080603010c0e0607080d23160804020d1212060b0403020a2c0712050c03150a261606030204050901120503090402 64
    0x10304000140d041226031407520715020000002c030780041c0139100380c250030301c1c1c056076049901401c1c0d0340d445e4904224050303480390018442c0400c505821100040810170010281c0c10300c010704c2d150f05040d400c4c01014182912022031041040c882001e4030341074107440300e804803400d203600b01451a8a80c2c0c0034010001c081d04240c070002548440805200801004110005008003038010081c860080c0030760050f00c1540d8200c4e0040d50107102000c08201013101e448880c50700e101689484016818110481c100b100c0240c0c110440c031007c0800e0500c11030604c042c8900c06404031040b244030401c29060005404548807103020405403081d008100184c4c054a095221080d2803071081c0890b02d4121007a02a51300100d40038448040e4034001a05103040c00e540c040166031440300c1d10f0192140d8001901801d04c0c01810502442c0b284a0903003403411002007c080c0a814107960151b900e910308810031842c4907068208441c0303410b411904100049001044950452041c0d03409622074203408400342c0c04041 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 237597428 1250 237596178 237596209
    0x308031f1802300402040207111503070908010203012103050d0207030c0204110c0a120e0901080a11060309070302040903030f050915090d050d09050307081b071a030a0b 74
    0x21003036003218031540700e40107005456100549041000003000388200041200c00c80c010ba02405040450003505140d001800041e000d1054203241110020200d441d05401c0402142245004818407039140c0e4000700c1d84009214080083d0b00319414140c0503103650404500b4113104000c0e480c440b208050054082e0350003200d140c1421504d0340c402d030801500c1291148000c9101c3c038900003031701108402d00c00a841480e05444001e0048014540d100010100404580350070300030810901c0c0115910540b015029241842c003501101c8140c0c41e2075501004d0680e02c0601c100d20a104000070b1000010303000c1c040b039404950108103024941030030340090040c150452038160600c020403c0208001a1400c6440d0034100107815658801600c9600c600c8030184080003e40300300208009540b003a088010018010300c1580d160203503da480f502903070b00c011040001071501003002c5c0051f00d01404420300402c243c42e1845481d824905000e4500e04c401403528140596914840d0764548070020001200c04 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 237598678 1250 237597428 237597449
    0x4050f0d020a1a0706110c0d08090f0a050114070305011a07080405040e0d090801060521030f0307020d11060c0a110f01020406030204090b040603020a061b020a0e0106080f010308031f 80
    0x2624a2003d14056014110035541e9a0824415240620740e80c0300702c4060702c8005000d400c0d030a461100c112810306015010224912070000400101e00c8140424503a4070310400000030780c98180c800384415410001c0800c0c3c05d151505004000040c0c50b4110265170f03290300311300c513580c420180c50b240b01c40b40119000b15401500d460200004254000b4011600d0106515410642c03070760f03004003600761703032580c0070302c0740c000c0c91003542c00c8045d0341030b485501001e0340003209a03420040c0190500100360812121700006900003020b4444268002c0300d04800441e08078050b000610b0101c802e09424480c42d5406000c2100c58a07a59507200001d000003029044400001d40d07540d41c1d03a9100170041e4015024507200b561801681c400c580c41d0604c01d0b0422a540981982c02041c0350810907500f0752908102e081004002902520040e03540e41000c0c4081d201c20f0080d2603295040540040121200a02c1311142e907000c10014400705d0300e84400d8070303400400003141c50103084000940c0500c050581c0e02201d03611 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 237599928 1250 237598678 237598709
    0xc0207180218090c04180e01090b01091a0303190c0215120f0601020a0f02010c0c091b020316080a0c06090b0f0a0207031d0a051314070512070f0309050303070c150204050f0d020a 78
    0xc03800132b941d040720202e80c4140700704402d0118000c80c43c480d510001d03a1546c0104038000c00e1000100c0c4038450102241460f140809640c0c000c030b00d4a15903210120802d0700c0028501d401e40c80805807560704103080d0940801c09103440300c0042e41da000161000f801004440c00300d001103a109814640300c03151b00c00b804074883c50307441c0c40c0315010704240c0c0740920342502c0d80e4150b0944503100000b034560404020140a440c0050303034840b04a682c0c042d40100e82080307010004140400d10307034004d007000070741701c0d511648280c60602481c1c08048005008856803d004000d458042580700c0d000c0803503480803a5020341c0003055000040c862100552105410680700c06502c1986450b0394801045807841130720b0005d0a03a1038442c129114410740c2074800b0604032440c0824040303031256201883d004003a0800040c1d0320455165189940c10481e07201c80000c221090b41000c000781e501071030715400c0c81100d081d03040c0b504002c00510020420841d090281c404c140b03000381955222502c0304000d00105802d801071 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 237601178 1250 237599928 237599933
    0x70813140105090106170c0d030e060403031101050c04050f0f120d02010506032401170703021c12080c1b0102070803040506040c081f0c0207180218090c04180e0109 72
    0x79110454000d1480d5180a00004c1c161001c415141001b03a181c0001c2d102d10b500b01c3d801c0110342000400e0a800308142c400d0382c10f0aa840b541d0041003c1d60103a2a4100000a0117004a0030748900400e400c400d002d05220801c043d450749044a1102d85007160441600303802800800c5e0000980040300c0114466410701885258040d403255024150640c265107642c2d011071000d0010203c4542d1041c16904484010032004032000c0018814102200030385841581e00e40000314030300d44113000180080070f02d02d0140700b00980316000c8049038186042c00030181c5050b42c140300311405004144c8640d243e4541c01c00440120a604540c02c50760300c07103002750f03c0b41001e04045940f0b1a01700c41c2140c00e5607a9560201e81841b00048414070b40c0c54000807100b400d50b020710fa000143c02c410a02400303612820720007146001d0280d0081c2d0603060110001030f01c074600d0354a28ac1e01a486425480e009003411400d201d01d00130520b048a040e900034840c1c006102c080d1403401c3c4000c051a1088840d01e51a26110004 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 237602428 1250 237601178 237601181
    0xb132102090717060607020d0803092103090f01050403090611031215090c091e060702090906220b060105030714030103050a1101171902040b030c1914030708131401 72
    0x2442c404040050f0741c40d624503040c80158495403034081c1d0f011441c0308850300002e1140b0000d41e0300c1100b502c20744d11190b40c07400f81080c01c4084c0040c400c0000708003100f00404220108019500d8a48220082c03002c0e0900d41c6001c0c00c10112401002d08100e02c034121403085507c00c20031200d21001d03010204245103041083c50038000c10428446d48107416000204d8149964041501c03401e01000301180b00900134400c160341104108000e141d00040305008483c00740ea81c1040e01032040b0301c030401400080c60501240410058000700c00d20310034942c40c030950007043c1950f010300d6010800b802c1c815500e03142c09405541c00060581c04410b69440003002000701300c00445c0841003144510710791240c0d01c40310703001916002060241d0516402403000098002d41000d03401450000d21424018500750300d512081141e58030407176800c0301c501e6000840303803101c0f080c00124441c4103030245400c62807850b491180c100d00307120117400842045441c002140c040c1200707040000105502194000c511400c0c801c03901d0 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 237603678 1250 237602428 237602447
    0x1508030c01050601050a09091e02030a0e01060f0e040b1f12051b030a0f03030e03070f020f0102210702040605040c081009020901090902030a060e090a0605010b1321020907 75
    0x8090750914000c0754595014000b51400c42400d621600d590f20b040201c80c02c010900c03c09074280071200344120348104980d5200440c040c8140c1e91000c80c07002e40d0002d00b44e0a4482c0c0317031b014500308140c15030100010620410380c2908244d100c0080d0410343ca400b03100c20038420711001c02000b800e032010b4001543e21580b507240a031181c8078000340e400c0740090038040e44090856112541d016000400038800152550401c0345281d44213040008100c880b1002079450350300000400c60b4400004448001946010441c1030f1040600344020060b607909040842c0c541000b841c0c241000c988007203001e104542d40c50300b158025140c0900104104000c80400800ba03083c1603c4490003003a4503007004c5a020483d00843e060400180c66003541e8500d0552800002d40c402410b00800682c5d409010401007800005a409018003200500b20321000342000012580c0603400392242400030040c5c031140350541e00c0860121480041c04e03030b000c40c00c0c14500441c0c0c04031003200290321506480422680c0c0381c01803403c1 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 237604928 1250 237603678 237603697
    0x518043801030506010512071206090e01051b040611070306020a05191701150c061401080f070e0c0703112506090509040f14031206010e0f150c01150803 67
    0x9109000300301005404a030b0044d5401c5002510030002d041c1103581c9030070783e9600180306181581c070028403480103504031420350700b01c1094aa00c41e001e0301c05400003401202d2f0880d1041c45890380c905100741070382d11203101c1c2d40300701c1c401d00403200d241021220b02800043c0085420030000d555030800000010a46ea21102a01850710070021000500c1813090202e070300c0c502040142e02d042a4202440d4000400840000500700001841e20f440003031814040c00141891380c0320801000e5050881041c1001141810420f2a80c03000808010001031410600d0b08800c002c203041c0e90701d9049080403280c1414806508450380302c3d000101074640ac04080c5000041c0440742c10302c14440d103a034011a5010540d02c070300e03a1710031404004540420365203520112441c0c40380701d10349014404401140d0441e0046170850495003a81d204021855070003001d40010b240c002c07140c0c006c0d04d01001000440c0014800780998850030301003075044041c1c0096104101128515507004d201d541e480d400c03555aa40103090b00c = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 237606178 1250 237604928 237605021
    0x70212130e15030a0311030c0a08040302010201140f15150a090e07020307081e0909090c091e190f060f03050706030b060a030e120703030203040c050102060106051804 73
    0x180b804801090409458070010040c00507141d45803401c80e00c4843c042c80d128814001045407504000042000c015031511a03040356880d9840c41c000a0b086441612002012841d410204501c112510720704592280b0701c592690300101c00d401c00328000c12030360500924118400500564203503002803103042151610103a000702e650319804101d80328054100d00402d00441842a0f00303214491031034a0b046515440081e43c1003000940c0010240e450030380e00c11426401c0320340340d1300250501d085150b40c450300baa400340a0b02070034043c80030b5240000030841c001540b0a009001d489415540011310702060414003032150503280c0075080701c40030b614441283d6601c0340040000d0410f02030f009000324074100400740c604015100c40b05401400760344940030382e50301403405a50002c4000d0000b03410b0345402680d005803680340c24944204000d1564108505540c0030b08010003103258094120380a0a0068110a009840d0070700070401603c0e80350516130b007208801c6000701d85466002e4a070340c0844161000c = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 237607428 1250 237606178 237606181
    0x3020a05090a03110901211106070c0b0c010e0a20120d030204090b12070312030f0f0902010f020708030a050c0102091804031d0a060f02161410031104030b070212130e 73
    0x801c5a0303101e101034012a20003c107e0b021000c150b5041500f404000050651890700030150354008401c0083c1c1c118881444011684410718182485884000e0aaa00017003d598405454000d6489504400c01804501058100e0055298058001d03005200f0b80304540404032a01c8014010350018000c010886290001000682c5800351009940c0c130102c0001d000103a095480310042952801500000e242d240c040c003d800f58040c2c0701e20411480500307800580c44805200040030318a80e0381c003010455120100030b200350300010046851a50a60400179620070f0b07031000e4240a8082c4126103540409030210050080c540e000fa028856482a82c0341c581c0c54107900a18041ea141c1d141c0c03050703003100e10410103100d400d01420b0b078840f0000b50390040721200941342e0548902e0280c10341042040c21360001c15501c0c941004651121803000600701840380c10064401070400340581d100282007484000003042c4642d0003805074401445522021640d14000e403103503045000200e10030002d05100080 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 237608678 1250 237607428 237607439
    0x8060f0d0206250503040801061401080906060f0310020309010605040e0601080a02010e011106040f02030105010902090114070309120311070501030504111002070b0705060108100b030d03020a05090a03110901 91
    0xc0e040c040c15038000c00103410801e40080c20240d0038034590604280e240d42c00c1100000c240c041003c0c00080034034100200d40e003414168040c8560503449411814080c1032414804107040c0800d08690011084c0c4603041e8030801400000d03c1d00c09c140981641851000040c0b2200d03140641100f03050f52015075040c05400c440d405d08556840003442070306081e820410101005621600e4096400170051605a6610a803068400d003003040039a81100e50585a5001c041141028003074a401010619011410b080c9800006003410001c0411030811f404002517034800c26001d0200c0c0406000c00c580b414812400d00d14003d17015000c04000c6482503c10003100092a40c428003a030741c03090b030b8050310701418400389500303125030302130503003807401c00c0d40551900031600003070b100c000e007151078000c500800241d450003000134140540306607542c08040c1080a00409034400145020780413400d8074005035140041c0104680d5070060009040c2c1c0701113074080000510042c08030980c0d103910201c48551030360b40da81c0f = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 237609928 1250 237608678 237608689
    0x8060907050105041401030b041b080c030601020c011b0c0605030415150618051002030702040b0409170c0c10030603060b0a060801050f0d1203150605070f0b1f0608060f 74
    0x511400b0300080080005008503443c20040307907261001810007141100601d000542540c0680e296640086e501031880c4640d1350340000e00039082003c00f00c51503d141003000000703480301c0c030103101c80341400010068044059116a07110304496000411000c0c001d41307542c0b00030095401a14203a90000001c2071900000800e40b0408008051b01c144042255141501c25281844d050700380b8070800c01e00300c0c4005001e4484080058034040c99602447c4d880c5014410441200d802c620340e103024524090028002a1428502c0c0c09100b0705400d80c15100c032000d80751641380003d003044071038220340c00d2180c8111182c0c15800c1042564800c41d010300103c0c80c03d0f014018014468400c51380000d1101c4010401c0c0e003804004800e0355000500040784001068960300300b0070001355000300c00647c1e240c03040c204503034600910501618003840c01a180541503110918050042100a01488603000100310003442201c102070301c400d0604030010001d956008007506100301140c3d070310b0003a03e40c0ba10f08221880d00 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 237611178 1250 237609928 237609943
    0xd0c0206090f010507050307030b12010608010605011106040b0705130f08060a140f0114010e0306040807050705220b01030b03060a150f12110612010e011508090618030d1104080609 79
    0x4642e1b440b804e40e5104c05084024003000b00016800c59625500044e013204280280d070003520000c0000304055190200041980c0c00c59800002150040c2d414400022744c2001c130640c000e081464041e07140c000381644100340e072a00d03501c0105e0040342c0c0340c6d0010703101034049030062040c5c8048100f00030040110f44140b81c2920216810080750f405017005000e40410110024400d070410b240400b0703609506408280f07800030030f5600351105c002c046041420000c00b0000e40010b09000da0303104141d15202107604a1945015120b868000c0e207034205403805912031390244d400c5a50040444102c1e00780030300c10000901100c4c07c05030700b141d401c03880455081e00507000d00341214103d02e188402c402d0306485031075100d640c102000750301800c1044401810042c82601e44e010f00190318002c1d5042d450519801c3c0742642214119042c06000c0c0204a22140d0225003268090000881c207864071342d842a14504503c41e98103404601c03880d02d02c2c8a400da4100502510030b44945404840041e02c803032107400d680ba00b0 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 237612428 1250 237611178 237611191
    0x80d060b0a08010303020c12150901110c0115050a05010c0b04060b040c12050109051504020706020c01020f13140901050d060f02180103060b04030c0b1303020d140c040e030d0e030d0c0206090f0105 86
    0xc10360a440390509e2021607600400a0000155960a070500d5510540c0085401442a919041701c13203111243c01407404014901201d2120001d03142c00f00180c03680742003503400350410311008000cd090106130b401045c0510002401082a21191040a080000a200780001c61442c2030700100d140e2060f407051900640c00d100c11111203a084400f044081d50000701c3c100c5186409101c100c8400101340080c1005441d800f02aa460703e14072200b049042d9940c4d44440340ba40350392a81c6078030544520045906460003640c00d40c20035070660a000f000b44c08d200c0020046103100180e070b2980c900e10300d5034407000700c14240e9050011503640e0a49881380d0165004c060f1071003885060801503545480010014029040c03c0c9002c01e940d0303500001e07401c0700940b100340c07415412490303c7c0f001c20405111100b400070048600300a41d00c10610b45503030341d019103801d90003016998a0305d85040981081507407400d61610600748070303c004454000b9164a02903030302e00ba241c8150501c2c0030042c9418010725100d00c5 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 237613678 1250 237612428 237612433
    0x31209110411040503070b070209070e0d080a11060106110f06040203100c020a0804060f0e1e060a020a0c0810051b09011407140606012a080d060b0a08010303020c12 72
    0x14032010800000700001481100c0c002d03020400041c40d900c0c240f02c483c0042245200f06502e90401c2d0052005200c3d0080c80d0740e080003c0580349005641d9007600c04517a00350440d41054079010703c10002e90360b612103180d01155a2158000008500380d0110761081e690101c4029110f00042030f603042076440304180d030000c1d85034010030444004030307542c3e038004160f103041c510445503050000e4a03203e0f21903026803c003a0000d00c6100c90014125004030118004201c1a60015110005c61045c00b011000c0d040d10345214100001d5001101c03031081144840e280e030030981d101c1500703a0380c00c82a80e0f00c0c8003074180c01840f9418080001c2d080e8002400e40951404034424240c0f07013083ca0380045500110780c0350600c00c1c0280620401c0d0204068420f69044503201c3c100410f00c6082260002d0130b4020044c0c450b940c0000040c2100e9412104044212081c40d031001040e9143c0d49210381c18009085242c10222401d00007003401c1d10035075444a1540c2c101c034040e03000c1d1040000e2070300522a40e151308032031040785039 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 237614928 1250 237613678 237613703
    0x90f16030f1503021017060d0606030c0b03040b100509040b0a020423040b0114030a09030309140d1103091e04020d0e071d01051819020a0207050a0503030c0d0f05070503040909031209 80
    0x103042041c000c2c802341e441040d00041e4503850303588465801c407081d040b0188500c00030081100700088441510b030000a50328114610500c0d000001e0703259440240001c00300c581e50f60124047d0402c6405039009006904404540340c480100010030900008a50a1142d4207090700d10303609501892140007407501001d0500d1641e6030780d1011502034004010110100b41e40c44505101060942c00c0540e00988c0c124045c02100030b4443d0001c0032845110b007082060b41080011010994507100c2d50b403440000704000c2d500001039940098024062500c161056504040b40c400071608046424005d0340c0b040310284064040340c0b084880403c800340500354000345030400104042818800c1d6642c0000c0c18210281103c03d20103d22040c1e8100010400c096402010188194904118103201400d000e400a50501030890041513440b40c800800100b40050760010f8a041c1e841074084070103080c3c01400316950b5a9486101000414404c00d045c0e0004a203040e801c80650814040c440e00241c2111003d10300 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 237616178 1250 237614928 237614941
    0xa180b03010b07051c03020705060a0b09070f02070e180d0206010515070503090d0b01090f020c060109151508060406060e0307270908070201020c090f16030f1503021017 74
    0x269805440d041d43e1314450201805004030075441450159005039902503190f010274038003070340b50100240c082d00c0340781d04002140b00142c8a1210030f070743c424100d26009200da200140240e0034002c803900b102da40c00812000704840c1d0701c040f160903440078180d1011200c403060107074004c90711a0428010140d200d000070b084409011811b001800d401402101502d03d00300c15500001ca0b04c1405410880344805203100400c0a601c0500c508601070f0300510341545000c0f20803a015440344014000d94508660340c58584152803280d4880002500143d81e114103402101c0c1000f4102403012244075110b68108107021034484d02c11440ca100300074000d0000c094080c107002411150840c0700c0458021100b2164002400140301d00603012117500622840c2d6460089000082c28400d49100307540c081c1c1078140600c010341507602c003175580c00b1640408440d4410800b503000c8020380440c0b0500c030501d901b0324584491411049a1900c2100d208881e030312116000c04100750f5202240a002d0221150500e00141d11b = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 237617428 1250 237616178 237616199
    0x801080d0804061d0106061e080a0e031c020403060b010c0f0312020c030f030105040606050418050604090f03020114060301051b030619030803041403180d02011808030a180b0301 78
    0x204188115004601c440105200710164204c00d40820490b0b03441b03000401080750840444880850f00f0000101000d4940b0006005040c0147c8200062980c91040c04100340702401a0360300104101c0c1450a00303d1007c0c62480a034110340010780d40c6c90b01e4489071008075800b0700044260f0b1a8082d003056000925a141900d07050f00740740700c1700e0301c3c0c54003000b14030030300041440181404c0051100098407541003606200440c2c007150860700612008220602c031061080c2c480200c1c13050089404110b07641c1c0d000c00300b4003408034082c000f04243c140e4150030f002c058040d08003038000c907030601031051a81d460780105820b0b0380c400c1c0c0b1036100780700100c1900b03138002421000840d4803903000303000c120f20142c0d01003642ca85c80801e9030040e20490800300c144810892030480416040401100550400800707e1080c40d056501c15009031041000a91303074003c41e40152041420680c1e8240d000484503600d00350300742c5951010342401300141c3d0420100201100e008800000d9401002c0010704580c2044207070f11 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 237618678 1250 237617428 237617431
    0x30c060b011116061107030305040b0a03020405090f0a0c021b010e0d201e1309020d0c090f0e0a2d06020a0f0908031206060d0b0307150206070801080d08 67
    0x181000b4072400380e0001103904001000c03500c1903895010034054607000000305940a05803000d0300075007104d6020001310358400142c60580703144001860381d5170682201500207200b2544000d03008904c82040110200d0680c131191312a42c81c50000740040750180c41c0c22a11140c40000392010307241d958009200652007036a00843c43c01c0d0103040d0040b51031194a41c0c50241c1140c0300e59910040301c01e000e40c521400c140340300300c401c00844510302d002c001d004000580f442d24405020616036030b8402d0f40c9000c0d0741e20101240302154100b2a031884840c0c0f202149005007511000e4001c801c2c1c00d1100b42c940c0206e0014070042c000b90008000d07029000710701ca920117641c40114154200c6001c2c41015800300c0d203207100410f6141b015444035038a40e006c1c0c41010b050303241e4903440300c41c0d160810701000c1754a92425544907840f03441212410b0303641c100211448020841e809105400d4031501c03001042c400c6600031104003454942d001c480b4160b60300c1d202201d410800340102e850503008040034205250084140c103 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 237619928 1250 237618678 237618701
    0xa0b070c090510091b020d0203040807090b0604051206070201230a020306300c041b1119060605090f04080409020703230904050f06010c020f1f080412020703030c06 72
    0x150801940d0351040740c1505e240703548400707428414501200405804020848220305203002031828146454440c80e202c0c4018070990060684404c503100300b503542d0208441c003403c001401490070403429030344103035200c0c2c01301c40a0300558030303000d01d0004000b90110840034006d481001500140e4030710030410003a4002506031a0404162f0411640451010116a440c01c206140504141a819110920303152241500e9809545061440e499503e204a2601c8605c0e2450030042c1b00030040b07100c101d11703126444c4d041c102c50006d0495080c0401c02d0542000045401c1120840070388c0d192001700000e103105c00d40d401030240b0380c01c04c01045500340c030350040d00740a4000d040019008a0000604800000c6038045044407030001a201c41585801d1044035080500480d070340c1482d00e0400000b920164030128040c0c803175010401151125a035454882c3c400301d06090182c0f407103038058180940604815242202d204242c500c101c00b99501c0040c51108407905540d8a44603210715850f02001080d001150 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 237621178 1250 237619928 237619951
    0x90602071a13030b091f1104152705030c06090105040e10050607060506010f0c170705010e0f011d060601021005090a0506040b0601110c0612191104050a0b070c0905 72
    0x404070b501d01c18013501c01d20a20b8080c08980304070350425468440e40c11813408a1a180c4900c01540051440070707502910b9045c0340450342c3c00806801a100e0040862501c01e0b19080b6580e0202c03400395103c242d0049642c00c1e0100c5226058600401403180907802241e03001500c140802c00210401411454100c00301081c01d08125031501c0224446600c107643c2520882d4840040c800c181d6401124000e2000252070441145401036854141c0c1e0800c3e1605c140c8481404544042030040a5000e890111600d030200d070100c01e00d098946000c2c0c0000440740001c03e103152102424048040780382d82c40307458141c2c050800740f0391081060008001c041c0c01c5103510700c188408500012401c012850185024040004140c9807000c0010581145840019040e401408100d48152650003e6405080013103a000c8034650750090382507050f8103070903103c8402e00d080c03a00208a101e0140001c00c15203130700f910030038883d684414903c480761060010041616090709000c1061509560029801000f08403d = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 237622428 1250 237621178 237621217
    0x5010b04110d1d2d0a0506070807030b0f1e0301061401110304060f030203040f050a0312050105300a0b150a150c030f030204081204081011180d0b0703020a090602071a 73
    0x2c046103411285c08080b80d10394040fa003400895038024440a0b032007045490280480420700002c11662030505440034052003101100105041181440d064140c02c040d000b005070030f80d07a88a4070b07003040080c1500c03408200f00320004182a28040100c8043e9502d944504030044100c50044000354030092040c1e8614007100c1c490340c001481440344403486400781d50348142aa040010b030204070794040c3c1c803040c07280e40012800e4114410200306681810b1541900340702c003c48a11005040c240c2808008180700212010051b014000c036102100c0c0903130a44190400584440c0382c01003c504c4012502c021a500d034510800003440b84611035035a0041d4a005400d0036600d050442ca001034203202c540800001240520401c1c03820420301514114a40040c0f010039504100782c103251091764425180000728090781c0005880350803030515469400b0040d8002c0d0301d0711120040003500908680c1c4009044010002080e600c000341407026520410b60b80c1e0544140180969a01d0b07110050310390000d100d055 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 237623678 1250 237622428 237622513
    0xf12040c080303060a2102060f0306090a06081510030204060605040312020d0c08031902030c090f15091203040803030c0c061b0a230403050a02030610060504030b0405010b04110d1d 79
    0x123024010643e0074881180c2c5908154041120142c0006e01c1045201d00d05502003001c210002490f60251607043c1303801500da01c42c002140d00092441e00013a400505101d000031700d4551080062003140d000320b601507e1507581010890700c0e96441400000050a05010700d80807541d101c0046410407601000c21507200c0d4602d00c084103a0308211400c0c10100c20101b0724400ea801d1545900c40c400ca012100a01140ca4481c500d40c401c3c01103881040c010306060101601401041007102d002c2e2000c4003c8030745900c0e02804000465102400c610554083c0d0408200364201c410343c80c0d00b40c0e8440501e51418410005801c46483e203075804002040303040caa0001d041c00c1110001400910300513009842499428014185401c034003810400c070320f121800c0100b110550003415942602d0b40080302c024603407101c0c1022405404c5500101d5485031400740c1401004080030000c0c00155844502400310400c0031012000c801e9880440d0354160b0000a41080703d06a40560541c039071103070300780300d030781d105a1003 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 237624928 1250 237623678 237623689
    0x30105090601170a1203050613050a06091407140a020102040f0e040c0b0c07030201030b0f0913020f01050906180a1802030703140412030b0301020f12040c080303060a2102 75
    0x151180416a042140107000d80814049400f0742a1420740007070880705070700ea44800100c0d052101c00010503a407171000c20910307aa00042d081d00074030103850030703c10390400b500940c000703020314440c05090034585002051704084162a0b82e21035543c50302c031030740e03a44d9400c8181507139988a1140c1c541155070070480030685081410306c03107004d8446901603440b80e140c01c0c90601502145038000c031056805c1405159420000014104140c0307a080c6800321b0742444100104000c803d40d81308180d03100300100d04002c0c415549159000c1c040d03008681c81e003130b222407034801902c0c1c511030311248903000001004480a19030300907443c5c1001000180414400f944da0714803d0540e0701c07041e610002e82603000002c0c0111513506020711401440400007884450615a8503801129800d1600c031080c15203c2e41d030514969030030340c1902c3c0c406543c881049d548200d010820b401008044400301c07036044061001203a515800001e072840342030080c00c2e0307540560508202c140b081e030b2910a8103003034450011a80300144c890 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 237626178 1250 237624928 237624931
    0x5100804021014071103060a0203040f0312090c090b0a050603012108090a1203110d0503010e07020c0616020901092003040809030312040b1501021c05040f2405040e0f090309030105 79
    0x40c105c00242960203400c15040410107000c0c22203440c010300500c00440d4080c011166036030f41c1400d0451034201021142c0e0080d01c0106030103800a2580310000480b501207421140c0c0040c011600220003c1c2c8070010400301c1c0c0820300a2500c4a200c00101c14480040321202d106414080d080f40d82c01c103165000001c0390300400790440024004d041c5c070f08404040d040441d5500410409001d000c0c20103d200009056001c1442211200d40034000403643c00c81c000d015080841381c0c0a4442e594410303011048000602070850100d00030700140000141c0007405100c1d01c44d008031042e160444507040b9258140058101400076078140c2000c011007412070b0f07401c1006001d059040d0b40d0440c06840d0605103000ca01500400020507112158040308150b030b03000c1942401941c0c05a80542a40c018501c1103503540070304d811030920081e00c1301300400c20041c0c2e00c1ca80a840b01d02c1818400c2c4140109800b2135940c001c501c00c1c440070220000c049401544260b440c940d100104400b1242881421310003c0e094950 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 237627428 1250 237626178 237626183
    0x190311010e1816410d090506061801080706030b0612010608010314010903020d0302030a060b0301030501020c1e070b0a0302160b0106120b0901050f030c1305060306010510080402101407 81
    0x902c1e091100c2c06908000c207541885808883c8061500c5104d41352088400c510b5000d00b1034403a07401c0480e100e41d0703800007502d010b600285420096501680b4002e6600c107010344005118880100480d4040c824213494681030b43e04801c064500720f85419000d030080c0203803043e01907010400307203d10354541c1007880c02a8001c0c245c1e07030381d43c1c4055403440c1401d001000c031541c0100a143d042c0403045d0003013500020a0444400240740041e40e0f50703580341d00fa500401c1240c101d1401481e0003c000020f0241c1500507008540b10f40064400030300d500e111000e03103107418044a280d00d8100ca4410003040301000040c6c0f2419915050251821203161340030b40b46111881c1003210410a6000180324595210b5107106102d580d9000400c916501180042e030300b08070510415124180114030a81c10791010300114040720800b421041814144040c08800342600b207980c24024410325000041d103241412840d00c415500c0d440325196a100d0743c0900c04034064044450b07082c044d8880d42600306250b41401441900d0 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 237628678 1250 237627428 237627451
    0x91e17310303120603030c0f05030d020c100506010c020d080706021303060e0d032d060e090a1118010b09010903050d09030b0a051e0403022406190311010e18 69
    0xc0c01c40c540a82501c40f4201d0ba80b40c1e00e03250182c1440040d8002d4080d5440f281c10841c601c845c1080c030301d0824a540710705c60b4900358007400801c0c069401e440005191744400e01b00d2038140419542c00c0d0044423708880364020354890403600e9003401080c60140200100d034041c07000986060350b0750549003d00801d40d84100c500d60b90720200c00e41c001c4400c3c4907904c007000107890280480c80410076410707030103058030b0310500c0c49100d0410840b1030540c03030303511903801040d070103089009034038010400d0341e281c000078036059030302e0341000d41c080c50a4a4001c0704029070360380c900758400c0540d080c854200c04d1904039440c2141444803070b00c4044013242007080404078121041e0b407007206403030440ca00300c000304a0240000006038201014003a0a20603200d044030440c0040c1e00780e824540d62400c01300c1c03510140c10341100420494212440003180f00140861040206562400c4030280081c202c2e6030708601444040c0641c545480005407640c0700f114076035040c00d801055007180c00385201d05816030000c00e0b1004007081c03 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 237629928 1250 237628678 237628777
    0x41802031501050306070f0201020915090a0e0f0f150d060c030e060402030a060b150309060402010f080702100c02211306020d0507030e120a06091e17 66
    0x14a0200a80c035000e4030414900d000c1545001c001c245d90b050f002e003044047c803145004030001380d4400d5050340c613008030081100f02c0f6141078215007101d9502c07002c100b5002d8290302d00c007c5190340c410b81e0b0341c0740690f5070701c046407003541d0315600300100342ca42c007801c046400c5190f420810364035a24440c009030f065000b446c0000b0004e01c01c45010303045841013180080140c102e0020000541d40c00f103011707940c0e80e0b041140401d0381c00e2100d00080e85140481070f103c248090210a1000120300010b920f403143d4801e807525004030040e10390541d9071355400c0b501c400c0183e01a03268108107450642001078511802d00403240310414070640040743d0040b0310311a000c004400304c0c44009030140310400e44014107807400a842030102e013010080252082d40360180c03d0200200b403510203038482e0b079503079482d9204500594010b9125864034030080c0c039000d4800e403074003007900d01c503601001d611086484003a81e1103241005541c1c0c054410444c3c0d03811840703090341c0300854100c3d0320002e540400c00e00460b05074a0000308125 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 237631178 1250 237629928 237629933
    0x902130b19030b100219050f0f100b0d08090f060405060a0c0c0e01060f110c130b0f0a080312060301090c120506091b04021b030c0a0c0503120304030507060204050418 73
    0xc40e045504064131a440a9a9a184064000c609859038000c6d82a940c200101c450030040e29260302180030700320a218244900f0508800850403500c04e4041d000c0920100a80e0402c00141070004900600030000c1000000d005281484040d0303003090010b018642044d40d1200090f400307401c11851080410701d09140c842c10000d20101400180101941220255040401c018021000003444d4001d2010b8480300b0310f400c0c20100540c041c0320a008001d00840b08010360b120b0301038039000c0b011034003615071071214698a1622070042c0c000c2d034410b00000c6003012443c040761500c241000c0c02c510381555130740407080085441080020060055990590440c94852604a1a1000041481066401c9043d444600c0c0045270010790f41c1c0c0c5421100540c0388e406031a04a40e100310024a40d002601c400144000c107404007090384003070035020310b820204c25070ba40c1d0185600c0304070803002c90300418400c10001c2d001a000c1c1e40542445802840010b0902d62181d000c58100c0e0440b540006c1e640c94108074030307400c = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 237632428 1250 237631178 237631181
    0xb03070f1d0603060106050703050a020a0804091b0822060b0d050109020922020f011b031d0a0806040b0408070f0308010e1f05010516320708070902130b1903 69
    0x10886410350013000690300d0304d80300030170078001c90600804020f40000c0e400340d404c1c420410b035001c0c19040303a402d940d0f036952110640002c2c252003401010000c038070002e5150881c000d8450511480001703201c021101c86004410044a070140390446440e40c1d146280902a10780c2e108000c0054031078000040c20303803400d00401c40060350080201c05d50701f90200c13408000301c0107801003002203641551038105e1440b4180c01030b69207a409005a1003040721903c0140c09041d801400040c0004070098003841c3c1100c02c034140a004c0944d8040c1d0111540010040f800240082209603402030084005d642460310720390b180070000560407402e800150784000140040e00c000021250091410011029805101043d0101e01c1c800345c401c40341440300100b40403140c0403140d2817003603820781e11001d00800340c18040103088491340e445800181a4002044051081c5000140041981c0701a0000e1418030b260014140c06035210b4007903070400c960441800220b40c044d8038007074503070b01030b00c42c031280385541c2c81a03070050 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 237633678 1250 237632428 237632431
    0x803040e2404090807020603072f061603020403021002010c17010e0f0a0f020d1e150b070f020904031d0f130e0f0a050607020f0c10030b03070f1d 64
    0x1d148011020811149918001c1d0032072161003982c011403020100d00f007a440350300070008080e4000100104001031651f1200104245140311440b000f4040f888520106a05006074401c140941c00200803801405608803546002c030340601c0d01610b0561a6030104100704200b01d6003001503034449a0304c0b0680c0d50400510740140300709091540d9150314001001f040760001401503d00301c00320b00d0204200c110980c0100050038540e0070155940c5640301c1072140107041150f80482440d441c204101c02d003101d0740c000c6a510484030301e04420100d05020304070000380c0c45200d0440c0c180010089400040c0c0301d1060380c1d4401d5000f80c4079410601c00c00c0b02022200b03070f07000c2001e904c41c02c800c9030381c01219503407201c0d072500c00040ca10300050002c2c0132034003582c85c0c90340804501c90b80b031151203d58003c00034002503242c4120340e160700b501c0060304410442662290840d900580c800003591407568150711aa1004145080007021503000d15a07903c80f1001518003500310641032842c0c611405480e0b0b08208929 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 237634928 1250 237633678 237633691
    0x4230103090f030806010311030c28021e150a0209040b040b0915040204030c12030210090c05010e010210050705090f01090506030403050906040902030c07020a090e0c10180803040e 79
    0xa01c00c90059075903016840c2c440300d000609100c010004254264402d50000404240c0c0305911b07640d80c1000003a0f1140b98000da41a000302c885004030200c0c0d031110a0705140e0301300b00182c008002111301401004140b1003450100c046500c1414000000d4000c0a4012402081259001aa2501c0c07640c00d103c1030780c41140e8001d001e541000b884460640740c24100c9a448002407180c40040d100d0701000030081d110b00e50002e0130140e00b0003004140c848505001c801c10350301c03a4085440c080304004403102929290000900038003280ca60401c15035015102a0581807814416074594a00c0420280308030b52040d960307800014004030325030110342070030340e030b000b82d402400d02308100300c0f40c581800244584002400101041030104a2a02589440003614058854410709648920f8000c20a8265401c1240c06034400d8032404c10003e00790101e0b1050903415200e04000c1c0049041d0103040c4041c102e840004841001603103180314104003400c1468002070000c903406565100e01d041903203d2500d802800c4c1 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 237636178 1250 237634928 237634931
    0x9100203070f032c0904030302090d020301020c0303102403090204110a020a1511032a0d0c09050d0b1501020715170c0a020d0309020303040b0a11011b0509010c060b030304230103 78
    0x4030303a00c0d91707110001ca5038041e50518000d40e5843e10240800c07018100ca0000039015030011503220b03900040031000d0352040d42d220000011080c0e03111340c0075074200d20b0000340e0a0703021803141112407900d104c0d0300500c40c0c0754005403001c40c42e042044e04210469000b0000c080058000002d000e00300025088185540709841e481407000848004407800e9511001d4040b18810421109407951662000b81c80c9030b8038050011150f484036800328006018060f4082c0820001c0c0c41464040341515040f401403400c560022819091f45c1e45404010140e0074000c0e20312415489580300000d03080c1107440d45080358640c15035505c0f400e03441c411059a8620005405002e484c0c0040c007100c89601c2c3d00041c1070b4503c0045103000b040c50442800400c0c210320031a0002ca005040006101e00050340207045507003e9090364000304a09403c0006e03540d1810302e075040a40004d001008014115031184580200860013241c0c0001c0c0b09810b0300001c1d2969010b940034040c03007041203498465100142e03080c0030600000b03090 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 237637428 1250 237636178 237636257
    0x3080309010b010e03030d0b0d05060915010f1a0a090905070201020c12041a0a050c0106090605131b111515010f0f02060a0f0b0a030507140d020609100203070f03 71
    0xc0c0d140d00078020346042248e6030f10404502951203842504405030400d042d01e156080c080724440c0c540d40ba101440ba1104801400043c9101111100304203c0740a00c01d030782400c00801c09400704a900c070440001c10408018000315501825104032400b81c82150001655132100860032810300c01d600c0d500000510090004100b590200892414619240300c078841e5a404c6c114400d94150185079081d80c4698070344a00814070844030351010007138901c211412449264020740400503200c00c3c029801e8120070034210000700b68000c500c1d00c010342c91341c141a41d0034401c2114000603420301c11203440014508080d01100319503046000400d1820700c601c0c01324000c46d08110042d40d00e44014203c00b030100d030f4400d150020030707038940e0102d00d50820003440e01d88a1036590524581d1040c00d8002c903101020b00c0205a0554904000243c5205a01038130007402c152000081040e9801c2460b007080960204101400014020500303000031144240c580c00740442c43c0340700b00c40a0601500708190400318200 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 237638678 1250 237637428 237637457
    0x72f070b130302120307051006170a03090501121805010506010305101d190e070812180411070804061106060d05030313030e0307030303061401090b0a0305090a0c03080309010b01 78
    0xd0000c041d0b0b0340603190200c0d00090120480c3c61441000b10103059402601c48001c40745070346420500840383c1300e40c076030302210f04030760312442e00c0e51154400100440c803800c104002650050110204544007a1030004001183c1c1540301c21005110748201c07020b035541e0f801c0091940e018419140c0010483e44081080c600f0049446a00b07000701111403901942040042c480740070800550700326030002074091101038045035810f595428a030240d00030b07601900c00611450040c141c181c4001040d521030180c1cec40c60810301031000030007458002007400381e030401c4060040b030545802000280415a40c0d00030f200000360f404d030708101000e0013843c4500f580074160804150004103480c1c00a4454515260f002e1141ca025690303414500700039501800341e610004241501644040115200c88140b40700c01004172004490300551805070300f240c0311007404098010b41c03007a841644d000301c0a00464410b01383d10340300c038802d403112a84111600c000001c10028525000c2c080c000030f07080207080054078441c0c841d = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 237639928 1250 237638678 237638707
    0x70f15080a060f0b0702030d020105060f060c1213060e010e010905060d06091b180305030301061d04020708040923010b070c0902030c0405100f02070e072f070b 70
    0x1184040100810100821202032031a4400300c02000c800034568002503442074902c580d03401c03100059120b07000340e140c0e40351107a0040c05664800c0c0d4000340900c0114100d41d00300401074200b040503015034428482d070384c9169440f0b503000384124015610302d0400149030940062200300d030298050b04203c9807e01c3d00100fa60010303140b80944e4003c407240798a401081032414004c040c1079001314441c609103590001c00d070342190340b06c440102807a1350b40e02540038801c02e2605402d00c0e07488010a6907204000400046200704055130401d5407440d640b82d10700d504080040c0a07a0084403042e14a00f50000b010040c00381c1ca841203801984031900c0105002d01000030281c6402014407446c2103074840001d03060100088030343d42001600c543c4c0c0b011901c0c3d04182140d04c8c2190098082c0760300423441c9001c000c9506015040c0020700601d1076009103690f90030000a01d240322000742204080c840480540b0300d1010440141c020720b51705c1e2254007864045c1c1042810714209592340020703290f00b400c0010000607040b0 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 237641178 1250 237639928 237639959
    0xb07090b09040b04020d1104050a08031e0306180c040e0f090d14040f0e04020f0616020d021c0b091603030c020d02030a0f080d0605060c030706052d0108070f 69
    0x4840004814000e400131501a100d0307804d00c00f65036807801c0214040c031020398015005560045d5401107142e41c40304480c60341c82c814030044039102849010a1800c0c20950030046038020b1010b0b002004109024030030411503007007556110707601c0e03001040c144078102440014603400b08800751000c0640c100643c4858981c81c0801c0220200807a50351001d100c007215400b200d00400c0c110a8584001d40c1c1d030303608108506425102244260030300700f04488585805001d454050412076401c03108420203608001d603a0000705400c9070040e003038a00d400e041000c4010346035803842c0102e803d04282e15140007a142003044007600d01c4000b0120681c14400b10b41e0140c4002c2440764180c0300d111001c1d0850002919001d44808020004103c0408540c10407064801508484200e024140b010903114402c002e180e024068140d092a40107200040108005030404c0782c03c090031070141c04071280c040b10152601c154500c41d460b001166400100100301c03003040034100410a14031b0091506050110f80b2946080 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 237642428 1250 237641178 237641197
    0x70b0408060604140f1f06020615090c04060302070f0605010909030e010f020a030507080f0307020d0201060e0103020d061a03011b08010b070b0f10050604060c230309010c030c0c0806040b07090b 85
    0x4000e00000d141c6c1d22a003801c0d4500f52280d981001c00c40b541e54000a6030f4000451742d0320030003d01d5118058141c24019401d500038000e90010b44d0400c0c0c00d1010440c001e400c10481a554241c24100d81d40c0400d0007881500e0181806000200d40000d941c100a446411070041003030401041c000c00350070f0107a01140c2c02403210743c0b40c47c0403691103d4908000c20755010300c8020b6442990004180007106400140c1001207014503002800210350710101521811000d100c0603400450958880c3c0004011b9881001611407481c00703010300340c10b201d01103400c680c000000a0303514071a01c20309001c042d03000100c80e0300402c00120000d00d483e07410756030117903040d501900c0d407040c2c2003480d00403640b407402003000f1102821014254940b02d560310341004203081c8218005441e034401d030f4010041e00020301a0030700d4031114008002e52501300300000445100c1c014032020340800c80e21070500400554208403140085c16604002c140e203080c01d041c030584226025080b0400d20402890800c04280d0960523070b0480d10 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 237643678 1250 237642428 237642451
    0xa02010203041406090414060a17280f0809120c0d030c030c1b0314010b01200111040e04031106070206060d080c030d0f050c160f060204030203070b040806060414 71
    0x3c401000c100c2500803569810362243c01d10500c17824809890003001d114080803100e0074501c6958400f80040c40d04960f0740781460780c2280c80d000d91100c2d03a091181260040740081000003441945070710b420014620002c1780c80f03420010702c0402902d40480e0113407260341c0c660050701201d03440c1d00001c0d0114907015001424004054100340c00d260080b144c20106031b400c8031005004040c928a110a00001804228cc260041d0480c1c26a200700520900700025010717140d080080d082c2c480d00401001c001d040b004400e6403600c0040c84484000c44c0600004e03d001c0c007501c08141018640600341140038488004545e1014080118213a40082c00340d0300300c0300a40d0001d003580700b6420285a60b10621450341c460344000282d40c4030301c034219804151044900c800c1000b4039290307a4480c06080c451000300320310b09070520400c07070003040c1a2003400b1001403150100501e0260f91341e0119080100701c2c0e028900c06003021808200e03030402881b0f181d070b1020007140d04009444070103090138440d03000504040c0d11031 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 237644928 1250 237643678 237643709
    0x206040b060604051819091a1906060905040f290a030b04050607020706090b0706020c01020c011d010b01080c2703060a1e060b03061c0c060c0201110a0201020304 71
    0x140c85100403030700a410b01420224100600000001105c0c1050f11080c00d200080c500410b0800d81070710442c0112540a2003511168110891100c0c0200019014142c41c01c1c40d2448518150f696104280c000c0c5801d4841b40e401038900800c11040314200e0a01204003814107119003101601d1015045070380240c420441e19102d80b800c04110200c0c000d4100403c20380c3d034203041c07005001780010218481c0070380d41d00b1a0700460701d0f0b00c000c68000da4184580e0444c85010f006e414002051a00901050f08030707803000500b011000040503003510344124404031803031100ca400d00040903080c05200c0003000300f0300b4102064203203410118502d1003504a028840c07000c0d41180000d00c004180d0384c01e40c1c0c500c000d086807281d04024014100421010900400030000e1076442c1c520108103024a004894400e5141411036403018148009000a0121002c900050f9280c0c0d100268216000c1e101610003030396840d83d80e0641d0710014103640c2001484602e9a40080102001071f0b074004100c0d01581c0082d0a0203081 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 237646178 1250 237644928 237644941
    0x803030606091903060612020906010201110a0e030a05070f06021c090315020702040f020d0f110405040c09080a03020106060e0303090d1203020c10050402040510150e06190918020a0206040b 83
    0x10b43e401d03000184018140100080d464010820510440d03000312034540c01621001d0040e802c0352000c10f001068040f09008180e04507005440c15004980043c1c2540d0542c40f25990b65414105c0640041c0c55a03400381c002409125810400403805040000c803c8209011075240078006844900c401040c80107106c15064507400241c041c0d4011a41c054420701400c41d4818060001c0d4000042146141e803a2070003000c0760001070b01500c0b030445810620700b85031500b005c2c140005446038494000520000c0c200003d00080200542c40c9240c0c0070b41d00010b8543e0901c0c000503d01e40d14041142d109a10902810741c0c55969140000d0605074450646c010b10f101c0c060041d4043d014441c05024580528a907800248000c2c0d00042d10440c42103800300100d541d5503001c2580c409190180020846906007a61412030081c5100384501c01d0040100d42000c41710884159102d00407104c03480044c402110400c9460044600051048461003003035080000d550002541d80c03200402c0540b1088480020811 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 237647428 1250 237646178 237646219
    0x240607030905030a150513020109090b0d050f0102030603192a120b010806010b0309060a050c0f04031b06050f0f070609050304150905030106050a060e03010f0513020a080303060609 79
    0x2d11016059540362452401c0505112200d0040030b069035013480b0003d5661404c251468045944c16120354a659052101d031500800c0b6554210b07070406c1d000d464100200b030042151444545500002583e0307890f10344281403c2a148000145101c5084610701e8005800000c4100e40900d00940281000c140308904900c12a01c43d407010309030340300c00080e038800d0248003e80305050311982c404407801ca0366219011031040c07104489403100c075000640862061059600800d0b004144501d81a042105045a48001d139005d075104960403401c1c5004201640861a90000249a01e0901c0303802c0c032844051080062058149188102c9000034443c4100029580a6281150030000726500c6603100c407441601010451a405c02083c0c03490000a0700f85814007a003403d5401c0506540311062511406962450003001c00711390654031400819080000c0c0d01c9824480d44a027402481682454014012008420381090741e494008000b084a0758481c401120101c001c141c691840b072510b290714200 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 237648678 1250 237647428 237647447
    0x5061305060a1e0602010b150a051c1b0f0e09010603270309050316080d08060414101404060f03020d0201050c031216050307120506030f120a030524060703 68
    0x6a400c3d54000c11a81400c03586034000082e03803081d4008100240840080041401c103103c4101c600c00e50400038030010030712540207000c48424911001a848098004c0c410649a1000d8105001ea0303080c5041142079900281802d002162800c02d07a50121400000c5888c00e00d05018031401d1648594504c2c6104106c07a0a403500c0822800803a60015041d1800070044001845920710921446102c10b0b41c0c1c04500314510200c0f404800140808101040c06491004009003480c2c0d01640e1003000215282c84440c49503c5000c0181c0060441400d0085454034088804e020a008529140c03080c013024880e0103030002680e030125181501003405100490f80d510400d44251894040401c2c221903210451103203502859500001501c0c50040e503104480a02044840000060b508014006080984c1d8841a00590003070b00b542c80c00c4100381c07070181c5442e05001e041c45e9210400030304640d01a078140300b084d030071641801311040c03119041c40f044507590204146051090b000012000e08041c000c61100 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 237649928 1250 237648678 237648689
    0x9031103030d0504110102060f10090b0d020d030c060c0e09041707050a0605070f030e06060f03010b0a06090306050604180326130308100602070b090402120f10080105061305060a 78
    0x188903031302d818508070700c801c0a070380c01c282c2c094400d03080800c149003400310f00709202ea01106042800e041c50000c00c80d000c1e00300114401e8104a180100c04050f8480d8105081c40c03034025120700b0342c8140c1c10702d44070381107401d0300c00c0300f00c01c0228201805040d590348080d16078015400690038440f00f460880703d050a03108141d00103055100f00c1444604003c0e01d230700521300c00c51094503002c030b812001400546c00c2d14070241901b4590380044001889604c2c00014801041360050f0000a45043c0c40002c1491041250024000f084c0611005c101b0440c4030700825911050640d0f0a006a0244000d24460f076a64407000500f8080708001082001c45881c2c40744c4d04c82c078480c0ca1500200d0900d448115405010550207600041008001480d40015103c1400840f5502e6008244540c6802c1026100740c0064901a40c0607808002803050000c440010707070b024041c840d8510307485040100d00600200d803a60301040071a41400c0802c08c003640c5401818074080c40841011407070390b440c02c0014150b0545600803 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 237651178 1250 237649928 237649931
    0x90303051c14010608010902091f02071502010e010e010b0303030c1b0706080106020d080106080c0d02130e061c080a0c140a0506060a05010c0b06060c0f010501091b0f09031103030d 79
    0xa10600406008020b0f040319581c1d1a028843d03621401d00205a20440c1580703500481e4191005c03001415160014210001da40705071500d064403003081c9240f50070641c7c03080c0e0060791190440b8440384802e1007002207004610008000d092400c4000ca40c50380001000c0022590010886c0040f000c524046e107501e05814905444640b07465010142544400f0b01070b8000510a0982c88103096024103c62070580f013003903e606046580e00ca64803c099403011041d858440c1e02803008950701890103c00001800d00c5201d00d917002c0c07400b003060000c003040182c5405400c1f10f4042c40100442d0005007140d6500610b07290101c1140824105606000032030a502c52440c8110901c900c284000400e155000d01421515006840d5944d001111b1090382114040c000c881010081600c07072622400800d42006840c0035101c000d055081e071070342100d4090b400860f4440d2590341080031043c000d60000c08203032143c21300011458841400030040d940d2808010100119441010560b0b5005c200380c43e00000745a00 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 237652428 1250 237651178 237651191
    0x5010e0105010303030501120b0f09030d060e04050f06010b030f070e1e010813022b0b01080d03050a020a080402310218010e10080a0605060a08100b0a090303051c 71
    0x240034000c0509110640001c1d02e420008203d80e012154400d000302d0304519101031984484400c49111140030345002c1d01d83c8000c0154001540740d138060b0030020000c40c9444001840d0500f0b0444c1000340c04031382d900407038000d6001402101d4284051341d0704080c1104101503d41c1e2518010f451601404191540c041c4002040342c041c9480300a500c414600e0a82e54861991140321640d00c443c41400c0c80254014103000d903001d080c00382c8081d800d40f000740b411341400020394183c84d00d58111500b030b04100d102c0c1e000341818180894241c01856008054401d086203025942074000b40441c43c0540000c2c4213000d200354041d510394003001451142000e96400c005a0200400054000d5010081c0051310301d003902c0f1814800d40c060907482102e540c0182c10710510510f906012980c60301c0c0207018256080d40c901c000b141c140c6601700079103c0b46515460300715007070400d044460ba0f0000a40d218100401003005242c0c041944041c00c042220750504000b0749031070305140c0700c0040400d02604411210314004 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 237653678 1250 237652428 237652451
    0x60a090c0c14160f05181302090f01170a0c0302120f030307020714030d1407061401180e0a0302031b030d050a02070b0a05060609120f0a060c0f050403051c0c0501 71
    0x1e0f1000210303161008941919620180c0040714003440c850154002010290b04a0f6045401c04c0b641e4011062040c448083d009640002c2d40c0b0310095420b00081020314006029004108100e54542e82e02c1030000c22218825a850240500c800c1c00024080d41e14000c1a0a22500404c9648000303840c480c1540c4d181d29010f0300c000c0d6504414801c10703900300240c140c0361070a81004110002503008942d0740c40d9010500440a40307080d03120081c02c40f0b809556030058820391401c11a8103001e4810852200c0b050341c05070380942d0544801c210b98114541094900400090300007080b946c00e02044101d084e41e50380d2a807640760441c002e800d481e800071820002000f80c00b03451980141a140c0c8583d000c0d421945a0440340317030403540200c4050f9088403080103400000d140a9107014440f2442104403803812000003903084c1030821142c2c0440d900d6842d1641c00203041d8001d54612481d01e42d51900a040c5072958403810b0b41c1c0d00014184500c1141010045810a8420600c000c4d4940d00880240100c040c86c1 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 237654928 1250 237653678 237653683
    0x90903031d240919140a05010203100b181c14030702150a0212090f030a1103010c0e0114160f0516060c02010215150415090b09060a090c0c14 62
    0x1411412400e111080c44681100ba40801c01e0041c03030400002e114000d110780b80c20b1229840510709440301d04031030080c000600000c100464045202e000090786a05042c520507100c2c2049822003241c1310000c0c4a03088282c405032188501204048418251407101085900c40c651a420006845050441207001c6050000170050003000e1090b0389640701400c8146002072a4080d04151380b00503040000c1003400c5031507160180540c040e0040000510306a58000a85070401c4010210380c00c40f11410740810904d030a1081141d81c42041c1024681404001c000911400d214000d454501c0342c046410001c0000c0f00e40d04c80211070703000c20410b0100043d800c02c1c076501c000320450b00b110301a4012010465510440c0c00003001541a00181090501018410310390072008044850b15078007180b00081c15540c40c02500515804c0e10041d0784190b080503620780c240c2c0e0b0b07100456406142040c041c00343d180c844030500821522860400a2442d4102c1000c98800d40960f1029000c2c1600200c5a041356401 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 237656178 1250 237654928 237654943
    0x30908100b1906020a1103010f0519110405060904090f0501060605030906011505040521070603020405130209090f100b030c03090d090605042d09270804090903031d 72
    0x86510000b0210460841040e440242c0070ba6001600442c030114009603240e584801240c200400216120601844190482d5030849040842e20701c5901c0710360121909120302170300201048915032901c0d04100126005102e410006800349540d14440c2c0c0610078071403001c0303881550050007030003103560300c0c1c070003d00c1c3d500b0a503014074030f038080c480c000558110350107690103110f03890b9180c990420389014100a800f002d1000b41d26101c000001c0242280355090000101801c890b49005032503a08260501a20389841d04500640c03030b104005842c200d981d0903282c990302403600448101543d0314506a0f2420005c264407586101c10080305002c080342c0503002951003022000111160082c0065049030002124841c0c1c401150040000748000c41800c40490715804180340c40810f2210090403110300e02205510402c1c07002d41d02c400d80300c0a80325004a01c12200e440125540c03d134403803620386c1a258401c600c602c0004a58032020002014002d42045d040c60f8038400c1e10384078014071694081d440b18030 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 237657428 1250 237656178 237656201
    0xc0a050a1709210403150b0301020705060117071a09040e0a0609060b040c0201090b040803060a0e04140f060106090e15090a060302010f02011103160c020d080a090f061b03090810 78
    0x780403410031000e00b0f02e0140e03800c50390802d54a41075a09001c0d28540104403808129030507540070040340000ca042040b550340203004840e0145002001c08201c84d00340800c0e0703001044c0640f41c80d05205000e200490076a803142c01d00721400100b44024000a03898080f810350018841c80c10410468184141ca50151448440950b014042860704a01c12400c80b10342140080030340c5d44020104020406040280d6442400a804100180d0329804018422141120201e55502d080c009a9550138400d2120340c0d20860010000d00007035051043c0502944110300031144104148800201000d40407026480342c100068484085810103002882c003034255404168049103808010462082c4144105c82806503070084060454550400d280b0030091054405000c000000f00c031180035a8a06894040e0a849415441d50b168401000034005621560041d0112000103608011075a040b88062600413120498483c400c601c0f0f150a803850f0a054020407050720400840c0469221944c0c8080701c4100c = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 237658678 1250 237657428 237657463
    0x11011115040515040b04061d0307080c0d0c0206030106080a0605090901020d0c020313050603040507080303090624010c060f0e07140f060408031b0102070f030905090703050c0a050a1709 81
    0x603c400d50480c851001500d00401c2402c001c40060040345499000d49244602c00248105050883c08000d140d1303000120f05039200400029800344824040000e04056030700c50500c0303c0500803d400144079804144607102c00e000310354001403650341d1035074084005007a005003400c01c98240094032a00035000481003003501d51034140404c10903400007054440200c0840c1c0e01c3e140840c189400e200c80c6400c0034004540390712130180003150251040c0040c500c520b0b020401811285440c46026200b810018802e5158052081d6156500e0740e010103540c0d1611380004000c90008404030b00d4400a0540c81070f13544041c01942c40120390200c000501c004e00c1c07902141c5190340d041860013040600e11035807064004070340c010000786910900c150544130f075107500e0200040c00d04840b510303503042c030900c82da03400c40014401180500036864400710707154000d14680740c01c0160349402902a106842111440401d0240224850510030300c12520f00941c2d9800ca0820540350800b0701c0c8403691036243c0c0c003070b030329016 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 237659928 1250 237658678 237658693
    0x11805090c03270c01140d140f0705090f210a05030301080c060337060b07140313210606030503250f1104020d020a0206060405160903110111150405 65
    0x1c58030707039040c00c4018483d100a0003410000000540da286ca003200710607562941400b43c40d58440651280000d84403040c84150f03014a400d540192000170010325103024400c080c8180066078032030307408081600740c1c280c4d800103070000b5030142c055030f088420700c044109124058120041100c040080c5040300c010104884640e8611010005a40012150094403070a051441d4185074954222107808090a68950601d001c40c03844a0b0140c461941000f01c140200040c0203080000f041444204440140099410240ac400700030300070407614840c0d00c0b00d100d40201114180ca24180c0100d40c2c650b4040405c0219507a20700d021a1260031101c0788004010100c030100010303040c014264507446500c48041401c0040540d2021903500d410544150050340c28405401242c145100405e034200058000b01514034000c0100415204010101c03040216050f40c0c6070700300783d0400414010303207500003040e41000480400480780e00c8a20594511240701c0d0401070303245080500007860003140a5016100303007 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 237661178 1250 237659928 237659971
    0x20a080a051906060b0d1b050a050306240c010e060f0405101a061c110c030a03020904090c03031e0203040f090e1e0c18070e011805090c03 61
    0x11040300d1000549282c2000607400126a07544001d01800741c45010000740c65038031580180099001500207818150781e03034105006500900c03000480c020740314078049140610a81008101c0c0c0006002a400741d2540d00701d0403110f144406606120031007541d003043d100c0b103132000103071b02030803580d00f14440c01d02510012a07042001d203010984242e0b0400300500311321a00e485c901004180341e03002c41c00342d44400740b090030f11680d54400520008100c2038207404600808414030044800044400001400030030981000d00c1010090300c08081aa080050300e483c59080840c01400024000038030382c0c4c0c2861408001c141d005284100621100f4001145510381140c00746d80d00c0c80380d405a40d41c1d103018450304100300e010300d030840040103000806480d10702001081004d0316441c6040c0f600d140c3d070420440420141005429140140c0c5d0900340b0f039080f402c010034043c00301c0710358400710350400141d1807560501c0b21103641010000d05024150a81c5440c220f08114941d1300140c921409240d01032801510 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 237662428 1250 237661178 237661183
    0xc0706060b040b0a260a0e0c012a020102010b09040501140a0c0207030f0f0f0c0611012306010c0b011202090702010203090616140d020c0f0a11010305040c0b0a0c020a08 74
    0x151001041c403589080d218800075241c0c4807050f40040710890340050b02c041c0044082c602117010380e46c500404696225401c3c1d1450425103980f002d103040000071409e04461011604c200100c5108100c800d540540b01400100d0240648421043d08160312005010030828154407040e851807100074480081c0e1034100b9908145d07000200b0000040c0d2090317109001040c1d00e200150700e51841200c041c25070550a0780c9a68405090b403c06594882c40180100066174019092031140c41e8014020001240b01e05121110310140000c145100d1609074000b0320305900a90641120941100810141c2e42c0d4a20b40c4603503103803140d98101c1c05060712002048805005000740c0b401540c04d400504266500c010102441e106400144800c101b07462051441d044a42c03c01410602c04203031380541d0790600510140c0c60201d105042d20440d9000f00051340100d442c00c20507000c490300c24640030907a0b407500c6c201581c035031034180c0180642c1103000030030203410f03504500c400f510644203031114140207a8400036070341c = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 237663678 1250 237662428 237662437
    0x6081608060106051305040218030a0b0601140c070b0a05040b1206041112071409300703080307030c02011b0806040e011505010c15090308010801050f060d290c0706060b 74
    0x203281040f01d1818001480c1640207071080141410400b07070a449e01c500041c1c9840040700041e070381003505000f03116036960300c46200d49250300c00c15100d030700e0a4a0300d0701e01c55440210b4459000c81003408195404000d01c10f004440082c1b21a120181d02e50a6003950901c0130364065603842d205500e04040500625001019611443e4006d03010113182e5444100580d000a0000f03150001c00030b0030428000186d440400100040640030b20003481c58600e00d0201e02401c0c5902c40900c0700da40101d0082001401034021030b98021620b02d004190300c03e9028050b805017441020b1040c0e00741d03c086000c1c80300da1b070000c800c512409044505000d43d103d81c0361711600702c07802c00b43c40c1e042610104005000c254016045076480c6441340c50740030324184002c181c54049402d030031400c900207144903004000000b801d01034550800842ea00107aa60704000f0002001c01c1d1112070001d0008404140402032440b8444044110004032030710030406240c50805402654000042210618640305010071011350000558 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 237664928 1250 237663678 237663697
    0x10608160501080a15080307060501080a0822320a06090504150305070806010e070512160302120a05160201051b09150d0c0906031b03020307030608160806010605 71
    0x404a41c149801100c4269000f0608100c0580f25a005180c003605034540c0341c020b08400c0095a1104000d10308001503403410303400b1120700c0d0300c2514000d010941100c1185c1555040e281080d400c1d00008140c180c00e01ca441c1d101384540b41038442d1914606080039140803600800a00c142003260310841008844006800355000141d54400c040c480c504255006440c1c1c030400c40c82d50a1059520b90750246402c07030541014505401c4400100240035420f81c0c0c1c1900501c0c02d0400c0c1d41801c0100f888401501380007040008880e040400e01c0740d50034003d80c111100d0300d1580300400c0c02d510b40b030342076900981004c1e0f4640c00c60009038501004c900b441072040501524006069510060400400e40c801c0e4010041140e4000340d101c0c2a80d615030329101c024003140c0d10500000c144000c0a07040501403603000c3d400380080c141010450300c00c1c000f4a00600d84124400d00380161030b038035608401c800400450700a08bc0310f20400c4c0d030000500004400d071008846220701103a40982c0c070358904480601405005 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 237666178 1250 237664928 237664963
    0x8010903021005061f03180206040b181509090a0216060b13060b030f07021e2a0102030a0305071e08100b1201060e040902040f0905011508030d020721080108010608 72
    0x20105c400784243c0105c40040700c01248114141c2c0181c0009441c0e51096026043d02240040c45254821a80340382080380700701140caa241c800c1510400c101544505841144900010f400282c0c194015506030b507034959400480c15034070b48083c9440c0e401400c1080c4064030403022050301d200b100b00b284c080c030015910a0300c10300d030035900e0307505400306520800303002d83c4250300403030031007405529000384110031070f21081d00102000b000303d03c07494500c1c004a8050034084050440c424050381d0300081101d002c0034492030001199510058202c4030000b0300c20303042c0d410002c1c0415011400d58010016402100002c041002c2207036103001c0e0b40b0b014410426030f0011703030030312000400c101d6010311414954110b02a0000c1440c14051340000c08480b403811507500030b42c0e80c40c0c0410080c003601340b058004045200b98224443d60800c2e41299588c000d110750800e10980000b015410040a64074681050740300d02e6200c2051484410040d09843c000d0007002160341c80c200c00020302490002e0001c402d1005510f9 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 237667428 1250 237666178 237666229
    0x3090301050a02131703070206030709060906020c06030106050711060406170a090c031401060f0e01080d020604050622080307020a140a030c021e120d0e06070c0e0601090801090302100506 82
    0x108402d482c5c0700c8001e181e2502041c4114009a15400010b6110741c0300c41d1740d01c0d1030081c1070140c0078000103216040202154400d900c0d40140d615148210381c1500c0f01c074240301d82c464605240507030514025031202c603040300d40807034009076040c0c02800c0340d2084070481e02d0b0168117039150340c0148111200c07904090b14110364a5010804240310840400303c40d0f0304807002007042901c0e016030f0010b110300c66000b03540380d840200042199000c1402500200708051000c1e01c8141807c0d02c0350781d920800500907514a1481c2c0d0001c20700c64a5011030606010350246003642c50785003200c0040d48031109001d0580d862034810382003000d60000800c01c6405c541c0c1c0354071580c02902598092043c0d02520300003044011500012380c00d01a50340d82c0d580c00d08a400e42c0010620410b4800c2d00074088891000118000c08003030240700300040c0c0b40d90342282500e60652021403203545c2c01004031034400890303224500703551a100142c8181980800ca924074100c044805100343c0c0c40d50300503c4201000c140e00d05a25810300e00 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 237668678 1250 237667428 237667439
    0x40f05090a17070f03080402012c04020d0204030b010e07090819080715090f03030c0f020307060207021f1106070804050a06050703061505040305010507080912090d06020c03090301050a0213 83
    0x20b8211142c02e507040162030a003521075554282542c021a0164085211081000219030384a0305600700024a86986d600c0002204003581c034034603030080c1d568032682d00810f0701f4819040e660705840080d60002640c40d01d6581d5051640080041501c000000501c54480030940500c0010160412000d1020707640c0141d0b01c5880301c0d1400d40048108484410000b0f002c030071940c0c0c407401880000c90103050a0012100c140c034000d421201e202c43da10040c40100c810442c0740075008020b0781c40e00341e00460096910429840069002c3e008001d01240210000c90b1a11100f50306c80c2c40b103040301420b035080b20080d4440d03020540e070b5010100c1d0000c0640d442030031602e0018507507411454009100303040115919440f8a1500c0f6040403010b100783c0015030201c1c003041070050034002d00f070700030340750303040101c01804c7c40a021500e8010340617070840f1111001a10209940b0f070420154900382d00a0801c6444911511a941d22540f001c1c0b21144250b007400c01242949680d4421624407001a4000c2d01c4213601d80b6 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 237669928 1250 237668678 237668693
    0x1020307050a0b10050901080c0111070f0501211104060909090206040306150b0d0c080f1303111f02090315070816140316020f070b0f030919030e040f05090a 69
    0x801c10084000302c1000005c1036140c0b12078007806070050310090725040084100060100c0c0418013003010f658080007040043c8002c0880c9101a1442072a005002c0000d6580201144109110070500240743c030050110001b400d0001d00b042c1c880e9a035804841c150b4400300307101600d50070701001e035020000300410070008030294000c1906d1000f061086000c9561260000740d00e400007404810010340307500081c03000302d41c4540d00303580c480c50a58500d0401e0400f0070700140314642c101340040912002a130326094405080040c45c0204600c40380b940762014900300850041d411072040c2a01034810a5007452501c00900350561140326290b54001031540c400b0302e0002e1500502e410641401040302d50300c3c6584003003200541c4070300c031804c0300d1a68400100c04001d1030248500503d045039000702034180400d10003842103500a210081c201303038a0fa10f0700d6400e0740c01c02c1041c005034001200388140074000c254124400a05018088404100c011110008081a504111007400550308248800c0c0c0009041 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 237671178 1250 237669928 237669931
    0x301081902030c0a030503040f0503010204150e0a150905150a0206040303150b0d1b020a120305070e031516020703050c04180c181b0507061a03100209030c01020307050a0b 75
    0x1002c59080c1d0007104089065904d481c2c209551507000041e042c44044501c2c01201d0060000740c00861030203107440c3c000b144101611824000300a50f401c072000c5256a07003400d94001d080459480c40d9031000e41400a000e0300d010384030300760240410943d4000c100408105403072500c2c0040d00680555500c940d0120018138050390300030100c00782c3c0b08020942241c8c40003d0881e5402c40c4038002214a415002d05440741c620409807000c40d80140340c1400000c004601042ea2807401c1d0078085a10746920b001607600c1c0c50401d1113a6018030071409028184000d0007000c074051b40600600c4440700703c1154089881703084c0d500024185a11541030b000c25818a540a00746123075070501c1d54002188540c0d2818050011944099081580741103409107501c064400d10090494906600314008442c0e0b4028003140240e85014012603a9403100d070b11103400190296001d090018141da210a0504404800940140380b40e540039114401d19842194000011903003115005402020180000c0e900c01100200 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 237672428 1250 237671178 237671183
    0x30c03051023120d230304080403170909190c02010b06040513060503060907060e010305040b0c0a0c05161e12300305010e070927020c0303040609030f030203010819 72
    0x1082080f0318205104141d03090701036950340e2040c282858441c152039035000001d204120010014000001e81d1101203804681d400721260014100c48602c030b050a0040301d01041d0421244410440100e203500d0032501004c498600400070f100512038220308075810980c91a421000400082c03000c0d25041851803c050420140070400741c4c1c8403400f0a050420a032802c401075800400d0a000700d0741c00c40300100300c4010a1900308110b14080e2900104218094081c041200001980c180e01500c40c074030119640ea040411618285950000d9020034447d0348100245c0c01002c01400c0500d02030000c0040845801c50f004030703816600b43c2c69100030244542660301c40c0344c4014000401100c80d10300102d000280e9a140080c580d0314280511000c039800401800800c900c0350307010301101000808880d42c80c1d80752a0034500322025000780300c2c000d1040c0d1602c08403e03c0007208000400c07010b5004040345510940e40c441b1081c7e20740320143d080e80403c1c014021030b074010b00380c03804481e408042c2c401803690 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 237673678 1250 237672428 237672439
    0x170a0212070e130b0901060c0809030111070209071110180b010e0105040b010e0f06220b070b090109020102120f0714060411090405060f071205070801050907050f0702150910030c03051023 82
    0x46903d0008cd00716042c2c04800c05d840140400d10700258641426010b81c01381444c01d02c195400340c001e5000381c4076003494032044010340d0b607489503c041d149254880410700740e03c03428071905541c44a034000741854091243c64812410a080e02c441d030b500c60035450120560207824144114592800c00005412030180362000345c2e01d440da040c8801110010341001000001481c80d41e91125040c11200d400004011540503811b01c42902c0060b40e000516800c810715644c0b06545031030021030700045622611700094100400741c809440301074408981d050045100d120300c4c030003204401040c8003510301c08035005440394000301c001907a425961607900d503101400d8504902006c0e034103a0114100d070002d0b41e04400181c0d0040051101e03040403225140c001d2914103107030741481001d074a2000a0711070f402c0024000c42030103070b18102c1800170401b0365034031100092180c0890078070401d0007402012510505000641010049100710203d00e0543d001e5031282d90030711141e170740c01e082d0b044200300006074840d8010 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 237674928 1250 237673678 237673687
    0x1005100801060320031f020a0f0c0f1209050a030503040503010c08060a09022109010b0a080309060d0b0a050a230a031104020c0f01023007170a0212070e130b0901060c08 74
    0x110145980310103003190400006031507a4180d01c0050a0794001c0c40c401c010300207900002b6000c1a41d00032805030144e4012040341303158018040484440049600c8650031491509012007041070202c0a031054860640003005981c1800c40125903500c420b079210b0340c000421990078040500580c00906070310031032841070100c0c0b4200541206110000300c23034080303283e503540b519410107180030041c1800a00c03200d8019800c0500580002d442d81c8a04089644002da0300c4241c640c264441818600c01020024184031001e80e07614841b48980c0c005010088124140b0082040d00785008000d400599400c800202c0345d103400402400029401442d5440f094414101091403618090006110b4444001c8a0048501900420351120f007651072407248000101d008114049a010182c00c0b1006c0080d03c1d25210351f00c0e04503074080244954005810060f114004001f101c6030400142d40c105c0c641903660803503460701c6d007142108030742c460060241e0062a460041103014400c8a40c8003c140c01240700c503180 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 237676178 1250 237674928 237674953
    0x120306090115020a0b0a022a1213120602030421050409180f0c050a080c03031207120603120e030a0b0f07210b1018031211100510080106032003 63
    0x2944080340c0108059400282e1780c0b04003880c42d40e000e0540408d903542004c10300854812503031030300f151030b10300a11000c010030948041d0120400e0880140b602c542041d9040d1a20304164029610403201611508036003502503410301442e0100c103042501c1582c2d070906044c10020b003c809811000051100246107078542c00c082034040c100280400c3c45001c0d00f80d030300c91802c414000c0b90081580074000c41e410410300b0304501c4d1008001c460740e02c03601c103402c051f00e60784881050710890350800c03090708a81d2810308084100710000c81c44408516080d109c02c00c10244120801d50343c3c0031b040000600340c45214011032000c5500c1c0c0c15217030f00310000c0d0429100c041c01646405030403444880c4a1084e81c0c1c0c48210007095401c091000e10300007241454075184d0286084d00442541c000351100908240307419504182c814480c03030015507514444400d44004401a40d0300305e01409040e1051002801e070003200240a00b814443d1034100da82c45003001c1d54102c3e0070b24000e4841c4064059140d010300580154050 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 237677428 1250 237676178 237676193
    0x3080403031d0a17040b220b0f0901020c090c0a0e060d0e031c2306041104140307060504080d03110d1419050f0105041a041805120306090115020a 64
    0x1025110b00c01400309008500344102211051010180d003c1802c0005202c03803520402120050640042990150701007449180d00c5107215900c014803128011400351b0031040000010403d14400340d003191071a4403030f00104070b000c18054400c005090700800a03101000d00400d41c204401100429982c14024002405010740701039010010b07180c0c000081c4400241c90401c0324928040041e00100070707181400c0c100317a4585040c0d080d0010760401c2900020380035501d03a0007100002c02d8617240700380c0304d40e9a4886080c1c0800204000ca1103030080500200390548140c0c02c4d00c0c2102c41c1e8800910f01c4290900c4182e00400500b1203900100104110300342d0044090702034019080c440000e10344040c0b50030000c2c40003504c90310100152440c10b14060094440c0d0100c40603055540448000030515404841d03048d0240c42e004103280c05c01c0c00c180b80c600d2540840154096168007402c140c4091043c1070202d1b10051004448030f0b580700011200600501340710500c001c1030001c03140111820600340c0e072680755 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 237678678 1250 237677428 237677471
    0x6010804150e12251109130206070c210818010e040903110d02030a080a021b15070e04022505150c0406030609020313030e0411040306051806010609030308040303 71
    0x3088408001013000507100380d00e8400400400703d511400000b1404d66840401d169075441a0f48205511808a5103141070355062581f03555000f00390a030307203a80702d20702001081014821040e061030740c210403906800b035801e1540e00540c1e0045a062416541c3da0a05020119014201e41080b00c1d01000c0b01d91a00c40f441030f05a00390180d20340000c031080004201d80b4184000f41039500310340052200d82030540d0085900c076013000200c1d90260303d501349003815201412003201001201d105090082418030010468203000e000c690741d50001010b54a014003040e4440c090340c2c04c1d00e8001183c1881c0351422910400f020003417040080d9800901d850b8503985810f03106036180074072003e00007010826a0303010700c0340030000d000501c42541149080c074142902c5c50182e400150511050300b40605055903031307603c06803c01010b00c402c66200c0c0c1d100c1c00e064004100460382c0d00000d454004155424240000c0e445048510304c2d07440c4481c0743d0031070345d048a0403500940308605243c0c8968450340c0c003e00245215 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 237679928 1250 237678678 237678703
    0xb0d1103090303010824070302030c0712080105100905151b0f0d0207090501030308060d0c0803040905010306060b040305210724111e0c030408010203010b04030b0106050306010804150e 81
    0x2c58881d4107000c1c106003001e1441300d603414441507840e2012901400b4000d81135000105041c01600d964920480100303034802d05000500395483d001c08030350041e4005000d14140c840648a0100d2802e016000b03031000e80c91740c02075035403040b0540e20f080035440c013007802001e0710001c030405803e86030007662581749845410907420300c0c25040440b10441c1103904111a8008090484041c49554559240500030303c4024003814003c0c00da0880740d40030720292000a10080101800712a40d942e070300c0f42d524004000a000032203049041140008011407501c080d10306503504000540403408868000e6482c1c5c8803122030080b40310509203c501c0102c2e0505405440e504540194800d0600031b00708104101c949400c0740c00c0040030f0074068a62030480310b0300201c00042e00c1d802501d0341c428840d500f2030301d1805142d0003540f4641c0004004142078a4804c080d1003100d201311400109642c0b00c00c800c0c2c2d802d001c1207480c40c1c001084030300040c0115a05501220301c400e640f46000550b604001282c5043c0048980341 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 237681178 1250 237679928 237679933
    0xf09050a0641010f0f02150a1505041506051b0102040306050a0b0109140105090a180c0f110a030509041d0f070512060a0c11010c03150602060f010b0d110309 69
    0x41c0300e141c01601c2c0c0841e10000720103500480311140c490002c2c2c0014451044841080314128000d040380d402000b820b4090104041151f0680c07510784118000307400341c6541000c140c503031268002100d0404e4017070404d0006240700314040150610300200c50641158003d2440c43c00f94480c0036071040d40c2840104040d6003e5080402c40f40307000400300c2c0c141d07540903140d181001400b00003000030f603142900714404880d0900e0903035541c00c1c09000107420f0b0910340c0c110056330006241c1110181e24a03900c0052841c1a503195118801800c5105469078201505c4600c00f580160080b403002074440d000512001d003000380700041460000c6c2c1c107144100003c001100d4a0741c0f00002e1402d10940c200001d40040804a0340324a0001446164603180e0101504110089031200300c241140d5002c1c030034200b20b0115000003041030b0030b0047c1c0002d015140a40d403a1101906040c804a081031002c40c62602c201d5010740c4800060b480c00d0041ca03c0766004103030205100d556a00320203182442400250300501c0c40d02c00 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 237682428 1250 237681178 237681239
    0x3070c0e06090705070c09020a020a06050a091218090b0d14071403070513050a0204080a08121506032a0a0e09010e0601020d080907030822050301060f09050a06 70
    0x38006070302070140c9520b0902c2018030200c1c0001e81c146c14030340259154100c0240c1c07202e5071030700b042e0b00d029405032005100c17600303080411000ca155a070145a60a018105e051a000342601e4241da83e4020422805030940400c0c030140b2210800360006134001a010b0400d5142d8502520b40c460b061403080b8402260340c12421080207804049500d07148207400440c040d01c1d0091038040040c08948440140c10602038031540060740c00e40f41541500c004150a030251042a40b4900e0800c891750f00080c851180c0700c40c0d410109450100c44980319046950191607140b858a1300c403401940001071b04001160f03180b070300d10410955045c000252074008810389405041001400130800b203410160003200c01e51105508228990f070303000401c080f1039034090074030448a444280340e840c10310095810142c200100000c1c0201452420040042c0f0754100c0310001100b203403240304140c02c2e00c105218030704080b40244c0060242c24925482207401070418071000808030342d9004084a0031401800100c0b01541c00300c0c = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 237683678 1250 237682428 237682441
    0x804060f0915090909060221220f0809030106091109041a2805100c060b0904020901092301080a050715170c07141e030c1203070203070c0e 61
    0x503000001d031140403503216140511401c003c00d64041841a89801c5440701c0ca08800e0100071390403a9154524169070184a040c1c5402d401c041410036900e61070124010b010001d1046000102c040c0c180d940140c2054001c070040d1645010381c2c100e00c924a905541c3e80200044d4004c0c00d05c105102080000d103900e4681407003600b00000c0341c410904034542401c0c60b07090902d0039a280000d40c2140c00d0000034807002001c000003000034408141c0c00031500840e40c0381d000030010380c00824240c50244200406e11146100c1801c1c0b0488002c25240250040101c00050100c2d8015802003160843c02214803002d4401c4078180706c090310b00a91204a483c1c0006004100307000c001c2c450701014006009011140d9234603d48010b200039035488242c0754440800700031651625100303085868164022480c0d0300c03102029004242c40e00b90901301c504010304e00c1c02021380309450200648040c010b401003c0c004045030540c003038000350302c001d09540c21030008109800004030681007103000b0f4880b40c603110130b5510307060707 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 237684928 1250 237683678 237683687
    0x613060807020c04050405032215020109020f030c010e010807030b0301140916060e1003062d05031b10200a05010b010e030c0f0a170c0a0501051204030e0105070804060f 74
    0x62403064011070805c010040410800400c803440c80c5d03040d0301070f0402c82c20000341c1a146202d807500540c1c24001c00c207240c990034030f90542204501600032a58100c3d240060001c1540d1122003a02c0d00d80482c1c20030703002005030341c000c44680740c1c032480b941000f00d0b910380408002400c40e0500fa8082915044030b40a101d007220003081084581e11304441420085407e08502501442d1076150b40d501c101c8401c00031150302c511070b0b041a4020302c94000005540fa142004c2402e20f810b0201c0246003040d02c80c4000101468002070b2151003513110f00851030b00014900c1070000c01294005048107200f0802c40d030703518603540e8446028554481c0c401405040010f49842429949444c0505040009035249980203070b03404a101c00c0c1c500e4046928014401036080802e0a08820390700108150355146d90703503100c9030310100e01039403070642c100e400d400841d44440041d1400e005400b207280d001010180014000380c081c0741400da848030141441420049070760380d5903400760700a4008070000340c00380b40d5aa503800e401 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 237686178 1250 237684928 237684943
    0x3300b01050a1b0305070803090c121c030b03070302060319050603010b10120e0f01140108070b0415030905060c04090e06010810020906040305030a020a0b010603090503030a0902061306080702 84
    0x3480d01c2442c0c0b924032070005010884503001515074455080c9601e04240c000c504640c400b5910600301a00d910b0010344240e144d407060300c8158003801c8801414140c0c100042060301e16141c480071082c103150b05c1e400040303000700075440949425101d95000400907a0f00c8101a5100b6000e80d000d200424940f0020300d01610400340405000343e0401160039100d59545500c03c0303519943d85400a00700c041c60f41d03450050034520100455a000d810700042c2031401c190007418088400b040082c4560340d840030615900d41c0144036800300d40c082804280305c40451140303404c801101629000c00c03148241c2c0c03a09410310005443c0320000400004042103885400d002d82c16500204030060b0440f585400c07501074454010100ca41200c0b07500045801085d83c03100141c40155822800712512411880f4001e03581e916198419907481d040c820001824078401d00640c400c3c3c1c2e5104010b9410340d102e00051001805102d9400ca82c17100c014003c00105484100f02c4000030300c203e40c0e410303045003440c0002a0510380e0 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 237687428 1250 237686178 237686201
    0x140d02042c0102040f06051c060f2606010b071a070507060501090e0606130e030c030a0201060e0c0720060c010f0e0f0616051c0605041107020108130330 67
    0x50000304178183d00c0d24040b2044074294207003107548424140c0303819101030b118211846040d2a00002058103940300442d4000e540c50054814142d01c1d040d05220a0035803140700d802200c0e44144014804661140d01402e80d07540b0030302078005550003421074120403c000301d031b0803400503d010402d1004e1142e1400340b0380c01400d44810420106000c41442a11280001d0505010f1440d000c000c1481c03154a0b44401c810013491001c1d2502c3da000000e0503501d0303904c50142d640041d803c0c004041106540c600e00540180f615400d110314001080e0f07208010118500c401300714050701d842c0723a05440c0d22800001e240542103807000095042d443c022030822a2442c4030702c007520340d11446034000340076000107100383c00020880c030070b00300c01e150540c080354540308211200050310003004a011b101589904450b043e40c10846041c40039520a1107042c101d40a800e40180c00120504040381c21101440b180009103406440e0056100128001c0400c0d2501e20aa002826081701c06194407815800d20500b102d484 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 237688678 1250 237687428 237687431
    0x90911010c0515060f030304061e0207150f050904050a0c0305010602160306020306040f0c1805090c04090203060f04150608060a030503030408210106080702060709080304140d02042c01 81
    0x180035156269103d804901c5100100b032100046050703983da007444e21032000001001c50f5a10383d1580401000e081d01c40e086d8500483c10005c040c840d43e400460410b00740c80d08400d09011140c4402c0e070440703000c034030341c0e40c01030a00c2000c200c034400340d450300e020341403250380e01c030300c1c003040303614041c00001c0031544d0507070101d02190404900e1103680c400f083c425600320b9404c0036015031a0b84031003002a000b002c0c04029804e400380f80180e4490156000070703814103880c030761160080d09190f6031414051555002c0701c90001081c01080306002c04140e640c0a9900460060040b0100591203008070f411107207000d41d040c0d901c1c1170060040141d40e5100941b81d510000640300003082614559910b540d900010708002d0141d4001f00d580400c3e12415108002070080340702c0710340081e50750f0782005041c2c02400e035018401801400d000407a000d024100d02c5003150940d00096190034030303015541c0c0003c4a030703a22141c1c1c030140d291160405a6154003580d81c090b903101850002130400c0341200070040c05103030404c00069 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 237689928 1250 237688678 237688697
    0x70b0a110c0603060415090216050d08040809011d1801150504030f030f0528120203060a0302040c050706020d050105091b030f130803040302010c2a12020304030c09091101 75
    0x162140c2e01529000b100035107011030002d4648019481484660704215805440442c8a000005140513401005402242074a40c1d50800c0002111140f60445000e444800304010340c244139403042841e0042c43c00d42d50350b04403904001900240f9040c2034061014608042900140b01900d814680d0f6a00d0007080c0c10800e15103440c1d691004035004803590003405000b00c41c2c1000451601a20841b440200c0c0d03d40d130f120090048801d485d041305240c2e24100001a01001041c00108151003202d0103840f00402402686255608000c09441681403480400100f0310100380015101d001404240000709008907040d0305003c02e00049410003003030b01c002c0c1d50401008401e243c09850403640c0020014008020b40c1d680c88040c1407806958030401010120000308020506a065000c00f600509035039a80400311080440001d8584240450b20b50110603261045c0c00602da03640102d48450f51401179a00b0142e40c1d0b01d560500c1d2415520004600da00c44080c442041604901700b400c1d0807090902a540 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 237691178 1250 237689928 237689953
    0x1050901060f090e19030f02210316030e1504051525090b04140310230603120c0708070816060f0e0406060c1a0103082505070b0a11 58
    0x110542c9110300c14145656441d160300002c1c06011010010080e8000b030840b502c0d803458002d00c00e180b90012040140140c5100c010ba02040d40e006d80d0503130142005560442d22400c01c9000c60130ba02d0303600301c001d042d42c030042000b00190034041496040d41102880401d032a0900b0f1841c01d04030348120005104410508110604210301a058000240031100003100500c05100f520403200682124121071800b143c005021108408500c0a10f0019000d17500550080e6041200303617403150b500348480358502e514010241601c00b55141e4841001403c9034100c1d1030f80c10511035540d01003645404039030842442440b44040c104041360080035140024000c004a000030340c2241041c6002d004204a011004e40c010144501222081c43c1d6004000300300c11681c5600150080c003080c10704032035414030803014410181c0c120707191034101d07500160600d103000280005034424500120042919100207251000450402c2101e00060084005155640c0d044204041c0c00d0b902c65204104141d0b101d07412003041c = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 237692428 1250 237691178 237691199
    0x632040203090a0b100f120618050705040c121d150601120509100e010e0118020f04020708070f0803040b090120030c07080c0705040b030a0302060c07022209050105090106 75
    0x26081d801c000010141e4507464081c81500d40340d0350045115600c21840442c500e10035522081c1f083e0700c44c510811010740c510814490070f181c060000341264000402c01c0142d8142900310240c034402c1d5142043c003202d6655018000c49800070048191915002c498407020001080b07200310210b0f580c0d160321214605000005c090300c81e4103140f01485615103010401c1544200504581c10003401c4041c84410300404d0300034000e00702c02014500c03940c20711006c00717100040f02c201036000c0d03a00031f80380d1518a185070084c031002e0f50240d1002c071104801040300e4004641c0306c017405401c8501c200300ca903580b41000c0c00c20500d0320101800280702a403505641060b400441c0401d500d084081103002034407941c0d00c181501c441d001304400039240c11b000013032410380a00c0228001c020340c0d4007110708021070a038450038181e840f008900000c025034001c81c003065441001002520a4510081800001480d103235285495207008019003c80b00380c03980a564104182070051980c8043c5072802004924075080d01500d = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 237693678 1250 237692428 237692443
    0x20c0c031b04270506060a0b040303080f07020a08280813020d030201110c24041203110d0f051503060c0702010804020303160305030a0f1802010f03063204020309 71
    0x18031860341c899500c84112906840511240c00040c040d40c3c100e4a0b60600c035444034402c0b218680314000039030010400b04050303804c3d102a0780d0503a0300e008a940d02c0b40a00024814045d1802c01580b20707900c440e13000529008000c0118914a02c445806102244041340c1c012034107801490a200d03101081006035403030714002c003840030340460b4200c040c411a800c00340c0c010000c5540d0044018000940106500c030000b4102d0400080d0b1030f000c0d070701035010240c2201c00c04c400382c2d0008d004607010800041c0380c81c826004250b903400c103080303514170701250542a1001c40d0200c024032070405440e4010810b000d040056600c04940703055010306200d01e02200102d8461154180003410b002c4000049001d64908109880f13032a030108580141445580c20090210707042211169002802d103000c050408100d030003156144564074500610000322a40103443c481c0801c4e04203020035036645d6000503004549040601c1003214009810000c08258041c0c042d45034030300c0c1c03480d40a58010014000d5414002030441c = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 237694928 1250 237693678 237693733
    0x307050a1d0405010b1c0c0905010819140901050a090302030901210504051c020c0a06080403031b030b0310020708030402150705060c09120606010c14150a020c0c03 72
    0x30349440c221026480501d40e03954003442e00700d4941030002c929000f030326008000e00740224140209134420b0404400540b4a40c80c035041c001580c01c18100800c1d4092001150014900720310700c1d145400717181c0158121307aa0805040404844c010612510341c40a114290700300c0c4000c0c80a000c5000d07540c4010355a8403580d0640c904100b00446011708000048424101c1c8082021003800b0b00d0815040c2142d403100380c2070b040000318a802503000d072240d0000a1501c1c1c00d0340080e02030301c101d619054042d1205032004200b601496106c0c52a0140000604c0c1124079400460320002144804030080c186081c1c03082c010404c07418410001c41000c11a5001581ea02590481e0b05c00030381e02240381d00702818001d201d8004c01c030b0300c03441050180c201042009003042c00c800751100810202c400d000e080d40d540007650080d0101e02d0300c0214501203000081045505090307182110090080550b82c1d0038403040486115221507408551501d6901050003000890001100105401815002c04803007503024003a14 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 237696178 1250 237694928 237694937
    0x8030a02090a0b04050406060810181d160b070803011502010e03210a020a051204020301020c0f0c040c0801051c0203120a12050105032a03120c0f120307050a 69
    0x10140861a01256540341c005014650034503035450100c40f42d50803a0143e580b2660910701d010800610404620303220341644148460f0342c0303141100c03040d90403555510307010059459503001605070f40c6945e440101c0c8078401004004201c0003d0a00b46c0d24600754000c80c500e107000b005103030040703242a010b4070306440300b0700501f591a840e4244282d00600101000300e070300c3d00000c5034051030102c03076520001e0741e07000c40c80d500300d00c981d201c5820004902c0343c03602c002c020541c1030100340854080c003484164000d202800040c03418400601c501d2801e065030300503090303940c41b0041003001b40c01d00e070107075a800003452b04101c203095060070300007110300902901c507900b84c1130741e1160101596820061f01c2c4020031228950f40c1d03244c41481c0000d00c001080c400b4440c02500f000000200e030f080c0050110041045450052095007a140135100c0e0301403802030303eaa2602c54426003014140d0420000c2846000c140020020440880c11150801e031005144001c3c1c42c500b841003000c0540c0250813100b207100c142c0341 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 237697428 1250 237696178 237696181
    0x251404031e0b0903030a05011e0b031e0a020c010b0d031e170106050711011707120e0105130b010f03050d050f0d0c0306080c0a050a0920030708011508090a0803 70
    0x1c01c031811100116001c0d02d0060325009100301d00c0804030007540549650300c0c4c140005c1c1c1e01d40103c0d100c16402c1078203828040507400d20810940380c84070081c64002c81080300c0244039000c0f01440c005042c00554031185e4040d03002400c84c802050074840c123441c11a01b0b407548040029152405403c3e090200700078098002d02e03d5039298800c0c8503010302102002c004010510702e5845245c0140b882d080b4035000c4074064032840481e2580d40c050704d448000640d40700b10342d00343c40e9142e0314211239007007074200181003407030319030a030b24403d07000038000c052041000c0c0c940311f00d500d900f41c14199105041a402100c440c2908001407006c42d42c041240852206a800c095543d51246c0840781028030070b58220038170760303890310610170035040e40b680095084810710b0048400c0c02041c007003000701c10308051090f03035401041c0d11030401100d00a600540c9002c50300c0350310b40c21008030949030050103510455090300090b0740c800040c0042c151062605403c0c810510f0441014501820030660300d03441032402501c000d10200 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 237698678 1250 237697428 237697463
    0x50f0a0e070507050d0201090b01090905060105060a020c0a0e0718062a1202060601080108010b0d021212030703050618010302030307060504060b03072408070507030807030b060325140403 82
    0x301d8408903408005c6421041031003070004c2c020403880c8412100c26801100000e0800c6203400749116543d001005004e050b440d040030010705911454440c2d06500030a0345c6a00c181d81c4079800240148224501c201c1146030010b40104403030030280c0b0124096414410a00c080d541c41081620740c0803008030310030243c80007480062990701f81744074020107030f40b06c1840251415502040e03503801384400380c0f00d02000766224040c11f03082e074015400313003504890306850500c00751404101001c00ca00741c2209032a041c0462292030300d159032040318400c0209488a043c00202d0401c048031203002c403a03420071700f16654107650000e0340313a11882c40302034026503c0e2804541800f9480d4815140f400300101120307035480c2d40d00500e40c0c2c040325084640c0340d0302021030003881c10140241281e610401542d41e48500d08682982c041c0d0b003000024152a08250f0340d4036122800d5111000198043c0710310f00441d070080018500c0160414110001c44410410071190310400c01c02a80d060b01c0a8a40c0718011070f14404205 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 237699928 1250 237698678 237698687
    0xf0821131206091202011b08090c011b06020f0705100c0507112110050a0516050d060902031003060b0d1e1106030403090e0c09090a0b120a03020102090406050f0a0e07 73
    0x5040504092103041c004413006405600011119140c1d070010700307400f01d00714000d44040f4402c60b0441c40300d42000840c0c065a62041034911445050401486480caa06440e0307d0101d130080444041c00c44000280741041c4001080307949240042c3d0075080c45903040002c0010080c0c010958010303c54101e0165016899071440c22060310388030040c2042d0b02d8080c5034000960349840b4041c3c000342291a10010440030794060040600c20b04d5003c15500828501d107004503050340c4000511070a039a554007010400050034001540180d040f00e08409116056041c184119028900c0651081d56074848910014480c840504281542010b4134200c07503200d42409180b01c0c00101051b5400301d40042004101a000003041c1d090b00d40d0b0f24255689940c036005e04415901c1100d5003140e000f042c003000240c3d1800c250f0400e8402500142040816102114040b40303070142c6a20700301c016035004200343e000303802c0922a4100801c001c5807180d054800b40341c085000002e5a000b2621a228140d0002e54070f180079 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 237701178 1250 237699928 237699941
    0x40b100b090603130b09010c110a05030a05030402030a0f1b0602030a02060402060a0c0b0c04170a030e0618220c020307150504050304050d06270308070e0a0f0821131206 74
    0x1c810701711030b40341c50802c040c000c080d04102e000214140e4220000c2124000070001c001d03d510078021881c3c11900c01f0700392603503000244226031520943c2100070000d07a24000c4c400d0305510a04922062401480c904003038080b040d08610115402880020000c542c00501d403a009034040d40c2a940d83d402c41d02e0121516003c84801801c0c0c0d6111200f440a803075280802082140c10041840d4450b084001005440396090744025000400402c8160710360b103040c40050450002d412005c052404440000c500b0091040015030502180c07000e140b4fe02070203500403040740000d50300c040c52800340c06603900c01c1c082c4079800c1208451640c2d100014100003041007240c0c0a00310080030741caa000c1c1e80d4034003840948000303030781c528020760342546008a91680044280780203616031030719001d0741d031986411031344840e100c441580d101020503000182c191400303c021001d403100c44054a250201107210990800020072125581c08003042000d6200d10200d41b80e00980c2d00781407060044550a042c0b0303002030640b = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 237702428 1250 237701178 237701183
    0x90f0102042310050f0c100c0806030706082a0c010617100203010e0c0304112716090314030d021620150c19050105040b100b09060313 59
    0x3000a002c19000446000c1804400414000c0c0031419501d00c24003e1140c08000c41d0408035005002111580044074064462060b902d400c55a5000e5580303c0c003070a490369611081d010440500603c4158107041c01200003601d181d040240c424141541000b03110590b00b44807500000303400728440c0100e42110211800202d011000748407040c1c5582500c01c0315140174200c1c2d00c15200d03403000c140c015100c80c000d0300e04031004002c01c0c5c0000d0380e0304080b8071340b61f41c0020000c682e203003803101001c81281c1e03c0020502ca2107000840c040c0c030304050400a0743d074031003010b000407111041625860300900e500001000a40b60f20191000c02040303a0304600f491802240714081d1030900200e8880b00400070340ba68620070a00400451030b00c5e081100c1d14102c05405521003641207080f0804201540c440640100030760b9070900111010b0345404960fa600406c01c1c03100c1124180d46950500080c0020f041c1c1840d0001d00c0210100d518615208940c0306c01c1c42034840090048a002c40040d521443d2464070000c1d4a4 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 237703678 1250 237702428 237702431
    0x61003020c0708032205030703061e15080111070b0c0a1103030109020a0e09060a17070b03090703030201050916050d02061612080c07020604090213080706030203010305061806040308090f01 83
    0xd0303c03015815120380117082459a108681d08801c2800d20604117104100d0303401030f01800e8610308545a10000c0c000003042c1c0d4021b444000b0140c0d008000d180720312292000a240700408141c00d014601e0b080d98840010911100001e201150209250704a5180c2001d00384c0f40031555080c0441301030311600040d80200c006400003000001d0841181c0d00184810001651a00014044a0204900b008081d2205030300410404400e200103e0301c42413610348003403008100ea900603a2401c060000794030480d510812600880001c000301038090280f20381041000c4090100ba521240b4840f40c0403800344555407081c14001c5095056445903401c8070782d0301c80d004005600c07003051800e05114104845000d140002c034004009100c00784020291740c503869008000c00d140a2811080c0c0303000e50040070f401c08007010484800100034a0800521004041c0c64030050303281d40c17450038924140740b03004107a080081000d841450442201084450707010b980b500301a007090301c0e680784092070424040108901507 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 237704928 1250 237703678 237703693
    0xc0d090c060e1f020312070201020903010608100f02070f120909090303050601080f06032d07061220030703020c0c03010e0705031c0f110a0807110f0d0308061003020c 73
    0x590340722040c0000000241d035403c2030303036039200c24810603c2114000c90380160414000c030200c6215080a094000350f5620002d800e002c190f40000e401c5a0080d0f128140607400f040c03080d05203c009002c0e420411840c240114100240354540f01031240f034a010040810207045680090030f0b00922880c00a80703126401040010501d250240060805660503030111341044005401d4000e600c080610078000a405002414010080b56200c07403009032a16010805580c00001128002c018260080110b0b6490049003e060107501d42111058003038841110024410031040c0c80601048035000100d0307280041c0d41da90706801450600d80401801e59040d4200004042d00b20b10002e1003074241c0c1c0c411410b40310ac009030484006603001d100b00080f00844d000c2c0244174501802460a400310002c01c0c0d00340d030300c848480c3e694990b45611a80c411030b45c00d400e070000840c80d82050714000074640002e031382c0c4000c1c10400791005000d075500101010b200e1030b41c26408a64841c8260180c90f03182c5600401c65112 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 237706178 1250 237704928 237704939
    0x40e010b0307270501060e09062202090d0b0702010c09090204050a03170d1d010e060405060a0c170115030e0a0209191508070302010201180c05102703050f010e060c0d090c 75
    0xa6407d07900380d202d5034170f00000c51058a800e1004010202c103104095907420030f1a104d180294006100c81c0b540203000708050004500104415403064005600009801c0c169400140909103940c00940a040c4140420300017178569042400550760807030750303140c103c0521142d421824428010101d0301c0c04d05081c2c08040340300088502c1c01d540200c40c0c0c002c2c40002922404150364110445018040b9400702001c50030400195101d0070036036085240200ac10018500507052070a4281d01500c042000e000d403455500d5418850710410003040b8018107044011034000822103900549041c5200c0d1595200c40c065481d00d1788160440c02d43c4640d81c004940d520041c091300d48502d84402c0e4050f500380b00a65032494032450850345802d07030008107901014105810b204010b9404c801c20300c2840382c1040d4101d0b00c9186200070100201a035101d14800d18218501300d8140751141403008400d1303042c40039000c16044040f400d40d41c080710107052941c681100c559000003402c0048005007020b058440080f62 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 237707428 1250 237706178 237706187
    0x18110d090507050a0503031804020c12120a05010f1203030e10090c0f120503030a020906090a15140307050a0c1e050a0327030305090310060f0302040e010b030727050106 74
    0xf1502c086485030000784d554001c3c1070301c030710620ba440001e0340040035407842d040c40e0070340c040d001005040086402081c10411a84295402142c001c29440e400e1810000c60104034040e803405410030010100500c1d140441c030034001922580c004003451b486006c0d90540e8001040340009440300d00405000c0d44503142041d0503020041d015080c6e8100190401040d091441304031510f54550100085145aa50200c440020740003031802c1c95100340200b244203101e50398800100f002c3c20302c113001420603402c84800544021103800030381890007018010000a6504a02555404001414090b03400e43c82850210070151084580c400041c003040881410b0100001700d117000c00e8440c0e101c000050001c2009018000c0c208000d103c01c1c0050040706200092141019000340c9001070111076100703010300a09000c2d01c0e41600800d5414440060400c03c0d841c0a0040d245004030500c003c01900300d0450200b911048140100703019490301820016010b80595011840c01c03051004c1042a035840d15002030 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 237708678 1250 237707428 237707443
    0x9080406030e0c0904081e0f0301030c0e060d110103090c03020a170f0a0c03030c020d06091214031b0a0c080c030a09060509030c13020c011a0a0f18110d0905 69
    0x94582c8104010b100f814207106103528051038001d401c040c200191581010303980803c01c1002c001d008418450056040d11510185010f1842861050006d9090400d5290038030f43c01000c8521800c2c0b0403001c2004a0098155403214034020328001c1484025801c000002c03400f543e0000f034000c40c1301180000d20510003c440d4800c2d054400c1529241c0900c8440d259456001440241c8000c9500c0c90801c0002d028500e803202081c03015000e008455101d0700c44000300c4034011010740b09585684900c0101e82d50200d4082c05d04040001c42600714181600a030600740d0301c001c11b00d800200002074501009000c0c0c460030f11032039446100079940d880c8825100781c483e080381d1170502c0802c109101c0850003034000c00079600840e5014009101d06018007040001100800700c161803215030801c2010762212003806034401c083c03160100324680b042a8401c2c0511001960320402c40c18180d65410300500541e0100d028003820f14110104861461081e004564840d961410740000d05c1d09150004104001c114903 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 237709928 1250 237708678 237708701
    0x403020a060c1a060406050d03030b0103050105011115060301140406090317010308030f040303060503030706021b1501060c020609040624030c200304050402211006080402060a030908040603 83
    0x40c002a6100c4090302c003903402410042641007490104291003105003559503011000500100d003503552940450b00d0141c0026040d40000c0d2a241c0081565826019990050030b080c40d02a29180801400c5510b9003112801500407000b1100407812a513030035006004e054100b13481ca001c0d241424502040184040d007401c80c0418810705070b43c0300c202649c58105040b40d800101c000d1840e621070400d040e00d21b50052040b014036503608004180303918108007800ca5144103640c01030b13640d8a401e500c004107840c9a40806160741c44112880c01c52400c03d8420740c1100d0290030091821000b0748001101801840f11064105180503000291a0009000100400c00344a45100814020042201510340f15060720300800c0208840b22481c00131070740e0b40b200e81d100b000190303130501da00e80d0002000d070380c4014200c035042f0140500303034410000c00141c0aa0001c142131202a8403e1400d003010301030410051000e403042601050300320040303020740c014004040d404246650b60326151140a8001e1108a850 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 237711178 1250 237709928 237709939
    0x3070306080c092701240b131a0c010212011d151005070501050f06010212040e010302041d0609010c0e12030d09081207020d1106040c1a040317040302 66
    0x40c0c06101141c4010352a41c003030030300b0f002d9a50303413400040303402c00482141511407401004603110404c28860f41040c414404460f40c02000302d9404180d40040c07030b4212000c02c0b0300030450b020201d0402500c0504903141544002e0341c8002070072030000c280c007030045107802c25400003803004a082602e091b802e042c0d48081c2440c1c0b0080780307030070340c01d1410940490f82801d9102008030201441e2820b00b100c400c03507098074503001e8038060241d5122400d48005032501100c211421050010940e01807200800141603400c14500b071520700204950701c0441880b003c1e0096644000515650207200000b54201c51b00d8002c80d245420304202c591300800f403800f81c000015a16100d102954038100d07032002c0d0412103d100030b5050006851000b0000c01c044136048074000307000c02082060380e101d20750081c070400381d07034014105980ea00031024003112021105401941c1181d4100000145800d6454052b00c0c007140c808880c80010503568045407056420203000c2c403400e00307030010030700c00d02c40c0c001c000307583c42a2034 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 237712428 1250 237711178 237711191
    0x30f0f02040507110604020f0607152304050601060305040c0302040504050c0a0902040617100510091514181302161101030b01080c0a0e10050a020f03090a090e010609050c030703 78
    0xc100d40e00f0041c801d04240c4d80d0000d902207409880c05159403404440f0080c01c6614001d015510742c8030080205040c280140c1d2030700d00400449910014003403000040d421a1001841c2c299180d544412050040300c0034076607100085414804c410005501a682c0500200031a04250920550b01c8801d40d4880740b050010f001d021400c0841802a10201c90035503c1d5451601d07050a1400d4050074003c003600c609a502460006659445540c03011600540362280ba6105080a50392400003619110600a0000004011080d60101c204964141018104500d51013a107200080e0400d00f1102c2c80c140d14034004114001901e600c052030784c01c518800d484c40002007131710500540c291214884070f540401e80c02400500c081e6900002070003860154502540080440400904280081d000d514000340002c180340211f2070b0100041c00240120000550a052405000950b8200075000306941951519002c1003140301c00d402081c00b03407004004c1400a490420141c44840e0421288100020704202 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 237713678 1250 237712428 237712441
    0x240303230a0e010e060904110a030b030106030c180e030a0e030c09040c05011103070203060109020c010b0d0b1303020c040c020a030f080f0c0322150b0105030603071e030f0f020405 79
    0x104480c20181552503881d0b80360541e90040d9860000c1011103904100300700004802c558940c4180050724801c1c00c142512001d200c0402012202c6002520740a6890460240042000040c080086441005640c0441e03e004c1994001404c211441c81c0d000e448046051111150040142d2141010960440301c0400c2030b001000880c40003590091310160340b40304107001c0755204440f0540c0d0400c40c40200c0e45440503d0740842d2404130b09910069000760b0100c0d0202c10720764280034010b01004202c469048210154036880a1144c014000d005000c0c207902442e401c1500a10a100f14000020820017545403520030107900c500c21048110000349090084208090151121900640003005d586805a44007590030b00703664000340510f0b09040c0c146c85409860030b031808244c06020300c07900782c1440c0c00399203c00e81400d8800d9000000c0c1408000d0040040d9601c0015441048400e5148486004c1d00c85d10004454000140c001034010075680500d00144135a003001c4c0109240700b078070200302c0c030355644 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 237714928 1250 237713678 237713747
    0x2062101050f04050f060d03183b0a020306040f0e06010302040606230901030207061d070f060806040c030e0609061902090d0b10121a0c03060d06240303 67
    0xf1903102004c00e05c0d02c4041031540c2403545000c01014481d0810000c468030348c140c0013004c0222640102c90394105c280c1c2d80040110280307000322803002c002c0001c42994101090303451840400901c6401582c2e40071000500a50301c0b60013144035103030208402c100d442020020700303407541c070240400d90080e4206140040c909102d403801c4cc05458044140407807502691708015030603441003607207e0403d6000e00021022442d5032250624aa007420043c1e0401e03401940d03424140b00c600e5000c220013201070a42005034541105807164080000c650001d10f0079035946007036001b003004014600145c0300d0a4104400000006151070182017020441c0d0203141d00c10b001c00040c0d11401b800903400c0311003505d00600203040c801045070420641e05400203040d0b1502c0e01411102c2e103945040c0c805112000525140041c40040142c001485048191441c81c10501080c49500c818800409496841c00c207520b26140070b4602c554404605041100c07025582c0c20000c1c4014840030f01d04c0c4221401c40f5248000306510f = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 237716178 1250 237714928 237714931
    0xa0c1b0f03110a080d080603072403150b040303030510150503070e0901060e060d1407021006090603081603090302030a060b091501140a120c0302070507090203040f060902062101050f0405 82
    0x110061040c1003545c0b000f190740101c09010590144155140032801646504140c10080040c0c0440e00c0c40d64802ca900809607100e02c2007100e85a64048418849000010121020ba0b40c150078003094a48030b0500c00b40110100e41e02107203801c000780069440183d8004025809000182e40340c0c50110016810812603010078850a40400c030011048240342c186440a40000c0032282e400040c0c0c1c07450845612903649007200c540c0016040b89100d0741495125110700e4001c1c152150313007084001d00319607890300380e44501c1002d400340c080886640010148128103081c051940582074454038642e42c80c1200261082c8d07074065200b0808100003680661180b074141c840e480c1c0c140c0d074081007107070722610078030310740c0d028032284400c001030070341d0b02100c12085029038528203420fa80c00503034030251428900d0a08205400c0405542e00400520010440c1106d48a80881d042000014022038910001d5001c0c07242484504c002c0d4419098002c1150404294070b040302c1c01910710192501080f020001100c10 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 237717428 1250 237716178 237716189
    0x8010605090a05130f14010c020f030406050702030304150e040b01020f0d050d1401030c03051507090e070e0d0b01080c03012c12040905070f03110a0c1b0f03110a 71
    0x1007100103180c26409401c243c0d003080c00300201c103242c08150b885a0354640d290401c20380e00210061202c202c03080d024071984441e1811072000c1c0003401c00411459869100ea4401c200c101301010a412056540500c101c3e0000d02004201002090003003c014040000307201c00710340704030321340b0100b07010550000c00c003400e8000c45c41000c1c103003081c1e01c250141e449070800303114075480f40d0381c48134028500341c003c1d02e03168061401078a00e001140e29524241d032070306002605901120614800b40928141c0003406102070f03820080c0014481e0352034160440c0e800510307080c0d86602c522004c6000091280c04141d20341130700d0500040d0f40e01e41300d0784000d260a94a04481000c02c515040040d400200ba0369003c054400c182c0c030003964001400c01a1514a941040c3c01204010f66518148134a040c4c014011506150f19800c0030300541e10220f14100c01405403503424424080130310805020030070300d650f0610007144000991400b00717440f41010740044200340001c4036491818590740a040c5000d5019508444 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 237718678 1250 237717428 237717439
    0x7140303030f04080408071707060207050901061409090c0a030b040b01051e07061e0b030706091412030a0906170405060105130b090a0c08060a2105030919030b0108010605 75
    0x8035000c1c00380c202d00d0070060068903402814000480c40500178401c510061114400c038000ca080f10120301c03400c00074541d1006095601220313003000943c441c4041541101d90500304903118050700c40786800d0a00c1428101a8402d100070108038a203100305003c1c19045038556000c12031080c0030f00c10300c170869090030580303030200c2d100b40100c440340400c040810352011103070391a0a085c0241551104107a849000182404240401030400741070081c0c400c100d0300c20b00c01c0700200001458a500540b811244d409059a000206c2940c1051601d600308949503150a03401101d40e64041d488001b40000301364010100054142c000b10760060307083c414028010390b0000e0142c42030380d103840c040000d80d00d90680e11040b12911031054540983d2030a641612541e9903510219100081c9100140250801000c4038810072000f1001c3c044902610111041c030b0024540340e8817091030b17604065185010301c1c00000e0344285424810001050000e03a030030f040328802d01c100b80050742c8411881b8280d60840c0101c5800c007 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 237719928 1250 237718678 237718681
    0x1e1005010e0604090c09050f09100204060c080309161502010606180b0a12090605010e01050904121b02060f37050703050417010e060903040515091f0c050714030303 72
    0xd03c1e1651102116030710400307412401968500f40b03082650021952442100d020f8003c0040d0802c00344490305d00c44958180071868a400c000d03007c0d02070504080701501d48070000c8006000b40c0c00400140c0c0d1003510120911482d2a9980010031030300c040c01e01500015420130f02d001980a0294000c080c404016031441001c02e800c0400400300c80e00442908010450312100d40300e140005c0c0c2c4111601d081c0501c1d004100d540c10a42140d44000043e03020720b001e030008208100106c2d010b20014003142c41149820b5000c4064030400c054140c1402c0f002a600410000302d103420a12642e008000c3c2854070038030000c40a40d000c80a02e01c005104d0000d00155042841c0000039500c207000902d00c9506c01e0818a09081d01d494070715500b2044c280890001d80e645d0000c40f2080401001070301d0340007004400851401c1e04120225032106a07140c000300c0007000118000c00a075840b440040c82140d20381418007403204140c80010072030b1920f20004d50f1207024030070380802e00440070319030400d000342c0c0030b402145503 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 237721178 1250 237719928 237719941
    0xf07051c06020708040f1205010605010801050918010b1008040b0718060806010311221a070602030a0212090a1103030315130b04050702070f0b040f05061b1e1005010e 73
    0x2c0d501801c0d08551002e0100300100b4100011011500a40004004489400340310320708130b801c40d11980c1015050100d400010003256990000541d841108011404c0c0c0c0c002e24150418094056500d881d64801e0080408400070317a40b140041d44114064850000c0c00e4035250420b56020420540128a500b0326600030702038a03000c0c9144541005040c07400087c500e000c01d2314180d8541090024049103890550305a0841c2000040c9502610120814941a800c1170f02c801100748520580200700f2600480050705070245030b8182d0720243c4203400365811034600f0f0017040742c4641d04000100c80e1401d54281540c441c0c10b002060364494440114100382032035482c1c0030082800283c0442ca01c4031600c811001e034640d00c1d42c0c00f41500590643d00241092410550150420403030b5401040301c2c40014030082144c0101c242d844c0044500076180680e403191002e4542c04c951031101e4082070144503d52820300310400306500070035203015080607520070349045032090040d00d8080c41481c400e1031140d000300e001d = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 237722428 1250 237721178 237721181
    0xb07050d1d0316030c0218040b240d03050d1803020d020d050a110c0a03080310091e020f0c0313090b0603040308072106080a06060b07080a030911030f0f07051c06 71
    0x43d824002c0c01c11091610341e5a00084a5450b080d0b00c03003040020350010b04c810070040c0d103c021b401a004030412002000128090101101c015020a11462149940c01c007070601882c21682d001d40b1030101403207000b04000d45a10314010075481100141700b4212034040f0306201003840001c40c0c099688131454000c2007001110120b9108646464500410050880c02c0d60b03406030304001180719184042d12451b041b00281c4460070a580280301060800801150100070a551495101000900161107004002010000b80211003400846110008a07401030720504611350b422039007030010501c100402402440702500069800502040d4414042039800b40918468070380303c5550311580c0710a1943c006040c080d07031030380d5004000d103030005a40c020a01c0120302910001d044010601490301d2003681d14a40c69108039100c47c820556205014410000044841c64028900408407407100c080c0c104299181c0034110010042c030b11464100182d0350401c15244650703078410110f40705000145444d40310 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 237723678 1250 237722428 237722467
    0x15050117040b0412050d1a010e0d080d1a030a141209130906020f0412110105040e010b0f0d02040602150a0b010e19090603031809140a15030b07050d1d03 67
    0xc00b1704c0303000c2c80a2404100948280c0552461848400e00080d060400161126000c006e0441c084d45540b0030740d40218020303a08803400000c5614000030404a0703554030300c809000019055030701d806000d40036000d001d0b20101d50181c0b20a80300a440d03028001c00700000706442058107558220322010f1540c0d44150740396100c1c0c0203ca02a10000d45846910b214010303607544580c010b90110003404490780c3c140075084440320246903003070030101d01d0036003021040548804144105c0c0c42d01c890008104040d403000303800b1342e408081180300035905e90b5200ca902940350000c0c2c07460800020030350000210180d106008800c00010306031108102034400c04140301001280388401000c903840824001f40f100e9507031080d1001140255200142d07003800541040e040595540421800d03810702110122407200170b041c080d000000d50074002655807059100349038103087c6900182444c1980b07400c01240d182c00000500000041c040d040014088010f40394848501007070992543d07600520100901100020081 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 237724928 1250 237723678 237723713
    0x130c030b04050c040305010501080613020d03050705060c040905100b1e04030b0f040b150312030a0f0c05030a060806150103150b16021008060102060403081915050117040b04 76
    0x8551a103500e404641920340a503001403c00000007820010f200080c89030b903024240c0200600084e040000403002c0d200c034400400392050404401c0f1a0405009001b21514180d1040542c1d02a2510304038086558000d4407131003151505100000781e0100d14407014800343d4454407001410410324001d5074130420060f070381880700604100404004607000e295003034420200d0f0100890545080d1170880700140010305204541c00c1520941e9110359008200424020080803160f6101e83d14000c448028180c0b00c004901c8484c0303807091841405030702c18000c500c6000c0d450740501000350354200c20390b5100e5040700e260320108001c008a21181d03100742c00c0161001381c81e45146c00d8868071441c60134016481040c8219142220f40554821418a99045c801c0c0a01d9410074090340d280800002c0d480b10f500410040c2007060810005000303020280c0030307071032845903c07030100040440c0062054500b181405103030b000c1551400290740c101c411076021481154425182602a01d40e070b900c900c0700036485c50b0b10 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 237726178 1250 237724928 237724931
    0x61905090f0a0803032a04061d060309010902100203130b0f0f0a020a03030f090506191803090e220311030f0f030a050105011b030c020d020a1203020c030c130c03 71
    0x203500642e507200c07400c101400c40c0c1e03405542d690414035100031002c0100c00300041719446d41081441c6070f10924094800315030035402d00f2900103049a0721101c00348140440140e0001010084c000388980551103030b00720501c01d559202ca4001d02e0901680c0c0c0780980c4c0c544494002c80980e052040b45070690140c4550f0001a0345241803030b4440701005040d4010402000050f030010b0400410306034035002c0c800081485800801c40660708e5229251984401040c8910f00e10600c10b8280400581da807108618403a411f0303c11840300304519000300300d242c040c0b180b21902c080182c04078580180e0031a0078007a1041d20a60010f880d00c0c142ea042d0750410403510910100d0005004100c4203001d41d000500941000070007682d542d280041c98003040b1a41078100e14100300500e80c0007408484603c0a10300b01c0d603090b0824400e00c20300c40c400100031200b0f020000750813035100a0005100c81107034041c44540740c0300741c081c0d406151420003810b580780076500c2d2155200320b640711041101c080541c00b0b0314810b003e13442c0 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 237727428 1250 237726178 237726199
    0x180f030c03070e0703150f050603070903050115030302010b04051003030810180903120e1b030715051306020a02150f0d0e070503150103020604050933090606190509 72
    0x203030802405620030b60103c04090100220513525108650311181c284841c40111801c150a00c80c201c0301501419001e91800801b1444541c0107040c2540196030100090045500c00390030001d0303070399031403100303c015600b0021540300741d103054001d0a10491001c4001c00101e85152030407201864040c1890b407000c0c1040b400421030b203c02589001e480340d800c0c0000f0400c0d42061034014408801204c4152a0500c1e148040e001000c01048500b00040007601860809540200090401909501c40c2c015012302010121255801102400d00039202c0c610141200c0d07541c1c401640c0300e10f03171400c0082d880305051000d40030003217000010b01071480700e0081040c2171808414800c4c0c2190f5006040d0b040e0b40c1d00c43d100412440c501000f501c880268442c00440c95545140c2c042801b501840c02514458030610700000c140d80300c9003861207080811010710b103e0003050180032030f51490140940c1c6004541c004006103680c2827420841e86000080440358401c0c6091180c1200c55820031190b807a4440240ca1 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 237728678 1250 237727428 237727453
    0xb07020f06070605010617060415050405070909050405060403030506190306020a110f1e0c130c0e0303070b0a0605100c060902150a050c010c0c03020709110412051b010203180f03 78
    0x844e003406454503403608039100c0300360104035450f003800510180c030550070880c1003607407000c0c1148080100e540c155408039003030f29500800c0d513490009800c01c0f06171074601400c02050220000f50240207a020b514104190348410041c01000c40b4624000103601036425400c00000c5c035140e00074074404030701d45007400050709449411414940004c0108c0e220740d1140712100d0102200c0000c2078072008a8070001e0a20b580300304003040450102d82d00c1e0044255480c0720320444103016140c60101c3c0036004081d20303a2015286012008418240c42d000308a0345405000318480c2812001106c10504a4031400c940c000756035036440185c0700c4040100d0308440c02c01c2e0020080129030780680102c00f25515030303944514040c490142101c0714800c0e40c1d42000715200c2910b0119802080c0b031700c2500e5142e240881c000c101c41503072000d54415903010001e1410340b401d03200184280401d07642c040d41035052441484000c02d03001280d40e8002c0384000d08031394443d284850010f14100908031510078014054801c80304449 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 237729928 1250 237728678 237728681
    0x190605041208090d060b1305151c170c0d0801030c0e130803010801090b151815030303010308070201180f18110f0c0609060f07033c06050a0b07020f060706 68
    0x250b001c99130b170f640303404200c021464240c05290400100c104204014075100140e42d4100b0303489070040c1c3c06550a0143c030300160700c40740c0d04003002c140c2003805441c0c1102c90210b80c0c1c0031580040041c01260086c80802c61074948039001050480350407000341d80c445e605003c0d510840707240141020034841101002c110000d2802c802650082200300d00004044105040009410304001c20411009010dd524054a070f81c03000c001810507100d69501c2a080c0d03482c3c201d031000b103c4000004991500c03022000008200d6454000c003225032003a030700c00500c2c0001c100d0301c0602544600403840c08007194181405200c0c040d440040032015034900100d19030b810403082d8007140c2c0c001c039903100302c0c0c03000015004c035048001c100300d91300a42c10900500c1546800c04410641c034101800c0380c42090b89801e04086030320a000c42d07070707400000c02420350020b40d49110942d4090340202d2085d403060606000307002800e4a0b04800c0617040314603001ca4240340c4000c42c8d082207990140050b10316807054041c0441070115000d03 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 237731178 1250 237729928 237729949
    0x20c10050c0417061003030305130b0114040e150105102a06060b0a05030703090c030203061e0c0a02100b03120c07140d02130506120f03030619060504120809 69
    0x4030841079595074104001c0451441d0121414482980030005110007008003040f01c13800c80b1780500d400540e0751a00403489405001881c4060325201007039001003a40c0040401e004800e04048608024491800720b080c0d80380d810202003d003107031a002c001040305082490364180322202e140303400a03280310400f10080d0000c0c032281c2c841032049003983e60002004118071905015100700c0d0b040030f0400b0440b8500900e82d101c020500307001c01d80c0342c1d04a842002210001c07030b0061580107041d01d03100d25000c04140704608010416628230a080008203611340b44007002c0f188401e2055014087c901c0c0e0400080d4044c0c184200041d8141c4a00001020114200d4001c1c0c1101504540030384081c13450f211070692401d0700030700c419218000c0b100071040140c0e2080c04940c002005040d0102d029514000043c4000159040f0301002d03010b2842d052001d10400b00046101c2c050403500108081c1a600c03440050b84054000d0742c000c248108000c2c00462007034100700360000d10807944585415888804100d02004 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 237732428 1250 237731178 237731191
    0x150e010324150203130314030702090a0c0201060e090a0b0907090507050a020c090f0103060f061e030c0b0301060903080d06030804060c1e0203030315030f07170f0f0d03020c1005 78
    0x401ea881031000030904554295a1880d52000310b040c1100d661045040e0744841c4801445942d0140714019500700520558064540090500c0780919210300000e014065641d83e82006529181002c03c40d680f421682c54090101c0c8401040c100d41d0654840b0700240c400f504800b0180b01c0c148000401d282d00b400703103500c240c150344c1e511a11030509500107841c000c108001035108001401c20440d24034090b00340c07541142d0300310707101091152070f1414010090925800801c03102900d04520002039040340750710f0702260f229100f181102c0380c2da080407a60b036020a0040b540040c0006c0402c03c080352882c0b000d401110a040d01c00500c940c1c4d03a9444d56081e070720560007080465903d9110200f40f04852070110500700b911781504100f06541d90000e901c1e88001402c0030f00c0b50416100711042a03c0400805004c40c10860868011544441403444006e41e84d184494151250184060140c0e1004c03427040412403010300240b001c000059420703000b070340004010340c400b4401c0c0820708009020b5070040c5802042c = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 237733678 1250 237732428 237732491
    0xe030d060f0509091f091505010e160302190f11030c060106080c03100314070902121012030c11150a090f0602012711100e040506010801150e0103 64
    0x602d000248400d85a0003450034905402c00b00b06011020300c4c09400b903034901c58400000545458500d010312200a104240104181c40d01d800860b907041d5114001e40103820158140075071100c400300c1103059205d0f02c401e200c140f00e8a030f840e03c42910701440e11502d0208203030905089050f150100c3c0c0c1e18503005080440d0b0507911a800412085801c43e1078250000c01d008082440c52404004084000c1c0e060301c001082c40950001d91000031000f4030a01001d0000c030360040d03507103e903100c0e425500c80d0b03c285c800400300002d51500040803409000c1c0351004640c99140c0001500e110b40390780c0c00310660f0503400303604046207608121803040404000c1014025903101c10305030b00d0419030b031000c0c5402c894020300305581c9030a4051180061001c3c103c103001c9103a5084800c04009894a43c5148000200c03098010941d500034942c0c1ca5000a109111400c044e00c0c10045d170780d100401141d5501081c0702d0340b0f54140086040c2000380d403142e1000c4401d99018100412074180d4140008010544400d0021416 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 237734928 1250 237733678 237733709
    0x10050a030b1516030201021c090b0108150c0a03020d09030201090b15010504090b03030403170304032d030507020a0c0909030e04140f0a0b09040b0421020d030e030d06 73
    0x940e054461844000000da4100103402000a00c000c00b61159019509891195442c40801c0504c01d404440508005034811007081000f514440042c00c60381208075440c203068400030640d00f00028010051010750a246607440d01c0da462010f0403640b1071004a0704240d000c00c1100148031032405140003c5100f6030002429903202d080240b41078001601620701c03a02850350102d40d9a034004141c0d030039140d40403400039901c000d8000192440c0b08a03400104004155505501510504000b861145000e80c03541c41c0e03204d4200c03c08004184145880c0d8009079041d414444071980310764081e0354441c0613801210400541501d540944072516444600340036107aa0b04102015888100d88002d00340603503003400102022104003c040b10020a0368010259100010705840c50941211140c1c10003d49400698180f50138a0003640c0c0c0b04903802e944405000d280c1c44e0021102400f4440718204c0c55010702a100d4015104034042c0c18511000e4100c5d110600140c2c00f90250b9119801c014800b5040404a8 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 237736178 1250 237734928 237734947
    0xc030604150b0906010e0424090c110118030e030c090f01080c0d080901081003060908030a0612050a11060702040f0f0507050c07060507240902010207120c030b151005 73
    0x54410800c03090f80a150000b040c00000d0b40c00848041c84d20300111000703d18811030469130f140d1440c2072005404050540a8001071540d034607408405001015925140b80c401d0070702038170b402e0f85e15082c10049098144150140030a00c201c6403d060084010140d91004001c4800200003103010344402000c0c0704954010040c0038401c0200400c900c10a440140340c80007030792105500c07801600318a60500a0000015241030740c1507284001441d404101000181000e00309802243c00440310002d50360b20344940860611038503100185040c0c0d10100070404030300d0719605c600300841c0d03200c107035604420300f8441c0c8801a036641c003500c00108200ba00c0084c0c25800e000c282025034030080d2101c0c050120800000d0390321f10011036a0710035265641041c59a81c0442d1400c4602e00000d5038010541c915000070b255842c10003a00903008140c002da0883d1315682d20b6030740809401c18400401410044200ca0800001e01c0c45001d85a220840500c0c49658030035640110b480401d10660000001e50005403c504 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 237737428 1250 237736178 237736181
    0xa0f090606050916091a071205040608132102030f0d0e01051003051504030c02040c030509120406021b0a0807030503130e060a1e08010e2415010f020c03060415 70
    0x3070015901c4480c203420070000340013910071070440c01138454034254650410010007808040312032040d440b008d0003c0c14841980010180e4102e806490001740c080c201154402060900000038103030003c03411550b003034134000034a80b00d450842d542000e500060044500401c1407802518110348201070200b8000c0c81d01c0706150031642c0051070003082c01a03462042c00841c1d0300142248241101c4480350b120b41c0c03540d040c207071988003864000039801420043c1003000d10740d06d604030038000d14050044407040c1c9001600b11030640a203000302c000503400010724100400141030140058a0b0103860300d2030240e1245407583c1072143c3c40d04242e8080d4000109234051a07122240071008004500f042c8110b400c0072070000c0d0303103500b6501c9095000c5081c1c00b88050854240d0044c00003c02904d0020071410104a05030b40e01c8440040c50071100c0b442d030002d001440146d011540303129049241c1204c115482c424010740b8601d201141020441c4281074448803581c40400c01d00e4040c1d0702640d490035a00030140c0e100030 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 237738678 1250 237737428 237737431
    0x60303120a202a06071b0602090415050102060702010b010516021801030b1006021f0203061c05250e0609131403091002012003191a01022806050a0f0906060509 70
    0x3e078141e00a404109030340e607101d41c092030401c0700185c50f44604849428120003a015079061300354001d00c0c1600c000c0c6400940c07040101100c0c001c0e025500140d076103907016401c81e683d40e21014049182000100b444410480740d000078640b004012015a80e0482584654014260401c480e40d94013002481072800b074401c1c00d00000c0c541480284080f8010341801c2100e500200d1303c0e00304454000c4040742c42c0f6943d0820b0124072581d9800510001c00090520985d29825008400d04228000103624a14020942c1c03520686440f86d00c0c16440f034961000340854484024580040c0c000544170f0980020901140208082e0511380110f13102c0c031402003009104204c4000d801c080da0300d040402280c0740c2005a071105022003e030001c40d100e6a032000140004200441c54400940c50010100754070b1a0360549a10008420390880e0b110003000c8602003d103122440350300d00611800c010603000030340581c1121313034482030303098010504000c035400c08016a040b500c0304880380c0d0784504003131155042190005 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 237739928 1250 237738678 237738757
    0x7080a15120b07230f0d06030501090302100513050316030c051b1807080a0c0201060915140d05190203010f0903050c10022a0309060703050d05060303120a20 69
    0x145000510004e9486403060003010b900d040e0f0302240c442608040343c0e10400c01103070084004e200d920750f00e1600a4441d8104c0c00012140c0d031420003c0341e16100c01d018400801c40c4c4c40801149071020200040d414107041d00d00840030089070b9400749001420601c007a40c095166880701c0b02d00c0b01c1c40c40c4104080d4ec07260f07116290301108504200900607500542181d040503800d100007480d0081309004901505082e0041c1c07038041e09240e0038200d034001c0c0d88041c10480c1c0300c0041c4a00b10603001810805e40d103c9100001c2c00aa221800e241d0580319904110150b40d48000d000103501c9035410700c80020b4844241c0245c0c04510003043c94469003005000c4140c141c1b03078101046140820140540075144842d41c80102203000703221004144840c100101c03048074100800300e50b00c418040c0303401020340d4011a4134055507400d242c0803414508000040d90040c441080788030392385585950380c0c00000c08244001c040148181c1030b00c401c00c10301c440000c0c40c07284542059000c0c0c0c4407503a500325018060201c040c = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 237741178 1250 237739928 237739967
    0xf0c080604060c02190f050715090906120f120516060b030f010501150f410703051206030a0b07020607031505090705071a01080d08090607080a15120b07 67
    0x14100c80e04414460721700c4081d4002070304001540c3c1410110b2410245410a103070b004401c081040026400080b100c0841e55100000d01c8841d071203581d090307807907100c24000511690503483c603140040d400d01000d44081600d480c0c41401c0100108234140310402c0d8180641c2c8840e5101e8205010741804d100c0c24908807045d500034400741d4036200011600040c8818168100503007040e0f160341240c461034a0800c815401d2071981300c07002101e82d59030880c00051a0999902c035999204071074048155080c3c40c4060f4140e01c549040071400820660760050040c0456414040c5050100c001654100c8030b40c00758150fa402064030f4981007101030201d40e001290000c20300e1988108022540c1d0709920150b02c0368691500b1903d40300540741c4401011149003e200d44070000600101c0c580100284e40750410358555034480c40e03138407100d80e61030f09ca00c0c0541b00000010403c0c0d0000b0500c040c030390040d0904088260900442c56907a1107009124001d60354110360030700c000d0003030102c2c86078020303c051140107001d0700 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 237742428 1250 237741178 237741193
    0x15030b03060106120905030c060108190803070305040804030b0403080a0609090c1a090a172406280603020705010b0402041d040219060807080108010c1403040f0c080604060c02 77
    0x1ea6400051140000300001e01120070040c034025007101d0402035001040303039100d1585040c1039846000074003820401d8070501c001000342d5400d820a0445050700802d02c83d19503124041c040f00503104c0204180e642c035608020010002c0c2c3c0c02c260035407060f4000d6407500c60908003449058203a60556006040300d504169200011400782c0c0ba1141c12074039501403020203210316150b10b20031030040e201207a500c00a0044005822200e071648200302d8481a07098480e51001d1040e084c0c4001a02c0d0310300300e00c042c9d02d0341c0059400e0a103521b4014071080603200e0180c1d182c00030f08041180180701d41000000030340200d00c0174200031007405800f1181c0d00417a01941880d051090004c2c12030b11002c28003c2105060b0049810754031403580c2c036107600e9803014881d00507680b540c1e400b522081c019154030300040d455400014030510b0610891400104032754412440c0c085541d0705100ca500058401d9a111150080381c4c80000c10940340c2e80d00900c0d90700c019040c0d0b0300c0c4c83e0030203004403400316021301c080d50010f00 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 237743678 1250 237742428 237742451
    0x909100507180504050414010501030c170105040309151202040f05180702060c0d020706060b1206040516030e0f011b08010f0e0a111c0506030c1207030303020f0f0a03061503 76
    0x1001820fa5205640c0010203944600300b40714188901501c82030b42c0d51800300044284104540300e58150340080491100d07a1058201c0d103402c0320801c80780a00019400c440c28031a07043d0254940301e4041d110300e00b40b0b040c101c940420070201c1c0e1203036001d81040c1c00d808108110310305104d4011604207022082200e01841c0035000a52200802060508651000a8542d543e801da59040d0f441d5076821400c02c2000986508002c3d00945c0035603071024130310603103000080061400d0b004141c8544030303444e01a6026440580d0680123015600400e0045000700c40d4403100b030f0002403294901701d904150148065050000c2d000d0800203040e080b240e01c45003c100148403130f0064000c80d40e005020f00e032000405c00141032510001e406100f4803003074019501041c00904120b42d422050140c2e4040b82614083d0f22084200103a40c54054607216003034002500c1000468084d40c060883e070901c1c400e174135140400d046c0700a00341740c1c840c80c0103a022035030715401800000c0404803007034520019820108000038106 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 237744928 1250 237743678 237743717
    0x20709090b0a020a0c0b040b0609160903150209090405070302100203130311010c08161b0303020c09090f0706030f061505091504050406080606040e010b0612150909100507 75
    0x100740c0d4000640000e0384c84005071040383d1829059422448070b000c141028900010150780580d0254400e084040100c0d03450103501c02c1c1e07000c100301603031030300554907242d50794001c40c50355100200f1008c0c41d420f0043c2103613600c490400170700c141e1180000e4030800d821841046801c44070b44400304110341c010311411049480050303552007500e80110480c40800d03807801c0125818000950f0043c2201c8020503803414a2100d03860f4081e01c81e01c569801d00d00d280350010320240118192002070016845003c0001303079800c0c901009900a01a031058461000782c45100910300410703680440e0010780e442c5130301d13292803401c0e10401003d008101d6030581c041c1240d90004055000c0c41081901ca40040d0103580c0f0003910381000c8400034840171f4010700c0100d90380e400c0140c07603800c12161b0380e01542c1080401e2600003010711500e842900b000304010308054620180c51540c03000200300a11000c0e8288040c0c44558580b007030707144951f41c2c1100500a01421013407200a4480160400003882900c170840302000d40107 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 237746178 1250 237744928 237744931
    0x203060711012901030b031f020708040e07210513020622090204030b0112021f020f03070b07030b0906010f030f11220b031006080606070203010c02010b01020709090b 73
    0x2203107030440d28140301d80355260051090030110300320303a8440792403200c4980c030354060912075020980f410401c8001040034107032540c0358240160243c2a6400d050702004440b940030f8440c0394011059141400d440d02068003074514181c0c4d084010598400700c50644016960703c094040441c41020b10140c00c0415004508125121000b842485c000c41d0140c0001900014450821540380a806005684080d402c009501c6804103603600c40101002080080040120303200950340500740c10030340c003611901240da0080c00004601180500c480d0080421400c10152810f54010b002c507046a0514400c09400c546aa5000e180149143c80810540b40e0300710303070034600a088504000c1811071410301c90034020b00640c4079400b4070300008511026400480c10103140d44200c828500361a07152030741c68840300c0f0700088500000301e03000c1c4101485454464100036421640150503141840c80581c00a400d5562007080304006039924803558000e5030b4100051001060060700811000b00141c440e111840b80 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 237747428 1250 237746178 237746191
    0x30908250812070f0f050a1407060305010807140d08040303030f0c030519200f0a0801050307140609180f0a1d0703110d0b010e01240e0108060a120609060509010207020306 75
    0xd440800c4c14483c4404c0103480c00b80e440025200b00050925081c1d0494070b103a80100d1a5114018011030041d0207882041d06031080f150060241910780300782050100300c190181900701c002e1030500800a0718207800390001d94420740380410f00821410114048a00070240c2038200360070507003841100042005e1600721009029000b20741c00100218050840001a11a020440d000038208007058810400745c04805e80c40c1d518220b00da41d071003040555424442c02094642a40c66400103003d141c00d0004112048002c0d0004c0c488040312106101080b40403520810161092010445144818030440107a90071f00301517001c0a02440d10143d540398940d0200601080d0b1441000100d503880c0c1010100855100302e03009499a121004107500e62803e2040504080b18500e21001200b80c2c803080d00904243c079581d907611080a8401120980c20261120b038200e81011804103140e180c1c0015441e002d4080c820214109042d8900f800403a10010009483ca0f40706200010040c2d030085038a642041 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 237748678 1250 237747428 237747443
    0x1501061b06022a0c0d0c090203070207050d06091703150d0206090405100306060501021219140f0c07050a0806010b071110090503060601110d0c03090825081207 70
    0x40341841d121000b8415008200c0d10403101001c00c0c51149900d00d071031184059801c050394500300e95601801030401d40824000c081c0c0d14258800d00003050607601a55000e0800d104a03480d26030354002250700700240c4a4181c40c850b4071025020140b299034404140070a031540030461135403504044043d0640c0003003e8081c41952600c030640155510740741036a20600b0020001c12040c109070045254008031840115086410200c0000380d80d80081503403240003a8110389240741445c088401c44001c020b0211000078480c084101042d00c182c69005004c03001d40710803401c3d03a1001d01c442280d1825030a079000a101d000501d00c01d01c215400030441c02d045072036241300c0076100d0400c1c0c50300400100180e18140d0704840e546050560f03007076102000c5000c940c0c0c1a001d0b201552914401110001c0c0c0550400000d980000040c1c1c0507c3e10aa00841183d0f00030300d45407070001d485000803414011059148050301c10394880c4d9074055031300c2891035401030101c0303c0140744a00c110081d0b80b1190249520260016 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 237749928 1250 237748678 237748727
    0x10806010318080a0903020907020a020603070302030402181906090203010b0403120203210105011e080609090a050304031103060709080703030c0c0e09060103230a020f0103021308060108150106 85
    0x12410000502c0d4803590083c5116200c1c07484c400c0041c0002d85610040c5e100d503c140021030480b5002040b000748064018111518540e29070750150b003e948042c0c412030704400c018030050385200c05055814002d200c0088010808a10f80c011007040d80e1280c1c11401e1803030320406c0100016000d0768110342c101c0340d0028842d41e8020409400307070708500442900c5100c56026018046d1207543c280c00d07460588100340c0340c02c50850004101000603003904101d2401207028000400d81d186004080658050350440455080c1340304c955859013190050360089a9652080c0b4401d190fa203001d0003641d5100c10304d0324025034402c0c508a00f80d83ea9845500c009014012000721190620003003210700c0d0701400010328041d01500340700300c107656550024031003a0b480040300c2c8112030f04040d076140e0f2003011420080c000e20781101140c0800040c10306102e4058145542040b060481c0d40c211100c4400425440c0043c1099624081e2102e0074481c08041d00b401c80900400140031903604003240103001540c0712240c0e27059 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 237751178 1250 237749928 237749951
    0xa2d060e0906130e0304030819141209100c080a241514072108060a060516050a1a13031e090806090309130207050c0d050a0210110f0c0108060103 64
    0x105406081c84d000e90100090100a000480000f40380e16020007040380d03401d8181107400c40e40003c066054640100302045408001c1e91b030394213002d800c1039240c0c081d20f003203d0860804008880b130082c0d401010451140410041c02040c0c4104089035446811a00038103510508400c11045503001d0410700d240600da8280d8070711300c20381101c442c081d64070201641d600c180d81400d4a10780445542556807000709000c41384082d10a181460099002528000044c0c1c24108142e920703421044d070078a0344091040700780d00400d50400a03118618051440c400c3c100104604500380001c0007070030564030748442c06603d0002036000f5507480c48510b007008000e1401d000341e403080701c3d0420b40760720014442c070070241440400340010000384650074041324030004000107400428168046c81d4005411500a40000d0720342d41461000342c403e0901c10025140c00c030400d58001410031031a03421140000340105440840700100700400528074000400034503034400170038002040b102000307017200d04040c0c86a200c40d02 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 237752428 1250 237751178 237751181
    0x21303060501080703051c1e120e120406050904020d06090509150408120711060c0a022802012a0c180b0a1a04081b01020715080408090a2d060e090613 66
    0x3440d455000d03510f8023000b031604004143c54050002c40311910300c0e00303a41074100b1500044009150b20000301c010b080914041c025101900f03c2103440307804c5038003004071440d44c9a1500c2814083c001041c40010302d0b003040c0114904d8101c0c0003980c0d8030011440006e00000c2a000e40c2540c0d0ba4403144241409142d0780c446044541c0e0310f206800c05810b200f4002400301100c56800038269400b41a03003101c1010210392544d4040e00300074000481424151510f0385c0c00341d4490802031043c8802c0d5803240036119071f03840440c0203600035001c2c140c441000068050040c2603014115014185c1118400d101c1d00341d0700d0300011804030440c400c45080c5440c6050100c0d0684644c0c050b14010700c8440184c40040c0ca490700e154007070502401d40d46005002d030000c08215105020081c160050f25a0769000959480c0d039100071090380100c07008c55104408100010f4880c403042a020124450038100780810042e08a007070020380204c0c2c00410034030038140c1d0248015103c1c0080c950784440212900955100c100800b0380 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 237753678 1250 237752428 237752447
    0x29190902040e030a030903032304060f0905100b1003020408100c18030f020a05090f0a0e070e011508090f0a0209130209042114190e0301021303060501080703051c 71
    0x558080851214130b4030b030301a0b10160f560703806914180280305940d519188800c00c06039840030981034650115003c60426400002c0b10340b04002c00003614500350300c0710b600e0308542c42e0941205940b01e05a464a6041c440b10200364401181002e508042c10070303c140352904102c20340106156641c1440c011601d109400c0386602c500103e0203030098913140e0070400003040700c00030242e00403905004005890706203842c070b10b0b10940c1c1c003140c000d8907a2541c45a40e17002d820103040c0d451951052100c041000404803440ba4000e00501d08502000c0075180005081a10000c111101c0c680048402142d0b00304081840300c803142d4112001c025643d0740c194058207402c03000c8406500000241d0403c820054001d400080602d4211408001400d00e080107e444030401c2258006004050064015001600104082d41c00c0b407400c201c403d1140b40000303c0d003241c01104060410040c214410014007020340b14043c09441ea480280006070304640703c15075540380ca08040d090104045c500c07000064420060784 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 237754928 1250 237753678 237753701
    0x160201090f12060b0d0203032205030106091d0d05160212030708070213020304020a0e0a0914060109060501050903030313150e1501080c0f010f0216032919090204 71
    0x20900c0d038076441c040e081c40ba4104000c5810a11340400e2040c545824540050b14507801030095242050010801566607005c19054266014044e40444d0685d022b00030305c030191140c6480040c140c1c0302603031648411111031512901c03a07000910050b04866200c8115034841e481d54083c000c92504600c08540c0f5080440707240b0055000c0440c80c04100702c601001040420b00880d450588a0300b00307082c3d00100d110658000350b0000c284a020402801f21080f2203600102180000404400301d40750f5810340c00e80f10101c20b0540d08500010700160100d48980400b030802840d0141c1401c1401c0701103036a0b1b00c0090b0000c007410b00c10007402d808201501c0c0d00100900200401485065003501c2d06a50301c25030004440452144c100c0041307100e1030006130480700703c4030082c003140c4036080e9103006546aa030000411011401150156429034402e0802d44c001188104803800d00e094004858140d0759800f48482c10100900f03d05100c0d160b1038010503034042200900c40040c81514074800600200200d0710704 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 237756178 1250 237754928 237754949
    0x4030f2a0501050a060608130201030f0e010203092104060801050409020a050607050a0204050604020c0c090423060a1b0903060216020a0303030f0606020705011202090307030c0b0301080c0307050616020109 90
    0x200e400c102042d00700780d0003102d0340d4100740541c50301c074002590215412609404040c444181104c055880b94024801004002d0000180000086109400d9130b00885190003140c1c446e030711444109624070701100b03401100b5002c20f07040c242002c50007044c1d003d06108541c42552110140000d5655104882c002484003c040355a151818a00203469030301c1d201c0706900c80e038035080000710300f41482e008560410f0824400303464907420580c00c0090b1041d000c0e109440541015608074015544082c454080c000d00700020201807038005290029164000340364040c068540001c0016140c00c0501101540e502c0100581c8501d82d460600d00c614000c103001035840009098000181a0507130301800c0c04c200016000d0118540300c1c0e00a136078075a40c038031130640028000000c2c14007281403607011703201a08004040d118116070b40e488080c0380404580011007820700002c01044071803410007650340b68907001d8018040305031828000959038003c65038000d048442c0400384a08580c031501403070b40940190002c = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 237757428 1250 237756178 237756257
    0x402060903011b030c0507030c1e020a06031e060509071b06020a030902310f0f0509011d0d0906050d1814070801022a03190c02010f0804030f 62
    0x122600b160f454000e03003201003031504034106845403285045803030700d0740c268a5003000581c16a58503210b440b102609201c0e8045c5627404540140c3e90100814000c0030240c0d000b0940d00c10152480da2105d2030a0415004180ba04908120f10b803070349050942e000904d41040003c0c4011905142d0745c122250340000c0c40d0610000b0a03d400075050780c007940361075000340c038018003041c401e100381d03c02c11111521851081030001150f8040c244250031040f205030b4800b5000c40c1070008800303034005a400030340300342042d40d448084610a9040c19501c2c040070302001f10040c007209206407c060001556801000100480002c1c0341c021014542c00107517403c03820908a2642200e182000802c00b400c1010100803030141c0b10002400100500903142d20040312540c0c44040134084001440e80e061201c03410702c0301d00060010101c0ca6444032005a1908015101d520340c1030070a00c0010070255030141401c0500003004240710100794030007100c901c0d40380103041c161003409070301c40300003032491210011034000f07105d080 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 237758678 1250 237757428 237757451
    0x20c070b0c150a0c080105040509070509070309020a09050417070c05060708120411030f0c0105090d0303060f03200105030f1911072406051005070f0c03050a050c091509040206090301 80
    0x1131101c0c1c0e11503810369500041340d8a940c10402561020742d00d666039a400141d0901091400c4645950000f01030b00300080c00300b4290707010070b04500e125480340d58040c1d911003c1100b030181c400305101044020b00d0010f8940313080c55442c07221200030b0f40903190160201041c1e410400c00d07001c0c2202d5603407190303c0b00503405182c03d20b04080381e082c03000400e41c042e00820920381600c0c4c50001e040f290101c4161a207500f0302c0072038411b0017014401008160100740d103600c000154848581c468074043d43c081c10211517450510b50074000f4819141c1011810080100200301004451900f81c0d50440105221603000c001d1805000340909405c40d21a500a000000d4000400c00720300c0c061944092141c03402a2200f808040c05e1084640f10310410750010034036036400741c204c2c1c85000141401171099a441042c00002e449003500802140c1003122140c0c0110032510a100c0b0410035902c881da0200e580300741e075280a421054540480b10b1440d4010280b84001c2404c6550f14410f6400034180900200b051018a8 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 237759928 1250 237758678 237758681
    0x305040518190203060a03151d0610050609090406020304060906180537030918020913050417070309030605071e020c0a0303270306050702010f020c070b0c150a 70
    0x240c1d040484000d21008042c4800b5190080ea0f10800c070050a1103140351440c0c950040c2c5c84c0102c101c501c051996070006599401628410700c2d82c038905280241214a003000316103001c0d04c0b10380c01c000d1080905119041850390760401569105501000140e200e864528005018120010f00240780d242080c00c41501d001d104507400806078090f0080703c1500340c030850486c00340080d06445c100c6460803130b103940010008803d000807090b40709140428415a80e00307805501540ca1140c1c80c80101e8000034a6010703440c0583c60031865501d0b888040040d81441d9036901a280002d41044042e01d10106541c4141802400d040c2c0003180c00020034001803821100c000c1c001c48801e41090341001c2000003901c17031580700042840c1100c8026058080700783c19514246c644e2031013008071a034151400041c00d07000d149102d41e2179006511500c000320751420126000780c2901c0b00c06c0c0e070010020b8414048080140c1000a80070300703d0782001c115640c0e4116502090381010b00410018210310800c605102c4074a407903 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 237761178 1250 237759928 237759931
    0x1b0c0b16020d080a140c0606090402062809090b01020a031206051519080112030815030f010501030c0801111914041401030b1507030e0a120c0807080309030d0c0305040518 75
    0x9a17078030030444001d000415542401042c0300307012290f000c400040d1803820716002c0fa642007800144403504059040104070080e0401000000454249482603030450381c2100841010f002605014000c1511140000f9610700c0300d10000360407c42d017607020803000d80c05603000794040c0002400c40001c820112000c40800c3d072044016941c2c03622400803082060b881109114183e0310681e221414150706078404503442000a007283c0c052094000030340c000ca94041201d40d000d01003000001c034a9600d94202030340c100d88594000040d990608040110b00d8070900100c0d038800b0000441c10341d1a82c07040c80e013111002c1c3c0e480c0c4510390790380002402081c1d0301130507441c01000341403d036400d100d40e2845001340580d22a01c06502c0c00b030b0140a01042001a00038000050445006022000603a50301c860314444910b0924040e1045d651520013408450824030089002e00301320801146844a8074010aa441c2c41020030b2000b0401902844d90070140b00707000729002030100a28400b0410200c04116402500 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 237762428 1250 237761178 237761197
    0x5132315280906051e0604030303020c031b0f0705040b0f060c011404050f0606060906070f030333081212191122050303031501030e010f0c1b0c0b16020d08 68
    0x2e0765042c800c000750340320300705d004614014106608081c80e580d4160065000742c0000c030120700081c0064409040c0220810781c111161400400d50491780202190500c03e050308460700580c1400b4400084e5251480c84080a940079102503039908040307410a80117180540c20345505010660900050010009200042e2141c010548080d030f103c1e00d04020b803d00c220314031345400240a104003000b0800428a80c00618041c0c28003282e8000b8002c92156110f00802410064441c6070364183c0ca02d599080c000405040d00130020503500501d4207404165000d11a1010400d0500f4000550800106007402d024003558420a02c48034020290105254000a030100f0020084003260501c594900015804640019010707519645a030704140d00781411404940e41815207426140e01c02100c24071881c000000308405c0029241d4402500078507641a04200707100210100b80204042800040340c08203ea84400300c055a49000c1e140350920406107000c00707075001c449002007c0921a08000801c0000f4 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 237763678 1250 237762428 237762439
    0xb040b070305130201050a050d1409010c050301030203100c090f06030c08060603070e0f0301090b0a05010e01080312160e0409030905010e0402072001090513231528090605 75
    0x15a44001107046400460341c1d003001c0410f1090f00c401550241e402026040d40d145000ca151040140c4050191240381880c80f611140c0c0a00300041d19000b8030800d11600a646452841c41d455900040e50341d00084003818081c07071ba138051169510b801400c03420001c10190540301c100703a90b40c1c90090010075214255002158400340055441c1c036154080700c4c4034900d9502c81e007032045d01050501440c0110101119007643d0703070318003c001054550b40818403c030810800800d00d9814443c0b03070b0920303a0060707000c0e40080d40144100d0703980d401d80e880707425407086403480b00c0c019600c81c4c80307400c0341c00c81d00840d01141c1142c546038a000a0682c4081084140d80086e21340704554044a01030104900c01c90001510120340c0a000f540e11800d8010002c084200514180c28502d03154400100b9880c03c40b514202c0143d41c07034400c50484000c800c040c0f010400014103100451808040c00e1311032086943c03450340329600000302d04a20340c940c02d00b0074005100c3c10404c900350076140c3c102d550082403540981b92041 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 237764928 1250 237763678 237763681
    0xa0b120c1008010602150c0f040305100b040917070221060f06101d0d1407030b06060319050415150e0c18010c060605100c03030f0b1e120a0b040b 64
    0x6005a1003039040310313801d0f0b0041c40d5a0040c100920ba58013000352a030900001c08221507403800d501c00c40600301540c042c2c00035203141d982ea40c0360344080300c50301001180640d08062498000c100c12044100210751203030320160f52040c2c640b001074412004e0b0085401890941c1d940c0600ca00b50000d03c007031184461100c0b03951151100820060601000d40ca000c0014920381d6030b03500c2e1181004110301ca419406440e00c4040e0100d41d9441500641441420303e055011303030301c10070038802940b101c1c2e03801c2441030b44e03143e01c0c4d4201070009440c0c0090300d21f4098980c64545000c28100100b084400e071907800d002d0010444000104081040c80c01c2501c10444404000404542004e000500301c500d413502c50203410f4140039600005548070b0640c1c0c0e40603030750b140d550071000850340c9580c410075002507a0343d80e600c0a18481c601d4054101c608220784001d0071450444c4841c0340751110360982c1206000c4038040001e40d0002f01c00a0103040141700340100c14080d9084c40810042d6180d0300300e026920403d044d0284d07 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 237766178 1250 237764928 237764959
    0x120b09010513052a270c070807020f03150103050f0c010311090f0a03050a051501090b0907230415030c050a080105190314060403090f0f0e0a0b120c 65
    0x40c05003020b000340454103e0b00214541d03d840c03140450b00d15a01c3c5003c1843c0840820010b9820b225201d1164040c031382c200266000150f60301d00d2640c1c08050400c0c49418480d640d201c4804a00804070024054207107408441d03040c0d507003002000c030181d608038180710046d85c403403a00030703198000c49100952a202c2c684030048298000d0144441c09a41c40c0d91103801d000b0100100111a0f980150554000c903941c840440072034400d10400d40d205018400070121600c5100000c681d405050b4003900e542480c090b40f0109a0751010103564000515181c0f1481602000c60164082e144445810302030120010f0002156070022400809082098908101d41584010150b0301d030b110325020300d00082c800200501441c580341c6802caa00300d400991080a030f5440f55200050742003c440d0b80301c3c1990004040008066000517550050084803900600441c43c11410588840450049402c3d0354040710024281c1242035011155212006010490740d07810800f47d2a1a01c8240705818065410707031014044 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 237767428 1250 237766178 237766201
    0x606080114041e1202060105091e0415020f07150f0204030f03032423030723040e060408040918021c060b0a080c0a170307030c0c120b090105 62
    0x34810000800c518541d100d41e9603090001120300d204000c02c3c00c402010020800110780500318110780e4000b04559410501006590700e4001c1460b11120802280907030410264085c4c3c41e0003541c40140301442c1114a5101d00c040c0c0688005403e00344c00106201092001c82e2412100d917400c0604100281c4140d035108a081e03201d00d020207804030410000c0d16000903c20341c090314000134028140c000e0308484003590240c0710390790341c44401302c505503194611390704254070f02200ca041c404134001d02d4164075180300e000c02030f0040880c40c002c0380058a07824010340c0301c540003c400168041d0a03101c441c038145c44c3c114580e03001802000811440c120415462118032005d5605168000f0302da14900e50601810020355071403407600300e400719211240e40740d01c0c0c1c9454406501404135074014041d501540800d00500c000d885c1e000407083d03e0240a580101d244c04400c55008540500c2c05c9085027241d81040c5100206590042c240003074401184003e110344901c0f02c81c001e0800d04000d10443d1a030f4800e41d034 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 237768678 1250 237767428 237767441
    0xd0609051510050d0513060b100905120c0a08060106020d0201020f2a0111310311030f0709060312020303090607203301080304030611190c06060801 65
    0x120001e0319201d2050140751410240702088110b280481c0340401c14010b03101900c070151752040504801c41142002c01c07640d8000c0c0502181d05482c2d21102c1e00780000002e0a41005114442c054200c845c5170140c03003802402142800310014000c030001980c1d0703141d00f55441809100d10801406030b5405081d20724410300848030a800e80103c0c003800c100b403852404001c45081c00c107400c507401d0404094030000c2c1080c0030b41e0200c40b002c05500350f221442108500102d00c04a5418065000e445400020300403400c024402070b03a4014032010000100b18012070b2905401c1c9240c042c05100750f800000318040300b41c110a060383d208014001c0901710166003a607590009640a818a8200d200044c1c7d99600c507000400c83c510300350b40d0556214981c2c402013403d00200903e200c000c540c84821410115820060091030100da03000b01e00709070740c03402c244152039001e9804010000e54544101c0710b0014902c03015192001001100c0c1c01020541910107800c401c00050112071844c105000002c00002c184280b0 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 237769784 1106 237768678 237768691
    0x302190501080604140a0504021507050706021603242022050310050403020705090f091501080c0d08070611030915010506120603070314030d060905 65
    0x10440900103065134016414160050403108800d41c0c1e45170b001100c1d000000d10368880e4400200c81c102100e01d040c440d2000415413800703003d00031548030202c51241c1c0072106400781c4c0103240b03102c280d4144070140024402c55034407003220300c4da100d007141e802c14170940c001000d100c042070011107028036080ca80c403807500200c0ea140f00c0b00140d43e4186c141d03282d11000d04411918290029580da8903003002146143e440d030010908250081040c40042e2400078036503996031802c00e60b07002c42c1803c1100c600c0998800d46c074101d81e8404c2d2002c0603905884040c0c0140094461200510070041c0f02603200b00ca4a203010028600810f007030384600750000f014000101d590b0300700703520054941055140c00d000d40006503c010402ca075600000c4802442d0b50114562251340c8080c0082e0800c2000d500107014030028424140d50000c0c0403008107d1040c10160030050380c2c0d103c00100d0300310b07503007107401 = true := by decide +kernel

theorem cover : BRFrame.Cov 237589928 237769784 := by
  have h0 := BRFrame.cov_init 237589928
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237589928 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237589928 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237589928 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237589928 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237589928 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237589928 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237589928 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237589928 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237589928 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237589928 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237589928 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237589928 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237589928 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237589928 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237589928 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237589928 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237589928 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237589928 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237589928 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237589928 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237589928 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237589928 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237589928 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237589928 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237589928 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237589928 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237589928 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237589928 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237589928 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237589928 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237589928 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237589928 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237589928 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237589928 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237589928 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237589928 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237589928 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237589928 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237589928 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237589928 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237589928 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237589928 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237589928 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237589928 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237589928 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237589928 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237589928 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237589928 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237589928 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237589928 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237589928 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237589928 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237589928 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237589928 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237589928 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237589928 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237589928 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237589928 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237589928 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237589928 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237589928 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237589928 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237589928 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237589928 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237589928 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237589928 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237589928 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237589928 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237589928 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237589928 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237589928 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237589928 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237589928 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237589928 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237589928 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237589928 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237589928 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237589928 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237589928 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237589928 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237589928 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237589928 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237589928 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237589928 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237589928 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237589928 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237589928 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237589928 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237589928 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237589928 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237589928 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237589928 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237589928 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237589928 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237589928 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237589928 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237589928 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237589928 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237589928 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237589928 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237589928 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237589928 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237589928 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237589928 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237589928 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237589928 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237589928 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237589928 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237589928 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237589928 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237589928 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237589928 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237589928 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237589928 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237589928 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237589928 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237589928 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237589928 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237589928 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237589928 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237589928 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237589928 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237589928 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237589928 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237589928 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237589928 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237589928 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237589928 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237589928 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237589928 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237589928 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237589928 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237589928 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237589928 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237589928 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237589928 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237589928 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237589928 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237589928 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237589928 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237589928 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237589928 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237589928 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237589928 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 237589928 ≤ n) (h2 : n < 237769784) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
