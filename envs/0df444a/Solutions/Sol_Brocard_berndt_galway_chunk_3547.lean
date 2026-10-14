-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3547
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T09:58:40.852838+00:00
-- url     : https://prove2.me/submissions/871fee44-9835-4f15-97a1-5b37e0450d05

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 637769784 ≤ n < 637949640 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 637771034 1250 637769784 637769813
    0x190f14160f0207062118230a0c0302040c2001020406030e071a220603060504050f01051c1a0f1801060f0b0c0a0b091e160e0709090e0a 59
    0x2e56001c100200f03c03080d445492640ca822844144024103180120310901500c01140c0300c000c02e10342005a8414008a01150044041c0016914918031145001070f6141c000c08040942100145031042000d400c00ea00404007410803843c1156100c0d40d240d03002c040320754004044203c03da44c0403138107000c81a00740c030404262050035002450694a0108490403400e804940202910b4020800c0300c10a50803514085055040b01e5506407840d854110040c0200200d00c100f42c815402c00d00800e602c00c01c0e414589050b240b025183e00c00d01c6180c114080702e41c07191034004403080e075156590390501d01b904401681c020300031080555020f040914102164480355007a5854592510384100240030744500032400301c40703107035014545035800c0419003400c0c0051854081e011180c82410025407c10102d04941003950410300d1408250344007407002d0b92403a044420149902440c0c10a20000f0401070005a02414914003101d807251914821010b41c2c0080310b901465900100c200350070840444040d0302d0 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 637772284 1250 637771034 637771037
    0x2030601140f0a0e03211e0c06040b0c0d02130f06050423010c021e0406080c09010e0421080a050c09060a0f030227120303190f14160f 59
    0x8190b03590266401521900008005002c4a00c020f80c04a860500414100c0f031031090440170001d03501e000c1034400b6805800380c90f004103150701000c0006558907003950303c5500c0b07200082c0340c283d481c0d0341c51609800e409001417540400c288100c07840321041c0c3c001014240800d20b070b1441d00c5490009180320500054220506028050006100c8100900c03007507030b000c9103000410b5000c001c420300140e0f14089140400794000e000380401000303102e103c401c1da0340003440076201040510b82d40e400c8251100036000c00c00f50b0285e14040108031418040d07515503003040c01007041c640720320b52081e411140c40708101920404a51010100300d000b120521401c3c0d030007000700021610740b40c0341d400082c80500c0359200314800c1c040544c2d01c01001a11a03070544071081c031100118804003103200c0c01017a00800b04500356110b0b2840320b4841e05030503804019a07000300a06090f102142480c070207850041c3c0070f550460600c407a0381d4205090f0001c40d140700302d40038501c60451042d01260304c42004082d401001c10190 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 637773534 1250 637772284 637772287
    0x1020d020403050a050714012a02061b0d030209030c04050615072415061809020c1f06060203030c0315031e010b0103050106021c0e060703090815010e04120e030a060203060114 77
    0x47e0700f660051080783c003180c2e02100a41c03900c101c0c83c45003150842403941c0a9040940494500d1a038071428502c51220013024080320f141c0e86169004805030301ca14000650185c01010201030796042941007950030440062019000c20044501c0d008140c1020310191411009261500e0039810010b035294036941c01d0813070600c03281c5800c0c2144400d190703e45c80340c2803c0002001407000020358131000d00b00500322040c2c0542d41c480e01d510b1001e80d00c41c1c4c00c9101000e2492000c100401d00110303071040500700d840b20b0b0007031411a0f65074400c26002d9000140152405808190702c60f14036901071065000c1c070842164140150610307140f145003111341710342c40039061518010062211030f40024048088103590b0710810540341484904030340101c203062000b0340121000ca0785000301030b001196041600c3d44031040300e044a590171240402e004080c402c00d080c2c060810017186c0828210310009040c14001e080005034210042c001c289000f5141505840840c3c0c0441404072030740e4400b440320321142516210f603 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 637774784 1250 637773534 637773569
    0x910180b131205030c0610080708060f1315020307120506101e0e0406080c100813300c06150b18210706020d092601020d020403050a0507 60
    0x494910755008000c0c1e15428042003204012003002110b4030302a034201030707804500780401c026442210303d005a06040c0203100c03020540900c002041c0d4411102680001c0c0c285d220003d03a4034540718108419a00f04403050f0300078008403101d000940c0112042e03035698031981056040c1104442000c1c0861344242c0400c0c0c88400e210782c0c040d864651310504010b900400c3c1159180c2520302011903560180c0040c10923400180e048004a1543c8580c041035071524140700400b101150a440c080700c0b003404504440baa03c8000c5980024101b02e010080180c4030154105401071480042490588800042e900d4030120200410303070180b030302a50702c0b01030103400650810903041d044d809006c1c0000789070080035020039503503a10026154030382d400b40702a03030341d00c01050003280c0d4440650780100800340c8170780c4040c003256600c00ca4181c0c00b1901c520074a0035941400f0f183c56541c00201c91600c15041d9000d01c4010411400c510050004503c920020150038400740303080d03801d1850680c401c0c004407900b07903900c = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 637776034 1250 637774784 637774807
    0x702011b05030405220b04090809280306050115050304200d1e06151809111503150d1203050403030e06090a0b150109260a030c0320030d0c02030910180b 67
    0x540351034460441e400f02f01c1240c0741d0312107401840c1480111130008400d510000034400304d40e02460581d2009a511581800347c008196024407060324000d200c02075090300400c03e03030001c4080c1c529902c00100b80d02c1d12489240c481462000c0800c41d030060f51000b40203400d0400c10310f4880c180281c8803801200f07003818608002920034038130340c00804c410036031181c1c01402007181140004c0ea1501c001081140342c2b105201050446030011980c80c107a40d040b030000e010051a200901c004281d03801413074000c1e8803045000450103000d02074400ca0500d500c030000f0410b1b0060500406200d03203810b400809000311181480804044060130003103100300904401030301039900c4080c00c01070700d8a01001141c41913103d40c2200034074200300500f4000d4025035020f0000c1503071141c0c49440250082d941d14440880298400c42000319030030414049a20400591120006c03070382118001880f940145c074208021034021513414288031903050006000e40800e50101d2441903440400703480722240450800124019 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 637777284 1250 637776034 637776037
    0x19060b0a030e0a05030c06040c09140604110d0c02030c010c05030c030112030912060506130c0f0f0e0a1e15121109120705040f020702011b05030405220b040908 70
    0x1080c030400da01d600040b50702d042e0400020300110b40c07110440307a941004106160b111802a1030071160708040352000112480c00d07000f4401c2401011240304800d40b9031000b000001d0001300c98400c0c10300750601c00c000030b440440c440c134411425503030007a583c2d482c51200391500b1690b9900040d010301c80c00340b09209201801c1c000f1b40341500d885514a500e01c00c0380c1d080c25034450782d180e40159444256840c6103420880d842e00002c3c01000c041d14412000c090ba03c0d146010f46989008500002c4d004000240d450f91083d20b40d40720001c1c041c20403004510044011440001445d0030124403040291182e203052040307212400c00609010204204205144600801144900408030040d54a400f02c9481502c3c00e00211a40040001c4c03c0803821400a09880d0311107001d40706e42c510407864207401c415500030303d000300e8030a207505a482c0080d45175149001015268180801e69540c80280400310301034458010008130826401c070190b03488250a0b10312001c0d40c40021106010700e04050400000481000 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 637778534 1250 637777284 637777297
    0x30e1c03020f03070507030e040506010f030b040b0406030501020909010828081303030c020a0f0506070602340605060612040b2a04141207061d09070819060b 69
    0x8564044008000044010307000710002054074a90010612500c142c001005042152082d1103800c155640d09042104136003088400c9808103c082c014903000f0740c40384d44402a800c40c01480001d0380303101d05002c50115500354208903801e80d130014078490b20780f804000060040c010381e0001c0010480c1420008a1042d03082d0140c203599100d40f10740c00c104807689050f26124200c8407410b07061166603007001070402030807840c142d026150023200403404010140305003054480161500b032900b88141d9460000f0b6015076001c503d0341c522112605001800040500a20500880e46060501c483d080c0081115005025148a89030030040b01e55000c09007000d00f075105410030800e02c1c05a4490010aa0030b644514103074504138481d4034080b0361191400007410a0b2a06501d8040c0c0000c4000c062042e6104404d1554096911030b01e001c109252080d148103407010400748202c1c100c01010700210b44c100c242a910f44000c910040c2c1001980c40d001e040c03282d02405220018002c07145005d406800d40d00c42c18 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 637779784 1250 637778534 637778563
    0x10e070b07060b030a0804030209160f0c08040e0103060207200f010302210702070f05010806060904180b0412080a02090f0909031b030a030b01111f06030803040605060f01030e 77
    0x7049000c01e2208541c014a825200a0b0903120126002d1a00b510a684940004c0380300e80f5505001c034801410010550301c5080554440440201e0400c1c4240c4840540da0740c1102c655008020100d20704104110460003544141005a201c038810b15141c0c1031400001c01c0343c0e1609080301e03141c4003141c2c0d0f5140c050000403001c0c24010398407021030010303440214070b000900c0709200f1a8400c0c0000303194002102000c860030340c41c00c441000d454400454518406944031980540e0a0102c0007071443c0a601c000744071808080304c651101030755591608003000480d41a00c01018680f0040d0b80d4503041100c00d94009440b200461030040c00d40c001079911b10089054900610f9140c00085805030204101d03000d64021200c1400c2c040c08091507643c0e01e42c410b521400000f402c1440f191015401303000b000e0f80d15407000b4040d02402154017000e81c0c2c1c0c8541902d16500040d02c441c0004040350b0480d00031030003180038000c007052034501034041c48241c080d9440402d0405280c84c18040300c041e404182c151714041c02 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 637781034 1250 637779784 637779787
    0x172d06011b051009080424030507030e120a031b090618180b010e03030d0203060f060f0a03020a1e05030618010f14030c1f0e041a0d150501060e12010e070b 68
    0x5051682c601e006c0c0e90044909200d0324907401d0704410500038030101020305940c0c14062591006c00403801e03203200110040a551006031b0745140740b24642e0107001503002700c0c81c5c0001d10524000304a07041c01010025500403c040580506c621648403114030000003075420304228044c0b608030314026a02d4488504030900c0c1d514640c1821030707841040c029419104c0201203075140d4941a240c03000961003a202280718004500d908004c6060038001d0310051624403c01700c2c14100210003e1b070295100000d080d0800902042c035103044414818611500e0030a030703860945a28128050148000007480c1842c2180d400c00f00404c0041c615440c5242a1034402d16501000c100b150f001c0f074a45500507810652245c1403848808402141e0b640b10109007007603590f0300c8240c0c0440f2090000701c812000417052807507050961010302e81801d050803400148141310324600e546056030810100d076400e811080001c0d460907031000d0517103007441000c40c042840b0b0700200070100d0980e160382d03901e2041748940d20142c0c10 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 637782284 1250 637781034 637781051
    0x706090f06150e0f06130b04090b0a0e10140402060304050c1809010b042a02070b0301121218050904150504050115081209010c030c080f030a0e030a172d06011b0510 72
    0x141c1d27411000106600808406640c1861640708001d8100301e00402003d1044010005c0100c0c0c55000d140404410507424034441e482e03940900145520003003003039546114401e414901074940d400361007010304120b80446254186140042c3c2518081907003030348698108801d020706d1040d218903490b125100e10880d41c2c0018003c020980c00d002003580031070f04001c804000010800c1f138180482c03441c0c91040d00c4841c0c041000701410f440410441502001c00b0313050000c144514181406501d400501035100c0c5941860a220054103a03101144d00315226515022003001c02021518401c0103010300d44060306c469038424411a846000d41d0700c140e030420081038041010705014104444155401c04c2540d6982e0780d80d8011250aa8002d58007050b40c3c92804c440c0d05041000402541c150440746d0b510403140d21602d8001d100e0200c405018045107d26a076400300c01d00e540d20b405509000b801c10451a03140c5403050007d08a680002c0700e103078100500920800000700c2c0451210030444e615040010b00c3c01 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 637783534 1250 637782284 637782289
    0x1203081f0e0109091202030304210509300304032f031006030c09050c1801022404120207031509060902090712050c0c030706090f06150e0f06130b 64
    0x6203951145003408403050011602c14100d030410a0294001c15404492103001e000c201d030750f444103e80c06080c400c41c4e840c00981d1031140001c000e446070039501d4024204005480042d02c81501041c0e00d400030031500403c18410f00c5d00303803644454050310f4009141498a1502d0b000264000d89550b41c0100c6d0034505ea212040e450300c3c0c85d1040c28000a001c55070707108101040d18004081d180000c0c0c844450702c43c000254071065014007441100d000c50020f040c0341d010074091500101300d00c422410741c002c41ca0070000b0f0040341c4010070740110907845103945030300786402c0082e00000003080a1046411002090005c1580c1c804480005d10400d8400250b08d8020304140300241031603800254000900c009100d85264809074100d5501400802081280c54082881885d40308003192035450383c0050012101040c1607500c07400816010305041e000f600e426980c0c0c40202c42260f24152070002030306205114007181e0040143e8000315040d200040b07401c180000415aa0141044400e10f9865681080c03494 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 637784784 1250 637783534 637783591
    0xc100209030f0706170c161407180b01091a07170c030d06180614100e040501030302062d012105070602010e01151a1b0312040606120308 60
    0x40c800c182c15122620b03241d103001403616001d0088001c0c0701d00b14001146907041c2c84011502e0003034100019499040c001d90f682c40141003803003000e46160081e041c0000302060103d00300b112217061500300280d8860700307030009800c190050b00404c202c0030784140000044034800088a0039141c02c601200305800e0000c000c2d01180c80754100122043c080800c005a2212803900600190352203003220280000d8490742035011200240324001404000505803d80c9003001544040d180c0740740c0c60090102070746d0300003203010f990081c0d00407401680600b0030010b94004d451440e058100381080200000081030113801c51003d010300540021207409188840c0a44141591511960b4450251a141a602e140c080d0007045d49c08404c0d082942000d220b90400a0300382c02240540d58900768000d41801c104803204030f10703040447c9018500c2001e49034000c070301c3d104101511002800c0480a04140b4040c0b5044050b2440c6602c04851202c802002500007a001046194415888024080c00340100b03401d14050 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 637786034 1250 637784784 637784803
    0xc15040e0c03062103090a060e150307030e150f060111030405040b040b0d06061707081009061808030103110603090a0b040203190803010e0c090105030c0d06090c0e090108030c10020903 81
    0x64103004d02804c0403494044081c00f01c8400488007443d04981d2203406545e4082040c41c16644140f18840c2d00740290b5211000d190404164680024044000028140741c5910410603002c2500024200200c0740010138805920081c2841c01d071002e004455016942c0c4d001d503016103441a600c0d48510b8015484c3c9500a20f0b031040e00500d0800341c020982031030b01c0203140342d0244088850f50b441211b4114480040e008003220740150060181c0c450304c2c8400700003042d604608481b25502c0d008000001204412050f10990190040e07503680d503d10310b413801e00e900c003907950f260180c0d50034010080381c0d81c40410100300c01500310200c4003803a131366440004d050070680c010b2031900d0f100c01030054092003444c5001e141601c0147c101c4402540719844500c07528011109018001101000005c281e01c4d030400240040280016010902c15115010030040d1103059808500080303582e0a8502d482c0380c4004980c2c0180b0480011714034201071840c46980350100c480840c4d2009400182d916820b0f20104149441c = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 637787284 1250 637786034 637786069
    0x1021002040b0c0c090603070306050402130501151b0308015a050916090e0a1a0a031203090503070b0108011514010c03120b0d03020c15040e0c0306 65
    0x1600c03521000c4410321038001050f1034039140301c1c1410b446075509080c0b08150240c0d000a00070315040345181d481c10068000100101d030011501c101d1441c2c060201e02581d40a0078506070310000049003968010301d0710110110b0540d19910800c0c00d403020a800c0701c1381c28103542031400340c2e600692816940042108040502d552085504200c180250b400c03149040b048607045031002c90000307444490801d445c592401600d60220303c00001c02c21907038480c00f200a010700542071500b0032030303078a80400c030a01030f0032140c000d40e29840c0d40c030a07072440c0303120002c59044240460f2109100c5003561981f000c1c040e0005610000d06035140000c005207c07080050310030455122804100a41e15140b48a01800d1141c80c2d03011581410400402c1d610401e1000003407014040e034035071446250545048800c0070441600c03005440c2da4204035a0b00f07841e1900c1c86d482da503001c0d4006000c105403c0040c040d022408000007003900350107010500905210085442e0000c400308502e50316919100001140c0e841c00180212 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 637788534 1250 637787284 637787287
    0x303090d06051b072117040b01060e03030a0806041a0604030c2105030901140d0c0c021908030d0c030b1905040f0c05220807060210060801060303050a080601021002 72
    0x10200062a08000e1007a0f8141c0c0400d900801c100240c0301050080000081040300700b00d030224602002c1001c80d0381212514036008110310b00440300038509000903101034681c604508010300c2081d41050880001004c19002980b528410b843e00030180c4401a207424840d5459103401c60002030140785544404000400e02c1c1e9403540c0d0317807070300c2c10b8102c0c25486101c0710706070a409840324540c2441410707810150024041c514015a0000446200c10b181d081c910f0040010301c43c4c612030700018820390449541075190001c13804410f00401685000000e41e8098580b5401700c24400100b020050399001f400c1a400800c040c1d405800540140a0000030b00740c1140e011004c0400c0d60450241360030480304151803c1060380107105004041e10644400803000c58000c00c80401103081030a5000791108140c0c08131762000e03444030711903400c14000f584010010781c46601e0105101055100c0c10008002c002c000300040c0b131645d90090914042e10300380c0400c1c41070701030018041d039000780403102003802508400c5 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 637789784 1250 637788534 637788559
    0x11091503030c0c0f12060a0902011403131a070c0f0c031407060f02060705090d051219090f030c050108181c0305150f040c050c1b0909150c09030309 65
    0x640c0d850042d009482d10030a0102003081c054103150745c18424001542c40500916983e000007407010700fa41650490402c450061112400b00c0c1c000301541c00343c0303494681d10314100c80500f1300b180a41911005e881c8481c07141c1e0140085c86400014085606d42e0004c11802e0050660078444d03a45203081c1c1c0090310740c8420681d02e03c0c0e840310201d5003000ba1042c0ea15900100c07171b1104002c03642c80c941141d440d00890010403200300d140c6000316100845c540b10b40d007100c1d400c2510f9400d04a0b903400540300d01540380c822007442400390b904611400090000034844100e09480e54559448404151080320b040c0600140030400307400003251908070318525481260901400c00200c0c81c5030f406d408600c0c000003460310700400c441d860819401000c0d4040240400c403080c60b0103040200a1003880b2400c401d018080121103c810018048000020400b400341822005810140140700780020300c800115044400742c6c0700107011301102a07400502c4c0032140d944454000010030714522422203203a078800c6860510 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 637791034 1250 637789784 637789807
    0xe0114070e03060f0915040f050a08090a09050c1204031b0f021008270102070b0c2101120605070311030405161502030715150806100b071109150303 65
    0x1103041c8890940071110507507540e4043c808040000d4810b1540d80d00408070708400700c0500c901d0340c1d070480d0154081901c03c0b00e0a03035030726180550220080b50101d030301081d101c0c1c01e440c1050b9818014a18004184030031f1030b01014001c0188034404007029440c5002000c141410b108105580300000b000704035055580050400040c4101c640c4c0d4102d2041403405001c0c2200c92043d603249008800aa200c4030700503c0402104102d1100031f98003150b02cad98240500008207040354103190140d04608400b554501c80c00c507160041c1d00c000d0541200040a1070010800c40680d00036000e174035508143c0000b10354450355412000f5081c3c409458504203c048240410710001007980503c1e00388600b200d40d011a611540d040910f4409004500035800600966002c030760054078180307031003402170700005550150340c10401c0e00039210340010f1419030002c010807a440001c1c000c081c02900642ca11181000d8055858542c4001d411070003600440f05540499680ca691512144016000809803922110783c07041 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 637792284 1250 637791034 637791047
    0x150e030601060815040c1d0301020c01140603010c02120414060405090a1d01050c0708070c0f03080408010f1415011106090a0c0509040201090e10090207140d030510090e011407 77
    0x1c040545580b039404840b0540340501c601e0f85006da154403207010045451000c602e2000c2a03541180d01950204404079000d4004e100d00101900e00c03170007403009420110140f40c02c441d560400030041d50320003050050000c55480a680464128518804281ca180700109030a40201c1c0e2000b600010500c0500c07103403440503004041081d0601861202c00400d124155090f20703000c1d0b880e90084041000100082100003004000043c01800e0001b01507503961280c0c02c0e141c1603030340141d900c3c000c085030903c02d080e000e0090721041c1c1c1200300d060169056001249800f00c5014090109a5034800c100701410390281c2c0101c41c1815a20007a61020b03c0d00d071499507101c0450620441c1c0d0380a0741c180c08101845d101c101c0c2401f583e01a0340302103506003007104007204a4400f070041104540700c00e500045000603400181a130307030301c0364030080c1000580c0620f0314076106890813840281800c010422110044110000080740e00300c90000c1039a00c0c000400b140101600100b20034210b25441c10071500c0c41c0c028a = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 637793534 1250 637792284 637792291
    0x204080d05270f01180302090906090f010608120c0a0510020408070f08060c161b060e01030b01212a021203090c0108070509040f0b010815010801150e0306010608 71
    0x1c40d00e035034403400c1101040303003640d000300915840145802d0082055205d108032005181400c03131241216500c07900040c201c00d6048490500642c0720000b000042d032018030180e0303503694101c8000d000c81030800030f10315114104505903c0c0c40c04070100340044181805c0011005444c0c000042d9200c45008420190180d4028010902c1a01c5940d20004001c43c1d41002c2104072200300e4080e0201e916914010026a4000745150500030702e8100c00c84003082c00303403000d003407000c0b6001001c1010918201e80581401004a0164141403804048603c0782c1d8100030590400b0405c1c5440d081440a601c00d034800038015400c6540c261001c88040060b0300710b0b0f1b121030301c0c43c04402d070702110079888180d441d5581c94401140c446001c1d4202e04c0000119501800c1000d800c400141060703408c21041c0004501129610068074009544030078107031500c1c2d40c00007202c0f41c02c44204d0100c243e591030f07210b001800c100f0040c4980c4c00040810307a01c3c070750300c180315039900300c5940802070a40340c20f941d540c14014881e03031064 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 637794784 1250 637793534 637793557
    0xa0903020f0a0f17030f0a020f0706030b090612010608121b0a030c1e021807090608070f110102070804121203050618130605012d08031c0204080d05 65
    0xc0e214000c0745001440c00c411128120000c08607941441c1c8441c44d1140c1c00c031601096031105000743c0942c0e0104601030b0034a030800d43d008100010005148510b814469440707181854503003151006240c03520b60400b548180f00760707030261407284480d04003401042c1c240d01440305401001c200284550104005000090001401128003a40b00544689070086810008c000c211075a58220005113000720380074081d4522003a01004000a4000c240070030314101d0700b05542120030040119054004045c0b81c0079141c1c52520a207a0314119201a1203079452540002c148034040d03550100c04042501101c080e26032003247c00ea2566030700d102c0201028012102100c40300003402c950300035070b8401d2007454841e80000740445110003c26554003100754018082480704040303500c12901043c103c0c000c80e4003c1c4540805001d031400303a26401401d91442200900790710542c07141c10000084000141c4040f62280940903103699403040d8048000d1141e0740c0001c055019000714000020b0f00034004c0c1450030113a = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 637796034 1250 637794784 637794799
    0x40b030c1e120c011e180905061f0e012f0f060a150b21010b090f0d0b06010324030501060510030e121b01050c07050c0a0f290a090302 59
    0xa2482990b100c1c50f020022500041102c5801500041d014040800c080e40d54140b02c10b910308207503032188460f111900f088500c1612201070210034180395001c080d00c0b0b11080c25040e540c04841c81d0040c450401124154100418411118201072108080ca00e04410f550b00e0b06030006000101240c580700b60321a4015640980400030b25403e00d24082d900c0302001c00d60030601c26900b13000d00c1c0c06164010144022016641c4100e1100c0c0c461001c071458041e00c922066140ca803030304002040440c1c0d041c400039a00032036901480b03900107413031040b100d0b030030103801d080c046074089144149142140088161070007003030581c3e0002083c800d0641c0201c00351001500d0040328050385140030f07000d490048140f080207a0009050381c20544c0c0742400741801540c05401084c9070b0303080300751207401e40f03906076008103035544005627200c100070080054030400d410548024804601c0c01103181c140604071b100c0d002048181d11080110410740c4c12440060a1a140b41c050700e03101f22420060640105000c00c0740a00ca2 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 637797284 1250 637796034 637796059
    0x3210c02040e0111220f0e01031b05101d0a050618010507120e0a0b040b0706110d0908122802030604111603020d03110409090212033006010c02040b030c1e 68
    0x13400706c103030098030300c00c280ca410142d00c1e568910301c504c0c400002440414140400105a6984d03040008400c90341030350303444030b00494a00030004d00402d41110f4a1240d0b1801c4020021511210165403d0008506420540c02c54603030040c0e41600c281d200040c140d0031207190b00001d1755002a00200b085400f522007894864440300300d0783d55403207a402640c141c0303030f018024040000c403942c00405601c0d52426007070341402040b00d443c0094419049045660500120f1b1050300b400d0408400caa012403413440126404e0f02540f0b440f80003101c0c101c13100c170308913030004001750340c903111078001c022070118a0818030f41d112880c280300b41800000f80c108a0041c0240805600550301c01c0c0120148207400103a1640b4151800045000038180b010049812014443c21a010a40244003801d001c14425840040f8034220140e00a01c0051066413100c041200b8400e10500d40d90055402410981c10344000480f218581c2c0003a1510f40c2e6401003907807100b06a514a0380761a04c44904580c3c481099501008003207 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 637798534 1250 637797284 637797299
    0x1903031d030a05221d040303060506040909060b040504030c030c050a170d050a0e07140a03061416031a040f020c0a120e0402030915040807060e0703210c02040e011122 73
    0x1c00c905c543c0b044142c400207466580010215200c0d0003521901300042d0071980d031400b080030f50700180e01c5990615903448104d8240311103406114600c01302210108070f01d2a0998010744049403045024013003010b56807041c1d00300001000440039594001e00090b120700c14440c80c0b4017140e44800034501041d0b04260101303104801d03a000d07450250740c0c076102408000d800c10070f01240c40d150082d000350780101d020a000010410f244161043d4581810321030031940b4006a182e1611945c0300521410185052120f50f1100e2480700c28014008044601007021502e90a2020180c0619103103105a03000e182c04d03003130400409c41110228902140c6410f092421801d040208034042110340780300d590410080001030400005807181e1052107140700030f0a180c1da5444810468103018900425644200403e10501c0030080759507003084081011180b4508140c0c0b13000706a00450a8000d0090340c6449028031102c1e400c2d000300d855100814400c0361100b00c004c5a194940700525500040d00c500c0c40404900ca4 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 637799784 1250 637798534 637798597
    0x909150f1514250b090106080f06280e010b040b0f0d02061e0d0b13022104021309112b110f0d030f0f021903031d030a05 53
    0x8450701c0e200d48100001d0000c40c11401e0b4020030403400c440e0540f5001c42500b0000c40d4414000c9030040d0404140343c07030300b45a10ba007181c00319005201154040045c0e52400c80002441c9540103c140d842400341400040b4901064a8400c030034140c0d060070049001ca0014056020414040b02100c0034400001034606100001c0160100142c0242c084281d55015040040091202200032070b194100120600c0a040310782d008100d24210072a1a22030320300c2203241000740c0d50422007810303a08515101c88224602c4a040c2c0700c01d072140031400c1c040001425962009102550020028030500085126180c9000d103207440c2c0d10414800c6c20301103030384180b0280d50104482011030030000704540e10650b0300e44000300340b4408041c507844020118040f43d582c480b1044054914403070348500329000c0d0050390243c43c668604007001c046500c4103501501d4111090844078009030907040000c0e80f00a904000f02402c0350244039001248000100321640583c400c0040405681e0442c0b85984254500c4805804 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 637801034 1250 637799784 637799819
    0x150a02030c0906031b040e0f01080c0604090c091701140903090a1208160303091505060a0b0708131203090b031003030509030118050c2b120909150f 65
    0x141c5018403041a007400e0500045800c0420141c500e024401c50b4410600d0551087d00002d00142204051004030b070380d04842d65001d800d80c039004d0300490f0a00c0c0e01140d10f6004610800f903209450300e0204450350300a01e00e04025001e400368648240e00c0922595028207402c0c00d180c440c500b010000241080401301c140c4105280061900c4000c0345010480003009225400a49400c201007100c02e0102c041011804605440380c1c5002c00c941040c0d041c000c3d000031200c006814582c0c00c0030108001582c840148100780c03a580b00235540c0301d009500b080701141c05100038070000f03030481c404086010320740b40d0700d1111203a01c203070b441c00355950700c501c40d000103400280d03041c8044402c9058140000f074062005052003400190002800500301003240e0340021840d5401d03030701034011405004c0c580c03c00c402560018090303000142098030003541e00c810322992920001d0941e400700b0740c0d4840c205124405440042c9030466060003a12211a56000c1d01c0c0079601c1020f4030300c440c1c5000024003081d11070344c0600 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 637802284 1250 637801034 637801051
    0xc030a0503030f07022b0813050d0518040204030b0603072c0703020f03100504050903130b0a020f0d050c16060509130b1905030d020601050907030f1d150a0203 70
    0x31902c0d0b8114251403c8000307421350096020b00e000560f000d80c00701030003e01d1014003501045040c2221007014010344405420301d44204c002c00340305804642c0c0003880004c558014541283e41d03503044940301a0848061004690043c0001400024001c003900454002c400c00ca0a580c102581c980710b500c040c00a4988982c41c1c5000740c100c0704010348581f95030a500c029076090161a00f901540c040c0899802240d044104400d04602070169082621405900c83ca090004505e4140d56002c84818803080d441100f00c41d90740080d201c0d0030789109002c20488001050100c0303446c2d1140b01d90161680d0001c03500c0d15214480c00c030070781c20f100d130301d100d1004200ea449441d05132501c1800d6091140d108a07480100c0802900d0786980745494550f15034104940036500010f40001e030510b820141800150302c1c8400855000ca001442aa511803e4858003d50942400500d40c01c0c800040300c051f01c9a0183e071050000b07898a43c1e4203507140810031201701d101d41d155800040d640c4100d200101d0106941920 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 637803534 1250 637802284 637802287
    0x250f0e09013e09090103080d0b0109060c06110f0301170c0a0e2a03100501110303041e06150303210606091203020304120f051207240b12010e0c030a0503 67
    0x42c0d8a650705280540d1030000740e840545041c1466010800010b406e900803642c2c00000110f15401d03200510030051041824640440003a24114000300030741004170340600415510020651107603803150444420103034502d00030b0780b290703035a12042d440300d140d0008940950140304804117046c94541802d4068030380f00142c204072522100d200300506414032040556080252003424008082c80000d07520a60b1001e8045d5803140c21301c0c1c001003032200c01181e0b54641d50300c14814040007800001a400780c4500d410f50b1a0340d080650f0601c0d10142c03182d01d02200c440e4109402c00300500d9446858640c803648400100704d40401e800184030704541f054071904002035020320b01440700c0440c2c13409150485001c0e00c102c906007501c400300030b0b0788840e000404449030305007055040304004050201c102648181070245003012240d8079410420302000041245440355180740045042140c1d101a03140074011f8002055080501d101500a0242255046d850b02c03c040c00b813034440ca40000e00b84a899032140146 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 637804784 1250 637803534 637803611
    0x4020d06030506070f230304230c03191a090312010b0406081503060103080c030d1b140c10090212010f090c0504020c0a0620161203020c250f0e0901 65
    0x6010030b0b00043c00482740480d500301c00c0c1e40720344c00140140070ba0050440160552400c1402050f1401c041035030304030a014250401d090114007241c65004400c200c480c038204455550107d40c1d41144150030103012000c13403640000c02e503001c010002e082581e04c07035158140e0302e843d03044144010844c4103030110f50640c403c90041c0300082100e000340c07100c443d134401241e04254105c5141c005503565040100d107152804070080c403115500005012540760000c042c585046103494600d91106424103910000a899810765421515544030082040e28100020004d84c0081e0900d100030388030565058950304031700070012403607140a00c00c680e2426189030080516000d995520700280007034803000e0202c072180d0b15003440090507000081040381107010703205134000c0e03440c584030300700480d104480020984144010307201d18000142524585558840d04030003e07041d08150900c400312900040b1b0309020045002508010600c0c0c01d5015449840c003d001075400320980081081000c40340e130384c20f0400c803c43e8 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 637806034 1250 637804784 637804847
    0x5091002070b28022d0a090303050a020a120804020f030106050a0905040f0c0e040b07091206020705100c03060810021201030210020106030807200f130b04020d06030506070f 76
    0x402440181003901c0002c50042c0c401400498000c0c200000305a0814640410140c410179250340d41e1400b500344160030b08210b0784000b0100380706400300405003c400280c08074441e00802006412951003094032040c2e402d01b02c4000e01d82074068500700e000300c034070441403215460103004800c250781c4050304c8141140d02d8540100040c01014005a400b150404a0040403a011546000150400c460001003030300300b900d0a07011200004040e04204011810203204030300719190310b084030b903800050150b112420350402904000721050040241c0d0b203044080500700e07170182c010104a40004c01500d218580f409020400e0348101400006a000381d40e0040c00103140c070041c403c0c1c000d2094400014416200d40d074800407907100e1802034410341400d01c1c108d0240c030001010080000740076629038040340304100c00301d04030284400e5141d0310507442e110850055211030741501c04400da117003002d005407907403810865181d000c150350003000542c07030490b003215007401844400c0f12a10001046caa440d40342086 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 637807284 1250 637806034 637806061
    0x19180521160c0305070e060108090109030f050f16030e03251a0d020414040b030c0d030f0c05060a05090f1c0503040807080d0507110f15130209070305091002070b 71
    0x1c04451000303161802002160301001514042c140d0801d0300b8004d41000000501580001403030804e06a0410048000082e80030030000802c052a0600646500100425240601800c0e159002009001001000749039001328030390003010302501520015034800180d51402060800412025241e01104100d0b01000711b005540c02c4a0195461b820446500c2546050341d00c0350f800b809142841a410030010300c2c2504c6843c901c141d0031801414000b4014010882908100602070244080d00100c0301805000d141141d02095000d81a90b201c1d14150041900a105c01c0d501c51206219036481c7c404010f10000d104910a800344881d40703500100c1003000c0303485500c001c2044480c3d110a018020002d5800405000c00c2c44441c2d1012425283c0501c0c0202501c3e011485800c1941c0601030000040d0004200e102001e00d124035012503941c4d4081100b03203c4891208000d421009207c2002142941640428012030441050310700542140c10030b00e05034002c8580140c41d4040002c0425840284103c = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 637808534 1250 637807284 637807327
    0x80903040e190e160302100306030201021e24040b010e06091918060c0e0105160807141f05010807060807030b121009060b190e19180521 60
    0x400801d0902c3c04405807030a1600c01101c02d110501d501c2004d004510300f107001c84030030300c0785490200003480c61500004c0da0f8820b140c3e481c00c400c2d04850040001d05109020946955100c1c403000341c5080044000d101d82c00c107045406440040d0712500214444031542041801240020071980003a141c14100c0041a01c0045500400c946e580810780f81c61980c1c41c905104040c020a07001643e01448034020f0580c442c41c900070b904202041060800c12401b82c2c04400e80150046001d5403a54007501e880c8004028052094100340710b80c0521030b4203030000e5221038024400c039800602090b661503160640d180c2c210301171140801c10040004840c9480f0358000166031358024044114100091182420400301c80c4540c29240c0c3c035401c10600f844803601610704c5000003036900d40710b200c1c1c02141400f091409406901035040d001c0d4089410b21650000140005565403c2004084000384840c0d1110308040802c45060080d4070403080802d51040701520004c05090b0203602e020722100c510504c892940 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 637809784 1250 637808534 637808581
    0x90c10020c0a0f0303020d080c0307051606060915080d051903140a1d120f090a0b12040c0b0c070501140d06030809190b040510090b1207080903040e 65
    0x4011000641d4510080400802044803403180079401c45c10020308040d94903101c601403045680c1402140d070455400c40750f024810385045a2500c4500c602100e80700303c4014054000e60512401080d0440590302031096101d12100034200240d4909482e5108e1005902d6140465002d000841000d41036003008402c4591a1800007188441094030b903000e540103841001065590350f440c00f0245810722407001031462684000d00c0d440400310742e0042070b442030190040300b14402181c1010340e9203858010304060550910400c0d2912030740803015007001012142039501002d0403100040ca140e11781c1c1154403a40f040030142a886007480300560f45000310201d0401489c43c00c0101740c546050760f11865000c1d511500c20a82d8904201c002c10a035a11b1a182c0a0115000c0700c42c1040801000000c440484505840d40700ca45807060500346d07204442c075484020003020000300410017584a84080c0e11840340c239101d42c2500e4803000d80d056079a01540c019021010480c00100301da116081480300e08105d40c0 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 637811034 1250 637809784 637809793
    0x6030a0905010f0902040e010608100f02090a1e05100c06052203120b01020304050a09240612140114010e1504270911010e0a0305030a0c02090c03090c1002 68
    0x3195605400c50340d440c40f224081c0d0b41e030b62000c1411413406000c0e0f4040003aa9030003d01626062003407687c3c40780b5240c80306c0c14425a4406600005000c1c54058880d2130000618002ca402e503101050700d922103030b855001400380c0e142c00022a042c40d000504e41640841344c1d48004040c0d00a5551800400026005c44680000801402484d031103201030003110b41d01c6955a80c1d007480c101002c2d44c0555400b004840d040d904280800d100039112201c0700da0450310b0500004c00d5048030b13154a450421110810000070380300c00c11020541a8121898080c0108980020446100040b12000c0c1840c000e0241d5105410a584400c8903913201f040b4848880381d004141156090041606400552141c1d004031280340e42c10090201e80000c6100040820803204000e0080f40443e927500040c2e00d080e14000d60600070380416600d61901c1d19403c59000d142c1c03000032643c2ea00d00301c1c403014101c011081c00481c8201425030010342006110015a4000c40d0030038000c0459000304400c01c01020544c0e4030810441c841c = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 637812284 1250 637811034 637811051
    0x120305070c090c031508011815110423010201150902130f030f050706020c03030904110d0e030301050a0816050103021c0f09120206042a0e0f070e18010506030a 70
    0x8a11503c08110019180000c2c82c2c18041d007860000f00c1d0560060140f41d25043e4420420068100350001a6502c010b1071072080c1c1c3d8070b0b080c02e00100300c40076680140c4100804d011555502c015203501b00e89044540c041e050750100d038012070a031004021003022070350b100714040020b224550043c22030f41042143c00107a590b02c0300a030031000b480c10b5100303980c00101e003070110061003828015003001e005c562000d480d9800311000802d50382e10903454214026541c581501c40222410b10654a003041950000d02001020300c2d84160390741c0007805018030580626200150591f00051141c02c65142c8599460100385000019002508000d55030480680503000c0d04800c810a40305058501500100014022079203007480380d02094844e03801c4095511403c2400049200c0d101e1110704590740301c40f0500b900c00743c02008003c1c0805a0f2042c01200030240c240201c140080c1e02452117411039642c1d220442641c9001c00045042c400021744208180030010711183c00c00c8401594418010071002c14180d1 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 637813534 1250 637812284 637812299
    0x308030703020f1c0c05070c05090612060901050a0e0705010207090f1808040305011109091501021c0206060f1923120105060406050406150810031a0108011401120305070c 75
    0x80c82580c0f0300700503002240d10803103207104034418482c00303611742d00d0281d04029059850543c0b8108501500b803051811100040b00d82d80c511804508100d0702a09507049400c107002054041e003015910324040034140780c018a40380c00d001401c0d1702103d00c16801400c0461401c0300020091200c0c0561000094941203800b024003051042c044495104048080e9154950700b416803c55825518401d800c000810a85050f40c2c0c0d84540030303810180303142d41d49401c80c0031000140e180a60903d070b000e41c0202d0b0080800e800c0b94002c610203210388410746035100d039084090b0400000d2290010502c0300000183c1d024440030307038522520308101440200e581e83c808000d0001440710400cad2120080d0b03503074580b4200603140c2010b008880007000151340502803e403e041d40325910151089d681f8003042000700000d02a865100c8480f4001c54010700441920415501b001882c10b03000d000c3c0c44d10a60800380e2100e000500c40586904071202d5103100101c90b50b46544c12919540500c1d015141007404041c04540b91 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 637814784 1250 637813534 637813537
    0xf1b010c0e04181703040c140a0512071a04050306010504230c0913052a09010f09030204150608090a0f03080702012009040c050301031226070e04050906040c0308030703020f 76
    0x38072203130065140c1ca482e00d450f001410064001007103a4041280841e5030303449980c0a0004d55004581020308229800d907a80c0c078204c070302c3e0700100c440d8101e01805003101950400034403d548003a4191811a84c9800500080e2842c460024444034050707484502410030356208644c108100c801a0703031804441c8800903001a041c001c1d0032440d81e503141c040c0f1801200d036240440c0003074256003000c45a9000c00c0c21450141c041c045481e03050084100c0712102d0036206101000103554001c1040068441c000c081c201e24031410302a51020420b94404210010300000b0207040c0ca0b076004252070700e40809a60103d550000261010056640f40c96a00c0344842303019100d0180c0d12001d00c513183d20b0350b00031810041034904c8041c200042c010200010b1000c15490801030f080603c86007405400e440e103603402c00701c2080c0c1c0e22111441e240d10603028041c1c00b641c0700e80c880441660807542402961114035120f501c640061780d0042510501003000c00c0010040740c090355000c061400c00508060400c0b8170488207 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 637816034 1250 637814784 637814813
    0x20903030f1804060e090604110d020301020c06100b0408101116050105070e1806061602030d050307031a0105031602031e03011706010602100e0a02060f1b010c0e0418 73
    0x40450618900b491400c2a01c50304000f01110300c40c049050800112494079828090070141c24003440014000c01501c0e140c04034004070740d005c1d0003150b039030700b04089540c1c0b03a0100744d400c0d840c0f10940b0440002c0d4091405c00356000d0780e10307040c06041c0505038001010b001382455040c04101b68010300007031000a4410b40c0054485014800100346407511315402080d8240e50f408081c41512525264402ca4400710700460b4444019070303495a0351030703015a03640720304102d40200a5061142000b04000c02d07a1246c050745c0a005161014816281641c030f4580c000b400e91a41d0314000b031004e200007011a0602c402506040380c4a0040e64503002113540705441051051035141459038000004100d00b0408103521800040721070068081941420002911166030201140a240d255445010005d00c240701d9000d03c2540100320381d6032040103503028011604600c200d0040f401084800d00c02946040c0642c440c01a802d58a441c00368008100704001440001c0416656000f030b01e0a2100182c1d10300001c000 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 637817284 1250 637816034 637816057
    0x902030406140a0903090503010513140f010207150f0204030f02040209011806201506190b18010f0207030320010609020d05040212010b060d05150a0b09040f0212040204020903030f 79
    0x41c1c40f134003424050003008040d07000a0003a850613013001682020b040d42a002d0f40d41c40004242010514100c0900d013103040704021400e9440080c3d0641044a40c0c4040401c400300002c0600404050303140550881c002d41c84094030a40e800144040107140c50350040040c42c00506103122a1100c019078072810607150b401c50740100305041003074281ca805682228807402d1152004102140010304105500c41000d060b10b4050180c4007030b1003514504800201c0d0280c400d0399541500d0308500300344500c2a0a0040b070050100e005034102c1106584049100026681c01d921030810b59004442c00364508140010011459540e82102060000041c00107003000c610000000c42d440c14640100113091000c03a02d401c0c0d050385403200218030b40d201c2c04159982000c5600000034681d82d003240e002402c0c14103c0a0325400043c224002c03924010340c03c043e10254409440800c441c00d01c0080d090100d209400444540c0541e56001400500d480e03002404041c0b030103020b4904000d4414040841074010301e00781503 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 637818534 1250 637817284 637817291
    0xa062d0305090c04050907050f010c1a07091706182a010e03030a080103080306010e180f070f0c061d06040605310f0c0b120103050c0109050102070902030406140a 71
    0x52050b00300001c428121003214100030505141c2c1c4815525509889094000c208207010100e4a0780030780601d008003030300320340c040d00d0103040401d95101c3d02000b142c4004c08908004408610310040c1d5a500300004155070080009480d400c04a5a060700c40e0702000c0144c1c4a00d010f060103468030004550001c5d12000b8415810042143c0050304190041b02c103a806640240580c00010b90700442c40c0341120b0b00140c3c1c10f81d4030348508004075580c0e050b00032030a030020509545038002c580d54446107403113910004a541059102c510f021108036081c0042c0d20b00203a0809200c0010400581c428490780351280703560080c4200e040715103402c2a03000c071015600d032030342c40b0100a03201e041280c000c03405c240c03403194560501c12100742e150300f82c00450364060100ea0480808100b0440226500400340c602d44e0b079401d03110308207803400350b805480c02d0104440b07600076071358094120b50040c0e0440041d00d80503000340180341c0c140b0789240002e405c01842556910b4450b414408401840012280110030307980020 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 637819784 1250 637818534 637818541
    0xc0b04080c090114030a03030902011404080d08070302091e030a0606060804060b01020a0308010909020409150b1c022103190509030d1d0d03030209090c040f12020a062d0305 76
    0x11102c41c168012190074660788018840c556000c2803030b034440c2da49810002201c8040c3c0c001203c4502c010112000c000c10b00040201d140313900080c018036050010341c1e640c002943e8104048069000b1070161a82203103202d40c45006002150011440501000e0200c5a055400d9107a01d011307900541c3c80704000c14440d00901040c041c2d180208081c1000c203000030141c86966942c01002010140b007042c00352641da40a0504540c1c030384d040000350325040440b003401c1c44404990300004200c0d01d0f1030301c0e114404405004100382411040c0d103202c5a001450704001c0d6411408240f200c04504448081500007004030880345520101c40c0c0e241002907035100c94407024484245842d00c0c488240c61000d0100200c0d400301d00399007107460041c00040603500c1c544816003515042d0068003540000c60307400401101000710007072210b40540102ea010204d034102807540c0b54014148850400f90203500003008100921180b8010001900f82e104d210018691402503030249070240144002e228000030f4440007071 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 637821034 1250 637819784 637819789
    0x10207030e030715080a020a02030c150604200f0f130303020d081e010501030b13060e09120307050a03052e06030e07060909230a050910050702190c0b04080c 69
    0x2954003604907805200654132030b0391070262040c0c84c010b142012454001462103507052081c0191150070400d881151980216400c800301c0544046810358001d07450200c90150082000392480c1e2070004142d28a03103402c25000c01040c032075010b58200240c00c6420130456a10b400c5200c0f400c4019402940903115008150000030038040e009020340040340e00d1400c0c01c10381c41120528403811150b09090004484800402141240c0400610400003a241440004a08200684440c441ca0134041600d407401504214510316010035140300f80002d0003407004850180c000c1e4031040e00855450303001d65023202402101100160300c1c0260a10301d0048200330880c281d014044c040502c804940986900c42c14007038020304040b1644241c6c07201c00d032200d00030740480c441181c0b0304040c03003029071403c042840e0003903621f8041c00c01500c200100e841800405010824248100d6008001c2c030360150042c40c00080c00d080c1d00d0034880400b5030b02c14201410010700080710100600090200718068403d81d41d50204 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 637822284 1250 637821034 637821043
    0xa020907030504020f010e03100c030e070e041a060a0b0720011407150e01020705070608090102120414070b0d09110f06070b0703091703090c19060c030e03010207030e03 74
    0x403103040c10300b420b003804011381d42e0071009441ea08003868070780c4400300c88000082c600200c0364000011380e454464402001e5516070001c001740b0510f0012944455a070384004c1c00f180d03404407000b402c000d98000100700500030400000b81c004200520f100d04035510f5092402d019031000c1c2c8100c0c1c0b50780040075a0362401e10103a84c01407004d2024207191850920038075149281c1c0c0b04856009040c5400ba0303181d40440080e80c0c0c0544410311080c0003c40d142c80041c94000d035108414041c44020131110400141c0d0070405000b1101240354492042c1c145880c1c0e40d80305032121409050091060045280100344521800080e03e00030314002d001084484030381c1000c601400c041142c280c0680080103c8200980f90b001c1140c0c5c1040e480030b03c444455588110450043c150500f0007440000080b46a96418112001660084c8035203001e039135030f000c080c50810682c2071088a11803a0030030440008c22800740900500802c0c0d9000b8140846102c28001c0005d0880c1e102c0e220440208804501017056400c0412 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 637823534 1250 637822284 637822291
    0x60f050111010603020604090c0302070f4b0305070b0c04150201090807110307080d030f0606020109050c0405060607210927050c04080a11010f030908030609270a0209 73
    0x200f01c0107040d81c010a00c1e034404d0b4041c00306d00607203e2010101c4107109504540d034103a00100c1d0f074950040145058000311680c01c2c9142d501046403542182d001d40d02001044c0203951200c1680e140c9101c0680d5070708030500010702941031243c10311014000c42c000d184400d2040f002406407954543c00c01401e140b851a541941204581c584198040010002000c0724200ba42180340c0740c1c55100781600003864541c0d203402001daa0300519940042c0c980d00340e00400340e100700a450600c1100e40f914022402c0303e520801c05440c5500141504001342000c2d8441c0750071500281c42c880c90b00c1040e4441d0740c0c0100400b4400580040b14184030200141d02100c118050700c41c01405901d440b2902c40e551642c031034400e00301550b641d0303504081400010740b0b0f001c0301c00a01440082d100d901070642080e42d600d818420506001c0369a144134409410320906c074604107540d00200b17081c02c40e200c60082c03120442006081c200401c031528040c102c07895882402d0304044070303450010a4006a00d1040c02300000e00a03 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 637824784 1250 637823534 637823567
    0x915081012030c02040b0319050c10080403020607080a021614060a15030b2706091608071419080f1207080715090c08161d160210060f0501 61
    0x40d000070352010f164a8a1030301120049020300104000905001843c49841400784800201604000010403410f10b010700403502c1c040150034003402950b17003500840b03000b801a002200054540c80c015200582c12804103d401410010800300e4011102c1a04800743c46040e810600e031401c0d84020410305a024409800522030b600c200d60070b4031118900c5010040507200c1c00c4c030002d0701c69540000c0004a884040c9800060002e41181306a103941050b10103440b0350007a0040300841c0d0300310901010449002400514000e49400000c032046103486104030b90180c1c40d03c4503006145d40c045242c4000e8142c40000c2e2500c1c8818503002481c1c8101d070403155910b42c00a008100100d210001a1008c01b904040e5004413400c0d007a4401d4010148220010242140c2c64000311f0500d40c0014040108200c200c18140702a03141c01aa83d0f40c101e490050040c1e01600a000500386484d1704030105a401150048039886880ca54408043d2481034102200d84243e0040802856a01c4049040c101d03a02c07 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 637826034 1250 637824784 637824809
    0xc021504050a150c12110303010e1f151b050303090d020d1b06091104050901050709050306160e0a0e0108101a01020601060518130b030d1812020109150810 68
    0x32140c0c0034003445044480070f070840017016160b8400314084c40886180005480c00e40c4d64a43e1151020045e40c00b056981400c4039498441c038a90b080190904a07056980c1c50f03a0503400d0105018017141c200c007881d0208900b800351514150000b820410145024100d400042c0080d2428080028078004071010040200074000000c4401c07100660340b120300140e0001c41c00b2500700900d00f000079500140d103a03426041032a003810002403a10640c4041d0203a9880da175008501035590007050fa8848c016030360503988041a180d248000c40c000e1f01210321001000c0c1c01c0c00001981d5400765441c242d400d910502450b0001c01198a80d01d4080c421103850b107004600b40e60042c18070000007540c3d00300500846050003000201c4a003442c03058000c4851440e030086c04450a1150303000800e010b0440c3c0072000d03002e403280900300910a13001d0450700849110311071800b100c0518000035192418940c10043c1d040c49040c04000c544801c0c2c40d1901c5d00c5001140c0c8070200181005003881c4e25a494a50005000850 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 637827284 1250 637826034 637826069
    0x7171b010f0905100512040f03081b09130608060a02040503010606050301120308071e020106090f05220618030c020a0f1802030613020412030905240304030c021504050a 74
    0xc0010b291400d0716000e40c0c40b002c8000c40c0c60802e40740ca1080198622000c00004104030401a00f80040a9a9442540ca016064640311080302103014080c04421980c130040c49021210704040305014000006e0000100300345a6a02104e0304281044d227424424a800180601c10350800340580b1004100ca403526030701d5589001c0d03050b0194000e001c401010000b5a03004100342034411515811307910008070038508905030246020340240342c01e102d046491400c0246140c40c0b0741140c490308d44160240c082c0b80b048165065401e40340b80d080c0c418100c035081d07610113116030104080d5903101c1400d80300352a04020103c96004009004403168489104008030040c1408080c0400070480c01440340c840f0050388a450b8140000c1c3c2c48100b401e59000c2040c4080b4000905140400012648500a8481000b8244c5600c2441020000701d0284840c0a20310310001c1e158110100c000c41d88a4000d242050004800c2c1e40019444480c250b50201c1002e0b021030103008518150541c07000911000c6440c1c1d04100 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 637828534 1250 637827284 637827287
    0x603150c09010306260c030a050717071a0901020609160521011505011b08070b0a0902031219020105040c1a25141f0b0307171b010f 58
    0x3004060000404680c008003640241c0101001e0050808107112941c04403d035200649a502026845803060a0a040d4a42004981c4101d0580c104004c0e08050303003001440c010000c5014031003a909d03c0755010001d0032401000c07458840c0041c2075085d554074803042c0002882c22030054103860403600890340024820780d018900c00c080b40c40a807240506030099440c0c0717001180c803288011425500781000318440b424181815410703104240c944030081c40d0090b8018401c1d803040e000c0140862010080d17000800c00c5000a1076201050790702c0410300100d80d40c00709041a8504042000b5041c01091450300c910f002c01e51042d0101e000d01c000c01c5603250541707403050303045920710491130803080d6548a0924a00b440d011186110740c7d900140400c1c800500558000054881c015a10002c1c841c0307900414107400b05011680d0003200e10034040d6038820002660040120094a650600c0340c104001100300d07668020741714080718075000d800c510340450244031501c0c0b565980e080c10042e40340c0d0030382a41d9 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 637829784 1250 637828534 637828573
    0xd0b01021605040507050c0114010603050c0406170a0e01091a01171e01020f1303150c050901030e1e03030f0f010506030f0c040e1303090801020307050f1e040612050603 74
    0x2c90084a0100c0c440d02c0d5401c00780c6452146800b820350315401c5c039071444541d008290006040343c0996408014982da01400740c41c0c1801503005800018040800000243e600e0300041c6030131001228000031807c1c0300f03140b06400c40f9416038040300d250b1486260501801d10f0104804e00410b003c5d40303401007186421243c5615140f031008000f80d411001d14035800c1000c1c095050f1043c035400b41244554500c401c0088c5569111107104c101c1d002c003240d2101c42e42113034150085a40c42c13503ca071502420320b40042c005601501c101040c594043c030820b5041c50943e10165581008440c514014540d00d09208003480000d000081c43c3c240b001d0300341c000402141e202c42003143c2c1e1158145010410341c1e114201c16236200d2140c0c1c0d01002d4444a03400912180544031220307948142d00c00d468020150740d50715080b80c03c1c0d010032500c3c2c4011a00500c82c40ca246045c010003010101c032081c0c0b01800043c960f812541d6540c005400101c009070304002c0740080b000891040d1600008110000c1220001c140c000d981d49 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 637831034 1250 637829784 637829789
    0x1e02070e0702062a070b150603312003120307090509011409010302010503041b060905040b0906150d0f0501080309010f0e101d04110c071208070b1803040b0d0b010216 73
    0x210881c440001c11400e24801c189800c054000d001c1d41d5032b400d0001c4101201c215211113140d0b10030040c050f040780421402c001504459100d084035010b5000180511300c443c01080425405010303030b1040e400040c3d0140e00451203480a0740381c0c0705415007404140012a44141c200782000e20903034140025513070b20030803001d04513a1709190003580c03650742d441e00d1440070400c1c0c2c421806140c03601401258540d00041d014040e03800a0b00c080020403901410019010025100d45070000a15894900300c0034200000701902240c1d04004580f44814250203811201d00742c0c00184140c02c003103a062082e44e4448481c078610f030154608403000c04412000a40301d282d090010209100c031041c0d0321030f4902c0314420401d00c0c05500800420001c011134011541941c46072800300600d00a144020407920f294000d1110859045035449007418119600c1c0b03421810003501140b02c95070003243c1490300c544100000d1000e040705402e05a16040329000d5442034500d510400340c150f401c40401c0e18229031854400004 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 637832284 1250 637831034 637831043
    0x201110a0c14190911210417120411031f1d1f0b01140d0606090b0406020c0405040501140108071a040608061306090c18151e02070e0702062a07 63
    0x81c1d03208135400841c0d070f900c00d400882c1e02c1d080344d10701b40528000c1001500b44c40b0385e0103040ca0290250040034505054883c040100054940f0300e0041004120001c452907454070307000e8115040b241641014045d054081d009000c10251109092288240f08500082c08035142d0b5004100c802005840e0610429041c1d101e0380e03120756100300340384441e841032615420070007242c4803081d500e811109410300500228014200032031610580050f1504001003140c00302d881541c041d003a11054242080041c0c03d01801c1600d4941d210f5500d24105111000180e0082544030f0042c03001600e46405201c021071306070750440070380321700b40403c02640b5040301d5119401942144c0c40f820a040c2d0303200da8402814075400601d20180340191203528190040c80320110034480d9140303030700070650351550b120510040d90409000106c412003410b2442103100d040b21446003190040e1042c013903c405040d005428110740740b0006034041340c14400c6121403a11111850088142890781607103001548609901c101c540090 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 637833534 1250 637832284 637832291
    0x120c020d0f0828031a031f02090909060702100b0114090409141f0203040804060c0602040801020f030406050609480c0d0801120204090201110a0c141909 67
    0x20100030000044489040d81c0d2031180c0101c201c2e094003c95a6030240c3c2102022074a0010300d03d22004a00c4d44082002d04d00038003d05902c004840d6122145c1d0724070558800742e40d0244243d0160341d58203040c00303220700598001081c851a181800030301d00040c0010708083e5a240041e120000d036070100341200506007190005546135060000f26000b0a01103101900c503809100d0701100c3c02d5004900440c583e40861480c40440d40b0900901040748002c0c0c5000b000032a08001c1000884d002e441d0f14040345006000040c10301c2c3c2d840e140390b420781e0b000f0214126001c2c0300104100400003140305454204d042503038581d603030b031401c0440c0b4101101c414001c4807109040c04041112100300d86281d01e449816040b081c10100503c2d121840c080c1c01c0744180042d0350142e0040244001d205042c0036040310450f1201c240440079035001d000051401030016410847c0e042d50201104904015801003148034055003200c00b07141403c02c283d500049607810740300d6a600c04403101e60708103101c102c6040e107107a0034002 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 637834784 1250 637833534 637833563
    0x81204050a0b09060115030203090303010e0c070b0a0c030f02090a05010e03072309220609080409050712060902040305030306090604240e011203020d0e0f0616120c020d 74
    0x7480c02024107401001200c16000700445442d02090b240d04032034184980302034155078040c00b9400e9003c00c0f0b13074808a503841400100816003042d0709403504181c4407504140b40c2220790316030401c4600c3c1183c594102545401241040c141d00d0705c554100e030904000c0860034440b5000c00a03920700c10074031031070303040059003031104900d0f0740c1c14840f0600406c07202c401040840c0044c0f00c0036a00001e6981d1007032042d40303104000f460174003600036040c0c1d644402094484d68020144e40e00030040c1101d04098030f05003800e010120300074550707104480c0240100c0d1580c600301c1d0700c240788140a4940941004107141d0052200b00001380300001586d0300b0040c21210300710691b5a003000f0400038600c1d00700d00b02603506800544ca021030351416860090700d90700120214036a0300c0b402c92890940ba03040000300180e102c41a0700425074800c042c0102460001080d00c005c20072040c0004e010303500541010200c070703603400c0581403c00800b000045068295800c0c0040d0550054002980b641002c441c003506030740304010071 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 637836034 1250 637834784 637834793
    0x20c0a0318051c05010507020610151418030d020d09032301110a030507030b01050d0c1808010c1106010f0e0903070605040f03020f070509071413151209081204 70
    0x10003000d041c014010f901d0542c00b80540c5565580c5401c010340303440d403134800031502d9548042860b500c02d00ea17405603080f1182ca0309030285d54203010b0039802c00820505941030b4103c44115001002d40108200d815000c0111382d0042506044d40048244155805550300862a0350409084403c49420420300c09421144201e62820005003500440142d440c1002d1b04140003000c1c006407401d542213550400155035640c1c015821640915280c41c080b890604c0700703016240350380e0080f240320b000c0c61811101d0303d4a01d0401d411211142d802c42d500c1651a501c3d403a2549500c03049541d5201c0d0300000034441c1e540b40c180050548840b40c00340b549002d000741d0008444101c1001103038001035122404100e103140c2400c0481d4440222f03e4210014014130b040c0740c2441d1000a0200165900105a100e154603102800e69041c20f00300f440207103d80c0240b0a82980b20300e80c2140c00d005208443c81110165100b8100419540d22071214503007507403404c0b0804022449840c191a1906c00b1100c1203002900d89080 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 637837284 1250 637836034 637836077
    0x6050d0e0d03150906060c022112030a0f1e020703090b04031a01050904022803020d060f0501240c08071e06050108030f0313080c0a080a080109020c0a03 67
    0x10180e00a00c1169100a00c00b0751541c4180700d5000c8080f21103407031a4035038424400b03641503071044000103040402540302500d46606000c40d5510044180a00301c0d0507803d801d400c00011540c1d0010b8054040100700140b00c444c02290004580d2030030030094040c8007445400800d40010304c61800c2d5501040c5102014000c0500d800980070422071140c41e950740713152100107420010841c00d60f0301c00c074000004032070401a07120f50203158010303c00c0700200d40000308842c030304102915401505804c03090001c05600c0d26002c50030034900485d00440d004c2d082c480290242c1e0410b03409030116011500b0710b84c5061585103190010580d1500d004032500c80a404d0a001601444001a10f40b012080700c0c0c060800360f54802400c442cac401e070b0341800242c0e27030b0742c26a0303849000300a08041203c00810008852004048060f00d45902c501c002c05c1c00d0400c01c4460343e242404142d404c90b01e04034001190103c503a0860940750050040d01402d620b08104a0036203a1603007000c0b0002001e00082404504a0052a05 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 637838534 1250 637837284 637837301
    0x4080a02120c01020337151809050606030a030f050d02090405070509090610090b03091504050f06011215020c0f0d02010906050a0902060702090a024f06050d 69
    0xc0070070351030b080100d60700c5000350710070f6071407061320749030002d2881c0c064620126a2200c404500078492a0300740d08040203018040c0c17400305400800a0f2032000c516100c01d16005640148458800070743c001080c64000d140020180c43d42c0e00c2680000c50380000a9400000e400484200c1d180c02c545a40300301d440708019004a0000c540d015040c041042200380c7c1c400054800f00c5000c442e102080d880740e03014401c1d44c28210031030702c000680c1024107000300c4041c2c0d4000e6420110038812142d8076010031045401400e8252022101a0003803905a240c110302040300038050046e4250180792401c0c243d984000e58001d08145560b582c0d004904608049400d10030601122400300641c1d0302d203202030b000240204071040003280d030305282c9004600403030000e101324080c0540c044d04031071500502d502000050030006004244d044e4003044000101220744544a009140b1103041c3d9038000344110791000891050510301c24442c103200c0c90142401d16025000d42140c0300c500b0282c4c0d40f002501800000b404c5400e = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 637839784 1250 637838534 637838563
    0xc0301060f110d12150810020705072114030a080a090302010b09012403110403030503091204140109060302160201030515031b1924051b070302011e0804080a02 70
    0x10155403090076000700b081d01386030703030070700402c00141c81c4072910b03000c1c60409401503140a40c4054898041c1800a900034181507000e402201d5000e42d6800301d00340a003506210410a0703c0c14000641c0c100044003c07031f01203001440d0041c1d4100205817500901c44030f0700521074102c0944070107000782858001e5104110113000030342118180c0da12740107500b0601c0b855070101e0003100d20440c100800d143c484d11901554404002c010391a00d807460310115842d41001e000207030720f4040d00040c01c800c070115074000c2005104200c1c075072074030701204030000d030030101e850f402002490300412211000d01409610f003e40140c1c24203000420791189a483c0c55851406400e482d05131007080e40840c814000d10207002c1120354100c440e1100003011341d54241c80409a449002c203429910031818503000100990280203400307031f10300b070740c18903503500d0022190f0700700d0100b41c0c141604015018400c1d968401c43e1401140c94800a94010100c1d0a5004044003801000544280b1022031042281d03442071107640d81c1d840c0c11 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 637841034 1250 637839784 637839793
    0x1b02060d060e040605060a06030b06070807050f060103150c030203041e140109030509030d0e0306180c10050306010306091b03020304020d0204020c061f0e0c0901020c0613031106030c0301060f11 85
    0x1850488000c0170180c850920429003c4000210380d0701ca4081c040360000301034030300c5091035680e603100203281d049201d08845900030304001201d6280708100880c0294040c03042840302480d03020082d011528980d14000805004208000208810b9981c4194402000201d45003401d1b0505009604200003010700303583d075080c400c51606156000e40903185503a0210141c1d900030051403c2a0b841070805014950141c0250300000d00e512007011044000300345505c00d4a2044046400064403804107040c104003140d004014031805583c1440341c4d40107845180000c000f0601c1d810403600c207c2d8041c1000f0f5041540000000b42107440c0e0f08240d00544c0d40c054810764035641c500401c291104000ca40201504180344191400c1451100715001200d41c1c882e540c009a8882000014081d03014940e42415032140c1c0042c00c8290700e413940280580c83e0f803007440c6e5980509514103103154070340c400b510078450b480501c14041c500b50404101e0341100d00324102009009904441660300021002c0202958080c = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 637842284 1250 637841034 637841041
    0x1510020c0621101a0a090302130f29120c090c03010e130c03021507150e010b010207050a060e120a0b0103140f0a030807050c160f061b02060d060e 64
    0x1000380b42d010044003114207402c1540c6100381201d048449200f60400c1d8150000f00c48140326140c3c00070079011100d49040d07a4825242c2e0003145000031010900c0390850f41d204004000f0140354450b42d10f0741000b007000c00c111040514454045020504400e901c01c210203580c9241c082c4081021004c9810058a00940361a0203503405500307800074860060403001840c00a034000216200104c0303440d40c0800c4500c2d02906640a02c0075501d054000c80880000c200700400105803401e08201940585a01c0800c1180b100c10810b820b44501c0089203055500107001440785070307100e400100641d100c2d8900f002c510004803001404403040618900c501c2c0c01142c8800e0103000c0e45440d044e0680340115440c00102e00302c90305c1d559490540bc0d440ca51260490010000040e115021072604030b040d034076103070381022000c10003141000c458072104800044c0706542005a280c001c25008000c02048c1400e5040162150345003106220340b9074003c0c0300310300c00076050f910413000b0b91040c806410009030941c1540b5 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 637843534 1250 637842284 637842307
    0x140408010f09031103042d230f0f06030a050603070b07110114040e0403030917040609080f0604050303130201170f0604060816090905031209061008061510020c06 71
    0x510703242c1640001d03ca4151414a102d0000482d0100c81d41007003030700307103011600d55440c0100700040c8860314001c414140c0002d0382e0144280a14540b00c0708901822184040c500f003081c07070306614490038040c88890030f00350000c0d0b07900402c0c0c9910850b60300700801d041c0c1d52400001d0401200e50403504807440c01084010610586400c4824180b03820388840c110341c928448407441500842c86144440c4900600080010703100742c00c21940e15100c6d02c08200056154001d41c88250040e03003103600010520030040040007010800070003030300c078580d01030401405d007601e84030340f2484018901c141c4000c0070703d040021640b04501424070450402003140c1c1b80d060240305448240c03c00c0d03e41c144074604192000c5000c1a0108102c074401c202010041a003918001e41600504001001911140024070004000700f408081d07151148428601500d03203854500743d41038445483d9080400382d540401e0802400345010300d03484086c11710440d400c4511012940b0228580030306420880d80040d03022443d0034085 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 637844784 1250 637843534 637843541
    0x41b171f2408210405040e07091d190308060121050408090f03011e0c0e060a03061a040e0c0d0e070b0c070905090c04090812040b06011205040302060106140408010f 72
    0x2c0721820103541c861540301050a264a070204000c500c41c10003008104400d2800c1d0f8007881c0d00c802481e0aa03a0307411394a6819404451a03115442c50b109040c080f001104101849082841c540845102074020b07141e440040034031000a01c0141480416415980c021b030307502028a0000480708070074080c0b8902031800c042a900486403c5014082e840a601601d16040c0038056030ec07429801c503284941071140403003008c0c0540d0440d0b00d040c0850350348109100d48400b0001c0c40d000c0070320341700416140e03e08034801c034802c00740d84400c07404854103000034822a107004050035049643e60800300e459915803440c0000508003000140070501c0785841c00034511000002424040c1c04640c00d1b00e10740ca43e00c80038001a210100e4504203180c000c00016110342c0381640c0544800f034000d06919007003480940b07440c080101e040d201640c000382c0c403000308040380d030307000b030f40d0b11000c0c02e0081003407019040c60742e030207507486c6410b008000511200740618603090401000340c80007091040020b0204040130300300310009 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 637846034 1250 637844784 637844789
    0x2030f030915090f1c180b120f0112200d05010504050d030213051017010801050f3702090a030c031202070b0a0e0a0e041b171f24 57
    0x1220302c030000510001004510802e0400545014000b000000b000e075034403a950b4055200c090000740c02c80c1050358142d0038a00c0d8098008540c4480e80c1c2e080c113140124160000400400c00256580010b0140a50003201c0d50411580805282c01c00000c40c0301400320031105403410740d00f040441e0322650511074150843d6018074000c105132042000c482004a0580c8500602c80f0100404100200110300f000c03194a41e80118a00d05605944030080c00d090307542070203a00405180e034542c41440240c14414140c29041604a03140102002039100c5210300007806400b40c141007030f51000443d224616540440b181094001c000c270340b0035601d03442d001c03140703003294003040c0c603184032451224401c540001015000d5462411246040410360401240c182022030720844d085a0300800004a00f0b02880007240a50300c20351400b0140c0a0200b50640010780d20b0b400b03052043c8a1080c0d02c400e03202c0214070a000c0a01c2c5002110000e00341d8242c07807015240000152006902000d0010817921191400405 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 637847284 1250 637846034 637846063
    0x204021204050d09061e0c0206040503030301151439010e030d0b060301051c0311010c0f03141603021602030a03030e0d11071814180709060308070605060102030f0309 73
    0x403121784030310007280d6081c1202c1c001c0070700301440e10502c0c1100d40901c81c4c1c40000c40c4010f0800d8640768076140403d06541083c1e0110f4841130780403220002d1250440c480c4881d0031441c2c111182130848140300c00581c24410290807030901010030813000181e0310b0402e120b805c0d0810030000c2c0611124650810b569030300910300800d80518101841c1214907180c01100d040710f10003805805601806080b000901401180840c10710203d4a00d406078568280189005800c458440701c0200d840340c000901650a00c01020030100228001c100c0c40e03032403058000304c40d440940340040c0c4070a941c01c0320110303c10000401035418840c1201842c105603041c0c0000007428491070644034140b0fa02041541c1c21400c0c4842002c47e41c0180d401807201e002145450318401c400d40b135001c01d42803011803102e0405907054410001d848034801c40c0c0c60302000c040200340c000304607450b4104a8640b071070300d8081003400b0b0020000c0c0034603118008075025a00c2013064030340c1d4004003031a85a6034200f071040c41d43d54005135140c050 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 637848534 1250 637847284 637847297
    0x150c0a03150e0907061b08220311090c19260406061a040305060705091c03080402011409150a05130b0316050a0e131104080604050f1f090204021204050d 67
    0x505c207104600440940d00b14442180301d21115584004660b000042c404001102030110b244000350b6200e8200002e6008583d4941b030500140c0500c145980028083d03a0155810042d84800503030342038417a0380e6107013245031020b5140c3d86034440b80c0709003a8042d104140c1041103414402481860b030701c254129140502d2030f001040c10000080311a0089d480f02a100d90441030000b0440c90003480181191000204682802d04441480300e00c0190340800031f80000303680314200411540c00902c2295141c10392642c050803c00c0b45400200801c01031801d0b00306c1d603400801d08449280c058000e9454050440341d5203a0095107a144100140c0c008a070304401c0046e10b4000300c03901c18040c42c201c8202d40090754070007500020050500000f4203507010b0702c466543d41c0c0c40400c050401030202a1001e8030011026066034141410800d00e00101020403440c1038100d4201211900c101110440d00c0c0342d40c40101003810302c00d5000160003805018811080907a2560800040140c0030a42d0342c40450a5116903 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 637849784 1250 637848534 637848539
    0x905040f0902010f0509060415020609120c07031e120513150806060304171602010e040507080103020d05070e10080d2a02030120031008150c0a03150e0907 68
    0x40103603070303030404064041541001c04c012203500c1a002032040c80c00141c1030a02e025600c0040c3c1c2c402c08059191784006820a90074028407000500c03810350845040c0b8641030804030801d070070a4440140303110003032a001140c014800c510074a00929000c1503040b03800850b05800c0c008d400391599104c030035101500704003080040b4118051441141c88800035a50380c141c0e564030142401860b40c4041c0003600d80e40c20280103480c0c1800c0f010020120071f01c002021404004d0300f4400035280c103030501e074040c0c40b4506000c10440260340c443c111604594040f101102000d805090460400caa9604200c1d4a150603504001403812606040d0082f54902d500b16805004140f00480d590501288002101d9800c01d901c00110201e48892050081c0020000100045481c15801e03c114594120011000c404420001480ca03501000001407411001a0040001340b0715298050079000b001c0102c003120102e56900c1d058444d610003000301e050104580700c1942c5a038505104d400046070601001e11404001 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 637851034 1250 637849784 637849811
    0x50102060c033607090b120c0603040f02180708040309062f030906160501050105031506091302220b0406052202130909150c0509100915090504 63
    0xb224481c1001081802004129030400540b943d0348141c400c0d44821906002040001c0c02c0c015180103080308040005c0c2c02c001c4ca400d0000d000105030040ca06900508080380702600d510048a41c000d0340128500e210708003d1000031b040190703282015030031030031000030008050707045070040e80554001d44440481d83e951303400441d040c600d2448003005102c1007084206401030000748000e65600600d003901e080920303070b0001c5a5560007980060014159008600b41442003e2041d03501509040e005000d0042c03002009030b40624020303084600580e00ca80000368084070001c00c1d00104c42c0d0080441ea40c1041813291b030300301d040d00380f038215800b2450076803c00c159103801d100312402c039034001d4000400c0500310207010781500300181034291620340800c500f4441d03000003028070001d4810b5140000c6c450486040c00d80780c42c6a00468000070701e1602e00d5030303080190000199200340400b04d607070060025104004985440c01d561001c000400d5084040122a8220b034030041620020b403402c001e0301d0780c1c00aa = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 637852284 1250 637851034 637851037
    0xe070206101212231c05010b0a1112030103030302070b160e040504080d0905100c0c0b0402090a0b03100c0809120f0d0b150c01150f0504020a1b0309050102060c 70
    0x8030310300d40742c0d1140d50000080759003403c240444501e00340300c12444c2240d40c0e8075004c031003034001c2c8900654000880441c0740506507981c1e03002c8040300c0000c004641c100012402d0a00c01e01440c40c0c1407140581c2180e0440b142080807120051074070a900791030307503503924026020f500501d80c120f41c80c03c0e40303500040c000c100d1040c0c4404039035042d94800100300065018403008010290055907404000c000c5144040764030300410700450312550080c135081344c01404041c121040c00d14000100000301040c0e80205804011140d000b0303804885881454070707600c02000c014075400e18030b15014000d10300300c100468083e51100d0b810020355269074600e503550807049911550840448058060148032500004003ca005082c0d4000821000140c0d02e05000001d070a0713440741042109940030008401c81505001e00072100010700d5a1020740c2014200b0241f080f002846005442c021980881c0d00c011652007050042d480710000c00c0210f410784210b060081c54452180512030152081070b0218000341c0b40f080 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 637853534 1250 637852284 637852289
    0x403080a0c09050f0a031a01060914100f030b090703150e011206180b0412030b10200709060e0a0617060112020a0312031a010e01020c1314010e07020610 67
    0x50b01e291140c0c0c20501000780700c248400003981c1101018102000080142c19924010b1400741e5600a0b59854102c2c01002c103891508881c1014007001962081c1c0e40310340302404d109007140e044c140354220040000328010700c1c1d1111460ba0009000083c03240319030301940301020032107054040c158244c3d25550742a901e56028811402c5038007001c1c02c41b0021840607440850000c0d405544061400425103644001c0c07681920705503111441c208160071040c0e05032140011040081c1d884904003aa804c40292403241061003401380c1602101c1503094008060011102801407110300704907990b202d5102c15550841112000c4016280170804144044906182c8445486440007410300d0303800c10985140c42550540e00b260400c4101c407000c0001280a03000c0d5a180e00c00e558000b80050303182114048107007000c50194180000c203081030030682d90120700443c031004280e44400d500c1040c2d040799001090034510740301880460800100d16184002c171079074003074101ca9003114100c0c0c8688520442819451 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 637854784 1250 637853534 637853537
    0x80c090112060209180f070f050702090a1508100c0527030307060c0f09060f0c1b0b0f03010303020d03060b09092e1701052a09060406080403080a0c 65
    0x11004000045049100010719446078501605000c0e680003c00e0303050b10f0700411507171500c2d4041708020424081407a110740c00544c80c030741340d040c1c9100302001602da4440d0341c02c064000c0210000107400780c0144e80000108402010b645119a9034484e401d503181e006001c0d94403015400c240c08003000b6480340d403d4070600e42c4807000f83c170b10030850440e4107518007124400850300350000b400340b40c01040c402d20074010341b80703481d450f440803558071910014585512034101100340700b140c50341e9040b0a41d210090f14880f50f03000001c0c403207032040d802c5050301e1142c055000800f007420000744403c092510001450489210713030229034082000048c04d8042c1d9166024800011800f400034880c00d1820000701e9410542182c0e03111110300080d155545110181464014079003141394042000520b0512601c0640020070b0003000345041520300300e12603201c6050070600780c1d030704100c9004400458000b00d541c0e40318010700c1c90b40c0e26070f81c3c5d40002d400201e08070760660101c1d40840002d0500e0b5400e0180344041140c9 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 637856034 1250 637854784 637854799
    0x10060203030601120f0f140702010e1b1f021f06030503180105070c0305010605030c060906090904051c02010c03240b03150405011202031e0712080712030603020a080c 73
    0x241c00045134466900d0201348074039912250003a03110500f83c8a440070501c00400c01188003220449030884820002d0801c00c2160314118008110341404601d842c802030307c0b44103a0f12500803d00c001482e416244140c00210000c0340012451230381c0000d040b08107100216015842148841032034801c803040c07880050020780042041c0c600554060511456500050600030704104090311012000311441c0c0044a4503075444e6414040c61a08002c00000000e0846005207040300c900e01181041c040c00252902500c482000b2a0402c0b500303010b106504612480c15000355080700310020701a10f1810440740219280c070b8180d003a00440309a000107000e1407418050007080c9820010030256100070300224001000c180c0e41c1016a5a070b000300d0b4001c1120f002c41403014a240d0040504018200741010505400d0034440c9030310746c1001c42c4400864001900b83d800b040d9903800c3c16601481401c1c4000c1180d000d0311041a903564050b07001c00e003035038000c0d10200582178a41d50a035a50310034180b1140e90190342c = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 637857284 1250 637856034 637856041
    0x506130b07020d21110a0e04060b0a0e041505060a0507020906010503161101060f030b010e0601051201140d060c02010515041a1909020f1b0a0c0e04050a0222051006020303 75
    0x99108550559401c1350b50009018540c10700c800009030000002d141c00039181039079280d85480e0501800001d8030f00c010001c0e2820100f1038024002c80085e811560003a80c80701cad0144031000001d0882c400401c005405940d403007945a000034115400408120f00c070b41c60160103d29107512980582c4d00c1148843e10350306651300c40341c3c0c0c181c0c0c03041307019060740c86550340b149800304283d01c6241019005500c107001169240d41401d40d03a590741c1100402d150b04000c008c5c014241000c0c0b2440c1e0740e034111001c50f211000303548880c4007c592881c0f00d0450107003000d0b041c0f1088103422355056119510550025070780484059100c8200010348420104a6503230318424841c009081c90038a04c0280242e06824080d51110341d80c10444069800181d0304208280c004103208102c502d950804040f4948000050701e4080c216680d09004400507018261032034140c94001004c03c20f080100761a070b2500209811048144218000b070140b070703450170f01c000d4182004042010020710076100c02c141d80d0a07401840c210341d03 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 637858534 1250 637857284 637857317
    0xa110c0405011e0f03111e03070605070c050d08040e040515180c1210150e0a1b020d1b1a012309100317040b0a0806010f020a020f010e0307030506130b07020d 69
    0x140031f0200034080020020071403038541d407c01503c4001c00164540589940403410305821000d200d51013140a103042c2c0d00c182002600d1002203030306661120341c41551548550070603602e003140b800800c1c21f84002d01c00a0002e4460b10030742c011641602c90040f5000b2901c44401d01602c0380a95100c425580c0c46100b0a035441e24054101c4020315011002685000d41d0b1400708104180c0c003035407011b4869941c0c00c0d580f404002c202081c52186003a6000514800b210717424010068a80e4188001242c00503020351402c1142ca0f00d80400d4441e1081040102d03035856041400402c0006040900d8824028885440d982440b92026104596061071050758900c0c680390204103058052083d000d0a038104800300c0d240014401405803507030f6a075102c40070b03840c0080003d488501d60403100021b560100400000607690b03100013041d0484203107010125280088041f901d8181503030001046070180400b04424101c1480400c4092400f500107950300ea100d9000c03c0c1d84440e080c001040000b81991440388900 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 637859784 1250 637858534 637858549
    0xc05031b09070c020d0606080d08040503040e060607150b04050106090e160507120e01080609010b03060d02120102070f1b030308070507111509011202030702030a110c0405011e0f0311 80
    0xc200f410300300c401c90040c1e80001d0b42c90740d1407081240c6951b580d200034810103104020749041e011950030006140d0400e80ca4040c0e60b400355105107880c60104800140c0306884102c02c0e100a00c0e40145040403800b0004505009002941541d60145240400002d02240302d4115181110340c0e0301030280054540703c04250030514050440414000d00b006100001201e00c0c0c0d800c1311920307181c0d0b20f01001400080004043c1880a080b0900c203851440c0140459440038044940225084542108074040e51010520002c1d004030807841035440411a9818043d0030960710180b14898062090421203000544148068500000d80080d02000c00038414601882c010321103103001d0700781400d817810920f002402c0748107480420f40810102180031003c42d60007400d40c03d00da003032044040d411498000c034002d66900503021080c040001181c0d080000610901c402c03410760801030403c5c4800c0d038695844400050040b50800140126842c0c0060002045105803081d280d12a012184140c1c0d240f0400890 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 637861034 1250 637859784 637859791
    0x1c03080a0b01020712080d111b0d030203160807090305060712050109090302060103080f0903032106010c03020d0f050f1206011106070c03050306060c010c0f0e0a030209040615090903020102070c05031b09 89
    0x523a40300e02d841541030300840600300200103042010900e402c04221a81891109812402854014020300091f60440000b08110340190b18050b0200c0e9200081283d440e5100e40c40a07001c1d000b0301d014444121703800741007081000300d10740040c00b160342e80b13421580848105041c0500140c10071001403000586400042804141c000d4040d4100070400c8002819a03104103000300380d89502c40d0f0444c10320752014031a564408801d0030201c0c00d03298075450180d10b0f89a420b0032035041101d81142858071303038001e03003d9420990400061035140c58070a0b51082956405407106400709005500d0403024041c0000e617503100b800c00b9918001c0c10344540d44e042da2503070800740507030340c0c4094144001d030702120003486001035140c010364800014142c9002c018182210f1450b4a5001c0c03180d5003818809070710380810207030304141e0203000099008180c000803c1e00d880160020000e003070900c800c840c18194150003518030907000c0d03108a150036aa0750100b543d42c0c4548152110200c03032281c1103148901d03104400a60 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 637862284 1250 637861034 637861057
    0x60307052206020d080609090a0204231f0806011a070f0209071709030405010c1b0503160501120e0a060c050405060a08010f0509090a0605061c03080a0b0102071208 72
    0x400d90046400c0c000708008540002c001640030700c4d08154a954000c511640010007a15072a400d410300c03d078400d40301c0d100e103500a800740307880c1c40e0100010b41c4050b480c4480c08403041c1d001d51a60a0840c6401d007001b40c02506603032100d80829021403d0100401d02904840c00d0003c01030142e8080022080e164200c0c0c0340503201395640a80820141c0c40e540000d522070344095445c0103c45210b1000240150405410003041c3d5200b03000502c0aa40c0210001101c91b4022040292515801d01c5e03000f400581038103daa014010b0006908041508000b2102951401d03200c0d20000340032200304200721030305030f0104015030344148510400304040351700c400000c174514039101e0324064540003c10b1041d40829211000101210010014000710180b503a0260001b00c4182d0910300b0403064845c1d035400f11034801703070250f0740e0780002c40d416036154488864859130110207030080c0032503820060140d00d4200c070013607403103030034102428603d41c80403441009540c103004004104400546a0700140c1c0c2001c01c001c070 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 637863534 1250 637862284 637862317
    0x117030d06090c0908160909020a090606050c01180b0c0309010603080f0c070f03030807050c0115060e012712110306040f0c150909020f071416120206030705 69
    0x20350900d12400303080050801c4100104502c5210b800c02080d078021a404010150421280f05044d81c06103a000f408a400941c03000c18144030a00009850746401c0c0d01002106150640016605402c400031f000fa00c006c3e00c0080100c203106502030701045035640b2000380304214060018090303982e070307502458005c000d010000610396100e030b5030798055174005031840000000c049aa00038000d81084002e000c5c0410300702082d180c91950f42d01400012026040c001440b1010440c17038008102540700c2078140d02101401c0802a03580e03072014104c401d140000c50b0000300d90b030380044103442181c500d6040d610301c1300000403011407078a0b02102065501203c05c9410b40b00300c40462140e691f0802110303020b00d014a070403640c900401d160003014002d10303903c0469100e42100c00030500641282e812011665049000350707441c40000c0d03801d02c2902c1030180040c081201c441e83c0c0b6900d560005101c03400c0c07217544951280103a88601c40400002000e4200070b41c80b210410004030940e01c078001410300c0d04a04c0c1c8200c07 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 637864784 1250 637863534 637863547
    0xb0a060c05010e0a0b16020a0b0c070302030c0a0c0f1401080103080a0201021218011b05040b0f1c05011a0403080f0c01061208030717040f1113110927011703 69
    0x3c0b410b01c200c46000740c41c07103071442061000d40c1461280d220024409400200b0403802a9560402c100c4c1e0001c050780140c210114070703102410300a00894540c132290301c0a0718000821840c2100002c284c0380034050071880c6005002c10440744c489a0540da0042c140c40b001c41d5030786595070704001e07548a900002e0865400703000d6046110807084140340110681d03481010003503000c10596003100e0310f02a401e40740e50780b06206001d0ba642c03c60101e40c140c55082c00025680e17400084851180c0c4201e1812041405126440504a54043d40401d040c1c0b0510711540141707030342c01068003059008a010152010004000141018036410001d090044a02c00003081065a420030745541c00901d5100f0b0310396000002c108820319074091600d60207544070941c14041810180c496401007040c9100040629141c80302002503030341c454004020103001c2103402d000c2204107207002e040da41c01c40c1c21060f0007409041104421420075411b481e0802042d841c40d0004c5a182503042911f801124010250030f0008100300d = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 637866034 1250 637864784 637864811
    0x31504021306030509250b160c09050a0b030304050a2d150f080c040501050a140a0207030c080d140318010504111f050d0b0a1d04150b0a060c0501 64
    0x700c00040440b924001610f1034407088180c10310125039003807600700010386c01d80c0310340c0a9010a40811740c0c0c0c651003800d4a03854280008008040020005040404020000074001001d504a64030400001c001881303c0e00880c000e2560f28015030103010313408034007000107002000118a000103000301c0c4030030319003082c9210302c0c1c3c07100f60301c0198002c0103c000d81d0b00035000302590400194000110f440c0340104040c60183c045040310f0040b03001c0e460410400081c403c1106124001d469840c1501002c0f096a401309a003029603168031920080319100c5861400059014020503508a6a18207440d280e298200c980c0c0d003298540d00040071840c1ca400d40500004d591042489491b10a42c8211407283e845145a030070018040c04c28450400c500c0d0180740d900001551101c1079482a0300011404909004803170300050700b1030341c00c2d00580480344071400303c50f24201390040d4060065011700b0750400000c148420441c162022000115000000c2002c104060344c03041150364115405000001440f8015559 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 637867284 1250 637866034 637866067
    0xc0528120602120a050612030405010801030206181e12031201060309050703050a0f02040509060717220b04030f11070608130803100f081b120c060406030608010c090b03150402 77
    0x113080030540ea43d071040044501301006c5d10140741ca0084002c0d81403600e480002802c2c0c41050100130701900001c12040704ca013222551210582e60014209244400322881545003400c000541ca8822522003034044020f200c0072046954030070180311010456030030302d1000c0d0050311402d1170441e650b00c20220000b011034020700c00b0118441c4904032159801006004101c140c81d0b018007980f40c03070b401000c24000030540008000c008220482818066645c88181c460101003400043c48106004855500100700403614903038422403194032140080c80c0c42800803103030042e183c0170010142d403081005100440c000c80d00a540b217100302c0d95500780650541e4600c1910b42099843c4400401142401d112030600b01c100140a411102c00400802e22940030280c10001c007140103038080d10800d202412a02c41c244400c14240f200075154943c0c2d1995514010014000b81c4509805d5510b801c440340c900c0c1e403090714600100c031403012030241940c803444440c103540a00c00000c140c1c003039801c0014081d0303c0030008 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 637868534 1250 637867284 637867291
    0x1211060c030f0a020d030501120b090f0a2315012d080f0615220e0d09060e030303060a180e0d120f090203070612180c052812060212 58
    0x1099480f041c003a4030107460210300d090081c05050a04005100c902c60849254540540050b880401c40c1c0340c82c0c20f0036043c2a005a1360144502030310350050180601c8150022500c4038240442603c0e40210103e2501c0342209041004012040f600410130301c641d8554202d0364034101081c4400080e614694001064015030110a568100100c50642c0b900240403096008000f800b4030003200d038000c0e00203201700d81001c5003180c41d107410755003656044200b9403224071400d82c3d1a046404075a5426009072010085100300c4001540030000e00b40035080110a59010b800040c00a00310789091481890f83c0000304407a40c04504d40c2d4541190501031300b00040d0182028549520000c25088040081900e4003640b80c103c0c171504004841e401a240000c584040b01e07210702c4c004034070300420340101c005048802c03005c1500602c14450f00062160460310031080355002c0382c00c049004c0a44a0040140d50582003c0c0481c52a94404000003c0ea903a0a90074451040d4001494519918000031310000241d = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 637869784 1250 637868534 637868557
    0xa0b030d110d03051512030705060a06050306100509180f07061101270b0c1b0d170601090510020f06090303162a020d060218090a061211060c03 63
    0x107198220300d44140011218041070b0301c1c05004c0ca19000c1d031041e40c00c81c1410581400b9441036280c0800019050080c1e4900a511406071580c50410031100d0300946203901903584203000b654085002c200c00c0c40c02d20001c5603006050541d56540d001505151042012101a001d010304842c0350310040701400740700c0c090f01039a21501c0c40c6402c0b0190550071128104c0c3c4900c0700c2010040140c0b21920303404c03500c5110a034030181c2070708148c3d0303450303100e01c858041c95898100d0300800c41d419441c0c085020030030380c01d812101e60300c00813803403c43d00d403103140316005807034060100d00125420700140c1030030602c01003c16000e0040f0b074403490020700102d25100c4119407045084c0c1010091044004450b03540c11a00f00352450300300c0d07000706c44010b1143c14901c601030600303400b0721811200085481d04918094640e8201104546a56030004d0181b10402c115040911070344001000a150f600140b0551094641a0090304074800c0190769680c019001c0041d80c5a100e1020710504001c503808000805282d142c0 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 637871034 1250 637869784 637869797
    0xd0207030c111012110903070f061206050112050421050306090f04051513021c060b0a121709041b0e0a0324140901090b010f08150a0b030d 61
    0x14104010860107030300d0304034800c01101000304210f9a0041c110000d031421203800040251361000558564421b11720000d800d401001400144111401c80001c1111880c2e1116000f07555161240d9007101c680f07004060100342d0b044065406442d031940819801343c441c5610100d024140000c24031000703c80f42c0710100164000040000c0e5052280c0b55a41244400c224601182455950710751280366401803256a904201e0005498010821b0721095080d0054040c0c95045200ea041c100d15200d0345c00c080d50b80d603090071110025403c040400500b11141280789a543c120584e40303229000950710f00710682940240300007070b4141d03074902c1080041603070300c0d541c015810f90401c030181403406003032441403086115480400c08500411700c000e0381fa882c080b100d80c1001c54804c3c030791001400320054082540e4660300030400c001c0d00542c02900094000c1c5184045030fa6141e000e030700710007291b016296107500a0074914024030502071203d5086646640301007083e85216001ca0314010001c4a40c8001900 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 637872284 1250 637871034 637871057
    0xa0203102003060306130512030703050403032016050304051504031a0907090c17100501030e16060305040c0308030f0a0f0b15031009050a05060307050a060e01030203040204020d020703 81
    0x1c0301c9021010601c0100454110302c3c0050000351a03c10080411482c1c5541200d050b0403c4010300600a505502c101d80342d0300c81c1800100180108401ca41c2140440e00e8131004000c006440c103200d20304802c214031a5894443c66658448140080c20411116032109100c045216940c010480800408800f50703992a14a142407225102d025402045e1200c1d031298140315041601240e1941a00d1140c840452903600c140400c80d00412089120081c010700700c17090004186030482da14048400990f814000380c2c42039600e00761100385040803004901d6a0803020440036002c0d40055a2050107480c5081c0c803141e03a501e0310b00c0c0c5507000b26420482c038100c540400200340c070300748904048401d2006041255001d0340c0e000c5156007004240201d5200e402000085416000c8000b5501400d0024014011400c2050440018000503135120348280141140861107042c4210b4080803500b0568038a2103140703c0c80c0054000307510191099800503000c11202400918a00090580038031907a518010f101 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 637873534 1250 637872284 637872311
    0x24101119110102150408040311010504030203061015111506010903020d06020a0914031515120c0906040203040b01090b01120501030305072f1e0d150501080613080901020a020310 78
    0x82652144e426000c418106110100b107040081d03505890340b000d440c082d02c00203080143d031240550f0f440258144140b808000251840c0e030072000480f00e40348160710b903000001e0030a640c6c1000b440a4940c1c682d00000a00700308a0028035620341215040c10102c2e00c039600c03500852240c947d41c4005641d2150006070701402070713911404020080c030b511000410440ca070240001e03104d0302203141802d0490020710105810000304511201303405c030001c11480c01000c0c11260980c49080c0000c01398810000103002580300d09050013181d10803513008000c072407142c0c00e100b00d44000b003d50300c0025040200706401e0110950180c03007014040c50233502d406441d10700034903101118019420680d0364400708075030030b60400003241c0c40340040404120f500e04d0f901c000c4041d03c550320b0808034501c9a8410f20850072213091200c1d00c00740e1105400800b805000a071780702c916442d034495043c0d03001c4207061130b80b0100901082ea00c0c409400d00080c14410742c0c11a42d216000280346c2000c1c2100c2e01c490326a04d4060072920f2 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 637874784 1250 637873534 637873543
    0x1e010f0e01050a0b07060c022e050f0402030613050a020d0804090e0a0809011b121e0801080d210e010204140d050d0c0807060c020624101119110102 65
    0x1001c0c21514083c06034101005600709004541004000c82d4484800790f03245802030008a641c10045003107400e011004c2800c03d41d052108581c2801200d14183c04580c01c00b4001c10f2143c0706580140080c200313034170784040d58410340d03445040544280c0201c0410200690f280c82000c451140943d01b450f0303c0f10b05000c040e604807014a04c8842140d03004a150500003031983e000d44021007001d0900e4000880301c025541c00e49460351200034800002501040b032041d801c0280e20241c2c03142003a240c08162000603058900180c2070081c084581d001c4050200400c0c4075661144c90103034403200301c4200c040845500000d440150100d0852650085070a0200c0c01500c4000404004122011030303124903981c403031945940040f101401041f110786903503170500a0034421101c11a505c03103030130802c051b05410000d48401e0103541c03440c1c42500704001904280e240107004024044000c1c00e60303031803545000054039404041c0d0341412690003950031110000314034030701c42103800e13005011000807954400002400c1 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 637876034 1250 637874784 637874789
    0x607020706080903031320280b0f03010902160b090706020f0703150b061209060609010906050f010806040f2409050c19020114041a0c09030a0b1e010f0e01 68
    0x10f540c01032042040520100c40e01480c0c00e03402101003050700303210703201490f11341041a80180d08030719074035545156009140707192141c07154103600360f009541e21508116007902c10b43c0106444988140014011500ea0303500a0180521070181d2100b130034100e580d071007080082125041012b4009001c10440241c0500c5007102250050b0054004c41d03040d5a01d0301ea0710340e4003020001d0703490782d02c490440868484800301c0e1140c0c000000031203070928001030510768401c000c50398203000f01640c10000031010901d000312025140c008200c04180c1d52910011034540500500c0550320a40724044400d03689030074410a0401601c1d030401040b040001c07208e00183c102907078000c0703a81e28941000c001c0d55181142c16140d50b4441d2660700b024032110343c1402ca001d82444c003500000100000c0a010410080c0c0107000d00302c2482c9600c4441d01c0d030741d00c02800001d020391071360150180c01c008210400200401042c2c1e5000b80201510b8240441e844c412000c070380000d8110128003542406d0a1000c01e4080548030700 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 637877284 1250 637876034 637876051
    0xc012a020a0b1b030c030a0e060f1207090503011e1509050705092722080a050c010c03090305090f1f080f09300c1f15032a0305060702070608 62
    0x280005002c410350b86c91203614842410408112010401580d420040b100041d4140240d00e0303c0d000c1310302e41e00c4050301c015564003000c030b400008000b031a400c040c00340031845a51198107100a03404072840001401742004da5003008584518003055101c07952155600071996682c1d80c40c0c035403c0101c1031000f03254120704025208690302002c0d1080400c6110459805500c0607907024455031070491a0000980072400104107d5001c1001c1d04a103910001401c48245420001d03c0481409030094040702d5030450f0140000d40104041c0403d420594914540008090030b49070150680100140201602503c104005a410300a0190345d0602514094010300760700e0180030440c80f01415a21104400c1498100700c0a100c003281041d0b1903036809680c104000e180a840d80d5000b000390446006c440c0c4040240024580b12801d2204481690260b055076848034000c0000304002040c2d010703614a4010004403114000000b00c0051024401c0354010036a82d00204003041c00c0450161001600034940c29 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 637878534 1250 637877284 637877287
    0x203090304060c1403030a14072309120f010603030e032a0d0614042604140604030c03060207060b01031118030f0a150b030c012a020a0b1b03 62
    0x520810003004880c119202d070b0400b4180c00845280003503400f19024075603803070b030b01022082040b800160f4110b0020900405040c501903a11010300356507404880c0c207802240d0403920340c080c0029405100a04890000034515040460801091460300400d45003d0380c0694580008104240e0856440c84003020118080c0444418102003019009440321000083c0e480c4030071034103100e407a400c060342600c81d0002402d00150521410159030010255412502200f0300d20807818586154000490759440544a1034036080c5888800c02950031584061034cc00b1400300400000560071060040045204403400b503104c0001c0d042010881e0030080300e41b0b05150030404242c007403050407001c44404690035484001680082e50200c0d15010110f9a801042c3c030503903034010705005c2c8511080c480000c1c207003002c4c040554964141754584d4005038115020030101481e04d04c000b902c8441c20000c1c80b02070219101d100f038581d00050b4881840b6130007940c2204000550002c2c1640e001a128214011000210b = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 637879784 1250 637878534 637878541
    0x8070b09012307210f0306080a0308191e0e03070b061201091212150e01030b0c09030604120206060a050f0f18151f02071701020705070801050601120203 67
    0x2e0709281c0c0e504103100860108000e2440c030b0500600541d00c045400080408621030304031040101440c6104210000c02e100b0040215030601ca8010801990145070113041502c0b00355405030703100040039000b58513002040c3d81d0841c02c49401d00c1458010021406009002d000c1c0e00e00c030b8012600c0194004040d50030800c42000820014000c036078014400340c8401110902d0036030a1801040c480701c00070180b42159901c0c20240ea0301c51512031242802003810444041c0410402e00203a035140704a0515040020041001c54003109085a100034101c1c0d41618150b0b442d000681010b004450440701c43c04c608000c8030b882c0f5030401105a0040c403d503801c5404270b003480d0014070540181d170031040c40789146c04009619510741070040008504c0d0b01d2900b14460500801550402d140324950724081e94103034082010020074a4015403002907a0780107005054200b40b103030165940380c01280945907400b0441e05000500402140c0000c00c881800080c032800c100000504110908501c404c8090052052 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 637881034 1250 637879784 637879787
    0xc0414071709120c1f1e1b050f041706010e0a181401180c05040b0d030e0f1f030609050109020f1210030816051c1d0a080f010608070b0901 61
    0x3050349102c1e0010070551a41c0c401031030b281c6451003103098481c400828a420345d10300070582d000180044009005043c403ea41c804030502200d0600d550748000d10399600040080e98001c50090803d198449141843d0544456042d84102c00c1c460b0300d02000e50089004106000c840c206482d04009441c806105001803490903c4404002030001340400c4140c44100b44d290078250710502c481d44141e01800003000c40703410aa00741d00079600c0b856008500b09407003402c070340c40e10030800802513526072501d40d00c1a0aa01c03d00c40188000c00304103401010072220807002e130041c03580c200f40a0b40251740c082891810840362405032041a0300003500c590050080c0741c1d1480164080d15584880400709007219a40c0e8156014107800070382c801b81030102c0008070700c501c500c200e422907a4803900488c102d850300c40b40d840c49601c0340106505a040012192382c6281e08180c1120800f00105100920a41c201c9131101201030406080c203070254060380d0f6551f01000401c0c014086c031001011600001c5040c421f00000 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 637882284 1250 637881034 637881043
    0x6030618010618060305010b1002030a0c080f04030f141204050114090d0507030506010e040f060b181017060c0a05030c16030522032001020c0414071709 67
    0x2480052031210050040c0010003540300c000200307005a8155030500740c0740701080c02400107020948140d4200030742d1100c5030900162034280344071258000c51404c0100d000455407110318803411210b202041100e10700d4040068040c2006c0c0d401410a50491601d0349004401c068003c800c24115812440840300001242e5042c0e4003103802c00c0c00c01000c0901454202c40540c41103001c8d095021a0201007201800400550002581d00c0b9008071502641c0b01d500c01c030b8200508139801004103403c02d52a0001404a8000106003503018040c0012284000075030400d00c0c200b180c00d00c0c110740380080108a500c1c90310103060100d03031400d00942014103100d00b028510f8854200e0350028002c000020a0507111050200c41a0000c08150086201c805181c010202d42c400314410310703410320305042600151120508001101d61101c0500c11380003c51a240354150580a5001e0541c001c03c100b58a290725030b401100864150301070508034a2070103a030040e1000b8040440180720350301040070091400300015 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 637883534 1250 637882284 637882291
    0x60f0c2108090a020901051306050301060b070507140603060103020a03021e0322021e031906050412021903110102040b04330203040e190e01050f071803170c0a1a0f060306 75
    0x403200702380440b8a880d2000546010ba1180da0590318141b00000c280ba420405001103d204000f510000d0707945607565010a20116500e913884001003020840d558001d82c0207106900c0c641c00c0c00b606004c287e803010b44607012030a10780c450407039000080051030010b00f8402d147c4180c1a02c00c0c00c2c0e41d07400c80e4011a990b2a40d003816a0410981c0b050194a20364040060310600144148842c0000b100c078038024014050503038003181c40350031145100000320300110b0222005a000b11462051051503141111245584800c2a005550800c0302103010181c2d180103002400c4000354018458064421803400c1c14101d00d04403118031030030700002001907400700484e0100d0b030404210140d1600d41d01401d0480d003140062488030a40341401100742045e064100714491128018224140c0c2d8824070151401880c50743c0d04400541d04403400c0c40040e090000290600c0d09119449091241002501e440d10b4840803007030f0b4920351a0344040762070013242100c2e20380c00061407074120343c4ca040c00004250b8688024 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 637884784 1250 637883534 637883539
    0x3010b01141206061b0c0f0a0513051015030209120c150306060d020d09030914010f03051008012d0b0a03030e040b0916110a030207060f0c2108090a02090105 69
    0x14070200700f103070f581c01d420b8443c40811003074512400c0456089050341d814039001400c1c05840860707a101d0013441e00c201e11008540d0090100e00a48507020000802030000030300c0990001c41b40400400d90342c45040e50310104502d41d403030050340c80d0410307001c0044042e40c14551806903803024480e0381e800d407184140c050000090074000c035220f484000028425000d0710050240481c804101070b242c2e01751640100d03190034041c0d00d507052420b0f1500a084c1074140001d29041c0810701c003007461685c51f84a50701096005080040300d150b141c0c0c8420b02c503829a0380b420301d0402a0035010401344ca0300085500c101c2d00c01d11104000f00b1562484101042c15140c0511016040c894056140b840940325034200b900781c0f00d0014030900540c0f4041001c0c1d00b400c40b00031903a100107214080740e030311800c20024984060f01e130190000c040b0149000b00031140b611100e2008000c000048504600043d24a94110824500198a60b01c4040c040000900700c141c001c04068455000091150158481b091038a05440d400e = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 637886034 1250 637884784 637884817
    0x7080d050a02070b071a0603060c0a0c03020f060a1b08041208060607060906050a0c0806030a021504171c020a020f0402180306010905071e0801060513150e03010b0114 73
    0xa90040c0c1c00c0c206683c2c081360307542800040c0c600400c00704120060000c0303005280c0345016180e000505d030361040d00b20b41428001e902004640c1a031030041c02d024011070700c01d2040f18820240e00d1145400c104080e51103180d00381e1151a1001c680d45c100c040c050007803a1510304070782c5074a090707120902e0b42d030000e4955006114124000ca400d03911081c040390000741c2c004000703101501ca546008001800d04581d41085185480c0c20040030b83e100c3c4411600450004006080218881e001c004840341e440d543c03052144020803000a581c84031f611244102410700024014241000954a0a03008440410b0045400070081c2c580140c1d50b401c2c01c81e480c00c40544005072542070514151140d480d9035605030f5494400c400000600380007a0700020301c502844d64401c403818280400f80411005408040030214007000018032110b03204401408804e100341407405045551812800c201d0b5402240302c40000c0c851500214003402d0900400d0480442881c26111a141a058001990040e08007400c006000d = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 637887284 1250 637886034 637886047
    0x13030806220903020c0406080c0f0609040b030d03060515040602060f090c12160906080a0b0712090f0b0601020f030a03110903070602030a120212010303081003061b020f07080d05 78
    0x30140900074880c5498004000e00002420080d550305500f800140c400c07410410040b61a20380400c00424418014080c0e050b070202080c1040700a070099104943c215075a0035220320517590420001d800c1440c113880000344141444140403102a015440308145602000108080d507800681d40c2c0d404000b45404c0825601e80720240c6080800280c0029800020550007062524010810000103031444001817a0710b036890201708140c0d80c0600c16826250400c0c0380f0039010827509441290301c882c86107041c001802010300c2c100100c4108200c00e54018070f400024a04003e41d00801542043c42400104140f1203400e034183e036a482003062001c10551600b8440076841807000c152100f0390030040c10350b451182c490b00000e680380c0140b0440c2002032403000740b0245441080c800c490515111600f0703900107a0070740d14140e80b680000f4280c4120408040400070200d41c0c0c034440d014045c9062178405200c402103031b00003480d00342400b550211940005a00300030340d01c0300090340390852800b400c20319107610 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 637888534 1250 637887284 637887319
    0x20d1220010902010c230304060306081005041205030c070204060b040303030b031606030e070e011502060c090a03060c05130b09030f060f01050118080d031b0c03120f02090307080d0813030806 84
    0xc01d9480c441b080d503c804140464650341541054040e01c4a420480311524464101001a0b40d81a030340900a07020714625010308512070801107501c40030b400380042c0360440c01d50214080300c41c16444003e94510100301402010781c0741c015084041030460040c419a64014081c2c82040c0c954030071541031543d6225806404401400b041d00100b030307100100c0d01030350796075003540b1203200040b01c4400060060000049140c0300180a90780004070240081346090308550f00c1c8801440403170301c0b00c41030003010320105900380411070030b0b80080c0c501821515122500d03c01414507001d146200101607821480070040e445102d00c10300390440d8824070b81411400c011220b64414950f560304219524040d1003602000260182c01840321002a5400700c2c0304807038000400c07141c21035811710007000200e40c2d8110781c030880300e10f401941c07104101440040c90580a000040c0c41d107035440d070180720301c4c0c0c1001950242203500300404607032241a0151451a8010555009005c501b0090000d4411048001185460b4 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 637889784 1250 637888534 637888583
    0xa030816020a0209150a050d150b130f06090506061c091103060108010603050c0907081f080706200607020d050325020a06060605190507020d1220010902010c 69
    0x2640c0180501034581441404490101c901d031034103601480d91b082001900317082420080d448940c000041c1c2d2440743c4c2510349100508022031031300390301120a9401c401e000e00d151041500d00140002c1c0001d0003071509010b507082d44c0d4010103640c81100184440a01000d4200400c480d50211036000160600a85401107120802c0c1c03410603010b228280020400000541c000800c3e0f90184040359802020b010030031000e514201c640800281c02c401c0400c58504603003a00641954190000005107a150002607203448070036805500000d004100a0720129185204848011038801c041c0110340b51000c1e000c1d6480c5035048000c4104000040055040c00d008150200c0003604d0641000c2000c0d01040001c0d41d540c041c00042c1c810920341035001524a022b0000c94466079024032403000c800c001c3e02400e4459400800301a42c00981018100740010342030346941e0380543c200c1d1200e110000c88142d4000d0744403d40000300419038540390b08140542c2c2c108030350f516001c0e445041200306081740748031030045 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 637891034 1250 637889784 637889803
    0xf010c02091009140712090305090f0f04020a0315050f010203030f0c07170405130c021908040312020604050f121b0312010e1609031203021e160b090a03081602 70
    0x901d107080e00c040d80d213503000718205008441540c4c62840e161a1a201203084440d10040100412010481038a090a00e56205280500000d110003500d1240030049400e0340c0c0100c404200080c0d43d448155280076054041101a01050794080104000035001030b43d80d101c081c00441c814032941c00040c005002c140e00f141c6400d0341c4251000e42c1d84200f1600c58125800074041d20384550703004210f02080c0b060300d1144111103103290380140711100c04510303181d1001c14005416244108108004008114142c01d0407038811810350083c0304510341410614186101c00c07a0101007a00309140c0101340e000000f041e50706000701448807100740c48078101100d2030341c40382c00610070680031104c0001510143c0c0c15100c5100b5041e186545204210000c4221200d5425000051402015407002141a17202e0741c0070b0400f005001c0c00c0d081031044284001780a82d000b00055250100c1d5001c500c204002d429881a03402c690200002c12003070125980180c441c50740102480d41c0001e8105110b032210b4801c0010030b41 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 637892284 1250 637891034 637891049
    0x50306010e1f090603110402030f180f0304140f030307030e040b0109080a0302010501090e010b01121104030f0506100f080c1002010f2c0a0503220e1906050f010c020910 74
    0x42d4940d14070b0003a01030840c81c842510081078403292211790781042e000305da124807031203905c9055a54600301c0c40d050b0600d191040740c0c03083c40340460031540b0321400c0008202038060703800f84482e0309a0040c200141802c89503000c50080e0000c4c0420300000b030300720070513a1a43c07204640c085007144c00040101c1e5401e41c01e903c040074611071900190185501944514142e07803a07028140714032880c0b413030034600382e50344642e6550026000c0001103c20307a4040d4800c4000c11440e00ba0300d860165241c482c1d0b6600002400d060311103800500074400f50a0917144240000e2581c4200460b10302e15020446888181700340105000e94610f00b0a11440c600c01c0d0b02c010822141d043c801c0001240c0d43c820b00b942e400703040c2c0340d81c100c0040220740320102d40e40010f001016a980b05000b98a803401030310750704217038000b03950001881c4039030b421010482044000c2d40311300c00c02c0242c2c2000740180410341091300742c43c01584540d00800e0325011159441c2d07030007070a2058003a01590701c0b0059071101c504890118a26501c03011 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 637893534 1250 637892284 637892341
    0x1020a17090628020c1c170c0304090509062503270c0f0f12061e090201170f1303050c0105130c090c05120c310b04050306010e 56
    0x1403e0b0f141090700882c14601c070140d51402200701400a07640c9811982c14503600003000800311a00f11a941a003002692041c00059501a02c03030810b0a560b810407000a141c0390004181482a216071344112a0b00c020070000400544c18500b40d42c0c900003070f00b401c003600c1c030640d2001c03030b054450b010b0f4128a5003940c6680c031401017120803448035501c6041403903080314502e1112000040300001c9480c040155100d40500514552a0110000303c9013000713401100d100d40c443e070050141b0104014401014481c24101081080c403620004199a0741400804045100c48007400f6000015110840d03020168103800580ca990314242550503018408030000b2941c00c100030005010303c1b00042105c0341d489240d1091200351901003903400c0d904141448000144140112819403000c3e1900a801a1b041250740385003001ea5a01054004400500c0765250120a400344584604a10801c001860040501401e0a05020010791280010b1041128004c41c030740105108000d100000d0042c01101d12404 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 637894784 1250 637893534 637893547
    0x905060403020f0c010306030c06110a0f050105060112090f15200c0d080c0306040b1518031c0e0d05070b030f040b0f0115080403051b060103020a1401020a170906 71
    0x2907544034090040f0303000d0302a03a54590078a5019000d101e042d2a44000710710380c0c6030b0402e41d00b01c0c0e064240c0c4070034605a00c036207030215011076500c4001c420350300c1c02800080703000d1501c88000340100e0014040c032a84140b030109624003292807100e031802c0d10b903408101c04241d0240500305e00090168908041e0001d106900030856000561000b0122401c1a1040d5400170446580685421400302c482000e1400100f0009060740f41c00d600c1a0548c0b54010131840c1e200c6840100492150000c02060103030400f81508021a03103010014542c0410480103100600e55103484020002c030311441035a800703488410810400c1060034000d040c003034014192142e40302d25081e8085483c9807410b86050b02e01d1429140880c105156400f1041c0c16980031662581302d50044400460703102c000203000b81c04004007030040003404c01d00020358042c3c80ba0607500500003941180100325846489a105910340f4841450220282c0d80205951040c031b5003100010740000381d1040510498400c21404903808540010322 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 637896034 1250 637894784 637894787
    0x909060801051510020a0f021516020f040c090b090f0d08030f100b040e07110f070303140915070c0909200d0b18120a020f1005010f030f060905060403 66
    0x9034460b03160703402400000300c00d00f014407911003070b601403c10041e0440c0e20700c100442da005094103030301807000d80002c0504201880d4010340381c120030600544841071003441c50035417512600042464408540c200321103203020b03001070102a0707e4031400d2902c4c1408250107040c0e41d00e0000120707100b10098103074000e0750790911f80200d01d82d208403038203152001070f00701050820a4a401083c20f98140646252400e41810742d030210741c0c103009003068104110950b004803090400d100301d2f04074452580c010b004041c11450058106100c2929032401140140914075456951140c4000c504001c1d21120ba502e0146041a023640b03091500980c40b030342c0c100410a401c03c0681c030840caa0850b0102c2409451004220030411a0007004102a0442401c0000305030700c01504244103000018650866403031050680300050280c000c690000c001d41c01054200b4081d42c0c043c1b048130703503454450f0b03002c0002e0744c1030030711120f4404c5c1035000190001c03081011365070402001e603001c240e025411208903140361805180 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 637897284 1250 637896034 637896041
    0x4020f04030314070b0a09051c11010c050c0c040902031908090a0e040b0c090a030b040c1406040b04030f03211d010209030a020f03030405060a08010801200d0c0909060801 75
    0x20403000603011003c0c0c0c519000c00d207015201c070300340d01802e00b0030340d61900241c85001d010380e103070141d451340600c5510f03020400440c046d590115001d516080c01c0f140c10340058030700710b4440242034402d2000810035141c01500100c1e031040c1170b0104075400503685a0034004a40703001547d6414143c848403000581060010102c0603202d6a002120001d00c0d16448000c011031a1206035001403c1e0680c00c80032901d1025403401401c1003100240c1128440c599946509030b0300b80c0b00b41c4050305c0070001100240645116a080060400b00542d6000c0c54146084c4d00f9050754400c0d40302c0945a4141d00c1081c8003010301c01e1180001071f0160b00000d01440b0b6420100e40010024100e43c82c030742001c0558031780038074a411300942c0c2200318010054000d16076542c090107111180d0305481a03240c00104004076103550750001800c41500c051b50b41ca00c2540c14101c07818210743d02500c0c40e0480c200560140d9a02d003d40800303e40310340140306804103141d402c02c102680d403071111b90810302900d81404c0c00030500807015070 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 637898534 1250 637897284 637897289
    0x60801050a050a03050a0209280e1608030f0a05131706010608060d0b090a060e0307030e0306011a3603010f020315101701030c06080711060a090507030204020f04 71
    0xd69680e030720340c2e881c800c01048110070310009045800c8052440d0145c5450a482603111004d00c0340c100f0301a8030070202100c032821138180c44d04941d5841d20312465400342004501e0302c4400c065030410f4030b58148540703250750b4085c080c99800f000000103081c0d154188140245c598507034034100d20940258450580113150440d42d02010003900c6400c000041c2030744203022560294001800d1507a4112094840411442e40181403030b480340315003040c9000085451089240c03000d41640690340701c185619008000c40002100a482940004014072540c2d621619048800701d00c0c01c40c00303550300c0c2d000c040d103035050b080403800300c22a40150305161859452400c600c2010352088000704a5030409c1c0d440c42049010070b40d80800c40e07103042c3d40c40f400141841041d9420040c040d0070a88407000040503400010082600300700e40213548050100316003074002d400e40703800c081c0c00e0038640036589010044598481c3c0040c15045582d85503007010b010301005000d150060740d00540155030b00d40000503058501c1d486032 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 637899784 1250 637898534 637898539
    0x1e0f090405040c08061b09130209060409060f080a020102060c07140f03040602010e070f140d17090907210b0f030601080705030609030717090f04050a0905060709080601030213140106080105 83
    0x4d000503540c11142c03007500c502d2071b100c101e44508054280082c006640722007500402466070801101c9469038454001d40002d021005c000320b07030f0604003040100700d0b414507400101d2543c0070804d81c20050307801280d401e500160400700c031900c03a082030604002880e00702c5200c180d1400743d5000401d001c0d84c080014015510b154000b485050f03920540540e448100d0300c502c500d65581ea54042c032541c16002d079005098000206040e44030030031626100070702051522010404840000e1a42450401e00e42c080d9121141d03080407071625100d1805a142800c01141c8200030580c0d550010015a03141811451082409021180076684405140e941d4080d1409007034824480d903c0003e01401001007181c1c1d103182c3c0840c05204c00740c0c0500c441e86268104000c059803000801c00303551490b4032240b040a102c0d0144a41c0451044028200702d801c00c08007030300d20000c2200c041000d01910200041c480d044907415540c0d42d1000400d0071056004003c8851001c181310004800003503055800b020884c10303541e08 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 637901034 1250 637899784 637899793
    0x6021c061703090d330b09060609040c050d152102130c020109080a020c0901060e0a03150207080a0f020c09012402071e0603111e0f090405040c08 64
    0x1508070740c40d900e03085465607a115074820410091182002c0031148042c40c031444418107026900c010082980240803039030301d261010b4a004a203510001e00030307800b080c2815944030f22075081c41e4001c11664820300710200e005540381c1c1840450b003446601107800000d042c200801000050700c8510301240460310031003150040110209005d0386ea41418910004e600514100308004070030140400f4100118407801555600d0184002003055403005003844441e99002d08405200c29040020745241a003003002004000e03200c191240d2100d507161400e581c1c00400c1008024008220400603100e0003000804581020460b00146600880c668880140c170303409980415104d04140800024248240205590b14400701110350324110081c0320480c0b058070668604c10b0300c070540c940b40c0b41c1c41c0d988103580340c204259007000a1030385846200d40043c0f000c480289041d070140100c240350b0002d0694602c80a0380020040c4052032290116074002c1009001404240740505204001e920380d0320400005004 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 637902284 1250 637901034 637901039
    0x909150b030309100309080a0c050f070503030915070c0906330c080c06040c08100207050312130f030309060b1903170d020309060103030f1d150706021c06 68
    0x1660290980c0c0440190046041000c14020040c422000c2c04021060555514001000c03800210041036044541c1d01e9801d010740451820625120381c60004260781e800001040c00030350b90110032921514007c8510b00d03c00c05400307005602c54411984000d1122128840010b81d00c00944c000908807403e0440c03112039504002c103070704200c0003202c400b90700314034000031001d043c140245911140c8038020501036050844d844c0c85989000c5094400350744c8441c0c2e010301000002010040f20300310030f01c1c1030001d42c101719003640c0c0d0554a003e480c030303010032800115000034410080716419050a0f90040754600c0c031388a89043c050010217601500303881c0c480c2445450209410140c01c02103030318003000040315491385591120143e40e04880c0e0880c51111080020410507001c40c00034601800b03864000e410954903625000d0812003003a071850b014070070640c0f0b24580c2c1034140003088140c0341d415100e9119156a00400800c0e51151941c000e1100c0d1010613501008100c508840000c4202014100320468 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 637903534 1250 637902284 637902323
    0x301050c0f0304020607081c050a06080a0203070b09032802012d030e010f09110a0e0f0703150504020712030b03060903070f1a010303051c020310051c08040909 70
    0x1180746034010100d442040402d0050806100806407070307024007402ea003010554150898002d14003101e852071261120280505402c1078480e00c0001e25600004114038a01035005c20f407503111031f1166888618004c01e90b13000a450600650155201c0c0345519107542c0d04130040301c15041040d542c00d900080c03d18214800720042e44503402c035a94a140c1c0b403078455076100d400c210701424861001a01a5482e450074840c1e0034070324002c00c611a8030443c0b4050004655400781700b00c20815520244407100f01006000f80c00c1c2c561005281c2040607850089003070007100c009000c211a00340d200642091000460000b40305960541e00c406d00e4242d0340612054106c40d040603962041030340c1d9210190000c0010700c2c00511034051068400303106285540e0351244030714900c410308409a0013034020600c0002c003c840e42e00c0707c00b0046012360b0342100c21811030601c891504228400d9008807400740041d80c0b4a00c00c1001c11038114662390b0342c082c840964803511080c0c0d2801820810340c1c220b0758440c00031055140752 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 637904784 1250 637903534 637903537
    0x1c02090705071718061c05091e01111603050903071401031a1507020a08011d0d0203070c030f0f12030204090e1b060f040801022205012303100b180301050c 68
    0xe407400300e960484c1c090842c0410000c1ea01440c0500109146404004c00c04070f524001c0520440900001e0b140c50427805029a44e800d1340c6135001c90945e40342c0031551101d80c000006454861585030b402020064a6140c01d540070310645a100c1c3d811701c68100000780c2448100780541d0320b0751080e038081c8103901d60056640c1c00310302142d4200794440000c12002c16000c3e90708026208941c0010080320710266182e030410708449400815410200003080c0b2034018000030040c6a0440361036200440c0b030f080450b00c8505000400340002003680840e800e10000380101219030089154001d00c1c58030075109a158080d000703500030b1084444190401c41c4400c1d00071070106002b10710004409060003400300e04010054203034451032400100602c140300100300e41000344050800480b40b141c0300c1c00c01058844a010440c48562302c1181004000048800003254194440c0b000c00a04401580c50341c440020404c03890b805504042000d246c082215040304411013012440b40e64203a000300055251196035a919 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 637906034 1250 637904784 637904797
    0x1c0206070c0308060301061703040905010b0712050a0c050f071e0609151e030b1c02011727030417120403030c030306030b010b070606150c021c020907050717 69
    0x20079100ca0296002c24003d00c03425038840b800500004070541c86140c480c0000700d8217a915103065101040912541d2842e11030507016040c80ea0a5600b001920303603c7e407800b401d209000504100f408100100507174056504078080c1d80d8400183c0300e0308005c41460641d00d450502c910340c80d020001519076030801c803849040098480580d1046401400d18084502d10003074001a50100b000c5041900441c42d07100212401480d002d40d400b00f1640910000c003c4c1c540c18841c0003240903035280000c1d40041c3c2e0000600d40007100014000f084941d6240407075444c1d405c0d0485101d00008400380b444030440000300080c4141c0c1c032140101c44130b4103006c4850036070b40c0d030601d030300d00c00d01e200100400c0c80828011140c0141262107450041000c40c1c0365036498025147c281d0080782d01c03e0f0042006010844240a07140283c8490f0307400400c0500b8105008000040f0180040d004031080100d10180c0d05019111015040d0054140036080c200260020030079801040191120801c0302d40444e0035025a8007259075 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 637907284 1250 637906034 637906037
    0x20a1706060136170607030c0e0d1e0204050106170c0310030803180706090504140412120b0607121101050601050405010305090f0d110c0301090f1707050f1c020607 72
    0xf00e02445059800220020600c403440d00d10700c000020f02642580c10a0303c810940c000a031405040c148006425281502c42540520000e103040c02030a44405551650154010161084140c020100303100c402640c480301039003250400001041c082c1d00524070300307592040c003c80030741d860f510390700003245500003074409050703800d8824020804500880050f5411510725414450300344480c1407640c1c600b2078107031701c032502040d0400e03800c000d0391401c0d1007010188191188540d2481c80c0503902c115808001072140b0b01400082c510183c002c1005904c1480321003006000c03075590300528200784160041a21081000070300f40c4c10311140f981c0040c040d1500038141038407480e00345800d00d40154064400244644c0451140c00d84454041d6020480b0011a8105455403103090790803c041e070741800b65020800780a40e0400058000150505070b52034803480d000b00045298144241090b52240304510700603015209080388800074200c0824140241d41080d0b644000040b0050400e036100c0034116103080 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 637908534 1250 637907284 637907327
    0x70509060d060b190801061505070507060f020304050402031f080d1409122e1404020402090f09100807050103051501030504061b0c0b09060c0d0e0109020a17060601 72
    0x8000740d429080350b401c0386402001d0880c2e01003021008030400f5480e42c8411010b0b9141d510812046c02d20b11480008e80805180c0030340381c401287c46050741d4666503c07684040045144060034124400e000356406000014015503903030400c0710703555607041032411000d68440480075001407100c00002d450243e0450940b40d8034007151440b20755182c0d030b4000c2a1104d410860190907245080014042104010b4144031003110110034824401409101c4000b03810b0004e00d02240560100c01d441d4005078082d5045038050ba40e110480003040c83c0300345804405070404036090500c1040703d41c00c101c61742034071a94421500407954a40045003a590280d400e98900056841c2c40c02041d48240c102c164840d003d2000858001201c3c0182c1099001c10f400c41d200003415000d0ba0070421103035115850f0000005c2d002400710303007001a80700c42c00d44203401c581c0c989a65148600c1101c8074007074002c0312589400034900741101e96a1040c81d03508003101d80c2e1503a8240542d0340001c8a940c041c05e141070b9580404400700 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 637909784 1250 637908534 637908559
    0xe0604030503041121062a0d11031006020f010204060c03120905030307020a0c1a0405010809070906090207020f04050708060402160209072a0b040b072f07050906 71
    0x5664642c00508150755100110601404030740b12010362590000701464801011403400c070410703040c058094204100003607410188500f4101000189004403200b404082d83c0b090501030b4030f0020300220310105010b080104c02c000c94011041f8014044684680075a110303d444642807600700d1180303008020209070b03c08003010100344260038010241181c0c450015517001c0c41d0b121646590000ca4205006a01101d2031200f044000a240c0000703010b01d00002200b03100b80702c030a80c142d01136030050300c1c100b00c0000000783e08a00c1c108010b000804000d0000c05c80f490302c03890105c010b5803022005a0040700c0c0d80032400220f04251281c140f1408040d502d520094881008000c080c0d0701032070018a91800010840780580e40e0380e19542c2c0200d03241e85a081c0d40440c1d581c403103982c41d611359114403034488101001c0e50125a403009910f034003590064500b5180d544940701550304000240704015070342100c014124164140e219002d40901840f01201e040b0380d9244200405220700300c0d89c1c141c00c40c0010007407 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 637911034 1250 637909784 637909787
    0x170106031805010f02090109050a0803030417070b040f0309080606090106140904020d06090e1f020a17070207090b0a08120a0302070803090105040213143103030509060a0e060403 78
    0x200385000c0040c2401141900640c0340c5900703513080001076040995002400110544c3c014290000510f001e50f0799031045440c1a01c41da4482c04000c0015041260a082c0452a43d5210007221020380e4080007000150605044c81241e040d80028104c00bc01d04458011072841400a2880e104450062035001c1503030070b1090403560903000b02001000309509101010f4595641d001810450130903500c00280b0702e01e0002070b0001da90130300c466040e03c0c0e009081c0000403503841e00c201c0c100e604c490280140c0d0b12990102d084604074801080c03048009074180c01d004109a0124111007240c00501c414003501000d1002c00101c005540300d24080e55000c0c0c050090b903000d0020103080500701c6410010f08150498407034041c0f50f48100c61421890b59030381c0c1008114070301a480d1107000004800c0401240c0301d144c004400c6204007510310044100b1803507200c10004815a07281113804018a41e070110b0030114540034014100c1070324914418060030000800b084000e2048481840109009051075165502d0 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 637912284 1250 637911034 637911041
    0x30a0807030603020d1202211c0606050409110d0207060b040b030c030c1e101206060212030a090c08030d020717070f030f030608070b0403120908030301060f0e030f0a03020d17010603 80
    0x502400394010300089601d681c2d020300a034032080d00f0350230020f40e85201c904811064512480c011170010351400c0c80c103000c7d003507015065500f95a00e880c0002994464040c0780c4207240540005114500c0c00080c0304000c110781c0740c00081145506813414003040180d1000c2584406020180c0b640550203082c801c0391754500b42c000c000d0740c0a042d0038a040e035883d14a02003051614400300b040c020641200260341403103007900ca403c004103510301c0580540a0307801800d03c8584005400188402c4d11000d5190074044080d140c1401015020212940d450b9501d050001070b4000d0241600d440068403002c20a0022601c200e49525622440300c0307018100564042c0c070461944400d65040565492001c0b546239020000c1c10094050b1840751a00c0d10301e94680700c90031141c16111a01008000d0f44204803140d030001c142c3e03054034003d00784404208500c0c50f00302c031400c0a640c09542d261044071407a0707031400404a4503014480c0241c0c262020512400300030b9401c7d00800c01c01c1d4149100b0700d001088441d02c80d51 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 637913534 1250 637912284 637912313
    0x11040c030b030d0e091e060409080c0d110c01050f07020d17070f120e0d120c0609060509151302040504140f0601140103060303080a0b150c030a0807030603020d 70
    0x2000540031400300d0200780f07840d041440183c00309021000c3c80080745440010075a01c041c0c45911000108005402500f40b9180540030502450311490782038104842402a0b918041c10304003112074a00220a00418010a070032101ca042d0151012030025075104408603200d0b05860290303940392005039401d00c0f000c40610b19041c0ca400d880d494400a282d180c007401400d4540c01030381141e406260a0070120f621802200b200340c203000b001505c00d580c9841d006560380310541c01c000002c0d0394100510042d6082c5d00300003402001071303140012001c1003210300e5000501502c1403030103c9441180c0c1310540d2403400029518103040030200c2d0281001890305030461580a4820b82c413041080c2ca5400003249411060354000030b158010500601440242c0d170b092004060003482c0038001940f558a001d404810058096592151583e59603107003600e9003a000d4031800001c00b44956605942c0f560b42c0d88a4002c0c00c8440002070080c40884c881900c03038010744041e0707900103104801c510b190365504810032031803d = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 637914784 1250 637913534 637913537
    0x603030408031606060f050306070309080c010903260c0f030406111207030b010216090e01090203070e011d0c0d23130209062e0216060e040e0a11040c 66
    0x400c80420501d000780040d2141200c0d0403404040c00486140c09410340719035411000ca15071040704100320907500046e4103a045252810001800002428402524030502c41c5924181d17003403030600420594009804464441031054005880c8140350010a110070199610b01040380240401002d0880b904015904070f403003610300082088400c40e030700d8803e030005546c1241e120300e807030300304420140c0501030810500c4091001d0320000c03141e000c180c1c40c155168024002c07265a106000b95110400350310036040310360001c080390b40c6907988a030340c44442d0200b401226007541c0001c144401481c1844907403400b070207003080f00e9410072410456603030040003100c02c0360303500a0403820662254070341001c00e24095090810f0050301056180140090540701412032400741c14002e500b04508200d0748881d084030303041200a00300040341034000300d181c0350400806403c5000c000c0000141d40d60446004e04402c10709030340910501204949181e05c80700c4108003d0032a00d035441d00c03644245803aa20043d00400d05 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 637916034 1250 637914784 637914787
    0x1c09031407080d0818060636090109050d0503090312220c080f1c20030423120c100c060609050a0e030412031b0b1303090b0a02060f060303 61
    0x15070035043d2078101000012000b16210005000300804034000e08a402151100103180030300744007022134610b500815030f041d203007807404c0a05001d010100c0c050700f5040e200240340041504040d40024020841048102c4039403040c0c0a00040150040056070320800031003025508020b0000c440d0384103524000d000b041e00c030381129180724140d101c004a01d507880b4020441c2c2c40c1c00c1030130510201d02c0e20781c034801084620f5110f02000c01101b05250000b030104511441d009035400b000c44003654146401d02c00c607040500000c140030586c2e940200500309200c80000d003101d23900010314180400c031501e0110b11003580d002400071030035900b0200344846100030381c1d290050304c0c0c107220340312300040380c00070380142c020961030700c091207098441c41c002d41b40100c1c0707280b015510749480c1c2a1400d40d030038003100008061018219451250014400e1080a0aa049803e9106510784840880380c04180c442003180031942c0c440700428a22070b01020381c0d03410a0039400400c002e0f210400340c03c100c481e0040299905100 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 637917284 1250 637916034 637916039
    0x2309070e19020d0c090602060c070b0105040e0309061903060e012607050d03110c0f03031e1204050a0201090902041802030a0e07030803070e090423210c1c09031407 72
    0x103a2051310102c0348143d8803c1511418528001c0c205030303014040081c41c140c14048034010922030b14207181142c01c21035001409246d0b07069610f00b140070744d600d426401000443d000d620301811910381c03202c041c0b00d95801c100640d250502554844002c0c0030301860f035240142146010444100e1808140482804503000c666481c40001c0000e144000100c1c002400410054140300e410800700c15030b50000c403100b024041810020a42e28041d0544075482c800444e00061031156a40084941c090031502581000340340ca420410380c0c60440040c03ca000036040e080004401d041403007a50141d42c5648034078001d2501040c0c60401030b4202074038006210f959100c560141c0041002040000e41c4a404001c1e124901020054480c03807020107a02d010304081d90411000800d02484a0441c3c0c5030a1b024030a202150090b0390f250004071100070340481a03e011000440108402600420341d56808598007010f14800c00040000081c60b440c1c04038550040900001c2d10800300000000100310881c1c031100d5 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 637918534 1250 637917284 637917307
    0x9061e0212191d100f0e0d060903081302031e12192d05030408071b050f030312010b03060d0602030a050a0e030a120203192309070e1902 60
    0x2e000e09180382442032180c0c8040022904840003680c81464841e0141d00d030001c480c04130b4084100700401c002000744020840d20300718000e41440313a85a0001d48082d000d01424500300005041d021400e40110725090b00242400d130a01d03146607a00760740580906110345180785040c5d140d601803440501ea80c017031104211580c880d08005441d05402d250034024040c030802d88040e0102d02c0e140c01031040d00b00d28010309815038100c4500d81051280030310b006d41e6240d581c0c0c00c158585e4007a0aa0007020f19090503600404078100851070002c0c2c807021281d41d10144117a40030142d892050b0340c20110780c000000d0040016103030a202559005102500b405101307c8203075104c40c202e81c0b00721004100e00c5d60303c038140300521041303101360152850014001c40c03500e02c4072039010b055002201c103e1341000e40c0000014401102109015511512284040c130407407900d06101f91941444061410000035044000342d00003600041132011a158000020083d44400413000722603000460350f070141a400308042522103 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 637919784 1250 637918534 637918537
    0x10051837090c031101170c0d0f090303140711060c03040501090209180610181e0905100f061a0a0e0a0308090909010209030c040213090213090b0109061e0212 69
    0x461040c2c01c035000190961400b030401d50040e2035002d04229410300c0130403170b601000300703003d800c5090800000c2d1035001c071111040c003403d14041c1d0100c07202c0c00c2c1903c20f01015010341010f01440030203544070f0620341e51040304a940c07010f11615401c99601410114190010441c01190440c0c0a2400450100c0140d0049042401d05039203051560400010b0100004000e00c04245c018801013a04045140790030000c0220710041001184280d541d004000b04503a00100c4101409142c00c0080c80082014100b03240c43c0d501c2140703081082414241448035024041c03054209880c030395242c08002c207691441c4144180c12002c11402400b4039002c010b00c1740d544a5448400844c0300d0000159180410000c0c020f0301040030308007445982c0180141107059401207090021010140d80050315104400001c5200201e96401241d4642c40007981080741c0a00e81c030854140c1c1c404460501603000c4890044030055214490040040c1491080c44c450841001c07507000883e40c2e500c111841c500315803404c0d0801d0b = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 637921034 1250 637919784 637919801
    0x204030b0115081003020f0d05010c05040609050609062d1c0b01020105150d051624090303080c090402270a08010b090f090f0610051837 60
    0x200144000400c081c0540d9449101c0a0b40c55103081d030214184a289502d10401600009204500c00000d240160701d5030b504812a85400c030b002401107041c5208080d15542c090f004030070008a1481c1c02003843d0926108981490002074050b03803a0800185540d100e81184640a0400d00c02100503c41541e0040e006802d66262000754001c9122200c101c100491702e0240441d415641042c0403c6600c52403034010700c00c40a0141da0307842c110465803a00604004402005849000000130080340c907030100e008088030642582c10401d0940c03e03000f001d4598188500c0f0050003d2000c00006134440121000340c180180041c00c003508080100c264044044038010340c010200d2810110b04030f007854130311100d000404900008002d1022a540800c0301c4120080002456140100114820b05810080c40390400781c0d0750155481400c040442d04120216441418400d042c040000350101c0704040810b8000e2540c51450904120800c5404a0f90021600c5141c5821040c142c4101c1240c100d00402a0 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 637922284 1250 637921034 637921043
    0x20c1905030904061205070b1b011811010c080a1202070803090c04200412080408060117070906080d0338040c050a0203030a020304020d0c030303020c0c1909050c0d020403 75
    0x200c0b90000ca0500045030002e50000150394424016640400d0000c01c0301d9090b90280750f402a0f03148034843d01c11424403e8184510b00719842d007081700800402008101c411a4031030160651001245001181c00a203986400740202004014030611385018280d003207084508908007505042141d141c00c231842c0c00031517004080d80c00190b1100068500b510a41404504194407561214600c00c03005800d4011401207200100140d5121170501c0000f0081d9401080070b50200c94841d0707102c0030161950700c1c1d00364032407066114152010804c0384403402500300f41d4505a00510031496078600c110060300c58411500e40324008610540c6804026076442ca9089414004001d006014a000d11007181c6084403050100842400030f140169808030480350020103010001d80c81c0d0b00e460002501c0343c3e0b82d6200041c4507600c000000010190560043d0084c5035124007515411001e00f41440244240c400c48502d01112881040c85461015030000781c10030012086a424202c4441200c012644150820344 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 637923534 1250 637922284 637922287
    0x50118062604051f0e030702150d0e1c0e010f0516060c0f09140f1e04050f0609090703050601090207172a03040303120509010b09100f0806041203020c190503 69
    0x410704040e8043d0542800c0d68010170030410001c01440390316070003541c4c0c0003071040a003551044c200b0420070041e54a071b1103122030104207021403112690303910032140806a07060511040c0101350a80100c095003090704041c0c44804280d045540c00702c0d0141d03c40c030940b08028805250640c0810114400c88428241e41e844000c02081c0c21440a061655168803210915a132800d9603ca10b0b00c0f40b04508140c101c0580d440c010314515000c84c4108140d510455541103440e02c0704210110754050003150086409a074800311580302ca0005940701c904030700010b0416800751004010411540d402010424005c102d5084080303019146d202181e8444c0c442500460441c00f0645000701116601902080c0210015441c0929641e0058482e10029081d080b1b001d0703a481c0010300c0c201c800c0d0400320095134024540402450034070080c0303984aa4900440840001064000c5040c03034000604901840c4c0224401c206402e0040c801c90183d0700129084400d8099038040c0405103407141000c1c0c400340d00c80c10196 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 637924784 1250 637923534 637923553
    0x903090603020915070228180225170a05130b07030c021003200318070e070e0103061220060f0d05070c02030d170c04060f2a050106050301050105011806260405 70
    0x3440e640140000c0001d82510410204440788100b04840f1030241166500c031186114ac0e0506504854070303e60340700741d040c2000420340452640980140704d40c009512941440a403181c0c15910a40101c0d9002404942c0703010408000d0b19041000140d03007280341c603011640c100c012094105140c074084051901c401c0200511200e21150a81511101d6060b0f0040440615001d2028541e000181880041c042103258101069119800000191803810700003001c4041d02d10707154050041c40d0350404014000c1d0003000d2083e01c4d00c01c013140d5003214651811800c00d04101c40d101c1c0204006002101070040f0b0f40c0318000140c070240f00344840300700781e0b03140c10022400c40581c50408800090a04041c660b04100500405420408024000150380f800682503110100b81e0056840d802110440c00808080203904004054004005441e4140c0080c40141d99032001521041c1858003100d001c04138a10040c010140b02d40c00500c0c1c5080d07205601e00010003181012070b8405d10903201550f5035005803e4a = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 637926034 1250 637924784 637924799
    0x30d090312020c100f031409030d0605040c02030a1103130b130e010312030507090e100810060302150a0909020d09110a1a090607150903090603020915070228 69
    0x720300c00140c07030000d02514000100002e24000b001c4c221a4240170b40003040c94486071103544440480c2e007243e0084644c43c2404040c06580b40c00c070844070f203e41030a1810100311402e041c050041076034419001542040b0700d0303000c107940d203403c1e22601e0f540601c800c1c0710610303044581856440040140c0c16085079601c44001400700380342410b42025003d40c1044004100058001c0c0540520705004d180004d000c4c0c4030b100c41281d4886096122070b080240c1c010603c100805040c032500f0461f90a031040f80e0b20042036030303005070942d8a42c1c8000381d409050421040203c248130303c0240107688061070304900c0c40d0303290302c0070001302e030000802d0030007917641c40000c241004007203d07900707580035022202110f80600d4081006401d440ca10594588540c0108004009441e240140c441c0c09a02c5102c0c40c120b1001e0f802c044005142442050340010003052001491130301903c222403500030081c0545138103110340600344150b84e00101d412a04075404401d031598030018040841c1800b02485000d5910301c0c94442d032b = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 637927284 1250 637926034 637926053
    0x5060d0b0604031b09090809090612011103070f0206060a03170d0c050712030b100e040e0604120318050705090403140d0b090130080702030304030c1806081005040c05030d0903 77
    0x1600703071078a0004d003c001300d0107d600780ea400b1481258901b019950307540c040340c415414410001010b40c2030448418048101402952048400d44d030f40b2141202d2011003240e0780c0100b0b560403034104802c56010b0000c05d0880c6140c2b010480d04121a600c0c00340c050702c29204a0380001c83c240000b90f004103450003003118200c42c0c2801100c1514091144034040c200050301c2001284a500c14000d82203000d400300e4a07590400000ca88445040e15502d1400e410070300340903429003c13200006031420492000c100c80c510b034079110b450b402400404030f181c01c090501c50011005072041d01488172510420030f03a610040014100010300c0710022030702c00030780703014051106011b030000040386410700f612840d800707412070300480c484c0048983e00c44843d03001d0404c1c1449206040000e50103010000c1c010050000081145048800d10100941c00c0d200f8280810300700c4205004002c0150042040401e04420b01d800058100d401750302e082c403e86035a803002903c3d05c1c00011030f030000b044100d4010002d1225050 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 637928534 1250 637927284 637927289
    0x18070f0609050406170c0904020f0d0305030901180f0b0406060b0301090b041424060706020c0a03020606030606060a180503010e0d080619030308040f0605011d10080705060d0b0604031b 81
    0x4a0310f641c44844045c03059203c905650449003c1c0c2007010000c1e040d90303071b4090218070000c00030301580010840c0e820010940d520895154220f982080752a64519280180141e80f06400c14008404c10600ba0b03503282c00c0c04c8000e80140e507075540300c4001150000c01c030f0000314000e102003200010000324240074801600e94002c0202c010858200410910b400c500716003040d001204180e100b01110a80006807160088080c040c060502c0850981210400000c070700c40c0b0301d0702903021204183e48890415650746011228540c0006041c400c2130212805504190000040700c40d840045c4d54a43c004a400c6136540281b2510a80c00301c00d240301443d8200805541004060f07400140b503030340c001098060a84203110040400caa0203000405111a40343c01100c03075540301d074050215503502ca000000400c16a100b5203030030740c00c410200328042c4d00c4000810803221580050a1241e141100700500d03904419200b424031030f2601381d4078240c1d5071041c0c0140080c2d40300301180130341518035004c0c030001e2a1654 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 637929784 1250 637928534 637928549
    0x80901140c03071404030602120f090106060e010f11150a0b040905031801020a1401020703141c0c090302150a02010b15070602090a0302030d033218070f0609050406 72
    0x40c00307811503001d01280c0c0c0c00360503410700c81e040020825104ca03c502c9954009040d140c4080341006a8204281c90036014140c0094800231584407400021f080720090320030080442d20302c1c4514510b950182ca103904001445043c5280001c020700d01c04c0f801c003035400c00700903501e060680801105240c0b500c200009210240c030100600003460f0b6400342e40703106401c020302041094103602c402c140c0c4204a00792a6503442060101048940c0711900d011350044403003140814000403a0100c12031400c0c00b9100391b560440c04003180303c0e080d1040d040040400600300d03020804540c0700440540c940c00a2415890700784414203984005c0e0500003401c40310f903c4606440745602080c104e20b43751406c010b40f83d4464000d071005a5515418001404407011075200075014000e0790655000140c040c4c0c0002000f2144030200e10360803400d400d56207031031284014405481c0b2684000b088002e01e074005800401010207040f20030290303c44a0038003000c0b0703040d0b0000e00082d110380c03018030950806010f01c400034100c0 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 637931034 1250 637929784 637929821
    0x120c010b0a080c45071704020d2a0e0a02070f0209100b0c0f0705010f0801091e2d05060a0e09010b03060115090602070b0306010e031e0346031506080901 67
    0x2010003c074646c5002d000a48121702c0d0301c0741107091201020010110400000c1c12030030494108944504600380780c8a40e140007000c2d08001081c0c0c0c1c00134022140201d6000800310a48a040d07400c112003008064444402c001c04402d022030032503807941c01011414a11001000360300300c41c03141145880381c00d810050410601d41c61041859402c20040c034107413940554003003503074115403d030703074248003500c0400401d294205180303651520826000001c00f60b00400f60450810503116a03c000d82d007007030b1349d042e80210564100304440c3c3c810501141d0810308000003c03c0804010002070724000083e00703c4440759514449030709003290842c100f1001090a800500ba025181800fa030000d404018043c5060054030807040e900d640d020f100e2041031200740718141c00c9440443c600141d690f00110880041010000603a2104103510b2640d212903911036191600491103858407203252003880c0d00c0080034541c072072540580509210141c0c0d006019155110b03022031500c40741d014290f40300c0b408580c101c00c92 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 637932284 1250 637931034 637931057
    0xb0609010206040f1704030c26030f07020a031506080730020f040f0b040c02150a241202130b0a05090603030c120c010b0a080c4507 58
    0x20040303401e07540941c00c540054511180350900f021701e41c4003654511168000050007004200105c1d060340c0176504507498886060524180c81030030300a00100702065a4010301c24951080907840007000c032248040d00002c022590780c0d48420400155807015030b5003607150b07201404050410000007008081e070801440f44290600d10843c08200d20100440246001002000654803800c0703c1207035410000d4020410900d01411043c0108854416180b15506041c902440d903440012040c3c08820005508052911000c80300307401414a18404001000c0007181e03800340d1049015043d008001100655160304080d104001c0c8044030001020040c030b01d401110541901d4000303101e820799005848030301080d224100000d18500802c003c801c8180b24543c864004686810080c109800c10711000b4881108072a04202041d417960040f0042350b070241d20b201c1c145e8078001d111200c5079801c0c0710f0307801d407010701650906494020001c200152007100c05503814090741d14000d020303482401e03403030207459108 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 637933534 1250 637932284 637932287
    0x606070804090b0f0607030348180f0e070503011404050711030c0106170d02060a0207061e0c12020a02030a030f0e2d01050f010909030c0c060306090b060901 69
    0x5540900b800721a5141501209610340d42016022000001e0000c0c1d15078030a40b6004014082205110191560b150100307051300b2110009c003140041d820031075000454415004075104841c40c6621030820280b800429080d044110010028103805040c1300c030030321300b0300c0400045400064101c00c10072100f0801000456542144075407502821500442c803900d901000700d8410076034500c162124000050b00ca42e0a0f07005600010071103a20b4036904001c41800e1041d140c48001c4203002d000075030040000a15400299030040c50013500c41e40c00090803410b8101d070302c85101941e030310024070f403966102c185612980080590040c1d440700602940ba0049543c4001c1d10b90042c242800d05040e12481c042410600c43d401c001c904a1140040b40c40c20101609050243c0180c0c0a030900e465017804040c550202060207030b00c1c8106015208140d05928001c0d2205c0101600031066003004020300c40440002e88540c2d01c1300003000256404603280742400000411a030a400c2514814003040292004d241d = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 637934784 1250 637933534 637933537
    0xf1b04060c020f0411121f151805090c0c0114040506040209090307121d0d03020d0302160f03021e0105010305061501171f0501030501030b0a11040f060206071b03021f0e01060305010e0606060708 85
    0x25005454027901c4000070b01c41546d0175412070341000d640224500e04001420301001c01400141e9403000c000d1188008007299a40030300420b60703000e41140c010754002405030400b10030701c3d0b070001c1070700045034640f41c07080d22100e03040c031003038084200002c4059007102480b00d030103000c102500100703d4241d040e80740d0796940030359034485000400c8103050300420f16100c80c00c080c038200c540440d004061880700d908240340c02520303a0b110303000300e1000d000450700c40042800148034690507030354000020719054803840c0e0b82005080032048224100522842800503903190900c3d03850150141c3c0d8071507911f40c11184820020820720741c1110f810517240400400c041060034102d00d4010700c0b0600006040c601310a2160980e1040741c01c0300095021410000901d0359001402d1482480d5554410111040450320020f207402c2c1038501074016440801e140268100c02c40c8074600d0403014501c00110030300c0c1c8100c820b0965981e944244d507030f65034034048010210410301441c0c0c1d0189007298683d250000d51360b290b0115 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 637936034 1250 637934784 637934819
    0x3050f0f040b1801020706151a0d020706020f0c0f120a020303060907091505070b0c040303020c012a050a020406060f09060c050c04050f1b04060c020f0411121f 70
    0x41e6410b040400e100042c910740710701204090800a6580302d54a041c0b1f20041d00302c40c1125010305001030400255040605034111109860203501407800c65004805c2c406900038074000c2d92615401c0040c1078400001c0001800c52140300005045602d840e00344040c10003e685034446007041c0100445002c00f503003c000c5950101c02140c1c00c14594071100803c440008254225902d145500c515030b00c10240c100c0090580144500518011551081c0c104e000e1400740e13100080169004800420342980a205440f0103010b800700700076406044490a114841d5005034280d415070040c0110000b582414042c24003d410b00e81000c601c40d8205d080c009050b0141c9103c0d5104011048840004100c410300c00440c501100030001e00040c148218003c0e0804025503449651400a48a40d1042e4000034103031012594541c69100000c201d46d002d01000340c64014440c0e6015580d0201050a0f100c40c10142200031503410300ca20042c43c041200300c0107028900e0180f84002e248131810000da4280025502c503 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 637937284 1250 637936034 637936043
    0x50417391c05010603140c030d1403070c0c0b0703030b030114070818030a0e0f010903030f050702061215090702060f04080a03021c02180904151d0a06020a03050f0f04 73
    0xd0340c100c0c440581804018540020829404c008000007030008a40583e10028145010b0341d6403001c2e804101903071030032803004481c0444e48140101d25101540c2001c2c6602444a09014500741c0080d60f039206005141d420007000000045030900a15901d481030301d07000b907000d5008000701060720400a4000c08006c2103030081040c2c00000070000796064002d6840c00f5014422207446021100014121040f1404528007440354002d25001e20b40c85080844200c2e030b01503d844010203042441221240d0111100342c2e0000b508000100ba5a011440c11034450080104045100e227003a0080002e88003001d04160210343c088401c0c400743e45044804a90001e5111030314554800c0401e8098010340218135013402c0e0b5003800001e80e03548550340d8004203200070084100c40c08002c1c0301c40c10000100c80c2554041c00754003c1103010320b504c0f03800e035000040325081c0c480c41c0c001c01200074810a1400c002d0103c203c900f06d80200c0c160840607090b008617a0405030044510100d864142007500800c8030090010300f = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 637938534 1250 637937284 637937299
    0x20604030b07050f0c01050403080601020303070f08100e09030706050606042d090c090303081602030318071203110601051206191808070c0501181505041739 69
    0x200b0140c05001110070151070003400903220801118014001c2c04100c505030045904540016015071000c0b04a9100d054180c6414848260740c41003100d0a00001b010400b003034080000210b8814172518205105106d844010343d40da5107146004e405407100030300b440340280400d010a1008010040600c00b0301d0003130398038070000c5a0790103031403560b0800180d001580ca20318020901c400f90768081e000310300b502e010791220503154841c40101c03561504410419801604140082020500a5840804c04042510440d590760752165581c60030810044021808215190903148421005200a03801418100d81010303030b9040c0c04d2042070300c0b010000e106001e001d14038072400b040c60712170f544040800c00c41d0307400b10300380c2d4007241c40d1070354042c0d122010680f00743c0c982d080c000075258418609007421a4805285400c064031b01264040d00c41c101c100c030902801340903c00072901c801b1211041c5480c0310080010300d1000340445031081032603c08802e001500c04d20f000e040c01860300500c2100003d5409a9500 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 637939784 1250 637938534 637938541
    0x209010507061a04111b030903070e040c0b031303180b0d0b030718090b011202061207030204080a030509130b010509152a0f03090a06110109020a08070807050d020604030b 75
    0x71081160f1841c0b29580c41850701c1c040114218600d0090001e40c00d1a10304146484803c805071562400b03501d8038154103900420051040c403544480765600184503205441085840305030325160341d0030840300250204e401c1c5510030240b690020500e075450001405a610107030501d604100d81d44144107041040d55141c0381c2400c442e0314200403d400900a41c0ca420300d100203240410b0303000d49007088090b40d07007500b60000880d264001082418880f0b90051442e4034203403911440c003000c9034005040f0740c00d142d802e0100080e0010700380803204070b0901c01c2c1d540603a41d1250305d041111100722000202040e6282406480c2c2a0360020300b103810030002182c03000a10302044501804038410040440f04281c04400305002c030b40d034801c1c035584000c0c00020640b40704903c2000c0590360b0b03009080c0c55030382c840b20010040004600030211401017681d41400860509025004103502c070340a948170790b050364400701c01007001080a01070038020300310888a1a140ca026900090a03074012400040d0075503200d903022 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 637941034 1250 637939784 637939811
    0x30305030c0a170103050c01111203040b0402010c12050901080c0a080a0b04020c01021201051512060d06060b13060206011418060a0f0b040e0a0e030a140d020c031804020901050706 79
    0x1402d100c008460420060f03580c40e4030b04140c668072031464a40c0400c3c0d5255014102c0040401c9601d61a00c0c10b1512038110796544d11801090f1001800603414420074540410100d407030302c4150040f90503241c403031a035500c3c1034500040070900010400341084606100017030703113291b104804a40100c0e4084021480440040000b8001c0c0b10f80d81c000e02c105d6100041c80c8003012880c0300700314120344007184c03c0c408000c400c409250a6104e11510005003401103c0051000e18100a0303144440780110b0380040c180d601c0d40b011818640c09102c02c6c80d004004c1d081d0421460303504010740703809015205000b030f2218800c40c000c1507011b0b0140d01244071081159001841c4c03512844062001442011075146101e0340d07500f495002d42c2c0c4103014181c809500325000400c0c1e0707592801040b050b250404011881e024009504699461360b18800881d20321040000b40c0403040030b8006407038140e691402540e92068040c0c4000220310fa0710b80030724050b50040c1300500d541c0c2e80110a43e4000c54001501041c0081401c42 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 637942284 1250 637941034 637941047
    0x118030221120c0a11060f0304030804050109080a03090507061e0311300c0406141305040c03020c16031220100606081305030901050a02010f05040f0b070801030305030c0a 75
    0x14407100031010805a00711080000c2c41041c10b03001c0c02c0e0117014900c0c018140001d6101304020703014150410808100004e01c541d80d1a03034014090700c000954801660b60b103001942c0300098410004e521400558144401441200c004081900345540440703e44000c0e03c5411999000381c10a00d0f030340d014489041601d007003c440b2122401e10141d0042c0043d400f984c454080c11003507202000ba149030001e010b4141500c112401c3c1c41280d00c1c1c40c0820107005c1c00000503a48410300c0c148c0908a410340000b800d03201d40c0a00024034000d80c03800341e112500010150310b0004080c1001900980062041010541400c1e6103c1c0084882c503001404d6419100d680101c0714440310724000601c940034006c0060403c9501901c1610101d40c0d5070096915484603601107400000c4016003560070410082030258014002040705650313500000c15050200410f00781181c008540644403200c0a01c1da000c00c002d501070b189548401e007070074100e0043d4190784000f1f0640c0030081511840ca05c00040040341c0c50700801 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 637943534 1250 637942284 637942303
    0x180d20010e060412080708180309030a080405040b0a0b0f070c0f0305030d0b040b0112240905010302010f02120304020904020f0603041101030e0f10090602130e04020118030221 77
    0x1402072208000000c180c90341c82c07004840036240808404403c2a20621400308a0b000e03580d2541e03009010b496141000c0000d001811882c00c480c07100708207000a94806110001c086030081c40e44980329450300b001d100a450440d1961480b4250302002030100c3e40100f4190b80d131041140340080d032900c070f0b585414288036004d5004909505d103e01d4000003001400002084d00c0e585075074051100202c240c003400140ca01d9003598501003100700c0304468001b04982d1148450740d0417100300b094000004a480c0000544640000c14695194001841956081940b100d40f42c0b5242c4000c0c500840f1b990b08142c0380d4080903000a02c00d60140300403c0035951029001c1f445124001e190b140d070380c20140381100e94000e500c0d0105000c00d080ca1101021a81c0c00f140041d61601c0040203400340070406002d0070010301c0c0d0030200f118400e9003800302c0000c250740001104007600309503181c03d156081a00000d00030a071018001400b48034100424030040e1203150200d00d000014260515003162100d07030080c2810480c0 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 637944784 1250 637943534 637943597
    0xe0d2a060e0a110324070320070524060105030c03040c0306020d05070e190e0c0f040308040603060b03270a02102003120601120b04060e0402010305180d 67
    0x101c0c0b82405103d4481428034000c4011400c039441c0300c0d03800300744103004104051941d40d01c00052000070181070003500203c0c009034001840e03c81c0074180200c044600d80101c5405e50744c1c1d038401300740c3d030078100d07078285110b604410400e10a01591500d000000c0481c400180105003614010001c54204003044078114050769018205545441421026070000d100481d064800103480d6000c00996080c0b0540c9a00e4a43d00b01c82a10381c03441c203021103101a036802825002c07070308604101265003075890380040c10146100f00c102e50365903807502c58002c0076a000340e0841420724008009100c4000010281407105181e2640c2000780403540038582424460003020182d00b110701f15181410440d4407100074407020111407506086840131000843e0b4034080c41c20301c484101d00c0c50010a030158001c2c0003851910605680200b00d1480d000d005c50282c1d1001c0d07008900ea01230840c144405c643c2c060049070391244c8030090700711030418154090340e5146a40c40044c41400300305181c1c00f1002664155140742c0450a = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 637946034 1250 637944784 637944793
    0x151403131403093f0c0d0512030a050f160f3e010e030f0a2a110906011b020402033705061e0906180a0e0d2a060e 50
    0xc50985103800c451500c04142000c005010440b01403802c0b03c051300011480800403c2900b8032201885503000000000b80e079a4811802c81c1203c001c1c0c4c030740c0210f03c40c103500d501c046602d080030700e42104256400790541820240c004903407100300f51303c0f0b80a070b1460321561030200b07003c52201c1c003500c0c1c1e11a8170706a00003c1001e05c0386039443c15800214915031510b0145c1c000c12640f00c140b51020380324058004078880c080010081e950741c940c85a00307030344207881c60650f68840080d11011181500909400b00b2101030354442b0b01c40070b0f545040c1c0901980208282050169081c02c1c5620034129200b44074002c0c45036034044040354500c0707013122a1045d074641807a6500307802603001c2c60030416281500442840513040c40c002070f005040c0000c241c1d8107802840c00980e40c501c4400204400c0000c01000d854110303508460547e0f001c0c140c1d102c0d05005001110001500d405001800b504001703c95401400f840f8000305640102c10f00c0c081d60b00200b640c508c5171307030540320b0b03951500401034802d01d8220f5066118 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 637947284 1250 637946034 637946059
    0xf0406150e0421050a050412060e060a090506010509070507030305100503010221010504020f0a0e06070816050c06192307031d1f0f0207050a15140313140309 69
    0x264a00401c0c40310020b043e608400d50180034101c48034400c0c04041400031b4000d000400194030710039034000f1054495980410380700ca030011003914200f0101d9074100c1164030b60803010140001401100d016110a40d191010362614034000307402032040319001020140e0701e000040c2520403500030f2802919000700255500c03400700c0c1e50703245851455000c5e0784e00b20300e80b00000500c84c17401d0300c02c5502514100f00a0f40c00c183c3d040009a6011080003981604104200700314400540414018814900062500707000c1e0721050408500d00700347e4a10150180c201004481d80301c0000316583d543c4040c0a18220209000048080c00f44c92085002d86048200100d0203c08050300b110110b908185150010302c0340340c0d03615082001c200189034120042446d880c5074007160314400d00c5220703407003403960045540305036403200803034400c0300c0c580c0c0000c417202184000000d0165104086c500940520b418407030843c102070900042d50b00040c5002014140c0c0150401d20104003441554035490300105141c00420 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 637948534 1250 637947284 637947293
    0x1050912071703120105030105090a0f0c051819050910090c0503070311090903130b091804110301230c071403040806011401080403170a02090406031112060f0406150e04 74
    0x4c01c14060070582810f07410002c126404d0520940784100102e0000306882c400c10f0710350843c500701c2c81100703560b240b112810101e00e9480d00710520a050a4040151035079242c46c1c10044111440c448142544d83d0400c400e102c9001c030300080c41e244007031b080c00f03000a8908480c40d2050560b10103501c0a0b8040c05103803000001e00c13081550140d2407000a0710600c01d190fa5a8500f1610b030f1045400e40b00541500d40c03800e104c8000c02c0c002030000f80030080c10424003101300c041a0b040c2000101e9013103038114210401d10340941828064594071629100382100342c1060640268034906004000c0c10848402040305801e000e41726129014290300c1000340d9540b9600e81c1900c079160b2030240284840300303c1c6600d66440039445079581c18811074060390703450078441c0d600768140320180380a02850103a5801f80000216070781c680c480d102c0150321850400c50305400200601c142580c4030114170b05250030038003c000c085c001081341103901540c404400140980c001c0c003071280b04155500400d22400d0050200030400 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 637949640 1106 637948534 637948537
    0x1080412020a2109240f0909020c16050d020d0212012a0e0d0b07030509070b0c1b09010f061110050708190513020402090f04050c1c020901050912071703 67
    0x82e5911030780024ac1e044002e441001da080000e014102003000f400d0400100303026154040003050320340001d00e50f09002c081c0680141d4041c00744c061140130a40c012425401001600d2030f640e150001c0720311501c0d100d4500c50020641e1682880d0103840d20305240c8041591000f007403030359661642d4040300130305809070040085201d103403000304414000c1d0001d403103210211001010700c0380042c40084004400358411901402003800140a800c0100301e900d8103039200c43c200801c17030f800484031081c5840442004850441e141c4001d1007002d07940108502c0c003503c000c4070840c0d0440c84910b841d03c2150f80580b411182641d20350a40303001800d00d034019008180b0014020003a1400c2e64010800b51842103d0460301c50700001821521260001905600c90381140800c60414220100180681c80f90241c45032242210510104a11504114150161900b243d0348020401d80711840307980c9 = true := by decide +kernel

theorem cover : BRFrame.Cov 637769784 637949640 := by
  have h0 := BRFrame.cov_init 637769784
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637769784 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637769784 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637769784 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637769784 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637769784 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637769784 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637769784 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637769784 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637769784 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637769784 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637769784 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637769784 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637769784 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637769784 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637769784 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637769784 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637769784 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637769784 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637769784 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637769784 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637769784 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637769784 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637769784 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637769784 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637769784 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637769784 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637769784 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637769784 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637769784 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637769784 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637769784 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637769784 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637769784 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637769784 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637769784 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637769784 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637769784 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637769784 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637769784 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637769784 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637769784 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637769784 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637769784 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637769784 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637769784 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637769784 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637769784 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637769784 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637769784 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637769784 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637769784 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637769784 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637769784 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637769784 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637769784 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637769784 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637769784 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637769784 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637769784 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637769784 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637769784 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637769784 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637769784 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637769784 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637769784 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637769784 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637769784 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637769784 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637769784 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637769784 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637769784 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637769784 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637769784 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637769784 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637769784 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637769784 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637769784 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637769784 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637769784 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637769784 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637769784 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637769784 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637769784 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637769784 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637769784 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637769784 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637769784 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637769784 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637769784 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637769784 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637769784 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637769784 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637769784 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637769784 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637769784 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637769784 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637769784 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637769784 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637769784 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637769784 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637769784 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637769784 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637769784 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637769784 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637769784 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637769784 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637769784 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637769784 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637769784 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637769784 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637769784 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637769784 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637769784 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637769784 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637769784 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637769784 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637769784 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637769784 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637769784 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637769784 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637769784 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637769784 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637769784 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637769784 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637769784 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637769784 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637769784 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637769784 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637769784 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637769784 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637769784 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637769784 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637769784 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637769784 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637769784 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637769784 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637769784 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637769784 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637769784 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637769784 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637769784 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637769784 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637769784 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637769784 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 637769784 ≤ n) (h2 : n < 637949640) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
