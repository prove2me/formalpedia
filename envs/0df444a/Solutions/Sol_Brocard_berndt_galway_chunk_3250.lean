-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3250
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T09:05:56.858742+00:00
-- url     : https://prove2.me/submissions/35c846c0-1e37-4f4b-8491-db4d37903bad

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 584352517 ≤ n < 584532374 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 584353767 1250 584352517 584352529
    0x40303050a140f1206010e120d020d050c0c0103020703020304090f051006020a02011403100807240912060f090f0c06020f011a0907020c0a03030914040608102711 71
    0x44a1009030b40c00901169028803400f0040320107102034113201c440d00396100001a611b14241c400e855030000085241c9030000c0d41c0025103801030030b25540172504c0c0c00305105021140d07440340350f044480b03e4018a50306038240d40650041c3c51002d100f0f005403801d064036013a00100f100d03902d40702ca00703d840e114404c2c00488064811160040c1000d0300c06440b600d80c0e641c0019082d1082c40c0034400c5100790010000c0c0c3c4d20000c0d80b44a501402004058406107680e42292078404003440c03012511050320001c0c8014401e0160544c441100c0c008001900c10031541d031100c10080c0b400d4401000c03620345981c14140041c0c0d14050384611103229011501c00e0a00f440d40091402100d03d100c8482a0f00d444240307400c0384035010b5080c03140b07501100c0ea03054554888000b01e00380040c0140322500003019801c0031040680046519081c2c0308044144003d064689042000f82c0b903041c4120b080c01d0300000740c141412055030304a105460001715035074001c2504802405007041004030143d44510311011a0360305d502c2e1007 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 584355017 1250 584353767 584353787
    0x2103060b21040804081e010605030f1207110607080c07140f130b1f0813020607081e0a020307060b04020c030405130e06040c0303110f100b040f02040303050a 69
    0x104600d64106400c0980c540c40e070305000000c41c1420000900060200911101118081c000c000d083c2c6691260109060a10401300710340030b6259403c1c00b001190500b4001103c9151175440401000ca00a84c0414200305a1100c0800c4d903174040032204058081c0c450000030f000c030f54820f01c04540c0d5118020306990910200c0d8005110b41850580002d00c940e40d0300503d64400700c411518109030307001482600000b01070000354240c201ca07020628182c040d40582501c00410f510791030725004c3c0d80e505154440d141c4801c0400961080c0140300800204960002410f9100d03803042d00c030140c140000e043d4a400e50021604580140d20000708035040088600030095400e4098609605001c26244110303143e00460107210701072608250130810941090700500031744842082910698140307800c121000e0340c2079020540124440380d042c031010140020729044011032080c09403501901c07900c907000180c401c106503568055244e000d5484160361901c0100019486915a1940c45141d0480a001d01001c = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 584356267 1250 584355017 584355029
    0xf1104090c020f0c100c02041d060f011203260108060a0c14040306020f04091b110a020d031b0b0a0e0106051f0813060e060105030f0304061d0409210306 67
    0x10104040d0703243c0c0d000003021103043c80100c80100511307503c1001283c5c10452104046d50083c02c0a504817450b20310403003800f1032070b0000c03020b40d6a00e070344468500301c081c41e00b07100740a42914011600705c0441d00c40e10f17100c00101684018a900300421051543d000c001c00c0c0c00ca15000d40000052011400c42c62159100300741d4182010000300000000d1038909016034032010708481c2d00001e006807005035840468010313140c6240708100c510403442118545c0c1c40d5034a2504c01042d08071301052082040015000003881c0e00800b400c40701116650119100041c694040070700c5401080324200081a01d00d15078421a440080011040b07003c5410a0940c1d10030341c8014015404500c903191400c1110580040c01c618508000c40c403a107509007002d4030a82000000703400d00745071072900441c411005c56a2412520304400300c81d1010207201c049526849540b10b968081342c9440c42100d8498000302410005071002080029841d046440d0b40c400004040c82803003001a04480c00c0c048160036200d540042d0074 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 584357517 1250 584356267 584356273
    0x50f0a091110050408070603020d0501050405010b1903020405100c0b070e0102300409090c0608010b0a20190b0f011809260d200301030f03030f1104090c02 68
    0xc060740303451a03484910018140165095a003942d019405407040310014989802113462083d41c0d444014000d410825400816030700300000010903142c240500c0c2d069404070464289444008034801c5100d08040c480c940c1031607000c0c00300007095a681e6601303215146260b268449a114180340c02d030071021008140d1824081c0300c3c1009032180e680062032100c4e85040050701810030054071400804400000301c1e4810794440081c1c081005040342d00300c00c0b031144c828080f00050a40f141c030203031500c6809000b10707185800c0070f0190354031491180704035203c46019a46045408080000341074209260b148003445068911a0040204441b40d811503074410204401e03402554108521501440884040c0c0302c4040d480380d00d80d40a00440341e024000540d0a10204940035803d5a08410540c00041c1044030280c5404160640164010201156448507810151440c0c0c29035a9108000e030a0180a8080599691031003808040301d1040310864179004040c5600e0700e140400310000e5580d0740b0a8001150 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 584358767 1250 584357517 584357531
    0x903060115020a0b04050c0307150305090a0201120b04020f030f0402030d050909070f021c110708010b031c11100603150902090c0a1103041203090605070c03170706020c01050f0a 78
    0x5940403c0d150b00450b480424001d8540b22070811910382070902460380da2502034800c00044000094981c80c4403100076450601907503485c040000d403145136400c40640841c072541c002d1403081c2240e0b84086506000100700500b00106000200301c1c913001220071a8a6840100130b01c01580750821410390710400c2407606071301d030000c404023050710400040c20a5051104010310a003034140240160070f1045902c0ca0f000704841070058000b07044050746100440640121803012403c0709043c000c4500c6500c0180090600703801c01164560329140c901d02c61010041d07070810030201684144035039404204d502201040640c11400c1441003454000c40804035140303090015001600e841484590161302103241c0c94072802c03c2d0390280ca40014140c03400b181d90200180103d451403980c400218458000d41d0740140b2207442e6034080d1807522840c24050000b19149504000148845c20a0011010182045420400650754000503a0008000340403203035140c000300304103180041d5403d9800b900c20340c018071840d = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 584360017 1250 584358767 584358809
    0x1f090611030c0f0702010306030212010b090709030804030b1f06091a03011805061f030501080d090e0a02031308040e19050c04090509070302090c19030209100f090f0b09030601 77
    0x1d0310540c0e110043e00e5101240c0d02d0f0940e0f00030707484070340115006801901000c615a40d0f4500030f1450221480c8510074203c045214580b15002080c103036544001d400e40307010300b5911000f0348101c000f4003405100140750403680c1500800036a410003024581c0707681e01031a0801e180c031090350f04070f48101e00c40d9800134001003090141c9444004c480203c0000000b49c152200030200d0128580c150103503012510b0442c951743c803198154404d60480da046015224148902101200c1c03002c0c051041d0001d07442d00d503000c40c20354402d690045070040750b620b40004a1102c00e136075502d40ca80099000b1442290300f042005484881e2010840c5c42e0314000504100a241009030500c45005078041c040b8800ea89000040c0b1448003045440080c60f0001d244107280c1c4ac181e0306480a5901812008400e0302c95402112086030080c0251032600000038103240610100034030880d415600f5074104402c000e2101c200041ea280c800034104090040140e01c5079039480701c0c01c01d0510b00401a44003c181c0c00c03400405000c0 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 584361267 1250 584360017 584360041
    0x15010e060a05010f0311031e06030a02280302040603140c03010e07120201110316020111030a0801061215060306090e0303090706140f0301060e04060e16111f09061103 73
    0x941c0c2e802d0904a0300f843d05004210b0040002d007035004d505210000600070800ca01403600200010401b01d1f440c0c6a985040a06860382c42c6000000d40040791a988600c0c0285065007d031030600c50458210340c180d41e40e400240580b58264000d032030300c414900342c01313484d558107208070300011005800a00020005513010703075a4901d00d01c41d1ba141070160344082d10840e80302d02c400c0303943c0102c8a004ca9484610025210565950b900c500b2408070b034480620f44e6094501000b0303208102c60300c3c0c9078101c180c0c0ca4038000381d4140c02c1ca100044c241558600d03003000b407a0034244448000d410155800503529060004400458151491107061a401030041003426080001c21406452203840d041c0c0740407401e040712201500800c101d0011401c00130002080055010a030614808400c5500303100c05940d52501c0464204c054031000c007080300c560409001c46000d0120700c0ea503040d4401c111408118565a8800c4040164100c000440d45a03491401448034a02641c02405004510300d03145090a902e4545 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 584362517 1250 584361267 584361269
    0xc210c03080c03130e0703060e090a0803040f0f050d080117030d0b0f12010504170a0f0c0c05040c090e0a0501270f020403111f050a11070503070815010e060a 69
    0x1240600140400802c402801500d2203030000340b190008180d21881a07007491281113030911b000078034080d40004c10841080c1140c1c0980d40080103004e50340b81e00d4407006140c0d130008000b0b489048203080c0341c100050850100700b03501400f440182c99100c3c5926001003803100103034000352025910540c0f000900c00d01104954900da0342150000e02c1c04000008142540740f030000469000401c400d60149100301900050302c500c3c403c955202d40c0e01c0907080d481c022400350003c11070000d40510544030000740a4540c140d5800d00034031190681c266903d0015080d074040400100024156400030040794244e01d810a80040e1031840510103903040c03030b10362401001514458a0b07001442d41803040c245065a01055100c02100429583c90b501d90500071180f4011640341c6004865000c02600310918411302c0409030300d165a945854401c20040c111203005200351040941d01407684001403070b940c104290002441c0f044081d0455000030015065a450160f00800010203241c00300b01280d03403601030b040 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 584363767 1250 584362517 584362523
    0x140c0c0c091501230a11010506030d0c08090a0302040e010e0f0312130c0305010f02180102121606060e0f0f1302010e04111e22050a140312070c210c03 66
    0x210703c80144104a003840c010107044034a04600019540c003170707964403400181003800850001c1c88aa101d801c24181d071919600d0410001840b4042a040002c041c034000313104690300280078a01060b200d030009411694258881205030307648000036200f003801444411403030100c89000c0d50801c034407224140c1c41c02d1030042080d040341f2040b0300c102d410004d8013461440a0750704200208144200107050710b00a6028042c200341140008a840c1c01d00d40c80016002c907814001c44845080102140b480741d02c90120320030403600b840c0c44942c007041e80065441d01601c140380f160f941c8102400c2c8200702180c3d68101030550312100c0350b02c015000c0544d03003060b012260484c040e04c1c0060307c40301140180416003d41d441c104560a0001721a00800000b00c000e0a04035280d0242f641c42c00d00c050035951312000703551003110341080b41020200046050134070141d44102c80502651100c0a5a0710351120607840004101c52103a00c000091105510511150341c00c44c0812016030864091500c81e4414190540300c01 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 584365017 1250 584363767 584363777
    0x3380901080a060209060d0507170604050403090501110a02090406020717030c070f1110020c0306070320070512031e010608090a0f0203070b040603050118180b0604140c0c0c091501 79
    0x5d074181d1103240450b440c0c0752040340d041085050110b4001d1140c40c150700c01004a444441c003054161515100d250301555158070b40c01c6443e450070380190b840c021a00709a0880c2e000d451004c80240e204d0a207100e105503c102001070740c41030540f8020000b00003e41050110070000d104011444050310f040b1038020b50030110449030b01181d07103801c4110030b400030705841e002440d001d040400d007130300040c80b0820884110250b40702a580c9900484c211307040c0040008a82403807414a196001e01c1d07500620306107010303100340d43c041034154000f1083c59100b44c9143c0d1191000c0055545034800e140070080c00f4100302d01d03026200382810381090f9924102d905010303040031600c0c60100215542000002d008150700c04c0282e4966544440240c02000c007480340001c032b0000d0400c1c4500f40100c2d441a02d4100d4964030b00c0204205040e208e11401d844014001c40d00701d6502d15912291824540089108440c1018203940c0c2e0304c504030b40b860603c40c461900d1800b940c00340092180803429990100752100081c601 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 584366267 1250 584365017 584365027
    0x309100603020a062316150b0a1208120f09010c021605010e0f0301060902071b0803031f0503071202041803050d0915090515070212071203380901080a0602 68
    0x8025454680092418a00c001138246c0c01d040000110102c854001d4859007290708000c44100141c61300b5402003940b0081d103440511454441c501e8110300346000307030b8046d810244001116000751a003987e025441000110412268003424007070109010700610140001000250f50100c0c1402c1c01d0040506000c64241240c00b1341d10340c0b000003d03204c0380c000c009100d9541d950030801e00951210300240c402049002c091010b020341c1c03036505402c803010040110314656801105e0403a009185a0468400304d21100005070390707404001e014047c0c40181d24826004503140304020450716080b04c5050380324504001c05c4042500103050f1078404c400c90300d0100d1000c0691529200d0000c000901e0031044d0314090149040c000c0000d007980c1d051100d41c03010010f54442c1c40c4103030b035581044248860390150030442540003d601021100000070b01d81004111501e5410004910b480080d2113202c004158000000641007042240103450505448804487d41400e10440d12160f03c0207010301040d80002d1 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 584367517 1250 584366267 584366297
    0x280b0901020c1504060e01050408030703150e010504020a0c051204090608010b01081f0302151201050631030b250c0201200703021206060102060a0c17101a0309100603020a06 76
    0x174401d02206c00020080c42c5018640808150425602200001d28150412154461000c070150580301c00c401940b80d280e203400d04010180d400b900d044c0d000c200040308036100103101000b07104136004002c00b131281c03102d04003c03411044940aa1100320300f681851141c28269030040c001e1a0054501030480d4181ca0740001f003607c2c8503002d90320094002c0c1600804e64400e01081010300000c0e4a0304d04913140d2641d0310000c00406002e520b24030060340145055132002c191140d011080c01059660441c1211350f520303151000d40c108101c455142005003016950b4807a69448100444403640713040c415115030302c580009080d0b803119881c0e01510409602200e2080341c04004207001194010502038182c04402982c0d0388890054495502610076107000c500080804d010f0110340d00300d20364031400502918158094400c40180c03c03900c010602c003402180d030242c0b0100b0302d03a880600a41c85035803070420204003850590b031180c0f4643d203a80b5024003440140c0d80d62446404440f5130f80350401e81c45510103 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 584368767 1250 584367517 584367521
    0x216021207090537111206040e0f25051c060c110a030c060f020a0207090c0207050904020d020d0803100e0108030c0303160203040b120411040504150c02280b0901020c150406 76
    0x901da61640910120300b86d2026800962501d218000541d014001c204081240c103075240c07000c18038031443e40c01500d41990900c000c02201c03000600350700c170804109542c070804a41000344146001481c1c03800e10b07010509225803400b030000205400e01d040d007410b04200f0710242d20745424440050800501110040900ca903e0304400104641802c08560311a0804006035580c44103100e5015910300f0110002841400444c500080364006000312410307650b50b174200001050b030400c049a204941c0060513011440702ca01442c803034a0b8020280c154542405040b10705258142c0c400f0390160f0003041405241a0b0100940382c209846002f40c14400110400aa046018540104404210100b0030403003d01d20601502d01460180300f0310b841c040303920018082500c10480740a0201c0da11982201c07065840703039015910041840c4103030350605540c0201c002d1618240b450022000c0c41c07142000041c000c0210809400c0b004d500002c500d0540c480b92000d89442d611010300d00000700050005007801540e0b = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 584370017 1250 584368767 584368781
    0x80909160e1807271212030b0306011505160c180203190506150c150115021c030b040908030702010c050a0915050c0d031b05070b01090216021207090537 67
    0x845015519032284040c56115484039000e8034050304006d181c20080d806840b41900e8444080c2c00b801c1c0ea44e00308003620112942480c8414104001084a00f86442c3c20903542c802040c800c45001292504d86206604001e03030829003034001502c100309201c852001c00c0f040442c140c1406401045079a138003000a910186105441301550741c0010350a40c01c41400b2452003007003815050030a45690321030a840c0f032040f040c158400c000d6848050b41181c2401240d900c40310110b00791401040000b02203000c24240c038041c070411600e03a6004010721018540a002e210582c078414a003c900b0001010402081064148580d406800100c1c0c2e0400c8481e104000325038490f5200400c83c2e102d0982000010001d116400722030718403407212140400640d100384201c400385ea070032031043c005a90800606500a501c030280311291a00302040490060720751010b100c605002000c00381102c60b16003107051054410040003100c048009004409812462021281a221026544481c5940b503088a10001d00724 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 584371267 1250 584370017 584370077
    0xe011d0a08151f05010e0d06180309091404020a0308070201050f07051615050d240b031009060e0c03090a021c031106160c080909160e1807 61
    0x1e80c00101510300c0300002c40e07806040711084005910781d0482809200c04801d015450004080860702030440c9050101002d01d00e00403200003682980d4100c5607141c0300c4038000c08402090841100700080c4d0300900c070340e006070400c00da500700d0b0510b0310b50300240024900313010091001c0008074084055911a170203451140c1c100c1d030003176550b41c200b90920a9540b0034058901000891030300e404110035001042500640f00780707403641c6040042c0744500e44060010400110440c00102081c5d1000010011590008155540d1002daa0f81000100380200c4c0c45160404480c0505142c0300b000108200303070a55610604600311580c59440b48070142c4d08010203107101070b502c81c028098183c050490b18001d1072030588a501ea88819941e42d040300f545601046607134443e0b0443e1254a0414903000b00c003d46821845000c0440c03508446500107031680b20300f07035451025180c3e05100c21015680080c81c8501d4814201c41c0c05103801002c80c00c010b107542d4000e0034802088910300005104d188800160010108 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 584372517 1250 584371267 584371273
    0x31d01050307110a2405151c03022812020a050c0f0f0405010e10060c0803180a06090b100b0c101a091501080612061302010c1a0103120e011d0a08 64
    0x490201c00300a02210172445500c2c1d540390074082845081c4182c464000b800e4094098100c4400b29100c0c4520400b640c0801e50550003205035101c0616004548645011200c8031060443c0e500f5061048603c404810100c095601c00002500850704c0011240304000c1e04035640c44240c0070030000b2030180385462105031f03005401c203000426000d440045103407047c030450340750000d406d43d510400c4030701000040000e0440c07a410004110822103c001e14502e00c400001140c0b44000c681d0380d01310844a44400c1510311080302d4090002e40e0318030392445401000e2040c01e0300e003408200c0301c0399a111503540d00c0c0c2a0842c1e6803960011104040d10032030f00e15400004041c0560307413906030741c1400080800c0c552140040d038088001101ca241c00144d07075551810700002000030f50345942c0000720305d41c9001820b078103020109110741d0004801d210340031442d0f1100d09860039254958501100d80c82c030404410001d00c400c1c4040c0703d5403640d101c80c10b9a034502c078880300c0da00d0350000d100216920500c0c2d9088009280 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 584373767 1250 584372517 584372543
    0xf171e070306210b010905070201060e0408180a0503030a0e190b0702152805161a07020d0f0503061503040821010b030610030e0613031d01050307110a 66
    0x9405601c10390840d101480f856201d50308072034900040c021103a0005000401480c014489541250301503a846903540c000014095145d510242081c80110350842d41003000003018400241c0e150901c0151010507600305000c7c42c14a00002d8030703070091804140c200103d00d80c0120701640c84582c40d40340d0407120305000f0803482e159004500143d00c03002e002d0f80201a0b486074004205203a00c12501c0542d600240f0702c15880d0504102e04422010005c00300c1004810b109024800403200300891180b2320500f4282644ca100344400c040c0d56400a1840f000e541041400c20a002d420641c8613107121240d01d00b05aa964800e0002895040020603005559a001c0300f0001004100c800405545038081c904a44091400007069282e450034007074814907400500104000341880c4044040020440c140400c1c1580000c20641c50000f0888244900b203ca01c5011003c1c0358008001a0042c030b40061840d0380392485000103001ca20025104001700f01c90718190f5004c1e001c05209a140c62644504554640 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 584375017 1250 584373767 584373781
    0x30c090d08030a0e060c0c070312121506020c01020105070e1212040b031807050f1011100b040b09060d030810080316060b1801050f0f0901090c030c0f171e 68
    0x82c064144c015000f03218100c00f2450f1420124280c0340b981c3d100800a001031815035462000140d000d948607c2030085250202405109501401110b05a00034006903128503040009251030346016043d41075900d00001d01150035802120300641043c00c0c1c8003c0090703100344010b18134064441d03080e07401e1300030040381c00703d80403000c000254024000021880704004040307081e191071329800d204055205003860b80007070352418a10380c0d0550440c23036818103d40030308030819130f1800c1c1481352004616066541c1e201c0003151519100e0600d54007019181071400340b40ca800490b0407020088c2016041c40f580c9800500c10031100c100002c040c0420000396a01d4007800c0805d49006107609a00b2107042c0d0500e980d64240f820510901130340061801252030480c0d291074148100c040295900581100b001202a4140d803542405a030003042d40709800100c40700c52030001411104c10118400802201101040300d1942c8024202c141300c0055140340c0c02c2d0740f0390440d5108d40421455002a440315003804101c60 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 584376267 1250 584375017 584375021
    0x305060c09103f0e07030203060106171b130e010f09020703120c02100c170901060302100f020c1c0b010b2d0408070f030c0902030c030c090d08030a 65
    0x1c58401560580c80c600042da0090b120307a050704510850081c203c00d81400d1070f03107114031000458100c48220000c02603644500d20142c5070340021030302c96640401c0c030800031410100078040c0148620b00c1c2c45004950100941201d051018060306030a01144000c11046000c0508440458142c1e40d0321080d21580c984104514440902c00c0510641742c6440014600250f07000302e88080360700d69106901c1c1507a50990300001c0190203122411481010b4411891020500c40c440241c0384031740b00d00b440c9082c1d41844660074400200445a542d0400c1070400040c0c8403c0c08440040c842800c001900b03280703601d0201c2c0b4020800481a42c00201030f14201048000603a0f40c00d2014000c84100083d80c1e00c0300c10001c443e200d100a440291030340480c02c41220741080301170100401c10075441915040c2e44940040c41d0003080c0e080442c40e450468020001c0011086609009210004043d42035107413900c840c0c0756900009003029001000001c81e42d103999102c1c0f40c05000710758000001c0b07480742012015000 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 584377517 1250 584376267 584376277
    0x9051005190b04140601031a040515090604060605040e1305010216050606040902030d12060f06021606030b010206060d05160303020d033605150a0b2701031b0305060c 73
    0x81910b00000c0341010704041c02070607036521207400344805540f42c1500440c02403a10b21010703040450744842000048d41c882c040e1500600d40e03030300c080c3d40300b50b075002c200181901c001d40780d43d1113645810400c0000030b410605032000c1703d0030090307010019a036050300a0342e0601c0c03001c07006006500c00142d20680f2001c448603a60550301850803210155540d000b403204581e0710047c040d501d07074401c0b0054080f46100702c295240c811140e1101080507903440c064003035203041076049100960800e50a1180103000c00649900401817490203100307800080700082d456540c081c041e80c4c0680c1c40c441520051220811140d045000e00b0b280c0018403590301d080003504c8a0120044000007800c0010307184078801721001050f2003904e000c0b035204409291900c0b0440103041c0300c004549500681c4500c143c500744807405144288048100400e509070003604020540c2801183d02e80440d000241110034111040400c0c0c4c19254020301c60400101c3d5501c0070010914590b01c01006441603004020f6941503c00c0940 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 584378767 1250 584377517 584377561
    0x130b040602100606110a0b2d010614031e0a06030213060e0c0a05040905040c080607020a0303062102010c26090a330905060a0f020f0613020409051005 66
    0x1040d140c1300c1208440800045210000590041d101c440214521078400d5811010000b04c904c185040881a040081c000959030b46200d2140c1c001041040e8000100d40c001e00b035103140079403071894a1800000491804000c0780101154640025500720f176640c484405190020a21310594a513005d000d00a040391707010301c1c130200c00c148000c101214251030a90f00350420980792241071030304100600e0001c6c01c0c01001a0b80841060500244069052007030328000d000c01e40c054900d0300c20f141005800e86050b58040c5a825461624650103050417107140000c042d42442d046503207415505040306003c1c5001c0707065414540c400c80c6007002034910002442c0380c9000f07990b02078071190796404001200030f0402509500a4120155074001d015082c0703011318400003400c25011460f1510045181e580100c0800742c0404e03c0d03500010001034040107089510300c1c80300001c110b10305c2c044440c400b41c80300d907513030090049884900c1ca004100c814010040304220184007040a4a40310500c0840c0e0b04000102e4 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 584380017 1250 584378767 584378771
    0x30307031104080a0b13080307110d1e2607260103050a3c031106070210020d060e070203190203042103030f09030806030d050301030209040305130b04060210 69
    0x11006402501c0076642124103010103001c440145844001080300014021000c04c05240810780009599401a40c094811075441d4980c1030f982206541c51310091081c3e0310207001400c3d50340185659482e0104010260034030341500c07040e0040010081810415410003000501e000400002c01d62220f13125001e140c6059041c110740a400e808998200781c00e02020f8100e400220341d103070100744d4200580c01003400210141c01851090404102940100c400ca0241c6c02d423440e4010b028558071a480901e44440f0b075025201031708104034040d42e25004001c0c5080d20135004103900b101388200742c1c00701005240b040f01e40c485070320701a90029200d9209501600e611250081c4041c01c07a4400029102a21244160000200b11042c041e84980700103c8044080644500c1d0300d82d001000c0e0b0040f00c405510039100c0c2c106500f000420142024445140d140c10000180010005a5582c00704207420942600345a0340e10400c80080d0040003802e60003c00840758001000101140d0010309000341082511003 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 584381267 1250 584380017 584380031
    0x60f010302030c0d0903020f01050405030a170601080a0e0312012d06092105030d0b0a0909150f0902120a060501050a050d02010305071808100c0c120c050a02040e03030703 75
    0x150100e001c00e43e4600340b803201c00d01030040110302c940e1041c07000e54000e0040f5032280208902e0309080d11411601114150808a0421b50254018240a10802c12041514064581100001d00c00a00101004d46480d128480c40940100a10441d040a0325688040e0955a1124440c0c9501800080981020071122003907040714054841030800b69a025614112443c0c42d04808629070000b1007001c0d0010980e0800e001d000a0707013003004008400d0701070030104540d0041000c00590048691007030f54454140710ba620b0002c1c00d220195001e0149072403000406400c108000750080504084c002e41005400f8480e007011003000070f42120051082070140411783e2074105000c2848917512034982c1084041813a800158041e41109070710035002e20700348405506841e903115072000c05a0105000c2c0d00805036003890f00106000d03100f082c4505040800c00e6412031340c0c5100300008110035080400c0300145684041010902c10803005c6a0020700900203035000c04002901d80c1c0c416125400441c4c17070028 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 584382517 1250 584381267 584381269
    0x1050f06030f041101030f020a1e030b03070b1b0a201e041a03060703021b030a210b04090b060907020624030307080414090a02070b011a1c05060f 64
    0x449200ba0600e0381002455200c9070307180c1d000c1d040140b0155052503241c441c078040000c2c15201408207c060f9507203c0d00301c2c01c100d001c401840c01b000600001094204950904552000039646044902140c003165581c01880c0c045460b04a080541550f40c1c0030342c600e0752050000c0c003614a2003000c211108500f50564031000c00481d240d22071034244500e100300c018950301c0c1c40c05600c101040c42003048104001d2104a000a08064086805402180d40403811180c0011841494280c2a9101000314079180860b40050200c5007a40001442c80c9609916060045001d40042d0032010000d041071140100501d401c24008108582c41e038081d8841c0030004500c28800240c40d400341c008003100709002090300d9100d51450444030b001c06e0f003612041000d1030005001d900100020248401742c81c140c2451203040286880c009040b040780140140801004503004554030f5044cc0d0801c2001420f040004a03a40030501840c13022594042f0160083c1211200e0340c3c004910402003140c803541c0c8045000 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 584383767 1250 584382517 584382529
    0x10603270f0b0a150303270e1302011101090303051b0304030e041a0904050f0c1e040c170a05040201030605010c0b04021c14070806011505031b0408030a020601050f 72
    0x3401410140d000c41ca10400714801e41e007415004491038002191120755022a801074403000e81c41100041d09402c1e1404800420301000c0d0310004841c04001c81446c42c002244260000c0940441c0090440440400c110f82c011100e450000015100a11100c0518103002c0c00400c0b0448114400d8440002000c1680c640503013220710030344c1d050300d81c20368042018091000421400b503031682800310004450790a41d0762812440d00c10b0b40316100030444c07401da290f410341c20103100501150041701c6100c101c40c5030364040501810110300c191000507620000c41011122140c03480344200b40ca05686040c07000b4a050b941003103208900030f0b00d050100317540d181c004440391085200302411200c0c407040800c0040c40d0962134600200444510542240f4051712242c44030107140c2400b201c00c0d409450200f01050042c08090b0040c8415000c40d81c101d40c0d81203014100d880024402c0210040d500070b11002500e00ca002d88016108280480e51100706494002c0d41c0e540007801103a1003104580c1c4000640d20b400 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 584385017 1250 584383767 584383841
    0x1d0901021e211e06030f1b03150c03010e33040b06040b0403061107080f0a0216030b04060213080102040605130f0b0f0c0c060d1a040501360203010603 66
    0x40301076442c2850340c40f0400d582104080c091070341c14022207250761100c520802440540c0d80d10407081d01c0c208403804042528058451014403901040c0384200b00c1001141e000341e9046503001101440f29a85a201050860b4144400e00211056407841c185004044813a11040c140781540d0400640c0102d80400110340124465405032400c10070003840045c83c02d801102481c1c0c0e54100003414804503548510403604180c90091804c4008112941c0d140c0e41000b01003500702002e000d00c0106815501c0d0006076940041c0081c0c00c1d140c001440c107050140506c0395000514241d0000c546031602d03500010b000750300c080d5590602240c5020f02050000340404164103c84801640703524006a0620340c0382580c02040280b1614000e030b12401000d504d841d001060545440240052035000d43c960510030403801c0c039111070260f4580300050150b06005c0058401038500c110303030304801c8080b40981d0809803454400c06201c80b8004400001c909400d03401c482440e220502c0c59019507510780240036050500 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 584386267 1250 584385017 584385031
    0x7050d140a0c0302032a1207080a0e0f1002030c0d180909020a0f090c09060e0310110403020a030c2117030709080d0f0f091d0901021e21 60
    0x820070805022500038480c149006210340140d034181400000040907803100010300034050003240e04040ca52007001c0c082c00b000001d6100101c0d0030103000d900e48042c6401213510a00a004404c3e89021141d517907024900c41024008209400710800132400039201d41108003018580d104e040f040512071809045000e40702c10304840540c0d540b81c5482c60034006070483c0b040507038100180d5139000c04ca14140c081950090103003104007040d18112030303000505134841c079803040c0e040048503202d43c40b0a540128140880351a06c0e0301c00f00c1c2e4007180e0458040c1511803940029401021020000f0400c0321030100f880c2101c0103080700980b110903040030f100c0c0301a1000301c000c09075080540c1100c9015002d10140d500841d90b1302c0d21100d41510741d9403440c0341c400c40388440c4001c40c10240c2503070540c079485040ae480340303c0c0720b06d0480300e51850000065540e029029843c0d018103a4030002034200720b03095050f203000c002d183c80c080036101c1d1070094071000c9a03c14080400d01d08a1010010854180c0304000d41c0101c0e0 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 584387517 1250 584386267 584386307
    0xb04020f0c1c0e0d0b1005121507050f03150f030f0f011b0207031b05060c030d060b0f1606020f21010b0301060e06070609050313090b09160c0602070b0c07050d 70
    0xc03142e03540c5d01d4842c0c0028405211640301c5440840c40e9100e00300d0046c0c542e0b4401c001081c40301402803045c070160710020645410890200829141c10038401c1c1542c0d0010059100a1034070141d000005002e00500c1e1040c07501440341e004000690040040c01c14450381e40c400c002c20100005010f141040840641e854025034044541003002508040000000c3c0c1c4142030348602c0607864400150044d80108917403039050b840480c0014078a40036101c1d10000704100e1419910301443d252041e90036004914080c2041c0b190b5a40407000d203d0950111520301c410000220380d82d40c000d00380700100c041842d00b600100c030558400803800c1d60341c28044078140c030780035240d400d821800601084a264441881100e02c5038607052003800180003000034101d0f40400d10303440202141070041d0b80782119003070760005120708443da0602030060040143d41000c40c8140c9861996140c5a0412001920503804001c0010902004105103044c0c0080500b4821b0b10490a0310004680340c402142c1401c003034002400b01e81 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 584388767 1250 584387517 584387539
    0x6010617070216032f281205070e090105090a2307060207060e01090302062d070606090513030905060904090813030212060c0d0b04020f0c1c0e 63
    0x4180d600050754084901d1049030300380a41c25040500c1c5a100380d00c02c40304480c562041c000a020b40e403140c02e4116103081e5959108449803070001c0c62152440400c5c1020403000c1090410b410f003c60001000303000d1a24420208034258a01103540d0456480346445642c0e4140c00b10f0b11703011040c09101e00400c01c0700014000a0916228501d01c0c0507035003442c0201b50800c0824455680f07091042c1c0d0000e000039000341c03800c0d510b802e10160618818403a40ba040048000c01800142d40b4801a20410a01004102403c034852240c3c01043c1d0f09030031100f10082008613078501081134030340284042c0c030040d42040c48207407112058802d2880720404014045400c4c04028840d80c00c1c101d000e001c0c1300200420115585041c0c2e1207042483c1e102c00100c00c07082801003002d0096051000c10441c40081e80c1000700802e20348005074041c10302840c1c0301c2d1071708192590841d03005179840d60191444d406515030540e58404410300c45550343c0d00039280324004070440c12551802c9601882032001c5912000d0701c7c1d40400 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 584390017 1250 584388767 584388797
    0x50a060b18060609130c0804061b080a0c0c1401020703030c1103031302062a2104090209031e01140105030610030204181a040b1032060310090b03060106 67
    0x60704002c0409070800052100f194014003a4050010040c6c52a181c1d9081410700341040b005540004c03505e07440d0505000c0942c03050650104041798032052801d0b0020300d420321081c0c1244c1c5500c002d50042d00410b00441040c95049040d402803030000e209890412510760124025a414019140003e070580c2080c00000d1800b0b0754400802000f51004180300d1521520480f0000044881203050001e81d038100d280c47d400c0c0c02d04000400046020f460300c0c075480d1101e480950320601c0346000f070300c0d10300303801140d48000c1e52070030030017154501810550b905203003103600c501b00e0081c1070b030103d2038121542c490000581030070007080f0b1038028a4036003c2c28841d942140c080c08064114100e11507558044000381c40e01180722103d9022000101e50030300d0107030381400d0800b8001014081c0c82d010b2103249126041240244c4000c5420100c480303034042c41d80c4080f0800000300128413201c0316981192001042000380c822004684055442e01c1204024200210303003895683c030000d0203400042100c0c2030000d803203 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 584391267 1250 584390017 584390029
    0x302030402030109020603150a0b090d021212190f030c021213030f240510053c04060803030402030c2209080307260a020c0316050a060b1806 62
    0x4018005400804c0c058030a0740481d086500031120141042e0402d60341109a1601c110180002c045029803a03080c180c602000517820080040000d2103000c402d18180d803404400d010000285030b540303100f20380340c0380f907251606114a0000c040000103400c098038806002d00a00c100505038500754014420090b001d0010000342c2d00c0482c19020040c2c11040c0000024001c4140d035030b000f440b0395904601710228844007040f2544268111200d54100002c00c41940707450040b42c411079100712643c4690740c560000a0010344a50728803201405901d6140c00da4108075401000340040050314200045030303840b8041c0742c5074081650000c0d0301d41c2060001d901207160444030380c1465681c08030500d04544020741305600711591000104d036803050100811044903000a01d024002e2004008005015404c824010441c100148102c010940c0400c0d02e5031306082c108155407000d2250b80801c0e011405505050f80d543e078011204840301030600d05610f00f075040010402d04d000289290300c04040d1220000c20070 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 584392517 1250 584391267 584391271
    0xa18050a140127020405060a12060507030f0c11060a061d040203030f0c0d1b0b1b040f0602070e09010b030a03050d0b091810020f12060a030807050303180606010f030203 74
    0xc0039074881c00c5410b1072407030b0b03040b040031a607501d16650000100f052040c4070a90b00020b24940c07148000a404101640ca5000310481c5958020800a0389543e2800290014120140c2410300c4500d8480c0606c03086800804081c0394110b11000c031a042e0391440d520344191a010b0168154030726000041507214140e1075017950300503200030152400d0400300940e80303680741c001c1480b656241d4811118014810341040307014017480202040c890071038415889259078290003501e00c42e62410340f000400c04902f0050300380c801800140110064042d40d82c84000d50311642c50140410081d10000420802501449103980c542c40c01380c050008481c0300d460a40f52900803921000b034454a6100280c125a51218682c4c40380c00149c43d420900b2140003c110700e0a1416400c0100742881005080c0700d0421580a81b000c11090341042030f0190340d2040402d0020503030764801014040e000c941d41007041408005140702d51880c4008050812540d5145070350340c001500e846000c0703051201124112803294004603 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 584393767 1250 584392517 584392553
    0x20d0804080f060a05090a12120b04061508370603061b12050c03060d0203010f020c150901182021010b0d0b0f040312090b0a18050a 58
    0x281803a5407524058203000c07859021500b41d420041c100f210a4215100c2c998101d4002d90042c80000400c2d81c40c40302203880f81c007102040c48400041d041c0900e640c0d0300302c690032120241081c0101603030340c0c01d042c00e185062209800402c040380001141c1400d01c1404400070501e12100b074070072101445010b003642e0100c0b4940000252242c03000310100c2c00034003901e140700307100401c500300040c80094002c04400c20801c03151003ca0900051103003204014042d2138208604440041d45412284006801800e040e8004404540041039940c0404404600c12202200c503814002c107a40c6c503600103908032030840071408041048100b104010901c400000c82c202e80c40d1040c00000800041c1c0026403c508071000c54a82403141104d01541100030b004104d14000103503540210030f4001e5492802e025030050003c001a0801d00010301450301c641d44400034507610001c2080129414203010b5000039040714182c80c3e00d4108031456804008961000b0501608480945200030496903001c1105d4901d903440 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 584395017 1250 584393767 584393783
    0x706230318150906160c0b060603060613030506010e06180a02090a09240602010623010201060f030305030402032122270b0f0307090c020312010b070302120c0a020d 72
    0x1400c1c0c100d44904a000e15501402006249861500060440c05042e81d40c8204400e0306c09000000303e40e2500590804d800b103a0040d200d47e100c40100d540c900861000301c01038035600e5800428404045405410380d052545401d5059039424144681c0300c0751900c03400e40a400340c0000401da00e071170380d003d06940300006105064160751102e603003003690852000d000a107640003a51840a80b801c0600e00010540c2c1d000034840c561500c030000e10f00e801090b00501040d414100002c0c2680e100703500c0344000d000c20040411203a522130030000c10350b40045400324060300c40d001002c0b8207100000c1031035025104440b42c592809164070000522580050b03590750306001880000f040c51121a0348540012604081c81c1c46c48081301c02c4940c0907500500038860040c1e2410003007088a8a000c1025020f4445200d4089103003200120308134071f58070841907032140d40c00744040040341000f000c400822889003c5c1c2e00701c421700c210784613012040303208003402d0100700e500c461011801814031000247c0743c2d500031082 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 584396267 1250 584395017 584395033
    0x60a0216110f09070509011d030c061c021201081522050a0606120203070e060604030803071e09030b07031a0f010908010c050c0f0f03040605160f03020706230318 71
    0x210751000400c4d240c2001095003c510500b4a51b405943d103414039004c0c2401110310313140500801e444a5400d04d207a80034160000b14000000340c008180801e03528600300442d69400140c3e0a02170f03a0707200380203035045030081101072401c0704000f941e403d0240ea00c4100c00d98503041030705014100f501c50910110f40c240a01400d02c00410518030880300105070000c0300e00300350b028500c109030800c41d00340c0042c000403c00b6014804186c48a606a50540e80d200c050940c1e00e0303e88560584030302d60120811400c500300c91a120062a030701200840450f4410301404146442d81d010542c255a6602c3c4211481d842d8030703c040406142403818462100010304011290039201c00450303095801c00843e940110300c0014001103c042c0c01c01c40306000351002e0f0082c166100b0b41c541c00030389030310551040000b0840003003201e009251240c041090301c86e91004800405014603d4065202c131903030310a5501061094a00100c240a5448070090944100b15024070399a1081035030b1403c903651018050701403050001d = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 584397517 1250 584396267 584396269
    0x117011401080303010f09020c120c070320120d0804020114040302090a06080607050304030c030c020f1002070f091e11070206030a0209040b010e0603131b03060509060a0216110f 78
    0x564040c0c510b180207180c0d6581010303c003008070441588032000c0c2c144100280e6280b0302001c248250b0210408036203d43e2010404100c3d0304d00442504090036000c50302c400c00c85a40a10307020910203081c00d035400c5081c02e07101f034405500c4601601c3c031800420a040300240c01584241044035120164406413810181c894010442101044507919142c1d5036501c0140306255040241641c09401780c50224514500f583e4010610144818000c1c1403104d010700920444d81c1c2c507030b44420344060140c00181244d10008009548001e1440b42c0320700c8c040c0d41a00802d03040320310301840514807911440f409825454030107034001440700700b110b01003800062100d200181e4400c801035014242e50800580c43c4e4503d08200800c40303080d44050fa045c0031180c0c94407007541d200e030b509032640103000d1481d02c0303082406414100020340d018039001c1c51a405141c008400c000340c60340500d018140e4402214505c2c2d0b98100048224400d05001184107100341110100085108002020398003014044c00c8203028468 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 584398767 1250 584397517 584397551
    0x906050f06092e120606140a17120f13050a061403091501170c010329030a471801060f06030b090a050f010513020c070e010314030a020303011701 64
    0x10700200c40400e281244d000034080c03e4003500c000f810341040c005500000117400203401020a101d8940410402c01040304012000e00050480c0c081c00b00da0507039610400c0044c842258002c11001100c684150004181420080c00d450140d4800d9110011101d800039a03440d5290001048002c0301e00c1601100c0c3c1c1030342c143c008030a000342005085084000a804842030811651a100504140c600407096034007108203c01424295100039444031001c0c51400070070706000d01c1240140050901e103d0031801c82d102c0c240e5074080d08443e40504030b102c06520480d00b201d06c2c41c10101503003440ca8080850f8811191b001402d000d40681400052850381c2e421004802d02c019921880100ea42c0e941041c41506000702415440700c0b44190400040c1b821030704410840f030041c06400d000718171661101d0540c0e00300707904413049083c184040b85c400f9541d44e4a420088407007400304440340d000c1d003150b42c07513a900001301b61488407860340c010b541140e0801c5082c0f014440d4002c1680d11964842c198102030b00745070 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 584400017 1250 584398767 584398769
    0x1d0a0b01390c03050d03290303190810090515090612060a0c0e010206160f1202040b030703060806070504060810051003050105040e0d120c0e1002010906050f06092e 72
    0x24418160307000f860b50508a00740a21280700da4245828812880c0c0028401021960002a410303608030b0300da4003201c0030900e14000d41c0c0561040b80c200d01030031500c01e5000085140f04189140d1740c40125038544584001740c51050314070043d400d4050082c0c0081c6e00d480704240e80d2000018002e5041a803504214502d490300a840d107000042ea070b13412188406a1011440c0c0581c88203000900341400c04410494180300541c01c030008100001e200c2c41c201c580710300c026a22560030000c0c1951030740e40780c04100c007059000343e0324100441d14003140001c42c41c20115031144079180c280c40341818107203481000c0d00e0100d001840104c1452145034041030569410001900c8280745a41c0080c441d8106028070007200c40c411049201c6074040d40010b03a0701350f405519210f400d001d40ca00071440c0081010706440744003810716802d501246450003943c40940c15403086e010b01340101c0c001d000300d859087c0030500c415004d8910542010703024000600200e05840042c3d4190071a00504010700c120344c0300400c2418807 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 584401267 1250 584400017 584400023
    0x62104030309060b09060603133905010e28170a032703060b03010f020a0512070801050f040e0c031e0c120309011101060308041d0a0b0139 61
    0x781d80c50b101d090181c42c0c41680c1d5400c030265000c0441d07080070710004074a03001c000c185150400700742d001d107801c0050030380010051415102ea00a40044a001100400114480342c0f49650758202cad0300290a6200340c070f400580440261468481884400d26075008107007045c02c645050b4075141001407107004418080d0202c2d034811000d0481001e4905d802007000303040303002021800e4001030301038200e030099030181002c490b40080000f84403200b00300824003508018042c00016840480d04852040c0c115005028500781e10b182049556920402994070903000c4c00f030150405003c0f00d16050a04250b8007400310000c05404440354000300b107002924101d00c2c1524118200da024004041c1e005003001403004098086400e18040405413828075620300416440904104581240c091401c1080d803104010796000700355a650383d5120406a0084107d41c0c11070f50300b04c0d4400d00094124816441035903c0000d0580d0307840308030300e99503200010080706c00c400d580402070890740600c40b10341d5220305803564600c = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 584402517 1250 584401267 584401271
    0x615060a0c120503090f0106030308071220120115050f030705070c0329040203030d1d03040b030114060c07180f1a040e030309150a06031a061e0f0621040303 69
    0xe402c44450703040403034011b4940120380c1440c4041c00042d8203c0c0c28141d03c6000c515058800290484000c0040c01e2003503200f952440c010400181b1040c42031008000c0425066090395040e6620b41d544a940c42d0044c900800103041403101186811614008541100b85482c242d0b06100064407030500d00c1c000381c0d10440e00d480d11032000d0f80d900c1c3c0a00418071030300503032254075041c607282c9600802c0d268407904903143c05803907580c0a07280f80013030800750082800049400301c1c0e80f102e443d04c10b410015030080c01091074440d0140980310481c0f80c84001c4174914a02140580480b51420150004407412000b03a50005a03c03001c1c403c034011040d201e614000407880150100e840c0c8003409000898500810300c43e2107800800410943c04c00010754080b50b4608821107404940e44d24080d5030043c0084d801c01400f135042c3c00781440491303900e4140c0c10700404088442c01801851441b0300590f07141c08040e00c9030031506184a20403617203841000743c030200021841003502080c0004264004900440701180425 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 584403767 1250 584402517 584402521
    0x1020c1b03030f0403060e0f0d0e032b0305060301020c01090c0f0e090a0f11060a0201090201020d0816050309120a080106090f030b010519032001020105090615060a0c120503 76
    0x303500803140006984096020b5440c00400900da001244a14040a081c0c59240c00d0303810001c0e2002c00c5003c100c0e009060a4070502402c038140100303910400403146d0b01c644554406683c5000891002c1103141a021181d8500c50101510940190000a2032a540b5540c24415030003609000e001b110840c030711581d0380b5002d03a400e0403000190b52001d03400002510384000308028a5401c006004500309810a0313030880701c0c2c451854506018240b01403101e802c6800400c1404901d42c054008142c418401d03025240030303210601c030071181c3c50012215040200301d40744158044034007540041d41c100f01c0384800d42c2d0858501c40390742d258950007a00e803100042d1403100108035442e40086504c015051820002e443c3e2495901c0f51a404a03040c02000e22514610303038055104041210316000440c1d00c81030b10b0725402c0d40380300083d49040a19400c603003d54203020005006c040041411072103040c000c1e029486c401382c480e0600c032141e041807000505000d51254400003161031021010210030041c0e440640e24 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 584405017 1250 584403767 584403793
    0x130516080114090303220c0b0d0c02010e15011a09061813020406020c09070e030f071401020f060c0c1608071d04050a030e04020706180b070207030b0103030810050301020c 75
    0x1d02c401080d400040c2c10070300501c0005541848501199445003401071108107481c2451410894980d0010b03c0c0614001181e080120b0282c1020b0312580031350f00200f061401145070b090303e60301280c8050510b0840000180f15920802e000f410a8402d88201d060a082d0100d0216559510000c50721103010f10350504502d6500d05950703d000d018071100015418649064400b9541e490604c4521344102c8209000800140c810034141c0c00004004040f522021f201b4001a603d6420345d02641c1d821207144050141c1c594000541c01c005079248000510a40d601c0d262101c0b10798001000c60300702c038002d11014010103060141154098001c21020705030541c41c003c0f01166060083c0c0c4181c80c2c1404000803c0302098010404440d03103a010f0510910a60540d00050024480d0b0a80140304600d05a91540c1071801d0794200d201d413030b116031a12002526020b4060303a0307400c002c0c0f02c024101ca032414014800a0301c121100d9400c03000344c060515140b52a2400203099800004202071590f00c810791040c20f13 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 584406267 1250 584405017 584405051
    0x109060603140703050d052b0515180402061e03040b15180708061306080a1a010b0412020303041d06040f0e1b0609030618061605031305160801 63
    0x85042c96030010070840345140d0351a500d82e00f03d05003032010f00a000c6015a10702d0a0320421000d460090081902c82d40802a6aa00180000d032180402012440c0f4002070340d08094847c4210207002031480400d5a1b00d6908001d82c990048848140c43c00c44400480f04240e5114051030065100e03c070f084c4128600f10031201c4d690702c0141000e6105403200030610700340c08000c0d102560014030900c0c10719051380c1c0710004510400c2c043c0c51150740042c601240052007850114454500b980704001e04c0c11712a841608a0700030303c0081c042c58544440802040110300c005004071080b952014040c1d9080682d01d4400c801d00000c6210f0808154101504102c01351800f8481c05042c808006000c0040340c0200110540d5514912000180408034108190306c3da40c8810566020150050450302d180c40e03e20f10f10115072420601418081c1710320400b1030b00f80010680300c0b0034a90481d40c0d420303040d030b91032820400008142038001e80b0140038402c89250012003211040000d040c0900010031800706c510ba41c542 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 584407517 1250 584406267 584406293
    0x120506070f17010905060a3c060807080a0608060f15040e0c010f0c080d0c0f0516060207022e0923040c02100e15060f0a05040c090302030109060603 65
    0x100504102c0c00700405025200c401c0c1514441400054950703030b0070000c82c020040a800401091480b0a200000003d4001075007200740304030a1922408080c2d031008180669141c014180422010000110114454840580c1c454821b4101003602e66594403098100801031f40c80f124400740c030208004005411901000c40380d001035604020151400341c000343c8840c807020400b810084014601a204e92040501e0404d00790040e8480e90345800f24100017008220f4903680801040c85101229810360040b03040d5060045092040031901c0b00b10780d0f035200290b200c108200e0f40030606291020a02d40d0040d4007a00800344001840011903000d100940080c000d54800c4901c1c04002c040e6100c032443c40e80b42200390305010b44001c00c1034000f201c1c00b64285003110002401252030b0240001e0720b60400502209052861718070b21091381c50300030030f005540d40c440402c1c58000385000350401407401c3c41e503c04081e4000750310348031960340d4403640081c0c25200c0000341610031a86480d4184180490700420300 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 584408767 1250 584407517 584407547
    0x60e01060804020a03021e18040c0510020613030c0b07030b040e01061a030408120705030105100906020a170d02040b0301090c11120717040603140a0c0207050f0a12050607 75
    0x407506180550000303150080781d000c001e0007084500d810304d45c0210f1403681a016400002c0c03408000b16a80d40da0001c070103004031400c0c1d550b4030308110009001e0910312510102c0c1c44496001d04003603550100740b01c0001c80c80c620100d08001d03001c010100855203598800e80a80001e507030114044405d0402c21080d541c1e000038181c0360b40d14205081107884910030400c0c1e0319100c1a01010340380e80e986c0c109840c8034020300002d4011a81c8200030001d031564042c00550603900100d504090240c00c070308040703480d810305005072000340e448003e1500c04910710a02004101d010002c01f0380c600345a035a40328050380c20907400170020305408030050050400c2c03805021028203581c54400d400500800f00c80b07070364003907a43c05881182d00000b440020702145400b601c4800c0044000c16545d2590384030020300400c2c0955451002c1c28148012480303504040c000c00020302e03041d90090403820700f4201040303d4000c1e00030b600b940c000354001000a001e0b107028501c0303c40c240103801400083c130b0414400b41108006406013 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 584410017 1250 584408767 584408777
    0x9030606060a12090c080a050a0b0906040c0b1c1b021002090906270f070e040605010e270430050301170a170c0c1801090203190e01060e0106 62
    0x8041c502e40c0f100100c40880c001e41004116003a250a096100100c0c5400014460003169005018040e0006000f03215512034642946030744d4400c51507640b2030f41c007500c001f00080300c10001006a000100054950309100b18403400740e200c0d50040900c1161a032901030385085c140010300d420019014000410117901d400c03410362801d01188001303100108020300b013a00c5000d40d482417105544100d60f59012000c100d14650066062465682c180320782d00b2141e00c000071f000c902c10503015003401d000310801c50782e041e140c2122103c0d00c00c0420043c1c40310078040030f0305020748001001e400c108840790a0301841c06240f01d0301200f040c0200d070305c1c3c240f1340c8040301c0464060070180b030040c0315074044100ea044074041410743c2101d11400e04054186401a40090820001d0300c590301f00415a1200a100c200060011100a103450700c0511094107404000f0b0100007814100400c0441c0403a0002d56001c0d6450500300040032110b81100c0407120401580c0c07103240e560710360030301142140c00003060142010b4144 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 584411267 1250 584410017 584410027
    0x1e06081c14040e09030c121323120a0204090c080706080c04030f020a0324052202040c02070b0d2c0a0f1b0b070203060606090108041e0f080903060606 66
    0x1810003482140f2450000c00e408400142400000340160307180041c2c028152510326590760030501c2241c000a90006142100020015602243d2003018058001c0c80c00a000e50002e88420022000c81440c10a1000e01901501c20016911751050001180c4129144030103542060011450100182c21076400c1c4a104800c0c003a1b000449410b450480364480044001c2100c2171020801c0444558030045c80071500e8101e000b032400000045040c01c024400081042d5614128401e400301b6250815124440c0b4ac907111300e0141c209508403200500e42e0380101c8001c2607071152403110b6903000241e0030050a40d180000300040400c1490450490054159403941140c24810140c845242c40350081c1b604120030500c004006825030343c3c8186003901c10b0f08200d1240d450060086d5503200c900101d00c640034640c0055040d01c4d04e042502c00311001070b516100c503070340c807035464002c00a44804406154051109044006100d040e4100d4613a0700c030305540d580b541d05e11000e05281c81b102501041c441d05003405 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 584412517 1250 584411267 584411297
    0x31c05070e0a0e0a02040b1c0c022e0608060117010605030a021302031509010603020c010f0c0e13110a05040e0603060105131107050109210804080a031e06081c 70
    0x20840155000c0c01140c0c0d43c41d4540d4044035000b845075501030b184403440400c1d00500790702e96051798800310000b180c0901030b2140c05c1350f0898030380c102d80b100428004031009164041e0040d0b041c00f446880e0442d6000501a922071280078a011800da0040d2000700c60481031601008081c0a120b0091400340c0042508240b00e0b070024215419041500350b466901000040c0e400312120441c640c03000c40509403e80b95615441c0080195000d4000b500381903084c03101c0c040c039030076030f911500509a44035580d0315041541482002121698008103034021600c0707443c0400900b5070b0400500511035140c841660300e5141000020b402c20001b06031a1082e0000c0e001000b45895401040e18102c0c0c3c0190000b0312000d84400300c4c0030074040c40d58003803c91340c41c10703c2c48010000b1150440200c0c105401030b45220f1400000200c6000b10b080f10000d0014206000440314940a604001d507140f0907000c281914440d001070762400c44442ea03100210365030201c200c0c0303d44007000381c030003045925003458041c1c0c0d6065404 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 584413767 1250 584412517 584412529
    0x604030e0609011806090f14090714070c0b0304020405090a050c09100807080a0302010e061905060a18050412020c03031b0a05030a0e0109050a06081303030b03031c05070e 75
    0x200c40103028100001c1c000d0314583c4074000041030035138411102c4100340c0d00c031000140b40310141d000700d01e1540400e05000c542d05485802680c40705000a054040e582d40c0c4c0e190843d0b5080460007160003290007880040d00041d01480a00c000c4d220b8401318030f4603490b0500420040d41c9014141d10110742200002030003055010070048001c3e84250b810440325100c0720800701c4040c3c7c0c1035001c402d59004001000c0341d086070124814070014040d0303000f4000001080c8089403161010b4031850700000d01400d0f003000c40d021603000b1640c030140003403d40c50050381d40c801c21030741880650b404045032541c800130042007004c40c025518551010384001d054410401c40429a284207210141d410300c0c55585d54014261401c00c07188030210790110907030761038040030400030b8041c05140b241640400c1503e60041442e0524074240700403150a44e5900ca50b50716a003844d01c6501114080a404041e00c42500a086440806c02001169400307002203401c0d8202182c0072080f140c02404c541c0c100444140c000c40d96540b10 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 584415017 1250 584413767 584413787
    0x270f06040510180504020a02060a1a03070303032313060507020106050a050922120f051303083402040506040921170a0b030c0415121b0306020417060403 67
    0x203003814000c103c07900c440c00715140056404503030710034000035000d42c600b503010400c80e0103250650401d004162000500702465450200e1403038050b44860010400b10340310750003400781070302c100c0000302da103c503011690004000304880b8800701d00e40c02c105810030000c8038840c4980c090003601c001c0000034142800140803002d00e1103410f00c901510000310740c3e024401a8602c0c2c07800c60410707281c1d5a0041c145032440841040c00c03510004a41060480f2201074000d1088540c2036083d41d42c4035003441c0c10755644401680040f00c0c04172103c949a06418061600311001d800040c1503411481ea00000c9441000f0a45100500302d6015130706103051040080d40f1150030340b060201d6007100a15406681e0012075014005020801c40715200c2c3e014407803240e00da03070300c01d12010b031040d001da4181c40311203000e00095072049126943c000d1070002d010800002c400603031800301d80c42140800b240b51000301103050080503e800668040c0d9000804100034007410100000c1e40e1040d2018001740d15203030724054011b40c01 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 584416267 1250 584415017 584415049
    0x303010911040914011d090303061c12020f0f070f170a0c0b1908092d100501060e0a0b040e0a060806100801051012080906270f060405 59
    0x10350200110041081c0300355806440e01e500c0c108000d00074041e110540c40c5080c46450b401c042c0211945810000c1c01554912031300d6004010340c42d41c1c8510003403000c00c00d0900741e06e107100c2d2519607040300002c1070b0002c0015444c440f50700610300d241b01c8040300ea0074010220030440103940408403c00c0980003060400003226a0200c0c0203035115018507501e414031000b008010200c03952000003251a04194010f000f01913462106100c80c4048030206031044001035030100f04680c0a01411007940f045083c8510707516001c0e48420301072640034011680b0b8894440311500780300d41c03118010301050340d110340c07807201c401ca0441d03189040c24508403080c4921b22950144d00300205022000600f0500030b134100302c009040f140115800e82c50440c425100c1e8000382d000d244c06035424900801d0300c1400c20303041c000640c2d6240400900d4940c0c55902d550795a0300c6002c1458110000b800742080720612001e42c0300d403e111124150412068600820489004241c81284100410b02c800d20075500c40010003880c01031 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 584417517 1250 584416267 584416271
    0xf03020f0d050316060207030906052505100e0102030411090403050304060203150d050312010501110304050f0d050105071d040903050405010c11090c0d0e030f0f250c2603030109 78
    0x9a820160f003503101d05000c04003a400c0203c805001c004181d40100341d001d02a55681401e9615684215858856116611072201a001c1032200c241001c4840c544418820811100301200c002440c10a69100c4440202d05035408030800c03017841403500100d21460320803501303111585460381c2d018181c0e000c00340000c0c002607408000507450030000c800540c4194401814800114440d19181c1c3d80d0740d028280e0400759840020000500e035009060716500707200c0301c0000e181018101000d01c0107001d20340020542c02072189403041c0c08598284103150144600d951180850900b08000300e44ac21040c80c0000e004618011010340407a51003030647d03003668804d281200e0044d0386401c19041c8260038003402581b0100c07407000d00169079000c900030010040c00403000d2041c06540304619880c2d01075140c3c403110300c503000c000301c1210241c000010b041031402c0b11440b60381c40c00c40400280c244119500101da00c025840c5040c0304014145480c2c4407004031610034204a992441d01c600d4481c00103100d90440b040e = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 584418767 1250 584417517 584417539
    0x10c080d06030f0b1509071e0c02061902190209010e1e0a152106090201050c030a0507060e06070f0f050f0c062d04020d020609040203040b09070f03020f 67
    0x244940000d0000d542000e00c3c103860100303d0a01c13070340800042c3c40c000d6a40e0040720381c2444d503040c941c039807a10030b103107503244d9a61002c00c2e05000030400031720400c0c00d03041150481145005903100340192030707040701511003403480c1c0044803006850520083e0281300203c00703410040c0010b9032100c07203071410354202640104603501c0d0341d940d41d50550f01d000c112076400d81080e4100f10107150b40e43d0000d8002100c1d0010700e02100d903602c00e00844400e214480d0007210340c0c10024540850b125801c107400c071500c103240c06854600c04424960444d00480c081e2400a10001841024001180500d00c4609070140140031141007295001c0c1041200455040030300840313801c0040094010010b607a484034058400799510b003500c41d100307600d07640200d0b03c8050002903203031440d801e500f410501004400c110f09440381c5a4035242c0801c40c0c01e411614007246e100c801000f034000c00362114005540200d101e507a0110490516545941c10a803564102000f0b42007070310700400c003680e507500400c41400b0f02030702c8102d054 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 584420017 1250 584418767 584418787
    0x91504060f022a0c0111031e070f0507050a0608090d0f03021605010b090a09170313120c1a2a0903012d020316030e010f05130605060a05010c08 63
    0x19000300748100d50303481e182080f0b078128824101c10404079208640705845001d600f0200540380c5400302c000c01001507205201801c801c2540401c0085142c40c201c102c503041c03110590f2096004995200c00b01e802d0713004075004000304d0421040b500c01802c15400d02c03404501d011150745513183d084680c250108421100308c081042c2c000d038106d801903019034001280c90740c0a0308006002c0c00032482c0341030040301380701e0005025165500c01c140c40f0712b0b409140c4842c2030201120003a5640c1002d07010b0311426851140907800079045840341111901b9a032a00031201d402c0f420404035810003a0400c24a4440850800c05c080a04011084001e40725005082c5002c18400c4a0041401b1350341c14a5055031a1980d9498840e04099034000d11298144500709512503900540c3e05900080d6030514010507101c100c0c48686001c0d42103120f0181409000041c96506020b40e40156002a580c039201a801e4038400014405240100755203d0710940b00c4411240c80c0100007000c007004180042c1c50b200c404906002e01c = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 584421267 1250 584420017 584420021
    0x901050a0e0d060f0e0c0603040c05150c0304060f11150613140103060b09090a0201170703020705070e06010e0103110403030516150b0f030c09010509090313080c09091504060f 77
    0x607a43c028000704600030042c510000102461850070f03500713108078648000c0c14901042141c0c440c90740400780c409103902c1d1401348601c150800368a00c0110006000680b02d0120410140005000507901c08112281070790015000342e1440d101e041d41508441441c00313100c002d407005160001e001340c500d034008044010100780144a44c03483c40c2420300540000000744000d80c0c0100710601030440310145640c41e1312010940d242c004040c001d0100b045a4018600580c4c4450b02c60f901c03420b0381c1405460f003101c994a85041c6011600141c051910590a2055550b0711500c85188a002800c08003c001c0c2e101201902c00d01803840014200070b800207024a50320241604040000d620440341111030b40d00c0811034018103140c0c40a58010006040a00545d10740080d000004800181007040c0a9080c00700780050080020410710041c4020480303044009080740e002c0000f41603400281c580c01031058100304114001900550719948841031928030199031b081c0c074a80044d403121001403030f25041d490040c0 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 584422517 1250 584421267 584421289
    0x1707080f09190c050f09460c0807052502010504180c080a02070201050703030c1b080409060902030c03070c02010e041d011413060e0708030c0f10020901050a0e 70
    0x540900b03014080d000c11200504210680700c0031200300f01029103100a1040c890030449120b000300d40b1138a4820a8411001d000007000e07643c50300f504142c2d400c0000407070b490384070204112008542c0c491401c07460a44c0840210341111451030503614040301545515009001c02e40c419001e001d04500607801c6a004200300d800425105902103d107640b500c260800a000c1c2c036401310003240b00c4100050607000980300321002154140c440b141000c02644084008003204801507061081600110b031000ca000d221010780a8802c0c0a042e603554100000d4400703503400b80d03104041d203600600034041070494100540c3c1c0c1c041d0701440c00782000485800106c070a43c0b07075203d1158002e460215000550000d0010007074103c0c45040080c400100f04103491110b50008580240142142c082141e00286641d0000da40e0b40895504a5164503242d007085400c2d0341c801000c9403c99840401503040c505420b0004003d80760340480114242101c0a0000c0c140380b05008100d820403c995162a405a4507200c01030 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 584423767 1250 584422517 584422543
    0xf0111250f0b010905010f03200112021803190b040b091f02042606070c0606170d1e02120304150905010f0f090c0b030402060c0609030304031707080f09 67
    0x8440070070326060088240d10207015404c1c0c140d003003d0010901b22000c403841001c49034822010703c80c01042108107a58070619203650350401c440c00c0e40d040d204140718005009140e1200c500001d1583c40001050714010295503044001c00749201184041500ca0008942c41a080010a011a40c071002d9681c00c040014100030800c01c0000c051264403107082d800f40c01036458070840b0070094003101c9941010204800407207001540138000080049104070950f4801c18824140412616101c4001191008003181c020b00c90b07134002401b0443d0305901010880302d00300301c1d08622600e00e0078004000d446010140e00e031012903200101080030040c0d19042114130484440341040b50054614001d800f074002d1011001c131450510019980c51502441450a810341c400003404a8a24000000340203400c0184142e07403140b420b000c401c6203c1d400780000b0b8820a100b0014503640e00d0240f801074512141d020f0510580c04050082140581d000039140b40c0000302c140d08000326603101d244640c40c09590404007 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 584425017 1250 584423767 584423783
    0xf03110a03020a0b0105030a0b060103020906040306020301140103060b0307123603031a0d1e050d0c05010f050f07080612030a030203100e041a06240c0f011125 70
    0xc0003410b50104442c41010f200384460741c9140d0381c80040690312508510080c204054002c0419195070190f03004291481c005464a810a9940c1d11484102d0b0803d0337101344800030801e1b900728502d40e41407040308043c11094044a09500b04010006c10044a00801c8900d0958480c8802502013025401004c0c0e40c120403940041200100f1034050021403022089000c00c1c1040e410215550340d0180c0c0c2e00600c14040c20541a220003500c6070b00c402c0c0c0840708889206001c1c2540c010100b07100b400320b22a205d0b41d6032112075100000303140540c00c41d6805940c3c8098146040b01748010020350b0952140c200083d4504803515480f800d000400005c613210b401ca4041c440015045940c40d00358019601c100c1c4825801c091030751341d9411082c0d50300b1088400500050048220741e000284d140f0081da0452006440e403009210040f030b140010ba00c003c00945980b41010074601581401000200c8108030004024491440e40c2c0c0b6503c903280c000c40c050b000c1c2641c02c009850103681403541012010355084221 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 584426267 1250 584425017 584425033
    0x6061903170712050c0d02030c0d0810080102040803030106020f030702100e0f09090c01120903051c0209220e010605061e090607060509070621020d1b0e03010b010e0a030f0311 77
    0x201610316402113445c01000e005030f200408925001005807410014060003620141c0c91046007201d0f1000010030505e059011ba800105254070244060805844800010340e569414184080d10701584403240301c005500401c4507500503103504444900586250400c24130303140301d03c4005602c1c0e420242c03480b034015503d10108100518006076824000c80281c90307520002c4110380c0c0130f00c16108010409400314030200600d05001116104400d09030f1a81c00c0010b040034211000905080c1032941480c01c900d210f420700c1d04100b002e030f1140007038062003074008111107483c000215101e401100080000e421111001940c0c0c2c225020480d9524080180150341d2103207503192640007840c056500c4030322445002c0e40400c40500982004402000d600f1001c1d480101c00c440e48406035200140821207140c4076442c148503448401009000c0380c01940718085404450400d05086900301c00f8114104605040341c1d01043e200c006412083e0394128160b85407010300c1e070034142c40851980d070341c2c0700340303841a005 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 584427517 1250 584426267 584426303
    0xf0c0c030105151c0507030215040e01060206041241030a06030c05271305030a120507090f0b0a0201151401030516020c10020f120c060619031707 64
    0xa402c0c4241c10841d542440040c0660410b503801c0313910315000f0810b42c0141c8003440545801450246078002d4010741902c1c00d5102e03040c0d4600c651007a8080710150b40f011301480b040100c09408044082b500745800b50010481d4001400d5010800d1070a418080501c0e0500c0340c0781441d004440c8078601010049039690800b104e42c100140154441580da08007141d4011510340703454600c0036000d4840c0210084101d078040702100d4240800340c00d60030350990051103800019000e00146c8100340131134556505880b040743c913220039601c1c0100180c08218200b00103100d4800f00040c048260b40c0c113100c1464464001c00e000f40d0040000000f03c100003500c6000005100040001c42e01403250203036424061500d4000c1040074841c43c60f810600541c10440c2c3c0440d0310705000f26540204031051048840108191b001c00e41840502da51a803031000700042c10b691a078004000494210606898134441c503060980c001c13403d08402e000083c104202020a0070068103244182e8118580180703d40c1140d00e1108 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 584428767 1250 584427517 584427541
    0x2040f060507020301110c030a030b0d0b130b07180303050c0102221e0b07150b04020c0f162601020f1201061206150c0501020f0d0617010608030f0c0c030105 69
    0x5500f01d11039803e160580c49001113290a59000300300060065003000707040e034016800303440d4601c402e0350055800d21201000c100038925107402682039648541d244512418814100300b401001c070403d101e024170800980381c8010041030200d82e0946400c42d2140400004107002e07100380724580d1003068034024500a0032602c110081c0c1114981ca00344004051040c9a0b0403000c84944620341d52181c042c050100440e003403131150f402c2c100c1c0360203000408100740c2d00003900303e80088003102c9650b80414078907200302c10b04010054a806603c03601c588003920b0235030071840c03058a544a1200c2c0e400400414249008250143c8425018200c1c10546403034440110b90b468070303401d05c030b08800600b101c80308590314042803007036006459074000301c0524007a10150664003004411004c846941d420014403665118034000f400070f081001e10080386861600c8003400010001c4518122070303074500082000600d500000b11380c4030900302c51250b501c509007000060b04200c1c11903880c1d0b816500704070030050312200407 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 584430017 1250 584428767 584428777
    0x1609030f0335190e0106030b1e0c09240a02060f0a18061e02040801050601140a050d091110030c09060f17040f080703351302030102040f0605 62
    0x34100100900d10404109114074203420500a94a4074000418518003070941400c3c020706100b8404903040102000e550300b16816907005940d9404501d0510000310141c0c1b84086000348510507103034082c10680503076816482074642c0180302c1c60340c00311000c007002c075404200c124611040072056103d18141c1c3d00a034846c00c0482e540c81074036044800003554a0040e00c24103500f504600b0340d0820328050340e6642c10042078120b071a8001120100c0000d00140701a00051014040e068000310b000d0a040e030000d00710541c0c0c01000780c982c0b001440f43d010001d5124055039070403a40700c50089042d01c001e0408008202c508040c00340c0003042c0b003000b400c4d0030307405401c49a8a10503607134075540c000e65210030490f0607025243d4408009449206030642c2d80d51286030711604640200503083c3c55440d10381d20311241b540003040480225002400410301c000c80b100d030901e079026542c0d130b4420490400c603110040104004094182c079005004a410035510b003541a1805407514648040c480c503103c5c00068525002 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 584431267 1250 584430017 584430047
    0x60a0503070314040803071808100605040b011b0807020a15270602100203091c0816080114130e0706031a1215180607080a0e0a05061609030f03 63
    0x3000d01d861443c01805107103611540e0090107050a60b222418104c0396580c0b480350035a0340c580301c01c0b00030030940c0082c003501c4050500303c0740c005002440d04041c802a01c0200d04000e050040180404416120300071804030f81d1075200341c59550301c550510018512601c11340003021082b01d620b264890090b0001d008006171510a660686454101281c141958400340250001a00304908040c185510b43c1c02960308012160709403080078928811241c4104005000400010109014018125180c5031846020f00b920f26100501d503041c8178a03598003840780c404035801400d040c00720815213009540030203181d0302c940003039548480e9250700083c06081400c10203550f00001051812a510304600b054180d400c0d00406420a0031a024a0304031090001340b40b20500342c0400c50100346c210051148500c20126038480180d1400c10480c168102e6002140128107640407001c000302041c000501c2076030010b900c111168100d544d040c0101c55a50641e40004e0640041600800130150401480806600 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 584432517 1250 584431267 584431271
    0x3070903020f0a0311060a02012715050c040b0703020109150621021f0504030b04030302040f050d0309150302130b12060607030f14120f18071d060f060a05030703 71
    0x1042c8402c203c0c420b210341c40b00400c082d41580007030201c0d040c010054030b405c0d00ca900000405280b006200f5425224050310f00d8039010b1866006070801980100e0f00c040d5904000b400c00840c1341c0301c00d10921074407603800740a500c04004122001014800d41018229550061404451010003000f01002d4521030103494640400c40c58030301c05628030369041c0e00c04603030020b10040c032280e21003124400890404004a0070007608110110200302001c000c240541d02c81e0b500180d40c1d5141a10000018000350401485081041000d2012a500240c028203070303000600012802404844107500a101d8615086c10300c00840900040801d400c6000d401400702e03540b071080305a0b46a40800c60341e80b00380341c0010045510410070180451154010340c0040c0004800c4a16000a03101200050001110004000b003021020450402200d04844d602c02002d0001801c1e40e90901c0c00b18034201001503400c94140f01200d0014070f0380c1e0794040e84085450030203003920355140354285000b0415801100e000010178 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 584433767 1250 584432517 584432539
    0x71b0b0c0c01120207022b0f0b04051908070b0601230d0f0b150f130806150603190510030b041a010803090f0d02030c030d0f0801090b0f0d080c01020307090302 70
    0x10f002030085920960340180002c051680d400c40b5410400419601c0320800c0548804032000a542c001103002e449028000b005c01e03610741490051300d031407207101401c6680400e42402100050010042e034550603803001e407200041d643c03440100c03000d01200355103d030f16414200010302c0b1072046000500c44c002c0c104806203d40c00350320b02c40c20103680845e981290007001c0c5070350102c1031060120141c1020710102080f0361428100c40005929801190011012500010f0902070305c052900e001614906080e901381e4103500e01841782d0381030714a5140b9414082501c8200160b51400341001c2c000103582e010320300501e00e00302414011030604107040000b03010b001940010032190000401d54106540052140c2c40840342d03901400195804070300226014880c0260f040c81903076092082c4991b8a100d0b40c0c482c0858aa0714400404402e01130340300020f050320301005202d8075141c000c846490f4002c156012441e4010b6850000c150b84664080c0129079440032090201641e0700403184400c407030080b60000700003 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 584435017 1250 584433767 584433797
    0x2062a010507140c10020d061517130201120603050f0d031104030f08090a0902250c0312110105010905180105330d05010b090f0705071b0b0c0c01 64
    0x9038025202e48011900e90003100c03800c8221100201450641d41c4140e40100040030b000c40b06a070014048000c102d0384078041841a908660743c4445c40710031614090030300e0803c0304602615040064070380580c1a041080003070a40e40601c10f031010001e504e80041040658a0510075250401c140440b211030140b0487c0c0c0e121184030340a0000e145003800c0e01e80e0301e444d00d135a644641a03c0025011a00d024082c805446c8030755aa981d02c50082a103403030701503500c0150300b104540d50004892895200808007111001003000d00c440c000942c3e03441312150044904401c0161070011000642c02160360a2130008980401d1079041140940e4210840d0701c01c2d0014070302070740d00766101110000040c0244001905886e07007aa444814a40e4a03c040803002e00c0a10003c101502e18504085d1100d83d11146151042d080081d80103a00ca00340c506e100c0424201084024103030b210b03903200513103099100d050440502312240359650080a100c800240e031019201840c60b1184052400d050102d4050441c125003 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 584436267 1250 584435017 584435021
    0x801060b030115030b0a03051006060905011409090405010b090108010903140301060f0e1908061e04020d0308070203041203080601030c090501020307150e06040f171e09040902062a01 80
    0x183c51450301070442194500404030300510090318075030f91000c421180000420801e0040e000d001100742c4c4013007040342c00d10fa00078202c03001580c0583d04000700e8807003074038403038680d041a2160300100f04c0712040c0c9501c55060507409040d24050481d44441e1085c00018003100551022224038841c0d1610000e01c82a14105000c0780009d11402c00490b00ca41d0403190b03e24454224659004001080086000c2400560394a818540d03040508035501c02c41c1800010841c10111402c956022070040c2254605540031480303940003068000c1c180451000460781d4140280700b0f48000d04000e0580c10300e0b512803410b0040151500f60b514501203817034031242d210101c0c4107001040a440301030f0021440c1182c590740e00c54440011103082d0f49090390303d0098401d03400701030140c5800b850050b150041ca1200900302017421100c2440b05410040b81007140d010568614800000c442c40e021004a4580503910081805440005002540424001809000e031401c00000890042d584102e8424001c40780340e1241c2 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 584437517 1250 584436267 584436269
    0x80105010b0a0f08040521041809020a0605070c08011103060f010314060f060730030203070806060304110d0302031c050105060306041e02040807051c021f020c060d060801060b0301 79
    0x56a0501c3c2a0501030003924a00e4101d44100104d500c060700314541c02c6099656181c01c0715087d40b00040400c0300e1001c00d030000c0d000354a2a01c04014100603940020203400071845032005101000c07584000340800300144500518450b8001c1c030010201c04c2450213654800c40d210751081050401c5441107510a01c0f410064013503041020708251200020098445010703045154450030030002c0700001200c88003103006a150600c50f407503080c803400000074108550142d1580c201032043c0304210302117074403403192608040300303455160345d03620b480c00d010340754803040d402e690b4000b00500c0c80d010070140d001000b4220701421240080c10200e20303078000d03030036640e0030b00c07800783d010409001003942d9147c0340c1c2c4800340c6852040e400d40c1580b200404c0b4041a41c220340e01c1101c094000100400c5241001c00b104902c1401d02140341082034a181e001071300ba01c00d07948070342c42e05407120420407052500802112610220042016490b9103076820a0009000380cac1c0203407600f9508003180011116279a5040d00c3c = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 584438767 1250 584437517 584437537
    0x31d100227100305092b08010b070b010b0a03020d0c1808070e0408180306070503040303110c190813090905070906060c1b150521060d061e060807080105010b 69
    0xb002000341c10380210094207000c1c14801e068013400c0e00b003030401e640014004204620140c0c01001104264002a168000c140d00200114104118400025004211a6055440c0e02c441d5913150b40400004030028082c450018450306d14110702c90f000e00760484506000400c2000001003000d07264100581c1310003043c4207680014110380041800079140c4c01c080c21600040c204901410f041c90340000b80780034400e9441d50301003803002090000341907060141d00380d0f1104450056181c21204c50343c085d81c4108100e10b0144035032030095550108001407045070325880318800b1401c9203d8580e03850000600d8003200071107080c82400c40000e185602d17800382c2d0301212101c0d21429580e619035103a415129158800700c004121804001003400c407003490095032411226a1500d0f110300714503280c6480d4510b54981450304119035010448030313580b90b1250618069010601203080070420a07104c116602694030b1a507164244800869025800601365086882c00002401540d985610801e0741e44a50f11b040 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 584440017 1250 584438767 584438779
    0xe150f010203070609150c0507060b010513030f0302010e061f08010902060901051e0301120201020c0a05130e011503030323060a0e06010c0b0f06010201150b0703031d100227 76
    0x80000301342c4503808089071a004000c1c1c840101043c19801c0c0440d8140061080414004108842400394034850242d07004002e00b8800d29081c0e032850002d600c64200c0c8001803503001018080e4081500c00e4015080a0000f4030032200307907003014220070403940b801d80e4250350f000d00c200c0c40029035208140503211045070058080c51614080303900465007640103240c10450354800801d80c030344a4604038021402011800605981e40341c06100082c1000e20010b2220b204820900301444180e03a4411404000440d80c5400542034070301903911303070140c04150304c030b42c03440d0b10b24650000900d43c264001040010343c55041a5440d1003000010303104c201c00751503542c0c0000072040d042c005010b040880e40c2d0040014180301c00011555903508104400490f15003c210208500f84909541c09014420522004403800d0400740c1c14010000703594014a040901015101e03c6c426800c0c402c40203600e020400c41c9001d41d200031960b82040d2020754030280071030b00561501d001010a030321020b0a01540c4100080403 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 584441267 1250 584440017 584440027
    0x1050f090c0d11210d0503061302190e0301090209010803040e0f0c0f16060207060f110403051f1401030501060315380a080601050405090f0d0305130602040e150f010203 74
    0x80c81403240c0100460303048403e03524402d00c0340c004c04004080d440d0f40700d682e9040d03803072134100144846151001c980621840c018080e60308205503140c24004290940e19003040300e20869800607000d8003070008080c0d00083d2050010600410110082c4295240c55172200c005440d0850115a0389008540c2c940e1f0185007440300458504210000b0403180041060a1b400003215031070340307000c0342e02400c011650740740d80350380020510040c0d00805030a802030080c46401c06186031038840d00d03400341d0001c00f045d40014207658282c044565100300c080d84d07040f21516815607180d207032050080c1050f0005031561490545000440141d60060310025901c1ea20702c210744094103000c00c135003c415280402000001d82c412260301d81c5030304200c000185a44401050385500d0030b4280003c81c0c402802000c5a5042000901030a400c0051381c100c1e025168034002440d660b80e031040c00311034101020020701c4c17540002070004005507054149030040a110f50049945410b0104200303240340c0780403c0728096082804 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 584442517 1250 584441267 584441269
    0x13090f11030c0d0b1b040602060a060503190611160b0f0f0112080c0c12010204030c0b0f0403081c0903050702030d02150106142802210405091801050f090c0d11 70
    0x50003d070071240c02c0105200090711510080c415406c20b400000050f44000100880d05580e405940003d000580c040d0141144004000c155008145006050b00d9190442e00428500000403503101c11100d920059407529145401a140602030301c0c04820241e03080040307680000030100c01c604807050320800704900c3c00c0507615509a90800d80703120005004e1254401c1c91502c03841c0c02c4c1c0107002126800181d596007985000a41c8174202c0e084211449000e100c16450700101c2d5007114240ca410031503058680702c4141c04940c90440702d0900452840c00c0c41070394010103410034003030603449200b00c080e90309482030110101da40356040101c000c2c103080e0700d9004014541c000d02500c2417082c0e440b06803a10708030892092207514a400030020208042000050700700c26414407001003010850b101807900008814182c003c40d01507800343d00e01c074155410100b1002c1804040599102100200a0016240080c042c002510080b00d00303c2050103150f405010b10304e0150445000b13503034000c180c0074050300e03460 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 584443767 1250 584442517 584442533
    0xa14060d02210601090f02041520071d06030c13270f030e0306100302060d020409051503120a0c060b01020c1306091803020c0f13090f11030c0d 63
    0x40e4060360045402c192280880044244508a1003680001402039500d8046150103c40802c40300c4549244140304c18000c2c0ba0200d00490f00e401441e20300102e507407507803040090442c1c103c3e56440940303100301040025850400c4100045220903010aa0a01d035500801c8c10340b51001d0132036040d84407041000781400080264081d0204a44004400704041d40490040c41503000b0107a040c0c0b2855100200181095406046400000c4041d80500414101140d00026070406800000e200d00c00204855580c4902503058078018076014109200c142441c0088401c0d0b808d0005400303000780129000100341a030320108440035070141d55104042e4103559121407006212980295046000300c0101030625a0742d151004003008400d100044c0c0705183c03a01c014212100101e04642000505080b100420f40110721290045010395234044500c14038000240e401c6188030603144240e1a0100240900040e0300c40b810f080d81c0309801011b18110075808040d510b8501e0440c10b948040c00d1004000018808 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 584445017 1250 584443767 584443789
    0xf011116060f06090c031d070b0409020f090a03110312090105040302151b030a0810061403100503100c02123c0a0816030c1b1a1e0a1406 60
    0xa6200040c0480c1c13a1040c03101501d800d259140e00213900c07a034415440200b04141064110024801496054600304a08043d805a40329400030641c1c0422044200407002c412902c0b00c502c01024429600e880f46440a041c100102d040c2d80644561400c80d084144250200d0314800300c16140d050506266508002182241c0c0098040401c02402000002a009881103410b02c0359880615100c224401005224400c009e04090f80311511070340400c1002e130000040c7d0000009414074a0b6a81c0c0c843c050044600d10316481240c16210707030010102c41203a10342c04240c0c060440d6091b81d111155500c82d80400c0d00071410081c020b100b1481c01200701d004070300034011210f00d240344140201e829240752071a45400807400b2102044082c8104800c810503003405a10141745814100580f1414403001085c048402d445108a04903441940d42448003074201401c2c008240d20340b5040601c2d101d002c466168000d521001d1124200e00c012402d800c02ca405404000e4a21030f40042459031050208491a902 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 584446267 1250 584445017 584445041
    0x81c0818101e02040f0e0c04350f0303010906050613060e1c0c050103050108010510060e0f0607050304050307080a05060a090c05130614040213050925020f01111606 72
    0x16641e8030b000740d102e00103030004042034002681d01a14200442c0ca000b48002d01c4110041ca0030841800003100c1e030001c1d4409090a1046000b8516540700c40c1203400301184004006441404080d0b030f80000008000d41c1601c0e80d04609010b00c90f40c800c00d01646000d204400d0800d810024000d2110a10440030340401c0c490042c00071f170301c442c02440c0300c46040700300744015542c0c4403000340180f1155806018440c01070200c0700c0208410715007814900b04c8510030b0f000340400c01402a40c641d00c02da40d110386042a000c3c0c010f1949a85081c1803030300959940c001e10520f0302a000b00c1034001001030703010030f2010107160002c001d4602d941d11880000000c0011100450380c0103844000410795031a9004400604242c10800142035420441004080702c10200c0c010312076801081101c01e40e01c40c281494045a078207a450050640349c59a13020300c1940d4450103109642e10000004040b01c0d8006010340c1e490310741e44d00070800099001c01c00410340c41010301220301306104010f02c10008101e036001c4078000706 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 584447517 1250 584446267 584446301
    0x204111b0f1231060903030e0901240e040f02040f0b0a02100b0607060e010c1d0616020d0203010207050d140304170901030e070602070e0108010204050108040b0a0204081c081810 78
    0x42c0f440400b2420001d4002c80f00080e81d9103418001c144e000007840c008a403040f00e44e14010340c58522035600d460500b4548136810019458200c2c4828001c81e22480c0002c4010401d0001e5404004020000d4211748100309680100d4500014202100c1049408240301980548107014107a10030901401c0801d0102c0c3c0c0000d001c200880103c2e54a20a00c1041c812110021440030404c4800404180c0c115107128040b8103019407880c8103586000845040400124005203a43d105000003210304400038800f070741550000905000300700300030802c140a810103403513105100740111098050b5000481d0020000811248555020011000a050700400501d03010502c0900b4076881410300d40168811005079000b41c0301400100710700c03203d490240c8407402c0210301b854503100008220b0040600081d0945442e540400d04881568040700c01810000b42205d88650103518121b1000302c071340c0038043c00580c80c05d000c1050580f80310046294204100000c0c400081c00e404600000c140c1e00d001c10109913 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 584448767 1250 584447517 584447587
    0x19050c0123070309091d031e0d050901150e040503040303080903070f08310302040203040f080c0304050108151f020106230a050603070503040f0204111b0f12 69
    0x10922038010542c1d14070036034034408001c0c0f400369400103841c1e601881050400203105203aa242e00d000041d00c800c0d140501103600000411024103485100b81c151102184e4102400c0200f0310805402c42030841045001c00a409661341c55010040034050700c000300382da04100410400310b403044581e02c0e009400f4070180c0e4034007189984d41000d020001c0400300c9040d80e02141a082110b08014030310800c2c601da4207518041d2340110441c140e041c003140002480b6641c0800450244444038610384409940107007034a646001d00760326030f59613030400d200c1c460002e4000750002e14058002c0000020442010304003c0a2500244c80d0b005c2441482d104c4204641d6600000550815410030300107a02108220740042030b90b03a003061001c0c402c500e8000a00510082003806070b95644130085a42c0075400c500b080d42007112600c0018041c0400101650740041c0110b0195000e1500855511030940404c0866160700d04000d0030381c0d04c5488120722009860000c0c08a1904800c3c4030003a07a031843c4076010104100 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 584450017 1250 584448767 584448827
    0x5030f061c06090605011a2a07090504021509060d0b0f131d1f0902010c0827030721050304031e03020106090513120e04050a0e19050c01 60
    0xc0c0030004000d440190f2200303100d50a00c0094403030036015010411070344002d2a0001c2603a0300d94400d40b12808405c1e00c4240340540c0c80460740d854184410001000ea0f24040e546841483c054201500d05a100308912204070f24030f03c04100031100a008054021404c000c228a00d490080480742c02e1140c00c000e940c07a448000c2e81d204083c045003910b6400c0005842c0b10380b9103d124840c0c9203401c0f00e4440ea0322915401400c1c100f0035a640c500380c40c400101103021005480100e540040d0752500a2008402050009a1810720315a14580c02c04541e0004607408502e410503070354003520700c1800084210000c074000d4103c20440c441030644d000d8421a0304e004c0c0e881d84c40384200b140d20401c4040280d50a44800f0816034203003d18401040a84010301c282d0820191000300540007800051401c8000901620424010026080e010100820030403c41c54001084405402d24082c2c984c40c60081c46042807807860006100f09500340c1060040c014400300b2001901c045005291240c1c24942e821072003510 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 584451267 1250 584450017 584450059
    0x1501050703170402041d03251a040503070b040b06040b010e0105220b0d0605150301050102060c0702120f07140a0e0a05090304090903030b4e060a09050c0306010605030f06 75
    0x54a22074003c0d5510310a14281c1101d181c1508030301403803039231182020000300c1c4922205c840c3c6c1c1d5482032003d0115445900c0d25070f00d10300c2426001000c400582040000344610f004015100f02c0c000e640611038911114011504451076180e00c60118005122807500c0c5144a210103010b49500014110717010f448900c1d694150300811381c0f030b102581c1c8899040c03146060503209501214072284a035819035041000107921003070300510321442003401081a000b550394624540361803529002c199004040160724294890030140103c0f1603256110101e1262818840302d080c2c00c4801591101da0700d070300c3d01601400a0320b000740c14510640301c1400085902001423103514440c5129480002d14243e8030400d110046c24000e000c400002c0a50620394510004078030050642506929441d445200c400c00074a507019184110100a1040c0c40400030702c4129940403445e518040c034100c1c2c0706500c1c028100b43c3c0c0d4003001d005030000103405001150048404001c1944c103c2d0008040d07440031080f014500706 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 584452517 1250 584451267 584451311
    0x1a1201060f1209053a030207060902120c0909030c0601150207080f010915060506071b09140603010f061a0c0a060c170901020301120b130c0e150105070317040204 71
    0x440d070b0445000c20b0800300301c054026010f095017019402c02145041d8420946600c5050350700f0505400160584c100040c56028110340d46d4001c4c2080c04425110304080d035030f5038030346201c1401081d020b004500c18100c008162803046402000802d6183c1c20440d80b4040c1c17440580184041d4818420302240242003441040304002c0d0400c00094500f042c0d08211070a6403800a0f15858241b902c0805e0020340c0b01d11084451140d0414503c200010110f00d0b400e000c03411740d501520350b252514000a1501111440990041e48120024400d43c04510110001c039034003031082840d8a100d055039005411030400140407080c218005803003035604540c5445040d1030051a202c1e002031021100710b110344002d0007000f50030503a03c0000b18195030402a10100c4d80141c504050004d100c1800060203161a44144a5950740d01c08040500b49954410f0444090340580340c2c1034066420409444865200748151004203402d40d0310269107030a580146a0a8400a80142d800c00d8541520f14003a20400b00440 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 584453767 1250 584452517 584452523
    0x1020306131d01091208060f062502030708010b03060f06030604021327140f1009110307080a120f090501140910050406120207200a030f0302071a1201060f1209 70
    0x1400ca000c5c1e6440081c4071000041c00f0078800e000300f030944449601c0700360540303540b0560708900b9079501201c44800440d210807190003d40c507200b00741000c1101d4030f040d080304100f00c005804841b15078445022000e01818210b82c0d803901a070200300060f02500d00000500c0300c0210400000448103000c02c4038101c000180364a03801e003111014003400400801c260025000c0c02d005000d02030f80301c1c07a59203072519808122144900152203d40450a120590308091400f236002411240030958450311251a94040c0002f940c0d5000e5036002140c0060003842d810900c0100b40d581c3d21049410302005550121050315036030400e010070301401e510764450008486043c1780e9512841e4650b8500034005103da026079080072642c90040c4170b114002131550100c035005103040e03c1004a00180c0002241c0c0c0002954006050300c01c00134a26070501d900441c206082d54900b4401d24a00c00d40914150704602c182c440c00500e58950300010822103210350350640d1580b0051a0000344266101c1500b426208820019 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 584455017 1250 584453767 584453783
    0x603280c03120e060a02060a020d0e010906060504110a05030c0d09060c090f060906020c040b061c020915040510272408040503070b04051e0a0201030e01020306131d0109 74
    0x1603481c80d800c00e0303c42140c11811900640307040c04408000b500c800e005481078031010340105a070038103900c0d15000001500c01644c0204800c0d9454244040901311500c079150149107840d0a1030302c8004000e08980c41048182c403502d107107480d180366050140d03010a0201301c92a6072010305a00150b1140070b14407030241603036a031a00183c1080c030244041003050344400c0911045900c200441ea4011a038001c943c001100c00003140d0a08130042240c520072510b4011132120200c98084941d4020343c080c1041c1d0000751511203020b13580328119001845130307016450b4020406440a1610780c4100d4402c000301443d880359000c180500c038400d00e400903c1d034000440810110b42d818500c07009400e0b00f1800300d007035480d202400c0d04058848580303902c20640d0181043d540c1500250a1042c1000b0801a0071811600301e0591410100c3e8140c07540f126060480c0024140004d103101004140203581c043c61006004800c80ca802c40102c40003400c0c40c2802c105964500b90790751510700340c28810307860b11502511103 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 584456267 1250 584455017 584455043
    0x4290f0d020c102c15070c030e03010612060b030c0406060c0219030308160504081002040810290f031e160807140303070c0b0409140603280c03 63
    0x50030341403551903c40c0b4010140f07810030b102c0b02e8a0340400122140c09070701550084d04c05520000382e00b012042c0d4030308000076026006000a49034484100c079400b038001c1c1c1c0c0310500350320418201400ea80c160f108802200608040d40c0c0e0105d10943e00c185581d04000301159007400e45500450b080da903060380408089055109090154246020141c0d4200c0f6011503801c2d00c07a04581c7d0103800300801404180c45d001d0144070306030880c1e0103501100d014040e0b1404441e01e0041041922000c2d40c414043c43c2c820b805005810511050700b4055041d900d07200c040b005658502100580004251101200c1e52080c0e002c804e500300d0742c80c280315000c1003c11142c101d80403100c4a1a0700c3e4a803a04502540b03020309600001002a0354005c02c40b07009491b18150540380b000038050009185018a41000c0c0c10716413103840024000c000c00d00103004030381c91071406014a071401c0c0502c04400300c0c12143e072a0150043c001c000c030740c0f030304007040542c5605800301c28030030818041c1c49100201d04103810881e841c0c80705c03400d = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 584457517 1250 584456267 584456287
    0xa09021005030604110403080301061107030606080d030e1f0c030b0913020411030712020304030908031218070803040315020f070f0302070e090d030e0f0102070b0109050a0204290f0d02 81
    0x42c0d811100341e84910a06c2d1610310740d01c4541510051158004000b91081403a043d50400e0190000468014a09100a43c0c44142e01c3d900c0b01e13042c0080c1000300346016904086d0041c0070802c0b104144040c0c041404041c410040d80020b0f111003c942d500301a56001a8541d50b82c030207196600030740c0c101904081410240c070600044460860034040941414010000200da002c002c44035401c1c0301c580c0250b00c0f40c8840c038090342e0325440ba0300050142d0002160f42040003021103a103512800c14440940c80629070031307419685410305409400c1c0b040c0c0080000707002155800c56001310b0b4091402c2c006191078281d0714540c0054000c0c41d0100d038440b1031043e111091640c100b0006001e81000305c80803115080031003040d5942d41d1045544010b0507225003d5401052017401480b15000401001303542c1e070302e8240340040700d2140901840000514260200300c0210240c0709840903204001401c0001030851303c1c007800e01201c05204940400c1040258050024070030001d003440c030400c020007503181c0b41400 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 584458767 1250 584457517 584457521
    0xd240501050a060e091315020c0f0601090c12020304150606020318370305010510031403030f0403080c0c010212010509060f0609010c051005012c1504050a09021005030604 75
    0x5840f000402c48a111100c1559580750f0000760052034400240c0005603140c94903800c4142d01e00c4d0400a03440c400701d00b034090b071640407628501c40e00a04c0c0a0b207155a80b03992100d01142d402040000004514910008030781216500031a009802802c0c0004071f21240000c140560b1025040340c030040c0c0001c500c25400c081c43c0c040c00070640c1001c542441810240580021480c4040703500c4041200190300c04199204118030580e01450300308000380624501040b802c881380300540300c101c0300ea12a80d001c80c2c5000c00c0100c15207020f003503440d400ba400c5480350f4604469412015106d4000190104000c15060317030b00744024560048612400151136240c02c042008504004041da801020803414615150b5600400c58141c0718090030048405109030070138500d000400038800382c00c20718010012400c4690008500302520382c13125510401c80141900b4090200706031502d1180c031b294000001258500b9401040e1b0000380c00030002819000c40c0c002607941103203484114003040001081c440b07141058 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 584460017 1250 584458767 584458769
    0x30209040e0d120b060d0c0516081b0703080f030612060702010501090b01020f070902130504090609050f0f10110c030a03150501170103060507051e180a06020c0d240501050a 76
    0x804004084143c0041402407103140c805200e103580d1f0384080101d03d0b008000f83d814a0381001e40c080500041c03864103d03800e611455001da11f8a6041c042c400580b040003030070030140d95101d040300c0e0400841e221548082c0e0000b038095940008080d035a5190040e0410170309100760001d071f0002c5195458030810504a9045002a504540014080089491001503510111481c14a005039640d011021000ca040b003150066541b19040411036014840603801000f007950052040da08400401034030701c2d90310410ba02013080079030070185100440300c03100c0c0e00c003044903500440b6007407518842d600071a007550302c0540c0f00c0d40032960703c103031100900480c407421070042c010a09000400390358040d11b040340341c0c60501c4000e09880c0c80300002003440d1f10550944510701071403902c840781800c01c1e450306070858000740c0031007034205203081030360003149428028a0111034081d0050007011400c0f209001c051540c0b030b40190f9480e041451903050101c10314200502e101c40820000601e54100f03801c01ca14083c403 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 584461267 1250 584460017 584460047
    0x705120f0c3703050a0c08090409050a120203042403020409050a020705120906071506050a060c030e01030908070b040f020316050f1e090a14042a14040b01030209040e0d 74
    0x1c0b9184000080d030040c0c202c40508245003402002c5803514604920f161042c0100681c109003824a020200400050442e0826100b540780440200c0c0c9414100d070b59019a1082c0d000c012585080240c010584044881c1d80d4400707807801610305520b505c900410786400b5105481029030010700b420900c0401d01c100301d84850180e030010714000028000079054082c0f040c02610001c4203070491000030f00d150340000014440603010040e1f5565680014001c1e00000c40250003042074001d80d010558172070321a13081110781c840403281c102749503a12158107614006008075100c1c04c0440800002d0f0360204000007011103201c1c0c1d40c0302d010b818070341441a500d4840050a020320b44544c100c4a20501214584118040503250f0b000310740e584612201c0034006c211444940d1018020603c418803265030003a10780c2e035508601d248036600c01800300303d10b1311600e071258100e2003c00f1132032081d05150542012061180525025041c680b400c3e001a00701c0d0328180380180c10f0780c002c6482c501980d401402102080c51 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 584462517 1250 584461267 584461363
    0x20d0c0c0b10032001020a150507201903170a0c09050105090a0e10090603060c030e0307150f02040b130303020606011d01210509060a110705120f0c 65
    0xc515564090201c05440c507401c0003d13407071641c44500380d1003004a89050386d00a40d4061450b400464020010541990410f00142d5040081080c0701c04401215200d0703013207200100405400540300c4a410b03080c54030304404210300f080207000c1c20781d01f22107020301942c21301100042100c0390740e01c090f0400e10a5404541800004e02c8007000d5503076030070404000c684600d0f80c401c0c5c0d19614103600f1104d80040340c01035030415282c807201005106c0950f100b601740040da601c0410a0f4a40c2d9a0402d95901581a00603c002121240c05e4495840c0e41c0040040d01d02020025040544501003034a0700e4008540c405c40c011444c1c0b0040043c19810010b564120a0a0900d106d44258071039141c003411041d040d031503051006201410020003070840503600d0622203400700300b00c035081c0010607a4582e802550f9624100c1e08044402c0791541d002c0d41156407181d440f00040465044890800d40181c00035803c01001c01020300110a15060521914204c8403140403a6032244421810811008884458100e030300702c = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 584463767 1250 584462517 584462519
    0xc030612170a0e12010b03060606031303110708030a0309050c041b0503150a090c1103030108030a0804080706090c1e0b070b10170c03061608060d0501020d0c0c0b10 72
    0x1107003652000844820646410b545500b076280590f4600c0303141070302c0d6401031038a139040083c41c0819488040e156400304d0540e2a03d071900400c0281070700055441918140c4003030302e60b0002074050400d40c5510400e807001e544603d6952000390341907401502d41d07000400d440350710b078104100d010720168283d600c0880e000c03c41e140001d0407501c0303900c2c0e0202c0781d0014850000042014801c91340480250688001c1044a071241c407040c00c0005000030614a030701080806081e40170811020003624141c60b1080300031414109011804c80700c10b00040c106503400003040042401190041c02000c60040c010752011400c103140408100410900d10580b40907144640c800340407108000c411288510f4210350518156180d82c884004140d0a560011105c0c5034001d140179201e07400401c001c2c10701030049050303450a944402d40010042c40802601e80064081c0001481d01e1600a00c1e1080300e5004070f0006044c040220384a41c211a9000f11038408552400c20030020000740b400b5650348280c010840d80245 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 584465017 1250 584463767 584463773
    0x90115030f06150f03060306050c1903090209061c050105072003070203211204121d0a120807121d010c020f0405090a050318091012020108040c180c030612 68
    0x14080300f10341200304a0341c50f682a5a01d4803917003210000c0c0d90040410400c40c20410710b0940caa52150f0041c03042c0944031680c41d10103600900c6048180c1f50003400c003d02c00c2e40c0d46020041c040c03100728090740172400704001c3c241c0816424440c0c24440c101588841e450300c05201c5810610750000d0140c4000d6a20801c00600140c038007140c800d41252070740383c00c500c03015885030001c00c0034001d003041c522451403402d0411041c0b044204180c03000ba440c0351624039482100701064046450191541500a805548100941398040c0b075814003c60160315200d00b0309186a6560358008142840e4000040e04401491160681c0b14104201c0c0a03090900e5101011141c0c013043c2e203026822103982c0f10310f54030780c00100140303418094202042d074400285e9a070b0300c11500d00800b1001088030307a42e000f4010080000d4620907140b200300142c58a842e6500c444030140d900440c2c07500c900030320031118a905a0400544090781441e0001c03650507070240441d44159405000701143d030550b00900640100c0d01e404408 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 584466267 1250 584465017 584465039
    0x1b0601051219030503220308010e22120216030606051903200a08010c050324091603090609230d210608060f0108071203080a020705010b090115030f06 66
    0x40343c0c1070070203903100d0340d900e155040846179403002100501c440380030304810160b000d0714189c180c0b481035420781d8003a21060128240c81c40028943c003e40c0a2182c0c100300420412400c2020b0055988112081300c032000d8050486a151584100c0d600c07a1944818011845c0000d90351104a618a0344e80c0056403450303c8500d443d560744115110300c8585070603550915164800c00303501620160009000f12a1070f6040104240c1c41100c3c5002ca0300b030300c1c00390405080341e581d219980443d001022880142c451195101d6442c658140c05000c1c5613680c0c02c1b0390300251540c020060001d0088044403000d040c0c7e0040012140410880c0009503040801400c04090700b0001c03421a5031010402120380400801000303000700580e4006201d00d203c1c80741004030b00c410410b91035050b141c40c0700940b0f50080e030700c140c0309800001d40e620080c0030401c2e840016603020780a60180500c0d50256002041d090707c207401040441400f80c00881210b000c0760503064220707806008004a0fa60242c1e010484c0c2c0d46010001a6 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 584467517 1250 584466267 584466313
    0x21e030f0906070e0f01090801020406090905100303090320040615080f01050a14060c0102040e0105011101020a020a0807151109100c020907030e03041a250b06151b06010512 76
    0x4490111414005c0032640305d81000000703080300f00e0003155999119100036000380c42c607108030300034030f81020002440300d050303511000200c95040e150101c0c0141107a841ea46108100c03d01e070b6192502076070040c40305944d540a080300400c13100e65540d040c59603000c03000f0102900181101030312020900108181c3d111003040324100e4a0301040d040364180110001084c80c030810f000300189600115020400d200c1000f407e60480d00e098076003941d101c014114141c00d074000da03010f00d00981c00605454011500f0800208403044c40b0303070700d40e078a01104a40754200b2140c68500603601d035200855840b0641c00c00c0350409018140c141460b0f0801880c581c0012130001e00284644100740d25508101c010b450100181c0d00901840b82c9807004800b1074000b92151a00032010340c9c501c1c0950181100004a9032100e441c04181d0400015982503941a0a0007581103256070321481c001c10800106240c818103941004460480380040c01140d45800304100011700b038a0343e000241c1c1c00691148032103240c60782c3d00303d03 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 584468767 1250 584467517 584467519
    0x702420a080609090d140d02073906120e0102030f010612090c030f050c122125020a09150e01080c0102030a0309030e1314070201052206021e030f0906070e 68
    0x160241b0003042528a103004050020342c807036002103405020003c1e003103000f0b5020300c0e9a0034002c4002e40d1140c000d0002d160342008110403004000d0302446554800c141081502d66030309000b18409075900c060340d00b240c5c0211100c0450b1811040140203a5500104645008404101c240139488035034a80301209075052000610a951200310442084428400d071445840010032140c204a1035800860301c4440441f0340043c0c031003035400c00307102c0010303003a065681411000d10310016942d01404400c03d0703180d084405990011280800003028991402000455180c4c41c00c03807602d05150072800c40c1c404106802107801500003141d14001c90760b000083e9054001e09180100302040e0130704003602c2044041601c580c1000030380b00c0085e404605034218800e0030800084403034565540c06422800c0b0394003610880d210b14600d441014209108815065170782d4088c0500503d4003018006d09401486000705d10140c510010003005a880c140d8070140380c0c00044040904050f1070704601c002c25000454442c1 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 584470017 1250 584468767 584468777
    0x51b041505030613050405030406022802060c01060902041205120705120708090915030d0f0206070c030e1c0203060a02040506030105093d08030702420a080609090d 72
    0x81d40c2075032001d136121007004250408114506150030420707202e1344070780610360240c418003031010056103070100565010016040d0500c91006541d0070445150b01c0300c120208190b4840c0c8001c6001c0499200520080c601884004013042061600c1c070f0801d0b4a42441048005c0300b4020314001c103001260481c40500c0d094032259030ba040074602010607002e10744034650005016800c001c095144855231281e89901101101d401c004014011221001c0c6200814011381110000c21000d0b80500715484003103120781004860581c2c0d5034045240155282c4101e05903441e00043c000c154201030107100d8000306a081c0551034281050045020703480180300c0c280c0607882070b00009145090010048059451403003903154484040c040c3ca07005100484a1f059896000080014070094000101e035030156010f003001914442040718600980b1001c180c18884a041e020a800e06181000c020010b00c1891f80c405902c5102101004045400003003255000b0340320641448101031001440303042075441c078900 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 584471267 1250 584470017 584470021
    0x2150f06090711120d1107020f01030507050409050c0d0c110703020112090506070305040605061c081303080403052104081011040504110301170303040b240d0303051b04150503 77
    0x12950441c0290081d401401021254280f6402007002002d00c2040505d041c8110210420380448a00c10f0f01c6000754010240c130800791036540260030040d80b05a142c00c0c00d82c203241d5220140750648104450300318840c40002885182c082d00707803140032820003052400c1c11002402d02040d80ea81da0306030101905020310f4049008245036a9001220026441000d860f103500307041c84085c1c060042550100d80c1e06003894002072030760134510300381c9410982c4a1316800790000300c0d0700d51740699801032000c01c843c00001400032020441c144021f00c0154410760007004441a10ba05688552541c9070440c50200d10400040000c1d120024414500821000c400212640c100c6071107500341c41980d000e10b802508003000140c841a803480518104c440b2201d03d08045c00720788480130303103900c0308880c014134118110000c01c02209001e0303031020151080c4d00000031590410070015a100840410841c0025107d80810142d00340609a00341440e03090741c004d500340750070076032800c204005d0440c0b818204000400 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 584472517 1250 584471267 584471281
    0x10e13080717030402040c0203031603090c0e04051f0902060a050a02010b0a0b040f09090206123102030c092806030c090b0a06090b040b0306040902090703050702150f0609 75
    0x4032030065500c0540b0301040d6015000905107a003044400f40d210310700c2d10036001a40c50001c002c683c0308243c0e84000d41a80c000c054400d030018001031509440f0301a100d0310205000d894000200d010340e0245004094010801000c03120410642e4030658025040080c04001610768a0640304a2846803d0054951840701d408074018800100303120391010600d5800100b544283d0010f000392502c02145c6010750703455901c0e28085d03e4100c03000940204c000c0104070a00602801216000805003402040d2100f5906007122420b00c40c4da102c0341c60803110500b080443c50100b240c030308188001d442c04d005900d481111a028945010454080007420304940da120b02110390100700915404030380d0041c580c0d1900020741c003c1c01c0a580c0c080c00784c40e0a0300b01003001030140c2008411100c40d08440da240a0804000c14080c2c1c101500312078106071160008401a034030f6501e00ba220b052640d40000f82481c15440091030a0001402948240801000d01c21149001c90030310340c0c044415641400543c0703d4030 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 584473767 1250 584472517 584472533
    0xa09051614120c0a060e1305070801090e0c09070f110604030509100309021503130516030b060d05070621050a0b030613030c0f030e0d0602090f1507060b0a0f06021c0503010e13 77
    0x1c200c01c4000e08c1c0c42d0070051465040700340e250580340018000c0000e52200c03042181d03a031740741c414402d034020584800070388010b01c903034580448643c80e40381010710750300c89041092a2520a0b14220f011840c003045000603418009a0100302d85120728080c80311900304c0d00441ca03030100c0c0321400d400f00c11001000450800740c40c4001d8610543c031404490450031001d5956002c0c159500084484ca80c509000c10704900d004c005031442190030002403e0307c02d01e0081d0a540d4042c8032903038548001c2c041c48607625983d9031071007001d10481100201041c0d45000c0d90030035040c503400070403c4149201e03a08040010075840141015125403059030501008181c4c10180d031942640c442d003d611005902229081080503005003060700300554143c49140100707010421138070000b41601c00c00e40010b020203004124141c004401040d4040c0003002001d403585444004082c20740c2004001d40e11081318062025049140901a0b070a030f498101c0c01c550405c1d01064007482c01528841d4103001d104081c0701800780386 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 584475017 1250 584473767 584473789
    0x31701050d06110c0d0e040b0102010e06070c0c05040c031b030c09030b0a06080303130303060608040b0406020a030b06040602010b01090b070209010b07081c06080f060702060a09051614120c0a060e 86
    0x20012503245c44102903004010001c04a825030081e804d00c031209130b4550050143d5141e800c1c0301c0f00a0551569052400c130307038000000000342c603160345045001660307031035034459070420125548c2d010030f82035080d41030240f482d19201040313002c051074a030702031180319804129541a40d80c0980344410507140c10110700301034405d03900030316228080007083c401d0003400703074005000040c46a1024000c103a992a826074885100300c1d006010030740400000360001b880c0790b00804190b00d10382000248c800041b00860880e4200380c0000300580e43d0340304cc0fa0803540e0000307072147c020840e0030798040c940000da43c04100f000c101032203040b410304070115102041040d84416200d100805600c01c1c16103441d4101700f08050450341c800d4a100b8003d440d550941c44502080d02440f42983e500200082d4660765121001003401c0c0b1400d80386c2d401443c5520113456261000c0300010464410405103140c484801c003c010880c0c100c0800c0c2c9079002c110f18011a07103402580f882140d0150800c0202c800010010640113828 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 584476267 1250 584475017 584475037
    0x3030c0d022203050d020106031a0702241f050d0209090a08070605010501090905040f12090b030a1409030a020705130905010207050a051624021c030207031701050d0611 74
    0x2c0d5400b03030059204541c540044900031412038001c510b11101c164205d407002c0c00b02404210b1a00d485444140502150740d42003070706441210340b0003030200c8000c91031302d4010701d00c0d900d0031042c0c009000c0e4076100b81a81c54600c1c1300e058900e280b80e514141c0045c04000809034001c1c02130f44010002001d41c1018442d074003d2540000f08070f56500001d1800740000e00c024020103000c140501d502280c010b0762403060b18810741c0d00c00700416140da4161128000d01450704140000c001e81d041c0046641017011000e5802558400310100d10384003011404203000130000c0c03605100ba401407024001c0075500007920341c00c8a03800d030340444002c00244c0ca00800381c23010a40144c0b8035070000032010104100026880302250244c01500c1c00d032400812982d5044040b0f104525200f2502a450310500940c801442600c085a00465010300d9a080c0402c0c1c0700c000100004011079804030301002490780201031045c0320550785003d8201d039818100043d544000d01c0c000540b07001d5a809840d43c2c80f0484408075280000 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 584477517 1250 584476267 584476297
    0x25060314131b091407050f0304020f04180602070c081c03020c19140c0a1401050918010602060f010e190e010605060c0d1205040b010302101b08190207050303030c0d02 73
    0x615001d07840f001d440070418522440001c0b07000200c2480c41201a10440e40c1600000b07072964590381c003008500c1c030802c1c100c2688540c0c0d540f022240f5210350024003521a04c00e450160320b5004504159502c102c46071300040494200d20303c039042c1040ca2103055503942200e428016121414440350a00e071240075524280c0b903102561120003804041c07540548401000c2c82201c1c859100d40061228a204610030211040c0c08070300c45954560040c800303440a101c000d01030040c1c1d003080003c880059035080e841200540c00c00ba00780b01656080c1000305014011128070b040e014145003007003100e410780c1d50203443c1e8602e0780d0340e481c0401e4403401e400c80b2000302070090820b43c55840070000b89413900b504441c5003001c9054958404000c403c6400750b28032803501301e4940421a031031602030051030403140d4400820030004501c0501014124031400326000c3c020402c041d00c50a44507400c801f84441800000c05540c4200740c1004195000002c903907201e14589002030301c8072480800c200180c080c105540c0c0e5406 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 584478767 1250 584477517 584477519
    0xe01020f070b1b030421030b061c02070b180709090519020f030d080a0c02070f0603020a1e1205091911010c05060114010e0603010308031b0c25060314131b 68
    0xf480f51000540881c800b03075003400c41a0250b0547c00c030340f03002c1d60503504183d050007182d00316078141402d00012001e114000d8a4501c03140d44241500c1c004a5403a4211006040f104400500c2080140080c208010080285444549550b07a4890101c1d00b9056241c1d4010003d50854a401ca04440c400602804451503800728200c0500000c40407982000302034980791807041c3c04d5100060030400c0303415400c600c0710f503182051000c4001e0340c084040d0801344481d01c0340311010035a84103502c6000308595a95030600b80c0786502d80313800b6900064080c0c11070b0781c440f908441d042c0c15010340080c3e0b80c03a030003500441c41c4000c500041c0c0f4400d081c0c410142113401000c0001070040c0090240d543c144400340d0700d090340d801c6140d08005003400203000c082c0c5071a0b0f003030000540300748002241200201c4034800d12400c045020f2200d0f4913001c4082c1c0040b4960b5500d020041c040b80290490f40050302d400c1c101131003805030208900021000042030200c0201c2010305c0320003884100520082d5a0b84c1400c0e59002e41 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 584480017 1250 584478767 584478773
    0x15030e060f04050d0c20040207080a050913020315010f030e0708150a060b0d0c020a0b0108100b040209010210152d0b0a05030a0f0f0c030f0e01020f070b1b0304 70
    0x401c01c9405866a014101070b9400891043c032008454542c07000c0c0404560b01030106141c20201c21040140d0002d900308950300225601802074103107410607580f45a034524054040c42215502c115016403218014414000420110449084986002e2800c6440303030341420011805002d102c5200116406410400310b0369180118109509881c0e10729014107a4981d807403401d08491552007400000d80d020310015440c1032454000520a41607403040b10090741180d2540000b01c40c00380e0080e00564030151031406c036500c140c0600403131041e04540441c20498400300103500c801301c92815900c0642e4810300010f5601481482101030802105605030401c0d9814800c110040001c0e40d80c18841803810740011074160004c11250745045560b646425500c0f000d0340040035012050f28030704156210002c00c0c0b036800d510710a003d10782c445640c3c04901c412402c4842022115040300d1044140d00401000d00c000c201c0c44102c84e1840c0d80f1074410202c503500c039000261040d0700041035025200c0300000740400c0c = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 584481267 1250 584480017 584480041
    0xc02060c1234030905090c2a10110a03110f030106090608180a11030a060f0c230405011b0c06030902270406020315030303190509030301030c15030e06 66
    0x3100240340d030141080c1010001c49040482e80600500190221805225a041ca0540243c129020400c031a040441500d0501c100b500301c00394449200e81c112502000d804000c01c911040c5c9815100c082016400d002d00c1500203105045140f0700f0b064136241c1041080c000501200c0c100c00d0748184050b140e584424005040e407046208060019a80c81c01003000b014900d10102d01e252403030002085604103c1da00c01d1040724400c0400d071b0741070094603c50030104449001d2400c9804164000007422207600c54003416820b000c558900c8089482c140c1e40110710000300441d410307030300242450844c00c0b540e20300311141c00e6030804005001c0ea04002c0c0009409030140c0112419510850307240c0701448184106420303143da90f8103807100700907035140481c000c104035500550b00b089890340800c0010f075415010900d558016142c5208050380901015103203115481025000f0107100051840c42d403440e00c03910b903a82090300a88404a040200d010019030213a40007011480e52002590454540304c500b0b404 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 584482517 1250 584481267 584481307
    0x20c0a02030c060408070e06010c0f030905090c040602151302060406090333090510090c0515041a0903100f02070506251d03060408030a060b0a0c02060c12 68
    0x1029124080e6500c060b450943c06072016200c488001300031651412201100004014240724103000c1c0c05100f103c0420b04100c00c10380414000e4580c00007042c602010300451090040031928116000d2100b84401a804036100003241c0c07092556034055261100175008414036a40001e5005070000740014400b5000741c41801124000c0d01003501c1010700001d40c4001892426100343d0800c20207031542c1c18031005034000320700d15000c0c1d82241c20018016007100c08a40c4110400e41b030386003180c9410030030307803810702c02001d401c002c00170b41d050402c1d183c0b4200e882610000c242b6070700000404034038000b15480030070845403001903820081c007041241d000f8010080d4000f00c0140d1f85400b0705000688074402e4411400c00742007201e0303915569038101807021592000340040503280240f611240f071900d0354040103400c0c0554040e1181641d28204118803000b2501e0365400400103130014007034048030741d42000c00800311765016070383c01b0707540d854103045035013816200300100350103410124480780c07901f5550340c00750 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 584483767 1250 584482517 584482519
    0x40516060207150212040302010c1a01060e0f0303071a25210605100c150606180e061003110d050c04051905130b01020f060901150506120403031d01020c0a02 69
    0x3e6030a00c0303d00030490716003072040042c54403854200002c20040d440f845040d030302680103000010050350214652251a0021ba00c51000220324880d504500d00d4818254121030000702c2c015454010710307079110840084e080b10040011100c110025081000d141205c02600c407010414109000c1840350261440100c2c080e4691000a1b8425610010903244658026030308010941d01440c401402d007120b01f401140f070f003103869090000101034580b1080c043d00015140c15100c8085104462070752204c42559503104840502d05e031000d005e6185ca0314810f1346500f08551401042d02d100038a1060201d1040407100e05519241c4801c0015086000004c0c0c01174540450b4070742c43c511070b0315000703013104045402582c0e48150040740a2201c0d140a80c0000d0681c0c4040c015a01c1007e86a582c582c10800200c070911003c1e5110f61403851507941078202d40c006000119841d50614040c90b50300741200b400200010140b50762740c0321039588039240c1d140084007141c2c150002d569940035404000e45881c1024001c03 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 584485017 1250 584483767 584483789
    0x21e0105071e0801050909070b040b030f0606131a0702030a2105040b090f1f030501030605070906080601230c0f070501020a0213240e24030c010305040516060207 71
    0x40b0101c03180180c02c2c0c807922645950303607401690070501001a0400d0140100d40548074024000030034800d020302a01c0184407405100d5140e02e0442c0202d411004001c141e5031103050100070740074101b1042d103240403d07030b8a40403980d40000d0840f000f1041d280b003841000b81d41403059481c070304100141c1c041b5509009117001100c08070624408003d42e020b0050740031300310410209119002c01400c002007000048400100b1440c1054040d402010f082040c1b890b0040020f03465000500c140013080c040d10ba04442c15140c1000401c2c50018010483c0304042e00d52410031052002251001143e1b00c00d01c51380d4644c00000a507204000017241c0d0b83c0300d48104c036560050051290009040d8008500309100c5900034002419001500ca08040240604803170088458030b4846c80c81450a80b43e607440024208401c9015518103000b898110140b5440c00141403070040d170309041050b51004540345003d007200303003008241511145007003424420a603010390101c15041c2030009815600141000840d6100041 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 584486267 1250 584485017 584485037
    0x902030a0c050c1b130c0807030e030304082a0102164103040b03100306051f0902090f03030712110c010906050c010b031006050102070f1401050703021e010507 70
    0xe90b51401805164915a00480c2038601168a0080c03400e801900017080c1c1c0c5a0305510403014400c595110090b07600003007118003040380741901803160070030000500c4011421f502d410b940b58071051252203030310300003201c0851540400c902c03202501d80300d0306c00c048025915000303200d5203100c034004001c1c010345440350805c0140c00e10300d10ba01c43c00d201903190600c1949444242c110041440364550080f0710740e600c010400000c0c0f08120740c0140d40540308100a0a400d2850340c2010003c1d22400350010007454282103084446004015a1004484540b2009620f4440000000301000d0b1a40004c40e094003000071648204480100074454848142c0c60701c0f090451030164095036560b42490703d80c00b2401d1440240b143c2802140600342080e58000046809030812020a0515544980020340c0d2621240c0a0000d0b43e01400701030f010f4200015241d01061a082d036924028074403103510390600c4800910f10040c1407003441307003107000f0040340c14500c0f1809081c1490b40c001c00088602c103000070a5450 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 584487517 1250 584486267 584486291
    0x203101e0506060d0c050c070f090507030507080103020f0103060e0a020706052a03060a15110111130e0a181109011203050702191205031c1104030f02060708040902030a 74
    0x1007928069580945040c1c1003685024500e402081503030b1303611042c0302c018030840800000400c01c1e00e0282074a082820390852802000d07005642014180c04149800d100811103000e42c000388090440b0340480d51400c0355040400103800620701904040080141502007045021143c0c0042c5405071060790204043c1c0e40d0303440b4484417140b8248400840b005050b404450076007402c3c0c05150000350040109418a80e034890032082540303104810700115050701c00e19081c4110a1103500c3c420001501401e2038201080310287c15101d03180540000f070038102c404640060829408002c0d4403542848030a802c4801c1c0c01c000d0311030f2081594081c8902d0a09001280341d4232010001c440155140e2600b504041c015070070407a500103a41e5480f1414903107000009103060410300d0601c01d03180203401441d41e4040450f10b4007000700d804820030140d41c1c00c020101d034101c040d40045030100c0b0707004503041524104074400036846201d4184090560380f00418042241c501c16401180500651681000f142c80404 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 584488767 1250 584487517 584487521
    0x20d0e0601050f06091e0303090603040f0201120c050a0804060f060303120e07030308060d0f0b0a270c030311070f060e0103051014041112040302010b010807031a06090d0203101e 78
    0x8440175412880c00ca00f00820700412211600c1003000044c02c1e2070410380e401d0049000e5410849081e1443c0c2610003a001c19942c12a031400130600784910140081d41010320301030181e00c90110a881041018400181800300c0c0f40d000300000c002092052000316904c1c1002001a0011160741e01264945450792044650020741841200d0703054444004503641c1d02e08020080340901415503611604c1e8501800083c014200148242c3d00040001001d4035060402da9a901000107124110702d8507520383c40c0030032184800d01080321f9141c58001909030442d55140d040c8801540310701440e4843d4140825050340003c4070083e00002a030f4100000c0e0748540c6118000c00d00c03441802511096a85047c0103424075410903a4500c00c140c8125180240c01d800491541004403003d0380182d6441030351460560b4032000054006010b417500b4406d00e10352002e107030b1103402a0768079140b280c940001d804400d92074102c41101da0325001010f413032000d5516004880a041800d001c003800c1c1000d4034165410012038 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 584490017 1250 584488767 584488777
    0xa0f080708041e0c06110708010e0a1b0803030c0a08150d0303051f08010c020d0212030a0b0a0503160801060501020a08030f1503102a0c1104020d0e0601050f06 70
    0x580d40e80d0086803500d8542241d4903500840c0c207480b040f5000e01d0280030501c82c01c5031070700800c4d0380e45d640e40c4400700c58012142004c0107034000b0b4141c0d0341000361740b400714800003601407550340d00000100351103282c540c2c40401d079001c1d0368480fa166000c080304001950b10071030041e01c01080a5210b0000d02e030b40b07202254100021511140d60b11444070500400420302c654400d96204c200c244c01c106500c2d002c030702040b41c2010a50b2041805a465100703c00c1529410b004103111f24009000802d901c0800c0c14002c40c1c0740c00300411811100b13586205d000503070740e20303109100c005100140c1940c440342c110650b0441b40c0941809814402d41c00c0c07050000e5039500c00122030401d550801022415500d812180d100050b00203001c24004200401e02c543c00c0341e409001c4054403030344405c00000e040d608891003400f90f410010482a0342c036144c1c1c0b0b61008480c0c20480b540043c40e0700c0b100040425100c000003500a015088400740d180780750603802c001074640011a0790585504461001d1604071250030400c040c419 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 584491267 1250 584490017 584490031
    0x1030507021510050406090e0d0903031707050409020a26010b04060e04090203010e0604120306030b0a0b01030e061501140307090e07050c0d0f17091b030a0b04080a0f08 74
    0x862182c80703000c2461814010303084040b20446045a55403140000c065034669005950025603450036460701071410040d0400c43c940e1820300b8030355145940c40280c14190b0141c407414044040b2070026001c40d10580c229005010380c81002c40d01c0c2c80c18000000e02d03102c460680424881c20070783e0014034810202c80b8071812100c0075a00fa529185c00c020044900d19101860070390019121441400107075001c0c082e107a0540480740040c49145070a0800c235000326441310f9010145480c04000744003050180100c954000440318000c201e030741203040120003e1041840c280d015004103400c0c01002403e400e080500a80d00342d88100d4880180085c600c000d100c01d440120114a010f18104460043c602c441540400c2030b06045060095611200c2d050601020340c1d0400103002e0006442004d40140315841030010100c41010549880c5010317581d60f442411000c041c6a85511102c2c519503001c020309038009900a04000d02400c1924045800350040803121000c590300080400015103d20b000900c40c40e5 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 584492517 1250 584491267 584491273
    0x50303070f02040e01091e1103070602060412050a0e010f052107030b150405190306020c0606040f09110108100314150c07110603040c090203180f0106031a10030b01140f0103050702 79
    0x6241d82e0304240c2c01d03000402c40b00801030303041103042547e0034891100208201ccc1c01a044500d841e141035130035100442110002c1c000c0c14090054480c4e804403030f0301034141d001c2c01d042c880485005030554060003401d80241c5904400c00c1444818442a001180140f03c984c40910500d42ca8004101c401030185000040d20f40d800e000405c0700d844e0402480c10703c0c144c0b03e10901c000f107440e910b512040ea07101c0c099182640d4403070018050b45003447c0c0319a0803041031060040081c80c0c2d0300e0b59002d0140c43c0034a42a07040040200202d408500d503401c6410041d6880b4003105504074105503100e480305640b6126850403d02080007500c015a80c5040710849603002c0f00110380080507c041041d150006001503400a0009034080707402002031000358010400d500301c00151490190015107866401604070b89281d050110400000c3e6400458900020321100c0c420440e130717180c4408088011075544042c00c001000400000c4a4412080b04100f0f9081683d40ad030388515454010350907158141c4503d4010b034 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 584493767 1250 584492517 584492543
    0x6030a02060d0c030e030d09030906110303041b0801060e010807090509060f070c0f0b040506010501090803090405090a020d081e031009020a0c02030d0f1d01080105011206050303070f02040e0109 85
    0x80c40c15444407001e8600f80c10005007854000300000c2c51038000c200c80c1d034903c0d0ba4401012090540000c4118010b0402d49441e600040090462940f02d0201800050400008078000e00d0040c0c0d5508151000c0d0080380e000300000307a1f990022040c0ca01e028881c00d4143d01501d4404688409180a03c074483c18041000300601d8071020109040030500803e10380030080c007440202c0010b5440d900c04810b240c010340f142c8915041c942800c5007803c43c1a80640c2c140003507504e0802610b04040241e9108240440b4001000d035110020207040c10401c440081d40120210000001c0003010700103080607048401101040040c40000006648400da130300380030071a40070303100300080c0c8030751b030000c10b0314030b4440c500f800200407a540402e213401058940324010480308205071052a52140c41410651005a500c204c021141000603060301e0040c081e0701e04004800200300261034582e045000106000307402c50707a841ca1742d0b04000302405282c3c10202d200700c1c285412040d011005000380002d0582011551801b4 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 584495017 1250 584493767 584493787
    0xe0c12060d0f0b0901090c03060b0f0f01200f010c020303012907020922120f020a0b041e080a030c031d121303060228090303090e04080405030a14010506030a0206 71
    0x30040100046150741d2071b1a444400a00c105002000442c0309140c042028104034040040515400e103025004800306000301e6040ea030301c003c40d0303d01c07181545c9940450641e00b0f0b07259401c0c83d8060105049035800e02c28014040707580040158100c6e5019004108180d10518514150200c40d0f04016071200d0203001d03034009460300f104c47c1c540207500035203004803a010700070312101240c00100d0140d603080c04449090b440c0c0c3d0b4000800783d01800c1148098150102030b550f81520805018101a00c00111821014a81100036040445003504806090f4445501820040160084174003400c00641450130800c1d0301c0c200100d903501590581d4000d07014003c1d41e000c003004580c1140b13890815454507420700101040803031004018001a06803102c00c032003a003511613030911542104c5502000400d0a0800110340d005280c0c01c02c0c0d41464406541d581c80c0c605081c40796000e2504090703418081d01140900300700f154030829100c00800c00c02440280c0d100e0041646512021030301a40214003004040e200f = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 584496267 1250 584495017 584495033
    0x3010905070908160806060609060d091b0e01031109090606010f12020c0a0615150509060904061202090903040f030204180b0f0103060b040219180e0c12060d0f 70
    0x1021059241c00b03114281d8903049945007014203022005010200d020074400c0d944180501e56000c003080c2d440610701815500810400e1250380c0194544981d2014036208100198505283c1d060a0b480c01c0d0303890984074141c00100401c20311089840156440302e1160605000b03d0785803207801c0361406400c0540d1404019212505004800010042c01e0440384404090520240600654010013011903040038900301c0c0031100100512441c3e607604410030401c1001240c6c240594020900c1c1c4280c54081400c04540079001d01e6940750780c01350526002107170752160b42140c041014000c0780e001c0740755250a280f40303880303102e2030241e66140e0003a02814005800e050700710202e10901c488210302c43c0000d903254085d40420950f80b05201c10f1038030004005201c800d0054040b2200216000c502e04102c0e1000d402d0100120030b591414041400011405035514203c000024600324070100d4145c036021401114950240e060900040c0c4041c0c0882c6183c00e00020002d000c0b81c3c00014103010820310380310109 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 584497517 1250 584496267 584496271
    0x60e030a030e1c170409050c09280503031204300e03101805071d0114030f2b020a020a05040509160b1903150312260f010602030307020303010905 64
    0x34002c0803e00010b000250f40c20391a81c464018803400a40352030070224000306594001c0c1c01e0303c00d100414007483c803d0b07903180055044402c12542c0002e00c0f0084102200520301d41c0c55000c10750502000c04c034568107511440c603181c412841100f056040654414507040908240340396411255900000d10001034090540b09034450303802401ca442c030361507403440c0506640e03108591503041c0c00d100141c1401c0020820464000e000e0307250104207010314004110140340340511400300e03612a03000103c9640e440078003087d1030100c904416100302d10700803110402c81900400c204d0456a48101c02c10100074030200d18103100c5a07000380800112450803003080b0150030003800c406075030f0080c544809180c0f070170018100b00500103110026210a8088041035082c00062840414581010340300b40c03410b40c000c500f01061303030383c0201401c1c00b82c682100d084030700080701e01190b52414008403003d00d541c464460341c0c8c1d11503201c1820f500c00907a00ea10040b61030717020030340e0002c025074010f00040c0889a400d0b00010f07 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 584498767 1250 584497517 584497549
    0x606080d0e09161d0d0501090b010506120a0f0219020c010e1905040b010302090d051606050a020c0103090602090307090506031b03060c071109011805060909120d0209040905030301060e030a030e 85
    0x100c81c1070345480001741c0b0418054422100c0b40e565100b1075040200703800403180144001c80c0e0740360400d01c0d035003400c14945900612100206039901108401c0080d07643c16035a84103040400031800350700b1400003035506c20b404c1c407544c0e0200d841121a00c2252400101000c2c14450400f542801c1074540018880a4802c0891103418103400380407460b510380325202e00c20490b1780038038002c00b0301c01c11007020443d51101c2600080c04101d020000048883e0b0001014a8039a85c20b00c1d000a0301e484d0382c2003001c02401100350555241c010303c800040c2000c0d04c0d40003140a100d0031800e40381500c500380d070f0460350300d04e004400c01c0d01a0000780014100389607560180c04000c0c0a20203084d0b55518802c009410510240c1010b800100d0020301c00c2019419449019489a02990020340c60b041c00d1100d00d40c0c60307580b40d5100784d40ca04001400419414540c041ea12080e80180041c0491401458896103a4109010300e2000031741d00043d90001e450005842c4500030380546800021024034014030031202d2143d0821 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 584500017 1250 584498767 584498807
    0xf0b10050702211f0b01351609090501033503010e0906070801060210200301060e031b010804020f06070213200304170306030a0606080d0e0916 63
    0x60303e0300c0703110102e6070490109203005040c40c003100110010070b140032142c03062456481d00343c4139015a60000505000c4400140c000c4456041c01049501c01c900e403100d41d0100c02d2006014042c98103072601015061004688840c440e2030707196140c2c3c07000ca03082440043c0c070207048003115491a56002c100001ca500640718400f5110040f08101031b25640280d0000316900c80c00420051130f01c00130300c0701c19040390142c584031300d481d450154000c2d911024003c090b00f500d40d80390b40b060240085216482103403070140a249840e0b6035079075001340c42e58482000310b43c043c1c012184480001c0101002ca1580744e01c05031590442901c541d0203021954850002e0365801010800c4150701685d14100140c064500e02000840d21041c1809819403004d075503103001c10141c0003031040c44001254405030003030701c0e12a100314589070b40d50580042d00d032446500f0090002482c1180105900d03d01140300c01c0301024030b4440b8204403603200c040c440a85030071100042c5408500ea0390100c03d81c410300e282081d0900c540c0c00 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 584501267 1250 584500017 584500039
    0xa0b0c0a12090807110f01080a05090304080a15050c040605071502041806030c15050708160b0702100b010e0f0d02010201110c0a0b180a0b0c1201180f0b10050702 71
    0x8804102d4180c0781c0180d0381e0078400320340e07102081500004d0040c48a01078402c01160321400340064841d4002415030715200e51a0300018040680400940f001000140226214883c450030109894500041500b20980c10200029544a15102260708842d8942d4425240c000e643e100c003425814008082809079802b00030003d0760440c4d902c0c002e80f54504800b00015004d241d85841655140d042d441041c00c3d840054644800540210584400f650010040350750b60442c0900e60b11a240300220040c1494003d0050254803940003940b0b003600d5021140030820499410015214041c0f42079207541c1c80b00300e2030004085414030308106680248180008101c1504170b514104168100e443c1d8412164001480340041c05480d2560581240314603404100e00f0061094494131004409030141c07001c1c0101c1c0200300b41817801c100b281c42048440041c4040755849401c000c101044000460b0405420a0040708609090b4030038001c040000a00b0556030620b041403d6600e604203400c01d0364450080c0c03c3e = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 584502517 1250 584501267 584501297
    0x2e080d0521060607211106070c020d050a02061b0c01170406020d1407180e22210c051524031002040303050a0801060302030f060616050114060a080a0b0c0a 68
    0x4548540c1a1450341c4400da034a85c203600051503030580c0031140080da071200c02030080180d002003240c1c8905070141c4045194901c00d04150303203480c5102c04001c0d08618000b0342102d01d4610300c0036408001c442c22080e079001c850340c1c00044840500d90701a01d5000309500700820005a11540205103200190002088001d4681809a502c0e03604640314004210405ca01800308140d031400c0b0005410200705480d1203050040c852180200035188651500b0100602507042c820108202c0a4500b00a210204a0149810000c0042d0a4400200d4261080e50000000d83c40c00b60f5440b071241c0d400b8414420f005038038000c0301d20103500041c0000d03018000ca003c100420803050000b4009940203403103a503502e107840c400003452144164800300405105005000400c200c26096580004040f2012900e0302c10050a60b00c040c114000018020361030b0140100303080424100c40e40c800e8400711403200103142e807002d00680315503c2080c000d040c400304038001040c90400c007000c3c041c9240b0b10b152000721200040 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 584503767 1250 584502517 584502533
    0x1e05010902120f010c03051611070f060c020a080c150d060305101b090308090d0320060f010b160b130b0c090a14182e080d0521060607 59
    0x19078411059003200d804020220f4003400790800002c42440e081109203402c03410020001040302a4800b00a4400c2c8a0303055040c0801008000c0e04d011180102502d940b594094022403080d041280103601e00326001412000209402c07500803000340c005100c40c0900c0c0c50b008255032042d0100178100d43e0710381c0d0120200f18104100e41e941c0310142d40014110350000c458003840ca002065407020070080d41420300000f5261800d890720300314182c680760700d40081d6180036100c00d44149040c919455081104140380840012854042e4075011004242d41c2d885c0c1003000c22a01c6080d003040c06040c80e90704000d0001c1c00304019030307030701c10605441103240e0941940c5a6540010954440090300710105559905280030300d0804018500c1d40d8107154502c40301d00108000c01a0f916003061844d5032040020104c1440342603003d030300041280c1402049003a0845855801d0840c02600e0080c4601e040451006016100725001b480c0c0c030030003200145d030110b004904411001010310f600404107220348800180d541e = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 584505017 1250 584503767 584503789
    0x115030605040605060d0f0b0a02040b22050a0b04171e0a060b010927110c03070c12050c0d060207080d0c021921050903030a05070213091e05010902 65
    0x18600204450070705043c11003c0d214003414841c40b0f036441c9004000000d0350041e401529681c884003c8030b0640e95025071a00034003541d403285a55080001d48031741c690b044a0381c141510198101340043c0c0d6521202030001c450400c2c0a182c501d17480c104001d010803412403441400d4000d4450880b42c80e00c80c0c5100b4003041005e00c071442d502542c01030440008100d072a0080d800c100ba001e2910130821480d00490030b0100803824021840c034011140754408640032904104151842401080c0c1c0d502606101256207a004070010f0b100183c0001d404980900d130703144400c41c4290410000c0600c803910404020440c92141c5003210226820450b100001d00440c0190000050107000003c0d03c201c4044042d041c00d50110703601c01040014a500700c0084c0c11200400d100e541170700086810b15440c038100741d441d88510fa0f00150300d0b11010520b440d0455100005060300740c429541d41d44034858070a1441d003a02c000903001018101c96052105801c0c00c10760b86501c280d40203a00101d40d801e26500440c10007004 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 584506267 1250 584505017 584505023
    0x5030102120603060a0507080f06030c030d2106080a08090d0b0c0307080a0207051c050c100b100f081b120f0615090307050f030a1506080d111509011503 67
    0x40708101e03541c41d0621072103078082500308041c8a14504180010a1104001d00e851514a4502d02280e0b00e03031404c000100c43c02d50083d003103074120349081c58054400c4000708aa02c18043c00308080010303001c0c540c0203070300848868200404c400d402955a0101d1030308403581e09504503e080d07460501280342c2a9110380241102c0d500e141e0b5030f007806100185405c00090030001c1a50041102d100051000914654410101d412010345102e84042c01c4940744a032140c00d03006442454215020368070b50758841440703001c2c01c8403007000d0061b4946044da400d0307030007008a1010801040c00a1a10800c407001c0540d0191100100381c9800c4035003003611104001590715003c460301c0b00c82005514181803a410341c20b4034801c02841d0402070b02c00c00003550f0300b500303018250040740c0300c050744105500c017002012412540603401102c2065010140700051041e4071520629211720b1020041e168003030b01c2001e0510075120301401000c84541f0050001c04006080021103641e64000d9540e1450114104c00c003941c4 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 584507517 1250 584506267 584506297
    0x5160c090c0c08091e10020f06100b04060809010b0d1a0106110d0302070609020904030c052a0409111e150a080f190606050301030b100b041a0405030102 67
    0xc00c005900d000c8501c000034980502c00001002c00114420030103550f90038400320342d58a0182d090480e194100300d08002a0b5800c051015111025541c0218001182600603000c0355081d50300c1c12070241d441070300380c410002a01d40c1040188502c500c02c10740d10f58002480400401d074003003950701181c003440104070181c41c05d0806000075105250104100303401071010b1300c0c010700890041d0350310580f2804465244000c1c141c0c00104102046641d4100840e295001001c000c0305140c241000381081216603000c5400b80200159490031250f80c0d0750b00120201c0305241d0050128264050000a00039442d050394403c0070303d42c1e41c00c0d0310780d214003281c1e0b0ba0341500341c4503a00c080d0078041480101c3c9164803039111480c0d024400355603615480343c41d090788902234002c525015200d03469140500c5107010781d040e2545091010108241d500030000354126842212883c4065031090b00078407443c4c00c5030240100c06c140802c0100401f04c0b000c1d403100005824890380302d00c1d056880f000203089900103199030030600 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 584508767 1250 584507517 584507519
    0x60603070c1407090e1e0309190504020403050f0609240403170a0605010905030312072601061e03021204080d150801060f0e01030f1e14150105010201060602071505160c 74
    0x1750078004078014444070281d0b00c000b52080c003410342d20fa01032000014081d80c82407564040240d12103901d2401894060f00031542e541d240d060030b07611002500f0355100244105804030303080300ca000410381407001f200380140c680841021585011100b000d00160100625403030507629840080070101d0080c08a000c00180007440c080002d002d420107035228600c2030304240000354016038100e40c03442d03104850340340010160040c5141420704a0150040701d814007000c40001c18060340003690400b240940f01c401caa82211a031000724180e206030764a5000c0440389101090006e42000040e0941c0403000c0000301c0d845004d500c00444002c025440040d150391100020002c1c80f440086800162492072102c0c10030750b0650303c40c0800035002d50390007068201c017074140e00345042411500d001029805000c1e44003d012405a1503aa041c03002291038200d00031000005403076005101e4501141c00c0c64025000543c58641400c01d01000314031070b031042c80020040d40000c0c991100e2101c2c00c544c0304840c0f0011035 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 584510017 1250 584508767 584508791
    0x9090f0b1509011512110418091704030f030e01020c0301290306090d0827010902190f0603050a0914030309060a11160515150315060603070c140709 65
    0x1144060b807001c54882c030101c1d01c43c02110b5024024814640d1166170120b110605070294034400d12031540310b15000c100c102403d00040d04103030040040c65010790b0080e041d030604a00600c480344942d01c0018003580c0410b15100009000300c04401d101101401502c0d125046200401d0941d2160102450003541000c0305449242404207900c0b0041e5082c2c0090a00e403500d524016690000d64003c44180020200000c1021100c443c0e0204480c00c0400d50507100390448500038060145250102d00c00c480c0e5200d800240c81510341290221280d0003050070070240740c0042900100320140c0030518090712580c004000c101c4002c519207800402070011503407490003a0066062600145c82200b03103505240e920440c00c00d6035010b07109150071006039041c0c030310361614200d407428003682c0c100c5188041507000c11400e002241200540c41d00d0a50944001d1188140c240b83c41e0181168030b0b07580150302384046800c0038030072011008030510443d0700542d00541003125910702600361740001c0f109a100d00c0c0070750700 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 584511267 1250 584510017 584510029
    0xb031009050c030c040324091a06030c030606010c110a06090513180b060414070f09060302090a1406070f0f020f030a0203120c030906070c0906050102061009090f0b15 73
    0x4882502040b031803c40c14108400ea02504c142d200240191901c070382405507100d101814000a500e40e60340c2008801141c1c41c0584d503c413030744900000d010051400003590b80c01c010031184510400103000d407110740d071500015140c801c8204802d403140d8581c060200c01684910504002502ca50344880b1616850081000200030858801c0181c07a810101d800c104240e0b000f10300442d0b42e81c81181200c0e56501c031070100c0d00411094500d10440004e034800c2c498030913009280301d2030304089a0345120001351641e005506a101e8520311981007800c0090802284110109010030507400424062500c0041c0c0c03101b610240881c00d00303440410403a450b61085140c040c200c00799484007940544084900c640000c3d883d29014100d00c29020300001d00300b056808240119455908c1c0188101c0c4ca40c065030038440d80001c15809818007a9181c80c1005c40c080d030000030b00c2e0b485400e00450740c280c0c0904040059000d4101c115003101c00400c0303015414001080d03886c0083c4941d000e80307103040b4064404010002 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 584512517 1250 584511267 584511271
    0x8130615051009030f030c08071203060e070c0c0b0d090206030f070305010f0b12191e142e030b0411040506090c1206030f1f0b041505190b03100905 65
    0x34040c1c00c43c01080001d0303201c46040406901420b00b1008582d250802003050300c10790400912600015000d10041501507200c202550b51030745403804039a840050075240d2a044500260600508441c100901d03241c80c8000c011141c071007003011034986115070101d44035401c03c1c0d80d205421008441081206541842664010041c80a080403003a1400c0301584031882146066400300c101d51002900b20781c000250035042100140c004c200603c0c40f040310302030000f0060944583d803424009600c9040748600320003801780b402c042001ca200000e20130701806070b4a0703041c910004110f404030300002088007410404d02c81c60003164134039000c0c440401000105c1c0d90041c02c03e4895000441400010000d20701030703c0e80400c10000540950b00c45c800024502000100d0b0350b0014465600b07400041e0f60042e0950085000c002c0081c02800c00e040100001d070381040c0f038040e2000c01c1c0c2d0701c0e081150303180200c2d01032920130341e508540035100c0c1c480300e0984941c1c2c8200c404903c4070a002e001004900141d1042503 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 584513767 1250 584512517 584512549
    0x10305100b18070e0120010608011b0e0d14030a03061d09031806070c03062705060c25140d0c080d050c190206040b010806040b070813061505 62
    0x208840a110300c2c5002c0c62000c0d1104041169015034102a64003038141c000d6071102c40c031861041d2180c6040020302802079801522665400c040ca6841d1092906d19143c000e00001c2d10b030488140c00130402d100c46d2001c0514142c03040c88883c261003a4120061006000c2058540c0e00441e040f8204a408c400589a121048122842000401500032008801c1e94507ca090b1041a80c54201c460000742d51802110005401d42407003c1c4000200803150b80070194041c0d60942c2d201031942220019090841c2c040f4014000d0b030041400030340c900304201c00038016800c0450796101b054206400850a5040403a01264201100104040750030405c005140700002c0e83e10781003c0c0e1a031952754050560180b00c0c024503071142c43c3d0012509241c064030039500c6049240603602d400e407034aa44000d59540c0141c8041d20887e1407200085211798000c21a540b146800020044440c2c40f00c2c582110704400c020080c1e680102c2d8540800c00040c1d03a030241a074040b02d031081009045041c00104024050079070642 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 584515017 1250 584513767 584513779
    0x6030b010815060f040e100c03060806070c0f0c031209030c2310090b0307052706160201090503031b060a020a1b110604121101030c05070b060f0306010305100b 70
    0x8088482c0b110301c8490b071114094400300010b800d18808100981408030605015000c0d8000041591102d503100494154107a6424000d980c0d40d00041a101c920940340b0b0000680e0900f4110f001c00c0000c0300540000c1c4c0701c6d03503c480e0125a20346030780ca41307001408000300c0000d025401c200240039000c078000d00a0943d600c2c449010114001030009180f02109030203004903607103180840494020303549080140790f4200702955a2901c040b000b0302c1980408604400708200001c094000700082d1410111008040c04407458180740032205051400481400ca040100d42600420a40c50074000780500b90107082101140001c00301015041580c0180030340c04491040c40813121256100114140f400030384189a40f0707913485030400c113010040e150a11a003040c0001000585d00030070380c14800031140100800b08600c42e4400045080d162078084010004009100c40004104284070709a007280c4014035007800404040080782c1025401d03841600c0942081e121052100480d0045c112081e80031a04 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 584516267 1250 584515017 584515033
    0xf02010501080c010809030c030408031e07020d02040504170c01020d140c070b1509040f0209060102071410200a02031509030415020307050a0c1503140403030c0210020403050106030b0108 82
    0xb034195920801e901250420110002003022031034180300301e40410000f101502da985403034880807a9a42e0260010824141c003215200816507840010f44e01c09541c014140303070b285c001a40801020f02406441a2064917a002c03e28030850048001030250301001c4c000940c80b1444071101c80300f102d18041032000109288410003840c0e8505404407400c040c0e021030b10014945848210190810032030100c035811000340310603c8248190841111100c5200310354a0350b11b55986001241c880c1c0c810720071000102ca0560071f40c1d480d4640174462000141042c941140100c810503c3c01c40310302c5100d058400560000310306030096050070f02003410724800c005103100c6541000c4018550707a22842c80b07101460350307202c650b404000e4401c2c01140d40180c4c019003150504100344c1082c1165050902c21052082c04050302280c505000f8051251010440040501a591075403000d4028004c2c1401c018114080d5040d004503020051020704082d60003600000f40c40360840c0b4150400b0b24040c0c001303030400e51181c60 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 584517517 1250 584516267 584516279
    0xa0c0e03010b1f090e01080a20010c080903120409050402120d0e0f0406080a030201140a06031703060303120103050105040512070213090c1814130807061e05090d0f02010501 76
    0x2405180301c00c0c80e24502e0320081d40d0804031105002500248100c140c0c1c17600000f80d5038400105145031a020303610084074031800c1055007d44100c140d5521f40411110f104c2040400d8210015010180028042e25224124460407040702ea0050b00012012980c850a110540c00e0500480d1889111031008140003072003010051b00c00500e102e00d480c03052142003da40c42c1071b100e64014800070f0018104480f1020044d140280c080c00b0420407a0003900e40e0100015040705490065208a9400114240305102c6c2d000c91a99942e100401d03032a014401084012a00f8694900e8140214040da00015807802d2901c4c1c0b071410101c081446c0c588592051107a80d01594484c000299203c000b228005031021440c9801c0710050600d030b208107603040540e00034030010161500889010716001c0c0031510603a489080c8080c15407845000944819418408503000585030750290200c00180e00328603031480004900310080e036500300c50010403030b00840021030000e40c110581000d04480350009010341c0d81011 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 584518767 1250 584517517 584517529
    0x608061501020f060408090d080309030d15050a050d05070f180b090c031305100c030b0a051206010e070509060a0504140a081b0f1009081903210f050a0c0e03010b 71
    0x604060081b100010328054123507660b214500c00c207640240c4a64903460709240c0c0036221b410024020021908100741e081100b000524440241c440c02001c1100e43c1e801d20f414800140030700002243c072481030002c0400c0c4c0d2034010500b40002c040c004504202c950340c400c21002076070601c0903640c1c050820b5209003d11480c229013501e43c058000b920301d400302101801d210349407992030302d418032100d86080603030031203a40c0c5034102c804030301030980e007948480f6612020b01c9180804500d080007035803c202e0060001c031a00c1c9192a030000400d00d0014207181c480790000c1c00d2944603c1880000c0b83c0f00103010003001025640004802c1c800329882081c481c07a0001443e1a055102090640310002c80c00349001c580d1040e0301c3c0101c2410180104400c802111809010300c1a14003418219100e1804130804c0014030441400c0403075855510740c803140c0829111120345c00c07413882e10018121380702c2c1c80f00c0c800d410461181038459490325101082c0e000c090300001d044601c542034003a029074101141c17003031161925 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 584520017 1250 584518767 584518771
    0xf02011103041106130b2d07020103051003121211070c1a07060e03090306011502070e130b09100b030c03030306100507050616030c09060f210608061501020f06 70
    0x203031a030344003c4903d0340080d48901c41c4062aa103680c040e440c01080030b4407400701500381c03005542c00d004001c6072101030b41143c0c048581011201d059041096900551007a0000c0e80c0001c08200d40c04c07140c580325910f08415006041c00304000031170030200c0d4100710f03805001e0b0020100b12412814a005416190112403100a02030000e24400040c0704e40c0c06c0c030b003c081c00c5540306500840c08100b180b0384a0946900c035440024a00e00c2482140e0010441c640d01c0031040b20070070721540042001c2c5203440680c494015000306405500300300350724448041440002c0da18869141072024001140c0441441e2080b520348540941c025400f0740c42213880d58500100f1640c001c030049690100d03503210003c1c11140c0b4880c605008001c2c2c00b17100c1c00d0107280300b144c44014210b40581d8805102801c2e08840488030313406207100e03560021380402c02070704025014a000000c02c40d0351000c00310302e0422240510058982c554041c1d02142c3c000410003240355621180100c14003000d01c050141d9092001d24a65600d0300 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 584521267 1250 584520017 584520023
    0x80a0902100f0210090804031527050c15030402010f09050a14060904020f040e010b1201030201211b020c54061908120705030702090f070f0201110304 66
    0x802c00d180d682180c02009602e00d03580002c034040c4058102c0c0d2600344a960000c0c030048a107141224a0301030700004d64091440c904036110800480380030000c00905500d030f240c01c8255141e0240f60301c20f41e0540c860080e182510590a01c0c200c6d62402c081c800100b1442140d146502001102c18061081d9901c03440000119984585016a44403c0000241e101d01c00c01c05020351091001941c455440b440c0c074060401c0b00c08590141c14940c0c0c0e03480c0e400e2102d20407070f0000a030a241e200014030056024402d41c2640ca4480c419000d481c090141d00340342100e412100450901101c1840c0c2c84165074100300c4421034841c103644507075001d0b0f00e40310200184441c28a0a111812110300003148448240710303002d002c100442c0d66144003800d05101c40320307410003e0320001e001e0b40701080c2d0501c40d05041c01d910000c454900b03000b4107500b403003049880c00725040340c10200d81e1400100800d20140e5500099039009603282050801c0c41e007440c0c0030240165101c02020420b690520710518021413903503003940d0340710760 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 584522517 1250 584521267 584521277
    0x27030613031103041203021203011206050403051b0c1c0c1202011101060f090506030f0d03110d05162c0105090a09020310300f060b06030901090201080a090210 70
    0x5440c041d40d1a00d0642c1c8001550301c404280001c242020007035060300e4074042c1d0261100722190300c11000407841b0900481100800360b0501e6800149998800c0d54414064641036050910307503880d002c424160007020b841300e9480341031540070f00e1034140195101a40f4405110400c00e4050f03544c0c00390800d0741d00c81e214403810b03500110810742e40658500b15002c51910020084141c640200410030b124034040e48003001d207001d0000b8072600700007440000c0803c214008100407421910114040c0401e10f0f00c460083c4014840e003014040c4502500d40a076405007906040032001480c000c0075460201c00c22409842180f480c105665000e504c1070079801c00a1824668450403880420780d844615405110f01074400000c000742c84601a00d608140d8104c06171020198405030340e81c000700481c840e41160881c0f917500640c1e00040101001980040c8201d80c04074031807042800044241d041110400c00903515882035204540c4e010094aa00c0307541034a00308151403080e004248280d076141c00e401c0900c4 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 584523767 1250 584522517 584522551
    0xc0f0c031709011407030903020d050c060f180d0306083315120604110111191a040c06110325060f18050708060106050f0d060b0708270306 61
    0x1080d0404403500ca40341403803111301d05100600074000d109502c4144c0040c0111882c4501e11031142e011140c46d408400000c0c07015444105203140404006000c1c83c0840030b030341c0c5150700303142014450030458000c140c40014805141000c410708010187d480180c4410010704540040402020840850400b5145840c0f803591520101c1c0b80c001e140080c40d5038407019800220003c0c0301c1c000741032440349106011240d40c04d105200196440c0380303102903003071050708070f00500c3e0403e9412010003269a4000d0b0050704901c4451005880580c0040d98140e49442890105102803500402c03000c02c0c820391180103525244405201e449445a4a0810480b00345401030201c01c1c0130541e080400b0024820400300300f82501418444030f40b444130394045800f0700604e4400a1000030100c1e030315048607460740360306280481070380c40b0782c1d1740d03034006030035100340382c4d43da5002007008000745026109640c030911400e550340d080215000d1040e00c103000300e007010894200041c0c2450300d000c41d141e50030480d0301c00b070241c8903 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 584525017 1250 584523767 584523781
    0x10c140a02011415130516210504110a0b160201050f0c0d020106050102010c0e0913050a060501141302160201110102210a151a1315030c0f0c0317 64
    0x90300380d40c03c46041401a44052091441415801440a4100b01e1310100740211804280050300d1044800720788411840ca0f50802c441e008003e4040748a12540d00c080282980c9190300d001c5413002c0d1010390390310b24072074001c04050074401100d1024000322041c003420820401d0fa41d000302c05035260001e0411001050801900d58407c0581703402001c0c680c1511707a05010064000e00908140c810b69005609000050004a000b2083c81c43d8500025207440c0165032110b400c20b01c4101100320803900c0d48214906070011038910320074103000e001001000d403843c01000041262a0180554850382c0c0c17441000a6080f0348454204510a01d40c2030810f0014034001e13411042c020300608144d01c61032001000034000c43c411540c04203116126418042000d42d980990700d0741b03240716500481c6046980a40410084800d80c400b0b00480348a810300b8546468480c0302c0f00000c1e04a403041c035804030b501e1ba9501070307013140c001c003625490741a176240c1000781342415100240301c120301e42c600c00c0d0240c00c000003003004 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 584526267 1250 584525017 584525021
    0x2060f0a1508010c030e01180b010b0c03191d040203010e0f040201050409091a011203020613061b0503041a06010c300504090501140907030b0f12030705010e010c140a0201 75
    0x280002c0000b0410040d203220b0260244c540740324040c466501e0000b07200c6641c0012216080d0054005d00020b00390303824240c0380346050340300600150702440184900305070180000c030711044c406403070703900c14030501030b6202e0754405400c120003001d100754014401446101c901524039a4050400a054002526a400166610710464010041c1c0713500701900c00e410701c10501c4046c5442e103004906885d142e13a039003c0424180d414440000c0c010780020000c1401404503000c041c084034000e02001802a0314240b0440c010180c039485407010800100811003446150417940700c03150100e5003410440d140c0400001c294090524008180c01816070004400704212811109284082e02c0105100d81200ea009030a580241c81000c04460400c800880c14260b50018610108000381a10800b038441803401d401418a000031550480d01d80500a80b26a40d4010101c400092020180d0381d04c58941c01c2c2a82034800030b110040c441c2e810149034500c3c6070390040ca44141103082c03050f0291070700820001240 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 584527517 1250 584526267 584526269
    0xa0c020d02120c1c030f39051b0f100201020d0203070207080706090605040b0705010f09111014160309090c02033411011b0807020a050102060f0a15 65
    0x5001452801d0080502c1d00004540754020000c41d21440303142d905805486600744000e400500003031750340c038010440700c0c051022440c0d00414200c61642106105a540d002c0704201c00010075414500035000041c4041032002c0c101c5021110741c10440c0304103150200d105080300184241c0591188407801a07594800e5068a0590030201e071b06641c1c030b04046800035503a40071030248128501030100300058050040d4070040460b03d580c2c81d01c6d420039140102d5203410f82c11215041c1c071155294450141401020700c91108154424514014514010b805006007401450b1010040c01140b1a881402d1503420040c0d0315444118038401080b54050700d4101c3d01020150301c40310a181c10450382003109034010028002c0051421001903040c110040f00808141e10400c41500c980a12456040400c0118081c0090b0b01818102240c0900c190321241c055020300c1e510640c0e9040300402c42c0802c620345111614000e110900c020000b0741015041b55480c0c6001401d07618149070b460403041c00d401d0440c810704d0 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 584528767 1250 584527517 584527519
    0x8040b161713020a050121091a0702010c08090f07030b090a0f030e01170606070204200424091d07023408120702130f060b040f0501050703050a0c020d02 67
    0x241d10782072658041d6408404000102d03c00c03100804041358039441541074103401c0242459070700c001d948011005000741040c0c5000d403000c040d4000c20b0040703c104480b80600440d503d50000402c112032420082025902400e030103807540145d076164044e11030001c0e80000b0b0b2500704644410980f00c00c0f54079413030109840401041ca0005440d00424180c1044903180c0c2c00b042a02e80f040c01d82c6038502c0014070354104131019903000e0780a2001c41d0140c00d10758010b924050701803000c44070103c449603009155030815406041446484840340680fa0a03182c84509550024180640c01d80e040486902154440000c0c4241d045a84d100094081d407080055444c0190406414844600404d81050442407002454614030b1400350700007924810010b0482c41c481070061816080a0b1250708004d02ea285514100e600242c55841c075001820a0344140c0d0024800d02000595a619101f1604501500d03684440d050000500c80000030a130488122944d00509190201e215910303440007800d60003640c130001e = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 584530017 1250 584528767 584528807
    0xc0607050c0907112a0d0f0308060105070218041b090e0f07080c1e09040f03080612120d0e060a23010501050712050714100b0a050303040911071a04030f08040b16 71
    0x410140301c0d06910b0306206e1f038020303030b5405000c3d6541001543d280c0b1030381400940200300300d211003650b000000040d80d0845d01c207d000038a58519104103500e011011707084840d04540d40c001030003a54000300030015602021101401030589805a2951946070a072400c0740903000c0014500c2c1c0e403400c80b042009044500520501990030305084c64000d40116541c1200881d01c0000403d25030716100c1d01566141011800400c464440020035141580000340101da00c1780e11002011000030b01445040c0c810400c5050000c2d81c000d02c420418055185000e402100102d035000500141c0d900100b01c82070a40c002032440d49411041d4021101481030a101401d420801c6940400b445004252005803980e00b20061102c8003d0f14104521400c0d030b07128142d41079004100402c2a0344c01e541000c002010100300c2c003400c2058a8a460307281100d50500300c41200e100000300800c0540010900d07d04079510302d07207100c00e85020307520086013010245c0010501010070109440c100c1c4602e0450506c002d02c0004 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 584531267 1250 584530017 584530039
    0xa1e05060a020703210e04090b010603110c0a050625050a05090609060d0506040c090b03160903080f04030b011401020d03050621030c060105120601030609050c0607050c0907112a 78
    0x100c49440c0c0464855800041c0340c0303c6d812415403074680150350215400c41142c1181c1d918040050b0014101000c40da51103580500809004a00500c045c0f481c13140074001405061902da168541400c5030700100000d90801541030315080740c3c0c0314080c0d804241d01410704175564544140011450f0081d529500d502481c0000e00c9607403010990412030140506580a000008266500b070381d1008950003005400d1105000007a4030f2600e842c7d03d004404602c3c01c051080e1602c036210612154071078440c2c240c6100000501b001001409540c190050192000d0402401501d00000792036400c0c0c2d203801410161200b003c12600d507500b50f2803807809403401004a5100031030200841d00c0b600040d82e452100d028807400043c40d81071000400603801410800f43c4047c0c0c3c20740d580e14000b011611003d407680c0c0300f50f409800d001d81704d0f000140700c194020740049ca24410000100202c0e2107004181c3c1007000700b001174084940500150429002500d80705818540c40c81d108107041c4041006040e0f503010300c003191 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 584532374 1107 584531267 584531303
    0x2180303160f17220504151203031e0603030801091a0918010f0b031603051b04150603020301030c0b03091b01120504060b0a1e05060a020703 62
    0x89000070602c140e04210300c43e40c01c180300c000c0403104880c0c10519a065007008410080a040f80e06019980708000e06c180c0358a1a071040481a02c56001a9000c250007600b00faa1000d03055240d14a801d00c904c0209409811241f0040d40490058400071070102264003601500b21919107110400740698418018905401021a0100800010a0007800e8003e0150403242902144040b440074020001c0606040b5004030140c1c4503444943c04000007000400d0390310004500c43c0d40080c480400c403021402402c1c95100d101000d113941440401c4141e01540694141c0740a040f0314008140c032482d2038200c62009130b2b440340080e03001052001c0e060100b406c03000041401894260000034031500d0140c1910b009440444115844200106c003904060a000c0b0082421040f181c2c247c1d41c1401c482450400e0320301440d80200400100703c0c00c0d590003000250700840c0d00c00b13844264114244 = true := by decide +kernel

theorem cover : BRFrame.Cov 584352517 584532374 := by
  have h0 := BRFrame.cov_init 584352517
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584352517 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584352517 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584352517 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584352517 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584352517 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584352517 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584352517 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584352517 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584352517 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584352517 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584352517 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584352517 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584352517 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584352517 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584352517 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584352517 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584352517 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584352517 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584352517 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584352517 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584352517 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584352517 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584352517 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584352517 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584352517 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584352517 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584352517 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584352517 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584352517 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584352517 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584352517 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584352517 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584352517 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584352517 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584352517 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584352517 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584352517 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584352517 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584352517 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584352517 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584352517 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584352517 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584352517 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584352517 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584352517 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584352517 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584352517 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584352517 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584352517 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584352517 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584352517 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584352517 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584352517 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584352517 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584352517 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584352517 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584352517 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584352517 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584352517 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584352517 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584352517 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584352517 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584352517 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584352517 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584352517 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584352517 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584352517 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584352517 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584352517 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584352517 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584352517 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584352517 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584352517 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584352517 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584352517 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584352517 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584352517 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584352517 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584352517 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584352517 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584352517 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584352517 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584352517 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584352517 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584352517 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584352517 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584352517 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584352517 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584352517 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584352517 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584352517 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584352517 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584352517 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584352517 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584352517 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584352517 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584352517 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584352517 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584352517 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584352517 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584352517 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584352517 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584352517 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584352517 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584352517 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584352517 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584352517 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584352517 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584352517 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584352517 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584352517 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584352517 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584352517 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584352517 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584352517 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584352517 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584352517 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584352517 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584352517 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584352517 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584352517 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584352517 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584352517 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584352517 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584352517 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584352517 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584352517 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584352517 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584352517 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584352517 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584352517 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584352517 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584352517 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584352517 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584352517 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584352517 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584352517 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584352517 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584352517 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584352517 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584352517 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584352517 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584352517 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584352517 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 584352517 ≤ n) (h2 : n < 584532374) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
