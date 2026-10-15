-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4479
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T12:45:17.529552+00:00
-- url     : https://prove2.me/submissions/67c17754-56d2-44c8-b5c4-c6c34f18989b

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 805395683 ≤ n < 805575539 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 805396933 1250 805395683 805395727
    0x181b030d11031207030f020a0905030d09140d060e03070b0906010e07120b030304051e0a090e06041101020304090614151603050c3409110904020a0c17070b0f060303 72
    0x24002245888503a40d1b400341d80c480c1c0440400324400340002c2201342001c020380c5c40070000911301500c400d400c2003042c1c030b4000a00d000703072031049900860103024885154416080340700944100d81d540d004900d0400d419030000c0381c008400740208000040d0000d18044900d01c00c02c00e561b03070383d01014680c4164800a148010601d80c15200520020541e83c46000202107a8100520458801c5000c1010000a88141e81103181c1d8281072600140c2204030015050741c000ba400344008040c1644000100e1440c05694000309002c2c0c09c040000035056200c07410022015000c1d074a80060b0500d8124001c000d01c00d40d081420101920302e02900824070400c050b0901d141d83d0015206000300f480441003242161060103a40f02010511900e0110010600da400401922a0170301c04d050351103000f09000e02070800310f607000f9600040c214824a2240302d003c252554030190301064441100ba8070300710f540050b03a0888251801d100420001500c4031840c1e03107d10001401549080240071030110003c041c10 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 805398183 1250 805396933 805396937
    0x30f020d080a05150909010f05061516030c0501050106030204170a030f2d02010b031506060f03040206070f050318010822140a05010b13020a1205181b030d11031207 72
    0x92484c4a035541807017072400394041400102e000e409503201c5504640c1c0c05011648261030360650203030280d18480540b0410b59900603101080d400302e00b42910006c0d140c0760020155441c000c000b1403001c3d0150b01030019125413030540c103002142a104295138031200b0742c0181c04200b141d0510f030442403107807400c800e0a81c6903400320481811121f80340b41100e80c1c0c00d402d820250b51240100c11150400700300d1129401c60001c400b038a00e041c61000700c0c485108103040c0100142c00040040c05640b03a02048030319961b03009040400041c168140309840b60081502d90300c000c44e0f0344105400540c0b10310250740c0240140c0c128501100c0e4034850220030361203020000c82d1012111116a403412070140f01200d0b0302402a000440c103981d80d003081040381d42c0408683d05c216131052000800190344400e01c84d4040c81102c1b400a503a448134a06507980841006603610284560003c1c0342444202c03c058003e4084290201d480340c00c40078500703650402d01c40c1c00c1021681d0043c0500810300c620314510ba90004014 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 805399433 1250 805398183 805398211
    0x6030102070506131a0106050f0703030b0303030f1b12061201060f030c0e100e31060b040b030307051002130512061e0910020d020d1404030f020d080a05 67
    0x1d660790302d04103001107805080e00e940c104440400d00c286400e00e600411072240e059840c1d581401f034060b01d14010b030042002510804101c0c441018001d5002210064006044075100d103070106040010400865082c641c000f040251103060041030025140084903a456800c10350703440b14180710070851500f0143d10a513481d52070000307182215003201405540a8004901c1c1c09041441084c1d5203600070700900c0b030000400c0420403520201c01c0d50b068001102c1c200d52144840510b04a44d05089132490700c000c0d0404840d039800400c60aa032220300510301c00e480c14000d140b4060109600c900607124042d00981005a0340d00641c403403540205550a04804119483d617140d9002ca0240036102c413501619501440030311080b800b502c1484c00c0003501740c1080e496607250602d03d10b034a0710450380340a0304403900820060390484981e01511001c000c0c281d070401460b0141c8000e810300c2c0c2e000b81c030160003040341600b8001d0074a1000c50f003903040c0c80700ca0310381900c146c990340400030080c280100418003d006d4 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 805400683 1250 805399433 805399447
    0x1120f0b1005310608041a0705130512150c070b0a0c020f060415020a020c0409080901230702150705010c0207090e0601030c14030304031a10090b1806030102 69
    0x11800c80300c03407149065a866072204000002080c000440c040441c00320603842e50320607811402e450000c0300351881890a102c00e41c0703070b916000400503050300c0d07000b2200408008009241d603100028004840045109602c120360311000d0107040c8030f0315100b03011582c01900e401192501e030100415003200041aa583c40d02e152911a52444482035621194041d264895490f110307a041000040004603000500150704165850781c4210380e81e101c035480c200342c0104840121a0080c40030141d220340140c0107000903449860302802641c49001d1050200b0094a0101130301d2070340750f1140541500f09000d85103032601c0c980800c64000c02c100201180701d981002440e000400c02c0c000e50b160b01e40642c009100781c40c28500c141059411034001661194403002c0100301041d001c52122041300d18070261603001c103109001180c01e40c440c6410150828000070708007001103044801c401e110b030b01c00c1c00c040501ea0381ca811812040e9480710220f01d0f8840802c60700d00d08203655014045400200c020001803601807 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 805401933 1250 805400683 805400689
    0x708090d17040e0105040b03191b12050607111908071103160f171b01020703050609030a031427010612051f0e0d0c052407030606020c01120f0b 63
    0x44030f5040a40b11010102c010441410700f0f024000018008030054044400d0180c3c40340030300d40030008050603850189002d4540c02045800c40c1c4041c0420089a540c060791074103119640c0c85050700c0c454001079078031040500840c404101d41c50f45011483c1c1c980b5514030b058030341a0554200c410705503214040e01417a2805a5030410800c00480102c0c64000380c41450f1101154068503240d00044800c0c3c00840000701c1042c0c041002c02c0d00c14403080c00c1091400213140102c3c80c2014a400052086c826503007400300701400040035001c1049a07580601c4651200d45003031141100c00e60340408020321111441d40340080c2040c6404602c8680800010059603400e00e43d000e03107100603c2502c2980050b000108050f003058100c0345c95036000f201c28810302c504051130b0b40d0b507880c9109e4107800308070140d65110101f0105014440740034207a607a004d103121481003e0250500c2d0180c0780d88010074500f880001310240081450800c43c44161a80d4101181c85807000010f4000c6510690301240d9958529003641c0d = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 805403183 1250 805401933 805401937
    0x3080402061c1a060c0c12010f06030302030c0607021b0907020c1309110a140d050c030303040b0f1308041e1d06091e041707020904030305100b0708090d17 68
    0x181000700400d1615403c1d582421203030300489604d02980c810059a82000310004003c0003581e070942e008004400c954134800c2c010724034030310604282070421000005040c0c3c0040501b83e6048100c00760780c25034465410036660b81410480502d032055801440880307a2800c1c49242d0b034031000764010384400b260f19000045940d040c1c2e201e500143d075501c0104900740720b00c0d403000b4000050182c2c0e02100090070300e0a00011446840f40c2075115042103c144002c02c0401e00c40d85040e190094200c176200d041c185065058124100d80003551b044041c4002140b60202c0c030701041800360005c120a10b401c1c1000d4090643e58100445001101c5506400084055001c2a000f940c620320010184043c140001008a00c031406042040850200300003d040240701801d001e8000e40e0100b00e11540004d002550100c5000b81d140180d0f00400e810204410b058044d00300768401c1d80210604021f80d916481490b041e80240720024020b4042800081002d0600c0c0c0c1480d41752a01505515034030604120794407500b6 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 805404433 1250 805403183 805403227
    0x90e06060712110708010b06030a090f0605011d06030309102f0102070c0e070f08060d0b040c030b090313031b030f110f011d010f092102120105060109030308040206 72
    0x1080082c045000741c4084c44000003a084d0407000b0320000c820030340003404601001d48512541c40e03441c00c1c0c3e4010086d103605509145940150140484d40c1c0d0b420b4010941a04810034000ea19005c2c800110645130100488884450060815001000507841120078481180c2d5442c141c01c1895091150100701503080001c1048031800035030382d00c219140100b0182856400b5295152001c024841040e07044003070055458803610317100000e0b030b4401000940e00c440c60b25000d402c0010090030700060000d4100140d040c3d900480b000801c07500e4280306c05607641710700f0b10b101000d240300d840140001500e52410081c5440601182c07000140c80c0c0e284d540e0010759900b011200c01c4265000303e641030034001d5a020000f0000d007040c200300020316a14122101403a00e806041008418400d442c00f4040c00880c03001d032096540a0300d041c80d080c1082241c1c1d03041110164072581c2c0302c4404402c8003405000d09841520180d40302c02e4038502d959015200048081c104a038008414086103494902031400c02c100d03 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 805405683 1250 805404433 805404437
    0x6040503030d09020f0306010e0c1c051618060c0f020a170604060b030601060c11030a060e010614090c070201110f011406010e18060d0203010f060f1d07090e06060712 73
    0x980851040000c01c0c5c15181703400d400b9811200042040c01d11032100030307900c6081126070076a41d00c08a103803015001c003032011104511340b801050041c1080d1107400035240040b2912000c1d00c08210211070120340080b0306c18400007039074555491002641c0440c07030266052000c1d01b18241c060301e9400103445190fa0007030202e0250702020801c414000c141c080d40c0160070040c0c0107042c0310b50400b00000e040a184403009004017043d5101d01015840400403203010f40d40004042003000b903d8000c1c64083c0a19101d90a040c403c1c0310704505040c42d0414141e40104203240050f841d00380076500641d138010f10400301144900500c60003600c4203000380280100c0d81060503000c24285403c0c1d001412074401c00d80c0b5507004102c1000a90a4126104076241d00807e0480e25101140000d1000074050070a114015901a06118001904103000e40c401d9041d43c1c0c03e04213080a4008041c1100000740c4200e840320005020600300b04062b81e10101500d40120014241d00e250070b255443d0316640d40d00744408600 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 805406933 1250 805405683 805405691
    0x106051b0d21020316030b03160e19021903051f2421050c09040e0f06070f1413150207080d031a06030901090b07030222050102031806040503030d 64
    0x800300902c00b12100e42c0c082c1240860550803c042e82d0214080706401010a05030341e0580c121041e50104026503442c1f40383c6e040d8030402510345d682c10341d200400340c60f506030351030480701c050928509a00a5a5500c01442001018200000b03011806048064101950080000c64a042250001c030348600541220810000c020741d21040e0400f074a82500c0602080040c0aa00c40704e88009005815001e64003519010416842d160000d81040c890500c0c6203a2191402e4090b480444003c070f458a4100014130686109131703215034003600c1500d4118800c10009450094000707801d0070f102c010300b15071560240300c2108140c0300c0584502d8003642c88540700c0580d00542d0100030640080200c0000c840302843c0500000c0c0000000d04001c07018011204e1095101100182d040c0700c09500001d420340c0c1003d0400c3c1d4a05006030007400942c000200d0803114411007880c1d1046820310700c6442c0c00c50714180c1c000e40c83c100d02202c68040259121481e154004810040003d255130104007030700141c0304030b0000007 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 805408183 1250 805406933 805406957
    0x5090a200301060f020606220e010219020601030b070f050a030f09060c030e1209131e090b01030b090a0b01150c0b07030f0b030a0c0e040516151808060106051b0d 71
    0x7914200c0000c10b403500c1006d065651001443d03164500d42c23002c6501150111368065682c0115008e401042c24031031200d41038480d040421640080d000c0d04903406445401030a1b01c450404813000d80b4100c4a0401251040080c000c05500c40e030701c070304141508454001034007581c2e035503140e05980e941c00040c40065141c0c1e2910707030007180610402152610b02c08480d840d1001c3c00020402014a1483e20b44a05aa4242c0d80d1400a804074207180c82c00451001000034181526050b80803403030038001070394070f0b8003070360001160460b0010b54009256080f14800495a1801c0e49030301d8401c0b40800c004040005294103880000d4030500454005d441c15103010815028518807a0b080f03508400d4914802e43c020310100340420b11070501001680e60303002614290347d5450a190b4601214081140d4048400c0440003400702c02c0400050005001c2d81c2da94060340c180007410a00c0c254680c01640120b070040c10040033130a00460052076140034820045150340c035600407285c20186030b9100c42d400300329812189 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 805409433 1250 805408183 805408187
    0x8160b0a0203070f090f180b0d060c122a0e0d0c1406071203180f0809150702031b0103060f090c030b10020703021c050a060b031605090a200301060f 65
    0x410384d0550520784060403a203070003418528a011445a6080440c6c3c0e09002d03100450103810580c2c40f40b81c0584030815201240c94140020b0202e0010007001400d2041e1903100d640590140c00320451480481610001c403111704509000c540e0b010040034026540e0386203e46803103181805900314040c121f03d4520910308021203181000700c0240740d00c1200b040004000141248114201c032075a0703450005030b030441d104030300d030109000c02c10094840c44120b07045004121102005100c60380c0d040c1c405401102d10000500301601800303100070b6054006031641394081581480c0003084400501d0301103810740e0349050000040b507441c1c001c2d50030702c1c2d00da03a6480041d90b054022001c08050a81e2490905044040029190f04080c0030080c85107210000c408240400004101d1405070820181d07480f268440c038042c4004c20b01c07441f05502a0044041514120042c2040201103800152101a0550b80c1c10300500c0101856140d901c0b140c42c0c1210b010501d1900900554042c0109842e2000c0c1c8100200d00 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 805410683 1250 805409433 805409447
    0x1412010e0703120f0c060c05040302030709020d18050c0f062205100c03020607050306042703080604230a0905010e03120115051804090b0a0618060303080408160b0a020307 75
    0x46014410a01c00079240c044d80401145c00845e0403080000307104030f05000441e141d110302e50010350b040c442c5d10404100d081840e80200405845aa010480d0100b6a052510b40c80402d074000382803a00140841841428030910f401151000101502e10b00090b80c4c035601604d1150700300851000000c0e403401e0010b41400c2c840b9100003a41e904105030481c20039a8006d603039501c02091102008008030203e20240c60315000481e6241d00e05000d6400c0a0b1980d014074800c201c0014207400152140010070903504080c4100d02c080c102800b1886110201e03031241c0d4441c0300c800b0b0300e0180072680e200c546c040443d200f031140f00ea407426a000070b1039448034094004005c2140c1a0041a4032490070700842c074000b81c02000300c94151884000c84503041954100081c002d0100c80006000d18035110208441c449003584203409076002c2d0410b00c070b0903180040d103031011240c83e800b005010521a4000c100483c0d402005015042210540144c0c449101c1c0d4417503c0c5d6042c280d8010222603004018009030a800c014 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 805411933 1250 805410683 805410713
    0x8060108010b060403021909020d0209090a061a0f071b15020f0c121014310201050c12040603090308070e0307051e03061807080a0c1412010e0703 64
    0x4000c0c01000c014030b002a80360b00c141d01c80241704880444e820304158124291400052166a00c115103d55000c02074034082d40c040c038026807040564600040c08a40c0301c0c4038071401d880444903800700040000070f15601d0303a4041007a009120328103201c42c2000030220311500021944155201030300c0c0c0d1030b088050320140d01c0c1804e0001036421210140d054040000b40f003002e1400d04662120214146100c16824440300c46044035410b428850000c1d186078181c00c002d400740021000407001c4105414204200d40c11102040ca0000c1000003944007640c880d40180031103150942c183d0701075000104038080c3c141d1280d84541d000c1b0b81c80308490f80a154005024070350116039414500075060104c00041d0f21024507002e224410740000b040200403a00b107160400d260f20b0090100c0d0032500b8841058007540610783e4410300181710b41480842c8144012441104890380700841124943c100000d038201c040745001c0d255003220301030312082c00000c4240030711f898502c1c00e08098002142107003030403901c1c0c0031101 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 805413183 1250 805411933 805411949
    0x60603110c120901030b0d050a050c060a05030c2215030b0d260c0d080109060f12030e0303090d1515180b240c1501030809130f050a0204080601 63
    0x402a0040c1c0d10000c51201e01220000a005079902c0701140142c008052100c0429004400c003018901042000602c4c8006103000d01304507907650305941c0401243d442410142d0b0b001400c00e1020a10841c0e0742006411510031491130340035419150040f400e81c0c610140c1c000a00740c2c2105140c0b070074594041c400c100c0c0703000342031b540d116904581e62100e0b902c41000860303d49900c82841280504411001e05503108020340c0c80c00d969445110400050440c2420300405040350300c0c100c1d0006404075001c0380d20301240c6000185038580d10700340e102544c001c1220401d440c0c06000400034002e440d41c90019102e0b40620490b9032810360009080e15134112100c0101d189081092500144400c01c80b072943d28616000e207040200c1d07070140180c0814803240c0d502226280200c101401c4401800318a40902044e403880c0341220031780001c0d040064074424081c400035150b40c40c10003141205081c09090015644134a00c8080342148000b903c441c00c0b550102c0311000702c690301060911403000c00380112070040c2418 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 805414433 1250 805413183 805413187
    0x403050d05011202100f11030d06140d030212210a020304050f0601080c120c04060308070203280b091e0c030f0a0b06040902011e0c06110703170604110c0106060311 72
    0x20380d004c00d49117003d48044d03000784503d4000c80e2642c2c038032442021503000c1c110810760740c0f1650307076102003405403100e8094200310703550181d40c0500c00c1c1846410380c01c00c150554024444a00741c200600c2441d40410b29000c8208811014801900724103004240211000b280040e40c0f8901410101c3c2009004400e41c1c0a0380c120703500410007500300042e41e03103407030508448411324000000202c0d0b260213540051184c025080002c000b040c4580b0700d010b861010300a4003903500a034070700d0117400d0120101005a41501d40381d00d28401c08100c1c00c0002542c840440821070300b20a8419a56a080c100c012510700040e81c03040300d00c03244a0034140009448940707800000c5c5503000d900d60f1500d440d403c0c010310650145680d03445040c29603220b20b005070385d44c0d090384401d040f10300c5d680a001403480007a1381c4241da469040410400c52000c45c0012203004540590324524590114090503420841c064201c691003074854550200e0041404000d0503010345141c00001c182e4600f41024085e5000c00da0640040d10003 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 805415683 1250 805414433 805414469
    0x1507080c0315040b04020d05090c1207080d0e040b030a050c0310140c090303120f0105032103180c0a0f09140105010f0c08130312031b020c0411120403050d0501 70
    0xc0c03000c40496014080f07501240d003010710000f24009000d409913032040da40c10310060100c101004a4030800c1800300351402c110742c02500e0501c503a540e4543c03140507e00c0d071101c6d0310314040703a10600d45a940c414000740086480c2010500107458452071140a41e52600015a1040c0c64601080f04107a402202034040c07082d00c0110420300e001da90024044844990001070f0350030781e130741e0503c111000c01040284004003030501111040c0385c0d10003409198000d1240382c00944c1d810822140f1402030302e8106101d145180c0e9100c0e004100c80300c24040c4980e051003103403180051035450f100603c000c0d2410080c285000c40c45c4c10200800d559581032004500e820711001405180d902425051300801030f41040040b0a8170342c40d12030600d02c211402d001c0000103038080403003000079064800c920030180d56004d00c014501d4034051400e0089030074412002da2701110088866041c580c120003982e042c2880c0f03a9082001e0240340550001048504900080d00013800c1c8410174002d120701e03405418903503850084449 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 805416933 1250 805415683 805415701
    0x30115060c030804020406080601060504081002130b092d09010f03050a0f14160311220e030903010e0a0c080a0302031c2a03110f0d1d1507080c03 64
    0x61400010b0200300c1c0d481c00050554035590000001441582c080310324641c0d40e0f10005007203070414000c01c0038900680d11000c0ca545140c0c001d45504035024940c1c505d034280fa10301d10900d20ba015001250b04405502040743c9a005c111448040021590009190b00034410040109014050300b08480110094106002040e000101800c8940e8015603510340c82001d41400c100000320303006e89040714481e0b0340e0345040023521400d052003107a01c102c2101410303e896004010000c0c0b410740100900140780b11000c0229038181e0414a00c6003501000d0b20314040d20980483d00392444100301d03808550244103140104161041000300401146000e05442e40c5941d40083d01c910800721714105148440450b20081c1e6025449481c6590702c4807480c48912400c0e4402c200c20740d6160000e180440d140040d0740b0455401c0f0000c4505400c25008018038000002c2c00070401001c07194035041c0301703e61160307070310346074410030030074500c0b84034100095010500e044000104000c000600c0d0414410003481072019044d = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 805418183 1250 805416933 805416947
    0x10e090906070c0f060905030405010801091b0e060d1104050a0e0114091521010c05070507050d0503040f030803010806010b0711090c0d0c0504150f210f0e01050603011506 75
    0x140385400c043c3ca20742c1d4100130b143c2059099015007414500304900c800c001c4e001004000700c0c1c200303072200c03103643c0c0c1d0780d8084200721501403a41d0185140204005a0024400d4034000311001c40108840d0400304e4680d80c8030100c0b417040c2d0102d500c0e182d00060600c0640b0b8241c0100d4018500c0d50b200b01c81035814a004030b5401a01d100c9414061007030070380803442095210b6011401d03814041c2460740c600311080c0045c1e00c01e0000600c2c10145501e040c6240040070b1054003141c800540040040100c14942000e000003501500341c2912540030a0201146048075181083c00540c000c002507a165418402d5103401c140040e80704140000042018500250308a07042401450044515030641d9440c41010b02c1c9034842e000e040c1000f2890b0803408030f8442d0304003002d0000c0d1090340c510301d0003505006406a0320744100b5409000804e1141801107600e0f0349000588442280102c408182e5440d6107a445007590b45020014603565141c3c0c1c02c1040508003445154000700b0140204100340789400ca000e0007407 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 805419433 1250 805418183 805418191
    0x1502130b07020d02150d0b0f061c02040801051611060f0606160503030a020406030509060f0f0718030c0315050f01050607060b0d030c0c0b040f06050901020c090703020405010e090906 80
    0x2035501003111019507a5840412214640240c248003000e8107041c08078815a20811010703014605d890913030455820f06004040c4a01ca0241c140751030311150302981071681070004400300e4955000c01c00030401560a00a4500070a1040c44020701056120b201804250b50444800c2099110780304114084c804008816040308054900a03590340051005000300d08481c04040d242c0c0c0300020600c652130740310b6401041101c1c07050b5020045512100007031525800c05031461034064030705102184102440c0c841d01600002c590400042a154107014150a1240c80d0300c25a172503800040100240b000c1c040c1c0051800d61205001c106034902040015044541805170f54040d41002c1260410001c203a400401c020500400c1c4480c0302119180040400a01050442da10a07003184002060030240301030f01c054840d56007041d000c080c208007045855800c001600c504500c11102002d6050325148a0070f4010203003036801598890030300d80050040c0391041c3d40140294411804c000d00481d01103001508 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 805420683 1250 805419433 805419449
    0x80a0c020616030b0301140109060b160b0907240f1b0b06030a0f050c1f021c0e060a0206090d020a03090b1608030702060105101b110109081207150213 66
    0x70034485003000320002c1240c1c1212540642c41d0042d050f00c991f1742e04c00c000c0d0403549102014088151104202341d564000e0380c0424405540040003000002c1520885a5124081604440304541d40b520710b60340c1d04489140a04004c501824030314090ba038403010b00404c2a22606080485100400501000d411600c2d0003501409080c00460b03450b80d002d00101c00c00e55080b404010074429141840354070b071341c52020345520405560381941c00b84000d0180403c811000c42c0c0141c400000483c14545071030302c0c00c2151000b040b12030901e02d0504c0e074560002d460501002d83c02440c141c60440d42c0e2500d881c1000d02007005660080144000103035110300c0d004103440f5075584194681d002d20900341c004c150401c01c0140301c0c04000c000c200c0038560024450341250812200718040040e50002600c0b140c500c00a01503201000d5400940400c048080181001d42d040c0b5200c2001940c5050050400c6001e110402114400152000a102a221800108050340c5204515080d401d07240c8014002141c030603000 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 805421933 1250 805420683 805420711
    0x50913140f101505220803041409131703060102010207020d200a0b0a03020d060503011b0e06120103030509010c0c140310051006080a0b04020d0501060305100b1c020c07060807080a0c0206 82
    0x17624503041031400740100540000c4903203464407000481400c400342a0464010814040000d1006540344440102503030401040080c0c400070301001c03030203548014942419503408100000c0142c8501d5040b00c4624060814400300040450800320518160501c40f4400e801414051289a841d541100e400080c0c3d400c006944440e0403040102511403076100540c107518161040e201c04035040d206118100c01d9030b5070780581d034080e0300401c401401400c540c0400e20244400500002c2d024500600503840305040078098103d003960b8203280c000417030304101051001c0c00c280000904081000c02c803945110081403205142902448000c0d980d00c2c800d400400c0203c0c000b2038808555036000000401002d0030541d6150024480304002e040c0a108200010b4a4580001c18101990514200b50350403401034619228202800d0300320400340081d40d03038581c0d0b4208201842003208010100090505456001480c0340c030b00806001010010180380e0b05500b04826415126404601d1542c00302801e00700c12 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 805423183 1250 805421933 805421977
    0x81902070308250215040303090b03011503110d05010906140618040902180703060e06040b180c0c1f0c080f1303031e0504020406060c03050913140f101505 68
    0x341400721000020350003d0014410326a1902800003c00687e802911105262560b981d0402c40704c0c48240708003003080c0002640384108620980103035010b4452038000605081520f07034064122042a880158602d945410410405240305114030f101c900841d07040d800c190740c50a903c28581c00c12031400c2d2007542d9a1500004540d2000f40e1a030780d010380da4521454a24045d240500242054001d81200f01d80c01c4000640914040c060400740c0760340070700710081503280b4504416103c8006001d160b00c090051203128140c813020041c581071000c035082901c1d00c1c0740101c60340804840c2801c901c0030400803d982040788410900700102d40100303e404442c0d881905174207003100106864414a4184819051248071015a80d000347e4091070003140c0410445640f40026140360701911001408110140405101d625185000b861400c00718000422074901c07550844224100031182140f0300f040c00c105103e0044000040c40010b0030600c2446440206802c001400324000c1200380301160705c00c0313142c40c = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 805424433 1250 805423183 805423237
    0x1611060408060403080103021903050a03140913021e0c0a030f02010f1a010906021b0d0611030108030a080f0705070f060f1505011202040b0306060a0912081902070308 73
    0x12401080789505881c0281050319005140e54821320099114410300384c604401d40c02d106480f07a007100c0d0302800920803801c0700d640645481e40c0229807600042010300c001d4401d6100d041d9180d4186120890040e84c0d603000c0c40343e100c842c1c807180510082200060018628000002030000702807905404c140c6108a42000e0480c0501f80d40c1c42010b000320308003006c51b49850703204d031100002c3c020240c8407610b840c1e441c0c400881e0740e90061941100c0902450032402c407142400c800d4030032002d008804c0850181c40090140809034020f80c09440c5950002a04401c560b501c83c88541d0042036061040f082d0b03040c8208001d09600541e00c029040401c45c84040081202c107a00c509101010301c20140010340e0881d400008040d090b11926000c0380102c02010704d9902c0c20320882e41902c01c01e0b036460381561901c20621907660040d407400800d10001d5080801d000040300509416188281e040302d03902c104201d541ca0320b0150100b14441554000001440050120000c0d1162104001410104001e0701c01030 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 805425683 1250 805424433 805424437
    0x5060109051e3f190203070806010f1505040e06010818010603060501080f0115033302131e0308030915010e09010c0f020705060f091003060e070302161106 68
    0x42d9a4000c40d0303250100e160542c401820388422040d0b50060b40000000065407018050410640003140c0102d10307000320104503a510111241c3c0003804a42140f41c4803450146444030a030440840340e40500c0e0100010b941648181d04041d000d4a4100e003028a0078020030084180a04182d051049040001d4421a00c0381030b40388040b40e90b20024000e040d5241400001400c00b8000d480c07041c040c0407004061070405003e51390340c403044620744502440c51910394488040e148004000c200214944460700301c03100098409908648000060b662580d42c065011260345582c0b04001100c401044046080380001d914411aa08440b14903601d0b640c26420600b051f00c0c2ca480e00c01c48030f031020000b0608440000f601445100d204000300082d185901d0141c5030f1850111910b40103030f10011040c003040c10184c0161200ca00b00c0d000d014240800c1d0000280d00d50800d281c0080000c1c1d0318501000755640c0918100d4000189007021440d1840441c4c0c18000d0f4501803802030284c07646048030920030344840c01 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 805426933 1250 805425683 805425739
    0x506131a0c241503031603020f07331b03020c0a0b070b0c0909150105210906181207050703060c1707090b0a08041a0a060f090506010905 60
    0x4240c80e001159185000304a61001c081c0d8520b42c444800040c5a02d04107840f1003540700c0c80140118100014000c50b10305020240303030200e0850180000c0d543c84070004014440240048071400312128802000f030200c20b6528000035401c0e42110380400c980b068210416501d102000302d080d00009401d41000c3c1e2501820404464010a482c02e0003d640d60901c00030f0040c241c4904955425a02e07062459581d9014504a141c1d2029090000c200a00329412008144c040107062035814101002c86805480202148a2100e105000200a441c000500405034003184074102000000e00d24085c59654080d504107040c840c21000884d0418400104070010085501540a1003c4410420001c00c01c8000307003d41201101c200000c038007224090044102650740a900480c10f06481c0c1d401200d401d0009030080e41c1c3c081010142d40f111070100c1c1c502c507100703150351100401e40c1407a00402d4211090142d003c4070095103030400b44081d50386e204198104840f81122100c9600d2100b003103620b44000951 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 805428183 1250 805426933 805426957
    0x10c0303051003080d020904060902040608280908090f030622061d0c0a0605030103052814010e2a090403090e040f0c09050f010905150414100506131a 66
    0x41017180e99406960000e118002068805115655494130110164001ca000703080c0460112300c00076503410b815070100601c500000d542c1034480c4070110342d0352086903034080043d01c4181c400140030b1004d0803c0300440d40e42e000e05070010031031440c0c565a00040e100e00071540c43c01e1304000420b24010f00215170852140303060128130039881c1c581b1001100395907506000d003c0d40224180c100001d00320b40200c003941d0490f500140503145501d101c3c01020f40d10b460420a200841d40c80b00329003070101e0000c44c170444914891900028190a143d1805482d143d450b0f551952640603100c02140840d4500b114080c0b411419103038007210f134513685800e440001c103d4005100c02c2c1c80f00c8040205100540c00d880f2202c6015401407100245c0b03904101d01550821a2031044101d00c0c030004001d15003c55100c10307400b03c0707103500701c035a1040b29000140039a40412016069600705200f40541c103d0180851001040115144c07403400c400e1240500201080d0304ca81e1803480c600c07031911000078542d00304452001030780d2 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 805429433 1250 805428183 805428187
    0x323030f0f0a1d0a0b131a0711101d030f090906030c1c0c1d0411041b0c020a050409021c020d0c030302010e0f0303071413050a0b190806010c030305100308 68
    0x104903e955030003010702c00b500c1800c1c5071000f2504892a0801102c40142c0024a4090082c00c0300103500400c14081d110000b0010080741070142c2d84400e012274144450701c1074001c211180321084020940c8443d100f504803e400400041201d001c070b9a00301e4005030f00640da07a0303205664400001e0b082900b8440300035001032040281e02c0d00031143d10280c04450b840354800400042c0c49a1403600200c00a038545c10b154900b100105010402c0d00c0c07103a1740003800080010410072035880c02c3d501080302240c20311002c030320050a008110300d0158050006000301b03480400105c131070781e00010440003034030756012400070709d24102500b591501001424034540080d8410440d41d503a140c001c1c005c010040c1c0c0c42c01280910302c4180303200b00010040300d005035096030ba0182d0b040083d5441d030540d580405d4510103801100d21000880e91508003040004119450319591543d40c44060144069045001103080046000c1003090980c2c011100781c0100740c00d840d00040558171805a5905505242c001030010100 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 805430683 1250 805429433 805429481
    0xe03091e12060106120510170a050304080d030e061e04050703051c030506010809060601030f0b04050c040f0602071d0702011d0105010812040b04031205040902070323030f0f0a 77
    0x80042c54604841882d5a003e003040c0c4244150380840da0142e548500300d4120030b00410000c1ca200400d04900c481302c4d02507031030000481e91000d1555006030b00240c09500f02c204030000c1d0030f4042c07050602e440070517805820680351050043c504180148404c54603850000089414050108840800b4582c8030080303504411880051810f070500c6001c104000030705040001383c0c0f5510848400d40540700340f800038500b507169000150090000c540034468001d030b03a01c40388a4242e844d8091503000d24141030714a5901c0782030041401c81c00b04039402c407100f0340d80645400c01803000105010000d40601d0f5947c40060f484410089000d04400c88503094808a01c01c200f101ca0303003042d488a812500c01c1d208803020841000b100d0300250096124942c0c4404081c40100041010840d040004070b065240182c986600d403d0078600301d0b000b0540940c000744100250010301651421000b00840e05c00d003000d81985450948a01032081c0107102482c400382c2000440e05012131600318a24203400d280c4c0d1080c11740340e = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 805431933 1250 805430683 805430719
    0xb0f0703120f053c0c1e03040b01291608030411100e0105030c070c030209070c0c05010c020f010c030201021b06160302070f0b060307050a180605040e03091e 69
    0xa0704c0704038120340305418400c0b80c84408500b42c064101e200c12044144030100040e0500c083e070080c8404241c4000700b2101003520890340b21901800e0a0301c03006500d80c00d00e801c115102000503000300c41125051052806034000e100d95603807008070015506c03545e40c80d03210714001c1c14807461b84005229a801006020400411032030954800c1c7c0305941200c1c1c0d00d02a03401c11240081322503401401305400308003091000043d20300916415004413000c0000302e581c0d501041001c601250140000390301c00c9040000c22004600307281c001c2c00c092902d80c400544030740004182c02800c4030414144074210080e4803c060007901130700c041c015540d5012002914203080310352038100407500540c1c440721900234071034054002c1c401c2d507403e1034006600d840500e0084d51040d8500b20050840d503494851154001035940d210000100500320070502c4080c0c03016100340700c0c0241d50b529013200344aa07081144000304140d0000580700d000380d080794442c40b0507441000000d07a075078070900810303000f01081e4500b0101d85 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 805433183 1250 805431933 805431941
    0xb13081c0905010b04150314070e040b0708010915050d031716090b03010303170403020304050411042102011e0c0c0b030403170f040605040206090409030e0f0a0b0f0703120f 76
    0x2a0140c1c009000844d0000d0030402100d085404890f4000100c0c10240301141c034200040804446a5040f2105552a03018421005100322802c071440c8251b01d007000034069008203404c1c01814900b00c1440321814a45483c800c131ba049015050013008500341c0c03030b800d1510840c0c003802e10006500c1c0600490a1944030f4006403601c0d04049004520083d01c0010385000d0441128100c2ea01680d0b946d040600036402c030300762201c002e8416002c501c414000800c0990383ea104154052440d0350440d0303a00e900d480864181d031101100d1009100e46202030b0500543d0304130108040000b0014113215002c100010181c544010214010300341940184000c80d0f1656240e000b140224043d071910645c440078a40c0000c0b0065046644502204c9400b01050001d0410b27000740703801a100510490034454828045000c60f520030b801035000440902d28030300700e41401c80040c480e20b18207840c2c0341c1d80c4508040f04103009100f07206024046003800183c3d03a0526120314404014080303050b90a100c4a030b111000312001e4 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 805434433 1250 805433183 805433201
    0x30c052e1a03030d0902151804060509042409080301080609070812090108060a092903010b0a150c080a0305010e0c0702090402010c060605040207030909050609040b13081c 75
    0x289080c1450604240100d00090341c0c52000380114640022000f0007005041c0d044004c80c4c01003a03611012104c0b04503c0090101440a0303007040a410024100b080281c0300190f02c041d0040c030308517043c4400315036403103100170b0002c1940240f82c00902c5401c03140401088041e002034903210000c0000302d410540450f041b4054842542110150303500d0303684894a4000d10100c0c4141c0310402c05c81401e041d4080c1e1849540088000d0044a507142e454580f0340a4445800b42e4040d4010701e1010300700c00140d00c08080c20710500560003000004541c801040c00c20000d4000c00c0542948081c00940d00c903c038004100362540c0c003407941920f4110400025018010a008a483c4449803800150f048400c0c8c030180d4052070b0f0001c02032840c81d15203400640e11804003038819541151208404112925940000c180d400c3c42643c0b5050211f1800301e82d5001c03a40060510344c03145d11142c0078040804c1942c030441d90440e80010541e0f003180a41c5ca058070b00c600c660465038400710840d680c000c80c180195484901a = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 805435683 1250 805434433 805434523
    0xd020c0c041d03030103033c02010507090501050d02090d30020c18060111010606021536030c24070f02030d09060e0f1e0c03060103030c05 61
    0x41903104802c0c00801c11009502101c05070300c10b10040004c2031040000c4088c61303407460b06149140c40441d18460813603a0b4403e5400c0c103907007080021486258244900e5030b0201603482d10003009802c12000030a20f1040c0300e01103850035008a40310242c0d0303035110410003d0543c0309080e80d42004107241034908201c0001500c41038020032910703100b03000380042800841c04100400c0582814501c02c0e004c2d900845c0608168100b046640011100740c0e000d100b00d0700070b00b606070001e000010a5918070b901e8404010b0124602402c00b1103200c1c40c20300200f00c0482302303c8640705918030302d10b0610001861400f07110880d144900c9283d0645001c54403803a86086503403801015280c690f903a007041035a19152403000d0400603402001038a540401c00d900582403244145804a09100b01072661480c1c03050401084d03519412810907455a413034080380c000c0c400c015203006000009098000030b40c4034101480091300348840d03098924100301040c00413041c60100028041c0304400042c12442a0545810000304 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 805436933 1250 805435683 805435691
    0x50717010609030f03051b0f0f250306020c030f1206101e030c050708040b03060307080f0706210504031710140d05030f03090f15071d060d020c0c04 65
    0x1034207a12502040d01581e03000701c41d50032408101da81c01c42c0c60b54800d040030b0f105290741c0d440060b010803007440383c3e0b0049002d64004003403142da04c450b15414950b00250601c1c80340182c1004501c0a2501055002240c0d0030420044c1c540c4030aa9050703042d0312852041001d410400180d408541400d8000140035903c1640d004a0401004800703640450494608601e40b820a20381c03003407102e200b80c10500c040031481c64414188011551008096001500098415a000300c20010301d801c0800c040b400400380100200050524000790a03113030b480c94080c1904020791900c001801c1c1500a03040000700500e03410030042da00d01410001e180e41c000040b50405080e003180031078401d828190102058a04103000000d10301042010404010f0361480b048503580030600980701960828000385110759501405406400f5492901c41d040411350a01381c1d41025001c010300246030b9220141460451211804183c110b4802e030004015000306000000070781d00000d0806111100411210741e40765007a58244 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 805438183 1250 805436933 805436939
    0xa1b0306061205070c120306050d2109032004110d0b0a050a05210f0a120e010302040b120711010f090b01150c030c0c030605010b031e060306161205071701 68
    0x1801c0d642d0507960312000071560714081000c00c1c5c411252a1306c0c0c4c006401c3c0000c20700c3e9140e000c02c606809010003518158807810421040c44680025100c1e290741903c0d01040303050455568841c4014114140c0c0c4d6003401444000c1d805881e6548240c03c020041d0801d1a11480c6c140261006402509042801498207410010301400c000c1905820350708014240500c20300c00c1d041c04a02100444460a01ca110307020b812400110207121824925000c0e0641031010005500068595080800b40394101403040004014a0790902d0a40307001d10058904108103881d00c031011036150304146041c0c1099407a180e007016203581603034003d503543d034400c1655440b141e903201c440c174002c080c0c0c00790200046204044050000b034070a00e0080d040511030428952840e442e900c810044501c00d800180e5058400014004c07007070411b00f0705a01e0503012a0728030303205151420100c0d85544003d40140081c40e0350b121b0310800c46014403010b40a841c9070b12004c00c02441e000d080203140d92550030b801c411601c0703810004 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 805439433 1250 805438183 805438217
    0x103140f0c0a092d0509190b01170f0607020102031920030c0415020307060b0d050d230d020304111507080f04030f05010f1a030a0b0a1b030606 63
    0x18259407007004000b600034614118805016082080000075254100d00d08421030b009500c83c0d0003019600800300080d03a2502020041c98000d11f80c680f6040d020f0100412030000c3c81c042100350654030303100e180e8a40002c1c070b90503080c0390150002100703c03a80241020000c1083d0b055019512440b504d0054850f000c3d8801d1402c000c640c1748076000c1204884e400521928422050021900a20384100080c9860341e141640b0b8112002e5010082c0140c00c0010344005028950040c1441c40301c0c00c5440e070510200f1075441d1540c40040c41d04090500503015031458012805454816100d1842180d2039550510850044002c0d4800c03541100c00000042d0122158201150054007400c002c0384010b141003680d0321006143d41180345078440c0c2c0790b41000084006a019408040c10034452b0001107500251015030703406603001d29110000c0980340c03074540c81d160790b030014009140310b8101038244103544800d00707070070060f00c152a00d603140d90a403d0151217080e50305612400454440380c3d20441c005840103c0 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 805440683 1250 805439433 805439443
    0x90402071e030f090e010306050601090317030703050705040e0406094101110406030b03160303021f02090d03030b060d050708012907030302090f0301060f05120303040f140a08030103140f 82
    0x170b1500402c0000011701c0060301541c06607400190504010070140d0781d0365103010fa0461000c0810408443c0031041c002c55940500800360096071a003001400d250519403564207215000740701402a5450303003408018825248245042c82401e00f411100c038580f000c03461100102d0070361000008100e440b141c0c09140034103105962442d41c00078441c514080c07500801314050131035146450750601407140c0e0031f405a039602002c0c00055200c1e030060011240b00b240c6000102c05405610540c0c44c1c0100035040440e5100410000102e615040c00550540c0c1200802d99502901c0c0101e0f07405c624041c188000190440389143c122843d2411051220b00c4000081d14076510040e80c280c240c810921992000a0198001c3c0c10800c8029020700e0b5010b1503440000d080d110701d42e00c0519070030403440003405242004020800c020188000441c55410107549041d4900070a0f40081c22010107018103070010b20b010310103260419000541d0f01c0c0c0302d58481c148482d029080c00f04880e824450001c04003103000700814 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 805441933 1250 805440683 805440689
    0xc150405060402090405070b0307031b020d050405130e0a050105090d090321030e01060b0c010c020c101b0b090615120604020105030a140903121b0708090402071e030f09 74
    0x40980507544a641c01d000d0302078005002158140211071010442c203054902442c803d900581e0041084503660740820b50311440140d002c1c003190040007146022603004001c580841da000e441c81c800740b1031918450340003415a03038560960790003080c60b00003d10905400a5005205c0d0109441203a0f05046059a0840300d80c072008045010304000e60b900500314800000c0e50800901f000b1407101d20a05001d4212142c1d80c010428a440100d0348225030b036424403031148240420300040004c3e060442c005121040c0011703824041045000200003500c06e0f450b40f0001c599441103c9070900d00382103007a0b0346c80303560480d6842e01d1440584441c00851811900081205007080c1c040c100c0390326507030011100c6900040ca4180481d4039190781d04030008031303406214441c031441f501075034a4448031441c6280c0c107003000d45081940806003030240444d44011044071000d6900c4445142d4540c40ba4000c03c000c1c2c0101180900004000f101d5170b040e101d00c08014003a0644070741d40b011f26000002405075402601c1e80 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 805443183 1250 805441933 805441943
    0x6050711010f030b030114040b010b07030509060904090c09020d0f2a180605030f1501020613110a1403061b07021201090b13050d080c0706020a140409020c1504 70
    0xd116a845035000e441c0140390a10145004203814040601007401c4d00c81031034840f000000441c3c1040103200040300340300d001d41030b504205450070900782c400801034080e045106200762000555080595950361041c0911640407101400441d84d89070f880d4029000442c155805a090045507800d00714980b00706503030707450b001c4010303200521154015030100314241070303200070f10014000b044030b4881e020b08a0747c000c1c030190f80c4081d40c0380340c49a108a43c141c1c001d0112603030070180c140040c0f016a0013080031948019412240381400105040c913403640c80340f01045d02d0308a425810080b80094084003100c80102040e0708035410b40d00c49524541c1e2040c0c03101c02816840000b4056400149890354018003004200800481c4c2940700b82c4070310301d0b0008203503100c841c2c4910f840d5550081080c1407206c3d445145c1c0b2814102035038901100c138140d0910038401c0c0245565800503440d0500e6000e014454a1045100445a215070b140c0700070b40000d40c001d04110b034052160350300e652040310010311014440d0f5441 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 805444433 1250 805443183 805443203
    0x80414180103111311070312020309191a0a09030315031203020d1d0d0809010c020a0312020c06011710020f0f0307120213050f010e0a0605090112061707060507 70
    0x16111480b8820800c48070b035501c00080c0880c508580c0f042c1c025000c10a01750b4014035902d1005d40740c00b5210107205604031031600d0040c0200500c0032408500c00046009142210203c06031502e00342d0040e419807115802884401d2052007910f901075880004038900c26181044002800007050030750041d10300c40241400d420001484d01107110f9006000c02c203001c101c01058260781810001c88201007000343c8c10f0913a01600b8502d07502e0341c0c00600b4581029400d0001c03c914014800000d4640c10401c2016042c460500399804c0b040d107940c0d045440c0b0072004000d4450950711041400c144801c941041401e51140c212950340ca1170395442180c0203030011011040ca002000c2c803440c11250002400142403000e03100c00c004940800b40018081d68241c50001601d4505000401c01104075820f4424100046035401c0210794903501c09a90a486ca0380c14400d840b20b15050048441a60061071512068100b484c00071f20304c2c1e10030303104501114002c0c0586074800d403240d000b19118000d000c0090000646 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 805445683 1250 805444433 805444439
    0x110306040c06050a0c0602180405100b0702060f1216090f050d1101020106030c14030115140d0c080a0b04150b03031207090e010e040209180a0b0c070f0804141801 71
    0x500300074180307070040707060a105c4c65000f80c8a8408036048400d001d14816861000d041c0f252800703215548d030120418a8600506041841d440554080c0c2c80b0300a000e2800010080f10440b03100d02581d07035003000002c07010308510f4914200780350941102c2800b0045040b141000c900c0725820028141902c030003030420808008184c44101c6408810503045055560720742000c80800c00100c241c0002d0081c00b01844001c4050b00c0c149030031509500801c814103464041c1c2800b540c010403000030100d800464080701000d00d2410000300e0f04425902031aa0f40c443c4007034200401c0f03840c2d001780f4411390042c542d000808034414981c1044e40c0c1c1c1c515130710b940340d0010030194916010700c10420341c0161580c600410340399110075800030800c000b80c01c2a480c40c01e0007000c2004615060f0220b541c010003804800d031124480b460030503666080e588000700155828400144281c20b403500b5606c802c3d070409120700024605080c241142d500a00038090300442b400f58045450402200250300c40010020000550307103 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 805446933 1250 805445683 805445687
    0x201020c0a1712010b0403110109050f011d0a0612050609010b03070f052241061c020a1b02030a150b1e040b1203030c030714030108060103110306040c06 67
    0x2005150414040418001000d04520f090081d034040c0c24400005030303a0b1421810400012045500d165040040f401d00500c010b4131101a002240b140a0800c8103038401400d0424201c0401500d0254001000b00700000d400c41d4030a4843c0082c07801100b08000b10707140c440034820811400d002d0760850000c20000f10364003505c113051032040545149441401c0410161110f1105615002140001c1c0c001510030310504146a082640f555420032501d07585480c0741c801d0030480030400398400c0035404d410761414020386422013154030042aa400c40b15000b03603a80210b0000750028900703000000e00403070603081103803076846911a504d81c0040060061070040e03524404283c1c024410019515190103540c2d0240d100c140c410044040381040c06660700301c610301400112007010450600c40c1c00b282043c4580082d000c01229001101c10350160f603a0b5451750700035144210116004600a00d0002c00040d021b0404031300c1078180c070311581d43c00b1108118601059aa0f180585024080c1c1e8031000c020407900d4 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 805448183 1250 805446933 805446953
    0x10080721051009050601090e030306150d0e1006081908030a05250f0f03020405150a031806060302030c062a0c03070608100902130e1308040b190201020c0a 68
    0x36205008480a00c0c0580d8540815144800e5003243c069000b20014401001035001d01d508103040d0390001c5055152050000300e40d0501c00f03901401c5400002800710f0404425003062000940260848900c0d041305c6080300018a01445040c270b42d40620140100040c14a80c0f51041b515042540c1d07500755156403d00500800c406000350250300d46d035181103003800e04c0da10b6425091110316285c401d484980e05c8809840c2d600c000b03c04c0b0782003600c10882071000799100c449000b103c000404580391078003c0e100081c1d00500900303c28000820b40501d4003420094150407017000e80b4802d030213542d500300c006000d004060080c4035814402c6a450880c3c8640d2074600716884118030420021200b0781c80c5400081303420145240c1010380061a643c04101240d1000312450300200b1903800c2c1140b4050614000c980f410170726000d00e9500074418400314002144043c10318500b690451440c90707036150385e020008441d030301490705000130700002041464014010301c02d0701c00b80d90003907000d0701700803c02e03a803028004 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 805449433 1250 805448183 805448249
    0x10b01020d030e070f0905040b010e0603070612021605100c0516021903060c030c14070203031b101107050615090604110c030408010c090b1309090305120f100807 71
    0xa108200c1d00045c1d03d0344060b140c000802610000041031308217820b00686091701604503450801c5418140f00660310b000445104481705494a03200d0300040112220182c801c01c2000030002d0700400d0310006000c80400c0000030540420401c005000f40760800341c0b440c3c09a049810b22000184a0071000341c04d04c00110484003460f2461005219260354032601160305c0c1c2008240040e641e600080000d0b80c22040311340100400052541c1003000c0e40d80025030380d216031107003447c800b601000c965001100402801c0000b00128800303001f1382a0b00c100008054021400c2078a40f407142501192842900c2501c0c1407160300050860310169440006000190420049500c030480701000b416124040030b00c0078001030400a030001c03130101c008090050210340c1c641c11004000008002901040300e40d00031030b504a0b408090049070522585c101a02c0d98050a01c506200d03885010801440210060005200b19100b0301d02440890b25040c8050b5100c00a014402101c2582468100064030b008298041 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 805450683 1250 805449433 805449461
    0x20d0c1202010f0906060906060201061a0723061501110c040b0315090a030206160503041b24260f10081006090c030b10140409060807140102010b01020d03 68
    0x4038511007210348003116441142071780c0042d90780809010b280c9460060600a081a2000b03010041c1020800450140d90070340f00c00ca503180020b84c50f4100a03c1d0302622040a440220000550314000e07072241d00e07450100c680c031803401000400301c3c07038641c010381c012904002203200a220700340e0514207100082c4124403400b03505d0b103c0c034244502030140342c200b031030301c2100c8403c0a0009000240f501074948500030341f500c5001145100100c4455510000743c1b54040d400211100f601071015914505044e1250081420320944c0d80350b144901744100354100343c14100383e0300d0030990f000256880c1140f802c641101000884003a021400024145402540224600c6804c6180c9c6544080c014501420900390380307196611120104110552841401c05604150034140320780c00b84a030000c0d1080d00e075054440e0070701c501059468a0300100c807003620050300100c1410010307240c80b985032030b60b506076901c50030004944081c0445070951041c02502c11010042e001402c548500079003c3c2c010349034031094526 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 805451933 1250 805450683 805450691
    0x218070f110f011503060b0d031413030b130218090307031d0a0e040507050f09070f030e191103010213210c0b0912010506210705030724020d0c120201 66
    0x416040b0a102d503684040d030f490b07a510b80980c69450807009075000200c15621800b001501980131075040b00c1d580b8a44404191210b80e00d581d0a10b1210340c9103815000506000105002c0190b4807600700c0e12201514021a0040b8213110041a1010504012204e0800035042032040c480000d0086403040015050841081018119440801e82da0191584400c0c4a03110a0052000b40003040c40840040c12041d030b400c0c50120360714800304500c2c410142003c000c100400d4880b440d200c1c400d5001c07098494820082e40c6400c80108078191007600844000d079001c0030301124880b0365180c141708840c00e40b194490403011072480c000d119074055001c00b40c03180100c14540707150320000c0d22031074406000d0729440300215124807884d410702508061451070b61015030314080034426544d5810800c00c04207050091540035035106801800d041c691170b90f00c081d8140c132810001164544200042c1043c620144004c0781008000700400ca07501d1241d801a030f000300f114441c602000ca403400560010300880d42c00041 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 805453183 1250 805451933 805451953
    0x90613031208040c0902130b1c051005010906080405060609060307030f050622050a02041d010f1d19030507140d0f11011e1d030a0c0218070f11 63
    0x580760071107008540010b0000c100704810060040030103006403c0017507085040001683c03401d010f000c02c5005d0703000ca000010801800200b0588921800099800c00502a50a1805001d100040c0e40c3c0201408540c4040b804201c041c800c4603003502c25500940101150b481d0380045c00046074000e4041d6415000c1c5010110101e426104000c00390b900c034000500c00d51801813a072000c80041c11007122911030007643c401e00425400500c6801d82601110b0002e50508000c04080c1c640050380d150105030b500380429640049480e0340590080d000300d40010781c0141c01030301006d03280d1660050142504003000c402c000481c2c4a9000780c4034483c4180c0c1c01140804040c81a0b5140402044a410000e902c0044000402d9800007003000351140c6640244100c0c80758000040341c1c4c0280303600c000c508a5403010303034400b840140d02c3e101c0300d890703203103429655280324510000301000ca40400580c064410109240070803510102c401c0d110f810f5680d5144c490388031842c01120000c10420514a081c82085041 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 805454433 1250 805453183 805453193
    0x1303050f070507142d0a050307090608100504080f0d1e0902101812020301090f0b04060509190210091e03020909030c0c061605010504060203041a040809061303 70
    0x141000ca0003800104103d500d0004208112816400c07414001d12a03401c44104c20050040140c803800b000c0802038110b600340001040c04428150f005680c1403252701030016040c4a41d5120b2030590740d200040c2c50540110010b0217043e10000e03036006080352800c0041111100c01e0801034440d90441e0f40c40840c00c0701c5913a55901008a0340c48141d01c880d80d950307011408614040e404601185e00d41c0c140792002d03403c10812400b0f0f0414a02c503103030340308054091590465400703500c006061035001d128146071171524102203c0c08401180c0c03c5451910701008140807800018052041741141c00202264440b164284029145554101170506c40000c602298441100481c4062819800e0515000c0f902c2c42c0104480c1001c060403010103600200241c050a03280818407810007041a00c02e01d6a0b004d086d06013078480c0d140d003100540254a0202800104505a0011401103000d950000070b050050300a0051020f800c0e1801131500c00200840d001604044020b40340880c105c00b0b168984665035101c13 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 805455683 1250 805454433 805454437
    0xd112b080c1b03030910020a080f03010609090902131d0105282f0708030c030103120203091e030a02150a090807180f021909030201080105030d081303050f 68
    0x88402080c081078440500030200416400344101420503103040705940c02098a0b403240000d0300e400303242d02244c040c401d60b00800c18a801035902481c0d0a075190310610a60300c09170020b014210000740c020600040c0d41e0305038000d040c525500200030303800c00c0720a001d03244014035059403c040c1c01d655240344281c41d20320038820b02c2d100313401d01580c1c2c0850a031f010f426824122142b0200480d42880c3c80c0c102c5500c148001c21600c138104401881406107413240d803004000b03010340e000c01030080000208011248110710080c40c126442481c0b00382858224650070b0780c0300d004031403145801606c1c0380401e06405041c151900d007283e4001d0150b0340858040d4020030075850688071000805940020742c207610517448805100141000d10142006504080c155643c82e419080e0002040780c944003482c0c100411541142c03e00707000440c285031151501000034010400030310081c1c1c08541a0b00c00000e00d8100444c4100c9a881e07a82d41d00611541c5400c040c02d444000c07a0307025006c02c2020301104c088040c980d40 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 805456933 1250 805455683 805455769
    0x503070e030d0905040b1818030712090e07050406080f07030e01020f030f0a150306020304150513150e03040911070206121008010204260f03040b1201050d11 69
    0x40c8440f00309040205100560314010221802001c20800307070404c40465103141c0f0f401401c0060f0018000d89994045483c500031a000901032316103821200161980080040085812000c8041c03031320750703901c00180e17858043c520030310307001c10b072400c0c00254880c28009150360301c0b00722404c000901844041c01e090890700202d0048104001c000180002d841131150480c1c0d104400034018010700e050170f01119421022880018080ea4001c4045401c00c1008100b011038581c2c0414104500d00e0b00030750302e001007045c0d0780741a0b5000e031020b0980303d405140340c02840b41d001ca00c4402107182c43e10b03112800e03000380148191407d500c40c05001c0c0a00582d1200010242c2c481081100309450400e40d94040341d61140c0c4e442044240c0c81000100130a4170b19408041d1008000981c0e4500d0b0720000c0601d6040c50702614616200c2d01000030085201510034018095403105000d8a002b2a030b00c035828092550070403840540031003180c0710402c059242c00e80070110288a80075191068001c4a107054080b030300292 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 805458183 1250 805456933 805456937
    0x409020d12030b0307091107030507060b1e041d120906120a0204170c0d06050c280e0307050901030821010b28090504020d110d020a030606020610060503070e030d 71
    0x988508860b2130308005c82d03c0601540081040388108010380b2584a20071010000c1c1070140100307142051018030b030301c0251410801360500307a005141140001012030848066072007a440d0501d040a201c3d0b000a4290000c211003008180c84d100280070315440b40c200c010b20580c445010440a00c4404c0f50003c0f042c01b45107801000340e295420005094520401c00d22102c140d03030700014071010b4942c1c0c2c2031001240780703401c603800007401c0d19826407030021032042100790086130542074009541101401c01100750700045e991b8505032031351101c040640712403040c414158050380750070040c008130f040c0c1401456501800160012041c4a20f94101c1c403211382680442c650100200c0e0f869501c0280103020245034182c2c44006004158a140c0500008101d003c6c840c092507010401d60345080040d40103e8100e88511a80c580ba81d010740010406580110b84100000f41800030004240340009605800b1740e0b0250611940581803e400311915040108010104840401e03840101d48080c00000784118440e = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 805459433 1250 805458183 805458191
    0x23010f0e060117070e190c0e0a080c0109171c0521060d0609021306091505010c050303070c02150307080a0605060a09090534091d060409020d1203 64
    0x141020307414903038140e100280344034001d42201e00100e00850f5000a450001000d606a40c558101c4040006011001001101d140940c0007000d59040305440c0c400c0740c005c50b41300042c103880303400403034490000c118103501081100809000c1c0c241c1e00d0802490300a0390004880e40030341a10800c5803141002e050f4200401c800080c0c1c40e144220034401150800169540d02c1520704021012501200d410030780600001d03954604181150f07a001c000750f1084802d581d0620005840c3c140401c000c1440740d1fa40e051070704100c0c00c0040c1c594059003040301f00030380000181d825951805800e480d49040d0f5001240e024032034141c0d440c5804444800745000e8251507803011030620340400b4030411200560401c0d8850b1400380800c1954581c0646000107403140e0701004600e64a480621158030b1440c0405441071400c81c0f01002070419114000c10680d40302652030b0031920355500e0b41d401c02c404410280c0c1089100e9000042c2c00c9050a80020a84902c0502030310700c0f04c0040c2e200c4144051120b8680710000f07442d = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 805460683 1250 805459433 805459451
    0x60f0a0f020105160e09072007080c090105150f04031e0b07020109020a091d010504030315140901170c150301050301060b0c0d2003040303021501060c0b010323010f 72
    0x10900c00c40c2c1c0d00c131940151801d0448107660024244600302d134440741c400e0403028005442903203c3c044d009032881c054070052840c040c00351811612090240a001120f00c02c20810b49142d24140c2c00301e504844010b800306144006d80b00c09400e15602480740b008500c3c40130080080001c00b101c44142485060082d89803402425180c42d0b0450300b80504034100710780c10007030b5900141c0e4032010700604843e1201c100140c04003006905140c04d88660064a80c01d5103010b042105060b019048039488280d8094003110454444031801c0f05001180e5109400819490051022021805921080d10801c0e41118a400304041c00160f1902c291580c1e050103003c007200400c21800c09003e0300300500801c5104908007800c2d240322554400c840a031240c1001904caa401d1901c5079942c282c02c48400c1400141c0f0750705ca8490070081d54070500d10703043d170342850307007044c00015028840c0d0380500301294040042441703a440d54440c2c1214541d802542e03a2282c0e40100c207070003407407000d216002002480400108060107 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 805461933 1250 805460683 805460687
    0xa031a04020f030a1205030a0e0a05031209030307020d030b0a08060403090504270f020a0503061e1602030703030b06160c0f08032113060e010b1f1b02060f0a0f 70
    0x209102a40282d0003000c1c0c0000103034101d05e48641001551a0407612550f58111180140c0005001a819802074140c8142400b00100060034203004889840c0016110f0746032080c0d0fa4072007160103000507082019151440c910030342010030418802806582295100c80c8204d0070024255402c034080758480c00c0c1001541098090016070034000c9001141446120705141d200003811403004000d1004140b02000b1580c90b1007202018090180449065181180e102900944101824103a0303c0521002616a4201420100424400703a01441c1440890f80d000c3d070207000f070700d10b07680da10180c10300580d0600c2040d03002e4560b8890061403079000861800304980c1103084282c00c80b02180d00100080310240c0f501d41c0001c10b00b010003c608401c980d4030100304228081e07d00c5070041217542044071001d4a0705054101703480c4040101d500042c00c03d00076180d00c02901544035184003241c02c4001e400da03e049511141401203001400651911081c0c0100b21816440700758948042402c82020510587d = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 805463183 1250 805461933 805461949
    0x122107030f110901050702190807230306060d06051e070203090a0506030c04150c021e19031203021e0706060f060c05030405040209040b0901060207180603080909060a031a0402 77
    0x150042c50403e2a00703030880002841480383c4580640620301e074403004a4803590b4854004014601c2a0540b48003680320070101400b081103a440c280450410f000b0107005180c00308a440c01418010302003100c05982d96541c1028200c0244641c00408600071303d91119514a0384852103030040754051130b9070700b02d001d0400c907214031075400980c06901e0610400450740c6002040300c0695008000c80340181e40410412200741f42c189000940240305000d0010f140c00143c90b12000341d9104450054050343c20b1603200c401e0030f102d0322014214529091054203182e010394020b02d0241024002514100b0790501248a01e5100344402c07940300356107036010003010b140109510f010302042c3c41c0c407110132495611582c0d6240250302070544110350000c2d01403003a90721944000b004c2c2c540038101c4080380d0380d9810301a48074602481032142410302615041d080d043c1d2032140c07209413944100954146002901440300d2544020006900310f4a8500040049101c110920380305403e080107400d86844e142c41440302e68 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 805464433 1250 805463183 805463201
    0x30a050d09090b090a200706020403020418030c030509030c0904050601080c150913060e150f030309033310061e051602010302040b07140c060a02122107030f 69
    0xa42e03d01140fa800b56511903108603049645008003155004000b000401403e0f800b05500e00e030310b0000907550b801c100c020b401900803203000b101d04008000c2c0e03e407441c00b4550100356000f00041c110000c400000f034003480103020a880c014003281c1c01d150380d032170120303821040039142900d5660226004102d070b42020000c15505100030b66244c0b001010341015102c0328041c1500c5144030f070031201d2844000a80136071268004007407411450059080070007403890040700701900740340620b11058105070136050000807250b905101400400205401c0388408051042001c0c889c050b849031040f860b0f412180c040080c50041300d0700001d41000d54501380c03020308200070301141400b03401c40c1503e0070710b1400e0304a03003554616440a110002614103910049000b0702c0f89070403101d0154030100c1d650b02404080051300381100300300302c11514489202010000700d4020500213000580c0440d2f01036043c0300c0b8410141c1201402c2201c0c21601510f03c4622101c0c0c0d10044642d0000a682c601180c44011900c0c0202148 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 805465683 1250 805464433 805464449
    0xd110c2701080a02012001020909190c020102030c0f070f0b1006021b0603070e01020f0322090b060a0f020f010c0c0308130314090105040801060605040f080601060206041e02030a050d09 81
    0x6071400d503002800c50006e81d0000d00019841d200420a180c00070340407640c1c60764000b80003d88901e40111a107000c0848040c5001585240501402649005208607070280c403109202609001240030190f40c00d078003d1004541500001c500d4030300090800410030301031191072403c031034164248032000f4030744030094205c190421000600b0100c41d80b21601105d40001451801700140c0b0301110040c1d15120712070040d03e070a4400007600f100f10718900e81b141e4210850a04c4020440b41d512482b00c0c5c251420080c200e58055400c218040c0c0300c41c0a0110011046014010b68922402544801e800c44250001d410040f40b142e5002c070f404c1541c07009506a2001c10002c4402001300c69840003085c24000806120000784c0029010501da030058080c3c1e001405060028840f0f5601d07140300600540040c480d040901d0040c820129800c2c07030209407941659a2075004282e9230342c0710b4480981074000001915417011a200c1c42c000980c0741405402507150080005104803500008003c2c90000198081c17a4 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 805466933 1250 805465683 805465693
    0x1814100507020904020103020304050c10020322081b21010504140a0b040b1305100209030d0903120c03120e1f060e0c0c160f0501090e01080d110c270108 67
    0x30060f95807103900340d049038082c40c0060700d0f903407180f40003403900c03843c1c1d486254080c081210110095038000000c002c3e10484070004003408000e0107581004179658000c0716116081524031049404c410f070003c100d80c4000902c41c1c00c080142a45803d07500401031140202c2d651210200f2080c45500c41c6010070001d804401020300707440c10345030b81884803070181008101c100800d0210302e200340c960000f0b00350183c0100030b455000c0c071080407240c002c2d4020f410781c130f000e800341c42d00c0024118010395182c801c40350040c00036010210340c0481220024001003040b014060580d108000c1060148200d0400c054038070000d1103c1541c40302d40b940a003e0700203c3d0f91200b410400240b0403691a0210140c12622000541d81c8071051028030700d040c0007800d42c42800078203840c82c00194491202d03140da41207034803e88401034915113451518910200034012640c15500c50000d000e800751051343d00c880000680000d0f102403101650000b842c040405041010000d81110400c064500703185006004103c81d9000300 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 805468183 1250 805466933 805466947
    0x302130f090b0a031a09250806092b02100606020a03030f110901030902060d0504052103100e09010609020408071e0501020d0f091d070210060605030a0c18141005 71
    0x482595201002420311740c8504049480240104003403141c0c0341c03822490100100407800c0d13200340a41288980c0e5254401c640c040b0700d0316100401e01d0700c0080d1045ca4007201201c050fa50509920490344440811807144030601d07814a0030078451a009030032990701505010aa508005069580e454180003807030380392444070000f0030102c40c11142420020308006c00d4000c3c0354000680e40c2c0c040d00f980d503a01c040c1048100720820a0100f064030500620200c0142182c404c0c90703450b10319000844110060b07070b505200610102c000703079000c0e0b035203d58001e0002c500d1540f90401c3e0f80607a00650b00114040d4070442c41840541072000052040c2210a030600700c40700c0c40d01c030000755500104841d18081c083d60380c51690300503100348032050140070207481c40004d50025814208541c02c0481d000c0c2c005005100b181110481c6078002c00003251020369070070b825901c4c2c44580400070844400c0da4000c0c0510050071006005a075401c550003010b0b1049030440c84070042041c89030a60407000f0384001c11400708105 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 805469433 1250 805468183 805468193
    0x61b153709020103090b01122109050405090a15020c121201121e08070605070807020a08030601270305012004120809130e160f0509070302130f090b0a03 67
    0x354030000100c04501c94406000590041074281c07005081d03280c05000208060b19503483e44110148a9649441e10b24240c02a40f0401d04180ba50000018080c840070045850305412054200c0c1000c026502c0c450415038440018500060705003466540120303841007980701c01d001d8407450340c1c440c8407181d1424541908113110311905000e0070760406110030340e1205100f800040039000d0f071880d5425849480302030421403460381221304100c48140c1031000050f0380303134030400c51140111929002007075a14034680d103580c820341009103c2410000704035408440f0348240145003907102030001d8803200650039030800c142580c0d900c0c503d00c2c00c040d040d031150070030001c103039811a411962005480c00c0315007070500e018501c502c9003441e0a60301c03d003c050313803034008542039202e00030206840702114400144941103007c00d1b0600d203c0e2200a085402040285003090210b096200446180051a050a04180500d40d80340341c3c210b604040c042c8541404110501d20407650b82c0c0008072040d209107491039550f = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 805470683 1250 805469433 805469521
    0x51804021e07050f192f0a060302040e0c040e040201120b100305010807060201060305030a1809020a02161517060612071e02061501050d090804061805060a0e061b15 72
    0x4410111548002e00103210168040202825900400030b2800390ba2300c0398002c6c00394020740107400c4e000e025a4007168130b8000b200c0071502101c4015103420056600d0360019650502c144c042d5803140303910f50707071242721503501d5800b2101c3e144200e8400090039410504c03800c0c90070760307150016015680b61502c1480450000000d48999401ca0702c1c2200c0343c0001602e0054100c5811340c044132016002003091080c46801054800b26866a10407020303202e641d4140341115001e0307094040f0041020070461210820450907060381c8410301810340d81ca815059134598544080440702d0b032002401c001c0c80941c0c03288c060003021062130707050710040c1705600b800c0320101c2d03038020003a1955041c001c00060030409010503400540680303400c00340c22a2165a18031000e40b501c849a5280920b0450b1042d0202c4c26207807a20988031080150364601c0c3c0700314404c0050000d183e000f445904005044c0080349448941d080004100a004c018000016400c041e01145890900e82c040402c0d50540d002240e00c0c0400707840030b = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 805471933 1250 805470683 805470713
    0xb1c020c071e0801050106030b012706030c0c050a0b09250b0c0f0f0f0d0c0c0e1e010803071e020f0405150409060212010501051804021e07050f19 64
    0x9501d0580c15921110290030b81c110354060065942088000201541c06a120f85801070081e2924007000060214400300202000c4901c0702e2000e0005081c80b034103102c1c1d80502283c00050400050100141c0c960900c2c00140c20700454070040d032001080901c98041c00404481100c02d58001c0c1210448030094542c070f10280103c42c0c0780440031440c4a042c10080001e83c100352255000c1c0d500c81c500640c400703515145e0000300121039100c0e0740d40400d8042e01c603001c00a400390300050300f01055400c119115001c034030060414015480c4913651040041510103410380200a0301d001150307520307c0ca190500c0c0c40d400160411031201d8420446034050303100e10109142141c802c680026040c0ea894a101404181310080d0940092800c640c420801c4075950060401d41105030282c1e0150b070760303000116074900c03891011542104001940b0a02824a0b4000d804075210500c588840503111582c1903045400c0894251281d62003102d81c203039030003810700007442c41e00e0441c0d1242c000d860003600d5106183c2010b403 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 805473183 1250 805471933 805471949
    0x160503150103051b07050703030906020708030f07170c0607090b0c031218190c09021e0922021b060622060503070e0f25050a02070306060b1c020c07 65
    0x2400140090f50a02c54800c0c801d403a13141c080351503c0071424131a6507014070340412804540081c00108031f03180000380c02e80845443c00300851600c52400c1181c0d105401c5400200c0385400a941640d161202ca01c02818580c60324070b0007071055203031050380207000d0216a804100381c89020824840c10800200c1110100714044859a11580b1000600f110341d40e000500940c2a00070517a0b103044070300c801840e203116540108002091642c4a0542e07074128890b4411001801c02080e00f94243d00f0640b1002d49142c0100402c0d440344c0d5004003c10006002d28407000c07056050780000c80b18400145d40160144005071b800040c403407454814049492502040100c204113000303800701b200051b440303800c84005858050151101d4640c0e0b004031b2110160f040e540340d250440c64034005090f000800b0114201d203440e02c00c3d1401014103c1074156001c1c1d1043c21503900314020b0403408000b00300d041c0900e1000740182e054940d50741000f05290758160b810b00130f60040150042000020b1902c4c00181030301038400c04 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 805474433 1250 805473183 805473191
    0x230604022101121103010513020d0c15081f08060705070f4107030840060201090f061e0e070515070510050a0204120b160503150103 58
    0x7000c260003a01040780341090039004040e00104400c1107400e0b48030182071090038111a414003580805003600c0045480e002d0030000c2c0d00003140585000e249848000d805500c00c040066290709440340740704003000e03114000c25400030601040304c1a50000a0000720001c0800c074a890804942549a21014105000304103020070801c052090000b1605200307540001840307131519411810045100c000c241030300905035484042c14813039203ca01040d580980d004094801c9a00710303620b24606400900100131109800440c94200010204242d0b08141210300418049071104103811300000a68000c0070440e41000302d070000040318690400b8070b2650000010955104542c401400d40802802c4101101d0406104907840b690210300d40d400c1d550180c0d100317001d10034080a0440d2900c070340c12000740f6941c880031005202007050350165402c981d1444026203807540d0786020240c0c00f41507100070765200080000344110704c0d00e514400403820900341017960643c0341c500f482c0f2030529040c2c13980b14145611 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 805475683 1250 805474433 805474447
    0x2118091801181718010302030429101e260703030e0306060a0605070f02040e0d11060901111b15010b070213020f18031c020d0323060402 60
    0x2084400c411000d640354000c010320180808000a00c26000a0554280000703c0b40840080ba6035012110340b055241010ba0042654070011002940010416504d40c1050314442c02c0c5050314841c0c0088040003240c11106034208401300d021554002d6121a144414410303540e030302c0004040328103088455403c4003004c018180014605032030b44002c2041d140d0300403070001008058001400c1c41202ca402e60445a0315680c2100f80300003001ea901034032002c620207000e0400014010341000b8010351014001192220300300c00640c1ca0302408151340700100758000c285146e4460200441580300910304024860690001410f101e584151020b00c41d145100f0b0200e4a40d03103004018032446070203004860030f01982d5990301d1303400030341190031308a200d806104003888800f074141c026205021800c50081d4038050310034810030520030000c50741e203400d0b0103210000f9156502855140c0c0d64a612a00030700b4010584c110010201d44112031a41c201203403041080c104522810401a0b12510030380d401643c0e060 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 805476933 1250 805475683 805475701
    0x106080c0913050102030906010306060f030305070f0c030b150f090103081605030c16150315120606051305101208042d06032c10240305211809 63
    0x600043c01660001040c00142d0800198441c1200d020704801c10089440c4c051140c0000c0e08c922010b00003500a11180010404140b6000388031842080d1404c0029500c0d0b03620000d11400301d13402042c0f49030081c01e082c602c0c107000c9030201815004403080403013981103036034a02041c005d100645200c520400804001c2100c2041194a000044e00c00c49110004546030482c0c5941c06003d00400c0c0c94a6540d035800d41d03400381c01200140341c1c400e0200b07012503081006110000c08100303010703503003d03803108800280fa03155402c4c06040c442035541c012a940c50714aa410309010311660200050102c0100800003003420b142c01d64040c1d8000c00751900154a01249280703c40b009040080c000540c201c00008550b601175100101222a9044880c140307010441c41d01c6c0840303076154819406410014040869072090360120409a040300340c4032030158036003501403071008942d81044030b403644400007403006c5030000d0f0710038429502d980211074501303046c803039044080c0301c09282c40354003c000c4400820792a49e = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 805478183 1250 805476933 805476961
    0x9040e160b13170d030f0b100e1504090207050606010807050307050a0306171f0204081213030c150201050a05091e19051005010807121104060302090a0c020f0106080c09 74
    0x420401c2165521601c0322610f20b80b036807501104080424548501c030b800440c541c1c000e01c00b401c0c0c030041101503c0c605007802650701d0b000300c0101d550300840c041c480c04210407040000c0c00142c00c0d045801600c03a0a50f00e816032070000c0180100f070600c0a1b4008000c2e031183d10004880e0f20040701c2c58880e4451070100030035809440d01d50004c440c0c0c016006402c400e40c0318001078220b552001a8290f0f03000c070001c4041501240b04901404170140c0100c4500c40748480c0701001844001245020050007641d83d403241086142d40e40c00030200a190a042111102d1742401015000360303191000308842d09000d80f040d80d440405400c41c02102c0e00d0780580204811060040c052400340d004105d1b9010040d91514544694414a42081c401e2030f090010074841c030001941402d44046c1005e038003100c101500c82c1c0e0314a000581046038401d807205004801070311103a818170300034080b0302000307d40c101e40315101038102070102425418aa1406800300044640001c1c01d1680751000e0303a51400300d44440030990b00310 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 805479433 1250 805478183 805478189
    0xc0d2102090604031a0f360304050a0b0d0c020303010b07020f040e1006051810061b061109090a05060a060c0305071a040c090e0c27010b09040e160b13 66
    0x1d002900b5060040c00740c2d480300e031485801c0c140b4484885076161411031252401601c68511800380010001650251f000c0480c1d030a035007400100c905042e036841c00280c0c40011600401c003180c2c40803500d08080044d600405158600f140040e40c02c560400e414503200380240030008c0d200e000304a50618694a4503400300b00d56108a905580301c1c40b0300041c180e005021288a00790052280380d030401c41c1d10041c80c80079800b903151a440c1c044000d24210080f11920f07418000001c8815600380d01a0014289100703121119803c6002c03603841c2d00001c020417031400c03001441540003a09020030480e1969030291194143d4060381070428100d02079003002c0340d507409407060040210303a404c0b18034600301e00744e4988248194400c6040c800441c1d102c801c1d15098400c030624403540c1d9801195030b008580361412003d000c1c1c80c5d0210703405405482c0e803080d00c0c40304c01c400c1c1d009140690001800d8451400c2c2800b44025074400900188079441c8224003070450001c8a00c00c208503460041601d03450482035440c41001 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 805480683 1250 805479433 805479443
    0x3020f1b10140d0c1106041b30051204030302100f020304030212160c0906090506030a0b130f02220506100e0d022403070f030e0c090414010c050c0d210209060403 71
    0x1f468035141182e40c0310040d500300400c881d00b98000003442c210881e40742ea80a15210300400e0096440c04418004664402048855000300c0d003001c44008145c10192000303502a0740242a000e594401d0f40048070481000403044030f004000b0400030035000680000e2801048101e20ba4030020303440f2005104030310100c01442c0d421407020000391f81c030041c3c020b03806480d40c25108204a48614080654481113000c00078801300310f010000d450780060b45016141d40c0e001310510300b0340c07881c10343c0040c100d8003500043c0e1101d0074a425401c141ea40d0180700b4640e20150a50314201146262200503003103612844010348210902c0d5100e1046441d02001e0700201591101d0740c2d0342c1d10072103905403035041e0400c4070306000044c94a103d03510310f14440d005511040c102e4001600e1416002c03070912507a00c000a1007554810030034034038408014000d2081c43d007031105581d207079a1a14070350784246042c0220400000104010604203086208100300045405105c0d6040103070703528240300200300782d40220303800640 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 805481933 1250 805480683 805480693
    0x509060630030403020f0a0e01030b0621060a0501080706050d110c0d020604030219150b0f03060a06030b0f0403200a080703260702071203020f1b10140d0c11 69
    0x41181c00000151060724800c41d030700d00b520b107503203007d100300c0b100b83d0f2150215007020040100040307144200c02e00c2d0440400750030441d85606404001a0f40111b628072144d09a114404004207900c0511496014090590142150902d03010004050b405801020f941096540020201c0c2d00a41011600601c1808099a96180320b45001a4540c0822a4241d000d03000d40048607c51a500f44100811264440d44a02e428042c400c41c40006013140700c1d055400100708000c00c0300e10b03a41080290711440d0320000100e0101c2c110324080c001200040c040342c640d680240d00f40710010b500181d0210103000e4450030000015200ca207000d24200303800801134081e41d80041d48809242d4801402000600c20781142104001d00c2c5000f450f00c420101d074030308010703000f4600c14080c074054410400c03603060091044540040030011441c0c1400e440e80b0340900340c8404007c10314100e041c1100030700040720031030401512200780307401160101e00c03a200c0c2e002d455039920404480044d0244031245240c0078841d00305d030 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 805483183 1250 805481933 805482019
    0xb090a0b030c030607021609020319050a0213090e071a161502030115080115020d0e01030209180402040c09080703020904080708031005010306050f0a0b090a150503040209060405090606 81
    0x20352141e4001407c0161a60280004503200d181070003180d02030b00340108503040c2030701d00c0e00040e001000040c221000d4590200004078448299038603607405000d4030030001031010040800c49140c00b03d194088c6030b0405c00d500e85110075144903c140d0f6032000d00915559048140c52030501c17540c0600d096841070301e40c80407001050750200b9071011180c08050741c82c0c1c2d130400e980b56016030030141e81345c1b078046006078010101ca010f11407080c1d031281e255075010b040240c1007a122200044c05a5118040041140d124030100025854240591000442181809601d60381800a06500c604960001900a00304803002c17404000b00300701180e01068010052503124204600101e0701140f1034459140003031706101020445d403070301c1251580400e030300a1845552f2480c0990304140d6820203002198000c0101c0d03000180c0c1840a00001481180c5941301a41c0786040d00c10800c030401d010308140e005174a04400c0245014002030170541110302158603070002401100c1e130094000c420016240b81d00844c02e041 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 805484433 1250 805483183 805483187
    0x30d030203100609030f2d0605090c090f0a090f02060403140f120a0e03070b030f01180c05071506030c1d0f0f04120c0516090506040b090a0b030c030607 67
    0x40c6000c0c0c50b0000148074941d030f450200300c0c0d9904142c0009822207500498000005000440c83d1010000180d181c6507855500d000b1070794600900e03c17040d1001c580b1036041200c040703070501c00051017400803140360160707040084106545000083c0b61006095460038032005201044210019690b030042c565680c41d600c83c6405003010424000018503880b813600c070100328140110303042c18a04141134660317091050b102c0003102c00b000741c030f604550940a03500c0c020a0061890004520070034000413402c9980d494043d23000d194940d55003203200720305d00c0c100303890b040b440d488401c4030f0070503421206109015042e002d145004126903800180105c41c002c10000d01500900c2000110800710707501d101507941d03428059a60800e040f01c1003054051220000b80004070f40322105024203d1615081d1005841684c4a134078042500d0001080808505000c10003403007140203941d4400002e4806005a54a85001c111103400c060700c480c0b010364640c00c1010701c58500300010480306600400b00c0740282810040 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 805485683 1250 805484433 805484437
    0x1501030b0909070603050a1b2334150b0f210607020c0f01051804090c0911090d03180306021810031a01030b030a150902030706090b0d020f0d150f12021e0f030d0302 72
    0x400940e502c2b40441c0c50050305606410190140e00f0003d01281200c184000c10002d100b0f008801c2c0c1d120042000c0302e091074840f1003a0301e0b941e800000c071400c40e280707a032000305151510050200c011580160b42c1c640c1c0903210035a8140601708207081c0305854045040c680d071440f41182403101e801c189031105100500800c08840e000719103142104010004d1600301e4804544200300043d0341040d118022080068866082004455101c0d0750800065850741d9611050380c4c0403d00f03c03200071a0310a02480d82e4a00744c103c0d201745c803031581400c001035000504e1a410343c1d19074044103418190744421090503502c0c1032010307480740b55024021640c16184004600010080034409034000d104240c004a40a40208895002d464000e07000e0b81c20028002d1070f603400303540103100d4040075030024002039013541540c0c0181c000030007601001c800100d0400c14002c0d0720014662151704280009426800561502100c0d00b505002c90026031390105035643c0418140c4d81180d942a8062007803a84001d1100d1381580 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 805486933 1250 805485683 805485727
    0x280b10090e150601050408030f070501110304050c03061006120e030f0705010911030a030504120503041a030405010f060f1802040506040b030108010b030d081501030b0909070603050a1b23 82
    0x10450300303403200783c01183c050140b4001c1084a90041050101e1020010040c040507031040c8000b00c5d040c90120700d00d00d0581c105450480b0f460780040030040003440c091040079442903005047c1003492745020360041010350b84c0d0600d621070580e03545040985e240c0510440301651100b502240c0d5424051030910b000704112101030b2880600d107280304500d860013280200b4151703010b540721070030103091140d150800103880000b02d5032440200400240d5000071045c000070312030401f0549841f460035041c524252a2030319090241240307008001e0080c07100b01e001c0ca5007510400f0410f200b03c03c40c0581030f94001c0c400c0760401030f0300100c0801c3c0050003505510003076042c3c13031082c002030010500700400e15545884000e510004145a20001200000b201319107a150203030500d008607a2007000800310b0040c04007a6079180440d00410340902c0000d8140c01102d41003494180200000c4810f1001d6585045000e00c0d000100011003801c588024040071181402609018540340d41e003d90210440000c0300700d032 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 805488183 1250 805486933 805486963
    0xb010305040b04020118031713241d1027082e05090a02010906030b15180d03080a0e0708151b04090c03060602161a0c1e280b10090e 58
    0x11802b00d800300101c4525032204001a800d50303aa00c04d08482604d00b6010840030150340031001002224642e00c80481007a01e0009407151812043c41445c01e0074074200501200c0903004200008000d12100001e1003644c17180e80f82400000513203c0300c00c1040c01d1480c0c07100164554200f20900c1100742d0003140ca824418800d8075034611301560303030209038213480816252a5102c114079078098a60003001004000392780702c0c0300b440480501c0c0040010150103d9174001d50000b013143c001c000c5105404e02ca005200c414880c000c060341441c000e206540c0790400900701d0140c0e1740001c08518083d00c0c0b10a501e9003200816100c58423283c64600100050454002000c000703030800700e00182480c00421802c0421400000785403501d0f0605043c2d5035030380e848d1081c0c400d03d031000f0032003503008600030b015458002007a55a05036140c1c01a030581c80c0340a01c051005034038458107400a0350300c49840c5e01800d1195038040c4030b11210380d03100910440c4200c210741c0003040fa1030130315000000140011034030103c07030f00d040c0b = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 805489433 1250 805488183 805488217
    0x606020609061005060904020d0e010911060c070302060f0403050a0f032307030c0c090906060e1602060f091207081c050615090a0b1c0b010305040b040201180317 71
    0x551600d80c0d032004103440702059071900840501132410311000802840034054070161610b0220785115049420100b05011640d42d100c48241c1009000b80741160003880499540e81440c1900b000e490700c0d1002071000a128450014412503c40012810b0750f004603004019214601c41034140940880d10000c0c0440019404030348002102c01c1c0c0120000b905000c00182ca0706116050b50180d03030170b8490040c01da0350481110400100e4403941e000366035045104002c00710b43c46203481c85580c500d80d405440c20a01c0c040d42d1406880c001e6001502c80d502902d1004000388a468444041d420a92101c140a41201000031190107110101c402441000c240b540f03140100c9852004002c21100c01b5110070f507000d45503909030310a140901001d085030034001041a0700059039144c1045880e07018649000e1407060f95802c05500505030f100d41100c1c038030b017820240001c2c03130166100d404280d0020002410b02940400c4520400c0c002a000c1c2c01469200c0c04001c20313241d05030741031001504125203c000007401c07 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 805490683 1250 805489433 805489441
    0x301061517071704050f0d0f120e03070f0c080304091d150106030e1606020703120c0209040206160b193e19030504120513030212010e030d06060206 65
    0xd6010610701c00d40881d41c3d82d400c8464016001d40c8003902c0503100f91000d12902d0000060b08000380000703000038450b1380f541c10040380e140d000a01900c04014075841c0c1303a8540300400820381400300032100850341c0103019003150b00e02494401c1d50240c0715001052107100104020030b948801d50310100284071448114840440c4c91001a9640c00e4800d160405214000c001041524080c0d00701415079190001602c0e903080d81c511004030480700302e52101d80142d201c1d1004000b030110b92142e0007030986262a0000281c03d0329000300c0d02c40500a00024042c00d800504007940000c802c0b807254016500a12141e014100b8101075090b01c01c5c0c0d8141000b403685025480140008211542c4031521085810703083c0d11140d1140080c554031300e40c010303090541030403c900203103002ca03130000c20120000c81e2000a024141800c2140c1e621030780800807010300c40100401c10800c0203030241c2c48210390703048a401c0702003425412182c0c05882c452903406542c0c0301c08145500f0004247d0840429030396150308460751075072 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 805491933 1250 805490683 805490717
    0xc180b060703091502010b030a0503040524030408070f02060d050a0c11060a02030a0b090108250323190506060f0306040305190c020d1a0702011a01030f0b03010615 72
    0x31401c600100802c2e40b9800802c1301045610a01c07200c407109000006895140c2408682403c074041d808071076641001409200900c3c02c01c040c001c01c440d842180074031885988085401c507100207000608000c1c8041384400805c20904000d02c8010380c080d203416200c84038520a000503100a844800049040c0380d41111910300c280e03106078002018100400c0540c484c0c2c3c840303000030751001c1c000d14065600c4610f0600b49489619009000f8560100144117212040d0fa004003008501035004502405d4071a007080441c105050240c404070031070303484c0c0c6503112420000b07a01d0844181e00380d9424562a0405000380000071424510a02090f1030840e80c681c901d00805440300004c81d0021b0114100b80b107000030481861040c414003680c03d00b01140c40c8811500003c2c0380078504038045a1281a211084e11a4020360159030340014580c0000d0046a0f8030b0803030382c1c02c40c542c800401c90425613a5400141c09040785c0e0010740307150501800030000305441d902042204082218101c010407910604540725030 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 805493183 1250 805491933 805491937
    0x41704090c030e031305010c080d0216150b0a0e10180b01030b101b08041e05010e0f0604092c060601021e0706030c1101060608070908010e10020a0504030c180b06 71
    0x80c0c0111001180b01b42070500654045080f4481518160000d00c2001c1c00030380c00d880101408106c0c508421280d018500d00b47d0740075100c140310410041d00304003407040140c83d80e1618100740d40030140c00d03e203c0e64079100c00303001e1240c09901c04030724503908107009201140d0a0f030200000b0344081e07030b0520201090304280040c045981c200c000006450420390f07c600c0808412519601e481048150324155079404003201c3c944005180c1c00c030583c244801006150f0f00115091120346090b0340000715480c4010003e840350085105483c00c050721941c02c607511461651803804803002c403800394140212108041c5075100011a0428050f10407213072a2126104a1010703121840c10280007408401d00302541200a40100e5005400b0f204904220017151442070048034094100e507900d428440c542024000c0440445520001060745424028000e00c0b0012400c1441407444010260791034558040032a464461540060506440c50402003840c10b034941207603241c07444010040c00b03d450f9003002c0000c00c1c = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 805494433 1250 805493183 805493197
    0x11195109140a120f120302120108010b0f0111010b031207050d0801030f0609060b0405191d070e07171e160c0b0718060905090a0207020a0e041704090c030e03 69
    0xc070b00340000c2082d49010f400e0114014854205212211002e035112035070401125980004a500403480c070802580503840203006151050080c0005500034012400e5401900001410464560f00d0081c400509401c84104d120028048450110a03840c1c0800c1c2c94002e04803c950703501904440303d03d42d03440380454905a0b908104881c07445203881c1d480d00c00414a8901c101e0702c141d16000910041d0fa268807541d44901c80c480844020400003c0d003400484602c0d02409507521005031700c903a0a150000707107a41c00e851068195210984840d07000740c419812011802050030100e504012556144071007008182a0030042000952a41d40320742d001e1000b52004e20000030841140c12010a0b01a005240c0200c128103041081604062824040000e150000d0780416001030b420031881c21710308500d80d441400c0310011410b0078030383e60010394440b0841c800e55070a0040e850210f814802c50400c5541070002001109075142e585004803c0540036441521010a02c0d000c425111103c01104403002 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 805495683 1250 805494433 805494439
    0xe01060b0a0c121106191107050102220605090f0607020405100608011202062a07080c090109061d0414070311030c040501030c120c0803071119510914 66
    0x1103a5400d00082c04596143c0e1451644c01c0d07c9190b2091529410302c001d196860084001581d40c0e1414928400b0400c60b80144038410303804c11204000c1790b030b031080503100050000ca03117952052081c0000540a40071342d40000e0341c013525020070710007d0411040a641101c00f10b45500c929030781d0714221703101d1194074400041e4005500700804001f0070b941d4001c0000c4040b840c40a1800030b0349403030005140060741e400000140d031021040030624036190202a006022855051100c0c6080601422000c031341114010045900d407404031701005005c0340c01360021648503080317502181c1d80741410703402c2c0282e81000502900504032030f030455007420b0040d903050300e80203041e1498140c40c210789100c80c1d80380440c0681c2d00355107006010030b0703d03e0244000d1010070302805120843d44140400c10218941e224408110300031000c400700400c4180c03a04d1a1400c0702e00420302d10704041503010341100e10001034080c9038551210000c841c42241d81034907103005180656603441c034407522108001300356800b040074158 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 805496933 1250 805495683 805495693
    0x70302071a160e033f04030c060507020105120c040e130c210206040801020c121303030e0109180609110406170c1903052d07030e01060b0a0c1211 64
    0x42d5280108550194904090100c0d0f82c0d61018088030144500d03180034040420303103808000c0c202d0144508800081c441489030303280c503051a650b15001031000310311600007402000b00e100c500356802001544c10700c4002113514030207407908080505850b4031500071741c4142c0f4520004030b201095104103000300c507503110b100c40007d98201480084952a59039000c8030320603c2002100040c0c03aa0b1001d00010b214040000d138450109211240c2000d140990a01d4101f00c180840b0400d0041414204104c6e074040c203004d00c81c000a1801280d248901c3c0d0400000444007183c03c2610240369441841203034403107001003121858002b030f103141d20b2040380704400028131410f04500032408041c81d15a0031036610001245060402c3c00d1804081c40b0524516000c66607400170841801b40c2290940c0031609401c04100d050021200c2071900070318085c14850030103981e4881c1703180700c0c5130950182c03024004031510513071619090310f8010b052103000e42d0700720388040300141c45941481c0907032200c144c403200c1c40002e45 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 805498183 1250 805496933 805496971
    0x1050c09090a0905030d020f0702040501320301060f0806153114180d030203040c14010e031009150b090712090b1009140702030a0f02010f05070302071a 67
    0x4003d410b00c00015201c9000400c180304e00c070b80b164802000104000c090064032084540100011204140c3c840c007042a034903030201d00b805100f11001ea001c0c2c1070300604aa80c200d02038000c00c0c01810182c01c840742086240d480400c0e2108009035440c03007005402c01c81564400b41c0c0b03090001d06502415001c15428880143e241075044e81080c070315449445440c0040c0c4945021040060030b83c1c190381020b840030054100011410050182c22590f000600342946181010b988078420b001080c410b003210005c0140d10400d4981c031400c0c1400a02c0d600404a4042c1d00315413607210014100e04c0300032903610700441c260002c10b4656019110410100400345915540c816405581e0b0240401d800f90f0a255030380310500000303c21000d101e01a03417202d0090766425041c20b40c224103d4460502000c0428140410000910750010465450900a19042c81c030075a002400343d0140011840700c00d50703241080304210207140d050b80174008144c040d0152102800030b28040c548504020354503100f82d07046482e121 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 805499433 1250 805498183 805498201
    0x1c2603160f051801170406020c0d020114071d0406030809100c020d06020304020a0806041a07020c0f2110090314162301050f0a0b03070b040e0903090307120501050c0909 74
    0x1d11201040c100040561500040c171001180304030340c12202d059000c505c811580c08104200500c804040c0002c1004039180101c100b04c5000007040f203002c1044016501050540007454a1004400684180f0202d9103d10b0034404c69000040001e00901086800071002e501c158205039000350094200c2104184a40b2440c0c003035030008000781c3e0851008540000c8060040000510030b41c050780d1007000c080481e0481d5041410007404050441d44903812440b41ca41e60fa5141e10885101116552000814243d0b8011030b007403a0302410100f4011151850703500c000d19080310001d644240d17200c0108520b6440c0d008154010f10064480380c036a0302903141d00040000700c2d51000007414058400350320031811041429102d00f03e40010054100101340003180d40c0e01d02401c0542c0324102d018008030750600e99059040e00031403095a6040801c5008280140014821100c1405000d0144d45103203845c0e41d0780c001c0c40011404200c1303080d0f180c600024499000f0106558154200400300348654442c0c8542d = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 805500683 1250 805499433 805499467
    0x120a050d0c09030f1a0106080127150807050a05180a020c100207060b04050c030c2b060806040312020406050307110705030714040b0405061c2603160f05 67
    0x71a10a2092211011001c5800c0107403408040703114113185a20f6002e440d9040200f41d1040c0e20180a000c45440140908990300040c50407072000c0c030b12000070343c00c5102c9a00c005842c4101d4000500301e174014001c141003001195980541d0401d549141a003a03a86003800385000c8084400c030021660075010030030290030384d0000c00403081c0303180440d03d03020110030480040764040700701150056074810040480303043c140a182e42c0103690f10801c60640c42d01c030b21011850b1082c2d200c04050340d143c00c004101a00d81c03991502c01011103400c01049030645901d005961204292400d0740402e01401c0e400d15118450700845042d290a42d45d441d003540c0790751401b621083c400d012840d049024000b00440c041d2810000744e0010a5504030041e041c0354010240300c11104255200c0b4060b0303080000308102a21480101e40700e4040e004440381c4105814102490810a404041d00380000b0200c110428403c03060043c0d80151070020390255010501c9009480c2c503010400f401c00410170034029400c0c1c480301550307 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 805501933 1250 805500683 805500701
    0xf0d0503160504030204051501030b030109031b14070b07021305100510020109060f0501090c09030506010303140f0f030f25081e0405032212060f1113030302120a050d 73
    0x20b100d81060b807a80d00180686504a581000c2e0441e41d1070072000c55a0f05000d644c40048050300204408600c949008000d03080c2d040a54054403040c0c11a0300401550707040803d041562041038030340c0d198031200c0c8204540e05c4080181e1045094455400d6828103522400340a02212210600c4c0240740500f800505005100e010303003075550f00c2001d41c02159460140515014450200103400d42c14042041d00f120040003040c41004810030007400010300010f9140d05494160400c0921341c0c90f8504018468882e900f009846910007040c07000c45c00c07811401441c0109a8141d11807055581d268030a0080850091495401c81480c060400001d004516480d00026941603410011030001c000c0c1c2c80d10481035404a84a500001d10481d4480703102d00803411648a61240c44103a82c03400d01e00648000b400074003e010150f03564140103604d21160320281c3d408a900703c8c115128404101c038022004098030040c0c0c054010036040554207000b00007124215035682e02c40504101c40d500e40c4c1002040312030 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 805503183 1250 805501933 805501937
    0x180902060d0513050d0201020708041412030c010603031e02030304020103110912100f05060108041202031c050a06060203030126010b0904080c0c0a050a05060a030b0618030f0d050316 80
    0x10101e01e42106008481c42440c0311915105a11600d01d40189000b441c184100b04591062002c100029201c408440448200381e0210061000d2900010b00714030112a401c0c1841c800001c0d85143c02d201074100310212400394445400480721140c00d0008403201c1340032003005070010000500158002e5104401850014030702c1d509288444002c0b8210150200f075042c03155100000681402015000741d4019542c0d424081c0030504241c1c001030402d5101902c014030b450084c4056151091081007035808658441e4100004041800b2041004110a80740ca1048604022004c22001e0000040f80d04840814a00c40749840601d802186c0448011000000954032900d80e41d041d681c40408140c003d42c01500d803156907655480e16076180000200c1c0305805481c203910100020350301c01d8001c80468805403041682c42071a0201100105a1001501da2010003c140c9404071280c07c806014944401c0d41181c8000a220360724075914980d920400001030802c1001540c0f2103000c00030103000004074 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 805504433 1250 805503183 805503187
    0x4150c02060a0e030118030f0f11011506030b04050402131a06031602150103050a020d0812010801231b2b05040209013203160b03040203061018090206 66
    0x903500003000c40d0b2021000200292aa00f00480035203028803d60b00d80c00343d100c1c00421114484c0d44d02800c52030005c010201804000301c20705000900031800c8011070561200200302031a0f045a00c071505100c58003807100000e180c040d800151342414465540515001028600c50004043d11000030707203d00000d049027a5000d480800f0707940c59400182d03005030b880b600c5410345c7c04881c82c00203292400249244052159920040001c13502c040761040d2040d406441030240c507411420844910700c1501c07005a4904112000040c3c448010750100c4c0c00600c910603100d900101281c841300503168207a80b1410002c01c00c250402082405400800c10030403002d0001d219810000c8410304030f02c070064030100c68207841d007081108518012a440f400341014043c02d00040040c040e08203031031188038030046031103100140c2d107907115074040212a45a031481d610585000c0e031501500c5580f82c0058404a000e4858007000c503001c40d9064002c501036074151185901c2c454000785988025042d0500181d17000841 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 805505683 1250 805504433 805504457
    0xa020715050d06032d110603130b042102030a02060a0903030905100501090c08011401110f1911030d050a0c06061206140a0b060a030b060d0504120306050a05060415 72
    0x42c1c0c0076040c000d6005425003583c440082d441c0708040c01c40030f1150403100c01e42c5003090000031840b803500841c500741031780e440780c03030381d440007030410120240a41c05011502c0880400040000746804c0610113180303500325000d00d01012a05990b40d01940c451303079015030840c00014070b05d00c3e5182c0c450700280303029240100b4203102648400e4203159503140c080050a4a0310010f01c1007036a103004404100d803c1d450903008561404212200036100004018100052460413a0083d0401c11a010700401003409883d080340fa41d000000c4145400b190840c2d00300c0504041130a07518020591450000c07450321018500440c060b0100c8502c0420321003260016514030000c00c00241d62507048600520580b00040c0d00c2414400844240038010a2420783c0c1e410700700390300740c44c3c1c55110944078102c1c001c1c14042000a15200020002e0103100344259040f40303840204024411644000c40c2e0388041d40d202000902e407a07100f800010240b1340204c540111040000304042c0401b451000d1502c2194035228000c410 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 805506933 1250 805505683 805505707
    0x151a040e0f18031201061805040f0b0103050603120406210903030603031710090903020c03030a0206010f0b070b011a070507082a18250804170a02071505 67
    0x903500c05420400001c104480252001c00c48000400c6000056007401c0d02c2c01540d1030a00414044c0b1810000a4146059038a0b04c041e00c590282400910a208004140b045a40188051400507000034200b0010a01c0c47c200030880d080000c000c880494641428042c01342c480c0e59040505100c04034090f00e0001c03e4603c64403440540c0c9206c4e41d00820400d01d9811f0041039598045aa1450502820f050000c00c00307108502004817804280301041d03140b4141026070910384041807981d00b40c00005141008503501250f501d041c0ca940c54500400c00c0e44405002a090050300381c0240340307024280041c0102c8402000004003200b040e84903030b1a01800c0e0ba502800c08440d584501d090364443c0071395020181e9030701080c80101009034540da90b4801030b100010b1a021a00d0103109040e0441c83c08501d0400740e01e1850107140340c600c3d10408000364024001001c0300e004035400c0c0c0760500c5551000d60008004801c8407044001d40e80208205800d0400501d000d500e09454907040c0311040110180502c = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 805508183 1250 805506933 805506959
    0x506011d0108030a0206182d01050c03150d112d0d11040f0212040b07021e0c090705310803040501090603050705070c170f01151a04 58
    0x590108105000308804200380e03559068105410700d410500400345030540c009031031503001810f540000c00700e04001d46d446007483e100045811044100c2d00000c9209030701b480549410440c004000c001943d12900071502070301083d922400000c034911850385c1549040e5203070140c903900540f80103440f200600c002400030f460400c802264004c4400c00d16000105d09000c015403643c09551000710310800e9940d0014900b5040c2c0405d02c203c0e51a00440d2158080d541a901c41d01806803842c61141041e0a00c2d150080089488030018402c0c0c224048203084504000c45250f00c0c900c0041004004840c104401707000c0040c036040405c4030520144000428458035a0789200307a40d810340101000081e03061803819a16004888a40d108200401c200e9a0102c00c1c00200d0700300349000103041d121500304541d184980c0901514901d483c0c000481c0b01040c2d0b58082d00710390701c03031012500117040c803981c45820707070380c0440301404c2c0482c0c207010030400750440181e0040c84d1111000d405240c00d0316056081903031 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 805509433 1250 805508183 805508189
    0x9231005041b03050601031a0d061d160614040b0c01271b081e0c19180e0309010c021201020c060702100e030405131d01020a0e1e010c020d050601 64
    0x9000c068030b0110315a03406100d1160041c10a113010b004800081c06040303120098612101e0140d50351002040500203280e01007050341c8000c168034140c41c00302e1011540e03600b03039404072424920201030001860a01800c0c045501d0009071503007504151038035040c0c01d066004084e500c8180d5480d441e49800c42d5151441c1404000b0b810301c4001d00e80190350400c20101c441c01d0880391704000032207000744840703a00080c0c08002e0790510340081d20220a042e03001400c1000b0140059080311144d904891400302c000401c1041c0c0d40c40b10703019080c1c2d00006114105485510f0b181c1c02300340d0400c00c070402295102e42004c041c0180041c2c6400c4056940d80c0d10182264170031543c0d0729403600710600380400b05a0511603a0030050783c0303150520208110022045e168881c03485814860402e200f455400e481c52a042a110f00304904160041000110000741c041d500000d401c0d400200c3c00c1880400c40e15044451403025406030700035030032005140c2c0c0151a1142c2e8410140c0e4440b40c0e440505c000140204030f60717400303 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 805510683 1250 805509433 805509461
    0x9060c050417030f090d0f05071d0f0402130f06050603040b0108074a0f0105010f111b010c020d2604080604030e2d0a0923100504 57
    0x38603840c2c0700050581d242201811051500b0400c100c480c0c009404094841044c001c840a00e10f003909890800c000b6402c100340144280200c000000d551607000c0e0400c2c070300b0343d4800d031212540c1e42ea0360340c0c004000300308440c001c1d0f10080042c7c0c00c03104000179034400110f19000003c0041c0d5a5150000151241c00444086508880c45030041c40300440c21b10440c0020700c40003c03403e03d03100344d502e101541d803415442042e0030091800d240c190001004841e81180140038800030703502d800e1001030344900d4102401460f01084410503101907482c0318012030b5000c00c0340e00380907003a10f030300ca007035131140f01d0060f41907642c104284811000701603910b8212554009100702e1205508400340048062a02195516442e03030143c00d0100300049007020522550040d80351605039041620b40d40003483d4980e210641409112006000030f145801841440702c020340c0841c0e450076055036503143e03c0300307445040d580c2501c0302c0c145111100c1200705a80c1410b800041c1d140c00d11031090b807184080f404a070444129421 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 805511933 1250 805510683 805510687
    0xb07050c10020408070f03021c110603070302070309141e040e0d09030501050c1e0a0309051b120a0302031c021c050a05061e060a020a0b0f01171911030109060c05 71
    0x402a802003001703c0040c400584a07610341441c507000a00b600012941365031517110103003550070402a10711345008185000030002e0303440e03082c02507004000750840b40d8110049084400702003082c1a40780f00d0010a000028150310001e00007966019034080341d62541500a603d43c83c0c034840c641c0080c0300310803a481c8250741c1c07030f40c03042e145060484c01d5803c068110b0f00c4c130b1182040f804001c00c080c14083d1b00c02c0342e80500180c0c0d0710744130f0405c11402050891409001801014140d281440396500b44d1158140304865800400c0d0240041c0e58075103540da031000b40580d00400c191101c0030350852903005940081310005040a06502c33440590000605002c816140d49100b041240042441400e4108070282c6000321001c0c0005801c0360104800203001303204800108180d90308038400c0040070f00d01d6501c0001030b1001e05018ac2030282c094000e0207201c10024000c000071504900008004240e10700c01d14884512200c03680740c00c0c0100c0c424a07460741c0c140d500e4045041c04141c00f801a104016016500c40da = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 805513183 1250 805511933 805511939
    0xf0905250807060f0f05030106050f030402030c040f020d0b01031112040f0506150a0b1e03190612050111120c0a090b1c180302061f08061f060e0d0b07050c100204 71
    0x10500101c61170b218051000610043c051194020305a510100100010035500d8549000181c541140f03807084d140d0050405020940b100b03460703009412070b0403403c0c0c1d05028481d0400015002c1c0c400704841c041103600c0a01007a880a5001e0042c90b40050003000c2e00c52142c049a1145824440201e076403004007900c0d406011514100815107000a007610701d040ea05100160310910040c007141611010502004004141d01007800c894000c512044c080080202c1c664454400c8190701455205544d55481d2000c42c01d4001c3c00c4004451802102c40e60386074076070381d62002040254112201e10342c02c0108050020403c22031020081000340900d10b0b51010400c00c00c0000029070300d54220340c44607a82031515010001341c0000303030701c2d8100110b0780e2483d4a0043d84070100700807140c20390005420b481540c0034045c840d00305078507406291404210401c0915143c86040c1c4401da5900903641e00400a8070022020030080100c0c65084112450040c1c0b40c01c08140302d643c9483d2030341c18281c1c00540e00050030 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 805514433 1250 805513183 805513187
    0x201200303010f1a0304030f03020c070311040501050103060305070e09030d0608010e0f1f020c0319050418090c031514101d010602250b0403030903060f0905250807060f 74
    0x11200500b0203000b540d540700c00440004c0032500000c0c000030144100207090f64150780c00b07601614900da4000007120500e41d620305141d0b00060500402a01807440e000021880d0b51003400383d07100b6079400000030a01540340201c41040010003d145480901040c40810740d22200c5001d103a004006481c004a800214500c90303d0a1820900f1907050923440450b00300003040d40e110b110214410508001601d5080c19102daa007144103440070003540800e0499910380d03a64002c405007094034006220352640c91401006d400c101c4034003a074003400ca081403202c00c0000400484280ba4025038484002c20b400f000304211207811441550703658020340100c3c030181721012200400c14506100701c1300c94129940b6048004c0d40341e2000140300b41c3d5026031405402040d9440000150003004503080340c079540d5507071b81401005040d41d03001c00c40d902400c203200300c4000845030140c5000543c003c8045c00d02c0c4042081600c02400e04260441c03200b61144500250080c8180061170081c4442e44400902c0c0c00e0038040 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 805515683 1250 805514433 805514459
    0x20f0f07060e2a13050708010e0c040b070b06040905060921040e011502070806090c150a0e0603151c120c030509041d0f010f0c09060813020120030301 66
    0x700b03500b9400483c2d5050309a0041c0d01a45411802109030689940980081484256200f0034000310b142400c080c420502d07400080d0504803003640c440300d160341d1140d090044051285210300c5641010a00000b00410021205140c01c482d0003400050202466030320035040070704c100d85400007034009030b2742442840e0703c4a00e01005003c2c0f0000d00c80c9014200851200c1e003030701c18003495021030140c0034800c01c107038020800140540051000c0300c1842c6480403440c0c0d515509600d13814029003049419010703440d120425203d41101e0760b01d420583d0b9070942c05020458000401500c0600c001134401ea1443e01e58039062202c9840d0b43c40880503181d01414403000e8038031344115050800400424100110794031105440c080f900403a00421050444020002c1c0c544412080000310f002d00f00d400102c5140540c009400307240074400500007500c544205440642075403003408041001c00300061823200101e070316074100302c1c0b0506040c24404220110010380d5020700123080740300e510000050000c080c041d50 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 805516933 1250 805515683 805515701
    0xc0806100e060a081b10090b0d0504020f13060f0b070308060127030f0b060f01080a020f09150306040e0f0d031e020f0301140f0105070605040507210b0108010b0d03050d020f0f0706 79
    0x90800c01c040c0751620240451180d9270565405a61f25000714045541e9030144416580000340f40f1003905900d18200030041009208070204404040c0001449032190400d4803115501500ea03002d079643c0d20b00044d030f01141c083c1c03500c014054030110342c0a004450f8040c1180914040d17651030010700420303d0141301c94103002d0b0401e88611600c2c2c140c100e01c1d03139000740e149520031034400c00582c80b8a0960300400c01030044807101750b400101c0d029180720a244407400307103119110440307050085083ea0b46203c0e8481504107403121050f000404075107440c0740030b0740203141c10106000113842c51051144449049820444075041141300000c010405100c0383c480d04800c07113000f242c0d0b171440041c080340060a075104100740244145d40303400004c0d05000c0b00317000e24001004104004840081006080380c0901d14507402150142c10403000403510a4051180c00310f50302002d08500d280e00c1c0036032002d8425410000c2d2062449070200082040c81c407081c000b51003a10f40740b104d03903900c6611a107090019604110 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 805518183 1250 805516933 805516937
    0x180e1608060604050d0221061303081024020304150c0201090801020301080c0f0d0b09010b031e030f130f140111010c17090712050a0c0806100e060a081b10 68
    0x1000610583d40d500c0001a00301b681120071008004c05c01c1c0b032007201901111a0b003141401010104600020711503d00e50a8910a40d200c40d800d070741c1e1401d48031a507646030041c0351034039801c1a880500341100110aa800c88494011039060035911008010010700e0400e0b6000011000c0c4011011542c00400307600180546600a504540c1008130b500e540c0c4103c000c1c2c80b40310306413030f405024407074403074148071070203680c002a084d1681c0c5083d9011501904004c648103000e841005003c40281401300828009240b008010f1490301c404840d022940e6000f1210f040380d2901c000b06c2c0000c49220301c00c0c041c8000c01d50202d5a081d00f0030327114005420f240c044200c80c0d601d43d0410081400340d039070201450450915003e0300d41903d4840b0740302e0510705032190b000640d81c101105019010f00000247c007444c0f503882004110a82900d278400651600401e807582d13a911b050165050000184040d0801d50000020340311461040e61440500c3c6400300042c03d5880480c50b2421001c240e0910311a8400d03c04818 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 805519433 1250 805518183 805518187
    0x7061403010e0a0903030204031a010f0801151206060e1305071409041b050a0603090210050c060c1e03430305040813030804150f0f180e16080606 64
    0x2815a40b0900018a904962503640c0c01c080b0802d40280c0c140d4000c1c40e005052441040303804201c51803060801c0c083d450702c51078007500020701d50005006031054060b10f04540c0c0303005842c140b00c070900030100c05001c90302c8a48a0b08085010b420200d1964802c60307411b107c01d0102200c83c00d0003401c00103a500200410b01102c44d00c2142030700c030388200b0350300580c0c0040440510211890046008410303500203681c04600704100041e0f0030750580012400318000c8138019502c0304540c8082d03d4500c40d1050208991304074500003541540c48030b0180000c0740b004411540000c140380500320240e401103c030312400840401090380300c440400c19840c109031014105144101d80300c03c0b0f6124192020112204164403100002c0c00c11074403000b130703440510054444010341a00c03840c082220360024020124655405404500b080d40b10314100341d079a0800b0303142c1c01603a0030350103022100c07916a40004030444dc0c0c00c9100081c40051200038900c5002000040c81c02c100000303c008000c0c11000d01420f01c11641 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 805520683 1250 805519433 805519439
    0x20a05040e1f15090b0a1101180201020703020607060905011e0e0607090521011d060c0405090a020307050909040305090a05060f030c13080a1506060c050c1c020607050706140301 78
    0x708103929003901c40e040d040b0b504041d141d00086850f400d10740c0100303285c03d0002c6000c2120540103032031107400c00c401174001c0c408594003c8810b4920161a90040d005a2000d10204003608002c4010300031613010702c00c00b01e1510a0350702e80909480c15901000360340700021104a08225452181042603400c0f000504102e0a0400006007030b4081e074095244100e100401010403a01e01d0340c1c1c69003149141c40003d0000380030340102c0112503591458a000079000b002c0004061614408c01c480643d000144842817544804244400035000140780c40300f440420032850b04180c4c0c9010351548a0780c800d0703551599a031000002d100d01c0c3c160380c0c1d0100303000759003e001c1d0f904016224000d581d44a1089038605480301d000300f070740340603400c590b80c040349141c014200a0414440c42190252030940c0700d08080c48099a1000101d401540088015089400405001e43e00d480e001c1c1c540442014005801c0c80c0301030305034001490640c42480129202c0d844081e080003100d812003404c8005100d618200b5003503603d = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 805521933 1250 805520683 805520731
    0x90503010504050d030203150406030b0402010305011706070f03020d150305010605040b01170a0902120f19210221040306050f041e080f1b011a01090504050a0906020a05040e 76
    0x100341113403501415004800034094400c40d1420f160074500040c42031100c3d40d943d0808100c960b8090720142d0000c1c0c1810004200c940c43c1c1b90f92a50b0f41c004060007000c641c0da4002c011203030b1241e203205210805400704600300380040340d402103211b584100c1081c107061501c2c41ca041802c4641c91f50140b40a6410000e4201d40390ba00b04400d4492807003080b070300201954501e880c0000605115400a62051441c500c00041e600300081e01c1c803202c00080100d40c0c5000901d80400e00e038502c9201c004003001e40c00d0708490802058506400d56000c03482c011690b000d803040081520115044a01c0803007500d002c1400c2052005038091075402c001007220300c03845400d294450f00704d291302058503c903452a081103d1410894888100da034900a9290402d44465640b82c11a004090000700d0703200c60740c01d0882e051900708501e00c110101007816110a01158a05010310001d0a001070039406d1aa5450f003c03000842c100d800102a01e0901e40e842c02d035182d04028220034114006007201c41d01400904800031401 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 805523183 1250 805521933 805521943
    0xe0313092003060402160f0309050405010b0d021e041d011211120c090705090f120607030e011509021201090612081602030d02060702070504050408090909120f030709050301050405 79
    0x4403500e20341c1541d07643c812010501921406000112100d4025010028450104090280035100b0364446040340d0340d980800c4283c40e000e00448548110070021204042145c0d402445a01a01110700130340400d000b540610a4101d0b500c441a40c40d03008090740100d0f0301c2124800c6c090b01420a694101015a840b003e0b100d0600300c2050b03010344100203428103440d02c02c103c5801c0303d800040c03104c02d203450f00107070040c0326130000132000380103805c12000c08c0d200c2c2ca00a0310400326030450000818281c1d0b12a00110301811900c90384a41c90f55880c2039561a2000d500d0700d0030081d0003181030150307075404a80a034000b5030605074050070340185400303402c4c801e280c05901801d4005810011890700d5680c85802080c2001150a009500d4461403101c0302d01c0c1c0d500403c0c61480b40d4540d4096482155a51082c4019100c00300c0f4002c1000c0c20400008925103004e144042e0450640800c940410319014400f00ca103500415051070700742c0011042002d490760129140c030150105500034072040c14607540c0e0f981d0310 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 805524433 1250 805523183 805523231
    0xc0f0b1602060a0203070f03030b0907020118060c030608101a2205190f0608070b0a082706040b060906010e06180609041d0d0804020a060c030903060e031309 69
    0x5400b0026000044a208105540070560440c2d00c08440400c246405001070a0402050b402a851280055107042c0184035954100790058450400104266034910050114000c1d0606255441c000480c010340108013900341d000e00d01200040c0681c10401041040c43c495071594800c0310790400f034071000680990021030400c20707a800420681c0b030f82040c1d80250004c3d24800240d043c5008042c1d9001495a00300e039045551100c2540d100c2c42c0c540f40300310b0051080d00f007001d01007a91030021646003030108907108580c07503504030010384400b5568461410b10500f03503402d4800940c0304007030045910b04621450303007188003428a4001c1ca894000410701ca800350529458070f400c6907205841058680c80212405843e008208200c440540300392000404507124005030f1602c25100902e0459004410301406070b40c00400791940c03240707040403c492600540da022001c00c0b00d10403000000034001d0041894200304000030f507844a40f050f007644ca6104060b8400304007541004446c0700788003110490036140e = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 805525683 1250 805524433 805524439
    0x50c1b0c031e0307080d2706150605040e180307030207060206090c150901200102180d0206270307030b01080c01020d0f05070c03020d08120a060e0105040509190c0f0b1602 75
    0x1162103c100c600c006185074200000c109402e5001f407100c02e900220b80d402550310442c420048410b481410b085000c08d50302032140030032004c0105000a0440e410710b03562004141c550149020a4260b6507800d6070403400c01203016030302010080c0070050b01030190a5120101c50000c0c07006c440b000d000645005038412524000c1c0f2000118a1480d034030454450700021100e04004810a40c0f0b000355a0007940b11100c0250f0034075003040d0034080c503d060003200c40c119400034109418081040c0304401c0010003200045a0700d0081480c1c2c034083d803400e00c034030be00035802010804041c0d89001245410990301702c01c568115000906607044440c0c01c204400c10f813030070740d00d007590b01c4482500d00b140d03240506070006036002540d9084101089a181c00074201680040e02529007500e403448040156540750040c124602800001403005080c00d80c03156901c044188210740c209060320411458047c60500c0070359011000740002d1003280c0350101c0110050100580c41407500c1c1c092003d0b4007a09401c80c2000384 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 805526933 1250 805525683 805525687
    0xd14150c0f160f03050301080c0f10180906030507061b150e0a02030f03041e030308011802090913020906030a1e0807081c0c030b030a0303050c1b0c031e030708 70
    0x1881c407021190444100743d018500311a20802c03801c010303000d5002445003403500c0c4199100c028250518007600361100c10041c0106014404a200036a255050300c058803689031140540007905000d540540b000070340c002ca0240001c1c83c1800002442204c1c0c1422280e1490000c906001c001810105050350400e41620001041101d0100181c01d00040744806981445007004075070342c0c08000300060085a82ca4403910380b00041091110690b60f4540c4005030100d1119401005402c4100c06020340f250040d800041c41d103180e0200059000304141d0b0120151a115030580d01141424030040f900020304800520310400f05650300540d070340c0241c02840c0f10720f9424040e202002001d0f8140c3e9000b41d80070b07035803a482c1e0f20030a43c41d400700c820090141208a00306250740c151640248920340308000060b000d040761010548055000c2c2c01c016101d0040302d142000440390003924480c19000c90858a80900b4440009030101b500d4001100340b18100d140c051110000801800000c69400c0d40d40032911507 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 805528183 1250 805526933 805526947
    0xf010e090c04120308090115032001050d0207050f0601051c061a0307120b070309080a302003060904030c0c03061107060e0f060a1a0d14150c0f 63
    0x541c6005680c0041c00010f524001030b002c05410060703851099000100070080311651800c02030440001c1e1002408603002c0552810300301c1e20051002810800605055140c801550f400f20b040380c7c824082507840381c008040141d610141840341c0c500401086a82800c210790a10301c40e100500c038800e000305019034448401415000386020481e200800405071441ca59564141e01d0000356035603022110082c1c28030020303081c98003912400c0c40a40d0001d10403410a0100082510104042c0740300f40711502c0000031420380c1148014041c4110f0034141030100368800e1601ca228800c595074010340b602c9210034410020a9100c0000c0c0c2e80c0d2142c0c0525190b040f8442d01c0c28941d04010441e000034001038103080310300c001d03110241c0050074150321510302008480e101851a41d100c2d460f403040590380760002c90200310018210f0f002032282400307000c1c8081c69070f00003a0009800080c203000c01c890309001c00c403100700311a000340101610002102d546030b20303e15108441208910400744c0c1240341640100b449 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 805529433 1250 805528183 805528201
    0x509070501140a020a0c08070602061f030b0402030c151305060c0c01031d030c030a0e10092601020d09110d12140c010c0809070504090302070e041e080c0c0f010e09 72
    0x81702c269400608142815880308200d6855641e07074001c1c103025118010124412034030641c0076001b02d820a024030380e00755055988084180300b0152040e64140714034540b916656544042184c00f19100a54050b070705d0700100e0408180445513801184524014400740b0220785022580800b00182480c0005420900c808079451072100c0c505e100c0082c0c803001c01c105100b0382001004082240f280e8445000101c110800c02c804815015140ca00054070324008108070780260300441032521490324440700003180b41640e01d003280c0001518044081d02c84907440103004021405801c031800507034031841102000d885041800800030120070801c03c00404003d0201142c03c1030380c0d51808940c009101643d034081004004200507561081503015106000406141c14401c62005036410740150030308034504214510400c20040c01650b440304040c0c106540c005058005544141c4941c00e125120006400118a80380740c1c50302e00e600490700c400718800d890f0781080c64410200000c43e0a44020b90b1a0218 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 805530683 1250 805529433 805529443
    0x171605030c031e070809010c030201020d02120415060b0a11010b0d06020a2a0204020c0f0d050c010609050105010518130f06031718010815030d03020d0509070501140a02 74
    0x1421900012405407088240800141090307000c803255032079800e03ca108411a28461010b0041c8020010021260113501403a620700c00d5a00a0000504007005a8640c500340c1c0e0164054903080e4800e01b081000304080d131a600840c0892007407081240030300304000c001e0144202c5428106003d941c41308c0b111405400d400801c58510060326648440c1c4d85490641c001c0c1d006185035101240c0000d100120b030f840c4403031100752112400b80b0a541044100c0d028040254003815002d1400d0052008030311159804011281c503408444d644e144da80c1410b0b80ca01401c540791600115685410f0000411142c3c1c0d104060b40c0d09610200c1100b900c4070740603000181e0194829840003181030410301800350360810b81c0e0106003107030301801c40140242400d50103e200b520070340310858582203400d20400c1d0f072035205024080d88100125205803400c1e082000003458001e0240011b00001c1d000110090300101d0781c02003d40010404008000623420200084e000c00e07490010140c03000400704062103a5413003001 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 805531933 1250 805530683 805530727
    0x20a0618052401230315011701090c0b0706150311091f03151401060f090e1b070c0305010207050a15090b06010f0905040f0b042306061c050a0e070803040317 69
    0x4403106c0c1c02080c0e400c803640c0c0d4024428600e401001444402140300103014519580c0e038021122813074281000c0c03c45209030415070b02940d10941d40c900c04c103d4500c901c1d032031101a40c000c04144a548208604010034500010202c2c20a0080d2100c0c2041c604a0740d003060013525442070541a2404640c420030b001482c213040c140000784500c4c80005205600564074200804550703840703410380b589403645036103205800e0711100c0c2030382d0003154454845c00c42c0301c0207410381d14451108200c10580da5101c0320300703a070001901030310260031000d4240e042061000b0300d1008000360900901280c0402e4a80f8880710300e0041105060005541542c050304e8492000540130f05401082008452800d001200c000d000345104d0500803480c00400044d954007509022040001110007050560b641c4020720080741c00126201c400c00d180c01600421410180c01068440d119480002070203a003440ba03201d14181c0d40751b020944c1c42d001000f09001003030001c0c1a500310345010040ca142d41c0d104001c101c40d0583c0c1004 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 805533183 1250 805531933 805531939
    0x4120c121d2808070b0d0b03030702030a060506010e1f0315050301090c0503120408030a11070b0f0d1b171f0605040e0901020901091203020a061805240123 68
    0x204040c50100d22852041c00d11098080071000315a8444000555030119130160203481740c0c0c1801801070594032030b04013181e90301000e01540c0c1000d040d51b001c64609200c0e0501201c850303032998100121560b1082c100c40b100750046440c001c07182d11075011050303c1c0000340740040805856034030218030514540d00c55002402d01038001c104001190402090030289030141510a01412070701c2003140c05044241c0e01581d4100c03001c4e51414030208001d407000c81006464512500039058001081050395015113104001c0329103150741c941000010004459140b03c43c400780d80c040b81704d00a01240d124914500c01d0101d07086941c0301c0d0716256001e0840319401c043c0050114001c100c08641d8a41c010701600444001c541c2502181c0c6a4120075403c0c0d02030080e80c54001080c40f0410450b00c0311200213078401c0d50090066502c0000346860b10300950382c0d0350481020004585c5e801d03804010003040380e04003949510b2503684c800100b81c2a02050202c061042190501c01c408038603007490814004500040001 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 805534433 1250 805533183 805533199
    0x170307110120030f07060f0c0806060307140a030504050c041e021c11121602030313032304051513140604080327091603180212010504120c121d 63
    0x21300000202c0d80540411a2980c2c240600e6800341c00c03081c041c50244a10a880e514516690101800b440ba00010451002c10050604401115903800018242035407150b502240500e0281442c5103042102010b03540070302d11341811145000401441c1031281c2c080302078090fa9620100c00031206d90104000c40328111807400c0700c1c40d2450700c1d00d1002407040815903524241151788003902c450900344205c05090240c1c208200003180607500c16001802c2d1403190401d01c40d1a100c2d01000352112001c800c4400d50400001420720007880d06c18240f08220307031038030050351401c81840c840c0100c8103158814a11420010030141410783e85d401c013030720041d2040e20112921500c1003070001501e18554005543c241101943e850184d00344564640d200d10070161602c01e8944000e00d08600600c181c20560b030480700c000b01c1010050741c0c1d03202891310900142c40003090b6400e050a00c0a1031488801c030303840c01d1204d0b82101e1000035440d0a01c2d880201ca0b6400c01980f40c0840c1d2000030005407192100c66405050 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 805535683 1250 805534433 805534447
    0x201061d06011e020d0c020d05190212010b0a0506130e10030b2508060406120803040b010504060f060e061204050f0606010e210703061517030711012003 67
    0x280540601c914026030300d143c10760414003200060039a0035480000180c0190a11000d16401000580c083c548050403000a0031025190f117801c01c102446d00d0f4480c00e8a00c0b24400c15460022300d402400801c1c10020000407525000184094505100d01c03400b818000c1800030100d800c0c0b03100324000784550520500280707860300800d81d0103110740c0400c45492900002007040103030a500703038444107004865241c031800182d040c1500c6055001300b0381944540c8819000c10000300a42465500394402e60103241c0740d050030b103008600108160082402285081d000300500320078044540211409410403140c0d5240540c08200640302e08000480c0944450050008100c000640640790300120001e1390440d4480c07800456440b0fa07807061740c5070312111000c48c8144840b81030000784020340d50340044032189580e035910b40060340d4400030125140c815000301001207a204c84050b03549c0c1864200554a05092507440c020104c64140040381040824800b120032408090704401c008043c0204403519448 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 805536933 1250 805535683 805535729
    0x106090314011d070906060215010b0304050a060c050c01060510050708071704240c02010e060c07090c030b1002030c1b03100906051b0903060c0703020a14070f05060a090501050901020106 82
    0x13010b0700c10004a203152420005405201107241c01e6850301013400b0b0a130b6a440c062040c5d42c1c981000e007050b6800e0241c2011800001c4c954450360882d5146030f225031351100c10402c651400c43d4100e520141c0036054440200d80006d0b0b002d03080710341c4654041741e55a242d8249060400e1030080480313015070300301c0300041d0100d00380c1c500b00160604800320b1025480c640358041c204481c2c4524080001f400b084a00560700602c0c0f400744003412002d5908800c0340c0006aa42a00d501559065000c10b0b0100e0380c0d46581001e01d051000200800d840d940c00118544203541d0340d070582c1d0701c6d160720500700400401100004c03503940901040000880101090043d11200d04203038000344130954440b203104181648c03155108601c04103640c020040240a00f18035540e0080106850307012110403021802411a0b1a00180840c508003108000035002040005e08140307001c100380c2e03080c2d0031680c407884060090f1503076240e11900c2403040e164280b034110b451b821410300603400350145801c00013104841c400c20a41030300c = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 805538183 1250 805536933 805536943
    0x108090a12120608150c090118140405010503070b0f0304020a03080a110136030201020702060417010c0e0d03030b01110f060a15050303070305070f0b01091a010203030106090314011d 80
    0x201040b10800085079580c0d201c6545a814040c030840440003107000800604000e000f801560740181404000d00300c900340410402c014a400000c5a01081741301101c080c00d09104045c05400c0640c01062000e08081074000240644071012a042c040040003c1c115260354940c0301c000e6502040070317901e41400c50740207080d007012407150754420361901c071103030000049642440803031202669203140c40241203074409100f41c56041090b8190b6408200d501c00507201c0030000c200924006105030000304500a0013425140b4600d02001007143c0d0500f1010141d6411407090485c941c941400100c00c504100180d80d1185014103070a514080c2e180840c0c900200801d540d80708031402c210400844941c5148085e42103440e0081680650060118100190085c4010404a400340c078054401d20b10699802c4138502c0241c2100b0840f40e11520303621480d085c0030b4856400352000f400039601715070510f10000d221b030855110103482e6088015100302266802c0d0b00104c1a0f9805d19920a482e90030038401035950 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 805539433 1250 805538183 805538207
    0x30807031119021306050604230a141c051218030604030807050c1f1a0d02150f0f0d0b130e19050f100b0a091503020108090a12 56
    0x490141034107406060404140803000140d0940c01e807640100381d0f000d0100c42c803048401e502c5407580d622808541503459001400040043e4001b81351040e054030100c0c501080d185038817a010348810319041c081241d6440d0550a110400d545503603441105042d082131030300c04000042d16a01031540b0344141e0012842c014580480c025661246620421044c903507100300842d405000201d001d17000c01c80c03a07480b850003810b0101850703007150307620130b80805550340f624080800010030300d940e005030401d03200003052100c40149040380d10501400054002c200c0b0341c0c886078140711240744006490003250783c10f4030585d04890b01500396140c5035100f003058500241410a049440761407808060514034040b03005134802041218050014400005543c0d4035071008a0021689800b81075091014030b5010040c0007400d03500300c440425000b64003421700001001c290810f440306400e1510301c44d42521004400e000f201d50a2034010314a0355090052410142030b44170051104c1c58400010040076030110302140c2c4 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 805540683 1250 805539433 805539437
    0x20c090c13050108130303092109030b01050409050a080a030914030a0215070f0e0a0b030411011d0114030c1306030603020117010501020a120306081005041a060d0b06041503080703 79
    0x106940b02c10065811040489641e901805107406840001e8420341000c4242c0c0d103d0902500001c400130b0314400e105034202a2000055507041c0c0410610004d070b40c5090044c901a1001c2004020684416890300801c81015260348000121030300c220b4420b5110a00781a00701000b41e010303004080001d0b032039074400d119020043c890101d4040441e130245503854010b20f82e54540d0081400ba0b001c0944030183c0c0140110f0380100003450004041d40010011845144240041d0b6000b03904c540c005010070b0480c203d0000f4244814030b00c2c070001e0741c115122100500c2420b00f09500ca036162905058544140400303c41824008140007a04903010f40006060f40c1c400d8803070080280010841010f2080e09119090040c0d000907105800f040c461101c40d00121514980490140d031125400c42c5404010160307070f1403c590f15000c00041c40040e03c14101d0ba103603101e030303800e600782070400019440105480c00903203010030940c0400d40eaa5160740c4400050ba80314010a4060b035940d0400080301c2c2c000c03000c1500 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 805541933 1250 805540683 805540717
    0x1b0f030a020f06010f05060315152809080d20030a080405062a0315031911120304052e0c1406011503020c0c090c0a090b030c04031101020c090c 63
    0x510b0003180b60b031800503240d0240000e82140d85280c08001a101d242840e5904560521905060f061a4100800f96401208604128121010000bc01602c0b81d030400300308000c04400103001d00c1ca0f0216201c0d5850300d0300d25003030400b0564000c1640d900c070180740203549144000908107051b641c01141c0b103031065000d5020f50301075603111150510b1005000b070500703a80807203080c501072407005030b44040d40d000070840c13035100e54181c0d04a011900c3c004010003074000310681d0300466001c001c2035441101c001c0c030080c0c800015207840c2c0e203401583c0340264050640b04050350382c142c2d034540302c8030a00418002c4601d4504035145184e66000707440312240d600c060f46c00780c000c0b120005600c00001031a071b04944425034006601c501c0a0001c500079000b500c000ca080f4090701c03282c407002c1c0d03450280c528000d2250b4010b481c3d4039136802c0d50140042540b80d0103000c21a6040c002c01c4281c100360819501100d40006c01203c00a00810040f403c220800c60ba460f802980c080034000c2c2c0c81d01b82c1c0068001c00403003a00d085 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 805543183 1250 805541933 805541939
    0x902040e0601150813020114071109152b0b070c0807081801050a0206040615080a150c11150a111801120b21070b0a0305040201080a111b0f030a020f0601 67
    0x200c05c40c0c0301040060301041c240c107542e08030490308400500506014514901005c0072000c00984011029508100350b8003840c5022005d80c43c1036080d511a100c4940c03562481d400969280c0c00d10348110590251400b0242800200d88074080d40110161649c4140c500341c1d6040e041c540f103c00741d0000010002114030541c405000c3d0750160085604420721500200002d43e296030303402c009042c209082402c84e10080c43c00054490041001c007410500c156014001040182c3d01c11003110659419002000040c0c9450311002c1c00208440a02d20700a002860341991040065000b0349200001c403107045100044e010844100c04007a030014110907070b5480a8444844c01076400d9803000c0b231805d44e1004940700c208000340c0842c5840340441c0084ca0030350303032025556001032000341c001880b83c0e8017081d1640700b017100315a131040070f469000348200410048101d440c1c6c4e8603401800380c0b0604a0b1003216540f1a803075091030030042c251003400d421040340d54606480c0c00c025103d000100318180b0314803404c0008 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 805544433 1250 805543183 805543201
    0x70609050108040803190b030f2419050403051603080f06010203030c161b030807031e0807030903020c030d020f010509030c060601050a05040806070c120f02030a030902040e06011508 80
    0xe03c0c000d6800200036411600c40c10b04000302d0700070041d00e400c0380c1075586807400d206840500c024030f401180b8002030038400030070f55004580d03040005500d4100b40701c420108258202ca40c02275203e0040c0000d0002025680d40c6002c0da80752107424010010400418404d02c100355111100911a01c1d5403160200a41c070350304010790b45c0c2d0000f550020307102002801404841200c1700b40011130640036424512400200000c00006520315410595a90b4000107604062640040c0d203155504240701a01c030000e07425903001455040081c01e03000826840e083c090007807520800183c001d802c00203041c2d44403d50f5289003e541c0b521200f070300c000b04e5402e103c0000c80e0240c1c0030007900c003000e1440015020701d0b034449004484a500c2500c004050050500000c6244c4c101006022f01c205c141d519083d0020070345007020201d07480900904030400400001c465032096000c030603201795003601c0c10007052004080c40084c1c0684100c0030009094481d8400004110050090f01c40003600030b922030000a407108100 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 805545683 1250 805544433 805544447
    0x521160f050427020d021e091503271f020306030a03080415060b0310080c0a0308030a060b0c01091109071e0e0301020a020a02040b0a06080606030403051b0706090501 73
    0x142001045090000300888541075009540c440c15190b40b180c0420044a041d008a0700302903454410150301284860034242d02c0b154000002186e690641e04114039040003c60f01c04004280c0040c10b5000b00c00b080003404012f0725000f100140c15540d1440e6174544524940c1d42c0000845c441200c4002c010101c400c8042c3c1c42202d01a19000c3d0107404013401c01c2d02d00392401c0101a100f1129204080042d05101901d4400c0303c0181405800e4140d41e424800e40805400c405038008100341d401158601c540e5a40e0810400100c2c0d50080c1140d803030796100c54101d001841c003548298901d0000040c9000f00100644c0940c03c10b521401c0180003600829082c8450100211008800f09241303152a4150b20481d45070b95018030581d2408400c060b43c00e80c042820384e000f0855802c0940c2c02500304a0840c0713058003c0e1500c000e8295002081140f500d540184030000142c80c0e580141070000218081c144203a04644600c0b107407011000c54403000d03d8000b81e0b900082d104140000f068800b02003015881144 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 805546933 1250 805545683 805545707
    0x4020a0504020f2a0303040506010816080c010e1c110a14060a03090503090a030f12230c030712080910060b0304020f030c1003020a030e2407052116 65
    0x4038850401003028482924a51041c4070741044280c1300c8001c0c29070420070002580f1691240014000c2940741040c91803400761107074180d03820605501f078184400ea0000641c060441024a420130b01a2413440c01705401a03c002100806801c40d004260309000b19064a45000c1a0030b4440701c101a43d2061544800220180c00e158086010080071923505e11981040c8087d03405101940c1c1303040500030000b40248596441141c1125500c03030440180080e00e242c2080c07440941c00d1520400d20541c90003a0104803041d2401e100b03440204502180120070000d80ea046940029082d20b56003c000000c0c102c480110b501084500ca00000818400b01c580940c204494280310b5441c08c60b11640c2c2003005171005921200e40501c1400302a1007950b44800c0c60b00c04012035600c00682d1112001802000c0e910000f0b442c2c4815444950607090b01004101c001c5060024014048035584602c0d40845181c402c4a0764030060b40d8803a88010b00103440f402849029800541f100380540750b0b100c10588404800312 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 805548183 1250 805546933 805546957
    0x60801090209220e03040f140102061b07080403080307030905251a160b0a0b010c020306040b280b0a1401080f06030c0303070b07020105090f10020d061203030504020a050402 76
    0x1030246100f101101482c600c00c1418100803a10300109032000b031454101e6400741411203400d80c82080030140b004c00c245420765003032000c0d140e10310b00207820010324090b050080c58600780004640741404845070a0f90080e680c030404559882c140100010050044414195501e010351102c02c1000030030140328a032000c1c01628030910b05481d044000030003102080c0c0d251603110307040000314040c40c0b40e0580b040c0d0b0144590128502820240b20080c121101c0a03c86418072428011900250b034000403035079401544140d0f1000b9aa403902c0381e0302c0c15079080c91110004a0500240001e0190042e0011000c4a82c103540001081da03441220380303403013010440c0300d41c0460141c0000c68588800c01200350f46c010b00103070403500300001d00004a450b551004030180c07901102c080602c940994207024040c0c202e0040341c007c0c4140310300141c4050302c904610f010040c850b640002d43c62000d61142d040a0024101c03002d0446100005080c040c005d0078003103404910901c24840e0110740352804d0720076100107401c19 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 805549433 1250 805548183 805548199
    0x7050a080f1f020708070b012408040f1a010308033319080a03050301091109011b0203010b060a021c11070302040b04060306110403031e0813030e19060801090209 71
    0x450380c1c11201d55142c200541c07200750208194030210b00458001c00b1110701c03071816600298908858500d400401c501c00201105020f1030329640142d0056640744c0003508040700c43e010591030715105910345110043c510000d80140000428000e03098003462107040300201c00003104200f03803105911150450301008114000f05052011818040b00c01c1d1250400e03444440c185640340c0d40c48600e400344540b4101c00181c000401441011400c0c02100c4d1846400440141040441d100291401d0302c43d041c420f0300103409034026005d558013500240741090029002070782c1c4d4800304900039101c51500d007000f40050002c2c40d501c1041403007600c1070010010040094206182160b007000041c08922910a60281e114100440482d03194072843c030101104003445903070b43d1326525001c4d211009594080f007061700c001092000081d0052180c543c8102a0b0003580480780ca18030f0155200c80012001c0c5ea0881d5004642c2c42400c22506100d00646010740c031007104a070381e1a8440fa041c0d02c10401d14035008010 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 805550683 1250 805549433 805549453
    0x2130f031101030225051005010f0f0506030601020a021e0a09091a15010c031107120506010906120210120f23010b07030e0a03140d03050a02120c0c0c040e07050a080f 73
    0x100480c4002c5d952003203094071031a442040c400001d03514285c0262502280e106420801d417080c070704003a0b00805043e20403e040d4030f80600040e407107002c103c40190068180c8400c820074540c090280310004034004040a180645481c0001b0003400f05007404c468100303010030a4005031a251407054401c4901c80c501c0c40e01f1034082c000460700810f05080803403d110300b1a64060041109104000181003a01d095502c0c2402c0e0741481d84c0f81c003006034408600780d0328100081c800200d4070508422880d4041d00c540c100c40007200400c440d4070303d006202d0110301c0e180803103101202c01c2d40d030803040214107511603281040840314668104000280300b403004c2d01c1c0003003104000103406124040100c040c0141b41005290352502c0740b00001e2000c840380308442d0048180203082d150144070311504050b400c1070460524811292040003047e01030403c200c090350100c3c4107000608200b11049076424060018800613418101302540e80b599401418401c1604580102d151400050140030705c03800c0100409135205 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 805551933 1250 805550683 805550737
    0x100c0606140f060310170f0a050c09240d0312140f0901111603090e010f0303090f0303020a1104110f0403020405070203090a0e06030c090c0a080105151c02130f0311010302 75
    0x1600c01711600340b405020303411f0000c50b0b000c0c020440c4240c06030b000b620705140d40b070301004140c11000b0880149507064200682480c444002d0409010400340c502c052400c11508080d10381d1038040300b0b05003005003484108202c58840821550143c40b44040b0030009884580b603250a03a0746d80000c0c0b01000d10184680e1840c60504000140c6550003030403c1c180c6035072204084a1180000d80040801c2400780d0b00c02c1040640c0041e4004c02460401d464465041c2180d80094070b0f810540c038050f000f10b01640e06800707607a03510ba001c0000c0c1020500c010b85e454841080507200c0c1d4120748003da125902d00380010760128000301c11540c2c3c90100070300c000207060411450141000c00070304041c2e018030644032140510b4032010030450280d14011090751301c0340881d43d8010709501d41604a0342c041d042980196410740b4040f02900c501101000d4094803640742d01003400d00a025010b20164943e8110100140013119101c0c0301058a0088030310001240c0c0c02c10065003680316203100302e000404410b86000d1040 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 805553183 1250 805551933 805551959
    0xe0109061b1a040803090f120f2223030c1f020c06030705072a140607080406091a16020906030c040603030e0f010815100c0606140f060310 61
    0x2520605031490003041e440d5900c01c0380b180c22102107410740000002d10030068010000b4088010881c0014a0804552802201d580c0944416584c5131007001c50408501d1403003d05010b0f41c5914201ca0f90300c6c2581d1450710340d560211525a000401d0800280d0460900340412100002200075059800201c1e80307405121000451504010450080010840711a91114000c500818142d510b1035280c1c2000d003440d81082084401c40001060510b034002c40c0c90214150314000c0312844001c60a5231000710011030fa1620a549004103070110000d008030b0141e40000d40201512121040d102c40c0515201103100e4134840c4102001c24965501d003910010b01d810000203910090241c04c0e0780301110104c01043c06c1d1031858100701c1c0454003854460031a801c04e444206201042442c010759503040402c19040404200070710b4500603e8007266030015640214080100f1551000702008142e903038078401e8500310105080b10340300360010388414505107880400d0780c4c01004103100c8a10481e00d0014241150303 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 805554433 1250 805553183 805553237
    0x130204081e0a05060a050109051509040b1e01030c1a0313151409010905012904090f080d0b04060911031915030302010f0f051614042102010e010906 65
    0x2500c940c182c40000948184a034500900d40b0343c5c4003007400e50401d00c4403000e448004040e80d4283c50381540341c40b001e030360b0f100c80e068000303402c1842d440b0305440c1c90030042410852402c407240e149100400000400000302c616100b19664104007008a5501142280c410f103c1540c4040d00e80c224907010303102144034106414840f002141e0001803e00b25480c80c0d0022201c12280840265526183c01040c03240a0081700040700c0300000300300700d80400f6275403459045014890740b405640d41d141310348100b200b808002288560046049a00d4262000d05080540740021240d40241c0c00c0410014071741c411b03070141c0140880c112641900396030b00e240d000c014880c2c000751000303402d40c0c0360440002c46044030744515028501039400030900305d250b00b04807030603034642e642c4504110785807104110811643c001c1c00d00351503506140c951601401009000c0072409650402070010b5605101c06c620140310444030102c41c0c2c400c0e2688400c0000013401922505194462074000c60000e40404d15101f00085410f10300d = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 805555683 1250 805554433 805554493
    0xb031e0103171c050702031c0c091e0302041805010e06040f240608030403110f090c0a110d030c18150e120a050c01230a0804080c120913020408 63
    0x3da0303052842d803401500d1080e00c00101580002554900000f01d483c1d10382c044202115051041c0030040c20010150303a0940700f11034140010000d10b03490b400105032210300860f0000d00074006064445840030344600800000c035403030742c60800c2d00080064003048140c8902e411403c80d01000c0b010742c5580356840546042c1c101e1086511380d141d608460103120b910702070000400110389840c110b141500606001c1c0110720f01c20000c2c00491149661034036090799000a07101085038842461480944000101305e052250600420200c0404507a0551108580d8003d40d994500301d404220700d9181060103070f00410f002c0500d150959138035103000701d4245e000c4a00c00761040003100403d200301810003054079000c41d840d40181c5005001076a002558030400c0302d07500300080500700080e6008042d4410941034000740f040c0c0400280134820100c05543c4a800d4074800e40c1c0410b82e1b000c5a800f91030784a600c1c0fa07071058020b640003165400141c070030344064034424001002341e0015a4101104030f0520100909 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 805556933 1250 805555683 805555717
    0x20703110d110d061e0513030302071716030f050909040b0c120903040609050307230a0503160e0c070b042310051905041a06030c03070b031e010317 65
    0x8190f110800b0f038110150040c280094213a803030003540c1c180003d0059600c0540f9080000340b2400c512041c2c1d01d8000654103040050380c54109103802144106c0509090908001c0400c084034000901c9120b14080d500c41c0ea25203142c1e0380010003d80d540e0003a640c5050300320030010002000640c09151050f0015904604c2d9400c01e5215602401600307000c59150125800200b41000b05e80c0c0c100b003006001d420100c0280900e00e00b8440100c4100d0a20b02421640d806a4003072116581c07210801b01c0040c21001d019034070500c031201e00204103403500b48107c0c24204030400020b40f114521300250780d0301540c807146c119002d450700d0f192049080b141c460984240c90b84103c4500942c6800c01841641e5500c46402246900c1e000b45002c142c074001c101d0070709801f0f0a1004100c00102c5050030201c00e0140415400c0c521748884010074030b48035448042d10342510134148081150359642c0003941c8208401080391064401d004800f0503808002c5c03100421494000102c55440881c200103400010000d0043e41 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 805558183 1250 805556933 805556963
    0x9150405040507181b211505060c010507023903030d0513170406050405060c07080f070e0105060c07061d0301091212060f0b070201020c030102040608090607020703110d 74
    0x7030540441022203050030b07951080c211721105030039610030b107900200b0b0074a104065050810b0485072175000c4000b42d08190780e5240b50b000000e4031010300c806484058406625003084203401802001c0c00e48512003d132040d181040d01c1c4103040b49012002c1d441d00c0c01008460801148081e2040101580050b850f000510600d10480c50502c9194824404540b0729500781c0e405003420031340c508104440032901c4c50200001c2c0441601302c400c440486905503501aa2411045010350501007290400c0425000d51811403000050018140d0b00f034a10483c092503e40e603132030080141a01c02e10350003146a0700100c50802429000c1c0500140300540240030824941031140003e00f11b070401c20044454810a507da900b00c1a03205d5910400d2442410042090905010381d41300a41801c2c030419030f01c40e40000e454002c40e4828800b2800b03d00014000390745070354036030802400c134050480c3e1031406407244c03100050304188001501d0b0120b0740c10091003000e00c1146801d01c4901401c01c2070035070b100200c5070941 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 805559433 1250 805558183 805558199
    0x16051c020f03040b0f06090f1e010e0a0c03090c0902130f060512150d02150706060e011d070804030507060209120d03050912030f2205010f060509150405040507 70
    0x4140c026003285009a0b40c1c070302858100c10203032000e4681c030030308050b2108004903900c0b464412074000c0060174050703010380d95050012a42d00002940d5a2101d40079000001ea402d4059041501440003c0424802050034020803130881d24501c0c00a407210300107240410242c40aa401080fa40c4250300041416540303401c800030900030654450750000340009101c0400301410311000b604001c02c040880200c81a0900007858000366100c040c0c4a12241d030030039040c5c11142001c56105075801f24040c00029034619158040035404d10030070071000b10718001d15101d0100b0704829440785020b51104041501e580d1002c1310640c200305003c6801d25800c1098200c01d0b40c0b0030087c0510851000010205041201802400c0d50390203814ac0f0815401560b2250503040030320162a480403120311042940e0f61039001c54101e4a001455030005400501d0100050041c1034104020f183c400510600440d1750ba003040c40305101c811038400d5a0201c104403200194500f0b0b80009402a00544c100e0b00617030345603002 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 805560683 1250 805559433 805559437
    0x1b150d06150e01020106060302040815062d030607050c0304090b0409060e030a0306081605040b030102120403091707060504030305090d061d010f09020d022803151416051c02 76
    0x89002c03a00c0b44400c001a50303424010103000d0025443c0c258109803400c810303243d03260f5506540540b4401c00500003202c6445101400301c0d4080c8031901c421106102c034880c20341038500b52184034024040d65000444450003a4106e038589000e001c010341c0742c64904505940140f110f08411075200361100c041c0070100e1018007494030ac404140d07000d15a101c800400c003408480d01c42e440603a007504403e26070140410f0410180c1c003100d00507240032411140b5240040d00920415071042000604070013440141980202e9040c00e0b6821488030210301c99165554994a02540c8103d1f03002a20411090000912890180241410141001c0d1540019548440035207500600743c000f079540e00b0300302404842c424001c0260300d006406040080d10103540100e404084100c201030f0040c21701c820700303400c06508803c2e1941d54030b1118142000b240d448c0e2030704031703c1e80c5c00031a11003907594203010070307111a829440c1159024030f03005001400d28484803201652190013403050f602405040141c00950903100e400 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 805561933 1250 805560683 805560719
    0x50306150102162907150615021c0c0201030e0609062703070809150a0f03050a18021908030d020d151a031909030309051b150d06 57
    0x4410004103124002840c18010300c0e0070000a15040d00c041007910841c1044868804842a100c14404d100b2503202c03034a4829050b000f8001060f032a40f100c3c04c0b01e100d07071003802565907854011041c01c6207020126524130313200d02a12000700a45100340aa14018000c1d0400036106040124801c0141c030382841c01c2140031640703070041e0340202c001c114501d582072500c03405d80003000c1480107905003640242e90f540c0c010041c2c002e21903d0001600c0519694000c0804403040350740d684a5500c10744584010001c10794654410042418000401d076410240d01a8030103191000c805401011107035000c10298280c2c044070012003c4e0f076135401040c1c08500303000521301140c0000c0096620342c1c00a00c41c80c2107075114400c079512401502002e007e852101307500d5501c50407100c40c0a03522074850004420800170243d0a21401c2031030003505404154054002c03584041c0901c0541704500d8850b85540a403240717020301c25501080c0342d05004140403000000d4810070032811000211980c44010401c1c500102c25 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 805563183 1250 805561933 805561951
    0x20a0c0b0a0b100c0b0c0304030306083012040f0201030204090c090302190f12110d0f021801060509120c0d080403060c03180f06090c120b0f0f1f050306 67
    0x40c50b0049141000780000903803000615140f40c000c0720a07200c2c0b141d000006440040340400000c00300742810311940064001d00301d81c1041c0e0700d09284040440c50000794a0422001603a0403901c038a07005d003445000c4d01d00501301001403e40d540d889581d4036190140c0d120049040c150b09100c00b0031405228850541e10315126100c8064090450041003c2038481c010100001c00d141941071001c0748001c84a6800c071004600c0b40760407558685840c680704070000400300c1d0018074900d0041c082c08480d0101c500c08900958401c00d040c100c0580048002d17100340102e5012807410010120b0300d0030a80954440300460b40f040d1020a000c0c1c2d40040c9000c1d035032540c2540d0b41c80d40450140180720103445000d445170500d0a04000f02040b507001c8000761030580d00060101d5414004040501c6202d40003004101d82c00b41040c401c0c0750700c903070450948100954003910180c52600018401440c4064a640030f449100300d410447d43d19903a011400a03030549800001d41035003c40062691070802850707000360024 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 805564433 1250 805563183 805563191
    0xb090706020c0303031e070302040b0d0225050c010c0809040912080a050f0f09032a010f0b060f091305071d012606040b03120304120903080a03020a0c0b0a 68
    0x100c0000e00d8641c061001500c030f60420428080000b4080c2c00e400c414038880021001a41c0d200c580581c0217020790b60000d41e48580001350440100081c2d8010910f407942074182842d00a00341c550785004c1c0d0031140d0b00421039804a4072941896010300c042440080c8588002450480e82a011400b90b540c10a01100d0741e6030304001c480d280348d4100d54281d611808403102001245804501509800c40103808000391015140100f5200d0600340119074840000340700c05039800180000888a0140d14030318002076510788100101c499200303008010541a0041409050202c0040754203801d900510a5552100307000c00804000c4110b03005580c4500400d4440142d142504001c148001300b15158403410444020588100f8403041024071034a45011000d18040380d03610b00100d0014004400307116454030840700714180380c020440c002c6100302e1044070320381c140c411841e0b019520306c00740303000046c1802c60030b1001c5c1c1d0717045101c0e1780984400301c80c0c0c0c0f0703105103442c505031121030505405a8866035142e4807 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 805565683 1250 805564433 805564439
    0xc01050922050a1415130204030204140604060603060f050625201203070318050a0810110c0a150f2f0a020a030c0512031618050a03020f0d0b0907 64
    0x29841061440d03c005110350080c0c1c504601e0400e00c80010640c171034400d15002442d048410320343e5050b60041c5074003410421401c6d00b00c8414166140c01102e41510503070404001040942c0b02e4000c0350200c840c2e020100c040300e4108810004541c000c0405012000b013002c41000003d01100e04400d1414000d11506100380d00a6544400e002d80c410001c0e401858264bd080138400d0000084030101c9806217084050000f1440040c07070801907940c07200390f214611607400301303002c0d0010440c0360f01c0c00c01801042140c0d01081e10103000078010034070f25171203942010018001041e1407844210315035103503003000038180b1440c200f500d089403162180c0e0b07408100c080c110305840c6580c501d12007400c0d0852100084c10300000c3c4000a658030441e900c01070400c00080034250800108001095064441c200820b44900d800c0320201d0715a0f0b4030100c2400056525021100d00ba0750720020841a25009401d0155550031602400442d1042020480c0c010055100800100f80442d01c218080e51143e0060688145 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 805566933 1250 805565683 805565701
    0x3151f080910050c1801180b0c0109060e0d020f0a030207030803100f09020d0e120412031205072708030a030c0c0c03141608030d0b062104120309050c0105092205 71
    0x85040818180600300707402103e003090b0104404212030000040d03a42d82c60500072540c0c0508282f41000b04000d0038991120840c2e640400c082446c600c0076401c40d0350490b101c00c44665035050001000d07002d604620b8041c400305442100642d84182c0c1e04050078050343c2d891130342c0f540c3c00c4041d07070000c2c110f01d502003112750f06070501e8000d030840030500c080100b08190704114510f64a01c200c0c07081400102d801211a0300b054050340b410400030241820030000783c6041d21020307003905030b01c007030032a541e40d8460101c034070300320b0308124a0096070380940c001c5040481d0040d05030b00620503c0300302c0c014066003503e0f25002810744a4048041c600c5a103903040b240c0100403000703103021841045c20500e500c1d107072070620201c4030010541c0c400612107080490b81d00c0074400803400703e104da40c8096103001c50b400c00f0100100088800207000b41e00c1001500c842001e040c004804a604c1d04400038015001500c44007250741c8610060608800001c119482806200038091100c8400d04031000c007154a480030003403409 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 805568183 1250 805566933 805566967
    0x101203050307090803030f01092f0903010e07030f031b0807150f060b0702060702010504170c011b080711150a080916030b07050d0f06080303151f080910050c 69
    0x88084c0c01103043d828803406c080208941406480714155582144156010881c03411407030440a282c0e8050a019594000c03240d10703440b07400c04a0103507003007a041d04564100050303134800700c80c5c21004071600300001e075a08403441240c1104800c1c5000000050102003030b480c50040c10f5142c4100c0400481459450020b800d554181c2e0140c40d105241101c10800161031904407288154100e44641d0381d48030303510050301ca6028a4100c1c0441001c10711780c5424010b0005010414420241c071541008003107504851442021801c0060150005000510000c0c1c802281d066540c0002002c80010640386494034009400c142081e00003d1800d0301171120800051101d15900c0000300c042d00c1030241551104040d224010f820042048000218241c1d01c0e0810f0388503032800e142480c01480f01c0750350380804959a4005480b90b44002c051030808482c14585901c0300d80d4007491310504907075660010380c000d41c0e4001009060150901070003100020984940c440d0912501c50848203684540c0302c41c6c595180e003 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 805569433 1250 805568183 805568189
    0x10b0a080d02070605280f020c031f05060f06031f08150f070c0203580324150503100504020306031005041112060c07080310120305030709 61
    0x641010540201e503541c082460000ea404a081055071180b40e060b0f550901c0e0280011024500310405c0380c100c0d420382c03040080450071710325400c42d914040d461042603181e44030032071008141c100794001030540364a1380d0002c9030b005c40000d2a00304920f807000042856075004035201160541080c0c20039220b0f0726a030031008083c0080d00000c2c01c22007035400343c070702c0650030140455074600c40c200000ba1203035108089009506902400381e440511108020501c1110391980e20703c201c0d0b802c9044400c1800e41010150340380e100074034044d0046000080b29100c0b040c070400c1c02c00205074844e500d003000d01c41c4d10f07425044500d0940f0b80c140c5074146003003081c00720102000030510802c80200240503d4540038090602910411500181e40e521884002881c1103681601111401c3c01d0104010502c00700e16001c45800d40306403002c010511031324000d1074a901040311003903115403062003d4008161103c1c00f550348a4004600c80c41c8468581150304003a9000034030850004030b00108001e102507005c4610703401 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 805570683 1250 805569433 805569449
    0x30e07090e07140906010806030721110103020a0e040c0e0901030b0106091a0403021009121b0605070f0803130510020405100c21182301020706170405030d0e010b0a 72
    0xd810f440c0d900085076144007420f228100f10a060205e501a0f80500154006091000c1c1d00c0300511001703420402c81221840e4162028541c060038805294000d000b00c80b1010320643e14140840d1900341044001d108114880e01008045e04c40c0d4042074490074041d40c0a54080d015000b000c7d07142620003051102c054000c0204950140c06c0304401c000314100b03883c25030760b0480d580d8407071940c0d60354202c41b0421107900c002c80250b0401180f0b000c0c0301c080004a1075000c180629000d100b92508002e568038400d03014010841c4040d011028081003811003c0c40d00000f101c40f0000d85084503072144c13440d103c04580c0300e414059002404218a140200e6841441101420143c0e00301c10319880d01c101c00c500c01140312965005070409644410303c5243c0060100c0ca100d014100031720344824503601400c03203880180152900440d01518070750300000d2100121031080d6641c0c0d507080015030064001c40740c050b0040b40c443c8000e001024080c9024021451000c880e1400000c82c10b4040d01001f070302420a5110328a = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 805571933 1250 805570683 805570709
    0x403020a060e0a030f111305040309050a050d151b02072102100807030b03010c180e0f0714040504111206040c0801060516120f081005010c12030e07090e07 68
    0x2c00780e15031400c00003c4036044803491117030a100c0e040120001c20315440340c56200161000310b1858008035400b090055010380c0d41d1f5014a9150001c2c407101014900403a54420560901103000548107000c035800020400004540060141280011b64201030b5000000da00311103c03d00020045d084c0d203903140c0300d0044c03c15080e09030540106260808139201c810410000ca0001890640a40c000002040c2c028000b00a0b081040400604001d20034009914045905030002210b0740700c0303940303907004800e041c50013002e90322881c03803c1d60b40004001c040c20700188188000201c176a5140310340303092803c0030001207030340750315000303c20814250040c401c901c100d192500066010342c0c00800103044d00d00300d0412070307a28100f45c45207072080e00240000420b61102018020031240d0302c012081560041902c501c001501c50b0624506409280d02840e0700044186500301e0108001d0482080c032950141070000d000b0052103680c030704282540c1c200388942a1913001564100f07204011070001021541caa070a = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 805573183 1250 805571933 805571957
    0x170103030c0303050406021c1512020303162a0626040b100509040c03051203040f020d021f11070f050303071b231e0f040e010f0906020403020a06 64
    0x35200d007003031080107000c15940307100090800200c4d0b03048482e25a44125038101c42e901498400000e480c07400360600c102400c00900281040d104840b000210350b0003809541400c1d000d525110310030200c807006642d00c1e900f541407406140f4030701105602181c0024002e02c1980c0c00c104018191904609085009110054089055240c0074503040d40156000101843c140c803a40d07480400315a4a4209a5204252030148030801030705281d10003c403403040b010f547c803e1246000c09040c3c0e000c2140c2c050048941401d00d40018605032107011203c1d80700400c4a250320079513420031845070504608500102d40c900c2020b112a200c10271948004012820a00c20310a05102c0845d40700d0280d00001003201449400e0105d003101360207000030240040152528420700d810f07d40d45042491451140c0c00303640d03050001a80c10401e00a0300110070070107003882249107550710a1000510302c50843d199103569030322000c000c81d813507401490a901e00a03940913031941c0c25801003185800d080d601010620520085031 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 805574433 1250 805573183 805573187
    0x1e0c09030d210c0320071a040b070507081201230405150f03010b040e1f0b06030c0a0c020405070f02011b02210403020411180906030309240304030f17010303 69
    0x1c40103200c2d0b60700007150002e10400141c016028000032a51468007a00c2102900c0700544003901295019000d15240c140700c440070902c843c9000d84020b00912784800014410a004000401c0001c0c0f00e600307298036000010b07961a40c061000e0300300c810280103118000305031460f003141006040f202141d041109040024031800f085550500c2540601200011068103a03401c1d442203542e60b901820a2204030007001050352214268070b410b1900112840085000101c18880c0c00801a8054501071540d200d0007400c1e8010f42040d04000700f000030001c440001030f00d481c0141405039129490b0050700301c51098000c2e0030340c2c0030596244140d0080000e4450782d0303a40024054410b04004010000c000d8068600d01620700c15500302940017810310080c2c425110000000700502d41c0040f01101044101d241008090b1a0544035158558820320000e00641b81100c180a180c00d000d0340c003802c2da45143c24550340c1c150000c503000e84c046070030743e0340c00c0d0180f80d0043c502200e40e800803401183d69604560f00 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 805575539 1106 805574433 805574477
    0x70308010e090c01090b03220308060312120f040213110301050a051f0305180f01050a1401031e03170a24030b0402091e0c09030d 57
    0xa842a040843c0100ca001016036981602d03038941410b00e01c054101509445407200c0c044083d290013580002c070880130b40d10988a5101a03d012410181042140504050400402c10090b42c0d01010341c015968050408a510451506e4a001050071344140b40092412a0300d00405c20914002030070145048030400c5490003515925541400268849070609944905000078883c900602a130005680450540c1d60410122600c01c81689050502e050034556039541d0303028800d564105004034110000000344020a9500d903503149501c030318811810b590b0042201e241207042503c100810f14415813040c2400c0800c2c10601140c4008142305041001d080402100440b00341584403503889c2200e400c15000483eaa49607000c2c4074102c0e0f40205024501400c44002950740c0407400505402644110302030741e125040c0ba01814031380003020080005005615107035940d0240c45c510 = true := by decide +kernel

theorem cover : BRFrame.Cov 805395683 805575539 := by
  have h0 := BRFrame.cov_init 805395683
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805395683 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805395683 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805395683 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805395683 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805395683 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805395683 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805395683 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805395683 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805395683 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805395683 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805395683 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805395683 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805395683 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805395683 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805395683 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805395683 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805395683 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805395683 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805395683 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805395683 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805395683 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805395683 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805395683 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805395683 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805395683 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805395683 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805395683 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805395683 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805395683 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805395683 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805395683 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805395683 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805395683 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805395683 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805395683 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805395683 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805395683 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805395683 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805395683 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805395683 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805395683 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805395683 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805395683 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805395683 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805395683 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805395683 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805395683 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805395683 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805395683 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805395683 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805395683 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805395683 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805395683 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805395683 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805395683 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805395683 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805395683 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805395683 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805395683 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805395683 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805395683 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805395683 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805395683 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805395683 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805395683 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805395683 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805395683 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805395683 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805395683 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805395683 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805395683 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805395683 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805395683 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805395683 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805395683 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805395683 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805395683 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805395683 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805395683 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805395683 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805395683 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805395683 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805395683 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805395683 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805395683 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805395683 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805395683 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805395683 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805395683 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805395683 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805395683 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805395683 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805395683 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805395683 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805395683 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805395683 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805395683 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805395683 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805395683 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805395683 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805395683 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805395683 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805395683 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805395683 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805395683 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805395683 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805395683 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805395683 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805395683 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805395683 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805395683 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805395683 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805395683 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805395683 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805395683 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805395683 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805395683 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805395683 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805395683 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805395683 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805395683 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805395683 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805395683 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805395683 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805395683 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805395683 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805395683 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805395683 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805395683 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805395683 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805395683 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805395683 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805395683 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805395683 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805395683 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805395683 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805395683 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805395683 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805395683 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805395683 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805395683 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805395683 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805395683 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805395683 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 805395683 ≤ n) (h2 : n < 805575539) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
