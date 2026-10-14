-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0957
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T00:29:39.768808+00:00
-- url     : https://prove2.me/submissions/1b031281-835c-44b8-a2be-e6bd6791017d

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 171942446 ≤ n < 172122302 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 171943696 1250 171942446 171942467
    0x150a030e010204120506040605013003120c111e2508060103300e01050a020c091e0c030c040312050904020d020c100c0905010e06040e01090c020607110d 67
    0x180c001810640c031811118480d81088401351640d50120342030200307020292040300d0040c040398031090300c001c3d90f0703100340b0030310744520111140300e030112f5400d102c00e241c007511052280036602c250800c0040c01c1075601400100202d140e040d041d108001014188840a4005400d0300047d0b1005148820042c5a4644824a401c940900042001c0d0340040d0850f404c2107000c1c0070b14032985c56030201c004006440c0628003140d041da094401c9000300d004030301c1508420307980c07040602840d0070fa6680700080026440c103950749218941003032494041240440620740030203500a06156101d80300d40b1000d6000d0140e0009640c2c200d0001020001000010a5440326903240500d5007071a50a100b005000502240c04c5840c2d070307541540d00001e010721071501c1448065106000c0c58410840d0408090b03004203034503a070303001e218140820564402c101d0b079501001c4c2e800500406a01600c0e540e16031030300c0800b401e0220001c501600c04c81c2c004c681ca00b4052032004100004203c0144115020f078001100d945594 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 171944946 1250 171943696 171943721
    0x20a110f06070b07030203090d021f051510050c0c040e060f100e01080705041b0c12021f06080607260c0408011401030203100605090a091b03060911150a03 68
    0x800c80b40c00012590380b0103c1c81040c440d1001a10303440c0411944c0c2c1005003106008046422561000c240440d12400300c414040086030000790a9651340c510741000c5160804c029030000016000b1007200703910200510461110034161560300f003c2c0f80900c410b4407413070309a40b1019040500003940c0010000d0305c180c1c1c015000054050b01c0c80d520300d6401c081d900280c00c50160360708207490500650400e4060b840c070001c012040d081140e0000007000b00112885440140303101300400b40000072600c20413858013012910038240c00c0c46040c0f0003400700245460b2150001600600b40022059800703281e101d40790003000001e808180e1001c0e05404036201000b4190143d440045c403011072440b00074400d48401d0f5041031060700b899411801010326007200c0454240405081003028010398441d0100142c115603c0c2102151180482c6001e1190319540d00110421250200000080c044260411210b560150900030302d118201c0040c00035019200700d04146428080102500d1648203602a0036032990 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 171946196 1250 171944946 171944959
    0x12010e07020a14070815010806040f0203030915180f060a0315030804030605100806090304050108090c04090506010f0608060d290a06080105160903081605060106030207060c020a110f 80
    0x10755558003003d440040d20000c861303902c003036810712000c0400c225900c440041490120103943c9010326130355032900001c1c001014105803032007030421510b003041a5400003000414070f040003480c881d1402c0c3c941c0c104400e0001c2030031004401c1043c5090581899000c0074014007032a03e40b81c48441c06402520305086408240c840e4560004041282038001c0d1020314480e150215042c01c10340711600070070181e60030205080c6c0000c4140308146600004441c02ca5000b0308003148542d48400100703040149065409401c58201502c0108100c00826468161661001c44080640c0c440c0c0d0100c4001030112009500300d248203a064000ca03d80c0700c0b3f9280c0003a18140141002d00c0d13034031540751910b001075444400c01da80300c131000d1080031401c0c06001d5010759105003d00850b40c04602c005c1a80032540301c05000c0d4100040c14010301881c1e8034000d12807075000b00c01c954407942c0d1408010020b6015400035038407075213041c00d190001e620210385880f0baa50004044100d039000c0c5420400c44c0002042c0c0c0561081 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 171947446 1250 171946196 171946213
    0x10813050618010c020c0121060f0816091103010b0903010e0d0e040c020a0f1101050c07030507030b060d020f01080a0f09050c03060906040b0f04030507060f090606080312010e0702 79
    0x86003085400d1248400d40c020741c030030070400b5550750300352600c102c599001d542010404000d2a41d00c04d084411815201211070000b840b1b01e444000204241c6e00000c8107900f001e070300420190b0000645241c6c0c0b4460a4808140c641d07030744056400c1354812806e034015010300700010003010925001810801500800015840030503204407441c1070b062181c1c47d4045101010003a074103141520030201d1a2402d0700140078840d0301503507a100005c02c03041300202180b18100c41c40c501a40b040007520884000070040b01d14058590805641d600580e1004075805030b00ba4001030103d092105900ca29198042c209a80e2001d001005441104006080c4020300e1b07503419403480c86e1081c5010301c1d00800d0244000e4800d02000401741400c000005200c8000b0354030500601002038940203030107130300c0010504402e030140c03110b02d81140e00d071045ea50050243c07404d0aa0b503c10000c20381d4058103580303204190401c03c007941e50001c1c2c0d80300d004490028981c0e00078040100f000c0c1d1a00404650b0111551040c1d07501c9030b = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 171948696 1250 171947446 171947453
    0x509010e031e0606100509210a03020708010b01050f0910050d020f0301051201050402011704020d0605040b06010305100b04090b0a1d010608061e0f032e0b040b030a02010813 76
    0x91041c565800850800c4400b03203000c04000d1050540142c01a18038036045040204d020700544512075105001390842d4910b4601a8846203a0107008121b01d0305888900d1aa424000c0d541c003524002d0b01250351030680785103d19801403003280d1300103080c1c401c01414100484200103800804034251401e021040221a254094510003809480000c2c4451034a80d41040c1c1482241004850b1f01c2c0560382c500000e02c00943e0304002409034450313500c1d06c00c0c006540c8510102d89000d18080c00101554248010302003080a841c030b00c144540380a0b82c0400c16aa00c19148101ea070510344100c4144803010402485102c205070040c860684019001141da41d030741d6000101904071540c1c8141101680d40014409036500160712900034804031990903c070460300c00740c5000e12a4814a6911034070101004042030b4506000070b00c04844000b030041c140001002c8034240c41002d4100b045146440d01c2c844100c0740c5001d203e0b8120740302000d8000c00b00114141c1c01510740035005800c0c0c250302205428280d001 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 171949946 1250 171948696 171948703
    0xc03091d062404060513080a08071b0302040f062408070e0a1503020403051209060904020c25080d020604051009080c0a0302070306050f1b09010306050a0e07090b03010e010302010509010e03 83
    0x4090301c0d0f035810790303d43c0c558046c10001800c40e040443e0030b400c6500160080f403021001d0b03810240c2c0041f00785003c000408503c040602d001e84c402504a400c000403000710492503400403045130a038098104401b2501824050b0303648800a00d0001f00e80c40340040345c2c0113842040c52400c2c041000d08000000c64603070401441c05410011001c002036000202071003000740900c01c1510100c0c0b1098090300304481c1d03100003015402002d10090003998041222202d40404001400b8241e04040c02c950b124030f008844070741108070358000d05890b8803403090f0601c0c100d4800110b280c840e9810802030454105095002e2010b40302c10f4400741c444940500805852420900c806001680301e03400404a09141d4540502a90401800b401e10300d06603204000e100ca0f80307294034011127140558529981c0c180e0381300580083c4070580005400c01c03928040415202290340c4094025900382e03c0701c141c075036a00c8886000c14802405014282510036004000550081019006110b01414991440f09288004c40e14 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 171951196 1250 171949946 171949949
    0x703090213050a060506040810020a051b0c0a05011704061a0a06030b010f0f05030604050402041b030b0f090105030a0f05031905190f0e121c0c03091d062404 69
    0x40081e580d0043c848020400d20036080200b200741c0d01c09040c1450011190b8036010341100c040d281c0c607000901c0c0b4010600c5042114582500000600e902c0549941010780c5c071903018500d18042c940a860205240d8015500948600181140407800303131b0310380e5100c0c0b02516084e8001407200031043c42e070150995600d0f4400d8040e101c19900080e06292002c00100560b151241d504140f0042da8405041598010112a44501c0681d004141d40d2140d1010a00519112140c0f400845510308070313011203075151304252070a42c011039011036042105410080180c0d001e101b0b00d030b416030061800600190310303520304d644400d010b80c0907282000d01f028100c1181c1c1054505201c000745001030240c842c601c0e50405204002807900d003944c0c02002000010708921159514188603103220700c465000b01d9003c12050f00c0e1001c0107100000e02e07200704074000d0304100344c0c8001180420035560000ca44200c3c202c20b403192030103c2c180601c4d4030303407520014001e4020010346544144001c504425406d50303000d000600 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 171952446 1250 171951196 171951229
    0x705030a0522110a0b040815010e0105220b060a0f020f06010b0301090908160c05120a020102030708070203030d05040b070908010b0d060c050c010c180902090306070807030902 77
    0x66580c60014515001c49800400c2400030508502104000315000d0740701e003400540c800d02c164640108003001890b403070901c0d40401c8000600240114001e50003281d04100703001c032680314403001d90f00c684500b900c1c0b09090207201e8000c12224412010310790085103901259041100c00905800d203100072a1840c3d0140c400b41001c161030013000207126034108404200100c81c403020f8559541030981340d42d034502c010700c90182010344442d0004180528442100c04540d034960192042c101e444c44c0a03402800948a55031144802421030710402e513011038901c080540c142d01441c5415000e03540c0141729045400107a8051006010351000b1301c3c25031141d540100e00842c0102018501034200521020007130f08410700c5030b410315054184c42d0b141ea040f150301c202e500c55008100c0004104044032280152001c0000f590300b428108100c0c0c5800c40f0350344483c40140130b8511132454941849005a224803400036405610020024803828442d5505681001042c60041458502500082c422084041111 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 171953696 1250 171952446 171952457
    0x151f0b030106090e0730020705060115020f0c04020307090302040c030506030d03060e010b0c160e0a0c050a05032e03051c020d020706050706060e07020a0506100f0302040b0d0b07 78
    0x50081503000715003a001008203400c030300c103545007408000300100b441d214034541c800c03000e5010000341c5c181c08607445509242c41d40115248c2d801c3d8185503995480070f06c43c14000200d0810300b60100b0f44003190209151842c03070700070001805148180b00c001c2d48000c1c03d401c2040006000800140d0701c5006205100a0300d981c003262505118041504041c201c009036401c2c035213806c00421800d11744006190440d03e841300602d4035010440c0d62241003800c09c0040b903a98145c1d000300498401c50103000030b0b010b000301035800c10070021840c130240c030148501241c000101c0d01c280001800100702d04541d0003d62030ba0f604025002030040710100042040c2d804c2120700c0d40064802c4030701c4a5560034290b05a040f284000c1c00c01c2140c441d0043d441d41700701d01070117040140002d2802c00f40a010b07001100108403101e10248940f0344036400039100d4402c0e41044600d80038200c042940004a403400724150749402c0c80b1500ca2500d0b40d420480140130648440c0e4012001c1c00390b1a000c1490841c025200364007a4441 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 171954946 1250 171953696 171953699
    0x602030d0b01090f0303200d09142d040b0406080d030b190315150f0e090d0e040c170c0705120f0a08180709020c070e0405151f0b0301 59
    0x200000d64070701c01802030400501d100208200403114a14400300c0760582461110487c940b440c1c00800410540c1034500c520903a00400012070380801c0d43d10842d00b0010781c1c0142080c400003080141603c114440385104414624400304401c940e61041000000900004003800034802040588407aa441110250402040c0140b03040d0140291a03480200f1544285500020b041003030901410707002c0903044480500041c0741c0c00c0056849000e08040640c0310700c0d4456544d10001000c0c010034020b075252075a081c80031840e400000600c080c03a1541d1a00c450352145600b5041c080145580c00341721042144001c0c000010501d0341000034007440f00c0c6080c040d41d46c1050f0a01501e003c82c0d00b008442201070400440030408030798015540c5140301d030726000c50356841d20030700417032070701410f4180d14203e000316080018034440a6006020103410802038500c2d40d40d5480814000c50403c582c060070759089126020118a0055003940e070001c00d10417003904100018082c14544102a003002c000c40740700100 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 171956196 1250 171954946 171954967
    0x40e090a0f060f06050a150e01050408030f19050c0d30050406110c2d060f04110411030c2a07060810050d12030e010e0307021c0b070f0203040f060203 66
    0x4c1201130b10003560045001c6240c403080303000e00c0e00740c21408400c01c160b442010365a80c0c07040040f10f005100c4042104d80b0741c00214281100c0d41e001c030301c00c00d401c21100c120b00c00d0302901130740070b0351021002d45002d03081045d610001075a075482151006400440d07903549943d0024046212544d041888201c0014540f030f00c1c0c6007800407101e082003c8848024240102c00b41c6100c00140101d846021070b244103801c3c080748401c04040301d94680d804032a4000c0c2000c00c46031407181000c03184100c1c0107101003180000080c5c18002110424443c4a0b01130204100207105018084000c0003038064054805141c3c50680440152507900140c0b159599000418100400c5600240c855000046485103000c2c1c1494030000404604000000a0460200840400c0e065000343e000d003280c20007035002030050200c1181d03040c2d240d600c240d00482c8036102481c601c034001040b0303480300400140e105840e000e0795120180140e58502c64880b00340114441000080340c09007400001c240104086e40041d91254840304 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 171957446 1250 171956196 171956201
    0x110403031e0519030c0203090406140103151d090304030f030f140301180902030703020306070905040e010605010507080322030f020606040c050d270506010602100908040e090a0f060f 80
    0x44000c0400405110550f00d154103d00281c0c1000075a04002816200000c416030440c024410490750007458240300050082581d03041a40d49030090342c041041441496064041110700d0145031903400c070840301d8540880c026403203c0c1e000825001103e01301640c035500c0e9004207038090030032400170f500c900076041c500d5045170504144440703140445041d503040032050312241200b40d50a481f2942c40303418030000d544003809504061b580180940d461483d01e10409801340070580300e030706e00403441c086242e43d48103010b101e00030541d90141d40b82858041a81c94420650b00081d06e00c80c402c1080c0340421045515041580e81082d2080d110465203241d49003010f07082c4003009080601640c10711541708000c1b80d0107000c031501c600c0c815000003000034908000c12000800030085081000807041e00d581800310000c3c072103049071b11903421182c40204040c070040c10340320f042c0001400c003130050009105500d00c01d01010303803119003d0121810796034a62521703001c000c15218243c0d001a501c4030302c241c0c007101c1030 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 171958696 1250 171957446 171957497
    0x60209121e0102030103020108220c0602030417060405070314100f0c1b050705040c02030405120703020301150b07060906020c0303150f010e150a0905060a05040603061a07030c0611040303 82
    0x710001c44c251340c0b4540000c2c00080d0010a00010044c1d1041c201440070380030884013806903008404041055218a0042c0d0b89901c680030304005442d011080e8050b0303081c00159203106981c00000f41840c20b00d180d45003020304501e00e070144901e005401c10104c034003407288152010007103411404640c81c44c5240340a004004002031184030f042c1417103035500c0403c0340029010100d41c001e82e0001401a1290001c034114099a00602d81c01706001000d0b084481c80000c01d201968001c40c020014402005d40410080c1c07000c0c0309800c440d4074107120400204102d40e010782c003907038001c480161510b0000c8002d603055a204850065100754a0b50340303850701d41450a42041d43e041d081c04c1500c2e8240c3c21a001820074030b2021400702008100240116405100d42240fa00802c4d01030191610303140707082400341064200b0f01803d40040c0c0350a1000801e00d001d6100c2900c40701c1461007152421a8540707088600340d032410015100980c0780c0303500d21700103c02e14000700f00940c045c0eaa41103161110211684001c07195 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 171959946 1250 171958696 171958753
    0x70801050d020d1101110a050f011d06040311150703050a1406060f0d0608031b010c03060605160317090102040302040609090c170a02040c1106070309170706020912 72
    0x100d5a41c9001626040c0700705020a400000140203007000c000101c5d13200c0700c61030704800a07000e0310b4050f908202001035030101b21490300e0000c1c420780300c4004c8000c5400c0f801c3c2a4005c8190f0040010802080c00703102034002e140120f8054a4402d041721200c095640703402d551400000b80d0320030401104000ca4030410380c004176500c5030302c007450620030002099401101e802e14622880010641142000c0d81d2040c0010060981640c0e1607512003110001048070202042299500701040366184c039103e48910030a4581c0b076241c981c01c18402081b03041c422101c56104800b030000fa248070388035100e40c1d080b10a1190407030320005a6101c0c2148140410340e000341c1e0003120b4540c20041c0c00d01c001010069210152404883c0b0300c40c0c0304403402c8095150000c804000780d0010710701203254540d641d00208540004400c00110342c459150b040c030403012100ca03080e0103030000b148894030301c074060100801000b485d8020440982404030040015a4102503010900030a503c0000740b00c0d030110740c5446240701c0f1020f = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 171961196 1250 171959946 171959959
    0x140310030501050711150103110103020d0b09010b0a080106020a020306190f05040c050a050603130b04032604120c030801061103071406160c080304020f1507050105010501080c04180c02190b07080105 87
    0x345036188809e00c14140303038441c103058000c502079081c281154400990311000801001c0c46581d2644210519440801d41c140040c88290011520034000120340007000e502400514855407445020214500800d070212142500d07107001400c50182402030900440c010980144103600e800200558203400740d210902a0006204201c440ba2004c02030313007400fa070415401040d9954916048a04003c44a4090f02d443d0300101e04006170766480c1511842140300360102410140e038824141c0f10000f4404c00203000034403200040c021f20348254801014890a80c003242e040120f5680e0340c1510043c008007a458662081003004011280c950010720200030314107250500541a0315070321051304c001000640036040180d200c0b03020b52201d01c0c4402c40f52900e4030185407203400b540340c080d000c0d020038402d55000554410101d02c04000150449003140d00c1014070b03a2228100c3d00d5024042c01d00041d680d025800303801d00350142603240100d5660224414104000f0616203400041c00a40c01a0031250080e00c = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 171962446 1250 171961196 171961199
    0x41103011b0c020d1b0b1206090c0a121512120e06120603150a0e010c02240415020714010c0201150b071b0f1a0306011403100305010507111501 63
    0x7500a07a03001e80190f0143c03410b81130382140e0b00f810351000086040340d1100b902408400100354003008080c040703180994840c5000ca440d84030402510030425070f91118000b10070802e00030110301400740030035548914040401c82084401c0496503508040d8090404c0182601800301041070708440040e0b000801c0c00e1140c6d19071042c4020545034018208405a5070118101241242d5410007455030340030a682504004c9107083c0d4844000307000e8044155030198241090410501d00108071a480c00310318a010800050b8100c4a0022180c8041d105841034114082c04400f000407034001030003141e001c0c00980040101c2170348070f1821941810460030071a450003605044807120160040c0444180441503521050a17042030010322400b4442d910003100d891038000f581c12101454002210342c001082203110307036444d5810b85148811140310b40000c2c05110a00d80641d041005540c01c00000c03407110700c049841c2d84e00d003800c441041e42d400300458080302091841ca2400c0202503015403e1601b0030f5a2175 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 171963696 1250 171962446 171962501
    0x3091b03050a230a030309120309030e0f040204030203060711160f06030c02190b09011a0a2c070c0b0c0a120209120102030408030114060a020309010c060e010504110301 74
    0x5018150300288000e481450814001c80500700c4000044070500030366000712811720b0003030000d02540004503002d001c50f00740c803103c0600074412040c402d030700350b00d075411058100400c0016140d00c0c807500c0e5134090b40c00d000100150701c003002080d2254030544c4a01140c410708049079807600032950884110a0500c290600c0303842128071039142250b0b114100415051a042d400341d0400e02c916540e0500c85031900c841905014440c2940c9000798180e8000700015071100174242032080d5001c0415030800e01d40d12040180c5124400b03800781d646c101e6110400010069450200301d01c034250b58100000d01c500003200103001e1904140750300201e602403030038074107000110007030200c041c1c1c0b0b0714038135590340d01040803900d0f501d40d101040c03646080310008541c3da1505d480c10002d550000e0080d441140307841d6051001c0760415030b04840d81d0300e40703940041d402c0507404001150340950a01c811200c441d1102c605043c0e0030001d0160728000c40c03280f03c1e0454901440e505041c05c4651400c0700b00300300744e20940c100050 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 171964946 1250 171963696 171963703
    0x6030d0e0616060f0e120d1d0604030915050901090e04061d0105060a050d0f140f030703020f06010504020421020d06020a050a0e010306121707050d0809010e2410030b0703091b0305 79
    0xa1f12444000814145211140052403011003a40ca000d6400303480c1c100001c0660007509501503d48080703042c1c02080307091108440a020f80e603616404504440c030305200c0000524145030740701c1e118010102d00c05407100c0a0014280c2446007403006a13441c0c0052100c90703d0200d1064000d880240c070b81e9000181a07440780200160b1200001d04858401c6403040ca10303100034021245500280707022255030794000e14000f5070710900669450a607004010005c580d51605000319421600c01c0624051508903203890117140502005080f80d104800d03407030200c000369950000d000400382549a8a03100da9100501805508454014034101461b241c1d0a10403800c009004500d0103030010f01c00201c800c40301c520744050b40f040d200c0c003405034400d0146015290394801d00892044800b90000d01c0800405c481c941e81e06c007404c1c3c02e9521035801da0304504645108886409500c15415140342014590329180c0b0f146142d001e0305c407007000a0700c0344100d50900007600910f0385049201c14118400b00c2c91502c0d9030340c030b = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 171966196 1250 171964946 171964957
    0x506060301150201061e0618030807080d0e07090b041d0d0c060902090901060312020601080705010c02041b02030d110708040302090606130807060f050306030d0e0616060f0e12 77
    0x90222040340c80524140c800d50099014000d1910102e240c0c246d0504015001d500301c3c0314a00c000b40a402131049a0703101005c0060490341e021220342c7c1401e000d96074440254020b14248084141e9841c0c8100c02580100403c0c0018104010300056020b030043c184010707141c81d0403c4a00305010020103100c036140000c0e27400500390203844c03c1c1c00012f205103065070141c610140040e5004e0666424040c400b401907200f01d048910800c039801401c005010700ba031301d034202440b17100d503540c000b400c00b00490350291500321075807480244002542c68481c215248034240340d201940050b071001c5003000c0c080e140707031281c4150079001003501401e1040d90350700c60b08117100c0ca00009007d000c0c11030106d1656200c2805130351501d10f00c800311078809074a500005a0700d658601c0b541001940040180b040c1078000c4048901482d4054090b00c0b0041f0014019159102d66104250700090700f00502003110390040c1c4000c81040c4124800318464080100b880d0685100fa06584284c7d001018851104140358040700d1 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 171967446 1250 171966196 171966209
    0x30503010905220b15041a0a120507061b0b09061005030a02030303061306030b0106030b130b010e09060123340f06090209090d0206150604090f15081c02010506060301 73
    0x91035071455054072000c007a00c106503070454202a40000c2c01046048055500741017510b8030404140d41d44141401180d2780e09002d0216004045c0500106210740115140c145181ca038040000c04079030342c1d442500c2011680509207400c100140819900c42c541a42c0c000c0800310000d080801090300082d8480c400038040e24030078007421101c24291040c1d50004001190040c80c04440c0b0369642c08042d01510694180500c5600c1c1c00c4440c944044141c0310303111070010103030344426902c0380440610a0f1a1070240c002810700c01d00100000e01c51341c2e8584e03c0c020b0003a840c419603440706654009806900f030804140b0a03c1c1ca8070f5600940303e129607182c0004195040000d81c0002c001c03d0900000400b60160003030f40107500c100c00c01c03545400001380d850744114107900f00d500030760303803488050352a11860029690101c41003000700729400c1c09400c10b603451420790780c0010311b024000c01902200c00141c1d00000030340d003204c0880350703e92110107040a402401d50000f4010781ca801800141640700502131203 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 171968696 1250 171967446 171967463
    0xa020d0504080d18030f03080a200403030c0303090c26010c05160c080d05040509090f0d03020903100603030e130203070909020c030c070902040f090207050303040f02180403050301090522 82
    0x20344e0010001050503005581010441502d0700c0c590070018001303141200c181880600303103090920360f0864500c09180c0480b1110b0541e0416003180d40450340314501f16810b80405889220940226051200880041c10a01c5480713515a54111150481c50081c6812a441c2d91610021148e2603821504482101855181d1400459640d2402c0e0400303801a402030ba405210728030084000540001c001c00648004075228030007941d85080c099520548c000ea070b04003503080000980b03000380c06900030b0f04d8450001025521321008505060040b01c0a0351710a1b00000e003002529009410030510040200c141ca08041d0318526041c6d00140c91020701d44200d80107194000340076421100e0034010f48074000d040d0390230384d04903655481655001e50807034090030407c204c06810008402c001c034800c951011364084003850455a4980391208480c01d8548140d8218441d840545001c0028000840c85207104c1c1c0c076015202d50402c6d00c6101101d8006040d503845900c54a800019028082101410a68040002d = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 171969946 1250 171968696 171968717
    0x30b09160e16050c190f0c0605040f050f100f0e060f07110607030206040209040201051c290d110a05181f0b0306040e0316060207120e0a090c03060b0a050a020d0504080d 74
    0xd000e0046c1c02c0b074000b50688000141c0803075034640c401c0052040740c040d0420080f030161a2000c104d103840d92403008960103141e50080000d0640104c9080c49501203c0c10801e03004c10100b800314086070700c510a40814603200140107001c101c441b0154280b851026209603082c480f0303665008c0c1da190b0300940017030301c03c4800f44001400c40e03204000303c0700308515017001c000400ca80e01c8880e001401c1d20010742040c0c00c40c3c01c0b03c08000c203059551440500d1100130070b00c400380d20094950072b4254800c18161a00302404040100b45c44d111451000b80d159401e660100140c5448600e0060420307410b8100007c3c580101f20404c84200c2c540c00f41c9030000c0045a000850320081e02c2c140346944506e4a40d500c140005001d0b8500344003096000d40790f02c034010400c0481404012a041f1f52610101200b91342c00a01d04100380020001507001b00202c0c0841d04001900c1c646903000b07449950884056900060301c0010541e211550500c08142d01d81c1543c10070030305290070460144e46581e00c5491080400015188 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 171971196 1250 171969946 171969953
    0x5060d060e010c080702120405010305061305040818060403080405061b010c39030c06020d0f0b042003060f0d140610080703030504030b09160e16050c19 67
    0x1040284540c008410000c04511800d0203001e4501000c00710041150713640041c42450010a00406244008244625207414040190001c01015018a41000c035920f1b5004520f0294898070b4010740c029882d0a4684042c0220003180403201e119040c09604144003c01c0000e00346010707541518030480d003141d11920361800f4031000141a0755003045641c00c00380c0300244030341c006201a02c0012034009151066081c0d9515003e084004607040e46444100c0700400080f0b8440c01c1c1565080388601409454600700759002c0e4155211910060344403942c42030710508528091143c5142c1e804031152800d010840815006000c0c04001e0000713002d90300884d00303a440d99590140c4540703410f40c80704440e510b496254032210341c0c038041200c100001c280041008100c038140012440d0880b0b038981c1d601443d01d411682e81041540c8054540b400f0742c402e40d00c9101d01c01d4180074841c8040c040301444500907180000780c075071508000005070001d00208102a22111402160b101c0c00c0d0854042442d040f8011440c = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 171972446 1250 171971196 171971209
    0x9010605070f02270411120105060d0803090f0709050703060504090f1b230f011803080a0e042f09010905120f03070302010f06050619030b01090506130801060b030903030a0506 77
    0x91340142c40030348020017040200e03483c00c0c521802001d4034000401c0c024091604e003210342c1a1019640686201441c00006511500541c1e000b90094180e40d407088560003454a040c00541000080075120b10070840c2c500c2c0d251003000e0080501300c8040c0154541a20f07003080c22441100007038404058081001000014060b0800c020240c1c44103d18801d07048051040e180003940c0c40c081c3c4a42c11407400c4801940c41040080da141c1407074210681f0140c61540c07a550280c4c403141ca00d80512403842c000100030f0380c4a124449010500e4240210004000384980c43e10145030740034a9460501806002850b0764406031240640b071094480002c001070358981245030406c0c051448601d4400050400c0c10164190850170485403260000e00203c0d0f190300411026015107034001103482080300340f0081c1c0c14825084a00c24250606000441c203032200080388082e481001000e284401000c0100001142440781d18002c05200c0c3c015030640c01c02e18060380d1680300181040791000d8a0340c1c0800c10070741c0d481 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 171973696 1250 171972446 171972499
    0x27200f0a030303200a090b160b04050a1505010b1c0b03013213080a090302060301150809070b090d03030204180c02010c03050903091e0301050405060609010605070f02 73
    0x40448500300d03030380d18008000c1c0103c001035100f5045050304042e560314941c0c065a03203e401540310307401c500307003000e45100c405c1e001482400c02042400b2100000315090640103401135000c3c4001d8242004c00e8200010303902001c9580e25030032440d041c0100641590003007915111400c140d410302e01280507840240280c103035582c40540c154640402d96400f0703111035103850104949414000341380b420000c08980c401504544007a01c10401815000c005032940008000d00c1d405404c05c1340032145c5940104131607030001d81000000b0051804000c000540009034643e21042401c000d000341070414803070b00000d00038507203242c0c0600314007083c074001c1501940549010b005040140003280c00348007503c101070b002e8204104090f510b081c09580c540c074800d00807144213018038001103141c10716000901103a683c0d8216200a50020705000140030307603080c05010b004600400042100d824248100301c070007101a0300820502c4000c000481c002802c160002400702c0c2c040307403560208484000d500c1d4002182 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 171974946 1250 171973696 171973699
    0x10302070c080c011e05040905040f060507020f0f0115290310060e041422050f0610060f140f09190e07030905070509040219080127200f 60
    0xe4840492101d0b000558000150400da88581c01c1d00880541d07464030f00b68403100e42000841c1044140b007400019002190400e01c9042d6034146944551604000c6501c1943d4210058108607091610020208480c2c0040824000204000702d4010b41a10045a440c41140031100310000050040c1c0044011845001c20100c1c01a0303a900e03010004240c000824015803000ca11071080091950a0600c00c0d0544841c0894030000103840345660004601030565070b640c1d1100018030640e001841c18008401c1408002e401414242001e103000e200604080c3c1052040003203140a0290700c5a10184d81004407108400c4560344024808180c078041c400d08007140c1e0040703d103140d090301134004909000219000480180e4058642a004605541e40c8804c00307081e0b940075810512240c503001d102a604244001c0500301ca01c40d040160001103406ca5020803c035955480d99000c000940e0320040403562101c5002d83c0860844c0daaa4071045070000c0420118071078a00d8070b400d4070b901c0d5640c10b601038180 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 171976196 1250 171974946 171974963
    0x31906030f0b07021204082a040606030204030c0e190e0a0b01061d060c0d03230c030f0105011826030d0b01020f0a0b0402061c0212010320091501030207 67
    0x82070b04200140d041d0940d01c032001803050704112441400c03260280c45c251841c2d0009001200420b23a81c0000810005c92a40d424110000c2d500c1e2150792035210390001000252409610f030303031860405586140c101c5d80101441c1400508100ca0841e81d003012008500000c24000340b410443c001007071502044200003070001002c10004200d06d48c00041c100d90a148107a04214040b001c42c0521515006080390101517034410290821074034000d40001e540d0545000b1680082001100b020308413200540781a402400c000050041410780c1008041c054034081c2030602001d80203460741c3e110b8010a1080b0010a203a0070440d0101006900300780d070b9245244421a038580c400790030118020400ba115240c0540b2401030403001c8800085810741c021030704030b000328019070364580900070194494240c10191010f0030300d0304944440d1900c0541940e804800da886200c1d811740c500ba044100082c855007c111506040c41e91103540d030244142d51041c840d0034400c00700c2c014040168043d004100d4001c15115 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 171977446 1250 171976196 171976223
    0x60408031c0b040221070c05120a030e060a0905060906010b0d020a0c0b04060e0f06010e071815020a062d020a02010f0207110a0609060807050901090902160c14030303190603 76
    0x2021940c525600c00b804101e00e105035101c4113015038187c3e0110340018010b4101170300c80503200c4400409801480d2180c2008110032111f603894a041c0001200c4402d003481c1d6403080070007445410411658003d40d41c0e8018007142d414265218414041c160320034071a15000520229080d00c60500d80072026404202c140003420700e49404001341c41d004140c03030441c3c443c1a803a03c640030800079240b412078a40d03280c4c0c8602916542000c03900a69502045140c444002000181c084120049a010018290702620100f4110309d441015508122aa030948112050003001d909005d1801d0b0fa144035040303800181e42d529a011b003030740980442100002a20310120b0a00c003809401d2070b08914404040f500000d8041c1c580c40c05a4405049005500c000b420901c0001e01c00307400380e0300400000a050512060303840d5520040d10580e400400c0192140091021610800c0040810340c1c001d40062115001021031410100c0e0392400003e182400003800e115600161082d83c0e8044c6018680042e00340e200308 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 171978696 1250 171977446 171977467
    0xe041e12080f06030a0201080606130b0c0a03090902210916090218030d090909050319030c0206060618220606050a0f02060112022215080705060408031c0b0402 70
    0x880c04448902d9030780111000901140350200301c038801c1c10b074141c4442c00c00d42c4a0340240301d0541c0141ca01c1d43c100c1d18100f10042054007544015260b03030410600284040320136450000c00b1411503a1100316a240180300120024144008907031409581001e4080385903519801d051508450b030180c01544001036900ac920300010350000d14610f8094000604440011014140d60340d10591107600000e000c0d071303410320840c06103400010009000348201e90901d200e0141404070300701d11042c00b43c04a50b0b00d03222441c9068040c0720840d48518202e03103080c1030040105c1010480c0c418101c8031440f03040d10740300c180030304500388004400190f010001004004e480e641c019085034031581c0204081007003031140075501440021150305850700026102c640340e216900f8094401c2040384100a40c214001d40e0703800000e0544128000060341d0b0901011031443c0600320741c1440f0280d0000c2c1e0042600304000d00c19880000f04490500c1c8400c034400c0714a11603100a02c0050824400441d4003d00025548119 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 171979946 1250 171978696 171978707
    0xe01031505041e0e06060d290f04020f0316060e040f0c090f0902030c07060506040209100305180f0d0807050403080d060e010b07050d180503120717040e041e12 70
    0x102d0440302041082d8181d1300c100030364a2800704c681d19406107102070894000707902100d03c02c00000c011f2100081e58401c109603c2c03050704044603030107085130801040009510703143e1045c000d880340c1074026101040c0f800054403410106030041c00d0510682c401001c4003030300e4541c050300e043c0e4030b580c034204040001c0680c014299031440c441c0018030030b003403200420b01800a1085a014108010380c0c0352030280c8a81e910f90290100420b45035000303509100c810305540b9904080d102d80c2d82299000105490300e030b800e039a203070289400e102036143d02650085008160002c0c103242c4e5002c240c1000d800030f0f80c170b01c1d60448031485250030042908102003110016a410740c0c0009082d60090ba00303110b8903a0700c4404520741c500503030b10040c241c3d5100409103100c103400f03840041d2510b29550700310903010392214086480c00c402c01d10040c03074401d0000740b0ba0051041c031009440100700000c40c02c602d402e16107507440c010341d5405003000e004400c80b20b568074075002d0501103180002c0e5010b0720211420b1981f5002501 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 171981196 1250 171979946 171979991
    0x61509220f0c050c031206010c06050907080106080d0206012105031c0c0e180a230103060b0a030302070e0903041502061b0306010c0609060e031207030b09070e0103150504 75
    0x4205050a5a90002c540504140d89a1000a01c019170420880341910180c030b600103000341e41031000404214001c1003450181901c87d808020040c00c12600c1d1480d43d608483d01680400340c030307070881c2c1c0b05020348542c040f403da8111100d0074440040000006a699800080e2040041680c4030008a114540030920321a1210301c0103c102040b40210200c400d661000166006ca070340300c6800c00d0358007032003441c0103070881d0000b9403008005160912119203201300100d410000840c001c400d8010020021340e8044c038100501d09070340c507501c00e515698001c5c0d81c45d15640640d029540c01c40300000c6150408105540091102081410928010490282d11804c00340c401c0442410142d04a250030112201140d01520060303603581d00d0199261120030040403941800c0310119210040b00795022010000303860b084401c00740c0f0380c1c0b60f800c040c0c402404070b50f006108140940651020400401d401c2051048803000a080128640c030360051295128800341d040190b0007890002200c11018030b1940c0c481 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 171982446 1250 171981196 171981221
    0x706111b0715020303010e04140a0524010504060b04050607030201091505010806060103060e130503040e070305071101091e050a0606080c0310021303080a0903080a030218040506150922 81
    0x2d1601c0c40c544001c9840e03201c24020000300c01038900210700080c1d9004041c2004140400a50311144d48035601d290900706507401a1400c0703003800c4204458528014025401031000301c504100080c54030349600306a000305c0c891284618000704414007414006c0d001044403e0f408030390082c00c2d060300c1c021803005120078081c0c1566445007000048030f55020348125002d5031180301215201343d56402c06613541c41e0021804440381c2c002880005010340300340200364025000c50305c000c10700d403400c020000e2a203a80c941c074040e9141e04050707480021407a00c01e90240c00d138094101894011041d800d08501d0700e4508840100800e103410350008800c02d0108a2080c1114105e05540070901c82040c0c0704240d0041840300700d01400e850400300009036100300200361440c4a070512518082d41c90701e40d450035030040c00d500d0010a400296100d00300000103501a801c3d54211410003442c2480030110304135464040c00ca4050880c00260410b99940d61034900d40540000003400850842184410025042400c80d01 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 171983696 1250 171982446 171982469
    0xe12181f110a060f14010b0a08162708010e0a0b01030314120a0605040f061d2e18020a022a0d14010605041b03020d1103010b120c09060706111b07 64
    0xc610351f60450b0445250049542e140a015240c440d240100107004c4620b130028440b100ca8203880e200f582c01000d0480360b05400c445244a4a400311840c01d441c11500c4203481e0b0f401405402c40000c920814040c1900d4242ca40280141d9512125200c0381c415030440e501960aa4800c003c041d000c19007000056078020341c4c0600036509003152110503a440c0c2d00075001402d00d9848100b00490001400c00d50003d54004c20b000c07001c9a0041010f0009a4580034425a00c081c3d601440054071001a0186158070080211320f042d403000740080d22480f4407034414030003142d040ea0034a80505c1d00b400f00d6a152000801a01c91850503141041c0d28070007844030b440321942420000125454288100740308500201d8078019103c0040001304e00075071108050009840d5242d8034030865980910145028000807184640e407916256607060343d00e5401040132100110400202920b92610030a403900340d503000e103000ca04100700c401c0d004614010810305140030039080ca9443707145800000d00b13408444000d00700 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 171984946 1250 171983696 171983699
    0xf040305030c250e0a0914060405070605030709050603150603090d0909060302030303070c260a0314070905060a030b0d0305031b0406080f09010e12181f110a060f1401 73
    0x20074203000340b050400700c80301803072800c10404c0380850741205034484c00021002910309402e503600d003482041008502d0309503100350108001c1000c02c0100b40027a102c1814600d096103803003e002041c0c2c070000d0003110b0280d000403002c50605030140c481c88402d054014645c90700c1e450f20441c11591603030b0221103e4000b6900030740010741700c119032081e0010750750060041c52035987c0d4154140c425035007405003142c050700d50b82d04610381078070711251070120f514095502968500c0480402020369410340099400d050188003400307040c076003100e110000c4540c240c0ea8180c40e10360111080e0024011081c009800180c030001040070503502000546c4102162414100305001301c0400c90900d000380d024800100d604c88001c1007800b08241c00565100124200120710110003005490401c642241d416680030360118803505ca42003c8960038140000981d66240d2a0181340128a03112480030341540900c0302a0320741295080303003841104840c80d00540148051011046e042d0000e21307a040d40c9200d80340c0301800 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 171986196 1250 171984946 171984973
    0xc310b0609090406020a030f0b06090607080f0304050604120516031110020c0309010323040f06060510122f180306010b07050c06030103020d20130603021509010804080d020f040305030c 81
    0x103203d502707030b40980354505108040d4240310050740480c0e02070350980740c00c1c410800d00310000e10045102e90300c00d4010307042c50305040c44c01c44180c544102b858801c0c49401e2041740c11030901c00d08030a290700d4051400c0c019145040c1e003100c5c14050306120b032100c068000580c2c1c881d2011b001000b070030001d40a0340c0070800006203000c0424113148290f000400c07054070502240c0411441c0182241086c0240c000203034059442d00040d00501800c091703040030070070356052250410000d1081c0004051110048442600101d0200e82240072074100b44105500208280b1103c2a02c209000708091002d4100c403d156196244d00510f0340051004441d41c0c850084030100d1401c10009503030483c0c0c1d000c1c0c11440e0440003031f42c2e80043c1074004020000d602d07480d8190010503944a03c9001f059000321140025000c3c250700504c4030346070004480c0442580c0c1000002c640307036400924594059000104151100e1b5040075480284c822415220f040102c0072802101340b180200c001e0a0101814045907a014403101 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 171987446 1250 171986196 171986201
    0x40c09080709020a0807080402061303060f150803040315020c011103092407110a0b070e03010b030106030807200907030c080604050606040612110c0c310b0609090406020a030f 77
    0x20b41c0b0701300040d002c1e0040780b203031809045156001031004001904046003000c0310b0340d880070310b03070701c25681e0a4445506044450341889002d5090160300e0303e03d07040c40d0500f83c04d03ea4a10403031100030440010600d1101105200342d05894101410314001e00070030525004c0020715800075a0904030600070501e1880d07040f071510407110301607058110454100d0340c5840042c0d07100c2e500505900311b603000c0c0364425070010f4155410b1520401c110385441ea1070405540500d821114a8190b150107a0725080c07040c00460201001d9621881c4e000140c10b035410080300030404540340b0546001d8000e0a181c0c28041d00980503040900740d0201d46e03039091600d5071307044104016108140c480c02d030085402c00052100b548100b2480000b0000d040c0042500000011000d0b5140d01a00d15004260801001c0402a1502e5100808004031030b40741040d903d500801d03403070100074003c1e5039034686641c1c40181810540380d01c4256540740000801c201486d18040c20010f000c3d501c0940721200213407034010440312110152 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 171988696 1250 171987446 171987457
    0x61b140f0f0f0616030905060708010f06080c0f030603030f1204060f05070e06030a020f450d0311030711030105090a0f080306060408030c0a0201030b040e2a040c0908070902 76
    0x40008040c0e54413008400d500c0c0c2c161800c1d480080588481101012680402c4640e00502c1103940f080c80f60346c940100207401c0c5100b5001132040054500600003100390510035940308564500d0007075903075110a00002e00e548a5503011300400100411114454419011440d10840c0145028031900441c3c0e4200c0046030b100301d070b801011400742000c81f685818002c0145601140c946401498581840c0c10300300755130012548800b1469403e100d0402c040741c000692003103002401400d015500c210048401c2c12400703d0702e03c6000780b910096010500d4482e850320418410120700350b0b540c0b80a9800c0201441032442c503880e00a40c01e0202140b001480000c0340b6499582042251000241aa690800a1b44003800c841c0d03101c1402e00c40410550410701c02041d422003094001d10000440744005030944d0643e6401c1131007039240c03c01e908421000071503100513002064001c0380c01a4032001404c3c802c00070400c036a0303410916151028108640240009003922600402c503880640e882010314203a10a0 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 171989946 1250 171988696 171988723
    0xb010e06090d140313120c08070614070c050603070302090316120b04050c0307081e06070e040b0a03140c010e0915010f090306050f01060e100207061b140f0f 69
    0xe2003003240204110012081000c0084401e41789400e601102010a0090716041400d908546881c41c80800c8a1044848020718100c0c1c05400014942080544030000417400e41010010004075042080558000c11000c1d08000b4a620348900704141c00400039040380740c00038080d21801d05841c05440c4941055406c603414420a1580d00c41f050341d4518600c20040c00407101c0c2e03c42c1c0102200640c0d020b01140010b4441c0304020b000600c00501c1c4103504c0351014290700200d4202d0b40c1440b04041e17003e51030f21554902510041056150030000c5203a2025540c40508150044030042c100080041143d00101e6002d9840070000044901041440c900035920038030307009031a200d0341160b1b50051808401d410701a0800c0000ea9503a07440d41001c0c1c801c2190b00400741c2840d18018800150081119001114241c3c1c5c0d44424a00441c406941c58803c0e005050034040501e0090401440c020403181201d54403400b0003d013680c299500303581c0c88001160460407400382d5a114601500c00059100c0382000 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 171991196 1250 171989946 171989959
    0x209100810051f05031905120301030b07020d0306080d0807050903061f0e0c0d0c020307171306050702010c030e03010e010e03070611030f06091504020a0f1e0801150306030c0305010b010e0609 84
    0x1c1a1554106e00035264000c4402d40a82e1516040e81e40c25a00914002c600410010190b46448103000b820005088204030615203400010300c4070450024908a580d11030f4284611a901c8040040c1c0f02d40c09103401455062003840100500080407280c2e44c44091946540c07602259150200f402182e00201c42e4044142c100307021f03854000c0b00d40d41002851441c01e005817454003826417900c07079201c54210900d009115000440120325030844640310300420342c51806504100341540020302040501c01c001c0c08001c0884c82150580e44d0a501541c06065482c00821a0070741c9440130035140d801040c0290b6045280c8404191607030300c900220b9209905a80c0c5070342035030f81c5171802c00800181c0038001c0c01e11020503044c0c035802d5444034401024850280d8035281400c18441c0401040d6000754240041481120310b0013005141d04400307074906444071519020002c01d00450114010950740e40b000c2e14103c3c48000000a1060642c0310485d2420280d90700307120040c040091144910a10b8800303a0080d5 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 171992446 1250 171991196 171991213
    0x12020d03050703020a050f07021906080405060703060602060a0f060b0403060e0601080a020a290409050a2a11031201031203180201091806080d0f120e0601030209100810051f0503 78
    0xc0326400104611032006100009010f0008074008000c0ac0b2a04003001040c811000d22050180401ca0326900100030b20b424405a820050020b4a920018240a1280743c03110701d03030201014640c1208000c2c100c0034600d00c0d00e03180d8a040000c003078205007000b003186018150001c0380048012404001241e005170105100c02d10b0000c5840c1c440590031512128540c041c0b58081c43c142d45400108024042141c0110302402e041c0c0c44a01149d03414030109140800c0c4001c4502e030800c00003950310f400c6480c3c0c1000c44c00d60414524442c15403040880700007101640400100400c40101d040c04c00400d0150350402a4100200201d91103104121000e8003051016100b00140d000d0410424508a880c03500419400d584029040c030300b0081441c002e003c9405007450380c1c10315034030200e24214910000307414000c8008a0310240c0e1114010b0001900a919100005420006a900d039100500350481100d0301d404071402020010300c829207001c507a278103c492082c406a0300380c7c801c0c102600c10081c0a0304000 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 171993696 1250 171992446 171992467
    0xc050a1a030717010f05030c0405070912050c10080f010e100308030901020c07180b01080f0a020306011103071a0903180603060f0301020d0903030b0306010f05190312020d03050703020a05 82
    0xd81008202c90300700554401d1030000c200001d403006008040f00b0300c198054034148410141030028171401c8502451601d001c00c0750050340040414200e4211030301da0750402d4071a04001e0b06100031885155041800c0c0541c02882035806500107114030301c15411841c859880b0042c03401c0392802500e0742e60000d40d04080600220319007000541d00820480700041c9081c910444181c240b5141d030f88a0040e242844d50813008900440c050882002030034078002d086454400c000c2140380102408040c4070395808000100240d001d0711803248030701e6030b1608981d141d900f0f45c82d000d0010003c01c0070a02c9080e09182c0854440340001064031003800055050300c150041c0382080c401c05800017490701d0342c00081c0200f4400641c03800c0c401170402c0a000c80c0041001c0896017406000e551340460114001e5012000420150305080401010303140b0440d000d107031580c0202900c956441079a000507013920b807904170340d11030310760005001500001d4684050240782e036400001e034224001c080c40c4030003107a020003219042c03 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 171994946 1250 171993696 171993749
    0x110c19032123090d090617040c0b030c040501020d0806010c0f020f042301060207080304180902040204060f030b0108090a02090a02042601060b04050f041508060705070c050a 76
    0x694003a0440012101c00d03a0015074a10052214000b1480c005941400f040038018851000080400c1c01e00c0124103240000040c8050080c03c0308401200020002c06c040003c450200c034014002404c410340c590414207001c0104d0791080c814a8007500c20711006080c110300a8000e9441444161900200d01d000790f122044000b1031450100da00117007031112240c2d00e0380ca611440403a00c108ae060305450040d41000f408040c41d040c0c01007400d542c401d02040180b100000704490548014014203040340f659030882c0f2001d05040f18009610a0011401040381d60b0f00c031101c1100c1b24059902030000303144c8100103641c13201c826264020550010b00002c2c02600b01002e84079089101d45100618055442000000103030645d414020074107491000500051000d01035103016100b12240a4034051400c4005001040383e8014180200e4941c1d2132802d0800750a4401c03801401d06400b596034916052070000c0950b800041d04580c0700b080180042014105524040190342c810241048001465011050b2 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 171996196 1250 171994946 171994997
    0xc08030c070311010f20070f080f0708040608040b100e0a0c020a0602031303090f0f06030c0203190203091c05060705070f060c080105010906020c0f010f0e04110c1903 73
    0x10b11000c141c01e98030f00d0300c0901c551000d85c0040400015060311030210901650a805040c5040c0d000500c00b0402013504400c00c420fa5a9001800b0380d80e880418014000c40d004080c03000e40b04c603401140006030181c01801c0c1c9403041d48210043c2c1d529654107a800240b0000c64022560308100c40000541c0c4002c060348176082c1c80303055004079807440c00b255840d901680d104076a00061072403484141c000301500014a03c0180c01d0081c461001d40f03007080384540018110f4482e81040540311080801d03003d00a00c101c0e00c040440c1140c0c0100e00d007214201956a60061311202d0040d882ea06801c8900510005c0710a0401e50110240010352940001140e036904580b1050300e03100400000e02001440314841c0881e0103a00d52582c4880b50300d04030001d408030585030301901c1907400041012013a40e03940b1603410541042400c000a060003c40c6c001c0394210000d0401d20317005407406803c43c0803900342c400501800b1a4481c1115107800e500f020284c451102040300901141401708900751740c0415440c44030303 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 171997446 1250 171996196 171996203
    0x11809050a1b03060501030f1719080c0403150501060e03120405091e0a0912050403030c0b09100f091403090306070809012901020120120405030d020a0513060c08030c07 74
    0x502e9a00c036143c04084940030380c000c407803000c0010481810000c0088100d48030254901c2d206041a810302031801e04210404100c0003041402e2000440080d200710584001d5508140c200d48400740d00c40710100100701c02e006000c08070700328559a10311407030000741c400b4a404143e008281414a08410f0250f099000341030310310000145044003000b01309014219115104941e4080303103988041c2070101900f0b103281510070030010b003000207201203034201c5607043d010740d8000c01003002941ca40000c0d504200c07d958120203200e042c81401e00311190107804c055440d41c0156004030071311000071211a40c9100d402c14003a01034221900062300e02c1e001e079500c142d110322240c3c00460445034801e2614182e02c00c291a80811481e20b460803600c0e035a091184948001840e400701d50700e1040404c1d092002d020303c1c665592481c2c0c00c40005002c01c80d0a0040c1c50402c04c085209640ba80c64101000d0015003094552079401c0150102c00614503115016040b0040d030400c1e9500c1c0755844008030025294455a02035 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 171998696 1250 171997446 171997493
    0x1e0914030a050a200406050f06160203010e0d020708010203012411070f0303030f1a040c02010204050d0b18010b10031d060708090d0c021806180c03011809050a 70
    0x41010803414851190b9603071050842001c034880c43e4680e030601c4900744c3c0c05680510728218003801a6268004062981c260403120f042e00c4003512596034910a1480b1802501942042446d01715007200040100950110740c00383d0305050303250b4056500300d010034071071100c403412040200503051011410311012038076180740442d54120b11500e1107241c1a1280d12852003c5d003490f60410515600d441211030b00080501309100090001c00400d000b0210400e80380d10441d503800710303003000798001d50454004150140101c10500014107142d00141400c5842c00d03013411045294020402e81841580c400c0e0310020f10000c0381c0b01ca81d9800b1001000001246500c00b005000c1f07031a0205810050103210324001d984905041c07a1040701da0f4104550060000d060007402c240250042e0780300c40c190319190881d9034855040d40e0320034001454001440c1c80304211403407250280260a42000e0042d811f95994100304159400311f52030800480c0e43d01b14010340703e5000686200d002414100001c80c2507040c10014 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 171999946 1250 171998696 171998713
    0x1020304090c0e0f013b1203040306150f0605130b190f0302160605100b0d1410180c09050307180506060406140306040615020d1e091403 60
    0xc1c0e10440d808400071602003180b002020040c0d14201c00c01c0c9080400c2803078001010f051620002040440c14011400c03542d29114442440ba524010181c0341c01e98020b0103081c3d0f81c03480355501c1c1c0e120b0340180010784015040900032a2100f08158403642102c1c3c8100300d100006150510884464000050003141c403410701a0001e010140b043c06490251480c440d9200b42d40b034246009015102d1125000e070a05005000040d0039030304424558807042c0c0c201e0350104080c1d0381d40c80c11805590700740c0c1010301200c4000c00c4601000c42e982d4002c80403d00040b82560003038640000d4442c40312007500c0b880208600a011400d526480340c0c101c4909100c4608046015940703030800a4140555900100e4011014112a482c0012a405019081401904c00c1c81c58035003803480040c402d5081a5000004000000c04a041c94640d9401080281241869030241d00c0b00440300070f48803108030096100160500c01c50300c48040030203031403025032030301c986a010106103000103c00d440c0d090106100e42c5030050403070 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 172001196 1250 171999946 171999959
    0x30608030a08190903020d080609011a03040c0b0703090603060f0b162f04060b0a0c030f0212030711060708010b0912120f220f05090a0f090803090c03031201060305040201020304 78
    0x50541380b01d00c0798000d0000000d403120000c1c00c1103001814584107512a00040002c010442c0d030b111a8549d032900059034943c2c95080000341c5654070383c0b10102c0b1b9040022a6001d15502840030019542e080ea42407103060341e68400703104070915171300030356040340c00c10494840b004484c18050841c142c820002c3c0300264013032072010344210414030780d1007000c91509071013500e05d40303498440d120140c00390103422800c10080d010002d1031007415400007420304ca04a854268130340d0007000f17034489990310008070303965a00d490b00005000c99086c046c0c40b80e8901c50640810051800369a400341a1016440e2003403e00e08290100420100b0f196075120303481c082c444c26580c1640c08840107002c203071032019040d40e55409400a0201c880c0c070400c00c2025110300c0d00401d00000c46c060890320304454003214020b44545400398070500400e5601003e00703c0a00d00f100c05010091a94045d6210b41c0303240050390035a40ca001d06058032880340c038041d000144550001130082034040ea000e56041401841102d00700340e114030 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 172002446 1250 172001196 172001201
    0x3060418060b01030c020303090706080612060703021b0c0904060f0603080f090f01110607050a030b1c03030c03060e0a0e0a0b0405030909010506070b150111010609050406060501030608030a0819 85
    0xc50507140c1039110200484156090700079207a0090442c4021455490306100d581e0304c565040c003400040100000120b455592880e90710500c200464069840a05101c08050025441862500f200e203001d8490101c0802000c5619012400050181012070350342c2d5950300014890b035003a50600c241c3e1040040045199540506422440b02480b2aa100c0a403010403010803801c040007810042d1125018001780307808510b40d50804690304195840314042a0290050960000016040100d007121060313060241401c0c505440c0c000d8030300300603040b1000c03421025192203001c0c0e81400ca04060124030700300015400700d10661040c2e000d6902c68030460f078071502361100588040c2c0305a400464458440d1900b400c6080c010282151907a18044640d554484040300c014440942e04460094050540e40240702001000c000360000b0051036071261005c8008103000d94066400c68908403002c00c0c554002c0c400c0b00305403401d1600460415090420440300b2902c0104000505016103044905020050 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 172003696 1250 172002446 172002491
    0x9080c103c0504090608031306030c03061d0601030501080613081303020405070504030510050f2a040b0a140a091a1606090b0901050408090409050c09010b0c0709060b0d02030604 78
    0x2580ca10350b40b98138142d482d1055900541142100d41c04c2004507045a0740000013a0007100e034541008905209007110603002000142d210f13542109202c44120600107080d03500300e00c03c075800d0320308010340e98859400990782c030421900a0840c0b00b150201d80c0100d9440400341c52107246904050000f152603134023040903680c0664440c8003282010034107008102080c0711000708289041002c10207407030090280070081c6400381c40e9264141c05001e03007004148101080c0c4a46c0911300c0320203540d540d0398100e801d0300c56100702800b00021b0b00c910103401d000e031040f808031000c2c00481c1c3c1d0388000007424604c5450081112101582d003030b12080054801030000c1c40d14078084540110301c0060a009030342048003d100c0b0003002003c035645058104800694680e00b9580801020364000501241c20b01d8820314150000f41c889074441d0394500001b91044c01c20008000084059007075a1449035140c0410069030340600588264440910614600143d9a40510741c082c400400109184840c465400060705d0301 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 172004946 1250 172003696 172003817
    0x70b0d1104090c0207120201080105040e0309090405030d060906050307030311070e0411091e0c0310030503030f01060e1206010b0a12090309060e0607050a060e0f030a09080c10 77
    0xd551020107120b13014007404000b4119040b211600408560000304100b00500030984a0756481322079500d00704041055405c140300140910a10341494104203a032030704022126070805040040c081003e41c414080d510440340c001e401425247d00f955029105840c40001140303161140140008050310708078000350040d40200e1210203110304a105101950100910400b030418440185030303444191006103d40c80320901041d82c1c0c40b80c0b1044a18020440c2c05c4d44007605510010041c400d000601c905210304079901c6844062182404105204400c2d4a591a084490300101d00401004000c01c005002e00d040500e0700c82c5500000700c542030308851003228113800250500030103000450f0040c40b14100c01d003044034031030b0400c80651b540f40c1d0356201009004001c1e90316046070010700c0b070040103240100d0510f2070503652511000e180090000e4850f00c1076070120b1041d04000e9589040a2903401c203042000c1e901d8410249a40710b840040841047e1520040041c44420194003030328000c90032800c070403 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 172006196 1250 172004946 172004951
    0x90501140c1306030c0e3c33030703230412081b090a24030b04090c050d03020a05010218030609010c02030702011214010f090e0a05070b0d110409 64
    0x69000e00b90408006508540181881c00f042c203605250000304410078400708489582e074143c0c4009202450305034644110300b0804543c00c03a0300c1004151b2000d07244002c400e80d640d504600020382c0c4c1380c05401010880d01c05450a1218400705c0c08a43d00085511601c40e0402040380d241e8407030350b840040c01d18030921451070071101c244010080d8400d032882100196141c95842420300c007040d10311036800701201b500408800500a0099110800084002e04512060081c54407030408044050705170900c03550300091601c1408000b524061058403440f98000060580e034508190500581160400c002d4003503200304030f03050000444c24001051401d02d101401c2c1580141c0100b414540340000e811304c85540d0420340100641a8004281c1e41c1e03041d02485c203031409280c840c3d94840103265aa181c409080e6003d4000b15031000569151000c82d140c10342c01308418044800c540d41c8800c4618001810754102c0b0384208100032268000d040015070f0410300184901c0d050065080c3c980c010791000b0192034 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 172007446 1250 172006196 172006207
    0x190201020613031e110601090606020f0a330906020a031104030503180d060c080613021603030f0b1207060906090305150a0212070201060e01050301060315090501140c 73
    0x5a040c8642504900501c540b0407402840750350251140f0500410b82c031500090a907a07040742032041c1e49001c000100702c1c0560742c503541c60700284405001c241c00b030340c8023520607420040100c10000400f0748042da00114000ba0340011f41d0000304000c0c4080071070146038042603c071400000c20500c10020414414800143d40300c60f081e40280650358045111010594148010004604003004803140c80100442030b220201501d0001040800c010a0140045241101640e101500068420b000b074000315006403040445100080030f031301c6608120412040c0e2201d40500080c000c0c0c109200700074020758081030325042880130404040c0e846800c0185070740280d60400071355130018400005000d592504c3c0005508584032250b845a51407401000610aa40000c0c419109941524410390407488456128208440002d0180455020328245211940f000081d6071070144289001c490380015405040003081fa260030040c06802da051310071395200d60078041d03042c0088400c02d01c15003c280e100c0c1e8490 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 172008696 1250 172007446 172007449
    0x9020424092007080d0908120108060a0e030d0b0112020c0a23030412020105040512030d06062307020a0f0e071707140304021207090b040f06030222020405031902 71
    0x39121a000c81d01d507090001030100c501d000401c103d0300216040b010a40d90783c840040082c0050010f001c0242c0884004589000912810080c0030b040304d031800304417000c3e5241d000c0c520046925031100ca00c0950f00400150f0741030203180e00642c3d000901414070b040c250003284000e0041e64040a01c0b9000f90304518825000c218001a043d00c00b4411118540000d83d266400f895aa110f180504103081507003403041011a0320640c00c96020b0140034198101049102035616681c0d0006000c03070764120b04041011500c5481000784558403842c00d030b484154000010701c01007980e4040d400a0382c0241c0142000700e8034640e6035050070006c1001d81889610391030548000be10284d080022109c50b03820b40c900f4803444950102201020100e4020542d645c6d1b1a1031000a200c248090201c920038022034074001420541a4460a40203400755800c2c02160312a0212104480003804000c0d4402c2c14401c0b0000c0c0412a081c01440b2403800c090018601505d500000c3e00d084404508800300300b0f0310130490000c5 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 172009946 1250 172008696 172008701
    0x1c050a1803020901050607060906021201030b07080603100f0f1409151e0601020a021e03070f08071a04080304030c0515120601030509030405040504050703030201110406020d030902042409 82
    0x21000c1140030341118119800281119410300c80c3ca403044801050480901c100d50b03004840f682da01c1102150790300c01c0340c508460002000d10096076106010800100d09a0140b0700d454401e0100401810f04264a404850024411200d0b00103010ba9660032154243d4214403c81e81c0310600c910004100d40780c02e40b030385441c111510312525041c080000034040c17082d400164490191901c0300d9032980e00e6640200407854034844c0c0070080d501c003056000c2a40084010058813a01035000d07015121400c0d20b170204041019118418542079500030201001102c41008103440880c605005c8a45080d46c0c44c100c040c03440e0010741082d141d070342a1440c104200d00c1c00e44d1160280030040c5007817505103002c0c0c5410300325007030b80203003424145500c400008000301c00500865010b080c00410401180c2800c3c107110b9075407030341400101c000d50f20305108810003900301070a0310100c81566004040721405104203e01a040f402030803600319890303014080c400c000180044010101501211010510300001e070400e = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 172011196 1250 172009946 172009967
    0x5150918070306270507030204020a12021c050601020a0309090903020a02030d020c0405100302060307030f020903010c090e06030a20031507110c09070507110d0605340801030308091c050a 82
    0x900c04181350b14000062002c100a41141d40417100140c944200c03000c03c0d10520180b004295843d4030000f00460002040c88900845142107501046580d54500069a8a1100704030190205a5018041010000702d80009140520a2043d03c103445181ea012031718080d20340c0c00319000360300a09201041400e1034499603a00804a606d6547c4140c61a004603095110150015042544441403a0425400c64045455500001c1d00800041d244480c006006155600070244021505004144a0b16000811604903074100742d05a170600464058240d08441008000d9014069800d0340d1900860780340d10369126404a8031151020f06460a00030305028022440341e00c0b4503044420300600c2a07215096070240c5034414264801d011004000942d50941b0100040001e801d00d4104801e0034841c00b12044482541d641640c01080110900000342440580010000e078030500100b010078451442c403500301d03929800ba030703000b0802440b412030351034110085880411390008500c641da95104001c02c1 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 172012446 1250 172011196 172011251
    0xb070f0509060706020a11030c0a02011d030319020f2d0f1009080f0706090213021c091a0103081c110301120804120606051305150918070306 62
    0xc0c603000500700000c090707006142010381071640c0402c2100301e290158154031380c00e04400342101d44884840440a0b6a2055610103d0009124180d4821044980d0340039008012000703014508040e40e0f80c0c80c1c8c45852071014000d4045100340c20440030142401d03c2616504904030341001400102070031454414115a116034600c1ea004011010f1211004901000c500c0b445e4030001c6070301101e40c140b40300c09000d000340324540c03510300184880401005034001c104891081d50101c000c00e07000600d8408a014590564407614800d41c84030103c02240c0d030044400c02d1040200c40c242c0301d0052400c0b4410f140c00d800840c2d52101c00140441c03400f0b1604410144004140b00c10700640882c01900c1e500340c001840303403011082c24105010100083d10059401428071602c0c100c0341500e032420054091b000c0e0b032003031500440407141200d09040c0e4500a0034032881260030011217a40405080c0403d20390000c1c180e881c0b542c000d40e498100c803034003401540015402248041849005c070710580c40c15a40645548 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 172013696 1250 172012446 172012457
    0xc13080a030206060103180b0c0a2a0305070201110d0207081b0d0b0606040e100618031e050705040c020616020703030207030b07120603030f020c040204060e090a11070b070f 76
    0x100010ba070000b1003580c04403003072a0104850320f408203105000034550400400c000381a40812034006280310250000d9580c4d035480400c01e00b6500da0b85150619481031541c0780c55805801500440d000701c0040080c0e500c10314213109000e0020313850904100c0b00c00000c100680180340b00f004400800c1025203520700940c0d504803050210000040c0040c411000010001d400000004082e551160159401030090700d6200c3c4861500035448081113004d409840046010b1104030510803002c0c9407040252a44684410700c508520740380da201191590004a41605c40c0c560080b9090726540a501c101d0308050300285424188030f041d04140c02c0384422000d04540c00f6050800100340d00150036812250000200c0e00d0036221414101c072808201c0943c805400d00b4403a0000415601c01d11280080310386609603030119440904110a0344214410703e03000500510349001d00b0b14100960355003104954000249000560f410004c5070303000304001350303410709040c030810050036008441d000726540e851a04 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 172014946 1250 172013696 172013713
    0x110f120f01060e0f130b1f0207060203030c04050409060e0f03070311030304050604030503091513050114010e010501030e010213060801030b010e04030219111f030b010201021c0e030d050c1308 84
    0xc144c4501c002510703a481200340c5900040011801c0e80480c02945014140800c1d008019004003600c94142c080c0100504c1004000210103101105680c02106180c024615003440d000401001d8080824207072400b0b6038480461070307a13440c01c1240038000440741014644404150502820742e5500181d0500b05400030002c000020307001141e015130044d450f05219450340c4940003c1c500c0c0404000d200e088a50250060091030703240c4507441580c0b00d118030020702c01c01ca07412022000c0c00400384a0101110400c5005002540c003a4101400110380c075800181004641b00000006507921b41c00200401d03503110051042c00030f030514850241154021451031341c00e140d86c3c003c1d0750b55050740001e8141c2d03562a170260104140f8141c55000600b000707000d0490054010400748000d900d0300d42103070100389004c9404403554018020b640c003406140c00200c100c3d4000b120004081c0007506c2607e0414001000380c4804a8200d00c0b40501400d13803842510344601d1b259811140d14141608410096480441d0 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 172016196 1250 172014946 172014949
    0x50102030702090f0c040305030a020c130b0904140f010212010323030304061e1409010608010b03030316020304050306160306050411090d030302040824011a0d110f120f01060e 77
    0xc2c10b82204103490b1040081d640c144005d0b0031401590802400c074040007856404003580041e100c40700c9901203407102c01e001046000ca10888190ba140c542d086000c020006010600c5500b03809109281c0c0c0d01500c180343d04519415007242d020000181c19141d000c0018418800d800e0348151440e00308000341e144005500340a9540c174000100000c18035034540d8030421fa5240c4280b12504031258541083c840404480d604d0203245c1d00071200307150507628241d80050760f103505004580010318003401952450300c41c0c2800401e0030100030401c0307041d80b00801000540791820045d06205152490507550b000a450100409071401e0350720581c415401e18180030308113015403003258a400405ca42c04156003451b45000d5029026650103821a03001e00c4880b0304200d14010396425a481084401c104960f80f9004034540c411040031008070149000e1041c240c40ca407043d40a102400c0f03040d074541d810100b501c8103900c0c00b40d0003114104980c5142d082070103e6410160743c205d024000d0b600703000502141d201d0 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 172017446 1250 172016196 172016209
    0x21050c0d230901060b16060209060301180e010b010509040506040e0706090825050f0307030503030a0207113c10030204090e120a0f03060e0a090c0e0402030a0f1b0e0a06050102030702 80
    0x1030000340f07400c006c00034142045a03a42c1201d10855014200544941e9075090420041400100d540403060404070720140f103071418813924682c014140c646604185d030142c10710004081c02041103410941e140c1045c00c0e0322100300714440c010000b9680e0b0300001814404028104814422520403241c200c00c01076448a03400c8803444240c0724261541e4a10382c0c92080000d192010540c0040c025000000070b0040d241d50a030010181103004440c030684820404040c846241e110030194803030741403d200b080461041510510226454aa800340040000840000c0c1c401e255820000f02082e400107080201b0142800346d501c6003641c50707018051041801208001c20320820100004100840d100b0201050099202d14084d19400790a04600e20708144c11100605008009840340e221030b0b400003030320100f16000e0511455001d0090203a00301540c1d1540404258890219540c41d52862000741141100c0540c4000b401c01000f584010b08010300c91200f11401c5400560454108002240150301c448 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 172018696 1250 172017446 172017457
    0x3061315140726090609070e060a050120030a050909090c010c061d0102030a020a0908030a120507031d01090201031104052805030304060e03010b0121050c0d230901060b 74
    0x40c1040415868403050003c000c007010f9106402064099040c4500c0c200000740c3c05125107007210440c0d03200b6445034005001400d080368400d40c40000700743c0500265100c2d48007661403044042000c203441f020f016049041d0380205411400140010481125524100200035003000f15800a81041108080028006101e80d030300a000c2da40c46100581c03110420604a601c480c003803c00842d16410600a50406544650354010004030200c1d80452241d2001c422140c000c0e20719180c400710481c00c075000001500e0000c140030241542d4103114520092405c01818240703401c0800051824424800902120307241c64045094040501043c00203440d8500301503040f03000c43c00c0828588041e08685560140d0701c2d00510341501010400058454002c88841502c010844c000d000806904004481c4054100f1400d0070b0b04005411403454800c0d65803001ea084007100c0002c3c1e10713144284012206817203444008075520841002d00e407641450448440e031300b00ca0500001d001152802003655040d000b007 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 172019946 1250 172018696 172018711
    0x50a05030604020d0224070203070608090601150903060911130c050702040f150308030a060b070f0f1109090f1905060402190e150103180b0c180306131514 68
    0x80f103040259035480030642200c0f0001c0a0101b440d0941011803003258201c140101c1c06881401d0380818510b0051804602c514800e000030a0584c0c6052103130481101012440f50a020303201d000407000c0f40c0b0a005110304140507104080c0e20120790b80c140b10180c00d032002a0286117140503c0c03071182d10f6001c0100c03564203070101c50115285805004036001401e0510000c20761b92050740000041015450186100e81000d100422250f55103039001c403018070420100800480c2001d00e0200021040e040c04100350340240c03840f0640d0300c0080045500d511082d62130604590180006a6010508201007200d142c10302c441121103041e195100783c2e480d2006032009205421920000740b81000001d900002081500f10003415401e203a80c41c0d03903249425400c030500190915041d28000d01540480c1c50b02c03a940304801c0f04203039071500d03090711560308a0001e0790715480e0f01e039503140081d41d8208021400b5400840c4060070112403860004601c041c4403400ba02c07924107091002203108100c0c958583e020342c6 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 172021196 1250 172019946 172019959
    0x1a01030e070806090105160806030d0c060b120f0f031201030b1b0f09012706110a020d06020306030c0a0b030406050402120a03020705092419051e0406050a0503060402 73
    0xa003a00040c18844181c002c1c0d109407088500b00b0103102c405400403030082c092040d14100d020080a401c54200ca000c60340030790143d000d8070419039501c1c8511a0b901e50300f070040300000742c3d5607400400148030303040000d0349071004d42c0460081c08088805001c00f03040e5031027003002185000070401103400c188605100c0904000c042c0c2001417a0710f912202c17001d00884170b414106e0f07960074106084600c2c035008410710f07600003003052011104002c0c02e14003a00e144400b0407030308042d080c82d21104481890510b01401d803540141e9500c1c1c0010b8503040802200c041c807901d80982c803480d00e0018142b50524034924540720741003d010801c900c003030030001c40f60050340142c000f240650b22400415028a0080b603a4007492151600c3d1070240356011440c00240c4100f16070044a9407945100c00c01810b4095032039440c1c9400021500295180800d80a59509800b80504d4019a0b42d40005031003507100d0315079621203101b0400080c14510f4244a008050881192000003050901020950701c0e81d0060001303020701d4 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 172022446 1250 172021196 172021211
    0x8190807051903030e0705010f02100902031c1e0c0305070b040302030405130905010506030f0706230c030c160e070c03030b13060503061311190f090518011a0103 71
    0x7006001c00258034081c42d01071041c20740c0c81c1c54002c004001401c0042024003072050301080540c402c000380e449a000c154010802c1c0702110154800820611408903072510840080b280c142d62404d182c290000c402c0e84841503003400e8001c5104070043d003403042104001c15000b4050000b600704060ba9042500074549010302d0b0307100e10b416807652086421065114640b042440700114464000155152007400244103e4503504181541d41e411a00840d02e00d42201c00140940ca100e012840d0418092541036030b5203642d00700488407903a00c230401d4020b103500f000460313055050040203030240003408216095256880c05001d01c3d410b100141000040101035240b100c00d0601c25000000031210043c800c03140b003003003892040000e218611032107009025100025041c1000341c1444803031f00740c0007400c00d0191a1028200410802c10201c0391a64841007500071854070700c00c101400181000f508001054202512940b9918a00d40c8035080c2d9a81000f07000740a00401002ca00c481c60001e09003c160030 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 172023696 1250 172022446 172022453
    0xb06030c0a0921050c09010e060f0a0905070503180a050d030f0f06080304051309020303090d0302150108150c070c05060c03071502070b0603121606090204230108190807 74
    0x1109194400300c0c140303a92903030080b40b6a080921403043c00d48100304940d01a0000400d000751148244079050300025504000b400c0c13414469940715421314010003001100303440c1c41c000000c66200740d0300180050704c0841041040360b40c114581d040c420301040280400005960307800e036100d0800320114200341d00d0300c5002104040b07a812000d68201451000e1043c81c1c0c4851143d0340d00d402a21410348a031000414590f0407034034a105003502660040c002e107240460f0082405665000403000300c00318800c80c200000c246081403080c1c4c0c041e050490140c040c2c0d00c0036501216195101804929140340200b0101c000110700750114000c0781c40035039056440b00e0000c80b8041c2540a55500a000c0102c18004c20017012801d60081031403520510100c2e1407503d0300e405155585062900c0c200c0040c008002c010180c005031007000c81101d104000218500700c03d40e02160a40d0340340315484c840154508045034141290740c80380c03405030203580020310100358881c0003001c580040b1080988000f034005844400d2 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 172024946 1250 172023696 172023707
    0x12a050714030d090b060a0303020a0803040309030c030b010501031d0c1e040e071a0c030a050f040b1206010807020c150904091a0901060b09010c0602130510051201090b06030c0a 78
    0x41040c01d2050300e84a1483d482c16001400310032904840070505000001c0c40c0c0d1610700b0090040d03030307010360041010301070079070b02d03081c03a03600240c810340c00c0c080c41100001c0091405801c0704041e51088074008000c3d4074010002d0141c130f81c1600e414400b1109070030300c107131a198002010714591408440500c10380301d281c44015200300c25101456001410800d03107154681c6d000a1a00450303a0000d0008076101c050320100c41140158100d12005400811100ca01c0f64403c074050444215880c07522850640d546d500400682d10100c50102542402e00402035150380021281e50f0102050000d0510000340d0000200e8480604040e441c00100c04540a03001f9100c95000c070700020341c0207022400040091101d61240d010131964442258202040440d03011004400e640203064181c40300b001c1d0001955030000690081d81044501c40940c03c4002256554000b15080e46261915031540d2102030380b415540840c0140c00c28425281800c10051160701c40c141165070203610341c03001507221082100c04945 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 172026196 1250 172024946 172024973
    0x20f12182404121e0903020f0603060a15030b0607060f0b04050c0f0703030b09090703050601090c05091c02040606050901090902040320010917070f060e030c130e030d0509012a0507 79
    0x1581101001c100d00c156080709170170f429a8000c54005c103600e901002044424481150f9664000d0b10147c070403c194103140d160200720305003604011407601e50100100d01d440c3c1050805a4080340c40310180840304a42e4800d0041c03102058805000c1c51500300300b00e40c602c0c0300340c007007440141c9030006981060511a0b8030007034001100510391001c2d07090100e404d40c0d40b66103500042d20b107405060b0001445c0c040b03511590711801d0540d1545410310b008030007041000400820035404108005040c400103035190700c1a140074180d44c2e103e0b9521044201c0006040c0d829079005400706620420081c13020808000d01004e41869030b80082c034600e801200101d8540070150711503074024040c00f28400c51040080380715001c2c0e0b02c08024070700403940da8141c02ca94803009001003580640000000d564941841d600700fa4032a40880004103080a074115034a1450b4410004013001ca903a41041c40109075081c001d81c00c814100070701c1d101c602d000b10084003804071700c1c0e05007500a002002440200704200003c2600 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 172027446 1250 172026196 172026227
    0x3100204030b160c0b0f04020d0b0424020a0801051504180c1d0f15041a0910021c0302030912120f0f010b0706020f1218240412 56
    0x103440e030780e0341d103440d8024000581c1c0d80103c0b08415070007a0281441500003020703468100302e4000080e281e0411030307000700c00090801d03a0000d202820180109182c02075083c0203911130102401e00140055418650030000314001654600400080c130030198801051815280100c0e85144001e820300040d28040c8201d511071103804c034008c2c8035003043d0117031ba51004000c1c02468644424012100c803e00701d00c1400100f80c00c2c0d01c038070171000d180c0345410484100c140e050000203603545000d8075001c40c2480c0680f5200c81c00381c25a000104440316007001038030002c0200300390009045010704903400014110300c90f01a04101036000c000214030750010044a40b09140a0001075903030301b1060100082080c00302d81c019001c52809001c5545000d00c514094126002900c020303042604640d41c480c042c0d440480c42401c8000b00703018035900d841d640d08105000c3c14590030000c0c90300e407240e50302ca810308104201a02c04001c507054000e0143e5042904681e015500c069243c050401130300c0e06650766501c83c007080 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 172028696 1250 172027446 172027451
    0x6060d0608030c0c04050c030403121e0903020c09090c0913061b0e0d02060d090204090c06090609060906021b030f010903110f0106150c02030a050f01020d0b090403090302010e0310 79
    0x1d5401011000f0544480803c0540e5441c002c0c22040c0015a5000d50b46690546400c000040100b1300c5901d40120644404001180300c0303070b000c55005c2d00c01c421030501c1100656141100801c240c2c0400807801100c0d029a080000d0703180c46141c4d5a1030340300118400e8060007030000060245001005010340e841e500c1041000680c8904d4111310700d4821003426100840c05e104041a20f500d00382008201b100c2c1d00500d01da141c11642c48141028000c4144100e81042e1500942130001d004800307500042c00c000d82d26003d4440c58010028840400341d408030051183ca003005021817680030a4015440703805918034038210404074082480c0041032030325441d05510701081102017581c0640d403600b424099108031100010050b040c0707400ca071654461030040700390441200d40c070350340a00e9243c0e01540c00241520b55004080c1c0b105800c0048046108104d6540080d0440703114149105111442c00d0903034004206107020360700a41550481e0002078140142d00c02989010b60b01000b201402440c405c60a = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 172029946 1250 172028696 172028699
    0xf05040b030604060e240a05090f06011a0403050f0606030d0816051c020a020a05010b0a06091a0903070e040204050a05040203031b0111160b06010c150915020a27180506060d06 77
    0x68a00c1b1400380d9900020700d00340400304143c0701c4001900384501e62032030081c1c00164600080b0740a10403803c1e031003030402031040c0070000101d0414000e01040c0903031b400107420740c1d141c1403042500380389041c02408140308001040c0303d054080301941c6900d00240303090942c0e0f103183c40c10354482c02400b0703281070612141c000550140d9240c0d0100d400c043c014480e40081c05a0800d200401c10300c01c42c0c40c000c0100003140c1150411821151111a0950742c01002151703140c40a4000400e080aa9540100c454800a44240310450a0600c54280e1116821204000608051303000944070701c14005000380028811000c1c40e04030500b90b0244010000090126540c0c00080c000d44000352690a410f4800281e280c0000710380d54010380c40003c0e8240c0c401d511210034881c60155500400c14281c0a46845107000d600da07040d80c0c4a4801819081c0c0f198030340b00720000b11440003800802d032202c109105010141d01c2008001520f501548403000140404200c2c2d50303d49003c070703a00c2d00505800d030900c00d0400d0f60 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 172031196 1250 172029946 172030003
    0x12d0303050703050706020304140d11030d18062c032503090e07020c0112180f0c0503010203010905090f0a11010c050c03061305070807080c22050a060f05040b030604060e 75
    0x520000c0ac1c0960f42035034480040c44d14141d661444a44d05401c5942080140022100159001e0408222101e01940d03440440740c031201e0032258080c2c0582005030030354059107805a140c1c0142641c2da400c82000f1458410f040320003c4207449074220500714008074811038000c050107140341c00d010348951415480783e45000e1000941e510003802405011448042ca52300d1144060302603e00514054024000c241145648040d508c0494260603503400741488030106460b60b01b13000840c020108030f4400318160a1100300e45003044d03401c1800104a42c0148041800548644900001c0708803d0030105140d008500b040c42c10b042c044080d03940e043c001d0b40b04002c00d685c04026100807460043c011212400c3c1c46100096540115019020035a4805020340c00c09141a100d444111400d0a5001c0b11690090304d440048e9130040d01c81043c083d0321800e040c09106412002e090060904840900c09084c81c44d000c00d460301400340014000e5034861180c03030000c1208110380040c0bc4045003849025901081 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 172032446 1250 172031196 172031213
    0x181807080a0b0a0f060f120c09050a0e06010c06020903010e0a080c060f0403020c040510050907090504050a11040e1302060304030c06060506120a0f060f0e012d0303050703050706020304 81
    0x107441466051410884001c281403500d503020641d24284428460b550401e0070640e038401100c100070040007120260302405032450f000d02001000a52101800c1c40d0a202c2000341c9000785800040801080750f0406c001a80c1c0032820584031500000c005035580402da02003805802c002807048260301c40c1d0924541000311041c001d0071841a808255a07042c0c40740813040e40c1800c0250383c0030b40142e000c3c00c03040c05149055030101781c101c650346c403c0f403514940e950b01107801c0d040308a9501c404180d014000b003003603041c0740c0282503000d85000010005075200c0365600030380340501c0c010302c0d2514504034009807000100e04107201c40c150700108202c0c1c6918040c07400401c050b620300c40c100c6440381010302c000342e03908281c03059a03040b500310907a0f044075a84403e80140180021718144000c15140ca400065071510403941c40040e08024004030801e41c1000000c034210819220b140421880880790b00c41c0b03424500200c503003900d82c1403410b1030b6184000e0804580b6402100c0380607040c02c0c400801c0c0310401140c0b0 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 172033696 1250 172032446 172032451
    0x120603071a0715060b071104020409110c0622030c0203012418181b050604080a05010509190b310605060f010e0f0d0f08031b09030318180708 62
    0x200400f506600c2424070903c242c600e90300c0f403150310071030030b0084900045d00d07044400101000980010304041e51407686405841002100032102a80020300c10b041c080b00f07000f080e50209a070308034444010038074500c055951941503009020400020a1901159003c1d00002c0c0c0740d100301407240c250000006000043d540441c8102c441c0c0c0300e00b0340b1001012403424014043c803107401461082d914034850f2683c2010300c95028520405071940c00700402c0300d0b513840780a000501a920000c00000007240341160031264050460a10b40e80000300610b2030201100080d00c4003a0312030888034071521000c250302c030001d241e8421003040c80600792408482608a034040340750f031030242c1c001f8409510b550003800344000d50100760b00d000480c5902e51000c40c0c186004035200900002d4200c40684203280c83d28a90116641022200c40b4800030034081007941c0d65030f80040d5844207000c0c80f440c140c0050002952032041d80494120071401114043c0d60703a8608100c10303000c4003048080d1025103401d081c02000c20004 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 172034946 1250 172033696 172033703
    0x21060b030106110d05091c0609030e1c08030109151703091e09010b03090709090503070605061002030403061d0f07090c05040e010905270a110402030408120603071a07 73
    0x45240d400f040f2400043c0098400403140c17100c51070a5203039010f02100b9a010103010b2440d0309000f149000240306c83c031690351041d0181d0349140d03000303d6113001c115120340c001803054000d501c030420600100c2c2d410b404a030b044404401000a1404d103170003101d09030b14165400404074404002c003024139000e010009200c6200200c030a040003d0700008050400c0109410003600b000390701d4010b00840d4880f03001160080881401c49600c1e65941901105440c1c1d4510111025040410b82100f044400c2c0101508000115006074801d400404025a01d0040b8030001d001103858011510444640c816000b4100301301360180c03641d10010103000e50b40d07100300344030714041c00e0325024125160610482c181d8041c1c1d030901487d11040c3c1d183c0840710300504030181c608401010005080d060f4070101c3e483c3c4110008088000d003d43c002c0b582031150100c0400c0302014000e0b40100f0404c40041c00c20320440300303540e0640b4107280003611501d0100b454140c141e0010340c120030880c07403618400c056210182144134030 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 172036196 1250 172034946 172034957
    0x5070501050f01140d0203030c01060611010b1008040b0403210c02060c0301060504060309020310020415030509030f091e150909130c0e1509070507030f110d21060b030106 75
    0x442c000408640c81d0240302c0e1050307000d01c10700c1d503030140d00c1c1c105000083c10b800201124101880d82c4082c40c00c46030141d204501141184c50011202e0302c00b030007441000b440440b8426007a0312500005800913030024002403112096000240c01c160007100c3c1100e2401c1c0c3e54020710102e90164800800030418003c80c2d001601c03640c40094042032031601120b040c0ca03003540d5036900f001d02d41202035014147c5604101da05006840d8002e10f4180b851010b000140b00f040030755610b03420442c0c000b03402c80d1070140089200e908100500340c44004c500b0f049921524003a0740c0c42c0c941c810000312000744074848401283d80901190003031200c0b51802006800d43d684101c4009440e6200c000d41c0076501040080c0003000750070b0fa130800f0005101116141d951201c0c1e202010112048804001892074804403042d001103200405c1401c02e15500c100080e0703220180d1304090b030300c80b07800c3c442065803a60602c942204003c4c40d140f2a504410401186002e604800c1800780051900c9030b620000700e030024041d0600090 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 172037446 1250 172036196 172036201
    0xb0a080603070b0a12020c0f0705100203070f02060901050702030609010606030c0c0b041403071506090605060304020f060a0c05030d1b051c020702150a0f081608060402070302010603120507050105 86
    0x240c046494030448035000b00c1d061602e8101c440c160b503400801c98030000450740c01d100b01c54941d81f0a104504c451107022024000b00b0342810100410568441c2e500b400310351090000c24005090700080005090701198525120555000100c80718882c00c3c0000707415003d2a0103028000700150050029901a40c40911001c20140340c2214280c65014015008401c400007240100740e50000c002d28100803601079905c0c258042d03d45002001c190028070485c1581d5140403c4009541c0c0300d041e0181c00101c1d4003901d1030800760001100b0070000d280081c401d4200050851005000b90300020485030300c030054a848a180304503103001800c41c5c0c0100751103000c2c0198510210b51180302204d5200302c2d008070f030710040a0803883c0d80c8002d4102e600c00326003205011503942080c03102c0c01c0c094180810650769140c940005400d00170b155442c060040556801c4000308403050325040104580e10503000d840050b00c079119410101d000d400d441e40007070f01925180c2e1001c1007a5038007400034030743c807406040240080d4 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 172038696 1250 172037446 172037449
    0xd11040c1e050708030c0901020a0c0f080d030504080904050a02040f09090b06010309030c0b04020f1e040e01020f09010c0609021815090609010e0403090b0301061110060e1305010204030b010b0a0806 87
    0x5101c3c0078802011003008000080c0c00f06034007070140a0164040c41156201001c40c0e441129201168004075040e00c00c40000300301c56001040600f096004514062000e410150740d143e509004600b4480e1080341c075100065542c40690307050302c00405116102d03410705555440356030020030354002d007555080303c01800524194040d004035010075515030741e00c3d00c2e001c50715100c01ca41e0000142c81243e1003c8000880041ea07a81c2840c0741d814400c4480461207041c003104108003c45413541c1862007076900622000000101c084161a050802800d283c44082010300d0300f840100b0b03140368000e5020207114115031019000c10140c61080f501c02142d100d09000803410090031490460f000d90b40b041000c001480a00312030381e0299000b6206e8100f100420b502c50321044c0c03c2d50004d13009078001a40c00003442c0c2005d04200000d0503410300c0484100440c0c1e090000f91680d0500042940d050000c1c0c0841003002c1040c254121030013180c2000b001e0601d940c45501c2c4070300c5075010906030000502c603400483d525 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 172039946 1250 172038696 172038707
    0x5010809150c030910021305040e06040503042601020403030302040302010219020a0504090516080c0a12110603060105040801090b190203100501081005030f03040501080702030f090d11040c1e 84
    0x401c09201900e4040d50344400c0c00e00c0440c1d0004160310014059030324628000304041c0068480c0c40f20802443c038070981810300303000449080c0244200141e02107030500001c280044112000d807104019130100c0c0c08070303606400020984031041090740f9840007800000703042c0d25a0140c4140d9100743d003a070345080c56043c882282540d4810010754080000c0104104916256200c180308610880c1918521461022000c143c0c829030341c0900046c1d00513016240641c6002c40c46400648085000102810713642c1d2140384103203c64a03a25030054000002058550303020300c0175240281440300090007207400d01d00c5c0812801d4800e58020040581c3c549018a07054924029284505808029590000d00e0480111030702da00181004109188440003c203158400b0b00203034405524110046550f540f40500040c205500208041d045404c203221041d00300203224100c0c0d203240d1003103501812a22040c100020400e51010909900901d89411561080d41102480750081840500300036240b40d200010b461 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 172041196 1250 172039946 172039963
    0x27060103050709181518060e0a03110d080a0902010e060c031317060403030b06091206090f0c030d0806012606030709051302090c07060606020f010c0f080c0c010e07060905010809 78
    0x20301c040301c01107042401d45680301d400d80c11704002c0c0303c91b520101c0780c40c0c000840307003c030401c08956000740c0c031040180b50b0005c8405010b4440c3e90018204204200750003810f0b00c602a2188601a40340e10416080d03a100d840361300320402009000580c1d910513107115580c1e941c40f0207200710f424084040000795520a01454092a201440240080780c3c0ca95170110000d0840b4480309a106038140054000da480d1481d02c40c40c413440c4400104110704002d40c1d65403801d9603100211303613542d11290024149032804070b8400c40c010207074201480c0079128a40141c03001c224824107130f02c0b482c1080c080100d4000ba802c51460184000707405032020f031521801c1050075108100c6400d2070b0210198070440060614111701c0380d015501c11550350500480e035640f01c00f43d4000c0e90081e0300503404010401c11481c000e00c111003c1e0a441d040401454a60080140000c00000d10300c070040030300401e03410307400b90086d040903090000070310a403840b032900e5a001034040480c1e80a1030b800075803107200048203904001203900c0c = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 172042446 1250 172041196 172041203
    0x100302010f050d06030c0609030209100803040303200a061e0c0915090f060806131401050103110d050702060702010c03050105060906210411090702060f2706010305070918 75
    0xc054900072029561a44420301c0c10070004d80e5002c00002181018401d08041e111580d07034451710a2039401086034280000e4440c01c2c3d88100124108040d14001003168100c0b90b2605010003c000080130a924000c0880c1384038070302d4003941c80000100f11190b403083c001050369098200c80c518051501c013080b22060401c039004510138a109008040d98407218004071203880c907024900b2a141c0c03642c04102e403450303400000032661000a200b03203440d0403018140451b03401c95080001424051903003152a9041c4910b41c1030507991b0449030442c00001044416207600080140402c0c10310540003551500200c40c07101c019444c0012000c4040d00c03d024560403540004c20007414061050200002544154040007040080201004440d4140c2c070000b03201d00d00540c0503a0100300884184a8002030007807030003085400c90390400840d503403520f94040c0c1003506e6040c903200c070307010246003030180c0030081e030107070403144540400081001340014250080d114030b0701062225414858108255948421005 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 172043696 1250 172042446 172042457
    0x1a070b0c0901021e12071104061d0106051b0115170f150703021b06091501050306130602160b04060e0a1a2511010c05031e0c0702040c02031210030201 66
    0x1441354103401000002c00000c0c00080c1d501c124400e400d5652940c1c0501d074211070440303140068081c20314081c450040200400c282d4888120141d051801c2e8144050142c070007844000b05e090340c40e14900d000020b6078400f01000030007141c420702d180f4402000c1107100f089103000c3c901c2206000a540130a03582c0c0d144cc146070041c000d160341c030b10001c1c4202000503d41000c1681c24096031412a00040d44001c0720141c40780075140a040c00811142405942c0d4103020311145401c0040102d5140002c020b0340c02007d400201200d43c8e100d1501c900a4402c0d043e41115085001c0c44480502641212207401644191010802c5840c0c076500300d81c40d001d02075005051031203680c0740b014401c80741e0040250320400048403100404d41807004880000303469200c02000540c038803195030444a09200d4450091007d04189081d46031104440030406160b01c01080c400360302c040820a01407504050300c030390540c010030034480d11aa51800a540390008070788106070300110804035082c2500041000d050341d8040e07440 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 172044946 1250 172043696 172043713
    0x70302100c180326031311030a08031f0801052410020a080a020c150a0f030618090f060c180608090a02040e1f061a1c11041a070b0c090102 61
    0x41d07440340d880c0d02c211200c48100c4a01c81302010784000000710b101d2206030148907440b607294244140ca055085450138080d61007030340c290740800c8040c41501d50111000d280000d1071640304050500c0e205203940000401d40c2840140224800e1a50041d05002008110480c421004200b04004070720040466809608000c0407040810400340081121500030300403281546001d402007600000d0928a81002c1100410b40040b02a4020b0007000c0402c001e2034240072140c14010300000b61514205a20071003544c0c0c0078010b040010004d80e046a4030b40009041120580340311004c0c10701d5104029001070400341120202e1054000c5007954040d2120500811801c034a030f80c02e200c01402d0000c5254806e03c2074008180c1d903100c0512440132000f03078500e808100146055603039400d00303601144900050006114040390481100c07001500804840700c080b40820342d280460781503210b95080784030340d841e05600205908a070180204806880b4549012040d9655401034485001c1d0001c4140140c219445 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 172046196 1250 172044946 172044953
    0x70b1e0f030a1d070e0402040507030903020d05030a06030c0e060307051507031202190e1e010c0b150603010b040302130603030e0f060f1b010c050a050a05130b070302100c1803 77
    0x3c00d00684160a070460780e032030050302460551280e110514020f4220108021814280034a903001080345c00d0500c03111005980182d2518007600320501003207000b02c0000c00f005044d80201004542000c041c9200130344030425005d410b0000c03603100340070b03103d801000a1039013441c1d9208bc0d01c2e080d12130000b9007000c4072943c1c2121140d0089012684098081c004401001c0d0400754a000d0b25942c0c0e101c1449914207034091101c403254040b02d02210000719045000701346d13044090f10308a941e016000041c544d4500f824140713141e00d50b0441c2c0ea000980840089098a6182c0c000c000b40e9000721880e030014000304c0d210505594260000400280c140d4501801e84d04142c5141001003400501c041c1c1003c3c2d20118248040e046140d84140380324185194425000e028490b501080342589001c5c0d24144000601030994410300045604104000806614240c10300507c003014120061896135901c3c503c2c10001e507134020014000d9040d80c07400515402c864020214a8401d850f40070301500440d14540307 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 172047446 1250 172046196 172046201
    0x110307030c0b070611030c0a0e0907020304030f06021b0a0b0a02030c092130180d1a0106121a0f01050d020f07140601090b0a03140f070b1e0f030a 64
    0x100119405900c5000c1c8903031305c95500e8040d602c6801c41c81c180a450b01c0c80d0580003000203882c01e003610700450b604401c2c050190780c003000b21070940b0340260820694107040e280c000300a2040c0700100e80307001c08207106e05100390740119030128136034002d00380c50b074090302c40c050301c40300300d1100703840c0100544e00c1080441161305102d40c0e0006a60b200300c150381c0320038020442d49820140c403442034401e400442c0c003604030102e490b0b1409680d0016928802810b20381002c480d01802c883c4204080d102d421240c2e1848100b141d40110400d941d0541d1541403000e5945840150406202c44484002203041c10080c0070040b81c0001003030b0010303d00801d0070780070710f2600300151a1580104200b8403125020420400f001b102d602c002c0190510400e0790305014640c144415040c082d06030006002c0905012206c011355852502140640e500a24236020003c001d003121458448152110b03171950150040010784c0100401c09400790b801c0c040301d00040c004981c2d1f904403903845200d418032101042071010a034250702d07d9 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 172048696 1250 172047446 172047457
    0x31306020d02030324181801060b0f09041d01020706020306010306060806090105370801060609030b04020405060a1706010609080c090a0e010e070905010815010302030d080c0f0a03050103110307030c0b 88
    0x5003206d08506024066001d8841c0e045440c05d03040b1007801105a18610240b103800d005080042c41c5030304090f8401e944c000303640709441c000ca00c20b503254051201124014102d10408038208002155a54030320728046010b5041110804e02092500900160a90149400f00e10071503006181d2841c0345c2c280020010070b012140c1d000d240150684124464280c00752000032041d050007112500c4062a101180342920243c1e00040c04100d901e54041000805880819030042d80c1100c011038175135902c1000c1604140307190721400980710321f42490360800300040717102c40c1a100c0e155264103019440d60380156030340340d0091302190060740400028500c0311311340c0d01044003032050000101f0050001c43c080d034501070041d0005250165504010400d4540800500120080c00d940e4040c0661460b00020b468007085c0400c1428004a4000154524503001c22071300031400d40d141e21612480324103c001c1c001c1009010403a482c400100c44c6540c18500000c4000c02c580d44940d0703911016080514114058022 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 172049946 1250 172048696 172048699
    0x7030807180e0105210d26270c06091e0907050406020d020706050a0f120e1b03010b030703171201090b0915030d0315030203031306020d02030324 64
    0x2010885603100d60102101c070000c01098000c060194180020014610720140240c400c10b40c400600000052021034629070341100c500b400400150202d501044201c800c0288014003c041c2041000c42903410100b15072248601202602c0c0c500d4007940d807a5502d81c0d403202150b01c02803d000421203440d011025007814140586814804001003020481460042d1225400b04801240c103016a41d410454003202007070034401005000d15040019042d44185801c0c903003009640c504903c00c01d4014003115403490314000040251400004a06031688010782c264030070f0129407500b00341c4a103414001c00140c01c90040c0a05022071559803003080c0c050341e0708481c000c0000b05000d540d11224052107401d008164900000c1001800307042006408800141440390340040c1003403070700c0c140c0c80008100c41c0904040c140000c40c09100030b0300911602c00c940c8025454880010003800c507082c11a5048101c030b8194080b55119164102c0998880c0070403500c22104d24081c20b201e0107004035038505400300701e10 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 172051196 1250 172049946 172049957
    0x203030123120a05160509040609030e1905031b06120403110609061008150c0310030204060f05010e011b060902060c16050316030b240904030201060509060d020607030807 75
    0x108401145807803002003108181c0d03410402c40c01060080c00c0c4070030700307024810b03c0726182c2d220300f0700c6d0000d032286c140070b0000740119036218140c0c41010301401c12000f1240d001041c0d03443d82d07100404015003d003000c4c0a124046e02a01d2649061005050503484004c040205010b0601014083d68903510400078800d03000c205a10300303090044841400300d540120400c0300908202d1401259000510890754001d054540c003054000c0062103410062981100000c0ea02c980e50b074541c40301c03544198071507800180d4410b1501c0800200405409040c600300d4000785c9a01c1c0f01c2054400040d14525a00d0324109e410b2503180c4400c0002039410b0b4068604280300805060421412a421514080103820151007800544600b0700081c80d041000103c00c22100800c0c00c0003a0869071000c05a26001c0d01e0072403011080c6d041c041e061800c40000c954014030150580105103000d0600034041c04841c030a00b80075040d0302d80070901c50704090b141051303011380140c5850324004c03503560304446100b8010104810000c = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 172052446 1250 172051196 172051259
    0x90c0203040902072405010906060503011202010f03200d050a0902130504020a031a180313061b06090b011e0e2403030409020912061005121002030a0203160c020102030301 75
    0x5d080000220300c0055040000503690b040903c1e1034104c80c0190407070740c21302c02d05000401458032609030511600340d0a01e05402100254041070380074007040d52215424800006641081c06040000351010a40c0e00009010715110700c04004200c03415418041d4000411a03c4803542c64000e800841c0c21520140104000580c7c81d100d8a402800102c1030007984040d440901040690300c0f0b82c4440090b80400182d441d05900c601d02030b4142d14944900030500140f00018001407a840c00644030494204c84140400c089500e08070380311810900880030141c461340e126440130450b40c407001055800c000348543d41c9860f602c103800d80f52400c140700c0e4629002440000704541d201070001e800200092040980c0321078040080203c0d108100e10704c1801503010408000b607032001400d80d801103440a903101c280c2e50403030399043e0381081d94492200708040d00000a202a5015950003944183c044000400c24242c0f851401c80304915a580081d0041e401400140000103468045100708a250303e900034801 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 172053696 1250 172052446 172052483
    0x60711041b0e0a1410140705060f0106020a0b01030b1906060306080c060306030c01111603030804170c070603271b0519030f14010e0a0c090c020304090207 68
    0x50301e0000c841900074030348500500032590000300c5080084001c88400300900e0624030041031240d41c00210502c20110444080b0103103024145155298901c2c101c003039540e404505000b552007405a58282112066500020b06030f88040317215107925034001000d1034164030750344601c0300059004d0000078031491055904520f070440fa20590004204a444c0403078014648850030707041c0300007040650f001d0001001002840c1e030f0b0115100300c02410134200303640c1e03403414130340c007186001c000b0b0b2105220f81003501e00100902d500082100d210714490200c620f5496000d02560041d03028503c1c010361203600640007844558065041b10007042e4202600505040c40d00d881c509031098540303002d0380c2e00c2c07920840704105613034580c2d225806460140c1d01c03222080d0f40800301080140e5941310281050080e45000781c04c02c46051440305400c071010b40284420b50190041725200c01c0304400c100d412541c103400003d640c40d80c5005e201b11407240b68020710304080c07620034810080d50000c541221403581e442000c2c0c003407 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 172054946 1250 172053696 172053701
    0xc0901051e0d09050c03070305031c090212030705010b06070807110f0406030c15140f0919140f030607090e0910020406090609050604050a0314150c0a031a0f06071104 73
    0x8070030002e000c61484110304040e802d000e81025641d0081c1c220340402e00c04140000b04850f42505c02064088c110018044440005c10501600940c00310301d0004030a509507001000c1c200070350240c8001c00082c00980104031a601c03031003400030f104031020b100789070100702c0f51003515006401c06040507203245502c03400a011249641c000b00c541d00e006900030302007400c0602d80d050741300c2451708020101d9219440d124601d80500003011091450000f2205515100e00070710303031542c1803c5078038400c01c251a28203184400f24100560b034001e0f07174800e00c4104140b030002816405604507884d103001e840e00304401003000c0c010050040041c4e11a0243c250008001840200000c0105980b243c3c50f480c189480144044038581c40180701d1201484207011542d503049409048940c009008800300c00c884840303e04081000b403c83c14150386000c200807094403444000d011100309035908002a01c03d9508201c000c0c8144001d282e040300c40d1854055150604200800041d0700819090580101e51030000e803e = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 172056196 1250 172054946 172054957
    0x911060307030f05181203010b03010e0c07051b04150302090115031803081602010203100e073b0603010308040512030d060602070303030e0d0c110d06060902030f0c030c0901051e 78
    0x121900c0c0ca03159101c170160f0502c0705450070740841e502c03a4519407504490303024600045c00f030400080600808550003440b90b108840100340d205040d1800400d20481c0300221406603410345004905029800c500e00200c103a12074140c82c1d008194074882d03401c0044160381050740c0d0f20000149641c5d99021418003018003180d0b00350b20312941e01c2d1030162900380c0c1c00c400f4148001d030100d0156030043c0107000c2080d2005580c801031b1074541d04422103640c0d41078011204040d02c1122101c1c131041100d00c003107035000e2984150360115660394114030b107210305c0403d0120500c424880170f084024180028886440e1602152650400060880742410241d81d01481211400d40c400805030780644420410035030036024400d204564400034064020105602030f000546402d401410300039810845580d5a075901680011580c02c00020800d950300c0d086104001d40c81510240c00c401c0d51900091491a004003c5038455100001303028203003840c1c10010342e03d9820820001c0c40c150155041f141110710300d40701914 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 172057446 1250 172056196 172056211
    0x4021807090506040308071707030807081b0a080f01050a031502220906030302010b0901060804030807021e010f0e06090a060509030706020f031602010b010504050918010509030403150911060307030f05 88
    0x982d691384510308a40e1160304010070300c00200701030002704003094008036519404807003030400c02e030340755102038031039078480300800c40c4181d0303024045040f0013000e5200524503c180507031244980315988030000c00c0300c40c0f03c80744002040c0703000c0444003103010020750700540328503000c16040c241c100c002c12a50020001c1b80741c0050840c0b0303a403400c04200345582401554a61942521090142e504250004148120060010b0140031a010106a01610030441d4880d01034501d0310356400c4151a10400c0d01900039001c440f00e21b82d0400c40e00c200041004506180551a0100180703a041c800f551841c01a02c0700608451139404144100004201140010b0000703001d9a0185d50343c80ca4070404d01407aa014541c412000c582c0741c403040a030140d82200483d81600c03c103c6601c5c0080d0355804003404003d100c8071070408954209028000c0701500080500107072441014452903c81d0b08038591011600b50400c0500000780e00c03614a07105081040045800021500d0301007108244880c46e1815034005a0b208e8 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 172058696 1250 172057446 172057463
    0x3100b0a09141605030103020f10020c0405011203090e150915030105070905041404020918010e0f0c180601091802070b150a0905040210030b03150a06030b010e040218070905060403 79
    0x40f85042c0c1501800648500d4140b01d401c650440d000b14002c04596040180100f100003959a101030080041d9a05880010006c0c0300c4d6603141e416801501100c428120041490018041803201e218200b0f184200c01019010b200301c802c690400280346006071107109058006160410151801e0156601c91030164035001181c03440e04060004880030070030104d044101c610280310050761040e0242c0c2e080000602282c3c0c10580380550103005140c900b00c007189034850310098006029021422010308101101c0c0525200304200c0d214117a440101c50345030000300085c5007400b08402c000001d000b101d844980050401c1c400360b944202200341610700351418070091120700c406203082484d62000d02a109401e011509141d400301e6007000d02c04000d40241501c60300e8400176520f080120001d0240c100040c1151410000c0240d4000e10b110300055401306494400411950044003000f03001d140d014099800b030380401107a1945040c80500101c08006d951800001c59a5641020b04003660041508 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 172059946 1250 172058696 172058701
    0x10203060108060118141203070f0506070c12050307050f0c06061908030313020411070f020306130b0a0903031b0207050a08060712110d020304050a2003100b0a0914 72
    0xb400e1900c006210504106904451240541c01c80881c10308a611210a50070880c0d100c800140780c01648a41e9040d00c2d20001c603589091099480700e610000b03000d1400c0d40c40d0743d10350150440303540c041020080e10a200801c00c54540034400c200440d81302c0d50383e1912a0912641454840003580840d00d841c6043d0300802c1404210700e800c2c0b8880c0b50600c04030320002c8545141000c515200d000050041c4c400769041e00000085d0344685e000720040c0005580016910134003840c00b210071070031030b102c182d019101c0c800014000c540400d61000038103811411850041ea60a2000c001912008604808140e100c100c9444103034007035503c4a001280b1500940000d50a010521009018a0344940304a5004800307009030290014107444480700011300201e00a6000c158003c1d85106505040c500d140c40082080144070010640380300d43c620903240641003403055164052001d001981c0a545904880b0414800800c10780c040d2041e164061301c40e000450756010007500700c50344100c00784841041c080c00c = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 172061196 1250 172059946 172059949
    0xf040f08041433030a060506031314060f16030b1005280801030210020a08070804170105010602030a0c03020c0d0b0108060703020a020709090f2406050609030a060b0a080a0501020306 80
    0xc044100c01e010f4600111400c100c00003d0407440c2d003c0049002580c000404079200a44540019002d000f010300199034a0500c0b080000c035100394110159042001c002400708403d00c0451580d02402c07098102c0751309511003200184070310000078500400d1540d11515107440c0d40381e001c01682890701e240c8074a6140c28945d42480d02c01c400c036840c0d109500c100a0210a82c1e56080035109054a805030f0b00c503141c2c00701040e0260300e000445500a0b0906801107101410032401000410580da061500000003001c01603e81e030a0310300030301940c00542c00c140489581c05128400076010103000c0c0c0f045421a5140201040e88204144020341d40104a540140401601005200d030004ca09240451078000c07200300003900c0d1b0a050040300c08031500d4500354014404144070802441d50018040413440490055481469003020100518203081c06000a0a890000251010808003074003408450496075503a800806022100d0340d84101c4403540411070f40001c1202005080c0308800040c0d980c1000d90 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 172062446 1250 172061196 172061209
    0xc030e0604081809010302091b2205040605030a050c040f0f06080303040b0f0403090e18030c010c020d0e1302070201090315152711041805011404090503030f040f080414 74
    0x10380f550b0152545200400045c0c07901ca02e12580724180385080c89842501080032081442401c00951000c0c030103a60038540340380c1e1400342004403101214200081d0baa2041450f86407259501e014043e0b800c90903204005003003d41018a4002609200252485a104030300c4122400d98024003469032011040008004c40c000b401900551b040c0d10400c86460695001010240303a4041c2680e00c401c030b80c000c6092000b00407040806440100309403500c60a0100c0028000d000c0301c5141001441404491b0182902580f418481d000b0301a20403030a100c000c1c50503401071350180000700d0420401c0325000011603000326943e0703007200c0ca525020030901c15003580c480182403590020a062081d201e4100c0c07201441800d403941c1080d40030740100300c428000100c00c84174040d66002101c07847c01d1100e00842c000e19544528180c0e01d031156046e0820481034103120071500d000800410f04d90042010610303100480c084541e10911800c03049400b0a12541c80e05079a800580c0051520002d0300050f112526140 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 172063696 1250 172062446 172062487
    0x18021b010902060f0c072313150b07050f1203010e0c0a080402040c0309050313080f0d0c0308150a0b120a1505150721110a0b07030c030e060408 63
    0x2000340a41040307078001070301900c02ca8552003107080c1d00003031003404040c00f4465800103041880401c1100c05030001c18418041c54040802c1c070881110788807681c0c8c03843d540318446410444c3d200303207007450303041c0440f10156a00c40c0c1800da03640c1c800ca20300c50142c00420030011070710280300003586807070794900a07555483c103502420452082c50300744400003116070300000841d4002e404403000304185460a8059000707058004018002c0d0100003030b10f6400740e0300192202c0403141c4000c100e502c458010401d194441036000040b5000032269106040800c0c49185241d421010941d51203c00162010000b05c0400703a55000340720940e0b001c5808400480da004841d5803090700c040c0188000d150001821248483e03a0081c64890451002001500403203181915112580075840545000440e00c05071900707000d1507003007000110150498400c0712004500a00200c0e4013425440194035084001c0c0d018041500c0140101517a0f6401e10314441c0003001340070300071030040f5140707580e685003160158400d1442 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 172064946 1250 172063696 172063747
    0x30203150402012109020a0314070f0b040e07090b03101d07090302040e0a08030c040306060b0703121d0102070b0402010206070306030b0604050c130905150a06080a050606041802 78
    0x80c000c100150760002070407800c0c21500c43c124607566003030068034402482905400385d080030352000003004200340300d000d9a404a002c0012540c469589003003180c40c00c0401d010b400306030002840100018003952100301c0d00044a8201260b5241e11440c0d61006600100c030280403c02100c0410444d04c0d60110800a03489188a03044400e4603028101519011480c030009016030340c0c400355402c0380e20342804183d1748140d00219095990412048000079600b0600040d80d10918100c00041e4008210003116100c50340743d1030b8507038030155040c511002001c4003401c1012b0001403000d94400d028081c40103042c1c6511031205200b5078100341c000280350a1004020340c0c203040c036080c0c0a0000c1600c160050ba8040c0c0212004520f5590b011111003050194070702d103011600c3c1704600468152125001103100310600519414560703040301c10062140308520030040407aa02602003a071403003030360b00240c2d440034000d001c2d10f20300390360340003003644088800440f00140d6134003107104240344c12203113883c4092921 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 172066196 1250 172064946 172064983
    0x6030f02090916020c0612040212030307120c02010915020a0306080609030711032401030b0702150402090912030c04050a0801020708121e15043c020708040f030203 72
    0x10450104042c034a01420100c84110222003010b4040c0c82000000300e00c4902402c100e0310b4000101030041d99510a441c100d1284017201d09646000d28000300f0350b8454a074031b6540c240c420000020401c010b00c20000c007101103542321803100e80410748848640c1c400c000c081c400182d0f01c040c0703d10000d044075802d406c00c0342e240d0014001e200346103200100b03a40703c65810003180c260034285600000d02c1c0c41009014a0245008284a0340290b41c800d403029040b01d010346041d030a20b03595034030300701c0c0c407030300441c020400d081d1241000c18058101607011603400303202c25040307500c110340010040c2c90a801c1242e8201107000002410b01680c240f03c0c0c0c06030f00a00c500d4000750f050044d9640c41e070510380140c626a07000c142128000031340d42d0320020240280000711192031812030800611041d5200c103190303121030080703013408400014410700e001c05014000a04944c034035908040307100a17415106080001c49016024043c44010508603000bc000510005001d40741c02803851041c141411082c000541c007000 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 172067446 1250 172066196 172066207
    0x80c0703050a1a0f101a09090c0a1103070206030103080307261e04020d08090a0b04080a0209070c05060604020d0b090a0b01020f150105210102070303200a020a0209130506040c06030f02 81
    0x30114141d04046d141451200568544140340c0d1100d00d01841c401c40b40d00c4038041e4203000c03165940300700500030800966120800328161510203a52071040d050002d402403006c1004001041c0c00e00d0141d03810030010714000244503000c064000c2c50000095000d131140541b10300b03001d0080010206501c0b801c2c805a0140b004d0f20f00b5070000780340904990005000c20000041c80c0300e1590341d00804401500c40244003c5e2240e4030f030101699500400c41c0c00328001c200c0440404e4185016140d6141c820340c0c00001441e15541c0c14045c00041c0d08003183d0841c109850300306200c00ca5854100d11441003860b070341d0014035080f240c0002031070100c0c0780c0c00b91011500400100f09054000c41c1d030b003506450b0300345d4004082d503000411052602949090a01a5502c04102942099816084841515183c000d85022004640d001042c2ca00c201c05841000d40e103c039220301c0050802d8003080d41d12150114490300701108540381d290504000701c5045030009040e04044c8142a0540306080c1607000c078190460902 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 172068696 1250 172067446 172067461
    0x1150906060905060f16050a03110d0305190e0705270604290604091a0306010b09010c0f15020703021f090c0b1b1c02120c0307080c0703050a1a0f 64
    0x41c0b1071205024440c5000095400c541b00b9051707031150429a000003103400d1816182001040b64448484804550154030400e14040d0700c640a040c1c090600c0450285c41c19a8400d01d06000f440b400482403124081d08400103181d584040714420080c414542301e4840404080f60800000e10090120348a185041e0030003060b41d800d50901068901c81130a40c00e80e00c004680064028025035100f4038140e410300b4403a900103245c111003101c40300f800364111013441e40c0310501c151032030246c0721106000499868a00c4086001d49207202c91160041401c00000032400e05800281e034072000b4181c015070b0007802010034003440030108203600192581c04001c0c0b07040681e6030000c000e00c1803141d4003d08402040192001ea102c1d4049848042c0700d404894040903229880d11400c40c4034009030015026650b00c41c0c0c000c1c400790040300c6800008802031498031b0181c2e518031803d60031071420000d081c81280804030026004111261065000d28240c00010701e500328804a0030000422056803142080240843d5 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 172069946 1250 172068696 172068709
    0x803070305031f031e050114042f1c03120e0a030c020112060f14041406061c060801051519060e0102010209031e010509030c0c040b04020c01150906060905 68
    0xf420f4014440700a801000008200c0d42d034139000948510740d10950424841c216484103802544980c0c0203005112065502d030520240c100d034040d14001d2140c5510f0321200200c46925120301da02c650b5080010780c86404612042c50401e601900d03c1261030224041c580c000c1011500303003511110901441849054154541c008010010b0520000d0300c100380447e801583d030510385555809041292550b07543d2071000e0781c2c0e80d03840b40062490890710440101d0805009184109458080020036034807000103000342d076400010701c0700421410002e52081c0700e84500444004040140c00410141010803174803403031420404c1c3c2c4074414140548898854422440f01804981140c205503820b8802600140c1c0a446840001e80c3c0c18007480d0460f40c0d41d800740c03d60491085070700d84020000c0c1d68540c929180c2c0da10554160940c203500c541041c00240c0781c20b40210b214408041d00140c18041c5004540742581c0054262559044800800744034801c42881008000c240901d441c858451401c2c010542 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 172071196 1250 172069946 172069951
    0xc08010b150703050a0c02040e010504060e240603030702060309100501050105041508061c030c11030d080f090307080c0c030c06030c0901030207060e06090d020d0801030803010608090c1201090b01080307030503 92
    0x130f000011130881001c0307002d000542e413411303000780080c03294006003c8114003d190468089804515120350b03c021005c0000302241703608407040c0d41c0c448142120640300841d10004022643c94070042007241700680301d1310301550241112600600c1c046042020340b909641d0141c1165041060078081048510461241200556840d0401c050f00303403a090082440c102c4041d007621040003251601c5c104040d40303c1d81102c00340340545000360410800038101a102c242d10840100002c43c0e650208250340d00d001c1c0b032076801c20311500460b450310726a80d64400c600d412080704980b040c1c00441e0a090303031382010b000b40d42c040790302118075074a145400300e8001c04034010143c80c58105540801ca0310100b1001e80e0203420303428052002c407502403070821001684c602e0001400c0006010303038400071802c0d41c0902000741c140e0f6071000381c190641c0e0030441c0840714041c00815000151245079960807660b151003240c040580b894400102e0030270b1403402c2281807490103a03c28000c0350b004000c4040070075407001c2602d4 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 172072446 1250 172071196 172071203
    0x909071509031202160e0a0905011803030605040b1035041406040305040b0d02040909081b061005010804081204080d06060809061803071502030f090142030c08010b1507 74
    0x201c40d00d07800b42c2e05000b420b823010002e00c00d40c070700705030003104078040c1e500d0a58051080d83d0a2000503110402e000503104081d1606030003007084210100ba00e80036070608110301039070200200390072101003000c910030440401ca00c0c00401c2d440050101780540320b14200000407080004204a0420342c0d0000c0051165120f0318060500100346c03051a01010380446c0d00070000804180315080721802d02c483c07a03038410008a054000c51204503000c0900204d00c2d1441011014042c004142c40c140040d0b42d50302c0300801c01c0303a16100070056882120b48003c803090295004102b00d64803080f000814101b1203001e07810000520032010204000a0f4000070403d030711912041e040c0c0007042142040c18514058481d004044521208120008c00c401d54051031207010302203094910ba0300d40403409401c890321903207400d07074038440b004401c900c1890800c00e0700000300c10506281004203d052140721300003280d030401c642c0d29010400c10070440d582401100240320040340c013402d051688180c05a124800d604008 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 172073696 1250 172072446 172072469
    0x30601050907140301170d0c030519030b0904060b01030c170105060c21090307050604120b10050607060f0b010f09030f050102090913031403060a05090907150903120216 74
    0x500c000340301d00d002c0d9500400350103c00e0b8481d61034140c07035419541e6440d0a10b11078460000800741031441940518441501038480505d03205641040d8031812031252140802d054440c1e03041c50f0242c446802c6544500e014000000b10f42041d100014159050441c10000700200310740044000c5c180001c206d030450700201c44042e90340b80c070307545c0306814a0561041310891040300720710b0810f41c1c40301c200240405c0c0300850982d0841a1502c0c20455540554010070510b11802c41c040c00c00039240b543c0598120440034200140c980d5204001615030f4040c04080b1074141d2105190740d845c510501403564000e0003400c2c203404a840a81005040040510014100a440701017003000d2090031345c100ea0071180c0103411850580f5190010010305254641c1c110700103191040110b90400414051764058200100f1000c21586414100314016002910b1141c00340a106000921303801c52003904482c20003252243c1c1561303031640c01c0000c80424040c0081081d0341201c1103502c10307600c0a41e0f105054500c510503a = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 172074946 1250 172073696 172073701
    0x913050c04060c140327030102040f060807021e0c040506030601030803040308041505070c15060b09150408012c0a030807081509040503040911041508040302031e03010f080c0306010509 81
    0x9051303089441442c040c0d96010001c1c07040c040c1084003811028050004586206140160090600300d103d00d100360300101907034000900009104030f4105811040354811241e071400c0040302907855406812413000e0a51024040c4169410940513490b402003045010741380075031468803100d450703210041c00202046581c000140030000c5680c8401c4041c081d044040245240c0041d020b081c030841514280c4000d011100c00b0386088025004100a03620b480f03400d076040c80100b8050280c0d000340e01a4080a41c58140b20100300c60000744905440c140584c20b40c41038205013101c06100109030300014131810303082207021002080c1c1000348030b60007030650310f0004502c2d901e030740322042405c040d0ba03a43e9511003508418841480070002c0900182c03001c16004203c0c1c0007221208160b03a00c01e500c40e0840c00741d03003101080100c1b401240c0c0300384d100740030b4015070b07240c0051035418041850080341c90307480c44440440148000303081002c0080240001d0401030102006050020781d80d860140b0500f4420b0358030100 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 172076196 1250 172074946 172074953
    0x9051e0a0306050c0304030e04200a0201020d0e01020d0606020d08190b030604120905030a05120705070825140f041508010f06050f0d0b390913050c04060c 68
    0xc40d80001c5801c03500400840c02c1c0302e02d0803500d96000361000ea000987c0040c511070149018410800542103101d43c0e074203480040290005950455070180007907542c00c0c00701d0b99000016026451103c2c42040006a032180204041d500300da10540102c0110340c0700c090401c09a5800c41000d5130040b055a621803419134072080f041c030203001e0005060750980035920034001005049003580c035098010b03498015105032920141551034406c408040d0569200b000c0032081c05003900020511580030b80305640b019074030741d80a01c1c40d00c51240d048915032b41440100e82c580d000000d0bc0c0c80302620310f51501180e00d40501c000030b401000c4c100c0c801031050b556000c64002100c010482c0d900108901e50082c8103e486100d0003000030a0180706450064070024405a0301d4900aa442500c890f8445602d803c5601c0e820503400c860510807400c9500c91568031b1188075096000801c049501420702e000ca0759400c0f61070300740a0f01c8020f4855243d000b900307202c2130040c000091402d83e82070300d00624004c86800700c0e505 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 172077446 1250 172076196 172076209
    0x10080714071b081f0509072606090a0b1012110a030219090b0a0b12040507050a0e01091b0e060c030f0c0105070f020c0306060d0f12090602070609051e 66
    0x400301c04500b040300b000000c0c10003000c1000900790f0150402c00308008030b880040d01c161042100d0401c8982c0000b10284540c510b0301c1012031001c155142c00210b205041c190103481d04400f0b03140c0c07148580c060160f0508200c58810303d181d00c841064501208646400014040d0701c011141c010404c2d80c600c60417000f252600b031105401150001c2820410140041d600e00d02021103003e0000c0c403509100003c04503042114000f4100c600c06803403149050b421038212508140013a2044540b03004201d0b0001e4143c2e58800c0c1c0801134003404000ba43e455241044040c00c440980c107070341c100b4840d11401841201d40040c1500244907003511030b00d48c1c80e0302059105045100307540e400b041007903001c1030800210030158440c81c45210192980644141658002d0742e0b41e4840d4241e0a03810380c0400b0001d045070034071120f85117a0b540305e26541c950b001ea1070350b01c0d00c081c0804411020002282c500f010090558100b00d903400504071424000e01031400c000c04039001c60300d0307042c05003208485c00c0d9110340346490302e1 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 172078696 1250 172077446 172077473
    0x715050c1002090411040b0403020405090f0706080f0f0f040624080a0209070206010b16020d021c060605011b060e1c08060f09061e190e01051008071407 67
    0x400c1a81c440c0011a4081c40082d08640c0d6542e0113540b4000c0180c2c1440b0041d42150300b0340741d0000708582060f03e15030070840500b100802c1003040c2c2c0141c50b00100b03540340c1008588060401d544810384a450400355001e001100281507401c401440c10501c00091500200305801a40006010074400d05400d10401002104060700781004241100011081404200001494401c48400c14140c0742c107403080b40c1d00d0703800b030160305150402007007100010300004801a03400782c0b0180058080807042c3d00081c10744100001d01d15440213070403000800304101e40c45417201030402424101b00041074100600e60070f59100320018041c59440d07003d0780c4074078405c100524882030044441d41c0c0d6044540310027040210161805030003a01c00500048083c50213045580c400d9074043e001c8011581c03c4075007041018019049560048407240d020703885007803100d15400c00350001c264005840e502d084140030705410078401c007404015401060040d2030340e00040c1500a002c08171a801d40320f0503203080c2009000c400 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 172079946 1250 172078696 172078717
    0x3061a1804060e0a0e25080d02030a1b05010603020409110306010e3d0b0a0305090105010b0a2f0109020906060c03030f100b03040308160f120207060f060f080d050a02071505 76
    0x3104100c800c03661b1a0380c600e4192070714a0107032208003030344501c166a80c1c010f514225000c610002085d005032122a4101c2c0d5989010b20004150303550759801003000c8a5089005581d00800d0302d69030461828100900b50040030722041c140c560b49401440701070146c0412660302c4996800ca8261503c180d00031000291500403000f05505556540000103800d5104202240c04217003002d0019000c00d4040c0b00c1c140c1224000304d4000d10744125200211050840e20f04480300303c86000c0540008607211402848010074a040001440900c6004106111b040203001e24030035031040004071145040807041e240c2068035242000c0c407680b10560b0803c800c040b00e4100d2401c0f90000b10030403007810341c80b0840501403800c07140c842800c118a580c003114007181c4100000041400843c50300e1410301564000e00103540a0400041c440c07107109401d1060798165400b00c0500244c20704248510901803082c0c0c4412038035802c046207006405600a9102c0c61540714140842503a03114030a20540990211480c4d21035 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 172081196 1250 172079946 172079983
    0x60c070603020306030706090303091511010e010c020f0105060a0b070510020a0c1208060d1e140c0102070b130501031d190c0b04030302100c03061a1804060e0a0e 71
    0x4603414010003e40084680c5882881000ca0000d40f00780942071020581707425941d0607044a04190440b03a0700301000300741004020240c00035082e03c200a204107402da42505001149240700c08a0081c50400c02440d428010b074506024092240e480503201d400701c50545070410745504403070414a041200702c028000d00d880c0006240500d90b0790001c600011684218404880750b901c403d000c03038454104a845036004401785401c11b000c1100c82030301158444100003000c000149598a015072052003a84404045d03011500440140d0703014460003005d092400b40041c18182c0607161158504c00900c1038a0505607140a1000c0c004950280c8620740c400328021034140c071030075900c408012607074010262602d002015001c54030081d048119802c070303600755000740340c40e40c500030580000306021000003080c1640d8400c0003a8081e0501c50002a4200c500c07103243d100c03e4001c0c00b52061140401416200d585001c1c0c05001c0321228014041c0c0010545130000b460f500d4040f8114504060098818004407 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 172082446 1250 172081196 172081199
    0x1207060507020306011203120b0f0a06170f0c0409090213020f070b0c1602040e071a0301090b03030702060706051512010b2706220f09021f02060c0702060c07 69
    0x80d001001850141c0c4280c04032400703070303980d44210650310b80c40300c800078000740025805c01d15120701034014a40506004107020011448100002c40455083c1c0c4400f01050810324007000d020141900c0940c001ea200c180c82c44c00b858a01140703019440f95000b0100c1c080c2e583c4001005640390090b40201c1c810785154215035407204c2a120441c40d41084008480c101e0010300080d806034084015517011044031035820100c0d001580c20000030342400004603440f40304000f130020f8019050545116040342d9560403d40d00d5040061280a8403000104c02d0b00991040146a0050b01e500007281c42c103540140d40080c05495aa000d030754540b8425200c203034864020608400c15513010b42c80308111100071103110340c0e81080d0780202200b401c80c0d00c061005004c1c1003030008440341490010544015180008405007143ca1901e80048038043c50001804558664200d802c50401c1034040d1440803002404a042400c0c1c2d1100940d21f8034004c01d40e901055001c61040115142c90098441c040c00110513030301d885 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 172083696 1250 172082446 172082459
    0x10507050f03130509060a0b0412050f010f14090307030818100c0203190305090a0303020f07060501030f03140c0601170c0612071b0506010e060111150907150c020d021207 75
    0x1000f89008640c0300d0205a00070840500e0045141003c6907004e012017070810307181000115504d42a4441660306000340400850050828400e400001c0340c0060000b4940389104e1a82030780c4440200106041d600810104022a811130511648900603122400840712252000b41c1401d0411601041241c10400c150420680100160481d0082d40c0808545448290b80031419500140c40b8640c1d260009030003180480d1194004241c52070321900c03124070741021943c8220869009900680d45401500a43e00415a00000030403000f4035541006041001c02c3c4800e0392104010702c1400811102c1000c010608001841f0040d0385220040460351207001c20903441c0d1522104603102070009507580c9000c0145600b4071660010b41750000001c05a6a0801d2005003030070002820942c14482c13048030400540c001004204030001c2e1011048980c0e0801004240c5400c00c6504001ca0b550080200309501c60343c858015020541c0407074084c518140309001040304040030340c08000c4580034440300450203 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 172084946 1250 172083696 172083727
    0x70b0405060603070302060f0f0f0304080c06280c0207080a0302030405282313020a030c03020c0c090a110406091d040305030105090907170c09010806010302030a02010507050f03 78
    0x22030040c400d45445503921000c2545480070303070100940c8088144040c40c00515440f001d0050f004503c80c0840c60034a000342c10407900d070000c4400711071008001030841181e810030b0142603048000880c17550004142004110a0180700c2505103440035a10001c42007000c1c400c00c0554010300d9800b09a510440071400c00a459a001f07000c3d890282100510006003d03044079440544080b204010140c0142460030040d0064900307c1850710720a0300920030035117980c802c01c94a0800d0655240160ba409510001409540105e08100e00f0b151051020801895010403050000e0b281181e40c84080d0780c614070544e000704014201900e803d035000ca000305040703400c440740e8000c6d500c02c040c00e041b82d002e071244401d902e0786040310f00900040d0284010401802c100f000341c4e41012106c01907a41d202c4d10380c1c9003000e46c081c88200841207980a1a01c0c5038042c10b10119190241c04c2090190040350705680200c2c1e6500b1141500078108540040c4010601c030081c007000107035540510946e1364590907001329100 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 172086196 1250 172084946 172084951
    0x7030c020105060609060a11210703180f05060705120a090608101508070c02100203040f080601030506061504090c020706080a18080c01020d14090c0a080a08030a060803070b 76
    0xd586010045021880c100041c0c5083c000000c0c10306180416001041300c1701d441c2c24160f00c5181c821030f44114420741c00140c4034005040114006900e4440ca428010801194040d00344010381d000f03803041c4404079415104400352602550040d90b9200c4a1070801c0c03504040f181d0312102040040b80c90742c040c80c0c1c061500401c481c615501c0001a48a9624000718002d81b8810700144130501c44034002a58003039840240e005900f42851044075400c2c1e000710340b148826080c81320051b0400101440740058240e0258080c1099000a000a41c116a5174030750315403020309880c0c80341881c40d03070203400c061781201110050408440c0c1403044142090000e99605401c0c011280451401c8001034200c1c0041c1c4a1001080b401101c02041000181c50741d60071613101048844e1555002c2103c003103035080c240100b0541803d940154055464030000980c20805600600ea1007018008070411122200081801c0101e8000c0c001e1662601c1d502d40741c0c002440140d001c03800d62b00001c1000c1c0123018900001c41d2 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 172087446 1250 172086196 172086221
    0x8030603060609090d0e061b010b040c030c05031902041d16030b0907320403020307090e070e100e0a0c170c07060213050a03050703030e0906060d15030602030703 71
    0x2801e9031070300820800e0f051412603c80189901c11543c103e17195100b20303090100d40c0c8018200d1071418209402001d100da6114000c0c640706e039110082e42000341464890381c840180980b60030072910ba28910001d03e903200103062503e1808403101852500c0c2000d174115001400c84e01c0301c81c4032641ea1b9080305018540704603901c001e044c13404100298046c1c024040c0802641000301408890b030b551a006903a0803c0e5278038003c1550200c81c01e440300650080100700c029098610f81c05403550700d07501c10035282008a81003030061500b4041410509100019400f094032030361410740710076684214940164030f0b4154002001890304006121a05065038010b1020000f95075580464010102c0a40e6840780141c034901c024010030001d407004100b482d4003818074110001e8120050301c1e9144005255116140c10588031601304d48010010141c00450036500345005071030320902445d0090000f6458040e01507545c0c030300707602d6503c0756185c0103980300d1810155a1080e0115124181464018000c2c5102c64034207 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 172088696 1250 172087446 172087453
    0x3050a0b18040c0609050603070f110304330f08130204050f1e0105010e0d020307030b0906060a090507020a0f0203010f11030610020712230304060c120302030402012a02040908030603 80
    0x1080c061700ca81c2e81601540e4010f040207244d6141c1500c222204020891030808001c2c2080041108580c1031000348002c1548801c07400139400c049003506c8000e1030a06502d0300c20f10012a0500216421001c0b443c82d801c4030b0300700103550b6507030f0017800c0300450321025001f90320618007030400c0000d901004016015071500025600200d0140d0800210541c082c0110f40c0425102800701c10545420007070b0001c00d61000d0142e4041e00d641c1c0d0b035601030340002502c0204413500000c0412045060502e041302c024400401c00740814104031101940350b102e0220040c101007100362041066440940201e171300f10203048010448014414001c403181c0d0016181903114201c050440d50180b40b00181c0c980540301150070494040225507640703000440040840c5180341280181685100000c0c00034000400c2551100d10101d84a407410340281004041c005003410710620621000d030740d00403400f0582c42c4c4100f0022000581222001d01983c05141d00291b00ca82001703041c6041202440c040d50040307506400300c = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 172089946 1250 172088696 172088699
    0x50f01050114061201032303070c06021203010311010c0303061815050d03020c0f0f0a0e04050c0d0f0b10150c050105070309151e050925060f03050a0b18040c 69
    0x10401940701300f0f401c02c00740d418010014008070320b6074400a010103855078100050700c441700c072006081d6041254150b8564030851000c000c1c89405100840e00c2c1e00b81000700c2c0d13103550f0450355005800130851200b113040280004030001050b01070707407040b0080c0440441201c0a180d40c0c0c0f0641d00540340d84802c6c070005020104000485081403a1040e40071079141e006400c0f9025072906010f480062100070941c00104040245125251400e0f004040c0c903280310360703400d2031800d03003049841d240340e441d8803501030b66440c902131000c54a02400c418080381e11648456040e00c1d45130324240c45170301c1c80d0050224003030200342450a00388c104884480c01c9205800034401079480c0b00007542118999407019001034032000c245581e44c9110b6011218003030503216659041c45ca42c903072500c21103504507035954207603000d0800b8698a80c983c4c4040c080c03000301c0260401e02c15040070790003403800711100ca035807040c140c03a000810b4100301c0b02c4e04000715010010705103500c00c4000c01e910540d607041c1640d003034503d1a00380f0070 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 172091196 1250 172089946 172089949
    0x18050604020a05011412100302060a050a080c0f0d0203060f15070b0108030903070b210c0304051605060d0c0201060519170705100e040207020901080c120105160305060607050f01050114 81
    0x45c211041c1d05000300d15042a8013169000040c040040c5441054909140d01100580c1d032503015104000d0350f17554840e154003480302d020300003006c050001d084592040c0000c40c00300c81214101c0790502d100003005a181e071a000c0218000004262500d0381c82a82c100054111848240c0646105030040c191543c469036500101030b264071a000315107400da0012003042c403000403064000c24822110800341180c0e9130700080c1c0d00c072182e5401c0e40c0c10107001c8000001c2c8002d008040003980400300d42500d02003401850b20340052075522504010300b24007512a00f074184194001e50008008080c050806024122004081c262a46441c0250074000c44211380743c0001c403000090440503144090a560801c2c464501e0503140c0c1400701c80c00e15446602000700c05e0040e122484030f1402440d0520091035801500307001c1244155183c854a0003d0f8500020850201240c140103280b1605c0c900b000101070b121070b4086900c40c41807650180441c411107140c1810154154403150480300700d14003490041c1940030 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 172092446 1250 172091196 172091207
    0x10e04050f010b070203070314010203010501030f0e0c0108190203090f0f071202090417071a13031b050102120f0601090e042a08010f1e02030112060207030318050604020a0501 77
    0x700c500e9018030301c500041c041c1e0503c580007404014001011078045a5896483c1c2c14006040d8a02c4440c80e500400108500d58060288040f0301e8101c01041c0800101c03801c9041e40c41002e182c2041c100b010240101d83c0700320404003108a200c1c0c1d6a6000d55681c034250000c0ea81c1c82c240361030010f0a40c40340b80da8001c9030041c040b0301402079800c4c1c030f0b01d014800ba02540800c0a42c0313601400990b8081040307410381000c82d10000043c005e076441070740711407596003a0148807500940b00038046a111080c004802c40041d9018804007030988040a10017403100650408500a008100041d10ba4441240c148040020b402d403419111380001d90341d10502e10703104e40d00d0016005085d50300030300071007007001a00c0072811031004540037090031036100c1f002c9503540e0054030309681c85109100d600542d06d8243c030242d0300d526200712048058101003076165500d08200714061142c18000903007490360110740d1500b0103100340c01542e4201c1d6600d0a001d43c60a10b401c10365202d0f10700340c500720710414401000080650044 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 172093696 1250 172092446 172092451
    0x18062003011a030915090a0302010c02120f0f0702040204030804090b030304150c03141605070b03060a030308150402040f0819151d120a081b030402010302070812040809010e0405 78
    0x40645603070a450012a031031054002070b04043d454003818a10100400900107843d02c25001a030060601150909012b42100c96000030641150016541149890000012140314031030300d4450a56a035104508548980101d0710000d50282c000039000080c041148041c2c4242c03400588100520740c207840030140c0d030b44a10320074880362a400ca00c490700468018030500481c0f038068200400703906500d100c5680d845d8449231201049469101075207062250400c40c481c003411003c42c1c418650700300000006e2465005200080030230030498001030300034555030940d9041c850003502c01d54503a0f84521292100b10f11a01400b1114410384d28144001c0c070024181c0c0000c280c001c807060000c8507130030000343c0c0a003e80403580465140c040014004900003003221492407010801220703214000300900401c10322002d030500c02107500c401c2d0b48014030703003515045940103642402c0040e5a00303904d1810700781500617110740d8440a002601040103100f2100020a00c0c524242c0c1c411608603040c03800c01040310310030b = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 172094946 1250 172093696 172093709
    0x3060216031d010804021309050f0f01061403060a0903120608031207030c12050601210209010908030310090b0d02040f0c03050106140409050402030c03060a060608060d120c061806200301 82
    0x81c4041001b505101d1807c009940500001042c605800e407a800d180c880e0f5810094030039800f07030103100c00200c400e1041102412900e298030310404130b08000240c0e140c0b40a0501d080309070f030b0f84a8500805005611058102001120505c5800c0d0340d451800d450303400a00041c02c40008000c00266014400d12034401560f043d074a801c48894003c440040080c08010003040c1401a032914107103e60800d0119074400590351000540c0c5c4140300400101000025031100405900c01d2040c070040c642c410544c1d1b015200441c0300000c00035422000035420a0300031001030340107443d1a040301019140d5410440c0d444140751403d00450740d075450304503140d804011708e8212203013003400144501109a002150054001812039040324441d00000b8101a0152801f40c00719a40b44002c000d10741d006040039030f114030201e503800300d070024a4552016085803a0142c4082017407842c2d03c2400c01100ba440103a01d01c41c80c42d000700d0130303042078903000300140070b61a031036500803000e00070b44070b01c803a002000c80713068481 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 172096196 1250 172094946 172094957
    0x30809011b12093f050903030d0e0a02180708013804031b03140d051603020f0304060e13020c0c0d030504050d120305070309110f010903060216031d01 66
    0x3060751040010250b4200803a0980600440c20a80e081100c9050400900031120a0010180e44902c125100d40d8910304d0024400d0910003056156000b00036603400d080c46c11800f1880101c03c0425608241098400a52281c984906a4803a90211007001d01c41c1d045901c84803050390f2074910501d6035071414104801c00d01031300d00d07003094100d05003001c01e100d103030303844420754101600e030b603103040074043c000168200030f403600c100410511810140013401d20028401400c409084288020f10500c944001801c0c030034445210601014800c02401d8007a400c544d090325200c2da00c500000300b501c3c0c109840c0074403511000d00c11501d071031802c4c400c40381c00010076401000030b03420000501001030b80100041d001d111042c0310000d11925988800818184200c4145d0f00d03034544440080d088540160441c003c051070410000002000035400190440d41202c102c2c500c0d208000c01280d0318452a0002014140089614510840300d01003200e550362107034172461550407955010440c50400440344a00060 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 172097446 1250 172096196 172096217
    0x501050f040903030212010602030901080a060b07080901050903100615180e0603030409060f03021008060d0212010e030403050f07230108060609100c0204150609050625030809011b 79
    0x1d0664012804684242009418420900e140720551310007688540090380000402003070365030b48003240320b500c001d540c5001c11800342000e038500700383e0007180002410314070000f850038040e07805031050342d8144a0040c100c81b0b030460210441c6001e888244214980304841003078410110380110348003821240c1050009103003030b1402040303005010001d0302194046c0010000400c000040340118400340207080c401c09620761941c81488a00d003420500003042041d501e050044507030f503506030200e919404590f41540310140708080d0b401001082040368091100081c00400c000d400304140c0f00301e140d40815154465170714140461100810403840c41c00303080c41c800c079074041d42c0940700740e6801c49006080f69081604180104000e03c0d0948109804030310160b1182c801c500d4180901146003d4150b031500116242c0340d00944145181e00641d0311504000c03c014070b0741891181705200c448221185030303004500d82c0c24040c3c10824284d030b540c00d06500b0841e01c0222241d00b10310546034603c0c140d0783c2c80a0071 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 172098696 1250 172097446 172097449
    0x6020309061303050a03180f060512151e1c0201020607030e0a020607140f030415030908070b01030f0b0c04030b130c030c060f12060f0303141c051501030501050f 71
    0x541c0914405000b0307000c0c2c0030700400841c40400c030424215200b42c945401c101c1701811440448022640b04a00740002c544083c0042644481aa01024a880e081400380d4480340700500100e405507000c1d60300129031032200c1c04140c0c042c201c0412515020384108681404c5c03d04400658008480e01a0250f8001008501518407075070000c0c0c01915007100399402d080c0c0550025115038480d07101640e40c60b1015101101c249000d114102001400710021031a062030305001701c100041e43d03130101c0285a580da43c0c1c2424040c40200b1120140e030b000c140c2d40003c0da160300e0290101c14100c1800d83d03c06140d44002030380c007426a400c4405603074018220410540c0c542003400c0e40100325040850b0791040b42080040015500c1c103417003001d00701c1a29095200303c004000144410a413801c030b0f85200e410040c04015408078188a40300740c940526001c070841c6a09160340c1007a20500303a200e40740b0104000c0c044206142a80454000e51100a55100f404d061034011401c0c2c42003030281aa022086c0d00d44a0801e = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 172099946 1250 172098696 172098709
    0x9060608010302101b060507020c0a0806071805100801030512090901030b0405100c0206090c04022703030c03030a0203040309080d0206010501080a0e01110405090c030f0601031505280f06020309 85
    0x4a00c4c4d600d824030818001d0407140400c0c2c0740c401c1d41103d84503102d10601c00115018410810380280a07912072403046e280064682d0b544c080600030a082c03041b050f000b500440b01040701c500280c21302800f01c0202500c0100020314411003480296040e009010501d8080b036003044c100e65154030028120395543c0d0941c3c841000070407002c1c1c000c840c2c610604854160580d6070340617081c0c918025401800003494074503951418000c00040e01449548100821080501d24281308503481c01034001c80b0140300c200b200402d03d0b522503021a14814880402085804171080d0000c41c45140309948100c4855038800585503902e104d0350110f000751700083c0060101c0d5226500d8594809a00040031840c240c516104900f110121202c5003a0390704006000d00450408019098100d50740c060541d103035180256408940740c40c003810b20b0341015298032a6051040c003026031301001c0c140041800c0c1948074100201040144940620010013510300000204450300b140710104031404c41d0040c5151078056001c0069 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 172101196 1250 172099946 172099969
    0x409050c0a02070608072105090c0f18131b06020d030b01050a0f0302040b04030308040506060603060d030e011202040b180a050a0e0a06090203090a03031401060e010819110406030609060608010302 86
    0x70070a804401c0601207034261f00e51003039046002800541070038801000d0b420021619521030090000c040f0405141c1c582a505507400c0442441e480343d02d0702c5600c8074004940b04694041c01066840c10007204000300a810b02c0c08a48640e000c46001e20390f04402a001d42d40e4112040e0301240c000c1c000e401ca942e000e12041d6000d405580f44c018585034131001030041c590450740094001900d420304000400c2001c21469070080000c8603082d04511b091800605603d40f8588000c0422624240c0000540d0192030380c40707884801520150344482d192200000b80342c1040302c107004410080780c8900c0e00e0341030050020054803001f0f81074080882c1031030407500e04c007400038101401899603420b0004900215102641c0136401000242424080300d08009013510203008003050030580307101c010001d05030403840e4806007000030b00741840303190b07500680c0914890b241888107000c61306144104e8940c200031001401600d00c0c90f20200040360f20f955801f002c5800c54003401000c0b42d94100144090310b0100450341 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 172102446 1250 172101196 172101211
    0x8090307080f03130e0f0c0d09021e0906100e04110909010e1008060f010603050901020c070e0a0c050f16020d08041206051302030a14010b12030409050c0a02070608 72
    0x111000c1c0e94052141c9080c1020050354a5a00301240000107040805a41002000d0844001c030280c1402c001c1c03907a41c8038028010912400c2d00207070103162100d60b90840140303640c00404403400e2040000c01051a95441d20300f8034411460070001544510b00702300c04001c1c050f0070380c0e2008100c440020901c0018000582000c0c042101071000c190155030354104580a0400e0400307900303e508003920400c1c4a181e01c0d402c08110358100608000d03081c0c61400350241112954940410113485a440c0c207030080c840c0300c0011002d030040e103001044940201d11140c1c010b80d1094000c01240c1c01d85901218039001e22104034200090400c8580030500c5c1c80600380003d00d00044c00b101c030340d0030244d407031040c6c2d64825030000c00e0355040b142100f818810035110b103542c401070803500200501c480354000b03a1900103400f002000394002504990000320250b0044444450180c101091b00030b000d17001c0b0341e503500148115200142400d0000741d1a0781e542c01a60055101da0b002892030b5400d2031020307134070041e0040131a03 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 172103696 1250 172102446 172102453
    0x1020a2d0203030d0605120a030813140a03020105150415031118010e04020102010b0402070b280c0804020405090d02030304060519050a1b020111040e0901140405060f1003030507080903 81
    0xd40242e5028802004402d2200b03000007141c030f1030300050142c00180c01081000c1da420070105000482e0300000ea8075801045c84000c030030643e8840c03401c00030041c8000c4040e100340c03254002c0d000c10190150712980c00f628240c100410444c1c851000c100603102203072004134960700140070800c0021001c0d44c2800b0305640040408501019030050404118403d0340003103400400401070105650302031044c2d01c1034203000d0b9019440e103d4070382c4554104103405024420350358800c0300a02c030302400000480c0d0000701443c1003449024180032000b8445030f42910240d01c19858140030804a5a000814191074030040d00510b0070341da100e86919006040080070700316840320011910b9060706041c4543c0d88030301d804c80000903064285101009030361024941210079a85040340c204500d0074a141a02c00b1204601181005545c81c500964090306080d81c1004c2448407020500c41003103804100039211b4a00b00000c504c540e074581004c4800e501c1d00e80300240c00304404004d0741c000b040340c0c64010903150170041d086 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 172104946 1250 172103696 172103783
    0xe0309010302090607060c0f0e01020303150d02010306090f02070c08031306050304080c0106030c090e060c0d0213030b040c0503120304020603070305070c1b0f09090c05060a12090501020406080601020a 88
    0x84005460240d004100052301c214001e00006403ca41ca20411810a200950440c9000c661008442032100f000a11480000b12044211fa1280e0003020240001c010140000303104c24516401070340022808960b103215400002c5240e050000c280d402d408401040202e03018940030041da516031000d0b00903261840200481126500e00b405020000c5100b28511040945000a000d08440100c080c00300c01e44c0101040c0000862203606480c001c0c3d44603100140e0f2812110a901d010f091541d10003404015000d08200612003103480800886409400350303008002c2c910145021880100e034000c0d4003407000d001180c010751107a0f01c0640d11005078201000c0444031500c41080410407000410324401a103002404001d240310400001040c0103c0180130904403070703407140c0b21403240c0e00070036020b400080355981016208030443c0303111030f0754032034104450907160030b0807800303507005005010210b42c450700801c0c51540700081c40d0354401d400c03490b040c000c0700002c6521324101e020010b40e40200c1c00080b80 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 172106196 1250 172104946 172104953
    0x503060a0b03071e030207051c032306011116031b050603090a030e010c0507030204050403090b030106020a020a050922060b10090f0608091c0315030f060501090e0309010302090607 79
    0x8501030201e035110500d03000302070011283c030004400036134030070140140310107030000710000360104102d1016101a08140700900c806c500410143c1003080c1c036200c0800c030746d21004014150050241e0341c280e80d500482a0703070344c09883d1f40d070340301280d055401c65200303008102041c0081c0d101c441d00d07030000000018180c2da44000a0040e0024bda04242c10b805c0241617400305504062404101c2a00f130801c0c0c0101c04054480c3c644030219440064081d6480308005002c044c492990381020f0640c4001d41a101c0d42c48102c02580c8002c6030804130f0003080360400118140c5040048144600d0007480c00c0190550600c41010284140c000200c810a071119642460703580d5400c47c0b60b140f2030f00b954403030a4040c9400d02c1340a044895a00c1403051207052810f0141101001c91160300c0401c4400c640e22440010060480003001203600005000300c40300e001208000059440c4c00403180203c0b41484640d8851554804480c0d103854812034990080020204650094002e0000301500912003810510f06e0344 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 172107446 1250 172106196 172106219
    0x180706050f1e0d1a010c0f050c090f090105010e06060a0e13061206060f031101051303020d0c0303020d0207081e011514030601080d0503040b280501081b03070302010503060a 76
    0xc220360a00d04012540f02c41c0c0814038401c460148003000762a900607803030240040e01d14100341c0790260003080c044c1d24840c10300004202d80e414110025242d240d040c83d01180b2088001c0042d20118510350920000040300c1c411003181c58010308009001c42c1c40c0043e181001d81b10b9030742c61504c01d5000b05100d019007201c444680b0130100200724070000204120410f1500508850341ca40180301361500861061001c1903124051684d040400c1c200181d0707804200c03402d89168002540000d52040518251504104a141c01c0e00203ca120b40c08a0300c0000180c1400c0e40c641c03940b409820701561016143e140070311001400030b0f01c2c0b078040e00c000148040c01440c56007100c01c0d10742c01c40710300d0b0a00d03040c1202c503a00b001c2001c6801042410003406184056040c010701070320018201400d80143d0401140b009000c0c0c418441c281c18211140040c1c20b80910054000b40c0024451800d0a00482200c4441466160390040005a005020b41000d030f095030300554561300301901c0150441000b100106801411a = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 172108696 1250 172107446 172107487
    0x606010e0d0614160c08070f1407080d030605090601020d081e13030f05040b030406110d02070c050307081219020109050f010b09011211040e0c0307030b0f180706050f 73
    0x1c243d40840c6240804081c06100b156030300c2041000403400100001c1008a01a0789a0a5004000683c1107280f4180751083c0b0400206809003070003202d00005011034006032010111000b510103000040d0f644007004045a411105180560460450490018480c40034150312105d0a15160001032100c02c015051100898081252068080300e60040c1501700d04083ea08103200e103089447c242c109514404c8500010304001c181030317150407101c90000005000c3c6d800c10119040c0464941c1c0c01c031304142c001c8c9035052180d01d009018840020a0b492000b040308517042d440104000d24001403928060701c0010703590b007002d085568801380c445c0014420301070a06034030200e000100d4080d0208042000c11a410f0340b2140e50008094101d40c0010a0070304454030000040340e00194008200c00464240707803400c0c0040b135242c0124a00482046104014a400b40040703446008181d9103c041425210403d50441040c50f0700c52039081010703610074030007400440c889658050504600030000d45c08028070 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 172109946 1250 172108696 172108721
    0x3180b04022809110403080a030f050601080c07140703080a170702010b010c0813050405090f100e0303010e0c070507180b04060501050409200703080105150406020606010e0d06 77
    0x140144010351030807a00008155468100c0d00720542d1080080032010a143e11030815900e4982d2a42001c102d040c606840c000c54110104c0c0741d45d84070700c0c1130082c014509989400d03982403a0401256203035101d584920310606420200798500340305a10f8002c86080000f540e01c03c00c3c030600801000103820800502503030219034840c11040800181d03c1000f002d40140030008581c98130900e0012070380d2150b004410950800d5860341d0324038081d012107002c016079400c002c0c1c22605010038020011000107004d0081d108a509580002c0200d460000650707400d0003603c9030303039441480140107501f480c01040790007a004580d0b140c40c1000c0c0e0b40c0ca10741480041d41c040d001d0350000c01d5004003004501c0c00707840d8100c0800c950400515081c1000a0020700070f40c060149900e69614403510f4190484c7d50101d03d4190303081d8240d844222515000b05080702c01d00500d40244800030300b074066070703180704240c0d001d80e52a5005401d5075030b9a88011141a2420188103a11540c1a004040494000d2145400d440c40 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 172111196 1250 172109946 172109963
    0x31009050f1b010207150c0210030213080309100507020a0308160f05100509150a0f09050a050102130506030103081602011b0b011a070503121f1203080a0603020108040b070318 77
    0x1d42001a00b403444540c011000b4221200600600e20360080d21f5414a5604035140d0415001c0044c0440003401822001804541003200103c0c2c0741c0800406090342642c101c801e0038840d00741900448607402651002900025515000c4c00064966400f418110845002e81e16480c01e0030b4450360b105010194054030031780c00642c030800070031080d801116801a40c41c00108881708011004078a8140e006020144140c0d035181c414520b030b4019044480c0c09900801151744154481c203113a0700039813003200b0240c1c01c0140031000080d142040d00690b4100c0790084000307403e0540b42c0300e02c020705009150080741000624090034920000c020151307545180280d0681d80c0d15810070030240c0420003401c40c0348842c580300380b1800c00050070000c02c40e810341e04ca00101210716118198003ea240e0b440d03898a4901d58000d8002082c20701004400d451701e140280d0b606d68641e00c030382054204640c554040603001550ba00000b60204100f9140075800105c1c42c0b400080c1405941d40140f82e203031407604201c480d400c = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 172112446 1250 172111196 172111243
    0x6261b060306064009051306090201030605150d18020a1a0f1614030c07030615051008090c0f0f3106050f03191b030803070c14010902031009050f 64
    0x1141305030010180c506800700300502d0901c044800c11000b0f8a1030000d003029111001d401c1164403e800030303401081d01824070301440e00007005c0550140c00c09110407118a1400000702d4181d00340d91200009160080c01d800022410004240110103810086403500e003420080c01d06440d07141001040d424008819101c001c0f4218a440e071684c180500c02010181c6c81841244069135003c202402260f40c0820001098029801c00d00200d1070320364099540048c2007001e0620303c030f030013030212445807404906a606800c125001c00107131075509103240b40c0105008862002070308103500001d09109001c0b81c0185c4406041d0b1b9008100c20400304600031094a41030204164200420b0310000c8240032405410566400e4882e040b6025484d040500017640044401405540b00c0b002d00e005036800041d0281d60703141900c0007514100c8086011540109040000905020f040c401c82e10001d6005010704000203030260608090b1010007410344060003481c040c1c0035076040c100702001140401c070108034070b01e0 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 172113696 1250 172112446 172112557
    0x609020418171c050907240c06020a0309020a03061a040203010b2506021809010b2a010605040f050a050603060106120c0306261b06030606 61
    0xa444030092909440400e03a0110700203610741d003035290741c141454030103a1142440600026220f10820801c0a242d01d044148485c605010403040195150070900c40c9501c42414560034420806503410030000d01c079a05c201d0001200727a0010f007400c6a4a180c0451540c40503000602d00341e29039841140c900c0e40d03c400808000c110a5034011a640040307500b1030135076140270305000c0144240d4a011104014040065240d1100b80116042040d0030850464468503800f40d6054050760015038140b245030002d0000510780d46000854170610b480561a00d40002c4a01010180b040d41051b00b50083d501c9010200d5261564130070350f00204259540171519080800c06401115000b030700c9280a40c1103000107000c0c0f0303500301d00700b1112a4400171000400408090f41100284070707641008040505440300765140000480311307a01050650070544810301a6030b4801c0e50f041d110340300301d150802800c0c00013802500d0700202600c040a00d05200003803114108080b45840c01c40400c000003107441e00000880e84 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 172114946 1250 172113696 172113701
    0xf0703050601150509040209011b0b0106021207080901030507050408010c050306090907060c08030a0b091e09030301060903081612050a11030315040506030c04050106050d0e060c030c220306090204 86
    0x5080a404a00c0c03450b41882008100b84903500170540034540005480c0481d074440d00d0343d080704601c2c0c03414441e800398040ca0030300a445400c2c807900b00103110300c071090111880f10301c0c22502030aa0043d8150b01d01903502c0015400b6040091243c0103100d02030000107a00c80084c02412042d0240d503039907560b246042c07420000c0b01500038000c003502c1c0c2c0c040e150074011140c0008d0740800c81c0360805d90351034036913458440b4034014007100c0c41c2c120b41000044041c0141d040a00d80c05d0f0b41c2e8081c50200c40c00c016514130794000c0da603010900c24280056415001000486c48032401400c3e0a02140600100c0a401d1703180d8501d64030075115007000140e0009000001585c0c040410441c56401c0b40146180d41480c41d09011f0400d5400c82251190350303a6030100d00d90ba50200000b044590020b4018449580d6a0303002404542203031002c640d10a0074003005a1f180100803504074412041c800ca464110b0711406410304031a044001c0c01407c86030036030309044502914803840c02c010341c45500f000c91511402d07c1403106 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 172116196 1250 172114946 172114949
    0x10c08093a1d1e0d032708160f2d06090305012313060207020307031113020408060c0d0b04110a1404030b0103030305071b0c0302040f0b03070b0c070b161103030a051603030e0f0703050601 82
    0x8c8c107030741d00d8280010f1403241400d40460340c1d0b2401c030058000c0304180755030000e9400e10094020b80020b00300000c0058104030a44222401000200b02c90080b40c0d0340340b0030a242034407504400e0b294020007e822031811100c40c014560117400c0040c2010b006da070119140402c5c6420507a4040d0755500f075036215180c5405e80d1009a102c140342541001d2600c8601e507900c0e48040d0a609104101152220880d81150301082130300c00c00800601c00958044070389411036000d540c449002406000354000c24041c0241114116544030b01080482e81c610f450880080c500a4840e2081102c031200060304c1e100041c061035a61409501c000a8042c82c0d4030401c421209140300105a00341000340c0704a40d80c1d4080b40c0c4404a40003980d080703a549a520780e405050410681081c0c8040d0320100d107140008032428807a10249110f450001c0581c0f0020701055500e001d0403800c81c0000e803042224881503041c82c080c20304001d102e030030003041050030b2604042c01d1403000c0c08907079010380c0078a0080082c440100702407030 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 172117446 1250 172116196 172116223
    0x90906030f0a0201031109060703110d03020a1d06130311190311150d0c08011a04080706050904020415020f010c08093a1d1e0d032708 59
    0xc85101c2003204142c440d04004400303418135689040e800c0200c2134101c00c8130703a02c82008054540c1c64006180180c000c0ca03880039000094800c000142450501902c00c55414900c07688030b5200072140000a00e2642070348000c201c1d00084180400c450350070041072540040c3d88627250315480046c0c0131050040040c18122460400d990102080000c40c8008046d000d821009a540303111591001c3c94180061041c141d580403803919007203071217404541c01819075068403191f60050b840020144001c0829001c5c2e8040d11400d50004041041a0f80c0600000d024064002d00b000d41448c3e45d4500b10001001030110f5040035801124250740e8140c020710901c00203180c00d0405080d6814030504a40da907801c180c501c0031101c9204144014000c401000e00c00c140b80b40d40c43c002c031400420b01d000030b08138150f060120f52401c0075181106c00a02d403400e40107014508080f40e602c1c00c0f944503000c00103c000d000d2425010320131001c101c8417034082004400000b0300441004818240d107040481c5190604040106 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 172118696 1250 172117446 172117453
    0x20705030f1c0615110c0901080a140303070f08150d030305060916020d050d0f0e03090306070801050d0213090605040c0f050f090604051008151509040f0201031e0509010209090603 79
    0x184520354500640c4001c811051a281004955a20381c182c07811b0f0301044016808400b40000042241c3c001407494106446010290030501c40c00700025900d0100b9150800400c3c541c0402c00d4103144181c290903032050325052190040b94210010807408460b080c405e50000e51544204841800c2c960407c0390005a0383d180701d02003183d0050b00a40b07030a000410742040010000d0800360741c0c401c03900070580e1003025100402c041e0110a48066032503114041e00c1d03010340201c900040700c1030f008180c1d650488030013425014410300300e40c0c20401040d107000c01c484001981d4000310008230b0954800c0c18840c1d440380096440060400c0381c0a03140002d254030091041080d02d05114064480360403558021006032004916030711480c10051118015403c039000038031070001c00c0440c1c141c10f1406180540c41181c04085d0742c140590a1050b041005c80303020f441e000d060204000154425805090701042c2d41e0b414441d035011546202c1c045e104192030ba01007c0c1c0d000306c2e01c1a158038050900e150081001c4006 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 172119946 1250 172118696 172118699
    0xd09080a050622150501091107050c15070503030f0601030609022109030f07050a0615060507021e0406090207140640030810060e03031b01020705030f1c06 68
    0x21542e407000010a103000041480d03404019891092000700e90303a940c4260418101c0d000c05401c0c5004200034412103014500b130030103202280310b0b00c1c422100400e82240241442d01d580d40705000c04042c1d400b0b8001d21401d000c0155102080e024800f4600402c1410b200c105c0e6420321b8400103094880c2034014118461042103103000781002c0065117400101d0082a0030403540d02d9112190a5014031142d11800000020750601000008501c41105a02c6580e0030000c9092200780b41c0481c00301401600081401049940003503e4285880c4034581d40c45289907040c0c1c408039001c20103490703481c1d00c01c02c10301703030049148070801c142604c0e002d0840a0307510041c0003d240c04100d50035090a0010341040b9040b403c000c0c512400651400075440d070000030340c11031040003541350050031a401120880e243c00410b50002c2503040c410260401400070040c01503082824840c80500c1d4010b00340c412460319036081048000040040c00500804050220a542c4480b100c0103c440b10007004500c4c4944103281460 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 172121196 1250 172119946 172119953
    0x1609090b0108030c03090d0c030c030b0414030301120305031306061403010e010e0d110703050d0519020c0906010f23130f081e011d0303070311090603010e041b03050d09080a 76
    0x1030b1042d07542c01f211203072000304242c20711610900e001d800280c4011860900071040c450320610030341c09948075501c0c3c400003850348110692640021300942130a51002c003410303000300c0e00c150080c0d81c00019210300f01800c03c000d030b6141c600710f80856020b000810540c4140503854034081c403403200f50320704040c003d015406804840c241c4a40f84001e00c01c0c1440115101c1c3c4280d10010411400a90791001c21121461514900078180fa0044020390341c00c1c110601d00071941d0351000c9403501036104042c1c0015403d84800c070040d20401d2958101c001040030111a04c00ca40411109408040000c200702e00d54907100032240c140321100715003203610603c01c40b050811440d5070002e001841440c1c40128104410480303204503000d0590680c808449000032003000c071070300038080015801400c06480130481508001d9039014540644844240e000d603081c80100942800118610303485881101d8406a4040407048018110034540054440c0d5002100302c1c824150444807520240640b0002000e10708160364 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 172122302 1106 172121196 172121203
    0x1051608042310020601290301140102060117100507030e0a030f090602210706020913050405010b0d02030604030e060904060602010915141303021609090b0108030c 72
    0x342c161508052040440085401802c5030303a01e805214042c50b080104600a00707913168048114443c0b85100840c00784c8481040300348501d50100c002841c1000503008401000d44040f50000002c1c400690748419200c00400071a0300d64400108501408a820a9010901c243e510b1a8100b503088440c4040344445c995504030080d5640c01c04a0390b540401d4942c59940a20900b8130b8001d5030008000e06145025800c00f51411400ba03012804c9458040c2c102080c9075036503001d02040207000e005a246170350048500b0312100110360002501c80d10003034802000d011188034038490300d4440005031050190014010040160b40d440040d001c0d194020342102c031140c5943c103c2d01514000e00c906582200c8409819900d0ba03120304c11442c0760fa21200e0b059040d44200e00010300140d055011410142c040c0c0c0d2408241c0440c5881d0019403582d041e0861001c0d6081404007009800c6c001 = true := by decide +kernel

theorem cover : BRFrame.Cov 171942446 172122302 := by
  have h0 := BRFrame.cov_init 171942446
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171942446 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171942446 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171942446 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171942446 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171942446 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171942446 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171942446 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171942446 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171942446 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171942446 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171942446 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171942446 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171942446 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171942446 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171942446 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171942446 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171942446 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171942446 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171942446 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171942446 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171942446 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171942446 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171942446 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171942446 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171942446 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171942446 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171942446 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171942446 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171942446 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171942446 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171942446 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171942446 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171942446 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171942446 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171942446 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171942446 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171942446 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171942446 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171942446 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171942446 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171942446 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171942446 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171942446 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171942446 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171942446 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171942446 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171942446 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171942446 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171942446 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171942446 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171942446 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171942446 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171942446 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171942446 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171942446 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171942446 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171942446 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171942446 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171942446 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171942446 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171942446 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171942446 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171942446 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171942446 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171942446 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171942446 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171942446 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171942446 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171942446 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171942446 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171942446 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171942446 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171942446 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171942446 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171942446 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171942446 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171942446 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171942446 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171942446 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171942446 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171942446 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171942446 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171942446 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171942446 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171942446 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171942446 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171942446 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171942446 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171942446 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171942446 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171942446 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171942446 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171942446 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171942446 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171942446 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171942446 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171942446 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171942446 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171942446 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171942446 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171942446 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171942446 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171942446 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171942446 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171942446 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171942446 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171942446 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171942446 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171942446 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171942446 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171942446 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171942446 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171942446 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171942446 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171942446 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171942446 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171942446 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171942446 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171942446 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171942446 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171942446 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171942446 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171942446 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171942446 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171942446 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171942446 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171942446 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171942446 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171942446 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171942446 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171942446 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171942446 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171942446 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171942446 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171942446 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171942446 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171942446 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171942446 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171942446 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171942446 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171942446 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171942446 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171942446 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171942446 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 171942446 ≤ n) (h2 : n < 172122302) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
