-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_5386
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T15:42:02.488684+00:00
-- url     : https://prove2.me/submissions/a7537f1c-f9e5-41a2-bfd8-ef969e00f6c4

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 968525179 ≤ n < 968705035 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 968526429 1250 968525179 968525183
    0xb161709032d03070e040b040c0503150306131115030a020a110601050303040909080c0303010806070906020a081b010e031617121317030f0412020705060a0e060d0905010605091b0403 80
    0x1c11708180c017070503100d580080403500c030020000c20111060316400343c107e0b001500d605000070704c031200d6402c050400207001405442c034401d241006940c01c0d580c1da59802d001c0703c0c6540c2c010700e00141d02009982664061805110391510168860b8007001e0000c0040ea010112003030030ba03100000410068030003000b240c054030170480000c0f801c62540c0c00d1a001601c06c1810241c41e170321001000103290100030610a020f0745d460fa65560301165030703c404aa4581201c00003070f103400c8041217410040c200412583c0c0d0200e818100100f00002030f600002d0464010504d00b0f500072003154070500402290b600c107208024000d100b51030030240300c1f842c0e140c04030318010050118101c480c40e410092040c2c240100f5000c044510038107640b031a000c00301c0012070380f0035a000c640d01000c820b180c84416001040c00010703998003400305428011040c00498900508056480d009030007000683c0860219018001e9000d004000200c2c0340780c03801052001c0004000e1040c2a60b1001c08035144203a0407490031181229 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 968527679 1250 968526429 968526437
    0x70210090b0a0902190603091509320a0803070201141009230709030606140108162001020a022506030f140a09020a120b161709032d0307 60
    0x8449032000c2130050313090105d083c10401342000002a031a505030096001144240c0078109102922a00c02041d40c0700308000411031061203040300540140c00345440c4502c0611007001504500038146282410070300302095600590000801c41030701e40900460b0300d074421a100d49001443c1104440560200a010352003405072030740304400048680c0c80302d2103a082c00c8090300460f41d08060078042c02120f0180300480d88a418000c1c00a01460f03450384e032104509042e19546e49903070780c0628040189010043c5401400703407848151201a034030144ca032918040040c001aaa120401e1010346480e80c2c2400b01003070403008000c04034040450140c0035048030a14200170a4012075413003c030019203031251004244001510070091a0085500892035641c001d0380c5c151084d030b0701d412585100034103a0b50054030120148021030150440300340041003101c490f01d02004160021545400c11140a54540546500c04541400030f00101641d5690300c00d200d2019031f40740c61a103207201030035010003000617041c0 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 968528929 1250 968527679 968527691
    0xa06030b09030a1e020f061003060b01080606090d050f03040305010e15060a090f0209130b01170c0715060e071d0d0f0b091c05133f0501020a0305070210090b0a 70
    0x613a008005006180d040a0181c603041e251000c0b040200300d0542c0b02c2a1011401c08022426650244030304d54020200504004c0c07130200504113102d000d040ca408200c50754412078619107010b107000d102038006140300d2400410180880511946400c0400380880616154003040c8085a5545d58521003110b106c0e040200341c4401c00b070001d200a0203071388d01d0b1540100c0043c91007076070f03820a03a2103a0910b01003600c5a90010908203001107481000300c500381c02a003030400c110008910765a444c10380007e20000007045480d00c8000311203a14209852220204000441c100d224041c001801c0080e44000d40d0043c41165003500d03400315074400e850010f002c000000c800b0940000c41070018610704a0a10b1000c44021203120005000c0d07803110315416010403120801150b81701e80e0307101e0000409105111220010248482c1e1081d10310f180126030000006084007100181c001e0000e0101c624007a01c0026092900217006410903603040c2c0141c0c03016143c40110000561707403000300342e04410402400510 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 968530179 1250 968528929 968528987
    0x304140406140d050106080a12110606012a08040303030b13050c0304151503030807030c0305091c0507061406040f23060f06030f060f030304080c270a06030b09030a 72
    0x144241c0d04011440d00072102c008d070900110690f42e140c10301c1c070769803400050b507400b180c407035220310058800600140590322000552522041c03000c403030751400e01244000109036030b40e00000c1d504c550701c110042a21104c2180e00c2c2e1803c0b0921200541d15403005021620305001074000d01d20000b84010020040d01920402d41d15003603004d4102d155019841100307180c2c80341030240a000d01103a5501c002402c0444038518680b1a00599000310070850050440799210030840104904040501c010030406001c40e1010400500400781c84156081601010b4140f8a0134001074824810740c0d016a10300300100c02001500d00341084104541612461040d521b6401c00140311000c1112020341c404004014840308000031300425000388000c0310201c106207010024580c50b406603214410b0142c01088900d0058201a5689400c00200c41990700d241c0304000d0781d07d0004042690741d0340c00d45640319018070401902050003a004011800218100701042c10000e090920001100305951001054403c7c = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 968531429 1250 968530179 968530181
    0xf031f0203040f0b0403020c09100b0409330305100c0806221d060f04032003090d110a05040209060406141b0a0c0905011d090c060406020304140406140d0501 69
    0x2180f990300518020071428a4140295112900c3c00010300c00c0381030f90085510b0107c03501c524421200865070144c00e01d4030740b01300d81d001002c00080700d040720109006040d5010003103038111740c0e01c004c200c1440d01920b811814454545550035a600c40c1076441c002c0c00100c840e800882d081d0b40f2084c2242c048986a0103144000c0800c0030007420035400b64145410007180000010349410101c5180007103995582d00d04109045455060f5005004110007010003c580003900803d8503a400307560341264030700003144000c6010004161811740d81c040d24001060058a00880040c000b804102c03030540c1081000400039040c4e128500c910014002c01e000f480828008110545410800400c00000040e40f2110020b441e0b00300c40c6001c42e841914004003040f01091845a981640c0c07050b840c00c51034448040100315108005803c0c20700318070401d50521000e0b0b43d00c00080c800781903035502440d200e82c81c046c0812448250001030502c250305011050041c080240340145e03640c9400c50380e00117109501d081c018 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 968532679 1250 968531429 968531453
    0xe130f020a03140c03070f080a110a0503013303020d06030605090a0203060c03070206040f0302031317010b0f03150408040b070804050906010e030a020f03010f0203010e060f031f020304 81
    0x2042403800858014034280d01a44541d10264040031000c040d80c1d0b070b0039101d41440c4021140d80300400c4120280b1004680301740810b0b80d020036240000500a00d030816058003507001031044c1c10018000000510111306000103583c0041300402c8452091291801c240081a1207000c0700c500b015404910340b60052603c4c1c01c203000968200a08200e1814407010541d159200840141c0c020f2080340007055a0032a000300b128401d000c07035405451141c9075a5603100c106414400c2c02d45c1184802c4c4015140204030000d000000d1184a1009903900b02103030049003540c00f1583d001e8441c00c0310740c00307007a15514003081300081c15841c1c40c6030400d40d68441c03600d85440d008a40000c42980070220781c0f80204031481c40180181c500480310403900b5600c0c0d0004541c00b0311414465505504507580400c0141000d00c4540c817649001400445c00c04220141d0b60200e800c00d9010b1501c8510000a015044c02c00c0100451601d03170580140c40e41e200403078401442e041c3c9103480c0c0045984d0002c005030910540350402 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 968533929 1250 968532679 968532701
    0x61203120408090414010b0f030a060302090a0617030717090d0c090b0f040e1507030b1207030c050612010e130204060303020a0c050301020c10020c0708070f1a03070e13 74
    0x100e8450401d8244041203400a900c40740c09030349070620026040c40c1c00c400d814103d41d5a00000c916000b01285d4075800758201400b640c10081d2588404801030780e40502c0e10b0f00c15030807070000055003803800c0d1482c508001030024420150700304226035008503038600302c01810080140320b001ea40742d0b207000209041003d407407806441c800e41144003180200294100610b0018122003203c450815402000300711042c41e00c41c4500ea074130580c40c0d07a10300300f25642143d50281c0390b07050018012140f140480c24124022021584980050b0003d00c00c001c80348841401800e82a502e0034244100071440511752601800303205120003601c40003500c1411800140f50600364003070410702820b0307a0380c58043e6540400840c1190310740f0304410045403034241442a224201481001021595000c41c1c0da84000d50210a42c51800e018114010410550402c402c0b0005d06020020080b40d918140c03204d44140611a0184514202041446515503101ca45000b0001007254003070b03400c0c446042c15200500c015421 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 968535179 1250 968533929 968533957
    0x1020309010e120a030903060e1c0f121806061a04050d24050906061008070e010507170913020313080f0d0501080106051e100e031e0d1106040b061203 66
    0x13548041540c404916000c50340300d41e00a1005940c2d030241c068659070060032054860707004501e03c0c80d22500c10060440d44003081d04000c101c00c02c0c07000c206415174080344820b900c0912580008070411100f03100354070040102d0492011040081c000c0160315104a1140b140b007510035410a0307007400b041e101c0248800000b001180d850b55502020034003c1e14088500703240314050440003d6807410840c4942021440c01c1d0740c0c90035030b07588055094a010400d903001604103c820320400e400100b45844003104a8034220041d511418078204229400065000ba84d107800d0040c17040c0825103101682d48480755502064050700c81100f990404800c1c0507070095000843d003888000540c0407019448507007940c3c0103076074581820b424098a590000003c004151f00861180f01e80c1c0202445052074525a42d401002d03070302c510800c80c001c404041c50640d103491194010726140005c05421080148003500c0d031902800140c0340c113484491080000401190040340035558002550070140110390b000c041003d1 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 968536429 1250 968535179 968535193
    0x1d13111b01060614130312090323070b040f030204051e0f1803040f0e0406020412030f0e12060a090c0f140306010b09030303040615030b010b030a0b0f01020309010e12 73
    0x100d00e50281c00244100d0001c03d2601407408982c0c2c01140c11244600907401c204c201d5149984c0c0d500c00900c0022807420100514040044002107000c002400c0c1d5042c0140c44820f0881e0408401d4209480765200705030440d800c10081007000c080d218505c00304c80d011100043d292343c92458403000084441e40c40d000140a42c8100708482c00b00a00c024003803184200c044400d80181049942e03a84a103000b120866240103e0070842601010326165000344106000342c01c050b602c809280016107500310490120b215001103543e41a03000001c00034400b07013260901250200d1040f072544034400504040c2a60303444145c554240104085004014a04200010b1560380d94244802100c90130326441440790241c400002000044d036416100c2c640d800402852443d16643e80398030041c540182040ca80440c511000030101d030711440e0b0680201195500c680e501d24010042c0320445407010b480b24816444055080d07102d90380041540ea0070f020130b0811410211074980010850031110788028000d10840c8 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 968537679 1250 968536429 968536477
    0xa0f030507180e240607140c031f0c14090f180a0c02010f140105120f0106090f0e0d12110405030a050a2609040207060b0306040507061d1311 62
    0x20140f841000110f184011108003040f8034002130030341c60520381d40007505105403004a81841e02e1040c9124902e000ca0f03196051380004a400c0207182024034100458640002115180c0350040d28026822490030503070b070050981c1c0701d4200d40216241c19009940401c200c0945440b212060112584148104085031078040a41d2001c1c1821840139401542007038000614103005004200000d1100e07070010949a00f0a801c0c4506040d80341226005071250504c071022200d401e2241c54050b254a4070b005c1000440448041d0a641030340c401c00c4215484001c8140ea810b0307101288105a10401d070000c20804624090480d82d40070300d03084a40d05004100301031042120004075009818401c00825400c60762310b160f18403080040100c80d030000001000314450a00d040d90003008030901c1410009900c40007007000c030349040000c69040303d69034130810051100c070360040e521051440b00c00ca00f80c8290140c41010801006c1d02460307060401307403a900700300040c980840a0741c203074903980042500411a00c0c = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 968538929 1250 968537679 968537699
    0xd050d180b0603010f0504110f0616060b09012c0a0b04060e041406150409020a080f0c150c030409091412091005030402010804030c2603010e0604020a0f03050718 71
    0x68980c50f1081d8a80110260600114001d10344a5904250600032220418050102c1204601d5906601c4242040005800048805031106060040400080202c5a801481681503046e04102d1035500314004112040e4415a058101c03d203002c4c441550301e403285507402e005041903102d030b00d902c0340c148100410b501010540040c8203c1c05810b540c01490003240c0d440da01d0380b006640320014000302409000c858107003604002c98842c07010307100c00703c0d076591400e440e13040520014034003a00340c01400d2101d28501c3c00d017801200d400759500f619882c2170844580f0560300d128621890a10507200c5a000040c4000180d0040000c0d64150540344c480e408010b101c0b500e9441510308074419008804c1c1d03503608920038801e503442140d06841c1c1030120340705c540f0140c80d541120841110a44c07944410442d5001e1f00e091810903240c0801c0e81c440c0c6a5042c102c1503503486e07100030030390360080f031051128400003580001c1001c01048507040c0003071152604401141c05c0004e84008109000b03100000096400304 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 968540179 1250 968538929 968538931
    0x60603073524060a0503130b0c1803010b1c0228062604060f0b100309140105060a030b090709050c18090f0c090f09090604030801060206090d050d180b 66
    0x224000340c00d42a0000d145403540b40703880d00c10007030300180180b102408080c0150019a00000c00c28040000c0c4002070340c6684903042c08580c0b410703e070103001c42c0a0100180a000360301c9030900c114000e012181d060004900b8003640031021a1000350345104003020754031450ba045243e600d0040c02c48401c03100c00100c1101111107032048100141560f146c130300c20700800d0034050460307060301d030b010a01030303100c03603d03039901828038514a001d0703581d03540301004011760f1200b0742c22a41120340e84010860440905028110603907080030081e090b410701e020007013603070703500b208040960390701c02c005409a440b000030340341c030300462500003031011444c00080c0030b107070b80d40c0e403025020710b4402650300c4c40c451412000788440248295030070b80000034880049000120f507040a411200d034040c00401c0790001c00c40000b02001b0081d1030106207500810148410705074800001800b6150070300050200313042c13003030641e80e443e00359081f41c40c00c00030041080340344500250003503001c0c090200748a1808250707a080c05482014 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 968541429 1250 968540179 968540191
    0x11040908091e10020706050912030d05070e190f0302100c06050c030a05010b180609030f100e0111310e0415360c0b1912050606030735 59
    0x803c410840d0500c43c070001300d207015070b03006503540b80c101555842800711401c1b01c1e039540c413820700090041c90ba083c3c15a114082c030402c4e003941c400d41c40310282c4051020b55181c0060442403c50442000c0c050288925581e1003101e5050701d441e6a459091001181da100303101a00810f62803c00050020481c0c912000e1402000d080400304040d9a9031048050f41c2d04c541c89400380d4032841000442d0380e610300342c405030100060190594803101d008091440c100b0108413070000105549040e070205044c0f0910070036414000c01c1c40c00d0391810419036842101e042c0745024142641510a400c003d40e4401055490b008000c41c41041d5a241814a40800400b0012031801000c5141410b602c51050348400d00035815240c0c1605d559184411407070000804441c1c000540c0c01d0024203400081141480004001d40300151500260302d2103c0300000b40304411281101c0c4903141444240522a520001240e070004003500301035400c1480e000703880401e030b1920320701c0021406030600307289051a2040c00b002e101e15 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 968542679 1250 968541429 968541439
    0xb0603160e031501180b181008070b0309151b0d1b0c12020d1b05030c07030f060605041a1e04180b100806072d03020d0b0d11040908091e 60
    0x414101c2c5c50b04102e80b080328049500148010300c4007c072000800c002034210710130b074190207115900d031480c007464030303003603520114013101c00004210343c40c5c400f4001640d4941520803184a01e051800f200b405040414490310f000302c100007860242d62042d81c0c00301d800e10400384600c2a02808208003d440304c1a0300b001a074203c4c450094005170144086500844805591101400c144802048500d041003189003119035100800640100f2102000b02d070307005502c40c070030700c200c04240c1349040e03400c0d500d550f808140102d041c00702a86140300e52190b0035100140c151440c00c0b8072a0018104014074400c1d10203141c005260030010318a112040349100c0c2d9042c000c15401c0c40d41d858440700310f0b076800100d108020040d00444081100c0c030384101d11079210343ea5000c0a4a1545500411003042e81103401001c10209500044a000d0342c4010302a10048840464400506070340903100d09810102a103005ca00c510313601c030310139000c010382c0e10255090f0140107001d11080c0c00b110390030a50700c400540c4103d48a0 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 968543929 1250 968542679 968542709
    0x1208030f250504170a03052703011d0d05030708040809030a0606241416020d170d0e1f0b03100f0b04110f0a08100312030b12010b0603160e031501 64
    0x2044000a06017402603250703490918000031641d00c0b40d5501c80401c41590524040203040c03080759024005c0c28001d8940301e4500003490044141035240c80b541110007000d1080620400001c150000d240340e03445904989010b44d0ba05003500000e041c85011440103207400d14011000c2901480c50140a41403134041410300c0181000e40015619200241c1c0124200441045201c02243c031100c20003128500c0540b03400030040856441c40f08022032020307403500c00f12003c24030001c0c40c207140c01503030400601035010381010000b15034984034404500c09008030f107640305c0900b4009078400708080d0340c134610b02040c100840034a0700d020354017814103441c5051203113040039401d00c0d04003180c204030340d9404e0489020a01e045d010400507070b03070140020583c41410003800740010200b0391028060408002654000410701c0100c01040380e80b240c50492202c040e13240004010b103a888283c00c0f20741018000c95107605e0200380c04004c4503404107140785030b5014081d180e64040c0c0c19044040040c142d032000b290400b0782d = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 968545179 1250 968543929 968543969
    0xc171015030b04080f04170105040c05040911090702100e0a05100b1f0203190201090c0e0115030b0d3806060702010507060b100f08011208030f250504 66
    0x402607000c05001e066111000c5400a0500001403015004403016281065500c105200a401715013111480f0b9075121004c10080000048803039020f00380c211000c0140401c15124014456070004070240202d29540c04150365034001c0120464006441400340880c1e04082c01c0e8a48812a00a0454940c800d0840700c4602044038000c042000c00003520351080b00d41d5100c1d03100d0070301142104460944c001003255507440310710004240c144242c280c002040314100ca190603100144c0982c40b20481c00f000c1d000500100340e00d12502d40c003080d028034000c5800880b4600203030140080000081041c200702c007055613010082c0c0c0c110440348243d002d05414401070141045500307501150800d6000a003001070500547c007c502500c2d825000e4840007442648840114000c48070700f4280340c0106011502d20f4003c20340c0720002c103002d03060466184000421550710384d5164000034000a80d01605070002914041c04444404840846030f050f15498022014014020754894019a031b42d8203050803200799 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 968546429 1250 968545179 968545211
    0xf0309030f01140c0a180e0f0a0c1b1e06090c0603020a170702190c1406090f0d0302191208012102150409020f0301050102011401210c1710 61
    0x100c07205500d007514120790340d440c0c02450340da10808580050000d0000c8105d00280c0d100c241b5800362201c4600300d1414189503c1c214445ea600804400c41181000c0001d8413507030b031044410180f9140e040c03055a511485180900c09502a95802030a88004420210078840c1e02c0d000900c845018030b40703c140c0c46860b003c00700d060744580351544012515100c6181c288255a880247e40440a481075401c07202052440ca2a6170142d80c00a481304010f4002c03d0000503202466100c00d088200c031841c1c548840f800221702045410420103116140421600080c503009104290007118226052042040d03640b82114620040355094000108580c00110f85010011f07086004c01c074078a020f01c414902282d082000c140603800c0b455120284c01d10000801c01102c0c00540b940300300c6502103d4880d070500000908540031511801002d8101c00c0042142506610900348600010032407d46108100c0c1850300d000c102c15880705407c0480c440c0042d2012102059280c05240030500c1800f0a480c6c0092441d = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 968547679 1250 968546429 968546441
    0x31b09111b0a03140703050906031515130e090705030f0a0302060105090106021e0f010212190b1c1a0f04050601060206010b0901080a090602070b07110102041401050310080f0309030f01 81
    0x24003281084d041c544154210f04041d00c0018400e02d0b041b40f82001c403002282242d0000e480c81110300c0c0d55201c2040b082c0c64080707169002e608400300307218240804101c50810011243c41540c04d203852042c045940701c3e5050050710040c0c02e000c0c0480f0742c036048407006540c1c2c1c0c00c1c28583c160014050344001040501d403154510b412101c01c0e90041c03103040070541d00491945541030130640140300d08403080000803420300103000b0107102c21403821094a40038a40d00e0b004402900408400b81c40e00c88a4409559100340016200e404580004100c0d03550780fa02c4180707089054100e0022120000800c0010410040c1c1c1314850340c80b0310155030345a6038400c401e0b40d031440c0a01868074024420b0200b5a11035104a100c1030380002c08070000700300000103444034800c030f81c000d180541d4001080b600300140550400140310f1041410380086192a24055a1000c0c07003050310221410004000045403421071280409400780c07000c00e0503580b82255a822580e500e900c240000350090182403013001402e80184114 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 968548929 1250 968547679 968547683
    0x1050c030411010e18100311030313030305070f080301091a150307030c09030611040f061d132309010f050103050c01080c0f040b0a1413031b09111b0a 66
    0x1410142007080b0041d140201c07002d40d4a40c01c00110748401030b10090044d020360043e00b243c0c2142c00200d0640c00d2030810101038210b000e02035401080356400790802248410112a010f00d04151900385610b003669100c0c404020290402c035020001041d145459409a021400d2165070008940c0d09501442142d400c1c0c00003211075000c003817000603000c40c06600308034002c440030b15054180c43c3d240d076180c000319521180f0116005030040741c01d00451084040c41006003146003032400c04801e40c51211384680c09081240c0703001c1c1c040c1c282d120281d200c1540003480e10102c5aa83c03080140d52448454501d20800ca40c0058290f00b000e0719414001100c0c81914183c0e900500903103540c0301e02030300540f840341016000140c0c441c410054442c4c0c400d855000703130014101e14240740e903a030980c1802c020160b0a200c0c07240502d2210803c000710b880460041c003181180e034059100c10f01080300321290151401180d001030711881c100303040c40b0300304030f81e440007003a0b2861444a544814000070403c075650780c001c1800 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 968550179 1250 968548929 968548943
    0x8061005040b06090d12020105010819150b12010f1107020303030a020f0906070b010806060405010b18031002040e01171f2414330715180501050c0304 66
    0x2050005080941180c4800c1c140034110a150240d680041140e4440b00d010603290311030700300d0880a900f80c1c2805a9401020041d0080c800035808a010504503081d801c4001d0a02c61021400750b1040c115030410000305c10001c102010703500400000034003901c0007000d8440e0301440c014912180300e41035010754002a801400543c19a030712040043c0095100c00e1540d02d900794284a07100180d6114070041c041140b1400d00400e495152108880c139048010301802c2c4214245001840034600d04800d64480d40d84000d00c81c0e454a925002290801c060b8410f01c2052500009010800e001d0181c140380c1209e02251144801140c0c0800040d02c502042580c0086181c03c9071043d0400009070b00018010102032680b10b00c10541c0614102203804d2940c031101003550404007208032850500543d02900c49004003042c132584080314245210600224501c4a2040120b460018454001a01c141c8007840640400c003c41b40108410492000f1a804540a6082c0400a0504042d03001564021544499 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 968551429 1250 968550179 968550211
    0x170c0301060906051e1b0106080c010507060b0a1701021b010b01020c060d020f0310031505040b060d15180210050703120b040e010f02031006020703110d05030d09030504050a0806 78
    0xe01100d5076440900d0312035134003003103c0801e440305640030010401c2044483c0400c44600b1641b486c0360a41c2c0c000c1d0320004050f00b01030b17600701d89a40c00c01d0450b0040b95005000152114441b0300007089008150080f402184070101c403a401c0080550090403111010503a040c1d1641c3e21070030382400e80d00365000c403c0c01608000702d0001e5070b090180240c88200d40e000805421301020310b071548400c3e003003218292054412600200180950042c802050f1041c1c2c0d401405075140c030751079540d1103d40c0545458015400942c402060001030b04d810180381c084842c06010f40441d6244000b0700388490103017a8854461041c0402403240104100c031440c683c51380750b10000c00420f00d5070100030b04116203401c0c0c0054460440c268021020300c034605204003401c41c0103813681040034100c0304841d140e030481810340d442131509001188c401e00382e10803210340440b004c1c50490b0080c0382c942e0443c040e089241e40b00e03d0034046204100342e003220151080c2c3c1c205990b0040e40c182e60f40c140680c1e881007607545c144074400c100 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 968552679 1250 968551429 968551439
    0xc050f010b1c0804140a03061503030906110a02120f06010e15030d081518041a1003020a140105120903072121021603030204080601050402041d090c10170c03010609 72
    0x660b0301d09400103086c50f4180b9520748510064914204042004e01c03142c000c18800c154200c0452009005207140c002803200070950b0b01ea43c0c9407031181010f881103003143c40c4c1e0210000c0402600d100c03c94000161400b6580d101111440168140c4240c0b1048070748001ca504142000200c40a20719265502c441d9240c9070100c6508500d00b40801e8180c00038010303884549014200e40d4401c1c0694491380301854650260380240742c00c0c190252000c0700b0800860001c1015989000c0028260340c0b240a4003000308080e0300050b03c0d10f2086080d5604400390420030044403100201c040d002342401610a510203d4196045002d07545030051882c2c0840c050701d45c10f02d841c7c240d0031001401a0006640180342001c103c10805e841c0540c2c01c01100000d4000905001002040c80441e004100540e0f040d41400c1c00d0003c114120656040700110200d940000500799000412001c0320481d0080d10080594103000c0004040000102d420141c5003100c2020901e141200f50407039040f00c8031942d130b01021034100 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 968553929 1250 968552679 968552699
    0x6090a0c05090621060303040b0d02030c070203070303110c030705151303050609010603020a140306060904050c060d050403030c08040512070311010204080102120705090d060b010c050f010b1c0804 86
    0x20340d1540401506001050694881d60020145040003a0a1440200210a86080c00040100003034000d800901c010840703c5030807403d440561300891009a10781d40d80c1c000c21111030188900195052060b0301d40001815001403110b02c44ca001d59041e00c000c04181402c0c140d50f2415403003003a401100d01240840814401001b40070300c0c0b800c02000348a095501c0d00d4851800c0b00a0760307002c5030740c1d549840400c1103140ca802440c00070140400290960294900081d40764003009100900564000300080c0c1040414020340707000c2d280046c2071036116004d070400c2c240101400c5401710301003880c00b000042900c0c0074214280c440c0364090000e141180820f07150f41c803941c01080d400c40c1404214450307a040f83ca800e001030000b03003480400050b200c1c80207401040d080c40c40078280c0d9050100412100715107440c0c200150410a070489400700740c0448190040b14100344489001c1c0c402d00034140c0403c086001074201d850035000407980c1240b2210203280b0a080d1412800004001c448104410409a040 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 968555179 1250 968553929 968553941
    0xa020304231905070602100e0304060f140a0206061216090b01110109080c070b0f040b0a0525112b060b120a1a13110310060b070c09020306090a 63
    0x148425148084801d0701c107894080d01090b0210b805802404051141980c1041030400c441a070342401c1c08080d41301d12840792648107601520080005503c02500c1407402102034111842000c50b07100d6607602c3c0d0090094883e0740c1039860702d10030b400898000d00303035440c00602450400d8030500b500e842203213844000710080c6902031489060000e41d410301c0206010038411507041d14040c4c0048c6988034511007016051100399001300c90900f00510500c81c109015105460945083c2ca0f5001d954041111050342c00c2c0c001c03c00c810702c00c80c40a8158161100c60440350703400452160f40c0082443d00130804025028908046040700b44500181900340768941d1403000810600a4200007941d0320b544000c1141d03094100d00c6107029a00c42000c100c20409100300c0700d44591070745140d021107070419242c60014000244006403c600326810b500c10542d0f400c1c803607800c03501950b030007c1208551780c001160007034200320402e8074a0111404000f8008100d4021640f16100080254840d84c1d40d51842c1c20042030 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 968556429 1250 968555179 968555243
    0x50d0f09080c042706050a0f0c17190e1c030501060e010315080706050307020c0904020603010e041b0611060a090f0b0901110d02040305060601020c01050421150608060a020304 77
    0x592000c11302d00c048101c9842c604403400f81c04049840d00d0425001c0082d15004d090104a191416442810341980300850500044040300038002e292243d001003e64522039111800e41c1c580f50034288105400c00240500c10409c50ae031a007205000c4841013582150030074030030079000c07500310040300c0c14940c800da00c074102490480c00c0d00580c0c0c5d13403642c58052400301280c22040c0490702c0002808034003034041003642501c1c01e0854081c401c500c0c00c0d0f40410100d02041c4501c1030300114031008102000f1102d1021358840a294844040807035480100800040c842c0003183e40500480000c54120341850254040d17082e000395850550180580c0c43c1c4001d0240100001c0c0705559800c00c00030307400c0b5018010081801c11420250700c8504606260341012406486581958446128903400d81d800c1816074044a40e0110407846030424801040603120940c24024045041010040e00c0c0106550220080e1410703503049800c5542d5030803030002284429500900301008192220341c00d14010911040811 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 968557679 1250 968556429 968556461
    0xf010909030c08032a0405031902010201090b0c03010f062c0d080a0903150516180b22060f020a110105071b060806040207080909070e030a050d0f09080c04 68
    0x10b41d254662a40e1900256035154209000400084160000301d1800003852018034105207400d140c00006680c503079007941040c1d800c42da210400010f682c000e501c03071440160400c0140040d494a0840c840e070300d600c01d001e10072072890665008912a803048204c0c0011030600d5960092505c5d00d881503202000e40c01d81801c0d80105465900c1001038a104082d09815045840329011682140360160340c081425240d803a1081c41c0030204076800110140030441c04071503044c071003500c0b942d641801d40b5020080e040b00c101f84500280460040e003a00490500003000b40003034285440c2c548130700315601d00a0041c62070042c0d1103442031030045000c02d4007030130701100141001803801c00035644105800e103a0181e0340c4400580ca4104004075a0040803503640f0010850341107152003499510380c1d5083c0a101110343c09482103c0016022602071450962200002411039030781c0c3c0c042c1c1ca020781e6a28602c40c28103002991011424003264002c0c5040340540ba01030b409400e0380028007007030000a02c000c0007104161 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 968558929 1250 968557679 968557697
    0xc0a051c1202010902040c030219030e010b120c030118051c17090109020f2209060902331306052206020d0201050121031d09130212060f01090903 64
    0x3010007a40707194088442d0004603080400d40100000c070b0f490401c014082c5401000200e40740031300c4459100046006040000c4c15140300d035065401401002c0240d500015003c0c45101402400200e10481d141d00314001d0050030b0310401c03410044000c4803001852030388194040e20140c10008020382c41c8011a1800b0068204004440d6804403401d803120002c50b59144030460650a20008000075070409a808004889c0e07210242000001d4000c0a00411a40d450940b0104540d0f074020501894005102d1100380b042c2c02a0004e903610010900c0c034444010303a210002c00080030003a6600c9155031030403c51240e140c048181d84c10b5004ea00c00e006041c10900c4410b103044074842118000c3c1286a00400b40a000c09a010f821a10183c0128000c4000d441282c45460601e80780080880c2e030500d0100c810071203032000c00302c0c041500200c0580c00840b9500b003103545c14100c40d160101500887d0304131801c412030340c18651110b0701900c543c42200c030204010300801c101a0026541c2d540700b80303490409 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 968560179 1250 968558929 968558933
    0x4060503041e080904050f0610051606061e080a0f0b0402030a050d03021803030c10090302070e0a0c080606090904110f0402040e010509010b0a020c040c050d0e0a0506090c0a051c 78
    0x580c002c1d10001c0b5214640840c01d00000d040610581d68005c4c404d2600d403c0605140c000240c06170901c491010400c600041c0817074181c0c00610003d0f01d965407060090001c01d442e480310503004032541c1181c040c0445100d4000640d64400a4001001038004540c000310261302d40314003404000003403050360103101e03202419000410800100d04004240c1c1e500580b200164130f102100707080514035047c421390080c0030340207854001007002c480710f9000b06000510402d440c507040e42071500d40d0707004128100c52481000300849a5410509504070640e03540b405c550340d113078204000c50040c010500c0d04107000c04000303800a844900015441100213003207a582152120004050340d01503046124001c005100400950405615a6001d0300500c1d020070308200854400035950404901c20a00c5203498407082e04c0403500940c200c9007a4801500180074905011603140d545207444002200c13140301d0080002d031402c4010905080160340100b40c0c180c0303140781c01c0410142c4044565004070402c0780c0508000 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 968561429 1250 968560179 968560223
    0x2011b0206270102150a0f1509060e0703022107110109030c02031605031c030623130203010b0414210f07060c0b07031a06031513020c030406050304 65
    0x1c0710881410510b00842101e0342d40700c802500d441042c15540035001070010b00300c080401540c000c41d0494000f42c40c0640c07500010281c0301880340e0a9a44c50503030004107007558035400000a4500c069181002a11400d404a003203118076096080300032043c10700c41c1d0700002c0c101c1946403c40c0ca94a4042c00741c45025074a1421610300503030803004240a6158142181020300c00c3c82030900100c00440307030407450400440e45840c03910b174000d5a203952051943c503c49003e44d00480c09401c1e0100e031940340345e80c0d102e40341d1100f481c0744021512801560b000c51043c0d00c1070717000301e9050720060751280e800c192419010064040c86085c0340b981c488000500e61180c0700503034403a58a07035001c0c2c100524003588000d4010703080c68059080501004082d10340315011604d003900003600488140340010382c102010891000340005d00d248194446400418403022a01001c584803001c04202c581c00c04000025490104a110704010740c4007607002440100580ba0082002c0c6601a000b4400c2400c0c5144a09a003e = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 968562679 1250 968561429 968561437
    0x90509070e0301140a0e061e060603070201061d040515061f0e06070c15020a05030405210a08130f03050a020f060705030a02031c02031b031b1b160e0402011b0206 71
    0x2510750340c6d400040024104006035070308800301c5010900211a0070001322844000109240d00400d400000f14411318802d40c0094002c00c1040f0042c41e1081492020252081d41907c003525248030380147e8440e0f05d180c0e00e84050084000902c00142c40354070ba01c0301c510007000e00c8002410701452a44114590311000c004101192045d074000c0c400c14240014528000310319014101198018a0b5043c0002c0d0000215001d40d00215030007000d119400407803401f00d0890440700721300b500804400381d08002c01d0314090003009440540401c0b1003520fa12980840c00580e22014065a000030891340140c00d000d0b21800d02d0040c0542242d00e0000181c03640342c40d6500c620b6003040180e10018003001410182d4103003001e0400c40c0c40c020b602d142000081c00110001500c2442e29040000004c00e403d0b10004036048856000618410748580c1090081c0920021541c130b082e10500078a480c540720910040c00c04815a001806445040d46468004458141307420b4101c640900c204a40320001d6541d01020f4 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 968563929 1250 968562679 968562691
    0xf0306332703050105090604030903020915040c020d0f0528020109020d03050d15150e13090b0114040603080f0c0c04050a0519110d050c04031a070807090509070e030114 74
    0x102181d070310310710b0858211a0000e11040d4160014024000001d90101c00c003070842c1e4045462549a4aa2404941c800d443c40341580341c0c840c1c60005140030058000c9404030200d01d05440d103548108400d401034405100b0009103201d103503842c040c10001c150003014021000300040c8000500070015a021440401c205c072010350101c0c402264420a130f04003402404104110b01d60041801d0703182a410304202901e40820000f8171942ca00c01e030100d6128203010f0758285a2800741801740e200320342072010f62101b081c0900159038640c02c210304481e007803c0c0034100440c1e92012910b490f00103260a841030a40100419240d54062402000c0e141d903214091940600001da000080074140310300c038440c82910400f118450241015088a03200d04840281c1d9400e0842c2c0401280d50390710001168800d00c584e407c02405444040c0343c81101d002c0341d6403454400c1c0501e480c3c040d055180d4031020b54046515209040c1e010340020002070305684601c00d480c6d1011000750000c540700d02d000104461880007143c1d0 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 968565179 1250 968563929 968563997
    0x3122107050c1c0f081f0b0904050f15190915090c1103041206021c0606080f060a05060705032814090303160c03050a030f030633 57
    0x7208040414460f03e0301d0039244281890b418003400c0c1000d084940c0340c0204105000070b880004141c1b441511117401c00b4644924400da4098076201a00b845d60811018180245c2c45e003c0002d1030301c03500e280e01c2400b401d80b800b0210002d568417401c02415601b40b841c0d40751818640c6c00009a03215442c0940741840f499070030350401c82c50401188204079202040c1c100b00300b0dc06d010780da22540c00003000300c40682d0b0400018258002711030800030003911074500b50f9202c1a43e5401c200c6000030762640a803054903884c0e82d030103c0d00c4d00c802a94464440c01500d02c82e50200c46c20700d003007085e131800300010040707984540103480c2403800356103444010340108103042006111a10780f480546600410780340401071007003401810807000074003080d40c07400b500514a00c0024804528005d02844084e110700542e0b11108a9964040520340103000340881468400860b0603c6004102e03008506a142407001c018441691b84032601d038540400c41d812444107100703002c0a20104404141c2c80c840d00030303049004000c = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 968566429 1250 968565179 968565187
    0x70203030d0e2a0a06050c0111130305160b0909150924012a03050715020901090b090105030f071b110a080609061f0e0109090615050312210705 63
    0x74483d02003e05040644400c084202c0c4107400b155500c11103002174580f6880e0458550322458140c9004224070501d41062140102d102a11030030a0a00c0324280e902c41c0003075031591242c07203d50301d4000c1064010030005038014001000f15007047c03500c10b03903c661a1000e6841012141012805054041e12402098030fa650503551401180489081032070f00c083c603018200004880316401b258001303a0003114080c114860380342c00e0502c102d003680d01c2c103908180801124500d0a001400942c4a50301c01030125079070203000203901e440c01c02950f801c1d04060b11514a07503504c640034500340440c01000ca000f40502002c031598142140402002007500ca1035590341d122443d001004200d14403540041c210f139020074100000e048002c22100d801c801203407541030344601c000b0001e030808d040ea900705511840d900d100003c0e070041141c22141003140120020031500460a15541c40c480705030060f80c1c1c2503409080340420721200305004090008400402500e4403038860324030786608005031010000904042 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 968567679 1250 968566429 968566453
    0xb0f030a110d050f1513050c090306010f090506030c18070909050901020901023a050c030a05030a140c031902071a06030709050118020f0d0e1c09030803010b070203030d0e 75
    0x200d900317070441c0c0f030080000c41400002c00000d506405507100301041d981c983c00400c0050700b04505440d802c000c02000d9541790340c1c46c5c0401c11903441c050701c0b4480d41607040c00003060300c5041c041602490084003410000c44181e0704940b0442014010740000f04010101c2e13000a07220803a84200d60140c5441d900150751050f1a4000a1500d06034030b040c3e104841c0c007182c04000601000c00d1180e2103580654410141008542c015a507034010040c415229000024000020a5100c0000c61042c1c08182c0104001c80c4040014000040704840c407a4841c0700030004a0f620400c44002c556691420090245c50031132a5644c00d04101f0300e801902000740d542d101804000d140030301107400503040c01c00040000358504039040110090a8030005585940000c9004d59100c41d9001c17140d040302150700a22462076000031076680e40300141c1c22031890040700d0143c426207500c00c1c03000c40112608014a03c2c110707400e1803404080d40c0d00c4041c00301c3c0d052000308410000304080c0e00032040490b24040c007034025000c40d0 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 968568929 1250 968567679 968567701
    0xb0c09040c02061b030114100c050102120601201e1603081330060207050f0a0c140102070315061e05040b180708072007030501150b0f030a110d05 64
    0xd00c41000c4000320a10040c0300e545058503401201e1f040c1201c07850350001c2d0941c4140c2d480418628041c00d154000101c51407981c9484030b407540100300a90b20400004d00c0c141c4400302d50364441c1e800b800b858202529070303503800b0380780c644c541c1a1804079000c1e01c00304e90860041c0d06100e81c0980c42100d02c0c500200d40307603500d040b0b00c2070488004d01e114281441018500700c0322480d20400c040e0022811110100c440741804417075410b5481c103503030000456401e0010103a0345559040a040125900000200c02264644170f2881c540e040d5401a00140405420744e501e2040782c0e20111485024155150030000703140c40c042401314070142501110701c00190410052005a450340c8030002c1c003907804030040501c049000410301d68405503901e0a5061901d858004540c403480d00038140814042005680040d04400b10b010342c2101d108800800c00c9052449058056051510400e2804039007030005403104030300c0c64011640042c404ca40051001440c52603007039181c1010901c0420030380d41d0401c0260103220 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 968570179 1250 968568929 968568961
    0xa06021509010209010801061209060501031a091605010806060d0606080103031215030308090c030d120612050628050106090509070212160c0b0d0506010801061b0b0c09040c0206 78
    0x200780e009602d81007041c0c00280c9100e0040c031881042101c000344445641500d41c1c8641d01c2240d2200307090000b569030b030419055a101d802c001e51a242c05403404a01d5880c00041c0b00c3d0401042040b40c40591461b050054502c503038000d00181e04600c0030800d0307a490300f200e485203c0140007207454092065046090043c20300460390303400d416052a01408009032900c140955007100c1d0325192000182e511082f20034200b4482e000c4207505845214620300c0c40395004030154241c10030200c0300f0412507030369101a021882e034074003015059400c6480410ba4074050f800c8200d032110504401505000f41c0d0f01d0351101201c0c400da02c50b00c00104101c00a10041c94030030109038000031544014100100210340c401080d20500d0708940d0f2024000c80d03804100a0302c00241001840020401a120f01c04404008081d01d0222400360008101c40001726109000741180d101c1c00846007241e0b406200340c0d50b2801060b44010340280900d48040c000303000075642c0d602494078103003401d902610319800c00c507154090344d000c = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 968571429 1250 968570179 968570191
    0x12010906030b0c12010e1f08060714030c0f09030304080d08010314010e1002130803030a02040905160804030c1a04051b0402040b16020a0f080606031504110405040309050a060215 78
    0x3001c205130407204041c3c07a03e140c150b400744c10501c103907a1111207070035000da81c8100707600fa402200d451001585020200e1400e11650154481d040252460f460003c024802181c66603149442446501e601c1c84421001e4106440b015003203e14140c1c54440c400d2505890408400010303502c1001441000319603866070302a000080002d01c4441c0f24140c803503803940440c8400c50031560340880c0c003e8000070b0a0020300300902d20f981c2600c0e601d04110480e031002c0c1d4818001d5060365070504011810b50000b0602c403119029048d40c030030582e40c40740d640c111010100f000007510105050100709241400041c3c010340940c1c8140010415030b6074004001c07104d8580d40c2d41c21032045205000801002c40c0c0501110305440c05078070300c40304c050024800506c40d100306800000c40702c01c0840c2c02042c0703940001541e50040c4070880848900200403081c82c14154801c0760300800031801d254150080c0e0030150041758005204c1d08010010326160800b150000c40b80b0350065006900441081c85490401c580f4103070422 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 968572679 1250 968571429 968571451
    0x901050717060f0f060417070314060f0f130602030708060a0f14060d061e06120204120602070f0501021c050603070609031401020918073b0612010906030b 68
    0xc0342503070000300489004000c1600841a100780102145e856008450192841002c1001c03905d1405c0403050b40d9007600d0004039a00e071018500c03441c00c50300c0000c14501c0780f5070010400301b25a0707450659840800c40a007941c0d6044407503e62200004259001541c0306980350b541e42021403030104200001381000d0b41c02603141d098031075418012203c01080d1a84182400e0350000c0e50340b00c070416414004c0c01d0030f40c001a0040700402e05003842c004090303940c4c5c080311017507601c405001c044255a03400702d1080b445008048031014000000080e129009401c04500490002141c2c483d42d4039010b00b640d0050040c1410780c44018022010315666200301900810150000c02c007490406030040c200c60b010340006072142c1740300c2202c8003030b824003501264440e400140c10076840c0300d030800c00d0340b90716081520114049940490000a9640300c2c03804446400e003104200301d404001c0703810b00e09807070b800e155450390406020010314100520700320041d8001c04521500003202491428401c10b44107001e0a03400d025 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 968573929 1250 968572679 968572681
    0x907031a0f39180d050c0f031005010f0509070807020309130b0907051b070e060105090a1e030b06010f0210021305041107050712080a14071b0e01141810030203060901050717 76
    0x400c01c001125884040142d981700b071801f079050002071401c0181080c00b182c940c03c1c01e0021400d9031403c0041c104550b401d0340d1580490311854000d40744103004843e0140164010300070380150f0714208903d82102d0031a54400562400c85034041207000501722a150086400080c0d054080041807111a40e880845805003071080e05000741c034005010003034100c170304012010424020310340e0360002007030051020003030f0700400006998030a4090300407480b007540c0d04040d000008013a1350140d810146030a607580c0c050a61000c16128a0300290041c900d101500b28136110045456107403403140a00c0c0245011341941c8500d00340c6030161900c12a90800b080c120781480c0d980c000540c2140a03074100c84414100381647c15610240d200050040b1140078103010358503142880c1492000c03011100380e804030440001e090381c83e14800100e1089006613140c012036000100c2140f4207120720855013000305800c45411043e60b91700000e181120607104460281d42d0b500501c030721180c00c150341080c0ba461001d007100301 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 968575179 1250 968573929 968573933
    0x8130308072106210510090501060b040305010b010e04050705070b04032a15020a0c1203020f120403090503160905060402041203050a030c090e06090a0e060907031a0f39180d 76
    0x180c14110b08420006d903105c51200d420010203400c02005061442c504d551620340d203041981c041c0040380400c0e07000c070706c2080d88004103040902800b48165042e4035164603103849555681c008800040c0180c0c100300030f15016190b401450458083e40e8400301400e0244e10700c04d41005605a042c41001c580454030410024406541240e40000b15070741100c0d00f061300a010410980182c4119506548005800038280e02c641c1c4100300e0440c0102d00940d140480c882d10780081c1555240d44100300361210410304010481c00041c0d4101a501c4030001d04003500389562280106181311110b03c045005ca0700110360048520b80c5071041409510251400d09507151800128044200e00902040d0081302c0e4440013035144545034003c808046c0020044400604c2c1410f01c5984803800c0780030440d190080500f00006007003c802480e0301400c0e056074005d003162100c0c0c0ba4402c0ca030b0700008a100748580a0244045103410f80703101a6104000011200c0d501c5034000c0342c05810144e000c0281d4403a503209041100 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 968576429 1250 968575179 968575183
    0x411131e11040609180b040216051c0203030610030b0306040c0312030606090b300a0b0603060310150305030705011505010203072013062301081303080721062105 71
    0x40340c004800c0c520800105c2401d80d005400d040b0b100c65003050002034400451801e0504400015001c1c40c1541e881c0180500342040f2000030280300001a802800801c41c20f1801382142c020b60050381c10300081c14030203100803a040500454040c1c030b02c40e40c40a010828032a02e44c80b07400e0b10701240d00d0200521410164050010480d42c0a04801140301140241002d006094451903507254014948107400d0031003d05640e800c4212800358106080a00181311800c004055030701401c401030140030000c000c00e07890b10040c1040a18a1603140701c0081c0000400d5060004102c06800b40d400400d42200000b0030101100301039014604640c401c010050229152842941408030310001c400840d1b4400000030b43d913010b54046c04d561032454a40000b400c2c2544400700500c0a5080340c0d00b684128075000155101c010456643c42100b0a1511000010344500038450380302c4180d042c6944482c0e0610340c8020f030303100f45100040702c056403140240400001440311301100286505080d40750001d5540b81c0b9 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 968577679 1250 968576429 968576447
    0x1081006080c0a05220f05031204030f23100b1020010b0a060905040b0616030e03031908060307090606170604060b030403081f0506030411131e110406 66
    0x225041c0030030060715092052084441c52080f81d4241005c100e400c60101c40e2200701c0b031082c032100c8081c1540c001040d085c04609544c4110405080d182841c1ca562110040c0f681c41d88011514002c21580e40ba510038584a4100303208103910000b010904441081d88044880c0d0001045c41a01800020750380a94008024079107032006025850760b41840d442c1142c0940190100d1651040d10008003049441c3e0141c4080110741c0700b22000c3c003c111300b40050000601c03901d03101d030800c800d2045061001c40d0140003805180c86000e4112842c0104000303441081700d1a8000000014070054103001c0c00d03150400030800030f0440d0043c09c2007083d1038044e002d080340c100c18881038500c40c86000000d00c83e641d99440100100010a0703450b69a00d000d00e80148000b400310784064000d2800b018155400300c0510034401524009401e051660301c0b9619052201003071236901d01d501807801e0481003140c0896004507003110701f440303d042c0c24400107010103500b0f846404400d0580e0100a11082001580c010700345 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 968578929 1250 968577679 968577691
    0xa06020f0f03011d240f01091503090303140c040506180904120e0118061b0209010303082d07051602030d080114040510051915020a02150a090311040209040e01020304020108100608 79
    0x2e043c0c1c00c400e001038230004420b40c0203c01c0e032600c605411904c660181c1143c80198400d58040061640005200c40807800a031580c40c00f06905200a20182c144000208440c10744410602c0c03440d10b501001543c50352040710704403080c07040c66040b02840d0390040e011400d101805d00f0005200b0100c54440420000544112402c0061343c69112281503084c0f02c98424003134002d02680030940c1c507410301520648055a502d5204a80130740e5149240c900504c54807208540c04003030701000d4488200440ea15004101003030304905000f00c0450059404210010200040d511100301940c5400b030844c0074601c0aa498500a23420030080050039411100d169054074021101c00d07500340303000c11070b030450200181c00446081c40c0e0340b20200302854000510349545842100d07000c0481e0790f4610a0700582c09003118600200324004030500c000764807019440c02d0000040e100505148100d00020191240c01007540100d035800418001035503070164030594844c041e01c0700c1c124240c0c60040000c002500003884 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 968580179 1250 968578929 968578939
    0x6010e09060f09040501051f1211130c0210060b1608071106072604142107030b0a0b0d022d0409110a0f05030a06020f0f03011d24 57
    0x3a10700d54501c115440d1014028080d040d01d071516180c034500801c408c0d501181c01d030005040300960451416810300964025212201c1c008001ea9901c2038000110100141e11680e1104030a030206610310542030309032406e034000c00205500d060020110b801036000854042402c1010442d000d200c0ba80d910a07195001481e01e68072000d508298202c0c1552410701c0b0380c8104005140345c240100d03c00295400101000c4a4942e0207550280002c5449648141440740c82c1a0078036038417038030780f580d0360a903044c0801c144103144480c2c14540ba41003c1c09908102e44005414043c4000030109104603401e4070016a040904c1c010a600000e100045200c400e24000030b6012883e0417100c400b035040a8010400760092240c03240901c3d00f000d550322482d08007801103441120000d001a2904a580111a40a00a45080076998131000040e6026071403402e03407900d0800c41218031241000080d402007103400c511003050516011518007101000d001035810742e020840d150190350900000f28640481121 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 968581429 1250 968580179 968580181
    0x90f161d010c1b1503060509070806010804170a200a03090308031302040504080409052a130e01151404080706030506121509190b0604230103050a061406010e09 70
    0x29003a48964005040b07028a01d100e0f0400161000350b02295040404c02914180031303968a0303005000303100744100c030610300140480021509c1c650264183d036421500440c80c0c014040081070140b503450b440704000c180051010702404480b00381e540c128058201204018040b24003607074038010411007140c00b015001500000c00305100d2116101228509503014005002d1454182406045034115218045110b03050100140e0400d08102110f02c440c1c0142c2c61283e5862072802072001e031908500b84c0c440d00800f00e482c02044496103500202d0090910000c0885d0303140082200918240105e400101424020302c4141700e45007001c142c0c5c20560355580303000601952030b2030015000004c0340c0c820301500c0c0101038074440f03180c5803107180610070389a90089500b0140c2c80d80302e0307a208044141e0301908072011840854464501030300445c0c047c08000703004c00c02107040d00704012020107081c0d00031511035210070500d604000c1580290b100040319010004054a85440041c0940300707005032161050550b10 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 968582679 1250 968581429 968581433
    0x30307110604031509030f03151503022701090623090a170c0a0f05010c060f021909090f050c0307030b030f010207081b01050412030218090f161d010c 66
    0x4010b880046420580440401c1405112503000707054550040e400264032010324020f09010340911030880c0b20103030072181518504003000600121103001b0780c1c1015020403983d801405501d8003884000d100c0982000040348031400501240e00a07400700c0140b01951640100c030300c401c505c0446d00140152041d503910386d840400540d0130811500300300c481910710051445c003203000041301e0341715420a5440c0c0403041d4880d110700c8510403941c8103181c005048058400700240755500a0440200b00050240c181000c1050060000c003080038641c00051003060108884070441c002c0145903411000104200c0c00d00800c075451612008100d00140b503100d030040b03840c645041044010419409000b1515101c9901e4507006907031007a051450310301d10407880c05c0a40001841086c0c003c03540552401610f24841034260040c0d040b060101404201080810100f80c1b02c64000d9845808900031032a542e140c455500203110794640606420003020841c0082010080d4100184500007400c158044d07040034 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 968583929 1250 968582679 968582689
    0x231e01062703110906011b02061305221b08010b031803030a0209030f0d08010e041505010b031f05010203040909050c06040b0703111f02030a090f050c040608030903030711 75
    0x40c10a00308046101c0600005104411040d00066201190702c094140c0320356004445c10302440c0c0074810780c0d094980c8000300600d03041e00104a101c114200130b81a20b581c500000b40520303d800e075290780300020742e00c444491403501e100309038850079452090720303030241d42e40c0700101066014002d031681c0381e20010110345000c01250f800f51695070001c2c1102e82d00d18000c050341d0003079041401c440f80a0b1040c0e00c500720000c00042040320411050b40d81d402031503803800b1203001120f10007510980d0881c6003c44c2e074401c2021940a0680a040c0c4500c03403980da03061805816040310f29100c0d25100c941c03c209001e21007680c3c003108607800c070b51003d14007050024443c24500d0425291402c015407040c40040c0000d0b48502c0407014040088c013a0b02d0f1400340c1c1501d44c208589807085824002001c0b005400d48041c022001c2d40616000181c54400080c881c015554440b180c01e54210151015071155810300c1d5140790500410020384850740203142007814403804281d99004400d80242015402c04a8240d03540312 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 968585179 1250 968583929 968583977
    0x203030904090302010615021b010f110d0801050a051903031d040e1005090732090f0a05240d1a1006030b0a12021012231e0106 56
    0x401c10840703000c2c079240190017012030b07100748505914001003800d07601c3d001081c0000d00d00e40b1105550b035071504d0040112803802403010a8414420300489004010b681040710480c1400c4548a50f40a9410300c01040064a400d51085204103029a21400b0a41010a1820813203a040c10014140307032003011401581d213000c076506908070b4544011400c4800000410749250400400d00300255202c0d00c4041d51030300e94a000c4e80c2d0310b5200e0484017261076250080460510200c400c44030f9801c59007540042c04c07100e41650241d4480c0c07050014054006654480c1c2030708501842800318019219a0320294585000783c10503226507040001d480901000d40c18420198003c1d500328000b0f031600300c0c40940440790b80d0042000191a02540c880c0c0f50403c4081c12007500d512911240c0724500790350802410241d030803004020458220390398070aa0b403050080c1c001e6045003580c25040021418001000184000c02d840680006440c1d60700440c4c0c0c4054000d4152400c40c0b608540d0382d03050303140007591500 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 968586429 1250 968585179 968585197
    0x22020622050411030f0601020a0c06110a08030708251209050c0603091b030a0f060509100204140f040b01050316052203020108180714010306080d05041e031e020303 72
    0x41448070b02e10182c050803004510175413801c6024000341c0c9078140120fa03a130403284001041169401d50a00181d40255a0000c50388071100440c1c000c141260745082d0b0541003071380e07040d0200d005078080c0071740d070807103100000d84a0043c65607400340200722034001004140c80110400c0c110340d031485031006011060280340a0190007074034003aa40d00b030412640ea550900309484d070110030407004001e0510b02c0c020400c6600a131b0000b800700b0255034141c450000400018005d001203100e00b00c40ba010400090010f480100b02e03030b0307840c07040260045003400b01410083c43c0341885603203451780202941ea0003005603034110401c031030394030601501000c0a46075481244510703410403070680014180b403188801e5420a6901c01e0f40c1c2c11100780c5800c0c4000da107592801449402347e4000301024000000301c048080e000c180c05242c04190540c0d148990740c14401c0115080000480000c0d01340b0410f40c4041c4c5d624102440c03401a40125403540c0c0f16440031300c80104480307028131041b0f10075406540e400c00995050340e03 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 968587679 1250 968586429 968586431
    0xb0d0f0204080610080f0d08060f0a060503090709050c160507030b01030605100e06100e270702060702030a020c090c09120601031e0c121403070b220206220504 70
    0xa03201c501095490f0700031035801c00d4502d5001d201144149000c01d1503018544800010003441c4450042500e030b12000920050700300208801507550382d5540b14080e0001d2030f09403034182c8d07203051142503642441d155401011105052030b0611840800f554112140764a07546622284c4924078600141000c3c92176102400c890304050000c0140103040c0e00c80e900070003a02c0c030120202d40e901c020000411004903840d0342c1c400360034800203503228002c0300d0b1040140d030f000b400c40f02c3c25540d248a50704c01403614001042a90015410004010f404001c1c01e0b802088900003581080c610480095682440c10181303409540040007055070240e61105903030b04441c00070200910b40072465070450303490f042480f069030910f040240c0c0303661250300500c201000035045040341d800d5904000c62030600c8a50443d04440c00401c03060200e801c0c3c041070020f0060217204021030003503810448038407858000300a243c4a09800152100b000580c0d841003154104c1d008071904032201c0c032060700c06001918440d4012a081 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 968588929 1250 968587679 968587687
    0x61d2b0203210a1413060b03010b0d050a0b070e090a0905100c0320030c09120705180a060506480706031802030d050c0a08070f030e040c02070b0d0f02 66
    0x704824034070a110b0001c00c0020442444e0311000c0001e624019260b8003c9850041110b0001c1101d5800c07094900b0380c05030000c00c80f800800080b90070260316102c2560a508100c0d624401c11200104007501f003002407820340d08115240d4006020340d10081d0401451941d174406d01c00400c507040c0600c0d181400f0401082141d02c11484014000c0c08552500203850140d0826004241000200340ca004e0070303440303180c641840b2100003071110505420b400a0214450702e0300024281d52203010140000c0218001600181481070721b00341030300ca00b9000f140c4246000d010502da004a107011006688545a096210044074480750300c3c174000da0030900454105a10600c0350b8002c03400943c4c0c41c2210030303d0b5010420a4907030b101c850a03000c03a07088025410b070810080009514491806003d22003500410744070321a526a4a071110381e8042e020884115500c00e40300000c0c140c000020076044642500c0a0083c0b0b2000700c802521100e0038055040208404030707018001800c1c0758003010340140e01e00421996 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 968590179 1250 968588929 968588977
    0x2060a0809070e0c0307080a1b050d0e0a06023a09110a060815010306030812100e040506060901060206100e07050c060a1d070b18010302070807061d2b0203 68
    0x1055004646083c046060704c00030030400620383c841c29003609c10101c80c9002100d046076045815910624204d58401e0b220000b40d82caa1030103011913190144944030050780c031100c002c1c6804d440300040c074041c045040c10380e20010b80071000b85142e0000d501180ca0000d0120b400345805d45913507806c440026000843c0c0100030820b1a00191018016641d034a0344000c2c0400c580011416129140070080852006100504000d0510402180c100030040d40d404d661544540000040060488055455078804c105100942c00c6c00c1312102c0c00b629a80c4082c0a0b28540003405850700d018512418200d1607600c000600000d00ca03c0aa840f140c0001080c5c80d00b50078051b00d460044c09900200d00107401e48901000041400003c40f4401c40e01c0703070340815017401410402050b0309100c40c070f45075040c0364007049400700041d0383c1c84c014600c01c1d1040500040d07580f46112251900c003442c81c9044003a0340304121082d2940240c1940704081141c1ea800f01c1c4c43d0340b0170342c10100e00710300510955044104541283c005 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 968591429 1250 968590179 968590201
    0x41703040501170103050a24020d0b090612101d10020405010813030509150c0109060605040b010c170d0b0a0617010b0f04350a0302060717060d1b080307020112050402060a0809070e 79
    0xbc0b03000b008503252600d9450340b200b04410310345074400203101c69120103840001c0d244180c0004404030601403421800700181c02c4924200015120100035065001034140071640e00000300e1604424038121842808000b03503409441480b4007029248031305030307019980c402500030320111200d07401d820000b232120ba809440c1442c040c081c60301402d84541e0034809000050752281d402e140e0847d80100b401228040c0c10619090a81c0c02a1007402e6031948070408015151550442d110003440c40703640d40100500400e100019102c81070300051480c0204000700707090b0714040c206417000d03142210243e58502075401c1408640c054001d400200d82103101d403404404075000309441480601a80070b5850716641e48000700d8030340e0005110112204110380105015041a90500201902c00e80c90000a40c1801c4514002c101c80d80d1f00804459100054050440d42d10910080200e1800c2006100302e003415030000e40a4003d050305041040a5203001440b1000c080080400400e905070010740e46080084440c1c2c = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 968592679 1250 968591429 968591441
    0x4060f0621020909040b041403032e030201090506090f040501030501021b030a0c03030911041506032301141309030f080f0403140906041703040501170103050a24020d 73
    0x41e0800c04491a040000124021203642000c010002012540c0c0c1d9a0340b45035560010740f00745c074529450b1100060750007007000114000c030391988512114140004480131544041c01910300401149c44e070802c0140d030800c054100b5a4070440d07032a0f8a032080c01c00030480c00c030f01400070381d58460305180001041c84030660023804a0800e090a04030b41d015404900c1e9a13900c0341c08442000505000002c10221340b1a40c0004034032031158030038441040312400010f080d100503580c403e041d064488010811130b901441203042c204c0d005c105c12025440040400020328005105049041c045011034607615500c2c10740d0913040d46c0e8407280c10031500e030701030400a000c1202070034201c01045e91a40411001c5441106451090303074542d45903024079501000c0d8020b0340d00140c50082c1c0100060101091740094401d510114403541e00c011500e1302e26050005103101c558420540c0404420030062000c22400301c1c507a05029086044c0c5503c0a80902d50346442d80740003010081c03950700c04100440035500340c0d0003c13 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 968593929 1250 968592679 968592707
    0x10204090f110315040515030307051e0f03030f10050a0902090109050a0510030c0521161e080408090d050303060a08070b04030b040c170a0c080619020904060f06 71
    0x2c01c5581a10307000c1c0d110030b11040c2d444503003410742050a882a4941500302c0340e8407805442035024240390310b00c0428610b40060b0411503203a00800f00701c090012605150606600b003400c010b101c81848034a2aa4030780c41301a20f0a41c18002c004002030045040b554014010f19000d41003100190740c4078060002900640a0140024180180004c2c14070341040341c101074480c000c002a0110a41e00c8080d401030084040c11820b00c102802503080840c1c0a035074128a480003140c581c0c9040c500390441d82d00400c142d4500300e060102e012200c04c40542000031407480350b00b031800d000c6c0307064980382003210150040c48907040e0300c54952030549040000101c042d502412041e42d103c241107441c0e07841951560a2030160f059155814001000030a0000354490b4005008d000044402034440e00c0f05014100d0318030032540c4c0c0b533101e0010041041420850040101402c0001c0c03c010b0400e071805813074a407000c0740314a180c2600803644e070700140c2d6280e00a50040000c3c4448042c1642d542d2005040101440700d4 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 968595179 1250 968593929 968593931
    0xc0e0103030c0303050a1b0c02040624081608040b0c0409110405031606020d050f04050a030b010302151905070203030c150601030e06060f013203040b01050f0108011a0c010204090f 79
    0x461030306440c038040d540600300450701110b0600400507085940790030064040e40d026407501800a00d1030200615074081200102102040e9907002d003010709201c4dc06000f29200c0161076040021965210b0b641c00c0d081030b406820540952204039944a250250390090303c0440d1400500c0c1140262440040044900a400fa41d070b0f017404201088a001080b8859900541c00490f113400445100300c00804c408401e100903241010307200c034080b0300705e029203070021520580d45100500a620b040700c00030203258820164203184c00428030048010703011080e940000e00102040210455a003482512141e80182c0100e50005990944120010b030702070b55458082803500d08048400784010030701d50b00c11200507050401e40d4802000444122544503140400401d2525580a500310040c075014002200421041d4503424981070940000708103038003036072103111004031020041c1d0700700c450f00d4112030711501d140c0c0e60030510303074000c0d609803141c201c0401c1d89510006000c41c0300b02d929070107419106a5814 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 968596429 1250 968595179 968595181
    0x705040e06010806090c0d0e07170c1f031a0603040309060e060a0509060702060f0304030503011d15360a0f0c08040f020609060403031205070203160b040c0e0103030c030305 76
    0x1583d48940c00d07070300c541d0411040000152010204001002a04500e402c0020b0350341d00702080d5801e0500e240c11004800c1004815548400410009490141d00440e04081908251004128200710360071400003403603201c3ca01c409000c00b40d604580041d01016141503070740c2c9058a0000e280c05010b001d60004650b07260120b242509140003510602c28141e201e10345407825030340400410360000a000c03648020100302440d20f95000c00c000d18000c038800d8450365160750500440c21460850400440b03e005030384001c0100500030300c803035802e154400350b9032100c40107100316503807040840901b50300d00e00e015510000d09180d5002203901e03100e841d5804003044066145079040068401c1c89510b0030002d40405c0128002c10103071440f039511141b0040505192103031000204605401c00c1c3d100b900400c1540914200b800d00b00c0c000c49038060071500c0603610701034cc0b0445030030389283c084c00060300c1c07891414009401c00220308941030107001545980291907942c0e00c3c0040500940c56800c03400682014 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 968597679 1250 968596429 968596441
    0xe01090b0109020a09050d23100f14011806080105090705031b010806090c07060f020d15032f040e0a20010906080c0d050a29090f0c0408060705040e 65
    0x310079120780b444d450380c0e500020380c60070041001c06401c01406543d2071080701d00041000c1200024500c6109582c8050300c0c0f00d2191000c250b04454015208104040c100000100c0c180b00d100031040c199080d019150701e0b44000c820302040280300c01e0300004220b46c60030003804800c400005400c2c00310340f812411604104550b42c24400b00c1e010304101c41e0b021604000c04560180703410350480e0fa02c040e0f0a003030503081c4240303511050241e90100000d007056690000300315800c107419006296646c0c10f00042e2220761499645e8140c84480039040b000d014202e0b811986401c5070100d807a104003058001c0041c400b0300c2180c01295103880f24007404071100208003149400394455046c4141011005840345401300e4504182501c0440340207040f5092081c0c20455201c0c121980c0c4079860007104800c10001301d03105807031204e100b480401c0c180203130100c1503507511402a0b902c1d0450a584032440491807082c1d9182c81282204500441e0003080e031700d00881c0200402075a0100147c0304680010040c502252618 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 968598929 1250 968597679 968597681
    0x907060c080406050703052502012d03020c0a06090503040611121801051908090f0111031308040b0f12010902090904020405090c03070609090507031104060f120e01090b0109 76
    0x141400414500041c8001c01440c1d00501c040c1c0f00460081c2400752030202034070403000e98051b0f055203204202502181880c2956481303090244c0d4084020341c2014052034401c0413461406210140c0c4041640000781a1580f0b6401d0018fd040c40f80e00074401c1c0042d003801d00c0c3c20380d16508a4020031000541c049990308094200240040130f140040704410710b04501c40401c40c0044161440250510800f0407074018a444c10076104640326181d99180380041c2010f800c3c80c4d0406884810706061032f030600d408419258040011681c228103e41d00900d8a410580b400c001e450045601242e0080c8020810214000d29000109240440e18111a440d6038031420001c01303d0182e0200d070b540004000300058010706082d4001c0d40c2011901c41200c0c90b0382c0400d80040e10340001e07600088002404190300700311030896070183c1070b040281d6080a1148504c00d00d091580c1e40582d100300d0003041340d00740c142980140241070341c5030340d1544d000b0144a50340305524110302074000d00808580c4032980307400004000d41d00d = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 968600179 1250 968598929 968598947
    0x101d030f03150a18020a0c1212050f0615090a21030e01050a05030c030a2c010e0105012702040b0a260403081501020f06090c03070e01030c090c050c010c0305090706 72
    0x44d0b2410030142c0030160410400a400140c0041d061061002101f00410340c80402450002c603180c1d0307410307100b5500410003000e507040580f180c1141c401150500001e83c0d1104424000590130911094640411f03000091026a441e4000c1c40c003050180c0b0300d1540b0654025407450007a0203611002c40e04a0580011581d5100d1403124a0000c4d105001051102e6668401140c10142c15507001c10b1320b8031491036101c04003d100c02c0300d40c0d03461020361710035480031400e01604000751a180c000704800e62409800d4a40c100c0e0724200000d1907000c441e044100440107605403400340503090f24003038030f4201c3d07804042d01c0f9440c003c0d004400d10b42d0140d160500d05201ea605241b240d54581d40c0e644460300ca05607a03c08051000500c18158000c051519041c0d01040204502c9424040d000704178a00da544149414030302c1c90b401000b0351443c55801032011400c0b1880303000494440840025810004c001d08644500811100540c1c55003044100c03010591f0580205005336610001d480c0041c3c1da03600c0944024032 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 968601429 1250 968600179 968600189
    0x60b311112071b170a021c050a11010b0607060507091d0105011e0f14041a090f030303090c060a0306180f0513030905040e03070b100608010512101d030f03150a 70
    0x180819030020380c805180301405c08605a03004540d043d000104561040c50700c520650000503901191300003050398422811259510054005c010480d813190124215104406028140319140c00102d1205407107a19400002c021010010301007071620000090001000c1c414640000e907603241e80d01c1600c0c0582050349011003e13803180203c0c20000c10059424800b01090030210180500001400174168402641b20180003200da80d07958118908000da203014190060f4000d034002d02c100041413800194040c40c40004442d19503c03520036580031000f9000316008071a0001d45c860001c1203800c0b0300e8001c2c440c840b020b0b884c2400281c1d1000c403101c09000303603a40042d0001c2c0b850390080215042580c050b0191a05480941c3d24003003885e11260680001510a01d07004070713400f0001c1181a038016882405413001300c1b16505480404403000d50782d0642080b0b00c6034081c4d45e400700c0d241218000c4850003c0d542d500400e0300d80391064102035544a130011100b900a46204400710901072514070082c0d004d81d5 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 968602679 1250 968601429 968601443
    0x91b0304050330041b0f0b0702100c05190f15020702010f030b0109090f020f0f12070309020105030402040e0a060f0218030f070312050c070f03060b311112071b 70
    0xd84c9540384d04d04a039902e20300180050590407408285104440080c1c00900081d0020305d55820070b03841442185049000100208118100c81d1b400140001c030b00041824411503000e080e010703080c101170301e010140c0e4000410890883d95507034001032042e0050711009000b600c800e02e5004a500d003d40558481c0425140000c60212040c40142c5a603840103280702d25041d401403c007043e00388020101e43c82034031403144081d80441e41881207000e802005600c000303949402c0c004a0310603400a0704500018000900c90b036140d02107643d800b85c04100b803000c941d8004a06100e0301e401403000b04000c1d44036000c407034580209480754501c0b5040c001001502e0800312001480b08500c2c50b107601e100c0c04c40c1008600c041041c01c0001c000740200401008000e46120b51101c8402c1b46146007200444907003003452400b4800360030b481c1280346503052181e2680c18629071114010a00300c40343c0c0009102c0c40350b000080780c0c0007290001145a1840c08103224900a441e8452540c50407190160a416101001042d007 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 968603929 1250 968602679 968602681
    0x50a090605060a06020c040f202205030c060a0c02030d0e13061a0a300605010c020d0b07020a17030a0b060f070f080d0c08100605130302091b0304050330 67
    0x1d042c00c0d4400e612012200400160240880c11040c0c1c0c4c001d00041800e40280c40410400f01803030102c010100401512405d001c00c2c03502d84bc002c240c85034103080040d0303c510340219262a06034001c4c4029a00745500070251042e60f089540041d00713941d8900c40309801091007580d036800080f001c1c03194200703844400d100c1ca0170210101c01494100d41c000b1780680100310340240d030040340f20b503420b24140c1805036400001c0400d507685800441252440d07480581004441c021600c017588400070220049504046c843c08243d0ba500c0090307240c94026040240300360f03803245e450003c2103042d9000d5409001d00030002c4c03059440c0b52003005800d00070400042c1005070104001e4001402120302100e03040d00c0ba0b25154203198420f01c65008941e900951038003c0ba800c0b000b004640c28213111902e000d00000c0c2070580c00c24880402c410503140007400000d0140e034000c80490070804005250400000d030400407940d03249054a4420380325001404240342000d148001440414000001542e069018074889061 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 968605179 1250 968603929 968603953
    0x140c0708010f230606120106030f1512150e07080f0f160923180f06070906030e0c04021b012003040f0303090209150a0b031b0d0f050a090605060a0602 66
    0x20700c503006010039174402000c02c0341201e821602c449881c000d02c42910001241e030508403116094600c0d0302e4214054210305081071001c000b01310503181d051030300140c1c0005507490705826a8020300400b0503035966032045070300005001c4c4000400503e840020025504045801e2003580c0d950104500f02c1206400d0706072043c00300018a500121f1100d50b200c624141409c19002d405c50102002d5400382000f20002c280206255400c001d441c504070a888020283d03458103020007080c49003540030f600c08040c0c03035078035034800039904200741210f09000410843d6520344808900182842c0024110042d5082c9006c082005141440003041804540b105601e10b68640d40c5020034020040b45c100c05150743c8520141c0540c480d104054450a8072815154140c140c0004011004100e6404211200d80c100300304940d0b55901003400e001506902e00305e645902e48540514003a1038504200124640761004000003504c0ca60401241e1500540c01003001ea01c5034414428486182d02565000d1303800110904d80c = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 968606429 1250 968605179 968605241
    0x3160f050118140d08070c0e0619051c06060b04090e0f0109201305010f050102010e030910030e150708070801050f010c02210a0503071109011a0307140c0708010f 71
    0x84014480c3d5031317251130000700d03640da4113034066680c1042c0420012841004290f040402d2400c40601020030303000b10a40c5070400051610382d01084801e4002c0100304200b0400c04150002d40c06000c4902125481741d407505103001c01066921003501c800e02c41c124000d61441c60600c01e480c1c0441c0c204800d10b050301d0160481d9500301001e54084c940194601c018954001018895140038004100c1400600d500c2c1000082c01e5815401e09a01980c10400040301c95a680d911501d402a005040102d49840481c0f6010301701781c90007051403803000c0c1920421015a90101d02540b05003550389401610b80d03210401c1c0000100d240c40c519000c01d80d440c00300400741c5000311110f1005a941c100e030907035000b080c9400c1030074104080c004860691002c44d200081004200011102d00740949502c5007035898402040020712101e44c500004d81c00000100c3c040c188500c0109030480041100f06a60700c118030515a61113500c0e219444071540703041d0031040f038581503000303982003940f104094051300041a44161 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 968607679 1250 968606429 968606449
    0x909071b020d0c170106320423070503010807170d110708030408010603020f0f0303041802090a0e0412020607020c061b0a0f14031e0903160f05011814 66
    0x683d40c0201860002940c0340c04902c0703041151240390020400506e400114107030700c092034054041c9030450345000b40c0b410900300d40c1c0000b00d010894000c62030b04070040591800602c42e41001e6800c8404004100300a500100154104c0f05400d04480d119540d83c0e030380d800300310b00340707802d01d00e403500700b14104d000b4184610a5005a0381c001e40544000a944503216451070744542d0240009035140c2c2e03030400030b42c549201e441a00c01c10513502c803074a0302a0903001075203902c030b24000d21111000e942112005d000c1558142c8a800c04042d2501040710784644501c002804100e40890707001e40000301c00b820280c80440c5684c000e01e80b80d001862413943c24403c001060700b04050811805070416130000e074a48040100c0720781c91303001c0c031890650446a41004154114002ca01c025194000c110104030603c03001c4214104040c480039184d103072000c8000203400c2c17210800d040d607030402401c400401c241100c030448404544c0262956401000040c0018401880d03510401900165880d101619424a64040 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 968608929 1250 968607679 968607683
    0x50409031d04150602010e16120b13020607060e3702190e1f030b0606030601050c0a060605040c0305150907230702270402060c070801060305030909071b020d 69
    0x11440c50b8030f00c0c440030000c121903031000005030f44600f004040b003041440807010302200c01c01400c054904101140042c054004001824821680001000303028840d0b200075040340d00506d203540c1c806030303400c103680074011000803030140340550805041004030101100a03401100d072400e45d0740740940c1b8400c8bd4004e08100c0c0030703600300e41000e480c41c105050243e05500034108140b50f00049090440d83c040c01e203034100f9101c0c0c10f000280c20007800400e4013134000d598021012640d0603a01c0d80d41200484503401090175585440c842c0484078001c01c000c1b03401540599005650400c0315501900382141a00d0041d90199010320003501c164005040600d00692b200d64142800320414808240a01d103000c4800821042c45202050600842ca001100c900300d0880070f400307010050600d01c400c042055400740000f48503480010300b04007030300400d111a00092a204000704102e941d01d00f042a200d07404680100d215060800008452500075a03034100445a400b4511926021075030902440005581701 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 968610179 1250 968608929 968608931
    0x60e0630030309210307090308030c22050f060708091509030304080a0c0b030106050a0c050f0d031a061603030902040f1b0207090b030a11060d24050409031d04 70
    0x11500c0000c10801c01540141c141a0003400c0d251000c2041c510182d5070340782c0754080380e8010001c0c48800b95000c01c81c202a00c0d00003030300550340c1c2c4452a24400700d1051040c80500c051035105000c1c030b5104134110b42000c8900990380c2c4c00c00240c0160820040313209212004141031418003507010383e405c7c01d401074038221505034404e916007011040001c0c074580141d8010801b903440903900c0c8041000d1303e00c88000034038a41c0c1c506400d65060141c058424041e408180082012502584052020402860040e80c41503010303640c0c450140c2e42d0080c050151200b44100b0100c2c40340c0b2010040c204902200c0036048049036054002400c5c0d502100507049001d000ea90154480e00034100d079403418880c0d40107048001c1d00c41a904441504042d00340000e9500c10804c2c02d1030007682c480940c90104d0f60650b51940402c400074403842e80000a0031038014060004031031890318001400c0040c20380d4244da84402040c01d900f5955039100204000e4903070b055001400556a000c41c00400180410842209100104 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 968611429 1250 968610179 968610259
    0x51b0304050a0c030b1009020307080414210a14070b07120e030d0603030206061207060c0f080a0c140f03040b03043e0d0c05010522060f03060e06 64
    0x2ca508140d203c0c0e4005071406401d80051017461100524600014002d070030065055141c000000b510403440100082c1c08890100300c240c482031014040c0c051320703d54071f00440c2c0d00b40b2464108490141c0042e8160808109040140400000c0c0d070025078001540c81062405180d0b145081141c180140d2489009016241d01710005c0a0400303201402e640954804005891899403c0007898198050011401000888250f00310000e003c5514002d0340d1140c1414416680e40780742c189000c1c507005402801c850000f18100054944c0101580580fa001d0641d414075428020b44c0c01e0303140c69690680d038010390300c1000100321741805000039560050040d00c3c0c00300144007001d50201006102c0301c0141c0e02c502c145928141543eaa40800c080b02081a21541c1511407039603034498001c0f1040c081c241c14000701041c4500c3e00c0760600d020703014451280300c45402059440c0c9015011b80c00d21010980400e040c5040131844684912045204807002000c2c000340e00e1a580e00700840703d400d2071141d1040c40e4050 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 968612679 1250 968611429 968611433
    0x3010f21081c090501090201080f09070b090f191a03160c0f0f0c060306150507110307260615030307060903090801020f0301210305030f10120803090606010201051b0304050a 76
    0x80304079089540514000316a035041c6c0d00c001424044001c04e5261382c4240350052000c000800620f08d41990781e04803000342c1d2440700000241e5202c0c4010000c0342e001010803511204845640d40c6c600c01ca5007104040440320f41402c0c2e8400c1c15020490307800d00020101c2043e036a040340708403000700c4903170301480e0207072400d00550302e030400d82c0c0c42405c45c1500c03841407034801042520703414443c150080c071082da02460820f03055000203040d4468000003901400c403d41d911440744d90300707100900c004d00f030101d00b2008800ea034801d140780484450030904503501401d40000c071107035400d0070141c01808009024502d000c11541c2c0d214010940365005a040003c07107a008112044248018140f11b010380130310715203c0d0703d803040d465403086050761b40c940c0d045d005d65940304c00281c011040d40c1c0c100e2981241540d503503403109901c0d0301b404000d5101c0d41040c0e102c903008100f40402c2070b0046009144031015a0f8032651540010ba0070f85e401a0b4070703110f200305e500a0010500103000040c64000c3c0c490800d5a42034845070b = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 968613929 1250 968612679 968612681
    0xd0b0f0f06180a030b07031e0216060f0e0102040f06030513031b0311030a020a0213200706110d02120603070e07050f04091119141602031504050303010f21081c 70
    0x1c58002c6c010075a900310105040320f5204031411090142d034425460555440703880110075403101c030002c2200352a20740c002280c40b07031358000003040b8480310000c6407100e5844442d080500c0b498170410020034549401300c1c210403034003407e507050742c0d070103864031810140c0220780700100d6640c140003942009054512110300701d8081c4010212007040340d000700080d50780c500400480320080c07881c0c00c0c0d60a1038605038260081556060510001030341c00d0064a40325541001800780007450401800d0002c00503640c9200e082c0c5601030300d6110002032403245107075a400149641c1d4902802404070160600c0000383e64680305000402c0c4003903c125051f03050680c0c1c1c1c0c002c0d00540d07011046528100001040803d0308201a1803294204862403501c620b000c0d4030495a00d00074441d40c814045180c50044845d0159201000038064101100c491001e5501d01814400d4403a0420700640c604490030b41c0c0001204041c0c80c00d070a50703502e459901001c1d105240e96820700e9070340c030032511807507150403c099000c170280d12 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 968615179 1250 968613929 968613931
    0xa020c19061103182209060203041520160b0115030e030a080601031a031005060f0402252103020a17070c0b0c0f0d0b0f0f06180a030b 59
    0x54003101031600d608009000d00010398100e255610303a4428444031280240444401424201c15140c404403019000340c03c0199601035000d0301102ca0810181c0c1d003c1040ba41c1c010342c842e5019406ca805030340c03444900e29080d41c0c0030981e41045270346108844040095174100424030741c0c0d4036429004031083c0ca83da440c40540001d034003085400e0452807440580740c1d0503010308810342c294000a1403070442c40c9940907200701ca028014a04066443c80c2c01d1000714000c003101300449200034111203006845090840140c20111040350082003a804c901c08141070500944141031000250415080c00354a1050107410304001d058904100c04200c01e5865141c035400410950303021b036800b6030358030822a0084d000d40200c00000c004c0b5040f206c100030381907600c00024032219030302420398025038440b00390941960103520342140c10b1400000b0540003a0b0b031240e02075130b2480026905441c0d101d040d0000c100d100314011281036003003441000240000c9100c14107501034114001c0600c1c0d903407a120f495595400d04 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 968616429 1250 968615179 968615209
    0xe1501090b37091410020d0806060721020c03070620191505061f080a2004211a04030918141503101107021905190e0c0a020c 55
    0x1d0780d1031080c8110030a58400d890303042e8061742d411040d0a5641402581c400d090381c42ca50410000d100410090350722541150b400c907030003e520001c402b0040d8981c07078060410080d00400351043c4907001d0328604001c91003c0498816840c1d48243c08840e50001929640a00113042e1a009601d142002140e2190309200361a02907480b113509914020040300031520043d048901c161201030b100c0c05040c00b130300300c82c1c0078421451a24440d50b89074071911001500c40c1510000321500e10014006140710840c0141040700c00071440f13207070405201d804217030f11004000c6018240851317500c45007880140380e0000580041c80f80c43c040350000d42d5404201c1c0203040101194502c603449403501c50190060007240d907008203850391901c841088401c000399542641800b61345200e40c450781c1030a08881410306503030140d60060030040540020010f10121550180146840f079003404089200707003c3c2c032807510403d44040c54800f81803600c4404005801d0b8003c44004000c510580250141c036840b0000d980300c08030 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 968617679 1250 968616429 968616437
    0xc02010908130e0a0b0a0b16050a080a090902031009020f0c010c03020301052d09072d020601150c0308060a03060e0c100c0302030909100e010e1501090b37 68
    0x5030a1000094003c0e401501c0c0303102240c1020030211091382e4070440d91044a00a481495644c1d00b05407080c00003c0481102400c00d005040c01541440400c1b00100740300c4001e40d484d15400e54883e40b080049000603200d110268582e0036040c45094060390080c4010b01480040fa801c100e50b569010742550850507200740006e030040010401350a048011822004028502c13100d45040d102c0808400182403250510695408001c505054021841101540502d094030980302e4640b20200707481c0141c076081e190040c45014000150302c00a614004030100c07950740ca120181841e6141103130690000307000305074444020710b000170006019105544e043c402d09000340414140800c100858403a405c4d00702418440810b00034000268040100d07421180125100314417070b1103103420500100890381118080711041e400110312004800711603480742e920b280c54244146c1303192004480301009031140f062047e0f130900401030b0240c80c6420410348000380c4414241d0b58080c1d01c55a2110b400304106c203030082 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 968618929 1250 968617679 968617717
    0x607020d0e010f05031306020904020a18090605010f03020304080405120c01030f2f0415080a0b01050a08180c031006080c0f030604021e030610080f070602100c02010908 74
    0xc40e40042000680010900304100e03e0b001e2004040e00d28030000308601082c0402400b40c0c42003200e55819550b419902401c110344500310070002412031080840c001d103071090044400580c6209500645c016114180c0d41c880f114000325800b98069080948103c0b24030105200206076a1261018004408a04402003030005c1c44034002600321010511102001801e007014501c00031700c000510000000e080000340b44158101080c80c000d070141e034120b03100030050603000340a120343c010140b901402045008000c0a14540019240703841070311402008680b01c01e0000700c0d43d07000080f00b003c2107080315040d0b80781400064002804d2100d200340002561b41d0b10503042c4014107042288801e204030944401f00040440c0001a0340c480c00100000d128800143e240382d201c8440e9980005d02050244c00c444040c100500420140ba44034000c100309842014a10f100c0c02c2000152201200e803550040c0c0490f04200075100090180204004255901c84000c1800940440d00a06a200d0b444803d2110 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 968620179 1250 968618929 968618953
    0xa0b0c04093e0412050106090c09050307091e0c0c050a1211060103050a0b04151e05150916020a1b060f0c05060f1003020d0f0b09030408070506070c08060702 69
    0x90001a2402c11261a105460400010040c0800c40b002d541000c4c1611190340f403c1d24001780507009680044003640c2c1404040001c4940000442d01521400c4050b034200c0740e12005040116901d403000130300c007071078949240121644568000402d0050b203183c18550303140c03151251480d15a00c0501160310800b17a1080310441c03603000c071500c900b49103410702400e915491502c030559114103600000c0c00714a00800844c0406ca080c4201f840c158041103418030110480d4580400040050725001520a0824000a0b994034508034081200b25006040c8005a11440031810008500c1c0307800105601c42e0740005404203800200c204007002c00b11040000f5030f03080c4100149000016101390051254488101d000214081141648000b04503165a8166940c3c9000e4003151165440a0b400070904640c04090041d20b14007140c01a000300c100e04600d840d8140c400341e8a1146208101c40c07500400790502040c9440740060550740d0054011404903030300c410344c482c104542541e800000da4056000120 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 968621429 1250 968620179 968620241
    0xf0b03030a02100b0102070503030415051306090e010909020108040f0303020d11030402041404170a050921071712030a020d0212070e0301060612090516060207060915020a0b0c0409 79
    0x880e130300080c400341c4001ca1034500800c0c1d07039001e5802184108440000008041803060060781c103080126101a04115580c1030003800070f40c460b0041c50450402c003000407602c01a41d00030184465410303902c080840d0744607151654009503c5008800701a004c1050782d440204a00030302c680c082c2c0080d8000d079a42880d1040000701d030300c011b042c0445180c0c814100404500000f50340f0711aa01c2000c5090380ea026880d004032094414180c2c0036501c92081c0e00c000010340c001803c900b44002c00031040b07605241e295800c000b00c080c56002080b0041d80079111000000e51039102841d0026881c1201504007034203050752405036044000344200c030310b000310100140303d540024221114201170f8000c10501e801c06100070010b102051418014544410000c020450100803014403102c9d0403080f820311a854103002510b42c40b07288101000034034210780c0800c80240751041a18190040d4004140b03e541e2552541d148410040050186032014030001030141440d010b0b000070034203644501d072001821000152 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 968622679 1250 968621429 968621441
    0x80a11030a03022208060c220b0d0c09140409030e0d11090c0f0904090807052b051c09020613090603140c01020a03140d0e0709140405100f0b03030a0210 67
    0x140152904c0410420040d000c1040390300103000201d82a95040c41c8030360303d50f00060b4600954291202a07900144580400d40640b120741d010010910003504501412218015640903031030410506007201901c1c0c1c540399110582c3c1c4c034804d0400c058494441e40020741c5072001804141d9150500c4e00a080c00d6150aa0f07a0f2544101c23070328201801c1c0741280f014002070b409901d1b00503008a80d103100781414010000c1c10b44d0600766002c000c840282180007907244440c00e4101003141019981840c000645000304c0036220202c0249181d00b00c1340044040d440003a0034507450990b089001000254410301514035194041e2140560103e41c09155183c01c4524030664001d513610354200c607180c01741c44c0c0e81c042168001c00303030140b42c01030701142e00d04695115441880c201070380c003501c0c06080701000000810702d00111103c40e1030800c00020302c0325041500404c00c60f4010415003200c1c0171755204043e5076028401c180745030038000076990b000101003441d641c0030302050b0b40036034018410203100c4442c5000315 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 968623929 1250 968622679 968622727
    0xc01060608060105070809190e1005030d0509180a1d0102091302041202090a020d020d090b0610051e04090606120f06050a121401061d160804080a11030a0302 69
    0x2518049050706d60760910f0055004a6100344d450f44140070700c000040d2000c10103081513420b103e03443c2c01d00001c12031044040f480f40c1c90081c0a44221404418050000e40b0302101d805000828440b00100042101520041401592a60f039202e9280d0245200401c3d1401c200b0302400140e6030342104040101007140c2c59080c404045c010001030101e5110b60301203244240e81515034800580b41c620142d40640500404000e01d28408943d04941d40b50541000304034900946600e030300c5032070f207209010718420000442e801250082281103007000c4082d20346c03009070340d100808604143c3c03100019429074400e5840321000a1210b5140c040809452054010407030140000300b1086240c10b001c140d0742c502d03601c01c4181052a004000c0e00784030342c034088999400e90400c000c109a42c0c542040000440b10130030000390000d001c100207100e100c100c1142007c040e88a031150040390b5280d648038019940040e4030f80080041070355110100e18401c2015200e01a525100035032141d90302440c8007000d007280b000c2 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 968625179 1250 968623929 968623937
    0xe13050c150d021c020c07050f03060c0304140f0604150b010e0f0f041401150f0f020a02060304020103140925053a03020a031d210709020c010606080601 67
    0x2000d01d040c214000c40365400c2408901503100d002c02c3e11040c10b5600329034100c490143c0000f07a4094003500208400b401da50003140d151545a55000a15643c0c0104503074032004c5010410200c0c000c039039942c84003c030000148007196000c820041015040031802d8038100c41c00880c13180301c00c0400c402c5001d4030709482002c3c138084400e00c0f84d140000303513a0012405000c0c0a81040904100661aa41c05c003003010481c9451480c105c4d60b450344030b4035044072483c205a0008420750400000244205040301c1045050303401040360035504c0d020850242d00c0030f08101e042c035649021800b84440b140301c01d02e10a41100001d00070108030702d58650240300040006141078244c00509018542c2c85501000c1c80000369080c500c111018445400707586444080343c5641294000720b240c0425074002011603105102e65035641581c1390002d2881c407000c0d442454141d0103c004401030070240307411018030860b40440310403240c00c1940c405280c41283d1060311511030341c1e51600000c1c0125a00001402c0c2c00060a1038 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 968626429 1250 968625179 968625199
    0x1090618060e03190807120c0c0905060616030c0c061809020d060512030a031a031005070302090d230610032603070302120f0105030d0c0c0e13050c 65
    0x185408030100a0040405001100010b9080d9490810425504420f00307100a1020180383c1003041860f04058021183c0d0329256aa25200d180300d028101c03019036221061488060900c0840009440020800c58000c003040c0422541d44801c40c2000b8400b038000e0725008131424407030404801d8484280c0110f018800021401d0414040f45940c0c00c0440b1803c80c00141c0310205110361a000d00030a41c071081d48002203103510051440c01200400741481162003c00125420760922181014082c0c1400d03450341240c0e20070300e911801030f00b0003503021000f0300d00146040200c44c0050003208844d04240c50062450f15602e40d85141040036543c090300482c0108090310f420b900298080701540801002d043d0040003882403501808080700c404400201502d842c0d00e0b003010000c0094100d29100c8030f06006d81004540100080750b250b03410fa91014001c0d0441c440c10060907100b00f866107100b00d80c074840752500001c1d5511f001649034060254000101c401030780c41c1c04e001d45401c0103400701d2441041111 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 968627679 1250 968626429 968626457
    0x20301170f0303060109090e030d0e071e0f051c02031c1403090a1407090216021306030b0106200304060e0109081501030f11040509031905161407081b010906 69
    0x30700707642150b000340d101245142300a00301e41c0c1140a4880c11428040c20700070000c94200b00400c234101964001002d44034040403005580c9810405486100030300c0030805014011400c028000d031000310002c0d180c0c80710390200c1d640824502113400ca01441000810420010065408000d108030f00010000c01c0d0300310309000c0300700780e264141d10704020074591440725109103880c2d09001c1f410003818071070004c540350040c00241012600078a1000c0380701d440004000c8402e2100c510880c002e0300e40110040c1000d07800c240b000d588001400c0da22071428032219034103083d404001c00003800030300b0156440703048442c007520004d0490f8029420003190360300f12400f802c0b070803659a0713640e50441b50000748083e45140035080413008c600000d42001d800600349403c00c0612140003008141858001e41101100050840116824000e0301354031620364840c0d562141c0490002115181c04456540588403095a6090140c0c5020709406280498070f0303d04410108030740e00300c001400146217505203070320403944107 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 968628929 1250 968627679 968627687
    0x1d190f2c1603201201090b060a0504290301020c160e090f100c17040c1505091e0301150e0603010c03020309420109060f06230706020301170f03030601 66
    0x241c84107100080040003c0340d11940c880b0008010758400c400204034410746070901102c800411910107000b84880d01c0000380504161040c2d100ca14051a1502d00041252701c440c40440f4040105540c150b409008102e1104802d0249000001c04030503000007051402d090f0900c00c010040ca40710320740d041060054107602e0080b0705401d104491050014034440d0540040ea100191007131a0301031030800004100402601c100c4100035951851030040082d05800411030b281e01c64060703444d0b00040d5184118490000d503250686c2e081a0040011a805e624a10b4003600110741d07500c15400301d801d0600380b2401d81000e1203130b0003112600345415451480c1c40300749580e5541d480d00e010181e036419100c0d0320403210344d0007441292141d0343d450000031000c0c0c01312490007021400e0003020126882c00c40c000800030341e18040c0e44112401501c40b541008280d070000c07007850042401c0c01941c001d01300f0144000038282e1005601070b20b0310715600c440000b8420155454122a031004410a600400510815a0304 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 968630179 1250 968628929 968628953
    0x417010506091b180118060e01020f0304140f040e0f0a170708070209061306090b0112090302060708070201270b060117130302010b040e03041d190f2c1603 68
    0x2401e0410104000002c0100c50500ba04544660031b048076030b1010030151790100c000381881500b40e08443e1107682c0030601c26107a12036403085d4000807080348005542420100c0303120040040060000680240e40000142032185010000ba20b9800081c41d101c100042d42e800d9400c1c805d180c42d0145c1c03c18080b5610448244142080a4410801e0f100003c2543e0b407120a801d0b011110000c0a0102a696211b200042c14039022031601040b011601020101e60741d100b031a10041d0164010300894444200a40b28900050241c00c210f5480310860003c003c4040b0004a2415540d00d87e44080141ca05000308045c8018000d9030401260b11450010398145916940e0401c2c0b0640e18540300c42c41902d0241c1c010112500d540d60800d090811042c1041d074040081d008681a500711007005168071500510340007401c8074203000c00b0001030b0745990480c1080e0b010110f13120740d542c80000c20b8041e40c00c405005000012000c444161880020041901e0501c920311265084203881c00c0c8090540e40c030100c080c20b03 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 968631429 1250 968630179 968630197
    0xf190908150a0506040f0903032702100e06040305070e0a110a0206180f07090207050c090f0a09020a0521070609080a1b0b04120c050d030210110417010506091b 70
    0xf40342da000c07440d90b17540c603030007142021142501001100810310b0060081d000d00c07040c00e5285905602c0a02c454444078103a21540d0b64010032a40d0b0a0101c40380649a66407182c000b5500a4014040440001c03c2000303603002402e0301210588c0c69141480810080d10300800704804441028002e02c1c0e05250001081c98000003130302135580c01000c45200d200c0c030700b030088810010248104100004d140500ea4000c10485000350140d640c604111028440180b0b03082e07c400307000d4024000001c40181481c0d00c05480c0510003092250169a0781c0006103041220300204100b103061001c4584041808210b0003008044070b05001480501e000a1309407a09007506010340215001c0a1003042882c81458110103001100b0741551155151256943c9013480203500b1110055404804181c0f890306001c1c401181e81d06900030040c1180802030200a4150720348c010b00b0540e010b11010840711640b1000712103c07003805000059510b0808100288244040c2c01c12416a1180840c0d0801013200d9003201c0c1807107 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 968632679 1250 968631429 968631431
    0x709090611043813081501050303160c0e0c0a1d0303042c16020c011b08070201021e0c0f060a200f0102070b060f09010f05040b01050f190908150a 64
    0x181604911800307a00e00d03241610302c0050006112130b805000107001826503041a0440b2000000761001103100074080c0240d07689036005104003800a440a811905c0c4180328410b1090029924416554640c80607540400124004500095544d83c1b003074404490004600c2c0d1084252211030109440b4452070140d130f010880d504071a070301e50a000b5040e54a99036598070720007246151031800302c10321200c000003940050252143c2c18260b50b02c40d620218100000b001e190030500050b81e45c58604e58000c0724104d042d4094060807030fa00e480a40626400c10140310007410741d4200340310410244000c0380f00543e100c1c1c1d2051111407003240c1d02c036641d1901000781d0b1004885403502c1e044400e2510704034022060096000251380010001310381d99550161100341c0e8010540c0c88440c040055110090040d074407004c0c0804410801c0e0718041d00003010f54581818514134003034103e4082c819a500891031030350581031100002c828181d00010b082c000f0f040100c05404003141c0c12520030880c0700050440d181036 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 968633929 1250 968632679 968632739
    0x30e09060405010e0c0c0c0a03110a090218040906231905221a190e010b1f0c0b0a050105010906110c040c090b0c0c0907050c030f030a06030203070909061104 69
    0x40346c4100030030014850001c0c100d02c030b110750b60302d0415500c0d00b030320b070031301e4010f4007100c000107444c06080c020307110414210752010320350820100a00004200207402981d5503034841000c104003100510350860255084606408946054400c2d810001a2035003d000707194640401c00403451a925100061462000c00d001c4010025090013244241c680e82c1141c203514019081c801a010650694422484102005d02105072501102400c07101c0307070300500d81c10001841447c07602c80420203a9002d080ca4a090080c1c034000e0b10f860764611110125041d00d0026a10001800b0f00d6801c164194010141494086000c90f2103000311911500503540d8175000300d4407104414203442c02845090050f02c1c0c2410540e4a403008070309029500c078200750007640a9050800405e601a11540c200e900c5030351040c0046141c101002271140d6541e00082038900c207241c0d07600d40400169414003048005040d024004298045541440421902d44a620074241c0c4000c22080151240c0c1000311800c84c17591032014021 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 968635179 1250 968633929 968633947
    0x50f010e0a0e040203150c0304030206180c01030c140c030909010506030403140d0b131506050a020703110d21081014060d091e050601050402070809090c16030e09060405010e0c 77
    0xa80042c0451200c61194194100f042c2ca1042001540c806c0b07009a003200c2e8140c40324dc40300390381445179500f1401543c02600d07100803554080d40014441e950f4503e00310480c4681c1c1c5c003a90b00c0c181c00202c003481e0310742c000041803602c624000d88498094402220042d145080559002d0000508400c8010151501151102c514600e944c4503104842d0050034a07009200e40401c1c9000034030070b0f40c401e07001403c50201c020a0041c80f44091350301070400343e0003e1000d5811910381400a5032010b0800b9032103c0da0000d2403000a40b418202426040c0d81d111110003041403a0000d0711810005000c6002a82c00e490200f00034038449003a6068488240c5021340d540b03400101000140111602c007402134811080460344141c2030720003c0c155035015509079107141c1d0300c880820041e442002006400010f00b44101080e0f4940b9101c11038029216512580c84c4c0b0540028012004900c104c09801103030340c42c040500c090a0200340b00358028001c660800096040005c03070141080094207596000c000420300802c = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 968636429 1250 968635179 968635183
    0xa060b1c090c03080304060c090302030316050a1205130b1801080403021e1b041b211a0109060f02100b06040803070c050f10020c06091f09050f010e0a0e040203 70
    0x760040c0c0085450026546a00f0407905540c003e8038101c4403e0728002c101c540e0180700b4150030003902da00a015510380042c4004800315005113104c01e60302c1d4081c0341c40241c00030300c0c84a81301d908130510382c0b01c0940301c4914114070303084007031035600c41001240d04215110b9440d5401500308000303042400c1c0004c1948840c00c1c12460400e24484140700e085a4400c140000100002d080c5807000c0c0e5100000d81410545007403009440d04c004507040350701c0c18206000c442a000303034040c444641c034614000d44148400c0e021130040e202010300034540c000071081c2d085071650780200041c014181c68140481414001c020082d0341b02603e45203d0200c81d5504e8002003981e85032806c6500070702503142103c0c0c88aa032410104080032080c031400d4132480c0030120022882c20802e24808029a0b1500508034942e013140038010598842500180d000e024480342280b403150f4403061450f615420fa54480281d41084c080c0309003400f007950140e040c0001c04118443c0e0385c1c1c4054001055910a0525103066192440440c1c = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 968637679 1250 968636429 968636441
    0xf0e0d060b0303120a1a030d0c060f32310501110d0501080601050d02180606210f0f06030a0f02040f020d0903080108010203101a070501050903071109010302062a07080f060a060b1c 79
    0x844015640f90f000030341c82104085503035118841510301e141d00ca120012101d80203804102090601d80040c042d00e62881003a8222560300510001c03421436541c80d044007a039445040c1c2c04049035501c0d070051012050400185024060075505011401e9560300080d10b2641080100040240c542d00060f0b5261a8a8180d51511506030308030b902c8030060354114942e80004860700ca0015980b0400106950700c009a014005e0002401820408885880d04040884810070aa0f002034580d6400414290184024a103003034442d50700065000c3ca9281c024180b00381030b07200340e0483e0300610034001c0181c46208140308491851300c200c020300319039080745505806001d0300074145500c5c2808201c0145000700c000d0a0592140d08042e0464985030100701d0400000c1c08060341094050281101414148650411812118142119141400f540c161410042c1d40200300075400074018000d2003c8200b0100e500f2081c01c0c0814094503090803510034203401804504015802c0008407203020300d0302a4440 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 968638929 1250 968637679 968637701
    0x9040f06060f06170901021905030703110d091e020a23090a020a0216032d061a0112060e06010e0109031b03030f0e0d060b0303120a1a030d0c060f 64
    0x32903429500d10024185a407031520000348544d0100001380071310010320850b0a100d0001d0300713403402c000c8034260490301600b0040c030180c141765542402061000d050701c0640203480740190007003200c00c4031780703000d80c11511083c540f101e107044824031100059031581248020342d05007541201402d070303205500c50300c0000105c0d4902d400403980d10500c44046155001490000159007c0741e100c0c00b00407071014082c0e01a0f01c00a01704505094820040100b541f413802008951b1429000d02c0002544a42c000c5070000700b002294640103640c2003815507040010503004825409081000030700d41650004240401001281081070025840e1001ea00807181207015540100d5000b10042c0100c1160102044070300060300801c0d0600d015000d00c51195a5106145030094903440040301c1c0783c1e072058043e00c85040d00940c180814001400304403020034a0764442c6001d07680105604c100a02c5500b410840c40c00181d0090b0000c9011503150380c3c01c400d04100040e4880000501c03011500114030003840c0240c41 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 968640179 1250 968638929 968638949
    0x61e05130b042c07080a060b0406180506270105060702030f2a0402070510110c25090204030203070b0a0c0605180601060806030a03050c0c06030f040512030609040f0606 74
    0x4911039112120a01448071621955901070074007844114607544c00071440349074510b0f800740b608080002d017550000486900042c00100e60715486001811400c1c2a84103510f00a5a952040080c10b252a07580c001e010b5003940d40da80120480228410b0140301c050045600860002800c1d500f1520100011304203a001e4000f5602000b406041d84c9060000090f1802c0c50348010b80c900311030619080c402c48101c00d9004004000140d032040440f0007034845d40a41c4030072100140309408081c0300078040b05a007007881e44146000c03080c0780100c90806248503006090010b02c140420b20050b2000506c0c9401d075041d0300101510340100140c100c0f45400c80440007440e090520381444131070b11400781c007428010110400d4620a80e00c2d507800b2a2401c5084503401c1d0315510406041010a01510040240c0100901900d04c0401030101160007580203481c055400110441080300b031000a201450444801d41d10303071855030500c0b200140051201801c00340941014240710810000c0780e61017580102840340c8 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 968641429 1250 968640179 968640191
    0x501050f0f040b0d1a0d062003090f0609071d0a060522050a050f18010608071e41032b02010603020307030b10180609061e05130b04 58
    0x10901d000c681001114100e010b040011088402000098078040b07120003811b10502400c0c252070302c078050b00c0c2442900e00021506100a0004010b01c00251f20230380c4042c0051241c02c041181c6d00c0c1c03400e04018500c41407034000e000103001841088910541c44402e46020046075250017100307400902d0268046944512203461040010b80b04411080d0324102a6100b00500e90750f41c8600f40699508036108981080400c00103400101007600c0389450310544000080c00f50344503500145481c0749a0043e010808030385a42c0101200c0000c10840907013140090030080840504042c1960a007034403050a04941410344a0502880302030794020211008046400d00f460341c8913080380704000315241e00417035914142c00204d583e00501a500c11240e028008000451440d00c0b07105e800c003001380024500001480000445040e002c80700d0002b1a1201c4002446a160000700c90844485034806194014a480c0352034019040d041008100c542c00d4401c6c40c1c0c140e828040c00c800414282400c90b0f40305181078 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 968642679 1250 968641429 968641439
    0x1216200d0f081029280507030e01050307030e061302040615080612010e06071701152c0325080102030c03390d150602070501050f0f04 59
    0x514558008040c0c80791000003500c504216490181119528410f0403491410008440c0300f58149070b080c2400500d14803101c1d210940050b4581c003500700b04803240200f5001c06100854150b401e0342c140d189050041c500403059401911042e0810000742c14030001200082541e4002d070420741a200241d029907001e031a100d48400040200745500381d0049240c62008500f114081e50300040051032601d418020382e84500801100e07070200c40c03a4003d15502d621503114511010030900f40590b10f40d84600501c03903042c1040302c030b890905a02000e2400d12182d1503e06c0d458000e0034108906480c203064000406903021104898101100000d0b050320400c403010b48204a03411f01c0c0c41d18045501200f010b0999220001400d0340400c0d0f440a904d4501003012540c1c40d02c80d07102c00d8455140c8044d211881c00000d00c1c50415000c0e030428070451f011b0700018500c01d10801441031607100140214003c103001d0620714021741d01d041e075024181c140240000d5544840d41c200042d118510340810502d03694603128 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 968643929 1250 968642679 968642683
    0x10219260309100e280b01080a03080c030103240e030d0614060702010801170f15191e0c05120403031d0312040f080d15060e06121620 59
    0x1c030303254019070084904458401c0214040c02c184c8000400083c5200e03c18104906840400740b404910b10004040da0b080000d107041214600802c0c0c2c0304080d10402c459800e000d014014003c0200d1480703481000180300040000e890341921032401000c0f8140c41c054000300900501055961501c0b5101c0402c029170003808941203a41516034003020890000240c00902070f81d4021520000d0100b105200117011400088000c6280511360f181150031007a1240b00c080d09002e400c07558041030501d218200300801d07000540c0d411460201071030420503448000789003e43d82400b0035840080341d0710350081105441c0305400303481c0d94a8085c00300702000d0400c0d140250017400c1446100000610002545d060540084240e9814841106d9084c1d401e41d1103a445210300c010310501143c02c52028050000c1032480c510442407078002541d81d00c0d480a00340100a4144841b58080500c80c6404002d01202c0f0380b060b00406411280c1d20300d01c2c0290900c039550590384401e0525031a0503260100c0242c0d2419080 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 968645179 1250 968643929 968643931
    0xe040812130506270109050607050309100c0203070209130c0332070f061d060a1403070c02041503020f060a140c0610150f0e010207090612060b01020c0102192603 71
    0x81c05443d5610f03545020309a01b0b80c1d0840038050110b41008002a03102d502440003590300403552003d0388e007040c0ca810400000ca843c0201c4034030050340701080440840c20310701aa50780042d1121444419101d03103039070f40c0d1544401c50200504c8440034010340c020f00b050342d403140782d07050402d0750082c0440c2802d841e0042e503810301c47c894044901c414540004426004d081180c01440400740006041d9400505000c101c1d88040d00020801c504c1074140c2c1c000300e1810000d0341c040c0d200c584e110101d80c4002e004000a46041000034802205114400c200681e501950003594201c00da80c00c03a1600e0040c14255001d407030040c81441d0391a40007801d1180310b840855050301c2a8548500708070203a454a0107201440c4c52a100c00b000315442031840f864160140f00c0b2030f8910041481107603c625102c20300401035030f41c02d070300080480341b22088800402c05503000701c480c03c4200703200070030b007403094000000d41c0c0364090400740042e841c0e43c9401c0300501c6082d20088424050483c002c02c03444101c01d003100d9582d40 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 968646429 1250 968645179 968645221
    0x1050c100e010c030b3f0604020310020a050d0510030822090b1003020318190303140402090420060a08042121021903020901090e040812130506 63
    0x1203491643c40c0c059001e44200c24a200010304041c6400b1141d031180460340e007070b500442590a205111250303001c4100600c1040f444100c0025050604152060500c0c003207482c019040828014410040780070b80c8a02900c1d91400301082c08500b940703c2112603800304400b44c001400d0a503000400301ca62681c40c040700249500c035203100804c2c45a98003d810100c42c1c111814680c0a80014941c21019120380c001e15040b14505451111001030201c00324540504100300b031181c85441c0300094103254242c4a000804140d88040031150319040c2d002481e407110040c80285010140103448a005220300a02c4030300c0300e0041e0810f9070300e031400300e805081d075542100c0841c1e07400b000e18040c0000d6003142194210340c005030f0316120102e07542c0880b07007211140c011068171011b580c00c4c4000866105030034544407000903942c4005948640d01800148402030f01d4003c06c091241e100107010000300103004a88894001c04441010342c3c813500d80007001c482030040c0240862183ca81803001c04641c0c1c004100b4242 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 968647679 1250 968646429 968646431
    0x1006080c1e0a0806150304030207090921020606041406030c0607030903060204031b0b0c060c031f0306060e090f030403030302090f0415060801060f05030109090f0b0c0a0f03060503030d090201050c100e01 89
    0x940f040c0b05c442580c130085400034016009080c0822446549820042c511442004030100038070300c080c95030590079511055130380164440f20a004860030648218130034108401e01360411442c069020a1341c0741d1b9034408041c003940002408009040c441c0e203d400117151701802c2035540d20b6032410080e900400c0040c00c1c14060900d1080013604240003011074404c0c1107004090304540c3c0d01c00d141c0318100d8000030000410362a50181c1d6801000764440d40c2000342d84110400100d69081c0b4005001c0c1e4030f0001c040e00150b074004e944c071111249002056408403903143c80c0159417121100e021070141e101c0b6928281d0442e04002c0d02801c3c5160313294420040e038240c1d503901405130f03982e10800c0721400d010382c1d824004110b0810061190641c1c40c0c0240c0c0b51a400b84203c1200d1042c00c0d916000e0090007143e019209107404554072020913441552281d5510b91850700303000740b074100000243c8034450300400340051540c0c0d030500720071a401002034a100d2030983e0203592404280c08041d5010304180903035508030f5 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 968648929 1250 968647679 968647699
    0x13080d12050f070e03031905180306010612150b0c010e010b03030a0e0415030f05030408150609160c02040f150b160f030c02031b03061006080c1e0a0806 67
    0xc8803041c4a41da110b202c80070608085600e5042c0d0644000b022140c4668041c0010049a41da01c40f0b41d04151510207115600c150380c40d51842581c00aa04050b61003034400c2e0030202c010400c0b0360740403107080440c0e50b051100194140000d1000c0c0f4108106611040000384046501100c0b880103600c560005904035001703004c843d001d1010152240319840a01001c6403e840458009060a500c9602020011445542c12039180e40340e114150b00c00102c100d50a40c000141400405070500103841100403544005841d8288032000400b041001001c3c1444894140351031801184a4210124403580142c41000701c00140c1c18003101816030090710441070f00f0000c00008501e9140411628201c1d0140032800d54450b01ea500c0c1e05402001c81c0c010b46c100032504080d1005a40c1c02d10229034010011000c0d0355042c0c105800b85400c00400901c00b00f800708103002c0400400e5000050300d5032003100360740b69903655865100c1580c55540190307150740701d42d90003103104040d09800103803990069404079614040 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 968650179 1250 968648929 968648957
    0x120901210912121512020109050630190e011e0f06060e030c0f060f0315010f0c0302070608100b03010b0307020c2b1103191e0201080f090313080d 64
    0x10b440720072801030303003001840c0c0040200540e03031191001c405205261145184c9d0359032000a1154015607040c0d0031f082c0f43d90500040c02c01c042c000905860210891000381450442e400400b2501460080f858003600c90340304042c102d5082d40604da990340d0092001080032000b00c00b00c1c0040015400e04501c1c01d1403c50b020490701c0c05400115101c81c03000b07005241c000c4280061024941c41c5150050b0408400c5c060000044900c002a611035049074018010244c02507000403c0481c84004070b00c00d20a072a40414080707540403132900c2c1696281e00388003032551141d6181d44420703c8158000d107072111000c00049006001c110086015029039400c071140c1009400400c80c421441e0002d020740320f281e807080c01c0202403950041c14200c1303000d5505a40c40c04060070110381410490040c0b070100300b0020b1325070030401610003081701e10103607041c8506401b44501e5001034008400648406110301c00d440000304501d00400c2111000d040d50300070718908541d618055543c80380c00c0301426010039190440d04078 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 968651429 1250 968650179 968650181
    0xc080709060315290a0c0c0f0b0d2a030213080c0a18020f040824090a02010318020d1a010605030c04150c0b01080a110312090121091212 60
    0x1075440b501140b000107551501c0d2255500030034031265094821140c0c1300304400509a6000303081e007840c094072104691905444c1140c105144e64012507091071300400280000c403000010703613079607042000e80007910b20712401c0c080021072807584030051000307041e00d01400400e030305401606000c1c2c420117013030084644030a582da880e025130700400c41e048030140100300071030380440c10680908002d0850040ca041100e4000c0000e6034440e810100d0258001c0c061010135440801d800d018240c2d10200c03005131410940c40e40350f110041c101000e0304054481085400c0c1c0341c40a030901c00410341c0141900345000040c0b030b18403082c030350020080310b2810500d400058014002c408603403069148030f41d02880c0a0030a0380c42050541c01d0010300040220712080710000400315100c040c06840602c00600603a0f196103801d442c1100060b1806002c1d400204981c2011441d017015610b0188090034141d904114021002e1440708080b0f00d0b6048aa0400f2006001d02c14031400c4d4501005080c1d035030b46500010318030040 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 968652679 1250 968651429 968651441
    0x40b090a0f110405010c030f2a03021905030406181e170a120c1b0303031a030c03030a031d122a06070f03060f08060a0c090b12040f060c0807090603 65
    0xe010841c031401c120f000074032854040018036040e0501050840d0098201c04007403d27807586c4119000910044c44080c140c0404c141407441c1038114007105515100c2c4e54441e22401944145024402c443e20340c5580c0c0740700700c180030010741a51075142d8410201020b40440d00d41b1503204142502c000f44400301421f06002c0f4240e04207941202100c002e40b4521394080b01d101c0c2d8045000d890300750f421003042c540e200c0c03880b0418000354007035a408111a60020480d041440344131115038420350046141d0035013030b02e0101c01d64080103518100001d202810107852494507140c1007090445000304021040001c0421700a00501030040040d048401041461109040300d4080b2004150b80500d000030f01c001c0c4130b44050a1200d08034507011455a80d41c21904410310416040421250403800411001108031303c9800304d5071045161514001e40760100a40072031040c4840902c05515640014040c8003218001c0f8a400740c0c4100e0401034660805001010741c001504c1280011b00030200006240d4400c1c040c40d = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 968653929 1250 968652679 968652689
    0x30b1c0b0907140d06020c1b01020f0c1e03030f0705010614040b030312150d05010b03190b0a050a090c0b0904050f1605030406141303020114070c11040b090a0f1104 72
    0x24085034040d0f400c00441000340f500031070b1401c0d000c010003069003c1c14444880c00e080603960155031001050300282c2090429500000c840d4003404500c00c030760307a80d80c280e0b404e00c1c034045894821741c1c1c002d00003184c00e5109400c060050140b0011f002c0c01044415400745080380d41500419840013400030400040e141d0310508507071b05502c1400380040c1010b04691190704986000300e0807001152400100f040744042480945141c3d5403a44100300e6424188030364181500380680704144240d60f585e0b000b04154002d08229030185d510400038948034503c0d07002c0d10315250800c8807000e1481c1c3d100c8a801003a8810001d1600550a200c04100348200304401070b80903490741901c3c800740c21030004080701c96410017007098030090344840c2c001102c04181c0080500812102104507500e82c01418041d00303655030002c010002803041d0f000c101505a0281781c5c440000c2e4804205030102c40140f0010740588080c0c0b00070740e4008000d500344011407000343d01001d582c40c01c002041c0140c1c1030a00b074441c4c3d40e0182e8811 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 968655179 1250 968653929 968653949
    0x109050103031e02150c0c1504050703120e0402193b010c0f05010204150f200a051204091109030d03050c0c060a0504020a09180210030b1c0b0907 64
    0x1080d83d0605983c40d40628803001481240d4400e01d0300700703030304407010020380d45030a4a080008601011500900942c006102c608040c14403505250f9034681c0d581d0105d1001401d070415507151030344100c2c0308084041300500300410035500d80e000400c50074a808a241c02d14404203c10548640131059141c03452011505083d00d00720342c1d5076566101c0d00c000306101c0c90050401c1180140350b00000c1c09451350346903182c0180c00043e01c680c02c000c0c2401200ca6440402e50500030010040030400c0d9001101e00c103820000901045a1b01c04401c0840c503000c1c100c44001d03c64042c0c40840748600030550040e00c01ca50100d0341c00e102800507044000200d100341304029402d500f0151248031a0340c003e800550708818441d201e2890210a41c7c103007405c00703100317468455419071181c050005618005500070042c10301c540c0104001500c000040e840043c1005009004420504120a00c24003075440201c1920300600b078001d00c40d1107400035002182020b903081340c5966003603010425140000811405482070052 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 968656429 1250 968655179 968655197
    0x215070f0f020c090a1802030a0b1b0712052a01091101091a07020324071205090a020d0c09090c0314120417010f0f1b0305150d14160806010905010303 66
    0x1060074054059421013400c5606c44580a03401614208041c0d2651030240101c0400b5080c407410700d0104100c904800c1200711030612600001c03d8a040f0307031511545807410141e60b281241c400390003210343e0100311b640342401440ccc4504600c500c19040340c58414495220300d140041d010700150345501642c065400421241d50b40c5005401071031000388030242c0000d04a03920300011814012102c0c0040c0040000c0440043c14085244d400900c2e40d0131450620038244a0344c601040b1184d6142900100a8802e054840da00000d000d0020b0f600300213064800418880c040345400d004064007030f648403c65440544020514140d40d02180d9182105020403000380340c2031400e110304520740350210051b203031341d560303103a00b0b5803007455612a803401450168070120b001240304290209422110316682d041c142404100310f0b030200016200c000c6070800701c075603034807210700c41c2049080c0400d1010740c0c1456125442c2c000039201d074000d600f442100c040804680d026070b2210301d940281c80081c0710090101380c03e88 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 968657679 1250 968656429 968656441
    0x70302030723070b0108031305040b06090d060e0607051e03090c19150e01020d0201141812070311061e0103020904031e0302041d1003120215070f0f020c09 68
    0x901ca0502d00070500c503120741020083d49648661100c01e80c080b102a900c00108000210203c22100300144821941084685405000700e071440c801c200c0070174170a003020101681004010f41c0031000c20081742048410300e203000b0001a006521030514040e0840042c140340483c40a410100d1707108011140c050032090ba265010300000b680e00e02050002600e01c0358011600e141416502071000c04681e4813030040c96810400a424403421700342d004116410f020048450212500c009900f05040e83d820b0b0b112041d0302003800e8148580c410494890103000140482496032041e904140c806144058441d41c0d10340c0050680411a00034802440d80c401c44010005403401004640d40603020b400c00352600803400c2420b0711007407500c3d075152012903400300301808204501049041c0a0390441d898400e207040c401003203107a907040c0f80300040520701400c00002400748244003048100701401c981041d14141003002502d85409800207400140800e40d82c000c511f4400a02c0840310500582221916101c030 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 968658929 1250 968657679 968657717
    0xf010213290c0f1014060103020705070b090105041e0f080a0b0c0304020a05040513051002040501081f0f06080a2003190608030a0903050705090c18130608150703020307 74
    0x109455403070042c00d02c1040c032040140042c404404c08403000042d000702d800a14149a00060107044c1014414080a40014070000740841583c0b00180d0083e22840c4d40c0c0012201c030300c96500040e104242441c0c0119150101f4110300b001c0e900e107260003d031016154103000e540c0750015032010b00426845400704074142c904400440d0032600180c411040d994070390340800c095900589211002400401c04482486403e0003001c1001d801a40c0c154602450640000e2032510701034941400f15202e41d0120840d110340380c90010003803c207038251241455841c44044d2504e4005c0b12042c00c13090401030004500780581701400c03649640c800000f030840d122000040244580d00c040f40e00405e94a002c00310b03007400104040e0421601c20b5890311001760462900f1800d150066002c90b000d4003044052120203000c60781640e60409944101d803110b10700880009891402400c0c0349043c4a01d00040410340c0c880c08124404c142c1c2c0c0311900c00c80c642d00c40d104114100e11040b2a8140003441650042c0c40344d07001 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 968660179 1250 968658929 968658937
    0x60509060a0e2b03030c05040609260607050d0f05010308040620010612050f0111070f05070f0b0c0d21090809091f08190b070507050f01021329 63
    0x25000c5211484542c1c556040d00d8043c2000d200000c8600d03070440d0400d549400307082400c800c68500f0b0b904040c40e005000c0c203420400e0061044408105100b2405492105081d5403007401040449282d41448100500b980d803111103003650150811001041c1030311a80110360483c0d90ac02c0c0214601480c3c10000c4036026803590088140503c4511000e070624002d0041c10080e0002d200f5422100d07203035151092414401484000d2581d060080012003002d0070b000355030402d80c000c50040300b2202c0350300e000c0c1d0038008580c010750b41e032100491000c079400f106074029103601d0b400703d000c4070b00400310144140c1d005560740c081480c084070004002001340d4410780014030003a20a135411401c02c0817800005011500450700c0200d440903e03a032800e0b03007a00e03568044000307044101c05040c52050b03207054000f082024040250007111880301180c00107100340111048150420b0580700000d0700c009500c0c0c041d41c483c8807c0040c00c6806003001c40e40011402e0603002c06400500c49100c000320480c400000c80e00 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 968661429 1250 968660179 968660207
    0xc030a02210405060709120b1609080106060513140d1709060f0d05011a091903050a050a1202010204081f0209060705010605040f05060d03140c01020d060f060509060a 73
    0x14400e4000c9070054190702030b005078890310151080349081d5100402c070035007961200c0ca11350b00181041000c521580c6201d03400600383d04120705590329000b03040d0b402d00701581c0800f10641c60100c0009450b940710010b080310f095820000707001c2075910034280c41c60403c0380c0f00f465842038501070390000007447d8840049594a515080c03c0c00e2210760ba000850395001849030002e01c40340003a0f2020b0a007164414180542466916106001440300d00391000b80540300c042030088c0e0800b40c0e5522802c17943d080c10001180e1120407901c0d1900f03949091920b41c26807202c00c5944084501e816090340b4018001e80301501c40302ca004001d25003441042c09482c1c04c016034283c004aa00f04803000c50307074585000810741c0c540940004201e43e4940018041210b078010290511203280c042803042035a1003040d600c7c0400c1e01403809142c491003000783e24096214507402d003c56588001861000001c00341c0100003103462090800c21031a9680703406032494071035041b41c1984400f0400132070024600078052141408 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 968662679 1250 968661429 968661457
    0x15010e031b1225090e030d051906270c0e010507380915060d03021c030902120a020102071a0403150621080412030201020f04030c0e0108060c030a02 65
    0x902000c100c2802c018854206411014052844001c1c0100400f8000d00620076400108060081500e5044d10fa02800740215240380d12080401c042c01030542ea9000100305811040094903a42e962264940302c0300c00070f40c2c1a10000300c80310301104003e441512910030a0340c4560301c042d03d0103001114598010340c0c0848920f546410751542c062245010403440000c0000c101005c2c030f84c1c0b50898100c42c07100404071085540f122032880c191b595241100d9400c80c10958003c0c480c80d00d1450282d045c140c103007a03900c00583d12000c0c00c0c641c0680c5604581e02181c000d44603124100d4404102030703141c200591010b40581c1c8250000c003c90110082c0d034003003195400c4c2e111801c10b600c1c0c0e0b0300d00300d07580800d80c0b50214080d20b8010510840ca4044040e84221542d40c25521222005030b540c2c50700ea0040e44541c04c1076107410300b01007051500030740484003501144124143d0b5940c99140c101c0c4008083e010b031640c0c204032040082210100061468003484603504040c1c00d66031280c0100c00a540510840c81c42c030 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 968663929 1250 968662679 968662699
    0x10504150909030c0218130201050a03180312060e27390301050618060103020405130218100912030c0f030801180603020603040224070303020315010e031b 68
    0x1100da42c440c580240b4460760756450400340c0f900401803203054600e084a6002a100b083c407040000c80182c1d03d40072942800c0043c2c90300840003058005202002d16101e001c030100c4088002c0550000e140341079580b00400c00c002d007175110b5050b20302c040b9044030b002112620720a82c0d2888006144092541001c18000311030980c000001c803408109003801003100000c11914000503c003008914808800308160001c01884ca04400001c4c00b0010843c45a00120b00120206900364440c3e0100c9002d03003c0a0301e40714007a100114010020b600684480003000400400e44040d881d10a001640c030178110340d91708101609200c2100035203140d1550807010b00402480b004000f51b84d0f03407007068100b13019840b90131a41d85442d05c0020b11384031005104c52007516083e020300059883d10140c9810940541d0840f00b881043c0029040030004548840380c1090085007103030405501d60010f503c00d805820300309100c0f0400b00010f6600007070601c004c541c103410030f44010310b01c0f0825140e90180504020000c3e048 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 968665179 1250 968663929 968663939
    0x306080c0d0804150c0b0105010c0308180c0d200928140f150102070b1c0221041b030b0412021c1107080d0519090e0a06240801050415 59
    0x9008130f450b0074040403508400c5104244031030003048900400c1d0a08020740c007520103035001440128000c109070340c00b00394050321441c112130410950707145090145c0440b5a10002d070822400705240c664a000340348000d003ea804040c249800118010009039840000c1403842036000780d10410010700516500e9941e5a03406d0b0f50050284040740610120141c944003401c152043d10701c403110026020b41075500c031500130403482c00c9000031203629010903000c0c1740e43c400e0050003a2008e403003800303290b080c01040c5510301a0601c03101c035000703402144103000c00c040003c1040d0541c000c00580344009413055034404002404900038485003044000e0038816540101007603c4044e130b06110b910300680000388109022184071400300540b00140c4030000041c00342024600c00282107100d0b5410b14803581034150004403259010301d0554029104410000e600d5107002c0121200800c058491224050412000c28540c0240351980c52001c412581ea44e0703410368205802d100c0a0300c0e0808928400e0340c034411001031 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 968666429 1250 968665179 968665199
    0x10e03090603041515270603020603180f0601170d09210602090a091a0915120703061109100315030b1e04153e07080a110106060306080c0d0804 63
    0x3015000300c0b040181910b03071b4200081c508840c09154090254602070090007d6070751b41043c1d035404012040c015116070180700c0098100722116a01d5015441004004503111600071800c0c9c1c624400c82d008c81301f0003c581c0b07400b103500c0d0b0014800c4038150000095031150408a03c0c42c1c280c0d07c0703070044001524141d040000706807088000d44c001603907540d42e12103c40221243d08c1e20030950751000c480c1810b003800c0c912070340030980340c8200ca441d00c540030303028146041c0034080c444503008581003002003210322041c4002c02459070040c0005807207034001034a00704100e40030f48203034400725115021500e0b5041c103650301e150b07542001804011540380d04005400b408103000c03859034401c03407040001c035810200c40314001c815900366000c48071692800d840d03541d0003460658000c2403000034047c9007901c0d00c601030300c054000c2c0c4102c1001a00c410000a120784115812009909000b0721240080050030303075425048041300c00c0b40c09422000e8006100d001680d1800c0b0f0481c0d640140544c1d0800c0c0b50650380c1c41100 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 968667679 1250 968666429 968666471
    0xf141207020c01030b030102090a0513180c09110406300903050d1a030a080f190206070801080607090b0f091909050c070f081b011a03010e030906030415 67
    0xe00682c02182007035070b5541e05011300303124607400794002c1d4140b60300c1d18001000d0f40080d0041c20700420b10086840c1d084e00068000c17403424901008400c501002605010410300981e001e400700050401c0303c00c0d101c01a007a822a41251200e90715603041c921210f00f0781303a00580002c092200005501b8119203120ba40d0301c0746610703007403086d100c0a59600c40180306c2426100300a0b00c0086101001c0400800c40d200800c106000760342c070082103942c03948403550001c0240601c0e01d1800d074003641c031101003142e1500082c0e103034050b0301240c0340d4180607a038400c4050f98820040f13480c5d1000840048003041007055600180c0030800c900c60b142800c0518035400719031070f410400440c2d003015104a1040040c3e0815200d955000114002c2c0640317802c106440e980b2030320703400841c0103001c0070380051484584901c0b102035603c80d0710310764024088241540036a2908010a082c03151095207008403c030032a080000860707201440c06000d00342540d60b140c0301c0c00c03550000080e5030910961191a1300a1070b4040c0c0c0840c2c = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 968668929 1250 968667679 968667691
    0x2040e0901060f1a03130b0106050a12020304110603131a190b1003110706020723030903070b070201050909010905240901050d02010915120b0102150c0d0b04021b1c0f1412 75
    0x142d00d44401080081481c491000034502c0300d1b10400900001c5688520302ca0110442035a0484c1d0301c0c0c490844f0b1404005e60040003820020380103801058508410304000d0103080c2007040d250450f02c403a0303114021580038013012903001ea06031040e058218000d400440351403020541031800c189050311103400760307032000500700d1345290656020280036280e81c071001c00100701c540c002e44c03c04080c400825510308250003500c001d00008180d8404680c071a00c100c0f04803042c060224502569034000c0040034060565814107c54640c0040b07611465141a110b040e444009018801d00e92804080c8480c01c168104e00f81d04200058002048026134070380d03041da8182c01680e0744243e107139402e441f0500700c401d4034907110b04541000b41112001c01c1c15030202900440f1205901c0d55840004081c0001801c803191802d0b0410700200b189810212260300094034107503d18145d8262410203804510b240600c5054600800d951942c0c1650f00c03840345100000814180b40502d2500ca400c903540030a6100450351 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 968670179 1250 968668929 968668937
    0x30090503090312040b04090b040b060d09020108010b090f091f1418010311130b04091a01090204060503011820030612160308090a0902040e0901060f1a03130b0106 71
    0x8141841d00b810402c074246030380d00b08012803c0c1030804c4403403003a80c455482a809481c4e180e14049080740e5a9520004901c0c9004051642d06c3e90040054400740c80b1005050f400b00b600d4800000340001141304030b5400d0300004042080d4a84810308020790484041c02c80c2008141d406984820001e041c4400c00c094502034002210b086215400c0003049924984000801e900d99401040050710a0452030301c0c0034002c4540d0081d44080070b051600400c14182c42a038000d041c0107030344090080d980300300c4031501840d40c042c04039a030b00c5401d400e09900c510712075080040d10801c0108491000e0484004601c10307210380c0070800c4180e0b0503111500c85000c039500d00160400109105040c5840a8094200c0c8940d1002d03114148045140c040368540510018000d81703000500018280d603440c078050090103034084115240ca44484841d04c000da0708a80d54050f1390301c2c0620114007001440751400481c0c00c0b03c451034080708150880d1800c190005401a001004a400f207440041c0e09070b24220301030141551 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 968671429 1250 968670179 968670187
    0x3060a052b140f03121303111c09050409020102030406051e03011508161e030e191703060d0602180a0303110115030b0a0e030d020c0c01030608030a30090503 69
    0x1c1282030040014260f40790368003c01c00000b2052418604035804490b6220303000e84010b150400b52121402c126084815000d41030425040940c0c0e091560b0541425a448441c00b94540341880110303000c418019016078014801000751038170500c010703c40b0340c00da8070007070301c0d01d042c0082203010540080c5c01907200d01404010002c40310707030301107425607201d03050344d0b08240310441007000549190213440000c2d00442c00b14160581c0580039402c0044150409000c8a0408180815078904006070403c02c0340c0e030325800725000f10450540015031b806100010b18400b90741142e0b0307480707400070360113010481004902051103499a035984080800254043d031141200341e52030500c0c003821101c408192112068a241040c4003180c00a85901d5002030f85541c0000c3c4516902079040c0f0714028030140381295800000d901c090030401140f40c0c81000703801c0c0c03418844203031580300e00350700c80c041d0b000300c100000c1d440000e0340140e21040181d1122000840001c150152000c900300781620700102e0252038643c8001 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 968672679 1250 968671429 968671463
    0x120c0510090209060616061a13060510090608060405040c051207090e0304030503070605090c1e0a1706060f0f0301022205041107060e011127010503060a052b 69
    0x3c80b080c1e0010701103954514003411039040c411844070303201014007a0703540c42c0b481c0000600c40603080a45140b00600e40105101103401c501e02401c8240104e41c02800864089240c0724007a09006007a1500d98940d14215a030709401c0c04018123000340140d07124842d6000020b029160031600b03400c0030b4049070150007098100381c0d0020a03182c1d0001c8440d91a0f10400c001c00c081500070054491281d4000e00204250f1502002c40b4644070706503143c550f100080301005051a40203020240d03030608140c038444031565840100e07560300d040c142c006c0c200e540c020100094040c50200301d0400c420b08000c10303c908074680c840c0404c4c00c9800004124000203140300003c041c16040b20103080051600311001d0000480c14007840e03400c3e0040310720090600703442d240d0321005039070203401001607881160b0347c0d00d4a48143c000c1c1c081030441c0c1884680c0f49111900c0e031181d480d511940440e803007510042c1c213501245162001f80500e03c11161083d000c001c0b030b0701c1450b012030103401407454245800b504011400643e40 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 968673929 1250 968672679 968672689
    0x8041707200105041d2502030d050f0402010e27090102130807120201140f0304200d0c0b0a0203041a04150c170d1404031112030f04120c05100902 64
    0xc0346414042c0c180003c11008290701045c0f02c10781700642801001d500d6000820546810f0004190001200c3d001b014134141e07800401f420040190400622050b150900e0b16840340d42d0648010780020300c0400c200381c81e030500e00e44d0103110031701642c5040900034958a040840c2d900a0f07842103d070365000500a042826001c0140003d84024405088441d140502401c5061441d002c024184600c1068041c030306c00400c019980601855645560360b45041e01d403d80303000300c1c401309603003a458034480300100ca810441d120040a81e409805019154104600b11160303800c900271400851000308004503004858400e40700000b03c3c501d21107900d490901041c650f003ca000403045d0204440c40d500d41c0040b5202c2d46d038140400442c0349041c0d0f0359030105903088001d01a15070400244a4909040c03104055209840301183d4500c10305558040145000782c000c80d100940d940741c0411121004280412281118006100340e1402c00c2161114185c2c0c549040508000358828420343d039050740c0c0154106 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 968675179 1250 968673929 968673983
    0x10240e09070e03101514030709110d0f2903011517010e150106030c030905031303020306070c1a0a0e0604080c01062711090a03081308010b0a0608041707 67
    0xd590600c17060040d20300040344c03085903118100209107211156145518240a58401b03807150b0704040c00380304582c480c0100a40c1c813052100b41c3c1d00380f40444801e4100301500c56000f40312209007510090408444030610301800c0c0040c10340c1e143d544e824010054004d190b640e03500410100d01444c1c1442c0c40244a01e003100d2125180c202a50003240c041031720700303a504901d01e040d90100c5c02d0004d10352003282803c40040c0300404001f8500d04c40000c01085040126050302c04a038403c80846d17036030ba40d0303400c02102c0003c03904000402201c0c1100c0d0301900348041002c000e0307010b00d86030000140c0c800c0390b109017450230301d040d80c054030024000140c082c0c442c0b000380240000381118129801402c1d41144003a001c04e9611002d4541b510b40d121850b8003414080740031100900d0700100001d04958507410080c41e00d6024175080380344854201e000194040040c040c8805160740104087d00c0300d4504001503c2c840310051040b21a0a5018590360392103070940007a1280318050700201c05c40a004498610300981 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 968676429 1250 968675179 968675203
    0x60411070b0a2a050715021215030d02031c09020306040f150606050307111234080f0d020d02130e1018020d021306021510240e09070e03 60
    0x1004120400ca40c001c640443c1c0d003c2c041490143d54072140c81c01c09880c420b9044102e0107110b40006a110407140b41540c0490180e80b9038061960b00050308801c065850f6040307482c5c07901680040c4200d050442c400341101105024000780454034020300da00090401d130040b1800c5652020003a448000d025081101041241484408100150409a002d030540c0002810740080010341514258128001d01a0b5040d80d82005043c030b80303513003c030301420003a007080000c9444180c0304284002c14500c0c140e441002c04039008004d446c45c044a18101d02069030107000c5040c0c11320303001c1003100042c0080744000e00f003d406d0010840409801c1269860180c1009407420020541d805018003101c5600c00c68169001d030210301c0165600884035108001c0d00a009120016103084040040c00b5600811910510450304001c482e80e9030300c50101c9201621603000f4500b804284842881c00e0a040c14002500140c0d142060000d10021900140c40e44400b103030802c0028242c2e800b10203a17414104030340e00b0340361 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 968677679 1250 968676429 968676461
    0x10b0724140c0405010503130303090507060905040e01021c2414090c030417090315010f030507080d0c06050a020412050109030207050d0803041112030408162408060411070b0a 77
    0x245444c000802d5400f020700b00e035000003a841804404c050190740030f10089540071040d56800c90341c3d00006054400f0521a1078001c038101301208800b800c041c42210070841080000c40b602ca188001c4c03100040156805094141c00840c031458455800f050f1118001c24102051950104002092090f40c003405008808030740c40c1072080c00001841a002e10074000361001c0a26115440103001030310304800300c0d040081c0c1c002d00138004249500105a68001d41e409132003120b1445030b49249040d5160903e480300800a5201c0506400003940741c0c004a8001c2d442e00e00260a154503000484615007080008503990ba644ae00c00d0410160140089401004100c40501908000b44c4070324545100040c0002c16103140d03001c11880c140c1e100d640110004072407a045940f0f035034407801410342d10841e10501546000d8800c00014204005c101004000711038800c402e0500c84064500b82e818060240165500648034107000002d0b54280c80a840600e00800c00741c4000d007002440c85003141d90300e068101c176507 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 968678929 1250 968677679 968677687
    0x30309090608190204061a070b090f060406110f041203390614040b0417090a0608070e0301420608190c09140d0b010b0724140c 56
    0x2800c0400d100100103143c0e00c5a5507400c00314400940102080e800444503011220b92140d40712007240c024200d0b4612980111a294561418051340c3d42420103028425a0207100000c3c0020180d4003e9803d000e04048100e060501043c4c10041c545c119411010356120031001840915620078801020f691040c6a071340da083d0f902124030ba0080d800d03a2103058850341d9085040c01044a5540009001200154202c685090a14004e0b91001040d00d0941c0e903400b400081804481c06401203803c0b0310030043c114001145000340954040f0740c0108994280104058001c01548003030240c4a010314200c3e07445a41d2400c032440001880041d450401005003014001000842490142d102074403801c0c05c0041c11540c41030580f2001030340c83c040034400b460802d00503030549074000c4500b00c203546100420315141500807081c0314205100c1c500150090780384a00411040c00c1c1e0800411200340900040b0315407000c00144140d80d80c0c1c0c0084a05409540c1d04012a480c960740c1d00150f420403003442240d850 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 968680179 1250 968678929 968678939
    0xe2b0807050d020903030705070311120d0f1d032b050708073207030312020a020c120c061809070f0206060105131e0e3417090105010303090906 63
    0x140c081c10925440d40b5500055101c090740d4208152015190300c801141e00c419140d141c410041d14104048902400d080710120382481e0380883d0079801000180d03110060550300e0355085800c23a0000300c4101d03008940b0307000407009481c2807094440b0300b0144820811514020b401d11454a640080301404000d810f1240c0d00010300c00b001159521508403415811000002c41d1142402c1c0c190600b602c0c01440600f40041c1b0810b0203e00c0c0e00c2220300a0315103219500c0d410b441d94050323128022208005030040d030088500f80c074100f161000156414402c03a10000054800310f00543c0c001081441c0100320111070b41d0070791414200030b551114003413801600405106070b000e0f6503a4006801103050000c04201020741c0c2600d80c460030000d040c0011480f5820845002d1114000041d008411280030401d00051194902c4d4010304416208109400c5c2e1740c0d00c1d1910361020203d481401202040030881d007100000844100450044400f0360001034654035600e005040c505465010300103a5050001c1002 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 968681429 1250 968680179 968680187
    0x1e080c030403030b03030c0a02040b040b06070210120c11071505030f061314060f0a1d0c21190c090501030c11060702071d100510030e2b0807 62
    0x508694148a6203450791160b1400f80d01500318a5000e507014480418030f82c00c40e0100184c942010340c003d4804210760f490020900c41a214020405034000e002004070034014201000c0b04410408140307041845101140e101d002680c91650341480007403d01826051889414040310004000320f81001080342158840601035000c001d250441400e80c96000648030386628100b4200403c09080c10416044507100b121404041920b00c640925201541134000742003440001094494058a030580d00094124000d00e480b802040c0d0110b000c01802403254402440400310400480340e854030119240419111000140d08074004903128181121181d189800100c4441924428070300810b04240404083c0c41000360520800d40d688120410400e08507408a4004250340141008402210003071241038081407061380e25002c01160741008100ca89001641c8000b81e0f0680d00300414203130448110141400d400c80c54180c007441c2c0c044800f20784a0b00d4014030000110090400102600340450010 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 968682679 1250 968681429 968681431
    0x11040903020a030f030b030d0f03140103050c040b03030405040504050a050d020c0901050d023d14220b0301080a0b0c03040c030209090703150207031707230903010c030c1e08 76
    0x2c3e040c0002e55441e07905880c4250000c441c5440090100d411504c07401e000249862070384421100082d00d0480b078580b040d5000d284007030413a43c2143c02411044244410800182080340c80d15501d0b1004000010f229260350082034411801100a03042c80007032400c04904195100c80d00c80d0864001c1d1150b90705a60798280c0b410b05440081e24a000845140d100ac01c40c0040032800080300c0361107141101c03a00464400c2220300c408a00c0e0801c842e00c088514040d651b0640c91825644428400d0026025040c03490320042140c03c1004882c8070501d55440540c95103078400c1e00101c0e02504062103810a000c40c60700d48a070841c54141c400343c038618040d2600d035142125400001c2c03060b84441e01144000340304008100256030030904013169051008030981c000e40c1300034022000b0408214004e101c07445202680c0d03100f0442c5403141c402000720203803420402412040003100c035500c00c4c4840c8145031424031914801c1881e030703240042e81e0114403601400f03181005402c011039640c104008662150300400039 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 968683929 1250 968682679 968682683
    0x2012702030708210a0e030a060506041104061709120406090e100308161b08060910020301061b151817040b0f16021203070611040b03060d0317011211040903020a 71
    0x110340f074904619085a80030006c0302815454030032200c401c07040c441c05a01440c000d46046038208400c24800315216158005c6101d600c0c0400c000c81c0200d86050140881a03034814601000d40e00751440b100250985074009402007800a100c0340014000c0c0e8040c22101600904c00c0d10110209031f10b140c0e120201481000c03203201c100202c22450604200c8130000031b030500b1720b461107440710303580d10360096654501045a14803094402c8103001c0c00708020510840341600c03030640e10300300256880c451a41e2400580c190444181c03101c002c03030306070300c1110340304152881c81c0c81d0046044800ca03a080824440f10b59103d0011207070410031040040920709030171614511400b41e5240d440b03500a100c29000103506840180d04044946640350740407a002c801091032900c03600d020000300382d000b42c18500d54011070181005454003080401c009140040e082280715100307291091441008042500301c480081c1c0c00082c403407c0032079505080099070050480c0c404001d440800015156480c029034411000e04c0c0 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 968685179 1250 968683929 968683993
    0x80c01030612060b1306140a330c0602030403211416030b06040603020909130c061103130801050603010e0115030b06130903050a08070e030a06050702012702030708 72
    0x402a10358591740d1107001496224a010801c181c0d96a107003c035071a001d18002d41c8034071441200855510900c0c003000d408491641018421219403100101486d80600100c0d4144805581783d00c0018800d0300003584514401e82d114405000c488400c41e800300c19540104000303a0804150404007403203508041c0d4800720848032410034801c940000d030010074008034201d80081d0006404612aa090b40060400f50020307103c49003c0d5072400301b001c00e0408000c80c0100300900662f0304010281c4101828050a031402090b01c2c988540c0c2100d00f260f0110341d5020000507512541000303000e290a01c0350680025101e00207109000c401c900300b20701c0b0f00307250000400d910a0507001c541e10740c0b03034421a0b00f824a1120b00400010a90707043c00361403900140c00f04400114003500280600d40b1403080441074000c007500a080e4003900e50346150240000410020445d940ca0426400e10015094000d13000448194001c02c20b689500605045c0b0070107401502c41981301d84208841ea5400d500d40d503190340e01d4120 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 968686429 1250 968685179 968685191
    0x90604030f051b0d08010b040803030c0d020c0f010e0d09031a07030b270105061801030e01150f03051e07030f0602090a03031d0916080405010b09040309080c0103061206 74
    0x10260740714024440c4280310f910407802004050100018680681c5000341c5805125a9858460510324829402402e2540c1c0040c0003041c42c00311083e02504c46441544400341c00d00540c00100341c0750002d000b581c922503a440e07a40c0720010801c1400219121511841c0041150341544c5400f038010b4401e0072007030401c6d100000024216803203070784120045103009003505d030403942110030440d00801500280100343c862000001d030507c1c01004840c021421002070ba00c1502cad5080047d4001c140c291071540840d500c1e15002c03541d0b8003014a6140241090441c040804c07400c50030400d14204c0b102c415035443c84404200c0d11100c480000300c81003100c1c1e10440002480500c0d20b0201d001e4014403c001e80c00842c03e4a020080581040e0030031226816482c422005c040007a042014100c41607a01000740300b20558510b80207407268985990040c01500040345017000d003000300381c1600c411501540041c1e0030503018000440141305c503203c1e2000900e424464141440c0e49e0503d96030a1110042855a6841d = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 968687679 1250 968686429 968686457
    0x1b0509030706440106090509060607020103061e0810020c070e07050c06010608180601051c02031903030510080f0601151107090b0315100918062c0609060403 69
    0x841c0140140b024640f038041d084103000c0000c2c1c0d4000980e420300008a40c2c0e90000c0f5080b8807580e4000300b01c0350010701c05c10181c0c03526414032049034041c220590415803541c00c045501504d80c082442004d00580540203080e160022060600d03082c0d004000d03203180100b0880781448400280e0074161035040e02c3d0040345407620784080e5410f129654148080340102d400000d91141c010032850300c203000c8030f020f1a4100380721801080d16017000b401280e900400341e000c1c2c06154103501810400c400d2000e011106912580c21003030110f011000302c21400240c803501004240049000341c2d000030003480c0c00800c5050345034104c4a03211401401102c0e0803a801480d240b5505205000d100c82c03030350030042544d01140e00e4100c204003910000d412540248a03180a1240101505605a10070120016000901424010b454010340703d800b02d0740c0c801c0d0381141c2216011034030b01d1007404140481400b14134000c8a52600700111500e0920701e43d011600b0201c20030821003004a9580d50045d854940600703e8003541e = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 968688929 1250 968687679 968687717
    0x70309051c030c1e1b0f030804020a0509071e030e0a060f062405030a1b08040203160e0612011b030f0b0126070912050a060b0306100306020706060b0c011b0509030706 73
    0x805c034050406101601d89809040d00400c2080c00340f80242d4500030307500e403603d0a00c41400425100352001500960303052026a440003104500c010540c600400c0c00600c00d20094a80100d6450a4a00581e00c80c01240701800d035100355401488188201069003a110000c0c2c083c01803915041c60a00400000080085c69940d210144055001000400c49100101d0051244404036030407402440340148050b6100c1d11004a4401c0f94142d609620950b03035281c0038031502d40d04007a407001c219902c1e22145041e082d400070311415545079942c1d0003c0d00340c0000d8610415651029102414018aa51a0146c101d403205d00342460450090130111642c4032400111420002e9038440000d0b520b00f000400104280414030000403400b40e4010301841c1544010907440300da0644030000851002001000001d409401500002d4058540020300c4e5035150400d6100760b014034281e0031030340d46d034102d024090b0003d420140c1881d401858031509102d001d0010a99510040c0110340038041c518041e948843d0302 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 968690179 1250 968688929 968688977
    0x62208010c0320070323030612190f0c0905010b0304120813080c1f02210f0f0c22180b0a0902070503070212010605030f0309090708070309051c030c1e 66
    0x1b410700441584481d8003d4440107401c10b0302e2141c07050060141100e00c201000500600b000b5061600d280000c400c0e640382d29914545000445180041400000d5178400a104403030090036140d07003240ea070780740c0340c50701074020341c0e14070907200600880c0c009000c0e8400e503c0c565110100d03070041340140d6402c1d1900005291850900c0c404d00304491441400250708107903006424070002030514140d0510900c02c00786010382c03084801d4800110302c07000240d0005102e4480c25081003038012414540500510b40d003810034040760004040000c1c0160070031410706581c200f600c6076603800d18104902840c1d100001c107201c1052154100840d000300c1e0a4052203018000c4400c1c10b41c0c002c0100400c00482c0214502901c803911840b03110703000d4244800d0300f8001c0881243e082070781c001c10084155550034000c1e00d21190151034001099510304a003800104104001051842c0c5840f00c0c0d1b00400c1102d4009042c0c030040700030413082010841030504925060070300d0050b0510030b418003103001c3c004400150014a0 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 968691429 1250 968690179 968690207
    0x110405040809041b120b1302030c250210081b0901050d1805060105060403051f0b030a05060f0a021e09150f0705011802030318062208010c03200703 65
    0xc644454020140d650f0813103a100e40115132190031828403007420f080122140c0c10f221581001c02c4070f600311154030540c0c0c01580e02580d0340203628144800050044131500c51100481c0c100c442c4403903001c055291611000344900b5071882c10a51a00d004503009070010807c1d4881081b2010108411310a60b00402c1914180881403d0410481040c0b46c2000803101d00540182c45034094000082101c1c00c01004031015240c000c8000c11025156a2089900c0152900f00e030450f1903036843c2014441d036040c4000348529014900030a4541459480e8641d0044041c10003613915104010b185420350348a000300c444814070506075500c400203280401e098002c65010340c4040c0c00000b43c03101210204801a02d1214002c50080102d070b08011810a00005802c0380654107601c1403010b0010150001142544450007811490034220907804101903160b002a1b8206040740b0030b0800d0200000900c510f81d90f040310b030b00d03041c03103800d500307a4484994100c46020301c0b0085500040940034580140041d1140070 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 968692679 1250 968691429 968691431
    0x717100b0c0c12010507171302060a0e042a050f130807030b0606030105011d0d02030d09031703131509080703030902100c050601090e1501030f12090311040504080904 73
    0x400c2003038040d2a21103801d802c500c0340c5541c0c1000c008905051048a1040169480c0e121480006004110201c034006100c1051001400150b50060700d1f943c020307100341c0ca4141c0710752064442c600304000a4400d109036120034410074100102074644108414440344a40e0700300b240c1e03111014042c104032486801928180c02000306800140340d000013800ca0112030180803151205d4480e042040780c0c0307100030312400b8009240020821020038164000e9022900000d09030f513164415540481d0829040c0703c510800b1503449402042441070ba0007100c041d2a4404a10f68034515101507004080228250040c0051080d84165585282d1035446000c446800107141610740c0c5031803800801038442000224040c00813100c2d120a03c42c01b421800b284c007540040900350700d070700348074404c0010b0014030115400c900c5040d45070400c1945041c007003030181d402050039079800003050804000900d0341007640020007407092001c102162901000f5008503900710340124031510b40e42006d17080c0e4019003035980c0d80720b = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 968693929 1250 968692679 968692687
    0x7020307060521070807120207020901060e04060902040510110a0b19140403020a0305300f131110140d05100504110f030606120403020a0204140717100b 67
    0x150b040805801200e00c8421001402c4480c0f00c51590524003c0d214600411101c1c800700b20300c1c07405a40400a40084400c0c010705019803500050200c201c2a48071002050605105030424106805180085c00d40c00506524080c42c1c00049980081815001410400d14411112041801780703d45000c6540003020300c48581000d050802446c000d0210032400646440d40c0b40392140b0714098041c0c801c03500754000c0c0011807041c0d00d0540702d03540b1101c0511000005c8825500c8101402c8142450782c811617219400c0b036241500b0700000400b03010713000f07030080180040c04000064505040118400055400b4002058441000c0e03c80029443c4010641100440c4c585071503a000e42c080ca1060020800c88a0b40782d59800c14070084a0048401d102c03a0b210801c801516005290011074202802900841c5800f038055140401030030261000c034010307086505401c056190030f024000945428006058860800300c0c40681000000803201c1404008440003030001030707584040000a201041e4000d0381c03 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 968695179 1250 968693929 968693939
    0x4021513030b090c010807081f12030201020408010612080328050c0306031b060d050c07021c2a090c0e040501080106060206100803120a0635010b0a0504090807020307 73
    0x10070b241240c1c0c84565102c0d40750982c5003588114555401401261140207c646941c1249042204980d2030f035081400969400507442c1c4124000c2c141060090740016201c605012045003500c03030710b40c44034004c43c2904075550042000501183c0d0850f0400304003d00c4400413007441c14a605901c0c0740c920596103420304100c4a031000c400210b125560403070a45040e80111444020f001000000e0142c1040d018098122072075101e620280e000705041900ba0704050044d40000d035403000d015040e00300300301010702d80300410151108036480f1034000071100c9070b814070820042c0764441380d03032040d484040c0e1110540b89010303001e00e441c5511003502400520107581c4802d50305011f0310107441f8080040c0319500c006138680000889682c180d4414030041c5150850b42810012080009010716080d540d840000088109031021092000d0008511007454060000100106c0005010304080e00b0307410700d0031108255a42d490403406035403080314005074060745401c090a242c0650040290940b00d242c07000b0231 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 968696429 1250 968695179 968695193
    0xc0f030a090801153c030606031202280201030906050a02040807240c0c09050406050f011d04080a111b0f06070b130201112e0c080402151303 62
    0x20940302a040280281440d56030504c001550070310405c1181c0050868000c410100640e20102d00e044002d90110261424840c01e51000c100e50b100311070243c0d4407070040040040c1c041d205001c03049540060008000c40d0030500c0350200803161080040c0041507035000440e8000c3e44080d0083c2d8100f841000305242c001124030081d4020f0042599600c40d0003030014200006070800303000c0000062028402c2036999205580300c003801b400c11903005445c840e0118407413071144540780c456405102d001c40c0e0380c00c100d0442c4071400d1040e00845003081e800b160b18030009041065568000b40e2064000360340c2e2a96040440f03420a042c041030760700780175011034a520000f80403000c80081d10205c038071220888158040002c1813080d0a4020300d000d09a1000501017a914001c11903814018101004e046c40400ba4541c28103201c0e05a05a0011040d0707034045005840d8031552940c400f40400400c42c200c0c01c0c00010706801e070010070003803050f0441c0740c1025118001e1015583c98144550f41d82c00300d42d4403894148 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 968697679 1250 968696429 968696447
    0x6121203050c09180402180901020406031508061609050a03031d010305040f08090f061909172109062a070b031815150a0f0b09060c0f030a 61
    0x8000a0a01011405180c2c0b0030b003c491581000511203000d541e02d59024501540c0020001d0707034040e08041d00200740845140d0068402d03c80400016501e03810050050111800b00c0c0200c07080d80c000071000d00c06560300051058000790800e20b041d80010304803408540301899a002035811001c0e01c1800000c00d5003025164443c01e00e161900c4100110f003500450440d40c0840303016166041581103440401c034200e0080c1070100014040c503185c80801c0001c140f480e4000c0054040c240502081c10b00102d502050a5018000d0031032404400baa001c040c0650390482c4601510306c0a909400c108a05d00300c00b000c580c0b455401070113140c2c07140701b0b4900c4c25407910b00d25014681401750a1894800e024000f00c0e6400642e200030000600399120740040d500346090380c0c00c103041c1c0d0340b00300080090108848818584540c1c1040a00040f0304409400e00545108a900540d200d0200c410300f445444820070540b9501d0409032035064030ba04a0300d83c12440d15101c42215100c41c04001540100164006200 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 968698929 1250 968697679 968697713
    0x70b040c170f0f060c0a0507030905090f060f03010b01050a030b0a0302131e09380c1801030605090c092101051e100b0f0403210207080a050a03120612 66
    0x40d511070900b85000c01c4d11030004441c4a510441d040210350000c0780124040c081c8103000e440c10103000c0b81c50380089071002c00180c40a0000d030441200304400391030020100101e17081d09400034483c04500741b0000e0514045e881905042c1038640300100516110802d116004640040400c104081c0480340540100320400c01c0320080450b800000481103201c0c05030310f443e030f0f6110210224480388501c1c2030101042c000080100c2c103035140302d070043c02000c07128003070301540a40c0c842d0b643e40c0e282d0460310411300341c0c5030003114141414a08204240d40d038540c2c0ea0b41d4130241c45490540d403401c0803030010f044000c4040515251803142c5800381c07440281580720910920149031000c00190b40e180c40100b210300201e40c0e94041201600702804020f10b081d015002d440d0518008a0602d5140c0d03030b07000c0301410704040c2d4440603000014500c0440d941001150300504400005d407850b144c00e51140380d16030181f07880c0034007480401144c00421200d80c1c3e2040c2d00804810140c44460b226901e0034400309805000300d = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 968700179 1250 968698929 968698933
    0x10302070b13050d05031e13050f160501030b0607080a02010b06030403111e1009060608071e050a0302030a060510091407030501080c0a03140f0d0c050f03040b070b040c170f 76
    0xc130301215130040c01141d01810206a0701820843c85002075813000308000d0003041d006281d1000c1c0390004600b004401c0042c000e240161000e801c040000f00100c4070107501042c10141810900050794903254125000b843d00030818903501c1052400680c050800c4004094011078000100300601d40d05c201c0b6851408240d4064910032000810b0102c2001c00407403449216400050125600640390340c054006140318a8020406556030142c441c24003e40c2da10100001e442c0081c02c98040d06094602006803804444003c0824119000320f56652a41440140940c3e601da01203606850030841490041503007190500100400303280c110615641503e202000c00d040c04004076100001003000c05240c01d0203840303003401364955141c4143d1180ca218105000e405003101d26400311105000743c105c0ca4803c0e4231601200c90480c03600b10300d080ba007021450384541041c4424000c0d501c0d03041c1220f0189030010700c505865121070902a4208900782d00c010034421846108202002c004120b28429a58944c1 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 968701429 1250 968700179 968700193
    0x1b0c080d080c091f0207051f03060f0e01051e040f09031b0201080c0d0603080a050c1501030f0f23160e0c0d1d011e050601020d1d010302070b1305 64
    0x3810ba0036010784940190701c240b03001c030521000b16000820404244243c81141d00c860359400c04602540c01c151000c0303440e00c42a0070011030040d01800f030803004040c41007007110400d15000340166144011301490384a86d070002c0500910030820004810003080c0203108001c14440d00d10114000d00741041d046001c51000f102416141b485151118010791f01030311241e0031076072600d0100c0801e0b403040801c04208c50340c03900080045000c0d140903101050254580907a07500405034918548a05c2c00c031411890304102c40144006000841012240e550211409080c0040d51511307480160000c840c00c540064188d140300e14409c0b00003005056074050007941441903841e40c0c00e911002e9811280d0128400c5e0030007020100810300d5004400312403d546000b003031004404d0a6600303640314820003078012026219038a005084520605811a80900050111138580c202c003405800001601580c1000032440160740c590003070701103900041e8454590320f020b1070700d400c107045041c111020540303075441400 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 968702679 1250 968701429 968701441
    0xc1212040c091515110114071106010b040608060a031a1f0803030105090406090c08100c1d0f0a150903150c080a09050c130f0507050a0c031b0c080d08 66
    0x40310718841496074a0b10762506a044c5201d80c0161803900c003c2404101d2030041707801e103075202032260381d40301e2141600c841c3e050304011000400d6a07103652550861500550700421001007460f088a00b20340b4181480c003215624000050040348250384040c1000c40109030791100315001c560f84612420380e1920800b60180840010800981c460207500b090381d000b000144058a0081c409a41c0107102c6c1d10003107400c801650314810848010b42c003203d03c50b44100c80c0058131100500030380e8104282c40c03800c00c900b613240400d0660441d02e070315180d500881d40c00c111142d407600c91007a0702c1c014000b01682c0c8180071a00d098010710082d440d2105035051038800080e80039075440c6020b000300304080355550000a40700c0540c00e0004142d4418101d92600c11407051040e9a00c980c41180a000e2007840001000e01c010300000040e9a001811541045820801c0704005034020b56510217403601413a042d40b0b1852404072a001c607044002d000b44c5104803c90700020701040000383c0c44400b603810380c1c500d44191a01 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 968703929 1250 968702679 968702681
    0x1e060810060807121b05062115090f0405011d0307050f013b07140405070305070807030207051009080702011d010504150e0d0c0501020708060105090406020c1212040c09 74
    0x6008021a41e401c00c116580030400161008034245c10942103169020b0703030345001880540c02200520300b0380c40d088002503543d896008065900000b1b0b00031507461001200c0c00a00504c500401c901c1c580940000400c0c140b0400354080030743c20a040c4010000401c001ba4030701c2da283c100c8481202d451041140c0c0340d00080f8180601c4500c604c9406a220f00e8404041c001350952101c0062803404009004040700503000400c146802400c10b1500802c2c0401840140300684800500744401c1c0b50401d418086040d500c066240c0e030010092030010384826003860310b01d0414070003801c1e810a8070f0400003101c01780051900102003942c0700341c0318081c01100102e5803495142c04001d455000c58428001000b407004034914644c1030840500d4000c2208081c180001c1c1c8404644034140e9903040088003d200950b010000400a0021000100b4040d80b40900180756440002c000402858002c15419100c0ca410007048098040b1480f5090300c481001e40320380c088c4401150143c03071400b0030000c0050300c1162 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 968705035 1106 968703929 968703943
    0x30f12071106070f050a090f08060a0501060f08010506090a030b040c0302130e0c2404060c050c0a0b0936041103030c060403031e0608100608 62
    0x51400200641c03204485410154450024085604d030400411000080140303403650707036000490000c40e0301e2441980440045800440d01050351080807800341d00c82c040c1c0000400c17451385e071264220b804503180300200303011072803e9005200b0f81c1810740c01082c11704000fa000f408025520b5941e03540815003180c040e9000300390024103208514082e42518440602d0807400c6c01105101c0c081e80c0c0c1c4628560245900c9007081c1d001007505081034002c945661a850305180ba01d682d070350000a00741444400301111140104801c140d01894101847d60545007100102400c0214420500c07080916a910603a6407030000d0340351400103e401002c00380d07008117007248100e16040910705000c005840404c0d8511a0f0024444400005800245158090380600e40880c4441a290314140714440d000108090942001400307e0380d69400900c040c48140f03210010403045665101058031010 = true := by decide +kernel

theorem cover : BRFrame.Cov 968525179 968705035 := by
  have h0 := BRFrame.cov_init 968525179
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968525179 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968525179 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968525179 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968525179 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968525179 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968525179 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968525179 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968525179 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968525179 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968525179 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968525179 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968525179 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968525179 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968525179 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968525179 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968525179 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968525179 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968525179 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968525179 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968525179 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968525179 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968525179 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968525179 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968525179 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968525179 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968525179 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968525179 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968525179 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968525179 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968525179 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968525179 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968525179 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968525179 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968525179 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968525179 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968525179 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968525179 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968525179 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968525179 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968525179 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968525179 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968525179 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968525179 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968525179 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968525179 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968525179 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968525179 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968525179 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968525179 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968525179 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968525179 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968525179 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968525179 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968525179 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968525179 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968525179 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968525179 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968525179 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968525179 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968525179 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968525179 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968525179 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968525179 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968525179 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968525179 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968525179 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968525179 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968525179 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968525179 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968525179 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968525179 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968525179 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968525179 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968525179 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968525179 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968525179 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968525179 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968525179 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968525179 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968525179 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968525179 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968525179 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968525179 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968525179 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968525179 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968525179 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968525179 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968525179 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968525179 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968525179 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968525179 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968525179 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968525179 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968525179 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968525179 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968525179 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968525179 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968525179 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968525179 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968525179 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968525179 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968525179 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968525179 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968525179 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968525179 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968525179 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968525179 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968525179 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968525179 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968525179 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968525179 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968525179 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968525179 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968525179 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968525179 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968525179 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968525179 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968525179 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968525179 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968525179 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968525179 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968525179 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968525179 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968525179 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968525179 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968525179 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968525179 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968525179 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968525179 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968525179 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968525179 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968525179 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968525179 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968525179 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968525179 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968525179 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968525179 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968525179 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968525179 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968525179 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968525179 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968525179 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968525179 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968525179 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 968525179 ≤ n) (h2 : n < 968705035) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
