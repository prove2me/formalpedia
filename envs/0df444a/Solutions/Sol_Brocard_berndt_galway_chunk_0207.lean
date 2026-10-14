-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0207
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T18:27:45.935425+00:00
-- url     : https://prove2.me/submissions/c875a96b-350f-4ba9-b754-53faf711dcdf

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 37050364 ≤ n < 37230220 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 37051614 1250 37050364 37050367
    0x70f1401050418051503030906040306150509070908120c030d20040314010507110a0605060a03230706110d050304020307120b0403030c0507020a060309050f030f090406050a0e010e1308 81
    0xc4051105030409801030000c1100c1e01104540b413414140c1f644104041c141e00710804000810020314154092450f244020340040807082d1254000b51414005840042c00588150b9040c000c0700800d002105010822000c8075182071542d19110f52170b8050307044505072650303450310403440741c00e4880d50302002c8014802e030305580d9507141d1505d140c100741e2405440010303610300000252018064600c070003803c1880310003031a900745155905000780400510072a00080c0410780080000d402c0100078010707c040301143c0385500d104560346850981140e00c002c0400981c0c0900c224402004150250305e030f03127103144c580e41d40d0b6510b0000c41c1ca0418594450002070045990312020300c40c0380d0903464019480381e0390501c5000c1c00090100d41ca0300030b0303044c041e5000c549014104007080c003070303800300002c40d00c1801910400030880301c0301c40c116000b04130aa940c9800c0000c04560a181511924000d004200e6010088506106804055100c1405000190002d48011401e100368031980085040c0d800030145 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 37052864 1250 37051614 37051649
    0x60509010606140403051203040f020a0b0c0d0903031b031407030309120201090c0902030403030b1809010b06041a0c1e010906050604140c18090f010305060603070f14010504 76
    0x55000742614441d80740015250450b201521030740000f16000c0781d800a0003000c8243c0243c007094900d40c409041141c03d5a2071641c0e80c001038860024150003015101c040030f8650392102e20341c90415501c489400d04000804009100280e000f000e60a48003c41e0141c51030a1901d62070309036075885500c8404090381502142c0d90b010181c0c180c12164074244564641031400003d030f88160b003038130000000201540004142800892555400f45601600078038001c10900d0a210202d00e07068842c6140c0d034a421500320400040034030900407944d00160590310a840c003071400ca24800c0c00e0580e02d181036044800000ca500c0c82080800401c0100005a10b0045450f0140440b05e80204082d4800b110224240300c000f40301c5103401d110310000b004035003c0e114001e595404100d88140c1c0640300c0d00303045081c076000200d441c0d1100c114491044041c03001450302035055080c01860050000c020360300c60350003d00140700d1025100c6041007200e14090082140810150058589004a13006030141c0f06001100 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 37054114 1250 37052864 37052881
    0x60908090301060806100623130509060303040e061207080d0801031509150504080d021c05160507030e1c050c010807030b0102030a18030c0315180c14010306030605 72
    0x10488224120000c00c5910313503650700b0701c0e01c592045560080b48408440100001030084065003080c200f0f1060f81c107000b86c03c4408201083c0c200340042100c8201400d014010303800d2031140035401203c214015070a241c606140b00ea1000300003840c4a0190b01c14100c0d60700311180403c00500070703103042e005a407003c070940107009100c200c09110540c0d4032000c1640031000c000c0c407031060342d078890740040840c407003041441d030108081c15014000310f0f0703c0f030401c0003001039030704d014400b9107038460b0740444440720303100307454540019a04094024010b1810308103041c0013844c1c100c400c495907254076003422240c1700d0070500040c808244607101907040699003140c0350704102b00030070901c19100c1c007602c943c2031701c0e240d4120403030480b0003d0034240e016074400c00c90320001c103004003401d140d0320b0500c2443c007030382036140c0d0b80f000c48100c4c5582c0211b6003400310220411080b030207030081500302814200034040c0420103403504040162035100704400c00107022031514882e40710350040c40145400c04018085402c2aa40 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 37055364 1250 37054114 37054117
    0x3030a0f0305060a0e040b090708011506032003060904140d0507050d17191e05040218151003090b0f090708071d0c04091505120c01080106030f0207060908 68
    0xc000001070301d040300043d00d0303181c0300680d68260345008105580740d90b2169a20303e1000c00180000140c0c2c0b01b0304600068425003405103183d10801c0e081502c0a0a1403c0e4028007600e148082244203281040d24400000020105a076440801220049000e4480e42451444440c07004c5403106e1500508207080e0f4001e821000800750644194100c8807000e101180807142a509240c1c01d4210701c403c00e02040e130648050102e00e80394070185100080303403100700c4203041c4030b43c241081a4843c2030712a8100070540c5002d5424100b0a651807444040e0381c608043d4203801d0500d200c541a11400c1d941c035041e00c400d4425071002e402c440e406208001d15050128040503c160304848040345407190120101d003081000c204402110301d40742c0800c481c030b0401e860120384680010003a42c1c2c4a0310070300c00094030f800f95015003010035402030141441d0601340f4050110312540c0ca402da240c01e921000002c4040d9034003001180c11209507140c001440750f03520070504041d10402201a14032410062010107010b4580b0 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 37056614 1250 37055364 37055387
    0x3150212010e06010f030509010b18220c0302090a0b090a051b07020609090402010e0a09020a0914010e0d03030f02211e0f040201020102211f0b0702060c0106030203030a 74
    0x3400040240c2e80c6056514074407408880c2240010241c43c09001050b009400040d0449582c80001c07982c0c3d80c801001c20340e0003015030340c0d020104805006001601c00700d0014a01c68101c0e00e0004c1c0803408841d101c1178400004c03444000c3c0980203c00000710792a00700e601443c1e04e91030040101c0d00b01d0400c0b5015002400040c3c4041e84022440102c00048800034811a4495903020304014185001d0000b00013100f07200900980c14451032090080c400d541e9107658101800d400703200140c030780801841c02000880036411030880509820b0641d200d030380e080713510842d40c2403080b079001c408103119144c2140584002d10520880600202d1000d604090700e08510582409500203000160b0301c40300c24803842c154030300c0c011108039013030008242110041c40181e41c0c03141c010b0002510f005c8030380e400212540344e16000202001e0780c030742c01d014440d80b0ba134a8055440c2040d2000700b10041c201898403409119103403000744504400543d079040c0e480c081d0031044c01581c000703054130348581c0c403038002405e000c0d25070 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 37057864 1250 37056614 37056637
    0x3020a020405060303090a0504020f09040905030d110f07060209120102160204150f030314090a12021002010603031202210f0601110d05030703020306030a0b0412020d030509030d09020a031502 84
    0x41c00080f01400c00105450400c04001d00718941c16281c4028800294000c000301044400f08018082c0583c0300c0d8091a031041c1d110350300441e40e6110b10105881150030943d007800c2c0d0303200100300d0001c01d07e0341071090f07924150308001d0050384c07140c440700060054046141c01c409654001700700304130128890f07900840818000d9409000b6080892100a4000130b24081c0302c400c0c6d00041e1091001c2803248509145040da400074540c81c099842001406041141c1e101004550300510303d4000c40c24191200c2c01d035115680001d02c08141565000340c100041c108481c1c80341640030600a4059101d14444480320000c005c030740b000360a0400c54280c850300304583c540d01041540c0c00c0c0000400000429504d071510300d13503409003140c0f0b8003001140030b07602c0500364039814801d070302ca03070030120741c409600601503031054209078904240c045c4040d0418416801841c181071400c020403024403004801c40303a0408100c0d0002801903031900c0041e64002140e04084c00300c40c0413102a0540345c0c0242d00402200d05207 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 37059114 1250 37057864 37057871
    0x60a030e0709061406070f0305160b0907060306080c0907030c09030204020309010606090b1201120303110310060e01050a1e03060807060201050106031802030d141e030a05010f0b040b030915010303020a0204 90
    0x5000d111161103040c6c80201403030b8940010038080307481540601004050700320640c40407030807071b11400000b000039109030021750416802000700a4040c81031000034501c1c1000b81a0220a0800007034071454002d001500b45500c1e0919640d0031072044003118046e40d4000c00440d100d05090014600070000ea000c0d0701c0200d0500440801c902054506545e040e05c20840d4852050307007480d921404818803004201d050589404c0c003100300301c4049014500c50b049003e10030000c14500003004100c007442000d120705024081040441551703100129900301071800280c0c840300040d41004400400e40f56200c8003607070060382c0c80410717419410340090b812100940c0d030038095200102e403002801f44a80900950540c03046172160f0800e4000c141c4805550810003d00e170401c4030054101c042800580c8404281150020411001106610545c1d02600309281c0000d0400e0808101c040b451150b805403410051011001410ba40310400410823003400403480e404e229650303490083d5075010f00503000c034403880c113 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 37060364 1250 37059114 37059149
    0xd0e15090703050d030c090302100507060f110702060702120609070f1d0609040302070306050a0f18030c0b040804050a060c02040e0c01090b0a0201020702040903170702030306060306060a030e070906 87
    0x90001d098000d40760020061314459060b90010340080403280c100300e051080341c800c0080540c2c1e9003804c0020722034032511038a903114080e16002c8126440070300340c100c400307107010006880f6030001400c0d110803541c1550301d50b070740790554000651700200e03c0d200301d0803900c6401c08125044a0102e54001220000c0b2071031000d464640744551000024101c401c440110341d540062001e16003180c00540250090043e074807190f40701c3d101c1000b520000c0b500c14900076220010409803001da44110003d4107888800210070380010b80d00107041155034800900300210b803002141c00c0c0405d00040ba40200002814002060354455018140026a04050b4455842d1036038040229901080d1010030300016921480344908006c820062a0041c0c420902150750921890006031114803c40d18103601945a01c0602c0c42c1c0c1c01c1d50122122002050350b41107410078030a00045407203840a0741d4008200b115000d4664801c0c1600300d00814849031800d92501c0b0701c0400041c0c0104590001c01503820103c4510400030303 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 37061614 1250 37060364 37060381
    0x40e010905090a02010806061309020406141305040c110616030b03010b010e060f07050f03090301060501020a03080a0504080c0604030c05060a2f090604080106050102070909030e150d0e15 82
    0x1182110b62031000c2e0825024000103610601c0c50303a03400a00146101d061a6216114031b00040d00798129000d4541d00090034000a908117103030300d00600f6500b58961811070500c84c4c8544161061241500490300c0340f4007410001d01400c4280300050b4514100c1d0010b1804420101c412082c04400c04082894101039040c0c1e8207042c020340c14202c1046c0c68010002440c0340501c0070541c0312030002e17a0a1a403d100e1403001503801d0021580c074175075200003951508500010582141d0031a404241590f1100b84400002030704051010343c00140441c4c0060b6960319420081401d00c2002c2103800c041c0141e808100801d13030000c0507501058003c1c1c0071035015a0300c030300c503442c02c0b1511050740480f0aa41480900030100d2100b55500c0886807000080f42010710803008112a500035030003105041c0d460750070030311155a040015200514640074107000100382902e003e4011000641164043d00d105000506c00c10744040850f0072094030b03220b0400118640c450b681e5200c01e4090b13841040b9201010102d0402c5 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 37062864 1250 37061614 37061621
    0x180112050114120c040e01060e0a0501030c0b0a02070b030108060406050105030d0203070f02030c03011401090f021e0c0f12120a021e1e130306050f100515040902040308040e0109 78
    0xb55450444400008000000c0203412400b00e00349200d00d01c2405681442034855000d82001140c0910001c44c420b0309006001d0200c00300144000100c9281000400200720a20f814004540007100c0031a03464603400000c80c14120144c00042140c2000000082e2b0400700041d2584601e0103002c0803c07140c0d803100304054881d01002d00241c0164000e0025a001c00c18079681182c80910050448400e45a0a4080b03802e65066180901d08002c002c40100881c100b10b00800160403480c0d1402c40c40d10070014000a8518403069961841580114000e140b0f007004025140c0d1601c44442180e032442d582c030140c0d61f540c0d44040b244038890f0b02a00041107546032a8000e41d10401407022000caa40d8100701c80080c110340200303c4003408050010a100700800b0303104010402c50340c160780f60070700080c110f003070400c15200702415101020040c2c6007000301d8185a54100d1058130802c40e034501e0306401110b100c0e0740900964120021a510005000081105000081080b03d02c100c18401640ea620401c24048 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 37064114 1250 37062864 37062869
    0x8100509013803010b0a11010507020303070206070806030a120c0606090e070605040b070206030423011b1806050c0f010f090203010b0a03030507060207020109030618062f0c030903031801120501 85
    0x21980e00340011701c10b541c0f4103000741c002043d9900d0000a8000e000301040d0950304251080d00142e0400400e200c02140d05212503a845022410074901d80d00b00f400200fa500e51031000d001c2c0055000c400b40e0a816889004040003181d006241400450340b5945600028102c442546c40301d4851a00001545801001543e0840d06140d0040e4141401a004c0c060503510041c401c0340c02da4869031840c101051660950b060910200d40009003178031084881c880740380c0c020f0740043d091103c4241040310382c0903001e01c01340039038940349030194aa00004000e50f10380301204454005e15400c2403210120b0002944c061109036000300c5c001d100102000050005500301404040c0003d0000c0000e030010802c503030020090300f44103241c010031060741c0b5210b01080307680e41e0313480b2304010b14104202014049240202e071803500b10162a514070048002920321039145281000042400c049420390f180441401039801031180034040d0307507480c0e82c844000810302200e0542503003c00d0b400004540320041c1c41c49451b05 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 37065364 1250 37064114 37064219
    0x12010c021b0607020d1a060409050c040b0a05100203070203060c030115050702010c080708031009050c09040509010917040602070b0a050403140a060608010f0e0c09070810050901 78
    0x10101c1440660060006140603000d070054400c01502c03005031581031288041900403034440a1006040d160403000c2d5101030201c40c403d071309040300580130803004140c2c050840300c22600002c160082002080c6051075a40c001c40d481513118582d0841c4030b4001c0000c1610b244224190b41141ea00d581503108913020a000749052030003c0014002c01034001d0005008981c014105140c2400701503584014507031200314203c9a200003c0b0a010040b4101001c020251024610074000d61504481d1140e00b40502c10302c0300e200e207845401080084400307500003c02d407078003c40400061015211403403819401031040300014841d11a002070141d07290419188070814a0751540d141a01d56110510058400c0003210324601a111103103000440030700c1840f004119504c0081760b00c49030070506000725000407001001c40d4005041741070703248e604c01544950022403800c042d0a10b4403120265010188070740c100d950802104030000c2010003406044a010241c42c0c01c0300d10700c003204100400d2000525401030301c0b = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 37066614 1250 37065364 37065373
    0x7150212061012020301060906030b0d08031f080f0c1f14070516180b0a030b010e0702030409020703020102040e060d0b0c0c010e010609020c060c0c030a2f070512010c02 74
    0x60241c54028091030b2202c500340b0345403c0c000e00c5403000100320b038420f902240201e84005000c10186805000380f840700d03d4225070208404000b61550380075440010300d8041e40000c0c0c2d55109801c1c000b107a604401a01c68041180c5280c0c02001c01c0340c0c0d5407504003038400c0c418103c561032a0801101c00c4803004502d003ca5580717040000b5901003800722a001403200321034a0242d20700000641001d00345100042103224810b0410740403ca000d00b0031200c0300d00f80c0a009a0903c00c0a20206105c40700315170440b94103c0100718282e0b20710310228118000da40110081034000140c0c0d509060381500900143c1e0701600c00c24a441d103a503820000180c402020043c00903e070300000580c84c803000400303007590408100000c190b0143e41000c0d1405c4410541043d0140b550215114030980c41c01c0000030384c450781ca1320b607807483c0a500040c0540c1d00c1c0030350b070070000401c070703d0a1010340550004002c40000f00c000440c4101e00448850049864100b40e02540d4001c600060174146444414080c003403417491150042d1 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 37067864 1250 37066614 37066621
    0x1a070c080109140607120b1c0309181404020616050a1b060807020a0201030c0e03071d0703020406020a0605040203070b0c0d02011410050f1c03081006030b011205060409020306090307150212 83
    0xc1b800761150790600c517449140c40b07030310003408546a40500f68180c407030f42c6ca40d0082801c0400c83c0742c109110502800c0040e1510000303070758241959101581080d01201c10540f500d4410f03003c2c041054600030002d1507406000c4524041108003121404810b0b10041c1c170b01d016a440d41000c90700036408030381d8000140c2c018151135000d94003030b5000c101c40b0051460811941c60074100840c0c9096802d034000601861450800210140320200329030308841c1c00c0c07a043d85054600034000350b03181480480a009030381d48102041c01c6640410290004000d4245101d442d43c040d200340302d0711100d02c0c0d82e405000d13508003402840f11401c2e1640640c8120344804803803207040e042805100c0e0b01901e00c12865000b588200c1800122001545482c1c0b10030b00ca9561340d40145016200807400d0411a40102d0030305050540d016900d86c1c111000f01c003a440c0f02031001440b5620f10001401a2012180c0a0f425018110901207900341c01b2005002190194891000d410340040c1404100c0c410f140c00e4400c0d000703201c00072 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 37069114 1250 37067864 37067897
    0x9060a0509030a02030f101a0a032d03050c06060405060a090902031203090d09080a0302070303030513061103150a031a0c13060c02090105030105040c1a070c080109140607 75
    0x281c0501c000190454800981e00d5000c41d2400348483c49180e03855100c01c00c40740c00705000d401100c0c3c1c50425029002d0070b10040c000440e580c5200d500008026a5040e0011a0b4040980007241c0f030f4071503512120201c00310181400341c07081d0300c041c1000015009240005009051900400f80591000351010064900d401d60f110020a00b40e04100d84c1800740d900f440802480e520043c5000f2448140984096445c0364000b41120502c0d030b003c04c055403c42c8404901007038003c10303600d0460f5014100456560b8541d0792175450b0641e0090010040b074941601c80d41900d60380000b03540b2a00301c940340c041040a200c0304001104029200003000610003012200c00040c11000d25500a000840ca00e4105443c00400700c0b84512a9000600042c00440c00d210951a000b900e250052400707500800c024202515405082031550080050200c07503040c400c80c1c014030035400ca84225820607020711300039407203440301406054484010303900c0018803102c5910714800802c4140c002d040355140c041358960071804 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 37070364 1250 37069114 37069117
    0xf0206010b090f0a0b09040b010206041101050703090510080103060b0d0f20120c04110a020d0e130606030e0615010203070b06060913050619050f0f0d060e030a09080309060a05 77
    0xe2803508105800f0442115445440e040009407802185650b00c82d52201c0500003142c0d03071010703140e04543c040d03018003011440566402c01c4000003071920694074121814165502c0e00990310854100c0110031208030001e62100d0103038140c1e80324040911074031154004100400803a28405451100401080b200080c100b0001c800801c550502001040d0007000c001498621010280d001640064008103014a880c1c42101e0705109001d10403820303c844404004d503542c00310842e0100703010356501403603026610340b003401c0356850b4020801c1c0a06511444000c0180890208c55207642c0709000100b050a00340d9103501840d0071040c0d00860034400340d62201e05041030043c00542c1c029a0400c61064039890311401e0101e1103039068000f2070b4908284040c00910311120000f00743c0c0c02405030041c411035a40d007070003c5001c2400c9604c2072107002a400002d003d105004c0c0c000300b8243c80c2140d551100107010000c4c0940300c4441c1c0310040119603d450300350322403041d800c006038400d0080000701c008902510 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 37071614 1250 37070364 37070377
    0x6060a06090b1c090f050c01020105040804090b03070e0a0606140412081308030409051e040507120812091c050406091203110604031211090307050f01170708040b01060f0206010b 78
    0x4000403c2c107400c10510b1003100d000c841d0940e40c031040e082e4214180300307003000b410380810000c5c4020031691606842d00403490181c0e004a00040fa00d400204a466030b0803c031001c0079002140040126041101280009284034810400490f00002540c0661800314042c1e408070303550010300d1381c0703815000c0c0c0e2941415805103028280d06a4041804556440c0801c06080500013170f50000a06d4280300904035004202074a03141d80c259148820840080c80118440d421580106000003603102e10380780601050060a449000c04181c1500b0402c0810002503240c038203104601c1c1102410140c150100c44512941c000c90000c50808113003006043e0360300480c05003090180c94250968201500d0840c00d10609860a40c00110000f00941a0010350b02c240301b910140e6074595440c00c0d40300004039403261000e204032441072b041040d1101d0316900900f45559400448840c44403585080a4041e04c40f440c141c03002d1792040344c1800003080c014003810b80f000f0140410380040240f03a10f40100700107258041c6 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 37072864 1250 37071614 37071637
    0x4030806010912050a031706010c0605090102091207090b030307030206010e0601050702040207060507030501050d02030a081305030a0605070806010503040b040f03030e070e0103050c0a030b0c0304050c0604090b010206060a06090b 100
    0x140b000103a540d4000c5120143c544914042c00485407103040003070000c041c0151841c002842641840100d03a000903500703410641c0214082015922044c50600a000300c1c3c0c0c24035000081c41d0105460300c5004a10001034680848041007035011100c2070594134056490002c0240e48440c00501805516184040d40594145010703450548207070b01180580c4c0241c4002c40b050b54440003406049505406424090042030703860302c00307020580d00020307030702c05031118041c1c0800f0002070030000e40e0800101690103040043d0840b481101da0389030601c014507084034a00001101000032520540c070a1080740d000c0c03900088100050b40352a110001210840170085043c166186100c4030680c0c024440403004103071a2082600c1c83d072550a0150400c100f00300610b2090007009018000103010645a03604002407400382e648a0351180b80c014a8050101c0130305912807030101e000906003442d50458605002c0a0382901c107103403580f000340070b04072403d4003a040c04220f0200c4140700806074200644038107603c1 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 37074114 1250 37072864 37072877
    0x9130203070b0a03091a09102c0610050a050901231009030507090c050a081503060c07060e0c060d0e070f0e0106142706090312030613060302090403080601 68
    0x141c10520316190700007810080400c3e200c0e106101804000da414810b90034880d841a4040e00d0080311503600e5a60300d260700303001c0e6540e40d040d40704003608000040070070b1895035609c50030a0340d40400b426914002111701c03540c43c07041c4a20114250500340d08501c1210380c040e12100b0790b41d00f04142019118014503051520b510041d540c01040d039225800c0d04050601510303005c40f100c4c1141001420410340d82c208030115030914110002c56903200701140d552008034580807049454405000a8103072880e94a07550611401080c04940c040100003030042c40c5c800c000c10029104194920303910380195520b582da00590a000c000000c100c00d0304042140c10782101550082e81e1a24191003040941c0d401002e14486024014880e550700060b1000b48030400c26002c5041024103580d2a01804101c00701040d00544201c0c802030b1511007070159603100400030255060f0f0b0341040032244007600308071007080c0300f000140c40210941c0c940b442100f095a4000c0c05004036075650340c800303070703075481026240d103040240 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 37075364 1250 37074114 37074119
    0x902181003020d1506020c060315040e031c020d0c020a0c0302090a0b040603060207050d1e1209051504021014030402040e0a170904140603061306020c01020d060812090913020307 78
    0x20f03a12500310109112a50310003084d041030700080c07800e441400d070705002d481c0401c10700c6400c5070b0030440070525000441d004650700440e40c01c020b08501904998407a082215441a089500c43d034020f40001d2150140c00c11400c1d49003c0201da6a840b0f905001e0200c030341445041c4090b0800000d05a48203942040104840030301c80049411101c8a600c251406070340442d2003000c0002c00d2042c808210758074a81404256107a041e504030b100b200f504810107012040e2400343d09617007141c10236444140c1103401d07106000c45c600000003c0c82c0080310100c1c41031500c22405440a40200c0c0030034011816081c150b030030b40e41c9075805d000082c09415100c8007144120811240042c845010143d800d400ea60405da448070b28290500c016a022311440104108060042010a8400050403648206d06c8107640b1305040e40d42c24820700074410301040d007003c1d500000300010b1745469074110307504503802d100c220b5040c1219010781c80058020340d8000c1d0707845203240d070126101410f900c1d401c8900600060549a8059 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 37076614 1250 37075364 37075387
    0x705060a0905031b03030a0c060b04050106021b010305090d030509010b0613180506060706020304031707050901231608210f10080d1d1504030b01090218100302 70
    0x10800c62410000070780c01882070100b41000d1089180803030034507000d442c920b4a00c1001940380e006810080003007214581d40c86c000d001c151780082c02c2d003600203041005203507103551000b174407117000468000301e18201e4281c01c100d5503c6489030302c4c4500901c4010300b000c401042c00c00c4014050141c4041d010790f48030703008071649541380f01c01019004140100360b4079007894045031481000c10344003070654040c640010400300b9164a01107503003440d4042c0f030040c0d41e940c0d946400e4031020500c0b0a041c1d6460001000c1042c142e07040300040640d01ca003602c8a0040c0e0080c08082d8809460307210108200040501100c08a0003c5916540b801c030700c5180c101d0300700f00c0c081450924001c5140e00100180000ea0248002010b11410040d080000e40e041119200d040000099a51030210901e0b8100302c0526984841c0a072040160201910014494900c10301b90f241e000226801501003a500114084000500711a5520031140454500c1d0318000c49140314070200108180070740305078010706400700040016407 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 37077864 1250 37076614 37076617
    0x903060106030c120e03041202131b020111070c05060a0908060a0203040204060909020102072705010b3a050c04082401080307030804080903030f0c010917030403170603070506 77
    0x1c00c0c45640026a80c1d141001c01400280072943c0848140c0c6400c5c80300302198008011501031710340c1248200e5446200788040360302c1c01e000903d0880160700d0240f221003e1480d00c05441942c0e111540203202c800c03105040040b1500c1281e00041800303040c3d02c803c0100b810312101030540904281004601242d032100341c103017003200840b000348006500100708030452409120fa0350203010504410071026045e9170001c1d40d00e200c54024085840c0d016248554100c50622100c100844540c60902141d65192601401c0c1d41100ca0f0320145108a0b251841030b40c4503e4140321340031071184132000c40d044103c030401d01c01401c000d0410116544200004541c0c420204031403030151030000c01c02c1c1580f40035260703014803c03081a0841c107001d400812002c000b0950142d14540c10503000301c216541d03001144c002030f1861152004070b0b00408004114044003090640c4458507650003060384043c43c001415000c2a64801128000d0201d021410341050402007080c02540c4008007508592050342c40b0310024016 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 37079114 1250 37077864 37077869
    0x2060f0c060405060f010b030601030504060204090f050a0609021c02070302070e0c030603060c16021c0f0b0901060b1c020a02010e030c030a0216030201020a03050304061401030b0121030f0c02010509030601 90
    0x25800341c030902040020410400707a012544204c808419410200341038034503c00504a01e04050310344000c64284a241e43c101d40007024150001c1000400400c52400030700b070101c0381c04805074503010300001c418605000b01c0380a2a0b18407425242e000342808034400940201605504500c1007070f40c00310750391648040050007100c3c40c090160326860a05c1c2013620f020b00041a907801c02c82d0600070007901c03015a06460503e140c0c12280a8904480f084848030b41084d08000680b8070041d5442d1001804401d10301c407401440e540000b842866107560018196102e00305180104440d01240000004540d0f40542140c0c642c0740b0012400941d06011240756401191707102c0e038183c0001505280c501d170100603010049014030241c05241d441d680001c2d488e0103201c08040c3c00c0c404004009001c00c041c1d079200e4407069520340071303200312540c513400c08240c41d2200b402820070b441c421890904031580100311059105505944030003d0441c0c428046480d030f00701183c120b040c00380912140e0f510303a4045c40014003 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 37080364 1250 37079114 37079137
    0x4050c07051f02190c15090c0501120e03030a06050a0b070c0504110909012706080a032601030f14150105060c0106030501230c0f0a03110405060c01050103030810050a0302090402060f 80
    0xf05075000e0705054001d600306c012911161860304c007100340010002c040e4401203810034205000301c1490340700d900b0050308000400306218007000040211a9000382d00040030381d641511380d50301e26a1a07480f52200342c82001400340624810103420400c61519400100d01006219072840c1004044004122a0003003a013010981454042206e600150228108607441d12800f00912034a458105001d480b2038070240082d040180d403071410b4a0a10b2080404206140d0100820082c0e42e506e050400e007201a08004a075003e60340c0550740310314940010481a401400d00c4104280d91808041140e03681c801c1180b00465521440d0000206030203201c0c01200c80d80e500d10000c443c0c02c91701c4840e5008100281a40c030501d8051104071410b69800b0b00355514060031782000203a1090302e8441c01c000c3e0007a80e0100d070340060005542c440d03100064215034105c030b22070b440d0b00c1d4040d01e0ba014011044646801110342049a0040800161603c40c44840e009400640301600c2c11640c070ba50003445500c016600302 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 37081614 1250 37080364 37080377
    0x40903140d050411040903051206120a03050306101d010f020f191203060b0d0b04140115030608120f130308040b0301150507020906040506150d0b04050c07051f0219 72
    0x2041c8824410140000c404c1110b081040c0092030350058068080c00c040b03400400748200004d015521145960b01c0356445140454561040a1500030500d80c81290340a00400d80000d040101e01e00a1030103800210040c003c000481a40100450b2204250040349045100d911441c1518107028491201c0004000813003100c84045800c0050810341c0c40d004200c10585412010842200c0c84815111800643c0d480421010a0b40d00010050301316a00442c088600d02000001e0700d2082c1403410300c0308102c980f41413203106c0d03a443c0007a40740c0307001c088101030304402000340044141070707070004280400040c2c5407804426165200e51095030050f81001e5404040000144120011140c00c96586c1c1c0d0b607803900030728007160759021071841d0303002a2038203004644910106180b562130241042402c0c02001c00542c546c002c003038140303028040c1a05460702491800d40450582a02c41d4201c40b10150000020800c40c4906549885095019004890000d50900603458100d0070040703000da03e40800eaa612 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 37082864 1250 37081614 37081621
    0xc050403020102010b03150402010507060b030105150f100503070c0302010f2309010203041703040f060e07150509030a030809071206051006030902030a03030e030d0e0601060801050306010b09040903140d05 90
    0x3e42118060010544a507200e2040600011a401086070f8042c0d8286461900c0b8480d9151080140150700c4010341d041d4240810040041c40b40d4840801d820000c882c2c041c13010001e1000e01021000310200701e400070703e0420000c1d41190080010002c0c49100e440009048119120840700b116040480010030311500589501d11030300241160b0b03000342040380218030f1030815a9950008505c15015040100070200009090050200820786c14a400203000d004100c065581e00b921140c560151111011885210b600c074240315800342c031080c03000500140825030311030301c041d550070400a000400d648a15800450740140e881c3e45101c506100310008a15820202c0700044981c000d60000380c1090310f4400e980c0b000da580060100a030907014140020401400c6103018110320401c1481c0190364142401502040e0b0300244c1e540c1200d44039510a0b40690701c0720300b003544400d8203100d001e101704c0f014000c0d0021840c05503c48035165109090040703511070201c0c500890790708100081c0b148180e0b68803c1 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 37084114 1250 37082864 37082867
    0xc0e0109050106020f03030411010c0b07170a0b0108041419050307030207050111191b080c09070509030a030e0105121905060328020a080102040e0106020c03060105010c0f0606090c0504030201 84
    0x1400c0c0504150300181c440002003600d400e1b50703804003d0000d846035030341d1405069582d002e400c0c46c109403908444d80030500d2915201c00350480b00e100b48040703615040700d000190360030031350700c6843c605840503035500056869646a401c441003084100c8285e07805000d964101014911841420a0f8814000740d51030302d500c0e01f800703402c12607a030b40501d0502c0f0610300700f03c1d404200441e4161822150076000d0082c03a2542c2800d09020748030042e02038418240b4040441d0766040040d8480025000300e40e01b50319035403920802c035994040e00d1030454050303010520080c00a800344901c00315560040c07500501308160900c400b21600c0c0140c8503c103e402140d02103e0799524907010303043c0d204d04142d000f40110102154410030141c80003032914400b84250b0065030031544d4102c0c400000741000b0009640380c907155101c400c404c4100784030340d07400351040403105e03c3c16081c046011412a1016100c03010302c1e9410743c03600200310f05410801c4880c1c03070b03071500d0100700f201903885005000c0c0041d584117a100da046200 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 37085364 1250 37084114 37084121
    0x60913110327010b010801120606080304090e070906051503280c1e140a0e0d06020c1006030206120a09060f06050f010c080d0c020a08070b04030318210504030c0e0109 73
    0x180c0b102981d04140c80c1c015580d802c5009241141e054283c03074586000300781480c84c010201a005910180000280014030024a40026622607002010340d00d1a0355210140c200b00c5085110b400d03003001d40c03006011101c0810031b000c3d640c0020754030b0820344081a40541f500c03e24030845900c3c0b01c00e9654a03141c20420780e0103261035402070941200410505000e10010f40610000c0781101291400000ea039a0b003d441994002c01e9640098140d0315034120074501803019400400040760a48030307038110303000c0c00480c50068800700c030380281042e03150601080300c24200b0b40c0e00034200b03800d1a4851100700700046c40e42c82051220b05105ca40011554200001c03c500e401c03c0d48401810400081d4107140414a0390003250f007400c1d50064002110b440380ca000382d060008140340507240082c04120607052140000c44141b08500c82d0b94100641584508816900240c0860160454812400e104034a07170103600545008001c034100142013035525a50500c5c40012070300001c40c001c440000400c40d1001900 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 37086614 1250 37085364 37085431
    0x5090a141c0306031502030402011707180803040608070206100504181a010501091d0604051f0608010905010504090302030304060915091a0c030103030c260c0a02030d020102090609131103 82
    0x3205600c7d509050300024048002e1940700da00d2800d001c0c021544081c043c0c582001f55058410080207010360b41c0e405180c6940207842200c0c04580001c00207007a6900c081103080c0b16203031802c0c2e00c0c01901d0416050100074600340a4410a907283d0340d60040105011043d4110703401d50340c44101c0c00c030b903040c10300040104031264032195603400200001d0000c4580e07225420f0703218006130703030000b410b03910416110300b2511940c4000a00e0403506001048007507110000d5410780e01001c41c1440a070b6a5031080c007044610300392019006070000d20201c4c0024090307800c0f1540881c021184819980014441d5a040359442c0c001102c50b112180389030400b040010300e540d980004e51800311411036140d43c40203007402e01e11346001401501d4441d0031041e002441c4c1501170003014003030401d54481400c2c501440e92800705900c180c0c4284640081c0c00070241c414001c80b81c0302d80000e445207091084800c248a0284101d00e03d07a40115182c0c044c8201d03060b0108042d520840d02030007140e00a51218518600405044 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 37087864 1250 37086614 37086653
    0x3110d02031f060f0c020d02061204080a030b03120337020d1d070512120307081807180c030e060a02130f0803030705030408280f020105090a141c030603 67
    0x4501350b40d201382d0485640007101d45c042c0c6255125904500c00500e1074841c040f601404219188144428407201070050480742c005034608104440040042554600d510b441c140b645404c104000348240d60b20407441c0740021594942c586079140c0781e01c051214101c00c1e0119010b0154049403203503a1814600951100340081c404044030640e02098050703c481c0b445c000c45025203005058000c0200c0100311380c4100402e18910103407a82003560000704404001c0d40c000243c05080c9080105d814408540d9200316103800d1040041031280c000042d01810000300d000083c142e407010450b41094052107100d1040340e09081c0180d541c105600c56241c69001a0403107201c21207003110500030341e40000201d980200990038460303100e6a43d81b800c4d04007449500b400c108000e01c0b0309240c4180500c8440c12043c0c4619548030010240902c500072422120104c030460101d0b8007104160001c0340c4c0c0c440d042610803082c00241d071241c1c4141142c0f480d0300e5500d8200e130000603540b1001041400b03625922501394660380c = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 37089114 1250 37087864 37087877
    0x1c0b090106140f0108071713030905040b0109050114070204020304050609060112080406051303060903020c01020d03021213060e0303090a02040c0305040206030402130209030d02010f0c11070603110d02031f06 91
    0x2c4202003051850305640580c14050000c01082c809030103004480c2c40384d0a15060750056260682c070a82d0b4104c41c0b0001200401c3c01110046464500350140045000043e510600420314160044810080d1380700c0e80a0000c00030030441c405a1100d0004602c40e90060004058a040502025161140503400024100e109a00100000d20180300301c404444040c5081601c80e0403941508201d0021a840100b00b02c0c5810709440c2056008100c1000a040036001d40d11000b6100100343c0580c401c10781e0581c00c0800c850002607646980e0010b045080d8001c4100040c08144040c0079807079a402503441500c164821071101d001c503d014054a60f40c9445031400344018103096000c20359600005c1c000901c119000491015049101c2c0e0580b800d20000400310349102c996140064000c01c80300880201141c100201c501c50315006016a195640c10540141400e42c50100100c0003001043d12084013283c0811078040034540ed0b0002d140a100300085105002c01400d8034114142042da0103003051001e07 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 37090364 1250 37089114 37089149
    0x20c06040b0a020309040204030b0f0c13030b0901020906030126031201090207030e030303070306030311060103030c020d08190e090717060103020f0706060303031d011103151c0b090106 81
    0x54940603034045421041c0226111035620806908601869048640141c0701150010601c050498428040d2030f003009074101c252a030560f10b8540344101514030703143c54050b0b070042000030b50095006501a841c1d00006040c0301c0c0520010380075034403e038840d040e0406512001d407010b501c0e51100c110320411a1000390300e0000040640c0d1a078990501c00e010000381d0100341c0b1414503008801d9a0030034000201036030366a191002002e00180024002500002c40102c006040700f031002944a0689400d500c800ca82e0403100c4c1d00f0000125400001218441c1e424800081403168000362149a800142c440b0810494698180200094002c042c281089044500440c000c40588100360304240b0a29000d81e4407290191180380510907200300605880c9042000424194107501401d49005159038184200420070708044c2a00c840d40d0544226160401c040740001c150041904031242010f0502c030341c108100c103080c1405c2d075501a4161410f240c02010010602001e1003607402030b1042780c0d1290002c00 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 37091614 1250 37090364 37090369
    0x405060708180a081905071124030108060609070f0801051002070b0c10150602030a120608060405010504050d110606040905010605210d08010e0f250206011401020c 72
    0x1014101005100c446004140c030303088100c0540c92200b4580702100d041c02460300d03161803180d0054909148181c16203101d100710910600c22140150f030892142003480c0c2100c8100700c150b0313200ea00c0d210740c0441141c0002c1790360032090f406903000b0f00905001c0c0045141400511151100041c8940200701c00c1461001180e40c01090700340c1902d40684042026002c0c40e1010391510540d0f40040b00540e10100d125882c00c0740015106010041418051041d10484403c903514207066015003005a0410701c0382c6440c5034450030410040d400c2100011604aa80380780b80e608019080c1e070240c1d038a94544040005200040190f10b851030854503040d01d0400080f00a10344401006c0c1031184600d441d120020705101094004802600f001030900780345ca42c21a48840030300d4070f031008a600601520600703022541c05000c6090488441680113101a542d124010483e03200041c1a0fa0068102c0d6910301c3d07400100a03107036008500c0310740003804154100b2860882240c105034245045501090320190140c = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 37092864 1250 37091614 37091623
    0x30806150a0305060402130905010f0906030302030f0310030b01060518030d0e01110a020405090709140112020103020a0c05121e040302030a080a020a210807030c02031c020706050a0603140102030405 87
    0x407061403800041c070352034600000d0040d10810281174504890b80c0c8020032624056071299040312024010301c0ca803d59070300d01c0502a6001840003502580007400054a0310307032a60015540000701c01005440300d9125664030741031440c00c1e0407140014401190120141100100d002c101e03c4e0120010215410384d010300030400d10603503600c14104640138602c500860030800c11a250b20f0307070081c030034805071030081f03041d95803400e40e403049403101803e15500f000d100c040040a541603d0b41400f680074a00c41d9a0019030295100d14482400c1104190f9010082074042c482100d4450004a29a5031010f01a185981c0949440a803080c075500c00c01c400c100590780010007403261035001c4240d54407400c01d2a4141d05040c6c0614000e845000211385044d00585c0416180c041d50905448100d0f4075200e2880480444510f58000b4015030b000300202c1c01d502185141e05905e4100c4060b0141c90082e0a68901781603d0301078800141c00c13610b4031424005c0011500321600d02580c0d06008604602d450344906c0c3e42c9 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 37094114 1250 37092864 37092877
    0x20c0609070e011401050403020618090a0b01080f04030c060c080601030608010b060d0e0321100602150601080a1503050703050f060408070b0709030501020c1606180905070c0c0305010903080615 85
    0x10224484859613140d0048003514015900200203130b441d05800e1001300c03884048500321500c1081c8041c00a468804144600295030806035102c120130760706d546805007a0311000d0810ba040c82010040080001d81d280541801e005031540d5205180c00c03d00005416200940c009075100e0f4100198070455480308400e0b1150400b030007002058002c00362407104e05501c01c01c2c0c60561902c10700300c1c11798030440b4007407a540e0141031461900c81120340c6d0740a003240c54000200c601144a01c16101082641d0b21840c2d0306500040104800200070444c070800c0b503c001303220b0340103c91540160504005011050003618658081030340071b40414907090380c5000c094810300c00300030124080d24000c2507040b489201442c1c0515032000085544043c40501155200c50201030032a500e120700340082142da204012810000381054030544001d0b081034001d80280500401d004100003050b1049000700b00f020300610000e5009000000f0303802500d050080007084018001e50040e0b500c1208050a80d4036002103a44 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 37095364 1250 37094114 37094129
    0x6010801020c031e041806060e06070203031b010e0a0c08070609060c03050a0203040506030f040c0501090501020c0609040b18010306050a0203010b04030b0a0f11090108150604030b1801060306020c0609070e01 91
    0x20030502010104286000d640c10040d101e90000661b03d00400d540d51104094451540301e58540c8407c100c1003201c81c1c8030750b0b1310080d00358206000340e07107044c40084c41d2004424501e20000c0780d0003426240481c03512001c218140e40c1c004800400700955101070081c03001410031481e1031035425040060190810204010080c10060300007000d4048034828000d50b0080e00c00144030300d0b52400c1010080b4845101520240d0fa81100c0d4070001509600480c0004200c4406802800200d0005410041550424003810b502b09032108407a1000d580c5507483c5400704807a0f00d00d2200c142d4158103040741110780091421008501c100010300a8000f19404e95085030b5008034003403503d903500c01c4c401020304000341100c00c07140d0a065091102c13030250720103400e14802c04c0e610280159905403000b800603211110164200d80108001e20110302902c00050380850b0045284145035402941d40d800c40e403842d0b2040d121690301148056071084184041031300300c800f400040407010300f4a0745140001d401032260b0b48 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 37096614 1250 37095364 37095397
    0x903030c0c0f0b0a1806020709090206070204050a02070c090903170c0c0f0c01020c010e0d08070302030c0d0309021804120f022a01030c0801120321020c0a0506010801020c03 76
    0x40410203608040c40c06015911409040b0598480300000103030011400c11011030031404190070025020304620080b2440303075004022040c6407824540040452580036a0400000c00a40d809078686000740381c0036410503d070050340c1d0700343c03400c201e005111142c00c092500c50400d009140401c0d40160700c0c8403045100c00c603414a0785c40709452040c0510030403580503c103002d0039080d4001d410b404500c00c42401420707000c2c1c903800b01c512001181d8a4448100d0cd56021000d6550030b00410107180207000c50510900407a40f50a0003c11020301d80100c1d503585900280d180e000342021400d1108001e070600d00250031681890820780d0380c000310260041070140c20030140508041c0c0c01d03442005001a000000034100801d4803060901c80b084010300030071130340420f0502e2040040a40700e150b00758103c03415215060800c005581c0c04461414050380910b807422041c040c21a9008503a00c001c10203180d103000205200c409601e42079041c100164089040e0703034814030418403001d0000c81100c50003c40902c07001f = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 37097864 1250 37096614 37096637
    0x170f0601060e1f090305060c040b030a0207110310051501110607030902040b0a0b04080f03040f1202010306050a0b07050106172e050c0a030f020a090302060d060810021803010903090303 81
    0x3089441882d48010b60100001c59450480750420018070641b40038809442d415900c810b0703190b0f4144528415a1020381e410800a120144641d001e407038240d02c10104034200f00a810006482c00100074002c0401c60f580d081400008549144d1900084c88203080840741d0045013031010342c46070300041070241810b4489034504c0031562554000010004024800d0417695160181c0040c15003083c0111640c5200f14814150410000410b4808070b60101001c0503805050140c0820103030103203d004c90505490750b01c04034513640c40640e0720015000300c9140c3d5441e11340300d041442c2035407291351024207602840c214881c0c00c02c001050503600580c3c1035484110012507407140404000800031072109840ca08070034081d940303820100034984124a59810b000c81d61509900c0012031281074107000104955017402c00050030030740042c010381e41e401280000e145030f075500814145125250128800c3d507000502e00340400e5a06659505d10100384c000b00412201603802030f0216005000113020b200516005 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 37099114 1250 37097864 37097869
    0x10b040519030506010915050a030224040f030f02040f060501270b12040201140306060d0b01030f140105010306060c0f1707081210060503040c05011409030303040c170f0601060e 78
    0x1c4401958004100da00541e512414000100008482903d10182c450000601e40ca0901106801d50303400030f203241d40c030446a8022080d040407070b60590004000038400050b0805441c140c180045010f44001c0c56070720700510410046542c50600301e9207141c500b81702485aa42c2c0a0104943c0d01040e05480038070f61840081c41561016582c003403004c2681c001481c20803a45503c42d8580541e02c01c0c0c80784c0c00d001c400940e407807069000480d20030307801c402c1c01d0229113400c840e01c1c1c000021100c1c060500041e024146d04012003501e20b541240e1a280c001280104100d5030705104010081006107070071200c050041da0740f01300e00b400070300e070140c4198101c40e000d84080c107c98085030303042c60384807a11682c2d03140e01d603503602c81c3e0810490f500185207110400001d1090702602c00c480c03049600007801c01c2006e040c40019a103802a0340e844070150b21043c801c9080a0b24200001e50045024660f240d050f00d1031305140610480045821184a070410850302c032400f600015410706454890400c5103000c0c1c6084007 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 37100364 1250 37099114 37099159
    0x30e0d02030304030809150708070b070c0b0f040506071805040b0a210b070e010503160210090507140109270b1003020306030c0f0102070b1605030c0d020f0105010b0405 74
    0x40d41c1400000340010070002c1d40170060115213401d0702c901c1d1000c00704410303a403107500074804c0107800584100f12190002d0040517540794882d105040004242c10141c48400d10b4040849100c8044c80c205c0e021300c401c0c02401c000c2c05074011111326010b0604081940310a40521030b9208070b502513921404902859a90110b1850140400070b83d81220350507903070030200c0b00314041001510a94103680110380490700c55110b44c50283d2040c1c5071b003803950f1a07031130144030031900d4445000c086008092091020752854094550101c6c014401054100d0505443e03214110b6425240760600000b030800b0400b4991030b03403080544c5105000b04c08440360400342c1080c082c110b49068141d00c94050014102600c0c3c2640c042c50180c07000354102c54811100c8000e000003c1206128680560b10004007040684101130051a00d8600c0c4001074800002542d155407440d0801138030008540c00940c020902c00e98100311420141075540020301495150081c804203a2140c0c1c000d95002c0d188810707800454191489 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 37101614 1250 37100364 37100389
    0x16020a060f0e1207060608010207080f07030e0402030a0b0108010803120c03091f0e10110414030c03010515100801060e0909010b09040302010510080601031a18250803031003030e 78
    0x80e0b4490f009100c00c0c1070b01a61228004598285c500b00c80130070000307014400c0c4d41e065544035006528025400c000c0d025143c00400c0214100701f101b0307000c554561900d0002c2d5014620300d0a0104582c00101e001410b0707010142c118036030561050208608102440b030358945c2005d83c1c000d1495030b0340c035030841d500c0c148202c0c1211000c00b54101790804400c078103203170300c160302000b0f0600c19200769581d903841038030035140c118900c08041d9000340000d201d01c91103c1c5a22500c40702c01400c0720351000350000401d017940d01c115088848124070441d000018181140012064070491905200b1907041c0000a0039454100002502132020640000d40c42d5000b5880b101c800e000003080f443e00c2c2c0c50700e0300c0c0c003d000e060200c0354140c4081c0300c41c200240e4284000f074211b040e2070384084c40c4034074013000001c20085590010404c180703a1850b00031002c0040d406100c2035080310300081c030243c1c07582030120101c2e101606c00e901440c101d5204000f040250f00382580050141e0b030381841c1c4145007200304400a24135180b0031 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 37102864 1250 37101614 37101641
    0x5040c0b0406020706030f150303050a12050405030a0215040308010e06011704050f010c0903030210090305040b040b0306010e09010806040f0203030c031c06050f01080109151701050f16020a060f 85
    0xc1c001c1041ca4000921500712916550184501d004c0c0d00030305026682e00300110100c02c00c00c03000c02e0001a0050010305448980b9140008800c0380d569910016680141d5080c1c41c190400542441817a906010780d441507240c08102c484141070a039401014200140704a5030281030740720109885a02c25400101000030050b0141170340e08180c00c0c06a20b480000e01900308540c6400e5945000501485c10b040440740c06401505510000b1401c5030041c044c0120120104101000003140381002d490103030020388186409030b9101e1500400240181c54007080183c41800d219004121840000941075402130340140c1c01d6040c1c0b24588042803640c00b400750200c4031400003241042640b103c22407940b51074403203000c0074412156210244403d160000005e1400075010400600110546800040c5200e0402c440f980c0d034260f4468116461040640004800341d449000f44041317544040105a0490100c1c4039980011900340e0000c1c2d9243d5940f44020201c1e61030798004d0380c800800364406c010b900d011 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 37104114 1250 37102864 37102867
    0xe01090509030f0d0510050a05180901020c030406050301060906170a0207030e0901141801030308130f060f0204050f03010c0905010e03030705010e15090f060106030f0209030111031605030c030a05040c0b 89
    0x220340c00013001e0801120064844041c20f50b00040b50716003100e050301203c00203011442c00d50000349a194008800078103180c0999002c0042800c08d000400042c4014400e51350b4413a00c03541405802010300c10140e2200781001505400c555011034085601900031020360030040e075505251030700342c440c00700107000c10358010f0b11035000244100e00c010080c020880c040b40c0aa0003045044001070150400717006c040c0009101030006900401158800d680700c1d401414803010191b107580e038013000d642c45c3d000e00307080b01500031a00300580c2c20944885220000128000d00a550381c80d08002c0c01080706103c0e040c100034100700400801d880500441d940c25411000070b000c40914111510f5494910380700724500601498000b40040201141d201d8890410038007030700003640380c000214082c0183c0704100786415400c000210950380c0074820000410402c03020152603160080000c00064444101c0109100e400c0017000050346002d0304481e0700c02001d040c00161915203051010f050240b503040407450810 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 37105364 1250 37104114 37104127
    0x1704020a15120e1606080c0702040b0a08100c030e0a0506060103051801090809100206010e0106050a030e06090607020c0f03030403020d050a02090106050705010b0a06120f0b06040609050f01090e01090509030f 91
    0x1c08203440480c10102c1e4000020145d464100311841d0394121440c900d00542805880c00601d45500a6004150002d02c00c83c80b0989030350f01c0c0d0b810200d1030204210107036502d91401380c034607401d40290f510a44110000d084803900a071501504c4244c000c3c5507904060f0303104001031915080c0d00f45103400c00407100080201c000ba174903065030750394880e41601d40700c0d5460030128105544000354840c180e420601c41e034041a442c085040c0d42980200c5252002e042d00e90310b41d403500940030407101e882591868000c0c1032605084001034140341184c11130b076001d10341620442c220b03502c001044030120303a030545000001107480d090150500150742e00c002d40c8650072000001d02980d000004d020114002d0008010b85e0f1042420000000348500c51074000c5141e070b41004480c0483c0340d00c4000d00e8494664040350050180001680a41c49504a90046021507a0a01c00e0341070640960742c2161702801d0a0101504041601410b088144516400140c48400142045805109032480b030521400e00030784814 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 37106614 1250 37105364 37105391
    0xc01020705010501050909030d1e0c080601080106050c03090d0f0c063609050712050709060201110306010816020a06060608180c060d02180d050109031704020a1512 72
    0x5019640c00e0381d0703940c2440c001040600c2c00c0380203240641d000000551600008217420006010105007804005180308020030380b07109207010b8904409220b42d82e0760358904c2d10100140100c0010f82040c01042010321020003040e500000300e0ba0740000c100c50040400c0502d1410302102440e200c001031410b469000c0000d500c0360003101144c4c1d01c0b9404030910880d50440c1000c0a4a070007409120590b4045170b16040191603034aa00c126044541131410f60014109012481e050355401d0310941d0010740c03049401c028450f030a100301340c00328104004451860501800080560102a01c04008030381c2001c56205003034020050303251a254401070a000c0b103903403030f8009421100d0448800030020001e1041d507184500119041030f602200074444d50800b02d81c4241a0f0094015a620040a03000341d0720002c2c86a40b60b00d201c0300f00034480c50011494103901c1c85c00411070700c0d00345142038070b9040f090103010050341e030060721100b6510340e4851114070002e80302d8101c840c50b5010750f100f80200d281c070f0100c61f01c00c0c = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 37107864 1250 37106614 37106617
    0x40b0f10030e0d020a0f030518090106090611010501030c030b060a03060f020424091403030706051503010b0a06020703081c0203180f0a0308010b0a140c0105060f011e03050702070801020c0102 84
    0x602d0701c040e11080d65500c003040c4d80f2810035000c001c11401081c070412000034050b602401c624100884c1c0c3c40403c80c80c513400b040b050300742130700060b010403421441044201d034040e01e01041003c05000a0090794510f607141039240020f40001002c03c1000e500003031041e11220181c000864000c0400d01640355580d48203030003036005010f04070305042c4000d9007002904101d03845012011803603440e1550b07075103051f0307640c0417908065050603410f020402402000c1115170046600808a0030080c840000030b020406007140c00b1150300b1405100322200805c08a90041800c800b00c035000303000c4999075603006040c0040c08001c0d10714a24903500c00f04c18005010083c2c400c000d40503c11004540750240b0482e00d040d0365082c4030800400141022006100095100c0007904500d02c117403c06510b02c03080141000c40c1034100d90081000c0f03a55400800a1130300d010a2044a49007085c200031416504812007401000704051030390041c1a21f69000c9504513200304a55801800440021502c440101506074040d = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 37109114 1250 37107864 37107881
    0xf02061215130c08060d050f010c02060a0605030a02010c0609030e0d0308070809030c030406050706060503010204060507050106091407030b0f1f09150203070308090a020904080c0d020a02060405040b0f1003 90
    0x1040c0c03001e04030440d085075200310460b10f95183c031a803016513650010442c042200c1c54084900340a100028088035109010b2003143c013009801400f018038103200c1600c1280c00980c03003036100c0e520400b41c80b40580d070028900d400d07003504410045040b0840f800c003170305c20510403581d6640028448050300d061540c440302c9240030b400c0c0340e0b9420007161904076009075a4000c0500000c207580040004001c030380e015000401489228501c04030f0580c0d5210f00103800c80c3c03c19404035020031030004054081000031701c241000381c00b01c61804c22082075000810059404000c0c00b51003499a40c40f02c000013a40d82441d6004903043c01002003181082c017241000d04001305074414008a50584000301d940c8000340d001c0c88505019274015030512910781c5003210388000103008501c0724050350b120400075888002c0c0d0700e8412401040030716501c040044ca074a02d032121610100c2c00b1500800d44210041c2d4450080b501210b50803240484c0c52507400c000201121200b08085502c1050400404012a01500030441 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 37110364 1250 37109114 37109119
    0xc0304030806040905060c0a02100c032a0c02010e0402161101030f18030503040c09060816080c0915010302091c030e030319030203150d050601030b0717040f02061215 73
    0x4182c840c03200380026241c041e14028000d80240001840190012000d490001c50b00e00c12112685031842d241d00884450710580e4000075103c220b07941443c0541c094640340880121120f070031140443d800144440c20000303000b07041100d1040065510750350364050320707410106607c44a801d6015481d08100110305100428007007070904802c02c51842d224071810f0700e8449084190340b040c42e000d0f6011a1306901c0100100c0d0707050701f048000300700d9805921441d000390031500001c00441c14001d42402000045d6800078000c1e5000700c090f0b1200ba21140011500450303107030f40907030b036106028005030042d02998110070341000c1d51a40c10b1050240781c0c80103400c114042e032036100c1515418420b245c1c07217100d04010300205809003140500320718403da0080d41c0c0030880b0a0010030300c801003000034050350315010098038554010303401401809620a141070700003000c0e086c40070b00703800c111005814200c0b0041c006040c030080703100d200041d51904000c0315000703155200e0321407452400450f0b20102d0b8890951050 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 37111614 1250 37110364 37110377
    0xf0902010e0303070305160302160303050c06010e01050d033902090a0b01050f0c0106050a080a03030b060a09090509070905040c080c010f080402040b0a170f01051005010f080a020f030c030403 84
    0x40a4100882121880d45c4c06945243c50310402191544030b0b10700e03101045045110340c00c2d01c1d0404201d5260080051071090755001da850190359041460504181c00c0304600c60f01c114010880e80da00e511000d02d0a03035040c01d05800e104149541034426422110028a80480d40d4003525103004155140c24a03862003154015825180c01210b0421182c1207103a2502141041003080168003180d0701800003910900c001042c05038459001c2000d03055280c0c8000360310342c0440d11400070160503000e4414001404e6a00905140e46281c2c0142040307601e00c00c4503103959582e40032540425040c0107800103403121040900c054140740ca0003d803003d500c0d04c980481d6001d01c601c00c6c0c12641c42441807401d000000d50341c002090b02c443c0c0800c8020100000c41c15071001c0c0107040054450307055032180030f400b400d81001e08600340a5007180750a4550003001d0baa40561410300521540e80c01c500301461150075440c102d00141c2c6c1d5224018005d1290b01c960b401080c0001c010015001443c40085100e03520a5807110b = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 37112864 1250 37111614 37111637
    0xb070509180610080c130e07080610050a2001020307051306050a0503060f0d050f010204051903050601170a1704061413140103110d090218090d050307030f0f090201 72
    0x314009142640c02070f5019510405800200d8070944541c0d8025002ca01d005151601c074114095540007290302240f074000300c0c0010810a1a0803810b010707030003a4140c079007250b00c0d80300f030ba00189203204d41000e260074880002c49020300d0811100c2105032002e1800c0c0215034078184080c01800039042641d400388100010600800c0ca144500103645002d011515494210f4440d00700700400046160300381a000105803811030080340b0308000c2485c00a20f20800113030b03250304280901800052251441505200560341000018000143d0b20b044810007005140313040e048142807810040f000d00060030882101030304e0000c00d01114003e000300c40f21130315200c4000516002c0f0030203e000b046140392400c2841c500401540c2c10002941c1101c500515000502c1e41380214021016040114191034040d40c441c05501141032025450303650044160040c401c602e0104165a600e00400702d100d400c00c207000c408104200d00035000b07081c030a02d1481e0b0501101d00310b011800010240b000c1e040e400281c4500c0207 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 37114114 1250 37112864 37112899
    0x60e10091103160e06061606050403030504050c040b031b01090506030a0203010906050a030201020a110a0504020d0204050a0e090304031209050d0311011d03041202061201080f010b060a0801060f0c0b070509 90
    0x310804c036200081c1110385541d03010104079440d0440078440c40b90146210301c2c800080d07454418140300e90300c00d0b10300181d50308103030601034900b150500c8114010740c80d1000422840d40e00103a00d0030580d141d48040c6080e1006040101ca80080d10b60005400003004004c1c003208014030780146043c1c030521201000b8240c2d840d4108018001c5500c00a4090b0700000c441e1030204207410008015440c001c2c00c20f12025a460002c142242d21211060f09246e901040034441c0c2d00d8894482c0d0018005c40d40600035a08285d00035a4030f901c0303184401000c00f400e072410000380c0303409006107600400d4020035031a01d40001e428041c1c0482e0f201000f00c80194a4143c116510100c0305920007941034010004500782400e04040d00c100000581c416a4091030074040c50343c1c203110b8400e905002e0b01d00c00b400b50154500840001c0c0c06c1d101c625045622a01083c0302d4032100d0365000010904540080c641004682080c00096407000350551010b000c804005040081658014008041c0107070240c0d102d5401d641003644 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 37115364 1250 37114114 37114153
    0x6091513030f02070b0d0906050f0c16050c0315010305060f010f0b0a0201090804120512041505070303180b0603150c03130203030408010509070306050a050402030a060e10091103 78
    0x100000380e06030281104000c030380b1440389540a10054012900e510b522401042d09907040004e40301c0c07805032100540010001103004184d0000c481d88140c545a04160301000c5403070140c1c22002401c0041d861546080c4901000715208005020b020f0b00d01d2038044548100d42c0080034002600d4522507c00410326501081c410a4120342001402c0b54030349044c41c40707940555011001186c1199200c2d18070402203508880140700524035000d1038050015146055414404036030b45807603600e80c00f03100070000450b5840c1c0c10140c9800e14a801581c4103001c2c41d003600184030030802082e501c0c81142c1c8040400ca15110060701501c811011200e12020b807400104c2c1c01e0754219008510690180081004100704c0362000002500c000c0c1603d0070681c845c429142143c40407103803944a540143d20810500485214058000c0350075400ac0c001071a0640101c3d80e03480351030a000341119500c40002081c4d441c00c1c803a103918440c0b101400e0220010300e081c0280600030b0901c0941c4280500c043c1131a07580700303001 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 37116614 1250 37115364 37115371
    0x1703090310020d06050307121208010630020c01090c09092d05030a0201021804020f03150a08010f050405060702151501021005010902180114040b0702060403050f060915 74
    0x8006000708600354100c80041c1d080902410b001d1911040081100d40d428402a40a01404440c620820106082c183c04500c01c00101c202480a030400610185501c4840c1301e84000402007101103004141003002040503980040305e266030b00c0070440f16614041034200008060144018030011a00c070741c00c84080365180d80c401050440c041c20410003000b0580c0381c103800c200c0c3d41c2500041c909105c0d281c1a0650b4072400c100300c0140d60000366540c1d41181c03041500440c65054a04500b08280300b140e280061201400c00c520700c800c843c2c50881103603103c682000180400340028044801a081d40c0006448103540444890045500054030b042c40010880090400000c0070070f91600c42c0c2005041384c0c0d2190b64910b0460090b980356070030804042c054a4000c041d1071f500180d40d42e0399040c01d04141c40e40c0500150401014954455000b148482910241d6805808655036a0f000c0d10003d0701606c903560004040d07009c3c03800099210000410290f04c103040d0384050f14864074540e0000c0e00000c000320b = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 37117864 1250 37116614 37116619
    0xd0c05030c0d05090a061103070305090307080a030b0a08070b07020307140904020d0602070507030c0e1602030406030b0d0501060e01050901080102070218040219180f02090d0f02061306030501170309 87
    0x1480b1a102e001815048250000e002405590801002d1748440095036810400084181d0001081c0900641d05103e213981c400c9109002d1801e04030f4590740d0441c0307482000c19050405865040310311307035650b82d0069107000b0315124080b5071000745e40b07483c0345e941500500000d03032207402500400265602d0700b9040d200b020000402400107079949070b08002180c08800402c1e00c24950038481f0800146040100201650103003e034802e84030b02c0c100078081e14810003060030808004822021540c6a000015141601e0407801c000c200301c1040c0b404581441181000503029600b081740002e40103a1b41c120141c140c40b0107461a031410b0707899400b41400c0c1c0c400c0440003504142c4500420216103030001c01260007e05c001c200c42c4505200d440300201030b0a058012224964002403510892841d500c1107041c3e0303c079401001e504024002000414660550f60054411000a41040115901c91007141c0001d8100184100d08903220040140100000d0060318500d5010b0351052681c1034000041d03032042c0000 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 37119114 1250 37117864 37117867
    0x20303100608070203160f1101020c130c02030c0304150207080d0e0d0c05060a030506010e011704080705010905060f15040b060304020411090d03031e0501030c03080304051906020d0c05030c 83
    0x4003801140d8450000b0f0032042140400d000300c009640140404090b06170244011000c425844e04201d13001c21100349001d810b65009406401064903000c1e001c80d520041c42c4400940b01204c040305134154402e2020210540c00700240106041080c1c080c003502c1016030f03500b00d900d01522a0007540e600e84140c50280049050090307080c00070300d00701c0d551b8072409101d00880b1035861380d0f40c80030550580220752001c02080e110f00801c55107591111030000c00e1310092070150103000140380008820000504003906211700014150305018003500032000385a4400100c1d5140c3c5031518005044160070740d4000c0c2c480c0d40802a8400e00e2516000b81d01440c42d0080405295032a1035081000505910040d41120304041c02042c25503901d050400005600035100410b001070039007504191f102c400003010800c640f414005001044100081d1b905130b0f640010115039035211400c0a516244d10030004e030031074030341c4241003800b001030907006401d8240c00c019080c0b0540b584804251810f00080307401c550030040 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 37120364 1250 37119114 37119119
    0x30c030b07050706060b0a0f050301051026040c0303020c030318010503061306090207061503050303041506090c120c020601080d0c02040605040207080309070608060d03030b01110f0706020c0102030310 88
    0x2500480540c20114500740b00c0d290081c181d03143c8043d40e91a03800b140001c400407461146964105052020022151600600d1981444001030100000d502d4500c10800103400d0007144002e401075640303000718200000c4159240620300f511301c01b4002d010440050140d41c1c9031001c142800016900d85001680c0403130306d421a40d03001118160001090301c1d070301c404954031500c3d08040e10310454001c0d140d0003030050b83e1100b0b642011415035000388201d89070b032500141c0400101d1001b0041d40c0e0030550080d1280380c4110310303000c09c1002d000960050820300d0310700709401d0f1100f80c01941c0001e492040000500965000d000c0c01d90301d55800348200f101a401c0059846070f20b40c440c26926a002c0d2004100003110b1b92030344045822038011400440702000d0001c00c0c08100c010400c6030000038020703072030900a0381c500322010981e00011254020140354131144860700c41ea002b01e0069401400030401c50300300704c0b50340d51101c1d030f00e040910901c009405416036000403548080101c034031620203518803140092 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 37121614 1250 37120364 37120373
    0x170c0405010309031b05010203070212120a1518020306010f020a0c030206030702010906020d02070c05032a040b0d0f060b011407080309011b0207050907050406081503010615050c070f030c03 83
    0x5040c04030108696945003a445a60101742d5000c818024000140c8a10741f00001070301d07102c02006c21082e199401d04c0303c00001c00703014082c0c1d54008420000412421215010400c94031950b4104808078000c596090303043c41007690165204003c00d0740d5054128485110580e10307002540070182904550340c400b80301500b050b00040d600310300715200000e41029a83c981a0417a002490660086a00000c03d102401019a001009054214060024003102c5000c2c4181207403450b2100805114070101030f002580d56900085003840d025003001860755492900032403090030b002040780c44030300c1c010602d20554890400ca405001c050000e1501d02512902c030580b80c0d8000a08042685d900d481041000040100410895072420f400902d0b46a08010401c0350085006090b03500700001130204000c2c140c1d210015580001c45c4010b04540c4071702e800042405408c3c180c0100301e0606215507250300a40c2d002d402001d0400b9130b401a10061910303215440ca08a04a210141c41123210302d40c20b00204 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 37122864 1250 37121614 37121621
    0x170c030a030914030a02010b0a080102191211030f0604051b1204020607060903050a0906030b0618030f1b0405090d02060403050309010e06070504060219031d01090f0b0406170c04050103 81
    0xc03400f032582080c91104911441d45150300025460005075103a100b004c099003881c032022009404100000e5040021809141030150340b6056408104a0143c0044031100f141754014048850b07030210055507841c0c413441c1a11646002d507800e6010303618280008083d02900c60341c9011045194420718039000354649404960a00900260f9100800b0403901c0c000a8807072059040703031403194640546034512010701a00300402e0394000f00c14075080c52009a01c50f42c4005c1258031581403500341c03042c4c0c080720001191614000a24009031031261946010341d03490911000d11022070211018441a980c1006132a101c170880312001c005640950046000240220003660b40400038000018016052070f5001d441d0000644035400481e40024040c1b081c1036040c44a5905005c0c40408101c0000059400400800426685c81c2c0ea00403a01051011603204004610040003600c6a00b45415169907400c0d0365507005200707000c0450704410840404501040056205004008440741081c1c541750064000e1b = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 37124114 1250 37122864 37122881
    0x1002070b09100908060106080402030609211b060106050d0b010201090809010302030c070b070804020a1d07050a020f070305031305010813021c06020d090302010510030503190c12030504170c030a03 86
    0x14860703242d0000c44c0b000d00030821a03000b04543d070740d17414643c01e0070b00505003007110150a5019980080380c1d80034425204450590860919918042d512070b4840407000b03000d4042103c0303052500918000007000c82e230146c00303840315113440c000800040343c614005a08a424041008040320000e200420840d802a0301450b4441e80f5603544620341606983e4a5910160445600021a0300c0b00240401d6042180c4044043d0144d42d40d1307095540c201402c0715250160080c448000c1220000b00c043d090341c428468030410301c1c454022141095120301d091f60301d80c2c010ba8880006504100c1c4006150741c460603d05000349405201b0100e10b22003074080c403440c000410b454500c52102d51181400180441c030041801015441c0d0004648000e850001c0c2521405003c4c14003079045440b0a002041d400b1007205c003410841d20000303000d1080d4000c01c1d640b201c240c01340644070105410026440d6601a0402441640301e404cc0385180e412400000110780150340c07011006074028052100c1082c02984480d56 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 37125364 1250 37124114 37124117
    0x5040b0f0a030309031707110d030203090d11090c090a180204050d11030609070510030b03011d030712020a030f11150a0b0301060905070e090411030601141002070b0910 74
    0x800d50880004140640c406500840024824080070001c0c00715800f01d100b4071100e0b621540c1d1629005071a07144100c04200e42462181c107001402c0020036000f013084404601018125520403030f40c4c1c0c20703c0c4803003001c2c5010711405180e06c10002005a0941801c0710103d081c010314500d40340b414400100e80038500421f0101610740e01b00000308081d5a51880c48074410f2007043c81200700c03980f0b20b05040c00c0080203007600340d07564480c910910544d5250540c0070100700c824030300050398032082d030f0020f07014000c0e501c40040070865841d04050910800300003030190900500c49400415040c2100b2a990420741e40040c00240005003101c00c0503105154141381d0300450030880307411000b103a500da40204002d40b604415260703603120b80902800c00f030023048014401b00710200700c1440d00700c1c1c0103400b00e141913075180c2c4101c1b07073703540098100940200c68010b007017000360440b5104c2da1a00f0541007603561740804140b05030210001540d00c0c03880000e00c3c00c00c0c0e40d140300440e03050826150a00100411400c0a00d0 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 37126614 1250 37125364 37125379
    0x20706110111030c0d0b0d0b0703090f0f03050702010807090602120a020f070801060f09090b0103020607021503130b06090402010f031505040f060603110711010c0303020903030a080415090c05040b 86
    0x400b01c100b02015602a040a0b9045940ea143d542e0000c07086681c1030803554080c1456030115030104441d1301c07055074001b01d40d06001c10184010b00e0044025a030f0780c2030041541c0e0840c1c1000c1c085c558400003a04919100381c0398003120362558403098880c1c0286102e200010f074021030100c0e40e8600c001000e00003c404c503004413a18000152500c82c00d10900307420085140c2e5442d0b400b040b45c03805049071070004201010341004951034646403c18000014080a40940f00004848045440d80003440207101d0740b181c0701d2922400c2495501d0442001c00c801619400d0042c0085841032520102190185605850b13802d50904508010340161000500a009038248264001036a440360302138407540d1101c241d00010501d0034020302804444210380c1d15210f940007404090005080d06040e806400000d0030000b00d5100c1924044010f84100110385030503000c00704061015035088243c15029a1060741e0554610880d4a0341c5011110182170141040c01415410041403c0a5200700d40c0c28401038807a6 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 37127864 1250 37126614 37126631
    0xb0103020d2406090509040807050a0b0f0603210304110a1208040f0902040305070902030a23070f110a02010e0d020a08030d0501060c08091905120a15020301060207061101 75
    0x7100c2c0721001c240d618082040d03062038255290512200902644e05181e81c2c66070070400860305100c00108024100030f400103148080c4003040198900142c1d0000da0f0004500d0500382c1c2116510041e500035009100fa90000f8011806810141c0440c04a0031003990856640782c80da0040c80c200880c0083d0426040c40c000b00d0480501c80007010354a001e201010350711840d00515003010196684001041441404140005440031903100101c030760020015849446104226004285c500d204c030355000f2181d941118040c0703184038454442c82d0300d52254101207031503520946d0907812540400740b00750800c03010000150b024000d08014810080c240301040c882a80c040f90648a03550032440d455803010840080d9400b40780242400741060703242a0301c00321159039615a442c01984140c51161681400d19404006482489001080000c045441d020000b50b803903502e654612000707451600d0406803100410800d4004c40341211020750082ca45149800c60132245541d01d4541c1c8080e954030383c40403 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 37129114 1250 37127864 37127887
    0x31703040609020306150906030c0109060f030f06090b03010506011d0607050a020306040b1f05090a020306040207061b0e010306030818031204030302060601090608090d1d060705071d090c040b010302 87
    0x2610306c6032115901a05100740340004015000d64010a0b0a1195000680070600c69034406110000c40c4c20a00b88800301500c3e800080d806442c50401d4002e81c0c9103071503400a00110980c010710130064041e0002c109036180c0300011140040c14040003800c141c0d0039020701065080580045c408540640295669070140c0e50009041050546080e0307055088601400031a6003103074800b00f480c0c219117503440d424915240215400340e0004215914070782c1c1c0800081c9084d02c450f01117035655980b11604011030341d02103200c5415180d500e4100d00000d03000358840080395010f07101380d6054030380010300242018400c0344040d440c0201000480d4160254400740a0380c003550001420195102e138010f0070743c600d0010001000d41e03403954014401c200d001c00c1070000c440b102180e120f1484490b45051138461080510f01d08401c58042155500300100007101014041c01140c0300d025241c2043d1050445e082c4c00071180366000064940307840360b0704a40c5250800c0d142541c000c01510506040250400500484 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 37130364 1250 37129114 37129123
    0x2120f0c12070605010b0a0e10090803070b0703061710050703090c0306020705060f060607060b03030c030a0e03010501051002100b180106050a080a15050105030a0f18060c090317030406090203 84
    0xd24195030046002020040f49004481c0505a682407041c01c00201d040c00400941c18140b45030b0082c0707401100c00b50603902c10040100542881c6d01102c2d56030a5078509145e180300c088a0020010b03107010b4000c80c19030f0303c000f5640e1512502c03100808001c504901c2120040201519880c14140e07100301c80030000d01581c86040040d03019403001615501c0d039061107401d0203c000c24082041164130200583c580e11070056607a2190000d200083d00340701000424514030420008004512011071510035656101c819115000341c03e038001e0050342da94409010710042e8030002c200c05030f0004480402c91146640c44200d4450b40180b842030842045422101080d4080c0c0000700080c60008054000507005001c9540018102e00208003800603101d00031054001c9001d21410490004081521f42c001600072012381101e0b27003c1045400c4910f078580d10361101140702110301904003480c1000250165440f10122500300004000c0c0d048ac8450040d600e030310080c000c60b14503903510800c0016880400 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 37131614 1250 37130364 37130383
    0x9030d1109092a0708030f1506030a0b0a0e0c0403080a02010b04090b070e090606160807080408011b050403030801060302030406020c06090318030c0f090403020f15060406140102120f0c 81
    0x140c940c500070200442e0343c00006a03d1640400700004008040005140c80f04499101070313202d4168070151100d030b490b581ca1000c490111350780400040107205200704254450b00d030766841100c801010560303c10010030881d2040701c0d0908580401d0104101190407c0c0051482c00201d1000040e0310b40003034005811151450000d036005405e44c010401c3d150b80010b45111581400c0f14400414506070000071014070400500d002c072582290200d00801842c2410390702420340c044040741d00c840d01ca965590007013072091403035801c0404071014010b03401d00404c100d074244c0c1c2d00355640c03101c1c1e40e08004040d0060340c0050000c070f8640f9070030050361600c0b900500030b45019081c584051960350303014554400a541d5600007061091b00b2442c0350740965503030b05468800552003601c200c009079883c0d00b0207a007480c0c0e11041c0e044444c05044144240c4400c081c01481c0b0030700080340e040011980700d030bc035044c5140380b4661182c050303032100c18260007000d0048080c0030b4074020400440e1400d40310302511400d291214 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 37132864 1250 37131614 37131631
    0x18030f10090c0503210c031b0303100b07031d0607051f06080d0203031501170a020a031b0215250201020715140103030503130c080c0108090609030d110909 68
    0x2400030740304000e12010701e000180021002080010500301d100c201c0a150005115001000010140a0000d042c01a1a16590030710340000c2d1414103018042c0d1694811514510129401e01d00416001c610500740c9001503050b6803071f10425520f144007a4030401c000008240d100009000c2c00d00000c0d020031800c1b0701c1c40f90020107501200c9203001d40d1000c0c1c070b0300c6410a1450b41c1058036040300e05540002138940c0060010303501c1a038600903c0042c3c650090864140941202c070104100c100c0030036400621845241d81e80400200b00144800c26141240c24100030050f0061049400883d052440054008a8040b40b0034042924001d40f1550101210440703c0540d4020400c4002d02599107503000740002e054a041c401590500390440d51110140001001e008012000c100064000c0d0710211009601c04030345428251190400780c0c2d680307480c00585000910a20001da0f01a00105540d40127100c000c0c01141010610311003400070384207804821001d8403040c4018011643c0d10300002e070103012034 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 37134114 1250 37132864 37132871
    0x10b01080705030105031f0b1005120a0203010b0403060e0f0616020613050712050102090d0303060905060f090c0706021303030f14030c040306090302010b04050414010e0f0318030f10 80
    0x1520003003004000c9030500c101400100070544010410500c559500824528150410480e000c002c0c041002d420b0742240c008081038001d103230494010102d42c00491410110759440c00d115406034803090155a1003483c0034001040010060340040900d4075445007a07860405d03c1c00013591401604880c0c0e40d03034084940103104c0c9016014481c203604003204a860702403540c46078071f5551307981a03c1c0c0b2650001d9020b0455034410310400394140c07408420000c00207004843c0c5400c000300523101602a500d4200e02d4040421703083d141138410fa540810010701100700e41d990b03400380354040f42c01408041c1c54182c3c0801c554054410700d200c074000694442d840e01a0002d100342d4000b800100c2d4041007540440b01042800a130303c0e120f40a0342d00f2a5072149010440d90b4003864101e014058450710141c02505080901040101c0d640b51203607080030390310080202080001980d903481d110340e10f42140917041040b031405501c1b20000c0c01501000c1c040d04a034203480b015110a464021040e4100c446682d8 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 37135364 1250 37134114 37134131
    0xc030d050c09120105160809030705030c0601050906010f090302010518040203010f080114040b0c07031e08040302010b0109051302090406030807050a060612020306071101060f120506100317030406060506070501 92
    0x90040f01c03850a400081d000308210b01d00740000355401d08511b0709620621074107600082c0c1071707042041100c07011944130b01a642c551400c1d44281c1e82d02c8900303000e100d1183c4420000118654800d1102d1002080b0b155241100c0c0c0c0d146800555950740a08112403006d802045029815111f038002503000b0194100300d0000f0600c0d1000e81801c40e10002450b0025907044000d2001040c440e850807900464030303904150b514941490142d601d00c003840c08090304c244180e080252403a4001c1c00c51031083c1d00030b80003403240046075401140c0c00c4150f405038603400040555455443c081c654050600080041d00005031992241c8403103020750004d007012600c0e60b01070440c0104202c02401864010888207100c0300088685600094903410014441c1742002a0740e41130800840f001d42045000781040c0000c82c8101d07848418800d8811301460741075404e481a100861006150b0104800c106c903007100812450509440060090350300181040c1c4e80c10f5103805022407a035496000034409207108000010320082c = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 37136614 1250 37135364 37135369
    0xb04050a09020403021302090315011203080f010f2601060b130b030c1207030615090501020f070807051507020307060302071e1203090f0c0608040b0112050a080c030d050c09 76
    0x51640e0400700d1580d005010420040c3c8075220750100e42004060701580761803811020a2818040382e01d01485410400300014582c60b49142c42c91141c2d009a9902c0425038400004c142000300030310603941e002e5840c030810007400c1d050804070302001407a82590a0340c0c1400d001e00e5802d5450395007002074100780c0054501d5424848905540051a2400c0303041d0462429655582c003034003c413600c03000c1c0e0341650070000300490700c258840d401800c402e070940381f0b540d000d40c0c800401e000028003505000d442035210800c0b0301c01c000540d8004407040d40c0010107401d41000c05018002104c100700a00c0d0750700500ca40e0300141c1d0140000d40241066903001600c490030b500704031070b0106600c1c10443d59503071000d4194001c507486030a408401070040c2400304804e01e503031418013605142290068104513000e4408501d032940503402901440c0165200106a600d6450030740c04082ca0300001051513101d84107880000b00c08c02c0180050101c22002d4a090003000c2c4041d205443c02201e00c240203200004005c4030a2 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 37137864 1250 37136614 37136629
    0x80601020d09030201050d0203041e080301050f040e06070e0102030409140a060e04020307270509030a170108030403030305040602091c02030d0e0108011202040207051b0a06170f0c09030102040b0405 87
    0x2500d06140c02070b03020b4030390f8001034040c1c07080c841c1c80380380e040d0000001800c0c4140c1c04c5109035040d000c00800802d0700000c0c20f046d1080d8200b07016440c0708400000e40722a0b0f0b0310f454001c014100341290084e10a688a0351000d0742c1c0d0041030350006055000038080040e02e108184a20544080020b8030715103c0c1c580159940201c0d05181c0016030400030f01001e000140e100042d4620a40e90100c0c91003400104000180c0290114203100110b042d0801c410803020380301c040301824000c2c105842c0c0d0004140c2c00b5040e40041407003409900c0c10b6600600c02040401d01c65001141c1182c00786000510340400c2e00302207030030341040c0c40e80c011801105002590440c10100803035028440946442d951103640440005c5ca0750030180b09024074088021310020555803940c1c104c6441d01d5011044800c2e4510652104402e011500c03105481944040c1001424a024160607911584400100c561039554007490000b84403004d03080c4c0a0119050190808a450074802170001d04010101162111724100812150 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 37139114 1250 37137864 37137883
    0x10509160e040b15070305040e0f010b1206010c060507180f0501020304170f061801050a020301032301060806010b070b0108010b01050708030a090602040b0d0e06160c110405010608060102 82
    0xa84421001200e0026403007001ca0003444011680480c6541c504000030720540c0424544880143c0d0020303500c1e041680200041040f142c810242d917240b607031500c40c2032195000034460050201c200b08103110000410981d281d81c001c00504101140500c1c1d5240c04045640c11600c29003c100d03d0145032040f500c440010900410003000200c8006090a000079140e0045105403498120755403030100d105841403080a2a04200b44101e4000d07141c8507000b102d807803900f9070041405518100100b41854024022a03041c1d0f0f800c4007043e1070f100c4800c0084900784202494041c00ca559415003c075407480c00340505402418450b0309140c480b5591700300381c4008181030388803440e16894100307a0440780e6001000d903010707142c12641a503202c0c0ea4040f040c1014182d00c0c0c20041c1550720004000c1000051400584401c0d0b8552a00f04211051030705226602e4809440030041c1c55a600e9140520a20410705014080e201c2c103145405461107102081c06d1322001c3e0049404038604008100d01540d040000114 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 37140364 1250 37139114 37139131
    0x2010b0409051c110102030a020301060f02011802090c120f06010e0f0d020d031119030318020d020603070207091b0318121409030a050705040f09080405091308030906010509 76
    0xc0380003980e0b900c2d6440d000010a1011092510862682c00c0c1c01811400d400701440c20003036582c0d152024140009520900038400030608241200b4030043c03051207451079a1000501d1440d810b28103070200003031150001d1082d0360f20702c81003142010400e8111205ca0240c043d0120581d0182030030400503000550b100764450050081d41c01e06c035041e80e03d010212040a4050300c10340d001180740e06003214032100b901f04040300c83c8509042e4141c030106c2341450241c0c89000741d50412100c03094940c444d151a00710440654840c0c3c000c03800c100907103004002150851814012110115a110070038801d803084403849040051100b030400e000c45070140144e00702000030116040090015642d2380314000403600c003000c10444040b9550328000c03060811284002001130031141d9180880c43c100c0c1e900d00706401203d015508000e001c078104426401000e44543d40454400d0901d81404280044014000c00302450f9540030928000031805010003035009c0c010b4080600900d60414040c42281c8402030914007 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 37141614 1250 37140364 37140371
    0x100b032a0c060106300f020412030206010602070608061e010e13060e0a050603030706020a0903080d0903111606030b06121303090605030412030b01110d030c08010506040f0317040b070c050102010b04 87
    0x120381400711030217141c0d4185110740003500049505030040240a26002102d804c200b4010311000d00d600041c84d14103c40066084481640c4c803030301c04890803002910800d0300000000c980007400c0075404014880518185028010300601c040000c2507010311100c0c5817140790b0340e40d400344441a1003451441d4090a0300f0014010780c1041d9021940d207100c0c1ca64007902285e80424611402e03882000000300854011415036110003510000c10700a100c95542203001c14807400d00300040c1c002c0460605540488054181605071401c401035015120548501d0342c4800c017041490381c8074080744030460140300c0b0035410104060f114900a801d01d40c482d040803003442001d00810001609149012007000d03013502e804030b100c5c130714040180c4204161090b00982401841480450650302d40c0c0708000d01429640c94070041e03640d5506001c0c2ea886140681c40d52000903c40a1010511580b6003041890454140900e0aa5503080d14115900100c000b198070031845e22041100d50381c24010059035100889042 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 37142864 1250 37141614 37141667
    0xb030a05070b0f04050a091a010e090604020c07080a0303060608010603051308070201050705060f0a060b0c0a060c11030c01050604050705031003032a060e06100b032a0c060106 77
    0x1d580e19100d11a551070020005011145500c410050342c000300009171400d9074281d15040214060000f80a41390824002e541d40e11000350301c03a4400410701e1201170301000d0a61290070900000e5030000c880d105c0c00384294200058405002c10000b06800d02070b68001417000d0900100510700700041e40950201420b0205002100d0660030000341910b51042e04591340d5013051005032007a028000025205003d09820002c041c4031000d9107601c00c1c0d400007000c0200c103446980c0041203000741d181049490740700c2092800020059400303860116a503003045072000551980191459000c940c1b81c03511651140c0c00e000030b1341094000e003a0800c0103030a00341d0070352403d42034880503c10148000f500308440400c03682d07503d090700c0120310b100c0c10120600312803495045c1030010190105010741c08840c400c1100003a0136100e4a452035040c0c40c9600700161031070f20b50340088890711804e041003003250840034807039540c8095444020000c107085000601940c2d8034010024041c80900b540001d0000c11240e01c4 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 37144114 1250 37142864 37142873
    0x7020d05070303180602070603150e0403030605040e0a050309040e0a020306160905151905040b07110a0b0304030207030b15040e010e010506040b0604030b10050a1d070f08010501210f020d0b030a 85
    0x1100c1c12345029181c009410034440700c00c40111211135001021896000e002d21060681c1604400240c8605680234400d80800c1d4401d603a5840c40f0314000b402c20380040c804034440d440c040c1c0064030440a81801ca40205400d6000a41440d0f0181d6024000d40d00040c04214101e400c40d00ca08005d0100b15812241007000d4070480c2440e00c45c0c0c80c2d0752401000c2c0b845019480c42d0288007640c02400138042c5094480f1500d2034068007007849210010701c6030401240002c0d0f1006246c044921850703041d800b13009400d26642d20a07855000180a250320440304403100d1016440c0d503c0b03407043c00c207042d1002181001071488600e00f140c4d80688200c3c0268108100c40720710b80ca44804a4040340d0340410109035580c0d8041c18002002d095030000c641c065040100040e50042640b0207003c0d240c503c0c58404d1850b02e40440030348201c009000d020700400c990600400c01076014940740a0058040740a640c151261003a1120440d06400040c101095011503102078900c0d83d84907000f8074900640080148641d0340c1c45 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 37145364 1250 37144114 37144123
    0x1180605150619140307030207170702010e06071a040c030b1006050a0e06090a08030703140304020a14060d0c1e05120112150906090303050f0f0402090a0207020d05070303180602 78
    0x20000c1da1800911110090f58411820301d5000c0300751400f04c3e601d0b800c05610050280d40031a00079295544800d0380d490000e85540c080350b0019905855a00a20b415035060111503080250266a00109014035010303030002e04d288180309034400d20f85521498118a03140f1a25140030303001985001100c103040c0580341e003001c2155100c01c1f8a003005199200c2c8400065a144605241c280e0040400240024403450000203000350300d100b6211003005280d5440c1c0345d551070008803006903002140807001c01030900c4a240e000b00a0401519241c80e104005520600791490743d1843d5000410b03403120410691600c281a050900d11441d11a02e0001c00c034440443c4244180a03441020030100041c05c200009140e02d44902c8904010a0141d980d050400400602c1448402ea0100c3c2c10b000014005815451603a4882c02800381503e0983d00d0f26020310590031001040340c40720950810501d80981d8508040340f030001e10540003000d440f03095103001048070030f6192036250345014104003486240e80115 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 37146614 1250 37145364 37145377
    0xd0c050c0a0b06030a230c010c05030a050306042301050306070315030204050709030c06030c0e2e0e0301060b1e03010501021902011205070201150b0f04030213060503011806051506 79
    0x181c0040d0b41d8036480002418040302d00c030014a15603100544540c041000341a20a601c078000065611855031400151110f60092a000f441354100b000704041c12030069010b142c20035400f40c40082c5656408515407800300310000e0312412181482d0041009150400c00380e0380c420100d14050140742090802c00c80c0c3d110f920f01000b071141d5140c000164115204101810041d034024064000440e501d031009002041c0c0011583c3c0060040481040c0a00b0000300150341c0505c0c01e406d152a0301107020309131440180269940080204080c0203900a035802d015010182183c0c0194a50710031102501c0500f4100b042c00180080c00180300400260b80c010981d0392408488179102400314442e84012512883d2a100384c100c80c45ca00001d1080050b0705500054003078502c0c040c030007411620340b0420080c0c1e01039104600b0400c08108024801800c0a444030000e5001c1710a01241d02a01c4600190070f40b584d403001c0340c1030354007840740d40e6041c4503441c01142c1d00081c420b201244400382c41400714035903200d2007 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 37147864 1250 37146614 37146623
    0x5072d060902030c06130f0609120b0a06050a06020705031509030a050a14030a05010e18100b03070b040603090b0f06030c04021b010c0f170609010909050f030406050d0c050c0a 77
    0x501c9401c0642d10184126210340c0f400500090b540c08180740e0865164149000e0301c00300e81562400070807518060410f003420788014a084090103d815940c4042c0c0703038001849800e000e52204000200398446100d0100580440d8001d46005070500d024140f42040c1c0c9101c000c9401c090384203100f94580e02100315000b80c0c2c0c50b03181c8141e46e08014081615078110a80186c2e40041001040041c4011298410303416551185003c81207515562008105c215100000c120306421600d0040750301304050b8008000303d00040c0684a286a84400c00b40361600642c0c05200403a1300c6501c0b940403c0140c045950f48158203100394070f0681005004030741e441c20a03800160240e603000030300815050540d10000d8400c003000000703001072074400000501c0486183c0b1850301060642818080c0b02c2c035100202482640060200c1035641c0c46c1c110703640701500004034140c41074000d0326000c1c07a202e94140001c2c0081e10094444555440a1031000000c07180f62650b40d8040010034080c0b00c01c401c6021481600040e0007 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 37149114 1250 37147864 37147871
    0x31803031302010f020a170703030c0302180f0a03210201060b0414011b0803070e01020f030702010c080702060708191806050901030b03031b060a0b01020106050a090c02150705072d06 80
    0x10302c04282d00d01041c086c40600824643d0342c1c02d001b0b800828000305401362280c0d400303104042c0492000d07016405044802d0f0002c00d80040c41440b941040114108150002080400fa0755680c0c1c48010307102034010314800c0124881c0600340001c0340c09000f020001e0984041c3d20b440c040c5049188009a011a1080d03410008001111040e5054002604510301d401c4000e09517641000c0718003034800d500c0340c40710b41c2c054011006000b405407408000c0d610040d40686403c00340407007969811030380350b014690403613000d4011f00c910f00c0407840c501c0c050800080d2502e5014003200c80014080c002816a445a01e0000e0700d10b84c06102c074035441780660f100960b0a080100b040c1c0700d401c1c006821801109400c6500a8104441d03042a031400103c060203002c0e441c030304020310300c1c00e0401203003030300c840d4028503422400c105010016100e0b960b100001c8030b6100c0c4159400020f0300c01d0f10342030a120a0761100e00103600400c5410074440300c000004400e05064020400034038403514000c000802600c00548095603 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 37150364 1250 37149114 37149137
    0x5010504180206030f070c200f0405100b030c16030f11030703090b0d0908031614040521030c0106060c05100506010207050d020307090204060503090607080f04020607060e07090203180303130201 85
    0x8111410101d1340c8102c04150b0f4040d0885071202e00f001118403288603209d0300d490181c1031308003881000d01503402155213000d0036044c50f5405800b035002400d040c1e010401008200504000c10032510515807003503981d254440b00d247d0009180e11085291005150810414400001d8003c96020125071580081c503854420503100440104001c68000d8440113000003042145400b224014a81c60343c10348030042c3c8048484800c602c0e82c0198060143c021900881420181040050304881501c001c0c0c1128907020821041c642901d440794400404034103d1100c0504021091080030781303004510340200703d18503000300000c2d0385154611519029201c50f280110135520140607817000790202d06420b41d81e650b030b21240148903620498001f1604d02960001c21300742031090300864040d4510417804d6447d511140c00b002101d038000f820442e500d07556040e001502d44024000c120091142c840016200d290080a1000c1c45941c40d02100e0340b50020003c002c20100301c60140c001c680c0d02840c1c03000d0f4070346 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 37151614 1250 37150364 37150367
    0x10512040f060e01020301050a120c140d0804080102070b0f07170603070b27030a030206060105090a051008220302070308030a110403050a050114070c02040e0c040e0105010504180206030f07 83
    0x3940c610002e005207090005050041c0c0054000318101d885c203441b4a07a80d180c2d10008030441c2c1584c084010101d1081403010040e00c0d031044004400030320000d1109040704115540c10245078070640c00500c499401244003414882140c4800e40e011100e9a23180c1700900d00603a001b000c200e6031450003240d1a0152001c50f809440422031a406007018001d0703590380e000200020040e4021001d449011150040e0648003141004105480d119034982c00800300c64544100544280e080544003e801c90045080015940c0e100d080e184409112a10303036907004c0c2803450780c548840212184543e04440744c1041e060019500141e180200c9400c1840c2e192207403111000c1e10080c00e01016a00d2900d4808140401400b5010030012500c0b44200001c110803002e401414010743e40c1210480b012801061484d4090308003a003081c030546025800b9120102480300008048420031a40324890383c0d9100f0060105017068410205605046c11aa445402440d8009159880020084183c1c011084085003156 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 37152864 1250 37151614 37151633
    0x901080a0209040e0f0d0201020a0504140409060f09020109080d0c020402030a06090c200105150103090312020a0504030b09060103110d140601240804110411040f080f100b01051204 79
    0x1c0000f803040c803020007400011036031007283c2c4601e110240124100b58124a005108075a40100e5a480c0d840c02c21b440d050000c440c408040c901150420340f50049000003441c184902010203010b907800043c030340c40d01c0c0001002107200303403c10869a1720036021003003110b80104400610381e90407280035980f41e03140301d002c0c0e001d030402c1e0b8442c0384010304180b01d00c0301c0039402030800c01072001c0b1290081950520405924281c51050320b2404440500403403031003003540309403c81c42c0c03018024140284030510203422042241d01550f0b00c20700041c0082818400c002914410540081541005042c9075042d80c0320380398a080c2e41e0310340c0c9200f45010304801c0700300803891403c2d034501540c3c0b005030f03844e66942e030343c0450201400b03008070424980741d101c41c804a01d008a000e10b02031508240b5081003e8020b07420304c0300905c4200d012000703002040c4400156600d0031182040038107040c00182248140301049585800118040e0040d521705201c0c90401c1641c1c000203070b640040c0d800714141c0254aaa041c00502c1 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 37154114 1250 37152864 37152877
    0xd02070c030b010e09070608040b040503190504150306081b0a030606080c2107231309030908030a050715020c060406090b011215021b15090c04020403080901080a02 72
    0x25040e600d900042440034403040103048449180070303040b03103075030b203003195034484680d40640e8020600e0b20000c900402c0303001d80d405a01c144100101c0c1d29080b240d08003513540c4080031100e840041c40000c0d080c00802c807115010400b0003043d00301403040c1070070b124820343c640640798605032561070410071071a126a256040fa60040d50005020400349494a40d40d5840700305a031003d80c0a45081206914144c0381c01c1540c200546062000d000c1241c20544c940c1c00303240300e200e0f54140c0350700c100740f03080c140d030b03880f049aa070316004181030000e080215403401604250081d440f003003083c1c0081c400c40c24203941000c11600502d030300200c3c0e1280e48400e130f581c2600901440718503580c1ea2154401b040308008441d4480d14029010300707118080740c0e176229090101c0c600c00c0c0c5d100800c1c3d04207942102095403045c2d000790072040c0c0c03400707802550b400307055414520304820604c26401445442c41400152001441840102c400582e0154903190842d10340584a10485240c01d04029895001540407201c40d81651030 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 37155364 1250 37154114 37154123
    0x81506100e060a0305040b010e04030e010f020c031504150605090c0c01110703030e010b0a1203030e07080604030f1106070504030231020406020705040c0e010c05031908070e0f0a09020d0207 83
    0x40390254000010010035049400325140107c920001c50300c100303000c41da0352086074140d58008084682100468403000025020800c1d0310035401060340540d400d02aa0f04540074081c20580b0918207418568605503001c4c042c450205e107040d00034096074a070401642e40c0301c55150b4210b551a568003620f140101043d42191f802600046480c10425a042d00301c0744400021500a01240e00c5140030080a22090310541e80a51b190008401c0005c0c041c0d001464540701d039000340c4946558038104c035800c0c58400c40b02100011010f203810046250404090000f01410000034a091b181440019100c0e11550001074405e00c58898800c1501c0852000c1040c0609040d8501c0c20707a168510060b800394100c1c0c014040903005a8501103400c0c1860b03c591480091140c3d904030300043d11400660301e80400d07200035111800100100c040020564210034001401035a55901910b070900008200040740900c092003258890700d41d007619074030000c001e030564031462001640da00c4400661802072049200090 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 37156614 1250 37155364 37155367
    0x50f0f0403020f120306030c22090606030b04050309090907030206120a0b041e0b0411030a0207081608040f0e06090c0c010221010914010b18010e040510030c081506100e06 75
    0x1a40888a81301550143c2000e9080700d20404e2080c080041c0c0c0310080d407800300340003014400c0c662181c1c03480c0c00030b510490280d03400244880e100d4075444440d902c222001e80d80d81e40005180d440c14105404241d500040e590302038074015055034000f61843c031030030000740031561004000c0381d001d0846900400c007844009004004400c521020b500e420a00030b040c40c1d003064503140b01c21050b8240b0740113880012482c000d0b550316543e2032800000081d001405c0550301c00d10180070440d103d0080703c1c3c01d408200d009440e519100c5107044103105403007207140c110030f103511819014045903880c5d0840c0160014034003145203803501165080340740280120701040300a402118030880040d22514070045c10384103a0301c0c00f448a17042c41d002511158030288140d01c4440342c10003400481c0420421010000c14052400b8500440041300041c00c3e10021396208000c071000440400c20040b40807004401495a00c0161255422100140e1541d03100284140d000e2414000f100d51258480c40030a020410014044e5 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 37157864 1250 37156614 37156633
    0x10050d030c0302070605120a020f1608030619030807030f0318030804110102030715090f020d060516080c070b04020f060f0408060105011805010521010801021804050f0f0403020f 78
    0x182610320350030081d070140c064013001092981c401c00444604d400e035080c036040544c0b9540c016400a511071809403440200c188502e4042e000d415242d46402401916510384908000041040c06006118001c0c5a8940e070441000001e28034810795030030503014104400b040203002c000307030094079502003104021740003150b001003010340206001d40500d0203281c00d8080c1c000010700580c0e42c0c0c450400050310b041c2034513942a400a91641100001c284103441c0882c0780c1d605680811160303590789500b280c040c2e8440b010485442d4040400e10003c0030303145030050f098205248000b1944c80342c00c1018201a840c0000201503440382d022240800401800301959060100d1201100b60010b00490415010b03000001695610401d050a00c140b20b080c242c4804a14241c01034035241d0000004c508492041c40500180c1074400c01070500070a80c0c80005a43d13042e2414046165194428240388100e10303240070f00c10144801e00011398840001680081035440b90304003607151002c00410074400384100e1804 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 37159114 1250 37157864 37157867
    0xc031803051911040b0603160e04060906030b160518030f0f010501031b0e1501030f091407050109260f03070c0f050618040209040902130b09010b07030c02060310050d03 74
    0x2407405540542c0f440d4600300000b41c100410740d85500d100316130004082c00842c0310910031082440d10140142012408016410003280c1991550f030311824299958640400500c061125103030350081c1c542c6688c00410201c401c01401b41e010384080d840703040400e11940001c0b44c03030803c1460b1410580004903004511a0840780340a800c003404211045510040106441d40942440405807100c0280c5c5000c0c540e55401152115016078001c80c1c101521140c4d42000318a41d40300b5406014003803284e11800192070304140b0b1900c40560300c0705040000c510010000102c9504107507540030810306002c1c11604142c0c2c0c0d10345c60803101c010161102d000c0001c0c10020002101440801c45403103c60703c0d51b20990340d108100890241e151810040705016401a25500c1d01e68001d0503405c0c8014000110352140b900840c0d01c4005911b1011901380e52054042c800307240110b58240100b80b000d01c980d240c19042d03507008001c038204683c024001c0c0d0b004404030355a1400c20b40c110001e031001500a0390b12011a040 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 37160364 1250 37159114 37159153
    0x150a080309090118090f0c03021c0305070f020f090403080114010c020102121812070e0a02030f0f100b040602030c161805060a030212010207060c08090c060c030c120705010b09070c03180305 83
    0x2248941052440a00e054ac200d0b4143c4c0707801505900e803181415020740300c0c800b1880240390100e03401100c10b105220b8540c0c43d0403401d4041c50083d511180070f58103252039800c00d00c0f480b82c052414028100c0e80540140c1c0c0c0046d10240c40c00030740d13180c103032254043c01c81031040f21740006121740c0c0f003045400c0c11000680000348141c1212510051414140c442a44d454101c1c03201303035844609030041500042e01103103d1480941c000d40711100302801f0580e03d2401c2c295542184e00318000682002404601c00d00080100c82c03040540300400c1e80c906403400c1e002003851001014400400358441001907100c1d80c5007074001c001187c0144c10070745101101c1c09040c0c000c2d44041c00407107609240c05480410070344107502c014401c40e00e9000a00300301142c3c0701005103980019262510074801048482c00102e410300c00301c450300001d401401c0c0c4550351481c2c45400c4d6a100c104513070041c1c2d04041045546039021026030b0145806003024000e0b4240b04060b0002000542c00207000c51080007040102251a4035 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 37161614 1250 37160364 37160369
    0x1060201050c160c0b21100b0f1809070903060509190b070c0203030f07031b0804060302070f0206070605060a060201110d020c03190f030f15050405060d0605150a080309090118090f0c 80
    0x130702442061b610751f60980706013800e0307014200008909101c0c81010003a40740003001d5007290528060002c003582c0d400641c8102c000c503604e60003c0c00a581c2082001181d018440d0802044005061a40342c0c0340d01c0184001001603000d054844d007080424a40d80c05100b0030740311507030080c3c241ca42c0d4070b0314503034250f02952040c50210001200c00d07c1119000e440c403c680c84590b5401101d072407501340340400131070207900f0600d01a2030480c040860780307005980c0c00000702141485868045a40c4c901501000451080b942c0980700390790400381c0e514010107002c0100c44000b80701040040e1030303c02d186e1185107103000341c4084541c084041c1c2c41780c02503e0340103802c00c005400c09075000d2201d102411366000a64681c41140c03041124110800d02a518040e0410b692100000d441c03502c0c10007a030b440d9642500d60a9416851590441c0030540c9981003030280c2d04050b001010066143c10401400b1860140c3c0502c0740140700f1540002c044003004561b0031030403480b50005030f101c5400d102400e02410b04034151 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 37162864 1250 37161614 37161667
    0xc02030c152e24021509100905010f0c171303090503150a060506070c03110402070b040803010501030506090114090601020102041e080f06090d0c0f0218040203010501060201050c160c0b 81
    0x2c58003c0d030301d00707200d1a4143c40001940541048221901c0c480392000d4094059100c6025103c40c0201988a43c41039000070360003000003051f81251419064210b0b055540c0708010001404a1075807074604140b00324cc0c01c42504a0583e04054803401d084550f20b10a421695250041d6103040440c102007002c00e60203000300350780800259a0b910208045032003203050040c0410020201000864003014400b09a010003400c050f25045c21940e41c210038940854046800d4034010006008130b5a152143c0c0c0c0c0d1200c015503025406505109990008000820b1818031500288000031440c0e4401c1d01640c00401c0c12446840c2510706501c0480c000e01028010705d02c41e40301303c4027002c071440e00024070240a074503040302611a0408001d0200d41000441405859086c80d0300d040d0301c01610356420301100c90411000480302c03410b01e84101825141c040e4031100841e81400d0900074410042c504450310000440281d0b14040400d25080ba10148254419241c040f408290a200c84201c20707018900354844 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 37164114 1250 37162864 37162889
    0x10f0f090b07050408070e0a0e0f070303090e060a050906030f0102180f0406031a090a0b0106050405120a03050906160c120c0806010602030d020a03090b0106030605040c02030c152e 79
    0x7102c4003161640035a00c1507400315804001c0c01c124480000c030066410030713501c0101083d13680071380000741e00e4018803088101c1c0c44c1e40031180400c14154005051409013403d007002c4c4585081c14400203a24050740d003d45841010404080346890b641005070500140c0c03110002c0d0344448038030b28000301100401140b80d0140022111a06061400d0b128400030b03294040001103148403803008070180e9142c0180032480900c220b41901e004101084903a900900160396480d0341c4508146c140100305881c030001c1c1c42203030701803040070300000e402905407083c5100a50342c9589584001c0010100308001580182410030f40e11404558807401d604103400c0d1030301810320304180b160b480e680c650745d40d0024440d540040e0010321011036940c0664004101103151480c022403802c00c103840703150104100fa0300007408640d075201b082009007014041c4d14161599070001d18100400324014540350b400004e070b400440480d000000d451111115000c0c4e1000702d011042d0340096041d0340012602c0e121600849559884 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 37165364 1250 37164114 37164121
    0x90303120906180303040b130305070602030c0405130e100209040b0a03050609060c04231f080714042108160501020306010e04060b0702010315120305040e0f010303091403010f0f090b 80
    0x1030004c2141d0065074041c0480e003080e655a22000701a0107402d4040301000810007040c0040348403070019500580f16048455a01c51610040201560305000346840b0b281c148894100300150210320840034090004015943d40389420000d0010102049001e60085503400080f040c0100010054402e410b8a001c82c0d0301621001b0160020b402688108540c40e1050700c1d1a1030848801401e0707042e000c0014017032003c1c803400540283c200804450b000c4000812500401c010198003201c0b9a05100362180c1d22440d00342441d4803100071080035180c44030015012026002085407000481e00d541c0307010303038011080b0b00c41d40c64000e000c2d6005850150000791031800c44a0ba900e0203200c0d1804550390806400c0c40d0030810780c010340142c11039005001a48001c1d01000490b00c0c2e6040c26000f00c240300f956015922410b000d64002c0760311000d41114410510b0000500020341c0001d40c1500380c81d1745408500d0084d0000300000e0142c00140d0b21495598180100000388a81c680c1000414030301c00c811201c5141d4 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 37166614 1250 37165364 37165411
    0x106050a1d01090911060c0c0102060c1905070206040807030804030b0109050f060d0606170d03060e0f040f06180b0f06030c0913020a08060412110102090102030f090303120906 77
    0x41c81c1241c160780084031030040005103001e502c2030350758510640401107248810000100170790000d0310003805a400c420a42d071180e40c0e040c010325521413088800c541c01d00c00849120901e460b580038080042c4040061018203551b55207003500c0045c22038200302c81c4643d449141100140d0014441101c18058206c0081003440030b0313000d920703c242e0903031200a4503541e5060411080c544910000c0e50f2560350b810000c10b03c1494101c0e02c0ea681c8034448000c00502c24115030040498880d0381c07250004001c450140400010302d00c1c441c9400907006140748000e001607003012070090200c109008641500c0729282020068242d400610881285009508581e10001415280c2c00c103c20701381d501c0540c000015144011185804240c44e002601d4034525546138040185040001c0c1c40607204420200002c1b14001c2e40901101003508080000303505000c500d00c0042c3d81d0b030040c5d030075000c100c0c2004030398001c0f42e880c104151000c4400210320075580e8144203202c1c40d22600c1c15a040d48005084884413150340f07 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 37167864 1250 37166614 37166639
    0x11101090f0f020d0605090f1014040b1b030106030501060906110c060d060e0901020306030106171c030b030102030403030c08090102130e07020a080706020c060114010503040b1f03050106050a 84
    0x160382100d45000101c20315030300c001414030181c0049034402804034840000c00c1c49441004d00c1082040c000345003001031910003500c0c1041403217009240b80d040c0720584000d080d00c00d02458019a000302c0c0b0000c541c65a081545212451100010300140080700015030300354076401403412640346464102c43e0710b403601070440c0c20000128500d6140d5008089200c000d041440c000c044a94900703000043c0c0030707203074031241c5060002a00c548443d69008800d00032940380a21541005140e00c01c0e038141203000065201da20784024481d40d81e480441c60340c0d803158050003504607209110000307008541c1c0b86032602d00900105180008980010314160000703110101c1442210f00100640f00d1101001e850003c45040c03211005140b0300440c000c00700f00c07000260801d00035110052003081b0258661144401e2145131420581c041c010b00101e09010307441998104d01101d4005402a100207020364074140c003003078041c00c0c0c5d280b035581c00905031400005012040d0b01000c140d42d41200c0d001c1b00c540e03480d01c0a0300d80c1c = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 37169114 1250 37167864 37167881
    0xa020301081f1d1005010503030705100203090703020d080304140c0604140604080a032003120708130b071107090506010f0c1118070323070309030513090b011101 71
    0x140c1c480e01409009100400020355506068a0080350000899600140d00c1041c00302c0e0903003d6001e15180750700d074145170240c18094003041c0c0044d41400056100c0c1a92150706520707200c003407503002001ca0301c0000e040c04800301070f540240c24034040d103180c0d203440509640103e41c285d90711441c00c040382124400218aa020203500284894200380c1400000ba03000c1d141400c184e41e00610400000501c42d80912031030100c28002c0d1640101c0c0b410003118035192003041850300002c0d420410040707a0404244011a8118040d4642102555640200100440303c100405026681c60710100501c5039070000c6060094402d900561700c440b80d4442c0700105a0b84142c4200d0f011038a400c14246400d840365010013243c50003001c844090702c1210001c07640401811044952070b15401e0104640c00b50180a620005441e602c00c00000000d01d11b08500c3c024409040c4004254032419004241031190080d940030b41500040c5692503617541c8010320040100c0307000b8501003034950076038241c801c2043c41034919 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 37170364 1250 37169114 37169129
    0x302010e061b070e0105030d05091309060b030f0318030f0a020105030712020d02071101080f012102060c060103060e060708041101050408011409010b120307080702010e06031302090a020301 83
    0x10402080000c10456411800c859008101e42d010401d00080041140c44002d141c0380340348035161350400c001c2c1070920210941450500030100041d600c19140c40c080c00f04001243c0100207042c01861600ca80074000c00540ca541c544981d0701050140d42c004001002120b2038201000240c10190081c56221810403842d0240c1e60006100e20001d2350040c1c0c0150751003901d518240c0740e0360240e081d0200403a008455541401e690203c1c40314100003605018260b820700900b07060559140003208490b00e190140501f09509208600700305030040415110041a58008e040a44411140c002140e03201c0c02440705484460801c4507800a0420204031a405420301d0340d291846a5125213506420b440000480390410800300000200744800f84260203040720380c6203900d0b07141d0500207495400c4d50030350814248a0b601c580400741d100c180c004100d0358407a0740071040c00d803240c109000580da0700d03d0301c00890390484c0c00041000080c003070844401c1081482142c0b401901d0f200d29400e401240024002c0b1035 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 37171614 1250 37170364 37170377
    0x304020402070c0512070303020607030501080d0c020a0b1206040501060c05030708031e0702010515010f09051c060509071d0c030f250302040623030708130204090f0b0a0501030201 79
    0x10054281600100b8082c3c0c06401d0000c096640ca2000c00c0d40500c3c040012201e6802034070b000d00405905029032500050207150500c002d50401c00706580b9004c0c503003040002d0143c546004000c64039200303112001040c0300a01d16460f880c000e180c07140b0b583d00c201d508911640c507140010602ea030082014a0786a0b810034011810000e0554510f590307640042c290043c45914404c00a541d0400111aa4401c5400c0d42c0085100c1c2049407149082400d00b103141e03414044803d8401c46a031760320120aa048440848804c42608440820600b10070074011016220340d08200800c80d079040f0028801089900c07041400b82809200001e03010410b04c1900c00742c50b52103080000c2800d5440c149101360700320950014540e120703914100b00b040c80c540300e82048004640c006c14204034036508400344071b0690702440c802c0744c03440d41b032071240218a1000030107030018070050b07101003660140501d444241166010740100a2101103051000440901a078100d400c003000c1800120481c0950043d1412241c0c1030b100ca2 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 37172864 1250 37171614 37171621
    0x415050607150507030b03060703050c161b1712030403050702090a0209040c12180c0e07050c0a0c140d02090a18020303031305060907030b070311040b0c010b040605100503 75
    0x806520101c0169400740c2d003450144032200441c4610750081c2000d880c00540540e942090500707201d4020b0203481450300d00420401c001d4506003c8500c0b03003805061030a0390b42ca807460005e40440e840c4045001000c10000003040c070000302d522001e08000c25504951800f00303d1040541c6600c821100240020400d00c50348006041c1154400e410030000b0710b000d414560b00c0d4010a04590101c1422000562002c1c41c0070b101c01c45034492500e1402c0f008004644100c01503c1e0010901454882c02c1e2040e01c0a10000d000281b0410503034009210100c00c6d01c0d030410107428204600f030a00d01402074040c0060764202d4451410402c0c01c440141d0240c40500c1d00d070f40781d0000d000200fa00212811241c601149810300580d02031000b507200b84441c09603011410198100f06180010081809170b10341d100745024404900d180704010f5000006280201c0e0405010043c0791281c022940411107132040882c030785a4032403040d0414202540c05490810116a44004001c400c9203a001806c01048080000c03 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 37174114 1250 37172864 37172869
    0xc01090f141c02030d1e0f080606030406140c04030507091b1107170318040207081b0705060c1b060f090d020d051501030302010c030c0806120a05011803030b041505 72
    0x5000a00d540307030b240d4108440d198011a0511030800062000035600b603440c614480304100600c801d9807414980310640882e0001d0250505002620300c520440c2c000c80050200102074026155140e4140b1140c069070920001602c0c298126000841e000d001e84840131403180814424051045404000e16081040e480002d03107419210b402908050b0145071008240c880a89280030000000310005580d9a00700e1a5040a5416000f4100d44114010041400030820304400e03192901a00010f14a410122403e110b20b071041d180d001540021003c1a1043c21050118207040090700c0d02e040c001c1c80403152000c0100f54850360354244124102440019040c2c1814203030b458031284060508101403101c0e0303c030f0a00d0001c1480002c483d10003181b0046c000c250f030a00a4800d80c0b200350030140928a9070780e44c050640d1100406040c01100014808421984200300d148511500701000300b15a03d40c0b071a410604400e400c4003500481e0400001c00ca441c10035109004280200822140984d07003403008 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 37175364 1250 37174114 37174129
    0x308030702160b070c0506040b0405090705070501090f060b010206010302090c0903100f05090d090e150607060e06060a0509010b03070c03020f0f0c0405060402070209061c140c01090f14 81
    0x180360851060703074070701411055100d8607000902640004991a40b589140c0b41d00403111940100c0c0c001c072020f010400c00e40c074403402910184d60044030761031810368440000301c501d80540c20016090b5801d0602000c14801404120180280100414803080d5401c0005980e07807003003071000a420010000004040340c100c02c000d0240b0060040555143d44c584045075030542e0804861000126031760801d02213041020001036032810400e042403400a860720103140e9440000070f00100b20909640c40e00d02152380c0f20003c44070825030040c401c02103a803a10702d1440c0d550300704a030401d000305148400401c5a28014200d203040300c070784002a914555955800b00d1355000a5141101035105611214820395414818003000c004440300514030344000004000a0b21005000280500c1c8100403403c05030300c0d803440b880d90000040d6074018183c000c00c05804481a58200045c18009090701030500d9007501090500c100702c42642e4680c015500c811880486031001c0c41085100000300e0801c92080c1031429 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 37176614 1250 37175364 37175371
    0x30207020f0108060f090f10050108040c03030804080f0304150c02030903061303020c030607080609061002060a05040309080a0303090605064c03020d1a030c01030203062103070605010909080301030803 88
    0x2050340c0e0160559401017484d00034287c64013110340d10142c003080347d02c006e0744414200030042464000c0480c18180c440e018004414007002e810840b1040014050000c460110303900c4c503c1d80c0b04525036a1400e400e200c1030200b5008071a075000c2c0e0030007207982c5040344000252250440c0c000c000e400c1e030b5200c840c41a85c108030030b142d003101940114000020542d9084c08082d200320b415031118038552610340c04100000e10010501e522a01d05115950540c55001030034540c40040c205c4002010707211402c00b9103038840b035903200c40b032075200b8088a1009c14ae490703007048002a06c83d0780c0521964460070100844c0c0301d40c0f00d0840100040c4240c40b1a0043c4110801720380c22000c096240c40d105400341d264945404110700000082a00056190030302001c1e0310030b05200070040d02000745440646400647c988003200000e5041540110120f1101c1d600c40c920b184178109000044088440502c82450301c0343c000c6401608c56600d02000010151702a0003621440c1c5e41c05900c4070f20f10303030035562001c100e1742014 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 37177864 1250 37176614 37176619
    0x9050d02040b0d03050a090806040305040b0a020c0303040801090203060c03040b0c0a170f06100309030504120c08010615140405090403030e010914100c030b1c030c170712030207020f010806 83
    0xd010040043d21244003a0308080c0c040d6841039600ca0b00e446004d46052003c0d801000300b94003072820000425401030075101518000c1080c9503651440400483c901056805980c1d80b50000250015080c0015030000f0791092003035083d1442940c400f40301008a010441d00078013103558010024600300361030b10082950030018100b44044200c00042d0381c2ca880000c80360881301e900e0b820244000d9103031200c0b105020352164602840390f005255401082030249200d00c202030381d4906949070800c030311400040d014120140081107642c0c0c0d103001401c180d582c80d0000e00003042048507081d8a021f510300481d02519401307400c0b00c505840395a403c40c004d04810741010b005540e9101c010002403801c00c035404400c2a200d006120000e98030900008840030342900d00c0c24540707401c80c0e80e00d2944a2690b10342034102d20301e400c0380c0e054481d8141515141040b500042c042902c0e041441e00384002e0f800a41039090048002c0500c4000c021010341c120310610b40040d40c04031000906900c10f40c801c21603180d204201 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 37179114 1250 37177864 37177871
    0x305090d08030103060902090c0306010c11120f01061a0c0a020603060d0203100603170a02070e09070b0a0201060303021c0c02090a06210212010504080301122310050703020a09050d0204 81
    0x1580c50303081c5590000e07002280c0030360311040d58206600e01002c503907070000c0748200000d21b50708106001a0007040c10702c60090860b0280c004025241c1e4403054008464034456094550300c201da19101d50080c80140552500b80380050b0440c2440e01d011429103c80625100040044502c107800300701443d0001424150310600c10409440103031410301c103107a42c540c00c51901241e00b50440c40c00520301722075103250f080d07142c13024441f406210707500048103400c0302c0610405940c81d07100c0138055814600d06411000c2801000a101c2103507650562005080f03034001d5080d10030355100900fa240855000607904400100704550078005450701d08109a0040030500740050b80558607445e4100c03d9407070b548a103803440440c03a804030075070400c582c0c5034900a030510000c1019107000d07592200d0901060040300300212000580c54204101ca00200000003412003021a51803603a850b0507585184000b0f071030400c1070904000c61a2940070307000f5120800c01d1600c030600464200f0041c45510411802c050b41e000f031b107 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 37180364 1250 37179114 37179139
    0x7060206071d12030c100506100804060f02071a0603014802070501140c0d050c0106080610091a06090f04060e0f06030607020d020a02060c0f070603021321030509 71
    0x341c00a41e19182a200f0000d152a9220188101c0c1016815045090000e00304010070920f5590b0b025200700041d0310341000322891b00c4606000c40105880e81001c40c075944002860014014030301105d4404c0850504260300366603d42d0141400c0c0c0318040c900c0c1003099a49902070b40c0380504521070324880c900000032160741103044540760295a099005e94405604000c0041c401d0b543d00c07034691041c004141ca15240f40600c141c45085c0e50384445179602c2d04200010510b000c0301d110039000400186a400f04861b481e080051666a1040e100d2044c160070b14074056a04003c42c6003000700c1d90400078000d003800d0500418500340011400d07250802540311303036151350106045203003840c140e00889041c280a5128a01f56083c103180000160052095501403d00440d003190300040503001d40380d0540d045920382180c444007914292103241c03090400c2c0a20800860010303410340c09000b1000480410001c0d0952303c80d8a2045506050098421820704c041c4247c04a4001c07070090101040103402c0350310403035 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 37181614 1250 37180364 37180369
    0x21f12050403031509060e01030305070305130b190e010804030807170901090606060512012105060f090c150306191a07060605040c051801021e010b100207060206071d 73
    0x3901164114046503558504081d0b6029810342c10300501a07018041240c00e06003584d02c05180310500c401807c0181c00114807040500c2441913401c0d00c0a2000d08590450b02d60b051068039403c02242c1030803021640c8406404030303108118141d8180d6043e1a0020a0380316914100e44030940100440c050100400c081c07141c603070b529860284100c0030700c00002010901407800106481103680401308010043c00ad41a00c900004822411280c101189030a030414404118012000164000d0b2007402154200502c50210f00700c01486051190152198185200200300141c920911104e46020303050001503a03c3c180101d000c0c400140c0707a040c0070500f9076228110500c0702d2000101e041c00c981c0c04284101040720b40d01450300542400c850030700880e88404801041401505c1944000b00340d15090800164028014003040100038521a0603403c81b44400c1400390813900c0949004800d104c2245c2203039407001c9101000d940140e8090440c07601e40e08001c8a603510729600c11442c54040d2640e030110356 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 37182864 1250 37181614 37181621
    0xa02160506040b060303070b0106110111030405030901110601060c0201050309010b030f03070516060507111914030609030408031c110a030f0b0301090c05040e0712060504050f0a021f12 81
    0x68800c0006003464600351510514444015100e28000d9006010300e50018048140c01b0f41925000d251400d012141c90800c00d0142403440d00b80a41502e000040c4414447e02100910039014280c0340c1240e194a0784040742c1d42d8600921901c400210140c210380e0056208038011034020201d40c0c00130074000e400e140040e08010f00303030035000c581e03910003d80141044000c2c800440001803000202005610303164015190f0b21546100614074141c052a400141e5980b00c022040030f80d0402d01c40310b0003502c03109200600100e15920500c6441444001034003194000101d03001e0718071900c007440c1446005480740d13a4a0008100700660507455202c07904403001d40402800f1540385a6402084c40306c0064120002c0b541e181d8140383c004d906081100f004920000c0d18017084642c10f403000141c40c2c1c0c21008280c244045a00100701d01e811501a20b010f004564000b14010340c020802d440c0340442000742d0a41d80c1d07910a0009402603416080ca2040c41c86070681000144201d081802c1060070f42107410044 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 37184114 1250 37182864 37182907
    0x80706020c032203030212160c0f18020708090409020d0812041208040203060c030901020412150b01180b0a03020403050a0302010f050601020c0303040306020901050408071805150d03080a02 83
    0x550003c222003498aa02c1080300d9244182c4080350503200303040d07450094442240e119aa1199280043c540300c4420701140450310040e00140c3e02550b05443d2450140039800c24800c2903004100341c00c8014044905200b1510301d0f41c4d0210340d451900412406000c00782c021007000b60b9201da900c0c1030134404104650003c0c0050120051071310003529140c034103c0004010a8403480c02c11a04c1000c010068400280319600038007500c03c619181e03501c500285019109541041c1410b6613140c00d00030401c6465081d00e1710700030420030140107640c0c052004481104404c0b4100f50b08040c120020000400214002e002c00303440c40c90058542030700c036254240f8180503450b0840050b9906c0303034100d4807a042d502c900380e0070500c01d2010700b40301c00c0b0320400a540d9018030301010381402d40c005804011a03001d0821280186002d1050700d2410307550b40319000ca11801d28150b240440d00b800c000900b400118040b40704030603002000010036500a440803500128001c010303104d019800c10000c0d0102d030740032f41d12001 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 37185364 1250 37184114 37184137
    0x15021c030203010501080f07021b0a090c05070c091401090b0102070f0b12090106050609011206080a23010c05040306050406060902041401020c120c12030702060f040509070e03030d0908070602 84
    0xd03070307514150005040d03010041c101c0e5200f071f44174414030901e55804204804007142c50444c26044d00308040000f0707030000132035201c450303a07528019548946a4000002d0484180514420f9040960318801340c416900e583c2810002c104901c0014405021164416892005e06104441c41c0301e4645506d80505400d503004608425030109400310028440c4007031030351260095009118031461700000c101a401400d4070681807002d015440403d10707a0a9000301e004040c2e1030101c45801c011814409110036202d280d0201c400d8030041c07048100b81050080320780009240da0b95a1500e89161170703080007840d01510442d203003078944d500001c41380c156002034400f81c0b03100c4d00040011070300711001901e02029808498000c0501b03a013a00e403000800700311004e5049040e52030600d00040e6101e06421072089c1e0100940c04000880c0310306240c581c0300c0141c01a22010750340d000440e1240003060f14031807410404264150f10401100108013201d811014815118191240c1811042e03580c94060340c011014840 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 37186614 1250 37185364 37185367
    0x1060806010b0913060810020706140a050717060d02010c031107030c1409131202070314060a0b03061603110405040914060609010e0a090206071a06130e030415021c0302 74
    0x3c10500e45000320300007a01d002c2d82c040100070301e0711115035110407c0c4136081c50841e034080b98403004c0c400d243d007208581c030b00e0100707650101d4507160036841c008000a80320307800054142c004006841c0c0c01118400e0045c0001000e030107000000d43d004440840d100e500440800c600c03844441c0c0441800c000760701c05144281605000c007420701120a90b461808000648500e6188043c4880601701c1000c003450150000e402003001c00000400341d02c1c0602c1580000c10591035411411040f5002186060040c0c0e002541030003410094010160b460340143d0743d0072030301e00811188030308950082d40016a0400d000400e2800c1c07650b56000a0111400090140d40080c9145802c0151590510a01da4881c0302251402c06c554140346000b0f40106006100a0070a95940004015541c660040c1d030307460303540640c24400305501c41c911482540d0341641d98a004980c2110b2204091405000d9820030480c008000e50900b8a0722641202081c4103010000c15401001d9419400b2002002c900c2034180d215100503 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 37187864 1250 37186614 37186627
    0x3040c030b041406090c06030a02070f02030304090f0b0405040506070c061b02030403050c032803021509010b040b09131106070c030507060e0a0b0307050901030b090106030c0e100206040f0501060806010b 89
    0x43c2d080c5403008200350025000b0003407a91107907480310180e0b034001c0141c007001611003003c4c3c1b8043e09121069680031b0340c10321000c1400101d05982d070b0001c0400b05d60281d070900001040e6000c0c00240d50046d035004200d9088140060800d80c8034032030030303008107001c1c00000c5044640500c4a265080c800015140146c000090500600408002c41856408160010440c62010320400a080f41c4007240c03098040c0b900c44440024140f0810000c0401d41243c440c0d000e16040405030b040c020f04007601903e02075801d08481003460316101400b60b110f10103e103500700184403541c0d2080c188000f00300140794070110030b22100300820426003228000d548200000c114043c2801e002802054859040f40e220340021765051024107504011340303421038020300302581c448040c540141d014101607025590458a46800050302541c513802078801b542081d2180e50016808070180000301544c0003545c0003680c80a004540086c2140b006104071600540c00080d1894a0b80542406d0a90031f80c0540c64401c40803659 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 37189114 1250 37187864 37187903
    0x2a0102070302190b0402090c0d0f1d0a020105030612071a03100e07050f0307020102090d12091a0414030f010504110a0b13090b0d142107030806040203040c030b04 71
    0xc0c4a03400c4a1010f098154849aa00c00180c120000c000a015079040c80104408030f45035820348414020601c0b01307201d080584d400690003415070341c501d081e50032552030420b03043c01004144406001d0301a901c4500c1d50303941106010b0307800c0c086c903d00e006c0b0b071054041c0064900021003e42c9601100050306a6a904180c031508403540c12540180c5070f240200014800c03459080411580c0040f40041e040d41c5030307a103078081030340240070f841d414a0b006401038941e0b404010b41301201000c82c0d111600c4100070162145189203220f0070825210704018000c120601c0181b1800c8100241d034039008085981810001f2002400e480041e607007114099803a54082e003940c5020101e01d0041e00301c0c960710700d04058101c103081403080c2251241c03901c1c50f03a96000c070320555101c410f0700408107900700c1c800400c0c00c800c403042140d40340e01c1e8040101081120003c034003501503505003140c0030150560740f80c000d15100c1030700300300c002d50016104480440c11381303a000001902c0340118610070b60103010003c15001007060f0 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 37190364 1250 37189114 37189123
    0x8120406050711190c1d07030507090609050607170d05010608010b09011d130606080604150e010603020310170d12060f061404081501030510020a0c082a0102070302 72
    0x2840070703c00318081105500c20f001a40200f041101c80403041910500d0910584d4042540c004e54040349051603101d414000105007240601943e513400c1045a039000011161200c01e8060030000418105040185181010240624134080d1900c6d141d0140307140b160030f075a64000c0b058a80b00c2500c0f0401041020f03044420fa03401000f011000a18224000c800280b0400040346240c00200c101d028101480d25a000d130740000101314171081002940710031014041c80030407a05540704a0801c1c0d2501008150102e0420440305041c4588402d84d003407032030550183d0401405091651000e1000041c40d204010180041616480241c01201d0f040040200b89485506583c3c000e1414604200503003510f0b00740180480f642031400c4180c5d10000302046410717205a42c00316800d031280750b81c0300f10002c401e10000350481e0700c500c084582103003201005500342e006c0c829520b40492030064203280822200c400030114948540305504212580010710b020080941e03502d0030303203a9070121b19941010740400 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 37191614 1250 37190364 37190371
    0xd0908010b091f0308180a0803041214030c0304091406010e03030d0b0409050f0f0d03052203020307020409030801170705060a0507020117010b1317100213030812040605 74
    0x280280854503241001c1081d990b0b02400742006502ca8910551a0b80c00e18244200035550241400356110071502e0040810340602241c0c0303121300200c69001034038103000021141129285405c0c202c007003d0a80b035a00c1c5540d0010030b04181e0b800308000c8841403040520040014003140d14000a88180e104118000f031100105960706012000d21409031503a8004161031007500d0b4ad002c0410f0381c1b1100740109002c0d003901080205280b02d1140c2043d0903110210b42c0c00c54400c0b0040c03c90300d00c142c200c1d40c1101924010f4a0340c413582c0e801c0d14042e01890103500c0d05407074014001c1c01100d180101c07a80c00305046a80c603075015000101c2401c010311014000b103421154449042000300b401500f0840001d6241c440c160040092104c00900c1e0011640030300f000d919442d980b50030b850300c00e60b03444801ca00b00d81d03c29003862520101d24240460344440c031164202c01311a10030024402c9840701804100207500480061402e02c092000010000d203a940040140c412400e00f188500e06003803810b031040e2140034 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 37192864 1250 37191614 37191629
    0x20702220212090d120b0a030b010b0d05060105070b010603110708070c0807060e06030105040203150a06030b100903110123041e06050306030303071206030f060203040b010e060a0b030a0f0c020d09 86
    0x40d613090b18481d500c00c1c0101017012892000040204060340000c0034203100e40e000074820350415000141c9115201c2c0540042880790300c060100d0b40d624001100c0d0341c402c40314007c1c10b11264000602265111360311600d0000307039680400b8070380000f94840c01006d402564046402018003001440440703024007409000f488581091242070b800c200c001003250105000d1140110303404000554100600c0089640000c8090b040154080d11b841c00100540b0104500c140144410f22030610020f10550316401101d800600c80401e0394078071001100c03a80400c450010050058000c00180c2003038006c001d200400111403d0312a2110854499480541d075512800500009000f000b141e928084203d07944181149400d04884450b94908001080795170030150407400c25010550070007100354000c0d4040c5002d02811882e580ea1512805842202112050b0300300e01031550070807c2c0c1d032007140039541060400001064050001201034122030600341104010703031050502060640e08901028090a100d = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 37194114 1250 37192864 37192873
    0x203040614090406050a06021614090a0203181b0a0e010303050a0503040302030c0304060305010302010314060f010f03020c0109050706080a0c0507120e0310060503010f020c060a02070222021209 85
    0x8000018207505012114400d0700140021142001d9031035a001001400008018030b410585403170340203565030703a89115540600c80200000c034400c0c0da08010204219002000040241d0301c0344080b1019410181465070f18203050b400c2503111110a10901d4900410350000350b070140c0100b003c0110711031040d480721034180d80200c01400440d901504803071088d021420229035940765890124035500c50703081d5540690202042c0422403651580106040703d0003681d0520098001c50b800300b0320201c090b0b42e003e600c09050b0f49036a8555001d0b41007180000c1c0307603050050500040c203a62170700b910f401200803101508624802d100c020b400108668001c40e01b00340800124059800181c40c030322031b246000d00315410550a80b00601d102d0400382c54a914060150350020170b02c07050440181045010386407295090001002c218056882a0b43c0c104048100620254544c041a04001d6005040503600078401c168291703a66400d6451401c0052203c0500503a26004400300300700304540030307040c070034241c02 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 37195364 1250 37194114 37194119
    0x170c041104050f060c01050106021e010c12051503011b0818060f0604021c06060908030a0509060705010608070b0307091403060a0c02010b040e0a02040c05040e040b0604020409020c03070c06020304 86
    0x9411050720181c48041d10009a400c0168001401500904401000640c240000894503c0c1d0205004120240264072141118a00c43c40c0034260f401035400d00e00058101e01d904d4264403007540006401860380c114200440480030301203402d540d1142e08200134004038505507541980d2000c50254800c3c02c108440c840f5030300b80c181043c0c9a090140c1016100c20403440481c074140d9403036048401a0b100c0e80c1450710703040b040c4100030000c4e0032240708203001309942080015600001108459204605649071403800b00c0620422640da004603606485a41d41e0b036001049551042102c2c80c05411040e86080e280d25011500409050a580001444403601c0d2030352601501c0019407143c00c010ba040001c41c0060700008224010880c00104540c8942001c0faa0341082d02c010a40c003659600959050012000c0180c05803001c0c46188100c1484960100c001008542c28018403174001c0001040980340c07580c1e0f104d10006030f0308409920462a0000610802080000d00d420030060215002071424240b = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 37196614 1250 37195364 37195391
    0xc0f010c080304080c150a0b010e040507020706050706060f06020a11030703021f1106100509010806070f14040e15090609010302100e031c1e030501030f140c0406170c04 74
    0x940001d03d024400304d1741c14003810040c0040c074003500030700f605860b00e0714042d42000b0103000304100c0740340410040c0d1203829090034280125449980d16400a0048500d08902103071254003000c0150340e110758032100424802400c0d00030310001c069030f900900402c0441e090400c0c044202c41ea000b846035011000800050301d0f4142c96002148014084840b40b4554400998000f803d640700b42c2014040d03a01040349020805000d0030a651040d21907065a80c0c88161030b07941c504041c1c2d0700c2e0700850f48003884050258411440000516029503601d4105640c0e1805802030b030006403581c050b40008500408030b41d09186803003c0d4810320407551409654515000f192464032a0064001084840102403100c1c2c0c0b010480e02c000340600020310040c035900c081c401051a0104905580540c120340205003103e442400740c0d9050f603400030302d841c1c008a49903440d04001800c070300603019180a03c110300059990b581c4110001000310040307041462003685002d1742050800c8108500c25840c140d5443d0200 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 37197864 1250 37196614 37196617
    0x50d09150306031208041506030303021905040f03080f0f03010e0711060411041a060f0309010b01080405190614090f061f0311030c0303030a0b01140a120506120a050c0f010c08 77
    0x44c001e801c011002d0344807821300b01c08541c040d64041100e9800c0482c00410507601d40c1c014a00c8014807038150105140008007140c451090b0721074913851031400981403001c034019000034003102c0d4540705030518003905a8410451174000340e20950306445000c0070013191607040703651f00421070340000c041c02c203519107070b070716034003044c030080c081a024a40d200035094030f007050741c8140004500d0042000d6229045070085044070b80c4121840000ea50810721048160350250780828000c1d03621038050110742112454440820180e0001551166240c4192030b4104440c0b9261a0062000202030310000100380c00447c03424802500340602d41c0230040c43d00ea070100c40301109078140c2c5d9200001d600d4841c1e01d5030000c1d1410007800841c0d43d04d4003000045c405007405035841801036820030388462140212011000e05a40200e004c0c00740810040030344103000748080d501442e40520000e0691903c0041090070501d0030400746170071603070359001d0300740c0c000e6610f404880f000d01c0b0f00c0d00340b80140c41c011036990740b480d66 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 37199114 1250 37197864 37197893
    0x22506020d18050402070b180109080d020a0504090509030c07170d050c070905190b040b01050306010e030f031c0b040204050a05150d05190b030115150c050d0915030603 74
    0x200080c02201c0740e214902c4601460061100820035525183c0500300026940415190080503080c1c0884040203540f043c05407501283c1c1000f281d90508c1008120f01001e544505188070800c04100804250116144207150150124000079912503100e60841841c2407100c2d00b003803800502c4400c103016100d1000403040c0303c91026142c15922a400e03034080514100340c82d04251740c1030741040e0130424002103007140c2c11711031a41d055052141e42d0000b400d010417200742108131400100100b00185540d4011500d400103c038000d41181d54804034808001e0464111019a84d0100c941521600c1d40044ca8007584081402c111411450249080300240e403c040c2d501c991400b40038014070341042c10900405a66a1a81d0340005002c03614009075031044d07080e8140001001d203843c06c4401016401d0510814074802c0940040709101c03403d0004801c99054000e4060042080705455140000d005010340041c00103240c031100d89541c140891b041c4890351040c1d01508060ec0d100c0c003000810440c1040b141c1 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 37200364 1250 37199114 37199117
    0x120b03070905010e092815020f0c07060f0206040209060d020307030605061206010506031803040b03070302070204050a02120f06040608100606080108060903030721091a06010306080a1401090c06022506020d 90
    0x40c44e1b038080c41c003148074030301c400e0035444150300c046000b04205c015032000388884ea00c40b07030a03121105d0712003105980000d5420391010041e8480e030002001810320a206540162004043c19680f018540c002440d1030400c0c5c00441e810350305c0e0020300203039040c0b452075003c5441c1800c018003059030400001c59000e0200511909010807044101c07603442c5024000c0f03e000d028a089603075074038984450b015020354031100c2c0490080345003800007800e0b054030f403090b100407440e40c44c04101c59031180c1800740d1358218050b00b89a841a03a441d00040d81c1c900406c80010f042ca010708001c20064130b4520007510361041640200242e4100f031081040d07a010100407a540078242d800c0101007130f0220500c56104050122124101c14030307100344403051014141418841249900b00d06e00280c0ea0040114240c59041c4128000e0ba0701200c0b0b024000341030740703003000841c0034100c0001418041688407101012a03075801200540c120f10650500e210616450400d58940c01071040122031400a00079941c000c00d160080 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 37201614 1250 37200364 37200433
    0x3060a0b01170412080a020405030a0314040801020412050105090d0c030503070c0c060201150b09010e1201090b010b070506010801020715090201020f01050a020a02010e070f0303120b03070905010e09 87
    0x864981c00740715030072100b00c100c80030704105141c5807508101c90780a40c3c0000c408140c2c2e030800501240340714004c55080c1c8034003501038003044c251590103540c1d00401d181d603015958024080440d00d68800d102620041c03036480418020064282000f9085460181c1300752421f4110b8689004d00d5500b040a81010a5140c5030480c0e5030754403000300311607000c1b10f6400141441e80072100051160342c15048040e40110f40070040c640030342e40e00040a8144541c00025000c10b20200781e4492619021140d100c083c1e0b4200700201700390080303541d98001c4902c01d821a82c03800d4000f1600e0300a10204000c2107004d080c0c0784008600c1c0c03400c552036009524000c01c19000005031184020b0045901c00d01c00c1a03100d503000070090085007000d055010282d003102001100541c680b0f4030141c190200050b0420455212580d40f290b0301e81962011103c0b802c007900c5c0c0010150322a0042c000f0b5840411400006000d03036840001c4d07550610110400d0244068a164480d512480da0840482580808201d000b1150000e0300c = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 37202864 1250 37201614 37201631
    0x4050108150a0608010207030f02150601020d050a090b0703021c020115030b1e0f0105040b0a030b0f090f0a0503030105040c1d0f0d05010e150702030a080106030902060c01020a09060306050f03060a 86
    0x501a1801380c00c444030b42d50000c10000e0070140c10101030500350249400742d900d0124440c0910207006d100b00c2d0752034010383c840030280d0300150280c4024107480712146441010251a960b000e1b150794402ca5045006038403020300f02e11021103021480a100e205840240f2580b05402c04020050a01c2c1c00060000c14804002c242c02c002d12585c0201946403120100002e03162003c401c3c61f1001c0c00b44541401a03092400c80722070392801c503c4942c141c0398001c000405544880d81d64180051004111011038810583d60000c02c0380e08000c4032100c1c500c14801550307258181018030060307403072074004441405181c40100600d0040840541c010f682d00382c8204048507403140000c0c20000b607401c4044e02c41c0d4640701c10b0031041d40000c00d0f4a042101c18008800e80c0b92150241213981c2c1c401c5500d1780000a01e00c4005000c2c540c820b8122940700c50004101070b0030700700c040410038220782c03140030100041440d050042024580600540000b00002c644c0d4074007030960302001c6511030078000d114440c410390b60541d6 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 37204114 1250 37202864 37202881
    0xc09080604060c05070b0f010f05040902010c060c0306050d05030d0c030e0c0d0813090501080c0d0b0403080606040f090209040f0c14090a0b04080a1b050a05060903120d09020f0405010815 82
    0x3a29412500304120a5107402d103050f07400c251f40301c207016581c842103104030081501e040901076040315a606a5400c0210403942e04d0f4100182a90884a0704058036142c00196075980c1a1403048050f01680c0030395640c0003441c0482d0200c5d61107250585c1818149a100e05070b6180c0440d09454010050714022040180c51400e08114420041030600340301c070240c80031590b0313201a80000e0695504604941403404048200700740c1c0030181c000201210741490001d070010b0311550340c181c2c0042c006480c140c1803d40b41d4403203641149580d040344864a6000c50000751620b03240c01510070101c01620200710000225000502021000b282404460b40019940000751501110600186210803903030380c03925142d0b00d8403034580c100b121045e18050b01c145092298002c0200540c0202e074001800c203e6410b280c10b09000c600e41101c00306903418040c0300d0a10710095801030041c82e441d160f00e13000140d081d80313138810459510b0605070428000c6240174010701245c400002d21309813041c1080145c10065466054 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 37205364 1250 37204114 37204117
    0x50d020c011e150e10050d060605030a030e010206100f140102030d06080102040602070b090604060804080c0a2114030606090616030315050405060d0311070905010305100c09080604060c05 82
    0xb024410b003001402c90342000034a920003910358200300c481c030769426510800c00c0d540c1c0c0c00546034181c4034101c0802c20400d07031604070101015944221400b03d000c59407440020700b070422014080c1d0101d11002050081c641e814800e00c0d40c0404019121400315041040001d800d407214050156003204000060056a008009881c044150154184550ba45075031115001c0d400611032180940302c2c1c41e00c0450911030410540b8004500580300710b08141c5040390444901e240908150790108040280c0742d0105000c0c016079590300d000c1c802d25104d82d0561450941c4d0b1040b00302900013003064440524440c3e6400e101140c0c0c11101c221002138554032207000281803032281c0c1050584021050a000c400c05d030701a00440241600c502100000c60f5651044c0410f4035003c5903040c0d071002c00c0b01d044000090007550301002d10840c0c0300845042ea5150032414040700d00070380054945501c07a5550614040e43d0340640d100640a500e09031103146c0ca01040240e4800019000601c9680c07505801c0003202d11800 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 37206614 1250 37205364 37205381
    0xd030209030705030a08041a030c0f09010c0206071b14030309190e090f010501050d0b1b16030206090d0203070b01170111040e040606090203160e0303390d050d020c01 73
    0x40644003268031700d1408850a5005100308001d00179940d240030040b03c1c181059900c101d0005c00e816241600281096025900140000d4180b0102000080158890a015007070340351248810720403680d0007601410b654400b035480366014600080e4000307030546010080e43c032075035026126512f14204904008554a6280c0c1001c0c01c040d080c8400c0011921002514002c401c16040007084140d0b00c81040c4860140240006005454a100822803c5a46000d11012040d0314418079040c01029a5842c1d803841d0702d10402d40059221005121950300103105810030591b141c0002e5103050510b83c0c030760389941c07014030035520b9130f0162540c0c00c807025400b9040b5a104107004003480e0340e01d0381c41c2c0490440a44050307a00b920380c07500c1c2c0f8902040d8084548200d0f07020f4030101d01401d11059880390215480780794550302c141c050100b8010501d410000801302903a01e843c681d22800c11507603017807068942800141c020301c03030342e803041400703255040e0080c0032241c680440301005691030410740039190241c06601d = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 37207864 1250 37206614 37206619
    0x15030c0f0738010303050306010c020406060c050105150d0201050309010f021b0c0102060f160c0b0c03010512060c04060806180114120c10051303080d02070c15020d030209030705 78
    0x280010410040c0003500d003000e01500b082c5a101c001c0d5605881803400a088011602030140300180046130199024550000301450030f500440d013140c0c007050030380c0e9480d4808404074160054071001c1010a016065002c0c100f001e0451148c2c50020000c0e00680542c4406418810300001003841817100b900450140d101c021029036441951140301d607603072010349121302224000c210305a20258400f082c09030107103c2c1850100102c0d120307408a211211030701102134040c001d5110000300010485020140300d814101d40c9540c480d0301d032106101e002d4071020907084284e044a0100500800c41000351000d4039107030701e0f250b80070390384000c04611110401e00c400d164100f000c80c00003909508a0140d400e0030407081c0c982480d106d2050000550b02d01ba106c480350350003411611780c003940718803804c00303000202da8a10185102c42da40f500c07019690750000e10740d000c466030001944418070603a0030b204002020050200e202c40d42000c200252581c2c0146072603001c1540008040d0421b9030100602c070040c1400 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 37209114 1250 37207864 37207867
    0x30d0c02011205010e01090c021c030c02030c100e01050105010c080a0806010306030b0a0b010f0207210204090c0b09100504230a080d020a0b070c020604060f02011103040317060f15030c0f 82
    0x110345c2c210501201c00d12500e0821420301c4203140d951407011070301400307110f86462480802c3d58008025400307800441a80c0046202c14400d902c000081089158503440b001c0c00d001914a05840a9500303403103058001d02d0600000c5403ca00c00500000102c92610025142c4021162180c0004801a0220b580003030301d10031404044c402c10015035401601c0c820026203032a420007088080a81c3c0355100c1d031040c52440180099411289036210301a060700d42d00c0200001100700b000d03501c09624603c06d8000ca124010b000ca03641009041148180e8002891403c01c142014a018400900d250039007818400c0d000068601a016480b034404007005401f1180c1503564141314100000d59581980c1425211540210003050030180a07000920009401400862405080c00010f0700d51049502012045643e1100b0603000244a40040c6000f984281e80b0325065458200716003065203c050101032040d0720000d01d112207a625000034485c038400401c2d01c60703225641c4022452a9000b40c1c0416801d0600 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 37210364 1250 37209114 37209119
    0x3060207030e0907080105030a02060304060906090b011505270a08030f0a0318020a030209090c1005030618060303041514030711070906083a0206070f050306030d0c0201120501 77
    0x2000b40300710648400a0710b50590640c2e8100084615000071702c01c00d905074000303500b07680150501000455006002d90004908510240d07501f0048810540064520614040040c001101d511031420110300a51501f142010465003030480720b00d810b580f1040480b07602c0e2007180e4a5441d01d6034000010468141a81d440d200b00003589042c9034003904d80a8000382c54440c46580c0c080c40484185640ea80190030b1180f46400c6500f40241c0c0540544150031a02c00c030340c0691807550f5003417440420104c443e51100c0d02e030b00b005000e116952159064001ca4141c0401c01c01070aa00c0000a443c03c0300d91084008038a040c003c40c007991040302d2009101000d47e400030030080029013000b00443c41001c1c030804ca40200740c1c0d600f445400c4802501400e02c4a400a100c1c0c00e115001c0481c05040420341c04014001d142c2d15003038a07041b00002c0c1c00341c0743c0158101408124480d900802ca8400152144c02c1052031450403100198031010003600e1241840742174640750096901c20b000d21810341007114403c01840d43c = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 37211614 1250 37210364 37210367
    0xd0203011d010605010c050a0308040224040302090c072001050708040f05030f1c05030a020c03070302010b010201151404050c041a070618030507020f1f09090b03030a090303080901060306020703 85
    0x100c071606410301c941c200203000445500c9031003590003030380d0042c0c00303402c49949503581111074503130141c81a64031611204d201e240d605142c031521074422045510342d03541e9914620500c8003624004210206040040c0040f0002c680080b20101104481c8040100c085401000588a501507020041c0c5900808140800c1c80952003210798150b17502281150a60011a00711603600c00744102c50425010502c0a40c08a9600500143d50000c0d0803040140c14009540740d594a141c000100950050307440d542d444c40c0658080c4a4003e0099040740c1560144d420542c8400d400d42103c64070a000701c0d52100052409442d00d01540d01502c42c2008000400c036010841d040e4070703000540252141864030f82450410311944c1c40060b06540d00d5101c9909020031602001100c0490031819600144042c030b000b0f40d07050701135810f150b4440d440c0d283ca0200c00e060141d120100c5001e0b00c0707118001e600c10429400301941010a40007182d503d031402000315074442c801746001d80801e6100070a590b0010842c0c00406 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 37212864 1250 37211614 37211651
    0xc0d150503070b04060210051e0408030f01050a1203050706060f0602060702160f050103090c08010f020c0f030301080613050c0d060204090f2c0c06030f07090b0c0d0c020d020301 78
    0x1a0380440032120b4040d19211114514411485404090b81c030509044e024021690007082d0300840c1c40e00300c1c009040d00c3c2c410312210310390210380884940f100042000940680001c90b00c2c00350100744e4a42c08001e007000340041c200c00000d1009000d2000118040f000c200c1070360031220150101c0a69590015a220000fa55588003580e220300940181d018549c01202e2454840044070300680d540741d00da5142400640041c80306030710a480c044c0002c000030900e94801d0003441951207003034000584c0c0380d00a40f8820f090614440e03034020560001c000400030101d000400e141c100c440c1340302c0b00c4031440a910341586000702c1c40b0211600624000c4159090110550280084a030b00100501913540010841c1007204c9581e82c4520741d5012808da128444c0005103902da200f08917800844070090711000000e041d54004494462212541c0b00401018a9205114200400da1240c61170304084130310807141e4907016a0780e100020454180e40364015540c804d1000041c542d0090300800415034004c1202040 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 37214114 1250 37212864 37212869
    0x6091103190209010e1002100e030901020c040504021311040306060b13050d0506071107050402041401090e07050304020607020f0d030e0406080d120f060f0e01051008040809090c0d15 80
    0xa0668010101160540c42d000300c51452070142c2d9501408100b00301080b40012160502c2c404622401030388032210b10403445629041300303031507004503102c0b50305c040020710340044088828000c0b03040400348001a1510200400ca0400c940c1012441e94510000110176019607440644418101080050f030800e211000300038030304040058400c11a282d10500080c0e04d1b400350700078119800f050004c0c114a124032641130703640c417a0703e054070380c620790b40d40c0018281d030895004840620b60044c0c8012066070040212801400c1c150090220741c03400b40170282c071074040100044c1c0281800605441150703122403011b064141c000b00011109003907400c0051031030020244550181e41b90440100d24a40c0009080d603094072199203155400790f000660b02d0107411000d0001d0b08480e2102d0002c030b2901005244600900b01482e414a0290724050030060860214030742c80b418000d104003448040742c0c060302102d50840e025100c1d10020703207812150301414410191a42d00c100d180c440085580e5004030780c0c0303a04 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 37215364 1250 37214114 37214131
    0x9150f06090a0c0f0c0201030e0706090e09010501180209010302040906090504060c2a0501090507121b050a05010c050a081c0e0f0c09040c1806050108070c05060c070606091103 77
    0xb0356400c010641151030803480100410f01407285401e072244545109008248103240c0480c01c0207210460700d1030146190405008a036200c8001d01c0b012901d507540552014407080240300d1940740c0b00f540c0b070002c00006a8410021340005514415901070b40494004214141d000c005065540a0003c02400181c500b15070b142c0c245200c3c912000e114001c00310801c8100c0d00f00310340e0030301d41303440300320303200c40c02690840d0309540350b5100310085003041c0900801001c8401e0400354a080d03174500400f001541c100e501c502042d200b00c09011544590a24500f07488081c2031001d028441c6040051030200c1c1d02c0c800070940b000c005840f030076011020100880000000c030050040790f0102c80c00b207844c1c0d000328510046580c42011024102d150101c6a16003090051200d42c0400d80c0301c400c2c0c6e241c0403a030301c40c003801c8480c0c5610042100396488014160300528601d04a0b242c040144d94264a0f41d0014006841320325001c43c009d818004113500400091203451810002e003040000724240d150001c0b9170080 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 37216614 1250 37215364 37215379
    0x5130905071101050105010e1905060f12130f060509010e0105010305010209011205010b090d020d0b071e0e0a0e090f0a0b010305010c0507050a020405070e040203180705030706120509150f06 83
    0x3840b1100500910b070585505031100b000d0030780d00106102001100801650411005940001c0c41d43c803200020300780d6032031045c040303aa0b41300c0e0400c9011010030007800410010a50445030300c08104c10302e2401104950061012655442e94648140074005c42040038803103528000000042150540c010034021000381c850704141141c004c040e8084907000d100d8202e00280401084505240144210008504c014160003580304692124039041900703d40a60121f00000c201d070103c08100e0126814880561615a192158010200303d005030148a02c03400381d00b81a0110748021018400103034420082c2080715080d84c5141488a070220007880160b4982d403814281c424060310540c01c482c1055000380c010414081305a0034000207110081c00b01041010400944001c1e581c0e0740019802641d03201802c1c9080b0310014245400c003842e940c0024465804103004120f040c0d040880708452003800340c80060b080d40c9082c405410001a540030300e07032185c3e20b01d0030449490480541310b405442c00740d0b90744 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 37217864 1250 37216614 37216637
    0x120705090903160609170412020a0504020f070b06030f0d05120f0106020304060e04021c0f0b090709060e0a030c06120f0b06031f030204020d0b03100603170304030513090507 76
    0x1c1e81c407403085480c01240303460307084119404100d00c0e400541c5400c1c843c8034098229402c0c0b00319401c840d00560001181012030361405004d5141000d610701c054541114214039050b5449800042ca10030080000d040300c52100006416035024400c03008250740c91000d50f140003c8101000308a940715286072401a109500850564088a0084e50684115400071494103041450544101b041003400300d42c081c0c4c007001462440e20141c23114403280030703c009000c01c1402814040c03405807800c0383c10450091205000304070540c1c0d400341d440c3c0300304d8441d0b00b48550b8600400000c10600340c3c45800103454000040000a01300703520110840006590000c2007080414290002081c0c03248000410380c000410b00102c1e40300180110492614200580c6c0030072240c0d582e5005c50b00b0b0340c10141d02c07044141c0e40c0d21083c1000382028043e43c080c01c00081e8080010341c2c2140c1c1c501d00744600c00070b24070012040c0480010209030003101200d40c0c9100010310f1030401070340c0700300344c5014020895040340050380e080d801c0c = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 37219114 1250 37217864 37217881
    0x80a0c0905070507030810050a0f031e020108150102120a080915060a060327052406030a03030506031002030a0902010e06180f040207060204082103040519020d0212070509 75
    0x20706029400643d2018035001e034a40f4115507814000e041c0d006d1421111600192940e1088896401440a40c909241075451030070075190011149904c203103a907801840c03110050303038054071980d80800c101502054030421500100d240c1a8483c20744040814001500200c254101d039220388100b003000c007150003030020754162100c80d050503211250040320100c01400402d02075080306644680180c65400300703a0240380303081c079104101c090540b89608086109072000e880144568554117402c01c9a04080c1002c00100741da400f0500009000c06980e500854082c1d6030512813200d210298031301c15900c071700f4030a82c000014283c001040f03010480901040d072050410400740d841100055110100040c62a8207020542c0d4048044d40e900c668208000c06c0000e10750320140014240d22001401400b20500c5c07005405040d800390b441c005581801080000340300028505214a0183e4860911105500c00b14034401501d0a00a5010401e42e851041c40003001401004a50b030032103090080f51258041d = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 37220364 1250 37219114 37219121
    0x705042a0f020c040207020d050d030e010c02010204030203150a0b06070b0a14070507060905070506040b1c0902060a050a050706021c15061b0203100c091401081003020118050a080a0c09 81
    0x10005a0440d8a0f0404940b80680c0039120240c00507041c1a034201860340c1e01403c2200320020311001c80d50f42c90310b07400c15041c02d115a0524040c03a000840c030341421a00000c0d41d840390b2240f00000042c2e1000014900403142d001030501d8040504410345031032aa00d0115007642e02118109a440d00d42000c7c0d4200d100003e11403070180900707440306450040c00b034664a01500104074180ca42d4450540d000501d900c81000400c020b11503004100d440301840c50340d51000d2441c2903103005256090401000140c0c0d185c038119a1800d5082c00c02540e51001c200b41038a8500038060041c000303500c0441e01d1007540329a4001603036580103083c020400381c0e001039024010f00c00c09008080c00241c070101e00b840d600d485508219081f50005044820200c02c0d50102c1094492001d0903400094030703100108404201d1010b503166102003400c0080c0d080c07803c10b00a4140042510001c0e0401012042600c4043c501e0304074000500b8020f032141001d952603000c07c607035405e50b40340c0c2141d1046624400041114882c0b0 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 37221614 1250 37220364 37220387
    0x50c0403151805120c120f03240406030804060e0d050c060901110607110d031103220f08181e04022a06070908010203070f050c0705042a 60
    0x8082203100d0400d0800304006004801c2d0b800559100c950a07400481d0003045062907098101103801c0d9503c07516007007142056007003000010031003800d002c0c940019070b9100c01e0740d600c03080e0030f1401900a4220005075a031610402d90054205144c60030100510030400300500940b8607a84a0015074100c0c5c3d8144a101c00451354060115005004c0860803807074044001e00d080c6070145000a441c1400846103800c4c02c800340c80050200350348103180135500d0705c24000c09880d0700c41401c1c104a00c8032035800c500c9035880020211200c034280500d00b2207142c803d401950740181d4000c81150703242c40551425007507a5004e0350340c02555800d00002080c0740d2070320301c0d145e040c03055410301040d058440510501010f504042660001c18045a00c0b88120404813420040d146100f080100740f41d05100501030004d81b1070307800520059004004110450b40c01849030000038041d45041c43c1d9071140306001030700341703001d64114980c007a0038101c0841c0350423906c20841000007100c4a055054024400d01030341c6949115 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 37222864 1250 37221614 37221623
    0x2011d03030402030c04020c0304090501081b0102150411010c0b0406060f2702071103030d0b0f0105070f030f02010609020c0313050f09041502090604030b070905030d17091c090306050c0403 83
    0xc0c84917030360034201500645040c150000c201c81c1400d8481102c2000d50388244c02103402a03118030319018074885800200340216030280007030840100c41030b03014482c2640040002c0d010041c60040d03070506912549107912600d0304200c00902030f09082c84c001003c0d100900c9030b01d44001ca0804003080800112440030402441849100345242c107581c0c0c0d540294014032410703183c0002d80e080007680c584080c8010f0600c01d200c12030000710a1800b0342000341d0710b030032001d0f000d04011045c00410000b0300d4504d4a100f208d40c1500741040c102442c440100d0152525802001107180040765000c1015800006003001c02802c2c0c541c521070544400500060100c906041e5602199803c08100450a00c070710052000d503000c04054070349030a01010440306d0b070041c2d20841c0d2441c80c44040066599009150034081c1000302d0203400c0c41c940c01c103002020f201200750354200300754035200800c1d90340300308000d41640b20700c00581c84940001d900360040d102c61107502c0150303022424000010091414501107409a0790300 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 37224114 1250 37222864 37222873
    0x1d010e19031d0604060203070605131109040f0c0602160b1201050d080904050709090b09070f120b0d080304140304061b0204090b0109021b0606030c010e0114030702011d0303040203 79
    0x1a03480442c1c0302500c1060050212022240400b903035107905005101421340c80c1c008540d01c0c200c0c1c0c50314a04451008092500240341156080006000d800070f0025014045500200c20b03102c60a003d10507034800e500007000103410000001e00d190300440c2003040030040d07140b6001d060790303642c8d85000180318100c100c0c0019621480140800d1070249940b4080500405159086c001040c0200d02121010340d451004100304200800c042403e900034102e07011002d6921188a042031400904080c0782c2c00200b101340820131210700300d00d0301554042c00740d00900030144640043e02c2d0504182560044d5001c0c0c1c0c0c070102503102ca0310100350000440d001c4692541c0c1d40d103151204003080d004c03000c808090483c1d00540b51000c94000c110f40c807140030b0107010788000c01680c0b09601039090200b4080c61080301421f4200100700541a500481c0c000154402820400d50360301000c4012603060340c0125010760620000300a01c455194158801d908800444410402d03022440b1a0150380c0d01080b01c00030f40c194003 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 37225364 1250 37224114 37224163
    0x50301050f1303090801020a030605120102160201030b0d022106160c0206030c040b030f010609060309030206010b0c0f070303020f06010e01050616050c0a060302071a04020d060207151d010e 83
    0x400c00001c614002e113071065819894540042c2680d10100c2c20b500020744544040c001303890200e508440b00034161008602d424410420a004d2030b40e4410080d05042da2442c03e074000780c4444208901d403039401002c20007102022403100080c0249002505580e100e00320000d114074070142e08102c0b0400340c0d5254104c10308407540c20071400ba17000400303d690b02d95083c880015141d1081024600030541c00045441c60340c100300000346040d869a0101c81018106880500440d40204400781951801c1400d1a620045c01e0941450154034004202580c402c4c010004241507020901c030702242c600c1020b5603141e90340c4035050840c1140170701035213030701000400980c800810b87c1074010900d40d11400941c0c00c0c100e4804005209500150300100c086500003d103041045508030049000e5520200e4204041c1403640200d5441e1250a20080001d5800140407050060140d401c2c8060301700c042e4140203049241100c20458000303c6a402625824800384200509010031401003540490028060010 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 37226614 1250 37225364 37225381
    0x3191101050705130e09010f020703260c0a0c050c030609100501050a050a0603050402030106030c06091a0a050906070501060f03030504090c030c121d0d0305180705010215091504050105060a050301050f 88
    0x40160100c141d80d9a122a00c99180031980003400d850f90080c4c463344410404404010210781d482c040b0724507503600020800c081d031840d000aa4510864078074004118800d1072400d10701d0083c0340903403a0791500c200010030001c140c00254001184806040034481030360380b042400140c1810b405a240d02444000c414844a44241d0100b50301500003000880d240c0d9880e1549064070310550001000600950340a103e00c2c86510080740c0407840e0700040038035103021030400900340e01666050500c52640041c5200600c00250808005800e03040c07060b40c40c4d40d0380c0345400761003640580b08120520b03007130007003a100c154000c0c820042084201d0721038030b61200110f144d0500030140840d6143c0141542a2012001001041070301d59400780d0392000180380c04d00c180c1410f0a071500d8004031500d54441c100c18000c1b40d07808100f0301c50094000301030f581580c888810050502841400840360910800100424418150040c038003400040d2517403203003203844905240c04d0341e038200c913010050941c0101041d00074 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 37227864 1250 37226614 37226639
    0x1051c1a04030e090f0108160819020d05060901090c090b030c06030c070b0c0c0129091509040510180215160b2a0306090403110319110105070513 64
    0x40e01c030f868203003681c00400300050b4402c1e1007074034202c061624400041c080d15400708510001c0d00f1240c4e03103141e2501c6c500b1055035654140e1941d608102171031011000304644640e28000b5a06501000365403041c600009031382d00134928114151084050604009010071030741c0315030002c154002d00034081c1c169072003040c480547c2c40900800404401000002d003c44e14060b0400c4c0100c00c00e12032540d49120071010a408d41e1900d418283c8c900600c0c40e03d0880e000c0c50901d149404041c140c415440300e03904c0ba14640c00401a10000c10341041542003000200308000c103910b1503001c40030004010106000c0c3c0c04504c0700480c14002500640c001840c824200c0c0b9480c043c185c0440994030403420069180d817680b29510064906500c4410f8804244045a862840005000e0050064941540380240000310b0012002e4005403d200003c1a61001601c0510883c1d10114884600d501c0d40d90400300004c0c00211880340101d10781d440c083c0030400c00ea204004850642a401c41000441d6090841c0094107 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 37229114 1250 37227864 37227871
    0x801060804051c0e03250e010e0a090204090204060312080a020c07050f060409060e150108040b0604050a09020619020f0a0203071802040f031a06010309020a17030f040e01051c1a 78
    0xb4094513280b41c100658040201904280030b140241460102e80781690340804c2c51508090000f4104070014800c40905640700e03640f040d080389003c103c40f400350020800810b00f001d4041e42050400740c02200f0312012036082400d03a072503627490401d182d4890b002ca504902910104203400c0e0881c0c40d0410117072030404c0c411400301d0001082c00d45030941c0c0c0c2c12100308a90300355011003001020700c1c0800600c0c1c00b04c060f400c0a560002c0c200440d107442c0540d41c2e5014224020000f0744119542c2d0701045248503141c3c02060303003035030140c411030381d90022824400c5250721281040c00140f01c0d08602d084030110201c0c0002c0c3c102e074090014640141440646001c06120240e101711a0790309200004020b400c1c2e6014074000e5020b61500c1100625191103c99821030081c40c0c0307414503007040a40b40041e11185010307070885000100002d00c2c0707010f84146d10302b944603221400c500f040011401203120703402007407214101d400868040e2001003150740019680700c11904085e1400e480fa1303841044c00b109070303650f1590 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 37230220 1106 37229114 37229117
    0x7060503040309030b1330030e060a0e1c09060e0402090d11040b0d1b0806100e0709030f060c031802032d0604050606010801060804051c 60
    0x1a448044c44001c1400f003c2d00000344910700d000c280701c0c9545500c060001003201d400d0f0004400612070b0340400032004060381c911f00ca46401780c82000350301e1060001a24071981c1c0e031a1814010031000047e40c0e00d6003c1c8080b00103409403c000100b08580c802c0c5c680c0d500b054104940100071242000720305014510400c40780d00719a50b1510310440d1160300800a100c01031116002c0782c05030801c14121600503121090000c10050040c400422110f65400309500440c3d07900e0720990f503414241d030340c0700c01d00f515940d00f0310140c8038031302d1544c0c0c1c02291810702e038010315500e030f1303e412003040828415a00d5541e21007e444186d60305004591a03241042001d0882d06042d80010752103610185604603810348480f8007951604e0024100c504014410341a01c50034546818400e80791b00084581c2070020304004c0000c104107000b100001c3c000c94000d4002c0054482028900300d00841c001d040301c0 = true := by decide +kernel

theorem cover : BRFrame.Cov 37050364 37230220 := by
  have h0 := BRFrame.cov_init 37050364
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37050364 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37050364 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37050364 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37050364 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37050364 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37050364 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37050364 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37050364 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37050364 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37050364 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37050364 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37050364 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37050364 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37050364 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37050364 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37050364 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37050364 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37050364 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37050364 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37050364 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37050364 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37050364 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37050364 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37050364 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37050364 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37050364 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37050364 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37050364 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37050364 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37050364 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37050364 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37050364 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37050364 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37050364 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37050364 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37050364 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37050364 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37050364 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37050364 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37050364 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37050364 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37050364 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37050364 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37050364 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37050364 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37050364 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37050364 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37050364 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37050364 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37050364 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37050364 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37050364 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37050364 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37050364 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37050364 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37050364 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37050364 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37050364 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37050364 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37050364 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37050364 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37050364 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37050364 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37050364 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37050364 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37050364 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37050364 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37050364 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37050364 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37050364 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37050364 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37050364 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37050364 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37050364 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37050364 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37050364 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37050364 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37050364 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37050364 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37050364 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37050364 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37050364 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37050364 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37050364 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37050364 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37050364 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37050364 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37050364 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37050364 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37050364 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37050364 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37050364 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37050364 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37050364 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37050364 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37050364 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37050364 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37050364 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37050364 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37050364 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37050364 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37050364 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37050364 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37050364 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37050364 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37050364 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37050364 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37050364 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37050364 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37050364 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37050364 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37050364 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37050364 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37050364 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37050364 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37050364 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37050364 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37050364 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37050364 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37050364 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37050364 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37050364 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37050364 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37050364 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37050364 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37050364 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37050364 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37050364 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37050364 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37050364 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37050364 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37050364 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37050364 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37050364 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37050364 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37050364 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37050364 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37050364 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37050364 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37050364 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37050364 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37050364 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37050364 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37050364 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 37050364 ≤ n) (h2 : n < 37230220) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
