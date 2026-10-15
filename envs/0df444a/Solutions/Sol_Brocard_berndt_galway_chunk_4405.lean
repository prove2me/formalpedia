-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4405
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T12:30:25.346828+00:00
-- url     : https://prove2.me/submissions/c30bb216-e8d5-4113-9130-3603faf4d128

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 792086330 ≤ n < 792266187 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 792087580 1250 792086330 792086333
    0xb1e01121a040b0f040c021e060903040303051804050a02041502062e0f2405090d1115130f0806130b07090302130f06090209030a0206031519050306100e04 68
    0x340003202403d580a206002082c44136101c0d0f100c0e084000c41e50b9405401454141551611644011800f82000b58002001c000c21090048240c2d0242c0c0e038140750540c1da8441001120640d40540151541d009107003806101c070341d50295000b0822a82c0300440740121420707400303041c5d0301c69404a4905211120704049200014808030907089509109042605034644070780c000e101e104242d42104002e07922424907052084051961480501d125140c280c0c5082c10300b00c0410307011024810014044d401d0304040103800d035113a0745252100c10125240c5a200c41030703c04484c005084521948a84440e510004913000a01250b664814040e4440d0526a6402d55407058080c000051104040040100001c40140e51b07900c2408060450442c022031100c000c000d80d07108032038165105428092040000f0080c548020521040c040e03011204607807a5514020010103041c44d0780c0d6426844500b00f003550142c030050f040c0c400140c50095044a000b0340d15a800e5000000c1d02d40108051640071000080 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 792088830 1250 792087580 792087589
    0x204051c022101090203100614130204080f151605040e0406110309100b1009090e030915040303030b06070f02060c0f060106030902190e1303030b1e01121a 68
    0x40025101070a450368020b81c40710000c0820386501000b02c55a51241e068400f0f510b07081100390030360049000c0401c0b6041c0b6100c01a10301b442011501c5000e5421000e9000d070f4000250b05450082440e00705030340700c030246407800310b465030400f2900745000c02c00079020440e070b11401c7c0211145800036440e050701d080c1c00c02d41158407408000340104c824946480c02d44c0c140220741009036001d032070040000d011105c0c3c000c4451040e1520300072480c8c0166a44c85600f2089036008802104a0340b81100010701c158600d00e00c0c50451050741c0c0d00075085813072100040c400c44d03103031401402142e000e0f1350108904002e010400c1941c1c4501c0a01070400c00d1420002c402528005008102603244101120801075410708000e007400400d80c00040440e40d80c54aa80550030402088016a15409003004945041c40d40c034210502004d802c0c00650041d060319002054001d40c000640707204011301d002140691002c1a50b00940d40c0c1d0f6420b030015510551101c10b2480324000d514820f00100805e0110b21011003d10 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 792090080 1250 792088830 792088879
    0x21503011a0d020f1206100c050c0609010e100f08090a0224070c03060c0e040b0306011a0c0312160e010806100507140715050c060601051e0d05070f03020405 69
    0x142d0740c990811949041c200420b0042c50302400d809134084191070b001c000c010030586010003010a0240201d41d040014602142d1120264000c446aa440f001c0345401212102d01e080851a00000084003841c2c040344c20070061100306180e6950b800715691b0369140e81d51517503000f43c8000d4202c030f0024264680a400710071600d1700ea40200d5591030400010740ca80300c01c80a115030041d901c181c0d59003810420305502079184a005102070b0390902048a007040460350360081407154901c60788030300401e14a1074401108842040d040780048a4070b510740c4003080c00c480c120903200c014141d0344124011804a0046002e00c0e803844050b103803d0800c0c0c0d100f9003400806015007040d034041110804c10400040c02410032486e000c00480000c000c00b504102211810b000ca11aa12060000501c0080019100040c0c2641e00c00420320b403440c1c0380c5602c1d0320b600280201c0c0f408048006100450940c0d00400941d00c4a84246c0342c580d0f80750261068401c05600b248154040d40340c00030310081040507281e114030300303e = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 792091330 1250 792090080 792090097
    0x10308030a290306012102040b010519030e0105061002030307031e0908120c0f0a03020d0b06070b040c15090e090a0506280b010c0308040201170c07021503011a 70
    0x8540401154024021821001c0c03032800d8900d00754041d0351003420f04002050142c41010140c0408010512000c8442c00d0300c0c81000784583c0e1501c0c89248607900c11002d40305112448403141c904101d1601026003d030580543c0b0018070f62800c6e000520914054070001040c2002e0b4014510315102d00030214040d0422030341320090f2107041026805500399911900e500c6a00425203103480c5d01d5600800001e02a02800e10f004c130a0090080c00d10900140301101c0d8141d86c1030038010381e40d0095000b56001303031020300e907026404840460002c06020f2440291407040c1c2c0301c0c8142d41c0d6880e841d5458510303405a0103d03d0350020368424428071604803119082034002c100d130001c46192a030700382d989526088040302c0c0c0109488810b04a050039030940f9829402c40b0181802c18400f12001c0b000003050303200c0c41c42d405401c000c251740105055900075820720448100c005000200e07454020300041c20b0fa444140124064000964080b460030712141c06d0340d051310f80349841080b00202c030090070302050308403028 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 792092580 1250 792091330 792091351
    0x18060402060a0c05160605070308060a05031905120f2a0304090b030a0212030a0815011b06022109241b0f030f04060c0c02010f08091515041b0801030803 67
    0x108284a205c000c50001340308541d02c0a81d140c090307103002404410041c180390b0041002d41024846540c000c01c0084108102e0113106020004c6801e00501c0e042d00c4d40008019050009100070141e21904024080b1b04098003600c100d03c00c09880c462080b000440000000d0b81040c4400d000300301107500844200d00c3c005080362052001070300001c904030396200c40003865610000d110100c032600911601d610190102c18040b80144540c00a090360350342c2d140169215581e00c901e0001c0002d2541a502020080c07401c2c030310f0101c10640b00003581007056032042c1d024400d401c1c0c80c0d500203400196808a07060000c0182c2c400c3c0d1682103e042c80a0842154503460b140103100c111180680800914450b5071001c02d9040181840e0070020b08071524110354130304200c03ca42500c130161f6089001030700c04138828a4071565550700c0c01c40711400d003000f030000c05801501d00c00610070700080e041e04d4100c42c480d00300e40c1080000040c0da0742002c1203041080341c10104000600404c085001c2030050f6911001404 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 792093830 1250 792092580 792092593
    0xf0603090a0b1e0f0705070602090a0305031918051e030f1005040c060c0809210304062312160309020904050f060901021804092918060402060a0c05 65
    0x40c2c4041500104503086200e103420310110106640320764811540213484481031403818185240d00a1252160707403006010302d83c000a01d0103003a01c816a41400454110095a845404001e580c21825209008500000d0350b100c24541c80051207601c0c0c1011140001c1000612400e40005c04040840360003805505015050604491304030600440440f10203030200080c1910b498230b07103442405d1594020104002d0304043c80300009001c181165074120085940c480303200c40d080c82442600030b0383c50f600c407031a00011400247e00da40001c660400035060070b021903546141030200c4066405140f954000d81022803001c6405c0d01c03582100c100001c0403502c0c021400810799000315000c3c0c507060301c2c22111b40d4840884012800018012660042d200c3d070000d5140603456008903250b00280c180d074074802c81e615582201048880602e00116920201380c4c03003261020801c1c0704010510840e880b0b00000301000040c40341c1c1c00046030b03044c40382c2d5000388498200105407000b1515560807010460f058030504 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 792095080 1250 792093830 792093833
    0x30605010c171201150305151c051c090e0114010509091503070b0d15081b0a03050d05070201270608130b090f0c01030e03040b0a120c030b1008060f0603090a 69
    0x115450103070015886404024011401c01811240028544100910410096a215524003120340b01031032940707448100049c040e00b4610704003240304031800b90319481d0040824102c0c0d0840c1c0301e0412100710710038400307041e07903143c0c01c101d694006d14016500041041103101d68070b181000a25402114003080c860320017403000b000c24502310041d04504004000070440400400b07a90081c5510240680000c4603064501007480da0303100f03980b070106125002075025004540d1240e5008070029900282154910343c2c08440c0507040d580f0962007a80091001d501081c65501d20f50000c0300b08408170001010000d1400030200d5503054050845e90303002c120300c04c41c0070200d040084010301885c1c1550107000301480c03900b8050325228907400311506040c14181380103550301021054800300c0300114001c650703459a2041c2105d2001d030251110360100c0c40c04101c8151260f055102c4207004000743e4040145152540090320700110840345141d008007403188509031420600050354021641c0d404030340096945 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 792096330 1250 792095080 792095107
    0x40b1b0a080403051501060318021c0204020d05160c0c050415170105060f040e070b09030307021203040513050f160212040314100504030c08210c0304050d030605010c17 74
    0x7503000b03403003507480001140d60058550170018010885410100215621448000e00304034481c2c4000e0b200c1c0e010700c0c150324921015160900001940140b08540d2500061580002003005503000380300042c50181300c014060241c2e89402481303810441c9801152314050070000a01004034555211800c081070004500b2000e130b20308040c1800c2c6400104d0b141ca010010b000c00c101d80034041078032841c103250703d00150032070205841090310030003020550790341000000700c0d02d14418610020b412810b076080d0601107650100140c41529411191750aa034031100340101c065603000c1d104803691600c0640410152644000d03040f201e4007041c01a100860200c1f403a40d21141c10a0740192140b03081d031203071292600b00c00e02c0410104c641c920420082f6041580b0010401542e000d4010510800010b1240440f01000c0721001c0481601a1b00c4819113001d086151131038005441c00c40786840740c4501c0740b440d14001d0040d0400d44e14103a41e11005180241c0700c280d03d14254508000c525038040080c140078401 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 792097580 1250 792096330 792096337
    0x60603030e0310180204090206130305030d0506040506011d040e0105090c031c050304030809070302090a1413030e04020a0e03010e03090a0b09090a110d0c180803040b1b0a08 76
    0x41d0710360006010000c8107041c00c00c080d400e00559054a4640c0c0c8000c150000b6074070300051601070b10000b69a4403288089100d91142560079061030f10b001e07400000708a000001007c032200b20503810b0103651540c1042c403050755010b440d000c4c0456a04050000420411241c2c0710500b42c0003040031942400030405e640c03c480c0151070392142074010250990a500301008600c00e003a051104140c9580d081c080300a0007404054001030410140c0c1011a500000030424070026540060520388142001d414031401810490b0710f607001d60a264000846d804844031810030744c0744d095210345030751600001c100320082d030003d040d007000d2060b02d86c904c0420740c8091050141070007030440216075415080c0204840d0007615031000d04c0c1c1da1420003000203151145040d40da041a00c81b00041006844d80080725414042d0008118541c1e01d003100181c4660391000c1581d5050f103c810818504a41310b50041c1d817244681d00519403110010040340c042460000020000c0c411070740c080d241840c01c80e55a0504a50 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 792098830 1250 792097580 792097583
    0x507060f2c0601030c05040b0102121305010905030606010c06050a1d0609070b1c09020406080a1506050d0b0f250305090d050a170604110f0717090109170a060603 71
    0x507909001140509000046440208100c001040b0a61459803680d0b40620540039180c0601d40b5480c2c410710036402000200014007107200e40c6510340d180201c3c01e12907503d151180a000501002c00014142000300b83c8500502041e5a00100b0812546a20020300380141500c80601d0341c0b407400640e000c2810440c5800700c0c001c1c4001d46080c1c1405028245400442c0d003140c07070340c2c580c100006000c0d522a124000381c1c400c680c513004240980302d40005401004168000d030014002c82c40b04808106078202004041c801042c000c00241d0b0700c030001d02c4505014150000c000180c284041001c600c5400c0c1450381c000a100e1040602c282c00d02c80d00021810041c02d035002103130f102c901340203801005001c0c0c010740d81014034000381024041840100075503040349030480b400c840040490038a44440e006215040b0a5210300c2d5a99070154603802126409120292402c101c04010084114600012903940d41c00503912040400d0520002c00e80407020f0001d10070706442800d00c0d190016019008000096 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 792100080 1250 792098830 792098861
    0x1302f0303040b04031101030501061b171c151a09040225030e010c0308071d0603070e03160e040b0a020405090a060e0907080d0f0302040302060409061a190507060f 72
    0x254070b546040b5400841081440d1f05060401006000c219030140050b201546a504c840b08540128140000f58080d564616070b152840000d4581d1910581c0b1418024a118050300304400759000d543d1100140160186810000c5e950503c4000600c06030050650807400400040ca4820701d6074403004144110340703030342d050071900362107400c20b05800250514900000b0300301440d04120a50f801441d10200030002c400b440170b40f594407050882440483c8035003040107407110b6940e042c003080140c1156006074a4910921480c1011b164031b4044503d480100c030007959081c03603d521695210100d00100420400ca441d03801d1100040c00c1d43c8030400203016000d04100002c1c50381c204419195100c00007800034800f540032220410a41e000007421074001070061501506e0401141c0044000c0d21841d40081d40c0804c020038041050803050b071240e0202c45203c140000e0224610b00050301501600d143c80b0305485041c003034070b80201d000d080240396061052a0001c1e030389502400070422602c1005111100 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 792101330 1250 792100080 792100087
    0x9050702010b091e01091107060527011515050d0207080403020901050f0f011b140d0f020a08091c0f06050601020705030114011406090901302f0303040b 67
    0x22420903500c0c8503000303924040c458001e045100c4c6446048032061042c8030740c003035444c04096020108081943d94060707100c4800d00460414807425400855520140d07060b40400da0b010001c8980144948220f400107210780e00d01e40c41c0b802e40048004501020318400b480401c01c4016560301c210710003004600e20660540352101d0031401408031150f01600000c0c001c0785035101c2140c0d03990720b40680d0f001c00542480c18615000100c1d19140c03402800030001002d0f82030021019480e6035010030034130340251065440100700c00c0c0c16032080360b5442002c080505141010010041141004030300a660404403415001040285903078a030501086140240e40e090354403400c0c8143c4d90703414802200104021002071203d454000ba140c081e0740010310a40c0c001ca030360281d003075403181c807500143c2d82c109000501410b8650381d6440c2d502d45811500d23407a04410507000740c45900c141650004200c4494024003003000c40762800700032038541c2282107003002d0440e00b11a010350b910341d41040103002519250007403684 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 792102580 1250 792101330 792101351
    0x11060c0601290307212903010b04110d0c0e0604030305031e070e040c0509011b2612061801031b08030a090501020c0603130b150307030f0209090d020303010b070c0905070201 76
    0x20480f9900c5d100006500382609241c405010590070a240351542e41480703800c07081c904c0002d0042c05803c1e0896040303400c06503669500d64080c006890100640c1c0003d0205018807041110f24130008100158000b000340400e10100b4810005990f0140d0104d15138540301605514040100b04120340d81000241c1c2116400040c0c2030074001d8112928050a081c4e0070b1001100018018602215245540410090350344041c0140e070700700c41c40c4007d1044491003503001f01440100c01070740b000c0300d40f1080c0c07080c403000300f00103051400444142d000d01640c416116400d40da6184c0c99404107803a0320040d10480c0e42c010a1000092004240c000a41d072541c280c0c0318174101c00a814100301c421010301c105018000c11a00000c0e8600314915564800109089036a60080c1401515040d4840e6601441011404001c0011141d90010305074021100702e0150380d83d0f007031216907034480e0581000058000748010005800d01d00054402c2034030030b00000911a840c0d1802e00c1c11940d0882d01540140e441c2c007241314 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 792103830 1250 792102580 792102617
    0x12031e010b1b010b030c2e17070c0819021e0304060905010c2006071b030b0108010203070906110c041406040e0f0613060b03060702070311060c0601290307 68
    0x88061019800a2042001361400030f034070f503642c54080034083d030003440045100d961611800a8207060484692201343c10a88005101040d50b915141d40d09a5580200d4239180c040e864030400c103603120301c0161401c0c51120b425018545e01c0d003807003025485050b06e96100c0c2514020400311032040000110340307562030700c50000d1450521b40d200c0b0341407204059452000c00c140c0100101807008030080421001d40ca840840c0c840c0c45059406040000803c190030030f200c1c1c0303a51642040324043c220f41059a604c46140900301c0c402551340300c0100300b10780b008000701400380780700c0c07254001401c007502d0364101c0702c2012070f05a40170705512801200d007500400105142c01c0c400d100b580340402005248000c80160120344d40c40019054080600c031001500c41000581e8002d2200c460000d42924510b041c17001001e503842c000381c001124043d078640c02019850401d003069418108090008100300e03440c3c80b43d0300c491b072400551a10074004040c10040700307803060380f07000398040c4c240c603030383c1a1000904c100c201 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 792105080 1250 792103830 792103867
    0x8070b090c1e06091512040c090606030c051206060d0e0a0b0f0412050903070b0703051801081302040915050412020f060f061002010b131d010e12031e010b 68
    0x1a00b003900d420070702d110241c5401003941d08101c020356548020102000c041d1000340144448081110801e1040000300304e0300a03c00d50440b81080c20034014503449080c19000d07115094201c40000b4421300190354aa4902c89096070450b90140140345081c5144a14809652003c1c1c8540c03604d510101c2d880007080704c02600c00c0e0340f010a890201020341001e683d820790350410b0b01401d03c104a8041484502958203001003001030020081466460364a403a019100b80c200d00000307a50030182e40103140441d40035070f2200e07114190318450000c0317650741c3d0703800c10009100845060b1000410304024140c10320f0703540b0940740628003a4a11070412017032124000d1801c42115551249500441c00303000041d407640c001c181d00024111000304511604801c103e0050040d011825844516914880c074408056804226080040c4441400b002010b8614609a03411041806401d500c10340c2e00007202131400f0080c68210540c11000d400528800f00030300003046081c0c10600c81140d001039100822110130022 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 792106330 1250 792105080 792105109
    0x1506280801020d151a19020f0307030903060b040504020f060a0c06090b060a0603020a0c0210020c04050c0307090807230d0602070b15041802130e071503110708070201030908070b090c 80
    0x3102000703800701741904054040c031a05060043d500324901d0254a00901c8110030061400d0102c0780c9a07180760600400601c0c0900c405c0c0d0b011490b11007003003000d0074036000b550700c21074014001c0880d4208000a0000030381c0404d04000c10000c0e00f4480390001400d900400e0540c81c0141640c4c04541000001c01c1004000355114009161041100030340c1150030028504005030102c0b06e0f03190503038000100f82c4c145520750103025800b0f4905010481e2000034200a54058602d41da541402c0e10f0b22284035a40e05c07107840c0100031752071400e55080302100c0d42c00000722074403201c0079101d002c406005a4404017070b60440481100c05140301c004001515200c484c050903251006c807010f0244005d18107940c881ca080300000a40a10043d210040c4400030740c0c0c01030303440c2d00d040c40b0403503042a586521000070000e0320030224000030705020488400c00400d006640c0340f80d0300400d40c03a190049590043d4018203500c04c04440c2c07080c09000410215806245e110b00c144450406800c3d0081c2120801c462000c20784007 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 792107580 1250 792106330 792106349
    0x140105030714220507081b0a08160905150304050c01082a09032b080115030902010e06040909111009090b0301090506040f051506280801020d15 63
    0x10000600b402041100b400026110240074502150802d61100f50211840030420704001c01c0c48030349a40100101c1c46401c0c60300449980744503070200c0c2030942c0b15030400f000000719141c0c01b144840045012058502a940c01c10390141c0e41d407040414070302d5914a00e081c1000310080f0400c03043c02010f2080203500c04091a145d1401e28005a1000d41020400c500492111080d21204c040440807021a02240360040032070340108084004014060406d02080309210079020f8000364803801010403506880c0905061103200711171003000c40007001030200c02c1e810840c90304118409038076207100074000b400403c1000314244074541003405401503144c458900601d40008450086607101d0004420350b4611400802c0340005000081c2c0905204ca03005002402018140070801c000c0050513155907101303505880400003d186007105407a4100c070116000001c1b01043c5514060104c000802065806814801030703448070404d80c2240c11000001042030b85c1e40420300d941000418103c4000c2c0200071 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 792108830 1250 792107580 792107593
    0x3060a051c3f090302130b01020c06070b0103030c0c090203011d060d0b0106050f0c030301080f1606020d0c02061b010b0f0a120f050a050616030c2d09050603010914010503 75
    0x1e240301070790002a203040c1d045068032054444244500c0c0340c14004c40d0010010540440d06210380300052001441b414050b118074500344c0241e01340142550a16a005540320090368039548050300c1300e04a80c0000c544811043c80e002c659104c407840554082c2851160341050304500e001145500103000d041103205c0c1e9100045400050401480c29044d1007003850415150302c070b4101010014060740e1100c256038040070001013030044c00041d0080c000c07580c0000b01c80c05907601322101503900c0e4007800b075607005801a580d0043c59a0040ea031419035140b000c2d001710314080b0000000029051000442c04484e5120b40c0d91208500c0c114100c0d41e20610300310340d03e09500b480d04c17013091112080403000410080e10b040000050210030300c0080c0000b5040402d50343c0c1340c0741455290344444500001c00300031a28011000b507038244200032183c12800d070140185001c4940d522204041d4140711225010420b03441c4005c00d142c1c070f030b0201640c000c0c05c0400340030a0481040e6508009428140c012502940c00507 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 792110080 1250 792108830 792108893
    0x403050904050c0304201212090103050c041809030c02030a0f11060a080a0c27090501090b01020c0f06160f17030708281d070e0105060a0503060a051c 66
    0x10010728111986009000001511b000003043d00707508450f10703180c540d001e001303545400240320b030b00180381119090341d0400242e5101f40c041410b5015501494034135051030341c1c10b0150b59450354090610709000e41460304520300294002450840d0f80f44080ba91010400e54490070080180905071803030344200d40c118100449003074014034800000300903d5840c1d48a803915030f1120302401e00342c19070f611040f030021441144808070b21919030b090310505d00414a03043c000030741c1d101703103104106d03403000305030301a00e0304514000130081030951510f6903a40c800c0041007a10443d88249414550903841002e40c0d04810b28a4180030030354140d15822030705125001c004220b6059400940300d680a821800c5c44c044011a80864a0006c00b02c100c040c005d8528014444460303144070038220f81d402c01c0c4c90044940823a02c0c0d40e00025464020b1040c1900014140070740480d46000340081d40d445140a49001341c40c076074a0001410720420441240c004156840c211424454030000003500e03e000c56115010322820b4 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 792111330 1250 792110080 792110093
    0x60403260a020d0c020f0301060305061b16023a140a02010e010c030207091d0d020d021b03010b0a0308190905030703030c1a101e0b0d09020a0e0403050904050c0304 72
    0x40308070881004110968242103540713070f682100e1b1005010703000b009842c0e00c170b281081d0386e00c038240c0f000700c695211109000b074207658003c06c480811000484890b01407056900f8004d800c295840c0d04500c8107500c00c02c40684103000c0c0d010901c84070400b00b0843d0f0f4a04281030500b542848890b454200d030f08031015920150360000c0e0102142d11080c644109820403606080741054000e03008034050908003800c1905947c20001100060300d103800c00c3c0ca0031044003ca00f80d903554600f4506001503081902c45607141740303100d0746441c41e40074040d00120740701940c103000482c4070906400840d90860041411031110380d030110690701000c11030926004031824030f4000703541ca103603e00c402801c00006e050380100300711800f10080011a81c001c42142c0034240740805075000503943c014510342c8903504000c4a46d01010342d5500d0115140d0228162501201001080c060078800c40180c1c2c016545840001c1c02c50b40350704100d03100c0d07030003a80c031240c95440d107808100c242e45010b01803900c40c1d8030520511020826 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 792112580 1250 792111330 792111343
    0x50115050a051c1b0e0403090501110c012a0501090b0c03190506040209040e0601030213110405040e07030c090225020306070e01030b03030a0302130f1d0702010b060403260a02 77
    0x800440f510b030f900528a401c0c00300c0d2103d0245250240c6800c00c0c005060590104d0a5014510039103403042940d80380c4004440f00d03c031380341152042d6480307040011525402100710003064041e03400c96407892118030300c404e010304202080444d0147c2d5100007400a1007002000c1c950400a4094981c0c80c50a18102c420180d0f41300d8000c01000307036560390200703450b80c0d00d640c100c5d140460080d0003401aa1071810300aa140c4400348001c2e4040c0e44900e070f81c28103040c4103203c1c01071445860302d20182414206020f01c0010111402e49201912901d20040041407880240b14000d0102903405641d8060f10700078078580101101f54810b020030084480070060b80c001c40d00d5580001241b400d01945840000128041d050500407681c25002c001005000c0703e43c1034000306500c55240b1220f0784141c1c5d0712588111211142d100c0c50503da0001c000c850f1350101040c8606030070455070f03c00451a4118040040c00c1c84d4400d600c1101c00c400c90002d60010000c1148102c0c8900c001104110b040600020002c1d40b03860 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 792113830 1250 792112580 792112609
    0x1a0a0b04241e09092c0601211a090d02070801180f0501060b0315010e0316120305090a060e120d050414031e070509010f03030207170c0409050115050a05 67
    0x26800b10109080c0c0e00c40c516031001418140030901c000444001c00410072a24010340d40504c0c2c3c80100300244401000590f00c1c101c417007003248281d010402c4c850345030516150000407515801d40c240f1900311b010096425501400c84080601030780c10480c6400380c508000755004d900c3d140d04005030340041e40c582c039941c214426001440241000200c1c41c0c028018481d030b8201810350344020040c08004e8600c14851041c468003070301d4010900e8814410160394244808402e455000411814802202ca600000030a14801e003001030500e2500c00018010003051740020002030f07081c2211000b54600b013581d080145404034082c20303040c400c00900504600c00d5019100004d045410580340c907417810401c0d64040081141c10b0b24480c5007036040b2603100c101c0c41c42858891810040003003000f00c42100d840c41104d80c189c0060001c0c602d00340804504c01e401411021060142030040c1c1d100e03032200e0049103203183c800e000000321002e03c03158010b50215650841401800300e040103221036160f96510101c0788 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 792115080 1250 792113830 792113867
    0x3010204032a0b0a0305090f0604060c120b10053403090b1e090d0b0c0417030f0904052d09120901021b0616210e0906041a0a0b0424 58
    0x30f40c3c4071140e01c3d140c02301004820b5098801d90007080180501030b0300c004450403580e070f2118600c02c0480b00c1c480c00d45412156266119030700da5400a0580d015100801d0352120440d1306240c0d0100e11080c02a001c0d111a4111203500b290020031f001701a808180c4034050003803000664244052400d040c10006000100707140742b000f00046100d00e66031990011fa00b0a544000c044080d8580b03c0640d82d995006407046030441d104620b210b4070074a001009403802900d01000d41800e005102041001a040c05000b40352039460304004240d1210130072055640c51701d5403600c42c0d00f6904219880901c0c1150454070354451520034000c0b0003241ea130201344005860b4903400d00c900785d18400c5000503824491101513000348004056500100040601c0c2551a440809803641044021850581c0c50382240015240c0c404844000900940362613400200e40500a41a002c1c51500c03070380201d107a1550a0300030406142c0041030030848640d8501d0882003156001c000b038400c1c2d20400602a0220031001d0501110 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 792116330 1250 792115080 792115091
    0xd120e0909210d0f090515130321022109070602071208090306160809121605010f0f0e0105060a0308120c0708070809091003081c02070203010204032a0b0a03 69
    0x10101c102038901400403c00c2c10070803444a940301400038100144111054081c2d04000748a6800c0403c45074410440d132820144010030070313038044900d241a41640d000c0360300e44400603900100349201070036003842040d00440303140301100b2945604000c000c02c070140e242e121000a00490342c1c041403200450710303040d18604805003139180201040c09002892901803291504103d803824030254001189182c03900d070301d50741d03031128034801e030302e49800b47c0460001c9002046003c00076419421460107007402100002039000d0b0441c0c5030b01c191442500303030400c56603c030701100611890038450f5580100040b40d101e000c0034a55528603881c1e000740844a00b800202200103194464090100c500c2caa500143c1d90341e40721080d21302040709800ca8a08203004841c0603000609091802c0c6042050329000041e05040c00101a403964038400340205c14200c56400b40014001070302c0900280c005144038503204548a401741c0c442c801c179221084c2001807940d101c08420000503440c8811111030b1103180c6800300340c = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 792117580 1250 792116330 792116383
    0x904170c0a0209090303040c0e06060a0f1106070914011707030209010c0510020a09060f02120a02070b0c060f1f09090206090d03080a0e0a020604050904020f0d120e0909 74
    0x4000707403038801a4100a4503401c12034034034004401188110f2146954902c1d1949503c4028407190741168a00d030030046c2040710082c00e6024400e18550310390140b9115001c015030204413401c06809480130b10100306070881c2400340c001c00c2001610500740a02e0710715400841103503484a0b161015014100385980002c8000b2a43d1062008541c001d800408445000c295046d240009501030a041c6000030003060300441c800748504844420b0107a186d00811b81c4014002d607220080d403103401600207620a0002c00214001c00001500070b41d00c014001c0c1c6141c2c5460b40442f02e600000510720f502c0e0842005078405104140d1290030203580f00c0c2c3c040060f2919061000c10142c0c810120a15031007030350311400781c040650003054144a640c0c540c81c28040607542c0d610083d50307101032142c0258404410312041c0184c1c24046040b5a00900084c03144021700c1c0080301003441c000c038680040d10340050701c50503041c03000d8222140f0814a901514101800d00d041c11855032030b44550341d016540c42d05501003660 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 792118830 1250 792117580 792117583
    0xf05160516060210060e01030210031116050319030212040f020a05120c030c06030105010c1502073008010b09040203090c032d01020307081f090f020a0e0904170c 71
    0x3881400c1c41c426460070540360100a5a9903c03d101d80300c580d5414450003195444801041504aa43c0546010380340c40454600394003a24888101d071040c00403d01520440c15030b80c18401c0380941c01980515a0383e58a05d60480b0040540342d4500241401044605070001c1610b205540c0b09401501040d102407507840040e02e04a495030000d03038003c107100038007201c144005c034424040200c100e007240d480b01540303002e2084500091040078045520700d41d0510210328524039072090a100000c0c0149001c038203a40d1a60904030071400f1004d200c560460074445007000f01d00314030810803141082010343d850154010064132592508501554010000c512950070400400c0b0345204002e0a40c0c01c00b080103003924405031980305102c00c400400300b0400c044e2030418400c8a0045529986180345507450415100b40c1074850f01b2550340c1c3c0d11540b86d000030201c98501c11900000c0603048003590311304256038010908001040c2e0288101c070390100340800540014020031007162011460350b110030303140c5840c0707 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 792120080 1250 792118830 792118843
    0x1020f010c44060909060712091106040b041a0f1813060b0a0f17040222050702060115020f1f0204091d0115030f02060f07300f051605 59
    0xe00003800b104080b02c54a0030700c010300b244684025a65030310907503948041c2c40d50f1202c090300c1c40c2c404601d00003580c6080f43c40c51740000b00118010781c0b800c101c010250010404950040c0c2c0004000c100c0480e0a1204130420408010482c04040e40d15060114800009610307216210300e9030b54240c60701d00d000381c550b00c500c1c0020303441d49c407414020041c1d180c3d54000108294810194440041c000014660840340142111722040740710b1180c0b0040ba94640e400c0c001d1028a02e0140c0c84e0085a401040d18980c0d06402401d2041c02141d014000c03e525004c12209801000003002080d5004a545880a40800036881401008005540c03c06101607807000c002485540c0000d440d941c2007220080c00ca041d0030310680c0411800c04000c2155110b001c00405807160980001802c0302460f80c41e440262030300701d001c2c1282007500c140803031401c01c40e55a4034022441d01142010030060321407552121030b074039400550b117008050400850790205180010640d1041500800440c8000000303501030201c00c000c0e5 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 792121330 1250 792120080 792120167
    0x1181a031b010e030d0c0602070204020910030f0c0504060f0e0402090613081b03031e25030207050301060b1b0106030210090f050609090c07051606050901020f010c 72
    0x155020101440000d4214140d10807030300340030864a52140c00541000100fa00c038201140d42d503550b0070b081e5039403420065806558243d0788503400340848400c0e50340725595548000b109890004d40384c40e4560f2803001f0303103008520380d5080c09002d020410040760449880706081c0c509151070b94113203802c0800500240100949136030800e0022812407805110203100c0d20503603400104961000c026014041411469080346a406d40c0060011508162406000f04548202e0000c0181013260310002c5242c40c01d0058084104454001c45e03120900d0780604c001c1c0c010380710582c02802841e081c0f485c0000c5034410000c8155855555424400c0181c03402e5105d0380c06545e0050640d07591a6000c08010301c40201070044135800143d42c5800501d910705081154401c401c09007182c07101d0317902c41014103120341000c441607425000d04c0c01c0f440c01000a2a03c5c0c4000360985480d4261a0b8502100080c944041c0e04118407007603140a0705c80e554290403210083e825030301c3d600c400485e220043c8440c41c01480d0303001e0 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 792122580 1250 792121330 792121333
    0xb07020106080706050417060702120705071802090f01110303071815020d09170a0807112119020315100815010515030f0f100509090309090f01181a03 66
    0xf804251154000001c104a80203a403003800c0500c500380c0015181d45058a080380543d21400800c411400501c010b06540760040b01900c0c110f85e0b0340c049828030300201d1489445003d0380021041c00501d41200415003803c001c0ca032113098140041220f40c0d0f24800980300030140304480c858041d5500d02c0c00c80d542d01409110407101c2c1c4d0107010110283d51740c0044a50000454004040070650f00368001c00c0f20030242c40e480040003956a0b0340c88070403603544880d0084d076a0380a03e0b0003079100b688465003500d080501070900c90000d0711724800014104034224844400c20100e20031841c02690300010a0100000c4884c0c1c1200d182e11481024222018558045030090140344284401140c4c050400d604070340b02510012a0011a1000003003244811183c200c4182584d0b03003c034040120710034040703a000c0c6010090320001d54444000400c00309040390902005c1d0300004001000d0b00b820504660002c800102800495040190203850743c0708103410055600e5071095503402520700100350407c02e10f4080e0 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 792123830 1250 792122580 792122593
    0x30608030304170f091509210d120204150f0201150302030a0b06032401140607030503072f0606040609111e040f060804020405090f071701020f0a0804060c020a0b040b0702010608 78
    0x1982c0d061b0b19003207120424800d8500e4802c0300c0c0e090a4a41075900052a914042c0c000d03c910b406d01914580c0105040c400d1156003484041408203240c2d804852000d03084d242c1209070051884001d0966079043d0311212541500a0704000584001444c44081d5912040640e003a54500d00032a203071401000c40c5901c0c02c0b40003001c807081c140c48481098141d50050042d001030a0610b8280000b9200c1c0c6400200011010030004446901c2404154103694401000088104000382040304c981c0824001480b180c003d501403105c107150034400c00700280510306040c00003140210f000502c0c0e0040b2403071001d102983d45030074031011801c403044501074201c0c0d405010003261917410081002c00125001c03400340d460100800c444100c00180e0b0348040c4800c600601102d82800c04002408155140d2182150340a020b40350034852014058104049155550aa01e140c036040070300555802c45100030039900100300c0f81d800b103030494404e280e209422064140c91502c8100041740182450741c071510301801030300f = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 792125080 1250 792123830 792123859
    0x30f0b150a08041a1e070c1e150f02090406090b0108010501050a05190305330d020604080318010207060309050c010e0d020901060e01030f06051008070512090d030608030304170f09 79
    0x50041d0300d0421041685c41d0416070b200d000a8500700040314015210580c0902d440c0c841e240f020307400420746480b4802402c55400703021205804da0300070310955000541c02040d046140d09003807240d007000b400354243c2030102d01080070028084607018040c9504005001031840010340c0500221641c16419801caa844900100401402000c0c10341e042032015054159a131002e5400349880740c1d20aa184641010140c850802c00038045102c503c1240c015100b40300008415a003440600703038601c0c000480c21950348114000900703100e034a40042c801d25280007510000b10340c001030124032000c0282071202c509202d510000700c1082100e00000d600080040010910070350100c4000500032082c6c074180440072000711410706a4004d80101d9802c0076103107100c600364521611324a600000c003424120700c1c20b44035198005a00c0c0c4110303490546940a0362080440301d5051103a00020400c1001550440c1040e44e40c010083d003511461404400000c078404500d40c1200c0101e46240000810504a26004 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 792126330 1250 792125080 792125101
    0x90a17030417090901060e0d0501021303030905150d0507050706021c1802011209020607050d051e0307082e060305060f09060102030d15050a06030f0b150a08041a 71
    0x1c0781c0440d11694030351071451407004200c0607100103220040040c0b03156030178060210340135070140051a41c03011034824040003262082c4001d25401c106910302c3c4d040036085041c050400c000d258000c9011b0180c0c1042110b1040d0103005a4042d08440100410b031a11a4001211140585507000d0420380c40040c110031820085003001070551020001407140449810380100e400070310900207400b10f00c40115408820010360b10281d20144014002803c001f156100c09160551030350354000070510000d044008103804150b00ca18640d05081074078914075009000608580300905a024610540482d035070840b240204910b890380342654041c50100d03a01c18009019110545285010380c0c640203551f2864103008400070301c41c010680065181000006144000b0041c041d4103c1055144240c0821141c0c1ca480b090401080c440d5008920920340f11050001c440c82a4001481020700c5000d0f00b010260313031420f44001e4080350070103d0690f520b50800364404c1c41d5003605907104a030703542d0030008148031 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 792127580 1250 792126330 792126337
    0x1106041121012c030d0207020a030c0f1a18010c020a090203070302183001021204140c090402011b0309050d060204060207060203040e0105060c0c041a280b03090a17 72
    0x7001c44400d01115041c032140f50701000003401d0246240c004110034403407020290010544684081c2034035149965a4403201e280000d2a0048605000400400c2080c0100e8620320703c240b1084160091400c0c0110301d150140000120850f1b044c0701c41011164290354030480050300400503041f0640d03403440e00a03001030007075202d13110990003040130145510590074443c4a08045040030382a09500c41500c111000a088040145018541d0208003c1000c0074081c8502401544200030804803031881990140c20036041c0003026000f000f00b2400c02015030703444083c5000a108150000c440145075050072192111160880d54010102e418141304102c0300b0740c0207104903a61942a651050f4441c0c5080381c0300e2086105e04da030f0b40f1414070014007084c0360040c020703d88507160074102e424114201c80802c0c1998140000b09013111140c001000d5203017400a10001d100d034040420101c007640690310042014040d02802008440c0800050007149003000790034006504004076400c86018040c02e50500d51 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 792128830 1250 792127580 792127601
    0x904050c1b010c1209230703202b1103010b030a0503040510050a080c0d060e1e0a0e1005070c020d060213050109081e01021608040510110604112101 65
    0x51400d0642d846135081446078804059100d290031295007440508024041858461034019002c0d5140c00400a82c0310340b01c00181490980d502c40d0101644801c118508501c0c2c0f01041c50315240e1800c0344801c5900f8a010180a60301c610f0281442c03401c1d00100e40100300c02d1503c2c0b501440ba514060040c008000f0140c01142d800300c13481c003802c441000040303c45005112212001c1428800803440f0880c1e618060f26512000c0c01c0300150855403440031040c0d00200f682c0308594100104155428014003203450341d88030f50b20315414421007030f1400f803240e40c1c0c00c0c03409c4689002a5840c00803074040c621451822a01ea0780040006410310764504240000350311116900d980070041c00c10000382d41d4007542c0b903441110f84100c0030f05210704d075900c6d501c003001080009507071465500300102c50f581b8910010b00c40495015103401e039115800e010900040c2d030034540d0f6210a1095055416940140014038180c0c001c0c1c3c44498080c201d101c92022a84c44410000600000c60144604100c07003c41580129801d8 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 792130080 1250 792128830 792128837
    0x9080c0f06160c0201080f09100c031a0102030901020a0321060b1c05040c091e02030109270807140c031e1b010206070513050a0303020c0112060b0904050c1b010c 71
    0x941c0b01c00150707541d428030301c0001d01040b10703840007942c0640040c0030507078065001070075518540062442c1c0c0c030464444038075000c0030940c1e40c0d0340702e0202910300e50b00401c090403c1c001140381980c0d440002c0d5a945c10310ac0002c0802c0162251800381621030442049100700303001090010035160104001980c114003401400180c1010129003d0f00403030186601030b6030011844190705007072104010140c0b100105ca6408109100c0c0600324446903440218005c1100450009810340b40708400383c02a28000c45100d034002890107104081214442242c4c1159800713420000031046a04e58103080204405440ea4103000d10040030071684400d00340100a107005c00c05480b000c0210805911100c90560003003401a400440028041c6008038000d010111010100101180d41c0b080040e205441d070760012401a00640d401c0c0c040c1e541c01500740192034a00500c14011103013480494060f9000b00240760f40315507211004240401074070011644045400e04000040369001c60781a4040e042015115002 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 792131330 1250 792130080 792130111
    0x15021b1201110a39080a0c2004060b03100b2209140c1c0b0f060318010506060309120a0c1505070224060d020a080334050307030309080c0f06 62
    0x500101801134107403c0030744200c00004169526202c0c1517030807030001903003030091000b065004520703850051041c0301c5104d8035500d2600c2c1c0003000d00040c1c80040e030201040c48030034000c0c0032420001d0107002064588146600303840304400e004520900c0b504000c0d03070603001c150b150045003c41d040c0d001516840a00001803109880300c2622824911962910040e02401c035076a0b42100401d5130041c0280c041c008024107130712030310140050201c1e40701780c0791000788100e5580d079500d1400e001c0c0074803a40718030200c0780c3c2811480d01c1400a91580b840907000911240005a6154803a005031800d810321500b0820b500964404000c59100518040e42e150000d031141240307549884040c100d880145088070307000c028043d01c0e2801030184100001608980c0b0601620011840d01800c0002d003120240408000f6031000c1070744614400d0868002e030f10b01840200c010540c000c5000001200c0190350701d03240004014146003440c81c4240545050311040740640d8510b51035456001681d10301404003844101038 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 792132580 1250 792131330 792131387
    0x23012007061a0105070b0612010f020304050727050406020d0207081e0a1d030c0301180c080606060f0a020111040b0a080c040e062e030615021b1201110a 67
    0x7548102c042140010410030605c4001030300a8051500a5005400d0324440f11501805609440c46040c0b40300229038003100700024894200300381d03801044113654048011441c0a4500c006007035524001c80000d4442020808010b034542c12200119200001151980b20710718110145900c00006030110301c43e4040b1544203001c025045030030000164440f41c0206011060404040085852807607060186101d038810711b4800380182c5000c48504080202010418540026090941c0e000b20502d0303840755041040c01e445450448148041c10082c0c2a02c2d040c4202c402c0340942030400000308107250200e00041d5000d01c681c040c00e00b240d540c0d00c5520725640c40305404107145c011032080c0c05c41c0240010100e20785041c41d14160300c614159030003d080041040007038440b80c070001c80c0104000b1ba566030003000800410040b805100c40c45201400002040c4e20b54842104d0841c1b064070311400c101808103030040d00941c00140c110581c80742990312a0384440c0c014141440120012000010007000307500c = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 792133830 1250 792132580 792132611
    0x2f040308160c081618060e0112080d06090914060c030708060316030b09010e0a0206041512050c032502060a1107050609101503050304030b040606180608010e07032301200706 76
    0x1400d60f140ca1007e03503616860301420a01c080c0034401d007642c011004200c4041840e101c0e0003840d015040030f240110b030b502c041c2c1c41c140ea248009107843c550144c02001c1804122140303501205d80201c01ca203400c901c681c8414001030304021415040c0708420144010002c00c00c941132a03020301c42c42a80f0f00802902701c802000d20b843c0d50070309000940c400303810401070121100e410800344071200301d880c20350040304055100104607503050f181501c1003403011040100c00d055050785041130120302100301c41d0072440c140c0b019543c0c0d080607124001098548080300d0800100c1000e4440154102040320b0711401c12010715031320741c400d298130800d08034280f04482c008001e44016680440b5803007002507140501c3d603200c0155450014204440c41c079244c0c0400581e000701002c0359900c01c649c840c00081c207030746080b60007421036084004014107600502010004900340008562003032501c91500c13010307001c2c0d003103100f401085514000000d0602007540c0d25100c04007400641092880750030200001902c100c081e0 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 792135080 1250 792133830 792133841
    0xb0406090e070302040f0b03070906030203010f0b06070605181f05010e070f08190204140f0109120b06030c03060708070206010605071203090f05012f040308160c081618 74
    0xc011903204400c2040107045c035501c0300403071003100c00300000d007903180300b0000307003044050742c054203510741c8848040c0250711b801e00c06e1880c5070300e03440410030071030b03010b000801c0242c014210083e10300381d55003001445a40c1c5031072002d822040258252002e50080210700108041c0000720600c0706494180049802104501028016485915880f00c1110044412548020000d1803020251526866608548000c0c00039001901c1001920008d10000a0901002d10701340000ca9040001d845810420300441a903800c503015000401d04400380c1d101000300e4030304810850b0064040c401d910402801c00d5020701c146004120960940702c1691741d4920803180c3d4028038402802c103010080d1205c24083c081e502c09806544610800c131295017094640e9400c4038036119a0003003c400c0b0610310840d0b2990251a654000e5400380301c14240340c250349600b080750180041d0101c2804032a59200180055180798000900d00002244c100c2400b000c121000ca5045100304141d5110100d0011700450190148 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 792136330 1250 792135080 792135101
    0x120f010605160606150f0e0a05060904181a041505090c10110d0905040b03031603031805060108030a08090118021003060b030109020304170309070e1b030a0b040609 72
    0xa541c02c1c100c0c5018901403150800a044950550b00c001c0010711807003420400d5400c1c2034540300c40380c091501513400751883c0d019440341c0d445204030500070b00c6150399401c00e403014550180c4e400104002401a030140805d91100081c01c40c9003c0d802c07090700b40d00c40082840c4207600c108100b00e8207014400d5002c083d1007003560700000d5034110b0341c041d2245081991403180c91504610382074001801540000742840322950602c0001038500341c0900c02420607009280343c20350294000c51401b01c05202c1d1206600100350300600f015191041295440c01c250400c0810503000403d0f9071032075075543c2029a0326813203028110082800c09000604404041c86601d00d8500c544418599205c002d070b081082d01c688010510041c1a0380348008189a101c0320081c50180c20010401a42c1e8200340c1064910a4109003604e00030080070410407800d0740f8013003112001c907a01e03400782d43e00580300d001c0d40d05036882444404103407001021040050440303143d000354107018800d9400304442521200704405559190a6 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 792137580 1250 792136330 792136337
    0xa12020111130339060801051012020f09100801050108060114070f15021308060a020c07090f020f07052a060a120f090b0a0f0605011407020a0b040605120f0106 70
    0x8100081450008183c0703000d05502c2c03807040e40e410400600d9800000401c1c004800d9213030034100f801615040101c090140c5000c454040e031a5150708001091180000411075040342c020039002160b60402091301c007498401424003094200c0500c00a00c1d1200920845001811040110350554010211950049850074a02d4500f1219031208084101440c10499100c3e80005110030b601949101401114031054030b0103800030301e400c61151a08001800c81c481c0300c1c0c0704000c08001c0440001e0307103504884403482c012444210aa200200900440301c841c22172010026a6600b0404080b825241d280314540c0341703140300d840c07524402a0f0814010081604100c0800640d0305d080d006800c0c0380c01207040c02c400803812156510b10b000583e00801030403200c441d202410b001c0301c0c0003280990003408124034010064a45880c0000b03115954511006081c0c803000901201591111460340024001c0b1a20140e40e03140e560000070020f43c4031103a82141285002e021448016401110b681201c103030b0342d03 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 792138830 1250 792137580 792137617
    0xb0316020c041820060d021b031204031407020303040303270602060109021602180f0f060306073b01110105011d101502010f1a030607120b030a12020111 67
    0x15546140012649079900d03410300b611340d50040d142d03a814002c0c12588000c5c00302585903941030070b458a10700c501100d200341c2034009204200a213030102d94a15446074052424042c15a83c12881002c80c0c40760140c06501800001400720605030003021707084100130400c480c00000e14000050b00b1205c0d10318098a40181c0141c4010440510580c002c1c10b02d41401c2409503130702c00561b6000075030005545603144240c001a90400c0f58002c41200031382c1c0c1c8080d420f000c503070303040c5040400607840d00b030700815107800c3c03104490801c452490701c00f0850103108031040c3c04c059882002692182c10414510b01140010b00f40e03484007c402c90b042c040e0904a41c02005240e41d14403100d00100d4108400038000d034071000c0c0d5103e0000303100001d203501c031800100a400000d410707500c1f0864102138480b400b0150f8640c007540c1c07810340c807103031000103034158009000c1c41c150000d400395009180c00f80201114060741840b82151400900501408909600700e0039002000020700341d4441d00000e001d0304001d0241e81c0d1804 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 792140080 1250 792138830 792138833
    0x212060613031104021c23150618030a2a18050705070c0b0a0905090108060a090543061b0501020405041a040608011b180b0316020c0418 60
    0x2c18090f1104035000b4009800e10082104020401d1400c80130700720000c0d21100314913528040e160900f611101c91428401c054501100c26074450060540054021040058010f480d40145030400c80c55507401015284a50110706001c5038042c0030b05103240c03406e64031044c070213214a2043c00602c22110300c040ea4004411014602000901e0001c0c0b46d0414008100403160010f0342e040320203005088074150300c0e5111425054010185040c64000f2030150f5094401800100000a100303a4015414900803a007200030340740040c2846c68a10800c40d440441c019103d1541c0316003540c00100f842d58581d44511228000404181c00347c481c46040c012a000c0d00411120040601241d11498000c50006d4a495900c41c042811148a070301c1c841101070300f07a5442c0c26249003900583d001004400024800b9086000e2001e0a442004019405000300080c000c5c030b481c070038910260000c00303406812a444c4d1510044a000d074034110444540140603030100d08805250a105040b0300700d0f50303488111081c0d90349 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 792141330 1250 792140080 792140093
    0xd020705012f07091a09040f060603061a18040b01050111210705190c30030e130c080c0a1229010201060317090607060c03021206061303 60
    0x41e440c60051099860899244007150201d02c29034108086000706080780c0307055038079000c0b90fa440e00b0b11082000019040c0445030b41e028025900305420040d11210f650091622030028076142e40020100c07410714880ea501c01c02c0d1302c4505e0f00c1000b400e80b042d5403c148071010380d0000e1002101c0c0200800d681e5401030100e94481c0e10707500c00c80850102102c230200c01e843d40781035101000f41e80156082100041501c10800140692859101199150224401c107643d079400c54203024060303009a25202c6442c00030440013085401d150394841146040c12640c2c1d4140200f004a506101d6401408003035001c4407038005610614442d180c160f65468010340b10101c1800c80755004501040820800a200141c0c069a40c895030065020050a04130f81d403520300c581845001009414505691520b0010004100044040024541100758040d45c0d003626a0009603540580403001d040b803480c080e02100c246816034014201d010b07960164121a0741c1d01c0d010054644140f00700c1c2e40c0c80c1240740c14100005030302e = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 792142580 1250 792141330 792141347
    0x10140108100e1203010e01030309090203090d0f0212070605041e08070b13140c01081602120703051306030f050a052e1206090b010e010b0a080712020c0105090f0d02070501 75
    0x4030310069600007400c14401003c15002031700100e4256515000420030150010304000040c1050711056042d07280c4100c0e139036119007542c0e54034018410319500c03038030000d8404d200162100070721305442611a8090308044000b07200880b002c480850b9102100a00e00d9401c4004541c002d0f400b242c4189040e15660315507019000160051101041c4800440001070940c0f00410351003076084020310000c40c01c003000600030305001c4c00e1a100115010311044110f58080b03513111811411540c0c0958030303001480c0840e21441240011000b22800150208055500d9045031040c080c120406111030346030b419081c0119101903c101031440c8540b0803003881e40c25001828902c03881402100f181d101ea4490031072045855a840c201c4140303903075502081c2003007060040f07240501071860b280d41c403079810100c03240c01c03a2090b46400360911a03401e0000e03162070320a100310261700308503880644d11464641c8000b80600007d0302d04a01c98007071384010b2080c1c403000080140b4148502c0d4001c0115916100054a1008 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 792143830 1250 792142580 792142601
    0x602011e0213030c0e0a0f0b03190c090e0d030608060c12130b0a0c030e15060607060608070b0409140403050d0c020f0114090d0c03021b040f09051014010810 69
    0x55040c2c03000000c2400c9808010080000002620652074855088022559508441e5a060b8a001124800d039100014250910b11900206140c1e80107141054001c80c010ad500002d0b045080c101e103854001e81c04600c41074040b03900c4d02c0c10f103e51a160fa50182e101e8000700d502140b60034050110944c01d61050001c1900181003014880034076610f911142c1c03840208640035100c20340c40303242600c4140d030f0510507130784d41e0a0500c01a080101003504455000403000c1c100503ca03e5000c207000d000c4c000c055100740c0c0104600c1c0c0459000d1580ca02040e850b64206225408480d4a840300c2e0303000c0f007280b50070402c0c8074a515545007450170001d81c018100802c40c000b84c05045100b0702c400c04080b100b007480b4124038180d914401484501d402c824061810f03e800d6542010480070f01d004c440041c8c2c00141e0b0b0804580d803203072110309460011001c24010003d0209243e00f450a1038103c1e0144a008280765040004000080c0000c000750881040d22410030701c5440310a61002030200208140d0f98407068441 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 792145080 1250 792143830 792143857
    0x5120c0c010c0618060209151204030c140a42020a031e02130602190201030903210c0806010e150c250501021c02150612250602011e02 59
    0x909180066048440104c441141ca26034001101e04480c6070400c06160741000c0c1c1c500203450302011012003260003201510003400d104410703600c0020070025549140d66851010201e440c010741074100303241001007427800c03942d00340020030403520000820140811022244041540400d45116010000f0342c083d403401000c1541d07594020f40b8020070808100d0901010840160702d82036106041c60003125168000025036110490658440140e016004890750702403c00194142460a00b40c40003065a03105800308200c4c0f094031015140b1a5101c003000600a54605080b03580d00c0005450000e10801c278254884065501c09503480e9107080180341148003602554809540168021101541410018901071030005c060000b940d0422403a04025003441003281414001080651140340b1000ba01100c14000c10011301039444402c941c1c0e03900c2c0d14020895071017821880111241c48a00d071001d60030f00000050015005105005035401810203621581e83c2130600c90100c0000d46c031020100010 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 792146330 1250 792145080 792145091
    0xa0f090509372a09090e15090609010f060f0302041a12030a020114010f03061d030310050301050c03011d07020a080a09030201030b040509030901030209010e040609060305120c0c010c06 81
    0x810801480142c901e14429000ca0303c00555002840301124414110383d0103211044030005541d4480315480c2241d001d85400190100d41001690908840b20100d00a192071a800c0c40541140055000d100d1500a402004401c11a07035082d0700342c135203500c110000b40035404130500c05032070594848c00d03030301000e06000c07030f0050042000300310f88a00030705918815030004180d0b2803410342c0a000b22208400e895503c2409903041030001c13142d000301404080d000319030300c40841d000003026142d56946091610121390b16854010300442c040c10240c01a680207500b098042410b00c000310044d00d0513a2420380b000c90607850b1060095441c030700c00901a6085101c6c00c07400102040360728004003461030030781d03032280890781c01c0d40000340654075100d48070741c000c41c50001000350b8000007000707441250809103000360b0740f42f00c0310004843e4800c1140b80203034072615003900041e0251282d40309800b203a02c920183c802034002401c51120038011441c0c402c2040d086107091001542c81401850703403072445038000181 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 792147580 1250 792146330 792146401
    0x40e070e0f060f0f120c040302031005060d060207081e03091203040506040308042414090a2f060c0c030c010c050304051005162607081213170a0f090509 67
    0x41078034240ea20000b1b2250000302802981428440f403c074030040441c050002d03081c408003141d0b080e20b0380e00700030303080542c08628107081104640031101e00203074980000e041c10f640c5002c003010a600c10749107560184120303280201c8060041054a104a4100d009000c290343c5940b4240e660b0301c0e00800403955511040902c00e44c9403000f5009810140c658400041d143c6000c1602c0f0141350000342c01d08032107912000e01c0f0340005c0c4400800e9440c007026807503210807001e0462080d5482e0060401400d81c4a0b5010a141e00d60080000e040c1100c02d100301d04494110b045d0b43d0056031000900c02e0041c00b01e400400c0300748400e0074038580c20311503e03407a460000d203401e40a0655480e0801d1354001190440c4034450313019040513500704260002000e150f02c5034031780b540d5640d03400014420a00303030303080031000d1070006403560503c8400f6202c041d40114401c50951a82400180c05070f11048405010500d0010745212042c4921281010303180090401c07070003519946203882008007a282c011804458078468a003 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 792148830 1250 792147580 792147607
    0x207110603010b030406050a06150f0e0406030f02091023150a030518060705041a190c0c09020f09010c052b11120306090c040308040e070e0f060f0f 65
    0x103000b003e000b190691242880e103011001c0d240060195052a41041e0003030150078008404072000341c08500344a8078409001c201500c451505000c2a640545051000000d1020030462541c003e031080360081099a66100d080314607003a0381c01800c0048480d00c00e90110715100b20038403140b0480c0180b038040d91130f01d5020f503014030381d10100304040041d0300c1d0000c0c08620000c14580b0302e410b40c40c80f8040c00d500e10340180000c03c24000c1d880f80d065058010340f51f00b60b40944180c106d070510851221080d482c40384400021f03104000364141101c11030341c011000620105540b094455050110306018681034411004440ca98003120301591140560100c07820712140d90544040340044034807001c91400c0e20420080e081341580d04c50700c601c0c1c0d00502643d4985455107000c80358080d00803038000445485008203811703240a150001410581c1c00100850700700d2003c2140c62203150f059076400c50126110040c03146200811840c0c2da00500305001c04134035030100c9000390100c19a0701700503504054001c000075 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 792150080 1250 792148830 792148837
    0x30706060b281b0f080d020a2d0509010e131e0e0613030516030201051803090d060b040b0303030c090906030d020601060c03200d020f0c1302071106 65
    0xd40c1c0a0000700414240c02c000071058801c2c11a25040a1085159002400000465100c1c1840440d0900004100101e602da80380b00c071508034200c030351121001d00d03440009500c65646940032907044941c3e50300d600403110000d424816030850030504250715080a0781d15404c01180c860601c18072071204600da03102d25264880200e0f91131808100b0400c155030101424850280d4418001d041c480e200b801040002102c5d5005001c0d090402045c41a82c101192280a03002da0714030b4080c18010303d03406155054005a02854032625a240384094044074980d580c0f05e10b080140d003000c10a010400850510f500c1040e180d14007507c045000800c8400190a6030b008403440a0b1110700403070030032034500f00614007550019040e8010030018075001c502a5503060140b02e100100100244200c0403d44114a640c070001101d1607016664850202c03e01d440c0d260f222121001882681001e180c11140055081020b0f840074002c1520384641800490195100385825115000308000d044c3c0c251300c0f048001c = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 792151330 1250 792150080 792150089
    0x14040302070302090603012a0507080711211f0b21160b040b09010302090607140d090b0a0c14030c030a09050306010614280c022409060c03070606 64
    0x6000050b0840c410410300d4280545098041d030f00d0521100b08006903840900b030002c426010345284d02291341d008803018405c00c0c00007494144085030b020200b03c0c840220081070401102da1021100560507000c3c0080020016074000340c1c8400512003c0000080001100103114500410b040b0f0040000c00d00c4101d5019132100700c00e40c0040d880b402e540f81400f400b544801c1101c40102d0891810350048181d01850249660050000403034000c141e000354100c840200000c2c3c01a41c480b1800e0800c59034406082040c180c550060300d18030b402c181d1048844c4821350317a0700f481040c10081031060845111661007421070707038415060f445004655081016012556952005540c0c402c0d40402c010315449150b48034500030b0340702e200180640b80d00801c0c01001c00d40070700000380e207030942d0214604010141580781c115182100c070503802c495500150f2451040c0c001d480e920300c2455a0030001e40d11042ca07580c0c450b4101740900c01804585443c3c0f004015504504c0126801c025054031241c00311003441c1e00 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 792152580 1250 792151330 792151333
    0x20102010603022701080111070b090102120a0b030c09091b06041a1e0a080601030902010507020a06020102030a0b030a02090103080f0f13051314040201030213090f0f14090d0305040614040302 84
    0x142d100404c0041e40c0424090940034000740700f40079103a030060203140900e4000401c05110080000c01540e401d6040d0b41c1c1072010103010b1707031181c1410348811004121411a2174000d028001135600f460821500403130180808030002c118030800540902d10620301107042680c8803108100001d4003000482d0000504801c7c44072160741c84400c50b40c41c9000781c1c00c2400040ea80e00e01402800003558002c07044640c0f0001c00c0c20301103031800003403004940f20b200d460b20080d4494030101c0c020400541c15405035116441d00d00c42040049041d5041503030b03649440c07100079802074104005000058158024011103000c01c401e00c2d051900c8260802000d401c402030b00c0d90b202c0c0d160f0004101e2071800c041e00001010118208001c1e41d40c0350f8a202003106030050001c0c0c107040d00007a9001a010514442200034200d5180410500340703004191005032801d040c10502c2141045221b0031310000010b0601c0c0101124801441d24040c20081980644002002591502d079242c0201580710f01034120b407486030f0f21950 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 792153830 1250 792152580 792152629
    0x5060c010507090e0f0115091e030b1b0f180603011517012d0b0d091505130618020414060405010b09060403030c050705210f010c1b02010201060302 65
    0x1000030f210160075403140e01c05162000c24080000340b49510035040d112140a049110713020400295000a0305a1100c01e860040c2045034006c12090005041560b124450a01540c0c95800103050f032840c444108002d01c44007009550b19801d40b01c0f0080071403442c0140c40031303025054000040d0041d0000d9201ca20512800f410115140358020814100ba801941000c0d03829418103145159a1001c0e50384c02001215401e283d40000511903403410050030310b140700c02c2e6510a083d02500107411901c0f0201c40382c000a0048030b40814003401141e100710b00c041740841e42a80030351a6480602203d400c0e50302d0031510614034001588680c090070040607011607500d19581002d000b032200701c03101640400d070f03061010f02861100d40d4a240455049a803d454054504500c83c20458100501d940c0f0032030344854600046480c0e4111806442400e0341358070281e41d413011101e82060f02380c0d8900314008001601e0700b00701c41074410482c844072560900620001450702d8581c1c0c04201d04409540d000d00e020800340 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 792155080 1250 792153830 792153841
    0xd0b01080304090e16090b030c090907090e07050f060a03090b040c03050d0903210504080d0918020a050702130e0609061017030f030910060b07120507150b010905060c0105 75
    0x900500d078050001d00000c1c40d00354240e42000048031a46d01841e1111602ca030703e88481c90390100600340103400010b11180780c504004112950340c40c0d01d4442c001032541011200c800340074000c04c8600c210350010340030380501c0201108010b0b5990140f00303888249a230700c0c0d20b400c01046000c150140b04a11961113810140d0442c03c20601c0c0c0148088200108060500c0030320000e00300d10581070b44040382450950340b0504041e41515140a240c011080c248141c0c0c20141c80140d00100c0308040329004104c0c445031011a110010a9100307404600001c1103003040040300500784a0070b61030b8026001c640025141d4080700c941805d00000f079400030b003140c1c404e0091050851199060300b0050035400d00c416030580d81d0b034000544900842f804034601c5000440020020341d4144481800c0c03958402e010014103456012505d810380140b8130036500b400c0e019049a40c05402001111107a5401018518090000c10b4580d00984124180713941002022500040d0689070710025018035500d800001c291450306 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 792156330 1250 792155080 792155099
    0xf0706090215090a14040e0a0609172b1e14060301060302010c1704050d05241306090201051e120a1e020d0912110f060c09010e0d0b01080304 62
    0x1924149000c0440410441031582d0303440380640c0448180c91405c1048200e9100020018442054028468020101541c00b0092103a015004091188030603050902030004001601d00404000200e41100805d20684c522465a0301c050701c04220500800c3d145510040e611034440440584100341e82c0701d28800c0030f40d910018116610100c150020000c552540d00001c00f0300740c050502030100740800c1c0030700c19281805c1e03003250083c0c50042c040c8102c03408c3d2890001e030349000d82281200c0359109042c0380c0e005560368100c0c0c1ca01651100800d94901c0000d03444140040142c0d941c12414841e04001c2c2a0041c03070380c2108030702042c00415644c0d07116070402200554104004224480c03030782c42e00c903119452803904000c00300032100d030043c0143c80710400c08440005002c4098050302c0f240d90b481d000058181d10858401c8880b0300a000c6d902050380c4074100940c1c070f01040d1121a10340b002030203030101c04e503c00d40c12000744500051000600c11010f40700e4440000e420f0300031440d41e4100240a0200190 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 792157580 1250 792156330 792156349
    0xa0f0906020f03160f05070f030311030a0f0f1e02030d270b04060f1a040c0f02030301050111070e0c070506011a18040b0907020c0406050a05060f0306060f07060902 72
    0x9400038040d6945004422500c2c3d10a0400811135414982000000d0210030100345410a40c03200c11036a940e44c4074185040c0500e040c1c4011000241000d08031401c0d150080150f980054054403006002008a0401e440121403034403660200100e00b000b044030300705c160001003d000310b107401440d9102d005403059402c1c0c07401d2501c507000d90029a040120028844002c1d0484c96801445082164450340f0300100a4035025150038801401d0103a20740100c1400175000e003055808880410101c1500001a03410259113605140540c205000400040d4041c10110300851075800031750f4445c0745c854400400c116820b50b00b00c107002201090050812208001c01e40c090001060750803100c0514101c2c09103c1c0c0700b40e25880c00030703a04c001208201c3d500c131500700100550000f0081009842c003081c0095a4000d426140d074480c0703090500001d901d0401243c0e0b00140c3c0c0c0b001d000305d0314011402c1400880c59002a0034181c120307408200c030307956550490020b411401d2184c1c00200c0d00dc807141c01040314a03a0b = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 792158830 1250 792157580 792157589
    0x40c0801180608060c0703050c101a091009111201030c0501020f07361802030c01090305030322080304030c0605060406080a0b04020a0902070809040608010920150a0f09 74
    0x2e10300001486030a50000301164000b2203000300d01c1c3e64040c1454221018007882114800c01e11035001c0590a07210725400504503440782c00c40c0514010b1031401049100e28017514401d80000203001c051294030415080b0200c4258030020852a0211840314225501000d0340251004c060400e020f00243d0f1b418009161781001c0311001701800e50400d17910204000304200c1c000d144100c0c2e6034000a0b0308030040e4405c800906c03026070401c0070118800070b1111012003200100d100b4002c0030340c2504258050b03800740080d01c0e080f400450031556050250102c1e42c8442000c1c1c0040044e00800b0800144104011071050f40700390307222070b821401c526124007030340d801404c080d00c104c2c14007005004100c000500b18601c1c40e00b262440c10552594004a40301755025001000814000542034092242e0100142100300d801e4504000c8181c2d81c5402900b296480b00c0e0090442c1c000c40b030040e500e42c2d0041d020400414008040a000c1c00a551850310103038095800e120105e00c112144c1003010380c01114100003030 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 792160080 1250 792158830 792158879
    0xf0e0a2a031208060d060608030a1106100b0c030702280e041e030909150303170103031e0509041a09060a1a0c10020f120c0915090d02040c0801 63
    0x11400c55582c002109405070441d000c00c080400054071a5551420745e6800c0c030342294040001603140c100c490307102d07402084414040340c0151460282081e0025110344282c030104246038a4a040900b100b10686c820a10390704248010b01020002da5036415500d03601c511000e1420741220254035040440c40c85c40d600c0380414440b104200404a10031034000d007840796a5540c0c40d090200f4624045d0745000042d00301c017403200c2ca452440d21008108660030400e6900036103440c1c47c2141c1200b101c4486d190300f40030080004000c001940c104140c50010030313851590300d0500d181024a0000414115900c09a180f1422006003401041d1030600404d80790300601e06441d88034102c0d00b040140904200c4c3e04101c5501e48200050b00c400640b018000008000103244080d580c030a80002030390096000084824907900310000411100b403175400c216042820041c10340320303070700300441d41071603039a00200c0140303401c603090024480069407180b0034011b05500503140d40c032280d4180309030300380241e44581225140 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 792161330 1250 792160080 792160163
    0xf0606140304021c0218070f0207090203091c2c120c0102060c0a110a05030c070f2d0e090d030c030209010903060b0a18060e07031e0f0e0a 61
    0x26861306046103031070300084e491803c1c05240c9440800c24480c01800e600300d01884003014002d41035071010507604100d180d542107407001616510200228441924009800d52050403a0300c920791100b0f0046103c2051801c24100c00320a04110084030b00480401104840c01400d24000c5403a01c03101b0100d008844500401d00c004403200040e41d522030140850f1801e59002c00c05280c140e204000294140500c6010b0b109040454a41940e40344c005090400c01406180408222040d0151455045864200c103484003d5008486000051688140080e10326980e180203d00c0819540e050ba002e0321745003004281708010414014111030009440300109401007150901d01c2c0c0e48003802009982c0c11150010704055424002030000c86143d100b492687c0242000c2301c102189a032100e0b00701c0300840d0140205580e800b50803012601e5100110400403003a03c25464500100d41c0900030503026010000b40c91404120003602e0a05100c8040311604100010101e00b0520741d0081d4500340c100c0c0400015 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 792162580 1250 792161330 792161333
    0x21040210032d0203040c080111030c0a1e0f0e0a06090e0901020d050705030103060b060a1409150c030a02101a010f02010b0a092403170f04090f0606140304 68
    0x40418460324120105a1603681c84980c42200c55070b250800140074642c0d903000c041c8191080c01075007040707906443e04c003e041e0340098110010300544401c42c48982c5003d00d9940c40183c03011440d0443c422000c200000c40614141c12500ca40c1a0300307001c030280e110383e0312000050f10024010b22110020134021040040d0800907180c000a1540039200204101265552686402d42c028000d451034074516a0410341480205600030300210305890084000b0300084045c041844980d101c0d04000c039000030400880b01001c408200050400c1000c010807959407080369029a59280d00068007180f46504001000c06c20310360100103900125608040034803040c00c100794404030000d019280c040c1849400556042401e01c01e5120846845000341480c80442d00d40c169003000300040700002c500401c1c442c84050481843d11300c0c0d40f0440f940030000088104003007001c0c2d490341d003000c00e401e01410380074007000c210644240940381c0d028811460001d1002d240080090211341130071403a5002d110100103000 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 792163830 1250 792162580 792162589
    0x29010b03240f1c0b04030e0a0b030105030a030302031512010c0306210f1b0e0a0f0203090c1203040306052a0c0706050f04050409031d01020c01080103110409050304080102210402 78
    0x22100c0c1c4046884480c2c000c032443c0a903440090400340182916480400c000405411a0189400200c251150510765896000c02d41c05440203014142e0700d079001030740c40740001e0721980055078400c07900241e09902181d10300204003510491841510165140c1d146103c41907814424680141081e800c68480000100b020310b10450029001614544080300030000307009000d80821914500b401c41e15020503030700e6010350039420040d00c9032600c817800d24100100c400004c4c0280c074040d038100d4000c3c0c458040d00c0b0301086940c0c080320702e401c081400706100020110389503208240c4113482c00d10500c03500c8139020502d010880c60300801004c4c1000103001a0071000400100c00003525110300701259079080100389074005005070f40c000b03030344181844600c030105603110b03184076144089554030401301558807005a8584102e0b140c2d03580003901d00001080814444021001041c902410000f0040320a441b1303d421503210b608050311681d000035090b0610104d030010901503048211028149007426400907 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 792165080 1250 792163830 792163849
    0x30606010c020a0b0a0905030304030606050a0608010605180f060c010203060f010c17030c070c0b0d06050a18090609020a080d0905180a020319060801140a050f0429010b0324 76
    0x7035050b01404102c0b24062405500c6d038001400d0000c00b00c1e921155a843d01c1c5001e4407480c0601c0d409641101400070704140510040c5040e19020307142c103401d003240e082d01c26402c030310000300d40c41e070024601c058600c841d120072000b81201c410350b2001582d00e16068047c41450304003588494101f05000107080d000c618201d644284c09407801a00507501e48070540380900c40d014100c400303080a20b0003000000d10200410007042800c040000600109546400700300000b5440c0c801ca920080a0001022598007654004031000384211070024400486030042040c0c0c9049404c0129158082003ca404c0650072019810081030211f401000c90756004001c817800400c09010100056004804220031401c0d092407004000a801800c0150390f80d651803c5018003450342485941504144c0801c0c1601c28a00850b48030700183c0f10902000c1c1ca07160344807095080c0e0501101d88440740c80b041031a07510b6501d0790b91030007030020710451038880c1000462203003c0b15240c26002c0c14071014290b03203a0300303032900d0910 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 792166330 1250 792165080 792165089
    0x6030601080f090c180406050f041e0302070f0f030311120d0507020a051203160c110105030c1303030512090a0341070309210f061d0a02030606010c020a 67
    0x50b800545039031540b545841400d1040e1503004019000711000280400885c0e171085001e03a10900164a40034003900ca5031206490241c15592100c2501c1c81c1750200c1e444904495100b0320440308007540e9901e1505008040d90400a05150641001c206050f03200c06601012000e03140545a002280c00b02d007602840380c504a400060307250702c0080d04aa000784140c162940d000000d450340000c800c3c0c0c5050240c0c0c01142c440302d200042d110907142a520560741c0002051b80880452280f588500054550350001410142108001c100d292031085a80038144011342c131903100c00e9141d00d01c3e40790710481d00e000181501e01e08c0d402441c0040101390300c9011400c440165102403045044000c0d48e6081c1b170101d40e640d50041b0030505c0c50003850001c2c10710080a909019075071340f040b0640c58086524201000e080414884900c60709060046090060043e82c014801c010001c1c0520a043d0030038610f0700c81440f000c0700c1750010b29005055080c14001c941d888102460980e10707140a07540000e00e0072a89009 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 792167580 1250 792166330 792166351
    0x90c120a06141516210c030201180b181903090501020601050603040f02220e1b240c030412030804021e010f1101060305160f08071202040b03120a030605030c0603060108 74
    0x202d820305c0701159411540c2e0707080540c135148032800c40c207024000c0e42130030b24124010362a100184c4004043e2240d40880c0303a900001e60b070b0700c98441444811010303180200c4c0301c44134064802425102139040000d040e0781c0740b080e2507d00c41285080b002a0030090140d010714000d0504004100001d440502c03c005055411039050f80580500000d2000c00b00c568200041031600c0e24a00c028002400100080400341c01c0384904000c01002061201130480a108480c40c1c8114600070090952650040d1502c0081c00e001c0b41d09241d9541d40b000c0510340b5501d000e0340440d030712600344002d40c10072081807595103c00222840c10f108401c2c00003014a06121600300c20030426403d001c130301e1807003908800021600401260900c15000300031924041da103100c0c01c0d101145000d000511254045000412180b1620303d20b1010340b015000c0c80f01500103001c10903414001d00d0384181c6d40c60700ca43e010380100c030071640c0c00180380750800041c507140005c0003081503c105028020480c0580c0c3c40051554000e04084 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 792168830 1250 792167580 792167617
    0x80901081003200901050609030d0c0f020a0306050f0714160f050a030818011401031e12021c0c1e1a040506040c0504090302060402090c120a061415 65
    0x7804525180c060300020550080ca103030400c8050782c800c403025501030007264816104c0e6a11001c02115103e104009901074120341140009180500d50101c2c40d0ba005031140c040000c229800a034103031940c0c0c3c1044541e10340d40c2d818450805200044035901a08508010404d030b002c2c210320450601034903900c80201d140580d80d000030070461222100642c0e9021085604514003031401604449084a2034001c0781d00b800c0082d00d500c5c005008211042c40c1c0c1945028199085444c0c3c01c03004e180e0384071040700d0f540090381640c00081c281d20030381c0b001c00c040e0b501601d14102001407410714180a000740318100101c1040300c00100d00460035169401c00d00001c0c8111004651912080700781101e82c0d14008010038030200030900901190041c841c034410004a05402e490300e0401040b1600d0580280050340080005001402c20300e0030503810000d4a81a242003108969104c0b02a0078215040a211a2900c07010411143d00d20298039004e0700440340c5506804c144040c80742c542c018203000d40c0b1b8a0302c00ea03 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 792170080 1250 792168830 792168841
    0xf01140a02031b10051f0e0402042901022401050904110307030b060405060409030c1202031303030207030b0f130303020f1303030819021c02130806011e090908090108 73
    0x200221141d00340300ca030300d00c000f03559440d450548a568080c8031140e100c1c10712001528408454032070a0050680707403038501d40941800007640250030010400c9030015130711010940320035a04d920b003038210010004c00d0a0781421000009051102000da50309929002c40c4030401614200d5922905403402500c1900303803640c1e103082c4801c4064050205580602488501200340180c500c0e2152107402c00b55800d00c50340c0c9565080c402282c011100160000344000d4501d8000703082d40001000000c003610449041c8409060040510405648200c025900c8070508208001d0404000742d8032091078180001c040c504003002d0030900003620720003420140d0014074003010041960942d072515800c41c0d48124442d4030703454082c1980f4810381d44000c8841080401650500c1c0310f008a504112042003140500000c0400200c003030b4100f80c0714202e0703402d07440c00040391010040220394028200b5501003240c0c2c5070090740070390708820076411207142c49081c040e0000208a6040c111801140207182410155036034 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 792171330 1250 792170080 792170083
    0x507120b0f090108030406030e0d050a0e040603060c05120a0c2001020403050102130305150103150902060712020319080c03010308070519030306090c2a03110a150b0f01140a02 77
    0x8003001c540c800312080010610b40000805071041e20320a0303c040103011a101c000c50b541d61310700c0118600044d02000600c58032441507180710708880010304045019505c954445003034a1006100f440011030104043c00e04c0080e040e1901d0300944604003c1010401c044030082c14074000382003802c100c40b0008100700c180c010940c100c80c01150000021500c84020020542d0013005510040c0e50502c1440f14a584100581c05224102c030362010f04011310078031800122014240d0340c5001c2e84c1c480c1c418820782001c42d0054442d40a10000341e405195074012081d211810403c01015903800c0220300020030458205180880703054030742290506866640310b24000e40761240c1d0340c0c410303000a906030004104141e01500020241e0345044010311000f009260700300c1e44100c1c4018104040320910b01211581400700240840140c003901d0032000014186071064070b0800e1483e82113410300d1001034090361a072064880c8140c0b6081c125030740889983e500b00000c129200c4014000344240c80024210f103110b00 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 792172580 1250 792171330 792171349
    0x4080706260106180e0717090304030219031a070504090f0e010903110d05180f31050703050402091611070f08100603080a0c03020c1203090a08010507120b 68
    0x40c0c19941510b684541c030003084003481c0304941440d00c003400c1e8081415401d00890301d100b501d00c5c0d5109008018400d00c450816100a000c413078050004001c04000745e100c461040042c0e240031002d002d8440d10b03501d400c4130300300d00c0c42c0d0b00c00c103080e03551405104c402544442110700b100d140c00804112044041c20030340c01400c411140a003150b10302507007903040581110181003115903d400342c400d070b05043d16007a03540303120b0343e06d0f448002200c00c0e00c1c6020520344401c801c0c0650501606d040060801110142d080e80c904032145845c6024400500403a440319000781d992100795864148a5410a9030110791410000f6000e42c08218204840d0090343d84100e018a54140264044480c410303031340d400910049030603000b80d81c510700035100b0107400b540441c02440d04903a4040241071a10700c01e00350484240001110440440c012200589015510a44d07a00000c550400c09503640e032030761800b04010310205921061082e414102004480c0e0740125440c0c10040e015140441d04c481c403c1e000622408 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 792173830 1250 792172580 792172637
    0xe03030c22140103051006020c060d02041d04060b030c1c020f06042718020d05010b1314062e0903050604030903031b0203030307030b03100e0f0c0604080706 69
    0x101d502400140d020080d4111506000003038808010303030f4a4600303031901080303c180160702c09a400800c900c1d045081440040c6000200301500505094403094410f1110754480d6640100000c08024401030242502c00d01340050402c0b0300514040b0000404946071b100101c90b1545418100503900081d51a048540701056400414480e42e035a22200e80b03400701c80e03510310384800e00c141a1a280d074a8010074818441c0c1d0071041c4580a00c92481c9a080040c1c00b03040c4403080b40c0039529103c42401c2c948900300741c0d440340490500003096040764695281d00c0300030020082c500c2a0000c2151014602c0108842c440f080d5140445e114030441144065640d020241d20084c1244140c00400c0141a0701040d2041524400d595040fa00b00480c078000c2c1082085007c0030f90705030010008242a01c1c065031006401a1018058689001c3c404482008580c10359841807240d03041100348541d0b0070024800d180510104a80c614101410020155902c440360700400080c0100f00d8031210b000180c102017828601d = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 792175080 1250 792173830 792173887
    0x9050405061611010606081005030f1b030a0501050411010807021b0f0d15020316020304060509040f09080313120201230402010e060309010f0b06160f0c0b0c0f0f010e03030c 76
    0x280d6a4003002442c000f0120f23480095000c508501041d68a4049007602c4c096801c04010002d15083d00d00c14403000309100001c40d0b243c411742209070006030003801880d1083d4020402481d808080030000351520350010025011500518130450b60044940c101145030041070b0b1f4a9600d00a01d00c0c042402d42a5001c8050940d0425844000d9071100940044d44030b03a241d00212200c0c503046841c00c0c1d0f42d0b800b407030203810302003802404900168149940320002d02104030f0000701c4d09515130740b01d50382290b006a54100d810101c511045082c0b01d503442545441e02581d200030400070090180b400c41c6040d024083d1001e5003c6080401c0030b5a1050303840442c0c2e4280100b4003692400c00c3e944050081905026821807203045c40c01079141da103001016940200780a145007420103103039076220005000c542800b00d40a5205100124580c0346030300180c4002c8128400408020642c1e140d00c520f03101c401d018201040c0c0c18054841d41c2c00701e001c020369401400d4503040a40310f001c5900b0501300c241c22140c658000 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 792176330 1250 792175080 792175091
    0x402040b0d0b1e0102030a12020d020304050d2312190228030209180702010e030307020d08010e0c0403331b08010506370807090905040506161101 64
    0x6040d01c95101001c80301d0102c0f1503091660f0b80703511590400700c10220b01c0340540c00601c091034030180183c201e00c07200207500d44010302c0c14546108050403600180c80940d145e81c845446c941c1041d421410038000000701c2010303201c03103000c2c00346404202d00c0f500510100f10140040070071154a103040e0040c1000680c203106640320f03101540c0035000a403100300140818010020801c03021402842121601c840190607203d54044141b100c0c0710380b0340e001d0301030790840d0344e1a60314079a00041440034601400103a4050440300c1070003880101401e07170603008180c60b034140406020150800c0004c46040341d500280841c9c1050f29001348404907108e2000868048903000c0c9030040313941003075000b0503003220185058202d820400d00219030520003405555007289042014090b000741007812078011402c0a40001d118105d076220359404001c1c0c6c400380340013080b600c1c0103004c2400e4000b01448082c1100382d10811291030640c44480c0d451101070042031300e0040004040d11607520490050040a01e601e00a119 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 792177580 1250 792176330 792176347
    0x180f130f02070f2411040605070f05010515120304080c04091b0b19110706030b19080c2b030e06070f0c050906060f03010b031812120a0501150e0402040b 67
    0x44007180b08031882000f924071131400070080607521452205100800d07800d800c1ca400c001043d16154851a016a840c00e801002800068000d018240c420310100d51240307a148509001c0c400b8038600c1c0c00040e0354942041c402480990400511081545000c80340868080450b0070034010f1182c800564108aa140d01c1e00490014204c0c030040c000c1a41026800c00d04134a201411500078180d84500e4240382c1240708108002e51103038000329000000205101000b000c044100d800c1500240d12051145e0004000d00710f240c80c1414081040c0512040c2000b0f41c0720011080c1e032000c0340341903401070920014101d041000d071220400d903000d59074400890011740d815030a04070402a034503c5120f00c0340b0a100001121807d008043d00d0b6415060403400d1300350b90918582c1030064000500300d150600d40e18600b020022000c10000c846084c2a00680340e940c0c13404d8900b4a02170000600c1c4e124004d00313041c0100251400400940a0440c1380d00e050b80c0c402070354100090180c4501c0e132108074a0b44001c60f0009 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 792178830 1250 792177580 792177593
    0x605040803300708070e010804081209010b0604081c0e0d0f030201110c0319020712150f18050d0804081821070819050606090702071505180f130f02070f 67
    0x2c2c00783c01d881c1c07241e481c6c409078403004540c044011180201406c100380071200b0704580440b002c6811000701d00010034075000c0a07001c00c10903082640135032043d61100d0b04007640360703c565038141c85030341c5240b4281c2c10352801c020100d820041245001040b0748400811001414801c2d40040700200d00600c5007941d03410940481a501c0d00080c0c041d907510300c0c0743d2401d125002c1c0000750390310032503014580700d4003034030400d0f22443c2a56404c081c40800e60381e15181d9589000c44c99100c2d070700341c3d0140410640c0354410542482c03880c1c440da2880300230500c4480c44c240000310390010140c81a000400c170001d0130f003e00c4400071508149440c2d400400e0741040c42e40000401001044c0300007903a0041044411102d41026485804d01a042001d8101e40100000c02c0715410729802a80d400041401180d000c941d591060a404040401c28080080c20120741207294040a01541048110441e114a41600d000740001d143c160b4040c640e2400070f980341380114100c840d54055a607459000035024a1003003950a284 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 792180080 1250 792178830 792178847
    0x9010b04031110080601030f230f0c07050705090a090c030602032d0105040b03031e040509060f0112180c030b1605041410090806180706050408033007 66
    0x1103446802d00300500100f410440c4030741c2c48040f450390398071405840d808019801000784980040340d4a45034052401c441100c61024401c1f6080c0450480302e41c03500250010302000d0140245c06000010894100840c0d0300140c0303001030328012101841a9214850514000e109175a0000d0a03100c040b5400818084140d01843c864820300c440d6250032004001c01a00f10002c0048045844204200622482c20b0035400a0704044025040728601403034005200e101804280f0501503500002074148042d05005000d0f6400c00d80035540425198070075400070300350381e400c0601d049140f95164008081c1030900b5100b111219000542c0315802504d03400d1015600e10304859404640d01c60f241c50f2910a88103400322070803140402d03c041c1400540f2020031031055802450101006600f1001198503401130103214040c0f2107606100c10b400013006a40c0f810084103074804000c5c40b0041c4010480120080704a80c00b040c424040d0003030019030507400301d20784070512000c01816078040c0c040050080d0441c420 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 792181330 1250 792180080 792180083
    0x30507270e0705041b0c1b26010606051204060c051c0204050a06080402030703030807021005011509060f0210270f0b0a020f0412050109060c0e1315032009010b0403 72
    0x24409888080040e070b0354031114064203000681b06507a410302145481e2860340c48107880e6020f001c402a03a1303080b40c0b055a00c011040d906200940099040030300e009109040081189041060502e4190f280310000510000c01c05172035a6159940701c00b40310700c40c200315050000004983c0710b03030b0000c4100c0207009420034050180680d80e00840800c1ca0b41c0a140880d01c201d038010010700d8150704568080740e03c1c503006818079096128041e0f50050103601800383c81d000e41700d42142a20390591665005000792070a511020a10440350310004400d03a0110703c68041c00703090307040800c1030840000c115403140315507085071034621903801e8681c0401c60b1104003400f0060061224184a80b21222580200d03c1503001c8841c0e82002000204000000504481215401080001340e031841e40c3d242c44060b07806680e0000c0024150804282042c034001c60701c1440910003a00410486115522200164510303010103044202c80d4105240d015080060715520804054848107155940c3c100c5c015664005000 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 792182580 1250 792181330 792181339
    0xa2a030b061c051f0b2407030306050402030a02070302010b1009091d010903090f15080a110c060f180a0224070606080619020703080103030e03030d050c0c0601060801030507270e0705 80
    0x41a40d0b0703520b4280e03101c20301b0142800a548104041c0050006039500140b022414107858190000700e955551015520032502c00001590702d0009180003421244024040742c812079a4000b00c1841c11361210782d1400b551806240043c040c1002112584203402c0081c40c2d40711383d8241100030040603800040007040300e155032100c01c9250f40710005e188519500c003d502c800100150b001440b0f0842036003100032114100300b0958942105078071424100002140c4182c0f840e0321000c10300c641d1440d1901046d078404000001703000030211a50000c1c900c0e98000385050201c1e088407501c03242e011039280840c0d0021707034070100821510b5500d801031601d9060480d1022541088000c1424110084c0e008030b950700d50381965402e00300d80c00e55070141c4030800010803598162000b40545e100d51421845118001d942d0100000d440c4d07111580c0c0749240500503000b51742000700c440010000600005035144c2952180d64812035001510501c000f41d500c0da218103e43c685080c0150f04110040120f80d0100b60341c1d041d03c = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 792183830 1250 792182580 792182591
    0x10e030303090a1b12060506030607031a0f040b060c010902010f09080c1201021e04210b131b06080906010b0315040209120a2a030b061c051f 62
    0x80588034041140d25079200c0d008403105000240504c030030041542240b50360062907945410182410700c112a03811203859a440381404840e00e070800040ea80203115260600142c0e12451408450b01882c08280c0c0c0191041c85403154030342c0c0c485e00a139068110140181e070710380e800c00d2710050280182030400d0703012800b50889000968030030b440f40b0f0140c64050b002031260607074010a1122011003900e02c416155424005001c0c0144491103250448a0300e648094446003001701c120300000b20500e40c00303107441415038540c002451275003003940e004101485a911902c81800d152a010a4481404241d804a85c00c042540da801c408424041d0b60b40c0022101031703a0302e85421010510007642c80d01181001520040300328a05600180307031198001d001c9516200034240b05500e030000629049448603c0144007180507503540358019035140383c154039550420724507140d1040c0c21382c028000e140500411810b0501c207000420306240510703880012124616408140341034214511407200ca403140c2401d = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 792185080 1250 792183830 792183857
    0xa0605041802010f0c0204020a030f1109011e03020906190e04090b13080c4c0f021b030310080718021b0f0304030606090c12050903220501 61
    0x203100301448041e8000c050300e01d09816400540d00603145500302d90070019a803401d40016180c0e8009040d660718281c802084d08901021104142c3d011b110090480d46410b01c4400b038a40e9000e411145000010109881d100c0381401c0c0450291085214081d00107500190b80c481c03a800c0c520300040b24480359590101c9541d4154108401d482c000c4002802c118034560104200141c0030010101b01882107008a16209801d842d0500b082c8141c030542400190703023140b41c080c1e46d403195543c02a16040104074101000d5a02c0b02501060407c403214001d283e0324013022000d52540c0d03046038080c8402c4400c500d0021004141d0301d55030f070b004641a4005402c100c00004046c0ca000420700305441d903078a80100c0b50034010702210002d4102c083c1051604113001c2c3c8084458101b80301c07007104110f103100510760799821404d252082d640558030840060740303440408803995610600481c11040300340c00214a94940d0005245140207451a100c04650542054220303010584079003401c42d0800e80307804072151881c = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 792186330 1250 792185080 792185089
    0x9070f140f190503100b0a030e01050a1b2309040207050604050a15020703230403020a0e070906090e150301060506040f09110913020c070e070215220f02040209090c030a0605 76
    0x5d45809442020b40081800392000c00c001505001003507103000502c05591509060070b440d000da90b2244a50740d580003400c124032040b824102d240e281070400d00009103040c6200c107800d01c00d2074920303166410702082100e0703169115012190038503080700444820b41000e0501545507038000e041140c0f40d88404500c992807a0160080d0f8502c4c1c0d425440704c402d034183e6140c8580d4514006403040e03a40c00400c00022005a8900702e0b07020250071580d80c001494581100d0190078103a103a0000014044140d030304110034002d02c3c100c9076103d1581991004500414404240544007907044264000404640421203019070241201103401c0203106000031240790030414501e02c030710020310780c2111500e4000c122a89450b001441c40c00d5000d0100c4140c0382c1e0724000c03009207a2045d04c2000050b0090311803034040b07440404a081e007011200c034840c0c0030351021071140c5079603100380400280720668960590003550f807160305540485201411055051411b0407102c8140e502c1180c1001c0303124a800741c0840c1c103090 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 792187580 1250 792186330 792186337
    0xc0f0304110a1e0b030c0d060f030b09060f0c13030c06110c0406060203030112080d0603060227011e020709020a0f020d0206040f0611070f0804091a09070f140f1905 72
    0x45003411150302410442c00344d00301c0d8802040754410b52030401000c240f980e124400d44004080000d000c01030356081d0f11341401d01d1a4003410141c2242d200000340400102400005504011501441c42d84d424408180c824800706540c806841c000c0035030b40000f419a000302003406080e01ca001900c2d050542d040800044030124012400140e01c00e2005204180a5a030700c0e441c240c0c050302060b030801769498140c0c1c0540300c03030380c1017115499000b0580603102061500020501c2c0c02e80c0481c070914205440c0020101d200284007003945400000c1d50408543c0240b041a0103400c88000c1035640780500c460280a070001034800714014442c00350381c0e240452001c560180582e6100270409441c8403681c4400f4007030027605194481e154002c02011000403601e0141400b41c0380300c2d03140315489a16281d11941262008011a40e00070000c0314030008664844456942c40840360401c074158045108044a002601459407118000001092600d00b4035410207420500e40440c0c0c05000e908c0f000c80e04543e20701 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 792188830 1250 792187580 792187619
    0x30f0d0f0203070b060f120a080d050a0b101206080111070506091501060c03030b031e07050d081b0c19091a0d0b19230106080403090e0c0f0304110a 65
    0x4c03010004541c0510f42440e2590004800421048081ca0503001b85414202c22070707401c07140954006109a204440c600980d0303442050b80f0070400a00c1491400715441c0680d01c0c0c010003c00611414820b414900c0341e00c048081c0140d0b00003000b440001003403c1c81c4650003440c0c150390520414002650301400010903111071071840b41e0f0171445900c5c1c60420749024000321000c50a16888805005084d1405c001c1d4800c40f102018400795400003240c005d6040042c01d42041d8080c170011f20010380400d004c0c2003210002c8070607409081181c0300e00c3c921181001d900030141a4010f003829442002810220a1007081e190188000c06c080b0021040b0101c103071f001d8160894010118040300b002003009908800d40c06000c40303003044a123040c03c000c0d00044825011801014075160526a009480c0b00d608a42c0942103505060344181800d0310087d080101d1486201d000c07140b404009288144807001742e442c0c1c0c8014840d81c030344a003020326004080c40d002c00b17680c5d030140c00d000030b000600000d06407600701c001 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 792190080 1250 792188830 792188843
    0x151303230d0c020a0b0f0910030501051c020d020301020f0c0715210b0918070e010e1f0e0414010b09070816090f0905010e0a090b010b07020f030f0d0f020307 69
    0x35454103015030360782c0070014060760f200f42d4038000090000081002001000000f0316520359650900d02044606030351928000c00301880c100040c010703030b2030304200f4031818000140913515900e0b1910014022110544009416500102e0180d0a00300c1c420050246450200280c0304c148e80c03580780d5443c2c41140d908803100042c1c04004030650351103101c075085002008401020a514080502281000209a40503429203202c041c035403683e22428042c2e003010f044402c440060551410403c0c2c0e000c04c00150080e003070021080e4040e01074405610345100182442100316602d880c01d410888945e40b2204d070403003042d50804401555a150440f030881c4140c0d080e440b00e240384e4035a09044559503006001c000207000f01c4460104840250f0000e1000400e203c04000c516507042c40f8583d45c203420043c1418492030300340665000020f4014940b1030541c0c142240b0540c4495250002900112002181035090b0184201a40d0aa41c010526401c40c49864a03400d40e141c11b4424101d980c0d220b40400500f41 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 792191330 1250 792190080 792190093
    0x5040e1e0a03020d0c03020109020a030809031513021210060b0301090507111002031f0e01080f2a0406050402030901060609060e06090405060a17013c0b15130323 71
    0x245003e100103034105c600038400001c0f4049194007190b032010003a0000e4650440102d000709007464200800c0c128040d0f030068901e041d0411290b4416840700f141c0c0700038410208540c0d003400c885803c020920302c03500e22040511a20340c2c2c40c1103180f91a0300038010360306100d0a0200041c41c8074050700300b040c00302d10403d000b41055810888120001c0d08080c0c541a03083d81c80b11103080c1310510302c0d1054030240c000302036000c085500d442d00291401741c00340c1001c2c4440c0c0141d42560801c1441c1015548208000956081060904070010300242055000b17254458804002c1c8012000154085810b491040c0c5440d94031f56103c1e00141c40c15078040b82003a9005004000c0d100141c1082c0c0c0140340c00074400313009802a1510344004604400440c41c04111b00d82d5580e200c0d40a9420b44040000010300c240c29840e01000d10710501003021400b1105034201d80e898000009040d2034144500c80c0c04c18007480615140c024000390340d00c490401e484150340740010341c48800d01d080400b814040e00c10040c20000d000c07 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 792192580 1250 792191330 792191353
    0x901020606150415030e010b01020a120c03020c100f02061018020c030c0d050a032336010f0b0f0609010f05120a2c030f0d0605040e1e0a0302 62
    0x205482800c002e880388401c107210004001c41c8403803691903446a1900c000c102c0034000c0103014216009004540d0440d030180d02d01001051100822480e80000d5107040c01503440c070fa0400340d1070301811590705a045020190a6040e103540700409000c01c1d4119030a841d0252281d490802c80051180134844030614022250380c8081c071558018058440030078281c9050042441947d800c2c03c44100c1782c0c2e400328034000303207100c03402d03601d0300c20040d00712100100307445002080c182814040c1c0000344250710380803a544200c03042d8040d840502050006441508100218044029010700f09103003c501c0c444c0d04003442c0c5201460403004000c02c148000e0078a0742400e841c10011206010346016030300c144402004145004105500344500c0707614a8140862a00405511003c1500b10b02140042c40d1014070031a0010f12000300440e40c10019007501c030703a190783d018007040c0002e19050b4009940549040c500740c2c00c035500070030590180800946100c0030018600310306c0e0f881c0c12200d800140180c000460300c00 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 792193830 1250 792192580 792192589
    0x6060607020a03081b060703050115030203040302160306020a030c0e100813081909090c0e1905090109050601110a050c0d08070f030c050613110f010302220302010f050901020606 78
    0x1100600003002044101c1d540d8480d1340690b8000991190030720103a40036152104020410140c2002161808000340c6d80b40c0341071404402000b4000c40201030f00000440c05240c0300300311a8040c200d8a141040d001e03542c80c40c0880083d800b154511000c241001400c08006025040c224480000078108440b00c18900030205c03080000184020111501c160321030f008a030354100641500c200030a1000324100038248007030a100c22960101c4126801e02c44007885060f40508030040c202c01c00e4030b000c10410010b0904c0400748403039400098004042c034000041d12152030700028050380b4282c980089240030301c8412611040003020180c04c81d4450410f052160418404442d800c46c007c021180c01c01641d69100003c0c48071108042d00000c4c02400d800c010720500748903481d0804c2030b090644508030380d181d550030300c40c861414900b072099010702a0180264041d80481d0124081d04408004103541251102c504c4a0107000c140c1c00240c24601504481d03014008a640303c0405030014442a0b6511007080b = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 792195080 1250 792193830 792193837
    0x71103040b030912030106020a0618033c080f0c030f040b0604060f090207050c120a030e130507080114031506041503060c020c0114040b1902030c070303080f0906010602060606 77
    0x4102901c070710b204020300320113030501031030103020700b0b5003d40461840c50400e1025a0142401c04c0c4250f491190500c000a400c0182c041580c00000c85803100511103d2002c1c0f07016405802c050300362041908010369103540013002c54032500c3c0c0203400e06019140d5820300700d0280030803100e0a04501d07548021401240e03031503070300e1a8403038801400828007540307911161403000d00e160301040782d464020810301d04010f4148032851001c40d091300c9441090259102107640c40c4007040d009030174004e0304a4918000e032904002c420605200082c02d0103241082c0d400103040500902c644801d11955011040388bd00d00803c03001e444d480a45158002070710f41504000044c00e4000a4001c7c1159904001000402c5805122111641030700640200700e1010000f600001c9a940c2c20804080100018011070340360506403030400b8012086140d0017041d01505030700d14807880860441381d01c01c000300001090361014a442c4a550340107200e06258480398141a5654420700a14000d0307000300f00010070608104015 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 792196330 1250 792195080 792195091
    0x19020d020d0c051c14011b030b06040b131712030402091801110301060f1b030810170304030317060a0308030606070803190e061b0d020d23071103040b03 67
    0x810b42c107030f64820005041c104103030603c1640300714425480c024070860070a000b005500b044000c1c003480c402e002c0e4041c0d00301614842a014569034010302c181d07d07251074007913401806004000a82d10000c3e0049010108040c1c480c03040300b021034001c1403c29032000705406111109003045981180c41da5400c201d402c0400030190b924034542401200e0880740c09016501d41401c0b0720445a5595040c4800103000148003443c3c3c1083c400001e4000e20407500e1142c1741c0908513054540359203980c6619a00c1004080b00743c0c001205c100d00690301802645003c4014821284252a070007044514502d22080a14044070801d5000c0c0007500100045a031b02ca005542c0500b00801c3c9600d0090a82e45800640d0400d0f509100b070781c155400d190740f11607203c3c07103504110000340c8001c00481c43c15800a000c2040c0040c07123417044100108009461707040c5ca4050f940f5031080c92205000c0b6420303424a40c401106d418429501d41a054404103481c0e50144403ca10b40d9020100610302d40341c04c00c0c0e2544019031002c0e04 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 792197580 1250 792196330 792196343
    0x100612110f01171302010f020d02120c031b0303091501030210200106030b190e031801030b0a0b0a090e0118090c030204060f2c2d011719020d020d 64
    0x414010040c0f018078041c07103000c07a90b440d061014294000100903171140c46046040d540200c01c2824810740010380e082071900d1308041e01c0d03070f5080346010650460107240307103042e44910801c005d05500300020028512030320f031000031204d5018090b03020550440080c40003a4001e007000448204c042d02c01c09415a44030184240c2d49603006214040c2821681198020307152481c804007440341c0305641c5c0c140a004015114403c1c8580c0e000c0e0b4400e552a0300c0380010301c0f00d030210000210303100e590103a04140e041c220001d02d0b00790303100d0761005403504550045010900041e45103030301195540d18400414181d0f0480c140d12401548594401f038010003004a082c0d418001c0c203880000180c3d524050381024141400a6034109840d04040782c00f10090781608044000141c00200074040c080c80e180b0747e02003141034101001c00c0450515280d82421020810074008030400003240d0000d50146017410114894200c807507120341c2254030b40840756054002540200440e2524015207819a841d610160007860f = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 792198830 1250 792197580 792197597
    0x5040902092b0b06060c031614011104060315142803030201062408061020010c09060503100306050c0c010c020d120b011709031605100612110f01 64
    0x601c11940c00724159624041d11518070403982000b44005809030031210a8601c54204050346a401f41c0340d00800045050200d81061003506125038002c42d00b52980c80c10b00204100b0003585004501c40e4043e004501c0864205110610040c40c4007070000d044820144282030b00303402a100300920600c14a86003140e020320703014880005000b5800c3d80e401144030b0b80000440510789240988002c001c0c0c0407441d0075581d400c600f0705034250040345490784404111503084402701c40900640d80007149800414120010349448403007480154400014072010382c58501590356105c60854482c4000c840403074050160440c00c10028050b82c000d650000e40c12240c040c105691180280c1c03c5a0810300110300503840000c0000302d59030007511039070b108011014140410000c0b800080c0c210b4802080080d0000f04070300002c1d01d22070f003d209480b140c0308075100414001ca6030742400c99889070418410b51005c0d15000340007a6410907015190341c4141c1c07140c421860030610108021910038030000b810306022450 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 792200080 1250 792198830 792198859
    0x100e090f03040f030203060606040305060426070605010609051e0d06110c030a0e0411090108043906030e0d050706060f09020c0706031107080304051203130b09010b010504090209 78
    0x28000340029081c442a02c0d0011413444c0101480c0034400b40800e8042d00c000c20041c0081840070900c507521a40010310700d000c4010500e0a40603c00b07000c64901291040071441c43c003000200e40009040b0b0b107140c1d0383c2940c4251160200040710b2009403802c0c0269003410115801820301801120f40940101ca0001d182d8018096134a41c13540b2007004211a030b000000c6010070240c00c850300301040360040da003c02283d40701d00c1201290b8451400640d061014a50005040214003125411081c089100f4410006c01400c0e512030030340c40c54083e4012503211408040740b21807092241c0c50140b40103000400b0302c081c0c1c0031401e994507400380382c7c15508941c5076100030404040c1a0704010081442a000503501d9214032509801c000c1c960300400101404c0290400d8616615402d1744c4003a43c0041c03141e50391307071524035005191004900c40e408003160040100714243d000a02a50016030040c03a1004456940206042c202e800c1840c0c0e00380419401d000512030f031031103a8081c081001000d800c541c2c504c52034 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 792201330 1250 792200080 792200083
    0x83f04170c0706080a0c05030402012001020a0203180d05150403030f060e091c090902090d0609080a081006091214072301020307110f1305040f1208100e090f 69
    0x90841d9400300d42c000501040400c0d07000c5112940615540001c000c50305000b4401001c03840050006410000c400d0300c0c1c0100043c044030003064144c2000002c40d40ca401800019450f030300310089150a1155800c840221400c1c080c1d102469194000042d200c080c503813038100743d13840300041c0064041584c2c90155500d4180c142c4610b03005040000800126072620703114a034613044054420000e80d1100c440702e03450540d006032800e0300b9a20784080c0944c50380022000301d020001c00d4000541003d00b0405100248181503004000e54181c42d9a0300c030841e030301c03800407684003074051050f10000785004e0380c00c01407180fa8030400c0c203800f403043d0855036031941d441c030242d481c24805070003800c42c4500b18080c0c140450208115070311206420f00145007030000c5074417082c81e81403400b01064055482a0800f040c556550f0039240b468452400e002c0003142043d0410b0325801c020b0001c200c130205240d2603150542402500700710b01c40c0c042c0510103120f040c01d00e101c1042019015014a04a01c81d040c14002415030 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 792202580 1250 792201330 792201337
    0x50306040b0915070c0c05180c0c0102070203030d02040f0b0a050403080306012709051e062b0309030c091118271006050309070b0703050412083f0417 66
    0x215540c07140810740385c80c2003050302003d4a910035486004155034101c0500c900003040f56006008243c003d03213800b88517940c1c60180c4900400203505002c0001c0c0b941a80c1000d0303003d0400e03903401000f400d4500307480729038109040c46502e280e10702045081c001000000d41c14001154000700600d083c1c0b41550312078020013440f50300400004051a0380780014011042d00e0b110f1030fa801906001510310450f81c040d00030500c001e026100e1405800480d002181d000081150400c00d10940102101600c015081c000c21259141c00201c0b018041c1540010750707041c15010300c074200d020b030140c000d184c0a03041c10b00340400001c000803240c101c909020341d440d06a0091120401c2c0400c0652036040d64544420351030031255094001005100003807060092580c07001400006403000413060655035211070409850790300440d400100700c80e803508852020445074101a0011850780c0b5259048070758052045d5139002040700c0a180c0d0360095408411221860180c2e084e0020f0040d15400310000c840a02c0344820b0b130 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 792203830 1250 792202580 792202591
    0xe04020706020946080607020304231c050c09090318090103031b06060e0a02070510330b0c070e010e13060b0102031620010306050306040b0915 63
    0xe602103001c00d05820011355141d0500401408a8085112161090071a807205208022103101d198690503180c2d039040d40d80d4010341028000c40c2c03014500141c00a5880e030060141242203030304460711151b05001902e0f00e4900c2c600042c04040740c803000708542c01c01c4001c0d08400741c40e588030b0740c41061016114242101d0181c440d18000d1640c4419615100070f1201e0308490f598018003808004101103035100005c82450000d4584d04400884241424405483d494005c114004c0111041c003100500640c014400f0b00e2081c01540c0611034000c5400c1c08441c080050009400705880308606000a45c014030340d4032a1003510115040c0340c40300100c49464000140c044010b074840c2c04180600e00c5071307006003401403054540c112074601d800c0d0781e80b000f551020f900081045441d00d00540e031980c0240300751040454041d20201d00402c0c2401e01a5107a40c20034809490511400285085540310b40154419508042c0091000d0b44440e42d403207401c00340080c808011b034040c0468042041403035521840c0120b = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 792205080 1250 792203830 792203843
    0x40317091f092c040602030c070b0c12091b04020a090306050406020903210f070f05060a14100308180d020603091f180308182401050d051b010e040207 66
    0xd003400d00c02003500c060b9459643d2940d442c5860480740c2c0f04002c034180d034010ba000b2030140c0c407a11554076594280c080c0d40300003051b4545d00c5c0b00b0000515a540b015260000c02ca904440660311080040e58441010000d4203030058081444400c4508080d0002c1880746a207250020307070030b503498494130110341c419a01202c08540000e0613800c2e91030208215803060010380010851140803c88041c0c880c420340760500001c0390302107007407020b1102a4041006058011003070322036900d082d8101c1d030000c3c21900ca080c0c0e10000803a01140201984e60f03d88420f89920400e0646050580001c07020480000c920041d031000700d105031400147c4070000590300800d42000185985012402001800c000341c440e08c00205141c40700c200300880c000800c803000c03035400d800c0546860301c0342c8100c9010312a028141e001c0b14030a801c0100f24042604d110320f280411100010f074410398852040090035080e00002510682c000320004040b140c4038200032a15140504041000d20b4401010409903000000d055440 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 792206330 1250 792205080 792205097
    0x10e0708010b0909060703150308160303050106110d050309010612030f022a040f1119030e030909181006153009140a050a0314040317091f 61
    0x1441424082c201e8100011079244802d031038414800d90341c4100c020810710426441d0102c18035040e1404d04840051a00140c905a0301d491b40c0011042718600c61a088000a00d484000646a0f1045004104800d00440a072030307000700030501191070f41c101a145402655a0305000654136061b00c400001d034900c01d807607070500724001120181c1000240e00d8203081c100e05c020800c0c02c205400075002561070070119070005280c140809400300400b0444c0400083d5400011003c102003000106088100e040755030512024840400c1c2907107034018000c10b00d800c80701341808100c5c00750365200c2802c0da01194204403034003103c500500c0412b44419500040d962520a40d03100c22441c0e000c2d45a103030076440603801030381c2d16078194200000d400170191814030880da01e00b18075003040f007000ea000c0c0321880e240003101c002e00c1c0300d420700702c1d114128a413049021440c0040c0003d0760b415101c058408030798020070002c0350400704007800300d070580c0102c80d2594090b00401c0003200c2da041131207500b8100f0250342d40341b500 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 792207580 1250 792206330 792206339
    0x3011203020f0a140d03150302040c0c05010f050105030f0109021f02120304080d05010803180f01030b0405010e010509061002250305010507200a0503030a390e090f06010e03030c010e07 81
    0xd01032828612406c0600703001188200f100109040d0007140c3d4181d42c0054000e1017600c04036840c44c043c030001016075082081c143c01042041c5c02c90780c161075049082e0f0b004040b440c0416130807203410302070084d00100951103810a40c0b0382c3c0c10302030100d11480c4c011f8469400c11214503243d9a8000c59049509a0300442c00c5401c4007601c0c407c142c05410510000d51412810b42241c036004102490028071607540641c01400c00d911036007107410841d030007420500155031105000c420708a804d002e01d0340603122000000c0c042e854042d021255912482e000b5051200d1501c0300c03401da0540504240900c5109110300200080c800d11550384034400f02d5403003c031000041d1425008025017823500d540d00f41d00450b02400401c0c80442146d0b000003030041c00103038039a1803410131300500b203500b40c00c00100403c00c800000c006c0f0703a4101c0c01c401e10341c01e03599858589041c0403c000d80040c00b51ba9a0f0349460384030000034015400f44070301490360b4034000d040b13038101144201d01ca400d4030380c0640e02000e140c112842c100f1 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 792208830 1250 792207580 792207583
    0x2f030a020c12071a07050318030409060305010219090501050301090e03070b1501140a210f0204080a050c011704030806150d06080c18060d031106270604030503011203020f0a14 77
    0x1d0740b481e040340e404e00b01c41c1080480100180409001c040e13035581c181d030311044070040c02c00440740109083e083c140217456507401c006000390841c8401e44031118403c0d505080d080e12501000013541c0058503501e007180d0134002d0081c0104140e40c01940a440208942004580c1c01070a003031081250f0201d41c401c4800d400001407610240002c103028029061110710420760f003010300340c0f03001000c420101100c904080d45c89806081d9000003145103600c0040d001ca0001400b00c1d803551072901607001c55810f418a640115008003100c0e50b40407034240c01c000498000703441201c1c807540200005220010842c5480075965a540c00308450400c650355601c8c003080f00b81c005000007981c2e03941c11140b5110305022000000441da400424242c03044e0454001c40040601a400c0e50350380e143c8d408129800d624000005114400c2014424000c42c030049034948210071000580382e105941c1559514156443c11726000052041c0c8038085080d4024281e042c00c0c140020801401154080d61428500000780036006 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 792210080 1250 792208830 792208853
    0x806040b06030114010513020a0201060b1306140c1902010c0c26060f1f0806160306050402090307061d0301020d050a1104060816051b0f012f030a020c1207 68
    0x203003413440c45500410003960341106001c42e1003198100581d65039020201240101000c1e00409110500440c9203004545e0114001c01543c0c0b4940740c4440180500481d01c1c0ea0340204030001da056845903843c4035080d00b1881030024402c0c03042c103101804000c0d9a0b2000710314240d580003030503940a8003002c11200112008180429001080a0019400c1407846c20302e4820004001d690342c810307960003c83c00903030118065401840c03400f080c0c90150501030030a4510300750141007035001038180100030405d842c0c50700c22541a180010010310540d4078050003519941c075040c0354111006006032600c86c0b075450a0008040304600520006803c0c80c00d03064000460307070040e0340414101c1080c0001d2155a4100c000d07280c10181411021006003001c41085074035100d2012041010328541040c00003443c4001503240c04000da82c2c00034400715400caa502e2650313422046480345440307420701c080034000710100300440e084203021002502c0c1018158156107442e1440e603400740c500a0004400b424040060f191 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 792211330 1250 792210080 792210101
    0x12010e011a0609120703081c060f24030f0204060809010606030204050a090f020d1404120201020307050a052a0303040b13020f040f14010b0409060803040510180806040b060301 77
    0x18120180d001c0c00415010f00070071100340e01850f5243c0d032032020704404122040c000c540c40031483d0398179580c10350b211011010321a1200c0d41d842c00e0602c003141d644007200082003a90010103200d40940403510f02d81d040c66408244550905903200d80001160a0600040020b8030964440080c3d5003484502c3e03600f101c100758480030406206000600840d52102d000c0c0040b1068640086001c0041d0300b2608001e01c10042c01b100130710b14110303e400b1101406120740d441a0b014449400c10700031040c0f000d9082c1d100c1201c00300000b94080043c03ca07803e001320301901520f02c0001602445070509105c10052011034031130000d0391307400032040000300241c10310041e070300c0a03c1c010040c003a1262540895403e401c200d10503449551108800102e54801341d0184510001c4140701c0182942c0d0750305e204010382d105001c1c02900508002010a00d403600008441c112500a052900da00300038442c115080d005040300d40e008444401000600c6000401c18076014070302490014070541030010070503003107604d074049 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 792212580 1250 792211330 792211361
    0x1a011e05030a03051b033a09110d080d0e070e0c04050a03150b130b010e0607052814010507091202090109021b070902030405010510030c1e0512010e01 66
    0x119000040c0d48403003520b44803074070040c0c5c01844000b040c603101e04501440041d9540e08011600d40c90902e07412000c4c100000b507040c01c044100c0000c040c1c8080c10795800603409000089100074030340403810542c1988c10304a0281440c1404d0607036403007254054074070745020b4096580c0420390510a87c018024025008031400301814905031a140105148481911010304040780100203d82c2032541c0303030414441094014100640c03407000c04002e40081c4407004000d0300041d0701d401c020300c0a040403000c48040640040c0184201d03100c1100c41d80100c441c0e283c1d50141e06c1010381041000500004000e4181e102540000c6400e1411041c02480940030b54040e002c0c40c810505000d0150710350442c0e09042d076080300c1d005a0f8a21410101c051100c001801c02c0c100d91089420000314419680e020b5401244144000d11a40d29802c40c80d08441c2203500010f003007500c1ca42c00c01c1108881043d0f00c90444068000320454160361500000c0708010440711001c0035945404440444001c00c0c4a0100443c9440d0b0 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 792213830 1250 792212580 792212593
    0x20f010e1006060c1a0c0d0903020f1014060d080705030d1b0f080708040201270306050a050c18040b101e03020a09030f0204180812010f211a011e0503 66
    0x100e81c8000305d10000d200944020080c00450101c880d4a0700b00c54040c1c41140007800b1803075140c9002580e40720903600040d01070064606502c0421f5041c01f950800b00c042051100c03003501ca423000c016010342c9505080f141d04c5000c10038000060014009403075854103148002079000981c11010382c18130400050b44e4200a00e00e03140302c02e80c54000c5010b42e0480c00c4c80c45d1900003940ca80c401a40c00300900070501c41d10030745004240c12010488506002607902c20a401d11241d124040041c2c1501e40944440055107010f00c1030451881035031010070044500200049030760380f4098042040400700341901c000060306051a807410b00c1c5c42c61000d01e04103400c0c0c40c1c214135000c045ea200904441e22404020540b00304c00000e8010356a0740c0d0071840c1d14401585040c0e1130400d05190103040399101c0d821411264040070000130f00b1000c0c0382d40360000c0b1003525400f05080e5004400400306503240000440d000004044501c40340d89a40c2da44a018004100b00440980c1f085602c01030fa00a00364400c0e0301c41d03800342 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 792215080 1250 792213830 792213833
    0xf160f0c180c0c030f180b041a0a0e1e0406030b0601020c092811030a02030121020102070612020d050f270a0209040c0b0f070c09020703091401020f010e1006060c 71
    0x70030000500340d09841c0051017a401984100c0340300032600e500c0e140c0c003080100e0116850603014000c104944080040c40254844002c01042600401480382c01150301c501004041c2d0500602d81c0c0c3c10200700000302406000c4000000c0d00b1200b46800c25101103048600f0014156010400c04e000b140d411207501d100c51811403031110400c00d000341ca40200458072103080390b0803d80743c0c006082c00120b0848071501c03844c00300c0100c002904240f046100c20b82881d00303003603640142000c43d50126034041e80508043d60415400340c61031300c544083c0e02c43e981c0c0c0c01c002c072404011340307845518080c0052100c600d8403070038018000f03243c48039060188041801140c01d0341c03620a0001414003441a415514501075664608101c0d50801903075000c1b0010035000140800789080500040401500c50b04405c1c01c001e443d040f0f6038080b070048580003000b141e0208000d0082e0040035128814085051044400712a00b1b203288034251140c0140b8480300f503000500c042400415802102c015080030700d080400c07030050703 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 792216330 1250 792215080 792215087
    0xf0504180b04180b0604020c0c0607110306010e010b0d02090a08010c03060f1d1501022406011404050d0f0c051903060525032307050720060f160f0c180c 67
    0x50101752049600082079103204006001202901c1002010540c403902141480f0502c0c0050b6003103140b190280d68000b240404456003464103981c4481c24240c109081490500c0081d84401c022550284e82801c000481c44002d0040352640301c800d66010071490319020010080d600d541c2c001000d03942285480340c00d00e0481e5550103a00c26016000b00c2d4555512000507403d050000700300e80b002104910420340340107560240030b4020030081e40c4082c40c1c068441d24101090065014803580840c264901c540400d50300400c0c01b8444d402690a116550758036000982c21481d140c4005116940300316041090200350f01c20640c0c040d200b0004d8190582142c020051a00d146643c44018540d450240c005d2200055072210304040c00c40b62070100f1800d14100180c0503400010007156030b4618040e81d402e4006042c0000c40c558040a060b0074288426800c01d000d90b900440505025a84c50702c1c0d040d00800c1c001c2070300e48013941c01040406c0c501810501010a00140d0044900d505800c0501c0d56000c00d40c0f = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 792217580 1250 792216330 792216353
    0xf0706050907180c0f051e0f0405091014010314010e060a08030a18140a27051302041d030412110a030c1505030606070b040201020a0f060c0f18060f0504180b0418 71
    0x59600f02032380c07110b004c044020503021703c0d0815034005255008114a07103000d0100344082e510580b2114031032146010044098503803a50303030b100b84a5414801007014011103641d4030303042480181414802368460755100c0c51a048600c00b800040c030303188600f50381c00c8000c1030b461015180d4403201c00e2000060102150a46002c0e2007450001d0b49504501d0841c5040c030a0000541c00714804144010700344640715520281000c402684a0b030b242ca0300c0c0201311241c100314200390541c08005181018070340488007400c030941c1c6006590500b08203c0c00d03156070f03a0301800280510b21031040310342c90760300301460741440740c008080240a00c8001c106001260b580c51080c1d4058690003800d6610a82d55840100d00b44110341c0d10040140540c8c4440100b08050b81e00222810f03041ea03070b01c0e0500c0c44079000049485000759281040030071100c502c180005031069012201d03250850030414a050f550f0f048486281000150088101d66a48000701941c905070140200c9481e819240d20b104208940310009a4403 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 792218830 1250 792217580 792217627
    0x201b0a091b0f120c120b0409020108040803060301020702030a080d11181011030d0e010b0103020f03150d0f0f0303060b0405060d0e2a030f030f0706050907180c0f05 72
    0xc1040300d00c0040b44103010f041007103003040c14107010391244020090100407114803541300490400c49000e40078105031142000b4160140d55004160b01c454981c06425032010307209a070107540800031000542c03410041c1110242c422a00669a00c0d002c1c9120030440b040c1d02415a08803000b040801c41814100c405141408022524101c40040010b07040e100c1c1900d2423601c8400d4080807950603480078059010441004070380c0024084200450011022889010000e8248203030a1011860544142c2e440e076a21103000f808424107100c05031103c500030407070400c0c02c640c5212101625020113516006440082462540040c186420100025042d00940d4501040c0c00d40d1900d10844103141003001c81d03010050300c55102d0f11034018072032000703000e0003041055002e885150f12408010320300000319080804c00d00742d503904001095444102038103001d402585244900341e40402c4200350b05001c80031140003140b001681c82e01c8900050a0f581240404c44244201404030a101010360906021040c = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 792220080 1250 792218830 792218837
    0x3050c040f06050c1e0a29190b0a051011030f040806041a040f02060c1606020102070201080c0301240e0312041e0b030a110715050906100b0406201b0a091b 68
    0xc400b28580c002024200c1d0740110f2250a0704020b00104005c01180302c0308c0680600d05c14444111103006003c81e40d070030782c401e0340d40040e03012080141283c8510310403e29138000303000342ca20f410700c481146c13110b980154100c14030035001102031108101000c1c048204001a444082c440c600c0c00c0d03202d15030100071591000c1d0256000140d504045081400030002141c103815184000f25100d0b0740c028001e42020302c040340801c0d2203901081e0601102030580e4100e130b1140c17621010030640c4d900894440da814600301014082490100165590240400c95004503101c202e140c40c1d030f107488140c2c030f40d0310482005d0140f080d0034040140114002c90f02200d6009074001c9010803540001e500307030000c0b48540000609822812003840c004007095420160295066034100c0d4115203c0c4000141030f000c99100d40c0f05c00c103208000400040b4080ca1003c50410400c14550890f013a48100d414100354580011095508548282e401c0c00e00c5d2054004019080550b410002c0d0400d00184800b413440d0824001c090 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 792221330 1250 792220080 792220103
    0x60f180e0a12020c0405010e01090617030f0f04080303070c0b0c031e1012050313061d090606041e03030909020901050d050402060910030b0108060f0d0303050c040f06050c1e0a 77
    0x443d0082044a80342900074100700030569603440c010032131400038010f200345181051000202c10701400c150103600c02001001d107141c2243e1071078108403607022810000d106102408001074584045c8040c511a12050f207640645910610b40001590002014504140414001d0000020502ca008001039400c1c5040394001c0d00d40b806040c002c50b403590b001e03207000100000b980303040040101c041d0840042c200300d8015129103641c006c0c2ca090b03a080c0b0903141450329070f4046507454038103454002c0d0049009401d651825860307a045119030b00c0d0541e10742c0161000071004008066001503458010081c0341011070812520a0000b005807007144802c00c6401d07216000b060941d40c1c2c0000329582120002c0144440711000480580604090224140450b007601b000400341c0c00c0454088102400052110446021743c1c1d41c250014000546541080041031202040000c4080e001201a10040d103505440326440c9103030350300d04105000c0300000401d02220750007401000181240070140c0c0420150b89 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 792222580 1250 792221330 792221363
    0xc050c15090f041b1706030a0201231b0307050c01180e09010b09090709110304080307120906020412061104030b0402060304140703200a06020d030c020f01060f180e0a 73
    0x7426a1320b000e044100568240000190b800480c0c440c4031106010b8814001d550305d804040e00e40c0700d0002d029000c00c803800340c0b20010700206003210718181c03c80c1c0060f5041c03040054011000b2500711041000079800000c2c5207090001c200b01e04910784030b003441c060045019003001054110414421205903000f80c01c00308100340802e402007101d02c000505001364030b02d001104140c1d648854407590001d00e1400d009444282e8003c02202e11554200302030398916101c0201c11070b006420204014546607548200c040002d5003030005000030007142d8445480302940d42007201c101d400c162843e45505004100800c0062801d041c2b05901c40e80444100b070b240ea4031803d2032800d00860b040c03088000c1c018a03501000b0407080700044a0b000b10079031203211940501c041072203071201190107440301503440b815920700b00d07601c03a421200c9101000d00c180d40c10454141041070070b4039995084114904607080091160320084d104140000c156204248208072036004030680390351130640040d140b0407000a0040 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 792223830 1250 792222580 792222589
    0x63c151403031608070212030414060a020f070308220f0506070f08032701090f02040c0210020d020a02010c140901050f07020306090a0204050c0703090e1e070c050c15090f 75
    0x80180303450000442c810780c150b04e44140960b00440d170481c07050216001e41c0d4924540001a6416500c0703500355404519540703000c0102d580c001d140f001e021072048204884182c441844070500440c07040400f15201c0704100341c0e036010240070341c141400f200034146042100d00c0303500811008444c800e4580c2c540c1c031500d03810081c85c840c00480000d07050140001c00c0c0540c0101000c1c02e100000f2003000318100718500f200d1001d0a803100c5102c00340c0344c818401409001351030300764888882010980100c815056105911200380d80002000c100844e501140c0c12110540a004030b48000c20a031401022110044103a201d0724052740c05038a0411201054002ca400c03090801c4481c4560010f084038642e1170f14000459942540c810f04900503824000400c0402e9440d405503500c3c154035864840b0003505010081040040c01031041c0d005030f1f07840c0703028642e20b00100d524a000e1001552043e84c082c002e4100f00346000b4a802c11503000d055000c07000f00d070442c5044250f880e00001100d0f04015402c0383c40018 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 792225080 1250 792223830 792223837
    0xa151809110405040f0204241b150f0f091b06050408030406050a030f1409071e12020301020d0c02060708070503100b09010e060a0509270c0304063c15140303 69
    0x1085107591b030f008032070030b00e40c026250340e1f8007000c0c60740e83c010302700e0241c6846c0c440c110a8000c005220b546164606400f42001c0c1d00001c2c0020502480052000090030401d01524181281915405075081c0340c08100344072a040440949081e0401e5460545040c3d4201e42c0c92080e44034102c00c200001c9189002d4612039003140f5803011410909014030a1181c040d54100c003030555180c0020301c00e020340003c8034998803d10440416043c150500f46a1400040d4842007070b2181089038155403c00031840f5554161051499074402c2c1da004044520307203448068603202000c1c4c09101800400c0c03041004508001c0a0032042e0b03010000351980b201c2c45000180e480c10b041184151f8008000700d020140c00c0d0f8001c0140002031803c4640540e410071205c102000d1703089240c0074800d00c03000c600001d040503216000550b0054886c20340014003001c941130800080e6980104094020546d04d0035001c3c1b402c040b07044558101801104010134401040c0b010402c20042c884c000500030303ca2000280c50741c041c0240d = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 792226330 1250 792225080 792225089
    0x2070b1e22080d0e010b0109080c060c0109061829011401021005090f1614040507120e0c090c03060102071404201b0a0c0e04020a151809110405040f0204 67
    0xb541e194280700141c000640000204a15503610308000300c03460b5807140050340d04072901c0d40c018084e0b90b6050028003560b5441110005225900c076545e540020300c40340705a0340c2c079884402d86046181070f070740340c00803e503a107800309083c0e503a91071403a8018458485c032040f17044501c03001030341480c00c0f01e03840180e05000c1d205150080c40f51400e010420490300104540311020803010940e031200c50b805424441c50000d030300500d030f1503000c0c0e403544e441a401c0c03e501498014200f4100604045503c640000548401a00d01a91500304040b100c01604010401d02e40000b00680725605500d4038100007541c400140c480c031001070344580e002d90080e8503554040404070700000301002d028040d080115000e41c0c0715070b20800c001d0000760f80d04030900c0808101a4070003680400c0c020b03400c41c50551403010781c40000d08143e07403040c0701100c0015580140c900013081c4208071b44580640d4a40320702c00820f2901c16501900703005080a841c1c0c08045650300840307003a580c040382c00007041c403a61000c00c0024042e0f42c00 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 792227580 1250 792226330 792226343
    0xf0703090f0309080105060111030f161b030b0105040b0607030c0206091c05070b0a02071401031407080618070e04050c30100605030112031107060302070b1e22 70
    0x4024550f1094295054500c2c00c1c0090116403141c00c0112400d0030320040c40c0003c0d4206000c900185110751000b0681110201d00c8010151456190300340f101c3c00c46058103e034030300d01c2e40c0100200800c20324964014181128104428036004020448610418200400700701c1c1000c1c55004668540054442d0050f01410f603201a0301b03451a04000302e42c0c014010b48072031041d41c04c0060f2049040c0708841507080c0e0f039406080800d06d0035058039804d0300c10301700e01d60516864040c1a400480c42440d01445400290745103240c4dc02d160043c0b040c550315047d5200c495045200c10040711540014403403000507000e540000b62551000741400050080141c00c8456030f00c1225510540c1c80c001948060241105540e80e03020341761000b82801d201010f1041c6c1c008508184010000340c03101c0030452061132301a0034102c40901e80961450b0401d03425401400101758041540410b110740d40404607880fa080820b10500c0104040d540d08404500615504001c1400f800f03c206454680d080d20720150751001 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 792228830 1250 792227580 792227603
    0x3c0204110f07060e0a050c01110f03070b182814060a02070318050a12030201020d1104080c0f030615030708100915140703050702030c0f0307030807080c030f070309 72
    0x41c8800550340406002d030342c200e050116113601110701085174030b1a9a485402001481031b0000151070500700c2c030311102c070207014400890707103d40e20500c014400544600804019850030345a0006060061f44042d0f11650090013076107014070710034aa91144200d011007508a0f000e840c50207518485000c810214140a4001440071000040d006030406501c42c0e101c3e10000305a2000041302c400da00c0c491503601125100c0c0410187c45a2503d120805010f4400586040c00004004c5c05807030204158014040d800102002a407909000d1240021801c55121100c401070b500043e40d2040c4c0038003000a05448218480543e6030308208078001414003009461080d840b8a03000da004001100301134034410f8031040d05d0100241c0d14401d211410700c01c04105c0070a80c8445d50100c0040c4002050034096101c1000811800382041000000e8160524001c5503100074a107401071580c0da014210a00b0300407104144404159454240c9600032004010300c00c1c02d65640c41c0407006012562000b404031000803 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 792230080 1250 792228830 792228847
    0x130615031b0302101409060306040908030906160c05150c07120201150906240210060e0a060e090715021204140a0e01051e0a0e0705073c020411 63
    0x181d4a0320100c0340200c1d0398055680d42c440007981c1c038444c0030b0b45400d01404100a540340c41e14080001d1600568060710004145210355140d0b03110303610607510b80175545c1c4a042000483d400f528095899074190f1b2500d1507a045041d03440691311080340700e0010f826a004d00003d80ca0301b02c01d5041d0b480440d0003100c1c602e91130740c1242e00a80201220070491030007050182000c03448030001e005150480b4400d941204c681110340400300d50700103b01c20b80404601503000d04007451811405807101400c09400d4140c1181030041e0100c00302c9845a10070b40b080e04c021002c018054401250f94811a026802000000c034401d2074101d04000c0301c2c202420341d00c40089004100014a05100c0c40d40c4001a1104004280c40e160b044003941000d06c5815030140110300c0024920080c0008040320b100d000d42161015a02c544030386079043c0c0c007105c103540016408500301042c0310084610030300c60300c81d03800701d4140000c8180ca281d40b81039a0b050759040040b00350140108540b5958450300c075040c40d4444141e29460074 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 792231330 1250 792230080 792230123
    0x4110a0b040906080111031504060513060e09160303211d101e0e0705032b08060102070302010c080d0c110f060f01031101020703080a0201020301061713061503 70
    0x603008010751949445404510300d401445144c6d00d0408403106142503554034107070329802a190244141d0803d0f15210002040d80341c1d84080301c5c0c0d108040201249a40c1041c8a2424441c0010400d044aa10100b40c00074001101002e000542e0303018a080c8146000604410200b507024030841d80c18a480e01c10444031000040d494920521007440c00e859481e1000d0b1150000d0300c803501406080841c075582c00301040203141e840020101c0622050f1703480743c0d548100003810503020860903010b002171480c0c0d103407940b15152040280c01c02281061400d906002c00000d5a8596500000f81070006542d010001d00c00c0b404155158100300b00ca042c0309006000780001c0503039200744140c800740d1045600940c9400c0003c42e00710310803d8a141c00e2041c0382e1842d01c03140088080c40c18904e0543c001d14801001081503d802000d21501c81d8002682c1d035454468000d00d0502044140e981200e1542c09010151003c02d00c41d0140940006010807201c82c01200f480000b0b0140d40000c08581030140341c841c00741032 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 792232580 1250 792231330 792231337
    0x317070201020f24090f100b040603020406091512121d1c2009041e17281b060b0319060506040e030a0327150b04020c0d0804110a0b 58
    0x1d565400e130030a80301c020050b6940c81c0f404407549a00d030007805c45203074005600d520907070034100d0040c00404c0d100d0f0303603030049001c031200b40c3c000035001c0e074881c030f2400103004000c5804030040c603400c40f08004840e19a1200e18500302204880b50801c00c241c2a880c0d00d42856910152125400403c0002c114961310b031100460300b14190100c5041401140b0105440111080240d40c0b02025004074103954607a5a586a0100400010715100550505460210352000e91401840b0545171503903a0f40c19501a4003210182d501014040c0300342c915203d0220964080786001a1000910008402001c1032808202424094840b15018440d80e072428441079000250044480c0c0510300030405038840c40140300c00e0392440188005a03500c100100315111b803190340011201042200081c0d8000d04c4150303001c406081d040c8084d00c81400351b03040b51402c0d003250300c620012010300b00c60451610350001070058403000d04c015503005201d801c0d00010244140313401141090342c0000d1441054544582c0000341640 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 792233830 1250 792232580 792232633
    0xe0a03030f06060c02120304080106080609121603030506040b060d1505030c0306180304080118020306092a061902160630180b0702010c090317070201020f 68
    0x90601c1c20303016201030544503410a442040d5220510088a5000e1003c0b120b841ca606013042d02c810480010318107020310a06010b0300045018082904001d40c0c494078040140c9011900751804104031690700b41c07d1041076452a80c58240032449030384a20004004000310350307205801980003d00100320030039580c0305068038446a0715014605803105d041c5691070082009081d0103522000200ea00740700d0185103009544214001c991510b07440b0540c460075205480c020a56007040c18040400b1407600303104c400c3c1d120500c0b0008040c00c001418003d464111130242206407031002d113802c614180c136071008640a0b10045c040b450424044004020350b20324000803000c010f24440c100c0400c15910501424a500c920705607254030f600d9610511034207400d05060114039580da5202c1b2100c0c002c03422070000031010b0080300400c40f80d141109010b800d4a5184080004003c04000140000b40c8450201a09880a941500e48400880c401070380b82400750f4260125500c01d900d03c4242d54842050303080c002c80e = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 792235080 1250 792233830 792233837
    0x9060807051e0d0e30040605071401180b0a0b030a110406030206040f0e28150302031c0e0607021c170d0207030e061204030309030210020a0302090a0b04050a0303140d0e0a03 76
    0xd041070b8403003000721103403085c01510508000401580f4895800ba254844c015280074008248092203582100c2c1c000006642280398540b2000900c8902031505510804070b480038820000c0300170000741c444400e07001c01405050410358110a540351035001d0b901443c0c0c054611580e0340e0306d81000703803410743c91846510a6031204070002201ca411074240702c60340d42002c0b90499139001280d4031000290582c50748a81000b0201c140000240e81e0410000326024a02844000700001080d030080c0383c4140c00080c1030107001c00300451001615041403d06009521800c140300c00c44151600c2212203000380c200c00b008442c0440e0106070302c0780540c02030400038803a40310a0418005c5900313110240c0212082035000618040c0000c001c00e010750800c4403407901c04e2055828100401150f103040f608054265000280d000c10030b8a01410118030401c06003074a00402c13400c007440c0c000040d80c940c0007404001c0400c6000c80000e000301d110030095a03000040d860702807000d8040a016503584e0074140e0400c0c0d001 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 792236330 1250 792235080 792235123
    0xf3f0d0306030209041e06020301060816030501120b0c1207180f05060415020a0605100509060f10050a09121104050a0b061e0c060a090309060807051e0d0e 68
    0x44900901c100c00840303901400300c0d03c1d5503a483d01d8043c1000041c1006c00200d02c040e8600c140015801d200844c040c00c480d40742c1110703505160a1198850f00c2c10580b000901d85003030014401e4a141040d1400d00c43e501800800c8503903185103481e4454040c00f00f1f10103800101c4002d00250f103802c20601c0440105000050a56035a65a064580903425104050300000c04000038000e40e45065640c6d403000c0c00a004446401c41140c0d280001c071a41218181c035541d8480400748103a2515400c07440c0c00c80030441d8032825203120200080d520411502a42c400c0c003100143ca000054000c42c0085c005014420304c40e03041a20034105005080c0303a035030a9610580c5480c0005100711030500c078922004078041d01060400000d803c0c2850400400101141c04540a0003503200c2240c00b084900d01c1910f0400010580041a280150032607145e50008001d02c0081e00402c404035a10001761151441c0c482e200c81c221244c0c035458403038144500f58190b890103080c4210500c1000000440004021568494411 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 792237580 1250 792236330 792236353
    0x21303030f1805090703090503070c03030801080708060912070f15271205090429032103150604090905070f120b040209041403030a2403020f3f 63
    0x31400040c3c001c4691043c62007010805e403c2c46607101d03010040c031032802c0b1b0f40750580d16240c44084103d268000ca001072850710040c0b0120100b4442c1070020720b49080148103a062000e03000307464684242a04100a40c0454100203008249800307510315908803070b0031040c1261495081d405850f08081800110403a03480d401c4851004180118086410500c00c0c0c000e4203121508070303420b600c00810158030540711841d403c5214141010505040c0d215103c21160500107810b050900210001d0050404501107074030600c0e06484048075406580e501a9030400d0304600c0001d000d80c000c0341c002500d46417801500c50100100017852a0a581c0d501a080c00316690380c94460720000d80503403008155680400218005042017a101500503114000000246018024075465030300b040355a02d8040d52581000080e44034207510b002c0407903100c2078141c0981c0d41190042040801048142c40c01440349441e00b0b25416000000d290309085800b40729012141c04c0103070903202490440c0c009550b801100704c405c0 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 792238830 1250 792237580 792237617
    0xa0b030c0d1d0d2016050306070305190c02120c0f06060a06020a08160206070c0f050f060415020c10110c1215180105010b220305060a090303021303030f 67
    0x30b060820001c10141100e508201c1d400700500754443d5000c0420031040d075810380c0c10302c5243c2c00300c840d8540810100385000300705458a04040c2020381810b10742410301c00c151001581d05070a1100740380c07000c1a503000c0407400320b161121a204808080c00d0200e80b8543c110b42c0821070302e50102c000400c60304c990720f4260403c2022580d51144402503405100083d001601c5000a010841c8110301442e0000700242c0114805030f1119404654021200105014440440090001400080e149234841912401c085009071007180201c1ca0454540841149514820400d4010000d006084180c030b14030007034000392501181c0080109640030741140740042d420000d56446914032064010842c0018064400b100c6610184c51510f54030002200f03103029010034003400e4001d00c4481300c0c41d980d41d440701c202500458821a01d0b41d00c1c055081c101040820f40004206070085156030340015030100518041c1d00a100d40d603120006c2566900c030000c1455004885071524150948030500007100e00010310 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 792240080 1250 792238830 792238871
    0x16020f041a27041a01092c160b0d0c02010b062212050303060109052e090f0e06030105090d080411041e091b030305180a0b030c0d 57
    0x111141101409208645041101d154502104040d01d0100c0030748011000605401143c080c0c400081140150b071451107410301150052003540d804203c41031074160072103c0808840c04061500100c100e0b50944400c041c09103c2d219804078900d00d0fa010341e41c4034041485d8001c0e440f030840043c81c20010304440c90042c002c050035000c0040480d440d1080140b601e81041c07070b07000448602a0340400000c904c10215440c0d58103003038005d07c011a00c0c1d242c04000140024842d40285025119181800900f61070701c0c255440f00341d031076154900c400486210201e90011490340000121942086d00044455000420382d000e0041500244402c1d030705c4c64103d035500d00a01682c003001800702d034000303404101d0300015043c060340020008900040e0103070b4240d40d64504075031441c60090742c488031241001a488034680701c030101d0001c564451480c41c1c90241c024058042c6440c03110301682042c940c180d550421010241019020560f00d07400c00001d0003500c1c1d048003400702c0310b6030f2401050003d80f13508455407 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 792241330 1250 792240080 792240101
    0x10801050a061b030c02090a0605041803050d0e0c060406090305071a0d1107020904030e1914130207080c03070b01050a030809041d06090c1e01050301061d0616020f04 73
    0x83c41004031108400241048260f00113a0800c548484520300603901e07040c15074000d00e07011501280c41070078441000222094400d030340c80081d03480002c020020b0b07040f106440c140080020b000950b001427004003030510401d401555401503000a0105055801c01400c40c1941c0c050700480d0502c90f1205031b120400f100c201d0912491103020300000b0f42c2c49401d07800440425421031400390507c10617a000c91510034099504501080c20402c654003541090034500800c44c200d008120340c1c140c9841801104400c0000d8014060008440d40401d0a03071590120740f10f082e400040c55542c1d031003101300903869801008040300c05070380c06000019a4500b190302c403000c0e0b0703400845880c81c01c42014108002811301c100c05502c881580d1111042d81c003030074492a4030a0f40d03c8409814a003814401700030311460500e000c50a10050070f5296a441e0340d0203801d4a06403180c03070520303501000208428003c503600f520b10746540030400080c5490380c05500141c12140f60710a840d01d1401802950801041d070355150319 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 792242580 1250 792241330 792241337
    0x190e07050a18060b030a061d04150c02120711030f070b0405040504021809031909260f0313180e0a1115180f0306040c0302041d06070905010801050a06 66
    0x70602110140b03408090800400301400a680c40c3d80e500d0880c0b5a8004840e950710507a40c40300104030420401c0e441e02c9100c1c1c10041030324850f26007543c81071001013602da00c0078005540c8564645400780200503295a07030016403007103234652080d803902c01404800030750300c0707402406480c0b1031a611607000621241942d00d038681c0141041d080c142400003c280040c02641e01248605d00802440803040c1540d0244c1f1492000d035544111804800840c24159803d600030000b41c114100030106404400304015400300c6040080c4a10701d031650703850b2001d00e40844003d808002a103070300c07421000c51020f00b2501d030010b42c607a01a9500407180700b100d00359042d540e056041405180d001034401d0600021050000705039405a4107a8010704c3c910340c01508440c00721102007030303014510740303040c603c0e80101c40c00c114010f050720f282582d103034220283c086c80028052511007441300740c3e02e62010708503400801304004072107070391610071002010ba000610426012505c0c440010540b42810511802038516545 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 792243830 1250 792242580 792242599
    0x151227100b120607121a062221080c010e1506010909060825091109090f010518061305160908060714070f0506180d08010522060e190e0705 61
    0x41e840000c2e0049105410414190040d6049540e40310000f90080b0507230a0400d4600001c089511000c0a00d2600403031411079038581c841850303030f018500381c403487c540c4203144989030040c0d4810103026042d5118100598026460140946506a01c1081c03103020240e0f280040155a2210342d07044800b2750082c44126082109091051284001907580c88807001c4c1000011075503030400b00080f0340c81c03040807503a801c000085640311850003045c116082644403100200c030f0352410b4000344004824440035210500e100000407429500e41910fa02115421002400f10f49403401417140340300303000300c80da10100d6074004000c1200b0303400040040c4034010946500396101405015002c154024030b1007196101d0708404240001441804124060f131058501c108840031030b000e9050a01038000c007040d0030003140e840104456030310860040c0c0040c0320074130722041c41c2d48190b01c040040c00190300980700443d840e0f801d00880021110404150072030b000b508102d00504410801e8035400540302c0c241c1e0240180 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 792245080 1250 792243830 792243857
    0x150506010903020f1503190e151303030e03070309080f01330902040e040c090c080708131205031e1504051e04060605151227100b120607 60
    0x300148a003a0f0010401c1d480e0304504640304c849039100302c0f03400340200c8943c9030034030142005000340100c0401c144050481d011521020301c05a2400400300407250b2b07074012014007030501a41c8100003200c840c505403959800c0b41d0402604d260585d204000083c80b50030b075000c071520810312801c0306210350494012810b162113a1079207541d40744112880a1400e13500e0002030b00d5501d03440180004d001ca41541186454a410b01c1c188004150b40101c0809040491003060603610200070344e03200f019400c00c64030b292a04410384c0170f60b006004c40245001d0604561700c40f0240c01101452042d01c04074406840148540f4820469500588502c5d074031a0700003c0c03c40d114502a000f00307a02508410b004400f003507090b000340b22201c0c02500c068800c940d5841c410312246c100301c03100103481c9010103003880c6001d10481400c80d1005004042c100306141c0003c4803c01c0f85103000402d003d100070343c0121034650a00600c264000d16984214a101340720802c040c00708200b011401510506540c0c5658084c04900d = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 792246330 1250 792245080 792245089
    0x1b03130608060609150f130824070e21010c090f09020406021c110d120606110303041b0f0603140906090a0807050111040e07020c010e03030d090503070215030415050601090302 77
    0x2400b4100040c6d01c140300c1c0544d8911540080001090743c1001440042200c1841c8100386c0041252541e010704940100504250007801454113600d0a40d0020b0b10b5220350112007200900c5400060155402c0505003c0f10a5004032900d06030307a03082140010391951803c50030201c2c81148038241c0541c201d200c40800f41004854640340b140c2260070500c0f940e0448201041c00c1048041c04040801d00d440241f1074050714500c14a000f07490113050001d4002d810890707032a900d00004200030554048a081c4112038548155100001d0002c0c1d212a130b540d07034440d440503010b8144000380d895000f0500001030b5a1840009005008003c83d40c0075107210009920703410801ea000170800d41e280d64841c03e40c7c1140648600041c001070040158910190400750703c001d08112580030605d040041e50030070184039560110442d02c030307c0717824040000d42d11102d1422600b540201710300030b544414001e0030500d180306888000e6228034031460208450717103000d4020341c0c2110b100340c0d01075000400815080c40117080 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 792247580 1250 792246330 792246337
    0x118030611040b03090a110f090609090703080a0306090b04050112020126010608190e060c0d0b060309030702100503040c14180405010c17011503021b0313060806060915 74
    0x181c16481480c0a0303d58001002980c81178810421a500400501d01400b141c8420b044004204580183c601d8000400040048401402492191246001080102e2030410400e00103590040041e51904da001c04054020400c500c01c00c0b6046050452411052a0611815068034070040540b0507905485d0011030f03803010044103501c0740804400b6900041240c1c811650300038a0709aa81807a07a00e08840c240c0c8031040046e003954203050a014402001e001c01042c3c6035844034200c4809625000c03801d44040242504040540d0011000001d1024110012000303010450003540d03e00401000700800b26014402101e02900d0f4001d0300100b0b0ac0780100703814a603540700c08010034020503506e50020300c2000e40d20584040f2000c0c0c1d9a59003480215030000d00c60740604961070003080f080c0d0301d0112581514a4030300070410425070700050309070781e0000ca01009028004420212170f2240444081c0b503104e040c40c2e020f081c01280000d800904c20b454020300b180c40c1510301070103050003240195841c440d1780d00b = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 792248830 1250 792247580 792247601
    0xa0812030f071701260105040201020d050a0306050901030507030b07170a0f0b100309150603080318011d06090c06071a040c1a07060c030b0603070e06130303030507030b01180306 78
    0x249040b500c642e00e10302010580c040d00b090704804c02d2025070300c1700102c1c500f880302040305241d03410101044090303a004a040f4008000c1030922541d9143c5010342200203240681107560310003080000402070090000b1074600303803445040358603616100c001040c1d50304000800390580343c01c12040042c5410b0165004515191648403001c035607120000001581c07510f8915035403000940c2c500c3c40c001070015038801c40428024085003000041e0a584410401d03110003022601c000450312014103180d1000d6005410290a0251000180321640d0000f92034810a850396001c034407a1840c40c5c0031074034140d0225600190301122041d0b001494480d20703803036200020000d488510403500001107c0712803411980e007601022805035030794001450900304441c1281e826400309443c00700c4040707068507078008070380c0c10000d141010b2400c241c1500004456216076039501110380010500002050307007603080381d4000c00e06c3d510305121000c0c07010011035000300224000005010711003000c01c0072815603840080903c = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 792250080 1250 792248830 792248837
    0x11120d090602030c1e0f0a03050c131214192003010f0608060901140f22030503060102150903030a020a0e030a03050418060803040611030c060907050a0812030f07 71
    0x65403900e41c50101c0e04112844894000000780301c80b52a0170458102c0c0d07102c440070351254100401c408130080c841c024810302205040e5140c02140100803030380f0547c1c03508403d20320a58491619142c50078a050b407400000c541e1240c00c1c180d0060441c1011482d00c0c031010f40508034001c6040c90361203941d80321101e5144001a505228450b0215440a0244012202c0480000b05840e40f030401c070a0b1600200410700e55459240c15142c1a11504c03802401c5d0304541c0541c481e4516480d81c4803542240d040040050b01c003180000c01550425400402640c82200300340c0a450704040c00507050710903100b003158020550741080002900510300e543c00740050102a24014900d905541e010a00c5d000720313220b0a0b001701d00049800c1014036080807200041c041002c200344002c0345845095680e90090703015810500c022604070f400c2c60741040090fa280184141c04072005420404509a00c03200036025083c0640c8880307030041307842c40000030304001d0711180101c520724595460990460340240604140c082 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 792251330 1250 792250080 792250091
    0x703050d08151203270d080c030f13051c1a0a0b03030304060e0111040305030405040b061c050105030f030c0a0f03110d1107050d080d0b04020c0d080402040c11120d 72
    0x191180c0c400c9401400081c40155900c0800c004020b010f800007000000b04d50703a80e45e08840e07403501d94640c038040681d4030450480e2a0080088202e007140501020041103080206520010700148119142120303010340724034566a001c007854000c0055015006408074035100c08000021488500803507100000020001c1e01c04803000000c1c0c1140d105840640b02c0c55203440490f603c1d06402c0c814000304d40b1103916454982480c42d6074254903400f9520420348601c0c4c0d5000300c1c4015403519000c4450341c030552884441e421041405400050100380580d078040d105a117500200400004111400d00f8041402410b04800c50b81e550400d01d4000c0c102242081a6514030903502d844c1008000b05202940d01c03600c008a1400101528000c09030340070600c00d400131002070020030410740444214a0340704d00081000c00102011801900c200503490341d0390f04c51070441c00e440b00da00188990080344200d6040c00b4100c4d170590100d420880c030722004a030540001200b82e8400c0c20520003000304900b49540880e0 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 792252580 1250 792251330 792251371
    0x21911030709051603140115030213031203060b040f0506070203070504020f031b0901320409020d240512010902030106090b010f0207030519050a0c03050114090703050d08 75
    0xd101d91944441011911002400520352044c4005081c000007880c0402244a5140c0d40e0040140b0612a00d8135940960a50307442040c0b0a8049849141030040510307401c5560303140142076549002c0610001038540f4a01242d42c0d090081260704a03400d880e0040102800d0900700207099100c010100d03458801c2500c00552521180081c01d5540c42d060410b603100d292011500006800c0c404046d203443c04200400480d0742e0300042001680d00312100889480a005015a003110340d5084018170032501c0480e0000d0a1031844d00203101508600205101d489142030390101c03540c1d488a505903c6003030003c014803031404c24082404c1c031480d185002160311256030f00441e0031904641c200001064030b4100746061942c12078014604141584001c00c09145543c41d01e50b10360408070301c0c040312202200040c4091010801c030051100d03070001400c9814690302d1030054002c0c403060800800408030980025110100400c404003244d17040400b429083c3c3c40601c040314038140003014110419842c1c030320001c = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 792253830 1250 792252580 792252583
    0x3030c0f070516030c060201050103173001360b0604031b050913020a061805040e0609061b070f021f0804031d36090715080702191103 59
    0x501e0940924044503c501354140342c00124115000030042da814000100005003580d200c4500c0125131035101c40e190710b040064054002c200a50345100c21504c0c0745d024440e15460f210f41c80c12200034841800e04800401350495004020004641003003006032005d03002030f070141c3c21003c030490000b03002078642500c82c0d90302550b004c299103144100ca01c40711418805418803503442070304071100c643e20740b44031891580080c1c011552402401d041009282001304c44c5008807110030003400c030080041c8090032000c00b005642e0f0710112034004662140402160b14441d00801918032803401024142c07a1800700e0b2200c46148030a03c10403038003e10000201302d960780b50405080100038050350348809609060400420541c01115040084004206107880b155520716500001d0b0300e464468800a1341c3d0010076070b00861041c1000c1400725212410000244804983c50003561078a452618040c1c0c1407103800c8a01c508200c40040260380002c100146080181c00c10019061090345000e03e200e03000c0012a = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 792255080 1250 792253830 792253843
    0x501020f2a1203041d2202030c06070303090204060506071703060112061202010210150302120c090103290408091201060801020c16090c020705010c03111e0d0f0203030c0f0705 77
    0x524154102050030300c5a40720204d07422085d042c00805203800c0d801d02c0307501181e50f861040c42d20812143d49032464421904d00b80520448442c0c001c0c0225100d940b5400c004d009025900c0d001c034421440e00c40080356520300842503071060b54220440d651985441181140164070140049040c014029103d9428140d64000c20700034003914912080e80b4002407001a1030b10310070010700040c2070f041c080000c2203142c4040480d400c698048620320751441c01c80c00a2410400e40c4200b05410803075200011003030009e020078801000032120448900d6008003050304582c1c3c84160b500902003c410007004000707240c1280490403a00d00b50000241065950305d083d0708a80c03140f00307041b01030f801c211017186044c0206c929000050808010a0003e6900750100a4440d0500c0c041c003070502a201d548882414031551100c14400314803030494a1a14011001b140c584844c5104490f451080b40d0b0b14454136845442803120301721458008505640f240e4040c1761441c2c000028000d10700c0e80601a800129400300700b030 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 792256330 1250 792255080 792255109
    0x30b090414060a110a0507110613081009080307031a0907030b010201060504230c12010f090b12060c0a0c0803010b0a020106050603010e0103030c0f0206220501020f2a 73
    0x415101030729501c040e80c2081d000401004696250485203511034000d18101c80c80c0e000e891402540c0c404003858800307259035182c0c901d16004a404910030817001003a2141006540c10401200d15001c14210b0101c240d4600d0b40d03006203010018008184120f0094115403800035010141810840d09403002c561064400ca81100000ea1181c00d2100300756020b106d15805480c2c2581e05101048009039050988100d907000d8948040c000300c002011038800300144d0b0b1100d07030000c800f092196980c03003400e8100c100c140a0310f40340d44d150a5203021246400f9007000f000750b850340e018250a640b900891001c03034108000c524180030f55980c2c0200041c1c2140010350103002c0c0c08410341e444034080d00009084074030b19001030340200d2081005024045181014504580e414502011714031003c2c50310b480a66041c4070003e4004d040070446051581c0544c0c00b40c01c01c80244541c243c1d8855481d4012070340d4403586941100b079600320901c4901c4040402c454451201410501450082c03407480205100000716801d = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 792257580 1250 792256330 792256343
    0x2060a030510060e01022a0a06050304050c040212160210091b0b07051207061d010902040f18300c0b0c092101060305160f240f030b0904 60
    0x30002d1602240c080395000e0100e500c1c16411030300c2d0040001c2c3d03943c43d000b82d9829885810040b020b00c1e10115010061445401030490a5016500c02c40a401e50700252001c0351213009901002340d0303e0900d80f00781d845600341c24103044419112101d01c00141d003542e5841c01c0450040701207080d580c0f001070183d10340482c07041728891321621034050015a4003c982e009440303604800c10400b40071460000b113155a0000e04541c0c241d50301e030640781407802081a0044086d81c44c1100b050880c00d404190300c82080180262028030002d8040b5443c4803c59540c5442d000c410b001c4110701070003003a00001c0c3d1034240304d5415110000d01102c80c052180c01c0c8011182d110008119141c0002042005036405800c0b1003111012802c0c0103280000890b1f00701032a80d58965400100886d01c8003210035007001c0d00541d007000030b031348880d03031805d040c4031000c10302c0c0c000d111010315020380004440100c40da80c410281210351b1122025500e012007102c2201541c6840002c05865150b600003d98131920094000c0d41b10342d0 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 792258830 1250 792257580 792257591
    0x70c14030c0a1d0108060408090108181b040b01020a0210141e190c052e15060e19030b040f05030d020d0507030903090312171501020f030a050f070f02060a03 69
    0x4800f00c1c034840c41600700d070f595904800c00744400030306030704203440545409080a10960f43ca24482d60780109000d0741844540c814900e20704140300260392100c2c49101c09031018001c809d540401640e07550181c2030001e401c16080c12500c04902e1182c0d00b1070220002001596182c840c45403031003400300b800c001000e80e908800140d007808400190902c92030413034079420030132420348044e120207448000d064075003070b50f641c1142c00300c1b40c046003040301c513076007209552008004180c1c1001880400c441140a00f00c082a06010340001170300d031103a0b4480d18101541407540320181540d82e6000580d0015108403842008820310400080302400608007600c0522801070b20b4041070511402600c80240028003031501d03140d0407901090b485500030007030340c1d0081d803090003d104948040f100040f05020074200a402c1c84140051860809901c19410383c0c268201d03482c40310300c0c06802d512440382003400030200b0010007203a0510408903019004582c050001060481c0e4560081181c1c0d50004403040c0000755500c = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 792260080 1250 792258830 792258869
    0x117010e1b18010b0306041a0405040c030b010515031308070b070c060b040209030c0d030216060804060f060f06030e10060e0f0115021005090a0c0312110102070c14030c0a 75
    0x100c1e42c003060200c056160540d1949071480b0f240c401e210141180380200c0d22a178408010b80c59082040c2c24011001c1c0040282e031801c0d0600000858540c04101c44402010000103110701d00404c03a07040ca4400ca120035840c5444486001000360010001101e0f0f6a00c2488074601091065091034072503c2c0340d803600c02c40e111103454131504554440d03031000d10031403041c0120000ba80b000198202003071010303070304200440c0250405031300c0d085c01c1000e03d541c100683c010200d00342e03601c004180c1c000d500c141402d01000d80300200e030400f5200300340940d5001502d102c8007045041e202e81c02c4464050a02815074040c0b00c02021345005586035600f20550701c3c0f03058030501c014911201d28041c010680300800901094541c980203481d140c02c0d580d00714816407124003042440e1014008010311680c082142d8840310754914101141c002910403080c00310f00045070302c01e0300308018021100269402800904c1b41810102240744460300140c0031501882080456034403074440707041e050060302d2442850310181d40311 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 792261330 1250 792260080 792260089
    0xd05060c030907060c03090b0a090510050c0f010522080f0a030b030c040902060a271e0f051507030513031b061d06074409090117010e1b 60
    0x139404a804c0100424160020a50000201c401c1c0c03070a1856240d40c0c0c15201500325540c41c4280c0100b0b03840620a0a641c0c01d0070b41100040020480c07160a5807103849400800d5800c03120200c0712038041203a810303400210440e03640100c001c034500c6503440d81d04100000c4052500d07900f201c01d14002081e5612001d01032031908014403c107410049501b40100c8100c1d50115049014a8141006001003150701d010302000000381c264a000052103e001d043e81d0718020b41032030a09000d84660217800044010038204000b1030540255070020b007071a44071a01820b026602eaa01c901c0043e0100031050011600c0f00003010040c10046029031007019241500011007010009150300003001c0c0b01004d80e00259036240e03c5007c0071040c0e03049407907586640c1c990408802c000f00600600720300021281110010304100403c03008816200003100c0240980c030180071001d072103050252613011a44d08010013003c0a100b084c5c10100302080c0000c928414a9140030b45070400d644400d0215103800052051107080 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 792262580 1250 792261330 792261343
    0x10c1208061f09030b061e090c0c030f0304140a050c09040201091502070501030f06080a02061e07082802100b01200f0c03010c1e03090f060515040510090b0d05060c0309 74
    0x46c111078840c0040504140c070000c61540500490003180c175080011158003c00e4207503000190394200303aa43d10243c3c8504603909500403102294540030600c010401e00c18005880600304e64008000c002c039002004c200006050010b0080b4100440d900020400c1c00c0f810750711883c0040700790020420a4101400903040d00d0071318190034119882d101d0100b000034000190803c48517015690540c3d2074400c0451031501d0b2072041c0d5201341c000130000d0004200100c0d00c0040141d6440e01421b50240300e00002c400f031102042c40107000042e84800f840525001170313031b8004010791905040c1001801c3e00440e4600001c40010300810b00ca130010040380b612880103110980030604220020011030361101070140c0403d01c403074420743c0462a101c40404005000e58003100c086900120b406149140c240b0f0224054503044031840f00a0004e90902d011500f0a030203424012f084c41c0c01c0310030396241040440802000c00484243d0b02001d045200e4001c40c1092114900904060000b10340c0d07480c5c0302080500d000d2 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 792263830 1250 792262580 792262591
    0x6160605070203180906060d05071e0503060a0e130209070e01110601051008040c21060c0c0206090d02041b0e102c040f0c0e030c010c1208061f09030b 66
    0x400401092103243e801440041c0381490444541c5040d1b01c420700851001d02804a00b40381c641c0c6400c09000e103094003c00036000c24010799a00c10102c180d41d503001c950a010030380d000fa80100c4490340c144001610001880e52101c0001255601400141c000414490095440401007003000e80d00922550780aa04140005481d131300402d81d40d413410000c164101a50401101080354400105e003c101074400031400801080780030404101400500c0914000c0307002c4100c0b0945d240407100305403180074070b41d01a6545c0e0010b06003070604410b01c05004081c0d8107258101e0344140c1d1f0300c0d200da1484c903581c45584004d03505039541050554284c0c0c10302405d2948001d2800901c0b0101c0c00c0200ba20325071800240304ca040c600d011069910010b004103014010440c82c14009500b0122030902c0c1a500200d01c88040030203d00f00e40c001c0c01c041c0c2c015103240e00500c00240100380c03803d80041010340510505500980c0240c07003c10000b03000018114003aa0580f442c1c03002405040302041805004004240c214 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 792265080 1250 792263830 792263833
    0x4020303093c090103030309080c06010305031207030b0130091110020316061505130c0906050c0c06031323070522200403081c02070b1b0405061606050702 68
    0x40b05080c0008070740c41070510004003016180c0080300c00b0024280c2c2507a0b1507040f07200c12240d00756142d1500c04e807030f80c10403402018400009000100c0d12846401040c42405e810f848500b400a80740e50503240d050001e98106481c3e0300780203401c28460541d4030440e401c0c5d0340601c02d40f01440c038101040004504143d03500904561052088070203002607003c0d03c1c103c1c6031303000c20002503100d0041c80040e011159a408554400501e40d10058100201c0e003005d80c4034076003681c9145895450b94010b8415009400889105900580440d03c0a04013400110b801810a003e00320300301055541d0515550b4644655082c4001d0b4000504040b810400401020740000c50b0300040f4035075404c0c0703030400c040c2a0a102c0442c59848180c1c128030080701e810500409404100c0c0c2c140e0f1142c03a4203186400d0b0780b040c070040b001400c40ca0b4820000300b4091096070003003a172240d60700a580d00d42c0901c0302910380d4028a09071801d40d08200001d05c0d0b6442200a20000d1100d41081002c019503051400885c0da000f003004065 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 792266187 1107 792265080 792265189
    0x152a02130903030e120d020322150c080705090f0d05120702090c040806011e0504152d0506160c0311100903080d02030402030309 57
    0x1c014043e450a04c000b038540000503075168038036100707000b215905101403222450603400071a04611072404407079960403002400144803090402c2240c81009100041c0d28a10850261901f075400c80d092045103858240b102500911403c28511320031000ca0648038260380d6842c1464242c560001e044400c4e094403800040c00356445228168416031890002410801040c42114140c034120b2000d0503141c2d213014a1094029005003001d41e02c00306014000c6200c2d2264800c00e407480d164481d0510391240b900220310243c0c500620103400030204040152030301c0320b84041a038111603054607081e41e1401c494284100094020760000c1041507070840010501c4040300c040c649180c000c60f1480a00070b1401000e40b038040b52848010810281071143da4400140d6601640c1d1040c00030741030f44e00e00300042c80020440301202002e00f0380360909003424000103e00120345010000c05d640c01018 = true := by decide +kernel

theorem cover : BRFrame.Cov 792086330 792266187 := by
  have h0 := BRFrame.cov_init 792086330
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792086330 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792086330 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792086330 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792086330 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792086330 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792086330 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792086330 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792086330 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792086330 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792086330 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792086330 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792086330 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792086330 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792086330 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792086330 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792086330 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792086330 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792086330 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792086330 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792086330 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792086330 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792086330 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792086330 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792086330 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792086330 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792086330 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792086330 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792086330 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792086330 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792086330 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792086330 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792086330 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792086330 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792086330 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792086330 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792086330 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792086330 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792086330 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792086330 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792086330 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792086330 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792086330 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792086330 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792086330 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792086330 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792086330 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792086330 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792086330 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792086330 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792086330 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792086330 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792086330 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792086330 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792086330 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792086330 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792086330 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792086330 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792086330 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792086330 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792086330 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792086330 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792086330 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792086330 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792086330 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792086330 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792086330 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792086330 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792086330 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792086330 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792086330 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792086330 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792086330 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792086330 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792086330 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792086330 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792086330 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792086330 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792086330 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792086330 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792086330 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792086330 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792086330 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792086330 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792086330 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792086330 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792086330 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792086330 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792086330 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792086330 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792086330 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792086330 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792086330 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792086330 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792086330 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792086330 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792086330 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792086330 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792086330 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792086330 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792086330 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792086330 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792086330 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792086330 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792086330 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792086330 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792086330 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792086330 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792086330 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792086330 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792086330 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792086330 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792086330 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792086330 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792086330 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792086330 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792086330 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792086330 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792086330 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792086330 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792086330 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792086330 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792086330 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792086330 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792086330 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792086330 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792086330 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792086330 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792086330 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792086330 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792086330 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792086330 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792086330 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792086330 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792086330 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792086330 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792086330 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792086330 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792086330 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792086330 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792086330 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792086330 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792086330 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792086330 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792086330 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 792086330 ≤ n) (h2 : n < 792266187) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
