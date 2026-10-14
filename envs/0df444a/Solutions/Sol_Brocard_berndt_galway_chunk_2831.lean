-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2831
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T07:52:28.620278+00:00
-- url     : https://prove2.me/submissions/198f5afa-7936-466e-92e5-9c3c08ace86d

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 508992805 ≤ n < 509172661 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 508994055 1250 508992805 508992811
    0xe0406121406010b030f06210607110105100b071e12050a03050606041d090304180506130504020a0303030f060e09030a0207051c03111213062705060307030f05 70
    0x8009007400103407181c0e07420508140d10841008500b0400c01800701c0e0f24040d0903510140c21034a026490704080280e041c0c0307068100241540740b043c9401d01c40550303000102240e4054461009000315a82c14640d000c958180f4842c240300c2c92000d010203000079030303000b0205003004d88140e102d81d80c0e0b072107507202e81c081032000700403400110300000b65416590398940117441d406041907521034a824505104050410a40e000c0300c510001c944020480d601000c6c4101c03801400054244854580342c1c0c4407001c000e060654800e440b03903d03810302c0420a1031203401000e10468009094880051441e14141c000e480200c070140522555070340003040004202c007402c0e00401000c0019502c4070f2051134003a141080341d40101e88100340c40c12298452002c1044044401a403601e070000e00408803048107441d05c0c0008840c454005008103401c3c1818111030b80280c100d803401d0359a01e802c02c0c515041d6541c1d04140e050350141c4400c1000b01400a81405401141c000c107251900155920030051714000b260419 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 508995305 1250 508994055 508994063
    0x1202101d21071721011802070f060e150108060103030206060d030905090c07060509060402030d14090a03030c120314070302071a240f091303020a0c062109120e040612 73
    0xb1800d1044d10608001c18840e1001a0400751195410200c051680d0502c1d42007140b49145c000504c08200b00040301d84040f01c0e0342c003580500096200100b0243c4070703000c844c01000c0d0760041100000c1d107040c000400074101e0b03815401604894540c4402d014075000400360a030203200d8144030018143d06c030b00303907a1403155226410729511510145030070019107102900c903400301d500c51420301000d69000304d1780d05451142414040a00f814040740d0303000074001e248901d603128205460010616400208000f445407242d10300c11204200e801069080f250782c2848114440406800100890b01075401800c2c2103020701e0004110301e601d4810802c40b003404a030340103d100040c1c600080246600000ca40d0164001c6800342003100742d000100703280c030700b00401026000c00c40401c0d11003454024030070014000e4008445242040d222000980440030528854211802c1419064103c00ba0351090350660b82d40b00314488151481e10a007201c0c003100b0040450341c0701e50303114000182409040c0003281c1c03c0e485 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 508996555 1250 508995305 508995307
    0xc08060105100c11091302030709140c0307020c0f0103020427062309130206030c09010e090f0f040318060c1103030924071202101d210717 61
    0x1440280309126440702c45000a100d01c3e44103040010f2900c030000c00340200e09031120b003010f80d14a54520403800702907030081d40501910501086a01168214110040c80c1c03500500c0103071940e11035038480d440111124001a0421044c0c0d188502e4124585401002d0504d4003506080c1c4900740c04c002d040c00c03002000480d0065010720340842c000c501078003000740001300c2c031048002546103401c1100390800c0341c203a10803481d100000d20303905901c040d00b210454028084646070b2800404101c215841860700c980440c4282c80340d9805c51801904880c41000f02880e4403215488c5d0915030a02c0c180c01038011410312450942001c00e0085042d503001c01001699503020040b40300d03080100220080500d064020b030070403c800e1185d40c03030380b2035074440804c030500014541c80a000a504c005004148005000c0d01081d040f43e404140d00141e60080c600b2800070030401d43c0300d207141c141c0861081e11041c450503000071040c00200ba440c4240581340312007000d64140345c00c24a559083c01c0407112110b00c048540 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 508997805 1250 508996555 508996559
    0x140325020310020a050405010e060c120a030b03031903050a09021c0204060b03100b0a0504151106070815120a120504170a030203070f022107090b03011122030c080601 73
    0x3504218111042c1c9020504510f844240c00d8000c2c81c0344a18096207050001c60f03d24411b00761030700300848461000c0041940c001148003d041801540443c00310300c0000d00744581d12442d4a004001c58691105404118403081900c3c1420740c05031070010100d0010340d82d0340c00b403180981c980e00592001d040240390b01001c040701d5881000b040355102d802c4030010303150500400682102c0d80348845e041c0d918010103c0c0d07e40742d843c20100d40c144240d030090114101548103c10040750008043c809020307c0c20240e42c01961404000c4662040440c1d81c8100f2a24600a0041500303218180300103a40301c80c0161000038107107450780307180704c00d0b004800c1d00001d50001c0d0800c032030318021707544400c1031903440050403000e03505842c0207507240145c00f800b81020004603e6582150f0318000c000900c1c2c183c0010320b9403200d0038401c4c40c540b16003035442900c42150a20104001918040c4622070b41c00c0780c400c20090910b00d4040d00313204100c90300000c03c1801003220b170b804030120b0a51000c84c4e00400a140c01444258 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 508999055 1250 508997805 508997809
    0x604080306031501080a020f030f030c0102031504050f010302040b0a030215070c060c12030507091e09050702070b0f070606052211040e180304050a1707050603090a14032502 76
    0x10b1041c0c41643d00302c00201c80180800c4a011843d24005070301216022003000420b00040c0c1800030701503076a0600d210002da007404801064000e140318005a011000c6464491020320090364001c5031600d42c3ca0110b1001440189050752004c4241180500350088054595021501c0ca44141d400440d00c5c6102150311f03404c01059840740b201038100751902034407440c01035492100040c1c451000034107041e05d80c000144c106200c0e000103802407219901020460b8030703c02da00701500619015032200300707090400043c545030000400d201103d00443e030140c902000d61b03554545641014408590075900c83c000002c4541d035481c00c02031204030340345e8810340c100b1103100c5010481340c02210f0101c11a50030310040040040401c0101c6e07200c4005030041c5e43c0007400d041c1c124254485c0b030704515030008803880045400700740c03d1445a0381e25810822600900c1c1c441041090324003040307840c09500c0e44901601ca000a03c0000c08124140380f6204a90910400042c0200d030f4a410340c0711101003020f1600d0303803c254 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 509000305 1250 508999055 508999063
    0xc030d090525031124030a090b1f062c040f020f040e06100c03110f070b0a090803041a0a0909021207030b01080702101104180b100e01050a0c1103060408030603 70
    0x804c9003207542c20b088042d224000990101080121040d1150100001d0081a200d4021554066000062a010b45817814810108030040040104000f450540205400f4000c1c00714503c1d140d516400e00b00e560380c1040c15640d5810107603241c03a4001d81ca0300c5621000700c2c928000340101c12540002e003a21542024440c00d82c0c1d440c000c002610a8199003c1804566044045015803030742510b40910001b5030007040910b841d00030841e1030800d205049000410604900260046030807990b030f0490515600d441e203d03a6030040d4002e403140e007107680b14620490300d5004000c003510074183c10400c00050781d40c0909800c0380c015070451850f00380c0320802c0280e12541881900d41100303007400c5c0640300b82040304d00203688044855003a8816580d44d10040800c2060300143c1c4c0050621b00c20125001116910000103802190078850260b07844075044409030740540c0e0300d1602024180e65290910111600844950a00f0310082d00e0034104454a07006030b0310103016040c400c9000d4080c007990380c106481130603d0 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 509001555 1250 509000305 509000333
    0x211a0f011502030306060409020309150c0a020c090405073c090b10080610051b03070c1d0f0604020d020a09030b070908030d0e03160c0303020d050c030d09052503 71
    0x440d0404c108200c000e40c1d4000c180c40030740e03104800058496451025082c81d0104c0014046160700205080041c801070070b46c0144048580e50b400d8809881401c1c0a02080f00b038180d034028455000a40c00b0300a0004000440c000031104070108540341008411408030b0917085040e640b040c000401044c03040070014054400041030030b5034009800016020018502700f809050b4900c1060050b0300b000045125130f0030707600340304c4002080b008050107c44100d5641c3d40200310803591560541c000140000720803640f40c41c8000c000941d400789949400321400e022078000c2c500b0340d10540c207000400303034040188080c103030081c07041d15a039a0346415810104c8a01d000200360303000304040c8100900c0301c400f02100f5a07034440c0d0311020200d00c280700400c8281c254090210707200107001d08007120100344030940d092801180d010341c0941d0100d45081008032010700c82d05000b1500c55004018540c400100c03503100d03040c0140920280c805008440445e07450030b6000404600c1110078009003401849989102d01a03 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 509002805 1250 509001555 509001557
    0x40308070906110d1419050702031002070b0a020a140403152016080909160f05090d0b0709181a030f07050603130501020a200106211a0f0115 62
    0x40d08280f0700c080d40c1c0e10020b00d0341030020412186520454a0302610030780d4081a1039243c4041a060102c100802d141c06c0700f9000d0b4428802d01000740c010510910071203080b00d80020a110450344c40e0028034001c1d6006c49400803c010740c400d48140701d844084080d1001d584944845861404040450800d5403032006507482071084540060240344003000071544002820742201c0c0400c0e02c0780c10054598000d0084840d00252540c0400001144480359201041542c1d11008008a8000c40490b00341c001c41c0d250302d4010030007034007410201c4c1e011401c041c1d02046070720f00036401c00d840d803000750803d03040c10b071520721082d440300c00320300d001d6495126070ba0b00414141c000740f640d6984004450740e90561846464000c4c81b00001013118079801d07040450795207401a00035541c0d010100802007001544070400e80051000303401880d074000c0107000c0c40080300c2100d4804407001c8254986a403503502841011580c0b40104140f10784004400070685201c0c1144900e100c80365807400300340348600c1d50356000c84d40c = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 509004055 1250 509002805 509002817
    0xf0209121b011d0d050109030206011509030b06121c0e01140301141201020a171324020c010603110109240810080105130201030e0a0f06020f0909040308070906 70
    0x180450448100681181c0000d1900502c2d8078601400d40416012106195810a09100d89001131110540010082c01d100354205da0460380e07101303580c2c0319403e866240750000840e00002080854000ca480c80c1e0885002441a0404503640d80b03d20320f00404040c030890b850080c040b000c1020307500100c0181c551242820180c2403001754006441082c48140900b03a18100e1020840c04035031580c104041080800d580210754074003d0100242106140304c00540d00010703d0400103640510f810741c20f01a0341c1d84100c05050a035445000d0301400c050311401180029400e01907800724940900910008602070b50700c2850580300d14000400c401800c4c1c000c401c40e500010074040c1718030080b804840404d0b11925000e03049444034100c0d580100c80583c410031581d800c05003400390040100d045514414400d8804021258940051546426a404014102440aa2880300450641d800034000c4960520f405d034504018440007070000719080d6000d40005940d5406c10240a07001810200500300ca42008 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 509005305 1250 509004055 509004073
    0x5030307060b0a1d0c030702120409060f060c081c0f1406030f0138151b0f0706030209040e0f070905060627030a06020d091106030f060d0c0503010f020912 68
    0x18000c1344050084103405500100080383c0c80e20a11a001e0036807600070a5a940b03030354403154200500311074014221030880d14000040c1b5140a1650000460350000505041c40c80e01760b501c20a400744400040812515100300308000c003502e215102034101d40d04013a01e944d043c0103003403501e41200f40c0308021241e8546000d030800b140101c0b02080825001c2242e24006014001d550f203040710b58031100c0d6400540ca02c0c501501d0f01700300303006000351041d521110030005c100400c1a40c3e8903c50304a102219401c031141c00d000f080d100b9002080044400b9101080c08000c6000b010301c5d210340c5800366091600500070600c100030150064542000040300e04904080030440150070710280d800340c2403212021403110100c952002d00c80d41c0c4160380c00440464039405d04260303000141c00940d40071580b21390500c0600c14246000e2068a0040d0315042100c1216500e0b01c040c0076450b0903200b016121556400c0c8005a150b40901030f41150b180300000c050385924070340081c000301500418121142e41c2110b000 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 509006555 1250 509005305 509005349
    0x60a091703071e0905030313091802090a0e010603020a060507030801060504030809060a02191b050405040507051c06050112110607030e01030c0c060908040e070512070f030605030307060b0a 83
    0x5058229907104480e40b0112003e202d003501c0b46281079011541500010880321080c5404902060480709042c000f030010304101002451043c0080000039130050005020580344511540884072841c0698000a05070b0384a8000803c501e5a0b5400100024400510103003050350002c1c13201e0040034107046c158240343c1160346071042c2d0b01850f10418003c5001086a4604c94802c004100c5500b0302e040480320700d500326080917000034816903240b8044c8802c0041c00a03607400c140c40750034410350f084070142003440d051004022aa1424507005040d6807803820899010030801c1c0303d0280204030100031042d91071000e184c50008042c4d00d191f01480390100f80b0031000401d802850707000500109103000510300310011001d840140d44907101600303a6141072a03900030000b4020040003075503e0b1341c0560000e9540c43d8002c031083e11a408144400c04001004500094050400171081d280c0a0401003205034407000400d245412503c025200b0700c3d1103800c22581d5040c90799803040a82441500d0f0260485483c0b0 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 509007805 1250 509006555 509006567
    0xf050705010f1e1b050a0203010b0609010c11030c060f0309060c04031104050a0e010f020301080f2b05121504060b04050a03020609060912030a020706020615090406060503060a09170307 81
    0x92074400c004034500010f81c0707502c104005400c501c0c684040b04110030f00c60034441d5940c05d0000701280298a042e418041a2905800f550005001607403141031010300d0341e50301c1d00400d50134003545030188650380c0301114540e40e00020b40b440398002240d094503403034828003962800360042c01410b09240f08100a1001c0b03181e950143d08410019200400c4a4807561500802007812181d881d00035464007298003131260154000358100d81e908000c541881244210140d20344511420f0880d02c1c03000b4010300c2a8083e09001c0a0204004904216041205034144407503505011560128110b0644868002d646094032502001d4030280e041a0308280c2004041102c0d00c0c05400068070801000c03440d0301791580d604080300c41c020006081c4e5619481a07083c1c06030f030382e040b400e0348002600a119000c10a1440042e100c0e120340c4508203040c1101e01410140402034502810955104d602c134040882c41391003c011550286d0b540880c0056100481d00381034469590381c0c10011722008040042c0060719600c00 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 509009055 1250 509007805 509007827
    0x191809080f0a172401090312030902090606120403120219030902030f01050c0405060c030c0106030323030402030a020907021c050a020d0207050906040e19081b03190f09030f0f050705010f 82
    0x8036030f16204c00c07080d00069461000e558401001102030340d425002c9158541c010211440c030a0340c0d0070000d40c60f0704042003a280156a4294038004240001401180c03094000e5903800070015001031920115811112001556040b00310201e52151f04030002c5090800041410f00c00701802046203040c00c444c204458882d5104080c8107000125504031419400d008075032020304800000c10950743d4038600075101902c00e0740d85035800000f040b104890a030003482103d100e60341c02405004200e160754200709038014080c01c0c0c3c5085205160720603040407000100ca1403441101e031100c0e03450709400c0300d0082c80d142400d0165000c40d040400100041c1d180e04442e01d401002c112004200c0c115910000d9252091440c0d094110520207019041407140140c002d120400800d07803440608c2144084c0150b4034494400c510001440c1d10403501c1001e40b14508009200030b41d440c2404941c0d581e42c071004c1c800040e4400c02e5651b00340380300c1460b04104081005400920080c204a0480c0e203420b14042d05c000408 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 509010305 1250 509009055 509009101
    0x60c0506070815032407050403030507080d0f0207050a1b061718120c0d1e12020d09080306091305030a111f0c02010b191809080f0a17 59
    0x106021542c010000003185070040400360032508858013119401105c002c08052490601501c0c20200b00c450b403295084a007600d0301034464601e0f241d40755035910381903400307103043c5600b140d50b41003040d000c0302060000f881d0550280c00100946000c5044c0381c0e0011081c03400d12407044c4c4525004010352030b0031644541c0d8600444808660702e03a0742c50144c0240131403813641c001e0b20307014141c403050301550028094141c092028046490201905409030364040b1410035414614100380c00e40706036948a1007149490904480d03015040480700c40c004810340c0d507410421900840d011041102500b0040b46141c0e100d01119181002018540c07207003500e0b80f01703540005040212040054100d20000c1140704594000986008441c000c3c0c0c1184000074080c00c070100300103508002c10400280f0b064814500e160064032409180240340c036001100700d0043c0c507403050352507441d0f01305040858104070150121449600080750349080c00080101201e1070030a4895401d40d036401884000c40e2400400c0840900ca = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 509011555 1250 509010305 509010317
    0x60a0306200c0609070509040c0b072f010314010f0b0708210a0e0d02070b090310060906031203090b04080313020a08160e04020607060504030c1b0f060c050607 70
    0x4801416460003055112001d8100002580c0e6500190000307225105598903810703074110720740300c41c1089004003080d50083c00350712428031b041c025444044018081e061107108224400c410b031641c080d40d940c1c007a5524441540a03442c0219003542c05014080c000303c0d80c50032140542d0304041c41100011801e00401c44c1c1d16101145013000c0000d10030444800000b1820148003910030740f011180030030300480d03c030104d2604003042c074400d25034001941d40300401903801070002d107418039482d480650413000304140e2600c0384003440a4804070911842000d042d480b4000301e50306085042016450003038003208400c041c580b2022001288100c40015000b681c045000f0f581c0f5200c05544890320ba040e204040d600c1018050f0005003503000044130700c3c4140f865078107901010780da240902d00000b811140070750069000c201c0d103000503c5903808164410320909206803884c40300c4d102c1042c010030710074421007004c184103402e01111922031803840c01030090745070040450f80316135551a143d8001501c21070520003 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 509012805 1250 509011555 509011571
    0x50601140a09090606030210081b0f27030f06090604110402120916060e0d080703050c0d0f090902040b19031b0201091707050a1113020a0807090e060a0306 68
    0x590601d8000c000c0c5007003841440700d0007080c102000200316521080b4843c0d0801d502e030142403406200c07424420390010741c00407044540703101c000120780c1c0407d428104004080020f04a44002128100c032203070004d0b00ca039040f580c00c00042c0340c580f1180031444180e69000302d04201d152080001c04030b0348581d0008400002d051a840898042d024940c41802c8803501c110810010402c0040d11203c900c1c0719400401496540716806d03611440b52015003034102c3d20b420b5550f03011603500b100404c0010f00ca840c04c42d2404840070481420907008a0203100040e40407100882d045a00c50b04001c040e040007001146401c2c580644146141300700b01340032003590b40d840301200282d402548640d00c110307000c45000413140c9004034024000c051010080b644560002e18000d801e1102e181903903800c2c0e81c41402807100c2851500c2c3e81e442003ca0a0384c7c580d102c01300260b0990b40074040e00242500c219251507020351407e1480026140380c00c1a0000c0003800700c580104040c0750b513503220384001c0b203400c094002101e103 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 509014055 1250 509012805 509012809
    0x6160c2a050405010603051f0b1204020319140609030301180b04090c0f170a030f0c0c050d0b0915190f090218041e030c020f0d060507050d0c0c05060114 67
    0x100e01544000c1c0c0c03003854a000001d00d01e40641100740b00340280c039000850400d030f41c802540c40b00c500340544407801000348082e940c404541c548154000303000400b180d10a0744103486280482030400700445814500c103201c8000349000300081c9800603030481c0503504541c14205510713030740211401d0300a11145c944c0302c04d81d07032611158020240e0603000b11921103a191507440c80301c0c0c3c44180e44105104030703407000c0c00c140d1100c001040d01124141d056803103081400300794034100e030024542c2200b41c4591104a400044a540b800d5403800030ba4850b001c0c0000d10310b40b0055440c18113445400d61400590030804000c000d405400401042c80724640c400034070281c0711039030745000b0080514020b40010300503000381441c500b15080c4910440c400c40074450030201f200b82c0c6454003100e406c401008102c0f5840c01c0c50040c905031102c02924800a8581c2c0013501103500c0d45801c2d9181aa41c2101181d40014000b890394401d00500380081910b0920541008007552059030300c00e414810f0010b130440785c1948181035 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 509015305 1250 509014055 509014133
    0x1a07080d0c03050712140f1008030d14090d020c010f12050411040e031608031308070b06091609031509050a060b01022a01110c040e06160c 61
    0x40554000c114241800101070003c00e425030311180415a5000d119010407010300841c0142d00030010801000e03152441044618040035100700d0007000c40003000b02d1810030070001f030003000c02c0d22000460b110508014070840c00f41c0c0a030000360150070180e84100300940010344020102800e01e0184a0710317130442011555240c1a214400d005d03401c040510042c0290b40311030381d90602c402c64081080c0c2142c07e200d2903407480307428125102c00c2c280060000c082810701001d1984105c031085a038000c41c1d0903684202603a801508125001d01183c8188001ca080003d0156444540310592480c00c49041c0300240030002180700003410444100070000c07920505402c0010f03402d40c0038040710500e40c407514101014008203840c2d64014401c20035820758820805c00540296541010443d1035024113000444144800c05003c0c0b14a1203522040b140a486500c9001311069406c0e01404071070410303c5260000f5105c7c0003990f0304100104440e00d003c10703070ba40000110001001d88581041110034910525 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 509016555 1250 509015305 509015317
    0x30712090906060908011508071a0415050d0c1d1c0c030f1103032104030e12070602070e040803011e080304030c2108040b0f0f040914101a0708 63
    0x105500b046400101e0f40e400805950a4460003402402000300001c654422030740e4500c1208107e0388111020403072504c200008042050701c0140007450f003621084030380c0051450031480c1c0c001400000d4400300040c0d407807040039429641032030318101e6842d00344800c0400c5048440054401c0c080c0c400c11911400c00708000428056100d03d0ba4200380e66030b801c2070164620b052200746c4000c104c250b83c2495500d0003004541c100d60301d50400240311441a00665040b2400400480501c9070800b200700d1282e0716100f80400d0481120300404210b0b00701400241052138541c0b051a45104240910000036000c5095034103490134480018000c80f00112650101c007055406580e070b60000003004414010002034400554500a200803600c0240e115100036030105080c000d02662820300c07050058052010040012684032103440d42800b908015021040d400b83e405030408a07070b200184074142400c0e1071690780c0590300a004a860340d02e401065507181c507007030b41c0403488000005844403c0199803410703680703 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 509017805 1250 509016555 509016569
    0xb0301051806010e07051608122703040e0f100b070803040209220803070306080f01020901170f070305070c060c020d020f0a051906090f06090209130503071209 70
    0x1a00301051600701d45281c00c04108218040d21002251099080c3c44150141440e50740700d5240410349040354043c00c10a1004503480002000111204101031105d030b8010a4514543d1141e0b1101340300440e802c0003502105d0f8020340017800200720b2042040900c683c00042050142015982e0022a4840030b142d44c1100031182c80c0440e5031400c0c001c5070030246200c0d52080d68120960784840b0314910712541851440318050351800d00e1000015440d502840e0808441e0030003240043c2c039041c000b4104070030080443e11903035000c6407108103503a02100700166004070304001c5c94036090101c0d20385030070280203211005250b151000310744114030035220164102c0d00f00f10104407140c00304c44000d458a5a51208000510400800301100301010a2229445038010010819400c0d00042e484900c0000c49040d1135040d41c0c2d801c4000414400e5110b0184c8038400e07000025036003c40d2040089031000a0321244d44248400001703400071b1781c00000c40b0f5415400c01d0000b000d424420400312407402c40b580000c0 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 509019055 1250 509017805 509017811
    0x40b090307151106061e0d030e03121c050606071707020406030501050603070e07020a0b04020d051507081b0a030504060603170c0609150c0a020708060106050405130c020303190b0301 80
    0x1e04003603200c443e142c0c4060f40c2d80141c52840c0c80c3d0f03d007042118142d01c0503a040c0c014a0aa0450852a05103880b240052190500e035802001c0d2100203400c00d001400340781200031001500021b1000c88400c0c3c03207600309951808101d50f00340000030400d41c0c055030310b00808140d50f00400b03c0070903100c001903450441e03004009001450712482c0c218080c05c41660424020300c9400700204007920351030a00d51250070f080d801000180ac280d1900c0c841d9100141c001d1f604440404400b201180e02803002d0300010052600141807401c11982c01030488100174140c0c80307006980034502c0b030b9841d409070459149000380c0c900401d541c9c903176003452001442203034401810800054202265044000098169542514181c032659503400e0002621443e4504541c030f2401c1c0c54500264558100801526000c034203481121101511742d201ca034580301c000e0b0420741c0488c1c800700d0100810304e4460500c015140c1204800e0000400c8a28040d640e8040a007480300c1e121091800351050840c1940810540c0328010024 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 509020305 1250 509019055 509019089
    0xc0a35060601080c0c100c08060102150a09150f3204120318030806010917030301050405041502040620210c01020702030304140a080a0c090c050c061501080a0b06040b090307 76
    0x79500420701c07c071202e40803528880c0010003641c00424a0201c801c00065023440ca50b85101d0380b40010040150202d45103100d5036000e0280d035109104000818184800c000b40b031020f030444441031913181d1010600c001041c1c064641d0307261910003569812680c4801001620395540c04154003500c603541696a551b022081c1090505500c6081c680c000d20b4281c03a00355000e070725070700c0c02c42264070b9074034021000e030b401000104030b80e003403961165501c640900c410003134014403440c5d1041a81e001d5801803000458484100c0c8418a1889400003c0a0000020301024100820710345803081c1108100c45480b60100300084410000e4045403559035004094980c0d441e2075034441e070040c5600489040c0a00c41007400462000d00c001204e510750340d0420b28802085241008140203420b90f0030508080103005e0104012964040200034040c0c02e042d020b4144000660000424a0000074007101c1e080b824000040e05175141c01040b981520201c1a0143e500c40c0320002183c0752508981c42506803103003980c1c807 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 509021555 1250 509020305 509020333
    0x1b05071e120201051906050105090904081c02040f05010302120601081b12010915050d0f0201030b0d0501020c060603010203100b130812030405010c020703170c0c0a35060601080c0c 79
    0x1940c810074140001c00f462102c00d8a070a0101d0b1510f02a8a001c90270421407076041d032a01c100d07045d600510452150b40b034500d003041c500f1542039a42030141802d98020800780140404049a0b402900007841c08508102541d000030841c5200034003d2030501c0050400300b2000e02c140414410301c00a071404040d968480b80303601d854400c8091055181052804400680c0304844210074012110000e0041c0300400c40303900c1e4540d1000c00070400702d0606940f06140005516180800c0b00124014400140c403800fa1020f0281003400003800d8034400e901c10010040b04a110302c81c4042a95070b4420300c2901e4240f0b4284005691006412102e020310a640c0c0c040c182150140003335100c0c138451002840210a0220182d030707204940d0000074a01c10f03060b601d20007907503180f202034454088450122005200b584022400d441d2054002403164140c254004041412800141e00b444141154002207074070400ca815454110151411381040180d5010520194a050aa58440d2040001d5420154448003 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 509022805 1250 509021555 509021561
    0xd0509010306080a050d120f06030606051903120c02010c14010e160b03310602090a3002010908060c0703110d020c04020f16060b03011b05071e120201 66
    0x21059002904110001c6082d110201d0004505544000207100007504440140e40000c00108100940c2c2d50315050141e5080c02c81c040c41c0c0003035004a400060780341c1003100707010715041140250054030601980800004540c40140d110b5150280741c080c511013090710040b2488680c81000be0001c02c0d01040001a01c00c2c194024186e82e000c207005c603080c0d03d02611880c100704070a44201c43da280800c1c00041c002d41030400050012000c40070541c602c402c0700041e240561144404141d50040d0302040145003428410f0f00000905130300c02c0000c801210300b2520340764001041141e00115034a0b2108142107902900890001c2e104890030b861181c03030168a0f1208540002c3d000741c00003504c3c100841400318001c5000c0ba03c20506034042c1050703110301c005000c082c3d4803c000c0c801c4028410411305503000c1c2220031260b0381034480c08012501364078040415094035061100e1500100d0207035070088a0301d801c0400c903011240c0c0303c0c030020408000001074020300c0300c5440e4058012510701a0701404641d0640c = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 509024055 1250 509022805 509022817
    0x110310060905100c02010819091a0c04030206090f18010b1e090f09071101020c0f12160611090406030317010f0602070e0405070803040303120e030a1b140d05 69
    0x5510603105036a21001c2010a80c00000c1460200c1c2001c100c18015500ca44030b81c0703512103111140902d1034076100d060703c4c04460502e4815500000828801cac1c2698000c6105141c10800700f0480500b80f50a603000a4268841c507003005102da080c210044101c0d441e01e401c9210502c1e5001da24a03015a035806c030040300c0703510145002841c4445c000000780c0012003101170303035040344018000041c0070f22113a05200e00684040c1c0f1541c180829102c414025080900007460b04000b0303c1c0103031402190801e01c90740740c01c03484015050b0030308062010b6040c4001e10003002c0144d0b07401c01c101080f4011130785501e500781e11450030b100350000d041080201c1416040142000702040110b52000c60383c3c0d0b00d81c12a480c00005001c0c007801078110003c10000000004403540d0003500a0f4250781203103070b4500b0060324607446130340220f02103800c02d285000903502511410181d81c0502003d10724201e45880000c140140000501001340700a2003601c05001c0300710b55540c500115141103e11441e107142c005040e5030011 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 509025305 1250 509024055 509024057
    0x150f03031206050d0f06051306060807030201020c040c020c150913091104090302060c0a050412111207080a080a020a020a0311240d020a0c0b04030306030303110903070e0a11031006 79
    0x1a0010f018100907407a509025040781e1455112122691908003500c4050300c007618041c40c404034140880d12610421000308845da00405201d4514400641010014601b80e441989408400784400f600400c1548203058201c2e040506440340040d481498050100602d4002d8820380506a5240203030744001380a0b80511011510741360500104000e0340d0055000800680000740403c51404142c0080d04180d41503051040c100743d00c032041c128500348000d0302941c800110f04084111810180085070400342490090304034075041c0b41c0e403280d82e800114001018404002605003c0ca4402d20001c030485500408100099a407401c0102905a059040c00d1003a840214140305500001c0140d5460900b14081c1034148101d4035000c0340290000142c0f0828880c850004c0d80000340e4607644948a6807003900c000840038114140102164581501da40c200c000c20022071045903400600c00044030501b00803d6601c2d03071a020f021b805840740d13603a40300c10554040701703004200a15025041c00d840075 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 509026555 1250 509025305 509025311
    0x5070f03030c200a030815090f1f030c0608040c08100510050109060801030f02150408011401050f060d0e0316050a060e0a08070605040807142506050d150f030312 71
    0x205800000950a0044083d55a07400100350038002801401010340c03004540305201c94454401000c101012400c88052002c460702400700000b003100304180c801c0444c407d00c035000f03d5a0465555025000c8a03004180c10301c07042c1c200140070020b229007610040d1440d40c00341e805909540c1880d03805807000340d4080b2140e034240c42000c0750382e5200300990f0084508554800440c1d9103551141080c1d60320a103026a00500042c0002c03800e211002e004000910080c4000513040303540b841864040c2c641030700481c1c0b04102440d840000c681d10582500c01403070009000080c40034046411618500c184449020b0910742806c0e10014410040349210b19a4000c410074004054103049407500c6010750680104036800038405e84000c240242c1c0310645c0907110f480c107145400c0c2d003038840c1d130314034040711004541d12f034040d2180090001c418814042c5100100ca481e840391801d0900c0540a4016008407044a03079547c80f1a44821207170000e0000105125140421255201e0400410022180340c4150000d42 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 509027805 1250 509026555 509026577
    0x20c010909050c161e0b011d15060c0a0212070612020412150207020306280c02031801140307020105040512040311010324180e01020f030406090305070f03030c 70
    0x152801424460320761561402e282a0036594080907251070442e00755410381c00c4030130841c117030400d103da018440c0340125170408140d89030254046510b01c500b44c401d502d80300c1030b01c148041c1c07055400c0c0c402c688280451390340d42c4a000c200215403a110b50404003030b520203034842d42003114902c041205801d03110b0b030390b03651a032400d03a0040b000141c0c41380d07108040b4410781d5081d1040105a8000d0002c10501d40c0740c138090711b80348564001916012043c0c5044c20155101520001c8089240d03192100f1101c0c02e46003030000c000a0b0720041e4403030068040c0e40d00d400008072601e902c1a071151890510198041d4202d68881c1800d8500a0092004075070440e03540c0319410a40c1e10760b089910a46007120340c401d0408880070920b03001107020301001c0c90044440070504108100070031130b1040d420090803c1502c020445c00181541c0300948080e0662544164410440900d42c0b5010740304a030741c441d800c01d40c040380c2a54245421241031050300400303000d00e803046001e5410507500d5004001003600315900d00403004 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 509029055 1250 509027805 509027819
    0x1020c0d020f012f010b040c1b14010e0114040b10122006030a0f0506011404090b06192c06070b07090f0821040503060a0f0f020a020c0109 61
    0x16040110196100070300c280b03642102d40c40350f00e00741442002c0342c1407045528200c280c01d11070000d54444c1c0241c035135103455202d0440c0c00c00d441841c030010b1702e40c50300340c080c23818402ca14040e140d079000c005040b40950000c0030346640404d401c940740303442562000304110030440d1088440c040c000d46044440108082c04141020503150081703040e07c1400b4040c550074012503480c01c1c0c0080340b8001140110414100b1039503d81d81d07001c003441c8602201400850100b0004010008840006100d14148162031546c0307111040c51000343c400b036030001540000c5903c2e01500085131402041d0071030240c3c4000c0544004c81980c8214040800c5644496006003400030051200c0c12811903007145804c08814405c01000c980e034046500d81180c0035041048900b038850810b0b03c030b041c1140c2c1100086911900c88500c44d400700f0103418207071034540800142440d0034080069100c5c9000380c941e11701e441e1200728004e14803c1aa21410803072081c84030443d50740344044030194135850002000b0707000c1401d400c0c00103944 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 509030305 1250 509029055 509029069
    0x51506040c05120604060f0e0402040c050f07020118030215130801021801030b1203030a020a021b0d0f1b09050103150c05030105010f090b1209061f21020414010501020c 74
    0x114001d51142801d04104050300c0300c500000805060384540c482c1800a8034180f200051030107095840d01701c030203e10346801400152044082243c040040c20090600585150380588161980c2442c1c4188901104100c943c0340c520190030107540a640301415050404180006014201c0000e8854030501d54601c03040f40ac0340121008140c0e100740444c0d11081961080e480f00140c1100100320fa00c44249070041c040c80d42e0400c403508420a680080c0380e4403034940410210522030504040005c400c903010010070704941158100030b0003002d10206d620b0401c06005d40000000c441c110003106443d54900e10031002d4402880203a0342d1006c0c03109010701c0d4010b1400345445100c0c59844503807540c0d1810b0011500c86165141040402043c2c807000701e184640760009010003840c4046080f00c03400c10300041810302c0c04c045d0440c0c13800055071900d01691070001c1c40700d0044510325040d1040f10340b402907007402090045100250700170f162000303038100f0740c103081400c0d4181e420a03422601c8841c80c06081c0494 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 509031555 1250 509030305 509030321
    0x614041a09060114041b032918040c0b030c120105040507140c0a060e06012105060c090a1d010f0603150306050402040e06100302130203010e07080a1805150604 70
    0x309820280043c0074402d582d03161300c842004085c00c0059001e84410b0002c03001410b1001d00e100090b00d461403940d0101c450307101054054125401070b184620403100185c00c11058414050704040d620700010140a01005084014a00c055200b6580d181040290715980c1c85500181424140f020020585051621415106100da42c80d039008124003c0f41100081e084503070619040e1050000d040e0020301c1d10b004006040520744010481c2d541410b10303042c4080340c8400d1042011100d1140540444d50004083d80c0185200454683c0c6e010303944c1c00305102003c07a07000402c01c05111000c1ca400ca03015205031504885083c1c943c10380090304c1d004100d00b50340000418480310000c3e00b0f0140302040042c0d029070b0300184000e20000e00021100866420030b1400c440080f20052164800c00942c00c00000d100200f0340d07150707002c44c5158180400342d0b41e90b00c0c014181c0030400c19050300180f01148198000c07a00c0a00e0702d01528900f549504e85a50340d2800081c03100c0e190041301000c6181800d0501a540f0 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 509032805 1250 509031555 509031571
    0x6050c06060f130903050711040905031b010b090108100c05090102070e06060421050c100503010e041506171e03040303050a090506120a0c0c030e0609010207030614041a 74
    0x1115140c1d40c04000c05403080311039031903100b0803107024114240d0092042074540ca110f520f88079240d98480c20303c45424016500307101d00482c14402c0d00340c002040441200c0d082415203201c1c0910860542a980c01032203502012030b0014020400810542c1c0c000411500500c5104010700440312a00343c103c41c0d038010110420301580c0074503014481c0c00e6059812551054003d0322030750410b07a840c0e60f8030b054941c0b00022980980d0742e6512501c24800c061040814072034040d280d200401352005001041e903c0140b08a4503110b0616001c41d0411000d80c0c54003519501085c1d003445400c0d1114130f03041e40149980f0703007500a803150050358282c4090300400d8402814210018504180c51520305407002da1000007090704008840c64003003010327a500405008440c180e001c0036032480c508042c2d981d0858900350f202d0824001801e00c2c110000768400300703421400009484e81501d41c01030800603894840304d41c20041010f0304200c2920034248528000510a81c01800d000210200b10030510ba0b900c101510101 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 509034055 1250 509032805 509032813
    0x904091a1b042c0103082227140a06140114070303050c0f07030f0e010e1003110c0a0b0f0f04120521070801140a180c02190f060606050c 60
    0x440b403440ba104844445410380c03121415407031030f82202d5011210980040300c8440b4041448425004102d8141320724041c05501e100940342008105041c4016000c41e0501854200c0d0250381919001c2e00500600c2e102014603450786d09006007054058600c0340102412941035545501e500e610802802c0e4034000703d14010740c5094100d49089010b804000c200f4035050714208000b02d40c03a900782e030090613124005d50707440380144881c1d00010010450b440d10541003145520070440d01d0740d1510300214640d1224200010450340482800018ac0642d40d401d10090142213101c0081c000154013040c400d40c21100400119520340b00451005041600c01410508000c00c1c4154070a010300c00415807108030340c0862005900340d1049080007007085030040c2c0080e00101c010050f00c80031010501c0303039040131160a0316070350408a000c8900c2c3c1d1581d160003800d98540c150204010300a008549406010415940000d046420030700c200e05070f8240d08503000c601d854400a10309115809448990744008090 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 509035305 1250 509034055 509034059
    0xf030414060a03060803040902030a0f020901120504020f040f09062004090c05040905180606060a0e0108060d02040e1c170c0c010e0f0d0e060c03090111030904091a1b04 74
    0x4401c098200402220501d0f554140c0800c1d0382104102a00081540c1d80c80507a482c68902000780c2a40d07401031840c04214018802407890b0303038000c0417407440300c2d86050001456030348900000d60b00c020f17001d0401381c003e07250001e000c04000c403a82203100178030f00840c82402440041c1c3c0c0209060b000030305008103240010322050080c410142c100c40c0d0080796030300e00607080c00c0d19038680d401114070030303600d200481c0240c04048041c1d55043c04801d40c0070b00300301e43ea1802d02c0e0000070701420481c121000b80d4100405840003c80c0e0344d035250041685960054801c0002c0c039810246e59668000ba030160700b101d04c881300d074001d100034401c2c08240400800c041203c910354444030307203480140d004003400c0c3e502552100328111009000b04143c215030b003508001000318600c958809081d60310003022142c02403604020201d8404400001c8640c0041e0078600300704081211480b041c114000d154400d039002e400c101404050100240301c01c0204610ba407240c91030394a0f84c0b20750340c00c1985070003d2820700c09018401 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 509036555 1250 509035305 509035309
    0x5041404020f09090a121d030f070603020928031a01030f0305090301090f050601051002070b0a0f1205040c06170f06040c050403300f020a020d060e031305030f030414 73
    0x40c1d241c2041c1440b0840b03500c004260344401c0c90701b00803104000002c13810411000c00d00301c0301207032025540040c0d0160000b0015410503540b01c5e800c40c040c5605041d0002150400c9860b824401180000b454030030400d40d410240100e100b0159520090740d0300302c0148444e2a421400313141d272904070307070744400015007840c010744d800c1c0c445812061031640c1c95541c544811010030101c1d036100034518880c02c040c007901e604240801c000840c402c043c586c02c41d840150306202140d450011901c84d034425081c030300a0300d04080b004503a89c01c042c0040c080d00311b081c08103001c00c01070013600d2542503513030701d44a005103030f440c0c0c43e494020140c085642c00c060b0003210020802500306980294605000c501e04149820f0b1240c80f508070258001401584200d111540b001030303e056400134a04070400b03071504d206064050f01000307503620103440c406031058411a101004000183d40305403052140305003965110002030040200c03810081c415a406405100d68074540c03510b02008480517a224541120201300c07070b00c01 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 509037805 1250 509036555 509036569
    0x3070f05150403080309010b0112182a03050c10030b01081b041205281709010201061505090a0918032703050a0c0e0103030807050706150602030405041404020f 70
    0x280c1d481e100141040044049422000118451010940042502819040018002c44249605110603441e110352143c1c0c84041c041d002840b0740e040072121080307015000490844520744a03200078802d031008130010070840c0101c0c656201e8881243c410010010700003069003a518045440c0c1e00141c9420000750706410140e003186030220416510318200f0349c070392007000034500929074103949990200100c00c1910054a2207403210101801250311440740c540d854902c094180728039103609140c00f06184103164400d5224034000d1a100f60324402d890500640a4803681c00250a103014407014035011482807054065413010a0000c2c01c000400c52032030700d007105e0403184001c0f500d80c1c05082c110180e90010641c00d014002c0c1d8080d00141c600841c0b246400703041c0e01d145902030b244540c2c0040040020a030406c0032940d01210a003403407a6074080394680140102421408030700030302c2d40158003080c52a800409401612816501041200f0681000f60420f4a04980007503100c0034159076070345c039410180 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 509039055 1250 509037805 509037829
    0x618090a050706030608060a0207120f030b030303010e06010e0d0b130206070b04060b180f070305090a02040504080a02070801021e070836100e010f020f0f0105040b0603070f05 77
    0x80166151810599545410010075078001c10003c0d44401d028040c6090600c00250404041c0604525102640c1e5903403003100300050f00a402c1c880041d1742851007038002d401030f1541c1c48004080e80e6030703580c69258111080d070303058840f940015941e5014010505103100305158047d0820031090f00d96442000203800080c04903070490b0024000e1042c0c1e0700003103026611600481c4a130b00d000c2001980c00f4188002002e5141c04010405000d80c14030480b040e102c14896041025440c0208250f82c0b502005498003e5520000b90064034007400c11052000131805010311042c15403c0d5102d0075075902c000d909130b0103059800c4807120f982d1800303c0b420486c0d0000030221588104916400d101c541061961414080c03504403641410b000c001c0411106068008041d00004a914070001d2070b54060040c40c40c00c00c000c00c1c07811b00c4001c7d20314501c0140200072820701069400e086941d02407040202c54080c0c40e043d101100d1a03442d60f80407628914001ca4403a040d85c50040725501410f00d42030822001d1800e403 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 509040305 1250 509039055 509039071
    0xc0a0b090a050717160e1605160303050601020132040507080607021f050108030a030f0f110c070501090501023d0c090e27010b06031905010e0618 64
    0x8585180081c2c02031042d00001c04500350f101c61030304600c88082e4102400c02441c500340c80003c0750103110f1004d012440d03e40101010501c1c001d41c21038200d081e00e007032091a0075032900240c0d010b41202050f515800880c403400c0c083e402400340420a00705080720403407050900720720b00106024200101b00000301c4580c4180030b102102e0354160781e100d0180c200501600d07480016004010349941541c64440b0010840110310020400c42d8548903209859014035101079041584402e40b82135111241e4004400704801c4441c01c1020380c0400f6401c03071050b4800305402e022801210800140e941c01441103204a13001038000e44800c80c144006151089440750f0b0a0101911081034156032082840100803c0e1f00d11840000d85c8141080e0090240c1113240d11484080040c00c042002d400c401c4241c18114168045d005218120080c4c0e0310360140c581160300325004903002c420881d018120409101000170200300c200842e0f602d070027000c0c40081d07080f51050b4000d24052640c0d5800c25514a56a50002c05 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 509041555 1250 509040305 509040313
    0x50301080a0f080d050906040b010e04031b03110d090311060708030402010503040c0f1205010e0d051801051c0618020304050d110a05070b030a0b010c020f0103050c1210030b0c0c0a0b09 81
    0x49404d00b40126503041d6145040c2d40d000344200400c2044803190580500300d11008074105151640e03008007400c150014100e201a021600602058001c0031160100407201741620340c42146144010140092480f09450760b02c6420240b2250b400c110741290034194110980900d1030f615500151500d81c0050030446a442d01c987d030008101c040460310f400a40210101d000b401c90740c0e82042400e5803040350201c02142c10ac6402d1006c9aa000f00845280506401c000c1e00310480380340043e40c0700d00548640d002c05c280c400d19090a41d10855001c581665024942032404100d0150110200c0c00100c60081403079200002c0c504100e4000c2e0742d07103040084280100c1e511201030b40e8580d420102240e0003001d210001009004141800740510a400c803000c2c80c024a80300c0041c0c0015504c120140c41c0d5605056544d008070b02c1c0c110040040721a186514810340040d0b042400d02c01980d040c1c41c0c8419035007140984081040da4071100111901600f900004107004481e80d00c8115440c000a02880c05903ca = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 509042805 1250 509041555 509041567
    0x1030c0909050c03060f010e030a0209062101150e01080a020603100518040201030501060c240b0a080307020f060702012309031209030c030303070507170706021612050301080a0f08 79
    0x207410301840340f24001c0030844075128107011061042e80e0340c007511518180040448095080e485c009a1401c0e01e54044500300c10648503000810503504003581e12840c5484441c0e0b8400c54401d0541141100d0005911708909240d07803580c81c07401c010401e01400c080c903003102403100e0141c9460406941c200d004c0d400050030f081d81d11400561880d81c005181c7c0604040e4008000540d07806104142c010b00e0107041810f4170f0009551940c0310004907008031b0200101b4140a280014451b46c045121100d01804c4030b072403a9101d24126036690013072071080b8030648424810000e80d05141041d9221a039060f140c10210303240d4120031140b6000d140d10007444c1c00304203001d030308804c0e036003080580c411980312960a591040000e05041c104001e0322400d2307009034030410922800b1a408001c0712140313500400700380710045500c0da181d030041c0b04034030000e030495002088115070307080c40c031080316001840360880c251004e40c40130096405020900c581521034004140400103e104a840051064801c1840d2440c0032 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 509044055 1250 509042805 509042819
    0x20a090b03010e0403030e031303140c270121020609190b0d0e06091905070302031006060806010306060e0d02030114101a070f060e030c010e010e071e030201030c09 72
    0x24009a02030010f0080c880140401d00d601482901481d04030000550301d003980010a1500ca8245480020400c03402c1903c5514840410b0000781c00e510001031000300001003210303010145034462122150030502c86000043c82c803240200340c003c1080c40f0121400740b64925000c0101b143c000701502900b203205480c0391000c014482a080000c3d224045004d03444564400c13044089802004000d02e10741e00071400d11002d0080003441003001102c5510300340201011f49449803e20085600007500341c800c0007901062025941c100b841a01d14998800e44a81d9a00c001102516258480d01d000b00f41e610000c1c00090800c0968400f40c0390025001150603030f100d0301c40c01c000715801c8414541c2040303d000140044124584280b0003ca1600f00f00307801c06003a602e4003100c01c101240010010788e030700e820010380030000344191480e0355410f8008102d1b10340b014101c0c0e806040c52148000e16401180008a0b80440701a0302c48014000e0603094200e450441d0b0066000303104140c240c80511440700e5000a2013 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 509045305 1250 509044055 509044057
    0x2040302150a031d010203070f17131403040b1c140a050a060b0706020a180b031909061d070621020903071e030b0604020711040c1407061d030f0409020a090b 69
    0x184d0808000140d4924003c0c1d0002d01001c0201c40300c00800040c00300c42560035207030b500302c40e0300300c0c4a03841a40c01a058a24054000310510065142240030108000030345440a01c0a8880314a07900000400da13490503407401c0856147c2401900740d2036040010071340271211a84041d51045890b0700000703100c3c0c2c0741e0108480c02d4007c0001100c0642d0002480080b9903440000501c20a18140701c9054850400d802940c0134000240341810070070a0701c895141c280c880360413007000103030081e00401551030345540381c0040c410408040740700b81c40354072030011342c00e0301c00e01c500e00f8181107288000301c00c0d0815651600280d031200c02c0407503040c81565008a18040c81840d10200a950100340158032403461500913107550004211600c940d205220001c085400e078060350302c2e400d10440300010701d4558000309550300d015201032542c0792800030820380d04001e11584410400412884040642003041c0c4046540748694062071011580a10003001940480c0d0043c1040044c0d904010000ca5260a0340807a5 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 509046555 1250 509045305 509045351
    0xe0d0506161112040f080c01020303070c0f0b190c1103120a0e1e12031b03070210050a021e0304020a361a0109050603280c020a02010f0302040302150a03 67
    0x80f1100004041048140012104006002c0396001d04142040080040d440780001090101070040909100c410803005406d80001d0a80c0700104000302c1c20f03e000c4081c0207810149140704043d1400d0300300c032407075030252a81e00007110041004514254459101c0c2e4102c103405459201c2242c0c07201da010035141014800310032124440c0e615000e50810b40031100c1d2400c010400a80d0562008005001041c400c41ca1020304e81407095282039900d13140c05c10200d1501c2e40e5914410041c6207040700344080a10703250028102c85408081455030400898921f820078407003507900940c00340c01e0401c20040c1c5078104200c11740f6400c486a203045071022005910400386120110f1010781c0381d803400c01b89400000b9246400c0620003c3c40c1111045044c10b0114120f4407000c0d020344024400112412560728911010005100750f0742000e02545102c942c0180d41c41240715130481c00700d848458400034180c807920a8808807500102007405403003104d261503a6960116011a0406440342d58615081c881c2c1c80142c10 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 509047805 1250 509046555 509046583
    0xe0a0803040b0601092103030507050c0f030918150d14010923150106120b0a0f03050c15030109020a0e0306090601030212072d0e01090c0e0d05061611 66
    0x90700340f400c40c0c0010148101d9800c14040d45500044442039018180c511007581c40d810300340000e1303a40b03c0c00c905a03158080e491080403180b0445481810a00c000f0002d0508802e040d5031021a550790801007400000c0125008848000400b1818040d0f10740403111802c1076001e40c80c403908401410b4012400d640c1c4116041d2102d43c1d03452841000d40e181400250103242d03005c0b028080920b80c0c0711820762024010b10811040189000359001c031600c25034407082d17500c28002c0007041c0455451541c0700114619200680d0280150303008082d81382400c00d2081403841201c10403510b9682000e6070200250003c00c11201000300c40f0407442a180c500b08107072030040505600414080d8554410002464601803040d007507604000001c004540e201d64400211a10321192000174000510100c0018401d562000b40034090703070b10000410003142d0f4003030342500d001c0d561801002800030040c0301028900c588020b2059110100148640040d603c1d0444001a00e1910820612a00c080140341502d8240040 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 509049055 1250 509047805 509047823
    0x3060608030c030d0f110a090e060409150903180e0a0506090106050412050309062101060e0a050f030a050114070f090e0a0f0e07060f0809160e0907030b0f070e03120d0e0a080304 78
    0x110807100327190305040d4440421a410320808540d9034640b1244a019003181c0700d40c4ae1280101307000c01d4080c5c1c40c100d211a01c2410b00742002c5a81d1071510b00107643c20342d03070100758501e420049010341c108540e401d41a90f1003604c034240b40c149003c00d615515000c455041c0c449006c10f20820305240c1d100350040c181903041c1881843d0b808045021004481c1c0c060340404180142d0f4801007401e511078001d0b90f01240c030210341c1d07d180000724601203800d10004440041c49540f0307242c010182e00300c0800c5058021407859441510342040e1401c1514821070500403038018a03802d100040840072284c0103038030030322884800403c041c810380380b0079840e06041c0d40040d0040345040031000300e41d5034410380f520f61000c0454014100140d0400241c1024161030103600340f241d19040018802d40c0c000c20528004551002c00c442d001d18056407900c014160a03205d581c0010030848948200e80b900146480407090103081c901d280c44103152000780104101c907005181c90003440c1e451800300b07003484003861060340174620701 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 509050305 1250 509049055 509049059
    0x9060902030f0c0a14030304150c1a07090330030e0d0c0f020f0607050a0c0e07030203090619181104060518010909060209091003060608030c030d0f110a09 68
    0x141003042c1c9409400e0309a10002c459401507a40405400c2102e150400e02280c03441380e880401c0c00c500c100d8101c0e507a10081000700311101913001c001c0064490240003085186002000660351a03072080d26003c002429207034042c4045410441c0e20030307140b01c3c2d840c50701618007002ca00c0b0a1b2065410200354010030355030140407038802400d100640c0007202038902409125041d9550800a000c40380780030340110381e80180300321243c441008483c48560002c04403101007502d40741c80345098606010b0f610022103200003043c1c43d18024000d80c1d0044000b54041c04590b600d45145416180d090b001250f4500d071150042c115000c550111102d0380c0740602a0000e0344040d00081c001924800d5103c0d50058010b11801d10f06024402e10003419160504c41c086000140350620a0280c05284d900c258010300c80c83c180b081440c44002138600326442480140b002c07560780c410003a12401102c1c895039141c0c10411101c22103407125407040441400307607000000d400e20701401c00152900701031880e130042481d901003 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 509051555 1250 509050305 509050309
    0xa0b0702060610020a0f030513030b190e0c04110919090e030a1b11060a120b100c152403050f0102180d0c081b211e1009060902 56
    0x8160302507020ba07070042c00c0083c1c10710002c3d41d038605c51070042c040d0002c506407101094450000c452100c10320608020520791242098a44050252114a000c054150840c08418842d000d1303041c040e68060040c02c4695602e03424000170305400352104850703040800030107209a40b1407030b510014504411a6001c09402d00b00b40108444441c801c3c91915131050000c900d20740c0e488881e010310141c1007140c0301c0070000ca503d40010402e45043c000c0754051004200c101e01c40d90710a1044048510380c010903c140c0c0107c10901001d01e03161611580000d110810183c00704d40c28254070800041021400100805182d0501440d140140040102e1008100341001481410001c12001d882c5980086141c20440070741c420014045054a130b0103841d07a44010401c2c4004c404444000f07041507019034600114a544d00301e015040148554401e0500c1e02e5110b0459403210629408600010020409011498100a103220039419001454860140b41d5420f200440c00b0700d010710340c4903110208a5003041e00c1 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 509052805 1250 509051555 509051563
    0x40309031704080f070e31140c0109180c0c0204050a05160201020f030105040f0207060e211309110c1204050112020c0607030209120102130821030c090d050a0b0702 72
    0x2000c90780200d01c180045070140c03030305031f4004d5087d810319094031174922a280301d040ca004251200c503104524680060020f50346800c40003001940545042e01a4203005507490040340c001c4691100803440d00740411007507a48120310850742801e00c405820815400182540c004484403000c40d910f440c180402e100c1c492a01c190b07a0b020900013582030507071400d56a075260105104462144d5200c0c00410140041b6604481c180b9400c41070601c40003003100001c558405603846080c24060355132003808412600141503442c1d03c0c2c0e50358480941d07a4a8045201c02400a5083c01ca80818007001600d802c03020402a422042211081c00b50315142f17800000b4003604001c40607440114010403065003c1080441c0707850380511241030058482190601150a2a2902840d142d0300e620000d0004000711406881c07108440d06c0c08101c0d05000d80b0998000c1d00340501015400904500380089500422510050307c00508060000d2600d46c1c1a515a1450903884c01801c3d1040400c1800744400168180 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 509054055 1250 509052805 509052823
    0x140a03080c0703050304110a030204020d0b0a091802090a1512030f0c0209070c05030c0d050d06050103090c0612090f03200708030f0c070803032e030b0c0304030903170408 75
    0x1c0703140d810300e4003546002e081c51100400c020300b0014081c1102400703030782d69454100a1600030700110f460f420f001c80070350010800c003806e092003003818030030000e5883c4090294a00e5000e00c40c040c0c0003001a01d03401d21605040242020284c01e890700108449400e58042d1a001092042a2403004d16002d050140503c001c0110700010402421841009602c400c04101d4100d0074a2030f01401e03200c05401c0c85815805402411070480c0182e125508506a00c0005002200403000040140640d10801541141e01c5144001c0208081c0300b006c2040c07501030210f5400711520080701103080405550b900701141640501100401c0d0002101103440907401e00d48401840c4590040c500369040002440c1d9901401210341901c0f100042c40301f84085081c01020024007141084948a09009010841246408c40900241d200b6014500071791806c0c000088126500112410001e40745c140800700d06505c01402501031019070200000000d12404854118024504429842d0f80c10941114144075242d = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 509055305 1250 509054055 509054071
    0xe061f050d06060318110d0519051504170a050706050408040914010f0506090105040e040b09240402150915131a03070309030207032f01110706110703140a0308 70
    0x3494117617034140c89006025500ea00020b0b4500c48151000c001031050b0440400100680206c0751041d5626451400a07141948107409440401824480d800b4402c0b0f001c80c3d018100c021582c10200c485021100140fa5083c0f8916042c1d107000b040b40c450070284d610a690407900b180000408000d90011485504900d604c4140c0366404c1c1d5240a1041c0ca41d61010700440f48034003c0000d0b01441c0da80641e0445004048518440310b0626141c03c014040d070358202d41e5001e090140d60308540ca0030128298408282a0752420090b0a450f0340d000c1c445c9544250015000290080000c0343c0d0316a5100509495004c4440c4120751f691010040d10700400ca02c3e81c48240e6030030342440000307200031000b02900c0c2e00030503a203000940d50b0401d0808910748040c950010b031007111801c8185c007165261107404840701d03215004402c421400c12004484a2607612964040f942201d6020b0000903c079030f107010000a0928102c48042d0744a8603401c150700100400c4280903030010810f030b02055000151070764041c840f = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 509056555 1250 509055305 509055311
    0x30a08060f100c0b0a0e0a0b010503120301061b151503030e0102030a05070206030c120112020103140c070f06060512100c05040609090504020d0602120a05090609070e061f050d060603 80
    0x1018002c3c21852140c00c009250802d407000207102903640c1d07888800700324101350855040d01c400381840101c40d6000e0083d54081e000c1c00d800e04141218650881c0d04a5040f982c0c3c2951079001b00340456160302c86640121040c0e422809250300a04140c0034018400581040210707072140b46281c041e0940801c1002e40b03040d50002c1c003c43c1c030465000b42c1621441a016100d050342c0755030b009070b06102c900c0f912012100d8080c04400115100c0c9940c420341c03143c00d10030b880070407405000d00d11590300701c002111981c0500030100700030340c00105240702c0e06c01d41520418000c20300030380300c0c1300140d0410500ca0311003449038400f0640e0783c090304003800343c10300c4100c0740d043c91031425040403070052412805008484840e80c0340d001040854075404a0152880d400c44030854076043c001e40b450b00340900541d88001854104008108c17413040200702c4a01034074121008101903494800c2400e156040140703c81e078858401048000194207560300c0340f072240c400e80d440c140d4bd0b02c01500141d045680c3d903003040c01014170f = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 509057805 1250 509056555 509056579
    0x60106050a051804060602070603051f05010e03010906060b07200931080702090f062209050f1f060311040902030118080901110f0601030221030a08060f 67
    0x2401030111a103580e800c0ca081690343c00040201c40c006119048450703000742c40c1010005070f5030b42c08a010707000c3c0c41080d41c09004944410000e5070382002040011141c00039001000c0100b58000e030848400010003400104000c40706844050483e0a6540049101c44001807540304000488103a070f401d8070205c2c49d4508101611402091610400030005041e01e580c491128030a0200d40c403500001c1d21380c84030044030541407171400540a4000c2030b4101e0040b110711010440091045082034403540c0c020f880d040140950410420704036110904c0401219900d07449040410002d100310580791444000402c0e010702501d4507809a10351200e005010342d498044240300180ba0300c40c06030b00700001120041113180e00c60000a0050401184c2d07000c1c040d600c145004204141031010386280b00f001d890b41d0200000d01c901250702c03000082000c00c020b0704410300620062034110322f14001020b03075444039041c01d1a01c15555103198000f50072640800c0020040201e05e25201400581c00c3d4829a0240e00304c2ca = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 509059055 1250 509057805 509057807
    0x506120303040c06140408071511010203061323180c100206010b0724060f080109030c06020f090904060603050c180a110c0109060f05010f0317070503090d0303150602060106 76
    0x2550f0f80602da0070011504500b1440c3c0c29010b064501500310042681d000e00c0e52164a03007800c1c101c40d00e4000224103a410720031314490041c800d891040001600e6205488280803944006002400c017401010006542c100b18a20706110224414000031010140042501c0c01503850305082d12000380c4144428041740050540c04203400303044030380078208580c441c01c183c13404881003005807041500685c4102e43d0480a4036280e080103044a031119400c1c0c000a072101c03a40d909031415480050003040303000031044000f031800d07401420503076400e1242c5410503500900040c90050140d40035152203481d2102130050240500c40c0da0035075031048608055074140c0c44182c4004180080c02c0c01011660b43d410018450307550f01c202c4408011090007002201a2407802e400100304401803417541a16101c000b14070152424540001e99400440d040010f00b405d40d9403203055808003c0880c2c580c0030a00c810b0100d51682000007a009101c1c0d02c01240c1c408880d0f030201040060b560040c400c42d401140104685 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 509060305 1250 509059055 509059073
    0x6090c080f0f0720010b1c0b0907050f0d08070c1214031c1a100512010f06021203040305070818010e03011a04090c050604080105011a040806010e07170406050612030304 74
    0x99409080e60a812100131040034010074048030841e401c20717560403000307910103681946455614443e8144801035154038155a80d6045a4000c0c02c2c0c004180d00c20307904441c80c0c40a0354500c43e52040148a00e00300c0d00341c2d15004c0e40401c03984007464044050150000700080c10040740d05299000b8011418240ca21312129a030744950685030340402e540f10120300c01c8443c5114036441c8048003610a4030104401d0600401650000e1030090341c0640010010400c400846183c508841d001e038000c3c55041541c00b00e4501981c80504101c0c1400020440c807800503800c1409448200c940146070503000400100140080c0b2021044a01c66450034420301030703000b035017080051064402e50340010040ea091030103081c010380342d8000c0c5170b00100205000800d1601500080e0688020710083c2c280c18450f02180030083c025401100340b10340040c001445183d0445442543c0b0a501c0e142140c54402c0b24544240d1440d07050301c0984219469000700521401c1441d1080181c0c28a08003c42c5140790603150342c42c1c0 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 509061555 1250 509060305 509060327
    0xf010e0f0115060c0510060303020d09091401090e03040f0815070c17030901020706050c040306061508041716140d090807030b280b090a0905030d0b010306090c080f0f07 74
    0xa000d0b2800139441405030400004010080c20341040060f640c690401039581c0704260344c29000283d06006c00b04000c00035001d422001c2003610303032014441e4201101d05010f00800d0b1a8039100380300038080007405401c04580c0b02c00408400d00a040440028041400c0c501c00040030381e410310803640c20b500300207a840030300b1005031002e081d001501e070348860310042c0c060311031240302500302420102440390b03252a11009000b2039200700020400560b65500461250070744448103008507e0203c0004c010034541c9100d03c4415000140720b40c5419609185040f80140ca8041607c0c0100d911a00104600041011060002c0309003040c46280b841c1c400120303074406079400020a100000d9001c154074660707030a101d103007001100c860900340000310b000c1d4000030000102520f124181880100c0e1140f0034a214255007030390404048c515109141200401508141d41e5a81c109035071648000355041d107600c1691590840b40d0760307007000c0b4101880b0410740c1c10805800c0c4c0450b45c84c0c0e0018880016003003181002 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 509062805 1250 509061555 509061557
    0x4080303150105090d0308060f01030506220914010e06010803090a14030316050619150509060d120302130801180b101e060f3207050f010e0f011506 65
    0x120042207a004940700c0c0910b66103682c1001d00c2d1881e820801d50064081440360b8016104c0144070800900110140c640544080d41c000b440c071025896102c0ca000c4a8422403000d2046c04981c9030301c0c940c2d80c0030012582c9000a400c59550755281c02503210103002c542e005080030401903003000810030000d2600c45040c441d0360040d5441c600c024410b520207000340d030144556503131029818001800d00688506007103d800805000e0803442807603141c251321a8210424138003611108490600003030040c0581d000c1c110f030340d00000302d03610700002030080d46102000e01e19075500540c640c002400c907000702000326040014a07034144601406620024820509402e8005240c52202d403207003500213210f13000b181c02010400701100300320000900c10b20740f070340c0464440383d940002c001221041161400380c00048004111610b143e090540b801c4190008444c0032646c049510300400340d6100d502d08074450640805a944841310302c0d41c1071005200c40c0c002e21410308020b1084c203c29003800401c41926003d040 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 509064055 1250 509062805 509062831
    0x12070e1c05070e07030e12030f130f020907180e040206032208070305040303090509060f040e1002071101080105010c0312090311010f1a180a0207020d050d0c03030f0204080303 77
    0x140a00504002c2e440c001e06108030081e102d41040e100080140640d800c013108940b148807411008025108101c0703100c0c07c000c100c00c0f081c68990ba80c58400c2c2041000303040e030b40380401c0c040351009603a42001c0305010b1030046c0c032030031b401a4540d008440f0303c5407240d1160b203000380408200405602c0e14812680c0c04428081e840e00d91b00340e03541c0c0100c144a110440602840740c0452404105a0410001d10560b4082d0300d9070300415075210104600c01008940c855003004c00305030590700300d0038603030000d9890f01400000e6850004460070058100c0c1c000b81029940044101540002940c001a0042c05000286054a10610262000307032964074540c0300c2d00a00d40d82c0c0c2d0b00c51401d0501c80d6051661003001c0100a21186104c4c03116034014000c00044040803042c0e101604880380b0b005001d0a41e006000d40c035603aa136a07503040485000390000c076004c1c2d0700002c2010030080003840a001d12600064540c80c3c0701035025650400038100e4060a61000c0602c0c0304000600407024000700b41c9038882c4004482d1 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 509065305 1250 509064055 509064109
    0x110a12020d0e030a1121070308040302120f091c08071103032802010c050414010c020609090915150f100c0b07020a110a050603040b090712030512070e 66
    0x80d07004101d180e88000d254000460f2a505030380d44034507103005403500807003103484000c070390380c092484a800c1640e2610402c1c02005280e00080c041d2100c039034014003c2c01501e083d11900300800301075a00c4001042c00d1030000060f0340d80700c1d02d0440c680e800700008030915900022485d640d0321000d4807030204007a150b008054820021036901300201d501d000c1003691a83d40c0d5010080018400e104060620301c050b5003800e102c000001c0c4144103135000ca510030300070030141d511032030010369030f0302510710b1f06903040501040b003142c0c10f0b22103041d120f0203030f014400205486e00d400e148000c01002c01408220083c0312001c050b616139912407211203c061030840c0c030050b01c035600000c10b036046203c83c0c5004003080c0c0e1540800030503603000b24501003403134040c41c210100b0244840412001c3c1580b0b0003400e40c008020710100d000304428421913580400d1000440728003035101c120b580303060b40b070007070003100080d000040d000610311480d42082e4110300d160400342940e402010000c0c0c400c1d41550203008000007100c04c0 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 509066555 1250 509065305 509065327
    0x103050a050c0f0f0403150204170a0302060114061e030603070b0721020c0d05010c02070f0f0e1b1314030f07030b06032508060c03010b09010f1e0e04110a1202 70
    0x700c9000f55841500807e0201c024409800690002e00c2000f92070680e60310195990382d40840d15015055040c0c3c083d00e0f2a80c2801d075110000c003034500e03a80350810010710a960010301c01c01e001c601040d804c140b20301e8480c03520001f010b28258183d0464001e25409100000010341100001c0b000e00100240510303681030b0442d41203141c84240018981d200221900303550078041e0661202c081c4004607402d445501d0380304c00c48828006c4491244045028000304200710341400d0000740c035000380742c081c03c080d01c203641c600c4260304580100c1c5000c0d40111490604111440700440c020113a4a401d50250125008682400d9282c42c96484003415440c040f00001c1c8507a0380503c44120034113809031300ca0a0103480210725500030409070042c20350500c074050100300d02c09074440599040301e01c440c2d13015161001c060011642c080400c980301703061103003903810360340e060245200340c16502c0c94541d02c00304082c0c801c81c1004140c0b200149000d84425080000d500803c6d404101100f10102c0c1c42c030056510b41440c0c035 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 509067805 1250 509066555 509066557
    0x1412100b150d1e0b0105030a0b030307080403030e011e020a1119030302010509010b010509092a16051005060114031509010305060717010e07111e0102090103050a050c0f0f 75
    0x150314114900012540b008094651003103140004050115210810301401e81c030132228020705050100b0018000902c2c642e0709500000946030005d02a00e040540300c1d030391100356820607002140840c4810203c0400c6591121456441d058460000e16903032486800194a400c550300c005060920b401c2d0080403241c80d9014110348140d04034a2204ca90743e62814000c1c0244810f8460b9040c550a002d1110010742c401ca060390003800000701384440c0c03621903c0d41825100c4000980110782034050010010b180700b1100a000c0512510b21203c660381c40c1d0380b80990900c03580508419055150000340f00050342d0002c0200b4400d5184650140da0703445400e4031113034608008550035840014800084104031000c50a10b000340b0194071455045400310f1a40034480300f09004080700d000404001a442c1480380109401d40360500040e900e12850340061450400301400e4102c0040c0c2d00012500b6442d40c6c14411260310118802003080107040c0519007034501e01c60b003000031000c40d00c0400c145001c0d00f0000 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 509069055 1250 509067805 509067829
    0x10905060a02010e0601120b07050715090b0105030f120301050d0c0308040902210c0a030513020a030c302a03060501090b030d0c060e150406061412100b 67
    0x81020381c85101c100310080c0a4402c940110b80180941c600015819108202c00029194072458403c210340c0e031030004a91980226205860600724400d17060ba940003107204144410340141d07070927120f0350705100900d031420417528440c0c0380d240c0c045a81c8114803000c400c03e8905441080318032034803a00e030609100801c424603401c0074100113000500054540400d42c0200740c1a00c00015096130440b80c5031030040d80b13007002c58005041140401003401c0252099020a501010045905c01c1c142c0143e000304002c60300b03a0700120b450010b100018043d2035100a0500f03002445405503a2841e80c5440169400c03200000c0d0048c00d20040d40035203a80c0003040000812030000000c0034001065a0341003c5026200030300c602d4881034034050008086040c04603940c0c14001d00c45d2107044051104c1d80d5480010310b00c00410f80b605015500c20003214070f0945119501030b1780100c102150545c1070445141030303405103010391446200301000761540a08080b500606c020001040050341740c0304c0c03201007049403200c8 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 509070305 1250 509069055 509069059
    0xe0a02011e05041a121003030801050f0103060905090a051204032102150f01050114090607030e040204090f0e0d081e0a150306090b0a0506010c020603100e0c03070305060d120509010905 81
    0x500d0131000c000c65500b01400c0d45440d12404c051880d02c500c0c001142c400344034040500010031060040c81282042ca41ca621040410324000864503a100c415030110382c02500c2030310294000b00b44083c1030242c20018111381c2405d460266282c60301e10707a02c16240c0341c1c620750b241804040e200e4005140318000c0c00002031003000c1c03020712440b070319000b00c03000c90388002401001c1c041040d480c24a10031142013030903114804030284c8620318013940c5031070590b4001c0038151000d9210f0f4081001040f485031a008025030706808140c049403a0303035110a081c0c22f003060820100c04205400007041070364202c4522860800c041c5840182c040c0e110b01900c00041d2400c0346441144200400c000010070095030312640c5800e0203007641d02402d0f103a095030075007590000d43e14103002803a4000001d0144c600301d4002c40e08120225001090195500c00314449010301b2552400f0f80711010040001c0f0350f405015096210710211211164640076075918501d40200d40c203200300700440070034168816402038007500301800b00 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 509071555 1250 509070305 509070329
    0x3030b0409050d0f022e0b0d050115320d03050c07060503070807020f030414030c0a06032c03030a020d0e1002130e15060a05040e010803030105040e0a02011e0504 71
    0x1101004e05003a60f00c0301c80c030005204040b03416001aa4212105c0300d00000c0707549541088040402e800061304500186030b40c88a590034031400003038003d1040f04907208130100c035074001d9441c140308501c0908809411200650404c2c41c010148480b043d00120013400886034103444204a0408442c903001d421030a6030a48945800440e0f981d030031002551141d60740c2da403000029507c05000301c0e200d404030b41856009a000b03100c02d01450300c12a880801c0441c01a04403807140c800700d400103514880c03d0f4020404690345480075000000042005229154100c005003500d080e005d500c29501e2200402c258038507540451188415500381d00003400300c030096800c48011007214940e40c1c0080d4011040d4072103110703070588006010501030350320b54481d0115440100184a408040c044c042c2e00c050405010800200004541c00110b1548103001e01029001140c5a40c100805d000c110788c004681620035600c01a094001070703a203c0700700c0062003500d00031008400507a04c4182c0c1c1d103004030342028922400e = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 509072805 1250 509071555 509071573
    0x1e050712090606090b10171f12050106080a0302071a0705030c060f06030a111e03030d0917030c07121e03020c1203010501020709051009020a031a040204050a0303030b040905 76
    0x40183c00400584051200401c803c0c0b00700401c101c8040c80210034034000c01d04521803070b505141465036981d88440000d500031071941c40c00c030b25401031941ca50083e01145904c00651001c3c01424402c01001e082400000c140c0c021003518003139070701c0000e403044036030003048c8800144501a40c40e098446150303005c401c4030b40f2404400262521110129040c5844220000014889240019100c2d403415000414481d5040150b0207100099082241002307100040004211254801300002c00f01001c0b21400025031844a1401d40701e80080c4204d102110304007802400800019502200c82e00740d8070048260503100504000d490404061000040e65451003201d5101c940d0590001c2c0380402d13112041d00c040100c5160700900b02d00083c000c540c0140d211134001c1c882c0d00b89940c03040303400000d032400598007181e41d82404802e0b41c0c01103100c0d50003e0344801207070741c404071303500c40c0b44040d124221390039802d09050a0115040c5200d40c44040c00301070701c1d0422000301303071503541c0500d9030305030000309450707000c0 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 509074055 1250 509072805 509072813
    0x7050a0f0308042d0f0804080601030b040308011410110c06040f0e0c0c032502030a150507080103020f01051e0414010f030209030316050c03060702100f1e05071209 72
    0x200044a041e0341a03c000e4036407100e02c0f1600400c1010341c0104100b08a229411521740800c070001004041b1100d40742000003245103e410020103008611804062600d890070340380090440030107902041c013411500c9203165080c1d0700e03c06154060340c464a06601a825100142441c000e1401e4000b500309400080120b0095011201c81e4181e400000c014007090b181c0180015043c41200d00004d00794006115041000c1c03004000030725240b4008070039440c44006a00007038100b5202c800116401202048050407504040c01103036030219150809803540d42c5590080b80e00c1040348601c1c036041002c0010200d131358207400d0b002c0800b00d5401c01c008940b01c2d508da01d4943e00c088402d08085011408510402054900c00c3c02160685600038000c0c1d03003003c8486101a661364141841207803d80241c117202c0d04107440411500c0d1040c0410340c0102000001d00c2188030498a10b4910810720501b00788480403440006c04003103041c1c02c0c1282d80000d0a95039024101c6e03a000003042074804180c18422124140 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 509075305 1250 509074055 509074067
    0x30a0f0e030606091f0915080309090a0203090a1505040209060409030c080f04080106030f020301050121020d020a0b0304060606030c020c0307031e08181008040f020906150c010501150903150207050a0f03 89
    0x203410070b060f0549070072303441d2680941d4900403206105d03807042c0030301c0005035111010f4000c1c54001a9650851b003400301950b445a200201c198240481680e4400400c419860710311a4240c000c1e50a0350304205d0304503140c030010403d9504000103000e00c00001000345c6020082d034211801008281c0080101e19124502030031845d070742020a034401d41c240400481d6011b90303400c0315180031140c45a58207440041e41d0034030503d900300c0c2c1030507680b1668242c40000c1441004000318415481554000b5041c1e0400c0c0c0060304070f8401600c1c45003158800c10403102d558078001480c100340da4100e040102141d584104000403e910b80ba00288440000f040b000505050950143c01d030490440e100c0000031500002101d506408460107024101d0103983d41015090007401c2680118014020580e04420003400a02e294040300580710075a642e000100310310a0701c2000042c03000c25072700c0d0541c5464517549629290a145006040055900280d03d03020410200210800d03654042c180c0703051208182406014 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 509076555 1250 509075305 509075321
    0x604030f09051002070515090303270607290112081305030d08010807081c0302180a17070e060904031803021305010e3405040e0108030a0f0e030606091f09 68
    0x2030041c7da100e10408409042543d505003c098020760411030728042c13100556020780400c03050030000d01d0f15810140c1b22240180022170040b1600304031a030480003402491036441202c3c0c41800e203030000521881036004e4803a41e50303a4020640c1525030750b9100c1d070000000f2890f8030240d410300c07440b041100e4898010030094100c1c0c1d250000d0311a010380c0c80041648403d54410302e03d07007411812515150b03560190740a000d5555056002c0d6280302540c20100710301040c15003180f4441001020800380c2c5010822100b8064800641100424100380d404103581c0c10780504001c0c1440403814800012501a0305240010350300200701030b0054103400e4420b00140803c0c05128048900003000a92640c807109030140c142c28000c1d603106005100140041050104c031011004208040000150508080c40498040d007140c8018554501c00e0740f10151100c1c01008113070b400c1c40740030000c4c1806030388d000c546103911800c00e403042d440568600c103e400010001400b0b00758141503c0310081444516503001481e = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 509077805 1250 509076555 509076559
    0x20d0902100e090c0705190813060c08090d021206040818030f0d0f03020405150a0201060609080a02090a021c0c0e120319020c0d11130e0604030f090510020705 70
    0x14441c003194003107400c0204102c0a03504941c0f00c401103290102e1503001401a607005200381d80c0341c80840449070840600c4d05d07400752210840421044480d000300350450380102590300b0040b8100501e40d40d0700d00d4074020944c5aa100365420949c10040d9151720180840710030044050301c02c5450245444c5441d81c0000c4510803081c424801c8905050800081030141c0c11005001000c800c101840d0031101550308041c007030201a0280400034454982007000d0042590405802b80c5641c580d030300003421507102d81c6c1f0034820450840020806450007048207a0301c240c06440c403000d19034072440480003900c0b035a0031014080c11700c0750100b0b180740358643c80090000c80e91780d10203a464607043d0800000d079840780b0700440150030412182299080b0f02d803000c08128090f0056440320402074000030004c40d020001501c02e4071078810302d4075a601d4089a04a00d4140041d0200301c006800007003030f0383e50103000b00001c003488419061260800d00440040d4000d103401460000590840c0318002d45404940c81864 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 509079055 1250 509077805 509077819
    0x140f06014103060a021e03090334030306081b0d03050901090e04060e0607110705040b0d0f030503010806010f0308040504050a0b03060c0a030e010b0f21010524010c0b28020d0902 78
    0x10306d034020382e00c00c49000b07a115400550402c800041c921300c01d00b030a54410048040c0101842e2500070507200300d03094480c003a440004a5500e0314145a050080c04808950100076064004c0d5040c0d50780c000c1203030304942510706181c440d101280160788085894109107202c0705c401d001c200800a0981003814008800011380352aa200d2100641d05005c2c0300440a125030070281061100f410300ba402800e8042c7c006010114000e0907481e54003e2682c401e900781c001030070020040c8494601000395600400390301d104020241e14546840c0804d01541c0100352149881e0320114001c08401d03007083d11200c00c000c00ba9401428010040e01d030a6000e41f25a4001c41d0030311b8503101c40c4c00c030103114049400c08060640c00b08074285d642001400d01d422105016030314606004a01800400d1041d02e10404044030541030b8080384d1181089104030040340c00307040011074a14480059201c081e0b0310342060b541480b00300072100001860054030b009582c606011840803800c2e0f010580c075078100c00c60a6000395880 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 509080305 1250 509079055 509079097
    0x231006051201062103053c0c0a0320010c030203100b0c070501050307021504060501140d050d1101091403030601090f1d1003140f06014103060a02 64
    0x91403d030350640c0328211600a1511000c10101c081003a44400c0b0742c40303440d0070b61030304c1400200984030820341d104034510b000e01c08080ca0007208040c01d0170070312200034201c100d0801031200d00595480b81051401400c100030660416402d82c1c2c01103c0074000c40400c0c00920111041c614014000d400c04c45541c491403c01100004105950800f21100c10a0b2400034100d400d0400b00103482039440034000c1021880784580b011150034010080380d01581c41010b0114103035140413281461103105e011074611600280701e104000032000a4428070507078482c1000c4078036003071741034600d0700500044101901c440742428120312800c0000c0021481071801340c0b1061411601d400c0024540a8140203c0403030451401085140c1d801c1c07200c1c0142c0c03069400301e0108040c2d40b26074448030300e000306100760201c5a01c400b81d03030100e40304280055405440401c8040b0000c1c1c0d071070300da0304c0e00c0d8100481c1c102c1106014501d1140082c007049044100c4400090304507505428803c0404000394400384507040b482d00000c01d1 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 509081555 1250 509080305 509080339
    0x109060b0415050405130f08090109092a020c0604030c051318080708091518010e0f150d0c02060109110406080f060d020306090109020f0a050d23100605 67
    0x5401c050106a402c0101c8941007909200040401401820705c00041d252510006254503040c3c00c2d00510684541d03480b00d02c034900141c544001074100c07800c0c6a05044003c1c0c9011003401d0700140289181d81102141c3c498414180e0070407412088154110100007400f1050001c42d0340d0700000c031801a50009820342141c0d40c820200c0350b4202e68481d01100d000519400704108001425081d8000c0103814500716600c2e0009042d5070360301d02d006240c1070000c5509142680c09610000030100c2c00c0c04c04107503111031500050f0b05100003184d00c512030208100f5412208a001d8255400940c6003c03041109464000010396264803d220b442a04c900b400310400e04c5610075000c0e241250202d403540078140e190812918a075440042a06800c81c15189400c005a601007006501800b4040f0001400000e02e00500280313015081f292805481040b208200035164080c040c1301a50700301d0039003421884066031403401e402002440030380c54455081d040500011130342c40380f022107000322078180710340b035007080 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 509082805 1250 509081555 509081561
    0x5090702210c070e0405010506040e1908090402040f051f02030405060a0516081b12030f0603150108100c030506150f07060603080c1504121206080d020109060b04 71
    0x21500010303007040007562030507030301d49261074075a40a58035400c0c24030000c0c9000030f14240560b403000c0740c14060002408103001080c460710350011410303602800060030740f6070210758a400051441c0110002841c40405224802e000d594140fa001401175660726074412400c24022828010a4400e01654180001010751058001650710f004d40185045c54a881d003044102c0c0c10a04c40f06040c84810091114150346001c046404284900d00160719071401021440840210714982c08070b03035102501c1c3d501040d665109489d0300406004840d040740c0c3d50f401c08a4140550040001c541e110060700108100b00c02040c00c120361101c0c03c2041058000940040301510b005603a290b8010290040c00c4542201c064018420031181400241c0f03084001c1e50f42408a4089500c01c1ea0501e80c046000c441c10f0b0020b100100b521018034005142608040d00c81c1020016080c04000902c620742d00c050713009000d10b0300800c000302008800e41342c070b110301544e010303001e0121400e00310b8461746003003c404683e05e0700b84 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 509084055 1250 509082805 509082811
    0x10605030a0b0609180319030c0509090c0702040905060f1608160c05070b040b0301050f030601031e06060f080618061e09010b0a0f0f0b0a0c06380a0509 67
    0x1140e155465030414050103000c00b0f000c1790504101c050345a0310708a010001068410b4000aa41c0c07006040360b40000c04031810750880104001c4200080180d55071014416034010401c6a00181e4074411840000c00030b0260b01e40081081c02040100b0509d2400c0b4005240300380e5140030f01904502011a046802680480310b0080301c0e50301c0c64420710140d00c241c0b0341401c40342c45041140c54881c0c4401c0e500e00d10f500903074085100750500200511050400d8488260700d0750060b40288401c0d4110381c0d40604aaa890011440c610401140d01d414071000c1e0300700c003005000110707450941c26140c410300d5440f02000c4800103450401c10b5448650b5480001d4400d101c1d20041c040c002404100c007140713800900019210580664851010907501d40e1580003040051040e610260309040c0b40000182c0d8520260b07011040d628818020105d00b81c1d0485a40d5140d181d0040000914031100702075200c030a10100641d00c074035800e6110f09120303000c08500f007504800045a2065210b5541ca00b08a6110b03412 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 509085305 1250 509084055 509084063
    0x31c0315030b27070933151206140f0907080703020703031d1e1c1b3503011802090d08121b191103040512010c02010605030a 55
    0xb04000b540e5040c4800c1444101c8018250807200501e0b040640f80c644003540e04a41c00903076854003003141c001a14013420314615884c1d0000341d00060b03080c0e01401c6d403200d10b22502d40e4103580b02e0322a4520354410a490a40c81d4444201045200d40303480c1c420054109904115000f100d01410f0241e079403801074002031255030300b69608442640c1d0100114040e41000f01d04509050310350f0010306908010b41026120041c0c0180104020ba07854080c0b181000006000c1d80380c680c200404084062003400700c1c1d001001c900c1d0404d0f48622000b901c0400020034114006441d441c04001d0411002c0d40741d0414000c001145600c1c0d070803407180700c0d0010020744400e00c14507400d03c048200c64101030600d60054082c0b807500400c00b103401c3c0d6141d1542003890384500d401c0f002044203c1c1c200000a0b503440b00058200c1d1107052a40e0a02520481c0c4505040e83c0040080c2407015041c0c00c11120141007048070007414003d00040d440d050000c1d803150203041c140500364007550034090045100d040c00642440f5490704 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 509086555 1250 509085305 509085323
    0xe03010b0d030509010e040e030901020610152613140304180b040209101812030e130f06080a020f03010b01050f070501091e0512040f23031c031503 65
    0x200e50b9096a080c1d000c101e450741404a036140b210180e42e43d520580205c44801d202660341c40c40c038100020b0901000815580e0b0a02003d13100380102d1002c0200c82030500d8441c24036200300d00c405141c0c882c1c0b089081828050845800081116030b041d00341320940c80e0351040308044090150b04100d1030b1a4012402461108080040c100c80400001d8000312548500039100515210300000801c88a152044000010544450340058100100c00340380d0000c3c88086200140e03031300c8540c3c008001007105070b0b00070702c00c007843d04601d5610341c883da01050701040c0204040240a551305d510545500d80628162300c1602e40c3c8000d00e0890406005210110505a41e281d01d841c2c0e51216030b039425003080005aa80790342c1d80da002400904c540300340300a01825107074041c1030368499141c403524108003400c0d01442f8a50901c0304010700c2280f081a41c0640d6000b5882c0440d01141c40032211112001009542e450b101d40a090b2141040b981d802d103030034410995003803052128103800d1021400d11840010710b0081 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 509087805 1250 509086555 509086579
    0x60b0a08040c0905040308070813020d0f020102151911040e16030603050a0605010509091b0409020d050d05030415020301030f06021c0f0605030f061005010e06280e03010b 75
    0x4840c005007a8000e10602140356040d0b169145441210380444040b00411581400e0104040c2c0001d081d83d8814502d201c5040d440205901003200c1026401300241078084003003603041103a00900c290004181c4444407003560f85400507440c20003000f03240140703000600e048040c00c2c0e0700314600c0444080d1940000043d103e40c44404424000d54203100b0400c040658500020001440901000b20182e001d85001704507541004200402600e000d00b4000485d40021440390110910614502000d40c00300d034000707822106800444c0f0345c4000b22034010a280074202d0584006900200614090b0740103200d503882000006004c4800c9210a000103407682c0d00108042c0d0000703210703400600304c0f4400d004841c846000c40301040400d644a60050780b00c540d85410b8240311340d0804102c400c0785002844024456414825143d8402030110b018450402480210000c0e81d40c0f80e540440d20f4440c140384420440021880d003403210781c8051a108070004a2071250380f1100c3c40c0500605c01890001418040320b65 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 509089055 1250 509087805 509087807
    0xb0a080613080d05070203030109140402012a060509010f180c0b0d02090d0c050333070521150a06020607030b0a08160905010e160f12020328060b0a 65
    0x1014060102d642090400a0400071a4140500ca02508150700150b49950400010400b0784401c1030b00e400c04845140c04210150f0790111070270381102200080c010009580142000b4644102000500614100320606c0050b8105500154034018600010042030412890700300d01d50b00440700c05810030860038824400c8981400c018051038242c500018904204180426154107011100355108170555004101c9400c007803003030303016043d009100e01e813800302e11040080c08541c0c0c940c042151411030500040801d030180084542c801d44002031200011101150310101e5a0100c3d00790b28103101c0e02507050910300344600c8160a84010f60040c0c00940d4407440201d0041081026140c0d00078018000080c540318140201c0c459604030080020301942004a6001070754010383c01089004d1144d4108052805844041c8030542900e103448100007541003012030b91142510032040c0410310000034044022035032201081a8001c0020380306280031445250340850300113100d2503c2066041001050341 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 509090305 1250 509089055 509089081
    0xe0f06040b071701080307051209011d060d090f060605180c0a091502031b070303020307020607150203181015060e010215090705011206080a33020d0b0a0806 69
    0x41056480e018000a103103284280400f8002e900010141c3c000103070460a10178244511051440c2400005160500030400242460943c482c0d0f0407044400304074070852652003500320ba40d081d0300d0720780610221351642421141050707180c4080f20750526000c0e0001c0c1ca0300f403030000241d4540440098403005c2e62115094080f40c3d115100d03c404004800101207141c08400720103607000c0c0d4081e4020340e12828034403030342d220590524070b400300c00740d02c42501000083d900008035404c850741602c03030780e1f11805d4520707095030a40040c0905660070390020080184282105000056884200742110f000d0b1301d800f4003d4003110845600c0b04010001401c0c1800024001c1841107814001072040b02e2056098031200700154200390350754074a80e0020b41c420030003980c0c0642c0c401040304141c1c804000c043d1424525540e900003119000b0900d10f01310603245024030820000350691007050005100b00424501268029407004210911813440c120901c091810200d1702c00c0b043d107002c100140300070b843e80c1e1458048 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 509091555 1250 509090305 509090311
    0x1704020907030b13060803181806150c0307032a0b0406020c07030227090312160c12020105010f0b090915150412030f2a03030612050703060e0f06040b 66
    0x26456141c0180307a0f14032441290010000301e00650f4231124a00c50440010349818441c5108051004040c14090014000c0340d801030022601340c003d0301c540b0396a01545010780140b8041d140404a21842896042135516000d80c5018450380c05070300414100e0300014646c40230292004100e840010f00240c0558020241001e420302107a058594130b60000d80c85010020303400c4101004030030b960064944881c3d9058100145401440c1860350108441d100e50000801401d00c0010454141611900641241e0f02a80c0c0212041402d4803105101034081c2c0428400c5920302c500301040040e0b21609a410381c2c0000c20700800c038003855111717190400e001510301c1400c0780d407000e04e854115a01c0f85140005000612001400350004462410041e000c03007400d2200030700b4080317403180391204040c144540c1030710700360428945a1403d45034101103004045642007281d81d589102c50341020310500144010071284100300500c003420be40f00e040d61b215102110a091a6840100440d00042d2402e01542e4 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 509092805 1250 509091555 509091559
    0x80718080c040f2408060703020316180b0307020123130809031603050a031d01080a0510050402031f0f0807051302070807080304050c01030522050a1b05011704020907030b 75
    0x4180058030038144d071a40005226600c1c96070488400c01c503042046c062142e001c0c02d1410114114070b01090f8459802d0036011200003001441000341c21a00c220083c0030000c0c0c03e0032800d4507100d1418440107030080c070329150400c044000b07411403003101040300e03851030380f10780d5501c07021126110755a83c50240303a8101070005036050103500342c0940a0050340c11030000840c0200300030b0000490b1410060050000414210403a4050400c2032070b050340c200c40d100c1d8002d90080e100080640d10320202c0040c10407103400c80e9600c140000103128001303480e5140811202041c11302d41d104255910802484c58241d03114524082d000280200300d54039102540c090301340101700700513160941d650365007141c84c2e000140c01c84c2c0d001800310500087c02010469085203880a01701044241071481e4803400c4100d5131141a010844040a0036007040020f0007655002c0d0350088a0544210210b2a0040c0100c041e014560000d43e03c0c0d00000c800e03007004100640a01c0e0050851030650b00d88030320860151035510030307042e = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 509094055 1250 509092805 509092811
    0x4110405060d3c030c03081e24120618060402090c09060403050106080a0b0c13050f060c01090b010e0705040f1211060d0b04051311040203061807080718080c040f 71
    0x55900f11110f450101c1140c483e07034070350000038800d250203014450b016158103611075890350380300d03003a6600e07130001074002c9544842842000c00070360007010703c060100e2040d500080180c5030001c6203400012014040d00d4840180a00c1c800083c0c011075880800b110043e61025444000c180003404000c001e0000c120060252481d258680c0c44050a4582300e6000569941c004a095005d008910003070907040400303c08010324069040c0c4030100c1ca40740c1b038050148294114101c41483c1d0341c40b00304071491148441e000380004076041c24000441142481010003d031001800100c1e4244200c04460540d8083d42003030644500302204950a0141542d0071074041e01c031400c0a60881da5a07002400940c51b40007008525044031205100a032200a0112802017040f52805400610018440401f8800a580043c0c82c1d9035000c0005414540044010751000640003d001d80326074041465440b411180c0c031007501c0102d0300000b0a100c012644a0411107400000790840140b91503084602c594601c43c2d008 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 509095305 1250 509094055 509094143
    0xd05060f060d0c03080d06153609060305010506030a05030304032f0303060a080c0604060507081303150e06071e0309051f0608010c020607080a0204030b04110405060d 73
    0x2c002c001c0c0c1c213504152403140e008103c41c481e800d124001c002c0a041c1405290f0781c00761a00001400f180c046c031625940c1c0d0140d0410f000c44641001036010001060512401c140720b5546240c40c0c004e1483c4d000540d099400c000001d805802c2c0004d061100e1a4864000d40c955a40e5823801c540c1c02140ca00310680e0706080e81c0807078841d8070742c1d805030052142401024568a003849070030003101c82078507801001d5070307000510300c0c141e2681e580045e14100c131081e060441e610941403900309050321030860b102550000d0a0004414094a0340c001403075148150010400c0c9000400c8a540d500300c11106c08001900410f40c21401d00d04001180108549905010403c020103948a5040c4902c0803522110038010500c00702d086103240c000d050040044078000c100c40d11191a0094440100500300010311080d0008100c01c154254129001560440c250b40c0090030182303003812000c000800018451820500818000d21704035804a281685c4501034107190542035000c10760800950034200c4c442c407124411 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 509096555 1250 509095305 509095313
    0x10f0b0403120203070605180613080a0e010516060e28140109020a060206100e040506150111030f210609060f0103060e04140d050c06010909081908150d05060f060d 72
    0x1d81b5018400c40c00c90303070b842d46401402927842c001005203032146100315401140c011030303000c0048400858603803811300440d0118800580344c40c03040e0405007640c451260f824a0520038141d0200c100a6050300589442c6508110105035000e902078a0307940007601d0340714482c0010800c00303a4852018644d4008120088541c0015102c20100e40c4003d000d81c2000b010850b070f8030403618040001d881081c0f1100d40a007803584403299281001885d07107602102900105190382e010300c3e180700386428000c0c2225034403008502c80040301c0d00f1511186803411071513080362040700c900c2203115215120207410103184da910941000b00c0b022040314510306056641c2d00120303280b0103c040c0c1d03501c07944c0291980c41400803041c8103685001c40d039100350010803c0c06d01614080070342c0800d03041d044940c00180455503100e1030412000a00c05c00c0125089031710f926480304041d40d000051036105480d800d019403a40012201885a01201004000e026070004030024a01401c00c010305600502c01514120205015035070b = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 509097805 1250 509096555 509096561
    0x20a1205041208060301020703351009061205100b010519080f1e0103080c1f0b03010c090803091c061103040510060311040e10180308010f0b04031202030706 69
    0x1e00750345a421200550b03103800d40209803a5000030f400d500851400c0e44644008190b1101c40c0003a88964001c6090031452100c007207c144100c2c400c2d0700714920340e804c00e40000c0b68405e2040c8113203072007203082c00c40c00100c0c80120403a80f10000c0d01b00c40074002c0b2040b200340b1100100403400409060180a21009440d501c007035840c41881c1c299604c80294605022140401601c070041c00303514148020b00c2c1c2505860484048181101d510071502070300c0310509511103080294100a0200f0f00c003603204070002042e8250403036541c070070058000b045011701092040ba91040980120101a40b0420030f1940303d080001c02c030b241d4000100604885104150389030000d44d2021414200505000700034802132002c280054041c10280500810400740340d0350315418040325044183e48210768a000100000d01300341700c21500782d200d00340304108a00c1e14004420035558884820342c00502090004140c0d101840c824070103640b0443c103414101861582e484a00750342c124035640441c00284082c0c0c002680b540 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 509099055 1250 509097805 509097811
    0x12403110a170a1b080910150618230a090c03020a08011e14010e030d080a060611030904020c030d061805090c1e1206090a03020c090712020a1205 64
    0x165031075900c140c00e010480005a4058201410b1030718003255882c0f9000540c0c03003442d0303d09142c107140c1107696a01510390b00b8241810745030300b0414107040340d043d4013600c0040d52341d06440c02c60325805138000c0504480b0340100301600880001c0501c25031040e600003420710401002160040c021050310340c540d030880082d100050b441e40080717074010a40d00d90883c2c00689071400360001800001c10078140200541c5083c00038400c032040d50b0f400c0031074040350340d01c20424404d4020300a0103c40c0c040080da1402810004101d400d5802c1c02d241010108002d88a0350f0305051041c80c103001142803003078090820000354000402903460f031008006211100c8104d020340300c0100341401003403489100c18030080e01903d10003001c100d0f8503001003d405046560b5038180c440c00801d561050f0706034500c1400412122849000c500c100d52140b0010411b040000049a1092612079401e0f00c0d4070420308810700c500c114003501c80c240412480900305448650750b5001c5c0100d0500c601d0005480d02c1c00300d005d101120800c0e = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 509100305 1250 509099055 509099057
    0x2101104090906140c0703080606091503040c0e06030a0c05060307030603051e0d14030a09060e0f010b031c080c0307031b050c07080705281e0609080303012403110a 72
    0x1402043d041c9442000b0800e50004894012911b0300701e0b95078000380a514024090340c07044402140c2c110960b218401001405040c00c005541c1d40e01702401c0c0700b0300d1070581d8401c1004940000c4001442402c020035030180142d070142142800700e09040070812141c100428036420965034490020229070708001075041010107a02e1224a40e460403006410410203042c21814404880610620f100014003200d91000c500307a400145180680b0740800501703d0581900c4180c03051119840200301c06501c1481c50850450840d400f00e40740903c0da444000824031400040351400c3c0006100d0300446c001190f2185103407400103032013101c801da071008a6090b4060040060404a00c140d1219410070051010700041e800400100c1e00e0174000400041c4c1001c2100f200307001d8034001c9040c0303420000305030010b041c01d40e0b881907001c5062543e01c50001240e200d10000a81c03d90030000302d001001c400c0b6411b80e900201d0180074030b404d2119510070b4074101e0400d0420190307030b518481e0143c00d03c800036000702005 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 509101555 1250 509100305 509100311
    0x20d0b09010f0e0108240601020a05011a040609090f02060c030c0a030e090f190b01110607080405060114010503040b04020f1801060e0306010b070222050f01090f0c02101104090906 79
    0x140810001450416080004954030990042c0c01090301d00403068840c0f044907920854a80d0303040c0040f0f090040ca10401000e9600704150081680d41d2108490de00c04000e440030030401d03507140c0c010010340300385550103420424100340c50740c05405c0240041c1805180745088034680b41c040307085245059206082030700082c081c4510380b0202c2c6000303003446400c484511041c01483c03c1c14060700b40981100d1065011107a940c00c3ca81c0c07190b03402000345c0c8010f882c0b07050a4401903c0c01e004040c00110044a086649004290001c207035240b910311000443d8034182d607014211740d9180d650441d0140041d001760b070f112610141b40c4146a503803501c0110b2003240f9841400840d4900500902071411407400a44243c000c80c006000a5020b0303401c0d03d418580440d41c3c042400340d44541203104036001c804071000f0768100b2003005080b41041c0e000c1412540c20010810804074100610012074805021305001038001c1907c0c46c1b803c100640040591175103081c0b0303007807815946a00040894030008030032560141c0b = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 509102805 1250 509101555 509101559
    0x30303021c06050612100f0609170105070e061b06010f030303110a051806120a09031b0f170f0d090c061403190b031e070e01050a06080702070506041d0a020c070603020d0b09010f 78
    0x1012b400c8024080c4401d40013400182000b40c005050110050000760040e00301281089086050030741900c02e00d209001602e8142d40c48000c3e44140052601040c0c0c086810004a1650f040d003001c111030074041d140c2c2c0c0c0c60b070410185030302c20320000c4000328641d54040804e2021030003800c0d05400746809230b42044000140030307050385005061a4000100304007103015014407403010501440c0014201d40e8020f20203420050389110b01d41460064404600d043c040c082501003000110307038861005680140c00803001940e89510031100601162404034001c1002d00c04555403404000899100d4140c180c408500111800040780c5415103240c140301e061105143c0e000c640403003d0110401500703c150380c0341d00a60520001c900038038400d10a94007042003140002c1c950510a20004020b008000c00c0255501e03070380c040fa0b001145014402003008451400441c2c0100d20505c215105800088080d080c0107245c524154000c0d01701d01d00c6945880d480f04c010700d006545011400e40079207000a26913480314 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 509104055 1250 509102805 509102819
    0xe090c030414030f1e12090a03021606090504200a0e0a05040615050c01180c03110d051f0b0a0306020c0d020c0102060420040501030303021c06050612100f0609 70
    0x2400e100c2900d00d0b1070b0401c200d80d0743c408128a0441d40e00c81758125045c1001d4114013041e94141c402c41c0f4036400d821810805008405101095241d130380d074025401c0b6040c1610f0f40c0e81924031299144241400300b460301504101c0d909160f00040c250190700303041c44800400340040c2d5100c0303074051841500007405144420b1701a1a200c823000000c1d2070f0603a420006c003401d00104580041044841c0418440086402410303190250400419410603000d040c0e40328140d0f11b4074010074025408105c54024990030407000750b00b8035a04003541c45410600070040b1071440c00300306810740306007209151100c0e1911100c0c0786c03a440d404016070046110f240010b339201850b40d0580d080c0091650704074115004404840031a83e0300048068100d0b400082c11401d00344070f000e03e500d0b4045069072564019062030000004d0680560180c07130704544d0040c128103d40d0b0300303d00500845e2145d000b443c1d48100c0c00d124800c8098490340246500560080700700046644a855944c1032044c0c55004100040c0c0082060000c0 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 509105305 1250 509104055 509104073
    0xb0106121d1509030c030a030902180910020a03110301180e070b0f03060406050d0c03020a05100c200307030605150d02100819090302150601050c0316030e090c0304 72
    0x520a14006105600c1c0c868040035211000180b80d840580c01c40c1011862281007402240c1a20411204482c0d407400c4910028004e05100c030000c1e44622203007034080d902921030341c01940c0b1468640c0040c0010380b03400043d0350000d4204040344002c1658558015001085032001980601807d121842c48041805141e109031400e044000d0301a070072034241005a04250030907200c41b01c50309074420362a03540345000700d4000e04059000a0344100b0010601c018409020307000400c1e80d000740d450b000b039103445900744103400800c0c1c07080800090000b510721001c11001070740213000e80b81210b0b081315201c02d00030002e0300d480300c0c68105a514981c0c40d8107209035841d2822142601d840b007a038450f00d03096165000151108500030110003031051140019110403a034244070400b00040d040108981902418000d41d40ca00d1521103030b01550700c000100b50a5030081003039802c03003071184005610700304401d031100881c4601840e04400317001380140643d605981c0c41c0c40e00c9108509803001d803a12071800342000044 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 509106555 1250 509105305 509105321
    0x905060412140f0a032705100b0117040c050d0804080d0905060d0903030603060e100b0315041b0302030102030a3206011b02060325020105130314070b010612 69
    0x6100c96035010309103645181d41901e00f610b0389071103d541c640402d15002c4e00602840803011130341259107800e607445c0707241c44552556814002c03400c491440d029201c0341e40407942083c9a06000c1164130000303440b00700f84040425440380c8507038100510030350b81e2000308501c181c0e02d46044880b610041014800b40804001d004620401132500c802d00d0340c54100810824462421804c80342611707441c0c41010305001c0d420090040d0b500c42d00800c030f403c0100b07a1454a40c2082e41000d020b8a04151403615140740c0011001c103c82700c50341050049817940d95a1101d00c0c418a660600043c05003a400000b40e5028405548100300100c0b020440111803420b080140000e000003200540002c031080114405402c4050b41c00482806c100c8009a09104c0c4401001d0b1190f00081d885000001046440000307036064009505040c030106010302c85050059090382d1007243c7d52501000c0e00866200440e02c61602210741d81000d0600314908140d07074440c1504030200741c200101040304581c200354288039034418042 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 509107805 1250 509106555 509106557
    0x2071202010c050f0703020f060c0408010b09060f0427080a0801060215040b1801060b09030d0903110409060b09040b01210302061b0c06010f0e0115051902100905060412 74
    0x103180550107003e0440d0180c40002441d550000c586031040500812a00f40d5028001e01251f25500c0c0018107075042c0e50190044d400c0d19401e06d00c00400c1810455103460251000030041ca0104008a091000818094048003220380710b20100c00000ca52126040038001c2c09111130b160341c1d1040200142c541041a40150219801495800c0c0701014000c41184c00c40d0740082d00c030b00f076500c403034145e0074114a280401400319480c10100142e891000380044c10303200002c0d4190b40d02d2514462056035444054440600119103c10311544145040c0d80040361207841000c0c00100c800301c650200701060307011541201c0400800f00103014545054064000c0912030700791803080441c556400035110a8058841c0005000c1c032002c510400300090b00703a0b90182303500e5084603410f694904085107003030150720804444c2da040200205000401c003042081189003604c68915144040a4810b9004020280e4108600880f800b0508820035401009159801000203003100d040c28105200c0ba24006a1414 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 509109055 1250 509107805 509107811
    0xb0411150906190e13060e01050f1503090106210203120f16080c030a081902070f260409090506180c01050d1104060f23030105040207080c07090207120201 68
    0x200c895039440221116103070860003604807080c50103c107550902454448580c4207045480718a8000d03440d520010171525189141880750f40e8030018024200c0e13441c0d03002c581020424020940315400c080003590480081c41c000a5004c0c3d170794085009210400084c9520b900d000c00b10305080d850100101c2c0e00c20142c10031428948200c81145080d9407044840c5c143d014400c10740309905005c0e48900707552a008113941a01e07910144484020003504017103078022141c01040110540e120303058030950b821640d020340403034582040f0f500c8038140c025000c00c18502c00d85000c00c0d01c0d07820400c0c0324058001840c086001081581c3c6500d041400d20400030582180904500c080001013800003400201170002804d04560300e07100071030800301501c1c002420b5010b4480000d40083d9041d40320107125038900080d075030a04441c03540c900d003107441c80c0c1c0c6030031007861440244010700c02480c05a006048651240c802c0618000014010906140051f0b10400302c1c25408600401400800103403511026a540700070 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 509110305 1250 509109055 509109067
    0xa051803340608060d0c0e090a020a060e012a0507030303020306030c04020915030c070c0f06090905150f121c0305010803040b1c020706150f0605040b091003090b041115 74
    0x100340000c010400340c0308441803103011046c0a0320082d104041c01c098a141c0703120b443c0c6001900e07520f64651400301e000d021803140024416105404241008505030349a02d01c402409400079003000d8501003510007540601d0200303001442c100a104001c6100703840158a0b45800340406042020b401301032409640100004e40e1503076150b244100c400066601881d07206e854203d007001e140d001d00038009090a0309020041021030004542c10100c075440c0d920071030820780b40c00515081e90802da403a0780d61548003107085941d500c0c20154003c000c01c40540f402034205c4108a0080c9894180c09640c40c1c0340b140403013100030940c0e25028281c00752032100c0003503142c1072824506004611a0031108515251505020054107071b050301121640c940020040c4010743c500940344560942070300c26105102d00e603440000301d032805601680c0454a8500d80740b0b040404640078802890040002d8008141e0744030040000100d42071050b900032401255110004400c0d8000d0040d00160b031401c0d200460000c0c001 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 509111555 1250 509110305 509110307
    0x1090b10140909030f0f0d18050604060902270105040b0303040513020f04090507030203090c030d0c030e06040b040b0c0c040504020a17011401080318150a0518033406 73
    0x10800403000303403900300c0ba960b00e0400e210300b14040c8040204882100045021031148010054210441082e90030003078280503e501d0394001000341c41c0107000c0e0700b00d42e0005010a0655210603801070010780004044a092172402c1c000010204d11440d6404c41980107000030708241c8500c0d0403500c0150b0041d0b01d441d05000014003240084501d24182e150005800c05001c0c0422007a900241039251082c0400c2c103110001401130340046030030144a00c21a2543d000900d00003840b82509038440c0c81e10030b0342d901b141c4c500700d814000c01c0c020706070044000c0200062001103240140014000a10455121000e1900c443d04215440e4811842907003080103010240e076507084400103c481c080e110866019017940701501500849102c3c844000c01d090001400300c101100910200010034018185000403908119803103072460880d0804600030700100001070302a030010301800a0081d0203030f07565050000007e2030a0b040c2c003284107010740400707202c0c0d2001411801501108220301c041b0300000f410590 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 509112805 1250 509111555 509111579
    0x1060608090f1e0705060d05040213062405120a060e0106140a05031e01090501060e0d0807020d030203120c040e15010c11040e01020d09110616230d0201090b10 70
    0x40000b0500f507078038903519402030302040303134400810014040305d440d01d8920904900a14040b1000d9000f002d101c42d85504080d0385101c0c4100742c03110035800342c100300c0300a412000101c1500c294030b01071100810625141c618000c840798494207080c803021038010304010501d550110181e0210007807109000c0445040c1c50b0000545151895510b00580c480d41c855102c580d5041c0b5045032501640314420001c1402290303500704c14107943d1152240c00c2c000343c0700002c1c095090001c0c103002c1e00300002400200700501c0c00d02e800e20003c50080c03046a00741044548411101c03202030741e8001c81400000303420016401c0054080340d011403641103440b03001d240d440c0003901d03a425200c401024400c07200c0025049030350710792040700c5188089000b1511340a0b0884248020008100c0c180d03417004800d011a049490410221a01400000b0034609a0b81c85643d0f542d5408440840200b41100c0c200c0c44103d09100030400740c3c41400c101d50002c51301184504044102c400c010302000c1c0a0800f81005110340110b0304 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 509114055 1250 509112805 509112823
    0x6060e060f1206011505070b070215070f05070231050411040513020d14030c07050301060806040203071802070b090a020a080d020c1e12070f0506040e0406020c010e06070201060608090f 81
    0x1480f5442c003904005d038204c4051042001c02800d4240b0074051041c40ea41c0001c42644800d000801700c0d00c47d842c0d003d0b043c1c1392080345407603804c00514200140340041c1882e131022099004c544200e0b16807100b1542d03400750312401070120f01c01c6035541d4030100400c0c0801e00c3d8900c0081c030015a400c0086041c04080c02c6814a03841d88007034082c00d031083c039001c1008988441400005e0400050369246e038884070040d0703240c44280c81002d00c40c0d0309140010440d128007081240c05691b000703004000342c506c0c11311040c4282e1000380603120219424040c02011400c15013180384140d031000e005c2c0c1513541882c030400040c071074142c1083c0c0c5554070034018a600d070341d0005529511780d6000c450b10200c00030490348180c02401c9140465801c50003601c0248100c2d0300015109d01629000744080b401c46468205201c0980a00c1c071949018200c1c5001280104007070b58001c3c40080a100c001241c04405010410f01d804015148180141e546031401c124071a031000c45e641d04240b8040282404080303085e9510365560b404 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 509115305 1250 509114055 509114069
    0x120c0f060902120106080c0324010509130f0602070318060f1d04060e0f0c0903060c2805040810110d0203130c0815090105040c031e06060e060f120601 66
    0x410040741075503203112015400803240e000911000303448030b03601ca486510413a031050081c403c511454903c040782e00e82461148820340310a81c51a07107014100000c80c40c000c2e18011501c40c07500b030486e02003031084401d00c0802e4003c8001603682c80c0f01c3d290040ca29006030382044c40f001c4004d0000d100c0a41d00c015211098113507840d120b0354580b5860680c031001b25108400f140d1007403a2030070000d0500c0020a0551160004e120401e495a50b404c40c0003420f4442e000c06170354180c0002d00051103040310741d8040c003038117814040c101c000e4103020610400c580702004503000120704041000c0000c03000800c84507190b608401001c0c003038401c0c00a00320300c190141040d250405600440007410b8081c0c1081015503654011400d0503107659101c0d291601e500c1d1607000032940809190001d1a0400140240390240740d0008161003800c0c556298001992509a800c6800f40d006082c07200100b4200e0250034003030400c00b4013032001030801c401048140c50724140e540d030240411034042064001c01241c602d04403451 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 509116555 1250 509115305 509115311
    0x80a09030f12060806010905090c030d1719020307030509120f091203090d03121d19080f0c0714040b01050d0209010c150c0206100803041a0c030a020a120c0f06 70
    0x380100c2d580140030640c002619501c106000007031b8400755901b085004130110415a0000c084110506441d0401105c1c080c0100340311415003450b10445050f215400010404804440c0d07041d00c1102c0240c1c0d1046d214600040d407100f003440003d050910070a61850794060400d85424241d844180c4039004641200c0d00c19815102c0043c040d0740b050040b100b00003001015944860740c13a01e405040390241c2e4440410281c50051302c0032040407200e0045155038121307801400301244082a4034281480c04604950250050116140300d040c0300f00600610001c80d4060400315080001c8120000641e42c03900d88079900b0301102d5012a6002422034002c1c5060000240e541e002c01d400603a10405484402810381e030300e0450b81c60841d40941d00401101e892a0300f81c2d030440e11061580d0685044500901015400400041101c211204011088000f18560705410072010490150039600460411005a049964803100b04501c0d0903030103451000b2400c0140c1445050b0301c94a0803064602c00081809076 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 509117805 1250 509116555 509116577
    0x11d010503040501140103030503040b151c050c031b01030f11071211030412150605060f0d090804060807180f060c05010207021203040501030b011b030c08040f0308030601080a09030f 80
    0x8800c1d01704c4d030310030310100190410701e5030340e0b1400401c0c0f070344200c0781070750f000c2d0109000c10003000121102c8010030100074294456644000711803001800d6600c02180c541c403a00e80710100310f03242406034142c01c0c3c00354503040400c0c00d155000907007994000841032220707500d040614640000030505031203c1d107030003a181c201c10050445042d104000c104072000b8042c40045030002d0070000038189094814420071604019840202c052425101140101a40603206200703518843c8888805403849a248801c08200800c1a8446002c56070003070f004000090031f28070030032040541180c005207468440c24504015980780c0030001d00c001405001314010420424004005e021b0709405654a080e00180084100c0b0a0240c0700c550720350140c420b0901003414004240c00660142c0c4010840c2d00054600e61058141a5002c481454800c40c080315105d405200200708a600000701401451040ca10f856503410103000240c03a52400520000d1020704181e0030100099006001707058090f460f00300346001d10 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 509119055 1250 509117805 509117813
    0x4090507031101020f0318010905030303090d0518040513020117070816030209031605090105010c0b01030809061b0a05011505032a0d0602040905100e152e0806011d01050304 76
    0x42c85c042c1007400c503880003180c440300040d010301118861050981742c07808450380c1d03481416100e00084591128581205c900c1c4041e0300d0242d801040c00c00da41800d10100b0411250020701250005d94903641ca040c000c6042604550700008840607056500750054001c0c60300c0f500c01040c007a001040d98400c1d69010b20580d8581c0d010350192440c00c20300600380c90080c000d161075442a40014403c151040d5155000001c1a50203011440c1c0300c560020b04450041e803c50311515416806143e845412003030411180440d928450210840c4000400c00303045a407540c1d007881404e403071541c100c038004806401020043c60350000380b40c0702c0546902e5808480041507104001250210444082d0400140e03a282020012144e0003041071342c003522410055500c0b03041211a105130b440c001c203480d100c03020300802c040301000341e140c050b071080080186400031a1540c4075a500e2505540891783c90944510310803115401c0200c0700da0248003807801c02d030a203000380b400c0c2c205040034203c524188140000490140 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 509120305 1250 509119055 509119063
    0x1050607060f09060929010b09040902060f0a2003031e0702010b0306090703151107140c06391e07170706020f0a03020c0906120d050405010e0409050703110102 70
    0x1141c000c4130400c2004010f080c184684a41c55454950310754040000080c540310140c0b00c00e0586032146111820301c0050b109000c0140304100d170503680f080061040100c3c05143d0f40080000c0b68065a94020302e90600d0f12080034a40032013900980c0d60414410007072104816400c001c4d000e001c2c0d03095440345440712401a030042c40c5080c600ba80601801d800c021040c0e800261384004c90b442414140064804e0300320480465108503481c0301690020024980400c5030f4103040420b815190042c4c4030500450b40010b0705a920454900101c8240b00349d0b60101010000d4580550f002d4011903114000c401d5100d450302e0f2508850082d003500c00005034840440010007030040a044810140101c95410340109661500184102d00c018415048919649680460324085499040d001031200d2920700b001c0050b1510020725140d00020410845200c59108000d0301060030526103c103581c807401c0400041c41d070309044501c0d501850615082030000350001800c442269080600012450031100040b030034 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 509121555 1250 509120305 509120321
    0x20c04020322060b01020705041b0c05030d05010609050901050108070816050c25060519050922050709090e060406020706111210120803060910080115050405090601050607060f 77
    0x88039841002500030854141d00060100130242c08a0314140d54400130042a0341625680c000300151040e100e01034240200c01c202c0c10306109000740d82c2809400202d55049520981c4080c0008044c4001044541042603219002d1724081c070f0b11a00b6031030b08040242c030f4031102415007040805503070310741c00c0000d00c100c060350030040001d0265000b003c40040c64000506803c805801c08510041c0001402402441120b4000c000000c0d80400c1d8a20700718144c0701d540000410300d810a107642209812545065190420400c61003c00200b1f410b10b040c0013441c0c0006500010080c1d445c2510201d8906000940c607030740036a000001603900c0a075403412001410008e0a64084c1200104290244611420850703209640f2031904400003070b40c0320442000c1d0313051800054200b080c100082442e5040a40726294808142c00c1d0182500b9600c6401500b180e4142c40c0031502c10540000c03c0c44140341c036008150f0000d0290004040769414880080c2552080710310060865943c0c107142e01807013010380c1100030 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 509122805 1250 509121555 509121601
    0x13050304080a0b01090605040c12090c17030307090506090315060d0614040302101401032604080d11010c0e1c021c052a060f040b040b0c0f010c020c040203 68
    0x302d54255107000003001c2c500307005449010303080510208080c105445017140100d0300d40e95908840c613004011034000c2007400d000307980c42d14410030045002c0501d0342d060046880c1000003142e0f0b130714182000070213240264000503c40d600030862650603550000e03c50042907207040303e062041c2c844000184a2500102c0d000705002c0c06c0044440d50301d54014aa00d200d03502036020703104071000710845082141c3c0401c03040510b1480c1d0000610224048050300410f28080f0400c2d803600400c9030507590072540155011031403170341c41032030028061540f1151421840816000074010089080c0c0042c2c59a03001380c07201d50080d42c920311400c0349400b5081e41d1050b85600905081110160612401d0007500901000c2d85d040c403850303c0302452411450103000c85100b4101c1c00e2180000040200161540920a41160300400b400041116415040104002c1c1424507280c3d58411502520b03600304210001c4065582c0d02d81480800415000f090030350108100b264016566a0350300c00c10200e1150190100c1 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 509124055 1250 509122805 509122813
    0x51b01060602030a08090d0518010329010311040e0408131805100b0304230a1b0807050901230120100506031f0b0a03020319061b02061305030408 64
    0x1918503000f00040514082d503985040080e034560f180b45546d18a520100d030000b403001c000d0030226050302074940e0100d80c2c0c14940403580300c4000c1e0b9040484000c0c2440402008050322003c0202d603018072400402140e800a0281490300c5c20750304d07a41e821f00080c4042c1800c140043d02e980303100711410300c1c5e2002d44066101c4403405110b4084080040504035490750004e0000c1d80c000c0352040e003240c00d503481243c0c84035141c1d000818038001d401d40c0400903240000c0908c540290701740084c1350b1008911781000d103615030010bea450320394200c1c0f0b0000342e640094040d0000c00018030800b44042880e1203e03c81b0170760007166544881e001228901031185100840d01d031030490005080b07102003015604081446801e21040e200d503420152641a01c4d10f1a29411659491009180b0f089400065200794000d180f00b00b490b50300d402290034040010038511159803130a11290403c4902c1c4942d0007440d459100000d03200503110360196907500e0203401c201d803a0700b00441c2e07142001020001c48000d0f2403481e041e1 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 509125305 1250 509124055 509124059
    0x30a1a090103121209050d032d020c15040b01060c020d060c050c0c010e010e041a04020307090e07031505090a1d010e070905090705270411010f0e010f051b0106 70
    0x43c3c070340601c464040001031035503801360483c250903000d1401d40a42000103031203200f50308a0150000d01c0b98607031802d0390015181b50112010b039601803a0200d0454101c000d41d68031448a141402c0c03811140100c41c050150030700340004550b1090800c2d05588240c10720005035005400020007041d0984001058030307007030a8181110550080c0070307154503000003044807104510350006580ca804040740850002d130901e1803809240c41d11707401620714081003016a410002249011405986c006c407801c0001c18000c8004004007400401c2250340903000d803a08205150302d811181038040c10358400c030362140024102080600003660300a01c0256a029000d180700030381c8140b114042d12111100381814003070000d0010760300c1005d01440748100c079444060200f450609080220300e05484048001c001003c01160003000d104041d01805907000c1d10814411400100004007281e10b0509403000308820104443c12598005100404125150500d280c40c0c4152100307501d0007001c064000c00c0c040d8240040 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 509126555 1250 509125305 509125313
    0x7080d18030c020907170a0f0b060a0c0210050403050a080304061514122409100e0109111905011407230f1501031b030b07200d05030a1a090103 63
    0x60b0782600d41c8240c0700c0c81d802da59107450690300c210401d00a00d01c2242c05900040500c0c1d403a0744012a10b0804c62000205502038002241c9560021810790010950055090041d0b2410243c10f00742400586000351805085a8900d13480e1150208001e090102c04004101001030325045607800500e0402020700081c0d43e182c0042010481c0b41c60790f401030a40c81005010700c140465004050070303802ca40c016003850b0541ba8501d010100030410b07051400f801015030f21018403030060411210f0110000301d00700d0795a05014101a001c076600d2407007a42491003000011807601c4040307080340c07402d0900b101845448079690045101d06000100900a407080f0b00524044c6080c03010000c500000858000c2c8410301c4100c0c0c0c0d0361400309240700368046100010000641070110403040c1005070740765030340308959a551f951079058041c1d4200d0049943d120b05109881c0303141c000c0351401c2e4400001415442c0f8a0140500240301c0585000015030310b07007a4400a40c1904000b040030880c01030403140756981c3d2414 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 509127805 1250 509126555 509126567
    0x306130905010510060e0a0e130203030c0c090105010e01020a03030507050c070320040606021f1b1d011b0b06041103180105070305010510110c0a06020c031006060507080d1803 77
    0x1460220034844101c1c003107681c0d0301c01c440440e100240a0441c4100c0790401d9110b850f001c0d4009c004a41c422414071301d403401a01c0610103841c24100c80780081086040000400991100c160402410014030252800042c0e9001420020303d5415040000d00c0307444110044445109002c20040b4521900500004000c0c00e40e441c030f811851a0b0098508481c0724030300308401e6900a05c104001640b00703c2d40100050200203030100c07040d86215001503074201c001607441400c0a541c91500103d203804001c2450038403051a54400d801003442c1900c40c03c0e00680c083c4803c0040720402404607000c400c0025101c0c1c590390b0014196003408d1408513128a802c401d41180341d20340504007030b1a5400c01c0081010140039001e0141619402440140c0b510700c0d501080760b200c85100c40c0312666100d0364811100c20341710400d80e06c02a2046901900c218500710701410700d442d02145004200700d1605a040103a140c0c44400d440090740e0007020242c1d03500a001c2e0610107007610002621403040b0680d1f00d9420590042 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 509129055 1250 509127805 509127811
    0x9040e0f03132904090c180f03050c1e091e24010906080a1808030406020a17040b01140609040e070503010614060403030e01050f0a1e031a060c011d0a0501060b040305070b03061309050105 82
    0x10102c80600b00b640c07041c031201c033a0550411582c0d1004840c40c0c00e0074503198480590210400c0000504a806a0342c4560005010743d4904422426004003000c0a690741d0388500344241c00f82400d11700345c1d142080040c0401d0b002844e10003034030f992390780c6281c01000c0c1601003088a9003203030a19440e41000d0034000020740c003c040c103c0c049102089504102190708010750b105580001a101940c2c0c61315640c01c904a03441668950300000412000c001c0e940c5034402c00d88040607510040c85402d0400088c1402c40301550444403c10040c58003444543e0b54050864050b80e506280c009500c2c0d01c0c40c0c1c016a01402007464002c7e207000003050706004580d00281c851b4041007800700307078110020036020a0301154080600b2414041c0e00090541690078400010020150000c000042c09507101024807102015455542440d0b0400040300050180074007407000900a0b5004603854585103680e03c0d84d07a060148500ca940b07500210000d9119a02c48100059000c8658003c1c82140c5251418034001d1a0031 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 509130305 1250 509129055 509129063
    0x601080c010f090605030106080711061509070302091507030201020403150905010c050403030e01030b0312071a010f0f0911190509030708011109040e0f03132904090c180f03 76
    0x560801102c407841001043d04640b6241c8031546181d00300f07241218200c40042c80031040c8000c400340700307014a4040044620460001403640d1030100c60030200301840601030b00000800d401440002d00e10780c4c0d2a4107000034008000b1940c2c0e516140d81c0ba040c0d02900441d8030203800305095154000480300c0c0b540040c4003d500c110002c00c2003089801040e2000d01483c00098002003078420407400c65406036100c1a01240300601711456540c2c110445009648601004c03242640072031084440c4001c8000c40a002d04080c0a11985441c00c0c8901036048020a1241b0300c602d6490388a40c944007584c03e0100c40c115000181d11664001d5400009003040c3d01c0750030510700a105481c00000e82d05810710032080e000c20352204140c90846801c0400000d80300c41c40700c038511801200383c4145aa903041004084240c0c5030580000914039000010041c60341da030302c0b55000c00e6201c0070112003404012080768255045600d002480c3c0d04002c100301d48980c0c0510030111030300758401d8003060540d1a05034107c00c49200d = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 509131555 1250 509130305 509130317
    0xd09050a050a0326130303140c070311120f070c051503061207080619020c0627010605090a0e160f090e0309031c021011070312020304020d0210110601080c01 69
    0x1940380180e18148060340da14031301d6a116011450b0044000f0f10401d0940c040d14020400001d038484540e800c600607107600c011520001440402c041d0498600032040701e90001420848078406050740c914850034100d81480d5000245d080d040060b40c00c20304000d0040541a590310200c0a00210001e80c001e4400b0351160304c02d160040f10840e40000c0c0c02c0243c44e8030741c01402c5907445225510b204a03603450f5000100d20380070301101d5101c10040161170b00c00d403400142c0300c050040441042d050f00640850201145e410500180301c1c135151108141d4020f8179001000846800030040e0509200c004040c510826141c00c000183c21540c040e07105080e0b80011504021240c500d46025540c0d20541c01001c1d0550008060321552090300810703000e120495005403000c1100c008458400ca0304a03100800c82d2400c04140320007415841040c0350449403041d034045140d810a0303000503194400d9140c000788510160f01300d00315042d116841c0070605044010446100e9611f412000d512407010307510003400984 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 509132805 1250 509131555 509131577
    0x2091f020a230a0803101805011706010602031804060504020a0806040b010f020a0b07090f08010e0c1804110103020c120c01051006050f0c12040816090e120d09050a050a03 75
    0x1a80c62065110903898000803c40c0c040550307111001034000404035904644c2c501000502d04c400d84685101c005d0801400140940c100500c4100e0612a0620b607071150f400170005100b460380000c111000c40d00100300618030b120058001038060030541d001076410a00108030031003040e4002c4a81030044504450510904034141300456242c001e900d000c0005a101464803804649400d4a65410a10310310b0003c0041d40c0364414900e04ea0340325400f264480e07649021003c841c02044c05903c00f5484112501c1b65144006d6981064a10015202805406101202c180d82e68000c0d41260880d245950540b104e03c510558080100d40001c03510038115400c10000a08040361040f010003550141e845481c00e168241181e03051715040400500c450f4410500303082d65080343d0790301400080c12110002c01414548a40071201001503030300001c40c09090045140f003c40d000b16040380d4105159030490784a400301041040a080000c1000c1c044c0e00885040030184000426003030380c050300907242c0280c0c483e = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 509134055 1250 509132805 509132843
    0x20409091b140609010806031606020f010e1501090b01020a05061302030c040b060703050318030f0d0b0a050609010f05161208012705070c0507080f010e010902090a02091f020a 77
    0x9a000500c01d601c08420031580340c0c0f56004511b1b1070f4008101808440320040f1003041d0f400b070908190040d6016a001580d020a03c0f40240500c1081082e10400f511101c2d6014081141c02141806800a16625140c401d200c41c2d02c20040743e1186a08407040724aa42050046868039081214044c0d00174041c5204d801d4460805004854004001030140303442c0c203815480c111510341014020300d5010400900e41140c20300d00700007400311600440050b030780c1e541c01c6c504894200e48508403c580122003150007088036603600b209844038914282011080c1d45032816080b510b42c4100b495080b040f401000051b000d114126040c1300e903070310b820f4072050030590b2900b0700d64900300c0700d034890710b0300b800180d030018180d440d01a08001c1c2c1051250070403221000381540c43d28101600b5402c888000c0d40304020040704080c0074010302e000d48003070b0b200801c882081074000c64400ea20081000340080d4000541110f107072501c000d210360100c00451050000d800100c00291111018141594002c0418200c22801 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 509135305 1250 509134055 509134079
    0x30f03040305030714100911010f0809101d030f04050a050303070c1a04090e060601232a0a0503040302010311030903090112020d14160f0f030b04020409091b 69
    0xe640c101009600300f804d20342c0c940302c0c800e0541c42401003d00510b1407013001c00d02540294410544580e01c0c500d5001002000100390f0300a801c1404100a03502c0305125600c00c002c1480000142a4000030443c80e100c090200a078103c40484074645102c00548041d400201d10058415158101d0751202001d03500c008240e80c9000d41040030b0500340d1b40107410048514949511035460b03940e40002418182c0e0343c3c0d02841260000320026440760451410801c4941c4d01c540d4011107201400304501480c140444000e00c0782c0030340c1016914030701356403484640740c9101000241030190398004907030602c1064900a916608244012408039003070800d04005151240c041e60312905000c1e00079424401180c2c0110345c041c82d0855600340d800c0d800c000d500f031b0800081c01440052001b0080e001ca580c10283c00e0000c6001c440e90184d001c014000309440f840582c0b003607010700700800030b26020401803085000207009200b03d6105030050f030b2406e0b030031804002c1488400301d5403c4440c045241170660300c000410007 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 509136555 1250 509135305 509135309
    0xb0304020a08150c0d060906060e030c010342150318022d04060807240e01111507080106121e200a0903021302041d0402040906051005030f0304 63
    0x60703e1410000584641c81c40710140c2000742c0300c0702022914a135581118405c1f940e160b0403282c0044d107865400300355400c0410004d002814203107420041d0141c6c08001001d0714808480c0e46c8910700e608010100b903c10100380c050340b040f404411140d0b40c60345d00c460229000480c0d00501e0042418481121845036400308070406c901e40280000100303030580d500701c1d80c05038405161f00f4844414020b090f801e0b91102c0c450b007400340c440e0500810a031801d0006840900c5000050036030004852000c0482c4140c0c0030b42c0300a184a000e00f408100030310040300d001c0c00c010b0a201200c00107a051000c0042036035200c040213048543c562103031088050b2542998054501c0c0481c2e422901c510b582c01c08000c0b12a81d80b081c0840120482c03d0709590b441018048215880303100d4082c00543e040f10240194901078800c3d240d90349200c20210714040c40d01c0c940c02801c04140000c008800780a200040a5464a4105460090b8001400c00051070031661909941c4031500a0030b0103442050800080c0080000803542 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 509137805 1250 509136555 509136583
    0x7060e060417031b011d12090d0c0b0c010213050306091b012105071b0f0b0a0b090f1501091406090301290117010302010c030807180b0304020a08 64
    0x11070182800c40c0c4401c20320080350054250302c0100700c02c0906400b500d620000c000c82407000828200c16000364054468040c06250003190021810781407001201011102000320039203070240c0304040d80c20f000404600316802044424400100000c0c9614194014042128201801e17800f00d0b465200b0300d50340c1d00c0c3c11981c0c0103565100c40b82c5c17030002960b2201c800309403c0052510010340702d0110100c1c4824810360820b02e400c2c5407135005000445410501c00d44400060b580c210407a0000c6444203032079500155400350810b110103010402e116000d4101c0c12000d40301414200c4942001c04118591100407100400020806c41000c8800d40c1b00301e40080807a034243c00401d0414503400200b020301d900c1103c9a80d031545d80e60410154203104440c1d0068035a0b1980c40702c0300c00000d03e9001402c0381d0111150556101c40f05c400510050381c0020740001c0b059054640f001e01c5030780300e20050b10340c1c1e6410110862071111104002410b40d184000462260340300340c40e002c50b4281e40e0801d40fa52042490301c581 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 509139055 1250 509137805 509137807
    0x90c02060403201006080d020607020d08090a06090b09010f420f080d0e06040b16021c06110408060610030908031015090303080703181e0507060e06 65
    0xe000700748550403d0780c0d55a02c182c0e0303600f495280068901d28200c41007031050b44042d243e02c0c04202100c000d01c580b00c00b070b1071103001420040c0b070031800003920b543c0c41001d29428408013030003280c1c502d00304000700d8000a1707004804003e042460f08281c0031411084030b42901d42d60034030707484458448150180d00405003110781a02c4a428cc0c1110401c1200c5a948500072881050f1900074507100701d12071124020a41c1044459070310341410320382401c243c80440440b00388206c800c0041c242d0f0301d401d003c90701207806807003040792200b020381c9081c08403030000d20000e940b007181e02c094012003091003c102d400c254420003041184020b40080c0d0001d6008034402d0054580024000541d6070610745581e03000080706150000b0f040015940307420a580090390000850301c10558180718859500540384a003140a040401c0890700d075903001003210000030801d0007056150f81c02c0d1401d80c0c3c40001c00c2c148260340703c581e4134611104401e4401d20708403411025104c0e481140000240c0b14000c405c1c610654501500705 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 509140305 1250 509139055 509139061
    0x7170a0e09071d06090301180323090a030312020904140109060e010b040e071205150f04021e090301091401020702011b08030406110d09050c030601140a150e0a1806090c0206 76
    0x51078100171000394041d503c0c3c081088281903c0840420154401c1d111911800404800b8079041324030300118004c0c2d070108020043c2c8551391850010201e03541031804009019094204201a0017980c1d405900a8280b003d41d80881131103039112416100850420081075545940190004000f0300c59500d642208110a00040700ea440070303590305c840c95040c070342203405070f034007170745080b5003084542406001e0b803140445070074038044400c0080624212003d505140c040e0448402030f01e180110643c1d40708001981d0510764a003900310003e05608261080702020040703002038040d5000c0c0c0d4089000410804141d9680410b404c9440040c0d07030484052400c1da99199a02002011800829107480e0024840c010842801d4000d104e41c0611071000f0b003030702c034501c04149490080d060b004a5070305588802d0f180540e840d420182c50860342e1540010700c00480701c43d001d40300b810080c98035540100b00c0c079501007000030003c2092500c0281042c010441565100c4503002202c0000d070b40340e40140c0004001c = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 509141555 1250 509140305 509140309
    0x40f0302040e0a15020703021203060f0405070e060d15050a150c1106160605071b1e080316090905060f04050405010b1f020c0d08040b07170a0e09071d 66
    0x2001c0103500410b0700701c81180c4000c0d10b03501311350103d100380705240a4002070341c0010076506000d40c1e1030110801c454039045092110005042210083c1c05600842da120300190300c151040803803030710500d00070b4000d0b640c41003161201005400d202c19181200804050001103904001052034200c8020500c004010350380994200c0306506d0303131441981c16605a140c03c0180c2c0e645c05004210000c00100407041c2118030b0714000058450050000d424040c2c400c290700307501c2c1120840c16101c0341e0700c45070300c01700426401e5111111401c0c04401820119000c000c001c0c01110808003003602c0181500c0d448072007030343c03145284203884044a4042d0030508074110009107003003d400003034000e0702c144004034895003144040b40c03002c403a9100f10201c1341301983c249050643c041c86090000801aa407070082c4090944030303018144250702c1000304001002880c203080c040c580d00e20101c42207081c500555551003106004104503491440b0038805d2075509c000c104450b0088901462062521154425412040302 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 509142805 1250 509141555 509141561
    0x4021503090a02040c030501210203030d0e031207020c0a080102190804031b080306150f12100905040f060f0c020c040c2f06062202030423010903080705040f030204 72
    0x850107a485401c441c8001a0355501814100311010ba500040640c5041440c1d50307a000802031444601490500316005620003108031380152003c402c01280002d10300752118a9481221a8200e0514000d001e102e105035012410040b403000031108298200c0d22104002c2c202e210b005800000c5841c50460500154000c1c21000da02c1402401e0060080700001d80b6003560341c4100c0c0049074000e00c00420040d061402204040b1140159070003a07040c24020075411529101d40006504010b0200700018038001e10881c503000a0f04080400340418101407500220440b1044011a80b403810007200386a042118455a42182c0550b40241201101c0c282400f004005200341101084440c801c0f1000c0314400c03001c001049114a502c80d0108100e03005498200381026010502c134050003800591110b1205404480304440d044006949480d2454055103400314100d088080ea0004261343c00c100806511a50700140a85c8403528507a40b4004122458420340c003a000c0c80210b205814409030034980c0c = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 509144055 1250 509142805 509142811
    0x209060d08030a091101050c0316032d030c0e0f0d0206070c0b0a020129090a1b020303100e07051b070f150206091603142d0f070f090c0210020a1d0904021503 69
    0x20408141400c5403205010088003904084812802e001c001010407503414468000c03e00ec4a242030321325010040000781012100000c07040c41001c00c10115802d564865003161240381d408403002c00100d98905035080c1c40d4000c071a4a0740554031384410456086400306240016609242d10a06160800c404018824002400c003040841d640c01101c080446400c000c031490309010f4004544034a8000420306100a0941040c2000c0050409008115810000b9070754010f46030150a002d0301c1007000c0c01860105107510000308403540110014100081d08070501e0168195826190700f50b40d04150903580300e940d19803001d00003240301c0041021640d6800a21040c0851409aa00b080e0312042e00980c03c19200d40c04170503a502c92140507184840402c01203424050314000307055a103140c204013400c9a10310344504428640c860440d011040e1081c043d548140c4044902152550b1526000400b10400b40c0151010f14502510108075440d10340030141c800c07a4028080c03002c00310942000442c0c1e030405 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 509145305 1250 509144055 509144057
    0x40b04030f141602090c040303020705010f02030f0f04361104080f0708060123010302211f050901120f0c180504111c0209060d08030a091101050c031603 67
    0xe800031540b003036200300810080004440030038203506107004000c0c0d00700c80644034038040d500800003000000d80102d0300d501100d03000d091038688007061401c1641148911600003135000d0000800020755080a4090f000340c6204004a0196200014070348035060102c00161071818159900d45030601e0702900600d4403066a18034981c1020364a290183c03500043c1300480c0d06c5504000401d100c0d1000400c90580100340c150a03d448415152000440564281d0001070405030005100702e110402e00c0341400c2c400b04244045802403500fa5071858544100c10381600e2034614041c400245460002d1005040e03072010320482ca100851a600c2d10b0b6051030003403045607810f50124000078001e42c0315100c2c280110244001080514062070244080c10450014600c42c44540c1000715901243c0740118980c141d06642c215010346034600000c140402c2070300300074480ba174008108054400181c01c0080920b22503400002917050385c0d80103450600500031041d0595009120703100c2c501c1080300d00b113070440b070107 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 509146555 1250 509145305 509145317
    0x5060c0d0e010911091e0103030e060708120615040503030d020717040b0a0306090903080f0919050c03070602030301230f040e061005010f051b01060f0f0303020c09040b04030f 77
    0x250406030a448440c035003075130041036a02c4010306a040c12000c0701c0d0721460303401203450b11b24044e80c84600c682c03406000103400c00050100c01903031034585504407404c16400110640d00c88100446c642d215240460f401d07030090180116080030140f464040d1800e0380e000402850900c088030388140002d410015050710802d44280032280011341504c01400601901d840740c0741d5420386030f000070301520195800142401e14005207007020030707404200c082d0010305100160318580c58002e4042d10f071030b51419600c030000c800103112004102e4000b43c0c1c213501540a40075541d88030341e60710082c0d80300d01092203281e08507454103189200720403d41d44101080d44000b82004210700d80d03000800c08440e0320529110056001c9000d00c0020860702034554020282441c03c0a48464540310040c1280241c0c1c24000c440c48406038001080c00303082d000840a070001146100d81c060ba01c0c07511195200440c4000d8015000d01f9051015074108844458800c0b03401900614a5880c0c0da80c2c125689521400c41c0420012 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 509147805 1250 509146555 509146571
    0x9080d0219050106151d091608040204060503060c0a0315080c010c06020c0d120509010603080906070309150306060f080709050f061201030804050102010b0103021201120c0e0a020315060705060c0d 86
    0x140b400c2c150403009000340c1d100d0559900c120b088040390505403406d82d2180e0010010807117010850322080000401c030b4a00728a003910790788040303005020142c01140d89401128100b0030580035410252407602c0460303a062104070500214058469998062540260080d0000400725401100d40f0a103880c4503140040ca4003180001c41c50424990064280010716042c410380e85c0c0c04e07203e000d1150006010002003003500e2030340d07580d03901521800003014002c1101084281c28180190307460001440317200210381040000e401c000b0003c14081c002c0e4030200307064626494081d4420040140300314500c2d201d081a4509210412414800b00c0300410380c003510030004040060f00c0400014000c51160044a1b11a414040007909440b91101c0450400d40305220701b0448083c82c0ca00c0c50304641241e0b03400c44003400941000d0b2030f650f8040d00300e000b840e100c000900400c059603a009520030035141c980b114201240004108880c400c02c0d074007a065a004a011800b881416001880c070719170807140c0010129 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 509149055 1250 509147805 509147819
    0x15090e090601090c170f0c040b0d0203040b010815040f170a0f12140f0402060906030708040b060a030210111e0106031a16110309060d0c09080d0219050106 68
    0x140031580385165410100040011640c0b60045071010032840c10000e0010820040c0850b640c00002c04503e60280c6010202e250480444222400b4140000901d90b540c040c000300031000c4d51041d00e08981c40c101ca480001104032001c1000001d010304d1410000194907aa1200c0291903200c400588591a41d403541250701e82990000303008840b030076250401a0000c1420141c0720051100f1b009140605200c254181400d944405c2a444290054640700c2a213890010030303180c0c029440e031940c000341c0000c14450050f411028162050f44070741c0c00a0803950360712080c0b000b403108074440207411100011034040c140380260301102c080d2400c0c000329a2a4240c004801239512047d108690081c1d550354018820b000e40107004404821202010940ea070401d49540d010082480c1110010084036000300b502d0001c09108585041d0b000420b082e403200c6917a8150002488404030f8500442d112030000140d2540200c1c1e0722140f0410703500582452010700000c0b40c0360001595040394103551b5200041400c13 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 509150305 1250 509149055 509149079
    0x1501120c081509090d0e0f0a060809010614031f09050a080403050705040912050702010c0b18010605060702060405010819050a062102010f0e0a0e040302010c2703020d080d0e0c0f090103020a1509 85
    0x21301c12560740510314208102c04a003100da040e08050400d50652810343c04648000807005800940e2448100203009011141c0d030003081d401400501c0ea000d44600d98054c04510405002900d0144084c0d84c2990743d80c004100072144100c0b40106019034000c1407014076400b640203422000e006061580d034004090307590010545080701c084034143d011082040c03401c1c3c1c0c01d00c202030182c4015141c00b4600203040d00040c3c401d0155205040c1003040038000a50342502880341e074241c140c1c954009210703034201300c2286400303407020713000703802540d20384580d6418001070003d8801800c90301a120170b000180214002c5600c24980341020b0340101c01e400c00002d400d11070111380c500c00ea00a40c00080c441d119114024202d210f100c00a001c0701d4100b41c0c000300034606030300c2c4280032240d04450306000b68065103060585030003411440c01f400e82c500300c070400d5a03010106116006140481d00c01c200041700741c0c1013000c0610280400b03034102680c2042400300c078903140d010b27042010031800c1046180b9501d40c2e0701d2402c = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 509151555 1250 509150305 509150309
    0x712140f061603050c03010b3a18030c080a0e03100c0305090a21030b060a090503070b280c0503040909030215010b031501120c081509090d0e0f0a 64
    0x45038041c03401c000e2201c80303214021101d07081c1c626040c0320350b040c1205018282d02040c062002541e400041d041401080650b40d11501116448103507907140d00b406507200c62030b9919010240307c500381850130464002821401c07000c290f041d201c804c10b0001c50385898150703402c150030103014401141c185620781d0750b0070015042c20002c900c20210311a034503150010300f0b4510281402d0600d0b844003da0b0305c0041d0000005520811210074152030310407544000701c1c0601440c0c032016411010003d52089070350741c050401400e50b2011741c203c8605541d600501795a41c414401038071440d82111650f02a446200140d07000c051200d072030801032241d00d90312001c0c10740d40542d01c82c40501b5601c200e41c13820943c040c440c165081038400c602c03200d81c3d858200d034030142c0c0c44020420700e500d041b00e501c000c895a001e0342d4040742d06100842d08009280075000301500300c000941c2c2c1149450391a945500e07031882c003950703d0b602c0746100070094110030280101c00d840b8528200c00c0d95921541e26110148591108c160700b0340 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 509152805 1250 509151555 509151583
    0x402040b091008160c051501120c0e07020d11010212010b070b07050a0e10020a0b0106022b1e09080604230606031b040e01020f0406120b03071214 64
    0x3558058000c10082c4202c0d41d0781448061009010411081c120301d2801c1100d610030038100520000302614146050500c13002d03062100c038a2940c00414202184003000c20228403865400060b99110b000c40404004111000c1c40142e00c01480813022911408103e10081282000503081c540c80705207824604400b6085101040c002082200130300000c000c003c0d4200955041c2249010b0b4643d00051401001606039801a24580e8810240340d208210140c10303a9000360403a000d030f5844d0180251580000d008500c20034480101a013810000c0d04c000520300d603520303120305510324a9100704251030f8070303022050814042c4a44000034080020320441f84120300c0340034890400300346240d013541c070107000b07860442c1c40b944107508009858400080100b554084601180da4080c04000010080c01d4500d00c4041c1e12b50001c61000103041c0030344e014005403401070700c44c0028600b40001c44c208443d02140b81c50b80c198082a010080c0041d0341c00f2804a01d4080c4007200c103122500c00103146030044030003000d030b = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 509154055 1250 509152805 509152807
    0x4090609091b050a270e0c03071a0403030f020703050a05010b010f08040c060809010e01020c1605010804050c042705100f0c0806090a0b0a0e0403021002030f1906050402040b 76
    0x140030440504200030244201e00301c4030350b505003040089500460180a11200f80103000b80d0b411003105038035600c480c15180b240e024001440041c80300380d1540824556107029105110340840d2a01100d0303000406c01c5004510340b410180396840445401e4184040c0e041035004000c00400450000e00100c100c9034010000440c14030003410005122101c001451410800b206080c0800503055448000440301603151601c1981c4030407889034014940034100c068030758800100c03481e00c5000440e411102480c1807801e802e1f0143e1725001941d43e5202142c004140d90400b5a004195103043c0e401500c0b07092074040c02c411070201e001c0350082c102068844c203540c9680207a0b4907854801d428007034414030664441c030610114498440c050504000030b4501031240c1a800c0c009a03c024842d402190442d800600c40750242d50b4462010300031500645095006000308011007810030498000c07a4060200341012100039681e2202c06103c0c441d8010f00440c0c1103440b444005080c1d0364900141000d400c80400c02 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 509155305 1250 509154055 509154071
    0x8030702160b0a0c110a0b040f080f03030906010312051303060222050a0303030914011d063105011e1a0d020109050910121a130b0a090804090609 64
    0x68280e01210392000c8040361007044643c42c242d03030185004e2151a4822036480c2e03d00c0b583c8001030085450380d00500d00d0790a0109001500c20140c662040844a8100c2583c4104000220351038491004480842096000d80300420004030341030641118000d4a240144c11300c0007121020b0f05c00181a0301c1520031680216603c09200f414006c58281d000a100307051b03031594503207004501822100d200180038555546544c00c2400120340c0720711601d040f0b68000b00002e0780d440118540b10985c2c01c0c4406c42c40e01c644800182610005444081d60200301c244612024a090390000c06051600e0011500e6540729405414860000c0c141001c248292810125100f61030984403c0c01001442c80035100d000c0d0810b00c0b1002d41d0f08900c60f401502d0090315248c526a0b030b0b491410003d50707072541c0560f40d00c851140c81030f41030060f10001400030102c07031100000d046d224400c0011058526031360150031030011341c0229076242d03100c1c0d01c141c54aa00c40c42d100740c2031650320300708542182c01c01c4c0e0101081540754401 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 509156555 1250 509155305 509155333
    0x3170d0c020a171305030106092405060910031b1d0103140c03040c1205070906080303060127082d12040623180f0d0803040b07090308030702 62
    0x4941031016144001d1000954540342e003621a142c08076450307141e10000a02c040d8210440340000d015000150080c0641991121054002c0c04030308140741e0b42c0c1406d5200c114048a0365098141241c0300141340d2418604d814041001d0104a81c000005140c3d503140c1c1c40004000c0855000302e01e0519403981c1e620300080151355501d9444410941e41010715020802d10450780c00314200c1d03000001600440c0e04c0350385516000340014001e4100b046034036510380c0300c00100940050034078166034030103000b840055940c407000341d584d000955000303011510100364603042c50290b020f40400b2000b1a420900b025a03100c203514101031040a18040700007100722454540e4207000c000c000c1c3c031240710005012a41c81161154040e00590181408100c801e1441c0300e040d19881d903070b4200d5014616045aa0307541c03065000d90031520101041c03401008444801c0c5500d182c506141c103030b560b410071a202e1075a96150380e076900f014802440c06050145403880070011811142c007840c490b0130a071700180f483c480a014 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 509157805 1250 509156555 509156561
    0x7150203070c021e030601080115140f0a0801020307021002070b060409020a0b0f041707060917030f03070e0f04111209031905030a0f150b0315060f040e010e0402091303020703170d 79
    0x1c0f041e8280e040212207c8103090560f242001ca480c2c8040071014410640c0c0041c1a08003d40c3340b03942d10000346100410070150650095001d0000c81e003c0364502c0c991442a035059001d55140900300c0b0203250300152050a25400c003010440c4000c1254071240e03151480341c100c3d41c1008480d1101805c012a0a201103011104501810038031a001804203070320b0710200034201c0d0360394000c1d4900c419445820410700302e030410540d03e100900004098503890019401072920741420302c081c0c0704640d4005c0c030a4581c2403a228240340c2c0b07000400150b00e00919802c81c0d030200c0402400c105d4039444204400403c0f0a81640e80c07040700210380d82e9560345c03800c0c45000d4000740c0d112030030804416850140940c0e41c00d04ca20f580d0100b126200301860ba100e0303884c02402c598505d6140d0040350890400200c115090318104000d00c1526102140a645a622001c00d00030040049074001c0d00502c0d8100400d80f0314a0288044401501c02e1040754103403a00c0b03a0710200d015054000f02c00500070046407107420044580 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 509159055 1250 509157805 509157809
    0x2030f0c190806270709090506070f1b050307080304030305040309090c0915170103140d140d0b12031c0c050306030c01030b010c08040e0f0c07150203070c021e030601 73
    0x151050070742d04085240b030301c42e40003511408200d203400a280503192003041031040403070340c0c00302070700d522a40c0c0300d245901911700301c1c800b21080c2c0291000200058081c0410f104100500d680b02000c0761000131000d0011000c5001c143c2d4140303c140900000114820300451160317100790f90100b824105480c01408030f10841d000390010500f88442460800e502c00300303000c110b641c100180031085441c058240c0d44001c0e021080b02c51700100100100070f006171a00030341c02401042c0200e980c8940f0186086421040d0042480481c00c0b0400581214035003a8125009528000308072521902c0c03d80901480d5900200c2e003201c48080030303500100c1000461141d24451881d509006182d071070608000f035191201c008415060542d43c10150190380d12409080003540e5004003515602da40b600ba44400943d012944007414941907800140f1480307e040075680e80135031000340480c0b16114481c000c4069000207158008000c410807045c070250360b40c0720641a0302c400c2c80c240d00000480f00018141400e40503 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 509160305 1250 509159055 509159089
    0x70308150f061308010c1e0f0e061603020c040b0f09040c17100606090b0901030e010e03040308030402100e0102030f03150904080d0f06050d15060803030f01060e030d2a02030f0c 78
    0x501c06500c440060f601c400741c03080311280323807100156022440a507030b100388820a06800c1000401d41800b00400c03991200356040c0641c080b04c0da1503650008200540f40c00c00607a9411269805840304d00f810444c900680181c0304030f030b40251076503c50000c03205034811100c540205901103480b002c00081d052080ca00540004c2c03900440207030402800e0107052050590f0541091350300d01103400001020740c090780480a82500b52640c0f103030340e030400520a42042d202a031081c0d0001ea01c100e18940240200b400702e01c4107330051420126850260401034000424010f440050345c605e0400c0d80e07031810b0000303100758840c4034039944800d4440051801c91b6040a1920350f0141b524006200caa5107900d40c814840354000c071074595100c028600303a0041e060540c003214441c07001105102490462403e030038145c440c9551104400e02c00c101c01c0503500c03500080254080750070402600404440501c00d070b0003800b1400c000f4452121950701107880c1c044000591160341d0400b002d0341840740303000c2a8440c903080301 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 509161555 1250 509160305 509160317
    0x8100807030c060806030a06020d0c090e040308041e0203060138040b0c070b07080301170a120809011b02031309060b091c08031f0902070308150f061308010c 69
    0x640da902ca02e140b07020301582044c40380c95030000750207a03000c1140910702c07988010255215040100341300c1c043c002151055000c41d1114401080500b200040f10384125019501d58181d0f84481c1c8800c841801040303038400403040d1105d00480036803000c02925000300700d0041d2403070f2540e500700d14a50702c024681c090f44240301e4a6118279500c80d2864400d842c01c0d50744240409594081004002d0718284d003c1c0e10440f812000402c641c0c3c280288500518120f81c1809440050b64848298054a40840ca50000d0410000855810100d40f0502d20a80d0040102c400081d4030508940070205548070301140c00010f900008206501410a50210005044201d0140044c50400c00d03e41541d0003183d15082c080d54150600c4400540810803000300b140d0404507056403428076000d61540049800f0b1002e0030740c25110343c0080c0311813a40c42242e6140d03400d039640b40807545401c044001e80031040540c040e44403e051303407030014036512040101b200c0c0400801d41651207250200883c01d5035404018401403041c = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 509162805 1250 509161555 509161559
    0x10501061e0203280504083019030218040f09020f04180b041e110a0e1909020301020d33030302031c02040f0803070201030b0603061c0f1208100807 65
    0x14242d08483c0310102880b504884080207040c0072507140c041c0d03a21007c002c1c0b207001024504256503103c41a40c1200720318020110401e0a0b490b01c00d280700b88050040710100714540c034511a84607501610960090f450104000305071540000c0580f486000742c0703080f65503140540c5086281203d8a16841c40c010f803408c0c451241482201030445201c060050646180c0000180c01c02009001501d80101d4090800740720307000c1d81c141040d005540717404c010300031031720b00300c0116481c218460458450310f81502c8105800f003010444201404e04400b00300e80640d000e00c079102e03000304d1501038044903164640c401c28000110101e514044e040040b0442805445600244042a408421544242050740380d4000c000c6400403844001e00c107990203020005151480491007040201c010450b56000340d805103c6d0302107040410544d840265010b0f80d1122841604048500301c0d0900911640c0c06005911880c14081d19000300c4101c00d52040380002c1e80a60410814900241008000c3c240900c014031000d8 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 509164055 1250 509162805 509162827
    0x40e0a03050c010b1203040f080304050604060e01090801050c091302040b2d031003230304120611030112030215040209062209120e04090b07030914010501061e0203 72
    0x42058090200040014154103003802500140c0a01401511001d80c80180154850316a0030901440d46000003d0100003045880002614240c80c1e00034800c514041c90310130142c1d56a0040c0c055541440030103180003d02030300c00e1048034440c0740c48a51595481030281c040203002c0d40da60700c214a21520510003802404c043c4000d03201c010032001004894816134004010a03400303210b8400900300d100000b0445030350882c4201e10f0460317125460081c20705c107000d99800802030580302030300c11551060004210750300305800e110942c103000300e03070000e01503c0c0c05000a0140d07100740c00501c0046d0358112004101541001400c118122031100f12200c2e00740766000a000640103030902c1d205a100446168505060b020044c603042e43d9007a08005000365803a22001c0000404c0141010035100600b406d010b0509018050382c440e4068018460755407540030a42c0100400181500c0c100304541031410204424480c950103851180c03980c07030320350004071582c92004c9201a940c0c07085400900038800c1034 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 509165305 1250 509164055 509164063
    0x9010c030c1119050316030512091b0120030403060605090105030a0b27010c030b01020d090315020c16060210050c0705030901081807031b0503061e0604090c08010f0b040e 75
    0x283d040c000f00c0d48040b07440c01c2491440c0244018104845100b5a06808242e0490300500c11502d003d40900b030f403641c030001c1050715941a03442d89000e04201d20555180c0390320464036002d0f04802d4400508171401c807003031040c0c90740d082600f0458100d0b070746000238081403800001190040604030010580d11076113945400110101030085112803c4003078002400c92594000a01150f0100008100450000d40000c001c2e084d0440d049000d80600b16040ca05540b050702610b01340c9030051449201d4040d00a4040c0c002d40c80245a601075020343ea04001c40751903e5940180204040e0b4020303d0040c1003444084102c1c3c1e405007400c2c11211041010000150300401aa0141d002c00d080514041d42d94051085110440e030800f40c2c44d0f800f444c1c0f070200c10002045642409201c10a0070040c83e0758480040c9503491000340c0e1031030700480c005842640030703100d8000c2d020f51100c806400480e80000c2a078500241c3e044a8128403078694650f403007086080414450505821130854007401400c500380074498039 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 509166555 1250 509165305 509165323
    0x91407080a0c090b0d060b040b04110d0e1207020d1a0403051e041805060103060b0301170105160813080705070608250518060702030601060c0b07180e180609010c030c11 74
    0x40c0d58687c107418190340e81d158402c8170032400160051103c0c0200751100c1e00d03039070b10103007145a2a07032522040c1c281c44240014400c928400b42e450315850040340303800304a031445503406c046030500280c081482074401200c0c00c1d50302443c800e4030742d01e44031f2070031b0166941c025150f1500200e4244043c401000b148542d560041d52040468000082c1c030384031200120080d1446402884400c0c90010000519070300d005550460741c10440c0081119031145003c00c40010b5014a80e4800601100081b0b24036075490b0000059840c070503208035203051020741e5250705020b10790f401900071440c41010040405504c00d139607049505001580c40c0103203900754015000e0700681c0480001440c0a0114240503213800c0c04403158190001d0413a1015a2348500090000c001c2c100d0443e011490300d004104d58900420f07900c02200712000307603142c1d102d0900b4860400c0000052042e101801c1c0300d441d02d1121a0148011402440107034008946010507200207401e58960ba00400c00300300c00c090300c41040c4c0e00c0204010038 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 509167805 1250 509166555 509166563
    0x60d020a0c051506010c29091b1c121b0305041508100b030601090801090b161b084006180527070c0b0a0b03060a091407080a0c090b0d 59
    0x149810040c1c0549030320344000039000d065180b800d018040c0c0305900040d2003044003192690717122703184e55410a0044801500442440d000505031815000903890301032040403001c58688081400c1c02c400740c801d40f5201080c0250007140380028244000705d02541c0c2540c030300c48242448855818500584151480b003481080382c1c03904e010010440700e82c400c40d0180024502c0400910000242d400c00e1019020155142072500204e10301ca06e0a550050308020801030b142c50000843c3c11940e1662070142e0300101c030b07070100104050602113522030200000c40046044002072042c03481c104482d40041c010642240d028841420016548503441181e403c051358429905040301c0d6200c90a51503800450054880388003100c1c030208040b29910040080c00325004140e15841626500324001c01c43e064074002d20707055000b0500080e007a180300d40240c8443c0f48a412480b0803009803002c514141800b6070004503d9820044961050100c00054138020304040c04080000c0340707402c4002014003924020080c = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 509169055 1250 509167805 509167823
    0xc10090302010b0604030606150224070210020c0a0203151302041806020406080907090204030f0b1302031603021201061413020415030b041505060a0e060d020a0c051506010c 76
    0x9800c251003034000083c0850090000f580b65034407450003102401071070146000310f4404581c03220007544001a84140b07248500d110b511048440100b016010400801400640c46040c14080044203607100a000050344c80018021818680c410141001005489800d07414200e0050140405481e8800c81c041a81210b0001d29800c1c020b07581440c0b991240006451680b010400143e407640042040d8440d40600d425640d1440c0c540c3c0301003040340600d000142c1040c0c140c492540024003480050b0b5000040d0008a0399403c2095001038030344090f010200c4904140b00f1020021070030244026081e0300704040c000c0c170110703041071143c00d9100050500f961040c2c106000e05440352a80750704a50180204190001201c28042d01c050041d040f19014035000300d19110b4224403071820310070002c7c00c0d544020429441c0c42c510b081d00f11007039440b00500e07650165003005950940d5a1a100030700e42c104468913031510b2002c0c235090031818114a0350003552030200280401a85a03030002d00100c1e0607a01c44a00 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 509170305 1250 509169055 509169071
    0x302010e0a021302091201092306090d030216020316180b060d0b0607061a0a0503031305061c1a1203040f0308031005120a0b09030a0c260d0506150c10 66
    0x7840300c6c03a8148645455407034103050b03c0602c4030100444a01c4414584c40c00c9088004443c8142e0f109000c5a0340e140c42d821424111016612980050400420070a0300500d0b015a50700003c1c14080040589002100800c00401901541e00340c1840385c890350700020401d0b842e000020850354401c0360507501c1602d594000c0c100081e900c00090ba0040b5401c040c01f044a0360400c10710001c203540c1810480e1140203155030010301440c0010845408440c4040e102c03d1692822080c44096000900300c4e20b2499412000101c81c502640720705042c01440100324000c180e100018440c13240340181d1541842d401c108001d10074040301c1d41c034880403a0f0780611455980ea0b100c3d000300c3c80300340040d00701a0b400302404549144000700080c0e02c269840c00340c0d00c0e15225407194450a9602d01c00c0f01d040a001c100004a0440810004009001d1464980f00c0c07884801c00c5462407012590301120a0401042d035407410300250341003540719441c0045103220300360301d009800d0740c0c5150f50b031200c813900d00daa041d10741b0b0722 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 509171555 1250 509170305 509170309
    0x2001020c060c011415131a01030b0a150915030e03030c0a050d0f0b01030c030b030c120f070b1306030204030c120c030206040b09130603030806060a030204051005070302010e0a02130209 81
    0x44c0000780200e25800d02401c3c40c2c85007110002140300d80910400700e640e4081c0f0020320350302c82d070b1106582000e0310258500c0c01f00019009465200115a8020f01c80341c1d0001c1c8041c0e0742c1442d11480000341c3e0701c51801e242402c5039030100000b041250742c00c15142001c6040a0b070700000849070402c00704100d00383c4400082030301700c0e07007440350049040703c3d142812903501d0a015103401462911400740c8050002020b051421821103091810850341903202415064260a200c41c03090640b684000540780c0120003902c68030302d05103496001c01c0003010009100c80d80c0c1061003842001400c040d180542c42c062650703d6813174600c01d5a0041c060459902c080c004200920b41e52503c00555010f0900e0340c17641e5540002c68034642211016070f004100030000ca107041c0c0f4803407240b0003d5aa06459210141e120901032200a8116882c55401e2540c00c000c04200c680d038800b9821802c00301b0b51b48899a910003460003d0079250810460100c607440200c2c1c0a00581da40c0c1100c28041d081303400300589450392940 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 509172661 1106 509171555 509171561
    0xa0e030c0d12030209041d0604050609030a0801050f0d0203010504030323041a19060e0106031b0906110304030c03060603050f06090a060203060d1a042001020c060c01 73
    0x24104081c0282d015151030040a000061f2030b40640d41d041c20443c618000111344c41e40101c08100070848104442079120b4400c9010b1810900e55020113046100d041c0140d91050003d800d4908042d01c3e0400aa803019030014005d000301d0900c1c0c00c01500400d04101c09003403207003103001d00325144e004406a09000d02e9025502c0d0b545031030000d80340d041022000d800941b201d0160348140303140d50742ca8015040a0418030102c03a9182d494010041c0440d11a00e0742c0294115000700c100c02d81c140c010b1003242c210784484c188624000d485200190452250f42c00003030550703038280c2020091021540c44403041e42e04c07410071504036800c0c504031740d42d07180307022074002c1044d5100d48241d10001e981d68000e15001903000d8200300a1a00f40d41e5071f0002c001e201c21803541d4181c80c1004000030300a0100310181501514041c0403074a150890000791100070f1801c0d12801501e000440da61508803d40c = true := by decide +kernel

theorem cover : BRFrame.Cov 508992805 509172661 := by
  have h0 := BRFrame.cov_init 508992805
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508992805 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508992805 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508992805 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508992805 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508992805 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508992805 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508992805 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508992805 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508992805 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508992805 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508992805 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508992805 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508992805 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508992805 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508992805 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508992805 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508992805 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508992805 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508992805 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508992805 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508992805 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508992805 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508992805 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508992805 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508992805 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508992805 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508992805 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508992805 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508992805 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508992805 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508992805 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508992805 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508992805 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508992805 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508992805 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508992805 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508992805 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508992805 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508992805 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508992805 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508992805 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508992805 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508992805 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508992805 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508992805 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508992805 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508992805 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508992805 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508992805 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508992805 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508992805 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508992805 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508992805 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508992805 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508992805 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508992805 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508992805 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508992805 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508992805 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508992805 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508992805 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508992805 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508992805 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508992805 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508992805 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508992805 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508992805 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508992805 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508992805 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508992805 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508992805 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508992805 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508992805 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508992805 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508992805 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508992805 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508992805 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508992805 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508992805 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508992805 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508992805 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508992805 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508992805 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508992805 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508992805 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508992805 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508992805 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508992805 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508992805 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508992805 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508992805 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508992805 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508992805 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508992805 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508992805 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508992805 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508992805 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508992805 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508992805 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508992805 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508992805 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508992805 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508992805 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508992805 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508992805 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508992805 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508992805 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508992805 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508992805 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508992805 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508992805 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508992805 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508992805 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508992805 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508992805 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508992805 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508992805 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508992805 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508992805 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508992805 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508992805 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508992805 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508992805 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508992805 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508992805 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508992805 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508992805 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508992805 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508992805 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508992805 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508992805 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508992805 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508992805 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508992805 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508992805 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508992805 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508992805 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508992805 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508992805 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508992805 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508992805 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508992805 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508992805 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508992805 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 508992805 ≤ n) (h2 : n < 509172661) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
