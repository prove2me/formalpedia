-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1411
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T02:51:08.296959+00:00
-- url     : https://prove2.me/submissions/9f8af2b0-0dcd-41af-bb33-3f8283b2573b

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 253597122 ≤ n < 253776978 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 253598372 1250 253597122 253597129
    0x4090e1006030503030708130b010e091612020a0503280807020d0302070501030b0f030601051005160305030601180605221e090f11030705090d080307170f0903120603010902 76
    0x456400550f45640700100340110160b0200d14258000c1074200b4022902060780da81010f01b610610079141c05c000e60001240340c01c1d030300340b09481a0030400e681490340550f82d00403840c17400ca01c881d000c0c3d10400d00f0080026240c00c011800301c20107084480c01080420002c40445000208540240d0300c1070004e110715401a2180e4070a440624002d030010036480f0314010004050b0b0f6401101c440c012807641e0f11074103460300e0004d8128151f0390100c0304286094100f0b50101d55130300807120b40d511000b201d00407581c10306130803038006c0d400342c002030781e4100031203103000018202448103100f190001034040180d88202840305100f40040110002642c0c1003640d2201c05170228110410254802501c1ca44c0401000c9401e02c101c8080607180d05003480104440200100e07240170051615041c4400002c2c0c0162955074450703801009a400b002254882c100f02c903008180400da5401141404081000b10383d0210004c640c1038890100800194a400c1c22107031400010781001e800d981e019925150503200503038 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 253599622 1250 253598372 253598381
    0x60d0f0b0c070c061101050901020405010f0e06091005040303030c1b0803060102150a0e010b090c03010b13150503040201200c0126010801090201020d0305070804021005360f030304090e10 82
    0x561303650f034080100c00b00c400060031030f8006042c56035540e00c104000c1140c2d0360040d0b2007a10026031030400709862900c00c0089a040d2050780040f540c425940c200100615401070058002d99020f507408000921007204251005030b034900346103010304e0500c1e00303640c00100b200b40103517130010040c41550000541861143c64980064560101032600d074880039020010920541c0c08c0701c0710850f8990918140201703041480c1c4070600450f078003807a00283d5003000e41e003611600f90080030b000e0300b20341d071500301400c00030265007003510300701e001a04c1c540500000150740100c01e82c00d02c0a85002d085449420030065611403d038a8201d00442c1a001591070202d2041071400d00030141d001c00401d40c08203d01c002800d041648104005040c0350a080c400382d141e011b903881d81d000c0c0c1d050310040c04c0880580d4080d54070780a0005c0e0300700700c64980085441d04034201d400f541c0141900440c20221026140200070607040000c128580680c0148410400c08040741c0000000d032100c2026102c2c0c07176046240c96810394 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 253600872 1250 253599622 253599629
    0x20c03010c030e101e0509070806070806040b0909070b03070903021c06060803190507060b0904031d0117040f0609050d03090c0609060c020906191d060d0f0b0c070c 72
    0x303562240048442035062211010311030703400750104100740310303800704001c030507288480181031503a01c1b0001414001c040040002605580e000c6944614200310300a15007401210386601503030600c1d10f40080e9082c46030b11280900d40c034501a00c0c0d441e00300b04042190742c0005152504128240e4030010250329401868034032100b030320141e070911841078145941078035016403010a00da4001c0042d8902c50949041d507000b4003125103803040e504e00315410304002502e40c031400751340d0100c88241132208054001003905100b641d00703d00b02d4128020304006541050010000600042e005000100096988400c28024a201d054001030798196600c4844ca40b1158950000110b60b84080180610000b824004002d0001c2d28011400c2e0707042a800400030000c0c000e00074090024a40429800c4d0784102800380c0400c001c0c0d0b00c1004290381c40302400c01c0e1340d400a42905d00b485001c800700300c0318103000d00b048145940000901d0207140080e52000c04000000b0280c480000c0280a0b07080004c2c04c051281006 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 253602122 1250 253600872 253600877
    0x90803041a040201140d0207060e0f0f24090a05010c080f0906101503200901110703020f1309050118050f2b0e060c03042121020c03010c 60
    0x9030300c0c0c946003019800000d0008181c014044004000040c2c3e4401600b80201610b00d0080343c0b218001c01c10540a4007807800d0040019080280c2d0b1906c619000843d480d000710300d4411510480410513005403182260404400c3c01e032088010000316000c0488150b0b084040c3c002191071000c6203450301821500c0c180410703000100c20000b030000f8000240b20305500045204050310150416206401086009114542490342e41d243c03110740441c0280d21107a0031002d80700c0c1260b00c40307e0b091258181d540c4003000d00e40c042601780c1020260510001070392429681d02034204055248035808008910301101140c200084d203030840f0360f0009a003801030340e80d1035010b00195210a00d007850302ea401c003d2400c070494002d50001c02200b101000c41381d9964407000d918050300c1a58030764035600302d07074420400c074a45400940000380e0441d0b138a80000103200300d5005a241800c80841c241c0062040c400c8950060a0321020710304040e42c102c00c404940856215900403904080d400c034010a0a454440c0b07a250007 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 253603372 1250 253602122 253602127
    0x9020901050c011b0914011b021215060301140c041e090c0c170a1d2407030f02070602070b360f0105090603010e10080a0b091006030803060f130908 65
    0x940c0b035006801000a04840106c18403141460b00000304906070142900040a00c090100420364451103500c02c5005100380940d0b19040c00043e500600309400c0c0c0340b0318040e44c80e049c001c0a5841c5494015805440c20300c45251a162504070308140b10382007154a6103140e500914000342c030340c4452048030201c411a40390780130701c0c522030b0030292201158a802e8240c1e1042c1003204000140d03111000400e02d01c41040305080c83c018090110f1000d819460320008807a01c031081c0e00740c61003010402381070110b10a03030f20721620115101c0201e0701d0348914840c5002590280d501841070305c0f84000548100850f000306811001289030304131600b109000c070486180303040d1a01d50000b5081ca50300e006580e1a0030b00302507213003200c50000300d101c2c1c0c8014450500341061071408a50200207203040440104060801c4425108150074000617048090354102e8141c850080400f100d40864042c0100b200d400000460070355a800007032100b03071484540e0203580b040807071052440b60034840c8280d280803405481080d4 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 253604622 1250 253603372 253603421
    0x60a11030333010804030c05100e011b090602100e01020f03070e0a060302030c0f0d06030f0c150801050a060807020109051c1403040804050d112707030c0909020901050c01 75
    0x54541e61000484030101c0324000d10340c402c99070402000342c0c009a052400303003100c0849042c0541883c60541d541c0c039000e818003030641140f00054018060465080007115900810640145d42d480014814040507030045a00b00580c21520390203040e40740761350070000d468145180c1d0002d40750381c0200c403007801248103c0755041e141e042c440402d40141ca000e0070f0851840c100303020b542007107014440402c00c004000088070711013242c071038101100135a07200c80300106a4025150240e84042d160145c40c1e480c6880402c0e0540e241e1241c00703030174122840901003803604c5060840403134541000030320745030072b564071218a8400514204003140c44000c480081444000c440c40004102c4609070300c41d500d90803000d106020200308030030300716011131b00102e03440b42c800303074140c90100004101c101242d507020f00b00d05d56205074140110035440825954100b0040f4942d10380006608690296103031000254500701c0a1200c40041c1d0f0040001c000e05041076801e00b1010b20b0181d0959031101c600e071001c07140c503c0540 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 253605872 1250 253604622 253604671
    0x3080a080a140a0e03070206120f10060804060e0f0a140115050312070314040b09010e0306130605100b0d06060e151204060b0402030702150a06050f060a110303 70
    0xe6001122103000b4450b00010000c4078241980142c042a4659501c0c0c481012082c802c01c11650b40e81d6010708681d480350103540211085030000c507541504241c42e6800945100c85c000358081c03d54201d40c80c0d01c0404d45858070341c0c40003400c49400400d01c1d8400d5030710200d41e00b0790811000c00713110710981064807036042c061003244c00d40d000c4101c22808074015080c05e11803580d010452040d00020b03081880d4a0310303c60704040f2105220078004580c44900010f010071001c1c1401e00501c171440b400e0f00c03003240c24110103003419034600f0111103515914500040307260000c0c4140e041141c118040d2280580d1494079600c01d02d030160712034901240c000f659018100011600100c0031000c5220132200d60130010344404426007140f041500e801c41060310500004c0c00c1083c02d40c00790401440c042c2c070441d101e103003410b406903803116500040300b07001c030030200000c41715801c41c0160001d540015111030151141c000610440e80c1004450300c06100503613421f07118450042010b10b1252404200300c0507400c0205684 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 253607122 1250 253605872 253605887
    0x20103060909030207090903090b03180706210515060a08090f0304180b040617010c020c04020f2710270b040b0c010f060902042309010b0c011503080a 66
    0xa4a495051000802c0842d4000c00c0300c0b81201d400c0c020100303094481c2e140403225940d540d080075140300004400d01070200c5030500d40300300c1c8030001411a08020744944080e2004030108081d41d807508078904528206480c150042600041c01c20b07a29000564445c00158003a001101c140c000922044100140240204103c0880c0c1c040940614503041c00c21b03040101459254242008840e112802040c01d900d441d40581c000306600c200d01400894a05021400380012202200051180c040781035064030b403030302c00c480b0300ca4026030790f45d40342c200c0310851041181d0145218640148589030072042c540c40328400b40040500e2580c3d11900641500303010b110054810015046000071684123200da001e1210880d0240c0d6917211901d0344601402007024050301401c003041410f1410b1100001d5401480d07000341007502ca140c0350060b00c4c218145e2140e01c45282e08400c413a8400c400d2030040120b0301c01ca800403c16904284004a50f40c200c8c0d01812802840c00d9104a0718918000744040c40194001e82 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 253608372 1250 253607122 253607129
    0x61c0204121a0106050a05031008070b04090b0111071421070e0711030d0513200102010608120708160c2301020609070b030606071505040c150f1d0301020d0902010306 73
    0x80d02802c40d410601c00808074000d60450301700740440000440e191030f4030466410001d000d420300300c645154a4a94030710311a0414452107020600300301300c00c81701c3e41c011a405c00ca206040001080c6880c039082072501c0d584004403120b0303000f030380c446228080d2404850781021429100b100034200356203000c01404000324014022030400026000f010040d28010040310480c4600e0140810261100340c801ca640a240321001441e14400000c0944800c4140140812802d801d8008001c1c180d9074000c11515550000840801640100071020000d00380101502d421241d2945a004141c580d40d10040300100a4200340303014881c0c0030703d44048010700f815000d10307840c0a2020700705901341080d1a07035895409008100001d070001c00060030f1626032000f554443d41c0c00c03000071205101c480d03088500a000036103050303594a40c0403002245420943d8940f5482d031400e42e6400701e894002200807610320214400541002c076012080c220140d600340050710503e40c03440c8002820b0380043c80090f00311907481c0d0 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 253609622 1250 253608372 253608413
    0x90615090308040302060a0318120e011115090c03030a0504080c011d040c0e060d0510060302120f060301090b0c090a140a030b0a060503060f01090c031a061c020412 72
    0xc030510005500505980131254190350b2a6100ca926200c1038001d00364060443c4228404820f024040c4092513140d8141c40799107803181c0c042d44c9110300044030780701c0098400c01c50703d034028080c18400b0499090502d902ca00208181c881c0c013034801c4002030956108003440342c00260081400d01c0050810b000b450358903102402e05845038600000200d001408009840d0300c0303955600048007449004000000031b0813402000c0690380c50890510f0001048103596064600039a014049000ba01030320071140103c1016031000c10b81d0344d8100881076801d50041507a9015520f80035280005031185102900034402070380c005445104040522003c034803581c0c4884050428001a18225125401d0f1102500d82040390060140c1c3c803507076001d0152044e50301103500340c1304110401c0f01d00740741600b01a0580300c65990900c06249540000ca059851132114132061030403000021042d0314103900240541e03180207141c400d441c1e03100c1c11040b040385c0040c2c1c024124954100146820004240d0b40810b001c01443d = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 253610872 1250 253609622 253609637
    0xc080604021003090215030a020403060e0f030403200316211205070609020a0605031b0910050702043806071a10080624220f1401090615 60
    0x260000388076a030514200100f41640c56002c0c00554582e800c0b83d8100034810300b01950b680c11704210001c02940580b10591320f182c58006482100c0c074004c2070b040420241c240c010350601381907443e540060009101e0145c1d0010840b4044c450544081c001c0351018140c5054488400d0724005521a12440e8904d0340c414031a900e00e131501c00500007003d111203418507403030724980390031071450300000402c0901c5c3c020b503100031004000910701f903100d40118420102103062142510202e14000d0007030084e42d0100368000781034002241d146105a014100b2580001c20100748042501c11000203007121460f680c880b500000003601c500340c0e00b81c0d51f01c00354840546583c0c0c50021291203240c003900c90315100701e14980303008020030354000100c11040c024041c0003080e94141d05045081c9629402021400c101c1c024103221076031000e181040d01400c02e0807803c2c0c080c5040c0101d038042403000b0f2103440c1d44168125035400da0500c2800a10308001d02a00380c01e030740024154141080e926120034000c10717000c200a181c = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 253612122 1250 253610872 253610881
    0x101e030207061a01021c0c080c0a03020106060c080a1b0f0506070801050a080c0f0a030203150a060b1c09020a12080715150303110a060203040303140c041505070624030c0806 76
    0x1104801c8135910b04d41e0454009811b80c08032080c500e503c1c0003800310003002c2501c0ca480c48020a99421051081c0c0003040f506554203819901280a0200a44403201c180010050b0310b01501079045050362000fa0700700070b0030080c1c0c0c03217000962605205031a294014001c014046070090a058094042290100c0009150240340341e42c0310396518880b4051211004d00014503143e504449010319402001d80703c06114000250000e99011079407018a01d0910f140000c50220704011680000d1011969404d2624030402d114094003500000f00d801080c1c44000240c0130411403103c44062b407099103410758560355820801a0941d000800e640d5017450f120028131402000c50300c0c0c0c0103c03541810304030f0114540601003410081c403844040c1c50b05000004110415174568844a40f18404420284181d02c407240f03a03a0303942c001d80c01140c07007085200142d5002e09024002401001344a450041140030304a40c1140041441d10844404021085424000c101034014540042d00c0050020540342c9132 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 253613372 1250 253612122 253612127
    0xb1804050c04050d08040308120a05060f0d110a0e010807050117010e1303020f010c1e2f0c030106080c1804020102031204110409030f17010b0306101e030207061a01 72
    0x2140310720303032084d11308442110412501d842920002c5811007076950b00c4220b000700410100504a44100c4541d2800c80041c5082c94a10303074040460f48060103060420f1021b0740c4500389248001c61465022400c03030000a0183c0f03c047c1828082c0079000c010f008410b1400001412920700200720281c1c004980c2c00604c840c010007051164010a000c400402181c0350b404c1c1a0304241e160035406a00d5401c150120640c03d4110303d0203c21000c0e50b00d522011505514400c40f50301c003409007003680b00c031440c04071802c01490541c0300c9a03802d0002c0c800d0381c4811801d4400a400c4405a40c4104129004040407001c07514090000300075820035045032038028034040d0300003510b922980d0401118904003001142c1071003042d103401c20407c4406481000111000c6c01c1c041c11382991801c1c0c000024a18010260a04481364a0315048848001c4001d0464440c0420010b1760402500808100070030007801e6601034a6403e03800c082c807911a00e005030b580302c603400c0400036500040000411031074440740d60000b50741e = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 253614622 1250 253613372 253613377
    0x10f05061f14070b060906010c03120e01060504050103120e0a060c2d030206091c080a02070204090b100807050f011d120d09140108070f0c1b0b1804050c 67
    0x124400d0301d040844880c0740065031410403000000100140108020b070030040000b10346401a0411103c0100c55078030440111208130414100500180140440c07840d018a036800c4442c0c030f0380700d000010403003a490350b020034211a401d80c41076451142c1c10582c442d039140c001010f03c0280c0400e66071010200d0800c0030142100e04101c200400407848400c1c64944030741130b07a0f8030200012400e0460342c41804a030034020340c4d81e0401d650081c4140100c282d03101c005010340ea9203d00f10300003a11100702560b5050480c600a410085060b0b030003944960305c0c40e0001d4400029140700c0d100925518030b00e20304005406160a403180c01c1070303005131155031202c07500fa038001000e43c0403000c0b95505003c21041d02008500000840344500c5090310601c0301717241e20385410941081c15a20b841041220510380c00c0011110740a040c0d0383d000204060101035500b00d8850484c001c4428081e950714a00801200f6031000303003142680c003030003901030041404900c4010902100440c40710845040c080340c2499980c100503071 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 253615872 1250 253614622 253614649
    0xa080a0b1009060305030a0f0810180f1d0705060703080a0b0d06020d0f0e0a0305041208040503060a061706041121030d090b07080f011404290102010f0506 68
    0x90400c0e000003548501204080006842c1400d07040c0505680e034a4a00d03580c2e0000c100c800e01160a440c1080c004d0f501c5040713041c2c0328015500d04d011000b86000d48507140c00d0030400100c170300d0700d0301c41d00c0d501ca005656004a0460a00d801c11036108040c1d40000c1c2d90400c1000d0b00074521416042042002295002012503000542c2d04000510b0b5401d03400000d204000e8840002c280390700219400001485503480841d201c200c14009220190003101d84503111007081e2401800300b0030612050001441492903005110712410b800313440e01d915040044e00d400b00c01c4400035861074450209005071814103070504c0030100c2000040c62a4282030b541c411f001101038044034010464100300100104070004400700000c0704005a9585042a142c410301501005605440e0742e09420041031803980b00310001e52103100100c0c0412016401c110f04010038032828403500d039000783c5400d80c00b4050411041403030741001c0b441440070a141400310006e42503e103411500449246050100201c0c2e80b140210b49221 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 253617122 1250 253615872 253615883
    0x1101060f05090f0c250c230904080a080c070c03210201021603050c01060306021602030c03060f060607030306051003060f0614041802040308040b03190c270b0c03030a0b0a080a 77
    0x1005c4491200c0039000c0aa0409860301292500016228210440344451000c0484c600151207040c00280910700174152001403000f98108019012540300360112a08070540d0700605240ca01161035860286005400c242ea43d100803c40c225203611455040103905102c50000790306000e41902881a0b46c015100090180080040d0304259070900f94814000786a02540071501c0d0005503854212a00405104034041d03c00c4042c0d001c1e0f14640064010721030141e43d018100e003a9503040500070680c000150890a0648402c0c001c80c087e6180d0350368500b6441c065074009081c903e0910500010b0340707282d00200512a200300110000c0f5815000c03a400c1c1c0b2801900b02860750000c0003581d00a11580c2e00103000d03a44d0210f0b0104458003c100118060200305581c5010509212884000c489081c400d500119520412001e4201240f07641d00403103c6820a0b52121566148905030090344803910140701c681002080080720443c9106480120500344e8403402d910303091090740740c2c0d10742400201501 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 253618372 1250 253617122 253617157
    0x10c031d060f070915030920060414040204050604031220070302010302031902220806060105091014030a0b040e0303060d1502070503070b07020c090c16031101060f05090f0c 76
    0xc203240a4613100008001170749415800395060040200208047c00048440141c0d0311800d41900500c0540c240700c07494018800c03803806241080070b1541003c45402103801540900c4002010342d5003001800040d07000e40003400040540c010005c0694804414061411007a450200300800c07002440c1c0c42901d6082c00c0040c1e41e03450340c4801510b001030284908031554000038015400009100c40260380e08035500e405010152507010741500c030201100e100380024001e00840d120b51910385a60b03180b041903414104250207055558410030741c4100c480503e103503107481802d003041c1420303c944004a08101c000d07500b1400c1080024a00c9104020003514400d0660400c0c41440040d43c102c82c920313913004084035600c5455141901403641d00702d64843c054015289200400d045c01c980d2140314000080b160f42c0343c0012114800c0d880702d45400142c00304146030341080c810300024410f44018040792081015040d242c0020404010b4000300504019a102800c0c021410040400e5484a00040d003032400d = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 253619622 1250 253618372 253618381
    0x70e060f0301092310050105010c06020901031401140f03010203011a03180f150105040c0f03020f09040203040602180d03120b010e091603063c03020909010c031d060f 73
    0x340540fa2104003c4c0000403807105000c2c40c400f00c1190355500c140c500d82502e00d143e00703c0b031900013240c4091182c0707400300e201d40c0314150000710b04c1e5000300f000070414140020605070030011140541826080449a100410050034041c40c0820000102c150114029072456042c40900340e0000c42000107003e2486012020400c5070014020703142c51040c0203011a20960300608010b5540d141075071ba620a16141e20001141c0d40c00c05006810000c0d0403600c4880c41503210180450003580f20002e00b504001d8280170107409036440e4001036010314003400c4096240d07020311600d090641d00a0080510402c1d4a4110b800041e030803042500386840c00340c01c0000e84002d0032006071651030980001381da0296400b41000407952220100c02c1e242c00e01560104041600e07010310041c03078031070000d400ca050f825200c04a4000c0030003c0b09900b210b0414071030149840d569a011039074055066501100694550b20340900c029030502c9005140040030511031010414480d40300e0f141c0d6405443c00620240440004 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 253620872 1250 253619622 253619629
    0x140a0e090414120d0b0a1212020304080a03030603050105070201060f030f0f08030901051008030c0a140304030c0b042c060f0301240812031012052a12070e060f 70
    0xb0400b07044030a042d29810200008840b070a58440741401010b07503d0000b8000f085e040800e01d14064480c100c0404020542c25216601d0b031201c503481036821407008010102d007501c0140b04c4484002e209480c0840c2060030361a08509542005104000f1a0301d00803082044a54005051084030f81018210b9445051410040040002ca1001402424001083c403250944c15800507109104403000c0c00c00d46030301e03440b00310303103078800c1401025aa03406041c0720400320303083d8907141011100b00400c0742e143c00e90381c0d991102c01c1401c5074800f050302100420f0401c02c084606000711440e04020440c1d01740c0c40100d15002d401d81c0c201801c401e000e08080c40c01c21240c4d4609612614207609100180601e12030003070110f0841500038000c3d001c081c050320004100102007602034038041e801c1c440c480d070300c1c050928080001225080e00182c4440c031810301000d18211900d01541e004190100442a004070068107004244030050710515081d40681d00400c0f1920000f0340c62504010201ea4440c603496940001 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 253622122 1250 253620872 253620893
    0x3021219120f021611010c0206030a0f06030203060403030c0f0315090f090b0907050a090b03030910020316121b020d0318170a0201020f06130209190e010507140a0e0904 74
    0x482e440750b100145015401c0e81e224041c500b030901c520200c1c480300c416000110f40181b2101c6000350020003d102098000805402100301528454400268190760f500045c0c607201f402c8d5010b801080e074171899913585940c058401504081a41428407540900075000701480540d0300c03c001143c1d9440b50420234540c05070700410340c0b054010920a501c0c0c14611541c41d211030441c81303010300c0349186035800240c80240c2e001c2c803010400c00801841c100748405050080791a41641c1e0842180010030001d00494410340c003e081541c000c080c5501003070814031029000141c405800c2c2036206074152840c006a541d90b4015880750b44c189081c14502c0c4810a401c003112000380c001904c1c4440281441c0c4014000103401048076000f682102c121b09102d0384202d88440c800d8a07400d101410000e0064054103211210640099100d00c19114004078214410100c8100103041502651107009100105501404c2d0310880421007403d40c1c90009400c00250038070550030070311070041c07513030500160500c03020020 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 253623372 1250 253622122 253622141
    0x912071103010218010807020d090b07020f0d03050703020622060b0a05030d02010203040606060e0306010e220b041208090c0904060b060c03030106090815132d0302121912 75
    0x3d54403003e0304116580300810034601076001411200004130400e02c001810780010310320303803190340560741801c510203610781c000d130000e903001140103501c0580b54132005143d1594038001da9486441c3d25003071400900741030340038000200310703103401e032202046040c0080103821150f0300c40000140e84202c0c00c0801c640c012503500150340b5000d03152810b40030b83d406400845c80f56128060030801c00d511664203079001d010315658280c060b440100180b110354032400046070444031b50b04c08145080030b003000d0032803002d21003141147ca07420702d40184820407201508101718100d843c1402451850407010a9940d400003000040c8151030328000b107400d00c03c4680c0030f00b2070084064090b656900c07004240070b41e00d600a10400780012198200010300d203001182d0245019101d440440e00c2e61112407074103d2425110314181c5509012200401c0c5200d00341c8861110042528501842c10b0100d0030082e08050f1212a9814130300410131560f400c0d0400948207950b03c010a0130326281c6007034000f80410081c100c000 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 253624622 1250 253623372 253623379
    0x150509011e030e010f051b07170d060e060102120d0b0d0605010303050a11030405010813020f0d06060602011805071a1314130e0a02060f07050a0b0a1409120711 70
    0x1440c546994190814810315900d0f100070303c42030400110450894000325075142d0110f16011030400c180411100030251540100d001556900d030407480b8001c0d40d032100340341000c40382e96280304000400c0e440ea61a41c0c009400d0010b05000c24041404a54a03c10303081000e07031041e80c1e01e55107402544c620052000c05d68015008112035030b164a400740099000035004c030086076200c0d166045000c000811036081d0398060f540c49030541c8404680d40c404034000403040343d0140e01040703681d5490f20398100e40c00c54a401100301107041403078054081d084920750018003055440c04003204012840008a407012681104060184c1e20078001e040e03142d9000b500c11030180a5042c03480002c14404007106000015400c46403510007040000010044803600d14004000d500154070000141c07411001a0510b040240078080c41c0600030703540c071400c000350010700710740841c07d400a01c150100584510400b402e1a00901e0300d05003060152a5500c600d101001c00700f941c0009007480400c101107200403c10786014 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 253625872 1250 253624622 253624667
    0x9020904200d0b060f0406031a040f090308060103090206030c07060b09010603060e06090124020f03040f09050a050402010804080d02091c02130515060c0102130609080c01020715050901 81
    0x161140007041c0e0015500514090070301c800300c40c0a00c0c0103002c54644940102495140030303c0c0020940190050005540c01e9106c614281140341e00c1d40d010b0190341c41002d55000440c2c900a02d0050042c08014203158101460106082c00584034101200c1c1c10488104110341c58000b20b20301f0360301422000700031030f811148000000038000d81641001003580c15840c4000130f0360740c510051041c62070092040700310f40390f0f052040e031219800300d41d02081c1048140c0b050b01c00e8491081c20161450703120b41d21001206401d01000c0001d04014480d06030002030300c040a012508040d00000d14001b0041d0015081000c00610b00038000c00d958100c0d00e00c244040c00030b11105d00b1016074450988070b204030a9008010504a0300c102c01c5c1c040c40f40c84c3c81541214082c000c14284041484a03c2d041a20b41c101950b5080040c1c4204100805601006180c50394404100c41e09001542d82050030301c0d42224190740c02036006101c20021401e20349010700c6185040e58443c200c1000403a118510141e9000c1c414050317 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 253627122 1250 253625872 253625921
    0x110c010534080304060f021201030201210203010602030a0305011401050a120905011812020606031b13060905042303030106030e1504112b0f0510061d010506030f0109020904 76
    0x200e1000c3c62080e401203508001854070380141e5000e9108600302c80013001c0101c3d0060005600803000c0c2c0c2130450f1440a1420001c90f043d0040301241d00a80015002d0f03800810508051a0f041c0589400743c010206800301c0f0f07080590000e80280900501c00d003c1c42009445080c804a199010340721003030b0080002e000000d0120341a8180c01c0c03040009480c1036000200345002d15000280d024010000a0b000340401000c1c100600160803498884641c000e03610806003088030310340d0041c0005803501c03800010b03030b50406150401c80d5080c3d9100c000c40022041454040441000c015241194030038200492f0300c80c1800d0085090041c48085905181110340c10302c824000c2d202d00c013200c0c40c001918050054254840006e11448600d180b803030141c5070f43c840c00c10001b0115655400168481c41c01c4500800728075a40d07409580c2c1581100d0781406c0d521002c09800071001c559a8010324082e03178400d03c6d41c02d0042486480f40414003c2c0480795400241100107915154080e00d000301e040480000300420 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 253628372 1250 253627122 253627133
    0xd1b1119031511030f0a0b13051f0e150409060f0c08040606090e1b0604080f030a03110406020a020d0819030203060324040b09070b1207110c010534 65
    0x150341290840c0b2842c1814406060f5190030440340504020300150070260f64901000c0301030802815400d8004c08035017820b0014014901609000303181000d482c0042959100f10400002901da102d110080f13620340500000c00886901e014a0060540700480c0f0419030303007008005880c181405910b03903894204170b040101c1e40400e003680030320310490090003025941d01c02c100599045042e5000940c202c00030224004020744003080c80e076040075103140c0c102070f501c1031110704108800c10700180d95003000800c81d9400c2da0601c10302074201980c4c2c0b0200e050a040c240001d42e40c2c030005030002d00401e03141c0703501c805000b245429954080b2192052a0058a846800070040d4105071590383c0030f80b003400c60040300590307603a000c1c0c010a05040440c2d24159a641c4400340707640c00103801c00c5468090414045101e021170001004a084201e174061141d041a0314010a0340800c2c0700c030b0706560b4110b11030910032603034004110f44885035003294195564440320300e62840450752045144e4600a248204020420b = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 253629622 1250 253628372 253628393
    0xb01201504060f050603010b0f0d0c0509010f090b0603040f020d1703070c0515010503030f160803070e0f1005041a041203020f060109051009020f0d0c09080d1b111903 73
    0xd5110f00344444d07200d0000345826500070340401c562203400000141010b00f40f440c2100e0303105010f048203155482e134410101e009450280c1040b400d027260948107000c031040720f00a5000c5018155a12031443c6480c0d165803140428082000340f0a40107080b43e0010301003480c1c3c55039400c412449a0581e01e00304507002405400c03030460b04540f240901c40c41800c0c02030110113124100e43c40174001d94a0200c258074030a041f5441000310141900d009059a4049200b2601a40c41a1020f403039201842c580c031b07810040c0600da4101500d1250f1805900210029408400c0d54121610703081240c4014525a9441c0600c1c010780c1c0010002507076840c4030a050603400100c003d07800a07007105544450340c030b5810712000d41340304a81c02c40e502e807114801048080d038603030300401b0410504a40d550615030341c903d00c5000d035079009042800103220090b040c01b011005000041140f4002d051038010305254800700340c0d21308800304025011010400110605440e0500d4a914003541c1d82c6140104545900d030403400352 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 253630872 1250 253629622 253629641
    0x303240e070e0d0b0105011803080c01051b0913020a17090312070203041a072108090c06070f0609020a080a06020a1b020f0d051612020f040b0120150406 67
    0x301c0b910444401414152010000d180e042403040c0d00680c01c05005442284890000e00040c00c05003034000045042034025010000307944001041c0c0341400400380310300c041c4c4c5d00c0500103540c004100340960f643d03e10003690303d48040028003607160303000108151140c003801407603008480302c1c00081100c0300780040010000c4505505035001d45031903202040740d4a01450262442d000944240c0b0a0041d01c02005030284500c035210800b00c00c080b0803922088518550030420109090000b403000240092045c4d420a0340c040c0c403818203102c5142c41c0d05004132103480001d40540e50300d090701001c0d510354600600c081d00540c0c084903036136240b51801034000d41c08160300800090349100318220301c2d070f44000c9003840315800611140781309041c0006c000b200c044130320088650313100300340b070240703180c2000703401032004141c212542c1c4148509401849415004203401e94803c3d40303010440749403a80c1040c291079901e15200d0780600c02c00d000c2519503140c8042c80102d85280e400c1c5204000400c4003a400c0000302 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 253632122 1250 253630872 253630877
    0x30304141306051008042310061e030b0c160308090f0604081c0608010f020405010909051e0c040302031501140a05011202160204240b0708070303240e07 67
    0x4040c071044680c000c8911a0180c1c9502881c40001614081d204076038054100d4001d04506901c42d0705101070b210304203043d208118098002c1030305608610504e101303820082810072500c04142a245005001425590000501d284039840200d910340b5050000d03078008498140742d40c804400d0b0b0b42000741c00c84504407450155441032010942807c0c078007088081c01194040100d50502000d62580d00c285401c6c10f00140700306a46490005140303600f4000c0b56040c3d802e80c030005030344900b44400140140403039005605c0281c240824098641d0001500062680500c010040140c40382c40d61020b240c8a16800698148640d80b030030501d0a2200c0e62450403a85030014207640c8074400f4090000e0240c09100390342c0800c524104040c0c2c2d003603a42d00140401d82c3c00c0d04c562900c82e222940024204d40f85100c3c01481d03030340420641000701112142d9503002d8551544003508100d40d655801c0a94494048001c00300760300c0e200c2000134910f2440740c02e80b141111030303001003100ba100c0c0b043c0b000d070200441d501c170700 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 253633372 1250 253632122 253632139
    0x3070305070b0a11160524011e0b09040b01170c1206031c0807020a022701170c10030f0e0f010c050c03070b150307180c050a0503060409060b03030414 66
    0x1180050b10034404044c01100e0220f0604a8220020395124880e100c10307640c0e4050b240c0c041d040070f12140e40601002c0c503001c11345800380d41070281803108008507080c41c440d000e02250042c00b030050800141d840000d4100e50210328015038000480e40c0c1500c0e40750b02c01d00c03282c4440a00011540c08400382c0000c82210051921580d6002c0c00c140d515204226052442c000c5d03c40416801440356060300d90240082c0120345a4415941c003250015580c0c24074141542000d0610000c101460840c4500401d0315407141043c0304101c2035540d0303e41c421720142c10321608041001d094028040e4008428007840c0360410402d40d003032000000c0e01d401c858a0000807651130f100241c41140d02980070386840360100300c000c5040842c580c3d914008520060101c9801000d9900701442944e420880d80000e000c000184055821000c914001613070940b40104092282c20700c60181200e503c01c0542e03620035000c543c04503560b622400d10b20f008040d400fa2198150100060118285107107644207001d00d14156940513 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 253634622 1250 253633372 253633381
    0x20d08040e04022707350405060109150b0307030f1a090c040617040f140708060c0306060a081005120102090306010b04142806090312030e0c040903050c03070305070b 73
    0x880820203140130200c0040c50004110460310585804118207503003540e142c00b8211051003034031020750f000c0d660f01100490300204001c001080c441c2900600c02d1600610041a0004030003040a6180c0a00040444040005041a882500301c1000880c920b40300b0414a100c0d04182c101d80000c0c0d00160b4000c0c0e41000100d207445100004503000c80d5059a07907078042e040e50240802441030040e009882482d0b0310721340d800c0030440c8040da90186608503001020341501d410651400d19500800c811a40c1300140104500d58a5074411211320451a01d001c110965801801b121407003401c1e085160030004080350b6880b44941507008020420084045070300c0341c5ea8801980b5540d00c164041c180e14081d100012400e2800d01010313062050130021500002114541e280307003c2e80005901020028a0015040040c4550318442140c4190686400d202d10220355054541c0e03007281420302c1e40100c0d50b8900c5c1206052041041da046c0d113a205060701c0d9218101d00b8020120f402041043d907901c2076040202d03 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 253635872 1250 253634622 253634659
    0x92a0103051501091503060306140402090702030a0c0602031f08100b030703050a02122b0815212113050a030302060a11090909070305010f020a1704020d08040e0402 72
    0x16140b810141d42e8442c4041c00e0414207450709010f4841c540901d0385030040800040c88038020b922990705044005140c5140c103004003c11081d010349140155001002112000741e480516040b0f165082040940d503501c0780d208401a1404141c41c10450465011011070351034800310307461031fa04150307850501200c21608105500c41c400b51100030429030080c4840c10060a00c184891030b4002040b00341c0b40480380c50902a600460a0010040710b480041811200240c2284031180c00482d05c50b4041021070b1071002103907140d40c1d000e000d04000303187d081680403080d0b000c110154000a103100070141e00c06480c3d101c070f000c2d0742107594240000c0c2c20150011406041c880180c1d82101d8241e401000c0d143c40e2000010000c0c1804100080305501c100300c44c00c0c16480d0f007101c441c0902e0581004100d001d140d420000d0031180100c8413000d025004010301c51002d41c0c40211000440401c0c80b1540d29a25a480080c502352402c0b000141032070340c0402c000446d4080d4a803054403540c0269000410030b074030b14550 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 253637122 1250 253635872 253635901
    0x1a030c010e01080a2307021609020f0304020f0f060706020d1103040804030816062919053a03020601050307150c0f02090921120f092a010305 62
    0x180d000560050014080c2400d0750400d402d01120120785c20a0f10305203114401100004503144c9000d60712a034a0040c0d000801d40c50740340100030700f1008508181c1542c0f0211500d20014002900c0388601000002c403a66800306047d280c42c60041a00b80e0365009840c0800194002250385020a440d14200440c0b0820034003c4a114660004002d4540340c2550f42e81c5d1100d8020722000d80001c080c2040000c0012050b1190504011108c3c102c08440c26081941d80ca04d2a002c18089004e00c010140d104401c6c1d2034008040240c540c01c132104481000d201039990120868151000c226080e0b141d0320002102c82036413444a058041d5003a24120707a2106c0a056480840d4807414500000c010f2800c4880ca20901102e0b09a600c01d04080262950603000500342c95000d4460070700d42d4201200d503200349030f0007081581c5000c005401c40c41c148501400c0f08000c10b08014000704121a0302800150800c0342442000780f0718580101d04202c071085104d07080c40c0c8014005105000c00e00d410b010032403d81540310b0 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 253638372 1250 253637122 253637147
    0x1061d10030b132409260a03020a02120d090311010902100309050c03010c120c11060109110708030406050604050a0209210a080309250806010b090d05011a030c01 71
    0x4201207480d080910403d00d0f105030801c0c1e9954070b43e21070903083c01e03000c100106101c0500c9640401c1c01c0c0c1c040c1c1030084285007200c14502907503140d040440105282c4100713842121995060050322000221420380c20071001e99102440d21000107a4095002c1c4117620441016009958940b0f41c40041c1c05210f080715001320011f54007456100744c03840c03010301c2a0031900065103d8025181d5440d0340201003800e481c28105204041519400c040500701c3c100e200b4200c1c000b1151400465000e1509a1161989010701941003100d03240c1c6418621500703017074201c9804075401100c4590343e01c3d080c1004030041c041074507254411030501010902e000103030300a0f00d414040c01803902c2c0b20346e1755461104900711001d030034070f540c6405401c00550100381a800074521801c4080080e0251350200d69040d0b039115001c451250386080954402d20110f4800500107042d10515100c4540e11615030b0006031060b401ea200081c095070030500640b00c040d84181036825070401c164112028000c1040054900451a52 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 253639622 1250 253638372 253638383
    0x30703020601050a1d130203030a030507020f210903010204050307030602271c11041d07050909100b0102010f110a0e0321160203070b03010e100e0c090109050301061d1003 75
    0x101d441719010341500300b054010560301480c60074060746034042400d51f00410541800701e59a078042003d05c41c0c0502c00c9581009800000d4241c0d40e4100761125402d618500610f40d880c84045250182500c0075811038000d010001c049805c0c8036521315040000c0c0d4000003289140c01c038100c1401a030701150052500100b00002c003540440092708040716a06801c5c00000c1e150441c01c903284030241d40707941c451000c441707900420800840f0b0780b000c1c146150a802c0c1d0b01c8640a0a018800c0100101c000f02e601d8850301c08401010a0662450300101d0252482d074000004880c60b180209a00c1c40e00c0078010b040030045a103c900c41c4414010403d41c441002c007803001d44800c10b40c0d4141040d40d04140c01015002c124002d460301000141c0c010a242c80040d400030380c084000000140101c150007103584e1760010f00190007491480c1400300000345550040c1c0340d42204880031403d00410b82c011030b00d1030041c201c040c00800c1155502c00c1c114100c5168108030071982d92110001c1001ca2030300b8180c1806580d0441d = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 253640872 1250 253639622 253639649
    0x913120203211003140c1206061018030b01240e090a020a030e01020708071b06020703030c0311060a020414060c06060f0a0e09010b0103061211040f0f020c030703020601050a 76
    0xc800341d401c0842d005007030024031856600d000c0000b5440d0101d544400b03155000420440d8030b0307001030201070b080c8500c6100c8554052810001c0d030b0741c1c80c0a20084d004102e0300e00311b42801d4103400340002c003080c0b940009000401e600000b2400030040404105003800040c400c101040b00d601050b54441c0d261417411750031801c180001041000d1640041451607154600041c11000041c0c00500f2078001c0002120807110014056042c41032a90407441041c1c078074546100002d14200000c0c0d62940288001014003840a00748801d040c00307002c8501398540d0a00980b102840c1070318120300294043c2c0200c00d1115881d8146aa86082500c140c6035210f050703800405041c0c89030002c0141d42c2d084180300c1540030000c680041030038001c00403801e002d09180400881d42d10795000015090b41c1c1d0b07542000d0813803071160f40581c0100c2c4403204480f24142c001e80e00011000d98030b10840300900341e2650303010020f0380006452151804000300800c0c10f58026402e41c1c40c0c07a62180104001c6000610503240c1c0f20417032 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 253642122 1250 253640872 253640917
    0x2212080f070c03090b160f0807111c060b04110307020f0f0d0e120a0c0602010504021305040f0201030509010b120a05160506031501090510030b040f050c0a0e0d020913120203 76
    0x1440003800007010f02e51b44072010340c03000e60b11415105e00c500d904a070b801070b02148441c20030510704a00040c2941c100c3d144440c4038552051411841d604c0a80688560340724162650107440d164014804901c506100c9681d034945000041d5803a0070460301040300c2d03c01c241e04000606804124051940b0309170b07807903020010380035080040c200c544050121840c00744440310400544211074500081205030004181860a0b00400c465503204449020190707003040c082100003040341c0010320805509080006454840c02401c9004000781c41c40c01e5040b0703040c4034000018103800201384046034880e400700d42c414401d550545803480617500c50b668203c0004d0004c601c40303544003e1040f1000c1018540920080d642c4c0000a00f03c4c040c0c1500100403036034800050701c40c1c3c01c2601408040790301040c018401400d02410405141c070030800b0000400444000d600c0c0169211340c80c00c13101c944c0003001e4001509010b040c2509140440c0c4049894a40c031000742c40030f4600110a07240103102000c0c540341980003 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 253643372 1250 253642122 253642139
    0x506180d02060d15060e0102010c091e03050d121b090b0d0f0c0302030712050912220b090909060402030703020405071107180f0204030b2212080f070c0309 68
    0x40440407a0b01c5041440b00d00c403004124440c04041d80307000c160000320140740a201405c03000c1c0620320076045904000e40b9038412900408072a0481e002c040800c0c4407280c00c084258412407454200420b41d00404002d8455983d000c1000030034405020000c011011440171403000f0348049602d080301003894141304000903803e01d8050302545005800115880c1c4c0e40e5021441100d035450103090100c1c3d4048107120b020f40e4484903465100304154804c22840c2031850b515035507912148183d42c15010002480c8140075414900468031550080c000c240c65902d4115a03240da41000821600951078900000c3e0b015100007000c1c1d00954025014202180c1107400303110243c2030080014090210f07043c070f202e081034420016800248031191401107100c0d40030410300255006102c10307c01d1180140018000b04075940d0480d60000100c180b10a0584462a10707508800d100d084060300408080c641240c10903081400580718602302240c401442d40c941c1c2c41038550012000d000380001c3d04c0c45105120304d05 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 253644622 1250 253643372 253643389
    0xc0a03030302211e06010c0c03030816020d08061005040803040f030303150e0109050408071b030c09020903100c02070519050f0405090a1b211704030f0f02061606021201050618 77
    0x703c1c18504000303039803595124804a259654420ac00113580c190410001c285604c0b016800801c8500c0942091402c80c84001c05004000e04004d10940401031420912400b03482110001c03c4031100342c0351541c3d07903440c008030080020701c0250003182c2800194000d00480c05200b9055900080c5040010303401c00085400030300c002403007240e540d441007088501203040740c803070956404e07151981c4154150031881c18010821250340302001c600d00620209020ba50045940704900049903000103600490760b004a190811b242e00c4560402215000c0c1c03c1e280c042c440c0342a05030394040d00c4100244c00740d00e082c0002ca8038200c1354140d0a82000e900240010160640e2a00c40c54600c01c01d896080d85809207c00540c2d0508401c030b01e0515003242d01400c000703021140f0003245c004074140383d04082c59901c40d01c042140140c002840c001411250804666564040c2c800d0700c80d1078100c0003006ea00a19022000b0761006180d030043c00c0c00390700001194a06141140c140320344911302c21035080120b81c288008030 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 253645872 1250 253644622 253644631
    0x21e09090a0504170f0a021501120311150705190c170c0c090a02091c0206030601050a0201110d020c060907030201050d0216060c050405150406050f0c0c0a03030302211e 74
    0x9054070440164080007200c080e21700462070100306079031071a401c00041c0c94001e10540341b11348810300c400100000b070081440262004c0d010f0802e800c1024030540d52030708008031680714680ea030b9013102c140541c450340310700a0409617500041203400e00c240d610007a10280748400340107100d00414684038a4003aa8070018092084050701207506200102000a0100404403403901c81680d02141c0d003912481d201507210042c03050300208024006140e004070b0402e200060415050000025450301140d04c01d600c05442c50100c207440d1307621000d0a0b00b460001e1740c4142104c011912400c0c020644985001c5203c5048a40c1610381915106074811914080e4200e0072a81049561200802020503254003d04044858541d5040e55803402c0008206100d449000d5891b640d8400384030511413282c00908079081e00300c504091070344031001030340342da807a0045c00b0a6080c3c0003000c200c400005c154260b0060700001646140b800020350403400c101c4160f180803142405500c0c1b004031080c0e1190070a40701640c00 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 253647122 1250 253645872 253645883
    0x9030115090633030b060c010e0c0f060403080f0703050c06010b090901140d03030c140301090f050112030c020904140a0c06020706030e070506071112100605010c02010f0305071107060201021e09090a0504 89
    0x181011f040b00c103401c4070303c002c12030100e507007100b00c0801c05803802c000c0d82074000c80c08030b4190303003054115190710101d0702607210460207421000880c03105050003141030394907101540089883c19a1100009112a0400034503640501021400410103c84c001121104410007810140070b0f403001c0d0320114080e11842d505001030007454200c481c0c2e000000c0307004601a02164a0124000070440d07180d504881050b030044075811603004100e40040c0e4051140444e25404507040c0c9072a03155800e15507100300c141041d01c805403080580360700810481650881c112901c40e020758061641e103610030703400c2c2d907002440000960030100c414807241c50480090020303d40246002c407400c15404c0045604407034000038111503503000a80c91145118036014290141c28203281c10f214401d0b06500103441e004651034880d05154031040000c0301103204600504e81c031900241140d1405a0f0707400003a000354403140b11642e180c5604543c0c01241c0c12940704441001c20054902d14141e503841180400a0101070400c80b80d = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 253648372 1250 253647122 253647127
    0x120c1709030a02190815010f06050408121e0d0504060614010203040513061e080d03140a0915020a0c0219260106050604150813120509030115090633030b06 68
    0x8000008004521482c6c0b00681625940e5040c128000581c1c10146d00500821400700700038030070840042401c941401102041907121909a810441b1281c1101403104041d1408182507a1561650300301900441c0560410460140c031250605800000c000c1c075603000d0381c02000200a6414541c54940c0a42900c840000c2c1c0251200031051107107440d03000d104108030103d041400b113060148100030b010101130a0400c03d41c42d0b909500c04117103200906a894440d649d001d0001030040c0154000c0c40c595a0000c210768503004120040d0441e042c482040e4050740c40c040640c2d60101d5085015410b44900c2e0f075280a1401210022259240b81c040c1e020200b5500c4460026584c0c5a00d00604090061400303400786203c41c00800414500c40189902321000c088464003001c10000d5011060200c41807600e2580c915824011030b016115000120040c00404000003610f445540c0c80082528049112008032098034510b0000806401d00c8612441d020312a400c0b81c442d019600c441ea040402514035030 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 253649622 1250 253648372 253648379
    0x110a02040c0503060a090b0a05100e030d031b090b09040203061813030f030504030e010509060403020d0b0a0b2e091d010f0515071e120c1709030a0219 66
    0xc05891006000d5004100003106119091600c600c6103030107400500810410324440c9400105030f41c2292003164068480e0003100800b0502c600304601d92210080e0442d100301c0030801001780107004200495800d65690f20070a21010321070a0300000f1581d5680580e4104605038040000030b500190002e603228030003420030640c0600c410606d80c4907007060301c2900b2a00c446030401404100320b0803003440070586420104400250000041d160400080ca40b0319140d08650012500c240f1803500701a61051851945104200d540c0900c0c1c0c1c4078004040c000d0212150400c20b0000401c04201208800022001403070000911010711100c520484d26056403860b41c3d910304641c000c80420700101005121000602c030300100303c14084000c01d019a42501020440320108045024002c80104954041121040401003080310040141c0c0c00c5140c1d103103012840e81000d0042c403100d4108035458042296055001003d0f1426a4040f84000c0e000d441c076000d0707035420003001c101c043c1408a1042c120001c0031 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 253650872 1250 253649622 253649629
    0x803040e0a2f03091506030d030507031808130e01030804030b1506031e010501090602070605030916081609053601180b0c07050c0105031801020d0207060b0d0c06110a02 74
    0x110000b00c030040b41141d07241401d8042c6414090346901c68250281c0c2c070401c1c0409500c00090004505842c0d01c1d0004a64031000741c00c401a206217800c019900000c1e5800005202d0f00c04010000e00389500118907409507a820448138014003403101508100c020b200c10008503d482022603404070342d002c01d02140c000903000160031504166000000b000f06001100400c4100809040c090602403e11511403841c1c0440259201c00c1d40c014402000404800706013040300401c0f85041c00d00c01c2c0c00c0c561501c035440300d101503030318200b140800400300001d2070300041c07658483c844c07540030b00d010680d06100350301b02c00615a001c5200b0488070800c1004610284520385084c810402800c03c1c41c0060a03101001b42000729507040048c12204070318004001d0a000030308005400d400d20142030904039184d41d100b50143c0011240c1c811603010a500020301c00514020b240d0041c1680b40c0702d0482001703086000014451950030348680105049000141400a140501400e0411025603400c50b0300150540c0d021 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 253652122 1250 253650872 253650941
    0x106050a1b0b0103050c0f1315050303030403050a02060c0702030a11031006140a0b0f0706090804030602040b03061e09060402032a03061807170c0f0c070f0803040e0a 73
    0x2d60707182010900600030040c003030022104408007110340c145401c0440c40040d06800700010209004ca0b501c10010380f46000220b920740c01840000c065070780320f2500d8100a4429440172228a00500031080000d210711b101800341d807080c540107401003180b085a0769400700b04000740200151f05215240d14166005010301448026050004651600721810018040d810009801c1124032100611400c907403043c600007910b019503000640803658030554200f051552040c0d2f0000b90940340001004104241c1e5a030045000c0d40064507071210244000b0312040140407051030b426800003504d00802c074907145c1600690307008010031604100b00341c81015295842030140201c000030300008401c01499140070628402c0340e050582000500d4603240400130701c00210090400784040303801c000b05070307207a00340c01c191111040220b100594405400c0e0f055a030300c0341d0912a01500d520000c2000c14140c0b40807080d102140d5000c0b0284000c0d44580a40d0130103043c860041075528080d1151040051044450 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 253653372 1250 253652122 253652177
    0x405030609010b10090e13081210031a0402090a0f060f060806031009050706050a0e0405071d06190806030102070812040b06040b130b1801260705090106050a 69
    0x41c1c40c3c010b803402d001003401c0c0444403505001000ba410411100c083c0c0250340d00140700a01c00c0b042e02e81134039142c0c0c000e005540e0100b0007500010200080080b50441c1c58090342d000d95404030300c140521106080d406002c8030001c1d000781c0d0079030100e0302d0444c2d5900115155069102e006c11402d0f180c0c0c60260703104205512090001e0503e0781441110b050a01940b05a200440418404d48055495080e44e130328007407160760200400003607501d41c240d103c3c0c3c181c1150f1004c01081031245040000707000b41160310f002c60500d40b0680d00c80083d20700381703824011603a110900c0d00c24104440c003000c4043d00d450900822240d00744d50200046000594041c0c0140b15a008490b40380402e8201410210850708005000e42e008070318107082c460b07096842d1001420b0380c0b040040e003c07a4102100010030b5000c8811101e80c4000084040041103211f211740c5903100b0b1003034803580c400003911007010751a981e100510800d500900404010311917288104002c112081490030461840c900c4150345480b5800c0c540c2 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 253654622 1250 253653372 253653391
    0xa0e0d020d21030513080703110709020d0504031d130b1305070305100803070b06040f0216030306081203010f0e040813081f05090c0909010e03040e07030b011103090d0804050306 78
    0x7801c94030420341502ca402c1d0407411071742c4000741030012903840c002030703219015001e0140420305101c514030500c1080200c0c060203102c007040d91207150f103001c0300014090070b403821004a880c41540421801800d040b11103020801003e480f000c0d111140d01c030000f07010a803003058104011054264903c42d050003500e0080c91984d40007d041d240c41440c0c44042440e6400107001c6400403c20500400c0740061080c0c1c02c44012600040e00604110382c000013880f942c05407158070000c05440906058060388000112080c280585a40d031141016122052009005000e002405820144102c000c40241c10b031340148540b0101e443c106030050250945201a4403200d415880540d03006031a1032401e01e498519040e0050500c0f2909000c2040e58031240e0700e07040c59000c1c0d4010400140c600009410810020000d001542c0c1d0b541c0d110030300090101e02c1100c03000c1c04641030040c880c8043d441101079500184500e0065420503034228200110444130703403001d6640b004213100202c2e103660280901801030f032000c0d = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 253655872 1250 253654622 253654673
    0x1b03180109120f0303020d020705010c1101050106030b031209040e030c01061505070b0609100f030303091106040303050304170712020609210901031e0504080d0b04020a0e0d020d 78
    0x100018900039070754120a9114612802d0780c80001c0c201001c04141c5030b03040c2009600c640c02410a0002030240d25000f518039030030202c0e03400e5403540020814902c40f0042c0b000740010303a00c584003035098800b108001c1d44c01d030b030000240600c0b5030540005485d0341c10000b007002c102945110341e01e510310b4001003803452481e551820100204031a1074009141207006003003490600072603454041c1807020007060140506107040c00a07207a025541411000b038010500f61403a529240d0030300800401c1800011159041025001c1d0614070303000c4241c0b0202d1354155180d902e140e44964400a940d000d900000e0a00b034020304c070020000f00207207a800341b0700c400340e03004182d60b01d000c2c42864640003034403030f0002da410080d03055880d1a01ca180100e900c888030a00f40071804200c21204941009a0310072186001840d210034481000707500c2c0c0007450300121000e800d01c000c008480420040303100d00c06840b00401d0900da400324a6003005440302e1402400240306070340c1c240c2030741c81c4c00c40380c83c07060200540c004404 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 253657122 1250 253655872 253655917
    0xc02040902150406120c17041b0b04060e03031801050a0c0803070314161416050312060310020301080a0b090312040602211306110d060906030201030b100c081b03 71
    0x719071060204805407090007040e0350580042d04003203145180f0074842c110302c1e00003800e2098450248802c00d09096127200980d603034100d0484140c000f4098000065034184026845107400020303100c581551105134002d55150344010345c0d0310341c0700c00740070001e220119412030b02251841014500c03840264802042400e82510304803504100100010910f900240c503448805611404ca00b00302d407403442405035201c0f1890302049108070800340017003031031000040c81d10401400141c010b00600c0150100c1e8000c41116a414040e07000900891b0b269501c140701d0b000104809140c00c5420080003000d403031400040071202d00005408880540340150001a52400c0ca040003003402c242142c5008150028104200c005d600c5414030762002c0c10147e02c44010b004c6940c1044200c420700088c05070704014581e660010500549404d20059021918020401000c0d041c000ca00c00c801c0401982c4058141d011680c034410180c00a203495036042006d142c0c41c04652004000030701e0301000c07407049411110708 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 253658372 1250 253657122 253657127
    0x1503011508040c090e2811041a091819120221070227010e0114010903020f031903020d02070603060b070609050c03100209120309030607080405010b090414070501050f0403030c02040902150406 84
    0x100d4043c0f140114a42702107407050640444595146440c01c90304940d05c1c0c0c44210786813468080030f9100700024050084500d00c5040003c02035120305100d0b20340c202c070760040420140d03115000c084001c5e805d500300c03c08003412406d00100a0250b02e1009180318003110340c2c3c5020700341c0f40c4807214400b54402c16080050164240d4414460f0050200c000f080280b41ca01d000020030b0200240710003030240b400c1200c070711802d980c14000032070381840080041c2c0101059081c02075440a003002e992001d4014010080350051103400380c403050381d400080d801c3c500881c031707901c1c8402007080010540d01e0b4000e1501c40790b071585d000d2204c04440b845103c809a100c0724003008001c0c6440c40f902040e2443d030700402c40c10909440224406a10041604200c030075940c550512a0140100070607950b0320000c541d0400c030411465880c100c0ba0280004221902503480f500195007900c6541c0a00040c0c8030140000c200180c8541e540303900f81d602c06040801d283c1102c1e408101c0369030ba540842c91140202140a2100b0359 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 253659622 1250 253658372 253658393
    0x30708030103051b030c011403270d120c090308030615030c1e040305060c1602090a05180c150c01060801110721090509040609021503011508040c090e28 67
    0x80048024041020104001070080441482c0842c235060340800020440c501c0110030b81058190041302042e40d05c42807149a869121030440c40d07011a208001d810300c0301c410791203110495010781c1c80f0b0320440e60840e150000300c2e0700002d01e520f5020b041500700c03a40748103452000c0c40c09810640c0c1003d80380c0d0340c802070800d4040700100c400403500b207043c0420008900005080e50304160030303c440c0d6994001100700100c48a140c9440a50031102960911010f0300c5198030142c41031540c41e02c0385000036803030060030391101c101c2101203174491480420b1030b852429440c000c15141103c14000214251358070550790a44868074044130080b100403c004050040e02c00b8001c06a2000018004500d1b420f01009882841c4e9805014040c883c007100050401220b42c1c800c001c5e42e5001070030407000300d18680d5a500d0030303402401540a040300c0085e82031b032081e001d038080c280140d034000d414000c080e090031402c00c014018194400d046120380d401d100d081d20000d40d861000642160304a02c142d0031942041c1c42c101 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 253660872 1250 253659622 253659673
    0x20d0201020f030105090712020f0d0501050609010e040c091212140301060c110609210c03070303050702060306011803080d0c110a02122d0c090705041703070803010305 74
    0x1a40100701c032034000342d01e80045905480040341d015a140d214a030044230240b20a1035400d60b000e2000501000d50f10b0b01c4c2e4058000f070b000181c8203000a80e01d4500380078650080300360040c045001520700c060146016003103015031780004e00d010020381e03996051500000c4002001520521003901d035140b107055100074009005520051403e00d1540340c070500a209904030003001c0c01a5001d1403028030969964012644811001001c010030a6105414504000e00000240700c6c0c0b882100110049820041a0b0300216605078079414200590b603024011540c3c40200f03070a0410551300c1c0b20001140102c115003001d0f501611015407501e031441041c404492510f000ca005000d0b511256141041e00000e00d07402556060b242c840d40a240a103d26180c1034007100c4803200d40c683c202d10036202c110301c0040081d401140c603044508918808081c4040081e0541341480020b5007084140010f1048801009649038014112443e00c41c0e1030300c440c192070708281c00c110707000d401c5620f0020982448684c0094034 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 253662122 1250 253660872 253660877
    0x1a040c030b09011802040e01080303150a060c1e171b060609011203110303070507030e040603020d1707021e0306060108060a181116050709050c030c0f130e07020d 71
    0x1501100e00003440b1020500c21405019010b84c07481c84080e4154050f50010110b00c1e0444c042561600d80c1c040d202c0d0030886480107101c004c1c0b08002d00c240fa02d00c00d414103e608035124140c400e201070f2104107c50340029084c04626001c00c03040000600c000c000b01078403191001c016515036030082c05000c4040e4500c0c12906042e0320032024014251b80d400e42e540c2c1101d505e581010440d040034501074450740c40001d480c01460101000f0086060f40080042403024071030740e81c001c4ca00f00b2004c00c01040f1034503800065045103220b40c900001a11441007102c0442da4070100c2c1c1e003810400e0780001d02c0310074503841300784d02d1b1501c46040340041d08041140c2a00326a00b424510312901d00000071480b40310081c481c46142c00e40300d4440f02025151940850004811425800d035a415016030040060091107800c507468400e40400003002c0d8154801c86e070003894202e110a1554440b46542d4189400c40105c4400c4c0100801800007502c00c110582c80090580382c00940061400400281c00c0000000f00b5105 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 253663372 1250 253662122 253662131
    0x13020303190e21070b0c100603151116080a09030807030c0b06030f0a020420070602030906060904050c0d06020d0213050108011203020a141603050124050102150a020c011a040c03 78
    0x7200004503e42083c1d5041110583d11280070040c0d40b1f1a1400d00b4401c00b040700c1c54000c01000f40300c00d540c44140da400b4991420711821024509808007807041246e010103a13414143c500e4001052000140030402d510315281e250709480c0e44070315001d40d0002c2001c070301186951240404100e031814500f51b100d10100c01505c403000f99007848540f04c01c2e0800c0e009210b030307a6400d060103100315584070500100c41c000c100c0d580c40d18601d10703090009500a5030742c03c5662050070006842e900c0e00c0300c021482568000d01030550784501c80140207026807410012260380d40c007440300f440201e101d840604104108060008603641c6088000f4042d480d040e00072001a940c0c0000307400100760006400c1618590000e08520201c1c8202035680c01c1040c903013811020542d803640f00206001d4150062610078800c0c1c180d46041d098640c030403440300c1c5140d1203164096042840c030805203040d140c81d1306603c588204009441c11045034002c9003102d0f054070190007490b1545144505900b01403044080796419410100b2 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 253664622 1250 253663372 253663429
    0x81f05010501021015180515222715050105030606010516080409180302120901081503010b1018090204050913140a0c0501180e13020303190e 62
    0x4e445210300451084100e803100795003000380c03200b144000003c1c03210740c80140d500c54180b070403000505400c6d6244030b40509610303041c4603a803402c40e03203c420072031410b40710402c103401408104000c0c12000b040c2c2a14403d0350342081080715050740103451002e21400f500b00c19521041c107a2011140180c0159000740d12150400c01c00c1e981200c00ca0300d4110616488011007507007440c00c03040390312464100150316810059152078500c00c80f03050b6036802e84a6000d5031306400c81a02c0c1c10482b402040102c03400101d9a402103114150180401442c4440203000400d4010060000c2950003400e0014180007880c12691040c80c40c02c04140b40020300840d05003586014581400246040c078050300c100f01400a010449007085207820f0020703031094482040d52545201d0b0b0410190300780f50362083ca40030419840a1620f2407014101002c107544902810010507140e06101503050740400d10b0480e05480304000340259160004154200c14034aa600c17800500d0400007402510101e424610f103e0040f6014102c = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 253665872 1250 253664622 253664627
    0x6050901020f0714040902060c0a110a060305040b13050c090108030409060812070605131703070e0d020306011a210709150813020d060c02010b15120105190b04081f05010501 76
    0xa13000c078001144c0120307480200c1d00002c0c0d0588981c9035000307040d12a01d40300c2c4080240d41c4241d40c00021044a4260034103944a4050381178880c00c4400a0180e50f00400048280303071401446c003900d41c000c2c01101c011482000124401e0303102a0003620b501d80c00400c04020420f5680100b001400703a14001e07280b140d064004800c400d00030480c0c01000c180e1140d002900c9070600341161000c0b00d42180c1d00c00207041c0010741c850980c3d841175800034000f4685007a03a0b8401d0600c0f041e13102085e039025006201507071a203450711500800800000c41e90712020460300c82a841c40c0c032048210344014031503081003030804500240010825610600e0800c0d0354103141e024482d0003d0419a10421201d0222004046c910010f082035001c1d000090802e464501c4404206505501c21851080c0a8076088249501c0468200700d50103184903a0b03030040ca0b060b0041c009820a5002c40309800645041c0380b9585031208100309040c0c10030f410948080d408410a0000300400c5540b0410038090340c0020050b030750410000 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 253667122 1250 253665872 253665899
    0x13330e070e090c03160602010510050105071419030e0906030a08070602090105130602010c02070905060604030f14060421090605041e080d0201141e0105010807090f06050901020f07 79
    0x10301c03600500ca00d000481480381481028603104000b820f039086900a444048002c4500340503080c0190700e04400503100c5100107503c1c1c000d4907816165242000e5a690701c0c040c180c01001102d403c0c50050484c07082c1804c4204000040d0240b1986813010130903180d105000c01c001000b0f280c40e2296102c04000404690b42e6011503590075007041c00982c0d02c3c074402c00143c90314411914810401081e4020008105a040d44000d01e00318030341e801d070b54036540c5d030760200f0741030750f600f500d0725036001104000810018441d00781d100c1e00684204c000b0030701c0ca480018400d0402d40304a6013070b01c18000c1c9031140400c80908892404400b00342d410150b00290030044010907601440c01101d043c00c030078000e030f044100860b00383d40000b00745501c1200c08244004200a020f821400490488403000d60089440c00401c1d1440498052818554404030fa207000c0044176414000f500c000d040c0b10268502040303040d01c039032103000908115201c003540e82c48080b00080c41e2200e0241c40c030200c3e82141d0b1051010301044140c = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 253668372 1250 253667122 253667129
    0x161d041101050a170a0f420f0f0305100c0207060f0c06110405150708070204021c092603040302060103170d14100e15060313330e07 58
    0xc241da22145004019100c041030060031000d081e404c03008010491a01e074101e66643d44140d2820300000e4403400c00781443d0004000202e41500202e8042c80c070a808a242800c04102d809200701c42c090380e104032081c243c0003e81c001d40061034141e84140306100e0104030b13030041041c1c1841c00b0495410034102c020b40301c05140c0a040100451032103100d0b0014460040c1811968101d41c04005600001500384d41980c018400c0314000c40036590225540ca5510b0161502c02d80c005d4803240c42e10040d50308020080d88181026800b99001100c0860150362500c039080340c640c450380f4246035480c4880c42c49024104d0280c0890b54800040080100007903012076591b0441c1d07031041c0c69440c0c030003940d083c90b41180144a42c01c803000786081d9480ca40071000442c803a001e460f40e0200303002800c1d215200d01c0c00858003110082851051082c0d40915030400744004c6921180759150351105190591b59540b10b0f69050301c60140c980b502c0c1c05190221280004850401140c3e10820800d0300d01c2100e100c0d4542c0308522 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 253669622 1250 253668372 253668377
    0xa0801030f1a070201050703060b040509040b0711070f051518040f1b080114120303150a031e15020414010507020604030c290901050715090203161d041101 68
    0x210700410840308006000b4000001c0c4181c598620382404001d000708001c90384c40c40002e052640006007166243c0848041c1c0e003001c0c100d46040d41d0b80f912031002e00880541080d042213003050352422007050034401d9501a08040d01c0703492016107004d00b00807000d90340c0040700307040a00c00c1124407903100d40202e078941c0c041015a4081240803080d407005004200c5080314808140d0758455040946074404e00c540d044e00d40551100d041d1407640c4092020441508006030b101c1d900804c081604001c2c3c1388000c41c22404001c041c0e26415032281d0701c40556101c1a2040c80c000c1150308001070820842e0108041b6144904030214101864001640c01441500b8025414814009076503025522460100c0e80516000310845500a6480200000468046c44000030515003c1030002440c0304060464110040581d1000e040c9a1261155012261743e4069a1a21955140790388016107007441030400501c03070640f15101c80c41c984a002c4880c03460b0044d0880300808464100000190303060700c001e00d8903800b072 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 253670872 1250 253669622 253669643
    0x1202090f010c031202041805180601060c0c0305011103012606060402300124020d080a1b031e060b04031403040906140a05010314040206030901060f08010b040c02030a080103 76
    0x2800c0c1600c40e44103c940400c0505e00000d40460078502c070044074101203040580411550391160300300e62960800945034481500001c004008591041d501d4080090103909901c4440345d032030383c41900712011820019080c8a0200040248001c80c00303114038598002009001c424019045003520740d480180b07090b120b03984c003040d170091a00002c8240300111b1440408980892105a54040760907424402d50062001c80321143d000d0326021903003000c0c0940c842c0c0041941040d0300c42e0540d2a200c00400459100d075480020070b000d00b8116a0b00042c0c0206520001003600d0106150b032100e94050040980303c50a103a001c0190400c050100c401300ca41282c000d540710100c0440744c608611440d840400258206140856000a0160701004c100000c5980e031400f5543c030b000543c145c82d4842c0d041da40000800c00001c000d41009d000840d40032550100004203191181031a056031403681e080343c0000e170340d11400e0003801e090922800740c040740703a40019800d00d650344800030402c00050100411a040c0e0 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 253672122 1250 253670872 253670897
    0x60102060708071202070501020408010b220b010c060f06050102071502030d05100e0106080105091605072d0308090610080d0c0203010f06090f0c0f0f110a0503040b07031202090f01 79
    0x41440d0504c0700c00041d0155940c2101c1d01b003040c040d410134012030b14030354a00344100c0020710b40030445000c0211070481180610540f50459030051404441080c144a280701503100018028414502c44120250b80044e80301d040c00b000928010340c0303801c1000c40700c0c400b1f00316407600b0f070300001500d903a11000800420643d80b00e05260000605503440712400c680310200101e811500044068165030041d950f11526646143c243c80c03d05220300c0001002c298200010320100c1c1170294070320000a1404401038070026003c54411131018007403816400581140c1c1032040002040c8803103a00b241d44010f00d5078001c2e007080d16060326011441002010301045081034003c6441c2900541d440311100d00e0200308640d6269240ca0261030300240c041c1f030740d901d40365000440f240074020151000343c59139196141c1e4065400c0c141c51036803102150304090b22500b860440054020401400500703154013030243c56403440d103805000755190070b01c40300c80d4a0041c054020b20303031107129100d9011082480c0200340c0c541c0c0b = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 253673372 1250 253672122 253672127
    0x12240e060f0d0819080901050709030c0510091502010209030105130b0c0d1e0b2103040512030405060f1b07031104021c0935030103230d0f0306060806010206070807 72
    0x20155080b040404442d1301c0c1220982002c0710364810241007009010039580c00c0300c200c1d40c0c050f660200501071014404140038505043c07030348008014203410080d0320540c0f038512040c0c01208010b500f10040c2e40019080415040038000c0a03080903101c03944c1400100c0d282e44000c525540105405c410781e001040503079007030103d9004420304400e0b6040881c1ca184080403e84090b01102c11464012035500b070082000044490503c1d081030a200099818141004104808080050880c201d1031009100205480d540e640040c00c0035080340c3e82099a0782400a40424481ca881140c6403540c1c1240800b000455800001d0316210f542c2201c0050360b031142601109000d42d50105880b032014580b03807203031b000c01c006201550030881306029501080245941581c1c0c0c01005c01140e014588400e000410000e02c0300fa00c140e1030344401101601800484914040c502500351010000244001c80c0001c1c03040d03010302c56140542a186013078910351a1500001c0d5851101402d90020450b07200d000800251 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 253674622 1250 253673372 253673377
    0xf040b0d0602041415030f07030b03030c0106120303111c05040201111504060e0c2103190302040f0617040b0a1107050a12080402011205060112240e060f0d08 69
    0x540c080000c640f41c42d00e40c40250100b040d04104c59000e40300c01c00304030410a0000b002d60b4420000780c00c1083c0d2984d40e580c4114060001d010009805100601014091b14002e01800000e06418000842c0a130144e0900506803500c1d84200507500700e0401903a405070f020400155418508000c01180503191840100c0c3d217041141104844e50007010b0521030041701c016001401540284028400f100ea038250305900c0d04443c460484c0e02c10308110700500074050030a0135106480081b82900e041440c808011200c05000480e50000a0350020b401c7c0084c0404040c280098a01d524025514030000440d01440d2103002e00f01034200c4c001c07040003422424075500301d50718045115070401c3e260340700ba20b802542c601084030115107040342c181216200d2031047e040d0a01c280c5e016234540010301d801240c2c0070300400c005450103040103182d6031a100442c00e540603c1c0f00182241240002c01e429a000300044e0302c2c540c0e000b50038a90300c0030f01480b1307465980000c2522041c0045070700e920135002d246821103079072 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 253675872 1250 253674622 253674649
    0x2410031509141905090d11210703020d080103020604030209180706170105090f0f0709050a060c060c170c0c0304090f050405070f0f03030e03030c010e07080d0507020f040b 75
    0x250704001401c85074004011034075000d40c07aa40c0400e08036256000c0c154013034950445140d0b03030f1a1320428124074400e1066510311851006141a141c02c00e82081c007d1b5004031900c0c01805a0500008034a4105136041000d4030300c60004c1c0c1f40c04040355042d40c0c0041d103035203d00c3c80041e100700010703404905000c50180c0ca018140d41c1e4682200c0040340d445070054047c035100803501d9012044400002500d00f08000e003144a4120604504669940c400540895081c05028102001103404000c14952240e0810300040d14140d29041c0151000d460003105881581c1c80c0102001401d2150701103140b400c8000c1a048a000b44007107880741c03190401140345029660000c01400e00b8040082c01100d4035500403405580620140d640a5031a0801c0c04051441d0348582c24100005100030004244034401001021000400b0740f850068862912403d640c041782030305000c3c0c2c1040004020791141040030719242c1400d814000d040802a0300040e10f180c604c40310032800307980c44040043d0560703a80c031040600d0 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 253677122 1250 253675872 253675889
    0x17040b0711030918100f080d030c1b03020319050c0a080a030e01020708120c0c0a0602460908030d0f140108030a0311030f040303090309050d050624100315 68
    0x940340711343c1d813021180300c0a503158400501802d8002c42c0300300100c0b0b200310070366880000509808900130002c80c02440310381186020006c59001542c00001103030128076056001e68011501d514000c844108018001045003007481000c11110405480108102e01e5081c0c0210076591596550401907024003c040c2c2c1e80c0c041c552002401c04c0c200303c0c01038060100c00d0000080540682e5a81c90500c010b40301d010108140e6a0202c3c80c100c0003e46990000c1280244a04621a03603280c840c0d0b030264140120014a4041d0801045500da00211610303a524550f0081c0703450342440786080e0301261640724121402144135200d5000001d011407a0300040c03076848002d074400100d980d4418145890340c200c005440c0010342030200c500d00d8184220140d9005000344003101071591215641075004100c0d002c0114144401c40c5400155940d907041c1210015000c1e00180207240362950211100c1d07000403060390322070403004130300e12407030b49464202c0c2041120fa410005410081a0f038890f800340d0725a4000ca01 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 253678372 1250 253677122 253677139
    0x3030c031303061b080a0203060f0901060804060b09010b09150c030c030a020601051806040b0a080d02010603021f0c140102130b0a08060d2d080406020d17040b07110309 74
    0x9000e141099101168001e00d07040004d8070307601450351a42c0c0e2905816200050302a0003191b0441c00c154025a0005c40090025104400d2080440c403644000d078040004181c9400421040c030840d4081c45248a408070740c3c82c9102e604103544007245000e07440e07407a4080c483c040361030382c0e02c09103140803500704607440b504a82e102c0003514042c959030361102814a00600a900001405040c00c00c5100f40501001766140303215039445092000500c0c9103450b1551190448a001a210109100d40d098800180e030000c21003600b503005010542c0d040c07140c81081c3c04074640080e2005a07020103424050356010312001140235141c000e8a0280c00340142c0400f020603e01070008050403200c0090406900c103840c2c0c440d40d503a0740410042402c82c2403102400d460a8a0b0b40e01c803860b12000d6004030b0030140ea05a01d140112251034840c040c7d081504a000584c5c0800000c40c412600554203940d45105420813440614196451076a108000340410050000418003141108414410344161000c041c0c01410b = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 253679622 1250 253678372 253678387
    0x80d0302310611010e120705031c0509010c0c050606120f030307050711060c100c05160809030106170304090903140c1f29010c0b1306050f130209040203030c03 70
    0x103074006035105081c080380000c040d0020161060142001c3d482d01a005003000d0040400f00880980c802541180ca138001004056403840b1040c2601d118510f000d1400501c83c9040c6000ca421560042d401006018001039030100090002401c1070b030124058500300c03107286001100c1c0b0f1500ba0b01099200d50741c0030210400c0101c6510002515860307008400b000c40d00300d210401e01090b0b01c5042800741040e081000400342c0c00d507903500b02c00b4102c2140d140143c44c0c4024102000281080c40b5400c071140000001c00c25800c1c40c003400b98401900090402c24042801858003503940d210740e11500c0f5151340c58488405c1414081c5118504440c91040f20a03900c10040340d405847d58849100c0c40610904040319600c10718661185104600b400700894500101211240c181600300c1c08041781004810000c0a0015050b178680f140904240f402180da003548910b40135040d80c1c0e000b04444010380065040048412030280d0428400f41c0544032841035440718004a41076100344128a00b261100080c480b = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 253680872 1250 253679622 253679707
    0x5040e102a08090601050901060c1709030a0303061e0b2203150b0414061e0d080a020303041106070c1215021803300c0c030a0c03021306080d0302 64
    0xb038400c0c003c1d10141c95845c0e0703da00400c01281428001c0710005a40016030100040704040b4074410010140f90260802c071410300003914011515404a0000c0e07242e980c00c0007100028100c407000c114100941041c22401d00d02c030b14100c1c0c0109480c41c0015003e004009152407800704a420146400194282c3c20540c074441c024064009040194000d62500140801c2c40207100710060207114003c001a018041c4600b1250030721228250141c0e2121141c00c0c000c0c0041c201e48020500c0c503c01d0b8000e136803240b40c1030410249685148030600e0113001d0030804400050407803a00d4005a03410318480080380129130911392040c04080500c01c229500c00110200703200c2d5000713608909803404074100d455035401d2812202c0400050103106282e95405c0b01000200c0c80824080c002032402034048424180100300000e2520b00c80c40003e4030040317000c401c18401d42c10710010311b150020f9944014448507103490b24859a47c00c110060608240d0f020500701e180c13501105106203a141d140c400c0004211013080034 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 253682122 1250 253680872 253680887
    0xd0c0816061b23090a0b070b011d0709170c0d060234020906030f030403080a080603031305061b06010f0806131205030402040222030c05040e102a 64
    0x1c0d05020032260840a41d5407050150f4101d0100480204a5000e40101c421005130807205103150b005283c00e402188000242014009180c081c902256040d4900341603416a0802c1e20745000d0741d01c42080420010035007080030203003110040303100c040b01450380c65030090400308001c5010703038031445054000d0107008403034020344a4007c0b031230600c0400e007400a01c0040004e6003180ba040c00c0d084000f03103d00244c03900070841c0d6400709010b81035440500c400507455085a00035081103442d424045000902682e00c40d0040340c0c05441a4001d40c40c0600e00c00c030040001809101e42c501c143c0300010000e1207070502c1c000446202101d00215445541c4500e51038071000540d0064511078820600001e05585415914603552501308010700408a03016508a50680c001070090340c125408002c80100c01031401f600509544000c084500e0b628254034161900340d1711b030340c0a14411418000044012600071850310303181090900f00049078607905c2a0108207020030f0b105a406848007808000303056400549 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 253683372 1250 253682122 253682141
    0x280903020c0906010302090f0d02061c09030311032401090f270612200d0501091713060302090f06030412080a02030c030703150e01080c090115020d0c081606 69
    0x202c00e8000da5070440110704a005030600940e2254040b49441081d050081e9400091400a0000307480e02c50703950700600d0107541c803440104165640360201418190325200e2040c0ba9000030b203400d0f180d42010707410b807502d101030780401d030200074840b06240303025038043c203113050042c41a1010446840d6942c03c08088002e0115554900520200c0b140f20310b00350749109200595540031003245500c0e4140c3c1b25480701d4090861844541d0700c0c501200d034902c0e0717a5504d1581202c0e00c01e0001145c0f40c040c5141043d4004200d46000c0765610003402030002d114001e11010003580c409207401a100c80da04000500000354000195403c802d000003800244620210000580d0f070342d544038850301c0e49601c5010003c07484120340c0280716500074404920030380d00c2600720500f030350079000b611007616072a55442c001043c1e0130b81c0102c1c80d41c1d1000911103001c0c18002c98090041c28034070304407600c2c06000c030000303034803072007503088010070002044030110400c1102029a0a0780f0300d1212074515440403841c122000b00380110 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 253684622 1250 253683372 253683379
    0xb240a120c051203040b0a03060e040f210203091c02151207090303022a040606020105010501030c09050f06030603120f09010306090b0d060209060f030f04030e0117280903020c 77
    0x1c1000c501c03030038200300e0303034054403a074000071803400b450b00149002580001c1c000404254540c227000648010100b280390013140a841c2c0e0b20380020541c505601300c0c01d0f01c40c04002111a41084030307449240c004c415964200000d0310031403a0400391200c89802076242c1c140080d440400d24401b682e0442026000d000900b030b082c55210350740d441d1001c00f42c8201400d44070060040c0d101e100e85001c0710540345110000303206802070304099011094006402ea0f640c9401050060707664000410080d0f901d801a09942c541500b03002c2103903420078001ca103982e0340315480d0b980190000004182d40c1d4404012030320114800342e040e140c0791505501000300c580c3c45140c3c0680000e00346540401c4c1400140700780c1c0c0302c01e80c0c014400f43d041c0c0415a9054040d410102d180307a80b0040901900400380c8040c2d000314460025890b043c1a18601450003829450064000504005c00c0000d0f180a08001c81317510358210380500041304000c082e124034064442e121044041c0844d09100f000d000301a0001880385c8680d0045 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 253685872 1250 253684622 253684643
    0x1707090816141819090f120e060c0a0b09121819080d0309140a0602030a0e0102041508060307051005030403020106061d04090821041109040b240a12 65
    0x10020000720f10321411025070300c10310520104da83c031070b42c101005480c0a020b01001c68803000300d0b02d600c0102d400c201030550b41151041005030700981c0c000f80400d13203200116442400c01c800c0d110b070b02d0758030030b0000b50040540f8503c0e80030490410f002c02c071a42c500884034a0b1a940c0300103100316590b420000018050244409100000d40341414007030181c151040400204204941c8200444c0500001481030301d421251043e04845c00e43c0601102c04014014000540d076402c00c402104125110f051f074070b03219a4070501c010b100000b42851782403924011450b00c039180f616440c0010342403042d1a80026403000312014044045a040000381d485180660000c0006643d41c40d000d641901007040302444032200d428000e034080c0b409074883c400d0540103031151810410022020000d2400c030107941d40d66007256500704010041084402d80381c0c1321003500c0f801c00c1d07800d00d6a600220170310090103d0044400c40c0b055a100003107200261025a200100004510ba56540c2c100e0003540f00c0500a5a45e032924 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 253687122 1250 253685872 253685909
    0x41e05130c050303073203040807050901140d02060f0c01022b152616032a09050c07022110060e010902031e010801020a030605010806011707090816 65
    0x4415500482c4c6c00420003207200c3c2d2070700c4042c1d4440d00020300910900826560500d00048200043c201511102c80242a0309003004200921610140d1150800d4504041c501c0d0060300d811010400b01c0d68103844181d2260081c91400c505801400c111107100e61002c12250310a01108001c03c07640c40400507600c0c4280c1800100f41c041d110318006402400c6000d10301001078450700c444101c21070038a000b00400c58030407100180d0500400c03039002055205924014000d00900c6c00000c14910600001c07409248034019000c000941248503012507190341d81300040b1507044400407182003d60043c00c03425002c00080c0e0000031181c03007001109092050081e440e80c400c2c000d104090650f48a482480c0b196840c001550b4069070000300004910700180c103014844c1054030200c280600010340c000358071038000400080c11212242e2009040140c00700c2030101d113907042404660301008041e401c01503999039103000d40e20694250710100e503902c115200456a280c5d220850020f07609000c0d24507003103491 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 253688372 1250 253687122 253687129
    0xb070909291206010509060409021915170f101d180c030a020906120a0311060f0105011e1e090509010e0402030316061509020d15060e041e05130c05 65
    0x2c2141c2c0180d82d0b100a005228600d0072403001540302d2002000441c0748552a8013082084003140c0240ca0304c40240401405103031300c441d6814100c07401510b008850740c144c90000000380a005890040340c1c21000f0081307804550b45507180c00240600305809032403640d403040302202d480000c550004ca0044c12210b5022400c001240702600c1400080042c4070b6403005400304103032542c000d0246a84082120b0740740c00d40c14070070301841c481c190103502c1c2c00d0300c0b4882c000500307820304900404000404504000501550303030440422501281c0d180c1512503c202442406d95003040d00344440720032903211700c4c0c460408a900201c2d00d41a51000c0c1c41210050341c4c0d6017040a8140c0c0306860082d4160020b1141083c0c4104011290322154001c140201c0e0202c0b003119a401c050300180c10045030700d030b000141a400d15042e800790002d502444100c1c01c01b00381c500000108021038100e010703849076440e00d050245600743c0101034061202401020401820700c1010a0b070f500c5510130080758000c1982c0c2c1d00282928 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 253689622 1250 253688372 253688389
    0x20d0f03050a11160603050c091206010303121b120e030d0c0216080c01180e131b0311010c0516090c020601091505060c0307060e0f0120070b07090929 66
    0x40400c2908000d9a007005c1c0240c0107000014141030320700308107000c000410350301c00000c405ca040102016240e43d50540c00c00070000c503515440140c0d680d050041603c1e0483d407920640074511900d00e010320358800075600c20006405410849031803440302050913101200700b0f0380100382141854003110071208045150441002030b41c86030818603044518030000305d5019000c000001000340c1003104aa6484100032008028152a101204200005160104040400032540c04110300d10f0241c66a880c555546810400b01000c081c1004817500c1240104001040820a10701e80250854200b980b00c0660500514200345594014814000001081041841254000e015501c104071449052500788042c55004401c06007041c401004000089526441410766510210b4050865203030345c1700c1501d0035500724410010b07141552068400300003941004851407140c1c0041c40c05543e55814106449110484e03101d4407406003450310ba20180311030300316030a070502c100211404100701d814040c0f04200 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 253690872 1250 253689622 253689643
    0xb01091706011e090c050315030114010b0d14040b060301110f0307030c0509031501090509011a0d0203070312030f1b0507151808040f060822020d0f03050a11 69
    0x5030049001071201900c101c040d0400310302c461507001c0302290381302c01d0541103400c8660038800150011082c0003020000e100b40c7ca401c4039048000b800300044407005401401d0f4180305030750b001140058880c070f50810a40054080048600d03840402d031520341000f084c42c1c24121500f1344694a0500c0c8800c0054041c4140c1c0c210300301c14500c850443d03898803416802881c928880ba070912600340020381c42c0c0c1d5800c111000c0000b090740c44101c482d500d4084010256500504107581a9040062105540c485440d0126020408442000710580b141c00400c0c104421904094154440d400c0c1e012403c90b0550003000e02e049030501c04001c078103185400e9801c909610a60000018010801600424035601441e008030300c00715000141c0d04c0e40003845422516841074100d0b8103050100e010040045480705e20001000541001d102d01d24101928001c0e484102aa40c644000000c14041c299103410070f10340001c0c0d40c0920305985150f180d050140179034000c00c00d0140060505250711081135404240b2b138040 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 253692122 1250 253690872 253690919
    0x271803030f0509032821020705100c0e0913080a11160b0a050d0f020307020d08060a0e0f040c090f0228120b010507060609020a020d030209032802030d030b0109 70
    0x1d90a02c0c1102903200707420502c19080201b5804a46a001001203c0d04850007160500603501c60b0360f4580141014841007000c0816441d04000301a441e400c182040d00384102242c00800a550b1050341c10b600782880580502810300100d0300c91000c9400c50201a80003240c1000c036000d44500b100700c2c00c0c0c0c00003540624000c88405000202d5080c1c015406403498058042021031204a480880001c0b60401c032907100040c2d1110300d1081c030440d045086160002001d407150b4031118280642e00d0884d5802401126040054100060611444060756005020041d0040c400000303105c400038007a41090b501c400340505044644000c0c030b82503040220503c03400e52103550711481c452000724001d0009102e054103100c001c0041000181c558810394028056400b4010380324880e080c2c00130f00d001c44412203942071601c1045210320541d8006002441500d00c2520364003020300780c01003d43c1c140d2556500a41501c40c030582e2201841d0150040340120000b0ba1b1400149686c0310701b285000d440b60042480c0 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 253693372 1250 253692122 253692157
    0x1903020303071e050604030207092f0c1203130c050d03020c010f0c080f07050c090403090e04080d05190c1d1509060c070503010f06271803030f050903 66
    0x3a100d012143d0084014120008145005448040c24404c0450f0220b006800c25079040c001c4001c948648080b1001e003032000440e0f210600d0b000404850968203402c0418008602c00c2c0c4181d07010070501d4001c01901d04600d449040402c500000c103403480b4402c54000390000800b15290400c201c80001c2c198046e4000c040704d541e4130b40103480003003400041c4420445060440000b04040c5c0300107005006070301160036982d10399418128207115a1100003441280c03848103000120742c6c04814802542c6214403149401c3c1c0f40d519180c4440d204046400301c0603414502000822854041100065007500c0c806004500c04070f8802c42e80b03c0c9414112441848141d41c009034141055601240c07000318040c140c618081000d00024604d411028040456902004040c40682000c1c00f0f41420b078a80c01805004507800c1c50500c0c0b59a114842c400c1001c18260f4004141c0400903400c80c0351105040481c042110f40c150400402500303403104413408460518020403041c140003c12a501c607541c0c0340c1444c8 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 253694622 1250 253693372 253693387
    0x207060c050d120b04060608060a0602010e0a0b0a020d11130506090a0b1b0f0f011b050d050601030b13060e0609040507050111010b100f170108030301170a06090803061903020303 78
    0x2240c607106243c240c1a1542c2e50300b200e03441d60720740c1e228450160081c1d4440071903506c1c003503041050303004880e003150045904098000d1004080082c44411042c1d0202c0782440c40e83d105217032440240210b0003441100307820078151b0300f041451703000100000c02034049582c0340c02d512901402110301c11000310380d4001d02452020400001303e80003800d07010014141c49020803850648151503c0703003551141c4400e4118031054101502d0074030510041c01c4900c502500b0303480b03d000012f040b03805419903400d461a16040003030850b80c42035001d01c00904000f0802081014005644801000c0d5400b07142d85444040c0b01045ca5071602c4001c0d188281c0d408030040070417600b0880110b42030b151090825015640340d00c002d1145136650b0b9050403a0b94031942d5051280c034452000200710080c105e900301308508240005104175440070089906590200d80002d00440c1d8143c000713840d10302c142001070324407881c04c002ca808103c2c0110055002d060200c85502c1042041c2440d83d400b08001c1c4002981584208901d2 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 253695872 1250 253694622 253694627
    0x5071a0606220306090305091008010b030a02091804030f0f030b030a110a0b07050115060f090e06030a0804030b15190323010504050a05060a0603020904320309010207060c050d 77
    0x1804028410b0210b400001d42ea581d03a1004d403030140000302d0108402250340c0c0300e5030601c141d132040c0d0500c1518120201e035241c42b20006042c8405400c0c8901d240d00080d0069050321210440358000414501204441c41c103418014100b028420100e0700040082c0d19200d403661003809404015074009020703000c02c1070661f0319a101110303a00030150708548101701c0000d0201240c406041c10130b01580002c100182182d8603800d40070041c3c1c0000d002e001c5003860030030307030325074403294070020340c0c2010369007100f1502c1d4903000901e040c0c000c4200a0045034006070100401c00c403501a00c1c01003400f01c03800003002e002e50081054a120141c2c0c1c5403040401d01e8000c1002c200e442c100c01c405900b0052000110520050321107081d41c0c0200c0f0140c607150301407034140c03041203002c1101039402030240300b081000318291307070000708016070140001c0d02c0300f0500c14024000d26040396540d1000104070040e07a0185c1c52400d0015100c4d0061580b00d400b5004241d00040c01d1802409a0b02d20607a105000e4029180409004d = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 253697122 1250 253695872 253695907
    0x2090a051008030307030605010e01080c160213020a0302090301051b0f09010c080d0b0a05060906120c0c010501170d02030f0a110c0901060c060b03070509010e13020a0605071a0606 79
    0x2824484081e1034005030240080c4021401604140d8001c1104c50604c0700240440c0341c03458050f4100400c1000f0002811411000c5e41d800e003580c0b68440321080c0003800011580c0000c0724603041424400103078582c070036405d9070050003441e81c10340c000c0c895940c42301c2e4201005041c3d4031309070400c0c0c1c5042290180c03080072000202000350301418108000251a19244100d03042031201e041d185a5601b50010940340101c1204010300044441c54a840b0200700810b0450040c090a07400a81d00130000c0b91040d5881360030b85044000120003001590780d42c10440082844010481029001da90403a1013084d03c0401214201441e1015a9140010145084900b01e607001f031600074601615020702c105540310418a4000c18182c0d48900b10103459050038811100400c000c90f100341d2220320108141e448a001030ba04640d20307502400340076640c400c030041c800c400000d030007136002440742030106105811002074079403e4060a4034500c01e00b0030b107a520400c4401030391500c0d070128090112448880b1910702 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 253698372 1250 253697122 253697131
    0x312070305030c07330f06080c01050d0b13090309061d270a05160c0215160b040c031a040f120203070b090303071704030f230309010509100902090a05 66
    0x11400708550015503000701d00c0070410b540d170300e0a4034203001c1605d50b1009801140a070448600b000c100c005e1a0820131a07480242a0700702e418410082401348888400340d000702100c0c1300c0500002c12940081c1034020051121070350440218102c008089142c5d4810002e40803084014950041c004402004111141c50341c0c1d0307850f40302c80401d9291042d182400c0f600c01c03030142000035004a07450610b0322a46081c891800004000c00022108080140c0d0b01c0090503c80d022000251544e200e81c0c0e000402090882400080c040301090f4044c4004c0000400004080380e000700b62000c840720100c040407606c4123060b140a03158070b09a0350184082480c501e028008448680102ca180195564031008020000c48840b40c2980002c010170002c0798102c440243d200012030f920070321624250760041c1250340e2203e80c25040004003411100040e0ba0382200c41003145c0c1e403480d04c0c2c3c0c0380d150469009020b0101190400c80381d009951402082e03c415000e81c0340640d50040108500f1742c0d440b80030030001d200052 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 253699622 1250 253698372 253698383
    0x31e030e04092a06030b0607021e032109040510081e0313060806030609060403050423090108100f110a1103040f0803030907150806011b02090a09020312070305030c07 73
    0x155012041000c0c603421204000080f90300c8090107281c01c50190032540e1201c50035010f40001c00003100141d030ba01c103105144440003a841880d615031600441d1a00d0504c0010000320f00002c1045840c0d51022000f5182a2004480600881c0e03149012001c1c0d05696108141d0294801301c0006014010000307001d110310301c040200c0342009440d000c039051804150303002001041d0030a09001c5181000d000303160307200150b02c0040405003443c1e03800401c58071442c417800001112015041c5038030020b040d146081407100801c17034142c6585840b9002d13203418200c0c1400080c42e01c1c2803003c1204000074081c0300c1482860721030031070901c0d00c41a000d480804860a80740c42a000401000c21000c0c0001401c00141410700021501e0386440204d1034900b842c103030081c2000010703810241d4403ca92003504a54010420728200c00e4072600d801c1da010442d00c0395400258040110003c000c5038034199071000d030b80d40703000714111080300b0345490343c006480c800e5000180c002403007000003c41491844004060302c600c00d5 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 253700872 1250 253699622 253699643
    0x906060509120a080301090218030a0f020d0c08150108060907030c061412040606050306071e0c03022e1a0a030204021b060c1c0b0130020c07031e030e0409 68
    0x6950302e103405d91017608101801035010480e422241c038201503982d010181900100149485929061903801d0814402845920091400c100300a508600c0d1030003402c086048400e2800c80214ad042c84001c00d02a01d82c030b034400e080006155600008a14048030303000600c5074551400c202040311048071084041c00003c00c1000740d400c0302c8200603169403003036015010000e0306a0500041605280025014101300020348800030044030742189800e40c8030b0b41a040010001034207141c10390405000c01580e00c522840c0044075204901c02130711058441e031f84800304000d0019095881460b0106a07243d294010316002c500b8801420030754000c05420003d0a9420119280c441c44076103015000c81d10f02d0f50050011802e940c51031303541d245022600c05c0084003030000710780d0324000811480d440d14000910f0300010110a0b80403054500290841c1c864980941d5140c0c506d0140c17035591441407000b103520440442c000511100c40001001045905030785000c1d070f03040408100005048001070580701503c40 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 253702122 1250 253700872 253700893
    0x131b300e07080a200a0b0306210a050d0809010e030412020a0e010b0702041a031c050c01060b031b03070206010b130b1c0605091501121d06040b01090606050912 70
    0xc001030089544160a091440c04501311400488052000300c1801a1002c0c00144030001c2581c055a500c610191403145a254a0900c40c3c11001c180180440c0c2901a8124000a0040219001c00c001180da103454003152250b003c15030898544140021054000748014000400c4580503c410a800200380e201d1980e119104052522400e0344905d014010010b00c84046003080c0c068440c85061009103202125180804240c0704c1c40c0810307130400c003d81e054404080c0700740207005032400b00d0404002045496164009174403154029154000d1098034201d410240c4420030301200d00c200f640d9800f5280ca640307009688400c43c0c001a540c11002d50710500c0118104000c0009401d0310702d01c0340140f400312184400144205c1e4440e0b0007283c0a640d00c07804000d62544007070589846640203281207400402c070f15402c00c0007000c0c902d1a8807a1001c18001a21860703200103003003070003a40900c075220266603031440c1c880100c91080c8141310202d00e00b409191750030724003001c2581e00f205012040d10040e000 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 253703372 1250 253702122 253702139
    0x503010606050a110a030e011b05010f0603050f010612030c05030705010f060302040b03010606050306220c0c0b15030604060906020d0603080a02121611131b300e07 72
    0x80d540c00c9200040d001044140407680c2c0a28000d0f140c282600142200805a03180186482c0c1c2010503541840103060481250040d820004081c00790000000c11046038080d0381d5201421080c072066a0034072601914101414040c8a07100c2140d109002c5a50003030926501038640980c0d14030251000c0c0024410740300491401c3c080d0340c4070543c0c181c4000890500f107104001c21039201c1c0c12030602980c502001840001d030001c0807030350030990845140f000c03541c3c40c1d540c41c8901c82100c0001035a8600700f1044000c00d07178010625840352441016014071917a10788090b138134003034501902d40341e0541c41140414003007841075010230308648c0124070243c5032031640d200460a0703444650088504100001c2e011060035814400c0c0b91018100f01c580030700e0815801500c400c03181c10210054194165411119180e9503040c1403982e4035112441e00340104400c46c1030005010010300f00100c0862441130030480907040c40803825403242000080ca40e0b072140800d080500620a4400040043c850b00d400800c8105 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 253704622 1250 253703372 253703381
    0x8090c01140c010f150e041502090f061908061e0f060403060903020a060e0c031b0a0e072601150c030e191d0c040b0a0207091a030d02030310120804050301 68
    0x40307013500104280301c403115604880e082c154045840c1445240c1800001104104a0003020801da00050380700d021940004400b103078003114075540400d0001e12074070701080d944075212640c3d0048e2076110030b03551510705120190001c0000700e40d00000c00f03001c01c6074502e003994019051480180c1041e050940301d58400c1d007201d00031003003640964002000300c0108a103e0152200c0a009000a498105a0070010036900e4415215024420f04041c03040865038540d210b00900514503181d480b415800c0007040904103c0705100e03c10704000303817030070012500c1d00351500742e90407103818188000300b191055a040340c0d840b03801d5030304a08004070039900c0c400961b01c9071104000703000c4529480f2803243c41c02c41140024580c4002c000d203c041003c0030016044500f80aa5084800c0224400e56850050710128104122030701b0400d0308525140d4106101619050030721092001a01260101e20740c00100b07990b41d001c100c401280d1074a000f60240714028859409a620a01c5402d605081c51f0710b03400000d0944 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 253705872 1250 253704622 253704641
    0x602040e040b16020703081e220506030606070209090c0a1e0806090c0904170d020c0f010b090a0c140c0c101110020a0216170c0108090c01140c01 64
    0x4114030350511090242d040031864004080c0e084016182c0f407101e001a490751554480a04021000300c0c01114040c0c0e500c9212001c5000001142d0f629040c0c0305103800e500c40303401007007030700341007150004519402c11604a03800303a11b0041c0810308000d066401c000c45858024020384203030144aa00013060745541040c0070240c840380ea0350540c5000d180320055050306240c0c2c400c03a001da00840902503185000316240000701810b884401c51035072a42008a0703d100c2c40660914241d000040f029041400c0d40c0c00f909111403003030140c4410640c501012400c0e0380300e894055602170500c3c0c7c0416000b01c2e190340841030807103140c100380f404490a64840320480c2c00a400c90301142d04085d030008103c2c5407074040310752050200c3c2008000003407640c6000d0750701c1c2a0440c50005e09580081c00180650003040f0289507030820110308064a9292031400244a4100303041d0388280c8140424181039600a070f07251445140203000a040101030740b401111094060020041481410030005640311028010101c54 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 253707122 1250 253705872 253705889
    0x50d0f0609080307120203040f1106130b04060801170d0e22060e0609040305180f06130f080304120b130b040506040b1803120907121b08070f0306020307030603060204 73
    0xf01c3c603000310044d0443c0100842e11203030718810420440040c91102800e8403254000140482041c0400042080b0b8030070348109103c0e140b0045000550800214020425100e03a503940e014130303036030362800180c1c040030b82c80b482d01d82034201201460f001da20500520320900401410341c007600401c00c107007a112441645943d1002c40d2900400d11144800d5511103802801c1552500403624098400800c1030042c00c04100081c00618620501907803180070056041c0700050009680c1c40c000b1902405403081c034440c070301242641c004005500400441558121649082e862a0b5528103560704081107000415028007040c00e0902d44022481c44002d041c0701da44140001c055508140c1042005201c0041101031180088001200c4007040802511103004117400c10001e5a158400414141100c5030080401045401c03000b01c1030110028020300780b14496600d201c0556100ca580079201c1c031f41c600660a499903000c3c000c20024045500850344100d452500059441d22644c0e140140c1c2e21a0380040030 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 253708372 1250 253707122 253707127
    0x2070b0c06041a04121d13240f0b0706060b0313060b03010b1810090e0a0b060d21050409020f0403020310140a0e03072a0902030f01050d0f060908 64
    0x800c0305a0290030b1082c10790b0f0341c0885039440d0030b80e152a4180b5015051070200580c451b8100c3c442076003401d00c3c22210320010203031b044520341060726a006094200d400790b034130000311085c24401c1c0f004030304400a40d098060b40300040c9007455202c45140c0d0110f401220903a1f51414001601e00501d405540507030401380d03450101c882a0700b0074605944019100c2486070b45400071090907644e5400c1c80310f0381030550200100055542481303c201020359903200444150404484c40012000424400c5590340b050480c0c4040361908000d1002004038180f0090841001400281704c0c00c006080b2440600d44070b2400600e0b03e52106c0c0316000780e8011400d0080e0510011a0600461405120b580031075009040c08004400d034040342031101a401030191001256202d000481001050007100c070300c00d41014440c1c8a10781d18483c0542d01e1016914041d800314500c400209101c2414000c40e405a415503101e40903903400c1208000350040080422602c450010088100141180c001c04882c40c0c0603201564 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 253709622 1250 253708372 253708381
    0xf09100908070801020a0507030e0111070303030b240a03020c1f140619060e03030702091f150503040b1e0405010f0509070b03010b09060f03090303041704061e02070b0c06 75
    0xb850240d59400181240e4010b00155030520303407001c281d400380d5030146081401d01d01c4180040c0c6820314141e2410009004151010051680542200c400f440c415209070104030132034030140744000604203001041d04010000c140d00580b107500a4100030b00344406950360a2285815180344103001c1004517136803030302c90703d203208941c1080c1007031507122805640c019845000a15891071103c2d01d0300070303c01401440c05104d00c1c940c07410400c0d19142e540c0034202c5615410202d0462005904500030700e45003140304072010405684058001d01440520385401e411030308c950703480300990344000780f402d9404a0004e40203910f040003184442d0060b03002e05d0002440654996611090301c00040510485070301070f62080104240d0381d8116811100180061a12030290b4030000302d007441040c04801c04031074044203120781c01340d010000718041c5104600824861003821401202402544500d0000c00d2048034101c180301c2c8200340401d42448144180c0300095280d9148c003101350400c1c1c4004003164030220400 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 253710872 1250 253709622 253709639
    0x40b030f040218072a08030615040f0909050606060a051204080d0504060209030114160503090109021807091208030f0702011b031508032a031606021809090705060f091009 75
    0x107038210030340c5c00300c00d2120300b1250701d40221b5840003909503401034040d002c0c0e00d610200304c10f0548010f002d641c80d4880500c0d541b20b5184000e007149a000f50340c01c2c0a881c02240b00c614254007201d040011a46455060107a614442210500024015200040100450740e518605ca2140520a9108833401a1140d050b60103041c215081017105d108209101c1041c400f0400c141004051450a14607043c0e640c1d0b80c61070641c0d80503100e0f185009400481e214550a00d07189140b120038415606566800c000c580e035003e424010700c10150300504078100070400305800c80e01c400400c99010355503000200b001a2030782e02c41003246103070402e80300c00130307681c1ca03081c4055441000100008228240007181824440890780d04403030000071298481110303841c01202c00d4a8140195003151141406108409229041c044040d44c0b15250b803e0a00e001c1031405101c52800758810340c00703a0402c400500d4220b0030041400840e0b4000c900b0101000300611001019550b01da42d400300ea07110329074030204907a1901455 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 253712122 1250 253710872 253710917
    0x307110c010905130f090807050303010303020d0e01051611130209010e09060907030b01120e060a0b010c0507090c030b03010e030a02010e21030c0c060703150605040b030f04021807 79
    0x1003410091802d004000750390f118085822050002a80002c8200d9082000b10003850244402400110f01003006018000e0120256040360300a0302601d18481c2c10801c00c0b2041d2680c1c0b280203010440a0041035080884101040901c42c072421408500a141c07000203000d4071400014840a50b400195409644d644034440380b05421058402541c1805c11100240d00e0200c024699010950354141c1c1c0034140c2c0c03260243c0440c0c0c4240440410000a01a00854440e641141c4d03881146040c90039140071940300320211030209410801410b8028180800040541103950181c1d04042d1100c00704c401c0e583d0284145003035081d050005590b40c51070700c01d02030309403461000c81d00c01030382080241c01c48440c0c5001140c02c10a02801516a403699080c0640e24640504020702040e4801e4104001c4841e41682c001000d2910608480003070a0303584200316190301c03d900406030106020320101d103030b0041c0a078055400ca8401042d450858640c44059000b2920444401c400105030564030790a69019004 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 253713372 1250 253712122 253712143
    0x260115090c090b0f030c070b0405010204030516030f30050c06151c0f060203070e0a2c0603030c010203091f020f0703110a02120a0302010f060614180402030711 70
    0x10000040c51030540b15803c64021044a1400007200100244929022074110745100d90b2228a460480c2003608003a4002d400070300045540384201c42c40d03101c50314010f4065004582e48142c20302da80702421b94907071400540d088d00800d1001c60300b03109440c1110030078401400518003980c4081c0c60b45c0024043c94a00b03000500401001d08a41c110010300b6141c402c98001100021030f2700304c10190061070000428100b100c4058000b910110602c0300e4254000007104010300300b01e56070071042d610744451851010b0b000f00e110400c52040c03140ca601c44c582c0c01c1d07080c0f644680e001f02074a060030711440d0480d007a0f900403501005160040c0d142d8042c15a030300100d56500e01c01002003107007440c08079058030300f0910407024080d0511601200c101da841038200b201c4181c66034080d1010081c0c0c081d1000546d03490f00080c000f20059420130f0022568008281f0450080392496690800b9180c00d003020380426603c41c2c00e140c0650341d0042c0c800102c58a4500046001d12001d079610300b05010305540b41c034100b044018 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 253714622 1250 253713372 253713377
    0x30c120c090102030f160c091d16170c030709140108010c0e0918011a030c0102150c030405030d02030906011a09010801140604030c080a020a080a050601260115090c 72
    0x80041c14a07680041904c1c09840340d041402c1d80c9203940e100300001d0700c58104000b80030102036039000c10b4540c03040c2c00c1201c0209c0c808024541140f4600b041c02d0f2500d600145280080034400c008009100c444021071142003e0181620b200181d00c10100c0d0070f0075040e805c2101fa05840c0d80e00c0c1c14030190302e4002180105083d0008016a00842c040200198012a0001d102d1008100404c000c05101c12410f1201c00b58003000700a12103005c11280080d5141c0101b42d4480d000d00c0e511a091b40d4004074100031020f40e107080f440c4443e81c0380b0121a07025003010300305480a200c248800c500c3e000ca80c0c80198080e04010380101040e6240241c0c0400c19420940803024000040c8103031050350340c01140a9064401c0b102102e4641f1600c10003040395401541d00103003242403d203000140342440440c54a00c0c650083c0d440007503803900da1a607a56100d000f44001009544500c1c01005040384400d00300c5c3c25154007904881105031044c02c0355080d501d081a00d000650216141040311101070711500301c4c0300b802ea0 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 253715872 1250 253714622 253714627
    0x12030108060408180303340c050409031b030804020910140f04240f05040e0a0816021f0915020714120a0803010801050901140703020d060803030c120c 66
    0x102900c8407030181c4018510720b00031800c440d14012803c0d0420f1503041c0941180d4030782119508582009480050051a03800c3c2d0741e403841c3d01c45900c0303914080465000b00c1010a0145800140402420085801c1d0204203481d94500c035901e50048070880400d00030b80d60394040c3c0c1001e00410104034809407500740d11115280040000302d003030003c00b9960b160300300c0b200380c150040440420301600c0d00301d020a0324504404003138402807030203d1226094580e00c0b103086045548071070500003107600d2080303151800d911080142000504a174010303c2165030091525446506907400301d83c0700580d1840190900305103890f10b84555074000440d00c01043c100c01060350350001d90a01030744a0060340187c2c1c4d09106c0010b03982200d601c0c0d00c005d511b80c826000c3c0c102c1e600e020703603820411442d400a024000320b40d400c042c0400c0c000f101c14040c80440b44248121055203480300c080c19002584441212840c2c5a19240c0000704003070280086c40c403401c0a545101d585402c0185c0c6115002402403a05090780c0c1e05 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 253717122 1250 253715872 253715879
    0x423030c0f0a0c06030902030c09091e0106030b040b040609060606030204090f060e0c0c0f030f03060a080c1e1f0e24041a040e040303060603060b0909060603100e130302120301 77
    0x74000c941c0c104c07149824001044481d500209080021840b101c540205800040c00007200c0002416481d030059461013402c039425003040a42690180c1c0f0000d80344465407404103011981c005180707600035102d0100050656540d544480650700703650301c5080030950104040020803040d0041c0003001140e240100422824a0314440d9141409804503042d0400851a40c3d54017608001310404100640708907038450b160000c2030f0320700d0b80c400c94800d030140c001c0c0d500c0054000e50000e4294807288004061065a01040751034515101d29000c103550310003034001030000c0c0603000d2403030004100d59540d583c0583d0b0600300306200860035204503418265100003407022502000c42c0c21740302501c0c058140c045485442402840c00e60140707820803844941c0c660180002c0642503401201100d000341c07001e010f081d90310142506140a090f554580120300e450000e03429240c080c0c01103903c8040a001802019101c402c1c510300d0030b0045484280000d101c1030004140b5404200326a1030140004480346550704 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 253718372 1250 253717122 253717133
    0x9070305040b07030b030102130f05030d051e03070306051003050406060506070c0506090a1509030201083303030c10020705060c2b0b090c0703030b030303070e090423030c0f0a 77
    0x52403c400c156403103204c240907503000c1d0101c4943d10710789480c0c0c0c46416111600c02030580401e1181e00e12902c01c1e0744015024902500035524040c002981d10008030b40d072100c490600703a000501c1c400130140d6421021071241e6400b2541c1d00b45c8080399600207003138501490020119002500070910543c0c1c207003c1e21001549040c044415a4015a50f194071b4104c4078001c40c007a9215500718a481d50b02c2e034a12a00402e43c44505a4104c1f4001d80e503c12142d145c4500c030700e02002025030b0705044c00306032801c00100c029101682d4450500040e085070700d0312325079010060410b621041d0501242d6000105501800781c1001150341040340070840a02d0030115001c090ba540640f4683c950640f2120703000403600c84182d44c000c03952000060002845460250046003140d440310320b080b004030f858030303080d030380c140c2800000d481c400c1c1d42c20703240c2078a45c203171050800480301c0c0700400271103030001d0081800d801420220070040110103440c00940d220568030f904181454405d079151243c6900003c1c8150100740c = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 253719622 1250 253718372 253718393
    0x30408130f080a03050904060308040602060403020d030c0c0b130516060908010c09050111160e09010c08040b0705180a0305010b01110307020a050d03021c0207140102060610181805060907030504 85
    0x10b030b040c107101d5986c440020104000e00103e5001a1500d44081400240c0a03000302d41030b485507109500fa10b10841052105508071080d0130101e000007044003006400103000b0002080d0132010b00401c0e003140d000756030303a10323468100011907543d82c0300c1d03c07014201712035a08410914041c01106000703104884071a90001d00342940c41c8034081c100401e28100a8404c0008e01c4404103080c501404c201c400c039140d085107104040d09540c4441d1a42c03900179920303502031191405500480c2e0051580300c076922024000c884da07401c403100c407001c0001c00e807440740d00750381d0340070b009900461085002146038a41071001401c50300100031054060b03002000310400503515458020b0682e01c01310bc02858603451070a04920b46152140084645918101c901e001e4507000944141115060302c503001c000200c41004a854410507214907400842d0010240c03580e0303016030140ba02c01080c0d40c1d95805041d94a00e04509050344ca422040d055941d00c40c141310007414020301d9941c0c000c15504080c041d90410369210040003 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 253720872 1250 253719622 253719643
    0xc0a0e060d08040b0403050a230a030503150301090506040210110703062d091202030702032d160806060109051008061c0602040807050405071d030a08030408130f08 72
    0x40300824105030400c002c07801a140070300b204014198595031607252460780e401c00c021043e114141d040301118050381d0001a0350a00104880251007841484e9805941c20707003001e00b240c0e000c1128070000c080d06440074490150214000c030b00500706414680140b010840e4001c40c0340c2c0411000c4414210101030010300c140440e6800400000c1030782a58401d400000800c0c47d080054510708080b0302e120045903040140214020b24000054101c10707071050b42d6034800c80348001d42503045110414603000e840039403200309500403800c41182c201c5150380310b4207018003004c3c2c81c2c071400c03107690003440b40e00c02c02c1000d107034404028200140018100310004100003007400c6001c040040c1c110014032652070703113080b02c0c40480752528803c004002030725041000e50032a0040302541c0c803c00d040001e40303203081d000300d0f03001e800e00703807a482103074111040b01c00401540380f00c0ca1380c6c05224041c20f502c0011400d50003540320710f025402e07440d114100641c142c6131b0507009500001c00300d401e08000780040c00000c07500c01c0d0803 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 253722122 1250 253720872 253720879
    0x209030613060207120507021e130504050a05190b010501020d0503010306020d0b091311040c09030b0403030b030a0b15010801030302030a1808030d0603020a0e011202060903010e060a060501020c0a0e06 88
    0x21410318582400030780710301c4c080100501410801010150340290140c10788a1007110080c0d00d50501141d41c07040f11134000400d95010040030308a9002010b10362003036030018041e5068900390350311a21034a24141b40c24110b90351840c0312504160070b0205642c051400340c0000d01c01742407002d03001c4000811600041c08041c0401303a00041000c1c14803400d0384000710401000d46042a44c0c034250901d026401c0000b40192008103400700726500915081c40740042004075521074405540c01c54403501a2240c1c010000c409255842205000a560401c41929400d02c1074030106c101349840c0c4080070680c642070300501d042c040701c107005100003034003c025942c80000a1408114011490540034060f4040c2d520060f0706001c00682507800c01d03d950402025280240d5181041c0355540c2985154040244280c155409003071340450700520f000320040c141d408000300041501c81441d81d200b81025401c0e54003000c85a5030b198100040e58046c40254802c1c2030450707000904a20b030181c1a005000000e0680740b2 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 253723372 1250 253722122 253722151
    0xc06170a0c05030114041d160e06030a0f020307030b24221503080310080708070602330907080c030c090a090c0e090c151603031e020c1f02090306 64
    0xb0302c1e106e0741c2c4500c2e0076152001441c20031f000e011154540700c80e0200049a6a5046144041103140f13100c8901802040d0207401007001c110700303442e504100c1c00c0d007403030490307140c0901e0034004042401d0303680702801450b00ca03459072005018880c0240040461044043c01a10840c0e00710035400700b2503481c0a8040030315880890090011540d200c16400319402c000c2134102d002c810701c8180800c18500c401901c51145c01c43e200c00b40c4885080d581c608d110311440f00181d10044040800d80030b2101003002560a69580c02607655501c1042c040452003203541001580c0040010040d00108012040300303080181c01810b03001c0480b0b80030070440d0340d00408a07400c0d56164401d240c100885803036a40c00a003215141c0191a040c5100040e032520381c03440d80c06109041107105004d9000c0110100d5061401c100d0f08441c03400903580c1c00340e0207401d01d0018822505803400c450303450746070a40003c1c2600152503010784444000c100030202c0701050340011104052052060484540700060103d403c101ba16140c4030 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 253724622 1250 253723372 253723409
    0x103120c080f04030602070204060f051f020717100f020f0d0207210f08480a050405041505030601030221010f0b0f0907050f0d090c06170a0c050301 65
    0x80c803807050019086065070b000800100744403595001c5c0041c14401c85081c0030051741e0b0005020044142c2c003606602c40d0b01c000c080c110019a000070f120b0816040d005807112030b69242d007411000090b2800c202595049101c084441e03403402e100d91601d207540328404600b0a0200031381d042250150000c820446680060a407050080e02d85a05850007a84442910440605000202040c0c003c12030080400d000702c2c04145c0c10f400c0d1803641850313003110b181c14104038415100fa1400d01e50010098900180740a0041c401c00a0044010905034102e526415540c0340f820080c0070444e14135103150040c0646400081c0059503010030300d181100c4c3c04580c08812032100c1c901800080c0d0500080500303541c0b070240d481d41080c1d5503401c40249040d007200c480442d12101c1060001c0030004a90070780000d4030422407101c0340e4408101130080390780170810001c5c858045503200005001039810500100348441c9070300c0251000e040d20b503a441440284140315102107c031018140e800103004008902c5440710509 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 253725872 1250 253724622 253724633
    0x280c0816021213031b031101030b0d0f030f0f03050c040303030504150204150311030906040311070506030103061b0512130f05100501080c040603110d03180b03010501090e0103120c 79
    0x142521110102c590f030740b5401a0012048021a44811940c041c120030861011510700203000048a0f000741102c00c8101c042c00045004204009105521900074200c2c98040b81186a00e02400d500c29120404903901010001d040c0a51002942041608000400c0b002c1c83da03101c01e50b02101d605060108807502d079403900101c2c08000000c0100070900c0814005040000d4480d0308030188115101041004a200300d80010b034842123416224641c000004140001d224480d0031142c0d00d40c000a90340e1a54982001070520783c020f91080ea0050707144c0e00c0002242081e03880c010140700a5003001442d00c4412240014000d07401414003440e21000c122800501c038000b0780b0740c840d0b664441c00360b420f0139526101c0b420041c4001c1c0118406445050248001070400e481690140c0303030804441e1000e040450108202d0740c0c240c00044040046007400e1901e5011880c80c1c0c440074040044a03107031698101000103042c400300d940960a4502103100400208050302001342d1001000c0c030748403010041a082c132 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 253727122 1250 253725872 253725883
    0x3050a110f0f031504080c03030709090f2a2601090e0d021b130204030503070b0114060403021513061e030606090501080a141003020901090606021e070806280c081602 73
    0x60b041f65001c000100136a07254061114015114856410405486c680b43c1352811510150440c285058038041c0201d060304640c60200901d04141c900045510300811100c2c01403140301e601400d148081400610490103a4012048552110001450f00041c0480020355030100d1854032094500c44448500903900d88400581f12080000c60139907807159030b494101c3c0da07075001d00c9041c2c41c0c442da410000700b845c202121403112001002081e036800c0900715020084070113050242154508002c128a242000555004a000701529150094006182c1514405443c800881d00003090720f80b00d403d10400d60041c00034419601c0078648040c00e0360701c0d0301c030200040c080401c48140c1c21003940100291078a014000d90180ca100f40c0da5070300f040c0d81e50345001042c3c0c0c005014450140c0c004c003d26107101041081c0c80740d003c3e56440100e1740c181da510102d43d400d105094030b141e08540f824010101d0144050b004950007030840c201c00301f21048200b00001c0140304058131200b10070040b140f6030b119840c800c108 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 253728372 1250 253727122 253727137
    0x30c090f04020a2c062208061806060102060105031e01020706050c0309121603030507021609060801060f141c060c0203033c060423090c10050414060403050a110f0f03150408 76
    0x11a8100e05108034241020349d05140f00038624400d030400649254804a0800d040702d0303029008005600300b180c96200310040780f43d50845559401d100580106009004590043e450030480d076a0f0f03030030710300312460070000ca8a0400026007403c004280f10307030305140a502412a0940303000a03d603140c0c2c03442241046650503602d00705020f1000c0104012400b17900610031202800001c0100c90b5542d0084041c08401c3e20072040c048a0080d1b203c2000e05185c51034079001c00302203801210080155031171004892000ca00070005034000300400034089025031213201c01350848140c00c000444010251100a5a0b080d5080c5004100002283c125261504065440342c80b0b0700c04550540360702d19408102640c02c440c62202d0344680240c507c6d642c01c11b18408500709005644540c60b0604240281c00a890145060313500084100303c00004584140072040c01103101d0700b00f000b0f00c1240002041b080d00b840460f62031040a101112182c243c0c1c1c009034000c005500ca4001781c2c543d80c0c660030400401d000d42038 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 253729622 1250 253728372 253728389
    0x306060403020306332409060a020a030e010801051c06020c0a060b030c010c0b0a05150603150405010503010e0a0f05014805030c090f04020a2c0622 65
    0x4203109001410380003680010340c500401039020f00102d034100321794071005050301c1d801c0580b8040d040c203440e00d00d28220040c4130007058654901080000459200e40c440504140160090702986040590004112110074424a0005141d50603d070005140c5045640000304400340110a0b02c01c0000c00c7c0c0680e5880d085107800c0d07440b003410900b4040044c002c0500c03c1486400342c480c400007a0342c05070000180d81a00044c80250580e49c10303004200a0402410024288020750000030303241c0e032403000139403060a130003000c2c03e112080d41d014881954010b030881c507c240d051028240e0b06510000b0400d03640c2c1c0c3c01c1091030308038a500782031036401841004590020341606814400c0000404074040e00001d415818003104000c120400d0341e41d15041481d9500012001c001140d0819410360107015200b9006011492120442000404980c0b0011501c1c0c049500190020800520400b200c1d510b400b1710550400d818040d01c00081c02407003041c01c1c2d560b824910301030010303007084580c084d90050800075 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 253730872 1250 253729622 253729633
    0x2a010215010f031406070e1005090604092909190605060706020301060f05031006050307210b0f011805060715050a0b040c0f0f140d020f0c0f030f03040803060604030203 74
    0x200550a00c0c1c81c2d103408151030348450100c164041840000f0843d01c100000d17951801c0040344c54040001c0320400024a10400030144000303503071f6969100c001c00007000c10740307000508180392090304002404804096003040681a59100319a1211820f15a000c20740f0300751100d0310480603080b038005120075081580c001c00003143d81c0382040255401141641c0f410348403145e600d40c40b02c00c1103900c0d100440c0c0c074a1100017108410482c490180000d140c0114280c2825280b07208809038450a0319540009803031521745a140101003420458499407a40c0400c0c603281c501400440e11103c0039041070312403039008850002d180428021035090010901079142c200740308904042240c07034064103004581c2032003189001015041d86000b00844401d048503919900c1d044002c200c02600c82c500c803106004a0404100101d14510200b440209101e84501c1030041d201d01c181c003000c920b89400c0034000201507008001c0c0c602c01e00b00400559074050390024181d507a075650703000451070600580c1c0c002074261154 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 253732122 1250 253730872 253730879
    0xc14032505071a04051207050c060d111201241706030f12090103140f040f03030e1906050a0e10020c0a12030e010509010c14090a1e03030806032a01021501 68
    0x5100c083c40c0610700400488500782c649211820f030502c900c0c04004c005901c904006001c90600c103011740850300c6d40b40800038690808141d90032480c1d01410700c40b41c85411070300052000008218102c1c00060340a030403424091614003001e092071450701640f030401441d050000328513a8040040050b1035000c1016a1114200e40c0b4000c0516000002c100d40403904040244c07000c441801740c014829400007006034240e86543e00d6101c41c1500180d003d82c00c0545404a02d045100c082011042014042c080180c0103070345e6040c5802103034400741c4a01100c80c2411081045098005030251480402c801e0050365809800c14044c034140e205440102494a0354914509840d00350703000680d10a904c0c0000e01a5580d0011114200d0301e001ca070000206035201a84165006000007a01d4525405071030450550b448403040c1c120010791301c096040c24908804107004140e44070480a0b000941039000b00206109401c0906082034240300e14102e80d00148542c1e040c0340e108205118030b4011213103062046584 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 253733372 1250 253732122 253732163
    0x23705070608150414060409260901030e03090306180106031209080f0109080d0e010209060d0203101703121509090705190f140303070b07030c1403250507 68
    0x80c1101d0040f0b0000d003400d0010007a04003806980e09140e00d50300f0781001a81e50340c00f080002c2020301015a4603000c4081104141d1500301c2e008500703070760f42c035450a495410b880c00040540360b494405201070381041c00000680e440000d21240c000780d500c1510713824010840c9150b80182440e80c000350010300c400358001c440039007090810065550901c15514200d2840e01e030309090f01d801510003014007034104005442c1d02015845410621079000025192648400020381c2c15044980c40704150369000082c4a40100701d00c2150001700070b82001c0c03110400b90100703855100d0041c007a032002000c0c101030018200b9000350140b005598030090101000703003000c40009a44100b01d0203094000c0140040c11200b0002c18150354045601603d8428949418010b10b20044142440c809030140b0040c402d0000003001c242044e4459011650001008501c2c418010b000141c00c86084a004400700248100b012003120401c2c0c5100a4051507011480ca450084802c0c1c8107001d00a0010005032400801054 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 253734622 1250 253733372 253733387
    0x9031002071b08031201090b1504080c0910060503010614040302121515150a0216030813061d0108040309051201090b07030e07030f0804050a08010f0c0237050706 71
    0x5040c2c40030b5241c0300c0e4603401e070241c0d00c0c815240300c0c8503403111300401080151210b411181c1c0d0940007801351000750885400d41c07803054200d13070041c17240c41c0c0081500c0c403e60b05144866944c00710741c80090405040c03428502500920060051108204050018207103a505140c2184c0085034058103901900740007500c0030352030781c2c40d00d50010741e41c1e90403501052200300310a40b07031072003240018840344444800411215055000500d400c05500617680312180392104400300c28000e501421400f603032640300308a2640c1018a82c1c000d07005002c00c040303500031802c03090100d5000310300c820f0a201d0002d4807141000d42b8410019445140c0c000203183c644184c1d201b06401060030544a540711503040c0c0c84009082c0c00380c4641d50b100000e00c1e0b12070340080001c140142241003a8502031030303000e0318060b111004944141c9560308401041ea44650141043d800d40d40324004405040e48060a0b464000b203503d00007032104131203001c002130913500b00d07692218a605103404040e40d1000445e9400b65a0f00300c0130b070014 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 253735872 1250 253734622 253734653
    0x10e0a1a1b0c0414070f0c0c08060c07110108011202040207140d02030a030509210a0e04060303031d010510091104050d0c0501080c0316030c020a05010c080a0f06050a03080903100207 80
    0xc50400d1001341c05034002c60103590061000e61900510042190001c84903a6415201a19118100b10f00050482000e002031806103610681d0a80c2eaa0104c3c01c0020415030000300441c1041154801041091411440785240507030403540981e4450740c900301192075080110f0010a24010072007a050700c9500000200310003c0552400d00484d80c542d02203d0b11303010742c44403a10b8102e08500104044035070080c000c108011050515010118802c0701240440b549600700318042030707079414801c071000e643c6100342481020301c00090050346006082c08060741030620440002035156504866002c40c40005c0e54064074010b407800380c03101c0c124141902281c0591181c10b0200d4a00801b280b0301003502c5080364402c90096052440600340a1411030040c444410110704601404940c1000100d007030245800e00c907a15660f880309820105968401c0300e201040c06200f581c9484800c100e0380e00c40c0c001d143c003125084500c4a07101c202c9400800c3c1050b1944200041851000540400300308001c800031207030 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 253737122 1250 253735872 253735879
    0x6010618080309090604110d0507081014100f03020702150304060606020307111e030303130c080a03020a060f090813090f0902030316030210020c0106080c010e0a1a1b0c 74
    0x19650721a060340d142e201d00c0c04019000314840740002d450b420140c012030680c14124070b103280b40030740028515085801c146c490100256459052020700e8204030a600007405003002c54040340702c058000030b0f01500d0111240300900c1078100b403c00c0905c1c02941614402c54024006140d22280120300200b95841240c1c02c544940c86d2802c080f07600c520000c103540d202c0c0e0b8801e4940601c01c040208100780c80e154003107070a00361403902844034685e45083c40a9801400c5990090002c6182443d0400c0814000d0300202d409038442d900c442e000c00c2d4005410140e1030381156000886111000c40e01002d4904080080c2080e0000190320781d441d01d844104004036250544200001c0350894006401c1c0c0b000040d001e54140d1042c0040c4507102d0084e0f0035000034074483c0c011180c911900300005001d0340c100300300b040281e035550b903001c009140c0c0c24003010107500c0342460f003031010a0043d00040e0101c002802104c620034650117450070307a8003501085442e04019048422601c10610103443c2e554400050031900 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 253738372 1250 253737122 253737167
    0x5010c020c060d0b0301060b0409020d051602071701020c011d07050d1709180907080606060702030a03050d0207080706021c0b0f012109060510080d080613020903060106 74
    0x1205803020030354884190008112926100e6442203160181c1212041c1d103034507540e10803000030000312010080009088501016072200c0303401d0981000c4035001082505520051060b00c01e51544c045982d106490340d4140c503860041303554007803070300900442e500041c0725032a25104403031070602005646811100f0034100e85a480d102d03c00e00280c0c244c0390138018089108540b9040e03080381140041c00440c4c0307020b0700003200160700c4e40c021030801d081610980c81d075070840c00c070078018154244165944004142c40161030042d50b03a0110740d4848800e14007404021000c01c55000132005070b0100c1d1480743d08001c40603103170030032802c00030001e500003440c1045100007204540030016280c001e82d140071200800400280180c4c43c01503585e07030800c81c1c052000720b014140c201110201803181003d994090000040d2500d40720002c03002640d21034205802980c09490604c110f1580311846aa001400307072202c04140d00c1f400c1e000006400344400f56070b85405042d002141c00c681c0521941c05007600e0300448103 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 253739622 1250 253738372 253738391
    0x50907050a080a09030c050a110a09091a0403140d022106010e04020c190c060f02030c07030f08070b0f060109050a1a0a09050d05060106030506010f17040c150203070501 74
    0x100ca9206010405000c1000c1c80c001a102c002e19500c04001a402414a019040120b0340d42034100741181070122401101240a000b103802c1c0b0fa10790501600c40403808101c01442c0d40c0f5070595070340c55a60040014111080080d042610502403080290a15005a61a5414038900f14041c0d000f0022302006024800d802101c080c082080440c01218181c440d0200c1c4415001844040d601c0000c522200d88280c0107240c0035605c0c400d00c2a00064020000a500542408070090207100e030401050f0856005000b0345181d01c1010a40c81c0440741e2140d258a04e540551621010301d003c2c501001d040b0142000402c851281d5100e41d00d44900310036610f0243c0700751280200007100c9017501500160f1440d40184400a1b85e040000b0710310b2502a00f00340700c005580e1000100c40c40b080d03000445868101c2401005015094051950401401d080c41031920410600080001580c000e03d64540a45c0c100883c081c012207062200182000f80129100c14050500180d940d0740000c1c01281c00350302e00740002 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 253740872 1250 253739622 253739627
    0x26100c03050f0c07060f0204120f0c0506040f33080402030d0908030a0810030c08070608060d0206090607060902040c0c030e1e090a0e03070f021908060c0d0902031204050907 76
    0x4600c501c1c14500c5007400c040135602c0f1003004040460303000042540c00c000200f195400c0180b66010740340b190011441d40c03801450005603030102c0323901090003090180410f02800141d1200f0310103130740100d1400d5010580c000c5c91288070300600064100007002c2e807101c501c466940840a41c0c4180e000380c0884560001d5088c2c22500301045209041d4039400600c11510300c54460111b10303030030440c0e2042c64109691280c0f900c2071611030301d0b440504241d015003010040c1640100005a01c2241220060b00081c02d0b90040341c490303c2003420940c85284009019800c02010340d215500c2d10707801030402c109491031104060082d0f16080420b40101e51000555541031410314950f03400120f1401d5803000d18010401400f50440340a401035012a4907204020300a850400144c1915805850751100040181c010312418020001c07090388075103400700f824025001300292a40d00041e41800c11551016103c20800c000c012100c0001c0d418050244200215920b040107001510b504449401f21034075456000d = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 253742122 1250 253740872 253740901
    0xc060908180a0303141812010509060c0301210503070c0b03070e120705090c1603020c0f0d020307051315080606101805010f27170109020a26100c0305 66
    0x40004140805c10a1700c1545d10002e00b41281e0034015512217000c41100050740e900704001c80034880c1c5c0d51002002072454082100d01d810103040703001c2600d1941007503038941c03490715100c0c40312500c0c11402031350104200e03080049880858120100100541c1c81d40416803042d40183c80600004058002d9560386103049143d50b80f10880d041d00428045240074184894080003c02c01c1070074000522810078220841d09070840c0d414441d43c081c0151441242c06c05c5203140f5001c034828050100d40d40204010f880c0044d003002a9107049500b800c0301552440320802814103149101c04942401d80006540b54000a005000355000c07555900c810141e4102194508401e000004800500c05800c01c0306500400340301e1104001c1d031520000c44044a0300311503010290300900300500000700030403c40d4211104d030006c14103424100910807080c1030b40010300c1001d1607004842d02040080503040c1504540d9803519200c01c2c81c641038540350b000c151119401000d0990061002c203040000145000030740120 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 253743372 1250 253742122 253742129
    0x3030b010518040902031c111b030a0b100f030605060306011d0c03060105070606120b010902131701060503010c0f1704120c03110f030c07090c0912030c060908180a 72
    0xd030308a01803035281004003500b13804505903014007507008408064615500e600061080075120a042420320015881c9400b5041403484000b1001c00300080c1e660b41c0c003080b000c0c0754940110a000440c2c945410105254006030712140d0280316094000003041002d401c420f200c1c81048040d1004c0ea070341c1d148640b80d102d0b540c450200c0c4880780100080c64800c07103100615040301e0185801410940c0303035600d0204032003640d000088405131232051503041002c05403101d40540480141541000300b00303040034002e03407000e0040048140340801c000141d207009512200c0185401070003404003125802001c5c004080c002d01c014005564403a04061041194021030700480c1c2c07100c0f40c106443c94003d41150322401c07034041202000424401408600000c0180801480320f010155913580c0d150031401b0f1a040c110750100700c800703041160001465400c811070004403000000c81a107288201e1408544c039003420701c1e000344500c2c40e0070f40d03803000e000e0f100b0003601c15089140b45e00504602c0503003c01c19aa1094071 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 253744622 1250 253743372 253743397
    0x40609050d0609061a040c021218150403030305180d020705040903030905060108030c010e0a0b070f051e070213050f0601030b030c210c0a0f271803030b0105 69
    0x204104001c1c142040311552490064900041184080c1d83e403405813085446404410440e101c0031600a00d858030941149014a000030840d2400305808002c40d03026039a0b4020b4444504942a402a210703d0500c01e245104600340e035944545038038001d00282010b540c003020305080340c2c800040c0b541001850803080c500640040c1360b0646032500701b10140c42911811410551501c0d40b46000034000c003c418082c0654801940c0c072201c080341e90600711f4102280e411055400b280c4942c0c0441c002c03806e00344c0c0000c2240b4000b084041d01150070348042c03007080120001c1c00e00b020b11504000b000a0041c00304584200d400300d0703811684001c1c45c1c0c281d8005440d41c3e41c421b4540004254035602070360201c00d20000250640300301228000014110300459052040304d00342420040500c21418800460600c0c01101c1900b140381c02c02241e070324903000b0750140803044050310040019445020301004400600341e5801e024402c58000704920310b05242070304501090410880030f400d0741c0207000383d51150b030240 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 253745872 1250 253744622 253744637
    0xf0e1509120a1d040207050d0906080c0f03010306050606070b0a0e060f040305031810020408030d06290a020a1e03080f010506070213060f0e160f080f0603070b0a03060f0b0406 77
    0x1000b8030f803410f5100b0079200d5401030742000b03c03400140e010311082030041803a460740d150051a204010f8691803008208041c0c0c54000c100d00c0340d811152a056906403a002040050159246404104107105401b030280c20381d040d4504103c2410815001484443c07159800d1710150380f00e006060100c41003d4074000e000c00c0d4180009110096a41100c0d01943c83e00c0c2c04542c01d404080c1604001c0741c0c05908038204d01d0f0000a01c141d1840c0741d5016080003040b0340003102692001c800c500030300c0016007025080c03003103000151140b91030780b0070030003180c0b0346800030201c00c0230b0b00501170081003100c05508100d02283d9090001030800703c002c412035040303a0000e4000f40c43d206407642008140c00c00140c45000142c0e0381c1d00c2c0890708956406000006d0602004810340508124070b02c00c24100c50440c4607010881500741181e00e02d03600c02600d5400640c00f005084982e01d400000a050000036000403942500100e501601e060f45904924112032904110300c5200d521200c40940c00c8c800c5005482c080b0b03450 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 253747122 1250 253745872 253745897
    0xf020d023421121e0b0a0f0312170a06050102100c0801060c02010201021903050402011407020303071e06050f180703020a06080c0d110909011401120f0e1509120a 71
    0x1d90442c2440c1e009610b402c02050105501c0d40d4101c2c2ca00c503018481c00c40391a90b02c0070034456103102c0d10540711011100710031040d150200403510f031030b042e01008200700040c941c803210184c0500c1d0307a410541802d040310b12052400045490050072a807044c02e00601c1045a4950b50340030302d00c104c1180c2402ca84e0340c2d040326070a081e8155100c0c1075250049046644c01c1080350814541005203000288075540c02040078106800010705040310001c80c0d440901041140600580e000012a40d00035886180484c48920072800c0c2082d520500d0409490107042100b000102e200340258948200003000301d20100035200301c001e036030700c0c425404001d40042104ca005d200352401041910b610080a000103413031b20040003001c01c00e50305201c00c0140101408606200c003480c2286403e409046424103c0300c941200d0b000080c49088401390380c0c058655140d00d00c8682c240d09030800c038113688040c411180300c0440060b03c1040d04100701e500c0002405207070070401c04107240d5421128800019610070b51040c50 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 253748372 1250 253747122 253747163
    0x9051b091305090a0b0a05010e1b030115090302040905012703020601140406030c12050d0f0806100210180605010f15030209031501081f020c100f020d0234 68
    0x50203843c8000d6481885080c40c0017880d1026003521070083c015000c260755152088401071450090080f091a030f0f8030805011031a000c10050728115101c61040d00f80d000700030341080e6007000180d04042e41090030710f0540810f1041c15003008a0b1000e41500c0300c4e2041c4c008501030381c00003540140003001078101000402c0081c0d05010030070003070a40140005816580c84e512040d0f0249260310901c44401403403a080b00344101072000440c0c188160a00c1c031101a0010343c02840d400e0020002d9100d41c0c002001208454400c100035181080d20103001c20203000c644213800702d440b01c100000c6401c1414840081001801100f01601311641d4a4089481d400c010b24298007940246001c99014450911070910006030045101d0080120001411480c1d0b400b50280b04002400c580da07020890042140e403815000014070603119003107034079000581c60305450044010b813180743c6010540c070780042000f805013100c09650b83c681c00d04d03404203009200030014055165051021000d021080b03407000d007490044d0f = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 253749622 1250 253748372 253748381
    0x3271503051b07031d090105010c03121e0f0e030a09210b0408070b1b031807090501170d020111030f060102031e0a1709060411011809051b0913 63
    0x38010b9604034481060701054800a801c80316095001031050341c1c1040d854001807071100425001691402c07500d6040c9000a00300c2155001d000b0100003c509941106411301e1780300700308074040b800c12201c21583c0e11a05a02074088244101116446c0c040e1a900c6410008100d50404c03c3d80d488041181c0c0c945154a46560780764501302d1003100864000c840000c1c81900c11a10451284590fa510385486040c9045010350060031f0541452042d100c1c3e45042140200b50f95003d148940005080d1120403540c909140652f4400c0e07005505003000031600b443c11043c200a640045406c5415008502c4000c909030741440303032100d500d05010000b2550106400ea0703901d03404241801101c3c0361401480c08102d10545944070a074400c0c2d000708011005c070f64003165030b90801d1200036a01843e41000301c07449454420180c8024500c40030204203000e10390180a003040c541440d446460b02007507a40c000140170708000c07943c20032921641e0303c4114200700e643c8203070394110310050006011403070000174400050 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 253750872 1250 253749622 253749631
    0x510060f05040e0106020102070308010512060411040209041b02060717060d080702100e0a06020c010516020a0302030a0515071d0108040c09060b090907080c0a0c03090e040327150305 80
    0x81c0811012031450a010701d4a07009001704c0d400107940b0041c03030a00505072001178000314070030140440c4460b130000c00000d00c6a00940c00c03600741c3d101d010030b4400007002403262021054101d410099072000a88007121105503c41098081d244141e41d104002ca0386c500c246c08802c80d416107500c02203102c60908a40050300b452003100600d00d884100d80008145032000729003d00003944000701801e940c1002d244820003413440b40018021041361100103401c42c001c00104506080082c0c80c01c40c20356507029046402942c0203010f0b2103d0b0082d43c28980e03125600c912110708111410400306681c0d6108503400c1c024002d2800c0d43c050b0580407540110f54080002d402629030960104012450b0400e51160b48001c1015204503030385c885030070b814086030010041260003030040d10020000141c0b5030380205ca03c0c0302c840d460083c800c0112440e054070142c195400005880c1540c074100420150022540403581c0c8000704040d1050103071400720150003280380610a02903003c5202c80d07404502070380201c0e400 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 253752122 1250 253750872 253750877
    0x270f0a03020117090a170d0c05090609060919030803160206060603014203061202010e1903120908013e0403080705060f101203050c030c01060905060f0102010510060f 73
    0x88075440e450702602100150007854001d000000e65030300f070070a0707442100752303500140c180581410b01c0030380000d40c103014014996000c1d0b030002841c9807080d0b0f105821040d1240c3e40007108446d0303c2c2c032400c013082281c1003100c1506031491007814022090303000242d01c61141710f0060030580f560b800c001480d1006059004100d00824080c0c181500c0200d140d56144242d14921500c0501034410201c02019107140354050350f0a61446100f00f80513036070143d00880340080903039914034107844040d544402d1400a40c0041d103207000102c801e0303024a81c40b5600d0710403221030394000e10240304444e8035600c603d0030010315540c80c0c1c1c61581500d4103400d0005114081440024212420141d894a0b04140c075800600216a541c0004040040742205801d196802510b0300f80c043c070f149070405c0f0b140e00502c4000700d006001d01c00c02140054142108004580d518500300000f40700e100ea8903840d240140c10151140e501c14001029078050315441482032038451405121510340251420341d06940e45000d2030116800c = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 253753372 1250 253752122 253752133
    0x2010e040b0d03020d141903020717070305090901080303060f04151e03060c08220c050d0b01061101020f03040b0903040e090718020415080a02270f0a0302011709 71
    0x45035600c807001071220b802a0007510f03d510b42850001d083e0500d44554002e104014801c1007003040400d003004c01008448c2c14010303521001420980246441254603500102e0006000802c040d48100038083c5204103440c00c01650340c0700c5d40059201d01040340c2003a08405048200103051501d600800c03610700c16440c00c006100c0e20303200195070b603410754080c0b264804000081001049050b120302d440088a80c904102e4508040c0080b2900500f415030340820404401741130414403490321400402001c00901d000fa000099151403c0044000d00c41d400100340319440c44544504180200c500d6045400d00c92441c6542c0c07542c0e1501c000300040d068800720b00c424400130801560394494680201110001049001e00d4a5058218481522041912280180400c004910659079441c480a071541003071109030f5580305540000740200c48062030ba400c024556100f00000b40c03500e074600c011044d1030b9071200c03007086000d11907611550700c00280001c1c812010249140c04120400c2c4d000913599042c0c40 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 253754622 1250 253753372 253753391
    0xa030b0f0d060207110102010e0d030f0f05090f060c0f04230607080c0601050a030804060f0216060f02060c040e0c1e0403030306060e040c020606060f070f03030b15130302010e04 78
    0x7400c074544404202c0d01d180d400070342c050a0080c01d00b00d1104200007440240042803000161588418035021140245a140c1060000301c490940001c0c1c040f01d40010100068900140010703a01d44611a000b40d0a0150710040354401380e81d1001c40d0100c08900e00500e240916004804103c2c000c1001600303160369100003168120366580c002000b8090266074480d40342c030344100019041090681c003d52040c18800c808000180220050b14104c84460800301ea54003c4404180d040a01c10300c0c2c40d40c844441c403a000306000750014800d526481d4103074219001562540000700d8a88101d00490000032502400126084499002880d9545940c2c100c1802c2d482042110205a0000e07001100860340300c000502406a102164002000c03048805104003c3c20000103900e9003000303009140030741d0000172594443c0b00c030f01003225440c0354000074550948a840c02d00a00810304680f42c544210030050244680841c071009a420111140b0303641010303c7c0c5168010b4a1412002107801d8001362960100c8 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 253755872 1250 253754622 253754629
    0x41b29040b03010e0103050f0c030d05090102012c010f0203010513180b100e0703091a1003021305090706050a080c03061314010503010c0201060f0e07090b04060c02150f0a030b0f 78
    0xc1d8001d110200b1070505179415071034420300b05402004004050781c080000007400d035030000341201c0010058180340742d84040c0d1071b00407405025195541c1208942c0017201c200c1e110400000010035540351002001b100313807086802b0050344401e104881d4403050740602e818000a06a1140c292008401c05517506001203545841c8990b00842e44042d20881c190750401901d80c840c40000d620201c81c3c80c081181030486d5440b100740155403140e0201c0039201e000001c1f90142032950190203590000c0040105d104510380349005444d00319601e1060b8060810b00060760b900840035541f0b511146e8886295035034801005035070a820080100e41d01000458164628010034030038094500000140c412907907040005041c02d59940c090074008580c0760a004101c800e00407103045017a2110a0300c4581542c4030088104d401c9103e54200c002c00190000300061510b410443d84810781e403080e603a5040d90b004410102200b4000da0082240719501000214007140c865403011000020090000e00d4400284011 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 253757122 1250 253755872 253755877
    0x1803060c0512070302430302071a07021c020907050f090d0605090105010515090603090c030102041d010816050616150911030a0203071701180b041b29040b 68
    0x5a1001c29400540e10080b0006e040c100310390036001454102d00035004540a880301131008a100355451282c0e03c10b00300700b52081c82075500031300b80466621008140b0020002a56003d080100d10681ca00c900c150f040404d4607103c0183c2d5030b0010460b80907641c50603429965940218462401e100040259190302d69900121000032401010001218a000446942100d00607009a0311540d04480140300d00a0032104846400706d055aa0644946503081a0707072618401c2079595070b2550000c113002c1581c1e24504d000e1000d2130048000659581d071b844604075251416a003154051220310715007800141420002001d082d0311500d845004405203840301d03104030781c0e1a4482c40b0190307214406107080c040000400038080404a0151801c04104e030f0000380d50303256910841000c0d00c8040d1081140040a5000c20050000f4400200c8401780b149006420304808440448074030700c207000182076201c0c41c29001e2080c1c03074410030000303a010540301e050303460b103151920440c10540c02080045904c0c2110000f = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 253758372 1250 253757122 253757131
    0x310050315070f0806060a180e09011506210902010e0a23041512030909020d050612060f0402060d20040f0b130909140307211803060c0512 61
    0x30008054140580000c0001e01100341000070000c9130404d010385c90b50b81c1c000b12540c0c0c14150400400c10045400900d0b02408268015800951940100030400f40190010f419580980302c0814001c0e8603080240c600c1805030051083e104007028541090310000c0d07201792500c6005061814204010400140c86902140c1200b00e0313001c000010401c07a00b144c80405910b0403001c030790510005210421940c02d010b294030a5038014000c40959500f4540500006005811003207001e556442c110401c58000d00405d40d1118040e007021425411800d001290031405032265501640180e10b4503000c00c0305941007580c49000b00e5950340d1040342e0b203401c10302800039623013401002c103074459141034075010410b18540c1c0300241c106410030080c2502c44c04112030302c080e83c01c289400a0762900030708203482012050008201588800104a01449066640394801d03800c1510b66504a00c3d00c2581211000c0c1d62445c00c3e0000750080d90309000080441d04400c040c1d0700745207040c0d410004020080c95401d90140c4 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 253759622 1250 253758372 253758403
    0x1230306040615030e1c020a08030a020c0a0b010302030712050307110f0a0e01140409120318080a0e190506120411040c170c130506180603012c0903030c03100503 71
    0x9080c65620f80050020b5070f10544082202006ca0700000c1c00070f0344684c504103009020400c0000010f090b034205a040d242202443c2e022900030484030f01d4078044121003800140c3c0310b88220580040c1100300c00c0f0710304011550050146080c01c0703607641c0b203040d00300340c6000b01d0740d001003410300310103040e150640050000c2080724031216180d403400d800341c54441075211540e40204e041501d160701160031001c4c0b210440c0700307d10700040c4916104001059403110b00400a1001e203002584c01949e40d032220390802000404c44d000c2001c80c010b01d031012040750080c410b880e0400b00c00d2203641424030b0a00e00360b65100d4041d00c445466004807000203000c0315407064007040481d100500c40062000600c008940c0201d16010301840c1045d40c480741485030240d449050306c500c0c800200c01312814451245588240c1015042907140d503101c02c4802c0c410000015500c9c0f40ca070303040d1801c1e903010a2140c259401041c01c10095455520392149840080d44001c2100555003010140012035440070070040d0040e82c040c6 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 253760872 1250 253759622 253759631
    0x80307030605060c01140906061f0207120c0501020f07140f0f060406091a04060c02060c0a05010c2102040f0314030417060708070c1502030919061a0123030604061503 73
    0x300c0206c031030b04005008900c10364407140402503940c8400c2108402808442c0c00801181e05102c0d003285000d005401c968010566a845078040010854890302510000d809940c090780d03480e4031141e6240c0b4148255291588040c8211149040076603241607a40e8004d00100b41408001c0003181940e80264070160002da04900204070842d400b40b800e540c81c4845a560700c0c5020b181c0704009000b07011110000e071199030300040803482c4c840e0400c12840b036030358060001d0001d1316010602504001c0302640d40c48002c1000390311800c0391092031080701c00340d48410000405890454980b03988034983c803146500036200405c404650340003a07c000741900803514004055500e040100188015405010302060183c1c0035104400100c0d0380546440100c4045070040e12580e0ba040c19500c1c00d4030409060b00314400800c2c114013803000070742103100b010b2501010030341c7d10b40c43d003001141c1d0184004e84c10891500300b8040700390703086210001903404c000014408213100d51a44046142e0481c49111000402c1d80e4 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 253762122 1250 253760872 253760891
    0x30f04080d05190f2a030e01090303080c0f16060902010905040608030304030c05011b12060e010501081503010b10031401080304050612040c030b010b0a11060c07080307030605060c01 80
    0x81003008555615460302d00e0030302c0d0f0503101591292909480c030f1003d00950b4505006907034400d2183c180006040c21052681000e212210036508000003404d03000111506603644241d4000e00350802141d41c540d076082d00d96512250010302d035420600c071180010900b040800f0341c018070211020f1740140a104002242e010510025103660b0013640114003960a100c02004550404011b8a078400c0d0141080c21a940042ca04180104182071841108010350002641305540c0310350840021748031018200504d5442c0e00d103080b1644805d00c51140000c80c0000052011402d0445081210390082d0011501740c045100041c4150b2301c070000300c00002d5903600c46000c1c00707812803900c0f4010a5000c002d58507083c184404602c8921a550136001561b0402003c1003c010355001c140c0d00464000c070342d000d599611041e40080075401210060001541c1940801e22114085400390103400c014a106240082c40d68130518690070080c90030043c5070b0384050016031354586030000c0140040a50002540305103 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 253763372 1250 253762122 253762139
    0x180108060a0c140d1817180307120311030c191a010303050406030b03030c0a030203131401020d031d0d0f0908010207080334080403030513020306040602030601030608030f04 76
    0x9650180c0d0b010003400381150104860b54a045413000b080ba4400400e081c030030844045c80000110400801c28503000460051300381007040078024041d00451411071441d5060704159682d502c0780262402d40788a00407102c0080d000b00c031514001404402a02d06005401e02002d003060243c5085c00e02c0c24030108000c030204036401010901e1200a000054010750540e1001000c0740500e004440505580d1080519903560030003d8502e80c10320700d021280c802c0c6a510703009442c0c1c0c1004000c0000000c40440205038408141543c420201042e4020b16a00f842c007803049000d01101c5028000400746203481180d161014440345610400b15100e90081c0b4003810703002800b58000354440201e5910500131040042c0c0c045040303940100c0e054000340003200c2d510482ca040e401011402424610760640e403048002d4104101d40d00c02c43c0a03403010841542c0d858080c00440c1310305034001398140c101308005800039045a01541e0441c0c4180340000c4e240c0d40b100e152910355844810164594403001c0750400c181d10 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 253764622 1250 253763372 253763381
    0x20a120c0b090313061b0c26030705030a12060e070f0f0306050a0306020d02221e0302010c020405090f120408070902041a0901140706020711120d0c02180108060a 71
    0x2c00d081c00030b502d0710340400510601c11034140203440030009140304d081d0ba02c010030903000c5074003504240201005582d035100c0c1c40455010341e0742d000b0b0230400c201c070030060b160300407065800d0150040090340c82d20081c2101101d142c0e0490940b640090341d1160085a0500300d202e4152040b84103844503d45c840d8841d20280c00080c0d401410010035003018804e01c180d490345003603501180d41c400741c00b40e22a02c0c01d071496400b82c00340b001350030b1a000d09481750394001d40041d0800300c11901c000c02d42000b0000f003150495424072003800060b02141010003018010304059115a51100400003903801c08022100054148907a07406414170004001c43d00b030020b0502480b0100090105203000c514291420074446010000b40301d0003003142101103201001039029000711111807804490140d503410541c035140d8020741080e50152000810b41c1c00312800e50134094401d600d40b10409004100e24452107500b00e6100e03035402c900303d80102501034200e1405043c2d040d118064481c0e1000b9005d50302e0b22502d01c604a4 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 253765872 1250 253764622 253764631
    0xf050606090a0315090b070503010303090e07050405090a06030605130606090e1c050909010b0d050a2d060312020102031b031017031b01060f05090105030d0c03020a120c0b 75
    0x9410030000c00709580c0c0c809040c0400c0341c0e0301c00c0c04409020320580702c20004150760407003d4655042c9030304110001c0d07030001c0254140d0340700c0d032520701c841c0e6150302d000c101d6840210313824404104100824040e5190000840c1c4c0d0010b105600420100e44a955500c1a80c0040e03540c0e1402a207451154802c01440b409248040c200b2220208010900c4152065036130b2109407a100c8094040c0140614461048080b10103c440241c00c40c1d0995940304c103000e1840d8480c003007540c0c0d82c034588808203070488a07601a0050800c1300c00b00d281000c5000030700e041c00b0b807c2d040b51a821003690303a4200000094103c60325181a55542d000142c49141450000c1c4070500400d140415017a000c00c02c00101e0b44d0b82c2082002521100c20302036008a42c0b204200745944950132030590700c0c3c0a171048031004550150410000c0d560b07101e84441031750396184244080b411003802602c0e07141e0044042001168400e05034040720500901c11030307803802d0542d162500348920021556000899000a0100b405650079039030b50003 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 253767122 1250 253765872 253765879
    0xe0f010908030a06081501050105090a0812041d070f11250503121612030e060406060305190314030a090206040308041a07150905030d0218040609020403080316031b030f0506 76
    0x1030403441b200b0010003081401503e0501c5004612004107885800c1a000585181c1003214000c905070003c00305250001c0c801c0c50412640303886500b2a01c218144020300911107515034001494152006448410721117168081d148a540f040114140e0680f4058841400700d50309980404c1c18a01413500b4034039081c000349807030b030000c020695030300702c00314002c3d070855401c40e00c102403108510400314040d2400c1205640d1510030381060000348000da6015100b100d2141003140e65050072402d01c840034181c3c003c40a0085902407102e50845c00c141001181c0c850130300440007621100960006c0c0e07107034000382c00644480101050a00c1000e200f10b04801140c00c1c807900207818030740c2d039646000303c00b10801d00f00d85465844146040c1008007c03c02d403071002250074010364644400154020b040700404035081d11550501a0028400d1032600c01c0701c041d41d400518003131a50340d82d2240d422030a58911440410560303524640c003544c1580f02e641d1415007201c6d030b40c003042d00e00c0714400f01000e440020f48003a20 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 253768372 1250 253767122 253767133
    0x11010c0503090d300204030b0103050c01030b0a080d05130b03070c0302150f0c09010309081603090e01320414090c1801050f04240806010806010b0306040e0f010908030a0608 76
    0x3030701c1362000b01080c07103030301040d02c2c3c101c4103420480d8501034055640010182c000010021041042c04202859811000e076800c0181100b08410460344506910904881d508001c9014650341d220720020025a4800b0341a800d941d6600c6001240c150310488141d00051001d03030915080648c107110f20045c3c40d40d01d5050804074241a070328480810005400c1d00c1005200143da19283d1b4042d03000b00d410135800900450b1a4004100c0e2409103d1100d032003103002540c41080810440002800d0f0341c1680d0f050b126140601030720390894000a0070032070b60b0030740320310303214207070b40d03229900e5014507103000c0003441c086a12410603c7c105e40c039007242031000b1841841c4529407603809040380365290f8110703501250048110300200b030110f8010312444102c10007884d01e004d10503481c0c2c51054018006c54036586c084840c140eaa402e05907440781e1082c0145c50f8001c00800120780c1c03614140c2c02400100c2e000800340c440100c13400900c5800c49003000070071101200e0110400095001ea03100b000700618620b4003400 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 253769622 1250 253768372 253768397
    0x81f05010e0621060a0e010c050c0a1211060408040f0e060f0915060c21070f2006030907150e090c0a090b0a0203040e1e1611010c0503090d 61
    0x11850000342901c3c0600d049030840180c0c3d10000d0398526119040c0000e4607094105000c045003d04148200c0038007660800c64061041031103202140c0b100340340784001e0407000c1610768843e05402d41142142c01000400b506000c0782c1ca0301408190300030b5100710340040c0d4540c40d0084d181c419407811b50001801010034010040691240400c111000c0780c100d4950b0429500c0701c580c292100c2024030f050750025404a1096006100000c2c0c1d00d4944022010b04824000e8100f034164182c801e0790b0004025052040c1e558000403015080050805110105100c1c001442008540250000c580d0460b40364403450003000075505090f5114804001481c00c0202e030144c6102041640d580a40700c250b01410002e4003600080c1704041d01809402001c5603959200c0b200e4030000d40d40d812500900d0480b1320440d012603590f034171404461620503036440190308282d48428420610b00140c020b00300600082c01159480f0b80b01c01e01c00c80b6202c914984034213403a070829008552174001d040c0d000201b03200301d100004 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 253770872 1250 253769622 253769639
    0x31c05041b05061204081c0e0c1917071802210702120f040f060f081e04061d030d1d1209090403020708100f0510050a170106030c081f0501 61
    0x40b60860707002420400c00ea00c41b4a442c0c06517200b408818428100c0440c8034590300b000d16004008600301c0e01080b41c402d80e0f40c4408200c8010381c01e86e00003544000c0080b04110446403078017450589114a030584e40300380d99800c0501504004400d03040c1c0500e6002451100400c130440d548041d00c260311444100500c1d28040295032411b445880109400b004030750112810041401c9034090b114659044645035038840021740202400c0c503000c0045032108000074003041820003807044240509006500907125078640800600c04480d0080484489820b590581c0500300020300c10740d040d1180c00540c01b54008400c2c070207a5160448040c043c2c00080c044619140b08100350307035046000319140c3d003154940e0700d4260314015007603001c0882400340c0020b040500d0600d502c942c02840440d90140210390326900f1a5a01111a009095000c030400b10148112800b1103c503c070361000c6000000745803512a19601c1c51050035174030055140e44084d1100c0e50312210082010018402400180400e5042603010f = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 253772122 1250 253770872 253770877
    0x7020d0f0c021f02070608010e0903090906060909181002122710060905011203080a20040b04050f03061005060d021b0607090b0a02060a090203031c05041b0506 70
    0x190100101e0000c010155558014100041111032446488a50161001075210110340c0700d1040803550000000030321040c210080e61040c5a4600998908991381d810403200d100040c01c0c4039040138080c800814217894072080280207140b00d00340041c56810b180070640c51b01c040f035140c501000b4010b2002d5103804c1c01078a040c1342c00c4480c840a001c0840c84120100325100900450100c15108401c40514021580d601410030b803002e4200c1400700c0d0307807503070544100078046c10b00050000d60140006111a0a190b00255000050b0f8101e001414902504015250001d80200c24840d400007000c124500d05002c1d04004a0800c0d1c010302041e1806802c1d8800c1004144103c502032140041d0712001c00c885641118102c1c1c0780b04030105a101ca10818031a03844004031070020100741170920115009255006640181c040380c2c0c01480c107680d0b403c12020140120b0354003240c0610041c400004d5030b0400b4904045100318010000032145440d08210840707452141c2941c410b070710068001e04c880c2d00e0709401c = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 253773372 1250 253772122 253772147
    0x604140409020f0d0803060a0b030105010c120e1315060305060604090203190f090311060c0d021c050108060a050c07030e010503060310060b130e07091a040f060c050607020d 76
    0x10009031075805070000c182e12194200e04144d0140313403c0140b408120340350b4007450080405840111900c0e0b00c0b0f04116405100070701509001c6040b8506141c0010b00800c645685080d080ca0b01a00c0c0c0f61001010a00c0b804070b0741c000c0d00c4540e4441c1d540801c402e9888026030000c1c1018502442130b41050404074100e132061740a4a01d2094000002654080003460740000303102240a04009280c8500c02440051150701c00840028001d986115100d060002c4c0c41d138003030801400210700d8140355414a0380203501000805040d001c0d00740e4211101d00392441200d009003015000782c2018602000480200c40e0000e00400c4090420300110000ca03032b0000d00d001d913145081c2013207a5662184000a850b0603030b100c040400285c101900880c903002918040c0070040d841024055541d500c4035030400380c080e002c5400d04001050380d8020806e0007030040c90080c0f103200401400b8a419180d20a601000b0429081000410043d8004408000d02017101e60340c0017549102034100d01c00b03d45402030200c00b6144 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 253774622 1250 253773372 253773379
    0xf060c0c0c0d11010c05030f04090501030b0a15051c05030f1c09030f081509010f0614190509191211011704030315170d02060601020d0509150c010e0f0c060414 70
    0x174440010030108008a45e0051101c0d20070584803903490020f100600300c00d0008488130b00c03c5002003407240c0954003681c0fa1080910961001841c10314040c0100d5080301e41609546115083e0f120f400304505100521042d0806034850340c5c0d580100301041c00e0140074200200c001840d181c036420210b03910041e41c0e14517458134642121580c4030600180040c0c4203100c600c03517110a08200015401040c803010104a40060325190180310002010680303601520707001078199401107080032585885034009042070040141904d103242488210b80505481a8121010005e0548002003e0103070001c4d41200084091800f5030102e01084000c0c40d101c440034000034141030700c0c2c40c1e03a406c0b000c3c4a00040d0000d091003100c000c0c0d40f59880e241da2503680d12042c0c0c45501601a00011414a51000c1004000510a61521403038142d410052020301620005e48008181003800255105c500070300424040346600c50042c00321b82040c1c00c3c1d9506016914841d2441440100010448114039240004403c00c04a = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 253775872 1250 253774622 253774637
    0xd050403080c030c041509150804060605040b1309020d08030f04020f0a080d0f0201020d1a0406050a0f030b070509120c09091b06070c0801020a170105090103150e0f060c0c0c0d1101 79
    0x6942611f4006554001c25408018036003070400d02507120f405140b056001302c130103105190f560380c14001284c03005101c442c3c2141301da402ca00d401c09070300d81100400510180a17000f03413403081e441e40c20850300250760304e56030720122000f8070080d450000d01d1030705059022100f141002c5d00c1c203000c0350340e2501c07d24508410301000180320700c5154001c2d41990300707000d100441481b40880d6141807510262070400142e201c0c030319002c03002c43e9500300110408165541c486140e400d1a086403a07501c034914006102004000040210001640320444082e601000c0180140a00d214820801c280700390700400e03880c07440c0d004200840a0715a5100c03511501c0b0015134045984003002d00388200d100e021508002180d600000b00e140305280d0010440409206c0c089070310300641d03221420001074009c00c0c0b202401c80b08400d44412a4040c103030740306101e508100e00c01c8030f070283e83c8264100d04203203040f1400c001c0044041003481d08118188038802c00c000c011280d610305c690955071458589101c0a0683c1d0420200 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 253776978 1106 253775872 253775909
    0xf12040803040b030a0209270f0f06130f06120210030207051b0402070f030201020315040e070611122d0306090609060f04020d050403080c030c04 64
    0x514001e545020b2038140d401000c2e40001c0e0442d07185076801c12250030103907544052198091040302410000320700c4828008010403004004c4000620f200d030401207144481e0a005d40c1c044004c55010314a140c1d404220401070103001c80d00800146042c1010a065100f03030a01841c4a1085910601c0c0340300030601182a03010303042c0010710561015421420307407000c5e08038041c0443c0014000600f0210b6035220608080c1c4601e90580c0035035400000c1c41404100c0350095800004281c034240a800304282120356580c140f40705010802152071101c070031812052001005002403800c4258880c03810212101c03806601680f1400050544c041820443c00094280c901c9000000c00060407941c6240a101c070301d0f08010082d03075208801c50750002c1d4995440c80a000189890b420002e545c1c0707418507014000e00340150015040450904c02c01c2090305038102190140c420250500360714054 = true := by decide +kernel

theorem cover : BRFrame.Cov 253597122 253776978 := by
  have h0 := BRFrame.cov_init 253597122
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253597122 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253597122 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253597122 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253597122 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253597122 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253597122 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253597122 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253597122 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253597122 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253597122 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253597122 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253597122 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253597122 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253597122 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253597122 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253597122 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253597122 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253597122 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253597122 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253597122 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253597122 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253597122 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253597122 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253597122 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253597122 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253597122 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253597122 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253597122 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253597122 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253597122 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253597122 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253597122 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253597122 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253597122 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253597122 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253597122 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253597122 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253597122 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253597122 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253597122 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253597122 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253597122 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253597122 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253597122 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253597122 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253597122 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253597122 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253597122 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253597122 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253597122 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253597122 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253597122 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253597122 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253597122 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253597122 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253597122 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253597122 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253597122 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253597122 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253597122 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253597122 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253597122 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253597122 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253597122 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253597122 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253597122 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253597122 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253597122 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253597122 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253597122 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253597122 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253597122 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253597122 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253597122 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253597122 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253597122 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253597122 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253597122 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253597122 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253597122 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253597122 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253597122 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253597122 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253597122 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253597122 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253597122 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253597122 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253597122 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253597122 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253597122 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253597122 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253597122 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253597122 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253597122 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253597122 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253597122 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253597122 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253597122 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253597122 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253597122 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253597122 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253597122 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253597122 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253597122 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253597122 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253597122 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253597122 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253597122 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253597122 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253597122 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253597122 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253597122 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253597122 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253597122 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253597122 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253597122 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253597122 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253597122 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253597122 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253597122 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253597122 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253597122 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253597122 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253597122 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253597122 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253597122 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253597122 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253597122 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253597122 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253597122 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253597122 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253597122 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253597122 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253597122 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253597122 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253597122 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253597122 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253597122 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253597122 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253597122 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253597122 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253597122 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253597122 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253597122 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 253597122 ≤ n) (h2 : n < 253776978) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
