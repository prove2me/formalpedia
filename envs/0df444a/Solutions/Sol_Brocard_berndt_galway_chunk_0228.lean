-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0228
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T18:36:03.824387+00:00
-- url     : https://prove2.me/submissions/7412b6d6-5c6b-4e03-a36d-7a5cbfac4521

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 40827342 ≤ n < 41007198 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 40828592 1250 40827342 40827359
    0x40912021203040f03050f0409050a0b040b060c07140301020f0304030c02010f0f0804060906060801060303030b100c031b020406050414090d0504050a09020d0e070e090105060402090607060e0f07090c0207 89
    0x4a200c0e0744c1040040d840c141240d40e0480f02ca03070121292a142c40c03418000800c240b850b500605004201214002c1003402c1030740e00f040101d070180c054a512648003000344116115001c1a0501140c2100140e40000c047e603901290183c0301c0d2000000340c09070000108800c03d1780150403494058000e030303150340300c036502c2190507502c482d031400c030000204400384001000216a9004030405500c2150040381a51340e40c00d2003030a45440b6001100440e0700e841c20706c061030402c480715038104401c070701d007401400f0b4464401804207420303401e0420280031710903103020540d12103401c440c004081c00380040151804076001d5140f204c000b540c0a034060f014581502c900320784208152000d89600034003041a451901d0b802d54001e40c005680005059243c4841090008040c84140c0050603c00c25000780c0b031a00e0041c050855030001d1100d48683e2046c0103000030f0f6200c2100362811903522080004284802c003000f185410184400000c040c481c240f80840d079041d6540140c1d0f0b0810b15030302250401034413000e44 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 40829842 1250 40828592 40828597
    0xa030c060f08090d05040308030402030c040c020a050609030412081303050d030b04140903030c0c070e0705030106080705030103050c012601082a0303030a09020105040f080303160201090201020607030f02090409120212 95
    0x1c800045c0080c0418004a00c0b90070095400c0b034401400c40d440303075003140003003000d4484c840002000350b0403520184051010900c1340c2d1341d11a80c0c00d00690320302400e0516048511156250142024a0211b0803000075100061000003964000d03040354400d00b00e40380000d015040102c0c01c4c078061814503004008144460740118007030410b6802440c10f590710040b9800f140c1c2c00090b216030306840b0340200052000c3c125425103000740c042d0b07921070707075251704096000d0001400904610100101040108046803010640c1c3d160081c09192016414444441c0c60b00041940c4018040491500b000051000e4001071070154241c00b070354203c55004840d41aa03a403d00d2255121905a0003c00024041d280c1c02c0c0d110300c3c1c0b07940c4141040c500341500c0b040c0d44020744400c1c1d004a5015480003040c085503116011007500c0446c0326200a220243e22540000e48840000e03200e1401e1640b01d100030303084511643c040d1041c89001030310400c80d14016040c1054554100e00480000d4040d80001c2c010f032a07450b404 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 40831092 1250 40829842 40829863
    0x6130821090a1a0d060305060402010e12030d1a1002010603020f010507080301030204090507030b090606010921060b0103110705010204031a090a080901050f03010806090709020415030b0a030c060f0809 88
    0xc2c282c1114a0940f50f1800c28034045454200100200716400aa903032070701c14400514090002010145403501c009418080d000b90b0700c1d8455282181201c803408030010844406400701c103000709511a0198074004680e810900c080c1d4005c0044c81803014041d41584601c00310b0340200c54118820304580010340d45481481009070034120100014000750809401504201d0310840860703260564a031211420180d0a5503845c005401000c10b0020941e80920400c010b0040380415940341c4102d2910140740d8038414600908141d211807100010fa0f000e540f2500300c0c040402c86041d40d40c1c0203850054000e40c0203000403100f02aa800c01c090f601070142400902c20700c00d0b8030003040011030700c0c0c40d6007105400002c44030b81040010440079042c01d40c560041d500a051007001011241040d4003440d081c0b2038141c02c00d250440c810301c000c000070001004810052207036418005407841d0301c0c00100310f021845400c0174012070080040092100d0748601c0e80c400648840e59924041c3d10b61605280d2230f4852650b = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 40832342 1250 40831092 40831099
    0x1020304050423100e0f060616060b06030a02071406060a120501090218040303050a09020901050f0612070512010602031602010e060903010603052103090703110613082109 75
    0xc288940d00b09940300300415200420010111070840200f00503c2104803028062410540010002d1070108408a070300144490700004091030b142000c00c83e103018490300303400d041c0c0909244806001007a40400216030014001655038a030084a04000c0d6004110849619000881768003408501147c094083c0b0001004900010726107001c5000845102905136400c0d5030320280440140d0340d03103810010811007000c81c642c00d0f24190a0203030407540300403d10b0340741e207041c41240f400607501e80700c805056440455400c80d5980d0034002242460080081e83c14162078400c040c0031f01f1b160014043d14031448025691811aa02d501c0c00b00e8990141056040e50701000c000004010340c003541030010319110203060507080c8001c4600003400d50380303154810b603080d4101d542030520480c2d00d158100304100004a0f1189036051016500356980c1e8148000b41a4005e0045038a040750b440c3c03401c940000404000d07000d1040e4840382500e44801c0d03245920100c042480d5800031002d4000029038407c450000d = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 40833592 1250 40832342 40832347
    0xf0f020c0c180c070c0b030405370b07020703021302090906010906020601030b06060f0a0f0216030b010b0a050708040305070503060f070e0108100515071703010305030a05070302150106121406010203 87
    0x2200f954541c0e41019104071041c145007880810451109405584200c0c02a40204000c500c08640c0042001c620b24403038840542c070a050080500078011844200e9501040c815007690b2032000480c1060103d41009502a5009a488451540320380203010760010480d441074891300d8220041da03030901c0512035440035030042c0004002003000301c0d48103503001d0000382c0020700d01381d40d40c0808001540720702501c50206200019100905604000c4075054020b004007a059440c21078940c030301810310511070f01d640b80d003000132b804101a2061095521040e441040107888584a01c0c1083c2c031224107018090180c81a03000085107445274042d845d0003030043c2d84402c1c90720891000119030a450040208582480c02040052240c440c141c0402c1c0101252501a45034a902d151901081b0560001d1075600d580a1005101161010048440d0074815080ca070303540d0061480e00303900304482c00010700c01c0d5800c085c00010380c080d0480d9694904183d80f2600700031039001002d050700c03e024243c03a694010b030f005 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 40834842 1250 40833592 40833601
    0x3020108040605130803040302060901060503241302060c0709050a0c08070f090302090702010b010e0607050d05030a110a03060311120d0e040219030902030f0a0803040f060f0f020c0c18 81
    0x41d5010b0380d00402d804c45081c07803d4446440d503040c2ca5005032412401640940100501e1460070311661000d050128007425401440da080000c8219a07030101200d604168030201d4409890303020400c03181907002d001c5507180d05041e90040d4803840f1901c610301c15141800c001585607400b910402c10824003948511510f9150320b0002c6034035003c030304101818401c0c0d0100202c0544d0700c01c010203200c1e07603113540040752901c01e400005100c081c645000c1c0340190302c14440080040c82c04281035640d034980340340a54907681c0b040403c030007030301a40c90001c502080c0000c16640310365044e04254103407402540d8010000c00d20005025103070084600c0c050164002045108210340708402594014070300400142c01c101398001164441220740c001ca0b030204e59a10000e0b0118241413217030510310751040000d00441c940c0d6483c0e0b81c0982c031008100810025051080f002000303103540c01a0000c40001100b00440e400d001c0d2414020b6000c1c0010000f82d1082d18007403802d900d0a000c5003c0100e4007001e00d12029101c = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 40836092 1250 40834842 40834853
    0x20304020a0b0a03020c0f0102041a0306090115091d01030b0619060503060d140f0609060705030f07090b120105011d0a0306090f0f080d0501090614151303060203010317040302010804 80
    0xf281e0502002c0517020000c035540040100078124440205e00c00050b0344074a40130701e4054100d0036078034016a01000b401003000d10303035940841604440052000211814403413204132928042c0e504620b98065032203a181401e42409901c15050b01d01c05c1c22410300700d843d1a0104580d000b48890800b40d1152841414400c031842000a103820940107000308070311041a60300e18445452040b00018030f40c0c8901030503d4243c6080108030b070802c8041c4040d000c141006107000f0003511004041e42c3d4181c110401080300140700e00205030042c408103144070317180d0f03511010028803802c0a00c2840d002850014611010303150504007000450401014210a9483d5640d041c001d40080785042c0c844005486c1040080741000c0c661200e5640308015003030780c1e1075a8907488000c40b02d040e04010a80b40c40c0070810f1081e10803500303040100403400ca807010400d04544040d4030091141d10740e400c006560002d000000c01520360050b6059038814034801c528070701c0d202940411400f56202c003900144540d40400c02007271 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 40837342 1250 40836092 40836097
    0x20c0f030a030c020301060504020c0319050307081503070914090607030e0a0b040c1a030a110703270308130f08060402010504060c080403061b12060b0d110909040804030b010603020304020a0b 84
    0x4d2014001003030469130342000404903040099580107982001400c4640c3c0c5840000300500d1040c41d0400a0840c00c09140040c0510f07001010440b10014512034000c580d44c0401c48031004001c0071105000f500f09420800d41c61110a450000c01807240b07501240d0168000d00802c2c201a521500a00101c4030680703406003d105c01a10a07205c400350840046074214030340350601a015101d1158940c4c81c140001e82904403086070301c0303040d0f44000600030100041c2d4072030707e00c2040c07440e02c8240c1106556000302c0c50440503910340c0010580c1c04d00180403410b000c2e2048405d01150800903000040715507034030001e0380fa180c00715030090000d50308000510840c0e01415488113070034000c2c0a200d0500b80c4070703a00c00f01160000c02d0800e000d610a1034a042281d548104812815500480b06100c01d07860443c4505060041400c04044e640d1a1000c000c00c42d808441510740c8840c0051035520b42d410581419151640705010a07260789075424008070340f8078040d000700e0740160350103031210440920b0105000e00303d4 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 40838592 1250 40837342 40837367
    0xa03050d0e06040b04060201020304030207061704060509011b02160e040834050109060e0109030e04020c0309030a151118040218060304140706090608221e03020c0f030a03 75
    0x3d0001085a242400c00351000e003041d50001652414503040280c03408400d0381c4524100b107042c40c1d01c11511407030440c14035003195001e036011450791100c000e203501400d001c520102503100d079043c0e0710042990010300c91030054075529481203103644505508400c0d02d82100d002c0d210030b41c1003280d03112000000e107254a080100d010728550b51115400211111044004180c0d0960f4507590f502c01130051510845050105100003001502031075a0b01801c01881040b840748a954007140040601c0720074000c0324803e0764001c003990490324a070b2415142d0500f08031280d081461900101e203440d88030b51005c8850f00c220180c0c6030310b200c0d1003481c20440651f0125902b0451080010a040c0c00354903182d0155000b24419000340e000500405001854550309501407800c200d8240800c000844e0000b080580091007211224184020350303070a225403007018038005010589000c0510b042a0595a111100612030ba003560820b418603020041d43d202c0756076009901d50009400304001074040d030b0303051070744 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 40839842 1250 40838592 40838599
    0x90a1a0d052506081006021024080609160302012007090f0207030e0a0b0a03090203070506030112120201050105130504050f03040602070501110d080c030a09080708040608060a03050d0e 81
    0x5801c01c140140c02d0302c1d0500c030710780c0c580102800420b212058104055a500c10007110f02e19a030107281c0b0030020740e00d040501c0c0e90101e841c4d0360506030240c0514510a801c0c0455035150141d41d141d981c50348507130b031041e0441d1b0304130207806002c0728248d18103451041c900c02c03070b80c05a585000e506207504130120401030411301c40c00c062107007060015040c4441d0040000d1190701980060300e5030f505081c064103006400c803000e407140200c03005c2840100600d20541d61902014640041c040e50740348017180c60500d00d034100308e0307205001000002eaa1a070302c0c0150300026200d130f82c074450340310400003050f401c0e03035400c3c001c842d48142201405a0512600d43c0300c0360b4030500030012030703480344851102d060440e802a044240180c001440500c825600220317042c0803145804000c00c145201c4207002024004080c181169091000001c1101020303141c10039408680c10003002a51810f0520f808410395000c1c4c07248801003481c02d030005180b842c0c1354080804481d040009840c1018071140704844000d03404850550 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 40841092 1250 40839842 40839853
    0x9020c060c0f0705071202090604090b0a0f0e0a0503041a030103030206071b0b0103080301090c110601030f0302150a090c08030702030c10032c010605150405010c0f0602031302090a1a0d05 82
    0x404c1080207000010540b084c0c08200510303981c014482500030041125009605210b00c0c00c0c0050071040300c19503c556403000000b148040c102c0c2143c090b00c0c4040c0344010381e2241000040900c4404001032045640081900b00502d016401010880c0401d01c000b82c00341c0c00c1400050031403801030fa1015a2500c811646138032269456031030681141d0283c000b65042d038070201c01070209900610500d84454800e0600e0804054440690703944d841c0d050100502e2407544010950800d4000c01000714541042e10b24000d1300d203810310006004020003041580ca00500500c0050a51008422929403d4014019010a001440902c034600101c52040703002c2541d694040314840300100b082c126007178030b108002030440d0b24542c201400d440d2540c01c210302c01c40d00b1030400045ca172107800455080311002c0c28200f850500a082c01649003108103401f0b4811400082000040006445950308040c401c8a1402058590520000845690980d82c600710032041c681c81c80302e0310b0034070074000b04103100b03c04441 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 40842342 1250 40841092 40841107
    0x30617030f1804090308010e07180302060706111b010c0806010f031d07030303050a0b0f0105040303030509030405060f1308120708031008010e0303070311090109033002070302090109020c060c0f 85
    0xf02120324203041074000480080043c408245400300442c2c00228500d0801041e40540310252030300e00c03051000134480d0100240035810070000d600000e001c20703403200505484010354041d201c1420700440d0101142c1d4030b4400c008030498000c15004c1d01410060b503131041a0210fa060541c000c0c04516070081400341c840c52440c5401c0300800c1460041c522940e00803840d030426202280550b15000c480d58402c00050901e40742c2c6981c0b0400b5039085a80514001c80c072a01c5222801c0d0440c4904c1c2c00c240c1c0c01042c000703010080444030800800b00d102242c6241c03080c1c42d41d074003400c03a2116010041070700c2d41a030800910b0003049151002d1074100e0051000da10546075215040c2c0e00b182e4041e408500ea40d00040200f00140d1f4140c8030300c11503080103151b05031600b0341c1e0000080c01d01d01d503804010705510070b100c9000c407403450150088800c0800c0a0904035440c10040d8040d603587c2807440200e200e001c1c01000805c901d902030081c0d42440c0c42040040038140c031071260300f02d4683c004d40b8400d00452001c0c01510b = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 40843592 1250 40842342 40842349
    0x7050301061503061401080601050f07300e0a0911040503030307180905070e01030911101e0201060f0501080702120301030807030f08100311010207030b1501030617030f18 75
    0x1d0014844002015064081c00c035010301541d520b5446000c40800c00c0302c044400d070360000c04095001e582440c00e10b50b0f40303005aa14541500602c503000e0103440c200d281010301214940c42a00f100c505020700c0b952054145081198075102c010b041c0c580010141c2820010344c1480d03001502d00c1200155641d0601d525075010918640045500000080300f80280380716000340092040b02810200b0000e0140349001c0f90090070140300034410604040c0d8035000d00003482201d04040c429854001d224054505244c440200324038030b0307017050300344401d6102b105c80f40d014014401c1d00c0c116148900c10070480b40c9413000560b2144c00003080401540035801c5003980d180840750046019600c152045501d64102d030800a001100061101c01407000103001d101454003100e685034104ca611400e5500d0364201030004034280085540020030400d5a0414800c05049440d1800e5036500280c1c2d040241d155101312100411161000b4030000e504108548008048408000c05815100d0480e2400040d41000071 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 40844842 1250 40843592 40843601
    0x603010c0212030a0915020414030f07030201390210181208040b030702100f090b1306020d02070b060301110304020915010903080a17010905060a1202130207051605010c0b0a05040507050301 83
    0x20071b040d940003c0c140020299010013480c0501c044d0020260310340040034082d40c542042c08040e05024000e400300340501c0101c503a00100d440284411a4080c1000054071105414880b04038410072203002184000d911440c00042c1e001c0c03d090940c031400b443e10170700d0030f8540d92a010a64400c40100f1010a240701040011740c00f0352442e500800c46260b034249203400710b941c000300c0f400d142801c02d1124030200b400c0c9004d103500807079500040d0300345090342e24100c0020310941e50301d01101c0d0f001003031007418803c100c90040e101e00b10540c020320142c0180c40340448544812107001398041041c40c04590000c60b02e00740050480300c18108802c0d06a101e0701d6010454204032000c20010f544c0b102c5490384809a817003694010308013000184254101840004c1c440700e401c0c081c4001e043e4000e03c0d80020755407141004a03111000709030442d0f540e041c82c10216100d00152400c40141d8024410009055108120b0540c030141c200fa19001c191310303446002000381c680a0000d448038840d4620100701a41c00b0b126 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 40846092 1250 40844842 40844873
    0x20a030309080601090b131a0405010609090f0606020322050303030103080a0219050c01030902010507020612042d0b13060f06080c04020c0304090510030c0312080603010c0212030a09 80
    0x1074581c41c0502d0b00c0409440c1c504160496090301d42012041889600c0c0c66031a880050550007000c20201c54034840807e64204640045074010b04050001510a402c0004081500c00188090000140002c94141690b01d41d104503001607004100c07041d00c81007003024828014107803640e032036003895403038000a01d5038000380c1055914400005440507400d070100031841d031105030580c000d00400102e0b160251928050320115041c1078544102400316882402200c05640e4002c013a2130301e41c03180c103541020b005003c842c201e41c40e07a000130305a10080740040c1d0f0041048461011040228400d40e02c1c8510180c01412180e40503200c501d001c80050014000c0780c2189030b6414002503130600e8031139071914184842d01205e000d540b04000c2000078840110494080c3c8084960200e05600d0f95400c40902002552006c0c040d1014000c01001300308840c840000c10820690720780c540c1d41c0740c5a0803d403c1798018000200944d00402481011a148002a580c0400461000500d180d12900c521754401c02044c03 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 40847342 1250 40846092 40846097
    0x5040b060c2a090601140f130f080d080f150f0d0f020108010b120a11070507060306090506090108030304020405040201020c031b120f030d0506040902040c020c15250807020a0303 78
    0x20b00d070019010b40841007082010483d40e803001d81c200207002070802511100c0500341800d001424017007140e50b503000c60f2802403141d420703000a1680c80424011881c0307a4003400021740102c01401015901c984007c50080c210383c010301c10b0743d40796650400001713038040844940040c1d13501d940d05102da803242e008420700b50090070b8540c40140d16100041c0000b00507084148140c4c0140136101410401c101c203a5400003034040000b50b0505400c510300d805019242005015100350000481c18a906403c12030484208490510071a107e0380200303c17400000740a490701c0c9600500008001d072405422403504940180141c44543c0c0110380805d00b044c01150704c140d001501203500714498208060924003800c0381c0e0000e0081212078210450312842050f07654400b0603101c0c00424056510369001e550110b0b8001c1007040303450b0100c17002944440b08000124451041c40da0b0302c600c4401c8010446040340e0254802c0460101d0222105000c000b5204040c3c400c040103002440c0103032103142c60080a1800398 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 40848592 1250 40847342 40847383
    0x50a090518090607020d02100b0a170304060816050a050d061a04051815100e131b090605030106201506030609010c0e010e131a03100b0a05040b060c 65
    0x791800340f9002024000030f08541c011664003402d03039030105418400107d502c4000c500d6203d4400025070317001e40b64000c6ca031100042e0960101001c000001881140c3d103c4d119a1110742c0c40212541e80700e070000c804100428000c00940b1401c62040009081c0e110440c2000520191180000400340003c5015290308030800103045c0961700d0600d6100002aa9a0039030701c0301c62505c030810003141d60b01f81d003015000d4031170b00840320403041c02000207440d015005000809030101c006c40603400342001c8180d05428114178400220032074030461511096543c5da49842c6d2a69185c883c086440a920b5050021102044560079440e24410300217030181c1d82c05100083c4560502d03d0403d814607901400c142034980c58050840501508441406000704003401c00c4400d206210001c81e40e085400c40004000c140740009840d416298880c880c210240160700b19821122412002021982c1411440d903000e440906e00b00420318094102d102600f0300600014249600308282d1444c0c10780604a00a0700808d0 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 40849842 1250 40848592 40848601
    0x90f0705100516030e0f0f0d11180f01030c060c020d0b060a030501020f0d060e13121205040308010305060c12060609061201030308010306050a05070c0204050603010b030f06010f0803120106050a090518 88
    0x400103102683d1b821078804d1201c003101c5000421070302c44d00d00000c02c110b108041c10305082c1d071503003214040c0344020702a80110b403508246020150000340022542c8115244022407250b00c21400e02034169405402d4815845041c5ca41d4000c15a0043c48680e00640110b00407000030000c0c00500310b40100e500d1101e494600e402040c80c160b0f01c02d44c002c00380c240408820011020f82e02c1e40100f030a15008008000d0b1115010800c4449020040b8084c2855040100b80410581d00c00c01c2c0074101c0380540191015901c519200038032500c10f04c0440b5005000e03440c0030815a20b0490300030706042400034030003842c3c104c0200114a50a100744d00580c0170410400040061100c00e01a090f030109284d40208810b103001c0b60b0240c0a40d48400010f4025503440300054026202584441a981001011a06041d00ca001e00950b107400034000d00c2c915101e121800200004004151285291402d0b61081c10342c0c20300700c0c1207070541c0000c000c1c4c104020802d0b100040e243c0b10032b8032120f4180d8601c03030f0079a0b070391a0 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 40851092 1250 40849842 40849849
    0x19020703020a0f0507122906130903030227040c0305070504060810030f0804080105010501090b071b030203032703010507021f060915030501140411010c080c01020a02030909090f0705100516030e 85
    0x581120703111f03840d244001c011055882d401e101440c3e215a03000050030041c030341001c0b4000e0050300d601c3c0d6409da5000032803803580c1e00b6006002d00a1081228240040c04d150780b0201e054a01c2920ae0502240c002d00003488601e018850a5900400c94a102d0904503541c0d120f60754202c03e50744080d2411900040e0900c030120f400c3c05402d01401007030030041d03019403a10744800e4441c450100060b12107040003010700b1820b00030103811070085400401b01c03512188490360254001e40f854247d915080400340d00d0181c0d90a044c010341e80720b000039401404d4218001c10640c0300c002500c0111024070b0342d8036070001c04c0782080e40c4a0034090300c000c0040c510710f00b42149080e42c2101d085030101142003a0f131808200003d4480b078404501c83e0307000e20300790f8a10322003480c00c1c0e0341601803030b5581d000950002ca4014801540003016020200040b241e140c100e0310340c06040ca480b52002007441d0300350b070003590080c8542e040030f08220700d4030402480c1c040d03d05640010040c401c4600c0c07080460000d4100300b41075100d0319 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 40852342 1250 40851092 40851143
    0x10c02102703050a0830150409050d05071a0412082401050c07030501020301120b1b09040c0909090f02030601090b010903020f01020c0a0e19020703020a0f050712 71
    0x110070304a001d1001d04507141d4035a20300d01243d000b01443c0f40081c00c4c81c480d588010a4040c0c1e00781d101c0c1e411804485800f000c03202203004480c001440d02c448020048035140600600743c00e42e801002612940501034421105940030070403d42d015040345d0074240d0003940c81c01c500c501c560b014001031403d00003040c200410850740035103025025003c4404448072192085030341e10f004c0c0b1090818698070194481810300348140c2d6030014059510101c00040e00d601681e214500305840b40da00c4c0071150360303a030305001d06403c80c0e00a0001c640d0021300c08405a418254001002c941c403d040c10316020342d6032000502525842901140c2c0d100340c2d544031070218101085901c1c00f4107001c000511101d0340345030008101e0800c0344401b038414508200c1c0100720381d0083c0041c0344441806001d54802989422905804d01c2040c3c605c6000d0500c0c816054580c04c0340c61007520700c00c581c1a0301801d14003c0c141c49800300c0c040b50102c155403500414100207400307582c040001c4040381c414181301c50a107554001028018 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 40853592 1250 40852342 40852397
    0x50405010b0d150b1c03110f0706020604060903090e040303090302120a140304060f050106210501050105120612010606200a030206041202010b0913050c0a050915010c0210 75
    0xd44050442c8400502c46202c0c3e80c00c0010089000035000005400240c54410700440014000e807250700d2140034181d2019a058025050a0032a501c3e01e200c610a80d41e0f4900510580e0016080507011034002542900a03031007003402881d0402000d03444144409482000b41c5007140481d5031901c0c030071308140d014002d80760313001c9180700000c0c1002c6990002405132420700d03166103c2c040000001404002d555030207201c0c9403030301000408c111340c0c690390050300f030a180f840c40e005a1540c0c140b032140d04070982c0c060306050303c0301a5070702400c0040083c250b49103108060001540020400d00c3d440c0b01c1542441010010203050792020120001c6c180bc8039920400d0521640c00c3c1e030444094a40880e0b000524030740c10a91040d03400c06070020842c0100e004201306846240d01c509070000340100c0280c3c0b2021640c44601400582d0703800041c3c001000902c0d80c8500c00c40b40c00001c22800241c0c02e003510800c4600c0454181048429059554001041d02040c0d180c41c80c045242600c0c400c2aa140c02641c683c040e = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 40854842 1250 40853592 40853599
    0x218010f030902060906160b010e0906010e1009050408090405090303100504110f070309170303040204050108032b09060203010b130803180f01031e05040b070201020f16030e060c01050405010b 84
    0x440b000f034000c11824401c0c0d0190f0740c002c100c0090b400c00b01c030342c0d81654486a950031141d0b04006507100d0307602d18011101602c48024503c02c200020802c0c824048180c3e0090901c00c0d04112600d24050f01d000c0138007401031054840180030311212042d900c4034041c1c64481c448000256580b450704001295690071a504218007c500d07100800d1005102c0b142120200842c0042c100c0d111582450100d5002841d40c01c24403006541085064410400002450140c0e10880d4288426031701e5140d0700790303a0300039550a008214180010200040c0a030480c500c0c020602c80380120700400c290b15080182c0e4000c0e030103419840c0c400105151007030601c2d511400034142000c09145480c01110030320380108004510144201e14080d01181203070300a90120044540e1510740c013020b03400c1112344900502080750150b80301205040003030301d228410310031200380444801d4000d06002242100341c1d20001240c00880070700a815904c40003580c0c43c50080e040c0c0c00100400032406150602c0d200382501c046145040c00b = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 40856092 1250 40854842 40854851
    0x601061d0105090d060204050a03050109020102010f0207050c0d0201180e090c010e0604090b031624030c05120a0212101403060609040605060d0210030605030c06030f16020102070203010218010f03 86
    0x11680d2142c1240d501c03800454000b0a482c03154109600240b09650095a00c08038440f40002000410b400c4031540314001d0b0020481d4000885040301644202c00004101e908210702e85002e03440d01444d080110707070041c901509a0710f012032441c06440d80c41d402c400f943d000d40340104910070404010f52042d07100d00703181c00a40100359201184450246000e0103000c07544448449441c1d80f01041500004140540c00a10042c8e8500405140c042c0e80190b0b114000904503a50b01100d00a00411300f2940d12540c5d41071800c100c18007118501d00015010400007602009041da044880e0800240218203141c081d08005250092080501d0040a4500e00941000082003000e0340c03980440395201c0d801000c08925a81d5110006581146807400207500c402c40000d40894154103a1100040d03070025011217040c50b000f10304009031030004540141d0308003024400036251a2820300c040a80c00000d000250074260140c0c0040d0036a040346404070111044400070403059a0711040c1d07c40f00c0c00260800b0030 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 40857342 1250 40856092 40856147
    0x504020406021f0e030d0203190e06130302030d0606021c0206101505090d110a060201050613090309030c03061509050417092706090105101b020609060309060106 71
    0x2520388108004520100c0c0e500b405210640083d90040c0a031081c00d0b0054a90342c8083c0300d80c0d100250015280403820500031b082500b002052441880710b00140b00c00140320340c0d81c42c490548201506458100c1c2180003d00003c103070303071000707000d51000f9124035006443c0f44944c3c541100202a10303c09040e045504c00f80a000b00c031003076002c6590541d4800402c07110802d050305400d0303641e4404c40c418640c00c003195410071030512041100307500f03003079804482d424003c3c0da954208900340c85007a503582d0783c01100d0304001d04c51074007164420010140309040c040c545960301d48444408130b40560040e40d044d41c49004401024021288600150404480070003e5060a403034000788060310b58040460940c000904100942e150f401c00b5803c0c10710300600140b0f228492981c030000150688506000700c0000c8000314081c86e00c92225003903000940d403624030501c41d40940c0701d0114500d80d001da8101c8010440c120b115113802c0d000703610078400783c001442954504003000300b41c0041880071906c65441e018070712 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 40858592 1250 40857342 40857347
    0x708030c180618010e010c12020d02010e012304021f021005010504061224060303020a020a0509010501051c0b09040b0708090309061b010b060c0a0b0705030103080f180301150f0504020406 82
    0x9050043d0286400c1c0142a40c500059404884100e005000c41c0c01d10609070102e2540000d0342605503450b41e00a11000d80d010700c007203086e1200308021410480040310005e004c42074850021358040e000a025580400c0d0f454070802842c46100400300c01070700414104045990540111801014252400c007c02131402a44007040641204010103141104951450480151720540101c0e2a0710901704426079891901943c2d640000c00100c0c010340c0e80745400200c5181800d41c140c1210010b0711132900c1c20024441003403107240104111030045940c0c1c64103510755110840301a02c207520900c84070900d81859a4041e0003140d00070701c5044c140d401005030f00e1303da840b01c90076034031644d00050000805205c1c449040780581401c0e1010394010001040c03410201100186001c0b8160140c20300645ca034440400403580ca11090001070014402003041c00c80c0400312900170321030b140381801100c00d40c0e02007100190a45281e1500c840741091004c0c4140804012600e003c0001c0c0000ca804501c0c0c0b03464040007 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 40859842 1250 40858592 40858627
    0x108030301060c1101120e0d02101406010c050f1002071401050408091002070317030403080709050315040602090409060b0a080a020904030e030a080a050414010e0108010902030c0708030c1806 84
    0x1000e55040300b10401c19071b4025a03050201d1150040148461000d0840c0c055546076160354074801840b0b200510755540c25144104454445040e01d00e08095559200560708821189030840b0140300f000210341201c901408404800c00403800b016a0741d44841c08c18108c401882c000c00c40301d9074980f6090000051030f21084480ca008151443c030440800707514181d00f00045a4409800001e212300004884441c11005511952090710f41d002d05440d840e00c222030119290048a400d54000840b2255802e0b94651650f801407059a01516280c0703a41b020605032200300c0e0040b01c24031344800e202e00c0c0524103564650080c0410700c0050094507400e0f000606402405440581800b440d01c3c1c07050b40c41e440520501c0310040d005992965100d0910600511a510601c101e83c85848030380d805084a40c85003c003031260510503550405282d0804014030002c0d88040e2619481040c1005010300040e08907000c1c42c17082a000c02c85035207883c05080707084240010794400c2441031004102034040080c15140 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 40861092 1250 40859842 40859867
    0x20306030a0311070f17060907030c030b0c09031c0207060203090a031202030405060a050a090b090105070b090316061401090e060109090204141807050613060305100905010605030f010803030106 85
    0x91820b041c03000f4a180c1ca050400e1030308408403c0c00c0780b8038013051a0508403c001e121080020840342560380e58510252200690300000301f040c1c141580410102d080c0b0070070f42d27400c03101e0750300e04030314084840f0f0019241400c42400da019100100100500c0030740c050000e03030000c081c580095803501c0070000004603400400e00000b080040030404801c2014400c01c152000392001520b9039035111101e001c0138280390084041c1800048050b5800300b044403a90042c2d0300b007c401038582500f0820965200501008010520302035880207001801c0311a04080035280a607014007000110000b02502c000ba0000d01600090440f9081000781398003202d002402504442d2084000120f032141440000c4c00b402e0b0014a920301c80e040c11062122100c5000340034000c40c3c1c500001c5801041e95042881940d0141e0009400b40c448203c40c01c02041c0d000340c00071544a18500310415200c2d03185e05031841101d0081c0c00c80c0340010400300400c0070704007104c02541e003d0f100e540003c605562410100900a004290 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 40862342 1250 40861092 40861097
    0x1020d030906110f040306060909110f03010902091911160206031003020603010e2208090f0d02030706030507021b06040501050f0904090b07031505100e0d08030903040612020306030a03 81
    0x640ca041c01542d40c48101e085941aa4844d03840d4240b610304211900980010b50b075032864202c001803405001e10980340c107d079014103c00e45107501c0301d04009800c22140c8103190103540310030030340c0f0059544240e494841ca404204072400c00251385191004c8030a00b11100208881c00c00c01110004880c1007110003181e8100c036115501d9a07009041d0b41d03088640d0b80b0003500120044000704100c0100303130285110700b41c1e540c00c00d64890090b2007500b121b1106002c02515484003004a00e609050102201b0007503d809010241020725560110345407200580c0300c01d0000f550792081c08a07440c0d05010316110a0410903010000c01100c42c0092503d20540c0b24090501800142080482101c841550b43c0c4e51402403040001a0f040d00317160405c1700c0304540030000240380c0360307030201119072581c450801d844c0c02501510b0000c5003241c081d146419011070b402e0b8072501a1000030005942d4a0056204404641c0610b840c0c0b0316085001c0c100300314003407038420031900501c10043c0302c0e100020110350311600361 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 40863592 1250 40862342 40862351
    0xb010903051507120c050a110303040209060f011106100e06060a1409040603061803020d0c050a0609030c051006030b0609071b170a0504030b01080a080307030e15150102060906010501020d03 83
    0xb4030381502d11314580820302ca500e40c101640c003441190450050604806144c0392007003040080c01c880342e1244811a4025800010340c03010400a0906000543d1400018100142041001581d05146c40c2c01158080c1c8842442030040c0401c0340201042a08103c00303413440c5007841501039000c0c1c004804201c41c00c00c03425000c9002025559540c00c43c074000c0d50844401c00c056074241000180c0050500f0099000d44a81c0c1c0c05900c3e010303c5035208580b45500300019000c040714642d0741a0140c50840001d604014121041c180420014050941c0719102c1050000d005031a6207440720000308000c100c18400e904040030414002e4008050044d00d0240a1100f04a46080d00d8070650341081014a00034680303000c6080d40d03900750048000c0c01a80d010349014211a03171703980065a541c00d5920002054690244089009280241c0200b20b17001074140640f0b2000000782c02051303510304100c501c80800c04400091202c2540c040c01090781045500c000703800c44e581000b0020750703030700700503003a40c02016580c = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 40864842 1250 40863592 40863601
    0x6060503130c1205031b030301050112110918010305060705030402011704022e08060f03120a030204090213030201120b09190e03041412010e060415020c06010312030b0109030515 78
    0x2c1c1d00303000e800340c80341200038402ca01e01402c141c3d0341d076004460840c004010444880303101c00d40000a81e41203c0050f500c0204031501c00c2c2541003d403000e10141d0012050030300070311101d90740d91440303c120542d400c00200410740c0740d420306600e00200505080d041c804100140000350740e10083e145520500c1e00003180c80ca44545c404941404415510f8900d4114001c800107030304940c8000c6101019600d5aaa4810791558020000410014507245074180c1c081100d64000074422000360041301460300f401401e0a550340d002ea01680d000501540c111154041d0501c1117681000110b6074501100a0400c0039400cad09010075422900030b0641070002142c0100048031100940040180007020010360783c0340d03641c2d00c03041068003040030202c61007200e41ca010317078442c03110510681404a04000050946454a84402203180c01c00700013040300580800011403811000c108950080d441101e103503a502c80c034000000d0031100c441d81120304000d900d44040010036070000326001d010700303040d10035035580e205d = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 40866092 1250 40864842 40864853
    0x90102070f0e1b0c122d0d0c1404060804060c0302120c090409050f1e0a08040b0a090503010c0e01090f0806010902090f0d0b010303090906060503070c0501060906170f010606050313 79
    0x100c2980315010b00c280d21149030703040d101801405141031404603a5501b0212001c04005004800c0c0e80005050070511211121282582103145400500e051a002d074040200156549a02036001100440ca40e030040c13000b001503a1050000c60f02c0e06150440c00c0060054100c2c80c4190f004e80080c0300410b02041d503400b40e1303646070300180c00c040e400011a90000c407444540380e1111076410803804003880340c0c54500f442620208a140096078040c01c054982420222407401c20780188003044100701035102c02082c0d54030244103480340ea514544500c110070001c0c0c0001003031003a11341c0102c03000b80070b00c0c1030070840098002102e07415510304400160f2074410f0300c0c02203016127803000c064550104901c004801480003160520741664003c0d5282240d00d034882513042c058941d18894880003502c100002100c16118000590110748114000b0900d42c1e603580e100e000380c941640003145108802c070711105415104000f6003840b803e2100003070041c24034190010700395004c020030501c1c46003c0c0703a610108005 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 40867342 1250 40866092 40866097
    0x30507020313090605100e0a1a0415030e0601050609010f030f0e0109080a08090102030402011b0501200a1106040b06150403020a06080402102a050c04090305090102070f0e1b 76
    0x1410450789400720ba646444180160109120f007134050900102005c410621031510092101c1e00600500400c601d458401c82c0441100c8030303108411034091002040c83c4074030524105a03100320f65800300d03000354004203040c149441039001a00c00d4108014101c450f903000005003064440508001812240003c00c80c0c0c050804044904040e51800c0586170410068002510103100700b6503500c041c540d20300708440d0807480140c401a012983d500504090000382004910b403041c13040001040301a111810380c0312004000c0d20036041d840d0003141c02400540d2192141c3d00e110382802c010001820903444d4041078060103054135005182400401020301241400c030740c021580030b007a9400c1282c3c1c881c0c0c020b000c0001620300328490081040400e1400784034400340c3c1d0000707011a4008141e1104000501c405540c00c10701103505000e07518065169a131389204594140d8000d407256a03980d1030314400241072540c00c0d04000c9800d05190b00a2008008081d465035020494402d0031500e0000c0f8000f1401c1030 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 40868592 1250 40867342 40867357
    0x2010f050f190801061404051309050c03070e01140301050f0c070305120f010f0504090506062211070201020607051305010309030c0605101503020c03121005030f0a1a0601050a0305070203 82
    0x1001007220305203990f4000e000781d0413103002c2c0c1d44129001d0761180104c0ba43d846a8841c042c0d00c034150910030880005550300c41503802c1c1c400c00881303008020781e101003402c28002d40d0000411481c8000100105488000607814001c2d0840003008507181c81d01d1744041c6804d025001b22944000030aa4408040c0210300325507908001c0d48924046141051100c0c07400c5000340620380c8605c00c540000036260401e800359040065101018000956628003400384840e18014001401100c0003c05004850036128071950b0130700e4500d5450790341d5201d00000e0310303101010701f80c0c03020410b0801049060505807070019082e80c0003460089440195403e040303403040891580640300034031749001e02c0740708184003200200301d4551042490341c203000030300c00381c040380100400c400301074004002c0c82e03030f00b00343c0c0d48012540030020194201c0501c2e10313100070a1905e001c030249400e0341c3d88000c03100000e0109440d02d6150040c0390040852052a24070002800350240390000c000303040e220404628400d00900c2924400d = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 40869842 1250 40868592 40868617
    0x180b060a03080304060606031109030c1005190309110108010302031507050d020a020f010f0203060109060509150c060702060a0501030804030210020f01021809060d0f021c08071101180302010f050f 86
    0x4909050411400401c0688030741400310303103803034104800d14019402b56404400014094925452480144030700511110401000c0140800180318070018044c004c00007000d031540c0c0050102402d10b00070000910340040b031810f00c50078100401c01680c0000d50b80d0080e00800a40612039295940182c41c64001d038907810245c0b40c00840e01d905d4407a80040c54104c114865402880901d0035184070508030301c8140ca00a0010b10114018003026000b00000d04100c440030b0520007030007460034004001a04031200c0c008207600400c0a000202d5810441260040402c9100f000654503581d141e20f8a4070035407000074001d0806c03801aa840034001d00c004074612041900235562400002c2c003d0904506500303585208850381750208107141032110190400c9944103ca2009140e07a40c0c00b004959003092000d18550556982c600c80003411100180a01c039102d00301184810035200000340031000c20702d4006500005002c002c0000d41c1c0c1c40008541c0250b0203040096403801e0210106190344039500e860b982 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 40871092 1250 40869842 40869847
    0x90103031211040303031a100e0f030c04090b1b19030e010b1008010501021e060403050c031e03060a0806040b0703150b0c060114010504060f0e0d0209090a02030105060301180b060a0308 81
    0x81c19010741000d00001c1c958104070a401003118100a6201c02304413901c400941c1d0106491b44d2810241c030040a00c0400804640c06c1e0020080010b040d5103403400221812405ca0040c8800071420030030389540008800440c60801d003000504544034008500c0b0740302016100c5d1041d8812134029440a508076070f0180c0001040c414505028050320801e02c00c0a005100d141ea0210000c9041c0140e000c14421010280c906615241c60840305500048050b8410740400c00c5100c40281056418201240c0703800711468483c5032940420003d0001d0340d00145232504a4010000014080f40e82d903079001c8403038240002c11032a130b90442c2180748040d401400442c28005a00700c1d40e5403001400d18120f0741204076802c0034482500045501d8000e521400010401c80190860528090310100b00070f42c4000d852001210101c0d00001c481013000c4e141d04a242c0c20107803071081581001e00900750b114005030003e004080004245280074680510080e010110240106002e590b40c03a4503070000b19042600143c = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 40872342 1250 40871092 40871099
    0x109080d0206060f060408071509080d0903060f0207080702041508030d090b0108010608060c0703050904060b0c010605011409150d0c0809010507020c09070509040e030a030e0c0f09010303121104 85
    0x3542c900303096400b00d1066240c90b14040240c0751140440701900c03465000390000a16042070850508030b88503004042c010441e03404244440f080040080107201d030340e40d40c3c58040c0f0f036040160454000920500d0018010805d070000700390f41c402119806913041e200042c00e00d440142d101100400c58015086602002542d1500da505542001e1546809809210388d582d030b81390909800c80b041889040d034207800c030790b00082e42030386004080c0008600034200389140980b0300c4001004c030368007508841201ca20104540c030303060000b4071810018010a00f486010a80c0328120038603c0d00800c01e1443c440c002d00142900181c0c2c222040e122503c9103101d0074071960300b0302e001c0508a440200c0c0c0b5420036611b484005403440e0b200080a005404000e009000c0c651510001100c0b0743d40051041c1360410340700d01e074181c6a110f04000802c0340541c00d580000309106407040c01414168444000307441012400350304002a6901c01e82541101ea05090641643c0280c48158000d48414100c800b5806800304000 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 40873592 1250 40872342 40872347
    0x905012105090d030e0f060f09010b0405040b0a0c02010606020303061002190b220b04020603040f1b1a090307090222080102130806070c03200102040b0c061e0a05060109080d 76
    0x3c0c91525041e032410b0020b10140d4004aa44401c03a010340701c519070000c00429103041d20f8203100c54114030800300219012901501040c2590b109480485502a0260800441c0c03007452080f5210700c030700c0b84000e010340c6141080013580c1e03010103004c05100e64440600d00d40060300810000c4010304003982c400900114604152001d1042140c18442c000a001825400c00c80310002d644202940000c00c84c0b130a44554090005540008004994a0b01c252500c0707800f0416091410b400c191080000400d0310381054011482c6c8075041d015445420002d04c03000440707a8001c601442a1600d007540144c903502e10760980c60718244140404000c1040702c2d60086420441034006146515080c100001020303592200981c0e00d00b8125451400109a541c1c1540020b1107451020f6048601d41c0303002d41c1e410311840309079013240d02c560300c0440f1100001581d260b46980030711025034400110364003004030221822092001000c000c150b046c24070356520010f0f005a0089007640f0241664100716580b2074080d0791702 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 40874842 1250 40873592 40873603
    0x3040302040b01020303010f090216050f010f0e0f03040b07051c0c060b090c090d0203010f29010f08010e090a0f08090f0a05060703050f07020d12080f0106090501210509 74
    0x60703014508140100c8003d500003c02c40b4100c0743c0c2d55444040080c5401c901c84001c0d08401031903d01303c0310f10702645012032030420200300560400c000014580d03002c0d440050031100190702c04441e94028102d9603d070050b0100030f07181240e941c419495652061443d105050a800040c1903051080d11901004110361100300d40d40c44910803801040240c0f40d400400081c113008586208504204000c80012030a0010304101c13014800703000441c09422084242d41650300031031107144075103d82c240c071101030351400f607160080b55070a00300340306c0074a0800c0d0b005102c07150500403090a00b03500008580285400c0020300602604440c5d8204400d6040c500442c595001644c820303c40d02210350b41d0541480c0c00e0248500300ca0f0000c10191400b203140d42c0c1070703480e41c000705035110b0b04410a1003010050386801c001441d406102c1d01c81100d808038596000b6000303c2c0007403c03002c130041c0240300600030560072141e2101034610900340300c80310f001300041d00d0300d00120040301c07010002d050030f00b8040350303140006c0d2 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 40876092 1250 40874842 40874849
    0xb040504031806021203010b070204060b1b011b0203190908060c04030b06030106050609100c0b2502010b06251505180309030703020f1c0c031203050609010515070c080304 75
    0x50350342c101c56441004980c1c9101018400d40c000303904000400041848000400c8900e201901c080340d01640c410740203030b03a0782104480c00d003411242001e01034040020300c43c11018401c6103104e88100504500d000751380c0d0107580c400c2d4180485510190320014017685002d401090340c0400c45089203040b0300818610b401078802112602d81450108800c6d150602485040d210054601421b18284808000042c1c207051510030500c50100103410119a15220f11407051600301400b4802210001c14050000701140410046914104030035615558084c00c41e0240302111500840e4003444000c00f1114104600b8020241c0303e40711041d03004440c1c1c0f034020034814a81001c8003514400c101c00d4481d228460200f02070360603003101c1c0003800185040c100907485210081c103200322021a43e4041035034844d02d0741d01581c0c50104850104100290300b60b0074403400c2d000d85020b000a00f0035002183c0b810380180200c40c803904090101c580080c0300d18054038655501b04c402445101c0c7d071201c003079450713611601 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 40877342 1250 40876092 40876127
    0xb0403110f040e0a0623040501060509070903030903060f02040b0703020604031b0510051008030d05010e01090b030a02010e030309060a030603020906010309080a0c05030702040203010b0904052a09040b04050403 92
    0x394a403050302c1c051145031080320700e080107414078980b00d603100001440540d6404c005192202c000e01e000810030b4003582c1c441d61061b0f00008400c2d0034181049102c200007040581004001001480081e510502002c11641d000c00c0c04a0344644011a0340041c0c007883d00121030758403000c00d04809160f0700285090040f402030303e87c9141d02c8204901e841111011542c0580381d40e224502c101e0444480b0340c403c65001081001c40440c080c0c485200500b503038001c0c40c04c044202c0c0c17110014040204490140c9005202c0d015040000e90712a070003103038655243d4500039040c003045074481c0c1310702c5d281071040b19003da00040c41d882d502c1c0c04014004e801400e0746d0000303034001d0507407500040342035000e48102c07051507402205440c1403030110076045407061841e01044405010a200344001602d03680051030181c8141004203840b01442010301045500081050240c4180310342c03034142102caa42034104c8100f00038102070f0369175045007012402620a00c0e00c900d40042c541020001450741c0000040c00d07002018 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 40878592 1250 40877342 40877359
    0x1603080402040b030102030c070308040f081b01060e0105011205060a0f0927050303130809040c1e03060501050a050a111e060f040308060603060102251d040f06090c0b040311 76
    0xf0303090500300e010450340c41075940c00412100d40801c1c05444e0b01366100c1e10480d5400ca1148036039441c4541504126440c5003144a00300ca802010788003800744402901d065082c5820301d614020001b4400c10000c0e100b11041907a03000803e61f16113843c18060007505050a10002003695440004010f142c103c14401907203040740c00d60121542c40500e0722008a0304074004504640b26940782d070400d10141c0c18203c945100400a400341074840d030240d0f80604041c2c3c0c0b500312060585030031400c400420f51801900701858000c091145a030440280c130024483c41c40c1150b02e412a0510581c0c5003018458904081c1c801d50010702810316010301074601d0b000200003544e84985a810b00b95000b4042503500a000c980020700041c0a42455005194000e00520440d08402e80030040070090101480c0c1c8010f40c03010609061103405602d490280004100300034444c40ca140c5a21085c0501881c18402007c15403a942c00313400380b000e40075044001d815400000b41d5510351746c2c60306010043c41100107a0042c2040c = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 40879842 1250 40878592 40878611
    0x509030a1b0b0304081b07030b090a20090a0b010909060905040203070e0c0a1d04180314120c070204060506030901140c07020108070c02060c011814010506100c030302160308040204 79
    0xa42c0941380200d60081d55182402c0022408401117076031040c1900961041100002c003140c050600320b4090b00d0b0b400c2c050301c80032003142041003084010a521b007004418031000c0c041c1903155048607079132218826400054900c2c2400049404800c65840b1500c05418000c1c0400d04c240d8070350045004038401c904481031a0b55881c0c04440252044510594481d002d00c40440d031a4051b40308000c1058015060059054060300003c04882414143c01400309000d085c000c1050380282e842c46085404503262405c01d050003401d2032100b00c2c001d250001200d8042405c604649858000801500c40206200d0305c03407a02e40304846c000c10a18200c80c07554070035080402c8890717040e17204031204240c06035201003040c0d41e06030060310fa007468018201d80100f8204170048030302c402131041d08540b4900565060000b5032905103440c00c00c08607001b03940345034540018850b01d0b0740d4042e440020707490603003450803042030300f405d080c3d0080c09a082002222400070002c038007019030118866104030b00c00c99040100882 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 40881092 1250 40879842 40879859
    0x313090b040b010c030809010213030503070b070302030903220302030109050d0e18060139020102010f0c020715020304081507020f071503020c010f06080604020a1205070608070509030a1b 82
    0x20b40c00005010030111040540030130304c6081c007691b00c04000000503140c0040f4058502d4100b2150340141c1d11508049031301c004000007100f00341e4000a0626040d411410043d41d619201c3c403074103810407005126580c0840c0e6448840c0c0d001801180c00400800040e01a07092140c0caa8641c403409400181c0030700d01011241c5412200d400b0072800c0e4840070403141c7c1e01c00c001591038801c840345580d83c444012011081c40d030742505801002c0104090540d21403400c030b20002e820748400c0340d044d40416040014044e001c1d9800940d190440f804030344119117100c9140c0301130b400e511454110441b0307405078030000c0000404000c00f05004120b103600301e50002c119004030340c0d15403806005440c0140340111002e45d00074482d4001e0403030605410300000e0a01c004296020407200320b03501040907034203c1002c110540c41c1c170030ba01d90000d00f00c43e0442c02110240751b54140e00c0b00e41c940180d9051004820110704c55900c00c000380d520108002e8216082c0d0005400e0a150080040c02e003584c181900082c003166040 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 40882342 1250 40881092 40881101
    0x6040b16020a060506010309060c11071d16170a090c0b0c10020a020c060d0b090c03090304091806050f1b0f160201140a08150109050f01030903110313090b04 69
    0x52803a0702500310baa031203a54140c0074204c0a4400e03070415403140c000c0e1001c0381c0a8460004101519220443e01c180c3e041d92490034840188c0c0720910701c0e000d07000c258440b117001044581c0d01944003100f02d02880c0d0781160a4401c00e54114511205185440070410001026405031042a02606244004543e01d4004900900c61580502c400e034201c030545032084400380d000b40003e41c0381c500589180c11101c90100d0b1131500107101c01030f401c58a540300d400240c18081d0003241c0001e00b04007158514640507000341e82d00c4c8070340e20031628040d40d10a0703000f0300c00c401e0b05401165942d111a00b440181020707240040c159206a03109504080c18222000100c0c001400305d41140b072440c03182e83e0500d40400d0604440c916954002d138103008802e0000200282400b0090640254540f0b4034030350b038206100204055401d1108650601808601c2804140d491402c03a503034100003480d0110700d02c011b41c5001c6072950310135013000c10644404103400c81803640f07104100c426101410400c20050205030100020744 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 40883592 1250 40882342 40882381
    0xf050117030a0806010e040c080a0e0304060f050306180903180103060f0b0904020f031f09020403021c06110301080a14061e04061e060303030c09030206030a0e070e0906040b 76
    0x40d441002010b0505008203406944000c050504001440c61040407401791020311001800041d0804200140c00d2000c1c07207292050070f00e000003103051505065000d04100d001020100c1409804030000b881d50790b59070b002c603224030b0b107014424886051400c14180d0b29040b2101030400509540da400383c49500ca80f065904603402d00d05100715503450407006400300c0e80581c5403190042c0d003c106000f0310504400c01140152100e40c01103183c20350704200da448862154001404847c01004204003507600c24003180e0b9240a0f0801d8040101800d181140c000c1c01c80d240071024410010000140920b00402c581c0845801001c0440c080c0112140d01d9403030300ca040342c0e20301b8003ca100c51100050712040c0c4004d94842c0c032860300020725410041240d4a94103840300c0c00c031582902d0b01014010150305020300508840241400e003103642c02c1d07900149507408000c250035078103079544035800c817140c0701000100000c18041040240d141046000561614000c40d016a0300b060054041195201024184a0b05 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 40884842 1250 40883592 40883639
    0xc071a0301230f220e070503150106080601030b01020c04090818190306050705070c030b0a11030f0402060919120203070b07120302031305030a1806020a020604120507180f0501 77
    0x221810b610401c540b03243d00d140641c4410424051300060300d0800c1c07040c010106035000042800301c0c40c2100301494050303120340907803885001034010040c0c140c00c00007043d0829400d00300455041c0d51180100c0c03410200940c1c8950082c2002184014010000010050158820010409085102c090140004050300d08101c0000c90000030400701d00c042c0d0041d0b8010020f803504901d00311035600d40130541c003c00e80090310101151b409008110106100b05041542c3e900046030031490400c1a80721162401040030340a003400003111102981e80808002039400e903507042c1c211858507100c00007000c101049040f030292080c00004121070054400b5109000c0d0700c0241400548100002240a0b400c06070600d50038018401c80c440000780244098109030285958250900c8003d842c4a42060b03015070052055410000441d40562980012503054820728a010100c07808245802032410103154000c1f90441060785407a281c40c50260420551101010700a00050741c0b114190080c450100d2801b950 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 40886092 1250 40884842 40884859
    0x80304020d030905090c030a05070f170604020408010c090302040b04051603020f040f0308070b010e090d1409090108160603020307052203060f090c1202150c071a030123 74
    0x61411050010360103100e0f01d02000b00360794800100700c8034001a50010b4002d5000b1040003003201141c45903603404400703850035140390340820801820501c195205002d501c806007000402e184c1f51038046800521482c0c000b0400ca043d06540200780464a000882c4140d08011441c42185090b0048038041c4e4038048415401071070420040e4003d600014006042c80c8d82071100040f00c800038401c210003540174100b4070380d58400c546400121404141c00126031500404240140140e000074103c190421a00304030b41c4042014000d0442800303111101c1d03a00840340e034004100d1400c08925000c00d40a0200c0b0b442085403111410342c16400111030050000368240544a0b21500c0048102224096400c250402907104e171200703010744850804444129854440030007c100e0060030034001040008480602d016403680010900d0800f0300e0200074455010490040800d8203200c0c103402010840c02c035007409116106005065003003440342c801c1c1015084403c0c600000a20b00c0340c40c4000c0c3c0104002d0 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 40887342 1250 40886092 40886101
    0x91003120c0501060302031203190c1b060605190609090605030a0221101a030102071a1e01120c1202130c05070212030304050c01020f101a041e1104030803 68
    0x1c640854680c41600c0641d00d582001016071010b0000c192401040340301c5903524a4a00600f000b8001c0752010384070024981507c11940960003a50307034944440c1c40c494007000d059203003400c00c058196a0072003940711140c0e08030880300e0410004044e0403a80e203905c4102c0003503580c0c103c08007100e40d81e114241d0103400c130102c0b4000510b00310701c05c41200595140c29441160390304080c0340c64801c1c0040008040d0b9628140108440d966035110b50100904030002e5260a245554024108941c001c0444030290644041000c0c2070310030602d1011019001600f00d580c0da5030b00302c040303c40503d00030186d643d461241804030700050f800340718841c561740107004261030000ca0804640248011441003081180a000a400503076844888032407050701d03a4000e43e2030b8102810b0160510075000d80090655003d2880c401006030042404401c00c44541c000169019225400030740c40100c460724198030a141540b071440c07032404811440f07004080194100044062020140c600c3d110b5400050400b440600014 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 40888592 1250 40887342 40887347
    0x906010801030f12051207080601110f1005091c0203070201030f06060818031902030c070b0a09030b040213050c03041704050d060b03190507030b0c0f0414040e1b09100312 75
    0x41a000ca86403508614000c80b46c91881204c00040d6440400a0000700c02d029141d0386c04400710290540c924050004072071404043e6550b0b40c01c04c0002c0e140036880c0d07000035039408400d001001e40e00100695100c00c00d00cac40e07a002500d030791000d041207010038030786222403110101e940f1030041554440d41b00c181d001c1d1254040510b00e08071006000c031952008000000d10440c0a1200a46011864004588502aa40a0908103006904040100340d0240141d2805a0744203002400302c9820150a02c495280c50011410700c28004600c0c0108a00740814000c00c4d00943c0011031040d806003031110340c468080d910403a054800c0384145030344a4900b104090100790150b0022a020f00c00400311400c01e81920400103440ca00389409039000d0700058030030810300070455100e41c0d20080e46190b807458440717007541543d102e002c0da01618409112000400009858941c403440340019200101c900d121040c181040e055600c0441180c0541d0001d800310b1807082030060848280c0ea4420b100c42400304684404 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 40889842 1250 40888592 40888613
    0x19030c1e2004061e0e0a020a02031603030209030106060c050618031c0905060702070609060806030307060218130c03060b030603060a05061801030b0f010b070f020f060702060f04050906010801030f 86
    0x11903002c0d56681c000180848041c07032061515000d4000c1030440b5180c0410001c140300d0041c00002003600400c0902949079010084a0008540a00c1c07040b4240450408030028018050a6a050341c6040b9010070201c2c0c10400178158640b00d041110200e0f601c0c18101c028001000c3d070400c41550041c001c1040c0341502901040c0d5030100e1260006541c0746603143c46240a4094402c500540c1041030706121040d401a1281d0140ca4242041034250400401003a80e81c440c455001c3d000b10341c0482d100c8002d1400031400d0400c00001441940d14100103110070004101908204011901d00000004c1209280741903038070864004001e000c0380d0b910003484074044d00000b0642d561220098404140b00c0c444440028040c500170640f02d040c510300040304100142c2c060700301654009061203888001514040618116603058072003060040f240340100d40d0500980b074000751302c0f120108511900c3c4600c4809001198000c83e007004042d100c110044d1135100c170030700020b01060440d86070710001c14a113461 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 40891092 1250 40889842 40889903
    0x3180213110301170609120406030c0e030a051605040902010c02040c23031e0105091f0801060b070b06042a0c0b070206040210030e030406080919030c1e 67
    0x40210710705007000d48041c03032a4400d03080b0386284c098130540c80310100010031209038449222802000111500e04841a10313010314800c40040580716440e00c502c9034400c041c1d4000085002c2c044601030a0580b5003907445401482c00104401041c500014842c6458080c10540c03680613114030346030030716079002d02016040ca80b00703201c00e000e04ca20301d2164509030080b0700034085408003035407600c07410905006058000d0701c80201c080a00720500500050365800c070615040007541c18110078410b00c0480c0c510203240035511611440d40f0300240050300701440401040554030440002c55240d81c4c800c2080112a1032032220f91503c0e00e016122036081410a00103a11440030b402c2400d40c01007190783c3d9114060f01201c1100043c1c109009100450425200a9403015144e0038244400d0200b020071665a00940c0705000030000d100022031110201400480003103001c1d0032040300044c0b001d0a01600f5500700715000c5642800b40e90601c6040d6500c50048405264843c4120107190040801e002c1492103491 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 40892342 1250 40891092 40891129
    0xa03061121090c0603010320010e0604090e0708030a090b0307032009010815100e06090411030609010902070b0a09031101050103110f0a0509041410050f0610031802 72
    0x203407020720400e9000018a080352442105052409105190504200307408180c003600080c80140300041e402c2c0080c40003903444a0344405104010b10040702e2501031100629006480003401041c0c49000b5000110248007c2080300c0d81e00d0f40e9a200d0950360702c43d42c4091000216032850030311a10640c54021030308000c807483c01040d80030102401018400541c1c03424070540000180d40d4140d0b5800c4607203a070b406000c40d00000384501c5440302084a10140c0c401e200c0801800c2c42c0383c1c10865640300117803079680301c000d0010000c094104101a54aa20603581140325a14003400010030401c54000c030b40b03003a0740c00160214951100c601c6074000c3d1240e01d4086090081d8113100c0000d5400902c00d80c0e000391300800c0030000541156007803042036100e40005c18052440311f081400207480e20350780e464120354407038400c0020400c8c91025904040c61180701c841042d040c0401d100f8000410316420780129801c503040340744511520019021120307080580380000c021320310001d01618020340303241140034804 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 40893592 1250 40892342 40892347
    0x1302070c0b03090d141e09030106170115080d0207060f0905121029090606120906060102070905040b06130b131409150c0d02070c060e01030c0e0a030611 67
    0x201084109500200d0707902c2c54540c00080100403250340240c07062000d0503046001e130700c1d0143e85020303d044488504901213403194000b41d51090b5232000d5018100070007010f9030185100d40e8000030319019100c10070511145040e07002000c11100d0010960240025560b00100001481e110040c0c60f41140e25001005024a0020006440d1212040c07860710000301d9001e00914003001002000f100c440c680c04031070340c0540c081ca210120b0000c92443c1c0e0000000c848910b030580d00d0000140c02c034880d54802142c10030440c1c0502c4202100082e00c01d000c0c6409800360742009803100781032800c40c1d00495002d403c8041507000302d600e83c284074518040c03110b074105022400d200201c1c0407035541c0891140d107103401561000026048180b4400c500c2e08503590f0b00c094003412951042e10609880003034044804090009004034540083da4121407070280c5c44000e050241c0e94601d0003416103480c64100d40c0c013117420000d050302e200d8814505101d0120004041e07070b186c1f9095481d4103008011009016000d401c1c01c = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 40894842 1250 40893592 40893599
    0x405011107080307030606090f0306180c0824040b0105040c09030501020a0509090a060302010804021306180e01180b01060e01020a0812190209030a020906041b080601021501051302070c 81
    0xa4010680070b409222800e59900700250010704071501d59107e5000c110070044140305050486d003000701102c3e085000070450320700041d4008002c0002c088010b00540020390b00040800300466076030b46040411503075480c2258100c2600c6406c28045400410000580005122030b02d0070360300c01d0700074034071620300600e20a03280c3d9a0301b4220b9020140f2000031800c00b140000d500e240c05442c2a50044050000344400d525543c0003070100c120280000340b04072061907411442c2207040d803200000f040390b0b500c0f000d418060066010700424000c10f008106d1350034003482030984000b540c101c0154a070b1100d08078031b140c4c0c6480c03402c0f02c400c1101444541180120709501000c21042400f1b440d03442c208100240301405e0400744910808a2610600c01d414010310401100380c1c1c0c0461030744400c6030103494070f0000c1d41c2c4082c0000c005200810100c41c41441a0365181c0510354400f00c0144640000e0f0202d0350714203101865800046024400c070b95000b45641c0810800d210150090405203229030203815207141ca = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 40896092 1250 40894842 40894871
    0x70f0812040309150c0b0705030c0d09080405012015060f090103050d0801050a210f150b0f0d0c03080702040b0d0b040201090b03070503070c02121e0c01050c03070b040501 75
    0x1070314103800203000000140208807011382c50181010490402008210440d0354850224a006142c9024000701000040a010940080340c0d043e02c186582002804081d2500c0c1200b0742040c050640014002c00003103038408118400b00d1007100c052002081d40704114080300001200080c1090b400842c0614405000d072100307400700f0301861049010388000c1c1b40d0060000c0207020143e011901c2400c901d002042100d0108003c0d0346240010150380100041d2800c1c40300240042d940b00802034100414040e40d4010350340d00025040e003048640300c20510b4504104031007050440380c0a0b0041000032410800641d00b200204a11072020740701040410f011800141404514101610214802c4080000b1507a020f0070482c060a203110071203041d0300b0820720041240c08014001c10074045100c2c001d8041d0b6030b40e045481190844002110181101c00000d0b42c0400f11407050000d26100d101843c0071150b00480075a411800c0460085046c0394160321540014000540709a03100d5594010f00380380c40c03c = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 40897342 1250 40896092 40896127
    0x350c031e06040f1508100b090a051b0f0c060a0b0319020a030501060b04060f0305040c150903080c0102130b030f06012109061407081006050c070807080c01080109020906070f08 77
    0x419004200070540d160800042c24041d04906a00c203076851f046030340c1c089541e1488483d401c140410f03000159a95800506061215030350181a80400003280c000102c41d00301d00105400b40f052019114540c0b9070800040a03144070070704655264116005d02c540e1101c850340207100640c0005c03d14410b5680d030340c662500712881904284004440094244522500f00301c100d40501c0c220f207020407aa10345612820030909540c02091400ca00d4541c441404610071800d400180d60052035090b03542c5403c04105000790702413069140300340700e0b8400024603203801500b5a0f10400000409506c66a5480011a03c80d110030250900810503881d041d034500045114840580d8400c01c0700098220b13088282006048004290364104a01142003158007408941d00b107040311610705141d515441c1c081c01181c2001801c1c1c010704107920640b640001d04e003000080c4810715680c2030301c54402d240d883da1008030591041191450304810104242d1001515009420b440c3d64015441e007804c0c0540e4070300e5101d801 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 40898592 1250 40897342 40897361
    0x14090d0305030601080c03040c090b0415080601050a06030603080d050621060403090504050417030c070501050405030d05070809030a050d0b03030304030e1c030c0b0403350c031e06040f 81
    0x160740030080000c2c0f56001340100360401400510103003140b17400d90360f41440307002034040c156009480c0c111203000b03a2290381004030240e43d10303d1203003404c540710440300d07550b09070900c0780c24032070300d5810710005003103010307102d1202983d42043c00795142506ca004140050b01c8050112034000d031914800740d41c0c040e020000140e1000544000c2c11081c189814000e252501e281c00141c80b03640782806200c0044c01c600390407441c040e00ca4007030603129516000242041d0098030005000b550901080104200000c0020946942401c80030845500c0d03d54045541d031408072441c1c202603000b08992882c250080c0050b1166590b00c03000428030741c0c4540046070464005803411404a40100c1d14400f0f940390050a401d10381907411130030451200c06407001004518a1140130300412085c1c800710701410704c40c9654410190302031011800200b1060000341002e15030701040c283c501481d80200c0d900071540d508981c000e01000c02104070740981c50543c0000c00300c007c0c0c0855446965440c42c01074500c407a00806818 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 40899842 1250 40898592 40898597
    0x61e04030503030403030f1a220b0d0b090d020a0302070e0c0712120c020d1209020301021201030302160621051e0c0403020406050f010516050a0519111f14090d03 71
    0x1d140c60001a0008e90304207640305222000303100c09665158440c640e00c40002000c4048684048940c1c24200d002031011030300301e58000000441900038401521a036600421805085400c902c5034600100d840300d00200c80140186c0100300304000400079540c0803900801a400b590740380c805241d0700c40703441c035000d625040c01041c07818a881040c0e80c0540b0a0307503a40303403443c0003030010b1406c041801000c10380c581c403405020036600d900600035501c0c03d6064034071440d59441c0e904855612414060754925180b1100150400c040c0d07408141c1c0781c8a40b10b85000d44540b141071420b15050140f10318040e11008026840b007245548020740001780c080307035a0340540f0f01c0c0c90b1b00c5903503503007103006102c03c1d0303607160700124090f0000083d00012640e02c80111500c1a42204d40b100221000d031600c21b00304002c0c00d00c054264810620543d128114a1100c1c03c81c051103a03494501c114281c1d01400741c10302c3c2c03040c88a6420842c0150800e06640554554041100c5070b510f8030b89491100c034002542020030b403406800 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 40901092 1250 40899842 40899851
    0x110f030304060b100f08060d0303060f0308030402120c03030d05130606030b09010c0806030a0807080403082109010921110f0f0609060c19090504050a0e07060e061e0403050303040303 80
    0x11400c004c2041c850030300091601e11001c0e540d040000d0400e03031001d011140540203100c070490500d40300e03501c4071000d44010308c03140005550301d00340441c0581090306c080c0d115606000044414840c0018403800200300a0080c504100000344614003c0100501459401d101c04101c000003c90030312031100078500c00c6802c0750050a100030010300711800c0b1803404092181d030500b808015a400905600d01540c0020300b940c0e0344c034031854803201034000c551009010030004680c108480884035106030030011400945030643d0b0755942050701ba1a4101001741411700402c070b040076103000a0311041c0485ca594144000c84561111581d1f1030001c80c544540890f0304102d800d000400420300481c0d0704070003040020915411300709418035041c401d84034400e408414400003583d070700f0302503c2c00500400c8001c2c01048140b818440c80000303030035812202407640c000c100012842c0b9000d001200c0e00090050b0400b400c00d20003503030040c41c9011090880700414410f01c4000300280003000118490391080d600483e = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 40902342 1250 40901092 40901111
    0xe0a03080c0d02100c0e0d02190b0403030e0114070201121e05060f010906050d050a060923060306070903060504080409050c0c06060a0303050a030519020c0d090b030115110f03030406 80
    0xd044c034a20160300e080d40ba04150091204550104c80101c6860302100c00e00d00030455840000c010382e01e20341d040840401810000a4450f003860302500c112030194492400440341000116040c14101c000306490030814012440035500c500900304048003012000074001100550150900034001546608262550200451400c0003456045440341c2820040303002c40c20240050164000d250403442220f03a242c0000f100032a0311341291f001480649402c00201504048007010420405100105519854013080715802c00003144c45c410031890356090035590465079510050f21014000303894030a003d000100e5030740980e00c2080d000380c20b1040b0007903031a49501d4510381011001080d01e40310f1031800d1801c101198101d800c03202c440c22075140c00141d0f5551030340700f11078410700748611510461000c160b014042c60000359600d02004103803140f16000b6500c02c3d40890030302c401d004402c64940e4904141d0101c0e40100c444000521800059408200003900b11030304c2c40d0022a000d4410070f0306c0e04170b81c0 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 40903592 1250 40902342 40902347
    0x60e010606090f0e070507260c060f07050315030705060a110d030c0c020409062c07080303010b0405040b0315090304061403040c15050c0303010905060a051e010e0a03080c0d 76
    0x42008005406000740c416140c50010641310030014550402d003c40011680100505605202c00c0c0c000030035103000802050800e45503280d00065130511491143d03c02080300e0035074116078144201d41c6c0da03a8861841d541c00d0204420450021101038261146480102d1190380c1c2102901b0303c60200d98555a031140c803140c102e45060111841303241030620f80303e851011326030b011100c1c4d960306805880c040780c004801d1038998020940032180c00b10400c1004124041e22500350b50190514007043c00300c0743c5207900e0b01d4274241c0700d100a00c645031081d00c0c208420060b40c1055000401d0034840242540c03628807450381ca01c5028032040b10140719503000041c0c144405034201c28020b034103041e500e420604500e0300e5621404403000790f000c0c9555500c20340340c5000600d8880d004652108601c2d070300303607038076940d5508502018000a0341d40501c10700646c08040740e1420140b441c55281c0701d046084074088482480151440d0407508142500140d44490100215006200503c03007581c01c80f000f04030805c56141c00 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 40904842 1250 40903592 40903607
    0x6030c18060614031302120a060b01030c030b010e190b070c03060c030501063905030705070b0307020604060b040b1806040507030e030d11070b0108070305060901060308030f090a060e010606 83
    0x4882400301c032100083c0030071456030640b903001c070990b40c0d510070380551400003a02101c1141441c50007441498086010014903410000c01c0000a880074400484400c406400340c03510302c02d040b40080c49c0105a4003940c40c2914400c001c1d00f00400030940c8413500c801040c130042d409030506582e070040f0507a0800400115128030b2596170700c64a0100425410600020420511890318035481c0d06502e900106100d5075207841c2d42260700c032011489489026140180d00c0fa04054000d07a520b0090010000340c10150f41f003280c0c4142d0040e8007402c25581c450340c82e0002001c001d1080b54025654050121158032103911921403406007001c9510b0514021003000150346009002504040c00c00444040501c4000182d461800301680041200030000010030458013648034040c1030700d40c04000004051030040741c480242c038000c1003602c1080c1c1e07844c110203003a5480c52100415400c000c0000540d52152620b03038540081c1540306a41000c2403644408090302c8290480300526507552000300112500704a4 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 40906092 1250 40904842 40904849
    0xd0c03050f070f030213060f12151b050a270e151c1703010308030403020714030705010809030c070f050a06020c0303030402061c0c050d050c09090606090406030c1806 73
    0x200301080c03c119403050840c04a20009000d50100311030901c9440d0a40c00c604050008540f20590b141e9941b040c107040400500025140180d01e80100c1200910078001d2100031414980015501031103ea030440f000e074400600d540811946441c58420901ca0301e5800d41000c2c040054191614240403003400d102d503014103c032610f040340084141b0582c03211030203078038100d880100030038003c0098104803142d071030300d440f07403001d58180000040200103622024500840c065800c480c92103841e0b1400c0400c90001d09403150341944000302c20032031980b10355040340d0f11590b814141c81c10074040f40c0f40c0e2407400c4942c2d0401180079030030794407e01c00c43c01c01c0315032a401800b261004002400428000c03a449100192001e4068440060402414403d0300c004030b101d411080d804208010310664010000e03004044005411130605005c95075410a690550300348041c000c04000050b1625420490b16034000900b8542054540c01c0000101d0110141e01c1c00a240805030440c000c1040400402180d19980 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 40907342 1250 40906092 40906123
    0x506370206070e090709090509030d051003030809070b030408090d020d03030608060606120a0f0209030d09090605090c121803040320010c080a08060109050a08030d050f01080a021e0d0c0305 83
    0x10170070200c59840f00114003121000da200144035100c801107282180305e00514079103414185814810610045402e25049a000e540c48078030945504646035122000d0748642e081540c010b1022a02260300a00140700380310004199030108030b055408519030916180003503001c00c1d40e4070010402d0100c244201c5900c88411030348079203010003960f250020350070007410002e4100d95440780c0491500e43d940c102d80c42c0c417a00608840e410010050000d040b500306019407908582400340000f01c50a01a8000d03020b41c580c07000f8035050408903482e424803458001d0a04060b1010840c8840120303c090000344007a5004010302020031103030644584100e109608410304015042da01e55000c6031803542960600303105443c115107151590340040360310a06640100b507002c01140030001350300c0400030003050700ca60b100406104950319801402d040302d1007449140e03102d80220506000500d030100462601d03000e01031014118000000200c0e0007c0200c4c0310441e488a019032080c000d1103010408074050380f5468 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 40908592 1250 40907342 40907359
    0x80f0d11030a050f070c03030f150e01090e0109020a12020f040501080a0204050c07020102061303090e01090e10090c271d0f030307020a0809060c0f03030601090605040506370206070e 80
    0x1800611506106e40041d040541c1c1c0c0a044410420320b80080e4040b0030a1040a02e4003526464401030030a420711440560303e1130b01440c1d0044880601450341c00640082654100c180741100400c0814140802240d10a8481c200500c42c1d07540c41c1308141c080d2640310010250001c451040c0b20032254082d090000c009818007402c00144e80c001440703580040400380020800d81c00b450b040e00e80d110203400801d508940c407000401e02000c2c55018980c11103c032822544009225192001100d0360060090a580310a0300140841d0901c003c00d0201d034000e40c14450f40c1204a40002400c440c0b4036002011180804050601900c004211002426207078402032b624505000e40e0180d514510844002c011541c04114000190346031401e42c2c41031880b41c001e840010b140600256181c5d802250442c2c0880c0a1490208201d48580180c0381600c0010b484035203041b001f003100d180044540384103405035148404207007401400c400705c80340d40668142c004183c0d50030a81da014120000420505000304902c = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 40909842 1250 40908592 40908601
    0x2091518040e0a0b041101080c0a0c0b0c090303040e07140c070303080c0910030b150f04180603120807120b0607060b0109120507030506150a03080f0d11030a050f 71
    0x881400030400104580c0000c01d516a03081d05400e0100020000d01504018000c000900c1108068100b040100342d0b100d001941d124010000180507212038600080c0b240401c0c400090a8602c0490300a01e003840400d09140c0a440000d1540c2d229410048030848010180700400b0380210702580e9000d00794580301d05108030700c01c689079a02190310018040041d5103020808110130b040494032604405841030482c000d581d00003601410f19803000c240112030190b0861010345030542510184810b50710003500d0a441c2a00003c04a41010070300e0030981da40301d02c0000003840d548249200c2d003601c1d403940301c6540781200c009840d640d02064603d800700c0c00d006aa144030351315281100c143e503521900000f1400c1d001001244c2d5000103030049642c00380e21990704000c0c440e0000f1741c40204c9108030202d91a030b60f5962100f041440b41181510f0304021161403d00000314540c0107071502404000310346040242e00c00c1c07800c0503190b020800c005c81c4000041072092054585c01441d41c8941c0070503c11200303090 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 40911092 1250 40909842 40909867
    0x20601030201140f070c0803070c06020f0a0f05100203090d090b04030210030c0c051608160e01060f0c0803010f1d06030d030e010605040603081216020309010f0e100201020915 77
    0x411141e50f02843c0400a400b203d01c151410035558003030342107100510b000d0f4451404507038030b60001c001518102e8040d01c00098240c40005c62440241d86540a0840c3c100c240d5079030481800c0040f000c80f118020f142610404030710760700c05140300d8800700c002024030501860000e42084540d0f00300500c440c600f081b040c030158845a020000c0601d003460b0004a21507420401c450704800544018203e0180d4000c00300b000074a40c2c1040c06a51004090b5400d1030f00d041c41c00c502411144c40340312200c00100f0010015540240c20103e02c0021500b01504511600e80d107268455100743c00036119410002c83c103100104114944d01704903088542030060504100c2d000a98035400c00e09008200364686c11216682c2c40c0a40202004050181041c0302c0d8a459282100480e0480d000e403023100882080000e0042050b610304440b1141340e50051403400460000446960111540040c2440812b6000a1290b01c42c038011480f040b802d03500040e118210741c000c00020701d1074241d07516550135040c081400c1144 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 40912342 1250 40911092 40911107
    0x912080903030c09030c0d0c080c18060d050f060f01060f11071809050f01020901140412020d020a050d1101020f010606020601051c020315040606051c030c020a050a09060e0106020601030201 83
    0xf40e001d503202d500c0b04240320000e03150208480403c0e03003140e426440301c3c0800003500461401d40b003403e0b040d0b4075032186160030310254061306141070711007601035800300342c5505040140e054002e0050098070340c0300701e10350313032051a1140c103440300000c0001c001300400406600513445a05801c41d468541c10703501c00c04080b66075504242c0201c1002907407803441c800c00050b00c0c2e88220001c640c040d095401c0700d010580c0043c001c1d0854840d16001c00d4004004500220a10013260151460050110b000c0a01394080c41003080345508103c2c1c11094105011449035900700078040300a02c150407041c0071005600009003092129210442c19030f04064003440032607004104181500d0059504030344910000302d4010103040c050030040e405004080381c465070080d911040c0d500c83c5000d503400303120347ca41e00d40c14446100404100004440070130300729000064840c1200b80b503560300013403500040640b40c0000074541d140d646e0000f28000d90700c0c01f0400c600e01c3c10014a900610712400a4401903241d41c0003c0d110300c = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 40913592 1250 40912342 40912351
    0x20a0209090712060e011107030206040602071e0506090c030304120b09071d0403030b09270f0d0c03080609060a0b130b0f0a0809070302011202091203030703091208090303 75
    0x400c0040006400381a00b008104020003503455408000407484c1000c0e4000e2a040302c40300c0e015402c1246452113500382000300c0346200d034998001c100700c0c0e50325180c80d0000c2d002004211003400c41d228460060040c1480c9500740140101c02811450604040440c50300c3c10044015020342c1007030000300070301d0300501c000c019041c1c0c008546031210b0340c685558074144003081e00511403248400c126860900051070039030b44601c0c440c0d10b0411000075090104018584c080716401800e486168200400305d04090840e82c500520904960786034041ca4503090070045101e001a0009070038031240740034154412100c03a0010010f0701c2c42081418003401082c40003c460068070700d410000581c00f01405001c0340503400410403209a41c0e203455039030714000003580c44603c040e00003540c40400300d503621101140b50401c49074141c441c81d0720104000104c2000e0f410240e0360703d07800300c022081c2401c003010a10040d032040031140d50000d201600b9150000e440555118030b0004c0241c08010403030341c8500001240c2d0403 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 40914842 1250 40913592 40913599
    0x203030a030b0105070602040305060609010e0c030a09030201020903060a020a09091505010c0201020f0f0c1201050f06041e1109120d14030414030a0909060b07050a0b06270703050604020703020a02 86
    0x10b100c8000161940d20072101c00500c0d981c400100001130001c08100d150003200100d07000d1109980e11795104080081c190303030030f40c0b1000d81000440d82030800d550080d400d0610900016050110440010741042c00c00c584200302c0503000201032420941c0110032030042c0003018810007590f2001c0b02019941103041c0070f03d80c18080d4429040302560b00810a0000c542c0702d510448031000d800c0d0303a43c1500e0700100084940102c26402c0628076008041c09801e10a548100d40340c0000c0e07882d5420803003d8407403411405104160a0708582c002c81c418003542800100301040203aa1f01c07001c00901140c50111511542e183c0c1140c4604000d4903070018140c0441740300d40e0011034980d140e030305000c2c00e640e5804e160950540700000b2a140903d80040b04042281d440913020000d40e99103070b181c190680306040005200341c005115440000c2c0d4998400c0740c01c508050400200c0720b00c0208602913840385030501c0924640300c2070412004d154140202648500162740a42c2482c5081d58007030342c0e0380f1030104024407 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 40916092 1250 40914842 40914851
    0x6080f0309042007030c03020d03090b041104021b071508011a090a050406080c01080106032c0c03120705060601030c05190e0301020d0209010905030703171606060314010b0108040203030a03 83
    0x548800a6038403c3c0d94106580c416507803034007403078042d014054002c002c030054092040c010502034002d02c070392004103402c00c01c2001e1641e6a07640701500303495001880c0e41d000c0e9080c420680302c2401d060040c00c0c1d40325200000d00089003440681101a030b06041c0711010042100e0050007000c0d254440b01803102c0344043d40781c0c0c0b903c4003000014006000f58014035005850400c0c000307101e03140003541d000415000c0c1c0314201c4598031000c00310162030301c411a49101c1c1ca00d007030022003042c070303000101d003810b14410003520070f0104501c0020382824003d1541042105010a840381401010310095411080c2400c04100001a1243c003070441e0280180c40f001a03040c0195036510700340250801030031207100500031036540204400c004020340020340d101c1c0c006960040041001d050025061080c0c0390040001000f0500e40040107007a0b6021380c103030a0940005000325030002c0c51500500303016501c900404451414131080030f40c03c440401ea0114100044c0e0810300c809a01c01004481e400c1c1c045140105 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 40917342 1250 40916092 40916111
    0x503040501060302040c030501051206090c010c05010e1203040302151302010e0d0b01030b011a03010e043008010e06010f0e010302250804060e030f2a09041101020106080f030904 78
    0x9006001c0d43e800a50030605007003a031588154540e00030303410380380102ea0308000d0340f01e00701a49503110b208584e40d9100341c0c40050011071a60192542011340e610a500100342c4240010a2a0800c0d0300c030840d030075901c0c0780030051008154041c8107208612812492a141d039160507101640ca0b0810440c020f81400200c01c400b010540303c0d988220b2681e40c02021001c01ca507920300c0c20b0803100c7e00901c200440040c90380f180301d42495100048904803803031880341d583ea588032901c8180041514182490310419240c685181d004808603200f02e030300f20180c40d415003661420130f20580c0030000902150400241651802c0c13002d42140008094031804e1078010b07118100114612201e44d000300c1d0a0320f00c003032408501c03810085140d0060099600311b640c0d103120010b450b02455651100c000c805070a0740c2101088a40204003140d0b0440c418202d404841800c13200c14020441d40882a2010348581c00c41c0e90a07403410f940c090003154018000140109890a00c9000c040d880c1e00440e411240b00d00d480380e100e031 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 40918592 1250 40917342 40917353
    0x120c0105030703060b12061903020f040209061309050402180c1902070f120c080102040605030411030a080a023409050a0e0115080d2102090d0c081e06070906050304 72
    0x2131001c0c001d44040e065941190345c8103003046510032116184540490200c0d460806920110502220390240400d1492408a4200000f9401c600704042c1c11503014014503030910b00c9059810f00920b414980013409050a0050000704110320803080b00319403d03401404a403000d04400c44807420341c0310b44501c3d0404078100049003003aa090b401882b00380e105050203d01841c4064401c10442d2003401180900d0340e0343ea100c036090b03008602c100c00202d5030070300000c2e0220f102581d982e260420000e080d44c1d94400a56201e0200b9000080d4520040e40300c9200c0442400c90710000e10101e111010502c4411003901107080d28200342401407030909031310390000c82c01e42a07054000c40410b011780b01c0240034050140300344040d402d50034441e0145a11a038040c0c841c81500a1201205d40d4141c81140d4a0782c0a00c0000800698044c03610a03030880c9052555001003481c0c0407540c1e01400b807a4002d44149403c0c84d03201c0c03106000034400400280c006806000b03999801c40515000c0300c005081490b140e54507402c10 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 40919842 1250 40918592 40918601
    0x314030f040e0411120c04061a0406110a05010504060b27061e09091c030204031106032703030702070602160302010c140102030405030d050a020711091503120307030b120c0105030703 80
    0x303458020300c8200170041c2070391000ca4032020a0b542581e0401c22150303180d100c0e00c66800c00c144d010007a404200400e01c406445104a007940c0403080d07003241d03200300140e912182100c00403a01601d00b155602100481c5191111203030f060501c2d01d500a41001c41d104030304086151010300172511420095040808540b543e80800824400043c0510284d11b818540a92910540008040c028030800c4107460454003e2081d0741c2a66040707031400c442240c0d500700b489001e5001407e050105a13800c4001020441c101042c1500703080c000340a9622401c100401904e01700c10303600f18000f950080484c40c1034201250301d40078216502460098840700460804500c26001500c0686155000204000030702c8400802440356000e205010070072070395035090140072405640c0000b001c00d40c41480c0340d03029180003101141c0112400e451140b20031107150000c0c2c50440304101140070408003204200c4140d81504c11001c44810680d0001d03840c8043d03c4140e03803507404030a14141803090100101d10902e110394803 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 40921092 1250 40919842 40919873
    0x5010509092d0a0b0405071d01050304033f110906030a0b210d1106041202030c010603032303011a0c0c100e03060603011b03020708160803010314030f040e04 69
    0xb00c401c06043ca0700b0f556000d010300000c0d00e0300403828580422031440c4560f40c0c2c28500030341d21a5410141c0090801183e04da80090029003c2011111034400b902c000107103080d001c40220002c8102400b101c509441c506100c821090032003600d170402052070451802c1c21101211411507155a580d40d07110520b80c0100aa9204550002d400d090742d03007105803028040404490608040329040070100c2c0c011944082d04c01d00c00210b40c1c1100c8003040010b042071100801605844c01580c0c10700c0d0403008141d08542d0654410f4001400340c802c07041040c10005480d540f180c8a50004a14640c10240001c6510f034032100010404003000440d08600c00c000d1281d1165980010a60840b410b1900401801a03c0c01c00440341310707009110126005140c140702d0341c240c0c49c0007112400c11801e00b9190581c02908800e1064a180c0d20401c01c000c800d0b0b0401011020b440c0c440e81c6206c1d280c1d41582444048900c01c80300e001d42d0b50b40100000486040f083c0141c03022960700e1149104144d03180d140000950044a0 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 40922342 1250 40921092 40921171
    0x2150c03040b070c090b1f030908030c0a1107060e01080703060306060b09120105040309060e01020a0203010e070e0c040807030605040204140907090b01170103030503040804080f0c0a0501050909 85
    0x10041112840c0400409400303000c1d150f01390080340c07a548800101c4000606043e802944000841c40c0041e0010b4519203a000740d05001a420801e625601410b500440c1e5540c0317146800560003010039001003060307a4400402d001011400e040c20300c0601700c0c2455404d52418003140d5000038660a1081e00050080c1da8456000d04c119075a1312000c1280b60000980c06214001d851061030401c0b5051103100d01c60358041d0340301c82c0c41c14500b1405481a25541c9178442c118000e8050302000350301c09018007003441125600504816103848510840c041000d8145100424100b20402400f0000502d54060305d40040c400100d5445904c0000c009014042900030502c50880030000250004512881101c0d030144003403141c8103a000045a071503440b0303985400605c441900500c0468410302c082c5500601c0b4100107440c058540100b1441c0c580c505000050540c0444440d0700381c0e051442d240c00c0241801c7c20305a0408000b50001902c94100030614600c522903215421200440701c14900d440c10b9080 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 40923592 1250 40922342 40922347
    0xd0215130804080a050703061a130e07030f050606040605060f0307050a0507060e0c01080105010314010308070f0507090608100c0e0f010e0d030e0a0e0603030418060f0b070521040302150c03 83
    0x40c81c02d02e4561020344019500e0b545860516152756400d030341c0302010440014407508d004807d032660750000300180000c86503d845802c0c004000200110f2807199a02c0c041d03002003031035107010b80411090340d0350742e0411400b03018180890300e210750f00c40c0e094942010150400a03140c03039951404441c20300441314090400d50800d0341d0b002001201040e80500300000b80d0b500011a0b0b21403005400340c8648010014400c08072030010000718a450018040b824411844681c404a054440c0c40c5840030640002c0f16055079002e04120000003000610603c6070b000d1002e1001110000f03002d4003030158408842e0180450203600ca03403aa12882040c0d1444100808a01d40b850340c0b030400810245000f000107024926181e0045180703402905500d00ca00e84c014011440c050411140e81e20030251040c1221640b52a014040780510102d602580a40311082080c3e4540381e00c3c1c14014507011541014001942e0710042003001c1c10b0200049900f521340560717043c58410701c60a650f192034841d44021900da070002 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 40924842 1250 40923592 40923613
    0x60a0b01020115150e1002100504050a080c061005041506110705030304090204080106050d020604030f03090b07030302030a1b1b032105071116051c0203011d0d021513080408 76
    0x2c628102c401d004d110b5032500d0a03108100c041c1310085954030703405405a4400c51182940380b040c0d401040e8464030a2081d01c960601950703c1c003180d40c214540e11001d45d048902004102121119101c0080c88c04a40901089000200705e0052040c14001c42c000c00c1480301d40821609810844d140041c10082e044aa0b5030b540c83e103180000390002d01420402e9405d10030300144a180910940c81501d400034200c1e46002d00c1c40d5a10000a0403510303045041c86004680014841544000303050898081d8402503130702d01e01300b0700c01c0301100e08000c01d1005c0800c8036002d010044d0382c001203a03403070717404103101c00c524902c0d55040581c4d4032040940b10702d182c5a12501c1c8a082400141c10807801403915890fa20510f05000d0210f540b034092168180d10fa055460400300031a142c5481078a9440741114424112100f0765000320382942c25840300c960f1881c068510740b001522040003001c40302c0000d440176202540c4c50340050802500003510890704406d500903010702344641c0500320340c000c189100c2129800d001 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 40926092 1250 40924842 40924859
    0xa0b131121011103091203180f03090f010810060f1403160216060509010f03060308030a0501060e030a0206090f210f010f0501051c0302010b100e030c0f03060a0b01020115 75
    0x40e50494030719542822a02e504903080101907038080d10101010742500c0303e00c02ca042c0780395040104485481600800d200038690f006110003034640c0c0030503000c4c40c0d466a0305010b220340c9084480580341082502c0080000360600d95a0080136a5943d15103404150803c8508440130441d655044511b80c20020501190312009a02d102c00300005400743e81e070500c90150390640714421881000003050341040561042e40c4940407661069000e8207001500c280c89855100003908101d91707101350b680c0e507080181f210a4116036010202c10049008060150840d40030900e14003488100c0c81c0a03201040700074185545080d142684801c910004040d1040740d042c10a50701c0b0725900d6144015468816981c1c014401c1d0300806047c6c2e44043c1374402c1e501c1780d15000c0452000e18201c01c0c0c0c00c6541e00c9405001c0b0303a03100b0644901400190b6100c401404803d0101400c156000e5142d5214036045100001c207a03d000c140d8940c803181c0880c0000e081d41c0c090300180d015041444e0a48908038200340041840407 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 40927342 1250 40926092 40926139
    0x209040f05060301060801090305030a0b0a032306090f070306180b190c0504030f02010807110102161506080a0305070819120b09010503120c010e1606020607020a0b1311 74
    0x308203d00074064a80d8410400382201c000034000b400240781000050b41002a40e00300f4024104040c5c0328070030680c0d0301d850703002072104281c18440d9035042d41c0d1410107200300100030490b04030000744040c010814800c41c000f80c1d500040c0c400281000c2c0c440841d042012100d640b80398809400c0003030b04156242101c0c241080f40c40c4000340e0382c200c4c0e15281042558510900513201074945c414604505000c8a400646074031038024400c17000c100c460f490000030444280043c10407040141c02c5204002528a0400300f006c04e40700c0c560410a14041e400c204043d07002550480301a014104030355110001c0c24540d540e407007101003420703040c40258001c542d00c99009003902e100807000740041150030b200f0b004102c0c111400b845070a0341079003d00c1700c2e603132142e009000601e61203d82d0800041c41000c5c021016040c0312003840305800e4035a00c90020000709805101040e800034451001c1c00000a05590b01446c40c40d01030020300d40740b805040b40c40b04206500854048540d401401c040c040550b0110000c42035 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 40928592 1250 40927342 40927351
    0x6090b07020601061d01140702040603120207081c080c0f04080d0806040e0601140103060f0b0306090115050a0302070204060e1503010608070e13061103090601090b0f010f0c060209040f05 82
    0x5200e402d00018034640b1500c4410400c1042c400600e0f5940045001160003241240a41d048844208241401070761350348107400c0210b200302c3c08031400000d40003001c2e00303080e15603100c00d807203810600700c040248010210700c040b01e081c98241a115512500b410500c20b0086000e180a100400034000c07501901c00582803003002c0440e503c02d10241e0b12a801d21003581c01c1c0ca15482100e910140041c412800c40e24020041810706140010307409030345d4038035109811100e42c0320b200f40c1e00c000828001181400610b182c094201d81c2c5059601843c0e945005084c0d10600d0207240070103230b0100b10441159210340000703009154101102c5201d08056001401480380008001d01c01c0d03107401070000d503a02010495804955503c0008400c55490b0b150340540c150326640102d800b00d50f80c1038805851860720f40a940149a50741c000d00c41581030403283d130100c4070718042c01486200c0701c03c1c6088081e0303401000c1060001251900c55418551031401d072019005100e074195002d03042003082c1e045020141e102e584207 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 40929842 1250 40928592 40928597
    0xd08010f12050c09060418030314060405010531050f0a0c0e060f07080f0c060405010f05190e070503100207020103050a020301060e0d1719080708101e0306090b07 71
    0x980d92100000c08603141404028001c0c0c1043c02c181640d0300d004a1829800074000d0800314100c0c19003174a414079003010700c1044012036514926519480c0704412029445241940d00b00f0265040c078002984140701c43d50740c104490501d1590070000304002c541101c4200b0b2042c014001030038028800c0104440480d116030181d80f038940c0c41010a8071600350400e50b1007016256614101d41c0c120194a558460b8800340e804090412403401844501c134024103500183c00094111420300307243c01713800e46418500120100f401c100500041c51066404520341402e4250b0004000c40842400703801d10380310382e205580c10b018164203035211661903001000074070301c01d070fa081155603101d580c86006c80c0400c3c0681c0e000075442c1000c04056040c4549800200e6010f00c100e240031201648000c0556400030a080070b4a100d012403030204c40781c04c14810798011104c0e003450040341c5481240749456400611401000000c550000c0c40050007031000300c006150029810b000c040054101201da9010661740c0d10300 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 40931092 1250 40929842 40929869
    0x60306060d0b011a1b0c09090102040e010e0402030a050a0c0911030c07030c08130303030204050f010c020d0803180303100303020c0a150309020105040e090609061f120f050d0801 78
    0x251500900900403141d000c0188032007a4204100d40c6a482c0000329130401c0034a08011280912013403180c20000c004c8508000c21710075240f82c0030b000e4030f000003401c880c02903801444140301c080c0008a0403419100080100006a580e03030000034a40100050058018010051000e003440b07191620300301a9100b600c0c0034400d20054022003400c030702c0215504820002c0900180000134400c442d940b042e0382c09109024181001030003110501c0c005544101d003c264002020850b500300815612079000003428038046a40c5950081007888518071002030940c9000000550710f0404510001810310721241265224a040c442800d0303942100d0009038058451912400c0b61441d04044d2001545c07508502c001000c1e80890b01a00501000c0d102241801030600000c42c144100300c0101d4816000760006100c141041c50a9070304200c000b401c034088400000e407200100c03002c400c0140d41147e00e80320113405032030366030305010030010841040100035000e074244491105a01c603050714107a402080340c1a0 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 40932342 1250 40931092 40931101
    0x60910030e1e06011a0705030c07060306090207120c050106090908180909100504081926100b09030307020402030f0403030e0307030f0503070201150b070b060f0901051002030906070308060306 84
    0x1084041e5680b1400101d078003940c0107018000905840031445540e0f406180e003400c0c0da80e50742038116003004283d80700c4c60303010400030070010780d160103003100400b0324a4045142840e84d0311140104007160b111041800002207041041140951065005184079035003008441075a1030030325819800078043d10f15982607441c283c407852902d2050365000c0e43c0e80390700a16a01040e650f44e5006018020310548184a041c0080024030182c00541700b41d506890341c0e0341002419940501d2041541c0d000c01180865501c420001c41101d14102e54055441003524151584150000a80780d8132030428025001030010050003070014121410602440c4607840503c43c0f0455801c941313a0320702034907002800049100c8130300c02d01d90340140001c0d40c104201307100114600c08400c5010200c00c10300c1c2e10004245000003901420b20896a10301504048229104030741402c0c03100021341b940354180119841603104200401e0b0803802001145c4071010083c203042d407290310078200a4480982221990302a0081d640041c = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 40933592 1250 40932342 40932373
    0x90c060a032306010804140705041407030507180506070204060302030a0609020307060f02060c030a09020d030809010f020408030a081306060e010617090604060507021009231911060910030e 83
    0x303c1c8540d4040c3c0d41c40000340e8860301c0e10962412a02802c400900030010040f405403942d000f8200c060104105501e11424559402000c07590000c0c500000c01040d0301000c43c02c02060001c90701218421601c2c50388511017800010b00614a03540000c0d41031186400100401003250080e070a914001c030140c03140e043e40c072141540c207034901e0a881e01c0181c200b00001807900c40550061a000910440300145560340e07540828907690801c10142c4c0410100b10070410410700034003a903030050000ba42d0660800d4030705001d60ba80c2e8041d4181c20300600c02090001030045c10b50100d03020825400240600000d03580360750004410f0b60a006490002d26000282001e11680248040c01021f040002300300f41c1e5160707160a4018034003c4c25410031402040350701c4510740610700501e403605028010341d900605a1a5000f40d000741d500c60f0300c1d045038100c840c002107038580c0c881007240c03110340204941c0b19043c0c90b0000520310340700308c5040e02d5002400c007550702c0442e9819484401c8a107000021240d041100141d031 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 40934842 1250 40933592 40933661
    0x10606050c070612180b04060f0b01090b0a02030c0706090306050f0c090405100510050309160303020607030e0703080c0604030e0a230d0602040305251409090c060a03 73
    0x4060350703030340409410401d40d403046060342d600c0008580c0010b800d0f00d60078003403164404101c0081d141c004010060005012641c40381d01d1080440c400c5c2000b10030070090000e008501c444c8034111002a000c11400700c0d50340248201c0e0720160064003960f0100da00c41001030002c0c1068001580c20034038201c0010382055001524038010341055500c40d003013000d00402c00c0098040100150913801d44040c0014150f1140c0c2c45106000c42c440d00c41c00c1d100e01c4c000d4001407609901300c071402010388006074100003003034000c210302e034004c02c0600d0701064186140c41441e2a00045510007401031000041d80110340700d0105603180660302c00d544a420b110811400c100c1603503039a0155125803008002107810304203200075070509080740588280c0640f006516994101c1e003042e0310503291500400c02006c18081e01e00341400802c3c01c56042c01880c2801e0448203950388034a9110a402400b0306c1002c100e21a20402c03406c0800000105069a540d030f044400030080c2500045051201c40e030110807504446018a1 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 40936092 1250 40934842 40934857
    0x9030307020a1514130306020903010f0c0302040819020609010c03030603080304030801030b07020c0a090f0f02030a06080607050a0f0804050309030d030b0102070501030b060306012303040c0e071b080309030f031003020301060605 100
    0x17446004a041d529804000e42c802854141e26640e6408404410449800307040c0c5e01001c10b860040c1c4881c500709205042c038004080c040850010b451044c001a5502002d07182d4018081ca04140c00110500d0b00b0341c000c10444c1c2010b486003174044100810103034004d8610381a0f82c1b04843c100d042c2e40b6111401d90340c601d0304203103c4d80d1020a201c8140968002d07079000b155030524920f0003007503886e8903407010012030780181c4265101984134102403003082c1e02003186039080301f43d92900c545010000c00000b0f045000b50000311040114503001709060160400c00c1c1d45402c1e10041c262000c1441007100a801030101c4013026004d40240d0400003160340c000d110303210360103402403d8030b80b0b95500e030401190f2070724111900403003801803c1d014900d8041d405c03020350710807807040d02e181100302e05110a00b040705e140103100c9400c000d407030101c80321380b40104001d820046070f101e440b20b926a143e0410741400e60003603170440380300c5120100c10081c2e510b503e0200d501c00c4070b000350020041e150700c0b000216107910030b061 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 40937342 1250 40936092 40936117
    0xe03060f0a0c0e0604090e0c06120a05040c150f0305010f050108010e060d0f0803070201110315040b01050903030a031a062a0a1e23100209030307020a1514 68
    0x3000075290000303500002058000d034a407078a03104954500003030444d001500082195560366803042e404101c10010b04481000c01c40382941400151350342d4014100c401081180c1d85615076000c81c00308152900040090039840d0310320003845a80080003000200d4220150000904003000058606080c804d1032003034440c1a9210004d9070b00b4600b0107440400050321407a0400109595003000c1191000c0c030800d01c40c49487c0c141d40c0c03030400003802820344800c42c40c25085480d0410601520000510600e60b1410040d1000b144c401c5c3c803e001602c0f6802002c0d0704039014080090491016641540302144c554104292000b201c0464800c0c001107024003108007a00c1e20400c602d20b8081f040300c1c41810b28192401007103034103500b1a039807600c901c41814540755540883c1c4035880b00400102070252000c0350301072000301c04075a00030b81c04076585002d41701c540201d46900250b1441d45440610407551030540117002c00a1050f0f4070914000403c2c2403081110000c0d03400f11f40205880303180c208942010101b070 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 40938592 1250 40937342 40937371
    0x309121407020108180f06090705010503060f040c030b130c030501080606060a081003020a03030908010507020a050705010c0c030614061005092b140d0e0a0e1b0409020c010203070e0306 81
    0x603030040d1140704c0050160550141c00500710030600b50100507040f4005003540281c02c0c40e06000d900d0710710b0403044c0c0e04401d040c000188100a03280e22046100c0d83c00c00740444010031104100300040e0004c114005060350880329620f9481105002d64100c1c640b205940e5030200050b07070b41e584542c0d4a461083c0c0c2c0d110742c00742d401c100c20300c200351180d07140302e40051002c41109121681c070360024861811507401200400d030190003c2006440038451140e1000c99400034010048056840d903480d55001d00400d814402d41e80521814800701d243c0420284d9403044081203102c45510703040703040360b10448145120703440e82540b038400e051103441581d078034540c0642072250f12a032288039040c8032008070381c0c2d6404d8110f260740a00086000c2d1680c14001441300c0000e8561401c40180043c61700440c2c10f0214065814004100700c85901121079030346c002e01801c50000354080444022010384600e5001400b4140003007000000a00c042d40214001c00194880c1c000d44a02c94041c55103c1c8000c42d80b410191401c0e = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 40939842 1250 40938592 40938607
    0xd060e0109080a0f21020a090801020d0f05150310110403020a0b190908150402040e1506090108160b0c010b03030f130504051314011508070510050910030915060603091214 75
    0x482d0003401f00400541081070401d510381c09110308a0b04030307801100d0040e41301e249070000c1700390a04c03441e0741048890310443d4010750b014000c02c1e80d8105000300d0b03522881d9201c1280518008440a60303001c2c0d86e006000982c0c13980c1c1c034810680c0a07003101c1805d008031003040600c007a52034000c80210048800000140007e81040c240f40d0300c01030401082a608583c84400060380145c051208280c50909050140e14500b030120a122807104140c2000c00341303905c0586650752050040b0b59800031110000e05850351984520082400760040c1907001e5014400032540661180d9900003038088446051100504070740c1d035a0401054602c15581c548031040c2101e6080045050101d410840420302000810003a1301c06150700001c1e030141d071140007550005a000c3c840c510b0500403d00c510306941c500079040180c04400140c0900c8200d001c00c050503a580501810040e898070012164940400c7c20040b0343e9075200d014001d80108034086501c50003005201070160b003e81000902042e1040d00182031424 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 40941092 1250 40939842 40939907
    0x30807031805031908060d061808070c090f0614040507030603140c03010e0601260a05010c03020c10060b03010911070b0103050d23090d060e0109080a0f 67
    0x1018024408041e103860500c100c05035529800075001d84644000c5130b581c0c00d07038800008a80c200d08821340030004840d0601c041966440c06a4809035084003000821901012004503001d03101c4400030088240441c4501c140044c5100701c000302d4a080c0c4003802440319a030700c030100f15000f078080c203410f10000300d0070500b10b0700701030f40416885040c034100001c02c2604c0340c44502c02ea038080c8003c209240d000600320000b5080030300072140d010300144010101c40d414a08003105040c180164156481910085c40e801400100b002402050300040208191801481e00030044c3d8001d0b1354441d00741c840d500c1e8440d2001010312601c4103c50103c5611801d5900340308100000d4107041c42480348500092140300c0c04500f512404500851280300141584012902e0180501c008450034038280321042610b400c00c018444202c0b40c10450032a0040829151450300034010180b280d000c007619072a1080c0101000025001884001000d4544038254101208122000000c0c00a401c03820700000c00041100e03074 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 40942342 1250 40941092 40941107
    0xf0303090715030209130507030b04051902030c0f03040c0608090f0618010b12070f0b1914040314070801050a020406120903170c070b06010c020102030304020118120507081b0d03 78
    0x802e40340161034101030400003440c0d100070a44920507a40d982d0284070149405110b04200c44406075400d220528007140031a200310a16209800410340010010b01d001e01c1d00342c211104145407991068582c03d0904204070b0042140c041c85002c1100350000c500002d42c0008c0317944188ac0b0f0348000300140e40d148041e12400c84a000500b003c41d640311915a085035442400080d000c1440c0001000c6141c50900700d900504581e0740140c112000402c400030400b181640d406902c510750b070500004a09640501129900c07507a44043c10001c0d8048140340360b407202041801c01c54000310001d103c41c5c6c4601c82030108a1040780705200200300e440000500511403900101d003481c1c024142644549a180b00200030610708a03900280c0000000f090380420005001c1190000001e103400340e80e4001c20742c0042c2d680c3c40007510182c14407140a1202d10032040168190f0040c010b02c800051140c50300345441551a001e5000c0d060490244144203140c2c400344007224850f100004084541c0304001d03442c2070301c40c1e0 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 40943592 1250 40942342 40942379
    0xa0903021005040224091806040605010c0b1308070b0109020315060a1b020303040803030106180b04060c030c060603150b0a080109120804080d02030403090513050c0d0c0c14010603050f03030907 85
    0x3005000d0310f4100d17900c1640e0303142d0200c0e00e06158800c528140e400c00c03040311026004a33051002e4101c1250100d1191071803143c3c44135038120780100000d400e0910b00010f0145290041ca5400e480c0000702c4c00ca011600034501610303000303503000d981420031810005071307000350020180000c1e01c202001e030303080910881500300320f4005000e0720f00d06070301d800c1c00d981150300980020011800c501c00b0589000381e0030328414002d040c03409040d824642840002081812905000380800010f0b440b03e0080c0300041e0711100003107901500c0100703161a1070207050b0280640d50285d511030312000780c0014280b50103010710268550f00c40f010101018580400780c8003541f001e0416500e141003800382c084c000c40c4502c0114081c0f4040c0c1c50320300042c2d01c1c15042009464000c810005018181001d10080084c1681a104c9c2e4050802001c104500300c25000c45080d5820900503201072098507944000d540194448130940e4015002d949014490b040345566902c025500c00ac0300c0c0e0301c10401001072038081c0704142c0d81d1 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 40944842 1250 40943592 40943659
    0x120c0204090b0403021e0106030c0b09040e010623090130050a030507020423010b0a1107030b0f01150206060d02040b060d0c030b01020f10050402180a09030210050402 73
    0x4481d8262540d01c0100c1e01100c044002d83d115041000c0c145008140d0400c012140d64021305c40700e81990b64500d00c9880f1889050900d25000c2803103201592190003030510340e0030105c000c014071680d07281c0801550b441a841030700742070309d240d03402c8c84603003090983d25068a003064043d880890391055421090340e02185103020425021180c5400070b54240448881070740641d45690b03c0322058010402152092180d0040e040c4408040400015640c401c140c1107c00c00c07a015511041c001c42300b80ca0813a40194500414007a2800200030400d0500070326005003031132014041143c1c0c85051a08000d1301750030700000940e0001e0001841c1d8900100c000403540c2c8050300c0480c15a00c43e001044964020803004d51426413162002d031400e42c2e00d4070446140c405d00b440244000e081d426516600c4101014520f01d8031a00d0341c00140c00c0d92135000305286082ea802c1401c1201c4d2414043c5d860041040d82c2048006000d15149940500410b02400703000b16001449600c501914031a4800a040400701d560340 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 40946092 1250 40944842 40944851
    0x80304020118080c040c0305042301020c030d0f06060311040e0a02040f080c031c0e0d1403030403020706020f03070201080f060a0b0a18080d0203070b07020c030d031a01080103120c0204 81
    0x188404001c1d0500e00600c0c03c5001010b0203000c080800003a1000200180f041501d020304000100b060b903942c0d034200c80711810742041c82400743ca060501a110b00b0100c201c2510000070011138200c1e1580c02118403144000c0100f0010f038490800710b0590f0355040740d45001c510240310500c04080050b010036041641c0c0d241c011f20307003503070388078124030380d00b210b42c40002950000030500c440c2d8102800180c0f5208246031070f0360342c814104240034052892001806014070f9090100008000c456602035000740c01080031203842c0d160501c0c00968420050007544014024404c120103034010000035102050f0f0305840f001d0b8640e1760441c011004510003441540d02c0502224001042034006e0000c0c01d00352450fa84031040301c00010310b05000c83c42613602031a241d03801454404026075010040d04c100d154811540f1000d9111908101e1428500c804041d516000300104105000e405a100031004c003949a080551045020019a1000001d00c40680003480070310860034483d100350549500188020000076 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 40947342 1250 40946092 40946117
    0x20616030b030d200c011e050408070b0901180b090d061503060f0e0a0b070e0117090604030305070807170705120c030a0b06070809040903050702040c030b0a0504180803040201 77
    0xf8a03250a1160000100da804d0582c072481c0031554030000c1c01c19001303000400c001078070080001c0ca84a03022010134451042c2c942e011201500c41c000f11002003407404102c8803056150341050300309034883c010f4140400c41d080d00c00741c500042d0300d4201044070154400c40e4280360b2000c1c280a25000f034041c0c100c9926036205440100f800482d4550409036000785000200300c15401104401c44101241c5032065610914501c0300003401c030b0304100d038850410726004210005131382c0103942c552a40ca003030b8070980c01100208010b0034000180144640c0c040c0d42c003404580ca9540c016a8100400e4550700300203040c1003104d244400c6000441034101d88907180030b5152501000c4407100e1070800b1344114001c0300d400024403496403068021520845c9085910b545024560350310340b403542c45201c003180d00a43d1140d030320100f8140250182d52445401a20501c441041e002008004211100700244112500d0030085002d08003441102c0d446094044030f210024043d84030500b10b0380006004904104400f0700a1 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 40948592 1250 40947342 40947349
    0x1302090726090d1706060705030403080406030902010206060f060714100c051b011415030106050d050c10050f041809080a0f080c030606090f04090b1512030703020616030b 75
    0x701d4110000444041c10708000d8503040c00c0940e071103008003c028440d001070101e109030050003038005070100c1e64240c0c0d034091860490700314000e5500c0076080ca500481d00061041e0160403c42860f4803da080d981036907140c404201d000b0145107005504200e09208020004120170213035600140c50b20300f00c4101ca0414a00c50040d92030751a000f0700041c0300413581d50842444d000341c4020382890300d0000d200c0d40303d054800101c1c00c0c100a2560084ca191020b014920303842c29032041c4e000d050045c10003034040215090090f035400c1441011030081d08a00049482240724009403511183c0c8401118036041c07030103400c0c10082003071181c8000919591940f000c0014002030090089410300d0f144d0501001c891180501108401402c40803510001c01c200000d50b500c078001c07101c282c5d500b107800d480d01c2d1080c200828000d0420b100001c1415450509218903030342c00340900f4035420012501020798110f11018180c80e8080e400008016910020100300d00c0101c4222002044a0340d00c1e0004030b0b640e014000 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 40949842 1250 40948592 40948637
    0x31302090910060801061212090506070f0506070201110901030e010b0901090905060108060403020703020103050916030803160216052e0504090f180303020a09031b0e090613020907 79
    0x501c50691204242550410550088100070414032000b00f02c6940707425900700003c0342d1441d000702608103211082c20305c0350151907101c01816028060540302c60103442d200580c0304000c1016145446800000b8001d28814007034902da441481403034509091410340190b010340340348201000c136035491b862001400c0d00c0e00b01006000707008002000c9210340c00341c10441c0c100401038202e09000d4210300d00300400f003500050385404487d030a00e00019039950b0300c4125420701c140d5200040a0007412040002401340142c040c0d03026266140010040042408060340d8814141c01c10841305100d22004110b940341000c458011083e45101a0401c0c88404814241040072400340130017103180440c5c18081c1c0425440385a801d201c40c04e4003000210703400007490480200040004040580001d22500b1051003402610021030340804040c0d03220003d0002ca1807845498007450071165002c0300040d0b0448000143c642c05842c2c1c44010000d21007440d02803000509000f0003483c1408985215071390024483c0da01e = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 40951092 1250 40949842 40949851
    0x80603120313030e0901030b040807080d090f03030605010903021311090904050d0f0c02241b0a0b0a05011503090f0c06030e06070306060f0305100b0a0203070c0504060e04030503130209 81
    0x442018080541c030b000b610540131900c0c401d02400620005000180340b0403009034125403c44000c03a102c000500e40407a05214903000122400e05280320982000302d80c40c00400c11078400e032070070700083c1c0c1c40e8001103071188003900c0041d40c45124030003e45901400e551001021200e6140c0d01841c20800102240244000f40d074200c609a0201d15101440d980c0b101d10760706202024036211010441c0d07a00001c0e981c0022042d1502000e408040c1d41e01c404400204603650b42c0c0703081989002c4d030141d800721161100b040f40c0c2c081c0c0e03900440c000001d600e44203510815058814164404051600d91385080b00142010720381107401003031110b07041001c102400794a41c001e2000c3d03500824840550480c00381042000b5003c0070030b15080c04070070b0002e80d403c80e0041d4000e140501c1c001850b903680c0c130b0844c0c80d00d110545c4618100b00e0700040606c840da03404801002c0060085400d000c5069a50041c40211903091040c0300d98140710300c0c0850002845a0015600705030f202030a5807110440c1d8002490b4204250f5 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 40952342 1250 40951092 40951111
    0x3110a06090804081207030c1b08070f030b150607200a0e010302040b12060105010f050f0403030306050910030203060a020d0905010f0203150a0e0601050703051c05180a0c05010806031203 82
    0x1c00f00021042040388844170400c8400d0541007105559002d000242000703030042c180780490f04204868000020b0079002042c0f80740c00c4903001c075135401122501b03910034002550054180400548070b080c542d40e4203880d20700301500541c60a016520395600801d58420344030f40207600c80d50f02880a40c3c0d5014101c01900c0701c19044100c07545107204010031184021682c034004c400061818840d0071020614a04603a030a00b001502c124498004031a40d1084000f82601d041010a010003403641c03560000c41519000c0d540c140c0e203034541071441c0b40c0602251000a500d60f10400c0041c02034000c64019109840240b040071030a507105a445600350f400c0ea4098400169001c02086a00c074403001c0b0015004034242d458070441810181309900c0f0717200050520b030522900040034820140320b00202d510844040400d9a100314917496400c0c00f801098682e1300242454008615485001007280004a507101c2e07840043c192030080151480c24004200f650305000d58100340f03905920140046100d00c0c1c854 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 40953592 1250 40952342 40952347
    0x1a0d1514010206040f060b03030f0d060602060606130b0f04080a03020c01030609020c060f040215030a0504030e060307020309090901181112060105030a1106070c1401080903130303110a060908 84
    0x31115a4000c84103414a0455000406101c0030404492911948503000391001c500750390990082403071845144105c8034503040001e602c900f0b000060340404c061f5036003a800d5503203640301c032410405175001300340341d28120110850081007081090002488015602e402d4142040d588101403400c02500b000e0990160300140d40e12003040d03a061041310050040a102113050245906009a03100c03401003541c1c480c2900d1740045001d658510b500c100e103400c62100c42c43d0392450042c2c80080500000d8a048000c182501148c580903d000401d46e40700d051698011400c258100c0200840e102000d001e85501e956181002840c1e940740d00c1c14041100d0140300b0b034540034101c190900c0b5044103141140290b580050006100d25500440c810200a41011b0782a54a00100d00080c0700307480344e441c0091169041d041c000406517001c1b810711110301800d8840e208651307104641c50381c0768442e411112061002000d420720000380036500c1d07416a00c1501c000c6135600c440c0d81d904c0310220744c01d90340300b5500a07001 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 40954842 1250 40953592 40953599
    0xa0201050a020406090e091005271207060c0c02130b13090c050907050d02040e07031401050906011407140102040f09060b0702060702041401060818070305071a0d15 72
    0x9006058101d040c4040c1189414a0321500601002c8a0701460760083c1044002c81e00b0704808010051590740c060f0020040c0d030600b018880300d107a08150408004c1716000e003604050090215071242100e8080007954900384d115907648008107410b1005406001c3c0d0301c500400540c41d0101d03090301152003841d000501403041010400099401c204a004031420024030300005549400403104846041d6071000540e240d02d10182c405001c0d02d80300002040c400f20780058280359800c0e190303015051940b001c00c6805a03643c0e160545d04d509020359508290301c4e202207552944241c3e900c41c0c984d00b031240240d0520007255602203030712507040c48070f5020740c0d0045028090004030400250007800d03440c0301005007503d401303040c02c42802480006480307800d001c2200415500c49420828550700f00e40150095907860341d6028200c29410307210f6009503040d5500006201c00300107000c205807074100005101c0d91380742c4a251030a8002071035610b800c0400c240988035210354039008c0c080511100f00f00b0208906d08 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 40956092 1250 40954842 40954847
    0xf010218030303100303110f0d0810090203100303080c09040501030c06141305060d0b06070507030c0801060b03060f010516050d0807030b011e03020f0d0509070506030103080f03090718020a 83
    0x50000c440c920035081041070082070200345074141c0450b036050821045601110501e54140803000c104440b0394007a210320f4105460b803001815125040c001d000070f103202d45940d11002280800c41d500b0b4140c002c40c05051001c00e0081e4603c0d40e0004136107404070300d0030403003c010030280c0c1c1c02070b0300407a013840011206002c2c1981100703151101d481c2c5411000d0810908a860204804440c450305005803000205c4520848654020980160003d040c182d5100030a02c2c1040e5100344910058174104005180412428018090b90044454049801d400d58850800f00130021041c01d030b00c0d605103d0704000402107040d40304c0701d05c6507050045010308032641c003500e0040c051510050148041500d03010361746916a070803210000e081519820480301d5503610744003c0d0000e120380503007802031840114010856452941210303205402003c1551030741d503525000d104890000b8040100400c1e070901c40060200c5945004e075034400310f481e040341e002555564500144602424070042200e8002446015164 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 40957342 1250 40956092 40956127
    0x2208070503060903040303030b010e04051501020c01020f03040b160203010c05071104020910081f08070f05040203070801052e03020a110609070b07060f05010f0812030f0c070807050f0102 82
    0x280c0c0900740a10f00f101c40980c980c4100e0000a003499034030305401c40c1507441440c0040055601400410207410600e0790113a402140d00400c07170042c800d410488106520200d44001c074180c04030b000318205801e065042c0358a411000303400e44142c1e41c50f00646c000da9024090f6450521450311944e0741c0f0b45490030700c0710061038140c91942c000c0c1e0040004010703e489865581040422925040c0c00546520114000078076004481d035450000318440802c004c00b002c5030a004440744640e0b00c0075504d950703101b80f20690004492800209850713000410150915030b0301c414086001e00114100240d80c092807280348040c42d20781000090307021643c0d03010309811844000c00f4000c2c2100800c0035191501d10240d403070b0f04602170b86186800124020080046a42210002401e480014446903840340a41d40710880d451290200f50300c0740d180c0050740105204101c1e4060607030400080c00c5c55071820f0681403070703520810b001c58818004009800c00303c0e0b000d002c45c420900e0f401c0005603450369031410544228 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 40958592 1250 40957342 40957349
    0x12040f0608010803070f05030c0706020d02070603090b15030a0506090d030608011404060b04021204110102010c05120601050a270e06032b020115031a0705040302010c020411220807 79
    0x7003805001030115031000030035207444903448280c011400c0c05500e0483e065004031200c0505a05c90401d0109405402040e041100c1e080c3d5821114203503650034044080c1c1d000e141c0042c194444100101d05641010031780126170204c003800700d82c8007920700c4e5607443c54103408844e8094941c2100c200340744445c3c1d02d40941c00050107100b0090100044d507407141491503001800051050b82d58001d40e041948654058900010032413003400c4191500c0c0c03d184a80c8500074000600552828a81c1000d00f4011030a403000040e0580521003039030b40709401076603d076011482c62001c1c080c0502c07503401070045010038200390f4011030200ea01e4103890312884681d006d00c05403000e8420380182d42d6080f060725200440e08041c8160440d80301965650304801d03401003568410108001500200c0441440041241c82d2500306450820380a41e645030f034811213060240b404001d000a003111552809464035401038610f01e452150f4084c541a58005200340c514801c058807580310742d19010400404c0e00600404008 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 40959842 1250 40958592 40958597
    0x909011d011211010f14040f050301141003080c01111602040c02011a0d0c03020a03051c030c0f03090501110a0201090b090312010b030c0706050c04150c21050c12040f06 74
    0x5103003443e0349510500580040e05410840391580b8000220f01c02d888108031810024441c40d40e440d145c1e0a00051484240540c6009600340300e413048602044240c0c40e4841d0a00d015100c1c40b036421540c030804103a2003c6207641042d1f4075032410024494500d001003c01e403000401c0c01d010410306e44140710035198070801c62030569146c03803294007079400102d0f189006401c0454411054414628017036030b03805030b6070704083e422030b0300400003004020001030780c0d41000303914800b00004080040011400e846400d05160001070550341c9400c08280a500032404c071b5407040d030000c2100c07000c006603203c582d00104039490043c0c0d101e0080100b8000340050036500700c2e02e00d1010f5032611909101e000540d240c188503280c02c2e03c0000000803018010b140645032210384c01030040c403960404c000c05080681160181d0b0800710034140103e4030683c00b840c08080d0340f80e0301401231000d00003140e24101c0c400f007035141c1150501204000c6804c0c000c1003400b950f00240d610a541d952a40e043c13103000108040c854000c0350a = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 40961092 1250 40959842 40959869
    0x100206010b0306060705282609040c05070b09030306040c0e030316020a0b13150806010f0e12030316030c0804080d110405130506040e0309060702040b03030909011d01 73
    0x540d98041c4112a80201d040c0c4210355585100d260062038512580c01c1d4807410b0384511545141d200030000c0600c0068080c1503503246840c6001e0001e451204040d03506031680c0d200f048000c0217401c080d04203004500180c00c0c002c1c140149038650310701c900700480b03030001c1d103030000410401685450300c61040c00c1e40c084d20f8620304817486440420781e244070311820881a40319100c03646c02190b9991100102402d004405a51100c1004011084c055901c2c02140c4140302e0800c00045640d100700b61040c0b25000580d10512000f00c0030320280c0d5025800c0d110181c200038805a40300c251041000294051040c0c00c0788074a50b185640001400c550010990b0410408103070203000c04110403000b07440d2240502540040c2c00c3d44100340d07450342e80c0700301e9101580080c60940320140d801c6a5a0213144a00c100f82c40500c104107040e07529680701d100740461030350b11140510008025040651111146610180c1124a0400642d0015074900360981c00000424400003200c0d00000f40700d8003050050004514500 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 40962342 1250 40961092 40961099
    0x60e1302090f090307081b07050108041e02270a06080a120f030f090609140619020f04080303040f110a030b01061821060b0d12080a02070501060e010510020601 70
    0x201501800780405001c1650080030510990f0240202c034003445c1d005010940d5030340f0b80070300d000041c8050300d040b1a050140c010001415401303800c500b0320455002c00e00300039105400d07401c0d0314100c04100d000d0b81c1050a104000c00002d000143d100c4950310202c9001d0f5552420300c04c6001074400c43d0300101c0d91030f0442200b100015841c001d01c6401c031000f82c02c1c03080000b040d48a00b02e00421003403000490050825502100780300b0350b41c0c0401041801001c03103019048600c2c1c5880d40e10881a03850a1246c412a000d0342251402e03940a07107203002c5902d10451a143d40c80759403e2031a00280c0301a10780014400d400700c20841c0c0015000d19000341560744a540c00d2640d2200034004005114510500c08040700e00f81c0c94401303c00c2000040c1802240400c620303040d41d02e40504401250108070b03900b81c50444403400b41e00d44801d0714141603622400b410034000380130030308880d03541000e0480000c4035000d00044c0b0010b102030180901401800c1c030040b01641c074082c1000f00307002d440d60b805400d5410040c01071 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 40963592 1250 40962342 40962349
    0xc070204110a020a14030909010e0412020d02060c090303070203120309100603030f0f0c0c0603060f060903081602030a0b0108030d0c0509030c0913080f040504060f06081914040303060e1302 83
    0x142605900100a41021740408018606501c601070781c40b82e0110300368002041040c01d6070060382c017a90040d416500756000c00c050507660b40d400d811950b805680540d000171340b14103280700208800c3d007026003520700701403040d40442d2a00081900c441024607010080040504003003255200c00d4128040600001d46142c401030098030880c0c0400c0c04002034091100e04640c040c1c401e034030020b64002e0072001820f0340c5000c02002080300d40a100d0415250040000384544107084d42030075642c00035541031400144007075941094800031030490b007500680008001064108031124003d00f89100550368680400080c2070494260003091010b00406001c1c04280b5103000038503a9030804203461100d4251200c02c1300841003400c1c00c800422f601c00010328003016000c840c001d0030403500242ea0520800380c8900e8011140e400ca03000e60310002d81030200150061001707400c890001000c402c4009000c001c69056000c41c0c0c0c03c1100c0c1603002c2070b2980010040380c14034211156000744003a408100160340c4c2c5d40003 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 40964842 1250 40963592 40963603
    0x60c07080609030a0215072703141015030209240a0b040806070306060e0409060605030102070c0806010803040308030c03060a0906150e0604050a030611090a030b090c0301090803060103051e0c070204110a02 90
    0x10303150000c040c1104a202000e00e2014901854000d20064070412400170340c240d680007450bc07038038062030404c0141502e0b0b030f843e580034100f980d41c024061920359031565038068002c12002a0607101c0351412a4600c01078641090442c00341c603581d0300c12a5110300b8258810314000340134041c60205464803200304101c0b0750241580d400070f14101c50200f00007505080140c05031003141c103c0c40c0d25500c001881c200b0048410800000c6840010940d050740ea41d400300c15451b8081c41c807003e054654100300168556410500031640948001c0220000c9503e503440300c400c41d001500003804442110340441120798100c02d40c0e40102c40121111440c160421010030f50492062100500c00342c1c613511031100a80c514400c0d241c04403030141c1002c1050f540c0381001d441c0d01005030f84004460140e80c0500913142011700489029a41001100f0b146480c6c40d00114020140144030400d084800da804210101407040c2da907000324090700c142501d4035030900400085031342c1c10441540000041000d81002c0d031300483d0 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 40966092 1250 40964842 40964867
    0xf060905060304062003070507140604080306010c0c0f0306050906180706030e030f12160206040b0103030804050c0a081b0a140d080c0f01021b0309010e060c07080609030a021507 78
    0x1c012403020210580700705141e40e42c01c46180605c10110802c900150300c0406002c0190080c041040c540100c9900e40d501c1300e00546001e000341d00c0c10400101c1e594000e407400000d035442540c070440704683c0e44c0414005400036800c215003203519241440601a4100000c640004142c502003032241c00300148959a90142d12940f001d054837809007414002c2e05100381d070041f03030340d6445807543c51503a213194080700c0100712080307514a18070455291140b480060400c2c4102e50140e1960b00617400c544080d1404030000b44215464868000c820b80c0c075483d4890303103c005200c10002007031403040f04c040c1c80107042d02d0101e030640205180780c010010036100004038241d941081d201d18294121074108840103104041d0340e51180c1c428540401303130200d0154000c4c080d070208211400000310942100949134800c0188140c0000d1031600d040300f0fa894060010100c0c440c1074003c47e0030042d662481c40303003040f07022554101d05420109020320b810ba010b212100c407001e90b102c1e1561107460100d1000d4900c0030382e1036 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 40967342 1250 40966092 40966103
    0xf02040b1002071e0e040809030106060206040f0206031923060303210604020c0703050a020301050a022803020c0a05060103020f0d0503040e04290601031401080309090c040515040f060905060304 85
    0x200034000008030244c20b02800c3c200c01c02e01c43e185041d0400d00141c0d400f900030b06019606c0c10742c0006445102155007070046a1200017610090300580800c40310742c1028020030603018100b15034940707034030113071142000040200d0700c03007201c400905c60032400d0701500405840c041d41080092100ca0404072080f10006040c1e40c0c1d07895166114003020400074020004a03003454031807540080300b40600015901c80552089000b4000790399104004403d034080c040b003807410255480040c2d0b042c0b8110180506030704005180042c1440d50726840c0f40e00d46140c00c1800c0c0c1d2190070241c0140154200f0750340c503080643c0183c070118401040390b42c40301e0b0b50784120700c10702c07079a14402004241000421281e50309022980c4106040b0005544e101142c41e01c1c00787d0b2a140070030b141c80c0d007a4000b45c0088a0881c101c0d0300b98000b56040c562844188800444001c01989800c00308000c0070815a40b42c0314580ca264121540751031721141041102c80c003e1072141c010b202400f6458004100d15a240400c40754000e40c000f = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 40968592 1250 40967342 40967369
    0x30f01020c151f030b090c0102010209010e040207030314190e030f03280212010602010b030d1b02060d050a0507080c070203060105061b01050a020a0f110304030602160b01030f02040b100207 83
    0x1c014030310700040318048070140c15049090004c2441144c80c162030040c00840c0640b0100c0140340c0c0160b0807885001602800b01d020740002c2261032409030b024000e214003030706011404000311802c0c040c1162045814043d005446400c0340d810114500c21006941007400056103005018401c40c446400f0040004d01040506615505520744100600c6040d415180066441d0385005000d040c8801090040b0f100641c030781001a680740c580012001019040d944800e403a40454156543c0209688002680c0101040104c40440c1d24607100d582d104800300000060346013000e440051450718083d001090a0780d080c00340202581c1e0204907541110b004603442940e80d0000f02c1d0942c0f00030019024620135510f00410044000300b590014040411280e40d0101d51001c00c001c2a148001c1d8852050081e500610003800000c0160340105200c00d0240038041d50304001d6502d020000c030003600211582452000b8a10441c2064050740000d18402c41d9403600c2c2c41004070000f55143c009101e03080703020008 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 40969842 1250 40968592 40968601
    0x90b040b091002030a050a0b10090306020306030f16080d11100207021522120510090302030705060a0204050a0b041202010e0a051c0c0b0a02120d060b0301030f02030f01020c15 77
    0x2c11040341d82858145003952646001202c0d000201011190215902c0c10001c10804c545400104100c9000007626002015815600c624009420040003550103100314400c0c888808400c011070700c02c3c3d1501c4602d40c040c29061002a07401c2035210400c440502c0007042d016100d884012581c004584050800141c6406d06400051070481c0c1d407031f0303000900e28800649209002645d40440e000c002e20340060700704451f40d945041d0b40c0482d00100203046500004001141071000b07400501c1100c0c02403045900f85007c0c3d448083c108130050380c001d18200c0d40001d00b0411400c003201981d00901c20030091a08261a0440c492089280400300074104981e1803604080c503581c00c100c9401425005d03180304211801598400003034800950151005405164001200c01c44402201c0421415502500c00d5a0340000900515007110504500303070390b103a59002c0756031003034031010314001c41c006c84a6841e440700e1401030506180780611204103907401000041e0000f000001c04007010f0b01c9124146001750740c0c = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 40971092 1250 40969842 40969861
    0x901030209120a030905010816031505030102030c0406081b191106010f1d10050928050403110604020918031b030a020706020106120201141911010c0201090b040b 71
    0x2481d0155600a061120351042140c00043c000f80705482500c5905c0529115401540c07600720071510682801c4c00e440300758180a1190708200d4250906038400440d440c2c56000003070980e00221100e1303000b6070022804016943c0d2041c0051b402103520100c60004000d1803581d985c0c184511422080d139151500c505404140c810845c00030515000310981e40d0320358480008008084081c0304540201102c514888021725803915054003079030101080624152800b1b040c400381140040190010141241404a007005040092803080501100000d82c610303062034060000c0c03401c4000c00302d10358041c40820006844103014603402101920808403044001c0802a1840c4544507085d0710700a01c1c4800502003100002c06403043d0302d0550255140070781ca0301022400c94401d48140e05a10245c11240c42c05540991410800c40440415170b40ca4845100034500c80803174003070340c0100040d215403888440060280321301b03511064103100a00400c456a00d0303100801001900c080c0404d201c14012501060 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 40972342 1250 40971092 40971097
    0x14010e060901033e011709030a03051b0711090c0c0c01030209030309120102040501080603030705030313080d0e060a060f0806011401020106050306180d03090b180c0a08010906110f0403030509010302 87
    0xd48454030700800e00b40d40e1000c403a16520090104d030109205c016040da000d003110301d249100b00c20000c0258104035100c80210041e000180a0400c0441b0180c50451030460840062440b01d000760b02c06c0e595000070f5002d1001c0d00f1802041e2a40e10b00040c410180541030107e0301d0120b0034801d20b0050303203c2c0c6038400041d00b035108014045a114204019040410006402510031501d090322144e44036600c0d44189600c901c210400101280c20400004240300b0700d60000080c081d00403d4001c2c1055524000401115041d103d0070503035500103070030002e42ca1058050400506030788186a40d075185001c0d120f40d035420040c01004c9c103c2e003440c214064140d100751720110080ca00101240e20fa07040040c030040c1c64000301800003006000d007200c0588150b0180c0074804070541c1c08041c2d48101d680b2105c41c02d0a0004000451082c0d0180d01180540c40d503a0f0448000500f80600c00041c0e000c0721380c64254110343c4800035030f4060b0801401301c50222070254080c1ea0490303400d8105142d507003039201c1c012002032 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 40973592 1250 40972342 40972403
    0x8070207080a0303050f06010306031a0a14040302060411100e120f031207090e070504090b131d010b0a0501080103080a05041211010201050a06030c1e080307030314010e06090103 78
    0x14407401e03401030145031389134100700c0c0100001070f69000ba580382e0a00440c140da02c280805071020070140c0450031115106401a6840078840c3d400140d081ca00204010109400392803d400680c41082270109220f80104d104203103450450b69040d4100320802c001c0c0c0441402e00f440c5104020f410b143d44480e80e010b000840d800c0c1d02c0201030769030312501e408140854120a940c9400000c219000c049545800c03159418020f00303031901e90700d040c43d18102c0003030090700c0c0911681d90005011496103086841034040c902d54004210075042d13180c0343c041c0b00b203800c40e4045c000c441d10650b010340042005980102015043d03c4e0003e01d1280d6038201320b00c0586092003180c1c45802001402d604880502001c5200c01110716801d9000b88609c2d222845e240051320700300d0101074884103148101b04280128210780c03440001e1350b80400440141d41e0714065003190449402900825201c03a00122070046103440d007405040e01000c020005c0c01c1c44002304d01000e50500004090000442d090f1a6268540c840d41860 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 40974842 1250 40973592 40973609
    0x414070c020d050a0507080f010203010b160201020c0d0302061e0f0109020c0f06040f121d01050a02070b040906030c0f08060601050d09080a030e060919020d2d0c12050a0308070207 79
    0x20300140d03281040e46c1d9a00c9101d025079502070000032000040041c001c41c0e040740c80d003680303a90800100491074540c200641c1c804030306512501c9e400030301c41e0b1a00d050b1300c0d008034000d03005001c0614111080b50383c4500031080c040011030b200406c202e882e001c4980e1250641d89840b000680300c20400744050b16100c01d1007060b6082d032080100301300400c1552811140e51610900c1902c034880a0b24800307407858030101488107400564603010f0003265110b4006020050a14411201303c0783c2d48030018804c55101e0b40051244946409050050010100d841c100038500c4404903e0605d00d400e07071407515400040d05050400c030000901440070079158014280c801d030480102a964200d0070f001500802c416070380c0ca90742c0d0040c8030000e64103540100d40c002407d07070746d855520412284c030380c20412a40384464080301c405030704503540f8204104507c4000d45844452440c06800c4102c2c0c100b20b5920051a4040040c04c00603108c40d40000360085407c5000b685d00d07041050351034840100590400c030140e041200e0 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 40976092 1250 40974842 40974853
    0x11e0c05030c0307020f0a05030a021003060b0a02100b0f010203030a1109040c0e03160602120c033c04030309090e01090b0a0c0e06070b04030809071a0403030206060414070c020d05 79
    0x31041004801840d07007500c00c44186151b1102c40d0140015442903100319a41034000c0c640c060701504000c0c50a000c40307001403a0000f9004e851f0260f9801e5a000b100c0d103400180c3c0828160728495030319221b40807040101b11000c2d03030b51069880000f0340e281b0005288084140d181c0e0401c5003045100c07400d5401070b0000a00030700160800000003070150049c0a00c0e40c1c0b0078850000c01b140a01c4c10100984107540c8954007030200255504d2450420303a12000d240d1001e88000c00c02c0500b41c0c250107940f42800c103481441c40e035504d80c41200038200714400700031040100f20200710800010b60001401400c803425108041500850400181d006028804001c1e0058000c030040100f01b100e0380d4400304000782203803240300030007031454203120042c007460720018805445440403501003070160600741d81c009000000c8500498580911032016810038042842515000c1410b104141e010300c0065484002950304101069010f05407109601b005031403c0e0521440c502c880003952075a590703245002d50400704450 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 40977342 1250 40976092 40976107
    0x8041205100c030c030b090103050309010e01050706090804170f1f1b0801090c030618150b0a050316020a031403060402070204110301090606050c1b131a0901060201060302011e0c0503 80
    0x801034032403138403144000307483c143d1410b08a20f01045074a041c2d903042402181026401d80040d00d032030b0001030ba0781d418040e05001840018856000702d402c110300c00e000c21034441d80303045021000181c00c00c210f46010342042c4410800b07040001340041c8207540440005030300350682c1004200500216510701d0248240d840d00403100307a0001c440604841084008002007003440404508640c014050180c1c020b2220701c42a141841940003e620400c07031100c4072400300d980c0c0c40440215070291030304034089113010080001c84000c00c1d0000700880501e0014259092041d50000d016581c0b518001a400760048003180c030581b9564140c6021580c090802c000380c822006410b46550402d10490805505140001c034205220b401511907400d0f8030f41c02840c403210001c1200041c2011000e9040c0c00250145072110756078014001c3e001880d02e4403c0451420303080206004a03400e05030088025681452400c200503644448a64280b80b9580b089108040d119081200c000e905020040c246220105014 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 40978592 1250 40977342 40977347
    0x80c100603021201060b070b040c05030319031a0d0b090313140405010602120d02030405030f120f090d091a040503010608030c070609260c090709060206060603010308041205100c 78
    0x10020381c0d008640d40c20500b00030f03501e802c2c20707100745015944500205200f0200012454510160081d1166402c8041c0700d071180301081c03071a000314699204240f220308505a030755826100b40e10414a0540b40c1450384007884000c1011203480c22401042811241d00290320003409000351074016101da02500010303aa240032075a4807280300c4c0d0440b442686440d00014000f03000181100030240904c40e03842c20b0520303014000c03000350002041620030340420800c200d64800208020203004008403100c032080d040401d0000c5154000500c0d00e50701d9480034040250646c0c001110004464070114505014041c4400481c5070b8003550348415050360804030041081c08001c80503207512201c14007280c025030b6680508480c1507009114a01c00466045c0160034500c4030286011100300140c0115a4041e17040702c0825005003048540f5000110103800922185505001854004404984a50840d4103580315540580b0681c8104003000c1450301402c002c01c107051141d1140301c298907008220300e038100c9902 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 40979842 1250 40978592 40978601
    0x706020d02060109020a020607120609020d050412020c060906090d080c060108160501090501080903090d08030604060801050c12040c032a0518010306020906090613060f0504150c080c10 81
    0x3000094001c40c8000301d0420305034070030348400100a50080c80141c0700d0030429100030002486d0305000b2030b203900d00030039114018001860300407000d2100140510740303800c0c030003142c81a03444c2e0b06045400c40568410540d844509a60880b03100702c1d845075a6082c10400035491460100005290b004080303800d001c11200400c01c2e6040342c56803415111402000d06040035500c0c454002d090100e40307051424042948151070041d80200c0c0c0004691800c03d107100080c400c0481c4100032219402c0010800c0810b0405001d00002011800000c0c441c0e030800341c0841c1d641380244e540c50361030051200005020300c00c401c01c111004642000d41e5001068403403154400c059080041c7c0036040200810008450500d0006502c21050032a80070783d040e429981c4082c0a54000a03119601c008248503280c104c0d81c0c0c900041a101c2c03100075503a68124078018000d040780781000074110030300c0810302c020803c0c42d140c3e0720221700d000c1c003615014902d111301c0c0c03030701165034080c070070780500c41d03108182e904100014540d20 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 40981092 1250 40979842 40979863
    0x30b18010e0403020c090106050a1d060d06060e0607030507080a090e071205070509130e010b060d0605040f0213030303020d0906020403110112110406051c02030906010e0606030c040510030b03070602 87
    0x35151744440150501c010107500303118060001d907040000c0d1086c0c61090000c1040c0c141402044809900c822000030f425822514109540b00d0740d072182001444d801410b000d103a014103458a80c01e002c8144ca010f0414055140050000240000c038a1b03051445640c00c40090b10310703016018594104041d005202480d441e0080d481245002c01046c84140180c1c2960140c01c03000303081914101d518081c8c80094001840072006564880100c40821380d540409800300780c040361000243c0300c0c94003080105407408201000031883c4100003110240b480c445106d0140c80d0541000341c0d90b0440707643c500e00240601100500380c0c0b880442c010040045400d03440c88903000903640c29180c203050a600c0c40484191040300c80e4080420401048542c1c019409490680c4441c0c0d42c801740408a841540140c1c0e100300c9001c08103402150051100c01021590580c20080582d44a81180b40c4505003075401e11560056610079401105580b400c0740c440d40140110170405411703142c60a030b40c0c1d80c02964410b24401e = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 40982342 1250 40981092 40981097
    0x605040f080106050f010e0103091e0b010e0105180403090b070f020102060f071d0105070b09070512030c030d050a09050d0801090b03010e070b0f0d05070c0303060b1306030b18010e0403 81
    0xc0c800244420140510f0b42039131001000c000781682d601d001519400d1010014070b060586400b00c80d80400c408440c84180100000c10650803a4041e141c40084030805821a50b0071550074001440651141c080c265018655241d0b0361040b92141e080c181d0300c0c1d5800d03038070004015000041220401440c14401501d05200303800b291841c7d1140d002c4072200305401c0b5990000144980404510f900e0302d2080c00701e40c007506060407481e1250315181c3c4503803408100c680e2240365000c400100a1418240061000000070801030741c10b00003400280b42d1280300d050609440141c07601d0210302810819031192902a9209085407142402c11a010701142d80901c9000700152402405200d141818000d2040401142c8080c00c030050418445034880c0d080b100d02d520b180b100600000c40c07807011600c900e50207000180caa1501c1800c0c14540242902d540b900200108201400a803020800c00d004641c262821810013150020b040380106030b0407814030366904414020140001030901c0360f440780742c0c040c5000c0c2c0d = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 40983592 1250 40982342 40982369
    0x705040b1305041817030709030b09061605070b010605031909110102010b0d080306040f090503030a0b031e031c1808071103030405090403030506031501180f0c0e01030e03040e01060504 81
    0x132046280b00980d03800203001c2c48080e80704445240500401190320590314280b24400c19140e40720a100200202c607003210070303400354050040e40510141000062441440c066103415860360741c22009078018410001400750100100300407042412448906404069041110b150603003443c041c0d22011420907400344d481c049850389103040c035000203101d40750003440080c80c42e19901d090100810403554800e61140e6a02c0b0803500141060004500408031100007250032882e080c105030a0002c0001e101107000f0660b0407101e048100442580c50b8140183c070142c00201c10403500324082e06018071010f100e900c40700d0303011081180d40c40103402c03140d009901182110b14041e0a15540b407280b8084c10ba403014204c3d00250000f48a60440340e40070b20041c09844541c0d8405e01c00d500031a00070f801a8102040811148004075000c1c8a02c0c1c4002c820718400f4000c0746103c103000361200741d0b6030101504064581c450070204c9031081040b20014806690301124135a0f440070001c01540060003040d130b004e08034 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 40984842 1250 40983592 40983611
    0x80a08060901080a080c030d06030f0606091404020d020d0206040902040603060b070302060f100305010c09090e0705010f230a0201020a11030a020c010e1809061608090c0402030705040b130504 84
    0x580d14981030f41c0c0868020824200952a268480c0d0080559005548000c00c40c28068403044d003e010000c5100302d5104d201c01c070307040ca0310a050315038039080404028984070f000c0666003c151034158100380c065480c074028902600101e050405680406500881c1c0010700044c12000c40d0300400496400d5503040000c603845005152540c890800040c00591011006c514880c0100701000d41149801d18040d991603a255500780c01d440204080e500030800d400e0040288003501d01401025480b842e000c2e003c2c4c2410000040d05080c40e44600740108150161069200f61540921306a9034070003099560b00c800b220440203010354000b07003406002440b00110098502c0000040e5203800031141c002d48250b41e0190011202d00090440a40e4006007101340304402c0990100c126029a83e11006480a8540302c400324188a200048603010040500e04100b19a0004200080d004008450150b541e4503414021180e6000b15005020507441c0000c0c420b1221055000c080d003210710580d02403200801 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 40986092 1250 40984842 40984849
    0x2070215031611120a05070c09090c06051216020a080d09050d020714060306040207080703020709051501080a0e0c090f0103031706090a0b04020c030d05011805130312060e04080a0806 80
    0x1c0c40c00e6060f00b1303904c800101e681120a00003e41500445481e200d0b04040041c0c4a42058110316440452026034031194902817062501a0030040c200600300070f0305d0840a07108140035180000e207060108034007822030a410718801d2008422107a00944056165030650440c407004041c803101c21900c903c82d06090403011400072034000e00725422440d4084003e00c801d07051100b180d100070811503100c1e074200017000004541102415072a0700035402400010308000b42c2400300c03074014002860050345407010821aa922089a0b60b0010020201141154141015a1a00c0558000740d40e220b04008100041850050345540c103c82c000c0e500c0e00c406000240020001d02002d5034a903401c00181e10001d00c0300240c98000108001001c0d0005213490fa0401c0d1150850f0454540300003140e444600400c41d02c01602000101c20400d160b0030001c50030543c447c1c0b030a942030703950003e085c40240364803081c150449901030740003009035a080d11050b1400380340c00b0403190710010f0403c0125180c000411040e09 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 40987342 1250 40986092 40986107
    0x10204140f09070804020102191a010506040f0303050d02070204020708250b010e040f0501020c1e030301060801031e05061314010e030901120605032b0503040b060f04020702150316 79
    0x14006000b200c0e07280c6441908407428403008005034198070420701c80ca41c050b043d000fa108400c0c0d0003480c0f40300c081c50441010f640c0007030069004511565060000b0301c01c0040c0c811043e8200ea5050070b01b03664600c031521001c400f9002d2040069400303880883e241c801e0012110060158204460115401014049005000c0c0d00e10490142180f6030100c014400d4210b0b40804903081401072200c804864a145d07a91406d80c0d00400410f465a0440103140c9202d07424100b488020384000790140d0700315810440001c2c0512030510010300010b6079400c24404d45004500b245903c1500b05003500c0c1c06241c008403250040105034012140000d030200c503500c0d00d00040c424002441c01840c00f45240414100044403400c503214070f4102c407a51b0b1180002410794080119041d045031200e81c2403a1600320004024083e00c1403c1d138101408010001c0000290070219100d500c000f003180d10380554920440824001d01032040001d4020a09408011b5601c8000e00034611500c040e10320030740d62004080040b140c40 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 40988592 1250 40987342 40987369
    0x90a02040b04030f05100e16080a120507080d0908040f0503010b01080a0507110f06010905010e15040c0e090a0b03010b0103020c0a0b0a11030705070c0f030515060301150801020414 79
    0x54424401800004d84d10700510a80500860131280140114007581c0115040041e02c6892684184054140059280055401000590090b10f010195911001c504000c800d440381c0400000040e000200a1303c00241c0d180001c0d16802041001c203646048460355015010300794828031500e00006143c50140039124006106179201081d5498000380c03070380681000703025002800b034001040030080404101401012003540c0040886500d00610401224010b8010a1202030503408000c0281d00344a1421400c0d4019103000070a4210300c142210100021b110315603010321440d0910545401d580c0211403007000441c000c01c46040d074080154202d118a141c000e1803030700301d5101100440c4120070745942c000b213421000300704c2c60100d401c80d060311790040340c00c0c0b400700307002054200030310001011003c09040040d02c1e050215045440c2c0700c3d902d2514442c200100d442400002d002901e080d082889040c09040788082c0c5281c880141034041e40003401180d07403d184030301c0d800300340345007501100058 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 40989842 1250 40988592 40988609
    0x7020705100c0314040801020f030f0601111c020304090c020d030b0f130f02040302090405030c07060206040b040b100504060602030a0e041812030e030d0504050c010e10030b040e03040308030105090a0204 89
    0x9440355507400361181c000c1a031303040341e1459050100203013500d820f00051450084a9104584e0381c0f92000d15840348220240c00c50b41001244c7c82194401c220008607850208a5503600b21f05803500e440d401c81c9507201c0d81d040741d00d06508100034800c0c0146c0019945204c0b6008c1d4800340501b00401082c0002c90034040c0d42a6442104000340900d07400300c56000c0c8e420f041c002c41d0302600e016280d80104052003400c0d542228264000568000c119000744244806407803036201408040c2495210b84806900191004d0709286441010070000030718210b9410060401510a00140d41e840b81c0c081d480e0742220b1450b0b07000c21001845c82000789018851000a40c0d148049222400c040b0348404ca403c21100b0024008e25940d00071000542204001928041d50920b20102d03d80c03400d450009d00707020350300e640c2c103052151030382c00d40d1440d9440000c600c507842c519240015050100f000003c002d030072607020305042c81c080001c1c0030040c440040000d5041c0c9000b545d1a40a0f6200d11040400f01c0c8a40d1250082 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 40991092 1250 40989842 40989857
    0xc0102011104060e010302130b0306120706020a0201030b030a170c1b060403060b030a0b0126010e0d12060b0408011b0801080705060d0906050a0504020301290d1e05060702070510 78
    0x200c01d0013641140c2e030800061400604060000c04991076500540c0c22032034112401200704052442c4c07111511070701050103000741441c2490200081d40c1c604d01c000009041c0f40d102c0c01c941001c6d40b0200714540c00c4d160031071a8005002c042e101582e40c1540441380700c510781d01074151410a00d800040100220440c043e1540f03181514580b039000c001c00c4c140301c0c1254540150017051021403103c991407806020100c41e0a1a0400d0030001064a0340d00683c46e01d405904080c01c18802400110f0382e182000c045041c10b000c1c0c688000c5101000b02059000790400e1400400c02049015055003c207400300e02c148800c040d4041484010780c3c1281c1e0074810f6812590200340e00380300720700b80703c1d000e03010a020344078010a01a1a070b40d100c40079200c04481d48035416a68200b0001545003d000c0c03002c02516403002c40080c000c96200c1c0e030502644020303245010301e0310032880c00d081018100701801e44034400080c9020448031803030000d440c1d0300c09030392410040c403038040b000c2200e01c0e11420188007403403551903c0c036 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 40992342 1250 40991092 40991099
    0x3020f070b0711010207020a0e07020a080406080712060308160c09060608040605090a050604030c03030b041a0406150c0204090213020a091d010b0d0c0c0c09020a030f0204030506060904060f09060903020c0102011104 94
    0x80300c9c0b450050542d000c48c0215111f000025000c100a4400780900b500c1d84a104c2c47d00c0200108442d0011224180d003500340001080480d0402044510745522840321b5000c0358407600780b285000c000c2d54410280b0320301e00100054140d40c0082c80600580c42018244140d480e03a0080561321500c80c003001e04a90085404107000071f004841010003244282801b040c5602c054001504072000d91f282509425102581642c180c03a00c4e105400103090040c101808004e851301000f0040102c1707032402401181d49000e40303c1035650ba000700d08115801100199a00e80c241c0000400038052031290690422280c034001003940d85a544040c140d40d8890b0400f82805d0381821034002612005491000781712070080c100c0e002ca40d80c03150303180103030060480140e41c0c0c1c41c40701c0e8010125900050094100c500c18001840055804145140c2003e41216402c0c45501d403410404000c041d01e178081c5510600d0301c24072134200300c44c5070014103056010360240c0e01d8041300701c0011b9080e50780031480491005d00402051 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 40993592 1250 40992342 40992359
    0x2030a050c0a02100906081605030703020a0309020d0c030b07020c060d0903170108030309390112090b0613021306030e0a08070804150f0203040e040303020f070b0711010207020a 78
    0x82000c81d0001044401440300394000c1000001414010700004401240501805801005540d000611001201d00c007540e42c1c10010312500026040e101019000a4000340e0306209070809008683c0041001000042c0ca2038041c04c103500030f00c02180e248241c480003802d000c0c0080351045040801500203441c09040c01c00078801083c04103001c03000c1c003200bc13407004250024522218041c20010300115035a040c41c0d0300302850052680d5425407201038004240c0c0703002001001101304001100120341816840e040142d032610145c0306017000e0070b0301d840300202c180164103080c5400782c0d0080d24408004208100e0740c0003640720b51f01100c17603042004042008954031035400040c070020a0000d5071243c207010364403140c82c0e07030290708140d0702c50350046410b0041e405c403600440002c41c4541002c140d80a140c0001030740f80c5c09188941d0107501c6d00840000c2c10705001c0e0b0103e900e485000503244d0350b50489481c00c00c4800006840140008400542c204030042c41482224051600105040212840c2200c2c0 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 40994842 1250 40993592 40993597
    0x1140a0b030604050a020d0207050a0c080a020612071709010902101403130303020405060a0903020306130209010b0901090b0d050a05072a02031203070c050c010804030518040e0709061d040302030a05 87
    0x1c405e10540c208003aa1500a81e44003816405100e440603025184880c100664600203036041100700340c003e0381407440166941c00840d1404039800240e280e041d035803000c0945030140c0e11340c002c44030f00383e9000130040c6240043d809805071a1084074000c0e0340703d044c0704046030448604251400c417040c040000c40c00c94034070b071031610ba1094400e29004d8641916071001c5070241c0c0050b880540032680040e02070045140602120350700403001840303030014950580001d141300d42c1c180300d4446803401c0024610000e0344602d02c4800608400c100752aa660703242c03620032008100407620019440d14081c042801ca41c80b9420421803010400c041019520b00c840413503000b00301d0468101d9062080c4e00304075040100da034001d03603c00d46158650b00020522403c000d8140010400c0c075604220301d0b10100030010f50032400381c5903912012447e4421070404580494000c24194107440e0091180c4400022141c0e8641c001c00f0654801d041d41030546241002c01c07200194081e103009016070004d100007110715126601 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 40996092 1250 40994842 40994851
    0x10e0f01060c050a020310060806010e04020102060403050a020f030a050c060601180b09010e0904060e1506010f0f02031b030a0207050609060d0b01050d0f0f110a0c0212031309020301140a0b03060405 87
    0xa03110b00d2484e036400240750108101400101319261002084448820300c5020f00416008001c181c0614003030f40004c1d1070318002000242403120204003400154420024030241c0c1c0740080449595000941020303003103400c80c004002c1d580c0b14100018030154820f594000000c400e10095504090811080360000d8105201090400004220b0103044c1d0703032818149030161740511000900003156103c61404d0040c8614411941036041060203002c2c0d0f405100c5506d140482c1c80c00c0f0100300c002607401ca040d48102004294000d0301083c03807181000e0080300810407008140c0880342030303659500600c10319001d02c00b00b6603800a000c0c07001e80c0d115070349500b00c0410100c051610f40e1907c00b045c01000300b1200b0003683d80071402d0344d690440720201640d00c2542c8504000380741c254206544004010482540703280300034064010f0040041035101c1c10029a024207c40743c50000a0645980118000350000d215500714558a45c4070140e0f00d0400da21008140c2e410b409403030349181c0c0e9210030b0101420000c2d0 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 40997342 1250 40996092 40996103
    0x3100f020c0106090603050c1512190504050601090b1212031005190612050402030a03232118030d090f12050d05013005030d0c05070605010e0f01060c 66
    0x40108440002032040d8400380c400400d0005116046062544c50000c2300d42ca03083c01004900302118200303030b0010507980301c0403061850342e1003643e4031b000840c140c0818a607880daa04c0e0801c001e00040000128225044c0c03202030f0f030708004861a480401000e1b91240f80c45407110380202d82203450f0391201d00001c5901008440e880340865541c0c0e80840c00e83d0156032088110b01004c004144403c030f40c401f840011411201400f07009505090300069240c020341c0f00004c06015103d5141000540390080e20605078401518031601d4920a502d035041e00c03921003e411142d03100410000f15060980812051400701c120011414040c000d03031107800030540484166002c8458840320303c0080d541d40e41e1214902e509039101c544402c90141c03901c01b610b00603000b01c1d040701c0c12921a9401c51004401a01200402102608042186041c10341c1548a402031191145050240b901c002a4100008280252190408200e50fa03a00c0c1022444004256040162840110010032045119219500c000d50044 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 40998592 1250 40997342 40997347
    0xd0b1224041406041a06090610050309070f080d0206180703021216060306060206061002060c070201050409052e060f0f2c03010c021605120a0c03150b0f03100f02 71
    0x1404460f00d07000c41202c046800c1030403040e030040503d0361110000d030001e0040d21203010506028002400540346291041d0800a000c0002803010340c0c1000304500900d10322000b022200d849018854a4000d62a0410058814003000c1500720f100320444c41c41e09c070340395000b6180f002d0450382007002035102c074400080284509070948032030030080250a0014111500d000918600c1c291010f03003416401841d881c45500b441814100a41c1c002c280594040365001c685542d0300024401a1424080d6801840d51a480c0c40c0c104024181d0903000b0129a19081c580c2200204c00c00202d0540c0028500960307000a080e4a250b4103201d001d100d01c42d11103415400c00501215041041c04910b945c01c0e0203a003000900c12203c1c400300d050038416020b1002c020300c0038005018004c0c4c80c00e02072800d80d1084502651606807511246102803102130206588101a000103542ea81806003868000815500c081c0d86081041700a91800703841d44802d5a4020700942030010101c4030038402840f41c42ca16075146a002c = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 40999842 1250 40998592 40998623
    0xc03060f270d02071d0601080103030807030e030c0f061b0702060a0e030105041a0c070309140103020c0a03050315062502010e0d030801181404060f020904020d0b122404 74
    0x240400007685406a0050513014a4094025810b00009551040400b05681030003003076613000300c1c041d05403909030070030f00c009443d0110101d00622400310f54452a0001103055002d80602007042142e0403007410440b07805860382c82e051900480591880048034804002d51001400c0200c0644451400307410706c610b201e02044082421748204a40858060051544e8200c203120381251458200040074245804c100307003568041d2203052540110086050340320001a11603100380c045407443e40007481580d801e0322451401403d243c10560381440000440140c41019051400503075201040a00b49450f201880b034620380419049100d0036070400c804c1020464041c0c0380c4070721f100741e56482650b40300701c20f616141c08004500003540d0041d507141d040003044150f1000180b10503800c40d811100016101e03203000032440c001e01c03403014941d030040d0002c280b201a641d002da201d440c0107841030f00c007401a500505825501d51b58000090150b6080c2d402d11400c880c1c1500720706543c810310920421601890 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 41001092 1250 40999842 40999921
    0x150f021b040b0d05010207021201020307052208011b090b070c05040203190c12050903040305120313061109040c030b030d050c0106030501110a020d080105010f080702100f0209030c03060f 82
    0x9801c83c0541d075a03900024a081142488059030040c2c401e000000c5017036050044c8000c0c031320b1082210801c00f4059102c4e0624414504089050040c1100d100070400f5000e401c000400148403542c010020520701c03140003404214180445040700c0d4040074002c002070030300301000000d40019003071001000100070280541c1d107142c030070b5001c0304685846603100c81e2008105501500e000178003451054209200800000710002240c003003d2120810040d200e5841c40038005030410225000760800c2d0900002c40c0854031040700809060805440601a19080394001d4055500e50036074941c040d0710001042c600c0901c2500274020b00c0c0351074800411201c1d0741e902c0d4103080d900280c18040805800042c10030a45030104900d5035110180c0c00c01a041e5072420780040d041d00b500d240b404060102c900001160f1500c00d10240d00100c1c039010040042c406040c06c0e0000a4000c108250301a1207121641141440c2c0014044d00c520741d0710a03044801c0c0c0c1c1d403d5004429844403001014102d50241b0090a071a5 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 41002342 1250 41001092 41001109
    0x209031e01061a040522051302010f0206040b19060518071e08150607050a03090312030605030a02100302071a0603100b0f040506010e1009150f021b040b 67
    0x4410034500281404040310346084584a9000040031042c2c020714840040703207041034408076034003214140314040c032654200c5c0e0046804004850190b14000821002d2600c0ca10104c11090007039846084069600506a980300303020b0368050112026140000c0c511450101c06202c0c10b04401000304107d44d0b910041000782c110750b403d035929082040e04026076194019040300004604505c441e0820303211190141080070b005c2c20510050401c62010800d645400044800d00c0c0c0e40300040f102007940ea824001e102e807016000450703080c3d81b2510a1004544a40030300d106451006010b41900744043d420000419100e441c1d00c02403540034045080800e00c651008039101d03001045000d03447c031740041014140024020300714201c619003102070b0306980b42c10029602c0e82d68290390000e842d8491340c0041c0d50002d0002c034500d601c01a200302000f00250700c1031a01c3c00720340c04400001d5400c0011002580c0d000c08a10b03641005030302c420f0105241c108084800c1c4c004100c0503000080300e1000700b02013420300 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 41003592 1250 41002342 41002363
    0xa120504030e040f0b030105070e06030115180b0a0f1e080406090b01060c03020c010f0507020607020d06051303020c0a03030e0607060605060703170f040c090b03032101060908030406050a0f0201020903 88
    0x3255078170b200d803986081c00c0c0203082d48a025850803c20b40816080041c00c103000c18001e601070511304201550320701d13011700c1f01003d100d101c0f0200784032400da990400401b26070222943c4000200c3c10070690502e10b010f1160300e2041c1e0131103100000c468030504012900035100900c156580d45e151480300300400d090b4154180606071580d1018030740348060030040c1c5010040e0283c14104118894402c3ca031640c04800e448903264122002665a41c003400001c0342c2419403000540365618003820b001c1c0540c2e000c040400301c5407007a001d0b03c04507000b58041200710881880003402050540c2c0b1162103506e0081c00a042091082c1c10011300c040d1650042003080c1c000d8030080740880c03d4813016245810030350810bc2d9001c202c080c2c10390001c0c40c0941d03c0b5940c0040503c90780c201151907800700c41e462342e0f050040c0c0c9c0d0f186c0041540c04a4a02080c0d00306941400284078135030104050840215103444048100c800b030b030390b241e02d83d589005182e201c125001601600c09000710356090003040440c4c0d03820300001102c03 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 41004842 1250 41003592 41003621
    0x7061e0501050a0b040617060d051b13020c060402060f041d061203091003020f0903030f03040204050c071a04021c0f030e040b1507020102030f040b07060f020a120504030e04 76
    0x1981400140b2050204030740060013601030500c8200103a030b90208070b00400103003040c03550a450300d4600100f0504c42c003414009149000f07117000a030003269031541d041c11421044500e0400070242c102c0250407441000450400c88c3c02144c00140903051010041040d440b80106051030959a00c100c5e2105800800300d031032410542005002a40c5461201c2003004800b0001451400403c2d4001502320345248610f01c082c99000700305d101b90810110142d42d074404010f41135940e01c15182c4100ca10581c0122400c0740700fa450300f00800d084101c54001d07a2903456000728110702c0c2c1e003190850059a208020002ca0384101900104c0c480070050744400745107a4400c2d00b00219485d02480e018041c03440420009006900e060048140c0b5030f43c80200c42c2250004c2d1225039075552840c00100c0c294803c8244900f5071082c00103001518100460043c160180030381030410101128a140d18160307c105441c00303000800006580601e42410340c4040e41061203410a004440406c2010805644440c0701d030610 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 41006092 1250 41004842 41004851
    0xf050112110402090613060201061d1501230f03040515010803030114130608030c0625050c0c12100506030c0108041b08011104030506010e0402030601031b0f18150b0a0507061e 77
    0x80c80700c2e80e03000c2e030109001c000c0f40c0217540c03330a98442c0001c81151800141000180c1a1754600c2c50940014241400354580c1e100c0d075208400c0e016400d0591056a0403242d84c444e810f900f185000d424031103d4184c4e5041000755103903920707120495901e84444004954070031092030320a03860140d81c4c40f9a034000e0034184003a503101c130298034802e414101c00818807400403552050400441d030403900c1d007602034001d41c10055212400702090f40e241000b80c1c0c6485420106203402c03800d20b080c000821180c10741200300280204c0d41c80300d00b0f15440301c0340c0540c8103000c00c1540c00400c00040c02c00c80c1242c0f8860f8944114041c0d0740e41c4501050a54088d24982d85140c24006800d10071f01c2418130003a40900b560100511745410700750b010950390310301480080c08419585002c4c903640084040c685004100403600070118949800407001541d201010210314075140000000c0d0000321b4585071412100e803001e010381800d041c42000ea480f5801a88111812580c0e03a0b058410500302c0305141c8900d400b030702e40008 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 41007198 1106 41006092 41006099
    0x160905040e0a02030f0102040f030305070203030d05041410020c030307051b060103050106060f030506010906030b06090402040914010e2511060403030f05011211040209061306020106 80
    0x9500a0412141ca807200000048201415008800307465045c40307110f20442c00c0f8400c51188802c44100103004001090180001c0c141090001e4250f91a00c1c0c0404040c004403040ac880454403103241c501c2c0c00008050410804030050f080000462a0602800c2c00036602e00000301150308205002610500d00200c10044c002c501c00c6c85801c030b0314156102d14200f03000c0d02c514042da000141c0140131081100303100340902030240360107840d440c90a40c02c10f001200544071203502540c1065003001154002e45981c4000c0005000c46140090b00301c4005070034020410b0181c0c03000383c40c1191801848000340340004107487c030400c01100d1600c1c1e903c1c00c41050354583c85401009800340a61001c20050503015000b1205021090104004d5a03881e114500c4102101c80006040803454400015032070425500400a4507001404d082c2001b242110500b4160403642000380182d44421040 = true := by decide +kernel

theorem cover : BRFrame.Cov 40827342 41007198 := by
  have h0 := BRFrame.cov_init 40827342
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40827342 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40827342 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40827342 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40827342 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40827342 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40827342 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40827342 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40827342 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40827342 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40827342 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40827342 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40827342 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40827342 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40827342 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40827342 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40827342 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40827342 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40827342 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40827342 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40827342 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40827342 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40827342 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40827342 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40827342 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40827342 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40827342 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40827342 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40827342 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40827342 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40827342 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40827342 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40827342 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40827342 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40827342 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40827342 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40827342 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40827342 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40827342 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40827342 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40827342 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40827342 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40827342 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40827342 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40827342 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40827342 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40827342 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40827342 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40827342 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40827342 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40827342 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40827342 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40827342 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40827342 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40827342 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40827342 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40827342 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40827342 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40827342 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40827342 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40827342 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40827342 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40827342 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40827342 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40827342 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40827342 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40827342 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40827342 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40827342 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40827342 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40827342 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40827342 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40827342 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40827342 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40827342 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40827342 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40827342 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40827342 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40827342 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40827342 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40827342 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40827342 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40827342 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40827342 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40827342 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40827342 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40827342 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40827342 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40827342 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40827342 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40827342 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40827342 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40827342 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40827342 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40827342 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40827342 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40827342 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40827342 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40827342 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40827342 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40827342 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40827342 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40827342 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40827342 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40827342 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40827342 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40827342 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40827342 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40827342 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40827342 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40827342 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40827342 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40827342 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40827342 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40827342 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40827342 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40827342 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40827342 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40827342 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40827342 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40827342 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40827342 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40827342 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40827342 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40827342 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40827342 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40827342 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40827342 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40827342 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40827342 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40827342 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40827342 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40827342 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40827342 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40827342 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40827342 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40827342 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40827342 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40827342 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40827342 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40827342 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40827342 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40827342 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40827342 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40827342 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 40827342 ≤ n) (h2 : n < 41007198) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
