-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1212
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T01:47:35.861252+00:00
-- url     : https://prove2.me/submissions/a320b652-18fe-4388-bdcd-e7847f7872e7

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 217805755 ≤ n < 217985611 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 217807005 1250 217805755 217805773
    0x33e01050921060109060609140d0f0204020316271716031a13030e04050705092e0206060102060c030a1401060810051c02010311040b0c060412080f040204020304060e 73
    0x48000f5400c0e0589084c00001c2000c540c84030002d5468105502c500410502d48040c940600d04018040c030005501c100c017503120029550340010709070b17001140c031048590f400c014161072035a4007101142d03d5001501a5121021800e40010104145401020400307842d000861a10303007410001807a00c50301c06800500c03c16220714014203122203d07284003030300303840302e20200e08100e28032246404171a03810740300c081054201200b440050000101b01c44103008041c0400c0c80c5648814603020000721049001d9a04068124424020048a0705c00d10b400c5600070410840c842e40c00161841c1c01003044442161a5a90b40e48802c0260448810300380040f50400d00014030b0a4120a080340200714825070480c03405c1c0c40b0402c1c005801c18407692031503802058003c0381d016502075440040401d05500c1050303e403d445041c56030b80f031341c015072004540303a004504000c244050709107101c407800000c1c60300350f9942c100f18500341c526060192010744516800004102000020b900810484140d042501c003008 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 217808255 1250 217807005 217807069
    0x40b040606060203091e130e0a150504020609120109052d1203070e030a0503030c040e01080705010804060b030307020306010e0a0e01050c0415050f04033e010509 71
    0x141660100da995003400008110b40e4008001c3d5a020007010b803103103069661032a44200c840c0c28400810380c220303481105041d95800940200c0001942080c0202004411032074481c1842c903000005001151514043c440185d0707034201103619150b400c5440000d0280702d14540ca0050421000c010081d02c1022402d440074007600300f00c0200c006401408001c02880c040420f44c440404403420803108004000080d40301e4050030400c407062001404035a01460f581d6034081c5550701c1503800c0c2809440109041101c1580504071602506a00c000703031420328a17000000c2c02040300584010a226102c00e180c000340d4a040051f0344425800804031140c651391610711024000b0140d40c1d001082e802c100d024902d4180500074580146003c00c000c6141a1a10794041e940115200031101044030401195010070b1607000900040c41c02507140c1c0c82807a0190300e092030408604003403034100d01c1800c00c070765007450200428003414000c2030070410381c4c592031a4001403c21100140310201c0341501c804a900036 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 217809505 1250 217808255 217808273
    0x50304032402130e011517090a0204020706050f0718120305070f0308060415030302120c071503020309010f060303050306040906020405040603060902040b090603071505132409051513030b04 83
    0x1103c0e900300c42d0781c20342d0721200c0800c3c1d15040120a9400b082c01f8105218004240309822540703c01c00000b5241d960041d5400134040c1c4e440141c0076a9103944543c107011520300c0c00c0c40c1954025510381494448003101e840c041c00b05803a28454244003200c0f40760500d09140c0200102e80c00d107a400000011f21450500c1d0251003034009644241c0101e203007000c0c00f0074521000e860705040d01e401d42c000f000c060b080c4a1840c4019808081c00c54014011800700084c104c1c1e00f04001e0840340019100543c580c40d044801d1421150144000b030b9615040100801c0407030b0b0041c003143d0304100c041c0e030049034005903428100080c2c89180d010036003142c1344c204004280a20341d842100c0d1640b08590a004c0c3d80b0b014020468841001d40d0500c3c0e06400c449000c112a80c07a503e410b80171005541481c5003040302c0d40385111103c0003aa408404c3ca1a4848001c400e10300340c80718103901446a504120311107030b00b880c0115484003042c2060307510055000030705d801c071902c81404220045901c60122803c0340b4081c94201c141d = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 217810755 1250 217809505 217809509
    0x90612060c03050108150c0f072001050a0914040b09190e0102070b06130905070f030b180303011703040305060106091e050105030601050d180303051b0705030403240213 74
    0x441460401c1c1000014401e0048a04aa10100c010400a00c4c4102c8003c90b40201601c510f5041c0000c101c1c840810110741d000e04680c50041e03042e00d20144a4003d151008000f804110341000703070402c080140550030801c550705480442c5d160340160b00e51180424001e04410040d03581c855908800c1003030302d8900300905002d003d910031081c401180c91091a0f403d0b80100320703009280b100d07880700081641c1050407940c03200c0c6611480100e107074800b41d142d40e4140b9100340c00005240804480a10600043ca1131042c1c020003600810f654684450030170a4030782c0410700400c1c01c042c10b07102540d00c00e0042041610040d41e04001501d61950392100c0160101019204420f070036264400021200c0d14a000014100c0c0ca043c0c48052441daa10001140c07035038480003002014643e10303080d00200c60080320242c00c0d410710a440004450a21902e04d0a0520390303408440d00c8114108001c00c0010b2010040d101140d50007d0040c01c0d69000c2083e0f5161268241003100c801403021038007034074050a03940b00d03a007 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 217812005 1250 217810755 217810763
    0xc0f0203060f090d030204030b0609130c0801020909070503040507260f01020a09060807020304050906130c08060109092705011d01060509100b1602040209101e0c0b0a0b010504090612 80
    0x104c60388850400f60284d000b503200103440c60310b8003c0000c1c050309000c03201990000011070880048142ea039030310a0300350095000720b10f59a50114510455007010040150801320f903041690642c0390a03901d00d543d880060207aa000d800180305d9440012150048482c0610000030035505c10021111270b4038000c0d0094170610000401c0c610b00041c8041c007071000140102844c0e0f02840c507060404c800e1107200c00f0080c20560704402c1520b1011001c0c0c00c580b160103c407420540e1030481c182003600c001420681c0c030360000d4240d603103041d601801c42002c10200c0f114242452400340f802c084241052801480f400315200050300360500d00746201103041d4450415180c08850522680d00d9952102003602181e01030412a00420080640100c110124000040740700401c0076142c80a01c0b408594202e01426804010401909a50307800c610b03846640410340c02e80d4901a2144900c907100c030ba51789003025015020480d5a0000780d5151f91040c0308035005050850001e00940e684da002490400a180500390703 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 217813255 1250 217812005 217812013
    0x1320040e0907150206070f05120a0506011706010909050603070e07230405090402010507021f030e1011192a201e0a1205010c12020c0d0c0f0203060f09 66
    0x8100030f42010041e0140c1c032044c1e40201529640e510043c0c07050006400105c040c060300388200c050340d401040155101e101450808540b07410407400141016100f82c0c110920110103104006890740e1100b003400866441c0c1401082c99200c1c800424189030503034200542006544080002294101031144070301d04131307804602c14088500c204d03074100c2e020350b0040c513901004680100300958420341c0a49502c0340001c1505004000d0b58040380109031002c906500460340b243c04440c0c50760414025081109401e06040c012a04100c00001d0300d0b10414406600c08041c0f150b4521100d48515401c4124900203a4060a102440d10000d80310b807400e00402c5030f030700841911a0b9156001d20300b0114120b40b020b081c15000c18104020504d03011a240e1426070490307060440000d2000c43c41c400c0030146805280001038040351920002c00302c6c446e10503c2d40c1d0460041104050324040000c03104a4500e544c40c04151450700c916051580d0000000d000e5850720504050042c1c9012008055000d04803d208817 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 217814505 1250 217813255 217813259
    0xc03050f010903020717162702031026010e010516211e050c090301060509070519110a060f0c0903030c14031303140c0901051320040e0907 61
    0xc503080c0c0b0341540c00100140c0200c4070401c08003500c2000e5804050180d01035692000e84410b1001c0c560f0706d0340d40043c50507504903002c0f2042090040540c010a00e000328298075500e094044540c1d40b076114491402840e442100000c07070a05484034a00c0c030001050000e001c1d800202c143c0f680071303220039030b4002d900014550381501018050b418107501c80c040820003000c9121884c8504004180d02814030701031031701005100c800c2d00c180d0310036a8410540c01c01e07500e803280064024075003101c01642225002d44d20034014408582e401400703456a032040020402c0b04411048021a40920b110155607141d00c40d0003400000c0103400c0d0410316440c07001150400c40b02440cbc51045541500a20014001c00d0210124a0206807402c0c80850f001038100201c9280050100c241d500300c1c0f6a80e070090b604580d920041c188540003d001c841e446481c215400f028550402c4005101210605580086a0b0b40c417110046042403030300b00c030320b140500c0b45145926155034601340303020218201c0f80780c002c9024001d00 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 217815755 1250 217814505 217814533
    0x3190908070c030c0e1504110415110f0705240706020403060f0c1b0206180312030901050c03010b16030207090e010213121a1e070e0906010f14070309120c0305 70
    0x2403144200000c403106140401c6c60018800140400d40140070052001c010206840584184080d11541250b40d1100d5190744c0303442d02c1c2c3c100300c00314401c0c02160304402010000d40c0c2c0c8003e500c07444481000d1131488c08807020304c10200e603889001c800510450010400006200c40c980c40300c034659100c035403348490520410100d4a80d204c18a11880c030200017210f0030090f0402030080e04884112900141001104c4c10000e45010080c89415038229000020050249028001d8641015003286e015086d54108040e91220b4011141ca01c04581000b42c00c00d4180340c82080761000500c40e26408010007440f00300002c0c041d621510181c0001c1036200400184804100d00600a20781c118891441c19903960086200324800a81030410180c04180800800915400802d011f0782c0c040d1030740b82c4490000b00901025450041c80c41c1d05101c0b132514412109504400c62510140c58101d00300c0c1c1c0c810780d40ca02681e20b80071a070030070350510b8080303846078041203100c010384403c1d01c4c0110100c80b01d407210450 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 217817005 1250 217815755 217815779
    0x60c1006170d0c0305031f0314011d1603060f020d0504061b020c06030c0a11010e060103233007080a03241206090510050601090b04030803190908070c030c 68
    0x1c0040008404000240c1d290810001060300c0ba0145002002120380c6c035200c0740303949c80341c0c3c1d80300b042c0c5d99548103201c0701c081c64004010706a00e41190083e109084d210421058400c00d00e20010f4021a124061744120840a81c11103805e50280041042035050030300f03280004002c043c4a03019070b142a40f500581d20384c0000b40702ca4407076800814061031a520940009400e401104001090000d900b01132541c0c0c030750a000c0d00004118020050074a503145082100e400c6054505814070f10292400034085d04601086c0e003034140764a0400c0c0130400014030140318418500340801c04082002180c000200030580000b48490142a42c003441320044808403121101c4515280d0310400c0329a4108000d2400c1e11100310140354001c550000394070030309403103050400f07002824110100703a440c410072080c0d60b000b504580140542141d081d0400d8190340ea41007a40c8800741280c80007c00050700c84907c4a504d805c03101105034840740c402e8640c8000c0c6061003d041c03003400221121550036102045074a6440 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 217818255 1250 217817005 217817027
    0x919051203040e041202030702102c0907030e0c060d020408160501090e0a06170c03011a330708031b070305040e0402040605150a1106040c05060c1006170d 68
    0x1544a520b0b2281d45e180c030440804a2190310540c00f0030b200450160307860385482000c01c4d071183c503030240c0f202c0820098408090429120320100e000818001a40c1d02c030858095030110290400140d41e800742c82000e40380100004036141c0c080800216440d11140640281c0110b0f80d41008503101860000d10141401419009150000b2003440040122034101c2c8110341e000060318400160071a15a000f00c4d0400c02c00c01080b88103503100030b5008186090912a580008680610042d003640304100041d858214400d0210783c03082a00090032060b816480910300f02020b0010744d155039900300e240086142d00212211b481c03055130314490b8003501554104070b681059056031014078041c14421200e14800c030244c81680c03c65680c440214075a200d14081c04140248002d00702e0300c50749003804c014180002c2645580035a0862010b000001d030310000000c0035034004465403901c8090681d12035180000748501411020304041d00000d0580f4601c22503d03000d031881c01074a10b8001c0d043c8007074031045c0c646 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 217819505 1250 217818255 217818269
    0x9060405030910170403030603020f04110910020f1504050d090e040303020c010221011404060b0304030e031c03091103031306180902033105030a050d02091905120304 73
    0x200010302d000e262181068042100300d00f4984410141d81d14880c074400e10403281200400d64a0109005520b0821718015004008541c180310304015040d112205000e0111203602610078042440b040500074031111000321319250848840300b40c10015100301900c01e075815602d600903540340e00c0c0f6143c40303104d1020513a0010a8141034035111686c0450080d840b02c0d121800340d550a0200798000d564290380580c00c0090303084c40d40700703035410300a00c050f0345c4982144042c4120b1410780100440d08030030302035035405501804e120941d0b254410100b4100011900079017402115805410301568055201040290048603500ca15030012020325035070b0f01c54011507044105040c00d00704140c62203006101205500800700042c099650500c41c02030360000e8a8420041011229810311400007400344000020603560f001e20301d00003900d032207483c1d10405c485181000800a402030343e81c103d64045424090026100c026405443c07000000e0300215400b4162003061700960320800d0b4603000054905840103 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 217820755 1250 217819505 217819507
    0x403030507030c1110030603050c060c07030b10031506030c140d1b080307050c0f03010618020a0c0c081f0b180402041d030307110105070503061309060f0c03050906040503 75
    0x119440554145011400c2180c0c01c01425241c01090b485401d030508845c1001c0c1c4001c00c00c98154074002e410501d0103154a070103601f040c422a10170003000038103041200c0c0c0100c1c0302481500c03400c00840b10b504a07a00040c21000c03c0712504030315030f51550f0206c001c90b4011410382500503281c440c45c442214280600c01e138001d2000050601050002003034528150340b1000c80d04545958151050564101a1065030103400c100c83e03415450070640b45140000d1b008130003c11025040200c050b0070004003189441c40c4603408108500154010b299940e2040d030400c88180d07000341c1d00d0010070b07543c0d00040070320055080700d81c00e4003116482c14020020710740c0c0f00034401c154170703007041649001c804801002a603119444165502c0c4d40d03d408000410361800d10000b56a5904d0701c0d00c009805012640c411241030fa251208020110380d011054941011040b00d409040240c5032a051019200110010b4956481d2048189400196510400d5452000c2d28140415aa6070b07032030f02d855080032030b00075100d500 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 217822005 1250 217820755 217820767
    0x60d0f020907090e09070f052403090a081308012405010c1a01031407081b04111e090a0506030402030c0607020123030741070203012f04030305 63
    0x141c109002039000500e45040703100182e580300c2d00200507105403000000e58003c0f2200303020740c2c1000006031001c0c2c2403d841c4054401d014801e4a1081c4989002c0410321840204c080350b0304142c20700140c03d9407a000000340e03884840364001c1079200900c0307200f645259882c0c083c11881c00303825144242d001e46110810510315524020054a01074a00c9404851805801c048501e8169128031114040c5010b42261420044200785007442d00c203031500400104c1d80301500c290707280d8021a4088404840c01d0703501040700d4074840c0b101c0304540580c040c003107040307183c0a80b400160848d40d405040b0a00088508005080d038403024002c003440180d4010750150072000442c80c050410a0080441300d20624210b00190314200440c000340812080358440f02e0340000501008941c0508285810880c0343e03034440401c8402c4c020008207010000b17541e05c000d0850030301c850752144400161942e036a0054000d0044824408003840360304103654584000441004500b100711403e0302c2a5401d0300e0385a141c0d10b107080 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 217823255 1250 217822005 217822009
    0xb1504030303060e150307150905090108011506020f0318060d0c0f090f14042007030c03080604020a0e01120e010e03210c071b0f3c09050405030c060c040e060d0f02 72
    0x800c00540e12303042c0403200200050b29290302134400e008202c0706000241c002d5030107070012100074080e4046421940541503100940b00c01004582c0e242118000c1024011403080110b25207000341064000740503d88500003c0071900105103040411440ea5901d40160b03d8429102c0c242040d4050503082c400c808541641c0790038594005c814000200c441d0300d80103403182020101c1c9130700800c011000504c042224208054000d0103036a0450401c0b1015401c010605100400c0e400100c071b021810020150f5100f01d800115510140714011031000038000207010052180e03807680003940b8485c5070100700d844030030b401d40c1c40c0706110f00502c60008002d10303040d201c1d11038040d0600701135240c1c441c81d2540c0c000001c80d00c00341440074000340743c41801d14070100c080310080d81c0038800014a9107500142c18411444040c00d210200d41030704c201040011f02c2d910380d414006d146001e440300100540c0704a10a200d90f40c400c6402800445452941003a9196503e00c2031189241c0911402444400421800d00c014 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 217824505 1250 217823255 217823279
    0x30506030d14090415150909091e020d05061302030f160b0f0d050f06011e0503390304020a080705010f050d0b0d031d010c0f02040b1504030303060e150307 68
    0xa03d0040010940307191440d182e00005a5590040d100d000751034490485c2140c2061240004000c1c01c0700c108100505130b00c8152130104491404c10540c1e130020007000455984108a04015402204a64841c0750003947c6145200c9040e4043c0e00c00d12a007081c0528145000403081050100141e05038822407501142040340c2c0c2001c009071101c68400d00010305100c82078401e00d4400c6400f6011611b40742403000005d8999845a0603209652040841c801e001075081001c0f40c1e08100303050080c00e51902401300100c520500d042288104801c500d4040c002195040c02450140e0300840d002c03500b00340da450440741c0c0c0394a140f207440c0c046001c0074644154540030700058240b9081c6a44003050b101c0e820000910890508a02200030902025540295014120180b442504203081c40d09450010781c5400100d0b50441b980248981e4a8011a84041c0c0350880341840707041071265140e85a40d22440c01601520007806031540d44049000000d204403905000104402d034041e015041c000c1c2003c10390229 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 217825755 1250 217824505 217824517
    0x503011a1c0b0a0b01140702090712020403050604050c0906120601120c081c021216020603090c181501092405090a030302030c160e0109020a030b060c010903030506030d14 75
    0x40407040904002c5020206000e1141d2081e1000142c0041c920780090a0000a4020540390640521101740140ca480c114a60011300f2030a0118400380c0c0401d000703020b0b02c83c03a00020058000c078801e03c8104800002e00051002c030443d51821603588200074409200c1001980c0c40d2660300041c0100440c1d421304c17698001e1140202c802964075078903801003514002110b401030045000d12812a0b2080c5d0303050200001c04903104c81c21510f41403640840e01018404102c010303100301c0000012034403600007004031000c950f4028112240803c03000e061219054800c03140d4410703400090040e103691b90300c030b10385040036104000780403400d1a04660080501900702440c0300f0500c035080040005070381e600300006009500c02d43c000c654032440320500c10708008500203805144400c694062210321803802045041da280c400700180c8030440c00d002180903003000708220307402c0f0000046200c01c4250640101880902a03203050100d502c0c2c5030141551048030b03080b0000000c50049018046000000c02490 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 217827005 1250 217825755 217825789
    0x607080406020702060c0c0108010623160c0605070b09191b0323010608010516120f09030801050306090c21070503070905101403100c03020717040f0503011a 69
    0x10030403d10f90701103070040d401064245010750092111500135a4400b0085003d4a11352509842001b164284c861144901d0500000b0010011402c05c004200101200e00c0c0107810a40e0003031042c1da14400507110f944820b03000c0d40e04581c1c10f0006402e00d0b0001560202400c900e502da60020200c545130313810340c02c02084081c98004940000000410a0001d2070400590304410741540d86056071009400c544082c0d200800c3c50341404104441c801c58100510f100c0d4081e800c01640c0c0480d030001800c001e10343c0075050211103180c24112000d0652002e502c1d070694800350103c5480d42c45541c0314175076504101500a41c04140e598503080340c10419012009070441607001c0300c01c00c545880000341030400c0c9400000a4954450410641c803988200c00c500801d884114070407802c1803640400e031151080c41190354040e80f1101d086036824401d6040782c2149400402c0480c220058500140b9640c1c4148581c1c800e030020701d1000700e000d00e01131040c11140d04040d03172030b84409400403003804504003550811031 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 217828255 1250 217827005 217827007
    0x6010308030c1204080406020c0f090c0f04090c0c03090503190303021818090d4409010b0f0f060d0507230a08011a0714010204210203070b070203060708040602 70
    0x5034181401c851164013076803150b0f1209858a00301400285441d0010f246e280c0f1502e807480c0f0805060700c6510301c140d0089800d46885a960001c1802808180326075401415141e15280b07550001e1a4456541144207100369070f1f01c48120b030740c2d070105990355004004020801d9410040c55000034040d03402400980c22103541e01c1c004036480070000705800c07205c60890303018800707960030480241800d1104025240c018100740b0030b1424242c01e195001c528a103140d40000f1822541080c2c0440002c41a071700280c000b9030902071915000e0b007c14003919510300110f01443c10311803c80c41502e480c0e080080f400318003401103800c2c90640d40440018150160860003441404142c4035405074034080380000310384450000f1550780705c104c8002021054141d011f040c642c01c0d030710070581c10030f00a08200d81180d50840d8480c040200903207007450091060ba4001d05040030505140610b00c29104510700500c1c0c021415240001d5851021288610407100b0080d0705030400e90024600e82c0c003a24034070f900301d0700400d001 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 217829505 1250 217828255 217828267
    0xc060608010c0206040b060d03080f040f06230a0e1b0d0b0106170106080c03271c030b09040201020307080708040e15040b0f0109090b01050c01050a0c081003020306010308030c 77
    0x50782110344158140d03005030016801c0200344114000c245800032825600c0044401c01c1e510020710144000d04104002191000843e0901840020002a141d0058002c01001200307801e1044c2c0c1d1700a2801c079034201184500002c0c00d001721b502c515003454550387d0141015100c0805440703904101103420f42d5000258000030f20200d644048424041c00c003a4032000010420340040e40210941644003400304400003040040c00500d0348280e0b034101c48403d41030510541ca001c1c000403410540d0708809010700c21030060710f004803560410300805000b00e48081180b086548144801c0340411200640075a00c20455180003a0040c8000e11000b070007440c8035410f0645503226034203203e0003602c8400200820700c182800914107445403062000d8112610601264420001b03000c420b2144a40e8950550b0f40300c0003031031a40250100e802c4004a40020040c900d0001e041200500c0354085020025000c00c0c0001c0b00c103a0000c180d44c06881e001402048260320f941c2c1da058030340d44001d191041410092180d = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 217830755 1250 217829505 217829519
    0x302040b1206150301080a030c020609030604080d06080a120f120504051c030203040201090b030a020c15090d02150a0f0b040c090501030c05090904020f01030e100605090703110306010c0606 83
    0x1400941c9030505a414450a21004103c100307442030041250340a800c00c0104590400000e40028881d450b062030400c0d441280005101703801240c030300d241c050050400300b00421184000401d8040c220040400c100c2ea01d660303070950703100a1807400405440d034403800f035101940591090988400c50b0b1a2403c1d94810b0010b1441c240c4a00780c50844035944000c2c0d81b000566032042d84400c1c0744205150850440c0307040d40009040402c80d102c4c42c0c3c001803000001c280110700680403540c003034521504880506c201640f540103c41000c40b1040198040c0c99090501c9620205188114000c3c014260307400b80c5a5602100041240c0000140c2e01903441c10a2070b52604c0718003420a944640340c585c450300d07502d400300260a64070240340d0f07003007007000810000304c0c1640c072680c1d40e0344c015130150b8030307141c1d50300010700140c006100c4020360f42c2040c822918005e01e042c126811a20548006452010b21354440101c00e6081d0f801c4950002001390b8180000303040e03940b0960b0400683e40c000d000100c0e4195071114 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 217832005 1250 217830755 217830757
    0x30203070b340b010e13030c050c0a0608062403070503100312030f38030c0406030b15030303070804140a08040602070509010b130b0310261b010e0f010302040b 70
    0xc00d419034900b40400c1c2d002d20003140d054a004285548407090f042c0340610101007001813228009040c020842294414020308100b01a010700c00942810315054940401420070b0404640c007620a104c1c490600d00340132504000002d05c03003038035150142142c80e10710702910a6000108900d502403103290002000c5022901d0040345104c0e1503c000502c403ca2070700f524103445c1c6181448044581c90350b0521080312045040550001d204a503842210b4901400281010b004038811607000341071801c00f005000c1c850313500300e0140c004440a00440c150131800c0c19181e00003100c0350301c0462441030001c0c02040382000820f058000c07150070703079001c2c10706540e606030240c02903004a80107074080c038420b10aa003415002a409004111a85d500300504004880c40c0c440d0360b80502d010900001c0b002c501007a40300ca4544006c0d100d03141c1c13500e0030248d1048010040c1094980e1703403100c0b44030341e041e60980410014164400040e040e0756400c0040c516806100f108842080178504040c0d081000013000182d081c = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 217833255 1250 217832005 217832077
    0x70807021c0c0b1801020a1509060e0d18080105330306040b010f0b03010b04031202030417010f050f0f01060509270402030609030a0509010309030309080d0507080907030203070b 78
    0x3640301504c07040b0400400e01580c1c0e44418035419540301e84001ea0101d413905242d0900781007030a038041010314680c0b50000260042141c00c0410744980235280c0b05440d000781c2c01c5402d00e0566013013944517540c1e0f101264242c1d00140e07002003807480b00b40068403000c44100c081c48181c074440007400c00495283d402192074a18226400c2d65009030040051203840201043c0c50300401d1410740c101d003154148000416203100714440140506500e4030540700d0305000740140e400405650082c42c148036200008613010b050003d010324842e07850840090b010692250360107000c2e80e00c0981050703490b070030f1640c10f5800d540507190311540b01c841c008096075020f1500702d01c10b101400c150032408243c00e251040c90301d0310b40c01500b601c2d03d9030014440d40e80003d5000c0140c039070003642442e004c0350161a605060740105040c0030301070140e890000c1c0410038246d068210724081e540c1c2c0e590f091400d41e42d80c90f8031911181207001c02949038200d26820404852241e014040810341a1422241070030a0f00070212141d90ba4 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 217834505 1250 217833255 217833269
    0x11040f061b15090506011220040e030d0614090403020a1103010626010e0a0203060f0601090b19020706020f030f090f0907110c060301030c180e0729070807021c0c 71
    0xd404a032080050511406004080501c0e0301c008a130032a41d100e5004800603502a05c1540c0004008c10099955030010500005107400782ea03510115121010007610043c0160824420305411818035805d05141041c40340b5016409808941e0503030340e8821a140620341020350640d2a64400b0581c440b11600280d80822008041c3c0000300080c1203460940713806010a4805410505030301c00541c1300410f000f07501c09140000c0c403280c0e039180401a1162509070300200032503000032402216060407024404503503603540e02126003040d5166000c03aa110804990003065030001e200d40305000810303034007130040e48000921080d0f169012402052080c181200c508001600381103a0004c803402c28804802c0c0310405640e22444c0d0360441c2c0f00e00c0c41801c054403908225003010704a4091501469104034400d400c1c07281079403222030b1f40310b0104280d010b00307070320352150b001311156100c00156080307080310262640407a1003410141141c0070040c000b0100d0381d003005510f00c00c2c10f405000030000c0d00284c0181042c = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 217835755 1250 217834505 217834511
    0xa1202130e0a020412020918060703020c0f0a0201020d0f02030903010906020301031a010f05011b0c060f0e04090c06050313060e01060905060f21010204090e0c030111040f061b15 78
    0x240c594540055500a411808a1441040b0502c11054a07507517007941c958040e038845516481e038054011402000c80b69040544c01a401444009645900240401c0c2020303400c843c01c96943d000c1c22a00c4010041c8002d016078403120483c800170740110000b850307080301401502d003407041c0f40000c03a080d245160f40c100d80d0640c2c00001032040090404c840745400d140c402c00700200c0d606101c80e5a003004800d0043d20f043c09174030202d000f400205948840b401907440b000014445544a0b80509a10680c0c4500d0300820b07085d01d035500c03035814903210300f441003038004100c1c262140c982340c0e050300c05030b1020f081d1005150f800d0005801203402800381e0b400d469070180c0009810f502d003407003c000b1294040c1545100310701c40d402188090b40c50580015824100310160b0040e40e03030903071702c5074020b124a034408d13810070303003090840b181112022a017500381c80001c0d1300130300c1031440450405555118074002c1950307001c0703d00001c1c0181441030310303000304070151040300c8180000551103944441110340104440291 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 217837005 1250 217835755 217835759
    0xe09220b0406050906240f060d140a02090f210f061510050712030227030f01050f0c0a02030f0408010c1d01050a030b03070e01060c0606120201090b0a120213 69
    0xc1e1a03c01c05500c118100040c0440f4213095211002da294204a1225146881200708245070f070f0300d0341c8890304028001d100c6591889100410303405811206004010307940c62800040e89007015000b25158100000c05c40403006000784208802104117105050102110860515030032000b00140c00c017942e0700000400c2036240ca160004401040341400358051560820100400c5411400b030b07030101d03588a0306444031602c081008800330f0184108400c010142c2c0b1504009080584803a441503003c1036084c1c03100b2a0380600ca16090350020303209080c02d0b0725401c0000f0451107848024180d0000184192031a11080d980410f140e90456044401c0c142d64890b41c0507492508004c044d5000d114030000344145401610010f00a4041e000080041c540c9038103c05070305a0301440204050244401c01c043c055868035801000e801e0415011194545005c2c1c000c5809071450018801480d8142c5d51040a1810300300341d4000c0750002e14141092010030000d40002600500140074140c3c000c0c451078040758 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 217838255 1250 217837005 217837013
    0x60406050915070305090120180a05030712051504110f01080118020c010f0f0c091d0601110a05060702030903010c1701090c050c01090804090c030c0e09220b04 70
    0x200060541d04a65000362414407140c03454021099010540d400c0015855413903e08a5015011100a034180d141c06001c051115290702070141880801804003003202d40d00301c200303001c6a81c455015559042c2c0c086c0c03904001c0a0100003545012502c10401d54000e00314088030242024807c0e03a045540d900c01005c602420700b000c0c0b02c3e081c410701091900c1c4501c0c1d49425015403008500300203440785580c0001c0c0c4a220300009400503561190203e0301004405100300c802c9001b0b112800b8490002407051034002040e919009034141c00744074220044000d911668019200884045440c00050244000107400f09000380806031180b00c00e44c020f1907444140340100350849042c03103081c801340808912104480600ca07070085040d0350325080006603060321200107407018050852148015802c22070000304112980300a0300450350401010f0102e00c054900540544803640c5100700010315000c01110350385801302c5d41e90f402070a800100f0241c903200c0c11703d040b129605464107a1342020780805000c100 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 217839505 1250 217838255 217838261
    0x1201090f0c020c0f120c06030f0601090b18040923060106030b03031305090705070b010b090102100c05070f15090602070203070602010c0804080f0904091109060f060405060f0912060406 81
    0x500d001d84007030032a07820710100151080c400740032058003501e40360b44028a4030108101845540300e00828258032898101031501b14088103e41850000d00841c0000032102503400540b01950002081c0122020289042c0002480034940c1601d40509010400051822055420041c1249440901030640c140403001d000d0f102100400d41c001c0d0f004101104196015151180c1507075002ca0303c65142c1c0e129140115940e0280b904050103401c0403200009000e0b13810b200500710a030083e0292643c402420448070115445100c094001c110104020b82c0001c030760200c04458140705041260032404948007a80456004000440b0204c1e80050040103600d000c00c0914018601c603c001e112007a00024014100200500001c094242c046200c424401300b030300a42d40300d154060300400402e10700e0705058951a60001d192800349110002240407030405001066401704060940ca24180c502800d1015961100000800034a810302500c01a50b8070445030000f0070510100900382810941004411 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 217840755 1250 217839505 217839521
    0x709050a0b090301060b09062a01050f090f06190b150f25030203041503020915030406150b041a09090f1602030918060d02090106110d0201050c070b0c1201090f 70
    0xb2050902001f811a500c0008550000100b80380a02000148066841142940d501c00007070950801003001960011400014801d8140d4801c80c4c56412102080c5038a07440160b0307a054081d00b04002c055252841908240340d0104054030507a042c2d41e040c190150b040e008403401f050b182c0030024100c0840040450315080300194610040b101890b542d902954038442e80c4241c03102100d4204015034194004d50541d004901c02900702441040c3c0b519004110307a0040b1000c40b41e2600d400c829141320b00c0c4a80300201901c882c0030a82d440c1c541400c1868580d0403803d50110380030382c010400b50b80d0035204d154001d4040c60410103807003c1828001d07030078580280d25007840c008643c000c1c88035481d079a66204001d401d20140d10001401e54403284042060300c5035003480690840041030000030a1680101c10000c2e410391941a00d0301440d280c54100d013a17940985405034140030178898400483c00304a6031541081d4402811480c00001d980c070071411981c243d0014078007036511000c00c41c116905002c1c20503 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 217842005 1250 217840755 217840769
    0x105040515030d020f0c18060d0c120533010308030a090519030e100903030503100b0a1101061502032205120c030105070c02010813152c03040b120709050a0b09030106 73
    0x20034040780c001c02607000c44008103124401c0607a0100358060000c1c190100d000343c03031409402110940c860520960355170041c25040304404400c0012153701c0b04a102c03900c03d13a607081c0035142e110b03440c40e15804a142c002820030140c01c0e5880b4403a200142042080d4178650b008140406801030382401c02418404e40c10136401e000d000e81d03008505c0c240b6800f80f800010382ea40750030302e0f58880d255458410740680c21500180c5229100085507160f10380c00908a00c2041d01c0c00000388a89a200d2400c944542c03110125103015910902020705407214070644182505c031140310080159950704000380d13400c45000d4079054981c02c00315510646080c28000c80c4d50040b0981030030103084010f40d0000700b009800800d4811030701c000764228030402100b49149040e194500c00240038001010741c904030341030305492865082e40403048480c0351644e070202c26a01251000c07400c041c28141001160880000020294030420030354176404640d9a03110a40071016001e1075140c140c84008841c207150840302d141d00105 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 217843255 1250 217842005 217842019
    0xc1e030c05040b030702010216060911040209180a020c12030108100c0c0809030c060a090915060e27070801030b0a110d0f1517060a020a080105040515030d020f0c 71
    0x40303621078124048900b180d40c0c4440c81030340d0381d5800004030300a002c0c0c140d183d0010300c4c62101c00b8092242ca81c2004404c0350041d41c5107028a510038040104a10030004166040901008005c10844040000c2d5a10000800001d442c141d114601d00c1c2c140701ca04801d9210002c004001030248007400c01c41e00784d030301c2c1e0120b0082000495105021b0481030000d01c009003c003800252002c0301d03031030600800314582e0000d81583c0d26100c4c0b01a01900940890003407003105c0746400000044440b02c0c1d08503400f16449500e841040d96018020300441c8080d01001ca800d05088038011001550307240d00d000c2c4107191640d1502201c0d411031a08002e4070f034020b0310501d04a414a601c161890f43c140040714101950f01c040007a50058410281024280681c00520344000003c0009030f244c00100e0b5446c0300b100c0c0c40050b07495544d10030100b4401ca0107003001c440c000401480041c0b141d0704051b440650048200420306524001d2100082c2c42c00c1c100810751f800607080003480751000030040014a405410031242c80c = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 217844505 1250 217843255 217843271
    0x4051207020102070b09040e07090204090c0c080a1107120f030306080a030206072604050a11061309150306020a11060702030903030d0f02090d0c03021008090a0204090303020d0c1e03 80
    0x35070325689401080e002102c001054501b0380e54540c0185411811b1500f6a1781c01d65641040000030741003840354841a9040000800c41036100b411a091b00701d80c4214060308154800400b260700000c85210103030588113008001c503c003c0307001c120100c1948a08400480c0000c00e1a0003000c0c0d4019600a4846601c40d610755000240c0101e990b40e030103015464040c0070034080110030120405602e0324124402000404e100500402190038a4400d002d11400d808116628050050503c10401f1600b140c620300001404032450070780080e10a1302d140541c0b416229165100c507030803644505010790208070300040e01c0c55180c50074840140d0000340d6001450600b4207520100340c03a80315034211511210780d51088c4000ba0f600e1039040d0b4942c80e00c050600315901c0c0d00303880c10214030301243c00142d01c100724001006d40c1603485841c1d8580300d4800e540c044d24500c1c40c00d03820304c0040c00c0c0c140740031070505800344040c00c2428002e100b0082c02003500c0c5c1d03900c006100700640c030505402c0d0707101302c090170542001c480c = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 217845755 1250 217844505 217844507
    0x10518190c0207120809030610060801060309050304090c05120711100e0a0c0b0a090806060a03110d02041107020f0402030601080f04081e0d05090708060105010c0c080d030203040512070201 83
    0x14404152400010201e14910010320483c1080c245802a207440c040b032100c1a814800080d002d40507400081e800c4485907145d0141c06007030076500d0f10425000854810043c8540c0e0b205ea00b04221903032180d02144d007003940300c480000c10345034420780000014101103540408004d05802d143e420444a042603100542c0180c00282c80c1d000e49a00f80f4049516100940c1c00d100c81007011111140c0c00c40340d00101d954030b414002c6200c0d03119114040004840c551f02144540e00401c28030f0091070020200e40e800c600e5641c58a00d10824400381c151300201000485016840f10f004036041c440c4081d00c5203035100340c5481000340300313280407140c240105d1050080160766608096055040300320440c0c415003960f0b0300d18014040e4410040088004c100685602c00700d00c0d86000a0200c8082c1c0c501c041c0309640d00d00c000c1d141e6600305842400c446620190041080d0350003108080705841c00381204205090b212441c1610b8000c0325032810f000683e0020402040c01014051a0f070074450618a20b860520a500 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 217847005 1250 217845755 217845781
    0x405010e070c0f0c080a1a1306112b0e060f040b040f05030f090907020606010f030c0224060f1207060503060d0f050601061e080c0306011b0605010518 66
    0x448107050118408404080c00090503041c10340551150b0000c43d9130f034981064588415072460220f83c3d103142d2400c40c01d18220040740042c45208000d021441c0300490362203c0016210071000e8444414040241c45c4441c541c1d505900c11204d10201060302418004807008200c070100400a05c460300910107110442120401c07054216030016034021894480d030800c0c1c6400790707207414010258400011400c02c0101d004010f44142d0008072042da006960b0090142d0302c0c0c01080b05c5040c002003400490b105814026030040c40d00c0d0070544111810a00e81c010095240b82d600d0401e43e4405146c8420007241c5d1400c00640d016044040c0c40100790340300c0c0b148020342d40388503901a0b1418400044002101c60700d03048104c05506d41c00003100c4140741c0c45420801c3c1c64040c2130003a00300090b400300d02440d0031802854a076168a1143e5181c0c1d9031a6036600000c0c00540014018504101445070705070003044104a80195640c043c542c0050107514000805c8500c1d240761591005101200f410000c3c411000f10b = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 217848255 1250 217847005 217847011
    0x60f0a06060815030705090f04060c03020405011e09050a0e090c0a03021003050403181e05030616030b0f03031c150f031e0b010b12060f0916030e19030e0405010e 71
    0x20300043e0001010700080d00b0640c55030002500101c1030400c0121040751410501c0c010760140d030041056402100c0120706a1080c1d0040c24003245000c010b10740c481901c503459900b011044d02e0620b03065030b107500010325036421a034004400c440b140c006100a110341489910341143c0c00719541800f261031540865003e450104031201896a58000030341814015080207960202541e103000c1066150a40074600521070203413051035450300c80000c6954140040d0b1140180c501f80c00c012842003100c0700480140200700201e642100a4504804c001e44040029101c1100d20230179048108240c03411407011662080708081300207040b15420054881c5e644014000c2e260402c9440c0fa00c0b041c2d000d003104103a09801d500070803410202d800000e00c02c2214000c1d20030344241401001d1140c031110100415401544200340c4d015041c0030200700032840c11181c003180c00b0365a040125100308030062003800d160712030120316030041c0c05040140c00c141d4000800e041c00142200c0c200a01e5042100c01c4051030001 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 217849505 1250 217848255 217848271
    0x90302011a010f141614300c03041703040e070503130327030b061509100305071107090501171f0f0e01050a0209180f0708040c090905060f0a060608 65
    0x1481c484005444070089801711601000d815a40d40b81038039200f0982d00c0041800741007801000c04400c0104610005041da008120540540700c81c0c0c3c079666000550300402850042d44020000011107142004184091141e42d2010f1a00c1e00e20f0910450400040209030b8420803034104104002454011609101503415140040061001000185c0c8407941584020742e000f4150f0800030402c0342d00c005180c46880146c0d0f080800009404001d0134a0041040312940904520903006d0814460742c007032035000543d40380c400c2c0442e000d42c60980c10314015400c07404145854000500c8084d4522246c0000002410010540d15000f84140601c9808503034032203107401d45610040701c03204121780101d40703070f4190300c00204001d0810442c00402984100c8a80313005900f580007108064241010070b80c1301d8000c142240c400c81e0b4541804841c10700c8010303c200c41018032440d011410002c10711642e203900703104174010507090078204c50b00764034054001c0442c3c94650034084280002a440803011380c010241c = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 217850755 1250 217849505 217849517
    0x10615050a1d0d0f05190c0b0705120301120506010e09030a03150f230301150303030f1404030804060e071d0402040f020c0307140c010c0f11090703090302011a010f 72
    0x1082c0d070002540c0d503050752440e44880720010000910243e50100f06146205404881c511110300340890000542c040000d8060384001034100210034585004201d5075100d0070070b4075808941201343e04400e402c00c2e00418002c449941400b81000420807559000d080030a5801c540c500d0821081c80d517038415031411100701502c44011041242c5020b00260141c0714010020810b0f0740c03640499015000d441c60498001d01155441300900c2c1018440d0f11407034903036a000301566a095440907005868600c1c0c0c160021075503082a03403071610810090070f0040d44030360703500340840c10a03051000503500302c90360030051900484000c01007403880310200071105002d101c00b0f011075035a81c00014000e19140c09101c800314000120150740404c08002048824407a44415801c802c800c9240b5070740303038007400704640420341e03030403000f404100e550090001580c81210100400c85584d0046402c010040d100301d0082a1103c2070701302015020300070300c000d0100c54600140d052f10b20300c00080070300700055401c109200b2 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 217852005 1250 217850755 217850777
    0x100806060d1131021e1303030503091002040b212404020c0d0f110d0f03050c0904060b1e191b0506040803040c06080609041b08060a0e010615050a 64
    0x40c030071a0303640640402c100440d101200701040c3c4006544064115a115100368201032015242102a940341c0f20540d0b40303900c66181999001d0b01c10380d1010307081d007905203e54050701e056001240000e10140c540b90916580700e41615180203c5606d48602200f0803448410411012070881860008010845280d40741c60350144404200288034a1200000e1401000e00c40103480350420f000030450342883d5101130044444400c2c075130f11071507002c2a41c00010329205641104038070940106070401c03011100740785016488000102240c1c400c0e40f0100c0180000b107004505802d001c940000a001424002c0389001800714031741c001d045c1c4c081d09242c03c0c0003c0b04082680c040582c01d5005240350b000c02100c03a2400d0a040c00b0450b508101ca046407a02800c210214500744a41c8000d07000d050050072061981e144c0b59120301d208540c200c02c0314004042120000b801c21400c010302d030700501c0c0410300000c074040902969170a58441d40c101010000e03880100d028103940c09011501440d241c0e24019404030 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 217853255 1250 217852005 217852039
    0x1106090402040b13240f110d031d03040b0412030e120601031b0e07142106040c0c020303030403030203060406030602070b061008060102030a032003100806060d11 71
    0x40a65511240c00c1440480c01103800040440240309a40301c803c0010003203903803100c20501500c10704c0310340c03040c030b03041d84202c13581c540d01680b0050490529828400500c000c070b4018a4a0000042c0c0140002900c030b414070341c6d007651212918600b40403c040075600d82414840034007564411031203540c0d040c6440c002c942c02414411030802c10020301c01840281e184854542240d41c44000380801d881c1c00100c05c020348000c44a03000039030111010540e56000c00c0d500c0d0041681c0c124501d0109800220040101401c0d11303030240e8842c11030680080c01103c0904200c0d041c00b04407441d410f00e40d000d01c0342190801d000350360700005a81d40550f25103005646da80e10400424054803036130f4001060180040340100400011102c3c0744e02c10582500c00d0f54000003110002c45407540113440c598056081003280440003840b1303420840da081040411115007001290b6501002da0080744c200b00c80c11079003941031040741400e00c5000d400180441e05501142450b0300da0005580d5464015441881c500000303a1103d = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 217854505 1250 217853255 217853257
    0x209010e190b0d0e03040e100609141002010f0e0109150e03031605040803070305071406161b0c06080402030d05030c040506090d02030109060e0705060304050a0609032312060d02010c1106 82
    0x15115400c0e40c0c1c595595000074160310301f00780d0f044010311004800200720f6078442c2c2403540848002c03400e04d41c08508030400313109100c0043d841c00000c654031611844801c641c1c03030056218403072a407000040c01e264035051102c8505200d2030000f01c800d05200c014244045c00105036900202000100c1d110030304030f000c09990611540d40040410700011400300141030708203000e070140ca03008d460800303212220884002e480d04000c4130968440358107501e0300604548500c58131400c00200c0404411003044688a075104a001d0f9071010000440b682c041008608043c040900144401e040041c02d6040500c0015043d000700e002d8030303010f0440031035406ca0564518107244041a00070780200f2190f581070600d1001350101c0c0c01e410595201d0607400060320308040046900c0303613400030050940800c1594070340000c0e04803100f0a504000102444511100550014102007a036400c4515582d0060411a100c0d44030000c00b2580308a884080c01d1001d030b40c014000d07048203a80309401e241c1940ea0b0ba4006000c07 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 217855755 1250 217854505 217854521
    0x9051c02160317160303051b09030d050f0d0207050d021203091b01031d0d0f11031c09020a090e10061805070203040b0f12060a0b16020f130209010e190b0d 68
    0x100302508213014042c550180e010500400354505031092040101c04445000d200da10706568142e131000c400c034801e180c0b10b02d000d044103002900f812480e11000307601400c140d0304140002d80b00703508600c0322950115010070000c60000150a0130758123618141c100b031925114080d404550303a07400c1d0700400000d41c4c82a4031113000e51802c007012051a9012072001c44d81c900010f11000081041c003c02506c02e03c0c02809020b1004220400451a0055804d42d9190342400b46500740d0107262540c1c1e80785c0050703403180c0e200341c040c15620100081d055042020a450004501e40020700285800c10512403a410310f40d0402200c6444070010440792a00d120072071a6100e50780c002c02032444080b6a04101003040c0e8010301c20b0400594010f000c6445650800004c12401c0c444d400c0303c0c4804020b1440d0070581d180c6d011244900050044682d244c00303402180d14015600c0160b421203500144031a021741c0c001142842001017036031605650308440c04813000c00e200500442303004102c00706560002d02c80c1c2d6044071803 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 217857005 1250 217855755 217855777
    0xa0b2103120403080906061909020f07060e03030a0b040621030e0307080a062007020d030e03060a0f05100503030a120b1503040c0b0a021b0402070609051c02160317 72
    0x1072502c0c0c1070041051300b05540c69001401481c000c100d40b071515460084006241c415071407080c034588034440c0002c0d03020310b4040310241c0040c82504085005889000d10200480b801381d6540c0c644001c83c2000c131403000040b03500c518a4920b050080d441c4031450081c64160fa400c0599405c8014241910701e520503612040d4580b04140010032141404190001058420f0400b0b000c0342d080040d415044011041074400c0c1d0380c00500c0321070090315107100152030721802400c0c445100003c10b07021a00300071048401998443c0c031900c000f45103c2d114491140e01104100c07040441d6803c0c400026105d214480101040100441c070301070410900780d01002406a00402e150076030001e8002c0d5410641045900b03554805581000103a50b4038040222282550039034007808a051903d50324446a00c0e10b890000d4009500b40071640000311144148503a1034010401403003100848046064400d0b02011f0800454000b01100c0d68180503500c007590949511210030030189080d1395503007041e40603c202c840d03 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 217858255 1250 217857005 217857037
    0x3050a0e030106090b0f060408061f0b270105070c170102091e040c1103030c070c0b0d091b050108011401260402030106060516061d030708040e0a0b2103 67
    0x213190325031754400515500d00b82c80111a040000f41000f640780602c2c40780340e0b0359800000c0091518400b4a071924415038114080c442a00c0e120402204550004a1121841a5842d1101c4100185906103046042003468540c2c40d00c1055034520f42c009525124604074074100262580e500e10080d01580c40482d4083c000200c0450449800907641022485c0309001b9881c0035150a2042d22886d003405051818000840ca507480e2071100e070074179900004098920400c9a200803843d500690300805516008001c00f18508849040c105030f0503210318514050109801d1042006980180c041c60440380070183d45883c0d0441c01c00140c0f410051813000c05000d0655080924140c0c5400c0ea4050080f40250002c00c40203840e49025201403250000103241c0c200070034002c0c00002d259401c28045400c2c40c5200c545a1000011140d2840d0042d00c02195a4072021030b0602c64104c444e454158040f400140034401c1e8518903002c1003005211800c000340c100c0400c2c0701018203820400803100b0040400c10b100c = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 217859505 1250 217858255 217858259
    0x1c23010617031201050904080a0e01050706091104050f07090302011404030b0106091703070807021c05060c0c06090105070c08070c03170918070e0111102a020109080703050a0e030106 80
    0x82e48079440701400b94502c4280b400042080e0030401d451901c207a038040300d5a40b500c071517814145c94140d120307507000d03040117801c000ca071001601a0049606052041002c9040c8201020400c07096440040c10544200c46240410240030b078413141c4001141d40a08190400481035200a401c1d4462900003034000c07880c2e4400003070318507404100c00c0c00b103400540d146140c41884016a949900c5608000307888005d0602c004c0c409450b02c4101da000c80c0182100ca0203008045030799050900b4070031188401c0303076000030403142c400030703000e11502c0d0b80311440f071008006519150354083c148256a03600640384450224001040000346103c501c0a107801000c08480e02c00e80045411159210b500324038066500c10110b440c4900e040150b0501407409a241c0c0c0c0f003d11109401101c5030170201881981714800c100c0401b9802c40390f48100c603c0a4450301e09038170042980546038080c3c101c0c040000702168900b54020000c6024071042d900f2140d458600070750380f149414403c035081c0c0a5041c0c0c2c11b50551174203c0c0 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 217860755 1250 217859505 217859549
    0xc03060711100c0c15090c050f040212013b07030c14070f061b081b0706110403050c060a02100b0a150201380904020409140703021c230106 61
    0x200c000309445150701200c2e0405c50051790054807240e02d00101b034602081010300140c541440e041d022048007030001404c0c07100780442140c02d044284c0c042c618000000320071807216003003030042ca041e00710942c1e107003c419102c00d07144036150b0340010b00140c1019a2448001901d41c40307108180c00e01c041d4402480d46031000b90a104988440418003145c4246c03400c1c1c040600720700d00c0c050300c2000c81c00c0c0b03480d00ca61039030314800400106c1c1d40031842c3c1305510100708140e10000e070700ca10030060414035580e0907984860440c42e180d4130303280011103414410725042c41451021540081d1801030040c2d8a40e0104082030b0502c0456070f68011604119110b01043c9110f8004940c15440b000c0c14012481d05480d0305a83d800000c1c030f81d00c140000c0311400d00691000000b650510036455500203101410004c0d90b400359031101006000309000840e1981c200303080400c02d40c80c01e049182d042c0a002003904a0031101559100c5a20704142c1000e00c10b100300c01940d00c80000300303600210050a400180000013042014 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 217862005 1250 217860755 217860767
    0x70203060f0702010515010c02040b01030b060d0603060b03010b0d0f0c03021203180603060a03030c0807170409050601021207060c090f06020c12030c0d050d090807060501060807020c03060711100c 86
    0xb1404019880d110004201100161000d41c210340d06840d03030381351405c8907001e000103400c500014905164642000d04015140e020050075011b03001e80c2d001a5081c10751a00006031544511560b2281e030410840d2001540d81d04178010000341e02c230742c8004540c0064030341000c130791043d503002035030000c0c00407010340c1540700120040038000a41d049103940007403204100055808180c90564208a900c0402e00000e4010020355031640e005d2910f45d4104030f581e0303940403082c2c3c26041291038000c0010408020202150003590740010090001c0d00540d551100f40b01f00c5401029000307008241c8500101403000c1c00f6100c1c0c58064401c0300b0380881190b80b10b9001a50b50071004401c42d0180c0a03160103018400808020380700c1505c4031344003400742613480d00002c42d410b820a00b90710003002c0c0d580024a00040009009002e40c5108284c0443e1562400070041c0006100400d42d40075034101e02d818041c1d80d60f001c500b1300c5d40318a040c00d00004ca410f141d000c1d28070300708070881e8420700345241160200aa0360004 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 217863255 1250 217862005 217862011
    0x304120f08030a0b040b040e120a0519020c011107120b040201030e0d26010302030a03050307050f071a0f1312030e0f0a02100c03121d0d032004060206010504020f070203060f 76
    0x601c0c18002544c1b56010701084400b00d1740b02a1080c6c0011101103d00704d10840108110701d00c80c035265003842605444240d26510300d625a001581c06505121050350b0800580c800c1103841d140034090051906044154aa0302c143d401131207581c0c008009001c580c0650b12003642c1c4c80d20007049424200c241000134000c1d5207800004603c0c803654211603203640d01081e01c5076050b41d5018001e00b1942c24076030b4082d1240d800c00340c41103003440b105006041c01c0c11100d00142c4240d034013030f5011b919510444240d40d64451401b800107209241544200310f9a4001d6800e000c410f01e600114a48549210580c120002e103070042107a20240503142c2400540b08000810300710300c07402250041803041c4803641c11703030725403443c01402004202030100c420b894840a0340300c0e900c080d00c1c03600321b60300701720705802d010313040031680000c080100e0395480941004521000200e1008502c02c036241c2c2c80c0508010000e5074402e014455288075a03000504418040d070103000342d40230a079018003201c050742450340e01e04402681c05c07 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 217864505 1250 217863255 217863259
    0x3010b0d141306060801020a020a02040f110304060504150207050c0f03071d01050f06090a0e04030c0f050f0f0d0c020603040c03020411071718010c050703050d02010c030e0607020304120f08030a0b 86
    0xf61300818156418800c5405114003600200f50030b00d1260300380009000f051002844090350b034880601c050405070011446140b040f41c0c005403914007841c0c40b50100d4040d400039200e55105000010004000040031440381004403030441c4d4800301000003d180a050740c00691006000007174005403144401c2001e07050311002c135140b25088104e10140501401a4070000d80e00c030180010800030301081c1d84c816034000f1f0103840c004020005544410b8110000c0b41011500c80d0322440c50f00c40d0301a424420f0a80c4520814081c02854058100040400300c8065000c0c0c490380c0c2c0000882c0070040030444031001160f010340140000d4240e84902c4100f81c0000005440180036a011007641ca460340044449403803d5208104c21f080080004641031010900704032464441d0581c040302003807007048440690f25142d0300201b80e8900e0020000c05856a006801103181e000c18140480682c011065034290303048038144030040c0e22182420814018850400b80400400105101881080e500300404042c0c1c1 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 217865755 1250 217864505 217864511
    0x30b34030608010b1e09180303160315230d061109090c04050d060c02030c07090e07050904050c0405100b0307080709271509111e0a0503010b0d141306 66
    0x2544c003481044140c20210310441c00000203682c1e15480d0007050703945c01c2034109240d000c3c0045501c1105103158000d8580c04511041070241400581c2d050250a03a100300c00124100c40340c0c80c01464100790f200c9000700c200a1034014a00e80c1d0307682c94103180680c0c02d6800c104c05114400000d40c26051316800203440d64011201c2c0c100285001b4a05012a8219034024000c43d2801c0300729202c2400800c0800955800c600040001620408081184802130710701103200146070440640c01c549480e5440d4000c5000b2810241040086440440d81800d2150241c0340807400f9510180c0c0800d107800d0701d0300f1011500c0b0011080c40300217984140141d10450b010f4481034010350300c9a4041204410040c060b1414801c05480d43d00d00184070b81142c0c2c80d855180440c0d0300c842e038803264803000741c0710303500d16074200326038041408010144200030002c101003c00d08004d242240c42180101640310500405c44c1040d0000b5800c0500d0001c0d40c8402c0d84030f02a41084543d03410840c2d001c40c0580141d410030343c1c1c4142 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 217867005 1250 217865755 217865771
    0xc020606060c1b0a1e0501020c0d0b06040e0a1401020309060a060b16020402090301020c010e1002040503150c070c0602011b020304060c0f0f0f080c010c0801030b3403060801 76
    0xa0071800c0710030041d64a030040c80b41e082100090000100114031064101080400000d080031200e103041869411064002558900b480002803401ca81c54200a01c1070380c04800102c08035801070344854101c582510b01059154014403030601c0c051111600900118204942546002043d80a1800385182505a0300192150800701c0283c2d40b0074003442c40140b40800c9600390b80d00145500c1c3d5207052019102506084c0040000707400c9030400c1c510100c1c01d07512079004030183c1000344450480d01407804021400e283c02c04000c030781d032210f07881a2039920f108080c02140059450200b540c51441c2e00002c45854a87c0341c8100901808030401d18000760140848901080782c004816102030741d070070760380c0c0480750b107113589408124400320041036031060140329101b00850f82c400025122a40200301d42940e07a00800c940c1400c40722041c159400300b104081c0140002461b8001250700551460041700104038180407140400203612a0040d003070300d4440030103211030303010780207101119141802080002 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 217868255 1250 217867005 217867009
    0x5010c0212030703020a090f081b060c0d1202090409141618020901050412080a17090c0d02130914070812040314030705030d05100b070308070518090a0c020606 70
    0x241101110880c0c02080c00020400761117070780900011085841c000d0700f03265440200700600d2040d60049c941ca6042910303c910107030200103041210f900b0640390740d840c0101e50903d8948a407004c841200801c00a0720345501e80c042d20345c045c2c0c0c0c0720311001841081018054a00587d0380d502c01d1302c0190b040d0103402c41c40117640341c02c0410041200c0407022000040b080b00d05800c03000354410540a4103100c014803004c01c4050031526150202480303418919920150120041c051440810350200000d07034200c00c04c03588100200f80003080200a5030500c24500c0300744002010320b000104542900303072500710541c042c0509080c98410108140c07040d545069100d0340d5158071840181c3e0030402c0316004110420015200000b034031203013400320040d40d0500040741c0d41d41d411580f004010350400ca880d541032150404100d01803600602c410400710f4030f0080f2643d030190101c1c01c02020a070500102207500714120b10b0075107801252620091000c503561500e050000010005000d02c800184100d0300010454 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 217869505 1250 217868255 217868263
    0x9010306120201020622050303040b0901061e1a160b010501140a0212030c0f04090902041a01022a031203040c0e010f1205010b09070e040e3403080c03040305010c02 72
    0x15501a80074040907030b1088001c0c20011b0410032409052006180d140c3c0c089001440910b00684c4541d403188024200b00034800c0c01c0d5a807030b4014801074048013250b809002d003e01e480b04100c07071041385a400d05400c400b0075605540a2011210030803200d1500c80300c00c00c00b1008103d81a03d2091300c03900101110300c3d5a5804902800d0000c001583c07080180c50140d99000000e954821101c241040c600102410b0303418154016074030100505d51104011f8086281500540031040d4042c01c00f2040d413425080001e41d100000c051540c85201300c454000b41890403103c90140c0c240c00a8200e0350721004c0c030035802c56150700c100c40940321140490304c003040c42c4054425142c122004a1541000360341010071a010766078580d08212481d642c0c035990b00c40540c0790340b14860b115106940344d80030102410301c24403064645080348540c0035041f1078240710f0f101d01d55801c00e900b01c01d04c1c0707550130308850300740580070f5641440d540003d42212400b103a11004c1141c000010704c00d8911680080c010343d5003880f800d84e52 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 217870755 1250 217869505 217869539
    0x40c0306080c120a0f21030203040308070c0c031b0e100501050a08070c1e12020f0613060b0406090510060905060304082101080115141e01091a09010306 67
    0x110360071001c6202c5052401000703c07014581290f050703c0d9500e81540d188200c80d52a2a4211102ca03400300c081c007001c1599804152800310030742815031030340c50181c0e801844094018000300a1100c00c1c0c50100901c00c1c82901800510340c84601ca008108100400d0400f03034056108010901c001d2030002200b0148150b00319003201c030181c43c0d031410104245415211410001e020004205800c0e0310f0300e010070603042a14190b01e02d080c0e001c00c42d00c09282480300f0b03110001c0c11548190750000101095941d400501c072070f8044180120105445003500d030140c0a007044240240c1d1250500d0000f1400c01400d612850040a0b1500c0680100b5640c1c8001d6452003c1c503c10b07154020001d000140100d16480c00900c9000c0b000e40745018101846000718208040a0f0440d034026076603030241114a010101040c8080c1c401c2130b441a207002c03802800640008642009030741144501c1c2d00f5042903900610203040907001c8566840003100c4181a928450b0300601001400282481000980e0041c0038a03910a = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 217872005 1250 217870755 217870769
    0xa0809040e1b010806010c0f03030f0b0315040b0705070b010e06010e0312040b090607120e0118050d02040903021606050d05010b0301181d100209030c1504060809121206040c0306 78
    0x10041030b4801903d1a0000074051818044078075000800a5518116041c84520030344001503120303401c02c002e100300e56620b90ba56010743d00900074071a800050041071507005511506c020b00780e0307442a0b412500390245000c0103040b2031180c400841d20034000c011142c85100d0a07614901091404820590307a00c2902090000d03000f0200014851116114020407040f1405444a4a414015503500e4440c800340c1190303c00180c02a10401595a40480c3e0b040da68802100c1540c0b078142440000388407642c00803402889160b035203031003408050081c488522b8540010401280180d0784400c06020381d4004042e001c440307880d040000c250704109200703aa040e2a001c94504850014074403658006020040b05e107403201c0d800302d51a0101010410085440a480c00d8004d62101e4000b000d0501e81004440c080d03108140000f4041328246100c1d00341c40c00c95100b8940116582c9440e2501d9080c42015040e4012650700080c0d4070800031120140d56000e00e40940d42000400d40c11442141156200d0203464 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 217873255 1250 217872005 217872043
    0x60705040303140706090f0b0a050108030a090e040c090c051b120313050f061305070b0705031903060b070f030f02010b1f05090a0f0f080c0105190e030a0809040e 71
    0x162100f281c2e00290011601c51000080c6284903130b00c440d01c1c080320006044409080641c1084441c0f1814020540100640e8006508100340740201520701c01541c0280811200c0510000d41404181c0c001000101030054003041040c1490500070410703840303401c908a20880c2c40d90ba64145040015858680c0c641a802217415a00c40501105803c00d01c01c0c810345040c4541c20300c0a10f1641d045c4908e41c002e50382d0504001c880c44442c03038605c3c02d0a100340d10016103400c0c14020302d40414404011595020075034030911010001248082d401400340b900030b565681400702c0c0c03d0040041d2010b8001c489402910b801aa00d01184800c90030303030720664400c1c0d8120b22039034020300e0424440d030112503040b4014240a030812030454045104a1910760000f003040200c40800c006000203802c2d0b030000b400c03810313000c3d0480364520304c000303461481840c0411100c00300850300481028410801410542001000e030340c0ac0301041c1c2007400d065003202a54a01c69071500e80754495502e40002d10768012041c5510070 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 217874505 1250 217873255 217873277
    0x40614040e010e130c0b0301140603040c090b03030c0703050607080906060109051207050d1b0503240a021210050f0a05010207090203070212070606093c020c03070311060705040303 79
    0x40d0f20240000740c50700440e12008131340d2030005000200400f000c0c042d407481c1180c0b60340c98034035045c030788502c03501e0842c2c01804208140008903041150b0b1809032111041c002c00c9480348080440d1544c82107140d0081c690040400101c200440443d00301c0c0561995030b12099280c64144070f0781c3d00c6000c02e0780d845003c240b0514040089040418400c0c495080e120150384c40c8950b500081490011050400c482882901010b035903001c180e42400406400281e006013a5070b546d10301c60b81b4607070340d20301101440d80d4100c00010300e14280799011190380c0403461007100701e1030810000c0010002400d0191501c205a003e0714194a4180511520304885059004100640c076096800c0000e50002e8141d074214002c0b03480301d44904100310000c1120510603680040c040c3d192054040460391200c0d01051210400d2040382c01c1881c03841982c1c13200051101c00c0549140d00403079410024031803456607454501010824030181500b20f240b4007900e070341ca43c06447c896900c00b4812a042c0c4580d000040c0450446610 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 217875755 1250 217874505 217874519
    0xf0d03030e0c03012a050910050c070b04060e040e03091804021c0507060e01020c0a2d2c041e0302070b040f05040e0c0306060d0204020909010b040614040e01 69
    0x7407458200140c0544150400d602c0c00b2a00390340014181700300f00702d418503510110b490480d40c034100d1a40c00c2c0c03400074104010700c0002021800d140e0400c0003048004201889400360034031003213000300607513041103950f141c0d100030203041c11403600500d6200b00c0c070346905550407180210445140110080ca5446260354010030f0085104010703000b60f800c45001016820844003004500b4840d9000d0401844038034940040244038014060720306045400c4401a0312881c3c48040e0041c00307030380b604600821400041007141d41240c4040840d0781e01a80858400140c85030218841030704402e4408030440d1603011110b84041043e01650010052142c0c4c10740e80c0c0652140d491031100051091040e280450b0b960340d40b00800c0c0d00305801203050410000810442444c1500c2103824041821002d01502d01145000a4445000924840c00f0b5041c0301540b008556a81d4101d481d0041e0082002c0d03e2561542d0f0000e043d600280203d1005c91003d80c0003030725281c5000f05903070854114180c48441c4c0c2e070030000 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 217877005 1250 217875755 217875761
    0x1060906140c0102040b190306030210050a1b1112060c0d0b0a1502010c1e021c050706020c030c060f0405031c0e0f1c0c0b0a0b0109051507060501050f0d0303 69
    0xc0703810401d003060244080341a000c1c00180010804000e44070b0b107403140100110708880341d21400ea800d0501c3d12a0801c0180c0b181c000040500c8040e090841e11403001110954402050a00170501c1300b1204481004002c5222480707901c0140640c0e0324500301e03004189065541c5029500210148828424120340c0f000d00d4003d0940b02d000500410011a07a030060b0451202d040c03981c4d0741c0541d44590448600991107610002071510751100c040f00300300d032084069103603c1c24880c65007030300d5403801508980e0fa019008a802040d070100045594003409440c280d1a038101512880042c06401e0124011460984415001d6078201000e5450500552404141c2c503180008040ba03898440742c00c2203066005000b038980940702031000d42000001c6180c1c8170301c0e041043c076104043c003048090880218525001306035100000d11400101d0310707140c0380142e0344100c0c65400075a0104100507800f030340680071406044140d220742410720503030745c07200c00308910501c1804002c0d07000310324030481c00c01181c42070f0 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 217878255 1250 217877005 217877027
    0xe07081209032404020418110f01020c0a03050f07050102121902071d070f08070e0d2303040609050a2d090516020609010501120807080d140105040f0501060906 70
    0x14119142c0d01040c5966804040f090400610b840c810642000705604050291400e81050800f46181c1711442da0741e031115019612030014042c0104c1c45840705140d000700b188842c04080100480d010b15602e16015540b01c0508103041e44c140600f20300060301d9400050400705045100710041c1c14542c0100804458040304000d41c070461140c2840080d211403018201c462401452448140c50301c0c0280024101309550010075040007840c00c10000c0e06580f0816030192403200300c0c0c5442c0c5000d0903040030181d0701100004200c5511841d54107003079525000000303004445850722040c8000341d07540b04110000b4070920030203031142074103000404a0014840d039454143c1e14400c0c82c0d1400f40c0c6641c545012580103d540d021444c10040d0520036140e010400309500c86c807140b00038445507040062500c180c0780c180070005e0000030042103000801142e00c061b2007404102c200300b0000f04502c0310454000c0442032045c03130302491921180303982400e4940070f501d060b18110389522450340e15100048603041e4030300b = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 217879505 1250 217878255 217878259
    0x8030406051e03130302060f010e1504020702060307032007020d0303050c0c0d05041a04050607060e030f0c070f060807020c06090a0506040909060b0603090c060a050d090b0a0e07081209 81
    0x100062070450304880050350040884403003041302c0b2001490064078150014010641c0c143c41840100003805031b00e01216801844408100110f130344290120780a070044c1c52009500c000007208010702c2560507800561204104034403451409010a0380062621940030080d401c41304d440400c8012a00a0300619006800c000d1058a420750420b09141003240c0041800c0c0054400a0200301a0a4010003140900e102c05a100d10341071404002413101e02c118507004148a40f5160b122502c86428010b60b40040e0030a54400d59403c1100b4030b454a968140c003d0104859030258081503d91062407001e1003480650004c114400c150410001650400006603520810b48003000c80c0a84800010f03100a0a80b10404540a0382a10344107007074441c1e11071000e0041c001481000390034500055a2410840e058507029074801d07030b8800403111885092039444c4400d040100900400030020311032881400308030350802040814201640d100d001c01e1080300c3c032a80c42400391980441c080d0009003441303500 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 217880755 1250 217879505 217879537
    0x3050a121103030406050a0501090204060207030f0507170105010e0112030512100b0705010e010606020a031b020f04050405100b0301061505031807060c030207060503070c110d050106150e030105010803040605 91
    0x1c010085156900880b030440764a44c9070340c00d000c6400da43c2c0c06040c0c003400c00147d0a50406080034402581c40e046440041c210060a0b1409403c0c02414440d0002902d06200301d01c004001c588134440c0600400c0c03150031883d402c40400000d89014550150b1003460345590b4051800305505c81800e501900906403280c0cae4032858500050000021008180440c840c2002007052014021130703508507a0142d100e8025034011000d1940065070200c140b032142e02c00c1d103050940d943e60600108044001510720b46030003621301030a01c820300c4000510302c4c0e1210180101440a8240c0360b00303241c01c0c2d0b8114032441d00180d800c034842c049400d002c0ca028541c00080c03911001500d04100785801d141042c903521210100300030203070312420316606100b58005460f40c4e00b402480e6050144c0024461184c0700c0e009000d61320700400034200365440b0280d50040d01d400000a00c0401e4807602c10305c0c1d10445a4103030380f000c25000909000c49044c1805075074104d661542c00340d4201483c204d07091301e181e4008041c85c030140324 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 217882005 1250 217880755 217880777
    0x6160e0f01021002031801060b0c06010b030910020d02094b03030d090b10060801050d080706090305220b070236070f0516080f0706060b120105010903050a12 69
    0x70f075440598443c001c060129619003e40c614000d00712503c0313801035a80c0c2c65082001c0c1444007000508030b4111002c94450319a030380e86001449050950b200540d40e40c0300c0c00002c0102080c00300e60007400707800208460448820139002400030126006c5003000f00107001321031401030003078011141c0016800008060101103003801c03000a0660303200b2014800f010355100c9012041c080660142640600000342c44140c1905100c0041d0852005125180c49281c203e00e0a03800c000d05002599981c0d03034005c00070710424115141c0a403041c1c0007007040101c0c800b41c40e40501c007000c2c1d092040c2011101c0ca1000c05140c400240c00380186188040c002c0c440d80d46041004102c00300d102d0032031144031504510840d4a9040826000b000c400d00950800308000d010b01074100e07000120300c0d501c0c0001c2d510155855035070030742c60100345480c000c80d480a03104600d003070b800151030040300c0006d018058840880d60216a242c1e401581c007120940030141c4180d20103030829001910001c03001f45a01100d003085c1840035 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 217883255 1250 217882005 217882033
    0x3020703120b0607150204060927090c0e160206070e130b0604030506070507110a150c0c090617010c0305070801120507030c03030e030706030e0a030518061303030206160e0f0102 78
    0x302caa620b00d51005d0342d0001c0c081220326032181c0114050b00702c0301f01480b0f58044401c9c40122001001ca040d285403a6208424401c0000555401d00144400030040c0d20510301030304c3c0c80310400032000c0390001502039a030000b032100b4481e5900316a045801414941c0c80801002c10340010820700035541d4101c0020413004c800315108201c2e9030700c00d4040d0f545055a490300e070b2610803041910606400d010b03481c0c0c140281f15010404903d541c0c0c13045549401c2c4c501514600303080c031440c0500e40c815603207649462400308201d80f5a1042010f0000820001e0210621a04c0c08504032403088900c4070020700450018000341207400514242240030750704442e411500c1b910380d201c1c41e880a920480200b042010b60306482c0c00c0900040c4010031480c1810001c0780c08107054641c482402050050402000050f9581c1c0d0a020b20144400c1b0240504025103883d0420042c00b82c00c00c4501040d00507120f010001007540c010184c40c00d00f91040c039600d160081c503840742070012001000b10342906600070b1503035502000b = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 217884505 1250 217883255 217883273
    0x140f0d02040807142b230a020913030801120311010212010e0912030c0903070f17061b0708090d0b04030315090908030c070f140a060c03020703120b0607 67
    0x646100c6000d82499442d03d0100110b0712100d81c64a80282c0e41841000d460700054140c07400d03100244546850b2685c40d45c904401414110703101454001900354614040310700c001010780505100350350929550f22a10003010340e010050074014000740c40c150040c0101d1202c421071110207446400d00541c160907148203a82a030700b00591080308550300701c00400c607211000d9000343d00010540f0103400b42201284281d101d91000500c03203030040744001900c00d0355860810500c03004004125039280e0054645445805020520788071340031a03c900b80200308a4a1842c0018200000010115241021320317034455029810114580e540141042c00003004121758010151269200c0e40d0002122260f68418402110fa590440411145844030500006d8000070449422403800c404054507001180740c41110304c10710f154010002e501d90340e80e84481150004076461141d1045000780300300b0b0705222048080340604400900010719150000b03145980301d521612400d0000f4100510b40180c9440300416 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 217885755 1250 217884505 217884509
    0x206040b03070305191e05060f0607111503012102131802010201151409060d0210020c010207051807030e070807180e0309092805040503031015140f0d0204 68
    0x3194a4608105081c08a1003101d00605d10040c01001001c1c1500c0f00352101c5a03540030783c000300554a2011541544c0c07200482c03041d002000380610342d070352001c3c500360362081803104103a8080c58004480d513080704403075801c1d0781c180c1ea80426441d01c40f80642d550300e01c2040c20a8400da030408001d10b00602c8002c07440c00346000143c05a8507500c01c110312480024215942c00c1001444200382c01424400c0500040310042c2d10783c8220745032406030b00d880740040d41854107820000c0d4001d02c0440039114007a0042440a1250001d0302600c125a0f50f030740c240f019600b58420006035020054000401880c0a030b4010102c4040b00412101000d0300c4a5a1500d008169005104800700e14000045407c040b8000d1221440314040030f181480d00500120340e101c1000b07010303a000c0c4004d80107110a844001c882450482c15140d2080c0700e14101400c04d030340c480e8000c1d80c01802c0742515a0b004581030340f0942503100c20340121703030316050303c6a1583d180d890580c1080b03288155200e41041209842172450001e080 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 217887005 1250 217885755 217885757
    0x70206030103140d02012f21070801080715030905150711070b13060c05010b0d0606031a091f14041208090106060c030302030705130e150d08030406090206040b0307 72
    0x3d09161401d154a8080041c4443d800c6a04200070700e1035001403d0b504c4c150307110081240f0340c0003015191085e4100d00a59100a06020485c01500d041d01202800c0600070075081c4c441030b180d0703600c449030992150340e28055600c41c2d400040c18550400e1203a4001a9001e0003013050b2600800c0c0e0b4003018a82c4941607441100042d50304540f1951008140f01c0d200060403c403802600e8042a203048840204680c0711f05c07802c0c4940303104040103100c404e4100c2c4e8100d1000900300d40c400e91803842c1110040195010588610ba042c00c02c514029aa0700380d13490180688070024034181c2c1c0c16040204031a400492030442c03081c2c40d244011a002c0c050705509d405140b09003400c000000305007200800c1c00b20000c0c82e0b004036030304000b4100042c9400141e4003003c01e8040c5400b40c0e49039943c04080d1070364401c04200381c4d071a0710404c0001540342d940c0329900740140a1112130307919038109841046481000003a024108d800c0410205000401075448124964806015903041590710a43d0640395041107034408 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 217888255 1250 217887005 217887023
    0x22e03061a13030210170a0504031b050714120106030b0f06090408040303050a0504050603070314011202010806130905100b0f1c060f02090604030602190816030908070206030103 78
    0x803050104186180c0d000060040d990750078000c034845409910340003444064002c0c1d90342801e5042c0140300e002c61020080308142e0040240c1021103840c0010700341190194001402c0800a08001042000d101061900400201141c904101980030500e410514665000c4480343c0101c0740f442080c015200114010180c40c0054a829802805080b0008101d1449405403000b0400080c55140c01e075000d4a4061509580364042c1300016101807007550882039010f03c01004000840350b040d04040650507100d4420002641e0315455401180920580240465070100014109091a141955690000e0311000c00e11070041d032a8241000c14011034175041c00d4035000e01000900785003a1103101c812081d01ca245200c0309201104200b5034a02c54018100354442012102400c099016036600d40c10080485565a07503914100d00254840704c0c8900800031090344a0001c0d0740208071840c03055658809a034a129071728541100146501079086400d80b00501c0390f43c026803160000745020714405c0c2d9003c = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 217889505 1250 217888255 217888259
    0xe030a39060b0904050a03050901180b1c0b03120906160b010905070e130f090b0718080d20190b040201030e0f0c010e06300c07080403022e0306 63
    0x30301c058840318841280100001d40a01000940004039480820707018900309455031581b8004a585090380c0c8190705002880c040d02164612030302c00104044610030f01001d021140d00007446c020f942c907425015502d5084001914501103019008004440b00100844c0c0b9141420407042a40e20601d003041e01d50054031001803064078124400c46d40c00003014288040c8105a18000480c42440504002d90880e280c00e404054211147c10201031241e0001c800340c502d140003071004201c800c00d030100001d20104200006940000030840890300c0c2082d588603003860840ea6012411082c84480407440c620550300314404410355200043c4960744140c5409840b800d0500005090740d2000c02e148050350410100301951160000e000d002d003410a080c038000020309a00016503500420140038160420042c3d2503030703010250301d82040c800c003007003455a516071203024989400e030041500052006408000a1001d89403031504400c150141540780d120b01c0c480035031036101c13580c0300c40c0c1c06801082d121002 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 217890755 1250 217889505 217889513
    0x120705070e16050706090f0302030a0f1e050a11100f0b060315120708010e01060e070c260405040e060103030201060b0c0a080f090a060c11040e030a39 66
    0x2600080c680c5603180009401c0070005500002e40e002a00c0c4144580012500100300c0c49801c803250325a04000c42507440c5e411400d010751254483d6241c0c00001d10101c00c0048844e01030002c44440b0307080d4001c5001c51100b00c8106448581c0b0032070000d070501200b50025034580364100007488014074414800f16001c42c428030008107861645030b040740705182c2802080340031211101e001d800da04e0100c800d03011041e41101d041e41414059042211203508101d0b00800000d8150824821580100d560120982c8c0341c6c9030840f010815480c0080c01c030100f00311590040f480c26140c01c0240c0141800e11464944d580c03002a08031500110040e141c3e030801c60042041c15020711580009201017039a03e8600b4403401442c41c0c440c040d0420050103000003103240e580300c03086a0207076040c02c88081d144030b4030545c5034107020380549002d000c2103c00d075444140c0c044240c145030141c107060015105c0110b0030141024800d0b20780f030307911000e41d00c034102281007108588559485580004200207490403103441540c28 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 217892005 1250 217890755 217890763
    0x714010c020316050310140a0b0a090f02130906060c0311070b0301060c03020c22200f1819050405040203150703061e030308060d030c08030a020c060901050103050c0d030908120705 79
    0xc010b40c845c0d1607c001c03007841001006c0d850750300c60300600c40045e010101000207143c0e041d5070b420031016246400304e001d07050102c41c0d00400b2200d05030040751201c666901c902c0d1040d01c05a0194000003140f1084403c000390003109614507082090040d00c08840d111150201640c009a104000086100e03083c5001c2c0360b01031200600100f010f03a03080501070640d012103800da620314031034071280e940e680e01c1d03a20a8440450041030860340c1000744940c0c883c4c0d064000701c1d5540214500d40d40e40810250380e40c0040c5401d91240300303d003500d03e4002c01c0c150b180004000040030f0040083e81c042c01200510004030101001041c8603020301d45000030180d04043d02c0000d0072042c8040d82154030405101840480e8102c203035076500c080c089945800c0d50055140031906100b29020092080c1c10210a0110a202e140c02500722050b25408403812a6a8920801e00380c0e0020320002e811500503541c14906428480308004995002e401c121030026550704c441481c1c078030340d010480c0b000c43c00802c04d1410404240 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 217893255 1250 217892005 217892023
    0x30f08040b0a2001050108070b0c070f031407080a0b0c0c010b13051621050907080115050f06070b0624040801050601020708030f0d200a0201090209010f080714010c0203160503 77
    0x143c02082207604254609540d0364150140c2110703082c02007001640d4102c00c000400207000b102c091107846030740d00e18010304100c94103514840e00b409000000b00e4a00400034a40f0140c54000c520400c2507100e9444050140d03000c045c0d010304030354032003100d611552106614031000200780c203c0090f05180c490301448002034006082d40c104120b50010350700d0780d007c0002d550915601c030070300010107480345a000f40c50320190368480c00c255401c20f40c0c0c2444070404407a855041302c80c1900c04001c09040401001701502c0351613030051000f104c0b44089025030518402d180c9041c10300c4c0324070f400c601040c0801100140c00c50340c0034078016074450702000001c2d64180550070040001600860815104011200d00743c00382001220070542d0300c80101c0c1d0402d02243c9403940c5800848035440c1c0c2c2d9104a2030080c0079050200b416802028181c000240200c15070f0040301c00c844851019100305424041c0404c0d101c41112011410040d002d060703200540d606000b80c008694032032103220b00103445d01042c035003000945 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 217894505 1250 217893255 217893317
    0xd0204090f0b0a0e0a0818030d030207050111090303120c0405040e0606040b0102010b03101104120803070807020309130b060c030412030f080609060d03020703050607030902041a0307030f08040b0a 86
    0x300a0b00c484c104000200341e01d1080e84942c0994650b00b0b210f0840d048004443c030345903407500c00c1c8590649001e40640c02401d90500400007408185070307881c0c106803184500b04260b40c05030700402031600d0041c03021000940124442c42210b11305503640c40050300f0707a0052084030409030010f20903c56035181511032000085002e0000780052100c0c0c0001a848464009a481046444481c0c071034803010007004650160610010010910a86042c14000c503041254020003041640c804584400e0002064501607031000b40300512021110076880007130a40c840a154004106210459103e0070034005440079103c0c029586485c404e15083c000c00041c1901c50040602071040c050104580300d1031f220560054059603003040034202071404030f00d410b1550340060308034003400050000c010340c96005492814001c80301130049080011101c2181e12060002da0f9050344011010030026070707001c0440b50640d02030722071142000c0d035a8000340320700d902c00110940000d400340d49001540e000d108854180c0c1401e = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 217895755 1250 217894505 217894511
    0x1060f0b03040f0812040c0e060f030706120603020a0602010902010801140612190903020c011124090304080f06040c0b070209061309200405090d05030c07020d0204090f0b0a 76
    0x2400d40552940d20020700060140346801c02202e00303004292007150b80340c0700280c50324841c03032825080610404089000f000c07011000c00b070208599140140401011000040142c542e5528211081d90490a455400a0b10944400d0004050382e00c2078201c02c0101007036000890065030700d1000501402c1c1c140c02513080c080c4012500765032915444182c8030482182c0300d140d51141c541d54041c14884008103000d190081c201980c1c00100755005c84d001020844c2a21031402001c04080c0c001d8580303641c1c903208100356403002c4a089400c180074140c10341241403441680d10b040d80b100c1c0e040d0b00b09200340018110a5009805000400840503074820050500e11801d60400e1243e600243e000031016000f284101d43d43d0260906001059102d450501c0d4450a13180044a40c0c1584100c2240504d144a01c50f40c0f41500065228102061a03504075943c2e5440030f00c0c540c4d4807205118660402c00c016604903403140b07101c00058485100b80345d551b60290a0060140869261400304008028062030301142 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 217897005 1250 217895755 217895759
    0x608130c0501140f030411040606211d0d030501060206130308040f17040603051e040309060c0303150602030c0f190b060303070512030a05060a0f060503280e01060f 72
    0x69040d55520555100b441c00030380f401c00c0048100c59900800c1c00c0c01500ca04008180820000aa03040040380b000030ba9042c8002c41e900e40c0300361040e041000c8140c10088030443c5036041402d5581c0304009200810080c1004000080041c0c0c0c5014110201d01c804a0341c0c400045c410917404100c0994840740501c00c8a9202089503001800128041c100170b0070381d60741c44508000c02c013034602036050078200c1e0520503448950300d071401000740400341c071000c0c0c40400f01c900100403056645940c51046405032646c050140c03500304d0498007200303800c4003601010760b644421001d110b0712145001c001e09043c0d00464403130310600034403810306044403c00342550f8040070084081c01d410ba003c03074480a8110204040940d07031000031a003541700d03601c0018900d02035074189102a070036080246015190703410003000b01d03556240070722125021600030621070322003030300c02000198411001107070b100001480494800044208002c0c03803854a208100c0159210740c2601c1c0d111000f40308100040000000c1c52031058 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 217898255 1250 217897005 217897013
    0x801110d1506140903010603021e040f0b0315180a03030c0f0206010f0504020c0a05060c031801140f07020109140c010f080c22030b010f031e021e0a05060c07060813 72
    0x4100c0e000ca4001c083c0c0442c080d501d0b941c2c203501880095030042c0940f07026035040040e020201c01c40d9400244038600c0c0040100c5450700034880c0d80754402000d03004245143c2d0344850318062010007003013100c02000958283e1300074030090090140301442510003213100030714030078003502c6221307204142004c541c004001044041140c0350385d130701160310030307100140e0756061200d00f682040f07070a1030040d0042c800c2c0410b00411142c2d8100441c42882c45089a01302c8078414042d49007640c1180c80c50743c0500707a070720000c110300806030070344950070005c140000541100c4a54174802c458002c1015032616030000b8400f0000c0f540c015031980181c90407490b10300250315044988c000c0d1409007441c032240c4039012075a60011034800e40d00381401f841d0080e14108042d030b55200040004465404122005000714090502c20080304405c403150580c01072511401d861402c0d003060401506203d601e600c008070050000c0d2a803100300040c40c1c0d444141c4090030b43d20b03082c004007500750701c0c0c081c011908580021103040c000c1 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 217899505 1250 217898255 217898267
    0xc070e0108011406040b030307020a0b0d0b150403030f050c0105090c1c020a1e0b180406060c0b0a050613020c0c030d0809030a0c08040905010603150605030c041a040801110d1506 78
    0x1341040300c000404000308400b02e4617500840a009400081c80d50004c6000c6204101600300e1020300710040c8003000006080c0140040c80500b500d8841000780b2003480080d01880f00407030540028a007850402e8035201486003074440550303080c070b80794000c1c807204c1c207580c01c108001e00b215100d44900842c80680035408203139004043d200b05542900e0301c0001c1c0544600c01540d94000f04003030402d15441c1d02c2d000a00c103260713030000b00a25105514100d4000380c481c0c06160111109138000780070061907925441000050031004000c50345c001215006420380301a00d00c05400482c81920044c0a4070686005040c42c08821185000034010705c0700400401c0040041143c1500c9103520b444584e103d6603240241250040b90026200f01c2d00303000010940c598180d200c4a00c80c3c0d02c030360300a103032542d0740c10050b240d40c0b00540c1e05802c1002c04220620004020700c0e91036086103036548801c0d1400d9502e60b84a0308440d540b07005036580d00c0001698a550f400a400740895414188400710645441c181014101e = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 217900755 1250 217899505 217899511
    0x80a11070b0c090904050d08010f0b030c1806040909020126040f0f1a0601030507030b0a050f060c03030a0615050406051603020f06012903010f05040e10020c070e01080114 75
    0x107240c403003000044800109070180c40110001600100e07403828540381c00303a04c400f401c110040020340c3c0b640001800c2d000301480d44084446503e0b0070f600e581c80740f500504441c0d01000c0d1550640130003020703101c02c80d00c82800510040402c00340005030350380300d44001014101c040130190f18040d0380c894001c920244011a658015500c010320301c11500c05454100c5009056981c05000800300c82440c002242c1e00502181c400c80b0300741c0e401c04c01035540da801901120f00f0400d0403500700e0341202c4288000d007400009200340000041a5030b0a00341124002c500e5503204803800300900b0b0b00c6140400ca814124054030080058038140a41842d05101c0024a60702842254001280e41021040c00b414028044a9481150002500d00750342c3c440c00395841300b4242a0b0320902100840c010000c0800220741924180c80365200040c0b450361400b010800540b0345a100c520b840e0041c00c1140dc4180c2243c070042450484003405040c406103030a002e03c003010030503440a1016410506640304968035101c825038 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 217902005 1250 217900755 217900763
    0x30c0a0b0901200f48040f0f020a0e01021f050a1103070804150e03030f0403030e0307030e0109060305040201080f0709050d05070911120a020f070c1203080a1107 71
    0x280507039260300f03440c41c482c2032603149845000f8105554483d101c04104903100c5448142c051040c07130440c0325000890008503440f0000c00304404003400904900380ba540c0361000006001141030a00300400703100702e40c4614040812150700040e64111150004282d089004090002e040c21152041190798099010300040f016141c2d141d0002c0d00d100095440304141641032a1444e8980c80e00400140c280d41c0d081d0b500341d4101c050360b03140d200208002e0003a0541100741001841c15521030036103240d41c500014208600781a00e91481800382d61082000e403020a0203640d4401b11925441d001401c030300350036085603040500700820440541d03080740c0010340040003001c140a40b60740d003036001c035004202c03070b013080368000b5500c0303031402c1400030001d0b105050380d41e410030030020244004415850b034403804120401c80c40c3c590340007410182c0309502800e0541607140c01c50b0314040650741c4101001109400c180201040915070406241c1d001f040a507100b010400c0400c80041c881c1101c840900651034020 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 217903255 1250 217902005 217902017
    0x20c190c060207031511070c0803120f070f050304050c1909050c03010b04120f02040f06030203060a0504020102190515010f080606031b060a0201060b070c0e13030525020907080105030c0a0b0901 85
    0x400100e141071b0859504036000380a111500e600c0740e42103070711384e482044805c4085030800086460412900d480c0c2c0e003d480542c40b141503400c4034440c1034445e0341000300203581c1ca020382101c0bc24680c880b56488060000400007603000642007829a008455003d0501c01c101002440184104080101201c09883c0e164030f0455400440d1302d0302445142c10040000c0d013182c1801021119131030940c1068040c2e038422070955226030b4030b0700c0407441210400c507000703401a407002050800c00410910100402d03409030007a43d80281801c1580c03100c0342d8017179016094125100340100a080c600340320503030300183c2c224040c02c031a20003141d40e80759240480d940e00d4850707440090344840e0f6500035407004004002c00c58646881e0303240781c2000b26441900d480b03a200900880000a0710f0318004400b0b03000715a07450b0316807904007002000401d44802c00071040080a808060256016075124100c840c403e2529542c6d1100070745c1007505141c2801300104840c0c1c01281e1f10002802128081710640c2e01c018020310f808 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 217904505 1250 217903255 217903271
    0x21c0207050613150e0f010c050c0c0405040c0312020a0204051302030a080d02091306060206090304060503150109050904060902011d06030a0b010e0616030e06030405030d0b04020c190c0602070315 86
    0xb4044d180300074184c4c40c01c054903004500d040c1d6200441c2061442c441103008009004c42aa0280c0d180c3c8200c00c40c01c00700e50040100d090007840c081d441140c00a00540c0c000800c40d881c2d5640082e0307030103042e81c100090390024010201318909801015881442c01503c021201c1055020075070310021f81000400704070011607494940401d5a0640c5e9035000d008044101c010080325041000300410301034a80180941000101074500c000212411550341e0380d59a85595620710543d030142070344004190410480345800207a80e5140303518540203c4c000c50300065560410310002d2300c19164030000824000542105641d182d4401c0c0c196684140c901d100400c8200320940120340c0d44001c1e0003210b61014010a0b0030f03030ee0645542140500034880c1c3c072070502e604041001c003d19400200c40042c0350354410420f0300041687c681003850606030141025003010300d840d00c100d00b001560641c0440e12100c175008941403142c0010030704004c3c402b0b0f0024040840c00d54a130250b01403203280381541100e0715901c0c1 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 217905755 1250 217904505 217904513
    0x203090f030f0d0c051e0a030c060609020706140f07140304060603080f070302060601031e0b042a170717040804050411030624160201050903010609021c0207050613 72
    0x8030000e81140a03060f00c0141c2000075024107142e02d0b02d40305403507501c100440190100310302d08903024814940001800c1c515156034084480004881e02250080c1d11140e0000301440a0700151249034812203011a0324002c000003001c00c400300509610201103030400f4490b0b1213420400d800e42c10351601082c0b554a680b2420014082d001e81d501c000c1c4100c03000140486181e02d80c4014205e041d2207642611a291150001103040d40c01400244160b0100d58503c24085200750b400b10b01c40d8031000d0008683d0052114280341c008041c80300c1010415040c84c10454141d03804040e180c241840304c01c0b003006509003200000c1002001105034110021094042414800008140d80041c1001071040c0459245600510f00c95001610003d02070703003901c04200328821000d20fa43c9503505400940604200e803180103803888418848059060207410858103003183c40a0103100050030141c2400340e82c92000402c44000c2e600030703140a6443e24030500a0a00240020a1140d0420301d803020310721440f811820 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 217907005 1250 217905755 217905763
    0x405060d02090a0806070207060e030c06030a140c090307050d0b04020d050709020c100c0512040305091c32070612140a0c11070f0504020c03070507060302070c12030203090f03 77
    0x280581d1025070f1040003d0b03281e4000500038440d00360740e400d41e001c0565812042d54000748501c109039142c0c1003900034201504088000c2c65101c18141700101b645404070454020019080e1100000c400000600c0c1085090810003000280025900402c0c490b4054456402d520030140000f8030030f80d1441d01031070600004022800103840710310411903517000c000802c10384e50981031034091612428194490103507801642603d50001c405088880190741c1c56404660790b601030000c2c20350096841000c00b0b41d4680800264004a11580d04941c507400c1c00180b6030340309181c40426559020180b881e0035030a80002c074411040314014204403081c40700007600c00c1d000e803665035000b41c0100404810402130302c1c810307000502e00c410f050b2940c20408403507a81003034891070b550040b5181004001802c11050030305e44d000b01403100702481034a05156183d40ca45040115980c40040000e0b000b141d0724003804260114a40203000441d01103000000b070360f40c0039499028902c0c0e054454102c5406d41c20041d18248 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 217908255 1250 217907005 217907017
    0x90405070207150f0c110607170715090809010e0114040b040801050c04082e090605070305010b0f04030b130b041406010f05101209121d04020c06061314160318080405060d02 76
    0x800e01d41c644000c090440442b40c0002c5e03002d440c860001c0b04c481c50250003e101e00c0300015000300d001c44ca0700700b0b001e00650b1100c246200c604d04000c41051540205908540075102801204080d242c0e21403500e12a1820750741d02501d0701c50700c100c0c00c100c00c0041902c001040c60100d400c044070030342005038048200d210070884800703140d0740d0b80c1051030000c10845031740d002c54820842a20100456601d44c0d00000042c05440f5410503030b03090801c0b091002c100740c1040b00d41e2100c100d000e00c2031400040e654400012a043d07d00b1038010140e4400f104002ca4180001409000d60b8511401e0f150b141000080100070503400c144203004603800d03448011107094200c00b030745541080843c420101c00c04401040880e18485c003210745e86c60b8002034211761400b0f008550030080510024002074480d81300300103441034a1040003290560310400700031001c0c080e007040d5101356100d140d282d080c1680c01c1406000e07180b8060069114403c03035241e100000740481c0c113945c19200e084d1030312601c0b072500b0341c1c000009200380 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 217909505 1250 217908255 217908263
    0x618010e010504120f08040206030117070b0c0a1709150c100e030c10021201050913050a0b04021003020c15060a0b130501170c090114090405070207150f0c110607 71
    0x20108030a0040c5242c5101340d2a4450b580d00b0b80c441d144a5044903d504141c900035800350702000100300c0c40100c0000ea10301045143d041d101c19643e581900311240d80903000c0c3c0082c0790404504e403810b2240c0048084aa8190b060303060b03140001e1540010004003050021034101507012414400d030030400c0106100408004504000f40c80c00401007039941d40294000c40e42900ca001c401c90075098890003036580b803186034030104420340d081504100756002c0c0100200c908100ca0b00c5c80c4804100200007254109008106009050401d4011310480540e814401c03002d0500400044220030000181407490280c42080d20340b5545403140014820700d02a0f101800d80c031804500b00c9109911284810102d900989689040c1191540440700d220422241412400000d1000000c1135004184050000f002c0e100c5e064601000c1c10009011908190f032004c0c01070b8080407050041c4101f803140d640c00e261080c14003c02c4844038600c014401c1084d4200240070409a002c050901d46070f80c0182e0794040d0744 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 217910755 1250 217909505 217909511
    0x20a1d07030207060605310c020a080c010b0d080c07050d030f0c030210090302100b0d0f030e0d02040207050d030b0603100b0c0f2a010504060e0405040f12111b01020618010e01 77
    0x1f03100c20000da035810105095902000e00c3c100c00800c200c8030701c14080c594440340c02070900c03101a9100c065032070b00280d07503c45195403600304800d000d0b580d1008214440b40b04504840d00d840100e21038514142203034100b0760040429001d104041790700304000c2040f2009070300c1c180010010b10701c1c0880c00c0c040c02500074400030741001e00c0d090800d40c01188150184401c0c45003082055902010403008061840b00039007244041c664000100380710303009542c440036002d84a6508003004c1d0380454201d0b4004c0c1c40a482c0da0308448110f46600343c0c50f004034000700c02c0841c0c4050541c00c0c80360001301d100006102e1007029071000034080d078208000f030000440c0d0040d1101a901184484900591107101d01c21ba40c00302100c91145400c503035806203054800b6111a0307580d0540d032802200500c0001d0402610a46030064180d4001c80083d059860000e02010385607288040342c0949524180f400358562420303030005a1400020280b42d82c0094840d0b8000e50295001044403101d0000c81d0060000404071445542 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 217912005 1250 217910755 217910779
    0xa0525020301110705011109090c0309280b0703060e010b070201260103140106030c05091e070905120a0f0f03050c0a050c100201020307080403030f02091c020a1d07030207060605 78
    0x40e2840c058262140175100a01c0031201e00d0402001a00c11040361aa101000300046040004240c01655004d10703d03100300c8100c482100d00d400d240605040802107000741e031300c1c010700c1007201c10070249800013858101400910304020201d85000b805020700f011b081c201081007004c0d680702d903819a9295010141c8281c0e00903080c03404072510700d424001918400004283d0740d001c140144034000489402c008150120303070800c820020740400180204040c2954503120004240410546c14040c2210b80c84250010740b400301405040710424010034180e410152a11000c6004541ca0084031a48005244001040703858156a035002c0d01f03000c1c2ca0188518492401000320000305008190401c0700c0c52007511205010881c00d0f440304881d20700c000303040e070320206000a0290304500c030001107a010140c04c0080500114034807001c10800603866040b120402c1c410350901030391000141280b601c0c1d000d8010784101c1e0761240f000340030f4120020198001401c0d82480702c01d60200c0094072004061145c404 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 217913255 1250 217912005 217912031
    0x1a0d051b1804150b031902041e1401080c0d020114072103050603150105031509030d1e18020d03120f020409050403030507111218030601060909060801020a0525020301 73
    0x4110040302800c010314214404ca41c0d0324001801c00401115481e0509084541c5c2d42800013a044000c000741481580085404c0c040c10140164106281009d410b444158900a4000d00e05541800140d014100c60b001100250744d201d410000d82c1c0d004191080c0c5d407075070f20307151402050b01c001d0035401259070782082091803070358503800450058404504481600f0100092050710745400e00c0350301d5140d809910b9540e1144071100860f0383c08480c01c0705680c18506500c0106087d551103004807280006954001d10b07140b005072003544a822002000011f15644960225120b000d5400700070f42841413121818a00c0450b40d040500b01c1e0200a80c2036450703c0c4d9032a0080054102501c00303d0101c0e04100c0040c00162140c0d50300c40700010040024240302c41c112890501a500189086600f040c0c02c440c0442c0356207040014900900c9203580b920030383c42c900601c0c9801c4a03036581141546900402800d52010f03030100a40762024000b500b41c40082e07440c0c1e0402c2d15641992a4000d41550900d07510721009 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 217914505 1250 217913255 217913273
    0x2805060703020a05120f09090601030e0102160213050405071701020d06060e09130201020d050f0c0106030c0e0c03070504030809060c07030b0105040608060c0a0f0c14011a0d051b1804 80
    0xb03e03c582c0480d0100001140d0140310b9020f1624458491b480900801c0030300c0c601a8401d076004041810009a2241054103803800d83e440b13850300b4a00d00044280003011030900d2110b000d40004519000c00141c00c1541e251901d500880c4195410014200c8042d040c40300c003903045a0003040129010800140e036040090156809030490902c41d40100d000900c0c0000c01c1c441c0c81e00450f0b4144e020340f1000c1a03a075000d0340e0f540c04c450307071a00390044c080c0001a40b580003407107200050342c000d1480c000f0071890201c101941c03004c000c000300c4000d001841480003103070b00704e41641c06072940190190780f604608408150180035030219114603109040c400000c1c071840144050680c2c400391014403265031034900c0b00d0741e9001c064400e1a41e9034010042d0181c07480c410a910718000c17150b031802c0e5904071410707140e110b111418012840c1890f552402240c0f207041580c2109032604500b50303448400c40d00705449064854504410601e031850f034043c1e410280d5604e04540e041c80c0c03001c024407540c046c00c05c0d040100403 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 217915755 1250 217914505 217914523
    0xd0603120f02031305100306030506010e0103020906010516030c170d1e0905210f0406080a0c030e0d030c02070b07030905040e0c0a21210e090105280506070302 70
    0x410200711410001902c0072003107070b03042d900e400d40c03201e01145030100f4004400740c0b43c2400c800300341c0d4030903012000500522000b0300a0800c0342e400345440d41140100b010320100544107034140703c006c01403a5803008404003803860b015050305000b80005174500303003240d00c10901d24094518800000e10b038481028207910506098000344094410300304100c0c1c13030303104a4001c1c0c0c902800311703807244085010b0181070b00c0c03803088482c00341c250303030713410134481c250201d045030030a40020002c20208802c01940601e03038070800306901c0d41450140710080d0010704d041d0300e844800c520001010340380e1f80104440c40c020040c0b040100150702e6440c0d40d070012803c00502c0b2450b03d0048500c0742d4108140b03481310b100e0004d2960002ca600411881c140d1785499a0100c1a100110740031901584100c5c004001c11180d05099090481e40c840806c0380b08010000140041180910140303d44074140051000c0d48817076032403040000b03a044c001554858a0303030f2071800c4051035a100342d40c04400040c0f06005c05901245002e5 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 217917005 1250 217915755 217915757
    0x1c03020d080606030910020304170301030f060e0d0507060c0215070906021510060c050c060f0c010506010c0305030a230408121617060d06090605160e0618060d060312 73
    0x60b103400c2d082020910090f22a03c80991082c01445000001c5500858000740715140700036110f54000c9004140b42c00903402503030031060340c91400c014450707030b406450061001c6802400c15040c12901c0503055005070040a00125643c9920380c030a903000b04031000d101c88414084201c40d10b0410801000b0706110b0107003c00601070004030880d04445407059502803141c03400780118040c02c01c9400ca030070004202060f6258400c40942c5001d0b6180c3c40024407204030704201d2956140c072060b0445003501c80180580d81082013810400001c250f00070142c2c0d400c201c850801040300395085008030440480401c05c1413202c102c0c20148000c102840009140e00e017030111a8501d6907a8800303240d8a0181c0705010310f4089890700d5000740c0c0c0c1c030403e42c3d88558009001131486801403100d80310081242c0902500b150941d0350382c424011741c42c042d12505606080c4500d8070420101e91000401c0141c0500c1d031101880075103603c0c9030406503540505580100d444a2010030200c1e41e00e0030180040c01ca10f036203800c = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 217918255 1250 217917005 217917017
    0x801061401081605030c12070905040b090712050912040b070515090703080307030e0604060603031e0c0605041e0b04260304030807050c0d020c040b06030112080304021c03020d 77
    0x186194000e0300315a1052a0f1003000b4450f44031044001d0340c4550000300340800c1c94008101d0081483c10320302803117029100c1555110302041c10308007840121943c0e088614811684a420806025070001c0c0d020a6034140301b5021459880e4121024680030001d29441c160a41c0828046030340c5200300701410f1098018812100b4410040d04003800f40c0380f09461a161b0358000100a101040040004542007440c615002030040b105000c0a0b08003003086d21f04460306600d454040050507402500ea807460110401544880b203200a00503080042c0504002c0c00251141c0024090028088445401e1103503851500740c400034516061009010880d01111490280031710781c0740a0344c00e200e06e9010750800c01c000a207152182d407003d4070b49220003071440040210411007012414000d010350321201c022500108407046800b03080000b030b211880b81703160051006000401c07240e074500480200250300140180d030b903a1980d00124010350b000e030302410204040940c602003095400035000001c1486a0740e00 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 217919505 1250 217918255 217918289
    0x1020915040807030f08070b040302030715020306240706020a0810060206012d1a120105060309070302060a090f0f031e08031f0312030e06250c0f020a080106 69
    0x1110386001d00e0040c02d80d80d61041006000250f424011504514000c0300c00c182841c910340c0d40c0b807180342802c80c1c04178010b1304081000e07420003080021330401058058015415898050301145804011003022b40311070001c85040300c0c991070b001080301c072215001081999a82d2039070002408500d030a40d220070034101c2e20107002601078804030710b16060b01d400e9080a103504030b04225030034020880109500100d0200ca02c0000c2c10149004074450303e42500951980386d020340300164030041e01c1607000e90b00a075004c0007085062240460b0b420240c0341c0c101d8403c3e44800c501d490880c2c01070440e1700980c1c1c080d5481072010415126600e4420200c03485090744090403043d49401030301003030224000804110742031003c0b40c2000075807120800400800a81180403540e2510b03082d0310010002007140110b0b0707550142d012840d03014000541d11600092580401603100340c10804800c150f281d09408200000c0700c40001c108102c0750508507190010024804291620300c0b2034000e003540d21801000744c40040384 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 217920755 1250 217919505 217919539
    0xd020406091113080d091419090e010f090c0326160210050a08010905191104080609070608010303050d020c010e100605010311090d02190311152b0e07030302010209 72
    0x4100c078496035500c5000385441c02d000d8005140111907c941d20482180301500c40d404400c00c0e0304010071107540d010801c5c210081c0e449003154012200d60103000c0c01c0903088004242d12001c4141101d40c0908840320065030301071040b03080400c060b10302d2003107040080c000e50403c6a45240c4010140200ca0aa00c0780900d440282d60703030b106609600f00815594401004104150742c48560b220100002c0d8812440181900740116210030852080092001c40e081c85405010440f0385c0c0d00c04d240030000c04070282000c03000740c6074000c140f000404204001840201c0c0f44442d80544629001800080c4402d2074007091840d2220030b00c464030709603189401e000160395031290055154240101070b15925107105002400300c00c0e6049030301a0307040125007070007103880c40c110001040154004c4d00c20034041c961070420401d0941d5802404036030294203000c042d03401950307410747c1c8110351442803060201440c80c08803813024001d10708000b9518000c0101c00000d054041d001000841411902c140408071801c0d4 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 217922005 1250 217920755 217920763
    0x30c051c0f06080109030504030b0601020d08041e08070b15011b0303091115030702070e0705090405040510051e01051206190b0301062d140d02040609111308 69
    0xd9400308205054000c084030800c40c0e8040241c80103040004511151203060a40c00d42d2034001d01100000d40004040083c803c00c1480c642d00030100740b000d04581c000d125001080c1280242014043c000d500f1001c00c0d052039020003841400b9070040d4219203a500506020300d40f0304085542041c8803080c12110a40c641c820302c2c641020500c2031188911001544e00c08400402450070202c9605103c0700300c06089640d03040d012800d10000710031840e901c2c64000002414074041e41d20031001c4403116014030900c940c0020072b4860303068050b14000f807140d481f4144107160100307a5881c880703498504424894542880610040168080d41c074002c07803a44c0c2c4600340800b1481e1403030a0400c580218000c81c000c03030991101d40c20360708400324000c01c04070903000000c1e085800c075501c0020420010085502001400041c0d0a23508940c50080c140d003030315207031140584030443d00300140300c1c01d08442000e046582c2c1c1d52240010700404c40701085400c25502607144107502c14407000c80961103000b00010f50042c005 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 217923255 1250 217922005 217922017
    0x5070e0403350a020d1a01021e011e1508010903051c1d0309010e1203031b0d0c0e041a09041106070b0f0708060d030e010c030c02220501050d020a0302090606040e0702070501030c05 79
    0xc1d008000003a0000c18110709c503200560414000c0d502c0d070a4503400080680c8040d000c00302d4850000580822072020728070810790301c0d03000d4007450341001040e40200388c02c20199034800030b9445168010405040900d4000c01180c1e46400f15509580d0580042c2000000034001e030b100c00b80c84a03900c55401204008606050300c42c141429441000081c2c04a5428054200e0302070010703586074245202004180e060303030226480100001e100d1080404070b4a458055000c207aa11803c00d181c50303880d000040780c28410010006801c1210001203a0800e40b40d15007200c04581d004410401241010300307124081900644004c000141200c1c080fa18601c1d21a4a41c2c20455054660201203100c450054030002d50101d815800d101125640d1009a1185010504440100c084444848501d08192b004071201a00143d008541c1c0c00000702c01a1942400c2c8001d480e01140c10003026507422000507030510480d0050036a22954009203d0700c41d40000d0f070401602ca00f40c9040c0700c00c1555003005c9640d0b011301 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 217924505 1250 217923255 217923257
    0xc0a03020d141204120501060923061c0b06120c010804110316150f09080d05030606070515040311010902010f120f020f0705070e0403350a020d1a01 65
    0x803618030300c000b03904181100c425041da08243c4500040464083d5025042a4003201e001039442211008019085c81241c001e03020703ca07820080030b007200795030900321005000d01900d00700b000c101056507560360384142c0410350103072014031611304079074500b4000b030400940e141c0d4042e4046210440e21002c002c9000841d00d0fa06940d001c6095a81d034803411120000f10454a4244c010940d02200038440d002d080303806071101034082c1d10390100c9003000504034070454001004004c110b1400b809107543c00310b074601d001d4101c7d2a2142e120b1f1248800500790707120b0000020070512803921107012500641607010320ac0c4d4020386410340c02c01621002142a140d040e14002e000a2010326482c4055014a1000611548a08001031201c201d0b022100c101e901c2146012410440030845000f080700400c0b00c8030280c01c07050241d10301414165009010b0007621148100507010030903080c142400c80c80703030030400035480849540c0c0a04000c14040001d6004c002803150081c1000c040c8001b4001c2143c8101d00c0c4801 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 217925755 1250 217924505 217924519
    0x10050a021b18070509040c03020307110c060301090e100213080d230a200f0c04150b03040305070c0608070305010e04151d12030a0e1906021b0a060e0c0a0302 69
    0x100d80d01c0b00e502c2e01c4028241401c0c01410b000040c0943c540344203800403202035450069403424000000340966000380340c0000e007075002c80041419500c901b02a24110b0700043c00c04119401e180c07000e42d040082060102d01c14a1011400034124407085803040304503445801600c0b0380340020881202c558001c4005407290004880e40001c8a0221500030078a00c002c0c0d2074882c5005051044280c803501043c9100318881d440815450300600342440200d40108007164100809c580702d1913030004480e05407148000607031011001500781400f81c03003111005580100020300040e1101e20140c4005400d58903036000a180100120382c1980e02c51040c1e010310b4004c01140c003900b4140036820052f00300084040c04607e4140a03004010004100030603000014050305900c03071404202d9482160800380c00c50b9100e5000d81140c02c403902d10030b01040c0696410504c0941d0320240c03400e03000700c0a075901882c0300c020b201c0d0710752010502600e40d01c14086c0302c080000760780500e12500700f0001000e00f00d01010f540603036 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 217927005 1250 217925755 217925779
    0xd02130e0f01050417030c04051e0d06060806070e09061905060d0f060504061805270309040e06041a07140406110d2c030a0203060412110d08060d060b10050a021b 71
    0x500201c00402d410b015180e213017000c1c0c0d44080864904118030504540c003a8440dc42800481404e100f0300f071340001d103071130300c03c2c440714104000070000000640380600910406070f9091000d03095030290b8015080c017502c10380e80c0700503110301000100301c00880c82403c1850700c1000301d0585483d020704000c030741044c061501003d001c200301c10010103001d0580d800301c0c1142174100100c0414601c40c1c51141000c10041c0d80c0728004101808141e484110721048280c01c41741c10400001d12107200ca1041c51006c0c0c0d80280143d0b1036203420798160100e000383d1141d00c04045000554142e00c410340606a061080594542500040007a074800301908461124040d4900780c526000c40c54000400351151b0090880c0c603140c01c0d54010a08068040d6816600791079500729118a250b000f1810031500c441080013044046402030000f00050806000a0700c6203015400001c1441803540001c5603039480203000c2c2c030b288078010383c01074000c0c2e10036110440580514011035143c0a920961041d4030b00001e88103040c42a = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 217928255 1250 217927005 217927009
    0x8032d070e1306060f08010902031e09030d060f050f010c03200a0210051209120702060c030d050907060207090204050f0f150307031406040b0d02130e0f01050417030c0405 75
    0x82807050000d0300800305040381c07544104140030b00001402140c81e00381c00d01c41c0000300242003510580004051030700400030b0029243c0e0b9801509034103050b0401780800c60b01ca241000341540b003100081c0b520300e802c080d408101c90748548601c2d0100c8070100e4a000169041a0064503580031880010b000704603085407101c9c449440c03402d040b40014100094844403209070b400205d0040041380120002180428000c0707043c82054950b43c0c02072980030082c071003021240000c07079540c828424001c2c01102c004c02d03105040718080054480c10000c0c403805101070314003462001c0c1d540c00d66105010061140c0036000412401e00e108850a603000940380442c50007400f8280700181c200f207600242c00c503940d910b00740503081080c000ba42c00b0f100c2075580803d05c0c188050001e008000003401340da11071440d08013850016940c00c000500e10941c1659080005c00f00c0d00e07025002005a03d144250501807050703030840c1c0c500c06510080c8601d115500500c400300c0071124010031408101e402241100d810003080c407144c = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 217929505 1250 217928255 217928267
    0x40b0108060f01110f010609111201050d0f05060412030c03090b0117070321090b09100c0512210106020a0c0b030c0f0a0f090e0c09040902180408032d07 67
    0xb100c010b052141c5402c02e0200814a00342161404a0950f50344200600c028003c0380542141182d40780c0d039050800704104100d001402042c03080c2440f40c4030300c4024000304003c3c000103022154100d006c1d505545014105601d461840800010003c4c1c43e100322260424001e01c94a00500c1d08101104641da0900c40f4034a111080c0d800f52000031b1181180c00400070303003542204003100c8a42d80400c420115a42c1010b0304004981e00000328202043c0844400c6850380c0203040800b104600d40b0a40e650f100b41440c40c20615603500e02d844480001030b040c000d98800040354008511141040c641d035aa852500300c1e251501c1074401009800c40a0341005050004009160000114000c0034a012403000180c0144c1d8881508180400c2e83e0f2032407580301c25001007140000f0020b02c1c50180f81c070324104038019054859104a0352040d030380c03401c1000540d11242a107040c4103450080328003c0d07003024281640560006c65050009103228140d0342160702600b14010300c2a5006206000f981d19a510f0507100 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 217930755 1250 217929505 217929529
    0x612030901030b12011805072705070e06031e09031204080a0e030105070c05011a1f14040f18140705030403230a17010305030904020a02070e0a050114040b010806 71
    0x84150754041c40d03a1580f5080c41048189002039850310046c44680c86d0290606034560b104400242001c580e11000c1d00d520300e10304000e803048100000c0c00c5d17134500000b643c5101b201c403040c0383c016034041b041046d003010658002c2413005489420b982a40d0380c8880565891203541071440901080c100800e000810710700145c004000f040c00e03c40340405085001c00d0071124200c8202c030000e40f40c100748a003408000e00c61038a01500c180d194003140039080c400b040000620503103a000d480c0c00f0000151545200300c01c640d030021032008115590700d41e0360480650343d02c040e000740c811961030b041415030329800b1807240e020094a5051007601d943d4074148242c42c42c2e080100185c06012090200568904803502d00f010901c1511300001e88070900100e0043c94800c0c070001c00405040320300010300200c0c80008c02e0f5074101c07000b120096a6084540307022401e000c0103038814155405548248415a89280c0000d8140c1d801041010400c04525080000b668002c0f10914086105080400d12a0030030703510302c1f99 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 217932005 1250 217930755 217930759
    0x1215030201051c020f2a0d0809030c060109020c0f071202010509060903031204030e0301060e0c0c03121305010b040501061d04020906131a0f0a03180804030305120612030901030b 78
    0x41260340b0b15400080e40c0c17044085090444000940c1c102e000741810940742c1b002141c0e0030085455004050aa6545030203010b90b10601411400291940c02d0030030448200e00c55076804c1c1d1301c10396500c00e0711030041d400c084072004a07400750100417190785d98001000c0b001c4840c031102c0c00d555241581c0054600350301224800342c200b86c0c00c001c04419603c2c104020250444e11031302a208500e0310303040c014500000254454402d07414544200f041c1c4d1025292223070054941642d043c0d40e10041c40030701c0c1c41e610480c0900100513811404000059130440040312990340110000d003d00c01c007181c10002116401d02410020903810708039a06201112100b0795102070000d00010b180240d01400120f454011440307881030141544010700001034407512a5850541c3d03401440e0424004860b0161203026105000c0f0415a440d04242d02e210864084c14150030b400c07851648d500c03522418010410703803018a499092814401c08140541041c0e005880030751001006982000e03042c800440141c8130000681d0717 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 217933255 1250 217932005 217932037
    0x31d03030706060308030f09060106020a080d0608070e011509120f0f1509021203030f041e0b0106030603140d02030f090102030f0310050a0e070206011512050f0106121503020105 78
    0x301c0002c45a1203400061350269a6090f101d141801000c8120000102815070581220b00108030854000441d0401d050740401c003180c030303005055101c2d001420143d01c011624443e4800000d42402c1000f5054162103030102d054507051000402540c9404003403103490481000c3c06003a5012902402906044038400c40c2032000b00e4803540c0310010b00000c080d200c940e003540d444c080d0000f18603017800c4103102030100002660a61a00101c10002d5240041001e0020500d01c0024005c01c200c8841c0d0458255100c40c42c8046540c440400800030400390100722503140b643d00e4a0100c401d000a04030407043c0265000f0340c03402038282050140754003c0074206040d07110a1040e2080800e602e00654031940400c0899044580303002e00308244884a54085800d8524400511500d10343c00700d90941900e2884010b1700c000b80700c04808070340c1d00c04103081e0314428038034000520180d4000344c540281241c040383d8400c01032864140b8000125500074003900d45070400301073704000550044000d0441170350746024130 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 217934505 1250 217933255 217933267
    0x2503081003050604140a14060702100e0c120a06050a0b10410c100c090303050304020f0d020d05010c080606040f1811070501050603120405060313060b0301290607031d0303 75
    0x281d19421829420000b54000b1401c0055092b8100401201d003641c2040905c031410070f040d042d0b9207071203001140c103010b2080c800c5030545185082001d40c1745c29a11600412103443d0245040000308005148280320f465048290071145101d0664180300c002160309134640507c0800c0548000ba4104040e412400c1d81c090007201107112400140003510360b62006040324110301030440088504a010312030502000603014404254000f0589900541c151580a4101c50701e00c0001d0f80c45003480c03002544007082004032420030a040d0800304689402c0d0310b480d0f10715161641002158041c0d4040c17284002086201005502c1c2040d4090910481040c000543e2030038203040400a603000903030944160313440e00180046810100700361180c4040d6194079031304041c1488001230841c4005024141d00c00418000c4200f4002564011004600c0c02002040300e50300a070101130011891058810100b031090407a0300180c2801c0e003ca9040903410391740d01070444140c018401810f1042150190148018024 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 217935755 1250 217934505 217934513
    0x100504110a12050706090b18031207030302090a0501020d020a020603180d0c0c0506180f03160807030605010b0315100513090506040b0103060509010603020d022503081003050604140a 80
    0x4500040e151078000758690b0405070030f200d498280e1a80c040004c101e000082001070030b09000903500d01415070340b4201d1900d00007900003442c00350204458000c490000842e0801c040c2c150b4001d010800040e02e900c0381c40c503611001a80c48680001e01a4050780000c1031050051400703000860b40040e200407070049918550301414034203155000203602290001da0303610144000011410020303d800c60707440d0700c0c0500000b0180c1500031400b0040780151618072a001a6070342c00d0159264051412011042c602c0c1c1c3d840d40e0325950403803440f040c0c604605c0d000c004940c04290000b04d920420001240c104915a001e050224515804902100700082840450302c401810315004e0f0050449050201c0c10b401c01004200860300300c03000f41c5050500d0701c0c8040102c0e07122422500c1c11661130b402c0041e02c0b85038080209010744035000110f80d603803440604590003400c13a105081c003694001d03500c1c0c0186070360f402d005070003041c11381c040506030368440400a00002d0740c10918000c0103031480180c032a000d90781d1361 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 217937005 1250 217935755 217935769
    0xd020a11040216061a0a090b030c04020a030b041a0103061a040b0705030714060403090b07050607031d010207080408010c050708090402070303110706060e070201020f03150301060f080606010e060c10050411 90
    0xe20403842c4039460000c104c5a286c103000b01406803905a07410061040d4803030000c0d6482c6c00d40210540144d1300132898074022030080e4400b504528001d00140000b00301212103032a14402c80f0011400b00e840c1c0b000119a450741000000902c00003204c2e0140703003c1c14600818100e0b00030610880f42c0f813004002000c00a07a0220030003c00f001d0b41d90041c905820140fa0240c16000d032038018502030407090142001080300019403d170444090308000a035281c044140c9040d10540f0b022541d000d41c0001084020089250f0080c0300b107403607000080040b60101c04085801b80b26020014040b00002c4c40b2400003803800b98000c0078418401c0c2400255440c81c03109031240b80e0041c0e801514002d680f4a02000b0359880c0d042e40d01e40c0080188021441c080d142c20300c2099500001d8101c11030162440b1900e24035480951140d0043d203241e0f04407140241d0380b8050a640c9480403120640005d580c500c45030054144001a200b104041c10080c104e00c032054000e40300107010013030050b901c0c8075080001c0241c580b1002 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 217938255 1250 217937005 217937021
    0xe16031e0228050402160615080d0206042001170601021501350709090c080105040503130902040e010e0421020a0b1509011203140f040501020d020a1104021606 70
    0x8005540099144590820b141c0e41684203502840c010000420020150000092180e90004001407203c10700344680b1001d1030a50406200c0d0b04c540511102c1c000d40025030f00f0302c5207200303400746805c5004d42c146203109500c03003544031800b15010803800700312021200e00141c2d2040c030620441d804004110021880410b0a0348411080c50036408104607440b1100e0b50310b0b584004141590b5041c144100140750b40366101d1003821400f0340c0d1010100104401904c2c80801004004001d20290a1a04140b0307103e030f10000d80e28090312682c42d400580c0b0003860007520115608000344540c5a07192242c04128208018002c49076010341c02c40b01c0d030025102600700c0c03407400d0b500e40c020606844603280c480001400070b0030000445c0345c0c0e0b50444680d55554052181941d00340043c8280c04046480c064810001400c0b603049600310101e81030204400410180c401c84009908032905000e00c120281c1c5c5850118101400f40d090701e02081c0d0250a140d00241056200c410407580103103000e8407180103c80d004 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 217939505 1250 217938255 217938289
    0x120509090a0b030c0f130209030715030204050306090a0309180f0624050405030d110a0b0106020a110603040b0109020a0207090e070f050a140103050601171302040e16031e02 76
    0x150720040b209003010461144070320004e40d000005001100f0000b0702920b900e280500c1c1c0d1640000341440243c60a1040c20002c00b00d00f1001900340d80c42d1500074002c1d4015000e241e01902c900307030016541650000d40105060741507150f050504d42410380d0318111420041c940c40785642c4030740c2d244400c03492038460003004040c00c00c0780b0020308601c080d41c4c9460386001c11205041100612051040fa41c012415075450703821030924031800b0000040403070134500c841d24042d000003100d0f00001480c0303401007180200d1505c14256014840d0807002000040d000c156806008104940014800410380b40c0c0141000904c034012100a20764841900c010741c0d00d0031812860907042803008004020140c2c0c0749401a0204454035210a8280280e502008020540d0681015107031000715049901034040800e0948844c0e002c040241f42c0b04106200a01903564128000c516015a8440188003c41d103110305d4042c507140d040507070b4034580740c20000454107000c15504584017241e4000696a100300700344c0907142 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 217940755 1250 217939505 217939511
    0x30b030604030f020c041e0c0207030b010305030c060c030c090f030c19140607030507120309020603070305180606030a0f050f031303050d031103071110050c09120d05030103120509090a 81
    0x1000c03c028142074103086018015401d241844403820310400b0700d40c0c44481c0e107180000d003400c0c00320803c9182240c903074005010f0541440000c001d010380400281701c04070f00c0004541041e150800b000903644002c8650101000f01481005c12525041403094035126004088484c800c1c1c900c070005072081c10f108100041401508420030441101040e00f1a000000701c0c0d003541015010348018055101d0400018046072040c20180d414038040c2e40046001d42c3c001e400240c83e881c1080340030300201400e50310580c079141c4541075903050fa03074001181c922800000c0c019049140c241c1d0340f000d00082c802103003102d4074080d4a41c1c0440d420000c002a10b00400030781c4104506500d1414482e0400d5a2500c9007410117042601001d11540b8841c2160b400c21594544510750300752041d5841d061550800a115030142410144842042054003400c00d000044070b14441d4070f500000b035583e039200452000004501c0500040011407402c14200038104c03007a0601600e000c0c003440014000140886640d001642c0e = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 217942005 1250 217940755 217940777
    0x2d032004180203010509030c12030a0603060c050c061b0901050a051c150e010803120603010f0c0801090f02090a061803050f030d060b030f01051903060f050f2202090601030b03060403 80
    0x80e090003116000306d0650055864074030a01d040701c7d11520382c0809030740d803220008089a02c5400781e6100b49c0040d5003000b000c00200043c407034001c10f558840c42e0165154840c2c640411800d4150310f1265003440c1100b1701c400e242c079003803000649080e080030340c21605005c014003403190030303280922088070900156500002c0030740308245148030000141e0040420011014010b011025002003184d0046296552119a503a241c40000f4054800c1c403441400d100d05104841a0311034001d00c40c0c90603240070100a021b801e208088810403401807010150740001c80700c0c42003110380d00030044542e016541907041f0034038507101d46540c1d190103040c01c0d614042e03500001d114503a00305140700b01000b52103049910792030340c00c000008282d41c04040c09460310070004039980440240e59555a540195400300c0c0501c8212003601d10300000746011100b2117031281c60b2000044103010040c00c619100240501c1d0448240016002c1c4011040010540c50505035145260700c1d20796070800061780710324866920b84000c50 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 217943255 1250 217942005 217942009
    0x1f14041d0304030521030714090d03030510140a030213061d04110d020d14010e0d02030405030c09011a03090309040f0e25031b09060f2d0320041802 65
    0x46882c41d042d82c108181035045d803650b03080c1c070740c200e80c0c0241345481d00c80852044500b00184920407264166409001d44072901d0425425130031180c465200320b00a2031910b9580c0c182000c8142a84001c560720800c0038909000518200302d624079090040380000540f5610740038100a160602c868080340b20031460100710400c280d01c141812001802d683c04054002c16a001c10181e242d04800105102211a20004c00354001d40c4642c0754400c8001c200d801d003100d4aa0003035102e601500800d030083c020340e4140c2a0310306007042c445040340d00080d1060480c2c3c144055050301e6402c00f61071907101d8041004040c0566459001b000c02540e5528030008582d43ca0402c81494001c5510440d60442d183c40740e20352124030000803040451b6007113100c42e00c1584501d071140817512215041017103400d25042d00850000190784455084e00d044030801c003503041000c226030401c1819248107103540d201c0042d00b48000b609208072140480c2e41707030744c0982000050700000340c181ca02c801e465807400414203400c1c0040d8 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 217944505 1250 217943255 217943263
    0x100207141b060306130b030105011203090e04081207030b0a03230c09071404030501090503190905030304051c02090c0c0d090e07030b010903050d02070e1f14041d03040305 75
    0x5000012038070300c1280c00310408119103010040034948070f020503803084070090f02c09401124030740b200140200455a101c0354400030840d0350050650025505a601003110290300038a40d0140f40c0114180e4241110041d06110381e040081c40d6804150f2100ca11600b5070321904585409903120380000c4650444011b00b1a070503c007042108521580002c00d00c104a855601903260002c100c0d1800c0c0141184420301020144241e82c0010495860312606000b80000440a001e1803003454a41c0031020400b43c0c070031a60400140101c55143e0070812007003010b80b5103590001c0703241c00e000560402d00151500000c0d0340800448100c00324180002c4c524220201c184052030a080346410040c0755141131006440311000010450818156200712442440c0c1c000c0d013001004583c41001c0b103480e9030796040000c0d1103030590304c07403202e14a08460100e0325084415504816905039954581c000e286817030886000d150841149542160380e498401940800c042c40001e07408959500460742e891135481c0c060701d4 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 217945755 1250 217944505 217944523
    0x619050403292203030c0e0d08090f060c070b03060409080c0d0e010302040303050d05061c050a1208041a041b0b04050f0901030b01030809030c180906070e0102071710020714 76
    0xc0200c2c41111007103005800002c0f0f0321029014030300080c1003114114142c6003400c2204007994803001c002280800c10200d0001058410340030340d029521170014005200320303030080b0401d1240c0360300702c4041408080401c1000c1c55201000034008100e0025a0315603a0b4140d00c402c40264107078014031001000140c01941100211400b803900f14030389859628020501d0140140701010300b170300c2d400440c820380d6a41c0000038004115440d00e4201040c0c51070b00c6559110010011100200c011402160080c0182d00c0148503a4016000c510f10820704030304992014001041291403007140928201880e00a03210340010f040c11141e1160740e05d0400c0100404c840d80581024440d000100060000540021013981180d0740715101e5a110b020440020f824050125100c540081c6111001c01c0880700000496003e00c0d514020b4940700c0c0c0387c3c564115400c2d40c00e001458096484928204000150b40c0d00c1104045d4041c07003984d0442c2c0e220310b8800240d0b030051a00341c0300d2407000080305000001c11b0085100b = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 217947005 1250 217945755 217945771
    0x21602090c031909050f06130c0905190207050115060906172703070f0b04110301060803090f040605120f0f0309030d030507050706051008100b061905040329 69
    0x400c6140c084144071141d01030781c07070f11100c2940303800101080000410a4007413a0b503519060310790b586820401808100034003181a02d110381002c0e00040d4258452003000d0168440c1c0e03030f0300580f65008905450107036002d8003003107415660700c0c103664145101e03038100c2c0c00c007410307445e5220551145400300040074601d109403030401e1940c440c81400070070717030080b0080708145804101592042205944103800c5001d245000b420a1000400f00002c100c1088103942c442c80c800e2925010315100542414200d070600e000300b003000e030701c00c2118400710f1400041e58000424000d2003c1100c2c1c0e280d2005c940d800b20740b8030f0942a60340c465156191400010301221400e030030840d0040d4200790400000075511425504182c1c00e1680c1d031004506058460700c01c403100640c0040091209027810319001e48156085c0c4240700150140c1c0e40d1180d030550440c002c441c3c01a000501c2e81f8213060b0003000c5041581c5168141301c043c48010000000002c03c210907040c140d1501c2203243c01c00c804001c510200708107000706020 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 217948255 1250 217947005 217947007
    0x1b08060d02010f11031c0c02061509191103040212160e07031b020c0405010602010204032303040302030a0b04021809100e0f030f0d1802061b10021602090c 68
    0xa6544440302612649a0246071600b60143d9100003a03d00c4c080b0b114690402d800f00080d02c2d414101580501c101c010144102040f10702c2c4552000c80e12001e003501e40c10025089020a0314003443d00380c5400307030000c400140c4089100658000a001c0300d00c000d80b4130501d44c03408010082589030080c2068440110b4034043c00c1c0c504030301640700d10140c109000b0b01c00c040d40d4143c04980920703c29440390744040e2400348990120003004101030360f1083e048005601c40c905000010036180c1c818003e41c2d080782c0d48001c002c0508601a80110f000204004007412640700070321000002d07940804c00c2c81d090741e00421042c0411708042c01802a44101c1c0c0d15400043c04501701449403401c80011016900f11100c000001d640807417144d02da09003507148035028007521000c81c480054031045030050000c042e40362000c10100741944400030baa4480303040065400b08007480805640c6e025080c40c0c82c44510340300e0583d400d40f0100200d5504a0300280d00c01c1c8900c2c4212480881103041c6015001c0c0c000107032031405 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 217949505 1250 217948255 217948261
    0xa0e01180b0607080a120e0f210d02070519081207080c07020405062101020d0608160302010513090f0204080c01080c031302030a0c17100209011d01120507031b08 71
    0x2c19018811600000d03c1000005191a403481c491410141c000e40702d564203021094518001903a03449400d91141c0180c000d00c00c40c140c0311900340045490b000420200c6a0400602080d12002500407035001ea8540c00b40c0e1007040d4913045a0f59807001050b01c03450781c481e10f40da1030011205074440000e00e981f0510003240309002100904000f9201da0b17540c1103d0200c1c4903a43d42d40030a40040c2c0804c0d50000284104014285209045d000751100c280090800c006041c1c1d65a485ea65807071030071059800d5032160080900255100304010700c41c0401c0c1f602c565042907500c003540307400c558082e6110300301c4950100e0705202445040c0100d85801000b403070141e03480e0401189a034090f210103010720342241010000c442c115103041c401c888205401c1810740501650791403203081f604445090700111401500c46060b41c2c818503200350f5004140680d210b145280003008001c0009084454940c103000078100000103480141c0582407240100340d03000b040800b14a0120826413074228042c03002d00c4a05c0c410 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 217950755 1250 217949505 217949509
    0x7180618090b0f06040b120c0f040603020907050708130305070303030501150815010e061303020a1a0703181e08010b061e0304030e06030906011d01030506070c030e0a0e01180b 77
    0x31040d00011520340c3c80850b503c81c600010001c088500290790050003810301ca4403000400304419a2a0308180c9440c17aa40001104001c1199990b00000b9841603e00010500f0140300310042d049191041040910f003001d210034803d0382d5207144d030080300c490344140c10900030107505000d064010110403c0100704000c0321240a07217410740040405d038000c410b9001c0c440443c0e10452042d03126000160850b03070354903042c0007a10304021850005a004011000d00024104c4141100440004035000b1003410005a641c084504e41c05583e0304030411a51018080740c2410810fa0034440003c0c51250f40ca030180c03400060a0a498a20171650300c19107040c40000c507101c55080c4140718810000c140b20390340781e985103010f03503100000b5285a9003050b0040204081c51a0000e1000c1c162412041681e940d60300381c510401000c07100b404003c00d10b80162000c2040d50340100c0d0b05030100da220381000c110890620b0702044640340540c2c07165414642e030324010004420b0740501d000318410354480078040c000758a00 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 217952005 1250 217950755 217950773
    0x30b0f01030902060f07080301050312040b0a0c06151206050c13050622151403071b0c0503010510050111030c06060918030706050f092d0718061809 65
    0x52281490780718a030007021503543d6070480703001c2454031401603102c44c01c130308200d103d64001b40074440c068443d203428081004101d000351002c58000b144414540300101c0c00840f1800c06080c0300b1244a80c40305d0462640c40c44080d03010000c2d001e0003c1c1e03541c0c0803000d401c203a425903502505040070103104000c11410015408101c50550b201500c95550303422802e103901042003040100300c620003001290104003d40c030a400301f0228101565882c0c140c1d001d8480b2005203101c181c5172513020412000c0f284480c81002d22842130414000c40383c407043c0391307600c0011a096510031030701c0040090040d0300c18026980c01c88501200600820011404d0000f19804160f8906020b8015846400c400d0001214285001d0495509060000a99803039000758940708000d00000d4410b100c0c4692450001500342100094002007900a042d880c0d81000000701c2d0070b9140c50640341000f0b00341c01000f07030118014443d89450210044600800500076107480d410440c280320701410000400d041800e040007142e0204 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 217953255 1250 217952005 217952029
    0x402040b010e150c030c0102030709060206240d03030e0d080702012a03021303051507030b0904020312031e040b01080613241803020a020109080115120c030f0b0103050d030b 76
    0x80d40e81c0d0484c0000720315500070644c100a05600020400caa1a948440f1280841d145a001c844580c2c0300c1035407194886605407030281038110700385c0150b0400c1c98100d0740d0f0141d09009040004140410001940c20081a801058040390345181070181075582481f6401141030404c0d801617003100e00c42c5032085840d44030710302d01080503004a02e10078442d41118203840155440b000b140d032204030048200c2410002110b0340d0700401e281504603105410b0420038607220b160300030050030b20125100e00607116904098110000e940c40b001e46a03e0058001162a00071402026072041ca507262009040c90036100400c002d004603e00407540c4009428040c0a00410004102600481c82100c0343d54000346150500c072805802c241200006150300441c4c0d860743d41e8000c3e40c4120103262600b8a5900740c4030300450340000d41c400030404002c40010400405400d40c400c00b83c01c540f00c1d0741d075100c0081c040c61aa000741c41020f111001001000410880304c43e884146040034030850301c0490000c0c40084400c = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 217954505 1250 217953255 217953289
    0xb03030702060d1508243711042108040603050601020a06020301060e09060103060602031c090c06080a0c08100501180b0a0f1202040b0912010b09070302030402040b010e 74
    0xf0542580c2e040c0766820024842c00c4240100e80c40036a281096513440d400c1d40c0c0600c00f214039480320703880d10705425585076101d4840e441280c0003010b0800d14520101c034150303605515004813040e18002c00c0c079840c02000701c05051200c0045d00c40c0e0604020070301602031001c02c112184c00000341c400010380004c00782c0742100c60340e0400080e260b98010060303042000b03000d0000c0c4091710010000c110141c024082c2008100c0688041e41503031740f900015000c4802a000d200050b03030081c816500c240c81c242072140750050203c00040b408200c1c40d564802000c4503600001c1c04101c407241045080c4000d846404100360a40c0381940c841c0c10300c0800d2950550701da0203094100002400c0301e5503071050700d202103801031030881d480c1980d40c0045040181504c9400316418001811619103c404420900070340d01070751400c8000a24028001c010004402c0b1100c4020506549480301d041d455a40e61582d40d01c1403615440150b0340c0c0c0f82c24410403003100c0e80c071403000307042c031102480301d10071500c0e54070300c07850344000f2 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 217955755 1250 217954505 217954507
    0x90902090c0a0507060903030f0c08010f14061605060618010f06080a0b030601060f18080c0f1203040305010f0605030f0c010f020309120307030206091203070c020f0310050f0a0b0303070206 83
    0x2d011000c6030030384180341c400741180b400c2000c5c000c02c141d41a404070854443d0301801b000b03c0300c07038044210340b40c24083c401c50f250310810003001d202c0301e607023030342d41c81e01d0480001c00719450b003038060b0150f11416089070001d8461790400c00c100845410801c0d0361540c00040103800d20802c0d8140020110114818052078040021050004246005d1035002c21054040201150600d42e51303100e00401480b110102000000c1d088010010302c06420010703201a80ca40c440500081d01e10003050042c0c2a01040c0c04551120041d0701001400400b40001c0010314054030000c504542d14980c250700b512071176807107940660f0140019585504020950a003c0d02007440d04188070000044202d246004100c0c1d51503101000c41c1e040450345000100078038040c0e21a400b5100f841d6209c2201030344038030700b048d03400980c1c0340b04000191040307114000b4075181c84d10003044a007008221001291408408201c91180e6030307524824000070f030207901c612031360101c00a4030501a00d200700c408a91240108074009000f0a0 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 217957005 1250 217955755 217955767
    0x9011809020604051801080d0c0b3115060f05090f040804051201020702090915010303050703120c021011030601120b0a0909050d0906090b0a050a030e01020c16090902090c 75
    0x80c0750b10840b402810700500d29880040211a10807480d0020300c00c40743d05101d01b00e81840442d00a024030f2510340d030050018a055600d2006142051a08130007080150507104031508024000412104440b400740e10581d265041840003003088400030740160080310f041c58020029a603544003125803140032503400c40045d03261440c4c42c1d1494095a000f4070ba01c26009601080900c0055001c1c0280d680211118400c40d251240c0722521b0304034142d4150300042c1110300500c00309019000804c81d0a04c20b2800040c51042142c0d07507011100301c180d4210068003e0708015001400354041c03800d64040b000000c41c55810540000307030a5022404100b135444e03869141c81d1440e6a5803070507800003404666003c1c80030188924100e525014008203c00100c1c2000b400807a045109114000a580002d900f092504190440070341c0c0a4210403001c0c02019200c202c0140c00c0300c0c0a00191848403c204010403003403040c504074400c4002d6a80009030344619040074140943d84800099401841c01003113103540301 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 217958255 1250 217957005 217957009
    0xe0102011d0a0c0504020f0a1b060203100602060f07050a0c05030c01330305070b03040807061d120c07031101020a051b0a050609010f0e0307030506010e0f060901180902 74
    0x600c494a00310046425080c0040c0e804049a22080c941c4203ca8070340c00c0300c0c0c4410070403040380a00041c1d201401130034170448080303c0c05100744500c0011107400d030540d4140349540b4001680d00c01c03101c40c1c140e6505401c0c03c115040d01000110b0304a180780b03040d034240e07180c8894020004d01400c108101000f4585812006204091080304c0b040a4020028000d10026009030707030a07050000c84140c603030071b080c50001411514641000d42a41e070b0260250003d07038a4500b0030060364201030b10a5078241d90401c41c00c0c000131a1841005001c12802e0200302a040d080d601050400031240300025217008108945625450701080510030b032503124100344031a001c1d04004030b140c200725035002056841599070010300c038032081e401300801c60340860300010744684031820300006025002c03400d40401c001d1203480d02c61754003d0035881d82405001d42203810a9a580d01c5080c58460203078001c3d100c5100c0c131403c0c41104070310f0201d00d581c40202036448201c2d5503d4203800341d22001c0d64207503200070076070f0303c0700705000f15 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 217959505 1250 217958255 217958261
    0x141f090b1b1c05070f0f080103020607080f07050c04050c1303140a0b010806060406091407300218030604050a1704090c02031308071a030405031b06071407120e010201 73
    0x12004119008100721280340b010b401400b0640d04040811000105c00d26200d101d800b0f8800010103d548100c0607074a1942401281c3e00300c00002c81d20502e061003030a205030700090180c004207008000400c074691f5000309000c00c843d00500301080800c0c0400001c0c42d28802045240112030303120310710708a214841c03280c00d4142404018010044001100000b40400e40083c1c0c142c000c60081710104803259403800c4c280102c40c503440041c0c010301e1540001602c00c074060440300d84201840507a6244409107121035100b20609001c0598460768003281030301044404040c820725a82042e002400c00f41400c0e1119680d42048820080407508507108020300c00c8041801d031801484920014403400d0543c0038007a4070394120032564a85003c02c1c3c1d0000490300c00000307024048070001d01d0130326204050080e4090aaa0000b00280d9652208010100c103400a60041c60025162540944014100504000d202403910300b10b8410400d0140110008116040a0303009203041c1c504144120055910060f405 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 217960755 1250 217959505 217959517
    0x13030806060c15040308090109150c090b030106030606031401050d020d050f070b0706140c0d1113060504030c23090601110709020a230901050313141f090b1b 69
    0x2d5009800e00050344119619003140207070700c6515025074640e990001d041c00c9451040c000380c41c0b440d1090000410440c00d0f4804100403285180c800b00300c0f61946ca0090146c0d00a0f0b0007440000c1c3e9801c410400340394184941e200e43c01801d40c03414460b52414000814100780c028000e803140d5201c0c0143c0003081410410100f03c0200481555036269941240071299001080107454290800b010b1144815554117118842c0b010207000900f4600304c0400c0f480280880d585a0301400000c001c000450900f42002400030400c0341d031441d95581c10b628000c1e00c2d940d15a44081000c0c14421480b5210344245146850340c100140c80c040350607584c0f00700407030308074445204440583c020303040040307400340c0140c00030000f420171a21a21419240c4020146c03143c8865090040501000d0029460561054000707540140c252050f0004030302d05900c1d003031610f0403481c01c00512913105420302020413402540010b010042c1e41010400105140c1341d00b0b030f81000c0205042109420b211142d01c0300b00c99201580c0b9 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 217962005 1250 217960755 217960777
    0x706140d050709120f060b03060405060f06180a0c0f05120105060904060e07020d0f02161211060d0209040506010309080909060301020d021c1b020304090506150706231303080606 78
    0x21300c801c0c0074140a000e020703043c0016034605080020081c1e29040010b0054013990f4440024521581c4940202e5040784010300a15446001d0a5490301d18035144002c0c10302903c010100050f003071800c2c1320090014140c8030840024484180301002d00d9100e0540e01d1811107005680031030741e8101410000d40144903641003007070030903408014401d040d50300051142000007a5190b000782505040c400360381da440001c1d6030524000300c1e02c0d01407084981d041d03c0c600e4400c1c4908003a40c03840911000050564021030030105483d03601051840040c0380c207004690b00260300303080800803500141c444600610034a10064041c0b0951000303d03109860035412a4611100003404640340d1036000303254540d100001119002e000e0921020180b001500310680c1c45031000340d002149001d16100c040c00140000500b1981e1110880210401c1510030800612086106240c0058a5804144006458092a911241c18031250300800c811038451100103642290103040088046c0e07218800038502e481000d005c04 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 217963255 1250 217962005 217962029
    0xc1210050c0418021b0f102c06040b0f07050306011b0b10030203010605120c013c020d03050103020f0d020f04060b1e0f041a09030a050309030706140d050709 69
    0x183d05003815501034a0114a4203640801d8403800c00e0030346998560408007030626030407070344100d5020481588000700c052640b01843c0710f0340a1b10003100c05014036030311401090742c102c8000c000c20048003101c060340c088840c030004800381c100f0000040507800010f1078036050042200019a841d83d07000440036100e940000403100350700d0f11280f144002c00c11444100d010307600700500459140b405640c410000302903c0d00404007142141c00450308203440c180e9000744002d103000000384030700ca4800d0440141c2090401c207881805260002803901111052030b0703040504e008010700041e0780d41c1a8801c140d003021204182010054000200300034005040140d02524280c00043c1451541019050084c540920800c408000c40052401e038800d0840e140381045042200380480c0400342c002e0300f0b5542c2e200404030b05007400070010903c2c1c013190103826101688042802c0180d40350402c016006840c1c03a01d000c032140358081684100078091a000806425107440010350264411236611700100007041e510 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 217964505 1250 217963255 217963289
    0x1905071b060e030c180a0b0616111806010906180f121406010f1a0d021303050f0304050105030a020903010e12030f0c040b0d24030302010e0c1210050c04 67
    0x1412070000c602090f8020301071041051482c0c5010701100340c8124844600c1e0a0640d0341282c80320080c4020380103541d1180003440220030b080d00140d9601c84007442034001a5900b641c0d00100004083c40340e03055040341001c90104012070368040840d10498161b400e01c40c0c80c501581c19807100030080782e00102032107609079000144c3c000d4400000007605002e2001e1645031b82c00c00b03079002c0d1161000d0085003c170349520b01e020000004540a18992071022540890500b030041d003a200a0380c1c0702043e0441280444801030041c0607040c0400402201244011440c06203800d0020f03025001c01403189000c650701040950007501c0c00c1d08800119201c060507109141c50101084802d030300142c0c0c085e00c03002c41580c00a1000d8608104031010360303104582d4282800c450480c0d0314042c01c072414100640d0001041c081120140317824056000d144240c002003800b80411f4001460040e888041d940720b14925902c1c480c010b280820101e01c11101c2d04000b207190b58134813140c968a403049601ca001d13640b99542c55 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 217965755 1250 217964505 217964507
    0x61211040e0f100c0503010501091503020f0708031603050601020a020409050c0d050d030b010504050a03080915040b1c0902010806090c0c150f090109050709020a090b0a03020403030f02031905071b06 87
    0x110b83d144484488040000707852100b400c40b014002400b50728082003400c40e050044104258850031400154900549001c84032484441d140e0080c040071101010041700b40102c0c6406030018424012071480e0810040c540f08000030f40d540304070a00039014070b50314001101440414040032110520140a0304040181c500d03103141c4e20b00d0403075074a9002070314080d480003a0b503101d181124211074000b2300c91806c190441d2036040c00769001e880c000364400ce0400800b814100030b0303000f074001012100c2e1840e441c2c100c1c0030308d030200c000f24450a40314107925080c92240140c1e002a01c6613002a82034510780354a950307110f40c3d07804911914243e01d2952003404048481e03c0902d1150500c20b0181c428001e01d2500e550405d682a1842a5030040140d008040d0501c0781e027100b58060481d030521443c00390101940d44000004951280c407240b400260005403d20506401055882200045200852400421921022010305405d8840042040005404c07081c4200c101a8400b24070610b03d0411460f55a068 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 217967005 1250 217965755 217965763
    0x1030305030402011707020307020411190509040c1b060b0612250807081506071718010c11130b090f060a0f0f0b130b121504061211040e0f 61
    0x2000c134005148211940013030705108100c580503039540d4000354200740321542004040c0c40c001d074910702007000a000c0000b003800d50b030114003062103440e102e04d60307151012818802502c00c0e1100b803100b1b1000743ea2180003624a030211040c20103811820000720005100c0000b5107074031170303142c103102e8403103015091103e11030303040340c500c04940b00c03100b010b40425a5405007aa800007088901101240c5901d0005058521250400c1460f030002405145010b1030380d130720000029640c40209800c00c2d404140c1002c40107054506107041c240900302070140d00b181d42d8914017500c191030542070180d40c00001080c2c1e408035603084500d2103e1700800a01c2a440c0042d09111a403204950305441111410000030f0800308801c4041c0c190381c07100419142050501c6160740582e030019800b0701d940e401f0404002540380441002e0904081e40464413207503800e00e80f96009400c28038007141482240351050820403401c6902071800025480110304402c14801030002d0001e1030341c80c00515007030050024030000210041 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 217968255 1250 217967005 217967011
    0x90403090905070e010c0f0201030b031009120c0f030509040204180903020c01030e0c0f0319200315070f0c0b0703090b15100513030c0b0d0c031a010c1a0103030503 72
    0x1c04200240c0c0d5408008650f212418481d442c045590007200c02c0200304005c0300300080ca40181004104202028007091030314500070b0964080c01d1759a001c4800304101c040610b022a05d0740d10307140042d8529620f50801c0040d6000703000301480070000b0b41040303035161501604c1c020310741841c1c007280c00840d0340351600241c07402c10000c90050080200c81c0e9255806440b0f180c00d8a11680004e02568544d4000d001c07490384403202d40d44d40b61244120040481a0121a80c4521482101c002c002410a8400c03074915009800f4942e200307400607024030103000c0200803141e0340b211040c680720122400000c000d07030703020050840180030780308034108124444c1e4064100500c03440c46403806035150398841840c00c3c441c55080c00368039807165290300d803030a910b1302c0b0700041c01c00c040c2c80e5010311503031b10f40c0d0359900d5108003280da200e1f0000748404160650149083d10412803514403506003446000c5a6080e20704021400101c0c4d80e05101c010b00c000b40c203201c10f183c82c540e416161304140280c036517100d04019203c5d400403 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 217969505 1250 217968255 217968269
    0x3031415100807140a0c0206030c04051507080a080a09060e0303090d03020313060e0f07030c0e07031416030221040b0603070803030f070e04090f2a090e0c09040309 72
    0x5810074504a4482c40d0007a1140c091a51603080314200f030b518800300395014856080410514542080150b42c07a00001d50081e0031802400790ba561416061015102c200e1526000c0d83c0002d00c12000891243c1046540340d296a26044071644c1c0e07001c1d07a01004110040d80a0421498030924221041001000310700030602c0408490042d040800200e007030348030481c5d41888219a0036030f07001c0040c5940c1c00a6800c2c90000060341d908850004003207203800c50a510589000c0001603040044610280401d50400e2883c6010300051060102203041c2c06400b4200360903502c035050341d083c2018820340c16101031003488c11a03910a9802c04a003510345940031758082d1002115880442c0031403400013803040884440402842c19580d8404c044002c02c0e4000b0003110902500352130500c803076a40c620a40c80d440303203c0e00c4d94031449040c5041181b203509807284004204e078140d41c101c2c4030340d80034102070408840c10030301302184400e4259420b506040e40a1304040d003081d02c0304240030405030401c50200507910a = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 217970755 1250 217969505 217969519
    0xc0a110f06040b13050309300102031905060907140405040609020301050a0504020a0c08030615030a0e0d02070f0b03060303040902040e01030510050f070302032a0a02150603061303031415 82
    0x142250b620b81c281e007024000b84554001c07c00c031815403c1c00c60f4040001d50425141e018902400307010f80c80b107010780d8820417a582e5800010041400c40f80094030b0b8250702d411104000a01c3c02602003081c501c8040d124600b4442c4414030240c0300f41d0054100c801510002d4828804140e6403400c89010390030a0150740c0c440e81500c2808a041e0400340f00740c68120840e5070756421941996100c8180c03583c005440c550704400c0c000100141e0850841c010b6000e84640040000c0049910b8101800d00081030088401c541007540100285a21003800034195541d512100ea6243c86400009295104d50391021200a002240000700585001610b5040701e000d81d080e206030b41c030451341c03160480d42c04845925090055801203880c561003503024551261840b8403412130303001c0040440d03121100a0f01e4103400114005101d02c60941c0c18003540da0300754500a03a445440c00e0100000b9103442c1c0060080340c42d40b10311961441854841c0c0c211110b07050140c5255160350034410885000b0b04482036003523000d018 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 217972005 1250 217970755 217970761
    0x20d06091509031103030c03040b0a060305160302040b01090f090b0f090a1d010c200a0b0c0a09050301060312050c100c02031e03091c030b040212040b0906010b030c0a110f06040b 78
    0x413010044030311480c44a82c115140da9510f50b994075540d9009010720b0715942d510307940400052010440311401280e04684681c08900d10b204010558120061403030400c0f2600000f040600c0b026041e03042a41c5d103d440c0482c25001c06004141240c02d42069a548800c50506003e45403003150b1100f101007032100c1e01802440d85007808a1700b40d80c0d890322030300c000410404c2220010703040007100c040196114010756042d0102c0d038550302c105500a84021000c0000000e80680003074001050348020141600240181443e6031298a003d040e41840c1d0000e00c440019180701440d004d00c8060940c03040c4610400c17559114482c000e41e00d802c49000c20f0300f4018220500850402480d00f45c03842a42e0b440020003108850f10120307007640c4290318100c003c2c5601c0d0b80d0501c109942d0350000e040701c00070241e1501d0036850a400c03c400d511401601c00c0381d440d0040c60061010f45401c9040300e42c0240c4183c072681c3d88010005c01101e0b006032102018440d80903aa410142451000c103003580114058417204104d51 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 217973255 1250 217972005 217972037
    0x1090b041101021c02030702012d08090613030801051e0a030c061709060610020708010612020316061b020609150a030b04060501021015090e0d020f0c0105030103020d0609150903 78
    0x100c004e9071400d0141e032040c404d5070300541c1f1904000e100a004034001240b400310710681c0d1481e15841080c2140450071f1641001030710401040692b600483d818038101011580b82c0700500f0003281806114018206101140d01c00700d0050f507200d02000c406010080c40b40d40d00d041c054602d15941c0562800110032500d024541811300c0c03810760080800038041c02d4151a0001007000f02c2001e03a001c070081d80580d0100203175101003845404c00801c0f114140042c1c00e0305070b2040500b0941600401c5002c1c881d5840240301c0d0ba94864604880351481c900d9000d80c0f203445000050b9640a41003100350310078851000c44402541c2d00300030300114200c5440c2800300f110120100310603264175004490041c0c1c80181c000c400c03200d2541044562111800361100007030f84603d5188180d510a44442c12140d201994001415504209135041110001c015280801820000a180e4801880007034860030701180001c06019080d4441060998405000301101e0741451690015001c090402e50201c3e070382c011809460 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 217974505 1250 217973255 217973293
    0x201051308030703020d09080c07050307081b011805041104170601052215030302060612030c060411280f0f030b0423060a0204090c05090109051201090b04110102 71
    0x80c0d0700004460540d5195542140250003c0000721006601c4004050100381913800130490300d004a40a89070041c01c04041c107240070384070742c0101c0c0c05900142c0c04914148018081032400c0000b442c0040703000400700b50081601140c0e4200075800f0385800351055288504800900c00c41314800320120207d41096411510fa50742441070740d401c2445860410350003201e1181c4103013545900c46002401e01d0003020441c0100c18160800c8016038848420b010041c54417014000749a4080e4008500d00340744454513540701d03a800b0b0002090016a00d940030306a558a54910401044008581c042e0382509505110302100e00c0c42000070840c50784002140e40d14148006900f9a40c12405c3c00354039442c1c1d507441c001200f15490724000014170082c4807160819050185e54042d5104040168070b45040c2010303c005c031110066140d003403210420000d41a80d0b00040b1100480780c04650182c131248000640a02601c800341c402816000890100001c20a07410468030704c001d02a422688024a9100c02d07080c6 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 217975755 1250 217974505 217974541
    0x1703070b01140d060509031819030f020d06020a1d0102011512080c10090b01050d02090f18070306060f0f1208070c051002060603011103100e130c06080403020105 71
    0x1181420340c0c01400384002014020300064009008001120400d840e10801c544058036800199080014a4160f4605102c0610103200d000c0b80c03480764030150703413180801c11045840f00030460300101c180325003035660b9000c404003003541111055642d8002018001c20104118020358619134205860800e59481481610006008240c1144461741009142014611200403c80d0b9141f01003100c04408503041c00384400c3d600b8036000100703140c0000e1400c403041c448141c20660040030306220000150740c4102e0b1050300410380f40140c202c5a21200d4580e4100c006403004130380c051042c2440001040542d90001c000c440f4214003042440c0c0e00d48540240707448041c840c0b40c000c05902e014041c042a0148024401c183c40707911448482030751800070800f4410078240c1000944c01503010000107080a000701501075501c0501c0c5442c501d04440200021940c5000300060842c2c000000b07880c881420540b0440342d03030011a2803d9581e50f80070014070004c82210308034015401c01d4003040c14004c450300d441e42 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 217977005 1250 217975755 217975763
    0x7062a030e0c090c0d0c0f03060803190f020a0605070507020a0e060108041b0f14030c090601082e030506041205030405030712030f050907062a1209080304090204170307 74
    0x1c0c0b21080410040541c0024084030b0900c041000400b2040d032880c8071b16107000141e03448040300340c054031001408a0750325a01240759030300300f0031076207111810002c14200804144c1c240810340c40b401070000c91078020040304c0200002e1901c010701421b1038200c00601205842102c01c0040941c6803c14026811810f44816010441040101d030001da86039414120754102103a10002480d9a04c4402403080faa5034801c102020b0346c0902ca402904060103800140c05094480d00058200310b00001c140035001407071011100c03580581150825070417005951010a1038040e414100e40343c0c00d02a4841c801942c0c00c441c0076038003296070349019004106403885150490050350405485072100d40c1011440300002c000c06540c1c041c0003104c190244100f0303000d014094000c10040b4103107440944840c80c0511544031240c1e01c074600c52840d444e14159009000c1d4046d0006040401710801614485001d401803d200c0c080071402040c01310080d4040e104840c031003070590015078a00000c4139140d01c90000041c0c = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 217978255 1250 217977005 217977013
    0x1e010807210b0601050a050c0d08010302040e0c0a030206030c0706020c0105090c0306040c0e1008010c03090b06030a020901091503080d090c050609030607080624040509060109050307170307062a030e 87
    0x449130341c065000342c000b80e00719042c202d1a081c2504052030901d030700d030034200001c41c5c500e100520544c1018030594609280d48001483c100d43c280002071601040c07448001d1203000000002051801404107581c2c016910020075920f4800d180c01c11030282c401162f15460510030340c2c50855042c90006540d9001d2030300891013000090138181c1e0340d10038000040c24107d010408600015008900744118458002103640000e4141380514190182038005000c0c02d00c41d501504c04407015903035110040c2d04441d081e0318006089a9285038140d80400d956102524404020502006104043e08030001481c07082c41c0050440d0b44079800c021036401030b1b01009130150700482c00900b013a800b500714990414001030000d01c800404035a603144140045407000c80c18107012408011605050b200150800c000342480d02c201400c00001c669502e100c0e10400201060581660301c1c402828421241c102d500b20100340044103400300300e401008c0c2c0341102803001c244c030350743d0a0710040d209104030400c814200d8094 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 217979505 1250 217978255 217978261
    0x14030405010816020c0901121209060504060e0301090204180605060303030c0703030504020d0203161a09061c140a0c021e030d0c110319020d020d0c0305031e010807210b 74
    0x181c1d07510840c001110f811361080100f45c6050b580c42600c202e008014103003580310204030514007000d21401c20800c40c2705118080b03805118081e0024192800c1c0c400d58581071786c01c1042203002078050705150101030340140c50400c4440003500f150040c41c07086800b840d400d00c105e40741c03882410b50b01c2c0310882b0200000c00c014405000040e1284d005290058001042418a10790070340020341270a4024022106002a28008010390110301c240700380466400e0341c0450074988011b020480e41c1c403a6240c8002000802160004c2200c22580580300c50742c0c524a4035156403911800c2c24009000e41e10542003d8401c0e1980c0600f0404410190320364001610041c50408104071300410140c8060340841c0280032000c911142095010000f510008420511710242c180c03480708043e00b44500c03c02c130bc1e800c54003d0440036003c1c54014a0380b0300700781c2d4140380c403d40c0c9680701809400f130042c0c000722819a105441000033100400010103000751405998246a0320232940310300c51501d5001d410007400384a5032400 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 217980755 1250 217979505 217979521
    0x7080606090105060927060a0e01180908040b07080918100311040f1107140303070203031501030608100b0307120218070225030b010605070b1602010e0a0b04140304050108 75
    0x1d8542800046e0183e06015005030002a09288607a040255400c45504019807483d0000d0210010001c45040d03150650405078040001090113908580740b5494154400030400240704542c0181264034995407150100c0c64030000c3d50f442100342c28800d1607040020b03c24030345c6c05816640680c42000244441c2455542d80d001400d052400c0b850340141d88041d1030003c08428003459000c0860b074149107590b14441d246c449031524200c1c11041c00f5500034010422003a800104481e007010000501c142c1105840d4012005001c40360800612402022080300c2084041c2d0007028841000300c06449000e40c40b041380704100000c06c0806035000c40b03002c5440714812192200d0a4015403584150350b0084c0c40030080c0c00c00d800300400c2d107040d014901e000070402e02805000382405004580341981c500425500d40458a42000d0030490545000c282140400d5000350310103000b150a4800f0756040c0d03e498108002006000ca400b59000300c01503e540244410210482c0c0c103480c0140c503210916210000 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 217982005 1250 217980755 217980757
    0x80a0212010f06030c03060c0206071407110d080a03061a0f0d020f0403050f010c03020a0e010e0a0e07030c02011a0a03081e040b0403030f030903140d021c0e0708060609010506 77
    0x1005803565581c581e9402e80146035402990099402100c00741d0581c1d01d90b00e008000c0b60403980c051000c540103070050041095003c03130356803035002c4040d82d4161034a5031401c110001189040550ba40040014110000c110104015003980c03020340d1000c1000302d903034149150031400c24007560007110601708030583c8052121800380501c240e003000c0049c1400b4256294000d01c1d40160026100d0b41c2c01740d005a85103c009000b800e120030300038901541800c88400005d8041c2007000c0c00241400760150300c072082034480304d40c65002400541d941d034006043c000d0b80a0010f211203034412005509090811100f034901d11038004100101520398400e0301d146886503080307078101d01d0b600070110013000c0740f0138451034206000d4000b5001868605584524601d00500714100300c0000380207260070888120046600714400302e032540b840da80a15520105071240900a04c0343c07030188a406102d60780d505107003e03c55809044c004001c041100d109a490f01489590750008658450784203410400600480c10500 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 217983255 1250 217982005 217982029
    0xe0f040b031e120c01090b07050403020901090e151f080708061605040b0d0b01030606260a020705010e0c0307050a0e071404030b090a02040f0e0c0603040524160801080a02 75
    0x58151645440080510003c59000c0c0383c0c81c1e9181e0303448402c442c0a000f20342001903000491800c2045c41e00d403440d03010840c00003052054040305560748e001b600000c10180101034a482044070f4181007450140a4070300314110780599484480b8403a0401720300804006100d50580c2e00000050889954101042191090041507003040120034480003501c00045030141c8544002541c003c61b000d103e1000040407103000d5401501017202440703550340c3c99100301f030314443c82e40903403000004d0640d0b95a9581004c2c1c131545000818642c0707031401d028812800482c20f055018011000d44480c00d80c4c6004101c5074150f540149c6076203010f04001b0811103401003038000780c08443c04101e81d04040d6252038031031840e0000c60382040c15800c5507221104510b050300c2060320302d0091038810000007120410307190b0348510200b182d41c040d42c00080401c080c0a810002d510704416124105107140c1d610140e030b640f1100040d01c06110350003503003000b564280c2c0035070201070603200750500810503069070b0380800c000c0c50529 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 217984505 1250 217983255 217983313
    0x70305090f0a2a1a120f01030201050912030f0f13050103140109050429060108101d1e090f0c0d03210e0d030b010e0607110607170a0e0f040b03 63
    0x74a4001816110301e0214010008016005a101c04881004911700a401042250b00c030560320010300044c6c2c0c1040a6030f107001d80540d0b06413213041401d00d0f0340b442c0d44074041c1903246540b0302280c481600003095006007400400d10381e220b441150740d00015420f54030410369114540d40207600501c00400b080e817101e41d000f4001c0010929181d04400b68042c0708181185810010100034100180d5580124176560042201c1d4030502e480f80c6002c83c00540d141c202450074040c2061203010072000014114001c0b840c44d03641c2810340c84ca00700303010600e540d8500d1206e010b40d2401000301010039843d01c0c400001640d501034171340601145600302410100b1940c0c000c2c0300c042c3c681d81c0914a000c100c04001d10803040800d500c2c0003aa51505600240041e2030040915100389003c1207071070002a009051090200410f0750401e803507841d0761415036010405002607186581c40800ca21100740d078000d0b000304200c042502c00d6441c00c4104401c2c0829200300c00d41080d0075078014195050303445640703c440c0c8070034201 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 217985611 1106 217984505 217984583
    0x3051b010504090c0509450423010f05150423040c09140601091707030b06190308030702011d070b13030605070305090f0a 54
    0x42c0303010b02c400054032020742c4000d040c040c100f40d42200b48024200c0d21a58108840290321040c68042400c1c520501c0369a400e0441c118040d0990744420144910b81a5859403105c403440c4500d0b8440d14005426a00c0210010b003003131140c11070303114100502040d981000d0454a44450b02c3c40001071041c2c1c0303008002407510f00740e0802c602084d01c1c29124401a651241071a1900c0b1080c0d910802c00f032400c0c6034a4020483c1007461641c4580720980314141c0b107a45644141940b070080d40f291800a500c00341041c80072032a40f51403191b100c28010a82d01a01001280500070343c04a640201c3d425040072090280301c940a0140c032028441154a4800349500503c200341c0d502900d00c51040c48080002d07114904110b2000107502843d0002428011410b05810080007000c049403d008507008030025840b100344041140c0c0035040c0c1000c000d4000041e12842d000c028102c1103071142010b04 = true := by decide +kernel

theorem cover : BRFrame.Cov 217805755 217985611 := by
  have h0 := BRFrame.cov_init 217805755
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217805755 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217805755 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217805755 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217805755 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217805755 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217805755 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217805755 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217805755 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217805755 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217805755 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217805755 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217805755 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217805755 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217805755 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217805755 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217805755 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217805755 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217805755 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217805755 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217805755 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217805755 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217805755 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217805755 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217805755 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217805755 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217805755 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217805755 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217805755 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217805755 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217805755 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217805755 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217805755 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217805755 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217805755 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217805755 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217805755 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217805755 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217805755 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217805755 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217805755 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217805755 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217805755 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217805755 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217805755 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217805755 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217805755 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217805755 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217805755 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217805755 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217805755 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217805755 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217805755 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217805755 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217805755 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217805755 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217805755 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217805755 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217805755 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217805755 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217805755 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217805755 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217805755 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217805755 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217805755 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217805755 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217805755 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217805755 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217805755 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217805755 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217805755 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217805755 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217805755 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217805755 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217805755 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217805755 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217805755 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217805755 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217805755 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217805755 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217805755 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217805755 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217805755 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217805755 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217805755 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217805755 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217805755 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217805755 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217805755 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217805755 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217805755 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217805755 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217805755 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217805755 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217805755 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217805755 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217805755 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217805755 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217805755 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217805755 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217805755 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217805755 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217805755 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217805755 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217805755 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217805755 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217805755 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217805755 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217805755 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217805755 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217805755 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217805755 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217805755 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217805755 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217805755 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217805755 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217805755 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217805755 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217805755 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217805755 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217805755 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217805755 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217805755 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217805755 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217805755 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217805755 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217805755 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217805755 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217805755 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217805755 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217805755 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217805755 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217805755 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217805755 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217805755 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217805755 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217805755 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217805755 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217805755 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217805755 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217805755 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217805755 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217805755 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217805755 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217805755 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 217805755 ≤ n) (h2 : n < 217985611) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
