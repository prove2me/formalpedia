-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1528
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T03:25:17.410079+00:00
-- url     : https://prove2.me/submissions/817844e2-579c-4f10-a840-b0f12a807099

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 274640287 ≤ n < 274820143 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 274641537 1250 274640287 274640293
    0x705131b02060402060f0334020705010806010215130f051005061504050d060f020a020705130603030504060c080702030715110f0d0c1a0115110c01020c151204080318 73
    0x80f0050f600d0504481d100d0101e00d46440d265240d541c81d80700031000300840301000e91076002c2d540541220348440c010b102503a9a08551840ea41e039401901d00290076203515005070406080c1d5200034a0700c2d184190414030f180821007030b40c02c0310703100c080c072142c0d100c44121456085600c85050040c290b009490308400304079030001d041c10b0704001c0d4550341e02c500c7c030484c2e0207071100100d0002400032590101c0c05401003800299a591a804002922020f0901903148502035055506400d000c080c8078100030b8913815159145068204842911440780c804011203a00c03104102002c010b071814402c50009000b40c0c5240c43c3c0f40101d15030054660b60400f403000490754402140b40307490500004142d00150b183d41815a41c590032414954490301038a5020901d616421000003501e011000303425110319034070340d1400e041821901c00c80741c0711100950f040c0d005a0042071410f04501d0485400110700d1180c44900d4075000300645c0408900108039426a08040040200042194503010400b1018107070360103 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 274642787 1250 274641537 274641541
    0x30118061401030f0f050f0106090b0702060304060e0f070f090506060901020c010f0921050609240c07051903030e030903060f06030703020a0e060319050606120705131b0206 76
    0xc00385000c1400c982e04140d00d40c282c400400c8416808151040000c0c5000c0c455860705004252410f4020300c01d0100042900394001084640c00c0c0540340410341c000c11941c40c41c0c60303d494010140005c3c3c410f442c2c2900491031030340142030b01001250010042503203048603ca180824140403100c000341200c2c01100100002174180ea8085022515010242022041c5900ca10411580c4050f150849200100140c030114400c902e0140c0310311a0a204000b00c1314181c0c1c0b0f0790750480e140e1583c24900a030300144050b44d6401110305903810340d800010040c0b11404e0605684826161602c4105d50610026082c4030700b40915505004400340100184010f41c940008600460b581c0d5070000c015024610703402000c04c0704c1c0da4051142e000190740050000f007586ea160200c00d0b1811a0546005200703120b55280c0e00003c00000d84005502c0e50484041c086130340d02c042c140502449a100401c800d4014454041650f69030000f0f100c0703410220f0580001d84c0c11906400c96271441c0302201040642d800001 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 274644037 1250 274642787 274642799
    0xe060c0405010c03080709170a121803060e0102090405180706090612050c0f032e060c03050313053301120f03120c05030412111216050a0803011806 65
    0x8020381c400c5500d032411104a40e200f10046500c44801d80000d8044081000700170813423a4001080034a02d0301905e01e0740a031a920480c16140414a100401003ca103510010404500c1c0c0768030107481c166030000003503d40515400002c040f80d03411200d0726800c88030088100c90130102048900060b02c101e003002038006081c204040c0c0049880510300d03030415141e8000642040c1030505944240079481d00301c54803414151608001c1898001d42d079911040010b91007100610000c8014084444645501c01ca007545510708030b4141e81300902c101314501e80b40c8943d00005000708502c40140a48151000c541d0040105000e50014641641e114900e068801803020245800325280061360143c4000c120050b1460145c070103448541c1204c0c40030389008041c240ca580c100e0000d5120701c0c0320b078040751044601c0701825984014885035010007a0700c080a1b00769054000c8004112560803050104a15003035543c429203070162514080700c0707194000c07004200400080d203502004140c0e2103001d00c15503041007 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 274645287 1250 274644037 274644047
    0x18050f0105041e020703030c0206160903060b0f1008060f010c02030706051e0a053c0903010b03031b06090703030c0b10180605030c0a0608180102040b0d0e060c040501 73
    0x300a9901c903a55460441035005202c184003400507210a10543d1a0417650030082c0017010200003a00c050b003e0280052195480d02ea44440703a1400380e121611094110f84481d002441a807820a40110341d0880d070007800d50300e60f40803050a224541d40d80381c540c50b1240a00c442e5500a84600d13050145071a05180145c3d000304080c01901c000349040c5407107002e9a92054100c0203030354004401100300285910762076034860010100c1c000c2c045201c503030f600c4901c40001103049120240c00c81641419400412820344840105a0f030b107001000481e40c98042d800203030641c0c1c4442510101c42d17000c00501c0241103400d002c000c0e813041a03940540122441c5840c0035000e0600d40d031009054480520000342c1c4100101000405030000100001c9404011100d5800920317460080c28031a11605041110610f01b001c580710988104d036442a1140d01c440e4003554660130102648034a0755000d210102d0a007940c2406070051852800b8040780c00d61043c60540c0c10500080c2c01543c08040820091006917045 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 274646537 1250 274645287 274645289
    0xb060c0304211a0708010b04081009030207090e01090c14130b06071208090120180402090303030f04110a21020d020a081b030c0117040c0f090618050f01 67
    0x559080c07600b1607082115000381d500700e0603004101500f0058031403040d1003401c0c0024482d043c50b840b6000307981d8813407054411034000c61141d4942c50f0302540c4020705400b00c980160304414031034011074210319140c1c5074401c140d6a134001c44540a0303640390300e0f00302441025542d00d0014050111540e01000790340c40860041098220038080092700c81d040da0f0031a4a80f1402c440314140c010802c1c00310039501050003450380c081070328850f1096003050400c00c0e003a99014203501030b03049095503071450f00f020300c2003403aa145c1403119034030351181d1300744451016034a0500046200314001d4034212410b150a10302401c0505017100010b011380711140c0107000403008004400d4500498185003112410b6920005071015440c400081d004405407400043c8540e000a0440041401203014a08007842509255850202000d403900180c0e0400e000e20070240407201c07440e00580034070800310360217407038176070000806003030340d210740c0021355264410004500c070403501c0c514494107500d06001d9403e03e5541403103040d0701 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 274647787 1250 274646537 274646549
    0xf0f0b09061e0d0b01031209080606011101021c0c17271903030e0709090206090607080d05070e0a0608040218060102010617030c0111040f1514071103010b060c0304 72
    0x81110030100b11109010b4680b41210001d03c00c0d000801c192400140181d402c0c070089a62540c00c2c0400c9520a024034070001c00d8810798401404550744031001162070080c0c607642004a55401c01c5a07103c14010b0b034000841e080303c4600b001c40c03203c0b030203038009003d04504210300031042190414815000b079500c5000444451a01c0003c4204070003061060508040900720503860555412081c10107030541c00044005204030b00383c1e014160b4855201003036401e8000300951001e810069604107203400b5002d400d00718014010305050850b034141c0e074822500180d5080e4081200e00015110074604081001c3c060666803814003c18200f59000c203005100241d0f050103603802c0c610005102c0d904c00d40c0860001e020340f4800c7c031880204422202d890f580081c5c1112204d50a2826183c40d40312807000300e400b01d8000a4007040c0c4146080125074400e0410b0014004120400249007102c412000280014601484200c00300c501d28030304050841d2440c018250003a201480070070704510020064a0444503 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 274649037 1250 274647787 274647799
    0x12070e0133050906031009050112030503010b030a0615090306050c04080c010e030c06040b0d0b0a0509040f11090a02210c07080f07020a0e01090506060f0d0c0903050d030f0f0b0906 79
    0x8401c11065840e0b0090308100c0b40c12200110030069102d42d00d0400c54119400035104100503601d55061005080d414000500812001c20040000524000040d54801080480064903946619003907004030600b081d0031000814a00092060004074410b081c1c02203415284d5524180c0707040c0020751a642c08228213410b2110354007402e040c986080c0002d04410f40d006140541c3e40d500c403911004a900301c1080c50554030300d00302e80030310a8141244150240e074801020071306290703510f988100d00044820000c885a501113045600c090320380007000c40c050142c00e1400750b102c03c50507042c6034840f003404e46201141a00c990a00100c031105900b1603200c1c68200030455960040403c01c0340c3d032031040c020b0007500200907200c006120381e10400b000d416a035524200b88042d4543c50b003013128901400202c00c05d41c400401c42c69040200ca80d001c803d56114070700b0b02c0801d9a54076242c450a01400c0581c40c0d01080d1200342408400c1c6079440741c803c508a03047c2d001c11080091001045000c1c02c02050f017800b4103 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 274650287 1250 274649037 274649129
    0x3070c080a23070302010f050402010e0d08070b01031415040819031103040516080a0b060d111002030c010c02120a110a060905011a010309051203060f12070e01 70
    0x502c0303106034010960b180801d21891240d1084000079560029200f640103501c1c2600c2ca409542880c0503450085405956104024420300f08224190702c01c130400303c070840300c2008402c1c0000c03124150b0500850144c1004581c9640c105d00c100d00b020211500b40f00801d00c0f1a0400000a00b11410703644040d26007040443c1060440c04280c00a140c003406c0c6607850070300441004100580001c89040c3c40f507409006074605079945000c00d43c0c682c2200340c0240811011740000300c01d428051108080c9500030020070b4018903a140c0071901c1507400411190050f08002aa26211b0000340501c401805d5544000d01d42c00102c40d030050003d008a00121040240694403051300d04410048420302540105040012201030300c0c001d8028010303021072000c0c101c440c055183c00e56000f403155403a07080c2c00c4030282101c5c0c0d1950540c050541d00052107075070300560540c103014203611030140307507005aa001401001918209400c010051005a0002008100c81000c0103002d26005482e0030844068050075a140e0f = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 274651537 1250 274650287 274650307
    0xe01091e0f05060a200c041401090c080f1f09091109010b0901080a0b03071a0403110a031a0a1118090f0709030f02131b0f14122205101103070c08 64
    0x122035550fa01d15840b40c24000040203154500923164100c800c4001e0401c40c020300e03d541030b40d550804981c0c008900483c00002003525240404011090070b10301100b000070f40d1510f580714100c0c0c1000805540c0410801510305c076a040211603203001d0004a18800d050010a40001b0b21860004140f4020b030740d140d001c061160f403020000070780078290741c098101c5c01c1ca004882c174001c4d5800ca403000b034510ba0060f80c601030503410043e02103410780f900070039080c1345240c501c44a40a241000b0700800c11590b036503480184440e951601905101d580c2c0001e910756000220200000450b0141248000c9240602400352050b08100e2407002c07240e1200400c66171401034000a074940240794603480115040450104c001005400c002c50803000c99101c02c0340c2107260b154100d0351035200100000b81d230700c8100003007460826440703a0035a0203c1810360100c06803e004410420030720b8611000c07240782d03100d131403c0c1194100c0b901481800200e101ca1450445c580800c0c010b2020b85800c00140c85c0030300000d6031544c0 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 274652787 1250 274651537 274651543
    0x304030506010b07030801051906111204140f101e0314130302150108120c01021303030c120e03101802030601030b010611011b0e01091e0f05060a20 65
    0x25504001a00c60301c0d070b5a100540203981c0070b030320120000f840b0a000811103151604c1c01c1e421035940d00358881e6440c0e04001c0c00b43ea0301d030b5000070006564032401044050800440300100050180030184140641088007841000701e500c000342e81c0f2425079114140f0f9425800f400ca020b00e016040c40501d84102c101070260001c0070448245600c28886000300308a2900305e03004011032500c20790031140e81e054a50b41c3c000302d0310001e010b401001c0e04011619600d54240030050210020b41c2c10005240101c07147c06105014042c1e032044010998591a0605100049140e071440c104142480c01c0f5407441407001039228046003130103d41040d90b42e010241e8481c207244e402c40c2041c1d03000c6d0840c1d40951b100d04091401d00000d110344030001b5102c1305000b0203c2d070103014000104180030070111900391448010345181003510640e83c104403200c400021030f4680102a081c0c0c05a0202d0b103074446504240c480040800a5041680958403c1000d00300d050f034801c0c00740d06802c002c511802d41c07810580a1085c1 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 274654037 1250 274652787 274652789
    0xe010908010501030605060915011205180a0c06020d090f09051905190506030d170402030a0c090b1005042715080102211608070309080307020102070c1a04090e0304 72
    0x22041d07280c0301c0040100f0110382d06c403030b00541c4112900c0e410ba9485600c5802040c4020085600150304c522060910b4400e0390801900501c1516003542400c03004000300d8a07082129030165281c0300d504904000568041c00071906510360740c5440daa440b800d011454a14040324450080290365510008882403030701403141c150a10074000610007800d162024502582190348030303415442c94480410794501c0c4c0020194450f0f03400da1580034011030301e4034484001e040002c005907014068518950009030384800304001034844500000f912860040610002044058001e000c1c081d040200340541f44000c2081200c8503501740c1c21240e040088550300020700b8005082000080200c40302103040041900a03141c41c0c0e0b82c05520007581d0b050030700514401c00007916102511025000740c121510b210345400d643c04041810049070311401070352200069802102e8800040c1d41c041003010070080ca550354078008205091020700030030025428050039105510404480030390322008214103c5086c41520 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 274655287 1250 274654037 274654049
    0x40b03040501110d0c03140118020318010e1b18010e090109060218010e0d020d0209070c0b1e09010501150c0f050708010b1518010c0311061602010608010b0607030e0109 74
    0x1383c035181000c2405002d4210450031002090800c03031203c1030040c42c4000e0074120342c0700c05c0c104032030070b048594004005d600280442141111003032032690b8100007400303440c503542282c3c03004240710040c084466409011100700244522080c504180f2281103014605054a0400800308060303101c4200300350042c4003075040100b07600e0010030302c0c028034a0411018007444c02c007038031610304e21a50b2108202e012841014025800744500c50343c4070140c1030032500c040e4031a903c0e042c621440291070302c2d40001c0800482d90303200302c03030303c40030800400c0c44901a59540280c6020000d0080754140101808440c1090160740c0c100100400890148503d01003a1400240c00c030007901e00d0181c98424107030203030408050b0f49010380d4588180e800103010545c2217402c1104600354059451202000445107010382d4542034082201c80805000301c13002c00d00030a40550340a04c40518254007a140103825101c05501503907150340340070280c9040d6194001180c15850741031400c0c4420600c4a00162010700c802d070418 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 274656537 1250 274655287 274655321
    0x81b030f060a050108010b090136020c030405011403070906230408010b0307120c0303080c07021c06050a0902031e01060b03070201020406031107240b0d0602090420040b03040501 78
    0xc00b0b00c0c80880e0344000c1c1641c1760035009001c504110303014000410020300c1401b0160343c104800b2001004500d882401c2005a1480c000d52110305040f1a01a070304011241200c0750800501041a0340c0c01c01b1607034000703048550f81c01d421860401005840c1c0807080c46034a0500403c11072031080d46100754410466842c522062640b100d0b01e95003005d00070998a05164001d110b662004207a40090541004010703174440005081c140c11590200d42ca490040c280004040c0140310310302c016a200564408601b81070001d8100d609501e080843c1030351340240181d0b43c2c0c60b2134880c15201680f03010640d2055514049038101007004510b45090041c8a0f0f5480008104408030a100200e82d040d001030084803944c0e6030500c80401491200c00b8035100d400c00c001c02e400c10100369044141c9400e03400d074461aa2036040003542d00c410034007081c0c080c90b00600445000d03500244442d042d1516101d400c01000821041c40740f004d41140c3c02409a1051340582e400d9020080005010080c0940240a0210100c281c0c = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 274657787 1250 274656537 274656541
    0x9120501020904060b070c0612180303090302060c0f0f090f04020406091401080f0105011815020c0411091804050a05160303120e06060607030c050303010b041e081b030f06 75
    0x918002e4006410b5248510b042c10b80010b1410495800e80d08000d03046080d03185c2403840e003901034601104e03003002c54142e01e844080200c42c2e0119540300c5425103002c0d4801040c0503480380390003410420001c20a146500c41032107030f2500501c01e4000e0302c0700c3ca5800050503580c0c1400200280e07000c800e14010a0740280001404118141d002141c43d0440ba201400c180c0b107045071500650300c0c110304490003e411180c110040110758464000b0300603500a00449118080e1200100c070003201c10b48000601603440b00b400748946040c0307413048411546032003004505000441e000a440e10041c05011452411004d001c10b0500600344030381803200d64042d003112207051000360218440b21081c441030303011544905200551410b54000c00183c0c1c00c07084060704490340e8140402169801c0040306608210204910400081c0304000450103840641c0d4a5511545421007129000110101008802c041036004105054001515140c07108800b0300520365040510007291500c250401c40d20300d2445404c003 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 274659037 1250 274657787 274657793
    0x1406070f17091311070f020118030308010f0b070b041101050c071202010e03031204141006080105060a05030d0f03110d0c0e10020d020c04021e070305120106140702040902010912 78
    0x20090140d90800c2e03c48444498010700c0700001c8880c0281101444034003000f141000614004400f500740340b050504d00440c1100d81d801c040200d40542045002c1001c00c00140454a0034180707250007071404017081d510b41611540d40c40b59129001e00024a06070b550f008250301a80100150740e1039500210480701601e07a0f03903c110340c48800d81d032020390214013080008600341c2008003c940e0000070564140050380c60f5a03951068045c1e81504214083c01610000400b2294601405004003004000400c82e418500c1c00c01ca8103810503401750380b00c2d900c144c51030410300d40c00000c205542d480c1400c0c00500005101c200b0b483c0c0748200824000c03424031348040101015001248a11507040942c2c1403004905801401e0381e0720207080d446030003d6800000c10031003e00d0250010300c1c404446d400175a09100b200602130b40190415501103021540204025801000191880d8014101c46c46e00030150803811600070114854010080d0260307031194408401c0da40540b00c0c410092003841050150112030381 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 274660287 1250 274659037 274659083
    0x10051e041703032208030f09191a09070f06050904090f030c03030e0f0a0602070204090c030b331003060302090703020403020307080303090d0c03140a050a0e0a1406070f 74
    0x10341210b6580c0d00064408864402842040c2d40c0740d40c001c01031455501c0324007c24840c0f64004245030300c28407130980d514103600c00d80c40b000900301d4401c070403144865a0b9030b5640c07490224000c0840040e0340c4401c500b0000c040a440710311f4111400341c14403944c0c0e109000042405050a204c000c0c104020011030300c0c080544c02043c07403000e030b4020f643c100181d404104082d41c890303c0c5405c0c0c640031541710000000c0469042e90040c10028402030000400d00c034107558009442c0d921364000d0f0385130051081001442a18000032941c01c015503003400408101d100403151143e005400c03441d000750440b14049040c0c1c0d00980c4a00e01454008000d00304d039103001d0100170701035071050000701c0c000e01850b480000d0b04100001528000c08541c405807180c50003483c001c45612090710407d60800c5600c3e008050300c4001103004006010803540e8550351031401c6140074200d07000541703207540181e0a0b40400c01c1002030400000d0b1005108890303180e512590342c2400a908083c6840c00b60480307481e600c051240710101 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 274661537 1250 274660287 274660291
    0x210050c010b01090f06120608010504050102120c09030a0807050a060609020d0b09010803040e0c070804150915090501050d020f040b040501090503070b090906010c05010e06010306050610051e04170303 88
    0x210082c440b5103041001140d00604612445030f040c210f81c00180401c0d401010b40e0142070031000750000b001941c2d042d1072402e403201a44c054034aa503000032100821070b0342e000c0055009444007046898194180003099845c10007000260454070045480010407406001c0045000c1e000001030180030703111219880250300202d1900c0525146c03500361a094205055002c3c102c45036040614101403070a14002d200305401007014102c14420401040044c040b0400b4002030075500d0340072034000620000150620301207411000036000d032411041c00e82a070100c0913070103552007864a15180d074180003e074006030069507020300c6104008503012030068100070141048827402d80e12148000d035140700740740e20b030f400c9801110181c000c02c0020308258280214070076000041031410664229040c1c5078503003151100d07081c05106410550041050001c2806481d030800710444040b03245048048020784544100c1440503800d5283c9824403580130080001c2e14000d00a402c032440130304003840032884e126401 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 274662787 1250 274661537 274661557
    0x2040b0402071b08150a0506010302120703050f010e06130b2d03060c03070503011502031c0e0f0c0d15060b0c031e040501092d080115050f010e010c0f021005 69
    0x42d03e500010110b00005400800b61500c02d0751036001c0d100c5052010140100030030341810b0540801074107848600b1195224130903003507950b002078030b03081210480440c004c0c1a4001325140100c030080c800c10341c3d101440c400c01034291010009810717968102190302c1c04909010040180400c0a42d0084014048510351407100300f101922001c0e6191400c0e001d00340800c1d5554000200c040c00140310f202d040442e07a00483c021801181d00340f40714000d102c110406036190802040f1b840700c00306810705034200012080c150031100948000d003004004920400c0b601900075140c00a01903404640344a10b070300850190504490060350340030905815a41c030b45c00700c091000c44842132141c2000c0303550300801b580c0a444051303440c8215285890440d07080415000b50300c1c0c2c0007501a035030102a07540840000402000c070300b4008070381e059007601c900410306001e502407402081420700c1d60b0070316a4001e100d071005000c242010b0080c50030600344080a0100d41c800290080d1401f20100701480c1c004000c2c188201c0 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 274664037 1250 274662787 274662833
    0x4110c01141003050a140f06010f0303030f0e0613020406120305030708070e090601051b010903020706111912090305100b040b011806050a021204030b06041104030c1202040b040207 79
    0x15a0362007005680d00340c1c840500285c000d00340f01c0001801c4450b03844424440d12084030392500050b0100f43c1071410030b13842001c2810104000700200364040c001c2c0c000707602401104000312604c00800b1500d4a00c000d008115640300c1188040455581d940100c025000b00c04000c580e0000301c0c50040c0c020b074001d844090100705a0070018a0180c4154540c9810b028003401e081c0154854030015641900601903100040301c03503801720301e8807040903c07440295500941c01010b030303185000000b420080784604652003540140d00075500f00d0170740040b1070700740715840741e01d4002e1000400412a08940c8a81005040d4010540d482c0c035100327151f81104083c420121810451003002c0d00040d01d074058240b46020f42442c030300d0000c100b19130050703000d080c20b1500e60041d1000c10b52039951403071103030380603400c1140c4822044081c041981054800e440c66031140c810131915241c20341e1900d05000c9a244101001c070484429200c046488036040a040580043e000b07644805451514054045904515000e000 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 274665287 1250 274664037 274664041
    0xc1203070e030a1106180405040f0b07110714030102070506040305120c0a020c0904030912140d0309050712061d010506010e031b010c1a100e0603071d0604110c0114 72
    0x202d0085207459030103500000d0445000c1000c010b2000940201c082044600c20700c1000140c00e0711240120340c8564441c030f118104a182c6482c00020040c40034001c1010440c05115000c40d00b4400140e101c1541d1a02040342035400303c203000640a4825440010014002c217010b00041580010260030706050006a1024030f07070710b000e0700c00d10034080c0c0341003034005074003400c60704045050500b082900540680782c814010703612451001e0f1010308800c0115041150760051403007950050080300300301e0303089140078001d0240341d807100d03962021140152a00c445165110340204120341e4446116030088188580708003441070305c414000e02d8111071a82c0403c40c60002070440c7c0c540402c07034034080c080400100c400d08049800440311425500411140204c141003008911401400e10a101d03141c282851180641800303002c4000b62000703010706020354090442032254584002e01422660460201101541c0e20240040d015143c0140c94410842c40000c0c0014420b9040d008050501080c411800a503 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 274666537 1250 274665287 274665289
    0xc06180b0304120503060a150c060612050d110309040606050904230a09080c100203090d02060103030207092403060605030d1e08040f0c120b24060f0c1203070e 70
    0x41c4821100106200118a20200c40c140504007540e00440082d003405091926914a001c0c0703901c584244c00d0108043c40840c0080040902459000d0040400b00a182d64000d550315a501e20300c4403417500910404480c41041c51004206a0341445001002800166610f54011306036510400d0341c00d00541c101310812081c200c407080c150300b80800c03103e00040c4580d210752540340100711560b41200d03001c9041041101081080001490944510a00580c0d80c2400d0780c8003460408804d003c40255000900101301190300801c8403411100c1c0900046244150b030448018107a00044214810100004000c0309001041d400542911402d4080302c2203030520120582ea403211402d1901e01548070003000d2407200780720381001900144a8104240d1101e9155120507001044c2c3d08520a9030344105885d80c03d0044144250303400030b40f6980c601d0141841405500703120110303428480e0003500c000034907040b5000341a0898900408030002d442810744c02005140095005036285800991403812031409 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 274667787 1250 274666537 274666559
    0x90a0209010f050c0102042c2a092b05121606090302010b12010203041502160233040503011a0603190216030f140313020d020604030c0618 61
    0x50354105859460720052008012034566020300559061550284400074a00790451900c1c21a02a2320440c04521100742c0d51311580040c0060019180d10380f182420145215005450940d9070001c18800d40c0d0342309207401261134070304055400d40d0392103920300440921800109550600510801c196940340300c03003000d1211180261120740b8604100c5030035101c0060000d07400130781458403900003c55242c15160004101a00c90304c48008165000003c000c01c00825281d40400d4500c602c004500b0003059200c0c03800c0d03400004200900449d000c2130f81da0711588881c0c0421040341842034103141452480c2031180f803035401910070b5a02030b600708020100e4071a0203941c0c0c0f50700041c0103026142190351f08904040050401c0c0386691010303a01300041441e0119000442048070701a48440340240c4680c0e400030000076196851041b03444e424024842150605600858500e40442d006001004140002552441580c5c40203040030f980030340019200d50066080c940c00d80300042e03041000b941c0c654003ca8 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 274669037 1250 274667787 274667797
    0x1030c0f022d01050103030207170619051302190801051302030303040b070306081b09071e0f02010b0405040b04020315010e0c0f0919051309170a050c06010e06090a02 73
    0x1d42c026907074041030700c448200003107100108055807510880c5598082400c42d90300380c00c10740040e0042034091001c0c440c61100080c1c8005104010300d0240b6090705000c05441c501410902c1140d100e00106031104650607001481a8004010a0030000800724141026207540b080240300d50808000801208a071300c50302409680283c00785143d0303603035983c2d04c00700c00703000601c0c4000307059548001003001081041003100f981050404188424500b5041040184006242104118010581445a06144480c2d1006042d05d0402003a41c2110718026809003a00700100d5800900e040200018040d07200c10040c0503e0082c0d064441d0ac01c00d158882d0840e0380d09005050003000d00348003041166141c100105500b212842c6840c0c24521910002000f40c4102c01c00000381461503d0188214980700280c03081070702058000f0000c0c418513549900000100c0100e25116031004950313004581d01400c00c44d5000400300d02a2402980c64200c2030006640a80b00c03180507031516800202040550702c00c8503 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 274670287 1250 274669037 274669067
    0x209030f070e09100218010f090e0c030f060d0c230619090b12061e06030a0e0601080703020f0d0318030302010e240402282301080f13020a0308040b0901030c 69
    0x7806c2d04c900c0b00c0054132030075484101401000041440040c0d95811070b039905010300c2a00e40095505c2c2001ea601c170344500009020355200e05600c40703c801c00907a5656140c4216200e0000e9618840b080f03840307a0baa00c202c030b095003c2d040103000400911a03070340d07603549000103480741d1101502162112541c510a000e02d00380e4054806062010558900e00054042408807004050224209000c0701050310350b0019601624807a85504140c44064000c1c06400d001d000e030b110007001000e2840d000110b45a9003001d546004002842c2041c0a26216030a40d02e84054130440d0310100ca95a4500240248031280c80700c2c42600a03a440030b0b115804480011614403107a1098600a0311180c080080800380800d900005083c1441d1400c80d000c05c40400300020241d1484c007101c8072070310880b0001820341915030141003101d118200400101c4101c03003a508104444000302d401c00040c4042071343c0d00015040541500400314000900307070b6242e401000c01c41c4081c2c0c2c0505c59004601829200b140a2900c20 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 274671537 1250 274670287 274670317
    0x3060e070b1204110d050303070e0913030e0307170624131805250902030f13151a1305040209150102071e0602120c0d030209030f070e091002 62
    0xa00442d01c0148607038105010b00481e64441409800003444030702c0c1c500045440342c00100030044031a400c01c50f50780042d4400d8941e1426460051060304411060110040900200c3c031041510740e1010004200a01035511508070b864a510380c00c0781d5a08404ca902072001203062240042c2c011010402101c0c11a01905603484106111540000307001915800250301850510840200340300b0004070840100d0f407900324440c0c01800342c0c405030402c4260805001c8500400c10f000e038101d0f2a01c00190310104c1030b02d800503140c0c52407030030300d02003000b1401d0000800d0611052038040d03a0422800c589810301190031142e050303600300b01c51040d501c003268003030760190b40721000a0111030076000d0420b4601052060340c000c00e4449000c82045110000c0150050450580038441746d1307010081c0e440300c07280041d03215007061880610507075a4a03041d01e0b0f00d82056004604840c1e2030300c1c100005e07040d8030040d900f070340c070050f45401152090300000c0704d03000e1261003000b1507000d45403494405c50341031052901e02 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 274672787 1250 274671537 274671547
    0x80703140c13050901140408030a06060203070b01050108060a08030a08060a1502060403050904060306020f12060105130b070c08150603010c032003060a080307050607031a0d170d090302010603060e070b 88
    0x61640244402020840321755282c0c404001c070702d050f40f40d40c0b03441207201e41c4083c1c0d102e08142e15003900300c4e0001d80050b001c0d54000c010040200e90b00700c1045046840034a404401c90344e172000460650615a88480c0e424403020032014a2241c1121070a8400e10040da92291360316524204015030000704001c0e900580c02200102c0e01180c4204002c083c20000070b0008a1034550781c0e902c55003281d02c03002c400304003041c0104144c0f01800c05070381e0390742e0880c0d400d1902c01d051076102c3c2010403040d032107481095038080300017a0131400c02010700c810400030300503807090310390b001ea041c4020134580008440d410720075440c000490807050300902c110042070104151200604034142034052042d44081c0886038403040e9000c002404040070802007610034030440107080c0a040c0014082c1c165403941e20f2030303001a058034080342c40e90303264550f800c04483d0700918842e0128809101c8204544101c6d6888a00b060400649000b4540c05400000889224081c100f04054126440c0d903118101805110b91050081003 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 274674037 1250 274672787 274672819
    0xc0106050102060c0307210216030201050a11070507121502040306050708010503120a0810080a0305300a02090f0a1e0815010315020f3103030503131b080703140c 71
    0xb03100c1c1f1000e11100300103140c55042c8100c0c6c280c88558040843c0183c2d195010007020349550302481680d14048450113041050591351143c68400c1400b030f21340c600d904d182034803051044200c12541c039101002d030b0855585890b03040c428054841180c42c207000c28a404000151418001108030040b20044111400d29100d000100c40d12040900500c0d9030002d20180420320040600c00503140d680310340c5171241e548014050401d0900c0b184001445100d0007241c820114418205450b60b010903040300059448000710005000c6131107501d17038103401401141c0b000c20b500014000f10901c041c43c001504982c10b40d151051540c5244a01d9140803035a0540010000595409803400800840c4000541000c04002d034900e403079003155185004a00124031070364118492400003910541c1c900b0308411241c0c2c25910060020b10024003c2e031002c466100c009070030310001508060713a008007032410107191590b9004003131b074510b03140c00162064601850b1000d4142d0700000c900707000c0e03c0f01a091800d04c4080107 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 274675287 1250 274674037 274674077
    0x11010f021602030d112e0c0503060102190c15110715110c18100902120a060801020702010e060904090606120302010e0f06070f050d0c09180b0906150f0c0106050102060c0307 76
    0x130f01040300300e00c0c40b42c030b0f0004200d43c83d00903811f8103d16507076041c3c0c8034540b06000a2a01c503a000105440c44d02225956001c1018032030080141c0368070039031060b01e5041c040002c8070301d41804c01c00380585008080000c02c4584202a0900e482c3d80c003940c0c3c0030100c414500d00c3c41c1d1600204030074142d000712401441149d01c0100013110f5800101c01c480311b224140c0d02c12559090b64040001171103d42d0990042152074a068032030040a00a510000c6013045405d07030018000c0401c041020744030b0f10303021500c680340740c0d95034100004072540110240482641c0b0817000c11800d42c510000c82c0954205040100012400140c1c3c01ca1402c1e0a07000300031540318400161072070b0a030840340303000b04281013040700c4c070f608040e02410303540b050b07150340e443c00750b500d0100401842228a0b08102c881c03824100300040c281e4501503015000f45044a019410f0b030503c580082d150703c40d0a40a00e10480c0c04102d01901e07003019440242191020f0302900c8075a624101e0400d2035200413141000030908503010404089114 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 274676537 1250 274675287 274675333
    0x305160b120702280209130305120a180807021c0c0303050a1e0806131104060318020405042009071b020d0209090f010614030c0111010f021602030d11 66
    0x1801070301d00d00c20b0683e281152210203007030a00c0e07481404c100321000b1810000b5105910441c1030601030755402c15560000d000d88680d07042c2c40b110408001c0840c2420350f80c1da0080440c110700020304d010205461412440a801c00030040e4880c06110462031100c1503200b2510108076480000c400119042d0380e81911560000d240c90400c20026080001d82140c01c0e00e0400500c541c01c1d20b4a00c0c840c0f800c40c042201041a10181481c1a4205800d4505042c5100309036819100079040109040481440841c0280c2d04440069441400c0c44c003440184442c403a0007440980c460702c640789a140a4100f030101010080d190900000c4240041c411418040040c503181248010030714008182c0c030b03400187c2816000d503050001500000449200074400344100382c001d06440724030004406a03000080e0301c5007030010149050269000c00b442c0601401e6100b1940030805203421500c1d8001000018000c0b00340080c00c1303002c2e2056002c2005254040c504106080b14040000d28a403091083c03480c4001c048 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 274677787 1250 274676537 274676551
    0xa03020d11130204180605102007090c0f0509060d0b2205161e05031008030d1a09040f02041107020301050c090a0e04030c080a091e0305160b12 63
    0x84a50400542d141c501001c40200790410240c1c440b424400420351581c4420711524441d03150410410090300e62031a418040e484038280002040c80c42d4260911a1034071005094850089180c00b0451180750391203802141e000f591060004409042c0030f83d410312420010980c0040241304007000c180068001000d83c00c07014104e0704910100804840c00c014810780d00f07a084c582c0b202c00f0002c039403c400f103540b03107008014a4001d10180d1490200846050f4031204a01007003000000180d0700e00090380c144c401031100b08216a41d800031a44683d000f0040008910705185507032200c51051b141040034903001e590009400b1300300f9045a800c1000411500e40340c014055001d211031400b40e9001c0c4950f034819607031850340a517140903200420070420782a412154008042900f40070120740e01c0310004000325070001201d13640304400c140035140400c00303070300c030301e007a501e00d102a80074035007200300c4420840384144211111099030002c42c2c2c006440301c0c007540c078100c2c5042c04410b401c1d040656280ea000f40d4 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 274679037 1250 274677787 274677803
    0xb0114011101050720070506030a1113030b010501180509070c0c08071211040618020304020a0f09020a031508192306010303020d05030606030f061305151504050a03020d 74
    0x20845841c0382500d8044490802140c01c2030800180032403010118091071034403501500001d82481d0000d481c9010103044201071a64401c1074070030003071140c03040740c49480040c1e80c400d102c1966454241e84a00090151500080b080980081412030044198027640c1d001041d501583d175075540c04a0320044400c40544400488850024440310207001031340180c2904060840e00c071149040c00d02e03486005003d40c0b80078901c0c25500f005494607544114240074604000503a59868500001700300c01026040501da204c0c3c034440020b035046450f8010881c00d859a24148a07004000b40c0721aa00c0407540708603c3c403a0400d8410307031694025000d080a50b584580d015189008140d0034010741c005880d205442d055001b81c0c01030090640400800070714041500d40686186407900209245002c0545506803012107500410303c540c1d0b540a0241e08100510020080c903c0c1c40000388a040c00d01c840514000c44049079514400d1480b01c044500361040070f0310004a0a2a60f420310002003d50002a50444 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 274680287 1250 274679037 274679057
    0x703170d09060608101b0903140715110f0703021003020c12040603091e08091309061b09050909060c1c090303020904060e1005040b041d0d02070b070b011401 69
    0x15600c0c803c0c41d0107000044010715050026503440b104580082038003650869807012600d8910b0360040c00c1000380c0758440c80038071001c4640c000003483c1040c4d60b004168940015295011050380c0510503035a0304020b0822204112018142c26403602d07124000650010101906103160f94002c0c0c0003851054401c40445140d90140480e006840e08103412101c0040c0e00c614000b0140010030340034141040700711885c803002070083d07502c5480702d10414100038001e010341c596440341c0d03454079481b40c2c90145c0c10001c20b001034030020304c0e0030304d40c94a02c1107031034041007514001080c641040b0030b40340d10803024507006101c99111111411b1564012112090400800c500700352022a07050141503112482078802584800408040206448840d049015000141d5041200350548060001c08480382510005022030540c0e000c6400303000101c8890801c02110398035a211440f000800c8019000300340d095a03042626180846150300c51003901400000720103006016940482c80d40007110841410584411 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 274681537 1250 274680287 274680293
    0xf060c06090d030e03040e070c020609030a0c0312170f130206160302060a05090c01080901020f040f090501060c05031b190b0a0c11072c090d0e030703170d09 69
    0x200c403045403100c1064104075004426282c06000d040c550140c0c4402130b608241c18814403141c222402003c403070400001d0b0454500350b4640c1000c940c403602028054038039050315820420741409080c0b20845403017038401610f900144c42803440701c0051009429100040d214901801941c010140000c8590310130440f150340141e5640000f4800d01c20380c24440910690181000380c2061401030100d0940fa06040c10810ba01c140070031114900340303007400d0086060719003840c02802801030413064540b2003c001342c042040c034080500761003240c010004c140001e030307256070084030030020865000703140e603006100c3c2024607041c000095203458407000c103c500280d488145200380020b015400c5e12810302c00f00c00d100c0e203e40203004219800089081c05038000d403401d000c0582da28524171403090301c6400809078800c1c03030301c603000941410491b072115030b4214248031070015151a192444080401c140e84c0b840a4a420b020600b00216600060b54400110355a5240642603001140104031280c0c0d40740388d0000 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 274682787 1250 274681537 274681543
    0xc01050315040509102a0e01090312120c17100501050f16060207200307030507090e0c0604030c050a090902060a03020918010e0711031305010e030a05060f0a0f0c09050f060c 76
    0x20b003800541c1016103c0411b03640e10b160214202c8228100300e00c0d4101d000c0700b41d8102c440c04003200d030b00c08002c403584241c030700d0115092100402c04600720b0742000c022280040d4444d60000815403a4100e04206807556208080803210500c00d1030f000c10010f10070b800040f100c0d00007500107110169007041400c0025034420301241d002e070a084648880e070140c291103580c1500710302e0048440603402014114199101c541d0f450700c1c50f1250150540c0c44000b0100c1e81c80d420700180001070f0024000f29108c039103d00d40700700554114001c82e4020520002d000a007001940036103104660040c159030302e410800107086000e0360201c1c0340b094101c042c1404c80d0a5048160030348034024860490305906d81d04000c03700514003030040c00003070f400d079105202c0c1c0c0c81402c409a050303c04440302403c100c4042c0d1421400321f0b09200c900503002d4514000d07001040701d02c24180b4080343c441c1890751002c20220090a0a403401c0b69840ea07a003000143d40305e1814449410046c2640082040050444d0b003002580340036645 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 274684037 1250 274682787 274682801
    0xe130201020a050102040e040c080604030c02120c12010906050c03131709130f230a0902190308030907051c12030e030c0102091305160c0807080f0702030c0105031504050910 76
    0x40103464008100c00e01c0049e43c2c100019046d00400351010382000d4a000b88412403040c40a0320a00c92203421900481c02005141d00004010b42001944400c030300c02e41d40209100207007030314800d013490b00043c003203020101224400c0340c034805c40e03448240503901c07196240e0103805150b07903d0300f108001c40540c1d5652000e401d105016a11400728200351034007231090a64843c02210b541c2e202c926001d0604407035560411030380c4011131100c00160354645000054090008045c08010080480004401e000c4172030b00031071040c0280000c03208446e0f541c50a00210342c4101c9042c0c8000e42d5000112400283d150755410585520351034003141c8198990085130940c1d01840807225983e50000340b602c16401e0150fa81d54500440d55010000c0e854161001501e403003080080c1c000300980c030030083d002c03c40020150303144684c100401549440b49080151a01c0d4060f1038268480d100704090b40c65658454401c40e442141001d15121908407a501030101a10740900303240c207540078290304807211030f416200b419 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 274685287 1250 274684037 274684049
    0x80a03020f120c19081003110f0d0507090e060f04110d021914090f070c0f05061003020f12030a120f02181201050705122a0415090e130201020a05010204 67
    0x240e031500a1140e80c00343c400e80340130b00d10a02070301004100d075181c1039035581412680c110110702252004640080e10441c2e22480071503200c19100d506100380040040c14405031100c14600300450500c0d00e40b102d1740d031102103400800040c0c1e00b90015000440a5000b029505d0300501189062a680d40c0012411509400840c5816041c403204003e0014811240c9000c0402514224000d08248005103000030000304038030148040c100c16801000b9480030304e080c0e1103811009842413800e00d405010120442440107a03c100583e0303807055824a401d0320b02c1540c3e00784080003980f80100390704040c1c5612100f001c2c0012019030b24030540c01905003500082c87c4008004004601e084d0485d8100462a00d04014442036689018100261660080122104071782d040b1402d1056507a81c2c40e14000c01d030382c81080c0305204200e02950720346502806025000749c54244256100344904070b03e08403210702652003020719081104d008903181c0003040011180060043c81903c000d22145e4486a003603a129900107 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 274686537 1250 274685287 274685311
    0x918010b03100510090902150307170f010905010902181e04050c120108030f0403150e1507021e07051306030b09060403020c0114030612030405120a02120a080a03020f12 74
    0x451841d042c4c4030498040c0c814030804002100b05c40d00490206250603080c401501c0e07000020480d12400380701e413803140c0e500c1042c1b50a00c1d4903142c499154054000e110b250032040c1003200201d504203490081d290750400c0f80d1082050b00c8020070402401580070b0000c80781e01018904404000e4030386000d030a01c0b03413101d83e0015540350060300259040030350591110450340c0040c406015600f08000072034048079001103241c0b04c402070460218008100403010303600c40c1c5c0f040e0040c0704c030003010b00304a241c07240403d5002e0b501402c01340d81e240324640e1000421800181c100410030312039442c00c00c2c240f8545030340c0007400107101070302c950b681c02c00070605035840e0300c03141c2c061000c200c1095030400c858500c03107000b0701c2d004400c42003ca000088600005e014113205910030f00e00310122241c00c2066800a00c001001801d4000b003820415860302182d404c10b9001c2d40101c6444080c0e1000080c410500c0f5038019201d501d0480d0810301140290030620100c500c0701010496540c1804a90352010700039030040661b = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 274687787 1250 274686537 274686541
    0x60609040e0714060702010207090b030c0402070f060b0a1a0f070503070b010f050a06090b0c150c120c0a021f021201060801060f032c030f0a0305011806050918010b031005 75
    0x1c00b150030f15800001c1c61041e103003006501c0040c0d038045804804c0b2050442e002c9182c20900d00000c0c20084001c041d260090300c0403801d18148031000f4a441490703405541c042201078480030610003c0340d054040d00001c000e04680c0300d110704914800500302010605c40301400c00c034032980c071a0708542c400318040c1e41104013000140300f80464a0800001000c040751981c030658070b8210040d0000710544500c50303400c203012030f00c003950711814006c14190010343c00000c2d04a2501c04010b6140c1d400c00c00c0c500c94a01c45510004090070080012503071919150307002018040ca50004e49600d00b04581ca490b500715400f404003030514400c041a40740a08205c2d21600f89075818003e00920400403204030008140c01c1101541e800010200c5680c5030007022007800c1050f4030189442483d40c460011880c1c05403a00180340007029525a1156069501007100841200c0821074980309031085409180e43c82021710000c03460101542c00b4104000c8002400841c04c0b00089002a0801d44404185d8410940fa207003 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 274689037 1250 274687787 274687799
    0x70c0b030a15080102031005040b0d060608100b0a0e01030b0711060702010203011401030b0a0b0a11060c0c070510140d180303050403030516080c030405030c0604030c060b0a0b0d05060609040e07 85
    0x810342c0042d0a02c04002c60541ca404540032103180d4040c40b03007900030b42d596480043c41e074a8000e500301c0c80310b40140e41071000b0781d52410555910f6031500d8500002c2840c120900d051480c24001d0301044400c4600c103a800b59003103031280c5402c1b05000e4a40c40920200310f4803501420003d02405104003000e80005032203624040f0522504003100c44140c1c109890300816007160b98941060f2000d94260108898843c2039948041d80c190001c103a19120390302c580010803032440001001819203a41c0c1905607003900e0b40e50420704c1a00e0000403103030800703e81c85180c0c94903440440c0d405407484d403880d00d90104601064070100c84802c200c401040e80020b07161300c00c000074140c00d406041d070400c10301506a400c05807010001801c500000e005100b00c03860000100e001d2003c10420341d807031344445209561142c14a0701e0081d012a80c0b4040845403035003000000c8010b031615003181ca08440048904c18a0b206500c503e01006040042030315074040014000d1403c1c40c0c40e203100e6144080c0b109002080c0c01c80c100300c = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 274690287 1250 274689037 274689071
    0x20c0304032a2403090303020903030d0b10050c0d21050103050606041109032d010e0604030306080304060503060f0d050d03021b0c0f01110f0a0f2312070c0b030a 71
    0xa08a81e2104000d410841825210383d4802c030740080301071400288a010301d150840107442110281c90749807001045416440d00c4940c041f40100303000b140c070100200003000e0181c449014100760700c401c40e00410301c1802c006008100c40d070100e0740114005884041041d000000300d500a03007046d18290b00100400035142890712603207002c4031003100414280165140001d0b80d032103082280c000e074020740701a03140210298400300c845000c4450000e01c0702ca0f10045140c3c1c0c1d2454110f030300303800280c00c0501c00a08803501100b102c058484950b01d113443c540d10601880700803a500b48085030012400c4664201150003400b58900002c43d50741c000d0f075198441c225903101807140126500c1c054214009480d8207589441428220090078282030310f0058960551504000064160040c540a10110402081080b02e0003880c0c80c0d1096460081c0341e40c1000d10041403440c01c192002c0c0aa00c141d000f458004001400340540500c0345100ba50070b40c0e29000180d05940044d10314907000e980384c00c0d06c0d2424001038 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 274691537 1250 274690287 274690289
    0x3030509010e0f03041401090503030307081e07080f07110111040602011113090504020d050f060a0608010c090e0c0405040e0705010e0d030909050a1b120612050a06020c0304032a 78
    0xd84001d2018283c2a40751a03100c0c451072140100a050701d2014407000c0c0d02070156080206801401d498907032800711409003903a1421034803a003521080d5502c0d000071302c60301c030106400740040780d40e050490394815054807a401c0b0080c0442003030050084d103010f0080400d000b01000c20f4140c10040391524548274000c2d0940340c0c1c5440c1000e2404040c042c9070a040d484850749411106025070204968079140041650307008011400f902c2d5000d211700c40940c00c3c000007039841c01500380d40c50030010503a0750340c500d03130890300030b441034800050391a04100004000d0403030407508403145254443c070b46680c40740064100c44070b0419441441c0c1100e01c00700025a00f10f01820b032030758000d90340074502c1400c603a8014503a003c0c60141c01242c1c0c0c1e50780003081d6199000d0340140380b208000d01c502c0d80440c000110262110142e80d403001882801c1240c0411126907001426041c0b6a203e0001c103141411651400c020f500412050400d621051100001050b115200c80d050303090503020354901010921100590800302e = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 274692787 1250 274691537 274691561
    0x1a071707020106080619060810090308061503040204240f0e09010507050304060e0102160303090203070611190609020a0b0d0c140406030c090f080c0108060312030f07021006030303050901 82
    0x5050f10422500d08007085a40e44580b196007040720b0075520860020007800030b5003101803e803241541e400002c0c0d04c02e034000d81c0f0480c0070792200842d07036440c2010000207010000740061401418404035005040582020400f0000f0042c1801681c031482e010050b001c807550f0003c54107000c000c0041200d9108482c0007500b0003e400000d00940c5004600a49603100c064002003801da5141d030320340c40024080d81510110342d80304800c130502d8142801d00601610241c80242d10a0080400018500b80528400400292080040c0c0910700c038400c1120701240480409a484680742c40a840050fa0b030440040301034105066801d85504144503200200c804020240051140d154070208010050750191030460f40341b4070300400d00b0f02803400c045031420480ea1003100320a00009010035a600c3c00b02c0c42104051081c0e03500041d41d07844404160313440840d400711003408002080450b0a03900c00c241f5181d4410040c2c012507070718140d1443c01100300d0351f6030740c8150f002a50b00d6081c440071003800c1c01484007100d0 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 274694037 1250 274692787 274692791
    0xc010e04020c0c100c120e031e060105061b060406050906011d0a0c05160524040f02090402011b0302030a0917060a050a1e090303111809041a0717070201 67
    0x1100da80202d07900c04005107030a03c01d0440200300040144161041c01c5030075400050300c1c2d08006d0940010341480c0d407003042030344203006607499030130700784400e8041600c0310158030021302140c2d1071720040c40b08650000684440d03d41d50361800840481c0708001041c0154441c110000c1d8a01d4403140b020300749141078200c0515500c43c40d4005215882c900240d039000400150300140c0e1503292241900e5600c62050100c03083c03805001c024051140114620111610144111100402e403698100c49004100c03801010b2200410442c405070802c0c0d01016400761040c1840071000f00181e45001e140c000d026070440c0180e00010f007002234140c1c4285018010920f00200360389041c48407203800c1d00c9080003814440c2d559a80e500042214440f504032013118081c20486503150180d00d0340000203408401410790109060444841143c01c5075011941c598030703060708410040310364004102ca400d5029000780d65800c00e600c44000f5003030101c200e21780070300701503260140402001700800c82101c50081c480c03c19a4 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 274695287 1250 274694037 274694047
    0x8060702060106031a09070918020406140f0c0601030b01090605010e010c12030b33031e06010212160209010501030e211201030b01180c0e0409150c020c010e0402 71
    0x40c0d00014054103540790b0381004034603240d00c80904c1c0c940c1020140000c1d88031402e48140701115030424400c4d0169251982d04460105000252400f68410f901c17840c4005024442060f0300180e03903101901d0804200c82400f40340c08440802c00745018000e070801d44c1e40782c40007801000b1036220361103100c0c01401c003820f00c03a84c0640d051002030660300c0c3e40d02c1c1c0035001440310154041040d00c00d40c051954890000d050345117540300c0c1d0043c2055000340d5101d40261450f0055114101d000080c181ca00c00e20b501031000000322105001164805406410719040d0300c20b01801c0800350004401a2407507a441c889601c11407006801000194030060340114145807400c45440760244020446010b40000307103801c20001c01032003078510748910480308031a45110309140080104028006803c0c1215a00860f04142003980c0318900c0440d40300b00400404500000190340440c140343e0007a050090042107182c0c1c2c440d181034401c0d02a98071600c2c1140c0140c0000e07807407060302c0d03801ca15040e840b400d007a07504604103 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 274696537 1250 274695287 274695301
    0x1080411010809120c0322030f0210020330100b09060a12051017031303170702040c080603010f1103060105090d06020d1a0118060e060906030f04020a0806 68
    0x395111104480c10403142d030000450441c01000240072410583c140555180329041e03c00e81c8a8001c8030a10f03800081c5030262000030241101c1e040c01341c1c1c3c0c10581c00403a80c0c0c900d900300542404550590130a60000344020310701c240d0030040c0414000302c1b12115003a4910408400c411201000b040041c5003800f24405003c2104180c05407050000c09581d410b9482c4540b0b08251010100600d074000400d0800d000c1003843d542c180040030849407038224940200da06d40a6542c4c5034000e090409100b0002400c00b040440d5511310840385d00d00800c104140b811845070045801d50703000c0300b110030100e00a1001d01469080034032401e016407100c4202005040b42e80084580c05100150405040042c0840e1543e041e46d55110010b0b080c59000c0800c65841090318007010241201410000324090207100e00300b05540181040051007400c0c0c0d10146100d81011000c1d10204c101c4684150807080901c490000c43c3c5482008600071084d018411070245000e01c1000b0303a01045030003841071504170600340968 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 274697787 1250 274696537 274696553
    0x30a0c2a2f0f0307090f0605090702030406020d0513170105180a020604090203060121060f050907020c1917030d06080a0302030a0e150f03180d02071206020c0706090f05010804 77
    0x1201129244140b400b000c000a00e080444c4d00012245403402e004d0000030340d100c0d800001242d01c01e80c1c8000c9166501c0c0400e90320f0380110711944025070003551810340300901c2280105004050346000f00507442e00d5120802450440452410740c1c0e030341d50b80074000d840d0501404250341ca030001000b040d0360700c0203502041260107540300d0703202c0041e00480171641603805440b089110140c072609042c1c940d0302c101080310283c80f50303208901a10a0103440840d20b810140742c5140328100f40e40050810424003402d11100030600100d80c5080072007800e001c141b032075549920700c41035907150313001711344442c42d006242c81150003d070310550b2a5400032000500094004c42070f0785024046003080301b0406100404500040c1d0010842801400001004441790070440302030750040c0658141c0040410303c0080323950742d4502540802015900543c3c00300b16070701406207a50001486658050709048210161602d005010340084011810b000c0003409a1807205801030010304003440c0c146c00a0a05d900d504070 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 274699037 1250 274697787 274697873
    0xe0105150304081b0a03030606020610030f0c0305031b1603120809010b0402040b0301060216050a2d060c031112040b09011b0302060a0e060408030a0c2a 67
    0x40800700006090040340f100392001100ca110300f0080c0200a10941900c0f0180c1031000c402080c0341c0389002c51294400181e45110381c0c01c0042c03201c491420350700c3c1c1708100c0034620070485904030440c1005c00003400602c054540650045950321603410054001401c129150301440442c2000d07110401c08100c0c1044211001103c90906118580b1410b000300d0140c0380c8120001d4005000140000e403507460000214100e400c20340c240d8400f41d60003450704210701128841d40c0c0c0c1c021001c1000f401107000610700f5140d4100b030f041003581d2034074125100c08004d803600d9100d000440c000740010002e05030089402e0304540e850304050030184401c1c044509850061b40a200e40e40c0102140c00086a409084419401410505404444a943d19000303658610440300c0140050402160100d5260000781c4640210380c0040301c64115900c6940107401000145c1020f000c001c061003902608240300d411300c0300f06c00b00e1075210036420001800d22032806186170528031020140005120040c01006000c82c1c = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 274700287 1250 274699037 274699069
    0xc03120910020c090406150e040f03171501050c010917030402040b120a110d08070b0601030c050a0c0f030512070503160c0b15120d0203070c052413030f060c03060e0105 74
    0x41c0024106420340d1f0040e100d0f41110a1722210134090106211010003080e40662181d03580090b2082d1400c076040f0141015a0403098010440300007a40d25030007040030302440b5600314000540240079403100d080c0c05000c81280e10203100d0000a01c03041d810a4003500c14207070400d07070700b10a0011121500b0766480b0380404000c1e141c000c8000c4524401c0d5604141c00c0c00440e0411240d81e15041141051000e0034010303030300380d808645000e0318500d98a010780c00352408050b41e5180c06092099580b80c00c18070b900316130b00440403c18100181c10b44405105c060364095011995030359202c0ca4508110a042e000500b950014410000c0400002440504140390f00440d142085a0f0150718071000c161501c042c00c45114240c0a16480b41c40b038581c2c000050a68039000d80003162400740d40b8814032480500390822814100082420a04654101001481c43e141c008109410b51940c0351280e48000c1d503007040c00ca4505485030024606541d16000f21009448980b80340c0d44d05524100c00200e40100d108146 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 274701537 1250 274700287 274700291
    0x3210b0312070c0b09010c0209070509120c0a1a0403020a060c050607090e01212112060f0501110309031506090a0c02070909030309020315010501180e04020609030c03120910020c090406 81
    0x5217542e034030a00761401d0050f80a07040c14010308281001070000d030080302d240c0740030710b41c0380d0811909101c002504942009000d8020200300d030038061071084070b060901145c00104000c210010060301e41a8198008208a43d159016640707280703021428000042c0ca071000704a1101c00c01e000e140c81d40800e542c1150b00e444900f030100303882d6a114441a2160040262100d4558100380b40e145400381a94881074089076151044080072101c0802107800502440c46031a42404042c04594052070010b800b01c4200c4e0212820050f030100003038600004c01d840422030b200d0110900ca214100300b480503400000404090098800000b0002c1d602ca0a5108160700582c4804103a007e2500951140c058244c02509403501c2401e05081404180d80a01c10b00c0d00180458088500e0600b007600c9076000d41c1e030300408800e2035458507020042c00b078100002066050040120409103a07074200407400261149146c61601c43c0c0c0f040d02000003200d012000f960541d009859032102c180d54a43c4020740c007036404100 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 274702787 1250 274701537 274701547
    0x7090e15040203210405040e0f0d030b060403050a060c20060a020310080105040f0203120403170d0225060c11060f0406020f03010305060f0a0908070b0403210b0312070c0b 75
    0x2038500380040c1e501c2183c41303080b504101c0c0701e002c4150090060702c2042d2000d00a03c03008400c1c1c1307661162038a240350f00d03981090410a90036840398010900b5620000c0006007403a40702d856460405808203070883e18143e40300c40707203d451500101440d248001d0070402010100c13101034219110980140640c2d0f110f40d00000181c0c2160b038030501d0038060b0030020000c0116140501e024000d40c091864164800c0c8035050310000c020104000f02c5065a5215139102c0190100481f00040b5421000c2803e00864081c480c100c43c01c207100c25441910744000c080c2112004050400c07100301c9a50103900f00810540182c4007014520025845400c00500c001c5181c0541d01c8cc14160002d0007a4000d100340c3d410004000001d2100020300c1a0003240d01c440c20241e1900c1340445041180c4404800030607100d070500401001c00d0148008613480340c000d0038414881100880034654611150390f4201c491030f502e5a01c4442410200102d40c001203075000642d2404056846a04008086200340da07200351000034 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 274704037 1250 274702787 274702789
    0xa03060f211b0801020c0a0611030c0414010509060c0105061302040b040501050d0e0f0a0629010e0f1f12060e010b071103010f050103110d0b0703151a0c07090e150402 73
    0x8078460080c040f0100031902c5101c88040316854a03010f00041da8814142900e00c00a40e001d10308481c007405407101194607191911441000030a071a00150341030003010b0181c0707003d58507801d00410700b8903040c000001c1c80d807a10340208441041040c400c1e003045403060005109182d00321040f0b40664000b420030035142e80d2114001405886c0c2d401e100c080a0086188165901c01d00040401501d841070030180405002120a0181e1000c2001c6008182c48200704042c0294052100d201d00b07007001030205c80014611201007164403801101c0034560a10414084a80c294840c990400e9804103100a110b641e203440c509a03400b00042c010070340750310400142c140c2007103040c02d012924032101600a2102181c02d26a10008203424801030301c99000d00c2d00e80c0b041a1400c0c0c5c030b00300c4241d41e0082d21400d560703c82820480090803201c180740411807826402081c00d00d80c080d143e2050482c1405600e58440c070404829050107015480b16040c1b60409002900c043d1004c24441e9444036500d414450a54840c0 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 274705287 1250 274704037 274704083
    0x10f14070c030f1a16230703050319090b0403050702060702040501140103150503060103030e0d0c080307021e090103231902120f0307020103050a020912010b030c010c1e11060a03060f21 81
    0x1031b00800702c1000004080d820103410102641c4103244140c0140094035440800340140c0b0b010364001800c0c01880e100240002e0f000d10080c2036014009060207042200c0e0f98080707421950f081c1c0260445414140440c0d401d9070f070600a04c28400004500642d45614180210f5039480060000405000b424105000d2030b44468040c0d9281c02d41114002d4541341e40c92001c1512544444001c2e40184040010f00f400656000700841031108060200d082507031039912620201c1080d4015045442195051b810f040c8008100c0440040d07000d003190148800c4501c10030490a00c901000183c6410400324030b0108171011098408082c0c084c20049040c0d5605420f0380001d10808011030f62010002841d400c80040550008540030410b0702150309060480c40199000d00000d01d00805241003c111400c0040f207118181d8900c03031042c01e2002411081034001100394115051841c0001c0d0380b000c040040000c2c4558a02c01000a146d82e000300040010401e800240c0561004d0120b10300c0d40340c10719090400c9 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 274706537 1250 274705287 274705337
    0x60807030f020315070806010f21110d09060218030c0307170114010e040b0c130501051803010606080412230703180b0a080114010f14070c030f1a16 65
    0x4d5030341e281c072440c4c0440098145501955801d00160a14004503800d03400f0341404070a0000e080551030070404450180000360044007405600708005210190b03d0140f58042c00040705c0c45010056100c49200200340c000c40d4000746480c4c440c0c1c0c04030300041c24030f441c0440ca8a0031340c1d54200c0c014030b010030441c030382d60701400902441754180c142c0c00e0000a02c100c02c140d445802107100d668203200c16140c0042990b1103029030b0802202242e04140100519030041c4011300715907954400c07000c545a4403400180c01c68030306510180224408808000c100b28199011a040c6103241c10015000d50b203031040e041038903c4171f00d030074401c0c140c0018031241030601800d84400c0c0c900c3c07071002e0100144d440b002c0d8030480b03800410352180811032040000c9901e440d03080280801d05810703551038040c0070404000302d4961212503501124490100900c10109811000280280d0f0140140900091052a00c2d038101035688020303421038a0801c0c00d2100d403042c5a071420130301e11000d25024a800d14040c0700d105603d451 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 274707787 1250 274706537 274706563
    0x60901140d09020612061009030b0114010c14160f0303020a02040b06070f200a05060d05180313060e06091e120318120d0504091a0402220504060807030f0203 69
    0x3c0030a901c5203e01401c103801d442a079087d1481820a0040c500c2950400a1404000e0800c0110700042c012411341382d045940c4000145042a00c400702a02c1d10922222a0805080b203a04a4001d0b0b0880e0b904040706000207100d00000746d0140e42c0307142c400948400c0e207083c0c000d20450301c6d80f030f00209941da03a50507501110382213055044d410070546040f40b400494008009000b40c90b00d040e100c02c91a0901d5140110342c80900554500545240100010180289403101c2d0b08140c1c10300c444208020005400c0411100201007011410000c000d0002e8549101282c8100710420034400e20740c4880072607950416004074026031101640340010180420307800d4891081c03001042001c4002070040840300550400d4512000242d0401d0f41140c480100200c1080420303020002000188120760024070240c450ba68400d000068000002e42079900c0582a441654014540301040009080b0034100038032080b10200f094500e8007001603160300c01440007400711000b445401023951014403901c0c0d030103c1 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 274709037 1250 274707787 274707799
    0x6010c02040f15030212010902060d0506010201090c080601060305100b221203080624120402040921030501141011030409061e0603091a15030105100e06060901140d0902 74
    0x31030f10422014000144001ea200d03803020b0303000d15003420040c842c0d0307110150041c24891400302c2016620014000103000c0310304545d40c0315103840100c0d9050051307002500c0144003501c440e516100000b81940ea018002e0031400910003010480104e4603800c9502072103280d101050844482e02109541119503408001a08400410542019803081d50284180c42c03c4404d1003184c50351050140c103580c2c21080454000740f0410a00d14000000c140d10750f41f140c030060010400b580b4650b1807801d5080021260b10080740158119030390300c0d070036004d111b0140245c038440180c0459000c0008079203a102c0d110714000e0000040d401008181c0600880c2e0140c02003410500503241d031051601d44100c00030a1131102c1b0501a8008503086209001708140340b1b40103064180c0703e15000c42c0719040c101d000b90801c003200c0d26100c100441e9840030f01680c1c0c03140305140d0700214040d103000d8810044843c000c0910384500020441c540c51603800140c0701104008512085840e007824040070002400c000c071010394840 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 274710287 1250 274709037 274709051
    0x308060901061b3909050f04150e0a110321040b07030e0d140601150c063305040b0d080f160507140a0905061e1c06140f010e06010c02040f 61
    0x603034010b41d01404d0300710094403d45540d0303940c0c1c1d6590032580181c40e08152110150080fa0204814205c4500720840030340e8001209540881201c0c40c00300700f400b08030b5151a01107540103c03450b040c001c00000e074890319030b10043d28407403048600491007980100082480701003003d10915100350f002203171724880980030740c482440324104210030f0040d0410b0640c0c00c4c41500c001140e4a10740702000300e01400c580d210303008030040d140e80c0d42d4003030414002c090401c914210b184400d0081140c3c480f00850329203031050050f03a410142444140c920050440e406a1a8209410009001002194078054a0320101501c039034100e1801c0c41d812040c2e01c400f40c00c5114a800216403605030385a450803200040300e00311005a41ca60301d8100750340040b500c00d64000f1b48404c5e00004014060810715020360010407000051803422050804807102a00070303100b9550b10f14031151001505480c80e81c03c45400300d0341100640c98144d851100f100010b01c4d0341d04104e000d8900f80210b40782c68218156000320100240000 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 274711537 1250 274710287 274710353
    0x504110304051e0a12050c060a1b03140c03070908030c030a020727090206041211030c0409150c0c0204060b03070306170c04020702060409021201030308060901061b 72
    0x290000e4030155440d010302d042d400a0020800c0e286820f4505071030141c10345042a44868040c5202d03810408140a010445204001c03008d002c5148150700c04180018100804c1908103403104a800e220014980741510740300a00c80500c0180d0b03030000e208a0741c599a030307441c2c1d4001c6403444078944c050b00052001043c140399443c408005003460084c0380c1d080740c107415034510502020282c0f80d599840300c541e10802c081c3c110582c03504600401400540303418a81503854910020940808000ba10070362050340303450040b8602070141d001007080840341805507150300d45a0846c0c60120409540d41c00c0d5581940020b502c3c081c0e29440c9900380c004204000c0c450b07889945460783d90049480700000381ca400004030381d002c5075140486001121030002c2160355116018000250300400e81a40d024005100008605400b40001c0956502821504480c0d5140d407501819409001c4d10480c0f1031100310006029241d8003102080c01d0400300c0380032007520842410039008e0071000304141c072140075030f4641203400 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 274712787 1250 274711537 274711571
    0x2090904030f030507021504030503071403010807061803080912010e011104080c0102060c033909030624060f070b0103030201050126100c02030408060405060f06090412050a05040504 80
    0x45042c15460074070944c0d40d000c0e4202c0c2c44511b4860012050b5191101081c042032060010396800f408504001200c07910319030201301d1a42090740014016408039000b17204069111800b42032484901c036103905584c0c2556207034010340c050300c0083d500030041003003447c030424003d40215100700b11401c02001792002070b0711601d09560260141d00c8007131007a180d070a0b95551000401c188901c520a000c0350130341d02c40c518680110f44404c07416040c12810741701003012044003020658201500c00040725a92981a800c2c54201000200101321400e555001182241260082c150a03610215180c983d0b49106400c9040540a0300102505907104580003008058055102905a501040c0d030201c0c0031800021030380059083c502d4100741c0d90031001c25580000e03110b07008461210068019a4201501d459000d4a401e208403401d4640d980008140301805548248480e0031480070f41d080700712032800e074582d0b0035900e66880a4008101d00000c01c4c04845100d0411784000e000001c10a2280c44030030303842005 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 274714037 1250 274712787 274712807
    0x2d0906030b060a0b0a0f030f0e03030f0901060f120b0601032301080c0f030c09250315090c0519050c031605240403050d111b011a031506040209090403 66
    0x401110300c0c0340041340c920155402d4900002c1c56035581341b2030030301c1c0700d6003100941101403503030070070613100c0c40110020306c001c2c4080c41c4a1288040040d02c1860070b15682402d40741c150380081c0d95518104820301000e480c0c80b03800b18495030009401c0c1f0b60f6071144001200148080c8800ea001c0d40d0036040008401252185c03900e0488541c00308440114a1200400c0110020301c20525419440700b203158000d07007070000c819580440c2c1020342d4034075030100c1400c3c0808007a1402000c0e0000b555180056014150440304a000e4003ea02080081458150000c0c040e8842c14500c0c00038240d010081c19042c6200d170b0200c4828158140036282c40750036076543c85410184584048070280100c40307441400c40c000b9045620f40d01c0400700018003948860b2401c1d16264000b4901d00c2d40b42d07407202d910080c2611400010300003040039694820391800c910080c1400c44125500c5480105501204020207a0700040c82490001c880e034076864a42e2185e00010b0002e01c603c100c11500005000b00f084141904004501 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 274715287 1250 274714037 274714039
    0x1401201903260c070b041707050601030c140603010608100b0f0405040513020a050d0f06090b06120106140402180301050f010513050603030f0a05130b0a182d0906030b06 74
    0x403111001074065240b8084048035640c540b08024054480424120400f1540003401f070000e603e00822030142022199010b01e009407901d034003001c010010468404c02c0180204582d045444e030380e000c2d420000b00544010311916007008652004654112034201c030300c4000b8400804000d50752144900001d40c10703000741c800c0c40c3c403e034a028000380f0314a000b2082c5080d001da004060b20380950601003001091084503400740d8482c416000e807c00000c0030ba00c103d142d1540182c2c0307180030520300001042103901e082052111280d04004003040100a08156420302003001c60b8056101c86000c7d90380800001c2c0340f10226819030030715007804036801032110403505071802607c044034015001c6051f141660000d5601380e4055008108104900d602000903140d0300303065240c05444e00b1503000740c1c031400080c25001900c80120000d9816680d03500070b0a0103020b001c0034801050902e1801e10308e464054000c0c00742c002c0b00020403405900c1042c1c80d0800c04003031726611908000c0c4070740307034103008594030403c40e41c031 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 274716537 1250 274715287 274715327
    0x1c09050402031302010309052404020a06020c0306070305060f04050406062d05060d0b031b030c01180509060307080d0c1b080307020d05030d02040801151401201903 72
    0x428a81424000caa2168201d144190072250040c0e0044006203840841601c0501450307407809075006400c01d41c20500c1e01c040e40340040301e0620303004001d002032107584590f0075540a2062007c40d6140401c0040e4000e60301d0400044036565000400c4000005404650b44241340c45c040008011041d4041400d80b030000c000314080c0d81c1c40c1c0202c1d00c0000300c900c00c1058100e4445204100500c1e020b801082d8098500b8030204040441002082c90030300103007a09030745800d2403106440700c1c1c04c041000c0c1204400911700311050054414a0007000740c028011240076514500004807191800c21544d00204100800c40b10880c0c95024001d003c039004000440c0c008102d00480500d0008501c040405c4e0781019002d540340504680c01c01003d45003400c2c00300d905004c1405000281060751001d000207041da600040384090408110030740c1d02d50907400a0700e441031414050b01071070f42e210181e2021416441040b1844050b81c0c401a850015080b1400c0b15010409850008259118a203009420350745034007 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 274717787 1250 274716537 274716539
    0x181a07050702010804080a02030f0d0c0305060a290c0d02160603020a0816170907050f0406080304170f0d050702031605010f0c02180f041505040b13050f1c09 69
    0x100311224810020041d0000b420712022401040c0000010141c913046401101d05d8411600c0d10f0851681290000d0100c107591081c0f21120503806001c3c2c1c0c0d5002c01d01319074180f120750a080c0841140030b00c1d03916910041000142082c881041c6004a4170100d09000483d0000d00385030344000d59070340d42202d0a120030303c900000064070900034003e5410403c5240c03203c6070300e41e035510450580400c417918108104210b010076003041c2e8100074144c0d401040794101038100d0314100320601102030903002009000d1031505a0400050b20003000350760558216a04d01c6090074261009546460310301c2c812004140101040c8070700460b044801010942c0c425010b80f001c2d014004c11100001810307200f84c9000c108407607802c0c54120700c034500d50700311103200030403214481c0d110f1141034540340030071540740358628142814001440500700062070b0f09040484280301901e0705664504113040301030034840310700c1c1c24400030781d007003000034045002d100000e0b508440100000200c84480c00c581d85808202258124038 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 274719037 1250 274717787 274717801
    0xc07120302090307050907021501060203040807080a0506060603060a0f09060924061107030501060b030105011b03091211030d03050703050615040b0d241a070321181a 73
    0x207545807110024090a40585400180094610014003e000714040d42d0409c110b482c034030400c01c1c0d010702038030307401542c0381d07400c1c1405c440c900302094101c5007407903006c40c0d5001d001070400140254803003020781c0c4654480e00c412000c1840149030b5082098620840240440c840c81e0302d6004c0d000700d130340d103030000d00c0320101c1100d9883c03103c288440c20842071140000d05008a0780240b00b413407841040b10b82101c43d1039a680e200c00d400c6035090b4100340c01016000004008030340e40a80c4c409404080111280880700e02e07564007030008850f80c416050000e041840000510003003d201d0300380700030050250303582c00820040040c0108000c94280d0301092030080819102e04081da451111201c0081c00303d4a820b0400300d4401080e08001c40b00301f800c0d621540b81c1c407240c001c04101710300700840c00c070030041100341058a80d500109480700c1003403008400740f01e0040420340c8031964a800f0128912080e803c00c40000003100546040d03001c0c01c01880580011004204140303600401204e00f0705203011072620b460b8 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 274720287 1250 274719037 274719041
    0x4090506030717031e0d0f0504020f03060705180f0409030e040e03090d081b071d0a02090a050f030a120c050705271e0403210e12090a030b0c071203 65
    0x3d00c00450ba0380c402d00c030749407000c0c440603c0340c216030700d000c6140c0f801d00030090074440039200b80d005212136807500c5000f400110b06103016100e030b040c9001c6000d0092850010b1001700306001e80703c000011440c003844481d08075140c2c640c0320200d601020300203004c5104035080c0a449503000780500ca002c0c1d4030b80b0310442594032002c815910082c0000b000b1a81c00c00b51602d40c200d20742c0004000b80c4c1200c0d41c807400481055401c2000100500011549450082c0d4500d4100200c81004004404460040082c401c15644074122501903a07000c48400042c1c040d1742c0082803034100c85000060030008140c0030b005aa03504801903155152041044402241d00c590034070854201c0300d0b584480400e6080c05005103460b1003e034595105140600c2040d101000c4030388a480304000391410781c00300e038100b026510100740e4030940202c1e4911142c000c3c0314060301d2011055a074040c0c0d110100178900701251030580c030b0342d07200601001140c100c441a043c80c01c0c1102405c000f984588421206822031203810b82c4114064 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 274721537 1250 274720287 274720319
    0x1a030703080d090c05040516020f010605010c0f06150801150504020705120c03122809030f20010213090c02061e0408120412080114060403080f04030206040905060307 73
    0x48290780c202084000280080c1854603400c5072201d400400c0070586440c2c62150382e114400e1642c9206400340299406424016140c0c04213001d42d0501d501448640d8016a9484c400341d44a0300400003020b15007000d000620281e440785010068680000030001e105401c514040800b042c904070520395908208401c0703114140300105250050340e10641451846009415002240d805407840c01c0003030b00816038181d07421980300c8644040e900b021003445017281c0b0325110540450508007e051101c0c1c4000c3d00f01103101410b441000201160681015030245020011003082c034000d41d03c5034801c1c1100740d94400103014405681e4542034003440c000c0e10004086029024590300740030303996018030540030042c2d001007055903281c00070412150031500390340c0e1f00380c865800350b007402a000030108001080800c0613400505128088411900580d8032102110100ca0f405502c2666500710700c8030f076041c0d600596001960100d00418009621030341c0d5000180f081008600340c07058540c42d800c40305082d80076 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 274722787 1250 274721537 274721543
    0x6250c03050f150a020310050a0306020d05010f080a0b060303221d010e160e060a050d110901050d0b0307080304030c08010606050316050d091403070201030e030702030604020d08070606091a030703 86
    0xc20004c100c401e4415801540c01c989080307800401d00c0d0f02c0350702041d00c8045c641d004407002a80083d00c045844d84a01c50207014180700040f010300030b854080e201da42d45a002c9030140042c101c1d100801e14a60701001210074541c144206010701d12051810044200014401e0184100311000e805421090a60301c00d4141c50020000c056103464034054040115003080d090710601500803000035841d07641c1c40160100060a0366040da0ba080401d00710f00680308506070020090806200d20407580c0c0e0080107846401d08080b41c001840c2c950700c80041e2500b1020703032044403980400200403087c00958080740050f100701b44028056a641c400044510b40f00c00c5a1544211140c03110808030300740304000034945110406000320310449a074036030013940c0741100000345141e1700020307002c130855816001d24048940c602000d107041205940200740c0320f0030b00520081c0704001c8100d1070403c200b0003d080d184115040001009510388031030030742c001084210034000c0c00c2204280724442d18900002c0100580e2383c = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 274724037 1250 274722787 274722823
    0x30509010c1e0201111612030c0e1203040e0a0c02060907120b0a0b04051006090b031302060a0c1203051b03190506010c0501020c0a1703010b040506250c03050f 70
    0x12005071809544212855014110354841c01c05c2c0c403030307002d4503000b03440d203018446152203a2030b807145010f2000701280070805c1c09060900015506060b04144015002d0f00c0035200105010b00400e001c9055104940101c182520a001440300c4208641d0103100040c000d5000c03540147c81d80b003a1f86035907402610074040100540b000403c0064003520406800055440d40441c0c02c0180c40e0028042e96000c0703440700b039000c44c0c0107420004a5807100002005024014200d0700e58180004201c0d2910059440039014405c002888040c0340d00c1a100703040c240c0c0c1c210700b5080082d900400010003400c020b480c101d040c0c0032040180840c107107110003103a000b0b2003c0081060001782e100300f0307080500302c0108503506000d001000380300031079000e00050000000300c0c80944003600840c50400141101c0b02c00031554014107100601100b03002d40c08940c00e94000300d518a0315109504500300a110741d003035a280104211810300c9040103210210030b01603e00c00c41c00c3d9038000b110b80d55407039950b045440101003842 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 274725287 1250 274724037 274724057
    0x30b0306190f0e0a1101020d14040b07050f1213050405070e090601180b1207020c010210020d02041d07030e01020306130e0c031e06010503120304020609280303030509010c 75
    0x704960b401900310781004003010449111481c1410b04001d0800700035900c50381c3d03102c180c5103903680c18030581805060307504101000c1c00100e001800113000d1800b507a03800800020760074041c09801c0000b02251201842280d8250000c038283d40d0311508500c202c0c0b81809144040400d051a20b4060184a4216961020340c031040c1c0d0000c22091007005449035041c840100004400d20342c0c0d03510b81c4005010300e04402940c9803c0b036171085895000081600c4d0441d005035000b0001682e012400c00a0040701c020090303240c284181030040203103c0d691280d2800309801041007541888803410a20a1605407010480482150307010387c240d120032102140d02500120503080544850f03484110032012030000c5402ca02c80030808030f032420f00f2030b5011417140e40c683c2954240510041003031501404064010301900c0900c9a803111041c040900024414140410f603145d0686070280340f003504420800c02c46204421a20030603480300e445000c20f0300081e0501c400500c0e001c2c014060100d10303450b9035903001c600c4c07 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 274726537 1250 274725287 274725331
    0xf0f011803080c1309050703020a0e0d0b040f08040504020412060f1e0e21070b15090703020307050705160f0f030804120201020f0102070c0e1305071e030f050d030b0306 74
    0x91303405404000c001801c260400301d6070170f260b441280c2c400c80c01d40c1c50042e900c0d03803450b60241c91302d800d8840c0076102d40001403181c0005104200a290403e501400d8440705803610318001d003050144d5005507400c0391002c54001049c0000202e02142140602e00401051950aa501080d1640640305600c014440715002c0902c518951081000b840c075603058905401e0350810302c22410b100032801c0e4502010114400c0306000403003000ba60040907030300b0350201401c00240851000f100c02440031050503404400696000d000320700315094950300c0403c0e40c998015148800001300345500840c071555102000c0031520f03445403061242543d40000126040502d031640900c1032000d0760348100d045004030a0745001d075102c2400030b4803138184940c0d6000c4216040002604d1180d100500304903605a0903400d843c04154042402c10698002000d5a40e803030101c0302d00074600792159400180000081d9030074005001c8082a441040da1559130b050144501d54020941c2e280c3c805d0310201075080184801c0b0b030341 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 274727787 1250 274726537 274726561
    0x70503012d03020112090615031202071d06040e0a0b100501020c03070504050618012c071d120a03080a050105060903280602120601120501060917010204080f0f01180308 74
    0x42d40c01c171240d01040d100041d0303403100d05441c40090550305010001c6d00c24000c103c01801c0f80f0200c09050720050000d64035003898401c0a1101200700c01503504008003043c02c41d200d6070000b0b00e401041800310b80c010706683c509402d4001045840c1403418001603004102903101043e6203800c9000140100030490801040000400f030140c42140d100391031a544210045080107070078002c000404260101002c01351101103242400c0301e00c440d0800000040040c00da42200c81001c010300c2400c4c0484040f0000ca0228469030034543c6030750700d50300c90358080341c1c02c1580c40304030613103d541070010038042e41c0d0340c5409200d414042c41d0001035140e0802001c000c030390340880076420f00c011034103203c01c00c28110300c0d10350b40120390001c4c520b005658800340400950756004180c286101c07030403000400a030b600d440802070940b07200e4050354600c0100b20180300f42000e000d406440140040c171080c2d03001113004004a6a842402056102d02542003e00500e10036070f80718034221246406403500003150b55101e040c2a4 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 274729037 1250 274727787 274727807
    0x4020309061608101e050904050319080601080f0a1e021314060f0c0a0c060e031504020f040209040b041a01090e19020a0c0c08060a14040c030b0c04030b070503012d030201 75
    0xa02c00071748034000070306a6070f40300d0468011f50103040950780c7c414080c0031600d1136002c09081c030b105005400f428044203036800714495900c400084c00c002229280c4044090240800744420601c420f0200300050a03034210740d0003000c03d880d4510740c51083c07554032095607906040444603280c1c0030314103005c0a1860b094031001045031500c100e090f10381080b1140e42d607544151070350b00308030b001a00e0000d0440d41130408104421a80349000b55080182c5007030307070002c0d11786010007840d1802503801040c025215103071900181140213009200b840528506d424400c14141c12904907030014055030b070009081820b19040341d01504043c010711040001184084029521020049e0100200031240001182c11204100c01a007103d1001e000c0c64142000c2810a4407402140e400944414409000008046c00c8200c81100d40c03003801a07400380c0e210b95016249000310b40c40606600103070760030020303140d0380500114140e403000380b40c881d5000040707400100890b06c42000402d4900d41c404061025601885030740e0 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 274730287 1250 274729037 274729079
    0xf04030f140703030501030308010e1311060d06030503030403080c0a0c1704180510080d05071514010f050102100e0c01110f10020d06090209010503040308150402030906160810 77
    0x205244001040035107a56120100640c000303541c42d001841095030060059006020301d0361500000c0c1803500301201184581c1c480200544003c200398201602d4281c280c82c1030b400c4403142000302c0d940c1d0307003455512940101c60803400511700400180295903180300b60340240e21341c2d5440c0c0703500f50380315525204c5038082000e0b03101c0666000c1c400002c454101104201c0a00c3c83c41c80c01007201d0078903224010f00045241c00c560700740e410a114001643c0d51100035544100d401c03021803009071001000450041c004c85120007140c503244800403542c11508089541210000e030b003103c10072010059040100d8a50300b0002c03103190003606d1402050761088000c3c0d05201d85100a03600014468a1910316010180204400035900450b064600001038840c10000303290032141940341640a00009141b0b200051008050060301c07004620700e4900384807864844940035000b155030341415403042e60740d4402140d90000134000b14a45a8a1510403c0e006001d8902d14107240c02d45410090045030f2208251911 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 274731537 1250 274730287 274730297
    0x40f090f020d0e030a0f08190209060c010204030f1518150b030303100305100c08010e0703061508010e09010b01200f01090804080607090608010b0904020c0d08100e0f04030f 76
    0x8030042d1400307200e0440c04240340002182c1e904241840904020f084022003428419050204404070010720303401542d8000600006030b07514108800100c00d800313190300089041d880402c001c81042034414000c0303a014000d20081d000d0f0040301031404192205c41c6e40f0041c1c844108140d04c4002030400c0c9021020200620010030003480400100c0d165403c22250b007091098005400c1043c0a01030040d840100300403101400148036403000500945010301c5516000d813803120000300164401c0c0d20400103404038484100481e0084000181929020300800510600d4000802e542c058144031341c08502c001038540c0c1b000030b00e01c00b82021103068440b030400c08501484582409482e0300b1302c40d0344c1e2564401e51503152950f00b0024130a1a1110003405030060041149040c8421a00003100c0d81c1100c8141c40e65907039908034000840c0207400317942102001e82c412000d2071407841e030f00f018002384103100484040104954500081c00c18140c2581c01c603507544032100124001c02d200e104a00c504130a24101 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 274732787 1250 274731537 274731547
    0x3090614060a14060403030c051203010305010b010914030703170708030a050115020d1b170a02061f03200d080d090b01090519150b04060c0b060303040f090f02 70
    0x5098103039004881414500032405040048500d4000c2040c00545a01040c0744400380c0f00b0310108100e4403c81c0400f50500104019090811000b040500e04041080c50a95201c1d60341c0c0c0b40290290011149287c086654054049103071030703002100c0740680d00d00130f005085491468581c0c0034030796a81200c284603038400300691800310721944021401801007400004071585403000400e10080200d91240464002203000d00307a080c1d003d8640030001b900c00b8a956150451454855040c4c03921115140d00910040740d0318404c9500030130400d10440f01c04022141340c01491101c0c142541982c00010800c16090500e26004142d48089a03845038010780305440c10401030300d41941941101c0c2e04501c45a880705408810003450208650042c10300b0941071100d81080d60f07a00d5040c0c0d0030f8200c09644181c0e2032100d0410f001c013288003100140251011283ea81d40c681d1350082011580300300646a2808540100c1c40c90f042c0007040303908451039074082c440d0260800243d140503241240f81c0c41c0c1560f0702888 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 274734037 1250 274732787 274732793
    0x30102040602030315040b0904030503060f040f0905060a050c0d0e03070b040f06110909010506070c030b150307150c031b170301150207050f04021b030c0102040f090603210309 77
    0x200900181650360000c503240d240c0956500d40c81200a048039008a05041101c01c090300e42d0b100d400d401940c18140705859503152070200d01c02c40c10564040780e00c0b500301204041206501d40c0000c0d0400d000d901079034195a109100e14090300c5043e201208104000c0008480741d5a0716072011018144d40d2003946d24148241d242d481d80c4d448162803d40d0115400c030700030002c020040c07003058008008900034505240c00100062b0140d00c0500c00c0c0c9000d5500006d51400b0408810445409560b008601200354203040c0c40540120318140500c600901c210100494500000b4041038640403a5a84400494800ba54119076001482480d0407071160b80c540450001080608800d8050604008058981d85030a0b69a05902c0c1820740f90340941d08400028042c80e00c804080300015101902c02694646c5454450060200890080c449500011403203840d0700c50107400810840b0340d0f8001191146031600812004c81d00f480c44018444000492024030720035940d8860440e100c16800e0005600354151 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 274735287 1250 274734037 274734041
    0xc0f1203030901022d04060c021305041101030c031a0d02211f2309071737060c0306050907181413092609030c09191a0301 54
    0x29460750728594003c134541641c03174440018a01d2111031403200d14011251450980c509100f9409080200a07c142c5010255159481581c1c00c1020000c1c082150345411f00300030400071445c0c150380d07000a040078420070700c0a11038011740746001c85006018603500750580030030841c002e100b28102d0308505c000141c5100c50321400c40511403060740d60007511448804a0314100c5801000901240c001e1828070b0b4050880b07a0507040c000c00c03402c07a10322074000341c640e5030126140c81365550005248000a03800c3e00c09102c40401d815602c14100603001e15450802c06489845480c59100c49100c0b0040000e0b00300480c80136004210103c178a800c00044241c0c643d00814402d0100301da0310004070b084600911400c0c0000c6160000500c4100c1d0a0a42d031944080046d10b082c0703101d50090300386a10380702c890b0140701c0101c12517102c51140440c144100151402604d0b404e8010705085071182c059160010401c3c1003050890303101e02c44c0a240c540b0304100400000000304014201c01120b08609481d40c61940c90074 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 274736537 1250 274735287 274735291
    0x121d18091c08010e0112081b03040f06030605090108070501024615270c08010c0801090606020c01050a030507030e030a0908100c05091507061b200c0f120303 69
    0x20380d44918843d030400c1d02202c014007040e44000d0550b00e1040315400851640c0041c1d450300012074001c038090302440b040329071a50060350016441c0e2002084000f403020b030560b020104458040c5ea0000007170313036255002511a0080e200b42c0d405600007400e9040b0400240001241c031000c0d6507010300006201003240d8400408050541d00780909440c041e0013401200013001c05002482c001c10b06c42894180507000320303062054403019507401c4082d40081001040d00e51140900a400000c0101080c40d14004160b060217205540c0440d19119002c514144080b80340400200103840d0b043c035000c02054214020503005003a00c040584e03030300900c1500142400200342c0d50a10ba91900041c90812030303c10704042c2200030155020b450b0581d03040b05503401006031044028205c81080c25520340302c074001014420914020702107442c241060382541e003080300c0b003524000140d585000511414080011039040b48451080035480300480504030710701182c3c2d821030068050210342c800d41031021124035603001 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 274737787 1250 274736537 274736593
    0xd05040605071d1e22090201091505030705090d0609031e09031203050414061014031902091e1006110a080a030506120a121d1809 57
    0x1a8010301814907070041c511002401c5081111840700c0300400010144e00c0311401c2e10361500800c00c1c1e29a00399454100c2911504403420400340d400340710405100c001d103907101c0700328007246044a0201d0140c103a04140d80d4005400d0719102c0c650b0301e4401040d40d16800042d012a4401c501c001c00b000001c81c1c0d405003001c0180b103a140c07055070005c02e54202640794540d040e14130030091079130000c001007240321841011a60080c2000645134540d424100c1604c00303010741d43c007418400c48052000500d01504824104d803003620102c000d445104040503140c104540b180c0c590124400d08880141c036021085a03007040907004405c010008407100c18012410403102e503a6000c114000800c01d65400407002c000c40040745028160315892955220b00e140100c80a00b801c25a98400141d004c2e11190301d110088000700c401c44c0c1c1d012003a4038061400980700c540071390001d0050311410f1750b443d4082c180710341d200000030107400d0280f4659403401404400100144030714801c1c40000e0241400c9040010000d0711 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 274739037 1250 274737787 274737791
    0x1503140a030e1206061002010204080d020f010c050c0309130f0c0509030106080a05060c031506030406090510050613020f0421030e060702010c0f0237050f060a0f050d050406 76
    0x100d9003405810510390a079030501032103490000c07604508000c60001d92044040f22030180241c42c0f81c0d002c03030080c0645e4205004501c501045012055000641882103c40400007030010180340b6030116400d00070325070303113643e1769005005580c000d140800250b0f429070800f0354002401480c0c4428201a115075103c840049100000d201c0d655050038025100503001c130600810820350a580c90700e80d5080010031007000280040041890406090000c001c020070041a254480c206801c010008102c11102100c56114020074203a0001050007424031512001344a00c404580c824003110295004d0318002d00012000c01020440d006026100ea90f603510f90848040070710002d00e000fa004071410f5855603c1444241b0540005070381c0494100000390784049007196000302440850300c00304c011103a0203041c0382c02c03146035189056400481001c54800200000c2856602c1c02031003030600090300c0311508102c00b0840c40104502414130128915035514000f86041500028078045442c20740f000c448a41e = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 274740287 1250 274739037 274739053
    0x1060b07020a1203020a0f15020f1207080702030f07110607060617030f0f0901030e0d030b0f0a08100b01180801150b0c1e03120f01080d050301060e0103150314 70
    0x306003585558050060042000c50107207144c0c5010303503541c60130721000b04501c0040820800304502c0031440f04400300341080664031460002200310440d0424a80c203011580404c0c0020141445600454003e4000f900075518180c10130720002103581c0700c0c2c40c05480c0d1003501d0f04550307069104d41006040d01801030308009005414900380f00c8d02100f941c549610164014885041d0321824070b001c940614038a807804650398141d8000581c050452142030f02d030240a4010f102c00b003030780c05801c8005282e9044440ca2000792010042125032581ca010b5621654440b40508014010700d41c080400143e0504080e144407491031100c3d03055a0349a08210f5890b5110108901414041d6810a02501030101381a0900c0c052650199481d035882149039421344044038a060f1541c0d0600440308405078507000e41606141400d0a110490b00a1207196400e02c034882d80c0002c524805d00c04e5a041c1c886941d5540178030b03a181e0b001100a480654580960340708490000400200e0060b42100c1010303075100900804 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 274741537 1250 274740287 274740289
    0x1906020f120c09030d14041401030e0a0b090610031a090f030304051f0207080a0309020406330305090303010320121005060f06070602030411061c050903090f010e04090501060b0702 79
    0x11071681640014041d460214286c071217941c00036a425600c00c511011041003a81e40102c002e004c0b5420031306004d000300c58604041c44115149144191401800c4802640310202c40c051408900d120141140d011a00c08030390012030b541006030012100000c99520420800070300d800e651042d00c00311150340c001070840c040645501c00040c450403143c5411401c20b121034681c1c119910869800504155a8403840011966141d0100e000740006841c0a191540000003a00180c0d05500032041002c5406188103000361080c040c013442058103a002e103007543d00c0c0d5a02c8540d602c1c0341001c0d031300a00012082003011501d40343c50000c1c0c1b949002008012109070518500110780300500a54040e8080e054001c060380c0300c1078201e401d00c66011780010307030306d07600c6041201c00144241d0740180d10610024540c0c0c000c401e60036115007100801e5404002ca6103910241c282c1c0c9200302880b2980002c0c42c0d1444902e158080e421420440c10040c2010172090503076a5540d0850b1100d400c60308440710701041c1d040035 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 274742787 1250 274741537 274741543
    0xf0e15060306010302011202130807081605030102091c030c0219031101090320030f030a02031c150605090301020c060a0c0207051504150c0b01030302010c030e1906020f120c0903 78
    0x80300036400703002c441d415900001c0c03c0e102001c039800003c9400082110074808007421640081c42c00c817051f602060786524686032503907459511040c111085032008501c0c0c5c901031084640039040100200c00f0f041e0507020510b51071140310400e50030300004522800141c2c54403608401c0054180c881c845d031460540c500309000185510005040221221041c000154288001b985c4d680c1411840e001c4806da040000345400c900a4451406001c04508070714600d800101815800b8814802224a041039000101c02c0342c1040c40000e440084102041207102c2c0140020251904041d0026103031038400e158a602d09103055400c0c0031a550b44503040c500302d50741400104050001100d105480035480c0102030f509004c0d42c010104032039118194156242d01131a018040c039940010700f90711642e964100a4001c0c600800d00318040781c10f0800101d542c146c0030503000c01e40014000c824a4004054940200039000003101c0924000c4c20044e80140c440031451041c81142d080d02e00701c0e0741d00a00024035003 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 274744037 1250 274742787 274742791
    0x1091b020a05060f060d050a0b01030b090a03050f13030803040b04052104090507020a05060414011a060a0e01090503101a0307050d0b04020103110a030c030b091005060d0f0e15 77
    0x800c40d001010488001640030a1050b003021411070700d0b0090380c940c1c4000544d02c540f020001445440b0f1041d600d02000311302100c3c1412203000e01c0305010316540e1640080e80310f482218005000400401c503001c2140000406041e071400003e85c0f005000752640ea41c921035500c1030b20141c6d042280001080208038080090104022444801200001c0350020b8480d4900450107048810b42e2500c1c0000c031708900c02c2017085211070b0001308032032007070409003007880e2021030040300d900d841d5080c01281110b01061400d84101b004001e4001442c1c103400c0b502c2114458001034019041003071507034000070140d9041000c03420360300540c28000f509001545031a8240201d0f1182c850180c0c0096008100c2ca40d00e01707414900d106e8005112410665039403004070018240e00d5a158903c05c800701d2004903080c1d06500001060829480070000c1b002088204040c01c442107418101d0320300304400a00c524203143c4090108044980d4000c142c400820207088142c4210b41c00c40303405503100d402c81d4140000141c0c0115 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 274745287 1250 274744037 274744091
    0xb0a0618060f05040317160c0609060216060809010e16061b02030d0809011803092904122105071a0103050309010302030c0702040608060603011a030c0409021302030109 74
    0xb88601c2110080c0a902551101901c6003840b2228901c000d005001140c0412240b900e03030300840741d040d2512180020150282c00001000c101c030200b041800041c140c1c400210601d0b6820703000e8a0500c040f644410010104030165480d41c1400c41d944404001402c082445100108680c0d0306015006000e0740c0142e4008501520908450300940c8010a100500c00c40fa45407103040c07607a138462003e01620b00b165400c101d2281c2e11905d20b0a041e407207a00d01d03058548085903003030304d030f01c40440c8070304822581320ba0343c0721002080004004a00e842c40c13034010128400c041110a041c001c940e5051102c1300050b101012a00001c0d0000c204100502a10700ca80c65070b4090790f10a5040d5281e4554034010365070740354113040d4000302049451440b003003640d0300300d903004000784181038844c1020398031045c065400c10b000e5030034401544140002c0545d0000c1c0d6030000390081080300780f1039003000054a100e07001030b40c01c0500c840d072200200140d4002540039180200c1c011888000e80170803600e90100d661542 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 274746537 1250 274745287 274745297
    0x1505070e0105131a041d041203050f070e03160902030114031606030f020f0c010f050601030b010806091021030f0302030c030403080a18050c1e031002030a0b0a061806 73
    0x41020304075050a00801d507851103070b01c64400f0320800d50b80314040c416604140071840071070030070500b4041d00c80100c6d84154400c07405441840c00e00301b0705405440040d1403050322607006000182103075104000d08c00740d10600400702ca036034903640f079202842001345410004016070000014000b000ba0404102011402503008101603091042206100641401034030308154995101c20000720b11501030b540ca800189400390b41d40c46419040c00d000b0300342000444841403d0600040066010307124502e000b0506840c0c41d00c0c1d03907540300b0401c801000f000380351702c4120082c0000031800e5204401d000440c101900b000e50f110003210708000c2c0c03500880e9a40181050300410810101c0720040090302c0d005549401c0c090410340b030b0300407024090301220581240c84080064010140301c0c00040c06000d00740c098403449411501d00c0803e401940221903069010340c80046c40944201c110703401964000722400000900884040c00a00380c80001d41c4032030009080003207081c810002c400d440c0b00040c0700c20700305 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 274747787 1250 274746537 274746547
    0x2030904050f01080a03180312030506190b34030906081b04060f02120c0c18070504120303242606060f030f07120c0f0503060604020306010c1505070e0105 68
    0x3003650740c1d03101804010108469080114181d401c2078803403d02465100c101160b1040c180035008004000480d01248a2025504100c410716000f07406842540c01b0494400c0c548fc1450920800c14100d442d1020b400c6e08003c045000c58102c00125400e07110710990ba5801890328180c00100140c0c1c01604840c644a0045124500590203004035030840b00281041d00503103120103000d03801c2c500d212242103040c501c00640c804200b4000302c0c841020002c00c40b00c4078003451542940440e90001210b044020a01c20003050051114144122a1060cc68603001c0b5032000c0c40345004840c0c580c0420315601107a4041c10074401e030150f8100c8000040c890b20100c800700840002503075070b52a8061300740b60050010440640c9135460038000442811040f000300c607441941e50400b500b445d4010041951403070410b06c008034820b44c911510341d00300e440040007003a03151120320802000354000350019050100050021000030b030b1441000f400d100c04500001802d180961026100d201500003850400804000d = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 274749037 1250 274747787 274747799
    0x9010b060315030c1002010606030e010b4c08070f0c0201180806010f061b050d210c1d0d03170901021c06060e1005030f09030d0c02030904050f01 64
    0x42030702da001c2c12000c107100404a1000100341411341540a4903007089130b02e00c03200d0005405400050468246035401c10100742d0940c6030900300c40498030001d50001d145c0422010980c112030216804143c101d000700c10161405c284d01c4100a150302d40c05a070481d0b1280c4480045407c100e52541c4400c0d40d0820444c10759120b40300800c190151003000b8140401c0081c400101c280d0030311641c01803c0380b00104d903410350b107030760998500400c40e100700b900142c0310500c028500740d00031090003281a07210009040d89103103c5403c1d680b0443d0481d421140600d0300c440a5280003240c01401d0710310b403140c0c840e05101104101e45401008a007030120340154001e151500000f64401c840c100310f0031142c000c92401d81c07244662140641300d45040307200e6030310390451001599116948014200c8005d0340310a0f012580c50340034041880c60203442c1d1800300b60700b88001641c150384a20392591205c01c80054a140c080480391394400c6a2440c0401c4005a1000c1801070050410780b2074160000004280740c0e04540c5002 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 274750287 1250 274749037 274749049
    0x41508060409021807141630050c0c0901030807060f0b03030d0506040f1104151803081b0102130e06040902100c0321050f0708010b0a030b03160b1209010b 68
    0x64000401e65404c070002510644108480c3d41000550011550b40c3c01140c0340c00946d00c403e410040d00c81c204100340a9901c9030b018400b9090307132004440d00894a03952040c06039102e0b0005580c283c03181c0112041c070311a40c0d80d00f03040e40c0d0196100b00e40e85a101c0341c05082410449036040c441071a8039192640000c580c1c0d500000340d502c2000d81e0880442c2c0741d91071402042c003400200c1d03012101c02d410720340d2030503141c803590010f00b0540f021414100140880610211041c45680f018540131911048052012400540040403000c00f612001d100340c0c106003445170300f240d22070a92200030780c0c0010028011b0b452400700b01c40d082082200c0a02c044103130707038001500d200130080100083c00b00c0c00c00c00904040c01100e0b03ca00c4c1c400642c00d042100d003c603010306406071008807043d18840c00d0b0712000400d0300c0c0c000d0b501c45040e52452080c0030305000b00184141c0c0188a81d0303040036418481c080741c4d06012800300c00000c02618104001c02d4840644529803a05044080e203a001c1507410300500001945a603 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 274751537 1250 274750287 274750309
    0x3070e0901150812070f0507090204210c1a2101091a090604020313050a030c0b0601181503020f040803072906060d090204140f0c09011e0e030304150806040902 70
    0x1a410540c1c508103840c6c40030740307001d01e494024024001c883e80000c0c00b000c950b01410894940000d101c0110014075844601420f075034100170101d0141c0070060201c0300ca41c41e00c01c0072250411403110318103420340f00da00040b544001c030003010788502d1800501010469010325000381641d90b111203003c080c1140001c4604000502050203158040000350010b003d400515210070f410030251000400070303040c01003651003136050556205940101007501035114229075100506504003032040e071130030490070200a400f900b8503401016002c0c4040000310b080440240b00030700c850001150b5134111071410a01642c94401c29842c0d1907882402164010180011035921070402c9071680d0b5140780d003040801c01043e0940b000f0350410b190205c00b4005581255266018405a00703c890749650b50f80042c150750f118482c051400039440c6000310180c4010b5026005416107281400c0c0881c0c0303040381c0840c0c9560440d52110180901c0074412503925a001418250441d030305075400d21114501d80c0104c2c0800c030030 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 274752787 1250 274751537 274751563
    0x50301020c03091e100c0b0f0106020a060525080613021204080a03060e0c090f030d0e0904060b06031e0906011401081314010207020a08160519030203070e09011508 72
    0xd5000e80b10b0000445080c00d080c4200c009051744482c0c54140002452084007003c211413807103030580072540d0741240a00c00c5040303c4141c1e00074005d07554242c1d0781c14048d0901401a0007860000e1042c2074400307401c07030010300703100000d03556256251402c071042088041030620500c00b514410002001110310a40b0420352081c0c0000500f5034641d81d00070120020080c0e0340c071404070070040070b05200301e8503241801402c0c2e04c44112800290040d5050800d5114120340001d20003040320044c00201c24105503601c1c3e580103000d0030001a09a0451000c10b90780c0d0700031500f402040041000d016121003003101031640090910004010325810500341415080711328211030f0500c000b2500060107003d0bc2c40b4074110282d40700e0360003402403801c1e081c0c081c040c0d04900c401300e12030521b001d4086614040083e003403210200600031200001c0c41c010a02c00601144010742681d400403120100c00b40c3c400700040e8004100070061080d00b4901138890500719418482d503840003040d0700d60100b0095000280040c01410 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 274754037 1250 274752787 274752799
    0x100204060225080601060806040b030c030c0f0a08030a05090a0602120d090809030f0c0109090b0609060309030d1b1d21010b040e070e06090103050601090f0906150609050301020c0309 80
    0x802c1074110848103150b40b080b010b0344258030021401e243e0220f03c40b070003040143c82c28401c142400040548685d000f24042d41c055101c00400091440c3c0141d01c100e01070000340030700241d69117420f9081c0c01c0d0742c05a00000301044002801854a0410440e034500402c620701c00340c9080581d003405c006a41c4205102c001d0740d00d8803130b40c0e0b032003e2149400c02ca40980e20010300303c1d5074078081c0d1009540c8607125081c0c01d5000c10004c020000d10203905014a040d400c00003450280b8150101041000c160400380c00f61400344414045100e4901042c480c1540400740450170076008008024002c03c079800c4541500400000c0c2c0e10383c500c003500c401410380040450741003002550701c004103105005003d50b0341c03080c8c0d100d03081160081e014400030030100c1c191404080e101020f0740d00e1406000d40a182032000600c230354052401004401ca603a44080203aa0b0307c1640401c1d103408a44500041c0c44020002400c14003501c43e0421805030021a400d004240c00c1e07000754201800000956113034051590114000d20b = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 274755287 1250 274754037 274754083
    0x503040c1d01030309170a080c0705090403030501050915101215060c05010501080c0d120c0c090c08010503010c0c140a0c030308011418041214030a0e1002040602 71
    0x211622098001802a41e070080a020308809001c941e900c80c00c3c803064001c175003105404a44d030202e1401205000c2a034000500c86010b05680320300d035035800502484030a0042e124041b40a5841910302c83c000c5000f580c2c0841d49504120410601c40c1300030b00404004030a0072140355194590b0400d190201180741800350142481984400140c500200347c589095649000822210f401c80c0c0c403210228052030003040240c0e2100c100c295924041100c1c558064007148026001900c0094615070015642c60095821980c0359540500e4803110b4200c2c40c222a100d03100d0041c043d034050170603401410224000d00503500343c404044c00001c0030000c040c0c007501d0706020368240480c040003200525030303000d901000b00301d55a040c010032150b4207004603600780c0b0540103000c01c50310f4285040980d2003131103003510140b911030760307240ca00984044100005001c5003031580940085da21001c0c0d80700d40748000f07011498244006005040441002c0d00c41002c1d8410b100c24050b4a42c0000c042240c29144a80c46a1070 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 274756537 1250 274755287 274755293
    0x6030209061c080c0a050f012007030504080105010b0a0201050f0606220506180108011d01141314150405190b18090a02010e03030a140a1101020d0204210b07050304 72
    0x740070341c010007902070b82002801031805000000c00405450007081959a0b80007d990724509079007120729203c1244007040d41500081c3c40c0d1500030801e03280300341403013440c1c50f5442e0040c5007541d809034088800c038400801c01c1d510b0182c0a001e503640c00810903c10500518140c00041e68a0183e01c15401c0704206144c0070300d540340c0071340682c6400340c0b400800e450348400000001005801c03c4200700b1340024000da00002d01e031b00d02c0326001071221703005104958280c1e003000b2191500340042d20304141e0000e800d41e4500c00c0341200f44140050503200d140b10680320718140100302d5012090300402c5009030710301020021a12140c0d400c41540740070380140400c46502110000700710100348186160101e14060034441201e600244a900f4076100780c0760901c4a9511a04050320780c001c00280310040b59030b407489400c004100100030a60441c0d00c0c1040d01d41c045110720b06c582260042c585101c8010740c009824001411381c0e890b40003a07289500d11069008186540302800cbc040b0140c10b071824010088080760030 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 274757787 1250 274756537 274756579
    0x203061e0f040f020310080a0302030708180904050f01050c0705030409090807140303061005070210142205090c04150806060708030411090603010203060f010c230d030b01030603020906 81
    0x1071a44024401d010004076504a24000d50080c0c1d01c10040a5680d980007030318410202c0d02d1115641c2540207942004591340f12852181d102c6101900540303610307040c9a8495807400e280e9030140e40500f00410260b44078161023421614054079080601c0340500c112000654000110f80a0300c140200105224815107448042c1e4002c0355402000c5075200d10015040c0a80000654881c02045980e4241040c100c0f000b07076118400d8200281d0030881d0008032600c680d000303c0301d043c602c8098042241c54084844950705035501020300904001d110440700700450325001c3c4495821061000c66030380b8091500316601010701c840c0081c1020f10405030700003407072691600300307880026030040c031820740e02c1c94030b86400c202c1c00e05d610505a12481582c2c000c21101d0805100341c07880f884010b403203880b001c02500015240b040310110110b0ba41403109005458507022904100e503442044c500038001501c070004081c017900c201c89000c0e8105403400f103040000d80e4440d404d040c8c01c02001c1c0d641100ca103548c0006202c2e = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 274759037 1250 274757787 274757809
    0xd020c090112020120010914012306100c061d06010509010b040e0907031a0f0703060f180b18040c091401090b2103040f090902030706050a021e100606030203061e 71
    0x245e03510b40107500c1c0500c1903200d52042c0c10807100d0004c00850096903000d040c1d001202000d01100c09162300042d62900300007000d034401031031505214900039115a608000e440c03500741c034805003010040d0700041d1100200308060141a0480c0c500209604054824030f5500581c0301d20385100c25a8001f145201005100400185400003c0d10744d101c03c000c40d2200031144143c814400d00c00c840400507001c144a07101d9030301921000100aa0407a140c0381c201e840c6000c2d030303040c4d84c0e80440c0d84403100e528503903403044111028101da01c20310700645400d007003403078100200e680812000c904200030000407548403543c2c1030648159000000b8200d4401c40442c004200441c1303001c0c0b59085070540700644a4001000e002107800748072010802a89901e0a00709039054140000d4140e8882d072401d00107a0b0045003d01034010f42403040722407001079500b02615500e6158a02c4206400080064851007040d0040402414040c01c040d0b14604100c0d01048440e114241d0020b6061021907074041103681d0811441c0e = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 274760287 1250 274759037 274759097
    0x6090f120607020a0308060102010b130c0509040207060b0a06020a0b04031b151d1218042306090c03040f1106040815180a0309060305091e0d020c0901120201 69
    0x400a2500c100069628001400e060740440d480100040300c540c8140a14040500c01400c10b0700d51103032331146240901003034410362062020a201c0c44480d0744440c0f0242c02c226000705004100030b103040d8144201c0d030310260070207011500325403003081c049096136502c00c0e0803541c14a09214004440f10008010b20810040141400b210780181403807001c540c0c010b21205c3d041c000310300514140c050106947c80c07603101000b50211314103000c0002608031000413443c400401400208420300703100c00350b9100800c1c20407034408a2000b0350901c8036501300300e01c0f800e0384a07021a402528505194454000c10710700c03c4001480c01d0308143c2c84410036100d90050302d00509900c0b0440b0341d040c4654402040c0c80104440c0090b40e0749180001d42d00d21a0700040c60041590192906003510f4244102200900002001e01c1c03030074400c690304e07201c50100100d41034544018100260180620043c0024205143c1c900a2031007007044a0062081140c0081001100303a82420141d41081000006180c1d0040b450302071 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 274761537 1250 274760287 274760293
    0x10b18040b0616060c0f1409030703020a0602030a0f03090206030c03090a020a120203060f0c09090a0207020306010b09040b0f010840021201020c1c0c0b1911040506090f12 75
    0x3e038815a4240303061000042c440e5506101ea400d44003401c9070b00b2800b5480c5400025000741c0c880b00350300011001068010400303000c0d41c00550716034000c1020000c45511050050b400060088105640560002c640100c1c0d413a0500000700b05400145030744c00042e19280180750b0001c00314544070010000381c0f4410380d005c1d0090007207035603c2c1d01c140e100c114004010f9000c1e005003c0046c201e01c3e4200700d124810303810200700c42c0c06c18a1080900848080040c52002c000c0d900704025005660300300101d5000308260141255902d520f14113203c01c0d00c404208403130103a4206011740e50765a030041c1c41d081d4030116142050a80749456400c49902190b656400100900c44108070034800400184a4000038002e481e40c010003022268030341c1c00c0b4441e440d190703846504149028600c0c07800c1d4045060302c0326518948461010550b48031603501e140c0c02d5034102120f0340380c484000c10303401260144840000c20791610758186841d00307010a81070320415406a1046002c2c1c24820000d07a1160342140b58443d4480407 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 274762787 1250 274761537 274761547
    0x60607030302032214011a03060a0e030706020408010b041109010806040b0112020f0a08062704020d0605151c08070602070501060b0a0203070b0a1b030c1b03020705100206010b18040b06 81
    0xc070400c142c000315100d05595081038504107901a07440030401410314003400a002692b1042c0700341c802401460310b510345c035000420a00d00842c1e00e0703001503c09850202c0001602c0c05000003048121540344400d002c4101d0284001d0055a8105505e140e010001b5a170100710900c69000488170903a0340741c60240100e202098161411392490094121449070b030329944c6442d00c4a10412941c200b010f01c48605414418415a1101c00f50025440c0c2062015010140100345a075540e820b4403011950021401100c0058180c0e900d0514040c03440001600706500b880202c54552200b01e1003000780185c404d0303400140003000c00c0002d510400c014100e825085413100d1660600a449a018840c151034000955020178125041842540c04039002a00c180b034402c08490342c150060891850361209003d6042035004525080b046c041c01c1640c0700f0b5005c1d0020b075003000c00300041e500c04840104110360020006210511200c0101d6291328900500310301000340722030005015000303600036284c1084010030307 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 274764037 1250 274762787 274762793
    0x60906090605041409120702040908210109050907090506031002131403010204120b04151107050f06010605041211031509010b03010b1c0c03021c17030606070303020322 74
    0x1c410002d66504480601c291440d9151014407a00240d5103003e145e000f4204070400e448100b0010035074584003410200c0e5a2034181c8811b089904490741807030503040030303032446020700e005001080c0c058408080b0401050424008481c0c0e503800e54090000c07025920310110f09140d408006002c007a4802e071078199a03988034541303074000340d203410300c1240ca0300050319800c50241e103010b00a03201600c6405580041981c01c6490b00160040080c2003a2880b15215569151280450003041c42202121351010790360791007481e0192070103507030422850302600410010320056034000111000c817200c10341c84800942c0755091200d45a0340c820302840c0d00d0b100701156140d0058603480a244140c0340e2000800c04101d2000c245400c0c2e98001c020541d01011940c0c8142421000c5188172400d14000c80740303900102d449901065a031244210540c0c0d00c901c801c0310a00405c995151540341c0040b400d82003a066007448800304040b0f00506100809041d004000210140c4e00c440075044d0304100302d030206200c285141 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 274765287 1250 274764037 274764041
    0x121d0615030d0c15020307110d0e151e130b0301150306062f0a0b01030609020f0102120f0f09060a0c050d0905091b070503180301050f0601020303041506090609 70
    0x20054024041c002e08400e0b050f0148410825440d0050350007400031a0a041d110000c2d0f10040074202400500c00034007440101c1005a19000c041d20b031180c410440d079140400100e116075030760070700002c0010000d0802c0d0084010045940014441240d07403a00851421049900031030f0b0803140380c002e404000007420300320142d18543d64240c42d4604210440d118482183c0c1f0b1011110b0082200301e04524404000011881c117044000358078040e248070078490b070f07030300204080e080e4400d4580740c2e200c00e40c030780075442c2240360756115071402d00042c03141318410114071500303010306c420600c9901d50101daa1200011890211445031000801d080e179961800740014201008151050b5403910504020380c110728016144001545ca00070042422940d5000d404810640310300158030095005001c88000140204054031032460041200c004000700f080904dc00c4807002089115084011414446240d8010007101d8100303401c074110200c02208000b00502825659006800c1a03141440c0019152400d03 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 274766537 1250 274765287 274765321
    0xe01020c030a0f1b110f040605040204091d07030b0109020c1501291e0f0415090305190305160c030c0906030312110f03041506030804090c030c121d06 66
    0x743c03913080150320300d8603800c1c076440d450050050202440100202e8245080704249a143c88020300108100c0d4851001c2820380c0c22903400461080c0c0c07140d6001d444cc03485a002184100501c0b4001c000061039900e41044005c0184144e0b0001d031340c000b664103840803081c0410b078008809000c801e542542e4410281d100368000480c41507020100c03a4000e003148003c0c20446035000c002031811507034901d2003076802c10b1603401141d86140c00ca004100002d90018983e4054002041940303d4415480c13644c204031741088801140590007001c8030181100003a0094159031082e0440c101c8154038030a189041070404c6495000a04601c03443c03000080c9174106c0d6007110050307070700c2a510000e88400980030701c410303204107680f1654911410301c080c0c1c0c102552000030b5988240a00d86c019006c15003c1001c030101c9499800950340341d54002020311110505016020720f40d082490100000e10302200c1c000d003038980c0404403100d41d13501c820b14800c80c0b0401d09200d461680c4070106542450420380e21804001c030003 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 274767787 1250 274766537 274766567
    0x51008040515040203120c0304080f1c0810030312022b06080604110d0c1203020a021815100e030616030c050325030207120e0a0915090e01020c030a 65
    0x1032600e0028941d6140500b40340601d60140003425030042070f001c10740142d00b0002401600b071200b8400095000410000c4100420310b1030040c02c1c0104260b400c6068150a04424038140328448040c80041d1004848450489030140b80059005003015400000392041c3e141007051240349007124000f0201c2c5100c22800354488841c01c022042e613508050b501c0f45021035016220602000c10710a260505034040c0d01828412217542d000291640115060b04006a10550045e40844500000c50501d000c2a4030148602e854842c06840c2a5091517200080302400b180a50b5403001030842e45801422050301c20b840040640300a854071500140100e01c504070001d001a0424500c400064000d1003200e000d0104036001c8540c82c4000401c040314001d14006650425500f00110000f060902074800700140e1103503103c40705c004045041082450301a040054420701c0c0c03070811604000f54640c01c00441d4040680440d80701d101d402030343d0080c01038524001083c00006507441c101c030341c06500002da900c2 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 274769037 1250 274767787 274767793
    0xa0605010e041a04181b030c060905060706270f0c05040b010c080703020c090405010f05070302030c0403030c0c211a0c0d0b130c02030c0111180603070302040510080405 74
    0x6800704010030f6440d0100c1160384800303522807009403414950050141c8007000900455244034603034400000345180700f4007164507100808184100710f018074800000b4003240c81c2001a03030303051000140e090f11990100602946d46c0b400c401e49407114004102c6240c3d20035940e100c01c0001c280c00c007854a03114030701044400411000001c0341c28a0640f0070340c51a2807040e0b60b121850b00b101ea8032021207500c646420380941c800d4411420090b903858074050b105034410000804e07502c4200b40c0c8003040d2500036100b6820f0500600821481e0240042078501300c0342c1510f03000c002c206c410b05090039184c005401a40c11085a080d122a00920382c030700e41c00590b80319030648100c0160603030b041310005100f41e8120301c403501c042001100240b5290054480e580000b401b01d0240b6038040700510890f5148032802d8056000446d00c5890084c080c410241d0341041118510314084140d00d41680209201c01c003648240004008a4501c80c402e905a8001d40000b52151145010102d009013400d14220b40480d6184 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 274770287 1250 274769037 274769057
    0x10e0304061115041e14012325050d02040e0a06081506130203071704110315060d23121312150203130507120317071d0a030b0a060501 59
    0x21850788141c0b481541c014605c01c07103560300c20702009a0f15850010507a22440d1a02d080b40b0560800c2c41161440e0440c1c40c0c0c0b442444240000401c08008010801800210301c00d00c10041095050030541c0041c00c2450f0195031f5011042004009001d0342d004907030b850300121b007013000301c2d001580120300b5a610001101e10000f41c03180722000f44401200c94a0300310301266040d58824032150080c5da044442410034504802c115040722500300307412a410f071160309071008031042e82e00f400d0104070001d41c0007e1041045c0d2034441c000c2072411040d03000081181440c100c80e07440e034200040405078600d01140a0750201204880705880680102c1c0c2d01e1080c4490361400010710000645800c200c240d1310481c6245000694030a007030094000500113040c100d204068440056024040800541b07901c1c070980c0007651a42c2001407079050100d0104240b1040c02040c0641349401c940310300c610061200d480c0300410481404240312004a600c003c4c10300d21500c09104c003d15281d0069016941d00780d803503814034 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 274771537 1250 274770287 274770313
    0x4020a09030c14031533030109030c120e030a11040915020316030203091b0102010b040212010801051e04110a09020a0e030f03130302060310030c06111002030f070f02010e03040611 79
    0x1d45e030280c664455017906203001c9900715900d003040c0030202c03145000b01c40d0b6004441002c6070a480c00214102d000540301213580b01000100786d02c200d10381c2c059140503c0340504050109594000e01d02010340310358150036441d081035640d6005540e55640c0402480f541c50728650200d80603400944803d4121400d000d04400351070312a100740c80c0b01d07000000080510101c00c0001c6807c100c5900d514134119500c41c201c01ea02c64a50740000e28010400585080066243c445001d003140c20240075091030601b00c114007011502004c4081e6042600a1080d9000240c0c80c400161031080c60741c000c078141070010914044064001c1c4c0c7c1c00d5002c00041d4140c1d12546d40c00540d00d80c49210b03504070b800190305000b405101500f000c0c405190312050f95480708030510788a4980c00402005944108005100003000c0310030100103011031840d58111001c29825400c0c400d12015800c58002d01d01c408010b290010242101e200b500804081607490050300c1d59540c4900006140e484020744c005a80d1050020340002 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 274772787 1250 274771537 274771573
    0x11060a09020d150b090c090f0609090c033c090c030d140d020c01020304021e130908070c29040f061808070e0402090f070c0204020a09030c1403 63
    0x1940c01440142514000d6442c48200501225042c0b040d5135101800300c40764840180c90341c010f0481c1e18000b42c5484a04040022010924070102e0140f9400e000813006a142d203181150030030010203540780c030303a50b5130300c0e1094a44800c4000b41940745105224001002411010103080da40d580036219110f56554906a590780380c8245400d4265000360490f02c40203101c0ca841580000041100629060258007583c040c0d0308400c1b440340c0c0995001050000f1850940820b09030202c0020000c0911001a0005003400e04080309400d80c45464440c0c2200f00414903049811150740b00114001c130a0311101c1c803403168404041400e4180e80c0c00403910b14580940015a41100c2342c100c9880036142c00c00303500f01d038200800201c8841c1c101c041d80002c2038052040c8054806840419449030310703481c0074010032072100c0c400307013054420303c0d6240140082940e00c0b00d0504103040d019a409a0340f4114094216142000c40d80040c20507111002d0114420649906254514101300c04994840240080001c1 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 274774037 1250 274772787 274772801
    0x6120e030a0c03181e090b1203040e040204061d0103050607030b0a030f02010e0306040809010e010f0e041a0a180b0a0f0e04081c02091206161803060c11060a 69
    0x21030baa00c40b086001074880c1c00100040040c1c09032215a0307694031031038558088003020088031600280c101c240405c031414498003515000448040e001112110515500c0c0e00c200d01521001040700d20004055441e00e8100d0001081c854039130310a20412108141c403c02028002141d15009000c041800c8a20a00820350000c4006000141145c41d5542c1c1030200111f80c50224107004c2100320f588a41d90b406c1c00802c2c031650003a01240d03540c0a10100052402402031441418081641c00c4412481d81c80000003140d50815100000d807204082800259000c003000d5076503002681540c0400c400c02c2168140107030315007009044c040d00c44007208100413015980502d6085498596007003200c0300340014080d401901a00e00645030520610041065805040020700340e543c0001c0e50781120305080000c43c40b0805014054105420540440002c1c1107a09e5289070410085462108850100034038400c000d41d4000c40420500c95805401760488280000f000c0031801101d00141c02c1c4c000f1409182 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 274775287 1250 274774037 274774057
    0x201110a1d010f1407020406090c02030a020115180e100c0c0308010b0c0307080a030f0501030f0b1308160533010b1603112a0a0602010e0a14120406120e03 68
    0x1c098010072880703e840c135401403401a640940ca8810002d1445a284520f103c2003000758065692030800032406425205c010410700f080e5010f5001c03c00c40d0f160580c991510000580700b010401400c20450b040c501f41a41d080d08440c240b90003c1d0a2001da04400343c8001548a626000c8441c3c0e81c601c210251405140040d5180750410412032000550400040c4412803490400044a09900c03d280d41115402d0300121072410703130940c000701440380040c00c50fa4841c100c04020440f4840766601d01e04940a4035002c4c0e06045d203a5811481004001c0c880003403a00030f5905c0c421010050344929520041c0c0303a03000031010301c1c91140041a202c0d13040c2c0403926664451343d40180e4180807550f0460b6070180c0030102003481d000b000070090b96810166803107480c0100c400c00c1011200040420040002501d1303001d00196031418031101c0001c0c20119500122682082c2c00c4040031052038005400c09088140042c030b907000c0002c0c080b4006401001900c91103668039002c011800618403820340c0c82c4103000e110303 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 274776537 1250 274775287 274775297
    0x1a010203031605070305070c03060f11090d140a0611040e06010c0f290702010902120708120708041d0108070504050108030919120b1e130f030201110a1d010f 69
    0x8070210300030f1000b46401c0344a450010710300a069140c0f0410003420781c0080b03d00b16120705c840028050305008044401400d83c40c4585428000d000140c42014903040042400d0301d5a5016090b118051004880141e00141c0502c0082c1074903c0060705a4885e01440405d13040c0c07200802d000b548201c000f01c440c0790340304e040d60440060b95203421401c0c0305414410060700c5129103092035190074950350b29001d00c40c07540004c03507501090f10400240c0c06241180303003001d84c000d20082001d90000951001d000e003110f0b003616511030590402c40300d02e2180380c200d0b4127403000302c5c00040c01c903600100e080d034100d600e1303101900d40d07450b200c0c4200410b8031002e2040b1b5910f0343c414005001585015200f10a85003181c0c1803010825035030380e030f01681c0e42108100603901e81d6001e4082000340b000c811007031149421180d02e940c505142c00f042218141c0020000904031074074580c29001010300075440b00b0140c1d03461140031903d4400d4140001c020159041307248604046019480e035a6501441c010082401d140d00c80c = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 274777787 1250 274776537 274776571
    0x3060e280b04110711040606051e2a0609060702211b0106060c0209090c010903030503070909050f1e01060801090b0d1514160c02010c020f030d031a01020303 69
    0x140c001528840d80c0180e8641d000c030104650f803401011698800d003620010360b10174508100480714a41d2010081c041d0801c155241343d0803150f0748240341603141d203000e6216a540444114807172001411940c1150325914214980d41d00020305a2007581400126085503036440320498803491145050401360011030505201e140038080a0541d40a11207481c094901c40843c0d0346080d075240d070b405030003c1010705500304154100f6545259002c6909030080051406201c0002c1078890315200207020050003102241801e482455498010008604107205504000b030382010842002e03140302c3e2490340c0c4590104040c2c031040d80c0d110704a4000e5268400c461b0307c0c10300782402800c1c400c599154030030010b8a0b21700000d42c0ca40d020302e505990b01080002d929842c0e200f07403024440040c1c00d442560303442c07001084401d5800385800a1541c0c0c2841d01103808401440403880e04010305482683c03502600640020080d45648a8002415a908955041d001c003030010b90f101d200c00d81d0100d00d40103100d00 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 274779037 1250 274777787 274777861
    0xc08030325050417190311010f0b0a12031101021c2301051908011d011104080a021905060d0f0c03060501020319050c0d020d08010b160f02010905040c03060e 69
    0xc6200c0050092030150780901000000b50410305c14001c4044011a0728070703c050100f01c90910814840b2000c1040030800c00070100002170408545104005aa0f205402800101445190408020030007440250f4481e038040070780b103800c400c0e80c0d0030304034110307140c504000f455500c1010682c04110800300d00340c005908010034040e034805416030401c2d007030582a03000101c4180900c070307a41040c2003d150f4401b1000b01d01c141282503a143c6040010b4100040c0414170114001141e08104103504698521034048016030489541d91107511250707110702c000c51440c900000c5074100c0503815036014402c1286403000341003a012185a80101801a030041c004101d00c5062581d049400544c80c1c1003280c1002c1502c0075a0303103410200d406070f90042c0c0016018040c895041341c0c4003809091010501400c2001199101e0098000038201070111041c1031800004c1d03901610701140a01005001406000c50780c07800500079044911407d0000100720001845c1600c0c0341c0da0660001c2c0070044c052540d50309401e = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 274780287 1250 274779037 274779059
    0x11404020f031b19020f0c0103050108030a0e010e0d110f030d1d030a020406170601080c011e0c0b0106090e0a1404031206050303030a050a180c0b0706090c080303250504 74
    0x3209141108119581e481104c80c581c000084e610b41c2d00400c0052030640b2010f0600c044014410305040c109001031148140200568540352424a09000300d1031500c8012108042c40001540d08178184001c51010f110b080300002d4440e00302030728150001c0000c88241030b0390b031100e5a80c00000403141c0404048031320701225510600d442c001c0441c0c0c140d0807140c000400310358407684400c46100c444018000c0414061141c64010032701880034103a4030080d080041c0c24150046040040c1070f00c1541c1b0b084046004440e0001620342014004400d5031719400301800d1140d481c09114180034850300050498203050142c02d038041c0c1c000e5040010b0b0b845603078092352105001c007600c0a1a90310340801044540b4100081c501c031300462039000c81c6908000c90950115110314101c2954012a8000000404c480c405418111440c400540d65502c09070b0030000c00402c440c0c2c2c4014506040b00400189101000010b5400b8102d0b144a0300209035034919400d50711811800b045021560600007048500d40d64 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 274781537 1250 274780287 274780321
    0x203030105040f021209070302011115071101140114240706180803042d0b0403050f0d0207060c0801050109060c0f02040e0607021c0c0b0a021803070608011404020f03 73
    0x804098248051714407003601510040f40c030030806601c4000d0400c00c0d507038810300ca070300c0404100000e00f403240360301c81d0a43c80a49004090078103104050401c0001d80000750321101c42080000001500f80d42c644192102401840121910440070a0f0010074031099502d00e000b04507041140d0726103000010390b5603501604c03010140e21070002030684490082018034000714400d520a80f10703610f00d061156030381c4148009a0140000d50000c103450980014401c518040d005a01800d00c02e443d41c10040c0c030b90125100e8000b0901d40180045001d81c00c1003104c0e00032548110a680301c202c00c6a072900011200402d02d0f108140018a01001000224800002e400c0585001910206048050144591508130240d81420040e40011400c500f5101007459030304680c200c07850f20080e001080d4880503240705015040d075400e15800078007a000390345186425060702301d0160543c1e010958411014202c290300b44202c01c640100b4001c02212880c2030310865080031a03003154182151134615840d0301c01c3c43d034 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 274782787 1250 274781537 274781561
    0x60f050906120d020709051003020303070f150e0f0f030a021b0103090c180608010506060f160b01030813080601030807060f0b040213060908030c0604021c0b07030204061b03020303010504 82
    0x740300100b4800d0034203000075558800703250010b00d1901e1800d00d505084540092803d00080f205003814801030f60044202c540103604180d150305040414104141c1064202070031070405864081c10034078610010900410903460301c0140c0c0d10111101414a880348200710010005802c4030340105245d420350791003401c405a041c0350000c3d034000540d845ca4040c40700c4d90085803a18040006000d505012405400d000c1c184900090049040c190045040c1d030050400300c203a5603c01040586025036180c18000c04240c018900c0e0000b035a41b801d160039180c1c0b040f0081c10001c040c5140c04101c00400189150480c0d60000402c0d26001c0c843e22030000401800f5181c0003842e848581104442d03945001400305801c0968480060034a01071000d0601c0c006030380f1940702908140001451140c021841795881074054070f404481480c0440c0107107074207002542c0105076030020420700290a0381540a041641c0c3d00342c403186103000ca0480585030400400b140100141c5c401c000501175424150000340d90554 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 274784037 1250 274782787 274782799
    0xf0108070f02150a0501080c0d0b060f03010209060414210c090c0c011506030f090b0a0207080d020d020a081e07030e1002390303040803070c150e10060f050906 70
    0x5400309222803007030400c4d02c85040c3c860301c450040c48503440034010f28017280350450340c0b4042d140c01035503000d0f120200241402e10604800655100c1034600390102c910b40710b00240101e0340c4a49071003100c42d2007640c0320402760040140e11484000e24002900f52a422240c1900070000c1704004410010942d10090009002410034440c440d50128240140c0c0304001a0020075801d031810010028120703440d402c40945d001c1c1c1001c8511001c646101100740e08982540800340c1d40300c46c4e500f4808445e10405094030140f034800038921811001c03650182c0249400d030355800358152180c2004007114019070280b10325a440010224480340d0082e4840445542e41c00c0c01d442ca50070400e030b024412a00f0030020355040d04000101d01149010f40310841a00900001d6020580c2030503228242d030742e010040004000d50310010110b014035002e145400402c55116015048080d101c000c1c21025189509500c9010300c205a410b2820303448034001c0714241d5003c6004035804602d0902000030808000c4e2050741c000b1307 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 274785287 1250 274784037 274784053
    0xb0a14040b011e1101050901020a1b02010e0907051312020906011119080c0c010801080304140609061603030501050603070f1d0d08040608010f030f03030506180907140f0108070f02 79
    0x143c400840c980240c0d83e40e184c0b0440400c070a240c803400d44038000c0c13800e803e03030748104241000290040d1100d280310742109490b030110980c510060b00c191094910041d800360001c0100701516600800504000444403250b800d01e6a4440d000d0b0781c0e03407040c204000d40c0a400440091850351090b01d480341144051801c1760403400c2c03502200304043c182e4000a40304524005801c2520340701c2041200f005ca042880c3c0305075290301d818020780e201d0103940520f800d411401c0e44040800e941e00e03004d80d58007010040c9a00d5036180402456a182418414201e02107424640002114503041c0c0a480c411155910307501200248144111084c0e14080395807070402092080551207602c2c4c18070180400c034403c08280d40e4443c00d0400180c0001c0c0c2c16400070304c00341922501400050401e00b400103070207505080203c2d81c0d0b1107080029000e60001c12009000c81880010084051000940c200498510303070700c4504101c0c7c18105110303000201c120505d01107006500030424072403045092030709a109030300c140c1d440310f = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 274786537 1250 274785287 274785317
    0x60512060f0631050109050d03090f0f09140c16030c060c030504050609060603070306022505010204180e030f0f070f030206010312020303040506150d050a0606090b0a14040b01 77
    0x1600194014210b4404290042c0020000e0801c3c6800e04040d451244045030303c1c0600081203c1054098580610a000310503800c060055682202034203c0614000480c1d49504100b0a01300681c4101c0078414200417140034031013034140f8418004d401a03080c89162203844480d0f01d080243c582400c9080001c40845c81c0c006c20030500c1034a0450745c443d540460107080500b001817601d6005401c54089070800b0f030074403070705542c00038010007240d51003000940c80764170507844600c80160151981c20000d011004542c10000c3c10b60043c001c1e15008001d030303440c00005420150460b00342d00184c03851a4400c00000d11815050300150112040420702d081c5840b11039510740304c2c14824504100d0144e40705070014410060703c05070210b00b55542d4801181103160030b85400d80d9a000140c0a00c44070002091000711688460321102001604002180d1f1003100518128004205500ca480443c92800079142c00c1883c21111500440c0c0d1040302021500990303204000c000d10038001c0032814020660184100 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 274787787 1250 274786537 274786549
    0x31b05130b070b0402030c0919230414011104050a0b07110a0b0307030b060304230c030111090f0105130e06041b02060402030610060f11010f1104031202010501060512060f 75
    0x5a224010a65484c101881030501d401d0080c4405403103070700074904100016580805980010380b2000d030120f8400383d03110345980084800d04c4600382800e200020003061140303190194a50074484c00080152a05001030301006000d14003e0a0780212095000c001c56540c0001621142d8050700c10702880040c0c2d030300011001c1c80f256100f850718401c00700c108051160140b1078440c0e4204196130341440c0d880d0503640d000a03403001c180c200308080120074a60500c14000c004600000030007074020410b07840d1041c2c0070500c0d5088800080e04c11444203600003455441503007542c913012160300328101c3c081d0411384408503003a00100403c0d000340d0348065640b03078011000141250021140c010305440d0800e03005150400b80000d044c088001c44c100d6041041c242d0103000c1802e22543c03803418400b84c04500fa40c0038050302281903100c60450030100440c2110200c1d00003003040b640715034401120100703454826030a841d4248285404a44140107040150302e0036000e240d408100103010441c100400c40010742 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 274789037 1250 274787787 274787797
    0xc03140c0105091b1e12011407051b0c010906120e030f0403060b0a141017070234090903030e060106080601170c0708090105040e0c0d0507031b05130b 66
    0x2109500200b02c2c950707070007000e0641c40000041900c403007041c503910300c442170b82803010082c0607070041070860301080b0205001c1d800700017000b9500310350b00d005082c00180101580c02501c0700103030080710520416401d14001404405801c41a168081c40302e1803e003042d01c0914075054100300d05900da262102185c44240300030192250742d00410b0791548d080d07040840403200306142c43d5006480140090240c00c40a945130b0078005401c032000b40e000d02d54002c08465048115401d0200305100c0c4082c02160358003c01d0841500216040362a52902d10000b555004210490740c001c0d007016072042030114000300c1e0000980030b400381c200814444001503010f403078a40240d201d040025010002c0c4401580e03c560a054429860203004406080161412000340f03d0f5210040400e00001948800e07640a081030310028451a0801c0441d0302d400d420145840c0c0c4048400342d00d8074901000038412070f02901c5054428901d80041c001452000201581e09500444416454442002001940d0206280104 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 274790287 1250 274789037 274789051
    0xc0f060603210c0b070210150e13030905040c05040e041506080a111905030f0a050105070305092d070f030210090e0a23090a0c05010905010c03140c0105 67
    0x1480034034504200c0818502c100b0107503800c60180041c0300e0a2940b0407042c050040e0000c0304000e4580310300200303926000d5184101d140c503d041c0886015035407900b1902d40101c0308074003044016960b450121459001c18850020042401d41c0000c2c40a800d00b54841d100490031380c1080c5186c00d4980c12203c100410450302100c131280e41029070040540540100c1d4014a260b0300204141c2c80a9a2440045510450002d00644618002070940c00c1c50200741c0001701009001c1d10590103a4100090b03c6103108501a2020740c200404241d20034440e105c0c01780700301100d0001d0302d80f00342c02c40381e507100b4164139a4013a85880300040c00c0b510414020300c15000208a1240100307407a501d140305020742e84005e142d410051004060040080b00d8a200b203151b44840340100c00100590141801015200010f5202c0c20f2084880e0800c183c40d900000d10000c0c0500410441c0d0400d940c2d139004442c01c00c03a6014150002e00d4909417480003900828140c28060700d118012410048404026805c54070100d45803 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 274791537 1250 274790287 274790291
    0x518060708121b0316050309011104030c03030314040c0b0d09080a030c020f03040f0605130b07080304230712030c06090c15090b040b0d02160602030a0e010608060402040b010c0f06 79
    0x1c0311481c0d0507030080c1150f5003001050207041d0302e002500d402c2c4881c19000f40b442400000070010700148800e50100030754a00700b0107060b4813281c680c200096241010300084010901e0000c40c03d00f9988900c02482c811540300e50802825803c0600c0c40c0403542202c000c01c3c0d882a26260301030006038030700002d4050600150b40004092507a024003d24110b200210761000b500100710602c01403142d440403030241c2d185400c000c0c0c1d40f802c252001586100301648910340382000860080b08000c2d071900190701460013203501d5010308040c40d20034075200d020010002140d61140c6001c102c003c5408840980c018001d040100d0b810609480310b0013600d2b00c2000840d2041440103080c01140d24040001c01c40d01c1d07440c90107440250420f0340e11205c03803085000300040c0704000b0403a0100750b00700d0340449a209880805000f203064461401401075041030b2054600c0074105000300c0981d007814840c241c00c440860b001040d0b1500d854003840010070b28011218100103460002d940818814081c00b030800d840381d000 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 274792787 1250 274791537 274791541
    0xb0d1209051c02010f1103070b01060e10350a05090d090f03020d0825142e02090d0f15050c19050408160e070201050601051806070812 59
    0x10092510a45400440c4644007514500051000d425680d00b80da580c2820a1280640204400e5607500e0f050b01481105100014415040008501da26412250b0f20744031402c40d40000d00412817820b2010042c4000116040c810050340c11a0003078113864440c840380050001000e201100038200030440c0c84a0710651901c0a010b07548104004103c1e407200640b901c5c004007801c041e44828000360512020b0b1140101859042c280300d0004100d400d00d02c0c074480140b001955000301501c05800301c1006031030040c49641c28031002603022810050791282d02c0c01807190014509401441da400005040100700e509111514040c1c441c11254070401c0d0150b81c005041d20310a10307202016084a5001da19981d0822080c0704a500c620401d60300494420401d1466452540c10120303440e009591207011188100305403a480102c500d1851001e60759a000340041507510703010240d00740d90003500c000f40014001c10505004608600c11341e1a034000c000c140030b2600116440708002900141d0b680d400310f0a88800f = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 274794037 1250 274792787 274792823
    0x1b0507030806061b03040503100e030a051e030901050421020c0105030c09060c070e010b0a0903020f0f0a18050901020424090f092f1c0b1c050f030708090111010b0d 72
    0x9883c4038031089c12020301620159500030758480c080c46944130244200403402503144100c60440300024a1007080068803442c24280481c06010150b40544001402c4600c0891050556000c800d9000d91900141400c6412600440341a40000d04144520b4806d1142c034a06070b80d0200107041a15202d0010490141400d101c0c00d40c41038180c0c4000001c41d000c1000340559500171a4800842c0d4044032040f010011403000708110a02c2003203d258444501c050215a686005103036201c400c500d40030410160b91006006801c078403950040ea01140d01201d8140d003030502c40c0e018022900e020f441c1001d03450b581c40c500b50b42c0034030ba6038000001454464200350005014985810768100c0c2e40000c00c258601c41ca40e240300544510340d03003401c43c2608007019211040480d0010189800054804811000c0884200c00144040c010880b554020540d8203089528000145c860075a0401c0d60340d441c0440189c01503070762410580c0068150754851200440d5651002c9840040a0281882d034a0381140e0b08 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 274795287 1250 274794037 274794043
    0x10b03190311060108010e070b0909060405040809100302030a0f15030212100507021b060a1706031203041103060f070806060d061205100b0a060801050402030c09150a02011b0507030806061b03040503 87
    0xa004403040601c01cac00308429640d1441201600709400740c4001502d51282e00305200c0c64400c015000e07801460b002c03d40c6030002c2d41756008600c16116401c0c20003504120703003494000c1c0d82c9841710400c104c030b9408900b4405450101e80414010000c10112003603404100c10312001d595044440c0300168101c001da2040d056201c084806081004480c598900b104105015180140c644018100c0b03008080c0010703000e031002c02911009411048104c1e441c1c0c68185005200b00a0b6180010702a000b0040411005204942d000e4001e580300d44a4000e95601c1c0310900040d030700000001303042c40b6140d00000130b203102c1d400c5045506500400150280f40d00c01c02a04080d00c81c0480c1c44c500829140c0c004111580d404000d41303055030b8041b103000d6525101d650180040340510f28a9660007001c400e51105a83d0122009006140140c5c009008446400d098103850000200d01c190124804200c0c010002c1e00c1241869030004008043c141400c4800c2030511410400700c101e603800e940002418007ea203010 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 274796537 1250 274795287 274795289
    0x8010501140105120708091207150e1203070c060605150a0f0f12240b070501050703061202010c0c0e091014011511010603081911010b03190311060108010e07 69
    0x3e00706a032400000720126008408020a0343d400c1000140214560400900050150441d44020941c4860450510060041420030441d0405290240001e11140c001c11040c000158101d505402c590301d444080c1c6941c200420101d91207543c0321000310361692590500103070100d680018070b4407170322185009005000351030404002c0c803074526002100c0075486800118152a03c010200704c0e541500040d0414120034030090240950128010800c0350b0722030080c2c401140224024445929243c10540c103c0b0524080ea0300c0b1203007007060b52000365018201035500d00f403080d43c52071501d6942d0142c1140842d400d60790000b136604030f00030079900d4181074062080034407140f071174100300d6514140f001ca007071064018140007840242d0154061203203007903004134020b5400821190b91040c03107410340c40c4a10329010011003c95180c1c080c440000405108801c0c3c0400040c000f00701d1034452480244030b00c40301001c00c03070410220b00005116040d047c04041e009024040c0041031012040303030340398200201 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 274797787 1250 274796537 274796539
    0x2030403110105160c020402070b09012405030606061b0a05031308010b030c040e07090f1b0503040c0b031302060c0f06010b0c03121024030605060c0304030b130c0801050114 76
    0x101000e10004500592034080c0381c04150600174401c001034130104002e4002d041024049103400380c10400d0400042d08105500700c8149240c8131130f51007080d1030500144450140b1a0964810030004015041840c001c00030300e490403100a031010300011801c1e103405819101241d10b6000401c030280344a86069110f8003504100c0000c0c006600d00e100801d40d90b1102224840c860390b22b8008030342402c2c1e418010400a0105244140000070301210160040d1050100e4407204c13001c82d0481c3e4010511404c1a00d00882d402180c01c120240390891894482c1c102414000864003080186001030b6240401000824201805402034440340d07682e4a0500030140c0c050010400d0400c080c04c0320102c0071084618500d054141c3c0c100d0394849102f006c41408840e0001700c8048000a8049111464560300d4010200d4075a02801110b840d0700c2400520301513207141300400c0d8814002400003900a01d00140d02c5924050028141d02c2d5644907414409000c0d803065030965910700c0140042680121440a8000 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 274799037 1250 274797787 274797791
    0x210901050d02130e1509010902090d020f0109080a1a0606030c07060203040507120312061707121509120e0d08040608040c050303180a0512030703051318020304031101 73
    0x5040029100344110a1480c0d4060360001d400d0403400b0003808200081d03e04401405080d10300f10406548034414000702e280f1841401c0b00000e00940a07000316055001c0c0580b2813130146040340c2c00c0c0900110b02c0411a81484820320012544000030400200400d001d1200200140060009094460701c041c0c101030003210b0800c1086a580c85440032200082c0c1e21080050356917450b402c00c036050101c6900f0032100034410302b0194003810703070142030307460700001ca491300b089190780d280d4001d102c5e806032081da07403240c0c1c00c10481002200800414400550300038240800f094030b910412804a4106040450b003011041154954450f44040c1080200c1c105407803031010703c035a81d1034500c9540564800c0310f0802c01228002010031090b481a071008000140071a600c400b207007031300080d4414034280b0072400ba0310304550010b0309140503c0c1811070b04c030200000d54070789022624125035940c000c44004c1d4294510142c00151001000c6101c500050306c6040107859080600c0e0040a924100750010340c0b681c = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 274800287 1250 274799037 274799047
    0x204060503030f121302030706030f0b0103200d0219020f15070e0f01030905060f1605090d11060417071505030411040507111005040c0602030301081005130b0921 71
    0x2d034841080701c807110004a9034131425a2111404100b84000540080d09400340400c0090900c0d0150441e07001008a44424000901a0001141124100e40590843c2003800d0300c07000c8000c5102c0024401c5040f804009031038a003019030034030446c2e201d524210006a0001c080c0e41c031801414400e03400d03403428090800c040b500b0100002442c007402071a81520820481e00d203491546e0003030303004200c1d0503403250649445240c00301c040c1c2c4c00010b00325038001d854241c1008540000e0310402c00c40d6a8100c00410000c0f0700f11964943d0342c1250010032185802003400c003c00710303d1044403001081c0c0f60142c1e000410360b503410b000290844c0007090300c41e50281321062082c0000141d0091240060100a41d800a030070b0303440880884038220741c1d11000c41c160140504030b541007081038220302d01c618060344201050f15981d000032030360303803000f48612012600001841485050141c100c05d41001021542e00391200c200c1e141c85501c1032040d90341c006560b0101004902c6000e1018003284003505100b01c0c61b08003 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 274801537 1250 274800287 274800307
    0xf030305011e060e2704021002150a090f020904050622150b040618020310080a081b0309040203090c03071a0909060d1703010617010f0e071e02010207020406050303 72
    0xd800c14007850003031006080d440c0b0303040d8440320005c1c0c281c10640f40000b01200c103000803400c40e001c416903069010340101d1082513043da000003501d40c484220302d0340c41c45003599010b00d1900100070502c01214140682001c010240c0da50409190003030740280064941e600782254040c421b1a4206090b064401c4d41c020002c2c00704040090b00030981d03001030008200c036180900014001c003d180c00041e0b0006842c5021000e41c46250b015521610000304100c03801fa845e004407595a8001c080b009103041020010142c202000189408490188101712420034015200040a903002260070402561016903070000130728013003061100400601c0c0c448071500006403150510f512030401c030540104c40100208400391101c4080070102c50b08041e848000059070301c1203a5080d0320a100b10400180c0c4502d00704e665a0401c2e00d942d0403626290010746040d0314000c002c502da110014200c1050000202e50614251014240b4144c038003440d90005941d108a0703c1000200c075040d41006001740e105101d04800 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 274802787 1250 274801537 274801589
    0x50405010b040603020a03060e07090e01050603011a07030c0503180916080a0b060708160b15060d090206090a0906050a1706060409081603021b100816110a0f03030501 73
    0x50756802e00c0e015071ba03a802c5003004e401a000c20b5215004152614081003840340c2d1003001503007aa0a51818400c4590b0b8039404c0107030600080c05072103d06400c065040c48140008802400d0a9200c0d08251070f80201030346400341190041c0f03902c003041d40d600c481c04441a01e00340003a140d001c421402001c600401003000241035810050031544145c0e80d959503040103507600c909460685501135400340e514800d28012a03401e200302d132011074605d10722402090007100300854400c02c0440c06081d507400e210300e20400720050915590240e030455410041c0d00e03426140d615141d0040c00c3d0709031011a4241c542014015008200e902c4660401002203c081c03803a280490800d4000350300f10b41c00311b90001d0300e007080d170b8461140c040b11041c04015035240030105900420342481c0c40700b10281c2c440404103000c0034030904000b00d0803981c5c001200c0300001100b4500e4420b2810f00e40710140f5020a0758003204000514184121406a510301000d40900007003582c54003515000d01208521454085503022500d10 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 274804037 1250 274802787 274802789
    0xf05040f02090a09020a080a1e031403061329030a080d1a03150a0507030e06042004020715050601170c07050a06050c030709060306050a0509040507050d05030c07050405010b04 77
    0x40315004110103c3c00200b5160000d02c0415001401d900300c680e40c07078032500d540b4641400304a840844400403203040840041f00c4500103038258991161001c00c801d00b48403203510080646e54000d6070300b540d004800340144204021038116940300254040c85055145101d40c00010541c400d6015514003400200c1002c10340e840080b051602080081145032914080e03102c1b0103c0c1901881181c02c810050400b20b0862402900584010052070300d1b61070701202514044445031003039034081804600000e0040030a0140e6040702803840020780c0c01240041e09a911201b000e0314802003015440c030894031385209040e04a007007424041640c010480220b10310000080c03111640340004604102031041c00d010050001d5880041044a803400184070740c0709800568840000a00781540415424003d121b9403090300c05c010003210030b0601d000200075003003400400450300d0380201800010b040e01c40c020884902845100915200c904d038038086403400384203a0101e4401c504010040000200640480d0 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 274805287 1250 274804037 274804039
    0xc070c23120a020301141609060f0503060f0a0f06021014071b1b0602060709080c12210a121a0d0f020a032a0503030405010c02240405040f05040f02 65
    0x1c14600e41158034505120711500080c1d095401c0242d50090411030760f40440c400c0184c00289152a01020400c4031000d10502407403010070110700c8408412030242c2c0146501c040010f1104d80184245001b00711a4103443e132050b001d8010100051003000d40502801480400e54642045031085407030034120f00c104058071120501c21440100c403080c2e8404001b03c50316a8201d451885140c075120b250201660701486014014060341000c0b8443c64401c10200b011100e40c00028038608100b03c040026803050465000118411402e48a070b00403407080200d003900114005107a10356048140240c880c2500305200c0590038502604103102c0c40302906044e0182a040e54680080720841c80d00d41621030707003d07501951043d9003040c000100001303010005a521884a0059240350180c0c0301103046070468054582d16800c00d00c801d001c1944a0b0841850980c00245072250118100005040b4054030444c061008000001d00b80030034101030042d0021224120400c105900e419200c003d203110f6850350007 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 274806537 1250 274805287 274805299
    0x803090303071205220f090506030604031404030b010f0806011a030403080601090302030f0c0f040207020f100513062f0307022214061c0510020c030f030c070c23 71
    0x9110f9445003041d01c81038100c00b03900d80c1e0000e1042114025045040c814542c814540c1d0f44041091105401418025a000f50080503552110390f0b0545683c000354285100e02c071410302000003ca07040c0c04441e402880103480203100d890401011a040010580040d201010101c0138646130400e030000b10b9074080c7d09494941c00030346901004071150329283e0b0000e540351041130411564460085803600d034034041100c540c01c501c4403010500044e0f0180400c0070354841c43d650b00ea840641003000b400311601003240751a034908180d2114556061040750411070003c4d0341c41441e08000030300c120043c050180100ca80e01304a000702864035070390f480b41c07400090041220b40d404038100d03440590a0a941d10030480c0502640010014584074540200ca100d0312600110540b044003a10022600281541100189c24145003008800700658481d011409040c80100704101500800c5000b031402818842203441d503071030f142d040c1003507500844e4010f54011905401101007081800301d10341440201940c3c2 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 274807787 1250 274806537 274806563
    0xa030803070815060c0c240a23030403020a030206060105120109020702040f0203011811040e01051207051005091009061d01023301060f05070f02210313080309030307 73
    0x50340e0048a061908144c1000300803508441e5004082280001c2100a89001040440341e0031a0401c40c0030040205144d070341d0402c103c0c2a814820784482d08003005442005c2d1001080072a0700301e8552045500741c006810032000d2a0030503905200c4550401c2092800504002d841c2c002c856054506110b84e01440364009003007411501c80d078020150645101c0d404544079030392810b2400f207903041c00c090a6100d40c6403135098034041e002641540c054610304041509540e003020b00340224080100100d04562081010014099031340705a001150350407995016110502c880521135008400040380c404c2c070034200801c2c000ca80d888102c0b41d0270310010001c01d0401402010060342049059415600c0c4010742c100c070041506d040780702c00d50317000101220745030890382e0320001100c6000f480b0030351800240041183d040032030046084015240d0000b010109180350054658000c0e02c940343c000b40c5103403c041103940c2c6200d1b050365040000c0c030458024528040380400000c1c3c0b01c1c490b961008103800c0700526 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 274809037 1250 274807787 274807801
    0x212150a060c0c170a0c03030906091a07030e0a0b191704050c09060d0b090a0212061509250c02030709060b121b1819030b0f04081c0203040506060a0308030708 70
    0x1c0c5d0012900691407410301912820001c103c510f542c02440003003169540c000820340c01c01510103410040814000d4208030041e50300315400760480c4542135100c1d04450780030400e800054020004803c0742c3e080c4451140450401404000c003220300c0780d000d0f11514007000041080496524090700c01198070015550340d10000664a8000c2d24002d0302da680c8090070864880320008920301664000c640f00794140d290901c0f120355a039012907000307900b500e540c40040000d00b00750f240300382c0210362120000344105142402d1005020201c40d0070001031200361022055041c144a210301030103184006010442c10006a00c04900c42c080c0a02410081c00c80010003840c00044c0c04001d04c04000e0071aa910034462071851301d070007401c140707291084690310440d15400f00866004003c40e1350044000a5070b60751014220340003070f0020300136500d0749001c00c0031941303001c1c0359650000303411860301c00140c603801c050801d6854210020062806581c0b000411310200d0810010b590b400780e46468160340d1a0354003a = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 274810287 1250 274809037 274809043
    0x50d030c0602220e0603011b030b1c20090112110a050316030302061609061803050706180e06150706090807060e0c03010c09090f0212150a060c0c17 65
    0x10911210360005100352020004090b603c002c03ca1321540ea100d0856100c10081500b00d42d965851801c4c40540d440d001c00d03400d03000c1d070841d12060340c000300f10400703840041100c0c0c000040114801c40d0130411140f01140d8058204491101844040d1103102e010b60400c80445290080c80c0340141c02c107803600507043d03030961784e010501001c1e00c00130b01502e810040003d500038100c06540811005030080f81d0020303004084841464400c0c1004e41d8840c030780d040c0f41032002c3d200050060340309054105550030102c0071850401c14200201400d07a01e040f00710f1085000c026070800b040d00070019071400b24080c044286c3c2c581c040d88840104031940d050b5280c1e468030785040200b40e04d080040c42e80001140310001d03c10346034400c035100f040e0082540d51590401e8101822a10700940490200e141031005001e01c0700349030b0010921304001d800051600c01100c0100c03004407400c07940b08501580644031540203080800f140b00041001e4204011004a181d54440c2080254001c0c400c044c079807142201d032001c10030 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 274811537 1250 274810287 274810297
    0x7020a051002250303060305060708060a05060309010914060703150f0b0903100c020102030a0b0108060d06021e0316020c0d0c1208070b07020601050301060f051509010c080d02040e07030204050d030c0602 89
    0x603090b80b0fa080360803450040e0143c04e852000780d44070300864000550071805800b134507200c0c01e4000d00c809005400c240802c00142c00c05052180d0320740d603603000c2e031000840c2450781d02c030040d414400904640c5000303240141034401014280d5561000c1c0f01c020010118140c030280b040d42d051043d20340d160740760880480d1800d0000f0080230549424100c0030517403c1c0e010350087d4020318501d40c00703105c0005600c00540305044140c030400d411840310b5032460b01180c4580c2c0502421940c4a5030b408880480c0800c500c91500700b0341d880700f40700c80c81d4400059090740402c4807040b02c40068940c884400d40780c0d260083c43c01018810410ba0000310204401000180000c80f200c5a90100c038404550501510003540c9407401d0043c1ca00a41ca0034501041e00114402c8540845000406021000d000b2010010443d04400c0d142c0b0b0520600c0c810005c001040c1300c000d001c0301104020010384451600341c0403c0720340400340a14007858030401c001c0c840c07502c9052141c0301e80764150500600141040c03410200038030032 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 274812787 1250 274811537 274811587
    0x80c040209031606050702041409100504080903010606091806050105030103030f05041203030b090601050f0702010c02181303120c0f0e030a02040203010f030b0c0c0a0b2203090e07020a051002 84
    0x60320001302d641a0480090f040280c001d135020402c200c00100060320015080d13032145241e07071004811012190301900315a41c030501c10391056007082034401c0440c1c01d441c21600003030089000d03440d090044011000d55450840283c20003804064078010010b04607200c180800360420603130030201d0074034501030400c40b0f00808a00c85a0808600c4c103080c0140100070b00c01489108407840408906030398410303c291450310900c4a50686041050340c010741e400048500226002103500c1c0480200406200c01148520282501c0c0c150262a52600a01a44000004c522241e00c0d107181401d480e07900c44031940c01c468103400c1103489083e1000000b85031002440000b50300034000400031541e03000c92210070f412280b2584216101d61078090550400703010354803030306c04a40c1c01455171001040b41c842c0007035003286049050030200801480220751003045c000003940460750b0302c14104800a56020381c194820382610207007144140d00e0352240d403241005102c040d0a203030007041e03030f416900d080307264582e51041c = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 274814037 1250 274812787 274812823
    0xb1c03091a041712090d060b1315080a08030112060e01150801140f0606031009091a0612070b2b0b03070605130302130b10110f010204080c04020903 65
    0x240501c00322050b580725009104a0b100c0e0450031018051000400036009090701300014108100d242c01e1000c07558088401ba2080da803290305c0070006031280142c02d104900c3c13120020038411044e52421440b08815031018610798806600d0f0340200e40400140c0707044d1380280c00100b400322401d0500750301030500c5590550180d4a460031420004210403050b108458413600207100c54580b0013201102200300f01c03003000401e12891700042603450700f90025a8003440344c4c1008440140c403070707440d8001c5400c2c41904444990811903c0ad10b55040306500c0c503440301080300c480780c0207240295115200c0e0450310441040b41404102481110036112103501c0441001030550700010800c0008009403107010442c6000e03018003000404e02c10301c244202e955111040c84016001c03482d503401d03c0114090660742d030480079a0748808101d5a078481c00c0c615010321483e51110344c044191140d56003002c070140ca018042da80704001c104803480c0d0101d00780c003050408840043e1200c00c2900480d0801038a41c0f1210b28603c = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 274815287 1250 274814037 274814069
    0x1a13060e0d020714090a0c05040e070305010807050a05010f0e01030b061c06060504060203070807030210050103080705011a0307050906060412031e0c020108010909030905060414130b1c0309 83
    0xc0c80000d11101e00d030340c00c2c0d400c650440340c0d034800221118500d68000c940100b840c078001001240781d40c02100c50402180303407451401e540c60605e0383c40c15400b5910000084d071501e004022200003000001d0141904880d06010303179140000182c503420b0782c03443c1c2c0418450222800e4445a02950103d11058400740c0324650313442c901200300c84403980e0482c0500c03002d0319100005c5080c03817150341690f0a44010350021840e00c03c46460b0525260800c81c81103046100d20174010300d01c8851030040a00940c864151262601e0052804600b034450031503140441074549403c040c07841d5400a41030003150020307130b500301c541e803034513004902c4500c50358000120407034500307078250109680600000c60715a0880446c1080100340c3c03500315040d456000000c2d00090400005100078141075104d0310f600c42c46810440b00301c603902d1000c107000e500030340c0c41070201080004d50004182408000d12110f6041d40e00704000109030304001840f1800d00c40d586495849000c203103030080501801d841c80c00f40a01c400148410 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 274816537 1250 274815287 274815311
    0xf090703020a0314060d14030f0706060602060f0609130620090915010c060203090c100228081b24061203360a0e01061b1a1306 56
    0x41c0d03100c2c25240340007a01d05101e401c20b0003030101a642c0510b500800e240c8a4440c1621580c0319200f58411400845c00300300408500c051000f4010413441e4171170800410325502d4030b0400790401300010600d486482506081200c10b54501400030340c45104041010540310103400c0600c0140b05403801006070300c0c8103980343c1c101510014080d1a00d80412a14180195940a01c103860f07140c0108156010500e1081d40a00103540f60700a580e12440710002c444d8800c00c540c00240481190181080244e00032000d100008507000708410310804820441d1003100100790b480d1070b660b00c6041d0f250790908040302c000140100d0241300c0888081d981d00c948045080c0305000c011103000e02035454511074506180c849865a0000c415983c048800f4900f0001800c215a000b06c04a034100c116920740e401e80b020300107400c0c1d4501c1070210103444014020410b41d8100702015007c800380003100d000800ca0000402c0001d52003040c0c110310f100c4020301101e00c9844007024403040e106400d078014261030a10300c1c01c0801c = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 274817787 1250 274816537 274816541
    0x90a0308190203120604020a031806050714070507030609060902220506040c0834020f070603021c0209010c080f0901020d09210812011e0905071b020f090703 69
    0x80008510650245110307010181d035680b00d030300401e090202c0380c4030010300c540c0b4003507010709650307c02810040740da0300780038030030588128990303038203c9080303590b4420f0240c2c040c0c0c402c0e42600b100c1c040044c0e40c0c0c6011802d40381d9940e41c2d501880b0003040640c50b81c0c451810080b0980050168942c00b40958414142100c3c181c0e13401c1000c00c50844403a45000001252032409014400e001c41607a242c2c1404d40c0c9400f4881d030351150040780b04ca14443c03c110f000c10806c200c14a103030040e1000c940c0c042c180140c0034510003410b10750f9580c00002058014401c402c540700c090b00d0080301c0000100341c01a81c2d80400401a80d501c1d104c6400585204400b040440419156000400d88440d01364280c1d030022040340310940c0c0c0f01507103004403108040586988044044c51070300515902e0f0180d06102c0c05d12400d05660040180241c0240d00c030300805400a507c08043c40c00e01038054240450700344114544000c00400801d80d01440b480c14001d104850019512079840c030142802029101d503032035182034800540 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 274819037 1250 274817787 274817797
    0x11060406091806050d02090a060e0901060608100302010207180e01090f110a03170a0c0203030703020d080a050f061c050105040305090a0f0b07080a0908070f0f150e060c0102090a0308 80
    0x2201c04a40110400d1403030280c46418244d910040071030000b0062030302401301001000b8462801039a0303800300403c0c20301000c03080b1440741450100208400e801e01600505004015205011011924000f440180c3e00802c03240250740c02c4e110b003032050300880b00c0d2030b401a2070102030404095103061000010310030b0111614401070b0007035203c200a81002c42c217200306203401e881f000d44481441ca40484984103010003c042c000001c0c600484072094a400081c1540c0c010241200540d00801c030020045d500702c3c5503139500142c0c4040421240c6800d101e003100520300284040e12a090000c6400c0312194030490a0302d0b003980041c000c0280f8601454040d2040d84a10081842170442602c002143c40141900900b6940f2401d202800c01086035900d5160f0b800c00e0400c3c0084c40151000401d448004001c801d0003410428001c0c0516032600c025032a91b0a03543d0400000b4600850005240b19081111080c0c2c1400070b0318140e54614180450500a001d2051000d03448011a640081030101910240c9 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 274820143 1106 274819037 274819049
    0x27050c2a2506090e0c070b040206040b0c0609061f29030403120525080c0c07141003060e01030303021c050f041109060303161106040609 60
    0x80007902000c01c1d5a584101440d2040001ca0b9111926400a11420300e00302c040c1d041644c00c0303071740e20310031094003402c1035110398080341c21921420704850090004d4401541c8605481811903160902620249068800c0c440803d94204003846148c1010b0110200c80c076129107040000f1420290001004da44080c0f0801c0b008441c04a010065203d83e01c290740d8045a0580003007194101e0307501a286840007961504205030044807000d5007502e4401e24105180380d544c40d800c801c0402d00c20517041c981103008400340000c03170042c0401404140c040444046c0d00401c1c403500c0803000c40345103200340d5080d40542c00040000c280641e0052192000c1c40b2001c1e1860070b0700002c0b030000c1d079400369108140c01c80110b04000521844201d0350640110444600c1e40300d040c01300000740c0c0c07030080780c0a04140c00300c000180360400c1005030b8050820880030381703240e46441c1d03a4400509204542d100302 = true := by decide +kernel

theorem cover : BRFrame.Cov 274640287 274820143 := by
  have h0 := BRFrame.cov_init 274640287
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274640287 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274640287 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274640287 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274640287 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274640287 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274640287 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274640287 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274640287 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274640287 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274640287 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274640287 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274640287 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274640287 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274640287 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274640287 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274640287 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274640287 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274640287 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274640287 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274640287 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274640287 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274640287 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274640287 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274640287 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274640287 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274640287 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274640287 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274640287 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274640287 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274640287 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274640287 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274640287 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274640287 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274640287 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274640287 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274640287 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274640287 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274640287 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274640287 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274640287 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274640287 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274640287 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274640287 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274640287 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274640287 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274640287 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274640287 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274640287 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274640287 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274640287 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274640287 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274640287 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274640287 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274640287 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274640287 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274640287 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274640287 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274640287 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274640287 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274640287 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274640287 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274640287 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274640287 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274640287 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274640287 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274640287 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274640287 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274640287 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274640287 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274640287 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274640287 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274640287 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274640287 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274640287 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274640287 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274640287 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274640287 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274640287 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274640287 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274640287 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274640287 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274640287 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274640287 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274640287 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274640287 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274640287 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274640287 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274640287 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274640287 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274640287 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274640287 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274640287 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274640287 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274640287 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274640287 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274640287 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274640287 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274640287 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274640287 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274640287 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274640287 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274640287 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274640287 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274640287 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274640287 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274640287 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274640287 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274640287 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274640287 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274640287 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274640287 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274640287 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274640287 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274640287 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274640287 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274640287 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274640287 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274640287 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274640287 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274640287 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274640287 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274640287 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274640287 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274640287 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274640287 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274640287 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274640287 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274640287 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274640287 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274640287 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274640287 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274640287 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274640287 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274640287 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274640287 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274640287 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274640287 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274640287 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274640287 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274640287 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274640287 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274640287 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274640287 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274640287 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 274640287 ≤ n) (h2 : n < 274820143) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
