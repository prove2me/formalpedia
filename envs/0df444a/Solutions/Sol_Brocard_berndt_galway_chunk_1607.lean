-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1607
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T03:50:06.872775+00:00
-- url     : https://prove2.me/submissions/61112ea2-5279-4350-be5f-fdc5301c40ce

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 288848920 ≤ n < 289028776 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 288850170 1250 288848920 288848933
    0x1202010201060f12030810150c02040b0a0b071106120a0c032c060105060301122d080702010210050c0d0902010e0d030e0916020619150801050105011d0904140708060f0103 75
    0x200071f00c0d0110b01180042c0014525a1b8882c80c0344001494600728948180c40460010204842c0e0b140d8800d0072100e00056400c008001003110505c174034201241c0c800c8500502595000301e0840304103020194002510001c00741d88000038648803880d011412041d80402c0300300b81680301c40b241c0760304480204248480742040200034010081903c01c14950f41c5800f620070001440402c0c001d0280c3c100c01115a10a00354000c070b19008000d460707e6025a200750300d841070a561022100301d000d8005e41b580a8060501743c45900e1142c82c3c541030640c5080050080100142040e0404070306208402c0103c0006464160382a04524403a46500c1c0719044041c0400201c000020500c01ca05510b1350f80480e000b035404111290031543e04500950401e026010308000740084130744060341d5918024001961110540280b4102c41c000e8071615014003400050f803c103c440e842e40560415406804107000450b100204501c00114805507486282c85191b074500340030f000c0d601114840078000050050015 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 288851420 1250 288850170 288850187
    0x50f07050a050607170c1b1f080406180503160c1203120c0905040213090b150304020d0503091309021f0f030906110a021e0105101202010201060f1203 66
    0x60441e5090000e81c9000700058051060f40c400030220040c0e1548500078001080a486816a04030b05691b80c1c4658002d807411410414000c0c107114075a13000d445100900b9100680f034456105688500d050b94451322903d0150120140d02030010f2031440320140071030400d0000d45450060710710909189221802e01c62442c0344c1c0c50708106400f4002042c0d480020380c02000070120710900351400304110092050a507460289a4405078101780000b0350401c2504004501100396640c1e82d03c01c1007008c0d010414410442e00125805800c03420400c04070340540717003614100c0081da120394120780c900554540400d04041c2d2040c0ca00b240b094842e58000110b103000000487d9010a20068401c1140340040041c0041c5d0369024020600d80c0d548002000e101c80c0350404070840000380501c507501c254000009503200003500d142c0c240e92698200c260354108042c064139004800c41c0b14101001800c203020210142c1c0d5101003241990359500c03000910041000e080001001c0781c02c118507211109040c094820311 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 288852670 1250 288851420 288851429
    0x809040f0e0604030807022d0610050604060302130f0e091002030403200a0203070803120907120b0a0f050a05070e090f0112030c0b1302100314010b07051504050f07 72
    0x1420701941d522040400544140c0c8035130989881e00250b252190b06034105071410308a5280a1007519901050f8665140c5a40b41c03800094119881c1d40c4d680d0b43c00e000c001c420b41c000da0742c0c410002c20007005007500c00d8014200000d0610003409801c4ea03110b60303110079010158003583c0a0742c0070500300328545206108680748425444000c1d4079602e001c0d80c0051941c41d642d80100c002d0944102c920710701c61000c00c82c00081c1ca03405002c4400d40c41d00e400c0d207140d80c0d401c0180c101c604100b514000901d01080400d1600865281e100d40c03418044080d9102441c41c6030007040c0740c5060740e0f07441480d8045c0c2e46078010140900c2d1306490005560030034500003048403290b129154011200003003403041411981d100c0314110b076001040c2c0b6040b0442c0d0701e030446481c01d0820300a041c4840640a00800c01c2c07904041c07984161085850800c03201e0900c00650503648104440903404420320010401414014028541c9a209a042d12016000f071a084000e54100307030f0307064486a001c0d0f10964100340e800c00200b4041c0 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 288853920 1250 288852670 288852701
    0x106020d14130504090503120c0301050a140a03030e030f0a03030c0324030201031d01090c1d0c0307140f0a170901090b1803070215030a051503061506090d080904 71
    0x140c03182c41104865040307200c0c040c0241e6035900040c080c44818000d031035000d0500d2041c036182d400c201451920940080c009c03244034190030340000031521600d15089010381c00c0904069425859a00c0c00d03900d4001e910800c0b42c040c0180c1246040280c41070182400191181c1c8000075100c58000c00101103418440c0300400d110300c1944101c900c0d403048038030f031000c6070382c2440c01090901145036006422081510160708035820900d00d8003c010f40070721031030705440040c12142600850843c400d00751080544064840314001c1000c20482c52140380e4488020049056052405043c280300c8080380d4071031140b2900140100d00c02c41480505100e1700391300214903100070b1100307180907203880c0703154600039040354100315040c40d96108145040c020303110007c2d00200000919603d001110b00160b108803100401c49180000282003d540389207010300d000d01c082c0040c0990307690b405e19a240481c3c00c820b9a40e102909100e1072120f580c544403011050b9111b100000d8440600800744411303602c4400300c44105 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 288855170 1250 288853920 288853927
    0xc090606020c09091e03090a0e01080606030d0c060c090e040501050f0a0b010905040b0f03070b04090e0a0c03120c050102030c0d060b0f07020603180a0807020f04060602030f0c030c060106020d14 85
    0x76100c0000e85d0440c1405010003005056403c4001c9495445001c45041e003084a004001030b2a01100030058102d8130307000c0c01d0342c0f620394a00c42055100e549403000400402c068119440c08500140e002d2200d070f0344103040000380701d0740728000084410030445040f14103a45501c2040306c580210f16890b50403070703100c92041c00203d4007240042c05e261b00a01540c0c1c010f5513291401d07400369460104801075042c0240030b94225940342d0034405420350284c054180c0203803d020149461090001d100c00e503003600101d640841d14119904c40b080d607407481d1034203010000051440000700341e007880214041c143c10003000d40c7c1c6480c055001401c0d00c0445d0311581c40c041051095500411601c0308540c1c02c00d504132807140ea07950300c0c1d4002601c1006001402402c521070720700e48504004040004140032802200d00302c15071034111040109813803090043c800141c000340007100c50b1400c0344c03016010341d641403401d49080c1441d09010310f1901c0d100340d000c100164400c443c96004103400c4034a4080f145c02c0440139524 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 288856420 1250 288855170 288855181
    0x9060e0c01020c150d06031a0402010219080409020a0c060c030522170903120301030303051005040c0c080309070302030a05060115050a020615010c0803150306090106030b0f06010c0c090606020c09 86
    0x8041c1c4d1034881c4000514000390302c20301000c45a0018000d0f50b03110300325520b0004d01954200c01d03024115070072405071081c04829808641300e0010089010751102c8203a00e040d0a01100d00065000000030b9001e015006540d0800180a8040c07541241d8085d5000501860901c507550307052921400922000c0d030904800300c000c9280d90700c00707403070119082c1e100380d23501c0c142440401e10304600fa0f1440030000d10080004002c16a0541010313010300d1806a50513042500c500401c000ca4007414a20408940c1d490014000030707061402540e8054818029903010603070f41c0d0082402c11404080c101d660703800c5000140300c250b40c1c3d480d541ca0048014900780341003030f0071203030f02940d541805801c2c4541410710403d06e8038039070f00c02c031010003600c0e5010040b0b5880c0d00303000030403140d0380403c0c2c4c801d940700340201800102c8090052242c0c204507078210191505035120b400c04031508400207050181000002c410b0340d40460851602c403c010002c0e01d03000200c0d90b150500c003d0420900b00c030840d01ca08a001d00380304 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 288857670 1250 288856420 288856429
    0x7030b030a060510080a1202100216020114090a090f0f0e1e01061a090f010e0312090310020c030d0f0606121a0a0b09011101050f1b070609060e0c01020c 67
    0x480c842e0700007000200b903200c03400000d11545043c0d21460381c1e0310580e01e01508001d13400c1100c15242c00c42d07400b06c40ba141080021131040c0d000343c600c04800341e90b4441000c0702644c03060700b1050701c029680301e56611300007042000c981e02201130307000090401c1d03d94421481a0079240300350344c48000b080c1c8082000c003401b18409034594400310074440100501403000001c182087d880740303009013001ca5070654035282e5282c0b99559030300640001c51241c0f24002400006500075600070f034012100902420b6035118101000715180c100011b2240c0501c05d04960000300d194a00c01042c030031000c0d90086488117808034071401a28001060208041e041980c00c100d8103801c030b400d40020510303180c804900d41e01184030f0803041d1907060011650010810b140000c44141950040a509400303a0b111901407180e0140039090310410b86018503603c8060300000c015810340c4500104200d0040d0246240a40341d4580c034080d982d4000382034400c1d954404801c244010100b1183c1420b5030b081c0041c200d51145c000014 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 288858920 1250 288857670 288857683
    0x1d0a090c15050903030a090303021e070b0c0f0d020729030601050a1101060f0510090b0306040b030a1502040e06040c08180a14010e06010506040b0702060d020706020d0c0807030b03 79
    0x580481c4000d04030082154059029140c10303600103000c590301c91880ea54001c0c8500608e20098025000703110000307440703c92007030300d0007000f480860042c540680341c4800c0f000c03668000710174280640035210507410a03e13414040342110a0603940205207042c103001090b2640807401400c0c041c1c00030007400410800c002034060360707801002400c0c41911801c4000d401e64006420045040840d46004008220341d4001e40d14030f0305440082e82c01c141082c10408050711035034414010810104000d0000a0081c81d294100e14140c900103000c2e200e04604c0d80d034407401900d0a10591194498001c1000d0145142e41c9014a80c08901180c050000d281200000342c1540005015070102c2e01951400010307280d020800101895400100c490fa810050010580207203100c0c0e050039600d00401000103014a0024241e40503914400d12041c030b0802141c0c00c21010740d0208034940782c0d254003440000701180c0c841c0f0140c01800000740020855400c0940002d0450070010040c00906107080340c018903c0d100010740c2c = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 288860170 1250 288858920 288858929
    0xe10060f0c14160602060702190807081b030415090509040303051b070b0f07030501060203040902030406110414150f0d0e0a020d05070f1202100e15041d0a090c 70
    0x80d160300388050400c580d0b444401c01c1d42c000c0c188074510b040f02881065443d080100c0b40240c2c26a9090348503d0404ca88840400790b108600390340c54600000450001801864200d2044004d1450510b48210341041c003c10349621610a030000f003402c1200c0c00415904100c91855490300c0d4600a00300381c0024507281010708090704141d42c034000104000c0651011440440401e08001e48071005450b040340d0300c004c1150900342041181003c51286030007030086d603059031070750f401460826041120280c0250130003001996800d483e140030303030000c1000e0360062016003d4030341c10f049030b2080a82400f080701c0008241c0303810a0303420401d90307200d440014290343c4000070000020a00c0342504076400d1034041c3c0c03250081d501515110144c001c02c01e001811a049480798540000c12039a9480700c050b07850503200019402c0346889520031212441802500c0e0166401044000c0c4602110a1003025410035040300d80789503084040c5a203000d44110030281d101804100174000c103007466a80c170345850580d104 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 288861420 1250 288860170 288860177
    0x105040812060120071707050306010e04030c0c06080a1a0a050d030207030510051f05060a0c1b030309062705060c03120f0609160903021207030614010e10060f 70
    0x890782e0780e8841c2945920050b201c0d4183c855139250200c0781e42c2c0761407a5100e40b100d00c0030308000b8200c0c60702d008269081100d4000340645240d07071800388600e071481c1009104400700726020494a00148007021131a01805003035903084445c0c034181210074122410458540c80d045a24030b440049030390340c200c103d029a0002d554041d40d4020740c0ca000c2e072908900e604010446e00802d000c1020602e11540300f140304500741013045c040c540d6005800c040112090060a8020314100b140046950140e0204810184158007a9240080c01ca41a48003140950002c40000340748243c10400711394841603142c580010b83c07910184014171501490000610b900c01c0500840b00890b40c002071030400d00c15100b82a44175400f414003460581d01401e0300b00801c072681482900c0d0f07a804a000c421a0000030310a0b1000b0b0740315038803024103540030049107000c0c4080721742c06486420703404000518035000c0d1110003480220240183d505000c180d0502d0300c030003031080c00032141a1804005507030380283d09880c1c4014604 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 288862670 1250 288861420 288861457
    0xb010b032220180a0f1409070504050c09041a030f0d0206060409080c0601030804051504031e020303042d12030903080c0c1203180f0607020112140403090f050301050408 74
    0x240440c118004103c2003400c101c0c040f100b00400078034240c01c031420209881400300400140740030f840c010200191040006540500000e220300d00301a4000f6800c600550340043c100f440c200c000905641601103a400310511401c403080c0c0504041048001d0380c1240c201402000c040250025900d00005000c00d2041cdc0e150b01c81e076010720007400101c9800789074040030755259684900700908a94046c1c8030344d0f80500015515001d48400303003010741d42500c0d030101006044410b440800c00400201d890280d0380350100b0400002c20903208010301010314051a58074010004404401c1c45221080d40300c01001c0d1100020702000a6114203914156070748000b00c0d5440c3c0780007410151a000c20884000c2e006400e02c9881c0c402104008040c096084c0420205006606002c0134882e04500044415030841004d1045100642c090030044210960501c3e00207001c001d00407400c0720310481590248e0200e084200c080c003106455280d0700018040640092009080995078030307aaa00c02d001601451800b0740c3c = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 288863920 1250 288862670 288862733
    0x80c10030b060702030106080601060f021902010f0e0405330f0108090a08040605070605060f01050415030f1131030b040201020c040f1a0103090f0605040f0b010b0322 73
    0x2c0d8151100140c025000b0819291103089207903994200380601c0d80429402c4200409183c0300190540440300c0108034580100c2c410f074015540350711035088800a01400c0e82e09802242c41e9842054071070403d0304c0b08040b031181c2d50900035013040301d5000603503082c00c02d40d40c52818588134090b129801c0c50703080c40c0c140e40681e1445400c1e82000f210b810f0040c059600010000b43c82c680c00000380c400b45010300c0007005540c5444040003030f9514800d004c07030f0205205100801000003800c80c00a114400c80c1008140d071214a9591000c5800340416045540404180c0c0e00345910f21341c801800100340042181c0b000302d0414401c40c003615580c0301c0204402c010500082c01c5900c24000d04074002c034080c2c828403194882c1036079038001d410000140380b01241c0010809100b507210b8040e00358070303d402c1401105071489640f600405000028030070340b20030301401060f070001001020210f000301847c00242c0d0710f904006910403403092049000700e070711071248031148c4041130b003040c07211540200d000043c41004518 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 288865170 1250 288863920 288863929
    0x11803080f1305030616050a030e0102030c0406032d050c04120b180d08040b0a0204030503070f3027170d0c051c030207140115080c10030b 61
    0x15040100314003004212600c030707800e0031000340c040e1680420985035080e8640d802c1c5a40c8940468030b81e444605000320414081d8020802442d000110740340100301c02d0200c48403d42a41d00075214180c04600014042100302d0345480380556440307607000b41464405181d441c04500071009402895940d81d140040f6504080030000c4a0060880c4001c0d4400780b41e080c1130001d442d1408507008101403410920a00e03450702b0200301013100007900c0d00e60040c40d844603107a1a51004006105610b001d60070007021000c120208041c0a0540c403501e801401d41005240c01c3c00145400001a00320001d400440030030800c1428a00e803e4921600c1c08200f400f00f0701002e1045986455244210f004401302c01168007201807851441d241d140750110780f0900200358007241d40c86000100a0103980040d030321101702d01e0304000e5440d0307000e401d850058146034a90702c80c5007a80041c428000d000ea99075071031040d0903000c4c2000d881c0c001e00d07074000a40b00911786040801c90312080001108100759852481c07664580c0e5 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 288866420 1250 288865170 288865217
    0x301090c0912150e070605070f02030a0b16180303050d050a0902090a020702040b0d1e0c051914030a02010e01140403140a020108090703111002340605090f01 69
    0x200840188209542010019003160340344000f503003420943c003282e420500090050894805695076458554262608220720a207440120b07414003d550034140403c2c4204031081c01130b0740c0c80d41240518010b00c48050403090460f1312600040e40d94040810100b40c00101f600e8099001d500701107410341d00c0f160103d0051441010003544080d08106210b01807189501802289109403010011071105508001d1401200400144880d08070f89000c50341490410307007034040324414020350303840030f450b00002010540020800d26414090800410099140300b21180320180141c0241802d5200c9800090403804401820350600c441c140d134400e41664608200e400540e009111405180c945210030b41d1174040028080e0700142c1090085400128041425811a68010500c40e9052218018440d03113081190609080d40141031020560200c0e168484082c0d44505030790849061111541800c0034501390022000c114083c4080040e80d103c2e508105040c44090030140310740307240440a0b0b01f0451 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 288867670 1250 288866420 288866429
    0x17060601080a1803090801140609130804090207050d2a170c0f010b01031532040203040f03020f0304030803011403120f03010501120c020d0c140d090509010b030702030301090c09 78
    0x40b1031040c01c3c0d050503845030a89060b0b6240700000d018640030300813803007807001c1c003603030f00660110741c0c1d002041e03080343c20304051480e1501c985801ca06003583e801c40c410485c2c03c80501075810350000558800160781c4600802c45520209500c06480609100d540310068003010004003c20f04400c4414060300718141651100e0f01c040e81110004105007e200f4041c0c021514078601103030a242120350012424840c03001074400781c001c1064800d25040c1e200b48182c40c1c0000001249a5a4118041540311030000354407807406005039415034003c500d0b000740b81c4000c0b40e0794400c00b41c000740410300014501e00304803411648400040040881c500300001d0424071010000030342c45d0350000e4401c0382c07080c0d5100a54101d13002600c600e0070440342102e619050b16400c4080c000140c0112030b10340804d40c001c585090001e4042e402c060081034283d40364900c1c0c00e0a204da10740100d07070003c408000514000401034058000c05100504600380700401a54a00041c0103116a864494191070903640c03181035a0740052 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 288868920 1250 288867670 288867701
    0x7050a060314010504050103031d240c060a1b0c08040905010810050601090609180b0603070903060b04020c060408030c07080d020301080c0a0f05150c01050403020c030717060601080a 80
    0x8a5503000080c000b03040351500611000d041000000755440c03d0f119aa04894143c1c840b54003c0d5008449640c61207044002183d0120018a00b10f582c01203507204543c02110200c0b2540e0385000700c0c4401c501c0c0800c010b0a6a15040c1000084442c416820300c8549403900141080c501c010414070b8084401e010301d4000019062070030000003a01000080c64481e2001203100401203074580c00d0045400205a02616010449070181009014242c0d10f0341c48182208940005141d41501c00041039a8010b5954070006001e80d2030900a100a520840071040c0c800c843c2107243c90000c9401503181c880040c0064003060002c00001c91050030501101c000c0343c0c0c070040c1a907540024985420081d042805110038901c81e1858405c891f081c50100c81c0b095840d07400210010601c1c010070021038041016504070020001d00c506542d8040074001c25004902c29006040824074071418580380c41603030307030042011100c0c0300103910400d02c01184031f0750859820700c1c00310a2940d60340182e2000d0302c083c1d05d560040 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 288870170 1250 288868920 288868939
    0xd0b0f06030a0b1009030b070e060705150604060f0e0601080402190e0f0108011509050a150305030702180c0a030c030b0306040b070809030a020c060d063602070b180705 74
    0x4003541c2d0f002e140d559400b00d403406501000702c00111190410307400010a02c1004102040001e4064044000300b044010301761841d241e41640e13401e00b0410002e0192642100c02014402e03245428061400588010302c6407005032850612070b25005100541414180041c8034007003020754803001e4400d5401600a0342c04c040480d038034090612000302c121101006860000008150414180074104400b10318000340a141030802c0502c01c01841c1c0602140040c59a40803184468a0000c20800003940100051070f1100c07202c0c0140a0304804035502025007106000c1000000307011b190030303a04c400c50300d80b4001408180300c010640080142c400c40319410700c40c0004003c2008045074505119150555800406031201a40e050341c034000c03180703100e0260308480d441c42e03040e0500038050040071000c0c21021441c076a07102c440e1403100c000c0054543c0030000001030091070b40d0f0b0741d8410000c1400028000c515001664683d04c400305009800d00b00c480413014650340082d941004181e0151800a00d034440 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 288871420 1250 288870170 288870181
    0x906040212040b01060f050921030d06030803090105060301090209010e0604060518040203100213060c0c030605010e011a0f030432030d1a01050909101a0901230d0b0f0603 75
    0xc04503c02d205e1600058100b0089a9001340b10340d056414108000c0c14804c62440704400a50f503040c000f2420320030078802441804a038418a005d03000065001e0359138141d503403d050040a0950300c00901c02c5000340c2c105044000180c481c00740241c111000d07900c01095548540e0005400b43c5156071099900440210304071000c100c103042007a009510032022200c5401507110010f06a00a44940421105518a04100140c015001504040d2190300380c14907150300c954a043c110350082c1c100703184240300030005111810020b000190400e100d06500f0742052031400810366103200040c0021320948d00c1c900f800b2480d039400000046880c0d007050090b10b100c12030403071031a9250040d0480780102420040000f201e590040d11a030005001a500c0034a0f00503a07000f40440e08101400a0008215051001801c2c1ca41e000c00d04191a1a0b0307400c003650798000000040403620070408580c1a43d82e964000070000e108c10781181d4231420181c402241110301040005c0c1c04111016050b9040b500001c208032 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 288872670 1250 288871420 288871433
    0x80307180e0f060d0819030e0609011b08190c03090210020c041103090a06020702060d05191a130e010b090a0501330c020d020d0609050606010c0809090604021204 71
    0x80c450b9800b1141603195940310420011003814a500141420a081002e4001844103039901c0042460a050100f0303050400c9800b103250081c2111044126552030346003812406046000305000861440c1403452400d00c0840c80d60548850540b071203c40795640c200d003046901940252400c141c0003807640c612422440c0d4080d444000c0c40003168883c2e4600602030280144290940e4000c0701e50800a0085100e103a854100940c0518000d0760b00040610010403a500e040c000c55104030511100c229070a2107480401c1c040d259100405002c9089010060241d41c0f0307040c5d0000d840c40b119140208141c1600c07a00d4a004102c680c441e42d411050a0b010000031079815000141241d00d0304180d100d07003085119080000406800031811080405c4001b6480184a40300d4442c450740010152000d2070342950004038210301c0100c04640061302e6250313803003e220003884510303480802800d00190a42050b521017220b4841c00c1505445030f00458089050782d1103e6041c0d4289441c01081142181070504140 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 288873920 1250 288872670 288872699
    0x180f0c03101a13020906040303030605130e0604110a092c01091a04060f090f02011206050319080408030406020a11010201020f0d0507020a081308060f070c08030718 72
    0x100d01038440e00c004405500600e10800d2110000080c0b40070354101942c0c1048450380a00400e40302540e000e02400b0510740e034680003400254801d8900054503880c110502c01c100301782a041e2544030785072400c031105004000c0743c0c1c0d0780e106510409000a020b000000505602a10f402001086260a182080f501540d00e441c00300c00c1d03644004074052417090120103003668082c0c11700404140c00c1c0e1f10600300070b580040301c00e50002d100790380110318850340700295402c03200c11040c2614221090082d280965800015041811000440601c0700c5800c007800b09a44050b90180001d03682c80900c103072410b0208203026900505507100603643d46139030711480259034140381030302a500c0c0d012401a4550660052003150400c5440c080481c3c2440c07a51400c110013854018030140560040300402000903171502e0051119a410607241c0074401d041105076460004003c1c00d420044a01c0d20500c8000c5402c0b060704203c10354081c1c9072a41c0d941d120f0700d08030f401c200c1019200803941c054850219001c1c0c26401e18 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 288875170 1250 288873920 288873943
    0xf061e0e070905010f2603030a02030609100510050903031b0f0f0d080403050a1209060e0d0201020705060627010605041d040f032a0804090c020f03040905180f 70
    0x40740e40941c0c454010300c0443c0e5082c812050806400582000b20134814040d04024042502524860000b94140c45095510840f0f070f0000155002040240070301d490a24180c04c0280004c0c1030004c141031a001c51080031041890318107000022030311641b1554104101c44510708000c61401042249102041e604e403880e00c080203081c000c14950700c1d507610307000450514560180d41d801d4880e4079141c40549542c1e1040018504118000b600103139002c0d2580202068a40b00c1c810000d0180100a415400c101c4000c040400310b900402003040468070001e51260001d20840b00c00411f59103070100e011807035200c40c400c21728040e182800021420b8008024104507400941802d00c030000c40104850440e01c00c40c2d0003018405800751900109100700d20103800d108440d5624003860000701080c40b80400070100484203648001400c0c444c01d419802400c0408145000804c080021003003100c0c1c807401a07018408410350794a00103060322000043c02d00912125100392049180f844220f55100c0d141d2442 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 288876420 1250 288875170 288875173
    0xd0204120f170c0d0f09031e03140703051b0703150e0d0809060a050702010b0d2a0b0301030f050118080c07051f0e0411120405071d040f061e0e 63
    0x4182e55090404011a582c0d0a401809043c503483e482c542940c102402c80420710810100c02c1000c000940700d199440c5052516403188034480405140042c90505155060400740c1010720005c0c0000e070300003091f18003041b80040980c20f160304081d0040d10705800c9a00c0a412009141443c9a845040c6d52007480440e0404041c1c071680841000309503141c00c000e441d0010070764005800034408000c168420358015805c1e00c00861000810313400500000407101701500d02120401d9104051000c410301c0e150308507551041c00305102c1c50060401410f02051002600744040003009104004082d071114407034202844000c41c0d400b42d07034248260b040d0003c1e03d00710364910480001140030302d468a0481c0b41003c001c43c0c2240e21140c184400c90304a614520015040b68075a5040301d40c280351180a00b40c0c3c032102c4106099a03240070b0900e07600d8045140d00010307071501c0c0c001c0c44003050a240c500301c5900c260000305500046050785010303401000d84603142c500ba440c0d24841d51030042c0194002c2c1890500110 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 288877670 1250 288876420 288876443
    0x3080708130b060603060307030b011d0f060f0d050a02090c04031a04022d0306070807020709020708090d0302151807060305090a0605060604030602030702030a03110705060c0d0204120f 81
    0x1c0124181d0820034028249408560006240e46002c2000b11b030302c00340160940e2162035590b910384145000a8100d003410307041d1184002624415928503c0e840380174011445078904000703002c10340c01d00030382d52018028010510f200c028440d08009130f418955000d8504003082c5801c2e10020701a410900046444118106481c0c00070220f00415a010341e03001403a1802c0c000c0c4003d24070182c075580011407480041c0e030203205941641e042c0001407060005031904042c1c0d1501050003410240290400f5a4051052007440d0203c0e410b90140c1d1000142a2018416400d490805a18150328090103070384003401c800c10810f9100c0f01c0d0540903061440c040032614080d0300c1d40000d400b503031011122814141c0c403003841500401c0c1d441d00050340100300a000c151805403a07031200c00a9034000c44e0300301c01503400020100e011580c5032261116900500c3c00480c184911656050b844000103440c1c849414800704018501400d0783d1b04075401000403103103148001d401445c0104100321018000d0710049010f0 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 288878920 1250 288877670 288877681
    0x7080301181d0d030b0a08030412020f0307030f060c031d010e0601060e010c0609020d02100f0212190806010e06070b040c1a030a050705071a15030318060304060906060303080708 78
    0x200c50070840c02c0d10190140c0740300c03084840c00310010520305800c40e602221010b00000c81600500042000e055800090b072600311190051109070246000740602a80c00f81000300082001225200025075211101140803860740030304502412028491000d04549040380b41c104035015030082440b04844030503200b82c3c0c5c1e6111800d9905002c1400c00d00d000c50065070180b000504070703a00c54800a8801000e050f0800c95980228130350f41c215503014000b00d488040c0d94030b140b40e0100040b03c0c400a04540c406d04d070005002c4022182c4408640c2041480b140c8804074270668000e402c2142c8545019001940358295820a120010301c1074030107480440722036001203040f401c0c03044011502440c04403d6481e64598220110040100070140c01c2000320a101d840c0004150180507112804000c240100e2070409500c04400c030b50703203038140038420b41c02004203e10b04482d82c0d41a0030342d5141111041d0316035480c0e0400c0c90150401d180002d100ca864040f011040503042844d103801404039030b50700500c1e55610b = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 288880170 1250 288878920 288878951
    0x708190509070b0d0f151e051c03090324060503061b130302180a0506040926040308070c0806150904150905071401030e19080f0708030118 61
    0xa454400642d00100301c14480c40303031003900519500001410001e51960380407200421580c1c08035108044022110007040050302490390190740503000c0141c011010b241c4400140d00305000004403e0448954628206160044c0c50000c0156005010b85512103610380c00c2c0e1b01e00c805d02c241d060302510b10303000f0042502d06001403e18400c0604007820a07001540d20701219403900500074641103070030081d03c0400183c030707200650f10303551348600743ca143c00e800d000311000c1c00c4c1c0e03600510540c003031403030020301e00c0105581100300b8404120f2070049a0814060300725215507031285400c00303003070850000389000800000124090440e20890259111501e441d440e241480024290b4540d01c40848000300d00400c140c44d4000f0310040e6280c0d03000035210120355942e4140001680700b45035520030403000111958060107022141c0301c0034005084d0114602898094114514034040c081401c0480c0c1202404840c00445e0300254020086540740e694603000308032070080501344140c9035410314110550320003e = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 288881420 1250 288880170 288880181
    0xa080309180c030601141603030605040e03070f140307140607020c090c0a0813060f0603020f012c04021201030b011505030403171504020d02090a05030304030503270405070819 77
    0x101c0b01185455a01c880004441e0400c2045044810780030070044200c40710010080644000c1c03103070b100440c06502d01800c01003180d40540c1c0b4006150070400114001402083c49564607c1d03001c8001d8515101c400c0c041850f6001e540b600414a28600196201c2000001041c1d44600e0081e4200c65540b442c101c140300402d1000d403010b4064010520102c0c0300203029100c1c5a500011000d0a65030b409819100d94013564000e11f103580d1030598403201401982402e03250300d80c00c02001e0900b05200340980a1201054503080d480907800c01c44010321108070b54898045906a88000b05008090758490500a00804082c4106103a086089a85140141c01602603d1086405440d056820340e0002844264404024280500c2e03641080d1f11100c1c65480340301a040a095081005072603000803014403da0703500c10b400840c4607034000e12042001a50010440e1a0318070003070900340030152000c0000303460200d950f51080d0f1081c100320811101c03e0788501ca481c8107038109079003500d56103060514030007190f4 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 288882670 1250 288881420 288881431
    0xd05040f0f0e04030c060b09040f0b010509130201031e050c0a020d02010b0a0302010f0e060318010e0f0c10030e0706030519060609050f0d050f030406021c020d08150a08030918 77
    0x154060b0000780401e004200510030700d03015040c0412408000c0000403013140040b40c0032500501c195401c030040c4603c0d54081c0e8090141034810180c60306115409102d55840e40000904140d00c40e1010003e61001481c0e146400400700303400d2011381490446400503400200b04d0000603c205c25130034203ca03105005603034010714003510700324070541942c004541004501102c5000d121000c28003892585600008501c102010300b4140d4104006940d00e0b070a44d500f0801041d159404003120048800c00070a19038290030007201c9080c29451000380a0b80907080000000c0800c1c0508400000d03d1034040d00030b83e108905038204042e03080624a00c43d0121103450040d68005891480140054101118143c0d01c0007002040303000d000d16140c0e500761400d000b40400040580010404001c001e070100800c1e0b4555a002d9002040b070040e1010095458100e420305504010f001404591410b125400d100c40096014140f8041c0a4855038071696a034032a00e07ca80c00741640b2501d00002140e1910100c0c05107 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 288883920 1250 288882670 288882689
    0x1106010603141b030408092707090b19031d03070803041203090f1419120e031b1005070203011b09090209030c0f120607090602070b0405060a110c030d05040f0f 70
    0x43c1c44d90f44801b1159002440b103a500007400c650108070100c24085244440405818012554034000c1c000900b540c07801da200f404600000d1064401c5503d0303003000000f0820780d03498000703001c0220802200740c0ca40c0f2121b2041c0140030000b1840c00f0302c1070140c011440742d40070f040b190075803c2e000213003101141c0300c0001c00350001c0c01c108490740008401074901e2401107038660480d410191410710b00c071500d00f00000d04841c060004040400f2180d0010300c14421440101c0140960103000d14495201107000354038140305600411200d002c2900403000e032440c05401034000c01010041c10095410024002a1000811141580015200094001c40c0d190701d0b405000b824210b086c0b841844000322540f09810360065080300061104042002302034030800840c6c3c0c403000b105c0e14101020b410400c0c0e5800858008200308414011a120360303044030078400052500c8200c54070441da11030300b040070603000310341e043c05210349201031164000041c00c180c81420030960211035079544860390303101c2248100d2810 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 288885170 1250 288883920 288883927
    0xf06051609080d032c071406070803010e092e0b040b010512130f1a070810050108061503010f1a0306010207060810030b010312030f0903021c1106010603141b 69
    0x42d103100b42c011302d05c01d0303180c0b003901103032240007600b000148102d0109421055201c0e080402400110b413280c100440d8054645030318041940c0c46004461005014426030500e500c00130400c035240070071200841c4440c0924499816a6242c0c5840084c468003070307250b2819003010a180301920703040c401d60f00c40c1c010507103c607850321490803044078401000a10380341c40d01c5041d040c40e10125202407150003280388035518000740031070210310030290154082d01e04820030860b50208040d81c2c8240d12500140c1e50242003e04241c1c2e103400018940180d455010143d602d40031000049551582c00c000e0142c0d8054540310000b4800110000c2160000700d40850041e0b118000400c8418000c0905a0b0095003a00c240302a05480307490311440014207900444000000b000b1250310142d042c400c13030348c44900341042800281c49945000395070b251100080c0c0308000c4070032030f80c0a405015106440301c00c1385031429982103694814001e00104405172000c4005100b40d80060040c0b00f07055141e07800207071800640b47c207 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 288886420 1250 288885170 288885193
    0xb010314060c03150402072a06050306060a030203041416060e0d05030d0b130615170411060a02010f060b12010605040f2c130507080102070206030a050601020a0f0605160908 76
    0x1804104d0310402ca030015070130401400031841b6211b05030302181710004442c212411005003114610325581c041c1b4100300050040c007a00d9a110800ca8001e00c4203458090784944983c14035500d100d605500b00b004500c20320304a40241540c1c000101c003100c005d601c8a0f281c20344c2c1c1c2406e000b04200750700002003417034000704040c03d961040790340504030b0900058284404102d41c1b000c2c0004407580c45d0000c50a0b6403200518500700d581c807404c00f0b0803507500501d6003a45810541c0e100313648030914200540c8118400f003225480c0c14402d41c4114154011f100003403040e030782d4815200150b50701810340ca822000c0901c0c004160301d03001e04100c800b2240d00040910700780d443c0000d501403040b1100550000042e802058003012540d44035007501841d0f56005502c2c0b6400c2c00c1c50030900e40245548200d0580c1d00600042c00540c1e2100c0a50f6484521204042480c1d0381741e0b80100d06000414100030140c4981c8a0140207110349540b04900c10041c010f85150500c1d41c0701d9090340d014985204017800c96100e90008078 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 288887670 1250 288886420 288886441
    0x6091103220807030201050a06050d0209060f01121802040c022413120e0406050306060f011b02030a1203050105030601050d060207031e02030c010b0411030103121403040b010314060c03 81
    0x2441c403803450708a680908039640e8240240e01c403680c1900140c0d100e20a0000c11f007030306d00c2140000c080803101c6112800703041c2c1c08940200c1004000a03c81c140366084d2003141d0f4041d02c4820b4150001080c2001080d0315051074007410f15024000b0303400b0fa840e141051041c2c03400003d00181c140010741e00000c40a43e0501d40305460240100415041c402c410079413400105a102d01f03030b0203621107446561004022509000844007181d000e248694001d1081c8030064888868040c2010801c1c42e054007504000342d401141100d488600035010310900e8040020300c201c408600c0b048840e50394081c003d503681d03a410565101d900f80280c2d540200215012000204a54010600d451081c108240b1904a000d0381400b200002c25070140980c20004650a400e0400c0c07041c1c0074081800c0350100034601d80d03c0c102c0040c90005000080980f010b45c000b0980c40781c01184204d064240246050381c0e21300d8245450004500d081c401180c0c4c0307000307440304441c489602103146442100401189070542c2d59108042 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 288888920 1250 288887670 288887701
    0x305060109021222021f0f0c11010309020307030f0302010603031e020303010e15150c0f010615050903030d02030a061818021314040606030c120f020d03030204050d11030106091103 79
    0x152102e0740703001000040e15415501c3d401310007010641d01191b1100346001e40352081c0c0802440804ca0342d034201d407000403600a0303401c40e90300c1d00f0328000542130b41c54400b10785043c0c019007001d052500704e03e07011020958150055020f60b440382d030314195520a0b1021000220000b03040c4003000d80c0040c0018001c0000042203242c0c04035481c203207400700c01c0651011860b65440120504003803d0001141c0b40600300400007500516003150080144a18150401180001c44452282000000600000c1d10355042003074598090a40c001159030f410300e030800c0d600800051158000e184d05c00c0001007412000c6101e4030165440c007241200304200c080c1d00700000c10440c10481c149c0340760394003d01d1803201317080c5c95039a2040380316100003c1c9041c214245500c1c041681c2c1d20040b06103000c4804500082c1200c001d00d507009a069079030313440ba20702524094000e401207420a51300f05508500e1315090103140c11800490501c00d0700200116600c65002000390b034200d6444240c8030508101041014005541c136 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 288890170 1250 288888920 288888961
    0x20301081c0912020a1d040b0702031218030c060106020c030d091d220b061f05071b050904061401060504212109030b0f10090c140c030403050601090212 67
    0x440308040d02c92034144000c0030b194070000207440301b079810001080b41140701150001d00c3c1d40001c60401c0c0c1c910001c01001d1000400d8200600a640d104100f0510100160340c089564032042c1c0c2c1d00f543c2c50f588000e507141e101200442c0b10740b160000001e0a140184000001c0d6425210000b82d80300d4818003080b0001d50281041103540b40d841c0004c008482045400e81c0200e100b0400042d45081c00f9040140702018085580a913450b44440c0c0401d00f80c00504035105154845843c11032070001001200d4200e119520043c1c00c80c03000700410003000401c0c1c0c0104580000e4849440560b40c036124201c0e52801a0b014407100c01074460612100000400d1407211641e20610440001003106443c407840e038480f03420004089181c0350710030310412000c0716480c1e500401a8417020340030701e0030a01500d51424503101e6904180d640d02c02c24941d451003152824490781c5480c260a030784109000a0a80e00c0e4080c0c80151600c0c0224000842d100d1194001c8030017031500d005000f89140c071460060003042d0b07045080d = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 288891420 1250 288890170 288890179
    0xb030402010212032e0b09120f1509010c030e060a0b0d050d110d020607080f07110a050303011404020c030f0c07120b0414011509151701020301081c091202 68
    0xc0c40c114400c01d00540c881c1e0039001e824000d03180c01400c4041229411105c1039113903080b8003020721006400c4015219102c4d0b0454041c96403010b2289078034144086040c0458044c003c540d009108040100240350007401d203140200041e4500c09000c808548455600d80e980d84c02030000704142d0202c44d0000c5031a494020f1406007403048036940c161a0214140880c0b000c03035402680001c0481003405800814019400502418a056140104150801031136401c280c841c0c1d0000ca4013051050600300e0308484800201c42004800c0d080a0b90780381c01c244559031150210000d408410305003402038a00d20000b100c021400c0c0300c0018141c080d01c0e0044000c0100c1807142d0203002400f254030804102c000360041c5904001804c25042a5100d944d000229001607030401c2403080a08108030b4023401180e120040000b00903100d51a0001603d1055000801c1c4c203240402c140c1c18401c0641c0150704850844c0229210b040348480b130000350301d454a400318041083ca80040144072150021030003a284005c0 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 288892670 1250 288891420 288891433
    0x614010c02100807120f270c0e0c270301050601110307120e1906120626071205063903220807020109090515010c060f050f1603020708040b0304020102 66
    0x1503004115045040032210558840200e500d082c0740b44c003d030960500c421110045560200e460348c000c0003007148940c5650060310b40004420603c241d040e10411245447d1100c1715a200c00b5a8003540b20600e40038a11030751800300441c11640c00342103200f402c3d640140203107081603039035110032150544640c105404d01400141e075080790780d5a85840381081040b5030000b141241000c00052900c0080385050f0b40043c0b800c1c000380564128594800c401274400d250700d034a0040d140e92814140651a0711246075004880300341420401d010401501c0781000c0d038510300780c008020100703602407250400d1045100b01002d01062003149040c0c010341e400180707103500064900b0500304050076207998280239184510041095030442d03911103c02d20042000342020b00c45403d185111706402c001c030708070341130611903400076860400c421a0070620081004410812143c41e00c20283c00f0781c10300032600303064400310301c2e081045454003034425035a04c2a000442c460608d03081074259109544064801c0c2d06512560 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 288893920 1250 288892670 288892697
    0x70503071a09010e030a0903020409060905190b060306040b1f0b040303031d010623041103010801051b0705033a0e0d02011109060307051c0614010c02100807 69
    0x4807500e200d10041d004909040703150464000742100e4036910901866081000441200303603100c080d50050300e03011100002c1d011010b143c40c40040c58940c04c000d003d0f005038110039862f24034411000000ea80940d105074501d1396000105034461760221001440170010b000440e01c000d0705c1c003007000c8050629102a0100c00d4175001e41007408d4001d03510031030029403620144100300130360804284100085100910070b5074104204070002d41c40c00c0c40410304400b042c104405442d036031500552800710f41104440d5981d41c461042c28080d0504880080c1168506420308445175000740488102ea90010040c44c281107242c080c2442c0712b50b00f04580100c4842e000040340360810b29208800c1484c480040000b01d810a000fa541c1c281141c8012100a40e4903159201400c1002d11040322600b21080715542d43d240d0314238006552900503506d19950005c0c4101d0300c000303070b503403180c0c010001d40b00f0b2428142c80090040c00110348a030740c4818003e4102c045003101841550041c0b0304190000030780d09001c07000c2d2812 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 288895170 1250 288893920 288893933
    0xd05060a0b0d0812100510020703060c140310090c3e06070c050601140a14011808010606091202180c0903030c15010b1207080c1e090a050a081207050307 67
    0xc030b0385200c3c031201510107110704084007035503045c010201a181c2c0450702c090303500c0c040e45825442c480940031a448160f4108502c0c41640340c0340c281c0e03214507074054590502c400b01440e640c4413030250303900c0c040c43c0c5003603200101d004400ca910101c40104030520501c05215004840303049600d00075030745405010842200721801d01900e0700c940b12542e54a00030481c18146a4605041039100d641032011410a14582c0e480310744aa00c00e456401c0ca03000113000c10700c0300484100044000341d007060562600c002c00c00d00c006410520071036800e907a0b90203003a03072150441004d482c0444002075101040b642c168201c4211714140da0350104ca14011241030040003000b280c215804070700001500c1d00981c41b010b078001e4002e00601e0240a40c15071090804804000624541d98040d0250701032051031030000c0c40004400b802c0703c6400c00240d00154602111114040d80c9800c40d400d260f201e140001c0c800300701800c04900080c11500000c0003424031501d00200c807401540040340a03030b0640010040480802c0a = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 288896420 1250 288895170 288895177
    0x110402030a090218060312031806070f120204050d03030f15092f09010809070305120307120c0801050402070c0b0a0801050907050a021b031510050f0d05060a0b0d08 72
    0x1040402080b4010507104200038031600d444807010707a003088424006540c80000e100c048100c020720160759207440c0c8482d1060b0764002c001c0070071802d00c074040401c0303400c3d980140100e0201d1155250b20f01303035404540c0484264001c50198607001400c544015002c00e10a0f0800c110740383c5001800101c5c0d11808450f401c241096800142c2025240c510344102441042141c9017070b00d42032811000ca12280d441190100e10034a07443c541041f01110209000c2c1c0c00c20b0140c0340c02950311204452040314524800320a640bc100c0e80c003800f24400c0481d4090710481c1d03019200d214180d943d100c0949030309060411000b50412607080e5040721134804041100703a6130400405240000d526901d0f100e40c0340001b0824240750051480c800c00c14280301d01c0703074882d8000560302c2c40042d843d180b625841d1600e030042403a00100071390f4450330450460900000000000392007054a0054640c0d80c1c00307045200510020110344003000b4001e50149000030f4000b0710f2580034061041c001000ca0480f510162102543d541 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 288897670 1250 288896420 288896431
    0xb0a0504060216081c05060a03060e1002030712060501050702010206012315040e060d05030f0a0512070c05120c1b030115061d120d03110d090b04050d03150b0711040203 74
    0x3000103015102200000014603e0514000d046c000352a2050105a4443d45440000c0045032640d0407440e1482d406c0c07040d41c03007614141c401152a4a03002000038444a00110481e00291034000081825407182d000c850798203406070000d0220707034600f5984084880304102400800079002c2d00b00300c0c441d5103800760406000c04d8201042d4403203040015210301000b01400c8075121b44d18800e103039000500c011003502c40c0341000d0310720540c8540389440250f40c11700c01c8100d41a81c1c41988002c00540d207801499644055000d030089420070310402c02c04840307034030500c80d005a440c1d0056035440e192001001c10001300030000343c00881e0074030800710071080d410b801740c0016010801205201c00240303003a0a201030070078000c03110f4951641c4e070041c0840d1140d503580e030038008054480c1c2c03500d00b0107450300701218815052410200070400c1c0038145074004400c2954201c0b00740c002c1e002d9080300395210740140c07150690f00b149000c50041c50124a0f0345141e01540c001c0b41d1040803000881c1465840388051407090703 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 288898920 1250 288897670 288897683
    0x110f07030305030f0703050103120c02061303060e01060b131a09030106030c06080a0207030c0f030c080a11010e07060e13060915141509010c08090406030f0b010e040b0a0504060216 79
    0xa08206104d4400001e004061008062903c2d004102040b030301c600b8080100300342c1c188981603101030300208941e803040c241041d0646000038000000c1004d80d501000c008510300008001d46a1503540700e000d244a01c0d80d014074882181c1d0001c2c003e140c0c1c62010241c4080b070b104d540d2440c190001c40441e003907070030692040e276a192034000104000f03a00148d100e540510304820847c40d02c0d26596020b041142c800d14043c03d1031030241d05403400c0500030600074495075040555282c03200e001e00401840d40d001e02c40885429402c1c00d60904400030300140f03410542c3c80c02c1d2110140c0303040034420b001e01d0281076000d194080b52a0f001c0040e00d6151f5128001c06098121407a625a5040c880100c841d95445070400d801020b089591500d42e40d42d110a83e07004c400240b802c030b600a615810304103014040e00d0b00c190340c01860803000004026440f56032025461084035081d42070703a40e410503807559080803100a40865510030009070811400d501c00c6a015104420042c03c5c01c042c0c141c121070000040008481c0c0 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 288900170 1250 288898920 288898927
    0xf04060503160312020705030703060e0c0d0c061403040c060807021c021b061c0b010207081203010504051b03040b07170702100f0c09290d0b0a1212110f07030305 71
    0x24481261043d0f0f0042c3d04c980010104c4030701d014007081d0b03640c00a21010b000f0541c0d54074400b02003001446021407002c002450880d0078001424881020b4100d44208804211039034030508801b001003090b41d109a4001c070030707081920b05d040d030b041d0340f580401001101140200303940342c14180c2c25500614802030060303000b0503018042c0e403880280b0389079004103144142000c1c0070004250700802040c100c0100c45140100703051102d00c00503481d142554008103868020040c2d020354402c2c40c1c0000d141200c000325020700040c0c03a4501d0806603511442030103020701c1c40800c0000c011441e45058503820400318079150082d5060314410a10138182030f40c0440050700400c0ea110080040c60082e0384150649a504000000039507001401600760b41c89a845600007070f1400321310180c0c00c0038200314000b0407011500e0b0b58000221800f00107000c5420000d20603042c681010501000103804603801c0c940c4241c0c1c5d8480251081e00548800c40c0507c002c0c0002d01c6003480440d2080c0b4180400f800641c400c0d20760030345 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 288901420 1250 288900170 288900173
    0xa050102151f08160e04230313090222030305030c0a05071e1101090819260c07080c1815131a10050f0d150f0504180305090f040605031603 61
    0x52041c04e079000c030341d180d1002001c0c04041925006041160602041d4060243d407241c0d40c02801c5000c1c0307085a90f140012032900080160b00c3e034000301400042c460840b1510328948580754000b07a02c5010240000b001400014441d011010082c8078400c2d4a042c01800e1200613035504084081c440c2400d0011065004924108800038031010300d04c040900b49800502d003000485552161b03000c1c0a00608080d400c00e20b424064040030b4441440c1306400d000100403201c5000f41c100e40d1041c54800c426104400d8001081780700030aa1030240d1100900c4000400e4901c500309040f07400c050200c5402420442d024201590340814458005444d050301103084d500100710580c140740b82c00006409491030182e0394007126400801c881c3c119004184a0341c40e145100d1080e0020040700c01c2842000c1c0030642c012415070b800101c020100d443c12101880740d07000c0600e0300707440c2c83c0500c013000f00880e6007400340f4400b6140a859402008802902c00a07a49a0761030010780741441c2a4803404d62100b44080900 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 288902670 1250 288901420 288901453
    0x306060906050f0a0b0d0c11070e070215360706020c04110705030406031817040e0702010209090105010e04091e0203010e0d05070f03090806090d0e0a050102151f08 72
    0xc43d4403c1244c200440b94540304507882c0710300c41c0e0f005a0a8069031010010750042c01007684010002942080341d200c0d580b601490b50b04040d007074547d140903200740319844092a01203801184a8910417200724004884aa050070b5030907080310302d000e0624640700b04282098803c11102005041c958024400d5440c0781048c4400c48660900602900f07004101a001068000045400303c1c0e40c1c81c54001600e10514202d110521819040107044441d2903250480146c1840b01500544031481100740c125259005e00b60b080707104001c2c0c0c82d40c00a149900400c000d6018001c0b40080e290040c001042e5600c1c0d503541c0e404c0440036150004403485405401000350304003486407079010a482c00040c0b00d95560004003a12078054884002e082c840c83c60304002c10144144060380040a1b18003c5a00741e04000c107445840d102c0c0c90303200310009a691031080b140ca02d094207d240072100c040c2c018010f03e034826070a102039500014448041c021041036641d000d4401c0c03040300344c01000e407500500000301d138003207008 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 288903920 1250 288902670 288902689
    0xa1203080a060b070215030c040e0709050f1c030f031b0315050f01090902090d08040b0d24030602031506070c06030f0614060a0c05120d0b03070602060408030907030606090605 77
    0x483c6546000d104800040c0c031810350380405d0507001040c9640b41d6139901708007a03262085800030b901d080d07001d0301807212254000d5100c4040d210301312200c40c1200b41d6a03081c820b8180008000000303072400e1240820110b406a104014910401d2401041142e01c01031503216100c002004080029620380201c2c14110031180c412000d400e08a807008464040400001c0044e4103c1c014142140d0b400101d0062540d0b50101c505040c0c1d80c030460781a2160b03030700c41506159810195070141c40ca410b1060107030714264072100c90100c1b04100d042001c451411511650000d400040c0ba0300740c2400e5000c035058090341c500d000341c110315115100d42811b1505010005040e520360300e40020a8500b00303482841800c1100b103000103007140a44807591100e42c4110100c5a80c2c0401c00041d00600800007068083d503008002400e51064182007401034480c08400c1c180d640c00c981c85950016000348002c200042e00e400000d541001c944070444036900d48a407030740c20449040b0703486446d405943e2081000181400c1a40 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 288905170 1250 288903920 288903929
    0x72001180f0612060305060c03090109020306040809011706031908091c33090201181806050a03050318010c050d080a0e010b030d051c0204092f070b04020a1203080a06 73
    0xc2c0512480c6545455842002030300e208d000200110010f0046003096202044141d002021031b070113070070f02d070801048513402990810b00081241c281643d0849000340c1040c003e420140090080c540154514014425407280c1260500810000c4460b282e0350030f840d4420074440c03108540080b6040e440d0200c5110400300004c80c0c0d41d000c500320304d010305410405d8481400805030021840e4417031803004960201c0440076000ca402d40100011074000b020101125030421880010000c06840b06c0070480c0726180c6120041c503561041040348008203074211440303000c21060400340c00904240c0c1d2202c0c1042c00003040000042c043c441000750044240c012b26a011748144020013020a4541c042600d40301e90b904510f003071060001e4500b15140e040c5030b01c15007032110900215111074488084501901a5402c40321301d0b0218140c4100c90041308440001c0d04c170000011291900c0d0240d500d2056140300100181e07031021840b880014070b092040006d1400c980b0940d40e9561901d000d045403011210300303420 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 288906420 1250 288905170 288905207
    0x306030118030207030b192f120a15180c0f0903030203030f040c21021005030f01090c0302091e0306090601080d050d0609020c0a030305060105072001180f06 69
    0x1e00c004070f038000c14408140e98028480101503601e01d00ca01c1d241981000081c442d407841e01c140800f81d9882060780c40011702d1040e00150030002c1c080c0b480002406410014a40940703601c000c210303e0b014030b9200300441c114400c802c44015940308e91489003917a0110141c4c10030354480000c10261039103d00c60000720915800c0c003d240c1402c50b10002c0d07a0b0b00005100da0b044020b0100802c0921829400800c003c00c03142c003014408080c68100c1442c030b43c1c90034000b240101e0b009548146030300d0140068900c1401d00300d07000c562903842d002561001c2e00d20481c601081c1a400c120306003071912003401c44440307e134034a055013030381050001c01d061400000030f01c0e070b030b540d504440010300c1200340124540040b40d10501c0c1c1940c4800484884c0c1004007110392000c080f16100207803603a44580b0100703407546118001c1c0c808101d40d41e680c0005490343d10035810f0092410948480e03451280000001a0402610600d009209048050748500b050900c0b5009006980c2d5401070401565604c0950810441c51045 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 288907670 1250 288906420 288906461
    0x6180504051003110a150f03060b25080c03030c0c06070311090f03011506020105010f0e01030f0803040f0b010e0105030c030c090f0c0c011506091e03170d09060203060301 75
    0x101d90030b103090102c2c0401403202d090321003a0501c95440c64140005444501d81d100341d8044030241c060b060340141800040403d0503d0380c00540101040180d6480ca40c01e85124187c00f8925560403103200b50052040351100e800f03100d010358040040002d0341c81840a0440c840d071783c402100300c0c103240440040240e0101410722986000d18281d41065844411059071503103000c00a503c00240540500048040622004040055004c0d0b0540050b8102d541d01c803600b141d05a10f4001c60306542000340009444074400e44541c0c80010301f400000d5510902070f5060b83c40034201035a85029030030007a841150400311035001441a450140a442c0e0719010072401840094000c4e404620074620040c080c00705142e542c1c0c00246403024200446010800340b40081000070f5544010844200450042c840056044a008244100e00440e4041100d5000710340c60030300b601c0d5669501c4080c0d5051070414070054180b09000c000e078454081d8101c8503202d20805030300d91501d8410f0508484d418141c0643d8848042e = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 288908920 1250 288907670 288907681
    0x311091e190f02090d080f0705030315120703050d050d141e010501171504091b0e0f0c1b030f0d05041109060907260703090b07181e08070618050405 65
    0x81000380741c03030751101d202611410050001f00050094a101a206000000400c200644c810f880150086000c40d10240b83d4507801c1c0307042e60b41d209140401041c5605c2000300c2c0c600c45003da006071004044030440031030134200c0710305112000300082e21029000714480c3d0141ca40d401e02018483d024001c00c0c40c011090b03034000c0d00c42c00104c0d01c02404070010050700c00d030071200c3d6840c0c42d0804458180c1224150080e030501c2c1c801030f49c01c55070510560f96684a0b0401143d60030032101441401000d002c40c50720304040d008070340c0000c0c00002e50805840d40c4001c21049040e1203801d00a040c1c801004000000d65140ca414074460408803107480030300c6a9002800c1243d180d880c540d81c141c0140c1a4501011601d022190505400800c1508206507a40e00e10821410359030582042c0001ca106070303188100764035080019180b0700007181c0b840c070241c81110ba003481006200b501844c0e000042c10f0304801c00c1035a6802190407d038440d00f0135130000d200d401c1c880c91910014420b0100a0905a1f002c000302d1414 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 288910170 1250 288908920 288908929
    0x5010c0f0219050c0d0b090615060a1815210c09031403120a0c0e0d02100309080f0301030c210305030601030b01050702130c030e0303010311091e190f0209 68
    0x108200c0c2d00301400014915040c403000304050040b028014086a14080190a01d00c1442c0c00403034000075070744207810000c0d141c00d2a01040802c9000301510790341c14207441084c165540c203a001c08001882209a400003541c030903020821000300c00540310980940490b40f540390801d888410803008240c01c0c6420031061641c4500204116908821866030400780c07408550300318403800e88000c40c100d100750144035200344a540102c440c1d18940d295035100c0e0042c4000d01c02ca0015108019602444080c65450058002e0704100708091003001151701d00307214403040f544c8a8100f80c10035520301c14850811701054025074000340c000d00080e4080b00c1601006e50300182240301c01005c0c1810143c85103600c403080d9004005031800f0b11341c028265448000011903038001015660100030000341072000c0708070380000c0071088070306894010094814184104052280f41d51015041900c4101050342d280310070304100038083e00900e00448071f64120f0039142d40f92170540d005041c00d000070910400c03030f5804d035a88 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 288911420 1250 288910170 288910183
    0xc03060a210305070302120309070f060e0901090209030102070f0b06100216060f030209100804030201050612100b030312010303020105071403011514160303090c0812030a02030a02091c05010c0f02 86
    0xd02d40707442d564610040c41c0c120705140709048900c1071a00040300b4813083d48070124802c001c0c0c07480581c680c054031743d80e4841200d0300c0c2c4010b41e0050300b201e074050060100145540042c2003886000d0b0025140172215a11100140c2c0005010b4030824050828032200b80b13004407142c501052540300a2441800c1d40152040901591040ca418000038203c40010716009405a0386100c10040c4240d1040d800c0100241036800116000c4005500c0d20002800320700d4038000c244070640c040f9005200c0c005c2d211048000420070301000503894030040c8107100a101d1071103007040c00f8502c80d9001041c0d034102694050a0b000a4221204600c48184014440d44a480c0184040e019492030b22080307000103000d030350182e0301c529140a030410002841103c10f15030103800465003180b082a007000003540d90211036860341d40303070812001d8812040011a841a6003a00919000200d440300107251402070000115406031889003060001c07000310151080c807500f80301b002c02904190a203182c0c1018a104003e48508 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 288912670 1250 288911420 288911423
    0x608070f0f03060b0d021b061012170c0304030c0b03060f0103150f080d020f0a05060403050703030b03030d0501030b06010207053303010801020c0708120304060905010e01050c03060a21 81
    0x7034000030050711030340200f0001d00c60480681d0b5564140070440010390700c250b80c00c010045501420382c10250f00007448500c1a64078072200e41d042418645a40c20807001c4c0d0600342c07407512080701380034400c8d42d20000801d2080582c1c00190f65980c6989031040111403150300909180c00d0600810100b42c448100c000c48680e82440d0000e10340741012552420200c841e00440003100104001081e454400211238000d000b56400b2230f8200400400d0103070751111103040052494000300085000a030040c809000c00502ca4200800d04009580100740b13107030056030458440641b903800410912411051031a00190284003070554942444080b80c00f412080206444180c0d5419100003500c10b6440071a9220300a101826aa1750b983d05c406070103500803004511050007000c90000f4005000500600441524a0002c1c25981e540c1c03190401020742d80c2090303a030742d500c550390205540020721409225111a080894480c01d0110902038a140181c0042000c25a05114040c034040c550700c0a00784039 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 288913920 1250 288912670 288912677
    0x905060a0201200a020106120c091107050d0f08060105030603060628090e0607050a020c04050c120702070303090504060b070b150d030503010503010510051e010212040b03100608070f 80
    0x100c80004040303005054184181d00004251992104840c1580008042c1c4d4650359000b44022900c03001d02459000700080000c0c1075044071b040800094945801c000500da8000d400c0505080c1c207922001d0a10140c00720410000320850b1710300e032040340c0104240d0b80180c400c6c41c1c403c2c2540340410109688950182200d071049601880030420381c960706904048030106044810315440da40e00d404005001e40340d004c48003d0040d000014001445101603030a504403503801801190120340510000b0100a050490480d60030032030300c161a003984000314090842a4010300b015461400d00501581c0300341c0050307215034100801009040d8031401541c0741d058101450007030b15180c40008858403020034428503000001c036030180e000c1c0742e0450051812118254000e1115a491806103000112240034895020400c0c0b95604904454020510724a16042c0101c620104151a104015400a40c818210316400004011004071028441c034010140f90802d03c15130300340b500d805000e014080c203070349082 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 288915170 1250 288913920 288913927
    0x30c04050402040f020d05010e010503010209090103110307121505060103020f04060e0f1207061209020904030507170d0902011b030e010503040602040e0a020705061602120c030912010c0816090506 86
    0x55540d04d030701810040a148404554810507094550050b150910070b42040807010000000d044c1018000c0f507058804c000d01d400b049a0950b40d80054800700014110b4051180d5400480c00401c000000c80009006000c540c0c0c02d1840e6004110a40c1c0e40241414109401400110001d40c0040246c50541d0100d0921055a42440c40030400b00308000e07442c5940b1002c402111400c1000100d9513205840296885646050140c1c40e080299248010000d402c48d04001c0060b0100748124003818001d071150030b8031901c00e00c0b214400c0c0550f0704001c40601d01581e649a11808560700400740366010a400550b012050304942c030049c056034504140300381400030000c006130801a00d5411500580034034001420780f8103181e400e820003900309a400b107840d88262004229041c01008620303440344000c0d0f00400001160544421140c0c206049544051000703010b000e446030b40701c4001c50403d08540f0000a943c1c042c282c00102540710141c400c03c4000c040c24624010140e00c0031044007540c0d01a22480c1c1d4 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 288916420 1250 288915170 288915173
    0x7060b1c0302070b090105071203060e070905181f08010506120703080412170d020304060608061b0a03021201080a0c0f0b0a0c03090b030a09120f05070f0318062c030c040504 76
    0x81f20711580c48000e0101d80701608194240d40c040e0300480544030444601d600c41e680b91001601c0c400c4160081e150710000002d07808404609920402e42e00401e1524007032000d1644054000d000c11160b0058046a510340040022504002091b501c036480b40c0f0004200d0145152600c3c0341d14443c9014520b0700310b1112503040e06000c0103d6a42c101d03050100c03c016915803101c0c14400094005076030840700542031100000d1001000503141d4091001c4c0d40300d40b05009a0088000c4040d44450701e03801c241a001e0000304140f2035104951030003050a00c0c00f50524001724505031101200980102660f4114148148603c038141d000341c0b00700e440e50381003030940c1d81a14207080e10005c040e0381c81401c25030800410441c802400d500038520051180045d0b802a042c5450300740d40b000380d001000000540709020002c041070764140c504500b5401390420301c0d030300f4103484185407840116030024004a54400f08540c80c401c285400d1105500c0d241d2075400c810700140b0002a00c68030030401142c400c3c1d40b180003240 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 288917670 1250 288916420 288916427
    0x928060c05090603090d020c06040303120506120d09090c02010203010e0708062b111e06070804031208070815060a08091c020106050307050d0f08031b07060b1c0302070b0901 76
    0x104080b500400d116101d03c5c2c030701402ca03543c86024440b6001406002c011350301d681410b60654003900c1d81920303450003183c49002c07140010f1000811195200040320320401301e040c424000800c0c940603a40c0c4007d00340781050120019102cac080150f208580c4100010880d0b070315100a203540008076864641101d480344400a451003044148040d0105102d4961500b0854110000c1e01214815820558181c44101c20020380003000031b1141c2030240d52400c0610185400306c000c003405071088501134181130b2661a21070003d070480c80501c002c52240c106000c0b0080d0028401c9a20940c580445810000e07031402240c00c5000c0c0034428000d10500301d0102e511803034180b2042c0c90814032940c80c03510240340c004000703020304001d21400303000780038110000c107440c103120905500e0150031001880d28420f440d079660700380e83d0008260140126807040e05c0039004507202e0040603c90300132440440d4004000c03041010085200c040700030301d0740302c9500d11000283c01003a420211010794040c1511100f4040058 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 288918920 1250 288917670 288917677
    0x30b01170309060a03050403300e12031501110109050705130b10020705011106090303070c080730030b010e061b07090501030b090703081228050928060c05 68
    0x2d41e800100840c010a0699140c3d000d40d10442c00f030768030701c209a01485520340d10b070749841d078607000c50542d10036009241a01c03030b4000e400414440c4c001c44607080110084c01180c0d810603181c0c050300084440b04600150382c8141103040c441241e42c001c200b000d0107076461654808d014440c4601072210860840043ca025900070b4901c5200507201080e4036040340c43c02901c807104c50162a01190501c8082140b41e4030009000d07104034130720341c0154915160b20b4002d5a4071030061000301c900c4c2c2020029240010032041580d0b0044a12003c0c50119225555420f60780d00b40c00901a800c042c6444841902c0b80c0e03100e02d200c1c208107020394189581c0c440083c800e80d0501d046000d651107900c40c002c0d001581c2c180d40da022034101c030b02a1031040181e4070b075101c110b0741360145444064508201440085900002d80c142d0f190400e8407050b0b52100c04220070140d00c02140c1d4404450309007603070307481081200130381400110071620342c0760007030060380a0200c041c01807506020310140c540c41d03556880415050003003085 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 288920170 1250 288918920 288918937
    0x1f0e010311040803120108010513020a03080f0c0304060305090106060f0f0e040f02070f1221050a0b0405252105220b010611070506120601030603020402040f05041104030b011703 78
    0x69a56410705c150103030075501d1082c856032645618000c0000ca88184005185070280d034000d00034856245543c4484207190001401e070002d40c00104078002503103030304000401c0102901d89000c1030b60b00d007100302c49084420503030191044c008900001030031550b00c14006022000141005c441824205010400901f4003039601e0013124070001c1c1b02d109100c85510600621480346050800030325200350110f40840107425082d4100c000184407000e45d926603044594000c1015400041c0c081612000400342c0324240c40c1c00d07545000381203020400148411a03450309060310b040c03840c403002c5403030884503042c1c0751180020802a0b403000442d45043e020068040304115900240b002003a00c0d0a140d4202c4000380f00d481c0204000311907950f280d4401044000c1280c00040a6605169400c200c074140c41e0802080241003542d40d0201100603919840548090010000e9800c00903007090300380811502c07190484081418280000c000061039030b102c1c80e0640c0c40b0003101c003d4500280040d24070b1030158000 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 288921420 1250 288920170 288920173
    0x7050303030a0204050a05060c071814040809010305090607050f0a030209060a11060f010b090d0227070e041a01112a010906050c0a02010809100207050102091f0e0103110408 76
    0x1403050b48074064001d84107942c0f04840ca5883c83d1b0755901080703031078480e104252201c1d03080320314100000f07050110244542c49028030701040343e0310000b950390000f0004a030100c1d99604045080c0c0255685031041e203901441c03200045c4610b0401c0e51000d005402500c2050301e01400008250004c0c6c0d111790141c68024402401c19511100884d030081c0845d2840ca184042c00d1080400084602a103a03440c1c0341200e074041102460b02c5842814014220203400050380c000041610704440d1031441c6400e883d41c0204105001c40310f0800e00801005038411001c0c2d9480740b801c25080a070342484001814580c5102400c010b660303001d40c0c0840034201034101051801000340d2404d014401c22004c03c051007420001d9841d4110161210b0042c1c44c14002c0580307420055012141c20b00040d40070340d0016401c1a011412524101c0404221005981c0142000c5400e80d4002c90542d1240c1407141401c406950001d030590300660705242d00070b00c850282c054441c105a01c0f103c10280b00440082120064000c0e1030 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 288922670 1250 288921420 288921427
    0x4032003041d06041104140d140303070804050606010c1109151e1003050c03190e011a09010506090102120a1e030507080105150406230a0906021005011d040507050303 73
    0x1192121071104540f468050b601306851080072400040864050380c50000e040c02c0b11007000c0b000e0040702031041000b00c0308618040640101c00500f0030245216002e20b41e100d1209161506e0094240074002e4000b60601500c02e0000c00041e1881404001c081d1054480c003086030313500700749080707a54102100150404d031850300f0340000c50b010302c00d000030300c190a8070701341c007134911000c000c400f11201250f81722540030003840070860003064240341052001d40d0b03050101e0a00040ea51041c00c440204401d00080300300d95916030540c0c20600d007890b004000440394141020001c10000c1d4031000d0300801c80c9000200026416040c42c01080582006408601b941d480320001740d8005e0f0003000c00351452000300e01c0c04400002c0ca0714045030700d01e0030b072518010b01c43e04140c6070402c203a4a1000e40720521a4040740302031007500010403000503125410340303940d85940051518402038144249103619000d1181088014814410111040301c0240c69409c036605082c0c0e0f0f181851070400140d900300c55494000003 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 288923920 1250 288922670 288922709
    0x30312010e04141b04020c0109020301020a0c05011d120a021c030f14040c0605090d171b0a080720031c1404031208040f0503040b18010201050403200304 67
    0x180751651040d0312901070184600400d181c590b07501c001c0003051482580d440f800072035150515030040c0001078611030000c541020316600103030070381e00a2a100800954061109814010240595800790054408840c10190940303100d6803265200344c04142c4a203400a00300300c0c124401c0004d240e40342c81c15000d51815646809005010341890003208070200d050540820300303007170515280c2c3e016541c08008802030915040b81950103070880358a1a51000c02c1880d0b28010840c3c070361516080c896507a03da00e54454400c480c0d40300254420303001d208264021038860000840503011980c11903001000c0e51200b42a5484001401003115012505405191806006c2d411036038040d07000c914442e103800e18400c00802050201d8090381c80b0203014180d100c442050300a001d005180d0b042806412030009400310354031402d107541d225901c6000590030004000210b08001e481200040c2d4091000f0f200f581801e4500030300150f084207215500740c81c218510705102c40e00304101e86c000c0c01e0910500b2100d03400d4 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 288925170 1250 288923920 288923939
    0x3030e100c121410051002010b030f0703140303010e0c07080702040e060601080112020904060c0504050d0b040605100e16051c050108150720010f050a20040503070e0603031201 77
    0x300e1400d05420700d11038640a83c400c02040d0311650303007942da01048074600020051840d0803100d1182c20b40d5a00c01e040e50305c680301440790741c0c0c00c3c400f50310041c03041905d185058446640b4140a040c40f540050005020004601081c290000d0340303035014903202d00040c00c202d0514460a40020740c0549800041102c0c1d0002058044c403840090722141d4441e0b0780c5010203032004035040380095001c00c2040020300080c0113948050400030342d920f402c0d0b040c581c5030404602e9500c0c42e584182c401030000010001002100c1c002c89901080988110308074a01d081d4000102c500e000d4242200195410075594082d44039006030360440d40900784020580c040c20300210020b000030301035001140289001d1052101c44a4030301c40c01410656269542c4031441d10310040110780104080d031540d52184064901c0e15160301401d401034811010004101000d0610200e19000704070340082c8070030050004114969001caa82002c0f40c00f0010603ca00e552880006411482040a40c4c80b04541d04c3c00041199205e = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 288926420 1250 288925170 288925187
    0x13060e030705010305150415120507090f0b1309050a0b0c0703020708010207030f0c080d110c21040501030f06050901080d1119291609050103020c03030403030e100c 72
    0x20a405841c91140c41d100110151a000c0301c80110300480130007891100e0809900840b003070080003007c03268094407810180382c0081703868000e440c1c580c0800e005100c0c0c00700d2481501d480d401034550401c601070382d8a001c00d1600d411500410340841d03a40049a0078020140050428698411807070a001d140400c459212500114415401031103007040202d50080c05100300c8021b1a05a1580d51350a05109011205500f0000c0c044031031010922116811b017502d07001c0c03013045546c520302e040c0e118001742440d2481c3c0700c200c145031b440b504100005c050722070030900c0c11141664020700c2c0118802d03002400301d00c0500403560006030004500c1d400040c43c1e800c0440d44900c034044541d580c3d91404400400c882e600c0310f8011000313106e800b03898a0500041d00d4540031689000075031050104e440c000b00315141c0f14040c11111286003c101442210046a1084101025000c01d003400c5040c03e1006070341d1550b900008100a0a0560381c411550b42c04404128010802400207800d101c142c0d170f150130080c401103 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 288927670 1250 288926420 288926447
    0x12090f0d030209060405041d1005070e010807120b04150e1f08070509070c050a05060106080a23090f071512090305160c051203031905070813081306 65
    0x285000c0140302a01c40d000700c4984400060005041c141044c0401c00200303480030343c0e0302c2c0d8002c3c1c03601c0c02d004128080c40048080b140d50500012140341042c0060961807074a01c0c00c1d03040100c0c880c10800310a40244030440b21a184201c0058201118804680102510090508011440c0d180002c03809010702c511445040310901c0d0400180c5244a698003000207401500d015400c0701c8401e00140c1000c080c0540d00284910b814511203183d62162401e00d4400c83e006c5d2110307004080107006141c0c005000542000e8001c03070030450860000740750514100100821008040d1000100301c0140d810010f80303031190954003d44a80c170760303208101000c42440001c0400480c0c80d040502e85140300700d00c00d40c20100e03015202e880c034081c3d2404010006400da98011900e1000d03084002c101501c40c091102c3d10700105500455480c00c004041c00da250700d60100d21620503080104102c00d02d81c0c480a5150030405441c0d020150180d2854038909a0180c0541c407840c41100d41c07000981ca603801510024501c = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 288928920 1250 288927670 288927673
    0x5090106080118030507050a080315041a060901030b0310060e010e010f1a0702010c060608010e06090303011419091802100f020303071b0c06050703081003030206010902070812090f 79
    0x115554941242a0780410482119000c0007100000c00329000e580205442d40c4a00c0585e0b41300741c0c8c56600c0d83c801c0d80007626407410b000d26a01c07290740682000d101d00416401903040c4d5518941c01d01002483c0b41c400e04079190304158039840e200826840811503603519900a020030b00166031100000c50020b0006d2040103c40640c41c000020201e00129290b001c0e01e559007010745187c450744001c100b050340318400890410010311014004a0361a10071a0080c00d40d0341c00200305a10901c041e00e00c1d10002428a00c101d4000700700410446403440b00c540c0c100c1e80c0c11703111811010094403020340c00140c19802100110b003406090b6220301005240e1502d42072003280c0c0b495080082d46d0040b0350719406020b914016078002c0000c0382069010b04a29500c00890320b1620b08610340130359401a080b01158004004110f02180382c00130503810000c400c1d4883c09200e1460001461514002d55481040c860028001e5000030580203010b041002c07914000178900c1134070790f00d050100005a03200105640500d0781d = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 288930170 1250 288928920 288928931
    0x20301110c0d110325020d0c05040c050f0909060d0606120209010e190f020f04080a0b09060c03070309080c1617120403060b0402070f031d060412061a030a06050901 72
    0x1d00901e0744441e00f0f0508070085043c0314501d2599840350611104444141c403006103c0d0005035a0810200003251295a40d400c4d601d00c0c0c00305100a442c82d0358501c1c024000c060114581450b8000706481e41c102c0d08864180c01500c3c0c2e080410180280c0c50000303840705040100c00b240e40500c030003601180038070a0301c4042d0300baa40e52a810f420601c0c140c942c01e4409000307501201103003009800c03000442c2601d5000610740300c1d800c520180f01b0b81c0070381d0110440d500008200000c0c8055044603543c0030308102c005d810585410401030181e484000c00c408145035441c107031a414804d070181610200001c6400310b80710031500003d0455420700520414201c0411107481c090261004109110f941074250449030406017141c0d00c050103032038a4040070350031590904c140c5000c08e40404514000500035110070b600e0f104901c00084c510050540741c0c601440f410082040700b0000410000a1039803c000001800390303130655a4a0050403040515a245c810f00500e0030078040c4540c40710340a094400d0003080f5 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 288931420 1250 288930170 288930193
    0xc1005070903200315060913051213081207051c050d060305030c0c0a1505090301111303050d030507090b130503060c0a120902010504260a0809091302060405061303020301110c 77
    0xf171802080307544a0704036031044045000380045042e20b142161052003912030700d955108503035a6580041020214101c0c0700170003000090410b01c010302d006201802001c0c980306458440342c0e51540d03c2d29140c0c91400c2503040b502109442007041e180309403c0d100081c00050740c1c909041d40c2d26003000313040740381c14095622a4090351501510711002c070380f1000e05580d11401c0261056400e0381040498540554851000441c1c0c034000e88001c00f0a200801800b180807425801e110f894813415806070814945802c062045264205450313a04407614204116541c0103c0900141c440d0b2083e400030b501071103040c05020003c0c806801074064280a41ea80900f03400c0381d4402441914800440a0302141003003100740400c4600201746455459400114401c03079403140540c914000c1503078410b0350703d103002252071151442e01e01422070300000d0f1008040d0800c4a203400040303162041d407003030501c20080011040384c8001c9043d2000c00440d00180204400d1a06520031034051340b01000300b250078041e2000c04003 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 288932670 1250 288931420 288931453
    0x20405190311220b06090d2907091a07121d04090c1a0c0a03020c0103051806061c0606030b1b0307140306010903050d180501050c10050709032003 64
    0x600e40f01d14903070450080546402d8400100058031459822031000c103e0b01c0e8240e210b4445510714644a0321101c1805c002d10014002c1588013003864400c94800b003c01e01180c81c2c1d10400303031010760b010181d89031b60103108450b810300244103c0341d0080c200000448207c00c06a0413000040400701400b0141c0c1c00c90034130400308822a2450100200440e4803032406000062510040415115200412074901b14840403520302d40f50b032104045005074002120f207000d55a00d030040c41d4200e0b0a984040c6046e82c404000c0c1074580f00004c0c480d60080751907100004403c403044140c1c401c129001001000303a00d881781007400e003850040f911001b0360f03d005860340d030400a01d80b02702c0303204080781da0b682d0800140c6607100c0146a80050102ca0400203000804008110b09100801c1c0580082e02c2d40f2007414505a02c1110800c0a50b2140d8103002c018414207490304000310300440c055000503000202940c641d0b2050350050829000a00910760103840c0c0001c15000305030518050600b101142e0f1603076082150301 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 288933920 1250 288932670 288932689
    0x20d02010c050f1b07121208041e2901050f030a031709010f050108010c080601020f07291606050901020f070b100305160306140c03041203020405190311 67
    0xc0040e20400c07020410300d07070481c01362002e40000c44100c80a03509001d0040d01d40601904034200b82001010050b08020202000005040c810b00342980c20340f07000d803030703800c421041c1c0500c0d1502140d80300542c3c1c040250001c994008950340300c44150141400e1000d90411100901885002c2c0362400e0081c0c0c124900015414022541650760000ca941102024002c0c0d6901610900c034030740d220510400340d201c0502806029140340c400015003560b01e070000500030b0b000601040e05641002041c0e4000d40004074008003650032075010880c000c0c010380080c8070000c0800840300d04204000c1511441d0407003100081c0c0c500d901901041c04aa100c0f004064200c2c4a0039101105002c8100280d40005660120440d40407041e0410454802c1d5030b131f00c559050001d9044c1010680c0d29400e002d100304182841039012500900320466410302e042d080b522020b12002d480a0141044d00901e404282c1c480c1d01220040c0c04060680780f030050342c54250100b4410180030841d0045088c0d004804941841440c0 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 288935170 1250 288933920 288933941
    0x30c060309030f0703020f01062c150105090a090c0903170a0f030c17010608090f0f06040f020a1208040306050703150501050a0509040504080405030105090d02031206011704060c020d0201 82
    0x6036140400003d4007180319400000304809502035400d4402400c1002e1280c1401031001e0240b030780074018005041c3c1c3d44090500e01d540c3c01208488180b01d48000d91f094043d00c035801c2030030015614021440010300c2c21103503600400d05107051885080001d80c0c01205078084900c00c1041039086a61849400198090110440c000525074048810014469040040c00c01c6407810f00440d030035401145d80d828000260030602c00300e250702c424000302c154100152819a9040c8020f829030741000d507010350312480c1c01b0f440a400e4002206101d010f55a550702c40340c00501c4d000e403009090107203030b10341151560000c3c48203844441c90000005c014502074019072207050180005101c101e030620005540d10b4204c00000d00812805202000040e03c0d607114a9005500070348160380c403685000209400d46030002d0201d19207420600300211461340000c10381344030302646c1044008550303611004032400c211410100e80c0e80e009036014041442899444908004a55401c2d43d102100d480c4040e400d0303600e540f80 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 288936420 1250 288935170 288935173
    0xb01080702060130050610051002070503070b0c01060b030f04150c020309040c02030405060d020403051b0a0b030402010516201903061a040e0f150103020d1218080705030c060309 78
    0x9040c0a000d841c1108603000c002802e980c541201d1050305c8281c540001180c1c0c00ea14520007850a00483c03404001c08401451070b407000300744503401d00020a450340c10f01e10a451400d04041816640400c0a401c400302400c0b92541080e180e14104907030b4881c2d00b2045d1401e64800804100c3c0c1c442000c42e0707006583c10b00131f140d001189803000d4201480010107414400e48210301051001003199503810004265101c051140540c8603070450a0150400c030746a05100325011080340ca1040544554460310b00f110403401147d500c0755514001030b02da61040159056165401203015020070108014a05403a148401c000781940d95000a01200130818241020700c900d03413030000c10004129400c5881040c20b8035458030740140d0020046410703140050b1205001e80c005081007075480300b0800c4000f0007900c8880000105d5451030b004541405140030f8098100c008021081c0d8501d4082c020040312082040c0403404083e0351401c4103515a0024001ca51090040000b181214940301041d28002c400c0d810 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 288937670 1250 288936420 288936449
    0x10605040303050a020a05332a0408030f190f1e0e0a0326070f0b0403030b09100501031d0607180b1908091f11070807060b010807020601 60
    0x44003610650092040d0100310710070908000700050081c0b004403c9405840100300700300d1001b440091f4640c000c005840c1502034050b04000035009c08446080030050780c24a44c140c140721503155414548580e800030340041c4400200a152403158400524184807002c40d002401c070f0382c1c4c120803521039070844661400038880040e5482e00d200415070559052600b030800d40443c642e1140428101c2009a00c292214040c1d0214030940d04801c1140303240784001d00d84c040b0f2800210b40e032040075180c10390b103010303140318440030000c0c003014001c3c0d000c07240148005041e02454030f082030008401074480c4c014140000e0401d10340e00004401200140303501292500505031039900d01904695850300c001401c104071030000000584424881c0007070099101f000d8808401e01082140078204020141044000c0e41c00380395101200700b0511710410001100f00b001184501900078548101e004820000e0017503031000a0030010001580c2c003003106200300ba26500640e60300e0380010303078603030030244580a40d1a0b00b12 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 288938920 1250 288937670 288937673
    0xf0603090c15070b06010f020a030305150916031b1b0203030906180f0f06030712020f040e04020a0e0103020a1203020115030f0b06121203090109021f090e0106050403 73
    0x10006558414210000c55400845040000d00903416014500c1040140043d00500303015041c1c00c401da0052080c00d241d00d1078006d00c00000d6480050802c054209651a408034110310410480020603520040075881d050030220090704105500c406160040780c58000390749070710080510540580304054079040d403415008200e60b010400041002c0b41e050100300040081d66179100003070110042001d1191651a09601c01c1c0002404422103062043e242845111116a40c100440c0c0d8000814545035134001003000340d440c0039028502e03081c20b08180104e0082aa1010082c503241300e10700888440315080e0340c80c5411307090740302c00b804045e4005409400c01d002ca9044903c9904400e07210303100004d1404e10800484044151039001103d81d00500c40c04242802000b00d02d80d034100310100e860b50300c442d1701c00341c5d40780d41c03100b6030f20400d40c00c10701c007000141401500b03500c03614070b041d005400b150341d8200812414500e002100780541c040307444030001283d14218003c4042c182ca05540780d5078a01400c6 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 288940170 1250 288938920 288938929
    0x270a031206030203151605090907030c021e010903020705090c0412080405130b01030b0f090115020709051e07180b030406021e040501020d020303040c120212031306030f09020f 77
    0x34010403148503498481c0000182c8003005a842003020891300b51440342080b1010302c1d001d0940c1d081a504010040c050400203a0b9003600807070b080361841c02c0001e03035281d00900507810081c15005c581c281d1030400c0302c110343c03298040d088038441511a6090303402480e00d990401c81544000e50398010303251010700c802d10108061180b8161428001e441060802d81d45400040c010840402008041d0b62240080c0400e544c1501800041c3c8034201c6076008010302000c0412440501440b07680d010149003140072404a00034400c420161854240510051411203130106040206102c40d80a8075030107070000d004280300301c07240c8400459204515446601c1c15500c4009508007520075250304c0e50070400302d2400013920300c200f480468203140391900c0b14901000a4102000d061031402590000c004210000d00c1d800c0c00304042c0c03401d0340342414101001b8000f141301002c0c1610301918510001803100707030a4441c500d9110844940350341c20312080e01e03042180e005a074503903a0001c1d0080310107078a115091a0 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 288941420 1250 288940170 288940187
    0xb032b23030901021b010b0d0b070c0b0f060a0501050a02030423030d080106090f0b03190e03031e1b2704060e1902040b0a1b06050906270a03 62
    0x85082400310182000c0c0314400540c07003690700c031081c1da500251003a114003000704440c01d6511040c000304007101c06000071030091a800b5000402c500c3d0304030001130f10180103150b61146140c114480e1031071403a2030080102d10300d0b0300380c0700c0034880c548801303002500e5842035085804080032503002e1810f0500e01030004000d03404080c2c00c1d40710b442c0c80c0004408a902c0410030364850705040e54511005515261000c2c000c440e50342c22440754000d90305d90074022206c01c03a086942000044080c2e0144c2043c41090400600740041e0900940c080042485960513403007101e02c00d000d1f6221200903007600c7d1f4a810041507242a446030344068428030041b03d0f0b0088290a6440354070110051440d41c10780ca05c0064110740d4903400400751500f000c3c0a001e00c42441e944014007508140c401103181505140c407480c154050452048100424002041501d107458002100c00c1030313014606101c46c2c00e010501c0350316143e04441034101e5840b520280511041d84030f003081c6000c00c240015111f240607d0702c0407212200c = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 288942670 1250 288941420 288941447
    0x5031507020c0607150609020a30060b1306021f05060d122007061b0f0b13110406050f060c0f1002090a080703032a0203100b032b 57
    0x40c500c200400d61200700050400500c0303006444a60b01c81803175610102d540395007199508500c1031240c0381c949600aa400f00c081c1c801096000c542032840c407400e084459102c448060036030300b0240b0000c2d01118030009040413a1170411010100c0380c40e03a400326902c0230250941070a00c800e50f080141d0891030ba500ca2900a0f002815802200c00301361a081c0c1e21411030074200d07000810090140e5103080e07800c0c40071001c4814100141c03210514102c001469410403410048030036541d00c200c50108010002130028444e80298800450300c0c04c903641d020a00b0012100b03643c00d003043c030b003901c0161400f8418003060b180d00411180d0740d1000ca406002e01c980020404105621070f4148410700e020302041141000040301c100540d07914034103001c0c0110000a507210a01c0c603401a00305000087d000348619014015004a01d404001400000d0a03028009800070390140684942c00012901640201d01c1d0004190100d803518040c00141122142c00d04041900b210080d000c400100d40c0310782d6001c04502e = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 288943920 1250 288942670 288942673
    0x90c12010308090105070219061107030b0f0c0d09120f031b03020d0906020c0a030e060c06130314070c0e0108030909010b03070c021f090b03091902060409060612060f0503150702 78
    0x2c0c06d030750226410800810100c1020200d003142000403d0307100803020701c131044040c0a041c1c01850f559070a02c2180c800303428520782060900000f1003510092044d10076080007104188070309070b024104600041c071070007007100c00a4042803130710075038030f000e40101140350391040700440e0040a8580128002d4200d100100001c80c0c81e0021100030030410f00243c4131503201000034160080b882e1502804190018220030701410b02480800618400800c5481d030003081440c0c00c0454000901e4212450042e10781c44a04c0c1102c0031418070144005002c41c6801d55100040b4010300b640c840d4a11507036409450101644050503600620600003601d0246410441c44c1c1080d40002e04242e00281d92849403400345210018200c2c101801340b80d10031078540c01003000c55001c0e491824180402a22a80c1000110781d4403c02c0300425021500c81004031002491048420031805441d181d00603c203080260b40c003900380e8201800804c00080c00c043d0300003102c40003001000003070f01d039000c6800307000b00052601056 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 288945170 1250 288943920 288943927
    0x9061404050106170c1b010b0a0e0405150c04030206070308060108100506090f0a0503010c0804050d0f08220c091a060c1f0204030b010e06130b151b1b090c12010308090105 75
    0x4000743d003510421b60320701180007255141e0b081041c0006195194004010098441c09200115402040d4003540000f40c102200250787c4040d158200c0b40b040d41d00080d0071481c00124034040c1a4404080ca0280034243e860602d1900da0410440a0758400c2c000c9a6011801300800301c1d2510b806941c0c2810070390f014040650042c0d66100013400c6030005035855020400007c200001c000040c003540f10800c11a0925841e600c203d0007000701401d4004108a040e0910304030162202e0890501c000105c0e5444801c410540b900c4550803030140000a5144041e980c810114509610b0079500790340c84010028000d1522001c2c036420f2204000080c0c0000c490039500b000003201082c1810109406440c81400407462801c100d006e0000521399141d100410030b18003c140c0d040c4d030fa180c40e102c541e982d0304004420348410f240b007421b113040149600542154412150401b00d403500c881c40380c090030b200480710003140c0e949a9000070014802c010031141c444200030014000110382201500c06002c040c5001ca06 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 288946420 1250 288945170 288945187
    0x3060c1902120f0408070b0c1207020d1416080a1a040201050f0c0102071104090c0603020307090f26030f03060d06060b0706060302100518120109080409061404050106170c 75
    0x1800e910410780c078241c400000409005c100c20170000c04c4010440a40c0042ca00000d82000f03580300c45074054000c04c4200300003000b0007995074501101c0c1d02c2680262401100100300142d55075240c0e146114101e0003d01781c40c0000c0c082c080850502900b642004801038819862160001c6080700200300328103200c1c0522210124640440103041605070400005a480c5800c0c1400c02903405190000c900ca50304001c90000081c2d512411281203070424140580c403619a0314050313a110005421100c12019407000010384804102c100c03c414101c844a5050140c48158045499202780c03448182c042c00c0030408540c0c82d00380b0500400e6242d014081c00101c0640310b4403410002d611030310050700c1080d00c83c0e105000750f1600310009000d001160070243d103003e11b00018003200607040f6440c00e1180b8140c00c0840d44e80ba10a4000303410003680084a160ba4a460b10324000c010481801b845503035840c2c015042002c0c1c01d082c071070141030707440c80d407110f40518070045c4e42000007110081000d81d081c00c0a010000 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 288947670 1250 288946420 288946453
    0x20907021603050303070905040b0f01032f0301090f0501030309030f020117190e0304260f01110a0e091003080d060f060c021302160b040c12080a080603060c1902 71
    0x4010b984500040c1d956401c200078000c08141080c3c1280d0700c030307500d001f09100385030b0380c0d11000c030600b805c007802d020507800d1500300f940c071341500c03070074505038403801100c41d14501c5042d001e0086058480064003000912003200d500c0040710001d00006021500f002c4c414000b054a140341c0e2280c0c0c600c1490000108032009014030004c04085d5081c0da01150500c00f1041014443c0c050f0b40d030b419400200440c149032030046c40c8111902440564590141c1801501a241c00c1c14000b142440d0185c03c004d00001d0700200d0050400d80c82180c18074001050721186510380d1401d0780b0160701442070126802007803811074413080c5840e03000d0201501010380d6224009844001210b0003001011a9110f801c455031035801804822142269141810f600c104015401e01c4000045c142409030400c080700b2556499184c134a0981c400350708844c040706903c4001c0701c01c21030110010b0400352099138440134240c481d081495503c01065414000c0d00909000c103603440c88c3c0c02140101c1c296030030310403900203417048811300c03 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 288948920 1250 288947670 288947713
    0x31103190e030606010309150902131a090f040f02011d09011401030606090b07080c0f070e0a06050102010203190209041e0f0c051305060d14090f240402090702 70
    0x400114041c6481042145400e00c81203038082020708003801000070715038506030780108041d28800d201c1d5451039058195200d09040b02896411094108480d843c00c4c061a80d40074900c2c00b00c41d10031550b101c00100c0c01202c4042844c0226445203000200c2c0310558019101c0150701041d100c8030040c031a4a100c116901d60310500c1c02031900707031035005034050418001020b03510f4036080072041c040351810801401004804035150035400407405616440d030024001c0c00c0076030307241d02e1104612513480d0108140401c900414007465008000300601c0e0356440c0103900381c2c0412034032480741d0065020202085120342c1c00404440000410004144045401d1030b00f00082e0040c1c3d1034442540c0d0042e80f814001c1038420303c0e000300341c181030113410502e903140317050300c002d0003402121f015500c040b442d002c0c0d440c4580c20052404881104e0078819240100e00c40350340d40100d98103902d01d80304407100074625040d0304c007664002200402c0c2c8011320380c5e02e540034032803002c1018042e03000f144034452002c0c1100081e0241d0 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 288950170 1250 288948920 288948967
    0x170a1203020d0b102d0e0d06022101091805150a020d060902070c050f0916050d020406051206011b11060c0a03090611030406080109200c03070c090902030307031103 72
    0x26041034480d002d911713045c000005200b4031800b008141020a610f42c004520f00030604e0121000c42c0e071465a403078410042d0060f0314001d407142d003101e40b80400640f01c1800840c1a144560344c00c101c9080750306403d400000302c1ca0400340c4035030040d500d02c01d54003401e100c015a100c1e080c16405454081e0300100302c01100d007598403001c3d80c1a40401e0540400c400d003a043c03130040000700da001001c03541c801c000410081d0054003024100c11646031b07405007030303000304e00b07540031031000103811529960740e41005092139210340f003850340304996500020f40640c05034002005480c43c1d00600070619480e40e98914945100c0e40707101d0b50114040c480c20300328034410001d84285611030750792844814036000014041c04c01c0003103103c0719a08140000e011090b8890241c0e41100c0c0c41400c04100720b406401800d102800750b440000c41810300003403003080e0301000801052079922072038108411517a07401c03c400c01c5901d80310009605400803c09000428071595844800f0200001507030310b0001000c40f804c903846044405c = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 288951420 1250 288950170 288950177
    0x2031312020a06050a0219050d180c0e0a0e030f0915040b19030504110405061c061a01020f030a052208010c110606010206180c0d05010501170a1203020d0b10 69
    0x82c60200101c5003c0d06801584201d019420301224102c61a80c40d48600079140800c800401c0c40000100c443d007089208515082c000d40d500d219074100344c044c00c03040f400b50a410801403c04503c40031554440c480d01200b2000196003410781c4406d600c0d409030300444103298082485c1d14440d419894141c001c01c006d10540700c01e1996554000a1103d01035181401182818503100801010542140701020340210840380003c481e510b00d8005100c00705040c0e0b5448100350003441c07074800c00078203074000364007000030b0a8900548030300c15004a80c3c0d4006c0d140c2d0b80c01e5035082030100e041d540d8040c03005032859011b810994082d00d44423503801401d030462075001250a03911400030041c501d80150200380c49203105c4015100c24600000081e50f10310024000f035550b010601d89207005020117010070945120010442c1800d06160304000340604020b000d05410b610700000a074840000c0024088981c59104034064020995031000350000d41100301181041522a1110186542e81130002003403e01c144c0c5 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 288952670 1250 288951420 288951433
    0x122609211306091406130e07020609100606021c05121e01091814250e0c0903151504060303080702010b0a08030d05060d050303010303020607020d0f120203131202 71
    0x3041c120350005502c50b4040c4050b0450a00459001600040768500f054503001d541e08000e03103d00851100d540e1102c00310000366030500c07a0456000c00d807a40100031100480b01d00300c914800e4182220464414070026078001d0040d4444101900707210781c1003074503508005041800034103041d41441c0013151414411070025408680c0d45021413465409000703a070004002c0700c01400302143e2207200800c0c016108083d1b400101d50306802c108071074488140b2803410ba555800c0030f148a503008240324020701100b42d840000089001c0b01c0981030710251306004004007140d441c2c0c603901030348940f406040040101540e080c6002551654020900250310a03601c0500c1440d01300c0000b0301f114007111007244500388044040002410000680b5501150420000b4240e2504000507502e009000f100030194000807000200b419008034160388120815025a900908098021542c1410110820380480c10340c1c1d14501c0403007103560207540e01c4482c40000c01c504281d80c2d2205803001c1640b00125006034000c8 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 288953920 1250 288952670 288952687
    0xd1802090115020601090c0f181a0d06052e090e010609170a030914031504111302070308161209050c010e04021629090a12260921 57
    0x10050940103188030704d000c0000240c2490001c045040d0302041c002027103d9204d110f1600142541d40301d00500945000c4400c0341c00c0354032460340c035420031b800ca000300e01c1c6880130004190078117507401c0d58442a030105d4051080040c441034030150740f05100ca10b04100c114800440c0c8540003c0c2e40c43d002c4c1c20742d6200c0c846a540380030b84081402941225480c402e07000312800c800002e4110203603005480b015032480a00a58010109107401c60a000c418040341c2d600c010b00c014000403060850118800351394040e0104000842c81040e03201c5c80000070005006000061204044010700d056458018548100c0301012003403010284d5071180c0c0c060721550841c0c00c0001c4035603040103118802102c107441c15030802c41d600041c1c814420444002801d00b80ca0742c2a020407070104216481030740d01000042c1e043c1c074280807004c2a551a02070b10210f411f11074542c1894411401203080184080401840c22161820b04203141040c0001400c500903078442c0004c1c0c1d01c4c2c42c3c08242d40c003402001142c0d00158a98050 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 288955170 1250 288953920 288953923
    0x2040315091506240e090f150301110405010f0f0c1e0609111c02060d020a0e131a1203031303050903030d0e100203040804140a030605090c1203030601050d180209011502 74
    0x600e43c4070240a008441c05c181901ca0101065015000380701013a001e50f100700105546c4006072011540c194605003940c0310303030f580301c4010b04161807082c0e0b9550781d100100d0b20146c0d486588254441c000c00e50361413034040060b240001c46000512481d50340848821a030341c0c3c100039a00e44007411103a4079a803541402007402c211424000201c0e8400c0c07000280065a00450401c0c46440200d81c21203400041e24560355004002602108501902c510f4003005d001000c00020108414010740402c2c49100840041c07503d400c2c4040084003900155196455450540c1085120820110709001040c0403c0340303650340520240a44140102c40440e080400320002030401c01811491107aa034070500500000c00e040c041030700c2c04d6030f15007034402d284040d20600042d081200340c1c0c070060000e41070404024441001080010341110255241c02070b44280c1142c0e2910780c0802c88209000610a025860a010194010880350340300000540c0a00c11603802244042074260000c50001401d01000d00d0002e50 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 288956420 1250 288955170 288955229
    0x3170c0115060e010804061b050403060b06090f061c02190e190303080c07050a03051206010c0201020d0507020109050409230304050307052205180d0302040315091506 73
    0x141c1024080c80a05204020f0a5068040411070400540360001420403c2c540d00040201440c00c50f0b10340d02022003003004110303600c540021501a0b0038015801e555090010a07105442802010307030469003a0a0107020164000c01d403180b21290424407200e211680b984000d29203060440080154035018443c040c000900d0b010f40d2501a1210800304000003120700c41c0b070030640e94140342844803501c400f08400006d014048002c0c0440c010714090508254002004160221b4405001c10150782e440b4015998000c1d481e10203805a0440750b07101001c0b6120314011302c180340c0305040144c60a521000490101c901c0305000b00c544400480e80001c1e0b0030912481080c150b00124029894030b4105404a921a0911f00c5424007071403c20452070480300d030148000c0110a105481040700e4644101c05008417032408140314003e0068003081e0302207074807074001c440a40f900321030800d07000f420240110004112205094402c2100008584d80d0b00045005900040c03190014071089101c0d03c01e198030800c0c4 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 288957670 1250 288956420 288956441
    0x604091e030f27030b04030507051b01080f04020a0303080a0204090911090f0103050703020d0812150a231311040303030501030b060901031208060f12070938030703170c01 75
    0x1e020300c4801e100c151080f800d80007600d03441100015140c0320f92030161014000d80c1001030050003424810000c0511035518000030036802d036115100c980340c094004191083c03d5401940103000403070b050022a000304045038101c06188401450646d0b43e100007800c0b9107560030201c07100d07000000c000c240c5240041049401504440300b01d40135500d10740d1002d949180c2031000a000d401c4025294007804060019520a4100b0b00400c400170701d00f60103004030140b0f045400c50710a102840d00072407610142c03048400d28000200869423480d000c001048580000d007848001859150503211030700109800c050b10065210b610080b980e5411490900d0040c0ca0040286002d1580034004102007143c10f02076000c801860f0402d03101940b5108041002c041c1031804040d000300300c0d684c00d2503141c1d038001481401c45110080030000c10b0900c47c50320100442c5440381d881640e0a8106100304444d0401d1405908034005044034100d079641c1e41c1d40c5611003010405000e007200003282c0705403404828010100d100 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 288958920 1250 288957670 288957707
    0x3090d0c05150405120d0e06090d1e05130b030a0e0c1309081b07090f021603030f0b03011e051f0312030f05161b0b0a0902030a06020706021308010e060604091e030f 72
    0x1d5060b141d00408030301000212f03e400803244241403001d18015070440705180141e101c040d4103d07484c0e6101c0c0402d075006450119800749081d080d5495040b010601c00c452800040c13106140705401540c8a014289075002941da03504100011a500082e02104403c000c491802402c101c81c60300c41c407070b02180c50700340c150040715004016229800d00300b00300b1212281c0c0d060900059020b42c42484900400b030b17028116070151301e0a00390081900d00d0b1800c5140003c0c0085043c01280d58508015101885400215031041034080b000d100003040301d084c5078414143d80c5000290038103001a0002a18802e6541c030340345107d24020454429800b1208003a00c840d0200b080701070310351640c0e07281d560700e1000344000c081643d501d0f2024115038003031040e41c40598010350300b035446040a0400f0b8000f58080d05000d203a91907480f6000075031200600948080d803202c0c1c0003a00040d51000d040c00050082e1000890300000c0c0403620010300307000c091034029151b0082e9580880c201e0b031008083c0a074000906999040c = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 288960170 1250 288958920 288958933
    0x10030e01230f040804060f1107091b090f09180b010905010f060507170d090b04061a1002120d0902032407050f03010308130b07030503090d0c05150405120d0e0609 71
    0xc500d0900445d81160140d1a198401c2ca580340001c03104090304000c5003485000b46040007a403091150405400d0100d040980313012581078603800e481c00b580302e20544110b051429810005d15542d90300008804034100c3c0016119140c9a403046620f40098000b020707100c1e69003006118218122510b000603249a0421a1800700300e5119000c80900017000320f285003400140310141800c0c1b98100b8a8403650244040740242400c0c03800364003030107a00d805254102c43c402074648407403400c00c4000018002907005400d12403052855005c0c164085110001116110845900140c4080014000941e1140d0328071224001c80c2c0c2c0101504a0040c00550800800340b0001911240c03100490b81102e9000c60250780c0c2d0b2500d103c03e5824010540d12100e02d110b8046204000c0c5034014000398401c0041406450710112440002d882d01c4081d91f401800c1903018001c0304080310030003041690072070300440c01c550b1060060000320005a0082c414481016114001f40c2c0002c1e40400015400c2908240940607 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 288961420 1250 288960170 288960173
    0x506041a040b042a1404110909070804021c050a12031b050c0a1a010603180c060503090715030c110a03140d1509020714010908030610030e01230f04 65
    0x42c0e1a001a001500c0280001650301440310b82d4600b056000b042003080e41c0300b0b0341d034407002811900b0040c440c0360b000c0c6041c81c03500c025080581045901e1020002d2031003000c1d071100e0904980300e00c00104102c2e0803803649039a001007480444500c8214034451001000300c0401482c00000880c1800c40352400d150034945200e08080401038548078001c401d280c040d803184040b1203214608405854040c013040d403011403812058010000c0d1034181e9400c0c0d18280b107042100d8906410703044a0480240c01040c0c0114140f140da4420070056801503504422a85865107070060001c1c4071200c140d201c030100e0303603c5212078011500048030558220010005d0b004d400604e8401410483d0544401800901c000602c082d2000140e80842901202c02e69502440b42d06c2c0c0c01070390020352000809031120355a404103041100814000c5441143d48158460b0454640206200220f0607101c040014503031541e58003200c840c800d100d5605185100750019004c4101b103c09415101406032040341c501861750304010 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 288962670 1250 288961420 288961433
    0x6050d020427200324060406031d030a020613060b0a0f0f0504051009090c03141509030a021c170f0a06060207080303070e0f180f0c0403020109150e0d0506041a04 71
    0xd03406400980201015017034100c480042442400a25900c00c0f00800c1c041421a0f25030b01c07880c503038000c15100c3c1c0308a4450300740196490240d81e06580040e4230000010702d030450005045040d080c8618000301710b448400c0001406040560410308001d025240104688030070b15000c04000c1006950800c054108406641c507041c18500524603038940760b5825000300003294060000550700301d034450b082410800d401c80d071120810000f03013a0304600c1d08049022068040110341404070030350020b040c51541610501c9000c860303940401c0501015152410022b0840d0101d148501a14012a090703464090250000c44005420910455000364414491031500000300e90300804142018010030700c41c0d00001e03409400e50b40503c3d821966069200d458165842d0351140030760440516007455541b0082203c450f80200d20010380003a814060800c000072462540e0b0b6008006468402d44d007516140c0850000b005040088a42d5031002c0e0411061003501c400402c81c500c05d45181900b6400d080e110003 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 288963920 1250 288962670 288962677
    0x4020403020105030a050606040803040312080c0c1c121a040e03030c0703030f0b0d060e0616020a06110c0303070513150c02060c070503010c09050405060f0a06050d02042720 76
    0x5d180403950707100401c5556894a0030b0b2030080610504607131340c90782c981c5001002c1d00c5808031200041840d16000c1400c1000103001c0d40c0f40e25100600510114a102c40c130248545c190340066024001d550034000c4548580d4001c101241d1b521400304800424048140000c4403515000d0070174079042882484920b650207022240c80e29054600403441704004400030b0010074041e0801c0758414010a800400c00800d6003091803010545000e842c403640e9641d00c0010010b0000381c4070b80050300f02c0e041e064000303049030340805156100404814209118130710b1061840c0d1003580d40101103100400c0030701c040110164400c0203046083d4100d041c52110480141140c030940800070b12505022484c1d40ba8140d0802001e401041c000300280180800110040d02d54034450181d94025414000011100c4c10490050000c401c009481411440c0ca0030200300c1d01604100d40a0074130035001c020010350001a100d48800d4003084100d0003a0010441603030004684805c010f6417455018515031a0f000c036229401d6 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 288965170 1250 288963920 288963931
    0x20c100801150e1f1d0a062f03070c08070e041203090b07030e070806130803090a0b0103030315080f070b1c02070c08010e1603060c051c0506010e0402040302010503 72
    0x1055003540407007803c2c1c9803641d1900c0c42d103800010024031035440c51010700c0500d210b550680c9074007406240100b482c8460080b40e652041d00712040180070040d0320300c42d9590f1450705050002450802110080d030100412140411003000e600106215090080f22407030a0024040d800040602c2481c01e80c0f07120048000520103020342c4040300c01460220b01a03044441001c1d40185a180e0301d00d00014041d0080106400c6140d1030722031184c000c00d03a040001815030051002d0400c2d8408840c0a50310104079501c02000712500f80561400a0300190150001d5400783d840f82e1004034090a10700c031000c20320b034a15802030302c407a404010010032030100441c1c02800d6442d000c80b0b159580030f01b500120340c2c81c2c02d02d0281d04551440050000e05009007502c40100703440c4048002d1021a4004078403a950b510f110b03105443c2d11000c8401000040c096600400c50b404590038224180b59890812803030702d00d22a0f1007442100d132035100300b111640e403004041d8009001200e0850900b42180c00007440790100920 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 288966420 1250 288965170 288965189
    0x1e0806010b070c08010c0201050106030c050901140717070609031701050904200a030f2001140304030306090e060403030b15071401020403060e031c021602130902030105070906020c100801 82
    0x45680521402c1075101000c1e144d400001d10000c1102e5100034024002481583c000a00e000151403c6c203205c1c0f4100c841e01c0005130340c1c403481840c01c11000c0255a020120898a4281546100c2007074041080503052407401003000040390200c0c0e04000c8e080e290140e1070010780c04030306401400142e9400307580d9074000b90410215180400e094101d840100307051404186e001503c458000108401c150a1035031035072298181141e00a503c01010449050a60b401c50201e00c0036541c4210b0000710801440d0720900070710340070400550b186010b0040303400d022100d0010381c01001c10070060540501403940c0b07940301a5407032000500300c130920710071070700840e10014403101d208038000940030400d4041e94041d581001c0200240d400303804466590740d010000001c129060301d081104082614803c0d02e10382100c000c40e06851000036800c00c00d45851040c04003c0c41555660200090384091081c00d22030180ca45690f2103480c10040007030b18050040310100d10411520403a81001980510501c4c1110074204 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 288967670 1250 288966420 288966427
    0x30e0d02090a09030e1504081203250201090f0b0105180705090d1a010b0a02120906040905091e0c041d07090b010210020a090e06120715180801061e0806010b 69
    0x2400302c4100901c1d042c1c40c0e92011a0306c4851002003240070040040322620000c4074601007001c5001c4900340030032078624034990212410780c00da01c00054820705000350b481c400003507040c0c3c035075030340c0380003060b1400d02a182020440c00600003410038814440c24a076558260f070403a483c120000034032034440e241030b003030203800403030011005c024050503001c122028156002d41d1641e140c030a0b6850b16082505000700510071801e84540940d8100c0403106000c0c009080146000d042140e1500076080c080c001d4a0503200300d95030494044c4007100d007002040750001c05443c498501c44100f10643c0d04103585007040182030781d84692500f9001859508030740c3d90030b9010a08900c1c48006030f05000050b030004c10714a000060981855501002410a862144026444607214001480031600c01014001c130594004002840400c83d40403100d4030028040c90004980980440620000e11460340111826911800b061148801540404283d24915401e10b90614070b0203913405c1c0c1d0741c0410b1044881200000 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 288968920 1250 288967670 288967673
    0x1200c13200a09050d0c060f050405030f0f01060906120204090314030907030201140c0d080a06050a1e060e1e0d1e020102060f07050d0b030c0301110304030e0d02090a09 74
    0x9401c4144640008125041801d00d180481c11440c1e0001030b0700e60000302c26000104a83c9001070003d161107400c0b02c020315010307040c107100369254550107000ba070501c1800c0c400041c0da681d04009400c022250f06001c1d003800d489070346005080d074120350004441d040c2044422301c2001070b5061004691501254081003440c1036040070f55112011404c0449221000410005803400014112044138401e0361074114800300000443d682e0300070b03a180b031120754010311a002a1540725140c0a500449441c00003c3d001c1daa0320000380401d03030749034000c0b07115802c260707805010f820f59221004001d10b0300d803d22400c2044840e0004030301c1000322000500d154408902290303030b6200d072840c1c00c202640c452040014408000703840c3c42d09043c0003c08030b00620601002510288901004500510280d00d80301e080c0040814410040e042d1a151030343c2505c595182d002c841d650900074949404252044130343d072420b250500515503201c0d01078480c0071700009400500141c82c0c010116900c81c0f203c801c00a01401360b0f = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 288970170 1250 288968920 288968959
    0x12090c03020a0308070512040b030f07030e03031807150912030c06050118050604110d11071a0105011206030308010501051b0708030d0f06080a02090417040e01030201200c 75
    0x200d40000e90060108807020041141800041003036078001c000320b0b8025454604604014821805180c056400c18400b01d54840d0030007100075000980f9060100c6c0d8401e18010742c0e071968008451170101d030b82d000000d0044020741800420098140c0c0c001031011004100c0c03020b00509910f10030300580e80c0034101c00307105040c46034003403501c242c0d4401c0c0140002d50707444201c0018158480383c01c210091901001c51510b113070920a491002d0740407406070341441c1c2003194040042c00084101039108100700003580c009a08040622144400465000d04550601c0001403d4101041d8102041c524004007170000c00d4004001030704550091170100e5980f01000c01400750a0421707003800c0d0007449290400301b044a008006407500e00380381e080401c0315002d40b01c8030b0000d070303401842604100d80007660904050300b02032000c03590090140710341c0b41d1007003183d0510640316800744c0d114000382c241e1040140210f69001165803034010051800d06070750700c0b145c683d0302d840e070340d8113032880e44150403082040d002000b5 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 288971420 1250 288970170 288970193
    0x605241b0609010b040b1e04020a02011d07080106120b04240e15060103090c2303070303030506150a080a1a0d03030b0f030a03090b0904151401120b011209 68
    0x1100e09440450400811080c0a42868162188214140292410107050445021a00304020140f0840b9008001c0034007000b9030000c010701085548800d60385201e141d401d81480030150f501c000829016180a00b0f035801c42d142c40c1c00140c10340d6101041c140100c0c803591040f542054003c10b180d012003992070901ea03c0c80040103070f4005081d0800d00c100c1880a0f021a8219400c0c3e01d0b82c04910302039980000440403140780c204020003501038914244403080351104003801001800c0c480d41681030041d800a0302d000c2c0c0f03541c01100002d483d082000f4250503d00307200000c030b11840c0e40a0382851006a8040c0c1342401c01803c1510146e500c1e00c600b20900b003900c001c1c40d0441c0c030141c5201c0e08030150307007801005024500f42081c0203600404407800b141c180014a90b0354a80c142e07550b507030114101071038540140c2c0140e0481740d100d9100c22142c00d50612219541c1d004189040c880340803802004005010b03911030466a50120389000c800215998004440c108041c001d80740010320025540703000c0d2107001 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 288972670 1250 288971420 288971467
    0x102070e0901020706150b0f070203030d020319060b0304080a0c02011707030b03010e12040e07030e061005040f0606020d0c02040e070e04140a030518060910050d060524 74
    0x2051a040c807030300340c006600500d1454040d0b0010f01110014074010003a6407480d10411081c00d50030000040803000311800b6001191000741940c1c60013100c40006020380c0c0003a554110111032811041070408400d00c0303a44010980c0028940c02c0d45099120820306000d608101030034060b948041c0c03801c580c0700d5230b283c508001403081c00644c3c50a02c00740081c02060040043c0e03004c0d41ca0640305c2210500000380d2000003044910301c440c5040d05208441c08500000b6103510305054646001c031010316820301c003070340c451030401301c100f050646000100710680b0321800c0340c001801c0c039202060140b00d501040d40700c2940d030ba81c10425000012440410018030b08147d0a0103a0300810b07501044403950440d85601907809030240004240d403d0583c0c076280d200301c3c40010b02107041004640b038604c50720208200090320081900d4182214131f80462411071010030510001034002402070000541c500c0b402c0040d140a45284e5940302d010340860850301c944801d68042d0842c0880c4544120111a42c0b201011 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 288973920 1250 288972670 288972689
    0x70b0f09061c0507020c032b02070306060b07021017040308060d0c0906061403071d0a0e04030c0318050102030403020f0f1203190f0e01030e21040305060f040b0f06010207 75
    0x601c10b80500003048140d031801c005004a0904100ca803400007208801603c100703000b203201d4070900240b9000346000c2000d50096000d91603001002c192984100e600030083e02da07040ea5a03140c42e00c101310304005c3c60700120b0180300c00c401f40c4104003440b24640a83c0326600d401d04941c2c1d0b8072440005005a8503045004007443c006840c00300f43c20f01c041c4c20100440714aa00c0302c402d0a01c0d40640c80d8100d01040301ca64000401401c044000c042c1c0d4820101144200900b0008146848030070700d002401d02100d050700483c1400342003c0801d540b015030b80195a4410f106040340c5c43c00e040000b5100c0c842e501c0082e1062400300c020030302c00d6940348070298003800001d100700b40401d03480b2035560701c940281070150740940d03101c25090b01260064003452420911991480e01d096540d2006400030300c1c0b01040105035114541c607042c50311800580e4003841010b013a08558841c1e1075841d025280c084000c1140d500341086000f440700180c802e800c0640c02480800c02010745070b0343c1c140101d1400310a6407280c0c059 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 288975170 1250 288973920 288973957
    0x91d1b130908120108010504031d0a05060f0c0d0203090307180209040203070807030506061204030807020f0708030d06050a060903081c0f02030702010b0f06030c0d060b0a02010b0909070b0f0906 85
    0x1044082c0d4014003072506188405034407030f03036198180307800ca8404443c0900486e111403130701400750301e807015050100500207007100e541d1307503e60001c641d441d00803010300f500d4002c00003808448004c081000c480041c2d840e20003549002c940d1008291905958071903aa4040c036443c1d0030318007602080c0c041d41c11545003e40b0864592400b150020005502601c2c40c40200f441c08001c01c2060801004803100c1804281c03401d000fa486582e003c03a200f0700b006101d041140a00c0d445540104000d115510080c07640c0c000035501c0d14a4950b020040301d105500c4140302d101240000c000c2c190300216280c0440c0d4000808039202ea0080300011440c4c200e80b44a5400c41c1e152203d805071402941c0d001d58020f0354194002c22400c1e10203410301c00c55180e503059044e03202c0401d000060711410301a00a22003d80c00200105001c2c4d80c440041902c0c1e00503841c1840546d4503050a08006c0c180019081d41c018844401488020328141e11003202d8401d180344140d9180c0f001407141038907210507045030701c00300400d8000c060 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 288976420 1250 288975170 288975173
    0x18050d12090813050907030608060402010c021c0b0105100306180c020a080307020a0b0603011a0f040905010905070305010c1d0d061820010f0206220f0309091d1b1309 73
    0x8100f0120701907103100e01651008110603c0c8284510001d50b494076004000f00e80b550b40054130f010504560486e070196000c1c5103050340c15609000b842c1c035188140810391a0b035041c142000714800141000c1c4003054071b803403020800b09031100856035030038106000c0054200c0c5100001c0b0308002041802900001c0c0020a00841540c001000440140110000769560710341d14101401e8030202d54044030544c000a0350042d50b403804441c03040d60340000400c0013602e00c08950f130751400d54100140036101d0f0341106200f00140100be0042002c00f918910700074806011307545449103407101082d28240202c0e0314400c50703410085d99600002010a034014000d1094400303291000300e1030603122001c600d00c1c00c580394008455000e516074103410000da4002c3d150036a2882440400036110740b00c94226001c01c98071030f90200707951484180c10b50340240d035841402800c1180345c0c81130750024050f1406000c071000711350380a658049510455840340f401c0d050100c1e400d0740c0000d00c85040d6100c9101c02c8074a800580030 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 288977670 1250 288976420 288976447
    0x1104050a0602060702060a021c0b010915020318010206100e1b030108250803041403010f023004110603040c080607030213080a0b06060f040815070318050d120908 71
    0x4d110384029801c0301c209540c4d640800099004004000390245140c1c0c442a0b0b004081d0f801c0603081ea0070600d04200b445545400a0207407824504a6402580000610149291400c2c00140c044c200030b0009003500c0c01c0140c00072143c10307400c1c883c0611000d1044003061803c210340722002200070b1550061612540c58806080c5c82d080000340d412031021910131505036040d840e40300303035084030b8190018504003442c100e0042c0300e80b22812800ca070706540e2081d103001013442c244003424007844400004050740d012240c00c0704120040c0445c10404500c003c08100002c2c1c0b048d048010316201c140c610946079103071031402d08440c03e856041802e05002d0007003001705041d40340d8007500d030b03c20b0546000c50403203507240d45075601d641751004050508110080000c0060406800500321004013402107443d045c1c0d40c0502a08020344840c002412985e82c206220b91175526028100e038514040070252150310342550364550b513444010b4441c09020301c8801040b400040383c3d225031009034022480d6070395940c8401c0140c = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 288978920 1250 288977670 288977683
    0x6130806070206070f0c020a030f08070b09030408100905030c1e150f0c0901171911030f0703150f030803010905010e09070303141b0106090b04020f030a1104050a0602 73
    0x80115205880019000c1480090418020351094540607000024510104d0303810601c40801ea81280c806140040001c41c200882e03800940901c0b0040e8850310a4a0940d8144502900c00360017907000380400d0015180120b10a20301881042e400140c407026403800c0ca0660141403a865000c0c0900030b0207060980951006164805514041d5884003102e907840f0340030f074501074500000e90780e402e80014a0710340e1818000c11740e01c0c105042a1944006030303e03c111070701000300c910360812940140d40641c0b4010500440700d4200741d148400303003545400c00b0a0041100001c1c55070003050348034120a00c020b802c002e070b60805082000241300b05075849050103029a1b20038802e022607a4940b5000041002091000c1401540301802038a0031a2030f43c3c404442604a0303800d001200a000c01c02040c15216489040c4914041c0c800045841842d08203050300300d07040420b00c80d01071401000000708401e981c0085940c001c125020000740140110111b030414066a00b0981d041800418046002174000412 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 288980170 1250 288978920 288978929
    0xc0306080c01030606021c0309051e0c0904030c061d01091a0609040803070f020304050909011e060b160c150c0605060604050d080a12020a05090102010b040e0604200613 74
    0x1201e208011000044040320072501c245001a0805115607580c400d000c10001c03182c1c0480e01c1c02082c1e182c140d496a41c1010500c1c280d4111071100111a01d40c04007083c0042400184104d035009034500d81500c1c06000c0103400e00005094680c0c0d803042d00d14035025000031340d00d1501494020040c09526140000e0318112018103d428454018001403492800700080f03840f555001113640d0031074403582400d607502e031170340308981056010034480400c00d515031070310385807041c05482c001052008404504c10481804000486081800e040050124000c2e00c4212501041c924070f603000c21031007504040110071001d8100d00c824203069000c01003004d51080046810f1402003000700450789071001000118461403003440d411194a00c54440820048400f4101c0580e20f030400c4103160318410300700d40c2240d00002602002c550003181c4105156070901c200c0d0349284096804002181581990720344d50000100010f01c041e0001d000c0700a1440071200c160f1035170801504441d110703005020b2032600308070903005 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 288981420 1250 288980170 288980173
    0xa0f120b09010e0d08040602070b04150e011103012907030305061813030309050a02100306090605120a020402030c0d110d0f14060108060109030b010e07020729090d02040c030608 78
    0x4a0070001c01841a02100010080102441c00c81c81000743d4440400a00999107583d0a105140101c1c0541c0000e61045210307004003c01c240d11110660100c03128881c0c5640d5580c907000d92811203a00c040c040340d064400008074681c4280c180030220088031012060381c5071a64000c5200020180c25412480c051402190320100c80b07101c03220001c10854080311607980301142e4103035107808240a544081d52039401141528400b50558002c45c64241003a464900066034446040100c6049446487c1c0649411604036400f00b298441c2943d6600340c4c1c800280c49140d0000c003040d10030010404030703410103900d42401c0c448058020403540c4127400000300ca11480d810581080000013452186a00864040461036500e8031800c00450321a0070051405040c400342020210103d4100010711b0300a020000a407403142c03a2410740241840820fa0180c02c0c000d0201d0311943c0b80018010720110a44e4201070390540740c034054030005200140c01c12010390811710741440d50080c2e90b8190000300c140c1d203c400 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 288982670 1250 288981420 288981443
    0x1a04091109121501060302071e0b04060e010e0303010b0f04050a03060204090506040b1c06021e130b09150c030702120606091510030203090102070515150d081204020a0f12 75
    0x10b030240e440e00107200700c200a0300e2010303005200c0305009a003c0e2107114020340c03001191240c0809411003c2c20229019504284118104410800030b401034641410100000b4410700801100080d900d00040c00351503c20714000c1542443e60072034105030340080000604880c002a502d091001c025070184c025185210305040c00070301281440c0c06036148072213000d41701c11540404d07000e071f681840c0303429203049520310340070049074020354410b01005244035150710000e5507906202190100600041e07000d080d100c0418000301d5015580c2c50002810305448003201a5a20480e10b1241d05500c40c12000071f50000880b0040b0f035a036000010054400c4230b056440001c0380e20307240d070036035442510125003550000304005a40c00c0385100350061908100b04100260800015940303031400e110343c04c4000c043c0305c104034080002601d40b9241211405900b40c0b220410901503466020103442191780d2301600a00c050041002c54480d40002001401c00e40140100141c0715011101c801102a5040c0e60812020 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 288983920 1250 288982670 288982699
    0x60d0e060f041a071e0c0209100f1401051603230307031505031c030b040f0b090c0f0a0f0c0b010e0901060f0509160c050a0302030912030304020a1a04091109 69
    0x140c210b8000d907415114040b9100d041004081c2d103181c070364081790400403001e000c000141c6800510900a80003803244814083c200340c210203490030b86501c141c1071000040d20001259030440111031520400d420010102200c07402c00752803c1482c1040710300d0f080b03900c081d014420742040c80554002c04940d50180000b018640803080e081d59540110f40d85900000341c04c0e540e00d59088100126913400c0d04003c50f844107000300090456542c10000b03101180c903500c2d608414600385031825440b03003503480500d00345009580da1044c035004498010042c004003a00c405e11080c011014828085c0c4d2002c40c8201960711003072084000b010681e4002003a40c00c8c85408a85c2c8140c0b0150101545c2c0d02030202d04c80c540c2c03200f9440d4800c04c0c2080745e90081c0034044180b0004250705101c428425402500115a0f0b218200b042c000700460020015803207030000c3c003d2200503918030400c1ca04503031072056441c1d402802c80004100c0380c400c2c1e0303000c14440351520508a81d0203506002420001d14200c03040074000e040d5 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 288985170 1250 288983920 288983963
    0x1b050a030c0b0a1406212a0306040c0e040f0b090f0d0507050604110103020c0d1701060921050c04020c010b2107060f210209130204060e060d0e060f04 66
    0x258131030101c1512000001c4c0a1301b0100202481d429540f050f85011412540d00a07080203251500c4044091004da1a40d00c984201e0075031490440c01500103100b0f0f454103883d111a2030800340542c1c000d44034600046420f10000b08940700c080d503000400f18105081220f00140d96501541076209140980713103200c20784038020341c26540c1240d0070102a0001c1d0756559513a10781482d80f01c102505251303080c4415a94441d003001480782140e0a03882d001c4800b004880c0d5034981c280144d000030100841464180443e09141e00103040c031208003134090f64201035500d40300f130400c2c4401040c00d070014400b0500c4981e1041c15017000302d042d1819520701c80300c071070140b1002095201440d416080b42d403211100300181481440300210006c2c651030003a03a0041134a80180024010f43c00200c4599002f00d0030b5030161402801100b6070050310030301149440d26205015083c000c0c0d00c40c603070344180d0740070481c202e0701e07034040d0403074807008040d001aa425450240108214220160341c15100e41c20606001c0e55903000 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 288986420 1250 288985170 288985181
    0x1b18130512040510030e0f0a03090603060927030917070627030b0405070b03010311010e010c03090b0a18080f0f03120103080702041d01061404020306060a1b050a030c0b0a 75
    0x2002d09010360032140c0d400245d01510100c150342402d0301c103180c40422001c40c20301c8845070442c03003903495051892500e40c005041c0e81c4a03070040d250701458010750400c2c0d10f001182c03400d0b604010100d00ca003080f040341000d03900e00c603282c1d0188140c05060503901040a801040c5141510403940303401003101c0114003000c0e0000c00c500095581c0419403c0203201280d04001100d501c03910450885241d43d4441402c0b47c03840d00207900440e10721074201c41041740303980c2003100340040c10028070307120050030308540f0000c1c040004d5101d00c8182030030001d0f402c41d0644c07261a071110310003040e2218003845aa140310f199542c03800e403d084621030080e0805c3c05084100841101c45903d4090034407003d90b401c1d0348981002d5400240200e0b4010380d90000c40b4494405004079074000810907000148403441d2480c26103060f19003202c0a44154070400030030101c0c2d5107120580d5a83d02c0c8030f28280c1000024212044d0700c1e20f0340788134013504074490030f99060b0800d5440074444120a1003028030030601d40f1500400019280c = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 288987670 1250 288986420 288986429
    0x304081612080702030f0f01020a030e0609150a0e010e0c03070501050f2512090303230315040915050a0f050402010206060103090c261e1b1813051204 66
    0x10009428640420703103803409000d0050004041d1031b840603540c01202e10300b80254911680d00d94011640098040d0584111803100a00b48040e2030b4a141041c000c940390000e0288500c800d80240010400c00040759100300141d51a4000070011020900c40d626075400c90001c1840c880e01c01d1070004111940b143c000d48ac00003520147d25824403061495060b01702e0041544070722060b0101c0020004102d090500c010b0141040c0c440302a202d085080051070080c0344083c4180e010302d0310501c0555030504c1011a5400100148180440d800c039038001400351500c858064240101c8a031102a040c0b010f034001c80c0a518803030003c12030b484084004400341c5900704d07000f9000d604001b0004102d54029000300340190303c120a07880700c2da600e4448034108440346042060800300c2c85808104c0b51a02084280d0180120b030f1050b900d0118204d030b105607039011008641401c08016888214981c4841e40c042c0e15031100c0c2c0420b90464a0b01d50b5400c2c9000b2103042050715603100b8014041d241003104002c9030240c5 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 288988920 1250 288987670 288987689
    0x30c0915090504110a1e08120a030b030c041401060f0215041e0b0109020c0c0a0e0c0f190302091008013002040c0c05061006020a03031d0601030503040816 68
    0x364a03108601c001404002e0007628800d80e0114540c2c2c090340c5004580014000a004041c80c0303807a2401402c0c50486650080c9034543e00099001003101c080c001907510028407454041021400000444d06100e40c545510f500141041092141110a0725120b03042c1c1d500c640d03445030801803c403000c981c0c4103a40101c8420181c008800315010503a0040804035120f0b5010759500003008d40d036503842c00c05d00241c0c850915a03502003001c24000d142401402c1c2040c0c400c070b881d101d05c0c0c0d007400c0160400e01c4001e80700380041071000841184136601c1409852244103c9522011512360420b0094003940c000c3d1080740c4210601c800017041c2c240a4558141603c128510f13003140700003c0240100006440110401886104030303581700160341c3c44c05401d21130400c941d649440f00d50b840c6080c0d450b113038014000381c18040010000703100850f800104105003d80610f004204d01855208486100d00030004103a40d902030000084140440040200102c40f601c000b101c9801303445041c021512420350085840f41d = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 288990170 1250 288988920 288988961
    0x20307080403060b040b130c02010f060815070c051c09060f091503020c060a09060b150702040c03061523090109032a060c0b0c0403050d0f11070609030c09 68
    0x4610303e94440c9100c40009040007404801402c00140000d41c04216681f00c1034840c10a00c0382264280916800c0d5114003209101c0790303003846000d43d1038000201407100c8060b02c40c1e0000381c8542c0724a00114102e40c001d805d541c030041450315001400e84c400c030907142c08250050000511544102601030124040350394000d00141064158813401040c13500d1030040540038040b403400e490083c01414043c54030130400064042d824078000003510102109184104184454004040d50410843c1e050340c0e41180c0c0007440e41503005058000300001e130044400444010102000c95800c40100110703072460030143c201d80c40d50040d10704507900c03a00d03440b03e0005042c4401040000c41c3c4000c1040154400b124221000902c41b03802203515150768051000030306071031000d60a00a4030414260046403140d01c0900d4642035803181c45d40d03152400e00920802011580000100703109400106286c0201000d4900c81541c03040c00030070185060100351001c45a4000008039a030039482003e0000d100440d060030f9 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 288991420 1250 288990170 288990173
    0xd1e081801080c0306010e0f03010e03030f011406071b030f0b070206150109180905012a02240a0b1005090418050618030d020d1a0301050105010e100210051015020307080403 76
    0x4200708840086504001e4402e1032301ca241e0742c28003600b03c0e00c440740c8009640b6850703e01c0ca501008001039100803400c1589189500041c0c40b02011600d01e0b680100364000b150224400d103081c0e030111a40090b02250070202d841c4100001e5030300b064020540791382100d43d0b5803650301d00c0d00c099405410368540824691101000b650003507144604000c80c080b20005035000301034903000e00b91034072440c42119002c2c8804101c0e402c906150b5000045010303520041c503024645680e44500c1035641416038020081040004142c90400e0300100004040036101c444901c403600000340803500103d612903c03840c204042616070a0b410b24241d100290090018a2140c480500c0c00c1c00ca08980644407803070780020480d01c60310764998001848004803141c0c1c0010102801c14945840e1002d89084505ca641044010081b90381d1000e080043c0000482c1e42038410008075205a1800b001d0710280c1482d94101810040d2140403524041d04403a0040d51f03c4042c4906c4150407a103d00c15031360001c03c1d04005200610 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 288992670 1250 288991420 288991427
    0x10c080907050d0204110307020601030c090908180d120306140d1a0405030403060e2407020a03030b0307051c17072018090d020f16050d1e081801080c030601 69
    0x10f05400030b080050038081034018074200394012200e03100964004001082040b61110502005020284040068400d0307a6152007540c860340b217400c1c03100000c0001c2c09a03c0e039608036000480d01c0c2e0104901c1a0004c039140c029001d072010b4420410350300c104410004190419485417900d240e07014400c0d0003507141070603400c0403144010b4420354451000f8800440007407407501c503540c1110299030042051355011902c43c01001803801001080004480c24824465000180140400c0c0c1c181800b1075184102d00c0071a290a910342d02c550350002107040411407150707100c00e400c19070034040c0a00c4026035203441d142e0780081c498007900a00705803088075111b0030f0801280030040d81c8140204800e60206c001c0340e107203e50110548841c02c0d83d401059110034016010040610503019210103002040d071000313104820354666100d89401450010800d108010500c011034001010641d21501c0e85a02801c0415980d040308000c2e07603804c0410743d11100c0039800707980c4a52044030b281d0080e529540d224001103 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 288993920 1250 288992670 288992689
    0x335010e070c08041a070c09091b060e122410091404060b06040f030302030942190207080606031f18060216030e060c1e030408190302010c08090705 65
    0x5e00000c0c0c0c0c00d00807100003514444038940284204800440c40c0721007804c000c0b46641c5c100d07100011039051103038104248c070340190918500325001c8866858240c88440454180104020840440d64601c5441d0700a00512a0485e000384642048103d100e61206c8083c0111650101140c0c0810461030004000420507000100809000743c440b0b81440c0c5c0e5001103810a034140d4201703c0c0941c00c089020113482c10a002e036110314601200420140a06840c1410114583d0804c0c0c0050f88a0300322860707048005031800ca400c1c03107001601d001c0400d050840025140c2c146409066114000c000200300507240005110000d9076134240214214254050000c00801c96542c9032401c60607505031941c0821081c0c400703004070086100102011001030b2800070252074803500b51030710602062001c0f104003c000216850a503540c0a001030210489541c8030313280d80074590050ba031030320031419081446414404000e82d6603100c0e030000d00c544849060243c6030381078103c8510030745502001e400c100341d180215a0 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 288995170 1250 288993920 288993959
    0x3050606091305010c0c1109070e04020a0509030f0c10030e060112060b09010315060b1c0c140406200303190c1214161403040335010e070c0804 63
    0x18000030b4215940b8242035600c4000c800e00810001c80f075010600ca170039544008070391403c0b40c1d1800a80341ca0b1102514143c4031180072400385602040e00303881c1c0da01030000c070b03113441d040281241c000c1041c92005950321f02907500800d001d10540c000e203040e030500070702606081040e0900600041da00b49040c014007116180400e9841a03100c00166a8507182c0500490285028554407507401000c0f08904096607401d41c06210880d40800c05c26900c00b001030054034900c1c00388003002ca004100e041041764400760003141215442d00c005000540b10750007010350407148007144919400320f03280c009060380328042100c0400c031080c0040d00d030a650b50300356400048040c5680c201000c01a00a0360850304945000b110301100f280410144850340011880c094590031142c40d01110101000268016500028200405012005101401c50744010070340e038840c5030030b0480d0380c0445840708aa0403110303102889000303102d4080d24081454180300d201504401d07600b1207200b0340f8081c0340c4240070309800b2140c110b = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 288996420 1250 288995170 288995191
    0x20c0d030504090510060905010c050a3c0203070f121205040f080c09090303010f030f030e09190c0203090102070308030606190c030201110910081314070e0a060305060609 75
    0x400f05090078207203e00b6005100b44516191320a003001c074080d0541081d508854140b119030814140040c1c0001951020a540515092320512094241402c0030000d03070708010720052281c121901401e050307030000309024000c4040f1440d499480040100c131072098020104013041d16186040031660507040c1140d00440c0b1300d890fa20342540c82c2801d032180c9c85035410150444d0050031040c5010310b403200c00d458011190b1005980f46500d0205c42d130550f000c5611004000c01d042c4903920301410300500b814039207404041c200c928036203446201e544400903850a0030303040a15082c024541c4a20020a441050206800800980c1e04503216281d054100400041c3e000e0000c01c080d2107084500d050008400c1059103954101a20a00c1c0203400e403040c1c031082c0c0b444e15200340549419580c6200c044501043c0b5402d0603a400d45940209070000900301d80701270695a01100c411549803800100c103401c4400004928440c0d4442d00c2040023540e4241c0f101130090f600039000f207501b83c80c04e5501c0c250003294812 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 288997670 1250 288996420 288996427
    0x9090b1501020c0a1401031b0c0f030309080406032301080c01031a0d120f14070227090304180e0303040b2805060f0102010e0715030209060d060302120706020c0d0305 73
    0x1800588280c0307581c2c02142c9170750f410070000c0146582500803400801202d6403180303c4442030707040041203000d1804c030107402524862445024940203501c0b440c0016004012035546a4860708050003400902220801c010f48000c03042880c107441d030258605940f0060301921302010a600110b003c1c0206548140000c40c0c040001c080d02e50355a00050000e52107104041e0001d00440310241003c000c081008050103040320b0180c0e1403400d0b101c1114102d590442d629917000ba1484444800703c031181004251212107407040c401c052000001a10440b006d1400e001c051140c045035520603071300e4003000c030000b5038410300c04140080e804542d410f5022010056180d4204014200050341c9010050451034444d5940103028450820303210700c00d81e40d0400e0000f400522200513019556217201c0c4960307000140e4a03c07221a01e18400e4044130801640200701d00d883c0c1a82d011031400501407840103d01c10800b00602c00050100490b8141c11910150090907d0b44134103002d001105070008821400c200080 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 288998920 1250 288997670 288997693
    0x60c030c03040e060f100c080f0c010504061e0216110f030a1109010b090102031b0708030f09030c0108131e06020403061b020105011401200a080d0609090b150102 71
    0x70030192000380140030703203202181010010701001228210301c04d0b000700f0a82015400c5031360000e00c3c1f1428182e002507042d42e580208694480140607a140303003000e075402c0a09001c280308090708400ca0452614490807080c05102400d84100e105100001e40141d41c10f1210304041200c18034001c0c00d425014019108041d8002c00283c06c0c00306039001241c18422002045c071060400703140c00e42c09042c103110140d103004070761b80001c2c4d5280030f00444034414401c4032880b0030080605100031401854550101c1c1c1d120b040002d22944c0366004016aa0f0180c40f824104001e81c4d0302c200c40d0a0300541030800c0e40c03440e202041c0c6440124040b240b2240c0600c00b0b00c1d410800c006040340c0700500081d4001d810000b40c990804822810007020b05074030b07004580c1480010700034002c1c0b002400711030b40e10900344440b00f245c404002503400114030078a06070b5802840501014011428000d024200c2c07019420003500e9116480541162000c50002e4180007040002a4005035004420300d28014140100c5042c01d42c01d = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 289000170 1250 288998920 288998923
    0x70302030a0309080d0e1e040b0603010f08060609011a0a170a0203041a0402090112050f07030321020c0705040b3d0305090604021909020c03031501180302060c030c 72
    0xc0792800c500150004808100d00710081c004d291640c143e61510701030005036070000030b03004c0b010003103168808560003c41620300c1d55168820106c0c10b202a084549946c4d6031802248202000d100d030104a00504001407058030b00086060305131000890469075085109a1415854000280e040d061100c40d02d01810041035031009207104048100016941340781c1880d009241d9006c0b980c039007003440500000d000040c1c0e01c00305c14605607120090b0b0000403500909141c0e02d0407030041c100b0403950082500c01302c103241e03009640d6107a400f00d41202203406451082400124420710301180515004420140100c2c07070143c00c0560710000092402c462103541c058601928599040c940f0045401443c80c03050395038141d001050105102d080802c020301c1c10301003060729243c0040000f84142400140e08048500803442c040142103048800c546412080d454075543c2d078000d5910000c40d164414041e0040c3d03100d1070140c11040f40b6103030096105465a401d000c01c3c0d800002c541481c0e400140a5801d03020300 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 289001420 1250 289000170 289000183
    0x60f070c05101a0a0621020c03040902030405010b01110f030403061a03010e01091506080a060908190201060e010506180108151c0b0a05010602121312030210060603020a0c110307030203 81
    0xd400360f4008000c840b0341c1080010402a030108050107048641e028811400b949003003008540003102690340d0031791030040340c10f51150342c1201031031510100603c420301c2815400fa401e100340a807124044644900d00386940da114807003086541d54001c02003480012802e80182800f04450240b0010301000b290001b401c0d103880c8000740d050382e9910704117a0140140400d6034081e1042403141003040c5800e01005035225130703905401400241e110f0b40e07600d0030040c6003003c440d2384182202c2030102c213000d011070081c0680451301c00c40003080052400460780e403619104441d29268000d1100740d0b59292800151080c1100070500b000344170303270f04c0d100184e50307102d0b40c0134481d201e8000700780710402142c140385c0381e00045009031103c6907142c6001c005110301500080c1d1700d44582402c080303081d282d61440d9203240c80014a50040b120043c50040700e40101900010f0407402098913020501c80641c941500310100d024003445000010b584024038000f0928207000c1000162010b001d031032003603031690046440c0c00f0 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 289002670 1250 289001420 289001441
    0x3007080c0601090e0709050606040314030703020601080c1e0a15030204080111070209010308160c03030917010b0a140409060e030703021b0a0b090607050d0305090c0102060f070c0510 80
    0x180050052030000d8140075860142210310000c020000e04146020341e100c00b0390043c80d0313005540b00045101940c5100c00c1d90000c5510110b81c001036030703a84514a0320381c1c10114003200988582c000100c1c808102080c840e8a1a0016003900c15120341480b90000100043c9029030708004d502c05d000c00e18181c141c0094681040030b450240c0c0d214508010720b800c441513114803080703410b03040c40500010f030b450302c2c0c03600c1c112034108000704d07201c031180150383c4818185a034000b001001d0401c800010107070000c01001c2125000080d1786200c5030421481801e9440e4010160781c4005040c0c0d003480190f01205c00200c140b06c000e4000184060f20b6607a8104480e2a040103c0e441e40c804555002011750400c034240b408425075411080d0842e040000c900c0100d0240140e001a0402003080c10f8141c45035000d0342c0384140c2002c07ca51744d00c60001c10140c01424203441c88402409040e0032402c841d40005813040c041e04d540020010030796240d4400b11010021110100c40b10b010301880328040300c44074000d454140 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 289003920 1250 289002670 289002683
    0x10e030f010c0f0e090c03100b070f0b1f050603070e0607050601171c030b010e0301050708040c051008040f020604031b051809030d1d0d1119053007 65
    0x207003031020141000e03c2d042200000c0000440040995031980445070750007442c50080640c07251106d840c036511000781904030b898640004a00b0a0a0142490301e4031181c900859031000e0303030784441c0c2d060680b50208050a406840c00000100f0071418103100135540041280b41c0759181001071000030300264001c11069440d03030301500041c82502c640190b480303200302e180b4000b80465000c00c2201d000c84d04805240c1c00615a40b01d1070144681d000f43d01540c00072100600800161402c00c40241045130192800c6e501c640100ba804142d03420b00200780402d8040648441040360791340d40d83c6100010740110100d80080c41840f0000000f0740900c00141403c408120402841781004144000e55804007104520340c03144030144040c4900120481c1d003405520700012a0f40001000044110030802501082605c180310500f1101c591003904010003d480b442030b1240407000b02d10001454852500103041c40d001003410800c65085095043e2001500351405100c40b401c409060496405c0048141d698 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 289005170 1250 289003920 289003931
    0x902070c08070509370603200609030307020603100806161814060c010603050f010207110d05061f1d0f0f010806010501140405031014010807061706010e030f01 70
    0x1100000d01290002c0c110a80e1003a2a500c0e02600f094480030b00220400d444420440d002d9080c060009954400c00c105280c06220155903442d0144820080c81d49402441e5241090b0705514030b1b04d0270465a020344010300840c10001c42c0d13020030040b580060710000c003003040700600182d01d15040c890244501402d4422005101a0041c00707441d0002902c8211107000c840b090600c229008240600700503102a1815070300c81d103451320b1321801006180c002802c14442d1079404003010314150010a075142c403401e200c15030760800303805208c01c40c1c81c0c07040010069003210f0001641c2c00041c1c0f01c030386034620104484210480c1d440290110180e40100302051207000001000345049041115a4001401021040041d8900024280c541c2c80c18003074181001240085001000c9446060f5405004001c2c140c48421a0146031040140f0514100d2890081d444000144011020640720215601600d8111582c04450003040324060014a001d0620a4101c0940b481d52410018040c101c41c0f42400000d8 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 289006420 1250 289005170 289005179
    0x20105040215040503030d020c010f1b020c0102010912030c2102040e160804020f010504030b0c07061b0807050d0e0114100f031106030a0b060a020a03140f070f0c0902070c 75
    0x45070100b2440411036801004100031a450000491344010b8a0410058844000000480c0500510340300c4449150901d040302c401000412030044a1104903000c80e0340443c03518005900b40c03107003000090f26040c00c041001301d000e030194000d40c1506400f0703c3c01300302c0880f80301d0040039203180d114603d4404a07400301d028001d0080348084142c100b080c00c54806065660240001c0c880080180000d0049540c22107054941c0d021b034003900d010755800070840e449442e01c4006040781d5003021106407109420b080c80441000c0240c0089008040300c0c2c0d0f035840700c035528420155030903406032480920b0383d5600c07411004101c00a104541031005001c10300f451034180a000004002e149811032403d280c0300440030000901c0a1280054061068039030949a541d07508001c001860303103140c15900f054001612480b0325901045010703845110382c403051040d41003100b540030075008142401c070100d40f040240f207001c1901c610f4403181c0d03d84140d552a40d5641ca0f20460390580e00701030030840c1c84000e545410701 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 289007670 1250 289006420 289006429
    0x3080c010e0601170a0f11060c0c031203130f2409020102010b04050709050111160e070305130b0a09230304090e010504020108060d050304120803010905070801080709020a021009030201050402 84
    0x1801814900070121600d429800400c3c0c564000084c024086d80101e41c10404000f2089400300314604010308454507242c1d0501c0c1c071034907000c801c0f00c00740c442c1c01054001c604142030a0182c900601d584408052401c8041d5203803081d40031120015a40038110510350b0f00b48251855030400017800403403010484440c4c034400039080d2070603d05018822403c01c800c000b07201c1e61100102048078400d1078030001e83d102c0700c8509070038003100280041c91040251000700342d20301c070305841c14080c881030f907401c11180d030b1240045000d070400840010880c1505102144001d00c3c80e40080740c540e070040c84000d014500c2c000c4401c8040d003466140400303a420104003082400310a01c204500000400020b0086280c1640002c00c1c50100038201849aa0303e000e2050901c80c003001503802801010a844000101d2401c00320f2250b0024810035446d68141000a19080e124012840c100c0c0d05a900800c480390820075514040c0d04240e2510301184101548480841068050641600d00031380000030903040900521 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 289008920 1250 289007670 289007683
    0x41419020907080f0a020a03020708040f031401090c06050d02091009061805090a020f0d020d05041707200d05030d06080106050603010b190302090d060c030c0e090a0506060403080c010e 81
    0x203000e10030341004000110380d000135219400800400e0041e035074800b000c000d030028001e41d40043c1010030f000c01d021541122600b0613000f07490142600b54100c1c0494072007a402e980c0310210051039821120401c2000c00e000d407000c0c0010b031034072078030150410203c0e1001c02d12030161401802c00042c05098100201500310300801c101e0052a1144002d003802d02000c100303520000b61144807600d03030029080d030785200080c00356090030310808410366507104c0489000018103000d4038147d0b80031603003100304629000110b04070b840c050741c0f08030328100781281c880684070301d850803181c031580000ca0a138507540051414801032603109041c050003d000d900b0180030500311a03860300154010241000103002c407100d580240c3d0601c2d0000482c5001884940104030302034018044500d4106800f20103032400c10045400410017514165030401c1900350b48841140c0100d2a840034680204246001c00c00f80c04a039000164081d101400b1a0b1401e80c4d00d0360ba0f6215948142c01e828540e955a40803402251020701c2403 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 289010170 1250 289008920 289008931
    0x80a060b12160e0403110f01051e01050315040501021303060f050106020706050f030703060f03050d12060605040e060f12060f060607030503010b3108060f0c040302090414190209 78
    0x8101d04907280311540a070280b2401040048061500003c0816116420a10040400e2803d94000e01e11a0041902904040e20026400310100342c0300d43e42e480d801005541204d10050003030940488a007001c0d0100c2d04046c005a580307540821550580c40141c40340701000711b120303000c0060300541007034600b01258410b8210100315085103108010081d409816900711040f030300b0285a41e5207a03800141e00400c5164000701d0000d440d00c1000050140100d8410090f03591520740544400352084014200c540c18082c09020034000d00060000c65540c1031141e40c0301c2c1c4040e1403842d070000c4400029101c0d80c180200600540d01c84020051075450700f01d1a035400503029030b4a03600741900742d6030280030360105000d01d18800c10b0201d1107002544224449620103040341c03c000304032514200d0482e40141c40d078041e40344c1a00c50340c008a4211044814030a10034240d468425040c039045a081059041015000ba900019540c070005240f1500340301940d004149a030100b140b0500920600c441900c00512 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 289011420 1250 289010170 289010173
    0x203010c020c0414100312030e06070e01080a0b0312070f0c0f05180705120a090f140705030606030a030e010512010b04030204060b090d1103160f05150403080a18080a060b12 76
    0x500c060b500c20817580c80e05072030740070802e48030a20340d0b240c00320010844c0c00c545001d2485041d050050b0990880c02e0491103c200ba690040c0f26511000c040055800e00d03080750790180d0100440500f080c4100c0701607d206403144140340c07018101c60312a01c03e1a05141c100d112003040383d500030807291401030b00890f503110050f00c51804601d03000c00c0160260107a04021f40180707902c10000340c509a01503110392401070340b1840b185140d29107030822002e81c2004000c8641d1a00c205100032807940340014030144180c900034010721502e1030f00e0780c08450203003800a07203e0600900740305450141e1850008140070700102c440e0280c40740d00e9401000207507445948100318100c020060b80c0c060303440e62008040130a40280340ca00d84030580c0b8001c280b8000c04070170413504010480401043e001c0041e001d071012100304940e24036030f50708210800e030b001c0c0c800c901c0001c0881104005100006000b4001d15007003111340203035004000d82d1001c40500b09013126030111030984d982c50805011340b61401005c0840080c5d0340 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 289012670 1250 289011420 289011461
    0xf2808010305060606161406040c050103140a1a1c1e1a0709090e030309150c0a0e030139140f0c010f1503050705060f090d0f0203010c020c04 62
    0x450b65070f00e804010300380c2d5001e18030004001000c03011043c0b64003041c641c020740b1101c045c44005031550b103545081e1800c4500c54801f9138005002d40c030030300a0081c4848a80c04564440c0ca84075503001c014807400310003000083c03090740715040c5643c5d928486001c16400c2c0c10070050104141c9401d038445040c2d0603d01c280190360898000c0401d0b075002c50004455811021102561180c20064440d54415400703540141e041032614104100e0120146003d0305144c821128000240c14150305041c03c101da05e0141c20078103103c00c128103880307045249401c20303002e400003580b946041c3c008060810301a604081e10501403981102002c444c0003410703080051860303c1c20280c1d2801004490310300c140f40e200d030314448022800d00e40d03291082d88100304449071a0700c08c0000400010840f4080007880c030094801e406960400601818031500301c4049107000422940f03407982150410001e240c2001c4140c0c1e540700b14030718010068400b48548404e10240d80c008103419020b070820403096405105a100c200041e45 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 289013920 1250 289012670 289012673
    0x5030109140106080109020a020109060612020f0303041a031012030302030411030a020a05010c0804120b0615090d0204110c07030818030c03060a0504030c061a0906090702070312050f28080103 84
    0x2130070764103441c168034026981e810200d404034090421090040d0180f490898006058a20402190601751081d01d00c80725880c103220400d43c9900940c440c3c03c0d20f50b840340f030102451000387c030000e60b8000e4074200e00888080c4c6455501c818080351803021404607500009100c00e10802c01c00150035503c040f8000e1a50700c07603070790104800e9002c502c1042c0c18014006030b03400801012409503009000c00c2ca07032910380b0511500f000b1603040f030141c0cbd01502032103030f02d01d20170013052214044a80d26440600001c02500803036082c8001007005101005200c1c80901c144000c190302806410010340c05441c1864607080e884035406041c68a0b07840441c8a44d00c0a440402c641d10085070041c1c2c0000850800102550755040c1981c3c82403c1c00d100929481c506407124815800108904200f00c00a8400040680d104000d20800704009c3c0c4401025912248080000405070407042d1a5844103142c030908090315000c2603450f903044420f600003041c0d000c0580600440c5640900c2041d4001c0d482c144c007035540356 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 289015170 1250 289013920 289013927
    0x150c03090b130321020c010203150405060d0b010b09300c03030c0a060c05090310060305010c050306030316080c01090606080c060a0906050708210601030501230402070204140705030109140106 84
    0x1411011342400102e0341c024040500030354140c4501c4800c8800a40d920700d05050b038001301c81c04441c00148510b20b0a800f01d021420a0454000110390001c0140ca06d0b90030a1862140c580100b070845501656540880240c0c5140c0301c4040c0204154441c081d00d80d800e00e0b9039582c01c100318640c140d80242d00900c00354500f56000507800714110b4004000240c0e080b241c440443d6644500d811035074040c810744141e0458088554003103000c1b2070190700200401c122068044442d44810340307009070300d64020b10a185550003101d60b400c0c03445d4802c00c070081c5408428030500742510340c54141901c1c1c656560404218443d0248808443d10000315042c9103000718103180989009100c3c0954002c01c10003090a104001c4008100c603100d2074400140c101313800c005480010021030481c0d200c0c0c002403c00c000000c0e41c080f08250b4651400e00340145512002865041c44000c6d004141c00340e9001d912041c01224094a0001060241000e41e81d0150341e58103102c42c0c0f509a500381c0114203030340700c141c80c01040b65651 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 289016420 1250 289015170 289015187
    0x6050601080c0d050406060b0304031713031d01120617010509030a05040e10050303030a0b030115050114130506160b0709050f0603280501050415080a030c150c03090b1303 75
    0xc0f400b000007819112070500310001c00136030700403914a0708000140b0040c181c003c14851806840041003402075512a85908034034801114001c000c18000d00002071410482c0d02c0d0031070645c006160003003030b83c208840510292180d60740718513840c0c1e01d1150300403a200c0c001e02440d07a0042e80000250316100f16404004c1452140b403180c41103103248480451140d07800e0741c4403040200b8009044945034140303418018010080900014425840c0038004205407003c03000043c00c80d00d050310790301d04951010801038100ea1025078101d06100c6c41c490042669940c02d405050a484000040007010360249000600c0b1000585401c0921000303e82c20001ca0303945500400d448541501c0c3c0e50313100c0c1c8403000c940c11000440040c0c400c4e0381c4180d00700c02040001e01d43c0709504807003007207505201180c0141c0c100d00840309140101000342e00903100001c080790261a400000c180b10300104020b2540f4510118100d8034210300c41d10001e40c4600310741003070014440d049908401c400f9036044c00520159400380c030150 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 289017670 1250 289016420 289016437
    0xc020f0409020105120a0f060e04030807050a0c02150405010818071a090904030e030d09030c090504050a0210050319140423070f0e01060e031905030702041806050601080c 75
    0x644441c10041164031940584000c3d01c449041342807181807082544002d0f013080c110281e860b6290a60006410422150140c016500b54441a907140c0703900c8021240ca9100c030300c21009005c60f0408600061b16003807050b000800103042d08070b845038204000101107400c003070044071501d1000304e90030002c2c20340400c54504030390030b0100031403c40c41d84120079800c5008c4c94400b640c0c010403c030104800c0c141c00c0744c41c0101e4070f40f003141950080741944006072034211880c00040c1c0440340140c014030001c1e490758000e58110340110202c505424882d40022070280070282c54800194012041c011a9109442d1084508420038814020340140c0d100008141b10024006807443c404254001484000004070090600030002034420380c13500d43d010f404c1e00380028425609455143e000000d0501e1261100c1c2207a240d0040c050b0030b8000c03890a8004282e4198038040c0c035140000c0190000680e00d620400c01d81002100071941a140f950030024221000108214148a6902d042007140c040d00f204840c900c6 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 289018920 1250 289017670 289017679
    0x70503010303121e1e0b01021914070b07080d0b031203241306081605010c080705070b0301141206040201050307140c0a0602072001020a0320060114040c0c020f 70
    0x80c2c3d481e031024400720a01d154011052840d052002505031500c61307034011045c01d02c000070302001c02ca0000483c1d40d4685025040d014400d421113200000e501e483e07041040100390701c101d5000075140e10850050394021142207503c1d40380080c10110100081c040c10074002004c501619000300344400c00d02281c80300901001c0300300e4984070038008401034601c41401218020303204601010740c400d0010000c00c0940505030ba24402c0000c0c800000141c2ca082c1c02c11303524181c1d41e05000340c00c00d40d9010007030b0708003040803a40c0d40200d00c0041103620b030340c201560080c000c00c42c085202100c8a400d118418204614850403504144104800740c0d130810b0449400044501c0d000e00303000d502d00c00051483c01003040751043c0303025440b40346090150130780184c8010707402440c52500c45461021003455402090706401e002d40c02042110740401d008181c0d000c40c0313440c0b51701c80301403411131480483d0070000300340c01030720001e00d0005155a15090501c03c01d04012800e0400700c03003894a50700040c1070000c3e01400702e44a03 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 289020170 1250 289018920 289018931
    0x318100f0212100317281d0411180d050604050d110609060c0901030f14040303060e0f0604021c1d0f0106050f102303060310090807060b03190b04060507050301030312 73
    0xd0f1503059106c0041c014007114024403084005001009040c0e10b188641c1e040903014100d190500d4640725649240c6100d4000c14502100c0c1242d21b4800c03000e000e18030f94041180030640000c01d20a10540380b05030700c00d9010f090443c140e078801920900c1448001807240e0710400030400754200004019401c144500c0a480e1a12100760040b405456201c1820000d00d00309050303540071b2140230843d2406075100780c409120240d100e1282d503a802c05e003106d905845402c0b5002041c42c50500303500501240740101d550200d40e945c50350541c025174400c100c850610a0882010b1100e281e814401d00c4440754010340240000f9241000207510001c4044a4070f00c640c02841401801601840c040782e6102c0d110740324075560030221100e12141d5042210410700a004400026a0f0381e0301c940f084041890703210041500b0b04110b521000010700c0c0007280c9682520070801c00c0607400321710511207008148251202d0b00107207032902e03000007964000350665051002c10710050001980002c2e805881c811400000034a = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 289021420 1250 289020170 289020187
    0x50a0e09041b03031706010219030309022418030304050d0201140706060f03030f080c030a1503020a080d031508030a080a0b0405010f030212070b0318100f0212100317 73
    0x1144112620040340c0b000c44141c00400c25400410304500c20070b1603c041c0c202035a4080069840700220780741160f206114000601c0040d000351b0140301040e00140c00d14054541200c140000d004171009450b20500c00859120000131820710100c00850043d400355051929040114940340b81d440790090500101742600c00f0444046400d8405494004206012071640d899400615006901064002900000400c2442c60080d810140a0180400541d103075507240341380200100b00c84428a0710325500b59400001580d55079000c000541031043c00b41199000003200a011600341520003d484402034030304000054011003582c0b0f44151f9401c000401d556040704460007005180700080d8498034000010401800001014080d03074804d550702070040101401040c0d442240e80b064280c09203040000810003921240c1e00c00c508405001100c105140340d400c3d43d01034419030407010040680c04202c10107444481240290401569114209503904580311864420003202d00f11002020001d00702d80d = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 289022670 1250 289021420 289021433
    0x614010e01181203081e0703110909071d0315060d05190506011505030f06040f02040503060a0b04060608011a03220507061e170405010b1f0f050a0e0904 67
    0x1429400040b106040365445840140781492051010f40000740d801e00022040d00f0000f01e0421039a4084c811043c00d5503031784004501810310070f1054001c4001c140803a42c15134495400d9580215a0780d16900a48000c581103980015541005c06200798410403440703000d5a04032030030030381003801030310040c4980f006810114607140032030f500e410500042100301001d004002c500581654003448120308031990b1500c00311894041038954180108407100820010b2800f60300c840c0c80b1403104007025080590300c00020f8240031048592820150300e5181d90700d95460b09110b184080d14003820b0400c120350500e40342c400c0010040406901c19a400004110404040d0714081c0b46d95644440c0459000100d107482501d80b0707220300c112030100300228210821094a000982181c00c055034a1000003285440355001d07146016206582d1550b80340303580741719a100d4402c1c1c0b5014445604941c2c40220b0201c0e0014030121031760042c841000010b021480701154820305543d02d172001142c140e40700d80c5403030624a = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 289023920 1250 289022670 289022687
    0x160504020f040e18150f0f040302010e010f020c070e04080f0706110301060509030d020f0c061806160c09090c0b03060112021903061203021c0e18090c01030614010e01 73
    0x3c28003103040d9041040591444040b1203409030010107989000c050905d0011002c04180c690304482c1d101c110005005040b01c01425610900a200108000d946c0e01240c1d0708644214208511407a0001207442e08040200035400050680800100d064a49074544e00c000e4001c0d112034885602c1c0014006040c0f0010b50404c2440c1404064180c2c1e030703541e45150103401c80c0e104145050190203034000103030720300d40042140e00e5a0607590018100124900082000651025081005480400e0010b403c40d44412000d071602d0132651800000319603035810102c00c2d5484640c05024480e041000b50030014400352050000c642e8882c015070380386d8440f10010b9030742010209880341094400f2a00c5c0d034501001c44002c0c0d00c285815101003114540301c442c54254110f2426000e40541d000403206820052403171488100e002e00d82c0b500e510081c3e540000140140301d5a100294103114400601203521020f018601c0d281d142400d041001620301020345103543c00d600c2c865810b000c0441e02c030480690040524 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 289025170 1250 289023920 289023929
    0x1080c0415030b090a050907051203120708040209010e01050f1320031008060c07030e0d08190806041e02090102030d09080d0c0215041b030b0f0f09160504020f04 71
    0x4001400316181d500800928985032414030030749200c40412450f010718401e40b4020182c03070000c3e08041d4109003c0c0000104420b0920701d2038441049040c22180c01ea409182c0515038503a91501d8508280c010007010b0581a000600c1c500c804130300400003079807840f100b106951416110420110121b0007110010558074001584902c005200b8075400d003084030046100345c005030a103442082e190402c036665140c0885804518250411031003001c00d000300c20381081a107000300250020080c0b50740308200c3c1c3d003084250303400010f10440803030444e0790410041584041c041d02c0c100104101c4032501032050b05680001500c1a60000d00d812003640300b441224031101c941b02c02440a00124a441855035101c1c01e01b90343e85603d0103084160081c40412182c1d0b82400c612002001626641c032540d120428032503045c10b180184010010020b07011100c528421100044161014540214401c24080c002401c40c07882d81c001980c0d46000b02c204440000640b0381c01e81d0b00584a10f411400c0851a1055810 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 289026420 1250 289025170 289025189
    0x30706020d20010e070501020111040b03041709030f030304440409061d0c03010b031504060e04050f43030c030f11090f0705072414090a0302070501080c04 68
    0x91407031020900003405c4048907400c1e8020420070845a95081c141c0c004da0040382504c010400105000c81c4a100e0025101c4c0030400619207016066070020f03142603854140541030750008001c0100b8441c502a030880c0440381180ca040d0060301900f014400001050588030f00080070701040d00c1400c0e00c05050b10f0140c10591400c0104540f00c0d442c401114509501d0701e85060405070008042900344410749048980c01500c10381161030b06c10719a1120707410000150b400540c0c40d20001417046860358410f00460203507015003010510080c059050200b10102d166100f0f14200c1d40402592414240d010008540d048103224140c40325003040c8412a90303400500200280300c0040180100c25581046d418418003c2c07000d5040c01c8070601c01d50803012150b82e100402640000f90a05018600801c14035204505440e400701d80194503464032802003d1035040300340c0d211032a00000c0380013041d85400004850081c280300c4201e9500039900c240d1400b0f20780c10804814085079044103104140d8000d01500d02 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 289027670 1250 289026420 289026431
    0xc09061c0618291507050601030b060f01090806060112060509070203030f1006020304030201142b06060e060313150608010209011416020405061c20030706020d2001 72
    0x10740d0000106440c401001405140025841003026001542e103d0030000c034103900c88020441d002c20585200140482021801c200092400501e081c018680618484c140611540c140f0344188001000303807068643c103006403000144240c41d4005149a440f8500746000000e14007002407480103041950f20454001c034907002070103401a0040b01641c4158807402c210f0203950b44866280700c0340c104a218180260304104000d001552280010031180c00510040c5031826a00305074801800a01800310314030168260648070303c802d020300580004007043d1400c00c82814201700051514030010f04403241050980240d001004840000740c0100a1404002c11800b642c4100e40da0103940450121070001d4408140c0c0c1c61100080c40580f902001d07580850b5603100781c26803e02008000c0034112a90000030541c032600c04240c0820045101442034214507601241010a440d11140504441d442504003403018400716600250b10080d449481c80c001414180112000c0b00111480b9210a915401e06 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 289028776 1106 289027670 289027679
    0x408102a0f0512040f052e05040309051c0b10061d01030b06070807060f02040e24060c160503010e0309010e0604150c06140c09061c06 59
    0x50801e00c0c03400050706070000141504440480d03031070480e032801c5c200300a4248100014a100881401c003070b0341c040881c8104a407003002101c0050b139542d00000f024503120300030880041074080c0020401c01045229410440e480c1e8006540a10704040420307160611406110211102559400c1c45140b01c0300b0012000c0070321842e85030415032170350104061562144000d00b6483e2092a034103549003910301d0481c09844605e0110384000348103100c10412440100e0391558060300207140f4500c03000f02224002404ea0f03081d00e16039000030010500c00501340001405110074030340f4014040c2140e6071a42010301f660700d41e003000c1511360024054040954015400d245d03490400801d51804c05071580380d00031144a4490780360b000162244072a170284482841142c0f900308120700c0701001d0b0b00d808200c140040c420380c0b145c103004c3c200004145189100610328005500c0142d03009104e4039585 = true := by decide +kernel

theorem cover : BRFrame.Cov 288848920 289028776 := by
  have h0 := BRFrame.cov_init 288848920
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288848920 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288848920 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288848920 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288848920 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288848920 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288848920 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288848920 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288848920 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288848920 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288848920 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288848920 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288848920 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288848920 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288848920 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288848920 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288848920 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288848920 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288848920 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288848920 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288848920 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288848920 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288848920 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288848920 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288848920 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288848920 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288848920 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288848920 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288848920 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288848920 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288848920 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288848920 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288848920 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288848920 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288848920 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288848920 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288848920 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288848920 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288848920 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288848920 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288848920 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288848920 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288848920 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288848920 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288848920 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288848920 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288848920 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288848920 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288848920 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288848920 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288848920 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288848920 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288848920 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288848920 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288848920 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288848920 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288848920 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288848920 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288848920 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288848920 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288848920 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288848920 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288848920 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288848920 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288848920 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288848920 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288848920 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288848920 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288848920 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288848920 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288848920 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288848920 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288848920 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288848920 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288848920 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288848920 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288848920 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288848920 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288848920 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288848920 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288848920 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288848920 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288848920 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288848920 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288848920 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288848920 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288848920 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288848920 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288848920 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288848920 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288848920 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288848920 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288848920 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288848920 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288848920 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288848920 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288848920 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288848920 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288848920 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288848920 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288848920 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288848920 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288848920 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288848920 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288848920 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288848920 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288848920 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288848920 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288848920 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288848920 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288848920 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288848920 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288848920 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288848920 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288848920 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288848920 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288848920 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288848920 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288848920 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288848920 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288848920 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288848920 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288848920 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288848920 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288848920 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288848920 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288848920 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288848920 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288848920 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288848920 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288848920 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288848920 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288848920 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288848920 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288848920 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288848920 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288848920 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288848920 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288848920 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288848920 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288848920 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288848920 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288848920 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288848920 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288848920 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 288848920 ≤ n) (h2 : n < 289028776) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
