-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3284
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T09:12:50.268284+00:00
-- url     : https://prove2.me/submissions/056b273c-6d18-488c-ad52-0525e37f2b78

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 590467625 ≤ n < 590647482 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 590468875 1250 590467625 590467639
    0x90809060307032a0201060801020a0207050d030201140a06140f033004030b041b0510080405010b04060801050a0c0c050d1103040806010303020106092703211a0312040f05 75
    0x2c0700c2e002c90280c0b042e08a4000e60200c83d2400342490030740c0003540800301c07209400a0008664402d40d9500700d01c80c1c1e144941c0103801141040c001c0307207413410640407924020310000c2200b00c03940c0c01090308802c013501d040201c659949020409062100740344a0019001ca4058000e90b2180010a8848211030300458100c11207911507500c01d110f10324080315490821070a291116101d281503020700302c0544041d181810b00c1144c0d101d05001c400340c1681905e20141040d2681508210b05543c441e002600c211155501d843c040e09464076036124001c01071000100104181c244022440100c9136490215420400c491091801040c1c0c0059800c10344100e6161222224015000c081e0540c0115000702d50f0340e008140000040c16415000a82511640a8200448008864100f404188071030035500d008030f09400c0cc60110340260508002c1c2000d00b40b280b030505403c0d0900c0401c540052142900d902d03000038142c400350804000e10340c80404c49030301d920b00e0705003001d81c0c0203039040303491242030b1150380 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 590470125 1250 590468875 590468881
    0xe0f10091a0105360102070e13020409060b09090c090105180402120109120903061404020117070e0402210c070f0b130c080d02060a060b04060509030a050d090906090908090603 77
    0x3c40010181320703000b080c0c01007004248560f584181440c00a0003864014030403203101180d0022200c00c11401a02e1641c02a07401c050140e09100141050050942d0800c3d5540036801c02c580765040154800d540303c601800000880d90b040180051040e081070313001d2400024004056110301c16801e40194044400c5e08065000a4070540988580e1900524070710340c0e181d070000d515070400541000d991044400380400b4a804845c01940082214083e0002d440e03c04048140c03032082a00e15001400b602d41601c01400c11008102070b81d02800e0b4402c10041440f04000340c01403038130328080d084200200304c50b282583c0b030740b6290240700300c2c000050052412100452003034003082c125610f44a500000c240001a0b032282156109d880038800840580507010005440603100c0c0700700e506503100002d0791400c0c1420208221855000b10641c9600f6109480000d80890b004020003e4024401e9845952240c200001001034030401e034000002d10381070450400000b806102584c03803986090396515280c0e0303 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 590471375 1250 590470125 590470147
    0xa05070f05160e100815070e010207030503040f08150c0f0f040e0c03151206070f090f03050105060a0803070b0c070f0212011b0e03060609100e0f10091a0105 69
    0x68021800014010801100000e0f001a025082032140e000d9540364841540d41d008000d03150b0780520000402c4060308400161a103010300d82c0c50809481c10b10445403210380ba581c80503d9940150440c0c00416109201046104010407001d00c0d40004a1071761003803400e024150f550b0070701800486d09240700010400094010300f04081c2c8005010130084203045003401e207000960ba50058401810600f1031030f060a000703007815003c5070b28031408080240499514444201c86810025620381c0030030110680000390502c0034100307000030f035026000001da01d0407d0410401d00c07400c9540440403607042404820042583c1c3e0748416403015914819030360b1100c0502d0b21402c54484860000e50117640e4140658100d4415800030084c50078a0a100c0d0f02c0740c0080105a500300740102845034150312240c0080d10f14200490b159401c03840540d201c82440380c82d0403e03c040d04800303c540d55059072040e41000700080702e800d5680003c0c42c130900104509000e40701200b0501001002c0c80381400300c00a1501804 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 590472625 1250 590471375 590471383
    0x90313062604050f0d0905040c03090c03060c0e0d060609141003081803030a021b0f1c08090303041203090f0e070f021c03090b0a11121306090f05060c0a05070f05 71
    0x260a1300d02a104000e0100318040c203145824060071f40218030b4180d5404040c4c0c045d00c641210b0300c0c1c120103d0b0000b1461a56041d01901002c141c0d03000304800ca48805540780c80c0c249413074815508c41c039000b240341801c00f01d110b412a11002c0c1d0b2882c2d10100742d000c0c015038070b815100810070380b41c0002d20680d40300c0d028049014285142c1004542610002034011203c0e40d010400c0d039800840b00d0b4140140c80c903014104090346103003050319644440904061120740b694203042c24440c501c12485681881c240000003802c5130402c0d800b4003080c0941101c1d034400c0607888003646001e000d1152100c0441400c0c19a221000b440090050040c04800d04a0b0724000d4020415401d844030101c480c40c6001c03884500043c0981030489003103841d80890004144003030f415000c0c41ca032114880300320030f0600a4000c40d100e803040c00a071543c40303600010480c00020030018050120801e0149506401801d09441c00c83d140c04002000c402000405001c040d850303aa0200848445030740150300d00504011070705100d420 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 590473875 1250 590472625 590472643
    0x8040609030903080723030426070e010816062606010e03010204180506030c0d02060a0e180f09070e01050d020303220518010305030702041a040509031306260405 71
    0xf100300d000c91054101b0501001c10720388403580c00301405015003010b009039501d006034040d6013010718980c164203011b250140a8074080e16610b00031624566074070f825464922101b80c02c00c0032640c1010964514038040c100072480200460301d8104810b00141103100380794289502e0080c0311000101c08203c640c0e01c034296454031032100030021507031140d4810403280c4101a07000d00139031081c1800001034082c038000c280d00071060b9002c0c0c4003210b6046d0030780c03c114172644042c5015050002c035201256541d2204005404d10a13200c14940c1094140078021100344074000b845c800c40703035014101c248140d0f03406000182c11134009179892a4041113500c002410750081015510345904042d000311440080c0d40d40c6c180885009840f010491104860b66120b4903a00b408041c080303500400400c801802d0990202520804801d4074450340036024000405480c82940c98002d80ea00105004643c0c8107007045100c000c00d1f041c00d0841c40c20a0081050100300040030301c402004000b4000503080c02414400605 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 590475125 1250 590473875 590473883
    0x9110c010f0501050f0102030708040b0f040306020c07050112021303080f0d1802010f110309010c0f0b040b2422182a081b19090207060f02090108040609030903 70
    0x8244407031040100c00815003403194610400030b8420518aa50010003159085600302502518013410705401c00c116600000c40c9103010f00381008004045115031000d003841842d52005041d800340b4010004000c0c0c0803c4484e0480340744104002104405800101300440b40d0003107165440c2c0210075201005405a4103000019605280540c000c203070301202c8528610b4800d0300c0c3ca40007402040c0c82241c110b94010308034042c652007040342102941c02604141e040318442d0030501039050203030f5038042c81100250b40885184120f4414800d4010b441007503242440610304054403040c1c102e0001803850240119114a403004000580c41522116089081031250181a548920310207103030480a507200b81d08104091103600710302080040000f0007810464100100526000a4035464601c051030340940855200701c6c44801070004c4100b0340345001c0200000d00703005889901c18285542520801184c80400501c1044422210780c0c200c00c0c495001a017014000405401518040d1200d11850700064 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 590476375 1250 590475125 590475131
    0x612090304090e07081c020d0c290a0c140a0c0f0206031303030c050a0e090603071701060501031503020a1a1312140106270b060d0b030d05120109110c01 67
    0x80f0000a0001d4400e0485006204030b6280c4040d80301e101d82c64451625200d80140c00c145082400c0a100c0d10f20002245e00031414000d180082103104c5078140c5403010601e5404107100100080c0561900c20449201101e00341040029000702145203c0d00c160071140060010520000c81448440481c0b002a9580506416545c0c24010035140f01202c078400304178000ba00300141000c00d54441c4007610a40c42507a02c0343e5041e484d0304030402401200050440b500b6102c1c0400008220f01e105c80c0ca0b03000812030340c00009069081c14001016507510b80842e141c0341119000400050701c6594910b0202c410345104609007482c2000002114410284000c210258865020860104501c500320080b440343c0014209801481425403d80305203114040518071103000c05050321020001e0a41c0348280540700064821000c00000c0858016550701c00e03045030385100307144c0241000c1006402510b514203080e810032041c04101c5890080c140504032029444545039079150310400c0c29200c1c0d050b040f000074 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 590477625 1250 590476375 590476391
    0xc0705040c0c0209010b0405031b01120c08070f080f07271e090905060c09040b0a080a06061d070f120f0509061003030206060d020109050d030c20061209030409 70
    0x2415002e0b020070030f912070074503000006003080305402214100c80028015040201829040050f00c44c4c40040460511030508221007061f1014818000304a24a80716500350381000070000380780c9203a018808090040c4103007880882d840f065410350b0311140c00c2c0741c02c0c040c0c400c4d62007030b414190042d4a00d00c032020b00402d60102d0000c03104141c50201c841c44000301100107540304140420f61303a414801800580240e00803d00101c1400020191403501600100c0c80c1020100410240c10340c5a1050b007841d0000e0f8103000c1041210300a0b031004001340040c1080380f54440c82e00e0529180042c20840511440e14060a00180244c041e15120006403800704017401200114038007030007040343d49403528001c00c80061150038070401800140c1e034050340108801c3d5200e5060015607100c006090303041c4041c3c0c40340010981c3c2d420301425012032083c6d651f10140740b2289441d01210425000c1028040407000101c0c020b521954155a20000b50004e40912510b40301c0300a4190700c02d43c2c2119041c43c0c100347d40 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 590478875 1250 590477625 590477627
    0xb150d050d0e0310020708031512150105031c141c050a021c06140906060d02070f11180703020310090c03020c060109060f0308132408090d080c0c0705040c 68
    0xc007419102c00d500340c4842c098180189001c0b4850b0400c0106a05004e1022412209451881440c0c0c9123001e00030356010040803050f41e191034981d101901419070304030010b00c01e84c1420b000400c8401c400b801203149003103050300701802c50608030060000034180818226082c00c040386585a0f06076105100704140d060040c0c401c00a5803000300b07083e03201130348030306920110110741c4031710400c0311010402e080440203030400f0040140005084a1b500200078054860749010900c01800c505114051590135121540390203040144402c025510804160100060051a154200c0d40c0054035117401656030b82d1781c1c02c241c030030700c00103800c6a84d0551070040074101e07032500b50780200124414681190724507039950b003140c07058a40ca8000c100142c94504170800010300030b04081c004220403c1010f40081d5200d003a9030300c0301300921941901d510b002c0d1101ba20b0158006800c5904114a0700207080b6800409030b02074070f028030107880b04030a4100000c403140510001e0000e00047c01c40280103002c040b400b00300c = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 590480125 1250 590478875 590478887
    0x1504030c11090c030601110709050c040f0801050f0a0b010c1a0106141303121211030a0b010e01020a11030106050d12020f06040c060e04140f011404090b150d050d 71
    0x50112681c40400806240c0c0b4603003040124850314010007040e2655032008011514480b0044001f1070361b00ca003000220340d07120315000b880d10902c1d109084a40311031400108180c0d04030a90300c40761003640342c4014496841001c1041d940d0003020350b41d01107400c2c0c42d1880100c680c100d4040001d070000d002c1500b42401400d000c4c007200c0c101d03102655010a030402445803a41306200d441d203040c0c040c1608030000c00005400c0607603001d03110a2030030540c42c0a1954542c1d003003507500c107100c00c84c0310820000030400154002c2c440d5040181c4217203445506185190b00107590f800c4201c1e40a4201201c81d1070703403042d60350250008409000d0160a1800d661110316205460400b003002e86030148c0540c03a0208400400012041d104541180d101403465103801d605270f80d01881c42001941003031303c401c070718183c0740c07104249180210182c51141c0001d40c903240a001008004848140c070450401c0f41c0200400c102d01c84458000c1611041e440e65202e000000403542044150004c086004170a900b14640d43c10034 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 590481375 1250 590480125 590480147
    0x9090f1208061201020430140d0f0914090402130f050a0605030604021c030318080d050708131e1a040c06020303011212090f15030f0209180405150403 66
    0x80c44250101280e683c1c05070903030150b80a000c1d003554080080b100105c83c5008400f6488000c24030300e005020464132030364141c4e4100443d4107501e40c80340940381d8030260301c20b140300c481c034400b031515143c4070b403e142618410740d81c2d09500d60f00c5103a400c0041429952500518002c0c1844d80008000c0ba5046000d000054481100d0900e4507501d400c10005003800c0228400344280ea00034828036441c1060b1140f00c050b03100041080d020035584140081d10202012610504903006641c100d444182c81044401910b90040800003004841402c0c0070a00c0c0113910074a03e007942c0815000090024100007a000030300300c106c042d004c03121501c0c0c028681d031001ea0f42e480c0124000c2d01500d05182c1c0f00c071030036640e1b440203205030300c0071740d40f0054000c001c541a907900039058070480c40d1040216513151044000b82c00c094100d12007881d03075640da0801554040c410445600303003660040d400c10074620300140c0c030080e05402124650126000080401030207110603030300c3d00900300c0100e0940c02c103403e0040c40d00d6005 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 590482625 1250 590481375 590481379
    0x12020d06030b1f050108180a08040806090d05030105220f020915190302160210031a190b0307020a1a07080a050603060a1a030a110a15050409090f120806 67
    0xe0020518020b5100109643c0905101581040d60b241500440314084000c103001611415218640700382241400710b024610702590100c0d4407681840e48207420b0841c05815a840d5902600c940000150041e0030340741140d0080780c5e0000103140791a44211114013035208404464581540158080e540380e000d804039040c141c0e220203600e074480c40780130f9445c4548504045060703022035a1140076031203030f0010022240380003010b002e0302915030b0120b80500a86d54010010079112208004040c000207002d4140060440e070300c0381e00a42d6011161003078115401240c282c480b00200090125000304103200304181c1c0416038181000b1100290310030000d054500030000b070007200211344880c1190103654010380001300506a907440391030110005142a40485910010394454100d0954041c041c4030001401030843c00c4400d020002005080401c0d904000311076400404d60045a6034404103440a0711000100054444c04904000990540d480c0e0300400080001c98003500705035202c0d060360f00505003 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 590483875 1250 590482625 590482643
    0x20d0606090e04200306090c100306030c0306050a0e0303100302030c270406061706090601060f0c0605150d03050702030d1e03110c030a0c05060c07031d0112020d0603 73
    0x3110011601e4600390b00c203000c82600c10102080100b155500d8402c400c0b81e4101c1c2d2924400c01020210303041400c200d035040076641096102e441642414549403103020312034541000141e0075666a0140c0301807074000a00441c1d5504000348400a0f150b001c040307050904811640c0302e281c032001d0040b034010b080c00124024043c000448200e0b0400e002010070205901c00001d84940b03850804238881d500040c029110310741c6800c40013a04002241c0d0300f01c0340071041e0001d071400346882076000b8901681a44448100321007922034141c49a0f0010202c0011a406500406c141d220f84880c140c10b80d200785004d03039200e4040c00050040640000003003c5203442a4107496050440703203001e03100f0300002426010891a9071404c4000d5074842d900512261080c6c1e0101c904000300c42c900b0900d1b40e04000c8001001c5459100e848003480400c01c07540d64000c40a80d0f181b03140190603600109a041d80002c02c1c1800300c082402d0740b44d40d038080d50141c0b4007401031103411911081c201440307401800640c401540e40c84c00d = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 590485125 1250 590483875 590483879
    0x3200a1b060e0901050d150f020903070807150518060a050c0f01051b07021507050a0507090b0f01080903280f031a010f18092306030c0f130e01020d06 66
    0x3020348040141d02d48024030b5419640e113080107103d0b814440040840c0c1c0e07400107007880c11440f40b1901c41c1d400c030034501010041c2c58855820a144c9407181e290400e140760307809000c040007942c0c1e00000c505440340061501e952111040410030803030003c4101201c2d44014041820384106a002c000340c41034501050482d4000751140c40013500700c0350280c882905e407035000201f0b01124112503004000580c03004c0c04424070319100034103031020b940218404a0300340d00300070100c4080c042c013088034034042c1c500b00701c00b0080c824800002400e4103103c1c01c802d5042c886850001001d2400c14170a40e111450850542d098486810a031452401480400d03800841c0d070480d40858628468032038015448900c869210022009000550311a124628404d0820100142441c9014101d10500700141a4640041a188207a0030000c0601d242036001c400301200754805c001c650354001501454541003a2485030501c0c08140100d000180f02880c40040117041a41034411041c0540c0149071a845454007002025 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 590486375 1250 590485125 590485127
    0x2030106050d05240907141c0605030304060516020a030f06050405010c0c08120903070f0b0601170c03040201030b031c0c1103070303092d09050612070b0703200a1b06 73
    0x102ea41d0500d824071131040000c41e860516444154115015040c1842c94443d20740341200d060b80001840c0440901c5100014402c035000d002d40c40240c1811406907091905080004005014036040d17090025180b401c01401d41d01e4041d000005150007680c581c4100c891805c181025240941e011035196281c01e80814043c0e11a560303414540b54402019460111031182144e038541000d0300410050004104140000e100700c00d4403490940306501001c05454100c001505010382d00d0400e80301010482c0800c9026654081129030280e07090900284401c045d101107450a400f00301c0025100d40c10450041e00590014895211548035001000e20380b480e01302070517100c03070080c80018042a04107005100f0007030b28030010b595520520361307c0d0048003400d80c0c10329a5510294046415155500f0a1004906082050034007041e41c3c1c00017001d0f005c1c038043d12082c00780310300c2c40c01a080199400c241c0b01000400140c100c0445808004c030781c901034050910703051565141d5000f1a0302c03e604100001e80d2 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 590487625 1250 590486375 590486401
    0xd0209090f061c0c1e0f05060307200a0219090605040207020d17070506010303031b0f0801061404150306061d03061314060f160216050f1302030106050d05 68
    0x1110043c200601e080d825881c0c422070700d10100d41c115030401243d030000c50200d209148100382003880f951502109071130b00038249040665900280d008480420400440e66080010307010300c07031205402c000d4401c0061410b01d08240c525035000390300c40070180750605041018400f50302959034030441000132a0303840040108a105804001350003903801c8a44101040803074400450b0400b83c101c0d854613001c200c0d5140c50030712a00740c0048000c03e907141d601d04840039009620312000d58041c14a08843c80341204050a03c1005118084c00c014250300341d000082d440c0c000b41e400034062032030000d8008808440250203041c940c0200c100154017400305e8007000006400303000643c0c40240240c4540c2c1c07110185e581094109500a40c0c8024602c00f000358001c000704455841810100d10400c2d4a0400c1c00e0645880c4080d10150710841d8013020310003a1031400c00340704800b280e07012509140210106c0300400c0f1900c40c0040b03185036043c404000050b50503007041c01400030002c9500100301035681c0080c48801 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 590488875 1250 590487625 590487631
    0x405060f04050403020703060903050d0b0904051b01020a05010e150f04080906210a0e190305041412100906060f21030201020c07030309080d02060105030604150f020d0209090f 77
    0x4002000001036025081692080c0c1c1c0182c003a1056400e07154491301c541c0c09403441114101d0002e031001440d040340354194407441104540881d0070704940d0405845441d99650100000c070841000c81030304600c182e008110a102e920707440340080c445291100140d5444200a02c208400c41340b04500042245403031004a070301c241c0c0d00c01c42150038592003c061015907000b80014110140321041905c010349100d403000741c0308d1105403001040c68081c0640b424140040000c4102c2400286100100025007103005d031000e0303c86400760107080c0c5140e440000c200c10501d986500040c000e1058004a801152308818501c40c090b0b941881600c1da926026458040a4411541c00b54102800c5811f0342d42c2c07040400400d103001e4800076041500b0008400c1c107000c140d81c011008502c007010704002420060040d410004903500281c205076141201280d2102c01c01040100401d1000602c0407140c0c0f5640e001500c504441c0000311f44901824030054000c1d48801c0c40148521580c00c00683c0f820702510000344 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 590490125 1250 590488875 590488879
    0x120c0706020f1002030a060f14010f1b020913020a06050a080c040506120402040b100203090306160f0f0513090902040e06090c0111070e070201050f09160315020d060f050f040506 78
    0x186100c1c0300d20703c02e0700030b40001c0d168003001ca0304c3c2c1d5070025249508892501c050110000824419560307580098400707030981c107030b20b014028942d503403203558070108680c2807100c1e4044d24103075020b0781ca0301207200002c104408002d511032040b1201249041e07005000c0e0510380102d88034034005440c0c0d404840d1150195106069100e641001070f140c41c122034484840c0c10501c060030209034850403900061090171140211001640007192010380340c0f80402c5034a40104850781d02c0118007403035100007000320b00081c02013020700ca0000400c1541038403a004a80364a00b0038249101300c681c84001e00e84c060304d889034050384103904110340c92807071500100d00940907c004500510418041200655040040300000c1070180540180002c860780640c801902c00c00890740000348518200d4100d83c4002009010105c0d10342c840c4802014040c5540d51210030ba9800010302c005050789000584042d218552426a030395082590000300b040c044100c0c081510f8041359941c101c01104003c0c40200c68084442a0b = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 590491375 1250 590490125 590490133
    0x9032303030a0b0102030c0f010b210601050f0612011d06030d090608090a0818011709030a030914010c020a0302060702010c090308090d1a0a110f1b0c03120c0706020f 73
    0x80303403015140c0c003403482c1d043c045c01601c2c1412041c180f03081c1041d0742c24414094994441c0c1081d00a880c01950b07610200001510892808a1070f228440e0369000c140074250040e8070310503101d80a540da5809881408800c081540e10300d41c0c6810b58140c01000b140e4890ba0b4010b03504011920038580441c005c1c1d4450361964440e02014039140b000c84140c2c00103498810300307000d030407416000329650303200504c201c1d03038920101c0700b080703a5136000144540101010102c070480742c24240001d20b01d01000f15454100540b502103226500d50501c44000040415661150b600c0d2072454504160046002040da500a8099a400341d0704c050042e0b09031020440400000340c0481002c1c800101e51070007402e034049003e088400103c0c1e240d981ca4142c2c4102c000c451190160b42010803001348040d01440c811a426002e0041c18081002d90842180c010700c83c0c10215811a04000f81c81c590301041040c0d407005000b011038085041180926120350b111180c4c5980c0ba01600401141d546d0000071740d40c100303142e000018 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 590492625 1250 590491375 590491381
    0x70b0c030909100f08030309070906030206040b09011209030305061008011d040804090c08090118170912010f020c01060509150607031e09090b0d1104021b010207030903230303 77
    0x441e1050041650b080308600c1c00d40030621030003201c42c01c0007400e000c40085652341004050300e40b030412140d03c00b00314181002020300050303c810f070644046842d42c130303011521038403801c0c0181c5061005c1e0120481091074030847c00c0a25070b0580101c3d000d00b00c2544c460010070b45011040700e0850003401117403c075135804d2504588440b5401c18140c2e02a0149440d1810030740c550f070070700040c4ca0759404c00c41c1c00a08002e042c01503854080c841d0003981d0f428200e005908500f181e544c0310440c440c40c61802003054000c6503138011a10303005550448a94a800204845c1e140702c05404007e41109505150541c40c4c1000802c40c1e040005106000d02e02460b40c040b11000302c002001026131010004404000f10402071a0a0010a28000340da8075042d440710b54480c4d05000012040314804950140300b0820450300c0700c0030500741d6255100350b400550300581d884408001d60b4544242c0c3d594800030642c4002400e80505611282d20016a44903801d10750207601000c00c26141c075410300f80c0d00c0c02d0301c0d0020004 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 590493875 1250 590492625 590492629
    0x9032a04090c060c06090c0e01050306090303160503092b18080a020d030c05010c0c02011e08070f0903020604030606030b0c0f1206180f01031e1a3303070b0c0309 71
    0x344c07010980b01c0c24010407107540395655020f84c0340703407940165058400900180720742e01c0c00707124017944017410000550440ca0041038078008203102e400180103011000012400f82d040074041d00580c0c0e006105d914450020403034584000790700700c408020008010342e20382c1c00e41e0006200c0c0801143d5105c00200503e082940070400d010111900840602c60b88601c1c40000031801c2c02045001c400a480c3c480c0684403500016180c80c021224005018082c450030441e11380d00220000d41101c024640090213056411081c0c80d00030782a0006544400d000c00c00008200311a00300390241c0344503001c151a503445109000040740104c120101c0c40c7e500900078a68002a00c18015500810080c210820020f03500e44881c200ca90545215403130386828401403050180c0c005141080046140c01180301e010680c560354803504c1d5078100b4492400c24070000c00c501c0b13407044a48200000504912004580e001c004000ca5043c00c854441d003c9e0041c12400140c442400c401da9000090b640701461600c150101 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 590495125 1250 590493875 590493887
    0xa1d06030c060a12021b0d08090c0406061e121104091505030a0f050717060a0c02060c1c020d1b02060c0301050d0f02010210020f04080105100501020d050d0209032a04090c06 76
    0x184461000b151550700508583c0c10802d04903050822344905c2280e040c1440c0f42e03418828204c03910342c06141440c0080040030b500540c283c0740306d42c49030344071140d0064200c411610100100e0352a42001d0070300c0b201c4101281060018011a0900c40080022420110441c10090140d104065064018001c90000700d5205c05009050038841d001340c50302d03140c07281500180b501d854140884194007410800018403070307600c01c241034600640000c01d0145005001e0001d40c1c4500f0401e5032046a5040c4200000b80c41a010364000266032603003072107400d4012031a0008072041642c218014071408020800000c03c480461341a0741001c0c00002d641034841d101c803010b003004140101c0c1148a200c01000205500788042e02c2054040c510280e91645011805420342d2009440b08450054418080090381c0e0000f4002021309403900f0219207d606200c480e5009008400101d900360140e01c180f5601c9840d21031030700b20020016815862118102400d02c01201c001c8003005041044003001402114001c82c = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 590496375 1250 590495125 590495137
    0xf03010510180603050325060c2a0503030a0209030a0b070216140f060901020f0604060204180605031e07080303042409020d11151c0c020f030304020409020a1d06030c060a1202 77
    0x1f50324481c0d03425503036580f000b11941c55603080c000401101f001c00c3c1e2405000201034040c48100300090b00c60300c45841ba40e0300d074800030380403e011550024540007152801e00a0510041e08080c7d003201d00d2408910103503c44481c001546031400e0100800b1404516064807965241d074040c007103450343c60198007403261682c84014018150710464165108055040010030710840c8124400b50f141c520b002c1c80308010502e59008001040e050130001d1011740c500040092900d102c031001c945403098200b890904003030550300191898080003003000f0900121030701d4550310045000c0c1d9500002c2400100310304591108000950099003008424007142e00c00c03800800300c20000b0032500d040304007009009816400224100403404508101075409030040c420004a44000c1c0090605048840e00c41d54a80c40000c00092003150f84512040071343d251030034144080c04010030801d4100303814010009030110100e45880c0303e48600c0c0e1900c04241048000d80d07415061075116100144100e0a013075004c2e41000c = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 590497625 1250 590496375 590496427
    0x150c020402040e0703092d20060409050403080a050610030504050f0a030309112b030509061209011b390f0501150f0302010c020f030105101806030503 66
    0x2c1c0b2000c00c0d0b540c50500c24074000c0c6400d440c00960110f41e40790809400d280040d0301501d1815a41c41411204052a076807240c69500511010385e02101000b164510204401030b5504144085800702daa12055400240621701a456100341643c0c1d1103d11025a442100c410342c000081940c1c0c8030356180a6009a80c0041c40ba4054404040000104500d00354446800f5000280c55443c41000e12400081c0f4232091a0242c40781d1500c4460b49100500c01c0d12064201498400d20701180401d040c4110260345040303800910756a60340f25495604403001c2c04c2a109a1480d5203042c150100442d9003040070b0320480c01c10746941c8110307500c1c442900c060440e5000c05a540a520510003440a00504103c5490f07a102d101000b4209400e41465821144020102602680c0c0040300340811441402e14204403036091078003101e842d40c1880442c0c250301c40c50314056050360a0405208411050f041c0304020f48525081103091111081c030071a080d034280d4480580582c004000703205034640b0824880b181c00140b = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 590498875 1250 590497625 590497627
    0x50a080a06351f0e0303150118050907080901050a0902090a1d0a06060e01141507050a0b10090c03090206030f0907082e140a0510241107150c020402 65
    0x1e00c0181d1030900c2904000b00741d00c2c0c42e909103805a920f03024804d00b58107404a00045041d49040c1046000078010b5681d12418000310f982c1d20300c0702e00d46050780880175040240018441d810201005070080a090322480895402c11002602c14922442030350394640e0001d140708102c0d21616201801030034040207042126104400498041204100c50580c1c0d038032030303280020140d241961555106006820a0841300c92155003503000d9552444030514101c1000303800c0d681d9144900e4024986000918028415161803041140e410200e080070000c541003002d0038002d0321100c81e01101181d0240070025030045090000c245070365005118a9030000115044443e0a80c988150a1810300341c40a00c026808680800f40030311418640c00c05400071070700005211400703000600d0010000020103002100d035803900002d14406460070943c00170500d042c180019a02c803206812120b000300018100403900d4440502140040083d20200312180a0700b280300000c50140112814050046c0a99000c1c0e0 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 590500125 1250 590498875 590498969
    0xc05060a0e0c0a0312081609270e010b12010c0c08030a2a0e12030a08060312070507030c06090806011205010207060c030e07060216050d150507050a080a06 68
    0x119020f4070400f031801109150220010050010a590001003000c81d2020411040c840083d4110b01148180c9540c51441c41150514810124940700101d90a90801d42081c010902c5154194815254260250f03505200008102503007420784400076801c01c0024400d0001c203001c0345d0a10701442d00814000004185400c260f07183d05010030030030f406621508488200040c4864008400c415100d9090702c0c1d00c0403c200c0620030717588034080c7c0c40c41c080c00e010b24900010f120b95018090440a0070213100042e4903210300d814503135a0f505641c04115401400c2030b2001c640d10b4052a80081180c28000c010a0f141e824015041945100c00c001181c0c11364007400407500080300b60050740100308607941c002a5100c4003c0405107008084d5010ba8255002150f1600122003499502425103c0c141c81240b8090040c3c985405005035811081c0501860101170241c031030742c040700030011400c440c0d45060107511051510b0f42214203d02c03a000700700c80110100c00148044100a0042c000070a01e42d1100b06 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 590501375 1250 590500125 590500129
    0x30309210d11280c060c030603021903030314060607080c10051608132604051305160f0923090108010e0f061512030c0f0109060b010c05060a0e0c 64
    0x6150441d111a99a000304002a6141103e031002101c0c822505149041e140c0c10100138082d4842c150004d05001e4413540205e04807030207a007240000750717405005003440840d020030442421100f07020440c00203041a030103400802c0107560541c018880108000d142c000e5503599004582d0004001c0810340c021076600b80007074511442100d105a0058520654a464543c001400c6020041c105068582c0221119001c41c1d03d00c0303550390588910302c03208252000d02d5000310703915000700e50205a100c21042c1480070000015003015004034000d028038050410800800e0300e806520810090000706060000c00c42c081c01d44103400525101140c41480106078403002c2030308a0000d8200000a80d11803a1030306c10068104a4000141e00e910043e00c0e540c14034010300070a880c001070b442c0388034416408801802040a0040300c66404202d82110b00c101540780304203000c2d181c0100300b920028a0f24030f503002c01d03501901c000c500150b071042c080d18096690341c050800074403040c05088220711403912007155903 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 590502625 1250 590501375 590501381
    0x9040302030c0f061b070314160605060d150c030603050a05100e0d05030f0c04030537050c10111c090e01060e040c03020405060d0218030307030c110402070b1314030309210d 76
    0x100360000c9c5540005006040034000d5440141c491400b44070744408501c00309902c0d01c00042c1310170364168003080441e84c42c2800c4010305000c2c3c00142c464002c00c0308940411500044211202c0c601c18018004e0a0840b41c86545034000342034a140840e030f00304005480009203098095202d80004c0d001802c0c0782d12910303201e04d419940781e44074034441000d841103d619600303101030030150049594180084542c03940e445440301000241c0b14000c11065407900407803809081c030707040d08508030f50403030b0408150a125062030101e01c100420103d2005080420454095021541a83d599481d0002c4451440c020b1100500c050854542059800e00000c101d6540b110020100c00c281a60003589030341449600c0c2c8211000b40303140b40d00c41e600c00c100d2180007a8108808411040d04030380c01c41141ca0062000c60701920606034000c18030340303161040107076070014800001d10b01d07400f5480405540c0d80000069559204c10780704c141042d402102e1045c0da00261181404980503210f070b9107810062401c000b0025 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 590503875 1250 590502625 590502637
    0x60103091a090c040204060e091009050c030f160509011b0b10060801120c0302130e01060e0708060a0f050d21090302030d0f0503071d09040302030c0f061b070314 71
    0x40341d010205000c852201004000480c40d01141c00718600f070f15100000d00070302c1000707500e98065411030000031503903614861900010001c0c4a000d00c0203241000f0803000c02e50040328242e5005540a000c208802c0c04135049000c80c10b03c03038a81030318082d0550015502e00340c10b001002d0081f1131340b903400340028100340300f02e50242c9422111380069a0801d000a0944107058005a510308445040f160104907004111004c40f40c042d54001c130320a443c00001405440701e400089003e41c00c01c000010040c001104c02c1d481a59184d80356001a29101b0030009045000e200b24030a03105404420301440c1f0f40b1404000100c0e01c1600360109002c048101d001d0079083d51241080401c0681c030b400c10960405111a403a205003600d050303080807020405c0900b1901000d0001c50410522840b01d1041e0203003031136644419078000f010300d13585242c58540207540741e1003202c5075400d9001d440d074150790b103481c00240f0034000c03070011507109424107141490b080c0c9504074240940c2006000101103a40d050b8140003025 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 590505125 1250 590503875 590503913
    0x60d061b121808031611010c05070209061c030302030601020a0c080c0306060d050303070c0611070c03170a170c090a03030906030c0f120b010522090e060f0a020306010309 75
    0x15074800300100d03601100c060070404202c10050300c0005002078071003400c4981c0040c00184d00180019440740488840d0616104813009600c1c00ca01549420f030070001800d04680308a840480b107030784031810300101c00b02c111981d0005405844075030001a000703401442e03109006104688110300c05131954001e00342c00760300103034440e040034003400c00c03070b04043c41001d0b8004403c3d211111015601c2d950b440d80d03440003c0600c001c104400031240c08101c40b40d003220000b0500d40b420b4640301c4140b814042044a0544000c0301c0f01c0d100122441c40c05030958003520341c20351003a21790010b0000c004c0f0104400f240018070f82ca40e540760420000c6203641d01c010140020b14000c3d5181c15801e420420080c084841568a400a12140005400c0d555a02042c42c03c41c1800c403510105400f8124801aa19030040c0c200a0001c1075116000c5a6651060520b40b0202c0b12202800d11150203588001919010151070007103403044003200080c0c224030a40c00464005406140c0001c1c0080641c54502c004101811220 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 590506375 1250 590505125 590505137
    0xf0210050406150308120c0a0c141e0606010e010906020309041802030604050f0c0f090705130e01060f0207051509060304050705130209010f0e01080105040c05131203080f01030209060d061b 83
    0x210080d5400f4440c9902440741f08126241283c01c1e1009084c4102d440340041c1030341d202540c40b0501c20b1007800102c04105054804036a84070744071102a4646004980c00ca0020318011600c00a40d8420030419045802e179402071441d181c0c102e400c0c0001f6010240200c4a9482c1b1440c140300103880030844c0502c070701c0c0540e002c1c1801000b5100c100e030074082150100c1d0b10034588200030b005242d132070121482e0041c1c458105241e40708000200102d18010542c00302ca1003482541c0009141a002081042c464001f50f0950f03071707003079100c90030041000d000d00310040e5141400e00502c8242d062902c02960440c0c051001c0720891544d60001914160005454051064000c00c1080e65541c200c0300030704200c0c2e01403c141c240340c0381c0200002c0000005103d4280315540310400030314124007850441d041c9403002c20098441c02d4449240150116448008800103201180001c9900c44900310b03c1d416298001c1464840361201c1c4200043c541201c0f40c240c50550359000d6500d8003030740a098171003032074106031644 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 590507625 1250 590506375 590506387
    0xf3c0b0f1e01080a050609070c03030f090308010f0e09070902030606040f030302010b1309020d061a090c030115020706020a38040209011215020c12040e01150f0210050406150308 78
    0x40c1810f2001d03140c0020321342000d00303012240e0b41d1100400d03482800b42ca051401c08200b802c00710060160681213001503403070301803101d084c10f0340408030a0581b07980083d101c0d1010390350b070882070386240100c40020441d000084240404036090f001150007810013801c1600307107901c4024240d0620016402240981e40d509445080c078103011300d40441c2c170710074002c3c00c20172000a034001c200820034004006050503034445c5160748540039900026501040644000f4881c94900d082001590082c0112909040402c4589003d103100007006002d4a00c542d010b0b1460340b00035501c00180d581044010745885001a40c003c0780c070803e21000030f030009860b007100d5039103040c18014041d000c0c5040c0c200c426014040410a40440c6070040d90080e5541d0b0800d0042e92182d1b8802c1450070100b41d22501c1c000d0280001d40002c0400c424221b02e4103075810301010720241d69045900351260f030604c030080b0001d0780000b01064104a990703401503610601031000400c3c1c03680d040a008017142090780080b62450781c04070b10 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 590508875 1250 590507625 590507627
    0x7020901080102031609031505070311071505101208092b1103010c170a2a020d08041e05010e01020406030204080c0f0f090a0608010f3c0b0f1e01 64
    0x1403420405c1c090b041c0401d00500316100c00740d0083c602a080d200481c3c490740400c0c4140d10070b6000e160070403201e801c0181c55400d03510b010110501d4801140c0c00060900c808508041169140305013181c2d0882070f0080c0c0d48400b9a03c50019402007100190300c80440110004201b0781d003080d1403038114030911003041c0b402236032400702d030100258114280260b2600031204282030b0003500403410624411000c100550320802414094000c101044820b04540021581d8801d4a1100c80c01a180c80b6025103020700002f4800b1281d021046030044c101800001d40304200c4074030303681e8446c13200e0301031800031807508209d103850350990740568001d0000a50008040090540c140256229140c08a600f0559041e6030000100d059412801051242e0608404103142ca980c0d54403000042190740028846010070815150092840150004104200420900b118003071072101c1d40417403040c80032107a8605d0341041b131100200080080960003900e41d00a44050b40d4030040003c00618581c0e982c596084a0341c80 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 590510125 1250 590508875 590508901
    0x4050f031201150f05030a09051e010b1201020a0c02060a3608010e030921060a20191b0c080616050403080d0f02072a0b0702030a02040905030702090108010203 70
    0x21a101000142c2011300400791340300d030480e500302c0204c0c2030200b050002c90800300d00700440c00e40150340520348082c040b518104103412004480d40d045910809050050384621700307030712070780b40000002000500c190005140c40800303800b10740603618082c299011b240c1d1079020309903c3c2800000c401c61140001d011a29230526100d40603144043c0240045032500c8441d6940f0302882410612235a007030440d1070f0ba01c640390408200440c500c0e40407110780b1305060160500030182c0ea030381255200307114054050885070107011118171031003800d4040000d070307000e860848040142a00c16440b0400201100e80072601c6038500d01c001d8860702000c1d100c1c50502000b07160100103138042080502c030040c0000c001013800d45050f109240c07481030f0f010a6050702c07404c0b0364009220700c44000304041c51502103501d0102c0002d24000c65148400c0c00315031913076164500585140a40c01001350705520a007201401400c0c0b0750082c80c2c0f205d01c074004880c1055a0340c5d002919003d400d800c203103a660745c04070800c2a0b46100030 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 590511375 1250 590510125 590510159
    0x203060903090d08030c07080a090501030b0409020d0605090f031b0708060f0a11120106030902010e1c26030f0403022b0f090f060c0b0f09031204050f031201 69
    0x160040d4034004010022030301c9000f4258001d00b0707080c0b0100000c1d000080081c02c9480e5140e001c0000d960b01c1409a03c060f1584106014050008c0e2038413200d6011130510f840788a070826001840301840310050364845000d04001130151000380030b112001005040e0800103011886480213943d03444001107031046203001d076a644031034000c0d4040030910401018800c03041350001c0d081d40021400340d0035941c0001e62489040902c3d180a007040c000000c0807076059100075210340c0700743e0300c90207003100c414100312404262558008040b00c2c85024080082c0044071700c450002815100c184500303000c090215825041201c100d05003070a24001c01c4101a81403202001c107112054101382d4100f200d00340f0003100c1201701e961006001010160888060180c1c0f552001003c50700006070200e80c460400920a4400b2982140d21204501c08115420307900c001c1d5503c542c9801e8003c1d400d000c0d990751a81e10340c1402900c20b6895000718030f00000e0101c0c06000508a403141d152828810317515040c0302c2c0c160780c0091 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 590512625 1250 590511375 590511391
    0x903030e0604170d0b151b061513090501090c080609030f09010f180b0c0c0a24140408010506010f0201020a0e040b031203190606050a0504090207031b050703020306 72
    0x1c2420400000d00e62481034800014245005031030340f1880c0e1024004000c9030100940c480c00102602e19215440001040c001c10800741001d11801041e404990f140c106481e49142d10f0348030584d2044c10308201d40b800012807191600400e1500311512a1401c4401098082d2840049036506004001003000501c1d00318224200451400b900c0102080442c05001c2e20241000000320461040030f20a0140a48800c0c2079681c1c0745800c6e13607420445540e03510000340d2080c540100c5840c0c0c099450305001c00012200d90111105d40f8120300c0201305881d007e005c042c90300303000044810340c0425541d075000e4806402d1900000515040141c009407071413000c44001e10071a801000341000e03075540f2040301100020103880101d0892034000002c0c0c01c14448a500c03802d902ca0120401064035042d40c80e6052030101c850040100030380340c9400300d070180708442d801c07008200300300410006c01c1d000307500411140d4020302d0900c203802c14000700041c00305405542943c0c141c4c4440c1082c400d42c0380902c441030f003101139 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 590513875 1250 590512625 590512633
    0x70503060f240310050609130201050301090f020c0708030901030f060b070b330411040302090f0a0603080a110706052d09060a020703110d1a060f04020d0903030e 71
    0x44880075185000504014142c034141070429000304a0540b0784082000080075070741c61058542e06034004220890b402403007100c1000c003003211001250400041d058040e540e0b44e185a08150b45003024240d5071004203400c81c0c0c204880d0711010030901124018000d41000ba50351021100c0006083d281081c21908c0c0d0240f1309001003000e07900480488898950000302d0802039518050f003005107440009440c039624503195526402014a00c0c0181c06806040301c3c1000046070181038811240542e0000a4008100f20701160319080b080782c01d03d601001c14500442e501e510381e40c030366595412a0680e0b002280c014080505e4221040c40001c0244c1402d28207a81406200c64828600b4910109851502d40011070301040780c2c0001c41c1180e0340d100300079007140d540e00d5038060000e641d40400d200075102c0c0f9880d104140454a041c8c1298050319400c00c9100c0440c804002011004841c06481290300444007002c0300107a0303c2d1070000e00400745540d540002c4a032041c2c1000790568500d03e9070741a182e00 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 590515125 1250 590513875 590513881
    0x41508070905040b0a05151e0909071b1209030312090809060f1308150708040309060807110106090501180209060f090d0f0b0402040f0902180a060e09010e07050306 72
    0x5446114032044440869010407121404c1e00410214174440e00441e0300040c400f26411944841d070300051a0340d0b103004070b4076403c03c4103051101582d80034115800d07600c5086100800d001ca48a118071244aaa003500d011210035020350b40c02408040140210f00403441c00b240400c20f00d50024840c5400060009041c08bc00c00d4554429407144a182e100611808021841d07452008003c402c0e40c03503030142c0121441000340c403000001e5490207903079001d4850340940400079941c280b18040c00360299515855803008141018015074203100001c2c4041c0c100b154254003001c070140309010318001080d00d1580001c85504090f541031180c1143d01c1003145881c010031180c0317621f44905c4100c80000445484080e102e0760644000ba11700340a0f2071001d03060607044400c4130300740880c0d0140700b0b0180d40f00316020044c202c264507400f0b0a60300d0030000a5402040c41070181900d101d9070702c44503030102141701c00040c1162141048a41c3c0803040c0c2d01c1c1d0090360340da280c0c1c072010001c3c20014507010b044202c0082056203 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 590516375 1250 590515125 590515127
    0xa0c02041b12020c0f0303010306090209070f0e0d1713080d0e0a14040603020d0b0a0c09080c041a192c01120f081204021503070e0906121204150807 65
    0x2c10720785840351901d40d00158402aa81d800c5c80400551034190040d00c4d50383d6544d0400d02d001c0c00f810141a03100c0d82e41040440c649900444942c0c1d20406940c03140d813005440031007002040800d6200a4803030030b4081d04001801c0940000a002076403406c0c103490086070400c04060310740300e4419804030600009100840c540d40d114414142100d10f810301d102110368503a0040b03000b91400e580020b4201010302021010014a19041c0d8400c1d15080e004001000b0f1800003115800741a104e03418003074002c150b420290f0b051a030801595862018064045d446888000c910141100c8280d42c0368094030034801e02083e43c040c2440c1070740c0c511003000d07920005103a104000343c0d05018400c2900105d61000e02c4c41c200003010b01d80d49040b50b0011101c5440c2c105c048005181c80600715405c900c9400d14140401401c03055005590040b6055500c51180e040b00b5010f00c881200003a20665201d1941c451401c03850030100300e10011140c0510b80079031640d1401e081281c281c40684490014082d1590070403101f1 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 590517625 1250 590516375 590516387
    0x90c0507140d0c0615120c03031701050d121701090207020a09110301051c05060a0618090803070e0109092307022a0103140a0507020f010204030506060d080f0a0c02041b 74
    0x3941c1c0040e0002030034452520b19501420765640045a0a0b10359101b8030b041c00b101c6c0c0c940e030040381c4c0a0380725608080e04441c2800c18143d400d0181c02c0d40b1480d0803e20801141d013602c802c2c40240ea4508044400041c0342c1742e60100410244e00c4440210f40000d10442107080c079100010003400780500a101502d101c403050b11040c001401140e014030f034180805100304400c600c05425440e000800e984c51070802c841d07668082c0c8018081c0c003000e10258445d900d0310380000d1003040c21103a0480d000074150345454108a400d0611003898504000200a000c40c00c49a50f12440c00c0c201c041030103000910740e2400f441d982074040140ba03541590402e102000016840322200043c8040e5030051044810910780141d00402d2090010403040104a04004241c3d42036407020307024090b150200c03070712131300131200441c02d0b48698000140182c004c01d0101d80c2c2803c01e07060031a90b040c441d51000381404061000c00782950486502d10f00014103030340642055007801d10501458400041185a092143c4a405864 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 590518875 1250 590517625 590517647
    0xd0c110a0323210310090516110f070603020906090312040302010201060b0310030206090120060402031903120207061e0614040e03030708191a09090d0f030b0604090c0507140d 77
    0xc01d031000000901e4100917021a1009040851b00400c400c0c20704041c218818042c80000d8004071340c0c1050303004800000050b5601c405401580107000e000e04025049010703400508010390070020030300c0b00030415501405408044045401071640b1a4030f5800021700791952540306c500070050800510110503070f4000414160707501a902c0a60b101d0706100103c07550074401103034140705440340030099602040414a640114001c07802c0355482e007000038415040307808554004022070341c0e01c0b10000840000e40c000c7d2221078000c020000c2c00d420a410700e0210000e85c0d000b048040350303541030144110360300c921041f00c80703040507030b420001d400800120035600c1c4000b51460040c06406000180c214440030070300b01c1d49a00f83d580038030808401030981540c211021028078030503000c0000103203c03000001510099110b4030754904079160301014040d0000d060008203550440c108100c0420076010034042d00b040790840f55a0141e660480341040011003680c03a102410316040140080e046a50100000c00 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 590520125 1250 590518875 590518933
    0x21030b01020d08040f06020301080609060108060c0a110304030215040f0b090604031b0810270f021c1a150a1a0c0118060b010f020607020d0c110a0323 66
    0x31344403400d00280c0300c441444028000d60001001055001000c81c08900501c24902102c00d907076281c088490310b588085900b010741c00b0092054103031281c800e4802070528003440b410349140503180e4000c24a00801074003044280c0c40d0000b020401c007904491054001d218a0000300e007050000c10015584d4030592001420078000400c00400c0c08021090440080420740e00310b9860243c0880c1050107000d030320303140d11603400d41e03000c04901e22103000c020b42c0d020b2644240441650b04240d07080144c0c2c40c0c074803a03145854240c0080d071100060500100c9058004000c10380c90140e24000b401101c0c00c881500c14240a4460000d04005014000072002d050307910039024241c50301c0001004500410900306250581e01c00c8a01d28424400c540d032200d00b00d46000c1c1c2e101ea140703641040003660f03200c40a0300e2500050f4400d03161000c5552066040012580c860514595840e4480c13001450940003500159814000d1102003440b044c00d16800280200c0004090705091051124900f408030b45640c46035 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 590521375 1250 590520125 590520137
    0xc0503030f0901020d29040e0c0103180b1e1f0611010b0a0b2d090d080d051009051f170703050a0303050a0f06080a062721030b01020d 59
    0x142030403070b0a405482c4980303e480010080001e107003112140410702e003002d03030300b0030040346690041c181414042c0818680303c8500825460000b54011801400700f21a01740041000b121044001a40054524080da0401c554103a038044130310403000a00387c001e4441040700b099040e00401540700491a0b45c111801410a00d402d00c0710400500d004d03110b440001e0740e10050038000401c2801d4074401074200c001c1c00580c0d500389065095412400030050315140b1840d21400c0c000d40d1007502d030441c2a443d00781c2c03058098908145c01003110700c041d90340c290703500080c0001c0c0103400d01c8409603500c605544102c0c0c1c40460342e13144800c1c0c042194030fa112400307003045600400c00f00304848041000300100031980902140c035106641e0030018001d02e426603500d81801c1c1896018020310a56000c1c3e40300303440104004c1c101130f4499944580c0102076884000355500070b402985c8212032001c4180030085401050550103c1715003408078a1032610343c0080300b003810329068060f10541d9000980321a8080745003803407 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 590522625 1250 590521375 590521381
    0x30c050625140a260c06010b0d110304030507021302030709030206070501140108030a0f1e08040203010e06070e120106060e06030403051606091a040803060f0a0302090c040e070c0503030f 82
    0x3082c0c400040b0180035852254100050400c00303031013101c943d42c014015002c000f0911034880d02e03507648901c8050b9052a0b003d80014444402800000c10a00f441141c1c002074820f10141c520045420444040d0301150000c0340c408194100014101c03150400741030704500d540362030907015110719400d00019000d107902050b00010054254800d075a81001159451007540c3d58401441e0751783e11104034034000501900c6004500c43c01541030345017020000c030801005c500000b04c216208400104240c0e45507480d1040700384a50800d0007150300440080d81e80428a0069000303000d1000140c03803000c141d0b0380c50a4410800036a01c42c10140a280341111002d90f00d46483c1012240c601411003480204240f1b10f03d403404004259000c260080d10500c415006108101180c105d03034401100c01a24400302000003624920b002d2060103601d04005001c040c2c90f640f690049103003480112030041130828000b0f0144992201c3c24600c950015480c43e10002c02c0078a0b07551543c0361701001d0188a120300f911004 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 590523875 1250 590522625 590522633
    0x130b2d0405061f151e0806220e0a0c08151006030905011d070603151508060a1a070c0608060307180609060b0d0b0a0303020c10210906051308040e040309051207030c050625 75
    0x80c0c16071281402110040c2c01181070001d2042f280e449407004501c00c03502c24001000c00b50410601c034014056003a01014a083c809502910316044104c515568404070441c010300c00588080340804d040c0000c3c49882c1c184a0701504a501c03213050031130800310050003000300200c03207100016050481e281912480d2200000f0a80900441d040300202e242007001c040c11150008000c0d1180305d00809061100b56910740c1305443c1910140c401c1609504011005d02c9030503500100c2500d501c4050000081d1103545018800072100282c20440e40302d030300003584075082c000c9402101c0564001316080c0e04503a240d030b50007a649008481c61580a40d13040c403d400308190080c641119009464020351601c495020324a000034031145104a9840d0300c0e010214120200080007044d000d48d11002540c80c10342011241e00c28454020011400c101c2c000c03e010446840d0840c0506c40c40420000a0241508510b08100b80c02120f13040640508014803612008125601c10f80d031032422031702c4513542002042c2c20 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 590525125 1250 590523875 590523881
    0x120408130302030d0302030a0b0105031512120f0306030706030b100e030307060f020a08010602070f17010e011508010501090504020109030b130b2d0405061f151e080622 74
    0x88065854044c109540074602d815030001c61007125085000c1050400d102c00641e003d01042d04d204005507010301d900d40c1d041c01d00405da40c43d50b82d00786040701c40c00030a030074101b11580e1140c50f115151a8001c0180600c505040002201501c0c650600b40942c0350491702080303400009012000800c104240a0072740761b102441195803941c0c010405200300001c041244c006540500c00c844002132a0310000900640301051000a4482c50000c0754099490220080b14080000e40c0390401550b86540311407106e0b009120300d2a80940e03100582804620f0001d201c3c1c21076a05034440407041c2e080c0010440142e92040302c580a41c0d510410030765042d01c4d2405c05000e09500b5440007400008000d052100399003051a074072151404800d80c0e4104a010b070000b103103403c1420340f0002c0c50795101301e0200f406070348401304185a90b009103808000349592100001c0300083c0442c0824085512031341144042c40c403400c3e00da0441c4555003803860b1a414030b580410301500c0300104006207880c621162010078200d0760 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 590526375 1250 590525125 590525129
    0x10815130309050a0b0405090f01061e0e12210a1211070203070b090a08030403120503040218070504030b0601020d09061d27010806040b010e04021f0905040b0612040813 74
    0x2400905041e9102c105c50441c0303510a024551290107113030300064141c40010380f0b180c1a41c0055541100c42c2c5149840c4d03035400d40c0a00051000d00c9400b800200c50b5407200301d040844070303801100400e0b07000c15403030b007041080c0381d0308020b514221001c000c40b02a1a8125036001403048040800080044a400a00c07095010b00b0304000d515009800000400b0702008014107020b16045a6048206655409080d030b41c1c0f0891100809115004036a070000034000e2006c2c5600c1800501b002892008420303050481100458900303001c10340110341401030000d03620507a07074002820700082000c0184444040c200780c0091290204000c1641e40c18203804029140d40c038070f2001c01411011a1110030b00745c207000e11840034a014928002d0200001d010b4034001500ca000c0c6802220608450f401c0034040c1e004488010010b0360802d14254844501c490b0100c030003003019000780e8640410505120800064a03800d0860303d1086400b844692215284540c14036003080d030154045583d025140c0d0782c100110095 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 590527625 1250 590526375 590526379
    0x13090e03160b06180a0504020307061112130807082d03090d0302011506210b011202030403050906160210090501120b0d060c0503040b0f1920031e01081513030905 71
    0x101c405c1c026160f0b40d0b6048280160f10071815208003a4581600716058410700c428400d880d4006083c0120600d6520020a0403050031320304c1041c0359032030f1403150780307485680c0c0e10065803035121000a900e032400c450080e1002d000c40c031010400f501c01c400512503403402040c4c0c4c45032140c40c0d228403003001c01d4007d60080a0fa00c00340055403020b6569208060140c9008180c1e500000c0240725161411080a1050410340503050f12003120844c000d000704402508001c00807810701c202082a50810364418000d09182d00224800d10031008240c81441801011038182c0018031000800600c60381c0c0c2c004162150707040741d48400161450301e000002e940c0c8244240c01030451483c182030506507660140c02944200d00450300317403100c3d403510f031b03100300400c04101d400c23024186d2007504c1d0402240103904a00070841c00103019140484030b407140502a0f13070054502100050928003196502d49005582d140180880c4028041e0308040b1240406000c00040c901407000000076626010140501200d001034040 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 590528875 1250 590527625 590527669
    0x1b07120f0c05070b0c070801061505070f0606030c05030c030d1d04060b0d0e06070f02030702092805090c150702040915061e05120706080a02070813090e03160b06 71
    0x74134114141540d0013005418030034011500701268149050040c40120303030001415442c0c1e00c0420b4012203841c2c11084080391802201d054031390200b034003806004051405460350b400201d141c8020146080020a107035400382d00110502044241c1103920800d0103502a0080d01c2013480480001e4020300d170542000c03a403408003040d85a28100300368441c005005580c011144180c43d026001e9822008068032000182d104010b14001030401d00034050308000010b0744c040724035072518940b044450200403183c1049513600704000d5008010810401d0351f81c4259182040070100c44007100092113014030280c0500d031911904800c0060000040000c0840b040007003140584801000560141c0b8192030402c9110903040480d0511300f07058a4141d564070840203207000c5107000d00070781722000001c11b1911b4032642440311901040300580200680c0c8044d001d1409100d00781103120044a0301c600b110701966005201140344001003441282e221508041240c80c0d03690f4560024000d103100d241070804c0164 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 590530125 1250 590528875 590528879
    0x9030609010b01180e01050409150f0e16050114070201110f0705011e02030a140409021b01050c03010b0706090816050d0e06180d050111121b07120f0c0507 68
    0xc041d8042120040700341d8400700602825404010f0300081405812100c079910401040145850350001168902c110064260200e603070780200111141030051200550711903025942c400014800800e41c0d5101c0b240620007942000f000078180c02110042106407480000d1140c00e684c010b0391b01110000e1614100c95100030604080e1b521070189210b07040c089140b02044040483c0036114941141e2090740c01581004180c076021a268074150000d00d00c05141000040340d04004c500041468003000d180c0b401503104c550154500b100c80060003402421001e00050084c1030f0030008845d032885d0011001701d04800f6608105480b0310824031030022901007041c000d4101720b800302d10414841c83d41c0c0c8404802c220543c0911902d84200441c0c05c408050301c12114203185003180d00103c00710b01031800007035400c0808004840d181d2001c00f480b540311810100f003040410201c07403182d03100a0004e000b28280062681c0d07161800e603100070708a040c003950000301101c092284002d2014544c000045907002c80d = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 590531375 1250 590530125 590530141
    0xb04140310050403050d14040314070c030c0b18030a031e0311041401020f01090209070f0c020d0305091e0312070602091306060e06070209040f08040803040605030709080105071d0402090306 83
    0x1034040958094011f0920001403c03e0000c0d100151007035406884070101000110141c65099000400032034241c45001004030200c0c0200461030040c003481c2641d5030b0385920503d1030481e80d204103a5170324440c0d44111880800603502191101c18032401c10041100381805103025006022159051941d4640c04100016981d0104602c4140c0795030a8007924620110b40500c2c60907102c40b0140650002c08401c007180900e481041800c0c1c05031620320b0700000388440c50307000480403103900c1010780c00a031010a90400743d140c800a601c80c203e8015032464003e42905001c03945404541546180602003c1998800e10150342c04640c202c0400421018082000c650940f004044078020140058400b54400c4540d003040c2c03048540c8140c0051084150b13030303070300c0d41c40d04560b0002c100b00325107550040c84002560346040001e04050000c41c0c507080e44901c0e0503c0300408030b48680d440010325070304002c140105c0700d4101c200c9040411200b904110303003540040102d4068801e81001d142c0500c1038904001c506 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 590532625 1250 590531375 590531377
    0x1501082a070614150f0301060b0706020405030105060a03122a03021c14040506030a020714060702060c1c0e0f0a0b042001020615031e0a0c0605040b0414031005040305 73
    0x514400d000030446611842d68202d29150125400070304c5424910303800815192038182c011101c2c100030008204141c60f00100d074074039000b07111704442d040d80105042c40700d85400e0050350b6011009a030345800003461a02c41c1015a40c0300307a900424018240041032004102c10300d850300708021000781c1048121075180007540c82e16500c9480800694400b80da82d0720f5840b8240d08000710481000c0141001d08003000c028140c0c4c405018100c016600304802d50016480001c0800400800400303401241fa0640f0040c1c1480001060255044030030000c0c50740b400066680d075105991200c0001907032540c01d041355440c005081a02d500390748200c043e50002c0040305180540b0407846030500c440b072440320040c0202c0341021001603501582007000064008d13181044905101c10004080300c4e501c0010144121070380c0b02c003038000d01882e0400303024442409984412413009000d24500545400d290800b841180e000724041da026411003c548508940e40812900d1303000403280204001ca8100343c034000d0b00c2 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 590533875 1250 590532625 590532637
    0x13030f271d010b1602090604020403021206010303080108060f150d020a09060906140a12030e1e010807081515121501021005220812010b0c0f061501082a 67
    0x1072114080041200e0220400ba198800c1c12203000c2190420030ba404c01006140c010149038116500b40000800359071144130070740203d010f0401038001035055040042c84588160020304d042d0b40f01c0420322088013165400b00354032180c00f100c42c0d00301d00d004d81c0028004841800c400395000281200204111000780d1000c81103500d0f43c44204103543d074800c002014860120031695002c0691030007003010707030074941c024201103100e450082c1110030300c18000f8891f00d10481c1440049209589070410a5801a4210f60401c20900382003400c2d10307040350882d0703a060903242218001e2000d05031880700e81082c40165108084c00940641c2031346800c103203c2040c1d040407440c450052240300440c606680d90b0f03101d00e9000d00d19050400e5900641c000d50b400c0c4141c9001000c03a103000c2c08210416618100140f503501030007040200c544c0d250b0640150500d8100380c44944095500868180540c110003000b698112003000e080445846c1e0f02c0042c50307200181040e000c81d011004402000c182c0851344001022 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 590535125 1250 590533875 590533919
    0x30a03030b040b0f1302130305030706050106030f05060d0809010210090b0907150210020f04090213050f040c1e050903060114090a02030606070201030911030102120a0513030f27 78
    0x10080c03c0060411a50b0b01d081c041041d00705240b01c0010306810303502d80040c503000010104a1452944e00c3c1d43c0c0600e0350340001c40c15251682c0d594014004280d0500074031a80101002e018081414924000b800c950814034004040042c0000c4e0012182d0080c0003a413041b88101c10300304151001402c21001c80841100d04070114003c001010904243c02240f0000c84030f9154000c14581c1c8180b1035060007540008101000c500082c000007880e8a0b041c002044802840d889250020b8a04018003111250704114540b00f1402e25a100e1042a0303ca5002510305c02400740c1724018403d00d102c142d400d40f1a1503859505801500b0010454050920b03001542c00d8054445c8011955081c6a5004138001a92007543c001c000300014005503200381c000d038040714042d0007105c1d200b40000d00061b08a0780009036545e01e0205200400621000130f2003400d61103001e128485032207086a550007840d0315854440b8000b40300f0310320501d01c002070400501458140052028003c42234460041c1c4e000c1c80d601c440084 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 590536375 1250 590535125 590535131
    0x5070e090604032c0d03210209010509040902130905241311190801230c030123040203130506060a080706140c030a050c060a1413020102010b030a03030b04 68
    0x6200148000303001c62050740c069950031400441c01003220400a1111107030300d1040c1002c0c001c03483c9982c801d1001311140f44039884041c0222102c410094070f082d6100c01240078070340305211445459030424100c482d50035044500080c9119035100207551904030703e200003a1070740b4010094042200014a04e080002c0090b01000f070310201e1030300030308450005c41d20346030030342c0e003811050b80090412144a010208024001011060a4070004c20441d02d42e6009460380c3e91101c604030340720100c0308014500d032402002d104580b8500740d6450b6180d03200c10310400c1c00110111500f900c0d1281052542d2402c81001403003035580e803c1c8140d0500f11001909070075500c0d8000c900100701e0030304c0d166420b039007214041405420b07041d191040030f40720f0040d142c040c110942c0c1c3c2000000c20401c0c083c0001c01022440c0e0f11307a80d4a420072840514134043c1c1c01080e41401920b1305d170041440c2c3c846403203410382c4644000400402403005100407400340c418500615010b03c1142c461800300b50301038006181042e42941d0070 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 590537625 1250 590536375 590536381
    0x310090203010b07030507021206070327080a081b12010315180303020d020c061603060f0806160e1903023a0203150103060f060e04080a12060f0305070e 67
    0x5a0100d00c800c1c407907182280b10401060001a02460103880b02e240006d106960640210590f00d05240b001c0740d0000009a485001395050411042040c0c8490b81c410801c822020762555080d200f445003d01810a101003600000c00300300c2121002003030388021080a6403039038551f05520111280c01e0108445107541c201d110185d0140398030481080401026480740391000c9600c0c260004d44c0403d0001400310340810851040c00010000280900214a00086036900b4070304000c0460300e090700b1901c00003501c2c820812444200042503030300050310003101c03108000440701c01c0e50a005a181081d40180c0440c960146a1442124003400c4038001e403a5402502d0018500010b513055641802c5600c82d142d09034003641903882001980d0642c400740c00c66800408040741c050081d5000d030300c01c944068441c802d40050f00d20750701800c002000005940d910600302a034682596010b500745200c104108815000c1d00748265800c46401001200400c00c810750300c03030401a44a40780d500032010100c41003008 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 590538875 1250 590537625 590537639
    0x20306060f1906210e060a0b010e0a12020f0904170906120a0519050907031e050102040e1008282607030306080a030905060d0b0301140a0b010c1212060b040b0310 71
    0x35010305c4144100250100b60b03220b1142c10001c25031022183d0400440707009299180d210904444090100e03200c00da10342d081c0503c100100d032070104440784d0040c5d84507010f200009445c180014034828144104580381c4020f0390100d189070003841c0c0c2072204a0500b80c103010039000740e42d002c68019000841e00080400d0b040300900140c605c21b44007003881b540000e4007040460140003100c001c62200720000c161044498a03600d09a070490b8001e4000700d444107050005c8424844007580c010300240d40035001c038500d810300310418291020241d42c05030403c1100d4208000b03908858801d0480c07803100644811440d2004030029801407401140071034134088010a00c040300040343d4a85a515544035031102e82458144031070364200c1103020b0750390b80e00c072640212907680a00402c0e00e49113848130190090b02c0c00300000c205843d00c094829042c400a010f905010903102d005072504911982490114503d000c08410020802d50388081c040031008140803a0000840005601848594078240a12611500 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 590540125 1250 590538875 590538881
    0x806040603120c020a051201060e01210201030902030f010603080a1103090f040c02070909080306090105010503190c110604050d0810181107080c0f0d0c020306060f190621 75
    0x140000702810403a0442d64442e10808038240c1c03019068036152a505e83c0810444401045110304594440d0301c10b00ca81e82e440240c2d06c1c01804041c000d200845200d0070b0110b21084852000380c101921488000250b44041260b01c0510110038000c100702940ca0500c001c09030080002d400024140d8500101500e02c004103517021000010300b2807006d0104042000003d0a4505034038055000d6007400040341c040c2840b0b502915400385800c1c66891074014100701d0300b24016000b080c14030106106010209200003540f0b000d5400380340c40020808000b1805a0303020030b52401d14285440b9400400080150125488150b6911512900316586a190500d4954401d60080c000d800d00403050a4140d030a054001180b0b004400ca9800d250100703d0704d5188090340101d00311099903000b2a8400e400080800c50a078848009140c580a4642d466001070f4444502800301485003400e410744000580e1000c905400d120203246400005507035600001d41003101010743d03c00152640c4d022034101d40c00e540 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 590541375 1250 590540125 590540129
    0xb03090d180323150a1b030603030509040f0209060a02101d061303120507050a020607031a0405061f11010c090608010b0c0c03070602010b1c082506060906030308060406 74
    0x3061004150340d50091042d0030300f007112062441c0d10030641021200c2c0104031080d805020000030210b05c80c40c0700080f0782c0c4940b410210780b42c1011301d81241080484c0c0c1c84002c0d10b20a48040310041000800d03400418041c0c0a9106529407101000036800840f80d00001c102441450085050000e1103403108900c04100d200f031480c03901604510001084681134402c07000400c1d1080c1840c040354480080b000007281e070120707070300f2020440c0060405600b5404020301c5a00c103451340303418092189040d0401000c03071020480c650081d5159008030b1f445035500c4544800700540401402d000108240008001800c1419660120351070140d01d1400980701d07000030f209452081c4c032101c52691030702c1008000e41d48484003a05090242d900c021805da9001c3c4400002080c8981c0041900c940e134000b00204181907400e01d1030054040c1401c800000d42940c103032030210004c19190309a50860300c40401c00380d1043d1b00b00622081c500000400c24081980c401403c2da80241c0d1400d00d00d907520800e00044915034 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 590542625 1250 590541375 590541383
    0x22d040303031b0c3c1a16031a090f010f0905130209270708100b18060d0606080a030e060306090103020f0d020406080f0c27100b03090d1803 62
    0x6001c68030202c0c181d0717140c1c4130b211400c1d8071052000c0c030300080c041c4200707090245a9950500500488100b4803207104a0460b455004400c080710500702448100d800c854510000c01c14191a8208510084500d892250130844050410081b918240c070b5002ca20180900806030140d030103803400b1507000003138405c25205004414400000c58120b40801c01d030080000c1078506212084021041e0112808080c110014080e00c018076941c0c0c21f140c100c034100100020b810012a20308055144140e407041144941c014882c0280b050a44a10001c88c4100700c2d10b0310f015004909220000441e01070001e800e50381076020756100480c01211a041003c3c5100903900c1d150301070041300052026140920300c0301d0b0080d238010b02890300140d0aa01141c151210740d4010782c0d56401800143c034440e10140611803d81904075a50041c00c6204680404d0105d4565414200c1c443c82c0d40c0011307180c0980e0511035015214201030f8584034030f0400c800c25035401c807148042c0000f03594086580343c5e551a125002d0152584 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 590543875 1250 590542625 590542637
    0x60f0c0804030b060604050d060504150b010e0904031b150b010804020904060506030f0a0308010503010605060412080a0e04020d0e070b031311031903091401080403080703022d040303031b 82
    0x19640b2190283c50300a014154003402c204000078266403050300000406103d88004100d80c074150800c0d508015103201034100483c180300048a480ea489200d27048000340858100c100da0b00c0c0d40c00e0440e001d00b0401c0c410070700840c0300c80302001070051004044d210b030980b00e501445042006401111454030544009400c1064040841c0018459810042d4808005021206146816030855107405010f078000e40c00f1a00c0e00e00107201906080c05000003420041e10700d549400c2c5480c0c00f040c0700082c94100600158404515042c03600d00c12030086058280c01403040d9100c0c0050306011005054080b9184000d00c1164030004d0038040c26002e40f231142441c0070701c2c140c0001e01030b16941204482c0010f59545401101c2c0c44180c40580613a1115041c2e0080c0e4940403101e05200440c0c4264100c0601c0134180300341441040300090b40010f21640c041d10500d03015071112109004806106040c3e00400031485c112003130b404009031450081d07c00c41340a96000c0c80004000141d100107144c141c005d903000506 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 590545125 1250 590543875 590543879
    0xf14010503060d141e0115050303030402060c01090c0b0a0806030c06160c09050a0c0801080102130311131119030b100e060c010e010903081f0e0a060e10060f0c0804 72
    0x5089410001c034980240ca1811206444c0701c0b48a080002600364401031050711210010f840340240300c0d08100c104032802101280d0708100000755030f4000240000e10500340060080e1020b20203422041d1080c0e40125019021510754034a102917803c8042c0700d030001940d1100040191600080c83e009664003e0822441c0c400c9207480403144074606001581c845183c29000203e803c414800c02e842030300c0c002c5000440016444004043c00ca060344004010380c01401190100c1d0b40d072039111005c480c1e2000c0e007204070b0405a00403a00d0656425a6070b0038440c038012845440c40d102400903c41d80030400500941e03a8200d81091b4100c0d611505515008281c1004c200595800307919003007000701000f020241080d034620034250035a406d04641c40383c16511200c0d40000c140d00034000a812041d035805c240d00f100660701b105c0b191001c182c81000f4210b1060302c0401c00d50705c616403103000500358503903201e10b403454040142016100c41b4800c0c1800a00d9201c000e1111a100b540c100d5490f981c401000d45c0b03454 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 590546375 1250 590545125 590545129
    0xb040b091e10120c05041803051c140a1506090b120a1e0e010609020304120f0513060e03060c070c0b0c070504020301030f060e0102091c080915040f1401050306 70
    0x18200400c501400102d095000c108511021140203100d0701c541901082c0c1410001071109886c0014180e5009010340d07044480000d8200c019241c07000038010603100c2100d0b1040d245070140200815410320701c40d411040c403081100380d401c0362040b180005007071000306036218012101184544075420b10540c040c44003000381c0340c00b601603035009400450040fa21007503520354102884076140340c1c41801942d44059100902082c05600c0041980c1b00e000c41c114034042d19540b02800400c3c1e40f5804001035190200c903428000c20a88100307451400b026841140c40b02800743c90103180720203840c480e204000c000381c560300500d01151a4250b200a0752095079103440e580c01115007010400980d2800f40000120701e41d101c9101a5000f140a1100000340030601d00b06241101c810508182d443d900410180c0c80d2600c4003001086a074a11034045207419049040129040c041c0e420581d611103802208800c0d80c1c1e0141c4041c00550304280014010a641e40e41d0a40361b840190041c01d010036400d20003e840e42c = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 590547625 1250 590546375 590546431
    0x150a0804060e0d1e08040804090b0307230a050d0807020d03050c16051002070e160e0306011511010b011706130f020a11010e210c06010602010b040b09 66
    0xe40704240216101c50a008454204000c3c07801640016107000c2a0b243c41c060b460781c04c80401005030a040c5c01d44d04003a221102144994014880180d0300c0e00180d030f146403401c1260000600c41d40310904a4a0045c51006c03681c2081034003d20b124050790038010865180c110441c0102951228000c4c1c5412000e900740300c911910941e00780e061003001e0181d41d140b400e0600c6031020700300203050000d51542c00c0100b040b0154075030520120441d40240e6043c0040c14402094a420103604543d50824502d20a4101d8942110640d0541c240c0144000041c0304038100f10704161100594480262006810074858200c0d82940e405500080c0d01490301e0f0540003442c411690051400b40035845880440c03141d200959940281c00c1940302d0780010009252903101061062520401009000b00d00c4000c2e0788a985080c04d0020141105040c241044040002022030b00c51407515000ea070b01c40e40c5c0d1140003034020060511030902603030408101c0105071901d000d03510b12504506102462640d6035642005075 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 590548875 1250 590547625 590547631
    0x4609060224040c0905070804060e0a030807050d02041d040204060e160503070302121e0604021c020a020106030b09101b0c23010e0616080108030a12021204080d0b150a08 74
    0x3ca80c41d09070340801c0b4010b031400b42a1007034810f07071103680c11f6040a01c4c00c00220703031040d81034281d2034006402440000f41e224140380d0b00301034a4030303040740c481c11101c052100038071a541c030251600b0346c3d603400c01880060039844a44141c1c000c5404002440c0d0f40d20007900d01050840d000242010f80d40c49010300303240100095074000c071461a0060501c0c0540d07901c3d40c0c3c0c001003500d03940c01d0030300c0d0042c80d4441e01000c9803680d80c4c0080162000d60070080e04002074801c140101c07200611207a0007080400c107161003540850025a00600340c2c11180c142024080d8892040009040105040134061901e01002c41c0b03014003582050b9840f0001e01203503450301c404000c40101c4800c1012200700b10003a80d031109001d84c075a003e0700e94015001c00e09182c40031001070b0529050410901c80c040c00100000b103004020740b05005100c0c100340c03102e9650318807048000d228515a043c05070b03c0940c2440240300c0c80c4005006140c4403440200603541b040020006207404010a03036103024020098205098494801030b90 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 590550125 1250 590548875 590548883
    0x30203070b0403022103040210030b18090c040c0807020c0a060f030b011806030209010e09013c23040614040e0f03030c0306010f09030305460906022404 67
    0x18001c0c00ca581a0b00d12010145c0038021504d1003c01840254948a0484201401141410001c040b000008135040010b00c20500b42a00c598800140c481102804420340540c002481040000b0310b80300302403c0e00000381c0c0d02e030700148500c0d5011041e03410501001070503034000780c4500c5014404001c0444c064014a0300280c10841d0211800c0132030b6000c015001c0260160b80c40c050b898110b00400103154258407603400e07100e403002400401500d07094628540d4184201e10b80c45500b800003a011130078900c0542c01400a0b0010a540040e8141100030f01c50000441c0d01e4007030b20b011014000704000d50f60780b4000c0100d0840e01c513808410f146884c0d4003410784036401c3c2c82600c480c2410341a145003150021180030402c50800070400c0010340c0d000d4a00015004c00c0d0611140303650464900424501903000b0840a00e20001040d00071a204000080c14103655540c8000321215400e4a192103596503d00c89400300b400640042181030020491010240281c210b00c00000080c940c60701410380301600c2a5 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 590551375 1250 590550125 590550133
    0x8060c0408072607170c0109180e030705070602060708011d01051002010f0204030b0a0506030d021510080d020a02010816021c1b060204030c05040b010806040902150c01061e03030203070b040302 85
    0x3c1504402401298010012000c04003545110f0507800f81c18441c901455904010f48070720180403442c02e6050050743c07030b5060100000d200c00e040001c146144680e60020305188a60b03100011401c0e4000381e0311344144019510940581d990340f01c007540e28140517581501081c10900148130900300700b0b0341058200107620010480ca00c40210200c01c0b40c0c405e82046c1c1d000182c100030060146070328012070340c202c04203400401c001041403100a4440c4500980202c05e81da400002c01d50080789140948081c10312102521030102c03211401940c4c919107560204d0105012000080c419000102c01008804050300541400c2d10050760b209001060580904d003840300001d9090f00100000104074030a174414000165200e003103091001d5012020b51216129a0426240c0d14081e64044200343d0805000d40300450150384a01c0098104008800304801d50080810729000b4a00150401800c50301d078141c0b00c1c03105001c070707100142c040149400041c026034810440e480005000b40d1400360b1007030080c4182c1d = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 590552625 1250 590551375 590551439
    0xf0c1b05040e0c0306070203040303020a0803041b09050402181605160b0f07030f09030e010309060e0f031206030a0210050a210c0e040b011e20010608060c040807 71
    0x80e04451100c2c1001500d41c0c400b0107018000d060801201c0e4111809000660419140d940d00945e07540507020001c0041c1e00210110303042191019041c04804041003a0084aa8844440c1801030000b12801e03440b03040f503030442c200440400e00c1d0340e0703000d4400050600450070502e8004e48460b03008051208444c503600910002090850144500a030280e0046030110304142200600b6140c8605414407034525001c1107000080e0040340507070b01c5035001c1c01c3c08039211b900c1e401c110001f1f1858000c100c4582c01041c0025405003000300007003031080d2100510000648075802403594074041d0107002074100441c18a41540240104007829041d02e50b4904540752200080c0c50003034150000d44414019500c8403c0707503a00e0ba80021201d141703448280c0d4100300030300040d00002c1c41840c210a14081e4406041d0302184002d00c10945545540419200d50325074100c0d0100352802000d00748903d14841c02800c02080500e4083e0084608036083c0c01c0003011840d0800c1851039a42c44080901c0e055507018045d0 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 590553875 1250 590552625 590552629
    0x603081b0c0a030501050f013005030d06030c1802070f0303020309210901080702030901080109110f0301030b0624030403051b06040c03060f0209060403060507050403210f0f0c1b05 79
    0x180b071000d50f1003040082500d090045441c2002001070308400b00400117240c811010351101c0d002d100781010743c40202c0c100d100301810030600b54851040c50202c0c1c5410610b0110030b00ca0010704c180210b9507032a10010b194058100b00034224017503c507000b84601c1086440d000403c0c0310b500559041046882030700d41240b58480d01010a00759070707010040382c2c000852903c0c0c40d0740c2c02c03aa1301c680c0329034940041c61038a8441c100092000c01c0501070140110750301d89640d016050118284c0d00562080f8518035030300e5840b414083c80c0f4250894855208a030700c2c900110750001c0050f042c102c410303c0741988078107603202c503a411f0341c498005c00b88018490f0700021201004890801c41d117801580a04042191103007182004000c2d030301e0210420807010700410100160341c135500110740c2200d0b041603000071603481e0228100c0d414800c0c0d92020341000309800d03034580d0012200c900d20110981e00d0304c0d807003010800c821068810300000c01d600c03004901c2c1d260341c94010030483e150781c070103601c141c0d036140c0800307916000 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 590555125 1250 590553875 590553889
    0x43207110a03210216030e0117040f0201080702210d0b0406080d1d0a1502010605040b1c050f0105040804060206060d02011b03120203090708120705070312030236040603081b0c 77
    0x503041c6c001801014078564596000031070362000311811104c0e443c01c3d10f06078035090315003480004000e04208501000804d5603200b400140b92501c85215007030035200114101c00c000350001b01000e5800b40c640108404545441e11483c000c8400c0b81c0040d01d03010320152010f4840412445004a45409003086100643e550140c50400303845030344001c041c0c0c40f004003002801c6070003603001240550b29003580c4400079581c0d0b0380714580079044201d12680800842c94000d0910f07007100096200756003418203100c20050080050805e80d00541e0840b1303240e990750410004203000b0581d0190201c5d00b40200490421107525000780c5003800780c28001402c0a009204800300ea00403900c2d1542900100d000340801c000500550541d991001407660a00304a900da031600c48250b0b2100038801500244074118183c0244c05a0b441c002034030441100c080c3c01d070519541404c4000c2c2d001c01c24500040602d19541c9028401c0d202034030381007030b141c0b81402c11809503500c54546000964aa500c5087c11440c800c0e0740e421 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 590556375 1250 590555125 590555167
    0xf03010e010914010501021b04061d1f12062d0203100e061005210c0d0c0813020f2107150f020309043207110a032102 52
    0x244010040d601d000b0841044448815228401c5600c5600400c416139001a12841311000742c00007500c05005d100001c1d0080000754442c80044080708500d91311400303ca1111441510b0b00c054000c0485072209048550403040c2c051400d0a03404180c081c0041074040e40905040a1105c05000101d803120000c048600104003020a005400008004841c04100400340051800d80303164481410600009a801d5400e8400c8400f041700218000c05000407442e40c41c2000b5000da2005c8501f03090880c151203640d4005c03100750525500f0a100301d04000d100e03004061240450828621404581e0f50800000b18000c86a80354882c00501910040591415221170b01005410007807000a181003813040c0551a41d814250034407460320394510006401000f1250580c1c400c0f00c0000f0510188800916018007030140000b0f010b0003880c8001100750140b0030b250150740e036602c074074000500180d2943c0d500ca08070070005000031110524000c000f24000d07288140000a07010140c14000c03454031044a5030810 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 590557625 1250 590556375 590556389
    0x2070b092104030c05040513080408030c0115030809010c030509040e010f0b010c030507080f1902010504060e03190e03030408150f1b031302030c330721050f0301 71
    0x7907021500c0344224402203040124464118604262a64403a006883c420307104090203152204002400c0e1200d100000c8202c070345c0681029241c5407904a000e6683c0c001084d11030803580303002e024250951004080c403040301e51003c4094580002c1030011a003c28481c0021401e0000c00e0180c80350655980c054248200d1000e40001142400c1c501c2c481d00ba0b80c01c0c007078040e041c006000d0404003c03d84c40310455003030b140c0240380d00f540d40200860f231210340d1150001180504280000841485030f0640003640982d020350b03001e03c6070b04540c074840c0d0780707078403d413181c42c076030030040545402c00035000b441481417403800102070300e0410b50388641c050700308070085401a815404640030403900351580c0c01e086810003480034444207042c094141030f1400c0d02c005081e01603d880c207210007100310742e0100b2400c0c0381d0794409003ea11203021b1001d0451040a9064681072060400615011000c61210140d51815030003e50070f00300301d000815801a10301c1502e40002c100542080905060708030103000750b0003003010b = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 590558875 1250 590557625 590557633
    0xe13150f1b0216120f0302280506090c10030c110609030a1d060a080a09020d060b1017150a0305031c0507020c10050306040b03071202040509060f011802070b09 70
    0x10300140242090030f9003680c200c80a41848040c05078125440b4000e00203507110486180d20480c030b040c164602044500304284c1000212401300d003402c071892542d00a035201e01c00300d031a15102c508515454050b151410794001410703a28036001b0600c42d800c209030f036400b80e040211380d68140e0304c001c0c0e040030811194102c5a41c00080d00e4010700743d0142e59100340303059510700050718480340b0340080c1d000e1280c000d04004010145000c6158040140d106041d003540c02810103400304c2891404801400204412521450b800030bc00c000072409280b50281c4403080841c0e6183d2540d85030b050303140e55290304180d982c000741e21960100009400304010f01c1c3c180a008104901c00401e0101d900a030f80b00140488210741042e41c42c0d401d03d48030001c3c11603629180b81071040d280e5680300003060003400c028182a90500c503c407000645800300034a81c01816000350350903c015078920708080e03030b82c0d8000e498900d0084105001004000445403111413100d541240142c540700c8240c507160080d4070180c1e01e04980c0d0700 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 590560125 1250 590558875 590558921
    0xc012312041a070f17071b12090605070807021002010908030406090c140603040b07030f0f0504021005090604061b12081806070e040e0309150a03060e13150f 69
    0xe408002c1e03543c8041e152419150021510780018100c9403c4100da046211030f84021070103081c040c580c801c0c500c12005000709a6918039080481454251005800c0444c080c1308003c0307250b42c4034004640c0c031190416000c503e00403080d824029084403070f01540c030844d540e8ae1003580028030210000c0d8010340c040c24001c10000441e08184281301d1480e803110058000540c07002480b600c840b07059a6200750040218001030381d0b07914055024241c0d80c0303600d01205207002c4002c080545a50300c958086d500903a0146031a0303480540603a0648034024056034842400e01c41081403034410315148d03d4410191900c44a20501075481d030690b0b244502075000400c400744100084180e07806001810400104000e20345c074109080003a241983e52140c481c0141c0e1505c281d004103502c02c204503803605801030041500781440840d060315981062201c1c9000a0401800003200740d21054114011384003a1115030400c8620303074440070401d404400b4003091580b29818030300c4000c40340c0b14400000100c4186604000 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 590561375 1250 590560125 590560163
    0x50312010b070b070f0f0c0f02030303010602030a08090c0d120513030c030302061e0a2c0304050909070815060414070e10030e1b0102100203090a12020c01231204 71
    0x354011300100410080800e03101c109580010045c2d50201e04d4105100f0202050034100c042568008019403d48000000003400c5c42e400001001c1c4000c2c280e440355401d07200c506800c0c3c0c6800207000440e03400015488030340d0108a040000f0003142c0e4a6007405803a000c44001c801004c50301c00da105417503800105504009042d018041203601c0400340d242520038254414100b050004080c00701160240d840781e0303400ba44d92154403040580c141581c06260110142500c681c0c0e203a004d0300032035010706034401c0891038841e0009119400c0e1800c80c1c001c0c081c110600e0464a1800000034281580a41c03103601d81102c0d113411040082c080c4100341d80351481e029080c800c0c050b00b10004c11500c4101842c0140482d08280040b03003140c55007a2018800075984a0440101d00d0000d000b440c0240103440041403003001000050160101761003400e00090045000500b60b031104e500224442c00b080b424108640001030f00f01c0d00041803640386c80c003941410b142c00c130f02d07060310101110120340c0c5038101101440c0340 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 590562625 1250 590561375 590561393
    0x515030f07020f01060f030c05040213031b09020d020415050307020a060c030f020703020601050102010c090b0d090303091e0203060c0c15180d03091a071403040204330f0609030f050312010b07 84
    0x3130682a1011b5152154000301d880100026100c007400b4844800c0e000020140d02040740f000030400d903003042d910b64101810011c000d51140c86505180352402c030580c540c050259060328440c02e00d42e0043e103110000c9032500006030161000d41420160f40e580030b40100d040a101608200e8025801810958142000a4211884115080148006a2800c0100440f41001c4a40206061201095030360407032800703a015000b0180001e04040c2c4909454007100095016100528001c50440307555866000b020540c1d4465400c15660540000c100500031482e16010706402c6804196001c14a2600340101810f24501c90724140002ea01d6026400131301050000000c00703026465001c184a05010601910403031200c0340300c020482020000a040d03544a90088103000b2400d04a0041c1d0401d41c0200f05001100301c2c0103407100425280d010891074440090701c01074900b83e883c0c201400d41185c44040c01891750940490342c0713100c1013044070b16904c2c1781b001c241e00810900e1030a80d200d0505260441c01 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 590563875 1250 590562625 590562629
    0x6040507081204030215040f0b070507140109030f0507080607020d0216050a0618150c060e01060501021f09050d020c150702030c0603040807120e0a0515030f07020f01060f030c 77
    0x40740d000610051a2002d02011201120360444000700b10b5107115840004034025079201b61002030350a9000282c40001800400c007141c480d40603610000d80311983d02d4181c0401e0002103000504560702400011440d20031070b0800c1d4010700803148111345c0c82d20b0703a52408400310390400040c1c0183c0e484a0300030f03804103c203100c0c1452079081201d0880c208800300303516809510405081040b540010140c4541852042000c3c00d50313962503601c6034001c800301034114100d401e800c807131991500c060011075131010b20580c0d040c1c0700160301500e001441c5061900c3c1c1e0140c00420707030a0352543c1e05c0590000490420101010750095005411584100030420a0b180c080194001404600700054001681c001c81e06607140c420855003907407261220704140540b401800402891103c01000d0035408941203500ca100408046807a0600c1d00d403100d091020007120110b414400c8201440031980b0310b0075255086510002c01e1049a100c3c103405c08040d401e54000b03505c00c0a105201307041c2071007401000b07030749540 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 590565125 1250 590563875 590563889
    0x4031e021f0204170328210b33091809010b0117070f0f0504090c1709120316111f1a010e010e03010b190e090c0105120604060308070506040507 63
    0x1003000089180c00e811008050441c10042507501c018083c01401451004c104030500107c40103980341034413018000301a040040c503c1005404041c80f91100150781e401107440d444459401c0c1c4074182800b4a520f5005640b00030342c41016107580d41e0848001c0034001e8418001e8a0001c07955080c21000500455121050850203030007100403c050280c0002e4424032010503868204008400318104442c1405141c00c6001c0450030a1484404c0561280400c1101888801040020745524504035551015102842000d50003480040c0c00f89607038260041044050b03003460146155239400d06410310301820f00e0412130329079070030703d090200805100e0b54090283d10f00c81d00b00340d84240d5001922100500080304d041110103103d010068a080d0812096408080c206102c85251081d1644a251081c000c0000e8a0421000103d00d6070b800030f0030b0040300c50181c4a152600c440c0e00310101c013000006000542090300da2100100240025000b030030564003583c050b2615003000e00d0000d0520240d40c1c0140 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 590566375 1250 590565125 590565127
    0x40b07210c02010522050402070501050f070f020a03050f090406150e0604030b1801090501110c01200306011b0203030301031112010605090106270f030b010603020304031e021f02041703 81
    0xc070050340c1103070490b800b4000080601d2064000094824071104030340d08100e4201d400840c0001c00c004054000303d004401f142c2c5444c00f682d40e90481220000e0a404003040182c0c03064031040d01003406980285011030003a881989800800000325080d07034941c2d0301c01483ca4442c513480e00000f40d400304a05000041c225612450a23246442c4e05407200f101400c4105481055140740e14414425400449441d034000c00901c45098445d0304840306402c0b62001420715402c022a406c032010015030070341100342441140905540b201001103e000d10039101c0d18084c451045d80310030260740c0410103940218421844610b001a80e0014003514000080c4420410fa040030030500c11550344189090545805161100507480c1038040c4040d046810700d8901c0d80d007002c0410205440b42c49030480010340f4000c00c001c1c08a40d0303940d00100d04031311003203801500160340540c141c0a80402c0400e60203081c01d241c41103925581d1140c0074040a8690300ca800d15100c0d9000030100002814803520700c0d4184207001c061 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 590567625 1250 590566375 590566397
    0x2130218100203041a0c030703050912010c030605010905040519020306010c140a2a15032309010e160323100f1803120b0141091014040b0721 62
    0x15528040c588e002428803002144652440c1c6814600c0c4030181c0e50b4030001c3c805c480030810041d0003040035011300d0f80000c44205001c0380b07604040c0161401030f031918422000070000c04140d0030094101618003810403071034405460210340d094408041200000000d8182040545480c400352000800340c1e406031441c580036006450b00308a03042045501c00b0340c80c91a803800181044005107024100d441c10103915040c0183c0004440b240c40d440f8902c100c000b0041e80d0b440900d8290754042d00031411010300350400e41031001031448a5030580340b800308851103030045164241c0da0b003030243c00386d602d00049070340f049a0030461405000d0b404000f80019171001d082403407520001c103120000e002c449103a680f107015040450341700c0c1e500e05d01601382c1e80d420361420148035801c205100d40c4810b4611418071244481410805251040b44e9018600400443e18002801015169480c240c0d0050040345014800020114502002021184e2040948449524044020800302d501c0728030072008010147c848 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 590568875 1250 590567625 590567647
    0xb0702011a18070309032307020907020c0d080a0302040b0f030901060605030907060c051203180709050106050417010605211c0503220609080408060601020a02130218100203041a 78
    0x7550b0032680744c0c0b401003110101c2d402c0a80b9201640081c08440800c00e0202914566805010f804400e2003207171078405680350075a0490340d64403009600765000440c00e903c3c01c00145411b004265607401800e0140c1050740e9000c0058041d0805081c07444150310000800035044030038030925000d0240350500f2400d5080142e800c0303640b4080ca014007014000381c42c5510702404020083d00083c005000c820555a10303008440800c052002c40e880512445091390100d021030150207100d0603611941e445500f01382c509903024884580f010f0a00f5025583e4030400b0540d03807500c0b0000308600c952003202880803480e143c101883c014103103101c20504031440e208400d80982c02802c907900409850240d5072055580000b0140303100d00300308020021460250600100802c01c0c0252045030382d10825544076031340303110059807030b04023410000358000700ba2000300a10b0b0b40e0f203a000e00441000794106101d9140b20340049016002142a20070243e030003c41c00300110b014130080c2030b888031941e449090402c03110300c0d0 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 590570125 1250 590568875 590568919
    0x14062503060305121309060305030703080a1b05180a08031c05100b0703090b220b120a0f1103040602070605070203160209060f0d1209080f0a060c0207030b0702011a 72
    0x1035068006100000c1703000000429403100e1005d0301d140c2c107007049400d9a1b89802e540d00d40c00a00201c0100780329500241180144d8450403060440b02d05012000040806084031075511100f00c48440200340043c544903500c990a0803c06081208025640c03003000710307541050701c19452858403070b02742400c041141020503801010104c6103842d800c05d032900d4240c5401d903407a850981041c0c80003c4086442101d40e131414802000050780380705003c050301d40b0b81100c05140d116035101990200800b40c0403d48006283c1c1c4140001d10007124001400840d1718404c455540c41030790195801034020a0180a028051080c0d80d0060070300d000840c94030007504200340c40c0001841c07020b4880c81000e000141a920340d02e0320220b01280050404002c681d161500f018098108209800083c4241001050403240040e0800141c5024401009090403aa0703ca902800d01032025000f14083c1100003c009200403000754011141500045200071780c1c2007c94102188021105106000c00a2543c4c2c6071800b9007 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 590571375 1250 590570125 590570143
    0x9150c0c020603100e070503040c15081803040f030615080f0d0f1803060e060c04050a030b04050c0916020f06060a180e07180b060f09060714062503060305 68
    0x20341c907103490f9901d50741d4041c803000c1160310030130005c0c0000b03080000207a07021006520135440b0742c0c0203103610307a1180341d07143c000b059040083c1e001c1a81c45010403614440038a01484d8205d9a10840b8600b0f6103844d018106d00f0300584c001c8076165104d5104404184e844c08504024150100080c102d010386104015034580f00e140300030b0301703015040000840b01d40c883c000c1c00203001c1c0020031000707159550380341100c02000c9032a40c810300c03400b0740e401107000c04010714212421030b0002401c0618190460b00c0e2064003e0010f04112268030517000c8550450b214010384c207228214005801d196032f103a81001074140340c881807e0340015003200041000b1a50b0750b000030340595081121001600d8030100c0701c0c100800440504400d0341c880c0c2e241c0003503d0680e04140ca60100500181800050011400d2104501070325112a4410380d007030181c00102d00700203010f840745501a107101c01800e03101d50500c90a03d141690107400110066108400303c1c10a9404040e13035081c540f5040090303034510740f241c9880e01581 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 590572625 1250 590571375 590571379
    0x706090501030506090c07150b211c020303162f0f0604050a030828050a0b03061923040b0103060b030a03081b0c03040b0315120a03080402012109150c0c02 68
    0x244024423100c2d503a50300001c0001e001525405d80404403c040292060341130f28074130700610803950f04055112182d411003070840c09540056055446100c45451910742c640044020080d84a411440d40c82c52130161084010502101c1041a929110018140850a100d40a040c0c1c4001d0074000042c0c400102142e40a0b09407034521015180d01110040300c1c4506503003802c40e180d0b01303441180641801d070311190003006110410001016090281900d85008a4031301028001140f00304001f8115500310004c40034010004e04480f0301003011344e0050010075541561444031110040c804c008592003407a40c3c03454201c0c02400d04c41721a640090116000030811801540c511281d910f4942001c8144c81c101068030041c0c030b4135aa145d041c0c43e0410b0700110340038801f490301c2944e20407040c1462583d0080c1c060008001d080c2c501c0749918251000780014104030704003c1030030540c05400040e48200e19880702d440300c0c0499940b00d02c1c00d10711011002e03549454819440e102c54403000303541003803004069a80c1 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 590573875 1250 590572625 590572643
    0xe0d050c0d060207050a05060603070614030a0510170304150305010e04020f040b0d050c0414060a14010e040c0c0c0b0c03250b0f070206010905010b030a0b040b030706090501030506090c07 82
    0x5854044060b000d0800020f09a10929414108002008c511a4460f150a800f280d1403181d54500488198503a90308900c50711a081010a400c554241c01055000c8500c8903c6513684d0350310310b8040310040540300f42c9a20354102240c2030006105031902d00f4001c03105880d0900455040421000303c401c0082d000034800c400182c0003036010380315500000b9001d50000c21a00d80c03842c250070000e8544184560646c81280341949101e003007115560a640200790103081500440e00740703081c0d0b5a24004c41c052460501001c06c550703109942e900e005090001055650380d02542c1814a002460718030950010000d9200a100c0503804181c008141d0313103600c45010410184081c0f000c40b074544a401c181019010400c024200f0840d654841c2c800b600070b400e2035085600c1603076505903640456800380108070745100b0030004140e10312150380000c0306070707200144005020600500000c1c6041c1290b0f200b03d000c0b5250090421541d03801d440b130310350f010342e090ba41b10350302d0329008030092424402d0040c02001500 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 590575125 1250 590573875 590573899
    0x1306051e0703020a1203061409010e040b09070f12030e0301201318060810050c0a11100c0207091d0312070507060915050c07020a0510020f010513030e0d050c 69
    0x2c401c200c04d0f46241e0b0824000d090703008280300000c000d080715010310f6010019410741e45002d81081664a070403243c40384240c0d07046449a40d00d8988046000d0181d921a101d0a040400c50301c6802c0305090041a0039810300c0e040304040d160183c0b10f0b03030300103490510030791511102416009080b0700c0344d44010301c4201060341d03038a141c1e190903081c41042d810410944078909005c1029404039404281561410011298041c04001550060b1001140c0800000380b0502404c04914090482d00311030260442c20740300018070302c48030340080b03844090802d80140d0141504004400c1c1611881c20111104209410b1481c000004242d42e40b02d210b0307801528841c808006080603208405660071154440700c02d00c0003160a0601d40700e1212540b590060391840e00d0301058022405034204c414940d400b8029660513441c05081000e840c0c4410307105015802180c0310492070b440c0a104140c0700300c40b980c0000313110b0f560700d050080843c804218042d0180402c1050f00000c44c0c00012103801100d412100002044 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 590576375 1250 590575125 590575127
    0x1505031602151f0f0b04081c0504180204031a0103030f020d021b01050903070b0d1104050f090a0e151f0e011205010f09030522050609040b030f0703081306051e0703 72
    0x455510018103444c030183c0103d44402084000d104884901e421510a4101882c03800388004201c40d00501007941040b0070440040343c1110000700480c140030043c20180d0b031343c0311086076a020000d141307001401440144201b41e000380707940200b80c5041c030003031045100081019654800c0e5010311040318840200b4002c040e8428011550500000f40548800302c0d610884107a20382c11068a02031040d00f010320240701e086144c01554201d54004284260803e07680081c0103280801400120304a5107620350000c401500f0030804842d4051418100020b01c1d0050b01e400d041e05d10310020500c0a1400c85081045840440e00315041d1403030b1005800c0e03103181914029004098001c401300000381000a482c7c18140c1001c0a401d0b80f50080003103c1c5000389110480300c0003403a600480368881c00500900703007a800d00d40d0100c11000ea01800f00c3d405000004101e610b080384907401243c82810004855410342e0b618140310008040c941005804c0c0030304a00384108500000c1c90140121201041502c141 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 590577625 1250 590576375 590576431
    0xe0f0309060a1101150803120705031b09150310060318020f27070905040c090b0f13030203070b1b01050907050f04091202060702010e0f06040b060a150503160215 71
    0x10101404c405e000250303035131050940329000b1070f4662450780100800070b00c07102e001d581180c1c403818081c0384221440300c100b06410b2441d00f10004d8150045400c1075401d1141c401d02d8000c5002e0380442903000601d901c2c3c128010142c0b03001e902100f1410b06e800d440240140c507500c0041000d035104450f40006a9618100f103445c08250341c2108031440000030a000360310b500310302c807035003502c0050300c0500c108031100c03c0a50f0a01c40c140b181c00c00000707040003c1c1200802910280c2400301c1c01d0720051106550329000070b49040c985420141200100158034610f03800c9480301088020802d0000b8070036880c0051116449600314480d172401450100444080e660b101d81c010709019a100415141030b4014585c0250303501c1c400c0b41c0c0100035601e04402c03001c05400014071014000071440061026542d0396940c1c0c801200e015142c40d030082180380b40400c64208480f459100603d907a0f84a540701c0c600761806181c1e08003229655415500704011006851240d0404c66030f00c240c01801106071000d8000040e004 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 590578875 1250 590577625 590577641
    0x10b0612010e0711120306120a0302060a020a0c0f060c1803080409021e03040f0b06060c03041518061814100305190e070e011502100b061c0e0f0309060a1101 69
    0x4034000c00c00ea000c00c628041c170183d401010252503850001c0d030307a03008255858250000103405a07000600140a04150390010800e460f1f1a141240c24900d1980d07a02301030360341903203048a0907038a483c6007241e80d960051707522400c80c070700000c0c08528918648410150f40304a0040c1c929042d00060550094191000c0c040c4900c41e0818109a8a04d094204085040c1c00c102d003c132510b0324409c01049003071074010142d4140b54180340146207050316011081c07805541c0d03c0400300501241200403100c6500f480038000040c01d80340c0301c00e00e021150445408000340ca0b500080c808180c0c0044c585555210000303500c031094158100081c041d1118a00c140040403061001101c2c1c42c104100c0741c4001c00c0c0480d41704101c070110b04101819989402c0c2500b04841828101740050388030b440000280000703034019044070360380980420b00c1c155800103c813804050701081d840b22a6143c1404c205240030070080e91400441080c0618100032a003c0024510f10820b2007401c2003200b10038004044140070740c00040 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 590580125 1250 590578875 590578907
    0xc0a030506010e06031302100e0a06080603071502030415091d060d0804060207080c121518191a060310090515151e03060402090c13090e010b0612010e07 67
    0x61246042c280651019406c4a812030284860b0030500c0280f50191240780501e21004001c103801500b4080c049501e030000401c21541407041d000001500c50301103100d80d40031500c0b079016503521414124507086464400182104000c0002010410310002030386403484801c0c3d98601c2d040b113841c0d400c000344a0101d1407101400794000020001a91500050100300702c4d501401510078102034031040003150f100700c0f540790485401200c000e0111810031442954032104182000340a12707880d00d00d00e0b141c0789074001ca00b41e0203240c443c0f031481440082c071000041002c1541c0000424900280425215002d2400000c0215260700c0510b040007014094801c000080c00c01000c1c0a2614459010302c0000911741c96000f407034008200c003130100c4200840d07021280040c00030030301c9445503400d00081c410000d0100408ae00706104250203001129106401882862001309000e07100e003a62908445401d01d801d44a8182040101d404001c1405490304450030500c15407010b641b089000e40d8241d041c0442c4070 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 590581375 1250 590580125 590580127
    0x1017100e010b0301060905040f0f151a0a38040302120a11030724050c010e0a05010501091e20030f010e1003050c13110a020105090d020102030c0a030506010e06 70
    0xa40000c0c415800300400d000c00310001e20916039592400070450b442500c0283c400d4a02c80f09000c00306007404100002c0d03c3c49000700c10076003048400094220b51185122200321141d03460040b81c98a0700d6810040a80403110207542040d00e1086203030003040920103980c1002500002840055940d10b0584004503005401c420351014150f6501d900c42030020700855a43d083c004140200341000900305007643c840404807070b085582100e400310038800c0c0420345010080d0400400e0391150081c001c907402c0c011020700400c3c0340301d800d151080c02d440f01608485525450700040c0c1d00e0440085103082c050707010005c0c000620301251210b2800c0901019800049000b00100b8400d507000502142812180f080d15804650341728a0840b01e440c9a01748400380607030748100000c510f5440d01000702c0d000c84603400c01c002280da0070b41d884440366400030a0524050b1750b4a008012030071030280051158580c051008516525003404c40468502620140700105681c400c0050001c0e4000c07541c000201c1d100820302 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 590582625 1250 590581375 590581391
    0x305071b0605012c151906020a0b0603010509151f180e0102131419080102280206010e2208091305070e060c070509070206011508101710 60
    0x700034003020f102c0d140780859100051404150008035100700c8403440d10b040c46003030700c414561840c0783c13145003011503101b8448885802170800d00308a0400418640d00503000307070842d0f400c00100c04e0500500c2d00d0b0190341008100500d020000c40d0b00c405010404825031110b03111254019401620144240204d0f44085400b05201d103040340100700c00c6100840902900901d84003550a0b4042c401c0c81d8084d01c6001c11081c44100a030f520400d00e80c10f00580941e4182102c107030389600c4580c0310350208107da5030001c0c10314a04003510010368144100742224411902c0003507002542d0749414400d2000640005000c610340c1c80011401c00032049003060700000050300f508050b103140d4007110740c052051344c00000307009a21102e4020079200302c0d01a100c125072410a40c0034040740ea400a05081018040c610b00420a60750340c19003103004015035401001e5035814070101c203d4880303061051105201a08007003040e03080a0b09100000d441600d41501004001c10b100c5914200c2510a5000042c0c10440c0c1 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 590583875 1250 590582625 590582633
    0x15040f0b04020d09121403011206020c100b01030e03040503060a0c0c06051f060e01140a14120a050f090a080a09030210110d0c1106030403091211030c09070c030305071b 74
    0x10390082c0c010394005000a0f40a0400e80c1c01100701c0b004000d06c1c0da400e100410042c001c48030302140035402280d002d40707030154000034103080040698000c21041c5d43c4580060300c1d035900d4411080c1c0c00c0b0710040154501401c1c480001d9503200020041c14039961208680c003c043c2c46803402d0384480c3c0d8031080a0055003022151a11440a12030340320120340c100d18000078086104462403482410103031120f41c503000007082448030a5016003040c00501002042d5130704c0f0f42240c20028400d10001d6845541e40e030505003003020a07510301406190400c1d007101c060142460340800c401c483c1e02e60103455170f03551780a2100d050b19a103003640c2c400385d40400070082d80700c0016089200f10038884409811f46038070466140301038400340c202100103010307400b0404140b401030038000000c5400038042d083c85003c040e540c201040854840e11022242002c058407041d019040400c8030b54082e601c101c0d400c3c600d51400c214001d00d59600448040d0030036442d1000304d60101e02801c880d05d44081c0646920f0420581030078 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 590585125 1250 590583875 590583881
    0x301030305220e07080c1b0c10030e070e090a0209070203070c06111011040b03010f08010e15060d06061707030209150619030e030d14070815040f0b04020d 68
    0x210a00030300b28000901030510030011182402d072220700782508480e4490200840380e00600070320b21940c940007000a50350354007441200d852100c00c900001c140d103212880500030b107401517030855001c0c1030805500303a0003500c01240c0e080540305481072140780d030350710907168a181411018010303400c030024600f403200c0150b0104c020030300c582c0640915140240d442c101155000481c040541c1241c100700541001c961103030700108440b5440220f84c03030034180c0300c601342c0500c0c0e4800e0307000040c880300508040050007020b0013084141d082c01000381042201a03446402001401801d0034403c0d05800200c0041042c1684190f0260940c80c00e140102c42d980c80c4081e40e142c0b9031b80400c3c0d100308100e100050300a03100c01c091024410015287d5810084e54802207150038024103001c806068880914030803020040029207100484100081400340c290740d800000640003a01f82d800304030070b1400b000030300012020143d8003000169000900c1d10244858100140507080f0318030343c000d0001428001c080f043e50 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 590586375 1250 590585125 590585137
    0xd0c080105041a011202090f0306070e1e1020010924110d02090a080f0d1403150108130b13021c0506060405060d0609061a01020109020a05100c080301030305 69
    0x62010081c81011400714249a2a180f40450015101680c0440c5800c07194001d0b0051520141141545020010000e41044c008681207000038910302c84403001d91a0003807240b681c0103044559500c5504500c008106002d4041c00c144081c000e101c1c102e40b4003005541d504001d9809048020011b034202440c00440080382c1c2e140852041581040903000070340584a5181403e41490303a06151005244400c1c010350820400243c3c8020041000603240d503081c0894240d02c2e8000001d8002c07140c80c864068201c0a0008091140c28024020042503880071011100c50382801d0a1014299489002c4084010b0382c0190050118112105000c124840194040c18003442210b0300700307800781040b1460b100350001034000f50442d40400081401420194480794200c480a0040085c68a00c4d4035150207841405104440c50781e621108210b10480042c0c500030b45500c244000e01c8540510780018100000c94091340344500c0800e0b28581ca418040c1855085090348104100c0d00c1c1d40e540e05020302690031607 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 590587625 1250 590586375 590586379
    0x6161106120a15050a0605040302132723062a0f0c0705030109080d0e0a120527010c0303050916030f05061506030112031101060f0f0f060203091201020d0c080105 71
    0x2180130615103861050002a03072480e645c1c0c2801d092850f001c028149801740f1085000998903000c8035804000c44142c100700c585120031030740d0700c4942880c3c11280c003000d0022840168902242c000144040410707142e800020303181c000030110315490419490700c003c40c514001001c50001f0039030014010240500610b08610050b1090140d580042c142039814402008080348810418400304203019803207000a01d400303604584c90b01d0140d580b900d400e1401c0d142c074000810740c003207140c410004c0102c006450f07150100041d4440403014800107040c0d2501c01078024103054469000a03141c8800b080f080030090f20700b03040007007203d41d0f9050410304150400b10580c1c80d4080d03080081d00e0452881400d1044440142c00285103078a807040501a840143c0da0841c10860140e800300315819090040801030310b100035502c4080c61612070030100311809076001440805045070100301c025008403d6031240141900c0161105404455881c02032061608603010140351202000c410b0317a1200c0583c4c1a1441 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 590588875 1250 590587625 590587661
    0x60909090f16030b18070501050a020708060a1e0e12070f0803040b011701090c0e0406090b0901020c0705090907260f28050601060f050f07080a030b06161106120a 71
    0x584c007000c06810103c0f141c0171030b07650b20070541001294842c50007009440c0d0144141c03000c8940711042c0ca4100071090b611060030742d40b298204014081e144410030515068880c04010841c05e0030841515924011001c40b1a18404564401406071039121020b0741640402c44551341d1810f840d0541740c0840a01a541800c0c42d201400c9a110340140f10360902c894021450f03050440c0b4101c00701400c0d41c802001265505d4966003810b0000302c015903200d0040030000000358a0320360a10807146401c0c0558451031240c070108042c400518800709103401564460500010383c0034122100510001c5d281c845015a4800c4800b03401034208046151064480c6010002181076280300100b15000e041882c045c040307410141c0100300080c0500c1500e0b40d00d0031a41005410503001d10300351000ca400141c0162603400380061041c06003903040c45aa00480c03000c441c281d046c60302024003402c10b94644030000784644502c0c034001a0a41d12001555000c2c074400c030107524186030030000440078009a441d64116a54 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 590590125 1250 590588875 590588881
    0x507030608060403050f0a11061602061515070218071205060a0510180503010f0504020f1c0803040f0f051f0621080f0301030c061d060909090f16030b 66
    0x1101040341ca02035505941c0d020b04000400d0361446c2c072a0b004401d10030501000d030000340c0c0b045ca4140400c80c03003180c02d000d5403420b2548008019081642c01000580203161070181d40025590301c4d0082c500420074110340170348482103031020503058408282d502d00e41145503000c1002c4070340d0051040900740c0015400388540d8566006000b0901140d0065640c0000280140c0032080d2081c0c170601104240311040b58011548d45021034210b0300da450664507200d40f101e0400c800d41c100729112544bc044161369402c001000f03110304040f511680e12006060020000100d800c0c40085140003d020345c00010314418001d044c9007041c0d541702d03a140c494440450f0342200d0f24100303d041c401c800843c0c06980c9400643e030f4485427007080007155541c00312001181808120b8400502c90080c50281d8401c08103000b041d810550007a09241450b8854241c0b18002c2d0441300301921980140c6144202c16510060300391a803082541c2441c030f404640400e1482004070a560842c040d07031000084030b00801020300c15031 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 590591375 1250 590590125 590590139
    0x2070b04020904031403090706080c0301050a1e050402041d07110601140604080d0306050a080f0334050106061107050a03030f02390906090c030a02120a05070306 71
    0x1014005018000410a900240260621010041c1c2c054481d16240401000e00c1d1201c42ca0741d00260303104041030388140000d00005810414194002050244660566140000060322a9841d00421001000480c0075a02000340c03e50000058280200255200d03512500c0c142680380d80c60361260f2000d420840800e680724011030304655400b03209000362030240e080150340e01414400841c07041c1c101d82c0401c80003c4014040c45141501005550045180c42c60941000403d040540201406070090000c40c0c083d010000103c800141c08000c3c0c4001e041c03015085040000400c0d1000701115034188440d1040010652242e0300791102500c54051480e00c2200c89d42d954007440c0a4076070013040422041c40400c0c002d160b0f40000300000d204660501603481e001015a40020340824a030f010300e00480310420105a201900044050300c049074507260400005002500180002107a0440040810408641d81c1c04440b40d03000703980c3e2031134079905000f2a403000070401103804000003840c00001141700 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 590592625 1250 590591375 590591377
    0xf19031a10080a1104030f110108010812070b07110307030306050411091e03010e07080c211506010e060a02250501080103060203071704080d1104151d0301110c1002 72
    0x44a416660300140c1d668404030040205008000042118424800000014a1504207c1e0228840d117034107051889100000b420041043e000b117051034009030601400806010203403918507420619080c082e1b19800d8007920824100c1800e40c900c0c1c01b000032150145501134100304200c600965080107007150f02500f42c5039038083e03034010740e602040105a088100044000120b040300000300001903980803620703c0c618000290b40607103140d402c0300510b08000c3c83d2040c800d002d0031103400c0988030300c920380d50281d40d00d601030032202c80d0700c1503140c6003c284a81d01c559031541000310b01600740ca03034442c0c40600207036450304081e2610b42001c10f03d4014513455200340c00e0000843e02c0684030642d00b64210b0b510b01d400f03034000030040004c000c282e02004050890a80813980074501843c5400d907990340040c0200103441c20300400c101110000c210401c80c410b61940c410642e100e0500e448000b03070036494080708000500c68840d55041d821300d1140305810442100a10312070181030112a10380711807046050507 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 590593875 1250 590592625 590592649
    0xf0a02090a0e060f0913050c061c0e0f030a092c060105031e010306060e0a0b011d040e0312070906080f0f090c031507020d030b0a0b0f19031a 62
    0x4407034040000c11040c030854400d15080100100403103020245140814040316044419400e2a5658441130040c04400d101004801d101940e04914084803142014070011403508440b102e10368818042ea4548400d0104100340c855a80969540d6a40e0000041541c03449000f01c511050503030312017030142640d0890010700000b0014544000b42d60741d00c01510380d9080240b50403403810b0130294484a040c1c88000b2280614414800000e12908104600a5241c0018125240e175441c01401c8039050fa0000c1410780d03054441551840601881c1000c030780a0038100080000c10701c03001c01c3c0940109070820003d441130149a03115211a543c40030f0840795020165800020402e0400209244003013180d982a4401e03046000c07030b00b424000c44003003481c01580e07140c039a4332440903c080c88020365040c849504901403525090110203050000207402e41e100388a422400240082c1d0200b01410103c2038842903c1420143c100041c0c0c03540001e0042c01c003800d043c2003a80c80b4004403100e01d00d088008070b84 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 590595125 1250 590593875 590593879
    0x5040b030307022b0f0b1603090b0a0c0c0b0406091a0c0f070c030819090f0303090504090201022b030f140403031a0d03090503070b030912030406180b0f0a0209 70
    0x841c0c0c1c0f0a9058501d4810001e1080c075030307404c0024103050003180080e10480318113407284085001d81e01c0c10740003100925030310744c141e10101420b1902c003d01240d11003050942280f03146c0e0f0b000481e912000703402d03104844031004c01800b101c251010070092100560000108074040c00d14400c1c880d001c2c040d2542d0240c01101c5048189500b030282c680035401d1000034002c058800d1801341c07016512521020702c0b580120712440d0b1048160310900b4204e90744090404018071454a000304100e0442e03030060403403c0e8600a4034003855880c61058150b80c420030646a0184c010218000700c6501d4180c003581298007101c0100c042410500d0f00c52460781ca921480507104520004010585c6a075035044014140d80c400d07400000074414200411582c40d0307607902e0502403081c1c40d4405050300d42800c3c1801c007041607204081070300c800d104101d0018004a0000041e24854000d40c0c0c0d40d60326480c00d84003c00c00e49102c002c0322910001800c0c20000f40d455041d010345401c2600c0c10070343c0e81f4050300001b41c0c400d4640450f = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 590596375 1250 590595125 590595139
    0x9120304050303040b040507050a1403010e1609050a0f05070f020c1e100c050601080a210203030c0c070f060e0118063c05070b0f060105040506161a0105040b03030702 73
    0x2034046003e05c0341960b0440c2c411010b83d0b0041d43e0306d60014941604940041e003030403503840c412102a00c3c0c02d2150304480e0041078040e100e854034144164000210511803031248a4a43c00000c2d0f98171502e510171800204040c0c010001c0c0e0418080080c02014110881c401500ca4160011100e01e0f0495040001b901c004c4c03000c5220403a64401e00c07140440c3d0036440001c0c07140740149080041c5050100c4c03406000b60000400394131005003000d00501e14000ca074020094007141e20205015404800c03240d00c845405c280c10395854400c48044d1070004070ba480b00c07900d840c100402151090340a520140840400d0742c880c0d400d02c01d0782c4a1400d03441414030980d00450800c40740001e06003000c5409009141c0c240c84441d2800000303908503060000d0041c2100001800001d1040801240300c00d84c82e00144480e42c522010b2030408e00203006840350380140340c070035400403c0c0603d5051100f030010041942c03250310002396205c4a01d240311000000c0c050540720340c2c1407001d03100380340c00c000058580c043d8004101c1 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 590597625 1250 590596375 590596381
    0x3030e0d0516120302090a03120e0402121b0c060109060501090510120f0b03010e0610060228140a060501090e0a0b0610020705031501090f0501060203090108150d0b09120304050303 79
    0x584041c0f040f102d00b00180364081c04160050f46e01c04406c0801140102103006a14007003640092641d00b540800703a224601c1800203040032440c2224141c0e01c10362507284d071050850004401c0056014455200f5558842e01c000030410791816000ba8040390802c3c0c0302c12034210b480f04200041c40c82c4075105500050200414030306040e4482d0412010016803910018091b4803000c0405c2c2500c4ca600c0c0e01d0301e4194092400c2c450710620000c02c0c00d00030b000920203809040d60081e00042011402049000fa10300f10360442402c1c48032600c0f051000100da04225004c10b12540340c458041c010910030003080515011000c081010046102070449a000e40c038071025582e88000c0050b0785441605040851003101c40101e00c5450402120301c2900b007884403850258034040d1070000b52145840100200703400e26004012698000041c0c0b003904809003001002a91001000d14600c0042c1c1d211592145028005030b042c0a8801e46441c052141941503c2908030720007404d1a180c4416100206203074410000 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 590598875 1250 590597625 590597633
    0x10c030c0306050d0b150613180603020306070f14181318080d0612051005090a020904030f030f0204090f05090303010b030f070903060212070f0e03030322050a03030e0d0516 76
    0xa0305c0e5011150000c5220321401010100c0c055412007400d40e0b41001d9000000e00040018200981001c2220082408002d040da8086038407820060003100c117001040d040b00000602440283e82c049510312541500c5480240d0004030585101942c0740c014002c500da0100303145158000d01c008040600c0c4c0e0001344903400da590240c0c551012791180c02881c2c0d58400030401d600512104000e441c0a04003d000c038401c41d90400d02116000340566400b5030002d034060740142c030703000c03d01036000d601030074032100c032441c000400d40107405880341c003401840c80043d0204040038560300054105070658000c000590b01d4104450b5244800e00400d00100c40a00000e605000c880e50351a0340141c49143c107005540d0783c0d42c1e0300b00503a0003503211003242c01c0120040025841c1c1c000c40c100f12140c103518007001401c2513103022039120700c005800f50718840034203085524400444240c40712680d50000498403603204505006000b020302c40c000d60014096804c807006a80d101c0d00c1560380c40c5100101c401c0c400540ca0fa1 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 590600125 1250 590598875 590598893
    0x6090714091c050a030816020604030e03100509160f0503100b06040806280b0d0b0703060509040c080c0901030818011202030f1911070210020717010c030c0306050d 72
    0xc0415400312100c0000e810b20190810340c115020300c03450041c210826a0b140180400b1002803100303544d11090025410800d600042e40c582154240c2801d86104071060080303814280c5031081c5101d02c0d030914041c0001c1d9580011a030050303144441110201e952119940c10220788148035450f41a030010a000040340c8041d80030700c4600000a0601c2c1c6401d648010300b900380642295541d285410f40204100c0f8441009a034020b2110b00c0b003420040441d90b000081d41e00e00c410741c00a88101e40110026050780c0c041e5000c8005810003c5c031107262484e19140000000303146002d0b240c001e0244c1c1d40c0359400d0f414240e15450681c0c0e844413940f424500d800303a2100e402080340b8040340c100160b10103980c0b0220f280703200940c00381d24681e5034224580341c65072400c20707503142c909460380c03000380703030401003c0b1941e044000d460103258110342c6515a00d00616040303143c0350003078100142c045c0b8100300502200005600072601d4000c00c0e2810f0103c20075901e0254120b81d001c0c4107554010b15044451400162491 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 590601375 1250 590600125 590600137
    0x100b030411010807032009180c0403150605011d040209060c06060f030c0109090f110f0d0506010503240a0e090f0c090105090c0c100e0a0b0c130b0705030d2306090714 73
    0xb51123600616142c2203007416020f01920000c41003000001c0600c18811140e60065201ca444c20052180324900710008081c0340c601c210401c4040e61045a2038184e5940f50111030780204024013264a803500751550580301c1ca0117444240c440c100f02010400c40f4100403070000e5030fa0030141c40340c40d42113242c100f035a40941a01000301d44c2e07060307941000d415516040009805c6110f800a482e40d1245c0c4684154000c581000c2c0496050050500c10441a40741e00344090401d290085000c0380e4410350400407543c40303034030b541003210040e00c15410020250000915043c200400d181121403a000c500240101c07400217000e4550010301001c000303620000910002c100200c90841181c0d0300c540c60085140c2168500d00011125420680c92181800340009181e9084403400c548585020303611075600f406400a4407803080c0d924404101403007400014070070f8840d20585800c05002c0d00100c1c00c142180f0143c610604900500c0d00e8010880f941056100b440c071480c115241c015092166201100c51a0851 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 590602625 1250 590601375 590601379
    0x11a0a08060c1605240a0f2013080601090213140f2803050f010f0612032304090902040608030c07060e03070302182203050d05100b030411010807032009 67
    0x2041d01010344103600c0e1602c3c1c101d0200007402513807504046101b20280c90208240603041420030b403554074120044114490031f0642d40c5100c41c2e50f103130514032110301c20100b03600001550144c0400040c400d69140c00904400513606407040712151103034111070406003482c9941e500100c3c600c00091042c10a603400303c013005841107408084c00e81d9400d00d075040306002c0d00110f60315004051141c60034a000d01030300012864414082c080b4500b0b1941d122026281518040c00b0000408110759203101011000201d8100800010340e0300c6c0e40301d40c03014000e0b00e60f03070804030302403440d0142c0010981300c0030090b580300b25847c001a0160a1424108a07482c03a00c002415906010743c140000059640e04013007015441030900140d0340785010a0412107401007440501003a0100d0780c81034000a50280895418801c0c41300c0000f42d03602c0b0f000080c1da618800c0c3c1c0100c0403089002041c8000e1000c0c20b6803040000703509030b8981c549903568000480982d0a6802c4017042c0381c08003c8840f07520f80c2e010025144c04040 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 590603875 1250 590602625 590602633
    0x21080715090b01050a1406030c04170a030f05040b12060f04020d0608190807240c021b040b03030405130209030a03180501031406060a03060305011a0a08060c1605 71
    0x2500da00c900403408094803034034155079446072020000c00c420000d00604003124010645403800b01c103010303c09801d2015a110340400000159207284120507140600b8040320450f01c9480c0c0d442d00541d0365803402c8000c5d008564031076100c503056031041080f20107070f40a0010031818003030780071091294500003400c41648480640f030000015107407071010b04071001c58040c2c0030440915004c0054100008280c10074441061010030f0008105524105c84500da0b1004541d14a501050b480004002c0142c10108942e8217104240d50000c2d80010b00c1315460b5400921040d40445503800c12040342c50041c581505900300f40810001484c00f80003620540c84000c9000d480c00e840e000000f820300c804400102e001c0380c0880101000c80c000b00142c40041d0500782820840c0800185038030b000308100821051060000041c0d0015481c825004203009543c80310007032100d21414504c034158015a91003081c00384589403000100803500141d400d00130b03002c1c002c01e07030b01c0c040700400300b4611007614000903552446 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 590605125 1250 590603875 590603887
    0x60509040f09200a12080a0f020712030309050c1207140301020f0417150c03040b041b0b04060327020f010908030c060412050703200a0602030108060615042108 70
    0x40c409a002590440d415190441030b600100f00004c00c01c881c1c009402e450415500034001484407812103065403000d06049032001080c04c012860298640c00c04d9142441949002c400c140c1c140e00040082e9110f14250340d40c64040b503007400f6401d18642c011240a40c841c00041160032420440c0c4003e0302000790002d440c1003072440301600d45501a9000c00020501c829901504440a0007001e4a81080e400401140d0511460700002c03400007078400340058070407101240030403c50420800d8410486030f2000c056a95450000c0310380d41041c03003800c000c2400c1c1030b1480402c04901c00021054a0400ca00d28010900c1c1d8082c00860740725103590906000003000007042d40340042010348410b2030b0b8031008010034509450185011184a590703001440030900c60403000941101c00c5004100014080428400040710b401d0310700003030340c0c03c0503060900c008004102102c01241d042d01c10300003a1403170740c0341482c40c00ca9081c2501c250311403c0380d07801c40490b4401c0080b0b242d112844040303000307081c0b03a41402 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 590606375 1250 590605125 590605133
    0x150a140702070b0d060b0f0c0616080115030b0d050d021903020715030603050319181d090309040c02210307050a0819050a0b09090606060d0e10060605040e0a0204060509040f09 77
    0x350045981d03004601c400b00c2d02641101d401c10a081d4040030701500100d2261052b0070240440d10107002d4603540e80025038424140900c29401640742d10b07401020249500001c0c100680c039004041c0035540140200968508150380440441e0492945a4003c001c40707403070040c012451038182d580c28030825440760000000f02d5000c001500070401c6058080c0205010b0b0000581399106403030180010700d0503044200400c42d801c901c14541c0c45500500694255500b400180c1544508407140c0c0d0300500e0040c00e03401e4580e0000360380300300ca01814954980d140c1101841030141c00110b850000041e41040100212442020010b410030340c80d21200d00503040500c80340d0280c40e0202c0d44200c3c010794503001c08078246480d1b00d002d034008080d02e01500c135034142940881ca0621a100c0300845498075080c2504610b1004c0100f42c4400200a000b008007680b01d040091955025100f0000d00186201c08900d150005100711070440b503007070311054502102e180c1800090483d12a16012079aa2050814081 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 590607625 1250 590606375 590606377
    0xc06070b18060603330f0718050109030305030402030c1306091d190f050a0818040608191b0305010203062701030308130c140a0e160c0c08150a140702070b0d060b 71
    0x100c0e002c1c401e200b064a45407d0003041409035048030b581c1050740120411441c0d80100a05c3c080c0e0390585401a1740e980c5d10f0000c0b904c0e20840c890515003101800b000340907034224a60118003502c585003c1481011003003c02c660020241c07400c000b110380c001c0d194020076a84410341c0201c0f13040c4921405c12014503161106802e0600d1500d0503103060318005520609480d19036001029828202d90422545003030402880d07455100e03207802405081000700104c2800f2a640540607140051466412030580b03a2030a80c2c041e40055641c14010403900240410201c455841031640c3c0d20000760409070350303203107490841d03003100c015144020b0812035541d0352010030b851100c960003420042494020f00e04079402401710b03c0d58164000c0400803901000d000b400e100745c1c610600400c030f140c540030360141c5080c10003403d1041190300c000e10610404103800060028006070b036124240c00036080003154041448084080d80c2181ca0400581084c081482040ca500700079000c50003e0300c000180c696140d6141e4906 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 590608875 1250 590607625 590607631
    0x90c0b0a03093e0109170c041401030f080d11070f0203060c0c031606020906030106020a023f0309100e030d1107170c06070b1806060333 60
    0xc0d481d01c91900500c5440d066001110409212208070900b000c003010110fa0700c4407400304409094082d214040340c3c400c50700a000340001d1000c0c1c00000520074001c1d0394030103010641e14059805c1203500803c04504410381d43c101c80d003140c07010801d5032a0341d640259582c01580c070171002c02e80c0c3d40c00020500c042180982100ca124000f1080030200c0d03801003500d495001040140480750070416000c0c000ca02000391541c50707600c40030308414444c080c5441300c040d0149107a00c40d04103a01000002d02039070300050300484e06000f900c0e08401002404071411000810f20561684070f45000a03042c080d0781d441000c3c1c00c0c0305800c0d405484c10030180d1000902c65103009045000011010f202040d05403609019450040a072400c0004400c0c0c9d0380340a058480c4a0741c4200084c17922983c1a140b0b000c4020300c400001080002e0480c0d80d10901803810620016064603280700516040c0c038081140000007039494000c2d4030040003070080071554089c454030450010405601c0078514081c84003c515100300040c0 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 590610125 1250 590608875 590608877
    0x5070302040306020c1005010b090d030c11090c0a08090a0c05090a1d031215150f07061803110a030206010b1303050d0e100201061d1503101509140a090c0b0a 69
    0x86c04080742ea91400c3c2c82068106078003038501005100c0701590781d204500030050745402e015500c81d40f40d041c00030b400740040851580124807002044100340849004004070030f410303120314009450b04907211382d4541404400400304030034050240058500300034050b501401201003c20605202c80e0b5841a4a2004841c845980c1c00030070f5078030b0414448138620b0360080c140c42c0c121544001220006e41600c00c0000c203402158000141c4481ca091514100c07454940c0001d000d0140c0c802c0d0100201d012440078a0580004455407032643c11000d0200d0100b40b01034041d8000d0040e6424001c02218947c0841c41c108a042c1000c0d1000000070f0003031015020040c86526803030031140348041400080c4401030024000c5900d44081846010011103120111044800310750b50965218440e010300212044182689071081912494500216402c0b048070000c0117010380b025141d450882c402910301418602203484444030000b11104078681c802c41f03150303010b03021554000d5a00e40360000b5950000100074 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 590611375 1250 590610125 590610133
    0x30509010f09030207210b1305030c030301030c0e281a0406140906060301031203051503190311340e0103060e06010510020a0201030c09081203010f0905090304060305070302040306020c 81
    0x9580305500031034414881d0baa80110403a9661f0b0b590340d4082d0004001011000b2000380e400c0078800100191103201042804032aa04e507164101641c0c01c1803203100b150f13040399042e00003d90011603080443c6080c2c90381e91001c0a111210000d100151034994507500000251100034243d5980381d0080b0f40081c00110601c20000441c0e40a11428a0004103420b000320f01c104010030006200c0000e0040b151414a4000ba850f25043c0307a80d01c901d100c40354601d6041c480c3d0502190700f00a00d1890551403486600e4040040f1301c0f4146161f00c509820242c000e0981000001400440c2204841070550310281d0a140c01d040d19a54481c03640c8000b17800c1a54080d5456402d49001a4104906400740c00304503500301803041d100c03400a6031404003900080c10551140c006240300303400790350703c1409440500c1c00c0d038015060150001000750002d11841d01c2c2c2c0101d030400044c154155100c1d080c094a5907030301a5203000d041120940180c04040d003075400b0503508010000c00f05291344050a9011440c002030 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 590612625 1250 590611375 590611379
    0x30a0309030509040218040b040b130902010507150c2a021309061503060b04050103020a0311030f010608010905160602120307021c320d09020607020603040b010f060f020d030509010f09030207 84
    0xb200498202c0d10723405003d14501100003a95030340301600e10088441c00f800102d002d688900c012100e900680c1c034001c01c0041c1e80039035901c0300031aa41103415024665520000c3d0781d05089006020302c1f20a000600c07101150303210401c0503040903004038421045055000c2116245541c0d4002207404034140c4110b9109800014010004030340240442c01d801141c0500031b65066800190146020b4880100b007911010314145103038074240506c0a00c4a1540020030626036148680c0703010740081e0030111205e010320850031041c0e4440e280c800341629150b60040074810501d02d007054070381c0c0c4050280000e510035041c0c1003055804585030382090800c0d698035000032400b4054094100b0355410f092032b802d48405c9448842c415504030541c0c080c2c409144011601c03201500108190f486a8200030350031180000c1000305000c40c071620300c0d040f91000100c1d040026540c2c94100d41c0c3c890386807030800c0181c101021041d410f6120750402600310401200004414010001400468450000c100c0158100e1501 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 590613875 1250 590612625 590612629
    0x1201031101020d090b0301090e1c08150a0f170703062307030b280504050a09020a05030d171b0309060412020109050c0d170c1b0f03030a0309030509040218 68
    0x21840f20a440c107040c0d5100d814401ca01080340030500070b030070000c0d0f6100b08400b036180c800c12810b00c1800400c400320b00f02c2c00c2c40c1c0e400103100000072140a00c240c0040300080b0a80d04150700208111024a030100d1309190900c1403881034003130501c0160000b481542c10200101e04240300740c00e80d5818000864200f1809640ba00003a002d0080484c024140741c020500d400ea1a0f41d90310440180c0c0c60309610103e220702d42c420010351100c6812203034000d481c1004220711650203a100c0d00803203001b01c41031401ca81e501c20170582e40d0b00c40d05081000213810203080ca51500b501b00d0500d81c2040c46914454404220395000c0c480640045505950303c0d44141c0c00d1100744440441040d040c903c0340e2000348880344160b01ea072036075880d0a60180703000d1031214848a00344035212002504154150243c01d50b91340c4054552941d8514944000c0b1a02d01c524001c914140340c800c00c0e0901c8035002801031820700841c2e641c10b40c01404116400c0d024460308012900b0141d88510080c04481841d400c0305002070344002c1 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 590615125 1250 590613875 590613883
    0x80402040b0405151324050f09060312090d020607060515090c12041106040f0305070503031215010905100203121803041a04030f030503060306070c0206090114120103110102 76
    0x20042d029a15000500400d85402807465a0a400603140300300c00b0005a50300300000c1000250048403119006000f00d1040318401c090003c0b11812204410000c1190080000c2038a05840c3c140c1e2580c080314868413003007540c0380502038505000380340f070005100540100e001ca5115074002ca8106660710f0030801100300b0348100040400058424428510303103c11040705a105000c0d80b82385201c03d4100090421020090501c0c1000e00580304907115691044402171050480c0000c8515010341c140204040c1400401e843c0d0000754803080c07000036110b0440a036840340403540450704101c4d021501091a89503110100c0c0d82c051035038021aa40c003092010000c0021010303000314914000e00440c40c54500300081920241c4000c910b0340c02c0031010425081510f40303d294001802c0d9156400c01038103042d001000345100700019025039035146e0f1000c1c0110b4001c000090020360007042403050f0166035205030301261000701140300e480d1528203a2503400a01c0d2109901c100d59591041002c5441568180 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 590616375 1250 590615125 590615141
    0x3021e041508030f0706150b03040b2a0a030e0625170619080f0d080906130314040e01090b040b091e04030e06070302010e07061107180204031208040204 67
    0xe10381c00807960404410903200d00c580d01c010302402901089160074089158007800c00ca910b21110348942507910b40819105810072038081c0d44280f0f41c440014440e10203207080801d6181c42441501366800d070300c561f82c561600400112010543c2d5042c5000c040042000321902401640440e1301010070704070304441c0c0d00809501c1c044100b000c406001c446811091601c0358110500702d0751351880c00240c0341c07407081d012081e6229004030710640700d0200b821400844d00744c039180303020381c0d030318015950b8248035940c0c8a0301590000e8000c04121030702800700340b086901c592080098403072149065a11106075420010a820152030705503600c3c0704111515080c8158140341c082907460841e103241072170380c3ea050701410103840c0e4028901100028101446a01070284282004001e41d07110300c034070b0034000e0080c40781c440d0035010b52203100c801298050248200c1681c0035041c1008040190505452602c880c52080814220f031b07400388400300002c3e81c845240c2d420011996038424607440d26004000c244d80c544 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 590617625 1250 590616375 590616401
    0x29040209060405040e160e0708060901050d03122c010c03180609080d110d06080f0d20070b0304060501050f090f040311030c0f070e010b12070903021e04 67
    0x4000320344054403810305840032607000700c400081328015000e00c141820610101c044042803200804a00b04021f00c1e0194000e006d141d555986642d50304d020300c5a00c90013070062039480080712042d0b0002034412400102141d00381c0714017188150740c01c03e005801c919540782200c001e040c840a8501401c4091151022856003454140914403d503400c00b60402c14000014000350b403524840814407003503600b261000c9181d69805c004100d40b00b9001d00e260f400031a1901d100c54113007840040e04460000301c8030b4880d90400050030300106051015900c21004c000f690b9191074440c222400032040500400340100244440e195580c501850103500b11103050300124418003644076502d40d90748801e1000c607405041a002c0c5a08d5459504003500c080c031803c440d210040c48000b43c003041000010035a082851014012944180e844640f024005103003405111075110041c07003c00e141071942c0301100d401001d141001c2504588a4000c5a500d62140040150100300d07000074401c0c6040500c1211022000 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 590618875 1250 590617625 590617627
    0x905090c0328150b03010905060d03050a0e0a0b04060203030f1807030f0201030b040e030a0320090f010c0c0e0f010603090b06040c200106050306160f140706290402 72
    0x1c01110b0b1401142c0301410748a071011510310145400c0d9680c0300e0f400c1e03014200e1001c3c81903507944030782d9034682e03000b402001c04983c140000301e5110305102b823120210582c580ca881e4246903441d4004c554103248540d5913603024850101c00101d1461190042001e0201680950b40d01e14005400d0345e40c03507201600300a290120030400c0145188041000002d490348058044e04140345800104d010b03010019186a00c07038a408508691014004002c00e90040340703440610800c21555800c081d15080e41c034a001c01070000b0001410302d46003020601119130014103201c09004a035886c0c4440080e425000411840c008009015079541da000940b801004540780901c041400b80ea910090307884003503c8103004940750300d1002d0010703014810702003080181412581d981081089240d010380321521895000b070140c2c002017174a000007000d8908006140e5200d117844045a060201e5001c28001c0e00c000040b030042c0407280c001007041c020f40b1801260072222070f0b0520354058542244155130b00b10184200c1c8 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 590620125 1250 590618875 590618881
    0x60308071a0106021c0e0918010e070617070201020c060405010f1b051801120c1d0103050105061b01090f06150906140f04020403170403060f180f0609120905090c03 72
    0x290008600900c1e1781424aa120f14076030f800402e03104040203140b2194810100c070304004c000405011070040102c2e181b8001c1c450542c0d00c188150321002e07603006120000f10300200c41c270920229600e629403c003032103100051828280454141c1400d500761422111a51210000805400e290240041b16000030065040d00201c040c40508640310341390810f0750b8980100e041c00030f66801601218141400c0100070f01c50030306d40240c01015104e90300020b084200c07407160f00418a510070311881e4103aa2020740700610302804240380701120003035114280c0e581e40d2901a6240050820002c80f0001032182e14082070b84000c40c0c0c0c1005036501540c1080341890329013002040302c55907000026545542c103a50703450003111201c0c0460040d2140d90006070541941c0398030992911800d40092088a0007090108140280c0c010b040061701ca80c041e86100e0a0341c0c10b03050402007419414412801c40c0706850004003c10b103551ba5401c021400387c140300c0400c031820740800c41e5040035030000b0790160b00e04036140c0c6540b03 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 590621375 1250 590620125 590620127
    0x708070f0b2401050324060f070302010609090c03024c110c0d032c0901060509090621010507050406030e0601030b07050702210a0204060b0c1f090204060308071a0106 73
    0xc003008103075000c1811596415030f079000b08240d1810821b90082c104c00d0796900c11510700d070742650140c03408400541c45d03c40001181c0b100ba01c2000c08441d0700041e603a89403031641e0200300719402d92039940b800e8030009200508505031505d1298000c04404220494508001d820b10024811a81844400d0080400300400138910205401c0c403020000c80f44c95005030114102281c4190082260303c031440000342c41c442d181c0c4221b01c58481c91900c12a0204141d03030703c41c01c048880f0f004080c00d40e5000a41d0101281c12490710b88004084019000d015800c081c02c040415400c3d01c009542840c04120006020300495130325019040c0103098180041000c2d504d10b1761901082d2900520072010004d02040e03907801c540c0c1e0016400200c0d8540c000d043e82c0c050070306005070746480850710120301c01c529040c1c00203480380100c1d0a952090b003060020b8071202e0401c0c5044800f014840d12a40c11141d41e40342d4000c01030f0b403180b20301c0e8040c1d40610011078443c4010f1a04030781c03900c441c11080b40c4c600f42c502c0040001e2 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 590622625 1250 590621375 590621377
    0x30606170117030c030c0105040204061203020619110d0605010201051b070b06040b0904050d0f0804030e010804050c0406140f0f06031506041a1c110f0708070f0b240105 74
    0x403901c002c0c5455075010300701039841c02c500442c0c01d4070110b4000000d8803400050150001406607008840411131203070340f41025a113101100d80d008001da007020300069114110a080c0900d2440000c1c00800c0c00001c121210200368010112a2903060780c074801400a56424031440e41d1144620000c2060040d00b030b818048280035030701c2c00602d00102c1800240650f141c0d07800000222030041d00c2c03003441d41850301c0d24a84485080c4401c1d800a81c440d20310500301481742100c1401281c00d51200c48455400c0401103559000c000c1058615105140c1441845d031a00e22074030f03000f840b12101003440d50410320308020302054401080c501c03ea4610002010681e42d15084903007003d40c09284072100400280454a07038002d0b40d104c0c0401501d071643c61000183c042000308410b12441a01c480141c602101c04000c44440c0880c90402c60030a0203020346608014000344050b90042003094107080899840c500450403940080714145280c00502018000d200c40e908840c4251400401d03e041d480300000f091 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 590623875 1250 590622625 590622629
    0x10501050702040908070c030b0103050c0f011718031815040b120a0b0402030c0301031e05061302210a0c14060d0504141b2b0807140a0c060306061701 66
    0x3c1981d550300360030100b000384400c07594003076072015441d880345a40e81452412210241f10070b45070380c012001011701602e0104050100b9500584481700e80162448143c0380d41c040081505c07440f82108061194104e00810251460907044c19032181c001d4200c5d01442800e107001581e030b140c11b0000f800103101001500060310100310341b4480150413a0740b41c0c180107000d0100840754030780042c03001051000d220f0a000044d81a030f4081d0440c044603480c0d0740c041c031004030ba0014015000380c000601080c000103003000e4000d5440e00046c03481e5198201100b410000001d0340d640c034017869210b60441010001040c030600010004049540004140321020800c4c40c400d01c2c2c11032480c075a031400014204404001401a40c2c02801c0072510009040a00c000a2245068840f4481d00710070110240e400d03403100f00c407070010004800c58807980629a8560455801c8040c04a942480c0c040c070412032040e0402092890500400158420300d14040d0040c04590482d000030041001001115100d0503443e0b40700b42c1 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 590625125 1250 590623875 590623879
    0xb0403080307111c0305010504050c03040510021e0d0603020906030f06191e090c050d1505090106030212030910080106020309010f03020c030a180906030218090a08160b0f010501050702 81
    0xf000800806146003044402d500c031683c0c1c16140144019030f16130541c8013505031803054504100680350b44018a46d2400104c0e00280b82e61321901e80c44001d600c6a8014003868545c0640e4104042c00c582107201c4960000340000942d035507250020015850884281500071a080e006800001c460b007401075140c2c1001004818107401c0711910301070081d00d99000107107910018072404c2c0480000000880a801d03c840d060700c0300316040c803001ca0145400c4180c0805190b02c0405511101929500130018041c0180035480556a0300c4001025868403440791a0700a00740e0050f564404d2a502089600c561440f0b201d0100f042940c014003c06400000b103841c41102400c1040d90910700390710850203071282d0300d510211800041441501c1070b03000207100041c0000c00c403100340b1817629081d0b04000c4444510000e9803100144a20b010228402600c1580040c080411b4030300250440d1202ca681d42d0055204816141400048105205040d005190810b4007841c40c00010b500d088002040c5024402000e4 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 590626375 1250 590625125 590625137
    0x4020f0406032f0a0905010509030a0f0807020307030326040c0e04020307091d121905071a0c120f01180c02011e02090a0e040f3504050a0b0403080307 66
    0x110700c8404a00300300c51400c18000d043e803000c80c8888140031503420540150000c0f580c0d202d80452103600071000d6917141a0060010305814002ea01ca19810f1108940d0696483d10700700300340005030b102880038038040c500039140c9800820400940062261035094441d11500c501ea003400001950f186c85e00d021202c03048188401500d45000090500050f03500981420b4a030000030790300801c000118020b012131000c107803900d00703030301d840140c1e164030a440100507400904000949280e0043c000782102c640580040c00124507171600e2851203010907500700f059020b0220b0040d84440740001400e501c10401d10b00f40c0c605500d80440351801e003000e090340d001310075218440103003218400d501101c4001e40d00d03041c0061482120001000030b41c0480c420500424600d440403a4420407003005901403075201003590b00f01221030b100c60742d0600d280c2254030203020064480d02c11401000c2071100381c0003150300300c0316580c0345400100700d1005200d50001c81c803440e040c4020000300e0210420b403a4043d0440c1405 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 590627625 1250 590626375 590626391
    0x60807020c0d030e030708060c040510120e0c041119050f070515010303020610061b020439030e1009060b090c0408010b01050304051e0c1e03010b04020f040603 70
    0xd90502480340e03a40c0b500000e003210000d0516601800788507160506400f5036494545510308162200402c0702c441c40c6100b0100802c01c01401d1801c035511440070360b4540241d004284120040c103950441003803071038030b40c00300250091500d403d00c1349207140194859050320700b1120b0180c8052190b020072622040c01000315072601103051003000c441ca29640502038900341d0382101d50610a000081c0001d84c0148214400120681441020003081d240c05442d40101e4200d005043c0385c107400842e1080360007685401c00103075218043d400750110910130381c42a210401004104810000c4660407043c02c0608120811981690204000a00c1e0411100105002903941003100113000682a02504000d2000030480e00c0082d14010780b003070b1000c0b80000d020701030b84000116080d0006842c05071058004102c000c1d03c040d24020f0420444461320107450700384a0603400243ca03055070b840700f10b0480003d41c00c203801340e10302807290700d4502008503000c60a003103440d011800c040c0614000d50003415650001 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 590628875 1250 590627625 590627627
    0x20d03180521010b06030f011a1c0b101b060209030c060a02060a050a0903050f220803130510140c030702040911031b090a0b04021b07210804060807 65
    0x250805888054001c442c909410103203200710540581c5041c082c0d510304401e1841c03503e050300840f4003800100409151a03400e100c60400400500480c4001c0a0010040d141903085598601401760302e401754002010b95840007405490340e440e4246104101640d140110440902607205050640003140140c640c60202c012a1401180a20b082c0d40020085010111070342c3c001401807103400d0303484040c42261a40b05518041d40d40c03a92006000c1441881500225540300c00584400c100c441c1119405040d0550501485042500078552035000043c07a15001c1c0012001d840091005941c1a544172612060041480c83c0090110303249140000d503050241030b040094401c220380042c41000700b404c483c54251245038515005e10302078024102c403681c00c988001d1400c41c2d4004054003a00c0169980201e2100411500c3c640550096003440060b02004110290085645008005101d042c0c18001d05440410720301c4c031620704d5009941e0122001411000654040300c1c00c60070000100d4a0380e8034 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 590630125 1250 590628875 590628917
    0x1c05041a04150f2304031101020712050334030e03120a090f0c060315050d120503060a030c030b091c0c0219090f060302040b0f090f070c2913020d03 65
    0x311204103e21084820801c1d03054405130240264880d444080490240074035503030a1307004000020740a800d06008900b415800390f0004c69014000104880309014010040715417800b030310303401c203e103201c048280400c1141c141c426514911612801903040100c0420304214840c402000041c0d217540b0340c0388140412001b082c41418007940902d00d103051031b882e50030081c018104c0b40055662a039001c8800900c3e414090f029009d2a90803100d45614203003a58010f80d81c9504c05885960001010340d000400b040400b0710503130180d482000d40317000b00e00307058104900e04000c2002240c2c191000124542c40d0980000ea0b0742d03010341d4140d90485071945004a6058120219400143c40508040030503d9628240c0c1c0400c0a5a200300e508100b4050032000303100c401c1020005441d040656400407902c04004170410f141e004805191034148154a5601c0c01003034104200881065000300400b61b0b4100c10300c00445510811702c0b40c5404000c1e50b241c0004410103405800601440f5108520880b0382400320 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 590631375 1250 590630125 590630141
    0x60c081603060f0506131703090a0b0403050d3b0a060807120f06050d03050d0e060601121d1f060503030702011202181203040317030105150f1c05041a04150f 69
    0x2d21912404100c00c1207c580f2a444150003600c1b0311350342c00c40421200700c41825641543d030020300410000005200550303620400c003411744418034421070606140381c81c10001680c4214006020700b2220a030382d0610005030025003181c0c00740040b010801184507444100014984102d8101182668a64000c08020b02460b0001600000e50840d00c03c02c0c917420100a1840801c221347c20001c0c1604200c4d591348407282034503041d000074184a140d00d1100e003180c0040e0b02e001e40c5030490280029000c100030b8034010700d40104500495200000c8009800c50b489082c00600d029000341d4504040c035400286804564940142d0f07880c1d0119440030b94001281c1c6a1072200c3c0003420a50141414003d186d64a800c43d220441c0d010141c2103a0120440c0710000740c0b03041b02c8005d1300c20301550908a0803411250041845440040c4c01800304940c0c81a807a1410040119006400030740742c01e090500f89015030a501100c0c441440141c1440001244c101c2c801e5000c211401002811008045190010380954 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 590632625 1250 590631375 590631389
    0x2030105150112060b09040b0301020f0a080103050709020a050304020d0f170c19050c0f060708210604180222020f0a180f03030503060409060c081603060f050613 71
    0x10410a0150285200c24074084098941410303070400319818209481d070780c2c004c076540d0341400d10690701e0354107054001b680a1100100094201101402804800d800452212000612100040003440803d00841e0040c0c1400f5105502e043d4140358041c02c1480044d20090040c02e00c0c0c01ca0740184001c2122502d01c1c0c2e544100d00140601003603000c148103400450050b4850b00441c0e48401c8a0200e900c40080403e5200006e005110054410081c10361260f03400f2a03045182040b501000410a60003051008442400f1502584402554005060009006038040c502d00101e4407603080805600040050341112501c1001103c1a003503013090b10111441c62030180007140d40b05002282002a105902c80d6550704082c0031400c20040700112118800c01710b80e0740c003884007400807a2040c00150350000d0040c0000c00c56051030b640310400c0307600f098400000200b8203000e11807214000369500501c8086072905200050a042c8012074542d00c500c1102e100301400036603110901045134941c0700920309 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 590633875 1250 590632625 590632631
    0x201120b040203091b0a0e13080909040827090a090501020d15051005160303020906070f03120614030c0f1503160906050414090709050a0609030201030501080a020d0209070309020301 80
    0x701d04c0c903c59031079210171100d0009526440c54415070f4200140040704540282510310995110300101d4403500d02605029103803210704100841d016191300310700301d0003207204100c6503a0796404110600309082c41a0b8521981c035030f080e842d5107181e65802042c036030006003c2400040d0141c051504500a2048170901c0b41d5803400d000e2182d10481c00c6840d008100c0b8000d480d501c04d1000e440c3d00441d40c41c8145603c00601e0102c0d140000d012a00c240e0181c40c2146d000b40c0244c1c90504207403a4886041d0302a502180013504041060380c140f50140070b000024640407005941301100e081c00203407200307038400f0424082c0e000300c164402e482e0741d40e4061400ca501040310341035407410103006e503000010b61007407038101140141c2c0d4001440c92160080741e04030386d084041400c004078171408101c4100d80c054600c0040107102200412281d884d455100020001c64665044551852001406840e0164001100c9400040090005d6103a40d60b0384510107904880c150380c3c1d541d85000a40040c202d500c0003070b404d50f07e = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 590635125 1250 590633875 590633881
    0x70c060f120c0207210b1b12040f050a060f1802031c02011509050627040f020d12020c03010f0614041e0c0512060301022b06210c0f0b070201120b040203 67
    0x49099004078025004407071006a5030b81f070286a00080d9006181265421400c00081502600c2e554840da04a1300c80e00520801403410f44625141054140c820354405554440965003542e03a489907443c03040014548045000320b68002a480e003400c020909106014903075042c035418130070350003080803d0034804092034458688040034002c0908480781d5000790f111181a59007142c0342c030b40301003112000140001d01680c2d980e070f840950405140040340c00c260000381000000e040e242c04d04242407169401030100010040416003500c180020201c80e00d0b103041420700ca15894242d41052882c800d03180824100240d0b0152a4030209080c90a080c0701d02d05090960010350200003032181d542d0250714880c19443e45001c141c02c030320070481609031000c0380381455140d040f14181c42e0840c400703020b2800512140d850070f182c00c240e61007894500d1034503500707401c7d0000c1103ea10b4007100500b00d00d0010524540c10a010028184104000a414082d84007559480300440350814841c0541c09031040d91281 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 590636375 1250 590635125 590635169
    0x5040804031202210a0309050d232a032203020102010b061602041a0310050f0705120f0c0904110a1d060d05091c05070c060f120c0207 59
    0x6001800102c4100c020909108040e900c000340c2d021241014010603408040c80c00030b1056698804d281407010706444180d04c0c004100207000202000f4001d8486440d440d01411803269004c605c195140342c50203090282c070001c01007000042001b900c445226403601030030300c054240f5600070040f90121603884481e031f500043c104445da80302268800c2c4c00901c050324045040062074001e203008940005540314196015182a4004012805540021071000d12030b1102081c02c00d04120207a506071902ca00170b10504404080d00540e201e151440e20724180038800700c0e1420348100241c03091002900c2100400c071201030002c12140c1d041401041044281d2566005d0403d0ba000106980c01050560070140c690084d00301b500c1c0a07022004040902c0c041003041108020324015124250a01c209040390303680050b050720301000f4141e56240c0c251a100c4a10f04180d4005a41d00807104000141d034210032016000b50207210148880e40000c0b032400207041d0124501600c03680420060148402e46010308 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 590637625 1250 590636375 590636377
    0x50c09040515061c06020d0b0604080706140c2e05190c11030418020706020f0405130c080103151b0e03010606020a02030714030a0501020414010e270910050408 70
    0xa039400146809030b44900c200140021034011040000d04d800e10790100282c00b0764010158207548a1000410381004070104a0b10382154000500a034850320041c010b9640081c808100104d49003001880d0101c10b412164560f88100e082c02e50807501c0503148415400e0304140003103111031a200400003442c1c1240307509282018425031000d01d0340f406040d140e80c0392003803120000c0c5088210046142078a0410381c0a409105e02e020103100369824401580041c0b1140010000c0c03030030340542d0940300c40c203020420940d1003d41084000070340c40c2216003000d49401265483c1101d0b000b0388442002c40181901901911210b266900c0a405c01c502c0c1440503504100b074002c1c0914254001c000b4a134454205981d01c41038410041e600da48080f03010082e41e5801020400c40b0070001d0269840f002440c0c2d100d60a9030000d4000356204964002d00c500b41c1c0d6400740f8424000d80003154026103c0c0d5a900074281c80c0c402088402007403941c0d0b07900188140d40c00b04018250011181d07420006e62805007000081 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 590638875 1250 590637625 590637643
    0x50405330f030d0f050a0302040504110705070501170703051b1b06181b15070b07030f1e0b040213240e011e03060306051306050702210304050c090405 66
    0x840d2400381007a03903082c140002d00340301d015201c2c0c0b0380440700303405480182c4480e0031100220080540030400440c80e0746440c026005403c96441071152102501d103001400c0c12803075041941044680340740000c0c1d00e8002004a904040141000151500c0b4440c0c0645107050403c0400d50142e80003c1c00c3d840240c03084000c611680122065401d9038403070740802010813901402c061165170000c08100004103400f40b1103050343e400103092607041c00c90400b400740360b81c0014100381c0d0610440340c200500c982d01405413110840c103103e010002c00207a8080b084078070488a8400c12110360b9001c0068158640768111116100000c01200310b442c1d507454103001054890f88694043c90302405e0030000540258011340710190b05031901842c0e01c041050540c10a114017500e02c0415032651000004194507125403401010407003c102842105402d018080d100040c00150855021005001c0032118191a00851055580c03182c0d55980b5a03040132071602e041e05070f0041d4001d21002c20b11040160005003019 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 590640125 1250 590638875 590638879
    0x3111309080705100209060a180905070f020105061f231c150302010c0308040302010f0f0b030d080c030601031d060a09021c0507050105030c0d09031d0409080405040533 74
    0x54a5134061103420144c0c06242c02850300060b0900c84450900e0207100803200104d22080304004a50340d038140041995425070308034010a0b0b21642140c2016428001d141c1d0244007070f1054820741841c4a46200514041c0c450b4034100000300c400004150043d04000001908100341d1a4440745d4440d0042121024002c204040c03600d0001841c00c0000078480072422290161503840010b04031f07032029900108010f00840445d561024420000f10042c4140e10004140203400104582c0c800280361074280004400c1060010000410400542c103c2c21254440740c203180c081100e2001c20200d00868071714140740041030140f181000084001607120a103030700e0085442e030501181c0340e501288144950140503006410482003407004d5405100150f40082c40d04410902d40710500039031004680d402c941c100d000a1002c01941280c090b0020100d4200000300d90802c00902c43c0d940e8500e6611547c810035006036150310015401c011080c6c40304080032407508018400310220b1300030a1148944105086c = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 590641375 1250 590640125 590640133
    0x15030d080919080a0e13020c0a02150c0d0e01110601090906050105090c09040908070506040b041b140d02030102070c14090a0c05031503120a020703050c0102030c0703111309080705 79
    0x2a5010200080b40070401e400101c02454640400012540701d66108131083d00220009071458150b50b17148000d1107101500c0c80503081c070b03034103501c10841301c000e036421f0503d5441d2041c400c188200c6030206140d00ca9101c1814910440320806005881c4d184644494640034040e0700f0001881c00881e4000d012801e10440d0f04200c0307030fa00c034010005041010307261441c0014041c4641c04441c02d299008200395405440c1c118105140d40d40d41610344201207a08403070054200b4144001c01180c521441d000034056156001700314241f4030034a05400841420601c03032185200f5442c00e54a0030760440b107005401c00305070000703180c0310713262038a40c00e0006542602480740c42c000900300030b81030700c00c0200d0b151455650500d541ca40360421007402898601250b41030049007452071b01c0303481c4130000341010f5260ba0040c01c56035140d0f0030280d00301000c0f81c5000b41076400403c00300100c14004107501003620351200300640d07644aa03401003020104c6400c0d100c0b00c075902d85041c0c0c1e411302105002800080e48240116 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 590642625 1250 590641375 590641393
    0x9110604030b150613061b080a030c11510115082806050406061809090c05091026060601030c080a0216050a06020a020d08070f030515030d0809 63
    0x100c0120b210300b074110031a98412100510907240f1641c403c10b460709076091847e00c00f0440d61550f800c81d9110208080c04281e40d840d0713408485800c030700036984400e443d1001c0c000e102010104098901c2018600303848404c0030000380520a41c142c3e9136280314001d0311032910340201035540c1a010170002801298100e54459003880d0740d040c49420900c6c8902030100821881000400ca881e1004881d5041a002c05444604c0864240c035544076010080a80d960f0f01034080505c1d585020f08851a074004801182c104421302001c1403801c0808000c0714410b5903400320a68815040c3c0140c6044c9401164041d80e840f415000d8142c80140c8458806100605683d8a500c54500550031210300b90020004640444002540b114203540905070041d054545500114895644c4a0400d00500d9007110840e81c0400c8107014076504000f13045984a481c20000b02a040c00d1601801408100000d40c0030113440e0710000e00d0340f2440c000480b0310342402501700ca141c680e0307040015010f0b150071140503140744160b03220 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 590643875 1250 590642625 590642629
    0x80a030c17071d01051c050a0b19030b07180b07060c0206070c150b0d0c0806100e0a05060a030f0f211b0c120c051c030e0409110604030b15 61
    0x40c140c050b400b035460b264640c05503500d220000820441583e41841030500a0041000aa080c184080c00816500145902d44080340384100d40c5107115141c05652584181d1a07107070081480441500e400c0000c8002503603440000302c1d100c1c0c00d800c501c140701c0d24181c0c00000d41107850b20050000d040c400c030024001030482502c100d0360343c00100c50f0080000c8000c940300c008110400e101b035086403014500460140701c020041805613403940421151000c5129040002e09414001c1c540c1183c2c0714080c928180385418040c06401d840a05030b8600e00d0b0f40e51012030010b588110505008507885003e9810005203401e011428600e10301701603841c0341050f400e440d050306254444200f401540d4a070010351120348090000410355440c012070b81c0400d9528003007004100503004204052040c41d840d1180341c280b905112111518601d0301344810840061000041d170409007244413481d080d500040d5a0a29080c2046400c0341e1070000e5401040c006004403d00c40e003941444c2c4121621141021a050581c007 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 590645125 1250 590643875 590643917
    0xb06070c050f040509061801110f0d1109033705010c03060f0b0f0c01060f080a15050c0d0b010903021f0e03070e0f090a081803010b120d0509030a080a030c 68
    0x517115502e07800000009614401005000c80100b1200c800054007070f1000c1d805d0211075103c00c581900c2e0b1080882ca80c00ca0f103d1501452580350b04084105041951200120b60f9501001070f441820a40c02082850480307440c0c0041d0340303880301e415011020f03080c144c1061802040c0c440c0120bc002410407802242c4603404500d0401221049031810746410780c40005100960072141d290f12065480d107000040c820307020401c036006003144002805001240303140040c03501754034000000d2464104420000135241c1c0c00700f65941d004000711b01090410b065001202c113a05d49402c020b5001d11b8950402002e40d0000914404c0550070b5111840070613078039810950390340e041e4452226181c1c00440020b114010f00e0352003e40100131641211403220f41c5542e141101c0e082444640c0c41d00f85140d11100c0545400d0280650021041d030300d0741c0c0c1180f00c80b1941d6842d5402065a0001d1102c0006d0030140c54408000d1440c00940201c0415181d19503007400078041d00c20404d03c200040c4050503084051036041c0 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 590646375 1250 590645125 590645131
    0x9090c040321080627040c08060a0b0a06051b371e021207090f0605123f0c0114161b060518100c02060105130b06070c050f0405 56
    0x184401c1019aa18800c00c090442c21004441451714000c0000b28000e071504862405580f06000ba000740c0d500b0983ca0514041004005990445c2050801c0c85c2c1501c41030f80c0017054900038a8825500c01c140721940326060445840320b00c00e4424881000000e6105103c60031054015064144407095078020007000d10f401400080d0803010035500d040b042000f04807a00d910188003900e81880300c03101600c164107000c9154000c0c840c0507100c20400d42010550301c034400142500310f542100c1c070030300104541c0d136404c0d1071344c01071032501c160804980e51802c1100d9441c103003000749520280042c4803040800999000303d05495081d60911034481001d14a0f116034511800000c101031281c030008100499a2015500c100f40fa03120541416902254044c000ca80c8141e00c050184110b030441d01c0540351410500b0401300050a1402001c8908140d011030f011381101c0080f90f81c003004802140012005001141c0c04a038000c400003601020090340d05035a8086442c1155000c0040310b440003840142d82080f = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 590647482 1107 590646375 590646377
    0x603090105150418020904060e010f02270607060209041103090606090108210318070602100b09040b04030c0302250f080114071409090c040321 63
    0x10840944060415a000c020007560035110f03808141043c0b4001741b05800c40008201400707038680001d01a00c182800030411040c524042000a51025408145c1ba111100c0d004c00c4084108100c06000c0002a102e58030f8600307079076607290081d07000b5000d0310390050b92402440165101e01e409184940400d0b40249107604009080003d044d505a02005003580180c1042ca0001d2880400b24019010380d9100c40d100e40700c1500340c050528035442c0c204c05030304c03503540c000541700d90008040c0300031600030004200c0680440140400c0603011070b400361401d540c00c40840d0000380310344c0c00b5001681c000c0c81a41e03a44030324020100c0e201c6082c0d171040318103c8054141802101e01c40203400c402019880020016140c4001010f1000c100080840080c0174611104030450845001210f91921000306840154038111040341011303000382c00242e50201181140b40500d2140d110070308502401 = true := by decide +kernel

theorem cover : BRFrame.Cov 590467625 590647482 := by
  have h0 := BRFrame.cov_init 590467625
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590467625 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590467625 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590467625 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590467625 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590467625 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590467625 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590467625 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590467625 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590467625 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590467625 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590467625 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590467625 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590467625 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590467625 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590467625 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590467625 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590467625 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590467625 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590467625 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590467625 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590467625 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590467625 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590467625 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590467625 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590467625 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590467625 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590467625 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590467625 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590467625 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590467625 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590467625 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590467625 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590467625 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590467625 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590467625 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590467625 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590467625 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590467625 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590467625 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590467625 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590467625 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590467625 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590467625 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590467625 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590467625 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590467625 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590467625 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590467625 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590467625 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590467625 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590467625 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590467625 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590467625 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590467625 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590467625 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590467625 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590467625 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590467625 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590467625 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590467625 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590467625 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590467625 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590467625 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590467625 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590467625 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590467625 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590467625 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590467625 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590467625 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590467625 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590467625 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590467625 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590467625 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590467625 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590467625 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590467625 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590467625 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590467625 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590467625 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590467625 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590467625 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590467625 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590467625 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590467625 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590467625 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590467625 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590467625 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590467625 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590467625 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590467625 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590467625 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590467625 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590467625 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590467625 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590467625 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590467625 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590467625 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590467625 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590467625 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590467625 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590467625 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590467625 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590467625 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590467625 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590467625 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590467625 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590467625 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590467625 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590467625 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590467625 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590467625 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590467625 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590467625 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590467625 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590467625 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590467625 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590467625 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590467625 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590467625 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590467625 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590467625 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590467625 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590467625 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590467625 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590467625 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590467625 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590467625 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590467625 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590467625 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590467625 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590467625 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590467625 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590467625 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590467625 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590467625 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590467625 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590467625 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590467625 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590467625 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590467625 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590467625 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590467625 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590467625 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590467625 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 590467625 ≤ n) (h2 : n < 590647482) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
