-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3955
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T11:09:35.50898+00:00
-- url     : https://prove2.me/submissions/eb66c080-77f6-406e-900f-0149860b1918

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 711151079 ≤ n < 711330935 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 711152329 1250 711151079 711151097
    0x915010507050c1005040e06090f150109120302010e061e0406021c060e01060f03020c0c27070804021005180906010201110d090b0105100f0513081f0f0c 67
    0x950081019203615802001070754102108400800c0c003c0301001084000140009003e0001c03400c3e0310b56060b0072900544040240b40b41010344040c0f00000500078100c03050000e9841d0100380c2c4141c0d1183d000d403481440d00503a1308142e1070042e000e42410682c04034180074400010300502012500002034802c40305040445450b1612810003d40c025280106448040001045401000d000300c400074017494140034015890000000e101003468059841014010405281b0039823000a004c000c883c01203602e00000c1420000002c0114900c140c3c1101d904603500420011035049078800c2e2040e8005d031007185a0082800f0708a1b03007440368201000018828004144c841d05202c080c00781c2c00f21040c000042c0d0f08089405070615a000340b0206030360035441d04449410010b008900d503005000980703440303082000c04400a031000500d611988100880031403001a40c054100343d44004121450960b82007402e1590311070848218440465280b07800e141b80c0705a0560a4840d02d400485150740714800 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 711153579 1250 711152329 711152371
    0x6090f09230615010c1e0c0b0c0703121b0b06010e010c0f0b0402030304080106290f031906120308072a031206030503030c04060207091e150806090a03090509 69
    0x594603c1c0c100c0c0c94100400c49891400260081001005020141803402104100c0746032040b0303500065005105244014040e00039010000106003007940e80c440058499030340c1c0030030b04071010101103090360340d004110006c00d41441000e813995030044400303030790320100c0e100e140300151055100c80d44010115018000b41101081701885100d80292004040d03030300c1c1c260b50b1001c01d030035140e941d0000b85181840300c0e01000c030a4600c14800108a45010600381040800615424139001c010002d042003d80c4d02200700100301541d200307201500c04400118201d946074100100405001c50b08603001c1007443c441d03007085a480700c4c0c1d00d00d44044440d640700c0b201ea0381c42e681102c8840c40d200003444000c3e21140302100040c000d0028602c500000001c007500c492614070300a2404203503a001813031140c64803408669981c0040001100c0000d0481c010881c401f4020071482140300b66481481c080c0a150140902010042611b88400340242e442130390407604e480c1084100c040684080c0d070142812000884 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 711154829 1250 711153579 711153601
    0x105011b06090b090102130f050d0b07120c09060216050609060702040b060304030e0a0902030903090907120f020301090605031b0108100909030e040e0c1003020d06090f092306 77
    0x40c1481034030085145840c69032508001602610b0001c41a50003003034684070f050b20072515400a0401e122545025454080403520800e0410805001c0d1040720000a0383e080c02803c942654400808042102c0c04060300020461062405101c0050041c402d000e014030000341c0d400003e403800204001c1c5846103040c00c004041d8007102040340c2181d140e280e01e001c81d035298408ae5110b540203445910081c2004030801c00103904907000091214418010710800e00000020360310010f4050325801019107a51704c4c203503071415240b4618000c8074140780020358000e807103030050b5048841c0c00006100640d00c40c010152203103e04a050000c0d4a008009050298460130086400c0030080c00021043c540712995101500e400002c10390205440502e000480d050900c182c805180010f8003400385243c1e007800080595013500164010103801241c001240d2000b548028000c0c0140750341041500348a01c00036000c0d000107841555a50450040404c03540501c1c40314002110052024125959405113020 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 711156079 1250 711154829 711154877
    0x14070c2301172802030610020a050c04050c1b0708070807140f060c10240312080403050c1b1305090a03050c030d091b06030b01020d080a020c0d0c03080609010501 71
    0x219404802e81441100f841d038406694001c0c04250005070b601e14240b414881c08072120302000c021940035040f0840032440100301070140000446002c00c2a4448444006260090340980300d80141c0031b4140784800c4400203200d0007100c5401068940d4660348042c116201c0d0b24500c01e0307104800c5040004d00540c604010004001c0400424043c10641c0d0400301524014110741c444040503502e000c480f1568489410214800d03203644000c0c0070950540d501d4003684a0214014001d005255000c241094001e00680e41894502d00c204c50780041c40c3e00c108131494400710a5035016005c0300c1a030005101c260b006241c81005000000c100e03102c0c81d954100c07866403100750f070000180000e1003200e000d100c2c070b405150342c0300303000d5401e840a1103608005c81c0702c1c00060f5030081c03082c14500058901d01c0e98000c1100003006402d400d00451a555011442d0080c0c400c1881d03e000500410040d81c4407181c008151105003402a9039414069480e2001d2110400c4207015190209450500f04a07200c80c03501ca1b44 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 711157329 1250 711156079 711156091
    0x41407170702100f0e03190e1e0111011b0f112803030e01020d0617011a040c1112040303080a0608060c0c0309130605040b04091e0314070c230117 64
    0x1175071a19180003c0c10342c4c01941402c1515003c42c0329810030164040d10b2541e04000c11694403c0e910311a440303403400d041301c05000c1e906004001d00010781c40c0ba029400700603c0102e07180c07140b29510034400020603640c800000400032840c07010350803500c20800100d0340c0c005102400703007008022190781b25010240c0d182904808050311500c2d9081805000e0000d05817903a0400c1010411506040c003106050313603e01031302c140d547e14060b44068a41074142419155140a0700c0000f2401c1c0c00450440340c0403840d8086640038810068040c01e6403003002c0042049a00030759852815888401004094070402c0c490740600f6801140880e80e18406e03e002824000c2000003202e01d403521000100c0c5060704020b41d00c4001e1070785c448041000c2e003090300a81c07641c244102c0d810820300c035103036403690942004d0684203a6400004a003e00405002c1d00a00a22000b4484516200c0706945030242c4000460301a92120600c0c000c012400d1064200d64031b01e455a058490404034a40c48500d100c0c03500c1d0081c60 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 711158579 1250 711157329 711157331
    0x4080d1d1c0512120717060103240f0306050f010807180914012027210c0118060206060405070e21120913020309010b041407170702100f 60
    0x40030010302c04109803404030604003029038441500420a039001c500c010400024001c0301c01c4d108600c600c82c2c202440d80b0010900303002413099242e203c084402134000d220140010350f9080c0c0800c081c000e00b410441100e10840e010711081e41c80c8600440302d03140c20b100c0c010495002410502c8148001e03181820780200d000000039004a503501d0b04003640c1000c5a20030300c0c036507489451000401003401008444201da5030481d1912480306078954504502108680a070201f06030301c1511a518500f04440c9201008903982d00032410000315a264003140e0343c520701081c100d49400c04d61141d004540401c58100388c000d842d20f44d68041c107004c06820024450401c00495142c442c0c0300c4d6a45000c1c0702c0320740700129101d41b000c012201e405894640b03d03098284420744c09001d40d170000c1e643c140d1440b00c6404000c00168494680c441e0a50140103200c0b000d90303100f400c040806d4551442c00b80418820003140d5280c00b80c4081406070382a1b51280ad8030b071840142c000051300c00c00b648450700151401a20060 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 711159829 1250 711158579 711158629
    0x120309060504060e07090c02030a2001051e0915010b0c0c1f3f0e100207020301050f09060601030c0e1002011d0607021522060204080d1d 60
    0x2503044201c51044400301e40c01a0307203130b081c480780007020005140607150700038081142e040d08510207542c80c010310618204010350701c2c8441c400e10840304204629022503000030701c690b05105800604962008256040160b1244c001030642c51000440e07000450b074040c000e140d903900b000543c01c92540300010608403481007072000d10403034035868100c08107941c00c621a000c01141c05d0500528a51240400c01100f8824031340c02800c6908402084008010091142d07801d01d1141e9208005040c03181c2c900015030140000103403d01091703030018039586100701d000704590b5554074180c411020341036070540c0c035651000000030315550282c0c0c800300c500c0c400c90a200801d5081c01e0f0010f0031101000240c0b0006035141e8010303075211102c000c080789602180304041e0486d0300e42200c0c029644c446407c6a40030b28800800801c61014001c18400061101a4842010724100c1c1c00c162010f0b5015100b2415513100c2c00d41c01c01080c510902918200015003c400d4a503030480004001c400d03034190101c614040c2c1c5103c = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 711161079 1250 711159829 711159833
    0xa0510050c060f010602010e0a0b130203071707090e010203040f02040e0f01051f06020d020a0b10050d060b0f0f0f060a03060b0c0f06010e130b18030c060406110f07120309 75
    0xd143c8035040500b03443d076240d8108070009003920000040c0c10809d500440101001441441000e80c1c0051000c205e0300c83c5002c1400080d160000c00d42c00942c034040130306158141514045250002c0d02d01d000014807032a42c5070300c41c1034203d1204442c0641060600c0d42600010724003038110070010301084d01241c01d41322602c070350982195000e44405101d081410f142d07003020300c115001c020040c031150000c0c0a0920f19800040d44174040b002000381905099070006580103490080c041c0a020302401e05418481185800c600a2400c1c48440e8400c0413010440450b0b46040200b940140c00041c04181507001000c0a01429401403a21f400605898a40100e01100ea41001c0e020b0f8140d010000c000381131000707540604002040e040340c5075100407102080400007101c0c0c81800510381c0159070140b10340e02c0c0f52880714030f60714100142e0300302d000016071281d0410b0700084070fa0050f4080c21080004d108000700e03010b43e0307210b00c800c4050401014050032010810761201d0401d207403a80e09020134001416 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 711162329 1250 711161079 711161083
    0x1e0305040203071d0f10030f1e0c030b0f0115140c0c0d0b01031b0308090909161d0903070201020a03051c0f0e0c040b0112090c05040c050307021b0a0510050c 69
    0x1060a9040c845208100305c1a41c010003091030300030070302e40145a0388a045032245142e45240a03409002e840e0018002e0008804451141000c1d58101180300c0030350b9183c0c50040990181942d010064564403000441c20354008407a000446800744c803548410790b50090003c851b5000303800c240380107004140c040140c0780c84280034010228440c3d10080410360541c074101c0544540c80c00d1502941000395418030006030110201c0e841840111454a595904c01644600e400203075002e11948401c02140042c1540300c44000700c117a460740841019090b0344aa5030720381d40340262030f40a40164413039610400401d028400600300303100b84c00d100d100c02c00c191900000070390f642c00c0d031030010240e1703100c00030070019600748461407400c082110140580e204503c0001c200c92000ca490b003503020390780c00710070b010002d80841d190001e1402500901003000560005049a001140c5150141c01075081c1210780010141e65154181c0300242440ca01a080005100c0c01c1c000348806007050003c100300a030009401 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 711163579 1250 711162329 711162359
    0x100305011508072d060c1202030310052b031806140a0c080c160504060b07150b0402070506041b0506070c0902030a020903100501050102011104120b1e01060201050906071e030504020307 81
    0x40d89a120051405141043c07c4005841c51101150018014005406503c51001040319011a00170140c04041d6006048401c840ca84041c408880310381e501040540040d541c0145020f44201d0720842603a0704010344081040d003449049004c81040201591030080c1800d5142501604285041003041c9007200c5c5400074000d244890000140420445071400d030040e00007a00048440c242881e2241e07035071075000f45050030b105203041c2d00d0b00681c0802d92147c2d415074440390307003250499129040c01c0c240181e2098804410f030100c26070300f00021590f810322038203c0304696401042942207600c0d21451200a420142030107466540800039841e90341e508001030030415120660002c1c84d5403609001a003180c100c6c0040d40034030310040c4001c20441c020703039212010701a0041c02c41c01c6c45554000e040450b11403010524041d40e4481c500211b00d0030360550046224140340002c031401901d4511007a1014035140040c22060600c2002100007207220781c0041c1d401a20107030407180016281c1d0144100800 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 711164829 1250 711163579 711163589
    0x4030b22031e030b0f040e032101030b060301050402060f031308041503050a05150111011104270203060604052e030b0103060f0311010c03110303100305011508072d 72
    0x1c60041d904101c0101111030166081030b506040101d0f601070008984201e0041c0c01c694455503403003c03c80058032003401210200c0d01000410350301940122842c0079007180a00090f2a8540398000180b0a8101482418060b076002400b25040c0100c82048184540c80103007440d10203240311402100141c8103201500190809881041a00c1e12000c3c0040c101c85000b8042c4112038205014030102c0000034070107244880e001e2809420003d20140e9039070161040450b44130b1020400100001e0000c25482480043c18104280b9810420705c2040c0f202a0300041c1c621903800101007204000c54a0031540300c2c10840520340d45508101c02440d01718180e1603c02c0c3c4030101080e1100003000e031940e85841024003401e401d45010302c105003161201101c0c030003c120340c1814810b550200d0000e040c014030964191110f03280c120b9507280792090029601000501c4101d40640c04e14480c0120f04042060380d00039580320400414100d440c003909440c611209044010702004991069200c0f0350200304424003400d = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 711166079 1250 711164829 711164837
    0x303050d1407050d020c16060e10090609050f011e050c0c1c030509030a08070f060c0509030616120213060212130b0a140a120e010603050304030b2203 66
    0x2115060401007910003140100607501001c100304641c10b5000310581c0c1c241803000400517242c0ca6801140381c0780c00d4100301145000031811034005082d40c0d10050320103440d1001d84000080600c041c00a4070340d180302d4001c0c0c80104032010342c18045400c152081c008507150500d403000a046010750141500c141c41c000d0781000500018021000e040104098044010103840d0000d400c2d08800024240b00b2040c0002400c01100140540003690f080003000301341600111951780e00c9039149040ca00014040b2403c403501410448000c2c3c90b1030240091340d03180040a8043d007155920020940110031088080c0014003031442501401c1d41c4252020340503520500b840c04012904043c0064541803200070540c100342010130100d0b40281d64801520308455208408a45444081c003050350840c11030b80405a031024040780911119501894440c4601c144443c10000d82c00103000c0d00f426074000c0c1c040035205501c104410800541140d900c1680898400c9140440705071280112448408014040e0002 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 711167329 1250 711166079 711166087
    0xd080412030320120f0a0e0610060201050a1e0b0112140a050108120d09052b0e0f0d080d0e15091506090711100f0204061b0506040209041a01030305 65
    0x21050f2030001d1003281c21040511803c103820074101490f042e00c0104080501c80c0c0000c00f1840c1d501542c0c02a03100300310030b40305403883c92a25a1418208a000d072198100541c00e21010601d0390300144615819020054403000c0d107406005200c40c0548061503501d4104000000900740c4901c0610800070320720031070201003e1902301044d0b900155001a0007858045d00000b444000c2074038079104681c81c40354411720110f071241035400c14034249003407103528004861010388100b82c581c10006068008a00035140c20300c401e4101c03400d01c0640722080e03d0480d006a944070340d03180420942d02c058090903000560210301d90b0750500f1918142100480d030b0100500c040303400e2010361141402180c0000804403c0003c01b450201d00180d012840684a0380c240b0151713152a40e00f01c02c051000803404194104240038200d481c810301c0000f0f40c0244102c500045201c180c04107104c04085c0b1520019400c43c00400d85502c8079000c210945a029108444003606207121464030707058802c000d4000d5000b51162625 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 711168579 1250 711167329 711167351
    0x2a090204060c110a0b1909080d0507140a0803010b18030a0302030a091410030903030b04062607080d20010f0f0501052d060903192a050d0804120303 65
    0x30304800d00c3d010721441c4c11600c1032080c405440242d810201003070098a402a11103d0305441c00420398000350b616000f108042040385400034010510310707101c2d481540c1c070403203084182c1d61140321004d0010b06142d004c2004001011204d0301504580c03070301042443c403a4440d280042d26100d0f0501e4220f02603000414050031641d0415150303402880200c01c0755400940042c002150482c0c080e00c03020506556054100505200b40c0c0b140c1320001c0003074403c0094986406500f40000c8102c40641d00c4180010001009160007003440320407120030310000e20170200380c050142c1d51100100315807000d19600b03846048203103809020741d02c100090700d0400074140401021600030344034140c10841c05500821070741030078260400065001d910803090b030720140c03080310380020710f01307108059007a80d00d803051103610310303207589a0703214900b11034404c091641404210b4400720b042c070109842c140c03400000b1070300704000d00d0400c0790344c10070703481d00c03460900e490141c8031412142c00d00c503104e9007540040d40c2c071140d040b1 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 711169829 1250 711168579 711168593
    0x120609010c0504030c090c20072603120c070b0403031a0402040501080a05061c050102180a08060403080601170705070c1a0409020c0106050307030b0907122a090204060c 74
    0x200701ea007949030842c80c044c1191205040708845100380407034195902d010b440b000744104607022440f11090590b0301180200d142c07103541c808150040d003c14103680240b842000105024440901c0a0100a0760900500c4580391282804c0104010b40e00d5034100240e0000640204040b071051b4829180010801e901c00d621540c0d02d112001094025881040280041e0b0703000610300c2d6100080540200c1c40c0d81d2144007096040c00082690703c41d001ea02410342d420800c042d0060a4110b05651030104915a40c03c01c01582946034882c500141d0020130201c0c000c2841155030369803118040c1030844205200003010f4100140480d511130010b0310100d011002c00102d2076104008000c2c84442c92f0171901c0003120240310b40300c0d500c038000d2510b5000034010055042034000300b0042c4001402d0360401b9a4134200035000000c115180c1d0601d01800c1404900102d0901401c6034084d00324843c8414000007040118010300d40740300480358244521000240c0540701e00084c00135040c4bd642c1c1c441007511074a0f00c08 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 711171079 1250 711169829 711169841
    0x60a050a080640060603142d07020a120f0809060c18130501090203190c05090d030302091f11150408070f0c0f030b06030102071a0a060512060901 64
    0x7034030618500f41e6812440394510380302e1204a204100f42042840000e100245000901240e01030f00da00303001000a020750036610803100c1000494a9404030360780e98414080c2e000044221840d00410b0f4080f0b00c0d154400b1a54031540b2001600460b490442d503502d4802224801c84100700004118445860b04c10364040752040d0080c0d1410000d2449042141c0760300303114061001103040600c40e21230202205e5072144440701e01060142810025561507a0980b00a9803048541d2003002c0718141042100040c179124040c42140540c0e40c46003810703030060401583d003200004c258109a024881442a030344c80040610602c0040491610141c1c103005d000f07815603440301e0700495250441d00d6108d01e00c40403800499441680300071001d40d220700a00c2c010310080c000c0711024201804000001c100562800740b07440035203008060994803079440404040c280c1c0b04400004184c80c1c1c03d91113915400360500104d903008052804082420358071200414200482c50351410420351102c81440440350081c8161 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 711172329 1250 711171079 711171091
    0x7080d0f1505011112030c0307030b01051c090303020d05090a0512090a0b0307090b130603060b040312030b03030d0f0902120c0904120504090c020d11060601171302060a050a08 77
    0x10700120240c800c0c00401840705201d05070500144040034501240280081e038119118009895100d060000c0e444409400c100c039600c000c0380c1f0f0b111410078190b00031800e503020018a5891025041001503100c1c001e008003440860500d034007844820455441400b5951141701c0c504014407001440b03050540c40c0c001e00e004c6440051307004210307024054945002800a0b14111181103549448111003225140300d0f03035200021003040450301d0180301407540f03000c100b111250342d001d014040e00c13003144050600c2070344001800c03004107522a0403214000d402c04900520010117a80c106400c008108054855100d1550140c2e03030f5508045045190201c0c2481d02d400110005084507030810010451158014001074440e070780c50a240f04521307108000312400b604003400c1c00c0c00715501210000e581c9a0346024000040790340c100124403984400140c0038454141651005040c00d1481521021094007501c002070300034080c100b010158949800070201d44401d0b0759016030f02e02c1d14100003401030b00094a4 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 711173579 1250 711172329 711172331
    0xc011a0604050d06020c0c04150311030607090e190c030c080a060302010203040303050c070320010206090c0609040b01030603061d1e10020309010e10050915010f030311100207080d0f 80
    0x105010320b440f150b2240303254507881180160755541d4044824074000c16003124682c42130615940c00c1070b82c518180c0f060200c038480d000d0789003400499020141c881400b114a480000c001c00f01c100454802d00b05680e411407032041c42038201400442540059076140f03000e050229480c2d0b0188103c003644011510b60214184a0801c01c003429a40002e480e4462840f018080040100380c059034000c0078400c0900565001101d80c051403404500440000300c1144a2409401081d0000d02d240c3c8000c00c0440451a0003401949000e0320700b0101300003088506400c0d41010307501d00e000b10025010748116101ca2010703403000c800384400075082074070b0612038084d243e100b0918650450352110000502c121400c0c1e1031034015032207580d554541c0b401007040d21600c400358450028012000301940e80700c1d0740520459804e0f143d1500340d039a40c0d154120828030131213280980380041000071912800c000300045c4229815244011030b503000c20b0f416030b04664410f0740c00100c000341e442100001441081411440024 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 711174829 1250 711173579 711173587
    0x10090204080d0315080a03030b1003020304020a0302060327010b0f180411040b06120a06060f080c071a010308040504050109060b0d050910020a08151804260c011a06 72
    0xc09900c814560702c2c1c4000749600c1c1d82d075103031403140028104d1001d0881101180c0d2260700c40d0800402400b50200d5032406804410030038600c80303206e4001c0380c0c4120740207403421b0315187c515400e100180c1c0c8000c040603001504042d403041913044521065980409150000c00c01850071020490310003654035059100780404800030f08140d0720142d0310703980329801a4000720400128004500602808200c030740d800140041c5000c031010040051340d00503603168604000d00703070700c900c0140c4002e00342d00c2c40c280104586c200094004100d4000401d4035034411030110701e502000e24255a40b5160a80003110020f40c08034003030149040c240300325030040a08040500070507282c030380800428442c132000042400d0300d540000d601140b0030001c046881c071204108564503601c080e0024000034050300c08088160380e20401301c40c0d501c1e1209030864402030803884143c11f81c441d549d5064900d00742d0318105880c280c0804038410013160300c90240c081070340d49030000f0444e0720300621001c1902e42190300c0076105a074240 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 711176079 1250 711174829 711174839
    0x708100905070608070302120f100b03060114091c0807031d0604050f0a030b010902071b0b0a081003021f1808280219061b0b060d0f05010e0610090204 66
    0x38281c0b04645182c00d100620742c4400d0300c201c3c040d100f514054807030070442c0002d0042c1c03240108642c6110381c011200a070382c6180c54060040a45c4402c1e1260703070004074041003100b0300901b000e005203520200105070403104107140f01c6003a0b85104000c0c00b80c1c0e50480c0491a1000d06070844443c203103a9642014004da181c00c500300181042c0941d01495015690295454a040c0ca503006688044c5401030f01c5011250303581d0f041000030b9444031004546000c8103980c1901c0050686260720107440c0103040080c00c1c00da00280c21182d0b6100100084122010a170000000d46c0701c42c4e46e41204815003075040d41386440071040181405490003000110160b11220400c20000080380c40191901401501e000a003180c440c250010140765401a600882c9006510b100c031500200441c211076068607210354149000402c0300300181b14042c013400d07401400c0c1c0051a5071078060081d502551017812160703880760854031000d003112555016200d07035038849018046902041d4900c10014098604194a494100 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 711177329 1250 711176079 711176083
    0x30d0807080403050d0e060c1e030417070807061a04141003081b0f0705010305060a14090a091209082e1512061e18030f0e03030c0708100905 62
    0x240301408004d4080b481c0820350900e508692901c0f00c0384030440d1040c0c10421003840680d8811030700e01c1c00303481070804030700d580070300b600b0949109640010400362480ac3d000740c1014103901c5407030101d42e50042040f4500018025124250b000250a0741c0d000c00c094100c400c1c4401c0b52903582c80d04050170130003410060854407180100d0150303903010824a440e40701003451108100ca0203821a0207d0151010740b4044100014604088800980c0c081c04561600c0050050324824ad01801160181c031102e0500da0b805d21070441504000201d500044a801948901c4000100518044001829034008000c40a010880000700600d9070b4019064180102005601c039018411000400e40d10354001d945d405a00c50350442c024007101d140604c03019040c0c0ba00c440100494039001582c000c130b0521090f8a00c403280b0440090310030112028442c100c45441c15100c800c41c240202d0200310030000a0845500e00348003503c115032201004125140c20500d1a84c1040800007040e0030040c5070034207031404605c0c0 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 711178579 1250 711177329 711177331
    0x60e0f04081803010f0c0507050d030b03060a090c030206160b06010206131b0806010b13080c01050409021608042709030504030210050405033c0c130219050405030d080708 75
    0xd0300b2205052a412003000c2405041c14500e018078261030640103c92064100e00144034040c841c0f01074424030803e010f002e0341103a4030800040e0b0164821000035049071050b500c000b505c580180c4103c9011035032a80060f01a6010300d030f68600450700744800b942003100072401942c000809001404180c41c160284800554130900080c003960340500200300b501031100030034001303040030000b96641507031101d584024030341c001c205100314a08002400100c442001ca04001e410340141e40702e910b06480e10a90760007942000702d00000724488590301100040c2448010300c01059841d095480312510089080c034245040c028032040c090500041d030001a5001040703400380c0342e0407900318038400804030f001c6455025640140e41c146c4551031075140b4440060f0390303c0d4045c814402e0b40101c44003a00c1c000715041000c0d4040c004145d404001c0c0031302d11780b510400c44084500712800050400c07503498141000c44820900f2000407400001d000d100604007400240c0340060b05040c81640341c00d2501c001040200 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 711179829 1250 711178579 711178597
    0x2010212160b1503100c080c03040501182d02090c070c1d220302100b1903140c0105030408040e180a050610090603080306270a060e0f0408 61
    0x1100203644224803400462080c9007603001898440b9a10303000c0360001c00c800b186404a03210b803240d0200005083c0030381c00344209942c01540e40d095181c88848c1c10340c0e0907800241040f5519520303550307c802001e0440c43e04212040c02402400080c413000e66020710344841d140a13103110004030415640150300c0c0d0110248e04000e21000040e6203d5175070401420a40140e0821110040c1d105005400360380e5400c42c0d40d001e541054540b0b07003a032400010520705000546802400341c3c01507450782401600e0395002654412010f002d01c00e131181221007a1825a100c1c0e0800c0340d084103d2000c200390010200011001900203080842c0345080c25220303083e55000c0d5109040000c101100050880d102501c4105000d400020469101e02001e24001d41c03a848200d5014120090350f1100280516041c01024110398112540c0d5185868800c180254a141200c00c102c0c0c5a1403810a00312840c40d10400360322400082d0030000e8410f050402491950001070014103a041c030603014440440c045000f11740c0044 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 711181079 1250 711179829 711179863
    0x90b07181406130f0b03040204050f061c05190b010806060303030105130504022706240a08040f0506070206070e0a150e0a090203070926070b0d0204030803010b071b03020102 76
    0x10038014003da140c1d2494203e10200d4075405000100d0500b5803001d14000c80c801c44040c0440d0342c8084030b4503030822040724469840102d03400f03241c262846921000508034010002c2c2c90503509103040f440410260791104841504400e001040f00d80e9041c0843c60704050b04030081c610f1540350900040c9412085d00c2e000c45151345d1100400c0440d40c846400241000c903903000c07a202501003002000002030708486907401041000103081e0108003030b074100140020340c00c000c81c0c11710252070401c9440030b00003082100c0c8141400380310340100300100402403190074030354000c184518100d48001d00e6a5204008503004483c94181031213903086102003000011a03515142c15034010040c0020000c6225500010841c0d10020501c20348942c01a200c030140c901442408101000900e000d0f40710503890214a01940c210140a0081510314801000004144040503007042e48a860f603081d182d0003070f07001e079400b40c0000840c00200a4400c500341c51084000000c1c107030703861550700084d4498001781034170b6540d8 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 711182329 1250 711181079 711181087
    0x2030a0815011e02011e021c0933150f0f03031d040906090530030105100c080406031406030303091b04060e0108060106090806070c030e01030e01090b07181406 70
    0x1c3c9100b580b10440304002c00d41a80042e200307810140000b544101c0840206000400500038241480c0c021483d40541c00070460041b0354006410120340300030b00a4542ca04511621581800c919034010303a05074140e48405100301c03510b419103010150703802da0720210281030303800b604102007904408406207454a42609840c0c00d6100300c0080c0003002603000040c441460040070005008001581104160080c0742031122402051a4460300700c504441394021500c040006011605202d41007103454021410141031030010790740d40322442d030043d401200000e41c0d02c6d0303044e4114400d8618a59042503050b400f0f940745003411100b1540b40c1046800c82034040250011802c40e0b038496602041c0205001e07111a240c550310741c0e030100c0c2c42c2d078000c0c81113000056921710042058000407840034060140b45d1500d004030203059505980c516240000603062503a80c400c1a83c00d2182030144150403807107502035076070b1403510106c05808041d8546005401804100b005d10042a035100303240510402224174030b8813 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 711183579 1250 711182329 711182387
    0x5030f03070c05060702060709050f0d0206070317091c0c02060a0e030c0604081f0c02190f080c06061206130f08040b0408030c0106060201050415020d0e03030702030a081501 76
    0x14a202c804005201e4428842005413036580481c20328040e1690313540b00d6034400e54680810680d07c1e22035a00951000d01700942e2801071030300c5001408500d01c681494803c800300040300303000101c401c503078002442c0c019414061580d141c0c07a60119103903980b800c1030401100260007003034490041d442c004c001c1c0f0107120396143c8035503401c01610042c01401000290b1b140d0b111140207480380100e0b2582c0d400200c1401855a15510768041d115402d01c056000700300c20858020400002d6400d01802e540005041380c1e184017041c8400010400c22008070b0003000d544c100042400380384030390303580d800c0c049070001c00600810003042111060100d40020307440110503d0b90070720040500c43d80d40310200c040d01c001000074010348080301811b4001c0080e030080103119518803099081e1401220014072031602c2900c054a80720303040c1d014103032510f503a01c1d002618400d15021079185034800e9400c500580e001045a41141368040c035001c1e4001c0401d000c0e4451000440c0010346038504c40420013a029a001c818410 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 711184829 1250 711183579 711183587
    0x403020c0316050108010b040815070302190e181603020a1202180108091506010f050c121b0f0307020105071a1009050711060619050a14040c0c05030f0307 68
    0x3420032005054034030560b814209188024014403c1501183c1801c00001e804100d40082e80c0803106210098003021103c0f1121810105c00200301005040c0d080c0404010640040c086403080c90003500c0308000145058100800d5288420715903006801c00010862035100801840403415400c1c2405610703000524010303680c80a0b40c01c04d410106101040d0014082031204d14004101c200303803100303440c584070440d51076110390810001030810413408010502c00d5201c0e0b554031507410303240c0c9442da0405040f0080103050241810071003c9940010529200100e0829889000c0400e8a402401541601415203460307002c1c030b50000c1d051000108880301441500905150443c0845409100354030340700c1d2821506003864000e24024501d000c2c00581242d0040c00407000049060006100b5650b0b05020818410f451840c520b900a407030741c0c0c00081c281c03500000e40d0060010640c03401c01220100e030500040b103006015140c01c10003080c00710404901c010003100e0042c4540d9101954940d01c08001ba9 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 711186079 1250 711184829 711184843
    0x1a0906010f05121203070e09100311090408071101110f0106061b0f0204090606080d17180627011811150301060507020301110a1d011404060302030a110c0a05010c020105130b040302 79
    0x16802c51850420081464a1104600282d038400c02f072860080b428441440006d00003100c0042440100708110008144c2c0854440242d0b04140340034044141d000345100d003040c03480f01c0000c0c61a03449081c2404104e4100c007613000142c4c1100c0701040380320b031681c942c0c04a000c0440c8019001e5945c6100044c1800510303005240507080160844000d10007905004125000c000d070709448810144012902940711440352076034601440c402450240ca40c808003990311280d236001c45e00c85180321450500304110030301810f658141c1c21000410002e8050510000d0118268913907485500c03030000c4082903460b410180c90542d49a46007064a070f80451021034014044000b1341d41031002e010600b078007036581c80784c00050708030030700000303004541003400c015221511080e10740d01c01c0341400d1100344240c1d40303c0e80c041d5074803410700007020840000301c484030100c43d40041e100d1107032508204045400d221090203002c40c0d20b0841c4c03000300201e00d4034018041013003810030b000604044d50740c0046014035100f00701c82 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 711187329 1250 711186079 711186107
    0xf120a09020406030308010f060912060b030f0717100504030519180b0d1a03120a0903140f0f060f01050105090f03010f020903070e010513091a0906010f0512120307 72
    0x401c143d5459040141401109125500c030524070740f18049681489240c5030001c071000b050004e040c8100640d1140082d090700090300e50135200300703608140071030070810541d40185810045040f81c0040d1001c0541081c000d4000480c0141c00c0c11309010020340d000088508201005040200b90a490307801103824801c0c0c06c1c84421500c05006011505400f4040100341c1e045140300b08000703081400a140c0b0742c10f6004e0b13491640c96005001070008581102004042504092a000c1071840d1650382c0c510000c44200032009940c1e214540301d400e068001c00c00c4a500d1000c0c00b0081ca00c501d0604003040881c00c05005080c1007010100701c041841e22800001d0240d4074006009002c014440080440250042940c0707910031301c1611000605a81481b0143c0e060398000b44c02c0c0000280d210760028042d0100d072400710b440c1050b1a5a403040f0310091840035000700ca902c80030b4041c0b03503d00000070b501c1c40441e401040c851a040800c01118800000304000303402144030681da100d90b1114415220a884001c0c0e03 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 711188579 1250 711187329 711187331
    0x201020a051b040501120b0a0c140d0911030f070315020d18050d0518040506120f01050f01150f030c0504090908090a09020403230304091107030e03030f120a090204 72
    0x1c03245040ca00c0e100c60b0861005690030030180c3e9840d0001d12800403000809440d1501e0307072010803003c090980000c11103003103900348940b5800e230b4061124459030061241c0300c1856070350707240341c03082062044813646203c804070000c0c0b8441001e981e00345c1d2120740310b10008000c51180c5002151608458040d915203122140303041180e5402014001280307400d030441103505008101004418600030000c3e2408600983c0c1d9011485511100740001801c0151195602000f02c2900d00300da95002c2022110906089001007041e00701800035412040c4103030440e034000c00e840300c099141e481c1c2c8008a01c020101a141c04141054411404d6405110729000003040c5403c004141040c40850802031000782c40599083c550b031652010300008070700071400020503203407041c81020b140440c8281d0340b0980320360050070b0b28600380e13a84d1030040442d0507100406000410209444c800d054002c9101d4184d03203400d4020314908610001e2010283c40b900c1071919078240c1d00408a1400002a1300c58210140e000d44 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 711189829 1250 711188579 711188593
    0x40e0712021204020f010206011406070c0306110a17010e0712060504050c0a14040501052d120f070314181e06010f140a03080903160b0d0c020309100c0201020a05 71
    0xb0342d07480880100d03003c0c0e00500030b03400041c1e17055100107030181c122440045401009038510f0100302c041e41c803400d0f0955000b01c50401c0400800e00f00d01c00d0340302819003d070f00181e50301071800c0d002e450085841003190040b003811004001c038030303c0000300b0b66000c0c095261103a030807000203c01400809198020365040352905c3d082103249100c0700001c24200c00b160316a4410151002000600c9200c1c40c01013038005107050113400d6034004189507840d81200c5500074800c520011403032200032500030700e0808640f04803690900c0103201c00e8280a0b03800804074941482410a8410400c8400102030f02040041442811b0190030180a10444202a510303c9001e1043d01200c808590307294000e0286203507004403401c2c0020a00b011400240c0760150181c141013500f469a00d840c85203410040e0240c0e09070003158002004102030998410140c591403040ba03486d4400034052004a504101940c410b56000b045107280da03a980020600c043e12040c41c000703100101c3c920041307090080704040200b6074443e0340 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 711191079 1250 711189829 711189847
    0x50a030306050f0f0a0302092d0604060503150130081201061119140303090703061a090402041104051f020115061d0a0807030f0209010f0506040e071202 67
    0x5048001180e000b12010303002e500c0f620040052000c66041400e5000220b000308100509012023050b80c004140e03d11140810491181300c56400c40541c000141241c803042008440d00d85841404003400040d401400026030a02d01c0c80940d0f00306000c0d096a12400c0d1610030341c66450b0348250403900380f141411481c010114502500d440e008040c40710304501f848400410b00c1c034414110080d00142071001001b01505801194091408014084c0c502340400000c904103003104200640c001c1020310014507055103103081403405c803000d480d946c8907101c0203140036402c107540d92084103070400c1d01124005099041d903101e0710700d984145d5001d103030070403984400b40403010200d000b1035525401c2900207000b4011490580e170344403c1c19014000119103058891081100000c000002c201c0f0084c04203441d490300c42c90381c6441e240a030391080307440c128049081c00071800d10604060060100040002c02d00303040c000000c882c2e00503402411810602c07103000940d0300c2e11500250300a854074136411540c648843d = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 711192329 1250 711191079 711191081
    0x20c0109060b0907120209010203190c0b0108030f04060e0402130605040305070906030f1101091a0a14090a0506030c090904200906060a030b03070504111c18020f0d050a0303 76
    0x1101003520980d00e01401c11000f8102900568480c40403070ba560201d22840c1c00b6a64000c3d00b0038208a81180b10501800d80c4032400c2d41c5801205130440c1e00c5c0c8204e120110300e000fa450f80d80503001001c85800901451081d1248001a1001d4410a0a00490b0500040301040080c002c098105004000003400001c000350040300402c10359005d482940c0000b0b07240c0c102c1d507007921414031005100300042c2c1081703000310344110b17904440c02505241664000da82c2d1200d01c21699070614200803d01e100081031001150840d41500c01518000c804a00300b4021000083c000c000d94462980070300700010003c3c0f858881d10003190380400c40180100318506103410700804100c00784441d042c103001500c510008518003807103150701c2400e000340311f40c1c078080410a00f2000b4111101442e9010702c2502d2011406540b0b5000380584d110018110a44810b0300d840602046081880c400f15010314180b40c2a2a0f2503ca41111400c01e4040c0d900b0203012036200e001c640c0b001010f24001c2d295015007201c441c00c1581c1 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 711193579 1250 711192329 711192341
    0x110d050a080f0a02071502190602090d0311070608010518180a05030a0f05030622021e0909060616060b150c0d090605040e0f130f03030b0a0605042105030c01020c01 72
    0x102e0342182c50701506c4050301e05140d5a001c1054016038044281d015a4086001500d4407083c42410058100b1950750045610741d105d9100450121b08550301079441c2c0c5074100850300081246141c01d802c59454440495042000030908441c82c0d41c08a0011b8221200080c90401c0528000c0443d82c1d0007049007483c1d40c03203404c50403090300002e0541e84214045407161041c0c1e4012800100344030032014a20740c40b503069041d02c1c0c4180c0d0700700b902449000c080d40c5111000c80c51060b141da6500c0e0303130b071280c0c14100001d5410003070200388110300a00101d1246c0314045205104246d103d032000581514138000521800c1e0894080070302c0a400080510f412140403524520180d0716881d00e00782c403500c1e4002900d0b94051800b1b0541e0f035034a1040000c80c00c0000c1811107401170407200621400007455125004821500b1100782c000c40d46031004a101400c5c100e1918006200628026051604000c511003001d00d0049504032000c8200716030f54207104041c0308032002000300710021962601c010003458040c1c14 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 711194829 1250 711193579 711193597
    0x60b15030703060f08061f0815090c090903030c07020d15090302010528020306060f041508060415060c0314030a0e01050112050d211e05070c110d050a080f 68
    0x81020000122250b10f00a83c605655400d0061b00040d80e44204954020505e00000c1200110000000806480c1031040c02c00c0780c118017003003000b1450300da0015441e26030340e10307651402403100c1d8081188070600841034a40100c054400703d0790710f00d12400012074100e0760140190200111010050070344440c0e5121400d1588260024843e55441c80905008a00c031101c4485c035a20a1001c0c3d9040a1541d034011a403003100100b80303904012054803181e51942140d04002250102c01c00a1031721950407c9032a81c0c0454101c4060007e60080c4c507002409102c0342c0302da036081c0401d802c541340030503010780b0301a14103078512000f268403464201481c2024081140017000304d5482c00c800420031070390800341c80c405a50404010200310b21b40050464200121400c040301e00c102c600b885420308142c0340075080e036400c8105203409215040c1a02c2c0f00403103501421010622600c00807090002e03c1d039000740441d100080f41c20136040c88007401e1550a04d2155080205036040014500103600784207005000808 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 711196079 1250 711194829 711194831
    0x50d2d020306060d0506060103020703090801051602060a020405010c08030a1d06100605120c0306010516030302070308070305060f0f06090409050127050c1c021306030b09010b060306040504060b15030703 89
    0x610b446040c010039110184c0040c00c1c64000000003941c5500907002811a540704c1d00c0c017105016551402c890842e40240c03580100c945c882204100c000380d04008060304031006503011464149840c0010f0580030005030028100c22020001940c1c0141c40d80c403502c00d40e84114040d0142851001f0455181c450071500001d841d158100c0100c0d105215070b0135100d84000c02d0715420b12503100e0840c01c1c10f55801c006e0861307040003004c0160840002100a801e030405110391000758544035285400b8120070b0004010104051a1404200ca503644501544000c0c4500342c9400d403004003000007042c500e21440a10704e401904100b003044c03c21005620902015802d26440440031803002c1020340c0082c8d90b2800600181d02c28011185580752200c0c65103c028500c808012030401140c0c0440c2180392117800b041e80ca95500c600c100f00b80600d544074554810304d40c0c80208450840781c000170f0041d000203060340e40680d40e103400103006c01151341e000116590340105844501218082200c845900803183c00c0006 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 711197329 1250 711196079 711196081
    0x92d0f0b0301121505192016110607050a050c010507080d1e0e060603010c05030c040e0c1603170a0e0a081608070c0612020301051f0921171201050d2d020306 69
    0x60034000107040301e0700e151801d82c61802c074402c1841010b03460908d00070303260300c4821308100c1a5951032000428032148564081c104107410307402e0440c00e00a0210405041c440100424000110404211200148200800a8050f015400c072210302060300c0b1916240c0d920304940d40c05032400002e80f5522821007140244241c49600c14116450301003070b03915646410061205001c41d4540c1441c0347d0b84031900c0250242051542d62260560140b5104140d0204105400c5500c100c01d40801c0c2503070140340305400b8031074050000750903991080505000b80200030045183c0344180f21207e582c409040d081420a40c8a00107400d00001c002c11500ca8200130611400000f0041000b6000b03507812284001d00150101c0344203446000c010011890034002c2080c0140013042030b03600300c40c842240c42c0c607005045802200303504c0c01b00480600d01560b2812490b00784809402e0201c504c00290540300c06481c0d9101a031a1850718603042515220800c107440c2d0b40c984040694020071380c0040c820384c0210100c3c3c40d0b03 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 711198579 1250 711197329 711197351
    0x10506030307080304080c0f010f050108010b0d03020d110a06230703050f01050609030c0406031b060201090804090209061606050f0f090a030f092d0f0b030112150519 73
    0x39902c038070316006115003000d200041c00301e10518080d04001c0b004109449840307000300390300ca00b100d061020001f902e9940314010301280d034091181d4034820b03400f600d6460801d00e1a440180d82c48070442080420040c0072000004c00b000140100e0307048a5010380e05000c20034640c0d010404042203016101c1d10050180d0014200c00d01c0303805540c2c01070381088030f501c0941c0d080c1010300c40ca5500041030035800d8491905821019240c9105a80080d40101402c40c140b10103020300c3d1013420801d038000c0c02103a0500001c0b00105010900301c1d0300311840c0500041c0c0e00c169240214046024000501e10304208202040003401842c1d04035520440001c205040143d884a41074138440070241e40c03041c003640c407400c40200005d00400022011250a0800044041d500d05445030101c40400b4100c51011520b810019582c109c280440b016003a5055040601801c0558151060205204101240d120325010a0500caa01d66004111810400d8207203c03516200180314211030284200005540c039003d400c102c = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 711199829 1250 711198579 711198583
    0x30a020a030e061603050a0902090a0603020108010501030209060301230d030f020c06041d10050d050106150e011b1505071d03070b0a0e1201140f01060801030f02211e01050603 77
    0x200c40c0150030244913540f24130b240100c008140003031420910503074541d418000341e03540c0c5c080c070392148008a201041c5d4a040d48001440250113130b02c524145401840240326130356400040d281035888940c0b10b884c0f44010301c294408101d05520043d504036420a62480505521428566122042d50229a03202e406101030010314801c610400c078480488280403111040f400b001590004d250380741000c185070302d5000080e00c0c00804e00085849a65900341084000341ea00d43d4a0105445420100907a4046000207000014103803074508544a441b0410700801201d0411117110207070401d410001850a40e40292540003d43e02003d01e03494216914481480c00054002c1501c000684c1d090515105140917208c010050052640c85420100240c00100d0709101d540168000b810305198241008d08580c0202141a0810000c0044c80c01c01030004c107000c0c0707610074681d030b07030541d04801c010b2082155148031468192000482c2e002d203001220362075003c64100314102e02014001c00150300c920b41015 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 711201079 1250 711199829 711199831
    0x40e060d0b0103061e0c020f0717190f0609062a020c040b0111030f09150304020a0b160203060702030c28020103020c030c0604151a0f04020a0e0303030a020a030e06 72
    0x1060250031000600000c1d03a160000c3d505c0d007130b850184801504c1e80c40c03640025101114074840042c0d100f8105a0004842001800000c01008402c000c007031540315030075038884c941c0c404c1c4082400c00c1100080c0402075440c880b02c4c1440d80113a000c22500768a032400300054080400800b10020f50030b490282e82800a8007052003080d107580051241c0d80b04402400f02030321003410300c4c0381401903440c40804043c00600081c140c0d50000e644603561040e0700b80400010030900301210b55049014020040181c89000401054410302803030b06484020712040d50482044500c00290503004031000c4c050030b5600040500055001c81080e100074002800c200c00705800c0c0c004611701c52440580f00200994000e6000b41590f00148040d2072808419540e01881c10006132400c03603a8004800d82c4c3c203d002d03d188034100442103401d565461440c80c1038001284980c0040794540315690015812903118002d0440d13280f0f9a0b000f030192522880c10b00d2240c002904465889008a0704050951010140103d981 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 711202329 1250 711201079 711201083
    0x5070801050f010e24040905060114070804031709060a110f010c020a0210020f0706080114011e0e040204051519140409050901021b0f0d0311070b040f0f0305040e060d 73
    0x540748903000da50811113072001300008040741203900601d00006070000e40050024000d047d4000c40c550400000044c1b5440c5046001c810101c0c040c0200000561100111400c4075080005200302d1800003540709524030903400910751208000820301091508080951054107000081d0781c4070f000308000d00f07800e03250403640c5100141c00181c4203400500d4000423904000c2510b10403a800d001e1010740c0c4502d00001c2d03801c070340049a801801040300c800e620003103211000003841e18543d100e240c86000308408007908240300501c00107002910145c1c0307440d81520b00a020041c80581014182103683d14039a11005c2c90b11038008403d4585e040c618054001403040c0e1b010700d812945814508044040141005019071a055400700b10200d000c0000601c12070041d000f510181580a5640342d5452074030070100a0762003814181580070200c400301c3c000303481c0d4541d00f21490030703030070307903940ca0211a030190b081c2c4014074079400000c11606059124028006807040602448265210007040142d511146400 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 711203579 1250 711202329 711202337
    0x3060b01180b0d1d01050f090607090b0d05060123340807050c041a01030c02010c021c05130f26031b0a21021501030c0501030507090b04080105070801050f01 69
    0x441001c01a168401c095080c0013a140000c088654406113080d00d02c103507550859514950300303000c40c00c81c0a2103100c0c3c1101d45400c041201c01c2c0381c06180140d13805880004401c0940d2100050b9a44c1d001d0103030300000800300000c03c40f44461200d281141c540242d2000140c00c2e072080c050b9500150031310741c1503516107401d0f1124001541c507a501e211031a0310403d000ca600307006450288407a0b071245d0082d695200c1d8410070086c00b41c864800010100d660b030f00440011a070400c49a0038145d9004910140c4c444060078500c980910b62100c2604c2d0380c0704069030480c2c6031000b039100203582140c9410071402d5819289a0702d0092803444c845c14181262201c0001c00e5070410031800b20585034a070301541110040f8001d480d02c0c4c144e2a191144010246134800d050140e43c82c403000e09032a4140080312001034182c1d2054095410b544541c4084030080c0516070506903a54007182080d800b690f088401400d0100340240c0e910740340c44246003c0c01060716120045810300f000400d107880c1c00f6444135550070060356 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 711204829 1250 711203579 711203587
    0x7080f0c0f031c0917030d050708040309030210090807090e070e0709141f0c1b0b04050d2301090c050409080d0f1d0f0f123103060b01180b 61
    0x1845070040c41c58040c3c1c110601501c1c69000402640b038845400e02c04580301c01940d29003000290420039140010310007010000040d00b080000f0380c200208000741e0b0f80541d9018150b2200e100b0070740f6428400c0e003020702c07a489420000a50140707180c000807038400e120000c2e00d4500f681ca041451f1585815540840812103075803013072000001850011040410040194a0b104036180000c0c031003902040c2640c00060040000d4014030807000302d5031600ba5440c0c1020341500d4070b402d016095a009a0250718407074400d6040340c0c0c003800740d20a13800c040c1d1000340c00701c080c03c2411011814000c00d0120f50440d02001601000580c515040c8241e031149a0450442464946041c0140006040c5040700c040c0c0c1503903039106000882445401203949404240c000c2100001c02c5240614000101c0800380165110f40a0301d040e4510250a8855024400080c00d00780b49005100341502c4104d81144818210720748030000a00080d83c10000030320b070b001e8030340201e044003c2105490540080c0110241d0001c100 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 711206079 1250 711204829 711204853
    0xb180124051207140301120b100501020d05030c1b0a050f07061b0c03080a09031109250e090a050a0c02070b0a1d04020d0b0307060c0b0406110c07080f0c0f03 69
    0xb10800f40e000d01c491030f0000a807401140600c200790004c0c0c0040102c694103c8040e01004140644a41c0085080071000d81183c03a10300003e40d14078007407144c90204400480443c12202c0144165201d80d0643c0500c41c002c800c0c810081580c5240c2101c058519100707e1120911100010071040251491995459429140e10b801441c4600310100212100d000c1200f00002140c098005803640130030603030310f40600515504112090b041c010040324450324000092050f02e00080410704201c0c03c1c152000d1015804456098900140e035071089900212040104221006540c0c1305500c02e07050b01c20100002c081e1240c04985d1030f207442c015070750300e5102005201211401100e0504454411050b01c0c0542003a000114050b40c02c541581140d540c1c44528000c032500d0280700c0c520141c0705a240c032441900194680852000700503001901d2140d0b501240210a0714400845e030300803046038115103c05a580d60100e540f5240721800360007900610401c40f00514011000d80b840310002001030134466551 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 711207329 1250 711206079 711206107
    0x50a181410050c070e070e04020414150408030a05070606091407080c0f071506060c0f020d03050405061305010807110a060b040b03192010030f0b18012405 68
    0x85071400e09001c800d2001d04411001000071801030622060030328040d00749480d0103440c2d2910104081c0c03255005100c140803d0f0380708200b03081001004c0358107030100803075140180d80c030348295005412a07020004980303501c81d420500a1504138822101000041d9032440c0c43c208079042c5440001ba011400004914200d22a403c200d420080328142c40d03250400da0b050030340d401c0c3d0206004603050203a81030103203050708079031103a00003d01603401c00b410141000d41d0ba00080302c080c020300074850041d1481c10404d0500c00d505460103028041d041c6c0d945c95000d03200c11250840c0030f204881c0041c03160400505640c1c4242015004042c480f0000c0c1011401030381c5040107170240a408a4105ea60741f003001e04a41c0e020410380d0010700c0e000c41c140341c040885003481041d00d0f85c0c00e10350035940b0f285404c5003200d64990003104121003441e4500003904000b440c001e040a0415031401c960f202c1c0f0300400403040d0354071162842c1d049a0f44881811345848100c000c1000b248a003d13010000f1a01c107014010041d548 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 711208579 1250 711207329 711207349
    0xf060f030b030f190212011e180b0705090a090c0e0607050f070b0a120902180402040f0204150306140a0509070e1f020d0c12050a0507020d03050a1814 66
    0x401000d580c0190510f00350a031400241c00310000801107429040e400307501304400c20042140405009100c4421581c8030350040b40040107000140d50b9613650941a24610800325076005076020980d800307941802c000041081d009052070390701c42e10842c003000408103154070840c149550151120010f841001d41000602c1e00f122030103545070f00941c5070303100300e03821f0502511019101858a4a8a175881d6100040118001c044003d0410349442584809641d40c940e0141811203a03004104660792284003003800b070849102c2002c40140081408035203038584090200c4101c0172990100212980c92510307118003014094800c0d00035001181c144011f04141c02c1c9568014480e04010f1000e50700580070480b95440d1641d40d880444801810040440c2d0500001d107210005141c88160f1443c680c07940585c0e01c043c040682c0c241304000880340031544c00790060312440e41c2c0003040354401c0d10490501900c941c0c4100b0103400000c0300303d040c51062000036240d001c140c1d1504040060407102d09001c0c4051082 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 711209829 1250 711208579 711208601
    0x60e1605060d0905010504140f0c0a0e150d0606090b030c090103080f160302010614060a080723120601033204083c04081203041b0801050708010f060f03 67
    0x10b210f541110102d1070901946000b0b03072264a02c40c034241c07449040a8245210741d640110309401060f45003102d965000c0c454801d49118980b030741c3c001c0d207882e80c0720051f200c1d8045410740c11209103070b07000c410f00c503913230f4004012030780d038004188141460f140406032614400c65019503c000c0450050011030350f0040a00102c54150711020b00d40040354003102208000c4100440c0140c1d1154810b205c0207400100200f125501039511a04221a00c10302501007500207145004000c1e040700b486807101c40400d0000d07840c2c011901a240e480410020314003444404685c409c0c046420a9000c00842c40c5001c030319160031030182c101038200c10816010b8084130b84054000d9507001d0050200303840a0301e44107018000c1c11244200d402d243ea9201c61255031400052000201900b4203000801075a000490802004102522500daa1340d0f40c07031030200703c00101c0b4405a4040c09824a0220790707200c0543c09140100c54584490000303030307a01c1c4d001554490860103401d002420102d040a200d5001b134001e504480 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 711211079 1250 711209829 711209831
    0x30b1c0c1d0c1b121e0702030307020904060b0d06021e07050a0f0501020f0c01020316140d090212060f090c0d0809042a0203040501031401060f0f0215070c060e1605060d 74
    0x9112802185001340684140515240010301c003111401031402a14100c1d020344849401d01c001900000d84034014070001174020360322040041e00300714481c0d0003040581402841a60703215180e0500400941001c400c40204005d2004284090000001601c001c02d901c80000c086404003a0b544180248034840201c41c159000e000c54549201c0c020f02030181303400740b10001616441c10071881c0a4010201d403045060244885449440b40320034002c440d4110000750010400300071901c0410310303c00b11051040782a018010038020035090b100c843c58000c44c6c40c0803c6640503102a007c0110310070070341750010000310f0100f1484080d403c040d04000705a03c2c01c158407103000d803009440e06026600c907010000050f000010b05100540c0c040c40383e101c40047c1a60420403543c100100a40842c07203c01c03200c000e11800d032000c1c0410710320070011540c284916000b8814142410070300900b94244a005c200ca070b090502c0e000025407000090001c040000f00303246810381900c2c010610403d035001d0340c41400300d2 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 711212329 1250 711211079 711211117
    0x2106130b042004021b0c0d0c0506090114030a0c020f1911120a0803010906120c050d02030f01092102150c0306030a140607140a080f0601030b1c0c1d0c 66
    0x10b43c2e120300c0500034a84410245421070000c0c04a034900b003160342c0034602d10403141c014000c80440d650076100b00581e102a50034a654500c9a001600e0806c1c05044540c0d8a6070300108210064030680c03c825035a40283d022200140c101c4100161111880c20511048190740340300308020404821512508160203000c2e000302201140100e401d010060030305907180c80b000401040100564840d5000074a50f021882e81041c3c0b0b01e50704d03608001042e118035441001c00312030301c00c00d43d502407002c8416040f41200800500100e8900902c42062030300c2001e002c03000004800000a00205030709040240000744d002865940010024068002a022507094864030054400084200b43c2a510310307a4544020300c824a0008802807181071507010f00301d42e030081405010b0001d41c00c400d000341c2020801c03c181d031b8143da420b0300403402000d200700b107194020f84061107180d02019000030b424016001c1e2450b17040194407038040900804814400e050040c0c245c60004001c405900f02629000d0f20f401c00107096 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 711213579 1250 711212329 711212393
    0xc010e0f0307090b0907021f05281b020c0a09020a03060f0e0415111225020105060307050a030c09020d0f020f0a030e19231204171b06182106130b04 65
    0x1407001000811035005035211500c0bd11405081c1211580814074070040000114800208120380c00d10320540c140c554010982e080d4803406038000c240a00020300c03621041d070303954400c1d1300f98044c81590180e6071980505284442c004284c0100b441c4a03038481c0c0c00d40d1405007140801000e05200400703030410f151a681f09200d0013a03000c41c40d1180075a20794004201402d00303100b018107000c8660312440c0f18100701c410400000d489040f61400301c0c1e0f4901001600c0c1c4a42e4401c000c09041d41030b2850016a01c00100036840020607805002032201ca59400c1060120a034240c5940300521620348104018204000d80000e5029941d0b010252683c0c40c1d013807488459045040c0f030f0500441103000d8142006c43c3c140321185031250b107030003002100c0b8001c0c4400791224420480086680d480c0501a440000303000f5408410740c40200c101c1800505421070802d0a00415a0f0562018203800c10302d0040c1c00c003041c0000c050b82c01603a031083c0c122036000882c0e182e560740c0c5a1214041105031441b82c0c0c010b480402 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 711214829 1250 711213579 711213631
    0x10f12020907032009150c070b0c120a120b0a05031902150301121a010e07050c03121609051504120f0f0507031a090c010e0f0307090b0907021f05 64
    0x200046031450b07054171850300300c0c20889201c8802c1d2150200001c2801b03030100c02c8400040c41c0d004c40300c1941c1d00780c1e03481110644103030414030101c41c1c0705000000003400c8000e0300d600032100c43c5254160401004074448000820103900540d01c54039a240d4030111000c91108014049561418402406044001c01c90781043d40d098000b68001e41c484551264070000b8822090441c80c0020312466a8013465030400741c03039401e50100035209100308040802e0605050f40c0070411282940f8004895401500d40342001c41004002580c10030300040c5a2a400907035030508841d490911800c0030b004604003820029030800c8030520300c005450510342d03d968000070801200300c0002c00c5005601420400381182050004842e83e031802c1c04a285100c010000602c5001c5110658205c00341b8000400030140c20000742c2d0082500380b550b0303250184040c0001c40b404981e12603950075209a035102e0b1559a404000d90300c0c0c02904c1c100c030800c0002280440c1350010180c0c0700341d83c009200d402004100e000c0c2400380e2 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 711216079 1250 711214829 711214871
    0x9151401090f03080912030a09030605041a04050d02190807060b01050403150507020d090302031908191d060702010512040c030c090c11010b0612043008010f1202090703 74
    0x3603030160000071482031720306040c03941c00d1605032180c0041d481d01c00c50341030040c50849980300185c150ba541e24013140400420000700035501c4c50b50603400215080904000c0d840703008110b11038015218292212000800c0e8660444201e80c000c440e007030070081561248409440031807010340c1040700411020001130018504400d03c6c0c0a5500005418600410042c3c40e000b0018425018000d07004010001690f0004030300e503188400b000c641620203000c0c030b000c01c82409042c180907004804e20503c4034142c0d5101d0303858181020341c0817561470401c9071042446440d1266002c042d00241080283c07020032180d034085103400910411000300b0b21690fa03100e102849807a0f0f04032420861301d070031750306035100d900a041803200e6070008000c11680c4071440c001307180d901c03800e100c0d100310656820010b000e102d2003002a0600c05405c800c4a400110102c5614144284480725000840c1000001080b110200220380056a82e1500540c040e41521b03001c1000e034580081c0041c0c00c054841003240034603555071500e0 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 711217329 1250 711216079 711216083
    0xc031303050307051212040f061e0915021206100c0524100f1a0c0714030601151b060e0d1214040b070509030f030f0d0609151401090f03 60
    0x2564032082145092401c00300079117004d80180070140070500614104010543c0c0103a4007008284207105646803103c06085400030100000300b000d010f80140c0c05941e0484e0b00d08501c03d45425040e8001d800c1242c1c02c80c01414014503047c0a00000135405040424000c0444006428201c60144040c1d4515207031000c4042e1808040791004900300c600300120b00700b90341100030500e240560780e080a030320248402491058035007503501c2d2500b03a095414a1011100390b05043c0c0b09491400d41c8074003001445800c1c1e4190107009108107000043c02c80024041000002d410f41d64a004842191140e0b40c20042c001c0f80660b010350356034039650800c4100b00030101a0000d1a00c814180c1148080c891003100c410700c11111801c00e03000308200000d240d40307840580c40240c505105841d8000400464504000300c1d00302c00d041e101c0014564079104482e005032140080184e814040c1c0c0c1d8039140104d06441c00344040784140604154148000c8a80859200b610981032400410041e51004002c680c00e0706580700f = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 711218579 1250 711217329 711217333
    0x18030f090f031b060516060b01030209030f0303070f08010303020606091009020307020708070f0602060c0c0f060906150a0302060a0f270e060910031103150c0c01050127020c03130305 80
    0x740340700100e8071083c000104000d0070001e040070b02c4d440c00368000c0380d10000c008200b0f642c0c50505051507802941500c0180c44050121016080d102408903540d81c41500c91501140382c041441d0750440c454040d06050700c2e07140c1d0140000d525060309110517042c001d0f141d01006c2c001100c020a0b8008244080c5100d04103c2d4001c0c204546480d03002820176809800c4401c040343c403508240403454000481d1504029640342544d83c85060111140c1007120b41a84040f045c09504144851844001402070282403080540c00c00e0440401c20080b030a0b04074400203403c480184400400320b4021a000e000d6404141004400070038801e03100c0d503000c1c40c501035408420384169428000080d0150a00380e029000b920200c842c1e0508070034001c59208584401040140b100c0c14206176a00d040c80301c0b1a990030602041055810040101a0341d50400f0241000543c078103000056416888403250054204181d6a01d603c101c0f84a800c0e03000e0741c05a00010864071041103e80700360000e2a034840021805800 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 711219829 1250 711218579 711218603
    0x4030b0601032715020f04050d080d0e03070b06030a11060919060c0c0801060b0304230a03030b130b130b0a0b2212030f121409011e18030f090f03 64
    0x103465589908620b50302c030313000b41c0306001c04010f81c9441c41c2201d0581d0f80440c0c05d4074000600e403030144403d101c1d002c041c11079542803542c0c22000c941c000000c0d01d409442001141003640e100d00505548510f02e42001d800c1c02d817400064000c0713050040007040003602c050142c100181c0d03000700b0205281040e600000008a28444100603c019000703400d0140a045009002031403421400c48020702025002401004451070442c60000003140101b0072a0806810750b0120b46941c01c0c040e0040000d402c00c0c5004542e0144002101c0d0100d2003a00046c0340010f10b05002015043c130703560010904841955040004500c0115241641d46c015060000c007a15200c0707181d0b504400c1e14070074a1900e80c01500741c203220543d441c0020741c00c0403032141c50006c50703e0002d030382c18114100c0e5006006c403601d805000c0210b80040c801c03460343c1900600710104c0713400d1104494a0141e81071200300c1381c03800520740c1d40711880c10700c1500183c82606250004113a616080601039280c10380d0300c0601c0905c1e80221582d005010b = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 711221079 1250 711219829 711219833
    0xf0309060e0103060e061504030b07051305030303270708100506030715020d030f14040f060605190308031e0c0c01110c0618120a020309150f04030b06010327 69
    0x203020790504280038038003030094500d400c40310014804050300e85886154142c11665401d88148146d03002903030000d04445180c18240e202070600e911501041c10a00000c0703101148500f00001117a00071030444460011020742a400c404241c2282103c0e01820b000740071001913184010003001c0610b5040440015082c203040e020540b500b80b2590095800c0c0761081003124603a900031a8411001c000c80c140410340901c600b100100a01c540050210805800700078841445001003180044504c2a1010064a5158820800d000d800a20751001011400c0c1081c00010300800c0556004859592901c44c0c15500c603414050b100411102213010040115101d18564400d0248640610042079428607000c054200c01da1070340c0e07005120300a40d02000e410316034542c40400c000010800c41d02c0b030107602c908280b180207459520603603002d8070420341409080444284081110700c0300d0320781c6a866180915694032010b5030f0310000d04050605507100d8403c1c030401c03802d00400000c2c0c030722441062034900580c = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 711222329 1250 711221079 711221087
    0x140c04180e010b0a080c04050112020603070c0516080a15051311040207020307030b0907093803240f091e070518010603243308012c130303090f030906 66
    0x142d002c092401d0ac882150000358480c802144d0f00008140790940105542e810240d203003000340a0704d140000c050140005001102240c0c244030342d0b1050300c04400078030280042c1026a10f050b0ba00c81c210080d035540e040001900810140c00300e00c3d000d8009800d04407503400003400c1c016650b200303039100c0764020108000c005041c0f00d40d40c05046841c104208808041030070160240d00b1507000340f011344070a045c11028403400c002c0001e00f910010102c80003516001160348407400329500c003030f001060b600c0210781021100c10a5500c9101d03017200800000c1c14608a44a000c140441401528000d00c0c00225540e101c069481c80300c50560240400603525000004086030f11641d03000c00300d2181d4a04011802c109159580225101c0e2451002c011007240701c204c5520b004031031102450015940d05803c40ea800070070761412100d00101403c680440c910b061081c603241d0001e484110341e030764800150704d4513000d1180d803142ea0007445d0005918009175100e81d568000c0900603004200243da04110083d40 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 711223579 1250 711222329 711222331
    0x60f020301080f030f030f15100203090a05030721030525021201091703090c120a02040513120f1209030810060903051c030b1003140c04180e010b0a080c0405 69
    0x3c0034000c610700f400e1802420024000a8848107070300c2e40040105100582d07150510f05103840c01010706002900c0220065a01c0e408404d040d402100141c1000820385000300b1b40e1000c886240e9800c030b25082c00035140e120f0b00f44400d1011024001c090084210380c03103140e03e4600905001e003444106141c2039004020b901d24240c109501e042e03042c9955000040c0406001d0074000c407207210600d0f102d468000c00d9505104401c6071103030704606400141644108001a000c074940e009035002c01c1951980459000d164a4500c00906402d000905140c0024495003031015400c0f4030b4030b05200c1680c86a0070301020764006a0f81580061282c00a020403891034402c1d800080400342000e440f00b40c55942c0e038a440d80199401c103d1401c0c2026100c410700e42c0641c1004502d200010040e0705001c00701071016009150ba1901055543d0b6034000055003110414120384c00d0f50214070b0b1074200120030700c1d00c0e04c01400c0412441815075480340a2103149489220000001c1d140c00c6000c0c2505140443c24071040b108 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 711224829 1250 711223579 711223603
    0x1502030703090f1202040c02012405090105040204031a090a0b041a0a020307020d08060d02120604060e0307020108040204631511030109020c16150e0d060f02030108 72
    0x12104010072002020040744d1065a5042e180402c0d042d070b80f80c0c800c2e80144031039004141507003c80c12500706440140c1000e40d0a48100315408016030340c84000380800c9000d10f00000b8000301040143c40c0350910301e551301075448200d600c100ca1507000e55a40720072000c030041d6401c03550003e400d403a0030090030580901a9010008000441c00c0d031400395802035071112510481c1c41482040d801188068440342550012140c01070f03e19084840b9401c66156a800300300c9040c0c446600c0c0280d01ba40c1010040200c03510181c0580d143d02464803107408000040c00021803450714000c1d0401d10035107101c1c900c1500058002040040e80819620711425400c60880c5070294505d5a00e11444141d00b000c01c43c0f558101c1c50b000b00c44440140020b000708001465203002003414800080000640d052072900104200c001542c2034030761001c1041d0718010500130b680070b47c4e03904c204410f036048651032080c40544505503004220710b0300100651240011200320702c01c1d6a044d0342d000401800081c404000f8500506 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 711226079 1250 711224829 711224849
    0xf07170c0d03051012080c06010303050c1006030206070210021e060a0c0809031207051308030d230105060c030f0403050f150106170a060302040510030b130308041b150203070309 78
    0x12030481d42c5080c82e0031840c09803d40c500704001c0c5d111306010110082da074803c03a19504850003942c40307040241164000608074440da110f2000c0240b04940700b0701849003142da01400351030400d00c035542000b05c1046144102000c46c4030340003440d00450400090a4540c00c0c9240c090070341c0342000c050080c29600c03a0280481800541c106124441100004030f40102c5080002445e15440c1d004044a0034800c160342c1d00c00d8114241c03000729504030044001c06041c0300a480410503ca030b001c0d103094074003624000700c039480c601c0800100a241031103001800e50040700d6059a2600061340030220198200d90000d40f001da104415000d0000c03c01c11280080c42401440044030790702d4a4001011202107094040d00d500c0c00d4408520154031581041000d0b503801081408035113090008044c2082d0148001d440c0b10000001051078401800401410b03583c141e03480b407940d940c4607120402c0d8425403204000340c9600341c00300040d50003061004529034060035801355584810f181401000300f41c1640146000d8 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 711227329 1250 711226079 711226081
    0x60c04030f0b090c091e10180e100f060801110313110f0d210504050f060f040e07020303010e220b190507030603020102100c140f07170c0d0305 63
    0x1c904299191031126a1102c141400c030b9581c01c8815081c0180070481c143c010342d080042c01480f0258100306240c1c51004807400d4500d80e82c0c448000b820454a10604d01070444415013100c0b5000640c01268110140b90100c42010346202e40010450b2102c82c2500155580c03580181700c240c1003805036000071401741107002e0541c00d2401254104100f40e8600402c03e0a02c101c014100382c441c5c5d4080200381000501c0040da6814605101200314180c00540340f11507412a26580c0c001d000e0310030765094440180c03508040a86078014010960700c1018100d041e40010b1000040510710b40a403540700e402158051604c9501d0f0075801900081c0150500300200e01e03003a1000c1a094032450044030346a0040340d02d5003c0e0701c445100c10f01069551100c164054140b004110b00b40c0d415410000c02c5034400e9086801600b02c03201500e04840e050045c650000300079280060541340c2c0140030300720b803100c03c08880b49032031400e0f80ca1441c01ca6550316200d000580c0070450810700c490170f01105072041311505041c811 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 711228579 1250 711227329 711227333
    0x30b06090a1701090209181c081b07020d0f15090b070e041401140307080f0706030903051306090611010b030c1203160f050f070b0d02091c0b09060c0403 67
    0x51841c440c080c0303030840d00305031140c0708500b442504000d1400d50040d000303c049003003040d9079020a816034513107c0c081c2d20800c1c4201000f800990848a552003660303031481c0740390710703400351100101d5010440503044407000c1c031113074003da42c80403404210544034000c41483d440f4540740c05503214144032845070300e00d49010284d0001c5090046441c1d401001480c1c0503050080000016006101705030740211500101d1002280081c00310140b44090300c02142201c14031036803400d034250703504100e401201c3c00750002e100411030300d408ad4125141c4644a402d10909002c0041c0c0001d82a0051358002400114410010020340387c004c6c0b0005080303c0318000901c90340b00c0b9000801d94420808031810b002c1e844040c00d2081280c1d0500641c3c0d80d910701c2d825481103081c200d0a142007400d006a500707441c0f600031310320380002c071036400642c003421100c101419504115000d04484000c3d0405c08016070002d90260f54507520000c05c5065101d05da200f10401900c5007018000207240580c01002e00140f40420002400 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 711229829 1250 711228579 711228589
    0xf040506060a03200a180b0942060a09090c05070b0601080601140a020a05010e0721060f020f0a0e01110c13020f0424080f04140705060c070501030b0609 67
    0x120120260044910003100d800100f490201194442e18a22006403807000140100390800004a2411111628a070301d44291562249c5c44018807000341007241c100060107090340c070b5590600c0c0c00b0004006c9800500d020040b900f558041002d03000007030cc010b103090190468030b02c80c00102010070310345a070410080340e90302e400c070042c040c1080d4144a2204000342c4c450780b00f10303481204001c86000b100d49428442e40c01a40d10540c01404407007079400e1858070f040d54100003803004103d4640040c0001c1046010140c1944c02201401c107440941c1c03113a0081c0b4295a0f00e00040c03861a4031204c400e40d50300d566034030040011075400050342c100440480c00000b0140001005e2480210032284010342ca0102e54404009201e80a003400702820049000560441c072800000003103034800d000c207400d00c12100300c125441d080480341784d0501e4407560301280c0811136a01c60310b0600c0812108568600d5218800104180c00c40304442c441d640c0703c0030080c856940c0c107000e035000880041c0c84450070040080c00240b = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 711231079 1250 711229829 711229853
    0x140303040c180e03130617161d04090f1b0e07031d07030f0b130f061d1c0f0320091f0905211c0c08030f040506060a03 52
    0x3001540ba580c90b903101c101d040d40d2081e484040c0c020708a030b0740e035161072001080540592040401250f08000c4206444e0040e410a600ca611241c0358102041c88440054403a4480585100030360040100050030300d49581c894442142d006010001444400b803500c103800c02d81c103502001c0d00e01e5110b84200f142001819071503802841e2400e011400d0301a8042318641d80100c0000c119481c42401000000d0044122540f0103d5004490581959035100134840920040d008010038007035500d428800811055400307410702e908010341c110903102002e490903140601350308400c8202c465501111250703581002017040145680e003828031002d0282100000d961408584421240400054090f142d139140108414051454a100c580c0d000c040c41d001003101c2c02c907000d86800340300c81c0c21074000303500c40c140c090001e90355000e002070910001c81c00f64811846120380d106414422030003a868002160319001d035114031410706118540d4500307414690314060020300441d000b600050070620102e0340340c82c800 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 711232329 1250 711231079 711231089
    0x902090a0c17160e060a080105061c05070807080a09020a0e040323071511030a0f1d16171009050c0d05160501020d0e040b04060506070b04140303040c 66
    0x1071410031041050721841e04070031a0041105064007001580d54020441443c1d440e510780d01c00240000d040d05000302c61040e5600d4501255881c001003115142120003828080c403801c0340c41010b6444800b115003540c50580c0c4c2100410400810060307581c0d4030000c015489402100e052105100b2500440c4900c4480d002c0c01400000f110006000e150084e0031140350551020111a00b203802a005d0507184e81150800b124540d1210072144240d40b4507008001065140680c0c5500c0c0d0344a0031250380060003030554000103d82c9419603200c1140759400c0c41c144980f040e130058010000e0214202d0300e03920b190703003010307240c4400c60b925000a4100000c4240001c00c1c011800900c44945007441450a0040c11400c2d80c0013020b58a030004005010075102c14280460044807060b41e00d40c0c0c01a61101042c17030750000002d04d4034004100c0e9190503000b01d050010b000c0c0001803050b4948022a51a50014206840d80c119040c140401c00c0640c4c00c18003d1001c0d00006941141000e41d00c21030800124410 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 711233579 1250 711232329 711232331
    0x200f01030b1f1115040305180102070e0108100b0a0f060503090a05011128020319030e070605030402090106090515250b090f0601050f010f1701230102010902090a 71
    0x8000480c2c40b50500e041405402110b01c0c0d8001d58002d034000d20112800664502e14024100c0044021280c840c0d254003490345034544e1402d18226070380050b1410501016581184960b200c00110391504407403a138040d00c0445c014254016105051200f50f0341101030260081082c00000c012000c00e000b001402c0c1d80152a0a90762500e82c071020610f4103c081002905035483c0891000101c00100010203002c118001c141000c038600c9290068000000280c50300545c000f0004107100800801314454180120b040000f0624004846a881e2041e19000361020640000c00e0105529007440032a0061070302d40b412091482c06c01000c1490b13500c0480244100c000c022030180b40d543d05c18105200c04980c4403620010700c00c521f0400c0c000c015815120704055014000303040320081c102040c0036042c2c034000360851602480f850011101c80c1e0800c0669803c1003c0c007568120411180e400460080040508a04d06940381c0031441001100e4010340070306581c907166108006032210003c02d80e019000c00d42c = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 711234829 1250 711233579 711233591
    0x11030901030903141801030507020309010c12170112030207080613061d150f0105040603020906090a0b060a020f0c0423091011030a0c0e03030d051306021204200f0103 73
    0xa0b00b07a03800312500a41c840c044c1004180600802010304e04008080800d030790078021500d40000c00c0c3d03185d202c0c0200217070008070866041808500e030081c5001c5031200515103070304140e02d040640c4c08071030000e0308400200903d0491502c241a03040210602038000070011f00a075044c82004950400429000140000d0b210658208110682145030000141030000d0743c11011005801000c141401c4584240f9a400303d800440c0605082c4a00000d032940588000240e0315580108071404a000305441c0702192a102c0240c0c40352200006032021207440d0700101890081d945500b8105210079540368003852038090038881c03498801a100314004010001d41c20381ea01c4485c016810401071030b8450354041e0a0508072035151120f040114411080180700300111004041c00702c03400c020742c00300c07203615038400d21984e0000742d81a0b0000e504a80300d02c0b0543d419640b5940c94805070780000401030001d0f4552400c100900481e5494140b00064000c80c5043c0044e480e0001607400d1708040c5024101345d6070301 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 711236079 1250 711234829 711234833
    0xc011a090709060c030210140601080a0203061e0d050f03032401050301090b0a0503061003140f0319020106050d0b04030315050604090c022104061103030705041202031603150c110309010309 83
    0x100410803903031401441403180c0400034808e50b2841000783da000c1d00107800c3e100001e8213001603100364ac0c01003600421400108171414a481210315030360030300690041c4c1e011100400180104084899030f107011014645900d060480d064140302d0f1100c44040300c0c06201090400703030b07a00c0001c0303030b05440300801d0025950450340c0225540510300c1d0890b54041c464101130040998901c540c5c141140d1140e042c0e1315510a00030401500d46c01c0c28081a1455407085c0403000c400540b1244822501c03001d8400000d00c250340da000103103490305125054681c00000004d200038140d01d03015041c00618561852911145410b0100300345100e148034004c155581d80c00e02c100454030902c148210030000d8501d052a0803842144506240c0c003c0c4180d17000300e10344490321082108003205803841178820f42c40c0c6604103480c00440a006c010740321b504030b916029100341103883c40c1d800c02400d0003a5002e60b0070700000d03920503480d0104860843c1e14150900000c010680150b020000c2150b20100e000e1070b01152a01d218 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 711237329 1250 711236079 711236083
    0x210b0721050106053105010e0d0611090f09192022150c060504020d080d0608010e030403210306030f08130608060306040f080c030c011a090709060c0302 67
    0x11114482940d800c0000000e0300a84c04030103000c4030070015180c00d03d00502c0340c440340b1880c0302103402201080c07010320040116602a20b01040e5114004e04200c3c1a00e071a96101c8003203509121130110348000c042a13036102070405203004d5243c04019140328600c1d04000d8081510a2004101c1c1840315464204000004504544808103194411521601c0b460702c2c401030892890512400d100100c000306000413507150003041f080303c07a042074903440c405400b2902c84101414000b0b0069070040c24510300203000500c10001440c20034001000000c6030750400703144609480007039800000662060000344085141a04100341c0c41ca0740000390250300c1a10401030f006031946900243c40b148041c0c0380d200c00c0c881100d0045c034203401d074501c9902c4600e03107a403002e41e040c0c882544d407150140e100000103800a4840805100d415001d03900142c24a0703040c1c444146994401c80340d400003651514203030f0016000d001d901e0545800d0440d01c1100c50300e0f1540c030080511410b0f1140400704054a9180701c10700d402 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 711238579 1250 711237329 711237377
    0x50c0903070303090504231302030a12050c0c03061e0901140405030d05060a03030e0616152a0e1504050d0b1501180b0f041509210b07 59
    0x54196150181c2c2d0b800d0181450b810742c81101d0080c1e0402d00451000c0c81c03102014810240345000d000c1151300c5400d119a4150341e1144100e80602c81c2c034a1810108081986240d0142c58540e42d595998080102c0141030a20008080303000e0307403041051006441c403101408405205040d0700345056a1b0304204180908070600003204101200c1061005001000c4020683e80b10780110900080c1c03904014061000c0c0244070146c001820304804a0880c903116008101c841001701036400c00340080d0711802901b40341500c03202d244690340c8200e03640d590504200d010100c840302c01703480c03d11200d821015000240c50001203101d001801100c0d0102d040d0728040d01c01415002e0401207180c0d481d0701d058101d84505442ca10702c0c1041d5011340c06980d41c400ca0301c401f845000319081d01107107840c111780c1046c540c000c060800d030124070520000c500300c00c003056284404031031769417940c00785c900c0c009070307006840000e0244410f5940c40d09100e0021a50130024650003030464078105008007000f00310203e1100c4 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 711239829 1250 711238579 711238597
    0x6060108060f0d0b0406050402011112160503092101060504061a071a0c18032d03070215120105010804110d020d050105071116031a090309060301031506090506060d050c 74
    0x2a56045c002441b007941d015a00c580e05c01c3e25405198034400809d1940c600c00300228a400c0002004040a500031000d0714500541c450760450303007002c60740c00014011515401c0055000d000c01d02e1141d807114400d0181c1801072001344d0301046000e0400c0c0711021010411001c14180d00400144c21781000100440d1000c0603800c0d8081d0350640c10240c0c240c0029030b00a03203094003d03c1c9000d1100b080c0b80740101e1106803900e1400002e181141c4c1d200079508074500040a03480d030300c2c0410b202c80400b42c0c440d07584060880c02c00800c01703035448440c2d00c07080c1e042d00720682105040285020030000081d6400420014802c000c44401451170300e50701c000b039403100e0050001055175007000c4c144100980c010101d4105140c0c0e250a60382c0c07040c080301034824440414800507040e02403100509600c8000455070a41064480302920304e40600000401d5403940203a00c212030074201414580303440082c0c0d00c9030718040c00c10901d05000b40e040072000903070305000d41804640c12594075000324403140c008000f00d5000311 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 711241079 1250 711239829 711239843
    0x5060a090305100603051002121306150e090d0504030804030602030901020d0204090b0109140a090b0a03230c04061212090320040e07080a0f050120091206060108060f0d 74
    0x25004039549006081c8500c0121b0b1680b0890100c1242807699000381d5442030300c140c2d201482a501c84464104c00414840d041e00c0c41c40d07550010043c8204140c0c8590050b20340308407021814240a000a031400c40514802c60401006000500000d03a1050480c1d04490300b1150140e140e85803420120700a10600c8140b4402c03a01c0000e00056154154002c9100604241c84801c030088e540d40d102e03403080110382903107680440c04003010310415030681d004040c01900074020480c100d03100e075103180c00700d800e90700c44518102040c030b000144250704000b82030013903100380c6041c0300c0a8038080002d2310888020314014003140c88030645640f118403564951004680060710750300138611180310b0208445800d22924026070601041400280c80010300b00100c0f45020010110403125403209041c0c2c4480e858119403d549a5180c0e0611980c0b803203620181c1c000b100c0c20603a5852440c010424100e00141c40c103c80d540100003040850707a00240c0c55a400541945d82c0c081c00c05508002448241c44000300038403039 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 711242329 1250 711241079 711241093
    0xc060d06151707030b011e020a020925140a080a150905011d0103050a06050903160b012105060a02031803040f09050f3601142e05060a090305 62
    0x5980c00700512410400e80c0b54209940d40300c401085040e2115114841c4c0480c0c4d4080010b54403890424565029010f82c1c41510b50401c643d0b40020f001160a0b60030081c2d4480f0505c00c654400002001102c01401c02d051818003118401c250070250f0080070814014000034100045141980390018103140054401100c0001d0711503500c0401800280074001c030b01500c0101c109250b800c03e8100c1c41c140e980290050403180c902d90303291005040700800200c454002400312007080c9203244c10120341288a4215070340c2c19818142e00c0d4400c6980240798540100c14042da20b40480d4021600903000f01e503601c800750b644e55032106952010070804605900a2000183c00902d103a8110b10b11825148401c4050225884458400009440603113080c1804101c03c0c1d080940030090441000060840440d4014042e61211401e4211b440c40907029a072401030f4410001540d0800c120003140020407407000c0ac18074940591a00c4016890107042c0c0581f4000440c01a041c0c011072a450085500004840300 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 711243579 1250 711242329 711242369
    0x40e0604140106050f031207020604030f0f11040911040c02070b0a050c0607030b01080703150b160201030b0a0f03031202070606082107030c0b0a0b132405030c060d06 73
    0x4074a0710111000c059440c3c440c0205442c500381d00b594804038070050040135803e85106901d5001c0e402008106c0e8408030802002002840d0400504102401800e982100408030f0a204c402000f28840d810310403407030f0801080018544000e04c231981041a500007070b25490b0035000b68640101074100171841500424400e1039658024000c004840349541030b076440c0e45030f0032000e8090ba207090001d5030100d044a40020310307e0307119034030808440c81d44500000c101e55488a144100d644882052044aa01d20350740c041956014007e03070403100c00564a1071191031500f0021282900d041c0402010005000d0041078142150340503039a00035040030040101c1982c403101185c0e10300b41c010305100c1c0e1580440602c0880301c1c0301015030b5000e5416841c0d00e03100100581e2100c0540304018074203984c00303030765241084060b214000044000c109002c4001950404040c603480300402080260200b0410b100c018400c07610045400130070304c101690031b1030b100c85d041040c000140c0010341041d07030780543c041c2e00121 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 711244829 1250 711243579 711243593
    0xa050f09012c1801030b0123041a030105180601142b030f0201060605040b0309030d0504030f1211070f1e1a010608131704050d0b0f010b0301150509040e0604 69
    0x103410070448030805688107030f0419041c416000d12014042c60520b40040100c0444600e1040c85151001394240700c0321a244000b508030740c400070a481e20071048041c08121070400344582c03500280488180d195541908801035901c290501a004512031141c21103c41500c03038000701142c81040507030030790314544159160030407014160020790000f003684a0035070801e401807103900d0a40f0300707541d540d0386480d06000350800145d001030045021480208014818000b191003510300952007075462010054445030024920702060f0b2401419a180505000403405810100c0e100154410640b082081040c00d0190007800369064840840c003041100404000e11041c0c070300340a4007400001b12050740c856004462011089403101003643d00b14030020b01007000c0303003150044c00e00741d0084180307000d44401c080f441c08403c504040340d4003c2c4001c24000d03050f42c0280594054186d88221604541c9480300b4416010600e01e001804c1c0400002c15241e60b03110354004014100461084070200e003007500d8075074 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 711246079 1250 711244829 711244907
    0xa0c2d060b0a0317250f11060c06070207181e0b0f030703030c1e021014040f0603050a06140d1410020c0c030d110a0201031a03060405030a090b0a050f0901 68
    0x2003502d440004405256180884c05c01800790b00640004403898440d644c140f910310700303070b524036138040c0c002e20107014140c0c0100700540c0b0a150503130190a02e10b1030165900c401754804c00048940d28249201070b411000d40d0400e01e280b12140503000b003241240c07400411000708a16210343e4141c020300d0740120605400030642100719110340726005140e40f100303a54800c5032a140400a60101e40c05104140c010b00c24002e505694009040c42c9203015511410915a0001b5901a1011980310010040c51144a05c1424000c0210416003251100c803078000964030352403030000801010004c042a10800001c03c14030100040c9080d0840d07407081c1680d8025036070014448940d200f4401c80c844203410768420f5642942c0c00303039450014a099480b80d401036000e051a000c4140e01070b00e084000c10703000e540412885014a0081020b1660740c1491440101054451f4004002d500350070800c822119900808490320142c2844800d9144c245003030040b100315849411003c08900300c505070251243e8942d00d40 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 711247329 1250 711246079 711246097
    0x12032a121005090103030804170a1106010801060303020309090a0207020a0f14121f09060908091002030c0606040c05070c030c050a05011e230a0c2d060b0a0317 70
    0x94006599480c10706042600140255500000c00100400001c3d019920442d0080c0c807506203001051135180001c001604004042d60000d00b07130b04416102d00000703104030b9000d00845030007403082504684019682e4880c011205000b40305031400200311030441d5059548a41d0b00415595405658404800c2107407110b000d9000c035005504035146c113a240c4006940490703982c0f0b8024104809a590107024a11000c8010000d02503d80000f034001030594840c89000d5407054040d81d0f2148000740a2140c00c2401b10718a2040d5481040706030001000054030300d501c408200c50102d103039510343c1421a064020b008009003062100200403042114442c0c40354140c440c140c0f40a826030356140011600d0100300603040c0e020312141c14010f140244079100e4520100400589a4100307600444000111740c400c812034000108145415400c0050800400340c061803418015180c1a1089171944010486044001d00107559111213803d107444400c0000000c54110000c08101500c5054034230040d8004011 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 711248579 1250 711247329 711247357
    0x2202040e0a06090216060c0504030602040e01080c010512010312120c030902010e03010b060304140309220c0e03030d0f15080309100206011a0702040204121119060212032a 75
    0x104290f045031081d24034900780981c000e4107070b5000e5118131000344402d010000401008120201c00b1441c00e00083c001051810005280c96140c403d150b4200220b1052003030420404114200c203800c040c2504506581e08880e4049815058a10542d42d03002e50202a00c002c80c2080f0305001026090750080c001c4500030307201d400821b41302000301070032200c034010002c1d40100c3c1400800c020071424250034200054200c1102e00d840c902d40001038109403204002060b50020070400d010200343ca00408804401d20f0404038050501800040e8490045070100e640040e079803110f14102980640124540d00d4a0f9007100c503c80d070315031006944a074050a54039028040c40480e03c0c1c5400d200203000380c101d5150207010000d00d940640c4040581c0d000300004c0e03178131a4091001050310700c0040c2c52981e4252140660700381850304075061082c000c1c200d04950101440000382044000d4001c1181d60401178400c2c8542e1b602e5584c015101d4400110058020707184c0b001392100304031208001b00820345c031820007107 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 711249829 1250 711248579 711248591
    0x170708040b010f0b0d0b0625170403080d020d090605010b0717090d0f031707031a120d03180b0f100b0304030f0e010210050c03180c0d022202040e0a 65
    0x1c183d181c0c0180d00d1003159100c2c0400c00005031110703043d0340310044100c40241414541004010212269414042852480c1c411aa1104100400c42180c40030303481e40801c0c840d09040c41c0d9220080c0381e0064203c02c2840795000a102548881d06501102c0307002c0c1d21140800555855116414641d0040c280c01c039413020300b0520304410070034218152100140010300c0e10401c44041d9a881c1600c0040400c100c090084d2000140b24035440703041410b2060074960360025420050440411100204d4164030b8050004105280c0c400400441d403401a0450b40c1008600c03105400e0710042170000104025140101031000d12100749014480ca9000c0c0e805151030007902078a44601c604c2c91700c416640100402e050340152042d0134014819009050414010345805506101c50300080d910200c50001d1040d00020405c88403101d0655881036420b01a00200f451215800100c2d041c2c95640d40c000c0d21500080f0308044200b605a0340412181c0031000040d0b4955650b0b0481c4046040b094504409041c2090 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 711251079 1250 711249829 711249839
    0x1e0c03040201030f0e0f0d0309170c1e010f18050a0308090c04020f0306011e0c02040906060b0a0932060f0702030f0601050102150601050a11010b040603150501050909120a170708040b01 81
    0x100412704130302e801260a0700c03100c00c85415001a0f52144007140c4072402041e042190f88400d8160000f600c3d02440004607144504941104c1141c500340503120300500ea1040b550003241c030002d0b851101643c103050201a50f1500c5e100ca904d01103500703180d190300c00d0000820105075543e48016500854003038030783c00c0044d080300c1f000d050400c00460201c2c001465000901d009031810b500715402d500d00843c00003c0c41e645a40014916a1000704c1080c0403c1042e0381c200070144015409444071100c0309004511242c030300e6040e03030420941020082c03041a0100e2005a110840c03021078030101c2d80141110544825480402c0d1105001d100e664094001c0a10f0040c050b5041c80b0381510800e81659594602450703a00280c1d04040060700d8034405668038202c00060340c4951241e0809540240008802c0108980c5c02105031b40c01604010300800c080010300c000c1000001e800341500d190400265100c1c000c80c0401ca81021403418040e04104044051000c20b036001404280510300a801c0030f5503076078070341c = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 711252329 1250 711251079 711251081
    0x61a030705090c090f090903030603061501120b03010e01090b09012304030302070c051c230a0f06020d060e06030c03010b030c121501080f061e0c03040201030f0e0f0d03 74
    0x644615030b0000403840000c0c10600c0d03108001d0186020080288040c0d1804d20003003000e4840441309940325034000014807034113150030404207902c044884007543c4074400080000700044c5810441c0c0d186103403100e9440810755003e4015091410040c0000c2145d0445818400b4240509072600003403540b84c040717044640d60080040b041007250000342411952202c1d54200c009500424080da6a50b65070310703010800b0f548c0d2400e000c4440180d00c0c410210a8450700700141c10001c50300c150506440038445003c0302103004200c1e10507403a0404218038011040d4100742c2c020740304440c0c21824a600e0b209010920a02d00010745004600079402c8440c0e0b505031509050884500b04805c0303a1552150712203000c41e203031003101d00028054a80940d8000c03c401041003034240c400782c2189005400540b10b110092104000d06644240d220340d40044214180701ea2202d400c2e0b014100c1d0f140150000f00080646e40203030031501405241c1c0f1010402c40e4285100d46480d0f4020611505481c090f030074082c5c0c0c1603031003 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 711253579 1250 711252329 711252343
    0x102718050114010c02030a0b01090c020c031605153609130210020a05010e0102042c0109050a1b020a020310020f04090207020f031c0801050d2a0b07061a03 68
    0x34080c802c24640c080001512001c01003402282d061141d001d1420020f482c24181034004c00c1c002c0000b0a04259100d0082e0905801c014024026400340b840c01c8880d009550300c5078221941540c08282c81c4501c81e030814418412141150300c8600f20640c80b4425a041d004525001e0140014180c0065824020003c140c2c1c0140c2c0c02280b410f50001c4400090b140c424103400800100e03004a61105449984090a413540342140000ca658085002c02002403203101503404100d20880d503601e2181c0410114400107018000c0061160b6940006000c0c51000d40c0142101d4481804484074088407117002940e500c0207000480c028007d40030102244140c6000f5034141c14003207258242010b00b40075236500250404903041c3c0c0c1c8040076040e1f2040c142c80501c0210005024440c80e400c00d8441d0f40400790410300c041c0d000c80e01450f40d078128540440c05000008c4030b2101581a60820f117401a2100c0c0c0c0302100030340020110031000141c0c5010480c0a90088255050415842c0e10546d144800c00d034440314 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 711254829 1250 711253579 711253589
    0x160b100608010e010e0411030f07061d120604060c02120f030a1109060901110111040b07030e01020d0509040c0c082d04031101050717030708180f0c1027180501 70
    0x16034030006c100026600d00d14880a118040c0489003241c810001c000c1c0742207400c0e0b000704081000780012540d00d0802401c1e05880c0350b01175815210300c0702100c81855840000500207403241d5900c0e43c1d51795509109100e82c0d480c403107020200300c1e11203641c000b661106500c2607880040c054175194004e0001c060080c10303103a0034007004103814208005440155002041c000d043e010b2956031f0100d0031516040607000d0005070495011190b16000300f45006440c0700700459400d4155405170110702a020350080843c0d6585c6d906890221340704000200641c2c1c00c03003d101004001c040c01107412981d103450344410501e00d01c0d80008480f240d0200e40c0442005100c5c5000c050100000d03c403280e161075000e02d005080c2203200361600c0611801c00500701a40c0c0d0003e4404400203440d00e0144901004815040c203020203110340a8041440044840d603035400003440e5980c05031541e40011007410340110710001c0c410116540c001001500c14028014400c8c150145101d1250b1911101d0081410b603c40c06040e00c2e = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 711256079 1250 711254829 711254849
    0x613020307120314070309050a0b0310090911030607020102093105061207030c06030c03020c0c04111b011b1d0d0606030618231002160b100608010e01 66
    0x1504210103484082c0b0040425418070052203029404060710341c0040c0005130103a601c80c0d0f101c0307003403c042000146443d0f0010010600070710034442d101c8052040581218840b00740000c1290003445c200c034040b030f2140c00d542c5d8140500c0c420485125010340007071424000454102e000105040d15042c0444a5007505107520000342c1640300c102c03480c40e0b005070b8200741e00134111420800505811031a002c115003040703601390900d0074208207642c0c041c001c114081d80c0c00c0c1000e41c18900040b0746241d90361785000b14284159114420780242044070f0742100e104000307a1614000c0108900b80080c00707000600b0511115111424040300268811001c00c05d0454068001c900d080c40601c007001007004032100300307840603580c41d20000300041c0d023441248203980c65034138140c20201003400c20010902c0c3da1021040250300011200448200201c1d090030381c4512030380010f0326050181148201d480e080900180880100320030321000c0491610350b102282e2306641e99103c0c980e21545401003440e03080c800c04c0d82d61 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 711257329 1250 711256079 711256093
    0x5010c0321060512031c0204060c06092d05061f060806060f03160f02010b0a03020904140a030504090b0609180402040e1902030c150a0507050f03030408030906130203 73
    0x14032510103070400701e40d520394804900340d600c0e00006440128819041951070b40001004030304e5030303036154101c1b00c98282464118117040c034040000d4450401800700402c0981d41e84800000c0000d4032650b1881c00c80c00180a00c0c040400f0716442160403c000b000380d860b4480d40c1c1c0001d181d204810a002503032201310800c0c190703103803130402d081e1800c201c081c1100b5031205c414080021008035150180d84210000b10906850015000d000340401c0702c042c00c44000c41e4146000e40c0b0301d03600c80400d0141141d83c10b0b0f40c0a21244d50307505041d06001807645000d4054002c100200c0103042d400303400703001514900c4004101c142d8201c02004a0341c403d8541c0d1540100303000c42c58500c3c2c070b0180c0c40001d07031007800540007007000802c5004a03410030322801c0070802c0c0c2884a000c0030041d410100000660400d0070347e49558010320034840700c0e409000b0041c80d0000c1010004040c02084018032880d814032821608490b12401c0520341301c0c103d50011281c1028070b100e83d00000d0b44920883c00100d40d0306801030003078005 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 711258579 1250 711257329 711257357
    0xe030c0d0206131d011403060903030c09060403060c0305191b080c0723101415030a0803010905190b1e0a0e01030c33050a0306050418050705010c03 65
    0x7841c0c000d03003003040c43c5030380030000000d46629039620fa1499403030b40000f155196040c10001e0300c00c4581c130312000d4000c4d07008d5030420048400000860350001c041c482c0d81c9448078828400030b4614402c5070801400107040c03410580006070150840c0c1e02540d0b0300440c44441a02a034030210031582e04981200c0744001c3d10181c00d80050040d503106400000c401ca00618210b820344503e0710201b54002c4c50620f0780a01e1180c485410b0003030195120170b8001400074051140b14481d0303039841c03038006014542d030b514103501c111040b69420000d94041f184c1c0844025120340e554611407004000495662119030403420317110318400350742d1080703c072042401440400400c101c452044025000c1d0074501c0d401805a86d03010512220140e1790320b00031340c811405500d54506000d001c45407181c1e003c0f0326285565901504a84807401a0070306c840f0300c5003c1c50456110511100214054052640310680043ca04030350400c0c483c502c1403c1d102c185000d4801c85010603614030045410b11881807011340007501e01d03501106 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 711259829 1250 711258579 711258589
    0x303130302060904090f0b060907050c03040312180905251205220b095802061f0b0403080315040c051c060b03010611210403030e030c0d02 61
    0x83c4801d000c3c100084072001941c521258941208040c1d60b403100749800c002d003510b01182c0c003980c00480c600d041414120b0390b0f1800c958038025404000e21041c007800102c405103111b07465404206680001d0142c1050707640f0700b05801408103554160901c0000c1b401c1c0100e1121a11188040f003c0c90fa0701d0980e104000305010005140191400b0404210b40f5610844807024140ca6400e03d4000c3c07101000c141881d0503521314010080c44036007085180385040e614201d01c800c8251641220608503014511205000c00c8202c01b007001c602400340d407400c0010041c2c2c0d83e00123141c900c40d1142122414802117080d1002d60b415907107102c0c44180c030314204814030009803444059034009894030f8103945290741000015080d28101c0c2c151000040000c101da54078030a0700c500d423800b01748940340e0802010303040101c90710042c0300500401c0140554218001e6a400c400c200300300c001c586916078082a0308400c1d04a1203240d10901c402d42c0010041c042d84a402d1034046010249008000c0c80221a0260395003448 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 711261079 1250 711259829 711259837
    0x4061421070207051f081e0402010f050d060e010311121902030715051e0301030533042303090d1410020d09020909210d0605120a050c030313030206 65
    0x100443c0100000014140c8625188225a40c0c02d80d40642c1d17a0050504000c1010350024840544400c0c0b0b00d1aa4081002e0305094640194086c07074412603040359020103951512030710b501c2da1010b502e006000200120400702641c16a441000d04010b841700e400200324200074091800303841ea402900d03000203d6072494002817601480a410380d10341e160354a0400c00080c24403041640881c40000d116461a00c482750b0000e09540401b00d00303420740d411602c84980e11010740040e601200106482c0c840c060010a03200500780005014a840c9442c084c0380019040c00314002141e03466040f200c042d856a14080280e0380c0c13080307024040381401801d549464110341561a04501c090161030300c009440c0f6540d000804411003500f4001c20030100e544140110044001c160403115001010030b04480c03003020020340203081030744140c01c1e11440707007030390403030040c07500798000c0380e1000070321000030a0b000c00800d08003002405071050351400710f0a0024180c40303100700001980c00089031141030006140000280c = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 711262329 1250 711261079 711261091
    0x1a150415030c09060807150c0224031e0a0c0c08030a06030b090307120507080d05060a0503101d060609070c032a140313090b1c030504061421 62
    0x10320440e0341c0e0b07100c82015124981242d00525200c80041c0030b41e5000b00300e064001d00b1010103c40c0f0480c1318070001850001c1081c0c00900c100b416042109003d040e048428102d0790501c1d00c55580ca0a00640c240c100d149031010540c11b9920480c00134240054078800c6034402c0c0c085444d80c4103941066580e00d0b2290344014001001c481d03960314013002003200c114141c1e100b4100758004595801580c189662080711b40c20401c010404204031803000141c03144103890480182d00408606911200001800d082281c0c0205415200b210484224496150002200b400d004103014074041d100d481110780341c01c0b0817202c0540041c0b125000c240301521461a040d03002c0c0c06468245580141c1c0c05020178100b1078000c000c120945010705c07050900414128422030341e50244015407070440c110450020303001c0c1c980700310130b9169600d010140300364070b8840c40c5008040310b81c080007a050721281b80107441c60708180901800600b0700305010b103518502904031220034803009003116080303090040d0859052001481 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 711263579 1250 711262329 711262361
    0x112060e01242103090b0304050106030215130b070804050105130905180607020c01080105010e0d06050406060807080303010e0a0c02011b020106090b0306100e100f121a1504 76
    0xd00707005000c6040d4002d914100c108140e48440d49044800c5550030039044503c0100c400c1000c0300300c00a030b0001020b4046a44241e41d880d143d503a2402c0ca0f600502c2c03079038000303134010a51010781c044a2504600915891640c0c1180340b80c0359881d40200f91150041800c010001841000180401d6015502500e4105420b4452860032a10340c040311042d9981074911a80040a01c0101c2852250034854942d21100610041c0302c5158a000000e008407018881e407411f000da00703462040143c45e42807081d04c80f9900040c09000e00d0900b0714080005118074403941040d4021070002040d085030200c11a4100c454902802000d6214403601ca0010040b001c040401c2d903598081c21410440c561131103048140c5182c00000e5401d250405041c1030321481058644290885010484422a00f444e50740684400d51900c601c1c0d82c0d21a4403c4201d000c868000344415604060001901c400e09940e0844aa106004c0032048503546581c55441d1031060310985c1d040f80310444070f50704608140e0301005980d01c800c1d43c = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 711264829 1250 711263579 711263591
    0x11120a020304021f09031103010c080118110f090312040305060a110d1b09080706200c030f030703180506091302040b0a030b0f12030f0904062402070e0112060e01 71
    0x20084580f6a8244d080c80100b04006000c00600c44a0303541c01207503032400d83c024042c80e00001030040c2403141c140251041c0b0300305442003c0386c00000fa0310440440300380d41810350b600c000341e107032a1210350000d6a602c1d10a208141000103002036003015a801c807507121004203035617200e00302240080d10701204401c1f8025001d20010300703000d600b805540d0003200001000140c803e09540c0c010581017554202c1c084c03070b41c0714440c20000968480681403c00500c0c10380d01e03074074845000f01c003403c241d00444c04941c948100050526000e01c040003e08100e03101e40c407628400d494856800e00f5002040c85000c0d444042480304800c40c6c00d00e031a0010001c00458001440d182d11f03500c5107115504840801c00c0020350b20314005440342050301c0d03500c10803442100c08501401c41840300a50305c0c490340c440c3d15030f012008100214a0340351500b02d400074009401c3c6018018045080c03a40072001311000100c01803252000010301c81101e0f06820303050710a0f040300440d0800440c0c6459001c2d200182800761950f40e281 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 711266079 1250 711264829 711264859
    0x50601241d04180201080f090a420f0b010c2a0906050315010503060c0706090803072d0e0607030504170106080706021204030b070c021e010311120a02030402 69
    0x840f907651000200c00821400300300b980001443c1003130041814400540220030301180941c00110454103c1e4030050b1501034000c0c0a2110380f8500c0d021002c0d01c101e200c11600c071500c42c0800110b417a406040800c003080003502000380740056a0710200c009010640c4065044042400c9035400100070b03042c5d071121101d00600920695161042d1b92014111136078824061046203014840c2c125100c541846000041d41000c000a486090241c504145c069000911000b0446150083c0c812182c102146548903d8821005028404032604c50002c0308503840b1103203d4841040030340700305258955241c40741101801705111050b0311641060f000d0040a000c001001c21044440d1040e1148040002c5110b901d1310b6a22441d001180d0000825034000c0c15514180011030021341d0200d030341140640b5076640790403400792000010b40d040a900710000d50b00c1d014107070700700d000d01c031050241c2a6410448260440d00008440c040d1801d02d1809901c040040b6071500b01c02d402560700a40001c08105840700d005e = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 711267329 1250 711266079 711266081
    0xf011a011115011814010f0b0304050f03121603091203150905040c0509010824060f0306090105070906090602060a0e0c06040f0e061e150d020412050601241d04 70
    0x13603110140c0006201d005001c40111030107806100740003000030a8841d410081c0304c0603959240e0203150400600440003400f03011082106811145021050720354808038000b540c0358ce1401243c030490b0502c8454640c098a62080c49005011608440788030080b051002088010304031503106034180c43c181c050080f41040c414801d03507010780d10580201982514080922071040b00507488001750f600441c0141103900005403080c5400028208424003580d9600001907914003052181501841000c0c20000b0040b07055200601035031946d01e40c4520203a807590200e030808030034003c0000682102e40403841c420800d820110350000030710180e40202c0070741c0000c1a61034015900458403448455805c2000540b24150203800c84001c2e00c0c1e40c241d5656000c4e0b44000d148220600c17900503c2001011a603202005041d1025440d013040c0540d600c070342e00d00410060789881c072000d0f5564042c0720300018021003425011042d050707006c044032202440d101400c0d11192810303140c0000080801c007a0700c0789642d503 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 711268579 1250 711267329 711267331
    0x1d1504031e021f06300b01030311100c1403090f030a09090b06031b210910050a0c020d20030406050408010c0f1b020609040504080c0f011a011115 64
    0x105070300504004145450a941d44a0070740d1503081401e00c2c194040c04100e200d404494055101130b117150301c031260711401c0c0010030b03006140090b1142c000e610000c4201540900c0e2140700907260003c0f59200240000b03014100c2e4205103040d00070983d214032259400c000100519131204c0d00c2d90944045075501c98a441c29584604449070000714203c0003888080c006200b100320000050712501d01314600a401c071841c00c0c0320700c0c8010f07603400d8010070040b404258080046048920301c4084003114107041f00000d44e10104507140341c22031810840081c2821200303103c0e08012181c16070082c035081205000c151b5500e14202064024000e4061000fa4a0340b01000280020452540d42c1c80d5250f00c0d00c5002801c41d09035944001c200124004e21056640d80030040c1100041e0019148901007128400030380648241a40300d500300c2e003840c080005001d41d1201806000c0403200a4412800026804238200c40c240c140141c00007811250205842d4490700f8000e08407440341d001c548045046200c0c0005c6914 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 711269829 1250 711268579 711268637
    0x114190f170c0406240809030901051b070305010f0e03250206040308070f11010f02070603020c030c0708031317070e070e041a0f01030e07151707020706031d150403 72
    0x41911290300070642040c5d02d01402c900c03032400100c14100754007441e13100d210710a1080d04008000c1214000380e601040604548001c0c50b040381d2000c0d42d6483c00c40d002c2d01031350303400c5003180e440c06903800c0c84d07000d010084640e05c1c0486580e02c10b00c0607010b0451400061040300c1660060300500c004000500c111004041050148607000b0704800c4501c1c1542e42000f05d250340714100594100e4903030742d4a4000a0303000685010341801340c2c440309d0b2000d48503c2c50041100010040c8203820002910031404030041098000c18501ca070303041502c840c2e8452440030324654031784082e40401801c0080044a0030307003c0e0411040e24095109640c020001801c3c0c1d283d07525914280300071890401110320300b0001d00e5006080a0078107000030034004d400c40e515010b1710b2142e83c554050500c242107100b481071468544018418051004c203052040d4001d41c0c03460b10f0700a103004640b600a1038181203100c44100045030925400400c111781d10502c1101070b03c100a00104d0500c40c1200070509500e452100413040c0f03503 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 711271079 1250 711269829 711269849
    0x605210109050a0305042102060306010e0415031b060513030b040f0c0311090f07200f12190504030213150905090d0e10080705070503070602030114190f170c0406 71
    0x4e07091241074245102c0c001f110b000d603840d0480010300140c07070309000e5070b9001c4000d003010070900305c000d004180071f4030180118007150500743e0004010840c0c000c0403540f03242c00f0042c0c80c01d9903589072003040d10540700d0000c0c2440c00503064402000096440080ca0fa40184144c1711103081c01e00300c1e40e8002000e103454004035586180303003040c007a0034142240801e50000c503802c106139881c20070250140a5140c043c207401c520085600c5a0034000204001d000e4030b90840c10220744042d905815001c4541d04408207405c4651899141218090720070b8080e24180c9800070240241000c40310740840060a241d42d03082c4880c00c40050029144d0600d2107054030544140e0050201814081c4009001024540c1824400c0c9142c03030394080303441e601520183d800070040c1811940d50b552030a0551541c055500e00030718450001002091181c81d40c400041820360942e04545450098101000084002d00402c003518041d00410000e1000e005104801e00000006460b420b803503c00c0803c041d82e00580041d1045 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 711272329 1250 711271079 711271087
    0x4020d020a020105090706080c0901020f06070206040302070803120a2706050114150a050307140315010915140307090302190314030403030e130e0d0f080108010605210109050a0305 79
    0x2042d0203000b101d910255030005011414106040a0401000900301d03034503e40012076074150590081180e54030703504014003250000c1c50011002940c030030b001c440c1100140504c40000414a1000040d90312448844141c0880307079403908444030080440c6440542c100e4840c85868800440407550010b58034001d103c0031071076604160160380002d0601380300b507000c2d40c500c0400290803101142983c4c0b184884d03180465594a80102c11100301440800503000c02000006011000100d2110007000e0a0281c030f4400c0d0080e5200011021445100c23040d4000c1545e43c40c0620801a2040046078048100e0402c00074035a101e8000c90350903403485c00ea51145544507107060060040d8040c9090312030a0714001940340c14103559004081011450b1201d024904c1002ca4480e07100007500158808000181110080740440000401c02149601e12202140b0f840c80045509503042c080c2c01d00342c03100680484104034490500c00d010365510301141c0813035542c40d808200042c0051001c003405500a50b40d068032 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 711273579 1250 711272329 711272347
    0xc110f1804050c1e0d05010902062d0a08130203190c170106051e041407031a010504081b0607050111041d0403170a0b030f2506080105060c01020904020d02 68
    0x2500380e044003041e02c1408042c00136a10144014500010a042a00e80c00303050803071450101d016059542009510100c003151405082c800810300e00722281d9045081d511011044440c01c00394480e40140b84c1c0050300703150000704c01210500e070b088880380c4050308507444140c02d03460a4600e0390744100100d0b0100c03c01c400030445044000c40000c1400b0140d0001c0010f1494507000030740385206607503907100f46000c1d0070002c101c0381c0d119400fa0303c0d030300341d0303103812001918108000070b0050610000703115402120040380d4100d0751240301504d09907200c10001780740140384455210381d011401101d903075014408001c1d42c00006c0c0280038100924100c5542d0316219410302006003c40501040000c2c5003c08100070000840e0b48005180700e00421105d881c1800e85030f007031020016068102e401501841004000400e1000000e00106c00504030f20381d24007200f0a40c094040308083c248101c0740000d102c000188400d01d800c100804c06404510001031400040c007010070240d0b0040118028940d60100303101e21 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 711274829 1250 711273579 711273583
    0x1060e0f010506040e09010b03010c050405190326090310060501080f0f010b0a031d060712090503030402040203060a0f030b060901082e0e06010b0706060608070c110f180405 76
    0x28014a100386402055810140032035282d0060788142400c203d0540003040104500798003024040c14090005d00c001d00c501d58014013607900a105a500400d01c10750002124042008160240c1e64086280505450002202424004c40100c0500345090410000c40c95540c10001d0185c1c40301c900402145903403070b1000240907508020f1030a04a48101c1c0c00b0810300b4003020b2500c03815900d000040300e4031401035402c2140180701c1402d036400314082e003110004210200182051084000346d50b080d0f048c52140d000c00341070391484403000b00707150301c03d1000c1f800500c1c140d00515132080380030b06419182540c5140801074400f00f940140c0304245100280030f014200032004a002d420004000d03d074844000000d000790329000c0d1000c0c407580c4448400c40714084110b4000c0d00c464808c0c503044884558590b0740003440ca030301525045941074603100d0005542e5000750070680c0f044415488503172030090b0030744230120180c86502d400d030391004004040c110950f440884224111200030780612403881c061400354 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 711276079 1250 711274829 711274831
    0x310150302041116030c0804120c1503090236010b073e0402041d06040606020c0a12050a060c0509040506010806060702150915070c050d08030604020c0709020c01060e 73
    0xc070716240030088100b003451012056813585502d07240000c1c0408190070454054050f9410100108010010003014015011426000e541006445544c40c04030858154115000454020340141045003401c1396209016000d00d01454814154008030910000418402400b40c0200000b82c00206d10032041c0b1050198611100c802d10703490300c1c403c44620355100035103008400368803044400d60751203503c03a4885030103503001000a007400385a0341034100c1642c0f440d0704c01120020700880c684100082c000b03200240120f2403020251501d40190b09003001018038002c4da50041c1c50510506c1b02c9800044c000d84952010b81129070307a1291240c05440c10002601c0004d004141040415424007070241d40e03450403035108542c1260010400c203880707101c1c41752038003850000540c4100300301010f04036400030300d0040400c10b03c1000c180ca165619081000103a20504c0d02c040c0031903e052000a038035040c96402030000300682000c862082d50342d8001001a42c1c8030204644050351203120400142000312440c03 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 711277329 1250 711276079 711276101
    0xc0a0c051c020603070201090507090e0f01020a050406390201180f05010324080606090906010602071701022205030d090510180e0c030709090e0a030e031015030204 72
    0x881200704a105011681075500000a0b02c10440000481c00d11030003540b0640c1001d42c48410303a4102c0b551112058010212a070600c01540100010808400c006100300d80c45503070240c03075550a00e400c00d1400c548400001d40031006052600c0c4403244500e8a48283d080100540d0319030790103918040c8001001c4290784502c041000c01006400d0001f141c10800b0704080d90000c0ca80041c0b071800351059400e442d03244440700b10001c0400b8201007001d005c04034202d44202070035651800103484841c8459600c8000b4407171140140c10880c414881c0000c0509040032008803d8005800d0035144060f13400480c89102068102141c221004c0259060510108001d6040e42c18a54880c81c90940403a0485d0701c0c82d4410005c200312140c44110f850b4040d182000900180d9100546601d48101004800e600503200300700403456818002035114118040c002c02c540c017200242c044085990b07000d075950109038890590501814110640d0344659200c0c23444070314030500203003040070f1445c0184421201507030301c8 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 711278579 1250 711277329 711277339
    0xb010801050712020a1e030605130e1501141908011506020706020c09040615031e0606050405010605190905120a060501060203091806040209040903030506030114070c140709020c0a0c05 81
    0x95100899042010356400400340d021102c0c1a411b4041c1c2240245400d810242e4409111840103465000035441020860078440880382c00288022070380b80c3d0b040c0d09200b81d2001c0c0c6004425441e450a1511250f9404e0320a00d5032510030944858060782076400391060700c1d22490b22405c00700044c0da81003002100038240760001d41014015040490b800d1000104090f1240c0d45403ea00320a00c210180064011500452900c00032420707100400c080b502c09031070603a9030302c2c1468400b00b400d1600d8807856040b6030440d2a00352816a064035002c103102c641010301414800070701c1002035a900c90a0800001040f4800508403101883c946a42180c0c1d040e04003004640c410b1001840a445840f41c3c19203031140010f440328141c0e2018000b402034413070103281c0760b0024185072001d820144c06030003c03402080100e000380040011440503100c004802c8402c5000121f441581a0101d0b000d125002d4a0500c4a0182c0303520b01c0d10703991100c0c20380c0d020400c200c3c990b511908040091083d40c00d038a50180c8000c440f = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 711279829 1250 711278579 711278587
    0x1218110103110412140a031214060f300304081e191b180c0e010816030905070806070f020c0303090411070609080d0617060a05040f0b01080105071202 66
    0x291031550f07029500848000c0000d1100e4602032001040d1000704010310340c401c07074020311072a2074020007002c81c640c40c42504600f002d82c80610102109072040c400c6c00d000c4c0110500c603110504214600c211a070034100d00c1d2006900481c45011503010664000035040c00a43e82c41c1e1524543c1c500d00410000c140c01035003503800543e514403001160380c446440d882000780044040078140f0b03a82c54410000e0300312900403503040008110f03141c01110700d0f8644074540c0801041e0b2164038103407003d201c030701019030000d845e00002030740c000d156560a81003400d032880e000039000075607a00d01d481d142c0f0a0700201507036031100040010307881c1c4c040406d02400802e44050034201c0501c8c070100365a400f5644c030a510450f1500190703c030400d13203141030b44c3c440e45e082802401504140d04050641e03920a00103611038078180180810303400c0e52800300d20340c0c80c400400141881d82d15401d0a200411018004603000300321006400046140742c00c0303260190944030000501070070803079400b8010f00c00c01c04102d0740d9180180 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 711281079 1250 711279829 711279851
    0x100e030a110109080d03050714120c030a090501110702040e1605040515040903030b030708150412020304081506041406010f180b07060203040611040320011218110103 73
    0x4110390301034660124001d980c606650005030703012180740c0c01503c001c0c800c450250103840d40c07603003106008030003a444449020b002030f900c42c1d05034401c0c1d512078a6004115008940641e84950085600555180d400901c01d016580ca06003900c00c0d410701e00c801c44101241d01c40562425116545c0b201d11803a0003006040350707860023080390b0a442d20a99202e2556440022101680040c540b03581c0745004104200746482894058014080404a64001c1c8204c1c200840c803c0c5000410084510181c40c1e09011640c459031400060704c20b001101d01140000c0c1300010f542001004440103420150b00b1203030151912205000881344901c000d8840c1c1c1518a06000c04d03660400c2248040328154070705598144240000a04d428109904c00c8008281c0040c1070344c14002107501841c003e501c90072052281c2c0400c11940040c5000e80d00011b040d000e13200303030300350b0350b0000007a0308000c414ac040c149910044002080d400440354a1081101303141145a11402005141c040300c00301c014013402c0c00c010414480c = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 711282329 1250 711281079 711281083
    0x3060a080a0f0605090a1406041209060203070f0606090c200a12120b12030d050f0411010f140304060f1b23190f0f0f05030406020f071b05100e03 64
    0xc0c002c050642030344d0b43c0200b001c1034130512101200c00e81001c1300141c1a0a402e0105030b40b4403040300c060750250043d00d04684050f106852140c102ca9007a80150306203d42612040380454003020210b64517030b03580c10300180d9200b0501487c010703c80d881e02c2341441f4a03d182140444848108041405500034190740b00000e500c40308405020740c003c0c0b0f0007501812100404030024000c541009510468019101039007940000080c4107815485030301740800c1e00d40c01c514200f03010782610000c00170006480b2a060715442060561010750303142c0b400f850b5081c40301c0c003030a034a9441941c080c3c964944464603100d66545601680301d40c94901802c03103004c00880d51000700700550500d50039140c0c9003000000050100544140e5660364450f41e07030700c2500b80b903030400030300a48400e0142d98041201d8450240403a4000c1f07821017400012600c0303640c519a40c82e61088004d50019000300e0613080e040c8003407004140040040c00940004648141c220b80c02c00081009000c402c0080b8401c00c001003610203425140 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 711283579 1250 711282329 711282353
    0x5030910021e0c01140a1a04110405010309031e0315050d0f02040e0307060e06090610060503010303121e09030801050409020328021207060f050f0306100e031203060a080a 75
    0x510003245440b00100004613014002c021074020140700d0481c280401d009160340034051100a207003150491281200c240001d503448460f40070fa5050050004010030350082c0c004201840c880c0c81c1040da6400c0c40c000704820722100c89000000070b541c032014a0b040c803a0030100c00313000d440c04a400c2242074201c0d9560900990034884024000c175140c446004050104201341c800c9154821020302121414902030755a03004212000d50103841044040b0304e01c102032150f14410f541c001d43c3c50900d10b07801c0d03850503143c115062900c0011560307070b03011925080d005003004940740d1030407480c003203004006820300a0008070180c01c02880345260207001c80042e9800103040b6840c40031300c0240e600d080b03800040c491401260000c065040000b01e511100c540d9008642003040d900d0070341300d03242205130308082150f2600818200e850214820404103409280000b07548501103981d03c0c00309841c0a40b0408207085c50f61818800c0c034140004003c1c8052494030001503006442c10f84001d000803440c0d030700c0d0345181901c = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 711284829 1250 711283579 711283627
    0x5060d030e0109080714090a0b180601090b04090e011a010c020d05012304051b0616020a03170405090c070803042901151b050c0118030606060503091002 67
    0x1c1d014225031540d0080001d100113180036401e032000d144d82c44920b03160310303481781405034841c0c0d0b503600029a04582d280718aa102c84809000c030b000340d01103510018449540a04082d042c0650901c0c0010160801d40081c0080c19144a010641581c00b5010509541c10380c0109150102c0b005031741a07007643d1210300d011a0341c1e01101d203c0c04036a55800d100d40109268001c658598002c140d07095442c1440e107034240d000c1c910071402c81d220b0614007070080301d64194410b10740385c0c0803504218018009040b0006000d000e40028a003000300c03540c1c4e9849901d001440c00e040d418202000c5002c204500c0d003940d8030343d809192003c00354900360b0700b40d0340c4040510005000616510b40c0300c24400090a181c002c0c94410907886c0c85040d2a5611640552a03a100b52038500000800111400343c80c45030b108050481683c3c04401080f000410500548005601019450031030040d00302c000701241207070150394003c00c101d40b00d0641d01d0030b00c0e580050401e818070007038802c03c80c010040d548400b03001f0540008210 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 711286079 1250 711284829 711284837
    0xf071a01140d1b060512010911090609040e010f1b05090a17071508040b060f0a03060b0d02060d050f28020913020309070603060f080a0b040501240e0a05060d03 70
    0x55490300c1c000c20001001c180d0315000c903500303e50101e001ca4000e00100282c07200b0380c0000310b4680ea40e0501d20107480d0343d04203200e0203080c01d1011080e9800c0c00b0300500040c01008001080b0a880d41c050f10f0300f1115044040c0003901d07259005480c25109400038a41c00014600c0e00d140703041c086a000c2003000c0d44034820380b1200c000c0d00821141002c02409410050700ca880c0201071108010342c001072100c5000c0e00d096038407222074404911246010718011090741e00103411403480900c1e42e00c91100511141500e1600044000c501000580e51709005090144c2c100380001564104150300200c55200180000c2c9900d551140c08024a185c003151804500f0b810340025a50f03103130f800081000f544052031200e5603140080207010f021080401e4210580b001903404000d015510003148105210138841c1c2c0c2c90030f4015600d034001040000303542c10341c054004c0c800030030307580803004081150304a91240c81d1601d00101c001840008071400700c940c2c00074200742c428043c5003045000100100520300c0024248 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 711287329 1250 711286079 711286099
    0x2030a0e06130f0b0d05072105071202130e060907020a0f050a02061c0c030c0509010806060c07060819150e0a0608060a0b1302070507030f080405060f071a0114 70
    0x2c0c40d02d4540007005000010706141185560307131340702125a08049100c600391414400081c8500340709103204012003a0b5200382c202a640c9107100000145405480b05d81004150401c0e040095001d000a18070b00112030002c810340340c40d0031500f00420001030401d034450b80841080c422066800201e00e0301d02d54100464025000c0149406d900e08179a2000c001e40150300810120f00480028558408030400745406008000500304210201c0341c41c5841080400e60600070300b1400d51003030aa50b988414040c2c01c052814204101c1701d85048016880540013030690700801003402644100003003141d49078a01400404041a419100c141603801002d0010b0606000034600d40006e40184e401803092009482e1181881c6d403018010b004140300c100c0c0584401800044600054400c82e805a5002006082c503d8150b6440d0030342d4050802c4244c0e00b85800b8800131985590b0705c4014080b0141c402c0e41c00c2c0c2c0c0c841c450b19090700c0c1c0d5004241c00c0300c9000b152070010060302c12862016005542d048800c0d0104e = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 711288579 1250 711287329 711287347
    0x6050904050f01050625020d0308090c012f0309130e0d030e070e061906020105071106040b0a0e031309090b0901090b040602030705040f03050c040e1c0f0522050f0102030a0e06 77
    0x640c030202e50000e54841c615111b00340909d07802c0f070a11070107030040e10256a501d041100056030301e901d58600381b128400d01000381c51810000d00e882c020318100c09205484c1350070075000002e288207114051b0b05c1e040ca41e03242c004000030790301007040c142c0c0012542414000042c042c0c0c1100d4503809940310324000020303d100041d409903543c2031075206050000e00503111458807000002d00803c0100ea40e003002c5080702000c25103007440091000d100300c0e400502114240d03113040861018081000402400b440140550110401c000002001a103070000c80026000d64a0401101c0c1b02d10203850314025915060301c02010614203403400394003c2e0031401c007503566114010202c03014030131540001e07401000c8003404003c0080200b0b074801c1040c1c1c2120709001054505490640750204140d145540c0b80c0c0744046010103902541c0b15003d0440c043c109141485102f06d0460a241c3e00102000f1180480440c1842a0b10f851840f500030030001317200440c24010100c10250100280144ca00c0c0304040100d10f00c0d007 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 711289829 1250 711288579 711288637
    0x3071a0a05091c050c032d0c03032b02090303030609040221070e251809060810140907350a03030506181612050106050904050f010506 59
    0x2004071010b01150205140300303d90440604065504407854003d00241c00924a0000345405402d000c040b11030416182002c418010701c81102c2c602e4055004100ca46030055400b80050305008040c10988031084010300c9200a20341c0c013402084007110700c1441000c0d0aa140041a0781c0d000c0015244040107484600008507201d07038008000c0492581c11032030004058000c2201c1085441c44800452152900102171450441c0303c1a110a48800e800030525100c0c03103175105514411801a0307130a40c140c0c0f60078180040e140941c104031501e60054841048415441c41240110389107080481700604002c030355251564800d05c550040038141d450803484049445800c55001c1c418410f25686501c0e89001268407501010010b03000300b8501000210305082107000380d11140c1001e5422455656021413451703d1b01300a041302403c0003030003409a8103451240c40745501074200d98403241c1e165aa907604000a032030008007400c03210f44040004018039154841034038044913148501403600b00074030b07169203 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 711291079 1250 711289829 711289837
    0x7030b04030806280303021504080306130902040216120f05030129070f020a0f0501090306020f12010303021f020c120703121a0a080606090606090319080a090503071a0a05 75
    0x9a56010740000c50016035804c005500031a4400c0e006d540603002d10480425a020040340c01500008003040003515500e00105003050444500400003000b0fa001d401041c200d0704110040040c48040400312010300030748074292091030840f4075003d040101510360080071408180328402c801100c0d42100c1300142d1000240305030258a440d56143c0707400c0c0509180144120840059001d0590218082168548206018241ca2042c0c4808400919690b10300c3d0081d800312201922404040c05501c00c240701d80001e148c021400f99008028041c6030300c01101c051021031502c5c030070003481000341804890000c58520301140c42e001826440d6150350030b0650b8203001922421121381d00d0301c0740d803210305440c542d442a2107030304c00e413551030032641c98414450383c41c4070035508940c0c080c07260300c00250140340040081840040c00390545001403417080013107800c0d001400048640c0c1c1030102e0750081c115400440c42c0e004080441c01003907014940302a86441e08505c200012000b20300041d4070080c80c0c0603130100d0f = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 711292329 1250 711291079 711291109
    0x7061d0411180312030114010903050d020a0204180b041b0803030c030a06051e090a0f020408030c1903140f1201080102070b0a0b0a1e12120801050307030b04030806 72
    0x2403001c200c6425250003182e0140341c80b03900254101c041c80202d4207001403541458100e1000d628a1642800c2030802d01c000402c401c64104005030344048006101844000d03410401a0014807510245104110980b513048060904442d40c510110300403c25000905030040d42140160b81090051700c00b18410b03d1498005e201c052000005100c0035404010040d0701c02c18810408000240d00d88040250344030040c0c02040b050180c00400078080e240c444c20840e00030610001c002812900102804143e0f005940584040d0300042842815240280b055000c44a045032070180328030082d82e030180041d09004100044d400004c08e040c95080c00d42e000720390b07040045120101066035900030030790217580b009000310340245104c4081a04860a0300170341801c00300c000d003080199070038105155489451034404030b44900b5071a00000d0a60f05880d41260304500503044032b0030040d82c03040c000d0513911040e0300442c02a40030b060b0803c086000315003295040350345450f010103152100000074030320756040952 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 711293579 1250 711292329 711292331
    0x61510121508061504050705040b0a211505060304020a0e040f0b0c0406030f1a0607020a0e0a0b090c041809060e1e07050108011d09031608250507061d04 67
    0x2003601c1d0000180f0302d10130740200640502ea0300d0320006001c00e4480a46598012403c00d100074010000349001902d28405545000c05001c1c0840f151062180341c601c45281016580344000b458810200d400710303000e03100030b80701e151540c01d260703020403000b503058454814190f020303c000c9810000c00c01c00031740505401c10303c030301d5803402e0980074035515501500c500710109103003440400a80c90355021305000700410148181001c4c0d2480140542c1e54008641240d200550030320114030801c00740030b498002d0032080300c0040d03004119000c0c080f51000190007100e191001b03210810480130400181e91015040e4000410303030440900d00345000d804040c102c2c0c07a06000310006092a58141c210515408075908211800d075590303100151440c01003030084035000d42c90a1882424400418030403030304880d41e28122072401d002c0189801c02060b030100200d62072400059030380e04103c110345a49140c02d03d5840d0f40141d0354900d64450759070396101c0c03042c4400e00c6560054508040890f0160103007006010784 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 711294829 1250 711293579 711293621
    0x1005061201121e11011704120e06210610090f18060302090f0619030b011a1905090a0603110d0c1b03181205030f09060f0703020c0306151012 62
    0x542450340c268034412017400104145158510300203441d0071507008a401200c4004014100d40c812113150115450003608280100242d080c034031080320317080320f4078095260421b006e03040c86c604110038003010b6505c1d8030400014550602030240128901000c0751003100c2c080610110850701180074005690010b0741c044c28101c01c020914040c4880701e4400c030f000300e0308541848001403641e000070401e030001a000c26403480041c0845100072406071003546000e0000c0c2d00b442c41c8030345400ca152101003941c03000aa8003044219550a1806042015011904040c084d1000c1407130068850300428800310495915044d002030340c40e0140003201c4c0e945a00c440d014000d60b10b0f6080c060010402c00e0310b41c070480111101e00094003400304070b000180076840300c080c62030000c0c00d500d03075802c0b030b0881540181d01003402c000760400203c01e840101100c81c440e4001e008513a01e61401c06003003210080c030b045854001125020459690079144910f0958a41040e100d4010740c4d000c1ca4000b0100c14032100c1107020098 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 711296079 1250 711294829 711294833
    0x4140d06020c01150b0301080c06090301021b0f010c0212070602090f10110601090908030609180a120206090a030e101809050906151c0f0507030305031005061201121e 73
    0x2d013018610101c4010f9149803a40d0724209213005220034405ea46294001944600342464450010880c011000f000541401d800c14210034400100410301105030b0f20012028808100078010100000403c2c009080340203c0e0002c09503252007022402400c05500080038200350352900791200c101100a401c0300c0325180750200103002000c0c1ca0301c90042a10900d400050f014400e4080c5092031540510759030f0840c2c40708001d00580090282c034511245126040c2c0d079a0781d40b420000300001500400c20442c001000c0c41c0064207101c8050b2603040140c1025040402003a002148002084000e80d0040015803200c01c1c01c556503900d080310f0040d03031001031100052404160b04460700400da800199200c60b203074090700c1c04042ca0044170968110611445181006680d449810840e900444840890040a64501e030508581e40c008034003080d404000c1c00703108041c05485c600030b410165115803030718030804401901c0c5001445281d04403131400450400300229050018050700480300a0001c4010714 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 711297329 1250 711296079 711296081
    0x50a180602030a09170c1c05010c030504020a0938041a010207050907090e131a1f06230f0c06070f0806130c020115060c14030406020304140d06020c01 66
    0xe0300343d00000303151a140403031310802d0051104c812202c403038010b100119490040c004a8450032842e45204241d4107540c4002c91000c0c01000d0100245980c0040c080c0340a2040260003c12b41d04001e8000b460010f100344140342c007420411440d50301907120303698550a1250300c0840018604034580003401c00300744d01100804a6000d01da0f80300241c00740c03228a0b84800c03c3c000310810807109440000e188450402240c0c2e100300840d03401c8900f00e03c40c0004000e4a07282c460000100c41c0000703824003000410040b01e01c000142c0a044901c2c0e18080c007100e01d14207803008216000e40046c2603002d81c140c486008140b00c49400311070000203072021250b01c0b00c29600341c90752544800c03200400800c074005071560b00e0910509240388642d01c020901c001480151184400414550084c030056660703030f9203200c120280802c0a8401040103648801c20352440b890318001c0380e0380007291a5035a51040c0f0040c4040b540101c10380d419030b41311507a1000200200c20010362684070004025042e2480084c12000031001 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 711298579 1250 711297329 711297337
    0x11030d0507060e120403151808070b0601020615040203130c0f06020d0206060105070609020a0308030c09040b0303070308040b0712060308040e070e0a0501180e07032019050a18060203 80
    0x1280d0800420f500401901c2d1203c0c0703811411411a1002c00c82800040c0041d14140b500520210000901040c410910304152540402c2507079101b00c003181850403c41e0106107030b94005020301c090405030038200309007100c05000840c2c50348696000b10014081d00e5441100b10707903040d08140d0300f5004c0303541c0c1c800005810b034080c003c2c03070010300980d041c20320003034000100300e0b0003a081a51603525026440d112940280180b0300c00b06d03030080c02d00c1c0300000846d10190265014400448030107a0710f0110004100032075400388030300c90086d0000d200c46030100f80c010140e607034000d401000d401410341c0c3d420003c8070390301c516803e81d80130689442c001106000c1010082d0040c0c0301040032450b52a00c0300a4195003800d121040d0960007605180248410352240310082e10342c0368460f80d48400103071520382d1482c0d0002e00f20380758000682d41d1000410f10005500c84840071511506c00c031460082500c49400010b21400c0c0c0c0e00c814010005903c1d0380e80d5101d101207840c903090010b030019000c1d4442c0002500c0f548 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 711299829 1250 711298579 711298583
    0x90c0b0c0c03012a030c08010501030504030e030d020c1c0c0e130f0f030806030f060a0c030e0a05010905060106080f0112170a0c03140f0405040b1203041404050f061c11030d0507 78
    0x800b010205011350007071089003440d4515864141c603030381c40c020044024020042c422010030003581d120b20040d031000c010300551320400c7d4019004840a920a00051207108079036028041e220301c18600c04250070200040a0b54402c0310328020b19501c0d24cd56060041c03c0e140000c11000000c080c40050241817508461100c0c4281e5441c2130301c5d01d5000405950b5032041420508540080000c10820b18443e808103100c03940b51704010443e01020400d06060040c1941d003a40c0c82d94640240100b004024403c450140007103040c1003030715003455800b0400c0e0510501651803c0543e15401206001040c981d000300042c041002d9980d0340000c076402440400300c0c5c2000c80204901c00c1d00d15035503140e14029241411a0b904042d400c00745001c0400c00500b40c81d48a071500719003001c0028206210030720080c40a08400c4600e0380d51114408103000440700028404880c1030303c54410700555646022381000503020302c030601461501d9034103100c10141d00d031840c41a0f05100382031030401d005800c40044c024941c = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 711301079 1250 711299829 711299891
    0x5070203070e060a0b0f2703030f030f13050a0b190e1e060603030d090206090a030b090f0a020a060f12020a0e010210051b071a0f01140301090c0b0c0c0301 68
    0x41c1e607811601c51503000e0741b5042c0d810004280080780c94806c0c59400d180b0780002002c0700750f0070402464040303402c41d404031420008508001041103c140c0f03403825000e8002c94000c00a841c81c20b080d8031900e8071000d1a18000304035210a0010400c075003078410310340741082c850002c10401c00c100c4c512620350310414800d801050030794460040400e5200400d819100c0c0348090040c505e489580143c040041000c1c81c0d0880c0e100905024034150713901d400f28180041d40c45044442542d003412440c903403921803040c60144039070344038400410060700d07038424500490b00c031410407100061003500e00382d590300804c42c02d46007030a00c040b40d07500c1101e52008a01240c0082030f020784418142000c0b039541078810458800c40480c030024513154a5201c90002800182e01451100250000c0714081c4030300c0303400c01d072101907848a1100c0140112040e4243d08881a0803c034000c00146170203076aa5128201b1620070303402c0e5000e012442450050042c84041240d00008000300f01022410504040c00000d004041c035102c = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 711302329 1250 711301079 711301099
    0x3030807020a020a05060702030a06020331080a030c030f0e0102031b070b0606031e0a091e120320070c090e03040815100801050f01171207110105070203070e06 70
    0x2500104800e42c40640140c2078003c00750a1400740601a030000800303e8251040c0a01e450100783c0d2840554003508490102503065030661604c7d0070555909a40c2440c0e0160382d070303071080003c0c180c02d0440e6902c180318100814880414001940181a03c000403203029081a298490982c1c0c10b41c000c500c13480c1c50704030b01112004a103060b03507058040c19800910002d082c82c0401c0081c98202d02540d440608072280c0c5041e42c500072540300c9145403e0b12660255a115608501042400c2c0300c04d0a0f1004c41c18060305014031280c842880486004100409165a8030504c41c00000043c8841c60042d108080c1165110010700e0442251503c078880e803140c4074681080324603840d0011080301e007182c806a0050032140743d0081d41d03060342d010240c0f1610f15008002c0d00041d1800d42800303014410518000d480c4032a601d131070740b68684011006000c0d070181d00503c0c10380720000103203001d45405940002c001c0d03400300007400040c0c503107124240020358184034980300000e000f5850106144294000e86605202c = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 711303579 1250 711302329 711302341
    0xd03061205070302060d1d0303010e06060f090d03020c1206100503010207020d031202071203020901080a230606040b0c07030c0b0f07030c02040b0901090906052518180204030308 78
    0x3040c0c0c24008100b41c015100070005485c00e80080c20700e441d070b176042c005a2005403040e14a650390240104600642002c00100f08080c5484040341d44428241c400314600200107a4940b0300348100c408030b030b2080b0004031820f014548200a0181c441101500000f01780c004940525503440b01250907810003080c0ba03001080905060090301d42c05507025114801d1050585e0b020703a4903481380f940100d04250700340f14920114030341118800d4003000355100140c0d1030200000040122034010002940070341003611101400c4950480d01341c941030706d118441c1450b01c86000082c40c1d41f1596006c80c0241c840407403c0040c040010402c45c00b180d00c40d01c002024181c0d10020b40c20b0714002c120408595000c1171000308080380c000d1003821045032004100140c90244140013511002080c5c0081a0540e5030302c0380701c41000031030b22070240c101860700000907460040750304106040d807241c0d5840d010044203c1c4511021540c10300381078050017016a4078915000140903010094201d03110030350010b0b21a2000c140 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 711304829 1250 711303579 711303599
    0x507030905190305030103030f0302070c060e18061507020402070f0b060916081303020a020a0905070e040e120702130606081b0307230c0114010e070f05090d060b0603090d0306 77
    0x10b502da40340d11014210307031071600c080d40c443c00c02c1100c00c07040c1a020041c4000140c84c0d012884064000c40d2a00303045a91402c0c02d21034002c0c17043c0c51111000114405110b41a0b0715174540c05042080e84044a903502c15a1001c41d0190203500070040800110f0b59014041110b007451640c85007070140d03031010050750f030365150620602401e004070010031841e0000c110311242041292525a000740120b40702c0c00681e602007401d100e4594403000aa80c0c0e120103100c020b95020f00002c40b00e85d13040b6414400440d02d182e01e16200e000045028000ea82d002481c0c0c001c54039130f458144501d0b0407290b4204181582d80c200542481402c8403813a00340305200116405084e000c3c0300fa603000f4016590f13154103a00076080b0844a11401c2804c40c0c0030a1010322501500c19001d0003a4500801c8140170904c155142100f00300e403001000c1c0c403c00a1000d486a8610855445070a44010480445151607240007070b0604070002c0c40b1703564519412081c004200821043d00049070310246199a404008203995211240 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 711306079 1250 711304829 711304873
    0x206070f0c02010f0e0904050c0301180506220510061a04060e310603110409080d0207020d3206010b0a1107120f14120f030a060305010507030905 64
    0x601007007000048001551082c1180e00d01c10480b402c01c16101213031000042c2c281e650841d011101d581c481c03c21240c0340d003028011107030501c042352040038040c005a59480e445000051482451300801c0580307000d044d078503410003c1c04941010981e8810341c000c0000c04090481c900071203c001001c1e41041d502c1c4c0c007440b0102c0342201d80a0340e03555001e0386480201b00401409952545400701050b102090200351300311680c0c03001045200020f2010700e10303d07065614034804445a4070561402c1140800700f4001002c40b02010081503005940d000c1520004130110545000074185106121332904100c00e0300c41840d01e1484920b182181041110000c10b580e0704090068a028240500605002601900002c1081003418068a04103616203c0e21240c151b200d56045d075100500c000c413403051000c6103000c400e81c0402e500191521840f5001541ca280c0329601d4003000303030000040024040ca042d0340c030550180d07510600910503424228001400b800846000b91020b015212081a80c01c00c006000 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 711307329 1250 711306079 711306107
    0xf091503010f060905090c0304020d02030123010e01032105040f06031a09040507090f0b030f0c010f0206010506070f050a0219150801080d05070515091c0318080a05091f020607 77
    0x14040c6c2d0b07034540c1c1d42d058141e04050702c101c0c0c2002e10002440010f903401e001e40ca0400b0214440e010398120100e030b50b400303040300680c015070005642c4070041c4041001e415581014400c0c10410380c506400b0301c0d10482d604e21455000140d840e07010500450b41d564140c00203406000c009840607040090401080001c035415034000700b00394400c078070030030a81e21140c10020108500c0600001c03c2d115280100b805c05c078078446620026008004058072039030300403d80c20705c1030f2114802409c6560504001c5407140c1b10702d01001c0d0000007503440030340c20008100704080100e030b8058014507a0300300b98903040044c45818050840703405181c809001c2007901c41c5040e45d040320301001c01020300300940001540d940e0720030b82e019141c0c0e00a4905e580814540080681c1c0949403100081600e801c4018801e001c07070392410074540070142070140b5000912901200700d5141c68000c1c40c5181d4440510900361541d01c20440740503080b41680b0008020f80640e0300651244400c82d8096a02d10b48c0d6290303045942610311144 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 711308579 1250 711307329 711307339
    0x3150f150e180411060403050a11010206090a050a0b0a06090c0903050c1903110d02030f0303061f020606120c04230c030705040315020d020c0102070c0f0b0409020f091503010f060905 80
    0x2401050044c1603400e1803d1014080521b803035180c3d12070608101405500740c0702c0032540a0129940c0d6810411039602001800184c0f90078691555003549585000c4c101608041c1010040303202e155203984110020509070b04c0c100315402c8100405020300d0281e12042d58140691924441e0038100702c203200c200303d400b180c40701d4036050442d52504540002104220b40002041c15020010384007080300b2044080200c000f140c403854040d04101480500448081203c01c00b010140c1c3d201c0e8000403401d41091040b01d056a92048100b02035282c03041c0031b540e10390712600308030540784d50044030000c0319107102d40e91305000d0382a9a886641212032106a402c2c2000600800003000442c5040074115812070710440058034007180304030351300700740c2e0492441da0070103950019582c010800c0080001004010000040300340c145000751019560040784141d06000d5000101ca00d05407100500300c4060307540081050300b811046004038a040d130030900412410b22024400450540d00880002d070031114003d007 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 711309829 1250 711308579 711308581
    0x50108100506160609150f06060504050f030114070c0b0c18010f14120a140c0306010c06061505070c0f120305250501021e0c070603150f150e18 63
    0x9200c0564042881c1d6035000c10f21000c1d41c80080c005000c3c1e9140b60740034540340c6c10950384c5507407a802241e107860825000c0500c0d01c1070030081c00da000300648084402c00ca42c0a001c030040030012a001d4201020182464a481c03010000c4664020044440340c901480708042a6503507074010030700301d10036166044e04c500e01c6000780b402c0e150310035408424401e00301d1400d142d484040b40402d002d1600481c02080007201c6840810a82406501c141c0454504148000c1d40d9402e10591300d42481c400600030b181084202d148000030f1041d01d4000400410840d040d50b11640041c40f4028082d03000804101c1d64180c0c1c1500014070074400122680548a200158220b0002156426a03450b400381103440c504c03441402c0c80440780d58451581c60300c0640200300140e45d806003100007500000030150040e50041060000d000c410200050380002d540d45400d0004071708010b80500c0c1c100c910300e680038102801070000c2c003082c1001c458640410301030070303034035444814445c4408100c81c03002d401c040d014000035400 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 711311079 1250 711309829 711309839
    0xc020102031e09120c06060f090717060303090901150f1805041a06030907060311040303080a050901020c0303040c060306050909060718080d0207030b06041803030e1212060a05010810 80
    0xb400b030503048803151040302d4401e03c800c0140f2104c0d400440545a058204104111380b90811884042c3c5224040b90074140502d06004040c14407d0707982001207414140702e0000c5c03c503460030070860300c01010041c2055265a9119801c01017450172458800014030300345040a08140602c0c1203621005140034800d40c01170815091000a083c2c07410030b0540c66900c900c0002d500c0d00c071540114014034060000d8584542800000b5098925100c2e200350001000c00082000c42c2e80702c3d01554100f07040002c08203690300c4148804d40a030003840e80d507100c0ca000000502040080203982c035003c0b6003e50300c0500101e641c036020805041000c981d12401c540141001610342ca200345150100128075030590a05036498414140c600031454981c08096400130380c0920910050703094507a404002203500307000e0303892100310b4a440080382c294010103040c0c0300d40c888229800240705a0010120315214180c0b50507480640603010103050798114000c250700100402e055100e012503600c1401d60742e040644240c900 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 711312329 1250 711311079 711311131
    0xe01061e050a09090503090d0f020901060519030b030313120b0901060308090f01170c18090408070818130b0907020606060301050f010908060114270a0203060d02130f0c02010203 78
    0xb0443c11607986c002000f2542c1c00d940c41e0050304060034000d404091100099206104c00148180c0014040c04024820150000500c404958001030140390101c1d07003921000109140d8019640041800700104501040c1022000400003c15014440c40e00c5c440c0c488800880c200c0d001801702410100d0104140101030074a08404428041c040c503045a42d420400558500c001d025144035441e10700000b01181e0b06001c003c900c804d142c404640c100043e083c81e070340b036032007502c00c410000300031010204800079196185803500b00444c5016000da18103000c1000001c00405200c0c075480d104101040103c0c0c0c009100142c0d651142c040901290b14503400d1504000031903105214003810420760900c04075a5100500025000340310440c8400d403c00b40302003c10034000c01c00c0c1c10144d54403c4480c009008010344142da1508540c0d040340c0140e507500c591010035031205000801035000800b4400351a482c04250b44490100c10000c542040034515000089090348401d840720b5403982100901c540348038000d = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 711313579 1250 711312329 711312341
    0x21005211e04030806010e1909110c0a03091d1314030d020d0506010e03060f0a0203181603110609061b0316240504030219150e01061e050a09 62
    0x81558800504003000d005180700041201c0440025002d4000e000e100c0d600030086d4080808102c80020102d00c50b9400a00300401030701c11480c44c4e50b00da000701004076040c0000c4426a84540064800d035021505024101d030403140300d1000d101c0f1a5240c080300c0d5025411031203009011000004a00021986500b02c0721005582d00c141c031404100590050300366103100502103841e8140000c95107180000001d094030784250344040c02a00440100031075070070b0310384100354840e07580c01e001a141d84411030a044080d4402100741094800d400c4481c0003900644004402c41b0302c5143d4025401d041c3c1e4082c0b0146000c2e1048140d04403105002144200f080030904204007800d8200f12401c145904100d14800780a074407042c0c68501c0c1c000e54140005c0300521048905564158040c4428249560700a5072807030b000d41803134007004030101890f0402800d980216904641c5406c02e0100c144266084c0c0c1c0281007520070400b086c85030705090310540c40b440741241c08131000200340c43e613807a20b4510a0006084 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 711314829 1250 711313579 711313591
    0x9040f020408010c0c1401090302100f1104030b040c05040c050901030e0a02060f0403031d100e030c090c040e160c02191d06030f070f050d0311010608030702100521 72
    0x40c080c040418100c0c0b0034480c410008006648800c0305a00760700701248080300040d8155640e0b41407410140c082900050010f4000b03403540300000300409040180c100500d0740c200700803000c0d0000600042480880441c03180175031701501800894696070020041116451141400416028801c6000c3c070740c003d501100c2201551001e03519030200503400580154480303103490440980201d002d02c207041d44148103c000440c03440c1d034081104407610020314600d640329089000c100380700000000d507032005d002e90158203002426101e50703070800404031400741d0410b000324484080b06100180010403000c00c24401401c0b9900c0309003007109030345c0a000486031000c00745c00c25a48000d2001800c200955000081c2032004090841c0e913080c42410181810f44015440700164000c00c1c0610210400b4500c0b01c08031032040301c0001a0803246c0c5010348050b224007a4964855281400002c0e0401d004001000d00510071030303010503202c04401d000d5805008449403e000c01400e4680700c1c400401c1a00182c3d0062 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 711316079 1250 711314829 711314831
    0x120601030b012309070c05100203061e030316470c040b0c01020a0f080402030c090702010b0307090605150406020303010603051024093c0e09150c0f09040f 68
    0x14503e0200302d2400301600c1020000c3c042c0703000b02090220900c864a006482008194910705103080000d2030400d600003c2d10003a1a4070b00003020907130341007048034064014480420501105414034012000b501150980203100a0212001d0109007549070300058540300d1000380c3c2c0107001c20042c0904d0701e00030202e4008403020407006c200c030059503003e020031013146000940d6445802400a02c0001006480018848880305000c010b0750045101a116a41a650f403542e5941ba14400c9000d0030718611940e8040c0101c18001c101c00c1d8094010b4002c0d50000e13642402d00010090383d05080344100e00c50080140c01c24001403155a2281e040b540c1c0003005811180314850f01ca24a10122012100060100480a29030840000e81040c0c00d00000c0c6080da400b10707000c40b2034000d164545c08104610031800c400317140100c000c10071000344038005884118403440d000c0c9405000300b0b40d51008002c9032819410300030001f5003405088011031310805144e00c01340342054045002d00c80940f45c0481c4030141700b = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 711317329 1250 711316079 711316139
    0x90907051302030403170a0222081009050115030c081e0303040b061f18060e03031806040902040806010303030b09010609050d0201020a06020f0a1b020108010308071401060303030902120601030b01 86
    0x6910742d40c419806507c110800595911030b000d0009044201400580c41c0c0000344282008502e6002c507440030411521600404c0c041024036140e801030030000210482c8401e081d0b404001d2040d102800810349140204640d10b241001c3c81c541010403401c2e80d61300c05c582c02000000c0021b0900741e0301c250052005480c02d1004a40b80c01f10178145442c3d651003c0008121079060740008601c1c8034164001e00e8103061405034164818042500c912601403041c080c000c42105400c0507407114002c50f0300134252070f6030440d10385450301c040c075440358420b1000b0b900003418580040440d00c0d126113801d040311815140c10360740c1480c010070302441041c50f000590544c0600d00852001c5000c43c001800d02d9a01d5003c45035a4140000c07014005940742031010280c464807070034810050340c00c03500a40c10b590300300354200d460b04c50a1078016880c82e81d20078886501d5081400000c201505600080c1505200316010303442e0301960291581c3c0c0707241c244170250051070003c00400c4010b00060f04041e40e40e020301c00c04200 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 711318579 1250 711317329 711317357
    0x801020f03190f0f1413021f050f12040201020d05040513051f0e060a08010e06151909091104020c06060f01020a0605180105010608010f180e010911090907051302030403 74
    0x115122901811041515030580442880010003c586d01c44004600e00c2d000b1400c81c2c01041c2d02c1c101c004480200222060865080e007809103040d079044441b800c0b06583d0703442400c0b503590201074081e58224094450703204201d07050b602800654065840183c0710302000c01e00d00c500c0501804001e05148840c081d803c0c094940765023a0111800907042d0003070032480c01e0130544140b2002034401c1e4400d40150745041c501407695440461040d40190f03544815080320001c203000a052105158140c0410441c01c61000070340701255001541c10a001d02c17001000c00c2425001d1005920a41401e0f885a4002e440042d440d4540009030703c40000301841100c0c0c520015594441c103d4100340d44541d400b4603007410a5454074024060310b40509118640217100e5490300c591400341c00d0040c007485000d0360745241c0062030300c1c600c0ea01460030441d215001344160010790030000c9142d1074624003140500900b10009410348000100c0e1021120b014281078100201c9090110094101801c11020441d04a2010f00 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 711319829 1250 711318579 711318581
    0x50d09021c0c03020f010c030e09040c17061603060e0402152a01051003021503060103021e03061e0a0308030a0204092409060308040302120f060106020f070801020f03190f 75
    0xc16210b0b0480a4565055004110070708142c29013280c10465a0000c0100090380102001e048032815078054206891760320708110803484c0c9030424100e07442e0210400d0f9151800040352401614108031446411803426001c40c2a40c010b8010151000c524001190041c10700081c49a0032a01c207405050070503540c0072140940208604a80115800c0800a0340c0654002e10030305400803007400704c030310203c2c0ca5036001c100140742000304546580f42c0800041c4a07039000c1d80442d900b12070a86d81c44007003841e603169620140d8105454060080f0f1742480d00610702801062141c40381a0000d01703031798425146540f00705007988003c294103400341e02440002075502c01030203254804800c05840b19454008210300000c1e0a40651000c1c1c0c15906200f0108040349100044405894055940410281090035000d10f0510400045005c5103da50000900180d010031000981c401040940b040d0590f16071140b4282d0180c00003210310307903004001281c0103202e03000e523034456018844004603560443c1c003002c0d4 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 711321079 1250 711319829 711319879
    0xa0e120f0f100b1f12020a030c08060a08070b09030a0804060207030201080a02030f010312180608010807141509120316060c0516033009031e050d0902 66
    0x40e0540e8803010707505020700d00c140800b094920400c20b0800180008000044010360a410703420b00ba10454045081a6486200310880080c8505815955803c21990043c01402c001d4184400a449000418503a2030b010b10a4000c54171401c0041902c5130034894540d00c51f82c07203406601c1d407503c0f55128400000b090781c0091700027015542c02a0080a2940c0005051070030000c1555162902c10810044070540044e03295040d02e42000c8400d1100242d07680a403aa0b11031094030a07404403183e200021040d0380a01c44605858880050300c503030303d6540101d0b42d048540c443ca9035604c000f0140307042c07210103850f001810180c01d000703004243c2c2140c810100b500f107500c18462850032a20820240f801d2203094001e4910801141ca04030703280c500a41c8039404855841c96000303042010204805054024482c0800f4400010300285803481c05080c61003002410030030302c101d0201c0c680c800303180c0140225480044010010b5110341c0d28102440404030014400c2000880e07101050b084402c0d40c61100e81c403e0 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 711322329 1250 711321079 711321103
    0x405010209030601060513141206090d0e011b0b0c040b0a03020d0b0130060812130e1e0a1107060f0b0405010b070f050709020c1b06030103080a0e12 65
    0x41e0745400400505060500503040582441010030030b400d01fa04a00e50903000f01c0700d00681c003200c088079041c009401d5210341119141c84c0e01c10442030019014011030100405402e5072250740d440b158000c010744022040c00d03090001d2046907440e03480402c5042c1c10b0958049120a002440e0948481202550741c12050b60240002d90100e0f0380502c0c507441e4800c1c542d00c100d003400c0071028000200c1c1d448100d020352101d40e075001c2c195004041d8410f10242c201001400d0500c05031010184841c00380e03640e603001a0110180c2440301040003984240010340d1a0140e00d1840300112000f2148403a50032004014007100ca007542e07a042078035500c50802014215079441a4030200314040400c0580741074442d201c0200e40716900e040c004000e00c00040080b110342c039500108500c1e0a03e054102903043c4865076100d0141c0600002e0480c044290106e0000a2000e8800c2e850350b1004070142031207407d00090000801000d07007040023051103805042220010500100b0160b620440359015604040e44800d00c = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 711323579 1250 711322329 711322331
    0xf081e0a090816031103040e0703090201020703020a080d230417070801050403080406050a0b06090f0a0f0914070203090f130e0a082a03041505071a010504060b030402031c05040509040501 82
    0x243e0b0805034000c41c000b030b207040043d000f1400d0a090010348000c2d1100a4052030074103588007000c41c2164001d11a000055070002c201c0c620301c0360313140c1907140c840c800c0c0340e1000c0000b0b0302d10540000c1c2d00016104451a159a1030403141400c1c100002c1c08542c440a0035020790034454940c0c0056280c2090042d907104510a51351810749081c03d1524609480010b0144040103040ca049501540c844100b6a4141201201c0306614600454003040c0e0300d12182d003161a40c400d1201001c1982e05541c1c202d042c0c180c1002503000c8040d65a00e60881c2c40f4001d00c42490703404210314042c04c400307150443d0b59004242d503005000410744502c4102070b04d00f10301c40508541d60348000c103000b1040f154015407440104c220554441d5592107112580d41c582c0b190340186090750901509407402203105000f540c071881d5101d02c0e4031019560b01c80f00040f015500344103440c8100e09010020444100000680b03008a03400350061542e603203540071419400d26115194010480d0170322000440d951119070981c083d900500c0 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 711324829 1250 711323579 711323617
    0x2090a08012f03041214041a03180f060f0421110c030d08190209030601061d151e090301020708070606050303040302060f13090606050a0f081e0a0908 66
    0x2040342d46150200d500310800000034030400010451001c2d11034207544403850212040e2002d08048542c40c0615003001180c0b000c1043d602d0b90142d003c0d002140169007000200b10304200b01d000035aa584103850180156405c000003103805080303001c007090740140c440d20a1075095015020600c0c10407030020600b400040c1f0180d10050072550520140c491007100340d010740701d808001038010342100740107000d0050007424600c1c2c05461034415415110b6107080241075410b0f43d40d40746401000c0103602c0066290014028500a40d10300c0c0101e042c1c81080300110b03019081400c010101b600000345408a8641503008201102e11a9401c2c8001c0201a208000c007644070354160404004a80154126500aa01c10042070015940310820b552111186100b940c5e9940d0b00d002c0c8080c105501980942001405d00e0000316405401102800c1c0040255441450064401b0411184000203a031f1000030000f0340000b524421410b00a00d40e4042d019540200d55080359540d20702c4142d11500f0144845002c0c10 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 711326079 1250 711324829 711324881
    0x81e100c05120a0506210102120103080c0601210f020109180f0e0106121b08030a0807030b1009090c05040b0f030708010608070e040506010c051005100609081002090a0801 75
    0x40115038100c2003900041000c0d14020b0003040446c4450f4860010300c13005080141c5020600b5011542c0d908070401c4428281d594910b03124800d90801d05408465025200c0041102031306140d0300c0c0d103d90401d1605551030320407501d40c04515074030001c00b80d04010148c2c2c0040b41c00340d000d880d44a04000244400a14501d9403507400f000c445812240000a905110013000000c1041032140c10319908124585456001c40507a03d900824592020804e8040443c058009a070445d4080c5e02c55103207a1014410402c0701000c01c03070026045641c50010503040c64080c070401c0881d43c40300c108401c40e41000c525280d15140954025000908000d04140b400810420180d47c000025801030401c2e0510324003030300f400d51000d400f5681081c2e0590007655070f200010840d0380700d0000303a404990884183c48012400c4841800034010840e980c0c00c03240c50710800003807914858800301c4201c03100b8402412030221424a0b1f080079511030024294002042040410503030000c0c8901030503e4202003400700140100 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 711327329 1250 711326079 711326107
    0x30f1104050f010207030c090506060c070b1b0105100b0d15080d0f080708040204110910030605040b0a0608040b1314010504020415030206090909390901081e100c05 72
    0x104840f070464010b4402040001d0b0104020800c0d501d080c0c8000c610741d5102000320710f00713000c5c4464040940c0700715074002800c5007514004110380f130804c1c0091000703c00300c954036500362a8107440d0030300082c4c00fa0004003c0c00c0d1012000d410f131480000300116100c000761072240e171f03260410b4128003003d40103002a41140394000011003d940310701d0420301c0641c40c0c01c0d8800f034000c0000a0000e402980c0703a24405804041d140110782140d80000c101c800e4003132601c81c00500410507030043d1805107260950446161a090742810202c603c99982c848072030352103540b400c00358440600200548080c0003400c10020b104000024001c009007400022a0318007401000152030516070042041d800c004800d201607103500c404c1302c40389041a68401ca072500e940f130b043e40c07a040445400c0001d0345085a00c04e5580b200060140c034005e0005a100561000c8503002c10028183c02e2040d10b485500030607060740f80200561810048100d690240c400601c000c2403c41d0a83c0d0036511140002007000034040340031042c03 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 711328579 1250 711327329 711327349
    0xc1e1603151a150a180603050a0605090114011b05030a050a0806011809051302040f0624270810050108100903080a020d0920011b03020a1101030f110405 67
    0x181c480000b400b107034079000b1030090007003986a0020400300091802c80d030f50160103845001000030700b0300b001c099500d0700010001c3c1404c8da02c0c000c0e11810458000b502c0e1404061180c140c81003194034075480342040e4010f503110f0b01c4043d03085200381c408103070103004140b0600140401c0d00d019201c2c02c0d62144881c90081485000400c054107104590410310000018030140805917086081c0000380754444e803505400d1000c118a00960003400c29050900405481d08003504441802d45040c80006504011840c401c015025070000150408040910400c624100d1403400c8442005c1d0740030303141c89500b1302e07003081b079400382d00080710742c46000420130207030100071114101c80c46003410001031036503075001800e01c6006003e05440640100c0e224140c0d1800307921844074290712032079000440b00140c00341030007429510407160100350100800012a004d000100d0901a816400b82c140d404807a991200d4030220800258101a55000c0c0c698800d0864401d030400134030548542501d852500c02013080c0e0041c = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 711329829 1250 711328579 711328601
    0x8070320010c0203120c0c062d1b1608120610080402150a02010b03070e0f0123040207062415110c04020333010909020c1e160315 57
    0x2141c0b01200c600198040113a03400482402400d00807502c45034110f20f428000c80f040507226000351010300004281420845160100301006d94103244038401100b07040d03103011141c820020b1300c00714819114440300300081c03d07900c00d032481b42e01400c40300d5241c0c111148c100f03100c5100d10410b09020b1024518280300074422000203490403505a2526034045855140c880c980da000240000c1080c252640c000e4100081c15900a0103d070400da41d20b03803280c44182000c2d03903040314414249002103506c140308081d865581c0d03e08070318507510b0a008811b10000f507006081c16140990349080c1a800199881007103103282c4910050080c0c030f2400c02580414800c1410502814000f40307074046425907a020a020b50403502c2250f0060f00c960303a5034455000714080504500d0707648208660340150707a640c06d241e034420740c0c0c0a903100312942e505c400c8014100d200391070760545250700c0845644500502003c01000f140716080c242d910540109003c41c440481d26003085401441440c11210304001078498000650 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 711330935 1106 711329829 711329831
    0xb04060e0f031f090b0606033c011205060604150303081b0f0406080109060e0c0a0e1201020706050603011a06130e070e0f0a06080c090307030807032001 67
    0x2111300602103600017000b101003000e904011054900c110201e081240c80e1080780d02d00c011181f80c0c50f290359645900c40400d0342c0341d40700f0040c40301d078000c0081d0500200e407504245812810003d00620303c60040345098200ca001c850082d550303400b12505030030f11010ba41c03641c08240074400d021104040a004002800c6040e015103100204100c8500744d4902a40340d880705004001c1d1032040c4242d1903a03400b805e02061a0310305020080c06158810f003400c28283e180746010402548240c807800c00b00340d5010402400b0302440c0e0141d1944040c00301d0080051540c00071141c038603002c2c030720302c02c5004030700200309014900031602d6200c0213803040c0034500d00703203240c030719001000002502031950141030050030484d214100805a44281e92080e02c4080c825603414420000b44e400c00158150315200b070f00400404110207000801c40c5a003e60303114050700700c83e02c0d001251951546c00c82c858030707 = true := by decide +kernel

theorem cover : BRFrame.Cov 711151079 711330935 := by
  have h0 := BRFrame.cov_init 711151079
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711151079 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711151079 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711151079 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711151079 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711151079 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711151079 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711151079 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711151079 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711151079 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711151079 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711151079 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711151079 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711151079 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711151079 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711151079 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711151079 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711151079 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711151079 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711151079 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711151079 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711151079 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711151079 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711151079 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711151079 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711151079 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711151079 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711151079 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711151079 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711151079 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711151079 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711151079 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711151079 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711151079 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711151079 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711151079 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711151079 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711151079 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711151079 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711151079 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711151079 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711151079 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711151079 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711151079 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711151079 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711151079 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711151079 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711151079 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711151079 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711151079 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711151079 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711151079 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711151079 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711151079 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711151079 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711151079 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711151079 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711151079 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711151079 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711151079 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711151079 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711151079 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711151079 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711151079 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711151079 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711151079 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711151079 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711151079 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711151079 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711151079 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711151079 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711151079 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711151079 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711151079 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711151079 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711151079 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711151079 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711151079 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711151079 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711151079 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711151079 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711151079 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711151079 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711151079 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711151079 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711151079 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711151079 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711151079 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711151079 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711151079 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711151079 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711151079 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711151079 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711151079 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711151079 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711151079 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711151079 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711151079 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711151079 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711151079 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711151079 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711151079 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711151079 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711151079 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711151079 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711151079 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711151079 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711151079 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711151079 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711151079 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711151079 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711151079 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711151079 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711151079 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711151079 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711151079 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711151079 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711151079 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711151079 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711151079 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711151079 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711151079 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711151079 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711151079 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711151079 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711151079 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711151079 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711151079 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711151079 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711151079 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711151079 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711151079 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711151079 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711151079 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711151079 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711151079 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711151079 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711151079 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711151079 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711151079 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711151079 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711151079 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711151079 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711151079 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711151079 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 711151079 ≤ n) (h2 : n < 711330935) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
