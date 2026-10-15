-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4492
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T12:47:38.650714+00:00
-- url     : https://prove2.me/submissions/789a8f7d-ff1d-403b-b0e1-edb272a88fb7

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 807733812 ≤ n < 807913669 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 807735062 1250 807733812 807733819
    0x612022b0803010b0a030b0d0b0f07090f090c140c0a02010c02010c050d0903020123070807020303040b07060203061e01080a0c11010606050405100e0d061104030605070302030906010e010b04060509 86
    0x1540502248501c80a54001d01c41000d00a40e15800703043c0c020704954201051710300c141290b00860001c9001740c50020f40c0050b2003032150642e911003800039141c40b801a441030707118021400021440800c80c0c0c200d485005d221b601c64100034814074440509501450443c1140e50303118401c0203015612600c0004d007414010705002070036140c0b07900c9140c1852042c3d4202c1d40401e03c40e4404200f107581c442c001414849840210081c6210750210390991889003850241200c4004600c0009554061044600501c900303280e5039518a80c5140c03071406908100c2d02c0c24030500c14001040c2c851034070b004014500210503900c41c6110307940c5400c204000c00040105800f000b007004410304141000740b04590282c000c540742c484c2c40307071319141c2004484c084501030102086420200d205054898040c40202c02c0d03440a0003041140300310300101000c3c0150351000d443c1d1400d1900b8000c06a4165008500a55807503041d55456a00d901c806081850288210400d180d41000200003180c0304501810080300020b = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 807736312 1250 807735062 807735139
    0x18060b0a08100f1b0809070e010b0a08103c030804090c030e0118021e011e030b030a2d0201080c0a03060b0f19182c04080d061202 57
    0xc41d11004e041e1801080c038012949403000d0060100040000000030b101202c0d40340c01c9503043c8803002400f03000d100440b0051216000100d041c0d1035421600c80d000d880c414103486607041000b40403d40c0b17011210501d84e0800c2c40340c00d454486800300702800d0f0a030f94000d00c1c02443c05140c04000700c010118210041e003055a02c0b04481110002030180200c2070014440c40501c0c0381250041080202d030b0218600c5440340501c0031000983d070806030900860500442410b81a403141b40150050240506116814003d442d0750000304164134002d54180751f21028401c02d0994034101c642d282075000f40d00039011802c90000644198204030007070000206520700813a1169680324024410307001010351a5061a0104d08020580101201ca00e040146440d0522020306000000e100801d07070350042d12405968480203401c403a070306108030766021100c039510201510300f07400c0090441d04113048a42103a400c00d04000b98a0f001200c00f2004039400401545016200c00c10100c01045181c0d00d41404c80c400 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 807737562 1250 807736312 807736331
    0x21902070e150d050706020c1009030c0b03070903050f06011a0a0c0b060d06020d090212150103021509033a090e04050f060403091a0316030507110118060b0a08100f 72
    0x2403003510f0042c0107e0700182030440b810300402c01e040c070908100f0340810448603c2040807c0501c00440c048030b05050141c0d649840d200c0040b11602c0c216040a4190711030410300b04206000061514101e43c0c00100d0b00c0591001c1a00c100510300c1010145070000d114168442e0105106d1000301d03420050080ca2010085256030387d803000e90300312051021010b6500c2c4183c0080d400c020342c0c80c0d00940d122901034418259113841501612806010281c0a046144d0301c1e04c6200083d4030071a400e00b81c00808a40c0c0d280c01ca002c10b400c10980843c00704252146140e60318241400d41c0481c060310702c1c00c54949882c55401c3c090b05800180d40140103071154451454088810700d0240500c5001d14000c0d96850152418150039040c0f0700c140418070315216600b00204022004050311313000c80c4460305c0c41c0218458540000441c1c025800c00708540f420752074402c42606040b0500002d1040718420f403400e2106448400800c0170b0320a9030700c904400d41d00140250804c4070440d51110351024118080010903200 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 807738812 1250 807737562 807737573
    0xc1b030913061a0406090612180b090f01020418092105070c050a0320010e091812090a06180b040b03010303031a060406031e0f021902070e150d 63
    0x104000d080070000c2d60303820180100080c49200289151039668254a0a0700e42200206000518460041002040300e035a01000486400200c5807182c1e03c3da0815814460b8101481c180c00c0a880f181e00c10704c03030f1400b160740c0d900c0103000303443c1207582c6d02000c01c01505940350010043c1c54088070441d0404030140740070041e14418241d1259005030703591080e480700d0462901400850b801c1e00240d00c02c813400700081000928110401c81c0b0f80c2410303130000c4c100780c40c03002c01680d10071015942a9032212000b410000301d80008402e40c0f0070078030000304990303071401c0d00141b1203a1841401080750f040386203007405018150040101c04030291380ca080c84801c96545004140c10b0750050341000c13005078030001c010002d040d41409501d00c106103102c40340210403403550005046100380c0c4106428103480744800140c2d02d004540d0f140300b0802400c0c040c4455403014560000075070140080c2803032044c045000f10850b81c80002c022050b1411807007000641c0e105c9054080c0000d2031032040340c0d88800310300100c100041 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 807740062 1250 807738812 807738829
    0x70b01080723060d0e0c10031a090603030703030e150405100c051206041a0d1101230a030f0e0a0b010602010c180302040e15010f0f050105030c1b0309 66
    0x100c9000340100c2800e10b0302201c00c40b28800300280504a00802428083e03580d801141d001080c5a10002900081242906c3c00c0544250146e6401001080ea008440f13816070004a0001c505503820085421000308210b007250302030b2041601030303006104400002e03020354013101c01c041e106004c640a5004080d03c0145a075000c50701114550040c0742c05500300141c90040c0094a140e9062050a160451a030b41e00810710050015101e50348620a0100c03130302940307644010501c07025005440c05038050401d8803820446548150020b4203605461981004100d9140ca02c0400c680358180b07003100c2884100c0213840c005c51aa10308550b907000340e52105104100c1d2640c15485a4100109903140c0301c000790849210798131050030300480340c000c02003000342c807607a01d4280ca034101d400007483d034244c00c0b450b03240c030407004403104c650300c600000410a210f035240c0c514201c0c1c15a810404806841c1c1004540c1800265842450442c06201c007900100c0c044840308251030400c02101c0c24242c12000052940 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 807741312 1250 807740062 807740069
    0x40203090a140726210c190b01050105070308040b1e010617010f0807030b2d4f0605100f090b0f01050703030f09080d0e06010602120c03070b01 63
    0x254030945040000d241c4403541e1041d001c40303062051000c0d5140c0e400c0661101741d038681002d28024514400b0701c0913a039142c29100512900300c02c42d405594140c84100ca4800340c000c003601c2c04c0042c00d000242c598800e0049070100e03645580e40c400782d5169070341d404c042c000c1d0240c07085601d0210b486c00d03c605000c4051403c1c0c006d2841e543d43e01000966400082a2200180c01103400f94007805414010840c0c00180582200e5000c840c60003650707074a144142e4008040341810f43c904994115110084d1074070461640100303508090f442c4800d280d41c082c2142188240244000c0d02c10340c6a4144030100308101d01c8170740d20541e803090503c41c1c0c06507940200700d0340202d8854000000344041848180840303c45c4a001d0602038030208403072031048000410320304c0300703003106810810000b40c0d04040610070f411115402155030300c00d0201c992140790007a080d07004180c0241c0d056292000300800014009007a03812924071340c01500f003114800158941d20792000c100d900f050705c810044440051071181c0d00c24000d = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 807742562 1250 807741312 807741353
    0x303060f060309070911032202062205090a02070b090601030c090209131e06120b04060b06190c03030c051801052116080c0a050306131b020c0a0504060e06040203090a 73
    0x124030300380744030744201e01c23201300d03006e280b6050800c1c801c0050b182c10040752400c1045072943c4084c0042c4086000340c0b641c61b500010b4000400100344011000590043c11609108107500056940d820b082a5990f040034403000d4000008901e08001149042c1d0090549500c042c003100c0c1803410103842e5800741d070040c6070a0904081c24030300080340140700c0d106910282c24411280c0c18115a603403240b461f0803030040c0002e4051503807945030444554510782140e01e0b090801c080061031481c203510243c6103c8607040c0075008242814036419465218a0448170215080c4003032460411010004441c00e401c80a81e106007000d030510030000311030100381030500c82d00c4408041d0310380000610000705a03040c05060124441006c4c0002c1101c00c2c2c0140940f5840b12054560034008640044003d01608010600f030418400c1e0301c049510241c0d01050026484800b902d1030340c4415a69800c0c1b004655043c40f5185a0b01481c01c0401c035249040d030011074105200750101c90500b03100c0d407143c1240c00100c0d8804072a = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 807743812 1250 807742562 807742567
    0x1509180209062706161b0810020a08220f0c05061b010e061003031d040e16050109150e040e0313090b010e090c07060905100b0a080303060f060309070911 67
    0x1c120840a00e44a03200007070f5900340c05e200c104404005040410140102246007a81c900c514441c0781140500c003c0c80100200d540c104043e40100e8005d50085040710006043e0900054001f0300681004e03c1170036034800303801c010400f0703a04da4158544001030120f5010498400c0050720b0b541c0d0f40040d107031600d8465415010a580141d80600310b4041070b80490301500848200851441042d418000300d94250408985201c0c1311110031034070704104400598040e180c81c44034a1400c03400140b040d000140945c0000046884d000151000785482c840d004450b82c0b84000b06040e54031941c0c9401c001d070400b800103e607400d400780d082400d40d081070072000312000c9041000c02c01d685080c0104ca142c80000c0c04c0542000d0710391000b103044040000c0c68a07842c03032000100ba2041026513401034003102d41040070f076401e00d000a020344c0060b000352174070320b440340c0100701000c9000040841180d0140c000200581051000ca1090090a401c018803003a080d000303490001030315101a000d80f80900d114150680d5 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 807745062 1250 807743812 807743857
    0xb06030705040e1608010302101103070602180d080406051602030703030206041502040302150306030c0a09060f0614091219080304021206150f040b030a1b150918020906 74
    0x1d801c0c4401441d1340300841d1054180f00c80143c005110605503601607803004019103e14000313407140311060445018078400081c000c03003032007a030364060a01851040405046c8100300800c001103c0c400080240240c64100001c21507c7c1c040d0b0000c02520031826500d0051104076000a410079460fa807054025800c92b6082204000740010710704824221100c0442c2083e003140c0101e80341d1141c09403400071040740000802c215075002c010740080180010203c41c00030380c5810790726002c1e2190384184000c600d0144000705005004540240c2010f40c0c2d200000d0501d807260301003086403c59803c41100500941c40c600600310481d902e00c25100740035030303141c5981e410144140306400828402e400c01c0341d00420280320280c0c840702c655581400342102c120f0307000c1c1502000a0000c158040c840c9600d4802c0c1c08000c020000c007405680c4642490144001850b941c0d04c40e1031092500d04040790001908040051005081e00018018041c803c09001802c081d00000810f103554480e40c08003511600e203c0c03440 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 807746312 1250 807745062 807745079
    0x1f0903030b030604110103090c12110328020f010509270709150804020609060409050f100303080c0d02070c14150a050d0e0a020a0605030403180e010504050a0b0603070504 75
    0x10700040158003d0109140c651101030b803a1650f009618100340d01c440201013440503811441010b0034100c850000c080c480352400320640001211814024007c0e48448000c0d0140c000e000010741c1c00b224156420701c102e0b503003003080c0922200c2240f81401000d014980321502d030040c02d85c0303443d0310128003c2c5e0103418498003a0514a0000e081d081003142c00d0b8000d1003a170303250105503a200e2002d0304010340c01d80c81d00e1002400500541c2c40c0103400c074002182c002207050444e08440c2c01143d0280810600307440300380d410004502d2900015001c01c4003080401e269403c501c005000c130076000e10005051840f25a50504840c0e0160711090740e2020709a28061140b400701118007102d1460101d042c50400d080b54050034600a0b00c140c9c800084d941d40e29007040748014800c94980c1c503070043c600d0309000e84501014005070011341c1e0640007e40c00d003003280c9150318800e0700c0d10141c808561903102c0580c60302c0108805014006e15680c000e0380c03130300120092602d84e040998010400f6881c0c1544844c140580c0707 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 807747562 1250 807746312 807746321
    0xf031911091f02011130090c10030906093801210c080717011a09040f050d09080d170a02130b030a0209100f080f091f090303 55
    0x848034040d41008a8240781d590060103041c00c14a204038507003281070504007a03004000c50a0161000d42c03000900000c3d0070303203080c410130740026580d0b18034040003240c841c00c502e00c240843d0301c042c0c150b102141c001034030315040440c69003400491a020850420a41d40c0a0540c5d8404070b08480300224002ca842c03440400e00c02800c0c1c00192082254201c000d6540c00a01501062294a008900a41040c028540031408035084cd54024240f0300000b5035840c01b19603140030342c0c4949921319650b180d00194040301800340511907007001904104648e020420020b448601070021640108000b0a090004100780f2035005980c9803502d40c41c0700c10785482602418010007a10748410008810071006d0381050a8280c3d98001c8c20069005844101c001d9800201b031060f6000302080d80c802004204070b505041d00240b03403224050ba908a00c104001d001514069141c0d068032000c508050001400102400c64440d4081c0c40b901c2122024441c1800701000781a9010080480d1600c803c0410103043d0103014 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 807748812 1250 807747562 807747581
    0xf03030e09070207050118170319050c06010504150806090a02122a03160f0906050105040e060906061b0606210d111501090b0f03010209011409060f0319 67
    0x1200c0c03181c0d180200d402502c070305060040c14148002d40302c12007001002c40b4042d0001d0301e10310300808030385803001100c5a9a604603260b800c1040702038081c110901c51180c01601c1016626900078550b903401c04003044064194803403030200d140b06d4441d0004c0c80c14402c12159008a0f805009003503005100d00600481c1541c1d902c10002942c44000d2a04001000c9952154040034403402240001c1460300000d00701404a0ba002d00c40034110440030410031001c20141e02110341646041102a50358001901c50f400781d44035a0342c9115164000034041d0030302990403036100c840105a07502d08540044902400740340c8002c500700c0d90b80300e1b0302041034500342030b510400c0c104841c010784a2104c51310303003403181c0d141780c1c60f00c07000d04000302c1034132060006004001e18458044c82c0031140c0880c1d070310b0314800c4004014051100d4811103482038440300f00e04062003120700e2858180e541d6000702c1d010343c119004951114001a8200c1d4041088500007013800d0081c50140a038402801200d00401ca561006d0b264942c8 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 807750062 1250 807748812 807748819
    0x61206060b090a06031a061b21120405070308180a0506072307090606050307172203050702060304030309020a09020307120921030c0f0305090d08060310060f03030e 72
    0x2c2191000d80e10308000400700c400624001c03a109040e1071440d0880c860844400b42c01c80f202281e803000c4c140e0481403a000d003407100d10440b05040c1d038980c00c0c8100c148000078101012101045041a4036045c2900b1980c0103000c0c500b120b240303e940e41d0350b15520350702c1500811008541d0305e0b0701020511b0b00210303107001002c00711216030805582da11041d0b9154000c80c01d00e01000450601c46541e0001032019000400a84008101ca00d98070741001d4610b038000c50b81400040c1d20713001408880000c0d20880da0141c900d510b00700454407017646000401901184056050110074022180182d5469005501c03840c440e50340030a8004442c414020300e2051504904950740c0144208410f150b4000c010f0300708102c00c26404200c029440c00c142e0030304219101e801c0007031518104d04610040d010b4200008030b010503940c11601d0307050030008604460b4143d4041100d5000301c107440001c0340c07140300700c0d940009006050b521088180c040b00003c403800340e0322a400d00c8a88020800c1415089100901154402da = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 807751312 1250 807750062 807750067
    0x9010b01020102041404020304020d06020f040315020c0d050a1403010b0a0212120406050a09060e1f0608060a09170a0f03060506030601170711010c02011505030c0d110112061206060b 80
    0x620171a405041030b45c9442c041c6034003200241c15562884407280380b0701d41004003155030319000000e10710b6543c442c0c041914a4010b8503040d200d800c00b18800c03150084c09000182440c000c040b502164a030340105030110402c218800c600c480c10701d103200154000c100c0240d1860342c48080c5130010b42080d0300e082c01d04650341401e000d100c9420400c02e00c0e031944944d1064000075076584000d500801001c0c52400909450f141c40302d401e002e0103001541c500d22014404036039500b46d02c44051b807019503055004030580e0360040d03c0480d0260090f90041000c1d40d10450110700d15100d195118601a000a00021b0016041408801c0d020ba018407940c40603040a4038854a5813800c0c10019140d415030700f22582c001113880c00001c9140b446496441000d111100080c4020740384008000d02034020b0009a402016401c400041d06240000c0d88040d1038201510710542e1514075100c95464031040071103541401012000c49180390140d205040151480c0941c20080d034074241003003000c5405542002003a0b0204 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 807752562 1250 807751312 807751319
    0x3060901050c190507150c080a050105030a0b060d0b07090608010f060c23240a1a1905100804060c0305040519020a09050c12150904030c0f0c08010509010b0102010204 73
    0x41400ca0350604055500b583d4001000d0308119840c0c46170f042d010740185108500035400c40b0040d0040921000b05a07900381a5880304000181118000c1c0b1030a64160b01c0122140001004402442ea0224008003256001c504035100c9440c8080116410382c0003c0101c10f0522455030040f01c440e000d02401000e44020740d007400c9000d40340c1c099100000c0c01d400d030100b8111000d01c18501401d4400384501007950ba1070018a1403032a074610310b6840845295110b03c0001d0540e480c1403142800002484120321000301e403500c20b0040070740c0c440880c1c000c0a40119004a8244c036600124598102c02d9581e8454a00c0c250400000b2620820381e113a04040c1050280030219138005410709100b16206800d480310303a01ea2000405010599014038120f03402c00c1c0070030070340d1881d504c041d01c03020382c1030400e03400c03995180300510800e9803500d20600c0e44200c207140460b010904c100800c075006445450040000300c100e8070b81c0d0000c152170b5844601d940e9103500070000c03135480a008591022000380002d5003810308 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 807753812 1250 807752562 807752581
    0x305011508130f2a14040e2d0d17131203020a0216091b020a0f080d020d050414070605040608180c0a120209010e040f170c0f0a020306090105 62
    0x20b848a0140c10641001c0c01c02c1d00b40441d0130b0741e154298200703000c3c040d541c032a00604424181c403948252141c28180300c01507103da050502410240ca124100a010380c1e6202e6070030301e13406d03510b090504040c100c2d0100400b203840c04204400c7d0400c102035222800c034611812485505980010100d03040d00d014682e0351000920368051801c1500d805050142c0c83d80400c04080346402e51034500b0801c018585000059116100c2e0310401e501c0600014154000071035041c01c1e070b501e441404005015140038100100803a54403405403812044519000d441e2128201e10341307042c4c43c425101514107110010103c00004030401159004005c40e00b030041c1400d250041c044c1128000070710a07200040007404071002d000003804000400b003001418601503545403c41c9051000c5c02c6035049010300039400002c5103003007107024090b100310303401308442c035942c10340383c0e2074400704002e403e48502d4070360040c050224000710070320107038408490a00041440901c24010149003090152480009902d03080a0040c1201c = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 807755062 1250 807753812 807753841
    0x22030b06121603031e0305190f06050a1403151e22031119021c02030c0a09020a0e09070813031214250504090f06030b04030305011508 59
    0xe008885103592640a240c2407424000581d40b40c0c00071442c103100200406030400e030f500050201401154146a0080c00241c00710364042c2c444241e4480c00e8054020f0f500f04a801403140044803020106816980b9804110100c503540c01031517410207880710880550604000c01d80c0980a2508985018201000f10805400c0c100040501e20102d030030000364002c0310b0f404800c024100e00c9035000c010980d18140140300780701032100c14546d40229200d940700148a024410000d607001411201c0545c074003078585040d034041d403070100c2e01400b03140b6440000d41e60303024000d401800443e5000d6590609130800800000c46546402e2003000800d0500c0000ca9100112940c4a00c100e844100c22a905050694040140400703400c0301e5130030089042c040000c0e029450740120320740250340b40f0140c1189141c501155231030b81500300281c070600041094050f5600946403110101c4400552540c0f03030f86444009400460301074000c80c0d00c3e00e0041000390703045022200302c4117452500324003900b424007903100e000 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 807756312 1250 807755062 807755071
    0x1008070e0a030c080319090b09010f0210050108031c15050f0a09090c0311030f1b04060f2312060403050318100b24040902070c0302030303090322030b 66
    0xe245580c03a8207445050040340510303081803c14109640d10800c240d601e5010761000a211907586209032201c2c0c6c06072040b402903c0460031038500b400340580045071070044c6820110114848d103140c03010f14500620405011345007134009103507a11801064203015040110f0100c8041385081d8440301380f80c0203203012130f0503130304100c582040d0080b01d0400103507019813542000c40c02c5032500010108008142d0300c0002100d200b4145051000c09400c2013545880300440300000c150080048030024460f07000750f10041c40c2c0001e00c0040e0b41030302c0b41010024a01d064021400407950700841507149000d00c2d00840b036803c070850321181d548402c90511a100d280150000703040c0300020010904045108a000300c0a0034403501f2610b060402c111500080e0803004440341c0184e0480185910881000346101c81e0010f90030910ba25017841c002e445d0009510600c000e0b140c129040c100480140d40c1480194041d0760f01c04004c580b20f032800001d01c545c14004501d100c42c1c00000307040c104002154030100070b030301 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 807757562 1250 807756312 807756317
    0x9062c070b0906040909020f150c0c060415030f18080c070e060a090908070f1b050103020a020d140904020301060807110a0f0f0303060803042904051c03020307051902010e100807 78
    0x2c006c12440402c2d0071b44403081203035030b106030022000001e44107600060404070088408458400300300000b0b007d4a48641e02403070050684120000d10a123001c0d422601100c05ca240c000036038442c090115400c00c006030b0000711070b4072030009040241003404120100250034001081c64940c00c151002981143c040d00ca50000307513449404110611003202c0a4418258110181c1a00315100307181400603141c0d4801394103203881c504000030915521038800e403020084580c00030031b0740105189054401030080c1d05000701001c4100180c0c000f540ba00d0010354000d0600f07490b0f0340d900f401d000c040501031100b07985c996203a0750321000080c0040b0b40003c2c24400d0043c0c00c40103100c0701c141541030440181c4a140c1040a0910000400141001c1840c02c00e0401d00c4110b00d40d1740c2c44565a504918284c07145118403680028100924003c81c3c1040070714080261007030048a18101460355424240242c111844c0781401c1d0b210080402d558009940000103241142d88901c0014000d101508170000907060004 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 807758812 1250 807757562 807757571
    0x101a09040c0801061508160912051908070b07020c010c1205270f12060604020a1e0206040b180d0302030a1119030e0d02070909062c070b09060409 64
    0x103000088010001801c00b080081c010075880702c2c0380c0700d12440c4001c214000142034600090625804841809621290340c5e5085074481c50300681300c007250314030070060b5080d00564000080c00f095000403032040728803844165844446a080000341440001c04001c155002900c201440340c1c1e110507034090b0594405001d1496020780f030000c44440c061000007541c41c00e840c0e41c0c0d040c201081c0211043c14a03504841c03540380d11186a040c005d280402c140e0684550344844c0110750a841c0c40d4025201001c039a01c0d2108050f140c00c007420b90310003043c284502c0540c10000c00d2009200007100159405141001041c5005120040b0140e454112001c250300301030307010010a101e0340550700080c882d08610b000c0980c5421010302080c8058060720980300c0404d142c0f01c1c20700e030718142c040342d08015040581c000d031034494a007525500181c00419003c450705a56a4011414107060303d0100c8040319009100744200c010084609161120325000600011420310921845070f03203000484080d44d98800c001324 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 807760062 1250 807758812 807758821
    0x15020c010c0f0b0702060f150d0206030703091a06010e061903050705040f0303030e06130c03080d020d02040e0402040b0402041211030a05032808040807030c02032a03101a09 76
    0x7007070b20402c040042982410100303025415a0005005000b0640842100096181e41d1041c5041345410340800b6045044c0e0f81094002d46445005980d01029500700410011881e589003204817954203c8200b1220451050240950740070281c2c03e20100240c401f1882c1504141181ca6542c40680c0d8080405440e640060295480344d000c1c1c800a0121060b8821003603180d28024000c1c0825500c03500d1513209050004401c540c80210301060ba03504500240c840b0380c11030f12211269442340102c480d019408110415562031244000c0c07001348604130312108142800d1040005840c0700c0b0400c184510f00612040c0802520500d802d07645a030f00c0050041d142c008403001c6802d240e41905c0150a0307000200d189420320401c2c00c84020708103a00c640d64141401021000e440381d12003030381c0140008209002c0400040d004403040382c1001c1c00181200c140160300d00150f4001c604200d501c41100140e806901030604080100110344200094280500741c0c2c5501c03003411b00f00c2e880a08502c138030741610125 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 807761312 1250 807760062 807760073
    0xd0f06261605120708060a2003040c0612110d060315050114010c050c0910060f03050c041206090c0f0501090801050c0a0302030415150f0602010b0d03030c03180c08010615020c010c 79
    0x20f40180f030031760140c56440c5421074190f0001c003100c211801600324040756055004858204686c807440d40b00c0031003891942000360444a5211001d012220315940310704080c0040e09500c0545604c000b0b200d4003007006800c5260041b401d40030b180302076003082d0401c0014030001c050a0348a40060b003080c64108014159420245d142001c44030b5010381001e600403d01c1540e05011005505136820f50329241d02a080c82101201218421506400e0b44a03090106004140683e001014200d00407040450884450780341c06501070f03140e5000c002201c028030010412541c020102200600d50740000700014078088550f00c2d0382d8440c0d501b100003010760002c0001c00b00050020041e102c000303160340030043c66041043c2c00c032409505004d007404001184038002007092050040b11400c3d0001f40c507056254055980580181800120328000d154a51440401f140107071054404614003801e140300c0d07494582440c07030b03007181c02d00d411049101049070a98060150001030510001c2028a482d80041e241d60424 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 807762562 1250 807761312 807761323
    0x30d02151306140f0105060a0c030e0f041b02060c04030b040206090411030106020a021e1c150c0504170303040503160f0206030f04060c110c060d0f0626160512 70
    0x400c050b00e84240c2041c01c90000c3c401c548910002c819000302640c07224204401c41c09504441000a04814000b00000c5c0c410070b0f404200000103040300080314103002c005003e80350408401005042c4580c58004515030402c03000b9002842c0448042c58181503444260300a4001440a4001e84000941313020079203070340d80509060418040d0541e04c035619250000d440348141d01c0140d200b00c1c1e2120455946040c181464101c115000702032880d0404010100340307d492075410309490030380c6280e50112500340a40541c2200001e07030b9075a903a5a0341000c1e052050b455101a42d00c0702c9620903c100030024200000b1a8020b0256550035000342182e0b180031803500415950007034022401000b84407000c144002000e0107140b0605050100141c100c80c11213040f802da688556183d808405c00d20110f05083c0001c14086130f200401107100700080d10720a0a0742c0301640220000070243c15845c46088940c00b0500b040c1e480c9001400400092202c88500c11059003d250b1054452132500c1408072010800c = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 807763812 1250 807762562 807762601
    0x72006030c0a030e100618050f0f06041a040204090c02060f0114060304140d090303030b1807030c1704080325050417030d050c190c020922050f010515030d0215 70
    0x50502c416a102c1c00803101f018002000681058200b0f400b186400400f8000d440c440c01e181d1440d150150340390000c01c000342080003076070300078404154480c1c0d5003500d031400240040e00519402080f80310798901c1c02072500c48002c101e10966240c8034010b1020070810041c41c11214811945030792070343ca4038200308002e001e00d80044025482040000011960000f0003481280e00a0320100442d01c02e1506000102c5480c0d0560014034200c1e03800a20304a020360b0021a00703403800e1911188405042507001c800301010344068440e244080204454803103030508100d0094034035500e00b400741e4208200582540168000c0d40c40300c03c0f810f5130341c2d100481c08101340c4a403203100c00800d200700d040403560820b00c0e074440a400201c00c031020302c4c0100c0703081c0500e0361680c6065000e40503440e1951002e803084400820102c503914035164101804000c80d5041142d4a1850807500000856062490002000e030f02c10080f02c0d4044c1e000400380c1800725401003642031101064042801d01c9607038003050140c583c4a03e86 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 807765062 1250 807763812 807763843
    0x40b0c040905010312030f0e280803010f151826030a2109020a140a030206040b09090105040c05030f0411191502011401030807020604030206072006030c0a030e 70
    0xb00000280072480c2680725048013a41c030304014080819402505662005102501c60740c400d100d4441c0103a43c0c01a0f03000310035040301c00002c0414170b55031101d209510030703030010800c0190f02000b881031804041c0100f0310210700341442028a044480b122101804a01c202a80031804190301c00b010f1901c3d4112102c0480c26809076030fa2640480400760180c81040d0344901c800d1601e50200150b0b01c0c5c42d2140b5443c550b0020b1160003010724100a0f0f07400c50300c00f0351141d9005440500d0001c010384940c03001d4806060f008052640310700d070b003100380700804505034401ca02c181c0c200342000d6009904041241d40014003502c04140c1036445040200c060375048490740c6c0c00c00c0c0100c0d645102025400200c04c00c6e03c1c00301280011642100030100c0c02d03100c0c82c08440c02c0b07801050004000194481004044c83d1388042c0056080640c3c81e00001c1a50304451400c3d560800c0c04103e1640a200c40023060032650400c0b5070050540c00c017101c1101c4c5d1800f4604c020014150342d1403104043d4901001080800c040c1e0a = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 807766312 1250 807765062 807765071
    0x80d1103070b070c11042903070803070b0109140601050f0702210c120105010506161103070905090c01211a0a240c1203020f120c0405030d0215040b0c0409 68
    0x18002130141c811084160f0311704985040c003128074a4140184540c240500295151072403000c1d2602ca004521038400c0b0364188510480040c226a0910191001c1c501841c00b038682c946c90001e1000540761140c6448120b01c440000700613003a0b800101356210040500726040d203502e01480881c261510030032480c1f02c044003010307000600301400030740d81d0002c5800365204484410002401400c0e10400e020305980500b007405132401c001c1c48440300e17084060182c11223400c0588408081303818001190016000b003515841044000308e410898a0717a81c42c02844e00c10004080b0146150b11821641000c0140a4560030f200348403040513440c05407200001031042d2007040d90744060313400141003007000c5501a0320310030740d07034a185000e10f00c034041c41500696006040801c00030110002d41c010100302c103c1403002d02c014507003030756038085103481784401503911a610743c01c00c020107280403146012081154400e8003900c1074ac14110800340d4210754404c030807900d1501d42d485031003c42d0195030800903055161 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 807767562 1250 807766312 807766321
    0x8070507030c1e03050c0603041b0612060b0901020a03031d0618072102010c0c091806110403031704080717031b090108070e0415030803060306010f080d1103070b 71
    0x140c082c400c0c1110315140398009501c2d80700790300008803141844040c0090b0048a1403607081e05112008581c0310b8030612000c412016003e0509502c0300b02c2d90804000203c2c035460280b04542c8034840d1501508929281904041840c80003d644c1d0003c10030043c101901c410144082203c1c411408403080c0e910300903a9000c3c68884070710800e01014200d0003441d0311440300001a010510802c0f8104440501d021030031032030807a0010340c1d4800b1204012154000a1100003600e51290310400102c0d005c402d8000480e1112801d1883c280c80c880c0d0804548032001304001c10010f0780082d511040c034004440f040c0c60340e030ba4030304194081c0c3c0036100010340513a590144d08607540756a080110b218800c0c070740002a85058100c689506406003003101c0e80031611410109900f50f01032800310003a00c10040000c901c1c8803284018807054030702540b084442b150040240012442e051101d14058201210203103002c80c40c00c0031065a4910300a40032083c41003152903081c24103414401c541c0f40c00d80181440409080 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 807768812 1250 807767562 807767573
    0x908032706071a060a060512091905160801020306060403140c040630020105030402130b10020a0302060109090f0b0a0f06031406070816030e0a020a03032a0206070f0807050703 77
    0x1910382d825641c9083c000700050403464562464000e43c0c442c1c2e56002d08183c42e58018179a002d00103062001984207800c2509194415401034412061040740a461000564801d13000d140c0b19a400a0003680d0050040003155142c10040c0c60032650000c0d40d00109284060070103003400d075841d0813650840c2c18210080707045040d4001da81c0103540030a042c05003102d801c1070340c60f0100042d140001c0c0000c004101190240c5400c40d0010a0b0000a140000e03074511920000780403103008040c0035000d6000301c5003800605406001c0b090041504680c00d0240150aa41352140d1503207681006040344c14020126650103c00c0d4041d0214100402042020320340b00e0821025a1140254005440c0f20b81e1000031740c2688030319181800340c01175000c1ca407132000301402d040c0c0142c100c080e458202d603c1158220030240c1d80300c409d40c40c01540282c440c0d000040500007000c9440e542114410700f4500f07203140240051b15a5011540f00f240c2111504810841c1417500881510403080090035522a8141c080280718 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 807770062 1250 807768812 807768833
    0x6030515032119050a120b030c040506040239010b0d0f15021804180b0117240702061b042306070605100906050f041a060c0d0f090803270607 62
    0x145e030f80310b41140f060591649000d907041800c04c076070541c02046600c7d200f402e00b07800c03803038000c0c070010401740c1030444111420011741a10b45900607000f0721422149a0006612059036240308050700038000a4042e2001c00c805a170035010091010008802d4201800758501c50740f003010710a1841595107480107107210001c440ca00149030302c150b20f004042120410080210002543c3c03044141da81686892120315001003003940444240c00f82c03052524440c0092200d0b0320342e4044190f008119801c0c041d20003071500600034050400c1603002c040e04d080d04034a80080e40d0480303041401d4003155030000c41040091400320071416400c20004100081000400d0b040300f849420410308010250b80d854001400b41c0e90184142900101c003404500150300b016040b00010207241c43c0001030b0940c031000813801c41d902c550b511103400c0c3c01c6050341c000615480820700030201013920708112802e0070a08c038242c903449800750303091956107c07a481030030302410b040c84000e01d144001c00082d01c032002401c0105501c1c = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 807771312 1250 807770062 807770077
    0x160b0a02040806011205150609130c080d110c0a1a070204060e0910050f0118090501020f040f08060f04120810050316080c0a06020607081806100603051503211905 71
    0x140141f00e0819210044125024843d01004080d0041030310b03545100c100c5012118000e95030b01d0f62449011840c8030081050314100034180d13862110209070203002a0405030740440c100d1140340740300005c01401070940c1e032090028443c140350b00d0f41c0d1804c07440017400405244d0b001c5500c9055902c1041032440e001309125459a80c42b40e418461540c03819809040e01c0d10034001c80c0b0400e100c0c100c0c9400c485582e9403010001c24450340c001450715074092400c1c0c100382c0140e44801c00e990305c031180174041010140034054100c60148110300142c1403540c2d5031020520706241200401200d0000107400f000140700344801404d003d0199403514400154003400314400d40500e902607c01c03598003c00310708041409500302c5104d64041e010dc0c0d00d0301c003422075440c0b401901c06008100d140c4542400c0d2201400201d0294480e000c2070002149005806030035034100400030b403055809080c14401945005c14070b060495100e550403000c0c0c00c101e030148007250082100c041c8031080440195084140c0040080844 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 807772562 1250 807771312 807771323
    0x8220f0b1608060a15230702010908060103081c0207021305011409090a0816060c02100c050903101d160611030f0901050a050c0f010c1103160b0a020408060112 70
    0x2003010004050b1404501a55a560081201042088144c0003c0c010302c40826061801000e0201c10660344400818626880e420b400c000189140441d80c01a01500060928001400b03940d85582c413400d0072801603205249c001001c0340b10301c0c2e03940310083c0e0440b802143d0051405170703031050b415014002000300f4001c94500c3d84154207040c465191034403510348558100c400400c5031170201d5076040c500b40c0020309100c4019603140c2488000403071501481c070140e09144d006290321520741136030704d0540b406002800140316007000004101c0d103012840d000800350314480451444001c41c00d0069050141400740c440d8054603803201040194100c0c0310044405079959110702c40d5020005076100c0c42800301100d201c400030812100954051b201801c036440c403600f461801c02200d0319515090140c01000c88c01d040e591041d611580581052354030401c040818020f5040200146001404440480001c0e0000b409480021a0b04d00340c2c0e0111000b5100300d600f03075055942e4800781b00110381181c0008440 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 807773812 1250 807772562 807772591
    0x327060106030c1e0c061112040809030106030c0b0c0c06040303020c042d09020901060f0f08040201050d06030305270303090405150d03021e03070f020108040303141303091508220f0b 80
    0x9101d407d402034030320701d0070a40044441c540304d903520302c00181c1c001e0526603010754a441c400070100c1c104d201c7c3d100003030074001c40c40c0f942d48800000013404c005030984407603c210400d010078004203600050f03103020000c0039600010b251295083c0b0701c924075519030040076071004c400700780040c078850340d04840e1351030340300f0340300000680d072980030640320460307446401000078818a920050b014840c0710b0303903508180181400f0b89032411401204007a619140c0094000c20800a46480c84c06200820100b041e460085034000c24503030000000d442c1e00c107042c003151107039840707074003040000e01008100c50007010018009a40714407a0b14000e515032038045401558050b01102d00d03008034002008039601d45600040c08c0903902007603801500d001d14050000c1d010195145003100d009034141800500800503940382640e09003103860010300c4901d0a4000d0f10b030703290648102030011504007407502d400c5104a102c2c0d04200703074200c610b60701000c841d41002d00f02c455002c13005000c2c4240d91038243e0250211421910 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 807775062 1250 807773812 807773831
    0x10603150501050616141b0f1816030221060a090204030c03020d1e230f0d081e010306050f13030f18050a0305030327060106030c1e0c06 60
    0x41101e909109868211500b00060785032020320510380c890b59407045003440d190a001c400700318540340010301e1004401401d40090170041c5800742c40d0341042c1340c04450364015401d5001e244001c0392805003076109180020809020514020b805460440102075103a49040d80c000030700000002041d11024001e901204000c01c0c100301074002c075070070750b134100348140452403a40d400e00c00003402a0b40f094510030014207034a0414554034500c4040c490040010001c2022040380d5206120001044820180d0141d95000700b10303540031450b07a109039064200b4001640e503240040002440b108268103003202070741e00210800c60160301c600e00a0384150031804c8982d503400d9080020304040400500840e07603d00f08451603e1186206400814107010031762240c03603071480071454244850b0000c4540c0c1d000801005000107102980501c1e180003820a040e08070440d1a200342c139803106008400405841c0c2e00200c155602880361107200d1483c0980c400141c041d100d40041c6440041e510442d50541041101c0 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 807776312 1250 807775062 807775103
    0x30d23010305031c0b04021810030c082a04060206010e0610021b13020706050115030216110114040b0304050d0801061704050c0301090b0a15140121020a02010603 71
    0x100c0c1620350182c002d6203019a00c0080010758940b144c2122280b03600c2d03540c08482c5072968005044d180c90b0b07200c0800713100c213140c00400c209009451303620300c1014640786200766050f5008c080f042d004580c1c2e845011b10070400e020080c1e952032004035007084030b48001900160003580020124126800b40c0950800350711500308100a52542c1e10341c0d00010390041c0310203aa2000401c00c2d08a01120050104481c031107480d10b403000766000185c2c182c465030340c0c0e500100146202d14070003419948051800714030f0561080000740c070240103000003800c4510506400003260b4000c2113200719103800440d00c1520703903656003400903030340d44200d8003114540240300c401c4407010700401320181610020749421242584c0c101c2c0c440008400204290303103500c904422020f0648080c820032079400e0180d00c44c82044c2c5444034010003600c01706428014118403907c2c00b007002400c2c0c0220440c1040f403d10f0f02c842c0518031840c001411180990300210b0491002481a845640551081c0e0449204a0740860102903c0c402c1 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 807777562 1250 807776312 807776381
    0x10603080f250305030c1803100903170402060417100203010f140a23030a0602032707080309011101090204050702062e12051f0b040e0c030d0e0103090203030d 70
    0x1c003c60384c1800845d0500c0f500300c025040043e03004d0f0b05407660510000020345090904c80c4480402ca81d502d01206c2410351111304111140680d034941402400e050740401c01c20710a0341314282c00c815401381b00d090190b1091100d0481405071202c25900da5071074601003000c004552141251486072007982d08040d04007290510126134541000700c502512040300f03d00e0440c07a2031003082d0b150141203842c0c0002681d6101641c0070702414941c0355240702024440076141d080304407800082c0d81c0200000c201d6103500204450007500d080c40c1003000740103218101405042d510400961050511b000c105000364001340c3c01d0701c0750507080100d035070354038902003220b0500301072070504034508248240501060300450251805541310340c00701e0300caa0f035a816040ca00c103442c1c401400030550f140ca030b01c5c403441e203041d008803907810100c01c3c0642100704001000a0380d402e59240340d030041c8034091450107103a070f00a42c02203000305d40203402c5d00c0e680d452102011005180031403250711811a0302c40314020100c0f4071481e = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 807778812 1250 807777562 807777637
    0x4030f0b190504150506031009150b0105120a15031a0702011d190f12030506040b0901050f120c0a091b020a2f060a0512151302070203010603080f 64
    0x4a422084c560901c14102600005040540603c40e0400100241017180714002c0d425008210070102008500000c5042c1c900c5181c402d41000018000249108010b01b4040e41040707c4550000d1207a0690110200008403540301410720f02048164100c0800701002e10392241520f0740c02080310300403540101a582402c48800c100c40c2d800303007032039683c0c50002c4e0107001d400500410088020103180c0d80c980c070300c4a1030f4000010000c3e8441040c4200d505180c0a0b000c0c0e610070880303202c107080d8107100108441503608200144070b0300070b05408035001d45c01032186060f40e94002e000c0e0381d403881c0c0301c000840103007101805038003121035205081c48120384041045078110390b00c401c1c66000d4090203240c14184003401c80d4016896031240700040c40c84e60358440140010550760300e0f0346031100008440220784800003010b40c0001c10940700140510780c0c03110003413000c2d40d440c25801130b04d030801070000ca8010145600024042040003070496450b0045001510210407500810b034295280d000ca441e010a0300003e = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 807780062 1250 807778812 807778823
    0x60c030c040308091306081b091513060504020408250e1306060509130b0f190c0c0b010308131403120c2b030f0e0312070504030f0b190504 61
    0xc002d000003510180100082c2200400c04e070340503000c0e0700302d607402c5441170b80c4150780031b0344421200d2261980ba00e45091542c1001c0f6400300440c039180c002c2c41c6031030690360a0322f8403841201e815105075680c150b010710082c0401400c110b44480d201e0704010342c0c0e41d40c5a1212041e0240c041d000c600d0100060301000c060b196003001c0d400560300e8000340d80f0303a4031003466030888407640c03a01b00114240d1a2440064460165000203d8481d009814501440031010b490302d21800240002c00c004014100c003900800013900d0f4000800900f5003408442194404000030070301d21208000105101d001005800604150340c82d0140e015a1070030b00e400840076600c021b50309600065094050048800d01400103140490280c03000c4107103076a10000822140d80702c108140d40061001003045900d44205840321007100c100b0000c01141c00f40d12913a03030180300780700a001c0e1032100004a03001d1041c0142c0b0021036200036107800f078640c940791580503072208803545184400030008840344080f0303d0054501854100e0f = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 807781312 1250 807780062 807780067
    0x150a060b040b09060a050f161103030a020a03081929060a02060601032c0a1e020a031b0f03060e060a050f06040905010e0d03092907050a0905060c030c060c030c 70
    0x7002d00c1320f5501301040c481d082c44005e21281d01002c424500401c60003015800078642c514241c503110007074666030b003440381c040e510910241411b160000341118599070103040505807a0345000d404005001c1c2804800c3e0b4442c2454080e00740140b002d0030b08240320b0007032400c00400383c8407030040c08814003940f0982c03801039215001080b143e5000380d00401a403180501d8050140176038031240380e03842142c0d05035a19503600030031015040c00000e801a448003950280030179241d200356000641a01c40c00e01000d41151000780903244c0420962911000034202c07407450b140e0329036507270401200500549044100c1c030b00801001441079011449405c2c030440921000807815141c10081c031006103489502281c2940d0b0328082c115440008000400f4285865035000c50061401d207091142c01400c040904282d0320b144120210790519801501e500c51098508291180c101540448000c01e10794081e41d0085800540009900c40200c01400c0301d8003841c0458060303485502d42d09185110440303c0d02005c0340c5c203 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 807782562 1250 807781312 807781327
    0x70c0b01060e060708161109010b1e0903010509030705010e0d05030a0b010926010e030a0c02010c0f021909050907080d03020c010204090513030906181401020a05150a060b040b 77
    0x50b0b00080003a04016080a0801c083c55907030501c0ca80c0400040c228044110110703c007000120560191248410794151415500d000d450766110300031384899403440420703a6034000c550a04841591300300d0b40010300a10040c101040e0301a22a4007050080e2080c3d42007000ca0454020b0000d2840c0985044e81d560f40d1071542c0b800351060050400010107070412815500c0083c00c2100c060804a01c000210500d114501d0b510041900b1500440240d034a2034005210515450360400719604041e074080c2402203052200345090307103075850364000c000c2d071014140503041000041d050b240c00c1070f0f0b803840c2801c10243c0c944220403130765208107200304046603200380d04c02089503100e500503124a0740883c0025003000e466902000a940307084805014110102aa202c18583c3c80f401910041115050010a03c8082c8881045440041c042e420402040c00420a1664400c000881e04290450251681120420070149441c00241c4003000c2c110700340100820b40c50700c0d010445007107c50586546240201 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 807783812 1250 807782562 807782567
    0x6160e060c0307060c020105090d0201060b0f130e1e0106022b050d1d07060f080f040f050114041101050408100e03071a07120608210c030a17070c0b0106 67
    0x7000d0700d0300c0c650209014820020b01a4007900351a00f1a603000441c1c01d15012315154a84500780c1d55030030441e030404104100440da02c40442c1d10591071625901d90303445072a0400302828801d0703805140800007450801c80401111301c890311600502101c042c0306642e0f12101242e50308518a080c0c00640340303031894031110086170b010304840c40c84c65040c95400c01c0c2100420b003048800640c50703003112110307a11280101e08424400701020300100e08100c0140c00c00050010400350008114002d00714940010506000303c01c1e112012041c3e028009220052506403506c03403c09040d107045503014502c848407005503001c0c10594068900c01002010207481c0384140c0c1d009004036280c00c1c815804104a02e801182c1503800d60b5505851b011400c940134246103000520104441184441403480c0c2181884290808114914040500034040308042c50a40202c0400e10800e00700003035034403001031100c4145802c1010b0501c15030503680b460030a41c0d60260190340700301d40020020080303403e800c010f2082c1c90 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 807785062 1250 807783812 807783817
    0x7080402130911040522110310090312050f071202160209090604030e0604120201030b2b020406052e02070f0b0301050f0117061c05030703080906160e06 67
    0x50000300700e1010301081c40c40303100071035802c07031420b96906581108203051810603005040e040b01189402d04034041d044c00400031b000c0c0204400400303076040741c0f40900d10341d0f804100741441440c034a181040141d8082ca409003c49000e00000070b0403d00744030001c0c00d1800282d08252041c403954403504581200038607000003c0d0700c80c0d61103000140001c459000542c58140c40b0b14403405030500208001c0c1040d0501034800b00081c0c15607032045104001c28005080b044070281d00b841d50a00b00400d0420007100018a00c02100a0070410350042c5201e40602203440455040718038029281001842c0d05c4005110660001040b800b01c00c0e07050004a65205030301c00070281c42c1900c5441a030310700640b40e003030098010316503901003906290040018061440c0030300c06071000210901388503010a98580003000400001800140704a843d020903c03141d1400c081030703502456016064075902e06203464060300318082520320403018407406001910f4a10401001c1e071490803180c03510000b08818008005d4103a = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 807786312 1250 807785062 807785071
    0x1005070314031315060e0a020906070c120b090106080a030f1e0e010306051509090402010c05030a180b0c100c0504080f07210503030a020f0d0c030c0807092102061c0603110d05060708 80
    0x500820802f808140d00c038000d100a84040c06008070003086908080301c0d8908082c0003110664944001004840f40010742c044403d039140c1048105d060140d07100340e40140395031015030304076003110001c20030240e03202102410b10f650903201004003545940c184010741c2c20203907010030184000c10a14040c0e02d803000b211540140305242410181039656038036400d6401c07448841c000b0a0a15070030300c11887e403a200c6007001e8148c5c5a5020b0604ca5204c8207113a6940c80e011640f000b203074ad54030700240402e10540c122805806800308694902c054080c480d5540d920a100d104400c407011843e4030f0720050380c60113103054150498010740c00c1d0340b504c4c1d51002c000d41c08454415408141000880c5140c5640c0c0140e45012019132130005424030080350244c042c01c8000c204d1410000b10f64028003507240c01c0c0d00e1030645000c0c8030300100b078944114800300e089807044075003c0309140a2140306105200840e0087c10a0b244a007200340030105112041c00580901d00d90300422503000040058801485070b0107981d400b = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 807787562 1250 807786312 807786319
    0x50607060e03090a0b0301091107050c040f0b060a1e0f021506010903020904060b010201061509091d070f06090911030c0711120706080c04051005070314031315060e0a0209 75
    0x1002c860a00044c000307291139015560515000c0b0041081a02c640f0508040c00b22112480d464071076079546094980482180315031246541d02c41400034148e05c0c2e44030010070f01010b02611341d41c02d06548060020009032000240d00819601c100c51003038030500261070300301040e400404003501c0c14421014000c40080a0314100981c0d42d40010141c0c4c1c4207041c01d80a0ba00900d0006040e098140c002801d54016401002c503908203090781091141d844a00c010843d500820005895550348804045039102e10880c00c0b058481d00002041884200390480c2c1240c0c16600d41d10242070751000700c00c068a08484821510360300500004407c0d0030198003c2101c0c0e4413803450503c4c00c06103100011185030214040400d43d603c04101070100c5074004134241e41002e106002d40341040c1c6803030009440d0f0642d00401604100011901c1c1003054040d00840d1440c601c00c3d0381d0a070312450031618504807544200400d81c0e0600c900241518803140d248913a0041d00c0195404610546d034440c1e005002e540200c0b44140c0 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 807788812 1250 807787562 807787567
    0x4050111030d050703480201090f03051b0c060a0e120d0f030b090903031b1908070e0409051e0a06050c03061f0e01202b09050607060e03 60
    0x5445500e440350b0f902c14002c0340c40005401240c0c0e001c0000100a452100030100b814113032030090003905400c10390955030304803030340d07034105075030640882c090b1458600060141110082040425400002422100310050fa4140c8205400100a5503800c404116550403020400107480c1d01c5200700c42c001e0805070040c01238903c010810880618000d141100d100001d0003c24400c1080c580c58001c401c140041121940f40d14202403552645921014050410044d040c602c0d4003000c4000400340c03000300f5001031000c41c42ca04105006000242c003102caa600042104000c0e90340e0346818071440c02420303003100003000030600b0f203019028030001341c0a054845208240c2c80d0703000600b05000f000e201d0101d2140c0325889060142c01e1210718602d07a041000840e10100c404e1a840d60300035005c6a00788000d1808000303d00e000e08000b18540c030450403802d242e0042182c41091042d410225541950b00d100300d003043c005021030103e440d944039001d0142d00a50400406000c0f0703070f45d904000340448410003502d1 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 807790062 1250 807788812 807788827
    0x5010b040e090a1e031710140613140103090c0e1006030c0215070917030c0106080304030510022d0c0c010f1b0503040e010e040c08060708010905100f092c030405011103 74
    0x3141b5802c102e80c41800b43c2002d400c148001c40c815000003440d19015586a030030104045d2501182682500601c000402541036080e1168480c0c1c0000b8070641c3c0162140001310f8480c4404180b81808440f034808030440c848001034580e1203489030007240f980960241c224000b032828030010510015000e134040101040000c9000c0d842c1d81c0500341c140d83c03848025540c80301c2c04021a8207403200c9030701c1401d0f02c0c0c0040c001080440c0002c00d681038600320b081d01c0141c1ea02600064121480000282c629030020010680c101e901c03404001004000c664074211174400501000454505004041d02c1d400102000303901d16000388035000d215a1240701e84141c070b007065101c81d11124988400d0f4410200720850703605120502c5401ca84041c00b03070280501038842e80ca041180904400010f12400140f03640d200d000a110303980d014000000340440d040200307900c0342d03070380030301c50180c60030080716000340c02400340e4040e810480c4820b0700b9200301002c0c0a1400d103440c180054840081c81c1c64401460b000410160 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 807791312 1250 807790062 807790097
    0xa0213180b0703020405030c100203040b031801020714010b0d170901110a11090f011d090c03100c03060b1303061107060501030b180606091f030605010b040e090a1e03 73
    0x1501c0380140b0380c1c00584540c03800342054549500b24800a00807035101041c2049c10354084115020f0b60a04909030781e03243ca032110050340320580720008480d0303548041003d00401c00490002d606100113240240b0041c980c001c00c104c845100c10360000c202c0205030b082044901d04942c040c100710722050404410b01d20350f00e10b1181c140301c2d05000442d102206407186800e40c0c80c1002c111600803001e000281030643c146a08920380e070b4280d20700e1111005224000440d01481000310541c0800b000d030640f0402038405030a000078010290452000c642402404282c1c0b40b203040c1030307510204400c8180405146540c5510005180140e910751203124100940d2010a6a502985000714803408105034240340c60441d01c40ca001c0310301e1440301a50082018000c0558a84100301e030172031085540d09160003070752750310f8800c594004c0d40b00801d0541050b000149d00203008014000f281c0202040c25100ea03124040b460302ca540c000f40040000c0181c2c030f0043e90700d06601400b490309511900b032501900c482610503 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 807792562 1250 807791312 807791333
    0x80309031e0c0d060f050702060903040e0411040f06051023030604090209070f1403040b0609060a080d020601031104090f0818180a150602030d0207080f04080d0e01020a021318 77
    0x13075030034903150b01488045886620a55500507001c0c805030019050414960b44c0342d120f030b03211b0030a007025070b0000b04040c0100d082080c101400014002c00180800c2d0381c1d140003074401841464440c18405020791051402010100110b000c005112151b0f0f0120482c0011560000307002203800943d00e42e069001a25420301c1c0d540603106c10380342c0c1c80c050b414a1038028202c410104000d070300f502d03051050100044040c80c0032508450120b420404658503000403690400a9500046183c0300702c0c1d00002c991500406d100b8140c03030044602ca04c6450042003400161110640300800403070510f6402000320304510040e14000000154800c4606072810000b02041d0201000c0c401d200340c1103041c0300c403101c924455461b503441504881801145840700c0a07450340190342080301c0c8580c0000e03203003003080800021101c513504c1c6a07241d039803070702e446001c01c0303940e14807020b6044007040d0030500c001c81e1580002264480554020700c1520403240800049002c4d141200d0b0342c0c0c840714240710101000440a284 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 807793812 1250 807792562 807792589
    0x616082703040312031802011101090b0a0621050309060a03021e1b122b0c0e01020d020309090601030b120106061d04060e040b0718080d0306080309031e0c 68
    0x1c54969046003012199100503c2c0140c051610307018945a80269588030070316840d409003030124a84846c4070605002d80081c080081030b801070784040000c0001d00d0383c0301038141c80000c408150f00082d0381502804010f10b020300980f2991050011822500c1c14000900d41446240340c0941010007a0110b00006512a9031100c08100301140b5400d142c40c011040403c40e80300e82004015858600e91602032520410450308404d40900030031b07074151070310300c4580c850110048004201030a10f6203c01002d80300314074249070050003620001c0101c01d100000f5a40794402c02480b6078032644600005500030314004880a4104030247d0301008482000c2c850140141915202c500c1c490001b026401603d00e0624070280c070451801c041440010300c4007030120303400fa41c04800380011b9214440c1c188c9848413180e00100803209080d02c040b480980200d20510001d010f914148000f0b0385800d803998aa000d4146200d41507485079066000003038807080362040902414041d1200b0010800c0451800301e900032 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 807795062 1250 807793812 807793891
    0x112a03190c0e07032d060b071217010602070b0703091707051003180209060a030203060406020a0206540a0203070506030c0f0d1805010504030f02061608 67
    0x110401c02c008811245035481000703071030b08000480611480080c4400c2021000c0f4501994001e4642020040c1c2d10210280c000b4544031500c941c07072454a04404900c1c11940300001e501c0d110003071001100c02d22998141c6090fa0003a011060070451080055044990203030100540c807000058a08100c0c21081e26510400b0007400b401400c20041c05803ea8542070354a04141c0b0308111241c901c00c2c080c4450210950440b558411500c0310b2001405242c02030700007a526004805c148001c10450303038000d0070021815002d417016a46c1e1203098014840301c0800e407102c0b20071020010300385111210000d103443c071201800c507003074021903041428900042015501b065400024400c2c290b1908015510052004450203807035460401c0c1d02e07290f14080c1d001d800d40442c030f0204006407800c01c9074200820240b04013081d5407407010b6030705004c0d01900342503906502083d0b000da4201d650f148080340d076a11900c408040300000c1c006e120400c68401da0018041c90240c1865030741c040e10016012034000e03404040c1c0 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 807796312 1250 807795062 807795083
    0x60c0503061005030411131a01021b0d080702100513051c08030405070e07021509030a0f0f03090f11120a081902070807030803161d04050c130b0406112a0319 69
    0xe00c0e2502232035240c86100d605562200605000d9040e00c2d0103107018004003903601000e211011b2805200d0b0307000c3e415000f0341c00000d0f004226880c607030040c0a040054002000e01000541e203505121204440080d840071034215046a070010800f40c200458002c3d01c244200c810080c1ea500030a54411403d480030b40040e040082602c00c4070400c0c0d030803950021444005103142050543c400b1b002d001c160100003003030240030f003154508a0300940c01030f0703402c0f03400c000480101c04503440c0240302d202c55405002d205008804861405040000e0b0a40d405a40302d0241860001c1c4d01c100c2001c402c00c1c91003d1411842a9100071586240a11038500290300c600310054880c1000380d010404480b08007148000c000d071001d823020305402070707840a00fa081e02c2603e0009039500c41044403545071103252020880c001c602c0c0303400949400d4070802841201c0e2240d442c0201e0803030a1180d151104100c0c465003580c0c91801740b40821a1900240c1440101340081c05c90b44040c0650f0626040703600d41d91016581c12102 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 807797562 1250 807796312 807796331
    0x6050408120a1d010b030607110304030b090a0c0801050708190207170711030d090303200f070806060402090927161d0103080304140721060c050306100503041113 71
    0xd1050f0541c6415040d030082c00200240004642d03181c1d4002d181030100700c2d0f000c4e00135044d504284100e402545d00003030201001d103490b21078695181c54804017140c2c00d4000d4040024540410303c2114061101e69860b4155600c3c0d402c80080c8144840c0901c0c01c440d5400c204803400a06d422020305805200100d0ba2521041e8070f040044070101e40080b458069001a2841002c0562100284043d241c1c142400c4001e403007406044000c1c49220011040c040c0700d000e500c1c88582000080d035004032120b500846105540b000103000070b03030050508081d00031201c200441c20580c4584030070500042242d04007030101d041c00c007800b4644040e606a281c5003d900200038400e803140082024018034410703c54545a500d0769035001000e1100420103012911611241c00b07100e102448900d0081a41810100d401996442440f4200034040d030f0072104285804003420076903000b070702901e12400004000d521000c03031046d41a035803540700030800c036807601c500c50821107160740c2c5100040003072000300700001e80d4805 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 807798812 1250 807797562 807797591
    0x13200c060106390821061305130b09010f0c1e0306180b04020d060b0310060f0813051e0709140402010207051002030d020d05010e0901050405030a0c020a0b04082b020a06050408120a 79
    0x290387e69110001420f0600b00b003e200ca840500c8410b10b58050414041603680c01131b032500400c04c10210318001410020b00003030780c0b0313800303600044407201780320403085905074000084e000c41c0c3d01489002d201c3d825034103203c6020191980b00f0060030728083c2000d8588841e03002140c088595980007500d441a0210500820003010f00c400d030003601c0b180c107005200c032803080340c00342032500b00501c41501308015980b008204181405400492486491a40d0050700e0710141281c84040707900030304100901e0481e044401d48106d60205000d1a0103030060161a07003003405004007002003080d008250f00c000c01094126000b144000d241018550600285950400510200c00400580312450aa040000340320201d20f010040b910361100c1c0d0b04081045114920210306107498aa100e10155180414001040c400104245641d08801c08640d484541c500c0d43c0c81c0344200351100c20741e005038402c00b100f100260459000b1074015014104e80ca05104032080b000510120880305022015101e0314460817000 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 807800062 1250 807798812 807798829
    0x109061703030702120c010b0306040524060609010f050c061303120b15090a080f100507050a120203060f0607032c13200c06010639082106 61
    0xd484000d945142000e4000a5803540f80500410f51520b00051842002e2400d61010703000b0303c0007030b05558940c82c09050141d12610b1a10f85000f01035a404079029400304c10002241c410800104628100032017030004580c00351840100a042c45801c0003005035031a410044544920841c541c1c21500000a1500400303440e200c0c0a6140c005007840240d00c400c2e40c601001c03d90b0213098909042e19842c0c00c0000910b00001980803003e24000c6c17181410306131001149645146003c0c0d40700f80842c6e2655401104c0310700c5914140d100049414402551040ba43d030011034105500511000300f4494007000607106900046041300421100f8000c0a80d044015030660041da5040c400a040403403101c01044116440e4506044010381d40d2141940c040724180407185403c0041c3c0c045a12010340c0240140e5440c4e00780a2b85001c6000b60102105a902407074042c2d000c07298403600c051242c811020740070040716244000b00c071103200034421400c910300d0040505901c044010f01044450428006010b07820 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 807801312 1250 807800062 807800099
    0x1b050f070f062c040c0518030607050a080907030b070c031805130b031905060f0606070213091103030c010618020c031c02071b0602060609240402040905010906 70
    0x4924804108551a080740a11907401000b2640d07149418120f841090542c48500409512614010071500754550240103080303e4501f1030078400702940a03001300b5565035000c031140000284100f10f8814078620511107280c01000c87d5049414040d1240e90716112110120341105c00907041c0f100d418103256100e5007840440000504407070f00da6040030041001e00380c01d405c0000b2203680351440719070b041d00c0411080400340030924190500c4142407030301e951620302c02d552070348a0307988641c003040c030302c0c82c284045030140c0740e00600000c000325402c0c06203400f90034031220075100d01e40c10054107071658406100902c0505003150002803540d050100c042030741c520030b0304a14040391051240c0010715030004120b40000e904804400d01c801c00001d18075002e41f1650760001c010044c101103e0320042c1c030b0b96001609a40e02c4da02568216641c10f010701c95601c4044509000c10101000400701d0108005208000380301c002d0800b61609849214010640304207034043c080032a901c0380708020b088151020b591700c0 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 807802562 1250 807801312 807801329
    0xf05010920012f070e0114030d02010501050a03140316121115010306021b030a030b0a060309120518120f120705101a090f06040609020a08010e071b050f07 68
    0x84103c000504202d500c0d0111282e42d814042890039000e441000000024a411560030b1955038407842c007041c0190012208038002e1180319101307050b26006004003811303103002030500c208041c9552141c0c0c90b10640703086413042038001080014000c030001c0741782c05e11041c010301c00d8043c0074180310001000c901c00c2042d01c261176001860ba10401702190421541160303005000940c60340c1182d0030300583c0040000c005000c034800022481506601030b04144210241181c48542290796140c0903000c0c1c5a4200c4014200c4020841c000c0280e07018101a203c95212013a20700d14a082c0382011a41c5c01048a2070803030303183d02140e11010b06520401002000c050381850b15420110a81d803a6540c07071014006500f2070b1910f407403e02ca5559444142c40209040050541896082100450309102c4069074160b000302c3c20030030003003500001c5008640702104650303640c4400e40e10f0300541109000380900b400081086103000a004d440c0c14604003000a8000c00183c2090071003054000d1600005500c003554 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 807803812 1250 807802562 807802577
    0x60102010207172101180507090602030a030c0516060603062003151c060213050f03101d010207140105060a031101050306030f061906050402071e0f0501092001 70
    0xc0c00080040f410b12092049460f00c4042d5035158802d08800807031180c440c4881c600c0002400780c114020910082e5444400708440e031188241200c111a403401400c0140c0d004000c00c10f41a846644102650b00280c6050350800100c42241000110700c0b2070305070b0307809403201e1003401404080d20692800c82100d03200441e00d0521029411050700008011400007146680b19074100c0d01c40340541c010814229688c0342c95802c880c40c05000a400c600e400ca40100056103010581d8101218113915280c030080003400382030340e502c52100107081000400c02011280c55400030300c54400340054203105205009054402003440e09140c21a00f008001c0d034410b601003201000412000035104134076100a203046aa03039074400340424940180005800700502ca80020402019480c14401c004802d24460610101d562002004183c0c02801c402401d800c0301e03040142042a0301c07200c0001603901c41c200d102c10b29102070301c0c1c603400c4800d1a0b03429a0250400c1000400384103044881c0d245001c1c09080480 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 807805062 1250 807803812 807803827
    0x50912010c2f0111120f011824060f120218010c03020f0f060601170108100b0a030c0e010609050d03080a0c05070b09070905091209100905061b060601020102 69
    0xc10920b00580c01424070302140340030900d440c4203461241c0401c00018002c1c0207880703d225020059074481c1da400c500444a5002007615100581c03600c9040b105210104440395169040340c400600c801003034055100c0307212403800c20760144081031000410054948055030103001c80050f10000358080750700480d520400a000100c0504802910404820318000c0d20403900c40c135080c1d240c98030645080360383d4400e05105600310080020107622a4400b130341d0300c100595084125901c0d0384801c0c06600a95000000300b07940b00380c12a40242080e44c07000b80b0441780c140d0359460307081032400190014941000303408014005107030090721600040a0540d020101118642c40041024501030112100c86071111500c402c111f108a05a0310690703040420740c0b540c0d003000c041059130b64216208960451f418600001c071014408104031070701e41000e100d0301d454001c64104015004807052054402c0c4005c80c40042442d40f00c00c000380140031260a5a01607091503440700900c1c0490051116045a00400c5901c = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 807806312 1250 807805062 807805067
    0x2e08060d080a0c080715050a06170a06090507150e1e0603060d0c050a060903052515020109060218010e0a06020c0108041511030f0109050609040b18030a050912010c 72
    0x903045180c06207080020f140403450704401621807440060502e44081c20400e41c0c0f9202c5610940c0502d550b1501000f01941d149030080076900d10800d44840e907081002d01401155a070f8101d182d00a02c1345007900d0300251200c11610b030950719522100d00054046203c03104a0511034841c091400c2c8141034601c050781903000242d201c1c0b00081c50140144a00d1640b84100159140300d9009000c0003030804c5451a2503450082034984284020f0b111841400e6030848958800d101c528a10301000d1207050310603090520b258810508940080110b40d82d030854600441c956101030300941007104080c005942c4040d000411100d0410130451042c0740319081045040d400052002005a00307086c910000d58880c00c014100049004207183c19604145040c090100c04d07a0080d4817800340441660342c1662201090b204489088540540103600c07031003c2400b0070440004598020240204100c2e00c600700b0940c40d085070080301150300821000305200345107161140340301034242c203084000c00c804100b0303c000 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 807807562 1250 807806312 807806317
    0x1501090e0411150a05071a09060105100c0b151801060504180612030801030c09090503030103060e010e0a0b07140f0f0c030d1104140d110402092e08060d08 68
    0x1010201038124800301c5440c3c40300c030b03403401c50a1160301548407055010094039680c031407501203d001003200f014806100705144100c3c091241000180b03507e03800c013010b120032100940408414000018420400208103110092280c1803d8412200c15030036402406041c092041d6801004048440140403183d40201968110781400b103c02d8805d20a8005c0c10006000c140c00002c24469544120000c1c035404c403884604807880b41c048906a140d803464002e085840600e002810350304100010008112540c001d03a41d0600714100004008100004141c07401400810842d040d004040401030b6240d0810050410590389802a034500031200f0302d12400d9200e00e00c1001c40c02207001c280602c02d044201b0980718a4149904204205002c010070307003507030b9082482a90154074158401c0313560f0382840700348845095803180d5104e110392900001c20020350090341c03071240c1041800c60014045414038904140400c1141200c0c0911205081d00510001c0020324160040c0020b040740c00c0002c400008 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 807808812 1250 807807562 807807571
    0xa0b03250c030807031a041a100504030c03030f140c0a110406030512031b030108101505010f210c0e0406090c0503070f140301140a080712021c08030f1501090e 70
    0x14005040c03c1b03020001d02d50320b2140d005a43c1c005203054414035000780d04245100000c00120391011944032120f800b00c51901c140d000040200b9801042080020700403c61001084007a0401e40d61001e00310000a10541000003141000da10103100b0100340a14110742e03000401c0f064609002150860302d4140d80c80800c00c01400070050000000b40d14400701d01c2c400742c42001d07030842c815503030750b91a080d2603508c0350f04605880120349404045408000c2250300c00301144c8040e15036010003110034500340d408000140007045103210454842c0600c01980c031a554182903240c442d03a5808014070700748802c8a078150800c803080e03483c048042061641040969501c500b1501c0d1191a804092a086441d140002e0072100202c2c00440049443c0440f803540100c502c0003540c000030010b586519040c1e840007144100c0d81c0c0a29008113040250502c018150040d046135540301008892a6803151501d40c01101c8428403030385030209000b01c52032030000500c1c0c1107000346007140c282c030300340741c0c085090000150 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 807810062 1250 807808812 807808817
    0x6041106190509190608220c12061b0c060510032112060e040605090706050f070c03021008191e0b0414010806160309200a0b03250c030807 61
    0x70341010513980f210542070075120400000080c19690b00406018801c0076110183c05040b03c0c1980748480702c0d05036104680581080004286924120b00f080406200c072406542050f00c8001a04540306104000008052240e5400e00005204d04007442210809041800e4440d100e00c002c00111321940360101b803003902d9a440c240025590a01a0342941603400c0b00c034000d50800f0700000784603c40c0030041e4031440c020441407040d80e85110b1440c0d00e44e02c00e401214041401445281100101c26002c0c1c4452840781e400d0344a15512600054820717404e0000c1200001c06000412005070701d0013007044289400610148104120000340003043d010a804000400b40d80d20101d030f1341ca642d650042d802d2140d4040391140c00c0c1d61600031158603040708566490102c96590701c0c17030030000e102e0700c200d0b000141c00441c81410b0501c48141703160200c0341034110781d134444084900030524450071001140507a0688814406a401c0c02001c130708130100f40d114000a2110410318100400c0d040b0004580c04441d61 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 807811312 1250 807810062 807810067
    0xf0518061504090e07150203210702070305031303050d0c08040e060a09020315010216080709051b0d0f060e04031b0201031e0207020f0d0201090306050720060411061905 74
    0x4070511440c09960f02803810f03d070400c04c028190400101c0c3c440192081c0001e0344428240c01002030340c3d00c0c8075200e5005951702d40303040424014448500c00c0303a003140c0548141d515140e0780e900d40c203195400020a0708443c848030003041003003007402c00001c02408002e0608040798140c0e615112054065846066642a40e48001500d550360f40e084103009070901403003c640b0703410003010780201910360601241c0980b00c2e840001001d070351036072a80c03011542003500500b8050b0400700c10300d01902016106600350424503407a88050510705d005441030b8180c403500000e900611001400965055501071040c0d00141010701002c00c1d4482d1659101004100440319889000e100403001490042c15090540001d58119881051f0b903800410006000703c0d09040c2d03510444040280703515607a28028003080d400c610420001d800d5401c036547c4064981000c810784000c42040281480320744003501c0c0780f170700001c0420040055902d802c0e580f0b902c094401c2800c0c10050030604000c030309006007000520201 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 807812562 1250 807811312 807811339
    0xb120406021201060216050609031906150806100e310b2404020f0702131407050c0d1103090103020c010908071406090318040902120f070f051806 64
    0x26901203580b030307003400b40821030a5a9030342030080d00e401d0110022030301038198040020345850400d0560718641c0c0c00a0280c02000c42403860403101140b124811501d140c2c94041001c5558000b402140c010103805025101c1d41c0303040782900c1c0103e5602d8201400b10f510240900c84482c0303040020380c544a90581d84130a100c1c00c02100580e0030074100800408804040b81001303c16001d40c1214200304001d00c4291664900c9a0100001c0e03000b41c5400101c6c180090150340d0251034080c445104e180601070340014500c000d8611002031020803a81000891400200c41c0741c00e400c10130800c2801107480c40d01d8000b02c00c150301ca06440307115000450b030400d0340120ba65010752800703600c10160654810310090f40c0301d4951030610b1201c90389400300896806140d000035140e4401100f2a1f01c0c4000b40d484a41081807070000b000001c00c42904280e07041b906502012004060400094040303102010082150360f1510600136040281504028050703610300b183c610100d2442001030350401d104070340c04000c0f00c01 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 807813812 1250 807812562 807812573
    0x40507030219111b060c0d030e01060b0309060a111b0a0c1e0915050406080f010c0521130209040302010e0d0f0c0605090115181d0c01030b040e01060e011e0b1204 71
    0x224024103825004a1a848441c40d4043c1c1c46800d14271100c6000344650742c0d41d019000d1103070104a440020315040040060f0b041c25065101101a6000007012800c00c4a141c4c59505081110b00b803042c000e52040321904240089001c1070b074014100c240e51072039070000d4035400e4200b000c80742c1300d801b00054651041030781e0300946503006005064098010041a9030390b2640d260749180e610358100d17584d4a0200b00ca18003c4c0701d1130485142240c0e80e81d4102b00c03030604009030080c088008240006c40020351300345500681d14034005071301541c020390011596054880030182001c01070034410f000c1c00308018560868541143c4000240303038000c03000162907526020706501401c100c0385a260114601078003c42c3c0b81c0c82c0c141c54281c1e09501d51408016084000701d003042d06c0825002c070b0403116402340c3d0f680d02c1071390f2107a000641d00c1040a0400b04400151030140da003515296007048032880000c2005100f1100050150b0200418001c0d40705102444c000380706203d446008401c01c40c0300346000015081c4103 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 807815062 1250 807813812 807813817
    0x210301051c022b02100806010503011503060b0313060e010e0a02120c06070506010e0105040203062821030e09070921021e0f040c020309010518040507030219111b06 72
    0x1641c3d02c2046045811240300c0c0c0700048185001244581800100c0102051052281ca4498101070b1a03061030340c3d08000c1500c408020980b8010105a103445003c103403508918051030103039240740071012599607a444d103a001c3d20200060514181c0c07501451711094000080c0e0300e0502e54054900540d80741003690b4050405500b0ba80caa50480d8000071005c0421030000381480c101c6100d0600c0d0342c40303640c0b2582084180d10098400a5100d51010b65420054a04086241a18510a0b201d06400c1d940d07545003591528004403403084514a500b2400c00d0580100042d40c0c004411154070842e40392510002e0800311080c0292408508442c0b031004184083c071000e516500d070001c3c60040054107180c49015a0707407262074001d000300c1c0205001000781c02d00b030040030000c11180d0055828510f0210045546411103076690745903450a0031080030315181c1d4031460307005c1c21240c0e60140c0c1c0d40c0500750040d4581522885042c041180260020403030a2001c111003140c0301e10700e03000511904c0b54000003591070 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 807816312 1250 807815062 807815089
    0x6030a020c070f0602160807080606010807030b090705180a0308030f04020102150a06050a06020606031b0a1d0601031410050f0f04021611180c0706020408030c210301051c02 76
    0x243c00540492015000603071070040c0d100c40c513440c1080300e886101687e15000948640100c1d6030000001c100250300400c403440e0301c24003914001403d8400440064016203040d5020b44c04a040012070b50b1041c00e102e500800480c105a82c01c40000d80703959244085480000c044500781048100440c04582c800d1140d59407000b058a18118a410650400c60007040707039204030ba00c5104140c2000075100d00124215103c0d8070010054000c0c0c008600c440c007420303800c0c2e1400c070364041e503400f00201c0d08030180c03112350b0700041461035988124079020340003604030b0316150802460f070302d402001c001200c0f4404e8210f00c140ca10507580583c81030303030032000325640c024241032056103d400440d0030074070007106004404d24240100c0e1014000c490b460f05100703c9000c880608001c00741d444001412140ba160000e01d080d0340300f4400189031076550720103030b41103402889070098240c004042b01000c648c90b44c19a1540003030705202c000d245501d800c00040c58010300010a684400f0310104d508255501d254005190703 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 807817562 1250 807816312 807816329
    0x60b160f03020102160b0a0c090303020c0f042c070b07020a12030314010b0c060a0c05221e0906050102011406090619080d12140708090129100c0206030a020c07 70
    0xc100c0705c0d260244121074122480305100d440c080300c21000903c19035107141107a401d9000341c030f1503d64007014031018010b04500640c0050700c6030f1100c13072652004002044480500d042142a01c1130710a07089081081c0c603404500c5481c014040b4001680c2d07030700c00701c400300c8030a03d224140c02c00c0c9501d016070250404000410680c840c1320700004440040c0b60090182504240c117480a5a4403140b01c40100c400d8080040001030081c02446107514500320b808030f01807255075500318016a07810020200341803000d0107028010b0402c1041290402074040c1c40007400b0700340000c2c4801c041074480303e821190700526203841103c0301c0d80480c0e4642c990b02c64030303441c041c0b150070340700b0313507203071196859a1384043e258411000144c00050b280443c80741e5101d100d484440783e0380354910a444020302218500400761041075103559035000840154480752a100707070500c110446100d6011020100000b80380350011b81014030490301d003194016550503080301d6220015010041e1a1640c4001181c86c2071400d4210015 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 807818812 1250 807817562 807817597
    0xf0a0608180601140906101209020307050d0515090c1003020f070213060612060f06142104150509060c0a030e0f0106030b1803070303051e040b0406060b160f03020102 73
    0xc02c0c120030003040c86444030503034142040361180010b002048460409a0002820101230312408499a8010411050000717003222505c51302d560004403080c501c8501118141c1c80045029074503c01c480300b080d40000184060b00c0c04550207808140045a240500c1e802c141c5d0025001005018500a4400d600c0c3c02030f0443c014101c1c030204a6001b4401070050001282914803041e840c11040c0c022041520715220460403443d1400b8400c0d2148100e400f1910b4403d80b00b800b60815041d60f003000c1203100f072030440f41c82c0413509041c10880054400d1018000d8090306141c200301039504005a00b6401280501c00c0a664840a0408500030100f4101007056402034082c5403800f810705401c070605484c060032481e001500c0308091600045110b088081a0750014001c41021a0185c0d101503402400024a1804510108040d1000da0710817101290020b100e10f051106000c031a02c0740320050400c0c15100c51502045180ca2302d0140c480e480e004141c0c2920a81b9107007094400c3d0145c4e4a5821001c440300e4 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 807820062 1250 807818812 807818819
    0x5060414100305010b06070c0e091f020301180504050a02090907090f0e16050a0b09010507170a0807020c030a0803060d0501060b07050c01080f010b070f080307020c0a050f0a0608180601 81
    0x1110240701e44825905903090143d00c800300e20b40401211031041d40040b0070f103080d41c40c0580900341c1100c01806440f0070300a00c400c00c41004900c92607142c640354612001650303507040503c0f0b5000c1448040d00541800d203002c04210003d88002507040500750120340104036542c07184400b0785800402e4124079581402c024504003443c02d290014081564002d05856040d00c002409181c0040513225079548030082150070018101c020000b089545010b00d051840c1040c82e403580d03048015490b90960002d40001607060902d980700d001d40e9040340f0746202a2807003442c1c0da030010740d94400009018200102c00408070381a5039030700c000300019660000c000d1000310f43e10040c0c100560007484060320207020703501e1100f135a507110b06000b500c03d800205440c64140d0a1640c0301d031407504602c0085850203401c0c00d04002252521010714410081a4010038015186a0a204d04c12907981c0c07240f40500f52401e01360b08580c1d59039560401343e03240d500e001c2c441c954a00c00c9508441604440e16042c1d4041c1c2c40020 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 807821312 1250 807820062 807820081
    0x2037020c0109050f090708130f0309080c0f0303041a121314030301080d0806040b0a030b010512070302060a030c23120f0f0621011e0b0a0305030d05060414 68
    0x380604036003600c440c0a4143d8070401d100003014801d0321213502106180000b401d0601078030a03503030000c501c801c807001405040d50340c00b80001d03540d03d000e5001c580e900b2820404010304110843d4012826241200300310106400719a40740a00d020320703591500c001c000c50040d0204d0301c0c142e82c200c01d04400781045034200082d05030f0300168a00c209440d07050412030040c41c056000000c40381201d031400010900440d1101003203030251800343c0f04640c420f0300c3c0c0f40c80480654407449004090740c0241519011549003404011410b10051003103616900240300030005070782e031002603d404081034200840e450580076400c59441800d05006180d56080c10700d04184446105c000d0070f0811900192504561030b521800c0303c01d02412540280024034030b100003082070401e10080c00100341000c4031000c114640041d418259004101100803036510700c130340117001c2201d5000d8580d0419055440315120307400d684455031130307100c0c400e584594580c4072004035039191251741c80101e1b8980031004110329824aa09507 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 807822562 1250 807821312 807821323
    0x19021c06020d0b210606100903020d031d04060321180b07110406050d0210030e030c0a0c12030f2a0506070314011206090c0b030c0706203702 62
    0x142402010304d80c4c28071813550441000c1d031113141c200d40010b0445540302810001e54800c40074000c0d04100284400000585801100800c0300b4426180c1c50811010b036170520040100c8050701d144514100300c0704002113200c4444220013511032403052119441116010381d98050524040304031a010342200090742200d2401514040d8403d100000c9540c4119041006403180d60003a241c1c07002e512109500185408100b681c4c1c01c01d4030341408503d016001506904640015042c00c0494000413078010821034403604050260a0403220700d03000c1001034070020a05080c4880c0801449a00c2d0000b00640011509030a50300c00082c400c0301501c802c52a182d1340b9a00c05035a0403020a090203019200000c2291900f816903006488118038010203803601d60203031101a40a84034490104004114090b150005510465150b800103135908950318018007203404910588003948800305100c41d03150525400c442c00452000081840c581080c61284001c0b2001400e659105104403000200141c0210381e = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 807823812 1250 807822562 807822581
    0x4002030a0308010e06010504151215080c030609030408030a1101020f043003120902040902030a0503091009060e0d03110a061e14061c0c0605120919021c06020d 70
    0x284c21403611158010f480501480c09004c80c42c2070702803032485500c0d100e0105082d03412507000c404141ea50303401406000003001604150310a13080754825040f5030034108900341d0000c4500c0000c1d490300d441d046a0307544070b0040c2d046072010482000710103c00108250103880403404880080c9588585e1100440010701010302c03541c03640380c9141600f01744076007800a030410098154440c03000100c0030a050400804d0f4084040780d01c80c2c3d4801079240561010464280c1c00e5110300010355075050a40e0800804500c0c040407842001a034400500a1591003690308129460596103503801c0109803605460350662114641c056124100c1c549081c8a00d0f9040288185c1c2000d40032244801c11441e140e00780c6001c000039034210805400031552504018424000d4540c01000d0780307038690f440e5071b038500b240407041d4001d100081022802c06d03201701392003513003a030008000801414105064404640740c00200c039006441905145042c2c101c0071209280c211149034001e108541d1807460000d004020074000c00c = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 807825062 1250 807823812 807823829
    0x10605011101020a090e0a0e1b03061305300a0905040f091e2405060109120b0412020c0402040824040b0a0504061d060f4002030a030801 60
    0x2149148a806100b11082900705955100355542410400e441b908809894094204d9503103c0025400700e09128000d010030105072180f084200c0780080514002014010008aa9215103c0310000d0030004000c0060751104021500480c243d0842406074171050350ba40819800020b1070460312540083c00405a900c11241044001ca4020981c1e04640c810f103c018003481c8031944410304030126294a0458500c41d28801c90851040300c20f0700c00503500e00510704c400719190801d0004560700b10303503400c014002a241400c0c08001503140c40c0c404034809080a800000072030300840704d02d0301c01d120109024001a106646d030710798940c001070796243e000c3d03100910301211074224070b02200320140b024091134200c01240001c6c0c40e80001400108400303001200d201c0c0e07480e4084020b000f2030f0890094a5480031000c0d24172807404225442e051400100495090320070b21a050584180740c201903e20159041c40c1701c00140d03c1c2129410101d2000e40000c2e42c5480340d8001e400130180d10400c458140e441e1038 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 807826312 1250 807825062 807825077
    0x30504050d14040e101205030d0608060f01091e050c0405150307020a2d060203010302130501081b180a060320130c12140604180b07030c0203120901060501 68
    0x14070704484149458a00800e424000c210401590016540064000410b69281e01c201d0796504201d50010080c0c00c4211031940011030b00d0000451144145030050415101030304182c50006440c0541070014054450390aa448101403e085000710700f40480d018045030810681c00c20b40900c80c0c44c1e81143c8181d61240040c120a01c01030305030041078a0203007c09800a0070001d800740d448541c40e00300c14180d0004820000300103424264005083c12025000b03000040c0e495055005000c5811462454200c480303003013400410101c2d000044803181b10340c02007051f20303a01d4074041c002000c0c4000849400d81c2c024880b028030054840c15403143d021a0b203d540c05240030341c4841c0c0300c0b00c0c1e408800c1d0030309648248054001e502d035405503000030940820910308900354894241d003100131034241032000034900510400300040c030300341485842e880c0c10894900038080c104ca950303403916841e8002d01440030540c81302e1582c55132500030801c1c5d41441d03001040410081c44d111940364000d1015214550014540 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 807827562 1250 807826312 807826333
    0x510120f022149050705030c1002180d051002030a09080c010c020c0102160e280e06070e0a0b1303170315010905030a17040b131a03090601180b0d0303050405 69
    0x9030003800d0700f100000a050340c0c1c025038a120550719030300a20402c2c0c8850004101c1c9100051052015007500c4260050041e00c80501600b01c92000208000740b40c05140c0480c248008914006408503c0704160700000d0b0f6203031b0303074611460301030561514020280100071500241003031040d0000050000c00e80c0c216030154410780012640c401c2405050030907140300c910240802d111500070b0703550190740152000c0707580030036103180000f5200081d6003c020720350b21400c0c228980d01c24045190002c1c4030340303802503e04800100240300038a8a1107181524840042d65808070610095480d004641115030000c100404025a4050740c1c401c41d50022031481c1c03880810200e40c007550600341501c0002e0010f024202e4070740d960108911031624044007040341071000050310356060004054114800500325145450510310b4401c0002c4036040a00306034090041041e1030b9000070b04e86046502140d4820b45101192040da80200080003d05170012004907040c028541c043c1c1081780102d21403c1210403245c0c0 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 807828812 1250 807827562 807827653
    0xa03091404180609031803080a0809160b070f020a060801090608121617040609060908060c090d110415030201020d11071401020f0106090510120f0221 66
    0xc208400300d8010403042c89030001c1841035111801d614400d01389440e003070052078148440d1826a40c0103c0e030303200d40003400b102c40d16804a40300390070079980002851455010190820f1910700381c060900998001315a40381404007d804d1078484a801808010580d512540010308070b8109008211140c2e08004000840d43c400013940a100c10300d081d01181040154101c1c0c02500c1d6604e2400c2c1d40c4100360041030018200c5510040c80100351503202c60324100e14004020380403408540c000c803c107402c034804101a10808400f12240f2000c1101e80f040d4481c1d0a14001051084164038203400515240f1540120182c0e03119060030349000f6003c03110314600c40070084417103000001448103943c119400400900c0807514160488040500543d00b4400e928000e080c00c40e02d0070352011408a80b60010701481404828070f540240c00c600009a280881d191117400902400d11802402072030405c0341003d854002e82805c204140c8858184c0b20000764000e00207034111003030f00410300b8000407010324468596 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 807830062 1250 807828812 807828821
    0x8030301050607020f030f0f011a010c33090302030a1209020a1503020403060207080a0e151903230a060f18090809090711240a0e0304080a03091404 65
    0x141c0050080c0e140c160f00380e083c81105401e4002c0503400d03110304030315074004d07150921048840f024100c00000d2021900300c0780302a0032001c1518181444942a0040081007a502d162500d2404104000100c0c03130504410b01840c51684008510072450aa0310f80e0400d54044002c0c0103000303690369050480900d00000c041280d4410800035070000c1030314010000720701e00f0280000c070401c0d1401c006040586c0c0e41c50b02e10603a88074440450b480d0344009080601c013900a21028a244d009882540b0485a411034903d0a442141c840803002d0380e003017070030841c00c80c481e810205070f081d4000941c15044105464201100e8400c1da508041182049070120f200882d9030a038000b1900100560101c01405400c3d4100506108800340c034084010011804c26840e0060b2003030081c2505c0d45c801070740c032200d49409810301d903040c203803c51000000032280b01110480c1c841d19810080b02000019031800360384202c0c0c074500c5207170f221081c24000d003c20002455040300a00045582c40c1401c0405081c11204010417078 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 807831312 1250 807830062 807830069
    0x60801031a010e060f0103150b13060f1b053f03090d050708070602030f04060608120301092c010605031c080106080a0b09281401061112040e0106020708030301 70
    0x2095400005050303882d0410700c2c40c42003e011f040000e0b42d100c0e060f6103c20040740a400000d0620f500151011018840790788100041c26a49000282e00240744001002c0340100202c1b41d0f120b51000a150052290500c4205a030592081d204615800003072030300c80d8881d000c0c1d01420350f005421100c2100c000d402e42c04803031081a60201800d10f0044400d020346a54100c401e054031403003018044040001d1403031004500410507102a20820300e40340c0742c10020350380141c00109254021600d140f80480004040d00d0544429040100d405040b5041024900742c01502a6585030701d40c0d40850303c0c1002c190b0000060b55402d0b815103040408403011010066081501c8400140c802c0300100401442500c42581252038040301007203031822200050700554081d00d031058042c0c1010410b907052601c6a1099941d001501e03c184140507015842101c0350300140b18035005e10007104d058401c64401800070003042003000c0201c544654840540740c440a509000e035034094454110041150700c0000142c0c1c0c101c = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 807832562 1250 807831312 807831329
    0x190f140a0e0c0616030207051002030c062206020304050a0b07090501020f06060d060c0513030c0504050a0510030b0a15230312041505040918170a0e0f010e0901060801031a01 76
    0x80c80c11000c00ca03260504c0c0304000b03030111b00074200013060300d50364040e00b4003409400703900440d11a804110800c1c00c200c0040c0c503103041c2c03c1c46806414000346c88100c1c00409140c0200380140c5940d91804c0c458200504000020a004e01c10703400c000c4120780054044040e0350003079017100c40310301007002c40503030350341c8141d0b40d4030f07405482002100005101a0448036aa1105140042c10603035001d00760300000015800440e110450003030180a241024890942d01020301942030056042105590f64510710b203000150903000240300050500c505a0443c4541340d50b90104032102c03554030444424150941c4e601c83c0204000c0c8082c629035840c0000e001e40b91840d6030200c4a1800e071038551800705004c1da140124052100502002603004a05d1092203600070180380b9a01944182c1d207062684810301e0004102c0041c0e05101605d01c040c3e101d0000003031500c0030b6542000d12821440103a60b907000c49604554010100c3d170011075100c2c5d001d81068126482500102e84084464641c2c1c620060240956441b = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 807833812 1250 807832562 807832567
    0xd240e0c041e15051011060a09120806011b05010b04050106020a081801090e07020c03100c05040603050a0605030f070e160e06090a09050a020901090e040209190f140a0e0c06 76
    0x4040166010f50520368035008000710039580c500c085901c05e65040c80d10b002003503c0d0b0055800e0080c0520010341d00c440e04070801c0020613219034403c416005030009140c1006554000517a050b4014202d8280490901c00005c0c1ca440d80307441c1c0217001e0326002c0304450080e4200000018600c2c0000b03500014a079022059600304901000b078100c0c0700100d401140d0400c0b100400c00601d10381b80c504024007842c01503001d05400b00e058028549028880c1c0e442d000300d50720b000c004409065011064400b03030f440da850023041c0d98448009000213054983c0001758540907030300340711070404400501d9000f00c405c20041601b06580744030030303030081c14500b0301d112003c1a05141802c0c41c03840c104000b0404018010142c0c40001d803030310841300458908840c080a51075000500d41c05c25a00b1000c01801030900c0b4200010904e402c0d07000c80c030066006001c0032401d0b0b5241805603040c0a003074012004120b10f21800300a01705e12045074070500c501c1035038040300841c5003d00c210782070b000c0400c40101d100e001604061 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 807835062 1250 807833812 807833861
    0x90807090c0e1828020f0c150403140903070801110703091e0509060316080f0f0a121b060c030902010e04090f080901051e0a0921020d240e0c04 63
    0x1c000c03003815411a0784190003101d0303a0100304064405040282401e00100d52900c2e45e911800782392201002002621000f40400c100001c2d0307200a921000075903418205032500420008a80b41c07d0550f00031111030f50a2150301c01000d803003940508403690080e5242000c85a44140e890940407200010301100a0b855105010070f090801d60a60020030140840307102d40c4601e20740d03403032400140e0071160140d003002810f070322a018100084a00628040d000e080c00340d8036030303445484d03848807003000c0740a0100c8104041201c012040c80001c4c0c6a4015a00344030000c98000020024800300d07500303e021940c076860030981c50a041c03042100701540b044500720110303031076243d113081600f010b845c4604000e02000441d060385608001c09507220394440106445920341c80c0040c140c0380a50700021250f200b40d405011000d03100d010400b10b1150160ba0082103403030542040450081d400c03140c020b40e42c981c0c2c50803424211640c1d01086490001f84140c520070300000301040252072144071211030303840d1050b8004 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 807836312 1250 807835062 807835081
    0x902091e060a0f03080702180a09150b011205130b04060506041d06151909091112070312092102100509010504140a09110d0606022803090807090c0e18 66
    0x1481b605000500d1080881d5541064101d40e84044504440301511080013608020030306994000c400301c4048103000c04000b06000829141a2210704034201c0c1d03d94002c41e4018849850b40d2520541000204a140c5054145080908001d4801d14000c43c030b400c07200072410300f440c071603400c03c1060f51000c0c9c40d5079100c102414480c2552151a41d42c40300426400502f108805502e040040010031804030b11000d1909003c0c203000f0551641a0007602d0b84c0421403060003000c581c400070380b517200701c80421824030075404462015507504a0b4806507003140903403103c81100c08142c400c10748201c03011440d1401d4a401100c0314010f01240c140814030500c03080c494003e0450046047c602d000c4d10a80c1c9080c0d48202c1c2c03800743c032100c1654140c21200060400210405030280b1800341100340000c0140c08109120494104407107400c0c281a03580c014100c0c030230107104c0c0c5071410050401d0000c541e4642e4440f15108020142045403402240c40b80741207244c0c40c24140300d4000c62001804410103140d0701d00610 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 807837562 1250 807836312 807836317
    0x403050d0c052e0e251e270b091e090d1b020301150b0a11010603020618180117011d0d030c0c080301030819050702030604020103020d0902091e060a0f0308 68
    0x10703101c2c580240d4242d0f080080c81c0d440c40b07640c610354041e58200c075079183c030032000d1003804041b401e001560901001031000d13007000c05215445141c2c84400c0c2c9614040826580c00500340c13620b00039400382141050142c0b01402c062840c00742c0042114100703540d11040b404568a08090107041c02041c2c044030b02c170717404101c00c561410041c3c0c0040c00200b005990f48480048035603181d04011022a0007044080501c0e03482986050b044540c500204001c43c01e40d00092128096003584c3c60b1030341e0304504401055220303a04681d0010159002d21010b55071501c80e04103004820510b4101107603c1d0100301680500c1d040340d150403044017540606460f03035540008901915000403003906008040c900d910005040d0f030000c0d8000d60140c04840c0d100d207402300342e039030010090910300f404101042c000711001da038012540980069090a0051f42e4070a0803c0c420090030000c580030354051030610800c51045102c0400300480d4802c00b9419519a45050400109032100e0182d400c0e11648924140001000c4200 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 807838812 1250 807837562 807837581
    0x110a03030c1103120114061608070f05010c0305061203090f06131d040303150e0f180106030b0609060d030c06020f0d020708070c091107170403050d0c052e 68
    0x7841c02c05040c121214a00e56407124400f0100c810a110041200c4264680305402d601400c9401c140703003510760607441002140c101405411410001107030400c015205804491190b8000020310031014007010180042c80100e50060040030110b00001c00401c0101c01ca80300d458000300f4801c01c0c00f02500034441d040e0802606c001c2441d004c1e800108014588030803030240e6120090300014586058500103007511a210110304e00c186900c803040c45600b0322402c0d040e0b40014400700c5140c0d966260100c0004800d500c0b1b06128065280400201c180550f210303415110f1003065502c0a4661180c82c144803d031010f05401600040c09019000009401a0000c00c01512a145c1c41ca05025060085c102240e0008004445000c000100c1ea03041183c60401d81004004aa800b0031010441f01072400c1140300f520402811500d601500c0000c05080c04141c0303010b1a007000c203c500e400a442000341c1704400c005401d54143c41340e00c010b03410100508041c618402c4e800c04c540280140d07542051000740c00503030f1 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 807840062 1250 807838812 807838817
    0xb0d060e010f1b1725030603060e070911030105010c15021917100b040605090303040905040c0f0b031303050d0b03060a1a0916050306151603090501110a03030c 70
    0x941c20296001c1c20f018612154841103c0d404005500c000040c10401c60040b414203100000300c2001081490054600c0c4c0b0490910740000c2040d040110450042229400c0140168902520442d40c0c0030005090419500c0050701003182900740807106480d404244100c60018104484000010300201c00d9013007041500c075009805e082e5130351000f4101108024007000012691100c81c1e80000828060070307001310f1280c0300c60010038240140c1420610a80c000c83e401d200c000134030120381e03880410480e402086104020025402e10345041c00c41c8160301e05c54001ca01000a0b804110800b80710101c0e8029000b00c680007100c00100e55003510f69800401b8400f011f0b946c0c4034501c6803680c5080c00035500c2101c140100086102292a4210458030416012070140c5030203010400c0b540d8103103241d070100000c1400d08585a5540100155a8004005110f030702c0c0c04000c200c1d8008011000300c0e03016818070a0f01c6060b603640c1c9030801110120010608019594844001d43c0e01007030085d40944000941c52 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 807841312 1250 807840062 807840071
    0x3031e04060239120d080f0609040b010b160c0f0807050108010608010e04020f040903110d142d04080c0a0626070908030f07020411070c061d040e0318040b0d060e01 72
    0x300d100078241740e8401c0360b0b0800328440f00c04102840d00c001c503e8640c407050481c0d082c83d040c10280c070b440391201c40501a814442c5000100011940d040d410240640c50f44408004440d50301c503030810300c00711101d208084052184c20f001192540c00358140c94103a032100d6071000100d038608550342041d000040d0059800401406217a0419119030240701d0710f03e8040e40b280301728900c0107030280b8903058684003898100700b224050081015620401ca41c0052800b00001c441c100c1381e00711248000c0d655094041020000017800240c9143c0070a488100482c2210b400302c8441e03440000343c5081d8030f1180c240d0342420004519294a0300c07c13010342c03504603c607841e08018407500c40924600d0b44d07002c16070780a11181c010500104515280c095203c40c3c42424560341e080c4100c55941c20b841e2032a900800c070a1241e80480c1a413000c6d00e035000c810032008004e00c1440174840c03060030f442d2030f50300202d40022a0380203010340184606081c00f68025054024092039007020464072620010300c5912480f04265403507 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 807842562 1250 807841312 807841339
    0x5040318030b060a0b0901020706120605100f2a03050c0a05070603020903070f0302010c0807030e03070e040b130507052701030b0906130c090b03031e04060239 70
    0x3280c4110000d14031640c86000a4185002008002c520320780c00325014010070005035881c0e980c040786080884001d4100301a0103d50740100c038028040c0e6401190700600d001c0d01080b10740d83d020540c058402180d4440c98111140d41c02a580f000c000745040c8031200d064201e203403000a00c20002080590b601ea8103942c00d1f000c9650303903103080407081e61041d00000e0300450170759910314050208000810750407400d00450b510310350001e0110b00708041c0250946001050481c1451300840091514502c001e0554503030319101c400c2c1c42c207240c5003642d054403c05e41010010b00b42c201c041001c008859088001014404e107040b04001d03400c124019024144400c2c070000540e0b070072204079407034065407294645022503e00003800d40d00d0708000401d0b8041d0548070348034160100781d54183c1001503c0500c240491703581041408249584648044407041c2403200032950358408843e00503200f5a6065802e4070701c0004d000000482803004145a41c80710f035070a01854902c1c030740d0711910400105c8041c0600304038256 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 807843812 1250 807842562 807842597
    0x19080d050d0e011401090b01020a150e030d0e0a1208060109090f0b030f0106090b090c03010e10050d110f030c1f03060b0703170f0f040f03110a0c03150c0210050403 72
    0xc03807441001c50844e060011b00c048255809848070310382081c40108680d4040f92908089075880b2407000c000e003903544400400c002414001c5034140d4208000500c1072240c81c1104a03940e40344041309407805a101c4d014589200e1040d80b8142c05610140c0d542540241000141401802d000d161106115501d44807034420b500d0511072501e03d054000c000107000d500d009041800e8580401070a8401c85501c42000104a040d00580381501c28080c00700e200e665900d540c00700421516002241c1c070000001071601003203520030240e4000c0318156504403c080d00441030581c0e83c19145101030784032a90b603901202e4280c0c1034240f490798024502e0045040e03540d84100d40081e1340902e5084c1e000030031121512401103800c03440c141c0c20041c1c0301442c0c803c1e403411996451850b10046d00081401e5200410182454800c8100c0d142015640080c1c5660620a25000d5008078813480100c82c510346988058001807850701c10106170801c030b600074010441c1c100641030000d150040c030850030b0146500000b441182c = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 807845062 1250 807843812 807843821
    0x110906130c050301030b09030913020f0f040b070212010608150402031c0203191803060c0e06040f0f0b0315010f140a031415010e040b0a03080c03070219080d050d0e01 73
    0x80740d8854695950460800406042c0000c266401c1030340100034400301915150182580003a030f81500603100c10307c2030310380b07161403003007000d200c50f4250003041c0407c003446080004d11900b8800c035101401107070036100141c03d82d0054441c80c851900130003160101813542500a0764407034402011f0300d1140000359100d020012138140040c0060b0700c040340304280ca43d429240914251490300f4003401c840001c001a00680b48680001045292940107040d1a240201071280c28543c0040c0404d07225034640907080804005845200e281d901000700000c0e40d4000c000849005804600804c1c111022460054405188080d501c804000403513103040712000c1030310041c01c28206547d8000c01d4415145100d5010316102401100001000d00c0c0c0280740b07a0380001e65100c580c4002d03280400c04140c0600003e400c0c21490780080c01203140019240000e0202100520781284211100800e803214070480c021004102d00542141e80d0106400310310040c0500040c081d800303640103000ca450382c4413001060a58 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 807846312 1250 807845062 807845081
    0x20a030e062a0c060a0e0d0e06030109020f09040c0e010201060b040f0537090614011d011407060b0103061a0406031e0905071503091502030402010507380411090613 72
    0x7503600da5031b011001c6024020854526451325021880c3d203102000540b4511061164003551540010344101c07241c000c43c1680c04518000300100445070b0240c1c3c0140221604211507401546400000f2a80c041144266815a4461034070044414185400e00090140c5d10500f010002d242003504441f41400030401c0141250030440b8008592900c014507054503819044250001e001002a9000d030340d1001c0702442d01d043d06801187d4941030003005131402e0401800303001031282c00155190038450f444e0400520301d8005ea80c2002000e6603240c001c41400d4140242681051042204003c1c8038840d0304208800b031244188030481410090840302104c805503411521034010780410032100c0d0301803900424440c080d08041c0f101c9000b540c1c410151000c0c500c02da20b00741d540400840c040da4400c00c2039510055101d20340c1c2e0038080031098144a00c60001c1e080c245041c8540046000ca5071312000c40d80e00507607001c6102c1304a110048100440801c006141c3e41e0172480d8070002c172101c00d02a00850404 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 807847562 1250 807846312 807846331
    0x9062217011506020c040c0e06040b03010f050906011407020301060f08060612031602040e12030708010905060616150906050c1b0f0601030f03020a0c09020a030e062a0c06 75
    0x24094032180003400d4450000c0119200098600204203e54011503c04517203e0102e071700241d60042400161947e00707240c0e416903003242000c01c0c0070461402002c0150305840b0603804d258200381e80c070307410044050300c00c0301c03c1400280320304400303400301c0181c201901942d48000c0002c0b9016031a40740d0400c21100640c8280701e194004018880c0501700749401607040078844001c0c6140c443c41c0c8001c142d03480c01148009000303d03a40d0003004d03141c0000f03004018040c104515420380e80d04240314003e02a5000703005000034a0f1401c0081009032034800202c2d200420901d408551180300b0341c0300c0d458011145000d880740140c43d46400d40006445202c2c2c40e1040d034010107031035101c00246005140c04d400112040c80c25900880d90a90410000146d840c1103940c801a846c030500c0d40351404034107129051030000d000b42070f040030200340600e2540142002408030399003044001c400d100c00c1603461500342e52907942c81160010712f644181d040b1013007401071040074003180e01c0d12454035401458654215544081c = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 807848812 1250 807847562 807847589
    0x5010c21120c02151b1612080c120a0f1503061b03090809060f07060203010e0f0a0c0f0f0903021203030f090d02031909031a0f1b090622 60
    0x440c407950b40300b10a68918144024010441508a6031103660005400d54134146290304190064104a01c01c0b54100384803c20f084d01700e01c20f546822059802003c903004045980030340000e031075500b02c00c15140c0c21910900d400c0d05580782c8014000c02020421001180da0f42c45100000480e00c00d0348004008500ca00000903103090080d024015001d181c903184410075040022641c0420300203030a40f07045000485445940300c805040d100e82c24804d20030010420f50004c800040e84841c0d0021982c800c42c18448020581e50300e44c5240012621084c0c034a4011480018400c40030503c103074120b10300c10006040c0500b00d25100e40014803940c08019412410b41e00000410a211001901964200112100400740f54800100c082d4607801083d0036000107008a40000700e0403807103089410005d5400c082176000008940c42183d0082c01c0071201141e0384441d00001c0740f503149554405a6a0300380c00004281004a414204540c646c01a33000b45054000c0c00c06040d80ba00f2410300c10401400204280c0d038 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 807850062 1250 807848812 807848837
    0x41e05070905221209050a090f050604090203030a08070e040f05060a060f1b061e0b0108241201090c0e07030f020a080105090604060b220806040c05010c21 68
    0x705454000f41803d9500c810810f0940003e030161040c4046180d02c0014040c10700406030040381c3c055200e500070b0b0741c4880aa2000030300c1d10282d0388402d60110300c550080c04a43d660b41c1c103000540791031110094055008202d44407107030344610348654019105280940428001c100003070152424808c0c904001555031090080d580750800c540320003442e403030801d01607115030a00b0183c200884010035444600c40d100c40c8104008150380605084c2aa407030807140d0071036000f4071510040040d0030781c060100302c0c80c80114850464040420b0307800400a1701541c503001d40e11003071069900450010302c1096480314100000601d074401107501030021400700780d809207040c2800900380e81c2c100c91008130180c4104000501140d1010324241903900540c0e4481954480314085001002e0550121924210200d0030381e070070400341c11409030801605036194071095102e510740d03911104142e500429103002110104501d5008903c0c201046000313412145045403440e00500d0030f98603801032400060102c3d001300 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 807851312 1250 807850062 807850079
    0x60510120e070e1f1203030603110906130c0e04090f0c090911040b0d051b0a1a040302040c020708070803030115030507090311121e06010b03040b0a05041e0507 70
    0x20480d4038030020002d481c90103482c0103003280e02420140b850384141408240314a400c08001c0d0003800b02480c100780c180541d04000740100010300040b01d601120001c010a02c1c82e0505005000340c1d0002c040220761101c54140100900c8120040b078140300c00425084181d6071039205052407103020320341c031140e230950780d02c0c101000701d509420a050851030300c41540081901c00c0c0c020341c44514184c0d0b002410904030720001c1c241c803408031802440c0748500f485005050007000c946680740c0400343c840494080d00d811440e01c0001d240320050f507440300140401c1016241075000001400c10a0041c4c40803942c030b03600c1c6242441c51a812500003a4400001002603910146003413969000300d01e001c00072402d0414006000c07034481d20019001c400c3c141208200b56032840c00e02c640821581080700c01040c03034001e41545213546030065160500640740000b683d102031504807032041e94410b20f070000e140e4480710100300401c8040c10640d191810141c030103655011406a001c902070184006040591818152 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 807852562 1250 807851312 807851321
    0x10290f040302041404030545040b0d020627090907231021020c010b130504051f020904050a0b1f020703032001020307091701020405010503040b070306051012 69
    0x1c4d40240ca054400304004a039221041c0c1d419845001458800784030070800f81948000303214400385110b18611086002150140200c4000301d60540d002e1003c45e0300481044170060003141d01035085102007044100c1881d42090b540100300600020005c9881e01c00c0100d0001d420845414038070350304c020000d1102d030441107011521100c440d2420320407444c07400c0109204600c000c08a0050107444500c02e9100300610402480042d41808115140c1c0b000402c1c641c082d1001c400018014200d00e16010308201d054017a442c41075030403200420001d0784c1d564402c40e1010201ca4210340056090005503803903a00c80c020309002e510143c1c008101e24071b0500400c032042e55079007003204107103400ca0340f100811500804d03040126038050908450030440c606004080c4080c2c1d111010035540700100b00b08603540c01403c40e1056503590410118a80c88007003040303080344620700526001c2902403002900048107201580da00c82c1d21450040b03400740d60384000c43c051280b001030f500b001c5140c0b0384590781c0040c4184034 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 807853812 1250 807852562 807852581
    0x70c180207170307110f0d180602031c0b0a0e04300e030a0f1a010603020a0c060b030f06040b06030c0901140d05150c0403060b040510290f04030204 65
    0x41185030544999646040607042d0591640301c0074040001586640102c4281c0c610120010940305200000b00203c0d441d102c22030007500104510400302c6074144000e000c0c41041d43c8990b002540340649100500780203920102102d4061900c50f080d01086440300304400d1f000384405ca110980c0b0341814903203801070a192111035080c11184843e000c1c0c0d031072501d8154064981890410001416807240440d007405e08502c40a04019866025142080f6042d00405c04580d03860b40310051701d980700c0310308a099129118080c2e00207050100240003250099000c19a4410b000b002c03070b0030f960f4107800a40e0034a50121303002d6441a40380d008000543c03d0038051060000000c0f20b0340c02c130960422500d04424001501141d028198000f00e12080000400000000027640b500642480c98244264600380d481804112038840c1001170340680d81c1403500410307004a007c039000c6980030b030800c1f80d25070300e4a4111500b200c480d42007040c03c20207048484001d004200c00d80405540d170701d09500500c801c2d201d6002 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 807855062 1250 807853812 807853859
    0xc0303030c0327080901120911100801060e10260907350106050a0b0a02150103030c0b090c1306210206030c070201090902030702010509430803070c 65
    0x4030032030508082a003440e8803251302000b041e44440800c0c0040f940c0501e50b140c0c0c80c1889291a00140500c2180301c001030000408448180d42c038000c5800841d201d103002e100700e20204030f00300501210382c80c1c03000c2d000403854502d29040d03120b0b09040405003142c0402144c00d00000d0808420701c040c0c5442402142c000e040c2c0e0024803205d145195181c0b0302e000b00c800c100e0710115034001d041012000000e41040000340b034001d11400b940c6848404099595200c9501030740944240100320130300b441802030150480742c141c1c4034529800025210420000c0004002c0d2005005031560340c0203d641d2005400c2c0484081903001801310300304009007203000711640030084ca02e19091001c00040c0d9562003125444012890441c1c2c80c0d600600c0142c4803c4040d40000d0f56050000c07041050140d0b0541c4518881c07a504401c580c00700116104903808440000784c0040900d0f9240b040350f4100f01d540c002d5002504d4240d1132500929520034507542140c000c01d80444202c10349500400881803600d1450750f0384144403 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 807856312 1250 807855062 807855101
    0x130b0f0909070809071e05060c0a081c14010e0408180a1202010809061003030c1a0106320d0b0d050a120807110c0d020409060609061536030c0303030c03 67
    0x501b0100360300074903201c1d042c81340c84000b8419030324003002d02511102c42c0d409a61903860f10503001400034096208548001c0709454070f884c5021102c1d110700e60314100d80c07074000c04045a4032940c81d80c58899100d800f807902246506003002c4665110000a040145142001100c210079180b000500070700f40034044a043d540a4004e2100b540b8251a05500b02c1c0da240c142840149003524105151215a0a5440114000c1400019055081b90021b1741d801815a0320401e488826940d5080c1c5425150703406d54045001d102e0441c07140403661141c41403810081c6840350580070396494901d4030287c14001c42c1c54080c881c0581e41500e070007030b4035940c12202c24100840310190700c08245540c1c00c8500c14461044035001c4841082d0740b12075202c1e81100740c001d282841001e0300c640b800c0005d014240b203121560b88211103101d1b20148507000440318000d003c0085c0c0880d841070080c0007140b40a003d104003421410040010000b410300a0050045109807400304490407202409011501c8410700380031050590b = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 807857562 1250 807856312 807856349
    0x90f0607150f15150c2d1203021305190906090c02061b030f04080f0307020d0f030b0a17010b0306150306060a050607030f1b05010203010e0c130b0f090907080907 71
    0x41c8a411014540d1905c45454410343c00c100c0a08100d030b20542c411b104400300e0510003071554206500d01c031030017807030300e40c0080d6030b0b84004a0403481100941d00c40703015441802e0186203414103508114151440d006e602068a40c440354003121303507641c00544140c0d03660400d194000c0d014099240d01030015a071341e006001034000000b4640c4001419840c113010030303034002400c201d0020191185140e103290180d480e0311f410301019580790310411790b80c2c0110345082000c800240c42400380102a10000d480c1031401c2d494200c400c90348400d000c00c1c070308065482c4e0900403040d49081200e944070b6051805da450008020f00141810018040d000034090010303140180050744608084910341039141c5040744010240c08000c07503030031201c5d05030022066010b820369010b1180540207103060b0b07000303034030310342419256440c2c024540d00c105100004d00400e4201d0401c007191244018000300905001d4440c0b900004400249194078202c1b44480403540345428040520010403081024191b0b403011182007419 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 807858812 1250 807857562 807857579
    0x1a030312040c1203051204021906080601120203090a080c10020a0512090102070b0c0901030e1009030e0402071e0c030b010b0d0b0f06031317040308030106120c05090f0607150f15 78
    0x146d000070140e01e204110114046482c1d40d00503404a041c601d18542c1c0142d15a00014a894000e0340c0a07400100754110005007041d0328400c1ba8040c2d1795030300007001d008101c5e90b10348100c2d800074203000c00b060142d121100c0003600d05000401c4821403940c2c45039a1412205a1100803c2000d0010030460380b040c8401000030f4140e0b48042c2e081488003d00700c0d124907007840100e01501000131031210302c1c05408001e103403140141d04401c0c03e10b071181d224010306982443c06c3c0000c034003400c20042d0400000310508204034144080441c0e0480c001c44501c1d911030744039110000d0000007a804400310603400507488460802a2050914408040b41c442901c80c0c0803600240303407400040e00c400b1000340710541a104101c04003080d0103a003200c56407680e07120342c1c0c3d0b03007402989a002440344401040142c4d04a04d070380d001911415041661035214039040410103014040321207401c9072025004030040007030b05c010600320a1a504010481c007404203000069107109820340c0c1ea50421540f0007001628244101c04 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 807860062 1250 807858812 807858817
    0x11106010602030a18050d02040f1b050c0c0405040b0c03040305160f17130312090513061a03071211041205010f06050f060712031b020610050a06080a1a030312040c120305 75
    0x940450f00800c5c1c2b04400c0c08018018500301442c070031401000c140c403d21607038208002e0084d010070202603500341e80617601444152007003141d0043c050603001000543e440301810186030018001e00e0180d05040b2110140f4440900484080d1150702c0d0200101c03041205000c124061104030795112820300440501000c449042404018001e550f28128807585a1290300d1607801000c00804250566071103034401002410203005001004182201e1950180c91180841e801410350380c1d40c442000c08146040d600800c0c0074035285112010800c40010400c01030250441410301580c00066001a04081c001c00c07901542e2195008102e000c54405083d41c0d018107079070030207030003a40240d04132010b584104c00610103050781e20001c900502c00440d11540c00074a6a00c141040c0020641d070a4499042100d8030702c0321320031000050401000150401c0307440d00408883d0511608468150003440002402c0d80c203c20400568151680e041100344441003622400078034140110200a01d8507803001011803 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 807861312 1250 807860062 807860089
    0x90f0b060a210c03090501060b030c031303021c02010c080907120633080d080c0a030e150a330312090e0a0b030d0801081b011106010602030a1805 64
    0x1007110030004207580128010402d105222a04200c40002d0140140040058050589142d07103001d0022942c800d00c50b044034051025000040d0031036560080c400c41d14480001c0403811406006010b01501980c0078610b0210071680d00041511080306200522003031008105110a078404082000340c00c40038081c2500d4160803070804100d0042d517410b07000c1c084c0c0d4020302508a451103401908a403203140c9000c1001d548c0d040041e5448400503040845d6003a1060300c22201c0d03540100704141c0c030700d80a41d0002107001e10302c0c000c1e102050030354100140a42c1044421449168440d03e1032414007484890516002c9410280384c5500c2400c9081d40141d00c0072400010400b50000c113960224a002d0720145c00101038000c0014600d1402d803c400d07010340040c801d25402031040a00008032103001d421030300d042c0c0f03c01c200100100e01c02600f01928402c0440c01030780c10300000031120441840140a010b02802e90754008544c0c89660920040c05c00d640c1c03098015060100c11001d201c0359075a1000300614 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 807862562 1250 807861312 807861317
    0x21030412021e06031f0803040f0e0703020405090105060306180f0106020f210c07180b040b0420090103020c15040c0e040b0f0408160c0e090f0624120601090f0b060a 72
    0x28038500c0a6034401e003034000d41140c006c40c840864000f842d4036032480d1913000d41d88410115030003529282ca065003a401540030b210342c89800c1d040180038900700031018643c01000103100d20b61070070440e841212501780944000e4144030700440188080340d0100035503d4071038807001c011300c440c5118825100304056000030050916400050180180d002006000064a0060b00e40c2901d0a24090700c0b03401003183c20481c50146061144000c40341c64540b20300388014800d0300720101c030030044c044181202d602014409062550900c0480c0e00c103982040030302c408000c0c1c0300d600143c40c10f040c18090b050300c0c0e8a5001180d509071510400002034801c00800c1d8003e10401d02c43e8149480f1072520754641e01494105180d080f42c0032203c201070000e0301c40994221040010291110346904014580750795040e94040c00ca503001c400441d00b41c04a49684c00c04501082058805650f0100300250142440481c01031085c2c2c413150040c09142e000b0702c60500500e011100820801d129032004c25058050300e4288000d = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 807863812 1250 807862562 807862591
    0xe0c010c030c12032423030c12100905010f0e06060109060c020d12080708010b131a21071206060f0806041b03240501020304030221030412021e0603 65
    0x20f034002d4104e121a941c080c0000c01902e0151441032040d0b07680d1b845443d03504070303000c0c2102600b01c001d442901200c113000380c0a44402003214050180d0ba51160800784000e20910500005154440c03003541c49952084001254081e03000740483c044d00c41100400741d00b80c1041d03080c020580c1c1c00c00d0a42c4102d031610704103080c2c0000719000003941a825503030060034401a005004502c80c0d400841e007885041a915681c0d10341e621490000b459000b102052003890500c50402d102c1500c0031410ba078050100f05a85514090031114696102408510115002098442485661038002e42c650500b444400003c008552404200511201203866008244400140450b0b072503240c3e6004030030300d01c254010b0540d0006031a07134014014003508500c03c1121b4181e80015650303400092581046a4050303000358206030440d000c014107440342c04030340e1440c04540d14001d604c040c0248003500092900751040340141c1111300601c02c2210849480b030303450034568403640407980c2e12901030320340085820210302e0 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 807865062 1250 807863812 807863843
    0xb0f0714070302030a0f0b16080705090307030c06050c1902300d0207150203030411010f0c0b01081509010209030601090b04020c1e0106320f060304060e0c010c030c 72
    0x504000403504041d40601442685d0010f0080b1b4407107007244d4134810310000106e80d54100000921200603000d20000400003070100d100113100703034050650408000c0a440140d5aaa5145003000c1d41c10307807200d0040b40010403100300840050045540a4411140305070040702c81c1e500049100e001210746c000407040305420868490542e200d44540d0740400400c0b90b0485280f030308060350301e011501c02d015154100e0b40e00d0a541e5071021096a0141e540243e102414547c0d02c001502d603460038420003010082070f0248000032030300301074415001300303112405800d0050080780450014140200a07481c207a004000401e021745000800c103046500c00703000055020040d1000602a100e1400900513a20549d02500070104860403145a1300b60004000c000007a03a820300025078610b019044e00b0391002030307000c1e0756000c2341c05222440440001000080034402c0c400001d14984c0041d2410b50318690350b41080b800b100801c004410303809109090a08110003165002810450084030003000c00d07100e1403071203 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 807866312 1250 807865062 807865103
    0x17120c0a03180b07230c09160c1203140604270c080102130e0702010b01090b03040606091a040f050903040b0702040b0a0305030a030b040911091503010c11070b0f07 72
    0x300a0011030f01910b03510180341c1051100048184030409025180d0215001c600d8000100840800c81c003a025904955803031080710a0240d041c0d02d00313400e2006840080c4005400d1455285501d14a92800a200e900e1a11410458003005222602881c030340024050b010b1081c0d40f01d090030b0008915040c6a000c020b182aa900b14055030140c0c03004d60011500840d008070b100c880c2d50594234007541c800082d90b511790041b0300b0b0307500c4001840c0c00b185801c034040c88401081001903502a00489000c1840d641d210800c0045400c005003100103000c0f04420b501991815004400c04e0200c3d6070418415070034550a080d403284250301c918061440000780d4007046485541091f45550002480100100d6803818280e450354440e0f0b20220000386026000c0030300e0f18052050482e41500000c064807144585400d2002210740070b0040d03400f019050090204995090051081070b0110350f031140c042440048507285442031582110a01c100140100c000e039154030803c3e20640da81000002141c003200038040c = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 807867562 1250 807866312 807866357
    0x30a0f050615091e10032102060c2503050f13031101080f06010e01020f060c090a0906061407020d061b031103010825080601031a07080f0c0c070b0417120c0a03 70
    0x1c01080001b2031f0703013003100345c442a4005404001d8083c0c44080d40c80c5141d160040c0b1503008003444034460340e021130038401415000c1c05407951081c201645442c50071001d552440d00010030748095424030107018400c000c0344454011500c4021b08000300f190628680111102c170004103054100304164103144800d81c400c0100b03200b4100032000355106070816a40c450801c1d40140300c0b003802007040d030000241e403901c40e02c20b0030111415035952460281100c615140154081c10003681d1043e28000b040300454494440d12a035044114080303211600808805800d40e2459001e4600e104c0060004001c4890301181000d1415100041084440c105030700d401201c0b001ca42080c0c03681e21038003001104002403406e1052400101c900e84d819070703039120309040f83c0b0f9a4085800300c44006a5201284014150704c002e484000c01d0b1030309460381a0345440d001c04d9941c200d603004001040000c050102d655400f84909100041d290600728174100c034801c3d0300d60395244150300090805c2542d0000c0303d81c01320030900 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 807868812 1250 807867562 807867569
    0xa0b0903070911090a03050d030507090608070c11030303130605060f01021c030e060702010213170a0b0c1905210c072a1508010509070914030a0f050615091e10 70
    0x85c40005031607051107591000481044400701e440c00e400b0807441381c02110030304116844c545d46c250b6075550754401200c1032000e26100b00e800668070b000107902654188040c1d40700f01041a1200002202410706005840001d4200d501031001c02109846999000ca8510300e5001041c50072881c001c01c07034500714014806d454402049018140c14891341c158190000c04030110003901481c2070716191451b00d11038122500000c406980089085000541380001041d844031409001905100b14400017802da554013a50740300c00981c00054002c6040014a8040380503021040d08140525000342c1c1000c00744500320020b0721004140c244074034070b1f072030000740c4482508408120b6480070380d90740c01c1100114107242d4000c3c0804e0501d030011986040c40200b26210701030b40d5507070032101031900e8078032104802c10b03040194050060b40c50b800045410044107001162150008101d2440e007130301c0b80c80c1ca1000e0390841501c9041c4290500882d164403501540c03455030741c000700004548401111007084a00d550 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 807870062 1250 807868812 807868819
    0x1181a0901060f1103040e06010f1202030907031421070f060603141506060f0d15140a060e10080a0e10020310060201050c190c1703060a0b090307091109 67
    0xd0012a01c41e52082c68102c140304640c95421121608000007610303400b460090b080701c40030780d6002403295803043c060f06016030742c91708001e500e10707012000030401c0e6071088540c00525403045204008102c3d0301c011110701c40c4903081c068082901280d406820120403607003411101180071503250f0510100721240009030b5030102081040356928a0002981001c04201074594050051901c1c030b1104c1041701c00c1d10450300100726601c1c0a40744110034140340c0103110f40940c00d42d541d000d012038440d01c00e000c21016080d81028000c0000c0d00301c04210102420f50483c0c010480200307a0510140c990703445130144075405081c44400390790381c0050840200f1191020461500c600561440807030300da40d0007103009400d981040840c0741e844075000d038280c85045d1503034030b1140020054a80d00c00030207841064004030340c2c603041340e03030400d29222841e03982172442040603061000400d2012524100f0b101c040246003000316641022114000240c0f207070300e203100c0d041d08a41c56520362a00444c940d011280705201c0103 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 807871312 1250 807870062 807870079
    0x130b0604030b250210140f010501050309070b0d020306033306040f0c08040302010b0a14280b0924181201090606051809071a04031e03080f01181a 64
    0x1040081d42d41c90170540392080c0c240b41c03148100f0340f051415811845803540d070400d13012691802c001198140d00083c40100c850003810070101e40301d40d0100040860f941211000368480c20480c0415003070441d06c010400e0351038011004100004034420320304880d9603031030032142d2480c0d0320140450041c0c07104811800c3e20300d1400c002c1300e8000350002032460180340294020000000c0d0b0809000a42c0c19a01800b00071455422402c051417030180c80d1056040d8092843d00c1c203428000d01c102d001c8040c1d680054040b0003000c101c1c0042e43c10540380c01c0700300720400c0e440c0130048480b108001015108044d00405498541c80c0015240d44036003640c40480711700c10008001c000b125090840c0101200d00800b84070740e8034080040b280301035007144280070300c3c503044c05014143e103002050b0000e0300318468603200d0350760b0030301000020400080d138420040141d1030040c0c403081c80a15009003421401005820b4883d03da00042c0700c50310500000380e0b86094403030750004402c0c5964080b0400142d00005c181d501010300c = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 807872562 1250 807871312 807871381
    0xc0c03030203071401022b240e070311180312130e010e0114060d061e0816210201050405060309030408060108010203040206090915040603030905130b0604030b 70
    0x400040d07024284c10100302a88010702400d0388034040100d8581c040b503034054450300c240800552442e180009000468004d210030b220420428145640c40d584020f0f0070420040c030300b000c0900d42c8000c032480c04015411078106562401d02071380325294040c1c52a00c0052910340c50130800d09103c2c0c00026806511644800003450281c1d03054012819000310000000540c00d840c5a400c034107075035402c41c24001d002e4440c0300b80803440d003104040b2225151622400601c400c1c0a040d85100c00c0840d860b00d00403035082920b00c9261034420b1000c107448010500b0100110340c0841c01108040e1452111481c5440040c00100c0700c078001d540059522a10000034480000c0d030001c0100101d5201c0c0c41550916a171b12002c0358200d020031240a034001200304051040da11340303035100d10342c04044c000380340c1280604440031408403040c0c0c3d007007100402d0304110188203e1801d0307241c0410701a02c100341400003261050106910780034601c0000c00c001080d00101d40011107040100340040d09107140360b401c02d0345 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 807873812 1250 807872562 807872567
    0x11060108060a1811061303060501032f0102060115030f0204080a0507050d170f04272414060403021203120c07050307020d0203010b0d050a0b0a0501081b010c0c0303 72
    0x101520302c011850b01e03203041c0b4603040e81c4502902d140d150b040301003401054164130600032503070b100500c2c8400d4035a45041c0800003071611b00c95079000e0360043c80d212214584558000c6141007020b0020024071403403c05840c0c0982e80041d00505440440c401014201e042d100b080e0040e002c1c8030b04944042e80041404a4504800180445514001c400f02d03095140c1e07031400d0104520300c141015180e4041c030750703419501c50101c0f4001c1c141d07040c90818180c0b8290303441d810364546a070120001d07040011899600d01802006001e81d036022041050020441d4001c10040c070200c103864490882d03001e801d013009182c3c40d515001614029900608080000071006103c030751280c1c010301d203164050240d5404905040000300a4a003da07500c00000c1d460203400b5000c1018084d00400100d074190340b20064001300c0c0e110429201c0c0c042c0e00c114010070710395076940f03081c001c1034030014203070700702c0510344001040505030000700c11110704084041c05040700000740040311804518007000d0040b407000c0d00000b08055 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 807875062 1250 807873812 807873823
    0x120c010e120d02030c0d050c060705070515040f0507050616030309020a031b0602061b090d0c090609020d0e06060102060f040311030406080f1b0d0b061e0403140a0f030c0311060108 79
    0x1048082a00d028004c0000709a031f00c1e002e01000042c140d40424001050310303018200a03c0e40c98040c030700302c070446c04c811a012010414111411528101c0400c211410030000f0040100500002ca40850030402002c0c04900c032020402c10280406403950207500a5403591600346c00919008000150700700005044c0c00c419070114416080103109217000280403d4141c190382140103040410b2502e0704980030100300310b003c02848203403103d15010100180c01e2029106040003410616400342c2c075943d500040320111000511000c1003500244100a000e070703030202e4015403040310482c100085855034181140e5074030344201a0002ca200004010030800d40050311207201d00c45000c8006c040355a5940000c84600080131035002200c0207002114800f0100d0700080c814080240030582080340b420000c074010054040c005542080004060042c0890120800110812038008011030505981c40c0ca180c80c2035078002508001034480410b081600c5000c10035441c2e01140221080d9584070384606840c1c4 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 807876312 1250 807875062 807875077
    0xd150303020a022803060c050c0d1e080103022103070b070818030a020a0b0a320709080c0f040912020f16180f140405031305120c010e120d0203 63
    0x52003404803600c00f04c101065030740c50110400c10796030f901502d9561aa00a0b10121210400f44001805544030310a4108981c0d00d03268920307a2405044440304900d015040c0e240c008000810410600500c0981c0705c86200d0940b0440010303886c1c041c0511016250b0071030298010051100f1044011b12290340d5000f01c142d8015001006000f140c1c5c640030861a550744988000e44004da001156014003290040e5030856101498950204190010341c0601c60003d490041d01d11307d050009080c44544c11400b94016401080d5050600300c0a04006200380c0d103031001d11540c0d20640011440d81c80d42d4072242c000c0124513070311050040703041903400b00c041d403103c0c1c2420903107c0b10301c61310300302e00c5e000c3e18034920400440d00c0040c0b52442000d5016039001c00f0b0800c804501c0752098840c0c0b00850400c1c601c51039a480f841c051006151070b81c03000c4524902d041e103154070007485100001c440d4040300d040840c40d00c24a40c02420301603080b88010001c1104880c0841c42c0210174021048801c2c44030360040000c1505 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 807877562 1250 807876312 807876319
    0x1030908180a0905040f0b1f03080304060b19090504060212040506060405070212070611210108070f0b0f090d020405070c170a0c0b04050a1709040e010b06030c0d150303020a02 77
    0x401d40728400f0b01c007210804c641c081c040c612a8040300b8007080240083c03075000700900400c003400181e081d02e40c20000e4002c0d0b00403580f00c080001000b080c07080a12415088610480b4280440c0e504030f5441c96400506014094019903254082400c000309a81104e4004423001014203151401d814800c2c1c80c1d080c200d6405000d1030501001904803403000c2244481c900040202605011298440e0300c000c0007201e6440380107220400041c41c5854020103c8054001d00315021001c03503041520182c240b071481d9100b1b00d540324000006000e052641030540d0f05005100c406141c0715800b80c000640e46102e003e00c040d4000e86040c0500c40700070b070b0010a00a00d603000d0001034402c2d8403480c4100301d241c071840301030f035002030301800b505400500c0c47c0302c2d1190400d008904076030341c00001d5107a01010603000e0b10b901400d8800001c0209080c1000d005290b0003a040b0740c02001109100400300d101840000c2c9200c0341458005036880340c101a1760302031802c8550801441004944030f203406540c449220701e0a80c030 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 807878812 1250 807877562 807877579
    0xa0201181503060602240c0a05120c07030f02030406080a020309010b0a080c0312180f0102030706050f04030801080307120807110703060b0103141303050f0c150f01090b090408090103090818 83
    0x1d0300940001610b00c1c000800310702103a80c0e9a500081003908080c0c508c1c1d0810408208a1454203945000280a8180308841a540d540b0321700d000340001c5c580c3c4400d901513410900c41001400d80086601d40e1200c400302c0e0250b03503561442e400034010f16070400d1560307002000000101d100217001070a070700145000d4040728502c2d0394006180282d0b00895010f450000140c140003840c90030400c1c6034001c00c00040c01203d090038590b98aa005980040328a100241d50b40c4040100380340c6c1c00089140108104d01c00365262211079102c034204241c4104440090001c03400210f00c00d0381c418a82c91014079014025500c501c0c1c3c42c0e1506030b000c1e05540030741a000908100c1508001240d2101d541d010b484012891001c004540d602a40c82e500640c0e12000085030600c010745035a6014880d540030b603901ea4403140c0c15480d0500308460080d506801070900145003250551168841c140704907045030308003440d15101d80c1a500100c015218526000b001ca00d004218a40300004284020312004c1c42142c1d03118 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 807880062 1250 807878812 807878833
    0x1406070305181b0d1a0c0a0e01080915040c0803070305030603120c2e0e060f0c0a0c030c08070c0803070c080a02010c0206130b030c0d1b020a0201181503060602 70
    0xc1d92820381803896101d03802d2600d045040f6250071903120f0282441a820015144078491400d07400d94400c440401c040b5030009a101525a803101401c0e40e102800d081403000343c01c00c072603400d54076031005c2e41c1a40c000b80018045402d00804070f581000802041c400c495440000c0e16000b400f40e001910002d010384100c010f0360001c0c100700c0003500e00300f141c1400200148030f81c900350b00c6429070001092000300f1180c14420000e00c00c10740a264000400701005001d503040c09404039541840050640442c07184c00e01c40301401c19071240162003140e8042c50288920080c50824030000d03c60310000030100c2c00341050020322941c000c405440d00030f01a040540700f440c2c0d1441c0c416101d144d40350300280000e040008060062401c0d5001c3c2c040f810000c1d030300b501e01e81c1d11100d540b4220341c001d8500391191103020500c0c04014019008011400b041e01400700c0030701c40c80c82d0001e0740d60318600100074180405042101d0781c01d207004805400904500306019032000160340047e0003040e081c001d90006004003004034 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 807881312 1250 807880062 807880111
    0x13030512040b0a1808010f05070206100e01140105160308160c030203090114070b0a020d0e010e3414120d021e010603050307060b04180f06091406070305 67
    0x280c003103440c490041850700e10622000c4500298041e4a0090344e65110b0001c14070217070921410065852408000681e400c00200117440e0960090001c0380e4151507260034803000c0300d90500c442c111184035003114460043d000040e2400d0140c10f12a0300b5000044020070141507002d1401c0740a0008482c2c03c03406c0c0003603060100ca442c248080701070301613401003088540035407107100241240c840c808449804c000d225039444031221700a803400c01072a500460610103002041c0b00d192003084c0304900070489600d01d503c0b842d40f80c101c0c10a560760760003070450b0354011081100013148c4a611200c0082d084140d107031140400c0320020521524081d5a480d48122000d40700000c0254090b0701e2034004102d50641d4208400720b81d086401d50394095529400008000b40d800c00140035224424840802c00c0c040441c04d200880d20b07241c080080302d600e400c0510022898003d07002c18500e401071004502c03400d81e820610310700c805c034254680080c801c020030001c402d0360503440b10303000d91051002c00c920200d0036000c0 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 807882562 1250 807881312 807881317
    0x106080f04050a021905030a03090806311403040f06020c0604061b020303190e0310090c140a0e13030306090b3303011503051f051e040213030512 64
    0x1042e0fa4408600e24015144c0b003481c0c0c940d0042c918003211112501c40e0b02090400414680031070101e12146821b00c00b056044c0038856219429284400109a11442050989001c00c1007a40d001d8458400481401000c102c000c0400a4000c1105d556550f681c100722080b01451103a54010302072030b2880303803484c5405812101220515665120720000416400006102c550340c100d038188010482d1800e00c0117040801c541d001d900e0784a4180e00b8001d9020305040002a03171084208034502401c10001400500e140c0b026038a10400c031101c00d03000d21010480a0442d5003146440c031900808004455600d85000c10031244a5074091000c25560090b500a460718000440d9003c1c2d1107881c10204000c00a2000c4051841c0c120818420b04007950000411791003038002d00d01101c0852100803180741c150003140e0300009842e00b5420405180380602d03400a09034080c40b4425a011041034010a00c8244c1184040400500443d50b840d07001d04d48000c0d032503640c441180d00313003d04141040e6500c5030005 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 807883812 1250 807882562 807882571
    0x40f0b042303010e160e011703040e0a090b0f061f14160614011d010b04120809040c050d06060905030303060d050a0803041b0b0304150e0717060106080f 67
    0x180c801c0e0380d6040d0400c450520080e41a040c2c0540d07032556030340d80349103003003182020b89000c00945035601c40c2044050800001e0581049101d44420483e840301c0120001c11101140c0c000d0b04440e415883c1c40d1001c2001d400312800c041e010a00c00800d01c0844060b80e000c0307a020304801c5444011034080da15062410341c400340b040e2800300f481c908800710040305600081042130180c0700d200103c00081d0303540c90115003000101544017168440184100305801030021414140454024801e616041310008940706074050b200c1450f0020041700308201d0040b0960b0780d4584000e1007070001c040c0441008110b500000b044030b14080c140080080d40c90b0182e24501c1c2a031b07802601a62a41d5a10703020b200c0902d0000c03404807240c5c85048503600106050401541c000c1c0d02c41c400e1081090342c48044111140807d03080410302d20010824400003800310a05a1407609060b8404515001070400301030a02510303600641074080d2070a001c80d504a804202076041c0c5100e07031925521500e072850740140c203010842c0c = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 807885062 1250 807883812 807883829
    0x40b0d0b010e0c120903250b040213020f0a021b010306030b0406110c0a080702090a050708040f0c0f080102040312030603150e01020f0c0102071406090a0b100b0f040f0b04 75
    0x1001030080d002c1149180c1d074454200000b091a002420b905680356100480e401350550b0008580d0001c0700d1541031121f036a62892980f00ea00469003510b58928440001d04028031549091842c00d01d0500e00d0380560706140d080c55207413626024101406901d071107450b40c54442c0f00d40070540f8000c83c3d40c028421071040e41d800411b801050391321507881a00500d001018a82c240e1401d01031819050070802400740401d1242d890f10f038503040c1e6071044c05041c6a003d000034806c10700b000204041d165004141c00c0c1c0c8250001c2c0c1d02d061020031400c0220142c04180c1041c10100ca40020100300c2d20015002403007180d01c20400f101c0075094581c4100d00311481800300600e100c01c0050042110402c64104e0102c200b070440005203400e03d024484c503a268890306021000d07135000b0401d0f2003848000a0720204516100c40609a21300d0204842c075221b260003a80148a48044804500106000d103c82e42c0070303010b00391100e90303500f02c4d5440c000d140360418441c61200c1060644041403100d4118180c404440445 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 807886312 1250 807885062 807885083
    0x60f0a080d12020d020a18050901060507030804022d0112110306010c06020d0c09140906011413030209040302011b0212070201030b03030d0f0605010e040e0c0f1c0809040b0d 76
    0x10800300d0b802140d601c500800c440d001c0c00645007004080c07004000202c295110755480f000c0341d0380b01201c000300d40d40c06148914500300041009903004400c8600365075140c0b0b00042e4070b40d11440040c014003407020405a04151100d450704044814482c4140300e0407003600c5031001c1d845d4040c500e0040e10002c2c01c4200d042b85050011031400c1d402031400101c0c0d01d00c00d28004d41440c58000ea44000c0311f0102d00c400340003800484041241200742c0c0c464100000082d100715100d8542600041c107442800b42010442d080b000807100140004503401c1400f8660084c51001355050605000f07001c0c120720907400c0407010f284202071040e02c1c00040d0b2041804c103100c0460b0f0400c0101c0c5c0054004050b808840380c0c140c001003040c10740e1303600d2a103d240070b40e8038591800100726080100040103107500c40c558a004602d04490300d80e81c1d40d0b00081d590002441281d1810140d1520408103100d01e15040000408115241300882000100c030040e000c558010b507810864181d1130010040c0e03c03819904090410f8850 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 807887562 1250 807886312 807886333
    0xf05120a0f0321050f0103440c010501082d060606130b030a0c02010c09051503040f050d0801080d0906080f07180e1e060310021e0c06060f0a08 63
    0x2a41e0b41a085091554402c2490070700480c040741528011100d1745100070022006104110510b05005c516640c0780d078014540f031030408020688000185401d50300b1a40c044032a07014004010100e9104e5056840203101075603481c03031b00e580e076003402120384074000021a5008000b0100000110580400c0c44014115912030b441400440e6104102851007004190008240040b0083c01180220008600021584e6881e04000e085951248501b002c009604808002c0b580d01c510118100b0405030840b607649031a545030450303003401319170002052401820001142030340c00c00b8503e81290404c00039903100360b449140407075802c02e050048070042051080443c0c25825520006503002104d41841c40156484201c02d40c000c1303420f40d220505541c000c0c03040011078015420719542c010781c00c0629001c14240200041d0303d80c1c003174460040c4203503408147c01e500b2209400350380d18086141d003500c1355030b00e8007880341545034001215890f004124142d440e0b295420040300d0841218082000b503d902c0c4030 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 807888812 1250 807887562 807887567
    0x60f13051c0f0606090608030903010c080613180c0b040314030403030f030905010603020604150905032d0a150203010302030d0815011107050a06020708070609121e0b010f05120a0f03 80
    0x20032090503102c0581c4c40001213814803851042c03c0c0603203800b030000c0d070311361110608150035903504805100800043e00103010b1291600030008140c050f2601001ca030510103c00b018046810000000d410200110f4000502d6401e40300248280c1e4025112590841450100d41e0740d030380f00d07510000f4002080000e164100c0f81c42035204038000b51040c4c00100b4580e94039000100142c100d5000b020703500e07032245503805002d41c0050b2a42c3c020032055025203030a41064108542200000002d9403044d040490035448000061103024520b6500100f0030111640042c015402900300340003c038040c2c4180001d940903030340901c0a052203215400303104903c80802e00c00441e611071810380404868420783d07001054035a0b821340800040d06180d13004008541c42d02000c5c5150002030fa1010090144460040c001000c1103461410210f40000165100c0000100e28091106007050042c1150900100108800c6200c155020480f00221210500d0003852007020362520300d46200100a981042e911000190 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 807890062 1250 807888812 807888833
    0xd081e060609040e0105150904050703080f0d2406051305040c0306081009060507050403080a21090c031119140f0a090b10030203041a090c060f13051c 66
    0x201610240c1040080b00202e820b490b041152000965128001c0102c54240102e4801c03d2000441d034507a40f504140c0c132000d80380c808034000034000341000102c5001c3c0d08403090480b0765080402004001c540c41c00000e400d03280d9a281140c0c58042440c1d86c000511510032015548181424050020154500000c01c00100000400d81c3c0516850b18400542110180001c454203002410081002d881c3c91400104948004080d101032010038403040c000f051442c2c0035103281150340c2c108801c0c1c6107a0401424054a1901c505138034041c00c142c0c4007001c0104035403204045a00c218080541828850204a000c0c40d00c4d0007120303403c201c4201c040005c1d860340c099150003d07402030302d440549003040c0b02003072040070640c10503043c0680703070101c5002c1401c05c01c03003c0c48407054502c0c00318203505003030351100e004d2551039030313041034401410002c17803440d5206001130f90098500416480d41c2e0660b2011650701500540c03042c1c4280aa00340000820f402c016140003441d8205550380342140c0c1c411f90354406042c = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 807891312 1250 807890062 807890071
    0x12040608190f060f0e061002030313031704030216140d08031005060f03090607080c1219050712051005030a150204152109020a15020a1b080d081e 64
    0x142c44400750040039040b485160040e00d4588040c004440c14070030714080d1050013808880c06141c04010100c16a076010050320b070811100d0000100c00660703424110b070300000c0350002154000c020001e100405400240004140c03840c05210702d541c0d0380d20b44036902c0c1c103807c0c40000c60300032054000003030000703480714010340d4010100030080d08480d8580c00440d460381c0091040b5040c0e0301f0000280030a045003009003603444a128603104107140740c900d0a441e210300a8026000c0c1c046075500100c1c0c0c00f9246c80310300c1280c030064410100010710f019180104051025094210034a10b40740c08201c00e421000440e1041e118064014903010701650b403159900c40f01d00341180d480d03030fa0900000c02e00c0301d01c088001c440d407186030362400d400baa8a071602c4100f4044174800d200009140c400c030080140c480085c03040171503076200088007010480c0c0e0b00903418049203403001800c1c001d511440210152144050505444842040310981c01c0300b108183c0d0500d00513681040d942d01814890060790030401c0307240b40d22 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 807892562 1250 807891312 807891361
    0xe0f12030c03042709020f09070215040b010510021504080309120f0306040605091302240d0914241005040515151e09180709030512040608 61
    0x30071000751011815078105400803034450110a600d161540000021a01001c0f1119020000e000d0154005410b41d00c403005050b01800c001c20005038050f00a1044600510010070300c10b20b945000c1c60012043c1d042400740c02c2c0b18003103040d440d581c5c0c0f0b4130010354010403041e00d00f90505562a113455010b060b400042c504407803481144400d03401c00b03000c10058192404182115a100c0c00c1c1001000306643d40c5400450041d155002007000941c100c411442d007094040d504410000900f803100d40d018030514030008000b01d000078a80b13140d42c405620010447e80900f1030200e601e40f80c0300d246501d1f000c1c1c212484600001080e070702c0481419402415400080c0c407170a0820a035603e001040c299841220040001c4524580b100580e0030728000654a140820f05074600e0150240d000140d4456900c0b491175198002040036051520b4000d015840b000c1304ea4044220792805003401401203045000490340c42c010300302021a01001141134800744c1d2015141c0701c941d0359a01c1401003101d0201d2101801 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 807893812 1250 807892562 807892567
    0xf4a01110c0a0308070c08070b070527130c020303011703070b09010e060c041508060f031914060411010e01091806030c0509220c03050321070e0f1203 66
    0x21540d046004000658481c0c0140200310a681800341c50314400410503014407810384012000100810708407030000340d202510840c1c548402c80101da40c1c5c0103094200307048074030003c0419003001e549444230804040171078542080b21511450041500c1c801002040541d000303000500003036600c0552a0301c441c800000300c038242502ea44506280078401d4aa2451607550351805201800040c060300ba0b0000c1014011031038103142030600c5e030001d45840801400c0011290206d41c00f0b5660f8241c82c4054030004045034880100d070742d500c8440705142c00c0201d8411400b42c0741d0029985000c03c61a104036003004c03504a03080084030066541c01100c82c1014100420b010022504801801d201c000e00b1015840016045080d441c0c01041d42151350006481794450100b04808070f001e83d01802a224024681c1202c103100310314000148090030713040100705000c00701e8000e070710401a032080e14460905608118854a07403a80c06d079010908512081e40004e0b00c0d510801143c240f817001a100d68080780207da1 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 807895062 1250 807893812 807893831
    0xb1b01020702060f0a0e01170c0c0a140106050901090605060d020706091a090c0402120c090607050307030201150b030411010e0a120f02030d020303090604060b060705010f4a01 77
    0x440650000151a4504c540850340c075032001e03403155801131005400e00b814011003070f6440c030283c090000180f00700c072903401c00142a644408203000b00214158042d14104a9401651015018000a0103460300800000d800091041c0c01170081d107040707070170103003065207800c6004061401960080c41c05494039a15503101500113501d80d03203184007803190590007840c4e6061a016072801c0550f1040300921450042c0300003802e00000f80780040d00181410303442a036820403d07000c80d82602030720f0005001400003003400701c145038041d007096035550501403c82c41d40984540c5170305503502095801a101d07904004420070b655025520407140c02a0091400c0240c69076006a511661019101110312110030000d00d0f046090802400001c2c44440c0099401d524201040da41d40380401040903103615115180043c0645503002100c644a80001c02488154040d40003100a03082c0050442d11507110b00e020360035222100554030b6503402032400720341c0100032115058401c0001c1d15003601041d540e03814414 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 807896312 1250 807895062 807895069
    0x6050f03100e091c020a0c05090405070e0703020d0510120609060216151104081c031104230603100303030b04020f040e0f10030b01060305090c12011d070b1b01020702 73
    0x10b900c07418054000f4102844003c40010510752180602d0f0103561105d24401c000a07030014400064a20540f0403082c60741c3c840c280180381800c550b0115940b048030310184100c3c154190002c0c104451a00014401602c440061030728076220b40c810381d00320448804025001031100d80000c0d8490740164800b50400203104200900e81003652400c443c13141c220702095100c90b15600429010f070043c5030f0711500700b5141c020140e40781c0024442681090802030710700020103029500141c15564181110741e1110348909280006001c25040504000c3e140e070b001540910700340341140d1060501c2c0c0c1e80450143d07d0743d41e00380c0180100c1d04900d0751140c1c0a20440d903081440c1c2020b400102000c814040050400014220080038094918501c44102020a00c041040d81082c2411240ea6140000d281c3d61a690070307c3c1840340000603aa44017810035038041000105402502840d80c0d2000120300300d00031111401d50f80d407258072448052540603c07400d03240303001e00941b00005800c81070016244c1000365000 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 807897562 1250 807896312 807896339
    0x3090b13090f020403061107050d231912111c1e05040b0a050601080613140709080d0207050306070c1401050a1e09021e01030b03100c1806050f0310 65
    0xb11195a640410100140541400341c1300801e4031305042c0a2800000d504d542d034840c04645112424003001d2800c100030344c00700c11198500000d45420715602c4444a840c0000403c0007001c000700095085040d0201c140301501c0740d01e81003a41000c9a130326150360094402c10031001021440309140d500e881070081047c1512506001c4091010000350502d0a0b103050b6070142806044002151f240030200305c0580d0700028859000300c1c08446912951706450092005031086242e805903001c1443c080c030182c150410000c8095070485030a8500580d80100101d90f1340b4118401d02e545503000314003040300c103030183c80030440c460300440230141000028240c907401e46e2800c0d1103255056a840c034107944281140388460044000042c010300080303509070002080000c8140032075015106484101000e80e0107075211388841301018059a440c4080d6a018500610701c070b10004000c00c9020885204050b50b07081d1100586080d5191313203091540340f00201c00250030052038410016000c240105145000001 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 807898812 1250 807897562 807897581
    0xb03011e0e0a0b1501140c07090203101d040b0a02132112020f07090509100b061e12061f0815040509010e0124180f05040b18060403090b1309 62
    0x8081c8480e010810006046c4499100d09030008a01440804800071022883c1012629200000750305c940380c5089803a1030301c0e0341c0e0b40541c0e07241002e404001941c820070407038280b02e180104036480103562078014000070303031240e03402720400400c06940500104111600c5544800054245005186441d90b112500300391074071810009640042c0703030691020001c00c8010b001d00500354080c0030504010141c96518008031280700052030711219050110b4541c00180e0b1030b80f41c088501000c00c0c06106d021160154041c1c9034209941c040800010f0203800e0019107056480c15501e00201c9495900300d00f00c5404d40041e00e01280d1205401100030581d546001e000d009070410000003558000c45c41006007190204250074074140d6002044414081c02d50145030102c400040303505440468031003006004028450310510318900e0030082c0014001c1418110344035202079104a416540c62203002c07a607070607040310010001086048280000354430000075000f2241c4945404240503143c45007401902c90081 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 807900062 1250 807898812 807898831
    0x70501050709030b0604060b181504151202070c030210020c180108010c110d030e0c041404021e03100c030b09040b0718150e0303040f09020702040b03011e0e0a0b 71
    0x3414400d110303802c130b041500701c84c003220104101c519140b800310a5000d41c040107010404005180c0180740c46407050840f90407050600b01e66110f40b01d003c0010100c00c206040e0000030203070954480c6046041c802c8818a40e00440f03c1028280f030341d42044404000820440c0850160313142036a043d840d02e10320046294150703140426290b05100d0700908461496150b081000f0600315825aa100d0204200840440300c0c41d01044001c003d21001c0d00d40701244c548103401500d407050301200740c1c244545140c013545c421030f0715190742142303030140096028036140304540c1074020b00b60041030071350254404400c0000f0703810b012500040400c0025000241114240c80c480d0500c010081c22941c424202c10f804003c18140440d05401c00c5010103041e01102012814030201080450075507a080080da0010542c84070f417001495102d9040380040d400c040350803070055092150b285460300d018080d0242807460001000e00d0714071600e2010003e0030041c48034000074083c1c0104503011485014140b0300c80e20300c08 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 807901312 1250 807900062 807900077
    0x1020d1a010201020909270f0a0201020706050708090108100e0403080f09010e03070f0c050d150605060307050d321816180b1f0f0e1809030705010507 66
    0x5495408004205008281164410452031004ea61000c02540d007001d4a0038001e800049000c5492100c400803a0312607e4a120b5640c000c0c0e690407000501d4218640300380e00342c0701d140c1e03510601507a180c010b4440003441500d003405284169440340c03640c0b40c0d0054200200c030300b450b139590701204034041d02070781e041d0300084408040004112400c4040c0d41c003e142c0800030000000b0311108242c4a00492400a0207108040540d401703001c55032050380e001d000c006140e141141030341d161009450582e50024030149050000014040c0ba24806030b900c0b8000b541c407110310302071035041c3d0036008100d01c45034000c400d1031010004404801490075542a100011080c1c481410a040c0c6006203030385d246000041c81c0e0101003d04516042090300301c0444500301d03204d098a96006c10b811002c0e004000c0c80d05d03004070640102d40c0d0148943d0600d8031011b00350740c58100308044126400c035043d00080d122160004c44440c1084c5072001d88840b650303444030715074056a00b4480582c5d0350b5401d607030703099529500103101b5 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 807902562 1250 807901312 807901331
    0x70804080d1403070909020c07051f0206070801060c060906111314120325120807110a080f071104090c051e030c09060d020d052d060c130801020d 64
    0x1165001004840800d2a00e040d81340020300209501d526003e0303031880e075801107045890824104080400783c500100509003181139003004420810b01503803a84c00610860001c42c00c0c0e14001c3c2d07001d5050360f080341d891090100350781e222500609070b111001c6403400d507a881205075088102e006096403c06a001c240c6002e0f00e0242c41f00d0350031a100c01100d01c940c0d01c101100c1684c44002007258681a00e424407481000e02c812800c120307455400c080030384115240d86421a002c1d0b4001c40082c8035040940344c822212801c44406541c40006040040400e041008080c007500800c401802d40303c2e1054142c0b80e03115130510041b600f45c80d0002c0301250414880d9800340b29a14119041d00900300c0c240e80c80c1c0080440c800300195a5074901d1600c580546030034030110350251940d048424174a42c01030880c540c69501450701d19501c918030f2100c00d60303a01d80259003190a040518800d00c070507071100020b01650301e51071003c0340f4030340c00071902d010510050440001c1202d802e0001e0300e40025403d500044041c1d5 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 807903812 1250 807902562 807902567
    0x60a0501050c0c0d020a03080304050a02040c0e15031f0f050f0613030b060609100906020c0f03030403060b210f070501050c06070e0102010e010e010e1603210302070804080d 76
    0x40580299050010900c610419000d00084002001c40c048a280000d51028000f103507035081280c1003c0c0c8100c60002c10441031020000d040c1880c54401d0b5400c20064514050881c1c41d032404a0030564480c2d00c11078403190052038030020710707007100007100d030701d070600900074501558000307a503000211b04012540100024a0907403d07003110000141d8009207401c20b2450601c4003160507000003403240180801284107600d030481a900351410192041000003000c400160001e40325100f80c1c00107100b40c00b80e181c410b0911031020b10741e0410107001941000cac06c2d555103070080d01d50190007d80102c800a200c89940e800c070903030000304200d4180a8541c0380038903500e00381008001d401060601604110100c2a410002901e551000040c6480d055110302c03035004174050f0a0b4504800703502e42c2410b60700305c0c4c80324040d0700152082c12100c044032000000a89003002c20b51061001170240041c15240306181c01407107650840d212410b1800601c0d0807403542d5401c0c0c3d1038125410641c0b00c0d5002514a1803000e4 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 807905062 1250 807903812 807903829
    0x606102f060c0f040b07051002030711060a0606050702090417030711010e07140d0521090103060e0601080f070504050d06050a0b010309020312090f0a08010c1e083601020306 76
    0x42c4010780b45403600b0340000c40103286100c0c91080808100c4006039480070321605200e491480d0030f07285415540c4c0d04000c4801004c0205200f00740103540654000706044481500c50781044171070903250107041c14000d03000c020211500034030980d080c03200c0c101d42400845442c80214800d001e903071503480390f0270720001d4030031b086030103140030408141e0085d1810310180c82c007903204450344a022916088080114508107082001c11280d8442c0b0104088180303860882000141c08912803c2e1307020802941e82da80135100240c030075290180491221000325000692244800b80e0005c4103080c928079195941d4041b864000c0c01d440d080c2c1c1d800f0364500500c500e86015000c0c40140078005d107000e0183c0007091700003a4882c034940250749164400000e81c80131507203852151458152008140c910541c0d42c0b5480c55000e082d9003000b0f80c00045080a10f01c4140400c003150f0844100540d903105020b58824040388070445258045203244400c5d18441d25200199103052135140020307100140e00d0341494000d000c0a81e = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 807906312 1250 807905062 807905071
    0xa09020f061b1c0c0803070e030703110f04050c0f0708070f03020a0303140610110709060b03070207170a08031902180a0f0b030c0304080f04030b06090105040e0606102f06 75
    0x100030390200480581c1e0304c2424041c8007030b0054200b0f0303a00e445d406010f803560b96900c0e0304a501401220400000e205c140c642c4803d0340780080d24034a0700e21400c0c40070801200c104039492580080300340726201c48a0030341c030301405403144140d0f82c2e03500e00710307060b290810340c00d01d50340040f40140d102c071415400f01503044c01040c9074500390880c0301c032050a1000001d45003c2040c24040100051502620104401084058020302182008012031900e500074400c41343d0044030035202511420780700040c410740c8275211f6003050981d40050318000d1811340e684a01c0d03900140c101903100c070200425900d00310481c40100324248925682c00d250380d4440c41400700d8a12a64820021010b28040400000c0d0222046940c040c4504a802e40d07a5951032030102c14502510b0a820302409010601004100d40c0f403002500401c802c54440d42d00c1ea0f61903003003105a07481103400501d1354201c2000701304503040c550b048100c9101c2d20304203408881024281c544200c0040500311b41c480044c0d00703041924490521205401 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 807907562 1250 807906312 807906343
    0x20126011e03030e0f1f08011a070807080309031c02071101080601090e04020a031a011a0a0906031508010c0e040b100c0314040b12091b01080a09020f061b 68
    0x81e40c0c42c5441c0035011107004007103580150702002c080612540c0c0c41c88000c40400c000c0c240502e81075800d2000402c3c5040034083c1d030046600320001040071095030b106a0711425480300c1030710718108140d500ca8045800c003410301d550700c2c44140520728404003190312906c80e1000c1e1810040e01c0d007016041603004d51034081707140ba0501950006102e0380d6680f0842400c280c404143d0143d4481d21188003160324403480350b001030405c48200140075502c15401062070b0483d00076030111440c085c0d178241034078030621413501840d0100d007041000b00802402500308084a142e02d00b142d039495541c9019860949a400c80f03214001409489a25580c0c5024401c2200c003071001d4034417021078080c6500245c4601481d04d03024091000340c2c140c40c045030341c4ca401200d010b404011940c0792540d118031503c1d60700762030030740300e02103180604202e034103440384d8024000c0742441c0c0581d5103d80d141c44140d03c1800a200d80380302640c00401d42c13102005240c032848000c00f2400c52090101d1030003040042c03001c0c2030000c64106030701c0 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 807908812 1250 807907562 807907619
    0x70f0203160608130c050d121403070503220c08160b0c060103081b0f0601061419030203090a0203070f1d070f0305100504090b0a23011202012601 64
    0x18403580140c5484c0c0c0300b0354840342e51500800398142480588040d510465200e1041d0000004021a1900e0108401341c0303a00e40c3d03d200d09042d4070b01035040c00101c44600c0016010320004100300314514512031800070300c0e40c044210f9542a25400281501a00403801036031100b805000c1c183d42801e081802800918035240c00c0004100240780c48010620016180c040d0106801c004031341e46440d04010220310390704440b1420041e1000c00d0302c8803400d20a003000304d03a41528000e0100c0707420b02110300320300b88002e41352036002503035001740c0082d00090510862407040d4005a001614200900705c06070405c8003503204620f10703002ea113050401c410b0080c8842a0509014400140d40081c85961000042c1c2404620381e525545103090b440401d502003580142420341c14014010844003160052072540e905000c03140700c0e07100d04600e001610350320003001c1088000411500b90003029012102d07105150842c49001e01c1c81007000035140750070040d00304400c4100108200c00c240b16000c4043c0c40c44088018 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 807910062 1250 807908812 807908819
    0x501080c0d150c1407050f0c0d020108061504050a080303060f01050a0207030b0601051908040501151a031905010b0a030e0d0801090b030a05060114012c010c05030c0102070f020316 79
    0x100d000303008580d4081c2c00f5200c4000102c034a020344518802141d8044160341c88801d54140340d55074018100c500c111501454080c0230403802d04020544489806855060464841609010f142e5000c00c000e030303020701018000403a65507280c0c4070010013411000011922070074501c0400c1400c124104420f4140402004200380e0150080344001c00c80b038228114058594600c40180c1321803158104020300e00700c91110f04036042d0b4200030582c5c001c0380a84000c010545001c45d505010385400e00500c1d0600e0039056040000341c00190046500500444040329418581c28951003500c100b0b800284801c2c01c00b08c0e0f1b030b10005078140b2417542d090b00120010f04041c08601000b400e210010b00805c2c5043d9241e203410140c3c0c2d1020071104183c2c580c0501240ca01e582e40380121090384c841c441e505400145403a00115440c1d07008050303407800260302030800c01a1010200190340b20808100b088034940014400f0542011080c0f001c6c060701401800c00b4a5000070742d00c1014200b11032415000300710744071200d050 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 807911312 1250 807910062 807910073
    0x18030f2109010c08280c110109030804120f08070309031719050306030a120f030b090910180506090a03122d020702060f13050d171e07060501080c0d 65
    0x510780503040303131100d662140e00c0303441160015803103880110a101d401000101d8140e0160144007040d010f4402d801d00510301d0401181da0600c14400640754140a02080c032101120889129080e48034020854460340c080d582c408680d00668130503408640940401c1003480034004c12280d440f07801d9010503207010005400f4480e0007003d140100d0030098080000f40f1151400c01081c0311640e04089081c6070200c00000051038031150f10f07a0200082d0500c80c51f1810b509020380c4450090b410f00000e410001c0f40c1c2e4001100400f59000e42400b40714404080f00003181080c030a02d80101502c0c00980008a6a4100030704141c0c00310769280301d010b260150131600800040c0503005140d5142c5540c60fa01c040500c01c0358064010608041d51040000a5000c40142810024030407944001d40c1500c1031591034040010101c0e00c400c3c00792030f16804100d00b01d010440000100341440340b0141440e03540040e42c101150741d4001d500200d4890780d8510060000c02402c01c00464000d0085880c40f9108040d5541c0c1c = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 807912562 1250 807911312 807911327
    0xc020f0607020706030b0f0d0b011514031308041d070305250c061e05150a032607060e011a190506130824070306140618030f210901 58
    0x1300410107503030318881a203d540e00d01d01d00071803240c020134219000d100c070b0410441e241c4081c41042034044064982404050240ea0038031201c0c03000c60809801d694540e82800c8a21402c007004660980e810400410070890b041c0c7c05d502d00001c1c85c0e80004103850030b800040c0032a0300190044d041e1b21000c042c1c41c0301000550b0001049200745240c100c00310a158509070002e03001d0480c003c2c15000f240704607034420350341c0c80e8891031084260201120444840380c06015501c40d1070700000e000160441da080803080142d03c032108206020045552404080b911620101d950040c14110565198080095640007440d00f000020800320781491180800c400c032100750a0603445494095000440c0d1103140030103060305a070003085420300361a04141c07c801c1160301c600b1852402c000320301c516004186410b11a1241605a400f2001601402e076402402c000182c0c010300d00b4580308041881908842d61020302c07045948036085d10042100d000548074901e0207403c000c0e241c1d030102d00d0510038601240e912104 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 807913669 1107 807912562 807912569
    0x9041104171c0921050607030605190b091309020a0b0a2006180307020a090509010c031122150203071e2d150c020f06070207 55
    0x15141d07000b42182a155800500400400d10814031002c1000b8200000c54052558003c0d2a60b0788500e894000c03900000040e4540908015030708103440404280043c0f21911015a400c01c00c1000150283d000010b215002075a00d07020350f883c450f400b40140d203070040c00100007da2030350100c802c994422080a03001513104400e10800c102031800000090f10700310060320640e1180024402180c401c100030b0101400208000300059039030309030a400401d0410f5002c01e217031501d407035040e00719018041c3c40400c0c1420f00d880240d807040b00c1c4049802034082d130140550181d4659010b040003030081d4015200355a2405030103a8215000405001403c1c461411411b11009c0402800c0c10754100309001004280781da0b420a490151600720000c2007858942d00004500540d2220403440c000c2c0035201c01c089030f840d40b0341ca1500b6418400e1102c2c9a03da0303001050142000000251f03620341501c03 = true := by decide +kernel

theorem cover : BRFrame.Cov 807733812 807913669 := by
  have h0 := BRFrame.cov_init 807733812
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807733812 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807733812 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807733812 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807733812 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807733812 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807733812 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807733812 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807733812 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807733812 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807733812 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807733812 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807733812 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807733812 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807733812 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807733812 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807733812 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807733812 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807733812 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807733812 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807733812 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807733812 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807733812 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807733812 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807733812 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807733812 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807733812 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807733812 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807733812 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807733812 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807733812 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807733812 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807733812 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807733812 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807733812 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807733812 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807733812 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807733812 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807733812 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807733812 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807733812 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807733812 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807733812 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807733812 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807733812 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807733812 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807733812 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807733812 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807733812 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807733812 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807733812 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807733812 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807733812 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807733812 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807733812 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807733812 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807733812 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807733812 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807733812 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807733812 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807733812 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807733812 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807733812 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807733812 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807733812 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807733812 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807733812 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807733812 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807733812 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807733812 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807733812 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807733812 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807733812 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807733812 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807733812 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807733812 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807733812 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807733812 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807733812 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807733812 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807733812 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807733812 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807733812 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807733812 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807733812 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807733812 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807733812 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807733812 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807733812 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807733812 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807733812 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807733812 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807733812 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807733812 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807733812 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807733812 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807733812 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807733812 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807733812 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807733812 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807733812 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807733812 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807733812 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807733812 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807733812 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807733812 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807733812 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807733812 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807733812 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807733812 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807733812 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807733812 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807733812 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807733812 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807733812 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807733812 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807733812 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807733812 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807733812 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807733812 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807733812 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807733812 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807733812 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807733812 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807733812 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807733812 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807733812 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807733812 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807733812 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807733812 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807733812 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807733812 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807733812 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807733812 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807733812 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807733812 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807733812 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807733812 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807733812 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807733812 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807733812 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807733812 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807733812 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807733812 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807733812 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 807733812 ≤ n) (h2 : n < 807913669) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
