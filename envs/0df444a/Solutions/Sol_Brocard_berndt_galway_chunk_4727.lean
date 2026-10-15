-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4727
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T13:32:26.649646+00:00
-- url     : https://prove2.me/submissions/49db3ce4-a23b-4ac1-bff2-498483380aaa

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 850000000 ≤ n < 850179856 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 850001250 1250 850000000 850000013
    0x11180a020d0f092001171f061b110a1d09011d07031502070203010f1e06031703040302030f0c01151202030c011d0402180405010e0402010507030c0303021b0a 69
    0x1003600d03045a450800040f81c0c00a41c0411480f18222a2000702140d00030800d03004842c020003202c0d03c0502c0b5003030312084c030896a011300d0102074800c100b0085200500c0d96202c081c0c07803414404142d901401480030885012071403000c03c0c803c0302e0500070000c16050341c035502e150030404003060604c4e105070a540d00300724020380309206104100e000403071035940d0385d035500c2065070f901d400c2400028030400244070b83c10541071540d01540c100c10f0f8018005d100716003050322400c004203c0d00d2507041d22982a0f10400c4403001301403081c0b80c1940d402105a5034204495098980503a002400072000c510042042d413a080b80769030003609031201a1000441c2102410340d0600191081c2d40142c10004810b8982c080103950000d4500020442804e00303d01d420744829082012482e90038089403ca07000241681031406007004812000404031002c10140e620f401d0043c803c403201b02c1e03000380824000c01c9007602080c003460088203070a10070300c0c002d40751040c0244400440240c0c040c500b001039000c0c041d10703000c0054 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 850002500 1250 850001250 850001261
    0x240f01080609060c091c0303050405100513080315060a1d0a060e0112090501180b1501080402060706180f0b18070b090a05100c0c06091211180a020d 65
    0xc4140051500d4241460060384860f0080c2441060703200001e00141a0307142c030041700075210503840341001400114240030740503000480b4211210701400d01e01705010002071260340d000d068160041d1014962a0351408040c0c1e102400c100585125000c4030178213962800d000b0b0000d8038807680d40f02d803000300800ca0f0340d5194501380c0301d4501c103628251040c003540d6400010626a580240380440502c2c0a00c41540300074034a0701c001916550030819031000480c4c0d4200c0041044bc0318074894500c0e99503c0004041c41c0c420417610900027901e000c08075003d4603125010740b403924007900b070020f484580b84a003800d01e06070110085840780000400b01044c483c038408010b50208035105901c00310ba4481041e40e440340d03494000c18a00040100c0c400c3d4031500e03000c5180015200140c1100060650500090038500304030a048807504d0340d101020980500c62900c203412901c400007010f440d10030704e5071105141403602003a160446558982c204481150300c1d00c00c1c2c00b40098080c01640c2e07501d0350081c2c206550 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 850003750 1250 850002500 850002509
    0x309070807081b0d140f031e070c0e10090c02070e090607020a02120312010b04090e0319080c0d18260405040c02011103070201140f06060d090302240f01 67
    0x80200c2d010200030f1112560b601c458107021240c00c5109007640c034080034a08805040302800e40b191000150541314000014403000c452298800102c2a8002c2481500d102ea500000c0601c0d22071401004200c1a0f48101504000c550ad1208105a240c00c8802d00715038186400304010383c0021020400c201042d44040c3d0020480e5015008a00d40b035440039503902c020080c000c6c0034401c1d20402e40c20310711051095400044a000700c5081c9541d42d91951440c54119001d01d00d030451520103c0d0301141c1001085808035903203007006200001804200359805000185901f030b0300102009004691210f522405029803039000810103d02c842d800c203100c0e41d00303880f44001d841d45203804045843e541c0700815030b0b01300e4000700d9010501591240c41240503200c13400c004d140c0c0460100034003050b15010f41010704041d45240240d901d84d230710750f00a1141e604040c0da83c250001400c2022002d0314005400c20304615000e80100e405005840100414001d0886000c3e20030143c81000e00071002d0000c0700050041 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 850005000 1250 850003750 850003753
    0xf060406060501110a0b060f0402121b0316080a020906041d1f0b0c0a0209040f0b0a1103060f04060b042601052211130203092b11010908030907080708 66
    0x31301c0080e4565190714500c40038011084480c001000746d942c6580400509501510542d151514101c4249503110142c6410f42060403816507191801d6106064a01c03130300044010098041141e2000d441e0080003500f810061340e001c206904050301d414000704001c200340d5400d102030186004003541105005400d2000d010801f000d07002c01c1000141d031210a47d900390303030025074440400304801d00d881c0d1800b030300039000801c4030200302c02d000005a41c0c460f40e500600300c011807556483d21400c01c4a040410920b1940802e10202d051824152054144200b002d880010242d4a40e1350403440c41d00580e01400c0b40c03105000a43c01c4046d01e004680040200c0c10009002d507040142c1c04000d0a880c0039030710b00e0310fa90700010250071710860300c41400b8540c1000e03180101d2040039504d0000a07500449581045106140c403540c00c00107860207006013690988000c007840644160100c541c58a24480402c3c00d41d03c506211021542c0c140096015103000401071400524115100d410945684d212402030f = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 850006250 1250 850005000 850005017
    0x316030506150d060c021c02010209031f0914010e010e062a12040302030d1d1c050f0408070503070501051e0a2c041b1e0504080f060406060501 63
    0x240300021000c0c0c0140c015580030708902c1804000c60304010020901600541c02c089030b0082c0c50b600841c0d2101340080841c608000781041d620300b0307800c0c4e104161016400d6440400d034a40840064881140000c100007000f04580009072208000342d0054032480c0d8059541e02c00c05401403800340719001620341d100c00503004501e00341d140c0d801509240e4018101c11903100c1c140c158603c2940044131002d01c186102d46441e400d1a081c029a01c3c0c011120003170815160801070010610b0800300c2c1c001c8200b00c02c0050010403507550015140d000710401c2d02041c01802d008080d00d030403030304004d0009000d590008101c0c1c1072809042514000c0c5541c03095040c010104074840502c0003802c8010204e82500900360703501c078a08041100d4003003120ba421042e1803a0a1540c0888140900d01e03601d1121003110b0904c40c1d0714001111040700003003c2c9020f00415030301c4a404611404100ca070702e04401c09810130f40d00785991010014244120240d400d8200d40002e010002000400d1050350081c00083c60307c40003 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 850007500 1250 850006250 850006253
    0x41d010c08071d10020c030a08041e0e0a2403080705010c05040602030301151206060c060e07060203220f080f1b060403260c0109021c0305190c0b010311031603 70
    0x15401c40400115000b0700c3c2034030704512020f0082101c01c402000280031160008c55030304108a65400c180208002030419603989250369054a210205403002e0b00a0003089494958404000f89081201103a2030b1005c4d9061380e0310310015480e210021800b86140d2640e4941e5484c106003115000380e05102403110900c400c0c0b001e59400406d4a06566a150320042036164980b010345500880c03024035040f6900303000c004941c0e25406090300e0f40451003504103000c07800c11004440c3d10350b00e0b00d02078032006a0050240708940512107070301e00001000346101110581c2c45001501c440f118075002050107a01c56841c51010301400c10107041d00d81400c144d02c801800d80c3c03500180280c070440c803010340341904000c102c641c0d40c18000f4842501030f0004410b0b6681d41441c4103014040d14210b58144d1040300d4903400d00348203e1950b6251704542c0e034180e8134641b0340343d400c490082c90110809510010021001d2203074000454124642c2c7c00b8500800410310403c05030710416140c0342d4241920301281c40000b00400 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 850008750 1250 850007500 850007537
    0x82103040b160207080102030a0e100b0105161104051513050103020f010507050c1908010b01030203191824110702010c080c01110d15060908030406030902041d010c0807 74
    0x107800052202c85038001100c0d50500300d00c3d003031540d0400c1c035240d403000007480541c2c580f6a1041c41d50380500e105a03a02c0c504502360800c00c598441c3c82c8280440c004001d40043d120548903002001031254243d03440d0b0300c8080c400700741220811195441da007030a48101e10301c0c0e40741426448004100810060103d5030555000c075901c0c86c9240301c070074140700000c43d46204100d41440804d5408801a0070540c00082d60310040c0200304040c8140000395281c8104c40c241940b09000304c034440c1050312500312a04282c40c04030402070100c0481c814480340409418000110301c07040703000303007248400d0803421041c0c2c010610000b101c810740740700c02e580c140030016403006076007005078103000c3e68202410540b203010061096001d807107640003220320040001184c40b200c40c1c990340f00c00340040000c2980c51040780c40d0441690704040ca400348009541c41032104008051190b0001c65100748080c10119903172101443c410341c403041c0040b180e20b0316511544401c103036a1b4130440180c3d2040c0c00e441e00107002102c40c107654 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 850010000 1250 850008750 850008773
    0x7030b0916060e01090e0906191a0609031903120614010e0f03070b0c01020304151e1a060309010c0e01030519090c08030304140609010b09060f040e0708210304 70
    0x7281030104500889843d41c4c000c0585600500d0110360340c40710362410300c4001703486a4048071900c0000030355100c03801c1d00d9892407044880030800c012480c070010a0030410811346400c001880d550511030700700803207414655598400c0c100e900c240c907024038006404541506450541e002541408007942c508456030b03900c490089030701c6400b40d80c03050000b035000010a08200480d0040e032541c000002d115440002c055005520960145072406074445a5002c0f540c1501c44910b40304200a41500c00580e802c0c00310b80c0a58021400702705115141c8001070003082d001c1c0c10403507030000c0d070ba55140420030481c0d81180400580724024a0108120f1500360705521280115618120342c84d9a6800680104084114110041c20080084039120b162910f01400d80400b0f104059040b40a16804500001014011001102e60040404202d0340e01d050074413648034a03152000d030b401174031a814680c0b001d00601400024041d070b90013624080074141044450f88035690327400b0315034070400c00400001c5180080351 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 850011250 1250 850010000 850010009
    0x605041410050d020c0f1c0914030705102d080a05071b050c030f0a1a041a0c09100921110409050312070801030c050316140105070c030507030b0916 65
    0x586170202181010f1420314a80d0030400301c0c0c13180301c00b2a1042c0d5a018603050802c0000d999541d20b0b80d8560b80346283e5007120900c440e806510890b401e0002d4600b00b40c0c518189155031074550941c002410100c0740300d01c45241042503068810034004203881d40300d81e00300e91007100f4040911450522480003080c5c0d14080c4440940020440b6801c0c00304041445280c0d00100010100d0360307244074071120980c50b20745a5000715002e04000380340c203000b44501214a4810f0341c003c0110f9411820304807840902110041680c04850310070081601180d85000751110444c0711a50f0b6411040d0030424407601c0da1207044851040c02600c9035000b0b000928000144000c2c2c007040c1d4000c00d03283e8440c50f00d64618014078803080d243d020340c00100800306500c0f6404074103d81c002ca06002e0420b903600700b40b6032902030606400d00d08445442091013101c50451000c500800189001860029151141c084092060b04122150741280204009010050310003d030004849001350900c811000306815a02c41607124 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 850012500 1250 850011250 850011277
    0x105010f0219030e010512010f051215060105090a150f080c070809042d050f0705030c1204050c040207060b0307060f02030313020a1503050402010807180b07020613060504141005 78
    0x44e0800d0030f034401e5082e914084c00742d43c40c044255846200c6e081030b80c1c42c04d0183c0f030301400c1507c983d10420b03000016920142c070011445410961075040046480780c0c4910a20780d0010703800080055504071421001201491942d121518000d180c80c005190803000f4144090020040c821800865085800c5489e90102154001071599020490035064281c10024a5002200a442e41e024850a400c241d10440d011501c032103291362034030740554589c042501c0042444805000040103103500b5010540c0060003030003142c0300610a4400113003641c0c8400000c450380d685030308040b1020f09040103460301400450400c26800d0f0165000207680b408020b280c00090307504d0100b00c07010b548070700d03070010007510b2109101d544003800e07008050090300059804a001485007000159081c5c81844c001c840c4151141d12000081d10b08070801c0c4d03458000c00002c1c1e030b10000400c480703100304030010f07003d4005040589801c1d407141d25105010400c03100402c00a8094503140090032903c0e91b102c0f00300c070282c203c80030 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 850013750 1250 850012500 850012517
    0x15060504090e1606180f060507020f0d05030c0a060b0603090a030f09090c031e110a0c02040e07120308010909080f07080d1a040b240c03160b0105010f021903 69
    0x585030b51030010752070286000c00200007800301e00543d020403070342680841c0d0109285960741e90304070701405500d41d1150f540000c009104100061800c825a162a0340005015000139074007600c03014115403040c1e010000e01e0340000b0590307040103400d000d0480070b400c0c1141c1032400c0d8901048200e844140f1000028204905130b0709814010b4000c0303094501900351140d042007418001c900240040c4001024000301c13640005a142060005000342d180c5540c04c001d0701410440040c1081c0e881d030300b146400f02d034425116202c04c0f2010741e081007024000d1501d03200c5480741020702d0402400d440410380002011604010036613011070a543c0032203c514440d5420f00e3303511115801d184099008600900c000d075410b0000c50624100c01f181020480d4800721020021a00650200015070f50024548804a4500c038403a08030342801c170025110300307002c110a0303d1409c400381200030503139001c0d82c00032560100564018441b950380031141c0b03114204140002e1a2020a802107010b80c18400c100080030041d070350 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 850015000 1250 850013750 850013771
    0xe151306050912040f06090b0a0f030e07120b040210080f010608150402120a0e0d1403040309031502030114060327161206140105210109021e03011506050409 69
    0x1c224503402d06080c81030941e00d56844045d101840070184c0705d240002000c1440120741d0340c40d9501120076420080c0c551114800d03140304190060044205400c0c02406866800115040600b00100b24240b1405110a0518151041011054101c5009000c120702001000b4815155505203419184e207418403d040e0b6130307003000321070020010340031603034200340041542002a90200355043c000e008a0009008000c4c1d800c1400d5624400140d441d80041d468014440070107010701d0085402c070f40a45011281c0c5622500e82c4581104895202010b0780e500000412070000c280e03544e0003446030101c0304c56180d030800d840742000c4c80c0388400c69615031200303020030f40c0004e1030300304540f0b86039a81c0e00841e2001295140c505800d000d05448003a0781042c00c046030119450900710800c0e05075000140107110400c44a5003135080d114002900100540d030b5041444090f03035038103890550107192a150b12903c1c01003681031509442c5040c1d045600307068000d0050120380e070003a055406031904c0d10800134600510 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 850016250 1250 850015000 850015003
    0x1d010902151c021603110c060a03020d09050312070f0306180c03150807060e0a03240209040504060c17010506040504020f040f03050f0d0206010e13050a150e1513060509 74
    0x400d41d412102c2d200007803110140198019986030540a40c81d00c140ca41c0c90921041e44070b00903420280d0f4032070740c204001e00009000343d015001c44407842200080d21089a40c0d90340c59517101e0601514100701d04020812070940c842c0011302a140f0754542449103900e420342280c4030912801d100c041c21610342001c0030321030380b007070303005900200b0656a6444246d5403880007540b2a0001e000314000150205031075059800c240f40c2010480c1c0e4401c00000382d218181c10900c00010041410080b0720750208000406a50b450260034000c9019100000c0c900d0342112010700b401d10300c058070219010303d00004101680e6803406840c12504d05540161391426014407000c2e1601c160340200034040a109804014054001100603031031503005c00300e81c56a42d00b99402c1ea0754101c244a5088011034403000160144804150410500e00c5102182c200e00650354030116000d0004204550340b03a90b4a550380e14843d403c00238650440058a8400303424144503841d00400212100c0c042c095a40710008075110303038070 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 850017500 1250 850016250 850016287
    0x10903020f0d201e090f10090504050102040609060f0c02040c090803030411100503100312050c030c1c0c030801050913051218010e03030304170d0207061d01090215 72
    0x2444454129805802c1001c070000140400380350740100e1882c203e8043da1010a13036030020301d0740010000f586550b2030740b061200300c000c010100c0715a614081000101505c241c082c65004900c13542c00581c5650509400070500e040715840402000000101848d00b81d8006034200c9041d1b07015140401d5400301e0030001e0398940358550010f00b441c8000030402c002c1c46100c1800d01c0b401d41048445c03080c0101c402c0800c49042c001901d04c0c803041086002d0400000e118465040140c05060900c4e80c10910042a203e0860b003000c07000c85066005a064000c2f00c034040380c0000a441c0040c00d00c0c4070707402455100141251014080c00303000c0c51200340454084070a0b15141d00b10359a024048a0140180074a11782140d0001c0d500c1c50040c24214100750100c2d801008400b48088015005504503500c0b62120380c8130040008000000710810008807002070742c6800102200d501483c40803852541c0c80601d40c4030500006210702c1c190b49403c85040040e81e0380c0c3c01c00c00903500e281030440d4589a500350305030081031 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 850018750 1250 850017500 850017503
    0xf01050306101d031915050609070f0e0a1409070908030f0c07050d032303012106140903070209091c050d0f0f05160201330302030a06020423010903020f0d 68
    0x403c1185200301a585c1020308518103114004810034400d5500e404001e90384d06507885503002151800041206214007440006848686000718541036a007003c284044200c1d0411004501c0a03400c0d144141000c200064203c4280d18200c44500d15202c0055224004d445110b50074000010711a001c03990200f0082000c2d01e0020441e294504040c5030180910304040c40071034a240c2e50311900ca0102c40c121066a04031500754503011250513034800103500c1c0f00c88282c4211544c969907840e0386c0f40d880d074680320302d44a40d114000943c0e0720340d001d004108250900403d418095404a030541000100b96409850740c0b100d81c3c203000e9202c00019000310050b160209551030847e01d08407105544551a41103107008516044480807c0e10040808a090751400c034101c51074146004100003e0b400d1803640e02c00c060305c5e0121145c010b15203a600107400c0039001241541c06a40126051000120803112141d00900000325021742183d02d40010b0540002131001a2284594100250301900c0c0c413290b40e805075 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 850020000 1250 850018750 850018753
    0x10e0f0f060f09100504060f03050403110105010b0315030109171605121903090f030521010e0709060207030506010302010815030f07031e081902010207050a03030204050f01050306101d03 82
    0xa52007107100140ba50801c5001c603218501d11355080c9100c900035001c550944110fa600c005070300c034050702d040e0050500a1f004404001391307032031641c070845c200303215140c06440503207000c40d0780342040040c42120f403c014404902c0b0364075004080c8001180c541e25007500c1090f514405403152240116412020b2400c4001b600d940502b880300000d50040030010100c02081c84140604890300c0b04c42181200d86c405001407814501040752004203001d80003a10340c20110781190100b140502408105d40c501c2030b40a166071040840030300080540004800d070146c00c280c402030608900d50340b10725030f03214810310010307050040c4200402c40f1511044c121034080c100103030884074140c6000f03410907a54010b41c0b0050312098419120040c14000e03003000da41d50990805052410900e4010070380c950700200003100c00070740d036003007091000164082c0803a10110307009480041c0c0fa180785c0720600851a1030141e02904001c000c00802505035620340ca017140c00e1040d0703c0c04807100104550f22500441107840d02680c10b = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 850021250 1250 850020000 850020007
    0x90335220f1209031e051216020a09020f030c090415170d0305100b0d060503070b180402070209240a090e0114090a020d05010b090109020c010e0606010e0f0f06 70
    0x140071440201d01c00d00c5200d072541c1c81e903544000c041100c1c501c0c1c850100404d81c0d41600e540054044808141002a501034825510030090306245400d43d58821320268a1a260402945040d031900c51520302c000c0400c1c0205619102641d0100201c074800101041c0c003110012a00e00d6040d200d503409074070070381d180c1d00400b0300050720382070081c10300c1c044100a000d140c858160310328102031190060a008a1690141c412810304101030541d503600042010304400c2d40d1414005a2654100b0040e40107000300d01e11166a0100c8001414a0701090004140103900401840300141c50f5080520307032114200d614407203841e80781942c03114000220f01ea102c6d80020030070310214001126034011203c4c000d020000b004100b8041d1380c81607942c0812900f44089810840340070f07002d420720315401120f0500c5100005040d192410000d41450400c0c1c20003011194040740708091714000344284160803906100a100740e00d080b1340024022848a40145c0c040c0e60f03541503001d055290041e5080c095440204a15207 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 850022500 1250 850021250 850021253
    0x705121804150312020c0102120f07080301140a15050f091c03030f06050a050f1909090309230f120c030609010203090712031707090504020c0109033522 67
    0x140b0540b2400192241100c034450141403d00000b1040b05030401a00500a1480041d400c502560420703501400214400c1145000003100e200c0254042e040d40d03840c0b00c0c0104a01e0042c00300601d00c0da0402000400241da017100f0a0b600030301230b541d20b032500d05880d0f036031580c200000c41d81480d0b03090903040550a440000d00c0425070580c100160501081c1c4041092542e1082000518412171003201e4115403075910260f41e0342440e0076040c3d1402240d00d0b04118660356404000201c81c001d1702d0a0f00000c550340c50034007010070b844a840301c5903415103200c0074941d03416000260b00c0c03075801881e07240308600245498142c0a014000341c84484401019101c044c5402c45110303020f0740c0210f038103801a0040e00c00106020700c035085800d80154143c0e0705c8524202e0720001140c00040064031940078400e0401001883e503440d400203020361155040046050040d602e070290852961070010041d020504420461805050346102d540c41c0d0b6402812410303482d10706100c800c2c810132003459641d00000020010 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 850023750 1250 850022500 850022531
    0x1203091e080f0d030e011401051e090f090714010519030f0c09031505090a0f06141608060103020315010e28061b0f0201030515130b12030705121804 65
    0x10000c402a07101409a1041307040001c6c22903000c1d5058040849a6100502150510b0501c84500b40d0b00c1e894036012010140c0001081c4400840c0c000c131204003000200444e00342c09021503c010444003054151042d2a01c0018025008000e0b8540c1508001d0807800c0344c1911030f8100001240070928200252030030100d005055010901003964513201821194084856038840e0718401c040990103802112002d5560f090b01144494041d2105038807181c0400c40e520340510918000d10307809540003030340c05202c04081c2110384010b0000341407500c18030030050f640507040800c1c10400001d2800358081c54480c400034500c035182403103c62024010f40c200c1c41c1c0b1265130304211307000e481da6526130b10031441c0c641c005c2604042005500902d040300040f10500154082c2c1c1125400594210001282d45600404175805448280d0030b21031142d1203901010031410800d20754090041038034040c502d0450f043d02d440f5520580c0d035040b0304442c240001d50307248020640c0600964010300034024464014069440d8 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 850025000 1250 850023750 850023763
    0x9042004050f0d0804120f060f1b0e0f010521041202060a02090a0e061804030801140a03080a140c0118120516080f09130507091203091e080f 62
    0x214010014240034802c1440c005400e0307001154842021890581068405050302c0104041180c1c2e4500080b20000000d21038003c2c000c00c0301d0120350004215220303916510308074032104101c08c00d0096501c0e14410549400c100e15100c24003c0c207015580304060304c1c07003245503001c0b004c24080c10408841070104100d41854501c00058250f801c031026902c0d800c05840c00c170306c10b10409a520840c48041040f69080c40e4a00c80d5006200805041203c80800a8507c7c01d1074100c1d000c070009560078005012120b0003000c0075509035800e840300c4940d1802d41d51148030a1055800c0341c401d110030480c4418410500700211003030710b1401c030300074010006407040c0d007180c0c04034282d800c43c0d07411118589030710000e00c200c0a07241c1c0c02100c01f4545104810707503140c00009901c15010604214002c011020f06600c405540488105901740000707480d141262000f400c010b00c0c0e030009000d5000b5080a90003195104004506560111818412400c40b9400a074407070b009580c0145118080c00b0100607a040000c04c0c1c4 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 850026250 1250 850025000 850025009
    0xe1005040509060c03010621180c08011107060e0a05031902150403020c040f2706060b0304050d1409041b0306052407060b041d0115050109030809042004 67
    0x740225111104195203034041198402d5a9000c00d00040080600c41e01508a07892001c03004814000040300005050b140303201c1c6019130381282c2c22401020002240c0d890401080d49200801080c14070176200343d010f109130350300600b10030b480e100030294816060020042c584d03070200c00c1300d5a0780f0080f440c00b42803800a110700c0e405409046803001c0c21141c0c10500c540b10315071540c0036200304940d5500b00320041c82600b61400c0183e944d4156a801c601b0344a4440800d10040152945220300d2890f02c0c4040d00c4a0f42c000840c903150a20500c40080c20010340c100c1c01f001c442c10183c519800c884030510541c0074051000780d1180c242000782041d080710343c4640314503188039a01480220f890f078040c480c0d1040c44c2e820001c540e003910030401008120700350143c0100340c4183d0700480c0c0946140c0020741903914060403a0300c1d010b0750090b040304080c03091081c242d00490040d8040318403481c04001a1000b07401c0c1c03201903c0c6e0b41d400105020260307a5580305904071030f0000044d20401d82d40503d0080c1c0c0d03070040d000f03 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 850027500 1250 850026250 850026259
    0x9150e190f060b03070819050108150a02130e1b03040f03020d0c080322020a0f15110a03080702030c06100510110606010509030f1c090905071e090e1005 67
    0x2108101598540105816501520781403880c4d5100e2103021210110010f1055103c021110030400040d140c42c000c190080c051f010003070846100800c503455401801030494100e5520411124062010805001c0e00322481420a1010390340c0d400002607150402100901504000208004c200802c1c521007141c2c5600907400c0700d44d907441c0c161040d100c44000341030103071030340400740300107000480c801520842c16028446004030301c668a6002c103005002c0ca8010510000300001c0c140a42107144000003811201d070b2608420f1442c2002c51180c54040d46d5030043c0070480404006000e0038020070880e064441c1c0c0c03408a810301c2c0382490750154881c0707040c040c040c400c030808040341c0221032140150066a600312009041d568480d21f0040d122039011818842c0c26024018100c3c00c200014400e4600040341007400844003000b4010041510311250880751030b0390300d04001c1c40b42c0503a00020000d099850250100c2e403000d84040e0a40717941034903510580526030104c0c1005142030610001c84201c58080c0c4 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 850028750 1250 850027500 850027511
    0x4090b040203060f1c08070f11030303010f0b0a20070e1506310806190912120f06081507030c0f0503040606030b1305070b040f09150e19 60
    0x8000c10380c8000d6420076031183c55240c0604580c504082200c1c40d1000c4c4942100e1500c010303030380d03034200c5070040d07101035a031507850a028a0510507001c0e101c80039064100d020f103203035604007040d01c10781c080e035030003210101c039400310f20180b4040c014120355000114201d651b407c04070510f061035a803002c2c3d038098040720702c80400104004805050903841c0e45c0c00000d08490421200c010b44203c4000380c85280607240011424000c0c035000741ea01034401801c0860302800c410318003c5109840c194055001d01d039003c1c50014040d003c9180c0b410f4a040d0400d1918044440056201e5135001400092903200035803071034000c0008a1a5002600041c80d410482100e55280d032044c03015000c075144801c0341c40c0031400e0215400901880341c8010f590292049800140490300d13a29155000a81111301c880d2882100a43e40e080c084101700d400c000b4400c0314480d43c40e180c1030440015030b40001e403044007502d58441c02a00e641000060f0700b90081d00c06c40342c0c03081540ca81052050254621005103031811403804 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 850030000 1250 850028750 850028771
    0x5010b062818050f0307090903021b030703020d1b0b0f040603060f0503061614180102150705041503410103030203040510110d0f020d080906130201110d050409 70
    0x20b000342d210010321001d0580c080e80c038000510014440032100c0e254180110480414081c0040c854150241e0003030b0300401c400e00f04200104a400c20851169129a100c20010801691184540c3d0100b990100050b140e111041a6042e06541140c1060003510000b040300011030110708080c00c00c85d030242c1d50502001d540ea042088041d02e160241903015040703030000481c88400880c00715660034481c9000140320401054200d41030708500d00119070814548507403072056074104180500031042c501c01801070b08042c900a8800e211b603105107464640c00040e065030450090f4000d0004068440703040605151111403c6811b40501002ca5099090745410558240100ca0ac041c1640d034035030000d500c0d01d802d04080090b0381820108800030800f50102458008401344030700540130301070341c6420044414418010b410b04005104941c10080c0d0103040013101c0c10000740d0150855028180b00008200500040b030f040e4030b0058081109119000c40c40c82e1680d4010000c3c4212180b8860070841003001 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 850031250 1250 850030000 850030007
    0xf05011e180809031f0b090703020909060907170c2503090905040f020d050709180203120c071a0a0e120604020915280518070c05010b0628 61
    0x6496650111540072a20030000840840c02003040e0743c1c000b03040b1094075001e07070180454440252003c0c2c0c01140c9484d20b940e0039091803030b07405410426906081d400c00c4114004140c030005c00400c43d521078040342d0003045403a0300492005d811890a100900d0345442c0c03004da010b240f588503038034042d015051080c1e1180c01c0c0780280920b43c00294940e8413551503078540603050b00900005001a940d03981d01107500300040e45c1d1800840f4155104401030702c3c48a280c400c100041f20700c0f143c48650081d18940d4528010303940810100c1c81054190f0000340ca60030650f0302a4940441600a804d0103aa1542101d040c845080003070700250b10b441c0e40d040000c180140510078034900d02200043e46503c07002c040380061400d42d8210b540b240c94603281041c40f914040004c0d0240380e030101100c65411030f980700c2c0580c080300d4a081102418058400c1001402003803000907a1240c000d00e200e04100355440741d04c0400ca429088180c3d1100d0081c429a2100495030400a6401541c1c9001c41004582e00328000078501 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 850032500 1250 850031250 850031261
    0x15061a0304120206011d19020d0c02010b150d09050f0307031d01020d0503070e0117070507031101142805041103010f1407110102270a060914040c0c0f05011e 69
    0x558401c07802240020310400140790007d040008002e4034045c9400140c2c2d040d102600c07914a5031003002c02d580302031081c06421518076240e030300e00403418020505a100408001c071100305851010000340c103c2c1b04c1c107003281419085c040d00b081d14000041c885040c164407050b295070100c80700f02c1040140c000d060069a40d802c080e03003d600464010300020f00814007420b40141c4010040c1410305590071030303c408414200c821a03a40010540111741e9100f4035501c071102962007400c0b04020440c10301c030116100b0803081c009000a6000036003140f10002100c0d180094940d8100804052095090501d40710100c00c0040074030702d02035841c207143d1260401d55401650f13581c0494040030306080d29000000c640088081203941001c1d9000c01030005050b0490740c141c1e0318142170801449944030602e00700020098903511050400c01851028002c004600030f8001388500121070010f4580741e00041036a00295a040140c48004004003140900030190402c541c00d1001980c00c8482000c500241012240e = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 850033750 1250 850032500 850032509
    0xb090607120207110f01020307020405091b010c0206091507150606030c020312070f09230102160e1f170f19030e06030405030c03040906060305010e070c15061a030412020601 76
    0x11341d9900d040724074140020185910320381031041c0c81c90940b1039000305042d55001e80c2c02034590391100201d080d0100600c41c04100314102484e0501e80c08402d0b030005443d501501c4e02c202d20a5200145405007415080c0c04c590311694030aa0342203c00c4001d00110004051030b105002c007190511681129091000c81103c0c250700a01400c0b400030f842d02c46085440300980107510781405110080440c3c04406c074035944882c000c41c091001c81401c5000002400c1051714a08906100c5070711406011002c08142d4081c1d10a58100340c0d00142c2e142d892118141c1d0300b0b103a1000b2404034450304001e40f00c0c500424260303c0700300010111034101061103041c82d00c0240c64540680005d003203142c040c0c11850204000c5400c00d00501c03c682c1404900e81c80c0604640c0a9070041424507501c0710308000395600b6009680c01409401c98071509071500000180034010108001030050384d45c01c50000c1c034000c1c0c075840f5402134400207288020104140703500d80465441a101030703580c090110680c0e2011403001030041d0684 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 850035000 1250 850033750 850033763
    0xe01080a030f030e340305030a08040503040e0108010c03050f09150a090b13050114150d03030917041a1e0a0e0616060b010e061c0204030b090607120207 67
    0x499807900d040b0b612480d001c12640c20140c40c0c09844550500c10800c480020000700c0389500e030150000c0400c120301c0c2d41786030b90030740020010340304001103003001c420b0300e030003000c0750030105504d070b4a51925505522464000044015881d000803620441c154400c400e00942c1d510b040000391a0840c14803e2804c0c00c640c10011540b01401150403036002c44840e0f5040154501c000c0740e0380b81c1980e581000a1000c48808a507450b006515000303001090041d400f00c109101031142603810001020001c081984141340d0140d01d000f9400b80400d80b01b40d212801c0240c01c031480311950b041c1400044c005034407030f100b4242c80750101030800881f03215040403260764011000010010b100d204400a800d504450300c080c003401069180b0003500c0c2c0fa400001e00d200282c541e80048000c85c1b0b803901e1303c00c0b0b511241e040750400403080800020750700c03500c003210b000da6407040700401c641052400f000c0284c8219040140040c428034240058032400040316030280c010f9498050140d0749100084089025100014080 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 850036250 1250 850035000 850035013
    0xc06010605030925050d030908030a0c1205122205060a15090b0f010c0213020f030a050115090e0903040f0b071a070801090f0902060c1b0a05010c170408100e070e0108 73
    0xe51070040044200c25200e4205000f070182c9da56803040c15500304144500100d165004020100040003183e042038092a0170034a003008440b0800e600f19000044c004044545414810508102080b4032920304c254418210b0321036241200420000e852003d544000700c200c02c04000c0b456007454040d48910740d001900c1c00c03d5a440c4000115000b40c0c01030b100742e800440d1500652204c80281c00181001d02e04000c281da92410700218581c11610140d1003c43c8a0081405020080740c0c4030070104106d5114401c0c40c1d4103602e42001e9282184560340c000011000c48280029424051402410f0a10300844205200003650302010030752210440349417001074422070040c8002140d560011051802040e0006103032802a400b003500c80d0303c8461012810713484484003540e201c2c95450400c1042c101079030010340091500001802d0500c1e507d4004142c811190880b03c0c4103044103013a1070041860340704407040c0e04100030141005003034203040c50720707036002c1c0340b5000c2590404010001d04a84c0350780300501c40d = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 850037500 1250 850036250 850036259
    0x203040e13060b030601080106050a090507050d0914010c020f010f0b01080721140a0f0e030f09040b0d15050c09010c0b092b021b0d0f080c06010605030925 68
    0x1d026500a100701e44065945002490a07181044800d0103041014000507216080c1020024030003581d905c41081d49007040d041021641d0700c0740940c0c9442e6150000420711036001c1c606003c55030341c2902020181d600c0c000c02960760070ba0006542c84000c039480300802040b00f086040340c06464441048074080740c482c00202c2c110503c80c02403c2c42c090310703c01780d008222100d50445429100320689150350300207002c040c04421402e62003000c00e211161001048004d4803003004640301c0c01003a1211040110214094101d0384441d0890b0000040040089101c0350142c0b1f045d0318080307812030768a44040c4c41e12000800b040e9903a0201c038225201610b031501011150760702c0c1c00c0e0700840201000c40c1d500605138160034030b02229145c0125501d10413501040c22100140c02460408402c45001d08041402100b0806455004141c4070f03113504480c2c00315250529082850141c800d0780386404540c800c0d100006540d41d40000910b000340112025120351444e4001441d4403090000c1701d101c14000034120400 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 850038750 1250 850037500 850037521
    0x301090201081b13060503073b210a1a0615031e040503090310050c030c0705280c06051314150c0705010e0a0e012304150608070203040e 60
    0x3d070b078481c00c2d601c5610f00005140880181c602950010300412804014400d015070003486a140888065811082c0300c0c81d03411403e106060001200c001599400700402d802d41c546415660a000c0144051b0540c40580c14101e03940302c1c010702c42510325998074200814010080c900c031031b01800000303200041e2014415810201c943c005000d009040701d000d01d41540b00e5040b104000e10980c012000355445485041c00d060505014045085041c0d140604010307550f024a4190b90f00070b000300400585500c11441c1480c40c0128416510078411000d000c081c1c28048010301000c20903204c0c240500f0030030764404058606004500100c01445c0c0e010a050205403e00780c01c20b840650002c01e404030401c81c4405114580c2c4c010400b04413280c005003c203200715600000c8003420800c00380c5071017100601c0c15908000c1e200c0b040c01180300300001c10b00307040d80000364106000085e0100130b00400504d205111b441601030168860840411400d10006004600200a40301150408226030030a40d80d10031288 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 850040000 1250 850038750 850038781
    0x90f0a05060105250c0f060c11030c030a060b0a0506040503190302012c1504080d05070e1201020901020706082205070f17012909060f060a020304030b06030109020108 73
    0x5504014043c800c40301e9584005000c407280d00c0d420300d0407031400c03041c90414500303464103a000f01b100c070003015208104d42e80d8081c114000554019031800110042000003c4c01c01c2100d1030740070307498801d9001a0701444103030750088902540842e8081602991076061010317034082c5206c0c1c20307810b400c417580c66030b4003101035414901c0c840d03c00e200002c0c1304074611501c000d032054522aa8200c80e015900345d04080c150421000700624012544000d10b843d05a803150450f102d111804000e00f1f40303c5000c201400e008194100d800600104003038001401810b2082c000c3d00f000400034010b125100001640c2406407403001d000e02c6e205803081141c0351046e8081c4064001c01c01c412161445007260001d9a550080c0002020b443c1d24030207038070540c10901c03000c3d0940e091940407441c04480f007a15211072502c0006c542019641c00e94202560741c3d201c2001408a00e05c60003150b4000c880001c00a0f0300d194040000e1056910500040d0155160201403500f2100090002800b280005011807201c0465203800c = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 850041250 1250 850040000 850040011
    0x1d01090e09070503030315030c0d050c060d060f1401030f060b040b070c05060a0807020f030406090611011e020405040c050f070809060f04030c031a09100b030c0901180b090f0a05 78
    0xc80b040b503541c0b070020034610b1340f048401d8490320070b84070381c100d05c185820b0225482140c012510304c8503034402c40e20b82588035815000350342d20540c0c0c00602803488840f540c1000d0000d00d9a008225041940c42c07046814884440700e049000a1820f810320700000c0c154032a100a0307581d00e900035404d10f400c00d61802e0fa9036200810a60f031112401c84000b0300c50f03549400a01d000c5810756100780080c18000c3c8041c1c5800d41c003d00584094000380f00a200340740d4800c4950084580d10306d04440000e100c9010b440c010001405600d4811444004100302840a6001001292000d5804001007103e03031404030344500540007021240402040180041070220002d0300000400070403d515001c0c208240c000580e109600072141200c0001c010002d12501200a1101d400b1a00750070032603107071807184903840b18030a100000042d035032185900850b0702d0802c83c0304001c420107404009607503100d074010940f02e00c41c0f808044606051206204507818207c00f00e902529400c50180e4040d21607258076005000010030 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 850042500 1250 850041250 850041253
    0x2d12033e0106050a1e050a060c0209070c0803090a0b130503040e0604110304060906050708060d061508030a030f0c0c0830010603051605031e0c04081c1d01090e09 71
    0xa003c01c0ca581c03440c04c8032000b070114800d000469190281c003208903e00c9503001e1449080b95040070040d507a00030340d6100d48594115000c0c005079039044015500c4070b042c0d881c06003190b40040704000820100007504045540282111039050b550700705510142d07933004400411a810030b1204008801d00d100e501d03a082400200007084509080a041005810403502a01d92079101d020440070300440e88140c0d9004242403511900500d00b44022503403801c3c0352140188800d9846807215401020803804001420460081c2d903515040400018040c2a05019400d08149441400800d060140070350b001100d500912040c14100d20910389a4401d1800c001540000d0440c2c03406038010034a00c00c9640a00b2590702d0016280c20300c5842d0144c160a40d091520a100007002481070403a107080d44004040c2c0c0311020954581c2c4c0f104800312690080343c2c45200f841c850203900110000031800310110a0015a0300c10010044105502450380ca40308580e5001ca207000c40c007030100070b40c28494141d20078a03c40 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 850043750 1250 850042500 850042511
    0x60709030615051909060b07110f0d060c230403022809090c080d0c170d0f0c021e1f0507021f05060f0d0c2d12033e01 52
    0x40100b0310b402001108615004903070801480005d0051058a010b41103082c83c01d401d103616a962004960f41d5000d0f0f2502c542ca40140180c0c8540d2403414280f00c181d070181060000e066071283c040e0400070956130f0201400d500107060006000c051040d134045a400034907903154010204220304500007a0190603000d007d44203004a550419802403401c918480c81c0802000c614000c00c2c581403d010740c0c4481d040088071040400407038203034100d40c0c4501d003001200a56401c80c82c40101c0040009644030401e03141800403c9501c10340119800c2c11002d040fa0fa0385a4008280400645810b028201c10402d061040308240719404da80e8002c1d80d00072201c1c0100c4010394012000c0040c120102443d01540076250400c200c0141003007110507421a205440030310043e2001d98071801c115005008402500d810b0000d032000c085441c15919080021780c40d842d4881d5604e501e400c0d210490001803d40109600441c844084920702e540441c0b0001c49030b08418100ca02694a801c2c041e080c200b00300c07a55903c52 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 850045000 1250 850043750 850043759
    0x3100b040803040609060203131703071a06012a1e0b16090501020a030815011403010e090606060a0f0c150f02040515030405120715020d090311060709030615 69
    0x60050000c0d10301c0700001d5490328503000c4018001c204581004085420520031548000c2c01c1d40d000e20290703145000411503c1451941d0b492440c0103404014280203858160188408120400b13140070392002e0b40d8105030b00d1544032404200b8103d000b41ca0440610510014010811008201504241074103048100040d41d0b11000e2036180c044c2c982c540311a6034116012441da40200d41030000341402e0020740001802a00c000e0030480e001030400d0607070011555084481d0b0b110302100c0b80706089520095840b96141c1000703002066049500142511032040417982c10320f000c00a480d80790640d903807a5126640c0000085860b50300b00c0400306c50740000701e0a01c03503e1910034000c01c012203010580060310f40d890242000306035240300a160411030030401c14040072500118030990001d1100328007542c0c0b1310070391801000c040000680c0d001998808260b846486038140c0181c2e56890190b40d40344040218080e0150f1510419603075040032990b00f0310100002040303600805580701e5000454401ea5540f0f = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 850046250 1250 850045000 850045019
    0x5070507021807020618070b1c0c020609010b1e060903010e0102040909030e040c050f0705030702030111040e1608070e0d05070b030712110a050714010f05060312070f080310 76
    0x40c81000d40c6460380c120308200340c1c59030400001d1b0303201a5800244025940c00405562514058010001c80c0e2200180e110070311620400700c4440d201040b0030800007000e00e03840003515840c069648056035400c00c84620100e00e400480784190302c5101c004540443c030450308212aa500c11248580c00d03540765204010201000e10181c4001c00320528089100b001c145030041c036076003032440c03035920403494050307000300403035014040e10003942d81c05070482c0e5a1100c6003020761650150f43c50007585982400f60440444444101500c11101f000c09144010744602050140004200f000303240010500c0001420b4288902070740d661032350000d40b040321203507019190b00741009041d40016040f441c0c00030500c001180d2103101e1503003101d8104003c0121454801040005114040780e40e010408041080d1051040042900324560700179030003040001841048003000c0d0804aaa4511902480381e4080f00c81581c10211840154401c4043c00c0000940e1390b00c0348144c0010b0840000c01e040c950300482c80c240d1 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 850047500 1250 850046250 850046269
    0x50915250501020901031103190e120c0d0f020d0c0b0a0e07030606170a050c0d0215030f102c0a020c06040803091b0906100e0a0b07061803120507050702 67
    0x14000242c4e64003580f10001d4241d9441200b400c200c0241001013200c00e00744103c4504000b801c00030003003450450248024502940ca441d075140c035000024883d443c8880c0064003000710401511482c004002e100c005071f86405680d4108004100700b4407003480094509284203900100340030b40050000300c00200b1510b41640740d00200c483c907030b40c3e200c01d0000c04010101f40a900710901c00a1080071115035039552030f00900380341343c1c1c004c65607141202c00315614041481024250030b0303a019124900f0805060210906851804401180d900042176000c0000031700f401c6c45e501d1400224007120300080b107200301c200c0140400c020301d50030b00607800005020320000d4001d500a414040c1c0b2810300820560a0402c0700090500901040f42c19031996150800515444401141c443c100343c0b25412050700c000d4a1a808140d10900200001c21380601c071001401d05640139200801c0340c54542d080070300441e1043c00d00030700460784a4000421a00d02d0760401907001000b032a0180c200b0740541d01140c244134 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 850048750 1250 850047500 850047503
    0x231f0206060a0504090203070315090209070e10140f03040804050d030503040606050a0e0c09010201141e0a021201290a0818060103020f1c0b1806010605091525 70
    0x304444244205072800c6900a0080d01c2c0480d410085004d440c1c0c002960765005100003414280c0e821521141070f10103902800e495a0081c1c60313820790740390001c0020b1040c442d035410075100c0c00384030402c617111038400c466400c0a003603408403403454003914040441641d08020b108a61004007000049196200e0001004003903100752149a00c81c1024545101a107155400c41809030400c004100103000300440701030b80000040c1d80f610381d40e404404c0101d02410000164001c00210345061100c42ca64601d000d107050507081d0003042098448480d00410780c42400c8100001080c5880140503191306212100c845019004070300402c505138048450007500020b9112021a02c3c00080110071044010201121210607028058030760655002400ca00c1594840e54010807508400c20944526178a46040c0c0c240c201c035421203030349420004100121582130444603d07000724800004d600340250241c072008180100342d41508444e0507150100b0760002c103c1001c840802091054035460008412110302e07 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 850050000 1250 850048750 850048753
    0xe0d150f06080d110c040b01050d05040c08010b0303030417091305090307061d121608040806090f0610030303020a0905040c020a05120708030a050a2406021501231f02 73
    0xc82c606503a050500c41c0d000c0e181424031000d40090703c003c113808203a800c4001011600025550117102c0101e525004c0d9904201e00796207000d040c407083c401d00806560443d54500c0c0280500b85070700060603180d0100341e4004200c60740e8804950130300400c920161104400107086220180703004030000d801e41d2800d695200107500000382080500c542402450201003030b0480da60131030003600344074503541c940d404600940e00c02c0c007040709603600d0065900305a413241c104000ca41c0701d90700c40c091103803140020349103500710741b180e01403040782c140c0c0100340148500e8442c3e040140b001c0c9103840c2a0301070b5001684001c200810b035400460607584502c6210984149030b0700900b10400e2614006140030b00c9442c001009003420700a50b4001019107003141d40c88510301070040b0b4a0b49440c1e801501a100240f50071620703030801c86000c40325110400d2190101c41d41d45e030840d0107840800c52801200c080c28081d1000c0d80000d9018001c10744030f81600c1601c1c04d040a1320ba494842400c4c60892060301c0c81d4407100005 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 850051250 1250 850050000 850050011
    0x2071a0f0a02040e070e060904060602071806080307030804030c120e1503060f0103090c0312082a07140f03041806240809031e03071209030e0d150f 65
    0x1414a403105039842030a10394110700d82810401504100040286020100403c0c0141e000c0700d07403503080c2550039400c005842445200d866000180d1103508500070411b1040d10034408091009441c0501d00444080d8405185024808c2d20121140d6000038010740074001da9800e42d6001820f20018141c5a008913035800d0320307100654041003455403042020400040e4240107011969451a4054803050002d0070001807204e42403801524484165001800051141401c8030005400904c154482c450306175218200d00410007131380c0d100c0000080109a050001e0005d840022140d0f1264032012440e01c0403100c40017484040c807440c0d9409500034840250615000c02c0c1c4407521405810051f040400d0900b25803c26174a00058118292011004102c110030104400034410310464054840c002c2000301110b6411407445c030710398000d0b0ba00b0b2000944060380319035041000c2c81903181c0260b06568041102c200042004174451001d00b003a151504000b2a08010300030030300c221546000400ca000c0354 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 850052500 1250 850051250 850051261
    0xf020d08030f150907230301060503060a120302030f0912070320041b030c050f0301260d0c080901020111070b01030615060210410c12040f050102071a 66
    0x3030070b8002d007900c01c40c0781074800c10383d810781e84280c083c0b50711178403525100040da2a18000b070030707000215054007564030350000f0020984980c000011442403400380c94403903c0c00d40d2411600080c0c000c80d100640160014000c002140580c1c00043c421840b00030004145400e007110a242403c40f90340c0101c0b09046000c2410070328007030518003500087c1c4103c508000d06907800103510308980d603c00035917040580c0c070300a602d4018010015106906280080107480b503071503142c00b4041c003491540b4000070030301c2010b010f240c0c1d03000051f04050201c20303503450449560144e43c4094054002107200da05654a841c44450051529800b5014003402420040b41c59499810f0400441cac1000c0103a60040101c0c10041c06001e400113941c22211000000004081d440070180c41072000b001e80e401d0710044000ca003c0c03a030600f5110300c4900e9042c407200c14500642c0b68940e0300221441102390490400710030000080100f0788050544204a02403800903280210a56442036401750f80c02c7c0403a43d45030358405022 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 850053750 1250 850052500 850052521
    0x305090c01080609130c0e1b0a0507110a0810060513110f090a18020a030f02270604030c0b0a09050919090c050301152d030f0f020d0803 60
    0x6400062180152900108540008040c0c2800034000c40c01400e20202180b8085038400c003641445800070a141515501c4002c410100601a1201074495006444074008881e11030101c801c1545641c80b101c1c50a0340c1c580e214080086080045a40414444000621048203110184440c0320030200011024142020450040661404c424106290050b04c02809840b00206ca0240c0544102c1c075844012900000f0884100354215841036207412007404001c0509402920b40740b042074401f8414649170901442c200c1c0118031394800c82c18003c42d61b05c1c01c00003820301505950754015017024605601c0303480b003110105040c1d201703083d0220009210505558411103a00c090300c4221050807843c1446204000e0130704014103880c3c1d0090380e42c1050400c2040c2e0050301c42c000c080241c002d2008054491902d01030940728410b404842d8081c208441350407600c10444405802e01c0440b200503035040d9295120051004041192030404d0400d603071015070380b120034102d0068440e1418036a80d01c0c5c00000d11 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 850055000 1250 850053750 850053761
    0x6030302011103010806190209040218040e0105151207050604080c01022404060506031c0e100c08030c0c210a032405061c060f1409070e0603180f060703 67
    0x52010341410f00c0144035041001c503401d0b400110048524181d0020303c60b4042c005d2041c805c040340d009100240c1d65000150110150b140140129420030010aa5441c000d007a1102110303002803100d98401480b07410f1400004c500c4500d402c40c01201c451a4494011401d1580030b60441d207001e5200da42d01403415a410020000e00107008640c40c40800d83e18201c01d001444080c100502158803072001805c107480800c40090000300001c83c07800e03c40d1101e1405400303484880e004900403518200d00d202e40724040d01c801c020442c0e10918843c655500c01c0e01d410015000650007884a025006424890501981a01040c0064107242550b10660810090100d642c6a01441c0007941e0f00302c074000324421604036000403901d060b00e0303095884035013070307070320280003103280c042c22002c80c58194007040390304425050f0b078181c90200c03204285480d0710100700040703120201c0318400081c420111507801c5040c100301840c0c01c400300c0c80015010640607a03100e0b08113058119a0103040c0c0c042c104003e03505605000b032 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 850056250 1250 850055000 850055021
    0x70806011d1e01050105090f06070309050306011505191b03080f13050c15090a0f050406090e0d0c0305090d03111204060e04050c0c0a0c061d010e01120f0e010603030201 74
    0x86244040c00404003012500d814451613060200104042d05662611102c0301c503071000c0103009c16a1050285800707460180f04d4050b860007441010000f0592020b0f074188a02c911400d615502e01300040400d92880e50780990900008000412443c0c0c01c008980041e1500020b100751640512843e05146011128500030144040740c0b08480301c1c030001c62000301e101c201240c401d84100c04400c4030881d1010b003600c100c032101c0b500301d0002100040d2640020318640c0035180f08440512080d691280342c0400c4d2040f20340701c0451500204c4803404294050034130b016010b8401d00b0460301f407031604000100e019120080c19004902d00ea401d040fa24681840145989605010340c542410705102000709003480401381d075806a595500415090300c1e0385c0c0c00b9105620400800c5a840032954588a800900c0300d103c1c03c004980c440c482103901044001c20306042c0c62040c5c9d90344011000e080f0044499030f20700182121043c0c0e844111808840203405842d0004806038008100c2600e07510f0005e0031030707010502 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 850057500 1250 850056250 850056271
    0xc0d08040201120218120304031b050603011721040e0601090e0106030b0307080106030809092a071e030e0a050d1709010207150903020a050d150509070806011d 70
    0x4200041c2e8203d40140743c00c0505078001602c543e5003100b40340c54401172802582c0e0000300134a03000034034030001005009a81c40b400c00f20b030581d103440391320442c503100602606a020381c003407006011240001d01d103600802d9050080300ea9541c4903103000707031820750600a171030410040000e0030312941d4080700400b50840380a00e08904850715100214a03c8181800303051308142c0c44403200100d80d54100526009000b514008122941c2d4919003040c407544a124180d003d00c13500b1001580c454202c100700301074050350071701c0000c840c10400b030071001690080204803145051040030f201041d19404450074954030a44440036049080c03001c0061007112603200328861131201c114000000c4a40d04000c404030a98000592682c03445001070341002c1140e080b82e000c40800380c580701d0075690b200c2800c2c0300f140e000b030740d5814004e41c4031820b01c4401c0219041c05060111200001011026541d1015a015610405481115888540342400e0241c280e209084104403a00d0821450400a0100340c01419058 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 850058750 1250 850057500 850057517
    0x6010e240d180b0c0a0c050f010e070608040c03030c0c0918060b0f030312040201020307080f0406030f0608060708060604181416020a1410061811040803070f260c0d 72
    0xb5603c49480b0002001300e250140d010500014090042e200c40401307540c440103843c4e18102d01c101443c002d15140d1032450b07480c8901503000480d203028000d000e02558005a480728030b0307070864800381c3e15a07480c502c088580042c8448002510b4006109070300503803800d200c114204580741e060000550710184030041c0f2139501c60220b0341e0390755400422268140400e0100c1c994036511800140d04600034501c02610300380340007c41c00c2200d41110010002e8030000c0e00c08015440d954104c4404035002d134021507100307621400104422a0080d050158003002c0104140d1400c0d4580d041090070701c3c800081e114810307446e02106450024507080302c83e8410170308415203584050104000b03682e0560b4100281c80c1104003008200d54100c28001c4000a80084005000c0306a950401030f80d08000d03120780440300c614015500c00c1890300b45048a0480d050749000703500b0108580c943c4501340045c020115222100210010020500716084005050528070741d65100c040c5000014100b800ca0201e05040110f881c = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 850060000 1250 850058750 850058753
    0xf0210021204051c1e0b0f0f0c0d110c03120c07020616153204150b06040503100b1e03061306020d06140103150e06010e240d18 56
    0x5010b540480740102e07401c0004001c400180e25030f9900d5940f01801003601c118001c2c040540c1c20b035602d1002c0e80710304502c0c502030340e0b0442d405404000c29101000a201c6010200d900c48182201400b25810b645000086040780042e50a036198001400c0383d41c50b41001c200c03425809041441140e0207401c40012a10704000ca9000490600c140745803ca80400092140320500c0f004603440d45000c010408200304951007060843c0d4032a5000466544a512a0103211641c1e01c0303600c1840c0c084c031340c45043e1800541011030040d002e800d8500c801604000d050000140301d9401f0000c10103485114000001e00340c0702c02007030014010414000801400c58401442201c4e2000962190310807851000000ca10800740303000000381c03060185402d0501e051038404603d02a4209a0a25a0b603003600c0400c03c40c14029070040c1302030b079503205174489103c58200045255015414496a521004081250700e140740c1d000f03021200c40e5404600d180900102e40d050000880c2d11034001440b00310701056000c074009 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 850061250 1250 850060000 850060033
    0x304300908070b090108190f0b040b010f0f0f050d060e06040b030703240615030501140a081c0216090e10140703110f0703030b031603020112110d090f021002 69
    0x180b13071046041080c00e400042044d0b43d2030403140c85413100302d0824022400d1711004800030b0001403588510651528841e0b8041c0d60051440c20700d00c42d000d80b508129555480c0c801e0b1041c8510011f5042032141c100504a51044580700c0d1002904141540340300509011080c0b0088402d143c00c818025440b00c0814804528a4803511400801400d01050100c126414038800b80a03240e000d605508402a060a01150160041416203242000c4001200b048208120118089120b0303010250800c204500010034064420302074068140125030100c4d13a50321015030014403692207080e4141c0d444400c10003480b801d01c48a00c5404640b10700740106100000328080b4a103024080105155956081005121b040d03400d44d6400c0070315850041d268141c030b040140241205046c0c040c800c0c000c0402411022010310105001e0325010f0b50b403030000390300c0581c0711f90081002e03900c4446002c3c418890b4030211b00c140e0040d001c2d540d12030780a9031084100c51052040c0010070046070001e40d042413a111480307254 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 850062500 1250 850061250 850061257
    0x8010b011110020a03060f1d06010305190902041103130309050102030a0503010510020c040e0a020f042d02070203010c0e01200616030e06100f0602030705030f0304300908070b 77
    0x120000160388103100f4030141c00070050b961001b20100c240b1840007400910200366090300c0d14604901501b103946220045007241c104452080c84120340c09100e0035038dd2180d501181c64280301030800658010050114880e035001201d200b90f0100980000c002019030002e52540284400c0c0001d500303101342e00c900680680014014180a4580d009031094003510800c0703d0b21810034054001c1142c1912a0303035160300d41d034412009070b0007160702001d80d808505161190360300a42e03886400903145124040940300b907220b9805102d0515809200d85c41c0075075400c3c80381c0c10340003030310f5121104d070100441c00140c0038400c05800315a5194030b00c0c601a6150302c0115400b90706c0005800c042c00d207402e14200c250700910315418908003070710401c4100b200e0121b1002d00e803c10358400080c50341c08a40d031080120f0707691050003c0240603420030b0108a44142d80302010355000b510a080b00612240c030003c0e02d1015031038104410410010b00311201d070002c0d4001c4110405001901c020304050707420510705001510 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 850063750 1250 850062500 850062523
    0x3030f4006030c12110714030a0f0c0c050d0c0812070614070807080a1103150a0b030103110f0d0206070501140a0605010912140a0c030c0e0f1b0f0c0708010b0111 71
    0x141c440e840e82080d201c0540032154101d41c025420010b101605120517541d820462272400420490195545614010400825010b0740300401c6034038142404203218000c880300c032044603024420000455000003e005185484845d000c503141c4030052030406106951001a183c603012040c40140124603a101d1511944014241050490303600c0c0d25850350b00400101c4008807080402000b4081c9180c08145403450701e0700d04139590406252620f10700d0b25203102c00e10005010020520100000d030910300700204035410002d107180c130703806166000704629034824038007152180d540360082503a220701e194800f40c1004404404022250615001030702c2c018003800344032007203101c000b00e1004002100c0174411500301041d0507a2007221079450507080c514518003044845c0301040c4004140b085410251600c02c9000b400700349941d842e0f0350310070540682282d02c4050b082508014010000000324010518000d00c3c4005001c00c4e480c0071306150031103901c1d02269040000510050700b0314080000d1500118 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 850065000 1250 850063750 850063787
    0xb03150f1906090e01051009090c030f06080d031d0d030e01020915030405011b05031512011508120a0e270103030309050f01090203030f4006030c 64
    0x4295540c00248200005051001e1524042002040c01540640c00303a00300c07400310b101501140d80702d03010083e0b0426040c5103900000c03800c490400c0015101e802c202044056070600086822042e299401074440940200007a030b800010700340c22181d454410712903802010a2215030703244003001c0d6135440d60494071850040640741c01100c91701071402e60460358004001061400c00441408104a46030000c0f50140d03825460103040d80e80303019404116003100500c6503255895550f0b443c004142c44110b0016039900228030104103200c0c40e07424410481c80c041e4422242e40e5207498024458901001914909036420f024000c101169400c61507010489004030f1b02e0400e1500c2010403104d1300c0d201401044104190b1380000024950544e12040c0020300400643c0c40040c14501c4e00d86c2070711920030000b5059407040211b03c02e80c4840c0340c082c00554040c940d51111444031020807080e074900f5260f00c2c2011015642d240c0b40c2d4141c840146030b006014504003400340c2a4103003400f0300490001005042030 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 850066250 1250 850065000 850065019
    0x3060d03050d0501170f070e1314100617070b0405040e030715090b0f070906110c031c08280203070507020603100f171e19030f0206010b0315 62
    0xc1500038070540d00030700c481c07440800580d81d40d145240000b40c09441d00c1915801a80c1e41003401203004604c840a44144540a10a0391a0803000010035410070201359180180203145544409060007030400c2000c40c4000410210b0402c0c402c01c0c0c0d21a510a5400c0082c0d00018080000c5015130050b030381203540480d80010b409500280d030300d00703500c00d1480090039820030349c00d02c2d00d4030b509550210182c0c171300070101c811460340c9002414804880c155103c0020400444003000202d10030109103801302281401d807070340e40c0c20300c40100c0d1402d074200c01100900c2005110110046910400b001e6100034850b140301d000001c88100c00f401f000001190340705680d000000201d109008404403a201940640002e0f40d03403500004035070286485000d1008580d0380100002090394000d0090b06a0a45200c00303001003040280c000d0615603198a40060302e4024a04641100b06094214094081c000e032200c0c0c103013030004107000f814400c0507001700903528028000e2080c6c210a809501b03054490507100c1020 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 850067500 1250 850066250 850066253
    0x11803150f02070f0503180a0302130506030f2b02061605070c0b030114101d120f070b030106080c0717070f02090112020a2c040c03060f0b030c120303060d 68
    0xc1d1166100c003408200b28807680000f004030006c000c021180c1c0310420121a11021810440c500305a07102c0a54041a9507515980000043d400325070482c1c0005c044400d100b0310165020308141c00b641c40c2c00c0040b41042c9168011026080340301200d0541440075204910740103002101d150440807101c030812102080b64010040d904c04c0b090060005c0f600001e8407503030340720003681d24501c2c410a071074029075000300781c4000e003806990f2413034400c02d2203890212550341200c14024260340740c9040712410301c104003a0090b8107000b48101000307001801405c039070300d604049003d030070ba02c0081c0048115210401611011a0455564524071040441e4140e0354885ca410594012965100081d51000b242400042c421000441c0d1311390307203482a600d0702d050684e02c550754540c030501801d075101403500d80307141c0310004002014115481445669076030240b9032280c4032241191003940d0003032402c80c0d440c0503000181c5800c0080b0841840b08032900c00249404080040e20380c0005001240201da07420398150 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 850068750 1250 850067500 850067531
    0x6110310030b0a1514040c0c03120e0102070b010e040309080a020105040306091b150201290f0616030201060302040501082415040905010c030510241205040b010501180315 75
    0x200039460090366105985d4441c051441007464201409100718608541e8003126030003410394281c0183c01d41c44c1c01c2782ca00074521208019141c00e00109080d03550070050b0b0310004546031a954081d190420491a240c5001c2c43c02802d07040303040d04161125840344591200507030780081158144c3c0d0f84441d02194800c180d141180180c0100f20800700da1600e460004203009849601096030704002e0342c024841c4004840c4610718009002007205400043c000280c042400c00148400806001400051804400340c0100d9030f00b07040500f04600603519040f007002540703000d019042c05030421801414408004029845041518a01d00e244d0304010000042c030070352840d4804e4003028005801806201140d141c194020070f100d540c494080303894440494042c110400032401039402c4040c62526071001e860282180a41d51015602000114090012250414090f640c05a489000b840300c0ca54107101c0090100c07007206804d201100041c0104001203890b5804658030651582d42c001400c08030701c1e0449 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 850070000 1250 850068750 850068761
    0xc0316020a050414160f0509041121061003050c0a11010e0304030501051e010b072030060903040501030b030a120809060c1819030c0602030706110310030b0a 69
    0x21a801450071882d0b07109045610f9540d482089170100c5010407070401041035885c0c0c01c9065025000550522001415040503807043c4a1000c10580090401801d080000104480c0c41003000e0b0101d9500c0501281d81801d803881401c0302510b00b000d00441c035001c04000028044d801c070000c2080030b20300030071903104400c1d8046112029000262540e560316420503601070302d8261101c0028600b003000f002081e000c480d90481c10f0380c24071840d0038980107468a48562603022030f90403c40703112259021076002e030380c2c40c41811103003450703400a1305250888058030200311400c2954950719411200400082410100c00c5a042e514242070001c2c078a80100b011034909810310000502c0102d205c51341d00b00702a00141d81a01c03e41a800840e0401e646160400406004400440a048a9a40f8114124608076195416120000c00c11040c001c3d0759131a000e0f84001075a00150250308000f412405000e45409140e078440c02d80009039180d410b049020300d031a0841840013404980442020440c060b4441d00030 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 850071250 1250 850070000 850070009
    0xb0f06190b0c100b0f060f04050901060c02040e1b040c050c0109060203040c0f0503071703130308130902070206030703020703170f18013804050f0a0608030c0316020a 73
    0x3184445403203501d94002540300103049009445498076580340c401540c020500a80009080030400d54110300034003485802410381140d501506100101c0d468584c1d0034014002c16403036540030301900ca580140011240c8102280c1c1194110a0941e81c0360104150035141c0110b05450018002d50031400488290140c1c03908800d0550030249004207000792a00990b0003035014802801c3d205541e800510210046407142c2d40d09030704103190801c0070710702e02c500d03180d50900030006032031030100e0310540188001106e400c2107400e00d42c0850405c001101d01900f000160483c54000c40c13501200390001030650000905d03203800c041e000514503040520a0310300da040030340301c04e0311501c041c02d00c00b038402c00303483c021076410f4030702c001003d69244402814003800190b85401e8844140300c01c0e520b0b440c800c3d5009801c0600c02c061444030008840d50b1560322415100d0b480c400d1800340d10f400d2280050044ea0010307480501e8a41c01032100c1318040c000482151104c0303402000050030700c07616101244506e5541e600 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 850072500 1250 850071250 850071289
    0xc18030601090207050607050331020306072109030207030f0222050402010806060a17040c05060d06171f0906150b0304032d050708250c0608040b0f06 66
    0x10302040c0b41c1e006072140c2841002038440f182d8441074103c480e0700048680c5911003212070003c2e881d4251154181058200050690b41c5800150300820728045060310620f00080b043c40c0c1201c422000120f4100040fa1245000d004038074280c1c400956030069800041d1480344c0141030002156600040d10349840316104804900804c2100024001c1c0011602a030115030004c000450600e04002200c13160200d03a00c0f010700301600c00c0410b0000c408000d00489481c4a01000071425584031030113001e91100d102c02c085240c50804480c40070091000784101910307804160040d83c00e8213107417070b01c00101405180010300c400c044d040c40e4000d0810f0600340d14040b423802001007041b480b10001940b103107001c1d44038100c0032010851040640060383c02d001c14000b40e900c0100d05ca09204000a02072a070080c11a6410414a81c0300340c101c82d41e11700300f800400c00f0f40401c59010030409100c02c10080c612401d002c40b0358501a100c8020049004015601c20b0060760b000940301c0c2e950380481c100c0242c1607034 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 850073750 1250 850072500 850072513
    0x207031b12030f0f020111040b1812100614010504181112060102150f15033a0c0b01092307120f0203040c09090f050f030a20060c1803 59
    0x901403c0d00c0c0c0320880f40b000141c1c492100f064064014050911a82e0700103a40c1d0340783c41c1ca4100364103019003000110b0241d00040304041c000b150765010141d00c4803c00300c00039000b84124070009504035038881d4007482d0003000c11842c0c0f0085a800206990031503242000050709803104030b907200018100c15818643e2200d02250080741617403041c01c0e00c5d114400070380844045901022011100705021140e0f5411002d00c8000516003403038201c50b0a03440b400241c11200603170402581c510300c8901c46600a0000240641c1d0581c507501440d6009001c650181850066222641c4980c2420317081405040d002e0740d11804500c055210700300c02d408100d41c20082e0303007a40e402c0003000100390710101144600a07904285c480342103c1e08502c00c6a01450b449041201c4092178140000043c004402c0141c2d00c0424030a001e0021850500c40d140000340410041d43da161a421005850b00003103100141d04000254501403030501d00040c4a600f0681745206141c03514550b00400c2c96900390071204640502525 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 850075000 1250 850073750 850073753
    0x10506130518250b0c07060f0512040b1b0c0c011b0b07031e0b06030a0f0e03041410030911090a020d0612051c0503010e04060b0a031109160207031b12 66
    0x803240d034800303e42c500c1c2444800e907140000f042c180180f482c54882c2d50402c1104000f458058000809402d80505142d424003074110310421940504440c1565247c4a08041090584001e61601510800881a2402c0400c01f038225552030407140f480702d0500c88054106000310b216243c2007071081e03070f0080320206d09140c80003009000d4803602500c5a1303090f0461a4902c0210f240d0f00a000041901410079811640d07461f884101901100b9110784d010750ba1103501c6c460402050000f040a0030060100c00610001042401030680c44148491708051514030550f00203442e03100300b00d42101c4102e40b4060b10b51600142c001c02841070000e54040c462030864005007141101100106060149060700e05000010710000c020300d10314071030716000810410042c0700d06e0221a20307184c2c001c1c0c050140002c01c914035801240c2c15a901c0d8000340d9199400a03100e840c41d01e0211540c42c0e01440c054039805c40031842d030101039641c00d031501004244003840b105607080e10a1040001340200801400010f107180325 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 850076250 1250 850075000 850075033
    0x30f03050702030106170a260f0c0d030b090403080714040603090302070806040c0e070210050c031909020303040b0c030c06041b060905010f0c03050702030d05130503010506130518 79
    0x1903007089000b9400c1030b0000038400849080c42d40c400d0107890141c40c202415507110080000b0000e940085069442e51142801d01044003900040107030000407592150390280d040d160540c00d1400301e040500b4501c5905458130ba400019030481e034141040856a15107940030768004050808a2106c4100450b000901d90f5040d002100520701a40a0311034085e1039000340b03030711004121800303170149101032010072050402c0090135034002000d105840b0301469105800d001c1c1c41e01a40c091114910120a0145005035010101e00308103500808002034500b13680480d4990145101e462894100400c1c051050310090088031a81c1a401094802e01d182900d05100c2810400a5041e942d503600c000105480380288900d60550b04141c5402d0240c08507032400315110040d9540460070410140544001038500704000449041a41c6900c1c1c1c1f25181d01110520703042c429484944280c0c1000b0620075a503c0302050030b0106000e403a000305007a80d40142803d0307203c05041d08244940324500501d00c001b001e = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 850077500 1250 850076250 850076257
    0x6071a07030c02030f04050f0d150c03061508060f0409080304050f0d0c1e141b040e0c09190603020d080d0507080105100f020115060c0c0f0e040615030f0305 69
    0x2030380307003009107802c0b02c2c0d4100d036a4000c403081680268000c000602080c90503507040d00030303080d0013000703107580074202c1d43c420b5080d543d0b1001c0104802d880b24600790060341c041c011800074001e240310550040c1040c0c44004c0c426100603001da07000e115481d00f200708584580c2c2003010841c1d040620350350b4034101440d1460703813080651803c4189010707440e510701c4128802d400c0c000780389412404a90051501909503465140542c5084841c40500c40411503a03141c207020500d000400c502485041070008414070040e280440c001c100300390081c40001407036a03206240e9982104100c070301c000390003643d804000c0041680d80c0000c1c1d071000d1001c2e21a403c0000c600018129115514070074040364a4000d000c3d18040801e000391984454064901c00030144245801500b405540c400452250507812401d901945280c000c480015200d8801c2c030203004e4800c804100030110404502c100034580f58440000c030340e018000070b00107515030b101c82810a03485007019002d50303000384080c400740c5d84030b18001e02640d0 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 850078750 1250 850077500 850077511
    0x1b0b091c05030a110708030a020c190501090b0a0608031b070816171207060e0a060e030c01110406050703180305062410021b1f0305091606050d02030606071a 69
    0x2130420820f4000e0b13102450954110582c0052903e0030342e00c440d01c0440c003940019194950912881d00b51030120300c01c804500d801c60740245e000140741f441c80e0034814400e505c000c00c0c0302005824a101042031460000895241c005182501160312000410290405680d603000040c2c2e84100014041c184200c4010841110003003030b81410043c078403c0005c0d8540d124641d203d4120750045c8074032008540d050300b00c2c241e14420752050360003d81540d6964802c544404550b10559031001c145200100703424440d40200c240c809407094101490070303038020524440e1030070060410590300c207898003600e6800a50805148e000c81070310200c1c9402e540300c109405a20000424603043c3d5294000e0071b04014140d4201248158050244008915903e4181d00300761074070b841c0c000382c0c20804410100d0345041081100b25061f64003140600300314660b280380218148814400311070300c07541001501d80007811501c41410222001d0381b81c0d6124030010f900381c01b81510107081c907450048015041003010f0025031060 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 850080000 1250 850078750 850078771
    0x812010806070801080c0307060f0e0d0323040302031c02100f09110f01020706081e010312080915130303060b03040c080d1803060f060b0d020403020102060105011b0b091c0503 77
    0xd170703a11052542d03502c0040f2051501600404e0341882400d04c2161010440d6005080c0300454501d840d000c12000c004083c1c1c02d03400a00030b41c54100008001c8101f140981620078402814242540c000a448841800c0c0700a01d80b0b60b109075180a032802401050100d01000c07004114040d42ca00014001e40007100c0708586072889904002000d150200d40111000c0041e40200251810705406403100100600904c041c40500b80d141012a840160ad4a029602c24044420702d090102009088a000603184281300d400080307030101c89420664003103500003180c02c5010103a1446040540003000706400510001c140001040140000700c14940100c46500040f84d8076405041801c4801d0150403110310700101200004001080141d0400c1984101c15040003074500c0d9034492103400342e44516984d41c001034000c00e00304295a018049a80144003e090610920b0b81d000403031810f901101e40014402c4100c5d00218079441f104019640c1c1c0d001c050387d0160303200554540040e045410460b20040c01 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 850081250 1250 850080000 850080017
    0x1d0a0507080d050414010818010e2404020d0807020a09060e0609160909150510110f07151b021504030605090a0206190c06050a0c0e0d0201020303060409081201080607 73
    0x242e0701c22011942156428051400302c0203086004403400300b40034100300507079039981130905403039a0284104444800d654000300224420030a0b10340b050800c00b4541000707010074104020142e00c6428140400540c88400c1070381e21007007071002806420894100502181c44c082c40401c5480c296086180102002c42c1d41c03107aa9501e2003c00c41c0030b1460741c001400068041d510030807120050f900b10624075001010f0b0805403640710800308600d0032440c044c1d0f00000f4082c1f2200c0b140a403040c46814204c0d6042805801c2d00c2d0b080000c040d4800010180000c2045039040002580c10080040e4a00c02c030b41c028005130414400002c0940070360030a0000f600e1035403400002c40e0142c0000508210442e82c00340005062500ba540040407420b1341c101c3c040288003403240d2504c00103035a407007100d1059200000c002801004004010302e4540c0344114580181c82c88035824000d41e8000007641d6114404690118a941c150b192034980c501600c05441070781d0341c0200c00880d03210004180b06201c0ea042e5038071802d0 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 850082500 1250 850081250 850081273
    0x30801140904051c020307080f04031505040b0f0a020712050901030c02060907030308180a0f0b06010f0e060306040605190812070c0e060604171506011409041d0a050708 74
    0x2240c000540b4001d10b0b0340d000f0001c852040c610800802c03411303401d0b401960300f08222038441c82d0050303004038032128806200050500c20040f1505209403404020041007166103800e40e101603200401800b9004d040804200090640d1004c0d0111441140d008100c40618040c02ca40908180c2140c07001e83d000c6414590302c0c0258a10004040e480b426120004081080c0b66841c241e826503805030071403081904203080310000b00420400c0304240c61188420703000d074180314144402c15141c0540207904104911200d000b0b050350021080154070710407200903689403a40e00c0060700410700e80d4402c94000c000c075020121800e20b12070444003150140c20645a50f01030096038181107100390f41008190000725402401902e8034042d000d03620040181c0094501a20750440040e001705540407055941d10280781c2c00528028811010340040003820140d403122807240d101c0050380690748041e030180d603803044842d804404482c0001c01c110080c10036140c1d10407242c1071403503e407003060040ca442e500c5280040c07070 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 850083750 1250 850082500 850082509
    0x3120c020a0609020a1d010e160e2115060f030c1e010e120109201e180915090303040f0209060f09010b040608060f06070f03030e0a03080114 62
    0x1150145a80c050060182990b451500400950500340d8105a480c03a02180c18908151640c3c40006034151303849540d0303d807030a01d1416450040c40f034400703482a5101c000e000fa41001c001220000b04403030b098617001000742c99400c020000c0d00700100d584908c1502c2d40d005511040c61901490041e10400c9902c1c0c0c85005140c0d9901d600038005400c03041403081c8000c16850800c1c3c1c107400080524003803106d501c4d144000340c8400010b0701d254415035900e46c0320504028800d12001d001d01110444a808030b0040000503c81c0b0b51048948817015440e440030200c6940e404044203d850b810b200034041605043e4161507490584260050180118501140d40400d000003035078070696011040c11545001903003440450305015224541020907850854401c1c1da5003800756000e86034070700c1c0340c035210b6160410042044101400c410700070040e5104800150701c0e030400316406580c010004440760166843c080b0002d00c040e903002c121034080c4045a404040c0e000f070005048910032010394121441303110812 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 850085000 1250 850083750 850083761
    0x7030216030305041e08010c0e04051e0a0f0b0406060f14030f04080a02100c030f1406150306130f050109060e090d0f051b0705150c1f180b01030312 65
    0x540410010f0000b0800c0420501141121070401c500c0c5017804d03591032042a080da031048604c1030100b40034405a1031182403910916a2044c0f502d21601c0000f09824610712000c40040e00d580c8a6603159894840303585001d82200d0030008014104020280d0707584801405021000452400682454509050340c0380c804203480c040d000c44180b000d02c64403295a47c60199000c40c04003003e500030b15901162001c1c261040400b0013242d0b803804140e151210703c07104101c4203104d10320801c0e20301030414000c203600c40c1e00c0141c060440702c8a50a9507600d5850025980240c0803030103041ca503052190f540380803480e94000b41d040701c29284043c0700c2547c41f03082d00e010680080b00c1c000042ea00c500109440140314013102414082507007016440d20710249240009980c0550035904164403141c003c0226080c070841d10520448180754203820001e1006105482d408207100700c1c4250340b0100c41c00c0b02c0144407507020000403003a40001401203a018a4a440544000d100990104660118000c02d400090055 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 850086250 1250 850085000 850085003
    0x2109080601061b2901030212030c06270a0309180c051c110705011e02070507061d10030518030408190c03020406030b011403031608031b0f0703021603 66
    0x1500003010401000d00ba00783c3d00e114055490418038500034954921000f084190340c008a1810ba14641c110300512020b100145104021a4000c02c82115202c0307022034030b690007500400120760441202042c107150b03003c042e030178008280145099101015041015902201c44c44550304c080d000d55a007801080702d1181c400310b03010801c100540807007403040c46080c81e9164034425000030010003140001c541508043c4e01112181c0d03480f0000000303441e41005118445030280415403070324002d40c1e5440e4459807284134081c244810180c03280d100a21901d90801826005440151000150071004024140a070b5a80340d05800601c00d050004101004540550340d06030010040009201d421620079900ca10060311a15884000800103a699010b130318000e5004040d245003075410a442c49013180c0081c44210700c241e00401004828114000a1450f1243c0000c0e0742030300c9959920804078070444c8009240c3c103141001400c01494403100e409010101d0281e030071a40350320301c01c810300e068410342c6000 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 850087500 1250 850086250 850086257
    0xc0906030809090403030608010f020a0912020607150f02030a060e06010c030f0e0d080a09051801080a0b06013608160b030403050c100b1c0218070c210908060106 71
    0x1102c030450500118298120b4403d20700010038654031400b0700e003180d413001e00d141d01c00c60f000a411011141d10150401c0604103028202c05806915030000742c13039101e040d50040134002240001001d01400b83d000269100c602541136592b40780460400d1b00070585402000c40c050507207408650a54428075001000983c903440310203119403095800d844880080b403c40e40d0002c3d2040c039420000d141500a0b109541c1d05494044425041a04010160342648040403070300784158010001c451002440c030491980000498840340c841c100102d07180b242810f81d0541541c04907030000d02c07111070304c4010b0003c00410b2240d4812151550041c136107545841c140c180d21440900c20602c2030300d00c00b000039134006201e0709182d890001002e040e40d080030004541c40369500e0b998040c444943c1021001d0142e42c80c00d6511110245100345d00180d89028040c45100b04035401c440080c0020f030164003c180c80300c0d009901d10024405240309010a4080e428220780013402172301e000500d001d40042d11905881c41500c = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 850088750 1250 850087500 850087507
    0x4150c0210110c09090f07030606080f0d0e04020a2c04112805040e010305030c0601120f2013091101050901140702130218010315050604051306080102160c09060308 72
    0x4001c02c05a000e0040f1706907000b8009203201c0c07800200440d00085100d030501261251a14a13803600b8200603140b9000e483c0c21560382200303010303400300340b24140b00c3c01140c0050710384181c9001258039880c0da0191a54210f6066901c207807134005c642078141d0004040b00c050080c007121292807603117409509050307142607038400041300e42140c6585d41113002000394a0078504055941a102c0180d0000f0382c804d6415810028840300c05441c140921405002240e580030702d110300fa980da140c500709032074001400c0141800c01c7c6818400d001101110030300b00040c42203401c089000c002000400c0134130300c1141da10252131684452540200181c03811010141c4803078001ca820382c6000351055100142c120380c0001d40d005220408002c40c40503002d031f9800c0e480202018031200002404651450348010346c50715202c0300400480e500c44c0203d500b40c0c3ea0984001c50f8036280b00b841c2201a04080c0c100320003650000c180720380e00c5c00d0110014540c0301c0c0520b66425445503a26078000855582e4003001d8400030040 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 850090000 1250 850088750 850088773
    0x21b1006050306011508040c170a02152712060709090509060c040b0a11030d0c1b0b06011d090403091403060f0a09050a06110307120c050a0e010e030d050c1005090c1504150c021011 79
    0x4442849115000740056140d9030058194600305201101c6070380100e471101c542441417440c0c84c440c00d640704003400c00a114a045c9842070341d055011b6031007204503091000039440c5605225120610800c0503072003c40c1d46500106007050042e0548200010000d041566004c850506c401031342b480c0c0c07581140605101d0f460714001100d19680c83c94454104000c2c0e00340340c000c0c64451491592285000f9540c81d0f6800381800140f00c0700c0c10310800110710035400f1100384515029850762040c0c000c0002400040d0369201890130b030b810140d80c003501810303c0d480c00900c0c18002e00194029841850207956030101c0d4030b140802e00c02180d00ca42400390026405010700c42080e40282440256550305042860b1a01d5080c400a482c00d0b03800014100080d5010235005c0300c512042000c141c1c41400700c00144420f00c0c000208541d00c00300002c880c0c0c420355030b0103e41d420510140d0101c4000d0000c00008990320306410201070414001d44200302d006001c0c1d8541c0c0c1d6150388c85202c5035891000501c016000c0354150 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 850091250 1250 850090000 850090057
    0x61503010b060a050c120304050303010e0604020a08151201091a01051801150507060513110f1c0f080a0507050d09050310090501021b1006050306011508040c170a0215 73
    0x170741421261403040b10301c3d0b1298004108040c500c07883c1f03c0c1d001160b50b0b43c100242601d480310090a0503005034014800d40e24915006070115134451100c1514415082d0140001980000c030294400b05035440c000503042444140c07140d2080d102d851414502d03035a640c0d5070900c0210343c482101c14441d141e006006005800c511150448844030b140340141c100300e903d80b030b1141228425074904440e0083d90f50380c2010000440402070034294115090300f80c10b1081804950340c5114500c25a100c54000007080082164128100d202e641e0020703c3d043d1250403010000e841c6500080c001d0700c072446180001c80803d480361444006640c40600a0101c1c078500001c1340014214800c021a41ca5400344180a801045100300c00800155540205203401c44c2d61020f2045403255040f01d4005d400500042c40054030800b100c0210003c00d160110f09a030b01c074202203411300c003207410050a0710384041240d0072003400081c046000a008441c070103210100280340b44c1141c4541c1d1442d45152100b5000c00750701c02003 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 850092500 1250 850091250 850091257
    0x9031a0a0605180603071e0b0912010e06100927030e0915180402010212070f0b04151a01080105060a120914071401020c131d061503010b060a05 63
    0x410200d07086890703100240d1001031015103900301006410030414245410803640000b041c2407100e00806134014014240c410000303004801e604803000810003030035100c4401c020000311100d8000c02404600c10505a00d52106507208080c243c0d6000020400132154450647c1f10000740c02200c2507110782039180300038000012401d400744084c542c841800c43d00e0f83c8121522850f4504101c00140c03074940c040160340c1c1460340d0300c44e540b03080d844c0070080182d030006580307402005800c4600d40c48075001c1c03902412414107041c0050040491740280403c02c4034840c012800140341301014010070032800e641002d14149001417a000426500c0100a00c0c14888020004c02c4140e02d1310042c0b50304621a001c042c5c61307104104842004011480907607c40e42400642c2c0501000d480801070500444d0000355035101c3d82440c40d2103000d80c9800748002c155640d01104c0902512996490b0862003154429180c2c04100c400c04140d00030348071100c00c42c1c9030604c18144003201c0200064280155640c04a4840c2c1 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 850093750 1250 850092500 850092511
    0x901080c030d1116080708010c26101805071b0f020f0103060e0c0301080c1f03020d0b09040605041b06080406020d0621050111030f0a0c20010e010c09031a 68
    0x1314003001c43c0c1d201c60003052501500c03ea000811049240280880c02c50b41c40d646003400300303c0b1071008000c1011044e01c090044511041061801e9141c2c982602ca04520175482100500440010364a0341c580300d40146201c0d00c0143c580001a000c3d0804c00a100040110000e200070040401c03200149402e440d0b6800c051310614001945907100e10180380c0d03414080d515079a40381c4010004114001c400c01c51401000c038180c0c3c03540744d050709030400707940c500a800305500249500825240340941e0158405010b00744003d244100074100f0b41841001044155025100600c10b1282414803a04144d24141110100d50b104031050b40d958507120001e400144c004009240c0320400041c2002c1e2549480d0b0540341d0110004a400c805881e105003140c084240a8003004002e000300500320001d4128150300c40a100c102180440d2802400c446400c017000d05610420085c66400c01041d0056006480115110008004001e8800010344200c0300078032005000315100c40c1d1640c0d10300b0000d40d2040e0000b = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 850095000 1250 850093750 850093753
    0x8060f04061b0903021504030321140f040b010f05010c03032708030118051302040c030912030207050f01060b0a180e07080f10030804050d0c050a0803090901080c030d11 74
    0x15810700c4034a01d48502c012200c0e00014030f5044140f0039440e05c60109660400d090225900d800c1c656075014002640e09407401e03140120400c00f9103a45036103508403032011060200344007c140782c0204101d11070031007521b06407070034149400007080b804044a000010713500c05031550311007101c0981c0d00f10003600000404000b402c07071a400d08103500740380d04018000540300341030329a220f40c1810804500c490110380c98506140c14001401200821141640742e0503030140c8021611011464080d4003900310560001d01d03074490000842c000e281d042e4068141c5a1040094070904007200e1880c40c26124a4010030301c40084c10082e880905000d9080328010003041c51030810b40d95a900301504800d0350481c0c0c3c540200d55490700700503d840040300404c2c0c0c0301244c0c0d603650b800c141c15034503801ca03940124080c560040300c0f06100b0409120011500030b005000007080024001c0c3c0320001251260003840500b40508246800810000300108500340700e94409401060102c691070002c8a40c1310410503040c0c0035 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 850096250 1250 850095000 850095011
    0xa0b060403060513020909030301030c1a12190c0c050d0e0d0f0f020a15080c0f090d05010209041824021204060c14091e030f07031101020606040608060f0406 69
    0x40d00b036002d41c80c03013042c0d503001d10416012140148621000010039100701a0810001400000c481840c2c480990f81c400880c20035003901103088443c6031150480c28050110002c3c10807c205034002440c0c504440406414488256a82003d071110903246100508030340150b961401018490400b00c24000c0c401031510066265130385603100001d42450041e12506040f45d0000b0039807d003040c2c290000c00500003100b4031038208005c02840300c0d40251a40d0038044002519920341035401084d00c030314080050a015042d0940e04e0080e00030b45c40307005101d00540c1001c020402000c9006100528140c00030780c10004160740e0612043c00c5240c1d41000c0b40c074503509000312107101003c090454400d603c0307804001383c401503e24000d00743d0701200b0819041d003103042000041503111101c08100ca040c0040354070400d034071504006030a1542d80750700b030443e6100f142400424040310400c9180304000c2a02a52007a07101c1205100a483c0b080c000e140c070035400280811800e801c15081d807a401400750500180 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 850097500 1250 850096250 850096253
    0x90a0b0301060f18050d1211160906060509010503190f090f0b0627040c0e070503073203090c0a09060509060d11101110020a1101140a0b060403 63
    0x1068000707810110005110b00f1105000a402c952160485841c010141d00302c50b1910300040e0b070052001700300400c00d21013500c0e4041010300804414242d25075540548001414030203034445005800c1c403505000c0c0e41032200c00900b050107103041300d14280c4180e540501d195520b021840200b120300c1c1400c0007407036466480444010b05c0d03201c2c07818594800c49180503080000d00f0007003400344019141c00d100c1d11043c0b071010b8000d01e2032180110700c5550550101c00030b94035030034009000c010552003100144821420001503d50150040d40703e007450742c03540214144da50000a10010341688441c003010040301801d81900d064034051640004071408646d9800e01590204110818075408401410b07200c160a0210b03290815019a2203207058a009180800645039200000407841c03406024003c012a00c411a0b403154410320701c20f174100b404454898211503540c1000b940003126010003d41c414140c13503629807060140c91241100241144503a03265107809800130324200841c00d5020340c04000000 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 850098750 1250 850097500 850097519
    0x4050f010513060b010207050906130b100f1106060a091d0d0f09080c1305040503041703031509040b041b0503120408070b040803190509040213080d05041406090a 71
    0x14800c03048a4924842c50005242840a545040310024103541284000344400c1c5c4541c00d406a1260f0100c403102103140900ca810300090404070007590300000d84d1445a09819000b41011244490664407000f042008000340380d1035075002d4400650003106030b801008101010340255404000304201e41c0b40d1041072058682c5001d1504500d800440d140340d200346071168000b681c44d002014040040c12030041c40350009104180c4010301581c40e1980c400100e8240039080060740c020388071440c40901c110084004a030b590341c10446000e18010380d109260343c81400c0ca4820719000f50f520410b040c880303031100e5403030310f0001e004101d200710355403844040001c060390100b0201440c4c01d0500c007169500d90410307a4413810009540c10281c09000c0030441000107410000807107281490804098444080c440c500706d50038412080341d254494004a5120b00340340716422110101c0d0319010403103502c210308038400d035054091840351502c0040586031760406401c208008010808008000310725041d01c3d00c5580 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 850100000 1250 850098750 850098761
    0x708090406170d140c070302040207081e04051c050613061107060219030204031703060301090f060212010e190504020d0c030b01210b011404092306151804050f01 71
    0x801c50340c0e200401d41403c0c0354010a8000d4503406800c0d00c03c1c6440141100f5590310400c41c03200900880c0d00184c080103200c030820a4079911003110140303142246003c003100c0300c03d801c00e001d990310403610f00c80d000380080b08280050240550110143c850307951000e91244880301c20000c01d989240d160310010211803943c200805206108010040c0c940f281c41e891452001880b030501002d0610412090022071030408840c1924180302c511243d896a8050109024051b6200300800406a00d6400010408250042e0050541d940c000213003c0e03903100c1d81d4121602045e50204030641c8007200c00c1c002e14100b40c0003071360300074005042010026026a9002d400e0011a401503920982140c01409000303035030020b440740e0b0303410a029008082d50503100d0a04084041c41101500c900b82c04510009490359001800802d030400111601d80205e509a0400710072036074aa20491f0040900141c0c041480c418614004540584160288039a0303400004620030040d000391014071035043d001a1080c0c090041 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 850101250 1250 850100000 850100039
    0x30b040605060c0d02100e33040809010806090c0f0703201c050a14090418080915070f0b0601021614090112050d030b1c05071a040b0708090406 63
    0x3420a0030203158000d04180851001e442e030241040240e44441000007005d0b148d0081c4000f44070407100e1b0580400300051582e006054621500780208414040c4100141203651000e807624505030351040200b1400c060308450840d01d0030300074000b40035003482d61000350030001d21a0500910481001007241d200b4452204214101e920107070030714000e00380c400d41d010f250301e24a090081c14220007007009400420104826261a0000300f5240c40e48c8e61181c00c03024030301039060840c00039400182841e19280d44207410f000c4c010711401030081c3c10032800000f242c1c4c416070810403c601c2c24403076035258000c01c403001d48081c0c1144980c1681100c044181d0704600001c3c404920100821010314041c06a520416030106410403000070880020401c04030300e0140303a86540c60300191340e10400c3e0002c0d45294280341c003009081103824000f810444001004015626461441414081d140c15640928850360041c3c0600041c02e0005c42c3c00a47c910300a4000d92000a00102e0015200c2200e454245d030310816 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 850102500 1250 850101250 850101253
    0x60807030623010806041115030f0f150f090c0f040b0304050d080c120405120705030417033f0f0601030509010c02070611100507050301090b01020c0d03030b040605060c 74
    0x1c414491075402c00d52140c00b069a000b91015600d4a6092a00c981c070052000d442003582010013503031079482d021000403401d089400980c80c2d0620740110940004116411048405000302140b4070441c0c006e0403080f0402e005041c1421500908203100c00c07000080d180340ca112000744007a00e10000c080001e03002070210803642688a14140c00c105240000e140181c000f804440000e210160804108803040b600807940c200c0c40b01d8440d40f50141c0f424118000e0142d240402180c20310403c4004002442180c8582d4042080c403603a4503480c0303449100d03401110060107604201d0080320110071101d40a03400103195044001074500c028010940c800310b4034a001003100038200071156815200f01034004107880004c12043c0350346c410284d0307541c00d43d000d03050a01140400e502036451082082103411242c42d00c0920040c10100c0c00038060350028050070314a0350601e0b40800084d440021010641400103108805003035858070180d004004485103103811035102c1e6800f09443d2104d10080c10003400b01e00 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 850103750 1250 850102500 850102511
    0x9060a0210110708251407030302060c0f12090f0d08041505061c02041107060507022505011119030207060e030a0b220b10030209161e030608070306 65
    0x1890345080340c0911044004010b018001c44020a010009440030340001074013200071010701305450004280c1c00c4000410a11091030f1518034510046442400ca9100e03808441d00c07034403140105d40250217110200800701805101d10007240140900c6141c002208006460364100c400b0b20a80c00c088000c0a039a011510f04006c1c4410442815912014030054400030042d03400c0100014a2a950171403020151404c4403250b00d042d03564641c000c040901d0800021907403240325281c440040d2004a601c41c016000f203021a0b0200c0c40701c2030700448450450701500c0c800600341401503510800c0b407806080c0f14031882100031400301001d0100c0f581c0e1802900202151498808000d010503000c2402c41e0281e00000d0f60a000038004248164119120105110780f9899440c040d5131503010300c500103028400300304144041000440304e4001603900907918440d40da030b1030005a4240f50712150081c00001c244c08030b81e0720102030340c0e010043c1c1c18a440c41c000c2070850380d0f075418a251110b550016560240d0340d0 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 850105000 1250 850103750 850103773
    0x70f0b130b13050c0f010302160c080c0d0819050403060f0b040501050402092b0203031305010e06070506040f030504090c110f060c07060b0a0b1801031d0706050f09060a02 75
    0x100000d0ba0240c0c00e001281c03036506165490540395921000c205008194803140c00d82d440c1c1c045d805440c1401010303c8010001c0c80c05080549684940d440350708001e002c0c2c1c0d2406034641c100b5004102c41c89400c0046a4030f051012903584c070000301c150082c4010003405120100000303140c1d01a05541459030308001c6141580c400c200000c45030181d0020380328500c1004161200d443d1800851803400301c0c2d43d80020502031021007180c1c080a00000250305000000d100c010784000c000d03944040c1d8800b030360740e000c85c42184828442144074441002c2c100e42d010600250024502420101c0359600c00c0c40d15500300f0f59590a540d059900d001244408610b150242d64800c43c81008954001071040006000c107040000e803075411440381c02c0c070250403141c50b03a00003643d5495130081100100f400c0558a80e032490700320340c4c19100e404400b5055000a003850f5045c0024413000c800f0110045c0d02c1405881c0992404030203441c194041c101c02444c1c00000c0c4241c9026070381d03080182603115019000f83c0103d0750003 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 850106250 1250 850105000 850105013
    0x40b062b0507050918190e030d1b090f0e0c090f100c0b1303170a4502030316030903060501030f0507063212010915090501080a08070f0b13 61
    0x2030140048500ba004020400541510f0300050040d1943d220001250207e40021a046126103035a9803140b41c10110a581081413040045e04004016901c0c5171465031070b4504054640c00d10f01c503c95906002c0404103a41d4401c0100900c9042e1005048a11b04007005012803078400c0031f441030320041500102c80006001a0501550748400b601541c0c5444281c580e4004c2c1c4680d03010441c403280c429140c0c00150980d06a0340c0501c1800c042c00d00c1d0070b031481d01002e202c81940e004054002071a6102c00e800d110481036a805803d075081e60003006076007001e1480340c1100700c401146105a0400103101d50000100c1d010788a075034061070003000303000050015800d2640c68100e83c1d500400400490308420705c1d0030418078038880000d61039059803003131480c400058844c2c140034404400d0f030850b559500001b0f4140c0594803071503c0c81c858940e4811034950740c80c2c2c10700031140244295080d982000f60040000f580440007040700511614400790005010b032a814041c54044800344010000300501c08140b142 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 850107500 1250 850106250 850106269
    0x130f0f0204143f061609050f2b081801080c12061c060509250608150d081215040e1509070b0a02030414040b062b05070509 54
    0x705490f811002c2200031001800084145038201c000080001c51142d40c81c405041d00840c0341c2880700315111410f22901d865000309036214000c01003248103400040900f441007184c01c5c0440d000b072841d802417101c00c000700c0302041c3e01980c41c211400b142d6032803000a200d041c06440d12030800703003007030801d07131110000541000400382600d0400802032082c0c0d10004000e4060311f03400b005c252040c41c0041d4690380b00d0b0b0208105000014103240c00c007000c01c918000005450440a040c411101101c0070419220031480d04030b501617940020a440002140240c440346400588140904000075030803268545032410741007900074503803684202c0d05106c0740c0c1c0b0030102280c910120445007002060b9114524513910000c1800ca1080e110718032001070348401d000e0080100815042c1e1a85950f03030071301c500c020345992081c05010000c028040610055080074400ea44036804050801c41c904010406035a6171082c030030b84164003070314883ca10600c0039031841c01020b0007001152101c0d9240c00d141e00800c94580c1 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 850108750 1250 850107500 850107539
    0x6120b06040509280c0e0702060c03090d0804050309030d0c06051f060c02010905040c09170705060a230d060311030d081314060708090d090311130f0f0204 68
    0x28189428403600b11408142071030360500040b54007841062a5105003203902030920003806154005c0d030009140440301c029180f084038030f0703825148a84d45134104151540001c1c1d45085540d48282081c002190041000680007802142104d04102402e00040c1c42d11903039480610005034288980c0003007048034061107811982d062a60080d20707000c2c100b420401c0d929032044d03900b0040c2c0a1019001e41e40901494005018041c07c24070200e410a88040c01004091255103561003050000900c907134808039842040c2c0703070014280c500e0803140704421202c0c20580b001111003030440742c0d4000c032401410300c0105180725008902142862940c00d1560700c010302c1d0404203000e500003118020141798003150541d801000c0501003614142641801c4080d011961140d0010388141c0c01446a4140c00c1900e5038455841c5800b2101030014990081361001c803548802081c0c1407401503000040c0c54500429060b82882003c0003c28031814200002514980804001d016a0019040c8400400801040c8101e03 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 850110000 1250 850108750 850108759
    0x201060b180d020909060105031501030f0b0603030d020c010b1002010e0601180b03070b07060e0d02120f0c0a060b0a0f060e060307031b020d0801172e06120b06 70
    0xd16100c0308280c01c1c45809000c2094000510030032006540d100055107419070041c2000c0990300e0200011680c80000b0700405109104100c081405035480d1400d20341a0ad03030010416074000d60968810a00003006040903915000902904008580520140110040031800400c840720000c09000940744012008011641441030070822103500003140c60454000140030021002c0503416400100344076082e0a906001d91030300003605552240c05000d529005100401080f2000c2c0c00443c0e40e450092203c0c405038000d8a40c08500790181c10140c01a1115400c4503860155500c175018180f1440100440d6042d546038000c035100d040103480a000780103003200001d165828050042d1094441c688410b1150100000041c02c15119822080c0368080b0030100c5048048061006901c0f900010064030000d4903080c00014008038540d984481500310344042c060080f4a10400684481090b100c3c10300d076003c1d480401a818010301c01c010041c080b03004400340c000c1280c80c007541c54036800382c040c5104 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 850111250 1250 850110000 850110011
    0x1005060913080a110c040c0309021509011d0301021308160b090d0611090307060818150403030513020a06050d05060301060812070c09061403010b030a120e060d110a0f0201 75
    0x2440b01022103090403001e06101115940502e0740301e240007120403810fa04582024038032183c0315055000849400d1007140c02c034401d01001d00c0c0c0c02031680a124445400208000e07600144050744120f640f4119a02800140c900070b00c403c240c41d118490b5602c14451507100e440d11031941c42003100810013a000d00392031549020020707c002002135000c968041e02140c1c0d100e01c581081c0c20608100c1d0350b41980074060310f640b0780d41c440d40980202c80c1140c9000c0c000c04100882d030404240031034070408035144070070745102a0302d070794404800070103000b0301d144464550803840b072000d039696a914200a003c50303074887d6503807051000703144262000980418001c1e810080103000240020490a43e00f80d01403170705030f4492441c1c0c04d180c0b04029003540035401c00740c541080450040480d40c001010208182c0080c800c080d40741090541c0e89115050141070340e0020410154840d04c0b500c082a03800303100400040c01c0a0703034852048215150708007508007a420000318072080a07003005602d14015580c0c0000c011 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 850112500 1250 850111250 850111253
    0x6100302010e1309050610031506030f03030902031608160807030b061002070e07030b0f1801090528060f081207030509150d0603030e0d02030c0607020d051005060913 73
    0x2025604292051003404140c02403008003d490780709000b0075030040e0454110b410500310030518000e85004c2038a06000ca00310004030010240a8682200c1c1e2010303c480d80303010340b500d08400615030460100d905010300551025690640681080035200003005001c1e10451130f0304a10f064185030340503910310307086100104085164800c004e68805004d072041d9030080114036049013030140c80d03000860010840401e1103030480e0300d07502030741d4142c0003583c501001c52688000c0100c410300c0c6d86c11020783d001c0030301c006004447d4960003032900000c01a01c00798140c1d28480d455007541c5410750312604842e5a0b008100039004016044c00001c084000c06001c4034808640034000ca4482c1e484054280140001d4030b415680360710072513841c4202c6070840341d40c4807401a24120094903d5101c02da0014240350903a00280c5401c007180e070442035005005182407507020302404090b41040720180e0f4049070000c05040841c106000c2204002951000002c0c03d00d00041000800e903405003076000c54018454440d0b0 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 850113750 1250 850112500 850112507
    0x6080109080f0c03070f03020607021509030d090201030e030409050a110307020a0b0403020c060a080702100203090a1104060504090b04200d1e053a020c091b040b03090610030201 78
    0x11101c000700b0240703c1d036a0f55000303480d40c0b843c804d01900420740500c51034032030f0034994003090103030140e401903080d81c400c442600345003c09468140c0303c07054140c2041040b4100100c2c1580900c913013a20604022403c035110368001c40c1180c00c180d0140842a803104100510609141301e0120340c482140d2006055041c0b050b8001d581c1d018445000b408040c420001c601410b00030001c45d84190001004155525202040204100026200300300584544080c103440c21f190380c0240c91080c6080401400304001e0341c0c4400340b0040401000a4100d40e985402103420303116405401e040d9030042c007400d0b01908080ca8582100401070b0041400d00000265202c241e954200f8207030156030b08010b19402c90802c115200e01d14500c440350041c80b5114410702c1d00c80c0c1d03490300016210281540408016194000c042d1a5a11610101d6400058001000400c89803904464090700a0200c0ca01d05034001e01c142c2081d01030342c0c00350304040d20900000c410000564420460749601004403081e07500f00515550020303 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 850115000 1250 850113750 850113757
    0x161e05090d0510050a0903080a050402010509040c1b030c0c06093b0403230304080708340b01092309151302090f04031407170d0605040608010908 64
    0xea114146041c051800d00000f04022215030030035690800603402c01c00c2c09040102070031501280454141c2e800240020701520942e4401c4d60180c541e245881d9003101000f00501030913080c0710901020b014001441c01510300d00d6051544a900c500007a54210f05194480710225440003007008403a110a110f850000007042c03000069008001d03803445852544d0851003200c807814800880c44190401013030590013240c03010304011545101d00c0103104031070084103c0c03004407005001d200f020051000055007000052440111a80c1001014800c40f8440b01d0303850030400c00440d8071145c1054170003e0080d440a00e6004003600d420030815074545d90b0b0b07141034200b1030701d6621000aa15038000344030741c8403d000360311002841165503101454501804416120345201c142d005003680c8000038403203284416824006c0ea0143c88980c060081a4020a40381d844008102d5021100a60310401c1c81680c2000d40280064a1408038840e400d013001d0100320f41041c0e0181c40d06030304103c0f131140480c90b002c044 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 850116250 1250 850115000 850115017
    0x309010804080a091a040524190504320402040b07020d1406010806040606150e1306180608010614030601092c010b03060c0f09060310050a030302030a031104050108070c0614161e05 79
    0x3e80668409c82c07601525079004940c04800031144809a501402920f4000000f0085c12031094001c4d44498000b40004c0b4044c2d80190500414100501d80c0945088503140140900c2454445008883d44a0740b80c02e09600f80e100000c1c0b548a14107010170013209000b40b00250444108a40d0b0051007148000c1c0401003008a0790300903c1000500455808290000c2c0040c00c011040c440c1c4003031150038120018055481008940e5103020302c04aa4825402c806072645000100140516424186191300130140505021458001048100410400700fa01150103070007040001400c4c1e11400c051508000380142030f210303076100400c0108013016100c010b80300a840295038981c2c80e640c658015030449191900304070790004030b0384030000c101540003008107001030f015641440a0803400c0004034040c081d90140c107020550324000100301a1003840d41a1281d400b50102064182c07902c045102000720940340000442c10b40e00a0882d0140c009560010207031150300310403a40c00030b01d01e004002d402034003003 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 850117500 1250 850116250 850116277
    0x1050d0e010b04051906050312031f1d011e0f060f12111c05090a021002011404031107080a1e0c09020a030b0f030309010804080a091a040524 62
    0xc219802031025030041d5410344000d8801c00c03013410540d400361510200c0326100000e40307041c814040350341e050209451701d8080c2c80c00009070031910781501030b1001705180320101a4015048500103204480d000d00c94040505c4c40420a4080d4103028a25080301d807080c0c01c515110041c5141088100a0240e0050448145207002c0c401782c82c20742001ca642c40c0c100010030070710707d003048003404a40302c03410003c0c08c0c00000907901c1e00c1000c3c0c7d08500401600e6044498000355040000742c10050709101000092140c00d81c4000526030720002009031085100740c0d0142c00095940224007081c44042003403001401c4610001d00d1040c0c0d19546608074000c00c154080b4594441c00c5102081010742010100030f004150303400d54a480914000400400303a43c43d00c1440307000c00303100b14031043c10040211f0f000214181d40d042d005e0b80c0d8a0304d034004c0036070081d0080750400c08600c800088a01c48502c02e0032a05010f0301c1d4955485152004001c0380315862401d110b00b003a2142e1000f445600840b08441c1e116071200c0 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 850118750 1250 850117500 850117511
    0x90a020c0a12020c090a150510051905040b03180d02010902060d15260d2a0305271f0906080a02130b03100e0c07030809070503070602060f06030c01050d 67
    0x2d040b4144007a2a10b06034004500405012010640c0d42080c560740d1184902c1c001010341e190104006880e141e0881008990200300e003002c0414890140100822181045440c0c03664a8901c003255510455400500c450103404c2d20702c8240d000e000342c3c200321500d40700074801c0e0901600042d072248a80383c50f14903180c0e03581e104041001c0c1b0407048200248a510100c1c10119070018200c0549008070a1000d183e0182e11081d0900c2406401c000c2c2c1c0d4401100c0c50038100f211702c0041064205883d04080e018041c040c0702c18000b4800080300c00640000070b100704440611114140054001001604209404500c000c4008141d0003046841198030902d080281d0313850b9440201c000b441000012854a980c028001c02c41c1e010300402507015090707a015140c03615540714900c0080300d03000d580c2c880700d695040210601083c072846400d03402c05050000d584045613200d0000b4940540340c0e102d00c015070005410801c008500e104040d90002054001d00b141440c0b09000800a100b07007a00703550300039a6803 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 850120000 1250 850118750 850118783
    0x20f18040b090c0703140703210b0a0f0302030106091109010f050702130b091e070302221d0c1306030e03073e060405120a050703060b090a020c0a 64
    0x54020000c1c1440242000809081c0400c0c082c0c5207601c41c21080e004541010381e200210600398049504041c0c15503035841950600146000c0c104802c00c0040c1c1030329071203502e464095520140c44000400385e22104c81c0034589180305050948459600102e595483e051500c43d5492142c0c040b161000300910300350b00d0b22452013805507424001c2c54006900041000004501c90100760301540346440c00310b9500700c40380d54480c405401a12107110854891214201080c00180241c01130140c03100d03180d00101c10a180ca030881d0369002d400390f20645c059041e00604c10701c260311003400c80c3d07000322450003240e207807418554800070721140d20710450b41016594042044030090500c1030710b211b694083c00301a4280b8500091007038680049804c3c00c1d088a682800014000045005040c0c07480301900030ba080c02c0c50802005000001400c00c0d124a0003011030001c00502c0600400d805175200c1d0f0000100964004c6c00e000c00314100800d040f202070300c10494007012085c005480003400703501500100950048 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 850121250 1250 850120000 850120009
    0x6030f1c231909031709040b030606010c02011107091e1104060504030813090c020a0b0a0b0a360f1104050f0918010204030b1905010b07080c16030302010c12020f18 72
    0x31940003425161034031495170081c2e04000000c2c0601602200c0c10700c02c068045080540780c010684045001c501084003103c0194040c4d2003008a040c003140c2034032009551940d034107003540c0c0d5801200d00e00c00c130f41c0103da03408906244501c0e407500300306021850800303040400150180c8941d01019000c0c00000c901b41d140041020f4400c0c014240b04a01489010b43d80304003c1d40c0c2c1c084408044038014800703000104401012301c140d50104100130728010440c1d14158044255003514480c01503074a03400300c6075180e80401d10544000d8003400d10000581151160381e00011145a46400c0300160f801704401c0016954000e4403035a1444201c030040d88a459455880340803881c2071620200550000c2000800c4c0712410003024841e40c1507180c00c00594284503251800caa13003d020710381c6440418001c810101d40c3e0040030b00b50200e801001c40e152881522076852008020f41d1049005039100e44055004a610200444c0306041100080d420210061901a10b502816080300080d0446803644115a540c = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 850122500 1250 850121250 850121267
    0x221070f06021005010515041404090210020d0215240f09010f050901080105220602160b0a0c08160f12060906030b09190b06030f1c2319 60
    0x928004400207030380d40c50065154040070b0034a02d2042c0ca054000203445c20400d240039401103665140b00d18203810007040302811001401a140c215a6640c00d01005071070f403548941d482d840a40007400806543c0f03800a01e4441c00c072031907103c01c5040c0b100380054281400c00c000c980082400c00354908681c9070002c42c6008200c03481d0154005200d60000411203610007039001540d40550708941683e8840d9205403d03a507058449030000e110841d00d41d0752145e40d0340540031070144906001b5203481ca03514031968000846c10026101a5007031028060180d1251044041004150074444164500540e04907400d4801c103a040e020f20852007560100343d8803e8100102046030420104085616180e0a20041800340401c8400700c00710008039968003800220b22100c50360a0b400da0000309020341d611480c4010191943d50144a0f442d18013240d54011f200d03403901c2c4880321a0600104204040c020022150440d105d031000c0c00821000c450381c011001110074140856141180000161000310342901c07 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 850123750 1250 850122500 850122509
    0xc03122508090708150a020a0c05070e06041b080f070903140f0708061923091b010f02100218030709020705010f020f031302010e0d08070209090a022107 67
    0x40c29111a8010303160841800c600074406030302228102500e0b40d280310394a40c41c02c4085401071801030300140c842c4130f00e90002d0009001500e0712140094180c1d0710715252560640003580512441c00800010b41000d00c00c07c520180e00382c0041111540b00b000c050302c030440c040c12480c0c10405802c0041ca600f4043c0c0c6c00c41c4003c580c44403003510492886000c450700c4980c41c0d00022041d008206001a4074900066020301880245c08400d0f00034450120003401081c031907149a00c0a0810508448485000420948681088400b8080b18000405d140f044161840b0804d414484002000b0700c68a50001c0c608605084ca1310300143c0e50410034002161000040d1041d0790716205003400442c0342010780c0c01510545100314024009040d46016034016401a040911000d9905100180c0051401e0200040d00350042c10100f008000700ca01117414951400801d42d044980058000c003142019442160301003013070000b0301138414552380014a400100e5072940341203054000c4a4142140070300c000300080 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 850125000 1250 850123750 850123801
    0x4021216020c0d05010e12040b1b0a0f120e0423250908070f1401052115090a06030210050717070605091902060f1e0408030417030c0312 60
    0x3c034110314286000e030915003010003072800b52500540c03080d90303140c00b83c074182d45d5809011400c200c6841c1d03141002880e900c58840e418422410f031b050204425112901c0c103e03009040c0c4861410302000301401011520100070702440c81c16035128191041003441e07251000052401d01c1440d1281040040c2c0d06e6129003001c01981110550b12045c9a0000c10a204460490065640c01588c88640d084000d40c18410300e108070310b820950300e40a61048000784011007000b4000c4801c44c840b01c5088050050855003441420100402c0c000d05107000c1e010380d50301244082040c01410b0469000c100d224800c0c082c02400e1010200b54102001071280c252002c44503500350a0307442d40c8840c14280d0241c2400d5965050b02e0040780065034a03080f030304001c4080150003401d030501c0c11040c08003000c4268800070032642722400542c62106009080b40c0100000c040711801140c803103007480125038111110340c182507440d41c020041d21030b9091010058803900c90303a10120464036903030398090000c02c04125800702c566 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 850126250 1250 850125000 850125019
    0x80d0f060e07082d06090a020d0e0309130203090304060e0607050f0c04060503010c090302060a0905030a110405060a0303090506070201090503060f0702010b010c0f060e0a1203020a02010b04021216020c 88
    0x100b5520215141c03107002c038801c1e008020b10390b00d038440e8400d10b003440c1801080c1c80300c0d000182c800d00300140240c1c0c000700d6242006180100c4003e00b20304842c0501820001600002524120381c5070000c40c102c08401404000c600e03508060204650728842c52191109114209075502890307500c40c81560140c6400109a8021800e10300c0c00e02d84501076041d07a5442070303140541c0030071607040500c03640c44039940c2e98a840c0f2000341503408201260b007182c100e40f400c0046c5207401050585042c03002c401e406216200c150540e000990410007942c0c1c000300010300809901c1d00801c00b0a270b03c101d40d038080318829141c0035914215400121015045504801e030548500d1041c440701210444030644140a260300030000c05a510300111009803880700060107444440c84a00080f070129801040c1849140c4102c40030800d03d50303210000c0d0301c601005400400d9010414051a907028040d1743c4030328200300ca00314a070140d0800f000000c5130000e0b200c004030810740f00000505500130890074603002d2008005821 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 850127500 1250 850126250 850126261
    0x4020a0b0315040f11120a060f0b09130203060913020109030602030c18090114060c0a0c030822060f1b02040516030f020f0405190302090a02190903080d0f060e 70
    0x40b02640340a146000701d00d08400103280e140b07103126442c4a144d020140310700e84068080c803e000302d11302401484103141e42e8200003c840d000d403a00306000b4014510f0094407000c1000030481010006c1c050b0079407540c0100b081150076502c0240b160792003092100c81b81400100e03030004070364956083c0c00043c1814800000d202107982c0302d8020303083c00e00a54044000d84000c000c10300030450702c00c0c49206081c038000010590103140c030201070300c0e810b07890200b202d40f81482603c4004401195500c1650b036030070001800440640007000300c4900c00340d42e80721008100e01d410001802c0d8021100740c60b0030400400410b407036002c1c5220300c00c2c5815030010003d000504000e88090310f03656422548402091820042006140141c0280d071940100300b10201c1c00c2600d0401881001401e000030a20780160017403000c001a5903494072940a0000c0c410010380795100b886090703c00b0256914400b042c048003020400008400c2002c5400f4064011008140d00303c01490103406000749030001c180894000b0200311 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 850128750 1250 850127500 850127521
    0xb0a0312230a210b2202190513120b01030303110c0109060e0d03151a040b0c061b09030a14010216050f07061d0607080f180a0f0605090904020a0b03 65
    0x200401010403440c81c43d6080303809464100ca85420980d81c01c940960071044401d03800e0403240140c42e1000c0005031614505505421080c0c0c2d41d48141c1003c640c0100c0c01c43e05804035106500c000e00000c1c0300c00c08060b255515158081c04051100408040e21154020035110701c41c0143e42c1054140b0000340020a00c6203044400340140b4605a003540c894244104040d070f11074018400d1100c02c0c1c8035040d9446042c021100c40d9403c643e120300c4a4400304100000b502c0c05020000c2c81110354060251085041c00d000201060080c50b414880241d4107002c0d40320181c1d0089400c0c010941d00092001c103841008000c580640500e0f60002c03481d20b00b0001c0642480340100e82482400c1e1030200fa13a5080e80c5400050340c0c13518001d01d03002c4100c0d480d440c66408a0070040d000b032007458000d41e4007070304042504900d05c40300c0d804003114180b80c4071407412001c0c00d4284460410090882c0e1071681a0b001e0400030010700038060b40f40f16a2140d9114004a0299100c100c551006071100d1002d00c0e54a182a14600 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 850130000 1250 850128750 850128767
    0x70614090f12030112031e0302030907050109050619140403030c050c031f0902040b220e03030603190218042004020412030f0e030610090b0a0312230a 66
    0x40c0418016809031903403240011812101e80540c0d10800da040d40d00304010b804031051040011000d101c0030758043d0f22540795482168410003007507600542d50386003401d01c9605048580c1d00150512940450501444c5d41e5030040d980b4464402c003103c954088075500c01c2381d0440003030203100080b5400040c003105269022116840180c0908110b0b001051644149642da040717000804c20801210001e0740034440441e00f08480c8503000030700100d00c01da013001c000341401c0001561000d240f0f40c2445040340581880c054052003078040d8014504500e00440800d03190340b0400c41040740c81640b140484110f41e5040f600500084482804003d40e24091801c1d5490800d80c01020004000c01390203d00030385000d00840381510001002060714981c0741c0d40942d561072140c04c4800a12507800e0035000140c4080040071700c9100c5104000a246e8584417a800444694020441c0038007105001400130410745080e040c146c284510789003120121107845000c60241c0c41650710341c90b10740050240341155010380d85 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 850131250 1250 850130000 850130011
    0x5030612070e3d0303110106091a0102060f04080f0c010e06130c0b1c0c030f1b090f050906090c070503040e10240e0301020c01021903050f15060f070614 67
    0x4500c1d0060f41c078002d01030b0303160f102074020640303599402080c000244a007140d0788120031000c002007070150301c41c00140f080d600c2c59460a0442e8466805c0c0b02040c0d03a040151a422184c45003072920907040c952621489403280300041521a01d0004075000808002d61000c00d0404241041d10701504111160f03007103412a04c4010b0300c103002e50450200c2c3c0303034406000700c40a164420f0582801e4808910711600544183c078640c2d81419a101c0c070640c08440306000d000400144c0c0f02000d103800c0c2e651000540401480c3e0803a00e086080c0c1e000501803600c070740c68001c0c0c00041c01c5540304501c1c2c3d680021032203240f15640d001041c034040032400150030403040040a014a80e07500c5008040e43d200d440c1c42402c0c0c01624844505454001b60754108127000760416a02c1242c0a0000f620700441502071030f0a9a20120390502c002e04444201004140e041c030545400c4004100d021a03130b414140001205864520380444c481c142c0080c0c0b20100c02d002d00c0440f04850341c444400e10400744400c1040316030003400c035403 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 850132500 1250 850131250 850131301
    0x304081b0315130209060d050a0c09051b0717040308040803070b06060c0c100e10020303060f011b03030b06040302040c030207061b0221070602040b19090605030612070e 74
    0x507040c100303074210b0014860000a120011031045076001c20032813142c081c1980d46c104410840d040041039080c0a08081c090003040c44d03039411840d0107004c0d0f041764401420050411100140c0300d1540103140111096941c001084166401260401060305d00c0759500090901d48009000261039001001a01e04035004200100d1035a4441040c4200c0784200c0341c0a980c81c0c0c10840040701c2030f01d0b00b44249402c0d0541e91900140a0b0400b10220700d88070b0b9900c038078401580c8040100f00040c80c10f4180710020810030300c0c1003010042e40344015000348895810040c103060700d500c1c81081ca81c64031015a001584c00a10500c405102c40101800a500c1a0415107045082480400081078600100004010703613030700919a00b0320700f1007001540141ca5500d1076000b0003c00219000c81c1042c00035102501140807581d40d01c0d0b002d09009241824094148001d0048410041000302d800c9410b49900c8841a54200704920342085114105802900620110040c031810b01c000d100d6006000b2048540d10071 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 850133750 1250 850132500 850132513
    0x513090e07170105040c05040c0207030221160602071502010f020d0504110a0b030105010516051c02150f0112020d0f03080106030f0509060403031e090b1e13140304081b03 75
    0x2c0750b03003a40e40448000e014818110350030416030506a003c031a50846030701c15500301036103903400640e0b41d8958161000c0048090300f10191321030410300c5850680c0c1e1988603c03099807031500300082e40755055403281c5070107030f0740342c13800d501d4494000c0d0444801c014030f4000c01c40d070b52021040310038020301d81507400792001203110300e4030001d0341007220400065403041c10905003107a10340001191164802030781c4e9000c040611141034001201002003901034070381396074112540358515100a14186200d00b1500c0100302100034444221016020581581c140d4044c00b486c41006001096440304040c2c40100080400040b40b428164499629030503241c0b269002d004614000e0030300d0055540950352000150824000300c1c00084c080d40c400101003a0094a45075400d00d0242d4440440703003a02d2081d5074514841c010407115a03411070048000a40d0300790101680d0801505010300c52000c0c0324000c2030703154000c2c866805c0035820800e0750014130441742101c903000445010a050740043d40d41890087c071070035 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 850135000 1250 850133750 850133789
    0x11060c040e010608090c060f04120606240c1e02060309010b04050c040501090b070c0e0403030b01030f1404111f270608070c0c1203080f0106110d0513090e07 69
    0x2001d29a0107100c0c848000c2c0402c040c0b080400405038000386d10300102c8d4408000004a189400441c03181039400b405000885c9803800009040482c6c080e02d1110441d080d8030050040341c1c5d00100f0b90b03040c260300900d80b042440c422101c1d00469802480020390300a138080108440007405400101d1101002e98082c050fa44505070800d00e9801103010b21408200e411400740070540b41c40c0058001d940c0103086008040307603691500c0040e504180d60640010380c40d5400801107503054007841606503504d580070800501e130340602e50524040648028602d00e210110800c2c035a84603500c400f45c40350303507001006d04002c603000003404500d02d00d858800b01c0b660401090103132990440e0110200c0b00320392501c001d66507441c94101c504c1c0c10074403000c481903c44e4010101d01c02004074402e04078580702e502c59201c1c5090058440e40b00400580c41401004402150b22042c1500441c0682c00c081007820180d44880344e041200da008600c64105981e03042c50064003515072800010f00c5411515080c44080401075903 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 850136250 1250 850135000 850135007
    0x905030d020a0303112b05010e0f150429030c06030c0a050706180803180109110f010e1f1e140702180a02132405090111060c040e0106 59
    0x9010300340026821440385080481d01903000a11500c0400320480d29040c0c0d4602800240484101248004294500c1403260690380388662170240c032801802006030319100700720441c2841c0c0140320405910700c1c0004803d10307407521342140140486181c81030743c0c0c19119105802d09000f828900d030340b02c1e05c20172001c406203003859011a400f0b070300e000503001c4c50b01c20307000003d6600b580010412243c0340d80d21300d07021022080841d045501d03136225187d8160f40f070070300803101045c0c402e0103001001a0392521500600184050100407003066098035014980c00d40940180e4200400c000d180341c00c24a410300c000d081c4001405148025141c84d110303000700c018050b41852544500042c20000303c0c01c3c60b0151811582c40c440075021162006000d40d803000d507042001098101e05680264000f0b4001c940290342c4d000501a170f4001d0040605180010f103200301e0078400131b8000080680500c40c00240142c410791140200c00d82d40340b40342c4101e801a08020150000c503501921416030300701000700001c914a0311 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 850137500 1250 850136250 850136263
    0xf0b060117160305040503071406010f060f020a110a0902040806040615081f060305011401090f0209090a0504140f2a130e071205070503150601080c0a12090f0201090503 74
    0x90810b0420007a10824000f80c00500c006030050700c0360310080c030030400026510340d03489c2c00c411019409020694036080103607030002490b030001010711410700f81034001a0780c00a1000c20841d00800511015904680440e200d540940c0040c640b69000060116203400006121405903204550070841c045117100741001d0a1614040d07522583c208440c0859030380345078807600400e96079000d0b00007400c41e07880c1d883d0740c21541c04004101c28000f600004000c40f02c5507101d280c5522011031402d62900542000040d038200c0020b050180391640c41e0041800e000880780c056014000b01d900311000e9580d903a511650b50356100c01540341406141058003410205155507415166014045000d05151200ca4401401d071640300403449202e16400022044081003070301000d94068405000101d06240c14503003805d18001d203c64822a00d40e0512400b0390780642c145922810000b030460b220507400d4412104141a590000e003181d08111001c418040c4642940a58a200343c945105c1039540700249600c1e0740 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 850138750 1250 850137500 850137511
    0x120c10110703030f03020f03040f0210030e100f020f0a180f031e0f02040501180e1219140a12050f07080c0a031409061006080108100e03070f0b060117 66
    0x4000907420030000340036480701e080300f903010305002d4103010040000307810b10381044405031a218484949942135003002d051692a40780d0601d000e208111460030740980e1414075020807404156038100c0c1c82e81c41c1074242d0592380e150410800d100d998050b403c00042000d01e039103440380b0217424100720010b49000290f0805040b02d82c0300c01071030b07000382078013403070312103003906840c0c180e80c00901d054504d40143d0395481410b0180082800c0e021000f11106079610858204000302d100316440741d039400200d0413201c815900c1c48151018411010302c58640c1c1210005a041e00ba801000400728042c07507511740003044d0008881c241141002113544c2d000b840e143c4040300780c6206010460480129442d003c454004020716002810081011081a210034484a40c1100c6800c0107402c08000c0c403031440b00c4410351100612a9140c01e075110b504003220503861f1502c98503500403190f6941940004204140103582003e50400e4291210440b681490024213a0071648180020407207000700a803018944410750150 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 850140000 1250 850138750 850138753
    0x60b15070c12080c121b0105090a082b1d0c0a14030309131a0307150c03110109031d15070b0c04120507080d0e0102030307031a120c1011 60
    0xd4601007000081040700c100a03240c5010800040d10711190420030640114030b0b02d82003640d5801b1064101c1ea1520354815004040e904040a0000c504000100d2910043d00140100d0b0385226682814191a588902807034804c0d860f40b03a5600c0e203200c150300001c07006a10014001c858200403c5150300c030013050b040702d81d02c007007407a605000100b0f0f2a1042d02807560041d040343d1400c1e44100000711080c40c1904100c50940d294000480300485c48011407034600c00035001890301604204c5440c04100c42d4110180400c8109441e2200385031041000c100c007a00940001c020034207183c100100b0b8800c010840a01c0300f51002c020719038906124030682040504118a9400c000c01d03661000c040b52005002110595420310000c54034503082d580c01c002d150311442c02020054036003400681403203212000c6d8020f002104040482c2640c010048070b50104003454002801e03121100044200c404120565410040b03856070180c4038100050b9090700460200d480000103410000c045070000c00c5c0c00040c038550b = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 850141250 1250 850140000 850140023
    0x609051f080a0b0a03050c12030a05160f141005010e0606041806081f0c02010b0d02040b01020a170c100e2107240506010206073603060b1507 62
    0x12610901401d9002508030700045280207840c0c0016a0200090b00150340d60740104050451600e45014440780c00045070002d1410715100c548041d082d0b0007000030508401d403440001504120382c4820219415600c081e66090101d100c401403070391070100c0f084407001107150030300204552458040541c80744400902da20f1509003410769a0b00005413011312594525215030002c60109000d00c203c1c02c00e2000c0342c0d5156481062252070380d060b14030001074181503924120300c070071b01902c81d002000c8100c2c0d0191408500c001c42c1c0c41c0100c1c940032030004060200742d54000f90011000500d002400c24506020480e92400c0b00c5007010400c6540f10203880d102c2d940184030059000c00c82e5400048a011000001420140a61507580d80c07441f103003420022030030704540c8600114205224040c0c100b01300b840205041d280280c030203401a6421800c0c1c10008440160500242c03030206940e590386003040090f1180156645409005840c2400740103102e80c0c01000100c2c980d80c0030105032600c464120703c15420 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 850142500 1250 850141250 850141309
    0x40b010e090c09011e0f09020304020a1205070b03090a140c2409190902073008180102161506060f1d040b0319060f020f1c0213030309060905 62
    0x24039005022105c00483d8145000090703003a11145000010080744001507920328107481040811101e541003804071490b416145800f01c1c5000a40380c0580b03142030f865a64984500c8485072406a8082d401007c0d440d041c00e64040e601404151109c2102054500b04840da0800c0c0040011080c000e469611100c0d0030b010041a80c81d10724442d06010444d52110f0340000d498250200c01da82c0900400e8840350f070030841404074400258003901c52000201c48604c5040701e40d8800030203160002d0440d0321520610786170b0501020080d4101e236034501c030000182404408030300e0900b507030001400a0f078180c030f49019400110540640b604903420304031aa110034844551307226110320842d10720406030b0440c5d17650003000300c103490400c025400340042c6081c1d007500080c140ba081082d14080c1d6060000f840c01404000148030050040c1c840445d0390380100c0000818002c242c00c0280515140074540310740070440001410742040d105c809694440da80c4603c400d4603082402203240d82555005090602c0079010702 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 850143750 1250 850142500 850142519
    0xb090a0902010c050f0c090a020306010e0d020406091409010615050f0a03150303050d2f0304050a0204090f0c1a16020a0504060b04081009320105040b010e090c0901 72
    0x306600c1410414011481500c0707242c0743c030603604040030241d8440f0340984401d01d03000c41d59503480100301400354518500100000d100c6558000f1590042080a84200456843e034110501421215030100161042c11410000100c0c0c241c03030900750707540390090120f0540703d000c003041500c1d4156105c6511742110100300c94601d40c0a84e05980402d591180300b0302002001002880045000b644c7c1d81d61140d41c0c0d01444022141100d140d40c1c540011281540b45444044c0301005104084982040d1680c0c1d445c1085414075010381b0000b540b00389450445001c02c4403000c5580700e568000e40c066540d540e00d8100120401d002c00c1d0190850b030304180240302410140070740c2c060401c0c1c40508a5040b0302d83d1000890244e441542000c41e91150125061080940402100350700300f034544428440c9050b95122159a8200c030034200710700484102480410841352141480f8106085000f0011850a4180703007484510a0103941088031064021800b1101c0002d50b4165a41e8014000040c40c1d113000143d4 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 850145000 1250 850143750 850143761
    0x304030816020d20010e130905030c06042406060c0f020f19060f050909180f240c09030d230d0b120303090d0c211808010b090a 56
    0x41c00c1c00c50071004960010707114002d00c94401840b4104040c04019020300c1100244103441c1c107241084001300a1101e243e4510030a1119190740303101c00034140c00542081411031244000b180c00a1180d40240010412a0b041d061440307030780301c6d203101006414441400c003641d503107200780c500141400f030741b481c0030415070807200f1103041c4000d080c111140c2d000360200b00600c40760f2180441100c10070340e0130804160418004c004518041c502145040e0554000030a000310240046d1020742818810130b185440c100041c448104500c011542c00001c07290954074428940080304480301001c00100321550f0040c4140c492200f8018058205400c041000301d5480400c2800d10302285800c84451580507903007401420380f40c0c141c10001c100f6114030310500080460400d0802d9803a030040041150b00701e03000c6100030203104549880c1018942a05250b22004c284d4041c0740d440400703003c507103050507401c0b80d044d500f0b000180307150407250396981240f03c1c226078600c00d00581100450340082c600d0703010365028 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 850146250 1250 850145000 850145017
    0xb09060a0c02040f050a0f1404150b0607060507030f06141201150806061e10030b010c08041d0a020901020304050411040b0708040e1003020d0b0702150a0209010905030102090303040308 81
    0xc8456101c4580008090310003880d82002526503440c02d00c20340e0b00c0039028180120340304034000c2c0404c0e03030350340c02c3e180000e0802003014180c40303854480c50480d1519504001a02e02005240580b108000d09006004040030340d101c0c00031074134010011090340020701810342260440e14412101c80f07200000e002d00122004d5295243d03540e9007129907501084001380312701602240e0014203841c6001001d1102d035030880c40450701112a0307003040800d15a2002004401c03111140b601149450044006903004e01d1100c400034003e080100b40440c002c1c29441210080d40c2540c28168000c3c2c61310f01c1c01404070f01c5811130071401600104800c1c011410550450011b4002c80c1e80d43d1f601e0716586400d010140c0d0010750781103424183c001803c100b0211b41034065a04080140c0d81c3c10303001440d40d40001d40c07100080e880140f04551040000f07480d103009000c1605007242d0f0141e4000507162000309103000f9401160928003041d00c802005c546824144240c9a02c03a130003038025840d060540c0c6407222180c00c020a03 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 850147500 1250 850146250 850146257
    0x160f0501050a170a0204060e192102030d0309030320030c0f13030303020c12090a120218070906180e0601031119030606030f0203060d080a0c0c121403040b09060a 71
    0x100ca00e45201040703c1c2500c181d0443e940140c071142040710080c011429100e0440c800c4e020b41410058048001d907d0108591400c0072892442c03602541c1510803104c1510081e5041c040c603c021700d6410742641101c0c82c00d41c403a660070400d9a4201c404542074a24100b07408a010009000140e8210b482e00018802c0b15401c0304503a050805140340500508280c0d00100d001a0700864080c052030f204010300011034055003c01424030410a000c0354201c0c02a11640304000184070340d842c20340d214440c14404070b0209500112041c0f0b401c54000d0000e58981c45000c0002d00c0d084520b240203070504640e84251030010700c0640d015202c441c0110040d100c03510040d04292410401e07034403c90507000b9072440c18501c1d52000718502e4034240d000b40031104600c401d584c00c00d0040041000c2030b55141307a5102e1f41503000351500c1c8c940d40040c3c421030f0080324400000f4003a051105c00400d2012803881603112540c0b2035500034208494441c4401d4580c0254450800c0c40c040c103002c911b549280100c040e01c8054000d1a = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 850148750 1250 850147500 850147517
    0x1080a0917120c040305030904020306041d010b010f030b1c0302030408031308060a09030503040f0309050310020318070e01030809151b01060b031e100503010e0609160f0501050a 78
    0x1122035401c0080c0e001041100c4900003011441c0c800640c0d080c9034000d8412034031078201480c41c4c44c2c50361030348910ba40305445507a002002400590f9a0350002071203041008201060300c01c1c40045900034000c0203a040d0105684e14451030400b4403c7c002d2400c1c48002401c01c06039006085107034018a18220340440950000703110200c0d01a0701080a0180400191000b82c021031404844509200b40540354111443c02e004c0e40c0c1001c681c103d403ca039001903010440d00009015414203e07001202a00300d5941806000b014081c14481500514040c1c021050710043d03982c40d4221030343d034400b07441c4503456015030f4820040002c100b03034401400f18117001404280499540700304159940d400051411954000d85100000c210800d11408020b800b036282c1d040d203503040003a55002094001c00580d0040701440740010030030040d50551000400d03000d40207010006003e0070840c0c82c0d079801c0711008881d00c1349414124030701502400344000c4a4011084204990410004403280e03400112400148550203 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 850150000 1250 850148750 850148753
    0x60112150302060c15010608040b071d040c021506040213060813080d1a040e12130e090d11121803031306090503070611300708041a160201080a09 64
    0x2030000702071451310304000d000e0240b44010103c03004401a0070100800425000b0000050308500010350003005c14101803118144c0c2644420904902e030b521140c000e4200503c0b0040182c000070f48000307081150000c0c601503507030201444200e01500030000203810003010200443d901a8400ca03410100a4200c400d60105a0716080c00316409006245040d9030340c0c1c03040741080750806081080d4200116401c1c02140003610707401d592044403001000760301e04d002811041d07103480751807044005c050704600d45004d840c0c000b4009499020b081c0584020800c054011142e15002007444031110b6070741c003400390034034006145004c48103003202202501403104010407401c4284e403601c00e03001498a540d0303880308d0700d04150600d030500465500c07610511414100160320403002103030444c24041e05003910400c1d07140fa444603d5600359480d117460011400011803606000e00e0303500030001c0d6860003d0b500d04400c4a0820b2140a100e9a1050104810000c81040040d0b22400d50f054021080b03450100b0554000d = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 850151250 1250 850150000 850150009
    0x181210050405060402010809160e0c0c070312200d120603051e010c020a0c12030c0c0b0405101103071515060309140a1703040320030705060906060112150302 69
    0x5440a03502c0354003c0302040704540e0f000802c507a0007030005001d05206d484484003001c804806000c2c1031942002d03440080c1e01d00380d0000030f4608100e080401c40300e6140c1c1d01e040003165150b4081c04c05000420161005000404070103038003101444083c005c00110034000c0003182c0c1d8807443d030351803401030fa1500e80000202d10108800074038a00c50390660900d00c44840485421500105000300a54020380d1410010440f003240140c1110220300035089501000e28080700d142140c0740c0018140040c1d071001140c42c8168001038405d644041c0c0c2c3c00c4102c5034100005541f41c60010f0088070459204001150015601c7c40c240b203c0e8080350320f000f240e05800700004201510302038000c00006940d44410b441403264000b1401580004e070000380c1202070341038a0b20f88100c007a442440c2c48160340000400d08052189004143c078002102940917041c010103400c1d503c99015030070a40d060311401c00881c8000c10007240c15406500141c4907594a410703240003010240c8600691407048040b01000000580c44 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 850152500 1250 850151250 850151261
    0xa030609050c01030f06050a0e061f08040c0509010b0d240b07021f050f0f0d111215030606040f0204050a0b0702150a0f030b0d170c01060605181210 65
    0x40740018011584112000404560035288040386082c1004c030100665190403094005842e15606103046c16507a5001054940c1304251291404002400b0100522a4804030042c000c078466140400b040f41d455003000088002801280600c00e0200701d01c00d05a803040e8480319519611001a107224801d813031002c400c0340703807a80c840c001380d0500084207821898040204400301940030341c108107541d050034000308070b4020703200d100c4404900003c1c0705400a450006450064040d070303400b403000c1100e030b410320742c0700fa0407050345000c000039140013080305251b0201c4038080144000c0c0050209544490802c805170a611014520140d420040851141c41780a101301c094001003c000742c5e03905c91351040c800c0040301e030b000c0c1044090041c0071070105c10343e0201a4041190b151318001c90004110000200d81c510105802040240c2c107255240011484038003900180080c10020000b05503601d100795182d100b01c48900c046a07640c0341c3d4082d11780c585600c01d800c100011a0854918800a4282200301c81 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 850153750 1250 850152500 850152503
    0x605070201060f0906030c090b1513090506030f0c10090f0807060f0804030909050c1216020f1207060c02190813060e180702100c0509190608010905060a030609 70
    0x7511014280b000c203200400c03d1005180c0b000302002194655150400d14194501a072280c0b10384544011170581d5511b12800c0e080786221644a5980700720401c4198020b002d0700c505050103040000090340b030700e004191b403801e000050001c2d02c4001d60142c2000450289581e0203014030105650100d07188200d0b1060303801405000008003403150410798082c1c0135a02110b40c00f4108020001000b001903031184446007101c1e00070354081b0311070b00d0321003540109018100c1c3c50b50a0203600410400d04420180e06150700c000d49400340d4124455502150340c55150403244240c001104006940000c0c9041d0320200c1050060300c141c54000f01e41c500300000380d0030b00c228103403444007000c030303119140d144100940c1004005c242400c1c009180114040348500400c9184aa0410465400156214000e0000100c800400701041159040c03201d00034010380c100804407800b03101541203500d02813040641a1003552038a448040040e071a00c0b038500090540100125001a14a100000054070601810542d02d = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 850155000 1250 850153750 850153753
    0x2013020d0501030b01050a0f14060d1a13020301080a02090a0e0d0c0b1006270b0a0306030c0b0903031b010e0607030204091b0f03090501110c0a173406050702 69
    0x2d5245003460035041d1010f80005100f1140d02804100b22800000e041c030403541c0a64030800c010010707500051260256501c0c0212140c20b004541400c0b40443c4102590b60008540b6000b10000307850546040340030902480280da4030084913000949403004405a002a4100c40031a901c01d03002e540c0c9080a00242400c80841c00c8901003c00f04807185d607200b980003800140d00300c080fa142c5140141500650110681e2020384140c81d0071811480f45d008201405085241c80d0340c070800400c2c000c00800b02c84c4006d69240e6005d6501003a1006100d0840d8845040140118140310a604180d00400c0c0f860b956400715650316203150414010600809211342c02c940c80050311070b07103006102c8003511003480c582802c9030080011064a15044400310072000322502e000580d5811b40d02c2d1050040c2203030501d036585400003040521000d0000a44100d44c1d80c072403150b5820355034140b180900e07540903203242c0c0b5807206944100d0040302d42e00329144c110800241d0041441030404c0c1e4603900105c507019600c0d507005 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 850156250 1250 850155000 850155011
    0x90a03080d02030105030607181203120608160e041101050c2b0e040905101d010f0c18060909020f0d1b020606030708060f0606040518040308060108042013020d 70
    0x807440d0a01c8074a6000c8d4880c140140819030381d85060198043c4d600030503a8a0001407000028907115100c2d00d9064848403a04100460301c6070943c030b90380c904100b01e200d0003500c607407030100e4503031903a8044d14002e507413214560400c04c482e00010360300c68104541c9091181315a030340429232035441c4108054400c0c07030b1600c01100f2003104a070040010a4654016014504003403044000410005142c0c071581c4048c500002c26a2650984440440c03000c101c0030784030740c00c0040b246820a069404107906040130346a084036150060b505011280d0b0511034200806c1502208004099454000342a0481b199140c0c81c40c1c103a800110404070b800301030805e448648450454200e10f50100005a00401e048006042452405410030364405008082c03140101b00040445c50300c0c2c444105981c0a00b100030102c5880e0300c0c102c0b212a01c0c10404039020780c0015a45400b2840c154000e2441d1800f8035040901c0310358180c030110b510011006c0708011907411007628108680410300300d101418194a04010100f40c = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 850157500 1250 850156250 850156259
    0x60a050714071104050402011e08011e0b0403030311090a060302030402030c0a080d031d06070809190f06091a13110f030601030b09070807060e031014010b090a03080d020301 76
    0x403001c401d00c0390058a2a0410400d80843c070b503418030580c1c1500c01c440110b003540d102d100403911546034000d010501c141c03200d010301c034160b00515414180c82d0040507200d4482e081045c01c80c03469a030781c490500094801c01007840440d119030003890007120711082281c40d00040b203012529046140e0302c01c400095011041c0001c514050081002c00a012500141010f0510030146d0300c50756803107051780030b159503005140c4a2a42c0040343d60070105000d01602c41c2460001800b07403448070103c032141d0480c0200404070f010024100411003900c1d80100c103103c02c64402e81d035100010603103a2000c4d91620482141d10308080040c00b6014810f407100540c08604203920b1400c0d410034040e12940b18480c0c502c2d0310751510036403400110241105d80003600d1582503120920310a04001c0c4542180c2d41718001c8900c04940701d60000d144603480c01054040b501c00282c407010203011030304400c198501d8084000e00400c800c0078400082d00b9441c40040003001180c4d520f44d80c0d0201c03503011494a62a2a8002c0010070 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 850158750 1250 850157500 850157507
    0x102040b19031d0d0e030a0c06080414010c0905010f02010212040602040603140c030a0c0909180c270c02030918040203010506190e0a0915050103020901090207051518060a0507 77
    0xf03251403000c0721581e0300c1d41c811001d1140c031a002080c580701000321600c440c0c005035030b04000715908160480c2450010507240c905c02072583d20b00b01c03030035990031107a01c00c1c50320742c03500500c1085c0c00701105030b036800001410704004403446c10101700c1e501e007199000c0c82030010414038501c0c0c15010358407070400140e0300e5103405400b0f01599060318488200c0300c40e06040008110301003040300d41c0403120810006902c1d00303c0c1c00a88010404c1d401213440315103410462465614203c4480007450f019164501c00d07036503150300b400d0320101702100c090300e007044245222905600039004000302a80c0d80c0140c0e41024241004505400e00c5d038614225110444c0051005600302885880d0b04040255007205c400d9214501d4030f8030300010792103540350b12044000000c00c600016072143c4113440d0b00649482c211420301c41281c0c090725080c08141d214169a400020780150944203c03014241d004028001c070019003042040040801016070101a10400882a0141050288074400d000803000001d16080038840107 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 850160000 1250 850158750 850158761
    0x3111b060603060a0c090308071b0e0618090c0103050411060c031c0b0a14011b060e06070201020c1513170310080102090a0b03040c080d0e1903030c080304050102040b1903 75
    0x103040c03503e40b10380812501d90100049047e284c0002c1c50b00d0395440a440c102c00c0c0702411552510b1030740ca1504001c03031152080110240610350888440c068202d81680745104031205543d900d000303501c80001d01001e54020740041c2e81c050300a104400c010b48110010452551122a001c01150000514400c2c1c4038000f009403280c800100d01d0401a1b40c40c2c01c404500d0590040c01400d46510b1010078a00480e0b1150000c40300719003200c00390404039141d0b440d10b203000d807683e00f0407c060f1b4060a000074035010b105100340c80c80c1451240c010140d01c0c0c0d608108914101014025000843c0d544003080089021318107185003c00481c010035a403482c10741c010070b0001c40320350407080b0076074010401070032756581c0c100c1c10302c0580da006050165262240d2030100c0248015902c0b4021b80d005510300a01d807250030900c0c00350314100c20b4855801406044a10300c8003000503000040105244e13180030b401044410b00690f030b02c50b00c66000149030540fa1400000340350802001403221000030710b80c164440f0340c5401903 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 850161250 1250 850160000 850160011
    0x3010e030f0c071401210e01150302010f0f1202091512011a1e0901050c0a05070f09060b1207020a05070f0510051207081b030408090909120a03111b06060306 69
    0x80050b40c00d44000001c01b4404408210507810b80d400c40c48001c500c80703a6000030003825422000700621240c00d200341007084041e00c8103a002c21071082188031a9400b410141003030101660364440e01c40360700e51289000750848102c2540028120712070251284200005012078800b580b68002e4562420345420800d150301c0f00c3d9407480104c148405e02c201000e0481a1550b104114040da4482c1c07002030040f030301070285038010006071081403503420500c00e01003056010f880c0704001800329141c50340200740039216140306454600000b002920044c00c1540100368111245e48103940c401c950b00d8a48500d0041d15401415003102039010070881803804010f180e203400d40904101342070440e01030400300f0f0743d48010420028002c00c240081e544440694030042d04040020f251622400c16080902c00c540151101c103004460704000b00c5e499503070000703060090182d8a0100d034a800c0c1c02c048118050038140c051705d1420ac00c00e00110700c000d503c90300c50b4030a0441d400024400d51074800304161030038070301404 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 850162500 1250 850161250 850161269
    0x180210090303020d0804060908070615080c0607080906040e0906092404020904031413050f0d050615060d020a0c110901060c0803130813081002160303090203010e030f0c07 75
    0x40c1000081d40204181029105030b00b0880040d40d10f50415002421042c600102010000a0b0920030020517510582149504101a6205075100e08000356078150460036182c0c800030503c922000207080c4c00c010050018003500c100d0911b951401034400440341a07403040515000401040360a6400f00400844040940c5070720144400c805002c0d040306001400c082c0c01358662a00040500d4000d446403034059030b061603200e640d10800040d60046d80d1042c002c40c0d100340b8084104071031524146500b41100303500103020b04a580c86010300703214044041441a074104c0b4083c0514030907a8401c0c4007402c00400192034100d191811881c01146510700306008900c14201c0b0030060041e80da000e512281620340c003002031030f542d8980030b401c40d55905414100600001d1700003201d4620b4840003003064100d400c0401120824104c190400c01a40100d02054042d001c0302c0403028041380c840c0e080b10903542d0002c0d000003080c000903a22a4219440020b410404c944001504841c4000800882000f02007149 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 850163750 1250 850162500 850162517
    0x8160f03080915040b18060c04061e090b0c07090603060605030d11060c0904390201050412050a0c0204050901020306210735160b090f1210180210 64
    0x2240320f1022001400c05803144414000180c0004585c40384003035103560010484109240024910120380d0142c0200400900420440d40816075441d032440902041901c40041140c28246070f0145a003040b04e40110610440c0400030307850403184074102c040d5000c4d0300041a018101402d0518008182c4030101c10060800008030342000d0100301d0b990003062007211030359124460f40015010340840c0c24280c1d403c0400d5540300c1c91004007e240340203102c090b085641c24103c3c0300d0005034200c0740c017150050182c04d141a00c132001daa10a4000f44000f100340e0916120914007900801c0c111002218241d010769400024400d40b494000c003818450402101c4488407181c06d10741d03072600c9a8961060001256034480160449401c401545203d03002e2041803016001c010310b162075a80c8185c0c440c0321440f006115000c904c0b03c0a04044803c82c80c0c0240120369281040350500500c40054070321550b103801000c0b55403000d06841c3c0540450b0040031003681e141401030340108100070324a581104284070121 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 850165000 1250 850163750 850163773
    0x1020c01020a0b0604060308030c090102010b2e090e0405060604050c090a050d0303020f0c01050a152601020c0d1206050105072604090c03050403020f0c06041208160f030809 76
    0x20300c420020783c08054056951100404200504440d40000304505008030800400d206914090006800e00764002c1c0315018692040c440c030208242d032401c61703500c10300c0c442400383c20913240d03e80280c507054030b0004455560303178010410200040d1800ca0b0590080000e1196a14045c000c2a401c100603411503450100c40c200044d000800d41e2080c140544002e03c1c1310414540294143d500c112002c0c0034a40d0b45101d00203006000f881c00301c8d401081d81d403412030307940f415141846c840c4007511190000e1603401c240c4010b0f849401071170301840d00e000d503400b0402102415414444803102010303580b54203074081e1400d07244a0554a03160441c60400005001000210380c08580c50036403200909040941303050f80d10300114262013641c201e0141d2604040b01ca806243c1d00d41e0040784694007a90075a05456682619261203c860f40b5142d54084420b10040c0450681e1500b0700b070406200710781b0a480e000007140000d604440e180026120103d20071910400d268108140940c0503070300e40003602c010400c1 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 850166250 1250 850165000 850165003
    0x70c0e041118270a021903060f05010b1209010b0406080106030b06060c070b282006010609180e1501050108090606060316030b0a090e010b060f1828090b01020c0102 72
    0x60200c0d00395483d24800c007280c10034000f05524940140002540110002c8482101e0a49100c100d91941c80c080119030090107910a150580342c0e07820009150020b501c041a00400d00504000801c0d5600d10011400755141d205904c0240801d10000c0b554500d182040c3c102c0b071400074030960050100b00311050503441c0120f6072606440c0400000c84d1940004c081c1c0072705103071411642c1040710081303011142000350000d002040da41d5114882d070041d03040320243c5545030f01d020b2042001080451200384061a43c69103040301c03d400150000442c2e030a841300907803800c2d000900e0603038000310b4080103014a590004609034440c103640014910380c10b04001180c141d00c0700615041801c0d101400e2110498840d0f0450944400c0c002c1489140d9900d8a4110000b4044800480c0c400d61174054000d140c0e045c458180c4a089681440103070420b1261400401d0718044101d4007a4403101455407105143c5d0035040010f07100b044824083c100c0b6080c401114101d030004110207055500901c078038106680d0 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 850167500 1250 850166250 850166281
    0x70b15041b0f0c050d14041805162c04021312023a0c03083c1602040219050a0201060905060906012a0503090906010c1502070c0e041118 60
    0xa82e03183c030010241b181c4142c00e049000e5a080400d0080803032402e0001c2c1051500414090325807804101c0326101d02e01026a440314168000d0f00b48010004840340d155420799401d885a13400103440946000204896903d40451507045001d040c185d80c0c03162015410058110825603041504030000000e44501c03042e079070b504140b4440c84003107003075111404200ca50801040155406401c0c141c0300d100041250101c03a120304140d10040c404c083c0704880803000c2c610040300080d450b500c114502800000b585400e81400c082c140e030440d4007005070780c000b051100301c450089030080d03803410b48400384034030000e095a20590115808904250900c03540d075488032952030f0440b909081010b44910b1140003111881510200080080720010310711050001c0440240b01d00c45003240e440800356a4480191703179102040401504000c40e82e801c407070103a0f48550080c42c11a000f141c02c050501d0b940e51281c10414000c54040780c050100c040051081c3c10070480c1c1007509800c00242c24594a03010310089101c00 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 850168750 1250 850167500 850167523
    0xf07091a091812031303020f0d0e12010e1f05060619050901030b1e030601080d0c030f2a051009211e0908071703070b15041b0f0c05 58
    0x55004610b0315541508001e00420281d11802081c1c40746042c0710002c074035910003070056001d4025000301d1100801c000c03e1f40e110328003c1352139081d0a64408400d001c0170b06805d440c0d07810075650310b402603000001c0030096116540c000d5800c83d1901c2d0304406811094540140402e40a07200500c4402260081e420100201d00024078102c0e40311341080c1d004901a1012102e559008141080c2c4071400c0058662181104003090f03044a01e0b503682c0341800b035582c01202605000181a060004d00028800c4400090031080d91409020f154256000703030180d1403005250440703200780700e00c0020030002c00780100c50003088850002c11071040b050312200c00d00580112085000c0401c40b5215404600881502500040402d401c5800c1d450720200a00f4000840c000c03107840c0d124100c0f0008040d03540d40500c480c900a41030140d8101202a41c07800f01d0400087c0400040c1880d04d5490080ca4072039100b005280c00d031050000004050a54000e00a006244c01100420004029080201f040020703484000d0 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 850170000 1250 850168750 850168771
    0xf0f030306090c0904141605070b0117070803041206060819081605100902010314091f0204090e07031e0f0212030c0615100801081005180f07091a09 65
    0x43e52400321058651041a014542c85460215403541002d0105225071144025182040343c02c0103040c0195424040c00f0b100400319420080140f0806002c1c0810856024000c011680b00035200d114440c15a0410340044c83c2d0348601540c200c080c008103010b80e2000309412005041064042c05d0529103529400c80d01824401e400600000301c150b1401072100d03510381003c2a00c400f0f43c5c01d910088090300c1c030454141e000a04222800004200b44218107008881800c000d003880b031480c00c000440c80f825038010720580c0307509200000309444140104001c0301004000740109500350301d82010010b1840e05121100051000308500040c940c00500451940403600341c3c0240728003c14191562084c0c5502c1c01c480c2c00342038180207001640114cc1240688103c40c90030468640c2d04040300c0704182449104616032010301d00440d10a00c40d8029a0001e8a135080d03d0080e2240840705172518005680140403907100c0d0b58100304025082c42046915001880e0202140d480000090258200600b004003034 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 850171250 1250 850170000 850170019
    0x20703170730050915040f060219050a0f0e011d04020d020403031d100503070f0c12090e0a0b0a1509360e031b070806010e0601020f0f030306 62
    0x1e0250b60349840101e00c050888419400940c441c079864041400244001d50600001c00c61039a4081030050b001d00c906a03080350320f90f0320354654401100c0c0346d000503210103130308010100603c1c039410035408e23041c80390b40c40c1d2694420311488014590410341c403005041141c410f070102d015a03071008050814040000c0f03c0751201030a10300140003031041c0c45c40c46803040e10008000080541100c0c2d81404021400b0317242500862100034004054a841141e0340000c2007000000d5540d40182c0c09402000240d250859440202d56101e0303a443d03036039900c00808905203540800c542c8110b140d15a50000c0b034102c085c408400d40502045c0481e0140c080c000040807010301c01c0152522681d100c0009100d181080400c801030701c410500c442c2c0741c00805a0b0241c840100c4d0b190b6082d400d000318074003020990002d514007039001e0385055600c070b10400c540702c1900070740d0400a001302042103268041e1950342c0316a01c040c28200000380c0f80007000c8003130500d10b4004442c14138090074003000380d9a21031000d0f55034402 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 850172500 1250 850171250 850171261
    0xd020301110c010e07060f02060403120e0a1110170c0a0212030c12060603060d150209061809090607080c090f0301140103030305150604181503140c0402070317 70
    0x261140c007500404020303000c00d404031800415000032140c41e06a000380c030030b0b058443c28112a00c114640c8842c0241e4003507000b00780024841e112546400340800d00c009140e080d0385020130705260f010f110079646007640c280c0c848003074940744203580c01408031414121400366405280400074072000781015000b22000c1516034005000380030071720240504240260f502c0c0340408561400390450030b0550038820090000070001d04000084074060070008011140415856030ba6200f00103500c040c4450207a001e0140d00d02d203840b8240070f4218482040085c82c408100c51041c400d121400500c01066540300d1001d2000483c0c102d07201c80d400401e50400142c0d034103111004580b400ca01801610740561820010803000101036a00d03a0582e0b1007550203008070784030810b1211030306007401e42c03c1c0c0d8060703802c0104008034614030450814269881001080c500d6103031120b503502660581c02030b2040d070282002810a000c0500802104000c00c94085040c0846900c00410800c002900408a800180702207030 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 850173750 1250 850172500 850172503
    0x20408060610020106120305030901110306010c150e010204120501180b0f101205161401050f0306040914100c08070e100e040e030a0e0d02010c0b0a0e010c090305101a0d0203 76
    0x805440c0420f103a0b041c818107490008c20300c5c0e004481100b8294600042c41c0c1c6000856400c5034003070702c0140d540784c88004464903452045840a14640c0b000c81c0d07540360680b640d840a00280c0010700c1407440c4140580c400d4280a4291802081c00103440031045840c0c200040c0e114003501c0d003200300d80c40c016015544143e0900c0a0081503009103203c0d081000c1440c041040018010015643c11b4201000607075031100c0f200b03031401da071142d22804500180607808858401e0030155a11840c020404141040b0580703c07a1520407d140c90109903070003034220020020f403c0d00800d03044101a00e8040c082c0c4c034010400900d070315441d1200901c2103044a03100302015125902c4411200002003041100d07003400e00d4400c0d41c9511016021020500100c1c90101074900b210741d4a0b0410380685400150140039540d51004003070090048041a55032240ba80c41c4001c00d01c1680f804d0b0b240c1c5e40700c4100c281d082d41072403458071052009045030342e0f05040407020700c0b201e034031484464164161121401182d282c030009 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 850175000 1250 850173750 850173761
    0xc0106050a0509010b0c281b06050d2703020708060702030a080f060d15060f0512060103080a050c030a0201020a080114220221010302090105010f02061504060e0a0f050a0204080606100201 82
    0x602c40602070030300c40c0b110120035a400300286115003c01d045506251184c04020403e030711401001c00c205210300002e010303941d00308540214400254100d94cc0e000003030b000010076180001c1d801640304c441d0030b00200c0c00801c80c82d81c0080d0f440c001142025071144000701040f40050080c00150f010344080340c0315464040203c0c2a841d40800428000500b11b404000203100034450095612820040065113040048010a0419030721000c0c0807107030b09549440d5020b40c40321042404000b0100300c01c4a404030184040e140360b44040d030002d0b03030717401c0821300c002d0507101d040c2c112000008501501781400d64614809000f4501030268040752500744101d444028054540c0d1882d807000540b0800c125030000501941c1030f41c0c4225600f904a90725000111903100d480c00305500580e0090001c1280c2c040d2000c1c201210300d0f001003001c501141c5405045c82007c10544100e504a51200304265a03040316001c3c0586c840070f04001141030034903215540d41d603070501505440c06010406e54008070305100f03400c00c = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 850176250 1250 850175000 850175023
    0x120602090402270402091e0109050a0803070606091e0e03090d0f02040e03030f0f060a0317030f0702010c050a03150e090304090b1e011b050d050c0106050a0509010b0c 73
    0x454844024042c03151542080f041c10400491158110a1a5140520035600d00850260402d5421030398010214961030300103200034140072043d04001056070b148100d402c05028450050341e160310083c5000816590f0300d40015251038240f2030248041c0400301c3d4440c0d044070130712002007600c0807044030181c20351040b03542c01034201c842d03010750106008517810a104c0781403007a10304200a41d950b4060f651a80410307180301180e6910700011400c010b010030a010740110000300042c0050755260748102034004901c090690201010003000310300a100340003240d001d4a00c0c0000d00442540000007801c51041d14880018966180700900c13403401030300b11200140c81140c45440d114200305000640d00c0c0c0040c450300605034188030b5114002e0a101d072180484140c503288030503203079446900545201840c070011070751064010080c0404a0b1082001000966558840d15a114103019402d800e40d001504201c1c01145074810030061615a1211a41114200c8010342d84035800b022a1504005031490f5 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 850177500 1250 850176250 850176259
    0xc050f131707060810031a1801090b07030e15190204030807050a052a04050a14040c141f0e1302190938070501060b0d060e010e0112060209 61
    0x250762001c1d60004a00041d201662030f144030315520000c0440300407009000003071500c801401d10303403481c803a084187e6403c81408103034180041c20002080d4216281c1d00000c2c3c07001400b840c1032000c5140c046c0300c1c41969186401c080c040900e082c0d4000366290101611000601201c072030080d0744500e05606480155900c42c5065a0719100c0d0f060041e40c0c0e00c0500820750341d03405200402c20b20400d14601e01280c442d4450f0300c0600d10b1107110300b0031000b008004e2035840f58030f4641240444a03140c801040d40308901c02c00d00d00c03540c3d90600844034a070304140c140040c0030b8212030080c0f00617600d079041100c4026a241c54894140917080d1701140c07491410100c8654014004551a0030003d02c0326102c07514800203684103a4466551101400d00306030400400e04007007407651403207102e4403109250b04052001e540441d45044090380c0c545084a4883d48510040400421b008182420364028200100481d00c1d441034294100a0304030315000040c8508001c0900007400001040b1082d0140e90320050003c1 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 850178750 1250 850177500 850177529
    0x1e0609070503061c0c060908070324090812180a0506010e100314010b09060a03080d0515061b010b0406031a090a2f01091406030910050108030c0601090c050f13 70
    0x94910100c2d000c50060706c01181041801007a12000040c0d071001b2290422880d0039070b06140e13080b113503062401c40340a460321501c0e00140c80100b0012801400d4040c110410041c0398a403026140002c0314107000c11a900c0e0b00540703014004154000f4000c0d064624144a07007005403218a0070742c3d01b80d040c40c2d00082005030900486140c040040d4440b00c410101a64413140c1035075640200a003040990200034113000090201141a605c0f42d4002680030580d005010b000c80b1490780002e1598014000f0317010309103090114800035000a018018003c1000e88050010354115501d20001e04010000a182c0c40400f90000d541c3c01003c120706003c043c4c000b0342403407402440d405c83e10748410100c000c076120b84c2c1c00d109546401b54810440107044540d42444040f00c0710000b0100000d0b640041c162000907c22491600c00d6010207208550007411000003c565601c0140002c40c24684164844101d1906d808480c98660360060104c408218000d048940c0d68000903805c8000c1030002d0300b0000e5202c1402 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 850179856 1106 850178750 850178753
    0x14070914010e1e0411070b0f0c190c120215190b180f010909020906010309060f0603111e06070303020714060f1e0609070503061c 57
    0x1403402c0e18058000b60001480c000182800000e880d009920228407490a481001101c0d1843c141d80c1c3e040c400035031100f980c000001001500c039907580c2c000007004000c680d07088034000140c6450a407000c4120341c000803d86e40b2142001c40f4581040d2503400303045800040c4940e05101180d01910541d500c58494000703020450030001d011030385814240555682d178036003440340400e00032407803800f42c80c048006070b04040043e1300400310302e031030104600050307210030b46a1030384100d003030801060591041c540741000b072080701e1045800c1c0345001004820040001040f800c0280c2c04c8528410b4208450b1074001c2d64102e605001c1d5003c6420084800020302940280014500461038900900e043d00d0b103203420b101d0b049801d0343c05652075104000501d00b004440c08851000101c03044084d24010011612034031000c0c24032800d02001000148140e80e4113001c120b00500402d64141e80c8604a = true := by decide +kernel

theorem cover : BRFrame.Cov 850000000 850179856 := by
  have h0 := BRFrame.cov_init 850000000
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850000000 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850000000 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850000000 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850000000 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850000000 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850000000 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850000000 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850000000 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850000000 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850000000 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850000000 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850000000 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850000000 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850000000 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850000000 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850000000 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850000000 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850000000 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850000000 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850000000 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850000000 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850000000 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850000000 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850000000 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850000000 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850000000 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850000000 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850000000 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850000000 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850000000 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850000000 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850000000 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850000000 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850000000 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850000000 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850000000 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850000000 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850000000 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850000000 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850000000 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850000000 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850000000 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850000000 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850000000 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850000000 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850000000 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850000000 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850000000 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850000000 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850000000 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850000000 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850000000 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850000000 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850000000 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850000000 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850000000 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850000000 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850000000 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850000000 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850000000 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850000000 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850000000 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850000000 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850000000 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850000000 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850000000 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850000000 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850000000 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850000000 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850000000 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850000000 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850000000 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850000000 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850000000 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850000000 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850000000 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850000000 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850000000 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850000000 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850000000 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850000000 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850000000 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850000000 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850000000 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850000000 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850000000 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850000000 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850000000 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850000000 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850000000 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850000000 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850000000 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850000000 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850000000 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850000000 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850000000 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850000000 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850000000 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850000000 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850000000 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850000000 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850000000 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850000000 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850000000 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850000000 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850000000 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850000000 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850000000 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850000000 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850000000 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850000000 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850000000 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850000000 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850000000 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850000000 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850000000 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850000000 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850000000 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850000000 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850000000 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850000000 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850000000 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850000000 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850000000 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850000000 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850000000 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850000000 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850000000 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850000000 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850000000 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850000000 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850000000 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850000000 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850000000 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850000000 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850000000 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850000000 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850000000 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850000000 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850000000 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850000000 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850000000 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850000000 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850000000 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 850000000 ≤ n) (h2 : n < 850179856) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
