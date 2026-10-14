-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2681
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T07:25:36.771978+00:00
-- url     : https://prove2.me/submissions/a726a66c-f7f9-462a-b61e-d500a5a7bf97

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 482014388 ≤ n < 482194244 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 482015638 1250 482014388 482014399
    0x60e0105061e01090803030f0907060815041e05070804150b061902160306150b280516030302040e0f01080a14070308040303080601120b030d120f0501030f030f080411 73
    0x104040184c41111090300b002d883c51001104000d03000400011a5000348039800803156099036039042103404080071100f07958220040ca80e0703002d00b030510b031300989481412601c452810402d6040407404480c0100d81c1c1c0c400007582101480140501004040740b0b00310b1340c2400b400a80c25000c04103c0d0b038031038136441d50304029625448094203071003805442e40d80c1d00312800c4c00d1103c598a0034510040c1581d000701183c6401842c03400104001d488086032904c0d03060026008403100c2c4842c0f4071b0040f20302d002588080c04410420000c0107800c0200d05c001e96842601c0c01a291403c01010940340c160080920000b01958001800074110000f0700703240e4641d0150403032103480c100180700781c2440410b5200610028000c05c01000b016003202c2e400c1d00c680782c00c0e0b0303078016400d050030f600d9415260125111a0103401c100342e20905548180c49194500c1c4540201052046d05a0b00c03e03821110243d0090ba072440a4012103010140e11032007900d84400700b071802100508150300c41024031041c00b22030380d2260 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 482016888 1250 482015638 482015689
    0xc0f06030402060c0111040e0108010b0907031e0c032004080c10020c27070c111905060c010b011e050334030501060e030a0b1605040b1303060e010506 66
    0x5603a083c046440004c4400d00038800c4052030b1070503543c41d030802e0080c0480348030f0440010480701c0701441101000c40c0010007460450711250000c0e0000c080c40400c002800311684003a02c149070060040780c0111f06155000a442c804920155000b900c15204208848030100800c0207140b000148110740040b0494032a921408041d00c242e280990b007000310303078011251400c040c17024110a0908500320415209124950340c58000032544c070aa011030080840c10210000102810548034000e40c0c041085084003005868400041803504441c07014241a9124079a02c0c44c2135a01c14000004802000f44541d0124a4013001500901008140d0300124060044080016410700764041d0f141200c0f0b510b00700d0300d0034400e000801411013400344402080b900d1140c1e41a5007070020304603030020b40040c40c0c42030726200c0074400707181400004a03140030030509200104d0081032450007022391080401915110070715514000003654860074010303440d0b03458502009101c1c0c480c00c2440000b885002e0b41000c04 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 482018138 1250 482016888 482016893
    0x810061701033206070e1002070b0c0304050a03080d0c05041206050403050706020c0d02060c090d0b10030203070b0c06010605090f040902060c0703030c020a0506041a0f091005090906030c0f060304 86
    0xa100321501c0c0c1c0019600303d0140ea42a1001c0415940d01940080c0c0d141c1a50051000c2800912800c4200c1500160b121070010000c1c9410400940441e103d1322041c0c07450207030707070382c001a0b400110754100f0740c3e004000007500f5804d40768030712401420240c5400c20350f017001e1a0040100202400c02c0010b0f011644031030000b0100361091080b16862a84800b045407134003440c610b142c0e030b500c0080b00c828025120b00c40c04500401040429514178410060207603100380c07065901e4a001010280091a40401c00c680100041e138050140c00d002d072426828854540a1012001d071401d4410b03800941446000c11081d111503e07002c84481c68100141d4020421200e41d2000c61550720078881486801d0040107400300030140d2001d02c400d02035008454243d0380701c0d141c008006ca01d1003148500d1645c0030300350b05001c1900024a010b0100c0c90441003600341800c000e1004142d10082c460703100c0d400284002080740d00352504a803e541c00c9a001c0c4c000b41000c4052102041c20720307681c1d01c0c649100c0c550210010b400c = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 482019388 1250 482018138 482018183
    0xe190206070b1306110c1f150b0a090605270d02041104030501061a07031803050a0605070305090a0b01260a0305030609070503160c0f060c081006170103 67
    0xc22076015011195616000070002c1c0a00c20202003200e04c20300f0000c1c068071030919241541d0a103142c50000d0b181d403003010300382109a0319002c0d03268042c49450f510380620100c41b80d480c40c1c00528003150515902d1925240c000c09000451f0000340902a040c801314244121b6010107244407400050900440104400000e00e41800c001000354011709220b13820b003510320f40c04c010b80300300e91083c402841300944800003c540703903218a0f4080780d084c1050005e0b0300464840c1040d03686003159503006200c45600d80c1c44041c1001d00500c0d041e2219a121030a200e41a0390521a0079403060040380501741410b008c0c1c4e907186c1518010704c50460540451495801c5005040d00c41a600207080d400f11520006145400f410681003180d03064410104003000880e000d0182044901c185e001400300d0319044500d820030b0320b024075050030589801c0106188040020038500c9000005c104507200d4aa80d03103030001003071a105c407081c0c001008000e01c1c811031b07501840030b4540450640758845981890004541c40340d94 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 482020638 1250 482019388 482019397
    0x30610030b0910080f190b0402130230071409031e010c081308040302090c1603090305070b1e090f280b040e0f101d01180e190206 57
    0xb40e015501805100790b100700e0345503400072580040140e0310b90104040440b5210b4444c81d9030301961101801c00340001900c400c004070761046c802006083c0405603944c0400c1280c100f82400481c21210246111803000307401c0250820130440020f404282c90907120080407140c401c44270346119500410500c10564092000915401e811401e5441a10182c0915030103008201c003084003007881d207800303c0c547c2c10300c62400c1c450154000d050b041c42c051950b8244141040010024503d00e5024885200e030020200103a4101c00d0180d83d0b5000e0f09410750400342d062507080d41c0854109c2c40204526018401e161880540000d04250040c0c1ca803104480840c00001600f041150b0041d01203000c0004001ca8030b600480148400c2240168640c848510071030034440c50240d0401070000f280000c00c030b4100440c2280d407118815080f0040c940c0d45034044a06814220340500c921089003005009454000e0300c2500350100e4100d007130008180400c270780350b01c038011002c002c42c1c4401988030b00e03020f5445000464 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 482021888 1250 482020638 482020661
    0x61002101a1201020304062f0901020111030c090a05030d0e0108090304030204091a0c090a03060b040b13140a0b0a0e07090e07050a02010f0905060a18080a26040803061003 75
    0x40c071002d200d4411038000e50086034210380c0d41d0310b40125410005001c56200d808032075444200300c024900703142044d00c035404c0507186070704541d01c0d5100740e206070019801460150622138003640e140c075550803c1121a803501d40106019511401031440c066502c0744892585820a0920030690345070032400e18114415504080c2d00700782070282c544208120755540d4900404003106440640e25034248106441c41050200b591003001c424090000c5112580314102910300100002109070b014008a901d0041c1e2a0100380240d070303110700c113400726851026216440586100208600c00404002441d80c0c1150f020b0850000310040010341000e00070995200900341e14045c10006180c001c60042580e0301944d000801542022408032103e0002c1c001c1c0c1c071815901001070511951a681940d00400302044d400c400c5151911611000c20490b40080400da003555981d00d014000031014132910102c40c0d40c5507401c01c070514040001048100d000d40740c2000c002c980030a407610240108901922024098 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 482023138 1250 482021888 482021899
    0x40b0d050604050c0316091e050a06020a15020a0507060c03050105031510140117010305010902010e06190f1403400f02040902030f0703020109210f0f1502040e061002101a 75
    0x101340740f0480440f20a23044840803602c000d0741703980b50710003281c843d055000010580440340401001c00003894000d002c41d05140d29026003070540540f03c250507154241c01c001c0c046540d400051202c1e0600344000308014100c00fa00c0788450078603010113405d240b10f6100303025207901d5424404030143c0c4110944a48809406000f072500d5850342000c03402064000400c0f070202e13070b0b03400340301c43c0c523007481810f4441000c0d81c0d088415620491020540d040c520415015003001104502284114440006540a41c4420b60b51905000d005000e140380c856400c0307a02010142d1089058201407034011480200c1540040044241c490a00c0072a0180c0004034000358103019000600d038100b5000100303d42100c0c001d0b1303200180300303545001d0140d100759203d14420071a400910510701068400c414444454400c294402413039942d80c551040702c2c1c882420007402c01d900001c00b001110305921a0680140782120506941031491340c000e540c51550440220403a6100c406502d8800085c40b1184a24a0040d01 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 482024388 1250 482023138 482023169
    0x21306030b0a0605030d0c03050d1104081b030c0307081c030b0904060f0c0504150c0804090212010f0501030b0604050f04090b161211041a040b040b0d050604050c031609 74
    0x40e40b001070300c5a8060303180284070702c2ca080415070307215000e40c280f002c1d09030300c40515007031008550b000a0035240e007101101100c2040001403520040280c0d01c0c204841d4070240d00e60109142c10541440740103c03c140c826030080c40107001b80800440d400031030581d50803111035944502d20042e400b810480540c01d034440049130070007003032003041d030410907084000c00003c09c800c44c00101c0075a030901a600a1a1a28812503410f01e03680707000b8944031406500035000b85040c42d0380c617042d00081c1d034070200308107500ba0708c0c00004122400c410307181d11000c1c01013400e00707001c170440c203401107111802680b04003446555000c4444540f501d4546c402000c45070001d00b60030003440c0c00c03e154032040d200700d80102c00241c00b03c079820b81200c1c40d070701c00d00e48800b032021051850546081061250058402c00144807030504110008807801e004c4000c20041007114070700c6440707055203030340744007180d00c020304590046082c003080140c2000c1120489078401341c00549090b0b014880e5008039051821600401d03c07030b050540 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 482025638 1250 482024388 482024401
    0x3083a02070b0604110a0c08070c0f0e0c2805121006090909020a030227071707030b0901060516020a14120706020607080a0b0d0614090f030403021306030b 68
    0x4000700806401a181c44a043c1c8468007480119607038040c0b20040b07250107001c000540c07440381702800308080c02040140e0506c00140c903600700301040ca60250690659841081001241c8a545907500c2248603400703900782549000b410b510300d6100104c0b51318001110207581c026500640541c0e0302521075900618262a000400d40800d0b81e5600405011825200000601014034020382000d1603000e46594030712403a55003404075804200180c18084840b41b002045032001d01d01c156071040310713190f80f030b0762080e0401c94001603030560103007040d001c041c14103080400c603840740c07602c0504483c02450099038500f103501030b0002518107404001d502080203500000c4070b54034100707a4401604202c440b141621980d82c10070741e80d44ca642c418240560003800001e0761b414000c0d100344c0d0b401041e42130041618541030001030f40d407008038601120300d16074500e40340200011816211b60b001050794001e114a4012003ca070340d580c06030b03110082c458542189070084e410701c0c0e504030000442d8016910555400c001 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 482026888 1250 482025638 482025641
    0x130f2112060b0a091a0903030c0a1505070c11060c010609020910020f07060806061201080604050f060105010207090905031b07170c010509100c12020d09080703083a 72
    0xc11140903914200140800c007100c2c91001c441c0060b85a807913038018145888108402030035101e110604a40c07090103000c1032034038180001c001050f40303640a0000f03081e540c580790700f89002654210101c8e61401080081aa800c140015285c1d030700140140c600342c55090000d001441148c03019180c5508220001440988540140442c460110b8030310704100b01c01c13001241e039184030303030203003580d90b8811902000701c98000c4800d5074111101800c1e00b0301c0c1070f0f2103c040301d500d07803000c1c1d00c0311080c1e5000e5002c0105000040c0300c20b480000c0da05025000c3d551500d00000e50301ea0540c000c50003034a544014100c06c00100700115680307090070081048040482000483d241d40c00d41c4541454548641078911000701c0c0804c560f905054141c450508042c3e6000c01c1c0043c000141d10080148480300e88040082407170190f60031150b03640d560050040c1c00e60920000c001621942c450012030340b01410034000a04410140c5500603c030064200000b08103440c1d05110111000e9808054080c1502c1c0c040c0701c5506 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 482028138 1250 482026888 482026907
    0xf1806041403061803120a02040f0b03072007051306090911120606030607030b0d0204140610080c030402010c1a0702030301030b070503280b060c060708060306130f21 73
    0x880a82c0d040390741e0130030b29080c0b45505078480030300758100300b0150909071021301d6582e411010740c01006040503101e000c600c121000b02e8000110040b80441008207050303212001803464144002c0d2982108601c84906545600d2805018440d29021046000101590b84980000c18141078140041e09490030407040c07405942c071a890164410360400050709900044050043c03201034018401940c80010413001000007880c065401750019031202c0140c1d590303005030401103016045241c00c0e400c0110402c10810401c2e03000c07400740f104e4001040080f02c810300a4a50040e020b080c0b0180304ca8013840d000b290040d9031000218440700075018002a582d000014505903841030000d0b0800b40c40c1d9840640e001e00080398103106410f1101e144510401d0312a40802c5841007003507010a00914810008059420045140c851540a1403c001c11039600c070408540000040e006032045040100303e18588094610006d4070b402070a244070f1040064414000fa1021840d0142e0312101e6038030040102010308 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 482029388 1250 482028138 482028179
    0x61e0414030313030210120f05071d0306010513062103030c141b100627060605190c0605042019060e030307050d2307080f180604 57
    0x3180d1100300c60741000412229256680c045812140f4656030030006101c0781103040e0020031241400e1307454140503c2c0521003000007540d8010501c0e00e0881e9000741003030b0084005490405003820901034540f400f08629056a90550300f1011524007800020042c4c4050b07803242c4208456810030114804694503400e001c14420758090000124074002250210074940d081c40c242e60041103083d00210764551300c030344a02c0e0140305849550800300da40700d08480c00307a401007010b060080441d82084880340244d41025611000410409007020310007003007030040f90018881c0c086d020300d5014101d8000d04d288540c07183d008909010a1500c1c1c42c0083c002c507419040a49094040c00c0c01c0443e925000c828000030003464115250304516102007210350002000040e47c0500003044564041402440a0102c40440f030316200d41072035001240b1500c3d41821b14002803030007000c3c00358600040889040360450b042041c0d101d038503132014242800f1103600e00c20305250f1004c4005030015103ca19568200701140 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 482030638 1250 482029388 482029409
    0xf090c09102303060f011809020f010f0e03190302010f05090604150b060301060905040c0314060d020406120602070b0702031e071a09010f0b0906370b0915120103030e061e04 76
    0x21f5409540c2c1003910042d0b08000c0d44801a035500040341e500c94801900480c40038035200e0241c201600c04641040c41c110a42c0e0404e0001c00e0600e02810f409014041d81e421012508011030320386603552585518001e0002030000c10305807090b0310740b40041d0308a000901030060113b0307a43e5075a00340152030f8a6061003014000c905007807130300c10054064403844905d1090380c000e0056983d9078000308502a01d4100d01282c2c0560f032242d000ca002c41d0b103c144581050f00c03030000103aa8100a00301306c94140360043c0340031b003150f104008014240c1c031031840c464000303259150940d032500c06900d060b080320084d8841100e0603514220401108840541190301c1c030601113901041200f204405102c00a803040360400d030403041c0c600308650f20001550b001c0e0110101880c21210b19543d42c0c404420001051f80200725455002c02d046c1c6462401b54182d101f82c2082c41203041c50016800d0504600c610305100140038010818001080342c0c0f2840d040310b00b1810b0b405e000f0150f102c103050080100b1f800c1800b031440d002 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 482031888 1250 482030638 482030669
    0x1090c030e061605030a090803010902032514031008010c03090606091a12010216050a0b011424041205010f0c210b010302070206030f090c09102303060f01 68
    0x100841e61500540c05000620f8400c08844025500c82d84050320034014159610101d10104050301c01440c040c6c00341200160740c038100755202680c2035400310b0062000d106218075070b01940e5002410201074061900070140c40380d840c0c642014601140354022203955003050040d4014907816484491094482d1001304000780e15003a402045841000612140c0712290661800318039100000c1c1c0e0300c42e03a1002c005807420102c3e40e100c507107120002004540d0307540514514000c02040c500c80d28050300c144c0380441a0348640400041003012042102040c42d080800c0d0100e12118250841c4c01404880000e0303005040b1310306d4154001c1003855003241d8428a091001580a44144485c02091251082c404e0341150030144d103030000c00c08039001c241810313401c200540c016210400918850a0345402800d144e1600861031802d150707882c4a030314440d0310b03c80101b014500c03100c803200094485031003103160008040c8100015103282010800d0741849044100080007562200e410306845c0541300340c0040 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 482033138 1250 482031888 482031911
    0x1030501080c0105073009030b0105010302070807061802100c030e0306070e13020d05010b1b01141b0408030301140a120f0204270303061a1303030f0c0b01090c03 71
    0xd0394090003085000030030030001c10300460b0b0b01c450350100407604401401c6c804a203405003003e41103c845034060105811007420002e00400406547c0148401e003425441c181c405d60300c0c40f125103d02c1c00010020760fa9a00c0107110501c1c02c40f05010556030182482c4004402020040c08220081004900040c595100031103141404a402801420b03c0d442e100040300c07011003000300c0c0320780f4040801607841e42030141a030039880c14010340c5d009111100e504c1d50ba400c40703c40c1c9040c003940c15100e000482da040843c4203161203088000558051038000380307410a8680103107207017500e20807036001c0041c0b4070000c0008a85003e02d000301c5c0300720040454425005603510085a028030030040030207009078007030b40700003405410943c00c41c41042075015000c41201c140c20a01c05040e1501c103a056000a076035150038880740e03070700c01e2070308078401442244107060000410424488010600005082005031030390105914054a55100e2443c0e1012528041d91b86404404000f085111507080010b410054031000 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 482034388 1250 482033138 482033143
    0x91506061b140706032c0c0423100302010f02010902150306040e031b010e0d050d0b2205040201030c0314040f050102090303040608090709231b070f0b010506030105030d1d090103050604020103050108 87
    0xf00c451500020f044540c80207020007008102700904496006941450181000d00000c18140325600540e4002c41c000d055000041c0010040c180c038505581c50410071502507941c0c0700303095007804400560159260f4503200401c0140500300329813a054480801d00d00b1842c07241d01c028800c61540303640200710401540441e00d584d03072240001c00340844d40400c46808410303000c1e0081042810701800201d144480e91000580e980c5d05500151641ea5461051000319a031600400580c001586424442074819280307108803000054401401e0140d00307007642c0c081240a40644100450040503070381c8990766001d0161041100300d40846c1540200803012038499800e10400580045054120603ca200455580c6040b4000b03480760440309901654205d0380c203468030090901c648508026040e42c010752030b00d02c44a40301a000103103e10710901c010300080c1c50019484d00c8844203803501c80926990354061100310a40044a030390042e00c61400030007400000030750036028034801e036810085030303998002aa4 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 482035638 1250 482034388 482034461
    0x1802041b0c030e0d080f0310060305060a1707091407020105070f0503042406060302090f0a05032109090c07031107060f050a21091506061b14070603 65
    0x810000c012441c046803241d0011849040060010200142161154015a00440c010740c0941c0300002c03c0011105e14403800710020302d81810f003032005050000018030f40c03001600914100001e403005028201c4820407089008140c5207000300b0003c82c80c07081654180704111003640c090b60811022400c417501c5003084c040e01c0c00322035403824190f407115552140d107241a4603541c42c03081c8070613800c181d04500d03510981d4018082764800682d2a01403400340424804003013000d920440c18028100840c2d1000300e008400c041040075003140041e0114040d03d030070b00402e500ca03600440c2420800c0034503500d241c02051418040d440307019100c0700009001d59908403602a0000251100e410403040a01503000303004016490300308500803141c507001c40700071210320040620fa2182c50303000c2d440500c00f800c55580389581854106205090600c08094000c5182000021007400718404800170b104007542511108041d000560748039542d503800c02005400719045600c1c0d0310074a00c1c4807070240080c551008 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 482036888 1250 482035638 482035691
    0x30c05010c0809061b070b090a1a090405090105011e0506030406050c041703180603040507050609030a050a0515070504080705011409060304060b120f0a08030a060f0303080103030215150d0201030e01180204 90
    0x5010f0708101d4420306801e01d5400010301c807682402200c5841d0b9070dd010721031140e0210000042d00390314240121007801c80c9100000d00404048205012a40f140e0f01240d5009400403400b103031680315014182c14501c25548082a10380f9501891058504080010600e401300e03802d1400c03242841d1010084544020b980041c55079201d5101046541403c4010b800c1c0808004c0a98440340390540b644ca080030840c51048403140c010683c07691044030340c440d5007908060586041401c060510351150354400507401642d0500103c20340582d171029039034044601466010f0240c07526424a80b030101c000e0b00380294007038486c0b000005524400800011444183c41c0410000e044804032034603400015840175180e40c022039100c141c0842c401400410400c002c0d403080c0d454210b5585503080081c1080301c0309100f4100001442c060001a030321103404c0c801503040844190074680038900c010b030024040600342c2c000303950a0043d03240400180c0c3c162100401c1c0207860502144502c5070188083c4210844038 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 482038138 1250 482036888 482036899
    0x20c030d1a04060b12010b12011a090d03020f010c051603080a020d11041403060f040305210108010e01060806060306180a17091801030c05010c0809061b070b09 70
    0x39030100e56801c1078003400c01000a0510021000000c2029280d0a0304580c81c80c1100140b048079032030b0004603a60040c100121700a042059081032403020003010b20135900d01244207044004070032070280444640344e00040c1495400000340c076000e5183c0c25403154804080d46020780c0404100c0c0900d040712202070f850b400720001010140d40580300c101c1d014000000080c2d003404042100f007501d20411025805402060761210318003840e0b00307200049000068000d80100050000035602d6018494005500d4201107844022201012180c0c034580d191901c20449200c0000481d41e4040d80004030300400030f0000d1080c42c0d15400c40c5a621141034ad0001c2d0950301803c00074000e20044041007140201c220706864001380161640c0040c4030808103031580300d01002442c00060b180c5029200629161590103041540c07664032950b10030101803086a06000c81c03c09414200072020703007104c0ca45117004000319110b07000c0c0c54400c0b224000c00e012061b03139403161890124107003c81c18107682c07503840c00801 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 482039388 1250 482038138 482038147
    0xf2406011716050c030a080f01060309021c03052703071e060c0f0b1609050f130c0c140705030f030f0a0c140d080604050c0702030a0803060a08070e0415020c03 70
    0x108442e0002c1c01c42ca440d0400600344142040030606000810310080d03a40e507101d0f200d050182c00c1083d0004107074004400d15280103550750060701c0d6918034444c407882d81001000c0019080c2000d98981c8103064110842007064080f8200242da29a0113081c0c001c01030b030860b40d01a4444001700c4096a94078041122001c0010301048070a00c1603203a048218800c50400d8650b11096a8060314010181d80100010062603080164241e000c80b0500050104a8001c151000c0c0c0c1c9000c036030f041110b01f0303203440303102d1300c4102c1b1800c1a4021341034044043c1d88422420030400c14a00e16984859142c0205403180c0142100701d100d41e1000001e580700391b039812458030315020070a07a042d0b4a01d840e00c94200d648420041083c6002e54041c800305180d001a82c4071644180b4101d002c12017110002480880e091070140680005a14005821100242d0107040196240c49140010301242400e50190010f48200035002c5a841950210300340181d119440ca40e10300041620f210060340560f40ea1085198818030 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 482040638 1250 482039388 482039401
    0x120117010e1e070509090c0f01172a0a0203030f0f010303140c160602100b030105160521010b0c062428140109090614120f24060117 58
    0x210340e1200e894580d00711a000d07544e48011418074501203a10044640000540700340c641804c40c06110300e030f1000d10b88000e0840c0c880600b62103c0700d000c0c0040d41b0382d82440032001031100c0f50549003032500c13a1001e0ba481d1102a04000255a42d004a8800c103440000401150a02044807007060580790b154036031160440609101044a41181c11410790900c6040d0840b41101002a000740c094465035000d0000500d080c1e14801c141c80310703141054007076890030040121016014a10890a070140d240281d664006a0821043d400361000d180207801014000010481d044c1d5004000e2000010240c036020354170040c00040100c045e180320750410510400800840c5003000701c080081c0424442c414107040c2c42e03a0090b0340c000ca0381d00010000150300d46c6050303456030070000c40350092101ca10140082802c1c901e00c03095a00d0f403010b00c50301460b43d1640820000fa418002c5525941b0950300711a50740c414005041d1030500c4680840c0f00b00702c240800b04940e940300d480e0b440420f5002d04c4d07100307540381c4415 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 482041888 1250 482040638 482040673
    0x3021e10050c031201090c1e050a0302090f0406060305040b01080a031709100c110115080a060b013b01031b1b050313081203041509080d02120117010e 66
    0x142d59080e250000300308854010004501c020301030503080346c0005200900c0c01018041030074000c3d079148064a002a90300210740d1010884000480e20303d00961036144d0403010980f0b000c1620304e8039070b000d03041c014045102c0394982d02c110f200d18059201400941d81c0c481503a41c41e0300e2640c83c09070015180e2180214040780d200300554001c84c00b8011198000e0042c2185801c071a0ba818142d00002c035924000a0042d0f1f0034000d02043d02d400e80507105c106441d003821640e4420355440e0050199480d1407180300260700a0f104031400300d0240d905c12552080c940000d1071000c40b0121841000100d01d050321895520902c20f030300c0100195580044500340ca05000e840195500e640f008552052105d288002001030014021400e81143c500b0441401c04911a0406c2032255651008620500402c80131450646414251028007a00014132600604081e41d19209842c0c802c01244c1c0001268020a001414071904888001b50b10301761520040d907000f401d076650f01c80300202c40e41c0603292081048411 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 482043138 1250 482041888 482041897
    0xb04150903050d08180721020d05060a0e1e030d0905030f0f090406080a0b041209091a01020709020a0905062d03090706080105060d05070e04110403021e1005 69
    0x2a4100884866a29525140341c002191040340000307040905104824024140d40216007032202c0141101da410172015454100d1407524185c1d0b03c0e504c80c074280007551200b601c5da22641e600041510300c0f40c540800035070054401d244400382d5602c42c0a0610340c03225840120410756502a0005d10302c2e2500c202440400780510319400c0c0c03280e000c00c000041a00155000410504549009450722034214108200445115500408117500a0300380400040ca1284803603034401d80c0289401110500c0c1c001c11076030171406406c10440e55141c5603400e4a1003203a03601c407030701d1450264212030106899010304026401102d2040780070846460f0b09000900d80076001e0b203020514036100c5c0381410301c1840c0c0b011606080c00b1011918240010520040b444140246005012281405100c951415001c030740c0741d00c2104540c0058941d00c0c0d010030720042c402c00805071011002002401030b690030184564290340f00b0710080303100b080081240c2050b41460150414690802810b06800880544c003e6516030b10 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 482044388 1250 482043138 482043179
    0xf01170d050a080a060506210108010902031507031503030801330f030209100302031806010303140a260711120d02030402010219150f0902100e1903050c030c0a0b04 72
    0x81350140846c081d00da82d800341c521b000c0350100039400802045030300304030040103070041c0b5000d074103100d00310000d610006034688412052058585550b81c5000044005112504d41c4902101c1d1458001041c5644441664140c1e030709107861070030b0707242c3c80d50030303001485d0300e00ca0b50881078000c200003281043d0003040300c14982500c0d42030240c5000ca0b5140040c010020094915010a5001c024042c0b200410291480c2e9010100d00508003941035490244c031000442440c5200190002050340419110340c0031100e07030708229922024a4081040008a08401150194000b844222606050b004001004a505a4580c00c070170310308180844040b000c2d5000803c01d0f4151b1145e402c030100680c3e0100400500540102c2d51030703100a007061441001e9904108070304404a04007110440943d80b042202104665503041c600c00031054107002c11525005000720124025140000109120012503812510300703040b401d8a404c0d04001d01080f00b2614240501860000144424441e011100020f8459900c = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 482045638 1250 482044388 482044391
    0x18010b280801051512180f03030411041a0301050411010e0109140d030e030d031b1d100318081305090c041401090b0d0f060f0506180411030f01170d050a080a 69
    0x100445500342041005a81200c0024a4000d0411088006010607c1d80701081c1e030141d89582056103848028680012603544a25500d0b0010700783d1740040384005e419460003500900140c502414a900b00b20200c1740580c0c042802c10381c14070041e61180d114001078502d41310182080e03074004424000c0380340d1110411802d0206105240d0b4156404208013070048040d550301013103281d840b008028040100d91101c03c1405001d0001d040984408a0002050301086c0c032626070580c80000e08a014000c007a50a68114003004081d105202821004104a0407070501d1514184d42d9402400310720a001c40d02044030990902c8140300d02a19035100403800c0781c05240c50140c2944850400005910490002c0c000315511420050402d20718003900000b0300c00d51040d001c21901c0c3c00b010800303600c22003440628040c030088200c0140c0d644e650100c0202250410a1074a900d00001a4400380200f0b0207601808070703021001804c0d0300c0001a80e03264402c2c190b03959906000c0882d40035640c0030310207001c121016 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 482046888 1250 482045638 482045647
    0x1103070209040804031203060e2e0b040e160c03260c0304060506010315061202040909060b0a080606030309120f120a090b090312030618010b2808010515 67
    0x6aa4007201940540d0007903510658803880e43c900032480510302d003060b20074103040c610108508103502001603400880c034503450810754078220003441e458010200ca186038405200001c0303108500c150240050311421881d15980d03460790100340a0704081c03240341400250890400d500040d100d800a4150b07040000c00d241444640d202039001440f50440b00b48150030400b0007040240314140c000d542d0000406e090400c01c5001203c2038505012590003030f10705021007102e6001c0d034140c4581c100d0b00100f0b82903a040009a0031803428001500a11909610500702a0310110320010089a0280902d000400542c9481894400d11000c2d5011b0400000c15000b500b030401c030042402e0260107120007245030115640c05000802070880c018a80014503803000501460001d51400200105200d0305100c1103912607a070480000c03490a44009004400100c0000000c0c1000300c0c0c40280049030744c1d481441420b000003140321541c20700361200e504d00182c1c9600c0100114240802d020300344601100030f16150 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 482048138 1250 482046888 482046893
    0x603150305070e04020112050f0109020f04051c050106060203040b190917070801111c2a0f08060411160204020d0603030207140102070e0f09070302100f0806060910110307 75
    0x1094050fa1101d0008042503040008560f40300740803000c040c400040801450919854129547d17405006d4048081c2d80003644803150385144081c1d03401890010301d1002c0020001311450008100c12108840540c241500425600d002200f5141944c5003007031800c0c144032002d69000c12078108a6242e0341030029400340440d85d00e4010304404e00280d640401400d8280c07405480f02d0071140c8920b40032040c10014032228451219551107090345400c441c80114181c1451210040c800064010280001041030003007202d45400000d030101010464031003c0956585a0910094031940d21110081c0c21040180d4100340f0942c6d8611504140007070001424a5101d4031200110f440681040e00503a108020800400790b0043c0141254142031019052041c44c00c00c502101d484040d202070b00741e104c413000203500030404000041c004c0d84c00404254012078559006000b03410a01d5092001480c86800160710b170410804031608801c1c094405101c1c2c4800e2070080ba40321006540d144014081040b003c0d01 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 482049388 1250 482048138 482048143
    0x60a0b0607020405040602071a061815030a12031401050d060f09150b2106131a0f070e0109030819050f03100e090601031a0402131a030d0203090a0603150305 69
    0x4103501c46c841c0143e4510741420203d40d60b441c04108030302c1c0c08500904100c01c648840310310114401001c0f4014030305c1c0e01d51510040c1c8295034000c1c925050b20508000e4428424100800301c1e00b500c6580301040343d55813440c41d01100205c02d0056540040d081229680041d40035400021021a1410009010f13002d6a40d052000800b1a03141c12941c0d0304c8203075201d6145840c1001c1d0303c0c2c1019142803860221908841c1d40d4032004010101000300c0208607481050200781d400040c200381001c9043c0700c16191100d480c0d038031345000b83c604600040c0d801440003041d5004100490540b41c0084629040c082c2c180c0c3c03010810029200b10008000051000101c10b0032402d01460144135907661104000341000000c0400d408000e000722007660020b001040890b0500314030b040030101d01d800380b07000c50307490b800811031a444145120240501d848040001c07a14140e8000c004400c0440583e442001c02074022650381c054a10301c46d5000300c1c1d03141c0c10403025000354800801d402c0e13010410340f00240e0300e0b1529030 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 482050638 1250 482049388 482049391
    0x50c01060b0a030b0f0f060715020a0f030c0521071b05030301060f170105040b0402090d05070509010605040602060a0e010b180a061d060108060310090807020a09060503060a0b0607020405 82
    0x228141c0022401c050503e0b05805103000c00e210544030400240c1c001d0000814071440e940c202e03070181c080020b0b0001444042d220500006d01c0b40304055640b00008000203000031003030824500060329200c1c1075140345100d074003190949000540300ea0300c400f404142154110340c01401100c184111103115481441048a4400c1007500920166459614041000c2d00c0f030b200884040013040401c0c101c40b404000c04600c10381c1500c4d01510009601c1a804010800902c0340d0040264002110100340c0200000050802c00b91002924843c4507641c0c0c9203400c3c1c84a0142d80203130005600304030300041001c10543d000c402040c0c1030000102e8072103c80808228140c2c81c2c13088034090401c1c850100280000f00f409454010203005031010444010440e42800b00100038100c10b04008006020a80c0d980e820010340c030104101e034000700110b50803854180d60303592081030200d00401411000141c2d082183c404ca41c00c584018018190b5981d420f40000014480311549030b500440a101e4a000350711244103ca = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 482051888 1250 482050638 482050649
    0x60109050a03050f12090105040e04032604030f1404061b12122703120e030f04030204051602070302280f050f0301150603020705030705030d0506090a11120403050c0106 74
    0x8003000052130a005080000c810891401c0c013104200071051a41e0080442d41110354020240e001a03c032481c08546860000d0001a8006d10f044050441040303c0d500301401380303100c1c3d26540c1403050700f4041940e401c120382510301d035200800e00040000b14080c045041c2103260040c40d1100b4148103a81742503641c2e000d2055500001c0441080102c02441485000c403001c007007500300d074400508807601000f190300d4040c00404128103690190030031007060f001103040110000960b07498130440ca1751182130360083e00c000d1f413049081c1404070700d40405400a01c3d0404850340d014040d95400c0d6020701001004100c0714014002c01000c4030000d0b007004545000107002142c2c03000a002c0d10788020000b090145aa04034400d9242480040364400d9020710070703081f140903080250325a5040c1c10300d281140505d540240c01e074040001c50b50303280c4600e41e108034451803048a8503061612941503000c02c07070b50090a858201c01c0b0800080c40b0b40e141d01803226038018881d1511602d801c0404404500392609036014 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 482053138 1250 482051888 482051893
    0x2c0418030c02151e0f090d0302010203100905060604050d0f0507060207050906031b0405150603040515130b1302060706230108010b030705190308070308040204050a02090f0405060109050a0305 84
    0x2011454244900422004005261400d010482518480e041c81000d4100c1410b1350001c0e50450120450064800407500100100243c1d2100e0070040e002c3d510440301400c00403641c19001c0f40400c0705120b16402220042c112070309090408050080545c04a881034071111901c400742d0303001440400c51079004d816150b025008031498941400130001d4045d00b650b20a8000041084442c11801241c5c42d81102c2214041503d46803074025550901c60498280d400903400420001448000034425820700e62070340ca00011591243d103407002001420304c005114460001c04a80c81044611241940500040c4424500100c55844000b100e4185d41a0030040507a034843c158020344107030b102801020004000e00c940304160001035207540c0703280161803003005036031a030302d00c0c4040010807100555440010103075603048600300904840b034110740491089003003000280f4500e01c0d500941c1d00c0e090340980782c4222180b08000304000740c5002040e050421400600000306a602d00314042c00440c002c0c0c01 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 482054388 1250 482053138 482053157
    0x1512030e0d0516050d050a020409080c07080102040e1506030106050d0605040f0905120910050c0304031208090d03090f06020702190b0721020303010323060406020a0f2c041803 77
    0x855086003070761080c1e204503514110440421800f01c1c0358200141d04407800602c001c11072401c400d132f43c0a60300d00c8086a110304840803070400c1c1c0560050050f124072103201002c40e51185558010141d07160751441d040181400100041402100070b845801c0d054480420701c1d036100c4000c14102c5001540404409444a8603913040c0320b41444450b19441001180501c0d003503d02010400031207900e402242080000034031041100b1080c402d980155038800b4050350810085080201940802e5031207041c6401011064110b042c00303803041001d160b40c0084110f500030203d80350a0001c0d0000041681c01c660800415041441952008000b41c11003911490712100303142000b02c1d000755482d064103000550f61402c000e81c95000825281101da0101041c800e44c158070b40540803d90310b00100c40550703c120341c2030004114403600a0240000950f03205045151b4055003200c02210036000d007034035140d480d60507040203005500380600301c0c10081d0003c40c40c0c01001c3ca00d501d118280e2401a40001c00303545 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 482055638 1250 482054388 482054413
    0x9050a0807020f0a0f05010e121605100504061202091206190612020a03080a1e120c0503060a17030906030c0301090e030a121a03030703020d0201060503011512030e0d05 74
    0x200400003c48151001e07950117017400c1e14800e1610343e90282a06204050034007500c50350f54003c0917044007000c4810794a209500c444a4580203900380501403041c1c401c407606800a901c140240d408650080c0c1d140c00b0b0342110280014000d5204c0c240c0d0f80d40001050004110445003040454000c4800c2d481c00748042c6414502e80e0100c40b072540102c2e8041030301c048003001503503944150070152504080d03415520850000300f41c13100c5101262030400d1610074880e000200c2c2e0842031481100300003240901c542a03102604071520b10017218840d91040c02000248480c1244080050f05603c500c0100c074541101c0c0c000184554000720382800c040c080000c0144070741c0106008400481480e20001c50070b001f40e09501404040322079a07010b0a055035451403d55040302c582d0200003481002d0192690f5548a0070025103800160b5850001340d824a80e00062a003414030807114184005070202103803508244440e40c0eaa014040e040e420010b0000c5042100e5903942d0440022a1007800200100741e03184 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 482056888 1250 482055638 482055649
    0xa050c121005120c0604050907030e15150103090534080c0406050301050405070612060b030f0a06080c030a080d0e0102211311041d010c0320030903040e0a09050a080702 74
    0x2c81d014101a000700f1134041064407500c080c0ca0656801325410501660741890407401040b1001141c8014881c0d0600384803d4010000070728081c800e00420011500e00342e03001076040c0c07900c683c0000d01d590300c03031a004c1d150710b80158600d8959403403280444801703015a03406181c000d2901e4224803000d801203003402096260a20030400200010380c0240070510785a1241070303c4210314483c400c2440128002501d039401658084000b6044200d211500d904004c50800c40211080750800600341c94100d0200c0c410300001210300f144c51004000f009444440e40c0c510b01160071078407040440755111200300860b44001e00281c01850886c02d100e490001c14040b00f5155004c000e03080e1240052802180b1022034910080141c2c4408155408a201c1005000c3c0502d01840e0014a00042d46440d50b01d000c0281e160300f05800403101c0000740c501424024004000d03600c802d44200c034043d44108002c0080d4a004010b00d5844000c403000000e051410340c4901e0704140c502c040880f000300000070300ba011840c00 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 482058138 1250 482056888 482056909
    0xc0108010807150f02030705162d230d0506190b0105090f0d060501060810060306050f19032109090507090608130c121101050703080a050c121005 64
    0x1060300500403140ba200350b1104007040ca03242a400c01c1a91300111514500070000c6035240f50303004003100d000071548001442c1c0015180540f45c102021211400ea5164101c48980110102c0080714440e0034a08a02c0500840000c484649010b05e941010041655004120a2802d00a001508662401d07110320a00c04a4a401022000b442c140320b69030166400010741d2810030044c0c50000b1030382c18242c00034410011543c001008141840c0010a00ca81d06c070341e40c00d0003800000c0b50b83e05280c1e1205402e03802e490850041c103400410b0a90011018038295426022400c0341c5a05044426240d4840015241403401ca401041c07691035580d0045a521032001c0e001008007020411441c20204801410b80c01d603889514204408507001c02e9003042c24180002c07440380d020a075003007180e030b0700c000070041003600c0c1750141c3d060482110000300c00e50042c0100c03508254503684a0096a48210340b80300100301c00f81008600040c1884019081d401c4418802d0081c000c202c810301c860351500040103440e01e413 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 482059388 1250 482058138 482058149
    0x20c0d0504080d0804021518100516060f09050a060c021c0f080a1803090e09010506131e0207060b240f0f2b1413032105090c010801 58
    0xc1000200300124003c80c099a03481490318140d07120f42c40324000654140103000380001c3d105000250b890864107280d56000001c0002d607142c140904164400740d615002d501c581030046000c1c58200700014400d07502603d2050f00807000003804040a845092170b00b00e240b2402c80340c03103603163381211982d03404110168040e1814050741d00120304920f001814400e40c0a20041800f070b826010a4402003d03810201003402500300f040f104a2a13820001e21107032040c860359441c102c0101c0400c01112041c02064803e010103080d1110f203280c8a02d51200901540442240512500640701d0078031120340000c000d506e001c3c24020500c006004204440c19151410400701c40030a03607186812408514140c800c0504140345040e11040e6540e03883c60ac62203100701082c0100130390200041106500c040145020402c0501000340102998020808103400d680d001c00511a1a4110f0f0000c0e10419a014400d200b0356078006400502c1210364007514426503580c9015003090300000225680140003234010103 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 482060638 1250 482059388 482059397
    0x3060f0c140a0201091b09050a02040b0417120f071202010b01271d0414030a02030405040903051204050601140d0b04030f020f07180b0321090d08030a020c0d 69
    0x203000034009040d80c00706452120884001198160740340c1c0c000c0d480000c0140d041140f000320341d08100728914041c182801380c01141860030000c12040c1c0e0030b5100b914161a814000e4902d01420900c0007951031b01400e4000e2610700c1030b02000a840080038002c3c248400b0396001e0180c44507003c0c03800640039903000c4c0100d002c5a24224114901d80c1e481500102d55000340c07500000507000c00060058948170503080343c0c0c2c0603001c0400d0b03003c1156102c01d00d98404c03405042902c07090b984c0e030758a09450707210b01503c860040e48148414483c514059015000b07061090070329a1610b00030040b640e803402c2080f90180d45581021004202c1c1c07008501d00c8007070b40c400032241c2d21401d0096545101840c0c80107032000e800c01054003004003a4a00030041541840c484000b12a6404e903151400b00c0c20761010704e21606001c4c00c0c039038098224200000ca40603012010400b5101250300e001207140a40c2081ca2415130000007000f00101003800c000c0214002c2610410150b0755a04c04943c4510b4402545150f40410 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 482061888 1250 482060638 482060651
    0x30303060b0915090303070b0c070201080603120306090c04090c0903050d0302040e15120a050307021903150b150705010218010c05030406032d0b12061513020d020c060103060f 77
    0x2e039151081e68000f03550094840c0d0300c516554012a00d94040c00c07400410141c41c2c0300a000d842d0483c0006000000d2003640d0b80d550603074482c014503443e1b621841102141000520108409103003504c1e1069115800c58005420f0a41d1505000241c0d0f1921010344041406000c050060103424401c8488002c501d0606501e41490103400c0d50110b03030000c1c100e860000001580f00103a41c2c031090185102c20340300703040310f80c202424100b545c0c0326480000101c0c0300c2d5240121020b00449040c604408070b9400103401110403080042190145c1101955260301c10b01007100d49500c0c2e00d020b4040c0c5009809480016111000807000c1143d080d40300360250b05114030300d80420000b405c00022501650620b18000c5900d45c41c01c0e90400c000c011002030384483c0d00108181700c03800c7e1011b038400710561004941800055035100384041d110042a1030307108418441038036209242c02c016006506131255003100500e031507007040c2950202c1e00b221010380a01d410102c0100280200d500505614032050081000103 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 482063138 1250 482061888 482061907
    0x1e16080a11160308070204091704080d03051320090a0f050c04030c060f09031e150b03060a0c0e0d050f1b0f1302070501140121050a020d1b08010501030303060b 70
    0x4000d05488001d00202002812204541f940c0c4c00840034580c1c451208841c140981008103e150054081d5401e62700c10b80125203800f80c0b00c0d015250080100f4a501c0802c521107413100702d8210001901644d1f01d40d06200b811220b0340b2404e48092040591540004080500b44c00a00980748098140c00c44100f0501090010401280528003240c800f8242400712204000d025610742c5480e42c00927241c0e010b50b54181007820481240140c2c0740c4e104d079a2070390360b046040710500100d901102115401d43d10410001e004034010381c1c02226461110300701458143d20381e2000441071b0300304400859464200520b020030310101081407000b442d40c0412112550361701c10010560140b62448451700c034140328113640481480d07540c112081950400002d101414a4400203814000f081c804c488030b42e00705000100402080606240d903640d07028018040003d00d0380c08108444000040682301c0519220f4040004054580c2e000010190b140010800d585141030250850b2219030280b000c28004100043d072 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 482064388 1250 482063138 482063173
    0x70c090b030d170106050c0f030301030501150b131802071b050913080a08060a05040c02250e010308031b0a030b030c04050c16060605031501140f061e16080a11 70
    0x540d5010f241550300d03403440310100342c5810448d80d0403142c00e000000000c070030703c107040d00070300c41d1000c1030b0420301d00e40c0d95a60781081d8203101d2500450003006600c04244180c080a40c4414842021500c01500700304a91300d510802c804003030f075480c070280c5003007100300070b18107000b1104e1740e018161014a0401003016101c500e2580300310070701e51017049414000a280f660710301c500325019100107003082000c07100340d0b800a503403511406032201154200e40658500c80c005980403000347c510756040003005034a9951012416000a404154101c240080e0044055210f9020704214421540c0c0410314010490615050012040206000302d01340340802090341040320480c0d038607540004110b980304240e420700394000d05050304601e07494000c0d20307480c00d00e081200c1800342c184c6405400f9904400145000c002402031540c440a03003059003484841c25400c030100b50206040960072619140c01003800340405440071b08030b01110406808220b0010103030b80b0400340b000050412000b03021120140c21400d1 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 482065638 1250 482064388 482064391
    0x1050105120604061205210c0c0d020301140c040608060411190212040f050913050c0105030c0c06100608070c0b15030a0c0f0501110106050f060d02070c090b030d17 72
    0x42401d006011450381c1e1903603071100000780030445101c120f0076100c3ca000c40e00c0d031000342c1d40b00b40c81102c0002c0328942001c2c840304603910400c0340c03802030490050720300c11303c00c0780140601c0a99240d5694078a08c40d46202c401c41d00c40c0f1030b5600150850350b6034203000703015001c828080e00903401645080f159240460800e000c40b0052140c81405104503e1103600413490100090403c2101040210f00090011919003440003a2101201d10078450f40c1c1d440314040e100b580403400039005a100300402d0a0350b5015800858102c3c0409003000e10b040b920000309850944143c035100c6d45c07141c071440104000350707024000c40e4202c1c809280255180c00981c84084010305d000d4020700c0e03000340d1204001c519950030444611034550005c5005030041e61003c80d10041040d621510b07000c502c40c880070282824040c4100340680d00c00a0000381804c0c0d25906001164002003050b01c810380c0c0c01c00a040100c0c9841c1034620050154050209041120000f41070908414500420502c01c7c080c04031018404c84002a9 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 482066888 1250 482065638 482065657
    0x40b060402030901020d090b22020a060e13020f030106081503061603020c0a0f12080903030c07110402072a061209080405120d083d090f0e0d020601050105 68
    0x5a2243c80e002e000d030340248034080e103140e1403914024080f41001a00c0c40394602c9400d0242420160390b01030344901404a0400b03500960111104c0401c1c80458060719500300722040207003401e14110800c5440d403080741c2c02500010005d103030100040015035803040b2440c1d401004441d4443c80b038070018010a039146c0c00944203a0009417060381003401c0c24400e5043d00c2c001a0310104450b921215410412007804418806560b0f6410007401c44025502a014090142d81c56038011071955071268031148a540228200322010310741181c903030f081d035911800903008660040e409441800c204103200740b00103c5068480d2078411a150080200b03d800610558410450301030118203841c1d145080384035403080d9089140c2c0009441c00b0f440d1010400207202401c3c0e2031680395100f507a15550a6245034000441c00f12408480341a8072105086102c120030f00c107030281c000d6600005441b01541d505640c403070040200a00c3c0d40303002c2201446801c0003065042d406d03a0007e84680e504090009107548642040d0 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 482068138 1250 482066888 482066891
    0x409050a0609020c0a03110102251109070203041517090102270f010311070b0108073002010e010c0b07051c05040b0c0333010e040606091e0510022103040b0604 70
    0x151f440c03041c82901102d2881e540c09950034030b030055030044a1140d07407180301c042d600102e11000c081b03500d08000721120700580c1c040d0020b50a1514002d48070501011a1b0301803810030030b0020303c07440c405000d0007141d80600ca1040015132107240000840038140c1502c1c0180d045c50000f640c4c0000e1a494920030650500028030b0003060b02405040002250f04c11124018000305000c400008d41c5040840c1140980d020000000c2c0c0040403500805500c501ca00c60314410140c1c032070000001036008080310701c1b50700300c10705000c0c00120250b150106020030445009010450025903230002a00c12019080144101d0004001c941031130303240c0d0b0000100c01000c41c2210b000010218650030200107194102c181c04070058010341010740f81c4884095a075400e690f002c51800b501c0607103145003e00501098070440e59400e0a680e2812a03914003005100401c140c80314a51400410f2540310301548003070f001c6483d002011101481090680c410f22007001100e01d0b684284103000c0002c180d070075001e406c01d408550 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 482069388 1250 482068138 482068157
    0xe100e210304030f0303150902040f050d0218010801050610090e180f0d020703030305060402310504140103051606081612090605010503190b0f1b0409050a0609020c0a03 74
    0xa046141d842a6040605044644100c42c0100356140d0070068000c41c4c0385e0030200010b0b0380c40720800140d002d1401b5180c05078450507024402400e0200000d01c03081e00040c0740c590b442e0400d40c0d005807000d001380c20203456651510104151070402042d0020720036070134648210802d1420220590707407200038005501115150800c40c035100001c0103503401220082e000c0e9074840c4101300019645400f14442240480d04040000303215251610903a0501c074501e503950404400c840840e028040b486082c40304a54540950104290f140d903c90716180001d031101109455045041641c54070000200d000700010100d0418401e0b0b81e8048a4183c100c0e1250105208581d002c650560f40c540d008248480e05514101c2182e0600c001500164100c41c41070301503a05001d12040e0104000d030301c15a01926001540b404902e01106407c078099212040c007078204d0840c01178040d42c0000b540242d02911000780c96005100f00010148076000c002c20585904516190103240580c2c0c582c0540134010b000e0100d09070 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 482070638 1250 482069388 482069449
    0xb07020d2d02030909010f0906140913060f020d0504060f020306011b081b031909050d030806040612051c0903122006090a05010609060518070903050604030e100e 71
    0x130b5850715000181601e02c03968492403079134500000c61103a054010b0030000c00065030119080c800300003403009001a5820f64540c7c0030b1040d90031001004440c59644d0b83d0050006102c1407003e00030000e1514008a541c3c00e2900b4110191084840c0c500c0c010761040041c030101e80e030841c21240240d00101180c0c0d031444810706007841a0f005005075212040032040010076030302c10100040004c1d02144070740c54014004e01c04226058180703400b40d6a0400c030404d03120070100380200c5007241d10110007003010403a45e0b11a00306d040000124030048900f98005414910300100f4400350030360300c00c0f4503d00140c030345156840c2e400b59403503203030035070703024880c3c4856011003900c94240c103600303510340c51400c07202141001c1030000d0f40c1e26910350044d11b840d40781880104110342240200011181c009001c14211241300301e2038560030340e010b0803020522040d42d0000002400a01c0a588298080d440f6066403413100c0707003030046921541007500108180c14040d421a0b40d59505c0b0380030001481340c0903000148895 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 482071888 1250 482070638 482070643
    0x210a08130606060c03020f0a0c0b0903010f0204030c031406060102072c180d03150501030c0507050d0509040c0806010c140118060507030b010206040507300b07020d2d02 74
    0x144041c11080c140000800c92580000543c88040c2c46542120040141d40b03401e55201e0302c1410008016241000c81000011409000707080c181c3c000270000264644d1200323a403c202d0344584d10403070308011651010828411140c1d60035841c41c81c14000341145141c9800006d40f503143d1405031080c1200200001039050441d0040c42c915288012220340003801c14040c0c5c00c1ca051111000d100c15841a10450210706101e40502c001c010f11209d1202c80c8541800015800381421400c44410400148100f202040d0f0801c914584031400f03840380760380d507103245050106541c031688001c070074000340805001c200c0c2d030301c0710840440c02c0d00100810700c3c0098118105d07001d00611a00061460784021708501480b200354031450040c61035072070130410204c15000590304d5103001c0318042c0c841d400850080202840540901000c0b03103031100b40c4682270015545200c111a000c0c0d2081d1000f07801e203820085040d03010450303c00c602d03100742015541801900c001c81c2e0101c800f909003a25884401d9421000785008 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 482073138 1250 482071888 482071921
    0x20f15130203150402040b12072c10150e06120405030405060a05090a120b0f190c0c110402040b04141c03120b060a0512070e0a1502210a08 61
    0x14180ea0f000c840c11048480c0011064a00342e206903d001251035591401280d9030902d031400c0c00281104a01e00340c1e01c28980308020044010020504807540002c0c850b000d901031107640c42c02d605008403030a000e02d94180d5501c140c10300080c820120b15040742e82d81d0750016584a080c00b031940e10841c2da958075040c3e0660144d43d004ca508110017013403141e00c807900300c80500f50129007a204080080e582d030402169000256101804412060f4041106164100701d020391180456051100380c081c0c05403a00101c0da140380c90700b0b0019076070620660801820800c0d01e92070a070121025400c0c1810891000e1092103244a14201c091100c04040961303200c0b034450303112036801310f001c0d03411302d6030f1904014104043d6070500075445454032191144524089050307c1001400d075032aa400d1a0b4441d01d000324402c0c0c09030503401404010104c0c051a80e8601c12140c0280548d500d0003441900e0300003000e49407084800d500d0b403000c4003d800000088001905803a0201498a00b6400544501d144e030440d9021 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 482074388 1250 482073138 482073143
    0x10b0327060907090e0109080906030408040305060f06030115050102060613181b0906060f030b01020a02030d02030d0e0c0d020d020109090504080318010e07090e16170d020f1513 78
    0x7440080000307940021a0000c00c450b003031042486110b4400c5041030884004040c01088220244001400e905010700519406489030a510746810344a480d20741c0343c0182222402d041500381310801000e41800e00840e50401031890a40340d225003001c001035214180145003a003e402040300e82c458064080c1c014180091040c9000d40a1103d182031040401010f074142e140c0d9403050440000382c2e030880344201c401301d400e143c1d10700224214039030040740038020103200141184240c910300070250b035003803001a05503807480e002590b55004e00c41030401030303d154150203103244e007100c105082b541d190b190a2201240d811034503032190305900d01c0141d4080c003403034000016540c84c010802c42044010401140140c910400038210344103030307000083c2030750440c0c1c0900ca565042402c0410000e032031500030114803a8408169100c40c201c0c08108c02c0c0b480b8569118044191110000da003649e0414071a0034242e0500d031010b00040940400d100e07640e085001440c101c0d0309540c00008401d65440f08400d001590b = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 482075638 1250 482074388 482074393
    0xf020f010923040c0206090303070c1104020d2f040512010608060c09013f0b1203040f0b0a0c15060902040b090405100815090c0307080f06060603010b0327 68
    0x1210802e8490340150341042d015034030744105100028000503410b4450200c0d50011447c566402000721202240340f00b080b40c10990b4000c0300103599440307002400c0c40c680c8141c000a2105003024070000d00650503001c48204c409003021400c0780448a00840e01603410580e108281031200307100b5a801000980d011043c0c0740240014080d00c41c58000050920701e8090340c1e94403401c003c10361000d01a501411002c91400400d510216600e9114034681c05020b40e541d4000807465013140105081d6041c0c28000703401c540001409001c40c0c0401406180940f1030403d545060514840c005452001c40d0040036205401c032000140719070301c2ba034001101910000740250f40b942c1d40d82110f80c48a0704258032581c866800c2000080900008211400440301c90f00d005041c1304a01003048401407001406240460040c0c00380101580c904000d000020007c1270018102404501411810010041c211510030a000c00040018215420070351742c008400c2201c003078004070b842c13000401604032003000c2040350 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 482076888 1250 482075638 482075669
    0x4050a08070305240a0e07150e0306090a0f03050d0912032304030f050c030904020c0604170703020d14070c081b0d120806010c1505070e010c0f020f0109 67
    0xc01144010440c0c1c85041110000c0d4600d40c40c140749410380c59100a801100c46000504011a582008010a042d402074400083e107800b07440e24140728040420300031405e50030100d0340c14281005400e80c445000c0010b03042d203404968581503009541d030006030810201248540d54502541d020210141e4440c4013408000402c00c4090094441c428480f6504a065680041020080ca041e240302d585d0542c0d800300c14801044040d00c840d00181c50542c5540710074801e44540d80c44c0c501c014000d00104000901240c0f13028640702c00620595650070608000c18420070300025000980f107107100d6034a041203860000b0206c1c000d1018003442c80040d000ca0480c00c00040c1c0c107180818519055240f400c800380b0203c000c1401e1010946a6144c020324122800072460b20451041c590250080b40514120700010096252076006142c8000781d0348050350756006001c440c980040c64052103000a0902048880c40e9440b0409440d01110019001d0b80e4a0540c0341c0c0c3d90784c4501c00c03450260410001a0310741c0e = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 482078138 1250 482076888 482076899
    0x20f0a0e0703050f0702010e0a060c09050301020f1308030f1e0d0504030804350f0f0f0301180501080c1e030106060c12080408032d040501020a03110c100207050304050a 74
    0x1508058030b14214406484012405c0f8510600503180e031210380c000180541141c5a03107010040c288403e10104001d1400800b04140d42c0a000034070000f40c14a039000c1d141d84180c5124094500700e41c1c040f140a030b00410007040041084015204107000c40010320307082d0602c441d10000c182c420300054000c11450b00007080100340c1c03c4071410340100d00031002d14400038011141b0030b10340a07240ca040c00e018880c0214031190500350303c00820460150386411030a21000040d118a00d8010414820032104040010300090b13120002c01c1140d80d00b800402e014651414a4280d12449480b0019005040d4030b864203903d84025182c6455004000d0004c02889030f8440b401480d02c80207040891340c0fa0b04c10111025010b1084803c0c0d402030760000380141c5143c0b58801c001e0710346c00c002880001c0c0f001800c0c880e41a801c0c01021214407131030041c0b00140c2e50b4600041d00070111000240107803803079001408410402e400c00200c00e203201b64414030050b51080d03281800c610714003c2c0d902099020350300200c0443e1 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 482079388 1250 482078138 482078141
    0x313110f0409080c15070203070602090a080d08090c0d15050621070e0112020a061b080d02030610020a0819050903060103030201091a160f170a0213080a0807020f0a0e0703 75
    0x5882100c0e209580c0c0424150b08070040100c821b0341c8000069100b0b10508010490a60041813070780c2c4002d11800800d07541c0c0610700d007000583c210110200340c40030100810050144515144800d00315032007900240d030369580720b180c00803038905020600d55500c0010220f40785e50180c044601407145500b1024040000540e944a5090041c4c412036074440e000000e0380003000c00c00700415940240380c5001c17542840d0084841004500c101c2d044400ca4600078408240c85000034110305000402c096541d00e050018020051600044c00b801c55100c04101c0010071203500546400c0d80280124075580502c03924125203a000d85030059615001d0840000201a01588104401485062100b103600d9640d0030809025a01300d400a03c2001328021050307031103118000040100241d402d01c0e14007400b0501c0a212201000c8880724415a80060700180c040b2011003c40c4c01040004014940c00c609541c5081c0b841c010920000d004080280300f44840d07640b4041590003410007400200103c0c60003820050 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 482080638 1250 482079388 482079397
    0x2100e010b040b15030a09021305040524071e0c1b030203060c130e06010c06050424021e0d2310050d0209060d11030706180b0313110f040908 62
    0x144183e292180f001480c1c2001e02c840c9001c6607400320380034110750312924258060940e4000032070740a8614035502030b108040c0e1050b5030181d07003d20f00800801001e03a0f03c500d1086030f0416110b40c0002100700b005425a0310800c43c20051441500225000c02468005d032600250082c000b807000301c400d2003d81030f11103a40d81640449001314100c0780662511107202c1070900c144103080b1044016842c041c07114941d0440119041700062511420308001a2501c07011903105807411a181c11202d1100b024001da00303000482e04502e811002c620304a85100103421a043c00d2094841c04000403800014000440e4802080f039450881ca04140203030b8140e5440301450100c480360402d00840340045224100403030940103495002d0a0f903040da07220748080102820030f580c011902e0352040c0c081000301c2c1d20184007040090800e0344600520f108081c640302241c4809420011500314144104a160b181e038041070000f05170001046600f0b90400d00c0071a9000450003002c030340140c28040300c23408100094000f071 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 482081888 1250 482080638 482080661
    0xb120a060b0f0a1b021f0305070224040219080319050a08190608030f0c1e0a14030d05011202100e0907050c0106150c050d17010303030c02100e01 64
    0xc0200039115a1412200d002e0801c0e107042d01202032141540090180c0010010a041da80c1c034000400c1c0d11368002901c40c2c030011140c050700580b80680316101900350141503004000360028090003a02207174140c3c14542c001880c580c03941000004141591900ba03d641c1541c050843c0901c09540c03505030075a503a42c08030a05501202100410740c140354070680607100e06055507030707404680c0d413903084401c0074003051010030060166980d44000341d500010801440381c0c2c502ca10721a03465141e242107081c1850090020314400e03443c0c0d19588001d0010100e0700d107400e15171120a082111007030b510b40d10b14502031055003d54171451b00001081c1080c0b40600d2400315482101e495400c000150000c07034070440780c031080c2c541022400c0082413405000784040c1ca0902002800010b88035603414980c0c0e041181c0c2404100820417100c4180b00b40802408036040e4a1102e0818002d0003010080c98201501c0510000d410150fa649510b00980c0c824060100c0c1074a00c600c0c14400cad403041c2d40c0147d008185d8461340 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 482083138 1250 482081888 482081891
    0x1b08040b0c090105030c0d0f150603060605070b011203020a0c120b060102030c1020031303081602121b010c0f091a040308130308030708040b010b03090303060112060b120a 75
    0x1900e003140501c200d8020705410395a160542d1502144402c1c150002100300501644034400703481c03200d8180c412034851f880d803000c5840801e40380c05c0020f0308562a0f0340080c01041070801880010460b0b400c500350444038580203540354400c0c281030480c2050340d0142d00410b101003103100080c40c00c030440e044040080c040c1c082e031040c5032074074401607a40307100d0901d00200e02c0d0043c10783c401d8103d00e80e42c416111450090075100f8059500700c000c14059200302c900340003030b402e0007460105159101c58010342c480c0c10821414070203a400c1902940e03c1840f00300b050b800510000d04003110a100e4a031404090900d40000d0004960411000e400d0500c0b464113100000c003010740001744000300c41090040300c105440c02d03501d0103045440301162644413000e8041d00752010140000040d200a0045200f0b890035a10300219042914243e07a5045042c4d1050303068480034024020401d20220459030424400d0074070516009140580c1c1015041c4c0e9440203105501c0411150491200d03d100584103c0b00d1800 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 482084388 1250 482083138 482083141
    0x20901150e0414040f03020304080307050f0c0103021c0b010e060d0e0c03072d150f2709020c0a021c0201170114010f141306030531061b08040b 63
    0x81c04220f41502c0c0090040408420109010480241c00325018a0280c815030380341135100c08e02185590f01c120700888043c0d2100060b820048014480d440d400d090074030341917240203040e0715202c82d1400300407002811540c0d1803555803a10380c0038a9100441c5030001d08041e8403840060302c2d9900a02178655110107600840e00085214a0081209800d481c1b0700481c3d0008072141070440c00c41d000c00c9e02e4052504141e101c5000c10301744200b82d00203280101d0756a65000c5031048400041c03410200140c240b2030809281034038622039241003030301005c0e140c49460050300c4078181c4d044a8a0f1066204010350081c12808d6104050109170440825a50007a21411187c104000e0b60300c0d0005024854000030010384544140158410003502c2c1106503585001d80603d09420000c00403544000148464100983c100300411900f6020359940702600c800400c02d454801c1c03004d400442c0540340a00407030099030499004005070395000124a401c0740c904401d0110071000701404058003070760151034103070780c600 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 482085638 1250 482084388 482084417
    0x50c060f190b040f05090105070909060f0b0304050c0411180a0503100b0d0c1e060e0108160302040f0f03020a0f03170a2703060c1b0f020d02090115 65
    0x58609028003540001c040c0d007140c18507508002042d140484035809a1a03c0b101c030780f0301146005040c0212151000000c642c1821700c0003500740c061941c8002c60050424004200c105500500c3c0b00850720814503840c0e9a60b500c0c0780960400c0b861217800c5900c58a0072000f003030b240c504c07000a056003540b105142100c071683e1404003d240d4440748100303a4183d0100b0400e4510107525005400c0210018000d07900c03100d459500c1c41920603013508070340303c408a040058403507060030066040c024400ca0928021100c07414000a080f40360003060031141010410801035601e10984c112001051030341400140152215400480c5001c2d40c441a403041410401c0480c241c040030800d10200ca80c0800c8146040c640015000081d40112070800140000b00041d108070003450380f21b220414150448042c0e0709815450902c0807140703c5500701d000c02042c180825040082c50101c40500d5030000d080890030086403001910b04a42c0c2c0c10000e4014260100010350100660f00b00350580d00c181e10745800441551 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 482086888 1250 482085638 482085661
    0x70f1106120a0e1f0b040e0604030302091f0c03080702030d1d0705040c09060c050c090106031409010e0a02061e040602030c0d021203010302040b03071e0e090a0512030a0e0d050c06 79
    0x24030019903940215600001280310360b80300d641c42400c0074002041c3c125040c0d0407d804c000b4203c030240c0120741c000403c01c0940c98900f04105505926400ba2060042d107000b000300107800301c031001014013418030041004d041c020007c0d80c200446a10742405510440201d028524190f82000c500c00e1286034008546071429026443c3c8a694a135a880900303032910341300304c0d10304e82c45041c29989801200e40c8009aa150007050a003c3d280351780300490890707002003c22030304010081c03008000ea403402c46204a005000320300c1c001042c3c0c0480c1c403281c6411064030020001c100408034508403480c00900015120b40100240c2102116a0f0a41c4c9030024920000d030b8440560800c0800000380030801840145070036844810720a401400b29a600d0781c8131030800e42c0b10010006003084140e007106007080900301d0300c0d0220b54004880d50160008020656429560f458140c2c10380d0300580e8040002628514503a0286413800081401c4428203a0041d2002d0b1180e440070700740c02c26038042c081c001408401c4a = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 482088138 1250 482086888 482086903
    0x1e08040914090615060a1106130b100b160203030c011d0d081006030e0102120106201c08060d1e030801060e010c02040b061201140406050312070f1106120a0e 69
    0xa11150201c00c60701c4c810001c450303001034104014055808500c0e4030b02d580c100b004038481d00040402d030000c64440d00f005092070070012700d980d40f50f28242c8003d01078156010241e88d4158203055040f10307904001d05c0064158000c1c07a190101139860090f4a9000942c814440480d52140d01c0c1990a41f007641041128000710495000840140c0840308110581c800d40c07000804901c030100040c100105034081c502101000c1e8007520002c0c08491900d1610360790366050702c03524080341000340680100c0100113800700d40c80031004000d00c42c000380003911503110f4424441c00250700c06100010703942441080201c50004400590004400e070001150480c010b44036802034040507121040d24a140b6404c010181c000b031303c0040d400c25400d0144078446010b41c5011406413500b2140101000702e07901c10b100232076100340d0105200c1d50204004403a09800b00e802c840c40240c0008000d00c5200460a01c44901c450741c0021540000b00050382d00000b0030625041800381400e10014031403000001034680d9076028 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 482089388 1250 482088138 482088151
    0x80708090f1e0d06020408060901060f142119080a030f0e0c092703070209130c030f0f080a02010c09170d0305090703060905160f121e080409140906 65
    0x122110031480c0c0c0c40d00345000c28219202d44d0000d8645603e402c200c0b41440001c1d0303070388203150391144010711140507008010320150090122841043d50080001072500c1144180e1540a2180070b15420303120600f03000d035641003507104200a24013022880c3c071802c65441190b1141c002440c100000f045044107004600d4400c1d0b00d10000c220400d00d1000304440300b07502808508031200442183c2c2010003440b080e0018030440b08000d141c484030740c1d0051000400008000c0c0000039290300344040080c400182030000d80742c1007203032441035807c2c51400f070152840d0400c02800c0c00c0c40200e414248164150085240708d05030369150f551080e5940b55107080c034030280310340d180b06400201041c00701e684648d0107603601c801311804940d6074507945d84602d01218644001034441350810441752540c011850503080040008683c3e0008a030f250000c0b000302c05540800040c10f01e000c10045521010f07100400d62942ea40014803599070b20b075140c15031401010041854a03042450000042e190381010a40d240b00c1d10 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 482090638 1250 482089388 482089429
    0x408030117010b0d1112010501060c03091401140c0c04060b09032103060d020a0f032306010602030f030702031c060801291507060e010c120b0d030305060409080708090f 74
    0x1c3c09980d0300f524555144010a0304482c007006e110f40d18550074000d0724001c0900740ca071102485c4203410000e00300d400b0344e0401032070051110702c000d0315a40d001c0414540d000d00750000c15200e80038690140c1c109080064030780ea01a040c500302042d018124401084040c108800700c8849041c1947c002c4d4000104080c40114104144005481401c00e0300f1541c14a510041c01c0501c200c0c0c0340c400c18103852980380c0054610381c20a101c82041082040d4120b002c0c41c003904020308196240c2180255203208641103180d0030382003c004940703014020000c0e1100c984000d00c0061000c9285031300340d03000341a10300c03540c0c02c03c0d82401000301100302d43c0c500c4036640701008205801c0301c1d5000020300c903d03d032080042c034034208400c011180100d101762040007004c42c802c1002003041240790030300a14080618100c3e882c1585409580251030381c03030b90340c0403034400e615040c0490541d1342c0d200098020001d0391005000500000f960754108000c1000405030580211054032510000b0700a124045040c05540341505 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 482091888 1250 482090638 482090659
    0xf1b0601060e0409050c0f040b1f03150305030409020a03020f0a02160b0a17041103060703020d0605010905030307030e030124030501050c040e040803270d0f0203190305040512030408030117010b 85
    0x381800c51f403c518003100948007140c045c4201000c20100305403181e00c1e10f440407020450f140182c0c0d060141c0303054242c0900f5810030300341c1141c4070540c8030320a921410080360760001c0c0c003803460b60081e0140c0d610821800541034441903142c50194451a200044044000c2d5540700481c4611031074090754480451950340c144080a0014072600401c030141c001e4401103400c1c07400d5035544e50200f00c0c40b4820b1809660250701c581001074210140d41040e0440c0b03060040c0c0004c240219240001911842c941600e80400f0b0f0761000008240107110084400a05400416005400000c2c2c141101c0442c0d01c00d0000708080e03030380c1000c0e0640602640c041c8400500003800403e0210340c40d180a950003445905160701482000000d80401400154040203240c02190b61104490b4100c0b07111340d0303004514001b81d4a0b0215110341c0704007010020032203c1c14140c0c1d55000c2070911800700403517510031042c012003a550f130410703040c040b80c150000d104103207000107080388210140b00107006122041c2d030041e0010811 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 482093138 1250 482091888 482091913
    0x10050108030c0f0f1b04090507031b0f0e0f0411060d2007020303090d05100f0509060f0403020c010f0c080c160b1204080702060c0d0e0f03010501080c01050f1b0601060e040905 77
    0x200c645d03441d8656000351145103d030046201400f602004500c11081100300d500102603010118245034400c108248108004204002065a40c0d07980f00f03a8510200c8101c0c3e44030b01e82050b2024072101d400d40c100c0350215481071b25000b50361003d140c031a030b13800f21514403d6000164031000c0c800c021001b5050340050254010500300b0350080c2d500d0610034425200d03480e0b51680450121110500c001006640707440034820349200521066410100500d0121010703e8a5100a555035107006102030400c031140384c80341e0f070f100c6c4501c884a0103da03200c1d414640d11424a0999a84c40010a0070440b00204c02c05000603202b0804003100c84d041e804e0100c1407041d070313582d450f071200c9500000f4080c0d03004402088800d14002c0c2c18800c5109000c1c0c01e4480a10307a0310300ca401e018000d02442c0a00b4082d80c58139006001e540f900041510036003200340784c1207a80b080007654505e401d0007800b101a6845810ba801c10900820100b6184d050750a40d580f10800c08052000700000d4a81040c0d024080342c0184054502 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 482094388 1250 482093138 482093173
    0x906060f070302030c03070f03080105030604020d0809010e040f06050a0b07050d030b04020702180103051603020a0e04141b03060f15091f0305031c0504020907050c10050108030c0f0f 80
    0x3081c9000b401540d041400c46100f1a080d82d10080c000c8038040306202c144810503400c80141805400c05034002e04162901c0d40c0440c2d0080c1107842e0242c03881e00d011455a003e0380c4144810100d112000e0814015051007500000c040c2445000f00f911444040750003007003241510b810f9907041e5422000900003485108029002441c2d03030603507903400a408014150168880c8406c20040e4076400c240580b4941c5141049818012200c6040d40152503a09080001d03a80f020002802d0300c2c40f031080d00c101c503141c80c54040c1e80c00204647c03051190054807021a404410301c120821f0440c4258291030040d42c1d401e5030225114003c5403d441d00b00d1200c1480340d0349040101046522110a0388894a04849501c003460b00d600b4550040721103500015400d403900f0681542217881180581080c421401c280c0e0014028002c001e00700c1c01040000b1030780b00e01c610400c0221080040c2441402c0003d5615461801c0c0c0380d50084805480b50b214809c01909410000074000d0701501400024006642000b91180c0c03 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 482095638 1250 482094388 482094397
    0x515010c021c17070807060b040c1202030a060e040507090c0507080406111006260c06091003091703011706090d0e130c0e0a060e010c030507020d050706080a0b0906060f 74
    0x1500c081104018120b0322903420001d1150b580980791054503400c035032a2040130392381140a054050784c2000d4406103861f401608000405030069000343c0c903581e41d00c2c001c038000e10459002e048002808400c1c0010300074040b03032007019103514520034817412001d0034003074541e80b05000700117012140810040198a204032072001ea881f5080080d81d00440c1c0c414001d2040e688180c0012140a4640401001c2c2d0b58004801c01d808801c82c0c0090825005644000ad10038090700000c3c40c02200ea0f907001e004414401d9120305452640700c401a44100b03080c09030501140c100740241102c5040c10040310800560002d80540b08503071040c000c088000c0c10320b50454150410103c20f41c1c100c101030a54022100041c0207585807100207075992480100d5810030045d0072981a4404d03418004d80051159803030740e0007000715489030741500700b00340d9408661022a8800043c0d10001e801802428404151141c2c00108103005050280c02484180d140b00d080020794142902d001d580000c1c10800346807403401c1c2c0c03000f80 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 482096888 1250 482095638 482095643
    0x313020913020d0302063108030702030403050f1513020d0201030b011205010801050907120818010c081c0f11070210020f0d0e180609061513090515010c021c 69
    0x744440040369020610603600120110056080312003008520015400b0070302d4a0015545001012101c282c502c01c1d00590403400504041d80000004443d240200110340c01154020100d41000090400351510f81d005002d448003110030507408929460b200a840705c003296001401403403244960f9005400070101d2020050601100c131504100655140c41800d008201140000c9107510b00307103541320b06100c001e80140d001880c8403110680800c903030909584020210305081b084030054680183c1e000d0003243c00003001043c0001e840c0c54054041078034074424201c00c04050260810350001a001c0e1159170118010100c0c0501400c00545030146610306080c209006130b03644400c070802d540d0300788035005c034101e004140000d410b50586c3c1006a500f40841444002c00806400c2440005444410103405c19106000420001c900306411303400311200d012144040c20382e0380d5503c9100002509045404003015520704004440307550044280007032055004203c400200801c04102d009520b40300000d = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 482098138 1250 482096888 482096911
    0xe06060a030c1803050a05010c020a0302060a0b0f0d2010051608210f0601020c1c0201030f051f080115120f081b010e1615050d050103030c0201120203130209 69
    0x12a20290f108030010b0040d5000380302600728010281002402d43c0c04400161007107600450300080829030104031950401c580c0c0f5404281244010000350801003601c50407544608245041d408012041c0305032101000d92503008003042d40c0030740c20405942108403140011480410411242556030703032421121600c138610319070400d00030081e4110001e0303052074120650f80e51041881401900c0040c4240e005a09100a10715440f040001c65660458113541800c041c00e641102c4085a0203074207c0120742c078080d641080310313151a0b0301108180c3c581000031080441400d101051841341802000002280c4c0340259840620f40070591000c080e1411b01540c0903042c50012a0001d000d00d40200348520020340404500241d1f512146d0845c0d50301c5074080c1699204074808110724103000b020300100c44402441c01c5511804140070f44051181c01d104080c02854000040304060f00284035aa0742c5000b0b030303600c80441c6030003900e03401248420345048806400111a41005240200d01d46912902e500790 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 482099388 1250 482098138 482098157
    0x60503010b0904110a02070302010210050603071710090b060a080f03090f0307180b0a0803030f0a240f03060c050a080112020a0e0a0506030111090d1401150f0f0e06060a030c 76
    0x45081c4c40d03410040b451801a00105000c10035503078100014150f0b038814400070000d505200b0f00299961007248150365100c09a1087e0311014001030000b0440703009040001e000e8035066181c00b84115000f15410f5110304103240d030100381601c00181d0b4010140313039000114613055680c0c0402c8416101c141da040c0d0315125190f404540e5118007090050306070b10094001c2101d0032b8440401c0300380e0001fa08240000c0d4014800c209030041e1800045030407040e11440041d10f80a2076460740c0e202c0c10340c007450420f01c411080b00080c07880d0401e81c0800840c6c0c001c81082168900f2001c044440c5c0c410f000300400040c1d10000140500341a000002601c1d51008020700c0007240c6d9030a40401429080300c982100a65520410840c0e050a00510031400d20400002c0d18013486500000d008500d1032101802c642c210421862400390254000c4111000c44842c00031101d9480074a200c2c426058002c580201c0d10b0300c10005905d030b045402850040030010196801c06400407000c030300801240c0100401c0203451030 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 482100638 1250 482099388 482099411
    0x612050705040b0a081b1f05070b040c120f0b0a0603030906050c03040f0801021c060b070b0c040807030b09010b010c08070308091011220e0105060d0f02030f0403110601060503010b0904 81
    0x81d800c0781c3c400c0038401e201200c0c00401000820700c7c3d450001c00c1d00b03060340710264040f07561020071140e07940c0d801520a1420746944c113000c0c20102031900011700680705080a40d06000c20001c22365201845514801d4960743ca820b10881540c4a92000030042500020140140fa0160b4060b1280005440c100d0b81032981e11300200c0302c404100c0e031040103241d5000580240c10303803504c00d108170820045403042c04420b01d40500502c41d4400d410025081c0c2070000301058400000c1803c6078004c0a1400c101c41c415512402c000102c841c0a032030544c503545c1783c410302d120b00e0b5010305010b0717402c0c94012409605000702500c0c1610812001404102540607940d0344182c900400d00c100c6810045801c04d0680700c0c0b2060080229590080c49c456000442c00f56041042482c8082080d05542c0300b9140036880c1e5510107403d1014000088040c04e0030307030000c070404c10a820027088041c4a01c0c065580c1c0d02d20b4008424101e51100004c1c0540c500050741040144006a003600042240c194040d200160034506030 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 482101888 1250 482100638 482100643
    0x2306041403091f11070f12020409020d0302061e07090501031109090412120b300604060f050606090f040c021f050709150504030312110c06040302010612050705040b0a08 74
    0x6064403c42c0308001d401c2d41542c00e0303210441980064000c80104400c50905141a5036242c0501c2441c044140f150302000854549400404000394064401134140e01135150294845804a41440c000d0804100b00c040e908949180f2a00494594480c4401c1d20f04140c01107001e080d038012481d44030715080000011940705d10030564441c0740148404501000301c00f00003050001075900076000181440c0c6079000941d100818a100d104882c101c82c264821000b014043e42000720001d404103000d01001c01c4140182d68002100352440340c10108025602d0408101c3c4a020b60103c068000016903c1c14015040c03542c40758000541c1d0340101d4280004004205000448a1444080440d210420300415a42100703001c00a0420346034007200c0c410130076100920354000c510020301040300964804150380d00940c8110111031040015682e80c1c6030b1400d04a58590040e1000c600546c0b81400000e84140260010121150701002800c4203e1400b000c0001621301140e1042d4070aa6480f400201017808 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 482103138 1250 482101888 482101909
    0xf08070c03081908070302130e130c0e0604060501050c0c010305040627110a0b0304030c08090a08031209030a20072c060d02012703080c0109230604140309 68
    0x103420098460f05031200c002000300ca001740c186414036005120103506246005040380c2550109031180c003156490020324000c02c0c0c0300e901e0251645583c0c05001c036001100011702d5210b1041510244031259403403004464038420f1a02112454005c6c0c0d0b62880c080d1720907000307a60800d0040c40041b0342c1e00030130f200c00341004031200350740c10280c9407841e00002040300240c210007014074101c4120080728644040c000d59840010401001c001080d041441040155816a0b0b140c043c06408940350a464010090382d0394400000300702e0305c41c1c9200004280d64400402c039824546559602c0c510300a034049089142680d0b0413005981d40203c03140440c0c0c00441c0c52a800d0801c0f45841040340c4840486d862440f400005459140900c0b01e0108000150f43c118003042c1400e2160b02d8660b482c1d003012039003a1600222a04018180500091070b0070000c003054015035140e40c0200545420852040b800610b001019100d10803250020303070009004c1804a01783c445010f6242003620314000c031150026405651 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 482104388 1250 482103138 482103157
    0x32c06031b040b12011203080402060a02030d0c080603010e06060a06180302060a08061302070201050a0e180a0c0e0a120605070c080f030a06140d0b070c080c01051f030f08070c0308 79
    0x1021139404020503491090500405c00700004801e4078115880042c00084002c2000e07025000004400790b405200b082160800c0f01c04071401c0240301c9400b070303004040500642d1418425803c0c000045107002e000315056020317540040c4800a10b030b181c100d041d5004580b40a4a010844110100102603110500101441000b580d92500d65181c02c508000d614010381c0600ca8100344144030000050760480100e90b61071000b030800e1041c0c590f2000014400c400200d0312005001c02000078450141c40d20781041c040092a902c030500d21405070403d20036424040d10990188070390b01580c54001c0781e4150310a541098881c50b045c80d460700640c8800e0440d40c01020301c04003040c000010088654081c0c07240c070307001e4421030402003410480c001c0020759014a2400c05024014901302168906004107208560980c2c40403445807980341007145c0600030714045802c524540315541401c1510340c5542c42040c20750b0750059459187c458551142010764012302e208642004200713030040003003036204010b0300341c022 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 482105638 1250 482104388 482104409
    0x10f0e030304260a03021b01020a030b0a0801150e10050d05150106050f0315030f010c08100605031e0903040f08010b1503011202060c010f0513032c06031b04 69
    0x41c60f140100c2d42103030495002000e8405101e4201000d0441001c594080301a1716001d80c660341311000846400091041e04800d641c40080c0b076036010750301034019008601c0c01b180c2c05a40d603561500e00c14223035510f441290b44186c804440902141c4103070320701c060b00b100103070380b0704c0500d242c0361000f0404129800e0790940b255400422500038200c907036400580581200c2c90078a0808141102810356800301604a4803101c45110880580c5e450800c1441134020011009010900e011507016160310415209032030002185e0b040891414002c0085038041c0c9282d1031040c0f1681e20025036403888200103408100240010000001c03800f02e840036032070207002904000503410140e1401c0200c11107151204c006040c00600c010010b00d00040c0b9131020080d0181c40042c1c2c1c48118204480c01070008208011078030b4504400d01655950754400d6800c1030303100383c84035000030a5a412020559080b070a1100054a40d12038dc00d42038280400996044000b41200040c0c0298a440c170410f9030300700c1d4200301280d4 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 482106888 1250 482105638 482105641
    0x4180614130f090542040807020f090c090415050102280c090606020c030606060901050c10050c0a171311060903011407090902040b091c0b010e250807080702010f0e0303 74
    0x10302c65101c1d603440703400580c0400d1000662800021740c03004030060028003040404583d80d400d40d03e80120356a522600201540e070310303141941ea42e000c907410580c103280c000c80c078142d060000d00504040d24030a944050300201020070025120304642c541181d00c1041c2c1244e080380080004006010aa0240c0180a4041003260a00c4002481c10103140c0d44103102e5440941440b8a580341e2608441c0c29100078a03089640b1074060001c40c0c0b4203044c04111030411071400b010010a002c0c400050141f17040c0c20345c0c0d09409407030008100103144e08251901c001c2d00d05034078000380c0051103842103030f0710054011741040d081ca07101c0b01c0040d007160521821090621511002c00c66000d502c015400080c0880b00300442c00c00d801c00d552801c07207000d003000241c0998603040442924048070302d07080c04400ea10101c05000c6684403540c09140c00401d603604080d0003108a0940c510580210384107150301400d5a40359980c2d507401f0012298414040c1003d0259503980360501000d8804c0e000e0203426103800d078000d40c1d49 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 482108138 1250 482106888 482106943
    0x503070b010b0d0f0506180916090e0c0d1703251101051e0c0d1e0f0f020405030a03030f1d010b03071a0d020306060f04180614130f0905 60
    0xaa843d050100900b0300c5c940020007403a9620f2020031000c51b01c4601e2902c03440e9a40300c50007444c1c8100e4400f0244541540c08000230400c5864101126000410041c0c0d03202204280c14400b01d040c2c208001003101c40440700040700710f00c460014642c401c0300350689194012a0346032004040e40507201c00000646004213524110400f4000c4030380003a0441c102448004070070107142c1c840300025241203050100010401800300041d04030101d0351120902003c0c3e04901c0c003000100400c00f28864041c03507402c20304030344040e010360302c02d84003120800b901815a44150742d6044004010b0720a00301e4685540c1c004401c103002035107031008440340950307000280b60070320300c0201032600b00d499005030302080d112140c801d108a12030b41901c0901100b1540940c43e0780b100d400140713982c060a141001440d40110f40060022502c500440c00e0f4005084d04118003034071810300140d0201800b010940040d200b424410710002154484400b43c90740ca80b0010f8081455507606081c40140c2402c19440309a06100060 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 482109388 1250 482108138 482108141
    0xb0307031b02030a2703120903030201050a0b1008040515010803040509010503030c031207111f051f060c060902030607030203061903051207051c0906090f210503070b010b0d 76
    0xa070324400d0b0006509110007110010702c54001c00d00315042c101c0ca00d542d40c0ca400401000043c01443c0d20814083c840c40005000410b601120b11003a8010740c2030130302007040004544607500d00000090000c00d00c850301c2000945401d00003910803141d51045040340003130310101c007070014040d12180d4040c43e030300d0303150a0800003490f9040c1c02c598840e8000700403036900000000700300c6070300708104042c505441d0348440302990f4170f0343e1000c4858650b029621159483d1000104074580388101c0b101c00700615150b450482d0903403d071301c00c5000450301d8109010300c1418000c2c0289107603a44200e0010840c00d030031f0340c00700c0c0c2040419900440400e0300401402294603208403c0d4181c14500d8403400d042518586903541c0d910402000f10003107440024403a000c0c05402c0c88120542010003501c081e41081001c001010140540f15142c0018503580300401d5140c0024401c3c002c86205442030804503125403503042e50740300c0106003151944010042d141c0080e2584400328020841c6120031902c40c11700c1c0d1060300 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 482110638 1250 482109388 482109431
    0x50d1d0c011809200c03090405090a050a150b0406150f0804050703020409061103040f0c0807030804090f200409110702091801020c1504021201020f0304080904060b030703 75
    0x905100d03200300108a00c000301c80d120003c89503005004902202400408808020540b81400011400181c3d10614400c000001c0507411301c00c0c2c03820000ca42d6110b0503680c03540744080c0018207540044150101103a00c026018031110307110b1000103232032250480020221002c41d070007004c0c500500c13040848401d1700030203050a146610b0400c42c503d0328003540c50944500d15800001c0c0b00d180e943c05103905002c4035500c4040c0c240041080745640e4101410a1411850080743c2140c040030003041c007251406002c00c052084071703031220305241040e080c4a40750b00980541003051034021b40d103000b06c206514411080001075a103042c0082d50701c031b09040d8008282e40300e000180007046010401040182ca0759201d80394840706e8200810b80c42c1c6030844000c3d01901c00c0c1e541555030303485000101d16803600b5171042280900e00c2240c1c01440d104030050002e00341c1c0102907103038125190910004000c02c0c07014008081c3c4103401000010314984903507030804950400e5500100103036840340c044101d00704804480303 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 482111888 1250 482110638 482110663
    0x1b05150f0403090902030702010b1c05011116020409050c03030403030503010801060f06140306010e040c0215160906081b18042d0e0307050304090e060f01060801060f050d1d 76
    0xc805180070b84001c0d010100320712401004603400000078032002c1c0b00b0340c450000c1110003405400e1000307a07100f42c003006241429065480707510f40040888401c0c1300408903202c20040c2440d24583c40340d640c0800000700035501e4203460030b0251502c02c0005560500082c4040c43c440d8603010346035410710780c1003403c40300c8070b80081c4207041c00c581c4140402504540c10344036100311142215074a5582c040103c4d100c200007507120fa0080d04012a0b00302c5903402282d038031790345400c02d90550001d0b6603c8007009000149404450b004c04c02c052400d0040a1140c010b00f81d008003034580320a10b81101d0303940e0a000f980f0010300208070b16001c40c2468214500341c0140a000070000c0403850064144501442800701a03d00a1068994a607503240c0340d130400340103030703030240d9082801e6945903030f554503404000c1c204549040c40640142000150948060b12205058400b80d030754000050717080ac80b0617180c0b0803e0f04444c805010f414014400044c40134042d034401619010754041690703141088080c54100000c0d8078 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 482113138 1250 482111888 482111911
    0x3150c120702120301090c1e0807030b0414061c0b150a090e0d0302030907080f070603151802030709031b050a08030c03030c0a1e030203060907090b191b0515 69
    0x407014030035048800d1301d064401d61b0078002110350b99403405894a04030498036000c1c5803681c4034000c40f45c40d0132144451254245450520030450a001048200d64080740b05110326070001000c1840341c2001c90328100e2805040001c0c02c0a0030860304c40720400c40d01140da03182100c0002ea001c03c42818500a40e000900c0e10f0780701842400b140e140d500b41c590031001d094004051303010000031504c04007044640002d04990081e2610110350803807071034956506002d2440030a09210079808400c610035030000840d85007800d14600c10701072540300c2000c0e40c0050034405c00c003c0c4981010010801d801c0c0349070500c110380b0710380804d043d01e81030030301c030f9031058030b601c0044641c2003803040c4c3c2c0c000d8001004496001600c401c0403551022081405e44904444180c2d018200352401240780d81aa0564025401400211281d0429581d044003c1f111005540070b01c4621403402e00444a4010103240d4510003100c0a0500008070b11110311241d400c0c20403984c1c1980c1c0d03a4030201c5180c1c030f507081c030442558001910091 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 482114388 1250 482113138 482113153
    0x1b0a0f0b04140d1e08130b030105030706050c03120709030209251b030c05101d0f07050f1306180b040e0a0b0c1e07030507020f0d2003150c120702 64
    0x8541c5502501d402d400900140a50104020414108115032003004402c5222520a1f100c5103082c8460300240210b6000748520f4070042407081c040e01c2640d8a00341d0001c011071170511b10074003404201001030995030512402c40004801640c8400c600d40c82401c41c4c3c1d144410201078109011200421310190406201c4001c804c5441c1e1080707100140031a680500b8401110042c524090385410380f18074184101c28913200c481914016415945e511102c040001c46885a08a10003191185694824191701c90200580640c0c0c5040403100000c2e0b0005621700010789642c9c40640714a18118405040aa0ba50f940d02e06001440e00e031241110000044009000f141442d03030f140303140e058026207100852507000c80d0415042814030300c0403010350100b145858849640f40b8019255801c0341f0000c1740f00e40c2400c1e81c07100150030100c2c040020300d0741042c081d440c50b040040b24154040f0150a440d40c0601038011440b0b0b000075000b403c1d42c01802040c2105a4880c07080094410740390002d0310450464200c1e00 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 482115638 1250 482114388 482114393
    0x302030309010c050c041b11030a091818050c13150303080408130305060105010801090e06061203040305121909060210050a09020d0c03050f030901021b0a0f0b04140d 73
    0x1041d140410020309003d030381000705040084c030700348003403030301650080c100b039010b51240621540c0c00802601e00d403102440c1c40c60f141496070304c038040c2c1c0c00244000f82186004021401802c884140c441620301000941f0607000c00c1000424080308030151805e03800490300b007586081c000711040c07000240d042c0c200405022004030407800f840038800a0100b000440c0402c081c0710428086800b00c0314050076003081e607680ca00c1c02c1b581b160400d20403280810210b0b000080c21800303900400344819180e00280840790340c1e060404c04003020b40c2e80701103054401400080000351080020145464842c4a00c546036860309500c411807025207040c95042200f088030400c00c540c1c0008603440ea20398500c1000c556541c3c1c034082c0d40020103e00c02d0103075001c50b884c803200d028000302c0e10080041d41e000300c05503011400c6c0f44003110317624840c08000a00581c03010311803480080d410462201100700c005d040805103035482c400050380400381c0d00310b400544c5002034108130440390007044030440c12082c2c800038440e40c1c507038 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 482116888 1250 482115638 482115643
    0x1a0414010513021602090a0e060109091208091e0f0304090e0127061e1a0301050708100b1b0f07140f0114090d0503181e06040b0d021c05041b030203 65
    0x2450081c05620706e8030100e0354401281d00403400801d018422078107a5a515802607016000c2a02c09440c5140000d20190315140715072012403280b02c0480040221030b607240c01184145510340004d56682c06040700400d520f030002e200920041c00075a034003046485141c0013440c2111072000d80704240510418050503546d02c1c3c0d0100c507001e540c209100064a111001c4000c002c0000400d41801c010b00d080141c140601c1c103d0941040c1540c1500204100d5480140944440c04280c4d10401e030341c0032522040001e0b4150f44024031480c0d03003008400482a008c00b00b80ca2500c01408a07411068002500a0202e0038851080540c401822982d09036011318131400038004c000711f0b884c942207409002800e0f40a949800e4000340f04258014100c1e55501c082c645228080c5000c1c00d510b5208520703c90505401414100c940d0b40c000600921140c500381c90180c2c444003590003500c101110b19000e1081004080c0203800d030290142000c1008960f40c6081c0c07602600000911203583c0c003030052a40d0038805078400 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 482118138 1250 482116888 482116927
    0xd0f0e070e1312141c020307080a11040b0904061a03041b21031803111002031908130c030302010912081504021615060f0e0405101a041401051302 64
    0x3c90400c0c080d1565056208101445408109007501c009103050316030311070065000714400c2c0150b56410045440300805407058441034003801c0440307002444244221911100107014440005000080312961000006041245d8840d200701450004c010130046c821b25982c6011240e90705000b0a00e030a040c0600c14034281e00c0000102d40c3c00d500da50b401030400d8019421400c20018000010b03001a549141c640138556000d44820300481000e400301060318000000e864001d4070b0f2924111085540c0042242d400304006d02d100410004d040c001804146a6008200914002c5d4008a0117560034117062a2201a001c0f007401000340380f81c10000d0707416580c201c40b22900000c60700503a070341100412501c0d88a142000c041c0800302d89070b042108175000c561003d0300700d80302000074898882d694120144c0b0220112000703000c03508922030b04800807c45030711200c0e001c640148008181003029001c101121701c03481000700310b4882000144407a03d80520003a104041c040f2080d858040c403a5110182e5142 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 482119388 1250 482118138 482118173
    0x209040c170d1403131b09060504021806071b060c0606120201120e010b04240b031308070510090f1a010b0414030a050111071502030c0a050d0f0e070e13 67
    0x40003041121440403840512107412050750700913006c0d07280101ca0390380c51911401d0200d41c84d100000803e814680243d640c05012508420707042503404041c400715900c00c80080303c922040703409940904c202154000050300c0d4694445207a9210b0707250481c01c442841e00700c031075002c035040c000034010303170784120480c00782c0d208400301143e200c200700b2003075015100410718254854100614261200545070322592131703200106071942d20a0b0741d2400180f0512041c1d03070710030066040002401c045a4000020300d00b0a2080c0d04881e1801e001c0304100003240c09528003110040c1d6050110424403c0450140010b5440c1c0c1c106e00300c0c10751424601c4c1090740f080344501c09055031a08400b042c0f540c1c0510410b0b004a4110000b1300c8084408140e00005511403402140c410944014035048020700f882620300c61425001d049180c21009042690301d40c03c5164a1803d15071508210750000107680a6241c0c007a103410010b018480c240030003c10110f000a145840c1307101046040b201140d6540c941039060310 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 482120638 1250 482119388 482119427
    0x50a0e13030c0506070e04060e130f05100221091b0d050c09010602030c0f01050709090509010b1e0102010f1401051912051005090f0a1e0209040c170d 66
    0x34200e18040e5420124180c002c0c0c018068441005070150300700c0501e01c08080b0484041105680355101c02d100c180c01034420b030304104940c1036060001002020003003100c9001d01c0031582448280e64044059030f01c608402803800c041000303c0b400c0041003038070941d00444000060b02d24444154208950240c01001e0240305034105903500b4203000301800810552038014041080d190307100d060103540c81d0b20404d44501140300b805800340090340e040c41031600a402c07036503611b201a0b25000700e903805403002500920b01556103018811445c0e403146145500030904c8050448500b00c0b900000e8216100500b2006180d414000301904e00140e075041c00e41034a01c1100c0703408824900c00b16400c9038503859009032190355076900b160014004005010700c2241e502001c00e215980d9034881c5c007511081071180e400e00961001d0a8140011910302182400003030001e40d01c80000495000182403a40c01c1c0c0e4151008119404c060101c0500b0742d031f00e40f00d1400c4000040c160803180040003481c5201e9050540d0031130 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 482121888 1250 482120638 482120671
    0xe06030a0b06180307060c051c051c09030f03060311060a0e060706022703030307121104180f060320010c0804150e0a08070e130206160c050a0e 63
    0x24140e129501030304018001e1511070300c844010000c0f284250000900c613118100c2e00054061241e20000d501c664004050300394a0aa0031101c1d50800300c407502c44c018007005108c0140c81c183c00c4d4403480c08045d910780d40860850b0711402c01522440d8000c0080007058100b420500100758030360044108290151030450f82d0700224131003103451607440f02c02603034400d800082075070502040c0c1d005002228510003000d00302c060312040121030b5103080f251594064005000065400e402303000c051546149907040485c070480982105103140d801500011074074441c03c03e01d120340500c02c0c407070800e2a40041e14104401c40c01c44d220008101c000d21105d0414055001d035520807030344075185903480d041d4020303001900d480d00e80c103546040f20780d05070b204000100140c140e201c840c41c0c03040080c01120180701c05403c030f00c0e00b4460081c6036040010259102c10f81c4440e0b4903401a203500d0b0051600c00381111001084560b41e203024840d06481b0352001c1c0c0708030400c160501c03c2080d10846150445520503240616 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 482123138 1250 482121888 482121901
    0xd0c02030a081612031406040b01090b040603140115020a02060c012007030816081501110d03240303050901051b01090b0603150f0c0f1309020a1b030e0603 68
    0x100842007034010302c1850003040c1ca00440e540c6200d030540c66449800c900c81050070740d2000303c0c01c81d0304000b4030101c0305088102049082c10076a010388841941890443e03961626120962002d90165108800107070f40d40701c0001c0301503010141c0c1405084100e580c003448c9143c0361002580d44c8030308070010b03100b083c0004003454800300941c441d40c0c101041310011010121025014200c580000304141c010070a0403000508514030348c0382c3d90f40000600e84074540c1c581c40711040820f40848070048039050001004507401002810000203991000b00d960200304402d5482c04c9003c0340501010103044c10100c00c2051000981180994000401c20b1811076203956459125041c0c0001858010700c065103040d9400c03040c80802d141a81c85040150101e54020040101b00c80203014200c1d1040d4030307090b03400e010403401c000e4040180743e000088142c2e030f4142426140c0c0c01e0070b551100e42c050529140e0009400c03202c5500a4440a04040010ba00ca0000a80d944010701410324803043e043c0f0440001000401 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 482124388 1250 482123138 482123143
    0x5151929040e0408070614041a070509031b15030c0d02030604090f0506010302010311040b190201020c030301080601081203010b0a080402060f0a050d0b27060a12030509090106110d0c0203 82
    0x1440740c80d00c2c942107810982450328a60307000d11030559040f8107010300a403912441c0c41565000390b90041c8209001584500c00c100a13070800303030840c410068104043c240c6a0740401c8484010742003060030483c1c00c06414100a01802503001c0d01611081c180104081c042d060400c0d10b20004800da000b6a40703a07642c1c00083d00401110b031004200c400019540414000d0019500341603e100f80c808116100648291201d02d000d54826030494550400540c1d000200c0040440c89200b1140005030030240300112071401d40d0002d03004080d040c0c1c0070078010007a42c00104108aa03440031541c600b031035541031040b952664415a55800c0a221281b13011900715105d01003180d41ca86078607003a5a8542d0800f01d40144154800c0d400700c1780a5050030410f2406107419041c0140d160b900c03418004000f0b03400c1c99040110b0300010209036100c41d586030000350b044509040c401c2c41074803a075101030381c4401046c03c0201aa0042e0030140803c03000703039844005144001407440701c07107601c0c0c14040c0c1403011601c002807 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 482125638 1250 482124388 482124397
    0x13020d0e01061d13140303190614010c0501061d040b01050d0309060e120706200f191a1005190602251d0106020d1b0201200105151929 59
    0x100411841170880540b044c001c00618080d002155801c582c0c1100c00c5516030555246004030141c0c220940500541507015452001e110361280c00042860365494290034240004003c00340248440e8204110400025260807805841c5c11560a2800c41442d20300505080300740c05170006000c2e01010a020755540d003071007201c0640340c4500f100e01e81130311100000c0040380600700c2025040b0101404510b1220040751101d8803091040c0100101100084681401080510281e44444a0f505c030034542055415400b4812042c00b60303081507482c980000d010f40c0f100c00501d510703801d049841c41402850b60108034050b41211400c80e440b071001584411050781c0049a00c078500096140002031000c43c61002c0c00d03412076410750217844601c0128901501c0c43ca111803400c81c07590070a10000c800660080070420301e11444130610096100c4d03d10601421220103548a8540460045001c040c9260951116041d412032001c8038141c1c516001d070821003007981c0032560780b0f1340c0340301c000d5005070301e401400742d4 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 482126888 1250 482125638 482125643
    0xb0301030f05030d1b110304081506010c080a080114060c12030601050c01020301140916121d0f100b0f01021f0b0901030c090f060e16050913020d0e01061d13 69
    0x300012183c610814003030b265a8030b9030310003090000b48401c6e00804c011040d41c045440c0d036806040845400031403c40c1c016001020b0781d06006480014501107041c250140c00c912806031203d80141d414901a49980566440c842d80b16503001c11040103550408105410101202e112403034403912007000507943c0f40585031042c003080d803011000080c2c003800c0320742d0345010f403605840e00e810989480e1a40e0580003522041100480c4000b1000400e59003581e002c4a001c10b094040f00c2160001c075520360f8202842c0a0401303480350b000110500d50a400b9114045807503200321400a5604050170010391146101441e40e13291110101e050155030389070b0741002541500007050f5508030b41c1c50b4034100c042d5a082d03000b004180c0345090b000c400241181d20a00c0d05652041151040035a20a4005c18032040c000360800c04014050000c11055120202d800401310500e00300943c0302c041440e031a0b0304503120903c000e201c07031303041c0002000b031007000c3c540040d68000c4004070700b000703a0344809402105c1ca0f40c16100 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 482128138 1250 482126888 482126891
    0x1080a030f1b0b06090603031617040e040308090d020c0a0909062c011104141012181b0f0b21070503040318030b0a090c09050c0913060b0301030f05030d 67
    0x40c242000700c01c0103180c2c416507089070016415206c100506039280204c00411403103d410380c2000010443c08902e161b841c0300d80322405072500f5190500301e0081c0800b6141100030407640d80611445031405e000b95a01d42180f4402424805128400a02404542d1044000d1117554008090501085070000d11600f10091200c2c6103924a408000504070202800e66505528003202511000100300c21201112481c94010115808040c1004240c03420024040203101c034450380d004040085014543d80a84110425103000c592820404140c02140c80799880c0d05100106c1401078240512143c026a640c02144503221415000c0d0001d03940c0c40c04030212410704900701045207469000f402144038a1181c1d03a4801c488803004a51244150135010003400c44a425002a000c0401c0d0b80c400d0b58001d00410110414582d51000b01c001c0701c2040e10a000c42000004100c611030403c145109600e0002030000c11280d4608140031807280418040244013055858210382404010410384448446040c0c0 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 482129388 1250 482128138 482128187
    0x91e0106030c0210110403020a06050c06010302040b061c1d0105040c060309050a0813050109090b0a05010807020a20010f0206100506090112050f0105090703061406070606030b0f0109060e01080a030f 87
    0x1246403054000c7e12081f4803802d0042d8010507900c0c4103005540400e50319000412050b4210f50030400580300309624a50489800d01c4130026942c1182e0590342801c070340f071000081e2241414911260b100030016104100c0c0e0501e400d2000042100c1051011645d1920300011030090a19101e4188010904080c02ca0140400c3d107184101d0000d0384c41044490076280c100040f50769420780801e0300c8c0c465032059031240070218104403a5015007541c0e584448148160344450055694202daa41c100c0c0500000041080c1c4111001e940c10003410280d0403110700003011f00b41b81018105403460038070701886010344804109000181d0240e005900340700300e504018003d030314100d01031501e83d00c030074031600303200e00003400118210030f000344518030580385035103408503807083c41d581031009990004074201c41c1e8a0b034480d400130118003a00011802010048180042545409105130a03103191350041c4800303d01c8540100114800001d03900340d0a40d0500300000341d21201c500507940d811a080428400c0d100480 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 482130638 1250 482129388 482129411
    0x9060501052a0f03030711010f09051b150a030f0506060903190c0b0c010b130213050105070c050315040b07020c0d15060503100c02250e0421030b091e0106030c0210 72
    0x1030244a86400d087c1c002c0146400300580c00d819a44246009032840d0000711001142d82c022540324400c800c00030708038030030703081d51050149001d070301c00440c59000955544015415800318040e80e600075034101d03896400c0522020010340c4030071104000c8980d50204682e02810000da4070f05c010010101100860388490940b1010f40c06450058015481100c00069000d8010302a00c20340d03d1114264440c1c000d00b81c240001594554007840b010b4034915156480001c040d60100320900701800e000743d100e20103003000c0c98100c20615001d80000103640010081d80469101e03035002c500d41c1600420000301201c80c10480000801503070b0041034060190f0960341048400b1030b080f00e80001d05540c2201c10074a0500e04000c44c0d10710520114059881903901080140300e07080059820074081c2c0c10f14a4602480411840c2ca80c202c5d00410300841e440355140340a070f141030f43c0030740c1d8002c601a40c00d0720f00545521400c0701400c1c05000e5102415940e0411740c44051080080410100c0c0c0640100031001a26 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 482131888 1250 482130638 482130647
    0x804030b01060f020106080d0507050f030304030c21020c0d1a0709050307060806060a0513210b06100e010318080304050601030b0115020a110d060f0609060501052a0f030307 76
    0x900880b0041165085880441c5105105000c1241c0b854405804030307040101049610340c1c4540e000359001c0c0319800a007440c0c4a0300340700850117144680c503507100381503161a2079130750017018a400c0000c10b80d804190281c4950045000000110b0031140c0001d400740303034509040c95062000d045204099600b0070000d8450b000188071054800c11021545000d40d83c01007155180c3c03080701d6698100b0380520210b0107250084c00a0100e40a0300b8020021040c0c854907200c0741020f2151400d803d900c3c2078116103080c811442c0e00f0603000740303040e50050001d01803088007800f500540a40c4030704151b9202c0407018011000005502010f03440300c11b641d6641000c1c03c145990701000e000c250352143d0303840000035403c0c2500c01c003800c408400b0b40103002d5001c4951500221341c0d0044d01c5540d0840240850700e00050030354810020b0081c01072000180c9581450715441c2181c1c0385400c42818840200000700ca03205288481c060030018070403600390300e281d541c0c44841c206049001074045c01d100c00f000380450907400 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 482133138 1250 482131888 482131891
    0x30a030e0105102102120d030204050411070305070b1005030a030c140c0a0b130e270d0c02040f090803071106071e0807030914010f0b0904080909130804030b 69
    0x344002070046031502112080d24030014401e044c0d00c4d101e05004404040d21048040c034942c3d000806c600c0140050701c06950601c00a8094400020b0b4001400d102c54546445020800ea4002c04c9540c10114969030250092040c0400a030800e804800090701e0100d500c01c2c010042e04000e0b055503c800300300e01e0054285070141800301d0344882010460040b61030001880e40700b5503c0203100380066071504a85803519401505034440e49c06606001240f003080b1113940c940142444131130b17980182410f140c0814000220041c0744903c2d040b44080c0c50040394441411400940c04890000b00a05080c00030002041d0002000305855400700402c20502e03080388404003904401010780300140c0d81e50f50202c9030800c072016504044a4000d00103c00d07180300b0741c804e039070046240c1000148c0102c00d48581e40141420300d0200e85680d1900000d041030b00407405030f80010001079445841e6418a561004007500602e44000d0040c4018000900d100e05103091001c007503a0003c1320725950325141d040c49070001c1c10 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 482134388 1250 482133138 482133161
    0x9020a080112081b10050403050309011d03030121050d03020408120c030706020a022506091403030f071506090203100b031006080711030c030327060601120e030a03 72
    0x25490088102c1886030550020301d5a240c030071503400c002509503206481c411907204100200300074210911030203001d1030180e2039050722031805111450a50317820b041d1030100300b84420705075003001d0340c00800c0e01c0c10754000414070540f00020812020102114100107001c0d440f07101c1c030303684880781c16600600540e8015070607500d610741d0140384d201c3e15109001140c0c1c3c0507802040841c0214406074040c000305511407055850301280e00c0800750219031981c0504803401d4105d5008c0208540204011006000b40110754004a0100d40080d41724003c41d0403c21a14100045240c100400302c1400e03a003449800c1020000d60780c498100000039041140e20140804108401052111601050b41d02c42d0001c005034480071070030680c00301d4082c40f001c0e00c2581408072211042400140c2030001e410146091801140c680c84e006078072407100c002140c503660f100038482c0340b402c45e146004510160f01413800e08001c1200f08606006070010701c2e030600d103100036000c00b244180609a054102c60005507 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 482135638 1250 482134388 482134397
    0x90d061416050a09030f060e01050711071505030c0c0f0f1b0913060b13020f031b0702060f220b090103142a131d010e1023030709020a 59
    0x21810700a9525101e42201079020503150f25080001458011109001e5031144002042e580c6200d80c20500751901950080080313184540480c488240802c154001020311018440706900c0841d0058040d00c0050b2a0310451400000c00f04419041003202020170000107040300d981c03943c603010ba2600c50781c9405030140c2251359100c2d4080585030680c051406182d100c2020149007509640d148020005c0d100c00d81e800c1641000e80c04800d910500c00b8001c080050940203560740790004d0101d0f040e803008840826010402c1c0559070260321400182c40790340c05a24a0265966003203401c01c403216283e04060240707515998030100b81d410224024213100075081e00c050000c0c0e10b03d040844404041286d101c1c071071395200545045001e0002c0300c1105d0440340c0c0c40019140c090010a003521a1115400110040050740c1540c441e48401000d41c5004150a000c09138080c2080c40914000b43c074603101d004200c0100f10f2920441c1030440b02d440d914080000d080b02c94140c1d0301c61b107280c040c0d0043d11444022a = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 482136888 1250 482135638 482135671
    0xb04050c0d080d230703020a0c1704030605010e010b0307050714030f0705010b120309040b0d1a0712020a0c0f0228080f0102040f03030f0909151503090506040206090d0614 75
    0xa0161001380c401c860105420550700e03a259a000c500179007000031041c003000720b400072000120301c00d02c07020301002c4042c00080c5d58070707030841c14201d00b9120183e10074541c0601c8800108580c03410321007681e030451414030302141d030782ea05420310070b68010b81f0031074641090100240e10101001e01100501c45240700308004e00400c0c01800405c842030300404030f080281c0c0c1081080030040d02c2e09030710000e14444002c0110102c4009601c41d02c10208440c2043c45004440000340200c050b007144144a40f203c030b42c0c1c070952a16a14031001081c1c0360940000401c00800a0220811035a030181072400ba40035080519600024404440746c0300f854611501c000c0d8040c0100c000c0c03a10038107000302c40645892049451314545507a0f0f048a0200d02c0c815000304000001e940403883e500503000e40714020030768440c01c1102c0350400f107205040440c544511024180303040e001400244020a40662154044038025118154030000c281c0c8800c20b841300409081c40c0104851654128490080c018241c1d00841006c2 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 482138138 1250 482136888 482136911
    0x201030509010509070603110408060c0a0809060103030518060d150501030b030708060c030a15090b0f0402030f042a06031a010807080f19020a05070312020f04030b04050c0d080d 78
    0xc80c3d10581e50b010b000e41054034144042402a001505402c040e0300440389440d03a00c10300c0c0307030030301d0800c1c5c038019031480000940d2700d04564030802c1c854110900c4800307040740d9490740d42c015104d0f2082c207010f000602000e40400c00316945401c29074a442c1e0f0f00d42c40500c1a4007480121101d515040e0281a02003860692001c00c681400039845090303074202402002c00340c030b907400002d81a410080000040f280c40e10300d0300f600c0360f0510030514001c024956001c1a15080f0204011100f060b00101d079004074414000c114402084120151f00641c01a034038003140c088a1800c003158081651405a4070f1811000000c1c07003561680c0403518005400c0384e0f611854500740011181408241d98550000b0b8160010881c0505031060241c1c0000868003010b80c2c00391495010010f070f82140800f200400c90101304c4000340754000d41107100441058008510b041c0009020101c180140e0001411401401000a08000e41003000200000300108a9400b0020f6031500e081581d01810000c0e00300e504000038001c9 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 482139388 1250 482138138 482138141
    0x1602010b0607030c020a3f0c05010503060103060306020c0304060306090209090609130f030e040b040e060c0f0706050f180d0f0503071206061d030601080c06090312030112020103050901 81
    0x10028002480c40340b40c001c2540b02242c001c03480d103c099900140b5a400050b513420390b04041500000202400c140240e003440d00c62000c011210b5031442c101c6581201c0170002200e2040e020306882d82400c1147d10b03615206c0048004141030b4200805152001445080c2c00c00d00101500854080380d40902c00d2a840d200da100590041c4410150020010f402180d51444c2010341c13107a11240604107080c002c00c20352100054401318890603800324481d002c40301c02904045c003c81c0411913042d03805000c0d107840500d209540e06001000802e0107900032856840c0030030004110303640c0c40d8018905000c5424048109920300c2401e60300008001280032100d4154200410b01c9512080c180d101c900e08101c1000c41510164002440c0104201211206e4100c1295a201d0304010340346543d10902d00c0c00980d0800c2c08a00001c80c0e540e4420b62210004000205001900640c181e00958002e502c070b00034070b400702e03203440030002c1c035031400740742c01720002c1082d03051401c0c1c00840c81c0c000d903001d000c242c6400d000c103070 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 482140638 1250 482139388 482139401
    0x11070b04080c0604180c12150f1706041412040b0309061b03070525030207050f0a080705040b010207050a03050109060f0504030c11031015030501050709290706060608160201 76
    0x150201820440002205d00a0b44a05884500e41c2000000000b43c04006002c03100c0140e1000d59040380003500384058034135055130002410310402c0030142003914890312a52400000c0000340448628054541403903424025091032036000096507848540705e0050500f01c0e0401c403808c061030303c02d608c0000c0217010f60488540700d401c40905010320351788548030222500c0c1d110748130742804004000c070040420903260600000304e5019902400480e070420701000020784210841902c281d0905800303001c00103020071007004440c41201c002522052980050b0705000183e804198444410b010001c203010040d00503020441c81940304008801c212094241204c200352005000146e06e1644200015243c880d03282045400504840411000f5000041580d0030340308003039000728070701d0b0b010010032009004140d001001030030000c2000341006618a08607a150380120300703480b02d1704601c00c1880e0305a01200d00c8550032080c06d1040301c0d2510405040400241d5640d02c04914980e4504c2e181c030301c18407409 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 482141888 1250 482140638 482140649
    0xa0f080d09031a1b04080a0204050601030213050f03072403051e01030b0406090203010e03090f0a120b0c04030b180f0606090a0906021c0b1f020d0f11070b04080c0604 73
    0x8140c014003100104002400411002c0130a0a11041010054400e0040c000600c21000184800c10b0284140700c02c1c0d56026049605240c014000001c00c5981c1c48444019554151030245240d80030800180c41c10080d540200c0301e0000540924155900c211064000a4440e443c01d00141d20381ca034602140708088012924502d40640050000509503407a09400602480340031454840382c0c0c0001c2d08680301c4205c90394080d4400100d80c0e000c0d040c0111135000003607044034140c0c8001d1038000c280e42c4c05408103100030003003c55100082e040c03032884e80c1504c0103036400c540030070460310309522101d02c804403031000e403030880c4a0210b44011380907000440034815000940f09859544032280180045d0548100c203d0344c8540034040b000300f61810f5414080c0050111901007006e8408805111408070b0000810401058400041158039000039441c00e00c071043d845d202049074641d400813101020701c0c502002080c00364400c005082480040a00140d888000584481d640610100314482c403c0d0f2250 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 482143138 1250 482141888 482141903
    0x506010f05060f030a0207140607020c010e0a05090c0c070f05211b2412010f030b010e150306041101020f0313120c0f030b100902120a1a0a0f080d0903 66
    0x9424202c07443e04007440c2c00100c100405810082a5501c00001081300086421141d00ca801080300d129410020304001d0341003070a000025181c2c41c004540700b1406e41c02458040c01c000c00102e261001810115900c0011540130b407400c0a40f40c4143d07241c00c0ca050b200e0b15204000041c2110401015090f20349101c03a6180c0c020414040c8420500c1b1021940301d0245a108100320120224507500700718230164041d200c02c240c0c3e680e4501c80d030710900340741041e00600030100c01041c0c144001050364110906550050818600598684c00c00041400c81a07003143e07014040c035000d04c0304204685e401c4001041c001d03000d42d08450716803101f15a4900911458107000218a00c0070000d5514400b03c201180d8016010604140d444035040807910002ea44115030300949030040007030300c61a074100c130b2020b400000c5065140c441d8141001d03d108c00701810b05004d5a036281001039661a8104150000c0103010302035082d030a42d14841440c00318007500c10b2417071b9030055070600c1d2a81e51044201006032580000c2 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 482144388 1250 482143138 482143147
    0xc0f0d020409111302030907091b050708040506070b0f16210f02030f0405011503020109050405060a0f06020a0c050d030f0c030e09100816270f0203070203070506010f0506 75
    0x208005080341ca00182c5038240e00c104240741540b6200c1404c42c079084803c00c0035981741440c1c0005480c04500b50300ca900081c0c03030041070b0300e024440023201402095841c03070b01540300c0c81d007410621410b1150b94001c1e41d11002c001880c104000742c800380c45200300490582c0c05520b90701c0345125880754083c16008000a4822020590144010b00c40d1204403600e1403400106000c007510b000049900569021041c00410303410002000001d002d01102602e035407560300c0310103185074000f0307000800382d00406104a0322180000c62548a10501a008013418002c4e0305250341c5c0c3c0c0308003070744402c10b101040e1000a0501c03070118907400c1141382c216144c0c1d41650340300c0e20307090f00d044220740c00c1e00c803c00c003142040114040310565650781d0110700e0280030417081c0080f581d850180343e18038040540c01040d003583c8041d13204000c169980c01401c0c00e03510240b01c111031802d41d8850428010202d8000320081948044184014180d00002408015215104454450341c903404200c99026580c410903074004070811 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 482145638 1250 482144388 482144393
    0x1216121b030b0a03021f110f1e010207110d0312241a16150e030d14130201030e120d050105100503010b0d09170d09051204081009230601030201020c0f0d 67
    0x850803c0106c0c06441c083c02e03580d881d0002e0310f05040c0c1101c445040d90b44685500300a1025110511165509040003107160840e02c1ea14241d441c00010001132041b00c6542e0b10300149401400b00302c2c10100004400c1000045010060a9400e0301054a90f0076050101003c6034403501c991310440040c1c0c7c0c48241c01e0910341d40e940e240c500c140900c50200c440702c0395540356082043c100d016958103800790030f010710744403080640702004031419000912050b034140c005001c5005c031070800c4c580d225902840d0106030400500701c3c9a03d4501d41004141d4030807400591406820030551226050b10800c48030900000e00a410803659030101b0300400c184800100441007049c0019804903441d0b0703204000e20000081002c00d80040c0b501300814002c0020740303d142700805c000c1c040c008000c001c010031000604290910968654600000c8425001140c0d03d911035402c2c030540f40c24241101007903c200400e51321b09103030b034561203560030720080b800351160030f030310700c041341b50449058110980250125111401d1074 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 482146888 1250 482145638 482145679
    0x308040e100302180912070b06091f06090512010c02190f0c06030e010f0501060c0201051b0d050a0212280311031e0c1216121b030b0a0302 61
    0x1030078000d80429030740390000042e00d030403513030480c0d5040e0700000c1c90592509034156418034a0742600c48007801c408020755800152003902c0305400c11b800340d84200d40383e61846e1b00c030030313045448000403210381480507000130390b10f54082c1c40d00042d070318255000300c807000c0480d50845c00c0c0c0c0c841000c080c01582002e4100501c51070034010b415600350251005100004541d1508200c503070050304003a000035120741c001034001d802400340d40310092292208000541c90143c0007030070244411700007410410006030440604515010b22103954001d8015209841d4070b5404c040d200d6842104490098080d0b241c0002c0089030410544011500040706108045c0740072165010026a50603c0c2040c1a0b945035000e041c18000b40185121304c3c0c800c000410b0a6140600d4151607000091841d07003102c4082080c0b04401080c3d5050741e40103920302032144002d000440090b40c0508412240d4844076203010441c3d00225070985220b0301c6140d158408004602c4035106021405500d804041d401c2892900c4100b6001ca10 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 482148138 1250 482146888 482146891
    0x30307020706050f040509010306140f1501110307051b0310020306060f0a180308031f050d021c051005040c0b0a17060a1815050d1a041a1806100308040e 67
    0x4100e020f45017036151000520004420782003038440e07681d00d142d500511114403010030341080307500600b0102c82c6015210041c9100c008044141049511694042d20403410019a0b0003580d003c000c0d078103c4030035401d50b800d0086250320f2041c424440c1790305c00200c4032a64801c0728014000034001601c0d10807005821400750b0f10144d010b00c1000855585408403241000c1404041c611a52031300d030703a038104030004c050340058400c05e000c000c907405201040503581e65154032040b5581690328010010419a44c4d0710303003501d00b04014109000f2060545c07401485940902c2c805c0d84075100a1800b691244034448040c0950010240451a82c0c0c540205903540390410b03039403200d401000101c505032295010030b003130114201c1604c08151100d2881814403179400c48d403800350030180c2d1000d41241880c1ca03481c101f240d101580d201d441080c00046404d00c20903180d02180d83d02440701086182c103003905200b101803003c42e0790354403901603400820b0712104a104004126038100c003d1a040a080800ac003010090 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 482149388 1250 482148138 482148157
    0x50c04231305280e190611040303050d0f0905030a08090c0d0501020403060614090414031902160e10030b060d060c11061e0403030506040b062a03030702070605 70
    0xd2440701409116102c0c010144120500c2c0202d20801d902d00c0c0760049066400f803009030a0f1801c3c0b40c02d0074441d07040003c0d800310001c04c0202018005081d820400c006010000462503401c000040100070f040c1c00000070f202c031500c8040100815291842c1c10b00440301d01090080c065042000296a82449104a590860060400d88040340303600400074455003041e02c0f007140c041c1d4002c2810000c1c000300d88180001170407a00d010b80c10f01d00b02d58000548442c00240010200c0400301d182d500c0d8420200b043d45c01c01a0410880c401d455500540a03565101011030700b6408015003102180e102c01c0c0c1308003140a2030028402d00d81150075079840141c224002081c803604802c2c1d00d070381400400e1041c094030f220446961110150000e020b090301e8188400144803080d0380c2b124600201d4004120784929034000e4041ca4005401c3d290b420004e006002c0c0705818a50004020407019109619940e596000c0340200c0c0720020060340070390215890703000c201c4180001d6380001500304075284c00340f40108118503 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 482150638 1250 482149388 482149399
    0xe04020c07051009061e020a170f0f07020909070311120115092705030a0302070204090f11030118020618030709050103050c040c0201021306120f0e0d03050c0423 71
    0x58803003021400c0c4000401c1d031400040d0250b50100b00c2103401a0304a114800c00354a441022005008080d5448c20b6071003005000465000121000c0e101c44800d454001252000703440d42c602c2460003c2d8100c0d004440c0030703403199203c03d000c18039003c800034008040369030009800394090299000c02c2000c1016401004e1655242e45000c80f08550a1603c400940410b600020b81409500001045081c2c0110003880c00d8107a058840045900082903c0310000986405681c0d0856440030401602c40c0c2040244403402d8514070781c0422086028418511038107a001b0000c1d0100f1251089640042a40194010341c2c10001e441e410300301032100340520500074045a20559481042604580d0700368030075520b80e00150062580ea00c1c10340121000b941440c4000c2d401c040d81001c5070b80d52014544070340307000e20407401240305200036581c01a044510600400304820441d418240c0d860750040009071002a00d00000501010340707040c1528182c80d417401c006015000080e81d0421820616080c00e039005 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 482151888 1250 482150638 482150653
    0x9031e0309060304050a03180f030f0314031303020f0c09060f0303070f030c02010e01050a050d0506120d03060807060503040b0a0b011b1a010812091908010e0601060e030d0e04020c 79
    0x2d8544a00450190303102d03c005028400486c1002020102c002822001140021070104003070007100300c1d10030940e81c0003210651004503a20b010b0390750216051034190701d46004801c000401d1a121241d001403401303034091300e42020008020980350700300c14034072541c0828800e0204842c3d05002f001050b80c3c000190840e4504000c075142c130a8400a0003404800003525500e0803000c650b80080030b002000d0003828183e081810480f0094028000c0c810203a18013a074450002d00c65584030810318517a810740c1800d6402e401104c5c4030040280150f8001c5a005208180001030100c1c410000c5a224640102d40c5951a0b25424502c0d0064070100d403115041240b4140040d29100b011190f65005a03c140c0350f0904641c4401c60140a0381c405a21051003a001496281208901c0350100c88c1200c0d0308903079840c0b034a80d24016003a103041898101c0c000942c078210210a04040000b4040d060307030b000740c4903003a01a0300941010340d80c102003690100042e0300c0140b48800340c1495000380180b903180c41c080e40c0e0103 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 482153138 1250 482151888 482151907
    0x4180e01061701060e0105091311130c030e0616050703030b09010e06010806030606060a0e0a09060914090d0e0f010e180a180b070f020f16090b03010209031e03 70
    0x2514810b4020341003080c80100c078034120310b0003403150a0080520000825207585410005101c10200a184044071030784015042d00b0410a00740400000c440100384008540c249400c40004005c40b004000101b031a045007000320f0440012070700c1c419100140c0804aa075004082180c058020650440626455141482c0f003a0390743c0b884a0302030800f8400340480c40c500030b0300040904401501c0300b4000e40024040c007a0a48032a011502d004100e42800902440d090001c03800781c80c1c0c603600a0800074031b031440102d00036003180c11489c0c101e41000b0040006484104002c2d031034101400150001c6404900b00c2c68050801003040c559a00341410711302c00026001021404080042d41c942e480d5450140c2040007000c014130070030501c00341c202641c090a4070035544620f48140050146024040c608030390144040c42042440d08051440c3c00751122042c1340a4025044101801a8240d1a0030400e00c840d2030300741442130303410804009009100e1503141c0c0f1900b441a45a010341c4038424082042450fa6 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 482154388 1250 482153138 482153141
    0xd030302360a0b070f060b1804140607110d12020d150302040524131e050f1b090108060105041502100f05010e070e0102010b041b110f0304180e01 64
    0x15a010312150040001440100402d002054001c608004414044003010403841d20b09001d0b000d90114002130081400400140d911100d000d000704070881c444100001c1003405401d0100c180c00b0795003226a5a103680c1c20070340b04442c42c044901140e51020781d203034440510a0030110719140f40040c0c01490a07544261040940d0040d00d1b0085502d40e20318010021802c241c401c49034001c60309280b17030741d9410b0810803035481e0082c40c1c40e100b0310505410001001066450380b00441482c141c0000041d040c241800d0840544412200401c05140b10f0001942a0201040c0d440b1091030910100703142c0801c00005446040002d0030307490401c10148408a80704989540203c00c029803900204500d8550111090554000492080b039460a00380104418004809560b405c404c0c1d0b410700e0381d920321102c00104d0052019021083c1d00509040340740302d0b0300c5860701881242d64160f588440c9010204480340d5654140c0703400450541d4001c1108002100d2440b4880c1c1240c4070b0080c01240b10800d00344102d0 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 482155638 1250 482154388 482154457
    0x901050601120c1b03021c0809150603030f0408070303091401050d0e1f06090501050d020102030306090c0c0715020609010c02120703090f0f0510110703021201021207050a110106050d030302 83
    0x10056441f580c0035569000080b044445030103014500380d000381c0741100c4e465444000c2c05011040b004103282c08150035546c01c1c07060b19204c2c004501a00c2c0c550b0356609409540700c909210980209102100200380038410b80c80028107081c040c0c41e0303603180096141c4201d005180c00403401101d800b981c21102514400d0b40407000f0100d800443c0891140d00305504001280c0c07041c2d2105210303152180a50f00180d07004025030341d00440c100e5001070103a46003401c0d40341a104030411580c4c18018014081121140340240d031002150aa00320344055a483c00007a0032551a2454000903038800707800c04200c07a1444005054580c464a480101155035041c162410040794011100344d0442c2041407055040054400640e10078600e44440e05060f5980c034103803110020300000c1e024840030b45102c0c5040101350121182c1d1090711040018500d81000000c0c010b0700651403401c00506845980200c2d9401400b82c4819141c0081003007100707420558096009511140040c611b54054a03c128004102211000c = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 482156888 1250 482155638 482155643
    0x5070512030a11030105030703121e050d050a02031003060c140309010507020d0c030806011b200f030d020c19030b010e06100801180c0203090402130e0901050601120c1b 74
    0xc507103906000d074011054078100c034103c00700f401003800100002e075000180d03001160b42112110309681c00490b0b040320086007a00b02c89404c0e0b403050409102c0307140e2090040903a4a01880104400d441d40710144003030f440161001c54030800c00300f20510106005030300010b1b184000341840e83d658020110300030002c0d0000c407464482e0342d649a04014074150140101c0d03851105502c0c2229141c012550003030f11216003d006141040030001034416400f0001c900300c00d485d0340110342028484c400c00c041da04003960a4100c01d01a212171503451030340e8140050341108040c01600909036503941c0005202c0000b603120409988048a00c80c0000072a46200c689400f82a4101c4100e00c0342ca000414045440c144001c80001c100b4542c0040000b000100c00703551807100c02030400308400c08200740482c07850080340c1c5507962040c400201c550b031240d941d5110750220303a1081e1040480d42d0f2009105400c0300c1040b608540450b80c0074040241e4140c2c243d015404992050405c10035a81008a40081000106108 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 482158138 1250 482156888 482156923
    0x6030a03032409200a2a020d1b0f140402210405030315030c210a170a0201150621020c01020d0b01021006060f110c0d030c0b0703090308010e0601050705 67
    0x50341400164501303408441c103040c0c9800e00d04a401000200305404400d4004600d581c0464491400c0585003d00202c0a030020103405464546003041e4034509004c0402054481c000301001543d008621081401c6980d0380c01048080e69003c0244000703903001803001040310b02c10641c0a200545980c04480c0600d00481c000d40d22450030002404501b040c0241240c444d600034010041c1d039035100c025004104540500000e8800841040d0328034180d201c0e44010000c641a0b000e4514041c600d001030b142102d11540203000741030084040c003140b000140a4400000c030808d55000d40050254181d03044840c482000600c1d00d02002180780c22604030501c2000200d445030318600c101d40c0c0c10008462100076081c0204a031529068010701000311400301c6405009003501441001a0180a000b2a661019000c8403080300c45140041c0b01d11741e101c20031280c02201c0804101114424414102c03e5541074496022030390074030001000f4400c00404082c10000d0811100b000100d05001908406000140 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 482159388 1250 482158138 482158151
    0x1502061006120b03101e060f0501030e011b0f0e04020c060a020306120604030504030606050301151406160c0801060e090a03030f0605220b03210a020c0909070311060306030a03032409 80
    0x1c01d51b0a0054002d005030501d810104140007403203d89a2160484100342000100c3d9040740d0109800743c00c11510744002c049083c1e42c000196500000c050100007400d903100c2003182100b108100803070080c1c040902080d485200050f45100341540156000000100f20103010f0003a02043c42c17900d04200d030210002640805d04000304003060240c4006007000320002e101442c05000c8484947c9440e00c240145805001d82204c0a40c507040c086a0111505003a954a101582d0602c070b45000060b01c0f94003500e40c03030480c3c0080e2040c14006a6802200c4901c00740280d0691713510100c000d0710b0b1200507407050799070b10300340040e580d40c071590030700080794401c0c0c0f8107000b4030146040d4070112002079159034043c3e0081a40c03420070f844256500300e6620301d0050682c0d2644450002286410680c03824076811116007421f11103503510011344002224400c151045150003a0740030310106020980b14940c143c1c1c000030064000a0098005100c10000030f0304105014104000041d0b0751282039104132141d950b40c05 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 482160638 1250 482159388 482159411
    0xc1b17011401060504051315180209031902151e03010602010c020f0721080409020403030c060e070b09060c010e01020307090e1302010e09040c03050a0605011502061006120b0310 78
    0x41c0030303401090395050035801c144c80c001c049002c10b00c6900c000d4a24030360365000086204038068100c40039044038036600c04c0311a17100d46168000e500c8000030340d100e8031540c41c00c0e4000510703c1c0801c0b02003580c058441990f21071800e46c60310454000d10202d58003504a014209208040032024500801c0c01c0d5002081c0300c160858040d081c40e602010f00a0b0541122005008410b4660504094100f102e4411074912490f4101801706000b117070001c403030041c00090008181076001341d15000305400b502003000740c2a464130580755924501c0c4900a03c0e294140a1100e09103406c5019103070111800001060030505450318900f280e204030380031008640400d0040c011000c00542c215400f45803280c10348003048446d0000f85c500d05004000030700c541a03500004040040080f010001194418101e5690842074a02140540390034099540c041c0d54105000c22910300c00900700d40500f00c0010074400c5207050100440f03c07106041044180b5940350021861251410424819013200c1804002401040038 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 482161888 1250 482160638 482160671
    0x1801120b04050a0c0813050c27040f1403130614090307030506090111040f0506090303070f06050f07030c080a0b04091b06020616020309101209050a14010c0c1b1701 72
    0x6e001140c8180340fa890000000703400282118107510100d13551402035040714000c1c80e040848010384856143d200301800100055150301d03564591052507500c100039503200410760b0360f00038039018003a405203125041107100d0054a4000c10140106800c3d49403500d1403011911700340056004440d02e0f8040e104005031060280712300354035003502544040c0b401d460a01da000ba6400c0c0e60103403600c5507200044000d03c0d40d80800440708955489001c0c01403644913410720200501044422800b00505000040c8860340304e44941a5604101d407034681603500e0f1040c8820050450b210f400b602300e65501e1003100410b49119070750399100d203182a200281401d100000741070020103000101b241c0e0740484240c1d01160040146d901600e4140c0318400351420950044400820381c4402d20740c43e0f4544003010040c4603000c2070080207280030b0086444c1c84a44d0550003400c80c3d1842c00000700043c0d41000d00030010f02c9454000802c0b0180410750341c0350580356205464005001030120500380c0d0764200c440e10100c1c40 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 482163138 1250 482161888 482161891
    0x30105190b010c170901020f060702070807091e0b12030c0606031b030706050d0204270c1b06050c0c03130303140703051b100f1e021801120b04050a0c08 67
    0xa00c0c1c034090f240550340d40c6100c0c0d0714240706205440700c0007069944590740300b008240c0000e610b14017121500c3c00e00302400780d20384150340290300782405115408980d080d4640a07d03440d1080c0e40405544030801c3c1e01108004040102246500030b0780100d480202100800107006000c030102c01a054901b404020580790540285a00604000300c408203501a90080ac1203000c0310341a00348140d44804400d00c1800074420341d0400c1c550b00141c103016019001c001e074900086c95001c018200013400b040c080540305a0300f100051049400c01d03003542c000080980e00010b80002440c5c1000d07050107111070b8003500711b402c0341203140d55143d801d01c0d0410606910942601c160846020403901d8800fa5450080c01845045509040303c08205071004a1040401c100c041c0b10900e201c040010100300704c103070320140980f08002c8040f14162681c42d11031050901c00c50300c2e91414404407130052001c0c000150382d2104101c240d401050f80c0c1d01032141c6180c80b60301030140f00da03226003000102c0f88020305029114040 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 482164388 1250 482163138 482163161
    0xd022a07050a0806010605030c0c0a0b041415010b09011815080f1311120f0703050f0f03030903040915031e031b0b011a0906071101020705012307020d0203010519 71
    0x3d0f0004016861f04030080b02c2c0c0210088400e80c4d501c000407a5a5850b142402c2c100a001144190802041c0817400340c840c60310b604500e003035800c0410402d1540d0700040702801180300c1c0302810400b4002d598000d84043c0c020054070403614000035601c0c40d2000c6901c40c10b102150104000d501080f000300e4116200d00d42c0910354031681030a41006803507030072607640c1140a05006688808200054600c108142800c80d000442200c000c1500e07460304a4841862010b0f0700b0443c411000307090b5a500c0048181c80c0326503841401036080500d02040b050190150f24100c00325507030040c001201041c0685108a4000b05100007c0d096222901d0018501034100e038213940c264180c8441c140020b01c0001546044500302c2003501504002c000240500e0301c030f1030b004d0070b5108000007800000c100c00d9409001d4400310076029100900c4d0f880c0015282000e4568040a00c1604011082aa1400399025000d180c0c0013602a10b81c041d4141d0103e0700312101501c410710a603405400c20b114242250107149245c00c0d = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 482165638 1250 482164388 482164393
    0x9060216060e0d020d0e040617150601090e0c071403030108010b03061e1801020405030f0106140105070302151906030302030702090a020f1e161b0f03080d022a07050a08 74
    0x85030303140251101c07605440c0744101b04110f8481c2005a40b0390b00305001a110300c0e03030b43d5008048a20710681c1c0e21030703000052810190380c680008100c2e6000d1640c150407999602404c0f409079903800103440c000d07400504211800029641d10344080c030000c002075400f80090341d000080c904c10b54810545007440003000d041380d0070042101d003408040408661900030080203500007032020f180c10441c4c0079020b990001601481110020101d0101c150003010441d21541c1895401d000304030700443c1e8a01c03400d2005805644080500140003003c95002540411455410380380350300c1c804112001d5030041e0f4810f40060348041180020f521f4801001500080ca40304214070b4460500040002402016410f000603404c1d03203015500800b10501f01c6524140189001824681c90303e01020b031140700400302d00180d800e188020941c041b90b08907000540ba00051482d08010408400c6800f03540034480c2c54140c40b140241c84014441c84100190210381c44102805170141041b05001c0d0711000d41d03011001a5 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 482166888 1250 482165638 482165653
    0x906030803072c0d170d021c05151e06030c030f070801030203071202010e1302070c14030307060b0f03010f020a030c0311030f06011103030a0c031a090705090409060216060e 76
    0xc040303e02034014961001c0e6894504961a4101700d80018030a500701c2a05120010358181500e4065004142181c240c0c60300c505007141c100c1c042c1c400c40324106d032030f440351107070f20381130503026260240d801e41e0fa0394080d01d02800d0820000d03012800740d400a550013516601c1c0030052003c841c01020700141d000146140603402c1d0343c9135800103a981c0c0703010b125414040703055003072000075a44201070650190134054005910592401e01003c0203500c6070b07c090351801ca0180c00811803402c0b0038902e1704143d900600a504007141174030b0b008018155007441580c81091010820720b9a103080c0604c201448070f42c40c0042c0c5507103104101800391a00c60391414101807514403449508052201501d802907002e00b040405a914140143d03400488030a005c10148804020894001070507004895000c019940034080700c103803110880280850850142d60241da0140050035661188014040ea4540200702141c0e00510f0b440f0340040303922040160030a04044619101480311a0150942c143c62220092061 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 482168138 1250 482166888 482166947
    0x8090a1205130f120b070c0305220305010f060302150a140309071d010f0e060607030c030e0d0506040c0602030307022503120c0201030f0c17040507090603080307 71
    0x1280864210300144000860454881030380644098090200030401d04010b644880c03640f850030051010807115455a940000c40d40e5100d0741400d0210f40d4540c07a00d905012700c0f03a101c4040c05000c4040d213540c0450b24200080490303030034020f05685019600002821605500522158134a980c5101d01020002c00201c03000c2c940c022900905a00d0418400742c40c4d40360201300c0f42c2000550b5001c0300c03500810007121081544c0c0020018102e40100d082c407036103a540d407441150341e0041110959809481401490701181c001c424082c0320521074602000824030b804005540c80c00054010703200c84e408901000b0402ca00c10680002401c2d05000440c00d40c607040c20029136410442603080c01c40c50341c140c0035540c0d054884400c500a1580034007241c40d420400180140b030344c9070065059000078240002a10805039500c00e0018501e5207a803a20005940d11010255120024004940c144240c9400040840c01e6200303520146105681040e0b0300e04000c2001444070520000c0e0703082080c20318801108 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 482169388 1250 482168138 482168153
    0x140c06090d020918150f07030902010905091b030c0901090b09030715020a08121f0609051014040806040b180604033b040c08060904020609060d060b03040308090a 71
    0x140c40c0d0484101039143e541d559110081c3c4841c24050700c2c4c510861010401042c21422403a109819452004605603a103010442c1584c03400803010380440c00c415424070813070801e01c0040e540099180250507031900300500004075036004446032001c09002041409040d0792140740c0700010241e00001c03a0401079400b000079210f1040b0b1143d00080c0e00c500040c26074650007031250444070b44e0002d01a5440705075400c05492400c00444103202048842180040031000322094001628101e0f0384880410781044180000c1da0781940c2c40c1350501c5080c00240c01d05040e5134000304040c000e11400341166081500e40407013641c6000c0c0010003142c0c400b0344008080c80e800203800e5403158144ca00180050a540410000c0c803000660a4519140d6580ba449980c000241213207070b8014284c80c10000c540d8a50012200c0ca9401c1c0c6000e81e0100c04100424050314040025000d1403000406079450f0041825401046680703691040051401c0401040141364210880550105100c0080c0500000d05d564444 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 482170638 1250 482169388 482169409
    0x12030215090d080a2c010b0a080105040c271406040c0206090d0e0109080708072c0c07150f090506060105070b06130605060703090f0b030c1603020c220c030b150a031503140c0609 78
    0x703500320b2020303030080c10010ed0003d050114150084080159041c040e92421040e90110784990080b07080c003031405000e03440041c550344161005000303814140c14600f41101d0991182103443d04100c480e040c0401c6d85001800000e000740745040041001c83d20b0b00700c4248900c000502c10445c10f240654051b04410382d41061650b000042e8011161740b9a04c600d42404001455800c803504645071910b070755020341469200c00205c60145007200c80503030704c0900456052040e2070740180803407500404141d0030700b07080303014010288401202007607007a111404a00c0c1600f10000035000506012000c00900c0c5020390000b002d80145e190361440c61800a403003c1c8540b00c0d281030700d8903440c800400c0c2014144203110303980001400074440354200907020b4201c1c0c0c050004608080342d051401100280035400b13880f51a0180c0c0001e01000003000c10560142105d410481001c428107072261002c0d00803007500d1038890095841442500380c40ca80600e40780d407400c03e50424550040004110144641e9600e40481 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 482171888 1250 482170638 482170649
    0x603060d08160c030f051018170f03160906020705010807080403120c0e150309070b0c070305061006031401210c12030215090d080a2c010b0a080105040c 67
    0x11035440c1c500b60003030010100c1a00003d420302e1010301d0048208084e1480c144401d50103842140c90b26100283c0520840300060382610320005c031244007400086151810024500c03a0309051424014a00c0c00e0030007660044950307580011241010b00344031078000e54a400503044d40d10040c010141808006007600348090550750034801a08001801c15210b40c0c039117200c2003020760b130900a07515541c5c0c020f031801003000959440369404111890300c000c0c180040d07a11660b0b404d030082403054542021101c2030b074407039105041c2078010000040017103001000410f00819201c50114003a501c0c09800a007220b5a540f541c0090b8001e0000401c020322282e1100c646603040503400280070795492911404482d0303560b00462966041e10161b0040c15004030b41414014400c0383c0c810803942c0e465550341e85680c441404e01c1c0c0810301100c007003694000740ba8001c2a20000b50a0041c584484c14061804041003000050b00e07580e448061001c0e0504050040070014a0402c0081c8440d040c2540c1d406950381aa0040 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 482173138 1250 482171888 482171903
    0x303010602100f020c0a031206050d080307030b060c010212071b11010f09050306010b0909010e10140427020112060e060d17130305070515221809060b0603060d 70
    0x460807042c072641c1c1150585e220075000c03204071141b1441c01034250004c90b011200391a107803c42c000b400d1306102d003d55031040d50080c0c00ca07181d41c1d00c8003800d4005211014101c3d030001c1c0c00340700d000b080020910080c240c400292070790001c189005000140030300024a40840d00c2c0107140499800244a5130607a0300f0f41c54242428018000e1044080360254419841907600d4810400006624407984004001404086d204850b50360380754422800d05680607038102c1c0d00c10900f880c0c100010344c1d00d2a01d640c00311100610107c3c0300c2d0403070f840e28031980b081100f8005d00594005440c40466800c1078030320140041548042c000a8038107904841d10070301c01460640611204070799841002203142c000141190660701080d191030444552040c220500d000c12a40341c801c5035408562803070403e00101c008510809502c1c9000c40400104006001000007c0b600400158000ca801c2c2001261007407034142c0d401c0005282d00c81d0f41421815a0b070500c1240740030790000c00c140a440d8840714119001d60790071070030 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 482174388 1250 482173138 482173151
    0x5120f0402120727060e2e0303051206010206070e1909060b04030c080109020d110d02120d0e2709031207030f05071805100201090501050901020a11030301060210 71
    0x400c003600c9812108500300e0140f403c01180307620a103100f0942d2a01381c800d403c1c0743c110146201200b102c0407802001125080070000030b94400c2c102020011003c00c5200709540300e451203501650b4245160401c42c0854804648650200d81d0420003c0c1d01800c240700501c1c03075060a43c8045c0608000c0c0c07041501505804d02c1115007030034049400f01c004c1c10412000c100a6a4800500034a40c003d40000c545003030b071009000516100500400840907001001e251802801ea5508a0140c95007603409400c03102c0045070b200503903140c605148032401d00d4806080d107094138100041140b0030303200d0118401d00c0f03030b000010b0700c82c190030f0f01d0f504880c0c410342560606911808407040c9140114040412099041c4040081c25039154111814518000c5028007150300c4040d4252a000c0c44406c81050400400c002049036203440300c003610402ca2680000154980381d83c58007802d6590440e44199940c0d00081e852a0903984401960200040400038600319410082d0003034503040c0c51050202c00b65261034 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 482175638 1250 482174388 482174393
    0xb0705090d020a06020d08090303010608010e041a0a05010f0b130902030601020f0d18150c060c050706060f0e0705030c27030d02011b0c020f091308070b041205120f04 73
    0x10741e961682500205031102a5983e15402075943d9800740c0c285000a0511000c40d89000340002581e05a031141d4507941002e81c2002c03c06640070b20020821355450088601032101003581d00f5059000c0c080d1644041415810807035002e40b50000c550212041c1281000424030641e1210020410303501e44442c0580d580e1680b40040307160940d51903031041107010b001010030016401144034144000c1c003440c8507181c1c503901d284540d400b40182280e08042406400d550001510b82e078022402040d040c10002d04100050303c541b0111241170b0409850090060000d1007031440c5081c550307510076158a0614518034201d040310300039008084c0b01e07031000c920700800c840300e4240382000c0e42c804000140407584d01814036103000303002c0c0402100940403a03401c140e8820020740b003010400241e60300601020a0049800e084c00040a80203090410404c0040401d20015542d10028861180140a441458200360900382c280b410641020f00500808110840440030302e8001d02e41c4c8124441d080748855036990 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 482176888 1250 482175638 482175649
    0x120b040212030307030209040c1713050f0f0a060f09050d1107052d040e0c09100906080f0c090f010b0a0309080a030617070621020739030b070509 64
    0x10800c210580c0000300821101320b0b4550b010f040c900108031001c0c0000813610320246e48001c04000d255000c55004000941d400941d044000d588520680442d0040361201154078201081015084010303003110540000f03200c80e9006409603400e13604010017104100d60388056032403580764010018010083c0c201460004280452030081a000d8036820710008a40d07034040301c0e042c0c2118440210482e410b200041410140700d0b0000d6502c0ca4030050580403214001c00c007005c00028403030580d844000001103155102806280010000c1200400c020071603a804e241c1400c400b420114011650381d001c200601c05100c1e90070341100d41010710b140e40c4560008044000e800d0301e40d0068018080016070381e08150b8503038004021524441e010340040302055010a03187c41442c4507500000741e42c1515601042082e82a074a402c010030070006107045415940c4809040c420421032802400703510100c0c0c007030022910000b500d118110340741703044282956101000800003826440400c500400c4641c911b0703d44 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 482178138 1250 482176888 482176909
    0x60f070e010f12020a030525020c1315062d02100e0a02031b1306030503030a023f0c0a0c03030b27011a0a0e01030b1c03090501020610120b0402 63
    0xc582c09645e205c05240014000e000150368031011405a0b00c01c071440881082105181d00d14140d0261155290000c100324400300c000c081034402c40c0e0748220140400000300d14031401000152034107194124600840301074104580c00040e000f20b40c8a031010038259011036602840d5050400014007010320070f00300351511440e4174009406103d0050303483d0203080040000039060204031514085480c85190b1407082e90510300c802040c07540107001142c1000039a4002d04641e5012840d00b040d220340441c01d0340d07a07129010104003104580804500d03960040080d0490344270401404a51604596540082c41051640c00c081d04242e650040c4084da03647d446440010201c0c1e036103052510b194031284031204007000307210340b004d200420504003c810501030242e80300807041e42c460403040f20440c03006502034560300241c22f90280140141044640098209003a060700030b07a12f0340115410080064034000b805020103800f0126403004005902e003940080c04a80d621810000c1151641c1c030208150240 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 482179388 1250 482178138 482178167
    0x1506011b08121f21020d05062809030c0215040f0b1306091a0309070314060702150115030213050303070308090c040506090106050921070503060f070e010f 68
    0x3000a100200854058002d601030510450002c1c09140030a8440b440c0c4401d501c51807a4005101d0f9402c01c1105060860b0114140050b10980110100e5542e00d400c12908845030b032950b019011184249025031088140d1844d01e0150401100300319440c061319403038040c1c038024490500e01038102140000e54080d81c006195420a0401140e01daa07521143d64005200507154000302c4c00e4001901031003403c9040884888400312454107a03c0d006c10f0306141d1000300101e0551040c00400130000b43e2031315492000100769806801c4a080c4000024100b0f890680c608e07800145000060000c01602c004440c0182400e0a006030345800007110a800c43e44561702056040c0408980c03142410f4224a0300e600ca4540c04040c2d42c00801c118040008862007138883c65040410000180101801980140210480280106179001da01d040381035079241320303886c4d55505d40c101d240100070030b0408004a50300810001d10040a502e080100185040c034508110f904000313006809403600c0e0b008403142540900c = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 482180638 1250 482179388 482179403
    0x4140703021f0809030f03040312020717042303060a0c0e060c1c0203071101050a180f080106091a010f090909210e090105090a0b030708010507020f1506011b 69
    0x44000c00720b825555041d51003034080341d840703000201c810f0f101004503070300c40c1c40714078080d42980c59940341241c80c80364210388907055590803c400000f248447e0410700026500a00c505d039242d0800c0c2070708030745030850300e48000ca0141c8180d02c2402ca42c0c0100f407031640085291130015007a40034400444045100b603140b5900072400090f01c04004a000c00c2d04011a00201000e41030074402002c1266a03214148000d07003140407408109607158400c80041482c14002e20b84a103031041101802201840c1c1b035840f44102c0005420704004425080c013a20340200b600000c200f01c10081c80389078a030340316805642c00b810400a034590200190107881000c0180c0803401081144988500d0202881e6440d01031110020000440c0c2c210104d01c10148003000d4180a00f842080303910b40300c107214241d4805403089400540320603071950291410020302d0000d141c100c0000c201ca09040c08040d0920443c0d0740d030103001e6082040c60404c1c0c6002e55440f55001003007840e010f0350300c96800701c410302c148071000700081c404c0 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 482181888 1250 482180638 482180659
    0x1090f09080f0307030c090f060807120e010b03160303091a1c0203071403011805091c09030b0c091e0301020f030405010b1f09060309050a21080a05010506030414070302 74
    0x10781000b020758820b802d180c40812445000040941e54610948551400440440340501c5024400d1030f146810008505085401907204240b01c001e98541c2d2040183c41d0790b50f2104000c00d403030f042140d42401c2d032200b02215042c0e4207584004245407024098070382c00f090000c40c1248c0e4128804100c0c3c3c0c5103440803504500c994450300545d8040c0d48107031391801c0002c00c00451513140e408040100e80c12594441030b03124105010070000409000d000300400300900032843c1d0381d0359404141114103013004042d40c450071494154500071690032409444034420520900c40da41e0a500c331a002c00c41100c02c3d41802c0e541c2c1c20480d00029001e8465410800c00b21070000c020300c01008015004000400b41c101c40d01910422190714006000b612170400f440010300e8020200201760099101500c141c2c059816164441610348809100300d142c028100040484010350780d42d00b6500843c9241c012205207030912155150000042d8180000b4101421500d20070f418048030420400203800210f42c040c000c400c6e00c = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 482183138 1250 482181888 482181907
    0x5071103030a080a0b090112110102010e070815010b0c0c0603090a021504050103180b01140a0e0403080f070207030206071e1b14040e06040f0305040801140103021f0801090f0908 78
    0x18110242c0e1030071380c450f0a0000242c16445c000d248141a01c11880e81d41c2e04e10b880980300e00e03420364010240d841c155580c03039420800700302c02802400040c0040300000d0500f40010308000d500f0810517400b1006040301400f0480186c000440e1084801c04201d6038079880b6211020311034200116034034000c1d480341c5080c030204403600f4444040c0c02111000d890410407050030030000450305203c084008d00545000006210040868009440600001d4030120341940c66215031910080140c0302500452440410840b002ca01da9009952001162015000d964a03660200710a802001002010030300000b5000da5210005002c403000aa001070707800c000c1e4400d1400c0004c0c020b034203004404984001d10f5002c002820140100c001201d00c2100420b41b5584a8981d0955180110130445c02c002e0b040000107221a000d0040e4001c0281e007215410540d4074520401008580c44101c8445541000049580180d0024070701411a02e6081d00480d544051b1200030f07004006004009042000100e4684603 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 482184388 1250 482183138 482183147
    0x4030c0813090f0b01032a090e0a0605120312040b070c06240f0f030b06040b10020f060612060604110904020706061a250819020a03091e030305071103030a 68
    0x3d8070800359100308203034400d11004405070703001d1418061aa106054101e841c1c41c116800c41344081a1625054448907103403c480d15501c3c1d01a151205000d860b440140164039001c5107018440110074021850131801600c40100c10300c0007840034240d40c4002d00054880d90081801039070305548540104002c60b0802c00020420b080c0c0b005039800f5449102010454040e1000c002040e1914030382218400d0f841e507070b62082040001080706800a85546654219458402c0401c2c540c3c80d003600030b01800c080014009141c0789004101034401c1401031007807038000740041000b07908a40c050341c000c240c02c4003800a80c3c80c40e01c901c80055810501c000365040520051390b0002040c1c4806c880203000e080c0351500302030001d000ea140002d1212284c010520141d01c2d02d00240100c0c01d00c5000305605184800f0340903042c6800c0312030158051b81015841d00301b01035000300c0c500c0150001c03600078a41d01c4410032003180790040324003009052043c00a46001402251502407412104c0101100d0703484000d0b000052 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 482185638 1250 482184388 482184401
    0x6050901050604021e13030c030812090102210402030a0c06030b0909010204031e150606050408100621081201120212070303020c06070816110109080606060304030c081309 75
    0x1111946000003051480c640ba00172035440c0d22805072000d490004050700c0b1a400c0e40b00050040c0307075041c00240000000d4020078890300440c0608070281e20750118400d55051410700902d180a264030400ca407074071820788220340204091b201066800300d03544a00c04a0b2410090075805403103444c8003800083e001e585500001c0d4441000c1c3d600c9031490725484171013401c1c1e0040c0c3c0801170404010103442074403401003240003803805009045111000505552403021a2000d4000100280000030705105407102000008004080003004108803071a2840f0b004c41c0400341c3c90500c181d0044843e00300184410081a50a80044100e04042c1560342d980308101309410b100049000b282e48a002c3c500c20300c00801c0401c01c0301e4068018146035000c6c0e030100000d0f9409030000301c50ba180c013840b06807010a100980029031510988007810303030f80715a030000340040e55943d000600683c0140700300115520b0707080a5a80040e81070500d130030050310314500300e50103004080301c00995111071f400015180d4200d40011 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 482186888 1250 482185638 482185651
    0x18110c1204090e0a261603020106060815090601080a020706060e04050c031f0506010903050a031d03010908040504090602040e0708160e03060402190b04030b0619030b070305090c09040605 82
    0x402908107540441c076261020701c103010f05004038282c0710326042c5c400b072041d004004400c403a200785040d01400c00c4840341012010241c0041c1c0d50340c40d003480000d803c000d442e604400f92010101e09098410000784102800a10207410001604003240b009a941d40513035105503444141400026100e442000c20004c0454017030f94a8801c1d0040c000305400c020900b03062101d00200701c4c1c0d40c0b034100510302074050b000c007404030b030304100024200102142080c000c5842d03061183e074600a6070b0030120f44117086422028404e5100e64941000480021501001c840c21a0410b4802081c11491070a20300020b000c0c1c1e5112180c81c0b0444010005000d510140b018820b00c144160407a1040345c55008503003445072450f070590554000c20102c2c0140c9040d035480e1031040840300c030034100180c5503c65900c0b942c1040c2d00841d441c200c00018801286840e2a401582c4503581e01c6140f01d0030320310744441c800d0910183c4004203044c0d4800c0411604c0005100c05100041c000d4480070040c00e00d8900280100b1040b59003 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 482188138 1250 482186888 482186891
    0x90612060f010f1e0917010212010b09011706040e150a0f09120507331b08010b0f28020d030e0d030213050409260418110c120409 57
    0x804460b43c060b0440210700201c03a81c0e00b100c418003180341e042d41502c0b04041c1d44144140f540e00000c45605100030100d4001600e400980c446400c1d41500c0c850300b1068010110200c1d0601a0301d07110390703001722425890707000c00308000f01c240c4544000c100104007055069150303024080103a02c1032443d01200702d021f4a41041c003005001215200306080700c510400081503141d44c100d100c051140314001505190740a0002d0a20140e41c010710841080c4112020102100c800261100503a6861040c01002c5038200107524500071008801032413158140240c690801e008181801090203120984034040c00b8914405550740011440d404442ca500740741360010b100355102000074511900131114041988402484c600c2c4100c40143e01035004480111481840550005031540e41c6003e04040b00d4050008000841110b00b0702e278490051080c10810851010041042101ca0781900000c1107144d0b41d5002030750354401c040160700345c81904181501889400e81c4042800c140c80024821210310f00e00 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 482189388 1250 482188138 482188159
    0x110f03060c0a09211e080406030b010e03010c0e030c060304080301060c1401020c07050406080c100e01020a0b0c09041b0503220b0414011802090612071505040801140402030d0f020309061206 83
    0x5090710441c90050003c2030046e00b4401000054003940081c00c03100310506002c0916007440d400310f801c445180f16400001640064a16006d04041c070a0885441c81502d21138a140740586802000c3c0c401072052004110000d141c00b42440031041880642c5524a0025035076001000c010543c2c0f03045600030300e4801c91500d280020680c1c00044c4c0d9603100600608200360780400c1040036a035400301019200d042d40102170a000001c0c0280301568440c514401803251201890b42c180030032540d0702c060742c00c01c464802e000081d280b5085426607a004103040080000d5184030713803040041c89181e150003402980c00320140700400495002980491a1a4000300300d84110b48885d0810741002c1c0c0c0020703400c01d01c000007141072410701c10030843d0f0602014048440d00d5a51f0410511104a89201c81c0009880484e05100ca0202801913041c0c0300701101045000341029000262a600c1850b030920500554903561120341d4002e106407040480000c000540325045140540740c20342044801502c19100e899 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 482190638 1250 482189388 482189423
    0x3030c090512100b0112020a09030b0606040806010324020a030b0f0a050f040207020307082a0102010908040e15040c0c1403070b04080d0f0513110f03060c0a0921 71
    0x414600211000310300400f0740850b28030110000300b1184004c079040000d00d444103401d004032400180011005542d55820151039414107482ca40405030000e41308142c200800c00220780000394950640760003580300000b100545545000c08800c80d001ea020301400469080700c07140d010340c07000352903140598401c2c2c2410358550401031108001d014155000c541d5038680c1100d400d10354080d0021610290464204d2038444038503900d4900720360306851326090008a5491403810600c1c4003902042c0a00080c4031003e8280c0d90348209015a0080c1c9a044180c00000f1304e100355000c0e04130038010070107481001540b9010710010a10900140140c030000da88003140c1003100304c0041141c401a030000700103000c17502c0d10780d211440c0c1e43c0000c15801d511034880d02054151011780c45641d0103802200300050034105903207005114160345542c554460003050034060402c1e1400300d00103911074115540c0075614050810141c403500040d400c1004480c1c0341030f0740b190201035000b25662100d801000070341c2d103018248 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 482191888 1250 482190638 482190649
    0x3041a090a052a090108100c18090501061e0503160e0909031e2d071a15092712070c030c0e011208030408070f050c0a0b120112081603030c0905 63
    0x20b10510301b2643c0304000f1448000714035031012940003c54030f0301c084140c01214070181c910040b60003031084203698500403c0466000401d015000380403034403818882c1d0306079030060182d000040c005400b0200c000780140c040c1d485030341000801d20f00100600d1203402c01c880160395a400c03a803c010824840d541713201c40704141d44400d60f94903440302c08000715500028403c0d90715018180f881c0c804025800c0c0150000076901c0580015001d82d0164003110f94a005941c9410b00c481c501d03880d03801120200b0610030b6007000d0407847d40901e85c03070104000840c0440e90385107181506c5110860350101d000b0900d8810403040690310811280030390400742c660b9071180e09a0048200a2052141c0798000310303034010005d40030401855005003e81d0341241088041d484650f940000c101c000c0702c460300300d40c100b00a40d01e0700200403006082600111800c000d584100c007000494180101071040352000301c18010008240c0865424590000c02c0d800d10344510f10b800790251850b80c03010700205480d0301000c1014240f9 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 482193138 1250 482191888 482191891
    0x316021e0a021203130b130938060c0309100908030d0f02090a090e010e011a060c010905030a1218150213030c0b040501020c040203041a090a052a09 65
    0x403201900e0503041c42e500700112501d48820014080c001803060205a50403030030100d0040030320070590b694903001c4010203030a02085400c01c2c031403540703058040140e8188504150144602d095003103c80412007201164031456008040c0340c0c000e80005200340d07032180101c083c01124509a843c01400503d54109071241c038401d0182100c50744c420303c490340341442c1d17582003580508075071400145048400e130080b403c405203d030046416151116484e041003002449807503817004000008000188051039049580c2c980701707001a00c24500440c034070103492020741c030070203041d54050100c03580d868844102900240d0804040c4981c84c0c41e02001d03044072000309041161302d42d80919101d8900f880719614100941003440c1510050805200110028541a5a82d0003409681041941319440c00000a00c2c0185a8080070f0066005000b8007002500121010240d4010781c0182007450380d406401614141d0b2801c0094500d2207042080440d400f030000f1400d110281c001e181b003901404001c24480003660 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 482194244 1106 482193138 482193193
    0x13020708030f220c03211209021215040c080d02100f0902030a0501022512080c07080414010f033309050109020c010c0f0503010519030206031602 64
    0x44003008101a012043c0d421048034600400520030b07039021107100101d5485c8c8940b80115541e0f0980d4205214400080324a030145440100c0100c000540b01a560740e8910307000842c0e050000f06d4015840c04860300241040e042c0568150001e0cc56070568000843d6201200401a5001e101d5116002e0243c4005600c4107080c20b51040034123203c07290402c01500c0315041000040ca10030700450301c44514181070f2516039680c0c4d4a10560702c40e82c440100040c40000e40072031412280542400740700c1e070030b98410601c41040744043c1c003100c1c1000d4011051102c080a9510000103807451000d0350079466030410105c0765207079918019240203800c01741001d6008916507080c0c2000b4810148070b01010310340b5403280392038030038080c0c03161106010f428018402d0401d041e00205002e07584400841c0d000d450160b41c0d1404042d02907030b000703100d0800c2d0b0060242c110b1505c120461540b91800742c0c007 = true := by decide +kernel

theorem cover : BRFrame.Cov 482014388 482194244 := by
  have h0 := BRFrame.cov_init 482014388
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482014388 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482014388 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482014388 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482014388 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482014388 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482014388 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482014388 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482014388 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482014388 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482014388 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482014388 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482014388 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482014388 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482014388 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482014388 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482014388 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482014388 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482014388 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482014388 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482014388 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482014388 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482014388 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482014388 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482014388 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482014388 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482014388 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482014388 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482014388 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482014388 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482014388 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482014388 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482014388 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482014388 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482014388 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482014388 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482014388 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482014388 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482014388 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482014388 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482014388 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482014388 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482014388 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482014388 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482014388 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482014388 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482014388 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482014388 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482014388 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482014388 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482014388 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482014388 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482014388 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482014388 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482014388 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482014388 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482014388 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482014388 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482014388 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482014388 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482014388 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482014388 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482014388 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482014388 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482014388 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482014388 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482014388 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482014388 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482014388 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482014388 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482014388 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482014388 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482014388 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482014388 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482014388 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482014388 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482014388 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482014388 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482014388 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482014388 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482014388 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482014388 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482014388 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482014388 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482014388 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482014388 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482014388 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482014388 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482014388 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482014388 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482014388 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482014388 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482014388 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482014388 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482014388 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482014388 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482014388 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482014388 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482014388 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482014388 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482014388 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482014388 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482014388 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482014388 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482014388 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482014388 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482014388 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482014388 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482014388 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482014388 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482014388 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482014388 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482014388 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482014388 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482014388 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482014388 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482014388 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482014388 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482014388 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482014388 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482014388 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482014388 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482014388 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482014388 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482014388 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482014388 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482014388 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482014388 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482014388 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482014388 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482014388 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482014388 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482014388 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482014388 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482014388 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482014388 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482014388 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482014388 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482014388 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482014388 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482014388 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482014388 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482014388 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482014388 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482014388 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 482014388 ≤ n) (h2 : n < 482194244) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
