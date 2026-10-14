-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2585
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T07:08:57.773472+00:00
-- url     : https://prove2.me/submissions/7782017a-c097-4303-a069-12bd8a8e6841

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 464748201 ≤ n < 464928057 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 464749451 1250 464748201 464748211
    0x6030501140d020a0b0d020705120702011704140a0602071203150b1e03040c0806070201021c0e0f0109080a1101110d1d0708030409051e16050720030c0901030803 71
    0x4002d801082070000c5280c2402c541c2000300075a0001405500403005076005055441c0503001351440e00366481d510100034440c1880103070001c0e0580c10003031001e00107000501d4001c1d101d42c41d81c1d82503800c402000e600317003400e9000585141358085104801c0c031145c0860018284041d05e8100201640b00d0300e2045080070314042c0301590200410400c90021440702c100c40300c0d0829403881c40e26441c140c6000e90540c0d809000b2400c1c5c50103086c0c0466074050050096a0007880740c40b06820300c0c08040381180300146400e411200441c8103103061001002420701c514201d4a000f00c170000d549001781c2c0f20140c009070098068800307603031404010744020500c0e0b0041e41e9a0700d1100c0c0020400c1103003462074059458100003030201c42d01502070700007006c22000000b081101e20301c40381031119648040c04820382c1650740480050300c3c0700d54030024100b104e980e6541880b0f010f45003411406c1c000c0a0b241c60104800c250103e900e10508202ca25106280c20001d401a100e011100081d0560440d92008458080649 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 464750701 1250 464749451 464749459
    0xe04020916020111040f06110d1b030903060f1d030702151e0a09050306012111220e150709060f030b0607060b042909040204020c0706080a060603050114 67
    0xa03a00d01c4003031003904401d8a9000d104a01500c42e1340b240401d9980d032100b4420325001c240766640d4043c860001050031110480c503030f100e420018507118200c03800d90000041c1101041980800400040d08074410350034400390001000071804c1d10100c3d410700205110000041d182d005010000041ea1440100948001e00300f400e80c0d261001d030007202c604505480700b120f03046400815500c0701c495209801700110340c0b0440031a02c007641e0b183c00314960500414641d1007103661030400c110201e22422200101c0d041c015000d4010401744d00d20a49104ea84458000d6034161550580c5881d07002c10071000e00e40052100013110242015800900f030601203110f05e0013800544d0000c0901c2c40d0080c2e211054000b0050300d516511406840c0842c000c2400010780ca1003140341040030b03c0d10a032460b01d600c0701c0c1d01e0031040c40c112004803103040140442000b001240c0c41502084840281c1c2ca051203001c004081580310151907017000d41991041d2106500448201440c0c2001004035420b640310807032081005903 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 464751951 1250 464750701 464750731
    0xb2d16090b03181e0a02010c0218071e03061a090a0f0b09040608121e0913060e1302060d021308070312111b06030c2809060216170a170d060e040209 65
    0x427000c80c01c1c10300041400180200303100100310105030003981300034089550b14101c054030303091041e00354111503250086108140f516550610f110f58014001d0607020300c010306400c41603a88420a0440745041d4128000040010840c0003c81c2018055500505007100151111040003510800b6078051500c0c440b0300300c1800340407541120ba041c41103d0303100c8801760550710400c0200408a000c0d0202c0e1185d0361200710031200060107840a8440203200d140c0c0181941d1401c800008000082c0d000b00a10184035952510001040d8004201e80b000a51145000b641440c8154501a00143d032024a07256690041801d1420035450889000000075040f150151691103640713021050b800303020a81c055a20480b504c0c60000e0f4950042d001484903a569845c124946a40049895510200d01440d5882d040c4200780516295220000c0d01d4600384411101181d00d10307120b1300102e0540303000b01200bc0340000303900104e0441500480024000082d02c0200c1420243d002c40e02d60007005000d110806298 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 464753201 1250 464751951 464751953
    0x9050f0409080d05040809151e030a06050303040306090b060105040806010b070602120703150611030316020a020306070c02150c0606011404120b2d16090b03181e0a02010c 75
    0x502c082c0c419420080030104941c1c64580b40014156201e944d5051040904c0380703001029900e50b00407140144000c40710708044541c07007c1c4016107a00042c2081900f00d4a520010480e910100064030042d8003c07000410718a40e02c1c1840c004002002d4030007810007004000034414003400251407811a0a010080c80c2e58458a0410742d000b4042e1001d04051890300000340f2450030f0741031704200d50b0103c0b04400001e1090382e552060310031003801d41c80380055820610008021000000c0b901c41c022160340180c9404100a03030029040c40c0301181c0b010080740d8806019020b5040c5500c0c98120061100c0c503961030001c06002455071854014040c9040141d03040c101c807440600e210a40703005105010781e83c1c50f50903040c900395042d81c07800c940042c106511032118001c24082c030203222801400707101c3c407404a0344604a41944140d15219680c080c441209c00005100e40100000c5100700411a0900d08040d141d51009003401140b0b81a1190004280e5441d000c41c1c0740800c58410701582420020381401e92 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 464754451 1250 464753201 464753213
    0xc110a21030c17030a060509070e0909030f041502010c020102040f120f060c05040501030f050105150f120106030b12011a040b12120c060a0606050a0c1a011404060609050f0409 77
    0xc2c02c1d600400d0100010009040030511001a5005200112080c03001c1c903101c100740810018111000070024842c02d03c0b081d82410042d0006030000020819207240040c103408000d1558042c0c3c0c485104403018280c1c3d84989682881002c00b2000d241c4020341c03420b4030701440207c5030251402100882d07012402100d0402255600e0070040d00c0d484002400982180280a0b240e90498400d00e400300c4e08008200700072514501c1840d060f04d0004080c00840143c1608800740e50300240854040d00c1010080304110611049048e070085c2065613010a2651080c1c0c10303c20060071254890744035038102041203500440d0549880700d01201a540041c1004415000401da01003c5502513524080d6040b9005801c000300010035039501d1840417149203445d4000c1c41022a503c1c0c1c40b942e00044c1d030502058002600c2181d00816182c05600c414080716180e04c81071100301c03401ea206104191303010030369550721b00b0140101002000c05080480031103140c10041901e03000f52005161195a07260002070130044 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 464755701 1250 464754451 464754467
    0x304031b020a1707050906031507020a08030a270b06240403052103100b0f04150806031e0a02040902010332010b030601021906110a0c110a2103 63
    0x74000b0700e0140321a95030f06a818a610a20750321000720700030180c000c01d0905100c206503000e0078000d0020602c2c4044101303860b5207804082e1440086004a61195020070300350b1000c1c40c007480b00840000f44054040c0e0301ca078022045400c2e142030b004020014003020a00709981c80b580940b041d28880c0b00703805500950301982c3c2c800d106200101c000403e01000740640001c44070180d89201e960501f204400004010140c0000c44548070f03890710030842808059002800383c203505a0780340c10281000d0301c2c0c1c0c0b52100460090210400019100300800044d1b1804000d0380000b9940500075242100001554980300c003142400640239035202d40ca000d00b1a44250300034101144090725010801540e00340a0142030034544444103912010b20012424001e640201d0380900016001040d0b4814540c20b1074540c02e04805055030403c1d5210140124085d050004040401c0282c0c6e0303845070780f000c40c40c00c408140704512801e80224000801848094100c2c22240d0b81c1c200105041c0c3c0d075441c141d10301111011 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 464756951 1250 464755701 464755703
    0x24011b0c05040603030806130b06040605070c05060a021c18033f1202030609271b0a0e01080601170f1207110114030c0903010902061809010b030108030304031b 70
    0x362070143c000050541c0300d203115000c0c0c0406c071810306a000c2d140418a060364140c41e20709030301c40020882008880d020f02c00078116288a041c42c4140e4a5403200042c1080d044540350402582181001000107001003a240d071440c1e01d5030400f002c1002d200d0780c00580d44e400310301009041c100c82ca0740310460014240962101000b440240c0070361602d4000c64031820380000ba000354049240301451040b40403250095a00c1444081d084010654030018642d03c90040784444425122204031300c0c008080f814050404900300c0b55520410061018041c0007404850794440044844440700600c00301401050f10360448140d503a03028a40040751f04105e050a076485032124a62203181d2000d0507901c0c0e01c0300542009401801c84000d012580070064803030b6200071400e10500381e41000015000da075040090300880d040038000094183c566404903500e5402200c40400402c43d141c0c1e06005440d04e211482e0151419a80a50655245c103035902c0ea2400090401400d10525184407502c1c8901811440344903 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 464758201 1250 464756951 464756959
    0xf04140403030b090705031b03130b010902030106180e0c0c100606080f07030213030201050f0d050408030103064718041103070b09040e070f0801020324011b0c05 71
    0x190034540340c06030082a44580c458080c5005000007203c5034041c2054074441c82d6045075050324036100e142d12034560383c0018052500c0680024988010803054a0b446000c0c120301c07400140ea81d41040c00241002c0003104000401d80c04851044c0600300000d062143c0110003245002e407902600264142003910030303001d84600501d4500700140c0d195100310218029803946c2080c044649420340200c040c0e109aa0501c4080b0381c62010800055218500400340d1a6030900e016061100c00700d540700c2540d85c10b5500750b541d08400b01c014000c3c880301c1e100710b80c02e668070700881400104600484035000c5605445000000303601c3d030807041c0c1c040c010802d00f100102000304541c4405000c4c01d0080e0407602c05840603030381309600c500140c14a050000316442a40d20400c0c240d1301f051344143c1044040c00c01c008003041140075101001403c40b0308408903402030408800050f0302d900c0c1c01008007500e04401040080404d160380400e00090341c11950f601c42c081c0c42802089950103483c14440c014201c10350160b900 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 464759451 1250 464758201 464758241
    0x12020307030623040b010f0206060d02060d110301030606060c03020a060e0a0b0702010905150907050634060507030216060c091e050f0f0a15020a05010f020a1b050c0f04 74
    0x1c8100300c111003803d500200d40c1082804900c400440786408146450705c0940d108a011505900d804204030001600c018071451402182c1804003044e02c004201d07542810901000500c2004138500a15010346070b5441c0582d80b42440751402551280d551101030002d655031855100c00110501401c0001e03500300f58460b049050480000f4020054541c060340c1c1406407082100e0305010002840707004074002d100404403281041c00b0409a03a100e60741150014070840f003521507000600f0088070381002004404800c0e05001c0c1802c2c020740f5402454001003500c1000b404241040c104000200280c008000080c070300c0207410160b5146040da0012031400c1e04603071301031181c59050000e01064400550750441c030415000c0c14015081c2e00440520360043e88220140320007842c4147e402c1480e441481111028185521102d0856440d2151a400b5070b4001410441441d0842070084520700040d1207211103980d00c0c2c84d616260b040035030007a4400c144642100c2881d60350354104131341984a044281d40 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 464760701 1250 464759451 464759489
    0x60305010513021903051e0c0909070e0c0310090f0e1608010c090e070804020d0c260606010c02060d0b09010b0a0207060f02030901080c040b071103060a0c120203070306 74
    0x2e0002c0321001ca100f41e1030300c1074120034071403002501c0c0101c0354070900030442c0d8482c8140e81007001c2c0ca808021901c43c07099403500c059a6588014060103030844074042c00c20181048410850302d000200f0f50444100c0030001c1c0301985142200740c0003140c5c0182000103800058104802c050001045001d10910620412807401001d051190003180c0382d00c402040040e003502d40aa07234010042c4149080f40c091000000c41842c041d90005071300501c010480381003c0701a995440340c59006400c881040c4d14903002c0c810340d1060f01d080d2048120150002031a03585810750000301400c1c05601c00030b0140002150a04c88520700d40c01003010030800610b00003c0e9a141c5402c0c4000d80c20100031440184204100041c0071805501c1c61020703811130b83c0c082d51034a130f503620054500c1d440c081c04490100033308000008080c401c680103090414070526458025005960803d490301c1406000c10304400c1c5004c0303410069a400c004040000079140340050b0701d82d50303030b0b4009900902466000c50303034085038007010740 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 464761951 1250 464760701 464760721
    0x120310030b0711100b2112030702030c060f09100908190e1306030201051e090d080307020d02160608060a080d020a03120b0a050127060201201801050d0603050105 71
    0x20000300d55401c01c1300c81032031001da02c03034054504102040340c0080d0f021807070040003510100000c032049140011524542c5c0403020090700c0754001c41d034050040e00b004c6100070f1043c1d010b0002c641c000049207004030071401d010200503140c0c5240b031a1501c00e00c1c1e88074004010062200140d80346644410300d80c0c080312464110141c145281d842c41d252145460071408480905148074480030341c1d4041c0d482e0ba040c510b82003032803048143d01a0b84201545c50901c80d030141c0d5550010392481040c4200400c42d200d007010540079242c5026000c1803030540d000f400c0344155601440900e442181c05910300b815061302d40c0c00c08101e6170400d6801c00041c5019000b0401c1c1c11903000a01c12a0f010700c80e64840e03040000d50f800d00704c00c941000030740942c88001000104800d62180400c142d400c003075044013183c4000044240e00c0510229488080548d4440984180038102c55106507010b4402c02c070094540356a5010781d03041c1c010720a803880c2c140305012604a001c03081c180e006c1030156902c41d000b041035081440c20300d = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 464763201 1250 464761951 464761967
    0x7030c0b072102031c0908070c031a06010203030703020912030c010213090e0c01030b032508070b12011208070503040803040e0a1407120209060d0501060818120310030b07 75
    0x76103001a580002e059049151803500b041200d056001d582005408a6003445598990041844894560004c00041441480240b41c10b902c180c84408000345940f50082000d840b174080c03200342603850b001700b001c00d98000c82246e0b806141460010f0761481103000083c4112414922803219200105580d0903520056000380304e440ca00000c060340190740c0e00b40792800d5031042c20700381115402c00d852441440d4001d8100001402005040c0c44004401100494601c01d46a80d0340d04441d0300350008000a03a400d220803401340500b200b50341d01d4401505506481414188103000403201d80125041c01e200e01d190035181c58680c401e050740e40c0c440d92546a2a5070360020f000d0340e1041c08001001c100825034a11030101400a1035282c40d03040d0340c0d40300301619a00c0c3d0355000151500e408100c2d13312556900e80040c01c280304549000075071541841402450040000c10340d080c83e4201e40800d80d00e0340400140d400e09201c0448005603a9030b9250b03040c100b1020160300040c034040c88403050101143d080540 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 464764451 1250 464763201 464763203
    0x10110109140a0212190602030a180302010b0901050103060b1603020a08160b06010804030804170d02070303020351060307020f060f1005040b0402192601050a090c0207030c0b07 77
    0x100004080c51400161560501c0f6103907942181c84850717400000e0000d4002d150f20a080e0346d000600c035a50003d101d90410200c500c2203005035900d003c1c81c86140741004125000d40003e2908004590034110340055602c2151107084100801d007010900f00b52081020702c024a80c000c410302e03102d007400d0f0710000e2180d07401c09003120104a02d0000611035480340300d05902c16a00742d41d600ca29034840380c845425502c44440701441a8400b04282105106980010211907209540060340d03882c0c1041c10303c40d91000252400805207440c1000444120b02012450304030015640d10b000c5ca500181141a118001000350f5403c900701004001e85550003164022007122300c40280e0b0740c0f82c1c0e20020b00e0440140300319a5064041001402404641813590001d990b102014000514100152803100019041020381702c00140140c49a5440301d04410b01c821400290002d0560040d410000040d03150303030240c014121030558030410340110302d00c208446401150031264a1034150340f5080b9031105607111b000 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 464765701 1250 464764451 464764459
    0x70e010806011202060304150603020901060f09090e030a051804050c0304030f11060a110c071737021903030f170f07050c0f0d050901110303040210110109140a02 71
    0x100004103500c40703c003070001665004080600e542d40303d543d494441c038030741780c2180354842e035401020005854062906020f070009441d0844c810980b01002404803181c1c3c0c00c400816414000d000b03025110010a4550100450404940f00c0601c807180e121140404c10300700d64480d080000f0b0013100011500110b000700d002c2c0d540e6410828896074280d80074000120141030580c030800001d108000c082c0d1069151124036102d552070000c401e10300c0c0380b40041c15084110311240c02038901b9100c4000300401c12402403400424100283c55040300c104800314a601101c2aa619020b00c00071035440c0504442089440c2501241c5142c1301e04004001c0b1f000210b135117001c1103800d00c24400c05610080034a2264210181c1e081859a903003604a940e904041c04c0e0000340c1c420042c40b00e16603a02030110255806555543c030b03441c0c00c00306e00010f01950308583c2100c101e4100f00705120158071007403500d0303110351640d041c4441c180d00014000d9006140076071001c0c00000e810300341c07205805004034588c00301c14000c031 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 464766951 1250 464765701 464765713
    0x80d0f020d110a0905040f0b030a0c05040c09080a030302090402211603140a020703031e0e0c0d1a0c0d1509050a02190305040302030909010305031c0501060f14040503070e0108 77
    0xb0000c03884501c5041251800f00d075040700c1c03c01c0306183c590450402e038a00103c0100c0d50a04941c08a031800c0301c0c0aa04032400c06002d0028806820031307201c0c1d0039000e20b0074500f419102d46410302283d154003104c0340260030560001001000703615283c044a00c15080d0400010902d00901500314007a8015681013500700404040502910301c031f4000e2510316000c1d4440300409441e64070540001394001e101c2141490303110039990400741822091407440c252a658007080c101c40c1c0d956020b040460681c0344a104001081049020a0380300c0407d03c24403040205140252702c03040c0c80c407029030160405030070015080101c9040040340c05200541222605070b0140035503211a065042603004007a050801660040d14030700f281d0784280c01440e0000d00a00699250420300004a1034541c805d0300290b8180e40002104c0031121008070f0740c0c150b49400d0180400855040c0303840203100034003c800b000c080040c81156071380c81d00703660412a002083c0040c21100016a07404504104000074822000580194 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 464768201 1250 464766951 464766971
    0x303020d11060c0a030b0415081606020a0f110a17070f080106030b0402150708030112020906010c0c060f03021b0f0f0c010903022205041401200313080d0f020d 70
    0x401500945050b100c043c144013000b20210010300c10800d1440d805074454003404045220200284080c200780e0016040d084c85c0761280001c4060541e00910443d449008080045101500000405940562680385452501c80014280d4001d5000702d00b40001140c090811070400245c0e12088603583c080c400041644c44140038221441840098042d405841c001b0f070062a007040d44549003459844e03420304144080d21120801c0c1c000740c008045564508556106500d070010b00d40d54400d9003441c00c1001a2000d555000c01401140b00c0c03041440b03611340100703440f613020360140c860840d100937940e43d000107440350035035071030441406c0d0030300902a601900d80a4640401d03a455140c206869400c5e0203842c40c0e0901c010021281c27404a0130b544002d00000b1000020b00a86000d036000d040c1c83d14000a446c005242182c0d00360740980703655405291a44c0084000605482c0d200c0801c0e00c4148410007a41880d0044c3d110300e913000414145408032460032a5104d5000d0098803d80700802c0007000e200c = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 464769451 1250 464768201 464768203
    0x1706400e0d11100209121605012706030519050a09020a050109030804060c02120a1109060d020f061809100e0a020301180b0102010e07031511030708070305070e0a0303020d11 76
    0x24802c82070081c0c0d004148428405403154000780101034015010480c0000c482140038100003003d0200d1104c804254010400b0b903038084015401110280361a200c8100f056140200c980c02c28815503080c91744890016200d60b80001c84031044a80c0f1401c14441c038a80300c0c403050000e02c84094100e1043c01c0000001c515548070f001751a064a0f80120140c2c642030800d0f0094880403980d04040760301040c1319000c0c000d07000b4140035000146102e8180302000b000103000300022070b04001c1200c0d00030042040c80c41c000da900c0724004825003109899003a03130b40b280083d130400c100345041c4a05800003003800034452440c5201181d041118000020080551242c1c1c2c2e07450186d02c0207105840e0070501da01d2030a18100581c2d8032005143c401400005101d103040c211050031b064042d841a0b0399400c08a18100d00000d86014201001c02002c5070789155180a842c05066200d01802c0c040400d41e8490002e5405400f07042c0ca21045e010081c407602c0c601d541c0303203030080d0380e54002402e00b0b00043ca01c0c0898003c8085c = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 464770701 1250 464769451 464769467
    0x504050601090c231b0303090f0f190807050106080d0f08070804020105030711100c1d0607141501090c120b0303030622050403020c011706400e0d 64
    0x244d80d5010f00721940001032401c0c03108201c07031200040400c01190340701408812403081070b983c0c1c0d0b00107541c43e454040c42003401d004080804a689030400502d01880c44408106101d0302c0342614540310300e1000609018030240146400203009600c0c020000c208003100240890200b0040c1d81d408100c21104a030445200900303403010030108031100003080c015801000a164010300300e18246540300f00c0900d005242540c3c0c1003036000003594501e0942c040c00c3e8442000c004182e80c4500e10240b0300c030f500011480c94803c1040141160000790030f0700c0840c0e2402d00009040094500f00391555503100e030310140040c10710f07810f02c0c0080380ca40621414401c485000d1000500401006541075903549010310108059034030100404107181011042c0318401e9203c4c0c503008034081d82c000c0913a0640c0400240001c1d20848120b080d000205040103516940c010090a1350403240c185100003c1c6000714036840407560b014034181d07c2012901000403002550f02c41c05040e4050422030b1100c2e5506003051325000 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 464771951 1250 464770701 464770721
    0xd02161502251e0f0c0f180504050304120c030c09050a4a1516080c030c070c0902030a151505090d0201020c0907050319061d07140d050405060109 64
    0xe5400f07140048042c15070f01600030741401500c44180500d025590300c5040809034101c822402c1060300148403482850381104c0c4143ca10180402880c00c044e02c860356240510300c66410402c42c003d0440c4100070480c51000019170b0b0101903803400940303a401c004040c120031101d65003401c5c580713400d0124210400e05a09003009131560040c41d1040003101c0101c41c00c441d280350056a60b400200b0f012405d0042045c41418150916100d20a0502c06940c0790079000c0d40340d51780108a040400d008040c259071003100c1d00141102d0070295124410724141444001c10762000c04142d10110410001c48141e800988900700c0000726000741c1610780741c560041c00f4001c4015400a1028800745010f0b00304038150030300d10360050045555034411000001c0150070112103140c00144044140403403080580c141c804242d00d0340c1e000b40302060615940d580108030003180c06100030b661001182601e401a411104c0302d030445824103503182c50582c1040c018020030313202140c2030b01c142c83c0005040344070740c07092002803 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 464773201 1250 464771951 464771963
    0xf0708101406010c0c050a080f0c0609090f0603070e01350304030b0915011215050103031704060b0a080d090b07030c0212030c1b01030e0703080d0216150225 69
    0x80e21544011500360f1000d103001c0b078680302c07500170206aa5554020f03200050402c03800030004081d80c0c4002500742001e03554164003a05c82884614242d5540100b501e0b8403161f100040103080c2d07569800286841820303402402003006500c004280c0c03000c0c8403150618001d24001200004110140b44030341e06c048825a80b030f298205002c144006102090070303036001300c184411140b41c2042c88014441da2a800c0c1e00200d29000c0c4c1c0d41000d800c01c410842488020200c20504001a41c91a100a002d02030100c0d0086100c402d81c0c00081d08000c040d074041c120780f58001d41440442038030380340030642d0f41ca51440d0900100f443d9086c0003640501b0a012101001e50503540c101c5212080e5090041c40c07070315040c1c14000340c04140849601007004100b20400d11070303904010880c81146000150460310401c4001000e41c110001c1403010800303645c2200e0b115074000100581c0d90f0411410484644842003001702036058184401500780466000707400702c1c59100b0000014a1202e40c110056104000340007051 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 464774451 1250 464773201 464773241
    0xc091e04050114100e100b161b0b0310090b0307090b06070501061701060f0503030f0703120c08010e0105040b030d0f02010b1c0b070c1104090c0e091501080a0302070509040c080f070810 81
    0x48001c0f204038015140e1240070402c03008a1550050707081103060b9080ac0007010008000c10410912503010000140320001040140d180e8072000700703803100a10300400003800e445d01d40381501078031050304864210b80c121000f002465100c11605225641c62492800e031076003000c00c08599688215194012100010019868615500c10410041d00304000c107500740444d4440e0160841114020030089038090b607950501c560400602080048040e00071a00941c600070102015450000c2d452120400f6814241c0414455070001c90141601c0d800041c0c11003290749800c400e98011444c4685420710488401c0c0c101d86e540d00040702c50701c09214024141211004070180141041d600400c0500d0080c208400c1e603e44640c02c0b032030b01c9071041d151076050b0351040003803020807102e02d160640504241401f90200810b01d0318020b64981d0a0702581c1d100b510240040360400c000030b90300d14000c1c20080181d50092101800135501c030b807024481eaa00c1070055030b2a08181301c107a84540c11904004810a20b5 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 464775701 1250 464774451 464774467
    0x120105062818150b07060c080108030d111312061a010203040b0304060b060304050f010608030f120a060306050403020714010e010804080a0207030510020405030c091e04050114100e100b 81
    0x40000100400881042d0b03507510503010f0f425580344035030060801014001d58034115450544100d80c0c20000d0002000200401884070080c04001c4640b00c022041002c5030419420392007a2071807080ba1800d074000284000c00154114401c02c8140c043c0e409003000b0440401200c40750b4400c40605021580160000c00085c4041d80300e0402031600a40a04000a005640716010071081d50080c0e03015203103a400100d6020301d4500c01d00642002d02200702c0a076050a525407001080b1b40151440000003480c508001203914600e548648002c5410000034403060410b42000f0351a1042ca018410b8108034050701001e0950040495102550040e907604c1000c0d984c540b00c0c1c0754113402030003c40d01140030381100000803075010031400d410f16040040060b40c5c1e510300000c0624248134400e605d4025002401005a104c0c0c0c0d0403000c111b155a0240020303500d640b42e00d000b90040400903d17501034445000d00b440b40300e20064540106070b0300000c61503d00c6440310f15580590a480e44a501180303481000001 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 464776951 1250 464775701 464775719
    0x518090a09060b0f24070f0305071b0b0a140d0504030309120504060f0309020f090412090e0c07030309030203040b04141e1f020f010f0506030706110a120e1201050628 73
    0x460181701203102420860b043d0380700a030072086200140c001900200c0c0e03070814441401c90040e2440d01d5240040e00062400044090031300507490080c05000c0b09000c10070741c1c0f66245044403142c4200f403c00b08624900751601800911600806440070440200340415060288003100d040d908a0749440030b0704006c1100441c0a400001d00c01ca03041031400d60411841d407141820b0600691040412044c02d00406c0b00080c100f02481e4006118103c00038140b210b04082801210760842d050700c1c0c0816141c0316820181d1951050350311990035030000080000701c40003010f600d0030302b140c1c003142c00034140004042d052030a031212070180c503840415048103030400420700c070140440d20900c0c01500c1c09803036601611421035034001e560696a6450b402000114941070010074041c3c204c900740f00e1070044401503019900c0c0b1070100000c4c04619070b10010181140160340034640448024000300c41c000c404030505004e801c05a465a0151900341c04048800c0c1da41e00344518030700c0131025242420b40c84c0c52518 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 464778201 1250 464776951 464776999
    0x90e0a0506040605031c0201150608012d0803070303050f07050d1d2b050c0616121b02011508120702041401080a03080703020a050a0518090a09060b0f 66
    0x801d82c00360b911400002e494600b4402a1281c01381c615043c64040920503003e4203440710f0b024084140c2c1c0066000f4880d458001e02e205054a01d541c01d8059009000c1c11401e60500741381c90071143c01980c140d400201d008000004100310b41c82aa404d014648503511a44a200c200b6105000444d03410301491207290b9090b8040f00240c000c0002600000e00302c018414180380c01c0114030f01300a10005200410b0000d905e00b100c0c2041450307d4407034a009545c10a854444401900409042003c2118002003600ca1554655080000a0100130751b4551300382d2501d0003000c10501030055400d0454455003400c0c4600310a04803084040681788845c0100380c07214090380280c404a07846951151348411a0029400d81c2e40a8441c40c00184200c8060f81030140092800030311400800d4010024031241e00e9000e416100c43e50307c6c500781142c5515040114036082280380199a0300a9410400c00000f40d445412504005029100c1003100d5100d10050019101e00001d0664019100380c1502e03111240b00401 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 464779451 1250 464778201 464778211
    0x10c080114040c020c0a1d1605030c0c01061a03090105340207030c030501091a160c050a06050703060527070f1e020a14012003070201240f06090e0a05 66
    0x10b40c1c414500c60400550140b0305074000500407e51507080c1c00c0e43d80109184070b5003000c070150700285d00080c80c001c000d182e4070000308041403294011416580c5402c09400000103030460b14100708820100004400302500103c807000c84544c04c01020881d0003d900152807092164001c40842c40301e4a20b1001d0203581200014408501c100040000481c0100c07503507101444c42207001144d14245820311010f800c10b6210002840a03d04c000d2040c518042c3c500c8600106580c1040c0c0840d894504010b410324105032006406642884100081c85601d640314100f0b40720201c0e0303d0300450b4404255040c159001c1d1aa45201e24100800700b034040d401003494a14001280c50050322100705240401481421100a90003590054101004209003901072414100281008025061040a80b5510f256207540000017020001010550040c800e402400c4280280c01501882c5031106500e1004416544640d00380000b00a8000c10749074460058001100c20001d04280143ca070315001c00d009003c0901 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 464780701 1250 464779451 464779453
    0x120309050607110f031b0601060503010b070609081b01060f0b040305060c0c010608030a0903050601093e0a021b0904031d06070204230105041b051b1e010c080114040c02 74
    0x10480031303000c208000d0207410890f0381420f48040e40d454459207000f1040e0850b4007486424070052107051044410b852206403c102d0118144070b85003803a9400e0302c2419007440b004070054a0003400d001c015003080007151842e244c900c1a0664845002000b0300403400b004109401941c041034511315510090301c102d01c41c803000040d00c281e580804078510b40c4400ca0b0030010455003841081403007400d0110303a0041201902c01e000e049030180003120303160b150140910f8518031001078160341620308074090f50300c405164680c075664403441030041e42d034003040e00242c0300b8045059440c220600b001c020300c1c3c1c0550350588500040d6213081c03080001031003491103855080340d4103000c0303100076965500a070742c41d481c1417a183d2022960040b0400b40b107210140c02190145090000e5041c3c80245075010403004c19a0b071030120b0b00e5484020044011900349001d02a640c412050304214114003400002800c4103420000c02c211182c03043c4c2900c01140911800009500c10a035039030503402e198210030210201c0744 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 464781951 1250 464780701 464780713
    0x608071b0c080601060c110604050f1306050a0807090501091404020d0f05030712030f092a0305162d1a0d060b031506190c0c08061312030905060711 65
    0xb40041d02d846800d81c091400201440d0605051007000c02c80b20b86030782c5080d074070b807890a401c000c0429402113464103402d001d60040c207500210042503a1101c000b402e80105680c444a80c1d0b801410341e102d80c6809800c0041e480c5c00000100c0b0006481540c0d416001c42c84e58082d81d83d540c1d001c100c400218207005031150810f041200000500c00d00040070300500c81e10700f402c40f4413421a00181150000c51451060f50314107030103c1d005c10400325134815101c000c291103c02c43d00003d40760707100140701540028540d1083d1204165800d00c41907034041035440c1c00c0301c801644400313508800c2100c0e003403a001040100750036000b4007101d0010015102032a0940c181d0314500782186030b42604440c0a9800051002408030a10423080300c8000b10000010044035114101840440303402070003040e050a400920501c007101030108000714452000800690040d030b01e80b468030402c4d02107940350741c03581180d40030320384d00700400c03454024490791401581240042c0f0869072030407000d40e00301c0000c206400044c0720700 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 464783201 1250 464781951 464781959
    0x9251d10090b071a0601110a0611130e06032802101e08090c01050c0c04091a012306160609050c100e030105010b2b1104060e0306010608071b0c 63
    0x2e0b0010a5018496004000b1696140c0348400b0001d8000d482e160402110642800e2003000c001101c1c00c805402032070005640e0050342071926644210340603016044000c8d180041d03400c5401c54403510480307041c0c040e260030085490707102e0140003007100350071000c401c0c18820b200507041041007003ca041131410400c03100480103000e800b903600c00c0300750140058101c004202100d50103001200c1511003c0c24558148004046440d07122046800c449010b83d81d240ca81c0c0301400102c0e440001010100200c2400c1c1d942c4500c0f414503030681803602800c600081c6081c0321443d04010044400f844004061107511044c0307581c4d801c020b002c4440042d1814459042800307420340d030b02400070341100200c3d100c81041171402e50a01d403d4440580c0a001468424840072180d0b00c0000d543d083d0001d01002da0414101c221884500105200e02c44450f102c0800701e00460b409030001c0003001075000440440300740317a0340e9080484200100f259402e0006005c41d2080350040c04d5a60700700071051094800d04400c40c3c031 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 464784451 1250 464783201 464783219
    0xc0720010c02130c0e030102130501030e03130815090a0f0b1305060901060305060906130308090a0c0b0417120a0c050a02120619200d0b09251d1009 65
    0x2054501d82c8125640d06403503d0707a10b410001c5d50409a0098000f541040c1d0b20074141070500b81c051007668107040d1100c3ca41035191909000f03d503201d100682c019207100b17444045540c1d5440340c0110805502e4201c5010031415400064603074480356021228851442890761421a280341c040d002c4188208520039040001e4800d000c114451a0400000285c1c41c1c598101107140600291000c440d60300044103201c41100061b00d0004031342d4150410f0303103050322600d404a140a001d2940646940c038882c0011948480300402001100c42d0b609242e414005044103c545900e1380e1483c00c80380260800044a0f08c41c00b900c00359034524001e17000d9071100c5843e9000304030b003119802c00804168103c3d00811809800c00d00d00992240383d407010070041d0384061460754560082d00340c0b02191016020505518010007500009003100020304102030904040722030041c0150032001100040b8020305414240710b00c25599030351740002d80001c1481c3c49603900c042c0846070801214000410121000104804034 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 464785701 1250 464784451 464784469
    0x51003020a03150e190902030304060305280b09010b19081f08210a05030c0d0f090f0203010c1713030905060307050c10092301061e030b0c0720010c02 66
    0x240c013521500c0c81e1034101e032a100c100c001c0800070b410b042e2500d00d2480241c1c4000082d142511864100014603883c1c032901c1841010341c90030801980040d0182403041e801d041e401002d0005000d07078260070203907201c0c0c00001e501d004030640c800400ea40c91001d80741d000c0c40764000c140c003c42e150f51001502c5091420060b011102c5400c0451184c1c451601550f4400302ca801e0380c0000d10041d4072440c01c00c200c41d0801000d80c80f000c1d0180450321400700307690010750350590000301c010b00100c1042100f00c2203460403c02900c0b840c081603119500e400e800d000000d0090f529140c07000c4500c810403055a441d030002090f80c00d0869001d40c20010b207143c000c500ca490b100c0041d0b00403001912a45c0d102c0303500c40411031400c61000c059161107801c28070200700180102d421750340c184482d5070051600480680040707005040aa2007002c1c0a08103906402d0926803040c202d00c250307030196400b0b580da9525443c3c1705940340702d901c0e801044424905014103040002100452545c101458481c90b100b48030313000922504 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 464786951 1250 464785701 464785709
    0xf07030e010e1e030d02010b130221040b04120e0f06070516180b0a030c2112111006080d050a051606020a0305060301290f0402070c0816051003020a0315 67
    0xd6407140000b0f2074501000060100190392000b404404c0d100c01c0860a00c000074080c519125401285132011210440303100e0800b41034000d0b2000d00340c43c003401c0c081074188050301c0589451a4460f41c0074841c510400401c8085440901222101c080380401c0c80f00551042c401070320030340211080b0b0102d0408510410000f043d850900f0494403108001ca0000c5900d00c0c0d42d59842904016001c000240e00700c0880c0c0212035101d905102a03c600705020300d04008508001445a4201510704204030b409c540b400b0b50405109003240d1880c048050010222812401340d0310203a800f035140e502c4060f104800404c0c251210746030603400c1c0140110700c00b500303d0a0041c12202541c0100d950446c207581489000e40c024401c030000d0045180f03034a140040c8184104811080c031f1001810708a140e103403844010907803c03019004544e560f142d0300b0081300210399400380c01e0301d034010320041c10500385041c1003000c02e482c0b00610200107540c881c4801c0c0c000394007a400c070b0014580c603013441ca41100c503520356220041c = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 464788201 1250 464786951 464786989
    0x80f040f03051006181a13020a11010e03070f020109031b092304030e0d0b0f0a0b03063102030618010c020313090e03070b0109060303020c060f07030e010e 68
    0x40d030651901504009410b20f1078400280351040412003c0e41000c100c114190312004000f440c00f6100b942c0c800303100d020140f2a0f402907405802c80360b589031154002d03d4204060b5a80050041d102c13006142650050b0400942c10382c130500484002c03030b900114000a080c030504102d2103c2e0381e42d5990608520003038425506100c0030000800818031035001d011400d038403502c0c4100315026001000c01c200200075201404101c8a01c0304a002601ca0102d419800394002c148000c0c44c2c6440c030308070440180201c580386012410304601c450b03079060001d00f0700e005030b0340d01861700c00d20008040ca11900b0f4001c0c07c0282c6d01c0b807400b1441003015031018001d19020340c00c111101c4503450008038005080d54070a06503d400c65008001d69a00416140c0d0114299900000042001d503c004041403441c010640d014007043c1c951400082d410007982e0080003164465025503201a104604020035801001e1150b12001c3e003c204440009108800200b20020141000d4090074249804a511091114503c81034 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 464789451 1250 464788201 464788229
    0x3031804090f1410061224020d021803010908040e090109020406060503040c0f060e060c2b020715080f0910020a05070507080712170c01090609020126060d080f04 71
    0x50f801032000c070341c03959010034007804403030715084001d000c407444c08101601054040300a0002c48580f1010341d40000e5881c0c3c404e41d02c601000c2c22410080d4030030807031507110740c0c036000f0707001c1c0e10381018090012880d41003003503c0c1c14507290840d0390420a5004041040c9035584102d400d0040c0c0d40c0d0300c1900d002c0d040658445840c6d240924285007040d282d03400c203000c106030501041088680c80038116080500035510180c039030955850980c81d00742010b040c41a18070001c2050907400203003046210302c0b00b8450b800c4031034a036074614465520b040340c01400000100c0000006040c01101e0024a42000c008001c881d074100c0107031401c030202d030000104000011000200b031010b210081000801030150040900461490700301e2140c400064044024401c0d911201e4420010f840390094400c801d80d04d42c001d000000c69443e020000b005888401ca01250040303440706400126200003040604114495103c07581b034004c1004004190808205e4800070104180240f40c0041400350000b0300158903400c00c = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 464790701 1250 464789451 464789483
    0x2010b03031606050a15060c15180210030605130e03130e010f08030315091e0f3103140412140705030609030d0b0105190e040b060903031804090f 64
    0x5442c00500945101810150380311b045240c03103400c4070704892050030035030b641d500303540761003100d100350115980b03080b6141130004841203214070b1103004168400c507211402c4103031174031095044035014000e46801c0002c002c100713110b80586602980f88085003a003200d003401c220b46803540d4604d00e103030011050071000e10010071200c03140c6d07018000038001840c05982140346c00b0840310501d5210380f0300c0903c1540c0b2440483c3d01091401c040440c2e4074039501480e295458105411048a001501e6102200340e440044030f006a120016000310f0030601901c0c010b60304a240c03411240409250a4030f100c0349420080010028090000340601920511107105031821495003142030845a91009019030003600411105180c0071048414034a03540c0c134001134421380312004071500d000355000c100050301c10400c0401140d1b0000178246c141141202c00b400064506010700a030cc0c0074255600d84c160780301703021710740343d0680d6400d000f2210140a080000c81e003060b500d40d0070028140400943e4201e801c408810 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 464791951 1250 464790701 464790713
    0x19110d060303021915050a140c1c06291c0b09130804150917011a0102030906040603051519030507050906130513020a090b0f100203041502010b030316 66
    0x100c0c3d01003040d1601000761940b91036090290700409425007000b6075800004d0300d860ba5a2303020343c1200c9800c0400c14820f180c0f07034509030700070f81c4217034104404c0c10b10381086000c103005680034803801d40d20100c20341d031346441800a2405511020700e00a500941080c0302c500032041d01d100030125804541c19021a074660060306003e600540601307a46240c110130000e050210780903008030b070125411a079181050480c41e481c04c40d000b00301034000b07a0001140c0d4055800c180360540261329020002140c01c948070381000300591f503a12a007507032240c00540a0000b008a28003982c03041c1d07803003403803d2804101c1441d9400000c0740c504101104403821400000e0500901004011032030240c0005e445006c11406e00e800020303c0000141d820305507541c0ca91000446050b16100d0840c4015405448042c0441d00e403c000c6001c0e00700d030350010303000c0d200d031005840c15454050035a4400a11680103985014142140301d244008440101800c0d5900c0c1e920088480c0c4003003001b001c010340040c83c4040400041d140c00303 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 464793201 1250 464791951 464791963
    0xe03040501200322030605131e0b151504060206040b010608071b060902041d010b040504020a1403150103030203030105100e091f03050307060b18010e19110d06030302 73
    0x45560400082c0d034404103500c00070440700c1d210768080c0105030f070000f19050507801c1e82070b42d0001400700d404c04040c003004030490303640e450b5180d101e40c42d1825985d81050018568000020000c0c04400c0c181d40400d000d00101c103210944058080c2840701c102d152580800d40961090340701d83d005a100da8100410300900c00081405021503140681590610943c0102041e556500c1c141000f0714080c2130750100300b1240c0c00070308103941c094030a00c00700201369804c0e9261640000f818009500704030031081c0c10b103414410f40344540e0703005040c10070306400c1600301e02103900020350a035014400d5015540c15a030541c11500c0c02948079038000d50356036050000780001403070b4400104042c4043c54040074a00e03550059203581c40201d00e183e860230003102040711400ca100640c805000e034000000da00f070a0001036085010500010364901d00204a00c85050300f4541c3c0034443c84080c80c0400002c10f081e60090f81010740303901052800419410608582180c055210710004102640d0364002002015018058 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 464794451 1250 464793201 464793227
    0x130b190f020d0c06110417071503290d17251511040504020c070f050a030b15181302120102180121060303020d110102071101110708010e03040501 64
    0x608110b2402c01c8025180031000800188029240c03002c90210a400d903056a0040890091152690445440460b29100107000c0e105080ca0206c0460900d54000d0042c40ca4105081c0f105c0b000c5114100d00305100403034912045688101034071104004a80395040000561601403801592200009541e1102000007400650f09041140c0054041005240021064030a905010031030940031207091015116680055a01c1440810240d0546200040030001d03500306001c100150b43c0c68a0400009040b144801071803c1100c0f00020702450114082000360400a403240c0020101500e82c800342000440303c020b81c03882c40c00d400005602d03001c0803903507403c1e00b081d001314078160145410010341c002c41c81c9045d050208040e9104400f64204a40c070903400b51044041080035224a402510381d5980e07030603c400502d001ca85011000d20601c03ca0714400c5c1d102c1d10030031054a0740c40041d40e012450000c10350790340c054100001001a401e0240c0d150038800d1401641d80c440c1010005046d083c0c005007 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 464795701 1250 464794451 464794453
    0xf150108010b090f0411032403010b0a051306050436050c190b0c160609060e0d110306012904080a030c0f1505060a0504020c070b130b190f02 62
    0x4100310120380b8215010b031a030a9944180010102000c64017400e0506007210401400008020030020090300007659031814080300000e101600b01003500b40d03440281402d600c5458a2001c100501e030101a400e12034910b440301045142c4e40342c0006003220318400c1802000181e10001044c14500e14181c50070002c0c01d4141c62800341c0e129151517645842905649004a45520a003800810322004034401440c2815000b0b60710010021702c180c40301580c0441e01c401c200340b210f004c606180640303150016280f032546d0f030b45030b081d1400c01000004401c0740001d49130040004102103075034501b844505d0103022f11746000c2020206042503180800743c10040c00118000c10f000a0107014401b140030304040ba00761510818580307180c14250001141100b004042d9007607030030b806200c0002c075000303548220401c445080d1801d58800501059200309061484d654000300340c14040d100b14200a0007000d1740488a0400075911090029056440710440d40b03a004a281c0705240c0c100e90001c00310a0307101683c8 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 464796951 1250 464795701 464795717
    0x50a122c0102030403080c0a110609030405010212030c0324040c0c0309050d0507140102030c0f1b042f0405060c01020403110a08030d0207030c21080a0b010e01050c070902030f1501 79
    0x2d03c006240a00280101d510302d51f00040340a4401d1280f406500459010403c1d0365482c20300301e20f180c0d40ca6104d0b103c0c15003d40102d045114190341c4090a82e031150100700001072455a03001d428a01c41d8904c5403640c500724540451300181501c49118142003800641c55175910fa50181c2001b41022000d544464401d061074208000041c90201e100412909150071165515560f040140d0a501910121513854822900c0b0150160400200101c0400d0644c1070311070746148e1070083c001501c0c007424108104110700780761094644280304540c00301c0d050100410f404d054a800001d00c203030340410130703908080e900454180b05005100d542c201140a084506140c1d030741c41c101240b0303128040c8500e00c0105507800b003404012f1600a1890188a561101c0030110b41003100d843d1440200d1010400000134440d0000503205850354400c1000c40c440503100c1c04207074800140111100e5000c4204e0025902130b19070000380111107030000c0d40c0910104d034001c41e0546000b03aa0044650a00502d080c10010703d5 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 464798201 1250 464796951 464796953
    0x1f03050a051f030b130f081306080c0316021f0f11131a0f030103030906020c0d02150d0e07170d08040f03031d070b0307020c1906050a122c01020304 65
    0x207050301da084030f6210754140c100c1d9480e020214405c0d2004940644503482c8500b07003800700007c200c01403040340c02e20000200207a88802c0e08842100e4100c07800c42503c00c04102040c681c88004088400c0c5442c1031046a50100762154000d06c20001000c00000907034480148070886100c900400d80e10030f80106e0b0700390518120000c40207108209200b80801034480110101d0405c0c09182210305c5041440e80081d540c0d6582d15005000000d0b920402c00140151140102c0d249840d900c41c90166400070010345000c038103072030071202962000310901c5005654500040d0040002c0c45041c004102500b8210501002100054280208404240304000200381004009103040b0742d40000586c1510300000c18046c0410107151041441c0314007012803103035490008051700e0990017184207051641c01d03181f1401e011000d0044241d11920f5401c00b00450701e80038031480d03121704042c1c0100340c86c0b868803000040220001c2021208040460f8506090b44081c0e481d220714149402c4070701441c0f40e8001c501d180b507d = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 464799451 1250 464798201 464798251
    0x1209011b0e1503040812100b12040201030b0603060f1c060e210301060219060b03031903150e040206070f0222110406020d201504050f01020301060215061f03050a05 72
    0x81c0d9402c0322101b0f1001004500003204a201b8100030b0701c10b45940c15030750090750900c1150041c084908900285c1000302070715941c200102030f240101806070541c594840c1d208108900c3c030741c02248201e505040340c0c50b03400208010b03000340440c010040018100b00301d00614141c4030305500c2e50b80000201c904000420541d6070000b82c251000000005a4142928900d00300001d081a684840e525210120b80030300800904121717018404800c0c9c900700a4908030b4a006404041c1502c0381c0400f000c0c0d82d10000b00903061003401800c140744078882c40d40c0d00e034200d035001412010800c0d4500c400b03100070110140003c00540311b4505016840420701e428545000002569034030b00480d04802c02c100c002c00d21261986094101e002d054005041d80c103e4451107820004a0008480507500c0344074001d9800c0b184001807007102d0595a01fa4041c00b803c0a441421035a43e41c0d007c0d0441d600149450441d1080090840110304005003698000c40d0714141100c5201c103880e0050700e02000860386410701303200111 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 464800701 1250 464799451 464799457
    0x3020a09090b040b101a0c0d020d0c020d140f0601150201050126010603080406030b010e0a080304030b090a050d081f060e100215040f0c09050c1209011b0e15030408 72
    0x40c4c8940a100700c1e5465044c03440d074420301075002d10556030320814000c11100c00300c0094524524003004492400d2503200040303a58400c02c440e40000306a8180d511000760500306007260403980a000070a00300d49031034140c146000c0409003170102c15001407005000f01f42004c0e0032480b404a10b84028025541030140410a08010b5171111801075030140d141500200207400640c002d54010403913a464a50364070001d03028140900b22540000d183c032650102511b484040742c41038540100c015406c040c01c41d9181542c1c0c40001c0d00501c0745d8414a0211000900104480d80d122119036403004000d0070008008c0701c212020107a02901318410381814046160701c46074071302045000315020540301c800000301340c1c01e0280d4146144010840c030000c21092108101c0080c1c0d90921440110514554440250302212805c3c1d918000100c0708002c000124000d00245e41e0700444280700001d100640c03440040034180b0385071a200045503051880850034540700340788408264a01041c18954505a5618182c0c0d01c = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 464801951 1250 464800701 464800703
    0x3011202010c050a0501050114030105040c0b071b081b040e0d050d1d0c01080708100302011d0306040c03050105090a0503090402070303060503060405010212070e2101020d020d020403020a09090b04 86
    0x22414294040035a8856076010030032503081019100d5410a80c00c216010302001d0080000040e00315483c0d03541820b051040500c03c0ba00080028040d80c20b01801402541c01807406035400c2c40300040c45502d086046501d4070041007044018a1a05802c0c5040d0002c030f0b0b54410814821898044103400c5c002000c03441d03001c0342c40030b49040c55540c0f07500d02104004002103c50b402003400056a2003410041c009040b02c20b481c001d0300c0d110b1055540c031030201c0e4500c17030880b180d414020710101c0410040d4040d4110b1603101c44100c008040b00702180011919002040390107a8803081440010002d21400b80319503904685004081c1021a540e522400c0c1c1d2172290580031070145a002030303442c0138503200394004005030500030280c680c1420030f41031980c041d41080d080108003ca40d5404a11828042c04209103801c0000d0720401440081c054100d4a0049900c06041655020410321b914841c083c030003050112014200103071114114011301c00200b18582040c100700340740070b8100d400b281c03044002e0340c0d00c1 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 464803201 1250 464801951 464801969
    0x6060a080f18030a051210030314070203100f1d07050f2704080d1505010f050307120c110609010b15070816080a3c020a08040603051e0c0301 62
    0x20b0316400c00c5080b5110969880034114040401c100c07040c0da90010042c40c030116691220845500d1310070500d800c9030071901c0010003080580046460508105026001075400203054076402e451070b82e0801c084c1c541c100629250a075980f05540002c50404458601c4881c0c0c0900400c02c041c200401b0801d02028109402c0c4104940c41c104000b0499810340241c00030041d107000101c0d42000c3c50501c4240c0c1104002400d0340b0b003802000128180230072180011204c0507543d8030421000f6000960300e5074800f602203420898113652000b0120204d008181080b01c6545e103400c0315205007401d5900301407024010b040f65174100301240340150b40b890303c000710010141020070b0b6100c5184c6082e4003d0300c200b00040d0f0b045050519218180b01d8503201416940c40241c580c0a5000502801100380e034001141c00c88401d0403640c26160300010403c0c2d40c8040300b51a0040f560901100e4441e42e500f80c100da8495000a501d482c1000b61a034131509040d12000807143d0102c0303941c185448142c21038001401350000d0 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 464804451 1250 464803201 464803231
    0x30f0d08130807150c1407020907030c05091008060a0b04120305220f030627062004120c0b04030c031101120f0608060105010c02060409050709050a080c030606060a08 73
    0x5001d001c0b411144800d6000c10448140c07060100840b02904500e000500030440c00300c042d030a40c40c10302003120b4025900500c224050366801009800038082c01c00707000e0030080b0600c5080c0d134588a5400030021000741d40c403140750728540b04c070070413003615801d030400502c9003000c0c00100981c42c50780100c04102507141c10816280c082c0c2c04030020440304051258880342c0c103c820009105503d004030301d41500c0c01070a052040300c05e030211000300b04015001d405550340303001600001241c00f5030b0004c0c8611480f00001d0700c1241c894880d004040d0415001101041d8556007490104408820040010900e04450504052464550042444103480003410a400c80c0381b10019a80c49040c2c8a0945901001d0410200e080e05c04c1c000010051400b490354548203601c0046603545c00341301e0460b203041d070040c00103143c282003408c0700000c0c01015020205204591001188603a2084110030203001c03046c00402c41d02d14100205868a031010b00341c039000740c1e010001d127034480d0742c89202d45900404904040349 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 464805701 1250 464804451 464804453
    0x610091205031e0301030302011404021c060209030a140105071b06090611031f06020c1302090612040f0501050601050a08010e0721061e0503031b101505030f0d0813 72
    0x802e40c46156071420410395050340e8103541600e064040d5040c3c034001c1d03000704003841502c08011041042602e0180d40401c051409422102560b004c2903003462003200c003d403c0c40602404a89801102d803400c03158441c4906801d5000002441081c0e0b010800d49010700800c90300d4180004528400c42015110a0301d801643c4141f000766089010544a507055903503591a003c20401703181c41e400406c680c1c81c02007402001501c90b100064072810410000c0c0860004003240c01108005e510400d50383c3c0e0000800d024002e50b82034100300c040d00c514051000c84420a2891418038216800180b040d418003005000e107011113a80300800d00d040d034141d400300c17000c1500c0f419001d851000900c0209045081c0520f26000222680e0708554203d643c0303000d034504605946c0c0c00d182080d0080313010f002e425910a1082540e07512880c4062640c0c07400f07001c150b501480c01010504e0950f44e80c180100001500508200140d05080281000c0c041c150303030142402c124000d20050140401510012643c1c105c041d03440 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 464806951 1250 464805701 464805703
    0x1603020913050d080402041b0206011401020c061305030709050c070b041b031203060801020f090402131205010203190c0e10180e0f1006121d060a06030b0610091205 72
    0x1c8510340110403144000303550403006005200494089002c3c0341420700065500e200300c0d40300c58002d0b90300d4002e441660b00340b004a030800e6002c60001c0381184030319a0f03003001c1a1107a000911500607400891903400b400c007001d16140414903030008103003c0c50101040b551b00181d0060740e1100341c1c0b08000f00aa52211304221080e0031a0030450340d42c1200c00300e80002004207407052036840d210075840901405689012060807800760700706080c000401041301640c0c03031500ea40180440040340f804500f0700c58541610000031403440b4030032030303041e0f6000062040c000315043c84442074a071000424807400e070041000501468070000080e0060701e000700ea0101c244e018a002d403a0000715580c50003c9603a40b003004100c5a942512107a500c2204071001c580b4420032002c900c41510b141da02c0700c01540f070707c81d1041401400300312191401d80f400c1180c0000d8000050060030b000300c01e50a0082801829800c08038021a0013910342446008182c0c424080d95401480500403910100c545417101c0e0b14509080b = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 464808201 1250 464806951 464806981
    0x8070c080d020f06060d171e0309160e01050f0906030c04090b0f010f030f030e1906030e1203090705090901090812010305060a060621110f180316030209 67
    0x150385004900409004940c0054030000c0c24607008200c410644449060003145d140303038000504840c8445410b11a070b0400c1000500c103400c000c002c010304125200001d82c0c100d8005582c400c4041c2c1100d144940f42d44201d07800500944012604002d05514000014014044051015024894580000f44030ba40c080c48001c1e680c4d64050414014041e4910301140c0004089518982444000e070010450501c42001001601c3d40407220300e02e0703081c1640b401c0d103100000900050340015180709120007290321703040b444c009084940b0081083d8000066031801c0072488100d10b40010001e00800400c1030001503003c04440050718020031580380c20035000d0241c1040d41c4041c0080200185a034580826480c6e683e040741d001c0c205071b5055490b47c406550035a1720794414880060f02100307500180c402411142d400c0084816000110a140030300d98107455000150f5901d107540c2c0100c2d40007120b00b0300703040501620504401401540d030f41c225039489030074a10701019029500c50350010f0421203c410030 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 464809451 1250 464808201 464808209
    0x8040b01240323101e0605030613090813090e010c09120f02120a0215030f010314031209030405100201231f090b010f0804030804111513031b06050708070c 68
    0x600c441d213080c0c0055001003559100314041c010320403500340d6000ea498020350701075510550302c071441d6072102c7e01001490181010340444a03a500c2c0c403210005902c842c010110954904414241a440c280d0150122a86019454a56410b05100301e00300d990003003a00e81a00c904c80001d600140460034005140358079034800030742020b201c6c0c000c0b89034504005041030a00d48200c2c3c8180210103c0f4079280c1840c0404e807044450320241400600c0000c0001d480d10400c81140000c40b420f0510301802000a40f100340c0c2c1c5001c09810014060205051030317818401c011000e40001c0c801e8156602c440ca1484504100b840920801c02c400b00c1c100789103003050041c548004549000c013140c0c55404020040510210b15070100700081d02b40040280520b01440c4030b01e401d034071111402d036100e482e0810b06543e00300007180c1c0081640100b0061950300740240140f031040385403407030181b8214600703807030b070100105040209402050410030580e64060219122607501859454030783c06945001180c010007900 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 464810701 1250 464809451 464809511
    0x2a020f0610080d09030b16030e011509110702010c060b0109030210030516090311090405010b060d1409030309031602060405040603050604031706012c1008040b012403 73
    0x1003440010071038a90080207548031442543c2d06100910381c29a00301020348401440c080d0a40d000810002d5101480791940b121070402003040d00b9609403450850318500c40c6032000401c214414080750b0901d128000c0400c860f190064275281143d00041c0810b6000003000b4044e83d100c050702076143c2d124003908802150301411100e00079040343c40240141c00100c1c0c1c00d1046920100d000018540300c1c00741c64003241c1d0000803000b880e080243c24045e02910050007a81d2039901c4802440107034444200a10508111540000c1c0515003820024030b038510240c003114840d40300b072043c84200c9001000715891400d4a0b102e1440c81210b91020681c00d0055034400d40d0b01c41d14105001080c04000321300e003032045101e65501e017003040300540b000c0c40d083e600b0f907160340c00a840e0b03010200b4050690740c100000c00c050440c41c0c1e0911028040011141c01400300c600300020f0340c010520007044020710070240176210001d1841240161400c80390b502c081e501e88180300700341d02c407001034040680c100d0011040c0c40c0480 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 464811951 1250 464810701 464810713
    0x309010b18010e2202130b060315012c0d03020c0a0f170a120e120f0f0d02010603050a020f010c0b0f090c0a050a0603020c070b0a021c032a020f 63
    0x162000e089150034414410000303c424002066078029015040d030011400c0c0c0781034580c00140e005d1000c540e45031544110042d64030301e21070b00555030702d8014520805c02800c0c5a40c2941220f0001030540b211a100d02040588a1000d05010804420206400001031346c1c0b04083c0e01290400301d00d800881001c10760010004007003c41d05014a0090340199021080c42043c03c034150200b0fa650381c1150900035148541040c10300e80d0f644d01c503a2241c2c0401100802c0f51583e440c604020b24208101c80040c0c070000c1e40301d0000400304200c10f201c1c8403070300b502d00d00080040c50724545810b6180c01c03202500074403803c102c1d00701106980c0600c00700704070390790400441c1c0d016103000322400c2d4070200c05a039022403a2048110403001440c1680301c030800e4a00180c100380107145000d100740c001c0e4100030006010780c0110200070900d0746400d0064040081103074010030490300300c4003116610404880c0d9807030070503007044294200071540d0200030301d200303000e0100c01b40c14108440089007000c440300000c0c40c560240c0 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 464813201 1250 464811951 464811979
    0x5040c02030d14060103060b2d1b01020d230103020402090d051603050f0f10090203150703060303030b04140f0910091a0702010608190609020604090509300309010b 72
    0xc43c4010740724036420b881c1008841c0c1c40c0c540e0804d15004104040c000c26500502d0804181020481488000a003003441e0381029800c054012411603603c02c0000c0d40d81d8007280c1d10448170014040c0034190810440c0703003c00d2144109011402a00501002c0e01407600020310160580360f14501c105050382100c2542c0d08006500c0d8000c4c07050312542b10544507441a19000a003444000c0780040ca049021401400d500c0300d81c00c0301c00083d26032804180d915000e00b00700c800c801222090750b544070b01d403281d034005065801c1d458068200c421101c4800d01541c908000d51a00c110708612036600140b0702c4840140716902e918910349000008400c28541d2420084080c4c20004c20500809410240101d04003096641040032800c0310043e20130140e550f40407900044204801e80102e00c01907014102c04281c0b00e04540114030303190b125a011b8a4025554402c20180903014000b040b00040004120001e588240c111020303a030b0a45c4048508040e0b0000203c0d60045095004550034040074000c0d80f608242 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 464814451 1250 464813201 464813231
    0x1504020d0807050c0901050f010203180a080304062c0a03030e0f030129100c0b0c07080a08011809051228110601080109020306040b040602090301050c04050301060b0708030105040c02030d 82
    0x101010079005c1c800507400070400e0302d0100e045a11848044c7e0042d41400601504013281c4007084007004c2d000080d400300031405040602c024000f5043e01c0e241c41441140300500c4070040d403161800c005085802d4402d0000550f10142c400c2d0450b600361410b109000c03d450001042e0182119006615602e0309178004019103541141307000030024161a02e804203075070424014100030341c4540100140c482c08004000414070248036070040340b950720540c200340403544e8084095000441050125000100400101041d04200016203280c20000e0100c1d60b065907846035954103800c00116504008038641a083e083c1c14a4025403211f030807403401d02420207002c00741c0120161880e11026001b0074001054001050050820769540a40113110503a1103440381a003980010340308442982c0c080100d00d103280d609006950040301140d58882c0c4e80c0349003034109400c40c2c64540c81610416824000031000c95051801d40381100e00c00d443c08285c2c2c4400c070108a0451168a01590445103405454400030039 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 464815701 1250 464814451 464814463
    0x621010609110316110a0f03080609090d0e01030209040b06030f0609061c03081801050906070809070b0403060903020a0f08090411040e04030309030e120a060b121504020d080705 78
    0x70304544100035a60809180c00807901c0708444030b000a00d181404503c0c00c03482650040c5000b40d843c82a02c12400d4680d46210414000d15025000075030706400f400030300d01d041001150807101000062804450070480900440c2102070042c2c103250b40460001ca16449642103201484801498030fa980c0c40c0c2890100c042050540d58180103078905000912241400e07103841c8010180e0000d00882d0041c80e0b0350480b01220b00034019014400c0d02c00700841100004d0150794005d83d01900507104a10b04110014a07030f17100106407826580c020301d0208500f1003c04100c40681c3d41000002c90f0841031410240d15180c00714800500601b60085505c05004400c5d01504d041402107600b13012140c2c040e4125007180c0540d000c1c0d00100984034010400003402540040c003582e10a04000310400a034000140e001480c09482208070b0f004042a1800c00242c2d01c520200b1040407500604600980b01883d907030b95102c602d071600f140380f40b04040f805658071580600c502e554402c0400d0340e80c030b4142c0f030b003691107031 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 464816951 1250 464815701 464815709
    0x30b010b0a0306150827251509090203100320010e010503070e060d0236061c09140f1b040c050304120908030d090212011a04020a03020904020309070f060905030a03050306210106 78
    0x12034404007107008c014170078210314001907c0c1d48410501d814072401900a5001515000754400d202d480040090310400300107000116a0124840f0740e4580c2001402602000b040c2c181000010000c200080390406d03c5052515401d0302e049450340d902980a00083c4162100f40ea1180c01301c0000c1d0030a03031610505d03031440d25401c001300e003030206800c401e00119008114210b810903041d80501403868603141c1c040c2d49014000c02c0c000407840c1c015140503003001c0c9450040115500b09818922012448203500b0301c0c210b400f664100300d1400c81d24002000b40c00040c1004004e071408103003201076907100710900c030042c3c00f082081d03d40c0c1d102100113310041401150890103862184421020a0018811401050b04044200503c001c0e4003041000030b42c031002d04a0b05044e0700340601d0005464a2001c0c41c8514690001400c0f000e080c4075101c1070342d0007542d1161041100a010500041d18082081c500c11607242c18683d440341c0702c41c030000700c25441c0c00303203440c0140428030f618000e041015040700080b1 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 464818201 1250 464816951 464817013
    0xc0e0a14100c110904020d0c060503070e0303040e0c0c03130803121e0a110d050f01050306280b010306030203031c0e030702030a1b030b010b0a0306150827 68
    0x11101d0310005440415034001c001d460905182007000f0141404520941c0c0f051000340804950909552081d07a41c44040d0407000015901000300b00c0c0032a08403042c85c089000841c003d5041624140d5042c03c003c9004015024110001c90401841c04d000c0060f2200080d40b440c40c5007a00c0e4660008560b2500855001448960700c0c5020030088644281d01400b452003404528000b50780d41c04034032001d00710000300250001401c011310f800020b0300b071180500803902c0c410f4550315035142c8800c05207803a000ae441607a03205088a45c8440901240c0c19402138030483c02c40200c0c801d103004006038014203113584040c0d0507010014211900c6000e11018590308440c01c0d80400c031088010103043c2d601e0003489002074143d4012031f2818003140410b0314414400e019a139904800c10b850ba80c403904540400e900451143d00d003c989612440c0d0140114805440d115030140126440d5800041c4404c1010704000603140c020345402600c03800107078200c0d013000c2940f0211006440d403402001500c002d40420040d00c = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 464819451 1250 464818201 464818219
    0x4030c0210050313030806060c030a03050603010e1f0908040b0a18060815040515030703120906170105090402040e0f030c01050f010b040b0c0307240506010c150c0e0a14 74
    0x111a00910a8a00135041ca40721a5070781000c6640030784649402134800341e0300c84000c0c8000080030601700b0041c14090b5007035802150f5400c00350140340c252495100750007082e07000003200c01104680003050341e43d03042504c107011030100c445003841d40c4070707118541020200038000243c0c0700107030303401c000d40020319200e41040e02c20007a5604070880b140c1100f51680f4050802e2141900098074154100b90f41008c0c2130700c0703103400201c9504002482c0402e2a81300702e07420040007a80300101500015504010300803420030b4101102010003280300d410381401950311500104000c10305540300c43c2e101a4180101404507000c14021740503055403500000011801d44d070034000000c005801c3c8018482c12142c1c900d0400d41814149003c2000304d401c01140d0200a02c010300140012400d071043c0c60229040705551355240b904010801402d80d00c00030101c03030611040c1701a080004d00c0d44500c903080004030390030024006000310400c80d244032140d018a03600c1041c2c400f003c15000d0303082ea02d907480c001e0104d5103e65 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 464820701 1250 464819451 464819479
    0xb0408090906090103020913061410081002030603071511070e0a06060203040b03070c030219060f29060a05090603100e06092202010509120f0f19022704030c02 70
    0x150f6420301740002074020554901203110f03031810b02055824240302c0c40001c0307401809400822a4500c0848140c1c2c04128464010080d040e401d004a4035083c50300d2105500d54a42800407075951026403180746c0868003e1001d40076076508c100100e00890b10020305590105a0302c210410008405541c15840507141040015019000104030303811140c0700340420f402c6540b02d980c2919203c80b0103030140e003580140c2e071000415550030041740200500c2040d00160000480207400211000d201ca850352034150b4141c0c10351407150034131030700323264070f80403151580d940b041201d04541c940034070844281c000d1f07004421300020741c21021200c8155038410000103034965400e07042104089042d01c045115001500d0041c100c5140e1880444d08980181452403809003610081180403483d40d51b01c014542095400c0f108078081400418140e0030500c00910000b04103d10200b6040f0317042c90300034841c0c041c1e0140414410715155030003c0b24202071b07220407900d2070700d8107006d003200e00c005000300c0c4aa501900c50305 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 464821951 1250 464820701 464820709
    0x28030915031a120a1709130203041104060e0406090c0b04090f0b0f0a1406071e050f0607170a0b190305190b01182903150408031f030b0408090906 64
    0x6101202000014913003080d0300e441c1d00740c066680c601d00c1800d101081050042e10384500b098001c008a50f004c0042c3e807803400341031a04032204211241c074401c90130300004200100c2c17080e0318540c0182c0c0091001a80100d2464404206100b5903c000c9441e040881d00150b00180b41d840380a080720801400e004038116641004031003010740d01240d500102c625814018207803910204401c80310701400192070003001e070700c52504038800702c41c1e1540700c01500452203003000001c0c0040501410454000c00442c10070020207440690b401c0e889031102a420000201e0140094001c441a12005403449100340c50f40d91455418141d41d00041e82c03184a1036000c40c0c4184c0c808807604884a40100703060003e6400c003007580700001c04400b540482991203952451800f0f481a44000c000841d4444000d030605100c81031500300040d502002054100480410003c968100110f0340d1054026098160880211f00c92400f072800e01c1d00050302c4104074800b0042088003050040c118010f08852400720782e9a128104 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 464823201 1250 464821951 464821969
    0xf010f05060a031e0501110d0c09081c020c13050103030212031603021606050f150f060901030902060f030106020313151e03020d0e0606040e28030915031a 68
    0x3075400002010080011802e81c10104c1c030411065140b10901c400117858090075140d69240044104000086131115004148580c001122103420548031491a043e9896120520380c420030703146110800703001c1ca080f4401c1c07003407104002c4000d14442c0c0644220f81d0660041100b40021030151060306000003862804c2c600340c3e0711a100b48004032449a0001d68110301a400c0040361a0311081406c0d40840014501c0c0529441080d420b5090042032030950700f040c54440801c0d101e240607074521940e146194580308121140004282004103420f001e61003c118184100210076560440200001c5401540840106240416410600b80a644807141c1d1042c0103c014455804242640f00b568a000e0f403003500101860a1400d00504100c4d541580c030098590740807542e01d0a802c9074003003003858500752056100002a1100410300220f8020300d624114030725050b0604642641140300e000c240c072403110040034086c0003800070046c51048402a000c0e110440d0004c0340210b44422f4085075040000070 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 464824451 1250 464823201 464823211
    0x901030c0c0c060c1e050d030b0109031e0f02060309030304120e031509030d1103010807060806060a05030a09020a1e1703090f0303041e0314030a0e010806031e0f010f05 74
    0x34412892030300c501590500c100c0d1380116100031031141044200c00e501000d500d11140290050200b001110070020100c0e284800001c3c14007101c0d1005101003039109049118840c4410a06036503a03061341054891401d911000a44c044000010005004404006540540d1064590f044403000d00c0e0003d54980300c40281240d01948009503400c54404507040d240c0c1c106070480c007070768902001080382d44255113401c810150b0700c844c0040100000c0c8810043d440c004c0c00789240c80541c0d8104080000c0031880b41110001c200100030010a504003c1907000c90b0141c0d50040030084d1040c3d65200500e0501e54044441800003a07000303000440c015a00d840500b01c45140e000740d40307015a044108141280724498440c0c06110910010030b00f23014034aa203610101c2e42c0e10540c0101c0385107140a1000c125403440740c0c46d01d07030800d0140840d1550000200010180f0900700791046541c0d44011910b0542403002e101ca1091044d80001c9400201084d0720710141740d00d13802840340b0310b1100010307415075000b604d03 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 464825701 1250 464824451 464824463
    0x15060304020607141603030e0402030903040605071e060c030c030e071e030204020408010222030201020c010813050703030519020c1c05030d020409290307060e03070308030406020901030c0c 83
    0x40014010325000c0000e0842502c9030011501001140c151305103400600003096003020345e05c00c0f09200f0f154010a1246001c4001c075001e41c6189008071301551a4011449204113011000c10341804000113058001446602c03007204c80c8034044c085c100a400741a04440210101e4a0720750302100c010f101c0c1c002e21300040070b444024034440d440d01d0301e05505031405030040c14400394042c40110040e6203e0004000500c49030b0b0003d80c94001c0da190340b4a4907456818107042c040140b030010001070341c01244c03800d201039090030041469550b116118401143c0038100070801d008204c804000c00d50080060300c01e80742d80c400d07180e0385e0480112081e03aa800903200b20507070108640c41d44500110303240145410b454402e41c2a81d0402d001c400e150b80a03600150040e90381c40ba10742442c0048400340d41003240005032b014010404940c001e1001c06d4840080740940b00030082090100c0d8266101040184001c541c02013500342d8034509401c010009400002c40640001e0500c170321006100d00c0349003607030f14030782d0410 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 464826951 1250 464825701 464825707
    0x60b0a17090f060405060603160f15031e092901151704052b050915041a0405040e030c070605030916060c0201030c080106021e250e1506 60
    0x500002000c440007852450a88600110480440d40510009004a2003035004040c41d0511004040c1089041501e118011006210420050b0f850409001c2201d800b01d0500800028000d030880c0903018000340c1c068045d40c5a801c07070702c84c0700c10b0340c2c801d010550065031414613540c280d4100b00100807901e80d10f4044160403100500c559110140011615551810503042d203039031801d81040328000850302601d240e0807001c00100004804000344c0e5108015600402181c260040080d005006440c01b0302e006840500c03160103200350303040884016081040c01522110540c3c0200041c66215000d514050380c101101c10055030b0300002a00c80c0c10020b5006408035a042c51811106074000412003801e0b0310803240800b030742c1c20b41641e040d8041c102c2581c0d0400e44050710b000140503640c11904d082c0400021500401041d6404504900481c4007480c00c4c100b64141000240d04d0001d049a58010168900c0d4800a02d0814001d04904455515500e030f40241d841052008001c500b820116030002020 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 464828201 1250 464826951 464826977
    0x3060d02010815090103120305070201110a180b0c0c01180302010206040209040c0b070b090d080424060f0803040515042603070c090b01181401050c030c03030a020706060b0a 76
    0x880c41150700140c0d41c80c2d0090302c120043c0010780740075020b81c011790b40010107140098800b035141c0a07007a800019800244614030b10399a03814140e101c1d1203600f1040006050011140b500003005050040544225213900c07000504140c2d600c0c0e008103d00540031402c103040604000380b001ca12b1000702e0b82c050300a0403159480c0c0d000e01903c9a0010310840e0348c180400404038000c660400540040380c000c0d5038107401c1d4585440340c245440031159509040c0705c620010400080c01006400b0080c2c0c1200d0100360030942d00485e000c000d80402c0e0842140e2000420011415100010107002220811070320101020020b583c103d01c0c903c514000e6500182c100c01108550024006902d01d1111440c4101e915180e065292400d9000490b0450408251202c4d841d881b50741e4040c400d100101a00d411781c50740e0500c0e01030010542544208030078140030021a540103180c90070f0040d5138110085038107881c3c1c0e920380401d00c10020360040c801182e10620301280494005d20f01d00c00d6400f0007106441c0d1544010034 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 464829451 1250 464828201 464828207
    0xb120609070902091f020303040308010b19110a051009030e100206010e1302041406191217090907050a020601060302160213020f0a051308060f0a051317120c03060d0201 74
    0x4941c03489a000743c8004880d04101716500311100811007164080c68507428149002081c084041c0d00030b4000940a103d160800500760009010b442c8a40c1484290910300f0581e403400d01c14007000140070360094003840840e040003500800b5a5522999504410301d0302c0204100c00000d0b074660302001680f0410050003210661242150450003061003c80c7c9005242e0018003071ba502d450403211151108000c2c0600c508111013802820700102000005040c104401356501e426680c002401c1c14480ca0007030303003103003c001c0c0c04c41e4407800014001071014a4000c001508a5000260000c014465000002400c510a100f0349218400c2091004030380580d035000c10461540c7c01403c202c40c240e08110785d508240d444002006d096460b07848550b2544404400a09084c60f964000130454003c1820000e80008000405234032084c421300c0042c0c1303916046c500300c806a4014000400c0d5a40f003100b030200c0b029064000d44000d009001440350719a0710510000c1c824042a84d42720b0700204024504001580 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 464830701 1250 464829451 464829457
    0x12030f0a0309030c2120151b0a05190e18040201090b0a030f060503030406021906150303080f1819031404090c2a020607051f0b120609070902 62
    0x20092500491030704061311541c02d54000e00030310328100c58600e0b41650780150403900400110100c6c04c145154000d03452045502c40c0c01040d07036030030440306000c00039803000c201e540d880d03001e4040102c1c0c0399100d40880c84041e01d80c0c0d00140c000400080d6200210a400348100f40c00b25803e0030117091341d0f20031b0400c10601403004030003a00480c140001480042061030b0320300090420300034286d80200d85400202c20036400c48640e600424043d800411060008a40004000b0a103040000ea0004501100e04210005142900c3c0d00f0201c00500100003080c194000d02c80f60241c0d20107a08641d2540b5456084461001030071003080003030300552840c0c10310014811090716000c2c02401d084c08981d110103c02ea0b410b40c01074008000c11a520452007425070303440481c90051419980c034012500c001c6d44441030344a800100000d00c5600006084400c06c88244070704a421141200060009101000418080c18840100c180180d0100c0c00180b0a001e000640c140100c610a0180c16487c1c2003500c0440658 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 464831951 1250 464830701 464830703
    0x201050a03021210050f0109080606060723061b030709061b0b1806090708030f0d0e031602030f1b09130215070309150e090601030f0e060612030f0a0309 67
    0x95401c0c4005007503d180200c105115030b1810311446042424081084000ca0b0010a60750420540c0c0b6010311102d48001000c64001c9070131544140c4071300c504d2500c1d02446159181d400304c0049200071010000b07900003049400b030280c404c0a0070071801d487d4101c0203035000450b40701001441501040280074040c0c4880171090200346400c5541a207a0b880d0020000c6d0251104000c0d03c0c00303209040d543c0f110601c8003981001511014210540c03414441c1c81c0d5901809094002140b0006601001047c0c198030602050b1750101c15a03031148017009054588009149003a4040d005002d602d000440e40800c00d00c10500198000c4a403000d0b00c2c0051102c1500020207040d802680b00740000d0241e0b58041030a041002c49200081da14002861f00a200314580e600560701804100a001403c5422a6001c01941401e488140a0b940c622004a010b440011024400749140c00c5c449500408003050542c86940700740c602c2da01c0031207500d00740d545d248550300c15103290761814040c20700c501c1e100e900180400d1b = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 464833201 1250 464831951 464831957
    0x40504080f04030807110a06020601180219022a0a090902040209030a05060717010b0f07301812140c060319150305031c023109060b070201050a 63
    0x4a8000c4603640c03648960000d84d90f80c1c1021408400b0031280000e4055400c00543e1454070300d80c0b80180c0a582c81c0f1040c014980300c0b0310446010090800103030b054448503c18081c0f903980c03405107264040e4555080c40350825586130804480034241882d0304081203c0d81014003200c0c3c1d402c0c0742200440052540b0041242e00039020400e4502c556001c0100003002405070300540380904000d407000c1c041603090400d48126031291401081201c2c100420740e0084100003445a03a20001c92420f503222810140d1032418045078034180081584003c0d5507840403400544800000612480248078030301c50910a04d0700d01024804c0050008a1110014240c11740c22000c8540c402096800250550411a0711180c2c80740342c4406008850510b00504909002801010440c1400c54a5141c0c891050668094a074000110384000907451581250400342140500441c4140061902040c81642c000c420001800c41e400c0403450980740c0c03080500729505c041070f40303240ca40c0e40da0041d100794001200702c6042c = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 464834451 1250 464833201 464833207
    0xa0b0d0f1103040503030105011b02090402040b01200304331107270606080609070815030703080703020f0f1902011b110306010b0a05090d020d080f040f210204050408 73
    0x1c11040c1c02550246108901541e100c1d8100000149081c80108100904443c0509411f0140e110300e010030ba00b054040d00c010030607114080040ea0789109140c090b115101c3c81c03159100e060400400900241c6022001e00d620200c2407503490420402c81903401e506100c103800b07103441281d025450305042409084255031145542d40000390781c03d081030402c0501c0050013801e925603e48a44901005000709081507202800c100004c00c245840c02040c1109004000e00880e2030201a10b8481c04021001812a21001d0301d82c50050100d40000000702e01510500074029201303c80402c003502100034031401130a0f001075414195460022122050341800341941d1580500590100e5251102d400741c044412001c1403207051500d0004141d202c0c01c40e0310f40c00c2c4903454003164088101c032035440d42101c1308003018200d030001421b84501c0780c0009018980c001020220306c0702000c060800c8800c2188000c2084d55507102c05c211002e022a51951190400d03080c0000515043d800141c005001341003c0741 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 464835701 1250 464834451 464834471
    0x90b0102010c201e0105011401030c020c1203130303020a020a06030605010212130b04090e0d031505060c0f0a14060f07050d0f20091306080601060c1a1003030e0a0b0d0f 74
    0x185021144c2a6801281d444100602402e500d40c80e1b4491030502c00e180c100080100c0b400700940f01c80d41c142c4014840c2940a009032a200c10401c140c0d8420100c030085602215a02c1c60040c0d81d9525201040340184040000012080d00038402c03202290812f80103001c41c00a942c08040d42c540c4269404c042c444d0201a02082019859001d0405803854220001d00d1601d903201003850009030f42000d00c10181004042e0364042d140344020701c110740f07065403119190300e0b018101c5c90400d000301030861000d208529040c0144030a46800d2044035906c2800e841d0700b5103a01c4081551a08126546c43c04588204410400b02d91903521075a1a1208444001088101804200300060120031064192180400c1c449514a420251020490012502080603d140203a07564440c0d03814400c8805005614142c40180300090002d40b50a10118200310b03a603140c002c0d038110090145020130b5000500460b08070000c3d042c8447c9400c29102404030050802010144280c040c1220102c1c1c1e808850305c0703440c820f0b = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 464836951 1250 464835701 464835733
    0x1060306060b0a11070510030b061204030905092409150a0306020c0705040b1c02061c090b01050d0506060405090f0f0318031203010b131509090b0102010c20 69
    0x54401c0102d07542d80c8281c42c0400904d0825684100c415030341103500208020741c0d0780c030920603015000d82000700f02c1c2c1d0100c0c0d0002e2050300444d080c02c0d040d05c400b00100001c16038401e10580c141d80e4121144d403040c2e15400b5400800b0300910400d080f01e10003600c101100d6141040955900c10b200c5001105203c030014041481d80c90a40d000f180e01980105141803890700c140302e0000503000517202000101070030340000f11502e003a608880301d0038100c03030149d80c107644a880444281c030203000b18009403a040d0341d00003001014016029110960700d94008641031a28912798200c0d150448020302d010f40720b01c01001300800001e0a020190301c18542505e041c44d1041c0011038842d00200b02564480300703a40c0200c4010100404660f10076080b039814002e0054891003079030305640b00d0400c0780340c540401da4601b5800741c1c45a0040091383c03101c059140c0380d00d42d020480c1d106803503480d5402d2050039045001642030325514103d100100384801d8180c40039000114002c0402d8030007000301d9052a1a0b96820 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 464838201 1250 464836951 464836961
    0x314030a0902271302010c020d1109010b0405090601030908031b04051507050708030306030a17160602030601092103030902040902091f0602150a202217070506030901060306 76
    0x20216044500100b00c56403125804455032100b81d000714001003940c9179000900b083c040a9009214540303050700300b01880442c040000c80d00401501026441d6125880703811641c0052140910a04492000690b00d51103070181140d0503030700405040c1161209246280d49100b00c0044080035401848001050f6403908821400076440340910759a030559400e05906001e405d410a0b04103500800500803940c40000d900d8001c6034001e4140c082441c0b0786810180d840c4214101d00c00c030802070200c0c00e014804c0300e034019405031109803070b80d10300c86640d03601d031948620088520f800300200b0401001c01190003600044603130f603c02000042d005041d90b001034121001540d51010403003440a228104260402c01900039080300d0005000d01c00740c0c01050301500344010031114040d5150620500303200000244180c0c4000550009501d86d0301805800074001c00005401345000640c00c0c0c0000d0501d030581a801c440342100010744643c4d41408103104807544040c2c440ac88035940d0310800030101d42c80d4451 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 464839451 1250 464838201 464838229
    0x5030105060d0f060f090509070506090913050d0f0f08010602030406031a0a0306020309120c06061005070606080d020115120f02130f0c1706010c24050f10080303040314030a0902 78
    0x100d0205c0c0c9041581001c00c644d002440c10416511885091200e9903030203098611078041210003d400e079807400a17004a0440d1120000d003148104004405055004055841a184141d40d616110083c4400448a00000788100000758004010512202e8401d422404002c521158040c0040c840c000c04208110000e07401602d11690100034801140e074280000140018800c4009003401286003c4548941015151078031420508071200b5915001e242a55105c1c1e030020b104100c56a5a482050b4036024440c011700019442c0c02c0d034890503004100e4025080d85c000006019601c0c4c003550b00c440b60f0716910b18091780d11030340174101c000d81c008250185c80c500004021010561040812002d800ba0021385002050500c4200400c440d40c3d03400f0418024080e0040040ea0b0f00203100c505495461203140300c80c000f0a13040174200400c10143c1401c0b64000c145543c00c41c0c00450b85e512040d51070340403d07180100090692a580d20342448050007540c0c0040041d24001800e8403180c0c0040c50894203c84 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 464840701 1250 464839451 464839469
    0x9080304030c17030a050315040605031006060201110703051207020102191d060414012307030c26030703052502060402120706050706050903130f080f0d05030105060d0f06 75
    0x5800d001c03c5115a02e180d030b4600c4820019418404d1310300014061340001010340110b00038a00c0412940d5889810040c0140307000341c02d80325426061000540500141e02a070302c00756080031882d00789810360300f007190300c0c29825907a000d04002215030f00c0c00009030040c00c902c0440d9020b001302e480468458803512a0821103444059000021800410b0311100f41449680701da40203200401000d071100422510500c2d017441c00190300ca5440315030b401030707401801300c0c000c8500700829040c007011f030440c1c5401d440c54010100941c040444240c90890920500c048070302804e0280b0100d407203503000b42c00045d0800b2118410800b500c80004580d401c40041904c2c10780168400400d200c2503082440403104100c1c2c6840203000c0013800c260f0064410700c00e10300d0041907541d88900150004205000ba02c0c032100540051aa2090343c840078208002660302480d51280039041b414681032000203808840c40ca03254451500750780c030f88410002e564210001481d1416201e5101000c0e42c10b07680305000213403660359 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 464841951 1250 464840701 464840723
    0x510050a03110723120c0a03030609020c0c0d05070902190e0f010e1009030c0b041d06030607080601020a060e010501060207060c0203060606090d0b0412030c08071e0908030403 77
    0x1820003010380308a0035800b18050030400ca4000811058042c0d268200c0c8071402802da038894115a01d85029041403044040b034401150080710240049942403140380a550f0604c900394803401754404910800360900510380c48a4070305659402c0c80e40d464900f0781e000c0c9042d81c0503190350b52607460690b4044c002801000f1181e8a0000039140c2011502d00211402d840301e0074015651030003c1c2c00320803c2141d82c3e108502c1200390801d1580705018007005194040e08040c040c6999510072840b8ac3c10038020310340c8282c00900c0c8809951803111041d03205140050061a403501c81f110180c0300d00f500500040d04501400300d41001290090050085031804440001904d45c5494002400d260041e006035041200000b86540540d4000640340e400c810126251640d0b44818000107183e2200c3c039000612010f0020100002c0c048404560b0401c00c8194a041c0b044451004040ba12050115105000b0880d1040480000e51107101840d00d080d091341080c5100c10b864034141451034100d54400c0b19403a4040c = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 464843201 1250 464841951 464841967
    0x2070801180b130302150603100603050105090105010618050114070816030216140609010306080d020304240c06090302070f03110a091512020a0b0417010e070819020406051005 77
    0x100c84150b2083d842840200584101d903030017074a801d04003c1c015285c84220340806e119507400d01c820300b040c0c20b80c903604110306a41c82c9005806450115034207540d6501e00000050b106001e0352010004d80100c4010344800c504140040da604100031096441c1e44000748018000101c00400510116841460b00158030740e41e071a009140400e0621456801c0c140c101c010030041c86906000d03202c2031401c41c4c041c1d03110712103200102c00811160388030759214071400031142203076038000c0024420350350b18080f0442d42c120608525201c420740c1b1008100001e007004a104080303085075000c0c14400d44244113852600d5501c0242c4541d04956810031303150044403113850203462078800310b6000100982c00f810700080c0500740700071820390090b100351004641500c04a0085558261501001d090003003e002e0f100e46d10342d403244079000852404a109586402002514450001225021654400c0003403441c0d1000e803c081102103030b9a10704a802507220b201c08100c82d44e40c90b13280c82d60f6034820f5592503107403500 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 464844451 1250 464843201 464843213
    0x60a1b021e030d0f171b0310140102011401030f06110414040e06131506082a011e050d0f050c0307120603080324310203011d070207080118 61
    0x21030402c0e402880018101e0030380f1325410074050b0440c003c10000c01380c1180c1d01c218106a01c90116420007a40802c00020030502c003a4011003403044e18020411a80c2040a80e4016402c88401e40e401c0c2416181d100c004000290106240004031446698082088000b40f507060101e40c000b0b4000c1501d0b82c0c007419034200c1c182014808c4400c090030480080005040c06141c4042c21107095001900647c5410036001c5c1e655640c0e0041e80041c4441c104681c40460144400d519445403000f0040d404c3c1605400803010750b01c580b981800480782244500080d6043e08410382d015441070500002075611039003044010f001c1803044500c22002401c499960f0f02e8083d074000c1c0306004034200941c8041c80c1000a0004c1201a425641d100c00c03200042078911154242d01a16080600f40c469480b0f0b44c007041054640041d51000c091070208040c000420031000303400d01c0140d010074003a2104040302d014000c42c24084150010390006105e0041e5058030f601c50100d0f07820749020342a400703e8403031941000e1003000300f = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 464845701 1250 464844451 464844463
    0x110708030d11070816080c0f070f091401050105030a0906020408210f03060f0105090904050c0a08280201170106080912030402060304030305180d0207180605060a1b021e03 75
    0x48240c009502c0c003925699800f103903004000d160035115004058130f204004602e01240d007d80c6c003000c1190300140c0544282e07940c03008240509500411840303000644207406e801509010101d80c0e010580b240c0c01c1100444131a000180142c0c0d1454550b91950080303681807000b0b1014000000240c4201e98244405100000103030f0800f5407180d404120b5103000c20000d00959801000031540143c001d9108070040347c2902504101641c040c04c1401484104100000c03490500300043d64050900d0745e40b00c01103500e500d1600c1100e2101d281d09015840007007402c01e803400c1000d01c14141000302c102088170000412000f60021004541d80c0e03130a0100000040140d403078030f07039927058501e407135450650b01065035404007410003400d0644620103d4034081c611440840368090748400c071404002441030080d50b900d0300c0d2040c2140030a402419015800060050905450740508002d1030181681c0e021600d5020400107003440c541c100b8140401680e403444a04420b1058189070702130f134003e00040608002d = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 464846951 1250 464845701 464845721
    0x506060904061e1203020304150c0b0f04030f1b11031509070609090b100302092d010809010504020d020d170f0c01050601030b1315121a2d0601110708030d 68
    0x425a04c0c0c65000258004101c2d003c1c1c51000103c0750049603c5081600c004005101c000e00c204980380801c000d40c0d40c0c50f6202032240b030083d6900001c0352000750f0b09588142c00004c0e003074112000c00550401150a5024211102c00090111110821000c46a0288e01801e45035500160000d500c10002e007584003e02d84058410b00c10101b010f1200080010349104007600c01001341500890180b000350307074101c2c02054540c02440c2089084612544039006200030741e14080c01f0400300f00c0850841e203014030403a4410395018200441c0c0f003103aa02003003c40d41480208035000c0e003080c95902141103071000a030202c1d52080f10718603241c800704840030b07081d588000e0403903041611b2300c0c450704812359440f40441d07003140511500103200404d402c0f0307821284d403c5c0d80000001524456401f010080c041080703c40421010210260640f00c44007150152101704080c4143c690209024508615055030125009001414408a0104e070004000e0a103400b65000c03418030303000403456400401003801100020 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 464848201 1250 464846951 464846969
    0x16030906050f0d050c0c06190e1c0c0c0f060905090708090a02040c020c0a0b03010509010f030305070813050d05060a0e07120605071713020103140f0a0506060904061e 73
    0x20b1041698000c0030301501e00288201915400894421134800040ba20302e000342d0b0003039528070314088901600300c101410701844041e1400c41c44040c00600401c1c43c91500314031540c0d80301900c0940d5002c844580280106072540000d0700d00c00620a44058500801400345c0d88a503115580b40030108004014010815014422448108500d034100806c0d00b602da203a0480300060340300d506040481ca00240d001d07586800400300d00c0c01080031250500a981250400ca800340056a00d4410a00850b9510b02c001000701c1d100f0b000c103400042442c0003500316140d07240f071880b149503541d1000400b00740220000341c640d60031801c28405002c2e0140503058815035444000d0401500d0320350a803201812480001e40340365621801300e4a071a2190000074403000c2ca0504a0040c0c0c1860000b8822a10043d0000c82c01300f0301d0101c83c8202120f81e08601c40c40385000c0c4030482e14642d01c4199102c00342800030f01c01940a5001c1012009030303500c920a2002900d400602d1108100d0318094020030b1701c2c02b07900880303d2 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 464849451 1250 464848201 464848207
    0x603050705031e180709050402030f010903051815030a05060a0501031b180807030321090f0803070e06030c040303170f071b15021809060f010c05030d021603090605 72
    0x5910440400e410011124011412950b44d44404021903c0311068422941d801854000140e1206542213140528001c40079580c41d000c0d00308065080382c081d04001004504140002c1c1c0444088d07100c000000240a01810b0b040a24500c840c41076901c01c44c2c0e0401e655a44405000c1c0c5402c3c200c0401e4041c240a003401c0000030082101403619030f4010956900700700900e03160003890650040704500500c100c0d0221000c0c15228603024081c0b0354400c0640c11062401c0d4404055140076010f204078041c2c100c40e107244c884541d515241065403009280c2801d01c030803018002c007030382c0350507000b148203002c07440c88291141d04500d00108800e032074000198041c80c0304014010402181c056064100049003052920001c0340c14142c40028507803000648050900261800904040d40050484100c001240800300c1903060030802d8600702a10400c1c4c101000170b0032103042c0e500400c1e4044941d40190200c07410f0000100c441c50903644034110441503058a0030481040541191086014004505243d41 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 464850701 1250 464849451 464849461
    0x50313141503011e05030a080306030d050414040c17010303120b03010b030618070b0f1801031506030e12133b04080706020a1107120305031b04080a0c060305070503 72
    0x98030707000c1806102074854507102d9860200d10313641d4040c0b0060401a0030f0b10500c40141c28170407440d400480d40b0310f0080c0958590044110702c91011241590851010503030480c060b0820b1000804480483c01e090000300c0845601d0406020b10050086200b940c1c1c0c1042c00c2034843c4001c064840b080410b40c060703810855030141c0399030701040055020580304e000c0c13048601d103215514980503069001c1d609070b0100140700d1545c085044000c020001e080814a0034110544004500325280b140e16500f900c545820b06110040c40b81d08064010303807050045812080e940c0c3e00840c640c4d0302c482c0c60061042c1d5800400c01c40240b0019840303200c2c140c1c02c002103800f02c0444104108003160310f10460003603e1204001400c02c0080e00c2541e0080c0d07080358045448560212024050545510403d003103403269100c006000110822640000303581542c60500b180c03a421401064445500d007520070054085c000800e60420800c006103900340960310b0040380d1841d0040260454001a080c00d08101c82041004 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 464851951 1250 464850701 464850739
    0x1b0203090d06050a060b0a030f060e2802040f0803070615060912020102031204050a060515150f0702040c0804120810060806010e280f030b0f0703020705031314 70
    0x21401e41c2010000ca02507031504005001042c403034008a544603c04640c0b030380030a500d5403121008031880002000307980d031108022840201d0440b8507040100440c61594040200c070a0340c2140304078100805402c040d1a19010304500f4801d8100c940aa440820b240c01485228090f60b011040440c0d40803400b00d0400d08020315082442c00781e00c91080044403010216407007082112010702c40c8080305602c60500340f51041c0c450300b500ba002e440450500d40440c00c02400f02c0541888601c0040042c02001c4105d192140b060700038003950303019294140011005038441e4001c901c1d102030180d8940380c0a142624050310740043d03001d20a020009400200500c600124007440c0c25103040c2c0c28480c82035503031400101c2d84400000c80c0030382c0140140f0b1501c4180c15031941264030102c2c03480d510001d5036480b16400c0c0e880b52031034400031f40103980180218011000d10310019402c13850718a0f0140c5469101c0c0c03620340c6154003051520f0b071100c10780c0808114091800c550003690010403190700c48183e10b111408 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 464853201 1250 464851951 464851969
    0x41010e06060703051c0e010e120901120603020306010b03160f0c0b0a02070f2607020603010e18010903050a0f020c0d02090612010f0204030b13053d1b020309 69
    0x218081c00d000914001414020000e841410712200e841064070345a20b045480078081200c4440425824551888071031007001c0742041c4031800104c850360815900400464401a89040c18a031040c1d603800040096103051001038081c0816181581e0b40b0704120111190025a0720707032003410040d400c0901692207078860312415000b40c000042a0041e241c10080c0002031040d544024100805103504ad400c0040802c2c0d2000304242c0102c00400c02c00861180400500c07400d00001d5019104000511210f05080c0300e031600b1002c1070020768544840103200508483c64a8016400f0500200d00540c0b050344c81b0f142c0d41030404003440907014095810001c5111262841c00080c8906911000680d06403a00d0051850040070a4001e1140c0076070824100000d501600003a60000200c0d00003582c10014516894451603105000740325802d85418120f00b448040340102c4415006840c02d045142c002c04c60f10032040f20340c81c01c00103031003004074910b003a8030020710546025500140314400c0c5640c2c0304812 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 464854451 1250 464853201 464853211
    0x1d1f090e0f0c03190e070609080d080f09010e030a0306090615021c022a0415180506060d0c1d040c091e080d08010e010504090807110441010e 62
    0x3440d499031510130740d4245814a190212440a02d0212014040c9400242c11005c840395a20741420490716003000c65210050b0702041d2002c41d95403404210080900e400b01548100343e1000054030000381c01807903007143e21400b07a0b800000d880d001d05001c282840e12500c8010600000c0314001c04807003a0000c0e4440699a60103040e180c18480410031050003805003001700c1130807608109807030001140e40141e4201010f1000d01451130403042500f90480c4501102c2030f280352140b0340706010085041c14001e404d000f8030782d80c0c000c4014031012203980014011a01e5000c900d44075401c018044481d0701c44240e0382c03540e04034860740c2014403607006603070401081d03c20b840b400d5011400006004283e540454200d50140e441c0b4414101188982c5a0084485041e0b481e8540e50b86050390362070080006030391072800050480e85042014000003840f8001e8000c150101510200c0c401c0100904e0884c150030100720390014105030140b2031407030301c1c01a00c1c050403142d400032032444550410707910040c8440000c003 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 464855701 1250 464854451 464854471
    0x625020718020c1204090e01060e04051905030702090a061401030b061801051204141b03060a09030c0b16032703080402120607120614030d1d1f090e0f 66
    0x16107110f2169051061114003a01100c400f641d865681c05105e00414100c1c0701800036520f0118045034003c102074080d40110303041001400d40c40c440034010040d0010000d0102d0311071008100c141c0c0180c070f5020504e44110b400820000d086803510f01983c0e4016500c01c1143d0425140248942c01d0b80d0754403050f6414101c0d0759455103034569004005880ba88180c400400c001030282c01040204100c200700e4680d45071608090f180c032010070101342400d40440071101c0d60b040d04080e00107a10071a10360702581c9214024a400c07540000580c9441c502000b0550351802045c844903003886030150140038080740c1c40780d0003a40300c50b124501c207890300c29440608401001c0021034000309066640e0744c1240d443c0c1c04034520694180d030500a04c0504081150802c540b40c5500700040007030301100d01d9a41070344080c406000b0340a03400030420200c84c0d1281c680000842151213030300741c08491312507900302120400302c3c4c49001e0350301080b444080d1007503039980e01071003840541804201d50840aa4003440e0064a03202d = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 464856951 1250 464855701 464855707
    0x503010b15090301140c0309070605070308010605030615070309081603020603010e04023c06031e040303020d0908090a05031609020f3a0204050312090402040503062502071802 77
    0x2e00040e000d4003901c21810401c0509000340803c8080e0070001703500408a04c800caa01039503071a00251218020054044e000c1a200700c010810785015500031035000340002d005807999120540740d1401343c1c009840940c0006c40e04c0d0000d0183c1c413401c110b0f06100030a0b0464100031a89184c0c005221403105015400b00814040041411500d80d03000c2c0c280240b204e42c1c540c0ea40d0401c07809544004801e0203001602c2c110081c0c18508690034803004903070103400520b8008802000c80740500526140290088042580c00c10601940000768420320441510640d5803070f0381c0b1000c44040086100040d0803c1e4865040b034100050100c070100c900700101d0b540524090b0300d03440c51480d00c90440c09142d54038080402511043c0c080e40410702c0801041406005141c84050125601001203004c1c07405195059449a000d461401c40441c014010641c1c0083c009854507484401180c148035003074a00c4c0c080703c0303125001045c500d941d002009121040501c0140301c3c00385804040741c1a00400c1c04402c0780c00d5400 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 464858201 1250 464856951 464856967
    0x80c0d020f2206051009030221010204140a0b0f040608130c060302030103020405091501060c140d05040501110d0c030c06090209010b090a093b060a0c090503010b15 72
    0x200a0140781540140030300076410300c0054041503030300e00c824410700c4540b41c2100031403546041402c807080b00815980390036101d0708682c21b120120b040d446920441d2510102c0c626910042400140062306021903202007062404050000902d82904030340d08140b000d1110540700700e46201900e00b01c0b0003600d003200080c1c442600d2000c09001d000c4c80600444100d501c0412040d4154004504980c800d4030100510366034600d455807118440990b002400074824010003466101b4601d82d05d941d402080383c0654031a010140510701041d0550fa04003080000c1782c10880d643e00709040003d0184c1d11401b030034401005120003404295070070300017000d00c40c6c15403060051051a9000c013401660107014401c1550715810721111f142c0009948038816191040003042c010424040c6817018038203401186480b0390481162902c401840340c200c01c07204240b04400200081c1000f2050148130701c150700048040d0b4806e0700415240c460781186009a05158030742016458111140110101088880e80c40f1020 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 464859451 1250 464858201 464858209
    0xf0b0c0c0102070503030f060105030402030a15020f0d090b060108090601051314090618070509040b04050f070f08010f0c050a0c1403071a0106110a0305030603120712020d0306080c0d02 81
    0x14999060210758404241a001c011300000114012181107803403159950341c0030011229840103c60007505a0010000b00002400c03c0c40c1150101500e00805410114004a44000340c3c11108081000d83c1e2220105803c0c80702080030140c000f1820320b002803040c50840d00944c4d03140810320585000c1d07055004c0c5a003210050b640020b01442e5a4201040103003446179020340d88400580c0e20b4440c001e80d1000400c000000028044120354028007e0a8190350782c0d1104008034000400035101e600545198102d8603009011200161500010603026a402c0c0070175542100c0007500e00030f03401407600900e086429009070a44038941064035201c0190130040c0b50400c008151050280c2d414031000c11290300700004008140905045c80001c007181c0e0381d03200070031038148c10443c3c04c041c0d40350400c003c0f44010a210300011588140d018085455512001000340c031158403403c402e40b4161051f02d04280101c5d03051111040c42e12603450103224039403c0546c0107407500784450700188101c180202200464035 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 464860701 1250 464859451 464859457
    0xc0803010e1f0b030f0601021b010309060608030708071703060109050d05011b03020d11030c040302060c070302090106120c090f1211030d050436110706050403180501020a0f0b0c 78
    0x41c40202000b0a01da444a4440c2d80340c000b41c40e10000003039144000b031440d520018000c603030340c10800c0710702c40700740c250b203005500070003440c0c009640d029203458000c030b4040d504000400040d0f2103104041e41e10300c443e040c09103165281482c0d1a1140303004009001050703900200070303810f440b421200d203e60541c161030264010140d03100300d40342080707002c0320300b600080c0c156004d03012603190381c40c083c0404902030b100100540300495151795103c13170500060025062890180215002c00b0045403030b002c0c2c5940015003130031403d82c0810001807907141400c001c0c980c14050309800b052982811021503007402e4034940c860006000b00000c0132000707030b00d0005111280b8403410701202c0103810b0317801134080040f0082c07056020f40100d80203409000346819086051b050090300c3c00c100410310707415003100c400714900944203060011003212818804900455058864940941c1c070a464000c483c0120359a21181e24506c1e6101605640003461948041044004050380c9598008500700321640c40b040403840d180 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 464861951 1250 464860701 464860741
    0x9041202010b0405010e070e0109032a091104140d0302070303260c0c01060b0307052d0d050103120201020f030412110609061510050d051005130218010c0803010e 71
    0x1400c0c4400042d06e038520580090041c80c141e03503114200030307114005582c030414910006100c0e05d0720803c0c02c0303084410030082c0f010034440031605400c4035594007146401c2e54118040b40745e41090028081140d1400007180502d401c4082e11100080135290f14081d4841c041880054140a80c0f4140f210040c45411040440002b030340195042d9401c100000c14501d0300070403022150740d0319041010817415000004d503841014143e58880c0380c42c00700e60405181c02411420550382ca1000c0007041100c20100d805822019048800080d566145041031540035401520344001c0d6441040700b608021a0034040702d5125411103104102400c090f4805c6844a0441041010700c1c082c100501c0525500484d83c3c80c0100c250034199400c0320340b01810000c010081000300710200b2020001100e2044442d00803591150305030044900c1703030303940d1404035040c2c00880c00c110000b00d500140c0058072859400e0040000c540038a0b1807071f0303071454035a41c1d51203611041c050502042160800241042c80e03199000280c4 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 464863201 1250 464861951 464861959
    0x13050706020c0a2c07030f230c0304051b1801081006050a0506040306020c1018260703030f0b040c0e04050a090804050909071211030609060603100e070302060a0e090f040209041202010b 81
    0x8c903503011089a0080d42000c0b65600111b1001d002c035404203c0e1a059030301464104001e80600c040760398560705141e00d46d04007190010308110214007440f21802c0c00600070f008100c0a4501210b44050880403584c035031300010300c9445d80d043c00b440252100300c1502e0030342e41c1c0500010f0f81d131190150303164501501d580762041e0450805d0a04034180041815019032148140016a00c3c0b4540c042092444612410851030003e0103000c941c1c0071a200b60010a002110907400003201d4031340c2000704041c0e131441c412000c0442c0550303403040110f040070701c0307020340c45072480400f08130040c80c1d9230360301415115503c5624440c16028010a00c00311060001d50002c0010700512a426402d51808066000485166030f1083c081d040000300461030209030944078010050180c521081d21100050080210785012280344c81860b03404030068480e1402032440f00116200c0701e007003006000c10000001401030100b24001e01100902c0016100c01c95116005a440744005242d044c44070b0007240100702d40303041d050b80 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 464864451 1250 464863201 464863211
    0x6010605030c130b130302130605030c010f230901111605010507080c10150e09060c0a0201140a0e060106020a050d050307210e0c0102010e070e13050706020c0a2c07030f 74
    0x44445c00303030520b080342d10948083c51261080b100c00d500300c614510441d87c264100160685480d03204a84251102485040c40c5106002d040c2d507444050054444420855100103200c00f0301c1c3d83c0190f030200801c07146c000140010041014001000110b5204880c180318010400c101082108800e803201091400308580c01c002100544c2000341c89070140454550f0034030301001c10180c42c80c201c124805d01d00c0b40002c3c0803544603002c030302090b42c0c40140650119542d800c1581540513810118034040c0c81545800300b000303407103a4031450811006038003002c255803118495a000800110300b8070700608460500c651a0f41d030300d85050321250728601030891044030b1681a11017110243d444440c250749800300316814600d210b0016400c036000080700700b0081c2c0c8407040800400c07280032281c5a10006005404240c030f0000c0d40c603949440e01c03035006540560441c1010112906007110035200501000c1d03003070072000a910183d1840102009442810300c01c20341300080030740d40250040c507203a50048400b009 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 464865701 1250 464864451 464864467
    0xf030a050a0f0209060a0e27040c05010f170411040c2006060109090e0a21020c061e0a0e0307080a05060c0f0f03041509060c1106010605030c130b 64
    0x100a04088030341d0041c19180441d580745248051080e1641014080d00181c90860132050070350344103200046141c0e1007214602511510f040280c84105032486000c0e0480490825241c00030300240c00b50003140c10442147e2411a44541c010540d900810031034281560580351402c2124010b420607015a40140c2055810b482d134592013440c1401440c0c41c000d04403c044185a1a0341c0c9034203041c1c440c1400140d101302c003403000b8825584402c600e418141c0c1290740c2c1701d00a54985820410000c032450342c01c5682d00d40160a02c3d0103000aa04d101c10803a03040c1d00d8039405c9403101c012030400c0081e40445003000304413039185074003c071200c280c0540c2c01001c581c4126a0790042a54039002d009044405000715008201a15071a40a6400701c403001c548407428039010700340000460700001e01c1600c140a01702c0d43c162010711a0720030000c82900485020071140b0410300084d1920100e090b22259030b0f449180100105a072200589400c544011a00da54403d03145507002c2005940d50801e03810240c0020b0550 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 464866951 1250 464865701 464865721
    0x150c032a070204140a0c11030316050c2b030c140309011e1505090c090607021503010803030f0612060a0e0f1f0501051903030e0d050303070c0605060a050102120304080f03 75
    0x4c0d00c118040340b01031110101000c3c04503181c50065400d0400c2d40d10610208001d0300d000002e00d00c002c0980d10700103041a60700003085103450344048958020f2808c04122000c1d892440070b11024691660905011502030904018070020403100c1d880000000800800c4c0c20700c0c401e4100382c03480001c1501130b40012a00084000052080720802c980c2c440c1104000642c1d81840030b0110b00c0b62044400e0b986c18100e41c8024000304d41c0c01000304aa120b03200c01d41e004194003240000d0742c040c00c4500001e5483e0324000c03100003404100640f4592160841c9d4a0014000c01c000032a9584490742c040c0111784000c0d5050f0162410840c91900c00f101d000740c4810503203002c1165900d602604152a040c01141d03a24018486003a07000e00c13078210443d41c2c1000500c0413134024043c166070890050141c4405044584805045030030594000000030240301c0b841052280c40e010703154005104031101300189242c440040d60b118000d00b100d46440c200031000030140001030301660445010720f50b41ca5a2403501c11605 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 464868201 1250 464866951 464866991
    0xa0c23010c08070215010308070c0e160f030218040e030409020c0a050615090a0c02070902070303202d0f1308062401120603060e150c032a070204 64
    0x190740020b6801c0d002640152002416070802901068070304156401c54a03802d806134071042064840e151402d20028031704100d00c80140c494828103605072418090702100800102d2441c115508042c01408140083c034802907003130306500000c90300050301a040e01c000c0c43c110b000d640d000c54141880030071444030018010584900030b5100d0401d8410340d56640e542480d100740341d5815507401c0b8003000c0c002000041c4680c002002040580112000980c0c2d5414001c00d0368000982180040d440f54954810354011102862030105101640340c20b0407030158400d601045505100f44000412814505003c0c82e008101c41b40e1246c50703030015549580b005607004140741325204180151054500203040e0140c181145c4d014002120000c014091440d001110f2094056505619069640d140003002802030300c5554078003907071030001c1c1c03140c2140d03c010070f044400c3c002e20b0b140000100f001000b5078403612129011041048810000c54445a5180c848250042d0702c0002d410600c6c0c141d01985070314140701e40c = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 464869451 1250 464868201 464868221
    0x7030204080f060c031303030e030304060c030e0c220209040f0506121b040902030c041d0d0c0c0b0318030c060f060d170306150d0603110108010b0a0c2301 68
    0x1c490588190600b8240c0e103110466052565200c00c0c000700c1d11035280c0001200080c6d00916010400010314646507085138000d840c22116180d450205030342841c2c041c020340e4002070040300a0684000000007003800b0000d0110314902400310801034100740c90850b4155a10f0344800b0740f08000c1c901140d02404010041914100d12a956032800406040e40008009043c404030842d00c11003490000d0601003e4581c001d0201e9140c0200e44003140c0d00c3d1154450054075003004103580301c0720b00420034107030701300742e0a04032503402c101c2102c0d00f241c003040d851a50a02192850300c4a01e0b5240c0d207020000341c201d220b460b202c80780e9001c0000c0c08803058000113040340c09100000080c42c8586c03100700411203c11414038000b0040c0d50003002c04043c018101c4041d603030040000d03105643c0c0030f001c00100109948080390201006a82d18821710500915001c840301e016001e0074058019414100180c00500403480c0f00c0c010090904400000c0260700a5140d81100368240480008441c14007864081e00754101d03 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 464870701 1250 464869451 464869453
    0x1020a020111130e070c1a01090c0e060316091208040305060f060d060506030f070806101706011505040e0a0f0f0b0105040909020303090d15061a0a0c020301060e0703020408 76
    0x342c20440101031804541d4140300404118000034640300e103031040d0410080c02070040c04100704000000c80c18400c0c07500c240340f402c500d4103140c0d9810440154225406c40307450f0007c12052a150386059156102241e420180312241c24480102e2110211100c49150f046403500300c0ca082081400c01c0140c00203041941e00c01d805486046e035030760240515201301203071920340c040700301d00e100c00c00326020394403c9800c20005010707181205101d001661800f05603601899003644144104407103044482d000134080c281070144840010545045191790b0941801408041480c4900980c0a9409801114024054080411346074908451000002e040000000080714181601342000d6011485804086101612407608150a044d4001c00915200130126010303c42004003407000d5590303952014419100e40d0380d080304907a503224a101550303d207500030700c0e0500c071681060000c50044000d464010840b4544090318039407070300009000d420554001c004030900c080500000f00e0f8960000c0040c0c8007024 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 464871951 1250 464870701 464870711
    0xf07050c01140a110a0c080d021c020a031409040515030606040606050a120e0102030a0506031006060207031403071b2c0601050f0706020c161212081801020c01020a0201 74
    0x35005460390070054000810705a410459050458040e12442c402c8207943c0080f03900d40c980943d19402028207640103802d00b035024060000460303604122011148a07202c0d04800302e64241d680103036907052599001010b0021018644903940d6096068665a500c0100140154100402d5100b081080464807074040d010740c10014140781001d001e50070840352941e172141d140810b903940c00c483c0e00380c00403d40c4010f641c0301c01706140c0310b0000b40041d41c0604d070020710019403828400100b510b0301188021011081c0d040c21010000e075900405c00c40c0840382c1080f010208a2507001c0309038218482d9510050203540c001450803184900060002c007903885502c84064054001015082000300c2c610f020340c1d0168240000030005d51040c8050458514040b1600c2c4c00c0521607504c80c0280c0e040f580790040c1c81d81c00100801e0100080c030701d00c01e000b07048a08046110080b141c60744003032400301803880c1040c005032030046201c1c4080c0c078a100b04070b541898000c6444584060a5601135840005c0c3c0744015800c0c1 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 464873201 1250 464871951 464871973
    0x1210501060818100f0209030f0c01020c1813020105270f01020a080f1806040b09010806060702010f08040c1203090f0b0307020604141002030c03040b0c03011802130302060f0705 78
    0x502600302525030410040136140054040b00015009100c00e40c0304040d004d20010340c0c6510100000c07881d07110264080c0050b0605000024a4071102d44c5900303204481c1e11480a02e103010705200b96400003000400c01c0ea001d017080c001a992840303011580040124243d045426561203200e007040380410403135020164800300d100483c0d40e400d5a0501030f0041e44200089001c1c8900c40000b00f4072500c150106207540004100091100e070000e900c4a40300040004000a4030340c0c0c400e48140d8803c60446039a81400d803d130300000c20001343c50800c4824003134001c0100e42800b800b0326080c801010400b4502c1080c282c6e6140081802d00301d07115846042c281c049001c5800744922007030324400c03260b9a00401d0f29640f2610343c40c02803446002210524019203501043c141c2d001d000452081c905805500e640e0700301441c1040003140001e01d020003013170040c4014403940c95815000810300800000150300d4074400d4484114003840d581c00250301240000c3da0110756442ca00c00781100a0003a03042d01c45161030 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 464874451 1250 464873201 464873221
    0x109030b0c09130e0d0c05120f0307020c04060b0d180212031e07121215060504050f0306220c0e04060b1c03090b2110080708011406040b012105010608 66
    0x201e51044c410302c0c2c2009003003120840c8500d0501e042c41d402441122040010881089001d502000b1030300c0c0f64140001c100102e841e01000b40000d10b103025641081454603183c8554042d0041c02d1480b2100c0761110044445180000070b205030f465001020b031030401c00034001803950f907030000c540180030660030030021000d00c1003281900c5070150440e141d007000703408080003120100f5204101c01d16060b0f0b20030243c0300208062015001615040d1500d03541c99082c101040313429916840728600c00d92103001001040303180d618443e180280f03283c1d011a41c43d241481c00012660304c1b0f4005220030304c4800700300802d000c250b4000c201c0303903075050381c0161010301103000d01c0c10102e00c80c11010380864025007082250361180b400030801c2e0440070b1011080e04252420200491205a6031214141000c1c0018403c81d602400a0401808140002c02040d4404809103030320b010010000f43c407841c1c1c0c2c0c0315480141c0c0d00a01003c2084942d91518410080940484500a000a0055070001400c3c01d00050549003 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 464875701 1250 464874451 464874461
    0x303020d0f0c030621110625030e0a23010e06070f1104050f1303120209040507090503160806010b0c031c02031f120212071d0108160506180109030b0c0913 68
    0x86c01c09480304480d0400c00c18000b0960107902c04103c1c1918000035003c00004025100808620075510042198039074010003000d08490340218030b090f4540200e071a010184200000070050003800e084106c0c6025600282c22405000009028010007140250400c400028800240d0724104c4041210341c440088041d1a50307030450f442c4100403070250001d400f181c05520b50b40c003081980280540361010640100741910003c0e610700d0089941040103118610341440310141c2e03030140007815881e551429010320b40c1c0e014180f20300c250081e00014413401c47c08007841219003401c00b00c02c490f04412481c402c800c0003503004885820f150042c01d04042c030300240303006220080300c00c48402545195950b03002c004403054245c030003685a1084800c00203e0032400b40c07001c00c2540240503145501c0d0f14000445041200c2c140001c41a4110f01405120a5030b0b20000d51369000c2003005402c140342080801603840440d560005402c02e8100000c100107840004014807a0403416206940085c10001031441139403 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 464876951 1250 464875701 464875703
    0x15180606050a0810091803020c03030313020d061d0f0706020312040305180a1d060d0507060c0812040c1401030c231902030309280303020d0f0c030621 66
    0x4608000080c44244101190344d0420002c0302d400a446a0740c00308001218248039684416403c90440300c0149501480700282e8501d05501070351462a02c070b0010696580c0f84940284945680440407041c44150703070240c48031404051000607901c0000116036075407440c2d1900d203900c0784200c0d8408510a80b012040d40c01c010300f0070502c4441c0da2502c4c1d40580d0590006190050b9903044401006600d946600103d40100ba0300366500007008403250044aa9400c0100012701803412000c00c000000d0000a00310211a0985410f020031140f6141c43d10760340c410080401d507040014020707c0144201c82c80d00e1021151011800e5640f2406100150b003510008a4140301086050f02c550310440f003961810305500c520306404501c2e00501806520544003446902d000690000c0204040c1c02c1d01007204101007030055241c1103030101ca09a4111034406040401800c06402007011221190b039600030702c00104a02c1401d0100ca00b0655006008150500c6000103100c00d0700e811480c181070f9210170710801 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 464878201 1250 464876951 464876957
    0x504060e0603040203251e0302030a020108070c12170106180b0a090302041817040e060409170c0d030506010e01020a3801150503070c0311030d15180606 67
    0x100103240030800709401c0200240d0b010b00401c980d1054078540348248000c14103030080c0c20ba16540c1007a41c803a00c0b940c1a1404650302c1c6c040d0480520260f640010a9040705509103008060b5a0b1a0582144c40514100e4010036580320741c50b120050319004540c00501080001c1100351980c0c1c0c80404a4004092600159603641e201c00d007801320440460083c0451807542c109000b035070f6500d0340840c0c2114200d080014140a46070840001c001e80e4502036482901d5a02000e4141410003142203942c51002d88139620070303561945018200200d01030801c10f041d035688962a10f42c01c0008102da1039240d01080c51000070314000016a0560141c0f05507645500d06034000c181c4844190390b12406104072285607080307099800300c0c80312049028a03042c440c3c1e10501d81c0030311040d45401960020071010725015002e01c007041c400c111000340c0c002d07441e820164040c6400362107601c440242c0740c00c620074071054203865410700607a002c000b1400c00914046411080040a005891111b400103c9542d1b008031000 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 464879451 1250 464878201 464878217
    0x18080d05061e0f0102010e0d0302040518100b1e0703020109030e0102010c02070608040c05030a030c061104050d110a090f0603110f060a0810081b131a21010903020a0210050406 77
    0xa030603c03405640c10031406000001c0c59446c002111803038242001c04960000f45c00040500c1941024041002e0010443e5100c000d80c0c1820f00c900e840d410490f0281241501d00400c15040001d40c0d880700c5000485002e00c41a0768807442c0c14020b01800b20940d0a5010030f0b1000640701e00e9510510a43c0e04030515a03020b01001c41c00c03d90202c4004501800544d281071004401040c1e640e001d110254809100b501c515401045a01d000f00030764100120060450400744410019500c0e00d1285904503a0712403008242c4051510004a007c022070f008004464501380340c107400180710707611031b03002d903400740350f0f0840e014400408016441031507400458029409103c080080d5018107202608134010300f8205d030029031280034061a0641050403011000c0c1404035400081c01e040054104002c0e0700c040a000c0344c800c1080c8034504181d0f600c812402041b440c40c14400304520304680e0704180c48008000e00295109080c000d5030392806400603480740401d00d44240c840d5010b50220b900300e60710381d160f07844 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 464880701 1250 464879451 464879509
    0xf070905010f05040e16090b03161103160318092306031504051c0302090109060f05040b210f040c050d080910080108010e07032418080d0506 62
    0x1a61880040c2d01c01c00388041032101103440303d1140303850f611418500c0d418101019a103100108090b43c0c81c0d11520402c2820400d0090030b42da07020110050b4901c5042ca144000c1ea010052403851040d05013003c0a01c81c040b40d900c0400d43c0c01808014808181c041ca58001c0b6201d903891404c4581071001c1401d9440c5a1aa080d2a500c0d00002d2701d41c0103a00406840d0104040d00450360003000494040b02d01e83c03c40c03200c40808151032a110a6141c4403407074210f0405a003400042c0800c1d6050141701e060041070004d1003205071184003200c000e05000c1c0640390b1615002c4a0300313003141e4000040e26040610060005410030300482c10075202c2c94000003008c00c4a4131300310501546d103208403415108081c00708003514294a034110480034a8603d036890302010740c9000d200350700b181d940f22405031580e041a9020004111032580840c07102c0018140303001c1148003614400c0041c110003e810f203018102c2039040c5d0610042c0c0d0040c0c910510010780600840c0c4d600320400034440110408070b10750b40000f810561b = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 464881951 1250 464880701 464880707
    0x513060e061219030c0507060e060304061e1509110f2205040216020406080c0a0e0c220603060905040804091a060c07060207080106150c03170f06090f07090501 70
    0x10045008032054448803803d600c4040d4240c240390702d080d4040f84580d5002e00400004010b080018a40e914001c03d98040480010b1140c5c0b00241015041c0c588a1000340e0380c440c09071003400f43e401d003090000c024110503098000c04600ba94800c500603c0c0c680390100854147d20740803261300180e145200392600c0d4200b4074240d00c006241107003d48010030302001141589407880248141e142886030000840038902c10013040d2007003604500070710f401c070b42c01203410f9465007e104802d840c60070030031032078665401c0d1004c2018000c0c40c42022054010202181c0c203010207207104030646a15a800380032258890700745600703035101070324000e00c004420041000503404a40c80040d52141b084151180041d08400041264020242d216040d400c240c404020858041046a0060018030005e200e1585000b205400071640d4000314001d1003400340c00e0700100762203101d04100350001110300c1c0c40107040040100310031180440f0000d000e52140c41c0851002c60b5420042d1b4490080ca558100200341004011 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 464883201 1250 464881951 464881969
    0x122a031209120b0621060a09020f03031605060907050607080901020c150d0606031e0c0c24050c070c0b0f0d020f07020301051e0c03071214010513060e06 67
    0x102082042420740407615100c141d50700c030001400b60202d80d4550038000100103000051401e28400000c0c0004012581200440d40c903034440307000140090004118000304002c2d0b404280b241d58103000003e404003140202c0350040d24007a00032800c488040e41d810351450380e10b00840c01340650008081c824080044c4005c1c0040100010602c165220711250802049000b0b22100404240003800b180d0315080705001e200d0040245002c1c50f00340030715220101c2100030403022201d00c0c0038280e2500c3c01c1180c80350190700c40031102c991151020410454100102120301401d401c82c03204c1030b0602020555040c014000d40701e207103410540e4000d0003490180c041c505588841d001c0301f02c1c034505010440482049202a248401c200c2d81c0803961801d10384105400c40d00d00800303c4051344607040881001d0b07503d00070000c0c1d000303018510309984ca4582803000c0c0c0f150400705200010700360034102440c900c044d40c122041c1c100c40c82681c42c607800c81c0d48404424280d0b0174501440b100d942d810800140c00c4e152980074 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 464884451 1250 464883201 464883233
    0x408030415110c1015060905131d030a08070c05030307030f110a081b0301031a07020109060216020117010b0d05060d020a080d1707080f07090f122a03 66
    0x10b01400c0e41c4546650310340108020070055041100c05949140c1d4602851031010581d0005128840c10000c01800e40304035802020b001d45008101c41011070381640c84160701d8400004a00d2030320048a101c3d075030302c0e442000d108002400100120710018020b80280ba00c10341c0c4900170b1415907441e1081100101001a505031301c1c5a140d003107480c61001c0c00030040600110981e1040c82c02c0c0342201d14140c1e5182c0e0081c0300c85000b07600f000104041100024551307959182c01c031000070191110f0408901420000c20083c01d40c1c2c0c8009201c04040c00c00189030582e1501c01e0302e40c01c0360880d010700040103e000c00d1140c41c0154108004070800d041c010341c002036001310010b22205a295064001c145020004c1e0044a2240d110060700502c1507046015150003101c03000043c02c1c14542584010103600340a803901000d8050b04000c900c80c030340544240742c0500185c2d00343d0425a6034070002114240c034030345400d8942e424400700001201b9690340101c0d41d04080b448203510118510b03a101803d04954441c = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 464885701 1250 464884451 464884493
    0xd0e06071b0e160206010e070903170d021204060c030504030912021201020a0306080601080703020604050d1e21020c1c0c0306050106080a060503010507090e09030f0c0a0b0f04080304 80
    0x340116440001000b0360b401001d10000d42100545a10070103407401d10103030094008110700c0c104004c50254010b0005046d079600012039110b141360101880c14034058000c00d4403480e400400c94042c030f01c035a80c1700300348268094042403140c032021450680071503070151005000983d6214007803000c0300c03107100d014a40714806041c00410f0b4425080c0c45089070028182800043c2e250582044a800200241405454600050106146103500241c0c15104903c42c19000e0103076161044244810548070341e00c11200303010000689031070351800c0c4141c80b2850b088c82010f18107048207002c078540b0004130b00001c0341014000c004200d80e40c100c40c074412849113508a400c0260020080005040d600885000748423a85440456050008640342a034030300c0d8003d98000e070700d031000b041402a405840c003070440d41149402070702c54482003011401c620510807602041c400c0007440382c1241000142200f6018010a0901001c0e26034100121648000f82e8001c1c001040038001b08002ca91840803071062050044 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 464886951 1250 464885701 464885753
    0x80a0203060f19080d08010605040e0601090909060c140c06010302042007060b090615121017060a0b030d0c1707120e010201050718120507030803010e090d0e0607 71
    0x4000a2412504010340c280140f000c29004c11200108200804042c3c8140c10110400e43c145040145103000724458890000030440202c0e4a0340d01403001d03580a00002c48060202400c24202030014007440c0072424009080710201000900c004410786461100e0304020307211316469a001c01014000b81541e00600c205000340d855a086010300041c0b6000348140d00108a01d12641c081100c401401000240240c200d1001102c0c2032142c03108a40312244040308030308050303d98a40c41c0c4a2005680c0221104524074141345440000000d1420b102d0603440b04244002c10212051503280e04020804402080106c003052000401d0f400d0340c040c07400108803880742482e00640316411902c2c00c1d0785460020640136046001c1d996820b0280340da00c05d0590401c0c5801070302d2500440c1803d040381c401e807200100f901b084c0008100742030298a008540002d0100d8495071900f0303807101128030540302543c083c03080840f41600c1e10300130544104020360080c00d86081c40c00e5601c0d07200300802c1031141a11a400c8403 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 464888201 1250 464886951 464886979
    0x3080c1617031e09121e010506060a0804030c0b010b0409061a07030f1101060b07051c23040315050106110a0503030705180d050c030c03070b0409020f1912110a080a020306 75
    0x11403902041720400e880201401c4500a82219021052160180390340e4104000c1207040c0d1a03c0040b144641981d2030700000c3c0fa81c8a040c04c44498102d4400144030040c5440001507521030300001d402074803802d60040281c982d581548070208828280c4075588103c0500540020030f0198865040115035802c000d03207080f10991400d03007110402d800518000c0000700301082031020030442000b2206284031202101401104d0251074424088084041c024004040d100721219a50542c0c000711f41c0064a85201000740c058032016080c24081c210000d020b620541c04001d200107501040e031074000b8082c524603180c80324101d40d607138891622b4944080005220b2041034441e5500002600d01900140240380e42540c1014100740842031454802c0d0f00403c020f100b402140001c4030708840100c0c0e4010303550b107448014401103028000e00c0d02c0c040200050340c202e0043c1c0100c01038240c1250550108030005011840100b03038003c1c4605000016920350000c0d04e1034490f58029a00301e08010100c1c510391700c007 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 464889451 1250 464888201 464888209
    0x519050a090b1309030801030312091104020328061e06230909090a06050a090c0519050a0612150e06010c060605150910050301030b04060b0a03080c1617031e09 70
    0x4c20070118000307251600108145076000925a5454904101c01d2004060030b0312201452202e40c0ba030988a680d002003c20f501c10084407047d02c400b802c60400e40801d17501d55800900404062061b009400e403041c00c022491100b072440001601c00700e40300c0e4422401010b01d4140210040c10034a84024010082d00300745036075154080780b0070081140200320031201c0c1e24003001666005002000d20350301b44024900015048210041610000e45645869480e02e01c02a41501b0340d9070702081c0c11403105034020885543c00056102c048602c1c840500001c2c103540400c0800300e0780c0748500b010017829500421000d6119011400d000e500420010403490340ba00c00046041a021414082e0341000255a003400d041014002e00b402c1001d0034003d045604d10b850398441000d00520080c481b41eaa00e038204241e41c1c0c1c10080780040c6030811000343d103404c0c0d6091200c1d40c91705a2004920341550b080c2c0c00040403540f18900c1600340400201450400681d101042c000c0d402e1a0385445d103442041c03200c80b0550319 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 464890701 1250 464889451 464889461
    0x150c0c08100608030f0d0b04060302041509110315060306010306081c030b1008010b2203140c040515010f051e040302090a090f0b0601020a02030a03090519050a090b13 73
    0x40c40090040078240d0140601181c0365684040c0258000344020041c8001120640303103884820180800c0c180d82c0c0c0000503000342010740000303600c1450a0060b8031404c42e20380c140d030240c2c0c075500c00400040c0141c10f40300c80c090004aa040e5992002c0540c270071100d00b0104091500a40181004102240c44411981c1030240d1403010104200c0045880210654140141011942d003030301c0500c0301030302c0820010b012100502071940d80050028421048542480810942d0300c42610003115040c0c90385000d6070103074440030028000b8070403104030110324039091042d40c5c00b802d0003c1c1b04500c4410b480300191111213118a00100b0f01c036051200da90003052402176101c80c1100c0515681e07032075045104000c400d00026025903801031400305590001514007110055894000d60781246698503040100c2c42c1c075000b024000d4142c010f054881c4c00f09900b085864082d10350489504844c0564220488507169442c4105640080401070030003403040940c6c004020f41030b02a0410b02482c07030b030410380c400b915 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 464891951 1250 464890701 464890709
    0x703051306030506010219051c180f030c080d020c090703140408040302150c0309010c02040204031203050a05060411090f04110703080a050606090d0303150f180c05090307150c0c 78
    0xb9865400b008a80c1d0b9040c0481c5001e00e06440b00a00303255410f0b281c440d0756141226545200890106180c0b40317241c014591409c0c4005028006140d107902c0b02d2200d90784401c5803000321480c030441400842c0c120404100358085103c503a004200c1c0d01c400c5d0702080b42c01c05002c2c1c651414141c0d9420381c1d00d4900341c03c1c0080c0707200f87d00881209990780c0c6188140300607410314440d4454840300512407040f065034080216001e1f840c09280099903c8000d0000074020f120307039400113001c1c2e500e80194080558040c1c01070b82c46201402070030813203907076100306200590b0001022104044d07020001c0070a00e150400304940300f0407000c2c1c00001c1d106165001c039401503004050550115002004206843e605c81c098658070040a0f1100c2d4140318485011860382401084004c0c141034580c018032500070041510b40c4014001401d04000b1550380792007900802c081134104c98410790500420010580c080c2c0c0450740120000380003002613a00d0960f1005500145404180c04c104d0480c8440c004201c0724643c0b031000d0 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 464893201 1250 464891951 464891957
    0x80a08041103010c08011a070c0b0702041d06070e0301020406050406210c17100e0c1c02040605040503071208090d0c08010c030b0306090a020901060f14040b070209070c020607080703051306 83
    0x1741d418074001007a1006e006100941e41d6804015100000300c0d00c44410040380d64002010b500c4103c00d100007130280810611140355000745014860391f405000583c2406510b043e2600c2c900c1c882110700745806d0340314038001c0e1004910200400c0000e00d00c00c243e40308407080040c40c0d80a601c10701500709401d81d01c00c003405c18001100c0990401500111030741558008000ca8100492a89001461461504000d05142e00e540c804614030586061140d030100f0100240c0e0400c40d81e071030300d942010700139401c41e02a071400380c85071440200390120245145508181c10000840c10f16201e07038200046031b0000e1108031845045c01d00c001034420406d0107059060441510302161a00e0344006140c0b030f14030f000308400047d62002004002507111024100d042d1801c070318040f5000400c210082d50440b50210782c00c501108006000540600400017400c81d140c4211000490385d10303082d0003128400b01c9080080d5100318100200e070f00280c101c50041030072520a0510b10b080034110700a00f60000400d41c020808 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 464894451 1250 464893201 464893217
    0x30903041e0f0905041a0f1614160305130303030b0f0409020d02061809040605040501050c0a0207090902011b0501050907080115031b0b0f0a080106030207080a08041103010c 76
    0x1074901e1012004054118244160241c5807401021180d1454032490101c5951040402c0a0182c010b40c1d444424074509984602d03400c1030a00c0b000e40343c00456400300105120340c2c00701d0419128203114961915140240c50415100417068031a508030110214140f0108209500a40543c0340c20000218080d450004000c1a000c05005412203030b02c0519104515058100c3c0040c0d0300d001c2071441e000e40659000d03843d181030080040900400c800307900d60108842d01000200007194102621880c0b00d0b0f0028001c549603071a107000140202010038015030013100c030074004000568003e031002401450540c4c3c01c000c3c41d95901408141844054600e651200104049840100081801440e64500800c00c081c2d419038803c83e44142ca000041a00c03620822240f01d8280c03000a901c09008030b140f06542c0c0d0080329460440c1580180500c201103003600d000094428020b1090f202c18903041605507180c40ba17280310442d40e4080092080310810210b0504090b207840c24480c020358407145486001d0 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 464895701 1250 464894451 464894459
    0x80f03090120060a050a150b070c120b07261e0f0105011d030c120a1a01061e0309050d0f020c0910051210020a0906270b16060203090304 60
    0x4800d9100049010001484008012000b140082c901e6403040010000080588840c084130303001d0078440b140c03503040c11046400443d0301c0b200c0500810905102e00c05140b4815034540c1c00da030005650250141400c800c1c10b0000d050383c1d00406140d03140c07001e0040c1d5a10b41c2c49140c0807502c04a1001d60b030b43d96001410500f0359100a51468160390031014201c01c1901a40c50000020908410b819541703684000c0b02d0f0b018070750740e00c2c01c1220152501000b0b040000304001c0c2d111301541e03845401d02c141c0d41d40c54411511001035901002c914141c0752a40d03a2800100381d40050000f00e420501d2506c3d08150f40c480380403000c980c09000301c840300d880c40d41d55a000c111032614000e180c01c800c104001e00c01e070707134a10a1040e04e420310741c580c1c000c6841c140e41c4480540165a00281440461503000ca10326000040c1e036040c80780c0c400e003c24155003aa440325100740b14010712198014090080813005103100e8102131000d2010301025101280200da88503219490960303d1704261b070800d90b200c0c04a5400820244 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 464896951 1250 464895701 464895707
    0x909200c0709060311210705011d13090b0c090d02040e0a0c0b18190e09070902210109140714130e010905010b0c1518032a0a2307080f030901 62
    0xc402161b08402d001d4009402c1c480306074803802d40d4460030303050007000d0208501c0e030484143d1086100c0750052850079040c0200c1089006400102d10072101140084002041e0035006000c1d16032481d809054814260b41d1642800010141d01010000e80c1c42201c1040b0001400f404100700906015444140c9413050f018504061090f24082140f01d40b058041c11101a070703101000c5021074103d16050002034440b03041480c141040754003d0002c43d800050389800d0360342181074900e4003480c904410322040e079959a80400b141c610400c1e95000e924240003190f6840d10540008003143c0071504410718146c42c0044040c0345030000c3d441030300110140c2e8010888268a8400c0e240140380190045207051160000561644081340314040511941808200d08401034041c202403507041d40b0850340c0c0d5103540c030000c541344480c020070b0741d030289080044500b940c000856964100d80e4440d183c0c0540040c425008081404405404c2c1e01503c5920000034150604024403c40c2003c070f07902030340e07458401034001 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 464898201 1250 464896951 464896969
    0x1905060a0e03030f041103030703050a021605180604020c0a060b030106051f1d10080a150b09040b040b06070c061e0806090615030a020a0909200c0709060311 69
    0x80c124562419034809050703040881102c0d4815000300383d603034066940e850001d007289240320729950144804a1b05000301a000401003480901940840341e040c0981000b40b0360082cbd242c012650004a0000d9401900f07034460f141c2074000d0f07130050015081401804586d0b29050198000f510082e46884081c06141020701c81e001c00380c8800e8454090b030000f52211501020131340e036070603000c00030b6001044c00640c212000440040070000c003403000c540c00156000304030140580b40125810b00d0a00f0340c060394078006e088803003107620b0b20003850b0600401004100041ca2409100c942188d20764050000740c0c0e407420000c1c02036a116000f40d40500313080010041140c21525504a032103000300f2010718101d03801c2110140d10483c200d41da0032081d520b54020404210306940000c11303146011050020240203500603111104559845282d0107030345c0c4240c042a10140044001076041b106848018803804c04020050841d540d000c072186a941e4403016021070b41036600648031501c0c2c404880d142450001a0 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 464899451 1250 464898201 464898211
    0x5060f12160203070803041403030a0218010f0e060d06030f0b1e0601090e1509090706030c09030b04020126010f140618060c0a0b0916170309040906020c190506 70
    0x40540741644003030081e50302d104000014000c15008000a000c0103070081d510040800140e080d40d8890a10740701d0500a9080300f41c00748240e10030f0711482840c0394818448c480d02c020703990f91980c214031542c0702031044540c0010402d2418030f4880c4404002b1403980401046801d00c6403d841002c0e2804400c04850741401d0486100000792503c00d010301c1d03a0b840024501175641c004110051616520f00c10700701030300e0701e4084541004414040080c5070307101140c410103c0710b058505110102c011a01290302c40440e00000f0a8400b03000041005075100f1400c049103400100440c42da880c1185c51002c0114800741d0084600704000b1038144000103a00c0000c100100c4156102c5007030560251440e2001158a80300502800000c10005011f40040041200c1c09400c0050400f0504200b5021500d6114543d81490032000c41400028460710000d0307090314a01e0344002441c00c060b200700070003018004058069075000d40a0242c11520b11f803d01030009110069901c162103210030b0300d8058144940105 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 464900701 1250 464899451 464899471
    0x25110f0a050a03032910030e250501020a420b030c0f060901080604020906160c050d0b0c03070302070c06051804150315060f08030d050114060d020702030705060f12 72
    0x31611344515a071800030504142c04640d156406ea4120070f04070300420b10719000201610420840340c001801c00404c0503e030900502142100d151940016071b0b89002d03125000344841d904445020380403000d41800031080d580e1020305044462001c0380c0d01c250442d441c4000941a1b5601180c10b41441d04201c0e988220401303841042d000000c44000400f9030040307800107030601c04e507280081c1440e6038135070440341c2c5100e000304155114615260b00c6440d4410291084a03401d0761a00081028603084070105503441d0310140e01c4c403a694407000084850f41001c0c114505264003440b800700002d01e40902c540180115680301ca80342c8442090303041003001340b0703a8618080c6140c80c40d00c0314030569000d4408188c1e07030845e1303194111340c6620245100800550b8410151111782090100b60340710040b00074181303201643d40030710641c1d880300c08900990b0540e1307c00700e0b48148100a01c054456194000c1c0222074001000c0c3d943c400e503200701155150748003a0f0320301510307000060f0007a42070900384100c0b1b4120280311 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 464901951 1250 464900701 464900741
    0xb03122802070323010b13020703021213030f0804090c0f1d0108070c020105160f03080a1415060c06010b030a0c081303031508120a030525110f0a050a0303 68
    0x40c8400d441c0b44c0d03000708182540d6000d406440303440c02094006c1c40315140e010302589485840b503907100000313400840007100117000d000342811001504809507000c0f140c6105581100c03603c0c5680b41850803000f2881102c25107024032000031224014455942c00000980300c0300d00203400c80900614038641ca00b6420716001c002d5903d0001070f60b11100d0168402c00504080180c80c0301400161a107001e0010f8443c81e80203458000020800f07504002813281c1e02c2500e03510200e44564107000c040d00d079002d20060001050000003a0360030984940d010301f4000240c5054030b0191481c02290504000360040490318500009004a4018030711940c8403085842c54015500e05051481140c14680c001b00a000c02d620f40091280940b030b40525180140720301c20840350310600340141886903030001d880c8100070034a888002020100350100018496429800b10750500c07038540b0781650315030160103140c00d142c440c21060703280302542005004d800501483c001c061005d000d2600400ba1f50340d80a82400e022000c03 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 464903201 1250 464901951 464901953
    0x310080d080115180603020f0405040204030606080d0908030a0503180f3414060c190201030b040b030d08041110080604110f0f070302160b1803010e030d0b031228020703 74
    0x84c02a641a200d003403401682c0c1e01d180303004801c2140296042603522601c005000070803c28554003a1003100d130b401068901c01284030000f52121002c0348183c10954108010702d5035000e12460017190300400b41d8040b05000d00e81c47c20540d02d0708005804a8001d5807080c041f01800d409150803042c00500c400a454507504c80b055281140590207220380300d400100109000440d90712442036942220042c0c08440b10001481100b01501c43d4004003039001c2482c000e01c03505141090300a00346a008080e00801100c0c40600f030031110410002c0080c1c0b203982c00c50314000c040b503464154011104450356100301c0b6034200b940412007100d1543ca11403980b02000c000030029040d040c000d40d2102c3c2e0f100d4403040c0c0c80d1441818142d09042c3c0d41146860611503040010400210350006040034071501c81d4076034105800b86040c542220344073b8502481d554000e019950340c41195400a031a00c42c4050140c83d500250005040c000c0e40150f211642ea0f00c0030310a9000703d2500d48041e1910003086403000b0840ca5140d = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 464904451 1250 464903201 464903237
    0xc030310140d111c05030a0801090603030903020913021003200a3501090516090f1701060b041d1506090622031103070501030603080405060310080d080115 68
    0xa006030083c000703260390058522680c0d0740d410940da2403135040f800041c002d56a00c0c1040c0c03294046074085000c50899030003c0750b800b0300c44c8184415243d0503100d03180c0c000d085408020111070002c1040f15080d142e00c1c0c4e4000140c441401c50b400d500c8068802040f030410f8100601412800d0440d400c019038020302c402d8807a590300400c0c007010055242e4030507040d8414001c034040522038000c6c4d1903411000c020000119a0990707442217105001c20002d595000119040444e02d055140c030607001024500e00c0c06004004442101140c2c14401d80300002e0080d5540e9413400c1a50800c0e4031805503001d8400600b01c0200f54600425070000351040c030002000c82c0c20700014443e004035007020380500c10105554020311802d180000c0c0000b200c4103101150365036803818810541119107028001e0103424000145540240202070070b5a61220259081504140c2401142e03040104070032204500c6a03c0001c52980a00c00511a2100c40e03480c07142a604041d248840d01120340c007500201b0003031005171458586d03 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 464905701 1250 464904451 464904469
    0x10c110f0d121214011217031e13030206070f03020417060703180b0c090607020418031e0203030118060302061308060106050f09091f060507050f0c0a03030c170c03031014 75
    0x1506d485130400081c980d080043e2140e801403c41b90401c1000804c2c040d4594043c0b0201032203040c090312400040d500c1c01c580d060794110710440100541d002c007003c00c0c5403074050001000c200c64140f41c0107040540c1c0fa01140d80d11040c1c140c0c1c0d0660f503044803040c407070103682c9030040c0e8411641408450702480d80b242e42c1c1c90004c41d801021001d0000000c5003a8584d947c8590844c0c000a800600c01d2000020302c210744540d00031101c0b802c6001c0384000320a0303d4a408002086003008030103402450a580ca842e076000111300520321111350b071690311600400140e40b0302003d4803502c0861000110309605203120310340b400d103068100b0403c0c01024030624091419800c111005c009040d81e1101298aa03554950310005404480090042030040003040090b805005410700c94040e6080314451141d444007551180c0c224550150441000c48040c00481d001d094880280361044006480ba04412550301c0f019401c4007045600982001050081b180c80c0404408060b208401006250300303200e400280e0129 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 464906951 1250 464905701 464905709
    0x60304030309060f0507031a0a080a140a080c031e0412021e09130308160512040311010606050a0e03060c19120c0207080f0606010c110f0d12121401 65
    0x350b1110145001c10401e41c10441d8044c00012042c492030400303c8019001d001d0840280e00f01070107902540a041ca041200d5a042710b040c480036007920041e5489540403807800c0c0031100b0062103907a000c000043c074102c008100c85807610020b0764403603c00c103690001c024850340074803c1207a000c0c8802d100041c0c00b0010340e06200d42c1111040c01044089800c0901551501d000c154007810322820001c4440b00b0a0940961510942d1058035503074070070318101f281e030300c44101c544000354040c0100b0642d0790441d482c03150014024240000c19242080c1142e00b03460726901b10300001140032810245503500000c1300402200110060135007460b10207095582c90040403201904030302001c031031040b004c0c015909441c40d4447d901c41030124070390300c04010f0350b156082e00c904038040c07148010310001070f00302080050184505a50b515a2515a6280c40018040421500754403081e0400140e140e59211107500c0e00341441405000740c4500c045502801d194040220304403103601300a14088100b130528190340c156 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 464908201 1250 464906951 464906957
    0x6030403031b020a0804091d0a05010c030b0604080607141b1e01021c0f0b1903140616180e0906040b100b040308130f0305030403020406060c050307030e01120f06150306030206030403 80
    0x825070081c60301d03e0350b201d0234403e0310342c80c02004160020300a041d00401681c049944040c03165110540501c00c2d148110f00c14902640c00c8440071520903840362140a0070b005000044908080201c08049482040e40581175072640c440308400200c00300ea034030841091902c4c03600031418001800201003040040c1207074429200c0c0c3c1c4091030000258261700426640501410880b030003c111300d45c8003641c140c03600007654000e142e95601e2510100c0000d51510582000d20070b030b0841d02c060b10080e50314000f1170224446e004120304012035980c8590030300a20a0720f40100508050602d41030120044c00c01807d004c0044100300000c0c0440540b0700115030440f42e0041540c4d941d030002800d081d102282ea6048a0703010b00f0400c000006000c0000040d0007900d008503800c014031070303440700165540d800528004056030801c0c04a18080303802001440300411042c184903121031104201d80701242d100d42d0500d4560f42d554102031140c90100700100c5041c540b01d05082100078250307000078065010043c001810 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 464909451 1250 464908201 464908211
    0x210921080603190f2a090203010906080307030c030e1f0f0305070906020c19080a0807060606020313120f02150c060105030c1f050702060a080f06330906030403031b020a080409 77
    0x6045d84c0c0e42007240343d101e821810411500e454220110103580280726200096052003800728070048040216503800303034140c403400d0701c0c071181e95800d88a41180a0740c01d5804500d90032400c002c440c1044043d00400219911002c0390b440314072014040301c3c1c019204000f0002c084009000c80303500019802c5115904444d0040072214005d008240c400043e00301d4900c9028803582c401c10004070b4400b0308203d510130401489076070344a0b00203e07543e020310031361491380d0a0303000b2040041001441d0900262405840f01840b070303000903000b0900b0a040040d180c1856800002e0441011030240f00e56405410b0441c013a006089080b000140001c001c055030341a070ba1200103034920f880c1d0250003201c014980c007505681d12070003084005020140129010b402c50310880001800900d0254044d00c0c03964840900a8960b04681c20f07920014030b6919a000501002003191070300c56036908028500c1544240e80116264005e20082803221801a070a54203551191689000040c0c0e076200341e90a540954900142e = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 464910701 1250 464909451 464909483
    0xd02070501090b190e030f09031518070905060f040b010207030c0608180c0d0b0604110c0f0c09070912020d06021216210921080603190f 60
    0x911418600a0440d8603180c0a40b041150843c0740070300c600324594400e8501c100100e00a070540d000d501c0b01645540080180082444250001e000844070141c22244540705810320f40003940c109840f0700d1a032030120354242d41074000800000010f402d040720180f000b800c00b030020503801c00d840c181e007030310454030b60683c40f010340d1003008020025504501441e062507611a0003400c621000e6442e00d000004c02010b84800000000396400900300c0642940c14207002a2502c50701c15030b0141000d0352040d290410003030346810440c09000920601000b502c280113028180130318101207241c1c0c4500504000c1c1c20440b5564001c00f070442142c0440d042c1d182c05902ea1301c0064202205041c00800c00340c40860310b00c040341e1200741c01c140302e800001ea482403201c000850036144070f0900800c01603200c09006d503803d9146a16041031000602c6003602500302043e51078608007841d0a1540000054104000c1000303511301000415540b0700b00c6c40d09007500c004951201c0c440d02d40802030160404004040900c = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 464911951 1250 464910701 464910727
    0x418020604031709031b0f040504020d1202070906090213060c02010c140c130207050c150403030e0a090c020f010605040603120518090106020a034503020901030c09051008030d02 78
    0x20b94013a80c0141621540c04070000d1100140c20304418450045040104840e010300b030a00c10903014980040c0700014142d0150740d030502c40c12040c00a1411400b4000380000c1c2c40006008101c080c1a141e01e01680381d142002d240d00c212802c03136021030204001d100c0c0001c0540d130441280004250080136010440c9500c4800c24640301e600504241c0010303280100d4001220540e014004542c80740b42559803032440c40041060005012051001c0f24a040201700000783c018003514101c03403006041c507400c3c02c1d0f40350702d50b000700da420b200203202580000021071143c0cbc0e001c1c030811002d0041250100801ca0a5850700045220b00c40300240500400003400c240d800400d1805003643c100c000c1050b506980c48280c02915280143c0c0100d0105040c541d108400113040d81113000007248001d03c000c403038074010034038101d1218104140d50703000703056281c0440580c48800055020714001c1400c03140c09890039905000321107004100c41551084e040081c411401e000c01220480411854056142c481e1a0006 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 464913201 1250 464911951 464911957
    0x5160609050703080904050a090b070f030b090a06060f020304081002180a0b0c0d080f0403031107051501050f0103090c0501030f0f051009050f1006140c0f0a0204180206040317 77
    0x240c01c0d40714112001003000f025400800c503584080d1018011030325044001000d448281600410854414000506544c40f502d1808181c0003030381380210301b820410001c2640c40303000380d4001c2c94483d110001442407070b40007101c0e0707030300c0841510055141601d0460440d07281c429050710030710a140c00080c207220741c403480115040b01200081a80c140107544010f10764691b0301000e03a4a03254007a05554000032401051010b10804070040b045070260f8807964118004c0c54100f104d40881d900034025100812020040300d4004a00d903000d010f01941000c007000440165565800c0c105420103039640e00240909511904944082c2000b0900d15101200345001e02400c00706140271601d0181000409104003a0034421100d50303841c200869200d900c0300082083d812601d402202c855a041000680c0c40b4100c0340c00a145150799540c241412040a20304114a401003031049601034490038083d49040d228011524401407da548040303081da01040090182d40300203003604104405100240c0015022 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 464914451 1250 464913201 464913203
    0x10e060d0c15020109031b02010c1106040312050301030506010e04080d0b0a09090302101103010f061b080d1d2a15070b04031704030503160306051e150a05160609 71
    0x1142c0c0c000105060000d000b060800307002c0d4006580c0030303032000c4905005c0500e003003810f0301a5104080c030395242d250800c02860358044c81d500b1002c00c0100201080652076071180e410143c0da1519600d51550a00510b82071043c0c011b44c08c8210500c00748400100e09000725410502100ca020544c50f0030070300001c0c407070600e9502c1481110300b040740354810503601052140c4034200c064000c01800c2030f5070300d030104e407800700340641c000c42d04ca10442800924003815601c0b0701741d02520140b40031403605e82ea90b01c000360801c1c1098000c264403050b00c4201080c55a0252654410b540010f00280c013030314a00a1204010410720100001d10f40c90410b119210840c0d00090052111b14460b1364020902d440303001602c1c100e6040d000200c1c801207982103000b90101c1c140c0a250180d0380d65046403144c0305d0620403906c1039200d00c0700341581c0b480c0001c2c0546a106074a80c414140c05808209000c4074001e03c21a0028907502c040082020080034034101e4104095030b0601d030070b414201c02000907a00e0a00c0c010302884034 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 464915701 1250 464914451 464914469
    0xb09010e030c070e0a0b030a0305030a060506070b01051c0309140f0306010e061002030405010e0f0d0605040c1404050f0c070212301c0b0607060e0307060b0108010e060d0c 75
    0x60b81801100b800a4208101d8040d16071030a01c80c1da0b1040c850085902001d04568036803c09001100170034800d00207180c202c9042400012400e42d6030000900aa0103404102c4141d071403140108134525150040001c07201307400380340c010481c031301d5038009010a64034051b400519900c5120300710706407141c0300700b03081c0b0441c081d04803452941c64150001e0300c0321044401c948507482d07403071400c06072a10200a84044503010307159030803404641000c0002070461001b0240d00441003484550200c1c11034040d0030700a82c018494403c2c683c2c00d04000c4400c14007030000142c016410841403004001000c0d4074181d110b05204403c5031542c0d210f02c0007600540d800145800036204801c00c079114900881905103603c09071480c4203034051011070002c0883e0003100301c601c1250017110000034959400ea0010b022258000f841e042c07420059941c2c440c1182c800880741c1d1101d900204090b81000700b00d118240000ac07003420000c680e90314001050ba0940303030080c0100c1c0141c4000403000c080004030311170b541c0640030180f = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 464916951 1250 464915701 464915707
    0xa0e1302090a0f0e0d02060109110c0d0f0e010c260c0a1a06040908311805060906060414040219170a020313081e030c0403060b0109120b09010e03 64
    0x80b6440300540240c0922403032441c44c0807152002d207840012a5200e40e04160040c082c2070786444030400c0201445a00884100f004001d50464102d00b80b0103e10010300c01d032580d40c9081c03002000244503050f600c0e102d6041c44081203000000c01ca8508400102c01001251001d88400eaa0300b80806030068848145030303032251040320006c00100d810101925021481c0c20011942d40c10f04000a4954049014004620405c259031060780c40864014403025803206002d04100d071500301c142c0c03030300480d8070000b01203101c0800000c140015024143d0859001c4804c02c00b141480400142c02d0300c00c600c50300d60b80c403c03202c1c80ac9034a40c44507015510105a0b401c40c0ea1080b10b40d010001e00480c001c0b41180803265404000240240c1381d0b407095038000c01c1c2c14100510300004680c0d80b1a2240e22820512458515000781c890200040c4002184508100004551100e1451505009454400032040d0511003200028807030300c201c0209152190387c125840820a0300c0e00c0502500401c1c0946012685000c00 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 464918201 1250 464916951 464916961
    0x307031b030311010b01080112020f130b01200d180308120108060907030506070e0109030501020f07020a150509040914060f100644090c120a020a0e130209 68
    0x400303042021a80a40c03145041c3e4040c0150160803074036034505440c045158100140300c081014690015882c0c405130001900e80524030000e0344454001c0307194000c641c5c903211305600c83c0d640010284007038215003100d80d12106211000c2516401c074014500700304002680c0c2c02444507000804080255080220b4940e1609400c50401d1418800d0058a9091050f0b40201d401d401002801c47c0840341c20402809241c1c540c0d8030300b1120102403808041c10020411404400726100384024500781e001c015016070707214100d106001032400c40b0707403189500050501500464a800c8400c8407200700e0b0071240020503d00e9842c2042907001e6a150301440761062400b000a2013001e4450709000b60914070010105581c0c400c01242c4840420b0b42c044034150700303d1080c0241070203120f110f40170b00002560740d1003030705002c407810340300420101d07003184255004062581c101d043c075421401c81c0ca982003014020701c000b107401041041c40140b02d21001c2c1800080082c5030881d240b00c8089a0f02d0740105a14528101 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 464919451 1250 464918201 464918243
    0x1608062e030c0e010e361b0a151d010309080a120e0d051c140c04260c010c050c1905031501051507060b1003140a0203011d06030703 58
    0x4500400d006940d03d000003103000a6007004542c850364202402c00703c288100c0080181c41d1200d020b05a00001c004000300c1900181445855001d40e00c4845980f8502e4181d000c203d10003545500c11042c04010f44078480d8840c4d4007141402d500d90301d40080b5000c0914040048000f0303d050407011f00388000120f68040d5a6a024410700f2010310106003d214031120440e500d038440c516440071101141007085050040c606912041521918100000540041442600c040640c04031b484510700240000d0074401c03441c94200501e0140700c1c0411007c40706081c4001c2c941da039280400da00741400703001d82444040000400090840c4d0300c01401804980c14808000c1019030390074021a882405148210a01216a80c00807030407100700500b202c0c800707441c00740c9404c2c00d43e0000d802600c0c0991610480d106540744c2e9449131541c0ca000307030740000d0142440001d0150301100509030220481c0108010480c2d034501005c0c14003080610580303d051600c4100020703160048a0780000e1201050111030512006 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 464920701 1250 464919451 464919473
    0x115021006080d080a0b0109140a080102041502120a0807181a1804050601021e0309030109080703120b060d0e0325150b0a0e0702011d010204081608062e03 68
    0x41d580703130300c080d03030320380544400554250b41e0000d070001d10500000c012421080c8003d000d101805000080b1540d1152542826a032044d08a10501c545141c1d0603c09036604000c0c14000c00b08907581d0a082540008008050000140004003008042801d0380006a0b080402d200100328a441501d442c0c06000d1241c80c0d242c0141d201404810900c4001040c0c0d0b0426010707071031041d00140c2c060012181003401d403110700c140150265042d48014401d41245480901c160034100d4007625691351120703018500106050503200c14041c0e9141420300c2181e0f07988903a42910550b844001e804203098241d59400361660262005a40700c200310555008112040c502c00c0c03426180c0a030f1000c840d172038841d01c1c2c10f009449001360010781104651204211500c0c0d0801d07082d42102c1d070b0b807001154401401c8080000004911f0440002c1d940c0000d0130468240100020030050003629081001e503403a201c0c0385500d0303520040c440c104a00e81c0741e900c50013030b00140b2001c40d0801085407180205030340701e00b00790404030 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 464921951 1250 464920701 464920723
    0x1030b1e010e03030c07090905070315021b0c100e06091801030303050c0f09041e020304060501050a080c13090309050910090f090f030e130212101508011502100608 72
    0x2c2e00c40400084030f0802004030b8030050700d500c0c010541640360001080083c240c41c407044d912400366000110000e034807005440510f4080b0348001d13840c0d08170b030100440e6804000380e0010f8250310150241a103a102c0580c11026001c1c1400e100c01c1d03035007000e000700d0080e124008446900c10030004140001501801c0c4280c142d0740659420482d0366113401075500144180f421040030f0400600c4114094a05070700842d80b60010107441c1d0011448840e074080a0782c10580d800c6590326103400050215082c0040c50600918103240100340e095417150204140500301190407076202e44800d600400d150150001d030f801090090303c0828545440c40b0344823141c60071400713021041401d24046c117000e0003060086040082d00002e400d02c10303100c560ba0a407901e45a80080c00d8014034001c0c2e941204004500c0541201c0d0401c902d41d0b221445c5c00f00c18044007140503080003c3d40c13a0001d0030384456580c0700c140386054640189101801280241d0103078030300221069201181230400001007541140454140c4000b = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 464923201 1250 464921951 464921957
    0x62d0909051b010203090307180212180d0302030106090e06030705101d1906030504051005151906050f03090f011a01030b092511070b07290a050601030b1e01 69
    0x2e20110b00480e00ca2003203900d410352541c455002849800303110781031011014096030f001440c264100d5842800c072581142e288480c054540e680c2d1015007018099030228504510702145558103040010308110821301a003603000e110900003803126202044140c028100c01050300e4401100303c0380c010116020b2034040062085041c0c1410070a081c0414241d0032000c5040d50518160704200382100103000040059070144a04103641d8070790b041e40d2085501803110100022600d50705123091283c41140d4079056070503602d610400308070300750340300d010f4420091003c414181d480e00c43c110307580d15202040d2545e00301c075441c1c070f06643ea018202c41c05d1140e51003401e0702d060140ea8201c0c020411102d8003168485000181c1142e0b5100241d0041503035181641c0900b040407200740d2142c006890510340e5008054125000640b40741800400c26150315111104003034100c1c819031002c040001c41d80080e181c2d004250725100442d6031a0b000742c10018030700fa40540400c05203000740c1c0b284c000300e030410341429004c = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 464924451 1250 464923201 464923243
    0xd0b0109080303010b070212190503190207050d12141611090610030c032c07050a03080703050315120105010303030b010201181707210909062d090905 66
    0x384400200580341200c1d0000366150400c00d5035000d08c45000128480119940140741e001810340030469454001c0034044c074001d40d00c520800360741001c0045003040c20030035940701203400c000a41d00c0c071840000385075024141d00c130910ba9980d01901c1e0540a0410003a02c200d0110b0907030001150f60103004d410500a92101952107141010301030401d4003540c80d244c018420f48010081c95010741c1180c1c4c1252814900007034141102c4014030394100d406500c00b01a154022042492560108141000350008031452034005140d80c1d24503c20303110b04500101408008400030340c07410014903220103481400b030646500f0b0080850454000c00c1c0902040f00441d1800b00c2c20039040d48144524003800e00456500188158680ca4000a003040075400f021402020000c0b003000a00000c50000b560b20001c2c0da080d501d05140310040d200100b0354000f486428902001000a43c01d2840f50744200307102403000120071441115440a00f030a607810212445040c00000402c1000000d0840d080b5240d84140800c = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 464925701 1250 464924451 464924459
    0x1503031201053f120a0507060b0a170303040b091903030e030d110a08070503152b1b1d040809030a08161e0b0106050c030705101406100f051e0d0b0109 66
    0x107243c0617900d081c0000860034411840010010350019a249500401001c80640e943c0014034040d00104401c0101ea00080b09100400001092484e00702c61040f0162242101c01ca4984403880c000c50009410140c407600030380841d41043c412501d41110440003809807036200c17041e80643c1d41c8210228030004140c400043c25852058081d240a6a25250b501c05041208410419214400d040c0307610080020b040300c001c200302c2d80c0a1007814520410706003101e6418041088846150356000080005c100348042c00110a1110040e03446070740712601a448921a101080c505081d855000b4907415000410000711310035030b501a41074612550243c200344403805e00e1800c400c200400003d00f401074080041c00b161340100054402c8401703100031a828105030341c9500f860082d942100085441d80c40c01000705850145260640c005003d031541c00d032040c45520001c00720020785600300100b00c80800c1c04180380b140d01c034000c5a6482c00d0114542c85d1028a08020020083c18003414003103a4030341c01c006 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 464926951 1250 464925701 464925733
    0x9051e0d0206102601090327030b0402010503130c0b130b090d030e15130302150901120b061e040603150b07020f01050f0d051503031201053f 62
    0x161003a01840c2c45000b0f2035203040c281100c00025040440d86159504540640801d030922038000392a0082c0d0700c1c4200f80805017028602ca8014071030081460728040024000706001540e10380e04141c0c2840e01e55903d940300b0250160702406420001d000c0c500031000080d100c2154030150a850300284544103030107640d600c41c50817a220307200c0c1c0103820121407020480424041d13091000c1d80600500f180c04030f10040ca006244a07400342c6070040048040300424010350600c412180300315020011442e1820b800c02c800a0f01c0c1a01d10307071030210380503218070080b9017076102c6005660020000d1094004035083da10403c28140e041806400002403a11820b108504030460310902189c140100c80d629000b00da800f406144008107403a01e051280801141c003000c00000c00070a0900e00c0d440c07001902c1d0822804481120900e0303040c051290b4810b20000219031500030546044403021520a41002c210904400104520780020301d42c11010500d2490041c0701b081500581400352030581c3d40b1008499254 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 464928057 1106 464926951 464926963
    0x1701110309010f1404020f0d030e03150402041401030803042a06030b1003050c0a05030405100207051b040501060f20100207061d0d1209051e0d02 64
    0x1e08500841e910504c1c03c02002c40508221900341500043c8428405080c00361003441c04490361020140103a034001e947c1800a02a40e0f000020a0340022882c5001c840c164002c6040c10000300c4040000240340d811717a58050021401e689440c0c0324802c10008201c55486c9070842d03081c02c400078811010014000304515503010130040e28000a00801e00c0d45644031f9410b0600b4241404808410300c0c040c4c07541d8551500d020364482da00c6040440c0b4007012203524050f07881c800100c841c1448004500e0044444494410010700110003080c041180c80034420000081c01c0d500000d034580c0d2042c40c2100c88150104440401203110502450a000504601c000701d40c0d80080d00c1c6c0100904c50090f401030300da401c0500040001d8400d00180c840c80c00010141c10080100345560200505a00c450100e41d04a4122020811501030307090b04284518000401413240c00c3d603c640d254070005031 = true := by decide +kernel

theorem cover : BRFrame.Cov 464748201 464928057 := by
  have h0 := BRFrame.cov_init 464748201
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464748201 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464748201 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464748201 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464748201 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464748201 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464748201 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464748201 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464748201 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464748201 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464748201 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464748201 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464748201 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464748201 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464748201 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464748201 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464748201 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464748201 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464748201 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464748201 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464748201 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464748201 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464748201 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464748201 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464748201 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464748201 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464748201 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464748201 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464748201 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464748201 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464748201 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464748201 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464748201 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464748201 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464748201 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464748201 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464748201 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464748201 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464748201 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464748201 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464748201 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464748201 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464748201 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464748201 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464748201 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464748201 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464748201 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464748201 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464748201 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464748201 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464748201 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464748201 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464748201 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464748201 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464748201 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464748201 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464748201 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464748201 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464748201 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464748201 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464748201 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464748201 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464748201 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464748201 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464748201 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464748201 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464748201 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464748201 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464748201 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464748201 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464748201 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464748201 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464748201 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464748201 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464748201 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464748201 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464748201 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464748201 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464748201 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464748201 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464748201 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464748201 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464748201 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464748201 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464748201 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464748201 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464748201 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464748201 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464748201 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464748201 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464748201 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464748201 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464748201 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464748201 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464748201 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464748201 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464748201 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464748201 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464748201 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464748201 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464748201 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464748201 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464748201 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464748201 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464748201 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464748201 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464748201 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464748201 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464748201 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464748201 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464748201 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464748201 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464748201 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464748201 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464748201 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464748201 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464748201 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464748201 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464748201 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464748201 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464748201 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464748201 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464748201 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464748201 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464748201 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464748201 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464748201 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464748201 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464748201 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464748201 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464748201 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464748201 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464748201 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464748201 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464748201 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464748201 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464748201 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464748201 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464748201 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464748201 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464748201 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464748201 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464748201 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464748201 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464748201 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 464748201 ≤ n) (h2 : n < 464928057) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
