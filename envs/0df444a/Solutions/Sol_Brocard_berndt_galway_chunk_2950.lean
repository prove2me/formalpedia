-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2950
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T08:13:29.199664+00:00
-- url     : https://prove2.me/submissions/ec878f4d-e1f1-4d02-9a67-c8a181c1ce0c

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 530395683 ≤ n < 530575539 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 530396933 1250 530395683 530395693
    0x30506090901063b010b191719020c250501020102120a0e12070305070213090f140304081002040905060a0e15060705010c080406051303090b03132108060111 69
    0x45181c285801e0f1350b078035455500010b00034400e445280820301000b0380007403111305000b00b00c101881d208480300e031103030703c0c11443c201c1001508604160b811400203401d83d6299041080f002054450940440303c1803141d0108642c0d442c1c1009202d501c1000e628000200d45203030f41c0c4c40c009560340c414020b4440340d03031590303100c6031960312040303905402013840c02c2102406000e0b900d40e4890800444014000307050294840a944401030310402c0096a000841043e11a10f000751030004984001200c0d282030340e008120b00b03420005c107540249076001c1c9901c0b450142c807034090318100040d010b40103407044500c00c000c05d00c0291500c2e001c1001452090045002e0380e560040040c0c80c0302c400394540c4103426405844c262400e86107489aa003560600c41c41c4a0105164106000401c4850310070150b01c004002003030181e498480c0e0780140500c0052180e00c190340e03400f001041c40e1070010207090200d280e01043d42200071015102c0c058840c284400d491010130b00b0400090905d5004007010403400043d003000d41 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 530398183 1250 530396933 530396969
    0x30f04060b091e10030506150409120c0b061c020f01120608070f0905010501020d0513030206030c1308010b0117060307082e1b0507030201060515180609030a03080415050703050609090106 82
    0x4543c03808d10b42001c983c81a01d80107080082286030000780d2100303980d665001100d09250820b0800a240905401d0083c80c0c080c2903600c20940c00c45482c280280c0c100e507110100754028004803a001c01074203510003203510385040010001c80001d903c2c401c88000c07524150301107a8501c45c030821a182407140e18003580062440082d114070074030091980c0355075403900c0d81c003007520ba03000324070b254004550303940300800e0008008032a091001881c0700145440e40017803081e01c1c1c0c2d0100003401040300011480c00440c460001ca030f09560705014060180a07605d044511410f00308000204010040340041c1c00c17038102d00383c0340c0c0d5070842074044d40c104141d2819258513103d2080200b100c866010120035400c555035100d001c0341503654000403040c2484040000c54940e00c0c61510641c10306034280c40c3c03a03c40d4104101d1088140c034045200004150141400b18a9a503903041400000302c5450401040074904020402c0c030507019401319004100030781d41440107a540040c11401c0703482130301450380d0f212403600c8c0e02 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 530399433 1250 530398183 530398201
    0x20a2709120c030203130f1806031e1103060a141003113d0f0207031112150c190c02210307020301020d0b24030f04060b091e10030506 59
    0x30b030745548207204980c0b821820786460322502c00d42e80c11031840c0000b200e5041210020095000c14800840801000840e1460342c956182203c01d4500d00c440c6a1800c0200e424085109071020039a640541910003500c0c0070900d000051019940c5e2061040b5810003054a0341921a00481565030dc40e81c601c1024040d00d00300034800c40000160f290242d141e140d10300c002c0c0392074255900c207031246071001c1c540d04070141d60140070307041d00b145910115400401c0400124440541030682401c0507265107420901c026031440c140003a068451409200307100a11030f041c0c2c00000206080510022a1071044107812802c40b1042480300c00a075025030010f410905004200f0038901c400c0350460308480c9080c41c16408242682c05c05c90308200066500c100c55a52414054585510b0300f06107440e1001c01e01c44c441c1d40b4003d50002424a9074640114030004041100d1640101c2a59100a014050502d0140c1955031741007000140c03900c0030f10500c004100341c680c805108000344c81c0d000014124070f555240036 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 530400683 1250 530399433 530399447
    0xd090327090b040603232e0209030a080708090906010801151d12150604050601020a060e030f030103060b012a0f1a0c13080313030605070c020a270912 66
    0x2d5a01c5039a0701c02c000001110080c0c020300b041224110000c103d154110070700e052a01c0007038104c1c090040d188280d2400209030300e84d408031500710140140c8807013042022038540b5198200c010520384000030a0801c0c8080d0001621740e801d001c0355200043c0d03882200454054101380300c5e20354030202c0d0003d0b61030554003c0c1e90301d0b03042509144480070902228400a8628041150141403a402002034540701840d40294141c2c4400192003d004e241001030000f55030300d0180c04003400440da1005242c41141c01171044a0403080e01c1c1261075102d5840e414960000c268061040c0d0104400c800001084041c5241809008800040420110f142501e80364044002c641c811500c0103070403a9100810046660303202e0042030f25010032912200c003000321008982140d005003040e548140071000503d43c0744840002902d90009020600780c985100590b03100310728190096000c21304030030102d105e000e001a1241541c601890354511144200c5040c003c80d462030001030316040d0b0742c0d0b20b09a002802070790 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 530401933 1250 530400683 530400701
    0x5040b03040f0f050d121b0f0507030e04060311030d080408041e03080d02030702150c0a030c2607030c0e030c01031830032d0e030d09032709 62
    0x43e244039400382544c455040286000b2070342c01046802d8010139a903d00b62080f41c1c1280c020038a00c1159200301c00019041c404400c0f040c401300100007440c0400c1510070030b82407501083c0030300240321203922407404031080d0a11129803402032059202404406104029040c02150082c0b40c1c0307498582400c0b0b41680c01100099080e200c0034801c0070000009201a00804900740200c03c01130b141c1c24041d800a043c4020503425480142d0b0f80c038180206608000c0c111071913803106003000215010041e00c00e5801501d80c03000d440702000c04c0703484038416140c1001e131180700e80311943e030070840d140036008140c50940c400903007a600741d4014801d204280d40260700c86584500d061401c403c0b0060966120f07950200c9d050300c500d040e004201070501da0380880e0381810000c0f000505051201d50001d000a805c03905109404800d400c6c928011040503048a5214100c110312030380580b030b0b450000c00810340250206820403000150841c010b500f0b07401da02c1c00d841918120410758a2a02c5181c0050b180107020060 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 530403183 1250 530401933 530401943
    0x3141005130b27090304150f03060b070b160c080d020f090a0b12070e1c0813030813080d300c020a02090a05090a0209090a0c06050c0d05040b03040f 65
    0x75039201481d907524903c44000700e0038001801942200c0c60251424010180c810284c41e4401d02c8180102c02000081103c3c0b0010341ca00000b0034240c0300e40c04c4003d01569400b8140d0640c0001c0c00b4006d00c09442c00e1144200314481050306d140c010b503c7c0c2141c000c8038160700078100b110107201c528040c10445d001402c0c0740140d5040b1500740601200010301c00d2030164072010f8894000a1a10300840d08005a2640292681400c3c00d0300244403001c90a40040402600144101d09800c0c1e010007580000355030400c5001c10781811440d459140c010040d6220010141002c0c413095800214002d002a402503400090780da15101ca600c103501c1302c4070b200d696490b80d070501115030440c00000760051041240c1007a140d8010b020904250040c07041801000c0e015040c1141020100500381c0380000e44a005181d040c1d0b01c220265550110b22400c004144500601b04821a480020600c4c0c0c040040c002d010340600554081c007050b080117403070a10413442034200301141440010045460b10344074104080c050 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 530404433 1250 530403183 530403191
    0x1203030914030301120302060f040c090f1b09031716030f0516060b041a150a0e0604030c030201020f03070b010b0d0b181005041a040e15090d0314100513 67
    0x5829030760550300244c0121007025059031803441807543c1004119001094030248201608250300d90300e251015a00440c190251140c02440c41c0e202c6075489548c40f002c41c0ea5207041c02c61100f0000400a07400f40c1700c29a00703d00b204548038500301c5201e0840e401d00449095000e034122084c0e6042d41c50045680c00c803014004140048007c426440740704c00589841040002080320030b400400c4201d40c402c24041c01c5c1e2400c001705a440e42e40307880c440801d0202541e42c4454454204080c1140c49500e4414282c0c1c0000006c41d002041150100c40c2c00f065074400d17000c0c0c40344000b2140199035039000344030300a0304c00e8103038200400c13241a48000038090a0b401c103101084200684000c02c0c4503440d261a0f031342c0010001e4041020500507103048001401041b101842100e400d0000c0c001c0360060441131910841e9105460044104100051048006040c80c1003810b890100c1400f911900c0c00007040d000319061140c61140801918203091041ca00310488060290034501400244d100d01e050f0004a0740da1 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 530405683 1250 530404433 530404463
    0x70e0a08100204030b1f0e0c04030c0314010608030a021903090509041101080601020d020c040209060702030703111305061c0510110301030c050621060d0b010801150e0112030309 78
    0x240245041d03201c030150096a01c1d4030310301d040764a138000101240900c0d6510f9404800000154811504844442880e0705903502c075101c110740940b145510003044a50000000400c10111310219076400b61103d00800400e42e80c0c1031416168804c81c0213140c010380080d02e030b640d0003485004103025800c0c06860034100250303d50006c20079001043e00c0507241c0000e85d12600700c01e585d0003403400381d100e0428409091014221035001e50390340e9888038031601c201d40103c0c0340030140d01e23000c0550711031507002400c03154090b50700e00703102d5503030304c100090140149540d1801d6450032003580180c41c080e43c406800c050804401c01402c4e040106428000c40d000d010392964600254228001c0c5110b140c3c008001c075980e5455450014010300c16980414040e030b509110568a04800a4110780340c8461110010060b0f5242c1001030119a51064024003c061a100120b1100740550000480d1503041c0c0504401c1c2d80c48076049804003a0074810314a8400441900000081c42508000b01c1113201c0c1c6031020404403 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 530406933 1250 530405683 530405699
    0x4170c100c021b060901140f0903070e0f061806060d0e010e07060e12030406050705071a0a12060f1703041203210c0e060f16030801080f15070e0a 64
    0x4180c00140c0164000282c242c0c0f440c50302d48403e6008281150100d01e48402040080c00302c98605103000040f03a0003088502c82c00f5110021215203800050a881c0d51a8a806041699000580b000c1010700403040c00555141001d00d05000c022108810803100d0b940c0710302c00c11036680d0009045280043d16140f4000e000c40e024021200301103040c80c094507006062980080c2880e1241d460b01d4440d04802298104042021003240e094500620307020b07503100300b84d081c5180341441903480301950300b203000c161a28203081e40c00a00340d441d103030f035842d464019007196170a000eaa01c21b004015060950080422185401d5035001c4800000c400541e42404d03540d995150a455002c841900800c00c00c112140002c50303509201c0b20125901d000c1040072004104000740300b5600c0142e514003c0900103042c0303102d420080103488031844031a615504008062600418090003842116114070a00c3e40182a565021500651061482c4a00860342d56840b600701c0e00c42c0c1c0b40700402c81e00302c1104800420a25 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 530408183 1250 530406933 530406941
    0xf150504080901141305152101060806010509012c1302070615080d0807120f0905010f0c120b0414130c090e0607110f1009170304170c10 60
    0xd4000c0e0300d110b4495105000241102d0440e50a480f1050313000c0101c0c00c03d4080c5d19000e003055400c2510100400d28078814280300c14420800a9003030400c4070305e00b00040308a00c0c0495410b079112a0341d1511940c90307050056405000d147c0d1418007149030720541a811403110a4001040559242890210401d1402050541d040d0034200003150703800286c46030230311900340628094445030300c0d402c14585240c1461203448811040e520020042007002007000180700c0c3c5a001032501d85413030b0412240450b6082c100003404000b8045450354244051071041c120184202ca80b28a115191400355030180701ca00002080c5210b219644076540381d2071021071448a00f001072040c02d1046103041003820500300b50b40741d146140d1050454604001c0781c081245008500543c00c4982800d140741e4078580f09111500f040c3c108140e042c051f11400e80048001c0c1030f60340220704d2103400307001c1c44201d035201000018901d110440b0f01510458a041100c0f007d61107200007080d0400b0b80f48161181c01e0b140c4114001a1 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 530409433 1250 530408183 530408191
    0xa112103130e010e0106030e1212040b01092f0f0f0a17060f120c09161e092d090504050d0905100507050f06040b04050709020f070f1505 60
    0x5035001054031805601101c0d0814060000c090100e610b80d0701d00074500950302c1050003141c0403d600c4101290150100700310801209500102c01500c070600100401c400050440f021396001c843d040c00001c42100071301c21503e03e03031101c50361042c641d81000240c0c450702050645000324000108444145507451601400001c4001c1120603614207513668020060340804445246030581c010610106582c0e0942e501c1a5403819612080003e0321110b1513418000b1001e442600081c5080821584440c204445084201b464031135900c11280741040040d000380d100150707408101e90080c00e0040a050710b036409510076001d0350035045c10a1b45454840154002e90150300c40075296828441005030601490f00714050178904528042d14240000da080a48503145100f0f0100000d4400c06200b000d02250014085a40c00c0710003a0800d0300d481101c0c03a000f01c5095030070380034240000c601c00800e4021650803105030365250307003072440300c0c0c0700e40380710900c00803040303c0d00440d50740300a46004c0315000300343c82 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 530410683 1250 530409433 530409499
    0x180d020301021201151d1e0405010e070f05160f0212030a030213050910030308100f03051605153403021b0301020405130b0312070605011406040303020a11 68
    0x3c5514000450b1089244148007609100303110249506510080016034040d40080792003910004500c10700d0130030900c0d0824165001401c0c1000400c014840d20880b038000e41c200e6448081040007510203c40c54001d0344400c4241d40100032a480c00f02c1c5040000020003400100a050100d5407001c0c024610b501c40212070020903004a104001070140300a0140145000c2e2600c03101c0c4d1410030190038840e00c035804020188110170003c01d8049820b403501901038151140e1880c106a140d060440d40e503403500b140b2652051002c1c02c0801d46042500400c01d68007a40c0c1c40407824480705032920380044451a158540300b04008040c1017a05421241901015000350087d1112800c03061540340003203008944035003e03a0040204102c69103e141203854070300760202c4001204404407000070b0415840300440c0050601c08900d40d400d100c02c951003076049601580083c2e4171071b00c07540244179040c020780c4000b0300983c005106401c0880c1d011190b0070300c4458010080000a204075070005043c07540e01100c1c0b20 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 530411933 1250 530410683 530410717
    0xe150c0f07110114030705030a090303020408070b090a0f0f060c1104110a030c02070506090f040b060a18061b08030402030703051006090605041b2a0f0b0714180d02030102 75
    0x150b5507004200c10008076142c44006183d85403910001d089032202400001071107035201070407028148242e0540b4003401820082da1212560342c0034035401e58220703000c40c80c80b854114200003540300c0881e072800c1c03c40e03900c0c51040c2e684510f408803d561003d5a00f5065800c030101042d086099682c0e441103107030200407032514030348604c000c9100900b240c850403050710075540401e4041c04260b0340c0800391810000e00310f905000c2d1a09200216010f85009540c080d0000404034040b2411038001200079880c628078120b1242940e5a26002c0b076030829030700395080003071500c90b43c100e0200d501e510003180d003d40081c040780c044582e603954403407606801d29142c0044940d582001e104050103801070310b000f07020407907050203540c080050704840c00305010602d4061240c0f080c41001a01c01d004101c0000c4148800000650f44e4603040c407140710381031108121884031425000412080c001e00520598010901c1014200050f240c5030040c0220f00c82ca43d141e0088040300c1000041e0f40900003020442c0505010380 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 530413183 1250 530411933 530411963
    0x1805100801090b0d05280b0f0717070f12200904180c050622030809100309030c02060d0b03060a1401080f2e09031d01030e150c0f07 58
    0x2412203c1c45840350f4891801d40614601081d00000c5c01d816003540124141c250f602038203001c00c8404440750008042005940400c0f45c3c20701d041d070809220f20301075110b0f0500140b04481007040302c0c0702214004d01144012007081d001d035100d503041441110030300e50001484910058014441c50307864420b0049000009640b41e110b00301402945140075070380024261a940d1603031340108200060240d14010300300400c010f2490340b1008200324141c18000a9a00c00b25101e003090500b690140c40114010804240404c0d43c240c03092007040c180d19095903401031805029820020035a02580f401e201050311000c18107650750701880030038001e0700d5242d000074854459540104036890164445130090700400ca40c1682c402010403014070200003d255421030031400c107241c00c1608101d181100b140c0d0300e4130141d0020142c0001628030000c021184490410319008011015520724044656942d0040c54903101e80c59040301c62107420a0780024040e04000ca0300046c40b0303440c2c20400099a119403409010 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 530414433 1250 530413183 530413199
    0xa030c0905060333060f03090a0210080f01060809101508120304050d0e010815190b030a0e03040609030b0411061201030b010603050f01060c030905120d030b0d121805100801 76
    0x2c0040c1344003283c0c03280c081c0c100e800005803042c010301442c0080d4080000008656039014007001024a030f00030060582c40311100d100511550301202c5100e40f43e0300c42c0c000070654900401081d445200204020320101406070055006480c10f8401e44902001d81d030000b080105041c00343e000c1440000403072584a140500700a450681c482d82490107000c82001c88084c0d070b07640000700310741c09240148404448894180400c2e0650025060105190011030022500b41a4040254054002c041c028010f00442d8495951684903500c40c02011865002c07003000020302116a0a602c94010900c24040d0a088008141c5550090100507401d078a040014401c00c40405003075409042c4503e02001341e4509140740403650003040c050441401030822844080602c2038420310080c0602a00180302c202c2c40c13820103540c0d0360141801c0c40100e410070301c2c0c0903468100325503075030304868004690b0140e4040001c4184c8085400d10300c1c100d15085c00b4500410390f41c80700080b111072107003555507250b807941c506285 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 530415683 1250 530414433 530414491
    0xb0a11160f060e1b0a09050606030606070507210203011a01020c011404120f03080c0310050d0f14010f0b0904050703030819020c2d070605180405090d02060c0a02030a030c09050603 79
    0x1106c07104510f000b0030322a29031941002e9a034404015074040740c0e11091400c1c079502e001e20a601150032184840b401c0300d24103a9958500060301d04c2940240315825200070440084140e141055006920000e00880550320503040c403202004000f5880d49096280c655901000260010035114041d90341084402c02d0780c0001200c1e03001d8501782d41c5a0450414460b0703111510514862207102e11404a0f41000303000c560401c082807207a00100c1e4846030303019112451302070072000d007071001c200741b03800d10004003800c1c030b202c1d8a44115805005410b015040d0f540135074412a001e4170f1260020405d400068440b19140700030003d008800006152a00c1100070040820707025049000007020701c403c0d00f500030b020008040c070030b50b0352605010303850760381c4c645541070404c1c00b01c05501d904c1414102030001040e00070901044a031503e07429102da590b9081b04000c0188541100000180d00410000540c0c610990080c1ca16550b549802c0b0111541c40e00080d8403600145c0c0d10009804031100c0d00c0b442d82c540307500 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 530416933 1250 530415683 530415689
    0x5030405030f03120105040b040209210f0a0302030306062101170601060905060d240902190f0903060e0705090c0c010501090b010906081902070b0a11160f060e1b0a 72
    0xc616113032042c20640301d0004184151400741c0c1d00d070b107013804069840b901a980c4048002d01800072211800c41c0000000782d0360105c119090284200d642c1c9180408240841c00b660150015440e58079004180421a8030540304911070314102d040d003540e03480105502900030616000082588180e511909044c21810b85c814014000c400c04104a183c840e203080e11507000842c03a0015030105108404441d10041d030b05004448166030001060102403079000c0e1108103000040d5000316041480143c42c0c040c0e40c11040f5010440e280c20410001e0a19002200c101419030207464401d0750760404151155000d5404c030031401004640c2d190080d4091007500d0041001d41c4040c00800c401c1e000203403031803800380141c0c0c080051203070001d8600750781c600c410645450000c41c02c540ea0481402c2c00301c6100000e40e4010304407818425061070001448055603800c81c4107240d4802007400507500c884140c50044070840d0041c1d21031409251a507820701c5185039055050000c83c031002c0c507400c108400c0d041c1c150 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 530418183 1250 530416933 530416963
    0x80d0f05010e0a050a1401080f0601090c0503041b080d0e09072102090102031c020a08011d0f0910050a0501051903210207080a030309030314090a06021602030a0503040503 75
    0x2a0040002c2c620070341400b07420003003540c000940b940360312461101800c1030011045810a80000000c1c2407030b00011074545c0c9140c42000c1d01c20907601c460a003000d0364071914800c0b00280040c0045030100d62800402c2d40703210f1184001143c0c0079510f076403080c2410f00d81c00703104002c41d031194022800d074189022070a40c444c07240c6c6401100000d00b148038031004000c10488010b09070380842e82800c164020022200303160300303003801e01840002e4003001c04040d61002c010103000a030104000a10140400043d00d6400b0b4007420701d285035a120410150941c0c80206447d44901c54070b41400f03941501c078815907002d03107000301001c1a00c0d03042c4800c2c062042d8290848280c400300b0500308102080c2c803c19058002091640088241c0491000481c5090030030313000058203005003400341c0101070f09039103c01401c078032a4a052002400d010901035120340c0071905410325800000c000c0d40000c40320780c01480142c03c0018131804890300b5401091802032510000c58a560000406011628040041c01c20781c503020 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 530419433 1250 530418183 530418191
    0xb04050108013e070503030702010b0613061d040e06090c011d040c051b01140c040501020d030b01050f0f0423100f030f02030c03040c0b031e090a0f080d0f 68
    0xc43e041d00b0076405200109a006503803604071000c412005100202000c1c500c40310107444079641c2c00d1442d181d80c0f05480401c007540c41c148903824241800c0041d40d4000548050440403d450100c05a510701c0740304101c2c1c2c10038103000640e2050b0b551548151050001c5900003850705140c000c00c0f003480d1a038041905418000e88034a5031954001d4590701d8801c404003a03501048000004101761101e000d01102d07644000307030200c100641c03143e0540c00124154124811400b45845601001c501c034401c034000d0500580125032452a100d01035000b241070103030b040c50014900758a4140d0907007a03230003600100481080024017007003030103c035070007860300e84100c80031401c003030031540340011040c01c1030300310030010310025070011112a4043c1d404480028000d103015981c900e044428105650b000302e0707084822440014011500850f440143d0f442940c0f43c03d000e0f07016840b001180082c11100a008240f5031240420032000201c0703141c820000103100300c4080e078580801485400540b00b41001040104c0d241c = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 530420683 1250 530419433 530419451
    0xb0103110405060913050f0426040e090a0c060f080c12042604170607031e0b121b180c09010c0f021002060105010210140c0c070f090b0405010801 64
    0xc0421501255811a0b02656a04901c0d011a90030702041041d44412440c05003041404d02c120001785104a104204a50a2201010001e074800b001c40041c1e160318241888180000c82450307030810307044580c070746c200c6030600300e16610010b0424503034000400145c4a0307400c0e0302405030400341035a002102d80e59210700380300c40f0171a082c0c030364000108003411803010308035021128403c0d40492104500310311115544d643e00d40c280c00c0040c00a18211681600c0744400203207443c2e210b817141c007011490a0b510011446403900d00c51000e464901249948041d0303103028051440f00401c12060205200c80c0085030b82c0f03184008000e13115400c0200302c0c0e08016408100904402524200d540c03114090a0042030100305082c1420502c803001d000a401030188000600d1a80d00050014102c5009900321002661040e9800d010385121000034400340e038440c004504410b08003406402c1d001c581801f00c43c1099a110503c10601e561a4051500ba07650b0341300e01c800b98102402100d001d4000c0c00000d005480c0 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 530421933 1250 530420683 530420711
    0xb0403020d060216080408010204050f0402090d0605181005060102010612030c030807090b1201090513350a0503160507020904020d06022106041815020a050904090f060b0103 76
    0xc0e00382802000940d00003034804e1100c1c0c103400544031641d0840350042d01d81d903d8081c114000e41c0503005240c82800000403188061526000300c1d00c600d4800381c8803500b541a0341e590507002d400064401820388010455030344a0000c1040400408000e912000c81c442c1010000642141d031550080e5406514551400e00842d805c142000034613030385131170203442d56610003804890300ca4094100c45060040052038003030300ea8203140068107840c41d0010400c0303182c94280f0095074011800c40010b002d100d82c100c203100301d42842d440d6201710001400040d024081c186000210f40c0e84041c00355008100044180700c140300480c030b881850324101c0e013001445d100198000803036064004100a2103510183c00320070030014543c05564a00d06040420400c040005035140d003854002c558050045144c1480740e00b07003100040003001d070071750012000c044000d941107950010703500200a42c010b02c5001c00c81741c4c0854845d44a8400e45501460701403026030b0031460f004003a17403440389035241010b00b00810b401800f0 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 530423183 1250 530421933 530421949
    0x1050411041a030601030603020d060e06060910030221010603050f0c0603040b0a020703030609020c030703080903071110111204050103150602061302040b03010507030204030b07030501030807030c030c14160b040302 94
    0x40700ba100390944075aa0280120301410f41717600006d421100b4401403108000c95904a0510050030308141c40759552800c040c404121000c40b0100f241d203502000030800b604007405001c1d02295850110f140c0352a1008059003540c50aa10446040c0e01181005214900c140320718400301c0b400b01d450f607145041603216260742d608090005046554002005820903006c1c0d8003500081020030b46c255120b010400510b51260803000040e808601640001560321002004a03910154484402504002e83c0f60a0008038190f008000d0148010003100c507003080720400404501441d403082c01030b51641098001030544180d414200c4500c405480c1c00c2c0115900842e00e1984001080d90a52440c0c03080d00000d005446502d031415055440d0030180414182e0580052081c2d03805010140700d1078603140403c40071585c0c2480003600751507017407000c100000e1140a688040600030301e480380701e2401c82d454096016412240512040d80900600c0d030140c00c6a0120384000c0c0b01940655041520716000706802c0 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 530424433 1250 530423183 530423219
    0x9030f110a0221070602070e040803180a06020711060315010e13110301050f0d03090302060d09051c12091502030a02120c04031a01051e150a080105041104 68
    0x300088a040d018851001c100d1a405190000c0034184803c801c1000350f1000c550000c0c1c01e00a90192400c00b040a500015860084408039113410011740d5072901e40c3d90840d00301511294000440d40c0b650152004200910f20070280a410010784d20541c4d85400850b2042155a0300d02480050080140c0400d204c03681c0c141e910401c0c00c144054140c1c4900103888111001c036240c2c00c04c0e161441d54510007040001031410703108140c4800700c0340d40c1450300700004a114014000c00040c0164001e0005091000c050008213000c904013184c5c00e20030386e80d09410325200341d4404600550540c161240c0590040e4042e60202ca000010400300c41542c07550743c1c912003400c40415210707400202207950b180855048070f5030009190302d070100300e00b0440803015042e441480f01b40e411945050446461080191616049480c02401c080d1400c548011020365440c1c60844582e001410a0040c004000001c00812542d4050742d6280c2441d070500d4200b01c200c890190201070711460511080c040800c86103450001c07 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 530425683 1250 530424433 530424437
    0x6040e06150621040c30170a0e09010b0310090e190c0e090105160c030e0901060c02030105011517041b0308180f0109060c020402090405090d1209030f 66
    0x4882020740442c1e698440c0503000c090180c064181403440840005495010b50710400000103100d0f510201c0e0315031341607440000e6440240e440b0314041651116409885120b00c00e407541c10001200303000824068101014200200740d1603c5216211702d40580498003411081003000e0640c20201860040c111007801350700b07030b03a5a8420348001d0000003040303001c0342200b030500f001134580f113185400441c104080c462140c1441302a03011511020060044900c100600c5030080390303181c0b041e4411290f05104000941c10700c420520880410703196416124084c01494480c0c907080d48084c4181421a041607003e002c545400003c0300001c0d82c1d020488400050f01003801826941b500c1c105603892043e60f0500b140c60b0084204000100004080a0120701c602c000d038481761074840302c040c40183c0350301c40c0740680040c500c0e550a002541c0036108081c40c0c940040d000500f4080f149000c00c2c1110b20130346850505900c034000c1000e80c0740c0c0c8104010081c1d881e00d0801d005080c09030b0785c040d1030f0010622903081 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 530426933 1250 530425683 530425711
    0x240303050f1810022a030604030c060e010c0f11060408030c131d04060c112e020309070f0f060507021309050a0b0402040c09052b081c0506040e06 64
    0x4440d42c1c88103035802c10020300070b48640442c184069a100301e03005843e0011030100d146080c03860f1010803203200000c0003601900c4541c0c4c8a68089034580c9910741c3c00c44002d0b0343c42d98003030042c0d1000d102d0300010030069110381400e5240807402038030f185403490905010b030384400b0400c1300241c03224080e250883d1640103456221003225152007602c000c0c54006000c0c00f00444608006441c0f041480b6004d64010b01c0104180d256118040320803c1d005143c09040f0303402080c4040d05241c0e41101d404038501104001201c81c058540501e047e80c0c0705954068595000c0a018001c02039081c0c1800010110514210740c1b0714a4044081d040d809081000f91041e81a00780760080c3d0740c40c6070048200e00743d00c0419541e1070b004901d01760501c00003d4a0903806146071800d16008540181c0f88002590802003600f4691010b54200015184210903250010214001d130030380003c0304c80c8080c200f0044008005001c0c9420b511a03281201d40040a2038491401e060140c404050301140c4c0c1c3d83c120844aa4000b = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 530428183 1250 530426933 530426947
    0x10e1612030e13180606050117010b0315040e010603080306040c05030108072102090708090d0503090307022403010e071206060f0806010201110c03091305090601170c03030301030303240303050f 85
    0x4020309544d82c6400d2014081514841006866070285064036400d88070300e05202840b030760007201680309005011441c2c0b003c0001c0750000941d218640703000e100091012805d110900046800d44500780c0c81100c5102021042c42000d24160007106420070b41854464195850325103c19641c614510036600c01c0c50355540c0745d42c007804005030000c98650700a04154418200210010075840c01112481000d0050300b00d850405880303501100c3c0219070600080d0304040507902000243c0b650712144003c4405002c6401c0205400800a103008107803140a50009240400c1c2c041c03c10b00c01e1404017942d43c1e140000c01d12044ea04103c208070180002e00e000000ca541d80300c0144e00416a91490300703407411003c6000c03481140c00000401c01d0309070030340301c0360000c10b0820341c0c480541d42c06860440e0350b0b07005640180449140311039800740c001c1511007140d4804591102003801c41c0d100781c005038000f03a161070b0001c0032200030003030110b8400317400a010403070b0078a10707100181540642d0b0340d1031590460000c1c0072 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 530429433 1250 530428183 530428219
    0x20a080112290a0b03070b091207090e0102071208090703061d01060305010e0708070e0c090a2403110c1203060402091c050607050f091011010e1612030e 67
    0x101d08a4040e420070b081440c1074600c25100101021100c01e030059051a90402842c01d011604070100d5202a1165040142400c10090164070300a0a00d070b86220703018000501c9942402804280d06100c0001a0760314000d00341090910760350258041485070340401d00c2101307040000c8a104a9130012400903007605103a4000c4041005034220712110340c24143c01000380030041d0302c84445540c03424101c0c0c104540c1d54030030f16111141880b4070020148044001200c5800b480000c0050362402032081d91019110510410b07110046102100c0c294550300710640e10701e40620400300601ca1000f400f50510034100c41881d03584403800f43c4c501031a14040085100340d1035640540780f41c88401803444c418591740504a02e050ba19503403081e91103105000124100c64060400c548440603003a4045260030480070500041c116652400700c00c100758034101403082c2000f07100d9400851244405403100c458140015140c40c0800c5d0048004160f100202c4800640c00c0007072004003100c10b69030b21000f1000a040 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 530430683 1250 530429433 530429453
    0x4030507021012050114060306100e0a090608011a03060411010e060a18050901080322030605010b071203022d2a060a180213151d0a020a080112 63
    0x2000350010b00d210800c021141e08140c0c00c07500c034143c03050100b00c00c0e80d0b51038242090704404070880340c1103c020400301d00c80d801c114000b15600c6005040c500b020b092010003060102e019588410141542c0da1001d0100e104207000d10072084084580f00000d0804400009440b004080c0c4024082c001e914200d044a07405071038a2004054010002d6803201d0311a90054041850030404401e581d19060b404905807400e0a007282c165403081d001541480303112030454190300c40c16003040d9907080d0b441e0400000281c2501501c3d01a11505400302d40310502440c0941d0700b108010326103c02e1500601084255482c41a084c2485010072049403500c54441d421900451042c2e860041515011507c01c2c003114a0b8402d0a0b4007812228084504640c0e66040ca0411650301d41500040403c0c8900280d000d89080c8070080e100b8450400002210000a00118001000d59005081511101c2c016204c00d43c0100c012a40c01012040c00750300d051185c040c0100001414040c4544180e42d403a0907800303000e1080f0b9 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 530431933 1250 530430683 530430697
    0x30e07051020030a0f1e091a1e040315050118090c0812040303090f0e0a0e030d06030309050301181223030103110f030d020705010818010212061c0506040b040305 71
    0x103881da01c00e00c0e42c0001301040b58200c448408190548451000704d0001d504401011b81c4a03a0f1ba41400c9081080b14071040c40703209010704a1840a0240c5020110620112801c9203818110710303603507d02e14502111020811300300c0d045403e2800c4010886d10281500a07440c0505105c00083c0b59035040c545101d80020136041840c0358403c2c3e44074250480d00c0e280040041e03900a4595810881c4e40e17100102d07404c5018010b45d0304044a00c0c002c00c004001c150000c0100e81c0c80031050302d0910030b441100700c0480d5503035841130300000e02c00c001c10440c0382001e104014803a40d0301842c1c10a8032095884840380d8500a0901004000305080d15032010002c0008404561349403031001e80e52542d4030b050100000000e01141ca100341c0f681003954600f0701d80051141010000c54003d082101e16040042d210482d00415140303841e00d0301600540154020720050407a404900d5a803210f500b042014800041c03009030540c600644950702660104000040440d0300590200f6080b100b540c951404842c00d02400f2 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 530433183 1250 530431933 530431997
    0x26060306042a0f03021206041536031103090303090f030102040302060c030d18020913240e1209010801091503120e01110606010c0308102103030e070510 67
    0x401c000c0384861404990f04101ca0084800301141208040c045455400c255401410007c020f40b0044500d55560006040f4040d00d0340074040c44604082080b98481600021504c0c18201d20384442c101074200b07002505a40ca090000d50401d904200407907924819030078881e210342d040079510151581d094048802030340d4046e041c5078039900c11000b19030340c03a041000c1c1c0d00e030003906001c9501c81d400529000304940f60740040c0010603d032a0403a0003855114940c1d4151980040b0f25240c4020b240010840c242440c2d40d258005190901c8800c0a420040301007016010110208254901680d1200105040d60f0f00000c00050100c582a03071210104200da02c0201280740350b011031032201d6001740002c49000310a0b01c520700e001840d03243c0c254071080c040340e255000c50107540e540c0300030a00c00c2606542c0215400006100c00e5150100074134682c0006000980000d50100c0712010542c0c9801408110202000204882420304000900714030b01e0080071030820592500b800c52420044402c0285540d0300 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 530434433 1250 530433183 530433263
    0x2150709050604032316170d0e06030714030712150605070b07030603060615021006030203030f2a0105160302030906011503020d061503141e09100c2606030604 70
    0x43c0040340301403006100307d8014140003003440031500c0020490302804011950754420040825080007520b400282c1a0f00030031010415035032001e51b50b40010b50060301103468880380f4000328001c1000f40c904140220b03102001c0d1802c05c0160540020640d54441d41c80308211240340d0324288201c004024940c40600450301b401e02c001502c084081c0840b0303242d40c083c1c0c00d07198030410303040c048415107215200007505540304012140c007150500303015210032080800401803c0a424440040c050010022350000d650b41f00b06000d10b40d5012000c042c0000303d1801d007503042d440c000b840320ba00e5200502c201d240c5804160100b805182c171950445003480c1940504000640e2140018104412440310b01c0f40440d142480ca549000450a480d0b1300c69041c10061505954048a0981d80000040c16200443c17146a50a4003100194090010100072566070310070303890b495240c034103900d1380c41c1c00c0007850307490030038003400f0b020388010441c240d200307402c01d1152200e0790301011301840d9000030300c1e03c280b0f090103d = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 530435683 1250 530434433 530434453
    0x6060c0b0c1e0d05070f02010b0f060f130914060d0b04110f040c02010e01150b0f0a031d010b03011118010e0a090c2607050403150207020405010303021507090506040323 74
    0xf0355021901800c0350390b68049004840030416800c0740c4558002e10b03884035030b040c4594034a241a038010f00c40d030000103a1150422181c8812500001000e03000440000d0722200240400c00d29940c1040e40f1090455443d1000340054484c0d901e0680c0c00780010b010490b0001c04a19143c8030141c07940d0b02c005001d441045030169003c07000b402090175140540c155400c0c0528032140b03441969480e01926000d40342d4900d03090149844014640c0329500400516498030054440104d0107480440307a41ea00d40b00220b08152030804041c21110341c0d04207196007220034460f41c1100c1084820103039050b0000c0c2040400c07544030000040f4601a00d0b848100e0a5051203001d84005c1c3c0d01c24104028080b9084c3e45848038081d13183d00d112030000850314940001c00502c41040802d04d003195448140c42c00c28001490034060340c002c117040d03547c02d070015030159100d40303680c0b00d00d0340f003810308139030b000d02c5030700e042400385050500185c0d842c4100d100290205a0540d41d0b00c1041c400c4103603400c40d41521008032070103101 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 530436933 1250 530435683 530435707
    0x24070e090c0309010c110d05130506072a030b07030c02010b120a0510050c190c0602031005010806180601110309040e0a020102070803040f03030f0315030b060406060c0b0c1e 76
    0x8400c0b114103d103542040e01141c2c81c5800303007a100f0101400c29015151619000704202c6060708402409207a041c421030300000d040c0c4688004003402d5000d603c0444c05140506050072412080703802e00c0c0b122842c1100204041a551070700560882c040d854042600300030700f24101d01510481d40e8641d80025030f0700c00d0007980321001030440314a511580981d160051130050b104102c5008841b1001c0b102c100704a8182508112144075482416909180e606a512070300d82c207007282c0046070030807035402d0f8007403050080f5a004030300b50358032401c2201c02d002d0500035003d078420650809080307141402003c40c600c0302d0f404000d106491821b500038104110044840720f54079541c03440140140d0150055030307000b0070141804000c41d0180d41d40b890168501c140b640d1340460304e0540b125820f004140d40d0b202c03044100c1000c03020140040d030150f4000111030400404100885104e64030400c24045a050b500c40041d91f20440d29a000d44407121240d11140303040c0512002544a02240c1440a000240e94004103 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 530438183 1250 530436933 530436937
    0x11b15050106031802030a0303050903130605250c090b0a03020d1a180a0b04060f0f051009020703090b0c0a0209070305040b01050f011b11100c02030f24070e090c 71
    0x980940c3d001c1c070000c03841c440240c4200f0f020100103901500031181d0701002c40d000e50412034000c1c0404048900d402412440c92252240c0ba0700030b03c1c001400001c84002d1070091180042160070900310300c000620709030741c5a081040f114898011a40d480c2c6454105030382e03c400c0044000c680103800c000800c000b6140802c000c4408142803051814030390003089250310303019650050100040c0081c4542c1c03415440d94150740b0001042115a1130f280c42403d0780b0412a80034000710610400d4000c1101d0800d80c288e10703100d40450700b12035004c41c0305201080110754858240b00031900800c00c10b47d515850760010509103d00c8a174040c0d00080003c043c0252994503070300c41840745000c2c1602888603605d80040000c0007400142d12400142c0c1c1805c4150b00d600256840900148a07000f80c1906c101c1d0140419a0030342c0207200f210101e171a0441c4030f000d606041c07211080c410003400c003521108091548411424660401100c0300500351000104594000c4624050703c80c0f00800840ba1380c41c114405400a07 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 530439433 1250 530438183 530438189
    0x7050f040e01080d031404080d020d020406200f070b1804050c031b09130b120708070e0f060901030f03020316060603140a03020303060f01230c0d020304050f011b150501 74
    0x138410400c00e100c480c1e01c28807980484040101030f5060a0300c0720380340e0030a907410072038030302c20610703400c1086107140402d030320040000300442d4550b0780003c001001241e43d1031400300300300451900f01c0c1c0904481c2500204600c2c0c252600c8608050310740030b140b241c1c2041e44051481c40b5421a01d00818400036151200c09148074600360028044440703070458501c50b09000c0c05001c5504503072885030b403600e80011500201102e110241022440d8803209035618a492110b03400348001d43c1007054244412820f0200e000c4e17116a440488100c10301705107010641e4488140710180480081e90060300415109100b15072000314040e50700b489409183c10260018075030f0344401c40303110700034428022100b80040b81c02014541c05070060b508656912045c80003a5480003109030401048903001d0001c08a4030700da080c468801a95403a44840341070620926000044402e0070a41d4401c0c8001c0009989051004038222020310b002c0c2040c14410103c0802c1246a01008120402c0e51211807490a1603600050407 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 530440683 1250 530439433 530439449
    0x803090c03070f211a01180b0109150c021203030f1005042d0b0301061520030415051204030e0a0f120609110915010306060503010806040b07050f040e01 67
    0x4295442006003280b000703074130a07008402c0340404643c6000625007031482040e4054904508060000f001400c1d500030309030004541c88007410601c0766200014400c03814400b60a007001c1e5a241c4c284005009850ba00d10026000c115a040a81085484031601b200d069840c01080300c1e160304141612070100e140031620200441400d04c0300003020b20b89406607400e120a80000b01c1c2d03410b40f002c003102e00c20202d290310400e1441d4403400e40c003401d51403d21440c801404002d050400c0b000325401c0080080100709840900701403940c04c0c0500c46c1001000325002c44014090b50a070a44e40c2440656207130150000350240307541010308000c1071540040c40d61b1080042190f00d865840d03220215280e010030103001d881d400c465a030110701e0000c0c4071540010140b0f8000c3e0b807010808209100010540401102e2000d0560010a038119140d42c141c02110702404480c00c010b400c66041103619942d600c0700034405072402d01a50301252651f4001c1e0b04035a01c6049200007241d54640b02c424110064034280b1503161 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 530441933 1250 530440683 530440693
    0xd140a0b19022506110d0501090f0b150c0a06091a18030d09140303040305040e011401050901050a171807170c062115043e070803090c03 60
    0x81038190718400c54821040001c2011041203080c0c41080f1840c40c1c080003254002c1d51980740b281607400040252060b0505080081001c2d810f1040280982c1ca0010070402d8040c02c0605d070b000a992000415140000d403189002d441c2c1c24020b900501e003410b070f100b0240c0418902080041808002c046608403065918002c0e411a214050451060440d003410410b964105001410b1482410b030060090140104c0e2690b2a14a140071064110750040c0c1d0b0440115000140c1044005420300c002801007800185806401c808000003924511860454a041210001e540c024150080713841d10700c0c3e01c1405141480174500074469024034075800100104038071130080009076030341003038400e4101485040c0140aa22100406100c8036400c4030300c0a6210760604510758100e5185501118442d0b00a43ca1203800e0340015414001100d840d4481600c0580f0440540c2c3c648400c04000030050340703c2403565000d24001c1040b00300507405210b400400d00d0a00000b4851040d400144075140700d0344c00c5064074 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 530443183 1250 530441933 530441971
    0x20403060228021c09031a0613020306030a02090a0213030303051e010305070306020a021203040302070311010806011d010c02030102070c060908060708160306030203010c02010c08060117060d140a0b 87
    0x103404260701e141442c0181d02c02135001d80707100c8900100c01180780c090b04000c1000341d20395407616480c0c00340800480d14030300042c04114007440e082d0012340c5050a201011446c508101002c207031242002200a80500c100b03402183e40d40c0c600d13504450740c0030200c04c00d001c4d850f501d034600107000c0c040603103456280f43da50f0310541e0b1046410b01d1107641286c0d4060028002e881c5550b540801a400142484044d4003914000c0e45007002040c0c015485248a9405001c1450661401306120001c4100042c1046450020040c0c0e59800c0008100c19a15940b03900d01c912440000480c0d0141116400940650003ca028402c00071071400440a0710003035240c0b280441e03181d0220580d0b0f0741044844000250f60742c1d010171002c40c0c42d000d45c07000350340030703440c02050840d12500801c4c06d4800d080d03803810051b1b564890030400c41d540040000c0c0c00480920389424064141d01690a400c10090411442a000c5248840c10003201054044601d0015000d03200f00115506140380303070000840d001d040d01c01c4520280 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 530444433 1250 530443183 530443237
    0x601120903031409191209080d050703020d0801080c01030e030c0102070f060506010809030a121119080f060d140109021f0f080f07030902012f010e0c1f03020702040204030602 77
    0x1000f81c075030b081d104d00c00805401e6261b5800800d0b000070035a062004200000c2600740060040082480180d1101c0d544ca02d40e40c80c0003482c01c0811200c400400086a005008118011a4414000c442440c000c541100d480003114258440d2160801d81988001200f404000001c2042486c0d0790141c0c00402203603841800542c0c00060440701d0131800d800800001403040d001d15140000300600e46000100036000302016801503004074092840b01d9a0040203c500350740c0100002d5100707a11800c00803c3d41490f10100710807004030400140640c041481c0b5250b105000d41c0050801600280b5160303581c2001442d0a80d187c0468030340340001000301c580185090b008814050003540090030050b001c0d0343d034060072030042a00d410700b01e04004400d00c0480c444140c0c4000300c00052020020312103421884140103007146c000c400e5545040c0c208600d0780717581c2d650f00f01292400201c4084001d01e03080141034100d00a11842500946c018400702c1d0100070b00c10640e0140c00c020403a9040346002000c81240 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 530445683 1250 530444433 530444443
    0x5040f06030b070c110d06090506090705150c1504030903020306010b04050a09020a0201140405010209011b0c09020319090c0e010b0315060a110319090605040e06090601120903031409 80
    0x41c290500480203c0c0c2c4070751103106910f0002c0e00441c0302228691001300001d0505813452815584070742c60b11152010b200e42844410b42000c01ca80041540625010110f00c03250103450301c4485400e80400c1500d00203400f403011207100b1865411001081c81c01d0320f00a0007404490200340d000c0c0c800c0e00d0000c58a10445011103003500c4001788440c11440c5080d5000000c1d5002c40041401c65480b012421044528009400d00851043c0c1c005610b804106000520b400340c072080d000040d540088400020900c0c004803481982da62803c0960359a8a804040107004440d0112440d0f0f94079000e208018040700003902401d03100c03071003184c00c85031366105000c60780b0b0300040d18409070421102411a0203403400c1c000400d29540c4504012030100795102c0124150341242d492403403c0e100300350b068000c032a446032003030020300301504040d414103042450100d02d059005041d90300940301c2c0c00114070127038052421203840c803156035418000b80d00c0b1442c0c020701401d41a13405044581056021406103440843d17 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 530446933 1250 530445683 530445689
    0x1b16081209040b061204060905061006050706050901060e04030207060f0806061822090c0503011104030b280b0f01110d12020c01020a0804110303120112060f021305040f06 75
    0xc682480141420040208500d42e10a0f0740030608001c1032244031120240207100d1405000300140c810500e046c61410180300a10b08801545045000c0c0071094101d030942c1c0c7d1054014000240d2590b500e9901d0b40100b6070380d002001190f0201080104041d4000f07800300130b44d030300350740c510b40e41480440081c0d07000542034510651000052014a039180c090410b001c0161500608401c04600039564000100d4030820f01d5a01c1e80e0b8846180105119a21071800c0c01840d00342c0c0200841e1041c440010780900890100805410180002c941000c8520303a0300201c0c4014103140a840044080c0048000d10200c0c040e41c0c05030800143e800780da58011500320000c84000f10107004d86900902049986400706030704c281c0880d41c00d03c0b441616040910280c5026035054603201040d06150070007140100340705015500c07da00c204a040618040105001c1c11501802200c200c100f5445c9407084c05080528510111544007003561400384c24000c1420b0211001603c08001e150700d007107001c40035141140 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 530448183 1250 530446933 530446963
    0x1810060c02010503071d150706050c0301030f02090c0d0f09020f010c0804170a0807050619091101030f092f030a0b070c0317010b1201080a03020d12021b1608 69
    0x840000d0100c0e00404c80000204540000031b806c1d414900700140042c41011b0a4100b4800c0124848041041134480d054010020907085400d540c5541d41d444141380310014024012100c0d44042041050a1002e07103602c16114403080c4620105000c001d8024220b9003016032140044620340c0384154002d000813460144c10542051500d42444841c4804ca0b18440020409216142200c0c021401807009400024400c0000c0c00c69800c10705490542048001541d0704150f00d03000d5964002014a43c116504003420b09000c2403091200300d11800400200d24041d00c0f030080300702000b0042c40d40060043c00c00c1c0d0320031240c86030681c100090551741c03004c40f60300500d40c4401001140116000740745c0e424107148a49001110b41c4101607540480c103000ba888002014808207000340b00c6050107031050f0140c1071507401041c2e82101600e0080d40c500c545004170b01440001e00c02c070491408103030100c0d418a135202c400c03138103040742012105503108004110022815040080420341c040041155103c0c25425 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 530449433 1250 530448183 530448187
    0x303200a08150d020303070602030a063003090e0906011809050705041a060c030408101a012a080403110420030c1c0f0c0302040b071e021810060c020105 67
    0x154003041e40b5040c1025582d0207403402000c040145e90401c01403211911132000940c0300c1c281032038002c0555030b081d008550380c0c140089180b00c000c0c52420210183d1b420440001030f81c02510708094a003110140c0ac40319142c011202046810306000503c18105c881e56280002525024400c11080307c148500082241e0041042000382d441d00c1e803c000303070016a845103004580811400180c0c16400445c00444036000440c0400c54000140b214280555010800b400b40c0c2100410000800000c103d81605200b036090340712501002c0091000103035003070313101d401c2440d050a05000380240c00c54801280c950683c803103443d240d401c185c01180034106d02108240c0e02c0141741c2d054420340e900700600f0000c8552040c096140a40c0500c650340c162542d440100040401c0810a40010b40381c41e0200c01c41810f004000400c0584258411030b091150000b44500c00b8450030083c51842c1c1422aa0203907020030502400d082c1880008109405509a039403904001c5550791020740d800144510040d02013132003 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 530450683 1250 530449433 530449441
    0xe101505150d0c080406050c03060d151d0714040b0d120e06070f030f170105040903090b0406080601170c040e0603030d0e030901180e060d03020f01090303200a08 71
    0x11000325801c40d504000c0c07050a0640240310101220000e03c03140e8000380e0250244070a100c207610a0b19000300d200345a071403841c503180d000b1072071000107014000d003c11110062071b10705001a9000075500244034007161320f15174070080306581c1c0da0964041c030350b0000e032000d164104e540340500c601c4114590280505071406e103103468a94030014030030406410b001e400740b6a00103c0da03a890060108900c510b440c2c2d41d80001350b0074001c0601300c034810590f05101ca0b12100389111010080c44a04440c8125804a21030149103821941c80e1001d5004e0f10420001103030128030540c000a003940b01e81802e903900350701035800306030035005c4903810b031110340d8420f0b0104814420700001824490b804240502200c0c03501c0040c8150344106c660b00f0000301c52541000c00c1e8110300d5a0300547c08012110202c0f00303504158203150310410102c2c40a001188580003240c0c811081500a220035404041101c0081081c81340c3c50030003034040c00b80c0505c00c1e05084101841e09156042d405c007507c00032200c3e60740d0190305581e = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 530451933 1250 530450683 530450689
    0x1050310120206070b0a1d060402030721080f4609050303120105010f030b150c0a080a02100c030612031d06041d07080105131104090507030e101505 65
    0x140050007607821020401c02c05010410202c101802031006e00300010b110070300b04400300c00760743d281c2e944107405401910078040507076000600c800a40700c0a1003140c07a815507805140c2800072741d0000040a460022a034400c03400c1c40c1c0d42c00303082840445000300885940700701c200f100b02d1200100401d01c40840d45586400c01401d48581003596405083c1028581d450764002865904040210341c4034a8207240103008550784940124009212802c0620581100400048222051403081e61101d900811050305907502040b49400642d006103220780c0d10040e00f94000d48032000d5041a02e0054249000b44456512074403071101214004900095000c0075558100c0b040d2a04681c007920018500b07503c0e540d142d850b84000d1000b860810f003840141c0007803803060444075030b0007000f400c1031103883c030b00400481e221090461580f0303803600000100c2c40c00c90060f6035058040d94000240c03191810042110f1541c00d80d100b005143d18440c21907110300326407800c28042e04c521854a003900b0340076900c200003500f = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 530453183 1250 530451933 530451959
    0xb04030509032803090b03060612130f03231201050f0d0c0f09050a060b03060108220b041b050a090c031b0926190f050a060f0b01050310 60
    0x101a82c80c0c078050200a101d509012400301c04081000d50489420117822106020040110b09540e82c20340c40d01c80c00040150140c0c0251284242500700018690700c80a119441307076540c8402c0e807a840103d5418010840d5400191280c4403004024843c80600c0c404010f032191240d0842500344580e0a020511240395020001e0f150000c408600301400a032002c400003014000040c0d400550303c1c50844030720103491001c0d01a180c3c07545007a4091280c0c5010804480c0d21040a08020340300b9140c2d04242c8904a802c00c8003074070b034800c1c202103000c20001e1001815005502070300300d91281144010050944010506c51250f01031150082000300140b10342100c4040921410002000050502074034034007000564880300150b40b450060016031541c081e10b21410f241d10754115094491501c02135039400c4050f0f400c0300c03018170340070302c2d1020400c1c0d600809961540c804180c0301c00744008c0c075005000d800003002a030b00c5075080442089a552085081d28403486050104407085450a10168130380 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 530454433 1250 530453183 530453197
    0x5060f0130020d06050901021917162a02010f031427070b0c01140108100b151b0706020c0a050d05010608030a0e0901060906120b01021908030402031203040b040305 72
    0x120b051102c600c0484c1c2288100c40c810b1701c40c58000750365010443c0655505000001c420400d1017230781260419240300d5840c0d2a6400aa0414117916a0341c444034290740041d1088a403110144400d82c004100c00070f8101c00d4a0755030b01c01e80350018880011802a000e071050585004414a01d10000a050444119035012400d50344480180182124154a403c203007003500400042d80c40000c40d46038038402480340540300c409804100390194101070380741d512914074407030b490400d503207400c1940510360301e20811880c600e542c02910740e645d90b00410410a25a00103ca95401e40180c450001b00980040ba40e111a5103004050105050400d010050805076443c0240c405650740c80012640c0c207003c00040840000170b4659080e5100d03d40e080210000058110404114500c0001c201c140e030030001e480030104a118022852034000d0004034640014100d044000216540c142c406003c0b2490055026a00039410380d5028004901c1c0c0c5000d610003918000c4c01c0c60036403400a07021a10482c050150 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 530455683 1250 530454433 530454439
    0xb010906031203111c05040c0501170106050a1e02100501080601060c020d230a051c0c11040b030102030a06090b030318090a060e010f14040c0f05070602070f05060f013002 75
    0x7040c1980315034205c590407208262140665070400d0000b8440e0040c20f0100501c024070b410858040d00240103d51480184111820f000011035041c3c02d05000d080c0240e450080d4100c101d01390010580c1c000d6032900d008052003055803500703002007042000801c41a0603141583c8880d82003110315400c0c03009030305c058407003030340e2200c0d00004d00742030801903151500e003c14410b40102440a50750421604080c1e0403034100c241420700d42e80381d2030710940100e82c010010f50400001e0f940d01400c0c02c04a00540307184018035038154400401c2110301c900b80c0c0d0007502a1140e0310810018042501c041c15620f03c14400f00501d9500b00035055100c6250410026511101d4614081a0380707544031032881c4101020b8100e0449220b1085044c400010351002620070074400310f909101c0e801e0307150009800d62160700986420460001404400d000da03540403075034a1030b485903441242080a00301180c440e101511600c0030301452100010381c16040020107194813454541400302c81202c04080c1300b00c55003000707080f60 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 530456933 1250 530455683 530455687
    0x910050903010c090303200a080306040207150e211b0a060c021b0316030303020f0c0a0501021b070614030a06120c050f0102030f120a0207080d02070b01090603120311 73
    0x11107500c0070f000312800e07000a9183e0000c0242149000b400ea0b000c03041c0b07040b40001c40750b1a40c407240c0c800000c40403840e81c2c000381115540e07120f0710081006841400c0c0040e0840810900d00c0110101d5039001c03061001c107041c1a950388480706d0000c00108495940e15865800c0288005841c442a020f442000c05101c0d4013200c51005e036543d07034201958900341080000d40c018105201c8885556050703206c98000c218098113041c4101903c92510002c0b50001504155000c212050780034101011140c9640110701110821701c9585000e5010b9842179204101100050500010080000820b102901c11a03158500d01c1c282001001c21a50002861801c00940300c41002964054940d19003c01c04d008100043d0454108014400b10610401c009030440d44200403000000100c501651403550400144409645074815032601034007440c2d10103000320b03070b00203081c0c0444400ca0340180f103801e210f003107040e1150313a84c1c04510084801d9444044c09000e0050b6844105612035840140102d807042d12240c = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 530458183 1250 530456933 530456947
    0x2030a0b12060103030e151902010f1e060603060602061302010203041a0309010507020304080a0602070c03050706050a090e06060a080603072d0b0a0203090d03111f0e010c05091005 79
    0x2a50400d0320780500d02094105400501c241544100c0c1c2d0b0000c0f80064031009040a440d003808026403042ca02c0421841c009050305c170306250b100790445444102144030070300100e00b19031074004412042403140001c82d0b11704000091024002d0041e40304a0b08180c000e01001d0ba02d00594240b480a0b0810807811400100804529000d42813400f540504510102d19242c0c50f2501c9241c1c21250003910f2041598028001004242c100244420b00c2c1e1758861005a22540c651800726100c3d44142c000502030b002c0d500b40840e032a80d00001801d05200c1541e103d5034610b03515483e8002e42001507608c207400080c1040583c082c40c0c040e10b5042e401a002400301c5800c0ea030b8503136050703e251100c0c8035501c100400007102200320a9681038401c000e0102c04200a1602c2400c0d0300195807407060300c102c80d002d60318008020080c18022085091811002d0080d5103900c0c1501112074110f40c3e1166200303050505d0090580d044110500c0b03038141100d59500d40c2c83c40d0002d00410024804181d030301c071a0811104202407 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 530459433 1250 530458183 530458189
    0x50a1407030506010902030114180601050c120c010506031509120703110a06061d2509030605090607080903212206020d0b181303050f07110112060e060402030a0b 71
    0x1490003440d00300c5c8016169418040c202d44034080a507182032240c44003010f5540e900c0403400184d0b81049090905035580c0d0981c00106041480700d60386c0c00302514010540301c030030f442e040d00004d2140d60708801360303045d0003001c8000e140c4400042c2c0d10f40300141d02203820350100c1b01403080101040360007800c1103100041502c100740d10307048007c041290619143e0b501000041201c42562041c065520615180e5241007100c41c00110070f0100b03002c9a0220015200030355901074810341010f0754201000740500e19041034600c0c0c0d21001a84e07071070005490400056640000801903a42c8a036402c0505101401030300702c00b031700c1d80300050035004040803019015018810107d40c90035040388985005a140d03051110301a0440d0080103800f80280e8800c0111403600031441205980904022410366103410325090403112809100b1840c12030001c0010700c1c005010074000d000410f00720980c1c0e0588000c28811500e0191031a07403051105901225001c10f1407442e00c0c1e0041c66026141c400009000c2d0049400 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 530460683 1250 530459433 530459443
    0x50a02040203191802090a0c120b180106030203040215030114010c031416051204061b0501060f0b07050c040e0a0f02030a0203070b03150604050112020313080a02010606020118050a14070305 83
    0x281341060440240d001e41141003605610f0f03408641c18900b044400403660300507000c5442c01c1c0e00350440d20340c0c0b1b60201c400c642d1076011030544502c01c82e040a07407a6031621030241c0298000d40f41a4800c071850700310032142d8238000046074140c824054079620712038426801075404207a80d4004506120b40d04a6480800e182c05010f040158182202d103000c042441c20400e0030000c2d5040d0b806403c000800c0140401a00182c4c2203200c1c00311621074141380c0300507050040c0101500c5d0441401040380300f500141c26031241020700646070251041d203200d64899000c0108486c400724110380c81c1d8000d40c01c1c00c1c001c1072124158451240c000703400d0381c003d81655800a07040444d5030304840c0c034511022052107008a000800c80740c09540a46015140c0303800c210000c0d101161914541c494242c0000000d40c00900902e4200c0b003660380070b41003a0312450700d0340003c0e003e051140500e0f40150319006442d032003540e802c5907041c540354200010305071400480c2c840b42401d90710a50001010b10403031074000002442006 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 530461933 1250 530460683 530460701
    0x403111f030207210c0b06040e0c0d1103010f0c031410051207080d0903030f020d0917030c010e030307020c0a0b0405010c02061201150905040c080708060a03020a0f21050a0204020319 80
    0x240700d0365945c0d200c0c50652404040075100c01d0007130b45010440c4101800c0041c3c0820000800c031030b9005c8404103032400c40300f200181003900760103500740360542405912031b822482c11080c0c10f8600380090040280c0d420800401103034050010f511084040015003003010051049181d90780039604102c3d10350722070074a0001c0824059000a0603044100103041d031101d185862082c0510142c0504404180010900011350180d600403c2c0c081e0103150400a0400032100c10622080092004900d0142100c7e22904202d8869002d4080c264003200399207812203081c0c06072845414540c0c2800d00748401180c1c400c190305003c0340c1000c81041103501d00400b0852190007089400d4583e4040c040505c4010803007002c80d0704c0719010f03d0070074070400d0b40d46812032100c1d5448191071a0451460307407030600103a0b07901103a500194111441d01400714000a620100100b5181200c800160320744001c4c176142031300508580c001d41913402c8140c03284014601070b00190b800600c13581e010080014400441c204413100c001d = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 530463183 1250 530461933 530461937
    0x403081602040b0a0e04120c0506181c120b0105120906011406030c0a1817210a05040608070c02040c052101080a0b101a0403111f03020721 61
    0x29050411440c25010381c0c140a035044ea0f89080c118a040f20008482c00d001d84000c103243d00c2454072162152003500c44401c0c60750003100f203d005041101586040c1580d009842041d4040c480422694a007200500d954080c465610150a03003000c0501c58000c05a240700a41000310800100c41c541402240480c09101d441003d0074895240001d03000c1c8900d0b40c000c0c000d024130b405204014803c0081010340b9001d04980c107100042c0c1490881990076006650414103040a0304044030403049030000c0c20781181e2000aa200c01c80d00501003503008d040c0603240c410030010b0000c01007480414403600d0300e29004100b6040604d41082554005001c1d10750303c060031030018401059298a031050a24915560154001d041c80d031541490140b50301d0f600019005030040c191140840c00340e000540318440107207842200151140c80416034000340354810b00c000d03101e40c500e89994410301c3c40c040500c20011f4076005610700420b07841035000c0c0d0103500101f00a4980707520243c0c41c00114000070308910f107140d00d15 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 530464433 1250 530463183 530463217
    0x1f0612050d030b010f0801090b010e040c05040f0503120f0c010f0f09030201150f051210060305010b01090b120109181a0a0e01150603090203070306060e0421081b040308 74
    0x404000b003c4800d40d0091a0401560f0041182141d4100c80081c1c1548c500540110384401c0210068070a030481c0344034035802c80e00d020280309080d50b100003d881522550564070045994441c101a50380c13030096a0000a810304000803000111170a000780300101c402e400124030b003002c04131000116118600c00081098842200108156083c031651600480d000700e4a8049800e10a2119a1240d140201c5011b5400c07840d4401c0410010405940205050b540c1400140e840c1d02e0140e002e81100140307540070071100d0b000406c0281e15641591140c854056144000780c0c83c11541c140503245440201e0036484104404501244051541d6141e02119241d4540e80c0d040c000030f6441154140601c0c080c0c40e0b45001105101071001103149000c071035040c540400d100032240002801c3c207003190700c0104070929201001541506040805101714010444201080e086110340310703071013006102110008640070006004242601d81d28407100b00e6807540c05007010303180c0c0d680f03207420f5016006d180954100 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 530465683 1250 530464433 530464453
    0x30a0e061b16080c0d200d030e03090d0804030b060d050d0f12050a0c1409150a1107080d0f0e013f020309011a030601030f15051501020f07081f061205 66
    0x3141007906ca0340d074210142070b400140c4000d00c1d111800301c04804101500c8851269039030200b0800d50308204401000c92214403010b01c0d00f46441d81c40741c4000ca13042805500080e40500d440400603c106800501804444444031401c0318680030400001040c4140c04034003c8030402148980d80c403441c00054005035010010b400541316014620a003902c0c4d02080204413030304c1d11130901d8582c0522001780c03030039112500c00d00241c922514143d2000454865414001601c00c4001010502c1a4058484034140ca04042080343c810003008601400318402000c40801104400070720030001c1854488040c0440c0c041c9807101010050102c8030030465000b00900506400a11400c0c1d00d42002000500c1818030040c0440d440e944144000303230034005800c00d900c1c1840020f00b114403038680a054204914a044a560f610109800906070f00511965103002184680003600109a40c800300007451032004400383c001012900010765410141c980300c00103070030181c01580c1d0807460f101d02c02030001422 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 530466933 1250 530465683 530465687
    0x121f0312020606031c451a0403080403032d030c0215070e010f180306050a14060f2b05060f0a021608070201020f12030a0e061b16080c0d 60
    0x103c0c00f0801c1c15254040c00c11108841c2d084040040c00381403a0424400c40c0142038101c040d2010541ca144106c0c1d07a41085e03450603100705106000a8a00c0c07402c03106200d2668003d4444c0c180103c0c0001000302e1030030001031001c00d00802c2c00303801042038803030030030000070011503004070041016000c40b01007501d40c4690b281080d0184007002044c14120320b00c90b054948250300610420f00d02007140e042c4031001400c2b4940c0d42c41142c0300e010314800d10100c1c1102654a19125006190884074108060300e095151410201856109402550024091900f0b0340601c410400380851910b00300c07269001d1148a0404900348035880d1094170301442c043c094a280c0383c2100c8118100040c80102041d204205407880c1314191f041e1041425000505543c51328224070060317243c01381440500c0498842d090704003240309900c200039031040f10301a505002d10303481301c0151581e40c8810340e5152440380c000b41000400a01e09401b84c00d00c07034201704102144c07a8064a84072880c1e0b1240c2c080b205680c001d42d0085a00603 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 530468183 1250 530466933 530466943
    0x40225080a2007031415040c0f0501030e060f0a0e070b1206060a02120706020417070302011b0f06020702040b09070f2307030c0302031b0106150302121f031202060603 73
    0x84407008150451451042010346803911030000612800b002200060458806c210ba001003a43d10384031154681085e0030600210010340c41101c0d208010360401140725407090145103001d600c3e200081806441e509500540d40300020300c021800c2c0c0ea6480750341d010b0031042003040000c00c841854a46c5d03511000100010741000144002d02500082148848042d40029407840c003004080045403143c0141c50b1240c083d2065a100414814404030318003502d1a020030200101d80c800d132100c0c11110b00542100030a2104e009001e454020b5001c0240302007042d540081402c184000d0000802c41c40483c009040c0c100c0c1035400300c00180103c5c030400722040c2c0103008003080c009940f40d1804c001d4440c0c1c19200062180d080024100802010042c0416008100b51084030b110084113401c0d00c549441c4080c002c140501c959030003000082d100d00d5006000380b08903403200d500c3c000000b16568801071021a508203038045002c02d44a031940c000003041c48040c10a4200c8003a5014060354108402051f20701 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 530469433 1250 530468183 530468207
    0x2103200d0512010f0e010e060d060e0d09050306150105071703070c03080901020f090f120708030d05010f050a0b2b050114040606020c0d0203190f15060311040225080a 73
    0x4c00c2c5842014054407070400022030448450464012290303417100003255441c0811140205101d00380114111401d00100381e015020b0020756039030401c280d5801c10150340d1041035130200782110a51880c00c0f002c5d441100144a42c501484501c0ea6502c261017030449c00f540115043e4000450b80107508e4101a800014150402c1c001002503041038840e03003000d0000d100f00c03000c1c0343c864140200c039003400752240c403884941e001c2d503541904c41c140e42e04d000f42078036580021382c02c00c8098500000401c02d1007841c000e00c4151034004d4522542c042c101300090240345d2254180d01c445a0060103042440200303111003c6080c0f001080c04102540360031800120341b800e040e16a44240c1c1040e10910025a00041000300c00030308440641c9080c0c46400442c7c00c02024101041c0302400043c805000d10405500d031025641c8035445840c00c12040401003c11200036000040290b2029a0880c2c5549402c1d0050006c20024001c1c21030402410000703540780d0003900d50121100000480c21902e030b103400170084940 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 530470683 1250 530469433 530469449
    0x60f02120c07270c080a1d0606061c0c03060302010f02010b030a0209060a09050f04020306130302120f19090906060e0a21050a0c0e012103200d051201 66
    0x4148070181c40e10340741c945038010301880d0301c116042d8803503c071444010211549480f0f00c04004030881480c1c014020407044139451202c5081c000640800d408284210304e51501d008040c01198030b07000d04000d6164004280400c03d039540d00008088120644591040003c0c1c90700d00040085c910320003d80b854120444400c19a40f41c00c00e140c0301c688000c1400601150b0480d00020a680c648002580d030b0b4566800118460b849c2c07200b00a180c1c00d00d20754050285001314100c441554410f0300c80b48008008100c001c0050700815010700f25044000c02924030b8100d115074540c1080308280c4184585c140405404001424400c020410440740303120b400d002e04081e1620301e000254180101e03601d001148260a00408200110102115009100320f04158000e060350707503030030341418054014070081c080d1200b800411400010110401043c0802003901c0c41e1100c4807280503500c043e0b40c0015481e11101c100032400070301c8000c9600034058000100d071641c07074003520750012002e02daa49960581201d02 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 530471933 1250 530470683 530470687
    0x906090408030f040203010f0603151a13050a06030b040b060922080f0c1f06081914010b091305160f05100315260c01120b0613060f0212 60
    0x40860481e804503075010100d203410841c140c44a01c0864010490046180781d01441d107580030013001001c0203440e00c14420b041c001d0011070700e8107294192001e2641a0968489070219001c01e80c02401e030045030f8841c0c140403001070480d5680d140d0040800c4119821281d500e0402c0c00c000c02c0e40703048016103400500c2c1100055140751251030103100f100780a20701174880b100110303103450114010011242d8031401d40e402d071416610318402d407030504403c2d4211940803506041003c0381d08200000c41b070700740910108103180740070465228071911019148013050a0f54070381d02c01c14040c1c1c46415404d030055001102030303130000300070b418150b0410000256941d40600f25102c01c21140703000c840b46005a170021200144103446984041c0c004041505a01e041c20b64403e00003c0c0c0c00c880300341c154100810684000d80000c422121164031240d551a1550104800484c0340c40c048204c0e50118070044c0c009403101c0e2406a00100d00719a1903503039401400052001502d1242480d814400e0070490140b48544038 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 530473183 1250 530471933 530471941
    0x80406181512110f0a0f050a051204110406060e0117040803010e181b1e130b010207051305041202070e0103110f04020c16060c0b0103330605090609 65
    0x40c0d2400c009101c54100306944a41040d54105a4403003d000120050b060b0b9454200c0e205038141c4e900842d076188003292072114001300c40381c001e400301c0f80c010000c1d075105441c007624803c3c00c04840c5070183c4161440d561202c0c281e031054603076100c2c03d07000d000681c940415142c0190001800996283c1e441d60180f00c00b1001d02c00020040c4003900d0646003501003042c01c980d039084c614505000110983c00c014410044142c1c04801c3c104a0480b4814050b58032501c9030034138465a510420083c9036454001c1c02c0c0002101400d2955405034400c500140b05803004582c1d14400a060710b07001c170a030301003207540d01d105000802c030030900c1106080d8601e00160492070301e0800910b9404105210280940300c50035282c00b12039940e035501d515110300062003152591011036900307945100b1302d0303400c039030203e2a4100800c183d80207048803000d41d54010041e5501d82e00710303070b11504604030707150004400e8100a4100306001c0501c0403450030070301c0841e40000c0c0052400c020402d0300840a040a40901d021000380 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 530474433 1250 530473183 530473199
    0x308010905100605030f0c0c07061e030606020d300b0405070c0201080c0306032b090915090b03030f040b121302010c060c091e050a090213031209080102040308040618 73
    0xc2d0b0341c810b9a007104c01c501d0755031f8890b01c1d03001441804500c24090140c044081041c0d074104902d124900c003403d01040706200496410b40032650140030b040056803003400020306a511034802c115034500c40c03110303d080756564601401104940141d040207015128150b084030b60519210340d642c000c10502e404055560fa0341c0018040c500702424440294900000040355a1820010309084140c20140e1f81108003d03501c08050f203075004c045200000c0d503e50300000d0004040d0040d5520061703401c49541031180751100d801c000b015100044c03901400240b000701403070030400c00540004c02001c103045035a03203510001000c1603500200358180c043c0903005260050b0364040244421980d04c114006040c1504540540320f01c440f0b5448050f0032070720210895000c4030322030a0901140d4055940c0100c1c1078036401032105900560115a903041c80c842000c2010400706014202e8100140c00d11490300c0b07481c3d203080c60990707006030030035a40007100182c104610f5512078407a610001c0f40030314a0780550304007212 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 530475683 1250 530474433 530474437
    0x120d0b0603060108040f140a140105060a0b0316090803040602070303091a1204030c0b1501091a0f09010c051014061c02010f03020c0f06060906060406090509070e0402070308010905100605 82
    0x805040d8100760f818107403c00c21201028811f40b90008221a02c00ca0035150000518100e100c82d00415401c0030080780e264105660036400f030380c5400c03d4141c20740e40c4410614412400109065080001c165400a030081d414001400503050f80d6014114a50440c10043c00074006d691246001640001c0f03682008404507050314110100c1d0784c561903940d03c40e8141144c41c045400e0010700320707440c0c2100307101171a081c0403403403030858200307890347e625050303880c0c210700e100101810200849001c10003810056030401d0004003211b400504150032071003d503440c0c05160a440040007009140d0b0b07000201861828861842d80c411421244400c0500c0890b40848044881c000001d050240c910030b07205e0030600070b4058400705495541100c80144423212060b54800c41502c8840c0a003520078040341860608804440030368550b502c8176201c040c50f100501c490004010182810031008803241c402681d224001400e560b4000d9440c0d52042d410111b02034100c80000c1c00c104800038500208002c80d035003040c2 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 530476933 1250 530475683 530475691
    0x9090c082e0c0e091915030203030f090409050709020c06010b0906120a022b06050117130c051f0815100513051c0303050603010501030c15030905120d0b0603060108 72
    0x80401c1c80d40d0482c5090350380c00a04600b41d58086868401c0021040b501d903070000c01d82c0b180480034000505e50034510164851107003c003a4254204000c0b00c20300d000701900505c00c024029100007103500103500c800d03080c01c1c0c82d600001760183d00001d0400508808100d55805406610102c41c80c0644410010740c03140700e40c5c4078a2030408150340005882c8101681074900c0840541070341c2c07151260281c1e50642e14800e50100142541c9011800300352540310341c0341244070301c41855a0520700c0e12901300e1180c1040b01b101c01261060200d8101007a41e85585210205415403020043e140b400510806480620003c08490703c9130746840c00964242d440e4071080c503048040d030401603038889019520708211002c1703401c00c50700700400c0c2400d9511052030050f503a0b50705000f5502041140ca803241054240d6030b082c0b1014100014001080c8034104130711817620b0040350103060019540115560312401e04000e4505054040d40c0800c0350348640c40d45010760f030b40c0d440088841500e075241c45c00010b052080c02030 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 530478183 1250 530476933 530477023
    0x60708040303092a210201080408070c12030905030606032d03160c1e080a02090c0702090114030d1e080c1b07140909060a020f0409090c08 61
    0x1044601413089000903000349510310038001141e43c0d480514000c80c0c407520b02c1008101d0180052032401204442e100c02541079050b90b0310480d5480d241c0320182ea9801586045c1d802c0401c0307840c00a2240d4501c80c480341c020b440307612224035442c0b41c2010141030440040206001c1d0300700031a000031010051001440422101c6505c02c607880d2016002807450044500350501502c800312803034107200b51104520704403001c90b603078092081400c99504000c0ca141384544032540d400310f0b41040061030010012903001320180f400b182048100e40014400e41820f074400512a02c0c280046100d13820148203c03c80d02103903080c4030b40d4890070648054103003880c02c049101003040344000704070300d1060303441101e0050800940d8418000805c8040d00d880c1c8505100b01003400d2808100206203081c2117841c0e0b48500e080d03002414442c0e84030348004000e0740c001c16401110000800021644003918400c1990017030080c05940c5210381060403040c03600070804510311110034a0b07208140141030004c2404102c0e000c207 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 530479433 1250 530478183 530478191
    0x70f110604240b030d05160c0f08061003050a110103090605040c080105090102070b040f0f1203021207030b01120b0a120c0302030d0804020a0b0d060f090504031706010203040308070203210309010608060708040303 93
    0x200420b1040c0602500e070081c02003c042e94000780e0b206078275080030b0503101d405055031429105c04031a007406050b6444001c1c92900140040b10106107403203000e100b008410304012489080036601d07601100d008840c12905204815003d10590009100751980800c0c408004c40c640070300c41d1508500801d001380018003040c01c0740030a104100c81c44444d0484240d20103406a140c05000388042d029401458100c021280802c000424161080c09000da8000040c0c5408507911440381750b60001d0001c4042017508845108000910b075012842512481806a0008481c941c00d510405042500c010b90703c40410500c2018480941d80f820178400484036084182035803139910003170200c003404441d070049189901c039240008407103074190030051080c1d109683c0d6000c920401c680981e00800c00b40d07051030040c1d109200a100245d4008000d10601d0300060442d0920150100c0403252114580440c5c1c68800f800300c01d000c074000c000d0154901030000c0070042d005078600400014108040280058105515 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 530480683 1250 530479433 530479447
    0x100f0312182d03020d08030108190803010e0703060510210504121209060f09050606121f140403051b03070203030901031a030703120f090509070f110604240b030d05 72
    0x104000c030043d80c2c090507181c1e240030581030500741900240326048103030040b200320351034080c900070010b0324040d48984071a0440c1d0030640c11a81e101002401e85090555071000803074140c0d142160b100d518112a500d08014001081c926621005108030401c003690074102800700150040f0030240081d000c42c603244c0c501259032020f030340c0500f00707160f0060b05081c5401030070710b09140c07590007048121b0300540445405444440a010040b14040c1b00c541e51508201c54810001c144404071888114461801040b505004082c135141b01d40141c400700c000c5035000500817800c0c01c50303241d00212107030072402850074843c0c0e68020940f00d10541180728100b665a5001c01c54600c0042d10340020b4100103005c840c042a1a450500100c0d0881c1c40b04d04089500c904070400107034416250780c1c040e24000b17096294107840381041907174110303100070682041c4090b20701498016082000071900c01c902880030009458100351400085c4502030004807009410464803a20544000540c0000191030745411a500d440c = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 530481933 1250 530480683 530480759
    0x603020405100305040512040e040614060a03120509040f0c020c060a090b090a03120c0209060402040f0312052104031805010e0d1b080303040528030305100f031218 72
    0x10300387c14919100400813070b000c1074020015080c1072195100f00c0b81004011549903c0d00c07000072044800550013101c000d0103200003014035166054115403070912909102031080007400f5640b081003000d124555500310002e002e94100301c0c641401e00f0507161a480d005104400821180341030081070022500000ca049454030307846180c0f001950031207100303103c20046080062411402c1181684102400004100e45203442c1c07007100c04481c0040100d0910300d2850b03845840045c075000580003406014040007011300300b1440e000890003030a6451103d0352416290180c00d44126400715000c40701c41d40703000d000590308801100d847c224111401040c00c3e0042c41c02080300030b00c11040401440000d180020302d000008080d6001d2445401523581b05003580c44101102942d842c0d10304541e405003810712010030b00036400b183c0c00409410381c2c1508280c851103074405280366580110355000d0032030521000103610801100788121032101d14680203251800d402070360910041d070b18000661840e4038041c078139 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 530483183 1250 530481933 530481943
    0x110c060f01030506043c110108010b0406121d0619090c093c0e010917030702100504080a030c1e0f03090506070320090102150603151f06030204051003050405 69
    0x3007500103040c0312086c200491202001c41000210b0b204600112103000750740c05815207506035101184010f003080c2c034010044503008098032a804415075901807119501070004c550100811041000341420300f0401f1210b03c403100908041c0360220300c1d094901c2c000410200da0b07241103610540d00480e04107000c9140c0803609065180314020814142c050300c4c415111805201107445444404000031804000d2690a80e0000320004100c00d1503080000341040c440d6000e103400c10803030f03c1120342001051480c142194420b80c0c0c1592203050205007031019130307818060031100a10a207003a00441010b8011642900c840d04402c8051050780c04140c0401c51082d40300c01c0c0c0c1d440e0407000b00e45050034040000384c005e000c5200d5041c41d21502d02c00000c800c0000f03208a80380d0507410fa00030040110500e2144e9044103001d03190f1035041c080e52000311518130756849040d0280f00781040040411180c43c20240c0c071401998003d400f414014803080155039078074441c1802011050802181075642c0303140c01410700d = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 530484433 1250 530483183 530483243
    0x90114031c030b011107030b0403050f0c0a0b010e0705090a180f05190608030c0606220f0510060c1104050c040506032505030631110c060f0103050604 66
    0x1119035515542d0300d80c00102c2c991000ba2690030312040403007021600c0c2c101902014011024840c0820300182c4254010603040503a042d6090502183c1c00b035203410005c035071005852100626005000c0002d10002643d00321090b8104603141c40582c0703000c01c444206501c0341084060604030242004817031500201020710800d2001c00162500004000910030502c000301d004030719000000c5000940002203503070071844207009100b40c0c0e5035401000200c0c1ca10700c1a509a02941401c032654051450042c5585110380b00700102e410b1400c40c00640e07042c002c9030b1200c2c04002d84070740d0306008035181600010900605640104160f6201441e40e2003600c169400b01e43c0240d0700104122a40004c50014040e41d10642e0016010b0302e29140100d03142d000c103135603c1c1e0380300351a503205060242402c000040c840c1548441a0000440c0b1001703a411030b00e0058551080b0780340010b2145ca41803080c85a02d9000c844101c501c04e141d4150b03101d03140d5505004000903c40007c256a10644c40c01074030040000b = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 530485683 1250 530484433 530484463
    0xc0d0b1801020c0d080f0a02042303031905030406111c0b180708090709050610110c0307060309060b030a0b06100c0f06060e1005060f1317070e01060203070209011403 73
    0x7596103130010050a403041200c2900322441003c0108605944500131942118041e4100c480035450261640071100030b00c154084d4544810480c80b25070340c4407001c000c00700d44070b262600c6440b0310b0a82407807002d03555000f0007004d11280c10011000003040c0104500140d0004120000c2c00200c6100800c2d1003040501c0b10741400300101c810480b4080e881813540344220a00c0c1c06035402159030f10200406e451090b141c440d80000c1941115911510440111906464590844078a8202c03140820f0608215410000c0001d803103400b0501446210f00800200300300980c000c14004990361900310701700d94050030b802c1c4211900c1c0f000c003019034803034006401803542102203a5554501e501d08400241554412701080414407000142c0d2104503c02c0310702256005031183d4903001c00e664400ba2194002e8110602c0580102c90219196040482481c0391018600040c13003d0342c103005101e40f16540c168809006c5610030041c1000503240c84802c541100c04154104334031000c1e141c00641040c07110303e20b003c1 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 530486933 1250 530485683 530485693
    0x3100632030a080405120105040f021005120108061f0503060105040207050307080a080f01060206040f03081e04110103240e06150c010b0f0609030a111906110c0d0b1801020c 76
    0x209000800740280b04981c1c08070384410b941b82800103c0c80c01c1c0c84085402a20039a0480e41103000341c03d144240c012103000c030f40f4100d0302d0003128800e40441a402a003010720b069000c00c0803c554560100008658100c2002007581641d183c1000a5603078001400f03000d00464020401e4410000200b06840c425070f4030403500c0d5142e06603404010001c09003214070040070350311304000090850012032030340d01681c0c00106184d080c40c034549060314012806030901031a0989000480103040440300002d0181d4401c1624040fa91481da0004003a100d00f502c0e11504180055003010300b60780c0f00c0c3c00d02001c5030458510010581d60700c02c0051038090104204d030000c0040000c0c44a0303054019402101404411940303460030015290070301907140200031003145c0641c8034200c036101003a5491213503104c026004000c20605c2d1031024000310301001076031240001c0b880c03102207410b4108062081c002401400c1e0b07009a031048803912203800044001d8045040740302645195400540b0a404a03403404d180c1c41e0860b0 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 530488183 1250 530486933 530486953
    0x7050d0303050708011703090415080106080703020a0f060903060c020a1203021e0913090c12050607031103151212040b09090a0905150705130f050310063203 69
    0x203030182c20700b00c0700980010071180010803600c400516641d6030039203c800441c18244070209110040c141d546000805402c0e038400020650400d000e0308014020810180c52182d10b1403060045510b042d401c2a8803154002000b40301055001c1a0310007101d030000400b2454000c00602603013080e000100c080d0070054030540240209406400802800381c103040901143e59004010640c0f900403601066031014400030340340300e81c100940212079000e00806d5200402c0d42d40740c001c3c8c90b1420a40310101d80b41c1c0c020307030304000700aca4051051020004078540c0061442c41d02d04460b0200b0001050454440c542ca0000b0810941c2c0c20018003402565003585281d840d40c072040c2400c126084954018812070302000007420710700d9580500c40e1059031003402480a0700032441141102e010007408001080024000004c540d04211160001440d90740019860281402d00389420000108c02c03c0502da42020410401028400c5a90100c1000742001c00b0840350203980c0a10041003070008507600d8400c0c1c00101c = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 530489433 1250 530488183 530488187
    0x5030a022a0c0306070207060c020a090609050709080601050a120836180c0f0c100507090b1606050a0209040e011b140a0e121b0f03070317070507050d03 67
    0x103501d00c040c6040b15203460800d802c06640f01812030b80000143c200c0d031403c000180c01114900281440240fa00c0b10f420381312000003044880c1c550115043d96160000d2103141500f107600c0c03001070106c0002500d403039030418000c00c07800400c0d88614600d40f82d084c00305c0f00a02840000b507505401c041c40c411400500d01c1507550418100300c1c0807401d55070340b900240c0506450201c0440441b0042098990210343d1210782c5000190003a6880348882d40080007020700007a800d105549a4045082d00040d076410b168800a0165150b500202d0001c0c0c0100b01107540500410340002042d984084045010307070743c100b86040a4000c251405030000d041c000c00750034544041d0081c08121884400228840e41d4141040b41c2c100000c4100e022646030030031032428118810340d01d5010700c40c000317410308004420f44a021840c195032408003aa1190b0702c2501260f0301d103419401c0c0f6801500c00c900a148450030340c1c54101042c600920008012800080c045041160a21404000306001010080c80b0420b034100 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 530490683 1250 530489433 530489497
    0x150403062a0221070c0b160606060809030306090703060503101b1b061524030b0915091e040b09060703110f071506080d030b10020d05030a02 62
    0x41c65405841035200c503080e00388001031002d40c002c020000c890003000c0c2660482c40c0750344404001da9007501042c0d00801c0c0b030308406000b0300c5002e00513410001c01c960981028022150f05401c641c0070001c0c2c07102404520710000040d80d82040040701e4003d5942c4445009900500c200e074401d42c0c240c0282c1310040c91800003588036800340680e0540f480b008900352402201c0c0804603642241880080030340307040214203598401c501420340e00c260070f9002a00c981c0a00e001c641810305440c880000c90006107200750340340c011034075080000c5c0c84032000350810306140000303440340e911014090031044000441d075400f802054812202080402c1d0014142401c0a050041d02120040501d224420110346281c0c441d100305030b501d200070155507080c006500602c203a03c5c0c4c440c0c84142c0f07054504481803a1003d07840d214000c010001540105001c8071040d0300941034681c0000314601c640301b102c0031600029008070311320b01c03030024519149036255100c2d001d9800900903450350b0070195100c420040301070003072698 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 530491933 1250 530490683 530490731
    0x80c0a0b190f09030906211b26010506132105060906040503040905130c140f1c0605091609050609011509050f010311160c150e15040306 60
    0xa818000d898011102c50182c0d40b640800400040c5100010482036205010044032802e083c107d44542c902c2e111030301d005464044d1060104805524188480e0307075040b4980c00e03010f2880451100c2c004500c0100002134802c1485503a024003000160007410000024114000d81001a50f040c45d0100b14180f41400070141c2108444d1403248a0100f01c98810009290f445154840000c601d0705091140200c080d01001e80f01050717045003510088000f842500b501009042c01c40304002d40c48040d40204990b001000c96640e000300702152403800000d483c0210441e81e02d804c8100450070b6140c000da003d141000c0211510400c41300e41801254204042c0c0140c0e010703490441352a105641c030740c0500a51918440d50b02d0003c07403284001006030341031410705581550740c1410001000500e07c1d80b00f230040d90204458103110806511004208154441000040c051080c0344030400310711020003402501c64400043d1183c040b000d040c21142c501c144c01c45001e0f42c2d1001c0284002c1c0b550103400c400f01006a0 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 530493183 1250 530491933 530491981
    0x3041104060503060c0d0b150d05090c01050915030619140405280507020304170303010f06090609060507021c050f010e0d0905010e030106030516170102030c07080c0a0b 74
    0x710005100d10300041d01c14043c400c50441a485c1c000d40c2010070b001448140314117600001240c480381c1581d121000078140208207003074085081d00e00000c10f02e0504216410044c1400014881d18905449600c002180c40782c5014255a032501c550002071600310308202000d0f1fa9004580022a10f960041c18140706140f056400340442e0310b410160b202c43d46400d1207114200d81c0380316094090035021f88c0086801403042e0041d64a017544641c94000c86045211811025500001c010030080e130b0803184d46070041422745040d404c11401e00038000d0090308a40b0507030041140c003042e4072095595440f599400c000400000e015211010f281c9140c0b40d0440080b1868154a040c0d8545261000401c1030100030304660380e0030160030304000055403012140c0b012140c040d0358400c40440060340800022815087c402000005c0502d0403d164180448008108400e0303401402407183c00041131054500385980001c805031520f950f44200f51031b0012050303020f00300c40c0d1170300148803601000c1c07031480e11840c80030 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 530494433 1250 530493183 530493191
    0x7170106020a08160f0b0c090f030c100f09121a060904051e01092a091119120f05180102030405061f0911040906140306150102100203041104 62
    0x1900040e42c076140d42c258007030000c41040104400700c1031030795000702800d40b02d207040c1e0141a400d41c4610321070400445400c1d0802e04005440b0701e10f07240034115044060801c81c0104580484640400d40420082c10f001041c80f050b60031803941c560041500401606540c1044402000300303007860070a164001c051300c1c41710036600e000b14980e4200903900360312175030b0042c000b4110300c1202d5000501f01341d4680f88103c0b5035507a1f0920480042c00701d20100320213905078400c00b00030501c0703c505a00e1f0680c0907030043c0710103454120381c91015002c0c4c0c1c0941c3e10b000c019038005030030030007451416210071241d039041c0410b05103040410b618200099001c00c0c0107034104020413041c641c11b80030780c074201d110642d03000d05568840310016804941d8840681200f5a075070580c0343d08290b44455400070b68080400010a0440101c1c1c103002044151044034024250380780c1d0009414080c1d40840d480760400b40102c412072401240300301a43c1d0080042c80448031600034110754a2800c1d040201c000810701c1030044c03150f824 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 530495683 1250 530494433 530494439
    0xb01050d03171302090c0405041d0d0804020d0209070807020d020a020f1017070e0102060f070c0314040b180301140105030d08130b07030516090f050d060b030303071701 74
    0x240440040d54191544814541c0c40b906400c00c0480080010b111034003d0359150703005860301d0020b107000d40d140c42c468940700c1d42004100000d81e4059452011507048075015060752407400101c010308a8503034180700b0900e807664004600c10200d00c19029400a000405100fa02c035031100c80176100c1e190950943d00d5480000c0000c90300c0d011600320181d48103401b1140c1e0398103403909449202034100317607040c02107060100321040704414a045a290b0040390b180c800c0008656014010550300401a05c840b500e10700d0090400751020015620103010000c4018003038122058032821603028016081e075294071104195078000f08121607029450295007404c441d1000d90746407a180354180c802c001e01606902e59121412034520cd801450390400c0ca80f118816404035048100e9280a409240d901049500e0040f00a451081e6400c900380100b080e2444104400708501c0c10440030b80b002220720143e00d103d0303404c2402c040c2500350586a8180400400c2c0411160000890050110a0b020008040e070f6 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 530496933 1250 530495683 530495689
    0x90904030e0f06190e060405031603120302130b09042927180a0f1203150303050a0c020103060f082a09041104090c060302041a040312030b010c1a01030b0105 69
    0x11340610250b506080424282c6464010f076012049003201510320340c1416038800001b45494984900144040c0f10b0303090500030710800d0a12003000304540c1c10250700d0a001e15010560840c414890a11514408225001c250381c8039000503a143c44800c81103500000560300441ca08407603401c8240c810090903940011542903a034101300c50200440c61050f160303460b20349100031003800e60a02e4499015107115503001908000d01c003504980600e00b501c080f450b00001c0501190310350350b4040100b4030704110400000303a101c2c040340c0d003038201854403d64074a054401a03000d0001900888000b02004001081d40c40b400202c106d0340724024400710752040001030008550120310b000b150b422011540010b80440e003d850480b180c0c44002d800001c0c44892901c2c1d0518070f190039005100000d0300007800300b00048410000801850442400d43c4c0740030301c1e56944440c150400242c000916880f4640003c040c0e001e105040e1005401503110882541082d030241200c1109000c02c48260580c0e80000c01c581c2 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 530498183 1250 530496933 530496937
    0x1501030c02060c04120f050307060f050c0c1b15030f070219030813080d020c060106020d020c030c0f04090c03060c031b1211040503070807090f0b060d11090904030e0f06 74
    0x1803440f50340e151626040102000b03428602400540341e0480140741540001ca080004000d4980a80070001d2918800b445010030b4440161542d100f466091240e0005403902250306000d002d40c0d071150a41c02c2071f075440841d03040c003a00301c14105070300d034040100f00380803295484540c0b1841042e4291a202ca0254002c01d8119951000103030004042c40f002641845940c03103040c1a50b805a000b0f0b6007805105002001a03a203d4072303e0f0411a000390004002440e010054074083c04020b0000d40004110440800d40d1184c00c4401c0501c10000c1e2205009203071220392107801041d401130b410142150710780c14500050041d10f401a400607160808056a444803180250b40d0aaa00e0383c50081d113003148890400900150780c456600f80600b0400050695002c00464004081c2c20001e0b1010503d02013001048030740c010de54203039070750820200c610596201303421a031090140d1400050140304602c180d14950003804086038010b52232505000900d9080892200504412602100c00420074ac05005482c = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 530499433 1250 530498183 530498191
    0x90b0a0b0304111f0e130509030d050429041704060905010804110a06110615031e12030403031b020a030516140d1e0509030d050d0f051501030c0206 65
    0xc4400d002190009400d44100682c41000a0007004001c030b0b1042200c601d0a080e03d801400310302c41050344241400c01c60156285412580020001842c004aa00e40c491080d83d045c14206992000082d040182c4924910858004091840c00380c101d44400c1440020b401c2d20140d801707401d2101211240c0410004940513541c039540ca24050a00d48401504d0301c14020344115140f15120000c12403644642c003e0740c000381070f01d589138082815865091414500c000d84000c0c444038240d240b0700010b88000504040b4443d05284583d4100b0074244228203140f8404840d904101c000801d02085c16415000b4000d5070603051800c076148951540b0030303a5103400415008000ca0414020183c0d5542952260b040b42800741042203029648401324a0806071898030080108240d4000c40300100c020408000a8500b2414040e144c070b124000029510809030721000f0402034000f50401c001600c58100308205070304001c082c045402d10f1550800b5003082c4210303c0e80024505880130a84a100180785801 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 530500683 1250 530499433 530499449
    0xd020703060b0111010912120e0d080910110a170f0f0903040f030f0c0501170c0304080f0703030b03010e03072414040503030f010f05210f0304090204090b0a 69
    0x20480ca5035603950040c0000101043c14000454103c40042c0028056120198410140041c2030181701d080a0309285002c83c8401e9000c0c030340413040380f00c400002182d507442405811308051643e2280c17501c601d452014181a1151814821104905451031028040300495511451400032240b00105590403080f114103007400284008a00b034544c0358402141c00114220640346482c0e20b440401459520780d9008450000d0070740200c209001c909055000540000d00c7d00c0402c40600d415040181040a00300c041d8000c80080402e04000415088a405408280b9150f440319103d04000e402040c01c0c50700b480c02942400030407a400107021007228200383c1e2081c030410030505a00307920007201c2528a65107001d1551400d11b00b10103410080e210344124811001540c0c0c1e1314181002500407003041c4d0100040b44500c8400f440a95100304860404120050034103550070a02c0041c41c4c03810003281200c0c0c000380400a000700300c0f401650024000d841b04014244071041d203810620145c030003c0c0c410151 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 530501933 1250 530500683 530500693
    0xf06011508060f190e100b070f140c0a0b091503131b0305071205011404080307031524090509060105161106031005040b010e0a1e03062c0d02 62
    0x401c80ca420600c0c0d1260800c041e02c0f01c0318040f04a1381c03103461101290061143c2c1d01c18407007080b564000496644000d80703070005c10207003004010345d50007007143c020440040c8980f44181d221800c83c4020000c0d441c104000401002e80d2035541c0303841c10b1036030388002d42481c02180c01c00045040c0d100d40008030b9004802c01e001100340070b80951120a286036000c01c00a0702c0b00da4030180003000c2601000900041c2881801c0d2200c1455545003450031281c00d400003055403440842004003040b604000e5950040980c2400304041580c1c442c036110515054000141c600d41414031449901c1e861010700440e180b00340ca4100324181c5600c20000500390484241c0d00103082040622020300b1a42081d40103144108080c04680d48201e0001d009504100c8072098004403400303080200e45428040e82110034400e0800c000c12000340b00200d80541c006001d102400d101981d49070403c1044c01d0309035802150440410400b0089144110001060f40c400004140c8075080350110b5810001c41c10301e8030901d140d00203003 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 530503183 1250 530501933 530501941
    0xf010e06010e2e020f070303090509060f0d0605190608070312210c030506040b24091503070906050a0206070f0311180a0f1a0c1e0f06011508 62
    0x5440118401020303030410003441c6940441c80741c1c0e05040c0900844680b00203400248560001d1401c820340b41020f145510420040010a4100428400398ae2090314044144ea68a20100300304420000b02d20b90002c407070042c0e20051207800d500090060040380107048003031480e505642e06513000e0380a142d02c580c001c13120401c00519140030520001303080b400c14447c420020400370f0848441e00001021250b01c07529087c14195246c0b040c80e6110728200c0d000c111229800300891079202018500c010f50b400c0c15000a114051803005844080314010315051201044c0414a289030b00b0558040000c540c0c0444003207240c602038400c0e60341264881d8000c2c034081e96200f6045810f04080b40000003810f503220074007518034820a00801404060702803542c0500419014880003076080c1d0f000c0540b000c5441c00c140200000c4180f01c00518800c8132240c0d4a4101072070000f82011003103200c0541480d20009820790b000d4001c44c51000945180301036030100e0b0780e2030b0701c000c00c02e00c0080e01800000f68000009 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 530504433 1250 530503183 530503187
    0x109110a020c04090606032406060f052a0102161b0e040303090c0312050703020d0e01090e0405011103040f0308010605070317070908070b1b0109241b050307080f010e0601 75
    0x1000c0042e005e60004503d281e500c0e114946440c2c0507028040011340c012984241c2c00c030300c42c02203034000d000502d030085440f14603a20051180c0035460b50988440001096014440c2e145040f400600321841c0085503944281c00032900940c50038038045a08810004030100f06614030400801200c10a829140c003e941d203940440c01005002812110612129808804600324002c0b11b4650384940d16503599030006410040d1409000d08120020020b03404454007681c0d0f0f01c11004022035040220380f511984451030040d002d841c03a41010445480d002c81004180700034902003000d140d001e030b120380c003080c0d0b25040d00329010b01c03031140c5c05000300d205030f410040308000b6206440d5010400d8544840015154103d080c1050701c07560001d15026008140300300c200045482411f084266400200310034100743e9a0300c800101d40981108128030107100d0088600d510b41c0090b040800038901d80d8040c45142000601039400a54011000a0386100000c1c400d95000d058203050303411141ea5003456a94103001 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 530505683 1250 530504433 530504441
    0x30f0c0c051902092205030a030212241002030f071101080c030c030c03071b03050c010e030c25080115090b09090c060d0b0a03050a14062211060d050109110a020c04 72
    0x40c411055004c8405c03000842c10510191070071440541d0b0160361030313050000003da0040050248810b52122802d104030404095000c0404080183c40c001e42e007501c902003e078114050748c2c0750019800d40010b0010b01700144040001d031442001d0700d80d10504d441d10340102c10700740800c582e080c14a001c10030103d101c00c140390b030181d6170100c00740c0b07011441c1112141c00906079014944049011840215421071107078001e008203201e43c5400001503040c2174460703d2199650380f4040d520f40c10a0124090280d090f04100040005480d1020090101e101041b5022001525600c90600528030304600586285420441d82d8000c446d0003004040e10000d14040045640c000c41b020104d059441c4510030590301d480010200450085000d81840850b0b030501c40844444230700311907140d8125200304803107281400b908400c1402141c0c0004400c1d1054509000e6164201d103105500020200b00000d030001190040d0b03040c2e0351105014001019082081314503070080080410143e000094070460382e04003540 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 530506933 1250 530505683 530505721
    0x1050706020c030a0801050a171203090f06040c0e10062019060912211a0409050c0102010b0406081902041805030304051921030f0c0c05190209 63
    0x615081c60810003a181d07612026400001c645c001004010614010071900011324401002640c615409440a0313100c1c0500302a44414440100c08034141540030410101c21098880484140c1c1c2018100000c200020384140c00c011062800001e00700080a080701045550a88800b0888402c4e004810302060000c00c1c040010701c9085042c40c025a80d000c2102e2055025040005404615040a0040d000c0c0d404004080c09a07600a0184c00c0e00c641d04c04000200c000710b00022003240b125107200c1b400035038583c440d40c800d00f005228414044040350701610030009800030411030200782d00740000d0b1890352044080c20f4000300480c1d84c0c2e010f0b03c2110f145200d4402000058168003c840b80c82c2c1c7c001c906282966180d10200421003000410030117602c0c130043c00494403250141030341d520a04229407031060810300032000708030312200f4005c1d00440310090201e8410f12201103801401403000080c1c150954985c07103100e640d01000010340d11140111900908069495600d0285280c1084d103809 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 530508183 1250 530506933 530506943
    0x30c0913050c040f02040e011d04080d0b04020a03020408011a0108070e0f040e070509130b010302060c1603110102070b030f07140f03090606130b0306041106040906030c05030f0d020a02010507 84
    0x403080d83eaa140304d60341d58030b450448016203031801e05e4025034800c034050300083c048201602184281c10381c4082400e6200d507019005030340d04c22100400d4800340c03a068080329009400410907080070394154010b0304c03d8806000007080b0900350542e810102001c403882080c049006840414a210700c51240000c0c03601001c1c00b031541801c40030380840c0890311004410b5a10741c10516050006151412700b25810810015008200945544483d0414035041c40002e00ca24030010302c0170301c142030a0105400702004502c90888240d668203101404030030004081d030050281d02400304240340340030305580c0034003400c0f12020100d41c2d030325400b564180c0d2409159251600d050101e0f0300c411210700001d502c00d5500700301030401810b080e4180b01404404100341140603090a50389544c40c2c5001580b6641b050b005204000c20b10380d5100450204c0c82190840aa01804c0900220601c814008080212130081c0d084402d4981c148852545800040480d0401604a481813001540c8a60064005680a8 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 530509433 1250 530508183 530508193
    0x20a020106030c0e090d09030302071401090909060b0f2d01021501080c100c050616030f09030503180309180417161412160f0606081605030c091305 65
    0xa6190f440514100d41c0c050000040e10608004501d40103000c1440b041005017031a81c6018156900a52601460300450010351103019004e400b607849000700200a183d154003c05c00e28078141881c2002d8483c4101c40c500600c07601c0c4501e02d82e070500c400450a103104d502184075820140e103982201e014403001c4c16904611920010382650140320030301a0003000214000d041510911b0203012494052019400c01d2120064441c0003140000c200507038016600280ea4500004060058004280481141d00d06500e407001c5442015000380c000d501907190752014001d20190400032a5592180070440351f004035180741803c40e000088090541c1061103000045070004081030402c1064101440f24211150100399107024002c0445159031104420000350012020b10b02d6849140d00c10607070b4460051002800c07000034000116160440d199016400307101c900e9640443c20b0360341a802000c9456130004c1070000802e0310340052003031500c0c400501021040c0d960f107040e01d8404000a402519a4024 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 530510683 1250 530509433 530509439
    0x204050a020c1c03110a0f0f0315060c030314100303050c0309040203040f0312060e0112020f04180b010e19020304021c032019062007060b0907020c1003020a020106 72
    0x5100120a40c0b4043c0101044201c102000034242c50105424003c441410454100c0095120304000c920b01d41c61700b03000c43c0400080204030000c20412000168030b0302c2c0504085011580019003104480c003964051186a5442802e108289021f4810380c015140a550400c00a801350014045454080040d2414207803110702181c266841100c084801c03091039841902010303004008001c1890b20703064100700e99810180c5041c00650103000d4210820240c9407803100b1550b6220301c103200410080d000380711b18161301c62030703001102c0c0c41c1c401140d0300144100089a014121070000c2d100d1404004032282c00d4004400b608000e600291003a60403940038030500e0103045441211040e203c3c4240c0d20110000e02c8150101020600c1a4041002d90412034014881085049848800da50405000603210f00100c0810a100c0304145010a40340e1001c1031442c180461944050f00048040e907000d40e00c1e9548010491301c801c1c040c2c541691140000d4800c0c0345842c03180d400b80840c0a00c40c000019a251 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 530511933 1250 530510683 530510707
    0x318011115090304060306080105070e01030e0a0501020711120312010506070303020c0f1e1b210f06010312080105130510052d090106020303010b0a0512011d070509010c0204050a02 79
    0x841281c1c1035a0b03951001070200420f90307151003a1001000c101d0000c02650601510080203004003503c558109600c0701c00000c0301000034412210000d034000000c540d0341c9010704c4d02e0b01c148842d141481b0b00c115030082d880d00c0c0703281000c011203500070801c600241c4280e00b00707030403c0b650f90422113080c1d003010785c2480349803100601007000350300c030115500050002c21000d064580442124906150182d0800c5a003034040c613541c1c072039101085004440d03081900e024201000030a124096807250a40f0410440030041400440c07201d041e28003608080b403001d0601401030f0b4118900b0701c00c15800c4001105e2400b030460003603001e582c01201f00780a503441a50f076800051001010184a014102e001c808202d041da03808a4441d140070300103490f41c0a041d85007905c0603440e40014410441c08880010760140c1ca2440340c41100d04070b050309210500b49503118443c078142d035410891240901850b000206494a01030b80640310403690507520b14001e030300c0650900002e0300010741405841c6400340600404e600e = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 530513183 1250 530511933 530511973
    0x50309100f02131403030f31031e03050405130b130f05180d05070503070f1a070306050a052b21140d0902010e030a05011a0303180111 59
    0x854400160f255659600d003804108042d501141c5004440402908079071804026903200310000e40c503040d111411481080c80c00140c11441303d0700000c0ca110020036108002068038180c9004030f650050000b4211000d1100075028200078001c0355040c4002c01484c41e1000b9059960b01a030312003c601c0420300c0c40030911024103401480d6440d612282a01840300d150311890f1303480345101900b011230b01030441341ea41c0c07248255032a1a082100001c1d250050050410880356402e0784a240c0400d90112420030001c452061404228074a00d940041514188240560720907188000e1861180c1d610745401c0001145030327000380d00070003120b80c081603c5103000304d814900490b014074600d40441440c082c05043c02c2011504410901c110464032030020722030a070507107500c240305c0080003030002c1c41c2d030006843d8003041240700e540c1841054103a204000c3d06401c01008540b041405102d140e020703d04054a90003804103401d010307142d628807010650300c950a011303081110f810aa40010031804400b102c2c607 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 530514433 1250 530513183 530513201
    0xf06250e090a05091213030605100b0d0207021329040e030f0a0212040806011208070605090f010b04110306040c09050a0807060212070f0221150105180c0a05030910 72
    0x3650340c400800040220074880d4801c000c40ca00c440c0c0785800e00340720110809907441c1c00003401c441e46d0727000041e40f00d0203492501e9014290360711a5a0300c400c0c00d0f10020000e54400303801240149445841c00741807120030300030820344400040c0b00d244520503080601e190f40109031031096000c2d44074015040e00c2d400900062182aa41c1c64480399684209003029141030908a014424110700300001c02c1244800b04041341526841100801c0c20b500a0030314013020b029480c0058200c1b03140000f0b00c1218070001414032011010100288600c24010b0200411545000340e0f8114206040002481b585003552252440c20712504041c103c2c5511080404c03061860f40e009001c0355400108103000441c2c04001c000d03600d00c0c0001d002e51511100303542d0701c541503e25000080c0110304502c480d2000064180880c3e101340704800840d10100c50480c40751030903410178070540c1d0141d8840300f204000401483c0445114003280c88003d89000b440410856031a4070060440d105401541c0b242101d48404e0b0240d0009 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 530515683 1250 530514433 530514451
    0x40c02011d030415050d0b060a0e0111010501121524030317070509010e0d1b0e100303020a0b10050607030503090c01081501031524020f06250e09 64
    0x2407014000781e411220100c15600846030390003844100180100104200341400d540c5c5007258452145541c000054a40301a0041e80800c010440c0520603500c01e4840a41e90f8099032200741d20026600c81d00e01300ca10a001e003074a603800c6c2c8441c400100b07240d5420100c21130002040084c02c00381056031301d00064807880b0314100c40a40143c04000307042e40300c04180034425041d0741c8000c96042c01c10014104d48070302000d0a05003c0c0f44014100d5903556011106030f610b4110081ca038038450303400c400121250a9026081c2c049200c0408118406001080c05c4283da0b4190020809061540c0314139603400b900401302d1440300d071180e102007045e882d4000502203480c401d4546c04e40b6030801c0900c003400d0000140039141081920020490b4049010802c50301d071490070300300000c80c2014044190001005500800301c42e507072a100c1001500e031815440160401d1036800c0c0c0d416440010041c5e41c1b0b4aa05130344003441c0c9420480c0c45807c0a001d28045160360049003806048102044003041d03000c00c0c02c95460b00 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 530516933 1250 530515683 530515691
    0x80c070308120702030307080f1e010f0603110f040603110c0102041d011401120c0201060503011e0501050121051305060411010f18030803060a031e052802040c030b040c0201 76
    0x11074900242d0340040641c0091800d41c80c1404009081c010018011841c00720184080f0700210032844200c0c0c05004095684001036844003060340b0403195900c03940d4006498410000103001807113058900c0d0382c1d0f04d80041031826142034000ca002c0c1440e10640b209c80e950410a02ca007641c42480200018129110701880c4c0c0d0b10351201c80941d041d01680b1070b0711070031105a40980d06070392240c1660700d85100800c000a0001810304101e00508072904615010b41c0380c5130240c2020300c00481111201455480144100c0ea251401102c66260f81120380801c03003061915191804001c0e0846d0354030250700e0003e0b0130145100e4132040e20382902520305549165200440344155603100160800701482c90901111004503644091010046c1d840054138292010001c10390941d101100b10f4015500903a00c401c841d0410211303203c681c0068034045509201d00042c85605003031144080c1d424100704090a0416900d80e0203000181040007010710805a4039540c07080203644610401c4000031003640002 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 530518183 1250 530516933 530516947
    0xb0d0f0c1409190612050616030b01020715021212090f0106050d0b04060e03070302030318070f0905070309060609021e0306061611030106090b0f12030a0507080c070308 74
    0xe0909406030006141445000e40c55101915000d0207950010000525590340342801d421110042901c0c0d000440c0d445140000340d4184040001da05024207691342443c20303070880c000c03030640465080124413805a00265000c2082c50140c8410302c080c0030550040c2c509a10401e5203400d40d80e4050080100e800182038144514078804100f400c01e00c03540640204003190512000a03140c50603400010080c1328018001010040070740c0000e10281a00307412241c50710482d1030080e440344c104907607004050f4451056403510b01030005080c3d08440c00c4406801c8910b00b0103000602600006040300117060321040b40702c4c0095454484c003002446014001030700c07881c0c10031092451039007480071410a0700d024428019183e642078110303034421645180c00c0a0405852a14090010b005001180d1551074180005500380d115003210840303410844000c01d03424000381c204140789150b8a420f1400d0352041c082e0f401218060340c024018a03009280050070f08221840d11843c0c03d180340c1044460000125000e = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 530519433 1250 530518183 530518193
    0x140103050a261b10090b0114040f05070e130b010e01050f16081804050c12060d05031201030b060108071d010c0618060b151c09020301020c160611120a030b0d0f 70
    0x42c103400045441480526890340301c85803546c07010b0207500511510419100c54640c3ca07035024920602507410140228545101c01a2a00c000e032174110b802102070210111100307000b480343c03a40130003050315489802c964642c01111180c000d01070f04440f40c00104141442e070303010900c400134014403c541c5165078444c4030b03024080151a160310340780224113220510064220880590b860480681e02d2440a5070b0742400041954030342c02c8001e021400700140c0c0300d95040c4034000c00b038141c0780101ca01d6000398440c0001140d001104981d80340000f0b07c07c500580441440031450f029001052500180045d9140c0b01c1108885004049862100b040c1c1448010003a10703010b031601280085034948450018281245501d219144805100c0b004450304001031460940c0200b801c0c80c0c020b40210349404c03a14110f96560560700d88201e2801c0d1450030002820f5118072004482c041c0384c0409000c000700c03201485c0c041a04210a01018507480342c65182d456241d000c01000c0243c002c0d94519180701a41c200 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 530520683 1250 530519433 530519443
    0xe040b160c021905031c02250513060302041b02100905011b0c060b040c1e0210140402010206010915030f02030307020301050405030d0f1a010f110f070504140103050a261b 75
    0x280f60841100c0c05406c809402050064810310a915140ca804072200c1800c0c2590f003040c2c02666209058548440e100c4200b40d000b00d050700e2090341d00f042480d401c8005c080c5610500c9a00f0b000503400820100b400402503041501c1c03007485280089034076554002a0285e06000c10390030000110b807446141c0a0081d2400780c1540e00b201036a0421495040e0707280280245405903115910074000768110070302d00d108110040500c807440780108070414994410054018040c2c0741680140b02d98030011414080e05e200f04c810300324249440301c11840c1fa56443d030411407510701e002d0303070b03d40814480140942c50138010184142d1140c1c002d95600c91a1200c520119081d02c218805010310300034818050740c0488002181111003424440030340c0c030424108840d500c0d134545400d0f40c0c84c058107450b4905213900158040a9030070894060210a40304182000083c1007440044d156910642c0344c0e201084044001c0c02c151421240f0301c0f241c454510300090920351001c0c841303021107030107039280c842c2195040c0f10b = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 530521933 1250 530520683 530520703
    0x30d0e1005091e0f0a080d0510051c03020705210706020c2103091005040501140702130b011103030430020606041d070806010f0e040b160c02190503 65
    0xc02040541880d81d000c65469016a2030300d29a02080400009152020081c403501902410b01701c0725002451b01d064101e58004000081c181820240441d10002404025005441c0064030b04103035105800100078459081c0741d8180c056004103c40401c0644909204a001c1070400320f030f1864243d51070041901d441c4855200a045410000383c00b1100d941d000000381d1001c0712040b00d000301c4400a00640d0030742c1724001d10660b0182c04200201703075007504500584201e40c400d885d2400b00e041d2291141840d8400c100b0001e510480b00c024000291085034400c1000c11018074100b09520304000c1518076680c400e03507060f00c140c80e0011801c2045810401380780070507040d65500c6944660035240c00395072014040d000900c15a162004040b28111789015502d4101152085402095441e441d40751242d200b03001305840d0f102d40043c045540049010001d0003154480d0304e1001c03c2d43c800725440c035001003202800e001c12800000c0c0c0c4000d0384c0d8005241c0012107460a10320380d89031400e0101031808021007 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 530523183 1250 530521933 530521963
    0x203060910030b06010c111807080705070302150a15030c032627060406080a050601020a0308070c08040504050405030a1e1409060c030a080415020906031f0503030d0e 73
    0x341d03080c00007a10300340540e50051820f003441404150b01d80340c021041e0f44e00d1800550070049225404414904c0502028020b001c180c641080030380300d02c0ca04a50070321031803034050b000d0ba000224900e04004143c050070792040c3c0c04500002c0701c1d0459400c02031150305076402070794030500c0070b503040c414081c07070240c0001c4070170081c400000a1441100022010b0040070007030200105045405030807880e00902d4103441100c010100340d96603484500c003802204040c0c0e10a9091803500b000a41194000980a010140c15480e010100d540f458000c0742c0d01440341c6012282e0000a000000f095292806024020351240700a1a2605910000108100458142c00f0f050201450008440035001a02200500814100141c0c0c460060700898020711038290b440500d44000aa1038a031a81e100c0c20f076902071840390b0141c10a161404001d40180d0090280003a400a0100b000c55518240118954a600da656002c04481555000001c0c1150441d07180a4002c0b521000d8040c02d080003070090000c3c0303200038 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 530524433 1250 530523183 530523211
    0x40603020a0b07050a140d03051006050f030c0c010f0501030515061e0f090114210c09130b010905100f120f080408070f031703090c040f0f02030a02030609 68
    0x15030001854120720380b0610303404001c00203000c1d00f803200501c80e011185401400c0e071000400b0b00310a1a42d682e203582c41c010700080c41e1202103031400b4443d0482800b1a406032741c41d28204200789030f212500b5031025180f4200000104500300c880d0f90b0a0180f20b0000d51000400034042d850350400d142482034030025030030078200071403c0051545c0c0d01d01c3d001444400346031941000d40300010115401d0325100d180107500401030f0000254a0b4032006204000403c1a100b501a000c00c4460440080c0641b00a6205039000084141c43e20304100c603d842e0b1000c00307100642403404182d03c032092001400c2c2c01c1187d02c00c1c1c803403080005107800c4600c054020007003400420950313403500a480751842034500b00105022054165003042c00305c0003017914094802d40050380c14550b40c2e1000390000b90898402129403010041d80d5a13441030a00c1c0907a4803d82000f406450304141440800004180304051030f0036480c0c0d41c502504580040d0702c061031282d03549000059403800c081e0300704800c080b0000c04141c620000 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 530525683 1250 530524433 530524439
    0x21c09030c150c0605070c081314090906130309031b0501140a02030403060504080405060a08040611090f0f190f0f05060f0f1c09030305060108070908120c1e1b0406 72
    0xc007441d0106004d4100b440094541c850b000111481c9203c100003a081010100e56a04104100d110f160222441103c813035240c50800411f01a99160883d50405150030290000d07084042941d00d80700300521914048030b1007900c9650317080c0c10300802e41072409a01c0011105210350350b0407910128080e41c800184ca41040000c000007907407840345000040a5907100d40204042042c41d5041d40d001c1c01000704442d8035040800c9004000762422181a2071075130900c00c80c0a80008a81c003140c3e03804901401c91019409074009020120b21030507c07043c1c0003418600125132000e0200110005800a207110030b214510b890f194442c03015290b00f0446c4074000c00c2181c031480a40020807500303101c9000001d5600c800100c0403031840c201401c822002150704001d00002015410380c001c1d4482c040c00d03210869580c0707a1140480e40320085000d014441d40c406198841400300c22000303400350203400021504240107124600c0c80e41c882c4400c01c015035510003004070040001c0040700c110f4a007002e86041000d280303 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 530526933 1250 530525683 530525687
    0x901020904110313030e040603020612100f0b180f04062306040b0909040809030303131a0121080904060b0304020312030603100b010320040f05040e0d030b01021c09030c15 75
    0x35201200070181b0110344540d00e22600c840e002300c4020342c0c008040b2511000880d07420410040c3c101c2d40c00a07072600c0c880c00400e1540b111841c5106440c00f036404181400d0070540030058485482c91902c1d8403052100d030880c1e4580d100e0042801501543c100c1c140d501195000e448651003085640910400082c4000d02440424009445080030111030524035625a402c0a207864030880e41e0941d0035000000c108004c401c044920701c1c05d418842e85090f00440e01e81c020202e4421000e010742d01091940032400c10340b0a00e0715070200251809150001e28080200000508581c080c0d840062a001e000c020001503260a001c509030303070310026000900c0e500c1c1410020352152075900391ba140441d81d501042c10164400d50090030110104038104004034401456111660028440c140c0f100d0001180864103080500510640c660b10307100610420000e00b80a8000d007500300691811403148400100e6030760700440c00c0942000351500d558a446007107007445c040c0344a9035007049094043c0d0564041c80f10f5 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 530528183 1250 530526933 530526961
    0x4060b0901030b271f300308040201050913060305100c0504060e0d032604060c03020f030a0e0c10180906050609090a0f0e030417060105090f07020c04020309010209041103 75
    0x20884c420300c80c140e07960b0482e01108416100c407020128001100001c1507400d1090307900e0301c40e500c94034940c841501410801c0c14002401e420000e0008482c040802d0055000e00090301c43c0260080010f44460b40c4502004100e43d40c90f44107541650002113203131045070551154101e00c83c01c91410078a000e0038502c024141144022071280542d40758040201450300c186003d0120040c21284010710344c18500c022200c007202561700351030f841d15050044199501a1085481c8041072850403070842e40c501c00054010507081c2070003425030158001c100080c1da0f070b081101d082ca000342c1d242d400d4006004103004081381441e400c900551481c1c201e05100903a81d80c001d80da0030700d0b01160001e00507500c0c1c44004003e405111043d090603418060000740d0780d80d0100c0500f082e541400c2040c0c2c4203c44d0146d00a40d0b5140a200b800d8101c0340e800701150120808004d5298801e2842c011224180412030116049030720488120f5200c1c3d6020031920750034034180c0124440540c0c299026400c500341002c400707001c8 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 530529433 1250 530528183 530528239
    0xc1709040e010203010e070924121407172703090306070c06150b0301031103100606020d0809030307081609030507030b0402091b032d0115020609030703091403010b04060b0901030b 79
    0x88445130649d4010300c100070480c0e84505200040c0505a0800b03d0150981415525200894518210101c10224860506110b40da140302d0f80801103160265071900d00241103004041070104004021054404119032400f6114980c3c1c0d01c60849410b0404200321141c11050b48a02e0b043c4100800601164600b500c3c156500004960318400b5550002440d1890407041e150203d401e107c40003a0307481d000f041c2c81543c248151102c002c40e540c1d008031951a44400c450b0b600200e0141e0b000b06a00d1f80c031581c2041e20501d0203051080c9407030749940b6958605075590313004444100d2550200421420800c5559422150351f0030b4030344140f06560720368112400000c141c00c030480c6580d01e10185048207007150b00e0950b0030741c10140c2e075507503102c03a108158880c501e0703840401b5105900115000c0c4800001301e0320380c070350195640104c640c1024923500d1003060748544a581036407104000c41441c3d94a00c00c06006103a100013065441c0040320014003681d02c54540d5910450a1200f20508840041c85602c4a = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 530530683 1250 530529433 530529479
    0x1906150807050c010f0b040b01030b0a0e04050f12031008030c061f090207210206090c09100e0a060302031006050120070e040308090105160c1709040e010203010e0709 73
    0x29644005044503140903c034090806582401340449a007840c50344803018280302030f41d042c0314060a580064003541c081250321504080700d41400c001d10050700301e100c5c0c0c201d03109005954a11220f070307080d60301e401201c0401103030b40303a0000140310020030411203000c001c0111038043c3d0b0408a64054150701c030380c0c0040020155202020301c0030100a0305240c0540030740101c0000f15111511420000040c0007980c43d07401244203032080700317080d40c0d00026080c5e118440d4038008281c0d0186010038000b2107940a01551440840c0d01e201141d40780c2800c0c2080d200e11000c8600040701d40c0b83d801054901540e900e04415203074a085030502880c2d030300441c8100d141550710580304c80ea034000380c5083d1410070150700c45122080b040003070000b096441001a400307294840024009a107800c43c1d5180011080303500c0c00b000c100b0410702880090952012801000c000d00a22070170249224041020b80d4001009a92144d40c004014052280380f1240c00c0d820862900d0030b2818207007400d40740d4683e001d581d40d8042d0 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 530531933 1250 530530683 530530697
    0x70c03051c0605100c0605090a050d030f0906050c0a09090b0d2613090b0103051510020703050d21201c1b1101140622060806190615 58
    0xc440716030403407401000058201442e040e071035140140301410345036080f5489401c0c000071a2500800180482030031303030400d01030400441038075001e4004000c0c0410768040c1c0d0761140101c40100c0e40707502c152803280e88140071180d981e800b9080c00801941d0a90820042c44e85044020409500c0c1e10303500016040e4840460102e140314041103902c0c4903078040740080036603400503845104456521601c070845280700300038042101088010b505403503040751010f030300030000e90740303c2c24501c0e1403001d00c08110340310700640e000d071a01c98840d28244201c0421000101e9002c01103400c00341410307002a42c412400304400c005100908008418814200c1002d5403010000314405000f0103652056136100d0200301001c00004100c100b41000c841400b050b050041805c0507209092020180603030340e0001040d01e84005540d03a09030400c0350f00e000565010700c40012a5482c841c0c2084207104107c0038100040c010003584c038000940640d40b02c468058003a4181c00c141c1c003000074000284003c4003a40781410010 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 530533183 1250 530531933 530531977
    0x6060f050a0909110417030c0a020d0602091f0e1f0f1215051e240f031306050115120f0b280b070b0a09020319030e0306070c0305 57
    0x50700095140c00c0f10103e1071901d2105000e03071030020001c00840707803211a90380208400c0c0401e45d0b220701030403048042c2d03500509030030001481c00c1e01c0c007144201d1060341c006040200900200d0741c0c0503a0080130800d2820003415040e000354012030f0044c4420003c88a11410a4403982c1aa00c101204d1001038240801f00103072141007409090803107035820200c20104194101c0400e2005d04181a101f4180124511016072800d0704030400e000d098010090701d2103030910036000505540004c0603074566422002031041440449000300114003840d03542401d80031101d5141040c0c000c941c0107034800d050100150781d50986840e005040c9040a02e03440b44005207104072481c42d203010703000031155298032a503c015809103202110f0300025000c59944046814240c603070907515054441d80102a0101c0204800600311911642102e2540c1e440a000e440303e02d00d114807801c2c84d4101884080300840c5101c400c4001030706041045030340c002010310340202c00c0e94a035200682148560309106100140801c141c0e = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 530534433 1250 530533183 530533187
    0xd02030a0204020a052101031209050105091212040e0114060901080a0c02150f0906010f05010c02090901061a030f0c090108010e100305161e0f1e0b1303021306060f050a 74
    0x92240900c0401d070f00484000e1b6000520701c1010240821643e4650780103581351018440c420300f00036920306849903440d1910240030001c44404014603560b00f4460004d035003482c5003184000d04010032a4400d054501c1d41000b644512045044c84100d0103280e041c051030020703030fa0151025801c50f40380300000468103a010812800c04038203002c0b10031460b030300b03200340f000d210510220284500c2104064410a0340c030f80242070003110b40c078840d2070300123011101b00401500e0000e910b140c120020b400001600d9640351100c040b8040350380c080703c1c1102c0020080081500e003c0700c071030740c1c00000d2030031030b0f072030700342c0080c0040e00840041c0100c00342055603500207802c138242c04000c1d03405960407104032402c03502c030b4280800314107102d0301411078030b0342c81d0f0f400300c0034100c110703c902005961550194944d01410701c4070b40d928100d4001440403081e52115000100004c528005002420380c0491a6002d24291f0040c4050341101c0c1080c3c034007081c82c110040041c15840034141070112214a052070341e034651070b81c0c2 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 530535683 1250 530534433 530534437
    0x12010207020907171005030c19080f03121e0f04030c1401150e0c0f030c040b0a091d09060f06060706060f15051e09060d09060f05060d02030a0204020a05 67
    0x9400950300b80a001445030441091003a030500301c4280906a03135040c40741c0403072010b103205260301580700d03422070750940c50080da001c00c18506504107450542ea548440614025818682c000c0c650000120030b001d94103031140e040d60290f450400d60506524801e034458200400511102c85d1980c514040740c2054400c210620116400512441500300000c0049008006454120308000d0030000000366500c450074500d4030070414031101d82c0c141100c00701000a40d41c0001c00380c1501100c10003020884c94040070140845174415074540d40e0082c2401c010b20800b800e804407082d400040e0804000d91150f0009019030320142d00040c0c80c8080e11100045095405110780050001d1304104011421406030602e10013241c07001c141d441c60072101da00c07040d50310b4814804660410706102848950786508040140400000600316a10700400840c000c021502030001c102c1d078403521401c1031029001036004d00780c0c21883c111040c1180d48078650000c1d54070b64034000001d014a4011815106032401241 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 530536933 1250 530535683 530535697
    0x121121040525120c0504020a080603060604090510020703140c030d05010918030e0103060f0e090d0f0206070c0f020d05030d05060616030e06070206070c030311030307140904110d060603140c0702120102 88
    0x21f40d04d540d020703540680314080845101d40030340b003400005140e524060081304623880d04000a000c400001d50364100296003d414150b003484a215083c0603c500060011301d0340c0840c06015503264240e2080440c10b507101030388699039860400d101c0781405c1d90544140954203525040c2240c901c258038005a000d080740ea481035118828041c2c2c00140e01e9101c05902e84201074010a49090560955064441d041e030481000d0040e800080010040d0b40110402c04007075004022210740201c440d4001091091410022207007904040345a04501001d8081c01e504800c08844107801c088001d00c29962002c000b960247c10001c3c4900e500050b41c450f40b040310a1250040c0103595504084c1c00d0001d03041c000c0344012400107442c4e0013150550701011084c3c9003d28110398a10a0b024070500010744550049030344998419601c000c2d414403161050000d02c00d61480c0c020200d201441c0c09400390849210106a4544400800410910b1602c7c9001c132200281e04546002610000c81441402070090348 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 530538183 1250 530536933 530536939
    0x110409170d060602010e010c05090625030e1e031b19141315090e01022106130510050d031b03030906060b0a121121040525120c05 57
    0x1070281007400c0c158000b10191000c07900240310850000040c1400c90b1000d60a020005109001000349850404010882c20000300f00340f040502c81c0201e4007003c10040c82084010403c00800d8540d941400c9180328020294100250071440f00100400d407224540580e03038289801c0a201001250b503202403011140d03841003480b0419030740362503424009450002e040d0348201c1100703203160045500d600a041c1183c40d0307440800700e081c1c90005000040c0000c80d54503a000d540a02500002c13801820b6802da001c8618417140341c841c20318000744110020503042e5969940d050804000044104d54000c6048801c262a911b003500c01030f050449850031201d01410102d21040e4801d2300307042c1e15410140440f4050001003204d59501d840c0448030344600781c400e002181c0d028a905a86c120a640001c80c0030032001d0b0303014035002e480340c00c2c0310100e42c0c0d00d0480158446550b003440306221040000501c90904640303040c2c40c84040f4800507201740401e100b100f1004c03400141035410424240d5080004060107 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 530539433 1250 530538183 530538187
    0x1801060b0408010e12031005010e0406052d011d100905060705010c02010b010507030206160e0a090f0e07030201090b031b0c0606030d030203010f03020108060a03020307080307031b11040917 83
    0x100581800b0304402448030343c1074170464440382070030b02c1014100c07801440c806200718400d603e0100151000c80301c0c04100ca0b4442e0f51a800094951980301c06085001c16840724004c0601c0040e03030704a10241c18680716410000351991920407804448200303141c404041303507000c1c0d1406131544111901a000e412280d001640030034001e0411005420124010000740c00034003442942100443c0d90740138400c0c02800503401480869070701c3c0d010f9649003112181f20301d005240303103079440c01003046c0652690049800382c1c1d80316044540f8881c6481100e00f440d5444024040341813564000a0452201c0e0149917510600000441c0100c12a21b02650005c000d0f82211031321600028a4640c88400403a00303640607008144004401c64803034130803281611100340084895905607001181c072010018078454000140c4400440581d40400c01c510050084000440c0d42e0803030f42c40c1c02041c0d0101255400008400d5918000c00201c039400c24125044041d10002004501403d281c0000103908a940280c0c0d100 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 530540683 1250 530539433 530539439
    0xc0c06200703020303180c09282301140f1005120109240605040b0a0207241b0302030901030b061207020705040e031801030c050d060b1902060f1801060b04 68
    0x1001452054049440c040c03089200800c200303445071f500f100701c3c46c0e02000400001e202c4a002d14039022100100140c4c058490b40180801000c0703e0710818170704003500450100ca40e414515851071805000880525440d03070250101055198600711445071003504c081c040000341900c0303601500c440c0111924140020359454201d03074010700003501280c865000c035400040c0403000101000040f58980d556440c0b41034074003c403500c0c207500419401802c501610200091080b1020030415160900c0071035420b5082e20b0300c03409004640b2010001500080e45607190300840d03004030548045c81d0080c04c0120784004290002046845030f0420140c0312002c1c0014031034540c0d4001400c001f603942c2618200126183c2d252019030782d01035420b841080c024800545040c80d4440e400c446203004090070840d0070302c1400c2c0f907500c00740c0748980c200c248030841c00b1420144402c1034091242504085002038141410607602000c03040c0750003040c0b500700d500200144681b00a0940c8050001c000d41c02e040f54886403 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 530541933 1250 530540683 530540687
    0xe070210050f060f06120a11120f06010f14072301021315020f070b0a021212041205190c05120d050a05010e0f01120c0b030103050309030f010c0c06200703 68
    0x40240d543c0ca00502c490305031607849040050803103000140d001008061584ca29681102401c800c106041c040356041c4001d01c8140c400782e40144c0241d0303096a41c00c03201d2610740e0004000079018081c001c200310103813003041d20b504041030860340c2068103e2541081504290000714030200c001c041e840c02584000b4054054820781c0300f40d6816031f0322001da4400c41582c40b01f8102d0f62185a114809032942094500b000880c408034028182c10b100ba006072201100404160400c0e07421232120419a002090104070400605051542c8400b40604109003001050b6080e1503a2225801c2d420007030101c800ca0310390902904008840000321110805595441d0b40c07003407140075000544004484034240000440e000c254409141e101c1c200c000503e002d82da00e401c103641380d109640c52003070b0f9130044800000b05050a0080040d03020390b0141c401159100c511806142c50044802070700c80325645003103c409030050f44079080807a000d81051010840d10580803c568601080c0308042840707140c00030b15441059 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 530543183 1250 530541933 530541961
    0x15020a0c170d030506030d080402030c1810090516080901091209030c0b0403020607080a090f120210090f06030b0105090a09050f13020d02040522140705190e07021005 73
    0x101a242601c4200070b01d41c0d07098094070342c103690295041d0098502080c1452148450991040c0000c049805114854010484046121a1040e090a100c004020011443c1d18042c001414102010011031420000480b4440340c94203514080290074804107880e203c094200082194000440d1800b421078000d01510401403031200311240a0540800295101c07840151011650050315803480e044c00c6075100503540c3d101942034401d01c20340340b9010505440300210340b0f010b00f0030005035100100c02070040003030300755540c40b5540400916030070038030002c18030201040c1110164103001c2940d52121005075030700d00514180f19006070b1b100000242c1d0a01c80d4000c0b500420003132405009a841e4a030400052045442020350400743c3e2100d0b88005013070561101ea402042d1140d490070003580f524501c50301c8104241d0a4610345420802d2203003c4070306220060040c4011180030360107500c0014021a811400d02c03880d102900c03110000340c2028020310428880c810710782000c001c140f40c01040f0340a44 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 530544433 1250 530543183 530543219
    0xc03070b0c010e0114010504020a050c060a09020111032110171c09030506130807020619271203110f07090b04090807020907050405030307061a011815020a0c 69
    0x1a6007019a0300031150343c18410250402001c81c00c1e000c4503800e0109210196020054003000c00c0400c1199806e900c81c2800074600400301142d01060b900003134000101002c0d1101e0350f03100160410413020a01c0113134002c01b100407801c2e60201d10051703510300e550700e0b11842ea580e000c2400e840205443d200070b03a00c0802c10b400c0309065004a80b0140341d071003204031414040e40c00000c0c0103600150216000481074015020001d00caa22501c0c50101a0350101e000b50300301050f990352400ca08010740740c1054005070003070400701007010b42d60403c950f41c420182d1001c0b5940318011aa1a548510308141071181900c00c440c2130844007221850000da8a00a07502d080d140f0420711054a00541c0c9034681c42c09010f401009900b0a4100e424684144c00b008007040001d040c0c1c1080c00002c00000900c2c0e101400075095803802000001450720b10051aa1110004503140c40e0401021180341a070903010f8294403004c1e159241c505014407108828142d2400c56100c8000e8425502c1d51000110143c008440d42c0b01 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 530545683 1250 530544433 530544457
    0x1303050c030c071d010e0f091e0102120a1a0d020402040f0b030a0507090e010303031d1603050f0c0108041b0e01171506100309030504030c080f0f030703020d110c03070b 74
    0x107641c95540800382030140a00501c2900ca5111001c50b1f40c0070015543c15410619070015240a007072007160a0065601c0f03200c1c0c000d0749940100700d000d0780724002096940d01c00300601b02030010318002181100d008150070600746c0308031003039141c0b0410741d113071981500c0241840c41e44a0701d5a540301c0c205920360750070849184100600b071030001810713103100d146110115000005030800c280d003550b4042e4043c0012f00b00440d031188841c1c0d8001450070b0100300040300c03000b1034201d1400c8a800c5003099810a44400600b0000d68042c9a403101d042e40d00008a1ba406600448020490340c4180c1e0300705500744c00c84e8400c80b410900a0004603414900d8001d110307107001c0c1801181c0743c00d482e042303505c054407070202d5042e640400c121000000030740c000c1c0c101c900524400d1414506c3d054030780d640c5c5082d411203900600d07026800243d052000b0303002040718080b408020802035040c808039503002592000039503840c900700001ea00c810f8142c08800c02c02025440001001c2d2075500e519610aa0703901d0b040103100f122 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 530546933 1250 530545683 530545709
    0x19051204080705060c070b061c0b1005030714152802060a050601031820090a0c030c1803080f0906030702060403030c0504060210020c120d050406060f0e1303050c030c07 74
    0x10940d01c5c90044510f0b01d94000040c10356035441e0000c10002010a02c10f50030000550484440040c0d09504503500c5020a408140504c0342401d0030b241c03800c07045400c0ba020140000b400a055a91030000100410a20f0100305035180e0101c124040c010801a0490b184c0e200c242210204103034001c47e64a1280e0071001d02001196030302c00045064070303580b40c4580c041501d5119004c01141c08070000c640320100c0301d060a000d4000e190041008032404480314900641d440d07020105d125454080c0d402c1d06107046c83e0030031501c201c1903203500e03103a5014800140600710016481380403d1061084d00d050500041c2590f80700e10f40395501031b44408080741c0880000745005c0d400d00c40540190182d0342940e844d039005001d10250403032110025845121050000c1c803840f1000c0782d501400d20010311080c682200d000c2898142840e11000f510001d82080303030200c14954003444941c44041500d94000c00e04864507d1040075810196003d111759800d100d11030000003900400c0a5000942404503400030000c25 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 530548183 1250 530546933 530546941
    0x3060a1d061906080f04020102330a0b06030a1e0501271e05090f0d0c0c081f150b040902070201091703031305030409020307030c021b061905120408070506 68
    0x400c2c922074081c1c03d0104240e4000b060070208840c40c80d40c0d00902c10b004480b25800301044141405207400d084c820564403200808140d001c405441c1070300842811418008103188400245845c04014141c03038549554580c0000385a401e06000401801001e1040100303503103400a100c030146c515044010203480c00c4080a03983d41e068030518081c100340600702ca90001d2030007a848041c1802038807030030007445220900c000104050042c0c010311212915000b441c0e04142c9407507903903282942d0141c003030341d08101f04443c0e8030204441284510143c10100182040c00c1c000c80e14424010348d08000c400480219000c00e070341941c4c0d8010b0a03c03031f0007603c2c1e038020556119220500791003140800300d0b55410078404180541c000c54507180b0f1486c40744050300e04054844483c1d0080341c00c01c071b9081b030002c1c0c2c41300712175072840d90180081420b000174410805410554500481d0301c1d4410b446807003444039103007240c00c00014030400a65405071200c4e08d07000d5450a02d400c00000c42d40020310292028001d0601003 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 530549433 1250 530548183 530548219
    0xf09010e0a03120e0a09020a0305040b070c0f03142b0b030102030103020616051507050304060b010e030607050d02072118080607030b04090b040b040c17030306040203060a1d06 77
    0xd400c03030b40d00c0005203071034a10f00f0000f00d8120402d00040c5400400e1404045024900ca00190144445aa600141518160038103d0550704d0103850706003840802e86035440852401c825070314080750941080c50388040075100c607040c81d118074850841804421654600b0807034014204c4030b1116039100c400d0100d45040d4041600301d02c400e2000943c411000c01c90010441c1041c01d16103c020301607800d540b60100000366610012608030b0f03810340050000001c000800003184119580d0010038a0021403008210340400d0755244082d140c0c5040c80310100302903c001103103804980120ba4098115402400c042c1c102c08106e000703881c1100003244141e007403d00140c4003403c0c0a4125042c0308020052901e803840c007640204424030f050b94000e81c03070304048804618a03000342c6020342c0c80b52002c0c2015284c5410890003041c4290054241c00c00030044002100c580041942c0d0442000c56006075030303450b0070300060403030005c0d54010806100444004000300c020704640b644204019a0f0010b0075140031641c13 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 530550683 1250 530549433 530549449
    0x50702070f1a1b0307023f0c0d060b1002011d0f0a201e03010b010806011d0a0e071211040f0b0703090806010b0903010b1804080a140f09010e 62
    0x1001c208102842042c41640030303500f000032a01c44190540c0e2526035646c02242550105140c0d50725011204030054038508415060a8440b0a441040c01c64101d8120322041e150706222142a1003894040584410f100107039004402c0c00c40c3c001c00c0c0c07040d46003031031001902070b0414032013906811030b9404244030141408605c0c10701a042c490090700359003483c2e035a480a2703110001010400488401c42440356074403170004903140c0c1505103100d004e10007100c204146c20b40d1101703805079040103052418000141d0300704410006d0389170b07400c9007182c0130000040800c1f0740440a52201c0001103401b402d1055003038204440307441004900d0f0085c0700e00d02122440003400c0c80b90707201c0c40740003280007041040351180c1d8034040c001c014401e1a0194070070355150445072502d5400c0c0c04c4102e1100002400300024a000d00c42c01464100c00e5620b00c0003150102002c111150b80140054040200007540c82c02d901e110b114a60307403101159a600b91104420460304003d500486a0180415011043c2d45090302e000340c0 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 530551933 1250 530550683 530550719
    0x5010608071403061e1906090603060219020a08090f121504021e061905190504060f030b090105010f0c14070f3204110c10060509040807021c0204050702070f 69
    0x717001d071903607220448004001351540d050501c2580e910580420a018036004003802140100c002584504032030f800c40c0750041e0504c2da04010740d40300302e07000b10000750180b055440c0c81c03c040f80c10381490b22a110108180e440c1020070481b007405507040c01c0c05015601203110380035600aa502e071320120041024001d080d0b0078595010b900203070500801e00301400340c1c044c0041c0c5080c40d151441c2002d0601d8002001c6090840c0f9503000f0650100f400c2c002a6884118074541c80031345c0c901800380b24070502c04507200c3c5106008132810409074180c0d0109036400b5168920159500110518038452040701940d2501010301580c8000d10010034001001042d030100244034032981206500032001a1504001445040c107407550880d8944501c0755010741014094100134140d6070280c10304901e2000c031001281d0498001d54401c200040a000106035130a05031005103074107489010017030444800d51081c01124580003584207061004102c05c2581c04212130701211034040c07654a07802d455444028103451004 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 530553183 1250 530551933 530551981
    0x801030314030402150d0c30090501060b0c0615060a081302130908030f10030c090207060902150c060604060501020d120e0d021b0301050606160501060807140306 71
    0x14120030788060014000c40d005880109414541c01a01068090a80107920b178041c0a5694012110b00b260f0040782e140030399202410710b80c0c034000d041850b540c01d07415101440340c44a990b89001a040110940c444805440d0301c1060503190b900141080b6034401040741c15070003580300311010709181c0c2001826140e607a200b907101d52007540d80c0c0c030190711101d07a0280c405980c881440031847c1824596481080220742c0a80c1d02c650780d07441d0070743c4280e0700240013410100010550b00420070126051000341400d8032001c0d040940d6803915801c0040150030400340282d0b0103012004c3c0800c0c00416030340104030301d004100070740380c86a50b03a00801046517442d05c03521b4096000340d030743c40184074490001d250503d680760f040017495500d1015918a8400f150b1600b0026900c0300ca060f030b440c040d024840c2100e001d4128028042c51070040042007080c0541418118500c15034481c0340200042034120401504008048902c240d54502d0201c918241d10012240280105401f191099050022500d0028016 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 530554433 1250 530553183 530553197
    0x7030504090207030905220b060909010e13050d050409140121060e010216031206061409031e100b121c02240609091b0402130e0a0203041208010303 65
    0x201850000c3e600081045080007103801001c0b50681e125142c0444059032140030040c040b408000c001e0884001c00412885241c1c02d000050003507a5808010741034611405140a032504e50b0140300d894030905800c020702034060b00f00b22102c0e181c2c1c8100500106c940d00f2a062141c0c01c1002c0e110381c0032020a0154010000300d2030f5081c0503000c200d007640c07025680304c2d04002840040078800036089070000a900104030b101c080908062691042c000002989580c02c100032161408001810080c9c840e440c41030000c001040042c0640da00b4008581e810103101c1c01c4840d04919844401d455104041424007030901d8100d04c48081e00b0b0401c000e441c50b1030550010920028001c40d0a2380306000d404405d41142700311140201000e5010f91031008100f010f620008050070001e0801004c4440107010000f0380c0e021b624180541030b10320306240f40000c400d840041e542c0390707013060007030101e000c94000003818a40d540500c245400d142c3d00941c400d60003900d598040560201044a0840082c80040c0c0042c1813 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 530555683 1250 530554433 530554439
    0x1302010f030b1c050313061404050103271203051005060403020d1712040308060f09040b040804091503060b01020105010e010b0d020706090f140c03120c070801020412150207030504 79
    0x3a41c40002c140c2401014582003515191031503803600c45044040301d02da00b0105d9009034a11a400004019041c2820f049810300c40d1030031010420300991051034100358840e001ca200c008080544500c20100e210122503201100e410680450041100f07401c0009240c00000b48003028401014829245c1c0204154074061561b020001d20607818541500d03a00f40040c009505503008000803c81902d14280c98121440e16003001b40c0b01c202d0052040c0c0c052100c58841d0b00e42595085900c0d54407542c01105100701340c0b03440c00d18010601480d009440c02600e091009401c1941c0360103140201e921034a000e009040d4414012401c1c2c902c20f2040e07660201d070500040c0300403801c00021b440d011014000050801c0e2007902c0381c5c4107560400308140c5100c1ca20b00918024445900303500c0d000c24031014020030740c0420203008259035030520b01403624207040100b200320aa100610003003005040c40d400a6485a07201c1d082138820814004040f24000d500f8213000010170a14003d844059425440d8541000c2c5 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 530556933 1250 530555683 530555687
    0x5030307140106120c141c0b070c050d0905031002040303050a0804050109060207230a0b0109020714013305010509012d05090f04020c101d120a081302010f 68
    0x441c0038210819540b54a00444e0380e0000d0030030024a940183c1c1001d801600d8000b0395088005451000c6006e5403480b07180d80d5140c02d05100c141c0c041c55002d5030a4646640e20f4004485000c58200001d1103409034091401029900054003010b07614102c09813a8540c1e03140007000201c0c400c40c0700040210b030090181540c0580030b218000e6106010344000b184280c035569602d01280c1c080c41c01200c503001064060140320102c02e010b07611415030480100180001c03a1103500881c0f4052044010442e00080c2210401041b015440c949401403c002d03c4045504840d2000281070004e80180e01494400b030f0f0b446010141c0303220400c03214103860359460585040d004403680c40944000003000030741c05540d45c01010401c491502c1280265a8007610784204a08106041480c9410740d84124010300010088034000301341214084030003074000034424030800040c49400c8502200d0605030041e0515040070302c0b0714100401c0121740f52b50742c0300c40d140d0320400020240d08111402038005000d0b81441c000d554 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 530558183 1250 530556933 530556953
    0x9011a0d0f0305070605010801060f1d041203090803090303071b0b0601081b0310150302040b161b08010b0a0905070f030c05090a060e0301060b0a270510030c080c0405030307 76
    0x1a02a1403c20b1408525403203600c1521402e9203c66032503075541c9002c0080102424085000d480e43c0e06113a00b01941c201c400015644024002801110000d1645410035000358000900344c3d0780712034a01e4580c0381c114012601d81d04216141d03c041030b0b031400745011020080d0050305c000c65000038031510700d803141001102c0010004041c0070300994120001c001c0c034006403014501c94011078a080f0b000b20704000c800340c5012414085081454014013080c40400392034010398001020301a40c00d1130318412420481c00201d0315185681e08224048808119501c1c1900b1000256005803074445185946640034030889400700c03aa140010300008540300e03018800d4022140140040c5403242c2413403840d1000844640807a40841c01180e105005059241407c1c01050020041c1500d128102542c055003e0440400800e0b0500e0002d46640000c1c0803a00110703501024107000307815459a4643c1b482c01500600e1840c83e4a00031410000019544006100031641030303800c003034040e500b0a4200d03511640e1030703 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 530559433 1250 530558183 530558213
    0x9020c011107050105090c1e01120209190e01120f0303020903010605040507020d08010e0f0c0c011401060c0203011b2c09040c171c0f050909040b09011a0d 68
    0x29549a08540c84206100c50280ca00c00c0e0086000040a003400084130385002c0d42010880c2c05403036034002d000c81c040c805c012640f0b0301610a007009000c0b8007031401124001d209042829602c400380e01c5c02180b039805081080070540341581d04080950740c0301d00d00c0044541c03800d2401000750070a2646800003d1098020704001940640081130550329240050103a480403144030b4010381c0a0824200704c07540c041c01ea140140902400c40c010b80c00c010710105140c500040c1101c040104c0018000746e000b900358000c20100610320902d103103a58403108000c11411022005074443d41c00c051744903900044155421000506a8440303045200c58140300306a910351030a100d402c44005040748445c242c50314040c440c4680d2090084840e0765090200d0080e200b620366040311015400403460004803800349925a00d0400c05050031400c0300b451820840d843d1180c04801c1c0e400100b20000d1004005508000e01d009001280c0203100c9000403010005154400c020b1142d446240420030300701107001c91642c0518 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 530560683 1250 530559433 530559457
    0x402090d02030a0b1e0103051209121501031202031c050a1e020306030124030201210e070501080901110909091e03070b06010905031506030c0a0803181503010902 71
    0x3004069800083c200890240240c580c12001c2c0c0411060f0355204c0c00c5d0303010741500c60605603810b5055440e1640e9841d41000c48801140000805c80107035550305231040302d06902e0800300e611a6110809030b05800071b080c4401c8800401d070a410000d90341c004029120800315403d0000e2105400c60b903000d0181c8005004011481e540307501800102d440f48140007144401d0110151b600e0622405050840e218480c4070703103078000031101e5404160240300c1c0c494100d07034091810b251401c1c0e400c1c0846031017440a0460b0320300c05140c1200610302401c08104203017111000d8941c40441d55a61111600380c44250600189580301004030300006d1420b01059074210400004494040c001c0a160060f045400701400f00c0c15171000c02d101c0100001300d400254451001c0c80c00419161500d00030983e640c5007404000d00c3c44400c5800071700a61001c10510240d020700070f1101d4405a561001c2e55201e0340200c044240f008240d04201c101800c0005403028060142100c8519513841c10314040c0080d0085650825 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 530561933 1250 530560683 530560699
    0x603030e040e15100b2209021603050309070e040b0703060b04050607080f0c01060f140301181e080a0c0302010513120f0210061401110c01091406040b070302010e061308030402040209 80
    0xb4600031170401901040d42141201c46092883c890300044044540d0302c000382042c0100190014581422070340b50059606060582c0c6075114840d8107800c1141c0d0b07422501c1040440303000c00003407002d08440903010710300e552802c101c1280c8440c405103180c402d90180d00d07088981045004000354404004012144206081c43d0a048c0d044800c03900303440f01e0340d10036400608a50018402143d005400d03001c0f0701d0046008000414401c2070748802d000716900302400b101240e1a207124100b0030341546c40c51903544020469518a0207140c003602c400c00700c50080d0010b61a000c000340081210004528403550803400180050060250480f803014a01c01e0035011409040445401c8554501a0300c028002640300710340503c800a00041a007514200529515070241400b480039903000f1204000f80e0780100036200102c5501300103d840ca200315807140c08090b01c0012640d042c9031f81075110300c1c02000c10000f540c0f900d81300c0200c841e015103101c0b800501812010408103005140580c01401e00714801780c8208 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 530563183 1250 530561933 530561939
    0x1140406090c0e030d0906020d08060303131e05090c16050f010e030909061909050606121603140103050607080604061d0a0510230d05030307030603030e040e1510 71
    0x54902c0c102d06000454400141c4150302d20b414030075850398510525002c03015600c2c080c0000e44c1c1d04040c01d80003081c4071541c03001c01d58545042c0115251181e10b6020310702141da50f100e1000358500d0500c03008500d074485084c04242807a028281d503005100e104080b0b410424901480081a00340c81c030700325401c2c842e62000c00c02000080c018481c160f158600a50340701c80040d000c1c04003160001f40036511450b009110b640240d2610750b10b103000c0d04d90310341c2c1c0021295108001b0840e00e00c591803415911160040c200424850070f6400008804003a070380601800122014801e00060217010040c6150410000612003d21554045501c00401000402c0359543c03182c800707204070010300500e5460305016041261660544c02059003008e02c00000b51a41844d14800040c62203861180c061001001491040325035138400041c6001c94000007503d0392400d10b1076014000305450f00c0110042201c112001d04286010300c9607004d00c621020161123000301440400b080c070303940108000801d400d440408 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 530564433 1250 530563183 530563199
    0x60903061003050717030a0c050c0d0f020319020d030c1a0a0c0f0912030e1810090509010504021309031110060e0a02160f110d060609050a05090601140406 68
    0x15501400c1c100551107421400d50501d035003031031503580090145100b400040b468040001080350342d04801440d1000d0403451074605039003045588844d01d90301c001c40d034490b8028088240c07410303012184205c0407100c550748011440d4203180e20410000c2e61060341881d0b00c10100f030144180a0145201da42040d401c0f160300881052400740544a1040055a40003c4034950350824912210200349040c109146440e100304d103030344406126001410010007485200180d100d070070001607030f016a01d1100c801440e20f031002e0b5910500501c603840c1218184400b0030900d61062090a0246401911103404111441c14080203000182811000c1020400704104546800e00c641c0720b201d00c01e041c0108525103002c1c060760400c0c00282103403001c07070702c100310308102100c2413220f0095030307a0300800c464070520560410001c16501030710305135044020075081d40c1c2008891380c0103e040e00c20280c0d0400003901e6071242001294401c44541c42680d2200005000e60385e01244070500c6a01c0040010421b683c40d0148 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 530565683 1250 530564433 530564443
    0x1030f061808091305040b0a021305040603030e100f17070507050a1b08060f01030311030c0706030c1202090a0302210115030c0501080c0301150507051f0e01021611060903 75
    0x820780c0c0c019400701d0403e516142c403222110fa0082c00310343c01e0080c3d041545038428480d002030102c00445500140768801c0c202d0210340c4000a00c0003c02c10401180d80b810060034071025140310900c10b521440c40040913602035011000d400c202da990b10100d0005802c4002608040a4030450501006102490000d1310810514003542c1c4520818a503181c10009141c103400100d400c9203e035034200d14100002a00d102d2111411240c0520b862900c844560030468114800e4a1810100740603202d00480c686070560172a541c50070090365020040601d078902c040c1280528000c65602c00e094034002c00c0946008041043c100021104500c08060940241e40c00c40b840300d14a240b100c1084042002800401040c65000346000e0030702000e1494914018400340c8014044c1c00b5040002c40d100c0c4030030341c0c401c00c02da48890381d20104a0780d5000c0071030030310380f1280b408800e003480c25800c200c1d441d26444011b000740c0d03900310041e4008026039441039035440c82c2030000e4034000381c210405000002840d070301004 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 530566933 1250 530565683 530565731
    0x6100e0405040f022b021e270709180c02100204030c0815090a06090807060c05130b04080a0308061906050c0d0905010905060a03091205090a0e01080601030f06 70
    0x40b80100320180f620500000a0100001400e4040201210321058031800314008440780e0440301034483c4004540382c113802d40442c9500315000580b246150201d0700f1094042800c036260b500c0c01d0f094aa440c5a400c0f54800d1490142504070440c0812055092070b903a00042c0700c660340350055a0242c0c0c1c4086044040342c21a60061b0740903202104100007040003132200c10581045920b9101c068600720048030f646090b420070041415030380300005c03070070300041d00e0903500b00a034048414001d03074003803410040ca02d800038a2442e000300400c010015201040c0001c64045a034101c002c3c0540300200e490580340c603039004000a80005107912407818154040c51050b010341141d850f06a1901c0e041140e0714070348184020b07100240b060a20080c03005a8008610400b01c407000c03194141d03030b0044150124017402500c0c000500d80074110400704002c9801101818916606030748900c1034a50300e13083c8410b071810a00c564500358201380014008500d000c1c076202d222078015040441d0071003200d10b01e803821069104e = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 530568183 1250 530566933 530566943
    0x71103060a091103070e01170102071209060806030c130f0b0d031e0305010b0712050d0606020c18010f15051207030f0e0606090705030711070b03090f1506100e040504 73
    0x19040c8403c00280b0108020552010f4004254990500002e112244811301070b0080d107442401c0482c9500c2000d4048406070b540c000c01080d00d0411010700540b00c200d0030701072040851510000600709007400038504030714040041010310712041c4280e50200400c9003910703ca0350551a15509000783d00e4521411000512a50b039a002010040f4030501c03040b410940010101400c1c40010010b8510090a0300c003036a8000c2c0c02c3d101151411032094929100300810800e2107814904005601c03600420180a5840c080d00c1d203580c0b1060200040e00c500f0400d004203040b000f41407a060088001c8003011400401d22401c0032440c04001550a80c03181000b1207094000a0300c1e4a03202c2103009590040c5981e54040d074000f4110780c101a000110302c240001d101d0403c028000c80020f501503c111140b4031303107000000568610755201c2c0e40c40000c0f94002c030340c8003615110345802d103285a84002a82010400b12154880c900c0d00c41000304144401c040e510942004a2002c406980e030b580d030711843e40554814 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 530569433 1250 530568183 530568191
    0x10e06180a0b0a110d02070e10091a03120f0d090f0503030f010503070b0c0606010c0602040f121415070f03090c0605071b1419080f06090105090120071103060a 70
    0x150000d00c0c00341321040a840503044410401403041e0001020410307600c2440c0d44084076a113080011a408840350b0040d0103090501044440c1e00307400003101d1804040680c1680d009920b28459040341e48a4480c0461102108000c118488801d035400300f900c0c1e611510b04c0c50010394842d1105441c41e0002d031030059108000c02c004000d00e280803c101402448100400c034100000d9910080d181e0600408160510806c15001010407c665048401610243c5001d1007030641f100e0b4a0a11901c00b0481151400440008004400b10008a101c41d440035284102a43da0f0b4840b811280030084284004c20716480f000250001000803400c68090f1826556880d1101403608290141c41450307511901840c42800090082c6250a2042c2054950540d10701110421100b84480031390000d911820441c05400f0060b0040c49000c1100350150b00d1716002401203884441599003216180c2d01e8002ba20403d1312089650041c5a0016040304c50041105580d0246500b000c00d0900804170f0b2218205951 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 530570683 1250 530569433 530569447
    0x203010902060f041d040f08090d0606090917120402150d1404030807110309100c0803010e071205060109050f1206040c050301140c0405190b0a050301150e010e06180a0b 74
    0x70b25007401c1e8250074580e4245c952410280c440001d103406000001d0901c200006103000c0e542c0300c502440b070f40c041d031001d0108074190703980600c40c0081511040803108070860070026400c000c0340e0400e55040640c8217044501380c0c2c656500f00200c042c44500340801c41d00c014001e26024500c548142c5c2d544140c885034410540c98145070043c425480181a00c0c14008c5490081b00800c01c000107132340600c4003e441030000295011015652400049030090070018000008292021051500c500807031142d1680040740e001c1d4440e6800fa20011144140000c40416041085141041c00c0850208000d860ba90b0601103800c0d02d5800d2110480b800d5900d446448000c200b0b43c20309105030703041d40321745564000e803030f0619904211b1076200e644076030b0384560488aa126011708003545804000e28082d4115640e503d410040a00305030003d03c15001c0424281001200180c010902417194035816900d08c200c2100381c00811610713030000c00e200024000001c5a45c600d0307448038ae840c1c001a0581600d11074903005 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 530571933 1250 530570683 530570699
    0x806030a0b04080406121526060a0f05060604060c060b1503041a1501020c090a02130e060102011109030a1403041502060a0c230a0512070522060c0f0203010902060f04 73
    0x1006440c55101c10b1070001000454947c54150b50140c9510a5000d500c4600d4000e01c0e59000c1c44546101c00d05020b00720504c022051030b07034072804182118000501260740c5a008103d090f00480c800c0d580420241c101200c00204264024101003c0041424000c503001040e0b00710300c0d402c01c450840301c440710070640c6c4980d018202c4041c0d0740100c3e001d2450303000441e403100003519030040e036040c18011b07000b40c000306080540359019603110b119001c80c4850f240380e90389039603502c2e500c0560b807840c095440c010001284690700f00c04c4a00e0361401900801c0d4019195640b50f01041c0600c03061840ca000500c0040b410a80311800060b0740c88582d13004207840e0800759055012a880318000d1418000c10680000c16944500c26a030071110030b07481c8103520f41d04114400ea82510640060503444100c1e00c04000702c070b98000018141900d80240b50a103201000c035001100d038025400b0b0080400d01400d600300000301e11091601105102400102e40c10099502240c403a0b08290030034041300e6008101444603030 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 530573183 1250 530571933 530571947
    0x203210f0a05060a032301050403020a110307030c050d06110f0901110a0c060810090c0c14070b0f0a030e1603212c0307080d02010e010515010806030a0b04080406 71
    0x1101c01e48080140e4101040003d080c00c085110050004402c000860040f140c1915140001150703000240040d20703003880d00945501041508441e29110311850f06901c2c10300044038016039501c041d14a0141d800c0c40104250004101000c40341c1b1034444010201c403100c540c01805000d0100703010345494001c10720000d0400a886080085e096010807000004076020707480e104215040380c244803080c0c1e110704c141c241d40c02120340c00c42c0e4a502d042089004881ea0f00950002c0760900501c940035450168414035500c41a06100d00d061607507041c4254a189000307000184a00300103414002441585000201d0810900c03001c8002c0540e6a07030010410310039100149a2941e8085008640100c0130b5030020f0b1080e42e0390042c1020400328030f1600c0240441c2c620035811343d00b10040449414942d1000c10030303a1250340c04003250040d42000008004a0014056a402a21000885002c110240004548120000381540e52620a402c10070f004144600c5040303006600a0108903a01d90410034040d041c8 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 530574433 1250 530573183 530573191
    0x218090c040f0f29060f1308030a0813052e0e0607030b010512040b040609020612071b0f022b030c02030601061704020907031b1814030d050a0203210f 66
    0x48144079282001d010004c1c90f29580c00f81c1c00319449500d072506005842114040c0813202c10490241e598003086152000014094242d140d5983d07110f160b03204c05d141c0f00c403c1e10400f0000c0082e40000982e246005124000400c010103100440218084c0100c16070103960945400c0c541300d410020910032084c1d81400f0f0101c006800307007030080c5414114143d03903a030f030300300204040c080a0b440000f00f81081b186400100069400404682c1c42d15a8956201c2d40118191400e03004140074842c000a03601c103030b0800d08401900300402100000307982d000d0169119048007034419084444600c000100d010303481140143e03020782c0c1c806010703151910500d0b26003241a04a02c2c14085016030403640321070f42c901c180394050390691b240c0aa54036516400c0d0050401d0424558410310000c40b807415040d84010301d49003c41c2480300c1c201d010790307139510400c80809900c01c0700d03909030300200c01c0080c46034003c0000b010700040c903104481c5041003450f0460344c0010341a03190102505100288001d15582101032a00 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 530575539 1106 530574433 530574461
    0x3090510021611090f07120b130b091014062a030a020601080c100e030109080a170604090503090108130c0e07030b1509010c0516030f050601060203070218090c040f0f 73
    0x1d010794ad0036041c091043d100015110841460b5440203c43c0106201c0b0700401c400c805019039580f003617501c11492641200c025a00312800036000c03c000c0030050140d41c944c07c20300310082c00c203007060b44031051a40c002500c81c040c5503281101c454800d805800d02041a0601e0310101e400742500701c4000e4103401010a6014040380c10481600b00500800081c2c402c0d40da4a60401046403402c0801030542d0b4424404c4500b694091258103801c10110001442203007100c0c0d9401115146607001a44804100d41c00e01000700d8040c0280003d0490841d0700b0101d01c203041101940310f0203000140340c1084440081d003001d000d014403507441241d030a020303944602c986a0801c1902c0c51069003040307030144651400000e070b00744040203407241980d00a11842d95040160340400001034003801400c5c1030300500100d0601503070350348103291518071b15800204000e81c04407400021650080341d1381d14 = true := by decide +kernel

theorem cover : BRFrame.Cov 530395683 530575539 := by
  have h0 := BRFrame.cov_init 530395683
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530395683 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530395683 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530395683 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530395683 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530395683 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530395683 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530395683 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530395683 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530395683 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530395683 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530395683 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530395683 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530395683 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530395683 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530395683 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530395683 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530395683 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530395683 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530395683 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530395683 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530395683 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530395683 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530395683 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530395683 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530395683 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530395683 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530395683 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530395683 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530395683 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530395683 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530395683 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530395683 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530395683 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530395683 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530395683 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530395683 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530395683 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530395683 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530395683 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530395683 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530395683 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530395683 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530395683 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530395683 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530395683 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530395683 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530395683 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530395683 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530395683 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530395683 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530395683 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530395683 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530395683 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530395683 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530395683 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530395683 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530395683 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530395683 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530395683 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530395683 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530395683 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530395683 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530395683 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530395683 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530395683 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530395683 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530395683 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530395683 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530395683 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530395683 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530395683 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530395683 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530395683 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530395683 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530395683 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530395683 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530395683 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530395683 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530395683 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530395683 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530395683 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530395683 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530395683 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530395683 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530395683 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530395683 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530395683 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530395683 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530395683 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530395683 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530395683 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530395683 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530395683 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530395683 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530395683 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530395683 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530395683 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530395683 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530395683 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530395683 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530395683 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530395683 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530395683 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530395683 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530395683 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530395683 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530395683 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530395683 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530395683 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530395683 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530395683 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530395683 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530395683 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530395683 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530395683 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530395683 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530395683 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530395683 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530395683 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530395683 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530395683 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530395683 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530395683 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530395683 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530395683 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530395683 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530395683 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530395683 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530395683 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530395683 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530395683 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530395683 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530395683 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530395683 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530395683 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530395683 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530395683 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530395683 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530395683 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530395683 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530395683 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530395683 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530395683 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530395683 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 530395683 ≤ n) (h2 : n < 530575539) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
