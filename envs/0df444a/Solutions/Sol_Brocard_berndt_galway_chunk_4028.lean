-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4028
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T11:22:07.892101+00:00
-- url     : https://prove2.me/submissions/57aed6a1-d088-4ba2-a3a1-f2b3402f2066

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 724280575 ≤ n < 724460431 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 724281825 1250 724280575 724280647
    0xc0b0306011205130224040e01090b011706010e0406051207062d0f21050a0b01030603030210020f090a032f100315050d0f050f0a030512040602 63
    0x4200800181190b981145488103100d442c030039150001d0078a6170120f50405045403550400500100c01d1907031142900360000b00028861203526a440c100c60720740200304070302813400303005403440e0741d1000c40e040c42254654005089076002e031f0b8410307100f542c2c0600000b8056403908007050600c84403442e0620300c0d60000342d0401401e03501001c1c4ea90783c4104441000c41062a10030301c000510384402940c81886101118010340500c40d000d052251030705100c00f401c0d06812040b20304024482134a4600c5c0702390518442c860350754043d000340400c0300e0b81640204080500400030340300035000b811400951200c108090b84182c5c0d100500720014600404085245420302c102d940d11901130041c85200076602814046115600d5040c0700d80095014200815040e04800715105980c0c01500080d40c844410400c0c0d2042c403001d0590049158032920885901c84804035240740d843c030962000030009402001460620305100038090341261083c1e0f405400d1550392810b003d851042440403800c1040c6585d82 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 724283075 1250 724281825 724281827
    0xc070617010603181403280806011107090906020c01050702031b011e050411121509030f07031103091c02041503020f24030406020301030b01060e0a051203070c0b030601 74
    0x64940184890f082c01c0020030790040c40605072800c40d0202412029a0400c41480c640040c01126484900b66040801d220061000b5031441a002070347c2c00d000610a20008100d5409044041203000800c5d004003400ca2500d94108094100c442d81180d070160280403100b1002c109005060180300749401444e1111148410715080d102488900703a845c4e03050290304000c08012190f00014210500c0010070656101e0800300f4a225200c44016000686401140305540c0d020442c4d0010b000c0b80018500c3c41d40f10003480941c0ca00910050010036041041644000b0340284105042d4415410960741004030000015a2004840c100059092080c1020004600e01441800902913415642c1c806e0749003560041761000d945200c0780c0d0f01a9290b0504800144201e41c43c00e4050700e0040c411507502e2400c2c1c81d103134029400a100480701d220540c8004210540104811078807101e01500c0e601180340b0300300802c40c81200721007900c0054081000303c08040b4000a102d0405020ac00c90741c69034900300140 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 724284325 1250 724283075 724283117
    0x21c121a100518010c030c1a0114060301081e0709020c011d01020a1d0a0e0412020c01090806041b05031606180501051e0903031804061422020c0706 65
    0x4030720300400c6800c004910000020220f400c501000a280810314075030b0a2800f50b070210b030802005041080b025082c04461815070786514181c8007800074403199820840140659400280103030301d150f8102a0700e04103a44c115640c107a10000c400801c43c3c1d146d5035501d00d9002207038403001ca2202070740d4448114010000440960b0381507444500d00031864140307101c4000709034421291214010a840403140c9200355120f08003203000c0d0100030340850290500d450403096102d600c0c2002c201600861003941c507290b00805a480458041070040c011942d00d40c3d80e420150782d002001d15006061030100420b40c0d440400c5029413a410300902803108905060000d411741c1b031110010741000e55598028031259134000c06888440400c01d00d5030740c03074240449482d503260242e040ca154041c880854900c0201e60050500c24926005071070411900b0303203441d941e045001003469010740144500d0b04942e042c40114503285600b1680100050400d00d01d2619642400c20f00e900034000200d030003c540d00051040c1c1 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 724285575 1250 724284325 724284349
    0x50907060f05030a0e100c0207180c0912020105040e0403050309100c020a15021210090e060403080f130212010e0105060f0114030417070c0305100b01021c121a 70
    0x10412a01504094000401920008000021305903ea40e00007080c00c2c02004000845000c0c001c00f44406000400002e554104c03902c60010000606000f08002c61010b10a50306c00c0c000b076960307071060706080c0110300503000f209090803030401004220000f2840880341c15603000314460380c4c5480d5241001c0081c170380b030000764000d20380c0890303d020f800006107034002410380340556103c107401030000b42e0301d00c0c032100a0203244045920151003504001202c80011070480a99035080e408000030038003140c81c280e90b913008480007408035409402041454071135442203684414819143c1c49a04559070109060b07440907a214003140e9142d06c480360540c2001e010300380c0e102509944501c116601803000820500000980c1601c7c04000000f05080c00001800c51020300031100e40c40b5a6401d003440c22100007159440103803281e008404c4404501c05a5010300c03508400142e0041000f121003074008824130f200a139502c02800984c1c40d00c500c0c03002c158000d02c5400c19070840100348080b2071001303115060b1244 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 724286825 1250 724285575 724285577
    0x23040309120c05010210151203050705060c090111030702150c030c0d1806020c0901090e1009030c030806030610170a061a04050603070305150c1b06060f0409080708070807080a0305090706 82
    0x190101e0380d503510b072401f0a01105c48112081c0e803858031600341520280b1600e0006041c0d07004072005c203c50f54800d00001d00080f5001e0380c3d424015519001d00903280d00035400d0003940b100f038452204145a074800c0280c640440050282e80c9040483e0700c031980b45c0340e010040500415059130505030340d040e5074541d2400801c1c10740081c040c02c1c080d044c0003d01e0f2800501401c13810fa940c824180701150003c000c1480c07072003a0140304000c0d00c0703a0360802402e4007040c0c0e44d00b28001185240000d4940c2400b0030707402d0045d408a2483d40b031190600c03180040c0c1c00c183c01d0098500d44240300c1001d02040490042d0802001c4486202800400d428180000c0e07030001080d41d07000345d010303c01c200002503000441410034041d03a03e41100f00c1e2100302480d00070784510a200140540d8144400d90081404103440c0c2c06000304440956881e03289105101c01d6603008100a050a4814800403000c203070101d0003096480d11400c0c1203442c10f038059980c2000c2b60041c510050020340e0759401c02c587d000c010809c40c8040c10803 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 724288075 1250 724286825 724286831
    0x70f050312030115020f15190c1209060b0418110607020303160c0b040602060a061e03031101061208030403030e0c0603060f0d1202010f0f23040309120c05010210 71
    0xc1c8058150040c4010310601030751900c43c0b00302d16003042c800d0081480c5003140e0b0080d02e42c011400c00224030031040546044811b145c001ca2a02d44101e2030b072040410780e002503120460881104600e6400505c50380302c0c1582c820703880d040c226005590301c0c07040d5400b40065210081e810196400c01d8980b1405224a59010b0201001080301698001007034503903d5400c0200910406214a44240004041d40c00304000340300200d0082902900030440314494034440b01c0030441c5a40e28847d50051040c41801030700e00d50f4a40b01c052000c03900c52688264003040754000440d4841da9000c0d900e0321407101c4030064804800c003109000c101075150080000306506140186000280d0400140807413201504940c424106e40750001c003261a040300003a000c6400c003418441c1c10040010103030207403141610008429160083d800c180c50101c1c895103681007018255120791003160a43c400e2480d10250003a4107001c01710394000f800b4100f0f0040110510300c64402d501e201031820002a2504e0030744c00140d000071b41 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 724289325 1250 724288075 724288093
    0xf0601030f1727091623040e041101080a0b0a1403100c0504091401151112070809150c0a110f030109050d14040b0904090305120405070f0503 62
    0x2a05050700108940c101000312141c2c07586120310b803258410041c801181e10b601a1922000e004052940a0765180503035040000b0303038980079800d124120720703110b000225500e800c903009450320481c00421322075030081801d450b2a48607001d401800408030b030200c1d0f0682c404802042d080d40c0c801d10150708000c0001040c00300300048000a15800150300400001811a451240c02503604000c00700c0034444454040114003080c81d00206a98854015142a54100f05010400000410a042c102c1c1c0c4d1203041605130000c0f4940c2241c001100d00c00b14003817481307511040c0603600007610003841424460542103544541c00d80c2800034000d101940c14046140c1030256a200c00d902040350210742c1d07400401c2c20440001000014120785140c44c0d450742561a02d207030704080020015000981c0c118580f55054074038a088400200392040303004128800314280100a12414507400145130305100c0d050050600d040c0c5410710326018030454023950301c1c4d4080103080081c07208096204001c0d10054000d0280c076a = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 724290575 1250 724289325 724289333
    0x102070e1b07020406050d111f0c020f040b130204030308060103020414150d0f0204030209010e092802090405011a0f0a0506030a020c030a2001050412110a06050c0c0f060103 76
    0x3000c0c0362000120072800207005400c6507215400080941402401244150708070700348550050b1201001d540111240300403001c03480c02e0304103140321070303291659415507000c1e0540c01e1186101c0c10354a06900f00c1d495103000c0b4410381e114400501003070b400000040e112490350500400c4598080c6c040c5060600c10442805403070110b43e514980c2d1303441560f0404501000e0f54003d002d52240740e0740c019030180790030203050b905184c6400800440703000300c860b000c0a90300c1e1111600c80d407509840c4646603900852511840320311651260400086150840d1603881c259000315000c101d0031281180d469540b00c100120030303001181440b0b40c101d0181c038485a4000741d0804103452000720b00a0130300c128401700c00600c160030700740c04648031010f40000ba81c0d11101035020107000002001c000d42009a0002d50f1210740e65014403d951007035801208000c0d25014440040d034130b00010448801c050b010345081500800c541d401024007031020720b1005540e80a42e14001420040040111251038001c800100089 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 724291825 1250 724290575 724290601
    0x10608040f0803070e06030115110705011e0c05030a090602160503030f0f0c0a05030909011706044110110307081e0903040509060303070b07080907031e020102070e 72
    0x1a848a110b50b9a030712482030035508901c08545480c0d10540c00000800c83c0c030455003010b01c0b5044144c40b00101c440c4044010b684038003480c000d00b030018508900301d00704100c000048042064540c03d045040c80500e071185400e50b40103e655402140301b10200b0080c490341080340d003070400350300b41c0300260440c00e043c0004d4580c42842d0109280d00303400704943c0d10240c014412101440c01c1541240e06200d040d2803c640c034ae8100d0f100700b034071503c0c20000000c0d011000303032810b00c40c0090110240c02140c0d61580c5818298020014a00140d4001d500c001c8184130107034241034035001c0c080e031f070314007054080d9880e28030b010002203020440b42d082c218041308003080310781683c1e040819805d000f1419a245122107158620051004188003041d00620800703807030100c000c0c4141c500c01c0d20303424840d940b040305260340c070710600030000e010058900c009503000317104449940e0440304100c2901d006540d240c4400c8001171481117505081041c440c068011036030108607420041c400111380032214038116036210b8031 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 724293075 1250 724291825 724291853
    0x103020f030109051c0215040b010303020c15070b0c0904240605090d02040b0303160b01060e010f3903031a0103050f04030804021302031f0b03090703141e0303090601060804 76
    0xa0802c4060a1105c45030080c4044070315620700a80c4c0312807030700d01410502d4100e41d0031710040d000743c0a00c2d00800308506051404401204c01c404150745082c401c0e07658100603040007880f01e0700030141800125074070740d03443c05045540b201e8000ba00007051041c042c4082200407650200c428400104001402a00d444082c1ca0080750102c40c005080602c03040440d05600c241403030003140c100210021800c00100b8030029041e105540d071506908007074800151104814490715101051518000203d420261b015008000140f6903040d9040d480801031125034484c02041100425113403041c000300a40d50105140208030240b805000b01c2c10715121000200e41c1c0604080c0c02c0013100e800040654491034005d0b400c0c4920200115900d1030b000383c07014071303540c031031214000341c041e01c40c8000500d5206502540e010340c035240040d041a5155907644401d9011280f080000c070f0254111080c12215200d200380210888240a1070b84e9150007803942c3c0c1801d005821002c1400305003020310020618115000003 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 724294325 1250 724293075 724293103
    0x40203100506130314100e19110409050304060201061406212d0601020d0801030c050d050132090d080a020d0b090702030c0f1506010e0a090c03050103020f03010905 72
    0x1585100324203c01d200500240c00140944a041c8600e040d14400020000a5100282d40c100151050004090303241d020803006032583d03102c0c0e0700f508030100e4019130184602036001807001a5900440c2d5496045401580c88180541d540d600c0400c880348426035014200001292854034000020310300b2000d80007124201844681200c0000304141402103803488c5c506100c02e50500c01040e210030a40500e0720440d400d45c01801880d0303203040694050340419050700d0388503091094030b50400d400e0201170701c2c00b00c4080d40c0542d00d5800b5820380ba80380c80b044504001020301c410354110030040c49426901d4014205603000d6200300803604e252940720440c6900f202e0030b654090390303961881885001600c040a501a8441c00c0b200c280291582c00200500d141c40e80f24090751078951404599036140d020708468a84244036880000f0f8041d0b1207040c8954062100410783c1d05110385400c01e581c01c0303404521107580440d03036948c0180150716040302840b0050b00101c00a20920a40755115902c0304400c3c10000 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 724295575 1250 724294325 724294327
    0x2061308030712140a0b030105070801140112020d0e0f160905041103030a0804020112060825030515041b03030203090d1103151603050402011b0812180c040203100506 73
    0x42080740304090040d110440c07031200340091388103000010402c40c41502c4507a501703840c0118404040c14103014040c40b5001c19203501c019a032a003a10ba1141803161070109041003100c0592511004452020f4411705070420800512241003607000761524900e1400a07000d60f02034259015001540c04114095a02d90000030420b43c85501c1c0421850301c03024001c075818000841c3d1404001e90210140d0306ca14002d0342e840041c0d070101224442140c007e03002e0610750f6000040f044410070120f8014803180c1417003040312130b41c1d15520f4640c5401d00020181d1080d55528003820700c000c0c05840f080c7d0400c615510b410041c02a440c55901941e20300c143c80d011400b4210f4101440180309820215420300a000f0b016150410500c9040740301242c0101e8007108869000b00c48900994480c0c4503e51203558182c490520945442c02c040600d42c000040495007079800f002158070f030042c0c461003140501140311003491384409414203641000e035503072055400b031481481084010600801080d0440350150303241 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 724296825 1250 724295575 724295581
    0xf030c0a02100c120b0901080d050913090309030510050121020301140a02070201140f0a050c0109050d0e130507080a02130f0b03060306100311060a0201090c0f150206130803 76
    0x507030030521480c0b1204005841c01c2d0980d403500d504050402d0040c05429401c010058101041100482c070038090320031107500c400c1442e2440d600480092004d510300070110f14044c0007444284090b502840412000100d104004108001e4100006480604c032281c1c207105641c1080e041c1c084030040c00c2084148140b03e02c1d100003d5403000e600104684116603072100c1c1c14900b280140001e035015150481c0021070b96070100c2a0b0900010640d10086640520145815107600b0100c500342c00010b14039082d956200c50020000e0700812218400044a484225000540c4004c0046000400592544ca1400d000800500c558010003d80c3d001c0740804c40141c072601000c4103240028229006054507140d50300c400b091260f5080061446001d00f1005c40d4402c2e51070306d955190540b020310000304142001e40c800e011f1407a054000c3c080d06e140c0c520000416001e1601e41d00c0f60302c02c807548002c6003440b26260a2050f403440742c1e40c0a05030f02803400140708a044c1401d114078007011009015181c0f20000c004 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 724298075 1250 724296825 724296827
    0x9120307260c04140d0f03140c030307020c01030515090c0a020307080408010b03010b180a021602130c11010612020d17220e0118200d050105150f030c0a 67
    0x90158054100907034a918a008518001940e02ca0300651181c000f040b850207459207400c45e4980d0105c1d9203c51001103110701c954041d90107141c40042510725000500400c90a4002000034500c6001c0c3ca40c01801c4080340300d0005400c40e20040d140c0740c103c118881001030316459220300c0725080251000e43d150b4455000204078210f0081d00b41c000c1401034000f90008171134a05420480070f2080450081001c0348000c81040000515040010310652440d00004c004205a9000d0051132071284856100b0001c41e500081100210a440b603440580e10350820110550011520645048080003082042d05103070f40d000710040301c004000d104001c1004d0140800c040058218a0059002c80c40e949a40301c0d04030504018920311031000500288110015168541010150403504515601000042d40c4001540030b090308001601c080400301301d094802d01c030078000404002c82c00800004844d41403c080207425a068402240701d80b109002660710b001c200f10440360070001460b0700d40d60319914100 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 724299325 1250 724298075 724298117
    0x409060b0f18060f0a1e3b1c0327030204020d020c0105010b03160207060f032406050702042a0513030206070804060e030109120c02150408010e0609120307 68
    0x4c0e00080c42c00c000c40d10b003d880780c00c480a5248402c265101200f60303c184181100c5030401814800e101c68600c075543c000701c4035149040c9500801105000620041540204000480104210440101d0003074444103166010400c2e810b0001d0008510350b9a00648083d0081d4441500020b031040703500040f030490406c0035034100d842401201000303008079270b55106031401d580c0044581180c25400b015401d20120710100710780c025121141c64015216075129000c40042446000c00403402c0f40e404c1c900340002200388501c0300100100c3c1c1d5a1a5500031910601095540090360010801c44c811414801c04c0113074180d22102c0802460240c0e29190340c0d00341c140c40300001c1d0f1300194005100141074420300c05c54100400c140d40980d241d5020080b2048185070880e50f40308005410202e0210142e2001446808502e40355400280440c103e00c06940c004505607100764001889607640e182c004000c26018007280d40d1000320072001c0c041864060280500c113100c02031020003004140c503020148620081 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 724300575 1250 724299325 724299337
    0x3030210021b0604080408101b08040f051005010f1a1b15040f290109050a112d2118010c0305070216060504090c0207080d0201020409060b0f1806 64
    0x40b04071003d42c03c0c03d05000e0080d501c07602444a03035006941da40c1c82c2d8005e1364055601401c805007520350403601004c00841d00b134200900b00302c0b001c0040c06180303000b0800c1002100210700c01a4000591545030280f0040c61210562048072021064104035208816501c01c0e2620107540b244140c00c0650100320040c00e003400c2c4030342000004056014030040c00b4211882c003110a2240c0c40034070b264840303100707a41040750118500e1041441d55a00500848030550445900480700b0000811742e9070756076001003242d4100d1500981d121803402c0108901d0200f00303201c94070050440d0245854107644d16500c001040c00016441c00215080e804034081803c0348a000703c5203048003000b04a600604440200900740980e944001807050502c2107801c5003071030200900311541c035101c603880e0030300d41000f440c0031f0588440b0130340030b40c0900b04001030381d12002e0210200d0700328039500059540341464991000c44074980c004c070a008170184980345000406d03108803005621903540c00b41202c860305000480c00c0c8510 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 724301825 1250 724300575 724300627
    0x7120807050609010501091d1b06091005071a01290f040303050904050a05093003250201020a0f08060a05040f270503040e0903040b0a08070e0a0303021002 68
    0x1403000c03c85108010b501841c1610141e00b01440b10100800700348030070740c01c0d40c0c2010791a80c018201205481081942440c0300e40400303098903042244403800100c0d034042240e0800c0c0440c40000c0e00300f08100304460000110307607004441c3c2c03115504100e040882c2015080981402855680080201c01040000d894200c0c1141d9091980c803a168900107040b41c205080b03544c00345080c48081007014204e8002c0030701c101402c80c02072900e20414400c2405001d52210f42c115180e0ba51042e000c3c031090104000c510038038046403500514100100f06d082c114001e0004003046900c10301209130202da00518005540c800e926000207079481c0e000010303948502d80d030701c8654090701e441ea4800c6180c0b060303002900441240343d180c521001c5600e0032051112401580280190003c010501140c0c0e0803120b656000701d4103100302d82c1450307100c0c3e5000702e0946c004c0d000703240811031040070810041d6200c10810750405c1c09940a800c070070300d1aa40032f59075084244a002065030042420155045140b910300090400 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 724303075 1250 724301825 724301833
    0x504051c0321020d0c0e1306030b0606070609050307061b0e0a0e18010501080c1005070c050d080403061103150102150c030a0e0102071b0b0c0d0e0d0b25110712080705 73
    0x17554070040c0035040e11030219406060455645000b00f0514803c10046a402a410900b41d41c4c0d80e80130071006900441e402c070340342c0350f942040201245080000d041140d1040c000021601c40140003485070900400c104000c100c011504440c140c1c0340c0078000412554808040c3c025a29150500380e02003800c00791340c03002c561a02000103040c0c4800039140310620030540e070108c600da4040600319200d21984001801c52541004c08000b40e00b0020b0040c05058011002d00b0306054403a614081540e40b801210f2300007000104c180f056454148070484076001c1e00340000e0009002400d000d48842c0d0b03006006c040d15130804800106446d03040c0c0c01c030000d8509558003c65403960303d840d180040000461404504084200740400c1e9107410408581010300490010803010341408400c8590040440d68180c118403c61480ba000400c0611014012090040c0308550441001b403c10901c42161910384104840c2d941c07400c030f0b00403010400c032081d40c0b1008129000d14401d420140024840c3e16401001441 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 724304325 1250 724303075 724303091
    0x30d0f0e0f0d0305150d02060a0201330506032205070f06090e0609012102130513020f01081603180b07020304090615050306010e120303070504051c0321020d 69
    0x492804031140d403039201041340e612040000b51071000c0401505410994004e283c0025142010117071001d002e00348000709286e030031441803000c101d400d0503051a80e400c00b2042503080700c03292255207002d030005035026401c5160a00f43d0411412808040c5c5114085150300c0300c00307200041c09008054000c6004682070725603034460041403442c0c507104034490a02c802022a280789042120541200c802d01c101c00001040f0b0314606041e0562110100d0340400c0c50350700802c902402c3e000d03052082c5100900710004000d540144140d910300c00d02d00504002840e000c10203010b56001020031b94a4131898002111081c0003898240080380803401b800c1d040e41d6104000006a00000900c280c1d40d40c00300c2800031a5540b07040d00d4078031041da000c001c04642c2c00e00024880754030400a1552181005214030b1100200038032040c25075005450250008070000380074003640c01c0c00c0311098407105981604120400c22924010b00c0022080240b00d010b1902190502d60200c90b42c0640d1031840b00100d04100d046 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 724305575 1250 724304325 724304353
    0x1030b0f0418110d050c31091515120804050301020d09050706050301051e030c0d1115040e04060921020d08060108070e040c02030403063902030d0f0e 66
    0x4290b041c4100d50980e40c03410785103100c0c01d2042201d0001e03940b00300240b9029959a0401aa101003030221034002c5180d166a421070b001603070480c00b40c032444264000b4581c481400e152800e110b0440c0316000990814908450307080f08040c1d1341c0111403411014260305060351401060341d1045910003580b56002142107124443c25500c00a0a940701d0001c450003a03681d4102a501d5000910030198490035480c00c08403001c400540c038000054000303080da16484c100400040c01401c51000c01d5070700d0303c900c42d560441810b0000d1743c00b4111038012201400e113072624219400c01c00c0c00620080c81ca644a200040c00c0050402d084614000344581c00d0b02140c0e08480c00035520380c004141600042c2449020903069409181042d0248180f50360740303045c41080b0800d11020b880075048240441c44100000404130f00b05c1d00ca6113001d41300d001c140102e82c0c46007903086600012100300244249803071a00c01c0710060b400004440401d03203940d4001c210201d11400c100010014003050400600400340101005 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 724306825 1250 724305575 724305611
    0x15010f0f02030c2b0c081204060902131a0a051c1b090c020d14090f1906120e010605011e1202070f031404050a12050a05030a120b0105030f040201030b0f04 68
    0x4481058013000703111000560855a0094892015207411703400c0203038604408500340c000380d0180c01030001151a05441e03000c00d0b4002c0c251280c201223640c3e01e145c0c4683c00c00540b080c407010b18408581030072080b4101030008840c0038000e0030f020507605560740342d9810018a0008001c24400c08035450b00b025a50340d64400c050441c8000500050107040380600950340564881015001c51250b45401d002084040c000b6a5000c07060f4558000c0c201401168400d408078040300251049550310b4a0701c602c01502441038035201d0065070311a90420a00b031105990002d0300d590702e5001c0c0d203401c504d0304030003550030758504528400701c0004500028410381400b40642149020741d110381c0c0d5107516a08441030311070703440c069800b50a80c050340d55107041000b1104809000070a0780a0400c1e5142e446081e51098515881b0a05080c041552904801d080003110300c5403111110081c20814a54900b545143e03030328244c0180020f042c03560f5100c04a01d240c81c0c482c5028200b08018004208100d0030b1650380c050 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 724308075 1250 724306825 724306873
    0xc30320c01060602070b0f0d0f110405120c030a080a050702030a0812130c091113150206010e0903030105010c05190602030612030c030a08040227070815010f0f02030c 73
    0x165800c1910000b401403000030b9110846034000c0d41c2908142454070401c01fa0742c44041c0144015486003640540e01a6600c43d5000030741e1a1802940d07124980310500c40d00f008050807680c0c2d640c0107800c1816594034003144001074103501c902c00654503403000d1000d40b0385010702e000182d01403180708902d004011002c00184088030f2103166042e8507a0b038a8000702c44140302400d00030728080102c3c00402a44000e07420807a150020320032100d090440d8081c0c210114112a40648500d00941750343e10310168040c4042c60240c600390480441501e000404140e0760b11061040c54100802d80188005114041c07040c4901901c0e0807a050020103401c0c10440040d4109803403651080c00390010a425104000089035a0036542c8809117003040e1a904040e500b148000b041640c00050b00c0340b210140c58a000184010b0303410032403c074605070815440c020045400100401640c00c5030b01c10128550b81c00c0200c00f2580410380c5071070f6844c842d0b6203d049086000c2d00018481620400825000d80020354241001c = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 724309325 1250 724308075 724308097
    0x601081b030c0d060e16050a0203041a1207020a050a030e0109150f020c030114130204060803030a1a1e130609110405130b100323070c3032 61
    0x2120381c5d15404154500707030054689405100f403003038078007507003a000e440070307221107601401924203107a915000406215070f038a8031510b20301000101031001104a03001130707402283e1032005080743c40503030b07444a0343c0d810311784405414400c0c0501c007280c41d6840b031300d84140900075040a074482d0f8a040790024020b8541c40c41410094082c400364880c03a030a0501c45c280b80d283c941080c920950701e035002416204ca10501050b6005600c1c3d140100c1c914104000950041000540c00290000d55080d410b00700c1c4203090040b40b04424031120040394440349217403841d4030342c002c80358a000c00031010841402060309520030100ca500b0144240002c80301800900708496081e16010002007080d440700f01291440c0303941d10b80c000b014801d4102c26034440c0d4070401c0c641e1600605041ca83c4c2c0d1620ba440c03500602101c07405c3c0041c14004030881040b40d42001004104c500402c00d110001002d101c900c45c15882a80000811035100182c03000c151200281c1d1303001a00514808207080c500c1581111564410300100d0 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 724310575 1250 724309325 724309331
    0x10f0c02060f1b0a03020d0609060602070e060a0f0303030203061207080a0507052e0c021302091e0f01052503110601171002090d05071e05010e06030601081b030c0d 72
    0x381069018985403c01e40c444106051402c909010705800030341000e5030920407280d82c3c88000c0b8094001e03100700d00142216230010306103180340c01d03030072908204000d1805016a6030b0017401c200300400c0c2d02c11082500c0d898100980c80e80d03101c03000303c0c0f4030320a4440952040e1059400000d140c202c00b04259990310300400659a0043d181d10511690b240d594089881c03541d4200c1c5490303c200c6148114107511031080c9000315410b055600040c0300c1c000c40c4a4000b040135400107040400d4608001c031a03080b42d502d095440f00b1192110f0001f448035000003203035414024009410010a04000d14040f080c40010a03071904004060400404d030400414180305d56120300b00010480f502c88065030300270000c3d984001c0c940071440847c42e0010b900071240850300030710802d03a6080010024450700c4040c2030003c6500c016840e08944041c80e00c0011351003507043c0300d281003501c061922080102d03640030000b8202401540c84000e50f00500200d284114504540c010050044085100c001020840c803109428 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 724311825 1250 724310575 724310581
    0x102160b10140a030620120a060503010c020a17040b030a02030402030f0303011424181f050304060216050a2405010e180c031941010f0c02060f 63
    0x2109030302040b050711960000c5419410000203c90350000e0700452120884c4007041c00300e5135481e5005400165104041000780b0040129400c003130720a03400104011002480b1050341201e020f901c0300c400d1000a80000c00c800031a80c0085640001c0303800521504818aa591400290590081d0810b035000c03442801401d242500208001098a040e1030150901003528600c5a0070401c3e408091415650103005030b20f244004181980082c0002081005500c00000e0320001000300015038411281d0103511011946400145c0c4001a6a0b0266100d000180c0d10024140002c0403211108070007032040c880c482c40c01042004d0905280181038207000341102002d14884002e056039424044e88072034007c040e000079800700c1c805100045654400c0203641451208801090810001c540b40c1d01011080c851010100003a06c20301c46070013a240e443d03020420003503000d0750884444409000c0603080322007500c203041030000e6101c40c0c001a1050790401800c9103502c40a9110f900490b01002101803202c00 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 724313075 1250 724311825 724311839
    0x2c0d06062303071503091a040311032b0b03012c03030c1912060602031b01020f0403121205040f02190819050f0a0302030403150c09170102160b10 64
    0x9520388204000d014201042c20118081c20241c800004e100800d9105c0c560f0300049001071100e1504441318020310a118501410042d00a034044694481264000c0040c8684242d0881c102281c1c0002c80c049400a5090081c40300c0180c00d607080001d516518003e840c09894060300f0003181c04044500000e03c007c45960006912800110b900c0c16403c001004030f030341c0a810517042464041c1007800c0500c4403404a1141d04111a0b40c0e4024a016a000140801c1103070042d9401060800c80c1100940c0740141c41007003028036025521000308109000360a54901c24000c4406406071b5054a808220354901401d02d0340b40d600444605030f02500100242c8501403401c010341c0d40540e901d0900411003115031001910011924070300c295206e00840480d01c00860041c40041c000304d000343d000311340b12802c5052241d1042c0c00001c80410851821340a900c3d495041004441100ca440850844003180d02c0380250191143d404404480044107241c2c00801440c911124002e042d40c0482420050311860 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 724314325 1250 724313075 724313129
    0xc0d110d02030c06013003050a1206030c03020f0d0602030a0515010e0907051e040e16090f09050a0e0d030608011a15030a1e05150d032c0d0606 63
    0x1898401641012005114003003168001b0742c240300c01d2021780104000c0407508501c08800d28101240040c00000c2d0800059034009240725003071103d80302c05c02505240d80d81d140c1240e00c1d1440001e01402039001000326076600c81c1d84810041d500b00e00150341d20320301141d003280201021200407441c0c04903901a85010b5118a0fa440c070500d01c040c18400745e0f0b8440000c02e0341c03550010084409840440130290440c0a44100640010b04a2020308901410300c413803008e00003528010042c00304003030230b01c04005491880b0380180403680102c04c0000c1580300d40000a0260083c0710140c25035106000309400c13100e5040d03101c070b012180080c4c020000500d00c01d01d01e1459030a00d050840d031183c000141039001805002c0210340100020a0004000380000e00319080e00c050310344480c0055503904100b10f012140081200c030b4550b4200d5150700142d1081d40d000d42540c4001002080926402801c00d0f944480804090000d11004258101d114a1807500c80082d1a8500994140f614030740300c0020714801c025 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 724315575 1250 724314325 724314337
    0xc0c060c0b0c031e0408190201090b0a02030609070c0203072c0a0507020c012a140d090e0708060415150e03010c050a080c13030605073e030c0d110d0203 67
    0x1001c0440c41e0341c5210444c0215030041c1c0282c0e80d60b2400c000e00c1d00c1025050705400b90303c0d000e603000450400e80c1e5007003103a01c2a00042c80b10004600400402856a58514510b90710221901308104d003900d04d4001709e482d01519400c0f004000c12440140072550341900c2180301c0502a000e501c4c1030a5844a4485083d5003050314070001503400307004200100d60151400b41302c1710715268940e40032034020b49140840b114082c042a81c400c1944141422250418801010051660700307000034011324000b0b188a0400004100b082040840c002048403a5140c0d000b80c0c1c0e4226101c1d8803410010f031504c14405080100301a0700010444014200801e4141801511489515500ea070303410402112400d50302410000c10010b807a640401010451b501c1c03401c6654055402400001003d1a0aa0b4081c1044202a269440c2c06e112000c0b40b465000c82e983c0d00714050202014200c0400300c140c00490310b903000e004251121405000d10f8030002035400104d034034020445c2012203041c05900c08081e40c9030300c109 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 724316825 1250 724315575 724315591
    0xc0a030201140a2a26030105040e15190b0a080307030807120203100504060504051b130815070906081312050c01090303060e0106050c06040204050402010c0c060c0b0c03 74
    0x14210398141d090140141c81c1c40f10740703400c00344000c0080881200041088240c081c00880c41c0250074010320507030100c1c50303c041406641c00080f0300001d01e040070710b0713000511800c0d12443d00ca0501420354001440031104241400d01e0281c42400c042c00c501c8541c415180a00040628152a48002d0315104020b00100c6a00401651914a50b40c8044401e8180186144d0602c264804841c0301c56a00344000c500c24502d44030340b2050a4140030820094494990000c0d1095040600380001c42560003004005c61100c600c0441d0741d04a2800041f400d41d0155100a8090007401e0381c000c08404910881e510840c5143d40741c4050a4485000340c58143c000e84040d40c40e2400d0300c00610000308071a030254440e19003420414288801c1000b00da00303541c0e1700d0004400007900d603c0108009080300c00b00301e000d00700e40d0412500f0320a206825655400006001a205946980110f015640550300038a51950040d2047d00e0300c40c0c4903040a8035004140350b0848000c5822800074200142d404281c030300803562 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 724318075 1250 724316825 724316837
    0x1a030a020c03131a21180f03270906122e0621062408011e0b0d06110f030903030907090c0e0d1b090e070902040b09011d0a030b0402030c0a030201 64
    0x2c4d40b11851408014028640c0100811001e0b440804c20800800ca44c04010011644d0300c0e81092110303c280104401c0341c0511800c08042785d860340d149801c1c4e0350f0000042d290803482031303841d6004520300004015121240071410303040e40000a01100c03000c03a006031900c0f0900407207a03610f641c0720045855030002540718180c0b0f290500001c1207a00509031310381030700004103a0182c0c610b200b115400c00c564000782040e9500d003007440104c440e400d14180244441d01040041ca040640441c94000d0800e2000702190303546d981c6001d2141001042e01c641080305100b0342e80f07903d00012500d07540e0f402038407804814451444001110105402080c509080917919012158542c806200f405040310100702c804102e0007010184c00007005e0803070801804020408128280e6100015090014030b400c504559401040140407601c251812180214000c0c40c2418614150f552a100700180c4102c865034000b1a00000006101c00d00011500a600840581c7d000f4111501080b0005000748002401700e1b80d = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 724319325 1250 724318075 724318117
    0xc06130303050c03090907030c031a100507031b0f0b150f090402030118060c091a1b031603020604030f0c0b0705092106100503071a030a020c03131a 65
    0x1c400c60203040c03d990b8a01c11039061084c210700264401000b181c01c2000269030300500031440c1d074540900030a00400030b00c00c820041060010030340c1c1a4601201c03e0038440c2c0041c100007014410041481d03002c0c555000002c0381046c03881c100e03030340b079910000603a400703142140030802410414480e40051107000308035000003c181010300610100c000c0060340e140d50384040308003801d0032842340d414815209000c006400ba0381c081000c3c181921f103800c9070300301c003000f90314140c0200d5050048400c0428403d80001c02001200d8180b032442c42000490544611140030b40401c25070006001401a0f200c0e842d1004018544c11040761650300120019008203130110118150a000307200500e18242d000d050812030034000031081c0c01c149100d1081c2041d41e031008040121104040601402a1034100d01800c0c0152614002c4a030410b411484c08015080c000702060222400b42e0440d007080786d654007070701d8440000b0003902400540302d20400020104445102503803940640031602c40720300201d15480c00c10 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 724320575 1250 724319325 724319327
    0xf0614070f0c0503031b0f0d050708031b0703030203040302100b01021c0201060b070507080c03120d0c02160e060f0a050a0b070606030b13050d031b2d030e0c06130303 73
    0x10126500070340b074014002c10045100e840c2032005100c03d10790014030300d03540303103c1800c00c500e0418114460b81d6280c00c0341142402c0c0d10780c0300d011030760059008000316880c0c0d1034110020801003100710b060b40401000003100b07000c054158010398801e5002c0d40075145000b26500404040d10207103c0814018bc00504c4902c5d100383d8000300c24031016015100009a568980841c82540d9014450503100c03940103010400c2403040404c140114440107034045e0065071014800c1c480303103000740559080319940b11007000e8401442044068100e15108000c0c540480e9542c0e154580c5035000d503401c501a40040e00d0f40c6c800742c10102400b5049a102409440407140741c4411400c180e00300100440c3c038140c0b11100040800c0c07a41560134054498100501c048140b10f1900c20b150042c8004200141424841100411168ac0022076000043d90401212714a811105000300b03c42da50302c2580e102d107020415005956041d03100d4400d0303404c10011544604001c5042114074054010904403032041031205000103 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 724321825 1250 724320575 724320593
    0x1201121a16050d1506090905010506040e0103120e041a040b090c1e040b0d0b0a0918020f040e01050403020f0c03060103050309041d0619050a140c0c150c040f061407 72
    0x4403500140001d181301311880e00b00030701c01955100c0350000c4c4118000380a045010720540703005042c11600540b4051420b07029207a02081440064800c0c0d207685000620b03940a00c1074000d403064020001c004c04402041c0c1d2040c1c50f011003188038001c0e41340407400d21003400c00301215409a041c41c0040c0d030070b0424079080646100c401c1403112100748400e0000060440b00503000c0e01504540000105100c0c601809019422103980d01010106092101e08440529400c8040c0750140c1c0561710700030030301104070100780a460b07000030781c0c0115032a240030442450750208021211391101400d588030740c170310142019078880e001e00025025070006c111200749480c00b41d100c4040c1400d000c08d60b00b909004101c4013802c2c8041101c14481d00d024840d058100c0200a1141075486110000104090405020a00c031800f400418030b01e0381180002e00c8060780c407020071400303c1c1d8411034208040180b0341603d1f011100e130810302c140341801e030f180000800d1031070050708039100143d0180e481505245043d2500b601c9 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 724323075 1250 724321825 724321837
    0x61914190b010917010507020d08010f030305090103110c07090509030c03030a2403030e03191e030513030f05100603030c080913020a0e010e01050a170405031201121a1605 75
    0x42c040c03003540008913209140400805010b1031000007a45142c0800c2c041d060a92544480e8100030b40350f401404006130300b40b00c1d070040d01d03010320304182c903100d4450045e0020300806001c00454500891142c040f214001000c0c01039803c100b4007804151541c030b24096480c09800f0707000d20b81e50001d00004000e0041e41e40700400018409003c44183c6041103103607544113080c0d400680c0090000c0400c40118203041010304040500d080c05100751805035141da10748141420080301c5865940824041814030070000c0d43c007407070794000d07180001c40d03034910f4400c8500319002011030b9640103004049540742002c2c031036082100e0b016220000000b10329503581d019075104841e0182c0c45051200f658107501080c0c03001c0d00d12070100d0345a1100e180748181c00904140361507480300f0b0410004011240c18190b104202c4c141800b01200c403050561034620f8000e00714050500e141800034020350001440c070506805010722113000d416044000004804900b05095040303a20090005907070b801002c0d841c3c400c00080a13 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 724324325 1250 724323075 724323077
    0x6041b2d3204142d060c150705030907061806050a14040b0c0c060405030a08030c0c012c010501080d050705010207120509090f0c16020d06050408090a0806060d02120708061914190b01 80
    0x1c0c8038804200800e00d07c000d441c0300f07002407004410081d80384410400440501024285907581c0001030324040003504960082c0b0040180c04110100c1e02800703004100107142400c10050340701d42e144c20b001411030300100c0d5045020f1150451644071810200102c40940300701501900900e115900d0b4440d4540c00504950400c40d82004942c405002c01e110b00000003d003c511038112000c84240e640d0800500c0910b86010f13450000101720590000031480c90100c00f50070480d84500c43c03410700c84d0081c0503200e00070302001500104441001e90040044c1500c0c8021592108540c0b950b4400c204100701c00c54051030346e0314040110800540c2115860840d851000381461a00440ba0f990b15098902c2650304540c180d9020416689500d44a91501d0141400000034402c1c0d10b440c1d000690490b00814002e070007013810717210b2801038410500c2a100584002c108441c441d0502a80e400c01c100070011000c0c400a203052151400d03100e52030400c502403001c0c070900c00c003134004240000340100042e89140e4 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 724325575 1250 724324325 724324333
    0x70e010e100302030705132c060d1b0306020409020c010501060207030f080304020a080d02060109112d040e091c030603150506041b2d3204142d060c 65
    0x30101f00714103d030440c00b4102d00760032041c84103241d040c0240701800300c0b26142d8800d010b085c00c1204a40f0f40d01003003580c16802941d008818407001e2503060400c4201d81018001500000d008500e015042e0002c142c08101c0c0d00003001941ea0794803040341c071020180002002c0202c809000004903d1620286800500042c51480500d42c0c4892640c90101c502c2c481d031000d600311400402410340a4480d141480c41541035a5141040e20b100c51064041c999550b034a079181800c1c0c1d90b0f13a0102c04081a40c001d44100000001c460502c0050303a03603a4034046407a0440d1038070300b88030405210f12a010314000c07698041003803c090140f03d03402d040641001017965401c955a880c01820115003007052003000c114580350844103180306011000e00e0038080c04102d12161000c910704003a01d620130340c80e0340014040c10302014000112101c85964080715089090344e601c000c07030080741d055401c0c8108561024100e500c2d0700009004c4400d242c2944d074903403140901415082541d16142450001008030349141e0342a5 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 724326825 1250 724325575 724325587
    0x3180121051501030204050f04091406180d05130b0a0234140105040e13050a0c2606010911070203121306050c0c0d1e03020303070e010e100302030705 66
    0xc00c4409400000902441d440e4018000002c8400c0c1c04407515980a2906510380340c20103000c140011207004219003d20342e9002c0034803c0c84001804c3c001c100980d03005854142c01c0c8516601e140c8030f00141c042c005805404c05081c0d24901070001c80e907980e02c40f03804041d411031034000c3c04c0501350088640c03001980261913010f0543c0c1035015001005181001c003c0b1005090300711141c18000280d04942130030340003c01c41140f942e0700042503408845880c01c10110982c1c983d07181040245021000802c50b1040c11001400c0044280060003500c092002c210480c07100c4035000200304200122070012904000300605c00b201094000010700f107803044140d4035264280d4082072500501c89102c1d4041140420301c8200c11000560582c020401c503d442c03400c1900007082d80c0d40b00c03c05540031504c250340c401401001c01401013601c01d8075810704402c40d2032456079800c010f512540100c6451000a090388144c58603036020382c909103840f9030040c00c0361a41041a0005400941c4081c103c3c00c14400240301c0 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 724328075 1250 724326825 724326857
    0x9091401060f0807210b0c1c0501090e03090109140111190c08030a091e0b030f0603010e0a03140a1b051b06160204050604020409090c030b0c0c031801 66
    0x5010080c001d0b0300c8921082450500700c1d50810703820f034018150980c40303442d11a03910315150440ba101c460300110a0540c640b281d281d1040c451040c9010214541b040203445e42c8400345035030100f070403034664803c1400701105900b0301d01d132240f1800c1001400301300550303414090030f2507400c0e0340d100c20b54040c18640c00304210445400c1c5800d050003214140c6526146014082040f0030404200500038840250300b446800000a004d481d203900501d112025480220a107009400f8502001001048112581c030709001640c06032041045503614040e60800808802400000500a0800d03030142d0350250301100e080301000596008854201c100440f203d45030580600810403550128410320062841415031042d80500174100b0911603c9440305001c1d4140c002d06d0000b40c55945d5a04450000f960b646d1040010000d000d160802440b0903d4111481c0401c549001c1d2241580e024100294080c0d9070800004528400d0706050700340e540042c841e41070b802080c00fa200ca400281410b03c0c800c00300f1907500c = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 724329325 1250 724328075 724328081
    0x9210e0414010819170f120406360201081510080910021201090209011101060b1806030705070311071203080a0b01020d050f0c010906021216030903080109091401 71
    0x315800400704084010403420604010040300940034480491a848150f110482c29406408400b20f0500c00042e542c0040021402101c00d140840c51a13031000303040504102c801030021200c0320801c4802041d07070030307450100d10149105400503e5004160001a5801100c3c10240036090084100600d401d03000503655100502009080540c3e80348000e140c840c1100e480c3c6120f040518102510401402000c00c08510b101c41c19550116005a6110800700040300c540c0381c0c412000c100703942303441f10202d00c0c101c0f00c100030145490782401000040c000c030003c10405100595444011410411000f0002405a4410400b4400e403100342c5400541e2805e042400b164a00001c030000b80010302000554200c0e40300e442e10b41d0f1020306c000d0114122100000d002d510490a01d14806e0030082840940c048003508502c90b0340c0da0000095484603101c0b40085450401521807609520a06000301d105074420300c510400140c0569464400341d1030f120a0b0401840210f0f41940c5811a0810700c0ca18130b04240 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 724330575 1250 724329325 724329341
    0x915150e090a030f03060e0c09030f2b170103021909020f072307050103050c09270c0a05030c03040606030516050f030a15111903050f0a09210e04 64
    0x903000c0c0c4001d40c02e41c0f80c0144102c44200f103010034503150007002e114030465503121382c4e0321032000403081e642d5208140010385007500028901c036440c86180e043c4a090340060b03c891144140010220040317240c45841a5944840068005452030001d80100050f00d481011007109800d0044041401a112040c01c416030b40f1580079101c44140002c2c040d400c01102c10440460010071022031011441e81c80191510791b184c038410301e4101a100c6c00451042412001101d403081c40c002c0001c501d01d462040c812400c980800504006a10464005140611201d0403039080e0041995890300d143e644109403a8a904090401d40b042541e0354400300c0092010481d060072004d49809184001d4a060708125000e648191100c0c0203400c150b80f9100081c400c14a000c4842040d2500459004054000760981c0d01602440c60b6a07140105815249181c040e8450740c0100420800ca819940e0f408101a041d148000300041081d5040e5506003c0d113030b84901120111981c1f860408511500e110020b03065803010 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 724331825 1250 724330575 724330591
    0x7050c0d08340c030302090d0b0105090f060112020705070504090305121605072307060f0801050f0a0b090d060e0d090914062101050103120e01030915150e 68
    0x1400e0040c000c01c0c014415500c00004800d0030802d0102007401005440030000810501910340b503010200f41c040d80544e280044003412810245126041030b4905070030a12a140c01603070f880000c41e11042c5600c00701c0b031040406840d282c00908a4105000c0207601a480a60b420302400344042010b55450165400003802551543c0d100c211a13001c0450981002d1f090040c140c552840070b0303a4058020342600c0301b95410284a400f00300f00c4288010740901d1400c4258418000ca08000c60710301c3d042285121503102030780d600c0b401a03898105020030410084001d950162946d0410040440360380020036070680054000b2090182d140d4841040d180700030b40540b0160030480d1644900c66001007a20000d080440092004a0580b0503060030000090001d0b80507100002c88070004030b588001c14076041c0160002004079607941e003032820441c2540006880022400c0c07140002f503621078000d107448150450049004107109070129802020f18844031400e031701c1d91303003000104608141700e024403400b90 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 724333075 1250 724331825 724331837
    0xe0105041a0109230603010e1e010e0612011b02010c11150604090503190f032a0503060a080f030306032103010501081306090c08070f1a0307050c0d 65
    0x10402004241c41c00d102401d8a41e401050240e0034981e8007140041c00c990740003010b90003618131582940540d8078905103042d00408004000903030300000d10320080c03042d01804d10302c080d0f01d0201c660b856420b140a20a41d02001030406c007064044c500303032034808640e0075a0f1000041da64400c2c9069400c540400741a000540d649a080c1c0c000d0300d400c245502390301c90b1054044c1c00c131400a20841521a0400b0b444180107035611020001044020000c407002c12840d014004071980c0c40703800007403445182d400070000090a0403e0b500e407070092008041e50880301180c0550450256a43c105d909070402014254402808980022010028000c1120450480014554038544402494a00490080c058442486036020030311401c0801e03056a0640d0001d1074554031540320140051092000c05c00090821450080b01c0020080f580180c682100c0e041c5090b41c05040da5107802c1c0705130580d0f91081c0c924009034a812059032030000c0000f9980003c80742061401c24890000161800c3d89004007031000c285 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 724334325 1250 724333075 724333079
    0x120819050702070f090c02031b160b0415110604021002012706050f040321020403021f030e0f030a11030403140708010615051c0b10020a02120d090302010f180e01 71
    0x210b413280882c0a0310803040180021070001c10001c0d5030303100c1c00700140e4000d80c500405d9180d90300d00f401411220742d5408482c20301503448400483c1d041e44103101c0c20070b079903c0b4911101001c3e401514000c001c16070140c054003041d40d42d80c09015103680c0541004045559806010710200c0700b0000390b40e1140c40345d4030f042c07241d0341e2940751080888001504d4884401d00d01810000001c1e880b82c0402000450004011203030740301d510aa03030107400f8a42000358001900686200790300c6022181e910400c81c25030301808104013914000b500e401004a480039240c004011051503203025090604c180d818036000c072458169641c5454201c180b17040d50400c8150401c200070000d01d1000d00036500646204510028a14540300c07000d419440f85844c010b006450652110032403602950083d0b44284019000446d11a02c0302c900a456205440c4200d119041a0700b0100c41e42100142c105940031080d01e8801d1820300356001999044a0350011a0402821b502612507031f1800000c0ca0004120000e0f1014a81d4 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 724335575 1250 724334325 724334339
    0x250302042a170a14010303050a02030d02070f0228090e030c030a090510110601030b061201091104060f0b0702010507050f0f010b102105180105041b050d12081905070207 74
    0x41c0040d00000042c0e0608062003549000341c09513604580d07041c02c015541e15a440800e90450241c400801ca1083c40858840240200c502101c0d440920031558042c01407a40402a0480813401402d2895000c40394800d00c90b411140e8009908915500f088908108160418921390303481062400001502608104103034103001200302c0d002040d60608076011070051851031794a510510010744900300c41c1001c17410b95110f40c401450300300c4611000307008165060805d40134003d940c8a0550256140c07190004001e00500000e009139010300210700d14101c1d032900111415000404152041d010b280000021400d08020b03000900c2203071000455400d1544003044203c03109008540c0074407040c5402041440384015a29080035010540010a07844811003030f00e209d142280042030f40d40c640b105100c24058070380c451021407203a5030440000c283e02e603024444100120a401882450203a00b40c0f603166014442d43c561004e00d4410b0901020a14186442035a40c10ba9480300075030440740090081d8 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 724336825 1250 724335575 724335617
    0x30d0e0c0303030903030c1615060e060307050102120c0114010f03020102240604050403121e0b040603020a06030f1803050a170114090405070807060f02250302042a 72
    0x310048019509500e04032440d65101d21005100440032040000c0c05950f214003c14607241c6540c0001c40480f000310303202a608024809030044c05030f001c01040029400e07103400605502034580680c05040914502c5441000c1a04801e6000090395210355840701128942d100c554020800e602c0c50318440351450001a00344850088100c817991689101c82100c9210b000c0c8060300150b00303880c000341d182c1c1d80b801d040310005031200c01d542c0b007503003820b807004403c84040042d00340f140004e1307408000501007941040111f0380f00d071000a4105505c0e03082042110301981c03240c0d02c3c00e410600041500284a0840c1c0c880244c2148100c01007000414566042c5500100041004001106410343e6504004140b051a59802e41d110303c507840c2a0001010231405003c1c0e81c00804240d0704990515445010252a64038407400080052103070360800300c550110300104081e491001042410114215003d01c0007a005003a9120488018034540030404d005118580d0b1300c40c10380741d0311032000c002001204825 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 724338075 1250 724336825 724336843
    0xc1101020610050d034d1c09240806240c100509070e0a06031101030b0f12033013051009050c210d050d060503030d0e 52
    0x441d4054800c020151105101001c140c48084070500c02059162804803000c1d00030180706e0380c2411001094030401d00c11104810003541619118281000300700d104a10404d6450074034078441d03800f4000340c107030a140c165056545000c0c10f00d090340e80c00381c4440c1c001c0c201051b04640000e001c11f410146031001d50303002c100c441d041801100c0c02c4101100c28445120480340c50a0307032003884140054041503986040085001c508070000c07003880303649455211141c0fa00403910030070a00036a02d00014804064074418542501d82c000580e005201c203d000442c01840007a601030780040304100d8640d0513940d42c440c9003000401d1000210382c1d0b00c442e052130040c3c09889903190713214403002d1600952205001c2011646c0412007000384403000505003040b903e031211034503010b2092071521006206001010840c00d400080560b40032074402c0c1040d0040d0341964102c03000004a400c2142c00390820b52203040180303144a40b02c6070100d060350700c0703c0019003103600c10720b1600021683c5150300d00b036158080c004e40309 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 724339325 1250 724338075 724338077
    0xf0b2404090201020d030209040b0a1202040b0d0302070e070504090531150f02070c080c0f0d0b060d150f020c1018031b0b0103060510080610050904080c0109030c1101 73
    0x3803100780d54000f07981c1e12411070454050603000f050f01815a120340e484800d200c40010300c42d180d240e9483c8a01181d07902ca001d01603000e68100129414141800d0030380054003581a40104500b07440c00c88100e240d0351001d45924104141040001a050071380e00a542c0105c002040c40b6003442c0c0c1c8010700001e07070348140d406c05150702c0c1701c0800c4102160120f009103c20000110012484070380d80082c9100074414440020601d400015004c40c0b0b680700020030140e50030060350f00800700505407040100942100d44014512101c0500007909818421504241140714140780904068030355500b1003990b8055001f00301c0302d03034081501982c0002c00c0064401c00c00c00302804100c1c1414594680550b0030398031101506010380e20b042000036126003074040d64100e40000070403242c1d50b10303460702038040c08003644c501444201401c030104080d074011030154026908034850b000315501d80400d2005101d80140240c40041043c401403030f18030350a014201002c0d02c00d07074591088480754a000305e94034a24514040c = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 724340575 1250 724339325 724339331
    0x503120106020d05040317040302060c060a11120103060903020c1c0b010b03010b220909110f030f0c0f0103020702030703051f060f06030b13140a0b0315040803040f0b2404 75
    0x8070f0300790401c0468058a8004210114000e0725038001d2000b48203079030000350441000a13521204034000705032a40181d090f00024441210011200d540c40e00440c942508080c0d00c54004000041007607004141451190058030411013070f10001550f0801e4203990030120084110a0408011000c42c03802d02404140c02990b0441d418850400c0c094022545020080c1d1041c0c44260084140c540c0d00368024203410301d0600c1007600e1032130129003052040003518091001502c004507603107404108800c0c0c1d132111100601041e0144802c0105038a0860f00c00c905042c0c0c20444880980ca05110050155025000520559940c0700080c5280803c0043c17000190f482c01c0c1051182c84d040b110010304960841c0307004241c040e585d100140c0e0b40d216501200e02d00900d448400007803d02c1480c50544601180034080211203c16402d05032660450141448003181100c0020000f64a0101454016003d050740548642441e59030500300301045d1861000c000142c580e8060041e4040362640c1a044191024 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 724341825 1250 724340575 724340593
    0x50a0e0102160b1b03073b01050a180e0603160806061918050a06060912020d081b0312160c02091503190204200403060507020a0609050312010602 64
    0x40a600d0101c1480200f032940702002090312010324098080242e0410306410380c1d2404c0c0058080e21034210ba0582c8141d0366401c44c54030903100400c8030f03040b460001000204ea2544419001100d050340400c901d00203110120481d8000031441080c5180540200a000003450522600b09842e042e21040352401d04201c0f41020f2020103004224140c00c20070079a680c401e4031001581070401564580c000500e841c50205d009070182405420207800340c01942420440c084e22000704407541541401990050301c00780d80d21800505086505a4409018150407400c20b03082c0300d44146101140c60b140441688082801f03000d104d03e40d503056800c003407114903094180040c85005003e1640d0b600300644246000d06c006085030026403503418541c5802001c0c1d40c4881e618014459482034070440581c000c2d4a8028048240c40b01e405451500c00c901c484260706107480c50f9100c40280c840103180c3d03130440c02481c001c0c1d800078849020b14104503100e5405107850b02c1020b0746400850340168070450440d0b01107080 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 724343075 1250 724341825 724341847
    0x40e0c0c030a03090f02090f040b07030c050a2604230c1f020106030624090b0603060d0302120a03050f0f011a09030a0b0108030415050a021c21050a0e0102 68
    0x2c035000c40e8140d08010072402900d040851900c800800065040540c900c20001002040e008a078412403281300d00b02120789414004034201c1d00c41469460102c1cac002c100b070400603401040031032460507081e01e4039201d0f50304038401c14204c044155007c8030700c80650610410a0305030b07018280d00b50183c0000a10701124000c00107810341d147c01c1260080305ca29111956006072003074000e90042c41d04040c0a002c0c44510b828444007681d1115114080c078a80040080b51103801c602500e00d5440004007000d0035a110842040000300003240c0c02c405500c6800307000f28181185130090038510900b51000607091900048550044400400941c11003290744c0041c403400c120038461004400310f05141d04c0c0c41d00344410100780f41c2140020050900240c01000183c0e0420000c02081034a41c804266110111240b00944143c044c0340c800c1801b50700f08440103401145200000100801140340000b13140e600c68000380184101e40411001180e10303403041186001550081d90b0b400750202008524012942c3c003 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 724344325 1250 724343075 724343077
    0x2130b011211042106051005130e150c1323030d0c06150f140f010804050706030c03181b05010c02011b0807120c1b0e0711030f040308040e0c0c03 64
    0x41c02c980139811105061041c1c0510038911310a40d8001020003007418840055015a0500c1c8196072140e1702640080c00717140e005e1300481000c40040001060485560b60740c1005005006000c43e600c01014042003504403c3e8000d10001088121402c600d051454088050742140c44018180290f11540b000f03002c030350340a1408007816400c6180000c10400801c00c1d821005100c0e0300c101a802000500415421001031610032044d400b2034a44d151360300a0340054400d02c80450340600144c01022040000310f00070b03000744001c440c080c0f0700080d074070140c020798040c160f00c1c6000907210296036404101c99110240c0c0018060482409c001c001031041c1d5000902d0801000d80c3d0450035a1826200f0041200301e405480400d64000c603403001d20b903481000180036501d1a801624020300300080c00d855205842c0740b10056a20807049448140d6840006079070f4140c44181c826494441040410384110808010340003540c844c001859031145001c22803012a4800317044010b0b2014100000050150000 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 724345575 1250 724344325 724344329
    0x10212180904030e03011118121002071e050c0a0602070f060c11181603090215130506160b09161802040e1305011803081b040302130b01121104 63
    0x103807040d15556071407030110381c100d90365101c1d55010343c201000707c0030a40d003000140c040115901c24121000e4050000c000000c500e4806800c43c83e04042e802d00d00c000c2898000300388190003061502e03902c41990350702c3c0c00010201c800c01d4035550002100d81c19a41380c00b485a00c014180340c801022082e003401914411004180304032400d0200782492042002144000f02c090b210700107100a010f041e034101c8440341914200c40c25440600c007403104840d228020b20400310015005006010b0504042c412004154003900a600c0820304010300058540d5401c0018483d840c120a084101801e007840c06900100c80a05204943c1e0440c1e0202c010120700b054030882144c264100851000c4022820b01000780305a411481c41c01c5448400c1280951840c0040d1600e148900300810903603105505121800c3e0300c07404000d0024102102180c034070304003038089820186807100150300e419035075800100a0b0310719504110400b901c4130780d525002e6810041603402103020800510840c240b56000044510942c = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 724346825 1250 724345575 724345579
    0x1e02011409030109050313030210021204050d11090a0b030c0406030206090103110d0c0201020a0f03021614150907060e03060c030f0c160606031704030b0f0a02070c030308010501021218 81
    0x118070000940c1d400d412110200781c01000b41ca96031075001003000711400c401d0100340d02902c44a0ba01b652400d04c00142d03101a01e000c0d4a00038103090410041100740c040120054501e000d4061840d0314030f07a2003a89440c0944100040080c6800800040c9401c01003000e480e184564a4100204090703200e0204460b90840240380005550402100c0000c1a010745000c0080e89482c0001c000c08403901580185030804c110b0302d58a01640c00c02d0f000310160306c40c02c00300002d0945407150796070008642c11540e0481180007405d079400c206482610391407920040300e103050503034001c0c401008040d400208e603039120007058014010500e0540142c0660340b0004d4a600c001498540014004400e10000d0b191030300820340d042600c8103024104034000e01030901096a28884841c509908c1581c0c3c10100ca040342e03445141144551f41d04000201d84020003004204031a401f00a072100140300c140c0a0b0020310301c04c0c1c885442c0d07541010002490b014500404060350001003000030a010f113016480c0d03000c2502 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 724348075 1250 724346825 724346827
    0x70b04060612030512010b460e0a0501030204061409010306031a040c081906091b150e03120415020c03070f05010806030c15030a09020d0f1e020114 65
    0x110324121008005580c0040c0081108690040405038010020009040c3e5917a901800c1d036201d410a020b0340c07090320040304039119103404c9030007003140d0300031600d0006d03e200c020664075000300e08000010080a03d2003000168203840128074510b030244106029040030300e8118201428442e0140c504440b03284c01c558410004a460b0880740e104c0c0c0c0115018591101c41d034000b18000740441071103c4010b503400c5810422410300814003000001e00140e02500400740c003101c0c0e00103070f2201c0e4020a0041c40a507950060f5101d03840301041a030038500700900b404114204c04400c4050010300304410f140c50b552081d0400020f00b011220901c1c1a14107071200500800315107003490300160b1500b54210303400c82d007501684034000b5200700001828000c841d802e80f200d010980e40c12042540310703a02900c08643c403829510005540c02d8400025541c010381c02c440c0055110800d0300002e21354480302400300c41c1419080403042c00c1040c501d90081910288103c1c0703040041c0103900181424008403803400403800 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 724349325 1250 724348075 724348081
    0xa09050106050f0d0603020604030809100201140c07030e030109051f1a0f040e0d020714031c08090703170304030e18040b0c070c080105010f15050901030c110d020d09090b06070b 78
    0x44190f0241700190750003802d03140c0e920b950b882e0000194105040c420700ca42a5140c80100e07150040c01342c0180302010703506410582d0340e40986604550040724007a8204000e60078401480d0b203091017040b003250b01901c0100181d0b0803803054071109000c014000305c901e604003208200c0ca001c0383c071504d104030202103c41e12050030142e8003003802840d44a94464880c8200d17090350319015004100001a01c145550b00c40807030301c0b000c052541d2103404211004803c0200d645418800f88101441c540009440c0d09480c40e142d42d035210803110400300500f40405207400000e0008140c1c00c40599140540300755220b64604c00360001032010401c00800142140d01200e0004168030010001c4981d0b065202014000355a126510701c0d0003480d0034000d400c41d50501c0c136004100d00441c034030b44403108076290703454500d45000b060044016114080000301480382403e001c200c10b54003448800000701d613030b138000c1c0380c0c410b042c80004002003440c3e4041801d46290070007401c1c1c80d8031444211900140c2020b056440d9413 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 724350575 1250 724349325 724349347
    0x72702070b040609020a08120304020402030403090f060810050904050a0605061c150b09161b081c0b01030209030a02040203181e10290301290a09050106050f 69
    0x481980030061540c10181d0030041004000e40c05061204d0094515200039070f2100300c11555100710301c0d22108480420b2000400500d0543c006503070161003403070946609a520240012449103581006021032070440401c401a50360481210041a048034440f00c82d0a1507107506031079001e052800303031140c0d844000042c8103894012141e00c2711a41130301c1098800d074241c24800d04011203c3c000201c15800d103102c006030343c604090002c0c05071941d15901c0d1a01025240c4c26610000105c1c18182208071803000314000c110000c01a2210514600c41500c24800d41401d00040f0350030000d069062510600010480303440003d42442d40540c165401603032034555590310500f9103030f2540883e41901c6020715182d820b024854520b507100110b40d0488000036620f40164065644a00105a001003040003001000c003108000c04400d0201600024040415005994814854004052040071038080d4510070b8100070209000410515004205550400d5030041c00c80c0318840130300102d14000b0070040009 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 724351825 1250 724350575 724350577
    0x5041203090512010f050a0614190506030708071b0b150303041e032607122106080d05120a2012190e0c06030c041a091002072702 57
    0x580030042043c0200a11010710344c0c041c001400e8481034041c1000701160200502c0e000303001c1561040b06481c9a40d01d00301c018000342c0150351100c0d4801100603d80007500351280c05c000c40c02640c0954400340d0324600030348081c1c06080505132154111491404800c0468901400e06130020034081d40e005950a0103c0040e165000d90380101c20441030052011040b080e80341c590004881c03003405290401c070344541d86041d9401086602c05445c00c000c002d2000005e0b60089080c58000c0c0506082e0300038054070f00002002d0020146400c08a0b03960ae00510950380c00b0404e13484004d6280c40e000d4a80f680d01c5060464142020301250000354540640314014885481c00b032a070480380c0c0142070740703401e14078505240a41d0700b80c0c0c0d41e1360726040d6a49251201101405180150721301c840083c01d000c28554148492544001c14003100710b1010720000c2504816044040c03285071071040d2140d207402c6502c042084034000c1000c0701e010743d0310407802005005c211072154a0050702d840c0e500200110040c0c2d40c1c80107 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 724353075 1250 724351825 724351829
    0x111120328050406060605040602030a1b14010b040e010c0c021924030506011b02130b0d141002040602070b131d040c05010302090d0204020d021e0304110409030504120309 75
    0x101d8250700440092940d000c1c5125030f004800a0241c140d60740801d6400344175901030300005030400c016820500e801286e04c486000080000b42951b1003072501c030001a0003280d10502c02c5651990145c0c0706520f400e02522840f15800d030020040d1840c4490040c00b61080e020b40240540e400b8a0341d800e032030324440c801c04014500080258410407491007500800b05c05620600b020901c1e1002041740380d403103815513031000312600c40000c030402529020446070301060300083c42010749803820311583e511010b8106414611880780c00400c4400d501c80700d400c1c0003100c040d00507818810702c010010990b0018500d4203c60400f951580e80750b18011303101c0c0c0603446030303044103070382e44403400305500e00709260f40040e440765011740c18108030151204011402c3e0300c01c816800380e01c02c1c00b50000340094030702540204064a1800d07001803800c01420521030646d004140039030381071000802003005100d400703203c5801001040714108225541075034050300714040d5020b8000d01158103101581014010446200 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 724354325 1250 724353075 724353121
    0x105070605180a1b0b1207082e0303031128022401030b060103110406030c0e19031e0512031f080303100f1206180c0905040209010501111203 62
    0x15203041075092440044c43da1018200d10101c010382d0004611500c102944c401400d115007503901611051400c40f1100c1c400750040a0f019403040040c4d00101040346003640320a402c1040510840c03071818050111110101100540d240400040241d440da005560030441d42039000382e03602942c0a002203141012030000c0340c45481142c600d10307800034440101d00f8100c0e4403508841c3d220741d40c1e09004409a55200e030900414031018802130010a020f0307040000043e016180203079071400d1f1400056129000c900e00e400410281711b10078814846080e94900c1d42c584a8854140c02c00d015555041e0b0705c0410b000b00c0c078008440840456100d20403488194180c007800c4445580c00d40e1540c10f1a503c0703038400d031000444804582e400052102254003000111307021034803908800f01c41500c4d120080c007084140018050118603028000804d100380e042c1c081c0032242400200e5141520520000c0d95060700800d0500010740b5026049103000507510301460590014207440342c0f900c443c4120500c01080c0c40036 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 724355575 1250 724354325 724354333
    0x501051f0504230f010302071221060b030a05060d05030306130e0a1103010513170a0302130b0c1b0321040f031a011203120525050d0606020c010507060518 68
    0x40f1400c0f01041141c9481c821180340c1c503c0300c605801901203124244c8000c100450201c0740180c0309000321400c1c003c1c450203070012007402d0305c0800188121074044e0801401e205c008014015074020038454154460001d403400c86640c2242e490711983e07400000c0c98503226129000c0ca0800390303401c42d001103842101d85000c44004403203d240c11240ea800d10100280258603104c00681701e0058150444401500042030f061102c04801850282c0e41c055144001416001c0080c0b4510300303405002c890040442c2080700c2d44a04100659900304041d680c0c0c440100d40ca054603018013a500031654907a13044031044500c204040f040c13aa40e806000700d40c0402c004007a004000070502c070540f000001110b00395808042c0c030307a032039000c20b41c00300003101c40c0940003e0b50302c0305003030142505510464102c1036094000030070300d51080071404602c002030f600300001134003c25100c61107442c9000b16000b40090307001401c0c1c20004180002c00c20b005121020340011780360000300f501d5541030320b5080c079030b000000159 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 724356825 1250 724355575 724355609
    0x9150b07052a060a0c0512270d15090302070f0b0a090e07140c0f010c05070501150509060409031403010e01080d0206190e1603050f100501051f0504 65
    0xca4541007008091400320804241c2412400c54039141d002c40300000811160500703140d0346080310034003080070f0112120b21502080300448809840500021135200c04900c042e0040352101141c0340c180740d4011030040110207040340c002800b184607146440e0340e10000203160000c0b42000c900e0214554030000703100b040c00d0000304005c3c240f0300c0100a80801034485818565541d00b20f182101c030121079107000126820030f46200c2c0d803100703001407146281c000d044403911820808107a013143ea5051030a40070513030008640041020070300503915242e40e641240030b802071414000c203281030001062644280c0c1d803040c8860405002c4c08000c29102c0900700b0320b6807207684900501810180030b000300c031018424108401c95407480024854401d59400b180102031580c25400c80740039241e4200c1045450003100c4010000320131400515008500640040c1b240130031030050642410150350039143c07241e003402d0050002e6140c0c2110102071007490419140300e003642c4e0104a6850242d600001c000317200034406 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 724358075 1250 724356825 724356833
    0x61906050406090b0c0a03080613060902031b03060117090f0f1b09010b160c08030c010507090602070b370915082a160b0906060d0c09150b07 62
    0x76000355507a50f02ea40c1c00c80742d190088205070307009048040009500019174200064400c041003608448058000484019000550000d440303098110300742c2c681e804003c00c100ca0180c8089040d041103240a0f6a1031400c00e000024400d203082c00c842042d5140348004920f610f00d08100c1082c1105182c81540d80114400c00ca09403114441802d01007001c1c41110100820314255403414100c1d80c070b0342e444606c2d00010940325030070100881010348100049490000e1007038000c2c402001011091000000c86282000c009000d0030740d00d130071540c1158080c0c0000e20804110034115030f40e0000c1300048610451040e040f04000b8207141c214101e884a412075180046508203078000d0540b016140a15140c1b9680d880c00c580f400f00481c3d1400a40c45860b21240000d210281c0452580320460f440614000903207940000d58400c10300b044440e0b0184908010b190f1600748045a00840215000a5480c06540b110042c803c203601483c0031081d0340703412103542e19150030380c0341d00100181103816844401d1420 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 724359325 1250 724358075 724358077
    0xd022d0612090f120315010e0603010b13150f14090a1205100c0c060c0306350304082d1c0e0f010f03020c1501090b1002010e0309040506190605 63
    0x30780708240e12543d001c1446281d80407803221000302040c2145170955032036406845040c40200c04c09030600000201d02160303521032800860103004403c03181a0340e00c082981c04101402c0c95132180b054810305415030310b40b80b58000c00355002042e261030201525048901042540d1040c4100b07181e01031090200002e00984240d0381c000194040e4080d00c184040700540726080c5c4180d069442c00007101c04100724005035203580031040200c0d003880c00040c025221b00c0b960b01c0c180010b255281440c108003c2c0c8205400c0c400d80d820f0700c0000300030055410a07203021211a52103003113003030207020030068052140001c004980e1750400107082c00d04039445e45224440c1c401107075001c2907450000401d20031036009a07040ca1182124011810703980d0500b9100880c000310000d400848040405001d4030320b94041031122070180e01e01902000074000b5180c8080000c1000134424075001e0802e590400709800b504180200507105039980540300800c55545000009054407404606201304d6071102001003071681d8004 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 724360575 1250 724359325 724359331
    0xd0203040506040506072607030e0f0c0a081207030503280b09010e04121103040e150901060807080103110a080307110913051213050d0b060f0d022d0612 67
    0xc181c481c1d91b191514121418401c2030310000000c200c4a1464468000d01c8400030750000c014500003820041009040d410008800c051401d1a400042000d4880c50700c2c0d0445401040c40f4001862200002c8a081c8a80d000c3d108024007440300c0840003030344014a000e000c00c0b504a6604e4004034894801b2900ea00610800e40c9030750052000800128101c00c800c1c42042c011500040c491040300320041040303d01c02b20364440c0382902d000c10b00001400680031400a40240c081c4078000151880d02030502441001c160300990400121106010a107a04041540c0c10341e600300014040341901c02011441907940c55000c00480c5c40006090818444070300c60101c0603ca00b1540e031111600c2c0d4292280303130031035aa040a030503500b1a00b80802e0380c00a01c802001000c50740c08018403829a9800040d008501c2d0b01001e92301c184001c02000201c0c5415101c044044074101c2e0626565155500802c4192a02c02075000411b1506c1440003503d8002a40050b03001d140100710a075114240c0740c81c010f02500075 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 724361825 1250 724360575 724360583
    0xd0206010303031b120e160612110921031207050c010510061b061b0918050709050d0203011122170a0308131b0e0a0c08010b0d020d020304050604 64
    0x4d0002d840d901c0103508070001031003040d80d03000196020320000d2801003c0618540307a25100356180e840c0c080014a03500c4004100039203e210b00704841c90b000d142038440c24a140b464003075042004440039a03c140c40f6000d54400541c20403054141091007920310310032000d0300641c500c0d8000030040c0040c0e04c80000c01400c04198003d01094454020103100042c85004031004917021030042e4a401c540c014000c12114010340000c01c2d000c00c004e40544142200c181c0d50400146200c005108000d0200c00b00740030854122420801c9141544000f4110009401803070301c40c450034100030307040d0343d8250421081441072000e01640d0305a5261050078541076130100280902027030600243c8203100b4080501502400d03800742c02d0050050340c04491a00c0020500c4440c06440d8840c0e1020800c0d41c6016038141104030000210035040c10400c014104000380360010041c00c0c0701140002980c0110628111410034032050784a4598040c0391019005141c401c4220b540b000c803c000a004000030300328081c50003 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 724363075 1250 724361825 724361831
    0x80a030e011802042009061c1a12120313030201240501090f050901090b060717071103030306130b0d1502040e18030403020607060207050102030a0603110111150a0e0d020601030303 79
    0x221170303040304581407881500e00c0131507802c1c44000a6802c200005101c8600c00e903491042c4020a001d00340b08480566008102e00c421040700e00b416820708002c244070b621f00030744c02484454603008400c0c0f5203200040c11035842003125048801054000d4022072501d110f80943d9502c80000c158420420042324412103000900714000058101039028035442034030300181403e821a0b00f0300d40c0c4440584454405147c01080801c40440890032000f10701d0410708504044a84d034109500b4508100440780c400c0e144243c04c100300780061540d403488181030b10403202d4400316002c90f10400040d0620401d0001500740d903000350044c1c0e01c1e08100c1d80140207698090701030318041e8450340c01000548070014030802c0036130f00410040c0094580b80c00903005852107448054500100e60780d509003a07800a0381c002c400c10392100014800c100e812003a50704450070030302c0c080440091682c403091750352124103c0181c03251085000308950201d550403000700b007030100c02101e04c1f40c480c1030b01c001d40e075100c01d05c002d6002034070b = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 724364325 1250 724363075 724363091
    0xf09030a0b071e02190c050d03090302190b0d0c02160608160201091a090c1509040f0e0a0615050303040e0115030207080a0e010c021e040e0109020d080a030e01180204 73
    0x40f182e1107180300d03012154010b0800c100c44c5100c030f95594015030403d4a032200c09110002e07540e03403280800e02405101e03a48074005145940b041c01b1010300f003101400c004208081091203081c0200302590300303000c40e0100100344110b0714001642458024106241010700444012400355040031003240241c8448440300c0e51248040012130884058480042140307644920135101c0070000c0300001c0d000b1102c081551a410f01020015009414400200d84221000724000707031030345030030f1144e2030300c0c00302c0454180b000c020308c05000c07515010585c074002e1845580706245c14401000703c811602804c400b8003240c1e990743d16119400d821032000d02c18611030104210403104814030a0080d83d48550340042c03118100061590203550450340c1c20400303410883c90328005000f6941d098485004000c80840010001d4100400c3c4000c1d40c8803010f984080343e041601010050302c8000d10907840e190002845900d030007240d00308078050311a0182c907881c250708020012020704025104800d183d442201c003000244 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 724365575 1250 724364325 724364357
    0x10801050a05030307030507050f0715021903142803050603120a020706050d0209031b040c180311150c1e0105150609010507080c0706030e06010b070204020f09030a0b07 74
    0x207200d0703001d00d0760503070000c0c09503c00107402031000d044058441e00980300d010540703140c181d01d0800145d0018911071015001041c2d040c0d0103210000c40001c45400da040722000070313200a411220310a500c051050030006050301c100001c000d50054002403903a80c3d162165000100501800702603840620900079210390810010006049845648003a0054980341c0d02c1c0c410266041e802c04124102c4064003000b288506035400d010201c01c00c000e6146101c4080040d4050208551035818840c06012a10182ca000c0c11080c003520000ca070342c8500301d035403003c0170800401d0800f40354010305002c8440205041d8034060020411403002d07109085d034040040d40c003128450903110203664811126100c03004901c201e04000300280100305060600c9440c0840b59034441246510541c40e85d01c140d0846c04041c04425454001c82040031160f00040203654102860806180320f2044000e1080e0f5001800050308124032080d15020f0800a05403000d80c0964104400d00c0702e0304803242400252840e6800c103c00d = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 724366825 1250 724365575 724365589
    0x40c0b0313110d020d12030f150e09280302060a020315040504020102030f040f0e090304050310200c010c18060905150d2c010b090c033301080105 64
    0x6940c840710640341114040d201c0801640c4003214403600f04441543c82ca01585030b02c00d07060041885886c4130b00f09445070301001011038644600b0803821500300a01803108881500c080010b890184840c1420ba86a0a90319403a224124403403d5180c1e10342451038040307854521a03090014040d4003641c030f1660b00c0d0714001e012440221004944051004110641c07414194402035000e4030600441c1d21b08803402e2045e5040790006d070310804801841c0481030024146102590b500034108400a40c01d15041a00094032807481080a501d8195690700d0321881d0511050210b46505151000654400500048a002e04101c6813144003040084150b0b0000310030482c4018100c0b0702d00d030b4828403610b040ac07081200c140079510b2074205401c014489030f4801209442078041c64111122800d407003400140068030b280204255040700d0342d00d042030314019600c85c5c03e21250301900c2800f2803a543e6507a504c94500c100d94103e1980101242c801700e82d0b440d1085060480b111321801d032502126a80d83c0c00401c480703 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 724368075 1250 724366825 724366831
    0x1410020a0c0b04030c050f0a0203010b0d0f140a02220b190b0c0f03040f051201050405030a081e0103050313052b0c090905030415050a0c200414040c0b03 67
    0x508040081000720b5000c1c0e042d01e40251003403514003102c480b035881c0c0c030780341c652480c0c0c88403050340084040c00110f2409214014001d1400d0395044010350454540c0c0c0381c0400700c0c0d50041c00200d0581291194040248620882c4981c010402900c500060b000700d40080b11f2496011035141c0b40c40b0224601e441d000140c501110740813000a5065404d14407035080e203404c04282d11481e1312485036501400b00c03090000d0005441c0e2810110b070480d01d0b16081000c440140d50181003240d2500d000d02c004100044100e450307290540c24920300d10b44030307154041d00409090403000340c16805240003000304007000c001400f920f804901030441282e00d170010030000e07c0603031034060303201c017600611031056620107005500028051215042d4490382c400d045001d580100c6011986901700150500c0086541d0301d9529415901e840c0030703410000d111001a01c4041d1000c0040c04080424030010050200c9103801c448600f4060802e00100c400d000100440c1c1000765005c0f240c1c00400040810195800d100b42e0b48 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 724369325 1250 724368075 724368077
    0x10206090d050a053618011505070b0702010e100b01120f0b0a060e030607050405210f1006080c010503100e09030d020712111b01050c0106121410020a 66
    0x9620745941410380745640300c45401c0c828004140100e846203100b00d000c8140c140602040c49100e6500303412030301e1080d0210b24900703202d140c2e0311102000381c41e4079820950550b00c1c00300c06841c400b4440003003a030700c03405546402481c4aa10702c0070030000c00d9040d0010f00135172080c1d031708841031950180950410307a04d5030800d0b0340c0003d80000001000031419040004200004140000c0610401c400314a41c117a15070481d0001c00c1d9a00f20032a1241010000213900811616200e405d26042c140020031041006500c139100000030350351039011035818024815448401812075140c114025100000b4001303500c03a0800c0d90041504541281d4007500c03c80e0301c102e0001d40302c0c07510f0f5030a1624079120722501800d40440b501c0244030444600d15284004c040d80740c000d144a03a150041d050005051501400c001015600a24441100030b6130540b2a020044400d00b040c680315400320210b13500500b5907612034082a21084e002c0e200344040c0c0140040300506107025a40d007140d40310710321000c1e4071030040e100c0 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 724370575 1250 724369325 724369333
    0x30f030901170604061a0307021203010e04060f0e07060306031b030b0c0708070b011d1b030a0b0d0f0c0501091d040807030314010905100806010b030403080618130b010501020609 78
    0x1e00b5848100b0100d03a1050005100081854a4008183c031818000410780707881440041072102044d0104070042c1c401c0f881c00000c80c999070601e010140881c10241004249588807802d46610395481d0300051a00880001242c1c2c24540d40d05000b800f510b26840282e420b444016000c1070041190380d8600256a0010b18100494403410312000da01d611690b020303540b6080a00105001512014107a402882c1c00c945600c400c185604c0704010401c40a0304180c44141c170450345002014662061700da22404002001640c0310310100410402d4608510081c01048550b00d54020045803d0804050701c400b80e80303900c5025207480c01003800032055501c1f200d80c600a00000750000340300700001c01490b480392030b02145069070391a15407101103082c0c029400c00ba0320b2f0000c000030140380000100040151000400007035151101c01c4040d4400074101600300181c150002d00c00d500c0311135424072080d8035099600140e1603c241c40c4008a036002e041183c00301219400043c0303545c800a500e41c000d01944000d0 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 724371825 1250 724370575 724370597
    0x270c09040b04020114070303140106050a080f0c0705100207170a02072c070f020f03040609052704030c15050433020d0f052809020301090f060b030f030901 68
    0x10800000c0c1c010000c034100044e100e0850b01e08802d0070003030034103944251404580c0e0013604882c4d11402405030442010080c081c440000d40e60b0780081e426400c00e010503811a41e988845190206038480d28a02502c076120b0803000d0b000383c030466401080580d000c0c0c882151034070b5040c180c1c0442c501ca0300000000503484607209012134040316895094034a0221a40c0c0001c0360b100a5250001d041206c181021604c1c1800240f110b940500090740f180301d41c48040c500d400c0c1010409001d04c0c0f010b02809024544466400904413a03841038108400c03035031024100c00d49402e10300103100340034050003103c00346050740c001008858076000c1c55010341e9115180c0d2481c0d83c0c000040301600107650100380945603446a80c0300503444144001d0100e904184804601c107403500014605541c0d01401c02101c101c0c4c840b000c07030b010344840c044007101c003100c220300420440a54000280506149175000d4062450315854104000490740014001c2800b50186e4007140d141c0039449440c7d008542a0301d000c50906442 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 724373075 1250 724371825 724371833
    0xc0e010f031203090f050627030f03090a0807150b040b0d03080702010921080f0c0f0a0509061602040c0306060509040b120618061f1505070605270c0904 67
    0x103200c1c450111864006004c41442d1500ca0700c0c10100072013603d0b107800a10a02c440c000d0100565904d00c2440100071040025100341c480daa403003241680a080d00021010408140090103440384080d04212950344170b00e0b9034107003100020007440c1c19449852904c2c01c80005c1c1d040c00d0040444000e0001c181040100c102d0703c0540315142c0003007e40c03007103568841d6100001941d40214264a000441c210a90814000405090644040c2680071402510400c000302d915203002103070088402030540503100c0c41c0b040406e50300c40c014522950390000d0081140c00e0b0402c88076220004c00780c02198103201146d420703001a01150310750302035140042e40802c941022410305030031007101c250001c1d0800c07105152810030a4100700c01078513821301140014043c4e841d56141000201c3d080110b00d00c01c240310000102088208118038440c3d001d17148480c0801808880c0200c05803080c2c25080581444240307072080166103c01c100e00412001030180313401500c03140c1e50025030100000c4003d01102c0c2240c0759925 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 724374325 1250 724373075 724373093
    0x1b040504020a030f0905030c1002161b0b040801020a09140307090b06070b153a080405031902040c020304030b06040506150c031201052d03160e040c0e010f03 69
    0x42d15010b00d500d907402400300341c020344159814140950b01864507900b11110b1103081070b148012008003036006001161180c050b51002500031640018a02c1c1490a081000034040003940e00c01500a000440d00040010781034000f4803003c4556510012074036240c000702052410510015078166019002c244030100c42a4003114002c04010903080c10301c0c00582c0c0d100c8406400300c030800300030039031501d240c01d2074184502d015a41814000207100c130325080c040344004583c24002c0125403181003c41e03100c244020030301103c02404001d8241c076210700c43e21401440d401110903049000380d180441e00100c051010040d034083d241e0002c0707000000d4a503481040301421000d880306500242010b4103d0101c610301004000350f01d1880701440d2500c1c80380e0100145a01c050303006901441e958490100299140e175031810441c1982060719200d0100c003404030b4600210740080388041014514045012961100381610803803241007210300d00e6440b52051110400280703e40c100c101107038a42400000c034402 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 724375575 1250 724374325 724374337
    0x60f0105060a02060f0c0d020a0c0209060307051f0c140313080106060903060e03091809061e0c0706110301060201021210120236040308060411040519090903030b091b04050402 77
    0xb1080c28140144c0981c44000c036270002c04208082420543d5860071401c0c08102103a000300114042c00d8464038060110b403181400d94212040c160000e0001400c01d4014034601c922250010010b104c5001691070440d80c1c0d906c5400b03000c040c0000c010f4001281c4405008800a403941595100e150500e5503494001405020180d040ca81c0818445080162604201081c1c8400000d8a9502504081a40f142001d0001e010204418018001805201e030308006107178121840020a40c1e464841e820404000c1c503181e9524030382428008000110240e054000d410410305c03003000303400f16445010592200d00d0032441005801ca01200701c1001520307091740642203049003c42140c858070008480000b680411007160701c1c2c8486103505000030b0503485440254880c0c1c0540e0104480c0014045a13251401248122407246100a00807001c0386c2104280c0801054450024012072416140c043c01410360049803038002c4200d41c0004200c8020f0040300400d0130702e1096030f41d180c14107180c14840a98004 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 724376825 1250 724375575 724375591
    0x1e09060103020a0501051c0510240f11030c0a080d0b010c1101141201030807060f15030b06010c020603190b010c0b0a33060f18090b01030b03030c060f0105060a02060f 73
    0x7c3c030034050840709402107a00c588980c3c045406554203290541000406501840540d50307407624500380e103a9084841580c054102c0c1c00e064003841c0e0040c18151462284c1c80c00d0a07800d0040e0b00d0660304011903000035003000c4400e20001e21802002c5401100c08501d0608042e0103241c405507100b0700c0794007414140004202c84842c40f071601e0081c82107540c280c03501383e00c01ca07186840080d0000c2402200d1003030071040321a40b4418030042d0134409101c0c3c02c09100e030001514a230480c00100b8500ea0240a41140c03203a070180100b81c4a18150080300d105030410078201c2c01c0c2c81c0c2000e10303086041d0300c5000341c41c850640c8a90032201c591652104e150041c00c420751042910400d02e09075904d0a803941c0315841080741142402c451080c20080c0c000c010000f88001c2400380021401103072000400e0700c01c103105035000c45400041580110700100c0c040c080225006405010000b00c00c41c80348070208031644990342ca041130b200140da0310401e0210a200f05001100181c001e000841e4a12a174580f45035040410 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 724378075 1250 724376825 724376857
    0x9090b0a02070c0f120203011109010806040e010213030b19091e1b150306060302032e090213030309050d1e110405090c1f0806060a03141e09060103020a050105 70
    0x441813009070700d4102c0c1d0450035811a090b800b100461409000d0240300e81c4d122540507090452180001e800740c0700241c1181d02c16030310303814400889002507050350301d60008510b10800e280d5684c104000c44040a540c180190800e1880d0303050100820702806e402c4541c0203110a8071400a1a03c046214102100c11100c01c00558280c00a44501c2140d070005041e400000c4141e014500c2c50103403c954559222200b414014000c110b84842c1d40402c5600c00c0c02d4a6140040321041d0340c035505010100794204861a620201e009036040c0306000c00c24050300d200703803604003120b6140e5040001a0f166001c00400a20400504c17281c50b4048440784541b03280301d4003c0210080c601e0300082c043e200c1c01c4465103010342c03068000c40c41e2407821000c000740c04400c400c41034024043c080f0000b0004540107114038012400002d0340f064442c0b003980080b40e101d61211103110b00b8100720170409d00036612000c1c4032050040000c0482e01d801c2000c59030034100e90340100105112840e20340195043d8000030300848070894 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 724379325 1250 724378075 724378079
    0x1205030d05010902030a05160801060c11060c0708070b0915070f0212030d1515051c1401050405061f2709050f1303090915080f1609090b0a02070c 64
    0x200d90140c18060000c0b21409616441c05000710021500020603000850449001d101105500102e2041c1956040c1c80c020103000100e040c502140070700c140d0306c20307000540000c030750b6015400071070090140c0322090300761040d1654801c81a841406201807241d4050b03194404400058015001084168481e10000341c0135003050300040c0c410349120806da4a10382001891080020301c61107009030030410314000714400c0c0c0c14982c403081000255445a8280000040c04101c2401810005c0248001142c3c00344640e0403c00041c1c104258203110f1140034900f80383c00318102c2c0c58110149000442c181d8584c0c080d04c5000e40003182c0c0318a41580d0728004500910744005c000d43da80c101d01018200280000c00c42c2d061501e404a600302d0010310100341000303000740c0c4000090b404640c09003110b10031880820602e50340c11460110b20855031203420940701d483c841c44210600418001d6003549034080d500811070740d40e401074055507103a00d80204821100ea0010711a444581e01074003019000e43c0305468115 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 724380575 1250 724379325 724379347
    0x100e071d1c06051f050307080a021908030d0f0b100203070605060a0b0705070510031104030303111315351f06091a0a200a061104030204060b070c120503 67
    0x4405481c1c0c0310354010b4010110100300104c100d0400180002e0300100482c2d4a070000d0103441c1c0c0c2d054080284201040006014440c0c45084c50700007604810040c0c0b50b50341c080409e100004c2c1081c00c40c0005860901c2100c0307810b4a80104040c661000d1074025601d00307091940c5101c01080001c01440d8855040103001c984150340501038500307648900020f219007810503003000544c850403d0301c14200b40c1861803555125a40c1403c0e5000c0300d616090100300328144810f00c6001e40901c0d2490007449101c0c0c1c500140c5c0c1a001c0c41125800769080d1160140541041d618000408078502c0800b0f18624071000c900c03490706c1c136518140d4442c130802ca0050401e800d80882051075030392980204006a5141028490b030107124950b60070a44420441070300e06810000003401500c20000210f0186900c0f21340c40369445c8040c1305008000364000001c200311b003190b5601c400a5045030201782d00440c50700c440800c0c0320366031400300c0c0c2c0c6180e00049081a414501501c0c6451062099001c481c180024000d050b0a1 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 724381825 1250 724380575 724380581
    0x40c02010e0d270b040512031603030f05061203030c0f0405061b060a06031703090c040c02250b0322050102070308041a19050702030403020306100e071d1c06 69
    0x380712039a030303842c000c0d031001d444040d62104a5500c201034019030440400a619280e0111401c4844c1a900401e00c07480507c8030030b085000c2c1d0560b83d1420081040303608101981648481400c04880b00104655296002030020450b0500e0007030ac410b900070000300342d502c10340901030010603000b190214035190312407002c9031340c0c0c2c2c00c02081400a03000d0301e00c00c00d40903c800d02c8a103512040020081081074610703202e1003040b05a40c0503c0802100c00004241900000e00103020011005401031000d850014002982c0d84448029403000e00502c030010390702c44d06480741100803641c480151a0554413810440b6101d8246000100e001c04001c03203041c4005003080c0017400045001303445000d01481c01c0d04014101002d20100343c11540e00303040c1046469003205600e540002031214001920341c0d16a4410b9141d44115000a0340c141f00d040204540f03400920410016070b812000c844000c0d45488205840f1010030b161904000c448804082c0360b0b5013402420f080d00c500d04d440c035a41030003000361522022 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 724383075 1250 724381825 724381843
    0x3070b130303020d0513091109061303050601080c0a0e130209040c09150e070e0f0a0b18090106080103080a021e01050612030301050d1407051c0c0503011a040c02010e 73
    0x603010104a0400a150301440f04280c102064201a454a650320f80b1682d00e03076010b8066210400d644460080b440c40050f0191b814240006e0041e41c1c0d03601200c0b104c0b0f00c2a07412444200c0b070741d1244030004950f01d0700100380c46010240241c4502080c60800880801c1e148000b03200c5003042d240682010007594804500f240a2402540c882c10703054241110300041e41c0c2c41401d0650001d5118504000d420340080402d0b0b400a00d0f172400310006a41c0c50300185c010281d030145168000c030741100c04207404030090000c024004424a000d81c03050006001c4c001c1c000000d20400300401d00302001000821000002407070b00303078454810707108845c04d07803403440690003c40c4100c039074240c0d5544100f218600f0a03c60404119201d04020f505640c5001d001031170404030010b008280c250340803540d104a1108004500180c000245940c01e18030f65220543d0103002c100d041a602c00c9043d04001a01d420188201d506503c4020500c48441b4521001d0101604824485204540d07840d104505141000d101e1011 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 724384325 1250 724383075 724383097
    0x60909040f0f081b030f0f1803010f060e10081906110a0c0b07022805011d06060a0b03160503090c030601170f0708031b0a0516180219050903070b 64
    0x245036030284c424800c000140001800d56a801004080d10070300b54103050741c06982200c2c140d03d646000b85010701041459148a954140d070810404402c121020741010094403055184442299603586120540c6002072280c0324498114496210107120032040285025025a9001c541c17100070780e188800c01d0b07000304541c400041c50000c01100300036141b1142d6411001910007040031005400d41d1102e546000415201060180690b0a0400400303402100743c000c80000007186092541042c95212201140c0051042c1c1085c0030204501e20407400b520302603001e002d0051580c0c1c49503d03050b60f0603807018100707212510660084211a50301040003d001c0c0002a5682c0704900d812204a840d1646141001c11150040b0400b071083c02d00c0003082e20100c601e80003204035032241c0d910b0300d0350800b030f5a648050110300541d40400c0400025541702d00464880d01f50240d0b20b944581070000490050038035400c1000407104c2c2504640d48a10090503c4e22001410365400683d00e0700d2011065200400c141 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 724385575 1250 724384325 724384327
    0x405060f07240c170106030b03070306020f0a0807171609030b0709080c0409030804080304060e100510230118080f0c030f0c01021f060f06030227060909040f0f08 71
    0x2002c00c0c0b14a000310703451078a803820080740d210215005800d8000f014001c40b000c05a9030101000c4c01d0360200a180002c6400c01400c65894180c03888150190f032022040c4c0c0301281656000c904510710a00c034251000b15440c0031801030340c0f11020f000800d40c031045280010040d00701c07804804111301500d110f00420880d11400c401c0c0d4940524141020800381c1c00521580c6041c40300b001207074100c00043e5010742d04c000f41c2940ca0f035503031030f05000411020205c1e4000c0d00ca496045441c1ca6095807203140100c02041d0640005990341c801d418001d80344210000c01c160b05001d43d0f04541d4040d0514074004200030888058041c1c4618110b0316204038030404884030b90001a01e50b03020b0806000541034005154054090340183c800082d69a11040200d1040d0200d44a0440080078040d8440350240180c01d400724100b035561080103019400c0a01212204c07980000011007000c0c8110140c0f5081c000604440d0403c4644020001d01d040014010340d01c030103503251601e000400d20810780d900c591041e4920b03 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 724386825 1250 724385575 724385633
    0x1060e06212a040504051801090b04030e04021c0b01110105090a1703011505220e0105010215011a0d02070f1b08030304050309280e0a0e0604080405060f07 68
    0x100a10740c000700791198807034006480b1402074030111080320207549059402083c07580300c0600d8110360a14507a103032180b5501e0102860200505a42c100380030381d00070303524403017240f1682c401c1104034420007504151901c5541d10440780d41c5116009451004014101401c610011805150a640c412200c480340d541140088070200003070171101c22040360440c48824103541c1030070304e8083c036203284020100c140040402e00d07540050302400e2400080d001c40200c6601141e85440b0010104001e020351400350103028521000360340a50503040c100d4901144280500075008240e810b2030f403240c03400c240415020000c810104030303010401074503a4400c0707506e0300700c0c61b103c19a10a620101d640000400360000c1003480b001c9103002042d50307030045086408000c407031300d850520221920401c500d000300943e603d00c0003a0700c05010760414400d0f030891405011008480240c1525500c04136070090a0400c280301c180a00e0a00b000034001c002040c0b12107510b06056521001421040314802c2c0804000080503 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 724388075 1250 724386825 724386841
    0x1603111f020c03190203060a092f090c120402090c271804050c153a0b030a0b0705040b0712140715090201030b120109020a08030f0301060e0621 63
    0x22070340050030a908501c03030203031a50000e51140c001902301d00000d81c642c1116028000480304140c44c44000010b01d05000c0c44a02c00d2030644400c0050142c815910311000444d84540503040300e034003420001e900703026690b0301c0d800c00000910241c56116505d8084c851008502031014003507030b0034000300a05880c101c005030b040181c3c10010b81040c00d0030054500034000040c03800100703156610000c07280ca9101c00c03c4000000c9003030080400400d10070134613050f5007240e031550065440c0e06405104110b0b00302c070a1160000103a03880c140100341c040d1b22030340302040400d20f00c180c0503030400075600e130444c500759a44003074008030f4002c00400e581c3c1c003126071700c1800d00c0c0742c00c118502d041000d80c1a20f40d0420b0250f41b50100d020300003030303681201c45031107003022402c40e8481e51081360113030b500400c85800e51462081c0c040c000c08003c0350880c00342e01c12030008a52003000000351035410040703500180c40c42c0e080800444240c1405601d50b0b403c00c10038046401d010480e60030320101d45580300c04605003407500e950 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 724389325 1250 724388075 724388083
    0x18010c080610020706140d020702040507030b0406091a0108130b0c1b0c060901030b0d050106060903050c09010302030a02061608030103030f170403022e05010e090d021603111f020c03 80
    0x1d500c043d50311102e010800300307800c1a2081458800ea40c0d41903124492800303102e020340308142c4021342c01440d0100300092250190b01c030489500e81a1801c000c3e10740c481c420b96040792400448800c01e203840c01444100d541c0305909166008040303810007100c202c2641e9840038500b2040d075040785501004903410701d04200b0030f000007441d01240c0300144030310028080070500302d02c5170304e01460405441e01510134060311425000760980b54020020040c40b070b901e6000034240b0410740800c4540780a08249803a0900e083c210090617281c008001d40300010059007007001030303884034085007020240e01c0400340202d611030003c0d42c02036009445550620582c040014180000c02c100e06907200700b0401408040307a80092a450724070700e00e482c100144141460000c0400b1091021484010305050000c42e25803101c0e2074050003404844100c6201003520501aa12100c84c030000309100345040c10208003062195800035038801e00540808600310b4244410401210000c00c10009603000d07150003131f101c3c02c0c200 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 724390575 1250 724389325 724389349
    0xa0f020403061523100f031515020f03091c240207030f020f0c2209060903080f01031505190e06040209010b040303080c030720010603020f0d08090918010c0806 70
    0x103d8500b0f19081031300006070381d03005600728090401080590541c1014007903405a840c0200624500d0840b59031801b40c2c0007420310b06c000c4080140201d10825800640c004162114118001d0010b80800500111120086100c0300c0c01c0d00c0706d10680ca2462601440c1d25001ca030707010307501a000f599032075450601420b07589141e01c03c04119402440d2220a0203c0480c1c80c0300c41d83c8040741e41d21914a0400030108905c0c60b00c2d0801880186031030411410001c07640d115042040c800d8a03520229521035a12002c4000c0900c4080c040100721110542c580c840e99100f5944101c3c0b070903d2a490500951507031f01111034010741451079038004814001940791042d00c0500520014229916050669074000e0070106c001c0e126030811140400481c400324000c00c0380803000c40c01400b4013a401c4103c02502800380c800c0780b205034003038403440d100412542030003403d011081c0d0700170b50800e00d0800e040042c0150108010111703000e0304800c2c80018079801081c081d210302c840140d5241107841c1020b07000c00c425000c401c = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 724391825 1250 724390575 724390619
    0x80f09180c090f04291807080a0c1713050708030901020d0509030a0b0c1e160201050a03061802040602010501050d0b0106140c011d0d0e090a0f0204030615 68
    0x9204101c046184001214001c0609075112102810342001060203008004200410001c0c0c5140b112001c0b080f01d503000b940c4040c2241ca801c08601400082c01c0c1d4a0400e403240b00c0002c0203c000180041001d4220664070b405c00d161110900c48807140e001c001000a503440780300d00d14000001c1c030500400f00240b07409810b048002d14908504c0700300103035540d00b154101405010020a98101e02d94051103201c420f181c2000180c81c4d61314051603042c85940c0034183c0089150f21072072000402080074000e4071802e9242e900040407011607900191100c3d001451610304140c2c407810081214900c0e2108103511400201015844601b00304010f425034005030861400388a14155060205030b1084105044a10350b0914042d08400138040d20483d01c15414082169030a203144e42203d000790b10804500200100b007a582c001e00c814004592500100c0d25917540030480101007500307603142c2e038031010340c4107203aa000520301940ca42c0e0b41415203a021203900d600421240b41003203109210200c1d85508a40 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 724393075 1250 724391825 724391869
    0x140f0c0d080c160203030409060303050c060a050606040302150d151403010b06030c03070c171902160e09010e0a05010902040605090121020409080c0c010f180509040609080f09 77
    0xc00700e03035900b00c0e024098050341c25403c288508410b6403001e0046601625444400348003090303d9007006405039005424444086c0704410015940e0415403050f01d0103008002d21a81c41c02e4610f4080100c4408248180c498407c010000f00c0d040260600c680070540042c510361a1200d481d055a43c10500a01480349001c0d0b41880441146a9990070480350301c8409500080d17265112400101da105c4625000249043d04003402024841b0040380980080a4140c0103596503c001003012a101c0c0e04032074002c040e20060060503c600c800820211761f000046000000f450038400421601d4072102c1c000548030303650f42da82c0210550416020307010203804141d5060711f207035141c01d81180c0081e030403042c5040740b0030030061200115503c039000040c3d425040b11043d503c815440030880d885042030381c00c01d40402d9081d64a01c100c18020721280b0340e485800c004000342d1626040903c404010014000c80d60030b42c3d41c0c0d80e24000030b510640542800b60410103255200d100e06800c1c00802a111542161003202c = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 724394325 1250 724393075 724393081
    0x82b0c020312010315110a03020403021306060f20070603090c06020105060a0e09030d050412111b0405041406041407050a150c0204090c06170a2703140f0c0d08 70
    0x1000091030440b940a1070001170042c0941c01e510050049606105c2c2804001a0140340c00398150090404d0304d0003102c0001c00140c205642208964141c45420b021401c00809110000d002e00c95054002203d900060042c034400c1980c0c7d0304100540d0004030100350795000381018001a0b00e0600007804c042d00081149061113400200541842e1084001c811841d00c0041c103103060a01c2500d680a26160083c002400c15140c403c21400590142d5000238000151390300303001c01e00140055040000d4a40d4600c0c0403032001c144005041c00800a45040d01180030385000c41104100c0b55204038060352022010391400e154990600032140d2040713104640d004018080c030581c0301d0154030862080e05050850b0462032011030701070601a84040c1801045000004801e6003150003141c140300c2c2c40745480c54694032140d40204407810281c8070b810004d200601c240b501c01000d444a803905020b0b00341010a65400400c5ca02c080c3e121352100a9a103070f0208080013041d07000c000d00025035555060241c1c3d586 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 724395575 1250 724394325 724394347
    0x10e19061509210b07020f0303150f09010b04090908041809020a08030c0d030c03152907051c11160e01080318010e0406090e03040f052b082b0c0203 65
    0x4428104013a210b03c030f040c804148114002c2000f501c080302018141c035140e10781641c1c41c04a050392084840d0098818503c011041d24182100b581607560031176600307041a040a02040003007000035011500b4881c00c210108a41401244040642800c5400442ea040440c07045c02a01c0d9515404001d05a10078002e01d00c41960201e8210004172041c0340018204545d03580403405031400e842c82e0002c4040001011400d40a54400001002954440b512515000d500034100f548207011014140e40c00524070f04a840b071503400d01541c0071a082c80c00c0440d10007402101800e0200300c568115800c0c01c5240b01300855010031150711300405141001e18100a462091592144010400c550401842a04000a5035903503480b10000c4e1410807002c102107003007550300c56a80e03445401010300780c1d03124500001d046e10f48003813101e00d0488104018050380300e070000c0021120202c0f034011280704000344210640101c84802d91441e8442010001344c035001000740c61000c0fa440740e4404401c41d0001c00901c1101 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 724396825 1250 724395575 724395629
    0xc0509071403070c1e060507020d0509040b010203070b010e04050c09071d0a0b040b130803040b07060203070327021815060c100c020609070509040b010e19061509 71
    0x85106141d8a03549586040c0121400c1c1d00c5810300508401060007a0b0000911407403c0386205841540c00b000580c90301c030004d03651501f02040760000500c1c10000d40c100390601d074202080c0d006040c0102d9085c06003a40d135013240000d00360800448407500c54100700611000700101940c07000709403074400707660808801c02030100d40c08110300b103c246005001c0c0101501d40e00080401000c4407045580c581da1200440d85860748010902e040c0c0485040d00840e90060101c00c40d01100c6002c0c030260315000f0740daa15000030f50401412581410754444009006a030b81c2c40d01d2030105400303680034004001c542e104010703012581c0d880841c000014101001415041c290382c40010203811a0103a484422024000f03180c102002404069141046001c001c201e800140d03560284003400709944143c0c0c0c9074001d201c9000da088a0240c04000884010040540303020300d6581c0110300e8503034003014491410082d200381d0b48590b00226403140c4090f41d10007215070003581d15003c0d010b029881e9070f0a49400d5041c2c44a = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 724398075 1250 724396825 724396847
    0x270915130201090e100e09150906091c0c020d1a0a05102d060c020901080a15050903120c0d0f060311151303030807030e06090a0305090102030f0d090c050907 69
    0x201614010175407a0300d070340c00c0c010000d20100c282c482031864590303661515003c9204500740601002d00106048000c080350240c800c1d03401d203008010000108549098900449403104144140c05820501588036041a101c542c0d02621265060212010742610200e40081c01608a0380ca45001e2284040c004180d140484409545408140031031040c02c60f00074440604c440300811900740c00140070b98000b003c5000a40c000c403104071032a030340c1e41c0359240c8513600840010608216802842e10780c090079444682c00201a038110790421006940e01c0c015164141d554007140c0002046483c54098179010381c80c4203617074650092243d54a181d80d00e03c180c480d40c0300d03440e1142640c3c8502549884e05081a80c0000b01003100c080d66090383e900b0054511403040d10120000380c20300c04580328648000500301d000700d076010000d1030400f28680741101c194000d405403d045010401901581400c80d1000d4203030b07200803031000100c00b1824941240304030101e0344407600403aa6034040207005038020201c550 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 724399325 1250 724398075 724398089
    0x11120d051c05010e01051c0f2003030307030b031b061206010c080d0606120507082806080c030d0201090201050a050c010609060e04020f01030506060927091513020109 73
    0x9100c482000308810030380c00304488940a41e1402e000020000c0702214014100c43e802c0c1c40008180c45517144940110b05034140291807120000c2210000401d1a44407100c4001000e0310780381c40c4c04c9400006030860388162600c00c0040d40320080d0440320f03e002d21461461303490641c503507040014003c5c08500b40340140c0c82000c00400c0500c0004200d0b90041a100308200d50199040f0b5803845d4408544008104074000c40001131010a2428040c804c41c0c0308460062a0a03242d102943c0d0300d0030200140c1c0102c410f0084c0b9011001e00c01302c02c03502018040d800151038914040c00c000002e4106041c03a0415180668045a040c68030350300150360084200c1c0e61155403460007517610155203007620b001d8280c81e8004034039145400c900041032289002003070f028520850381e40629104410044043c2c0f0f0382582c42d560b201408004d620070174503041c0e154240316801329003c54114003286580040c10041200c070840960800d41414045400001c3d4481d40047e003014804040ca043d900000c0101ca15402000 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 724400575 1250 724399325 724399327
    0x10510080a020904020f030f15150304020301090615060e060307050f071109040c031b0608010b310317040b030103023304050f090f15010c050601090911120d05 70
    0x80d0701d440d440c1c04440505074090020b550b82c422541c400d802e00c0c1e104682d84003640310703207202180654500300300ba04003440c002080d0400c000d4414144c11115807014200b00c0c0e241d9a0780004c0300c0001c52501a201941e03031130140c0b640b440c03480d09030058400040d8041451041000300104240e90360403405072204000b0b6542e080b5210001458450500e820003000b81d94403501c078104100800607100b0b42c80c070130342c0d01c500005c1004650840042618038418000c501c040790644005008190451002e0300740855101e0300c084002c604080b0600300c841c03180d070f1161080f08180c00c3c180207000c0c40020a208000310080c58a19040c6820010b01480c001800001d214050b0023003507155242c07448405030b00c0542140c20741410140603292100d03e40d806849114021190101d14182034a04054590320600005025003d10342d0703420080100d8030714140c101d605002d070f224000300c0428010071170203010b8007078017000080401d424140380787d07808903600e0b000b03200b499032900710075448401145480360460709041035 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 724401825 1250 724400575 724400581
    0x140402090d0618060e0601090b0f0901150e0d20010c0f02010e04060902031501020c03150c0730030f05040807021509150403060506190e0a0f0f050f0c0301051008 71
    0x41004000c001d0f0001e4143c50070f10ba60910540c2010807880e04849030800b003082144500c005210400c5002d01201da8030a0078880100520040c903030f548104004c4034501601d8843c0c003117002407581861140e047e0f5040368210310640c982909030840d03103c107850900303107071a8001140c0e580719240d481021000b810050100c186000d21380303503904841c0c090b11003208195228505840c800010166105a050051054100510090402240700740514080d0540c0380301c207990312000c400c1160b114440c2103a1044418030780c440030008910f40000b80c2c28503207401c0300b05013001140c01004d4800c06400900ea20345001b0901c00040e02d0321040750402903058400c6544c07040704071407800050103061740c0580c00c0040d14a500d075110302450000e01c1a41e108010802540c2c9540041c0400c255401e416940c400303090107c1440007041104d103180c0d001c0324032100400c050080480c210b00b0741d08c000641a80d010748070018084441d0042c6c000691180021111600b190300d8400018500c628000d80c400c103100c440004 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 724403075 1250 724401825 724401851
    0x7090b101d101d060c0d031d010203010815010918030f02010f061d0c0a08062107030f060e0109030503160e0306070f0210090812090309120106140402090d06 69
    0xc12554a4000b441c2c07000e4100038070b201504400d03a00e000102e43d210001500051032500f403090b181100c0804004200c41000310070250000c00050f0b02040b4001c003818175100c805075090000307502910000d005030441c1c1070145d80608141c10107070401a41e16080110401c1c2c015444400032141581515140e200103034a068283d004010403501c0951040c100003022841004c462081c401500040c1c40083c165030728000c12002d1806049400c5c07001600810204146190a401030b1318410030311001d03640c0d214008054940360202a51003200e1444112581205007c018865800e0308162180240899080750750b00801c2c0748001040007090b400810781910013070340310b520004a4008081c0485400d400e1510300038100c0014809514014803a00742d08860303036002ea01070f4010803a84562610f0500c15103202108c86804010304500043c030040c400f5543c3c80e613841a108000c0350700500001941400c081040e01c5000c905011103004500421617030505803a12040c6c010714541014000500c2e52624103 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 724404325 1250 724403075 724403117
    0x50f07030e130c0f08010e0105060306031e07051c0b07030e03040b1b0d0c0c0b0a0e130c0f0e09010e06060906030705030f010501090b180105130603050907090b10 71
    0x440540001d00100c50100c40b0005500c01c1c50321038a01c1d210320801484991003224003c209004100e00c88148600402450426001554000a0040170b5500b0060161b8030250281c0352a60308100c1944411400c01c16424400508000105806d40300402a0303795121860958006000e90f41010f82e10040354580c11000d00941e405400810b90055407590152025809a107512030451900d005864281c0a0140074840c00310740d0f03503840740b03101d01a0b41c03a200c0b00b426142c0041900c64280241c101e00805240e460440318680400440d10006030b800240340010000c0c0c030b80c80d0580c4240881d400b0025180e80d1151301460445070b501a558450b503503042e002c61200c0c082e10300c400b60070600100c140078036540c12201a5115035505e070031540c041d0380e946004485a0b2218461140141f000700f0041c2110320680d804100e410106041061078450344e45241c00c9022203030783c00780001a50b90018000081424030412004005002084c0108150310f00040c15040e21030701408c017482200501d01044c800c1141d = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 724405575 1250 724404325 724404347
    0x30506190b0a03050a060e07030b0a0e030d1407081501020a060b0a03062f04031e050106260c03030f1903090b0f0a0c1107050d030507020406031b080d050f0703 70
    0xb0304804201d42e03881c5041542c410a00b40200d40d003d0500020404403100000c40508603504080e040d111521908108401040d2081c000202030104100782c41511502e801a0070008103000101400303403408100c0100b604101134107691044400303202060640c0e81c0080c02000b880d800c1400001c0e808107210000f100340507281e000404040c10440c91242086040d403001d241c0c1c94201440441c5101008030040c02031099020080c080340c1016011010540c02c0400605041c4c881c1c07000041c1c054845950304809111006440c8907542c11802c1c00c805075400703118100b9040307002d0303004606040030340c05000036070301601245440541d101d02c80302040038401e8000404040c0c11500c10003642c00c2040ca00d11401508660042c03004d824904000305407489140300070203003100b0001070080281410100700c3c44d075a00c9203054042060910880e405641c1c0d40c071036040214403400c100760341030300040c003030b4202da07030280e03020f66056080405840001030b0803404540482100b142903a80d43c42151034159a2207800b1 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 724406825 1250 724405575 724405579
    0xc030b0102070513091205040810051003030c060f050901021c0905030a03090503120a0b040e060f0c13050913030e0d0c140d120e03011104030203150c090607030f1701030506190b 78
    0x215811b080c8947c02c000144251a00901650748048072200d060050b03074425038102c10200b030044820400b2038492a540c4070f071036104103000300310200c00c00220001c0c1c90064030304040a9500050103078041a4003007860301006a0b051060000c43c9658a079180c4a0060360001014540c0700c403480c00030810300340103da4040c952243c0c0380d40c56051002c1c9000c010403004003a40d014501d030803890b00f580000007a10502c140741111b1300540550743c0420b030500d00e400104209034400d0b105100810580e9405290600c142c184580c110900c80c41424020044041d902845000d200569060304c04201507070445d02c15075442251986d000c0c10884003141d56852041400740c20008208010270031250300c80c13180510201e0481c003d021155145060808034410362200a506511007646018100300d80700d5582d034006a21074419041500e5400401d8050b440b40070304030300090440321141002c0782c000c03403144074040d9800d000c51620b44c10b540e6041d0362100081c1001410140c000c43c2080941007036004400e10840c0 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 724408075 1250 724406825 724406843
    0xb060d0b0f0d030c120e100c0c080a11040c090302012a02060d0e010b030115060809010605041407140310030f0212120d051e060d0c0e010303050405040c030b010207051309 75
    0x301d050003031941c0c006030000c9030814025170209083d41c2c03007000d50442400000303000ca4648a140f060613510104801000c03500d0a0a011380020104005e0011070f4030240283c03400380081c518682000201d07480583d5120070300c1900c440a00250764401e0364030100501d040791403e180480c1d20030300c14401c0a4031200070360100300001d1100505940b90495804465108c000b4007030100703928201426124009020042a68087c608109c030300d00c02c4600300e8001400c0000056040d85400c0418140e80c200303940e04031005d801d5424810655400600c1150b07481c15000d44c1421400d20b48900740c1210042e100103030101c16540b1011065503201e4a54000c507000c0700017114217801c01100c0030582e0303401c00750300284940d203045c00050140c4c031821200c441d800000880b107078142d03a40d60100003500c0c009040c241d4410307c0750300c0c0c00320308076880103811030103580207403103131a1100d02c1d0074100010344141640450803d03042c00ca50141598000a24206586046401c0ca00725441c01003100300034010540c02030401c0ca0 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 724409325 1250 724408075 724408099
    0xb0105090903130b120708190c17010305010c140a1d03030c011d010605010e030703171c1e020712030c0203121f0609060207090903050c1b130b060d0b0f 67
    0x70b002c00200f000c1240c2e00c0c924003075a99504807d881003881218003110322445041100e120311011380c040007440341282007803035518907540140c1e5105c1609800071100d580d91003124091441e0171068401404002e50a481d1a00003050340040500c080c0441c94040d483c0e17203070690350321a6414001e42c1c43c07010300355008005203889101d001d200202000c150820341d51a00c80c000c00c4031b5200c0c0304034421042023b00184241c1d89107940c0c0b20b0007071020b1038000c004070005001ca45c82c809100c000302000200102c902040b69400c4545015801c00c1d0021400c10191041141400003030840c400c0e80d06131046030800081c0300100744c9e42a415489100492004855102e0400c001844a0484003002ca50b0320011828403a88a000a0314541d009014040240c1d0080e101000f81c1103850b000b0680c2d00c4e11030b1071316a0601d401d5507880c520301a0442c0252105a0008114030041d0528101c0881070020b43d40d01440000400b1021400c0ca00c180408402155241d400c0107a55844400c0c0c800d04000d80604441c003152 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 724410575 1250 724409325 724409339
    0x1d0d080d150501020a110f0a150c0b0f06131e150f17060a0b060d06141005090d0f0204270b07030b01270305120702010212070b010509090313 62
    0x60040c030307841250408410041031030f500c006038080240e64820f814080080f041d0040080e802c00c1c0420035a4071546010022804030480031a107103101c4031a0b00d80d06200031785071a20a03140c0324014455001e40401c0d10400145540300c001c102020207001d1000541114401501015145a64001d414080c00c0001da40c2c00440c1a02d103200488955011606006446041040c650509840460907583c080000b1403c0492030790f000c42e4403524001c000500d00039668144500ba40c2007030303000d100c04040e500f040c566a801c02c10000488001103181c00c6280021480c000707108444480805030003d500080a00110344a60340712508110004003800c0204141c98103690380c100c20f840d42107071001c00210200d032030203003e401220a42c0c00c058480036400a210f040120208001c0c80c000e07940b070035280d9030000c00301e001440150310240e201c040e6150b41e01068000a4606a17000c4102e43c00124200843c801003541e6881043c107542e0111902c1c0240c0d24fc01c0100c51450140e890141d1151000b410001801 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 724411825 1250 724410575 724410581
    0x2307020a02011706010e10032a020607090303120b01020c03010207110114070506042004090c06140f0405120f0f060403140a0f140c06090303010504110a1d0d080d 71
    0x1500c01d07603a5140b410700c1d000b4011903a1a044d2043e50124002e131081900d1b903e0b0030120081286041d260000e0000b800d0301c464034850b01403004039001c90300107061210311650706025459000a450038413032000391540c0c1c1c0c010000e01038454801d170302d2980c036905110f8583c82441524a40f220080c02551a14640d003850b10394460b10100450200300708c41040111080b070001030b01d0403a50881c0c09400b45a843d9140c001400d880d80c0c1414900a11218201b101039031144114602d06025414880031142080f00c080c202c0303411001c101010303001c144101010903004400f100d09980003600c041808061544c0020f180c0440110b44107901d0081c00e081c5101c0110000300e09215500a41d60708070a05540805040c240c031030081004000707086000034111160151900c2c1d01c0f0152140000c91506401b010a182840300030307180b207074807504004010421864203000310100358248031550f5191012900025200c140000100d54a84030343c16645070055960080515134543c220050300d90300c1c1d0701f4050101c01 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 724413075 1250 724411825 724411843
    0x9020d05070f0e04030e0904080409021b12070f23031801030c030c020d0c0c0b0c01050a0b03030405011b0f140d11012d090f03050d0609050606030109230702 69
    0x140c422042e00c001508001c94072801e010f40c0e00350725403a624140000502051000007003041d50000c00801c4000340c0740b85c0e1403005212a8503508103c80ca0003001ca00b4045c01c0017400b0001c0000840d09106400104010201c00003515038410020404401424482d104d01c41719000a040c1030b0002148003c65020030102008250401766020404008010402d804a8164005100046c0d01c0900070060144c0145103d0003d123025030110801c4030303560420a810b95200481c01103141e51100e06100c0280c030360f401504a651000c8010711304041c00c10340004c1285c0020038804141ca400c1900c04028084400c034000b080c1500700490b0102d14000c4031a8665030104030000200090041c40d022140101c180b20b1402c860024908880e032149842e10801c3c021074140421020803507a62031721070b00060441c0c0740000701c0d921a8031034a07200c643c51002c0e01c0480c3d03026071010507590704202c2000000d03540c0310308076411741c4c1d03c0c0a000191040c0b04058400c0ba50581400c0460444064041c00341183d00000d04000c = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 724414325 1250 724413075 724413089
    0xc08150f0c03040b1504110d0b0112020702100503181c110f0601060c0512040303081009060b0405090c09100509100207050f0123040b12070201050f040605070309020d0507 75
    0x854841c800d0781c034800e00c0201d0300601582e180070049840f55002c1614a00100300081011a980ca5480c00703407020b42d070002100da011035a44180340801560044034a440a440c0385c5001c504100c03603900411a0312162a21000402400200042c0c505201404408002c4040404c0300c80807141c5001c400a410b0a20301058003041c6880d11850750840002800c3c0d02007800302e00079046030303403819030184c52940c44400d04030307020701500c191211101c0076603014200441c0a590740c4c039502e083c0800c0c8213801400d2a04100d2007241003401c18440c00741c0310011030b01110f10541e801c8851f41d9820300016490700903c2c400302e5000004106910703065600401401d05407034100c5010451045c541410fa0365849944503854101100c03140d031500542c0503924409483c0200c0700710a650002c0e848825440d507115800c180300904003c909907002500000030950320041d0780c002003100d0706080c1d901c4842d00302c0080c17008000c251501d0020303159500c42d42004030241d5014103044c6008956140168891a40c2d0143d10 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 724415575 1250 724414325 724414351
    0x705191a010b031003031d09040b340e060d050f0601020c040216151b020a03021c020a060902040e010e03250b070c1707060b090108010c090b070c0815 66
    0x12070b40401c90300840740074810b140f0b60352080f40e00d0342e501502d010001e2914101002028a21080d603501c5988550348164407070a001004d5140070901052003011603007800c12407101c0043c0b15808660951145407843c2401d050101c0503480030f1001074024800c1082c4006d66a09000c03e1009444010f565280a0f6100340c00b030300c01d6440004c00388812402800304004d1421803194102000c6014543d220702209641c107008079025500e07001400c0e1a00f18002e001005a02c600040e200789981444804042854181032803003c00c02001d000b980c40812070f0000c0c044565a070404011582da90f440003184402d008001d21a0042c7c0a0307920f80c80b170b044500758501c0500807100030740400c6540f800341000ea641c40380c55041252100345084030794038030351032007194001c0341500c0c2e5852039013490015080140c410710b0302091641d0a50240004e448041e4080c0b0303060781c1000103014440e074005d0400c506890f4042d400b642c80c0c070568101a5220f03905603208030824000d441a240010010f04061032080c40c0081e149 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 724416825 1250 724415575 724415579
    0x308070b1503100203180d0c2a0605160512071a060303070f1407030b041a0108250e180d0f02061303030e0609030c010c230705191a01 59
    0x104045810740d60382c035401581010b590b050140e4095500301000e001801603060b050705843c0e2400c61060b4160300800d142d020844104a0030406840b5098050501d00ba4002e41001001039511042e004050a200380840c0300401800500954020a40c002040350206801250248244d5100700b4050354101c600c0201c2c60101682d10314650301826000c0c0c000d629041c499210003541805501040341d4000c10703054800c1c2d506c41c0c00c01c0302201030341c05106004910b052614118002043ca103400300c0140d00e4010042210307120200756100c010190207409080d00c5810750088025156039041040265010f6042c028040003481d0040b10a104400880d2401c14982c3c00a40710b605140c218103006920810024100202c03d500081c1312070310908021035184e01058000f0700304241101c0d5000c0c1c035800802c440303006020901030b6030814032082c01d1041740c0400c200180200b040107841c0311100d604000500720704001c0c0810030b138104030713200c2541103450320b21524160150f088101140210f010440b400 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 724418075 1250 724416825 724416841
    0x190807020d02031305060f0d090c09180b0411040f02040b03060103060501181809081206030705120a0602030903130b070b0a18060b0a1203170c0a0207030809040f060308070b 76
    0xc440003901c113074214840c43c40c07810b010460294844800020511400d0200880e0074109014600b500c520484646c01028142000c0000301e9164000a95001e03a240e8401e502150140c44410340042c0c0003640c8003500c0d5024004070380940b91120300021020710006000455034501e030051401307040240c1e0240412940c5000440d030703416010110703566044602d0700400043d600210705411814146d02e0200351008940ca407160103030815468a14dc24a400c0100301c09454180041806002d0441e3381c60208450700381c20654584050100500e15580040880c5000c01e00700252481c4144481030300c200c9a40b00c407610111038007c18000c4400e07036a00f00129803c0c2255018a00b6420700c1042d651541c810141c0342d8001804410207000e412003500c800101d0840d03140d200c116400f81c000c1e21080c4142c840107683c038222160013020150030301c4042c071041000a41c0410310004480d0030a0440361a0500e03140090000c081e0341d030400400920f03000d000010022a00f01803c038a0b401409103204643e14100 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 724419325 1250 724418075 724418077
    0x1c0b0901170601140109031e110316120c080a0507030c091b0f11010204060e0a0905041101121103040b0403030c0c032a020a080109021e0d0314190807020d0203 70
    0x2504501d900000d0050101085000c0000041c2c841450f20440b060390343d446080d40400d65400d40c8600d0140c1e040aa82800003122140440307040a40081800c20800d042090013802e481c010400500c001f280410280b246079840080609400c1c829a5061802460010341e1107926200c22110100341c2600010740b210617204454104041c8010060f001e00318000440700c24049850600902040325044812290244090800f83c41c1913140d400c40c40071600c0401401d10300320342c0500c1710303581810304220008041440c101c160700020b003041d2118682c541626005042350100c891300450021080100307020141031140d0095000740c03410007c0d0001000c084441407000b81010b0082103600701510308042e24102000c20381d2004540318042c0b06010386c00510700130010780c007030341c000e82d12641e1510075403070300c020101c090440582c2a0988410070002103612441d101c50082d091040d881015212401d5002c1241c2110011180058004000340c06c0981005410f03540040144208400700c1c40f2280004 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 724420575 1250 724419325 724419359
    0x30c0a03081c0e240f0f04030c060f0e100605120a060209120a150c0e0108010b0c12070c06030605100e040f0f18060b03120d0b010309080c030a02100204030b060904081c0b0901 77
    0x846c4e00c6400d9940e0744040e5414000e00707600b1140c0c40d6aa000c3d080030350030a4800c80c140700038041c0c00380007010302d903030034220603200c6a0308041c1c800c41e0320030700d26210094000f4081c00000d901c00405a111107809000030400d111040194109008900c4800d04128824903054801d1541040402038120b44100440b009c0200e00c41301400700c0c048400500542c4400006015018804d03030031907900c814103d94400b02d6070401c07603044400380038000091000c203815004183c080e00c02a03442500c501420f00005003410001400746020781d642e80d960304001da0305508880328030311340340009002e081c581c2e60b1080105400c50400303a49040c98145400c01920380821588811f20103d1603003420310700100707414002005082d030341a05240d59041e8400003d6400405400041005000741d5195103079160081c1c2800404a01d0f02c40144c030421051001444e060105074101074141d422546665a0385002e0105206041c143c1c4011444407684041c00d0301c09404ca04480e04c1d0643d00129140d0742c4000b440c49441041c = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 724421825 1250 724420575 724420591
    0xc08100e040605090c0a0f090c0f05030c0c192405011802031f1211030a0f0809190f14040905030322080a0905030c0a03081c0e240f 58
    0x103808500880d0341a00310b140c00a050400759411030040f4000a05900300305d5000300c18001171404200314207a06c034820883d00240c24108529562882100186070784030003007034003410190100300614103000400440c80c01264840010881c407086080401008100305202c1c3d00e80100751041800c00c5149000e41c504a03001a450b14207a0103100307100e48060f4000030245481e070b0b001c0c51286a0851014003c4200510300030440400007011410000040206528410302a40c4800c000303078001244115500c41d4543c210f0b0751140c03246070f4007000900c0d40d06900243d45042025420104115080300344841c203c501e6616540010b6401c1d500b0b00c0299040400c01803d00d400a000082c0040440c541092001c2140400346451102c107544100c03564206900d500001801804148440e040801c46511455811600e040c4070324956500c4005510607148001c180955112180c500161550030450a040304003051b40c00b40b1840c2103416103002102c00c0000341d892128800300d010b040601c03000500401103 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 724423075 1250 724421825 724421849
    0x10b0d0e0705100309060e01110a08071e0302030a0f060b04050102010c0305010509180312090c01031a090c090a03051b03071e060806060910020109110118051c020303040305010c0810 80
    0x503d0030079001884000300c1504c09076211800c03044646030038030940c803100074000500c07501c0b540d4200005200c0303000240f82d0300a100c40f004032518000403420040c000c0d40083e160160f1390b5900d4002d583c014012104120766942d081090104039240c9000182042e00d10aa0082241c140702c050114242d910a205040d008141c42001c141c3ea004410009804402c500c401c80f850206c0c00c00700311051000488a4030f1140c0c00c0404c82030450b45e4036000b04035003411205440c020003000100040c0308000f01800d10024094005030003012034440184c950f00458011080e07a0345c48201446a56420703412004641c4a4000c2142c0410510f500d8106401c0c0030203502100c1c00107501301034040d0303100c04000e01a1076102000740f124004c69621040407100914265002103070100940c03921100b11001d2000700d41c140001b510040903008141c00d0b00d1421070303030304448202059408008200000c0850140650035020000f4044103000c1c05400207543c2030415510010641c1d200c4c9803820010b40309005031121414 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 724424325 1250 724423075 724423099
    0x20c0d110d0e09010b070302010219031506031406091b0f0c0115120b0703090c15020f0c01020c0405040c0b04030c0f120201080606090a05131e0203090622050105010b0d0e0705 77
    0x7115a000d006d86601c68000140307410624956142540642c1c400c05001a4503010307010140500e9034185001001c4030305080c04444038041403502c1d0007030024a100c2c01140000001030701c00e550788411218480310000c9042d80e1302c0300c481040115030f0000300c0e01041c035070a0808000300300d00460b910a0440700440c41d240346118840d900c850050f0000352010003059110b0320034a000c5094000e890b001031401400381d4941da5601c00d006803c1c03241810f0b4024542c0c010440040c0e40340d8001c207540740009800c54000401c1d580702e182001410032160032255242030085404404c0186005400702920402a0004401665a603510310307140c134080c4000340000c800c0c2000c561107040c000042c202c801c10041604003810345035804540032800d0064000c2c1c2c03407a181e600c01400030380507500e661180304144009514510300140300301c0d42d8040203800041c84501084560080c40140300758102c160750f115000344407a50751011074410f50703007004005000c0742e4500703031440f1521000010001c080b940090030540d4031030 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 724425575 1250 724424325 724424339
    0x20a1b080703021e0618091005060f09040e011103041419030806130c0f230414030a0b07021e160b0d060305010905012c0312060103020c0d110d0e0901 66
    0x405002c4c001c8090104404065403d0703a16a00500b100000c0030b0804003c0411090070011519009010122001c070800c0e418480d549880c0210f82507440480c100320f5030345030038601080081c40d85240c1405194a8a011124801d1580d001140100c0c014520703001d82081c0c0d080802c1c0c4584000c2414103000a95006410002e130181c40c5003540030381c006090204400c4018071500c10348002c0c2e03031001d000507050210074540582104001d03041c8170300c100b41d0000c008016400400301d8800c1e401440c1d2582d07082d04165100340c1d410003103181c1d0a0381c8084090304506011001030751392800e100d4680301002417111494140700380002c040c2c00710002892032503000d919010300b8148603484050204092501c1ea0b0011022034003d005186900d4030440000842e040c411025200f40c1d040a0740001c10710845040f13502440f04004160780380c1599118484025444500068001b44205030b500242c5001d103004c030700001c0b9041088030500190724403d80300441184031044032902003250b845035200b20414014003e403 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 724426825 1250 724425575 724425589
    0x60c1b1014032d0f0403120908040e1b0c010204140402182e0e0306250f090509090607080603060915060604080106240206132004020406020a1b08070302 67
    0x80180d07144859100e60202e0008495000031900444d010140c44248410554880070140c05c00d8011401045000c107540e646000c24030480c42222070510300200070443c08540c0f844060443c040400419503075641c6141d8840c0030f900948564581c1092044424505080c24000c0792b048903031071441d00f000300702d180080001100c49040d003481560743c101c203c09c84041c00813081d041c603c0d1281d10382c410854518420545855401840f01c2c1076802444040343c2805651040c0080380103180c2090405000e4440d0120b88000440c0d0000d94004168410f1010a210220b42280a21003980e60103400e83c1d0b03803000b819580d09041d80c51102540c88562515200074200d542c46802c940c00821300c0d45000e07a9000c1040c01d5035600d0b0021082c052080c008485410380002d040c0c507400440b8000b8296a182610465450740c0541030b014043c80300321005034007500011450390007007200080c011900c03a0b44079080250b840344158004c0318440f502c0c484600b5103110f4401410300311803206000f0440e160440c0e0900c602 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 724428075 1250 724426825 724426861
    0x905390910030e030c0102040320010f270f21050606120c040204030b0709080a0c0b0d0902040c0801090608030702090a0e071a1c0c120b060c1b101403 66
    0x415030390702a03080440d0300500c01031180b0b81d85c140c009601ca80c25400d01c0e46c000c04081c0001340d004141d0648449103640c10402007407102d039403403c040c644801c0100300e800c920f0304104d8800e66171100200700441c43d075060340100720540d0942c600442d911301c415405041d80c40e6800380b018115501c02400201246001c12031804040325481c141d035000300541000c50140c2c0c00a4004483d064031120800007940e910056200040402c44020048004240c442102005481c01441100c14001503104078074240381c1c00040b00f659015104100c2000b0016000384400028010190090308240c0000350590001041e01c4440d07030001c0c1004120f8131580c840d8001425007050555450186400c0066089581a409448810940301d100d580e0103d85001d00e411209011000051034070340340198105503071220300a4450440b00a0000b050115000014401d0041c005201864400d100a01c21a4821075100406e81401528a101c0e203040a113404e4481202c0380000d000d080000740001608800f1410030115 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 724429325 1250 724428075 724428077
    0xd060b0102071706060103051e0402010e0f060a08060306100b0f07020d150204051306081c11070602071a040b07030302030c04030204020301231005040603020c070905390910 76
    0x14030b490340c4070790f8a03400458140743c0d940d16400080400100d9609030213186e81c040542190400b040c1c0500d21400c40840c00034002074104a240000c0150303e40700d0708503214503000c0c020b028540340c115004005140303200840e51640a80240782c0415892001d0413003242c16160311030080d41c18140c641c0711602c41904508016030b403040c00040e0b03040100380800c8081082e03441801025aa641c00c10085c03004803a034202c0005100380c5800c0f8108082e031000300307030400d40100c02d01000c005420342e0001240d04601b008003803000c50140d07040000384140c000400500b06c0b840e81c07001c50850140c9070501d40e2280524421060b56420400000c00001d10950096501810350385255040c41c1d12a00420104d8009800003a4480255031031101d42510003082003103050b804880300201160700740401090b50141d4030a0748141500446c041176000c8050021a014080c8000704022a04d01b10f9500e081242a6100700e0000d000058030851082c3c1d00034101d0740d889061070403da072411441800340b04201e0208060b80c8 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 724430575 1250 724429325 724429333
    0xf0c0102040302040e0a06060605070b15030c1c03020609030301030c15030908070b01030b0a09020604050103090507121101120c0f0f03180b010f061110240b0a17060d060b0102 77
    0x440142ea07944034040807145c0c0c500050000140518156003280c0103600810184103041c041100003d80060340f01d5800000b2400c510758020f071100104e45083e441071100c0340e01c26028002500d6841598940c82a264060ba080b10019101c600b8066181e12082c0070180845281c2102801045141c1c40e01d10381d07440881c5000108110700e900e80000a40000f002200c100902d040100107202003400030f590041462501000a0480c0f540020510721651240720305258440c5070040034454113105000c01441011030483c90003c0c1031804426515151b40c00c1c5002c268500b4018102d80301070b22603402000d049032200360b0082c6000d407060303038010800b07040c007800c041c0c0b40c114100e2203000160017040d401f80b0803035a4106550501c0c00040b403c080310f8100b007003001810b0030780414440001035000d9425540c20000914020a00381486000c07d01081c502410f841080380058070004c860028190203040c2e41c0c03480500d000c8039581d992508029220f8940c8401e401e100180891000c3e4840341c040c0314140101e07 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 724431825 1250 724430575 724430579
    0x60302070c06110f060106210b0a0510120f0f14040c330306050109140d0f140316110a06210204080d050408010b0d080409110403060e0d02150106050f0c010204 70
    0x1c0c80c0020980100f0000b405010310101040646090425490723004c0d142400340001d08000706142d10001d02c641c1340319802940340c40740128043c14607956a4214040248a1400f0020150b00504917522892a98a142080b555804818400c1c0e140c0103076840090b402c3d185280c410103034046070051040e9040580340b4001d100300342d04000e0718a914407005441c041041490f05c0700152481d0070b0ba0b03101d07440d555407001c1d180100b907031214602e40100381d0026517498203002e20305003030821503280d540110203440005544e140a4400f1501d20000f50301c00c109603140240300c201808070b0030429220b54000302c0c4482210103986c65100d01422044510b0000041c00e10399141d0700e45203000040010800420b07030005090090403000c0c0100d90340304c0d000740d580d8503110380c05655440310340c4164403606032a55a2803413002e0358440e26404980003550040707414407002440c5501c10351100e02c60501d14000d81714128051403501f0041c5c1070103040303903580d4480d941410540404400d280c8e010b030400080d41d560030000 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 724433075 1250 724431825 724431853
    0x1b03081506030f0603070806070e13020c030301030f14030a0c1128031505010e07050708040305010212150108070f200613230304091820030106060302070c0611 70
    0xd035220b40f18a0000440c1400e0400c10305003400990341180e80703203411110410803031641000c2649a00d084c145c803041204400300e5800c400a0164140040860100200010030301c00c00000780107034580640e07010300c00c9018100180c1d81d24801c9410020201d5903512030400032980d09042002c18600250240c0d9086044103841c0f41c1041c0081c8241005024030f10081c4203100104d1818513559905035010000e550400c0f12664207035038002c090b041002000240c04003000001c0b8140c5004661103002075403203e0001036482080c1c030007124100c9800c01c1003580b01140758800d00a442c041c400b1925044025094000b04484040100f0303040fa9445141d0320100e038400c042009440c0c81450f01c14a030502c40002403400324644190004815443c00c0d42500380300704001c011003110200d68000000244644080510501d502c0103004007400d1404aa4104038858032901c0340f0808000c001c030001c101050300c4582c15000c90282e440702406d0071002c00014007000d40a038100180321442142150030400210b50 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 724434325 1250 724433075 724433077
    0x50f0d03151a1b1e0303040f020d05071a04050f0405040209011806030209010b0d0c170112030e100c03081b0403061d03030702030405150309060703111903050411011b03081506 77
    0x70071100e030f6600200c201100c05202020002c1100782c1000030b5480d5050036101da41c01c003a000b60340030f0b00c079040c031320080820840c04000740001854038041e100e251540e0910148515041441054018500d0000060303640c030b81031154501c26680140030301d10507424040d00444018a00c540035400503504c010101c0960b4424113418020071000c046955150241854001650020303802e0300e0038040152200c501344409094403606440c101050704000001c58201110301c80041890150040300c0d840c0f0300c46000c1d9001c500050954040d8031000a070341c490207029090405403900021030f0b020300b440309000084290304421040d500f4210010b141c0140c9411a500b585d0041d02c40d0b2000d80d10000302007109050035689002c0501100100074190b1904c03511540d211400103080c4420540d403003d0a010440001c2c050390360011580ba09003801b1801a06c0c0a0002c010a0b54162204090400822244d40c49018010311400500d414801800c1d8569010f441d004000380008140480c405045a00394079414 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 724435575 1250 724434325 724434367
    0x90612150f030809120703050a1b0312050a17070c060e070504051003210c0f03140f0a1e0f05181e040c0c0302031608040f03050f0d03151a 61
    0x3c8150b560440d02c0070008420940d08103580c0c640c00a50080011840c04a40c1d030314000e800811301c074030740103004d1604920a07441780c200520303c20000560100382a4014050302c6e04101c0ca4440900005007040c09220a0383c08403243d5002a54150980c1c0004031617400c4040407840002c21600400c1d00d400004056500440b8046206030044038104140310b40650300b075100d40e24115002c80d80401000004000f407801540c042c0c10f60203200c81101c10580b0409207140d200c281003107400e484556145142055130b000003030300c0f0006070601d03110300c4e604440c00150450106560301e40c0c200288040c1e00c25945c50b04034540b07109001244851140060716110b400071102103018902068168420381040b089921840e41e83c02003180b56041d0000090f00042110700e00380d54527001d14402c015518040e50503100f95003284046005500b40003040210000c0d071104ca1038114819600341c1000340e0011021644c7c0d81c0c200b1600b01401502c20011030b15039440c01c044414644500c58600741440201e042c01007002 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 724436825 1250 724435575 724435583
    0x7020a0806130c060503102c070806040c03150303080702100608100e060f0a05090a0609080c0c06120a020a0c0503070b040314040b090f0d0b070e0907090612150f03 72
    0x4182c40b4001c0110341c0e0541e6024003080c3c1007a03401c50401c440700784030310203180c06214042900240700f03000030030402d2081c0c5550030401d490302c49240b420700c070010401202038031250300030f90810010040031030103802072154a10401400d80c03981c13440c40d1401c43d280b100160882042d4007034005c1000316001c1a0080e8002390a49000410329895043c054104894061418000c02d41281081c0680c40007801c000a411030212000402c494481c2d00e005801c01e0032048004212501d42002c000c10000080b000c1d08900081c003081d0b0700200c10a409010062181d03002d10b07504850344034006401400140d02402c4400f41c589412005200c0e5940d4582c9103500030002698230070a00d1080204041d402414803d00c00b0304095840d00f01407400454100500036108140e1103280000e0340c1d24038585400e038200100716049000e0100504281030050300402d8242c5042e400f661184000481c030902481001c02103d004d90f07600c060702103004401c817000740b12444940c4041c0b0440080083ca084080d00d4050141d805 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 724438075 1250 724436825 724436851
    0xa0807060804021f051b030c03160218040503030403120b060706150f05100c0609020a0e070e06031509070e030d02010c120b0904030c030909150e060306100b07020a0806 74
    0x5004011510001d592a130800d00602c0d1000714926a105017910804824001c044403004c0110001d00d003180120030002c0342a10003c1618402d16580d400800c2c407042c02901c403413800014a0090244480c1c0c100c402a086600c200041000648240c1d0041607000b040500000d4600994002074803e610013482642c140d600d6601c100f01c080c1c82c0507a090001c100090900c0021480c04010684a0360240b011070b040c07191140402c014001c1c036822011050350300500c032103c40c0d0b803220f4120109110a84a007800600c0c45801c480d6a42492030481e8017401d80c161302c412880007580100025020700400c082c0410006001040e410b85007000005403110480d00041b40d5400c002c90024407403610402421115820aa00c0c2d900c03680b6165003080d04180c140c03819074101d15050805680c0b0300b405601542d81c2901d07060080c138502e0074060212003512000c01150046481e000d04242c0c1da01e40c1070340c20140321402075500b0014994682e0041071401c1c4040c00000c1d1083d0380b4103e141c2402005c955907401404 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 724439325 1250 724438075 724438081
    0x7050418050606010f230f030705071502040308090f0105120f0603280b180a05072105060117010e030d0606020d0c051b0f030a050a020103051614090a08070608 70
    0x102405003d03071108003031070044042418100003d003200004c050a114081c0000c0d94000501003200880b159441c41d071004603545e0808401c000e101c0da00c140c1d400e440d49040711180346004c014900031182200d410071302203030034540c00708200a62244d44e500030301c0c10f00208000d003903003c00c500c2041030310604140c17900b0754003842d040d8141420000407510a0003640400180c00134100600d190048030690012940d048940d100315104145d1aa50800e035030303451150b20b4406040200000304c9401f524840d5903c004514040040c841d641c0b40d1905000b06590005001030000186000f03180c91582e000200202d0323045590785140741590700403520203014a0b1031b0303101405910340410085003c208680303400303100420361ba159541c807502010034541d10154101c0000318203076141220200070900060560f0341c0c00d0610f02c1c1c0507540e401e031203000b01c4c0428103103000074480700441c40c40e5940d4030100fa02c89241c81441708400c95404d6200c901642c0e8001e4016070301140080701084000c0141c00c0070b03110034003941 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 724440575 1250 724439325 724439333
    0xc0b04080c01181e140f13051f030c03060606050c0a020d0624050301060501050c07090c14030c0901030c051305210f0709050606071a060103060306020f1329030907050418 75
    0x2540c2e4011060003a29a43c80c044110344604447c443d40000d503890014060302c0303483d14144c1401031402c407141c200c80b02481c007005101038444003030101c4c0e10698081101c50744c0c81000391814047c0404030340d1283c1200b4030702000b50800c2e5080003070300d41c8512400645a030703600c003480c03070303001030030104807202000e858000e015500b002d00c1840080d002c2401c1030303401c001c03103600015a0390300b560160003080c0303072210352081c0910302541c141d00c48444a591050388a01c0c103c6091101a08403040c06400203040c0300040c8419801942191008141803800380c86c4c00303042c402841504404000561840c08010801018295040c0810b80c08044014080d1006a01c1c0c820b2910a070760014240c1031084204112000000d266080c60352441794551240c4400c2c1c2c2d64210059004045a501c082c0405000099a074070f0440614018a007a080f01003111000b5600e031091002819840307001028106141e40c150510050008007a45e4005000022500280d0719203000c01c1c180c03043d00c010002c41680110100c4100 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 724441825 1250 724440575 724440599
    0x3010501080a08070f030e1003020a030c0c080d110c03040605071a010b0706050603010b120606120703260d0f1406040c02070e060105041a070c0b04080c01181e 70
    0x50070041d00030b1071500d01e5a00c500200340303d07850000f0000013012031304204150080ca110740c19080003d00783c60700c0c1403c114014029511003503030040000c1ca448480c8001c03500601c45040c9042e04450080d040c4542c102c0707254000d02e84503011200711142070005d100341c1c48042005001400e030030750702c540c0c4652040c5889140c0d011b00f0041c0b088003c2d0140010b02c0071012400c01d5030f040580014009c0742c1c039141c40010a004041c01d80000d80c211590644886407400002000e1740100b000b41c500c6060041c0032502a91160998080140104400078200280d0180682c0c60030740e00881c01078444c604401b06042170200c9048030f851550071619012980100409c2c542241c0d032010007a03405005401c1c2c40b5100a454452a019105c880f582100c082030050340b107201590054143d044c2c010800c044451881031090300444001c0303607004c0c04008045240049002514102c4001d400108451142d120064815400c40e0301c0040c1054040c03900042e58140f8070030b51345001ca0b480b003484c3d8a254146110020a = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 724443075 1250 724441825 724441829
    0x10e0307081e0a03020c0f010e040509060118020702011b020a0b0705060a060f120b0c040f090e06100302090c0a0203070b0117010605151602031e030c060a0603080a050d06090f0b03010501 82
    0x1c2d80c00941409012070340104a0403400b0004450809410600c1c20050b00c50300010031200c0c0d0400c0c50001081090400050528141c0b840e464035a0f0150303614101441c00d070310880c040207000840c0446c0c810b88002c248462000d6051008140504c1c0e661252031034030042d003001d041502d865210400b8882c2240c00c87c42050007511031003540b603030110f0074291103c2011646240041880c00e070340c4002624110503a0564004e04001c0064402d01c5030fa070021503003c0d002006a49806004100c0403803c0c1043c842400e03412285d020b07240c0c03007903a0340d20040030805404c00802c0e0400c2d8002080f078540001c004294180c040c01e01701c000001200c00111049086401d1500420300860401c00986806520001551420316005940b2056030109101081c10f00d00c0314264030f080101d00c0c2020381041c00010018010031403070b201c1203400380d94540c8003a4042d10040d12000c2c0100c403007000002c0880340308800800000ea41003101282e200d031355a0801c2c08460120700552805680c2e03401003540c5250a00070180 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 724444325 1250 724443075 724443133
    0x8060105040b030708130c080f01060e250e060a030509240604020a020312070e01080907060c02040c0315080c030d0e0906010302071e06090606080307030c060209010e030708 76
    0x70078582031101c0e0300b14520000e070599050255a80008800f10034482000001c143c1c0080b12041b5955114405a43e4100c104000e011550904401045548400100520540101000f01c9086684030111584504218030302410042c000c180c0c007000da02c45a004207060070440e03800068a01e0b003080f501e410070071045581c40c1111540384d9404031440310103141641006088400590b03a98001205920390301c650000820703036206800400c140c068001c00b1106420380280c07908036072076880000301500c904145c0034144c0400c3e003100d0070780c0c00350505600040c80341c13405090008401080c8000210404015441250a540908164190340c1002e00103445104002d0a03c01070b00c0c550b4400003402e0321801402c180c100343c0c0c00304024082c0440220f01c4040c041240304265500794150601d0300140580607000e0320018100b441c000385001d03001048548039505541c4000c0040c403681d031001c000e0b500c4a0140c0d4100600c140917403a044c2e60074172a82000700031000003031866000048814104645080c1002 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 724445575 1250 724444325 724444327
    0x6070807030912081e180d05040305060a0b010306051f120b0906090403030908040b040906173c06060f030105070909020c07240809120423100207030308060105 70
    0x41c00209983d040b4104100e4500307000b072040e40c40303082c2d0796942000e00300c881d102c0003525000c2c04200500118000300741d16040c007d9600d000d0910070143c0e9680f0551200415607400200080c0714003050b58482030845105140201e0925580d4000940401400c000350300b00814139600310041c2c1d0380009141002000d82d90003444540500e0001400c3e4800003040b40d4082c44007000000c00b090b219501100805034040b040c1a03e0710380700c1031400c81940060041003001c0d86021000300e490154800c2c5c826601600310001c0c41403094074980410ae500b6410121051010020482c550906a000313024036a448040001d1000b803410408111001c0ca54009540c001d034036000622641070b900031840b206545088001698a0700d504000b589000e80c281d000b008000c0c1c008200d032031510101d510a5112034102d949180050704d0f110000c50303c40966040701084204100020400208841b03090202c0720104041150071500d0300d00400c04d80710403d2480401a001014240101900071410300c0d00803000307203403013 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 724446825 1250 724445575 724445591
    0x14090f060f03190b0f06091c030f1211030106050a09230103050612120f0409090b0601031b08061306090501060c050d030c0804060209120f0318010e030307120507140607080703 77
    0x13040b42171207139001003030040200181591f119210f918540b0403148003044c0d242c104400c3e41c00c0081104d520350341000c000581d1000000d41c141100d02a0340c6200c01d20070b4040e883d5910300082036516901c03c41500041c0f207248500042c0540c00849801c1c0d551100040103c1160801e00c001030450780001c009a204480c00440d6881d466000544030610002042003195101844c04110391107004036404003507101c0c20140c01d00c040158003280f01c4c2c0122020b890a1010200202901c00034102c0d2040305030004440100040701e80c80c00b551040c0c072442e24600b00181d030030307229002002921000d802980110300c1c00495a410440100612150a02c0300c2c0b804016031061103c0003031000c170001c0d0003d403407541c000c41d11308103550301c202c036011104181108071501d03851518038551301c0780c02240c590601c448032018106142c1d402041c40e00c00107003005020390319028407a035400811940e0b1100540410205221660001c0d0340f07503d081204486180040110745003000c001408170b44000c0162040600b000c0d10 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 724448075 1250 724446825 724446829
    0x100504110301030209100e10030618050a030f090306050c0403020a1512020d02041205010c03050121060e070e100e150d0605090309130509070e060114090f060f03190b 73
    0x7520305507641110000038030744600ca01c42d001d06542e90002c201085d04041846a00d00900209100700c91203000305200c4154208001c032400f4480d030300c01034140d4024214010010744207094842600762141001400182c0741d482d42e5089407412201c03180e24407000242442907250801c0c03264001d00384105202000f030307041c00b0010101e2702080b800705c200ca0b401064031141d0040e0b81d0181c40103044280303218450711007103003403040c042e040350586800800d182500125000d543e1008843c202601000d07485540310103640c0304401844010303a08070150040031400f207070074030700d8400142c003407102c201c00c01a99a080442c1040c10700d0028028640b816140c40c400f501c903450300c03038845450b00d0300903038000f60750764450030014258499401030541c01a04140b400c0500e00580d884140282e4141088402c203985480c420742d10710034141d487d035001c650003045841c507155610b4014844030901400080c0201100408120541c010100d0035402900c0031080007240112280c40c40d0300740019400a2000f4464200 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 724449325 1250 724448075 724448077
    0x70305011a0904050d030b03030708030915091209063703060e010e0c1b0d18290a1806120b151b031c060f140a1401020a1a10050411 58
    0x50b4031700906403100c180d120300781d4060003aa003241d500301841c1ea40d245094020191103000c81e9086002c6a001c0c000401c544440026048602648080c2d1591030a403060301009180c1e00150168082c542e103448030005103044c0d03414442800514804031440c111000c0c20041e041d02c0003600800d80c0000e0317100042110508150000d40c00c01c1000c1070751a940c4078900b6040001c1c100c1524160701d54842c6451701c049095100d0304052a8000700044014841e03100c1e202c0e07145882441051180c070104009105604040300001070602c1811410801c00c640001200038443e0015948500003060b88050792b582c840e1000d009050002d04100c44220703000c4004080200745004200200b4a01e8040783c03980038645608200300c1c0d0b500e20401030032181c82d4a42d00102c00240c10300303010340b0780d216044442c00070701c481c1320001c0c0444040b002445007018604040324015604d02090750340d8114402d6150a00104a81410031546a02060560700f828030344916116648100e6500041c011407816960040c0505000 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 724450575 1250 724449325 724449343
    0x50906151e01020a05070e18070518090304030606080102091017011a090310061401050a0801030f0206090d0f050706020c031b03010905120a08130503070b0703020c070305011a090405 80
    0x10021400120498004034034091002130020924441c144001c0b80c0307241a900c2c514820070074070041c007440c18032850001d52039041c81d00c50035401543c1c144602c1c000d480e041c83d0781039002204030110b904040c0c1d80e8890b001507540ca0303402040680d500090250300d81c10905210652102c0354280b40340018503440682e040c983c2c2c1446001d442c04401c041008868611900316407400400504a4807401d0081c032081d00201018440e10300c508280389035044441d401002600c80b8444c80e0b4448402c0b130ba10759100c0300c00020900c00100c2e4020820012103045941e038000c10030080f40502c030070700c40c0f04449151241c60b01c011074000783c06542c4040c1030b1061076540012024407030604618401003c0303a8050109015140000d0024014022000c54402055802002d044204060782d81c03140b0a498500c80c50811803c04807000d04a0b0300200061400f0078004030350030360001a180780040c640410386e00f02c40d003400a15042101c59944400c1900c504000c81c001da0300785090f088481072520309003551507556403c084 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 724451825 1250 724450575 724450609
    0x5090f010c1506140904051b1f020f01060801050106021903090513140a0b030a1e02150a080c0f0a08060d0803090c010801211b0806010321030b0102030d1e020d05090615 74
    0x2244e000031a449c1c08540d56420101140001650494018060748544100c203c180d5250320b0001c00061100c014000c4504030355042e00508210200e07841003c030312001d070700c030183c1c1803101017400010207440e9240c0751840403010403400501c860f05c500e01403003000d1010b4400c14069003040001550707583c0106010240c1e81c2d00106c0d455580107812041e50380403050f100061b40c00107818402400d0145801c2c01088036271540e40d2411078564400b071040c02c1600500081d24000c003000d02c48103d009020300c0c4000e170015030061440d09901c03903c2d5a01ca21a51003125000d001740c0110040e4034841d42c100400b140500410910f0700d01a01e81203494030002c15980c180a05192441c5400701010240e270f100c010041d00001d016580c184da12070400c2c60900001801001c0c02005402c40d0040030b522038400c51460b40c5050f4007440c80c190600c0309410107802541c04804e2120185025081064020302c003c00000c0001c0002141601d01044401c2c1480d20003000100c3c20040840680300540e10003c00105158030 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 724453075 1250 724451825 724451863
    0xb150702030118111003060308040302091e0c040513020f250f050d0e06090904060b01050c1009121701121502030f04050d050a05090f010c150614090405 67
    0x1090000030302402e9210701d9014031a40b41840c0c0c034113000746030034001001c407426151149a21006003044040390901e10000d441e51100b0302040c001840c0101c02c840d0071490140300880301409200c0386090604c01a01e95410350f500000c0c00300704a040c04010a0f5400340d00361002c50400c0e401d0900784450b4030595182c1d5100c03000901c51074105a1540315408481900600c80150b88001c034034000e070342e0309615401c080101e07989406a032820301d0607504a441e68070000e0702076500780c2c4a0380e27145409006130851882c107014062182d0070880101f088901c5444c40b8940011500007100d0a0030304cd409400c0a0b204200500c0251903203800803038542180c1100d6100301002c601c03103000d040940d0824050340401c0800c500020a00c4030303002440e9401400342d8055030039108413807000b00003520f0b035210300e00840021601c14454140a885c080c1000f081c000018141501c10186503a1400c2007003a6401c45146071a5a501d8103000a410055500b410740d40d094400701c410b81001c0d02c40c80e550f042c40131444440750030 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 724454325 1250 724453075 724453087
    0x605160504050f041523060a0e04050402040b03030f04030b0c0f120c07150902030106050303031003060b1903080a0807170406050a1b020708010e011b05300405100b15 73
    0x71142e00050351800c0c0d10004030000c079101c0d070014405281c400031100c44003000e03440e40741c03c0f45000340423545413010725104c10100009644c1800b0262000601c16680182e440180d0042c603102072005007020401c5a010540e030354154500722894400107819403d0202040c405a540301e00414100e44554501140f0380d0410340c0c17543e1201403144a41c1000402c131045640f1645580031840d00703c00300481c402c50003805440d0315901456035a000444084030036100310355040020400c5540030b0160180c01800b1100074141008040c0e81c144401e81c000c940f00140040c3c200401e660117203016412544c01d24111140d0480c40c0d0500b0700d104006070000d401d82e81da81d000f10350b9260955110b00d40440d007444131500c0c038450f00c48020b9101d540910841e03800354240803d8044400061155401803116a10440c2158a480d0350480c3e098004560100c421002e4000484810202c0c7c00220800c201590703000460349840d2034031381e041090400d08966814180180c50083d80d48590255800400850740b1a80b61a = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 724455575 1250 724454325 724454329
    0x3071406011d04110d0614151c0f02031c0908060103020607030305071209080a030b06030402241201091a09070807080a02040f09050a0e03030f07050f0409180605160504050f 76
    0x290312a0001c5e0b02030082d03c03644080140c3c0e0b4201c002c9100c0016903c111696238a0034030b0049100c15640e059220380120020302d5070310201c6e81c50703004082c001d0f0f190003040015940171a1a040c04034400c640c454240500c41d1502c580e10001070800707856844040c1880354519030108226000c0c07034a00600303064a40f4005440300d803003040306e80a07403444201c060180014508080101da4031078001c100c002420202040754078100328040b64011a806003c81e6240e0b40740c80b40c0f194402824441c00b400000b420480d0a1400149071314481c060040140c00203030340c2c82d0b110000b0310140f0754200814080e0246108020b0381a07003120301c40754050510304141041d40e541c4002003000b4401e030340200f01c80d0300f1b0080000c55041415400345118241345603040220700b044015842e5a40011100f2104114016000840d107074400c00c064480c080d084202181010380712200c030310a5841e10440001a428004001000c0c80a00e002d2541c204961079003001e14803855403c020002d118a005d40c9000b1012041c004080d9 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 724456825 1250 724455575 724455593
    0x309010509270115020c0f061602090411040c0806030303130507080d091a04360203070f0212130b07020d050618240105010c0507080105070203071406011d04 69
    0x7000c5950304018100420b03210710300201d000c2c010350502c091440e0110402c2400041c0c215090b4800401108603880c2141c10060550b01540040000c21559201000141ca43c0c00c1c0c2140107900c2001d02d440b280096600780b2003107403c10509007080207040c43c1481155100030045a41201c0c1008a011507802c1c0d45c01d06510740481039218514034480c80d03030002941640040c0d05c8090341d13102001c1c0f510300174000b03030607403180d00039805005106004103151005604841807248d0352030140254801c540d4014216580498004540b1400861034500784080c1e000e41c103110f034011070400006028146203c0b00625120300406024622074400001908801e540d100f15114048030b51220490304603141c0341c16110740e0102000c54541c0203101d100d140d01c1c80e000e640380c108840800002220303202a840d00004442a201e03601040e5014018003002055560007809039074440c0c401c0d500155a194894030742164118172003035035110990000001442203009103128140010390010203084140c60700d040030085 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 724458075 1250 724456825 724456849
    0x31d0907200705210c060307200f011b1715010311070c0807030209010f060509040f02132319090506010521060103050a0b0d2006040b030105040c02030c0309010509 72
    0x4059104d0042c0d440488925501281100521081c0c518507140c03c42482030038001510081b01090354072000c0d21017030224410030000700c50745034121b03802031005003544c0c2e0840e051290f950408551624800d008c480d00052000c4080310080d01d130408514165900785030801c0d034070400504060711072010f040092095419611601c0c0c203d031400140a540d81e0066a6921712031008034018000e0500000d0141e085030818003c80e0744a45a0600e400c00d800308000003000d5090200e6466a42880604105454048414050241e0911004c00c5402d42e015242c4070800b001c030b01d1803040e2190300c0080610740700d0150301c00c00c417003640741d02041503101c040040e00e2a000d114039100c620b55160140c018188010101d450080c00c080e00c041040d070700c52002000a981d0f02202454205103021034020024084143c0300c0030546108040140101400f40001c01581c010341c0700307901d03441c4040b0040c025441c0500c24807442c0821400203520302414103c48989900611010a06210000c01e850105844082030309035 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 724459325 1250 724458075 724458079
    0x105014b03020604170c092e0806091b0307030f021e03061003120305160c0602210105040c0206040c03060209040f0f021209010b0a09050406140103031d0907200705 72
    0x2403201d0b1645a2400e0f1440041c28140f100e201b40075090405007040b41d015030007043e111208025130840340c3c400001443c00c41910600040d0020000110300c002404828060207503a00035005002456200c04040000c035818a403080d00700000c03c20000d0b801c101d0700011150705858040300d1034240f40f0307815803500c004204a50075024100030428119120754402050324802c030420034120b21b241a04804440c02200c10038001040355102d00b41c0540250595000c0e02c1c4140c802504c0c00410100709403420700c010038041490f1807110f0044c8480d141c140120400d01c04984005d07c00c516180d218076600c01d81911001d880c0560000c0c0c2154641c50303d42281030382a813030860901000c094050b030a00250300c825100e40b4040f040401080b1000410701500e1201400101004602400d186442c0020f010103401112130507500c2e03190b01c040c030302040940c81c02180039454288c40340c0c030b108a400031003006103841c4910a241c0c0c802044803807600041905072209000302d802130141611000c140c03a01030650030103031b = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 724460431 1106 724459325 724459327
    0x3060b0d0501020c3a0503070e06030705041e0602060601050c0705330a141c111305030c090a0b1903050105014b030206 53
    0x4502544010840310384142141d64860881e844041c03d1034403134126114109000440e010100320050481400a840c03a284600c009241d150181c40401400400f0001c500d026114448000d0180000b4010941d40d06201c000a861608075208004400908a031101c846546102079002150b007a9001004140c85200c01906c50f900098842d03045846401800034065840c03151100461003482062042c26000c03e4070514010802440305010311001c1040c002c3c0035500c854000a04a10100c600b43c40b00303080d0b040d0004226004100541007400c03d40344049141c4588000c00e545156010207002050b03442c0203168a170f0b241e43c0a81644a0041c1e03000980c4103080d82c100701e007405002864030b240c0848002c0a40c00014a079082640c0c540c1d0344000500c2200c0100d8a03088a174141540c0650441280b0101104008058104102400c0110a0401003103003406801806160b00900d06 = true := by decide +kernel

theorem cover : BRFrame.Cov 724280575 724460431 := by
  have h0 := BRFrame.cov_init 724280575
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724280575 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724280575 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724280575 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724280575 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724280575 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724280575 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724280575 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724280575 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724280575 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724280575 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724280575 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724280575 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724280575 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724280575 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724280575 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724280575 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724280575 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724280575 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724280575 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724280575 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724280575 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724280575 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724280575 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724280575 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724280575 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724280575 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724280575 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724280575 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724280575 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724280575 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724280575 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724280575 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724280575 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724280575 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724280575 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724280575 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724280575 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724280575 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724280575 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724280575 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724280575 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724280575 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724280575 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724280575 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724280575 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724280575 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724280575 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724280575 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724280575 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724280575 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724280575 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724280575 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724280575 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724280575 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724280575 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724280575 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724280575 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724280575 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724280575 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724280575 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724280575 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724280575 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724280575 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724280575 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724280575 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724280575 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724280575 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724280575 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724280575 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724280575 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724280575 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724280575 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724280575 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724280575 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724280575 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724280575 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724280575 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724280575 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724280575 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724280575 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724280575 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724280575 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724280575 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724280575 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724280575 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724280575 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724280575 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724280575 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724280575 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724280575 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724280575 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724280575 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724280575 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724280575 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724280575 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724280575 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724280575 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724280575 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724280575 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724280575 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724280575 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724280575 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724280575 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724280575 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724280575 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724280575 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724280575 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724280575 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724280575 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724280575 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724280575 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724280575 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724280575 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724280575 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724280575 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724280575 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724280575 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724280575 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724280575 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724280575 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724280575 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724280575 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724280575 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724280575 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724280575 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724280575 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724280575 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724280575 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724280575 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724280575 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724280575 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724280575 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724280575 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724280575 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724280575 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724280575 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724280575 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724280575 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724280575 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724280575 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724280575 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724280575 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724280575 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724280575 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 724280575 ≤ n) (h2 : n < 724460431) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
