-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4771
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T13:40:56.677273+00:00
-- url     : https://prove2.me/submissions/258a89b2-0cf4-48cc-ac7a-1e1241a43dfa

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 857913669 ≤ n < 858093525 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 857914919 1250 857913669 857913673
    0xe010f030b090103110312120c0a030f0e0604110102012918070e040b0909030a0c050304090903090905060d021e01120f0e06181b0a03061d060f0c0a0804030c0b09 71
    0x1c1c05100601d42010700a0b00c840b1a071140810600040508110320765420055901c8610b56a1050030001c50003000b428413301c040506150310361304240c10000b40036004e94012220300310000d940e0401039088a02c0400c2c075036656064801c070058503454410600c0d11881c40a8070034111008401000c0c20079100882e01d02d004107507004523a20540c1014800c64500e810151800801410020346490303503806040103580030015480c00e0f600030020140107440040c102140184141c032944d14019207801024060503070003515000c0041d4045c50300b5064042d9186d00500380003644180305065004034500c040c90181030140d03804d80300f004070b201071003109140040d01e240000c0c1d203a1135848290130003501424040b00d01d801d5524003010818003007a440c0340c0c070303003420b0180f404100c2403004034003019280e501c0501843c3c64017403000001c440c20b609003103400d0720740707001d07245103689503040802039007400d450f000c0c5e0504082c0b20741c4180300c5c00340452507000340c000d00301905a2001a52107441804003121070002030307 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 857916169 1250 857914919 857914943
    0x160f030c120209240d11030411090702071a04030204051f060c0606150e030c03060610051305030d0c05061f03060911090412090b030c0a080415020705031e0a0e010f030b090103 77
    0x400800e00c02c1c1c00c5491b5882009911b542400d0703c0b01003038019503281c0ba522514940010690180c001c20240c4001d0240034007103140700380f02d508154003039001440160300076820200081e410151124030214800c84118078105035a080c624211414100750034119480e50340d4050120300005080c03100c1640d0445540e82000c0d213020241410b040908c00c0d12454001e07032166052040c0c9075120081c544d0300703a0080c5042c071740724486074603400b00c504904e074000780e0540683d4051501d401ea111080c000024000d00464100da1114a40c038410804619034800502d41319a10500c0010025001030201c140600390b181e00c5184c1d07100004013100d0041d10300700c1d4030201041e40f041c085038012059000038904041c5840c00c40c540140c52000a116005030803041202001c00035041050a0351900d00b03400f80a40c046480300110318210303542ea84081c1c4621a0400b038916082d84021071501141d0320300b0501e80e116540200680e0064840c1300040b1400720a142d21020408181c1c0c48011690b8000d41c00b0300400451 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 857917419 1250 857916169 857916187
    0x1050105210c012a14071d011e090f0b010201150302090a090c030f0b06010e100f110c04020c16050607080a120b09160f030c12020924 59
    0x700c00462148044101034420141001d03201c0420b180c1c0400c1d100307003030004ea900440354801c00744c41034441c400710800201d159190207118041851980c0030000030210360140762a040c006da0b0b0401c0c0340e04070600280041d8014000751140b0000711810050318400d5144858503880940192814801e081600940e654081c528035030707090041da4440040c1c0920241e01a080d9004910b2450000700006045078030f4590004c20031070040c980d04019608000154084040b034509140007000c2500c0700c03800110600c00c500c00720300d03015070314405010a07900c80400b1104c80600c01d6615100101c880c98480c010709400051588843c0002d0640d90760084c00340540942c8082200006203207500000d00408043c0926000210b40c1011902c01c8030140c05c041c04204010341141c0c001c2c000125141c1e400c204850244900c1521001b104411582c15803075050707003001d0281d81142100d040d1004c8100041e00680c480408402ca64020108120060f1207141501800207584002101070b001101c041200041e10340350b = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 857918669 1250 857917419 857917429
    0x6040f140a060801080a0f171611030d0c0f020d050f01060812031605032212020f0f03030a0b0a0f0602070e01080304050d03030203060103020705010603140c0111060c0a140c01050105 80
    0x5042d442c2408a10395062981440d962003203414000d102e07803040300d030890601000400d0840565007504900f40e403010b002d100502c1c0c00002150445440e01f0303d00019540b4900441c80701d0b0350403032950300c01c85109500d48541d075072407209281c240e81055106404402043d41440703000304000d039040c00841c0d0140b07041181450700078030181803c04000c00740103001c81255101281041031403e49003c54580c3c1b15003411403440c03510008400e502c040b1516410080000d107c07250041603d50343c00b5140400c2c860340c3c2c541d48403120949005100c0e0020000120003010319409900002400381046040c1500c03800c2c4241124000d403c46400340c1d00c2907004009601151000d0303030160100300081d6081510741004542d00308500d400003000d064001c0002040359100b603050381d007030503081802406140e42e641488207111540b58140545402800314001c9154054a40003d400740b501c00108181d591307031010340e400ca4100109030001c1103405158034001582c880042c2034000000000010301d5450641004 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 857919919 1250 857918669 857918689
    0x5010305031b0106211a162703061d030304231f0b0402091009030309050a0e04060e010b2e080708060405040c080a0305031803090a1406040f14 63
    0x82c0c001d80c10700506100340c02460072201001600b41c61107060384446440c0001222291084410358201400100100703e4170365070010002448903100e040c0716444090306e0303040e1310180c0b828070750040030b5000c8108001800c51303000942c0d14094040c44081c0318400100e00c3d044d640241c2d01680e44490040c95042100004280807580e880c1d0f05004110034071030305241e01c0d40c80e0020440c07004c0d441d5072924002c9058a4503011a90941c5000344041c2c00300300d01480240080300540420f0300096001a004280750074400c2c0c00e401561203003000042c1c69511555510054440001078000c40d54852000300c42d16100c40f520120720080800009446250300d10954141c0025440f801041018a5040c04102600700740c000790800000e440104a41e070311418403104181450b80325200a100f096218000e055000010b14050810003403100710344866240711603078030300440c11000da001c0c45105041012050340106030f0141d0b0340c05080702d41895601d08603040d0304403035540701d00d001c07541e061816826031030405141c0c = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 857921169 1250 857919919 857919967
    0x150e100206010305100510420207090b0312030408280914030c120d0306050a0302030613030e06030c04080c010309030806060a1205180706050306060a03020d020d0501030503 76
    0x90259600d1a29956942c05507103401d0040c181e1346a02003000f481f8052814400381c1035242c4207640340c89040002044a000244524940e480b004d02400b81d00d142c0301d6212480c2070901c2d40227004160500e501d200051068650890307043c400d403000c0c104c510b070320000550b200d00d02652210392200440318000001d0b81d03181c43d0000340c20400e07100c09840f450b080150101a80d11315112840c81e01d0103a400302c0c1c030b0104240003141d8401c0290024540b990f40c0020a0740c251040c07554240300048e40c64040c01000f11140c0402541500641c0010300c401d4410070000b400c50f4021f14000380046542004207d1580c010344c2d00311040c0100150600805808210b00c0342001402c0c40d04205011041c0c80003801802c001d003045229040010f100f6240900c90f2446101603002d04408000f9800d061139040e00000520b1401c482c03600820b10005402c500440c1030303078480c2d500a8440c9140808148003200294031031150342c0e0b07031240e090000c0704079456248620307400b0758440c40095030b0f181d0610050b0522041d110200d = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 857922419 1250 857921169 857921173
    0x20403050d020601260c031005011e050d110310290f0d06051503100507080c031603020304030c0b04031d040606090302090423070920031807150e1002 66
    0x10490030304031701c0044111000309420201c0c00c0c0040b0b0341341410714044403500b581c14403d00907503110403880b5610080c102c075280c000a400348a503095880d4080400340c440c480c0d1200300042200c000c01c640000c8034484003c0101a11000307003a0268400407158041104c010a00c26101c92484c1c2042c6112031880c4810100c8042180c0e118800c0001c0d042da410140c002c0c076407603c50000c100701c3d030391b0f0f02c6500e292003070014140d505500305154140c2c0100800c98491000410070004070b0392125218040b40d004080c41e445189030207110f44400d6002c0c1d84007a20031001c02c1080d060000c042030f403154200f80683d200c0d40c0c407440e1100c1c46090031849850700c01b01ca14400c501d006010401c0c07940084410302100d6040d14a103020380d880d81801a2a1030500c481c0c2140e016061804e0140140c1c00310340b0f0026200fa00700c0822218111128884420004504003403030754100704042064140104030040d4810032000c112101c01d070f116210000314420055589011803820400000d051524403a0540c0080315480 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 857923669 1250 857922419 857922421
    0x180b0a0f0e0f011d1e180403270302120f010c050a230912101401030c0b2b09050f0c03070308210f0702060603210a050409060603020403050d0206 64
    0x100140255041008403030620010070303131801484402c1e040003805098001d1130449040c9618070410824a12038000600c1841c10009a00184445000003401590195100c022401d06220b48544844040000d280070f14541e0fa8000700503611455021b01440c032403c050910036400560650070345101c80f1002d0244036003840341d03990966204501400d110030f2408070700001010402c02825a119618580d07801c0200c0c003120718004100042c000351015038800c020806061002c2040c041640c081c0402408101c201c0c40c10070a138408980544990a1210820000684c2020b552142da400e20500150100e85882014040c410280402c2807094044000b8081424401c2d0010341c440c036040c000246003201c04107200340c01d0382c1c6201d10814980c4050168200c2ea08280000821481c02103525000512409000501e41d04011801044110000708140c9514884035400d14450300a05664401c001091100144030340c080e0241c5002014107843c0145d90300d0450170020b00302610b0b8450b003410740d48004 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 857924919 1250 857923669 857923697
    0xe040c051e011b0201120c1b030504050a060816030c11060907080c041b030c11070315050a02161101030b041e051b030a0b0402040503010504060510090603170a180b0a0f 74
    0xc413100d10031524041c0000c0c402d14840c0b41503940c514a45480240c074180d54135282d0414ad0020010015104100d82500e085980c0725001c40303c1c0c0404483c0904490314140d000c0044038080c3c0c010f02003a00441c00c02034130080c91900000c0c03a0200c1120f1b1494075901c48403040101d484240000780303580000740c0b400c1c040703410404d0414641100c3c0c01c8840302010b940701241d0729441c0c0304102240c1c61501050a40d42e1007030b66410141c880c60040951008aa0310309004161032111505c2203607042c2c40103d03444c80e907244050321100415030422540e41d06150b00c880305040255101d02c19498828070001050362420b104249140848400800c00d00415002c2c0b20b51200d045102429a0303841f1400120100b10f4000c0c03040400c004c0c2c05545c0c04181c0640c00c000900041011316004075108078800c21500741148e41c0c5107141030549881d44401340070040b20000420000d00094020b0002c40500d04006480d481200c0c00c040504040c4c3e488900741c40000b10300c9604196021303000f07041903d041c1c035011211500b40 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 857926169 1250 857924919 857924927
    0x4060605070302031b0c03030304060608010c030c020c040c05130305060103120e0a0311130f0506040f0515061b0a0f03180e06010324080a0b16090e040c051e011b0201 73
    0x8040c445c008640c00410501035450821400d11041805000d903a12800e041c80c0a401034081c41c09000901e500b803001500c2d06c103202c0d2060810407502a0b00400402c07400720140720080c1083e0a590080241c10402d8103455083c2141c0c0d40021482032004010642c507500704084c1c140c02c810b941d030742000100b400c14001d95440e9010b11040c0c98000315000c4000c03521130000b03801408030741c03001400c850411003403000a0800b50710540c0b0682040d07034288404c8080307a0701c10040b40c2c001c8a01d145108203003c4e200381d450820001900c81d260751141c02e180840c40710080c4919000000d07208a03070072541c0000c24010594811007068201408000a4201c242807407595080e20000402c40d40c10142d135a400c5042d100340c003401001c100d03100f0581c40e1160b152110641611908a11000d4602c8407080300407405e80070000696078441a42a900c0580c0e981c107003124004501d5018109589980300224045403690352991342007401d501d49640d00001d0b8042170b0016040744d0b250f034940311008000c2c1c0d084601503600 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 857927419 1250 857926169 857926177
    0x604121719110c03010504030905130e19150204080c01140705060613150605040602010e030c0705041508030a0504091805060a020d09080d09051e070303120207020910050406060507030203 82
    0x210304110295011100702245083d0000840070392540c02c1006100525400200741c0c0d0a4079030035141c020381d01c0b2910a24405aa2980e400003034240e110413a510540140c6004241d140c1b840f07501d01d450f0048210803150180d82040e0020b17a601d400c05505056190b0300131041c4c2c00e201540c1007204d801c000c1551299500d82c10001d04c09070113440882000312094020354484d0b51100a909100b00c620b94540e100148aa000307070050700055880c04824405014002044d43c0c603402080d401041864100b805000290425030300c40c5401200e94480800c00e240c0a1025114400d5559a500d03111840c21400c0c1098812400000c00c0f00d00782d600d010360214802080c3c25511902c0014003596800001032924014200048050710101010030340d01210030103500040e40d40d0780140121000f21940540c5c0136080c0d034015940e00c103550700c40304003000064003440c1e4011400741c01c00c0005082c1851500403d10071102104c00080540808130107020302d140c10310900024095074036140c3c0c108402d641c5c02039920700c5 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 857928669 1250 857927419 857927467
    0x120a080a0224130f020409152403020609150307030c120b0310052203020105090d0809060f1b0415031a060f0c240405190803012306041217 61
    0x504500c0024031824615544804e40c0c0980300300505251820311200b401040c070402c2d540641400c0d002c03451214030090034107074840068142030ba15450355082125981c005203902d500f1245562071032081500750006544500116100410001d01c1c4c01c10080180d0a0800007001003031500c48026610b480024080204210307414000409480e1840c4c100301e4501e02c6003442410480060400080681c190402e1740915484c204130b40b0b0045948000380c40f40c170403c40f501a415481440041c40f450401800c0c690458100c2003020001000d01440401d1940680c0200408011190150b1000b541c5481000301c0341d90000d0007102c5191113000015618070442c0000c002d00e040124094181c94810300000501c40050f0105a84400299a6810300d1000485e000d03211400703084045901481960300310440b85a11407110b0389540c0c20154000600804008200c424501c0d102200306540c9070300300140050601c2c00f02c403014204482c64445207402c190303108801042c009106400503039001c100c01000b000 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 857929919 1250 857928669 857928691
    0x1d0c0f0f070303061502152406070305090d0b07120b0109050f28031a04031403041a07120e0a11151c1e0c0f0e120a080a0224 55
    0x8050500b103010f0042a00910b005851240717200c1c0c0d5090300001c035002c03440d00540580c4500c1d510740444500341e965409000c85000c5410981103800e1410382d0082c02101d1180c00c1840c00c0010640100d5000d00480d4070444e456140c50007800100c81e0031220a044078900140e007840086803035000200800c1d83c62117031074000c002d040b0010255640742075262f50301c680810245100b840c44c880d036a0b805c2d86140d21064440c484132a8031060b400c104552664421030301a100c400c0404d4000102c00d0061b4001030090f15251060300700c80c03400c11400300340c41303010340350981d034400030303000300141c2103003142d020045c01030680d030100d0245000901c80300442a001e4000311000845040a4400101c080c4905400c402d502d0300c14100c59004201d080c1e108088400106003801100000c0031040713012030b09030403101c00100c2c480030312200300f8500c81d0703004066680e00604500a10803152008501d41301d10b45504950920000c940d411190350704001c1c1810f508043c121014048039081e03140d003003242d40949030070700703003 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 857931169 1250 857929919 857929927
    0x20901030f09051f140c07060b0603070206010e040c081b0405010807290f0f0d0b10050d090302100c0203220f15020304030f0302030309010b060f09011b0506011d0c0f0f 74
    0x1511154003407445d10224510000035441e20030041c6069911003401160494030303001c20040740d030510b801a00d210714a60380040030240d00707103415151000401007086030610802a0f010403020300c02d0080912902e41c00c4607008414014000300402e03510141c0140240b03601840c8104824008400768a4801142110f0140160864281c3d520b4501c905000c0381a4088001041100b01c3c1c00300740100340400c4084400c202050450042040c10480c840c043c1c80000c600344841101c00c4603551018110610a004440c101e0b980c202d18041a540307000e8080c009a000420a0502c0030780c4058101c445944852100b40c41c03030b0418802480b2442a4007540340100110040120200d0003002101d02660304240514100c2103c1d14000390342c2c3d40300f150981ca0035400c000140d5010b08082095681c08113160450601b0700002c0b42c011504505c903110210541000030b805034000c68801d0008a0103020300039001c5a80c401c443d0015401c0800142458540c1c3c041000000000405041030743e4900917a100c01c1565 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 857932419 1250 857931169 857931223
    0x406050f130303020f0f0102030708070516020405100e0a110304120c08030103121805010f050c07030b090c100e0607021018090b120a0c030f0c030c0306020901030f0905 74
    0xe4041c01030803550710700150300301009060700010650b1202010301c0407a22895480d218a40c04c0c0e0005483c10408502401d0114005a0254014211841012801700381d02c405e5034000400742ca605031182e6a4010824105003c0300c014041000e07840032405000f0301c400c40142e80904040d20000700054a20151440060380c450f205144640c4100d0308001420f480796140e0400c2c43d00e2014400b081000b16449100090070341c550000f40c0c00844205848805100c005031505171110760100301a0b020b58060981c01000050f01103050341d000b0520702006212011445051205c0141c2d0310b240b1000380181e40c14001819900c820494142d540d0543d4601c411840ba40c2060301c03a55800030802c0d80c1ca006100300450080382e20303070011301d040b2030845011952000c1030381440e0303e4954803038024000f0800c0300b80910105480b8017260401902c594441004a139803610303400c4105090384c10440d2000d400160300301141da414020614008210081003200d28200d5581c0e9544000c4c140c0010b020341194100340203 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 857933669 1250 857932419 857932447
    0x24180c1a0c0a110a08060601080109020c151e071805061c1a090c0a0c140313180b180412050c0304030c030507090501030b01120804090c05130515040605 67
    0x110340400300c001c5402c00d0382c0c9482d001c448221a500040d018520703524000800c0f20000400e54050307039068440b030410703034240804403003e944542d122842c1441080c1110301d0b108030381001c2d544509114020000c00e840c84600041011902902e42000c10010404849064009100d010102c03107003103c0785503440483d00b030f03004454078240b085c44141915001d500e800140c1944031a4501c0c10b4100c0f21560303250340e5a202100d0500801c05c006000514480340e06000490020f502282805003c0072a81001030f004800705014003190001081603940c015940c1c9296054020031065070000c540d074903902c41c8090052600c4200081028102800e510f1501c42828011001c0b990000d41c40340980340c2e5180ca03030a110480c0382880c4012201c074464210000383c504c00c1403140d24180c0c1d0340b1458524030340e403030a0001011000040c00550704a41d04100000b192513592041d180b1005003600c1c0c1503202c41e0b840d60b01450080d0950300450003603c110207400300c1500003c041300d058900b5402c1241d00c4184071520a1 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 857934919 1250 857933669 857933677
    0x15092d0b0301060e0906120c040b040b060c0a03020f1c05031506031806011a0327240601030b100f0905100201050405061003031b0f24180c1a 62
    0xc680c110000002040d82580300c46042a200c4003500c50500c59100c030720620101141081e0f484034141c21080394002645400d07080200b6900c0b00038404501c40c2c585800140507603100c02038000e0340342d01c208400750405030188001d07101c40d54460080d002020313007845141420b011240080e01004000400908036080302c0c038410314070382e90251600c8d88910b854440180b64201203504500c1c140b0505000203910000340d5001034042041d210a41d045484418165043d4a20135141a072126a20110840a88010010282c0b0b0070f1891066404450107140d82c846071510113000300e0704043c00d10400802d542c986540f015001e200384d20703001440301a0103004403207100c1c1d540c120b240c0c4600840c59000c056541500100e01540c014025584551100e0049480004a034400203005c14103003512041e0124030b0070840011540140001d0000200380d40d24098400c20800301e0340498940c201000e0207051052003050a41c1c541421081a80003450f101c05240c51510b21610454000c480d00210591844005407 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 857936169 1250 857934919 857934929
    0x30b07030e070308091206040c030b2d011505070302120310180509070b281101050f0106020f0d02070e0901021b0304180501150f020309030f0715092d 66
    0x180b82e05540340e151409842e4072a411140c0701d50341c98034214031001c6002c5a0140070310f40c4407080e100603628550f501c1d03081000043c41002010340c0d08004100d8200c0c00500081c3d00c2c0041440e4a1003581000e5866a00451841c1e042d010001c007030100400180e000111650f04291141040740c43e69540c484500c06030141d50040c01c01070405074480d505901032900018000d103900301c241c8003041c1e1101103100340d40c010510300d20fa180c41c513200015800000c0140d08101251320345042e0101901500c1c0f8982503600540c1c003c00d0301d0080c0c000400519605000810001d00c648010381400354110100a41e54581d50255440340e1580001107040f50200750b0484915448510f01c0c1d40f03540781002d403401c0c0c0301d0f013043c8100ca00e880c084070400d0301140818400d6506907030120351481d1100d40c614604492580360040c0c4a801d5200c02c1008082c0381d6010410200e018102a008001ba1800c2c803ea8400d0b80987e90040c2c000d105244409100c0000c189034600c0025148110159a803010304403001c0e840045a402 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 857937419 1250 857936169 857936173
    0x90601120e0d03091707020307030308040501111b060105011110050903040f030c091b120903030e0106150e030f121c0527060103020a061101140c0901091e030b07030e 73
    0x40c1ca0846416400038144c00780201103508035008030002105103441402c1001754590800d00c004e1000034010098182c0090064000044030715106c000000140d11081041d80c5031205002a03908021003005100c0c0903041c2840c103144150346002030707250380380c3d01040401c01207a10344001803102c040400a54004240c8900f85000c0a6528108000c45e0803090082e0203210342810071082c00340703280000d11950068541d551035044000002c0d4a402403200203401c408150312038880405e201d000f4081c103005800a81100c20b200c00c0d8908010340302c4460790036068001c2d00401c094204458010420f0f00010032114100c1d03039101311042107106080d21554440504c00c0c236102c1400008548a04603030800044051920740494150350032594071303d8244002940240840410b10040744650b05104085050000100c0c8241e0802e80070152910112061841c00c1c4011030040b201c1e40e03100341d118008080080d0a001c4c207000e960f00051301e030541ca0002400382990300001ca0300032444bc1c1e20a200124903002 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 857938669 1250 857937419 857937433
    0x120307050607030c0f0c02010c0b13060e1b152b06030b061305160f05072906100e01030506010c3e0d06110c03040e04060614090601120e 60
    0x290103002068070700410000160b0074890303017074410b00940d010910030741c058403220200c072180d95a150100400030326012104011040c000000f4003d801452420781e0070310050040c2d0094650200c040b0303149542443c4c8203403840b0a1240040005034115a6100540800340711156801158410804640b002050361980b410800006200c00348c0c003400d000da80c0c219114052000e1600b010400e9074401d491030110031980135001001540511174540940403503007071017410408141ca59810012969000c004058800e145d810203a00300b003900d03a50b0040d000c48800b0129150004020135103d541c00d903141c10706690350049413182e806001070402c1264040c8600b003004107c0b4070b100d121007040b0241035110318060030540d180e0003d185900c0203a400e000d041900080320a48a034000362982d403003141c05414080240028000702880200054454209400250708092a02604860143d4030181882180b22009405039a4034071496070082803d10f030820742503001401d00da009000142036841240709000f = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 857939919 1250 857938669 857938681
    0x20a03050a0309120b061e03070902030a0501060201060605030403052a01021b0c031b0d060216150903120b042a09050405090c09151009051c111203070506 68
    0x920007041ca8440d40e41c8900c0385035982841902d20700070705401031401c103804001802609101c20a14442d0405100c44a07502810f500845e041c0141904201c1107240c0000c00c02950410a0281d180105081c0c0700030001145801c00040150101600040400800280085104842c03a03e4582c3e00795502e0242c1d2070008040031018002d601c00c0c05001c1111103032880d07000c3c0302503000c1684406020040c019200f81c88801b142e400c0c0c0c1c1c04005000c43e038040c480c00c01c420080762080c070243c0082c0c1d0544004c0700444c0b500741045181100c07186240f07035080b0b0405240c0c41c002684020180c086440000000c644d402c1e0070b90004020f0700701041811090580702c400e803007940720030300760b09001c004042d21071117103a9442d941400b00f6518225031039405a1b10040101d5902d0501400d41071744203112950300440d601303240c00000c0022000308560000280d94003414082454480300440c1005e91524140311010160340c2c0e28240308901c492541d108065503640261008002e00440d0240c9622100342d0b2010700d000 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 857941169 1250 857939919 857939923
    0x5030a26120108060601030b130b030a080a031e021c09030c17180901080d0509010203250308090d020c040f1e0e0d08151003060e0a06091104050a03060504030507020a0305 75
    0x24803e03482ca41c800d40d000700342554000c1c03048146400020342140403905020b04004040d01c40c1c4062690944148a01c00020400d00d90143c0000041540c2c08541507041c00c840c0180800001403049015104000380102916031004000300c415680b600450503104c03500b001e5502d000301d0100034224a03026040106a284824002d103161101c141070580c40821101c10700052200c240240d540641c80300008512050088001c0d041c10401403048918200704840403091502d144030030b0f0b84403450111808410075803c099410390101c1048000c0508483c0150000d40d1429091080c0c1e0003940e40d00882003151400d40c2040c941400c003200c1094087d6030f04031000006088031390154142d4040c984051384e28030f01c0b465007030780503091989502115000715810000e01c43d0303c0c0108001419501c020001e894481d000e9842c1c4580040e070400a404c81c94841c40505654441d44244c01001c4204000c0c00659601d08584080d29004040003e003581d45240a58080c8038020300a03501c1001d03444000200000 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 857942419 1250 857941169 857941171
    0x1b0c1002060f060a092a031415190303020304180c0c0b1807170c0103201602040f05090f0607020d14121008070807050f06070314030a0606090b0405030a2612 69
    0x7011208046c5403003050710880443c0d0806406032880516003011a00c0c40680401c903d0303c184000b4004541c00d90b0a02081e51540050b034021400f50704041810414108404c0a00104403410703003040c00301513401c003402040b03140c8800f0010300803081100840c80d602a5014640404078042c0100c80c00d6985900e100e040c0c00d181b01c4510041072141000c2c00026500c41d016804c15480b100c4243d103c007290003600900300e81c000400e940101a123070082413016903164054410b00c6190f00760300182070f0a00201c0a810548000316200e182d500a009200780300d50f00141070150545589400c4042c00a00d081400d520300c42c20020380c106d4100c050501135540e0040d05440100c0741e2600032500301700e5440005903220322580c4a0709a0001b05400304030002d003811401071808512915005024104230741d080050750300b05442004205940c4c500500c0419001030b20078000d4103140f002c1c01d007001e14100020307680c1e0b02600c3c03004103045180034071103000d10303034518002d081d1a0b254200d003038030303035410100100c44050 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 857943669 1250 857942419 857942471
    0xb0a06020f1c210b042d060e180f0d0f021524120709020405040b01050c03070305070f1a1b0c0705040b0310021b0c1002060f060a09 58
    0x11482e0480603000d2507065220b5420054036a50112a04011400c2601401d01500c10140d03460b038900380c06070b0f6075512440c60b00c0361079401c40300852040410408029810b03103c1401c0d00c03c1c9403080c03c0c880500d100c6035042c0c0c00185502081c0310703884003400650070040f0320210f003010b500c42c0303a10000b109500018000311260140c0d00700c0381000e50a56010020171829100e04121011801020551481d00b04100b00704240240c00310341c070100c412171f4040c0342490661014240700da01150a00c020f1925015004080300d0918100d4100f06c8c03000203c0b07442c1d20403481e004003400310004001042002036002c00c1c000d503070042c0018020b90403541e191000d00e0740846040b482d804c0390264403143d0400344029103c060b00b02e00f0050a0850410017404001d022580c030060f070510600780c040e40003400d6030000b00700302c001c90464082c1120524480e0b503d40000820194418010580004801980020307460707407140000746400d501d0b4440ca00800c0320312004d50042e960031801c0071142c1d0f13101035144041c07002d084 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 857944919 1250 857943669 857943673
    0x1060b1905040303091806030b0f040c050102070806011e080f0606130e1009060e0109150c0e130510050d06090308010e071403090f160303030c051e070302010b0a06020f 74
    0x261041003100c41d4862408010b000c50100803051003114142d001c48410440903200016919489840383d0300e80c114225003860320324040078104810080c5442420b00142000c0c00200300c1d550600b02d19689440301400740544c040014034404102e41c1031102d50000804050042c0c1d054002482d0001c0d407140b800300d07a080d000e071825030401c0001c85003a205094800e0030701d1001d4031140440d040c074400a030030301d100140d030010b0711a6400107404034280b0174236000b18401c0c400d03251858905010042641c0d0031001c0031083c00348650b24102c2640b030324544004120b803000c00010325540c03900200b1418003100e8101c6a04903101c240f0307000030007445502004d00580241c039034040f2aa41d421401090382c3d8111080c01c0010604140058078a600201650300982c002d000d550585800c1c0d8102450000062100d0105c2407091104009140c3c1600c966040c1c20420310b05285013480140c02c02010514860b1202540500000c50006041c801c0d40250203a140003031448200c2d6664160003566008624084074040c = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 857946169 1250 857944919 857944957
    0x1309030801031e03050a030c0309051b180c0a140f0f030109140622110d02070c06030203060f06070f06090b010603140f0601030c14040602030307031a01020a110604050301060b 77
    0x3c000000b074102c030180e45503550901e80300100104802a100c800c450009160302c5a41e4100080d6051003043e0001401c40420b40300b0072400b42c00c0120030200348040400c00b903189810701040a40c04000c8034156940360400c01b038005042c0303040c82c8051107103d51500141c1e00105c3d10040c6d40ca000402036048507540340c070500c022011110b0034a0150340590b2860362200c024846800c00404200c4010840c00750080002144011048425040d500100540594a0380001e4800c100001510a40c001c0c040324901107046142c003030b000c285010f80e155034140c42000046050000c11081c2102c1d9980f450b2710001c1448040e00520300041300800a00425001c24104400c10704408101c1f15094231070a80c001003401c1e40d8031600019001462a004540304102d4451700ea11020b504500040000785515402142d8078509080000c0c00c40c3e414462a031095280c1c800055801d07a03002904e413130000d8001c3c030b580d03017408184000144284595031195406500b404400900014813034003030401c0004645840083d = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 857947419 1250 857946169 857946203
    0x7020a03030f0221270d021311070f0507080f060105040504170d0b12010207080d05090a0807030801030b070908031206032508010f0501050d11060d0516020d03020a050414130903080103 81
    0x1900446045c4260070820b41401600507242164004010b4440d200300010030708422001c854503980003103010745800507951101c20410108010360402002c886015225070034003155003980384c150601c1490322554441011500340310342610f036004505440162940c0c0c4820041d40f6101500060044910841c10314481020030b0f20103008075a41d1503400300e6481d01c0d25101584140092801404210070351044c0844540003a0380c0000502006020f9210003805603d0b42c5050345d160351004000d8030030402c060104002115001040c1c850142140320304225036030722000442c2c40d003003650b012542c900d41c2c503025885214480621003415240303410000c1c000c0c400070415110a0b16000c5c41010381280c10580c41d000890740c440542c1e040760fa0300030a6903103041c0c805d05c490f10648a043d14410029401000d080e907207141c0400c003000d40d0001310305066091000c0c2d100050220701540c481c04c5440c80c0301e80d64200340b66481d03c848891001060700f082128080b1303803d0040c04800240011241b410070a544950 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 857948669 1250 857947419 857947477
    0x3030f0f0806150f211815060d2409030905030c03190c09140a0e010506030c0d050723011d100507020418200607020a03030f0221 57
    0x4880c40c2d015051401d0400300015080050b8031940301141c410405006071084c1e41e1a6032100102c500d2034024008a0b03081c0381e00c5050750011a008400c0c0c03942d100c10000485044490b0340c130f50340500210f56403c0c3e40c4d40c050900344445050305580c102caaa01403982ca40c0c000c40c090f0f00101045000b0b80d070b035404040c1c0b01e10926541c1c0c1c010100c0c0651540c01003214075020604d5000a0204a2003416000929a660030b5490150b40128070481c1c802c002c46410080b082503c0e20a000c071503401030f0000c0c40941000360110352a0314003025000d002c0e000c20359090040c002c0c1000180010324010031044000c2e076002c101e4408c6203da20a502e800505034112500750301400c0980170b82fa400300102100218505c1ea101524035600c40c10080b88c006456031092030f15981d6066003044001c7c05251004203278049070354405200e401c0100c81901c0383d082400302e0409616010601d0044d642e050405001c10f40d0684400d82c54102e0443c4001c2c0c1c5051503000d905c00b10b81003040601f40e500b2074148100711400b03007205151 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 857949919 1250 857948669 857948671
    0x613050f09011832030f1209060402130213030516030614090d050a030603051b010216030f0210110601031b0f060806040903140c031b010212010902070302150103030f0f08 75
    0x38010000003400c92510310003003020f640c80c10000249001d0000c41210313090341190011710a14848070707404200305a4001001c1160f030390118003400600b00303a00e02540058104511074042c00c00390b50b408212008100e01101840015503000400c075240521001c1485003500b41e5408211210780c1800261940002001e281c64020b0020740301070000d80c61241401c5076203411a158060400d6184c82000001c11307000e10120a0705c07440e182c9080d2603204140006490449040c60100701e02c81014410004514802c14507011540c0c100d0b12400b0f0540c3c1c0c40d000f19548101440d6561a50207000000400c00c80c45006540d14050000c90314100250740e138002c00e10703151441c07103000f011a2004c00026950f2421f07901180106219041c4024280341002c8001e27219000380305030b01c415620014001039140c1c11a0700c8035134003042080080d85050703000c142143d901c1e0412b03c210000140c02049130f0080600074042c28070040341c42c4c02078600c81d40c1c0d0b0f4200104100da5042507000420441c2e64807400580c0302d040f0031 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 857951169 1250 857949919 857949923
    0x270712020406080307350f070314040f0b0c010212010807060311130501030e12030a020a11071202011b0f0c03060b010206220212010612140c1302030613050f090118 72
    0x71654000118500b040d1b00305280000155454485840d5030300003500c0d00c080c0002d4040b0b2a05507859141a01d8081c281d41950841d0034841c0c5400e210401400384c0703042d202c1081c0d07960400202d4071040042921400790180c105107241103840c540c00401d0851b4005800411521217a8080c41400310303040c041d40c014412040e01c00d00051003031405104550113500500c0c00030070300000b01c98000d204440c1e00102600190b8544108540004168960700e900410950700d0300c41c40c03009070505518280c005840300f50200300007414400751011031034200c0d81c14485960000e0300703c0c211780108001850320315021055804120303a0039107403000b100c6480d4800a115441180c482802001a400290681d030b03640440e40000c99009503861001ca120350301c2030040c200100418401c1c9540c06000746040b02010501c001079171020340c803075402040d1990711200000441c00c04000c0c0140c1c2d82d00c0d12000700c2c1d40780f404081c542940e41d0400c0240410407403d500d0052103603c0a00c020803800f40c80352900e180d8002c01c4180 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 857952419 1250 857951169 857951183
    0x30221010f0b25031d0f030a030f11010e070603060e0405122209060e0106110c210613020a090b0a0905130b090a030801090b09270712020406080307 65
    0x1061014400d02c800038a00d510704036070070180b0094014541d0000368200c1008600246085129a000442e0040e0500401c20304030380c0c040c00070b08000302003aa1069504809400c02c080ba005e078002d0f150141c1e1200c580040200b009011066490a09a50b134000504c240f0000914040c030026a940c0c1e240f40090080b80e101d006440000c3d800f0b0441082c1c2d420504442c5081d10100c42140c10320540c42007454001e2003503a0010928518100e81d45d5901141607001d6814011072302e100308202078000c039209000480460307022140c0760b1366441c1c29131000c7d500101000c072032260600b485100003015020f004c24520031a500446241c42e0410a0141c4481550340390b0040c00c244003c0c0100d004c250021503200d07500c00c058009a042c1501d990784541c0d019101071049411041c04042810303070100b406405011501c40c240f0150b0002c5001c90015100113003803a8040f0b90384c031401a00921040b10305250195140100c4e11500d843c0c00454040381203840040344141e14154000802c501c000c0159680300b500584 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 857953669 1250 857952419 857952449
    0x607110c06091e04020405040608010b040e030f040e090a080c011506030608120f0c0303010e040b0709030b06060d110406020102270f09090709050112110102060402091611060703022101 81
    0x5000f914010364500d11a801502840085800d0311944281c10041607024008201070380141c040c001252440901a56150410042003c110007080c08840469105c45146080c41da120b02c0110704144400c10f0050a000c00061400444441500706803007000c40002c1c401107007542c4141c150100ea001f481041001d40001064000992004000d0807200d420b030855030b80b4100e4441106401c1d0790098008292902104040c0030034028030300795065003c010707418030b411000d045495003d4480c0b002000700c0d201d840c0c009114101c04009810800746080c00c1710856468544030a4064080d4025401d0070b8140c05001c800000804070780e0003400c1000c40082e1080030004e13107103418014050f000070800d107210f125000300001c003000c075840748030300812554410303848041d40c42c501030a207290728401e6141154411010700025980d160411a04400020340d0410004c1260100b42c460b504e080c4122039540c068007042114103070f05500100034413680031502c0340300c1d20141013800c40036480a005d21030304003030441 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 857954919 1250 857953669 857953699
    0x180f0302030f0d0f0b0f01021e030c03040602070f060305090c040207030302130608011d010b0901081e090105010905060303072001021908120c0a0504150309060c09080c0a0303050d15080607110c0609 87
    0x400c0038410b00d0844410341345000c00bc1020340b440c69210342d011400680c0034038010014510b1904090b405030000b45014012801c0a0404d20f650b0b03948140031900c101d6001501c90100740c00380d070486982c1d0502c8600800c00345d039603106c081c00101c400d02c100002d50f82e0103240e8044030030420b10a07a06a4188801d52418004010011136840700001d00300000040404000d8150b01d000b056424410b50910001203450740c14001904241c2c0d202911690180d802401141c0010f0080b154115a01d05815041c2501340700c2440100d180c0040c4144015840e20406840ba050101a2000300b00724540036030408410348442514600c28440d015a9100045061000b0310085c2842080b40440381003e21300400d2550450321108126100c425003100498040682004903c1040c01030402c1144c046982101c00c03460740c3c50180c082e01c01c200d0106809503071004480e090383c030341c00411006012032000312210347c07605540140c0b540f286040c2c402d2551158603a803d082d45009012111345036805450841c20304912 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 857956169 1250 857954919 857954953
    0x1d0102070c0e040c0308180a0f211b0305070e070c020108070c0615090b130203071407020d05011409071e06031e0509011d01180f0302030f0d0f0b0f0102 67
    0xb401c22241d08140130000004100070724080c03c102003902d03140c0e06142c540e007010007911600c0c41c0d0220940031104603007080304007007104551044103030100e0003030788000b140e1a010f0b81c3d008241d9442d00420048160200034020001223031016a202c0d101000616101d010007601ca00c2c001c884024006a5000000b0306e040d88600009030760584100000326000d2005035032400015520f4200900e56503885a54120328030300000440c21088000c0070840c91800c201c040140110941c0004008101c5e0010704007085465141801000c20f030402e00802410588840c031602d58038060340c81d458030f40300d904004501e801c6002881000c4801c010402c00c0f596280071004d402825001c4100e451404110080c0003961b9440c3c041c481c444d802440000035802c0c034031542240c0d00d46a0030700c4600d80d40c1c0b41c4120809041381d9a01c8050b262601710003054450411440c00328554032400c18403001c014008120880c100700c564102d00d403000e651030400e200020004c8140004215610000d5005902910480c0314100c44 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 857957419 1250 857956169 857956171
    0x170a1b0f0210110a0c031e08060f010c0c120c0b030112020a1406040e090102160b1006020105060306040618080f03060a091b0806030a050a051612051b041e1d0102070c0e 74
    0x1084c24008030090880347c0014200800300300c40d10206440c0c03820070103286000304042a100200342050481401c5540300c0c1407006032503002e92000590555120824003000c80300800043c01d00100040da42d41e1140c5028041040c0c510080740912800703000400c002c02052084200c940014042500b0640350103e40118802c01404a45055508020007652000c002b100480194001e031024001802d2484101503400426400f01045909d070405101c0d007550040341e119001604440040f451800c480c2e445044900b004800a108880020f95a4005c41c044030145105d42c07001c540609005d03543d55016801c1d102c140c1484c1e00042e198041444041380100c0c070303458114a0103012500340c010280e94961401450b0340c1e040e25940c0c0558804c6003041c0c0204001e070054406400711040b102c0d4550b840e2556800c40c2144849840303030150041101e512507500020f524801c01100314034820700c2d480050010000c4240d071621a0f03101c8008128014014000c44040a61286021210503d841d046400744a0 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 857958669 1250 857957419 857957423
    0x40209070309060203070306030302100b031506041104301a0c04090603060213080718020307030b0619030515010e090405030f22050907170a1b0f0210110a0c 69
    0x5941e0b01408040703400c40c406584140040e0700c00181e581c4c29410068504401804602034040c189803d030702143c0c8002c00c2103010000d00300114101a00c0d00d40c0000c010304a03060b00d25001e00c1d0082800606501c5104a116414688000c0c00c0c1c20301d0447c0410041c105005800500500407803420341e45000c40300e01201e5031058070480c1540c1003d4a0300c807070100f980c60641c0159006d540100d00410b910b9101b06800c001000c110009101c0d0f14541a1815a02e00c03a120b054a0020790100016144a0283d00b0801c200d44008140640d92030410500c0c1031307030303030604c5075070b400000d14080c00a01c1d0042c2d00c0715004c2490314161100280c0c10b960b0400c10a44400061040300c8a00050229854044040c00640403040c803100100c1281b03096040410b02801c5541e000c41c2c8a00d0108007807241c46500000404e814001a15551509645212034980074010100000304079410b6030b00f015510f598450f81031b94101107150b0076035100ca01924070507000d41d8264100940d00c014104840150f540c060301d16050980c0c = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 857959919 1250 857958669 857958671
    0x905130b120a23120f120117010e12040b0703090506040b0c06070318060b0301140130021e011701080102041a1315090e100e0601170402090703 63
    0x1003099000c95180c50160211900c90780c08410208100300d0641d100598101c4400102c0000300106990700303035940c0c105401e1001c150400204440c2c454035840444403205010a500328141d69604400030508221402c40ca07140e503c0d100d20f59054581c0440da02d45200201c03e0b02d541043e08109160380c55030712900044040c0f10724103c00061a407100c1d0060402030008040903a114502a174050341889402840f043c10540b030004d901d00800c0714595803480e07007034200e4800a40310303081101107801013441111400c00c4200010001860f268042c070b0540c14094551307d060424501e018100390392002241c070003507004619420b141700e8040245405030a1540514211042011004810411500a8002c088681d4001400788400d00d40550741b18026001c48035510b00d0003410b0503d038440051680600300c561038540d03401581d444d2141001074043c00b0703a443d008000d824540030010032841d0074442d405019650350002034140d0700520000ca40340b41088030394102e40d5196401c1008081c0c00418400c145 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 857961169 1250 857959919 857959931
    0x130209060d051b0f0a0b030c030c0d0911040f090b04021320070203060606071a27010209180f18010f0f02030604050f09070e060f0927060106090513 65
    0x202d1400c0020400c454142c4140c00300c20282d00c4140440003040400c01c500400124104018030b2450b541144c0e40005024000750304d035140c42c188140e491041200b0501c096042a03580350a0140d04001603070869400c031810008840c0c11900e0340706540d410a0003618034844000001c0141c20036196501d00c80100000004000c00c0800003140e00038031400901c45c5142c40440c2e02401c600b010002c80d034018104485250900c031066403080308245101a44107481501c00010581c028600602e00ba608081c000c8440011350340401c0c4103000f03400c418170044c4540600e0b00c491020020170700d611801641000390103131740c55449000f09544150011424803096603916012091076005204000252901b40005a03403800c00c0b804100c00c1c3c407405400d000341c10800340e081c0304091000003100700885404026030501075880300006200700c1441062143c00001c00d80070040507008054011014a44410829020306400c888460765103009001c0c11005c02c070142404c3c40319290421031b10300184654003001c030310 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 857962419 1250 857961169 857961173
    0x12082418060f1915080c07030e0d05060c120a020a0215070e0603070906300f0906140123010e010e1f030f0c1b0303180b040809040f0203130209060d 65
    0x34a800600f041040820505070074842c1c43d0542d004851280e4007441c00070041d041c0001102007030310030300c50020305005401c1e8000865450341c07410018000c0d0841c0070745801d86011811050107504c00c01c1c5401c1e01340c0c140f03c0000c00211151090381c40c0d80300349500400c0080c803d0500b0300038507a409810348003480f064a000c000f15941d17150085102d0015035441400c1d007460306001070710501403421070300004a02241c1312122600803800480c40101c1032200400c2d60f28207804650020280a00c0c080c0c0b005c1d060594200e241100c0002084c101c845420711442c941c0e403c1291100e242c15041e2416000510313003281345003590311400c40d00662000081148000706500c050500d90344145a0095010030b45940140490752558454040d0109450401408408007034800440725070ac500c200805141c0d03a0b0400c5040c0060221a1703034140c030340c41030f45d5a1140c101b40c1407411080d040190f0300380c03050742007e2205000c90802c0c000d0f28040c2280d00caa0744004a410781c00c01070b00410003040e45410034034250302140 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 857963669 1250 857962419 857962429
    0x5070305010e011e0b0127120f0203060f0709050f040b030102070f11010509090a0522210c050d0f0203091305160203030103080f0c010912082418060f 66
    0x1103a00b000c100005076a041d00407120f100b8507021903400d420b20f2500b0700da10140d03604840c00d084802288600740a00800003501d0f40160407458002079040003204a40c141000302d504440b0070260b00071402c4a60030368841d500540a0401120180001000f00c60100694103004c246c6400c0c202c4000c01c082400720300000400d0898102100036a10f06545000c030409120246401c500700007001c5c80c180c1d18084403040031802d0840003500d03c00c00746503201d0000780c900c444040b000548000c042e035420302900b4107007052060b075402081d41c015061006200000914000d0740b0030a025a8401d0240c03a80c1c0d521030209aa07503d40b150482e205500040100480603a03923340030b00000021224001801d007000203450729010040911001958010001440440d1460054a04d08503a1014066454080d0440f81d405403060020043c828074001c0d0303407090f00e0343d0030000852254005514801050b900020150544d80440d619160481d04c0c4004024103034004800d503950010300505000c400080c03050100d4 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 857964919 1250 857963669 857963681
    0x6020703020a24060b2b06080a0305030702070801023406050a0c1d03070302280e180d0503160c0c0303050a11061018150807050301060f1409040507030501 68
    0x401c04200016024909209900c9401c010380007000c03a0505000c400c0306184400c103d0341c1d490610340061b1030040f200c0c1002c3c58100344080e007010300544140c0c900703d02c0d024060340c1090f202c0ea00503002d5840041580001482524260a042d444003980390440406402e94a01308580e0402d09038a007080d0103002c90054051240514441380002860082a04005020310022048000c0e13200c00002d030544a0747c0e0019030001501e4040711345642060140500000400c10074001c40030001000e500015414080800345214000e80e20245400c03030324403041c0540303900341039904402040e0b05201103884040d100303103588251507860034240407500c010348585507a10841d9104030005480095018519075020030414401c401100c000c08203400c0a001c480018455130094082c0852100a128164107460300b1040d0040e40c5801c0c04400c02d521100041e841d0621806802e02a43c240303000041c40c0404840c89404450051079209080b038644020080940d0001d0401d88981c807074140f020000c01e400f8410700c = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 857966169 1250 857964919 857964953
    0xc050a080a0e0306270304030804031712071d0303031303050f0d0f0207033504080f130302030705060c030f030402010c1a100f03030c0f0606080d0509030609070f0306020703020a 78
    0x5411800c0030840f0501c0104213005061546c1080c0401c10000d2001c00070b45050340e50103080860311201501c0b016400e80110700e0456480040102030020494014441c4451380041c0710003402140d00510601d9a02c2c801074501c1a2050301d64481800031904c07030005810703d141782e4241ca42c81c0c00c66449404d01500e08244840c00115030000b40301e020150496008080082c07854a41c016440e104000040e403503010582ca80b03145560400090f040000b028115003140007940031003a03c80d403501c0c00c0c0042e42491400124000e00caa00008039603858540c050307a41101d1010021450705a4540808410380c1014000b203040c000308411500004451301c90180c2c40c4041c01d1800380880c6402c0000b61b140d199a5070140c1c400350343c0d4040c1480440c0d4030000c1102e4440e04010214142c44061805c080200700c182c0c8141074a00954090482c800c0c1e004004020350712080301107800f0750b12000f1141d40c40d00d240d40320f5503803070380c03440001000000c0c0641c000c0d02c0580d0090054404400e03140d1070b40181c4240100b04 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 857967419 1250 857966169 857966191
    0x809010e030a17011e0303030905031201080c0a14212b0f05090109120320100e070509070f030f0203010b0c1e1b0f0d120f0c050a080a0e0306 62
    0x100d5050f550107400524018060203400d00c1c4080316210f5105101c010502001d4101615100e820f01030101c100b0484c0d00c02c1c18914411126980d68002040d00c90701c1c0113204510680361008009041d840358880640ea00000810022014080b281c0703500350803421034480c000c41d0044680d1000c3d8280d104059140e01001070b11401e04000c5032800c003c0c80070700d03c1c45181081c0034061000e0351840c0d9200d2200c0b8142d6401d407000e280c81c504079050540f04012011501c00300d001600304840d200c014007140017078031079800042c00d206400c0001d6001c2c0d01e5401502503e90400303510000200c000e4424510a030704101c3c2405c0c001020b100306208a01640e009030000c0ba11104c0005202601c1942040707501a080010501281600c00c0f114880c1d0b1207010817202c3c007029109010038000d0f1651603805120b038090008142c003000c14079602c0c1c448508803000040d4000710700007100c54144a80111600380110780e20038090a1090940c0d83d80c404603422000d40c150402151035841001030710104895401100c981007 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 857968669 1250 857967419 857967437
    0x3080405060c0703020d030c050705100c0e041b0e060f0c0a0209252007030c061b030912080d0e06090115050f060c01090b0420011403070809010e030a 66
    0xc0c02031a00c0006090800040020007010003c00d901140b100209072072850040f400c06401034003254a1300070f9080280c0140550500c4092030b01c1698000302c0600c2181e12007103001700044080208440030031f51004035010b02400e2241000e0301c18501c400c14107800a1081e400e24102d010064801e80200581c021070307900401c050f909501c2c0c8910070303a5012000004000c034034400d00c00c1083d0b9441d04000e0704000e20a580c92140c0d9880c100100c0c802801102a0841d8082d60740e90030540c0c200700541c071521021501c0302a091808581207000a141d0030f030543c586001d4585801500f070600c2000410585044100b80499036000090b400f901c11407055189c000c000d02d05102d80c201c0e00b128000841d00700844202c2808100765152009610380e0003000319201e5841d0f000c100303c0c0714058116224010041200807081004000240074411090840c1d02d40c0c00e00e02e038001c640152818241e010500c600050107000081100d80705225003035206041e0310020442450302d600d40d40c03940d04400b4600e004118592 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 857969919 1250 857968669 857968673
    0x309191e0e0c07030e01030c120e0304090c020a020d030c1104020c030901030b09061e0406170a05070504050f2a16140a020901051201021e192307060612030804 70
    0x94182504414148500b81c90a09580c2e40904000460100380e81490f80f66410340b0303019405150507090425554905020840741e030300c0010340300d030b225005071141e0514201c1c0008040d0301c002030000e011a80900000d0110303200751400c1e59170094900e012107a071a02004040400c3d00c507800602032500d5050015501d40302c25000150540700701c810307c1070280f40460108546c9940382c0700c041c022015640c844403040a200f401103406025550001d0304510801400d07444078180000300d00c0c04513401075090f60b40c00d03030301c40301004156a02a52001c08154407440451886080101c140703541c000b045d5400d1030508144c010040300c0d40c0208a6492507004039014050500204102007124002028050003001e0030542c0012080003060041034050711a1181c0f030540300b10250304850841040c6040d0000200c0e031020f40340c030700d90b0050450b111800541c11907070054600540100c1101b1880c2511a2441c98080c19481c05a8000c0347c0141e500c2030b06c1d414009002e06020040d0381c40301e8001c0d6241400c9103894 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 857971169 1250 857969919 857969939
    0x11070308070c03021e0307050409080d02070b012d1a121009060e090303070503060102101b0f110a1212020f030109060807031119031b03060b030d020309191e 69
    0x2210010340e1407403000405c0b01d082e9501155940c203840b03044900244802c120704200d4800c0c02800c0340d98085502c001140d106200090140d82c2c100e85e00d0390b01501d106100d8000c0b80e26182c8010118141c0351910100a0085040c4440c08407200b50f441e181050508000c070702820301c07528040d18440c4e045242000b0a0080050300d00075207006c0c104007141d80c0c039107050071103800b0f56034440100010304019010020840c503a100b44070385000c10b802d01c641032000005003403000807410070009034071000c01d00440810440d54041c1d000300300601c0802010301480507594550014203a121183c40041101c13488425460b5200c1b807000c2c0c410f101c60b541c503031520380d03041c502079100310b4540e0740029810b0380c00800100001014403070f00740101007041c0ca07040f840c1039007504105140300707032a0401042c2d0140441044200042400d2034403c40c3d0048205011500300a42803648840008003c400180c008201d6a40c090800940540d554458007001ca08070030f94540e111130041c0c610307440754181c080300400100074985031 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 857972419 1250 857971169 857971189
    0x60e03250b04030c05090c070b0a051e240f03030403020607020f06120703230f0402120d020703020a1208071506170607020c22051909050d1101020901052709090a0524010611070308070c0302 83
    0x37080c0c40d01b020400581c0002917685c091484000e1040c0d1001660400f1511004d02c2e00030b0101001c5c1009407584500824202000021245000040e16144807080c2004004508039245143d08000c8501c648801d00d80d40304c041c20040080c0c0c5c101785680101e8916100410140c4600c480c10703405032104a003140b04010120300c407036000340c1e03420340e0340c8240704042172042c0121071034a43d10103c4030340b4844c2d044402d0703000b4118542c060300c0c0e4581541c18103220110041039107440740c4c03411341c02d44004c0c1102e90200044107090300c14507080b83ca00c58800541d5541154840ca4001c403400031515002c20214224505580010300300b03d03000d800040b0541c7c0d0250308040c620060745480402541001031745030009150780030300301d9803264040b00c81484810081c20a0017001c00e440020b0218401841d040d0034886e660200620211550b00c0749400d0100c51072600c203542540e50000c0b1380d4441a80e40f070700350115081c50395440100c00c140900900000042d240400512000b849041405070f03251460040000c0704803 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 857973669 1250 857972419 857972491
    0x180b1c030e090408091903020d0602041706011a090a050405070f090902090609010c1a0c04170105090316020a080f16060e03250b04030c05090c070b0a051e 68
    0x101c80c1c1800002503003203059403540341c2d099078246c1c0f14483c04068034a4004040d4400703034000c1d450500640600000c4c0d0014401c1d0380149600100f504906645144c0e00c503024460319003071460590660402d13982800060039400700040000e040d40d601c0300c0c001012100f013501d241c804075035154408a003039a0414056401004003240c1141402c4081001c00c02070310805040c2d50410032400e0030755007003000c1c425203040d01110f1810b00c041540b4004107144501e80c410b0190914250910b488074101c4d503014015030748128070010186081c00400c0554035080c085d50041242d00001c85400419101000c214056000b402d10300100005852400500b03120f00180d00000100000002203078480d80b400540350541810b440f5854105406550440c5140b42e81d0340c0101c0c56100c0002400028042d0082c1034005584c0f0449108006854140101100d482000c0004010180410001c0c1b1444110342c0324662200d042e034480703c100071000d0811800220200c4102c0d035500070700311602d00c210f00c42c6441101d00b11 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 857974919 1250 857973669 857973679
    0x4050c070c180b1f0f03020c030c0109050c0a0b04140f15120703050105060a141b0c1009060c0b070909181a0702030d0f0b040c2a0b01180b1c030e 64
    0x4001d103404c802444101032a90001e00c12071964075030186102e9030440c0c00e915002001e42c0e40351842000750314042c1075800c50646540c81602c00e41800c0d0714240b48120308552540e9001c070b03d01803912600000f05100c9c441150360045507482071210603102d900346180888410031070a0f6494a05024407245c6e0140507040f40209880c0c04014095070f00c0700f10031140c0d09051401e0a0989840302d05031500c00384a5003e01400c40d08801c000004080c00004002c040200b01f01c0d01e01c800b1910740c48044800310703d184035040010b0319003501030020034a24207283e17410208a01d002d541d183c0d247d4000c2003e03202607820f001801c0d0250401c21007401002c0710807040305d842e00000340c0414144544001d50300c0c0034500c22840c05c0ca03a2221a15410756999100d060180300103441404919101e0781c014142e0201416119150042c240601d5583d5907685c2c40e880c04164045400c0103542d003041e2038403054039441401c0a003030300d44d5040c2c8a407060399200865503000303c142010794125800c9180060452409207a903074016 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 857976169 1250 857974919 857974939
    0x1d04170a050403060f0e16080f03090102121b0613060c231b070303050310080a030c0b0408070204060b2a03070b0603030403121205060d020901030204050c070c180b 72
    0x10550200490b0101c80d04a0008550160788402c0e00004144d016040c11492154032011851065803a6854048490140c2607560000b0b180f0030403503da2140d41003142c0160003003040b01c08070107000c41c040e041200071840040713845100d8002c1c8500d0110181c0e155088a0144008042044540c0c0102ca410304558a846484516191360503914040c41c40c003004441e031004104080940c1411341d240548a030070000b01c0d00c00c1e42c0c0d41d050180c0680d00584d0450300d90b40b00302401148003480014141d03480348e41951044080801521106251031000d00111452a01045000056500e078055880030b00300d100d0041c0e41d100380f143c48100b00217050140401c040c6002c600102c2728840080103403034a264102c15143e002d9a9401d0009041d8450b030b8000501d2900048480340720a5444584518054904a000c00c07594607500b04000d039641900700020b604c80c1c0351100600c01400e042e0400b03500032b003154016605150090303441c03803007441203a0012030040000b220255094109030065000e4004252190010 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 857977419 1250 857976169 857976187
    0x302071202010c140313050312041a0403020c04050c0d420306020d020c030d020a0801050f210f031206100c0f030518100e0102060906010f060e0a1d0417 67
    0x404c035100316110b10610b2000c0005404101c2a94000c203100d0743c00802d0f80e90341c01440e50b601c05445416282526600c0b1585240c00c000b040007501075004a030180c0007030071181f40c4202040042c041c0142802e00c9031100340039084100f42c1e2030007080d0a2080c041031161903035020b18040d009070010070a41c80080d810b14207400c030700128400075280580390032038009030b81c40192042d4a8081d104814411600784800a00e411900b8100c0d07010300b10080f802d03070703850001d666198208a003006c044a0b41551010500082c0d0b450803409006000114241d8030540303181c1982d0100700e1b03007160080d12240c855045102c04101d00e52078040e00c600700c2d081050038004518003003a00c0740003603000d104000505105000910701e00d652100315003d204840002c0107400b900101e0b820007080f0141031001d0714054032a610200c4c41080e070215560341650316514602c00304600e0004115106a80d8042182e005000c0310030100314001000c5121148030071304510a585814580f400544491011507807580c032100500608003 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 857978669 1250 857977419 857977427
    0x706182909061308090324010e060a05090705130e070518040507020a021504090612051504030e011d120d0807020a05120a180315180c0b030705190302071202010c 71
    0x3c4a9400c01d249039107424804012a18004440c102002e42c000310204403c00f152446110794103030b4070358521000785038a843c03007400354241c403501880790b004403a00d0001e840d035886940039000c1c066078403888600176940c9040402035a8002d0740ea900005e4400109000ba605000050071034407141030f41d0800840c6040304000303480ea42c154400a21586240070345241103000d080c107560103400320b03641c01c0103541d6075044d0080c5100341c0c1141c1111140988044180c0519409292034459601a110a0a2131580320b0045880c0c400042c2d2030f01c00349075040c05c41c18080d2590542c8601c0769190034003d08201ca075150f0040d041580041424085500400c04100001e2020803280041215244c0080e150000c9190a64070520310380080c1d41c2e00300402c1400000c0c40240c40c0c80e02c00200b03ca20b0100148000f520305840c05002400c000f4000c10301c0c02c1c03800c2280d08840700065501003003030700c1e02d28206022040300147c0042e4031000750001940200b0004240b00d0060f2840c9030700c1d800703030000304260070303207044090 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 857979919 1250 857978669 857978701
    0x902130f020a23070837080618150301020d0504060506041b050403032f0106050f190512010207050d02010c0801050d21050c0f100608030f070618290906 67
    0x1000c1e102c0c04070300038802030041090b81d099141d003843e46c00780c516400012016810100d0058000203560301011411f581840d0314601007001c0a96412603141d03480e01c1c0880d003a010342c2c400160309990b081180c8858540c8074425180141d00c50700380801c56090000030441915021401e01c1d00d01c20040410100361608241101c084075818101484202400d4021315004960217540300440040c01e404511600c0c0103610000544508481c0010640d0900d000d2081914040b60010405403030603409108a2815800114080054000142c034028a56403041d00f4000031b405020050703919069030011642d08203c1c40e6000d00025540c2885281580e110041e91072062070000d007c0800c08040451a90300c100100c840a5480703000302ca0b0403001c0c01020a9803502c06400b5107844501c0c2003400324000001008440410811152503828410350344c94140c0205480420b40080001244214000400303041008803e980351801d004c510300e2a0024003050280700608501540d0811820800d1701c0f05400019 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 857981169 1250 857979919 857979923
    0x10915060f0648060c020d140309030717041a1207030911040221010504020a0503280f331e18020a0906081302040902130f020a2307 58
    0x2488080c49070b4001d10038801c01c4a22079480d603051420f68404042c00300b076100c1c0070030321480c0104800070645404a0315010444110f10000324a203001120003083c44001d5a04030785a80e00307803403901610390b0300c8441507950305084002c050f01c045020030492251121a50018565000312031404000d0396030030f00b4002000307069a080c123985200a00a10401640d40d05078500c004c0c000715070b030703084119655012803003070310403038120034a000000302e080e0400780262241d9024507150070341580c030780b20000580141c0e13000c90940f800c4038207144034821307400d14000d8041c0b178002004002a491220150108264032851500360390750681c485071001c0c48200c070140c0049440800700b42e0707051602c5580512080c21071f071f40701100610921186204441c12039000f0142c10f0310070307250224459031b1403070144e44481049411092000718090f041015050540140b040c86100508a01c04058a0024401221a10342d08142481d90115414000c01e81010780030042c504003551098101c042d5103068012032040e4900 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 857982419 1250 857981169 857981207
    0xa03050306040e1c091502070e010b22090204051e0a060806011206080c03210406050901030e03070b0a050105180a0f150605030702100606020319020708010915060f06 73
    0x18081d0000d801d2064072100009210004e40030303c1800c0006051280c140a802900e4100c410940d411031300010b0094210760a603c5041001d038039000c00c0701d1168018103072180c00380d01007081c1c00360050120b00440300503246c44000142c481c2d00f03040c244903403004501002024000c0602103403800750744191540c412600d551030800d000d41e50706401242c081560030502002c4a00b07100e070215404002061007100a8400d03000c4406404070981c0e00201c1c061102000d0450000410080c8503040c415401000521810b04000c45d0381c11100b5000740c80d55211940560304292410107000d151030560090f9401008100c0320080540c0424540d2804140c02501c00c0040940d62006450780e0b110381d40102c100060717008502c04038030b952038030094111791003158800018015043c440c0352914141c0b0584041d520264021030600b00c00c003824000300c0081c00100c4080d0320072420000750a440c00d000d2101000e00c10403d000300301804101d000c003900c0b907c0e006040c1000021505025a5038414000c0802104c8940 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 857983669 1250 857982419 857982431
    0x403150506060d09210e0109030609050a0b0a1e02090307050103090f06021603021501032102120301090603020a05060c0d080a0e03030406090308130804122a0608090a0305030604 78
    0x2400921614000701d202d0340c18141c041c0c0901c002120022041460b103401d940900002c0d80d41146c010341068515404201d04010038008200c0316844000c00ca4410411a16030189544454a1102d002c50701d40d0115600c1c1c0c92442001c21450900b4817440c0c0c04040c007541803590041c0080c3d00c5007154001d29040503030341d4047c1c500740b20110340350071000c40e00407104641d0313058002140030381c42c2c0300e00720203030054402c401e107200081400003490380c1205e401c044444101100707013401c03454041ca06d0000104610400b1001c20400e00960300560082c05002c01c00031381d2a1851042c0f14a07140d81303502140c440c04060098205c0020040395140441c58145480b6809984485200d001842e500d880c89000384008820803082001d15485070030440e009440b600c80c16503400c0843c1c540c0c04803c02006040d604148020000000039044001e2150b111380011550985d4418100308410280c00586540340c1c4034400802005401c15591604001c806003e0001400c0a4501600900c400307030400303018039030700e40c = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 857984919 1250 857983669 857983681
    0x90501092f1e0f0a1d1e0f071206060801050a0503031c20131706060d15060801050f06010801060f05180d151b0509090402040513080705010f050a0204031505 69
    0xf4901c50355484004200d10010f0740ca80750f410b150b591408025090070006203003c00c50395400758038421228990742403030810a40d18050401c2c206031015220340140f04260607581c1028155014080c06070a07940d075408000d6141400b04440d03101300740d000b50b0080d001000f01041560006684900c0a441002e0214180321a41000c0502c646480807214000b40d020952000200070401d240e000c441e9a412101243c07140440d1445e20381c00141c2d06140e100340d427440c1d6003000640390f04004541020341c80002a400b44c0e5200010b080d1081110b00000c000848420401150380150885024180914050b96081d52003040a8410f11803862040111300741205a10400e0b070302d4407010080103a01007620020049581d0841000d02024100d80141140103020500b0580c8a00309503054024000c0902c10740d6100c035000e10000b41409000507000034005c011502c04102c0520003000d42510810000919900304e1a48400b1910b001d030440804a004000c1000813134411042c00003140b81e0080c001400e80c03115 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 857986169 1250 857984919 857984929
    0x1008130309050604030804090605100c30030e150105030613021f05070528020402091207170f060c040b211003060501090203070c0f0303090501092f1e 66
    0x2540074a6003c100018084104011140600100c4041003003e01007103031620200956074058068060004902100b0140804c65601c020031000d40103050f1524028403d007050311540088115100102c2e450318100e00c2012010014100800c10350401010700b17504101c00039032205c8001d030418100f2614160100199620910302c80080842c20340c44048100b102440901181c000600a940901412000901403a65141d040e0030203841d800310a01040040d0342040000c0d000a290242c02682010400ea4094000c2000c1c1d00a848040c616100906922405501c0c0419461a00d5841c0d00210240244559002306450507190b00281c3e4a0f1240d10401400c80d00d000d00c0601038032044400c100f480440c0388054890020f50380951400d210507238848404600783e00c0140c60240024101201c0340380460004001c0407251842441c001c144910961191400d41e41408815501c11803030740c05144079101c1da0000d0100461281200c0300c08007000000096201100707042c10010031403400b0080c441c80d0b80d5 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 857987419 1250 857986169 857986187
    0x303020d090f1b1a0f0c0a05012c0a03030b060c1f0f0e03031f030b153d0905120312090a1203090201030f050f06010e10081303 56
    0x508408000c6000107040420000920b4601514000240000c030741000007041c20710410380d0f96050310800142110100182c050b03000400910911200b400010f504074014494604ea00d0301a40001c80c05540441100713071009d410244582d140c0403100e800944420010a0240e200c03605401d000880f030b031000c40407802c5841802d000e0219070103141040e202d9841240401031032007403095800c02c40b807488814201c044480e094030340c00c032590050002400b6404421004043e0000f07c8004c4521183e8a540b0f00308600411303a014242c0700d0030408002a107051401d8190300e008000008000402c0400310444951180c40540c55071510f220248500710780e0240d00000c0060401622a000c041c840c07038941501d1703800042c0001c20122090000c0350400b0000200707103101d140c200030800c030899011701c015001412034000882c140750f105c003101f1400c3d41040c0b003100e10802184803860103a2500340001481000008500f45c4034070715402c00102c1c41c07035000c500340d54812000d80610f012000d441c00c0039200080 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 857988669 1250 857987419 857987437
    0x605030a0216032a0515130b0f04030e06030118090204111b0f0c03030f0703030605150c12250f0219060e0f1003021b0d020d020c04060b0a0c030302 65
    0x41c0d5054200300f050391001080e040404409030714229010040e142c00e011140b80f41c8080d06a41c45003c003c00c00402c00765501c1d4000000c031400c0041c440440ea100c4840b41412620102020100c2080105150700410401450401100c40c245507605006600401510701300c1f0495070f4035520303141c0d84115100d940c8012860709035404140d4543c0c0003045241c0d4038001410003c01940907947c9445082c074400100500b0800e070040103142000540103441c0798540001000303034200350711083c000803035817141504070500c2401d03041d95079aa4011120500d141c013008401101c5092810800d294290b184480c480680c0300c480386d45c010344580e1600b0100c0e010f4050383d50195201c0590700110a540c0c0c1c04a21a86c01c43e03c80e91610110580b81c0e03420411060000902c40390800c0c041041900110312170342c001d02c030700c1540680c2540c46402c04007900c1d00e4440c2104503140540e200b044c034030940a4042002120700002100d044c0032880c20308843d90100c0c05004942c02c01e01c042d2180c0e0b2400c02d4040c1c0c0640d02d40d08 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 857989919 1250 857988669 857988697
    0x51606050109061d070503071209020a0312031b0503060609031501060507120914060c0a0b041b0f030c1e0e0c0414030627030c01020408150606130605030a02 69
    0x561142d0340900109224800e041c136894500c81c11010034503032a03c0051244039161241070841d03540e140d003602c03035611808005054a94555a101c01665215100f402440c010010341c7e841414400c0040e040703074070003903500b400881e039181a0034801c1c0e804412603a0041c810745c0d4203906c0b10001404030345070101a210392082c8040f00f50011400503804006404040d0043c04039103a0303201c600c44140e0307190345203005014101e40007807101e0100d03041a00c010541c7c82c0d9150b00311200401c190f00d802c881c8440c10340707046400034101600c946410000e880340c000544503801d0703800ca0f0f861031a81d512000026a01c00d04203000d50360520100c401140d0100300d0020032201c00b1010491402c50003030480c5901034010b8060b0103007490200074640c00c000400c07034403800c0c261818200d20b03c00c041020f00a185c2c148201041072004108012000c10203002500003000d0100003028840034100c03520040b910020302090145070140460751400c0b101501803011200103003882c503600c0e206c00b0b02e188003a1003103100c020540 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 857991169 1250 857989919 857989921
    0xa12120213090c140f1222060504140c0307091508070311010305281d100605040608060415050a02040909030c030f050c030a050906391c05160605 64
    0x1a0707910b5001415020550b6540c8001444010b0a1369854011550f0015801c403050000001d0140d80391141ca40181a1a449404055141901d844100b003100030454101c0c0d10b80042c802000200002c4012181003070016204905021011a540310071511503804059101e460f0151416400c441c9100a451034100341d826423922070400c00c10f0207510344041c50002307282c100020b40b50646c059400205014510a000c031004008103c1e40261583d43c40308280c00200940714890303407000b0450090ba08110000c00728465140c03504000c11144564005001c40d0080342c20000050030480107910f04540800e0001042d840b1021141d00030301450300807034100e078a0400714805041c0c10141070b0030002e101e80d5508028062031401242c3c640140078009202e9030050080c00301ea04c0c040c0c00984100380c4050a6141405010905070414654101005c26800b91a4012a05004d0032824800c402c0c0c1d003500040461a4441c00c19940347c21a65405c0020005e01003071491607107040e150400d48440d000b52052080b = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 857992419 1250 857991169 857991179
    0x6070206040b0a0513150e1b04050c12040f11060a050c01180206090d08090a03060209101805091317090f0103090f0201051b0a080403140a12120213 65
    0x52100d09031000d450441141c000501040b18a0048901c41d460502e00c602c0c6407042e81d590808610721205c00d40c40c01c41d0300c840c2e86044c1198200701c506500c0b4008040410400340d410240021104050800740d200902080000030f24850541c94079009548002103400c00300450420900f01c0c0d2007458103503482b505c0004c048807040e5020000e80241054a07000f0000e1410400e408480d82000d844003d4100c01d0a0140051500e0301c5540001000d0154024a180035000d0300050810030701a00308403805075002c10300300240d0503c464452201c2c446800e10342140c0c0b5207825252288a62489001d100711805000a07030008500d81321001c19541c46454560400d020041070041d03600424801e40c05003c90003030004440d8420b000701820550407402d4801000c5c01900111000c2d4801c22002080c166000d40000d501c4008208890840c0c0c005c10019490743d0862400051551420045005552088901401107070140d804201c020102e41040c0c4413008118107980081d0265030512219940b60f00c0340051 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 857993669 1250 857992419 857992423
    0x15180307050d090e070c06020c0f030c0f0114130605060f040c0905010e0a180b0d0f030e010807090509060409170a02150709030c301b0f08030f0912060702 68
    0x4146280f601d070480c01d961a81c0407480003240446610000036840c3c40401b000c900e1a0b40105140c40040c002d4400d9958036102d030601d982c4c000d610402e115481000201d080e00400c0c4980040110310700c2c410505801c0518400d021428200c10140039140d4a8020400554403008900d45212000c0d00c14000c11007031304000b61507501a03101743c0e07011403101000b0460610f42900f10000380c0300741c00005400d6110109240005012807405250801d00f80b8542c1000328840300d1144294520940d0380408107429440014007038403010f00b1080c244242c80c44144080d60f601032415038001c0090746d002400c0013190820001c10403400141048000703000131109015640401d0341c40c003048020720026060740350780c2401c40e0100076511014080041c848070901c0045050040e03059540001e080e4145070b880034522041c491580340d20201e41e107001103c410800110018503e000820f082081c0300445c03490a05a82d49a10820084101413100011012100d83d2201819084440310f030040310028606110065 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 857994919 1250 857993669 857993683
    0x50427150b03060f0616030c060e06090604060b041e090c05130b0a0509060321040b0417010f060b040b070c03050a0c052b110607051b040c030501081518030705 70
    0x60213442111260350003400d20354100c606808583c030915180402d035860845815400f800201c0b041500c1304902c510201d810041940125485800b030081c2d42030925003c4211609413031078501690520500810040c0c510300c48072400c1028103000b207010070240c074200c0f044041c0e603006681d00c18600010100680101e07841842612700644007908016150420054400011a40198503604c92442c8082110780302c6c0000307010162006440d805d25813101c120020a81061b04404003030b0500c1da5805540c64024002c965881818010800c046030800000142d9841130380a80d1144420000d614820400c265105400940e0040180c50062050303180c060000b002501c5840d116000004142c1c008030f99090402001c000d64070b20f00380540e1141e50707503040c1c5108011443c991003103060001501058007401801c24442802c82c1c0d912108030701c90b08200440b901d00740d00004141c98030006000c4207000007001d400d40f006080d00345600350b0700c2c01d00c4a4242d070035500500c0c00300e01001c0303001020004002198 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 857996169 1250 857994919 857994931
    0x2f030405010f080402090103061503140604210c140a0609080c0123070e040902030d020c031225081e041d06130504152a050427150b03 59
    0x900c0a0a80c00b102c03c0f20081c0058401039403151034840100002181d41d4024840c11318038404500c0b00950700d4882404c1c8100c0e004644031150040400c1008000c50762091464422a071169002843c42604000b000f4503c601802441c81c001c0100c00314419004010009441d944001c2c14080c2003503c2c0382403d42c98024168503042582410420000c800210300701c0d40e1207064003440e269480e981c05030220b4062011950701c9030440e49d18480500503031802d00000c01c071002e05400409880f0305030410305107441801c0e8203000f60780c403042c00600c0c86400da5502d030b644442c0c6140112106806c090601190911441c3c140540d030000d440c0c200680019040c018004481e20507000540321440d02202c11040d541c21070341e041e0b128151a1140d0070854a90b070140750400c0c003410709803410412030340e14842100c410f03000c201c8401108084480410741d03402ea01d50800f407000c2ca0100d041618102d0300c141e260312055000b017a00029112120306904040d0b1050700c070781204880c0406003698664025070994010b84403 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 857997419 1250 857996169 857996177
    0x307080d0b01030b0303121e09030712050a092c04030207090501050d0807080315100e0f0409051c050d0f02030402010f03060b16020307050603040302010b13090506072f03040501 78
    0x1c4080d660003449400c02c04800030b03018510700b0095807507441007000020f01a01c65400c407503610003d900d17105900d1900c04d9003034100555a801040c04e241c0c03100514a800c401c02c010702082a084502d910105500886840a15072612020226400c0a0040c89100000301d4112404104800d241e07000410704215200c1a10400032030b620741e07007400000081498090222181007194500140c45c3c2c900a5601c440001075040c02d502a01000800402c807056850300043c050050141c45807600c4001400c0420741100e082015840d141d880340d880c5d00c0c041600000400b074080809101c2400b840460709050120003040206001064001000390001d0700e00340e000540814000b03000f40d01904c5030600b6145240901814a1a02c5401e4401507000401c2282c0500480d10001850f40b00c0902950040d8466000401c00c0e0b84c4135402c0c400d01c200400c645289080c1030042c6100807030404a80c0c660841e60703525041001080b84442800c0a40c80e0203500c181c400c07162148004030000210142003994802d0303032 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 857998669 1250 857997419 857997431
    0xe061e01060c080703050903100f06091a0f0f03030f16140105150f0a0306020309031209030f040b030601030b0904230f250b0a08011508040f0201110f0307080d 70
    0x442d180205614000e1100d10200080d0300480d0040e00a46a0428020115440900250004c1c420b4400d030030624003842d520713000103004d0b81405000709075100070854181d2021450041c0040d40882101d102c0600920346201c1d08038068800f80222200510b803081015500c0d50a60b10a0403042c0403031401340c0c1d296940b40f2402006aa040c010356006401c021815500344007a94104045280d080043c2ca502030b6102c1d0001000881500242d84111080000b440e25042924219002040000c0a202140e0000c02000500302280d406a9060311309906005407a80d80c0d150040e1300400454200d00d5004941a08000c208043d4080c5400804118540b1983e4180f03090000d9036501000c0c00b001605070401d800740070790b20300102d0b1060500d45c0a80810301e040d03030384d6150486a42d07002884030400514103d006201d003400c0b11010000181b010f141c000b2642ca4907845c0c00031503844c44dc10003410032100700c1c401c0840c481c00b00708240000000c40107403903442d0028540a511135018500304681d144c2041 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 857999919 1250 857998669 857998679
    0x30209010b130b070f02010305092104050a050f15160b040602190e010c080d090624080c0d021201060f081015060e09182a0a05010504180e061e01 64
    0x243c20b035105150b110400c0482d040700c5500545c0580030060910b03c0b544210084014500880ca61012455020307903105c41c4d4482c00c0809100d519002500100d0040c50683d20780409074a406d82e9400c000015624980d44131442c800381200c090044840161240044038280400d00085600401d0004d442c1c41c50300ea60701d1070054080c1c0d0200d28560302a0f01040440c1040008280b020004111001d44a00300013000390702030743c0300f10440d1a07901025085c00305050380e08152240d2108020082e0a4002c002c000342c07140c0344000307104080c070014002e005038842c2c916081030f8038094000304083c0a2913902110a140c58240243e680d00c1d100a10360307616820728920315180040141e01d001514200e40d5014180d94640041c002c80321006883d40008042c403204801c00710380c050028002100c82e0f041ea000340103d00140b0000c109030f005d0142c92080480c01c00800c00d50303070003000b150103d6910700f22000500184840350b2000f82040300c040b19440c06601c0800980000c1ca0004400c009201d40000b034150340c0390 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 858001169 1250 857999919 857999939
    0x7090305030712170f07050903010207061503020310051909022d0f0a0e0112030507120e0406090b10030b0f060d05091504050613110d0c060f030c0c0f060204030209010b13 75
    0x2600d4a25203401701c14081030040784502d00608034000f029001510307010507a550350f0102c42301e1200c0343d1141030b4122800d10451909000c45e8080808030603060200d800c00c000803024503030394825081d009950303c410344030464580244d102d840300c0800498117445198480120b01d04c08801c460304c1c0c41640b10401ca09910b14201d4803013015507120402c4420960300b1b200f1302e00550070b0159010390500034140400400201060454020330000d41d540c003c41c00e801c0000d20080e54080d030405c4040c50705080e801002074950b503103551a141e031145008141000d10380007041d4541003104641d41c10003c0010350301582c5006401444c02806420110344500070b580925142801c0c054030024010341000c000704009980c0d491345280b249000301c0c0300340d40342c1161034000750110301e58000840398030781500f608216841d08480011a02d01d01410280129100030400524201c00300c10f004045d003482d200c0c0c0c041440220383c10303180a150301401242041d610b41c84d038002c04d80c00540000101d203102100c08102c511031 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 858002419 1250 858001169 858001171
    0x507030e010c1e05160302070306110414090705130909140705010207090f02120f04060509011a040e10020703110d0203040b0708070311011e061a070b0709030503071217 74
    0x1d5035584621420b808801140c28010f4152204100075051110541500140801c4200c5e40c2c404e030020600f4518514108081d5200710752881c4c98100c05000400c04002265024058090216100c2c4c02a50358000103449134001c0e1380c034000f06e074003440074085240701f0a94021061140140c0c00341e80300b0244080d60f80e544284038014031340181c1003400c1c200040d180d1600f01c4944055050380160410030101c0c088034025400300d8849050748040420300042c4580f500c5160340060801000b8880750a150f00d00f486408024450b0303074080e075a604410442c60800380000501b00d99a0b0406655440380d0303040090041b00380d0104180b07540503500e200a03090f0300020840301141c0c2107101803410200f003500c0c0c4d001d040c0c100740c2d0242c00744404803215210b541c10a1141300d0fa40d01e00b0102c41e29648031400614022924541c111a04148070f600141031514440002e645601d94401c6080303d203603039141c070300302c410318038990004255210110304002000b4501a00c0c440c40001caa0b5814210040080c800700c2e1100 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 858003669 1250 858002419 858002441
    0x1b241a13091e06020909041208150f1306080a030906020601091406060702120a03030e12040302092e0b04090e0105401103011808040e040309180507030e01 68
    0x1482c414405803080d00211980e0020302640005061101000c00300b01c01ca04222011549952038003400a0800e400400c0c05030881c5142e4540300703c042c00a804521500000342216200d610042941110b10300c0540084024098140c180c0300c0380042880c01524499050040c400076008450011828030051302c201d21850888440c2c030000380c0c032102d040c800c80794451003040e6000b882d200d4800b81038030000c00c000e190700c2e486030390009000c1d244800c80b2410801b04000d0001002c008020800143c2d98548046800c924619024984410b12462070006504134500c05501120020b200081500d04039002e80111941604140500f4480c1c2d15598229a41154400c80d01c402c40d944059400b00702119699141c42c517042404a415180b41d0010340320703007030004200d41d210a58031038202281400e00808410744000d0f0884882c401581d80c44981c80d004a01480c2100383d120800642854840c59000c8003c1244442c0d83c0d0500c5507100d0001c000d000b04450b50346c0401e041c0404550215414416015048 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 858004919 1250 858003669 858003683
    0xe150c0706140a0c1529121f020f040e0a02030405011407020d03110c01090804050a0509071d030c060307020109050106320607060c0903121b241a1309 66
    0x209081d40c070022041071a00c40030045c555505601c60364180d100e101410b004055420700702d81241c545c0f04010410841c2d80101c40e080c1c102c0700c3c080710390041645241c264101007110141c0c4550898009503036602803a41f0803074410b8410b500341b103030042c081ea0042d402107004000a120900300410b0521100c21705849a0f401a070154000a44c2544a0343c0b110010508240429160074240d00015095400409081d203240304000740801c81881c0510b20f20380105410341d000722031882c203544040d011042408031200b01c2910101280141c2d50103011a0b454844002c09841d2241400c8000034000e2114181c1101c0562805801007080c3d005502a120010781031412000c0d000344c010608019040c40d0601540c0080c0709011440001d101c0340988200c540d0709603544c0d04024a581800715004103040101d0041c000c4070401206c2030b0014800c1c03100c3c03990304028619407070480300311600b644040c00c1d056154082e10f000005440400050444410b08904a9801280100341031061046030b4070400c0c010000 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 858006169 1250 858004919 858004937
    0x111503011e0e01080708011415100c1b0305100b06030a020c0712062c1b28090b0108160806011b050102120c070507060e150c0706140a 59
    0x1400580201d00c42a41d01c405809100e5601c19034010303141c40a8005101c1900300751000d0044070000d114000007030b14452001b095a09041d41043c0200981214040c003a1200e141460000c0c3d00504a03103d245030310108a141c06403e5074001c0012280a00049030300d80100d40c0401109141800350000510006005525603115200040000d501147c0e203081e050045000001c2d64880080300b0300840d034003c50020580f8000c00c8003a894925030241520a1020b948944101d131500004001c6601584848a6581804100c0000e03801501a8064441c035030740d103041401000b20300c1c80c0034104441006100380042e0030f42c0001918900c1044030080c160720281e80071030700401d21441c446504210103060042908050074100100140d0840c015180d50790002407010f040341000c601a940f0820500c015410400240d1360103072110a0b1b0300c5030300300f00840502c141c11030382c1d0740503c814100381041c0300c0039594425003085162151341c94881c050200320116442c2d2000180d840841c1c24103002940e4607600303 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 858007419 1250 858006169 858006179
    0x13090915150305060108010b03061b0d09080f0304150b030d0c02090604020c0303101e03150c0216120c0f050a030305161a0f090d02190204110304030c11150301 70
    0x1004001c1148a01c001485800400304006101403400b90080c0800415044200810f2514140014000d202040004150600300d1001d08041c0c6002038500030006c25500b00605104502d80200d51194041007030020138003003040b0300308004140355001304400307004806001081544420b0300d101d461001c1030203107100c14014a0283d9446521000041c40103050560104c90280b07150803c80710241d0300410110300740042c2e26000c040985801001000c00921b40c02c60346c81059080c090244981510f48038292044c0e024000d211100000802c46100d04e0443e0ba908081910221011015035107424010004121071590040c190262040038184090070341c41c1d83e40032030b6a40d000401c00c540300185002440000f4604540143c4880620b119440301809c0c481006401960003800d120f0b032503800407102c2100c050300810022100004001041000c03155400400e0103881142c420402d084400005c02040540004890204502840100e1003905070201445007940000c2084018a40c01303000400c0 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 858008669 1250 858007419 858007421
    0x50d0311030c030a1805030106150e03120a02010f060801050402030a08071a04080304050d110d0c110405010605130605090319030e03060c0a030b18010b03060a1a13090915 75
    0x11189440c0c045a01c1c0c40400301c4003905681100301a100000c65a40080084014501c919005000207d008004c5e29103440b141e8400d0741901d00625041c03050600c0c4109040c0e8052240c02e03100f40304208001c0c3d8a0303d01003002802040300480e5a000c0b02d24001011030441414403c003803103540c1c080c000f040c2c1951552607285464022441c100c0d9042c24038034902c1c5680031010500c1b40264420000c0315160300341850410b04100b040d06075182000404c044401c088600000c003019030003118104100080100d0030024240031104007006e0704182001c0002884660042c018000314442e032810300d040a40310b110445e003510640c0c0341d4039030580c0403070740b400750515120401c00c8019200342030440040d0317984008079080c410704442003501281d000c105101601d400d401000c40307007101250b1803451003080064403011202d040c000c009900001100085807a22085081e80260400c2c01e1180803051012200008581c01010700b0301107070411090001e07410200d40155010703e5881000605825a0014004 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 858009919 1250 858008669 858008687
    0x5010b09011107091b0807051e0307030b150403061503032703061d07062102030a112d030702060a090501110c070f0503070f031e02040c02030a02010e0106050d03 71
    0x1100c035000b11070700010f4059561240c0300800c0c2c41174401955200c20010040c1115034018402d10a00c031003041030305104404c2640900b5241108a607080c0c8946a040e421001000c9a420194100050174100d10000c51401c0107041184c2c4511414403815160a08802c0c1d04881840014080307652040d510410304c0d00d030040c201014800454240c42caa550303440d010141c800d1800742e08500e0110018403c0704500a100d0f04001d0130303160070580c040c044907020031041720b242c2d089100c0c10b451380440410024501604201650304240211548a602c1c17180d8103400004008004401c05d800c1128402c044002441501e105686075000b424190340c400b03403071002600040d40225119542c2d00099503040344031134060100d4520b200014014141014044420380000380c024031301c01ea2081c0c00410900095200d00f030b080d640d024400500c4003140c0e2681185100000034000c0d8454113046485046540c00005800075000c664003d00401e490b0f2114a4200c8189000da00d80200c1400d03c61408a03015801c25 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 858011169 1250 858009919 858009947
    0xc0f070609050a2a06020d1d0613030b161407031115070e03060a0b06090121060e07081503060c091f05070c0f0e01050d0203100509011b0305010b0901 66
    0x51491103029a48800410b2811350f88008a000e0841d0390300f409004480402000c2c0040d40010080001d42020280404e101207403001d0100310030307254600d86c03a200c00c41514107a400107103c12150a40342e15142d50280d01c21141020060407000f402e00985108800e1025000d00c00050645002032684044409004031041c01c40b66208850301003c04010092643d446004c01c1d81d00c800009109600301420030001500505c0018204803010143c4e41c3c0e01821a1191002400c100f01004d00311075800e0711244841c164006a14901040044c1c83e501c4103040310711445c450390300d4014954483e00f44034101c1c0f11614081c1d0b0103a00c04400119020031017070044c689808010007a4282441c00c108969aa400740d080c03a00000c0c8012518400b08203808285401070154411a1042c0a04004080030302c444144580d500c2201400e020030305545040c05031500320080158140300c14940010803038040e08280e040803600081461048002910038800c6506030b40f49943c10701e242c00d4242004460f151018446 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 858012419 1250 858011169 858011173
    0x4090c0c1202030301090605031c050c0f010c05040e060103051006141215012c0603041104050a05010e0a0207150c09170a030f051903110906040605120c0f07060905 72
    0x91001051003040702402149840e402540e4030341c1084400790030342e81140e1080f802644201215810140d2181c0790b00e03550052841c0050300c41800314030052420041c0d1041c85119460000288550359000000700181c4206d0746210403c0e0322401c00440071220200c0344010113203a90310040c81502d11544003c80000009103066040c0f43c1c400801d070404104c1030780c440034400c001c40d8078079007a540c0098035400d00e03004640341e04010401e5003000d0954600c03140d90741d43c0f05000020000d41007001f03400e00b012161002520800152030a400c4420051600b030003546140c101001c005510341c0400e00803208042e51040300d541d001142e41030a0b4011f0990000d614041c08043c0d20040340488242021110b019421001468000001c0c24003800190121115108124042011003041c108a500c05032502607607280000d80d400700303010f104541c1d025003550303950300400000b000078159138400f010700b800c0c2c09001c00b036041a89030300500704030511030000c201030602014824500801e43c40c5c1d005561890040d02 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 858013669 1250 858012419 858012437
    0x6090d020303040f0b040f0806040308041e0f14100605150304020a03050f0304031110140c1e030408010b04090506041401020f0403061b021501051e1908060703020f04090c 75
    0x7908132005205034109071000c420101c3d08010f580e25029040004001d0400500301904083d20b0003004498004c2001d4021655801140c1f807034402007070700005480d04030310707422103035500b502d0045c900d91406004100c0300e2203040d004200400f0341c0d20456040340c3c00100007012030205601c0d0034100ea0401441079900c121400e9000011601c2801042c9500032410042c6540d00c1c02c0d440c080041005031400140180c642d601c910b00029002040081400880080c0d5a1507860340d1405600d0000c40040350f582c00c01c402c054526800e8070020291041e6800e03603000b4410208544240002c031003403c9005030055000001140100e5140100c01c50300700d0040380007525042c2e495041c4480c0c0c5c0d100c0da100b168030b250f65425003013080018612403500c031035451014100d072082c4101a9840545c042c01070b07510403c4142207807190640702103080000000c0c05803039030b030b000c0b800000c2d4140013035500d00c0358080900843c000611154480c0c03003122068100f900d84076041904081e03410000702035040340803040c451004 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 858014919 1250 858013669 858013679
    0x20601150201020c0f2a0a170a051506030c01141210090c0207030618050c0108090102090d0b0a050106111213090f1e090807080c12070515060f06090d02030304 70
    0x7102070560741c9010300085c00c44555000620300c4c049203a203038502c8001c40003059108241d030380811647c201d900d042031a4540c081c0c0b8480300c41c2008036101008102d8414200c45030003682c5204c10161240d0411015282d03031455003801902c5e010001d02e40800d201c1810041c1d0101451400b40c0e442c1c1000d94203001e0a1801d88484000c4201c0764001000c10140e0f001000030820008503020384c4040115400d9400088000c90760b0b465520981c4079146418020300700d0002d10000c4095040d2469035000500e40b1031501c8003414140c083c0d40301910003c82d40d07404d210022985501800204c030b664138800d40103004d42d89000c6000462a0082030104004081c8164001910412030180302d0380384004003000112410a44400b50180c0c240d1503220800b0344c00c002211011407544030554106541001c905035940c11030070140703410070b20085484602046c012030600140140050b50a000003014079280503c0e031188020040400e1600350303660380c86007081000e100703581072074a80400c0052000d070071a41070035125 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 858016169 1250 858014919 858014923
    0x40c11030a112e05040204020d0c081902210a020f030114031608030414060c1f05250302130b0318191707080c060403050d1b020601150201020c 63
    0x8040000041c0e01c1c0c810007070310030000340102d02016842220310590100c0f41014103905168201c501c181d2655100c00050564445404580c01c41c00147c00800c0105c080b0074010308820070903640036894040766001d0760380011030791080f10404030b00cee41c00d914030030400c543c0c91074001c000c020190049990244002219000f202002d1030180207541d108602d50750b03445050606e4a000c2d06400c45626030300f0700c810040b210000c805c6500343c0310714040312060075140b00042504d501c01e0400f00002c3c0d09c240e504c111014020760615001e200b084260900c00743d22446920b1044008811039030014207003007401404558004d03070013821080d101000c0366002c140d80d151006e0307054108965902d40034488801c6038030614000d00001054841e110640542e4204a0301c0d8111420b054404502058100048400a0090003403c0d5141d401d9011b003120480d1815140007440c44d00000312801100f403c2130403504461194101d42d410080d840d500501c0f01d41e180c000640c0c00540d805516401b59542000500510042 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 858017419 1250 858016169 858016177
    0x13170c150910081609060e010c0203010e06040b010614071707060f050c031b0c25080109060605040606030c120c0c0507030b0708160507030302090f0603090a060b030a02090402040c1103 81
    0x8140c50f0b04503186480c03040041c1c100c004007013003000c00101402c1849082e07000408408070f2042840d00e5080310a0301d10200380140481001180a4800c010400c030402000341001410396442d03035a4640583c01d8aa405642400b800c000189251146003c2d88444a00d030b10150140d40d00820010411a01d60644170003200c0c0705480b4400078400000401c00c02e0800386040c840c04100d60b9031142e1910b503002900f2511103056080c1420340c80c0769804c00414a10a04008001a1980000804c400010782c6080700c014000c40c81041e01813801e011001511501902c1607501038040c6468a800c0040000024401440308404050078004501c01c45400700b901004150055440390f6640007060030907070809030211038001d162802282d44034041c010b00a90200a6035403e644c1810f0248e150000c24000400001d540c030255a0084004030400115210000b1910510b9004440410482c81072000b80342c1c03903004030390019400c905200003060042c201607000f0028412185010594071081403501030850340 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 858018669 1250 858017419 858017449
    0x5060c06040308090f06010b03060d0b13051903050702010e03010213030f2d0311100c0e0f01030b0d020f040f021209010b030331080706030213170c1509 67
    0x300c0344040004041d0000f00306500900040000e100d215140c10341165580c40500840e80c0c10400800890740ca80c0b20800702c1c11105078002e0f0003036180d04e08031400b0009080c640307100b60360f03500c52158003007a99210b1031552042e035505555000e14128054006544000c0c9040340260959400c0100265100c4490080c3d0055440380d00810000801c17410800040040c0c00c201c681c801c1414a90344006140c01e1000d421b5103076050030095012001c0d04e000904002c2c46210901070b490405d0b00709074545501c071102e4000d1401c2295148850100407004504940c0030884958000000121440151400080071401e0200080c0f0100e42c501c24181e40342c0590304072402e249050703600d00044c130903601402e0080320344e400000e40086080c4440c4c201040c240e0f030b1130004480390f500b0007408054401e0030344802c020058044031b0100c50a0030b0392000024025804410f034150140011030313003c00c074000d0000040c5141d0b02c0300c0d001040b107050b862040101070189151110300340041000002400c0c0c807a055030041e0740e0 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 858019919 1250 858018669 858018673
    0x6031b0d0605150405010509010f05070209100e0907060905121c05031e13060906091407082509180b0103061a040b0310180803040602042907061505060c 67
    0x5441d1100384143e260340c8000598181406100502003030b6802400d4854044007440c180113460785505e030903a80c500c9007410194004400070208004109500e4401084420500c00302102e655441600b070f0b156a418041d8600140ba0103900b0025071520004280e0056211026941c050800c450b01007441340000d0002c0d0082070010007001301503000b00100480c840804808020b50345855012311582c5850380700001c060303070b540c0d00054045c00113503400303c1d40440c1c1c00709890451031a2903094592307940580c8100e80030f80c4a451204039401d110030b0606004401c56085a6002034101700003040903006610034241c401d90303861190404a80c164008074001c40c092040010544040d940c0c0707141006c810307000c540c025814007a0b00e03410750b20001030b00c1c000340e0509140020082c41c1000422000c540f1240040d04205011003030005001c940d80c01001226003580e240500f800a2004201d01d400e681c0542c49843d140a10140011070344070381200b101f204005040221040c0c540300050a1500310540e100026 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 858021169 1250 858019919 858019931
    0x901020114150109060819090606030f0f1115030103121e030c0201050c03220302010b100512090a05060a021806040605070c0506040f09021c06060c0c061d06031b0d 72
    0x7030750704130003c10090850f40c0390548052800c1c50110608054083e0b092554070342d9200c44109100455200401541c0d101c0b108400068640c10141c03c3d0120b1540e09a03030004944640c3d01302403603e0564040500d2001d412641940e20b1519010f001628405040050266210040783e2000c2d4000c64115010080d80780007810806900000b421680300800c02c00c107908007001881200c8101c014001d03400100300324144440902d40c9422400b425101640076040154003818002040e00240548001c200c8000c08800d103995580e0620b40c0c1d9620013801401d6a040b000c00300d17501c961580c00603c04c501c0356607216480e005403900030426950003a40302000151340403503048200045072041e03c1c01041c080b10382c14102070801f208650801000d105690003540e000850108034240c014040d00f0142d0303045410081030303607030311006801c134508100e0803500426011000301e8028000c404501e83c8000801d05000040e282406004960340040c10320000580d4400c03c00075000c80d030600818903401003600100f40 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 858022419 1250 858021169 858021211
    0xa060306060e0108011401210309181409060412050304050c03060a0203010e13030e0402160c12120309080306040e0307021f0e0a0506121902040303020106141906050901020114 77
    0x2100c01a21700034448454040042200c2c1c07841e200104035480802c1505900340d80940f03400d0b0703102c0cac0386640007c5101e4003440c3d01d0300c10400c09500400d03020662407007650080d50b4020429480300c3c02254000e0040414a00044105208201a43e80503201d201115105502d07500060314242084a40e100400d4002005100741000040303080d030000c04400004154030142d40d00a0035191100039400e010380d0380070483c2c5c0c4480002c0c5c0d42c2440c40d0341e0002d0804c403030309441d00d00c2c009081310310120541e507840c02d608280c001d051182c4186889150807884040c21504c0c0c401c1044040d00307000e12034011501c010300a08016a40b610060718a82083c11112414500d0600c00a423207586042d035094851807544008000c15152101103a0a21145800c110202e40d160100842c00d9200390410075032081c40483c008c070030540c0540c001c00c10703146003540c0240404018400c0000d00c0220080c043e40b02900301c5030802ca1175010764003920280c08140000b050881c003440c60070a00c4802152856000d42a0341c07a8090 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 858023669 1250 858022419 858022421
    0x209030d1b141c0c120f021f09020901050303070b160e03010e1e030405061804021e0426030904050403032711030304081e0c130f290105030a060306060e010801 70
    0x2182401e400d00b0711359042d45441d002102050310801005000d00401c3d103d802610070302401c040301040910b0410000e101c1c02c0b8640003009681400c034000d0107104004034282c60000140c42c4100d0780072083e0981030ba07405000f007000d100342c3c408800520400e68440c0c9001d03034080c0102201c3e1140ea0b4014070140803840140c1c2c0052590103c1e10760316401c03c10051055442d088115120320780003440003403040d00b800e0007180082c440d000c10054680b01c800d40505142107523130003c00c100d445010000007030608806450b9503000800452020302e82c000c000e000414140342e0040ca610074001e050000340e05000c0380c14190b941210348004a805012030700c0c0b010800c6005201040200000da0040d4203017401c000805544101c01c4490407410b80841c2d8040031912000c001800b03240038083c0202480124a280400c00303032031101d00c0e003568030341410b8441c0d402001141c2900700c126601c65542400c40072200055900c0d500c082d0502e080d181d182c3d0400b01c0030075010b008d250014401400300d00007030341c0740c42d540764 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 858024919 1250 858023669 858023713
    0x712080a0f0e03092107080601230a05100306090216020406090b030a1e02130c020f0d0926011107050d030203040b04020609041d030c010c030209030d1b14 68
    0x80394203032070b15944070890300300082a903000b000d094802200045008010070301c44200c00d400d201c0d4a02c118030740410a80d10118140d41204d103040c0c0c01c0f00324000030f240c031140e03101344141549401000d1540d08000601e00030120701c15114140c1800210700344c590300310b80705980c080d9510364100c0755003103658021810140300f024001d00e007408003084041c0411000942343d00451001804412115a011111100420b888a031a075401081c2c01d40d000001c14003080a003003100201da0150041c4d072a24000c1110210308580c101c4e103d0343c0c1d11036115083c442116400070407002c9007042d0f10408a0b001d08030030400d02c00c15031805014008103403030340054540245410380352040032042500503c2844001201d94004607001581100e200381c5507065840410000d054592914002c00d0041000e00c02c00040480206140c6184000901407100290402e809910900310001d8050b8044000250f04070f04c80c82403c0e6900c0d98000c41d05090100f16126002e80d2140c402903d4040e8004041000c00c8000150500c = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 858026169 1250 858024919 858024941
    0x106021b15040308070309090207060f18050d0807260105030c0105040f09021b01050a05040c081203010504020f07080c010204090f06060203190207090903021c080c0711060712080a 79
    0x592101c41d00c88864800302c0c0560321009054040c081107150806004210301d030b0203002c41080454440c507042c2401e801900710a40c2c3e244c4901d2402d201002c0000250490000c07aa400c28000c201d5007071100c00489090000034940e00402801c00b200e804507000d0406003507114100440404030a504010426082c846050603242c188001000704012a007110740402c4120307a1462001a10f6004040074803c1c0e81c3c001c005101c0065180c1400c101c0c2c0b102e80ca51009024038001c01d11500540d03203070085240d5620002e10290103210080c00100400d141540090076200c4002c1c01150911402e691007000c02c0e008103032216040d94000c24140f0400304e20303200d1440620f8900d0030900040340751a10203910303440b96881603220b010303200000300440781c02045014001c0c103400108001440040c10007d441e0b00d28a400000c0380c01c01000100b40311031143c44010b0241c40321400a900d8068955035888402000d815403580015040c0703d00c2000c50786401c01e840301040311751900c441904d080c841542c102c50a40c40b02c = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 858027419 1250 858026169 858026179
    0x3200610050d0201201002121602010c120e030903060c04140d0213090f080307030603060f020a080105122b020c040501080c121e0a0309060206010819060b090106021b 73
    0x140c0e20150303174081c911691a00c42c50300c0760b8240c40c09660305142400886c03000e2211680c0000303101120354405440881c4500900480c0d120114400340d030481c00e0f50440c40f08200050483c41c0150072030291503000e015400303114401c5a06c0c004503400801d007000d100b19002c50040c080070608010018001c0051041c5480498410199159540c0000c4484811440700003e403a914013040080044801c03068498a401002d803a84a01d00f551008001c1d03d200d01040b182c0600b0f001490340d60030a24002da4071080541d4607070ba44942c1c00c00080c018050113031100141d6900c5422408000007130007903032224110084071900c901c0c07420700381c4019181c12942400180114038040c010000918007184a011542c0100e840d030404004802d5250314003112506007000b441558110f5000a150006280180307034860744594045541d565800d1380c40c1e25091148801035040149043c1800c02840c8460311181c0c402d1200080700100100416186031090f000359025a202403200001b0400404d25414001c6003122 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 858028669 1250 858027419 858027439
    0x1905040e01030803060301090f0606090c0e0d0803130b040309033003020f040509010b03010311090420060c0618010f020c1903030b0d0605040606051206130320061005 73
    0x14240450340500c4007600801011000c80d85540d000c0d0800341045810440250f1030300114203251001b00a030b0302c1401001d82c50248940e005901407549000d034940000d22800f44074800e034079404081e5000500b440800d0702080c4440c40092941200280141c0c000c1d030394141d85905500e80405820030380c44030341e0200103410400f08180030b00c40c4110503025071b1a10f80962035a07803203149180c8500a40e0003441e400045c0600220b106c10002005e141240d00900e05810014140c806112010006032000f030144459a00817542201402040441403680a81030528040f50f002400d801c011060701c2c2860981d981e82c1148070324250900401c428801072490031440c01d1001035140383d8400340002101c05085000d03600105150295020303070000e100181a0b0920843c552030484c0040200b110100d480c00c2c94168049118100000c011080c0c0030b60030002e10444c2c0b6040013108115401e0a81101002160b50388a985100c0051f4241001803c10005181c9824482c50011440f502a0004c90203440458 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 858029919 1250 858028669 858028679
    0xb0c070c090209060d11130305100c0e06030c0906070204020a0c03170907030b0910051609060203040f0e0a09021210051e0402210d05040504051006080a0e0307060908190504 76
    0x10112090314410201c0044d4280c80304406070a140103071f4458041540d00a0070000501002050354840b0382212030007000803200c140d105035a046e140078201c80e0440c200307000080e4003800c081c0003040c2d901d10042245007061110303030009084ea40590340040004902c3c10390079041580200a84044140c540489074032480c003c031400d0780e22034041c48041e0452040380080341c0b82050030710105507114801c120502c00c80c1f91264072261201401500000041d010f4940040e0f40c40c80401640c00385c4188085403c1914940342d124916400c014190700b012654446007400107980701d200780d9100001c0346000e060340071922803108040f200020055103050304c1414448003a6030075001d03c44d0b07120340c1c121616601040410480b05164642490b03e03a901d10441000140c5e403600030001d0012103008503402e05c082c0d070f1031007101022503010784140b0004c50f000d007000c130b102021a80c00c140b00c20155441242d083c039250317441d010184e030110202a103c4400000d5015175103d851755204082d2555402c003540381902c0d04d = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 858031169 1250 858029919 858029929
    0x12020d0309021e0d151b020303040c1802090405090d1403061c0309030b010e16030e06060f01050d020f04090e070315050631150807051c0b0c070c090209 67
    0x45440f80001c14041d16010150798038200e0505568005109092011224842800400d80c0040f038001198410302c81000851002048070320860380400c1d032251040c5071980011050f0a81c007901410301e43c090050750401c3d16544a5070784549041401880301151541e4040c0c41e0b800e09a81c0c0a100d40020420400c181d110350f8400341d41c46444015911140c1018241210060801d0300700070b045959601c00099075800d50801c0a01500e050504aa40300320014801d03412a0503001c5210f000707800c840c000840ca403600079440c0051503810304041d031038011050501004c036442802c2030211490040b8007071080b442c2c10310030a050f0103024402803030038a056072501000d2186000c0c5108000780c07034100142090710b401d10350303aa50050b040c4c5810040c1c00d8266210500641c1d000446501c10310305075a5681020f1044805402c4900380c2c0c0240c20818103200501400003000000072698541920b0010300040b040801c20f88100a0032122984503045450060110002a800b0690040c0188518580c4d543c41c = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 858032419 1250 858031169 858031189
    0xf051b12010b0304020105042105060a0902010c032d0203040f060e0303030a111e03040b090d05091201111c05072307240b1f14031b0712020d030902 65
    0x1400b00c4581c695680d440101c40501c80c1d0381101c101100d40c502060700c002c0e141380c00105c850b0307c12400e07616955242c90580c001c8505087e00a030001e0020900200407034010310721b15140c2c100c840d440400541c013034141510f0035568420b107140141d00025080042d0f401480c0d40e02c01401c4286040264410070302d001035500d020190102c46411307a500411204400040120782000b1802c04a103100a00110301c88003050b00110b4040e12801c0c6d0303a000048005c103000c02c1c50f68000b02d00d51151810010310744280641e080030045a400d9a42da80c025401100c02c5880140078203000c02e001000400d03100c1c031410400d40b100a000700c0d0600500c90380c81000741194400204402d0b000c03091442c4c45442e41d061040305010b03840d4405490b0602c6242c24000c1c03080c65002050b004505071952840c1d00703540148000b118080600c1c0c080080e104e5101c441d13007144484002c5070441f090700070518034070b01c0d040342d0a80140d01c01f000072103c0364003951665404640501c40c0c030402d1011810304016040c1503401055032441c0d = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 858033669 1250 858032419 858032429
    0xe0316151b050706031406190909020102010204030c030b06010f08160e18100807051c02040e071509060f0e220908040803030601140310050d0c0503010f051b1201 71
    0x9642100203480c42520780c52620603801500300c03607589075580340180040140303a50051400d411100001c1d9182413000c648200e20300700d8000e0000661601c130300c62004200c113400032030440d5000c2100001180b0706121100103140194612025400d20400140c2400c0c080b460200620a04600b0041b40003071880e011900c03603004d410940c01c3c1005440000744000c840788000d40b220f10860301031000340542942260b0a03150140304403402c1649440c20008009140c15041c7d400b48501b400040040c20160083c14585c82c90a00321000b942e282d0655440c1540c039000c0c56400224040010400b6943c0403014141003203075800c0070075031140306c000031450002204400c5540103d59040107030071010141d01c5094440e0300b120030306440316102c0c031106450381e10603290f407030008a068200e074040320101412280101260480001098a40300900001d00340424041c1c8030b07820300410002c0c0301d4800303024072111000701c0c0380005100e19090f0f0030181552100c8400300824441071141107501003010382e5080c150b0f0 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 858034919 1250 858033669 858033677
    0x70c0914091f09060e0a0c0503010605030303060d170d0e0c012d020f071d0702121204060b151b0d02030711030c10020a0b06041e05070e030d0e031615 66
    0x2d0341e05200000503084000009200a140031203402d520403001c600000c01e207100305485040107940307504242c00c1e00d10318020381d68035070070410120300a858100382d0180c0341441100d01c2e044c1a00d8005011402d500285288042c045d110b1030100b10a040030700c140202c45c90242402084c5e010348500781082c1c00700e0012048140c402c000410940c00e4020408941c0948207102250000c40c2c81d110074030b520032040c4048c0480f0354070ba60003080ca20b500100b165210000756850081c2850f42808002449210250042d1805507864081040c9516400d0741d11040c0e071103100f8415502c0301180e44951409020326915902a04000000d00d0010307400301c2103802032600f090010307000c19038640000c7d003051042149150b0246840020303036009500800c005178000e02a01c1c100c6040da4400d402d1005035841100d02041294070700380c0414050309154091070300200949041c0b403168507140080f910b403901e01c0c80341c040030801800106505160411001090010180c0c010505c3da01e03004070f14402d50300301d9203008244 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 858036169 1250 858034919 858034963
    0x3120c0c060b0109350d0c2907030b091014011818050912090a050907020102160615060c021f1701090b0a150f030b04060b070c091409 59
    0x540c3c0724102e0007010345610840041d5101080a400040c441c41c1d001c50740c5680328110f82c0c071701e6502c4046084108140c86846610b01c03010140d031000d048040e0f000d00004044030210420302d5004184030101d00c1004c181d180056a00e1049040145044000b00a45285159242c091245143e640c40802d001d440030700b00b00100f094840011003c805490f005074601c481c95440d680c00e194415005140114101e00a90f9102004283d44003d03900c5411015900400c130300004021a00744400c12507030214091000604180ea200c03421100303010350107415a05180c0358101680c19494502a840041c4070700d0070b120603000c1e45071f808109074174210b950b0b02c0c505140c0c1000c0d15003100d004d00031038801155061002003080d03850795603a80090400000c124010303001c01d000414820308410f900c00c280015034640f6030b0403810240f801c4007c4e065410043da0084c1e125000010b9031400000500b012601c284224140c2a0501c088141126042c48410072031a00200500440381800300381c00e2241a044001c40100c = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 858037419 1250 858036169 858036191
    0x1103100e1504110a2a0b041a070c11010e0a1206020403080307080f1302180901020f0703080912091302070204140403110d0f02071710090503040303120c0c06 69
    0x44410400016038220782401d203001e00c080c0c070f200001c01c100400340c0c580340345034401c0012102c0d450303241104041a0807400b001000211344410744080c0d07c42d10880344105070400b0804a00b0603840141c9182002c644100d28070020480c0c41c404550000741d0070300e004003800c0120b60010b0105007c6109840c1e2840402002200b071041d107404407405960000c61180c1d072824481e0004180810480d1104045101c5a010a10042c007140308500041d400411083c00c50800c0102603003910005002a444c56508209609050041e075000d4291030707019484890807842d146d415507042c48024109504003200070861001d466561720f0060110300035141d00103846186610100380207000d03100403100d104c6010410007080581c000710904000c216081174072500c0c0046041136965401400884015810003802441150720300c80390201554110401c030b0301c0c3c0c4400046204100d5120240c00d80b21504005814810716802900418200e010003004219a0041840040c0700350303c1800001c01850310780e00300c1a6 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 858038669 1250 858037419 858037441
    0xa031206030f0c09060603060b2512020109140a080f03040c0b03040b06030f0109080a140730050c03070209061801182702011b14030d1103100e 63
    0x101842e48452202c1c840380403410702d8048038400780700d000c076480e040c00b8000c0351552180c054142168402c1ca03856043c0841054200d00d15010300440d03074a0072085480f0f42d40400c610340c50401402044d500001103840c25070500049500120410b40340941c00b09050000083c8000d04988440004841060b242d0700c8034070b00015217015551044000d0400030060100380008041580d00580e0120201e405400c007800c2000d003a079013008ac000e40500d9090090050f04c0b40940c2a0160920101e40d00d10714100b16030b694181081e13449025042001102c030301c00e00340d5003107204000b0400e00072814650300f0301d4440390580d17a4901c95104002d00544840c0046070007034446404440303182c3c14001a00940c2c0da101c036204503032081406c15541c5403a003814890f008505102001c02505000d0400010251603190019034036010808146051031381400e60040128a99001510000107440065561030000289a00070348000d038400c01c15a8204105000d500d11030079001000326440e682c1c2c612100e64030004614 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 858039919 1250 858038669 858038681
    0x6040303050c1c0c110c0f090c04180c111c0509060c0d08060f15070f0f0803070f14040602062e120b0f0402010c0f060207020a1e0b03090a0312 63
    0x7151032030f143d005810310b140d039000380b600c0c16600d607aa6022075641c201401e54510940d001d0703031740080d0401c14080d640c1c1060020a40d010030a030794941d2074103070381c0c643c02e4108403ca4594901c9459641d050170b00001e502500f54030221180700010400c0481280301c01c400c0b030010003002428044002548440d41d143ea0041d2200340c0040c070113540355a00c00c408064103020086901900c50006c01c01d81c00c800741b906c1002c0b03001c1603844102240c00e003d41c0c0e1390f40f41e407007041482d81596500346250355a0000342e0100001e501c10180c036990040704012144010f006003002d0a01030711100700602c0140085030b030000381103038481400025101e620001c503940b081c0d44900c2d2078903280740815041c00030a8043c07002c0c805c40c00180c8500d2040c0c0f580c1c5d849101101a4070800e403802800143c0c50102c40d07010540801800c0006805031800620b80416640003807030304034990380000741c09940c80350070b00c0308410080082d01c024039103c0d0700c2501e1031400f0b42c4029111000004010144050b0241c07816045175194408 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 858041169 1250 858039919 858039937
    0x30c031407030903020105181005060607080c0a110d020f091315060e01080708150a0b03070303030911181b0706020f09030f07060504091e0501060e040b09040506040303050c 76
    0xc8160a0251006018000070388060b0050343c2400040395924018901c482031001c1400c01614030107003001e2040c0060000504a5540040203200341c0011642d154010400c00781e0800041c083c180051500c0c08c103034240c840c80140301d0b0455001020258840302491841c020007195109c41c41d590303118104944ca800341e5800350035485440c50040809200b03030310923016079448541c03001c926aa500c1f02c40d5980d5156000b03041d019000764100c03903405924141150341060142202042013400a0003080c030f800b140b50310640003e520382c8422001e00981d0801c00c03220340d60554400600c00021034101c1a54080500f40010005421442d945065150015144038981c086419542d4042403031045029400c0a072800e1b1090141c1c110303609103a14002014401c43d149503e402d03042a143c80c0246000702180142d0312842498151022015040d80c4a600e018040c5521200c00c0c86e14220240000c079010090454044d00005007440041280000e203190700070380c5440e003c5010b684801251845020320343d04 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 858042419 1250 858041169 858041201
    0x903030e0105180c09040206180a15020102300621061806090615040c090b0c0105010311040207030206010e07020c030a080307080c1c090203030f0424020319030c03 72
    0x180103c00d200200030800001201040b5a000060b0038200100481c041d10004d52055040108004082c00046001500c0310018001368405903151000340341c0c140710580160045c0d500107221030a01d80300d00014074524010b00307600c420b216070f80c2c00850003450010700400e2203083e020208014801142c0700030b0000a80c03100641c1c20a00380401c180749400c800e00d031051681d0050100103000c4407000103001d4803c0801c0010600c198091b0810311000381070301c0d0b0442c000c101424a0110344000c500c001419800b0080000040e0fa600d5800d00c20341c9501e4030030490f0720581c0100300303803400700350b0001d02281501c0d040c40400e1004e455020040e480c15055046450b0907015015280c4207001207003020f1445507400c1d45034a190365442040c5007000e8400e0800403401c101c15001102a0708207a80c1c0144007861028040f6498059412110241c90f003103903012001007540014003000781580f4140480004031140021400d201c20031804002084140040c00b0070141c1e9039880e02d031260700c00c0c0c01102c5d0a43c003da40e = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 858043669 1250 858042419 858042421
    0x2d2a15230603060c0a1d1c0b070207050415030308060402130f0608060a0617041a01080d02010b030102070c0e19020d0b010305071103030105100201020f0d1d06060a090903030e0105 79
    0x140500c03030004101c42a0b44240610310015240d1250700040301c9002185903220b003440d2174080ea800c204070340341c10800c942040c0d440c000d01d13600450003c05140e0781405110b00c2d4000d441c01e600d000b17240081d2900060b020b03d0815a4090300c01002100000036130b039041c03c28120030307036030000400d009020701e07500400a0340e0b600400080700c280c000090f0382514a603980310b1030259034803424480d1a60091040c0b0000800182c0c070364241c10406c9401c00c0c4c01500c921200340310860f0b0003250f010070740350a03003040c90640c00c0b410104094540912440403669819030096040c00d00705e48401d9400800741c82620a00142031000aa590840904030940004480c1742103403101d032401e002c60014a204c1001c40c6c0400c1c41c4c1004200910301034050130b860b140300700d0b006619682c20300f030521100740c03401c0700d01c041559002d1241e80301090b030343c0c0c000d040e00801c403510005884202e90503c4401c1d803001510800b80350400e005004054850744e0109083d04d811001c0441c0138080d078a01180180038807500d020b269440c0034 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 858044919 1250 858043669 858043721
    0x20d110703090603020f0f0a21061409090c090606280324170703050106030503070615060c0f020111160801061a16032d2a15 55
    0x20054a21607000350b071246440d0751600029400c900c1945200400e0050911011000b40c8560303004005034040392400d0011992480c04559220310311082d55400a40c1300c400601c640005180606d03100709044541c07601c2801d2000c10705444200d40441d9500078421080000e0883d02d411045450000301c20801d4003910b40100b142000d09417840e202c03000002e060200c440807140c550804070b44031100040006100d02c0ca404240034070043c00094884050260781c000201049082c464a002140030381c02556503501c140c80c2c00d804480e090040020103904803481448a075900c045071980b43ca5010070f450f640e02d40c080c001aa240300c02030780240240d00c02d24900d800140403101000f811225514000c1c085a80c45006a42110f43c554862189502c020300403102c40405200e0500003032800380c10442c0004c040c0b03175030709601c80c0801c45c0145001151031090f2003816911100c905501d00f041c0c00e00c03200098a60a50704414140b120010b0084100c400c0240a0210320354450282d681d541c034035a24030a1800 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 858046169 1250 858044919 858044951
    0x110d240303170601090806072f01050901110c120d1d010b1806102d020d1805060702060307170702010606020c03030f04052106070806030c010c020306070e0301020d 72
    0x95580c0e0340507281e81c0000303d0180e501901d4100d00799410100902090398a0301c100301c4402e14400c0d0202e80e888400321007030700215940801c1580c150000000455603207442540e05094405581b22280700d8203040143c0c110050005c41c3c01c4a80b9034144401070b42d100e02c00b14108001e08100000b130307010403c1c821141c40701e04805501004018000341c405400c22040c049a203890140201d07983c81d0031000000c844a6540c0c41400044500088001c0c984c5190070030104200306a1804503440026034054010800d0b25070300b10000480a4241040050a41d400c11001c42c0b0140544803009004034004400715002c280168420004c41062803a00300140c640000000d020b01090710071400075004100704c0340d0943c01e001c0704407601e1111034040a40342a15010501902d50103a04200c3c1014103501c00b91210340c0300502443c5d0049025940d40381460904008050401c58042002d45c10301a0508542e4010f850204055600c00404e05001d0081c2072904c01180c060300c181d030000e1607424030746a0702010364800 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 858047419 1250 858046169 858046187
    0x100c030512011d0a1e0c03020d15030b090610050105250302070f080606100f11010204060c0c05010f021c090e09011406030712110406210506060301110d240303 70
    0x543e02c0034203038a4459000c400d084078443c00083c0b4045107501546005288150801c150450003071034014540380001c05004211501d5042056081001400400c1406012144c654024030b01d100074100703504040300b115810042c588160760500c04c02203060a004424107a0b181401654036140e5900d400c003d250080d01d8170a1401505030f04003401001080a0200040503481800003030400c407550f021290040e40e0010b003040321002008800c4040009115003800548010409600c03800082555403074200d6090489070802130420005015030348042d60700190901c0c911481000030341088420100484400c0c045802a0080f04084024040c1822056000c3c80400200050103443c40d1100400c1544a601da4400e004043c403c3c40803000c041048505060380c1e40400502c006140e07580d030226104041c5035212500c41c284203c1806000340039061020543c00300d000c8008100c0060035a00f0100303140110710082c214640c0d54804030340c62940314119407102100400300c034149a40d892500400d40c4030 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 858048669 1250 858047419 858047459
    0xd1109100806040c05092101021e210606030406090503040506040e04050c030109050717011b0e151c150b0f0c07060219110409021c020f0d02100c03051201 68
    0x460310013074081040c0700e801a56a034680080003460381c91459500400c400034401080c1e400c42d5800c20074201101e01d282850b09000340300c441040d4841c00c3c51181e5411009010f442c140068008108000c0166990011658456070003440001c1c050320500b0014594019904039603080f03100002d02142180101c4ca06900c0b580c4224112400e0030481e0003450700b43c8000c3c9500600704c1c0e001d407074140056a504400480240d2010b800010500c0c0c1c0b0200a00e45c41e1400c4050001107041310542c549242000040312035170b01d0b0541d240c245010751082910881d85042264200c01503520703c4001c03052501203400c100188104d1820be51181c10080c41070b121680105000c0c5c0d00780c403403240300180342d0f800428140d050f00a00884110b807012a522564040035000c80754550045d5643e040c100141d64448040d0300301b809420b2050130604052040c0518485045070291080302051283d1005036210703071005404407094075100246030940d1030161100e0082480c4101140380c0c48001050b908040490101102 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 858049919 1250 858048669 858048671
    0x170f12131209180c020706210c0903050609010606020c0607050309040c05040815010305030a0f1e0206010603060f0f031b0e16031406090a050621060109110c030d110910080604 77
    0x1c0c40d006041c0f0110f0300c043c550800960861007081007054050b890021002d440d034403044001e04803000c103c40071a480341c00d0050100d24224030078414060208185079001e80307201c000300440340c100701d17000e0355844240c110540f040500158020801c4418401e40b10000000b8106020809000c0c1024046400c1400760048078868500c03004015000205032504807038000d8043c601c0c111601c501116824004035031032040c0000390005200108000560a0400c1003d50103409903505042008059030102c2c0d121b210001c440317810a003c5080311040000c1200d03445050303180c034030040d00c2c0103401842c52540b000100c110302c4d5081000c0c0c40000441c2c190070396403507601000b0001b20061030480307a00081d15155001159100000c03c84070640d800150401001419070b8818900e6000b40f00b1010800c85044155800140c010810040c080c02001140448403400c10304100a00505681c0c9001e546003c0b80310640b02d007245004400010100d418488001d01114a0a85c03181300c064055134040e00c181c2e01070303 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 858051169 1250 858049919 858049949
    0x50f0102060f07051806281d091e0703020a090509070e0d260d0b15030c0a090f08060601080a05010b0724090f170f12131209 55
    0x25031000c00d519100d0001288021029154843d040b10142c02c0041440e03080e0103685036a0605684500241003003504501d121803880d080c042820000e2803a074945507080c07026014440e1504140c00c1c14002140b681038400c50410b40d01c00040640b000710030b05007003102c1c0303400d034061045095141e0014814140e99803151031840b0794802c18002d488404596420000d21b8280c2103030210315003003a1f1088102d0140c10310307500780c000da02401c0392010070041e1410f41c2d1000005201c1c0b0882a540140326007001c048540e401400c102c5d0600300501d10006000342e00000d00003500b184528020000b11000d01807100b1058409500c80c541d090b6166001d40c0c0b41400b1170360007070006904180a0203614140c400e4a80c2e80e40c14080d0f540d94001014102034072480a6403540084568042d42522074032110a00522581141c40e034542001d01071810401d01d0584110010400460980170703d40882e4441c01e01001c0905c8a592030044425449400980c010500a5000705441401d90f20645007810794003652446465 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 858052419 1250 858051169 858051199
    0xa02090a06050a1205240c070312021803010b04050106200114010905240f010c17120124020312151201020a0e0604140103020f07062a02030324010908030d050105 71
    0x100d046801584091b00b02000004401c54003070005002c44505c00d04003400c4621120744c400702aa00004c070b0301c0c420b110040d050711025260901407200c036824250780800c569414070300001c00f6403103804100003600c05000b50480c100d031340951051b0721416407031200707041035610380060790007410050741c2000180d05020503034000101c441401401c014001405041011141001034540b40142c1300d007030310207182a00c00e03144ea0000c10801170540c4000120045c14540c14540c0c1c4100307513142400803040411070b0f280f46c0710880350004116400041c4199000203542c1d00c04c1c10300c02d018445d041e5600c0d00300c42010558500034805401038211300e01c00d03460b1800b46224034018029540502e1082915204420207460015400f90f4000c00b000c070601000076150502940b105c0d42610541034014203074030f095400100b15502d44441e100d0482c00144082c0d0701c1c4d800c0a0030920841040007c0e80049500035150034076142e0700841c055402004240305032602d800c0a407602500514091040341e01401c86d8803d0806 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 858053669 1250 858052419 858052453
    0xc0305061002060621160b0a020f0706090b0f04170105060f030c06030411011e170c27011e17161707090f091a0405090a02090a06050a1205 61
    0x8484d103005860540340411030304011200803505814110107014000500c0388542e800c45548000d016594030041d0b0320008204024604001d1061808094011440c1448805d43c045584011203c0854200b074a402080c80c03031880d144030303541c090860b40042a01c9282c0645041d0021441200101c4107606610f41041c140358881c84074840300c0d940b2420410003d8000f6041c41011070f900b40e01890034186d00310309031125800c0201d2242c0103038080b0300e04113102440241c0103000d00c0ea1017078030305080b41c0c1860ba03902c4640e016481e04103a144c000305d25503071102440340d20580c03000c0c0d0b0b5086200702e0040100c41e4002d000c1c2c1500020071a50100d54080030010741c05405880035a2100c000e03a5131208541e21500134158070b070f02e0002e80890104107181200090030001144203c003d0147e84400050802110807801403000c101030005004600f40360802580030b00201d02d560503641c0603a046110340c0d40d801a214014412034014907031001c00c849020880b840c64440c0d2200707051190080f100271a4000040d91 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 858054919 1250 858053669 858053671
    0x12030114040606020d05270303030f0a0b0102031354050907030209041401050117011a1f0c0b040b060310052206020d0609020c070909080d050c0408010c030506100206 73
    0x811810020141d64040038160000c487c0f90304000b91401c0016080004d046a005403120b08003840e401042c811310000510443c48500c000340010b520b0045000151081d82d10a80b00f58011002c0680740b06003e010010310080e8032903010f2000612180c211445408000d40508480000c40c004114154000c000341c4038240c02a100403009140003403940e802c00c460540001d004a8803031407030400008448500340901f0b07003e0003c20400c184070038150f10090f03084440401042e4089d95002c105403419413105043c0c2c6128a004104074a4194000031064401828140c4002c0042407000100300910144504141c0180c3c0b086054401c0300b201d40e680cbc203041d101c040d00e0140440c44e14005800e103034541c030250007103070fa8820134015003400301140a00c81154500c6c0d0000d074180c1c0d000100108000300510102003d840c1846040050308266180d83c82d090140070b12065810395a08081041c100984040e600107007000ba0080c011140c039030030003e01401c4295051405103581e95452a884c0340080340d4a = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 858056169 1250 858054919 858054943
    0x615120218060f160b04030e01081e0c09060408030c0d05030103050c040c030e0a06060e0916090b0f0a06120b04020f0706050613110702030d090e0c0702031203011404060602 76
    0x444281c0780401c1082c20341c030030000700d0007808040111000801d10710344001100c6026181c0a00186801c0c10701034909080c0c111241d04006030f100c204148404403241200f40d0850303d0402d8000c990300c10300001d0652055079100ba5001d00c0100d80015150000002085415020b00c2660480c003403d00c01075580c2c0c00f007800300a00a401858000c54282020707030115071403410910f00800d910301125852401c005408100f550304070744402040c0680d8200340034203034104490000a21024000080141e91114103015407542c19448218415259460001311105c0c030034010655a444e540d01c4401600005240070800d05882c04c228a08045107840c2c420381c0e5400c1c816425080c81c3c04003503942d400042100074412a849203e09002810035100c520070324090341401303c81c0703658412590040500d0311000600401c108941000300344845c86200f08000d4103c2040d041142d12409144002800c10100540914041b000880000364103040c181c480007428000761420810340352500f1040341c5603900e959034 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 858057419 1250 858056169 858056197
    0x807030b060d0606080607021515010c11060c0d09090207110108182d0606010c0209070504032f040b01020706200303010308030f09070518071206151202 67
    0x1000852032400526901034001000d200318540a5a2944101c51994000b40301c16403100c010004416010801d0300314401c80c3c038000e100c0c0317880d00002d003800c0ca0a03001049810844550030020400040300040c4500741c1004100e0380c0c0352501c00003425a00e9524480090005102031000284200d287c0300711a06203400140060254020748010f40b03110300041c1507621403150f03c000c00c5800ca101442141c03813100c0c144400c500240d04244400c072071070200c052601c4950308801d0078840542e0308182480c0000d581540e02d0b00590b0b5481e48140c405d03001c1c603400580203070051300c130111709002e40c007141c001e40c11007610f402c4480120110a000031541c6012002d405a80201024003c442c040d03201d0a101c07040c0030740c0401000e1901901e2070b041d03800c2a44206c41800002c010b001c4070f1111024480d40c4501008000c105040c03800001401c0c0c000401891038419881e240400e1180d0b01ca1940c51905082020060010a68a040045da82c00402e0000030016000603d068080c1c415402180c0c8027120040c1 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 858058669 1250 858057419 858057433
    0x9010f0e04230706090503010f0b0a12170c010c080a1b030209040b0a0f050a05090c0703050a030f05181b0d06020a0e030a26031303030e19082208 64
    0x9681070741c501c500d203141060b80c4180305010401007020048440605059520410381c00d18250902d42034405d003842d954001420b180d4051255150180e0900450b981700030308445250303803414500c900f4002450410b21138400044d480701c1c01c0005411190100c1b45960381c401a551341c40d480d080c22220705020041360303006810b8555203442d100e83c01030903401c0002017000628004540006400481d0b40e4000b422102088004120030315100101ca4000c0c0f1040d54400f0040c41c0c041034040c00c9d40f00f100d0006040c0600130400799002c1344642c0c4945c1d040e40c00420108458100082d100b41c80c3d07600081c0582c17082c411400d40e002e9111407500303c514100400b50071752030901031941e62070703010750440d603803030400c00900030300910141e40e080165818841c003ca482c00128800c080c400e00d050492810480e00d416010418400d100d141c03100c1034550140c00d4640010394070f0100504c00d05185505840350130613918440418184402c080050448c0b0445070280709d000c04401c118251012643c0c4103101103500609 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 858059919 1250 858058669 858058673
    0x1020415110c1e03100b030613021507060209130b100f0f08041412070519030503070309020a050406080309190f05270a0905011406130b0f090a0b09010f0e04 69
    0x8080114034003a20038640c03c80b09a0000441e28000340300140c0d00103c0e03164020340029080a020003038220501d005164080c501c250045007505001916501ea41140040d204080c000315a060b900c565000070031b1004003500b0b50b624030014000240c1c402e88200780e84246420340901901d0401c0e4184c0d11910b56400c00201450161280200204140c4107c410301d0110300c0359800a20140080450101039140c8401f1181802850216482c80c402c3c83e000c2d50b0070700032000c42d0304242500c0c1c0c0030882c2c2c80e000c15041110710204003130a010340e00250b0006e0411202051151011024041180c015a09095880c0a102c8440c4003061148107100a8404444050201381800c0c4213402ea000c4451524040b4600002080907201908903154102165668801010003800b0700801d260306003024170241d01d50030312100007084890300301c8415a00a079180000115900c030743e1005908007400400d03844c26460100049809410b507201854031032022000085412015540c20100b80c1d030f8001c0d0f510f9141d039515 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 858061169 1250 858059919 858059929
    0x151401051c0201030e0a0308041505072f060705091507020a17070f0b0901090b0c100c0201061802040f0518040803060d020303071a011211060d02120901020415110c 72
    0x80307001030341050f440303680340284440304204004c50302e4803980c2c45e4022807526007081100d211075211580c603203501b400309010000f94003070b514260640f103029003001109400300101e130b6100c03c092980d4105005000401c051584c01c180034000b00d00081d26a0075121101c0805102a80704031080294050560981800302820701101850301d80215000c0346c3c0099120f255943c440902c0303a0010841d120b00107013007651540d2203007074500107040152449081550250b0169101c0c404680181002036550340720700b031258400d400c103800070856050004640650810f5450103540140203002c41016401400079107130824006da08883c0503000c0c0541c002ea1541e80d01e48115620241c0050350060011240300301690b010700c0280112449403c09918074101c845a0340520b10313059100c0440e887c8078100900106110071200030903428200c5513143d2b200491a40f0f44002c4c02119a4410800c501b030b000c201e64001e05500500030f07102001c0a280a0380f510510840e00540d0301035413070312582c0003200c003e90f0600348 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 858062419 1250 858061169 858061219
    0x3152406030a052802040303030c1106061003060906090603060b10020303010605090a030b01182009090c04080316061a0d0f14030c0304173d0915140105 67
    0x30a20380c04c108000000c000301310300b600d5410303030340004e903000504008040e014803604801c0a0705c4d0400e10410400e200d5801e03168007000b00b185000d0001ea041c000f561520a80c4101c0c0070f0502d6140c00c100d03143e1910401d4009040c00d02003281d01620f0032400c12010b00e0500e80c08810b4941e150300843c550780c20000b003100c1540111028680011029401000040c2d6964605020b080e800350315038241c0540c070314140c09030f40ca14408030707015001044904528070034030422a000380c54203441d019503e0b2141041d01c0860321a80d40225514080881c200b106140c81200400e44d0398004c400902103108141111030724506100101c43e480402482d10b50006150200404601e6001e11410003420b810b54906500355445100f0700400e542000500380046403100c000c45200110384001044e00e65150aa10142c186031101011607d4505100c41803a40880020542d5103094807101800740c403071b01d0300c6c202c61085030010080d11000d082005260040170103031407290486130010000622426040418050840 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 858063669 1250 858062419 858062431
    0x612030d060f0b12010b070c1a0913090b010501050a110105070206041401051510030f090c05180402030d03090c0305030723060712230c0d0507180603180203152406030a05 75
    0x780800095501100d2801c2c000780e00d2781441081da030f44003820820071600448080407005604d085800800304802002a605664003824080d0f65000c02090a4a00b50305200110801c2e40c00c020400003a5039011038100d004512400c000c0c0341c0f04401046860994070105c03040b000f805880354017906903183c5001c5850b100d800d20304001584110408580043c2c032036100e03081d02c109622400401c07181c100104a001000611200d403100c90030981c1c0041d03104e9200b20101801c140c0c85882e8a07082c0b100e041c00131381c01540c2c03000480399602c0303076403070001c840003910301201c0c0c450034400b01a40b00155002c03d80c039103c1c4d020b503603406030500c00940c5e0002c0100ba1140c41c0d040303d0b400745101d00b00360180c10b00800e405110007804203522004090b4220007642c0c0001c0480d810000807510f550440c1401d40010002e5607032604012480c2652180e610300080c1c1c0304032019506100340c07017214540d44121019180102c9001500b24143d04204240c09444901201200e0300b10301b007000026001c1c3d00c140e03c0103401c01 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 858064919 1250 858063669 858063683
    0x110a0e070819022215140d150602100518061602030d09030c05010e0d05070b09210a1806090303030b0402130b040e01090908030f0612030d060f0b12010b07 68
    0x107a0740300c0310a00f01d03003100c40c0341c3c003940b005041c0492032a14482c20705401401840500d8a52911030003000340740b090085608501014040341d4080109a65001b501c080f085980b003030404640d440100a64a844040c81110f407507251001042c154015559640c5100750075100500741601c49800d0100e05614005000c3c04600081c0b240144050160044142090003560742d5140080e1508140e070845000c49840c103450380c0b12082c0c5486a503003043c159040246c02190300900c5a075003004a03800c00d100d05501500c00b00322209014542d611840141010207107030303511907041c40b410040460700b4840b00e000d00c0001c2070390244200002071107274100003008130000e440542441555441d00d00044900c0d004202800230120b011b000c403001d404281401032540351414000728615440304003440c032010f40780d00c101d0205000081c986032161100c030321000c00c0005c1220798a6010020040c01001c45000d00c01c070780014008000f0707611400c401501d0418003145450025a442c25030400d003503501c08042280c0f85 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 858066169 1250 858064919 858064951
    0xa05061f0e25020a12050d051e220f1a091209101803140d03110406080430170603190302160303090510050c101a060c0a110a0e0708 58
    0x45c80c02a012540e40c40c80d9142c55885403540201c3d032041d150000d0940c100f8011804100c429103454220440e0000c076161400c0c9903503002440d442c070f2203000d03003d0040d1010b03082114100400a007402340d0310005992064400e100c5c0c690044868440c0c0b03081d145440b190340180080310f16450482c2410b07a0300b03d140d042035000c10500041c180100c100d142d005035003110380050b0394201480700384082d445504461604100d490703090242ca011034025800348404110301c1e0030001d4104101c0c0514814248144146503500362820030040c0040c10450220f07000190107200c80788031910785565843c1c05080c0003070117040310200c00080e001c0003101a02c000e90440c0310b894603034245007900004000195000c0d50712010010f007013a06001450040d22402c00070400c0c20818503040007008122580c0d0116030b10f10114520002d0b810700320603086680c085540c0100005906030140100045e03100710a40718240007170000308074204100e010581445128480b00440c80041d0b43c007482881d01e168401420140c10000c = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 858067419 1250 858066169 858066173
    0x3120411010c050c011d0a0b0306100f08010e040303020d24060c020109170705060d0e0d11060a0f0209040204290c0d03050c130303020d111b04020c0a05061f0e25020a 73
    0x5288d200c1c1400c200300009100450a141d41c151104240700d0801200c14000c903c0014a0110144203551142d1034a0001c2010544240c0417600a403071040c20a20600308060804601c810020202840c40500000b0000d0110300610480718200d40507100da01c0050301d00706d00a02121194041c3d80c3e032034018480e0100b0255035030b5000d0400340b01a20030000303007812604001441e050104140c101444a00d9000d011031075000580d103a40110107100104803d001d14468401074048d00d01515031050010802003503500707c100703440c01303184840d52900c0340700d602502c6a0780c0c4a201c3c54044000603040028a640e01c41d020390029904440300c81e90b01490418116080c0d031002907241c200310016041020200341495000d1080c0c031150402c800034200ca142d8200c40c04042d40e031442c0c44030380078980201c0d0200c005034080c0070568400381c2141c240c0c0c80c1c0b86400e604c0900c03924400b000e000c02105c0c3c000c2c0082107010305c1380d186a02c110140c01c0a82c0e160100b24180d0089103a8542e40b50045203d00342d05100 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 858068669 1250 858067419 858067429
    0xf020307122006071e020f03191a0c070f03020712200301050c09010e01170406050108100b010c0b0406020904090b090d0c1109060a0803120411010c050c011d 69
    0x1c001e80100d510b8142e0107410b1156003400e079000c9615510450707092051002040302c0170384108020f1014140c4188142d45440880c45601c1c2500344141e01d40500144061b0045007021000b403114071813000c030780c0c088605c03126400e00300c80c041d034110404240038000d140005011050f0481c80724064011220b1f02c5070349412943d854520b4640813200100100400821121950121032800d002100244014902030882181501503140b8007410400240c070031001d164000c0b403404e0343d81d541582412026103800c0c10450041c140c00c0c801d0120340d1040b0026900d10585500c00e10350300001c140d41d21200b14550303498580c018a401303401074420650822403808144e89500c00c9241c028031a000814407454101d11503801d080303501100200f0300c1203c6290f1000160080d80350310810000725060300c40e5445600c0400e40203583c03038210018520000542ca075285040c0038003030784210320800c80d03540081c02410046800f507001480003481c96110902850256014004c03012086058400320101c02580a000030307 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 858069919 1250 858068669 858068699
    0x1505160e1807141c1e09020d06110c030313050c0303070c03120905061b060105060903072d080a020a062a03210506040506120d0503070903060911030609070b070f020307 74
    0x184d18950740e000c12071a00b80c2401c860031403c07420303010802c0704102c143c002c99030340301841c04c0c0142003d95640a80f9000600f15042d18840e1301c0b0300c1308036900d030f02e060148a04e5001d1844025189885480c0b60741c00c840c40c00000710b82046502c10b00071165079241d0303605c05108160340c18101c400d01996500118440e240c0d40b020341180480c01054001c20060f441907207041a8068005038050300081000205076100020340c202214044000000c01e40c2c1e000d411402c0c0c80b26030314503000311940c4107680042d802d000004c0034040c5038001c8520400e1184c0d101015105642c2401071100700b86c1007900507200505580d2a000c0d00c0e40c1c080d050038100d40948103108080c0b0341c24a0688204240d840080c0309680c10a031180640c4400191080d108e440c1100014950340c034419185907080000020004a4051107100c11f48020359114105002c9403000d89818299040326895050007449245d001848006000669100311132242d550380d03151148a031500d02c3c03c00880403044e40c1520490b000081c00c185104881 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 858071169 1250 858069919 858069967
    0x21e1509012a1b050109051203040902070c09050601051207030c020c10030c030f180b1e010b0705010f200d0207050d08090d0908191505160e180714 65
    0x30102c4039800b490240041040ca003a07100c22890b20080a01182c0d07000303020201691000c0b68054920240203039002e29521a540000e60641e0020920004000c451100301041e036080440c01d2101c0d035188001140c69000d40107800f089416540040340d000c5000341d0200c4010515881030350380345030403034010881300040410108002641c03204103903803183e03251083c0c100a2800715028049010944d048141c9405500303800390a03440300c1d40c0852000b800101c40034040501c079000601c002d695540303d40320ba0750840081943d40b9403c1035128880d031800c07071140500c0c0c45413440a08500184c0d2a842080c0c60f00b11882d00c44809908006a401103001040440312103586590703006002c0c0f6040400d24107000c0810381c10400c3c0545800d05001c00c1401040d6000001191010390344591410305088182c2c820300c5804220081c6000103001c50465080d18a04900d0469242c61107650202418800800c1c1da545204001c8041c0b10701068401d0f00c1410f4030029007252904460410a0316203486d03518942c240c0d86 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 858072419 1250 858071169 858071237
    0xf12050c010911100509060a08060112090605010609050910170f070e010807051008071d040e0604170c10020f0405030613060f06050102030d0b030313030f021e150901 73
    0x2031405490901440c4c11914450b2410b03504250b01600800d04600034680d02038180813a1800081c400d0740300710001e64100d00490414418801c2c3d0781003035802000700380122000070304030210100325410424101d40c020803940001081091808044034460800039426040c54001c0c1e0200480e036400400c0717200c1c0601407000441545502d0b01032003c0c60071003964810340c011607190b03119150321a0007070680e0f075101e41c8900340f200d541034100382c90345214035040590343e50143c0760107c1c0341c0c00c0c1d600001e0301c0c43c0b16600c038800800680482c245014000d008420b800341c4c03d58007680c05414540042d40103000070030a800e07021820640c03500002414102e003103a01890900c0f5015090040c0714445c0180b010364800703800200300305410400003e480e07104118104002c1034032501e52041c3d685040040f212940002d0480402090b2a842c01050080940800340e104841e0406410085c58652841c2540810000c0081414602d005d4411840343c005ea14081d060000401d20083d2810886003071036030310b0075076170300d = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 858073669 1250 858072419 858072443
    0x201050a23120a1805030a03151205010c0905061e07060608010507050c0d0e0d11030f010513030e0a050307051c06091101170613091110020706021005040f12050c0109 73
    0x260101240c805213110000e0342c05030b4a510b40861700c0407080f03420000c07681c03401054109001414581c4c1c1080d96008100304509051100140f002c10b620203400c00d01c81d903840c11a42c583c0c0b141040400d01400b40004e0901901907040710140545800030400e86200d21f0000c140783e66100220707821614100d0380361001c140001620840ca52040c441010f940075141080410801d40f10042541e03c2e51110005001c0b0040ea40007000039a400c1200900c1e0240c040c00034800d031301c0e0030388030b0520701d966030b2034202e01140300c110300d000c1c15152107140c543c140c690180c001d0000c0742ca00307010484000426032910a10b001f2500003000403a8080c01010700084c041e89591580b84900d100044c60740080050f100f0306043e900f001d00c00e5907a2050320307210144004260104000c01581802408400c81c0c100b000d5002d1490354040c0c42c441e4001c11800c0444e245502a548043c00303410842c010b59800326401080b02140783d0000c00051010744104004205520f4698244407071894424210740c0c80200036500f14202c48 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 858074919 1250 858073669 858073681
    0x307230406150f051201031103100c021c03050103080d090f1514010b07020d02040c030e011505010f1407030c0f080720031b130902060a11190201050a2312 68
    0x101c1c0308698400b91900030300c1d102d4030884e1054001e45c103020041c04410603889140841d0b4040160600d0480400000c0240000c006006076450a00c0d414840174a261002d104420030b000303110305412250070840840c0392200480e1210f000f0220010b085400c0800c840401010078540f40140d20815008400002d42510720f1078100b942540503070205009450030840440181c0b201c000104200d50f0544001c034a176a80c03044140d01410000d0724407a0030390701e06046a02026003c08032802140c60070789803c4c08071106880c0c12200c21003003031a04011418104603203c00207104a5a1040703a600401c0310303d039242c0c0a603481500a07800320006854014845100d95640201000707001d201d048128010a07590038002c2d002080782c1ca25070070292203010324140480a04015400600009038000d107010366070740c1c01100c0a4018a00205101d07441c1c03140900c2c0a0401030401e440a08840d0140c56071810424840c100b201c091240c240a2164840c005030311207e140004800380c41c61060b01640d03508189050 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 858076169 1250 858074919 858074927
    0x80c0315070c120e3d1101020a0e040506030f07141305070302030a0e07050a0e0604021b0a11032e06350105040b180a021302040518010302030723040615 67
    0x16914800c1c0c542c01c01d00080305071700c0c1448103222800c041d0b55a1240c600540103486001c9107914034090740d40000b035019890741e4066214440c2a8080740d04000c1500c404007803603038400078044e05005940c030481040c004689400c54103110078000506e802c049407140b400c1001540c0b02510040007290f004802d019070b03040c43e03019015400100100504072680351500086420406109a8900c0444c1101290494407240c04451501c0001c00714040ca84002d285d9203075446c48030100c1942c08102c0003158035a02e190100d041102c861041400c1c4150f150004005519040d21001100c945a9550800515402d031481c2c9110850318200d2402c0440d0710403129a034440191240182d078503450302c1e0070000000c41d003914590b080301e403041c114041881100d031035619140d0201c50107544a840001c203485803a841e5002802520302c1541c18098a800c50f041c4202c41c61403e0000030351603045102c0501c880c100c80141074026074150090082c40e618000c2c0881c0c21554540c00a6210491015140c00c04a401c = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 858077419 1250 858076169 858076189
    0xf0c0a0b15010804050601060507111806010908070602060a0b0d0605090303010f0e0903040b0c1002120a1a01020c040e0a0215180d050a1b0e0a060609080c0315070c120e 74
    0xc282405002494140d1720b407900c8090501407e0107020010465005001ca00764460f0f11002c4c020f8840c00c803000d00ea00700100c90160071114940002d6a8003400b240801010030207204548682c1c0041c030140d2150f05612000e40040398245400c0f00c414080000483c610b0301607a0b0041900c2c00140d5a01d5042243c01030402400d60440518a06514180441d4032000411607089421060a0a817148103008000c0e052013a043c0c0911034150000c5140700401d040c2641150280014000821144c042000d4080c0d00c090780608182c09600940c500010b00c0c04c00fa00600c1c0c000c01074000b55003561000364000703441e05000b0001c01440000101d01c0c8a1900082c284180e000c2c1c00443d160850259550790b01aa41c00d1821802007088200c0c01e1401201c54503660b114028227441c00754010540707060000380340101800d1013180d0000309038074400107540d200414a4104200e02402804001e05607080d0342c004540042c20b540e04000c0d05100401c0801e600e00458615220190f42d0794904c0b500da42d08020701005 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 858078669 1250 858077419 858077461
    0x30c08060102070515300106030b0103181104110f03060f01110d1112030406090203100c0c1103070b0c0601081b0612190204060309031701080a080f0c0a0b 68
    0x8400582400303d40d480c10b004101c40d0f42017110056075a00070301c00c1c0041d19043e03903800740003600e6480b608105980f207101d00b803410782d461740d0360401c03240340c518004600b51010250810b8441004881e00400300d0101d0360f0041800034003810110f0b4004002d035024006902460700c207000504040140003061510710400e064503082464107800f0400000c140340d84419544941c0810b10620038905035070f0344011300c2580183e10020401f07640720324003818060041c001164040340321b8010b0510000b0341c10034500c60a8498107207135988880e68078007550b0340114540e045004550511a806000403181c0c4c5030070040005801a0b0041d01d250b5251411462070600700000d8000d002081c6805090261264000e0b01c0540e980c404020b0052b480308030403240020380c003000c05540340f800014007040c01354040d000394420601c00d40e2107417030102221a080a0b0500f0a003e64412904440a082c0224500c40040c000740c649644c5032510b040c412155040c5002034017042202c1c04601c90080003650111034400e294512 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 858079919 1250 858078669 858078673
    0x50f010e030f0d030f110f03131a04030f18090e0102070204060306140a060305030a030c1e05180108150d0201051b07050108130b04060509070503070b0c01180c090506060c010507030c08060102 84
    0x1441b11a4408540664050b200e08110301000103116400007150141000350404403946101e0262101c03403401000072141500441e1050201d005120712898003801e50314081001100560304090400d000b07045080056801590240309100c00359032203201d90710080d072082c500003e081e000455460f50440006140c020020724000f000c0000c01c0000c41150108280c5140000f000c0c000410140ca00b0050381c0c510203084151455801c141da5080740080030009299101d40c98284912001140c08180c1101c4e0ba03085640c0000e0b2000503801d000410074000c42c414142a810a89441c1c0c50b41d04a15a031420040715a00408040042e5604090015009064000b022130b040c250f0344c884c3d1040c80e00c003400c010145565800010341441e01803000710098440102038a0801d5035912803045c2c19004001d80040a51034002c80900402c14115809403c0380d000c12144103071442c2a072000020003000b012244c01040030084c0c544800c80030f1203081d101c3c2081ea1400507900c030038513100412940d0b008010314195 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 858081169 1250 858079919 858079931
    0x5100903171801090605040920360120031e0403110402030403170402030705061206090c0403051011040f0b0703030510050604090908161a060613050f010e030f0d030f 73
    0x22550150440301519078208e0049940300c002c1c030112101c6004549007a1004501103000d100e02450a00420641421020341d10711061808040c08819484115820b02040392000c0d01801da1140c50840950111f1700310580e414002a0b9400f124100005080740c802120000380601c104450b9454040a808081d2011815850701c0d5501070301d001c4aa4144003001c207030180012702150f408004850181c44090001c0d03071500c2c102052068114019074000e48500c002c20001021301300c80d8810354049035040402040c01d8020201d60b10700400250000306c2083c04208400315424010103440c40003402013190490707644845042c024101c170750140c100400300d0008241044159145000e541c02c0d110704910000300405a46441c0d85540320742d208102050300c619001e0400d000035000300d00326104070550041c0d260f036101002c1080910a05029170700b1072450440c14011410709100e003504d000c206040c4680e02200a200003450004200c0e00c075062544022031050001d541405a0421030340100740501203 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 858082419 1250 858081169 858081179
    0xf090a06150c03080702280f12121a011403150d0b09010b030f030f090315040602070c08010902031b010e0d2f030307020607030c0b0115110f070510090317180109 71
    0x1444001803804c81e080000c0400c0030301800488c0c9403c0c00303050742c0200388007a244850100074003208a00f03544600c80b0341c40e25a0082c3c0c00040036002e0180401c0c16910355103200d20103450240d482d003014050b1180d80c1c0c42d440f2802040d40702c240c0300510743c50242c0030302c07126490224040e9094510101c0000d0007500121641c00b81ca0100109071407404491914450325890054046458102c80b6103128955144507010302083c0702c4254000c0c96840d00400100d50400d40b44c1e401103085e43d581c1d000c000c4d0182d0042d002c100e00c0c3c0000b00a0001c080f02c05260121500109400260901c00011426a03c18040580141400580809665003007810481d040c0010b40e84000080e200d00425801038080c4000085c4a020540301d40d9403130f071085520001d058241e50716614a1810300900003000000b040c0614032049040c44005030100f00600e01c180107240030744c00c00c01404421106183e0b00f0041c80b07406c04000c000217821400e00ba140c035038a2002d071600c5000b0f100940d10814216070503141840b05082c02441 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 858083669 1250 858082419 858082453
    0x605071d06031801020403202d010309020d12020607170f091c03140c0f1c020c0304060225030c1203051611040501140f090a06150c03080702 62
    0x806140464100782c482c0d50704400e110203400240c88110300c0754070000d0040b0400c607800074aa0240f142c00c401c00c01804020074144543e06072515021007015031002c400d86000801a1a0615100c6d418540842c00c08050380c04520b00c800518003c690402c0c01c8009031089580c1009440d80c40061f51500e100074101402c0404020840034001030121125900040c80b8a4030030417000101001c54042420305d2001880c0040c001e0455255191401c00e2020104840118030b405581640d91008075441c80d03c564403240c01c049020401c1d42450098090017032118014003030020b80010200307a005411410340180080c580c0c0c07181e04a040a00311400344040c404aa441006030040e114100324418000110742410345844c041c2d9080c940580303600c0c000b075808101081900d00c4858006443c140841c0c0d8903240e805c0440c480050081c2d4110b02c07510f41d403060314501840034542266a4040c0041c00340d407115000c03d490140351031108080f842401c803000400d85d1188490354012010701c050041c142441410107 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 858084919 1250 858083669 858083717
    0x3051c051e10080307030c110102010501050604053309040f0203041e050a02040614100e090720060c0702151306050703031410090e0a0b06151c09060507 67
    0x803407076040001030240c02ca160050301c00740407600220381c0c903145e191400504003482040100d801904101c2c540c081035005004060503150024107140c03d0508103002c0c48411911491010454010340501c0c904182c0d82c048900d405201001c80c403541c8a404c07109000640380c0180038086114030410400010401d582d00c4441030340140c0142284050682c203200c1d2504e151900060350080c43c2c00710001d901c00c0d56203000f40207150242c07451948103a000c0c0b0251100e28080390400c0d001700a40f00040c4900c0d21032010301810201c8994003460324040314034014036213481251420b9003400b001601c2402c0d86031207001600441a400341c100e15103414030a01d0b081e060813034843c2400313104010503036004144c0217422644990142c41410700580c50032503032400100b00c0c2ca200d0318640610740075020b407200d0008103030340c1070003500300140450680703600c1d040c00b03c00b05c04160310416180c0140080f0000d0b001541c22030098a520b49804104032078242405400c8800144c050000d1000360014031078140349180200b = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 858086169 1250 858084919 858084961
    0x120c0f02010e0a2607060c030207140f07030809120a0f17030c0f181905010806010c050714060f1222150b0102030c010608071829040f02030403051c05 66
    0x107140a0f1000d0044204e40d0090510080040703050500c104503899055010700065400703010f10250454081002a8950b010240303c2010b90704104800d102140e1420014101c80702d001d00380310206a54a507015080403911801140e807000b03000140c0c418050707000003042040e000c00101c1c500c2e5040094501150b80300300c0140060b8000c010a002552460740c02d00461070100103000b40c2c41c800003102c3c2281501c0000d0051707a0100b1081c1c000b25100d0351107586403851f4107034000020000b40e810900b882d1441da00300f00c80281d0114040042618040d1910094a100c001c9081001e040f03050162004a40f22003074100301e0072142e11120b6401c00f217200f100f500340c000203000c44006180811000101d003144110300300e0380c0456007000400240400001240380c00c4802c0711811001c01c40c0061481d41c2505d50b02c000f8500e4124210102e40c40089140380d144902a0000f400025406440c10781d841c10f1f80c0048405a01180d80030400c4160856190301040b00301d8501c00701003000e458502507201440d1040180 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 858087419 1250 858086169 858086213
    0x506040b0415031e0c090e0a02120708060d02010305060a050a03080c1c080f10030818040e0a0309060f020313090203060f0405010303120e01020c0a0503130608091903120c0f02010e0a 80
    0xb400e110b050242d19000d0140c4407c1b140d803c903030711b40320100c00e001c0d6000c0c00c0381560442192000959403486070300114003a09005011038005511600110003400010300640d50001b444800014250354010010303000b1441412020b0311900942c0d582400d00c008400e10001545003001074121141d40001d1061b48003003a200d540781591116002035400079156003005103011000103803503c0a5001121036059020100d500b441140c068000c882e8544a40c1c21008011540f0003030140444c030300850011000110501c1284e040c607040c0b40300b401e078030340480d40140e085660000034401141404600340c0e14a46027981c05002ca549107a400509a042c015449403500d039071391a014000c05000c0d0112800d0140840817660144500e080144d01c950080e11004003801c64443d0001e2441c1c0501d50303951042049034003801760102c480b00d094108850464048040200411002103050700c184140000440140d8030000300c000c2d00b1780d0180c2103401c0011070751915440b200c101c0c40015441014442c10043c0c09407 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 858088669 1250 858087419 858087431
    0x50913051e0f15090712020a14010c06020a08040212012003071407060507110706050301090906060e040c080f0102090d111903150c1b14070506040b0415031e 69
    0x850a420b080300081c004456004100608100c200c008003140e018803842010340b0b03041035032480d85803041e83c4007000082d00134039003d00410020144528107031103000c06040441c2ea990f1903603128030072079008122140105178088140015810031894400140c00510b00810014801c45c4604408010401c05a41e071584000000340c06a886820000220001d4813070722921821030b031910030050304003240c0c51000508440104040e030800010544100d9030705480d0386203940d0801c01e001d00074025000d010b4580390345450b00094868030b1100481d1041e805940040201420b1009450400150235404003540c1e0050049444c10341c0c600b4902082190300c42950103070b4007010008650080300240c04200540c0f0b002a0000074822007030070004902900910410003011311000584103602000e000d00038448000110000240d000240c0f035103154255421940050b40e43c0d0005582e650064000ca501d04801103800c2045207a56124a054004141401c0c85400700e8081d41c0b080d101e445420440515032590 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 858089919 1250 858088669 858088723
    0x16050703170601110106030c080f010204030c1404060512010b01030509010c02070b070507090509030403052e09020d240b040c14030a060918050606010914131103070905091305 77
    0x220103103040d14840c10090040c16528100544c818888d80b00d440341d030f0f000700315100a010b141842110305880d0300401c038000c0c2c0c07800d01040c2c05d00049490b07901904140c0c2c6d00e101082c1c41d5520b1481d00b03c000c10103400441c00c0c0d200f200006043d2080500101c0140c0e0500c4912900e50341c0118100f07099811400009440e0f18090030040d10303200d4540d105105040c43d140a011902c10084010400c1c0c2e400340c1c040366070506602182c0020801c3d1101c002c0c00f00f0421340c411840c13101c0960407002c6800e000400007161014a515260708204100d000144c1c018903451820681080d18020006800c40032030381008410030399803000e465050a0911380c0207103840000040c00340b0115a000d03101500b00d1420420803040400034501c1c0f00e010003401903030148180030001d0101d6205007500d41c00c0c2c07504545030f001c00c034003a1400c5c00340240031840c8045501c0e440c1c1983c052403261030700185104d200103a44e20300400d8604400c0c0101404080c000e0303204180001c01c0c890200d040010020b00d0681c480380340360050b040380 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 858091169 1250 858089919 858089927
    0x5060c010b0a08061f060f030513021005180901030f0b181209090c1c020f04030203100f061d070e040e060a2a0c02060304050102040f030b16050703170601 68
    0x45038103501498102c2c001c070f410b610010b003491040b003a00302040c0c19208801c800c1c08500105101c2d120000d298040d6114840e40f01c4e0b003096801101c4c1d03401e455400380c8164002442c415000034910f0000700041045001d140d452030680c00020400d45500320554115125000080801e5101a144800d8000814811a0343c401c00c05401c41e0400103442c0c41c1c1c80c81c82040420741d40a00c640b50301c80c0e01c1901c00300e0140b0070503d04841030045480421403c0104c411030b00d001a40200b02c090b50310b181d0a02000002d61020301a0808402c42040006800e00081003000110f640342c2d040702400191020360702d00720141c8800d1854000c1d54604114000720400000036010b02142d0710a0400343c000c040c1070190194064119201094100032189500303090b4960074404c6c480601a15800104c02c04509405801d0a000450f00940a100054a0306403145044000ba10b4981c0c0101d40d490041c4080084100b180b405a0880c4c2c081c0d460007600d000340e5602c00900724007041200030343e0102210301080d26603000e = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 858092419 1250 858091169 858091181
    0x11060c0109061e140a200a0806041a031504140d0908010f06031e0221060f060906130908040e01030c080118110603310203010b06092428180f05060c01 66
    0x2d0a80403551030390015030080190302c09a034618065810014504036a5650449400781624040c0040dc841000c00c604000d14400180003a00c0b2100051480c84040d8000d01000606a15030340b1800140c0b4a4040340d603003102c0070a161030310382502d030080c1800002c0c45104099409011910184140c500c1400000c10180038800c03004104d282c1d509000b4080e4001085907889021040c054215a599040c1032020001d01101c0c400d80c05014540000c10020080c1e0290000c1400380b2221410591a075240f011041c100783c109840d008000d007420842c8460074044c5880b405031000740180d046005a556443d8441183d00e100d1003110b0100005400d021045d280030310101d0814191942400e1241c0f84120000f5a07900a0f4003c2d400c00b440003002d82000e10485258100c064404500100354840b40c0c00740742e030007403822503d00b9000c01c41440520070388641c1c910320841c0341000340d07180c42201101811281040300040007281c4d4000c0704219908003c980071080314002c2c3d865a0f41c5890801c07241d401480 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 858093525 1106 858092419 858092471
    0x1215130501021e0433030f2306030c0102031207052a060f071110021c0614010f021911060c0109061e140a 47
    0x8958610000140200001410b00c41c030381c030488060a40e50020780010120114051000c084c800a14011200d640f0180001d100e80000603401e98120812800301810390703c0b030309001005401d400646010b401c0010403642c00c0740140349060080c5082d04c0940c060f204200c1000981e50000048501090350011414266070f20440110b80d1540000803c6074011030301034581402500c80400106000d4194001d4100b80c540680600c8841d00010f000c0020041450a00103840c04040b416481d40c03100882d000d070741d0707410140d0008060307403100140b048160310308500000e103070082400d4504092803d90b01d9000d40080040d007281c0e80c0070032521021f0744076040021013001800f40c00c207501d42008050f20f1582000198501035085800c4e4010549000d51078403c5111208480c030910b011160040e8002c010754058010044a0310f60000e29010301a039035083c0e0303000300034551030844d11255 = true := by decide +kernel

theorem cover : BRFrame.Cov 857913669 858093525 := by
  have h0 := BRFrame.cov_init 857913669
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857913669 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857913669 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857913669 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857913669 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857913669 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857913669 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857913669 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857913669 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857913669 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857913669 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857913669 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857913669 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857913669 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857913669 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857913669 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857913669 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857913669 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857913669 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857913669 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857913669 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857913669 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857913669 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857913669 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857913669 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857913669 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857913669 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857913669 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857913669 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857913669 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857913669 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857913669 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857913669 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857913669 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857913669 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857913669 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857913669 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857913669 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857913669 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857913669 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857913669 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857913669 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857913669 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857913669 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857913669 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857913669 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857913669 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857913669 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857913669 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857913669 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857913669 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857913669 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857913669 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857913669 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857913669 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857913669 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857913669 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857913669 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857913669 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857913669 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857913669 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857913669 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857913669 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857913669 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857913669 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857913669 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857913669 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857913669 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857913669 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857913669 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857913669 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857913669 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857913669 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857913669 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857913669 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857913669 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857913669 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857913669 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857913669 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857913669 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857913669 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857913669 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857913669 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857913669 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857913669 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857913669 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857913669 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857913669 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857913669 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857913669 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857913669 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857913669 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857913669 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857913669 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857913669 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857913669 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857913669 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857913669 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857913669 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857913669 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857913669 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857913669 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857913669 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857913669 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857913669 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857913669 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857913669 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857913669 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857913669 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857913669 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857913669 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857913669 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857913669 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857913669 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857913669 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857913669 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857913669 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857913669 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857913669 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857913669 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857913669 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857913669 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857913669 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857913669 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857913669 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857913669 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857913669 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857913669 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857913669 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857913669 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857913669 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857913669 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857913669 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857913669 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857913669 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857913669 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857913669 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857913669 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857913669 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857913669 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857913669 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857913669 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857913669 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857913669 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857913669 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 857913669 ≤ n) (h2 : n < 858093525) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
