-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0232
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T18:37:53.884132+00:00
-- url     : https://prove2.me/submissions/463b07db-5103-4aee-b609-a8c3db00e78a

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 41546767 ≤ n < 41726623 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 41548017 1250 41546767 41546773
    0x803030c030a11030a020307080f070f0302070218042a0f06031a031002040f0b0708090609120706080a0b06030603070b090d020402070c06090501110c010305070c080304120f020c0102 80
    0x18261038158000c0d507070001a80c40c0c045141040d003c0198660b5000301d8a4030002607000c028406800d501c022820303444013507201000c1c124206568058940031a00b0803907010190009070400442d2503a8007406007040406000100034106850a81003103080d05400f0040c000e4032000070a0080d00c40c00c1e04d0011620000d0450040c6414200100c000d4818001407415009103446002c580e51000c211100078044100c4006807a40e0801c807504125003040c0d0b02500a48409100d0107000c0fa401200315207515000315010380e0f4820340e1038086106814a454601407a00903c100091210b80046035107216a194150030003042100c030b0304008981c0001c0d02c1240c1c150303100c1c450038841c41194500410003580020a280c49101299001a003070b0790100340d044414441c40c4000300200381e00310001d200a0b11003400c001e2490402120302039500d00040e44c10b10304040d25203012a6000d40110f002c55960394002da480c0d0ba50345824105000100741d107011640018003d0800d24088620126140c000e070700c016409 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 41549267 1250 41548017 41548021
    0x19080c03150f0402040207050d0c030e0103020a0e060315090406020d3c0f060603090c0e0c0f090604051305060307050102071505031f0f030b150f090a15080c03060907080303 76
    0x8040b100d4a000384120782181d820441a00814010070124009901079618066000500d00d0001d01d01440c3c2c00d6070354107250050244002c0c2c1504400004070201081c0c90543d100c0e51903180d4800c030f4220010110350820000801c0c070050104a40040002c4c0c48860030031300001c4003407902e98800c1050641207220002002a110400308419000080f038028424800b1802800944d08002224007550041011070b0f0784071030400030803584001c0341008010b074210409842c9440044254070f80300e16111a031418500003144683c5540312400d58025040c058400e83c246e942c104502c0c002090280ca080d84a0310800310000b40a40c40015803105461550003010314000001c1e109540b02c1e000900100b0071200c0710700e1208008401c10395080c008214401789601000d2443c1400c8000183c0540304844070180c0309890101503c40b113140e00303200f45040da10280b0030b5440c007031039030010000004003a0300d24046080c00242c119002400350b0211004506031019601e840715030070f030340d0001d611400d6226001800 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 41550517 1250 41549267 41549281
    0xa0318020109060c0c0504180501110306100c06090507120b09010504120e03010905061003170414090601020307060e010510140a09050c04030c032027100519080c0315 73
    0x13801d10b8076441501c1d1a5040d546500000f000e864404401248840c0214a000140042401103500d0100031000c410324506100c8045002c2800c18031021050000c4220703510f08010103940642c011580181c151403156071900c030340341035010300c2050a903402003100b0085240441c06101b21405194000154501d00c2c846003001d54440c00c010035030070707815560ad94030000420028001072f81b00d101410015000c00f030851505811848040d084440c00c1d09040c40280514400d0f241440c1110a0841c0c00c4003190f070355440101c0c510b1245081c0202a0b80c10401c0c0070108680c1500054040d414031142d20f42e4045d22040500e018480d074004242c4e000300702c00d90400c10f100c55a804242c1000e1100c50080c07900d034503502c6085072803502c2d610032600c65050320303c0101f89411090344007592403002c071011039030754554a5a40705c00c0d0441d8150320920b004950003082840c030700000c0b0580144009040741e01020b07030030141c441d00540c0510a02038140144070041c00946004103690101d288070914416082d26542 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 41551767 1250 41550517 41550527
    0x50a080106140409050a0c0306170a08030a0f090302071410050906090a0b0309031e0403080d150f03060209090f040c03030503091204030605070e0a0602070b0306060714030a031802010906 82
    0x310b0302c07555840100b00c0410004628000c0351703c5000950000306003100200030040490b042640000154190420b24101030b41e0081001541d45801c002c06581700d88483c000240207094407501c40b4007091400304a4410590007242d504221003c134110000c2044c480000e005081040310700302c10002e4020441c1200511f040c0780035090081000c2c0c04207515035100d4030030019561040c0c0324081d481c0c1c004660840c0074101c010b200e881c100b02492400d0304043c610b584140710b03401150101610503840c0c2d20814090800340007050020801e07422001c180315660b00300f9500951184030064000c070540b00000300d1141001a1a900850303004850b80c01c0a81303140c804807101e4001402c4807089000b032000e03900c0c203041c080c0c01420180d4010f14000580b0700b04220090a10451100040e0164840001c200142d64011030203a00700c0300d8190441d50740303949100c0094010b01c00c00e4030040c03058260700703c400d6132500c1c0000035000507038098404010080039200b103500a200801c00090000d8070780b44060103000e00c91 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 41553017 1250 41551767 41551787
    0xf0e16170307060f060816080c0102010b0d03030b0d0803010f0303030e0106050609010c0312090809040b0d0c051203090303040b0c0f0705060403060b0409020a0602060702011112130804080105071d01050a080106 92
    0x10000003405c40e40b41c0d2061030038802c0c0c4144003101200e01c0d1009002071602401103011a150900003001005460404280c1a94410700c0c00340074113680d2501e15840d519004000648964060b411a98175a11071140811403103d9000c1500040c0c41c00103155000c5105104090503101c00030611820009c840300111103044211038101d04010390161700345006a045d0140c2e403003640c82206826201d41d40c00091108884090032003a2081140140300c4002c203118900500517076105aa506030368510101c0014518410044195010b100005d0001a00c002c1e14018108440d10001540e00030680b42000030b41e01d001c02e000c0c0c3ca078810410070003000001c40070340c0300006c0800b010b0000700c0c91103259000610303000c0c041c0e0321040c00b40c0c00036410405400e0f0b0a20442d03202c514402c803070504101c1c40078500244000000d02d80c41103031314040118030500055406690003015928000e00c0f0038584000010410801c3c556040d5a0142038250400030798003450607198841079980e6440306030303880c10b02e040b600102c0b4 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 41554267 1250 41553017 41553041
    0x12030504080a151404170f040b03130201030c050406020303070e040e0f0a0b0a0207080301030809060c0d0903110109030308060f0a0911090a080f03030a0e010f0e1617030706 76
    0xc0000080a4405000030030740d060007110180b01c1c0240562000050342c4840d043d110f0318444000400001a003e0b0703104030041451070600d2a102c007030840764100c00e4440d41d081228400400f00421003c5100e86602c8200c09100b030345c040c421204507000950b40c41c044c038011000540c0042c4005510280714030b4110001800040c008540140740c403800e582090b10341403071000309404c010f5a6400340b207408042c89800c0450300100b1841d00b8441d4440c64201c1c013040c08020064500043d425880b0355513074081c0e03017043c501c00065401e003800b220009030007003090b031000300c48450f080011681e10358080e4002e50104c035056154503200d03540741002c1005405050803440d51240c0d07500004201002144500301b616030400b210b903640d90101d42c1c02c10820340090b07403150340c0681c8480c0340340142c11800710940c0d070004210540800c01c00e2084803068090301c031503011010801d00e007400322451150001620304510100c0d201000c102500d51001d1000a4030311091140e165000700a0300c3e000402c0b980c08410001c0c0 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 41555517 1250 41554267 41554277
    0x301020a080a0b031f0507030506010810030201080a09060203100f09020f0904050912040b040e1006090b03100e0c070b1006021209030709060801051801020405010905010c150906020d0e0a0b011203 86
    0xc9250140c2840c150039000c1405d4159445d81080b001c40e030144a00ca0b0040307030034206407842c0d1802d05c2000f05020402c0c04001e041088540108202c5a00e50300000103442d0f00242c295202e1900c0b29950596290700c0c4200c4d0803160319840006445035840c400c840b40c0c03061010320380d450300286509000180001030010300c89807203000e411845e910f4101c40034001600c442d075981c580d00c6240601d0068000c101401c035290550f142401000710981100c084c1c3c0844208a00e00c50f01c07551201e1a0204d01c1c02d413a4055800e401c42581044008a003200040824074410050701c2110f0310381600a01c1425407d006000160340655241e020ac0041d41014100401000741241d070303100d48a41d1584203541036540486480e0f9100e0092000600701c04100c111001c035464001c500341890240020400b900511030741e8140421680e8150920255484602e0354280e0003800b404103180030b20709100298044011302280b0b0b0701c0d115011400c20b01c0410b40c400e005070840224003259007040f9907400d00e142c8042040703040c06 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 41556767 1250 41555517 41555533
    0x70203120f01030b060904050a06050a0e010b0307260a0c06030b010906051201060509120109140601080a20040605060a08060118030f080919080a061401051e04020418020403060b0301020a080a0b03 86
    0x25140707004003481541c0803080403443c0514101300c20300f5200c0c1c080d0800d00c03940010509200419400301c0801100c44d00e0061781c8103550380245054141095810098a40d50000354041057090309034020003c03010086c0e1300c03038042d03d554010480340d9014940e40d1b091026081d4004100d42ca1283c0c0c00b410642034000c012114107003007040d000d421940311100c210f4a0180c0343c02c0454400307034244070141c014a0410302400c1c4143c0e00b80d541001c80c140c606040a0100e01c1c0103000e107010307159030307200d2000341402402883d0303a0217000d000a4803294048031818005802d000d0009580c0d51619449000c032640003188180c840c8007555007a00d5078000503030058202e0390280c00c1021101d415910b20f070042c0544400384c20318400c5410540192002c5045044070342d020304004110584643c291207100042e401002140007a0000005029200741d51181a4500a0b00c0300b03c000752049174024000c0702d00c40c02e01040200d9044052509174000c00000b000800c0191002800d10b419940001c82081da00a064483c00 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 41558017 1250 41556767 41556773
    0x616020a0f0e04060b0103090308131509030e040c03060506040902071401020712020d0e1c0501090c080706110105010302030c1c05100207030305060a0311100e0603070203120f01030b060904050a 85
    0x782405034020300c0d080e04001c00307100521134680729400c9504401c2c030341030140c0f0f0800d44024040b920094003000501044243c400280030b08c203680c861200c0c540050900c115055410001c15508440c90994841c614022903240174070700911540c3e0031114040d00403800d051901146400079040004140c0c1c0c003c5100704450341e415020702c0100561441060f1030310300c10014100003413901048910a40600141280780c40041d55420302e0000303640e0070b454007004d03071466a16100e030141440d0712000704000085000410210310109035101690b009a64030908107005c01d00710307800e0b18400c0c40040c0d015007216070280c0c00c40c10490083c0d545c104001c0d4542828003010340e42d072881c201e065214007011030f031b010894404141d418010341c0e410034801c03581c20121070b0460302c07091940c1250750255482a1464107005c00902d001e81940d001003140100025100d00e04124041e460f6801801e081080090740c03000240b000303030b14041040c180d0f900050380e10541c4c0d84080a0040c00c14010b007080e10f03c0d100700b959040c00 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 41559267 1250 41558017 41558039
    0x230406080a080a021509100c05072f0301150e040812010306050609060607030207060f2a1a090a020d080405040f09060f021602060904060b030412090609050616020a 72
    0x100700e10400c08a80e4400f0300180090800081c000c10001d035401c807105000d6003e000140c26500e01e42400d10010b07002442d070b0740644052152540c0200881c0848021110744294a4020b9150b0701c0b8500c0f00204440040781090f0803074000b12007480c1e03041d060311424022111441c0c1895403040c400c11685207020803205a007030221501340d00495461b501c400c1005128144103d005030401401d40d141403d02000c1e40c0c1c0a92520510701079082001014078072030402510030030010801e0406030250110002c0c000000310410300803800c0c20359841000d061000381102803d0b114601c00d1186034050100400140e003003040c0804001e00c15034018000f80030105566030b80b4807401044000320500029591000d207480c034143d030300307002c9141e0241d44184520b40106130480601c2020642c101d1350140e0f070b0b00d41c4400040040c0f140d501b0204103602c0c080308120401508c180091104e0006407102c0c840c60360740b604100d960440f0781c00351701e812030024052154803201500383d010f41c0510042180030350300e440302d0718110 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 41560517 1250 41559267 41559283
    0x307060e0727151d040c0b040602030d050c041208030a0207080d09060b0405100302120a0501021b07080604021c0302070513020d0e0601060801030f0f0b07030603060b0a23040608 78
    0x19100c034807003100720034054502c83d0003889401201d80300039491a000c1004659007100741184048031040c00040c0400110f072559801410407141a5502c803900c40000943e04d400c6014103041d814502004180f0049030402550121a03c022007001c040312556141500c1d40c2000d4505000700b6024020080044c1c0c040003c0e104d80c0150000004112843c5d0400703500340c905050006000303e15120500504000b040f204905503034065503440748055186604600d414a100409040755201003141a03011340ea0140100005104504952026441d92006ea0310780c201a5402588141c40c810343d00d1215405c19000c422250103070045d504c0840d501c0010881d0003155500344a8001c0c0d002564074240d03061803241850402c40302000707021a40c10701802902801040c080500230404030b850442c10441941c00026403294086100c0d000307414600d1000c1d010302420f00044030304c1410048440c0581c14400003090844681c00b080b000e1141101704250611414003404503005a110760700032514050070403c0c40 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 41561767 1250 41560517 41560559
    0xa0b0a0c120e1003050f0c0c070308030114011202090f0f04021216170c0a0c0f1704050a060201020c060a050a0b0307030503130b070c030303020f09040e060106080105030d020307060e07 81
    0x20388110a42800c203c0031100030344055051519050920003240f1b007103001c41e94803248444140c4c3c2d84246d242d0415103810a6640010a581c8000001160080500780580c0410600381c0310800003450307004a2105901503c40380a400070100300948119141c00e030b0354440e4052024000602c1e06001a035818401e07013084070218041016510840241d66001a641d098052820000d20090810500c840c03214403e00400c01d0411210312040310501402d50758a4480d41e034840c003404413850301618840019005403082921611703440c000050394500600888003500e0018020301450340d19144080018040641894100c0f541c9800c0c503000c42e10200200e070050760184004540700d2224139502c01d42d007146600400390054050040034001031103541e02c401aa9418180540c50300415168504140104401d503540b1a0a200320b18808100110301070307050b221181ea40000d0350307803901c041c99501c0224a500d040160700c04c00c02d03080415140d0340b100079061700803801d031259107a50301c0f010360310181824104 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 41563017 1250 41561767 41561777
    0x81c0309050307031d0d020f210d0e0411030106080708040516080303060906040c0804030c11040204060e09070e010c06110d02070c08070f0501050f0a09030c0801140a0b0a0b0a0c12 79
    0x4100380c040f0118541444c11000c440c5101403103260340c080703240300c203523031080318010580b900100b403c0072a03480008840400300c400b1100f041c0a110001061003a40701d00c15800343e0314045801d152401060f084a040c0c40a90303d50704207680b1000c1040310f51203c01041039506000e000d40501c3e440c5814484140200159001551030742410800c10054520103030030380303106900e042041c002c125042048183d116425003002c50494ac3c2078100150701018544000354414800180030070025001140d40170300001c180c0d0b2180d100c0d941d0641c15103e034035101200c11b000c02d4549609100081680d08000429a055444a4142450002090145d80007850304491a0b0151001408401c0c801c0114000038150702079081142c0786000006801c0c0c0c030408892400b045400100041d01c2c9010380c0c9440000d5600070b6000c5541e41d50f6092541c020301c00f01d05074040c20f5242a010074040440360251b0603001c00010041200e161400303001c0c00965009c0a9810240000030070804e002c101b00b40c1c1d06e001070842c0c2d5156 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 41564267 1250 41563017 41563037
    0x3010c0f0513051315050406080a030f1101090b010315060e0a0b0f030604030507211403040501090c030c06020f01020f160f080f030105010f03090c060f02030c0a140610081c030905030703 82
    0x30000000201d03001b0602480c9001010030540c2400194141c2460f01820640a071410130700b07007181c504607055404126923080c4038202d010800e02680c400c0c1241c2c0903804251820240d44104801c3c2c40d01031007888020340d18100840c00764526588040c020460007401e000c01f201c008404a4101141154140d01141c0c000c03550b0002e0088589100d5001003542010407000c8440000280c50400e4612002e0044403000c80014200102503218000e400c0c0c0100e686070205543c1e160039200c01b4068051b40c401030044041d41c0220f90014002e8038040d0511501841c01e1004042c040701c0b4844141c2c1040e03980201030780fa0200030840241c010a5400390180d0416607945c100300002d06404100504041017626011407500400c0f1007401c030105a0f0300e6450101003034400c4c032204a140d801411080c822a00550460034100417071408049120220401a40c1141c0d841a070a00600c4404e0710808405800c800d0f105001c2c0c0c0401140488549014200020503105a0302d540d417030758022110489c04640316001c = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 41565517 1250 41564267 41564291
    0xa150e07051b0a020a0e0405030f030406111c0c0201060303020303042006030705091e0f090403050f0a02011d070b041e09020a0e0316051804050307021c1103010c0f05130513 76
    0x503170b00014000040c2c0c032034840c1c285551402e030b40307100d1280c11002d0207001102140c10440320350001e0380c843e41703200005a166041000701e0a03982c51310031000310789d00d841c00305020512030060190004480d0550055415642caa0b1245402015001038000007410f2090850000c0d5a80c01c01460060342c450395104c0e100c0c0003003001c4c02041c109030126000c035964001c580d441e01c1e07550070310080700c1e0407400d03100003040d0b844600d0309460354007a03503281030018140410142406030f4158030603001d003108404605038110700c070055a600c0d440c090007000800a07003007100b4000e400507100e10315224601103400001c42503a807000b202c2281c11004001001030069452601103241c204601c4a900000101003244c0d02d281c0703030005001814440c0b141c403800016500040910005005403403109402800e00c150041c2c0240c51004600b661030703001c50300381d240300c8022942ca040502c540320303800d11940c851109007803402500f0340c0e150704401480300c00f0448034030001c82e880d241c1c4030080d080040540c0c0c0105486403840 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 41566767 1250 41565517 41565529
    0x60f060512010e13120e03010204090207061a01050a230d06031110090504090804050a09050601020f010e06040609020d0c08030c0c0f0307140a0306050403050901080a150e07051b0a02 80
    0xc2d0001900166031003d00030301034445001010f01c1369000c01032901d40c550307403203042d9400c41c040d4840311751552001c980041c010616400800e41140f05503010460b0001c00740d0700c0314034490a4650140042c40034001c1941d81d43c050b50521000001d420407a03503900d003408848840c05d51000007251100c613240e820400401c45005481150203004075921000b4007103164000b01010b246126852180e6115072604080c00012000c0b240076150261000702000d0b00c4a007444080e00f02502c6d00340c01445842c8a40d10300020621448911200d42e0f8041e280a07115501d41d64041c0024080c02d80e40301c0c06101e4820009406440340c480200455030145840e49070307082c9003d0800385071240280c020801481062215a40420b024040c1c441c1d03484034824011200740410600322803600003c3c801803801052000340341d00320028001d407030002d0783d45c01640d03503540c45204160b807841029102417800418051101031070464016034010028600035061400b5488903070594440c0241003021342e0005940c410540c1090 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 41568017 1250 41566767 41566769
    0x30f0609030f0f0c081e0d020403030206010b07030507020d1e0501050108160b03220f051f0b06071205210103020909030c03030c0d06150807030f060f0e0a060f06051201 74
    0x381421801121103d0014006401680c4000e02d0042c002030150080f00940c000b03104039241d801c1e07100ea100c2003064807060095020f40810341c00b501ca6100009402c4465104880040c0d515070b03640c1b400c0040075400d025000740207181c111001c0e01011841c01e2364a14140109071038602074800070450b54541a0b40314201584d00e07080044c0425005400c0c001c941c2e1000840f030700514081000b1502101644401c0620b01c0482401025000901c5450741070100004007000e941039079102e0404450004140c0008403101a1030094010005011110100d450150348003061021402d00928012051880040c4202ca2203001800364108400500560410b8000180e00400b0040154603040f015134440b540e0b07000091101003a80000940380f40491031a0f040382c4001c3c40100c01c000081d0f507940c0c2c0d02401032901102c10400091411000b0b0359102c8290040380200d03541c1009001816041005800d01000010898204152030340c0c0c000802d000740708180801440307995105911240440c466101d00401 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 41569267 1250 41568017 41568047
    0x70f03180911090f030f030c060f070c03120207110619020f010506181504060902030f090c0112020a20010501031208370c110d050c030703030e0304030f060903 70
    0x9030982d41c00e038800d1000200c0711000011220640151301000c0001d00c0c100c9008442d02c9280000302e4452210310b0b000803164010002281c0321800c41e0365001048503540c4d42ca10000d4002081d11010b10b071482066030082140c680200d044892001d11030020442c60b82c8165540e0400000b1400e5070100180d051201c801070b5801c000090089003040700c001602440c09608940126000c50701141d10484c2130256660121400341060141079503c214140c002c0d0400c0f5420ba1450a40c940000c02c01c1601103000350f103d00301612a080b500845031281c100a400104c1d0710010b2102c1500e82d100001d03048ac120000580e0014004182b40d815450701500600e1a40701500c103100610f01485590481410085003008480f2261820204a000d1a80040c000c0c0b6031102d0b8035070304d01001071294030f0744159084004e000d91011504013159080301201c0c0e522403a00c2c14541d640040c801800040c0c13181d000241003566020440303040c641c03640c0301c1903d455130780d0600300c0300c07950303614500d000b0140c1002c12000309140b = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 41570517 1250 41569267 41569271
    0x110304050f040b030f0604050303070e03030913020306130e073002010305041104180b060307061b020d0b01090203040b102706121a09070501120b06070f031809 70
    0x12030040811000da60190605200303070303210a0b041d007481d00c3c01c00c01e03481d81c0c0d011034049a20741d06041c12305644a074029036080c03000400803207440c0c03114180001106c0e04800040c2c00d44005130101e0080000035003024045547c043d612000c6a81250418025518041c03030f2080540811403400030103010700070310500b03020104040c5000b803103070440d01ca1100603c0160203090100d26582c9a290000058803041e1203298094a80014800318904041000000500c201610140f58541e041015900c003428440d0301c0010b0005004070350764000108803116954800703403440d95205803941d035001c5544426007240e0065540030081106018020002d40c0d00049602c0c481078910b424803008003407a101500d01110b6120340c0c4012548440385030741c001d80007440100c1130040300c646185860362007815010005001c0c3c6641d8000f0078880d0780c0c0450110b045400c140c45500381285c16078403810103000c0e1242800da01c00c400340a0140851401d100c000c070600c1c800d542d580402c1083c01d507404401051600000303c024 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 41571767 1250 41570517 41570519
    0x50408160305101505060304050303040c0e091e0a0212030a0e01050901080406200307091d13150905101b08071b061509150e16030c180f06110304 64
    0x2500820381400b943d5454070045800080e500304900600c00740c3c0d1055810840020070002840808800303980280c0c03155090101580c3d4502c00c00d00f0540b8150303004482900246503205a480502c0410f903403411401c41604d851181540000f01510f84a440703060782c1e80c1000903540f003020350160040d40100001d0910a040c0024440004c041c0b08000f040242400d0f03442100343d04900803842100300b6001250000369076880c000c01c004140100300c0c402c0c2003003240381e04081002e0044240b16640300f07100901d03c0e9a0810400d4981a032400729480340240d0240d03440000c00007040040c491001741c0d888484001c1880344600191701040b602201c0f003001042101c005101100740d03c41c88003040e03034510100400030300300240cc141e8020000c3c22a518442141014000364100d6503030070440350000311045600d001562145c0040b43c0c0e29040b034060181104070501e10007014029402a0108074030b514000002444001c3c01d0180c3c6055904048841e525001040003820313071000d4401d0303100a044015506003 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 41573017 1250 41571767 41571773
    0x150a02072103050304031209050d03150504140c030613020c01050f0708040b0c0903011e060905100f0302010815091306050106030e0c040b0402070b0a0b0310020a0e01030e010b0a060504081603 84
    0x24000540006c0801c08624078001c80c1d201c4039009154031507084000d035004189003040180092038070711152400c42d04101e0000803907141911607003c3c00110350146851300d544000001059620040005a01c0359075600300351910403252002e0100c466020000090500300004010031200380181082c0c1003000036010000041e0b018100e02c0d030800c0caa080c8098445414000080c050400c421150608119070301713980200003a40e0304590200c4006000c100215141c2d909001840040390140b025110f101210400055110b140410b60141107070580359151083c100010f401003a05543c655a400302c1d0744070420601020340b040e1070040066003410020040068826a1107907111484103109507910701540d141500c9075012241c0e0b1980c8011000d845d880c1214084009200480c80640644501c01c040e0000343ca9034802c0760140b0fa010388075940001c0c80200110040d00a00c017442030155211448450280c950b00081c8000d0700b901e4a8140c1c840e0708018409245c10401c120a9020032840c82e420004 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 41574267 1250 41573017 41573027
    0x204050c0c03120606041503051605040b040608100504050a0902040b101b0204020d0e060a06050d02012708030d0e0c03120301030201050f040e0a1b090b041202150a02072103 76
    0x206480002c102c215070b507100c0c2c0028849001e60347c441000f80c480510b0200320558540e0003123100d0040024440301d03030001c00004480b54052401015101ca00c20030081c88158062881f1542c002c0035068000001070302c44010900361542904e00c10b0800713449000800031440d05018101c20960242c415072881c0c2d000e0100100040d81c0380714500311042071144a40c00b551291740449111011207802400b01005010040307070365010484200380418600705000c1014035000344d42c1d82440d40c050b585c04922140141c825a452002003240c174071040340c89180029011003d002511384000001000104903d8141c883c03410125080411803080d000329840604c5240c1e00c2040c1c0e41940d030203107001f60300c0c0c140c41e810000720fa00c150303040850a400008104020100d5940091051441d544000004041d50100070303154881c0900418182400900051000403801940144030030300090211010400c0c9181903c0c00382d102c07501110060f084810103100300000041e07480f05502c010710100c0c03900002a100182 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 41575517 1250 41574267 41574277
    0xc0910090903020c09070809060f010812030915040c090605090103020d060b0604030c0b0301090606030b031b030a0b0c090a050619050a0c050303070f08010902040501020a1119080a0204050c0c03 85
    0x6605a955080006040c400c102000c0c04d9600034042c00305030b0070078034030141590904940a40c034a22462000442c000700c80c0103c0340c12110b10a0041144148441e0041d040e900000c00c0300e000d43c440c05803d0002d011000115501503805a0090405c0c242814040410780d41c0d980c01c11401003965400420040c1c81c2c400c910210150030080006059036818006a9280b090f0303031024104100520012904038600d00045049a141001c01c020503640c0708070a5081e2a5a40c44140c1d040e0800ba40321200742e64150300540e000200102a100900480c1d5144c980855041e00e00001140c00451081c1d101d0a005160700003500d41220003d00b0103501010b20070007d542c0480c41c404101000c1100240b0500420080601031341c400c0541c0c1d101e10389400020824006c505c01200040c90400000611510b144203c40550720103902070b001084503512001291120b5180550300b00e2000c24507810340100c0390404001030240c1c0400b9001c0084180104005c0e500060f20540d41c5c41c208101064141c00000222a = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 41576767 1250 41575517 41575529
    0x6090312030a090c06030b0f0409020916090b0a0503061002010e1e03040306050414010b090c04060503100e0103140d0810120c17030a030e070501050403081803030403140c0910 77
    0x29a60399030b080d4650007601c1c00030001403881540d000c1c08078040b50560404050350006480c07902c1c040000c2c500f04400c0e16101702c4040c0d084581076021807401d5038000801c01c2c88030114102800201c0c3e50380350000183c2e1011a00000041c0e02000380090f17072501401100110f01d42388001c0c0640401550001c4e00e070001105008040510740e038264034184428420740d0011504001c080159141078100306400030320800106125518180b604102442c01c920558000c09440400030304160a014042d01e01e680060481d03609900394440004511002c2001540a07520600c0c00000381249034a40c2443d2140c039030860004d016006007003050200380b40c14540c0440b4280680000c50a04c1401c00800254054108501c2c0b183c90f260740c59440301d0000001d00c080600b0b550104004a51035031465200c611500030399002074010042000402d00301006081451116840300142022000c0000d02c0c552059000301d9000c10400c0c018400031a0612200514060a40e15007076540343c4481a9014040c00780202 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 41578017 1250 41576767 41576803
    0x1081504111c0212010e0c010c02040b0a03030e011806050703050706021606061505030103050606090402030f03072f0a050108070c0204020d060e0108030a051905070f150b060903 78
    0x142400304450800300c003250041c014a00c40c00e0a020084040703400c807007040e80030701d19122981d44c03020414828102242280340180220078800001140ca010350704a059a0082d2610f003520440d543d400d446400441c46500c6580144e50000009010f14162003104a02c06600103010800300da0000304880751940e240c070700250f0310041c0d80380c0340000340543c0b51300351420401c1d000b8040c1080400d074401029148600c0f5422140c6d4105401140c03144400d010051190304000081069401c2c04204290031910040c1990401c041050319286140c02124003900c48a400d0107681d001300812000102300407424625110544214502050302c01002e4071420381040100400151910b1262041c4001c542c0c2c010802e46d0b4590111112802424050294030f40b11070078000005001c1000108941801d0219191207082c20f00340c4402c1c1c0005001e82c21100c0501400700540f500044140720800d2a1600c03030504442c08001400041e021500140201070040c80d003040100019940000d031001c88080c02084 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 41579267 1250 41578017 41578021
    0x7030c0213021b0a0203010b06070302030d0504050703122601150f03150f0e0105090402090103061a10030203090c032a030c120601150507020a0501030f090b130b010806010815 77
    0x407920080c401d0102000640305080c012000e4210041040e0146034001c0f002405940c141004100a52140500060240c8c5c000c100035550181c850308890f600038007640a44110030782e80d45074007483d0024042c000c0c0000e041400c5010600c280301c40b44c1c1845404c0310a80c0201507041207411140844050b078203000f803015900529503211721a0300581c215400b903540900d04650707907580c0705107181d085010f400f460803802c0c000480c903806d0015805104580081200081d84d103540c40e1240100403030448460000048480344500c1e496000b94110801b0311350342c0041e62490080e0910b070070301000c542c4071072003070300aa0210342846000003a00406100cc0d281500b0100014400080c507107401004e482d90888441c100b095a010004078215040719258004140b1046140074102c03058841c5c52002540800b00440502042d440f9030301040d405100c4c0d4a0014144100341c840c94604041106d0101c207800009841c2da04002c103003602140140380d440e0003048194149030a00ea142c003100420000c0410751500 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 41580517 1250 41579267 41579299
    0xa0309091b0c060b04020a05040608242206080c03011d07031410090c030605070e03030912150103030906021923010207060603061506110d0c02030307080c06180c090402060901030609022d07030c02 86
    0x2c440340704420001c0cdc4c00c0051599800d9465115462088254440e520340511140203088070400c1c8240c185040c0083d00750356065503183c900706408944212002e204002c0d45414440301d40c420b072070801c2e00031031016603424550b00e440402d90340b008200c4000c000010084c512162000000e0350801d17001254340031150001000100d00d07100e00802d11580d011040300000003410341041c440000c0d554158207456901640e00b00300c291050458200030201d00048a00d8200141006180c80c1c1c5400c94000252600030303d0388448056034030075001918026070b00c4c59442c3d501c1c0d000c4a01c00e00201054100240c07000505109203807101d0cd4181c000e0300b0702041c0d00d00031007150713024000c035400141c0c000403490310380350031007070a03661040b04440c4040b8442400070809101e410010700c600b2940c000400158850303490b9402d00500d5040030020700e051640320800450145581c0c000f40c030422062030700e010380e4000206007000c0c40131811031010703000450421500c40444e40c092045c09440c2d0b015200c403106a41019 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 41581767 1250 41580517 41580559
    0x90c22090e210c030702150a0201150f0b07030e0d030f080108150406091412040609060503042301020c0106120b010605090307060305041110020a0309091b0c060b04020a0504060824 79
    0x480700130f5100c0d482c8108421405407d00250408500c9036000308150102000514401102c42c0500603288815080c1004119100001010714522a00e421110020540007003101c00c1c4030f17940101e01055010b1005040141c1c4142c0c03c9005000344002020107141080300068000d00c0030300045d0606440743d0440d414881092121112248640c080712001c051100380300f842600325014800010701d0140d0700144191140d8140c0340550f4200034081008001c5c009507036041401c0071820100c41d5003d00409120305400c1c0f040c1001414690020404080140b6161460b91416040341040c08000e004181c480d403130000e00310307042d600642000150f82c0c0352410400c04046456201c1980f010140d0100c051813540400c168803054407030340303680090b5070b01c4000361410340e405041c08059100190000344d200350320800c41302c000c02d40140e41c0024241d4174100824140d0340142411400314100081c20405a0380c0140c1c2e865200c00321040c00d0203038420300180741402e0460f80340c0032403040002c046107403c03068442e = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 41583017 1250 41581767 41581777
    0x3010b060a170702060114040c030605030304060c030306080102030115050a020a020a12050606030a0b130c050310020901090801020f0702040b0f0301140a0f0515090c22090e210c03 79
    0x800040d00d07032400c22801014a981c2e5502e41c0041540c0c8000318407042c0c000a00e003410b03a101c1480356084820031b0824000105804034002c401c05440714000901524280020400f0302125039803001c000e04141005000d0729500d6100768000c0c2c0c0304100401c6a441082d481140303c441c9403500c10366035450590228039004910402039400040030000041c0c05c160882c02182d420301c20b905948503640c55504043d1a0031030450081c02075034a0000041c2d51011048404a03010b101e00c410841c0251105e001c00d24000d188449162101ea0020703c41c21190381000c04c0754018404440254a0302084580071070f95400b80740c2c002402162560203480c070385d0782c50080345100c40c5406002002441e0481e00110381104c4d080e607403002c10a20303001e1000d0982c411801100e105026046070100c1e0700459038140610900d004003070b400c5902c418407004c12100c10403500f8440c80301200f96038690306030a020440b0201c03001c014802c03800382c4c425035060440030302950444280b0a0280807050b00c07400703604030913401c522035 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 41584267 1250 41583017 41583019
    0x101203050f0c0c0907030207030e0603070c050a050a0201020118080f0f040506120106080105120a080a0c050601090501050a0603060620190501090c090b010c0b0901090b070806030d0201020f1803010b 87
    0x40860b09074241c0d440000d036802d92060072165540b440c0c68041c0300340c1c07c900c11041d01400148005281c2240b07420300d03600542e00103030540340003a400b0040e0344400303003062100601150250050300e00c1006540c0d0900908400c022864000c01540c0d0752035032010310314803658007544d100c000003081c21098160618103807001400c016050903592102c0085048089900340502ca0106898100220302410034040c00000c0e41410310042c0405426a00c500303040d0b0f0081c442038010001014110400203030140049402000f1604001c5002d504010803c440040c298000000701450050704008050303200d0201e21452541c524036054190050490030306000440c6040e44c0c0e12151b0440000801005512103005280542c0444100c0b9442d5052007041d102c0080700c09001038138804220002ca400c80c0d00481d00003091030000100d0f445140e45101c00b000302101c0c5000450960310400c040c0c0d04003031000403d042180c2c40210300d171000400e103581e0b40b80258a040104241e0074104030358261803d44c090303965200 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 41585517 1250 41584267 41584297
    0x60d080f0309060a0b030c0112110403081803030901080114030c030714010305090111070b1e0a050601111c0e04020c01020d0b1c0f06050a0213090213080610120305 72
    0xc0340188544641c41941c44450511441c400103440032154800d04d00c503c2401805028141d01304c200449882c07030011007004106036100004026140c01200410043d40b18800058641441d080b1707115114800c5007609000e0381080000d0706a40c1ea00590300c42c1901d0725030200000038030801c400f0a242000a82d58070350503206030303c00810100e040d9000d850003840266400e00590f5100c01413182600e81c49a04814001010302030040041c4101003165800512a418001c1540d420146503192a20550f1489041603a890502c107040d41d020001c82d00f409400da004200000062801c5500c60303c0d00c0f06c4900c100051003000c2d02c155a12601120600c1c0c1303001009644415040040c1030082c40e08000ca28401c050b00e00244c40400c800b030707124000700e0f07400c4624004c4988142d10780102030308004200c02c101c0d9508004003e880d1140c541b20360007809004000503166044c12814002c000c1c4135410280c4240d00503010014409810600007003174840d41d5580007210000c516042d01d4501030a041002140 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 41586767 1250 41585517 41585527
    0xa081513030c1e05011508011d070303051b150604050f0f010b21010f1d040302030f21091011040b09040b040204030f0809130e030a030c090521060604110a08060d08 72
    0x80194a51b21058618240c020001d003002d0b29041003110344090a4124160003d4004002082c0500c0c00b9050340340c0c0800604c0311007101c00303c1d041d0070000010f1103690710060b940f09100441c01d003803145503400204469502014180110f07002c0754800c051158080c1c0303900015a141010f070303000701c4541d816070301c000c69200742e96101c0c450300c031645900d0b004541405044845c414640007a000c22940110303016009149400b8071101030596503440030101c8500030748080303a1900708250081e070031303445921400083d200c02e41040c11840151109031303d048012460901080c4030047d80e0720200c80704502d0480d80000c10032480c0d0041030290040c0ea20160140740c0c0d0302014028052104001d061110003200d48407200b0a801401900715062411904071560083c42407686190003644549150350361404e003003590350356820010301040c1701500d00740030000c0b0000c50301401c3c0340100440c0b6001030048406104071007030f02c0454403080c0501c14a00d010000458045107068844060301401c19412441d010359038 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 41588017 1250 41586767 41586791
    0x90702120705010e150f0103060902060913021909150302031801060b031e07091403011d0304030303150305150c040f0321091410030b0a081513030c1e0501 68
    0x819243d407015000d4041c210f800d48200792005900c46c460740843c09007204036421612403000501e00e00d1003c0346c000e801000345182660b14002d26000d21540007201681e43d00b1009001a0405400d80950f41400003190040c0640300221061080c082050301d00141c0760399a491040d108034916200303240e019444d0480100d40c90030548011481480403504044103a61410941d8203400400c9030040d001030b400c03031402d201c070200d03801220415580080001c218019455100c041c11101400800006c0e4000039042007015014041c9000f648541c0211b80e6150346961a07003030701c0d1142c1d03680b08000c100b01c8800094640400c0026100a000704e185803d000e2500e902c1d0650348a400b1141c81031140310510048860544520141c2041d5009420000d624490103800c1c060030200c010324140a142d192900798000c0d80307072130149800500c00d0000820890024000954811030007910801c1003501500c940d40c0401e400c10b03000043e060313210300d150440e13111240a1092a00c910f6400030300c15400d0920540030 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 41589267 1250 41588017 41588021
    0x3040b13030308011a030708060103091a150306040b060402071a010b0406090503030c10020a03060321031b050a050901090914040209010501051e0918010303030905120a0c0209070212070501 83
    0x90324400d0300c80303004590300c50094007140540d1070385019240301c5c2080059082445003550a400c0714040c1000701b1501e04a40d5079440840d02e083c0c0900c0c050740810100484d0410503108030000c1c5030154007030308190405071030700004000010000c9000b550005210800c0218007034001e5030540e4201d50f08640c2d035840ba00740104547c40f41c45490300142d691100460340340b50102c00c03500a101c1c403a00400c078802c030300c108950117034010104980070315076a0380c400404140c1d03094000240111445c218a0955a1004050201c40051041210a182c4046103445490300b1900321740902c0124244951100c1c0340800484913852550801c15205051102c08101c6152103406580640c0c402c48910040c1c0c3e803144011512409a04c1c5031402c404c8415029485410200c0d0003801000009011052100e1666004c1c60501d6070a0313004400082da500040b03014444180001800c00350781002d40c40c075001c1700e041c00600d00c3c51003030f50180c480c03070040700450311480c000c01071403450400101d84e141c0c44124904200d80 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 41590517 1250 41589267 41589269
    0x30a170d0b0604080309010f1b05030c01050a0b0306010e0424050a0c050c0304050f0d05070b07110307050a060f030e120c0105010927050102070209040b011401080402130e03040b13 79
    0x200e00e03070401441041a1500000381c0e001d41d1101001182001072070001114110841d19505003400400c0f040c009110390800c400003407203400f8400540d80c3d85001008a800c581e03000300003144803442c085004500307590200b0007a04440d06102c25400c0740d12035051064254018034030b1070703100100081421480b0310241d000584990070740348041113180310091094580e4454111081120342081000340201c1c07400d5a141450765801030300c4580c0c02da40c039a4660f468900700f604285800c280c04101c1030100300300c0c1c8200400d40301003a805404040e142401003860390006d03000760b0042c40340e17485104001601c0b036808400520326400031600308081c0e21800604550001c0741ca009a5420000046044075141c0249002d00c0016400c0550100307021442c501104010042101d07035540030046a40965990700c80180510f000704081c100742d502d0810240c104180c1c030204141800b40220400000d41d84041030003211103400b00d408641203003281c0c00a4250f202c1c0d42c001224410003c03c070140c000c43c40c40c0782c0308 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 41591767 1250 41590517 41590537
    0x60903030806090403230702030f06010317090d02010305091009030810060503011401050a021006060e040c030c200c0a0306020a03060602070305100b0612150a0504090b04060506030a17 81
    0x7803600c8410900245900c03c0f240a00410310780c000c07201000b400c604044031515940e242807424441d0940c002400c1500f05518208241d01c54401401444405444510300c0d100346500a4a4008a45c01080c04c964602e9030280c10b050340e403030014901400620465069046c101c02c04c0002c4d50700c9140c050320341c1105030f03402c408100c8000320200f001c3e402407007240d059400d4200d510241c12004801110142d02106c4584e0460049071203120f40b00c00760740a44130150546403100c807405503885082c001168403420480080500b420a0446074a800400c000040d4030072100c90441c070008403540c0c0f898030441007082a00140003640c0003041c00855400b514203201c92b0f0380c0900c11070f9510501240d5a00160202070030b10381040890b801040e1a80d030002e00400800351205080c207110513070310341198100711034422040001d000c0d400140c2c60318208100c080c00c0100c03003c10507496a074031809512040200000c1141e60b580000c10b1940e0b0307082114403c0c0301d611a0300e15034025a0342c0089082604407400300 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 41593017 1250 41591767 41591777
    0x30f07030f0e060c1b06010e0108010c0504120f050f0d12050105090103021003021809011805010603020f071707050a150c080c070602030a0e0304090e060c04140112020c060106090303 80
    0x3101c0005016550000c0001d1008000c1610f6002d00e600f9640d0110510b0140c0c0c0441030080128490240440c034020070f00003100210545c548800e850a40740480c0b034100400c0000c200511444607d041c0d5071a440e038104030640c41c801d00d80e2800c00c2c40c20300000d1540489201d00d1803091049503000000c007581902000e4140072599a45040c403006000a01000358080c4008442c02450303031007580580948080712500078140101140800e0b00e0607021b13000004100012001050500f400d4002c0a00400c000c3c82c085180c00b50700035841059000c1d04c540100f6410b091100d859040074400260382c0b682e40c00c40207440341c0c0c214520300f9451103003041031070082280c03c1c40c207a2204507020780c00c1c0300d2260303403a402d19920300003083c1e80f810000c1d4001000c0d901c026540b00106100d81d68104080d00150000e03000c0006d80c4050b51b000c192405200800e05010359000308410300c244014801883c4a1850a003030010445c03100ca09074501171300442c481d14009200d81c50001458660240041049034026155 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 41594267 1250 41593017 41593031
    0x2010e0306070509090a290414070219110402210a02040302030d05070203011e0509071e12020d080d020702121c140403060e030405010206180c010f030b0303030f0703 73
    0x5040d181c003011a104404100207025030350703441c00d04880817540304001a000040800102e120780110750303412014002e440c000303c41460410f080a101e03009a0340c4d010350f0110f0451a121000a40e40d00d039198040c07a070211170009000030454180002e0301000c2d370051055468880fa2100c0300c2101c0e81c0d10b88031030048000c280c041801d5118510840742504d4025024040d8580203900903200c6034410f0400301e800d50340c2c0302c00041100164038054001456801000700382800d00f00822444e14541f5002501c0b402101005c0c6451680a45c60000484040c9440c0c08440500c60001030741d2014070b00c3c006080b1800000754003848040d654002d0415a108031180c01001d00c05496155849250400c4840050101c421480315280115150790705200180000c42c60141c503035a035130090310040c000c07070311142c0c1c00890140601d60b014803605900c481c4c00308005444c4101040400c1c0d0b1920b010380707100d0521a01003ea4000c081c0f10b07400103803000301d020342140d980c3c0c02c001c28007070b164000444401000910f8102 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 41595517 1250 41594267 41594269
    0x110c1c020f15160f0203041e08010e010c020115080606090705271309020d060e0106150905040c051207030506010903020d0b040b06010302040f060336030905100909021b060a020702010e 81
    0x80002d031343e0100713500860900f401c14a6a004c0f40070b600424a03c0301c01c1745076002958020034000d113503040d03c25000100e500b04008a01134250340c0302050030800c1c81c400a0092000347c0000501703580c40700044070702c0b82250b25141d005484030310501c41030312440c040300b40808000001c00080a18242d2082c1c0b031000e0709200851042c000c60340c00b248001e60150502100c8004980300390040d00844204000006d18640c3d10340e02403040540c0300d61000080303a122001000185403501c5403883c0382c03915081480c6890400c1c41702c1000281c0061900040c556100e002c10359a91040b843c17000610f034043c0c1507507029141400c1c00c11640908480840d0005000b00c0010071030351090081d9421100c400d046102c0c2941000300980103040c0c0f10101c8807850300c682e007204420395aa8840d06400b0450403000e00301ea0102420001c01018041d0030840c050415046a02a89540940c6c550100d03038160000580758070301070501552182030302c1000800c52044c202407100c2820264001c100d014400d880304440004840 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 41596767 1250 41595517 41595527
    0xb1008150601051b0102040915050a0b0306010c050a0b0c04030605070f0e0d060209090406020310170304062616021b030706080403110d020709110c1c020f1516 70
    0x264002200001880031550a50140000e407008031341c0300e07080c1c104802d1083c0c8542d00320313005640503030301aa84403c001e01800d911f404400c00074102c10303502c1e41c00550401101208600c130280940d4100110030b01c200382401003e0041001e4141e00c804040f00d80c0c1014108025690450700042d42c4480ca02008038070003e02907038034590004020b84901c503d1000200030800c00d03010182c0140c514a03020000c082c441e0341c841c070050b031003948108001a12410300720103201d101a076a42041d400c890018840b0751309280008107407000c035186443c4c40181200803030303034038040410004031155014030801e052280181d8007111007000030003554215a1000601c0901e40450304911103e42c0d019004400306008651003180b81d1a4024002d083c0380c509100030216152818120400440058105440c00d00546003280280c0070100e81c10b030b0000b8105500324250584680e130200300c240c415040700c4004080306000340580c01c00070058800b81c0710b4804c07a9030701d541c0c488102111132002e03001e110f50307400020324018 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 41598017 1250 41596767 41596783
    0x308070e0a060f140301081606091a090f090a1b05070803041103011d0102030f01060503010302062703010f090c0602010234080d091a0108030d09060b0d0b1008 70
    0x2004100e40c07a1600c1401c0d91000000940101046107140407400ca00720b5600040d40202508001081c40c10304100c0c07026030403200c40d0805810401c01800030045d106e0742e07c0c1a051568507456030b8647d181c1c0030a001541c11049010299044442442088101c4031694010000c03070008800714169a035511100311214440c02c000107003c80000c0c03000c9404205020390315040b5030000350001880e150b0262201071140007808a01d8120b0b9000030030820504030300704485006000c5070810b0f60443d41145c3c00598240160f002d24070f0007207090704540c1e0007200134188040c04410090001c102210900c4848005007541c0c01040c0c0d4442054000003400310f10520032504506031500102801b250400b01211004014800d00c58408202c0c800304000719082d040245400c191450700000c000b010b510f040d00c081003c020020032070700d01e400010010321401000b00c40d1101f814110004001002e03140c82d9008000840f01190401c1a429401040144c1b907801c60340a0701e40b41d06003039401035940300040e0b40c40e952 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 41599267 1250 41598017 41598019
    0x1090506030d05090d0c03080a1106060609040b0102010b150a0207080606010c0b180d080a05060d020109060513080109081c02041212050c060c0405040b090408030609061305070503040308070e 84
    0x102d0700d110145101d4405040c0d040c10003010740341c0703050940e226048002641e800607222030760f00044c403001c8141c000308402158075000f0b019003403a141c44400680f60f40541800b1174051a228a40141107038401c0d40107518016004080b40c9035440c1c0c401d203460b241d4000b51882344c0540714015000c15400e1000900c20711a110582d40d20003100c2280d580c1c80e000c14070241c4840d10420380a40007125044060140b0000000141d44050041c03903d00d030400292040500743c5806410102e0000000d40d0713118090350261205da05006a885880d0501050181860792185c44154a0071507440204501c00006140d6084c5104284200403a0603000e06c0407445144107001a50310488401b0b40015103814400004401506106d8140402040780a081101c112400c5012000000d02805180340a2081d407400c0b14060722002c50b130b0704d89907403056440c1c80007a0406104046410005090759201c0d429a02d942ca29040103100508000401600070781040e41c0450109881030001440d2500c5609038460342e000c = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 41600517 1250 41599267 41599273
    0x6020c040b030c0f0d050703060c050307030b0907020a110105070c0806010e0708011421010507090315020406020c150408030a02030301030618050a020904080c190c080105070203030106030e070509070c05060109050603 95
    0xc044e104014181d444280c0407661409610b1001022940c14410a1011920751300c4850346c910b403591000702102c801e40641403041c8603031824000240d40c00124201c2031548101d508412443c3c070001a1a280075030b1400401e0326610540108801c030010580d40d040f210031781c42c07420007030325058000c0c1c4d00380c0024040c980d542180780c050442c0764944406d8901c04429241ca0715112481300801d081d084d102d04075401d40c0880c0c03d440e402c10404c0707012600708420541c09801141450305010000b9250084003807030074402c02103107031950564180841150014812170341225070f43c04101a010303459420911081c1d4805140c01d42041c100342918040110540d0b00c00003038428004250308202003000003800c1503d40240502c0f0740c0845550400c00c0c41141c20308e440702c8512440d014a06100382c0b100b10340060b852a4107050901039255000400d4a054440c1410086210000a4035092074050745500c8594003403003a006000c01990010072005a0074050003d46803140e880d03155180580ea025100160107034 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 41601767 1250 41600517 41600539
    0xf0f0d02031804060302090a0b01020d030b0607021210020a020d02060601030c050708160c06090503100b0f0d030507060c0305011712030601051308030c060601120608210c060106020c040b030c 84
    0x58424010400082c1c401400021900e0b01c94020a86102e8121080c00c0c04594403c809105517170100003162000d4541d24043c0700725522100031601b603000d8030324024086c8901c401c8001c49810244100801103070b844200315295030003410025034610400302000098014140403440070f51090141084244003611030b10700c3c0c00241d40d29613803151b200300b41d08050b00c42c10011090005060340301c0e0364001d00440c3c4d6803c40490400d4101410080c850ba5440c0c9a28a415420b907059240c8094206a001c0e04442d000e00380e0f0518281940c2c00d115120004003514600b22040c0c40d4990140c0c4521306891040107510000401d039001281d540c140c05040303d901e0401880050900d41c400c2d0000c000c00007966200c80384080c0e6030701c402032a43d000444000d0341500b20404100003543d20240340812010580302c20700441e40761903030084d154100f017221030249400c40c034181c2d00c03640c004c9421144407011a1084403203e40c2c2d1400020f4540040b1080c1d039205070305002036283c00c0e180004407001c0400b40200091804 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 41603017 1250 41601767 41601787
    0x20a080a1110150e04050601050402280801030b0711070902031b0403080a110303040b01050402070201110609070f090b1309030c050a0f020a1d040b07020c120f0f0d0203 74
    0x15040104400c041109403801c1c400d1680062180100410080d0808a10100c50b24400d039081012a046800c8600d08902084041000080d50302c0c112402560010ba940e14072841082c0300b84d2203d464040b103040001224904070b5840f10100d0304030781c0100f00709207060715080d8044601e01140343c151030450b40300c0c2d0001d005811030740d0300a60704204c0da51159150510444007a001070b0704154001d0f03540304000325644c0700d156080814821909185400b035480c500d031503502c0c0e00c0c1016040c0a070307034091a4081106021a4006c02103070400d0344268007210a0f80c40c103400d006594031424000c100b2000501c020000b5034101a0148032400100208014800c3c400304100c00002e1801c0750055080106001140000c20303011322003030000d10300580c00b0811141f070034014031501004903804101c066001d00c13000f82c032a0400320310305500035502c0001d407407907038403428401c9140803c041c001c9a41303c0032284030041214400901c40380d01021032410754800f0300c0040755007522410042c10f05c1c00035800800c401a10 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 41604267 1250 41603017 41603033
    0x5010b0f030f101214010c181a09121c050306150706020f0c0604060e060c1c0b030d02030d1b05071b0b0d0606030506040b0a0506130b07050703020a0b0a020a 69
    0x803200d40002d80d5000030755601076058841e10130683c01c0d00c101c3c0001c00039414418081c081d0015582030b504000c840b0401101c20004c5204181c49228441403000d003643d000d0350040401c03110850310080480d01c40105c1903002e0342e01e42d4580c034240025405080030404d80d0a0044064a2107010003e001100142e41d2940364050303603010500807200300340e08001411240c1302c0003020700203040b604001480c903840c003031410800316003d0b194205501c0d40401c04004880002d28201c44102d04240f0100c202c0500c80c0e0002c40252180d40e10300e646c03500036949800c003c0ca80c0000501030038450b1900c01d10000000d0040040f0b081c4072515403200240b000c014400100303a00f07441402c800c081000000702c0031707a580c0e0b100d10407941001780c40c0c250581d1201c00c01c00986902d800341581004048408104094943c030010748508120720503540220400704006031003188500b801d0000b407500200d880d951b40d07650718141d5203d0314107002c05c911661b00070b40f000c20f40e0145003060740d822541c19001808401501e458041d1 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 41605517 1250 41604267 41604271
    0x51501140d09020f0d03031407030e060a09020402191d0607080403141006030f0b07170a18020d0b01030b07090b030a0513080d050106020118170a030b0607080a020105010b0f030f 78
    0x7070400d00c0c1080c00020303170325240648410203000740c1c0c0001da905004100130240100c0a404802090b043c06525001c030307040890b1081d00460303100b200103a0031003d8804a0060f00902d42581c80380308038441503518032508103071603020600300800b070501078802d04402c010440c014404c01801004080c042480040c4070b280d600081404840110b60300c0c280072900410982d94207400841d0300d815109207590801012012071500070140d803c010310b50140c00d078605c10040200600b44804075490b003204402c00e100c42c030220400c1c50340280041071282e06900f04207011003400c0c8001c0750398580302ca001500c640c2c4120407490680300d00600709031850711100391710001303044c002c0d004400107600c0b0107409000500040040c0054078080345d0201e10f035850300c007029084820310310881140c09aa03500f0b81e00000c1d45034259500f041c0c0c01000f00c80d21041d400500700c005003640c0c0b0f800c541100d0009503410901c50304002400e19884160300031300140c2e880d4284000c0c58001e201140c0c0c14500b0074400706030f00c4581c00c4001a = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 41606767 1250 41605517 41605519
    0x1516020d080f0d0209030d3e07060c020307050301020a08040609080409020a031506080c040302011d0603092104030c050607060b1903030305010f0506040b2b051501140d0902 76
    0x40c2040103903003034401c890340102540c0f4a50783d40098940f00d2801c0030700c070a90320036255003451610040d07040b10810070924000000c0c0720120b000440d8883d500042c0c54805d11003012903080322441620f40d0302c013806d440d220b40010b034841d1059410001d12841c05008403582d144c0345a680031000d8940e6074640c0050700d90514122000313102400b0100700f904151003d4522400680d4003c2040b100c24203280300d01c19010703000780c000c01412604111002e10f162040301e0840e1740c2841d11000c01d40005000791102ca80810303c2650015001040c850500c600081f44130000e01d82d04101e03030000064828132085842540f000814407140f80d00100880c2c64640080e10500d40507a0f40410035543c81d40000b49120503d000c0064130764036048052061550600c40c0c640541002c1008005507070800f130002d062805140b0603100c1e410000504000015148a0036040e4201c02030034031911400e80352401405407034115030340348054a09036000425503124004c481d100c0b0380b1a004243c42c00340c8008a0f08007816121303c0a03 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 41608017 1250 41606767 41606783
    0x30415030f0203190506090c0f07140604050610060815060708070c06080117060108030306090601140d06140d020f01030e070e0f07090806100905060a0504020a030b1516020d 76
    0x184078803941070004503c24014150310030f0300180b0036004d0b6000c1396405000d050040c0394140420600e40440000c03a042d066901c1c809070340341c0d255894142d062441130301c03041314640500d205020400100045035405221409407294400340c4800c4104c81d290340c2143c0706900000c113032034009102d0406100922031280a91a05807901e242ca0b222010f40c10380507805400000c0e1410010001c4081603107944502d100000050009549402c40541c0c1d2404090300ea2807140740d1100105140380c0c05107100c081e802110420031600c51520320a500700034121441502d20b45580c8142c4900f00c1e01d00080c80c0c102183d401000d01c0100c00700300d0700441c000c1004002c440c03001c3c480c001010450151400000d80704200c250075420301480c4c0f6071801403404011340e000d8503d5900a505020406c907031a0070301015100c203900000b5442d501c4a000030307202c0c2c1440c1d02c0b10741c01038400125070600300d07456003150700c480e03d0a0b01e200c807200091103804a0548140d110550503502d641901c0b40041c90110f10f54540d072401541c0d6 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 41609267 1250 41608017 41608031
    0x60603040c050d060f1a03120711040b0f090109050a140708190209061308010e010908041404141501020f07060c140703021011010609021305010509040905010c032301060203041503 79
    0x48001284d8210706d90100d0501b00e070000850500d02086040140c4210084643c240903055903461040c0e42130840e1030303219944507107100c0c0d11900c40c0e500c10b07200c0f220700800400132541d542c040341c80142000d0318500c0c0c082d03041900a00280c60f44079061070242d00700740e0380c1c2e603607540d40c452510041c9168246001482502000340141e1540c580000d07118540c00a0030f016522440d00e01c540b42100c450a0a60340180d05240424002c100f050b400d0b1130480341d055042000c5000c040000800411109803d03003164440e080a10a00d4031242100d05140c90080e02140c800114840c42103503600814411440050085141c0704005410b4029410f80a00450304031040f040d180d80c0043c043c82030900d001c000040500e000c0880d0014240108001020900c104500e04a040d00b2072800c9071807503008550522030001061100ca0311030b907000403040398210000700010056000010080c3c41d10120540f00b8025080c00089420341c560f811504a1b4107507002503140500e8032030307000c01c1d450301e0f0741048040c142d079416 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 41610517 1250 41609267 41609291
    0x30708010c0e011205010b07021e030601032130060b0703031b051305151c0609060605090a09090c080609031b03090112050a09050304080303060306060603040c050d06 73
    0x10a074a4074560384070b20804540150005000c2ca44800420f15101e090a0040004c4e1041380c040790102a010345059902c10300d04d44602101d81d503203001494051141e14000010f00144d450140c041042e44080c101070400c4001c0708954449010f40060340c0e00344191010b00c1c1080480020040c2a1881400401c00981e104000d170ba03d604422001e40110703444849000c407489503152150f0780e00ca040d041650906070304c404010b1a0b2180c4e809098040c403501c4090b2541e40c1c03010401d85610101882e512030a511600032214007810300d62103403050082c02d203100031851501410680704c041c60042d040742403141c517008001014041050702602c00d02800040400d03612300c18440188100301000007503a40300d1242402000000302215264840e800c20310000c44280ea0000c203d11007690154000310303507501c50803031030002840d030700381d00902c83c2c400002d000608450100156205a10450a54800340d0700c0c0d40c10322810380300884000300394603a000000d0107a4a410070340050224040e100008010080703413 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 41611767 1250 41610517 41610521
    0x150512160305060a0501080a0309060513090e0115080102120f0601032301030c1202010819020c01091407060309050a08070512040305160603020c1e10020f1e04050d0b0603070801 78
    0xc0c01c1a141508030508001d031030403c2d8051a401002145c00500c2800b095450083c094001409181d0400c0400100a025032a80028130400303070074008010401007940c61542c600a2403c01c0400c0c40450b290791000a581c1030610940d140702c5c030b00141100c2550f64800c00307a24009401000c40741172643c1d5a6040001549414814060001100031210107505600381002000901d9020307a0220071103404200050340e111500681110303014002d9080181100d146102074001c59400c0d9807071350720705001c180038411400d10f210034100003c8280c40c1880d42b280d8003201035800600002d001988000e80040008410000410101e4084c40540e4030a14901c28050a41d40c020761040c1e03401d030b0000a507419104100c048610046c600d40c2800c6141c4001841401e07120411301e02d1090344000903e1482030710000038003586071301c00c0c800e880866507a18941100e6003542c001d90920700c084d42407400b043d00030303404082c02c540988030000c00080d19200240c0d142580c0c0ea100500342c9826004940001440308424 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 41613017 1250 41611767 41611769
    0xf2809050a15050a1a04090303060302030d030f0b0a03051507020c090a0e060f0405060604090218040305040608161706010302070501060311030c0d0f0305030601050f0c1f15051216 79
    0x14a80d03042d072110010446416548040c2c4100c80131403411070560b51101e050b50401d070709034005940201e2196042d040a400800259201035058018004036000d00d65040d031110f40a420307101402c002ea86060004e00c10308440340c0c08020a15402041154030095800c1006580004035104942141c401c2c000883c81040068415486464170388a400070301000074003c2c907504c1050302c0e1094844d031405854050741d800014041c940102d40e03a560403003d40d00c2d60441025181541d12100c41c240c202460700420756409885190002264003012625010074281102c04c0107566566074200d1140030b21304e8250b40680034142e941810b6080040c403001400a000b603000640c05808001803046c0220145414a462240d005101e04408078042001466410020b11140e8041c904203440345d4407100161010700ca511514000400080307040e155141c0d000032176014a51f220600e10a0601c0c2c00d103c100152030b514200241c6900d1243c01c00d0146003806140c0030030075030402c4100d401d4101c074810020102021 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 41614267 1250 41613017 41613023
    0x180b0d020406080f06180c07080711010906020a08070b0c04050316140436140c0f01030c050a0804030306050d110a080304030f0303020f0405090903070b0f2809050a 72
    0x401c0400403507800250940e070041042280c400e81c0d141075000143c03500c92088003405280b5484000c0f0310a02e0315242074480c1150302c000e04070350f1400d150525944449442c4501030015078101070118402d440030803010b14260380b08058500f054410b64031013280c0400140750f810350f50f80501000881b83d43c10400d2210701c10455902d40101c90074101e1224006c52103418580c011400d2850100c43e00c288055a81d00040c1e40f07007140000f4490091011a21610541c400b80c00c40643e40c415421103070b4080f4044440340e404403507104200400d0307030065080d605032803001404079406014802042e4028211603521920921300003412513103910024500f4109100c003901c0c0b000f0b110400043d6801d103101e920002d04141d000450070140f45a40c0c1412240340300038001c007010f030041850444080309400b510f0203084c000308081c2d12032510002d800c0e960380104400341c4202c001200070030740c1d103c410f40b00e0038050141440b01c04800d00c116180c001919904102d05400581e840200074003040c4180005010544 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 41615517 1250 41614267 41614271
    0xd0308040507050901061202070204110f040801050f0c180d0503180f0a080a02150403052b0908120715020a0c050f0607051e0912010b0a080106030210180b0d 69
    0x6041c105586081d00300e42205002e10070302401484240d40000d2208000c030fa071260090399580051020501801d50581d117600d8a000105440002c0300b512800390094982d040003c014175542c2a82c01c428140058031204d001c00d004220765000a0010107440913880c802130b00040c1d0006032507540e00d00d103500c05010b0581c40221001035000310300d0643d01e007200c240811108162554140000c01da211515850000e1150100d40030843e9401120001c0d10001c40d00042510101390405070300107201c4081003486000300f601c40d002d160045026003080b2003681d0710703003000301b030058002d000e81c800300c0d480580188c2c1c0030007400b01c0d0348015490900040140d5130403a600c82e0484c04103890503524100c00c0d2074400155401500410402c50f500c0401e4605601c43c101c0e1102c0034503405112141a440351a915542100c000c0c0f054000442c0150007495001006481600206950f0034400d4202c03185400005c0d0f01004181600e4071092055080401c0d00c68111040e02000740c4c2c42070ba000300d0f9809480000907444d = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 41616767 1250 41615517 41615521
    0x2031e0703200405030601061b12020303010e0604050f0f090309040906060609060f051207090513050103020f0618040533040f020414011107150822080316020c0d0308 73
    0x300030300c071201807001125502e82c241070403e0006a00c5003414081d5200304080001c0103002845140c005410150b0007240034200380c0403038140207407680d109010303c3c0940c20103907010a40782d0602c1c0c4111881035510380201c001300d0b103404031947e1050300c0140034005e00e444213001003041c581d1240315144080e03200b084002440c92501c1c0d0054421680e0760b11503010710401b00e14800006420008a40500c6182140c070182544c2c0c003241981c422600c4d070800c1b90840c610002c841d00b1100d103a4401c6060b240201c4e0351030000c2144508101320b81c400e00d03c400c00c00c4140764031140e1960401e81c10030354002c0d10900000c01c01c9400c43e804030826a00324140031420303803422548010541424410020070004011080d0703d03003801d0040102060400400c15810090800b0803254030b081c040c4141c10103042e81c203040e1041e001c00c1c030100a0081c0400d40d030003134140080c05050510707090709800c0440032580c800a5a0300355590301c0002a0050088031407001540121100030000c1d83d01d00307001d400154400d86070450f242c = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 41618017 1250 41616767 41616791
    0x103060609050907091808030903030708060a050a0501030b06070501090b04060b0103090c1502010905070f06020f030316111903031b0c031b050102090603010f1a03040206070602031e0703 82
    0x20380c00d039501031000e0354607000c140305440314003042c444256180381c00041040780c921040c0051148034241d0213442c204010050101e001800301c01580184102d07030f59001d1030b460303030703010411552001e104003944506200010000c95000750042c3e2445500202000d00380351098403400d00b5250103840486031500c1c100d0401040107005e12600b540401c1c20301c0e080001007450f80e602c00300036185008411620f960b90454800ca10300c01d400c01d04055a01c50192854035a03200081580035441d03006000241c041c0c02d0001c10349c0d690000503a44603107107102486401189199007a83c82d07075111000c130038960180c1c11140100210410351484030922035a000644403041041d25050311100d51001000c02c180e07050b40c1d9001c40d034010100c038070500351900c40f0001c02c44c031482c10500a10460001c030350001c40110000032541cae101c8080c0b400700c640104106964a220100c110014801250000e50061052014030301065103a40035540c09a04845c6ea04200302c0e8290901c4d06080f011128080082c0d00e41d400c0d6510 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 41619267 1250 41618017 41618021
    0x40203070914010506030402040e1b1017010509130c030b1015080f060f1c0606080303011a0f07081305030708010b03060a090c051503041e0201020a02090402040204180203010306 78
    0x3400007480802c80044401050226000103210f0188544404008138055603a03035440f4014008144040394162100c0d42d6002c86c04041c10044280b10301207002c0d0301445a4062405901c500e04d680c004404942c2c00c2808001176010090522000c100ea08030b06c0c1c500285469943e40061401007011003210b01d041145503010482503040101c0d142d101d1010724800c55081422150041c00031b00311000140e441202040781c00112001550b072112046001c5950070380d55001507803255004034406d210543d20392b41c01c2541ea01c0284522202c025801e14420b00b1801c00c00058000101d0000e00285480d00ca522384290725001412070840d4211004002c11803071804100c820b0040514500078801c03080303080300186d10f03000700601400d86a91a9100b0a08110008400703a001e4180100302c080345080484803800541c1040710115500807031440c0820140c482440b20a5145d41d0590042400080541c02e0003c40d030760103801260010b800f0300000c1210080da05103902c0a074100c7d100140c80f5071450410303000b = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 41620517 1250 41619267 41619269
    0x210030f05060d0206270d03080a0e0a1a06011707030f06050f0f01030b06070807051b0319140715030c08060607030503040807050c060f0307020d02070506030a0f0603060903030504020307 82
    0x1100d4440c1c40307000780044c1c640c9419108030000890303100181042d044103417500c240d0b03031011080e1f03c184058498010150402c452038004d01008030208148411a01f10558030404440083c1c1010342c102d042c2d8080036a0100011fa1051040c5040110742d9004400d03070001c0103050701c032080403903201c01c40b0440b6104c03a071144800510301121300741d001483c4900850007502c0815803c0b41010340340c2c80f0070b210944911040740d00681e40301018956a5800341841a03c03688002c460b500c2e90600501800145c0ca00021003a911500b003031143c11504c4030310f5132001180817041e00003090781e01a540c00012180e41d0300400c1e40340c1030721030b0320041040410034078020f21280e00180a05d03c00c960600807440825031100a50754420f900a04059480d00c1c0e17410320034501002c074002030780d0004001500450581640000d94014000f54003281d01043c0c3c8070006986401c924000d9039004442480010f80c601001d802070150b0441811000510326140e4070340e48250f4400342c1080d40403e840e4410300045040800040e0 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 41621767 1250 41620517 41620519
    0x304030b18011a0409030302070507090b150a05030601050d0e0607091502120702010e06040801050703090b0106021506040c23070c060906090306020d020f030411040b0301020708030103060c020a0210030f0506 91
    0x44007001003080e44035003e1880038440e02031990341e168541094000c0d070450312503c0c1c00c002110a070594070115a03015212501c10b99001d120241c0c4030002000b44d43c2d080d03822000d60f544590f07003140c0d905801103903035801904901a041d9107401c5d0115003000b041c05903900590055407490385150400400b074001041018a01c0115405086040e0018003090300350303805594246450b10854200900048007030042d0b81048003654644000d201d40c0d04d816038402900c0c0e40c0304010318a03981e070740c411040e6107440da2400e0b0380d0411548240055410720382a03001c45c903442898180003404140144482c00300f600508201c400c8640c00280c000e080c429075101980040c505458084000360401c40c008000314500d2000526042d00411407510103070094050300d9504000082c01a164946820030010105d000c91415004a1502000341c0041c1010700850f0f80094000010034603691a543d44c05e1700600c000c84c281c40c118041c2140100042e520554404040c9040b6500450410006c9083c4021a50060301003 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 41623017 1250 41621767 41621771
    0x60b1206040c050408070302090903130801020a0e0409020306060112150e22150c0203160302010b04060b030105012f0303090307030206130c030b060f0a080109152d0b030304030b1801 80
    0x101701c00d4000107001c105407641503074102000d8450b01034480c5180100d03002800da241c0d60f08404204220705501414440c0c9655852500e100b02d1001400110340c00b207800a5050b412040010310341c2e5000d041c100002e40803c1c0741c00103881010450715040b0610641145d107070484c49005014590010040815100190b0f05000512012542c1d0310600407842d0400850f0543d101e0440c1d0400500030b20645081d031011303c034071940d6a2110b150090007804400c0d49140705030724200e000320302c00d100328040e00e0580344180c4409007000e0054550001070320f42905c030702d4406100c0001000404400b40090360064503004021504da58079490042c0c2840801004006003601200b040300205e95044e4407102101c0d0055400845611040e002c0f528102c2101d10240c3c200f92182c0f800240e42c00154021480e090040603226503200c0d00030380c0e0a00342c61009035819026a00c8007a00c007030601045450291900c40c0580c000307241a802004682942c02c1644140c918034080b0b810050060900b010469030b6886110003 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 41624267 1250 41623017 41623019
    0x120e1201020c0d0c080d05010303080603100b061b1f0902100516080d090c0821041805070504031403030109060503030a020d11070305011a030c0d0b01050d06060b1206040c0504 77
    0x42542d031032039446810104055400080d0502c41700c0001c550b06103c00e00001e01c0749603141d06015250303100940c0c0e803038006d10546501003e45400c41c483e5180e01c1c000182041d01d40b06082a4511501d2002054849207005900a4010501003446410608100c1d1f000104a00c8081d004108424008800390814050100016250344401021501d80103074040f001c01d481708610704071140100031420f002014240e07000302c0407603040000280003100700e10000200f44ca40461074120340d040e0085115041e00340a00060800302510340b0740080b035000d20149449401c05680e900c03840012082c1580341d24964100000502c8a480580191800f805003900114038201e14410001c0d030701c00c0d403100840108406e0200405442405104140046801c0002071003480c044000a280154240304c1c1548644107507411104a82444584030400c01d4003c0c0181040380e18081c244840c40703229060840e40641e41358800b1404400040240c04500c840c401d18411324a00f403030034041155140c604402c103110003440 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 41625517 1250 41624267 41624287
    0xe010905010e1209041a04051509130308040209041412190f080a0e010e030f040e15010207030605090a02130203100b0408100902031203011706070f05030c03060d120e120102 76
    0x100f04c5000604c00d0b10005602145850405240b89000040740d074010308000520110400c0842d8013011000d00f2224807032652500369403103100b10341861000b80801c2105001901501c0e0061031190b10a016218507000c20300b900144074107210000c240481d1544012890f00354a03101d03040001d000b85045c3c1009900e1315110000035015400c0202070303000d0181c441d0b981e0b908082c0290003407040071140c04201da445540070301d8000c017160441e0086c00c040c84a5100001c902c19614052000c8040040c0c02034a80c0d60304640300c45003c2c050003481c450710351168002c0c800050700d42200000c8003d150140041c4c80781821b4540c1203c1014645c00740320070801c05e00040c0a404000305080024044420700081d03c45040d1003c6410505403003440e020005000c000080e0602c01006060382d4180a941501c06a079149a01516412001c980510001c1c000b400059600c01e08100150f400503030040c41c180d03200700580e845e40c4980301b2402c210b800088001407005440c0c1840c2000c0c06c900e03004500254200f4071004 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 41626767 1250 41625517 41625553
    0x30204050d06090501090c0609080c0a2d030f0b09150118090203011103010b09090a020307080105100e0301050403050903010606140f0a0c051009030807050705060114130e010905010e 80
    0x700020700526a901c40000400c03400f540b101418039401038006050030b80d02c41000d400180c8601c580410390003013105a10780d51a10344181019500e15130105075141a000590340c1301030314031100056501d03820700000320126410300b802d80700051054a03126003903d00814810700b404046030f00022542c880000502c00083e007041090209615104005420545400000e000d40104421103450301030020010400c840e14500800a2040030344071f088031519084000002c9200032914000041c04141c0140f00a1904d44c00700f5080d20a01e140541081a04800184c00c440059508502160001070802c009040a004600040c6103a0800c8464a5004900c2c00154402c040545040140015031a9106801140600c50481d0040100e88483c3c0c41421880000e0407400002d4021070300c880001181684614110f40309aa88600a002c0c01d9103047c1040d8015044a0500c80e44016110f035040604803140c03044400c19071002c400451260482d0030083e0031549200400d680036006682a000c4100e000303 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 41628017 1250 41626767 41626789
    0x9041a10030e070519060314130204090602091309030206060f030304170f03040905090c2b060b03100510120c1202030709020c030a08060405150906060904090302030c010c03020405 79
    0x20704012800341800440c07942842c016070401079005552100b00407100c1500b400307940540d400c0e610200b1002c4494001100f10203c100c401031500b6444044030030044c103013a003000c0e003000c1c404c0b6000350500d095200043d041209200d2041c1d80740380c2d40d00300705040c961304000781078003c10252481d4801070f2124000c42c4d200e12450041d01002001c404c1c0321500f48500704000c0101e180d43d9012740341c480b03071200d04100c0503040640e5255414070030012441068a481204010050080b0001e50707500c411054102507450b02202d0140c940550307440d03042744c0d1920b09002c0705240d60100755001031545043c9110700c0c850220b0341c12000c141418100c0039000213161403a000140c4003c50020b0048520620000345000415007140622078000b04014020007000800ba212400d003d40b0340c80c1860361070105020844008803402d10750320100307000740d40d10742c28000784d050b41000c0e0240456103070078000001300303042c0c505455080303005908c0003030400f078150803e228001d580600e40c0340561906140100089181c000 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 41629267 1250 41628017 41628049
    0x60305130f0c05030f1006090c09090c1808030d050114030607081302180a050a2007080f040803030106021504030e011103190801060e010305130311070b040b09041a 72
    0x28400340342480540344448000f80002421901c940c0e030304240c042d07140c1e00b415100d21011402c0550210703210340c0714000e0701c007814555605c00004a05d810712036000380907070b2601390082c00380d03221103c40e41408414802d40900b0800b0000c550341e8018060010442c1e10580c0a0907900d043c054401110382d80c08100c0540104c81441c20011940710740d0300380c4032039516001000754004800d18002d4800801c0d00265489110300e20000c1051f0365035020401c00ba612a0100100b2200547c0c040c030810700c0b80740d00540125030003018458241036901a400e8404d174090707004000640c0c00407004000d541d40c10412060400c2c0540d201100d6400c040c1c1e0b02400091040ca11241485607001e0300c4081100c00b0001c1d166001030409918001c14100c0b600600005020300a07040000d20b56480000e055000340640c0e40521000c0030b8503a00701611741c404031007a07080740e1400c5450740106280014510812800381000e45000c5514aa8071103400c010441102d01181e9806c0504640030607000c803e94495800041d080c0d0 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 41630517 1250 41629267 41629283
    0x9030f210307021005130b06060310031b1715010614030604051e040605010609090603230a02060301030501140612190203160e18010209100e0a26060106030513 70
    0x44008080c0d050107060044c00a6441c03900d41040b0f06410748000c1d00c4e071485d0140705034403e80e8458000f48405440102e03083c04040b040548204000b0f12100c3e030112080c07100c01020388450f9240c90760151060300c40b240d4022164030520442041500500300a4010402400c0c03a04040c1d0303c260102c28503000003088940700d40c0c1d81c2c40000d69204031b08030606071104450b0b649440c091030503141907402441c0078010000083c28091011880e03d14611a031010b894128010081d000c0111030015400003400c032070031040d0702508024100580740c01000e980694411000441c41c009440c1002c000d900300105403e20070011100b24030303880b0700003058070a4800d0742c40030444007108450000c64074000c405000071040e10210400040c031410b0084d4840d005034580038184d15030386d001c4141039080c0c3c001eaa880c3c80e80300d40401c0485040e940101e08031300c0700f081c001d060181007a980700c0032043c1c42803141d1885040080aa1460780041005000c0180034023401d080411803070800740000500c0303042c0d61100810942c = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 41631767 1250 41630517 41630521
    0x1510031209090603050d081b07060911060301030c15020c09070503150306070e010305060402070203120307030e06070809010c08070206010528030809090f040f0609060f09030509030f2103 82
    0x24420710801c4007070308028009201c000e54900d061561040f00140100c006000c140c0030490341508041c1059404110899250401542d45c0340d42000f0810f4031412509448401842c0403251280000b40d03008500991829002926081e0b1900d504c1130460321070411500b154081c940c5aa5520002c660416980d2800c16107030380c1c9841e07903006208242007200e50305110380020484450b80c440000b1540d0803080e079060000303483e0700d000e0006034050240001c2d45600003003920080c403c4d0076005154061664a4081218000080c0b900e0408405a03031031170010b6501020412611024040d91204080078503011005260000300291180b01c18003900b481244524a140500d11004c1880070030003540780c0b07032000407660301e00e000d90442e48800d400d58015484400040c04604200b5406840b0b59009004403c3c801e18540d1580002c100020044aa1039036034a01e01244144900c41c1d034000b03500c2519a19550480e2200300b42c6006142d40d801006a48602004504000c4031011080d00c1c00e01311030400c0d166 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 41633017 1250 41631767 41631803
    0x10b040510080703180503131a04030b1f15090503061005040c11010e06010f050a03030f03020a05040e2a0f1b12161a010303020c0f0a08030c060108151003 68
    0x84d101400d601400040b44465590500c1b0780400101600c4528144c20080722760b450b890070311546500c90b40d208100109200410104260307442d103076841039028265003462000500c5402c01402c0c150800600042c03400b04c0340202c0764000714010068042103009140300e00c1c001e6070504010210b40506c0d80180d4840f001070000f1405961324a03510301c202402807103408000d240741a0380318002d10500000d02511480000c1c3c0d414505850030540ba00355446015820340d00d4010740296009031001e00800004100008007800d60803003003409006c41c2d0308151303c11040c202141c2861074410103000c80c6102c0c104a02a005ca0707405003240c0c2c20607801196001000f40100c10981041c0f80320f501010400700001d03075180a5418880404076841c407501c01d0a0799450070710b02c00710001400b400000c0150b84080d900781e80c00e10701040c600764144002000c541c1800d8540020a0039508107203650149503000c41d006004480042c04290020406524410315518200304600300d11841d0388009080e1402c0503001c000c003 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 41634267 1250 41633017 41633021
    0x130515091e0604080102090306010603090803040b0c0d0e0a03080a020a02071205030409020f030907060e0603070809070f061706030c0604030f03050408061005032406040b03010905011a0108010b040510080703 91
    0x1d2100034800d03a121a503070542c8901039400040030f0391080c006c0380000b040543c003a01c20003001c036400c01a800d040da0380729502c40884140103401c0c9000311400b803100c1714600340140124005062038101620300000c003490040c01c0c0d0f00002c0e040f18111801403040d0050325500041d600c4c00c82d03800b1514406100c100c1d003811801e610641e00051410b60000401403240e00e0703040019070040e00c200e4104c034015651a0b40850b0440380307210240d42d001504102168000e80308000d581d030440f4021080e900011396491041a1030819540f00c2400301d0036007900000440b00d5404040d5100e00c055010b070030a0035a50000507410700c01c0303000003402035140c50011000e16100350117032000307865040112500b03401c043c1440b0900204030310030366120703204610003080540d41d02c4503c881c207002c0182880c0040d494000400c4040c0101000858066503940c22040114000b400384d40b040790140888034160386200c00004012080503000f45810881c200000c220b140c0f03882c00301041c0846e0500d01409c0940f51503000b100 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 41635517 1250 41634267 41634319
    0x70e0d0b070c030f020102030121140a030f0306090e070306051e1e16091701020d060902030a05071b02060711060a0306060306211e0f060213051509 65
    0x100c4080840200658242c00c07041031100c2900a440310300002d42091030481c281c1c442402941c280364005031001341180202204410f180b44034502011140402c88481032410000260a034001080c40b60941001901840303a1400741c42c2c042e1003800041c24145403550ba0b4040b42c4070013404281c1d16000589900c540e074005401031074218801511781d08211914280c80415581815415021350300401c00040500400c50a543e40e9629100143c4c0d1500004240198600400002c995000c00159040041520a000c0940b401d0100140c582c03e089032207904440000f000300c0c003031064222428901c0c141600607035030b4241d8100c0347d007641ca94003868428400105122386582081002c52000001a01a0402c0081e14480e90301040015511101382000030301d60610a014100040002c4022442d0400d9403100d200000340400001809541c6200b043d1031901801e6452560119260141000280c921001010100d031070703207069032001070958224404d4003001d078418082c0141200c0d0b07989604000f00 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 41636767 1250 41635517 41635523
    0x21005040b04030b0601181d070306150203031909030507150f06030303050402010e0102070605091302090a1d0601020705130b0301090615050f090106021f0e01060f0303021e0303070e0d 81
    0x5510340f03669141100e200d26081e03d240d404502580e914903a0702c413102050340c003241d82c0d4080c00c00040500112401c05000d01401c1c1104040d1201c002049030382007130340404d07022074542d030045542c1d281240c0d42e051035801c4014258000390900c0d0701138011035408410b4503440d41c0c000ca40441400c0305110610020b041258020020a041007030010505406600143c440c80c001e0b26007808902da191b004a8545903540039074004940c092000c0c04503402c001503035042c00707401050018a441d10010004624029540c03054404900403610070030002d500f4411035070030000a0006284a60030100003603815004012021030aaa5640e04030103160703400d401040b85603420460070072802290f130010341700c82d071205d0107514025106401c60080c1070400d020101d040362041e602500a032206110320883c0c1008034001e0b185036548900c000780b5031310320030701c40c00f00140003907141620018614500a410503d07100c0000140041800300352800782c0001c01125440700c2c076490105400c1d8942c00000e40c0c090ac12038406 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 41638017 1250 41636767 41636789
    0x40b0708071e0c06050a05040305040b0901030b120303010302010908011505010c0f06050406020910081902090a0b0301060c1403070507051c060e0a020a0806150103090f021009051e03070302100504 86
    0x41c111060b0025010143c0c140103d02c140141e64880d90120144d50007035800600040c4104010013a1a08082c050940d40105240106000c15401e000800762003d6004040440d00b000004008668008809800030080744000740080c510410f078031b070402c401c10301c241030501c009401e0480c02c020318401e20700080369100e4010022402c2c5070074454000d41111010a001d07110f410400301c88580213203440c921503015840905c01c1c03c0810f80540c0b000c0d4004a50007500103100c21320200d080d030025400b031400707001c01e076413001140c0c81541086565005100e01c117a003c0c0e0420000500828408124081a26810b68054545103c9000c07204c020a00a1101030201c0d460148100c0301c22030045580c090641c021500401000c0d1100c260340d813251300a0303d0340c0300d001100030180406075000350001000140540b00b130050042054011407000062554520009910400d040c4150b1800500c2d4084d041d444500c00b0f00700b08914000b20f6502c0c40d4900019100c1e80c80d44158001c41c80c0300c2c41c12200608015a25 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 41639267 1250 41638017 41638067
    0x11d250c1401090302070501090b030a0905011407020c040506150d1e091401060501030204050904120504180905061b1206060405030717011404020d080d0e0d020c0a0e040b070807 78
    0x140c2e00070841900300714018007507240001095803041c0151400da580440d136282c40c50b152895144000e05030040d04807043e5480e00c00062092a150320b1480c800d00d920f4000d00105040001000201e07840100490711608100821203440c0fa01e1030159020302c8034440000a541b0343c02965101600b00c200d8a452346903003070005490402500140380e41c19094090700a00040391500c0065007a40202d00032580c02019100010780400d0390744181d002b81d00303c9810319a240c90b40f50b0001641030318400c403000802948902400c402c00008000e4154441c0510413072007441d010b242d9490040744a1140300f054005596030200b010303075035075200312030003084010202c40c0e220380d603000040c4032000d0031085018030f0351030001b0207900f000c0089901481703540d0041c0a40c1928250750364601e000d40040b400756078616540c0c0880032600008200c08c044c1c02d1020f030018442c0200c6902003003400000d40c1c01c2040e20040c500240000140c0005000da040f1a071400d08220540d507a03a000c560001c0140c1c04039880c007110000b = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 41640517 1250 41639267 41639303
    0x80304051f0f050a0e090f09103e0703020a0b070306030c091a040603050708010b030f0309090403021606050301060306060e0907030510030c0e011d250c 67
    0x40045410645074450200c0d4030700c602440038481e1000040100e40d031100031400852149005000b04465403c0103000010320101164141e08119130992802c02040c00f4400042c0d0200b14000404400344024445011161803d005181c64648200d40390701c140d060030a06e400c4502c50490100c0c0161b04060740b14507c03801c0013503407401464001c0d10b02c00d1310200400c0b0170034440e0003190b05481e04950a42c0d00180b9150610004001c003041c0543c0303400d40451444140e95603802401c0c0114002c10090100d2410000c007103084134200c5000920030b0b0701c00480050f40301008004c3e10120310742100d62007259500d45c1401d030300b072180c880824101d500e040c1c50f020504035040030181d030503540540d804120040e2119815503400c0070f41d0f9042a44403010200050390a072294000c5580007a945c0710741500e0586e26580c3e0040102e464101c0755500032000c1c0180200907034100c00c1880e20704216401803190500c00c5200340303546008039021440c041074a091184080c010801481015400019500b2480c0000c03 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 41641767 1250 41640517 41640523
    0xc0603040f0c1e15110105090a0203010b060702090f0702030f0703050304030206100e0a0e101514060304020604090b04090c150e03031908100e041a1e040201031508060108 75
    0x140102c80307004160001046400c4040c011a0740f08241c1801e9818407410512000008800c14003800100300500300a071518501c2030051070b010301e1b400c2d4018100c01030503104241c00d44005800b850b0044c0018406480503a9540c00c0707103600011030101b600e000761202d1608904511a8100540e840d0000007071001c10181d00c5402188a80d00170b81c29100182c8820722610400e18030391060884030000b41010900300324083d4000b03224032600208542100c0070101e5840250360868049600140c0c05070401c10000002c0e45110600400c00c8400070300c0c510b07080c0c2c001038181c0501c3c01140300c255a600f03014681c50b01e590b8880300c1c1440c0c00c020580d603030960311604081c4c1400e201e1032070b0000076014103840106085c000241d0360105075008520031058082d60003201ca05900a06581c1824441d800000702c880300403180d540168040c40304543c0b4072aa101150400c1c95000d007122140c081c003050b40d482800e04400e80c15402583c2440c0201d00401e00c1c440c00403006d40305400c1204180616000002d00504c00 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 41643017 1250 41641767 41641793
    0x6120c0503010501050904080a0918060602010e010203010602070e04150906020a0e01080c04060c05120c030406091a0d020d1416030c0c390905010906120c050f030c060304 75
    0x501a6400425120001c0c5800d0700e01c00c0c4503203504601620003181c00103410034007a2040e101d941c60b00c5003000341e81c0d0300c1e80c1075020303d03140480c80200d60f03400050014503428000c00c40c103d522a0000d51655140c000005d40d500181e102d00c540758000b000114080100304881c44201c0c2c01c00000502c08030065003042c800030350007040c07040007003240d03414450b80325400384c036403c1d00c41c9128a003078908091401005483d5007030300e07101c1107440313006400a0700c2035144410060b1030b0400c0c0c0f0b50021900d903824408054103501c20390700048503042c0400c1100c19002543e40072504030500030480981c403a44244120b90140103030300819500c008101c030030849032903040d04444072206040c1d5010301401c9004401980c11419a050140102c001c15050039026908010240001c02440f03403c8180405c80c49036056806500f0b82118041c140c50703030010006820741d4000d103409000d0007030542d500115a0f070b807102462401841414042d0054070882004c1c1d42d400c0c001c0c0c0480e150094621590783c500791410600c80180 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 41644267 1250 41643017 41643023
    0x3040b180a0e1003080a02100216050d090b0a0509010c0f030809010510300506070f0806060a1d060d020a0804150b030717010603060e0c011d0d02040209030708010612 73
    0x3400000101200d0b490542406012142035109509040d5210b40003d83e000009000961080d00910042d43c00e452006001c6070180c0700b0890101c2c0307020310304a8148298140a0001c200c4202000d01c1104015000c454000e020b50402e6540e4040e80c40050381c0c002c0e40010301600302160954020b05154105020300c0c40351200c0d400800a987d03072605071101030700c83ca001c1c3c001c16143d040070303411080c100da0030840c030800404100c5251004a0342d58913444c1900c1259580000f0710354000303030444640c100020b644c11a0b81220078034282085050010203882010803012460300e0020008402900c84008554411407002402d41d40c44900c030501401c031030000d950454400c543c03012002802c0356184211103400100138003400c5c0e114038090b81d1a240c2c032080c0010407007a540e983d00000000d101c5205440701b43c0d08003400740207051a054009441c081d6034030036403401c03110214005991503031500b00080711168100c0d0010380f25807001c8042131074501140c010b0360705c40d86054404944001c0070310103248403501c = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 41645517 1250 41644267 41644279
    0xb0a0320040501060c0303020c0705060c070807060507030f0305041505010b090a0503010c05090d06021306030f050f07020c1507050d0203030105030f030c03031302040b1e0102100b030307060c0203040b18 89
    0x30950062004998092113610000b40d284800500040c0c0720f60001d115441965084440c01c6417140c0000303a050b03100341c501480c9c81e40720b50f4080060400900c1802c1c0101b440c4d0400c13038204803040c1c4000d003840303100702c0d1400704255483c00001c04000b02c03048c1210131510654010441581c50700f4101e800c81d4440c00b90688511503400c0d00203040e00d070500805164480a6440c1414140b46209100e004c0c0342595040314956000c0c03118881103000708803503000400c41c0f680c01082040300c03000d514040318009080300403c140c1100c200000b690300040ca81c416040700b0f840401c01d0561003003100b00c0601501c0c000600b58000c08100c449a15400805036041c0c0300e0450070341c1e0484082021160340e07407084000d0124160400e05c0010b4107107200c401c0c144038190010f80081078122503a0700041e00100404644113210b02c16600d000000e580c10411100780c1202c00008100d408a28800a50307a40a081c000a0840d501c8104071021715100780144c03002403d070842001d490718050709c58800c3c001216001c15000781 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 41646767 1250 41645517 41645573
    0x309061e0b060913050613090b0118090f1707020a0915080628020c0303040303060f05180408090a03050703050a0b0a050106120b0a050d0b0103050607050f1b010b0a03 73
    0x100e0004121806144010302061501c003190b00c6500240c0402000c140c1c2c01901410f040100540c7d501907803c440380b05408500303c1d0340c10030303041e040079499600003818900d1400c000917001602d01c80306c00191b2608000760740310b80e018850041d01540315550780290010410280001c00c0e20302600a0355850b078120140010540c1c031082940d90312081201d40d203000d01e607038080300400d80c1b01c5545042d550000308000941b130024420b880d1441d60781700740c5003100003e0f52040c0070002c40d00503078541c00241400325050000300e214040070507020b034401ba1000d00303034071f00000d140c05085d42c400d2a40e20040d5803003c29944425520f0410503140e15a244c010350341500c821000035103e46543c4504c42c103882c240c0c0c54809000c202d1400c0c00c4020720f07038000201d8000140040c00b05060340c3c0c0c5001d8841c2c00c2c2c82240c881c115581140340660801c100a03050105021084c02140040340d08141079402071034080481d10303203032101219403074050710001a19640081600b02c011003401102d181080b40d209222444070f041c5 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 41648017 1250 41646767 41646769
    0x15050102011104141908151f0605090a050a03030c05010b090402090408030402040f150501090e0702030307081918060b0111120f0d06080706120603020105030a0c0309061e0b 76
    0x601d800b907203100e2001c04200b0007440780d00311014100303003207141c050000d11481c01711240d50443c9800580000304141d0003d0b0346680384c80000d019aa6101c40245060480010000080b0040d1038403406144103001c8040f4825640f500d035002e148004000080940036030136a2402c025000c0d074400b5006031019400d01201c0e50450500b840c03844e01669015190607842d603180e8a84134a9030f00003801c01c03a1f0094440e25080c0104009000c0c200f1140c102c504c00f02407003460103001401da80c071654010182d85c49010f08104031541c01200340c95120015041040c500e544181036501410002c000040341c40c0d140250041d803c211011007502158484d0104211402079280151416810481015025440b810140044c1c030780c40d102070001c06291902041c140f100d045485e5007611519041044aa440b455040200a0f84052030341c06554260008010050940d00001c0c910b00c0000c10040364180c0700c00d070501010f44a684038900441e0816010008104200d0f50f01d12003c00f00e0000d12812402c0c880f0820301 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 41649267 1250 41648017 41648021
    0x1030e070f03050d030b0f0f031c030c0f080415230405010506040506030619020a020313030f030212031306020a090b0d09020f0301060806160e0901090204180207050307140c0604091505010201 84
    0x1001b500818202c00c2caa0804204580c4056001d602c40c2c05002d40c0c000440d24645180a5000016040c1c40229855442210042210303180b1420b480c1000144014003010940c180e0781c1e43c040340b180c0034020800c0e4211501c0e802505403421108803007007d513401003005114040d404070b80111000c403010b10603030700d0300310400d540c4020964075512880f2001c0042d142c03c0481d07034020200400980103990419480340045070010301d90741d000380d444402c501e03580c108060341400b0151569035034408660460074505140d0584c5000007100070141c3c0d0340040c8041c105e90050444400811141c203c1c15075942c00e440040b00609440003049002e051740c0c252507202c619040c0a02000c3d0b4030b40b40d00422666a541c0c80011072076204011001c14403010103d504044d0b04c451129601906542c400545e03224549001c2802c8201640c000076030107881400a140068808800c40b08041c3d0810a05250304540b05402400c043c0e1304048503911800010300024004080c0e08619410745000882c1041150764034011f9003 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 41650517 1250 41649267 41649281
    0x80109060f0825052115070f0f0504090e0c0117070509010c080d05010608160201090209010302040e100f0603030305090a0c0b03040302070503060703020d0c17070e01030e070f03050d03 81
    0x642500440503d1141c5a040b11004000c40b201c0d201c111100c030303983d5003c241da100d000d05444800760071444442039125401c004005140d4500d501c03103800c41c904501300514024841850000300648412101045403241058030003400040d1f00402c82040203016030b641d2200ca85140703901141802001c001205012044503121f00500d032602c91422100000455070501c5054044130729141c18070120202501a100e9603000e014151103088950500c0c0c10508503051003a003207201103a051441040068403622480e0307044070ba069030082802c0050780e14032828400d042c0e9000d0511407a011190a10003001d4201d102264003d80b020403054a40c0402d0301e0f2185002d60014184100f000c03402c120110043d0006c5034014003d20540f21444d40340c80000b81031040035100080042d0b004241203250300ca09100e141144501c60502c41280692010035032642d110040c140d00500268940c1c00ba40341c1d0280c0c000d0b20070804d800c5c056454090b101d00889001a50078042a0790901c980350b00088818001e1003244 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 41651767 1250 41650517 41650529
    0xa1e080621060703020c10050408041e060507140f150601090e0f010611150a091502030708070305060307080a051501061803021c02060c1506100909050408040b030403080109060f 78
    0x10719a0343c14400c1d0042d42c800e1850b024540f00c0c820391104110102c0c410180202d00c1140e4650399a45801c580c80c01441e6211340e07108400480d0302c0304118407500101143c0005c2d82c841f2846044034043c00a050420f10030800c40713483d500840b140042140c0e911003400c0e1051900b62554909580c455910208012080315000c680b03055140c0103212240c003c80001c01e04038144004c6904a600080d0f0500341240281c41142c11680c448140100700710782d040180c2c0d00d00f594030700c08605607d4603150042c03e01d14090885400d05a4078000b103406d507102400910098602481240d061400c2481e00340e81da00c0540205181d640060030000c188640700e02c02c06035090f5803a001c4c4560443c15a000c000592000440d10000201c0c3c0010b00030040c0ca880c406022118a450050050300035014900c5013403040051507184640e0880c000c0b41c1c2131540207a40941070b191301d03050002d8569164a0420901d01c0342e80c0001c0c1e200c0c800801003004243e4417a4000b41a25a200014015280e030345001c0c03403103190741d07000318 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 41653017 1250 41651767 41651773
    0x501050907290c030406090303031103041203090804210b06040b0607120201060e0c07020102070f3204110c070b130303110703021002010608010506060f0403080a1e080621 75
    0x880c0c20b080041d10b10341d001c406001520744404200542c2c9940d0060b407040d80891100c0000f0800e043c1c02d0f10862103440051034145203146400d60f2048000c0030704825030340c1456554145030007030110b08020b0740c0103031000f880340080d0046281190a6805100d880032170381034002400090480c10b00e400761980c007140c0940418100101c40d982c0c00f4040f10700c0c0c5079030001c541d07071101c0006801381140102c0d4000c1c15004510b076942c81343e90000a0500e886508216160000703500c0c20005003800d004101d024000100001003110650550ad250070907200c501c403036200b42451201114800114018005443c0901c200c03010300740d580f080032000313004002010300c050036106e400f0404a4001d00c00e181203038900f0800c2d0766800b900e990006041829076004000180c0d51503a040c003c40e002481581d40141007240d0300d504095000c0b1081c80d05102c0c0d03000045c28144080f59030392403140034090303c955012908410440e140481030000f040100c0c211202c2d8800c00b00c2003506030041c41000400c0340d80503255006 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 41654267 1250 41653017 41653049
    0x3090306010b070615120201110c01050301090c03020403020904080301150201090809010f1b05030316050403020f0d030207030606080a030e010507020901030308131514070203040f030b060a0b0a0207030501050907 93
    0x1400c015078101d100f040e515213464549070300300c9455110704440648403208201c50343c020b807400010f141c1040701d2041c0c0102d070300c82400168543c0e080020307281103984441000c100c1d1480410102d000e40510f5200941002c40b540c28041003101c843e01460590f030100d41480390701e58007070804a0036a03c4c01040a0b00f40c140421818219512800c02c01034650f03810706060140608003a2074046d4921506c0098031503402c0402480b174003000404407101348412500c0c2c030501301801d40d000904900b40042880d0f108418044507036003058001c1c001c400003583c020b203042000658800499072500381e248821800680b04910550183d030164003542c09094004c2c20081c5503070b0855400313407240500941040b03444a030242c40800007400361041c2c0c00b0340c0411030f140466940300b60420b18900e100050161419508140000d01010340039030440700c110713034000300c0c44459500da45c1d0114160402507003000e46884000641c17100060340010724001103a2080c0c00802266072401c218684441150042e0a40c0c18800c00d4 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 41655517 1250 41654267 41654279
    0x507080301030f0f0f030f0e0301060503031b15040804060905010c030e0405090f030a020c0901060206090a06050a0908040801050f150a030201110f0106240207030b07050c1c050711030309030601 85
    0x90400070051007442101401c0445403112103c614a58a0440016050b18403147c40380703074041010450b842c4264024070285040c0300010b51070780110000a940d1800120015549200030482507024040d0040306510f02d003000d0500381080d034030600525000c00c20250000541e94400c1007120041e40c3c05590345414135441c0002c000c080d100103800e2071200d01c078561020004000c00c1c00100500c4000d600180948601da0051200c000c0050307000c10103541001040107141e0780c1c0490078070782c3d0725809000050640d484000c46401401c0060024009036408034010564103070540c002c42c020403686001044a035113940740840ca0300451482c85400c40e110000030030055008440300d1040150750410740f00001c034424051800c5482c0742d4406848285509010300744084038400e04c0e41600c2081c8003518180d81552103483c0090300c00303003181d42000000513070100f4246040c014280351650f81000400c07080c106490042c080c0d040510306481c1c1e203020000c0c0503164030b000421109070105c0a005811168a005 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 41656767 1250 41655517 41655533
    0x2708130e0609180c22050108120a053106020f0a0201050a0f0201020423010f020610050904021f120b03031606050c0706050109090b060319080a02030f0f07030e01050708030103 77
    0x440b00e407091311050001d550340c070841d9410320700c81c408040d410341401e07880c00c0f019200c0c10303800400b41d504409055840001010100c401403211303418103a0760750701101128806650700619510001c0d0412901001c5114440d510703600302c078059421603201010420305142c80303480040e80240421020811202c1d0503005106041598606000040c01d05035500781c1010010301d0184944404d03030103a07848448541c1c2103011003025001903c014100703840c0c0425888440b071800c0c080e4030710691485000401b1507503054210031005803940d06248920203a1075002c1d00c0702c030b01c0d0000c058440d8140900d400c49402d00000391008805605090007000516403500030060030080c11007510300b40204400b5003c070f1110b000b014000d0000c46000203040301f0605100090300005040c0a102e5088602c48502c1c900c000f44500c00895008000140d031490241030991031841044c0d03400c850040b010405001c11259140078000b01030082d1941e1a090918000445961003401c0d802031100c9014001400890481 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 41658017 1250 41656767 41656801
    0x914060118090f0b03120f03040f0809060d0504060b0d0804170102040f060203070302010605180609090115080109020f03010c0210020c010204090513140102030108102708130e0609 79
    0x204420520302c2e1265011829240a0152152655102d01104071141400c01c0070444081c64108410f00380f2803510320034095880043e201070520401d010649043c0102c1600b12925410001e002e0b6039288a4044600302800c82118161106440c00e594902141010302460007041d0f48a03907801e00d46800c14412810389619880010180c7d9070900000c0b51424501c0460740103000300ea0011625001c0318600242034801d2600024090001c04da4081d00c268112411150061f030100e80307035421aa152807180c0d00600c800c0b01e450008009051001844500c1984007103e602c1c000d0325505a01c3c1c2c0c16509160a0381c0102c80c180c801a4890262140c02030140d50103803490080220002d45829503a8030a102a200184c50651210903480762036000c00070701103450806418950025400c6600d0644002d840d88950302d04200c0c001c2d00c90200300170158518050f074001184901c2611404102c13410002119084892140b455400008001c21680005103a0303510400c4000c0640140b1b40e629090580c183c0b200e = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 41659267 1250 41658017 41658047
    0x5010c0b101e0806060a0b09040506010221040608060312040302090408040b0a0f080702011a01030b0103060f030602030103150603020904080f1b0c040609050402030705010309080409020406021609140601 89
    0xc031090100c2c041d42c107244280620300c071000c04050340e1402c189016050038405020103100d05040b040400008020405451100000f150000381a6031003c00603401d0041102c03000c800281070480c00340803007800c0c1010304161019540c0350491540c8540c24169604941180ea000408040c0000c00042c070b070002c0500d503c070f44a016180c1c10180d80d01c407100c045030002c0a02101280c0365040c4100110781c0114241d44c054450b00c024010300081c9903c65100c0090b0450341c0381055141c0c0604d5080e64081c1e08800c00610161004d8061503071b41e400c01000942080c081181c4c3d800c51001c1000f40c0305580d0080b0020389030018451601030301c560b510382c8a1540f24452042410105000442550f0a021540c0e4415500c1c0030203001c69581c010104421548180c01401040e46400144000368600060500c240c1e8000e080014884401d81407801181c0074607070100c21000e0000a0218600341c1c00b05041164403e9050900b003a15203c00140d41600c20141c1e601d02c0e45c03101d94000900541c0711704020f80203105 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 41660517 1250 41659267 41659291
    0x4090201050c0d0804060b0d0b0a0e07170a0506010506130b0d0b03061f080a03090b0d02070b1e0f010302010f0807051b0a0b0709050102070b07060b0a0303080a060f05010c0b 76
    0x741050b0002c1c1098010b11400e000b14000c0010401030144500a0f9000300300d0846000a411180b0b070740c1c0f001c0c490006408401d03c103640c1e0300580c0344a1002c21a110142416500c01013050328071603d0903a072004181012500ca02440e40001041e0601d081614540f600300460801440d0030800400c1ca1a0029154604003a4a4091007112900c0501c5114051400030201d050714443d9404190b5020302a44c1c0403650b15403240301400c0100e5400701d0042d060b81c003a4541a0b59500c4c00c81c88440c06409803002c00707000440d098060144100c140444100c0c155240765191017541c0d80e40080041c0c0410910020740487c40b40c440f0910041d12614072076510120f81c2c1001403e0601c114100d242000e0110001c51181c0c0c0001501400d200d020300107145d0000241c40e0a08030a0b080c400000d488101034410382c078800350041a49410040d4940000c60724010150100613055903a0400601d00e402c10342e080044189000c401188181460040c032081d5201a16200140c02d40340d41c0308246058000c2c41d600e9034107 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 41661767 1250 41660517 41660527
    0x703030305130605040b06030f0c010504052106071806020c0f04020304020a0e010906031103010c17090a0b07050405040c0921020f04020301260109050706050f12070906030e070b07020409020105 85
    0x30f03020b00c0b500340140d019801c400f1040c504041418603000326980a405154440700044055070f0340f00d0121026110140e8014810300208240410320035820021100329010f170704100419141d01408205440c0d182c482c80465403a694070701603032144020705520382c00612500001d1010f0500350019034000d032014040784140c550b68801e070390085900b80c102804c6503484400410500c0460054010403030812002000449507a10300a07128a08584241c219030044a000484c1c5480a010b080b489503044803a44c80c5600d89500000e02a03405030141c01e00c218902030390700901500c600290300950b000461203813100629845010080c20310608201d900c6030110032010800d85660029500030010035400c03600c90b41450318408403d1094001c815800ea141c41184400304200040300c5085800d2801d040c0e0762249140d43c060300b42d210740000c03a000704107070310203101006074070040c04402c80b01d0315581040740c03600d41c2c0b02c5c280e103541503407140581c40081413003901d000d0318150b1700c100d920920506040c1e10301 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 41663017 1250 41661767 41661773
    0x3100b01110d09050a0b03010b0315120a0b060108090609060109050c071b030303110310060c0f061503020916050702060901022503050d0314241201020327070303030513 74
    0x52102e4484000192000d0000c20145c14010540f601401c0014511401e641c10020900302c5808020b00d410070103c4961945541c42d01c607060501d00075600300d0300740e1f40f241c400e600301701500401c1036800c507000822001c0024200c0001047c20360040c00f910010745056407800310310001501c0c001d007078030055680030054900083c1c2c0c20060707240b812950508994201e45181006000c84407182100c9810301c6d010400c005214610540003820f640250410542c030960764201041070069858000700800d00e8901c0d2110b818441d840745004607842181d02481655071400d06500004800000101081c028452540146001005004e0491062045510680540ca0348100000d00001e603007006645c04c0e4800c1c014003505000b4500e046d26181000d01c40c0c000d07c40580350100c81c004100c01c0c00301402102c001c02c00004040d008050600c01055010304241802b8014000d40c0300b520307042c1803506c00f1140300054602041c0d20642c0a01404040c102c01031454600f076000e000000c2101603401d0780746d180c001c00 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 41664267 1250 41663017 41663023
    0x804020618010e131e0204080a0f03030b090a0902040c020f070308031b03180c1f12060305060a1505031501030305071104150303021005060604050d03110f01140c03010503100b0111 79
    0x1030301400c0341c000c41c205107104407000304151407030170355031103540108000d200e40c006c005a20140b461f444801d0740c00c110342c142030403402812045007080c0d010070f0720b205120302200140c2142c45190300848040122018115003642e41d01c44002c80c081150f00190300410104210310b0185034004100f4010240c031840c00c008251441c0c2c403c503400c4407100344022207e42268410090403200007015209450350440d00341540940b0642c102842003000490003a8806072409a00701400440c1e124003150440d080500190016155141d100c074078a00d005600001d00f440c0010788540004070304100c6400c41c0e401e4ad2021901540101300aa5074000407072040440f41d101c601c150000d9004844603520385500310b01c1c0c001d041c5540003452002c0c0b24100340500c04141c4c2e842c800c82c0c1c1140e03400c4401000b001c48910b4181d90114a6031001a00e50007100e41d1141201d0064101c2c440748483d803004200300f0303034a290148006010078004d09805a20142381c0d03c40c940303d281e00100304c078501414407003440354280c000245 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 41665517 1250 41664267 41664289
    0xc030d050403021f020f030f0604090b0a0203010611070b0f13080f0d1202090109141201050a0204031a010e070305070e06031306060621050402061c0605010f0804020618010e 76
    0x40140c1c011243d81d1450030213880c3d040d0800240c0321080d46070001c100b03020391007804007410040300c3c1407040f40450480e039140c1e031240780c035a0b0f48079486517018a02000c884009400034030500300403407079100c0a030a007050086040d00942d040444041c0c1084c0e06103540600c10340040303081c2c07458106502c0c0c012415000401840d8003402641c8010420f02e00c880d6001400c181c0260b551103400f5006200c003403150380e000301036401503410042c1d1401c0d194440200040e81010320808042d000d502c0e200a101520764160003d00036030b8020015000401c515543d070145038082481440760392001c5034007184015111f80c1240b40c2001c12440c04000d0000c141c000103e16900c20b51740d2580281810114204109040c081c100040280303041034105ca040b003443c100c3c12066038080c00030300282d83d28000b90455446001b40c501178120708803110707506d019943d40c14004222500819012844005540c49001d1280c2801c610455000e0040b50401124011a1507048005c0c0030240c10b2020b2040c2c440701c1c0c4e44402646903 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 41666767 1250 41665517 41665523
    0x610021c0e130209100e0306070c020301110f1e040506030408181002010c02060115050f1308010c09060e04050c04051e060307030f060815040308070203071b2303070504020c030d0504 80
    0x140e461400b0000c0099409040410805200140151546da80d4001ca02c060380310341c2030700303003030000340c440d4400240100501d00c2d070503c01490105403000314180c3c20000d080440d111f91403041410070668030700034560085208040e07102c0c1c000c00010f00002c0f02200a400c2c401030b80380543d80500c010b000099812000380410030010b0790758040101845a0421030310b40140a8400514500c600b40c560062003031145c82e00c5200c6201c000905c124100c0108800c200040410030f0003000b4801003040010080c21081c410900081c00d0016440c1142c030781449001e00564010b407200b46028500f03801d00000c1d2204401d03010030000c00580000d07158881100644c41207070366a900044009118a00c2ca00321a039a8102052942c4480c1410a2816182404075005501800c000c0615620100b08915500c50850020310100c3d04221f40342e075041c4101c48440655500c103440c00c0c0003048010344c410320020840411507141d40500001c010500f000da006000391791001e001d4900d4000c010500d0700555100383c81c21 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 41668017 1250 41666767 41666771
    0x1050705120301180b0d0201020d050f04051f02100606050304030c02030a06050c1b0303041208090f0706030603030306060203130e060315040b010305010501050108070906030c0c0f0b010504050610021c0e13 90
    0x10131011103640c4185004000c084629188220041c0c0000350303034140c0159a04144400019542d00d2040600300392001060024005c1002c6038250307282d02c800076001004800944121101c401002d1114094201036070807581d103aa0455880d91021150700c0c103514820707a010f005590040e80481ca0034025144503003654140a82e480600304c00f4a001d094450b408035034250014414000010402540c0070520903151400001c5a12021004d90400c40c541082c0f42049c401da00d000240035405070044021070780203490410007103980710404d82e100d220344100c0b4414006600e0052060039841050140c1002d0050100c07000501c102a00c82511a03044d40d0540d03059148000410820400340501405010207190654190424803c09801406580a85018551243c1e01840d2580c400c4075020303041600600350b045842d0720f900300404000d00030f000c0c2c54080d40c100701c00100a4103110509120740e000782d41c020070940c4480b00c1c0240e0320300c0103040c5501c104030019002c10800d0345d032040354405090709030b800 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 41669267 1250 41668017 41668049
    0x40e0607020a0c08070b0f070206040f060c1a0f040f030e060706060f060302040b040b070303091208090f070b04140a0503010204080d0e0405040b0f0a09140a0308012301050705120301 80
    0x8110f030304854942c4503015540c800d0350140400b0300c05a06a0705640600080c003a203455151000514034011508002c00607002000c0000e0200c2d40152807032a154041d0810301c5c00c401210780c81c4820844210f4004252560303000100f8006150400748481140c02864008100b104403400502c03190300c0448203a075000d032100c0b401e000250784840140001e01250400f1494a40780504032001c074091440b400c01c00c444040303808010705000e50480300b54181d104441c86020010000c000c6c1915009440018540c0310f108443e560b0020001080b0041d60303904411141803d07c0c0c030601e03442040180002c12303000302e0541030029594800340060805021040080d10404410b804001c000c0c1080d030310202d200b00c0c140014480070a4280720327401c1c2c000703654042c0c8048a40e00c034a14031024081144008043c5214030b6040741c8004404544114142e1203907480c8552640d80d00359603401c030060300c25140700300109403407e130049600500050010340c4c4200151980006040b000000c2c5030405d0b0710a0940c9800c85034 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 41670517 1250 41669267 41669273
    0x406051c170307140a02070f060c050c0a0602060604090201020111030103060203010e0f0c0702041109150d06080f0627120306100c12050d0b0406030809010206060a03110f040e0607020a 81
    0x80038030240641400300c1e400c520740403e0083c414158428400d040c984000b0f62085640e00c2440488081d1501c5803100c01055a98240113210041c221340c1580c05005400d420121840c0100003001140c0c500d500500c9107072901c00800005044c6054228150343d42c40381ca00c24414080300203103000358040c90700140c0341e6140c0f8429001c01d4400034550001c50520100704080d0300ea000003a1110150144c400043d540d80003926100c00340f0130260b0856102402520500440c1c031160300500d10850005014451140d07103951095841e041d04080500f203401c01c0780024070074452201c640703441084000b02410661074440744141440303901c0001c0d1164500000c20880c0c10308084110040799101890101c24041035510340c0b02c0e4680c0002d21110401c10002414485500c054000c00328856004000700001990380ca0048e150390311201d03030a07026005140c006140352404509441c12260000141060490b000e803c001c110307501011103a03409540c1d500000c3e22200f0070801c8a04c0340e0f030b03250020410321030141 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 41671767 1250 41670517 41670533
    0x80a0b0708160c030e0303220602070e0a020904110a110d0e0108040b15060c01090204050a05010f03030e150406020a03020705060406210e0f070e1f0302010e0406051c 73
    0x92920052146501c1400703207403003000c00100c0000c10342d490308041031245440c0032144a08400c1000303a2511010500c18405040c80341080181404200800c0d0030301c2d5a944240c3e1202014411000c3c241514400070b1010300325a0003d220040d00240f0010f40c9100c03d0200500c1034004211040020701300c841941c240400800c100411103e00c0e0624210161030100000d012440c003c000905004945010400d40913401d13012030b49440d00242619154254000c0c514024081c50000340e200d181450046a43c0341800e10905050381c0f400281091000e003940c0342920141c0c41e04050903008a04c0c100980c010704c11000c06000544100d030302418070710901c0c1c14001c0c034016068105910030716081204001543d0044410505040c49401d04400d064103541d100005101400d0141043e01030001c80d81c1ca960408100102915441c400c4e261541e11802060588204a0a8079504a240700c03482400550f000d80803010411000a01c00703d9003949130800702d180b0b08902050500c200e1005110001008028 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 41673017 1250 41671767 41671771
    0x10090506060712030b0315070203071104050618070212070602040504050a0e07060c020604081506100f1407020d060c0509010e01050c0606060f040b0c100b030105070e040203150406080a0b 82
    0x1100c0715070600c1e4090b21001503c0341c80308040000c2c03580d5801210610f4406004c04070400703044d004802614540800c01944075030001c07500b04c6414224640ca04164641845114000c1d0005446903104a0202c1101081042c000d0240300552080881c13900b10203074420000c00c12580304820250325180f07004107120943c1e90181003640218106568042c03600d00028060045804034602034080240314000f0914912840d000402c0d24056640108001c3d02000d503030300d0256105803041c50509007410000c54102540b08040303030000362401e02c00e145a5020401030200b250009011098068099a501003201c202031048000300b07901045c2100b5960704400f020034880004e003080c0b0328140914490544038500141030b5441840085002c20205080e070003a40d0140a00d055620356514926582d29500d00c40044071400990030104181010b040c18011a40201d0f202e0300c8000c015141c060420001c0d41004bc05010312401104120040341c1d298041e0400a000310f0700070b40415200390618400507480 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 41674267 1250 41673017 41673019
    0xe010305091f0c0504120b0403020f030c03040e06060906190305010f050901090905010b03030d0e1c1b02120a0b061503040b0a02031003060615020f070501022104030b10090506 77
    0xc804060b05540e0050304041e0700e0090000000101c2c2585048151014091508003601d98480c60b079803402001000c00440e40a1406602161000110000c68507540d20910500318029001400200440103c41501d6070300078a00820090a0500c140e01040150300030030302600ba03508448070600005074061007110301410012005000f40c03030929004c102c6407141032007050800c43d070f0b860308001440030030b52050514880080070b03647d8070015800c2e44ca0107400c4000c07860002d030080002466101c0740c00c1c00d016642c1c0c583c50b120082c25114010440300b104a0a0800382c6c1c11215000d101800e2940921820002e035118050140190502c1024000c086050603084222880c00b0403d1002140100c000b540d800403d01c2c40240e501e6a071020300108202031540024903440c241071020503405001d0b0004035590803154211017220655140455503106584200c03405600841c2e2121780d0103e15055202c45d1000750040d0514069682e174480f020014129200b10340c0850f40f078414840406d039400743d9504000 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 41675517 1250 41674267 41674273
    0x30306050909030405010804150617070914061011030c0102040e100501050313030908010c050a0315030309050d0302030714030306120a110405060d02090a0f060611150403050f0304030e01030509 85
    0x2d8100b003010b640b4800c03070041700d060110420014040000c1551040ca10b11181d12060001c60742d00c0d001c5020502402107600e4041c0221840840d2110312807142e9502c80344c402d440b10f0207684440701401001c440c005514400c2010302d61003080d02410800c000c0c86800c1290f8001a50b851410301d880c1c181c180050000201c019400a04108580c0e001c81a40d800c884400d000c515480d40e1482d05440112483d44109815420303c80114100d035041005040d012406031010700102280070a403104280c894003004011032120380342800141056181410f451b4032900440703181a525840d081c108000384203a00d2081d5000001b04100307800c0480901e03aa18202800400807aa41981e962440c0004035001c6800b172951200040e2040d80e8140d030340202e00d41c0203010305400d0b0030401c0f02c1d41b010b002c1081d800c0b0151400d0482c0001c020740700707142d402c1040017510040d0800103211004840a000c0c050400d81c1040400d06c600c0c000042e00c6401980144d1207911040b00000c61540098203440b001003100720950 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 41676767 1250 41675517 41675521
    0x1c051b19120303051f060203030f07050712080a0905010204080f070510120b0a0e0405010f110a0e0904060213060e030607110a021212121b0702010203070605060d02060c0a0303060509 80
    0x5000040701c0350455141c1404070b55940c1e01071400d407204503030880d80c0409160756031000a4441e008001180100803d01140045036148401600c9900c241c02c8014000705600e03010307044403403240b55480d0304a4554200410400c903251a401d003642c22641009819400041d00440d000c0020048940184400c1d00c0041302080030400c0038101640d00b11b000401d6030344075846500c460740c80c60305d0b10020f060840c03144601401d041c2020b0b4001d1802155400d1b40b180f0301105911504140c400382d940c10500e80c0d44000308500100700340804100043d004580044e024002161050401042c003006000c0c40c6c2e4891104040c10820549031040107881102802a124281c85810b2004034544030b0240d01075a0003260094118491441c14404842c03405c182070004c24a080004d500ea00700c1406008070310706000c2c0154504004041500c502d01c4020b025034420170581c0002002c980016600400c002d03d0a0303240307003860300440c0c101d5210091203191900000529002c154051085001428007542e03007514038 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 41678017 1250 41676767 41676779
    0x10e07080106030b0f0925050c0c010c0206040806010e16030603320607020c0a0e070804030809030903011103071209020603010612150609031505040804051c051b19 72
    0x10300040c0981000c0540b00d00550405899180d800081d000025180655a10341807840d980040010101c6503e99080d084600c3d0106100d40c6c00d0712030003980b50010709103900300b48005481c010802c500485e08450b050000007050903080c80518000d116144d8403981c1c2d40340007040c04003c03440620f030180034140ba107242030000c1100d03003d001070705480e00d0b52100e6200e102c8401403040190300c8043c0c0f600d40e00c2060208048160b01240c2182c1503a01501c40782c504e0b94480400c201211030486880700000c07400000640031900c10a5100e41101504080d01c0c07404104502090a4400341409500540e20001c140401d07540e104250308080340c4101030800c0320380b45070703070014445101c107101d49020030802e4100101026440d80c000c4d0f0042c41020781d920f100740c1c1e44110107840c0030764600c819030b01680c8014406040c98224080c85108551103808585003a00300401c0050100010a840741e990040940c00c80c0020801c04c00c900d450100e000c210140314404404010070744a12910890411422050030840307 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 41679267 1250 41678017 41678027
    0xf0503010f120f060912020c040e030f0703050d020408060403110a031403060f12060105010824150903010c0c05010e010204180c020a0819020709022a010612050102090306010e07 78
    0x5540c0c0307418100c100c1500c0c03030825540f0f850b4801e03000b0b84070502d4055614100000d0908200103e01d1940079036112141d00400c03c41210990401118103800410185c0303c4081080c004010440c03103400c1907030a020840300080c1c00c1782c105800c01d007540d921410503c8280340e00669698028902e4500402800d4066034008180e07040d4907020400ba03070804404990f46580f507000c20005a840904a445021402c1e0280c980c2c8020a204443c082488a4040b5181c0f01e040221650003011200c040340c0351223010014081899802d4001440c0d014050061440c4c80e42c3c00c0c05030102a4555a41c7c040d420f980b281002421103459489101c0542e104010400101c0f0482c510540001426100040c44400800082e410005442c0000b4000100080e415806c002c032001600b09c3e05015034201c85002d0384800c3c028040344902d400001d64014245014510041c055440384030282d03c16002040c01ca43d02c1c0d034444500804084211142d94002c10f4140aa0908114407070051410070412032041c2014400585 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 41680517 1250 41679267 41679269
    0x2b0207121a07120f02030f07020a051203090a200103061509050f0303040305060408031005010c08042c09010e1002030f040b13080307050a110601030201080c0a03060b07030806010f0503010f 83
    0x354010054001440140211003c45482c1d510b92030a000196600020703000943c0308868604900c03205101007160345200180c070008040d400001042480341280913800e441e00000c08000d01d910030780b008080060106105900c65140c861500c400c49a1544005020f40718207800540e07c06110326104800b1652014a0004890040d520501001000800b00b4110303c41d079007015055114400074031080180c0000194401c0c00210f03282c40c442c5444030011561601c5540000d0000c00c414441444103005645124804071000000c8002c0030352012441019900200c55800c1140d645030400c40c52002e0510545a91190110007140355252100c9441012030000e072002e080c042100000558000d518280920507035085044c141c0c8034030740200002c10550040b2460303000100c1c01c50129800c09d0340041e0b0a03041c1c0c0e0b0b05859000c0c43d40e40d9004154596000a1440c1d8109605d1f04d20000310104000003c00b0546c4c007a07640c0355001d24000001408a4220018260800034104010880d01c400414180 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 41681767 1250 41680517 41680553
    0xc0103090602070c030503090909030a0206150f0307060f110102090a0b070309181a0d051005100f1509080304030f0201030504080d150504060803160b0403022b020712 73
    0x45210241c20500c1c000e008040b40100b80800c021000310512000002034091100119920302941d5140c24910742c8900a130070420b0302507030022005c50104410b220440d031490b00301030000c2d4040f011800000e407130f01c1041c1d0f02000118480020a81240d907100001101c03640e80303000291324000c1030901140b400200c0388201104180082034160070503205440090050800701e00001800340c044103400002d142d509150b61518000c49842031a40c1881c000b8280266000f102400c103c107451004030020f010018100c0150203074030f500100e600109960044082c1000341d243e10b012480180f406020072000740c00008403a80b0501080000682900040364810b07420728000c1030715196403902003114056100018001c6041034030181401007850306060480704202c40501c485941d6942c0581c8a1150324211985003025410040202d03c407030080030b400511901c1214100f5020714421400c0e004420300c0e001000c20b440804ea00410b03410001207021300300d0000c003542d4844070b13035036168242e4000c12202 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 41683017 1250 41681767 41681771
    0x7080f100f120c0807080c010f030504020303090405040c051005030a0b010207030c2304022d040536040b040308010b090a0312020c030102130905130b060d060905030d0903020f06090c0103 82
    0x10803c040c50844000404121049642440d100d496043d11643c810711a54005807120590b90780c1d581c032a01506000e03c2e00903001d075160a000c10248800f50000420654040c494030000061a8540401c1404000da1540d281f07071304c2c0e040505082c4151401300e644c1604540c401041800468841580d400480c0c540890417030254800545076070148007512001c0f80d01c0b030720205100382a4404043c0071003d004450811000c090715a645440322400343e40a980d4100b14262085055400d08020940030508009140f21202c158028101e10381c5c07800315030440d50580d4000511042540081c015405490054842800e044505003c44c0b00f0360114070001e006141001c10030700c00e50b8020700ca8042d48100c003070b000b0356907912040507181695101e8400d0041080c90500010308030b580d01035a4400003644403802845075100c41e010424401c3c0756070025190150b41300c244000003035040008166903038401d107011032003d0007401c029017040c003031041c0d402061304640100722001e440800c1108140f1024240 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 41684267 1250 41683017 41683049
    0x901050d0b0d0305030105090a200708041a040503330a0b1801080f010204050303071205040e04121e080a15030501090501020306040b011d010804031707080f100f 71
    0x1414058151070703188a400501c0d41c900007040c9907101c0000d60503102d042d80c0782082500c421364020225051401542c03201900b00751846e034803a07a000002c040c41801030940e00c0c10a521140c084184001107803240004050019080120341001d000307d1038010402d1407140d610b643c4920021800c8000c400c0c402840618240002e04841031a034407520000750007514428640c50060394100340b034207080c021501c0c1c42c410a094102082014000c032425510058040e508010640d510281600295103002050250a10012902906c2d91507171500c43c0307003d80c1d030700c0c1c101c00e07180d807000750124850b02642c5d25205005000800c2d070700c8c3c21181954211a040708002041084a40081c52081c4280c1008001d9401d1140410078464150080e40c000e240441d010026440d00b030b4010342c0c4024400104045032074500b52800f811f58003c10800c0d510600a0800c1c0036800a103044400e1064400c0741c4031004501031005124071140c4885486511448a0b4404c0c1030343ea0a0001c0d4032103852070b070f108401c5540c02c1040303 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 41685517 1250 41684267 41684287
    0x2505030d0f02070506040303090303060f2601060506030a02041802030105061206040209120f010501140a060f02010912030218040e03121b0408060f060612071b02030303190b1005090105 81
    0xb0484140700e410405884841c03d00d440c0060207000c400b801500081c1c01d14a005c20070215900341041120b40c1c0304000030040c18401200c40d603440656070469002d544e1050700080e207845400c0190700c901c280e04001651a4103000f460f484508010442c08002c81c41031006000c20b485113012158658040001c40c00d89075a1840020064032400b180742d600304400d01f1114070403600009600849000c4d401c028800c0ea038907105000c02c010002c0e06242d44c40054030104014941c05074880752071520491001003400701c0d03c0d4a03080040b074048280300340000d6002484050306078110800414210080318107000c04000d400f94550b40f0b004e25a0360740f401e11820808990b00c440103a40d03240344050100c680380c3d145c5603521041038890004440c200c0210712414001001ca00d000b80c03c607443c01c0c03c0c895010201f500d4040c811039940310070072074000441504817000c0000d41c0e0208042c502c10f800b80d4102c0c00408209407551400e80301c004900600551640c142c44a0342c0780c100c0160b41500c0d00c00c0c47d0454403070300e00d01 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 41686767 1250 41685517 41685521
    0x30a02070203010603081b01050c0c12070501060302220e120f130f03050a0c080c03070909081b0f0111120403050a050d060e0412080402090610050705030f2505030d0f 73
    0x343c402846d50000185000740c182001c00c0a43e15021500c0017040076554034014407031319200d43c0481d043c2e90340044441e00c02651502e0003400409000d10300000ba52512640440c1c80c12040180200d1120042ca10301c0c4001c18140c01501c5501c0c2c40710b8054a8503080d4840801100c1c0a4100c00005507a40820140301d10303070148144500908550103540c51042d900d00b07019850300002c0e10203803480c125000c0f0202d580d410014102000201c00380003000400d190544210080654020403940c20004008000c455051079800890040c00500a09400e05d284030b0044c0c211201c03045200d03100c980500203091482121020682d20541504046590703c403c08000c5038180703d482c0343c00380b03840d24100c4049500d058840d010391240f07201e0341022407001030240c4107660150b42224001d43c040b02900004016003000d5a0021003c41c490815504202c415601c660940c0c0221070701040302c01c408113480d92509100059005210041c8a00c07421200460301c031715881c0c2c8620704c0d410721f50549038446516800078036 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 41688017 1250 41686767 41686769
    0x62706130b090c040503012d0f0e010e010b03010c090b0d111b1b09040510110d0903020c030c0a06080c09010917010212060a06020706030e1c02030c0709060b030a020702030106 77
    0x1403003a1041d24241c043d1140d1500701c0d000b2a8001d610300403c00c078142400c01810303507601c48442003d55400c07020644c0d8001500c18103821100d441d0321500001c280100074003500d00c907180070300008103000f00204103060031551400c00c9030703017080a403c00401c0006e070780104a0341c110727114100204a403003c9107503440e151311801c404850380c810031590b21249801c01142c01d884078a496144000340e5055031007000b03c07501c000e440203040c0d0b811811130311080c0c4455501c140702e2055200403440c2032404420328081140c0304040306402607000300140810700e160a01c0700b0010f000d42242c18070441750400300300903e500d10003003545111010000e1512a942e004131a15001071064031061b0140040d5060107602030b402542c41320340e2260454011030000e14100404d10300f03035140c0e41c1c024400c00740b40c0360045003d07040c1c40050503114007455a001e40300003c000c0001c5412199030f002141e80e1440d88514501c0c1c51050341c06004860700d071072024410322001d1011a80c1024007020b01686a04203030000a0040010b = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 41689267 1250 41688017 41688019
    0x1020f1605010608160807050303090a210602030c0a02010609020f030f0c0d0207060204050118050102030d020f0702031006050108070201020310050105030402120d110d020606030a03270303030203062706130b 91
    0x1500304c1d646041700c000140101622040000c2e00d507103e580e501815070360b002e8419583c0d40304598000a01200040440c84400901126a0706100c191252105012a841558407030440b0000098030b00030780707030240a0000148a0040d04624001c0848002c0c005070102070213080c0080c9065000c5a041e810314402c0e40d0310b92445010455461006251090082d4032901c201400b1444002c2070901040c0c0e090312090807180b06030081d40ca040740c6e00a07408000c0d440f130011039a15070320038000c0700050b8504000700a01c1400913078001846508010001d403515500404a40841e80104100010f240d81d8a072654101c400a0078090b4694495200142400e107218441c50400c2c46040c000d0030805501595000254990005907400c42c54090b10481c1c5030103045405c5900340d4450501ea0000a1044130710400080c0200c0340d2807100c440070106283c0b01d6600c5da0003035000980110601c0800d1130700b1101c070610310415400700a5015034081c21845a0000140072501c40d00c0d560410b40801d2001e5004540c2412b8 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 41690517 1250 41689267 41689273
    0x1b0609060705011e0605010503090a081308010f060f0e040c0302130b030105070c030e010f0905060708070b0403090906090207050607140c010e071502010608060a020708040306180605070201020f1605010608 90
    0x8984001c0c4d06104446281600036040c90300000d49540100216030242d22050058805283d00e43c46e10106540501d4810b17200c1340c80c8501c0001c0002c020301c1043c081109404010071340901d8880c2003641900b40b50030085155103848244070000e081b840c0e0080450b641039618403440a4808150401070a1046510b5055401c0030100309105a2103640301a5843c0f080e12550152005003004550010050444001107607500710103104d40d15041d0050035286124915040c545000f0b80da41d100b03030483c00e40d03048001c1891004184804081c034080c24020b4038211f030f01181881c0044e1191541e03940054462014803c410a189041c0140d0700101d64027000301340300038002c1c283c204551596402d014400c0d107420000f040d006002a81c410701401c01194055401080c503911032498450003584213500031a00c00108020000004480e401100e0744640085980c4c461101c503401c001003507440061440f011648100003901d0316a06010603030b100c1e43ca08110044c401c981c80c1c0b074002e0051440790000c0e60144 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 41691767 1250 41690517 41690531
    0x3030409060e0402030d18050d08190f09050f090105010807030b040e0a0201110d0c03050a11010f0b0f120d0509040207080f0702100201090201050301030b091006060e0a05031b060906070501 83
    0xc603007051118083e610a0f81202e04054501c1e1084800304034030300842c145915070b00c0f010001d43c540008400c90480c002c4100710700e841e1824190556207000342c200c2c607022038104481405c0c6243c205c40d074030b001440b0a03514165600000f1000480c0503005000e8141400310042c045180345110303612009999001a00030040d0310341c505000f540e9050b24040c01ca001902e42c088248400001042c46044007505480741494400303240d80941e000d40210300d10a04200d14a6024407650509005051002428840000d855103404040c4490007411161150007070f0302809c4000038003a80040c104a440e107003460060344845101000034064820100003405042000ca0310707254248031076005080151080b10004076540c1c4000c0107900380c8490481c0a4045401440100003080e01482d005134083c4094040d189a030720460490021614140c001c100040d448001640d102d00700800a0005081d0480007400203031103000d1042000b24045050300e00851012030f0320309054031070b20240c40400350f004009020300 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 41693017 1250 41691767 41691779
    0xd080c0c150d060f03020906240d050f1608071101110309030406031508030712050705011d0609070515071b06030e010b010c0f030f09050307170c0103020301060c0605060303040906 79
    0x980107007070b07184290b51030204002041a011101841240e41c0030717155803195900e2204202c96200c4d0b8100035900000e0644910100d00140c00c02400c080c20444c00010305424406229512854020401c5400c44011480840304641119140381d00418a180c4200c1c12012070f504039001d03050740390f581400e0f01008000d012801002002900585043c1d603010040c031940c03041d154441d000c0314403c204803a0810840705012404c40325500c0b810000900f499441c03d5002d03900d0b0303400c40350500324070a0f00200303c45002030f20340805e0103166040010000107010722814000055010102040e500d00c16140000e060b501f0402e18803450320085995020264090384d0351316000e0701030000c070988403645501e05001c4110660003040c540c650f0f2a04240b0180140c4000e5606446654444c6141418040c80100001e02917508004901c0906010310341d03151466001e00d01c50340b03800c11113003442d81030600500042c426942d102080c44000c641180e0007103100e40300c683c0400e086100d542c00050a2a042410120311 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 41694267 1250 41693017 41693059
    0xc0513080304140a0303080a09111002010905010f05060f0105090d080415090602030a0504170a2003070909080906031f030303020a1101140a0c0302040b0304210804020d080c0c 77
    0x4458120f03c01c8101c81c0c8402040141000c0540801800304d80c068002c5040008240c0c4080440f600c41d041c001c040d03561007400604410707094000000180c0d103800c3c501781005800c4c0200d2710701c0352110006215604001c0d0000e88100307000010700e8100440030401c2d6080d90f0710b01c00620a51908500015643e41d2264030f03643c10340d000070b02d40c000810400440020058400011034402d8685c03a80c880d030419080c14060340d559980c41c030501c1c01c01c3c4560010440400e200c00034050742c8000c1316200c072440300b410302c00740350415501f540840e01c420319080e4400c02154680c2c0840303441d050101c6070190b40c1e50b41d05541c0c41403845a840da0007201082c584010040541540c000c022004060b00ca101a0000c50050982684c4545070026841e60070706000c260304458641140342d14544074107026044c15151a603042c0c00350002c42d802d50f1b412103018040c411400222500b0b02c82c214082c64020b60320714080e000320300c514105040c000c007403000014000c1e403070721418008254a04030081500a02000c44114044 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 41695517 1250 41694267 41694269
    0x30a090308100602030d0b01020309040e0607090e1b0703020a1a24010c080a090b070b0604140108030f16050d03050106080901060f140301140c0a020c0607020102100c0513080304 78
    0x8a003020020035070782800503000c14121500f43d802185891240051031024040305c6200c14103520043c88070050942d01c1e8000d001c1c036440200c009240d1460080300c02060030301d641c0e00071495803929038144410b0000b01d9002c0004030050f4400155074100f03925040b03190201076000500040e4061445c64100d00c0c0098180b4042e403800d84500700c1415170880c6c2b1444102c0644080c9003c120700c1d04c020000106400081c026201860070206401561904e400c1560780c4900012600c5410580400c500703490144140104044080038810f5a5810100b030180da0f48242d082d003c1c82c200c4046000004403400e044403a086c01d43c44011340304614111800030b0082c0c502801010042024907000551403e0144100801c445000340c0182c912498804420006400317001d216405540b0f030101c0700040c0c000b01e04241e00510740f2070881a91200000002414061814156481039070100718910140c0e0f40051139040b00306581c080010300050742c0a01303940303a12603800c030304d540114541c80004420701c01102401c = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 41696767 1250 41695517 41695523
    0x307060c11060301060e0d080408030c01020702151204150902060a0c0b0601030c020a0201080c04090908040306050609100311040e01050711070e2509030804030f032003090d060f02030a09 82
    0x81d40c080499003048000c0c002406100f0002d860207980104610b03000c0c4010307012501030464146059103c250b02800d41e44508201489a03400180080031424909007554801c91500c0015062140900c0920500c14020300041c02c00242499407070b80020740741e03004046150780140400da0320507101ca80a05160361401058441d00d032a600043c1003940203009030000101140d01404203440e0503801901c5007240a007580c0b80040d02400301242c00b030b40034450103043d1401080c0e0344d0384861847c0b40071420b031000241501d00580740c0100f800018800419808203503a808402c080f01104004040f800400c1250b1130982a503091100b032010064002c0d084420f20a00c032002ea4006544a50f1842d0907543c05891080e0040c1c0000720784690340150714040525544186001110303a0381d02d4507007000b150029042581c03d8030400d11803504140d00140302c0218245070000c04010740504100481d2240180348100f405044829005030030086183e10107242c01d41c8000c021503c0b420720900100050808080403 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 41698017 1250 41696767 41696783
    0x90105070812010f052103030a15030c0b040e070f0203030402060a022a0a050406080615030f0a05150a05060a0311040605040504050607110f030301050409020a030203060426070305091c020307060c 86
    0xd241c11416030302d002c0846c0001980f541d2140c2600100408a0004083c2c01c90218100440007680481d48100284070346a011038440d03003071a08850342c070f40010304804140221760035292420b50700030043da40d0142d0101e96050312005441c009a0130401250210100e5000201d00710000d20301c070101e1801240c0c1c007628408850364580c8103110448600d4002c0300040c1d40002c00091481001e41e600300c10022026060319841c134008080d9034603051512904881a030801c0309140d46030210702c29801d40c8081d21400038800d03401c150f0301142e4140c0e01c0c1e000c0600a0130181c4000500c076200c0360010b00090401038810170040c6132a0510f25141c003410f0f00d0000c00910100920021b6110028140100e00c0c41d4901031483e59181c001000010103052004a802606a01d800400f45e50140030b86c070700c100c1c0075640c02242e42000050174980c0e00c07403041c2e01e100d080c4070900030640426808400d0b600880b0303040c4c480a0740802900c4040c0050780560304001d502d0301c10707000c01203107450380101c22400c81c0d8403034981 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 41699267 1250 41698017 41698039
    0x3030a1a030102090603060609040603080f0702010e0d02100807050c071202030601050102030a200a06090305090f031f050c070f150b040621030c05071202010e030f03090105070812010f05 82
    0x705400d07880342d034035150f91045003403000c1080b42c41c0410040c06560700c001e0001804030394a03900d80d071240d0011224550684004070b464010340d60020b0141c00e0b0164216049500d0341910703400034401104030701405c07080003440c0001441781e5000c2e40403038645045000403a00e20a40d2010131828140414104034042d000f1383d000020b00f94000025100751041548644008100ca005400c8200c0030103441c2d502039105505409011444520035184194003a6075640d54030000041030050000204030000d00940c40110003420344901101240001508498042000c0e10703004600c96007406450000360405201e2054002040741c40c40e5070000810180e041131114207000b00812080740c18604c80ca010b82000c201252403220f00c0c61614640070752003400c04884101a940310345250050640088020b445000c0e0003601303541c3c224040e054850340450040c420308840c0d0031000e4881c01140b5505051043c045049030130020a98265000102004607102030341d0303592500900c0458981c80350a020300c0050b00 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 41700517 1250 41699267 41699269
    0x1006020708060105030c010f03060f180c1d060a020c060301080105040b070201020301030c150201150807140603040c051012050a051803070210080a1509090b060306010806010315020c03030a1a 84
    0x31110f0494000a003d084115583c80055941c0c00e101003502081540d1000d0108800e8072121040010b49075031124a121000c07034109010880c0c88030400e103006d1241200c6044c07c0c503001740704031590000d0140c481c680c41b2884280140c3c0341a40c00204103500c0040400007050011056005612890140d08005e00a44440100307034200d1200f800041e02c2503c0c4d648060142c09804e41a8010704803107403000041c5050ad1100c0841d480e1b9442d08004040c2d0894201000303d000b480c0b04039241c04004840c0c051840c10a50f44001c000416446070078040c007500c4803040d201c80d00480c603035041c00e18041414442440d142110800034101141d40ca40c101007811042c40d0040c40c00001c0c2d802c40380d030280141514101e0100700351003108005100c803902a41307507041d80700109090b0710004010101c043d40032611011034609040b03003100081410f806071384100010031030780400007107450440c2d07000001d03030301c1c00c1000007002c90180c0b0031194403220511000092190210351940091791840c1a4007200c0401c15800f0 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 41701767 1250 41700517 41700523
    0x306090809090f040b060402030c0f0d0b040b04060e0a0e010e0a030e0102060f0f070e030c060f03190e030f07061b1e0302040602031b010b03190605010b030103030503010e04060902091006020708 85
    0x148001d4505c5010308002202400d01b40d00564102c0003200a075820b0490681c0c400381590310030280380c240f841c0c407045071405604060140a0362441e084400703000042c180100020301d074030010914144561030300e0000241c030b07100394803404842c4044000d07550720411505003d01000010800c0030300510850313001980e840c8440010600454030164024250385461204a603001c48079441581d15014900f4030450341c1e40c5039401008004070342080e0a0b202d2801e1004400c0940040c2c103030142443c24070000c803400c01d00c040300f126540013108030981e445d144582401e600030b08618410fa40208040800c900415401201000b00d04800310943c14505c508000210142e004134840c010240e401400030000c1d03c1b01d60302007003003039042071302c0001002c84100f00001d15100a1200c15039a242440d02880107000081c0100d0f0f01501c4125000d0f8074651569400a08074401407051011840945002c01c3c00c00509800281d620780e0000e1031b40c0b9003810300b4a014017802d5103038440c1e41e001d13104d22080026151404 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 41703017 1250 41701767 41701771
    0x110103050610080406110c1f02030402030c0603070306030f0606080f280822060207060f090909020f090c091813080913020d0203070306080303091b0a0306090809090f 73
    0xe0900d075400705650784143c48205000e002103130031584500644c0710181050010380130102185c4e0040055621820a90b200d0a018101d1440214010400c020141e20b001841201c03021081d140183e071f031355074580128020401c0703410007440c0d26100341e42d440c144503c5420603000e0f15240341c10744410b5840707005040e5031940e08080111035000f2549080080400f40c040c1000c1c014090100d01e8070f005605a8045841c00c00c0f00d29404080f1803411040c80500d03410172141c0050200340c01c1c114000061640060480d150520900700810b4441c05d841045440b1074409540c0600094030120303e6023841d1130094015004050810301540c0d00d403a0034070b07036460710b542902d00071480c000e4154040781c1180c03513920f4941c1c04010a107801c1102e104008100c004c10784000d0080100c0042c0c01030b101e081018000781a5140d5a03c851280d51090051000321400420348000508801d03400c2c3d481d041c0c0520208007000e10303c2d800034200c02c0c40c0181c080103100c003e170010301d4040c0b412036540c0269a40c041c418200d103d41 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 41704267 1250 41703017 41703019
    0xa020f040b04060e0a02030109140405070b0a0504033905150309030c03030108010c0807080903030a0b03010b0a0e040b0609010b12090712030e030f0106080318040b1504031101030506 80
    0x608051060a080a80c800c0751181c10180010030042c3d2144d1480036189002d480801e0300c1030f400001040005224802d5411814820300040105d0520303458150b80d440ea240250141d5100000700000400d00880442e402180c1c06001d00c0306410503040034401c0b03410003400d5040c0070105044141481502c0140b440c0c01c1d00c000500107520034180070072022890700000c11b07101040c1700c100205000b00004201a41c003e00040001080094105c800201001d10141040040c0315000060005421010082d81d80c450062180046c9540002001a0241041803190741d00921480703808034030040008442c1c1d00c5280a81d5440d07116449060600c140381d00244181890f83c0024448820701c11319035130702c0940100b404405c42d03113856200d000518141158901c11404a1410181000300381014041d140005071810020401a450001c5c400d45078400d5080064884104024176803d5a40e294040a0720a130042c00309800c61488003450703030341503010b40429644000c44000f1110b566100703001b164400c001c = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 41705517 1250 41704267 41704279
    0x50601090c051b0307021f030c050313020108091507030e1e070515041e080c040614010e010c080310030c0b041a0706020c0a05030901090f050307050909160803070c080a02 75
    0x1d900381192820f00030100d0041c59404100483c1015070b030340c1c6214402c6904000e05804c803031417500740050100c901041000c0f0a0000500812040021800321002920340a0034074042640e23a1200707131400c10031317600c01c2c2c041c100c264402400f48281e8980d00c80c02c1e0142489003140c81101040e0504040707112500c01d1204554444c40040c449410014080d50564000300c120358102a1110000210081d40e04040c004080f080c2c81d040101020070440011080380c03d840800c0380d035040c41e51010404003008000e41c1405420311100590ba44200c000321602ca41240200d6140c0c1003941e555000304215200540b50854450408909066590211822196030b00c50041c50300c1e074074006032685070700440419a0080e90901032600401000d00074444610702c10707030286035102c215000242c0701e60b500340c110444a50070114144955140003400b541981c400303c805402c942e0300c506c0746510700360039500040b0000751124800180c03284004040c0920a11488402803c0c0703480f40c03180d950300d0f00000303001782d4001 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 41706767 1250 41705517 41705527
    0x20111040b0d021b0102070614151305090a0c030c031202030c03040603180b0a060509150a12060e0a0302030a02010c0f0206060d020609030a0803040c0b0906030403050a030915020304050601090c05 86
    0x1202c5640102048111841c200040c810024840ca007240c101e40000c1c5c03100c503290303000f8486184c4101000743c4e001910030007120640e001d250105078105000a0f0b00a1038555a0000c580905810400303c0c15490f0b103d6a07041d811516403500c04101d401912040b1850240c0842d19200d0500100588402001071002141041c1c03401d08200c0242c46d009599418030f2000000c40c0011850388080513200300402200492034604e841c0502c140c0a800601240d1051441300f0b222800795103001228080f510b04900800100c070403820808003d00014800f00c1d41c030b21506911808158001c030144c40d100c20340d90004c002080170110183e5180e0001251400141c20840000321145404500c0400040c005400a4100171303860000c81c2c90100d00d001b09075003e0401208103c104400e0220342c078003411115440302d00b0115440082086400b01900c01414040d0210750079103d00e2003980540340180c0c00100c4c80d0742d008000004c07107000703510644041d600e60103038100125901e08540500202c40c140f542d50b0b180f80c4 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 41708017 1250 41706767 41706787
    0xe0411120c0304030503043011060703110706050604020d0905060103050d1e11011410080f0c010804150f0627060602060115030608060c0c06010f060903020904061b02030406020111040b 81
    0x1102e840403a4411f000002080d1001c400d280107000d280c20234292180007048200e500ca55240c00e0000b40b08004060030b0480050b011041c2c40c050781c1c6010360025020485882c1c13580003030043e004008210104c43c0c036100b4a04180100022414120b90084040e030b43c01044040c811075030300c04000c0c03610340c81340019042e440f9650300c21480c80c01003800107000043c00c0780390a407120108407010744402c40240d007c0d43c002c0c80000e00c18031520a000d803072900101088400240042c00b42d81e001000035003c1d010340701700707020381e01078580140e21101044101001503546440f0011004c03c030680c5500440028a071180316840694481d5105540705034004000c1341c4c0c0381080541c02e89001510450805031115000940c04500b0840d2500444080c0c4019443d45403103004036260031030503403100d614680740c03e404200158001c451881640c1d01590b086500b6911811f000b00a4041c01540200c0040c5241c0c0b6001c05c81c3d070200150080d0b84050740203110a4070600810207640c0030b18020a44598000c11402c010 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 41709267 1250 41708017 41708033
    0xf06061b030c0a030306050a0e0103051002160b090a17070201170a0f0603121e0507021003020f0d09020310090b0a0203100302030304080a0606090507020a060b010e0411120c030403050304 82
    0x81030480904880c5012800326982d0b0400185a500300e0209445003070600252402c016071310042d0124440b150346641c03441c3c444c250346039040710140185581c00904d501c08404004050f90b803298001c0300228260418200403a5034840409013a2a003040e0000043c00d4540440220380109405958541101864a000b14000040a4141c1481395034174080e40a441c0c66500a010046000d10303c11403d2908041010b0040c101c540c10f0440307110030210a0449540e003010a88402ca60155501185070095440960082c840e4070040030100001203664070b40556280c101121440c402d9060314210700300302084405035801100000d201d0b0100714001075480c002540515803054a400350101480e030741c0d40100e801d550040d08410074039003042d02c030300c03007806664001e850041100c41010400c3c0d10b40100300a40702c02d1000801031101d5140c0c2c0401149170301c90b507101074650000070000c200942c000402280940d2202014003104031504000402001066060f00d210b103415480301450340c1d990750740f0110 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 41710517 1250 41709267 41709307
    0x106051204030f211a0307050306010b0702180c1806130306200313050d0806010e09041506060e030f030405010c0f030306080a08070b060d05070603020f160b0f0f0606 73
    0x20412142c540c030a00e040316284c4010381034100740400003401494140400741000d50400144c1d0003940031910821980c0c800241c0079044889521245841d80058400500c0515a80b900300312009650001d000d0800040b100034441c2c118031070a10391000d134940007071101c103000e801d1200141e0041a070042000c241e0360340110700100013480362014109005003070303e00140c0080d6060004c07484034541082c100441000b00c6150f122650a0108961900c58002002e008640c01400d0080c2c00e1180824104140c1010741c4115600900c403e106032a10340c000240982940401a84240700d0703202c008454600220486081c1c80060351140c4e40d49000303032030b50400c1e003007804012010035903111000a80e2000521514071480d100d00400c6a84030350504040510000240c005440740400c3d0031a80300050b00044c03004203c424609003d81c482c0ca59070411034690141007003407503200e402002044108010b14002c1c0c5d11a80c218410034105440304103c41200b05030850741ca6030407a00070854424500c560445800d = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 41711767 1250 41710517 41710547
    0x40510050408030304030201060e15030601060c02040e0708160b16022e05030103120206250201090206030f0f0c07080906070204020d021206090a0b0a1205070b0c0d0305010605120403 80
    0x9481d10341d40b4200689154000c40301030300142d5444100344400c0c0a00b01000790013421000550b400c01c0a11400240c441030103208110a01501e100c0300021500d03540c02c104800956001502c0d07403181ea070000561511118100395100c0401c90102081c00015101500d03c00f01080380c5100d001d0f080e0f582071082c45409800d122031808980650040103021881c0440100d083e00d5590341e8032540b4620380003161260680700c400554004100300112403515070515150307040003442601d90082501c0c02a4010011404065009100001040b000c40d10800c801d034001c1800c0410003007070341e550600010081c0103aa030000e02c408810000d2480390b180400181c1010f500080006140032266804d150480e8490449100d4a503131940800a0710720300800d5150740404d03042c07424001035001400003401d4920500801c03d0061140c0a01c505010003000100c02602d5882400356a80301201022a036031000903a01c2030009040a001182661061056032080010f00701d0305001500e4565054070f014181c62402 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 41713017 1250 41711767 41711777
    0x1e0306030a0c120302070509040b040f11040c17011a031602031c09020f010203040f05060705071502030304050118150b010c06022b141b0904060e0f1b040510 69
    0x6800803500d00c402d920300400c5100f0001000884510300a0301300f036459440b440c4500e502c403003040081401900015881603100385100d040c07004900d0801d04120f8a8840700740c005141805440c0b0164002d00e4081e06101ca208291041c3da903105071900c1424554215489021014008108042c4034034103d940d02030000d005480c02d180000ea60042000401150b400c40140c580d0901e00540c20801c0040d5611102840514a000d0408503101ca8682e03039481a6070060345c001031514244001406a00041d1004009607078050214010081d9079410aa400784d405500e001030401e85440081450170b00140e02032065045214000c10140080c80d05000540c1031100b042003c0c00001c002d48020a0307900d422075050610810118000000303003007000e0055183c58078040c400848400100c1c4001d610403000c403401c64518425001c3c801310b500581340c086400c03c0c10800c010502c2c1c00405031851140c4515a02c050007951040080e41d10701d41380c0900c5c801c0100082006000904120492010300403031801c2c6 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 41714267 1250 41713017 41713033
    0x309060e07142128120503041a0601020318010306080d050309070905160c060915020406110106050303120702120309010b121f0506010c0c030b07020d02030a12020307120f060608060102031e030603 86
    0x1e6030300f060641020030300020000070030001003210310440c030300d00f80c1101b01688292b8504000040c1d034a10454828508465500d00c050002d688a03401c801702600c5002d0686104181101000c0c08a402c1a254004c85000308900492220943c2c031a6520a40c50881100400c402c1c0310001d80d80398000580a50300319072200822000316407614480040110803030001070f42c552400c0c2303006192210540e50740131aa410309030300f0801c84e5400010741d4100c0c401102c0b422200d840e6114181c3c60442031083ca000d4068020003040301ca41d0065001c81030381c02c400d4035044a000030b0310540c503480d100039400702c6a0119151f01401c00b00021580b03c280d001d907040c10161015841502c4144412402e40c0c8103d0300070001c40c0800c80110350504c840344a01900f030004504012106101510745c084442c0d8032682c00b60302100007a8204d209951500d104007051408110540511701c40c1c0014290901440c1e008c220f608020030803d51001040320b41000081c881548150f090480904042e8400380c2020b42c50b02c00c0e801 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 41715517 1250 41714267 41714273
    0x20402090d08070308090c1207030209070207080f0c010f0504050d0f290a0b01050306031005060103060906060206091515120f010212010e0601050304120309060e07142128 75
    0xb0081c18514040d4498040d1490401013081ca819000d501842c091504600c40c02c0c4960700c0068000140c1e41c1c11100c02c0360741d603180c040803882c0c1000c5500800c03c07031180302e94400300300c0804140b1555105080c2d03180c850404400303201361498403803441482d40285410302d00c070f0045200c11039094400c51041c00c020405841200b024258040045102903aa04038441400307900012403003207060a14085c00c2481c158075207140000d4840c130b90070382080309075602c8000045803a8400e41c010000340c01950000c010586c0c0380c0300002d564050403941802e1700c0c401d9800340040e210252040c284501c044101424200c12440305100384101e0744004102a407041070035a0203040020f0011302070f80403221500082e550300d0034800130100c00000d0b05050601408100340008215480700c9848000001e040c0490500c0ca01d240000042100f200e0046860081c14804242124244410020740700111211040381c030402060b4940d02240d070408036142e40c00040e868000101c82c500069407851010992401025941c0b = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 41716767 1250 41715517 41715533
    0xe06011409010e040302060f0901090b16022104050d0303060b041706011a07030804050a0c0b0c010c031103011a0403081303060c020309010c08030c0408010e0a1e0f020402090d 77
    0xa04980c800c0140c4021222190030519001401001c0d4110103101e00d080944001c1d4642d1000341c08002240c10304800944945000d40001006952111040d1994941119105044404400208014003503000c8070404082841d4064004d1850001424a003900e000c1c100b144184c3d404c4821014076803a03503000550f03032100c4400b800081045992108401e200a5080c138180007058020410092600002030102041c00c0c094550441d172506000c0b086071035a0501d240f074000b07440001081045410300101d0b4800c5000702034003a002e01a0003d1009840d140c41c00d6055504003d42d82d50400b205100402c800b000c5400c00101044d00b903251030b4600b50300c98540c8106a8820001030404004403d0f04204011a510810b480c80b000c0340b002c0c50508101d080001e048040c80880600019808408900509484d0088400030001e0000800650140940041d194000b407403058407204d0520080b5010310000c1011040b0656104550586507403050b420000250442d03580c0c00e401900c50505140080e840f1 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 41718017 1250 41716767 41716769
    0x50a030e0604110f03030304030509040207061d070602061005031b0420030906010504110306010e01120c0c0c09020f0d0f060e0403020105060a05040b0a060c050a021c0501060806150d03030e0601 85
    0x81c460390f01203082c10824040383c112182c804a02a9004004010102e9030040581c2c4039204201c4026a41707842d1418450301810f4800c0701e0a2000d1a00d200515610000003070050071155143c09a0b880d540d17400a07040e989861511640c0c3e0103410804901c500078001c030000405a480c0104000f882c0d035045500d1241e0f51102c4104c01c90450710001c20703c42c0860042144500504080381c050040089040701c0c5855404043c2030981801005110259141c0c0074001700304140d5500b4008002e00d08403400f005100f80f00b107420640700071a5616000c10360545d00d0003240c90ce000320036969031401c440da24050005003104044500f2040d6605030100b07448100e071000300e018502039400410a07060030030030405000d28a6100038810f80c0740000740c03c4a41c451501113001c031801810310300c28030040d03030410030300b03006150300000d42c420702403280c00c002d440b00c40300c0010380075000304000c100c0152503842940e51840140e680e181100b0a0b03000e4601c0b54908003d0640301203210349004580c40d020416050302e48102 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 41719267 1250 41718017 41718023
    0x3030504030507050306010f0303050304020420090f040207030c02010c031e050d1503050c0d110301020d051f0e0c0d0e010510090f060e010902070f120509090105030d0f050a030e0604 80
    0x40000c08005102040000358042c260031406001d165241041c0e00c00200e400d840000c050000220000c2e09540d40d0f44d000800a1002207040003000000f0315402066500484010f449110b000410310001e052a10940c2c0b54254145c0740d007120310301c0c582c0040d10a030174542e20032020492044100e071a496202c4451a0701a280c5071156901e03480354802440540310f6070400b5481c140701069003000810740003d01e080243c6000e1783c0c400a421206d00307080200c90481311740142c2560002480c0666034606030711032446800d18105110020b2045401da850550f21480384007512900180031541d40a0a44000d1142003100d9900080301134550b81003500350b6038121856104000c0f100740800c0003091034090b000400c83c00c914104030301400c00da20748100711810b0003060041d590102e00e000811008854003145103402840d80c071030408901074020210380c0300010f51400340010200009081c1030000b007644100d00b01d0340b64224140c0e002031046070250019401c4101b01502c604c11003610241c1484041d0260340 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 41720517 1250 41719267 41719277
    0x1208030609011e15020309030f030301080c0108130305250506010501080a3e0f030103060b0d030c03030b060d15170706140c0307020405011d1503120903070b03010303 73
    0x1034924100411210305a1010800c007140c00803200003c0c00540442060380d001c1214071940d001050070407840c50240d2031070103070103104076403a1182400002010754102d821030411610020004001121804020b5501c80720032001d800f038480000c0d018202070241c5540307402d4040c060240c20300b110784501c07004407810394441c0c01c18801801340d035034441d060644c08076038001d051020140c1110f510545081e1b100c40315800300c01003004125110a110024801200e0703050089131258180d40b014105039200f884201c2d4036602e03101082e0905d0811805011100d03400d0344818030800910340341907000c0d000e440020356100008100062403080b06110b0b41610540030a402840c80c1d051400303007141c0030b11603807c03e51143d010810030012994881c00c066550034150715001d03292030710b40180614500034040000d5010703051400204104222a203e892944480e0f0140302440c0ca4030b0314234072851b200003010540c240d00099030b41009024060000d000001d00901164080d03943c59001401c20f070400e8008030700040d = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 41721767 1250 41720517 41720521
    0xc070b010e040b09010209060703030b0d02090103080d05090d120b040b031002070314031519081219110601090209030708011802120c100c060b0d23030304020904021504120803 77
    0x400c20803c1640040100c00071840c143d002c3c400500c0d80d0107042402070815890740e014048546840300c1c41e07443c00340d002d0490503095031240781211203504040e4032040032525210001d120030b2000240326800b80d156407202d090007110755407114040c0c90b1004400703070040d40314681100e8070b031000c00001c50758044c424001a1681d9082c40d000748490080041076a03551024400e0040e0350b0b90103944d50b101340070100c03405828092201c410283d40c5456a1150707440b80140064510100388500c01445150b00c55030502e01904035140c001d648030700201c01110314030f82c00a0010302c801b8809134001c03c10180d000701180e4001d561428498291840401c4200800c0b0750340c0303a804210300301091030b041440304480190003d000e550f40071482401445442a04200009203440188030b419444094004805030440c0329a81050400b4210030011282000314440680c10340c500d008408030589006039030061041100c2c0c0ca0b60b408001e13038002d40c03a14105464004020005040109540d420541441042840d48134 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 41723017 1250 41721767 41721773
    0x201020301061d06040b03130b010f06080702010c02070e0703020403020312090f06120712020702041506120b031c1b0609061b020a020d0615061809110d050c070b010e04 74
    0x20048283c42e903592501a140714a28030b81c0d44905990a541141c40140e48903913a107044030100c0d1030508e8010740300d03102c180c0c008141c00024811007401d6822548804c6001c5d11002c0e02242211410308501c00142c200d03110503c9500004502c20350450a98500982480c0d01c0ba00002d0602d181d1030000f5000c4540012901d0307030303410814650038030044200c40150078800c0d000d9640d014040024440c2c01040030002c5c08100c6800c4a078141c3d9000b03900075004201460484030000403070036283c050080481e24402d450030500701a8014051a620b026015108080c3ca240b00307141d0012407170aa40c81408409101c0b00c1d000600290b20740c056034003802c1d0120704100e590030840200c1e50071102c41e28524405100c43d0f99550b40000304e200e800707541a1400402c4010a040c40e0000740904920551005544030b000070b0f405a00005102c21840c489110005503551448288100c03880a100081601024080c1003040d100b19440f0300d47c41240c0b0520b01c0d25116240e6181443c55009801000712295050103010038 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 41724267 1250 41723017 41723027
    0xd0608011a01050d05040804030c03030c031103130302010503060411030c031f150e030c0405090c0102010e150106050a020f030a120b0102060421120f0507020f060106050a2d020102030106 82
    0x10603020050308084030704400000306103102e1007a070282c10310b803900c0c081420413005c0002c0b01d0045810528103003d0304d0312482c00810ba140213960540004082c0300805d0a22080882150b40c480c42d17820440d0f40240c41c0d5401500c503908010956507019682d1000082c0c0032000390007d601c5030750085d070000e56a10b41070070301d00035000d281050b8485010800c48140034a00941c040c0114440c20790603e6410130048400091810b1031074034000e81c0150502040c002110f00001c2c040310b03509402d8009008901551000c55030b103214040c4d01124a0072450010040c80307000340003d1500c414544180e8a02d001001e04840c0740d40d0243c0c80c680c0020b4403000d00400c0043e03080c860007844800903c0901142e0400b80c94900140f82a0034218840c503c98003005065070340200c6006803208900d80b41844548032a04030b03540100001c841c0300001d80165400000420b40208113030307040e6225900c5960800c00d03210b41c00c030b03158207450804c42c0003010f55600b2034505401d00d065480b20b4030100d90000d40c0c2d0358103250300100 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 41725517 1250 41724267 41724281
    0x17090a02030d0504080c010c0813031b08010207021305040212120304020901170a0602090a0503070f03121e08041103060405010f2004090213030b010902070309061106070f050f0d060801 81
    0x4104030f000c1c40306011800c4c010404045101e004d10f031544011040e8144029a4031401054080745e8604100001c10170010503d0240151110904d12400d2a80c9403089801e07841062030095114544036504416003405e0b174040d50700316001809110485411302522440c0c8040c9180c40c12003020007001b0002140391100c2075501404800ca8203c21b5044811505036403900000f8009180640208103000700c0e0710f441440c1c074000c2c0030060440c2d42c080d0340c0c2d00e0640b00324405400309582c0c249441c04111b880c0350040654441e00f165840c40b01c071480700181012164000c0103002281c21820307078102c1c1c0300140c5d0b040140b00e000d50b0160000164500c00313021500708a44102c410500e408903201402d981c21884c4030291002c841e11510090ba44487c8a4010030059800f03030402800d201e41080081024181c03070703001e03181c00e46c480e0f2200d5100545681003074130320f0342c0581001406035004c10001100726100d45c80250501d011400d0203414209003120190058000039101040309a80e0300040200a5007401801 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 41726623 1106 41725517 41725543
    0x604110424090605010c0b19020d02030f07080601030e0703060203100e040c0807050a0308030604020705150a0c03051302060a0f090807120317061309020117090a0203 73
    0xc1c0400400e03019155050303140903400f1440b940642c0b42c5070300c40d0343c014541c82050b42d6022400e0b1040444841d05c034041c95000d11084110406900242d0301580742c0580d0380583e0724200d4801040b0b034100a011604040c2001110403010201152a109481d0400400340c6d81c0c1e42d403150094021031055104400011180c0100818020410405015140c2e5081698011540c820420900c01124000a0519801000480c0807441d15a0040410a2181c001d440e00f40d146880ca542c41c7d400c00b2540310300501d0b29030100340c43c55a45480795035401556801103141e044840d07000f242640c0560038000c400d0000c2d04d03911b801c40034055403400b401041d58a0813600b420f6101c40b0311403a80c861103003085020404120706080403045202c0c082c1c0c403984029050034042a440303c11000585002d41090b4140300301c0c001c03041c1080d0341480065109400084c0100440743e02441032525064081d6111 = true := by decide +kernel

theorem cover : BRFrame.Cov 41546767 41726623 := by
  have h0 := BRFrame.cov_init 41546767
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41546767 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41546767 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41546767 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41546767 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41546767 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41546767 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41546767 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41546767 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41546767 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41546767 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41546767 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41546767 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41546767 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41546767 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41546767 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41546767 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41546767 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41546767 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41546767 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41546767 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41546767 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41546767 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41546767 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41546767 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41546767 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41546767 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41546767 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41546767 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41546767 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41546767 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41546767 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41546767 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41546767 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41546767 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41546767 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41546767 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41546767 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41546767 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41546767 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41546767 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41546767 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41546767 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41546767 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41546767 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41546767 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41546767 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41546767 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41546767 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41546767 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41546767 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41546767 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41546767 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41546767 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41546767 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41546767 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41546767 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41546767 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41546767 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41546767 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41546767 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41546767 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41546767 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41546767 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41546767 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41546767 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41546767 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41546767 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41546767 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41546767 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41546767 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41546767 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41546767 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41546767 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41546767 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41546767 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41546767 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41546767 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41546767 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41546767 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41546767 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41546767 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41546767 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41546767 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41546767 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41546767 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41546767 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41546767 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41546767 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41546767 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41546767 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41546767 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41546767 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41546767 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41546767 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41546767 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41546767 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41546767 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41546767 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41546767 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41546767 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41546767 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41546767 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41546767 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41546767 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41546767 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41546767 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41546767 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41546767 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41546767 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41546767 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41546767 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41546767 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41546767 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41546767 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41546767 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41546767 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41546767 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41546767 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41546767 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41546767 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41546767 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41546767 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41546767 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41546767 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41546767 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41546767 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41546767 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41546767 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41546767 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41546767 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41546767 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41546767 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41546767 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41546767 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41546767 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41546767 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41546767 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41546767 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41546767 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41546767 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41546767 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41546767 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41546767 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41546767 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 41546767 ≤ n) (h2 : n < 41726623) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
