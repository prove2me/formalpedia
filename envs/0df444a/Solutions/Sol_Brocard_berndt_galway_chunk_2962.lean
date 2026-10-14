-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2962
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T08:15:35.336621+00:00
-- url     : https://prove2.me/submissions/ae84c9d4-8609-41df-87f0-050d0772c327

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 532553956 ≤ n < 532733812 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 532555206 1250 532553956 532553963
    0x801020306012a0b0c1201060206101d01050402131e05040b0d05070303080a1b0504050111060601091e050a24020a1a040f051203150301050603100e0a0f 67
    0x1a241e090180000d0b0aa2005200688401c002c44a0601c2c02d440c0b0604803084060700074031130b0700c0c0d80c1c2c481c800408202c0c40340300b4018043c2002c000012921070707000a01503010300c0c10540700f8402c2035561000204038612000c0c0003034003000d0440040006c0d180ca60068030030386420404218429585000394604807009a5140b0076280001804000914281c800c841c860b03113003607948c076a001e4030741d40c0e03480d0303d034561400020280a0080c0c04a071701ea210503401203001100e5000c00e0800a42030180180c0160014810b140c002607240c00c91020217513010580c14000d0f0410703159610550708201c4c10400c00401c0120782404800c0e41200064166210103038100101541a064256101c3c1180354050b407001c0c00148800303540c014940d6800140381d1142403e410792551141080c191074178a0607208401d0201000f0380603100785494040c94a40c0000154040c0702e002c0302141d401c10746042813600707960301181c0d91a41034002e041fa0090a82d11900031411801e414819102071041542d1015481c910980082d03 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 532556456 1250 532555206 532555211
    0xe0f0112210f020d11070302011808071409060d02030d0f0212030a09050114090a0201050f0c1f0e012007030306120503070b0a050c19050903240c120c0306060d060801 73
    0x11240e0184000e10455040d45429504c144400b10705c41d5a8555500c0300a0420410f2a441d0840d49030401c0210003401000054525040d07803111503c00101815545500c40c001540200c0c00380d14060340e80080c3e5903409400740245020744103040d5450280e0308010001d50003030040fa01c40c3c1694640046200d0005074800190000381403c0613400c54210520311401c1d201c0c00014032245c01000102c0b500200d03424600f007562180ca0808011240c010400307900e00910030400d17020902c000380325003403c43c1c0304458010001060300d000002e0a90750148400062001c8183c0000951002c4000400d01c481c00390501058080d9100d000c0011550071400644d8507800200c3c414040010898005030000b0a038502400303075040030b4182c0c5585100c0c04d034400505160840d100402d0030302800c295400004c0003400c4e20008000008482215440540000301c1da06000000581d0310b9190703402e481c1e200d40ca0030002c0d4255034416800230210b42c000b80c0b0540d4440402e0044244005045c01510050171008001 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 532557706 1250 532556456 532556477
    0x1d0f0c0c10050118020c0312090a0f030c0b10061b060204030b0f0a05100b03130302010b090c041410050909040c05030604120206070c080d09060207080318070e0f011221 74
    0x404e103071590381516080e10180100441010008000103507550996506400045600c40c10085847c0c0142c0d60b00041c01101441106400e1607000104d10f2032190042d51444510390382d03c4c100a200041901500d00881c5680c20308a42280c41214042500351185900600e0183c50780c035480f8100c0d0045034101e401c0c4400b1402c204030801c1324062150070100710508840c0050503d18078540d14040106404075441d4406840c00500d4800d4203d24200701000e007229100d2b080440c1083c2843c1d20030302400e000e18284544e51405804c0040ea0000421866540c29013042410003c12103180f40242c020385080c0c03200c004c089155903084c010103002c0e51141880320b1229141060103410120300070301d8a800d02072a095920003181d60703c0110380b06031203c1803001410070010301d0484001c0c012040003500c0410003004002c2c00055203c52101d406c6103100884807207a68600c11804112012100c903400e8100c6140104803082c070301c401000d0114451124450b142c44200821200c901240c0800f4000440f01541c = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 532558956 1250 532557706 532557719
    0x3100507120606021e010212090106080115080a0b1e0f060f0409022103040b0301140f24030406060e1f06020a0b1f1203030504030201061d0f0c0c100501 67
    0x8404441c56154103050001070314000740607444601304091002681e4075130030029402c01e0f0a40c115400680c82c0171352101f06041500782d160003451240141c8040350713b09180c0031024100404140e0072180013000a11000d22241e0b100c01080402401e440b180044820b65583e46c40104078178984115007240c032220240c41d10408018003503404000e07650003907113001a0754001d40c83c0c256920320390360983d00c04000c0b41426007001d1850b41c0308940c014030940d000403001040c0e4401814070074070000e07030449614418100600400c149109800c0c0c0490828840d5001c1c7c3c100c4040301c00c05580d2041c0646400608a584c8150300040402c0496207036158084009043c80031103800c0c6080f0303001e8a614401807030401c0c0325984007249404081d0490460f0502140090003007890b04860340054207040c4c44559140f0760034038018000e0642a42c0c00ca0165082503001304040502d00d00c40300805014074152445616000c0c40d03142d0b520300182521038180d604001040000e41c0c01c024148a24130300010000744c561502c40c = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 532560206 1250 532558956 532558967
    0x3050105060903100b062b05010b0910030b010509090103061e020c0a030c110319050708061303050c0a060509030408010e010c0f0f0c02030a03030c180f060c020105040503100507 78
    0xc11540c458881032042010b2928002110150000c40120001d284180c00c40015528001c03001c800081901c030f001c1c0c41c40894074841014035291711590781880540d8032040c9600c0f035805400441508403403c4201074140328880c0d04050705101060420038036001c2d224020403085031003608141c034415124445058442e02150003070400386401c510441c01d00c0b5007560b2941d101e100c0c40f10040d040041ca10b030340380148100181d005411801c02022078469104050400e0410287c0301c106907502d014801002415160210354140308a106403038031620501155801e540c036411280c031881040c40703448059030020705184030301809456200011501c403441c01d0303150f5013910b00380c00c4952a9079040c1056502e90700e400076094010350901d820071080c000c0489504650000500358042c0d418403805c80020203060301680249003d000c5682c0386ca580b2a0048104550200a072040048088800b0000c011061084c0740640c00c2d188140351891519655a0000345408010042e04103040d03a18401c1c04007050300300 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 532561456 1250 532560206 532560209
    0x601020c09010308030105041a0a08061e0103020916020c0907021b06041a03070c1a061c050a060b030f01020f0408070608010806060f120312090d03021314061315030501 74
    0x2160922507030760450742c0700e041500062003040c1c006e5407119504001e10380b281040000c03550000d044141e94550307502c8031507607aa00c10b03210302048c0b06521180c02110b030146420207060700d8016080502a0710b8803034442d4490903032648490214005d02041e40c00365620034030305501500c2c17960300a000c40d503000c00c04000e12405588410b4480c02c2e04000401c02c0d40c0b4050140e002e481c010b40e0071039483e50b072410816101d4186040000707241c5810380c0f940b4441c041071001141d00034001521038500200703401c1807180c80c0540400c405411a8814070500c00085d54640040f4000c1d1000380644900070802c554441c2a0b800250110b00002000300d410311000900700040c03001011a0f10346604503524160f24680c88000c06000303036000b4120b41440540d41c0c3c40c2c075007009913456600400c69070394100380021400302240074ac94580d80350064102401005219000341c0d101d203130002440d0b122240c036141071311b1060710000c1403480c0c101c101400080c4a1041c03001c0b21a004101b0061301e070307000400c501030050444805 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 532562706 1250 532561456 532561459
    0x3270a030b241e03060702011e0c02031e0712031802041a1005030901200409020f04031713050103050601050d0b0d020a0305070e06010903110603150a06030e10020307021f0f0c080601020c 82
    0x1090004044103101041c849c10401d145000002d0800180904034190301c00c05a5030130560300916202c03003c12a2100045c441c83d07016040c940d0941502203012000e0b1910780c2c554000c990443d9083d0350143c0307400d6002125200c52001c03070b160711202140c0030a02e140321400709840450404010010320500c20700400801960038070808030100b850118410550155000305103025a020440701213036034280007180c0245802c81c6040d0f0010350516591409603100c1003c492808051620010790342d4043c3c0103c50003840141c45640c1410940c0d6005001003606e000c000b6800b1040e04081005600e5820300d402c0030b580640e0107850035074140f24851403c0c1102818850400000301c1003040442c0c884201c074100208200c03081e035981c0d1220344131020a0b4000420300340c1c0c0310300e100400040e03540c0c060f880701445800e03100690301784c00408142282203000850f1548090f8000350400640c502112000703005043d4100800120390007200d0340c100480743d00b40740c140c020561304003c0c0095580c0400031000f49800 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 532563956 1250 532562706 532562711
    0x101112010e09030412080d02030a1b0e24070f050c0925030c1206181508030a03230a150509070e090c0c03270a030b241e0306070201 58
    0x10801d03900c0f030b0790b48294070a8801c90b10900d4412010070100c0c00446280d070210840035034a9060083c5504014400117100d904100c001d0702440e842a4003c1d000c46065020081c5480c6680c1d9202c2c00c961008150310080080c144800c200250001e11011360600095010ba0300501c5142c2885041c404201005450000358041e5090749802c40881c64040e9030580682d071a010079420b8802c2c9003075841010b0701040c10401400d0610200c1c000b0b580310f2501c683c1c40703c00b10f000c0c030041309030325000441c041c414040c0d10001c6e00104500c900550083d08201e4200014000300b08070307040036450082d65280d0a84104100540b101c0030340303c00310031030540800508021200d02d211400e180b000a880c1d1210300c6007043c020200a40042c1c11151840261760f0030303004072015296110798001c0c2d2501d0648030444c00401c0d4003100d07008000682400c802843c1502d501000c502e4031500d45410300100100c0007041080f403271000a9510815031240e011002d0340002c1c042e00f241c4101680d20416040ca1002003e105c1103a2 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 532565206 1250 532563956 532563961
    0x1080f07080a0305070c1701090606051002070308030714120103121d04050417040b03060a06170a0207111e1e100c020301022214060307051209101112010e 68
    0x7900481c034090450340c14184140e803009103113000803058582c1c0d40700403018800d00282441701d01040d0880c00059100d000700704059500d03841004030321842c51600c10016031065005000140702c0310000d6811020b5401c2c4480d20301c0351100c0810b03540d48008184004d040b8428010010411010100e0110105030f00340350340e04051000014007802d484e00d030a00e10483e00c40001c40c080c440030030b00321044d90310241680c0c0d0303a0b10f441e5800003005a01c02d03640c1900444a00b100014070521980410101110341901031400c0d4445203192000703034000c2c2074190b8403464000d0f03a00001c1e42d100d01507044195003000b62007916070301b01010060120000c802c0e6980c0c0d07014145108083c0d5681c903600b0500b44485052011002c030050001c070303009003d0301c5030700a01851085001c0031b8000d0050340743c100301d1b21440c04c006404a40001030013140d010907590000407520901c203c4a658404000d19035200802d8400c452007000045c0b2007105a03503038820403040141e40003070003401020400b2642409003922044611300c50 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 532566456 1250 532565206 532565219
    0x30c0a05101b050f361908030406080c0904061401020d081902071a070201090b090106030b010b030612061017060c04031106070b010f091b1e05040305100501080f07 72
    0x5105130031030044031540c0002d50384510040c4442c41c035465000301203070a8440b031421000c020a1160000382030300c580d610090803081b0810710074180f07069442100181d1700301860050113403035080d070180040d03010340410f00070307681103031240e00c1180001c03d60041ea0400600d0b020002a062091495021040115020405c44001c400c0c1c084880310031840c14005985201d6800d11409040817060b03003a4402c4415410300c00c04070780c15040002d045000745007012040c0c4030b10041900300c0308180b100810b469001c41c010042c0c130407580f0265501030000382c0100c2c0daa15000c1a820b08100040b240a445440001c0007070210401b2407000ba41d03001c0e20b1030020580c80c20090b0010100e4025440000c2034503041c4200e1000b030b0f03264002038541c031907409001103030319584626015603441c0b0907025502801c0d00e028020105228040c2040b100000c040c1c43e1805d10752007811006a45030100c0905c0402e2100800c0004000b400821400070499407003000041c80d94108410079080c40c0b812010720200c1da2080c90240600d = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 532567706 1250 532566456 532566467
    0xb0d12261e1e0a060b0304060605090702190b0403050d0207060e0d022802010e030d032003160c03020f0709150503070302060409150509010303050c0114011412030c0a05101b 76
    0x3a050400b90500720b580701a40200a01801d800c0b0f80c002c0712001c428402003040b40c2d0040e070207880049500d010a660b52480403a940d141201c0e00300102c0c400003200202180c1030303e5099402500038a000c40c82c058102e02400103a82c090102101d14070b585113105500044280702c64081c1c1402880540704450405a81c00b050514020105440407a40d0441c5002c6a00441b4021ba00b1074001e029503101c24101d010240040507665400b04e10809030700c004400c01d0082c0e10440384240c40d146c2444081840500c42201c14190006e411410361282c040e00700b0035001c04201e820010520900b0210701884184071311441c0381e115500840c020341c050003045c00182d46140a59081e1006c1800004440300f01c038410b4540b050955101c150801103040000c404e241d4010f00800d18581030f28000e0014041820520384643d00034424070011603036051141c02c043c64030440c07034640306c0c03d0f07202100e0402c0d049911050800742521400c8426074021500c08010040d5070040031481403203d5031401c210024000003805 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 532568956 1250 532567706 532567741
    0x1e0f0d0905030d11010e25090b0616060e01052409040c0b0310120309050f090403090909051c090303080a1107030f1107030809130b0d12261e 62
    0xd00240801022a1104c250300c011102c2c2085000c84801004201298912030019408081d0800c1640004202c00607203020321401d03030308054022448d0846400c515028011083d03021a940b41e1115801e0380c3c0301d030f024083c00c4d0080d042008640e600603120904021030b00c0c41906114003580d580307000c00c408112445041c40c00c80d03a001d11103903a04d5860030400d035803142c0b05400ca42000c0c14080301c074205065008039141c007a900b0903940302410000010420500303607070407503001340020100b402c28010311500d0303000100451b01c24012568191007017014420410b42400f0480005001240200149035010f8000f81c6c000c0c0e0041401c102842d5079941900407489403480140a212240c1d41c00807042e0701c5042c400d54030743c40180a03541010780303900d801c1406500000049114441c0005070764584030480c4109214a88000c18915820440355508a801001c140111003800182c80e680411080300b00103100b41d00403028542c1e4818031389003215071180c1211064101c100086107007000b8200c442100c0400 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 532570206 1250 532568956 532568983
    0x1030605060105070b010605090a320a03080d020706050f010f050907050c0607080a0c030c1d15031302041a01082a0c1501050d1e02031e0f0d090503 65
    0x40c25a460100681e810700c00e4020040c84520031030000070740d40d0383c000040e0080700320480da41030019a5403071303200c030340c80b50078000d224003d00314090241c029880070310460700c0d42d2078041c00400900d40c0e6034807401d4180d00418500c040840d0001082c60400a15200702580070111800712185541070000c181500d00240c01207900a4201e440440c0d03003540200300760350404174440c0881b001e503e0035000c020100001555401c101a0502078200300082c001d0085094590541da101c46103c035800c0ca0000d1b1114082c50f42d250000e40302e0b4601d0024440b80c1d0021841b03002a03094590504c500f51041c001106d0708490007056022821021203041c1c1e034040d0919070050f484200000414490a5642c040058450b0b01408200d10004280c5d02401c004100c80c0f14012890030040a20b13a88c40c0d0a00c40920442200185050707000d00c44400c0ea6040203000200345800a0202c030390700c590840d203080c0c0d181d001d03451140880d80008039804442d5402c0014000000451600104041c40c00380820b9980c1f10f44000107 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 532571456 1250 532570206 532570211
    0x42f0c0d0509030111160c050618010305060406090c170903070c03020d020a050405070c020a08012705070506070f020423190e031908070e030a0201050f130305030c070e0f010306 78
    0x20b144a5609410500380302d403d201c003455452110411040c480002003030103c8a620064500040a00d84001038950343e02e80301c05c1c0700110f00c41c400011401800000c120650240d55081e0108680c10144202d00f056605a1030305820060006240501e101c4014041003241e481045460f002900030440a01225419512245801c18034400102c1c0300130030707030005600300e0b28020802c0707891a030040714044101c0c0280c0e070b4103800c591540d49039420ba80c00e80a1540501e441c1c1ca0341e6180c0c02c00c0d8040c008038402d0142c8143c42e101c0351100300041c5c0d603500c10901aa0385400b680340d03207819480c0905c11702c2101488046510701c251995440c4443c201001400801c4240380031310f01001c02100742e041600c4160003d03060f281d8900029080c1c005141c008400703000001d9243c030000740b44900400c1220700d407541c003d00510224040e40d0044070716030b01203000110140c0d0180000c3d00780300540c005400140d40f080b0051a1180c224001c203500c2c04642c1da01c202210805601440000002c104e4150b040d00d400c030802 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 532572706 1250 532571456 532571467
    0xa230601032711030615011b1a0f0a0b0a0e2a0a02011b03140c0c0f0109080a0e010929040e090c1302040b030a020a03020f0c030306010201061505190e042f0c0d05 71
    0xa8501c027420360b10032100c448000e00410101c4940b20200911270401c007074042000c440f40c5400e00900500d54018415100003a20215035160113407902410124081d02c5c1e84100e241d090030741101c8540200c4121400342c0e4640740d13102182030311900b44110f1602c07186400c004030b40c100312410100580c090034618242d500082c403d10074007410300544018006440007404400d003545080001680241c901d00001703060411140d010f1344c07044c42c0d644100c4480001c045414000140030a000a444010f926645a020000080c001c820050110300c20345111016120a03486d80c2c003440994031207444020340309481000103220007010982500c1d000740007a1030042e01d8200c907036010740080c425000503080308030011444604101c2c000000b10f200c0d810030b07070080c0081c580d90300a0380c01c0007100e41e446602251051201d0303082c5840d0000321202c4103a01e4905040f00524900c0854100e40d03900c2c000403070004052103e9011070412418141500045005a80c6004106507034aa15140100720070700420400061 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 532573956 1250 532572706 532572713
    0xb01150210110d0606050403060506030307030801030b06041401030548040605061c0e010203010b221a0408190503040b030910140a230601032711030615011b 69
    0x10741c0ca022402aa04004c1c09407a400060701ca9001072000311b8190382880c00040c4141000b0003070368106903258850000300c1e401c60391045ca0050f0000c001c41c0c2c1059581030b12480c07404040055500950040000e41203005510a0762060100342d0210f110b00c03a9068070120380b14460180c14411000850404240030303455070800500030348981e621141c0e12540108610f540c0655098030380c0f50708020301074100704400340601c0b0305090340424415031a00007000d00c0f0310f0201e44002e00b41081d8064030029980101c80d211034601450385559a415940c402011070140702400042041ca182d04201c43c16810101005035106030fa240718078041c500c022407021001c1148014100051060f00b6401c50050100b140260700440725141c01301d40d0703100440e0400121500c00a81c2d03003d81801840000200c841c141d80304001075029000301c0302d5089960022640c1103400380320106600d00c86a11a54a00c403040c00c80600b05480c00c0e10140c507111031151180043d01440c3c0e08200c525224450500340d0318142c03125030a = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 532575206 1250 532573956 532573991
    0xc01080c070606030b01081c030621062a1b050c04110f0c150c03040b15010e060f0901090b0a1e0c02120f01060605090d080d0e03040608040b01150210 66
    0x1344010014080100003041840c00810215007075181003101000c3d04000000480a0710400d1089050004030300112210f1360b8520825070008500403c40403504603880f00401b0600d032400d003000801a8900010740c0f40650740542d09414000251a440c2504034450704c0c0d1903194990480318078800c03582c42566184240d288000c3d030b500540d00f209195100e0f0b043c00025501c031220b1900000319800c4e0000000d01c400c00d4502034a0003150403c0500b5140e9407070031803400d800c1a034003050303d05010b1000d980c1c040c90b658036801044e43d01ca00c182800d1312030040390300160484100e500a0369410f002444030301c0041364861501035580114182d00e041c09203030058183da000640c280081d4010007500c0d07120310383e0b034400128458902040002000b699a40d480d0840c2c882c0640b0048542c4589400d8078880829415800382899466101e40003500d082140c072581e1a560240d07005030042854101044280400c49451500408214011040c1540a498000d4841c0208104d18240700c1e03440602c0380e101803101 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 532576456 1250 532575206 532575209
    0x100612020a300302030a0206010905010e0403180b18040b0a060503040605060a120b0f150319060f06030b07080a0506012a02030708160f050a05060d020702030a080316020c01080c070606 81
    0x1600c2e10010203503080003074503680030052030f070054400c0d28000280c0e00403038410981240c8000b8280041ea8403103603803c0307506112035031444007400590480842d08120b20b500a0500c01500891070903820b00000500c030984015954040c880e4051070420440981c1050450b82c0c001d5100100103801d40d5880c00113000c2010503042015403002d10300c803140030045039601050048004400c100c960740d0b00d12155407010320079101080c1c1c26400000748601d00e40741170054000128401e11002c07860891841444080b034403503500998020805100f03000d1840c0e00f0900c0e00790030220312070050155107016000a04240c402d0f00080c1c0d40d000c200d0070311404484403d0b01c000341036030340101a22401640d071030341140d0b500d072840c400480320b407203140c40001c418a807002000c0407200050312080780380b46040b0030001c0d42e4000c20f001981558003000591f005a03418002e0b962001c0c4148000303506c030300300030151032541c1101c1d41051041d90712401c01010240e8028101c940e210b41c00c2c04d005a6076006919250014000d203 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 532577706 1250 532576456 532576529
    0x708160f0501090303021b0606150c0f01050a0b1903030903020f041409012004030c06110703120503040c06030203360f0a03140f040605030c04120302100612020a 71
    0x81001443c00c041d450703001804034a00c080c1c0744004900c009081180c03500c106480311a880b8000200100c140ba010758084c00e02844100140d40b142004503803201d007507030403c649403440103035070746544529032506110b0804e0511000c0310341038134141560303000b802010705400080d21810040c814904166207507040101d8940b003c1100700200c0c1411181103000e03008818181c0081c1d0503c50104600b0301860068070102ca8116083c01415894041d00769150100021086014083c500b0003202290005010850042e259503e40345c1e24903060401130040340441d088001010b0042041c400c1c0c1d28940d602103480214940c0d824103410390449100d410210100035100c115004078174100240b000e020911f1006035010713032038444d8208142d540c05e4400f40f0901082c1c0000f01024042440050710910140d40c1c03003504112068134050311007110068101690380218011f90050302c441582c151b041c01844010000ca1010310620304d070036400284010031f18000d12003d101000a0009800210456401402034 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 532578956 1250 532577706 532577711
    0x21b03070308010510020c01050909090a020306040c0f05042c2e0f0504020d06200318010c050405030c090402060405040c0906030515011e090b0a0903170708160f0501 73
    0x4285006416442c092080707620840310384058541650021801c00007002c8143c1d42c8615190401c01004a5404060102600c0d0f204d82c82a00005031801c216240c0030340c0c0100b409091140c60010310021a03180790304541e0081703003880b111000082c40586090418140c103220803d494020a40c0d1504e0103d00e0501c2e040300300e006405818a074103000740409604a0111000c4c400380f141c914600c0155141614025002540800c1f00380c042000c0d6413201d48840e41640480c039101090902141c0c660b00306445082034481e58000d51540c104091040c201d41018508241c2e007071629100000e902e030126084124080c05c4420006400c40d640c590481c1d0181000a00801144400040092282c0802d0044c040424074080c0810a10141200500100c400c143d42c2c1040082d4101340c01c1c010a040d00098500340a8000c8004c21080c2082c00030340083d11042d40c03034140051560904030322b80702a0300440c5101d00b40800c45200481c01000440311000414404101d60150718075202000d020100341c003070207552 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 532580206 1250 532578956 532578967
    0x509010614011211130515040620030c01290d0506070e0f06070303090b070804080a0309031206090b01090f0305071202130204290901020601052107080a030306060f12021b03 76
    0x6a00960b040c003514010b40e5a03c01400c0c000c03448052034030a60040c500410b4031140c6038502c6602b1010b41460380303c5240c0c00c2e2801c1c003a84022142c20745003031030801c809000b5121608103640491135829280042c003203450b00d0307410540341c503456101d04002d0840800c0001200c90803d0039156030700950780000c400340c0319541d01c40190800070000c000c0c3c0c0700e0440b1205149030100f0020382c80761030740c0e50140d60404403c07440c1200c100c0d0300342e0043c84101811405d1001d00f10503c100c02510388120001050081c8000c209201a04001007601c0c40076042038a01c5250880148003044000a800c0140e8078404280c01c80a07140780000740225003094480554140002401b0400c1e440045082660a034107074680300c145c0050741d103000400c0c0503200e2000c5c010f0340654010070845c034058010826002c040316000c503038906640c041900b451051340006500384d012941010406a16202d280c00400349451301181c1000c0511000b403000544241081c4829004144255026680c2d914924a0034140d805c070303075403a07 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 532581456 1250 532580206 532580227
    0x3050609070e061f0804020f180708061203040905060a050a090e0705010e010c3207140f0114090103020f18010306090614040207080409060b0309010509010614011211 73
    0x1000e440c042c900c5100200d80c041640b604180c1300b0443d40f00c5807000f4901c45031071000c00858013000300030016a48940d20704a08150360300d844916800c140d10009030600c180c0fa210780d000d018410050325140c004c51590025000303440c40401507809460640e0400703d06501e8100c0010210101c54001d640d211258040010b0a10a2540400d80c41c20100702038400b1030340e48100640f0302d42c5036030f01240d0108004401500c00220518020b2005e40e005080c0100ca10400464426500984000700070b696401000d0500429140568101501d48126608210b1107034800c002841031340002c40196100a000c034580049030300980586004418031030055482d8030150140500302446400d00502184c9003100c04620b94070a40542c1054942c4d00c0e0003502d100100c0c40030300c0001c2d40f1410080d40d20480511001c00c40d5003080c09503000510a9513440e035101d04180c00001e08445000d801c0b00030913890000108003030f40c7c4400711401c0341d907400d081c181c0281c000104464081c108107180200c0d400300c009071480d6038 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 532582706 1250 532581456 532581463
    0x5061201020f070611120109050a0f02130603060e091e0c130b1309080f0c0f070608042001020607110c0d0c090e070f170a15060302040b09070c0303020a0903050609 72
    0x2c3e24001c0d4414041924070306040d074114860004011070740c54486006001007542500401e8200055100c0000c0c24040c00940d5000c0381c000c014559403600b1400f00800c111a81402048090400c00c08602003d0900504a683d180c81002c0ca085000c1d01440211002034020f000c600550240070f4000980307441150288801091002440751103800c80c412240181100d9100300f040e032690024449140080114502150382c01500c03603802c03507100e00d54a4064070102800448020016511007881500b070a207031410030307035a108110801ca1051015030701c0301c0d83c0c0e0014505400c01d0032400c04040a1071060318480c28100c8a0303040c0354206034520b401800b0080c03849142400c8840030b100401030451907403003041c1c03a044c96104082d00107040b0740307007400208600340c58a5041c801c24411680880156603521100045840714907a01035550a820015400e04c4e01400094000440d008010b5150000003d4509501d41e100a41050f0740070405e81e003441e001e00300039400756400004660a5191403480243e4 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 532583956 1250 532582706 532582717
    0x271202100e07271103010512030c07141504030c050109050102030f03060105091c0b04022d1020060603070506040b0a08040510060b09030106080114010e150604090902090609010b070605061201020f 86
    0xb5094401c40c8c2ca400010110580e5074511403100908081c9140044840c5c2030b0b0044500c1a038402e00c0c40307a0441d40d090b410701c0184002c5110700c016140252901002502c400210f0380458107640040110800c20800c401c100c0b58442400d0801c9522100c1140c01700740d201903983c1c2c10061140304107100d4001c0c800504145071103203100b00c0f104200c01c1c10b95a50039803901c0c03030b540c0301d04000301c0742919a40840c81c060b00785075005815454802060a020030295400c0b0304034000d144200c0e0055000c1c000d80d42014400c0f200542025110b00349003902d00710030070300c0b18441c40f40b0250070860f180f000309003000414403124030b006010180c203218258541c804c16002e81d11401c0458403c0d840d00b0000541521b040c007e15011000908110f4180d03840c2491107103548500407c010190094624403403a207035506c1c40604007901c0741000c00a402586071041c444105000b0340450310401a40c80100303c1c50f807500040310403050303007c080800c0030384550001c00c413006489500800c5950000c01e05401038220b80000e00b0 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 532585206 1250 532583956 532583959
    0x20a0801240f030b130203300a140304031e170609010b04170106091509150f0504020f07170903060c03010302010e0103271202100e072711030105 64
    0x703484a00048104015051081c921141c0440e6002c02c04184410300c0345501888203600b11811010581c002030412607d6a0701602e441e000038841884106a280110050518a1012460100c0344074003d044070a80344100307080048004005810944122040d442e0800c1606115400c042c00841c090701090f400c02d1500c25011142d00041d1880c0b51000b0101e0403142507a00041c9401e090012661241c1900304c4100d03042e641300d1a0015090025101c0d074074111980642e50710403942010711200c1a11011080c040200001210911400da6140220742c100c0b00202c500680e60210049214401d003c0d00d1806048044070030040c51908034100000c0c00c480c0c00c11825104103650709a07159405000a0001900050540000c050f455009500c190b08400d02311018250807585400d0b0038203078142c00c0004680c0301c02d124160300a400e030104440c0c6401070401c1d8043c0700310114515030f01d5407408a4805ca41d85414000d030501000c209052240c80382410402c001c0c84a1500000c00954945c828820369 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 532586456 1250 532585206 532585241
    0xd11120d0e03010b0f064e150603100801050c040914070f0c021309050a020a050a03031e030b0a090204030b01090506010c060e0c031b10080105090115020a020a0801 72
    0x10300c0103140602c10510304280080211700c104400205100440e0401c1554105c1d100380750403860001c0554581070741200508041030754905180701044114910300e110b8500c10701142e0402e0110f00002c078009640000d800307840c041c0d2a0354981c4911255081d082d0b111208952800091000400d24030000300250b920301d203428400c01c3c0c01c0e566920100b580c00c44101e00090800c040340350039184527000c0d000c1c025000400a00f41300001100780c80440d43c0d900011550361f4803181c1108118140161003030018441258180c41507491034601802158611050310011181c0c06503581c0007900903800044040301c0607280c0504591290300d20b40003984a800301380d6140c161000001000b00341800342510a03a41a903500b03064506a40c1c0c1c4c1c0c40034181c0394200500900603040c0c18030b101d84003081003412450480502d07048590408050000040c2590400c000704510000148083d481d1405c0300c82c112050290014454035403100b00300c0c1070076400000203520508040c0c0006030744c0303415000b210030b900101906 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 532587706 1250 532586456 532586477
    0x60c010516021f15050907050901110708030a030e07091407122009120d1706041802011d0d03031b09050f01030905070b040305030c060c0906090d11120d 67
    0x40c0d0f980c0700c240d00c4600f00c021400c40904695146138002444101010010300c60f0f00e9260400a00014400c035024400034101181d094219a4480110050010500c02034020581060602c50b120b12480740101d091540390190f142c207050b405c005800003400844001c04c41800c6104c101d040701c5205645920000b080c0c13410540742d0046910a8903039004070400c03130301e00050410306108000d81201c1c086e03a500c040624944054114240104803111070195a8444010801c41d0b503a00c4411020701858011440e00e480c00e400880c0c00ca40c0017514640900b80780c88480c8448861003030a00e0f00c0e40a80e41c01217441500f2004041e01a088400150303003a00d000002c240304d0407411103941c24648901503002e12091b140304801e502079808940c01a008600b40c41d096074443c90300f021340b0791180d4021070301c903400011035040001040c400c5c2038004295480490ad03004215002a13128000c4211071485024207100c2142040805000140600b0015100c08071750700c0400707241d64907400b22218100201b80140030 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 532588956 1250 532587706 532587751
    0x50c030103020310060e01060c050a050607050a021006080703030809030c0d18080a0201020a02042f122a0d0f0516080612070b03070c05031305030c060f0a030911060c0105 75
    0x1a001c1580c40014000c3c006d6031800008880160b8407103819079030741c05901300c0d040c00301d00148141d51007181c0d140c55050703807502c0307420f0700034905110242150101031a000741030090324400b081078000c5030b0701460000b60a803a228030241c01c51098042445507441921032000c0906e4018007403505244a0650184c0314990341d00c130382501d91a40300340081c0142c0040403980c0051600d44c0c03000d14030b912120340a0154400380540c2c481480042040c0301c21180c1c003c11031081c038004840400b6400b000c22284242250880040844106c04214103282c00c09004a810b501d4903e099010210140c070204084c081d6050418040050341d1240c0038000008884400044c0e550400c640c070b0350f4845180d54000e06e0310b42e03d02892204c0c1a00041c00100c108180310500c0c07004030b141080685100c0300e001120f8000300d4a030034105450203040c002d600f40525000d01000c0402010802070307591101840c1000b00300d4904510f000c0f0140d603e0681115441080400d0845030365905501ca24400d62810000b403103448200304 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 532590206 1250 532588956 532588961
    0x30a0501150e0c160c09140415060503190201050904060b030a1401080d1209020d1b09090f030e0406180b0112110307111203071205060109030510110c01050c030103020310 75
    0x540145000c842001803481480c00780d04c07006615805004030328440d9440b003840c00143c07080c3c54003007010400d03017005020a0050555003403244008911003000700601d0100402c0d10f40480f481201d50101c40409801e0070359010381e04485001100500811101d46c0750401102250000d03600c0c40e920318a85141010006440540c82d4103907440b010044c000c18003003820031102580b2400415500c1a107643c0328200680710702c014520228415104200d4040442203521850200b5901034042c840c103011666010a0520304880f110640526000300ba40c881880882e02034600d07948400c0c00d07040395903001d03d48403032142c0c80030b8210307030b0240ea03071001c594402c0c0000c1c1c05460303043c0e1422000c20400c1001c1a9518020071100800741c0d8110255440e00d280c400814059400c11a14078011031146003202000030564415280c0c042002d0134030352185419078039440d40d90b000c0c00d0008080a6910610403100c0c2c03001c1d0741070351040b8030750724004d000d54640301850000d160400c0c40100d003e48a144200b07000c551290 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 532591456 1250 532590206 532590211
    0x14040201050f07140a0b060306072a110306150f06090901050f0a0306090303020301030c0503150a020309010906060f0807170316020402090d260f030c0703030209030a0501150e 77
    0x141d44290070150340518401159104482c00c035048001040111031a00003800320700c0e10140501d4103e055480c00c41c06050134044000d00d040104203107a01e0709004554004010400c0c6081000d9048140343d031071600e6020007000c07003100c03a454400d4404004a00c248400361082c030002c1643c0400104a403501440014002c0750b80340c91788400c0f1003005005900305412a9140e20300c006104407445a5a0344030003080f10344c40102900020f8000006005205000c0107a10007005c2c164024403a150f450407654410ba140508140025500000401d012034006d4014840403a0820b600f04003003a0745d22140002c042da180300b1280c081c081c8032130006580c000440341c603600c0e0388454050f52810030300e00805142410700f02d0089900c60f1382400304108c00c4e2147c1d031600341228071401c0d444c0a402c6d04806c100c2442c0c5261030403004611002c002c21130584228100ba41d40190b02490500e4176180c0a140a038080d0040f0784115405210300000300080c004150800341400f4030800641c600e481e121402c203500305004 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 532592706 1250 532591456 532591459
    0x16081608060414151e07050306130b0a150314010503010b0d030c020a030b010e07020f010e0d0305040f02040203040b2212051c05013002090f0403051207090801140402 73
    0x140300080c0410040b1140088100310318003558011120360f01d002c0402c0c501070340d0817110b0b070116601d031201c0890040503843d0000703007501b0318030304603e0f2020004011000e4030000d4000c1c00d13103c50b140300705900d60180b80300c050202c000340c0380c0c240108100c0c020000d0600c01c0c0301d440c1c07000040c00001078130300701807103007105440c2c4c09880c40450445545054801d816458012a08007001017400800700d84103201160207014084942d00d007500702090004e1900404074500440c3d42d01d03103408614603600005100300c00450b03e0074045829595800e1014100310007004c0a901f1500010800c82003000c940d07440343c03061f4094420b8404650700c0104d01106c01046a01c010101608020303846481800b820140843c903410200b03180e146500c0081920507242c0c281e06c580485488034543e407215400e0000302c20f0000403c40700d40c0c45d5003480785e00001e801c050041c200701441b10110740441c3c01e2601c00c20444030f21002380040599641000c1400074402c211510030104554a030213011400034014400680c0200d40 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 532593956 1250 532592706 532592713
    0x5180901142b02060a020709020f0c060702060127060302060a033314040f09030f1d060a030e031213033c1809020d0b1207151116081608 60
    0xb580c01c1c4865641700425032015072040400000b1003000302e0004000c000c0902885588038810420f40c94079001c000760682041d03401400043c0040b804080b45440410050b050700c0031122845c90350140140469003020303400180c000350501c074441c2c150b000b00d480e021111480002800451102d08510f01d04044564001c8015160821481d8100c03580f510350703200020400600603000742c421000711980480c4c12400314000c00030055416400000380da01c51703031250310224450708a15000440620030040700c101890741c0d81000703440c0040208203860f480710f92580c0c4400c1a04007002c8000e104540050200c00081c0b00d006c003501210f07400040003c134002480e566004005d0560318400b00701194031302c1042000012071001203401d145c00c1103040180001c03a00142d0310148100380c00192008108101d0080214056412000e040092a4401c50f010301d107106c0088190140300b201c02610281c0410164410392000984502505080da42240c0340041143c0d42e000c19604081814019403041203050340 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 532595206 1250 532593956 532594039
    0x120f141803041d150d050604060b04020a0c02041503021c0510020720030f0d09050f010509010903030e0f060d0f05150d0b090a05070b0715050f070518090114 69
    0x200f0703d40d205604140c401e8144a00b0184403004103c0703015a0700426a2194003030400e003c00d1207102e00c07419020980942c1c003980380c0204c00f00064580204280700900a580c2d41c00c2c240100080e040c4c0c22009913034010103458046002480081d4820741500d01559980500000440c94031000d10032100700310f60007161200c0c0c9420f0021950400c0d51405506900342c0607100320090390300800c0c442c1d0240990307e44c4070450308a00b81010b01c0582e0356110502d0381404010080e080391682c02c5440c0c0e00459501d8030300b142800c0021000700d201d0b010f21550a0742c00903404600042c040659030052060480e24503002c001c144d0703401e54448148404030000c942c002c9807641e140c0f4041900210420740c8142c002044408500d46c80d500c0d2450586241d201c0d0740c3d0351901145e200200840c0b40103042402138022410300c618200401c50502c0f201018000905100c8002034107444038441825403505608014040d0b283d41da9110a22030120030070348a240d2041c0c5102003624898242d04401d031120444c807100494200 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 532596456 1250 532595206 532595249
    0xd0c0512070c21021513090c02010213050a0528180c080f06060f07050c09070e030616201f0506040b1906031509090f03090902090d03120f14180304 65
    0x241e0002d030408007a15408000807e07000001d002d005007042c101d900040e0789480030341800c0702c2401d080e00814800c43d182c020402c07142c0d036411640c45c483c8601c071401843d11220050030102c0d80300d01d584140e0001c2000e0100ca40c00d60001d0348039005241d65500c6202c01d0381e840990b100180c0d0411540341d9403000d8180306200b01c1424400c060000244120110707204c0c0c114078000aa8084822501c0b14002840001c0035130050a05010311500006a0401a10800ca10200281000e0850f20b0040283c425015a04042040030401d020b102c043c80540711914202404540000e003800b181d01c030b80110304010041c005410481510484180100c00c000030f0359044c2001200030344143ca1300050101c94100001c19020030600c0b540d000640b09180d0304512900c549005012000540e0080014520500c150926600c903900d5070380e00c044d414500200c005020202c03240c02040c0700000001c142c0e2408092109400050200700d00440d0070080400c020300d040080b8036030300c0c4158001c14040d240e441b031520010 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 532597706 1250 532596456 532596499
    0x3150e09070b030405010509011107030c060b0a03061526030702061b030c0105070f051204020f0406090c030504060b09100e19050702030919080d0c0512070c2102 71
    0x842150191481d9541d202880503030b9030400d8509071080e9550700240503409a09104210381607a0b400d401504001803620701600d2845803900280800d522445000081ea0321a5603a60103158840c03000c209210f200100c40400c01314600400c0703026100c041041000c101c25442e640501c542d0700d40114640b0340d0070b0b0709102d0b854100603080150700d5858030184022481c140b010301410b4206400006051924076801044542c1c654a902d0038048108900e242c500405041640e001d501911281d814072109e0300070400030091648140d4500d480d11104045495140e08002d0040303000e03890922a2285100400079210b2003541e40d034004010202d0304001c94140795000c10b80c8484002c1c11030720072088120398201552001c885000060300b00150750180d924007a0b01c05892010345611051089080c48007041c3d403201e41205640030b211040020104005040001e02400c000a194440c1c49074131910340042d04811601516111002d5240c502d00d0035010224203440b000c1d001040c0c1d90310800100c0ba007200 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 532598956 1250 532597706 532597711
    0x40605010206010f090e120408030315010e0a09200a090f0b0f030f0c07080d0902040f051b1b0a0807140f030d180b070513090614060307230a08010603150e 68
    0x5107008030040d07544911f0069000c0d00050a0070006107070b40385850400c080b240f4000d0154181882106c3c6074080003070311011607003000c3d10005103000507424440482c150107201084910340030380d0340008210000d107030f00c03485900c100c40c0010ba00320801e6407101550f44250180030402d020301c0b40c042c80007a1a54010806260300051407030001460100152035601055005a80000d81c10383c59000c4001103060034400c03564036440c169801c210500308420060701d01644941a000b88040c08592014561044080002c2c040e11640845090240790300c0c000103d42c2160b007040d1200000c8a03500d910828005c5601c004846103072000e10300d004508081c801c000c0001c034565202d08511100070b40c0000b150f01e1102402507155448268032500303108992800f241c03440d0001c000342418140100000a14854001101d0701d0440d6029101d540b17180301211070b003212000b12220690b002d003070901260409001041c3d1744141b5034803180d0503a20ba0030242c0030744644000715205401591002c00104140b00308054 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 532600206 1250 532598956 532598981
    0x60114040b0d050f090c130b010905030114010816030b0112061b0206061201090209061512070c120806031c02010204080a11030c10050414030705090c09040605010206010f09 76
    0xa0426072680301c0810300307070048001c08080e50354910501000701c10f494440703030748051840c008003a00d440d88070101c1d1011552004107200c042e111540030a090380101410409400050002c00070701c0035500d074801581c10284107128840c00b41410052030021441e03c400240ca411552009059180c528001142e68503003000b502c4007a62000c1c9640a043e034003203c0791940c0c015500600b010f0405008026803440445030580940e0f06d03050300078005803201ca4a8642c840360440c1c6600e501c0c504e14140d01c903c1d100e2900d2901c0c02040440801000c25007110000c01c43c00c2c06002c0c0351071042c17403981c1c00769940132050360380c1c503030550240342d00c0741c0e00646150051501075190320002d4282982d0f815002c0c5480d000010844031645903443c90b03800c9040c01c02139440c050070112061075000d04a00d101034004d20440c080d1070422034139082010b0007601c04008500040c40d000c0c1c5150700301d15260584046580001900501c2541001c2d000501356200188041c165103031b481c1140170042c074140705032000740580c4a980 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 532601456 1250 532600206 532600247
    0x20408070303120213060f2c060c0f01050f1f050f0603190c02100e1207030c05010b03030d0225030230040308040620070b07050102130b0a0f020f060601 67
    0x178203c941100c10500402c0350b0f888070404109000b1014080030400c00700c20000950803c00d20f003400803030b130741841041c0e00213981039581c86103840700042c10000c02c682c04140960810050001c00f1502403c4c56110b00070340b10108080704100b035081d03a0707443c54034441c46a100c400c1c4149a265854200300442e0401550002401126034686402c0c05a0341444481d50250300510344880c0703070f040180071b0104913410200141550003034944503003400b802020005410044001c85003800c12809602002441e84e000b0b01700c030b40b2503816003031f040d0213984418290140000200707464410b0104032030f00c1c54209035141d005002441d0a242c800e2500c0d00001c2130f00c50351581c00b00e07803850b040113400001748040d40c011600595100e080405c050310085103441010000e4460900d11500c080c000318244050303400e034076143e135a108110708005001e130007000d98032074440030740800014030a0b5648000f415101c001b601c2d0143c04a80c119010b070f07143c070051200a001e5420020008050f0b42c810042c4840b45001c040a2 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 532602706 1250 532601456 532601467
    0x702030105040309080c0f030715020f1911030319140f0c0f0c0d0b070309230705190612090503070f050d0320072409110a090204080703031202 63
    0x280c2911426101600840d100c0d5205118042c42480034444010050b034107450f10907e00804251358450911130410315001001d101d1080c94400e20144101ea400e072000c071408e56280c1a5494010550044201c0d514002c2078200c144ca814080300b0390710070400000d008100c1c11000750b81500c890340014403000041d60104000000b2403020070241a0414036080103001d4810411b0096140a112546041c8039004060b5407070005001080b055501074038915001c2402189813a0a00e500b801101c070306001c0402404000464010000341002182d404952126048002c1c104181003203105c0c3c044c500014808060503503a071342e02908098141440340301100d103810031580b40c0803410a8050421241900714080010804e54940241152100a60288108407100b040f1001040c0701c0d07500010449203880e5a003840d40c46965102060b1006006800d0040d41010314043c890060074140840c41442c0070303100860754021902c20345098070340b11380040503a982103441c1983c0d0542c8034084c11755115000c110307 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 532603956 1250 532602706 532602709
    0x909050f24040e060105180405060a0905070e040503030601120507090b090f0621010e01060c030f0207081c02120c0d080a020702040f020d1b1e0224071d03060105150702 74
    0x542080c048403d00503021550501c420004940c40c5007107041006850314060102054000c41d1a6420921501002070b0325525031134680d041007002e82c00784070200d02c410100300a002c4080003e51040400b44d9881844985000ca02d82c00c403101611a4030001c0c40d8002c0c03c1c8102e51140c4000c0c100d4801c01010006444202ea0005030107078414000308000008a01e007650035640407446035409444004500c8060350f041c4000100030303040860300507081010390154030700113500034403008002d8a4500d05840310020701c003502c0c0c6150428880074000501c103100d4244040c0003100c0a440388010240041d010005e0300b400101c602030400381441d40107590811079140140d84034410300440e910110400744e140c0e003116031100100d076071074a201c000c404404140d00c0b00b1298412100d9240c0d12140c084240c1218040200303d25141f1985184003a03500283c1c4566004082441260f10070986980c94200068800b003401254014405a49406601c0840140810710f4840d1810040c0f1084100b01410030f03501d41c0 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 532605206 1250 532603956 532603961
    0x1707050721030e0d05070f080f07061d0c041103041b080f1c0f080604110f030c0309070b0703080411010c050d1710081c0c0b070f0909050f2404 63
    0x885040800e41d20303d284200315005008130041c50400703040850902400707480300b011040e01d04c1c2005101040014a108401e80309106440c0100c0d0441c0c41000351502104140596110b00254184ca92180d4500500741d4a40b6006603a50001ca020342142541c4070369481706400000d1f0000c18118554010000c61011410800c45cbe4101040c080102004228400e80444482d400f09281c41009241603040014a80000015406c04030541c0e001074403032a01e4000c0e059034020594106511240001842200c03013030400a180920010415140c20b150344401495252098000003404500700c00f0008011400042903150ac83c0c0040c1800c101c80740c1d590342d0341c0b4140b94449042901040200c4c8102c11940380c001d01c1298080842601c500721309050180391341d5207c8000354602505803a9034010218640301e00d01d51082c0a40c00b0011000a0400000160132100d0300041070b00040c1d2204c01c001003800c000d014142c01460200342806094451034682c02c2103200d1064011121031b24800511000e40303551 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 532606456 1250 532605206 532605263
    0x611161209090b010503040f06060b0a050d05090a02150a02011103160305060909100b0f150406030b090c09010e0d0507061805030d09060f0c0c060309050d17070507 72
    0xc45003040d014068440107024520250007000d01140b6004445050ba60801d040341c2c0c0040c1c11142c840c003a46028078100300540825000710408910200c0c0c2200300681000c00f62210001564081c00103503681902c00c0d81c4c6010280000c0d51207036008080d54602d00d100c030018150020507100100b02030315a0002981154000c1e5000074001031103560304030100ba418450380360060030440c0ca04040e428299081b0f69a0554040b8207400b850b5a00402e2000c3d9503540c8118404450103450b0b00ca040d0b00344d0050711580c1d0014420000480e080141c142224903040c4a00340c4140c0c1e012045a0910110302d00449442d07414140d2140c12500190044c00821400c0048a0042c1644e81c0d0302c0d5078041c06000380007145c0e4203907803002d0301941c4290540c1106c940c00c01c145000f91b80300e92a00c3c0c0328076070360b8003c00c40d0102107045026007070b501011000b140040c0c1c541c00026187d80203004641c11500307114011100789044900c01404245081c1c003050320240704900038005140030320204100044040f10100b0740d030071907 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 532607706 1250 532606456 532606463
    0x105010608060f0906010206061302042102090714030c03270715181502030d2301050f0d0308070507021201151710150806100618060903061116 63
    0x300140b61800d100042c11881e82518600c240d4107004001030b43d501c00107003006101d40c800c800820406201941a94000d00e0700d560701c2c0d884000150b54080c000d03180790806a008400c540000780527603018101031a00020480b140900e56540d508a20405800c041d058014a03268124a891145180c1a0510b00f068242c000350180d140340460303000801c00c03a140680c0c180a06c0403c8003145152461503103045a48525440041110100c3c3c100d0461045c00e10011000745441400101600800750540c5a511260024a0540d032a14100440707084580c1c881f661003c40505100d00107442503850681001441c103085d8100460350b40015111041d444160300641c3d56528070716926000d0842c440c0090101441c610b82101e40559244c2c1c81e5510240e50180050300c90100c41050344195004038001c180120644034181071485146600d00ca1601c0b9260024a2040b044020b009007604c4c0c3c0c004503011a100d45940500c1d65488902070022401220140c1100303004403212034010011a8608920 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 532608956 1250 532607706 532607717
    0x110706052701180206070218040303140112020f01031e090f052e05070e12060a060f150c1104020715050c03010f0303110703080d0915050903161401050106 68
    0x69000c42400c1c5061505104000c6a05082c2645000c45101252252243c2c06688555982025001156000c0800d08524200030b030301400300400e159050b03008078144c071440482902542d0380c03810010b00c0c41401042c0654400c0d24401002c5040d23010b035000a05013601c00030782c40e0380e451003014540200ca03080c100030390b001c0d090b20b40c0d1039041040c01d00002c0000c0c044560400c903034441070f03240702808003d9600588103859550000c6420359010300b01d000884c80004003042030301c6144000c1161510400e44800d801c260030660040362100c880e146100965002c100d02010310103ea4500322074440d4100d08c150f680d40d002c2c045129054469000801405004250150924405401f180211440244403085200003880103014811001e4034180031650545400400d612800081d18142070301a07100400c503030303000141640c0c0004103802032510703039010381030000f02407400314400400e40e40c04980704101500308100c14500503001102164403240548401d003042d140240445084460a80110000c03c1 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 532610206 1250 532608956 532608991
    0xb06040905100b0c0d090801110403150209190302041a10050d06090c0905090a020c03070b040204180302061b04140603070c0812011a070309271d070e160311070605 72
    0x6c2c1c0220341e5030002c00201000304004c81c1d06180d001d0b0280603500004180e07a418107600303010342805030152000344100400175200c80c038900400f41ca40043e2413004034059404c1441032480e4505580c403199a40710068140c103150700300120300701c401d40c3c00410025240d9603104004290501d17148034049000d00151104101142030104125403100002c020401e0309004010103950034501005403909680e000408040980700c9100040282280151036410212090f4181c1d06140d40021f40074095203000c5221402041071900942d041e110b81d008028131080007071031052144c20107000541d030140729441d21400c0c0c0121951404c02c02d6120a0304130304040c82d10341c018001d1502007031a9100d14080e01c3e4178246040150b0b68050042d500c00d00c02d0b480ea09040c2d9251511826111209805611001c0d07010070080c58880d2151840002e6000328071201d1254120207d4902c020000aa0089035030b00108070980c0540207080f0054003c3e194400002d000070300064000a00a0040602618601e85100c4268 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 532611456 1250 532610206 532610233
    0x507031a0c07030909150b03090106050a0501020114011e0503060c1801090e072f0105010e06120a1704030804090915020906070204050606090607030804030e01030b06040905100b0c 79
    0x104405006120814000c00c07442c00080c1d013080000d011103011400100300c000b080140c0740005481640158040075000081000c0390b5410743c040000d50701c0440d2003580d00b03510f8900481c221180b1032640385501400e0001807007641d02e442c8403011100c0c1010009407003c0d40380c102017030818a056880000e0b509002c00c002c03481c5404003a4110011000781b80554949181011010440c82d01800c001305008201c5014014401c0b03c4072042d0204105030300358144490400e220030300070712092080c60142039001c80401c0851400c42c0c4981c5481095000525150340f41d9290240d9400420841945400302007100000141c4100d010b000203001140001504117a0390905000629120349131001d51841002030320b6250f0b0f02c003810340b55500d0f01514002190b42c0e404000c1400307446001d640c076a00072030124507841010f0344031081e944a01d01c2a034600213900344110064094803000900c50341c1c003c2c001d120612010b692503000b1607100d501c1d2640b04405907910028000c0c980d000c1c01c00603245820034001490740 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 532612706 1250 532611456 532611503
    0x1011070c05010f0909020a0c140d030b090114060f090406061106090d021b0d0c26060105030304060807261b030606031b0c120310060201020901170a0603050703 70
    0x248070a0030300341c03d2103d403040000c154a0260142d526141c3c0e01203140012284070780f40c1c5141ea603601c043c1245c4085801c0340904e03542c456881c04000004c1c14448000b055040068541d8126444140e620084402030010003031117400000040841c04810721100c00e90f0340e6640a05802040d56440b545908070300c034403840e400d0002c01230070502981d0000540715152070f80015949004108106912040a034200004408000b034410181100c108800081075594500810440d207200e00c0d00664104c0085a03009500d03035109110316903060b00203210401402c1c2c002c050f0254044464500b000d44048000e860100d10b001c0482d80040d2204034500f08085611400c56210308103807041c151506502c0c040c4001007143c44010104800000b9406401c6000074603d015034400c0b41802081d00c8040908221028081e002140d20032401e102d40a00010124018400c42d100100c060392100760820f0201c403070048480018042d1011995200b00010104074180f082101641c49200f0706440712185c06440c524 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 532613956 1250 532612706 532612709
    0x402012c041d06071407060608070801231f05060703120c020109111314011512020309030909060f1503250c120e060a2c0f0409051011070c 61
    0x44941402e0000c1141000010b2a00d60000240c98111800d8003e04a1850207005004000708003505282020031b001c10003003140800d881c8038a008100c1d0010017008a14283c41100701700329407a081501040c0d40c060841400028018a9400d4116041d030f10804250980d101650030303000224000c09075160080113020f1100c01940920090000b0320352915414034140c10f0302c1c0118494a4580c0c0340c508280400d4001000403e54039141c2105581c0d2140031090b1903e40100d80c100150b4041d83c3c4111048051081d2401904001d0046041100d030310309003c1c800e00d000c0c0c9016031001c0c000325a0703c104da55940e4288502c4400000e5540c50b0b0a0040f01c9416100030980c55014200b4043c0041c074103e580040c071140140c1d0007810703000d440c8050200c160703030711028804d006030840000101850141d81015107030740d502034980c490701c1d20a91030b0715402c01007030000c10071150700c60000884e410300341ca003d801030b040c3c850150003a0f0341001c200341c402c2d4007128841c5508036000800482d080040c01000c43e000ca0 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 532615206 1250 532613956 532613981
    0xf070315030b0a0f0e030909060d140a0507050d0b0a0903110303010803040f0503030328020d050c0702010809060c0315040e010501030b0105090906041728091403011802090402012c04 80
    0x442070b801c0d0310301c0035107e000d40c0880c01d0003a4440e50000300c2a998064281d5400d030b1f040a650b002c400d403510310a50321180d0801041d101486114000176407810007907281848190424610241900c0380000d80c4003911030001c00740c04109003003c42c03800c100410300081d4020b164507801180d50b9850420380103140042c907030101c1d2082e0004d000f04440410f115948000d0b15880b5071140d0060801d8030110070090044c44101011a8546010841a00c100e10010440c8a0003602d56101c0b070707550080401c0e50f540080b01c10400110050002c680b01032002c000f28111002c0042012442d000500182402c58030260720a031084403a00b8010001400d06011840e0012560005080a0b1510380c40f8180d1004c501c1c5c0a800407003400061004950418040c12031444201c4c08058500c0f050092000700495081d00940c1c0c060361a2013459030003450144071b10300c0c0000c400c542e0b1031402d41954080052460f0020010387c10f000c80c81c007601e040c80300d020300c8085205411000e45a120120b00c81030004a82e076141e90603 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 532616456 1250 532615206 532615211
    0xf0604180c050f01110a24090309030201080c04080616030c11060112021507050c09090109050a301124060405041403070c030b0f010b030f070315030b0a0f 68
    0x901040c07010032010199882035850198909400300102c0d0444040300702080c450055007010020008086249840c4d603055604000c25281044011021107a01e03802c01008203140a0040006501802610340d02c040003801d51410207940729109d40c1000e030101d81613015415901a0405c0c03a5415118030345111a003441c0240d0300003084900103070307607c0301805213000e41e401002840045580d01c604030b103090005400b105481e001d0740d11302140c0c0d036044d0782e40703da01c6000c00100152182c1300501c0b0320380c0119040802080c10780140d0311959809030310380064241550401c441d2274170180352007020900b680965554690745009500c600d5081694442001400275540c1101c0b0000445907070005810800c00c5900190544462a0030740340c5412410307080d1014040414400f09200208418104981c012104907440790343c1c0300c99205e0300740750900428442c00303414008203c1c0190940c0c0c42c5503001c4050705000030054001e400210040d5915030040702c00002a508005038041503004401089410440030f = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 532617706 1250 532616456 532616501
    0xe0f0109090c14030102040306110d0e010e0a03050f0408010e07092f131e2103020a15090b0c041401030b0102030405100e1e01170f0402010c020111060f0604 69
    0x1299104210303807141403050400f0019200281c0c0d000c0d17044400841d8050f500f0440c89101c0ca1400116030440c103921082540341a817401c180e642b0601500c1180b00e155000703404085147ea800395400d0700107104500300d01d02e06000100e103000091007036100000181c4020401c0b130b4581075441c81503400219024410283e0510013804013052900741c070b011b2244070007000b603c5048150002181c543c15500940c8a403c40ea400e204d40003005481401c00c5d07070b031140c203281200c04102c2c41d585a07d030701d2010000c1c01a4010540d400c081100c43c025052400d06140c0045410442601e40c1c10161400703441c481044040040d04000c001200450804022420f00b000d100c0415100000703922030046124a50052400c1c2494016a92040b038100f4000000101008108a00c0203e190a00c0442c0800c00f4007040303102403038030b24104c2c0d10000346214001000030303981ca070390b034942c0116a08404000201d050000049140d41c1c40c80301030004034420091142c40c41450702e45201040103443d6540a25185d00210f03988 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 532618956 1250 532617706 532617713
    0x9050319170408071b0b041d0606040506090307030f08090405060f030606150d11070204181509061b0f02010c0c050604080c0c06040e0106030b041803030905030d060e0f010909 77
    0x540c00343d040300752240c032a150750400d40c2449801003804814841450030106618000304083c009a403050543e00400c11001e030b4416415050544120741c6c000b505100070811450254010290340c00f014042e1040343e5900da4407904c5101c824601101c00314800305030305115007014030882d0f501c010308540c00b494000706100840d8072220050800e034090401c1c0700e01008040030100441c2c280200c0f62204001400e4080300040b41500110320407442181016030074001045034075103401c0d103142c0003d21559211a04858200200380040e011501c40341c030743c1040d200110365020300310054031582d22003242d0103080c110001c0c21100041014400d100d101c1c07003282c010500009035182d00943c010000c03aa24001e55802e280380291096400c0c0d4405000500802c05076190309089040f40c1c4161418010740c201031041005403000b40c1c0e60064811111039015020078440d4000120f500e0007a41540d2074040101094800d070340d07454010340480001001400388000101a400740101f5900f2820000c0308441e54 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 532620206 1250 532618956 532618997
    0x60906180f04050c1e120601182403060b09100803180a0e0403020307051002090d021c080c01020c0708010b0619020f030304060c1b020102030301090911030109050319 73
    0x521001419141100180c00c0150400c00b140c4d40d00b10060903800e91140510351102c4002201540b81e004214036030509918080c00102d19060303c0708400a4104240802050001001d520005c8004910070002c00300c242006d00540c503018501070500842d8031001030050040203200a40312003154028071104000b5a4004010380f4081080d1034000b0100304030801c0060740d0551650082017030083c000c024003007010740000041042502c601c00760352180b51002e4420049002c3d1206003600890461052001403614044904071115486221011000592580002a0805011440c441e0f5000035012203a020070031032107000300311000003402000803060116656014114001c881031985402f207181e914020f000725840e4443c0300048907181c1c907040c20080c0107049011919000b24143d143c1c4802041000003104201e9501030300190b01d9a4a040e20300c0c1d000301070100c000d4403c04500c2e104070505540a024500c6050b01a4002710385070f00c40e02e00094460508025a0070600100b41400030800c2200c0 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 532621456 1250 532620206 532620211
    0xc050c1c050607081806103305180a14060a02100903050d060e060108010b03062206030c0501110a02041112070804050c0409031403070504050a030b06090618 69
    0x1603442024050120003406205030340d104005229006000800c04034540c4500b11520a0103814406007004180c2400d031a218201039400100e0404062024400c2e8545501c0510504103090b0030406564001d0080c4403403403901c00c05030800558002206410f4000400c2d007a1ba08500c111041c030b03540c62800d00c041070583d1258a40c2c5018100200310f0207142c60083c4034041042e00e00c00000d02081c0d1641ca40100548c0c0200b140740b0141b850200085400121709070b00714454070040e100c4040c280d0034141444090b030401801c82e41d104448507622030031403000300d5030050546030011001c10254214546030380540745582200d030401140d4641d00059401c0010f007004c0c1a50151400075181c1568007880e405849a84800b0702104400420300108680c0020801e201d10b000700180c031488143d190400040c1e455a0381c0240009180c442c5c0e080c48000ca40004507000340660500910b0955a0b0700440d54404190b8015541011102e00b0800c0b9410a2040e04e9840101140c1480000703120118203030481401 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 532622706 1250 532621456 532621459
    0x1d010c08061f0e040b0d150621050d080402190303081603020310170106050607050d0908162606010e220b0708040c0306060f030203190b0601180b04240c050c 69
    0x11000d0170100b035201c00c0d1b40c1c02d10f0780d500706510303029001d801c0340c440f00541041e100e0001210f103510403060f41501d88410300c600c00c60f401000b510001398420011035040350701074403e81e880406c1c03c000d0f020180113501100021813017a150307880c00d0b2800c81d010b000441c5200d45e00500740342c0100108004120714100350300945039448461b21040107110350540c0180b03600e030084c90300a000014108117100001848030880200c0d0755414100301c0d100c1f1f07151601e84c814000c08040100e00c2190500501c00180c40944500c01c0e40e02002108000b224070240c030703286003039026210a01c80842400706003802060040004513100d8071160040d200b60780c81c0d41e0100c4005001104000082d0003003400c10074104040c20055800000c24496107484050b170203c000d85d00c2c4002c0780700e44101c92305042c00d95840e006071840e8540016101070542d841d0001980c1c0ca9132200604030a003d0440404244000500007030001b902d004007105911036280740150340318021058030a001d002002c030b40c0e0f100054000a542682d03580 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 532623956 1250 532622706 532622711
    0x30e0d020a140c090c0403330e0c100c0b0c0702010f270602030c0d09031a06030f010e070303121e1e09060c0315060903061d010c08061f0e04 62
    0x5402c00550400384506a0030303501c00d100e101400203822000b000303001a2400b4024805040d04203404901401111303021840c00c075031000302050700c0e0515a91189241c1e0160800b601c044800c03810018820311200150640030800c1904111705001341140003d61118403428650b1515100780c001a203503808121809003000040f42e0081c1e141198164503106d6040041c217622000c2d61550b81c069180d400078517000d18107218020030b10303482c14420103005080744e070408c00c101c001c082d40a1001c1c00c07840c002000c15800d44100c84020301c0b074070024400e5000003a4a2000303420790505600c0c009040c40c90300540e171060710303041400002030b10200c140c81600e1036200510003e103800c40016000f440034001400c01182d5845d1007485820b02c030031504035004286140c1d40070841f100206041e02c1e01c41c2c000340107520019040c40028000205694040103140352004900c1c00e181aa01440c2800e40310700155000001d440c00040c000142050080c004a180c841e244540c6003201102006192284100c0d00900c01c58 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 532625206 1250 532623956 532623983
    0x5061804020625060c0e0d030c060b0f1c0320101d100506040507170a0203071b050d080702010507140f07050d020607320306040b0a090903030e0d020a 66
    0xb501d40c81c040001c4002403003c4034521080c00d04000506902041c200800d0404000300f0307041c50403c00018220f40d158480e03c08150a6880b10001020355a402d60b81041d114880c07480e081c4c3c0c0d80504c0c020301e144078640064a601140c41c0040564503440c0241e14602c0c10074682c05901030004c5018048806c400c0030010704100801440703040d10b1624010b014003401400480c05041e009030b000544250030503601481561110f100403a01800309215015000840d840860604419034008503007050842c070700801d00c1207041c00c482c015070740c101c0b00c11540b560220358130b03c100070342000b80c3c140d008041d40000c000c2c4d4039244c0e20241c14001c4102012800306d0000904015800d1090b042d908001e4009003114940201410081d640b0314003650000041800340421010810080e050523021042c5490a0448000c1c80302038090325400103420951700c15200e100e000c000c1d0300d5622540c0c00504c1445000320300118141006002c8a03003000c03403c1f605070071114016480d00d0300005c801d241164060510b10807007 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 532626456 1250 532625206 532625227
    0x4060c1403100e09070b041a210402040b040618090201050d0e1e07080c091e041b0806011a0f04090501180e010e10020a0e06040e0406050618040206 65
    0x320100310680101038004014042112441019030781610507440c010741d400d40301c4104481d03540010f8810028600301c1080309102440c3c2c012a116103816000d4041401c04d24a1854282c02e82c2c6042e590f101d031030052000b000254a040e00548900b5242070f5000c11000f070a1500c0f02c00305420000580d5840c0e41ca604000085920640442e4a40c0000310000c00c0100350940040e42c6444080310800041ca0b100399400411030008a00b8200700e5414000400a2400f00303000d2098880006140340604400b0112885508a0051400703220383d1081c800c1402c3c0d092000340d4080103510315004040c180e48004018090665411581c1108504600f0260303100c8902c3d48078035140b4859030300400241401c140002903440e40c0d00345c000c1c00e0407017000b030140840301e440130105080381c01c84000342480703030702071500620007480603801858aa6501c0c904480a02600070205081364056401015400c2c448000c0100f40b02d01880344e2a00100c04a503440d0f00885841c8507d41181c4024001900c02c0c1c80c00549a2030341d = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 532627706 1250 532626456 532626467
    0xa090320180a05060907020c21010f0e0601080304031509080c0709050402040f02090f1327020a05040c080a0528020901020f0d050a23070c0f12030804060c 68
    0x150100030702081921018030030507915400706440801d4800e0074200820000d1030030055081c400c0711598018841481064200640900001c1906c000c0c00b0200190242107a020f004402c0344003043c4601045e16035003407145514054059200f008650410311062002450b8014101441c40c908403010071240080d092480440c800d13155803014078803440b0350024500c5607503000305114500864041105540c000d01c00f5042e8401c10b0441c540c00070013010032140394a0208201488100008400551051445d4100c1d84941c1070b8501072810180e04c080c41411454040d00e0440905030942e02484a01c0102601034804440039100c502000c0d02c40d800142e1701c920180c2a020a0703540b2201703030214542c1c40003a40c030080d4054044a401406905d511103104080050002080d040503030f0350b1482d0800003c0c040366a0055004e0b50161901c1c03045010794124500b4001d0118a4015004852250b240105100021002d40c0c008214011310050b00700101e41c00044440d481a040303000456182d100500c101c0700c = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 532628956 1250 532627706 532627763
    0x20d08100f060f02010b010512060915041a1507080a11010906110403030813020a18090f0503030603060702010615050f120709050415241107060807080604020a0903 72
    0x40340e440080300014010b9000b9a030701e43c0406140c00030091006088011105c0e0b10403490600c010400c0903010400b1800d041d294294084103288008203404680e000160550322a1030b82c848845041d03010f040c05500d0080e5072842003c07001c00b4030600d07241160390342e00114041d10703210798107018941104440e00c11080d008422402d600a004000c1d09004110098494115000030303030000c2c4d000030018100850310207905003101d800928220a40740f80850040c1c40e142c0340c14074081c00a840da0320900c0000c0d1003416582d0b0340391150b00610f841e8070304482490311b45840100700508580c1440020000404182e900348004001d51800307070340d200311168050009101d402c20180d0340030100f000704860310358010303c10b90640d603084406101c11303104168525903000e0540102c6010641845443d0308182c080c1c1070700c1110103001d0815440f80040303211410300700301d03944c1d0010340400c00b40410052481e40c04040c2507070115040b6802c50400d44081c100501440041c00004e041100340d49440c90942001e11010a = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 532630206 1250 532628956 532628969
    0x1b010b18091f0501170a02330409050906060a0e150a0b0d06090c0507030905060706090b07030209031e0a231e100618090602040510050309120a020d0810 67
    0x1110603070341100030000c1c4024417a60300295200303c4104a03044021594a191940080881403000c0000c480f5114141038100e54030b1000c0f10300c2c201c3e03100d0780d001140a00014450032500203007600d04400a182001001801944034011000c4240109a00881090b42100d17400a43c0d1009208550204049000c1341e0440e090051022624040080d400e400160548400350810700420b84aa803080d500c500864000801262166a050045040002c06010740c0c2d805101c01080f505010340300c0c002c81110075900340d00040c0e0001210324860504100701e030902d4000704140c04818140c100031a407940c0c080000208010419000302441d05030040e949003041411074140d030860042c0caa6480e5045d000142c81071500c0c00b50000711050464184100c00456002503105030140d007035013550600800183c00112141070380bc0c0000b0600343c480204c8070b8074510081d1075045da00e0603d014442d141ca400306440501c02c0c102003101080b415408180c04108010904111809445480a01d8a43c02d425040300 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 532631456 1250 532630206 532630243
    0x1603091e0f0201200304061b0c18050c041805090715050a02010e0303010509010506071a0c031905160e0d0203030a021e0102041d04020303130801021b010b1809 70
    0x210140007025024406181c400d880307103003c2d805514945100d2055009203a040c6402c00d11080003441e0149588038071603101d00c0031580c00750800349e03a49070004449411004510ba900410b01450b040a0b124080d0080d030082509030031707d0302d002190000d4a0070040c0401207161288041049003031304020100203460700c0505a00c1c2040f404034010925040f421040c00158200f400d804c12503203020003182d0503540003500600042c1e01b88000d010f469072040c02d08481e00d0f00820500a920091108494021008010215580d09201c07804103000e4006e409007204e40f1b03142c1000e0010842402115040008003400e0030702c85110484e00003000015405400303501404001800d1252550108800020f043c80d151030103017400c00c500e559401c13070045018604000e42800301d9041d01d07180e0118907a42c45403005045038a8211a440008642c00c407a6110f022603039001304000092880222110310408050f03070081184860300030000740c0f28036100e030004015022140200300c080006001a10000c0c0010115 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 532632706 1250 532631456 532631513
    0x210c030e06150103110426030c0105010803040f05040e0a060b0d06020d020901090806010f0b07141c030b04090f0f0524071403092104050d03020102040305010507030203160309 77
    0x56038402c1c03a011540b180068941124541c040007078a040c0d6099429003454070f0304c01c1c807103200142d00e140030b52004406240300c00e002e0101000341c01d0043d24060310800028503180c034904400004c81070f540743c10a81c46607040114000b07a003100000c0109900e80c120310007250500120703022440c2c403c0c581d2000340086000207510141c01620707400800c848030080c0e898043e000e649503000b82d241c00c4207020f029200c800c00181040418078000c00780c50882c1c0201000382404461030300c03980c64603410b1310070405162000b650b8842c13056014414403504240980d01400000070300e030f907601030320800108010903250055149000340701c403c000440da031200350010302c0b0040c03495480031540190b0440c0c4000000b50b043d80707051000c03650402a2802010300c80002c0a6548000e80c4078001004507542c110b140220a0200142560b54184100c90b02d50181d00011b81d5582541007550079504020084800d00d4010014008002500d80f803100c40302e05948ac00148003400ca00e00201040d5500c0004180442050f170b8 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 532633956 1250 532632706 532632721
    0xa052e0f06080f1006051605100504030215010b0c0a03050f04090204030c14031f0209030a08040f03110a0807030b15091e180d1d0409050606030d210c030e06 69
    0x20854003c95203020801400c0d074603440e442a03903403d240128030000d00c05101c07a0255180100e1045e61061140c406c2d03440f00840c42183d08111103003224154010303803107681e100c0c0d4640008140ba9015190542740d82e450140b808402c80da94170550362001741080400100d03041c2c0c5240b58000c3e240035080c010b20642d40c0f155a400e0141140d00e040c060310100d80b01c001040700451400003500c2c0c04040c069140d00303141c4124a00e82070000c1d004403910a0705802815243c200250380c55000b400904031059131518100e0650800c40c40080b030b07070881079009025002050103844e50000e100b0040741c0d8808594805551034003054600500580080e680041c1050184007c030811074104652941c902c810038081a51074503501c0650344c0000e00c040c43d01307070410459032031040e10454280304e00c0e06003098080200e00e20100442c1c115828002c040c5c816400c01820712590b8642030112200c0390190f494081100003012a4403104a54400200c003d4103540d2841d00f001d8030301a410440c8001030210a035120b40c90300c6207 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 532635206 1250 532633956 532633967
    0x20a0b16030f050a020601090f0b0307090e0c01020105040209060405042d02120c0d020405101e050f010c240f0f330314010b060a02010b01080a052e0f06 67
    0x300c200d021401c0400c01d0201a84a901a2294202940c1c02045a640382c85401c000074011058209102da4032601e6924441c2c80403c14107006000c0c10f02e001903400980021641042c000800050443e410b110901001d60741d000d41440e04004103c40002d500c3c1c941d1310300f48400a0b060140501d10400320300e0000250116068100305240c002d0b181190b0712024100c809480719044a0030651041501120001600f41a0302c403d03031042c00c2c241885040c81d00d56820380e0a0020758800e0000c0080b68a4081c006402c20001e10306c515074007801c101d80c06003201d541310701c1141c01c803c81060341c0f454009403090600c1c00300e400142c0c405042e040d0030030030504007050308006041a4102c0103e00b81c80f150841c0caa60402c10502c0d04445038440d00d002c03900d0700319980c2c006810306005100e1425034135620440303130550f03841004000c801015000003643c0d40c40c0d031001400c5050b0041c0340107840c9151208102440c3c0c20914607649006080c0144031a0500424414203083d00b243c0101d40a401030110100f082600007 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 532636456 1250 532635206 532635247
    0x913090c060e10140d0b0a0b0d0203010f05030d14070c030209040305030a14010602030a03051005040e150a0c0906030e07080708010e100b030a0f03030621021008040519020a0b 77
    0x82e10f01050a6481d00c600342c0741082000b2810001020070800c4542d16000f55001d4210450300411915242d40d440c0e0350b40c0e425400550361201403650001c0104515040050351100904054020304408098800b01400c048241c0c003901000c0100000c294080010112100d4003448c0e00400c060b4682c141814010700a400c00c6500c0ca000a14025031302c443c6000c1614514104c0d030710361b401189401c54071181140030700405044019940c0400d4404900c0e41c0e02c0c0e010710384442040e00010035507038000e80b00c01510464080d00c4406018981b104040720310b58403080c14400e0354028240400c050075803a0342070346005240d51000c2170703600850300086078184041d0490480814441d08480420b07100032004000c0f00d00e140e4800707500d54448844400002e600440c6aa80c103402401d00240250351243c3e04e4101c07003100302070762401c100f003400104210700d881c6414009064036032805001a14040c0e0390581c0c0c408c080c406081d8a000b1341c0200703504540d20044207402800c0f070515290b448580400b01e013000c00016 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 532637706 1250 532636456 532636459
    0x60b07020907110303071808010f0b1e010903080313060c110c0f130b0604122d050a140a0c080105010302030c090c041e05060715050a020f0913090c060e 67
    0x600100307100c07620480c409594022403002461644c0c1b106941654140f40000c400402426845000100c0307074000e02c162000c111800c10081a541102d01c10010700c0c9241108170098001404004003e41e40d100e03c480060f030380d000400e5a40d030307114200401003281010000500e1759040c00503590030b00354014410a1110f0801040390880c004140810003603418440103650802c01807000c0c4ca03480405900141405e01d005042c080c03a05072240003207400810142015100b80e03a540d415003540994408044200c40740074611040c2d140781c0d5659040d2150128130001e0401280c800d541d4841e00c07424420100200d51080400c1e0b00d0650719840c2e10301074402440268424040c10b4020f19843c180f551403a446072004503070aa1500307082c001c004007000d8081d1469030f850603242402103000e031600c80050001a010300c000b90310000d84500d0b000191a801000103030a20b00500c076201c94500031009880c1c62010495080185001c801c14a0340249268035000d400c10000420008000ba000302105003203840 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 532638956 1250 532637706 532637719
    0x1d0f0301050a090c090209060313020109031704060e0a0503031204020a0f1d010e0907061b06050f1023090c131203020d02030304020a050f031507030c02010e010b09060909010f060b0702 81
    0x35174690020403405a03162694000c81d00304001156041140c00b0f03c05618814100b0464054580e144c0c80f00401da4007160303880f080d00004091201e107800050394944040102c0e1280e00303590420300480d881c2e000e030740c03036205402003041c2c089011556200a2800900812404205240d9a03000000302000c0c4050040780320040b036900200e100200084014420307261072009001c09450081308540703a0306030110701d00c01c4500c1d210318100050240d010301d0340280640b8142240d1f82c1041d0315244449982a8030a02821074402800000501124100c0c0800102101d0038985542c40000b0380150344070b43c40415007401a010300c0810005c0d43c00ea03000750704030300a90850b4406203030300806a0396880140c4002c0c1d0700003010003040000780380080307a40c500360340c0107000e55268925849440c84080001d940303e202081c3c5980c0c60042d801c1d82407042c812040382c900c00a21180101d00302103024a48041e01041c01107410760000b81e080c44094116250b51204600301f08140d5598400b001c000f904281c0c0c0480c819030 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 532640206 1250 532638956 532638959
    0x1061e1e050909010f0e0612010603060903030902010e030a0209150111030703080103170906090d230f0d03051504022b0524010807030e210a0306060f1d0f0301050a090c 74
    0x1440c41140801ba034200c13546000450311a1420042d80032103405600640d0340d02d414002c0000740c0140603075842144a500c01140040341480090440b0140007400ca019520400142e0050307a520b901c1c0f2500a031010b042d8517448080c444c01224503240c140046000c500c4001031210805a1000302e817812a800307804412880003100885030b110b4801c18401c594000d27000d000240b61403800d440c003100c52500c5000000907401b0360004407507840f0010f5842801c03a030410460441e01480c140020918698a49001c10491424216a200710790f10851450300881d4041803d41d5141c036500c2c50750303400046201000350450307440c02d20326024220480d002908014800812801c09004600c1040f5094051b1a100255030b62040114014102d155103030f0f40702e2142a4401340e0303041d0010752003941c0030524400544e0742c50380228003a0a45956606c04020000721102c1e041240d540f08451424822082c0040082c0d0045000041c61481a1121141d410b52800041c48040c0f009540f100882070b00c155250019075 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 532641456 1250 532640206 532640219
    0x30703091a0f0f010308040501050306040204170a12210c1106040506150d0209191508030d0e0f1e01090b090a051006060c08091203031807090501061e1e05090901 71
    0x43d80a1000611490301400248400c0d80a20702a6a21140280006050541e07038041181c0e103000840d400c40306600a650302c2820710001340c1500070440c0322820003800ca124505401003490840c40d0b040b18540b907075040441c1a4510600042031003e0400084031000e05250600c1d907250081542c80040031a030070306401001d420079690360840c5507002031100c1741959603180c0c4010000f4110a8440c45030355900225076503600441410f8002d0f0407a100250b8490303c1500842d021185865450340d8542d00141c0341000503000001d4042e07441070030011045541d00200c80050142100c180000d20402c15103041007404040090741d201803074002c1d030071150500007180914048480c240144000100ea000c00c070008078990900405d5148409130240c00c0081c2c40d103066600303581081c0d4480b1000e80548015440300c5c0800c1106038082d04c515101082503506d0010302404001c401c080d00b0a50f0603000b5a0704021500940b0003c15020449034900c0100c0a0745a004204c1e5011200760752003640071800100d4035 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 532642706 1250 532641456 532641481
    0x708060312042304020a0e030606040b092d07030b0f010f05041a040506030a0603021509180a2a120537060b04031a0f0705030703091a0f 60
    0x10303441140c082c6010708040801091030100070803803040308002e000141d00381e1103030303c024902020f4680e2004108007402c1d04050130560098070b0fa5114600700112001a56240c1c41d86034ac004c5560100d080514000c51445110904c40c10303034000624030a10200203100e505500003003141e403822107040122480324001500c0641b08010070200141d014402408440340c1100c0d801e50706503074000c00c9420240c1d581e0003c0c4c0198011200e089041c4e403140300c00c0086003040c112082c01c5101c92075149060039440b801081014605a01e19118005004003103a140c0007540d00501080d4041826808035040030f410780152070b611285841c0002e84c2d400000380041c412845454020030880f07904404500401c100280c0402c40c03924200b40381036049156480f0a296403241070300500b14610559141c03403450030031001d400101081d40c140c210402c01001480c44103c12503591089081c00c0c41512a1107070304088004040e4001c00421b40d40b0300ca500c2c14001d100d04164548a4a02c5900f00e11113a03580c0c4601051 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 532643956 1250 532642706 532642723
    0x1a15070c0608100305070b0408160602030306060a0e030624011b020f010908060106030e070603021903110906120a06050406051c051504110a050109060e040905010b09090607080603 79
    0x20010310900c0c01e000c41c0340b05078034403500030f101d2006550505450f512414240002a40316200d0002c000500300709400c01800316400414900c546040340a24080e0b000e500e03844010030045c420440011101e020314054036803000d42400103402c60368a49010340d20f0f000402000760b9540c09400032151450395661003082c0b4907401c0e1400c2540e481b5004007542c2032000c44080c12402e1414404502004103030000304101940c020301c2c6a581c0402c6030103800100606091464104038101401000310f0348000b1100108082c185910f45400181c24a039107500300003a005a039544c1c0c0e0f00520001d0302c00032107a5110314030b60141d209150100900d40c0d40704104421a00140b265940180840000d003010152004c0c0e0403c0b4603011300241e90711040d104070180032007002164125444082030326401c0e164108520010090207003803c180c0c001c142080c00103461101c03000c601520840d1102d00010810100b0b41042d0034604015210000c5414200450b03230b121082150403400003440800040d1440c980041c0828 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 532645206 1250 532643956 532643963
    0x6060309190204090609200603010f060503040c0506272e0c021012051005131806020304080c1009020603040b0601021606030515040608120a0c061a1507 67
    0x82641c941c4000700300603841e84005903485030f601c0060b82c2c00304465009104115100303403004030301401c90121040c0c1c1c020344540c40038081c900a01c014040460410200c8080d02c41c9070626503140e42d26407808841c4c46140e90132054001102142c11381041c40480c0540c400071030440e4a003816030392410240142c1d4242c850582d03d551103ca424602601420208440307410719515002c1c580801540215150102821740d96000a03240560303826041c9051080303680041c00401001c04046c900400903404e503031100c940000c45907407044120042c80c01114078100c1980d01c424259101e25050074402c605070800200d10255000300c2a20b0004030015210b030303d03040369006001c0703402c584568484510071540140b5950551140c4805100205d40404c601802415280d60126079858056000b03820903400002e250301942c02c00c0c40502034402e010944400301f102800c1c2e940c3e21050b4421041340c1c00d600000018000c5c038901006502003045001c0b46014002c02910880c0c1104003000001d8031910400e80d015 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 532646456 1250 532645206 532645213
    0x90c0c021f050c030a08150103020c0619021c0b0406050109151209080309100605030d0203070602180d0c03060b0d110907020309040c0e0307061e050309010213091406060309 76
    0x2440c41e906050855a1480c05070700303045620342d1961440d8004441600418080420040000c08811608111480a00e02507007072040c0c0400082c0d44035406420308400b100d0411000740b40e201180d042c3c5c4d9070504074800030f00d403802d0180350350001400003500050113103040034400b10380c0c0d50065110724215080620011200c0b82845000c079000e1108500a40a2503100c84450011075600030141d4004c0740e50002038542e80d000d102601080b120b2a5000c01e0081d0403c001450000750084113a45461360014030140c0d44d6a0180d200010f02d4800420311584174400c242d401051010000020301960302c0f5120401c41e440c00002040411102c0c60340083c0707001c0a0240c2e40b9070700e0621032982c2c4d4004450f4011a403c1250391030010303041e120803005d0035001a00504812009180802c100b1005044504002000d603e0f04045250303805004103441051210001c0422100c4c5400d504840108130b0b0903d90b910066207800e4158043d26400e800125000e6100700070800d02d16020003240c0c003030598032004 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 532647706 1250 532646456 532646479
    0x91e0c1202010e1002101b0f0804060905070314060a181e0206041701111e1602030d120c0f0905040903021002190809010b0904020405090a020d0c090c0c02 68
    0x30884a8520004a0411210342c0395019280c54104c003803180b08009401070b21801903400f03034000c101c0307058480c0380e01c940411030816110180c11042401d420055850172204a035034030f0401001411408400610ba03200b442c000201303200c0041c1040e051440c2042c295445a1210503413403055414004800701041100201c04001600001004c1e00c20001060311112001e05500003840c0e581044d0f0148240b4a2141c2400c3c000c00f03000c1c451081c0f400c154950b40707410500601d0302e03c00c04020b003284840b0718080000c4d540300005050240903101c958010121101c0d41e80b06c600007460a50700c0d1646030060390600d10519161401043c0c094908072140d50349036050303450201004040c10326020250150301451505100c1201e0324002008280704101d4001302171414600001c166440003040c03680340d80d1403d15640c88550b00c0d02012a005034049a02040c952200241c1e0703400c20002d004000e5100740c4464200c0e040108a60b4040200c0fa00344500700014200014166508040b07554020b5200451401 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 532648956 1250 532647706 532647719
    0x1b04210201021c0917070f0311030a0506090a11040b010e01081008030c0d09050603040b010b090a0801091101081305060c030c1908040c0512100b0102030f0d091e0c 72
    0x11064215005104407a80c1c1c0101084020070340451450003400198804800e20001c0b4142803082a500000c0c2c0040c04440d19101d070050808000f8003008015030b420f01c490510a650801c041c0c02481d8100040e0340071070819005640e55800d10340c601325800b0461080c004040c0c40c00b4030514130021410784840d0300c403444c100d004544079400202405c42050446001191410040010b0300f5000704d03200041440700310010340600007200c140d0046104820070400c000001d00d00c444124111000c40c040709440d002180009442d411913900714651541c83e0640e0a3309010100c203098021281c2a2240d072142e032542e54996040120385035000d44603034400c0c0041030b0012050001550b00c0809078540c0b50900500441601c040116240c4c0b038000a4020400e01080c00321464018005001c229007400d01002e05000d6151a450354227514080301d41e0f01c03903c140303041c3d000f402100c1c030300e50000c030b103407a81c030414078440d0310003040d500390306407140e8001032024403801690038076a4402503080038030319120524014 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 532650206 1250 532648956 532649009
    0x90515040302160810060f080d0c0c0306140411030601050d02090402030a0f05030304170403111e0a0b0720030a12020a05070f060e01030b0a0515070f03081b04 70
    0x300220214400c590700030072143c40d10003a0002400c0100080c0c149041c207126858280e6003140c0100c9900e820340c482c104102d80000030150001d006500705208001018100f41b500402242d2010b0201070034850748078101c003003240350144141d1290f80d807402a11000411315587e4802402501d03004185504140302600d0410307030b107550080c8014200e0384141050b5643c44c0302d50500c0d140445165101006200400544101e42c0000144102c0003070b080038a10345039840510307111304c01c89002d894007000280d6501c2804c044441b901e80060080c03a07000c0e44d50303c6010501e03403040303000b960004010074458101d000125a503a03816a8010028480441507450706411640d0301141241544503182074880010020f01084005000401b0004034440c9080c0c1c0150006e00007001071810035117050b2031411140da50490348816281c084e58503c3e07003c2450312120103203110340c9101030110407040c20520201035110b00e17040d00c01d001000d07141030790940a100e440e034075000f14050f1400c90300008070307c042c841c1a01d4 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 532651456 1250 532650206 532650211
    0x50303071b0c0303030902100f080402040221010803190302281e03050703060803090a031506050301141605070503040b0904021c06080d1d09090c06030702070e0a090515 74
    0x2414410058801d5071002c41c850319507442200400d0302c4490400030761610944c1c0d2044400c160510048a01200780000c1c10100c0040000344195804034035610440d960403030b00c0d5002329121080004a503120aa11a078a4100e0200c404012031541c001c045620310a00a40e04003400312201c090240000c129408a03040a201e0407204118210556115241c810314403100009900e407000180ea050040c0001d040d03581035003140030b44e0380c800c0104060b5030308c1e40c8081000f02c0380c00035890300c6c09801010084000e4880f540c040d65042d82403901c5041030061078581c850081030f0703040700140b03810840401600e9901840303401070714540080c0403c0150090355401080d000200800c01460981c202e603100e04910940b117407459005944440a009000041007003011406090074110700b01003503010b0b001460300d21101128001c0c13075001c0200e03510311000c2000c40d4500000402898480c6483d003070080d07846642d8803903a411009150b000c41c0320f0604501c20000c0360b640003405009086e592201116110402 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 532652706 1250 532651456 532651487
    0x120201020a05030f040f1202100809070b04030b1501020c0a0909051e0102030f0105040b0f0d0c03210201050615032202040e01020903060a1b0c0503040b04090903030e0a05030307 78
    0x28458210000b40c020300c010f103031004254010b00d865034104007800802d26010b40042d544040c0000314200035941d1062081048000f514113400300e541d60300a4241002401e0380180c4600030007007800700810090341c4035903126204074440c0c0d074002480c44004a036030314610041190007994514040c80444925000b000c8100c0c054003c9640e880c110011840061a001c1021940b41e5404802c1c405000b804400c0ca50040c079040f5001e0003071602000c0041d2031400304110302c038820b1421141840810124052820095411041c0201d4100344000801c041c4a00514164015464200003078034501e0300444582c81051554003050440c1d0314040705c10024091001d0329401c6660170801780005954030b01921002a54020001d40c40e080d20100345480c08002a11aa1040d41000d0500a008011390f49501700751107580b91503404180c030350900c9130031440b882c1c2000e41042d4001501180c0c200340c6821002500b03120380e41c1003221110100b0f00c0c54580c83c0d1800000c0490b0401c10104241a105520300e4010703806 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 532653956 1250 532652706 532652713
    0x6020906040b040503010f050114040c030f05090d090e0405030a1d03340513050c070629010528020c1c030e150a080a0e191709090112020102 62
    0x41440000c0c0d00e6082544100e141e06000901405030f4102070062150652003110280482c0d41025a44440501c2c00d044607030080340c0d50740a4141e460311981055401032a85030042125046c030030100798803942143c0c11003021075020000020303600341d056805031196030410050750500c042d20f0f50864920240c0c00c04526070409410003a2060365003031001e8140d003007001c0c070600c0000c4114001620ba03220415154502c1e0200804200903603190040040702c90001034a0004a0340c0d40c04032558031600441e2000350000307140c0041c0510004040c5542100343c8200a500103544035054011502c0e48240d600e0750f074412190300203900b1500e40085000003001c2c52070040c0d502c8000c0c0e440c045654110341402e4205c0042480d11403e00b80758001c00392480da843e00b6501d002038070119a2210314684204900d59040005540000700b0302d000c107605c003a5040131340c3d5081d10042000c1e4001e006150400000540704022100301c8091442420320481c0c0e05440082c0410310960300e440408080106030302020b905500 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 532655206 1250 532653956 532653967
    0x42c07080c0f0313080c06040507050a080304140301090f05010218100c031119060b0f01030b09040b06040615120f020406090302011211030f181f020d0e030408030903010f050402060301060c0602 85
    0x8110070046d18002c488100104568541400c005140100e6a40028001c5000c1c1c5001e005210002c000c0b2020745111503001d60801030364402190041416440c06803003034144401c0e40c07040040c190014078143d10740302d00469044e050342d020450912015440ca4003c03444840d141000203003c1d10000c83c0103582c0f0300644090b1641044131424480301c10908a900c66a174620b5201a4a070001c8072001d000420b20301004500e00800101e0078100d0054400343c41c00d03505d44005640f6585a8000101804d6183c03204040c0411503640507200c03041c40051810824200745440200b08490320a440131105641c2d0390a1441d0f240d42c0040d200c0003059020f900c09551a021a4540307041c40381d000390f0003158416103c05680c68002c043c54001c00c07190a2000040c0c0142c6031000c0e044446402d440e10192907080700598848400001100801021410515500021400007a0a40080040d00b40c940c006c2d4020700c180030404c5003100803600101e800070b500040c140014060b552240b000049203038400c900040c5083e = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 532656456 1250 532655206 532655213
    0x61c03030e0f07050a0806130b0a020d020a08150f0a290a081b04030c0e0601120e0610080712080906041e031202010203150f0105042c07080c0f0313 65
    0x80041001040c2c03907000c1c0a0800c0079003001800d01c1c0c02404600054a0f042c186195080c40c00d00c011080602001001c0000c69110200c0742e048414400100c201156a1007612002400c85d0200b11641c1c005c0c1002c4401d8410b441c140b03041c4021400c0401440009264189507401258002031202e00c01c00c002c0d43e1410480a071031580042c80c04600035220442149001c48080c5c0e0301c0c0ca41800c0b840f032443c106000c01c1001071481c06500301030b41c01c03540b600361039a540c05004a07000d04036020f280c0038050030120224125080403c103240a0081da800944200d0340710504a6940c1003144903510102800c841e0082c041028840a4121440e006003000d20303050f40e600203490a0002c0480051826040c481c0420801400a45110550b07090f030000b0760a42c5800741003004036414401485d401416110100107090f072040040710060541402010b08091064851445045103051041e030300400310404606450f005000304d5225a201305011841c02070034504400040e00b0150280d070350340c0801d1702ea10000 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 532657706 1250 532656456 532656463
    0xc16061205130f0b131703060a06140441150405061c0b12010606030b09061f120c0302070c0806012313090b09010605040e0703081305060c03130509061c03030e 70
    0x1182d006d1540c164482c2805002c11000c20300a40c8a04140010060340072500c2c041e00043d08d085800c0c2c020300c0135508842d203404810b481c94400d2005500d60074031441400c9004200071004201d9020f40e98410400281045040c8911641c02065032055092201401718002e66101055020200c440802e001c440d41c00420248400050801c2c0e43c2c0e5111002030282507414400e91a03003181c1181d100c0101c2c1002004100d0383c00b503411001e4001140c40d861400038600604002d68a02c403c0c9070100041b100e01c3c1401002508195030868880c08585800203c565000800c6d5060302c091908681400d19510303078001c0c050222196054001d90380d200343d0040e64800744034103c03146019402c50059490210701d4039084407502d4204900c01e518000e0300704c1c101d0000081400070380f85d020300702c995520440d200c1c2d0000311100740d02669200c036000888580b0f031400403014200a03840b640d024a80d4640311410000540c0007100c0031a04030760120034400e0644400c481e050559406414005859000400954103 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 532658956 1250 532657706 532657733
    0x40e0f1e15090c1815060712030e0c0909010c18030b07080a0e01050a2f09150c0703050a0c0608070e1309021315060c020f060c16061205130f0b13 64
    0x2041c4c10351041100c20070b540b14101c81c091504a403120318000e440d0b076800050030001d05800f81050303070380c004c90702d601d000c1001b18002c01d5000601c11070240c5054203015028222100b4003100156031510140d01103043c07914088140d03940b010010b4403e9540c46421141401c1c000c098603282074958882089425007031080314004c61700c4010100b402d079032840400c8101c4043d0000b814030318140e0300c2e00345241c50048059070603802c0d0031102a400143c0441c032300303103050090513500c89035801404000410000c0004111541520548400c6d8034156541c0060303400309000c50b032038800b040f2542010201464a02c1c03041c61048007801001568440d107070081180408802e01c0520090742d11110440c10a40030000d400003032981d46481041a02268045070f00c048811040501805012610000c1320000340120310480005050183c1389980d03801006007240c04182c03074166144d20b0500072404107111400d0862007950448210106400c2d940e64030b10048100030300344480008071b8020100001d1540d6980340 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 532660206 1250 532658956 532658989
    0x1a09100e07050f010e01090603020a050c070f260a0b04020d080a09090f0204060507060f1b0c2d150b131e0204180504020609040e0f1e15090c 62
    0xc80075041c54148030002e40c0d070034682810301c068400346400aa034803c00c035400381c803014500907842e9000301d03200352541d00505405070780324080c80002040d5515401220740882d120024032031420000411841e5030003403c2001a8500d811202c900d001240c02031141c0d5030020720283c040c445e00301964031142c00c640c06c50a541c10000b100d0301c04c104460300490091038892100240d0461a1a1601c070000d0f10700d201d19100185065100c209101044401c1c0d4092171a4842134646a800c079446013000811001c00150221620070303c031030303201b059071a080309002c40104485016180d151181e403102d201e000c0724105410031440e200c01d00581d59458046480c41c100d100c580020800e0040b040741d0ba0788842107450500c60f21881404100111140421b96409100e40c1d803d00082503200c900100e03c651003200d04254100f400e0a941d03400701d000014034444095a040c054400a0300d100d40c00070318581050703614002592100342c004115080c165600c3d83c000039442d0840e0070192140703001c550700751a11010300 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 532661456 1250 532660206 532660213
    0x17070309050607091d130b04260307080601110a050d0c060e06060d030c031211030105130e2505031207030f0c02060a21091506060206041a09100e 64
    0xc00300309040040c00d030031850030704000c02c8a50400b4213401104441244100d00c0c0384884012800d0701c1e6981a12030603032500a80088602d20300b03804c048195044655402103c000724528202c40c40c0b40f20000c0e240151055600c0b07114a40302e03840115241e001240c241d003c41d00603000c6017000107030b0401903d104031070741c2c1c0c2f55001e400c1e400b400c0420880340130382d60041040d0403035030800540d60f139500d208480090345828003880300651420100c900725140c4150f1006245000c90504855207000091412a4801c442640010340300b01c1c145400d03a403002102c01040e0b1710034500c04000801c0c03c50300540400143d2010300c001580d07440020b04c1e0151150031101c480c90002100014140d00c40180c58801e401410310034401c20303896010507228469038201c0c40070407210b150101720b9001424003070109c503d4600340138440e17103109040c60480d09c110306400c210040d21702140025118004107503140702c0c5801c107030010350507480000070b029004e000a1000f00203000358400c58012030403610908080b4007019004 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 532662706 1250 532661456 532661471
    0x209030f0601180608060c070807060501080a11031b0f030a06050c0a0806150d0c17070f02060603070509161106070e0a1212030f1e140a060b0301030b07170703 70
    0x3521854400202c2c00d403d803410503200f030201060001e61507400c007030461000e81e91003072141818074079400703491801024141010000039107110005600f80541e4003924000c20915405001c2543d00d00681042840035016140c0c00781c25883c04020a00c032010018041e030b144284c40b1f030399a40403200b0841d001121064086145101c0c254400c2300564003210a0344c2481d41c010191620b55002d029501d00e001c1a903807a5400b0488203840b541c0d5200e0790541c0c41103441070303500308004e014184014209106d001442070600080342c500d0000307a03450481d0806010154140c46101080c06a82c0507148a00b040c40b0500c0c403413601c6504100b0a4034402c498036075451141014480401200c602c0343e9000d0b005000d50607a08201003040e80c507410311701031550b0034005001d60b0b901941c100604240899891703100c1c43c1c114900d0914041c1e401844031040110044d00d000d60712105060100c5241e40582540304200b0700051000030070005009410908500b0042c29122103180c00c0f440c451421030702080080d840c1c001 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 532663956 1250 532662706 532662719
    0x108150d260714010207050604170403060507020d120203010b0403030509120706090e0f150103020a0e150703080a050709050d030e0a0b04030302010b0f1318020909030a1202090a0308030a0209030f0601 88
    0xe00400c6200c5a0005e601c0d1143d20f403280360341c1d414090005450401c0b11420500a0039001084500030b55014100740301d14541400042e4480c40503041c0e56000c58041540908190f03000e20890f41aa00b9015a040c05c20707055032022240f64000c4584540c10910003200d801101508100780c0c4010b200703507600c0400d102d0034a145406100790103045101d1311030f020b10500c88500032006084540308001c1ca00161542d044800c02ca0303940c0c244400e600d401c070314a0b028500024102e2001011414000e484000c803176103620741c4020807501c3c11180b40000843c100f80c01d0015151540060313000728000d01d8080004492000000c040e152680d00a400311580045d0400416030203005980b0100d1084034210554000000450200092074010444895035121844081014042c0480989402400b619114600307260350720303920303070008401c0408550420560790f24030156000b00d40d6030f0790001e0b00d901d030014078682c1c905100d41c00140520000580138001e580305601c0400c0307400d04644240307000300141d515141 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 532665206 1250 532663956 532663973
    0x1090b1003020a080112050a140618070308190504090618060b03251b0c0914090a0b060a031a07200601030206160c09060e060108150d2607 61
    0x80003203080c1030060000a188542000005044a200c5100c54019282c1807404604100c0030040042200c0c40100035001103ca0019a00d440344424a020612140c0d5248010313940740c102d44401040b0b600100800540030141000411505259082c054145900c50343d8010641d0215001400030207181000300c60f200107070b405104001c054035284103145007050030040741141c08034419403036044013201800c00d01e20f2154100c4850360011300f44d4070a03400564900804210b4103481100603c90800040424100340d22032201e011b05100002081d5a501543e039215556034000c1803180d228110150000118004600c440421240504500e0144c030780103002500c400305007115407030359850310b00300440011400602241502d4040710301e2511004168084a0404603400c00240301307820304a4001101d90300c0760840001e403008150705850540e102e600441e51044119a400c80000008809140300e0030620503c2d0002400786040200358289500034109401d8003240e8894038850000e4988240103419 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 532666456 1250 532665206 532665229
    0xf030c0b0a0204240225030c05060f03070c0c0f080a05010f200d020702150c010f0b1003051f151803050d050f0903120405090a0b0121020f0301090b 65
    0x1d00341141060b06204010705540b910300d003000003484012007031011460080003003043d42c4000c0e02d082d02016101c0c440a042c581d001d0710045404100c10a80468540381000a40311640d0003603c1190655541100440d6804040001078841000a400210703582d040c0d980d6031409001128003d190030300d0b00f480c10b01e00b11546000390507170451401100007030800701054170b05104100401c03035540710030644640034000e110351840298090700c2a14035500d10f15611002d0b107c0061008003c02507041010140d4087d1030b036540c002940800026a42131003503000b90b12158101c1c0440790b40750119211032450020721a45500103030481c0c034032040c1003001e07168450418a800a040540703a0509803559440d2035981c41190380120620001195003840303111548255030482130014100c1c1e1b1010551010130740994018000c0314050b03203035400001c0316101e40e805004d0b1040c5c81a542ca00d038040c01c4a00d41c40110401a50088040b40c00700491000000d0324030103035011b40851080042c050030000100202c1c000007 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 532667706 1250 532666456 532666471
    0xc020c040507080105010c140d03060513050f01090c05070609060b190b0a0e15070f060c1d040c030b0a170f1f020904020f03040302161403060415090f030c0b 69
    0x1004200081c2560040d00c0504445c000e007070807461000c0341d24010f0350a50b82c3c049400b1841c07150803488003025a141e04220112502641d0160064070300d01485d50940b07104640060070f6440046c01007003100065403040907980981e14055040000300e5680e281500c0e002e040589409884070111078203440c101c0d0810b10f0b1780c0c0362000c42070007091424800c4640e901581600e0700c1805000201c44a4a407503003051408104520003160341da420b180c0c86c2054591040306d006441961510f80017190240c001c090001520b0348214450a044502c0003c0001a20704c041720403007003640322184907440e40c80382c01c811409886102c07030070801c1e02d07480d005003446c10500f44901c03d850342c041c444400b240100d90110200a205032040903075280c03402d0001c9400ba102d05034008000c4080007007084149a80400d0038190090580c40c45400f8503620300c4a10326002d00e640e086981600301c070001c980014920380c401030481d100035070b010a9040040e01d924221343c1082205038041941c0c0d1400c0010408140102a8007181 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 532668956 1250 532667706 532667711
    0x70b07080910031a010c0b0610020705060c06091e0a0f151a03010f09031d1c0305130b0c0309060706060302040204060f030c0302030f280609090303060803040b0f0f07050102030a0c020c04 82
    0xa5034980c5004640060b19289c050040000103c0019100788030a501401b40501010303584c00c505503445695030011076080e80e2a0240410620004541c0550518844801c90003840d002031107850300e0b00082d040324001c071407100c1a10741000240074240510b8044042c0039800c0d401d01303031080041c542902d49014040900d00e02e01400c000000b900704221f40001441508271080401182c0d0220307244c1100403040780441c3e8500400c400030581d000e0014070b481072647c0307100020242d5411501802e4010150100200d400a00101401d8180360300a00b0805000d101e01050090b036030340200b01281d0040c0c0200380010300c01c40000324615018011004100c24602e0300b14910b16014190300c0010720013511a0b50082504d00000c6243c00d04010503040c01d1b030300103100700b2000d59102105c00003000030000440111741441c0000541c1800801a04c08642d0030b407a80d9403901303003800b100c990b240e8050000050014024000400407850902c082c41c824008003c2c001804040f0040c013a242041002742c46110b90b0 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 532670206 1250 532668956 532668977
    0xf1106040f0b07030b060d02040918080a050a02101a030d09031e02010e040f0b1302030f0c030603330109020a1e03020c1c0818070b07080910031a01 65
    0x1c00c090a0034103010780012402005031101602280070f0003107502003a501c418007050100030700819034002d1040303d2031172204010010500702c40d4a0f0b02c5141444c043c00856040c04140e03451030050004001c9403c4074410713544002c035121500c40031541001e42171601c40d075000200840c2d5048c200042d54141c266420468102461980c5050f259001b050100c10341c01400c0003250700716400b4166405450600a2051000202e1418504018240303121070510421a00c0c80b00c4200088501c2220702403000c240b80c4000c00d5407014051220b50b440548600d4041c800d407080010440b8001d0b104400c100460b1001c0d03000003801000f08904204181c21046000e84100580c01e07002e03070852032900c074540a01c07a01844850500c0030035002400fa60b141682c850060002c80125009414100c085a00540d121514070b1b407514409035102000c001008581680819401e1080b4000440600600751090510341d140101a10104007400c0040140b4000320f510759558020340c1c410401d030301d0101d130000e20748400b100 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 532671456 1250 532670206 532670213
    0x6050f090a08090607022e0305070c1a06030a02090c0307080106090e060904030e03011a12240c1c0b0a08010b030703060e070504061e060c020105370f110604 69
    0xd103c0d14000c81c1c820440090700d40115140c80c0c5005942c503d000080301d000004501c031040c2c054418044203c0004e1a0030005950103019100c0110340603040b40e2094031081413184103a01c00000900119030512030f404140700103035107000896105542d404c020302c3c0c590800c160b020340200d0068001c5018000031000500c00d82441c000d15903070210040711848450344a0782000e880c080703050802c51f505035003020311a0387d00f00840d0000c0103840c0000d0f00d004c00da038140d02603207075154810000e201483c40e0034003103a503c8417907801002c03039008a105072005250200c0042d256089015644a00c1c210584411030008035281400450000f000304000034030000e111703400003c1d250320450000410b030950b102040c1e14505400c00488000d440060020040152903980416142c14600c0f2407100c400040355000c2842440394074203504080e811b8542508011501e020b04502d00007003504040e083d0180d111018020300018024201499503840f0b071082c41803001002400c1e1003449468400f168000001e02000 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 532672706 1250 532671456 532671473
    0x1603020d181d1008030a170a1103010e0405030c160608161407030c020307081f0204180c05070c030b1b0424020313470903010b0d06050f090a 62
    0x601c000810419a5a01d03010007403d44840c1e00b161000384004035000b64103e80118291f2007030710079503800100d607a441c01c07200303c165412903580040c00071060004002404480718041d400c544110166414101d1600340c80307140c5606071201c403551000303c0301c0806c280c9801c81003907030300004d072405038030749035035500002030440c80d0942c0c514903405034001520002e052288c0610106075900806950210703030790300c24440d07850815001d620180c400c40043c1540c8040c5078801c0702c0c215000e861034448000c03007204d40d601c003e1900d54588400d000e010015400001d040001410140d0310950900080382040e08000042290380542502c04a070100000d01480c115000b51004100f02036014110145500c08100d055014411119045a803008000f24641c146040d2144078051074010030b04c262402c0c0a03240c4032009140c0b00302c00742c910b00702c0710b6072601001c09401440d0b200030290000c00d071202500081104035090a0f0705580031a0740780140b000140400c0c5d903668008032010002c00c6041019202d8491 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 532673956 1250 532672706 532672739
    0x40b120f06190302150c060903040e071b060c14070c0806090a110909010e07090501081204290c0f0a02030f010b010210150506030108010207060c0212041a1603020d18 73
    0x3045d018204410910380b0f006003100d29001149064540508103500100e9881e0401d00580b0b402d29010030001e6a014480d0120310042c1000000ca10b00d204000d4039840018002030010104103c60550206001c4010380c004000d02072003410040d920034a0140c1d03c4c2e08152000c0c0c940900d40e04030710034160101e161148003201520040714803d1240e1a02d07010f4500400408503055002d00900000107a852543d500060494480d001540d2070b00040c121f103180700d44158090418a4400c002c42c0305201c3d191200c00582e041031801c2c1c2030740380050704506685800c0742c070301c2c0814255204020b078004504050001d0341000c42140000d020003144000080d450310552102010200d40e07510782d44502d90000c1c07810340014407010380840c5c0e032961110b040301d020394403000341550164100701c203012019200203082811711146405d001c0c1030908042c0d280d00380c1c469001350301c11522002c1c8460112104000c20780d004180c820340041141d0f001c101c101800e0145140401c17030790040e860034200a400c0c0f040ba510784 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 532675206 1250 532673956 532673959
    0x9010b0f2a0604050d090602010c08070c02030c0306090a0c08120702010c05010209090f04020325060507151a03060a1e1824111309020a05040b120f06190302 69
    0x807162450003021180d001000451080d0310301c0794030140000e200d8040352141c06281c20f036681c200d08a0b11074006900f40c804004254001421002c00208954415018107962910040543d0032011101000034502441500c3c5c242550300075402d20803c01030b5100c4801c000344003010280100488458ae1001180200c1d0006814041c14030b042404000c4298100c800700000180190b0081c1011040115510800c55049000f44a1440000b11500b003104020601500c002c0132501d0711030410740c04603641c1d08960011113181504c02c0b0491050b0005005400e6020a650b400340e40e035220540c100340c40d01c84094a40d0f03140e01d107010701414030600c4408204841f00002000854030f24643ca5240c520960030684c06041e210100003031400c50340b0183c03012002025075100502107000c1030400881d0034070070b00340400c9004100c03c0b010403a02c200c94000d80042c51181c02c1690403e540c891000c5101c0c0c1c40f00c0441c0e40254403003001c1109204203444c0c0c540c0c0000f8160748d0a004015071030a84c48001c1c2d081d02029 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 532676456 1250 532675206 532675237
    0x2c03130f15030b0a03060612030e010e0d1b0807080c030c06040806070c14010c03050708090c01082409070c061802011b230307020a050306070f0815150909010b0f 71
    0x110319913100d05114400469100354104000d903520031381000110342da04011400121144c020054030340c464400140e02c144003c002c0d05031160070b40e40302074010445040f01c1507100c14080c0c1c0000e04d144284040030050081401914440c0d40c0841094205040e040050344a90400c2c4014442d04000090441e44070190b4245003010003140d05290f515296402d644107555130a1060321090603a047c0c0180303003d844191200f44150300e88030078040d221030011080f24001118140090360030000400072800c406a903125203014422810040785404000f164404042000d141443c810403245220701400d005400d019842103061542c00249221911103400441e800390724003c201303009804000440c18000c1003003049120084880703079a101c0c0c1250006038441c420f401e00005840c18041541d61080c205039603520000802004151690030024100307400300c4050b5142c0518649882040c030b03002411540031552203540c0320b0200519071405070040108500107105529940f2064400d95170b24207405507a0 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 532677706 1250 532676456 532676471
    0x7060215130302031c06031e060e1c05180306010308070b091b12010e01150513020702060306060c0a08040b0c0f070605090d02031f0606110303070203030a2c03130f1503 74
    0x1c030000390a850b00080d040ea16980c6030340b0308c078003419048264058460082403020621035088903031a859000a0204e84007151250301080c20304c030300024103500d481000b03e05255020030011902c2d0000c240c10481e0003000000d040740a119941d800c01c1d6008400c90018072074418602240c200401c0720741c9415000d08100d10b4031881c402020742044c2410203994000304840c1013409a0581c0000c454030034103000d44010f060140c551100c600899620f82e4015103410b00c0d60300c9170002d0004036402108121074a010710002d03440001c10170b400805c000c02d40805d155490313160500c58941404503d000c800d050390312403a42004904d8210b0240c03029030400300d41d9094040340500129003058914407075441d80782070700c054003c840380165200e42c00740c1b00c103aa5000b4408464a03c255940e01c020b40b4110090317841800060744007007142d048400078062030605003102000c0f100b0181d0003030482100800f01a0408140381910b171032145d0340d24005014204007103444914010310a00c50407402c1d0003107810103448824 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 532678956 1250 532677706 532677757
    0xf19092a0e060f1b0322030803040f050709060305030307080601020a030e01030e0312010f091118040b011103160b070c02210a0210122027030706021513030203 70
    0x21340f900c42c0e12284149038580e444018a40e202d900c07809841a03e04504440c0c6064241d54061b041c080c0c1c0d502060652464a0701c0c1c4034900302d202c0e504001c07103ca1091b0b92001c52054a54002e80d0011403181000755100c1c2020070010700302d0100101580d0442d400009000e0200785d00924841c1409428240080c4400b065050035041d84a00c18200300d0500b02c002c000a0100303401250f41084940c00982005041340141d0740000c184513800029413980b002001e50030b03031482d15a1082032810b03014140217a0104940c0380007411500521007020344641c5043c006402c0c44940020280d015a1514140c0f145028550006241d1f132a0190800c0418410280d2180302c0907080004401c0b258006081000d04c2c121140004c1810300c1030244000e07000e0078140003080352801c5885002d95540c0202030f00b4204201252858a40c515005140100480040210090340c070140034a9020340701e00e9000e014038218507910f91803800c501519616405c030400d0040c40201e5408010b540200b41c807a40040c0c03806074801c0 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 532680206 1250 532678956 532678987
    0x1051602040b2e0203270d0f0b100602010506100509030c0303030f041b2612040f09061a070f0c05180f090109030207050f19092a0e06 59
    0x255120703080390700c584030000e900070020503980c00038451080c420100f2101d80c1c0f049031a406103441c54002c0c0c40e601c0541d200c6a0100c0c104028008801800d04900003046890700003c48230b05210643e11f5000034810b12280c000030070650406040e450001380001e044c02c5000c80c0f003600206403200100040072402d8a01e0740e07400d05c0200e105100080440c7d07242d00340254240900c081c00e40b800c5441c2000c0c00385000704035644031100422528121620144035564500124036140c603000143c02c82e001e0b19003404d850305940000b420181c11040c0f6900c00c003505000740071048440640080820b400010700400d098120b51003119141503110071001302a07100303840c01441810403034100700d0f401000788a8003003c0340302030b0045c070788200c0c104401030507180ca44400c82402c842100c00090010380182405002c02d061900c82d01c00c100501070461010721130140c0b4002c40002c065080f08040b00e4403101c444100740c1c80e0403d1564070080195110001c0b03c4214030180103030f110f40c00b40a02803000822081d15009054 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 532681456 1250 532680206 532680221
    0xd0518030304090b0913030c080c010e100605010216051f050d0f02031005060c0604060c0c02040609060317030f0708060d0807050d320708070c030f020f040504020105160204 76
    0x103001c50703884903140c41c60b05000d000d1315502140210b034581d0008008883e040042e50015806803214440c009440c0c035840314a5028034460600b56403581c030424600002040612100802c4150000d041c2c0c0c2081c000905010300c98882051040034000c060103140e0711941c8203d0340342460440e0100d030042004050b1482c0c010340306070b000c0c298546580b400d10b40c02d160700114495220350502d014a541c0340d004120042c041d000c1904019802000010000b584079881381144044c0e42c01c2400116500341c0c00034041c1e0701e0a800c5040e409480b11b408100300b05800301e41514059603900814114680702100b00b900c2d00c0c00601a108005210010074001c0d01c91f481e0608604d81c100c1200c2e50344800d01c0c20000e68916122105000051505920135032100c80e045d6105c2c052241485554010228030b00807502e990071400c0700382c078039a1003000385000180c1e0703582c170780ea001314450041194003e90500400401044010300136000f14141001c000c0141e90007022100044084901c80100c4081030000c600103210340c = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 532682706 1250 532681456 532681459
    0x2160203030a09050a060f0e0910170313060e1e2205060a08010203092505060a0f08090102090607060f0f0e030c010f0b090612150c07050c030f0d0518 66
    0xb01c04216a81c040c1c0340f0b4080c4d034400d4030b84020455996004403440b200c107401c070000007003151000500d0303442e003240c195411841003018090310302d45806240c1004516010604c100b640f00003010080712410180b010000c04071410681c6824009a0119001c1c2c4002c12a60010070700d100040702c000e07511540302e040440c020b5441c924604c003810040c1c1005000540d21203100d0b00c049240040e403c141402242e10803d9144040d02d505420022103000f07034441a044403000c50300c0c107100840c0f0340d202d48026090025155440802c208000300001d050428041c1c41400d11703074010801241c00b52103460841d03c030164449000500c403118100000d006010032030514042c2428587c0d41e400d040750000c0641503180040c0000c2201000f042c0201c000c44e50048209a0004201d10001e6a1403030507000700541c007004082503504c906d024840c80321880108442980030284045440c0c014001e04001d03007251a002900207150002000301d01c103035140d0008d615881080800140e031404840510001e1480c0d0340e0 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 532683956 1250 532682706 532682713
    0xa120603061a03070f1a16030801030c080a03140901020118050d0f030510090b010c290f072102040905040b070311270a080f0a020307060e1302160203 66
    0xc4038074003200030b0418802e215521a550004400451402040e08002c80d00909100c0c000a80780c4189601800340f05400303c41e1404041c0070741ca01c5c80000f0101c814825120744e4070681c0544c107500c0c0c205100d0060303401400890707010440d0000000c1d046802101c030f50ac0003d841603140d04011004031702500d10200c15400250081c8411410000c0001d400c000007821501c0b01c2d0940b105050044041300c00071100280d144403911020801c030f07012548581d510b210185000759694030303d501e0380c0f603038107022a002080310081c4240c0d00042ca00090391050300142c1e8244a5101030078000f07001800c001c41010740c07010350704121b0480310f42c09a1980c100e400404601005112500d01400d144c2c9408030200c48000220781800003210b00008403c0131030f0308014070500c00080d55668012803900c01000c8501c84c5800444444e40850030303078800c0150502804100c4002d0810784080e1050505211503903101d481401078030148082c080e0741e20000c88406000ea18001619000900310340007446211440c065010300 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 532685206 1250 532683956 532683959
    0xd021308030703030e0c152d130306060501170a1113090501140402040807090c030f090602070201020c060a020c060702041d0a060b06071a040203161e050d05060c0a1206 74
    0x40e0181c11518841080c5c2040d02d1400e030b803c105100c079071003200b6421140301100308070f981da8004183d03003d01d2000c02002c4102034407060a150810059001030f44003180e411030000100100101800b62401401e020318115000714003043d16621581c1001c6c11003620180c40f40301d82c0400d4401c80003919140c2610120070000c003903070303200c00c00010042801054518410600380b0301032814140202c4045038280f100500c582441c1401010040040c10400420581c43d07078002c1f10030784440e0041c020410301a20b80186d03205034900c00a0b26002d10449000d0042000740701200285d5004500007000c40c901742c51031680c41d01a88002002084011307241241390180c6001d0b200284c0380001c80e2100703903204981c20414050101c04100c000e001d194002440360300c91099481e81c040d140707505207401c14070103404c4442d43e00112114545144a0341c000c8420720140d285010011506584140700802040c2c030496981940c1d40c0302c041e211f0400400d0000040710005203a11014803690105038050301e00ea10410802c1d = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 532686456 1250 532685206 532685213
    0x41104020307050a020105130804030b071110051603061512090c0303080403091205120a022a0406050f0f120a0615030b0a0e060411030c04320c0d0213080307 69
    0x5070013420b2128019880c08000a8079151403845050605030042212410726140d03685101040100034554000c1140b01c0d850311121400400a002078107007502400700721490a1074140404c00b4000161030209810300d0f40c20410114100c81c1004040c604d440d194000c146031501c400060150400002c000303400300392000082c035602c81d4005000b14426650702144641d43d004000d54001070060183c01508040032404022801070018a0000c0d5940140c8295042003d0140409450703061294031240d460320303090740b07545410720900d009404100c860b10400440000802d2541c129014258002e21240c00c0303100503c88100500c10866600900500042030f140c241d1b203035029502c4c4000c88554070108042072184465000c1c840c2c6c4445d08100401084c1d4a548401c00301c500c00c070100c40c0c0c050080980b40a02c94403a4068014925610031500d0b41c504035151400d0403440455040404045c52001801100e841050440700052940c0c4405600c0344042008100210000d41c0203210074800040e181042 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 532687706 1250 532686456 532686467
    0x111e030901020c09070219020a090510090f0c050d021e030403121a01080415020d0e010921050d05061306060c050606041107150f050c0c060a020f12041104020307 71
    0x1a4102039090303c42c45500141070010396002a40c498001da04480195044000904483d036072883c0020318800303c866907860480d0856409943d40c004010707680009020303002c000e0080405100741e070441080014004100102140904200e0050040d000101e0914400c26800701a0704013500d0210641c1d2401c00e4540a070550101152407480d0a00f4881c110406000c6813071005119101a112a800b81d0b440780d03112401154000104144a5421702074071070625514810701083d1040c8000010340500241080b5032600000841c035801241e043c010641a00d0703100c1e0a485078586918000b040ca5101ca0002a0b802c0d40340e0364180886900d09800001c5031a03001822940450055054407000d85640052005407581400701c800c01038800c000d028009150030070600300c000b8402c603000401200c00c084c0141594410b583d03010380480e001c540401108014044542c00160003c400c501d000900d12880b445400b42c0c0c40d84c0240d0703226040009051120412858140c0c03140100115603c0c641000301420 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 532688956 1250 532687706 532687717
    0xf0408011109060304140a200a0503121207020a02090709031a0405031b07030501060f030203070e07020a11030c2206050d02090604050417130617070c03111e03 70
    0x95030910034200800144403040360340401001d812a46950340343c5d260005450703818000c6100504c00c84034054040390807041d10011004c01c9600e8408103014110411600c081d45400c490f100c0c4d00701d01004051359101004541600044400c24a079583c0c80e00410b034280003000c5006504200380301d0810100b1603000801c1c100b030f20711038030180d6000c90007420f0b125410b902c210b9000b055980308201030701c07075500010158145882c40601721008607440e59903c50a4038519030003120200c0304000103004519081c000000036010b0b800c001c0580d4031300401e0081d0398030b910716000740a55409a003140c03d5902e09000d11200c91102074540f0201c03504800c0c00f0030b0042003102c45070754000c0c684480402e2600d00341102c1104076070000c02500341604c2d00e008010003480c0c090030445000440050401c15040c89401424141c44071071040c11402d0714081000d0500503240000b0b85410303141100b08040c09800c014901c90f0640c0503e0007408582d0502641d03880c0c0074202c1c3c00120807a0a40083c0046240004006c29 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 532690206 1250 532688956 532688969
    0x70b0d110903070e22122a080901140310050301060911120c040e0702100f0908071209080f0102040f05040b06040b0f0d0f09061a01200709020f04 64
    0x49000e4805648180201000c035581070f0044034080100210070036083da01702d100702c240804c030303943c90044410a502c60070034121034520700c0d10076004400343c1104c094540400003e485c4001c1a1002c002c940c1d0440450714000c00c51180854500300381d074800e11083c0700103030400c4d501c26a641011016420307400707101d00c1598465802c00d0300102e00c0d0b02d214028401800c00c40038032203040516100c2c400722054801001440c0c4000c0c14003001036010448000240210344a401030004410144183c006886441c0080c0003d1828814a0800543c040f0f0489109070782001c2e014034103001c2220100c800000319840001c561142e08108045400c041d4000d00440300c000480c010a980c0c0c480a21040d0350208071a0b641c0301e04144003c000c0301c6003520041c2103444d401c05c400307490b00c20300e45400f00854164504161045039608118802c0006c2031260125940e0240c0c91180d02800034800200010140ca0001c0404155840c40001d5140e0400c42100074040a0030705540b00c054040546400746c21038130405 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 532691456 1250 532690206 532690211
    0x1b0614060301020a050913090210080f011d0604020306030a2120030319091e060c090e161107080307121b0821010b0c0c0108090a060b0111070b0d 64
    0x1103141c68144202c42100d401a2140303070070312499034200309500c103800000312004ca40380e40ea10701c011b031388400707405d0402c1803544c88132129801c1401d500b01c541c0b54160071003030502d00c11419074208580c9080515510020450b80507270b03607607200300103c0e0520002c0070000380b500354010302c0f02c152442d0145400e40d419555075600c0310b200300c514100d261003240001e0804170642040001c40d4600c19184103081245d10450000715005c1c9941c0c1d00c04a4801100d1141043d41800c80c0c0f4500402079a4020003203003200c240b0703045108a081070307c0c00a40c1c10300034001043e102c001e8221104018003c0500050882d220401e442506e9500c1c0440350303c1ea0f01c00b43d41185d02080c4040f0318110305000780c4001d01426420340ba182805e2401d47d5a02c551984003155401208484010705440c92051110980c0644001c1c0034050311400e080c01c0c2a0b1800a907454014140304c0e5940400072031000c00200003104981110340803508106003801038500a0040a41010300d02920341c01092401c922802827800e0070881408 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 532692706 1250 532691456 532691461
    0x9020417060f0402011808100c121a0f0307030501060308090108100b0409021e0c07050a081b04150b0a030c140f072a03200625031b0614 60
    0x686454039012900007441410782c901040c09548507a12241030f840041c4a410070381c0341c03a82c00b003514208612581900941d00c3c0c129445003568030110b0304a0002213030000740000e4a6103061424130308170713903005940646403c0e541c04915680801112f002160440002c00003a501d070f0a085c07044c2e80c041180c481c0031a84501c049090140c400045500f124142c03a205410607041ca802640030b50302181541100c5101d081d2040f0700314800d8030041000075480402070000c0380c42c02d030612403038604503030062490381c020300316078600c3c200e1032600b051030180121400218650541c0e030f60825040c950b00076200f12180810485000d41d0158060455140d40d92a025a01912007008642c0c2d0b00c501001c00a84000600030b49000030880890320200000010340c0001100301c07a91032038165105a44184c0c1e4cc0d9140708004000c140c003410f074150032120291100b81c9009000d00640307012080c620808502c0801e00e4162074203140c801d9545102040d03400b9505032103000ca509208010b0203005050204013001b2401 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 532693956 1250 532692706 532692749
    0x110c0109020a140d0b0402060d110a0207060e010516020409170706060803040308120a090506070203180f030d08070903020402070c03051009031b020607052b02210a030b0901090204 79
    0x8202d0b54030800802c00c031141081e17540d400401c0300c4007030012030308580244003d60390304500d801460b440da04105212522128518002807030215180e0110080c450309078018180c1c1d91307200049a83e104080002d5805041c141e2010400a110540010300030b1040c00402c1182100c10313100621409000d4603082c4203260311080e08585034070491200074130412080280c0c1c81c040354903040c820390140250300b000415005c540c681b181010303812a0000010307000003da80d10360603181c40302005800419600002c0300000301d00420b944d04200b040b40310a04c000c010018000500c111080307400b455010300155111300c41803410410b000c0860008581500511080c80e5141c10075110300e102003a01039440c0c60800e495242c3c9020034000f40d0005a810400130000c19010500420107007d10308111800d06008081112035422041003019210701117421a504001410181c0244403c810541c0d0224694a0384084001d5004001260b43c170f9410028184c000100c450003079024201f103492140e1101c2d1030301c0382e186 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 532695206 1250 532693956 532693979
    0x3010801050402010915020a151e02030702160b0417072304050a09030e06090a03061107030f0f090603020310051c02030106050a12060b031e07050f0a0b0901080406110c0109020a 78
    0x205246c0059100051a0001c142a0039030b465030342d05040400910078a40001c440d1105510403501101550000140903161390304201c02104410254185403a0604055010304240f04510030b108400c0c0e210750445215580a026080052640243e6a4008155040f441c54040b61400c013440c412840c140000b102c6664030b000e0300c228a80d15a80d111149503410080102c1e64101c0200150000503503034000c000180720703108080202400f06101d585070302291a00400c0a2401d1582d0820441141c0404040c01d8000e440300d8141d80c4103040150312a07660148890402490b5480680c0c0034941550688034143c0308191b00c1e082c10300a40080c0001600c5005000a041441c40740300034403900342000d10041011548080740c0c01b2402400c0c0c645600e141c0e480c0075000540c07090210380b00c0d0048901000186056083c01070b0308031050302d1940076189008040f8450340501010783d810b000b443c030000340c00c228143c0d104013078401e041d070009506c4500c1d60b030040f8003c0030307071610407402290041d00c0412108001c5 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 532696456 1250 532695206 532695239
    0x20f030c27070e130f0f061805060a03031707140f1209191b030821070806010f0f11060702100e0102091f111b010e0f100f050c03030108010504020109 66
    0x240500c0c42d40e01c4c51031151002081e0044205008956404070b03013960b500940101e90040904081c0800c4450035820b00f041102c00190040b440303000d100d1003c00c0061b41021540030390301a01c2552034010b03680c00b10142c80341030324600503501d10040010840307418000c01c000340800c411300c6240c0c48a1991405901540c4852003d0780b00c1e1310702c45034182840003812024110b5223100d90300b8000910380d170792913503209050741001e51111100c003440406916803800074144076038800405e240030203007030500100180150380018103403404c10030ba818004100600510200602c098904100c81b004d01e4034010003900e45900140300f195180c00c00803003a90002c014000c0d84c9035080300911b20501620507000020401d452940c000b4184500300110115110b010f2080c1a80f01440b9132907000c88681c071200061a40c81060f0410303109084e96980c492454071040080b14003d07a890030480c401c41090981920709000d100150201c1c0d11000001058500042d001a4042d5101703032520f50406440348910388110469 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 532697706 1250 532696456 532696459
    0x80702060105090c0a090f030807121d0d03020a021e0418050d050903070f09050411040e07030818030109141e03030601050d1d0c01090b0901050304020f030c27070e 72
    0x50702041103564078000810484010741030640c011683c44021f00c250040c15402a2207441001c00d00d8000c1c0f19200c50050f0321040715180c4002c1070050030304150251950302d10381e6809441c24525440816000f0040080803030b80050054103440b10210740c11400c23200362030102e030003241046000310240600d000662905640000500680c1082050440f04ed400c0f03598401e40c54468200002408040706411402920740f422001c203035413400381800e0400105254103107015519103d10b4042001c0e004c6401d070309582d44441440e0756409804003a00717445150f15071603070b859441c03e54030b08104507114220000720000c4400f070b200d0303140300c03030003104070400340400d40001075001000098a07a61080f0010441101d1207400001c010002921816090303000c1503642c0c2e02030384900c004018540e048090000100522010f0501e447c81000008000e8003001e00002d000b0849140c60710315070383d414821440e0300c100103841d1042018030815503011100d40c4000b001100701c0850007103000c0c0752080c050301c038040c1c90 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 532698956 1250 532697706 532697719
    0x6060314010b0f191a191e0c05010b130e0705040b0112050919060b12030423060d05070801091b0c030c1a1006030b0a050a0302060d02040810050403080702060105 71
    0x940409000545007074200602c01e0818024000c102c00000b4284000605c03240801541c07a56951403c4009840e04001e02d803050090f0701e05010398440301081101e5041c809451300304419130242c50400d0140039040a215032080008034601d411009070380c0310442a0b10b0450032940082e035642c05220489030328080c00e900142c8803104440e0a0328040e04035035004604502100c5280c401d5a402a2402d070040f803084400e81e8880010710032904d0000c41010440c030544014514061a0166104814000c001e20b88101ca28481e0b20200030b94030301082e42c201a00e8640706000c0781c03604002c01020044240107501d0318a103402d0300740c004c215801002aa51000c191203040031840380e0340b000d84da481c460302c40c01c0320040030600710420f411714482682d40c00b6400c1c4e03611129000c0c2c140200030342501c203148480e9004801c4490f0070041641c0320350a5000303d03a0140da549640b4105001c0c110040c0c810394124210910aa040e880c01c95449035200500c564041c3c0d482d24696103400780103d80b01c00d001c2c401c2da40d0016 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 532700206 1250 532698956 532698979
    0x106110c040207030c08250c05010f18061101090501060b130b09060304031b1a0105011101020f0301150203040f0617091c030f0b030a0b09150f0a020a0509040906060314010b 76
    0x401e00c03001840b000500c0200300e5521742c7d035101d9010001d405044c0c1105c1c0c1d610312141c10040e40d41c2104100074902014105002d10310f4951600b8002808944104020040000900c40e4060b80a50060303c196800070000c0c0001c64072000c007542c041d031140c15640780c00d02c01c100c40001c2c60990300058940f01100203002034a143c030769860450319030003609080010741c0203110840001846030207680303030349007e40440d81d0f01d690301d088005090451411034510103a4010000c1134007000814040b281500c4012184541c2e81d12003140c101d02c0c50107075810032451103182d07a801289450f0442840000011881141c0c07a0170381d40c45840f82d480e03040c00c4164510a00d0309203c8460014001d40200181c81d0600800064504071540040d1901e01040c0060b110116401d0522034841400d225102d00740049900c031351582e060500362000c05a90003400f050f0020750114540b840e1520400c200d45528000403c10300c04000607080c44401006544822211030100d5042c10001a0045c0a828080c01d0010401204403 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 532701456 1250 532700206 532700213
    0x50a050a0807090e1003050f010902010e150415030e01150605030609040201052a2401270606080a14070c0f060b31050103170d06080102030106110c040207030c 70
    0x409010702a40140f000540e8085188a4948541c80c440c450050540303074100d203982013650804406c1400c0541d540d040c041c2c3c0c40c1c00350343c00006440300f20703c0c2910300759510034400401d401d942c02190821440f5680400d15402e03e02c2e81074000d074200b03c85400003080010300594a03a90101c249101700c0001c1041400043c0340c40c5444284c25078414018140070745480c00c004007407008a00401e08080e6004d045028200180008105401002811080310340c0480c0703a10820140c1404144101c404003403a00198000e480340444020540384005407061140c0f640300c4002501071101140d14130b00c500d190054909211440e03c04090040e40252141c50f940300f01512440c260a81000041d260346440704900700d01f941300d000101280703019841080e030022000c034900900d81c10400f0381c079002c11410903005001050000440c50105220b8180700369407001c035103850401400310b07a070000c121544044000580c0c107030021140038030b4003800c0d020340d1000c0030742904000c101c0c00b440d080580007424946030300e0000b = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 532702706 1250 532701456 532701467
    0x151804060b030a0203031603081f05121603030f021504030f11010b06030103050105190603080f1b0703030230070f020d0b1009050609151c080c030712050a050a 70
    0x4100c001d07041e0f4020310400c0c1c01091655010700040c0944121401710794041c1036119501a030808230320840420f402d807103c9044106100d1a00966205054200c4444a04034041240300707161840b01c003c1000165886c1000350080c10034101c43e502600a031440c1044643d50942d09034460703581900c0340003c40300c442034205e0703444040000c0e01030b403596030341c0b1040790640e50000994000e600c40d400204007031030050501ea000300c0881c2c00b19800d0341c0c1000f2040c0001350144042d20b0304c5040002d60151944a0382d030003d0740301007085010f20198015288084249940810003108440b00c0c070603082a4640c0c108e040384d82c89000c2c25084080d600d001d009010014401221501000e8001410342090380c1141d1542582a481030b60150548107003000200300480c42c03400742c0c82d40054201c0f40014580380c140e0b05050000070ba60440c601c14850418034810078040c40c1c2001c00e00c0d03500400c21030b440e072881d2440c0a589511580d01502c8034174441a461010301c0c4118112011151a84c0c0c40d14100022981c06455 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 532703956 1250 532702706 532702721
    0x30b0306010e1308070b060111031e0a0e12010504031103071113060b0318010c080c07060b040227040e060910020f090607060906060503071a0903070509090615180406 73
    0x50000c214401020604d5103000e050880d009030840400345c20800d0025184c1d808207802c800064105001e000300c0c00c038281c1440e90790880700003c0795913203c01c40d0318100c2d60140e80c1c1303104c00c0d4003e0030011507850030001540401c1c800c0d031094680c6440019040403480d40d03401070090051482d4641e216100032401c0c8480300c403154011505000c2002c588a030542c4050703400c2141d41d500041ca091100804040d003d0051031202466810056801c8c205061001030501c035024010749425100d40c003090054986a04803061030015000c4400f41031101c0509a8405454500d00351080e800c0c441200711010300801e000740180c42d1000142080126400b1603170194000c8941041020410310484440b0b484590003130102c3d5120f160005041c850791301d810811111250000d9001c0d07880000e007844400500c2c442820400041700b011521200c11600092030300700e554101c66000600076052140144000500b580100c40c0c0800015164800b0814032130156444806a00c0f120356010104001c00c0c200d500121 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 532705206 1250 532703956 532703971
    0x40b0d020d020c0a0519080a1b08040b1b0c0a03020108040501020c3901050306011209050322060507030c08030915040305031605030415151e15030b0306010e 69
    0x1820081030107645000c0342c0001c40f01140c01e40089101c042085420701c001d01c110701145240d481800040d8485d00300a0142e0320508080c0f11400e02002002d098140c501c0d0038440d80310413943e9580741c817114410501d800c1310455005461840b03075824050440410303034100700c11016010101451075034004403012100604252015503003000020341d4020140000702030b07100000c10758000c4c0100703840c0307009000064850744066220440c54030300c007a030b07400800c403900f2132401d01e44220f40c0e1038445c100318020110400024a18440042d242418001400d8005040d030b0100305000901b0380d035007200799420311030404020000b590300d14484d00002c2100001c2c4d90000130782c1d421107401461640390483c28200c00d0302c041c0c01040c008810000c031410700c40240409200c0c6803511310701310b04241c0d40319407014000071801140305031280e0144c20216007180d9400300400c0031030b9031010f4842c0c00000002003060540269017018102c04030508040e8024002da948180d8003030002d200e1a80b0b8140c041041c1c010141c0ba00 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 532706456 1250 532705206 532705211
    0x2160809060f0301060e1e030601062313140d0312230727030f02040903140a05070201120b01081501021f05160f020604080906090d0302010209180c040b0d 68
    0x4201801c102c07010310301030305254440030900d41091041064a45008a81d10105800b80a02c1001c03610003040a0b0b0449125040c085032083d07601d4602c008100d04515094140d20b0007203035404c01c0b0842104580d007100c4108120980301e444420901414000350200507010a1014201c221402825400070300701807051880d0101c070b241c245c200d45649043c02c0d03030703044000b50340c41c41400310094040248881000313500c5c1030b042079285107503624550f0540d50348020b481641d4602d200ca0a050290b202d56844115078060ba1f0796412030704001a220390850403003640041c240c00c1c14100741d518544036811810b00161182c000564030204882c1c0704290600b1201c0c11806103000c9941003100e49005141c01e10a80c0102182c1803901c00d01032018482d14856480400c601e02d60420500c58012a100d904507400c901506c0d660520140442c007244900425a074100d051001c1010600d5411340c0030b8115580e0442c0e05600203011401301d01030854060b2038400b08080104000c00c003040d400d0004103500c41048801 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 532707706 1250 532706456 532706467
    0x810050d0819140c010507110c0109090e0f070b07170a081f09020d0906050f0c072a1d06040b010207060c1a13290f090a060623040216080906 62
    0xc4443c650404407490b00e06a440d0000d1120140d00310881100010300280240801002800000c0883c07540303208400f603007907403020100452002030003048421450301085418460b41c49100c0f401d60352110070305551480308041d24188400610049400da40c1c1290b80f01482c80c1c80d52410b50711592101c48a00003d40c01c1914009006083e40c00a00342c0810410000100800c503401c0c80c0060341ca0007090812050014810032400b203200ea8103a4030300c650041034101c02c41940d514205c40c2030320503d03040740c0160242080024081101d1041d43c140d40e82c032410050389a1a05010b0100b80d401d0201454056046007a09000c0d46200d0090000414003415240d0600c0c0d5551b04100e6080e5401da0305100f5821846d01060140080482501d141c89105d0b200c15030030628040450003908802b80010803503070862000f203403041c8000c00c1800300d15a0004010000300b0355500034130005003120181540d81c82d028003507090584c44c141c800d07035000d5002c000d0f1041c0550030596460000fa8003140600c0c0c0d001e00180807 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 532708956 1250 532707706 532707737
    0x100c0e0f0111010c0203030106030b0306040b1305070902070503070c2306030a060902221509030f060f020a0c06060b0c060c0307020102210108060a050103050a120e030d0810050d0819 80
    0x1131852040315074019603aa541401d50040543d080210418065480300c0f0030f10000400b0004040e0740441300c0070540300005100e00e8500e05200c110360088000c94000b15800041c0030000c802450528815110071410503076a04402c1255418941d4402160b03030008091817660402000455119107a00000629240c868061a0032a0032402a5140c2540d107076050500e40720f00103406501903c1c0040c01210103441200c002040102079010041040110032520000c01001d60041e041046241c1c5c2c055444034007900d002841815079010070765105040400010f4866180400c45001001c1c000180c1400c1e03130b0344c40780d0380c9180d840076141004542d4200a00242c03240019a020707140310f0400e0b040c0c4c0c0194502400103190030030103003070008298a888010000982c0000b00300b8103496000c1504442981c1e03902081d910385452001140c2c040c041c05200c803440d60303404200d240c4202c02d4501402e00c481d4440c014414a1100c071500102440c1080103284000c6079a07003420400d2078030300c1c501102044601c00 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 532710206 1250 532708956 532708961
    0xf0411130303090914010503030d020c0106030b010618061d4e0105150103050601031401151b110108041403040e190c1211090d0309050102100c0e0f011101 68
    0x40c01035001400f280400e028090b03a6000c0c0c480903070060b981850440d41070400080e200d00c101c54990030f040c0e45c00648402e9010080d04003400454000d0300d501c03003d42c1e50b150042c08031259200c6140c08030032215030110b103d900805440c00002c016080d100e0030828507906012011001d8403c00fa20511906020050700d000d20f140c02031814101e8100038100c82d46442011a420201540c3e000d25904040400c0f86000f411110b045400c1024030300481c098940030010b03402820480c0301404103640c000000b03c1da920807020303070500101440d0f031040b01c0d411440e00402d045034075a10005284100019172490250b00c00c45c50b6540060207080280c84400d903400005195600940c8034590f6034254100304000100080c07800402a4000d0000b44203c0404e50f0000f405d80d01c0ba02c0f0355200003507a80c01c20b01455070011302a62820078010342403030819101410301500c40b40b10f51046500600c65103040c2c0d003010704c05010300040c050740d41e181c060011050604100050003003042043c1003019041c50482040b4090 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 532711456 1250 532710206 532710209
    0x619090f020702120a080304080f0d05070207080706090f170709020712030c02150c0c010b030703060203040c1d06010509010e0429030304180513020904060b130b0f041113 75
    0x14080169241c2d05881072005604541c0720007403681d00f001c4050000b0440b10000c40707a20952000303466584000400c404943c2c2d000c0e03010319041c0075113003504100c10a45c0000c0c001054031000402c403041c1941c1c03208200c56804a40c003d924843c0d0580302d0800100600481040c9501054011340e0016501c9903414422a001285c090341e558a041d01c018080c02c1c0c145c400c046202c0c5180c4050700240c070b032800b40c40b8080d11010701a1900d03040000ac0024202d0310a520168400b00005c1c2aa1103d40d40c0b0705044001c0e4000b502c1c2940d134a100d07200d00080188035040381c120002e81010000e103103607640030010340c1c0301d80140c414a81031181c1c40085038103d03580e620a1031031044a0700300615614039280401c01820b03e41c114098002d9000300014031403c0c0303030b80c6010500c4d56280c217030204060392400c0c03480080040000000350405a480c084c0000c00506030010700c4d9186090f1840c3c0758006010501100740c81b0116400e1f50007038a1040c0601c00c0b0b04140d00300c1504041e02e940844c0c600042001030690f8828117 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 532712706 1250 532711456 532711481
    0x30f080304020f010504060c02102307050c0924041508030d1a0303070b0606070c03050616030b1810050603150f120706080907030501021b100c0503061909 68
    0x100001c501e040e00c3e45600030802842e2040c05c0c507041400240181c1da003268003912401c07484006111940c0b103116030081c12940303480c030307042104052a0385080e80d400040017113a15014601a94500382016a10f5604c101100f01044011403c07501500340304048918000d900a0f413910b05100100840750040b0b401060200d0045035242c151003122030032682035681c806640802101000d0003a43c002098400d200d411900702d990a0b10707000006140d40c810800c0041509000d2103000040c40b101040b00307480344581d0790071845400034001045080300c0d605d214403075001d28001300f140704a41105628551060203d6142c107520303034a80300000c0042d08101d8050ba06c01020400c6c1e1081c505100040d41d452601c01c2e00d510400b62070f588010341c0c441100e8010041002805000144d01080812205000b9a0800000c5640d828a1008d024094840070210b21542c8600314528464109500c0b802c5521441980c984c1e0860304c0c1c480400c09440ba04001240b0010104403011414010a01c1941408c2d80c0 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 532713956 1250 532712706 532712723
    0xc05090f072a0309090c0c2a090c050403020315011a0a03090c030c050307210201080601050f03070e0a0e040515101e060e060408061501120c0c2a0504020a09030f 71
    0x10341179840055076110080002040964640d4800103030800c030075419402c0c400318548906d0140002c0c00e11900b14168007000f840c0b804c5c00000a44103402c0b03c010001e4074000c0c0c06440b80c40c00403030300b815000c160a125011400d0740824422019403070150150150590078130b80800c1c004542c0d107683c0e400d2552500140c42c12513880a0810813031404008c00d00c01040311001004001c0310416205109211003200a41402680400241c1d140c0c46102143c950420300c01200d51681041c1d0710081100c2c009118840c052000000702044c45812000d50034407550344280102003d543c24401c1e80010741000c4e00566080b0004640880d400c040406650115030703185090b06000781c03a000f002000c014400c02e1650040b8400c00052000800224403c0e42c8060020740b900e02c01401030004a6a00884044601c21b2500d41359041c1e074415071016040070307202d0092403450344510201ca0505c646c60300c0c0290481303203070309041410041801c0c0798018003107581391810311804043e907a8441e44803143c4204030890700d051 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 532715206 1250 532713956 532713959
    0x403080a090b0a06230f0d03090f03080c010f0b1e010e0a03060f0b0a0e0a1503020409050a02010e0609210106030605091c0201060b0306012010090c05090f072a0309 72
    0xf40c1544417044400f198a50a00c4e0801000000c6080c00814004080c0505031050070b090505014098980045c016002d0f01442103980f1f04003000c6079005410002c8407075090400b000c0f074540d101c0c0120241c0643c01420a07200140c021410804c0c0b50903104018107000d01c1002120356580c82e0880d42008500404000c1401005c02101004580294043c0351184150920500c840d004483c076190b4840c6000e50b000071845d089061181040f02142e00003584035003804022010003038042110b1100f035100f81c0783c18104544e448100702c40c83c0503080340590401e41c0b07a41426401185070311262010f1580e00000540d07a600c0342c55030f60580740222000c0301d04c0da0107078150038182440840001140c000300d1000304545400c100310407416100280074103042040300951803401da2941d05500070080710b40d00885001c6d080c61089007000e406103200503038884888840c005054285500710074801c10a20380100d1943d903c1081c26600c40d0150f02c0e441d803112140045c002d840600610030482c480d8065111301d81c409 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 532716456 1250 532715206 532715219
    0xa03020d021b100c200103150608011e03050d0f02060703050408091012140610030213090509101e150b0d02130807080a0b1e07050a020c0306040b010306050612060403080a090b0a06 79
    0x80e05032204181c002000723074204201c003e501080942c1901c00c803c12200c40c408091303100358958002500050907500540e2030070250350380c0101980729880559002d0b124036a460001c01c4e41210b40c21500501004000c011900c801d00e8541d4010605400310300f454244419001115030842c1c280480412f95a0401000d1290903d03010102c944010481d1405501c3e040c412040f11a01c0d540304d100c1d51035195165004150740c0301c0c042c03240c040001780710007040001c5690340d00d41c8140f54110014100c40c00e40341500162140c041d91041109564851400c285403480b41240e16000b9800075940c100042090000854402014090170008201c150300620841143e030421a104540140c40000884661031000f00e5154406202692040441c00d00c02d85940c80c014050b070400340307030000296140c0111020030003000499075589059a00038501040580c0e600c20034015101280c140703d0480f50300c54030011f00024810142160f0003007001001150425065a40c01801035003900c0714542c1d191203103014006c4 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 532717706 1250 532716456 532716461
    0x51c0e07260a0b040305040509090c040608030711240301180c083904080a05011107020306180307080409050a0b03070612050411120a03020d021b100c200103 69
    0x303150124606107504900c40c0344099803006000c1004081400741000a024180a40240d400401d00509080e40d10324020320362607140c003800702000303101d14942000410305190001c142c4904d1a404040c13494184241010841520106281003c494958811800100300110051070003801480614203c03054988908400da403001d520890400100794100102200b400392010010030207070311241014104411000c0c1000040655680c001e040003400103881040060300c103140c0c0d801400208082d030104000103020b0700c04c802001c1e5050780202d000c18540010050600800ca500004880c603121507662000602e8009511a20b40700b540c813420401c040d01903000e000310a0700100c003d005098104030024000903034000c04000c081e42e80d000090200103614004072903003003000780300501c20b990a959465959002043c124010b005185170074030b4141c000a0810101034541015005c02d00859042c003461022a080d504200305128070310801240c420a04803000403086401c001c82c0349142c1c0c001605 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 532718956 1250 532717706 532717739
    0xf0e190605012408060d02040e1516050a050310090f050402130b010206190f050126010c0206061c060525080f070309030c050f070e1f0303051c0e07 65
    0x116072212441e10303e0040d103055100c2e03003100968100005951903c202003843c603040010025003191400d01c800905000008090301000010040b440c00c0313035108042001184009490301c3c0c0800d0040c807001d03a00324007032030255522161401d0b58078401c0ea51094210192083e00c1501c500c2c0a5654003031205600f040b625642e64110300c010f0500882c00c0f1500001c0d542c1c4070003401c0b10f01c248008100020085029002400c1e00a07510348140407035611240c1d440a101c2d01c0100c40141c2092003004100c0009040c020205222026006802c00b551602c0c240b0102c10000c0017403414010082c6014400a41588201c6000c0c110012214591512241d284071361500d490000e0814014001c0c20031020f03002d4400c005a001d002858007092944842c60240c0300c401007020018268020401d00030208600083d8100403501003150034107060700d9041e001464100507428004421004001c14404a40600e001345005205000100c15011402c4984c0c001c03103218016a615603000a1402c005d41c0c20103411004 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 532720206 1250 532718956 532718969
    0x307090b0901021b040908180906030a0309060c06060b0d06031202032703070f030605190605060904200403052b05030109050a061203021507080c040303030f0e19060501 74
    0xa01c0c200c000c00001c0c0d070303c035507440d8050303104100c4403010140c54030b558001681e03d40c0d01c404465164401e0b00650b00c60140c1c482e00d0103014820340702c0003c9040ca4002420031503076405840d20342c1c0b100d0a080341162102085031040d90120b8441c0800128122100020040d000c10b4450004c0e4460035468000c522441c502092030071940705110444041481290020380509044105500041c42001083c205003259102c0c041002d014000002403100507005681700d107441c10301d1050fa204120680c003007101d4641c000c00b500800d00b0302c040f01c0c403030616500440c90340c10030030842c50101040c103060f9900c03644580c00c120b8054201161000c4083c0e9000b0410f40742804554194050030201d101c014210300051145151b45034603100803441e4074007194001d0020b05414071400c01c030780c5028103010b540c07000388070300301200000f8031000070b181d2901c1548518010716082100d58038091450f14101c010300285072100c2d080030381d40d444080407404100518030004200d04490400702203241040c10440e04143d0004 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 532721456 1250 532720206 532720229
    0x13061d0916291e070510110706060902073813050f010b09130c0806180c01020d12020c0c0904050609100e070b0d2301080d0c050a03141e030709 63
    0x40001c804800d0f9401040d01144188507140d080c9170900c01d180c649149034502e26285011074118450107a84001d00380c40d1300503901813100954070500710040707204604001e440c044034140078116141c4030f24080c03101c0c490100003100c814031001407801c04a45054916190506018006004011080c004010a010310348020041040c800000c1030404000400748400e02d410120080300304028040220040c0006000315942071038102d44400d501c203d540204200d920601220151543c40000c84079407418155448500602e401180701c1c000c1e401040d041507190240c1c40e00c02c90583c8600c140d06100c1c60044e4000c10329401c1000406040107202400d16801500b032117a81c0030b010b44d0014600c822078600c8004039540d6400060800f009007010b0441101f0303002481180c034440b1201e41c00b1181a6a0000b041d04c0a5100c0040143c44529400bc8001e00c00d4000714000740100b40039809002c0000100d610039031815030404002d1144140c68809008158008070902001079800a0cc1324007030304401095 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 532722706 1250 532721456 532721467
    0x2101090e101401060f090b04060c1e03090b0c100f020a0f1719181a0603010213030b040c05033f1b0705180613061d091629 54
    0x2039004003005024540912820590061036140706c0d50030000100031070101d09884948900008002c0098040d050b5000003080721403814120701d821030030451641c1500c907090b400d80b815a4250fa0764100c98481c00650045101c1525480750b04d000741e8a901c108000e00681da1488100c0242c03101890345404c00400020031402901d9085621003a5005080e46548c1681f0361582003d541c01340624040c03032514203201a181da0204240180340c3c0c01c443e2140b100d0a0200c2d918003040c10700b00d0044240c1021a032031a25010400704250381c850b1504140a0103070468a50780b984042482c01101e00c00ca100031551030301260b1a020141c60100398190000420750100c186495003142070345c001c588440750003ca0b40ea0351002d000000308034203001454080d00c084001c00700c656001504600880c0c2e42809138161a40100171210750b48280c0b403e81e1a1000f410903240095031401d10300020091074107030303503100390404000001c0400c0001c1004280d2100c14030020222641c40b030419039501080f003406d0200c140030 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 532723956 1250 532722706 532722731
    0x111130b07021507020f150c0601060503060307030f020303070501110d06080d20010b120706030501050d17160c03151406030c0d0c0317040509070c0503040b2101090e10 74
    0x5040d5991160f000c0e8980240d800002c00c10400c0208055000c40c020880705010081407000d00b034a499071400744e820680e620b000c05d0340c1d030344004c0744c4269040e00413190078800250100c5030343c60018006002c803801d100c156900d4600b140d101144000d5902000b044880d803131141d0f4002c00d0050070150300907006a841d6030901070040c40407441c000301034440b000025900158250b0002000c94001001140c0c0034001c0c00e0340c1600c50703106000c1c40002900300380c004102400d020016801c03e50380607400400000c0208803000a640008a01e0030100b40e0400300f840100d2210701190003d9800340c560031841039500c1d00414200d410000801070340303030046020040d080d41d020401c1000361400f07440a052800329842c0207000d100a40d0002070401c42c880040301018400380c00940142c07070098842800755102d00c1d2096440102e101001406039204210a0200a00072400b0b0408010401103150301000700c014041e90741c0d41c2c2604600c00312030303450f4407004410004001195010010b094204000c541454 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 532725206 1250 532723956 532723969
    0x21f050a03020c0f060f06040c02070308090402070503300f1021050f010507020708060907060e01030e01020d09120e03070902030403050c15060906090903120403110111130b0702 78
    0x4031858241a80481e8000c1e140a042c0040807200c01042c0a440c010f2806080e1682064810b450f104e004a00c1d01504401440c00010400141d03600489164240107407070341007101a5205a00c12203080c041408124940040d80300c144110000141c5a84400a00100e140c02d105d20300904510745200c0d10307400d01c000f038416031103444282d40e1076076a4010703011720f5103860790030150250314028402d200d8a0503485107100107502c0507005071000d909580540750b4541a19649200541d201a1250852241084858003600d070203030141070103040105543c490754120313a00320703044000000030640e15600100c041081c5c1d02042201a91581000000e160521000c2580e9035824040c0381021a400008141411b00842c1541c002000c2c10702240c45081441e02c100d114034000b07555103400341131010041000c1d4600700c82024070a8492070019802c101980d1008000103401038070603414000c5102c03000c6003010080c01390790004031100035915038462446000d41d13100c42051340303c0740c1016018030a41005a5512 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 532726456 1250 532725206 532725217
    0x170a021603030b04020c0706030603201c020f0a0608041a0907030212010603080403051606020a11010c030c170a020f0a2609040606030c020d0305072307050d0c021f05 73
    0x14030b40050301c02d8524010400a100e02c4d100280148658200014002d0f4540c2050003542c0c807035101c001d03d03440684c0a089034210301c10041644010100800d0410a80321220300000b01d000070300c80301080d002500410800940c80e04039400080d42c0c5010042070100c00811052246156082c0c050720707107001c3c0409503c841e00303400000c1c403e005000444007400806d4028002540d0850380319580c40369a481e00965441d022020046103903070580f400103000380042044c01c1c0d0b00c5d40180c11100c407103170314100440341c800f0220011402c1c0414042d0890100d4241101260011100c0509a0741c0c6e519840029140503504048a1101d521464001c8002800340d48800c101c4c164000718200701215a120f401c1786809840f0000790010b250030000102c81e585500007c0078012070350261260000c003020100e0540307800b01c3e2000041802d0100440c7c12444280d1b4181c0c0149a14405c281011a25682e5608040540740303201d000403040a40304d002d625000030b41d03510040b0514030701014400c80781c0780904140580c = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 532727706 1250 532726456 532726463
    0xf030c010f0f05040510030618020403030507080d0f05040309090b03061b16051c03060b090924060c0a03020f15070521130b06150414031903170a0216 66
    0x10320764050b0940c1e0160042d50050f000081034088440d400040040080c4020303c50f615013100040d09203803000e013140c401c071411b40c0d0b0503584140c68403205403103103c020f61080d4120003030160760790380020602e2028071589020720b02c03a5844104552420248105940402201501ca41c00810900242c1c2d151100c0c1d9a06242003525040c0d11a42400d0320031214029169002d011401440213204169210b614010070658a17510208030954840c004a0302c10700a002555403c020791f203000c52103207440740021504281501c0c0d50820711208840c08101d40e50086041b02009038042206801095010700c8031000201d5080010044a03c112009842c8204082c120342c0030b000c00080c030440c6074506180c1e07428401e1402c88401002c4d0074081080c00f03114030307420011341c0c4840e5100042034580c5862110b0302040c04220800c00d00307203801c000c8814030010070408901d90610610100800c0e000e240707a421103140740661180d8900c503c4504e03d10200d41d078010a40700005104024203080404040710100b9080e40 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 532728956 1250 532727706 532727717
    0x303040513090c0503071707060c03050a0c02030106050a12140607050403030c02150a080f0a0b0a03171209060103031701120b0709030611090301151a030a18030305060f030c010f 78
    0x2180c10428002c80e400d811070790701401031041c00314900e1401a881f0114583c1c0004884a8994882d000c45032401186e800400240c000c02c0141d0b081441140380141040c001030000810941d140c00141c200c2d4081e60040040300034511a41c400d01864002c00c80c14583c010014208a1901c0c880040040c4603901004040c0302001c1410415074541400c44d00c41d1050f50201d0aa447c8068035024110751380448101000040325400205150128042c0444501001e01030190b0141903070b44d000601d8402e80580034141034140104000c8187c6400601d00480801000d01a19411803c1c01003812044209100400041e8001040305080c0494421142504000e89220503100d01101b10b40c0ca202d15030000c4c1a0900b068566900000e0b140014400c10301c0481c0200620303221084003620b901001c0c4034450b00c034a01068070031402c11540c001107522004a8400141800c200301d02113031440000c440a80000f0740c0e8200300070701418200524482510304400400c0e05041c10000280715102c01c4080c2800c100f03 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 532730206 1250 532728956 532728971
    0x1e120f010f0504020d0b0406180305071e080a050a020a08041e061e080612060f1609030b13020a18050708130506071b020a08060417131a07050d0e040b0303040513 71
    0x1d86509ca80040c02c840c0c0c2c81090000200d0400610079000480b042d50100d03414803400c0f02d41c1d0003100c0050032155004c0120742c101881410140c802703820808070b1304258029802400e00140040009002500da280c10046070300b00c500000501b4407086812003814021a00c2c4151104056040c80707610540c042d140000b495640c8402261035203425105c101101e20034001401100c1150f141500d01c0340c4a11000d03001000c03c1d4140c01c072510340292101422915000d0041340a00c03d408088251642c005031071942015a07811a01114680080708207546661712070600c10401d43c40300c80326801c0500c3e440f0b0407102d507041340c68054441002900c945c0034001c8518203502c4119040303062a2001c1e40041c075401843d5603940250741c545c2004c94049680c4501500c5408441c4802d0050300d00290701c003448005d020342000485a8407810000031508241c00a011a0001a07410400368020001039500c0d9820034604805003c10382c0c18802c6094469001400305222945130200f0600700082c0c0b004000c940765 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 532731456 1250 532730206 532730213
    0x50415050f070609020112020a09051c0b070305010929090403110307060203012c0c0702040f06060f021002090d0303050a02090402040305030c070503070e061e120f010f0504020d0b04 80
    0x34800d011000c2190500850b80c0d0341400183e50000d07134098000e0720341d01c0308510904559001ca228a161890109616180500460401c080e108141d10354010003040064580d0312003456114040710f0340d1000a84580041c85000700a000d1340c82c50340c20001141e40b1411450f03080100d01031031129001d004004600026080c1481040d0450313140e5a10002d8039030b5140c0c5030810b10b01940c002d00130003035007001c0c11300c0c4000d090262450340c1030b02c0100b422507500b0300d443e0a1904030b25039000090030381c2c0c00340e21551071f01005503a9105800091559859020404141c10b0020f410442c6441da00ca2441c0e1041c004a082526048034007101168980b40004040da24940a94001d000c2c01400640140c4041400300c1001000401404151714030421a0740b03840d500d0f010955106140e00451200707401b44030104005040201d0890003840d40c005c00d007510442228089040c07030313502c0307521000160300140721190250310038420000900c04e200c200740074601c0c01c1d402040281100401c010701c04404000081d007070 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 532732706 1250 532731456 532731467
    0x14040f080307180b040306111326011d15090606040f0905010203010e060a08030c0705040f02070210020d090806130215070b0a050604050906090a0b06010e030304030f0501050c0307050415 82
    0xb03d00241c12440c103011340307a0034404100e8019010440c0c031a440c0011086046013400151070020700c010002242181c108240c02d41007a407160490f040c15030355980700c2e00c1c01060a015a80c400050800d00d441030400c0000300300e01d040e001000c0918100000d00911190100101e0000e80c8102d09460200e410114040c2c030a00900703995001038a03030351002c0700102d0006400320b5001e0040c0800c071100c010940d01c6800d41500c3c2d1003250080790440e844140d0801c0582800e03008040b140394018030040c2801120740108524040180389540142c00c111450070101d90426080c201030f14011000300058940075040e00a0005501c0f4080c1c070469440c40c2e14404225480101c801c0d02d544200010364500f860301044028003c155140b81c03003203080100082c80c011001540c01e110320200c03c0200b02007062504c50700346071072018080718108403c04d0f01400c0b454504000820043d441940c1e0401c3e2250329042c01404c580c40a04460b005007010410300a245034031409039800d84001180c406a84034400e4819a00b = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 532733812 1106 532732706 532732727
    0x7050a0308032a090d060605060307030506041b0e121e0307110108040302150c04050607110906090c07240608010b01020d0e010c1113020c0d0314040f080307 69
    0x614500b00c6001e00009011b40e00000d0103135110404195240c3c41200c0c00d401080d1100b042c0000c50805100e1100114280f01e0701078501c0d0541e0100504040014001e64440c1e500301000391032401c0c1c28089465115946840503409a01c10004682c482d040b5603410356100071007400b60080b41d402a1000d40c03065034107502600003001911018500d005002e4108200681d09102c08502c584901004104507401080e03544031f1105e21504000e06190002d046901441800c0180040100c142041d6a84190700084502d03003522030081c00c036140d0312141644000c03d030500c0c000158401c010350018107152800e0342554840300c4408030030f40b00305e0b0b0a0100b0350b0000300d1644030134003c280c00110131901990014650303034005075540c24410503608a00750305034007074120380f10f84000685c05220713141e448540034802c2d410301d01d0551941c0741d1108000030068110750300080001d180d14402d87c0b0601 = true := by decide +kernel

theorem cover : BRFrame.Cov 532553956 532733812 := by
  have h0 := BRFrame.cov_init 532553956
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532553956 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532553956 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532553956 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532553956 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532553956 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532553956 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532553956 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532553956 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532553956 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532553956 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532553956 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532553956 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532553956 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532553956 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532553956 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532553956 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532553956 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532553956 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532553956 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532553956 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532553956 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532553956 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532553956 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532553956 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532553956 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532553956 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532553956 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532553956 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532553956 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532553956 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532553956 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532553956 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532553956 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532553956 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532553956 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532553956 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532553956 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532553956 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532553956 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532553956 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532553956 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532553956 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532553956 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532553956 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532553956 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532553956 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532553956 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532553956 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532553956 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532553956 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532553956 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532553956 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532553956 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532553956 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532553956 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532553956 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532553956 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532553956 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532553956 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532553956 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532553956 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532553956 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532553956 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532553956 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532553956 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532553956 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532553956 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532553956 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532553956 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532553956 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532553956 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532553956 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532553956 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532553956 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532553956 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532553956 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532553956 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532553956 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532553956 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532553956 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532553956 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532553956 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532553956 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532553956 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532553956 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532553956 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532553956 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532553956 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532553956 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532553956 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532553956 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532553956 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532553956 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532553956 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532553956 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532553956 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532553956 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532553956 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532553956 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532553956 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532553956 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532553956 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532553956 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532553956 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532553956 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532553956 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532553956 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532553956 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532553956 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532553956 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532553956 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532553956 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532553956 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532553956 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532553956 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532553956 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532553956 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532553956 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532553956 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532553956 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532553956 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532553956 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532553956 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532553956 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532553956 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532553956 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532553956 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532553956 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532553956 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532553956 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532553956 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532553956 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532553956 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532553956 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532553956 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532553956 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532553956 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532553956 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532553956 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532553956 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532553956 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532553956 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532553956 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532553956 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 532553956 ≤ n) (h2 : n < 532733812) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
