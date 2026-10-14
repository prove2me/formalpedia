-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3753
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T10:34:32.836648+00:00
-- url     : https://prove2.me/submissions/acb85254-b5e2-4563-9192-37a211eb3a73

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 674820143 ≤ n < 675000000 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 674821393 1250 674820143 674820187
    0x4061e06030203070902071a07021c050d0b0a050a180207052a060304021e01020c04020a0c050601050d050c094209091b2701062715020102 61
    0x85950310420010340ca0b08008000c01000710420031890060141c0350700c1e81d1134003484c903000040c04603c030200c2c8460b4401c0200b5602c49086a4100901080c00314004013194400c20814540d00d0901c0055440b034581081403004607203000301103d529030f01e0300c40300346980e80015042c2d1100c25400d020340c0d008a0b1003800320641c900c40d602c50280020400740011458840460603581c06060140708000050321260780d50501c4c00541c10241100f5044100100e1030800c1d48008550010300201c0d0110b0b00c950800d002c1d0071010f10032810b41c0c0c0b040e0303250000d00407030302d403c0318000e0041e92000c0311140d003e05013110760391740001c6a05140c4503860130b0850041c05a003414541c0700810f030711b49080c094070340020079003544500d01c0881e012400c5040c190f4485655241c1c049480b654583d00760400400e80d680c0d60096040c20500d1300e04200c20b03041e580c00700000c0701000d11603e00444c056035460304240198002510f4440c003121800e10140c4c0c140302c0220082100201e0030780035594204480320a2115000d43d407884 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 674822643 1250 674821393 674821451
    0x123030702060c04030c03110f150910080c180a2301030605030c090a0c0c02090408031b030106020613080f031f0503120904092103020309011d150406 66
    0x500d0400d210002e2038114000c001401c440c5040c031090000900c2c1c404135a0480b50452455a10600f1641c00034440040504003070354451140c401070761059080d04050507200b40126180302c1e00e000d4801041c0c0310000115000003075810104942001001c1c1344111001e0a1000b400c1d6036441da03120705090410001074580c50300c0341d01030194010117542e4503012740e60241034141c01a040c003d40180c0410b10210300508500301072511f810790329913080d111790500701003260010144145400c0c40d00303081c00d0917170050b6100c55003000303240c1842c00380607116030841c1c0c100d49407540204103a988040740503099007040d0b901110400d104202c201b410313110f06030155000d0030440212807203091103006096500082075210394085e4003d0303091048801112815229040000e50b40415074000314507081c1803a040001d2000c0d03481d800f00408491480e0300d940698400d8019074000c014940c2c0030701e01003016504444482041e540102c500d00b504118202c4403d412030302c40e160109240082c62204544607030b0700320702088 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 674823893 1250 674822643 674822647
    0x1312030509070f060c14030f0d0509011103010e070c0218072628060b0406171e07030c17090c0315100501050705030c0105010b0c06181b0123 62
    0x40c1905100b8100201100300080101520b0900080d260a00610014000d6402451140346004052084511544101d40341d02c3d5a1604540458020f007000d4172062055803902d185a030300140c00720112410303544c2ca002500e440e0764400e030048aa44145e0b1008a07040807110110350100010310800e940250601d4846402c45d0380c170422181284506000c05011442d81c4405010f0710070f000c9046018030304100781890079080d28003d10b81c40608616402116007074800038002031000c0e0701647c101c0490b05040c6c2d140c811503c0d9040e6880a85002c0e100c40d0a102c0c481201003240f00780294070400d01ca2460b400d005c0c0d0045061f640c1502e09000807a240c000356000342d14440b2941c80c4c148552071400a1101f01c488490506c01c804d24568502400b4007810b11000207807800c04d020301002520041e0844000a1001d90785507007041d0351365002000845240e108841c007190302c040b85c005840c822009840300801d010384070101c0e02d0072440b10b030140581c1404045c1e0300c25640401d2440c2105843c04009802527 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 674825143 1250 674823893 674823901
    0x150b0f0a0f0317030919081c140702010c051e0f0705010e12130b090d051e150108071203050c06190b040b2b080304060b030d0903080702010f03181208010b04050904060513120305 78
    0xf0540309c001000d500840e454035084007270007500b2005843c803100000480d10084c1843c04e0b155000c034415034114150070b040204140702006415082504005a00ca042c0c0b19400c4403014844d0907402540b0804a9099040c502840780000c01c9000c2d04000500a0a104120038107440d500e04148080c0307002e0f00308002076100040303890f8007040200c002400d034296110180d031400070065201d0181c2c0c040c06122a080c200c1040c24544510300352080801b100b4180c42d0141403081104c8000c29450103d5804941081c21210040ca064407940e00c401c0000360003000b10a160801b48a61504201140c00c2c1040704079034403401040505c0041d44c4a01c1c0300d41d20000c6e60104240406240c249440355060030851045014000140448141d0715601c0c0e081c200303465070080d040c0c0d054000d4200d12103402c2c0f018602c0240541403040302c002d074070f106001c1c50300e80020305c1e62030f80c450b03a0861149014040c0c00044403404900040c03003da02c9103500a1400b005040000c041c6d6881d01d201d040c0e800304110000e0f0300d80081c0 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 674826393 1250 674825143 674825171
    0x609050705060f03040807050f0d02010e0601060314130213020c031804020c190f0f030c02010f08060307170a050607090918150b0f0a0f0317030919081c 67
    0x18030041d110807590350b414940d50b2111074070f5600c0000c0000f0300000001c01c807481044020091000124280701c00d8032600c220300b02c8000e0003009040302c4111644518400007421038000c0c03194009081100c1e58403c000e5881d4689074048040f030360412a00100703072050121b020900c52001d0526050700e032000d950360f0140d03550400e407200c81d4a48114416481003102010070000019074a42103c04e00883d07880c40d46030b0342000b400b86000c0c20001781c10785590181c0702c4201030744500e01c40080c0d8801d880740c0500d80c1040404403070801c2c08855007901580a280140f00c0e800c44002800c4072840d00c4001c480c0460126514142000d10a460260110300720300b000340b10402450065aa1500f802ea8024a1000b03141c0c82e41108060b06042d600300c1c0d55500d0200c2c51035520381c194080d202d04c00241500341601c0d51410358190000692100760345d4600e02c3d00904094529081c01c581c0900c405500426461060f01050050350f01640c804481070101084950070000340040c001700103190780000002c4c1e56660241c5 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 674827643 1250 674826393 674826403
    0x3100c0908031204030c03050c19050114010620010609020a020109150207050709020f09030d0807180803040303052101080a02013507092301110d05070b0c16060905 72
    0x18090340d0003d00c00c20008500840c89650301540518000d0400700c010f00301991742d403045030407400240c05610081d2a480d40c1c8051a040100d228400820074107110700c024610008080c00be07d0001205901411001d0005110407003400e0583c80c000600700f40d8a04009040fa4040405a00035035103814841d014426442041107080c2118070341176142800c2ca41c3e8468403080a0302481058682c0841c0c2c001304110100c041d2001c45002404440d072862000d640944081c00031520000014115841c05d03141809405014003261914402541000d046035019901900a500e4001c2380b030a40400c0b0741d001a1031110414024031004000d002c0c06821400010b06801c032401d19080440031026520040141d20281d8003000d4403013030158282a16068421150030359207500222403040c172120801748078627900f03c908401c60001d89416403280f0200031003030b0300c03005220607080c0880d90901150010400b141d203040d50204c0c03250916880c0210b0000b400d9134240307182000703840c2d50b0341c0e800d924000c00c001081 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 674828893 1250 674827643 674827649
    0x115080105340318060e01050103061b020303040b0c09102c0306240301092405310807050a050106080105091009020402070f140601051e010806030c03100c09 69
    0x889000c100c0925400b000707104070b480707580042540e00c1c002c508500d404a04c0803a2241c1d0b102c10f007032044640d040b010501900003800242d0b129894420303a17002480a040040440d600540c0145040d5941c40e151100c20000080c500d25001c030080003004030a079614010480980056210001d84005003000383e0905802ca014032082d480c6111003480e510781e400520154044039005400680c40f00d520403581e01581200122a015820a81000100000d960341244044407100344801c880d0504603411066a50607181f56002c5114078081c00c5400d0054188907100e401c440c101d000c206c9185070b03140c140940c452101500c02c0d03042102103900b00082800b5000041000b00028000b5062a034141903d0380c1015440242280e59901c0b818215151030301911403039034118012007812850703810503032010107554502c40b18501178400041418680200e1661100800c1c4c0245215031098100649070f103000036001c1c550612a4510400345540c04016842902044050200f20f4050b10840603281d01c1c0b11350 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 674830143 1250 674828893 674828941
    0x4020c0d050415021612050a050303010b0403110f0a0e0a0e1b09072d1206080a030207060201060e040206250303020903010b0105040b0f1606060b12060d050a03110115080105 76
    0x5c400484690182a0344200b43c0302001c075203203014181361404a00d0300b048403000601c503000110002884003088070140044901038150096a42c101e4004c028904a070b84e0780b81035204c1d002c2c410602240c40b50800c65544142c1c060f03c009000c440501055140c4103007016501c610590b046000e4000f81402c400c4c403078002101d03040007100814040042040c1c0007031840b03900e0a8040729080400d09900c110003e0000c2038048400304110b6481d2170381640c807511010001d90261152080008000b40305100c0c05085400b40e04001807070b0744440d0308200c2503034808402440030500c3d9988003264044028625038910b4402d442c0180e5a0300c221080c142900c5010046034103020040c0010459041c220048038200e42800d4081a030360000f50422040c90098070301d025054500d410340c00704903040241c0041000c1000915407100da80c1d50403003017103410101c03034071300800301d03089107c111001a0281ca200011005848004a12049109031080904402d0342c4211921f81d192024050320002418488081003c81 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 674831393 1250 674830143 674830153
    0x203040201090512070f08030703081e06010f050705060f010e090102070b040212070f030b041b060e0f030c0d21030b0109030b0c090405090c1e130b04020c0d05041502 73
    0x3600042c00c815020701c20b6a00402d1040001c50051600b8054140509681c0240d03075441c540700d042082e500e420580c4101c0208480201080d00c1020b81114100c500740d050030b14802d10341d0b52400459207050b560890405011050040c100042c80600801d48901404c040d4507001e507140c00d40e80d1020101c00f0384040a1a40304006d401c01003102114150752141c4c040d18103003d07500000703e0017444c0180071f9003c09106403081c80003100300030120380c1440c00b0b00d0040f09090700515032940184100c107898440d41002c6000346240300001d0402d59940964120020300390f8214900680100e004805840011180a0f0051419018a030302024500d40e800421b46010071002e5400d42c006801d42c034443c08050010042c1c0400240b480d84940c085800c0204058000e0115040c1481c8003543e88502525252040c2440c080000f201000c106e06004040030003010000b482020b101d024008200305103109030031503000c00056402c000c04010313402030110b0640c1d8032580c81d490011068150010b405c0d0b085c00315001 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 674832643 1250 674831393 674831401
    0x60f1205010b3a020325060f0801091509020c101a0616050f030f070605060111120f0c12120a050f0c030a02090306040b060a05041422060204120c090203 67
    0x400c2140d62803410703c1041c14401a6840540c01060126040020340c1842000c0250b11100300c00304d005884840c03164000205a526100247d840808601112001544a600400c2242110340000c009030440200210445444042500a983c00801640c4842c1e02c40c0350740c180d410070640714507155400030902c04040303142c148000a035140300e05a081e60b00720111440703203002d0103000d1056100101909045a50302c0e1110980c408041d041914199030340c6180200056842d4013508505800482442c090025070040604007051a00100701402c5c0301c100c103201c02c80c7d070b4800410541d01e200100031078042c0c813840130300352440c01303070301e00030140300f4200d04200034000b101c03428054154103d03a14200240d100d654408262000303000c2c51801aa16218480030702c0140700c2c45d981094029101a01e04400d150b403564240710640380c07040c50650001407882c000941c00c803598000eaa07849031143e004d0000b40c9030540c85d01c5040e80c1243e040403640c254480304502c10403544540c148020401b074907055003540380c = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 674833893 1250 674832643 674832679
    0xf0509060301090c02070810150e09121b03030f161119060b06031906082814100e1c1d0a0b0403031d010306051c0303060f1205010b 58
    0x70601c2a440c60b03e490b501d00141e40307402030103c02e010b0b040c140e0840d58120118a1044090a82d160301c2c1e0312080c44540c1c0119a84d80c80342055803049540d01e000f8003103003c210341204116400302c0024918101d0000484503402420300055000303541040090120303051022080722010700c03180036401804001c0a101c003030031002003401c50800340c8034030802851003990b05003d0050038a50400c40e51200b0000100b010100d4010380120030b2196800c020085182ca8001443d0b9401c0c8466001c041c1900320020503020310141c0700d109812502c1030007011940361605606500d401c2e80c400710010300d191504141142c40d80100040c1304421000d580e10340c010002100702a1032141004804050503072586580142d81d01c03500c0044c80104a00440c0d9036960f642c0c2d050003008801c03040b010402c41200c0044640030b96120740582d0f82903507030081404080e0003a058800d450051511022024142c86100000d1202070440c1102d0042c501090203041e5010b051a095003116800e12100344107440101e1076801d100 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 674835143 1250 674833893 674833897
    0xf0e032a091312120605060403031107230906040e06180f15070f030912050703030510140919090f03020c120c0f0d0b0106030902011103070b0403030902180411010f050906 75
    0x3d00d060003a20b826544c401324010f0140e60b00000d030008400540041056406020b1604025460f401c2e0346010340c49a4190444004400701030f54210462085228585000c2383d4407500700c04001c2c00010481c0300581c91508005048034043c440b55030303041725000300010a004110a214140000e800c4002441c0034414190070050403507010846c106186240c10b5001e5809200c4454100d00d0702e079442032080c04000d00950204008130002420800410750001d10070403000290341c440d10b4504002c40d80e01d414842c10b00300c010900b11848202481103007080c2240d203e011812801040d04552880365130070043e1800130060304460003250803d4403109200307400f103115448400e040312080903500c0d05400050001002d03070405441081707280000101140c05900c4201a24400c0c0c82e00002c40125664403034590050301c00140100b151b10740001c00217072190b80445581417004240d5131181d4420304c0c411130703d00e5003110102e03001c1c01500417000700c40d0b1700551207080c0102c507850b0070b51400c2d45031000b040041c = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 674836393 1250 674835143 674835173
    0x1214031305012301091802030a1b0e0405070501080606120105040c09080f031e1204030c02010306090513050f0102091f11030d090c0b0a0f0e032a0913 66
    0x252004900490401c14290410b2020000e120005600c03621a040b80740050f40003846900d0350145840041c007100100300006c13420301078004019080c81d82d0107031104810740e0341105a200f2084080d000203e168100f404d0300e44c0c020741c0650005c001480c20716001515140000c1d081503c40c103002d001c40111000310114490540314141c4005c101181902d03010744d0050a66007080d4414016110703151420640000900b40181d079051601400b21606a5008000d2050611000f10b8000560008000c2401a2002e114461041c0340020b08140d851100c0b0080700c2042d40c1c0c0d1165540c0a04040c028402e0402071585041c19010085161291020000f004d40c0d201403c80180f0442d4000c815029500454449901015510a5035030750081c061204c4000e2103043d800302e07010307103405e0000b10381401c040040d80c3c4516102c3e00d40300700c1c12140050a480c04450810400d0b4103101e10321420440c078030170480004510f10038181a0b409261507030704004200310014074a4940d02e060203401404030b03011102104d07013 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 674837643 1250 674836393 674836411
    0x609011202040f0b150c01060501090302030d050a1202040b09090105091528031406010609031211011d0d030f0b01080103031d0405130506100b03010515070b070c121403 74
    0x483c4008080c03540150105081c07069110f0512004461499801d1006041a00c0d40100800513035480d080191080720f00e900010b90954002030242c5051401a030060a05030300c94100206114130984400c026030b405074100d0f0550044c040ba20095904100100c00d014203c205e0301c201d020300d400c00440b94032070f01413a41c0070302c81c41c0b450006810280d074110031410340307152075022040d6030b6071281006082d1a1401c140d020a910400c8000140207110328068419a42d10007840080358400d03c00407142c8280744003000079155600d40014441040342c040100c483c0d94400c014014254a012014003201c14410040c0c20140c2004446100743c1e034000f4425045d070340d041c00c03c65048004003d030003030303495488020103802c44e10784418001481c1c010201038034101c3c07051003119040d0340c503202081c03001074061040303040c0c0d124240014071580c5806000f024256041c05003c0e810104c1e15181c440312000e007681c03500c000c01c002d50300031802d111010051140300340d540d041c0000c0c0344240514400403840001d242540c = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 674838893 1250 674837643 674837651
    0x10e100f140109051008010b0307060f05160b070306090b1302031b03091e031e0d0906110901140f0414040207020301020706050604150308070f1119030b060901120204 73
    0x105840903840000e4030108003501c441c4641c1c41d500c140b801031030260741180341c41c3c080c03210015000c01e0500841007013000183c09042110301d0507800f40d0340c104480c07039440f05100382071045404d03400724582c3c511005070003406d200c442e40c00d00c1a405012076485400141005080102d407406944903c001d18080404c0c4800060b540d61390890300704608010349422458418002082c41482180000d00840e00c8442d41c81c100d16003921b4008107940e03807090000c0c0403100c0424040740c0660440c08006420000501da4011806040301e507115000c88422620404041c00003240800c40386d44e2000e103808000e290b24100d6890560803c4824210b40114031494500311221034000c0c109840b43d40540302503035405002036407115914501003010f02811101a4011407a201643e0740c0d080c1080040c0c402c403a08076043d00d180c0b0b09541c40d503500144650806a4000b1064006a800c94644940c0d0414018068884000d42c80c110300d440b1006c6107024109910030742246005002c0c0880e181ca03a420882e504030340c000307 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 674840143 1250 674838893 674838911
    0x31112010b130b13050103060b09031e0c03030c07180501031e030c0c0312080603031926090f010e010b0901090e100527060c190903080f071202010e10 66
    0x20140b840d500719100b0350002040041c8031948283d10f140644100f624240001d030748852a07001c19000d1a08ad00780d06900c00354074586202284407608a600428400b664010190140800e10b143c5c41169500302c15440b26800700408004d404444442045104c81400a949180c8520038260030004009022056242100701050b0080f0200c42c800c0382d004010115141d030341c1c00c140c40c900c5480d80d1003102080c8407100088441c5004400c80703003610412005403900c0c00d07000c6011240811940c041c0400c020100c8550444004c1101a05d0300c1860220010142407404944ca5803c0d5000740000351001d070305140060215a890b554039905403001c444000403484204402607161500c031180b01d103405458142803000904c2141014030752081600c0c2d400b00d441581c0f80e141c85c0c1d034000445600390058014000c081100b0485070ba50106581c0354a07020308000e4403074540211642c009a2009129603001030410208241a01e0380b1134000704900081126152190005450390300140444d20391560b204c60704 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 674841393 1250 674840143 674840167
    0xf06040f1e12051902150112060b06030f01210c05060c031201060206150a0b04060302030613110d0506011704031110110d110a170406110316031112010b 67
    0x1481460342014142e040741e075184074042c03d00d1340007031007400084883c009480140c50000401c0f1400894400701c0d41c110740c1ca0201c2c03594040e03078092030840c0d28680f14219102e0664400e4043d60280a00311461405035161600c11905418102c880a0b80861214001404600c0b580100c00440380107817921a55200c8843d5058294441c007412403602600d440004140d155001509920400703285072683c044064180400c12182158880c5c5070b44100100400d001c003900c00d802440e000780d4081c00f0740301106110304080c826034a5145c9201c01c50000480ca80070a00481d00803240c11010a090240b8200d90305280510903400003440542441081181e0030b0b072003542040070001c640741d609010840880c0c48841d001316580005a03440415013050051384000c1c886000700e4802c070029484040c00c1c9202e1380022101410000c0c010303600e10b0369a031402c1c2c850011a030000c5100c0e00c104007504100f0407403050050116900d1451886042105224080c11000f100c80103c1c15074850b082282c0d15020000c10f0 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 674842643 1250 674841393 674841443
    0x5011110050604090203060a0902010f02012a021c020d0e1f030b030c0a060e03070605270103140406051602030a2c1005030405060f1b0d060302120703050f06040f 71
    0x6c0d014800c00c000c04c94000c082c0e07404050510b20036030b150040440c01000481c240c0b401c40c0b0103800003c0714105007600701c0e002d4651401c513400c118015580105000e18035035a01c020301c0d1540c4005600300b0780304525569401034003c0c1a04504455143e4031951500742c140d5500c01d501003040c1450360700ca00c0c0f04c2040ea0100800d8080790002010031503466245c1d00d00414644184403c40e000b407040d1480400c4560081c42541d000c4d1300010160406450007060209202d8250a11141856920400034030390301010b00c0c240d440303140070700008200d03402c0c1883c02011400c14015002e003150130034002245d1856012080f5200700c82401c144806280280f915455510319001c0d4281e801180800d0031200c0d286c10a003e10300c900d01030020799040d5901d818034684004000c446060084d1f00c2c1804203d0078100d0500589152110803800080e00c613100c1d40441d25802034030460b11140c4c1e100c42410000c10204004403030100da0b075000a40340ca4100340ea184001c99081d460007c02078480609015100e080e6502 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 674843893 1250 674842643 674842661
    0x123709050708100e01060e37090302150106080c13150804050f15070c050f0a0503090f190b0a0c05010507050a0818060f150310020c0705011110050604 66
    0x6036107229940e280660380e0b031410700c0d011029a40c00d008001e040f5450610034902151b644600d81000c40e076030310030610384451221942d103034401c1d215007120340204500c0054100300382c1080c60004025440e818042e1521a10b112008101e00c100c07030050002641c00710301e80e5000121103000e6500c492021a110f002c065840d044500030a4103606070003e09a80b0a10706405a401802640c1c14140c2002c42c00d510307284010700c00340b03e40010301d011070300452058040036040760045094600304d40084c0740c0d00d03060082c020819221740d030020810f402c5a28042e68690f0000b401260081d510401810303006001150a2280d440020b0010a80d2465280a90049010154032100370441d5142911015000d90070040c1550001800100042c18140010781c405200b24071100007030006a1700c03142e42c6175100c600185100b41400807409910a41c2c2c0381002101700080c6140d1015072604a841812071030700c2c1c0e2030b902281c1045410408141040000320300c0d40000c1c0e040307030000325140d030302ca0f404035000d095804 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 674845143 1250 674843893 674843903
    0xe01050f091c06060807031a07090e07081f1202060f0403080301031505060a0513050901060f06030617010c0c0f0606051806090708400305123709 64
    0x550344612056141c010079241501c43e0900700304180d1a0a0210381c5c445090100400003a410740610b5591395190f48115032091540c58212401c41d01c0f0803000e01c180d40d003651684c0c0410020410301654440071104a080e089100d4a0b1080326031a004002c0b132003c05000b0081e00680e000520070b606070550354215405950007800140d81c07542c0d28540100000444029001c0491400020800510f07181d40c148040381d4008007074400c401d0a80c0b003880300800e400b400c002113a650f108000205000d250004400804158030000f03101c916101070902103c80e415006081c6906d060000500e1030b41000b429148035130003071403070852040c5603e011002800103800284c0d10100d0b80903101c40901d035681c203843c03181c1c0081e1400700312500c401e8000da0710307540250f5880020360001540c0c1201401481c080c503c44030001e2400382078025080b80000001010910203900042d00040d480007441413100a4070740061420810b080303140e0160380c0c85d0401c1071040071f00c1c41c41c07000040c5080010103015085600350b15000 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 674846393 1250 674845143 674845159
    0x60706020a1107050402070206030103062c1b0f010203070f0302030f0315100201051b0705030f0307030e160506270a0602060105010e0d110103200c0703030801090c0e01050f09 77
    0x41c00903040382140111440030307218503000841c203801c2500944100c2c1c2c5d80680b5403030859081d90f4072039014228902010f09131450512030303064400c6c01391207c5100104400b02a10042501d10300d8082241680c40c0d803035010700d100c0700000c174143e40d0010031100100d8005e6101301680f105864104d045104000d603440000d00080f06100011061120224a0b18001c458944002000303030026800c0c0c4504890300300a02464184110300e008903c002807140602ca80166445c0240c042036810b0550815111900040e40e20075642403240000c01c4003807209000d60303080d48000d81c940300c0002e040c0d00c1908070780e02904882c2512081300d0696941000741c513400042c60103541c680c507100e000b07681d81000d10510303000840800155800f800c1548004031426000b001d018002d1040a0054000d00900c0c0c0c210700504155034010b004841d58080038050410b40703a0084c000707052460400a01d08e44043e080501d41c1840c1401d0650000e400140101c854242824959243c0c507100d10030341100d00aa8034920b03080121 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 674847643 1250 674846393 674846407
    0xe070b160515010603050a0c02060411030c06071b050604081c03111c0605060f27060f0c06010603020c030306040b01021603060615020d0801090b0f100f0311130e0606070602 76
    0xe60002e2605070b45169604102e01d80d981c140d030301c0a076007140340743c0000740c2c0051020502044000d40e22400c5107902034110303140300050038045030256104030000c0c1d038034400c1d55000164140c0040a05002040c040300c4e4642001d060064141d118040400c0f2128007503610302d82150241e000340c004044c02001001c140352103141400c0403494650105459820725031070f210b00400c127803174080143c1e8013002d501000d090405840c00400040c503041c07180c6103910000040400300c403075580c1c00d0003040c80094102c421500e951024603804d2038188180c1010050500603c40709000322000007c4d41d900c11801c50f0041981140500140d040c1454009403c04100c80001c0200030301c90340340c024004031218111031781d0080303c43c1d50003240c45010b16140f11000590050040092000c289c021040c50a0002e0a01c0f840f200b06000003040300680750410b0012403010301d400e4215036010311401021401294020b4a400481101409860024081c00202c200e4000100ba401d8031480152110698000400c40d80c58034 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 674848893 1250 674847643 674847673
    0x4022b060f0c02010b0a060c06021c06081c02030403080304060c0909110408150f041b0b07030f021b090613020f030f0108070801090503030c0703110d210e070b1605 72
    0x3800d90440d20140d820681c5c001d0705424011540001c4690680e01c00700030321159a035a50196115811000b640c1404803505003020883e80300c0c0300c00408183c00105003841c0c2c4020000c1c00c9407011600030307046d508103110030004aa81c2c541240c0e80164402d00c0003a50741c105007010354190130700e0342150b4070707036881c204001641400020050081d1030042049440c1d4140703c01d21079414200856114801012103408078000465003204580141440004840040c0d191420b42c02c850704806015000640c3e41c0244100190301070100d1024854152050740003441104040340c640784000d03000a02850001d00303089c5181105606990311b034000a02071a98a0519500f03540350006c0a010701103103400381400014201e80144100e1801710b03804000307141155200500880150001079094080c800400180700d4186401d022034104540d007600c80040044406901d02c038039443e06100448402d241c401c00c1000028001076003800c450100301c0040d5102554000000700d407682910081c2540300b81402048541 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 674850143 1250 674848893 674848901
    0x504141810170726120307020d08011e0b0d0b0604080a0501060618090b151306031d060402061e03041406220308041407060804050d0804022b060f 64
    0xc82d80d192500c29112006a003c0c0c95845030b2044881a45449426010907440c004400b003010540c2020b0700d00c821032600d510240d0354402c889102c010780101003c48003c1c2c0e01704020b5400351039400d001790215842244000d214481174016040003d0740414081c208a030541c0002090740e0010b071406845d40c3e41c030103c0a60300c107110a0215115400c000b0003040a600c141021603160b1045000241e1581c40e1040401c01800b000603001d4106810420f20103400f50700c10000c3c83c1d400c410301400400300346007402c01012a032500608002c0082c841c0c030100f0000f035000a8a5822540484225a5401c01800300e140500250201104040404800c0006101a9401e00040c82c00003100740d0300f040c0c0e9028511040c80240340c4d540c0e90010349411110b40840d1260301e03025802842110920484c01500c0a10347c074141c03c80d4040400264404204020090705020058008015040c021243d0400d0760003d600c10300c1d2030416130300b035040c1c0007071600d01e6080c0000e054a52a410020411094207204d507404050 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 674851393 1250 674850143 674850149
    0x10503060a110c03341e05010b09040809010f020309032a04091401140615031302040612030e12030405060304061407200c1003110c12040617070504141810 68
    0x303172101541e0151941184010603103a031101e8021505540c004080b40c401145140954156580f190700c036400780c6a102440d40900e006982964495007104001000c0850002c10401150401e000303149464034001100f110445c10341c5840082c4419650300e103080011028100f950280c104040d600038000c0d0304110310382d290000802804645030b5040040100d14041c2d4034540c120042c01d03c1007100542e5030300a0b40c0c2012401c03020340d886004580020742501c02a40080e03c11401403408882015082004608072060540d0403d400035954028180c49000d5442054010303003000002404204a030f521840c02d61000203038221141c20101300042c43f04564100d4218002502054260740520000b144550f18200034a42d001350391400c0812405003501103100d200d6250180301c2511554800c1c0100704408021601c25a107480c9005401050354150304081585003101c80240300c4420b42c0b0104480c01da03070341224510080f0701e204003c2641e4070f6491f2841c6001030030760740a001c04041c04031481011 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 674852643 1250 674851393 674851447
    0x3100207031b0305040e0c070f030e010c0b1617061e0d1203021206060c0604121214040210050301030c030b060d20030c010f09180213061e08010503060a110c03 70
    0xc87da2200d188000c0d42c892000c01400740c0c1f00040070240064407400403480701e5030781854003030303a08031841c0d5840d820380c0000d40303c03c2e410403000320b540b11113581e002c4d140c804e852486000e010940d0401c0340124130f020301e4252040414003491400d1200545485510b030040c15401103154084006c03000d0024025005100c80304070300910075003ca1540d103048001c2da43c810f00301102800c0c0b41d40f02c561b10a000b0b13142c43e00d00c4a0500980030340025084e4000d02c181130111183d0003841486240620400540e100c1c060003400c00d01805100503c0868092041001600d500c024a1002620f510300042c0e91103a160000605203102c95503441c0c40001c12050342c3c07424901c240c089804c0410407000645003140011208400203030100f2007004011030040303841000e03002d010b00051030b0007a06100e23203042c42c3c0c1c0c681100300071980c544595405164201041400c3c4003075440c00d000b0319414400000c0e02e40c40f0103001b00c8074558590020074140920f0340700701c540c101114401c8942d20520710b0141050a80d004001883d = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 674853893 1250 674852643 674852669
    0x5010203040b060105072406051305010305010c1e111e0a02030c03120a0e0406051914090106092c07020c032107080d09020402030403031d07030203100207031b030504 73
    0xf29401403082ea016981c0c00243c0c05102c08450081005400d101c03802c50180c0c64440c10b00080548130308842c00c4a8100940300414107606505040742514108444401000201c09550100c0b45810905681d074008c1442c1928160368440001807900500401000401d410a005940c2c3c0d00e01c00108501c0030b41c82541618890b2880300e007015140c140009001d50303031030001c110044899118024411484500600001e00d01e9210360200c3c1030240141c501c140007803d101c400b8000700041c8030020505100403102c01c0720300e41c10194010300500700c2c0e204082e0740a58280040500c005022041c4c1c0c509844c12a0140c080c2c40c10749802582d0349071000c081e5000c0d0040c1000211646071007210000c81c007a00095844c586090342d0b488001560160406141160b92450107200503603642c001107001c0c0303029036000b044c1c241001d0034017600c807101201143c0c1c07164801c0d90108011b232808a65004010b050009c0140c4840003800c0a4460301d000d401005c203100072403103000d400c0603044070142c400d485410100715 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 674855143 1250 674853893 674853901
    0x1a0a0e040e100903180902031b040b04051005280f021515010c0c1202040b100c0b0a06090504050307050705010801060909050417160311010603080d0e01140405010203040b 75
    0x401111046810402181c114900e4400b4541c1d10340c00c08402a8031030b2a1241000b03010306001404d2401c10b0300002010b039000814040d040111583e0b0300d40c0300a1185001c0d14141c0f030440b014040d441144101c03170182c03164080d805507141c0038009036141241c61002c800034003003800c9410207103142416540c0011480700c80c1c0180c441480054801036005899182e840c06841d00d413000d41000400d0213a0783d040144803001e51001594801c1c1050003008021007102d07520820381304001c140d51416803000c0c011051451141d081036070040603204c9494010344051021780b190316a550250100790401e0071114145428001040400401030916601503800d0301c811940728001101c5844080c0f080d0070002d901010b05001541041c0d200720f070000d01c500c049120750b00c070940c40344205800a0704420801640c1c2c0740b900060581107440004002c1408000b045694155901d030826405022091040c150b614803440245940950190303080740140d0f40707040300900c0d05161480c003130352003214111460120b000220f = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 674856393 1250 674855143 674855149
    0x31e06061206080a0f1e061b1d01081b070b1b041a09030102041a031008070f091104091d0c010f0c1e0b01150908030901090302191a0a0e 60
    0x2003d6610b44409420510100d458101400e89003810a4801d00f00103c040c0040303400e80004500e40501c00c42011540c001000138040c01040c81e41449004c0c0200046000e1088020040c01d504240007400c02c0b1505403141c2280580c1c42115a2051081035400214141400741d17501c4864450050403031681c403c3c52103035103d001030340100e22070550303559440440034080c2040354014080c2600090300050405a5032154500c00055041e041c5a0500c000401d005c4007200c81010341c0003604441000301450f5180c030714140b401982d20310407900a0717a99004542c0c3c0d00d414140848000380300c00b0206200c000c0000a000394640e02062200141d4030680919185e554042d001d4900b40700d105c0e40392108150810b071103584181030449001c0810b00c010852000001e8201d440031400b0304100028000c1c1c084080741d019045070a01d0b044440d01343d00500507452207a83c8645c004094950680714000182c1a41c40700c1c605041d241e411254080d00c80884403a443d0800c80041d04840c01c503942c400340183c20780424 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 674857643 1250 674856393 674856401
    0x140a090509010902160803071809090204050609090607210c050a021603200f030a080903010c090302060a03020c120706090312140c090102070b070506010602010c02030309060a0c031e060612 83
    0x4038544800c0e021001c0f85c0070540c5072010395230010090515450706500c8100da00c4900c0c40b03a400a035480c1c2d9a41850f481941000e101c0c06911240a8451403481d0420110241c0c0e9054020580404c01c101a0507004c5003c104024a02c03800b0941482030000b40540c801c040c1c41034001041341e0006216000030f4580300242c0101c2081266002015120b00d4076604540f00d004888140c1e500da086000c80e000d0201c241c030104150b24210303002d40311898032281441c0416003510112020442000386628050001d40d640500b221b032902c420f070a00680d1848100c40260400041280d80394038014080751074401e00810390450790045103e9a2520003101010203080200c80c0b00500303034040d4201d0900000d06c0001c0d490001c00c00305005004850310700707a458584408a500c004421101034010000401c0925024018120041c1e824000b039420361611101c0309a0f10781004085100040d1a06800380d9240d0003a840103403503040c0146074040d00301d01c20300d8100150405206039000a010349001030705126980c89 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 674858893 1250 674857643 674857657
    0x10b120a030512060103021606091514130224070501050f24030309330403020d0b0a0902130207110105030c071113090b01060f0c020a15140a090509010902 68
    0x21007500345a0035581609001c4402050f1360305166080010180314126019003482c581c0c40b40e080800d101d00945000d4124010310034a8246541c00c1c100608161100d0703603c101e03441900c94031660307540c2c5001d0001626100301080204e4100c1c0c8200c91842d40d281d520002002070750300500090025448003030588841340c0c82220300c59008802c0318028413000002460190854074001d00701e07800c000940c40081e41c45451201210b81141100082141c5800254803003070328066000e2105050030320b10340100d841c44920620040c00c000076440003540c09501075000091094003e01046200074600040100070741c0720240c1504c28155100301003005602c5070040b00d00c03078248512038a0600c1141d41d50409050110b01d90103038420700402c281840541584110007156008860845155151450141030361480c42e020604000c60352444c030b002341c0c5900110f42c0071103c0044902c0f005040e00b1800711a0685100c0d070340040c03078500003105d100b8540d00c01c1c03542d000e4a4003107803120078590780d440f1280c04a200346a = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 674860143 1250 674858893 674858897
    0x150e0d081321020d12030e0d181e0314070b0d0b01080609040c0909140a060605090f0c07080f0d0e071403030c060c090303043308040b06060306060706060305010b120a03 74
    0x4280c0c0e0014407402e511448032112420040740305041f0607009070600c600c4154030342c001119601050706401081c1f080ca4000e01c000c411400580c0d046045101c031029040c040075241c0e041030444841c0c83c1c00d041004c58020104041119118100e81c0741083c007030241c05102d00e002801c854041501807514403d0140525030089181507a80d00e01800640982181107040c3c0e503d02d000c0002c00181d80c818800301c50540c0c42003500254180c100030410101da5070151041500c104510204002400c0620071a4003883d00300d0030164403540600319110451081e2190888442d041100c0310034002c50000780c1c4015102d40800c0043d04042030300905a0381e0003517000c550540d51000b004030340600181d400070112500007400780d83c502a210081000480301d070036409500503111002d001cac51a003405a060030902581d10b0b000c2d00f9400c00e601d9145985030094003040c825000080803da507a5240c42c112004658854402d0000594a081140c000e020130720781310b4014171401c020002c8490700492002041036050b = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 674861393 1250 674860143 674860159
    0x30c010c2d140904050c090108070906050313060b0315010f0501030b0102030f181f08070806010e010806012114150306040f170304051e010204150e0d08132102 70
    0x44030003142c0ba052241c0b01156500300401000840f510303607002d0705104651101007035036a6114a000100075040060200303081203040e140038400240d1050450341c202102500864440c509400d008000b0003003030500305d50503c500c01480c1942c0f141a00028100c52840301c002e028160f40d440154107890200c41d0381030040e0000c10420240c104944081c004209130194188842e072038100c0411141082c0191140384c40c954051000d594640c41240d05074018a945040d240034285840042c1010b5008821541400b5411001400a07440b03040303400158055950a841c00e24500c80c0d10100802031031070318900d96010003002841400c84040002d54000024004108a0380c803500d45042280c4219000c40d40f0b121580710181f030009001000c1c2d030065029101502083d40d5290700c8500d2100f0b504000252a401070000300f24091248442c00c0303062102c0d042c43d808c101d481c100028440c141c03841c0c005001c1e01005c00d0140e4258808088001030b281800071140c1d0050722800f07160039000541ea4000d500003070f2 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 674862643 1250 674861393 674861477
    0x15090717010e21090603130c080a1202070f0506031e13110a0302061b0304083a02030307030e0307050f030316080f060d031806081005011107140a08030c010c 69
    0x3a030085a2203024541031007c0071010340e4800701a0381803507100c0f0b0030b668007200a000a12104051005224009000030002146081255405160a4810795105410100000302250054101103c3c24049469401020300c2e2050030a185424012425074155510b011040c02ca0300b031080c0004140e07078005100c45e08114540102c032951103038000e40c0710002c3c08140000180c940081148104a142e031005000b0405101d8200e1410030a0348030900d1800000b0010bd1850a80c02104494000800b480c0100b9400d0540000900e1071094080c010018481c0700c03203140341240b02001030b60184220000e88280312905110441d00325501307548489441c50000b0110f451842e01102c03000310280700f810094100307428080c2000c20100140d1110000c551000104103c6503001d1030560302034002400c24502c2d1140d203010311540c564080c040d80343c42144050780c0c81190f136034030140310b80282400011241c0d00c074026001d0601a0041c02c4080000c24100c46180440701c0140e0146180760080d00c2c1c1c00e540f5082 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 674863893 1250 674862643 674862649
    0xd030e03040b090a0312030b130218040c02120d0c0207050a0f0e1017010504030306080f1903110f071802070f0308072604022115090717010e2109 64
    0x210120086501501340600040041c420001c1c0d04005141520005600c02410040c1303c144100e140c0c3d909031591041000c0700040c01c042810420944040d5000140305140717180592400491414501070418003003070b410310010494203e420341e100994292591142d407034044c842000c000d030143e60040c800b00102484280150a4140e034001c0102000a004541d034182d031001c0000855694015651a0070410041c5034160089100130400400200000c07188401d0681d21040820001400603401c02d82d00c0d41030501c56850042ca68403031a0075500c00340706040000f0b0f0b490140f403103410346046003c80d565200d00014400d444109400603c209001c8071180d804a5844000030301080c10301550003c81000c8600d6503600b21215103884e0200702007418075004000400d8032011681030302c003899001007001c0c0d03000429005024802c2c1c601e145034030748400084a0800039140c101d503040110220511903600415046200002e4800041d9030103024084000a115482c1803040368584108001514080c1 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 674865143 1250 674863893 674863897
    0xf0904060e10180209060a1808030315150706050f0a050601091a0d1e14010e0105030a1214030f18010c1e020a02040c0e011709070e0901021909080d030e03040b 70
    0xf05590b1401450002d00c180010903c0d0821030071000050300124205d110007450040b00360203840002e00541c1585050701c82c03052001d0003e00518040c07909180120201140d02c0305840f076941d03000d00144000d2906807c22032036540103c844034910381c20440400c2d07242d4081d01401c1e013541c5075900b41240681044000c4501540300c0010500202da44a0000c611003044120400c16910710100214503155044203041c02c58106030001c4000b001d41900412441c1e50018420a00344d60182910303224900303582c401d850b00c3c10440e0081c071044400004002070708641501c2c16110b40000411001580c0110347c000d0f00703d40c9000d0500307001c600c44031449101c00c6920740d42e058400b521441100e500341b100350f01103070548200d280c8803800b05030034a042514568005200070801001c000f02000c1c14034002215658900ca00d03c2400700d541600404100610300c01e40455400b0751000001e40103d2690340d0005190140c103101d84042409600c000c0c03603083d44039004401f001d0b10080300a41c2841c0c00c0040703072003e50f = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 674866393 1250 674865143 674865179
    0x290a060317220b0301180513030305040503040e010308090109123504030b01060906020d02060c1303050d02070302040506180c0c070e15130c05070b0901110f0904060e10 74
    0x69a101c040c480d900490300100b040142c064000741d030380c8a5140281c5400c503103a00e03002805103241010304011118942400b91034500d5050b203400f0800f51681e0522500f50710681d013146011003040d40000c414841101d00604e001c01c003c0e82d0350651981e64640344201c0100111000b804443c40561240008042c810201088060103144401610502ca198891513201c0c2d070085602584032801042800d80050b1118000c06060010f44030302004c0c95802500c0d01c4000727084c8281108081220701002e01503509070710141d54442d0032588440e21300c840180d566055407000302c1c07049080000003801400c3c58000c0c10310184110401d901e1585400840c0035449c0c004500426141c03180e2040042da4200b86000300b8041c44001c0200e01450803c4800d100c0c81c8080751856642c03da05012141880d03642c006d0842d05101d40001c0034001da034640d003403403e0147c045110011202d010215009640b0a61000108a4600c08550404c001030b59051000c8181200300e07094140d45641540821440380702d40d14822032 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 674867643 1250 674866393 674866417
    0x27280b040e010c0c02030724050a0c020a0e0609181f110415020f120a050a090f0f0e01080a020d121b0c08060a0b06030703110403290a060317 62
    0x4011503a0440741c21030301419809400550800c428000754202400400040e203580c00d928400f042e10618103804685aa05245040190000d000320300c1910950200618560040c100b004140d034809107500410400d84100f0301c01d030001404940280e50030505490340e060b000000e000c080c040f0110216943c050f0f814081a41900d445c03060640280200040c0003a2003c4c070403141c10403020340402490410b07018440c500f5035008030800c1094041d4441518501c0d1401c0c903190b80e40b4010745904541d09061a80080f0310707019001c60204400308a2428501a1545940d03000d02c240c0c0d80f499840c0d586c00450354081c2d0801111407c00002c61b444071070040c8101300c1c40c2407855100d90105803040721000301640603100d2049841c401d0110741400e001c1c130b5400c107202d268188003003256640026035a2001420340018150f07102010703602c0280003001c1e90000c54100c070311000300f071607088a1f0b03294031120f04040d501061900c0f000154000700502c20a416260860380250700311076040800d046580c020580c5d508 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 674868893 1250 674867643 674867651
    0x7030b011d2502151e0912030a0c0c060501030302060a0c0c0c0e1b070f061d060f0a09140c04060605190c020d080a020d030b03010c080610050927280b04 67
    0x900781d13003906942801489602d0040c42d42040b42c20303c0f24109200601a40b60580150b1801d074040361806099940001d200b0000003001500c450703066504520609004004605101c0000140754003c0b030030758460b02c0091001d00840c840042d00700c03042c01d180d410007845100541c2040c00130300b04001070a0760150711125030f60281c0c403550303103240c0e0306410038032048401a01c420300305c0040101c2401a411f10300410300c00b120381c042442903c9500c400006042501d40441c040002d090b48581c1e4102018a0350046000048411080c000325190f80782408654003550030800000348184c42001103d11040c2c0b0400640d03100c8402c0c1c4000c032405090780c0300c2640d01c900741c0e010202c00b0030352a07401080000362540042c0b284002e40040602900c50028140d44a64035101d0310603210784e00301c11880d0340300700d045034140d113543d1080720150703024007a0749826a001403065540d0030203031044400f4181101304140702501c460765400b0082000303150749030340c800300c0c44080344000b149400160490283c0d807e0050001c1 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 674870143 1250 674868893 674868913
    0x2190e0a02030c072103060909080724092012060f0c04030212010f0e011a2106090a030206090106050105090f030a1e0b011a0a0503130507030b011d2502 67
    0x11940d4118841e10641c11700740d41e050096880c1d098031408004282e03025085c450212213444038000360040d02c02c05003525004001e00414514001c01c0405280b074400c804101c145000d080c12100c80301c5400020b540f007044110030345520320b0704031002d0f080c0080b0480240090760707828480600d00781015114061040c024440400141d49903000000f084a98400004040403687e0004e800c1da031182d4164000c0340d140aa5202c0c400b0ba9000da1102020019208400c400e2548030004a05942280b0030302c10302c0c0149000c2c400d00c01000b049800841e4080d83c22900c850312041089401c0790390f0707445420b01240c0f0400c01c186d10740c103040488070080c00008040c0e52042050303840c0d0441d05203500410454034600d103201d0400f00440c02036414050103400e07410398041c0c002600901c07068030401414074107110380880081c0000040c1100040c820350b100c000d50303c00d180e0f00d2600d1040d0700ea0a005904004040c50900c0311000b10800d103152140e00b000c10003c1a1101c0c0400480c0c150001d00312501c11405009004 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 674871393 1250 674870143 674870153
    0x30903060708090c0406031e020f040905010b031b010801060f1e02010507020712080d020304151103070e030d021510080a051b0604060909180501090f02190e0a02030c07 74
    0x94401e40c495200c4055a00c0c040c0185401c1004850806114501c3d0030400d0002c10076003503010030700e481102d205420117246400051085811040b80c140d005040102c1801001010740103104400401d42c1152a000d45c50584049091130121402d400900183e004014451251402b00e4400486040071100041c10b15240440c82451514910141c0c2d11841070080c41c0350304000340c40050007203075800880f41e03526640b403241e24403030756140504407500400814140b082501c404503404041c0c0701c0421151004201040040d001120303000081020340381140414100850304903180d000650150281c05040c00c140b400d8080090701e0710403560500750703001c00d900404000f8095500e0051008068418583c1a8031038925605000c05001e61410b00040141980103100300c070586529900c00300e01d05e40c0030140d400403000320b01d0000c1c000b9030a12440006100741c04480d03500c094003d44440000c4a40c400c0240d40358034613072103000304d0903515900082c989071039035024581141480011034600000384c0c80b4 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 674872643 1250 674871393 674871403
    0x1140f0309070e0c040e1f050307090b04060b030105010503060d060b03011508010c050f1c15170d03020f090607020411072003160b090a0308041e0b0c0717030903 71
    0x40d00300682c0b20000c00c1c004010224030711644002940e11461600313080035800c081c0040302801040d0440084d080c03160301240c200b0410340180c2400350441d5021541d90707140300c01420800642d5030040f13203449008500050351000700c034140c07001038407440c0c81c42e19650280614405298015680c0540c1c0384840034a959080c00f50380e240040d02001d400e91682000d02640c00c40e864901e08100b800720401001a43e10382c40005e513840311000b145001504410b69a40307c1c0680000d2005007268010488003185814102e205011844100702c102d40039a400c1400c10f4041784241d00a0822114080c040101946400c000038040310f80b0107040482c9a11301c1d0912107010380c1040c8021a5848104102e910703001010603107050301c00c21b00720000c1c05403201c800100c420000881c0159505001d00040f42030550325222440070045510410303141d0340c1d90f9141c1d03148441c2c22050001e20075010300300000141c1c404441c0103540c2d034a054003024014a034500100381d04250070a01c110f10b440d00091010f20a2950140300b = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 674873893 1250 674872643 674872651
    0x1305010c030902011e080103140a0c0603020406200c15091008090607031b1101150305100c231e030f0411030a120509040608100b040c09030b0601140f03 67
    0x340840d16031510f1001410000e03890349101d001d1259243c00282c06a40103854504598001402c0c21030140b0034240c07a070502681130006400b14a800c1800268181d260340200100d40803581c0301c40c5004602039a0210380d503144400c8500c9176004014441d8249400c5507551441426100e80c0b502e0482c0840120b14454003112603917010680d64010400461418890503500a10900d0104400649528000c820f510740400700c20400c815003000102d410380950010402d010741c8501074001540c0c2e40743c50b5507030b00d10351604000c4040c209003400b03a143c1d0041070701140c10942c3e1184100ea0718004440707503086401050340c800820751442030034107000264500942c040c46400c000c402988c40c00e400d01106054008101c14000e5001c410301c4402b040c2214041c000b05000784c5006c0756211b11150024001c0c06443e001600e039401041c151010340c0107564802c000710303c826102841403d010306002d0301c01d103030144806080340c1841d0000a03107942c4513000e20141c203a0708800440c10815012880603080d00304136 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 674875143 1250 674873893 674873897
    0x30f01140f1803042c04050a02030706051e070609020603010b070b070e0112050601180608040c140a210b040b070e030c060909040c051002031314010e091305010c 71
    0x210500202032030880314035601c880710900203400865400702c410f590744194070854801032501a41d18001d01d462510700c03084100481c083c2c024074201401c0407501c902406c03100f20320901c1100c0780010070701e0043d01541e0101c00d5091000541c2c041000d9440d5481d40184800c403001507031664a82c00507aa0384010f18047d01c0311401941c1c444203a440c2c81d40042001904450030b100d0b80c114079904503a40801d1441d1400d0344180c01082c943c94410040c1d6071a001407280c61800c1110380e00100705141d0140d0b045105901450320080d0090b80d4040070701040035582d10054210700c60140c280100c002e0622040318400806051012005183d1545220001c090700c0403a000482441484031080e40f0031205071a03008210040c18456800c803001808910540f403240e406000300000040c14450b00000f000f0013868051302000380e07401417410003501c0b0f0340200c2200c44140c003810008500303120503e5144698041c180c41c3c2041d044482c80410282c03c00061040e60380400b00c940b1000010782c01e020f4085900c03401d03 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 674876393 1250 674875143 674875181
    0x21b0304080709021303030e04110c0c03100506010c1b0f170c04060b190903060f0b100203092103070606060503090106140306160507052a06190509030f01 68
    0x216480a00305035541e0f001e24003040c010b006540922854100c804100d07039060601100c50254003006c60060024810341c05d0f84c801010400f0700b650310001c40d520f200600d0071010345200c600120500d90464009643d0103000512560007400090700605003404901c0250f6050300c0840d603141c070101d41c00121600b2208d07940c414603c802c91134880c10420000c10f1002118240000c2d800e05102a00a0080c29041070300301959070206088640100380355030182d900000c080c020328450201200180505140481c003c1c9003001182c049188080142c070300014008140d00c1c26902c520900c00000310b4609401d00e00e40c00700700001000200c2621510008085540b621903c0b4908640c4407400c480c0b4550001103110440000031086680108034240d015110031091281010502c40440d114012264003e00c0351144282040203038120344083c20045d4103109000d495000c07090b0500c5aa4040c0742c1160321040800b403603541c5407501450140c008084060111414080c14418590940d20300301460141c0c5824 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 674877643 1250 674876393 674876399
    0x2505220f060516060b0f03120306090f0403051204031b06061503020a022a0a030b0f06040905030d0506280509060604030203030a030b0d06050109021209060108070513021b0304 77
    0x400c00c000000c01c200d04000e801d0202c901c1d0481142409050010013065135428030000e955241500314081c00f0010702111075800240d080014550301c01c6d215548105074010024581000c84009544034551581d00c00e8186859400c8446216002900490a2050340442ca48400d83d1540c840c061070340c004c0c5c001013849403410811040c020000100700b0101070042182d042e24640010741c8014010703003014121000c002d040042c08509120000485e88044450f1000085c4510380020501400e61000c916000e9100c410410040340e104a000500c1034109000808081200e680025848038020708071148032511258481e40a860445031801c0042d02d01c0000e000c1401d046501e2544808159200d618190441d00029501d01403508001c04060310790420305116243c0c8585814040c0e802070043c02a961696040400b9401841001280801c0e140c00181d08920028a007030407280741001410b0b00ca0b040078240107100d5401c800030b0007885d80800c1600114004050f091181100706405152100c2c1 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 674878893 1250 674877643 674877659
    0xc06110c1507030501060504060c05070506031e0a0218220f0903030e150c0d06120606150e090a020f090a08071d15010f110105070306090e06250522 65
    0x80050082c0c010186400c0060202980190454040e26980d042040c1f05052520346940303008180d800091b00b00201100b8020030003505814200012006034500a5a5940c1030f0350108030701031620301c0c40c420b290100c98040b0600f08440d5003249507000d9807500c001d907905a83c016080d01c11a280700400641c0c1e818821041c90782c14420741c004d070400e21000d40300000d8001560140c1d40000f42105e0001c643c005a00f10f2140003652001d0010654032070a05500d044034180140141840e1154000a111503001000201d11031000b150300b080004000c0883c1d03803123035441403000750003076044901c0c80c20040224000c1640e0f407480480040c010300c0014411a42804022021001660100040d8074045002d101051001c20404082d004086c0b03454801e0743d940e400100c5081390452030b0301a29500c2c00c0180414aa41a0802000d0f03c1822109000c004240d40085961b00c40c225608000160314110342c044080307811500a101003600d02d089424a8001070390a0b01000301743c140056440141c0600f003040c80 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 674880143 1250 674878893 674878933
    0x130e1605030c090405060705030709030b040503031005060304150b01020c04060803090312070f020f0a050d1a0705090105030a02071712090c100e01211503150c0c030c06110c 76
    0xa015078902a65044c1603603007560740e26000c1e00b54420b0050100c000f960300780c0b040c4942e00040d038104101912a0030641800e5880390f20981e110714003010036841c081340d10b00b041c10807240101e90001e1000540b980b4101701d500140410030805046004228403004182d82e14080d00c005020810302440d1f46000c038074105131810b41591207a00981000b0f002041c08a0748115070440c05030740580309280007644100009814095541200f94042c00410280040c05011113410b203608101511195060f111100c041d10301340903c8043d5400560100700103419824150080c0c100313184184ca4498103507101c0d40901901c1c2c0c00030480f0701750805c02c8004001c94400104100d456004003500c24969464500100904121420501754107006084052442410549041c60b0b12403549000410803406420601002c000702803005583c200715050000803820001d1007015400d01d510346038004051704075038064548102116007510310999458003049041d00072802008011242d401504034000c4858414507a5 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 674881393 1250 674880143 674880163
    0x1c151e05040606050d0b03070b18040b03070f031421070b010e130303022b140f0c09010c03020705130507200c060d150f181802130e160503 61
    0xe0740c2030080030070032550058125a0f491201e40e10104030031141d00003282c80c5c11380d1a849108142000109006440746d00c1406c1c0e01603110464003408582c040a080541d50846402781410302d4035409007c200080d2582c401084000c11901541d01c46202000301407103504148001c0d5080c1540090903e04100a0a4403a4090164415001c3c807508101e010950810314094008090650024800491144400a014000d5103080d24605034450100e0b02d13002070032103d1030002a1403403040200d5964030500881c3d904c1599491030450624901000440b0680c00114081e000d41c0030f01e01c00071070541ca40401d000107140b0b0810000c50b90f420003500003004445112a42014160078101001e248040460200c000710401c86145850b42000100c40000f000c082c81001c00071510400002032170b0701c588800c0d00c221000c903604448407170309540d000e0341503603024035848140061240784480146020600e81c4802000c0000c0001d01c0003422035041d1801030040388960120010700750030401464200305038840 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 674882643 1250 674881393 674881399
    0x30a09050c0324071112030703021204081e0702090411060c01020c07170f0d080c0f07050d021509060f1b130906060f0c0b040501020c0a0b070806151c151e05 69
    0x1001713120754081600c42c6115007648000d10b50020106250070b209406890114108841c110540d003841c0c0740c02050750f4407501040142840002c40801380d07101c8042a101c181d500a001c2055a698903581c95085008400d005517100005215045000310248007608010748400002d140090900c40200751440301140b8101450b480107508541a80c0e0208440480090742e00f81410107403501c003080c50303050096524269036084040f03401402c1c00000030340198081d034140c00360303084000ca07440610b00d8544c08990f001d1481e031004022a0103007072070840495120160703e0001241800350350703101c50554441503010101401000c01800107014902c500c80c0100040c0c1031040c520724807010042c0885001100c0030f00703104001f600260a110013901141d07030144100302a00d6180e10240780080d00301c1d606480941c0003c4161001407050309128900e0606240401421810b01010032030440380c0d03a10070691103400517200c7e019444400c008640c610054081018a0381301c5a03031b0340d111002811400c0d401740d44 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 674883893 1250 674882643 674882657
    0x3080901061202010c060b0303160305041d01150c02060f16110a080d0804110409050d1803020d020613050a06050a0311030c160c050904062906030a09050c032407 71
    0x10050303800c2602468541c0d0300407800f040845a404c0009e05501805200e0105405280b290ba401c0503445001802540c05014100c4010028a031030943d220344240940b00c400440500300e07808281c0610501c00b095440100203500d0b0007402140880907420150310003a01c0b10002007a0b030200702610815542e401010344580c02c201d03140220b213035519001c1036001d100340103107031004c2004d125a007400c00301101c0003d003007444042142e16003e56940100441e200000e0784413241c01145072a44900002140e400504c000d00308c1e103168081000d290300490a8042200d414080020141c561100403002410319882d6242c039001d0180000d0240d458a01c0b103000c5c145410020850018046400c0c1c2c0c0d0f03c400e43d01e1070840000b145107070400103007410b0381115030b01811b80402c20003001000c1c1c124100c0040301c1041e4440d01076490700030120048203500007692010090000035011440340e07026600050003601110b061282e480042414070412050860f030040c2c40701e151900360340c881c00002c6e400c102c0c0352a0580d = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 674885143 1250 674883893 674883929
    0xb0a300b0108160e011103070c24030e33010303020601150e15030403111c031a10111609050a0605090709030204050411030115050f0d1104180803040308090106 70
    0xa001e00804900345050181701941e101c1b020000300250b4041e590701c109241c1ca481d445080d048847c19116a4900d40c0e40d00004502c3c40240c880d004010211158200a2a899480380c0c0341c40001003a042e0202410200d0403100480710f0000005a802903020360023403c159410039242c0d03100044040421424400040c1080c0140d803a030031103811000d034044044649036141c07450b0807641112410000310310b0348500124032034883c960012550343c000c1c050310200f2907002c0c2c1d145881c5038010b081c0d0f0400da111a04100090910f03000342080301b911a01c10040c0d4902c3c3e10860034a000c83c40444d0001d101a583e00c400700301841354588107080141c0700841c0c441030186031400b401000000c090000a0081d5204d901050410000c000300c03c50078040103000f070102c11b0524001180110552044c64030800307101c50034034114241480206070854000710307041c00060186090001030016054504402c001204021010803007000255019a10030340d19a20141856520381d030955642d502300304140d443e1041c6003 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 674886393 1250 674885143 674885147
    0xb04180b0426030c031b070c060909050408030720190606090e0715030b0405010602030310090203090a02040e0a0503120f010e0c190306051201090317010b0a300b010816 74
    0x10f25440801110002d580795103120902c071094141e80761700c0c54400000704070a030406c0072a0000105560340c03076035a4201c060f42c5a0100b401d031441540c0c05030250b0001c00c0801d024a22558090386c0a025005160340507140c010750341c46c9481101c1020580c840c046040010801180c1c0c0150001890000014000c25410413a55038481340d2a125543d2600404c0c5030b001c0c800b90090304041032600300100108490742e03459801a460f988100c070244a400b24003c4003007071141c0144203490040906e1402004410020b90900008041952540b100c6100d4001240000b940800040c0560344144c1100c4101d420b105084110b0303d0b8042c0c201450b01d800b036108000e04184541c040d1020700303201c503019600041d2101400e40090030950030443c2c0111090080041d04201500319103484ca02c2035903141e415482458100d201d8a00030f0103640b1800004106110380c0303510a141c402d140f040b0096800103c4185842c40b808031f09281180b6010980c1c07200c6542106680001c8007550040300c0680d0000c000c400c41d140 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 674887643 1250 674886393 674886397
    0x1608010e01110c061911071103060a090c0b0915030c09030f0609030d1d070801050603070e15091905041101080901050601140a030605040905010e0106050a0b04090b04180b0426 77
    0x206000400c130821400081c1102c94000c80c071b51085c0010915990f02c2681005c04100c00010792150080c0f04400104480c10360512070034016942001040c0ba51b00c0c01d0104120240c0d0011010a40c042074a07465814002c01280041d4040c040c50001c980d51400b600080c541080002408501c090f0011070030040c441001108691514601000c00100d0341c0700700170612a462104800d0815621515401280b80641540050700642044003103a0480d81e0300c0007500030300101100c808001c044545403211a034207144480320f8020410352100e04c598408555604101ca104460640306417040c0b5507401c15550f04a11903540005020000f4007035460b26100107000204d05030700b142c0c0310750000100e0f041820312035070140014000c000e20500949019050250191907001d031109000d52908000050703501d85118804225501d1041d100e04041c5000e8601c0b005054002305560403a0715514800620388000083d03001462289608071843d041c5424858240001e840a0718610341421614184c0400c070b600c2 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 674888893 1250 674887643 674887651
    0x140a11031c080a0e0d0f0e060901021509030702150304120e21240604060501052802151305070e010b0405090a0f0912020f030a080411031608010e01110c06 68
    0x52106040e1a064401c070001c2410f01d04109590207010f07074480d1704550200309182180d2150f5070b80c4405034240c5003040203a00c0380c142e107a40981e21056040800074840300c0c110760b000300c8005c2a03906041c2150082038003803040040c0442e1166002080208100e4028078400a5640d107140542c0c40a9218020448843c0e071002910f0b52111680b2200344500c0b006c1000c21404020701c03508504020031116844080350080c0d803c03a1046051040100700c07035120310252040700e405800c074250015007101c030100e04002424003000450082c0e0641d42d5600250900990003140c03c4200c130403000c1c82c0f40c00c2583c00c1a4007034111014151224004008000211059900382c8204403110301e41922506800d40003010700c5001c200405040c01c01d0141030250038a803140081c900ea80070346a4080bd020740c1140c8074840c00c180d42c00860303c0d08011402103800c0003904609080058112a0036103036161082105082c44d5200c4441a91160320341c04503043d00380101d195008072503c9031401c0004061042e42c46060040c = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 674890143 1250 674888893 674888897
    0x31507080a05010f031e0c120c0b03040b06010c05030d0c1d011706010f05130b04060f080402060d09060914030406030b0a03020d03030b0303220302090c070f02060a0c140a11031c 78
    0x101000c04120f0140c150001c100364087c3c00c072640030383d4035503210b502d0320098581602c404001601c0052060f1040301103a200e00c1d4440c4600303d50b552440c0c01512107038a00741c0165101d110034084075a880c040b0b446460905200c40d102c0e8803c0d54001602c2242410001e06410f04001d4464000300729106030031040c2c0d40000c000d00b420350720001c0e1058200c84038007940b1031204869801c00e00c00104000040c1c018015560039a0303039038200340c0301241c2c292541e080c140d40094006d0020008800b400b00d0a5000d5944a4403d5070089001c0c3c01a441d02d401003402e5194105040d000000c1c20844580c05200f44000c5607070039142e002c0f6043c07454000914498074203001406040d01d462410301d45940910448009000d4007001514001c0d0b4200d00c071140c0d0100e408124007541d40310380070803000403441d016148120b80c0700d141203d41000f2503081c0000c50b041403170030030103211a107503c100000301c4803640c0c1390b8400441e000030a01d00c041410185244e100340400796010b81c1001e8041224220003d859466002d154 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 674891393 1250 674890143 674890163
    0xe0108033912030405160e1f0e0f010f080f0a020f04150807030309060c26090d15051506030711070e0702030910051303021e031507080a05010f03 64
    0xa40c000450105055030303145503038010b101c80e03940250505000746000c0da000c1c5049408000c010920100c82e00d14034090350ba541020701d170002c0c1c1c030302807040c40105444070000f021540503956407010354807044041c0c402c07102c9002d0b0031005000412a0807480c0300103108480c02070110b03007941c0110a4407500c5910703010740201c00b90143c03040162581d4020343c0d042d902c10329002000655500d1107540b103000b01e000480019030071050003d0b540e803240a10055154100c4548590380c14000f98600162030804104078540800780706019907036407090b400d0350845018040130280700d11409003110880d9001840708010100e91000d00042d0340381d03041540d5002c200381c24800c21280080f80d081d860140a40d01210485640b0010841c26a902001500203100242c40070024a074801c281920710380229507280403da01e886604002600d410901c004040e18040c0b079000500701c0c20000310741403440c00182d4030f070922074031000d05c208a60b00600d5598000704110003040107504100308040040b4075071101410803101 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 674892643 1250 674891393 674891467
    0xb09030a0b090d09060206010b0406030515062a030a080105090a0b03011503061b140901120603110a0b03010806060618030d11101a01030c0516030302040e010803 71
    0x2004450281500300d18005114981003280e00d0b43c07140d030a07000707100080200d00c0000c0d10a000061943c180e650511300366050a0804078100d004100c001c2034a510080b11561001381070b140c0c14010f00c01a2021800400d0f00565444c45d88150300d042c04600407982d004100300d6083d158452103013415204216062890358946105c10b038060000d07442c0150b495440e201642c40521000b000480031073344120300500a101544001e10b111000d0340b003a850115251000119030401d0500041c600d0002c14107101480410027900401100e02940003101d10000034031500c0180d20741411140f00030504451150320f15030401d800355072115006844140140004074106c5031200e01c06114142d150806411510042400c0320000d2009902c4800c6061364000d0381c40816002440340514580f00303110000c0c408106c0c2e140001140102501501c0c042008801e02c0030a080e21940d2207264019400384d0340258540c0e0405419400d003039010b81c00b0550541c020000c84031308000280b014140c0055805002001d801 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 674893893 1250 674892643 674892649
    0xc0702010e150a031e0b031018050303011503110f090d0c051905040506030d051b0a17030105150c0613080904020a030207050d0801050a0314010f1a01030b010201150b09 74
    0x201c0c00c034181032000003c40d000401c264540d200b5a42d4103940b040c45003050365840030784822a00d2100140b6050f4100c452449140c51f9681c010780120503814241d01c0b000300e5544c4445085070402c1e000008402020304800203010362500600c42c0328001c03000c01600d4140c60340040c108500c28102c625000e4a481103101c01404400022000101000b070150034484c11001c1214075191464080c29104a00d440d010070402e0400117643c52215106880f500d1900c2c1002c502440059500171006c0c441d0321a17001d2000c0041c503001240e49402400c60b00071500ca505000412000402c01408444648424054104c1c40d840000305207800849070795011750346003aa82090325140c03050614141c1c2080c000140c52005039450750040213614000d009440c151a00c00100700e46880b828801c00350b10070a4000c09002240445440841d10700307400000003015204003654609898111807218845441500c15400c82d5030513026112000700309200070442c0503504840002682d03140e00030800c60500c00710786004c89407 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 674895143 1250 674893893 674893909
    0xc06100605160c050604080d0201051f03060902061e0d0e060c0304150b1e0a0909020a061101090f0303050601112113030813050a090504080a0503150a2c0c0702010e 72
    0x1340504000c0c0d0b40c580382e0034a1940d900c09805030100640c84d00c0005003050b006d1000c00d85450f141d01c507100c14641d2a548803040608a51202680c1c003084c10000c003c0c0800c40303042c00c03c591240c02c0302030680740c4020b114248200c070041c13003c40500d600003404000300c0c500080300700e0b5845079200000185071100211040020014466540d8018000a24482400d030940107090302c030700400c642440c0440d0b110301042c4142c508903100250085281e2000340820350040e03810030b50b0320100c0b400004602e003568448000c8018403c40560101e9540d205100e01035907c06c00c2e6406403140f8900404901d40c0700c0740c80440c40c5001145d0801e42210100364000303000140841e9100454002c0c05149d02c982c100d40d4065250200e52290a11816600d200014a0030081c000c4030302c584d4020640a08000e40300038142c030746500040c0342004071000c7c44410b018640e12040011302a05c10740260540c0000e45101c40e4099210041540b54a9164041003040c401401803c40b800141d0a00e004504c0d02e42801c0450310341 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 674896393 1250 674895143 674895149
    0xf1305010914030301090c0201020f0a051e190e010e0a032a08101803050906131509180227040e120d0606170f06030309030703080c06100605160c 64
    0x1048040100209045000004d5410780301300c2c9808100c9010312140c160b00705e2186258000c504d40703042c0583c0240d030740110701401000c8404190000d540301c6410444220307034420714540b03418070781700c000341500c0650040744c49009020a0034404c956040394000a200b9400c0703032000600c07142c0e00148180315100c0b00d00394a001c00a001c245612115143d4a00a443d4505a43e0f0340408503d000006000641c9640c003106126800d5200c80745802d405009200c01c95109100d080c2c0440c1c41c8000014203c81404442c5808c1e02480c1c0d0384041e040d0400100d91184500f94105040c1d13140184800c81c0805d10031846400c070742c14606240d80182c0c5c41c8501090141503202e050031842d0050a60700031748032400d54002c2088821520341002450784030f25003030300d040e0311a4080c294a040d400000520040512160a80054000302164100004403000034070303001040d041100c108c0f0303001c22110b0080b0310400c540c5801030103031000c0000701404c1017030040c150b020384403005c504121010540c005200070b505405c005 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 674897643 1250 674896393 674896403
    0x1120b06090423071e23011e050d1505031002032502070311010306062703020406080703020a09061229010e011707150c0203010e0706030615080f13050109 68
    0x355055210813038030f400030391150740894441c000441d03684122072203000c1d0940e00300300040201c11b40402c100d00010b16040e450541032048250728500c8000d5a84110444601a95541a99031500f25064400d54050301c2e4001c41049401e00b0034041075074040b402c074440302424400141c0703035910510340c203c2d02552120180041104c140039030900950104410b0f003503d0180c02601101c400302401101220405d204501c0000d51524002c3c207441c1210625410000e002020483c6068480c1c0010307080ba056036000b9412940130001c104114100031366008002c207442d07082008510314007804000685141074000b0702e00c0c1e194501201c0d0020f00c04003c0110401e401c12400d00d15a12149000403442080c000c02400441c6030240e25001080061708c2d000b965201524000032200307055080d00d2003a1201001c0380d141d501c814258079501420450540280764903600410070915059440840040d82581201000214800c0060450601d00e640d074000c00f5840402040e00765505095005100c00000101 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 674898893 1250 674897643 674897693
    0x6020c01020f0706050a1b06020306091b070b090f070b18011112130305010603080909060d02010e060c0102071e121b23010504051513110d050312090304090501120b060904 75
    0x5008e019401f85205000944040c9465160004090900310311181a000121300800c024000681307894416900030852000701c80d410f0303048104584c1400903e402440142c900802c001e00d461409402641c1c40d00c00030300740390004450f00401240c0760301241002106480d80000d03610340c1c20140c11046001503400c24020480b00c0c0d00c900d0311034003d620580429104000c0107000c0341051800da00070505055050b19102c805242c20800d00659410421a918a6560a000d4440070500701884032842010228600c0001d0701c485c07608150109900e030481082011980d200175500da4805400551160007040443c10a80c41c41c40b410700b480300c040d404001d60750800e810310040050003e012180003202111492155403005c80118404d1503815003c4c00080000420181c0c504005101603141c82c01901602d24246004481000313060081e200351070164400181005201002d20401c0d000d05140e00c0c50403c03400380d64503200100748028106070f11610622010408000a04845000c10085005068 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 674900143 1250 674898893 674898947
    0xc0a1e0915150507170408030307120f02180310140c070203010b27010e060d0f020604030c0e040b0a0209011d1305070e0901080d1b0512030f0106020c01020f0706050a 73
    0x1400d03070b00070b0581111100c800d07461914403550045e0543d000d54480600850550f0b641c42c204031556142c0d2441c6580383c0e940d0702e040300009103e500081001d02c06954041c0403000c2217806043c40c100d2071803000e0760714910b0001c4010003568050161a000310003440c0d0303151035440300d0001900412808900690224550300219500707030303903517103400c400f142901200d8013181c3e41c810300181044030454020b603100d81c122030440006840416118a40c900281060b410b040d181d0b0f40309481503ea9820041c082840303203040008120b08a0f82581e44145021001c0d400c0c0261040013821081003504410300300040c010b1244003035141e008002e04820010002404603061003240a40500d0304422030601804103007001003281f1000242c407c0e04003585a895007400719240142017120941d900003201c450103061003202c0107802031005180507603c90407183c01c0652402d90081e00c0c0c08186010710b4103640003204042818900411052308481e042e04007144d96803210001141e40915a462100421210403a00 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 674901393 1250 674900143 674900147
    0xc090c030b03061803090409030903020a03050721051203060123130806090709020f04030827040902010f0f2a030201050105030615240304050c0a1e091515 68
    0x321060480c02d805550301a256100c0c4001d582001c0300b995000b0342c0c4204000c480b542410341c46116414001e240003441ca41d00c3c1c1d400a5212107041d0f00907207c940c001c41090007484590b0031907940c40740303441060607003080f419500d441e203400d0b01c0001d4800e04600400010302c1c1e6401201a09142880c0007160b004030b8503420202c05607a04030440c100004c1070042c5000ca038038000003c0310350151006c140205400c40c60503200d0300c003a60252001c0e40d032424040c000080000c01c0c0d00040c005801c00229101c400c2074a6264200f080000c205019215a0030507913100003503600008680d2011147e45010400c0c289040e4045d20700c80e6210000f006414180d8144944030b40040b45096036203442a4000e01c16a40d84004160f42c580045d07030388448843d1540c0d1442c1407450030300740e00c00d105082000685145014040780c4030154002711419211904075916141480c0b4042c54280050701c0c510400700b403c5071041003452a02c00c5140100e100c0340d07a4400700e1841500000d1105002454480407103c080300c840200 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 674902643 1250 674901393 674901401
    0xf0e0403030e1c02061008060105040e0a210e0901030308040209060118030f050f0303010f0b1c0903050d0f1a01030e0c0a12300f140309010606020f011112040c090c03 73
    0xf03204010b0241d02c000c2110303021014184012100144002c0200d070342800f0810000303103803084400000e440344088010000d180c507541c049001400c1400c0b01c07031107014484060310b84020346070214800c98504005000098205070116009501664629a580c1d6038034016a00300e07503071a02c400c0360280c451200004110601c071440804922500580b41002d102c1c80e4a03075a0303030000380035141360165a0141801080da07420f0103802043c45004a1a2290f085031004400f191500c02c3c00303400089001400015101045c0075624607038415003010494048035426248a19147c11a81d50415407290510400a0010032188854050003840d007150f0f00c0c0d0707a08050000c110300c0c26048842d01201689290301044d2915044600781c9a8851a03100041c0e041b011201c5455460f980401d018888504d890b0f13886805014610420391034000180c05400c01d0400ba00c0d0024034954400e441e810624124440701c00c1d4015a0003582d01c0000d04820364a80d4036007160b111103180c001c0c0c1111440c142d000c840b5582c1c1508 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 674903893 1250 674902643 674902693
    0xc011e0339120203101a0706110408010e06091e0109120f090801060812030403021f0c0e030111181804060b010f020a0b2202150307180f0e0403030e 65
    0x212040b1007805a03072440b040c0d01040710454052130000700204040e2924001020340901000d415904c3e00c07010780e43d0700c82100c082e0104808083c0f004034052210240920412101040c140010202454030840c00c1c0d40e100c5000c917105610b2804c0c0140744940b14425008105c0c0c455010408480308400414002d01d1090034810000001e4841d000000321b04d0010300c15501581c59120203030030171641b450303e00e910b07d500207001202107200d940d2000b440c2c0b86d28031b001c002c80d80c8803042d4081505450620014240f10007140a14840d03454109101e41c0302c44034a0484510400281c0c148582c200002e00007184110340d0198250f040c01280e08202c00c1112592161074205000d80fa181c006034216a022030b0b035035454450082100b510003000c108911401c0242c06c0c2261b40035610168902c20603400301d580400f107200840b000355404001d005845401c5440c1095941007010100d404c14030f08500204c40720380034403c4010700d203400c4010400303040c40b03030300403103034628440044400b4012858200400c0981480d = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 674905143 1250 674903893 674903897
    0x10801020a17090a1b12050f0607031a041a0a24030e0303040312110408150105030c1e2407060c050a052208060403020f0c011e0339 58
    0x415184541c00c2e2a2640030700030450280140000c00d869900c000c20202d140f40c1d91000c200b424100082c90010000c02014024070540c05070040012540c0c24518101000e010b890506060000001c082100d45d03500340c1000314100e40c00b140d10050010f8940c4a030000c50030349500550001e42c00f24500072600c2c280245903c0910800e03035003404015084040b1398032000080300302d0300100041004a80704074040c104010710b0a0000541c104030408180c8030344e0003a4441e07400ea4024000d00342a04240e0160180140000d4019082c013036070b14400545107100e002c24010345601c17080800c20450b114503280d503c03044800a00c00c4098240d40c28404401d07040408200c6400341002d40607030f501131081c2c054450301d5000b519024103203002a16901c0c2e00d008c02d0000100d1914070703440300140e6008208030090180340a074028011060352240903e00b401300c070308005410710a004000b02c15900500101b4940c50440745800100d101c040c0006034100242c81185601d02440b600310300e0000c50036609408818035043e = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 674906393 1250 674905143 674905157
    0x4030b07080925181506030e1903020a08071104290d020f0d060b060d140c040305060c160f0309050f0108010e060d080f030702010504290c1c0203010801020a 69
    0xb140c3c0200342542e0b210301402186400b06080002c1802c01540c104140651a004508a94996203040d1211082d5200320b000940303400600f85210300a002d500d50112a2929250410645883c0a9550740450500a11400c400141c103030034000d6070070003840728510081c401e01c0319403880544903010150260b14042103140c652400c90a40c60140c104071003042d03005d00a001c0070b010303020401852200024050b01c4080d2502d5900c041030303a4280060564081c08800001e525a41c400c81c0c1c2d090042c01404400c413404100024404243d0010f0115030003980610119078030308e203e2459010b005298400104032404020b941c01c1059005035682c02034076416200c1032070b0058000d00440e80c59000b03100c0c041009008030046180b50030300074040700c0480c2c0601c030390343c3ca40704c8507510740d4003650b00803240d000041c0d55403410f001c1041041485480c5080203480f81409443c1d00c2d00c0890183c040c00760203480e0395540012001c40c844114040000380d200c00c035108640380d40e52904414080c3d4065803064000400f0 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 674907643 1250 674906393 674906413
    0x614180910060b090a170a230a0b100806010e0408161415100b0d0f020f0d021201120b0703050403090810020405030706140d0209041413030e0102010209010f080c04030b070809 77
    0x81610801c100560b110041001400307545a164102066070b800d84429510f038440b1600b0885d007000850b404d94400c42c81041280341c110980c101809441d0030480437500180c00400c01e040405000641060704800d98555a01042187d0000204079000040656004050340c040440e00418050102ca0380c0701039925550f500e2403400100c10034180240803031044244403000104215600c49580440e012100504d4842c00303109110054000a103a5042c0940003d000d968803402d48801900403c142d6405568241050f540c0c50300311003001742114101641d541c0002c00785446601d81c0b200428103a070590344032804003101c040c0a5845806581e029104081c80040c09910660350080c5800c11404031038105544000b1100180d84000079141d4047e80700d800c00a40d03002200ea40a00555003a078444030848800c1c5006440d00488940d041d0641e481480341540c01c4e40c0043c0070114146813032804d403480b50b80e4a108689103008680019203607855800402200035003201440d405800c8400c121510151 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 674908893 1250 674907643 674907659
    0x30c03061e182604121a010e04021207031b0911090105040e070e1e3a02130906230103080415030f0507050901030614180910060b090a 59
    0x855000ca20301c12030703101089801003070502000f60390440f10700d0054080c18141c00250100340c1c006400c404a04204408440c08101c1290001c2c2d00810000b1110282c40d89810b8044080c9540144080d01800c1d080d02004135210003401450080c40e80411700e0290460400e130064134168043c011200820b00e44030595000301290410346000c114142d40300c51a040c02d06515103072960b40031b01500188415401c0c101800d80d0740d022419038141d00c0300382a509040710703d800c000013803900603035502d00318414001d04250902c0401c1d1411545060450b0b40d41c02d0103080c4045444c00c0c0460800c112052f00d00300d042d408101480e000103c608141a0320303c0d175400d0807121140d100f08020b12008220401c1040b00b040700030341c0c0c2013065400c0c001c03c0c00c000035001881c0b540302007a1001252000002040000d158889681520410002d000d0040491120b010700e140031070810003032001e031078201e444103034002081e03103e00300a0800e4100c0c1e080018017809a0b95110401281c00080600f842010a139401081601d = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 674910143 1250 674908893 674908901
    0x10515190e0307150f0906050306030a02150904050112170a0807080c0f0a020d09080a0209040b15120c040b010c050604020d0219141903170310030c03061e 68
    0x221030300c02100302040000350155609800e100d000ca8242c0039825000820010b004c0803188840481c3d02c40d01d0a844101000405c050078680140d82440420b105004083d240081c6103c0401d40c181d030300b05040c1c2440d4078110b0f154015010000d512a0514002242807c008500141081d2048100d078500c6020514041042e02400040e840060601400142d00701e100314041074001883c0c0100514100f00f5600108041e030000c5203850142e80a000041c596540c0140d451008192840c080e0820500c02e600180d0030f94006040a4824140440812000c00d0310045009035035000500429a09140c0e0414a8a5648140c1450301c1246041a01f014079402500c10006159201016041680d074682c00c108804a045c401a80c22043d1000403503001c60282440304080c083c5080364000f03424581c0c04020030780c06120700c0d120b0540b00c0d820b010000581444000301d8800c00b201d001c075440f9601c181c800003040e15940c1c00644030020340032000050120f1540080d0008040703e004094101c04000040c06407 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 674911393 1250 674910143 674910157
    0x605030106050f03040f120c0528200406030b070806010e060a270f0317040608011809020910090f090c051207080703032d090311121005010515 63
    0x86034040020303c100300344842c011a0b104e441207101d00c0b40c40c44151500300364604a0b2aa41011500c522155414010100302515000e031058064a11450700d03c914030030045010b2000030700700e8241511079180c840341544100c1210707001610810450380c0d40d06200c02300000c01e5420402051440c404108254441d0290410508000c1c060354500403100c00d0450303180700300d00351003200d60500701c643c0b105164600c0304610041c40003002e080c0180e81542407400940b000d03010054130307242c0104010060250409145070460302100408000003122410100107070041710740083d072149210040042c13500110b20402e0070f43c1c00418041142c0d4149081e00411160541000342c020034500c0400c000c6440c21581031400107240b2410380e2465a952480d032403070990290030460105112400713405c81e0150520b50380a0f90410b03000b480c070301d540001038040c001c1d43c3d4030301010b80143d000900c039011903100d4020340c280c40c8411208071000c02c2c00140780b040003800203016041c85070241045a08500c0c0c1c1d00d0302501c0c01 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 674912643 1250 674911393 674911397
    0x18010611030403030e01080c09040608011d0312010302041503060f0204260a060b131415101706120f0c030d02010e03040e0421030f0c08090613151104050a0605030106 73
    0x10905d09001511025070003000030b0200c2000f005244c1e419142c0b409900000c0c0007030000440c2c0c00006404622400780c1c28000003069a01c1070010728003010b190310120741125010749002640c00740c2685004403103940364001500c0c1030b0900350079140d844503641c010011203500443e00b40b90340342000200030569020800300c41181c0d102c0b47c02e140101c2e05aa102a40b6180020404d40d00c0306030b4100c09074141c0340506204443c070380601d820005002484002c000110100300c69940b02210280d1001e040c42050114030381c01c941c0401c00040d2281c45510070040710040d00d400705c238109400a40440d03601c0403042d12040c024003c1d4160102180e00500900c2640c0e04403501850929042084040c049080140b0640c4d44164000c02e90440000c2d00403000310481c150754000c1502892040c08000b0345408080360310412207030344100044450041a0503411582604140340803405c1410040005d00388038203511b011a243c4102000070b0400c8100038011610141d03013104810343d6614056a003400300744a6400 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 674913893 1250 674912643 674912657
    0x302060c010204032108070f050d1a0a06090513020f0708030903130e04030207080313050402030408120f010626130302011b020c032404030c0606080d03020405040f0e03090118051801061103040303 86
    0x42012b0086d0000c44155110703084035001c135a26039000403044000d03540301e5030204100200a000c0c078104451642c118054000c400d615200c85408841068414914080c02070b01011010030010360040c4112202480a0382c0116101600c40341c1903c0354290560f800c80c007500c03a58000141c51100401507486a4512014100c81c8620f403809100c0a984010412030f210582040a00f100981031580d0320b000e940c02e00b2400410350305081000d8292001c000100ba82c01300c03540b03200e150102e00306099903403080c0f9040b1610404480c41c40c0581c05444500c48481c0310400440752078030000e6000510700654030084088a500d01c094540418091211000d106c1d00b8016180000b00840e0045058401c20b920480c000180d46d55900152428407200030006000a034000030100402d1400740144c0e140e906800388108020008034200e03d40d24410444110f05220b21740c00828000100f0100901c01000068407403191608050440710703207001c0c05d00900c400703e07280140f114a540400400e81c0c3c16a40e25071503002e = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 674915143 1250 674913893 674913907
    0x3061c02011b02060c030d02190c0506070f031506020616080103020312091203120103060b030c0307180603061e0c260c0412030e0a050303070c0302060c010204032108070f05 76
    0x26481d100d6610142d1300541c042043d942e25074420001082c1001c0c0305c000043e06c441c5948510020700301d0701c0850000300610825014040713840441c04a8125180d070070034554040381104141c3c00341000440c04c1e403440320400c1c0005491900821280d101e841a035501e0040b401014900340c888207003e00000c1e4060f07103c0c0c01410b812041d118002c1c00c003084000d00703c102010400704c9044c83d5034845458503100100010040040000074001d004408004802400321100018003007070b50f07903c0030300c40ca8030301d040b05903000307444480300b6440710000d990000428803030754502e01c00360401507484a0105048031301d440070142000344140c10758008040b8404414442c06070104122501d204007034050600148100070016640040321602e030000c0d03100c2d0b00c0e102d00c0010700300200411414075a120034002d410400c000030010700c0e0280d00c00c003920b40c100c0e24107840ba000150842d009000b1604001c050501c0351054911480c82c64144030080c5c2000e03503c500250340ca894086454080032500000800c030284036031 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 674916393 1250 674915143 674915177
    0xf05041e2001051215130515040f18030c021c0f122a1208010602030d020c0709090311060705040e0f04050a08030a1e0c05271503061c0201 61
    0x1012180c101490f110b41044100b018103007400009803a50002c80071411043c1c1e0345030916411280150102001c00c00252910303140d5460700900c1d946d0294855039a81f103904507100d009612032012401c41002c0561000418a009040a4412001680b049000440d1000300300ca011036555403056100d28100b0301f240c1290344055040348903e004c1c0041c080e801d8680c26100041e800c81c140380070158110410200050b017443d42c3c40383f07860b0420400b04203000b4018016a5000000c541e8000c810050060792108048401401c00b512a0016111a41072100c802c080c5584114000300003000300c801c1d0b0320240c403000d00a40707051140d449114210715100340010300160b00c018690740e01074042c200b682c0058069646051050340200c598508143d5a503440d01160f42500d0114440c0303c00a000c2004031807a43c1b0b001030554040c40150351400503400140740b10480060501890001024103041e0708054241c4a8007220b03041280c14500070241080c0c04001c150003101c41c000d07443d07010703101c03503070b03906068040c2d = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 674917643 1250 674916393 674916443
    0x121821080f1e04031103010e12070602450d0b04021f050a0f2a081303051e0d1205091e0604060b030a030906030c0e03010f05041e 57
    0x44406075600600c0484440742c5161007041003002100c903410307510ba003107142402c2c804a014031200e000740e1401c00592120000001d40c00c0d11000028001500e6441a04d0608003a205146c11040c42c582c82c4000c000380f400a040b200c032800100c404114191007401d41e0300440003041d50703030a00c2e44801d000c8200c4000c1000040242e41280c0050110344107801050318810301c00f00382140050000d0f10008100e0b00241d03105024110011191601d00001d02d1810b4440d4000203080c01d880f0500c030240100d107001c21052008413002c004484145e0202c1c142c4e07904009446401052501e8200e520780f040d00c00d45c1240c00315083c207841c1d0098442040d41c60399015808024140181070820310720134248520300d000d00c4000c010080390940b0004000601d8107207401801d07070741c40841e0303039000764026080140020780094184059419510b0000342d240b224401c1190041c524070700031038165192480c0380703000340c10903009148154000c5400500400a20200364001340700c2c5400648004108480f1010100c10781c00 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 674918893 1250 674917643 674917657
    0x120909040606080a1208150a05300706120204270f061202040b060a080f090a0c0e1005060a090501180504050108030a0813020609091312182108 63
    0x1c000590503100d2100038a050003611042da00d008001a02d2130a41c3c3c0c0c8000e40c01c0e1b00080c0941f02e0440600c1d4600814020700c20760044c54401e0a800011048464000c04202d480b10b025010041081c4140c00c00640c480e203a9005e203200144445040c091410610f0088800711458001c07004201d5079105040e20510401c0e4500e6489141c031000c4c00302240f9124080e51001e0400001003c0301402e00d4030400c81202e50100b0824001d6005000307408085811142803584850a50b01600090791181040c0e81041510b0400803d08a9080710200d0609a00b513101881103e0046541690303584507000c11149000f5500e03018001a0030300810b0129511070f690a0748820080282044c2c10381d200c80009084d94026081010250710110705071441070b520108258002c0a00c100b51419001180c002c584c6610400110ba40141441c0002c00c1c00c00303500a1203004840d0704000f840303170180d540603401000000da44030756400e080c8480c01c020401e0417401c90900c104050ac040c81281b0032500c1d641e9400f072a04425 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 674920143 1250 674918893 674918903
    0x1403030f0f07020f01020a02030a0207050409030f08090f0118050d08090606040f150b0a12140c030705070b040602031e06030726030c060a050f040c06050c01021b0d0f0212090904 78
    0x200c034a852068090000d1f16018009801554407600340b03110091a007241607124034400c90502ca842c001098000e0041c54000200b40b0340f180c81035640c10a0149001e800244000040d0f00e040c070041100c1000e013488601c058865819100703040304070482251000c60030348040507660069008240d040c81c00c0e9000040341c0c030517070002040001d0b4100c01692220507603070200305107040005110030711543c0082d101001740e1844004010401840381b211043c6040184141590080000814995402102540c1c940d039404641d03c0c1e0145828541840030350810345090144124031941c034640ea001501001e442410054014024640390881035100c445094070000301110b038500c0084e025007000d10040920006013030050405040c07501c140307001c6440080940c0101c860003018080060f039044c4640040b40c40c20b140c040c0e2507070030b100b41103802486620141e01240301c0c80c0105110031b0340c001ca220380603078095840d25160070034040010b036101c0e0440340c1e130414400c2c82088169010303e44220100d030440e01070 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 674921393 1250 674920143 674920153
    0x150102100509030301031202070b031627030c290915030a1a010c0206070b1005040612020f01030504080703030e1905030309070b0412020108040609020604060504031403030f0f0702 79
    0x603084810844406035001600e40d00000300500c144000c0c4032180304134400c24030050601a2400d40516043d010283c00d04210304824031100c0d03a001d10603040821200c60310344410201940da0b8980145180741480115003002c101139000418002c0366411a03000d440c59180b42d44a500075450401c03503903002c80ca80d80d41c00940c01d1048841c08000d000558403801e480d0000080d64880c0301501d00380d6020000c422410000c0e000c42d4030005031100015a1071203039002c8064003081d111403085065915468000603003042c600303080020115411024001d5060003030f190054281e40350401142034420440300504842010418040060701c258440000752584205942c540600305002403000740562400703580035407001c0b00348425024240702c0e002c02080b2400240749406e15000f00b0503090b43e041200a4180003400000400303110054010a40d215802000c0a5a4076200d080203481e03500240026510b5a082c2046241984000011a8066440790f080d8124a9a5a514104a400c40240460114016 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 674922643 1250 674921393 674921413
    0x3040624050607051504050610081c05070302100c0309060e0102030105091306020d090c05010e010807020d03020d060b160308010e190b010e09040b011701051603020a0504030b070c03110114150102 86
    0x17041a100307025502c00c201404050900d0369040c1d40100d0075421200c04ca410501801d000782c14904912039108101d81400f6490300502d040036403d10700c00040c1124000e01b0440d814050551562002c2800c038443c0c442005011050400c09080740824090107803c0204e0304086064200c43c58101294948034680151800200f00340403419100c101d0000c903040c248004081c0320725178003c1c519900402007031800208500d03240200968603802a0420740605500241c40042280315421a0b00030342142c0f08030759540d01d001061460010540c20341600000c0c4054008200c0003c4c0328a554002c21b8051445c40c01d0041c640781d40b00052902c17040c02d034184107030484200815181e407a15135114a018001104c1550702d0100c41c1f40084031040e01c02c800e503034502000c0058110080b0050003924815290060302c0315622441600e240c41a900054004904581002100ca500c007801504841c401d99034401c41021010102e800e0364900d1080c6c90b1200c4424000410000480340300210b40a0144111003d40304 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 674923893 1250 674922643 674922673
    0x100b030f040204022d0301032f101103190f09080a120903020409061d030901050d0509030708030a0209011b020d024c170408130e09030304062405060705 67
    0x508060300c1c18500001b100420904c4092000008254080d940c107001e041400310602ea9054a03404035288980764254030600030303500c12181c1250302e41c0040300f283d43d209503412440c01002000c0d4400c82c005070090700c0c01c42e5818841e040640031201004000e0990000c0b80d507a009040c01442903c1080290344a80080545d4443c05403000c41c0340aa9000075400d0100c06099041002c48104080300d5402007103201002e9030b12a0848000101203d070015840d03c031203c8403401d40c80f40c030002502c01c203004818440000c4141d401030460345000d8031240103040d1400c0e42e032a84410710020207940100e200c40c0020140c200340307581210840e001030003003484c0e14610008803062a00703001071002d50280300034140b104004030b5444c1062100309040c041c11040144150b40c46040300200020301555020981c0e4084800740c034065000b40620120900b00362410004003903481d0400ca805a0f810350070074140106800c80c04112445a01c41580d03440131503410102402141c4d800f01c0011516481224043e9503004 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 674925143 1250 674923893 674923957
    0x50d0e010b1f03060e0c070209041a0f09070501090b0f0d06090f06090515060f07170406031a10050405010e030f0601060c0c1406090108062403100b030f04020402 71
    0x4841c0b0700600b00107001e80030050450b1030940081d2003030407625042c0b101084ca000107980295070704940040715540c1d0362408030301c200c0340802130310181c80e00581840300070f95003a0310351032207440c4038400c458080b03940b4001110255440d01c00c1c0c1010b0f0100700000d00310b4004a0004190982c40c203a000310b81166511030450440e20741c0002d40700c0442d034591041c060b040280c040d85402210400161480300118000520b40e44124059660008030001d9050308201d00b080e840e020f4490f005001940f01c0d642c2d101c014000c0c186803489941c04c002c00d800c1d81100c1d46400d4454841c051955903e25041900380f0005503001c504140e1150b92610954003110800603042181a003e80565502d5100c004201d140404c6c02c0729050f0002195000180c1900c08036480340700594160b00b0b801d18120655484080108140344e10000240421f80700301800414100c524400960040c410b4241e030402c066a140c002851030300054480030300082102c1c0c0420054580707a0054500c5061820300b442c0c0200300c881e0001804 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 674926393 1250 674925143 674925169
    0xf0806030f0d020616083114032a060402010e031006090f05061c02090a0f0c2001061409070302040b04060206070210020f070f0606180518070303050d0e010b 69
    0x144e018204100e0441200c0480a00403030450500400360309002003190b000e44000e91501050140b90b020103400c40403051307000c1100e260017150301e400d0140c480f80c08907102c2d0301c129503800d410b118001202c41800d641000d1240c1c007a00b0b2202070021903d40e81d00442d641c2a4000106a06109410110358080442c0c82203800030040e03813500144100b210000314060b243c0080200707200d0700c40d01c0c100c407407a010041c02c4005c20130350460300301c2044d43d940b202490003410040d818801c0700780741103100c4034010340058482c1e00703040d1703444601c00c5060500e0301d0280c20b0303801d54040c0000135450441007032168101041c8250700919182005410683c0355141c402807a0081d03400fa000590003030b028880600e805000e4a04041c0100703a0130352910000308048080c5100e801401004600a100c0d1340050126583c062400303081c1994130b0341600301040c98500b01802c8162400342d8100f402810342c9002602c006003002c1200e0307040e118682071040c101c2c5164020700400358808040d540b14440d0628135a5680300450b45 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 674927643 1250 674926393 674926397
    0xb040e1002030a0e1c0e03031303030c0c0506090a09050402030f0a0507030c0b040e010b07021908030d1407020d05070f062a0e03030d0f140a05250f0806030f0d 70
    0x1280341070f10340c00c01070314100311116400381c1200150000d18407011484440b44e0a903030070824203440c5141e001c41c3c5140f081d01a02e01840400507c08010903600050f24030819014030320a0076290385401c00c03c410342c89580e6a00d0b42c888180c0604226400c22904681d0740540000c040c1c800c0300003110340040c1403400603081102c00341c104020500410260844000140c8840030065007064140f24017801030b6103042c0510075031b0039000305a000c11941d4203407a0300004101c0301021030706c03181e075013a8181d500e801501500f01031600301a0030140c0354510070b52a03845891254020903210040c49001c2d9420340c4410700c207986044c04000c180f0040364060180400c6a1000038903e9005107c11040a004e0202d1303a142c641045094400d0258913900002661148001d0510004030b020006021800505440480c55118201c81c0100800c00e03902e940030310322441c0f240341c107040f2070104551000881111a8401c0300030480d8040a40c602500c6800010b6000b4000350440384111040121249015015499140 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 674928893 1250 674927643 674927647
    0x1b080409091110020102030402030c01200f06070f0c3c120e010809070302010e210f0106060f020706030b1203031315150b0309070f0b0d0b0618040b040e1002 69
    0x10b036081003541d62404150510085045080943c00039445800340750000d070402c80700000d03d4141c3d0800e0341f51500c1d04100c2e40e0450b4101d61442d160203833184000c442c0100414251114688110300075640110307002c1d07102da0341e0003001c3c440300900900302c004603840300340c0300e02d01003124090490b60400142c041c034002e40381140008040728000300039045180000b41001011010322440c80400030300740040d2582403e0801c60034400d140400d04031610b655601c0d014805810422905010120b9400b8445800070020b0292944850040d2a04050b000b03401005030b01c150340401045100354003d15104030001d03e001d0321421f03600d1080d403a50300282c940c8001c2854006000080000030041c0591244104100b4040c0303203003a41806070710110500ca030358080100080041c109010500054000d40240e14184a0303443c2c460304c0408583c0c0190101c0d140461802da020b400624154007075543c111050080f1800740d404030020702010b0400c20b110240c10a40395000d4410006051260390303550705d50040010307 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 674930143 1250 674928893 674928923
    0x306080f07050f0a2102060c0a06061a0403050304090f0f020301090c031a030718200d05090105060d020d02190b0d0b15030601180302060a0c1406071b08040909 70
    0x3c400780400700c020500c9015840c4042144149011071034918172001d864050020030103001184c160710640003650346500446013a00104111640045d0640303048181000f4014111926040e140c4102e00000d08140e0081c80100900d18182e0811010400c5100002c510a00b10f05200030903038000307822100c881911000204800742d0300d4480c00e5a44041c9110725840910b035034000c00d071a40032902603a41c4501004a03408408480760300842440c080c403400440b0f40c401304000780c9140d50010f600d07683ca0507060002043c0030b13040501646005280c014103003070040d04a542000510080200f0498001d0740d09807002c1c50581140c0e591000600013202072581d83c04e1041c0da20000c0780c060b070410324414641840486244408142966030014080c248840d010126040800540a241d84000d51080b0005a000b9a40c0c1d880341c000903800d44580314520848030300c4069161900011164080040c051030784c43c005075884017500c030746030900465840b45401c2e101c840c40c80680321140d1041d5280b0941c28010 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 674931393 1250 674930143 674930149
    0x1022109040f021b0a030f0e1203030a0c17040308070c0203340e100b220803120108010e0a020108190504061a06070b010b25050606090c0403020904120306080f0705 72
    0x2400c181d002c007009051703004070555010348910b440c641d9070810411001d5541129448440d282031041040500320fa031607190403146140541030400408000a43c66000e103625107404d46e514a0103950f154030b480c5603654911908840b808001181603038180f08461505a4070a1101003103914450800d041c1c00d0017180914660742c1260082c0c2c01088065101c004000545440c6a4960259128124180c0d0b6401c4050038107100c0c00c442d82e40711240b003110080001502c143c000020070f2051012041c040e41c83c0c2c0c2c2d0701d084038203ca503102e02c0210701ea040248000c00540c4540c00342c690040403075101095912417591490100d44046504a0f101e6940e604d07502e071440103003540000840c004071203203450943c440d510300d480100c0c1803181800c4440c000c01d061404070b0b42d104a09040402c110000e404c1c00c00c081c10055030b40c02c0140d945900401821001c039140001c00c00c102c2e801d890f00506802919200c9075664040c0407428401380741095601c120100300c410083c040503107402491001840181c0c188410 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 674932643 1250 674931393 674931427
    0xf1401061803080d0504030e060f0717030106020a150213081e0705011d0d08071a010f0506160c08062a04050a03150b1201060602010f050601022109040f02 68
    0xc0703055810000802c0090030200c200c881003041d40b2400b007602c1d2120701c1c0540310410034003102a40814003049481425001c02d01501d280c40c0105448100b80c100b00c100c03042c0c0c510081c014000180c0200d410b80001c0340301207100b00300c02480c04a0051070120300c520318021242c4d02e07030450140b641000c00049924858002c41805444084010307014003031403c1d0020f483d5440c07102c2a011801c920590f10340316543c850b00b40701e8129412003421a9200e205180840c2c0000c3d5403a504200703a0034540000c1040080300c16180c0c03d4a030090659460705003103280b40a10038a14000880b0328890301701001c01c000d001844154001c5c6000050b400510907401c0c0094210b00e842c4c00c00c0c401464091204000e0b60f5104420201165000041c4000400002d004900600060800300381c0000b0050070011103840d05502807411500594020030940702c00711a000265401642c2d02401030b40400b0300810020358002c0e291492102c07890400e4588028000814181c8901d84803000718240c1c003180010300c410381524 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 674933893 1250 674932643 674932667
    0xf0a061211090d1e1a0711010501050303040513020403050304172b0503040302012a090e0105212a15071a100b0705010209240f0d0f140106 61
    0x30310642802e0761540411500d422600000e0300c1c03030800c10340f0b000d07858070711100c0001c070a5001207442c4842000a10300d580d60380030a8603201c0020325101117150740c4071418450581a00c0c40100510310701b0340742c80104202ca091401c00c00803c140d0803c000000200704200030001080ca0490112020082921143c10721051105481540c20041c0d0300030701c2100d448814004048407410051340300e8a90b4141240100304944140c0c03a21580280004080c1c25440720244560815568010304980c4641c54100800000c0c49415000412249080c003482003001d00c00581e06080000c80d620403c1c140030302c140031240140005200549485a000310f404c2a194040b0342c1d100c0d5192552030038410b43d40f032242c1c1b00c9a07840c00f1203030002da2002203001803110400c1e450003004a040a00c1e10340d9040d00341311b8001e5200ca00403502c11800c0c803000e41c5858084043d00f480801c0120007881c24440f802e000c00102d5444002e204991b5551400c0d240d061810b1441194416044c094941c2201d40c10510050310004083c0 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 674935143 1250 674933893 674933921
    0x305210307050d1109030a11030f03090f040207031b0605091b130e01110d0e010b0f150313140d02060105041514032407081b0a030203060f0a0612 64
    0x420004010b400c02c049a0301c41250f5040029610004041c140d280e000e12a005c0d80d0501840700208280624984d00c10f401079801c80548035021801d1300307415070b41d105514099402c45003c90303048446150a601074041240070b81091034081a908103151840d000307a07a02147c0760740d512020702446440410a188840d0201114072000e01c1c2064000340d0280c072803444400b403541d101c5194001e8074601b03402000c0b070190400310340754880020310b0b211300240c101c00100d00140d41c64a1383e59501d0b4034050005043c400c90260075102d4140c4800700c0d0501a43c0001d00d001034004200865000240303640103140700c0101780c0e00103800101c441000c000d0901c4410791000b40f05909040844a880e809005c0120848184140869190340b11002003424140004080c5404c0500c0681300c03400851026200d0340b02ea19103503200e08013603407011948a088158001d03460080c02d02400a015064003c0d03000b03640003100104503001c1c000814001900055040e00030b440003c0c503c0500d8801008980208010b0058207 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 674936393 1250 674935143 674935147
    0x15040813061e05040b0418090c06110c04051e090c0603040f0219050108060f0a03060c052a03030411040207050109150b010306150309080f0703170726090c0a030521 72
    0x429170305031840c0694018940d41079440c4003005510a044e902c04180030b54007046541d100c5955120180c860001404040040d000301030740c0034070510f410702c40d607031140400759005446000c000304840c000c0813009050014070b10500790402d8540d07940c440994852480b5403088002140184140440940ea0008800c049070b0005014040d581e00a00032035801030041c4c50041c2c4501020b000a240446030394006412545882d080350340b056271110091103c00da0740b12074041414600c48900171080d501101c007801581060011070002003000002840b0210002c10250900066865040c2140e0690500720303032008011070441c0300e82c86c3c1402820524a000d0804100c17491500c118005a8045250076a040568070107052042044500513280e081030702c4000191982c0c0e01e480d0191008416000c48152408880e0010b44524880c401c502602050512003460306100f200c4050880714000c0d001051901500c601003942c3d1b102e0003041002140600d0081092200d58a22290269400e8140310341120f01 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 674937643 1250 674936393 674936399
    0x292401020a080c0106050603010311030601170607030b010309150603030e01030c0e19030c0906031502030408120402031e150108010b030307120c0206030103030c0201030e010e15040813061e0504 85
    0x118101640079007142c0b034030f40d580c4803e960050041c00d05030021580036602100200a004141c54407e41c0304109604950080e62182e100708100d070544207224845503c0f440000e2829842900580f00c1ca410604001c205030102d55102c41d01300080300000f0000305d0b610b070020800d069001d60b05a584040a0804028910385c1a0008000e01180c20b40c0c00d0190b000500014103400b03d0074840001140c100305407035005e40c2c44030407040140210f48026640c003040c41c1010780d240551442113074005c1d540002c84900d03024010300e2818820342c0c01017080c1d0741401501180403100035140340b030341c09450386103000d446500500001c0c0c034814078041e00304142e103a14040e12007220391400000c035240d081d000840c0c900b00c4030a140003180c0f005c0c0d8003040250060400300c000404c02d9000225110081d00c05d803802d000c200040080c081c00c80f001441c05e55940c0c2d00c68442c045000c082000015081801020b50520f007003402500005443c03901c2e406400020050800c043d0f0150390000000e6544809241a03480c1900d = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 674938893 1250 674937643 674937647
    0x20c10050a0309210207030311060705160c05091305070f080706120b041d150f150301090b090c1503010605030c1b01090510060b040e0112292401 64
    0x14126030710701495a6601100c0611050502e0080050400c0b009002d01c045034020094030b82400b88022400704030720101d02c0701802d00115519124841c156101400c24602c0c01e0000d124030100350055440c114555004106902d60940b01d512440e020102040d5403521031410514003101e9074010000690006000e000303036080851610125525413500c00c10300b00740d119070390004007480010302e944140f8162112400e4143e14000c5110042000c0503115001600e1403084100744080b1441c1c44c8802205000519104400b12072002c00c040240001819040e10b95403031080e02c074262100300c0b495021004203009481c01c02c40c4100c1041c04e402003141103501d40000900307103010281c40d0b00f030545c9021490704140344103c50035142024000000f40401503090034035540350b102c0110000c02041c06c1c60b0000c41c2c441d000c4e1084801300c6507201d034011466842d05e100700c080720760020012641c1d01c10505000880c41483d920350b0108280c20904401103080510542240c01d0742c44c203100c034548902c401e004440e6a = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 674940143 1250 674938893 674938897
    0x6030b09070f1d250305150d0213110421141504060c1202071209050604030b01150c05160e07090518040203100c020705130b03060c0702030c0d03030903020c1005 71
    0x5110780c032501d0b0507252041000410503120001350100290140c801031160380c5034200600920708000c1c0100c00582c1d4009101251180c840040e4001103c450710784040c408542c0b0081544010320481410144c0b07541c03500c298044150322503918001c1d141840b8003481070410803140d4100100000301070781614010301000440e40140f01400c882d0740c8000c0011507d000e01c1180c0190040040e086594000ca0314040e81400707140c9030b943d000a5851303000814641090821201641e0300483c0d108080ea20302030030503104004000c280c804205041700c545002560030400c1c446084c00e0000c54002e082d0910000d02d800400c018591001c215500d07500300200d44518070b540c16280102035655110b80d940e800420316200205a6544902d803418022094269012a112040e100304580d11a00c0a0a610454040e0f94524030b606515400c900f0100d098113003420000c201040c4040c0641c1d200e004107000084464400c1c14040c0d001c01d4071003160a04041c4d040c843d090807682d003100c40d0548800b1034280200340d4 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 674941393 1250 674940143 674940179
    0x4030c0f0f03060506030703021003140f130b09030d0c1d04110906030a090b011202120a030f120b04050403350c1309050709061e1b0f020406030b09070f 67
    0x400c3c0c0c4c650100c1d0710358405120503006182c0143c01e024490100f45170003801402c04103c045268451140820260600f1040003801000101c912400c80d2500e601c83c004060000780c0702150b02d1004220540c0c51607181d0240c0040117595031541102d1841501814807006001e0b41424420b0b0726160000c0c82900105d001c2c0e940344542914601d84a60340c0c100198010010400301405034140000001100c61281ca076040d0260720aa448522071118140803d58030360150400402150750b46220815482c0f0407040c41030080004030010503e0340b0320201203011600c0c00da80036000564108608030440c80c1024844464440c10003a089628040e4040201007010260103040429800590581a0804101c4203c041c0501107000c11150401100c09050040c8034440d000100c1d402d0803050340c0395502c030300c400d1144440c2500c41c0d211800c441c08084181000710f001c200c0e6031101600c81503015071a54420b04002c1c6100d200c40e504c1c181404d01d5010316082d6198460009200300403418041c88400b070660f1900 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 674942643 1250 674941393 674941403
    0x31f05031b0f0909010209040c020111031b12040605060a05370302040f0b030f0d020703080310080f0d020c0f010c111503091b0d0f0219080708010204030c0f0f03 71
    0x100341c032580d00003150a40050354483c3c3c800b185400348018600198020010100700311803c224030001124140d003030b98141484940809011b10018144503411030010b401c1c00300c681d071014a007480e030401c1182c0c0040d0560b400e0313514035601c40c03c1101d141011ba03007140c080d0104503900254440480005603418402040415544044502500b142004402c1e10009190300034028002440809095401000001101407103485500c1001003c200042490040b0012541c05084681e00355221141e2580c00178107100745040d201034001031026410311132030101103031080c00342044901c0a28020324081401000030b108800d644544d40389130b13030072596401c14a41c1c045800d0700c641b4084400122603030b405a101c1610848000200648868007103542c04100c80c100900c800e00c03558800900000009810005001d01b0024595101610381541070b200c140105965450f00e2684501c14181041226844400e0980d00840c0074030070040e440c61248003074040036030785c02c0c11f0514040180107502d01c1031001801d = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 674943893 1250 674942643 674942683
    0x11706070e040e07120507090b03060a09110a0e15092a070501180618030c111306150908010509030417070e07200615100c140102031f0503 61
    0x845511160003c148500b81c0c407080c0c800300c0d0369545844420620b0524101c42e60f0050b02d0010038203654601c41c8440500d00a00140190b5450310b82c0c42000705541802a110f40b9510b02c08014941e96070f1403070390054100103c1450b85e83c20701c3c540f2040d030308080c1005d1a01c07030b0500c1d1040107001c444001040100100b60541e101c40c50040b40341c044040c3c4182c0c6000707412075080a10030001019010544401c56210f0360080114540341c03039114503401064100107000a03190740d00c03139002c1000320021160b02213005143c08461440301c0b005c40304480d4903906c150208140906040c840b2500043c2840c0101380d050001d00c402c1c6800180c0c1c640380e1080d0700034100e04942ca0039484403103036420040b403070183c8607112083e85581042600a020b1f80000a050185120641c103a03c24210012404601170303d00c0d42c01c8400691440c20402103c22900c101c02030030005102007440200b94141c1001c6c0402c0d0380140010782d82d080a000013000c40e03103003803807100083c44801c1c010442500c00044200000d40503104523b = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 674945143 1250 674943893 674943917
    0xf030902010509060a030c0906020a03050304020d03110f010b100507020f01110304030b0a0501090c21020c031e030702061305062716080c040605060f0a020a02120d020601170607 78
    0x10390540903e4030340300d070002c0b00412801d000700d4240c1d0015090700d0704d58035002e08180c0d80f403d080340d41c2d440291005001500c144082801418010650302c641482810051030148030355800514004404940c0f86241e91a0301c0481070508000000c0d00142c145890060700e0400703070740c010880e05801000f07114100700c4c80d015032009114007842502d001c0c540c0400c0040244c1089041400900428000e0582040c9003aa00480300ca000d0f484070030010303107848406000000105e08007002034002a85c035096501040100b00c0790225003840c89012040e610038a40c0c0c5a0a10050081c6006030082c9050480300f0400b18410200f58002030240d44902c0403200d08200e40c111407204001c2544252940038980f04041c0b4803550703690207410941c2524054421922290b2400c4201310641e40c484c840d158205d801000303808282c540340c000500c90001d990045580035042c540c046600c024880440b181c05801524407101c0c5940c0c14800e403401018612041d58028910f0311100b0340b61107000d4200b0080c024184011 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 674946393 1250 674945143 674945147
    0x63c050a02070816030e100f0909060e16050c01091a0a020f180a0e0711060702060c04060309050a081201140303030105010509010305150a080d080f100312022104030311060402010f03090201 83
    0x10650f1940054005126656447e001608054112507c100800c001d80b9000c2103140d024840c040480c2d01554022045442d11404aa1000e41f82120003041010820a01d9801c030400d01840c601c80e4415440200c41205416101e103101c1ba020745a18256801000106290000541501c0e6403128141c544c8041991100008060b0002f9500500582c41c3c07100800511540100c0144001d01e40c11054429587c0c80078000ca80705d80085840038080c032030a0006218061180d0f0080286a2291085600301845500c0b072480607006500344402103188000148900a100e8039441e42040302500207501315410701001902c14003c80c0c000e82d0400d81d40d0710025452140c02401100c140780042c001c9000f068417240c50644400e4070381e00f8100400d84040100e486103480d8103005110b0341c0404000b00c5454115035607101780c007150402d00c10441c410740764120703141d4880100880200240902c0540d1721803441c07070080c2c036030003003c2090206030700290708010151340c00180c18400d4004514000ce92582d043c401 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 674947643 1250 674946393 674946407
    0x360b0a0513060e0112090201140a170a09020a06030209060f03150409050105101413021b01050c0409060501021f0f20030106110304080a063c050a0207081603 69
    0x2000184001d2280000b80150411040c100311030080e0f96000300040060b2954007034490405000f070016144448490276202100040e19100b40b03a450030720700d500711030806011410019280c0e00052a514100c4038218541500f8140003000305003070550621242da00002e01600440f207880540450010000c2c1c1c9400c07041d080c0b18031111001313000300704180080c00c0403030082c10129510411202804000301e1440c8030140d5042a05d28000e0203000701c6125000690040e400401040110344031010094081a5003030042c00c3c41220900003080c0c440d1303c0c0c6008401919038a501c11815034110425449041c11842510130304103100b000081108501503040100411840c071881c034041d82c000e000000c08001c4400158100c81e01d17503032144501075618000e9900ca10892080c041e656010341c241a00180241e0030442e02c0800c16030407440d00001a07180004102c902d554045400c540e106054015800144501038000309001c0c0118107000c40c90396010700d1340c403850000d40103d20380d21a40c0070416110303207a = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 674948893 1250 674947643 674947657
    0x18070510050c06040308061318020f040b0d030f03150b030402010c02030304180f050f090a0b0405120301030308070210060f03022b0b01150f05030a0c140406360b0a05 73
    0x111125441c4c0707810002c0080105890b1544280c0c00a500041c511143e4010342c031303049109140d0f203685043c0b00e07420441000301480380740360007d4440011060325600c1c01c01d0300700054001d40b41c441e01541d00c608001c0446040c0c074007620403101d03804003d1003800c0010080d00d50103682802e01800728040703070000a1a60045074402000c80707005d14800f020000c001c1c1c0020b0050a03074850207002e541c584150242444104807000341c0d10307501034000c200104a031684607940090041007940c040d0072140c044128070760700903002600811003001c01c0c00f000950401800d070180000c2c410400c03805041c001000410301003844080d200d4001c03080841420040c1c01d03600405821481291042c01d8250b182207082400e003445000c0004080803600310603d80541841d6003804a00d50303c1d00d20356540c8012003001442c440c0c221404025407445482d00c22195003000f0000380c901c503150000c80e40c244041a250000d401105510072122190983c03030a6039244030307070340c0940d0388229031642c545112030780c11515070140003 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 674950143 1250 674948893 674948917
    0xb07030c060e0a0c0807060c0b0a0e030f0c1b0a12142509020a0503041502090909060919021e1504061d040e0a020909030d050a060e1807051005 63
    0x1001c101c980da940003030444483ca00c15199036001c19920305069850b01c031248101f0004c9280f035840e000c0003a440c84280c0350302030740307403900003c140b05103002039031468001002c0803070440c200060100d8404010030848003d108220a00502d450303110011805c400c4c1030b03102d00d50516001c04e500004010305449032043c1e03034030f00e00100d80c4003030759000030900d441040c8000b40000c1115190302280b404018021190820780c9501c942e0710b9522030340d0b21000440103c8900044582c0d01b0b00c0380500c40d81d00d04d00a40c0c0200f0000d4001d040b00d06118071100e0030022501c0f82e130588100345030000001a00e8018029000070319a64100784001d176204041104038a00b5407042400010002d0080b40300740e0801c0c4100141c85000303442d82d40e03caa03040d041c0003c07144105540c1c1515804a2036101c01890808489030740007074418103507402e02c0c1c1d0b1891028160b50741514882015501d4500502088026180f4958080b044015009402800c011202d0b00d0321602d0003600d004240340c04444106a00482c02c8078403049110f = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 674951393 1250 674950143 674950151
    0xf120e010908070209010e010602030307050702062b0e0a020102061302180702060a1413020f0f0d14120703090e04050a08180301060b0910120b030f0312070c03090b07030c06 76
    0xd02e0410155481148124401c002e502c00104000c0103100005042e80e5898006603c0c2da110f4000030fa409811045040380d11031410041c10841211918640700c445140d176070b8050318054040501403e6031107030f40d2241c1c17240d4088140200580c0e130000e0880c0c4c1011440300f03001c21080f0b40e07002007440464100d03210001c2843d46000d000425500150152084802c1d02007003001c00c0307015a159259203025075034254122101240c40c0090310b881100486641002040314422190400100c1d03441080c59205642c2c0c3d011411100e100e03142c06000b1600d03078408401c201481e205c0c296030060170010f01e60007030105011040e40003904000040000c032600c66040400f158464056145005001c00400b85507402542400d1001aa90702c640c0142c038543c5100611280980208a504640c00114a001d030b4002c01d481d084c0210143e2001c0c4071240d01403400c0b00186540e0301c6003022241401c1400b9000c3d44c2001071011043c8007085c0d02c80e03017900649041036940e9540c0d0080f82011641550f07002c401800c402e01d0 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 674952643 1250 674951393 674951411
    0xe0a05060c0f010b01090e04061d0d02030d150302010507150e03190f0f0f1b020d03090515090306150303280905040908090910090e010203010501080114010f120e01 72
    0x1d050b154641d444002070011800b95001102c00c2c01041c4030f886c1c111b0104101017030009156800c5070390101120b406040e01c503954800700300d1912589944039400760f003000900040580050183c40c00c3c202c0d9082594400d945586c1c0021300c00c1c402d0900150010100003515000d00084ae04000b031124120000c4030b032102c3c1c080741d5582c0003100700b00c80301000c244800302c903940c030500818104811940c283c07200611004140010b4464000000110300044220030080e40140d8580d204102400d000c0e0750360301189410401130040546c10305107903442480040c0641001542d0016001d5404242103010310164851140441d145001703499518220100207400001540c5014006139004080c955031074444c690368109100c1218200f00024005030303010040c058690400d6010903411a0650300c3c2000c405545201000c21a080f00a071000350b0b9400100401c40c0d5a40094100d01402810040260140c203080020b41001c2103403c481081c000c4040041e001024103512407070705006010001e00032218 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 674953893 1250 674952643 674952667
    0xc0807090b040c030c0228020a0e010f050d0804050d08120406270b06041a091005010e0a08030a1215061106073033050402190e0a0506 59
    0x22850074450701451600040c0103141d032190140d0b895500150300604004500307002c254074402a2440d980c490815502200c40058480c112410300030580080751031710315410262460701c1050154005841103445104400102e545c400c06c03101262011600d07032034141c6580c0b601842c180145942c0180c82c602a000704400e01c102504403449200c9046841c06034001c841d0642d1103c0f0440550140c036003510140050340034245940700248bc2c94080440040b150049030000750030400864074031440381c005c00300401855801c04040d1283c1d500858084601504104050340d5900403a0350701810000e82141450007440ba603444a4409006400d402c405142c0300c40e406040030402e01000c3c4454400c807000104094801e07a041b2a81c2947e05074143d603d010440207040041c0c90f580e494007001551098400e680004a0750802c0d8010a4503608484d1400c20522181c204003076503100c0e90046004005854002a58405241d09044181071030859503a4040c08a2240d4640c0e03001980c10900018001032181 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 674955143 1250 674953893 674953901
    0x7081b0a0c03120510090e100c020a170715200406170109020702060a20010204170c010903080301051005040807092703080c071407260705100c0c080709 67
    0x180c0a074540501d51480c1504003804c03100102c684010801002409010078106a00004000305a000032100300724100316005040f180d003d624030300580e01010200c0300704402d03000d1440c0f800c0480200e007130034103c0342d0315100c1c014145950034030703101130351400e4500c201418a00303006120b000103c030150300c850710b44901401e03650a048440c0c03903900c1104d000103407006070b9008490140368060708550500703070003803000c3d52250b00001c48840315011481c20f801d1825400d10180c401400090032101c0ca0f181d49141440c1441d1800c80b4103030421907118406c2c0301185004084a044034010380e003e903000300e9100000c44242c0280d8214562600503c0320009070801141c00c611480c44620700c5844c1300145811a091003400100c10050200301510001020018800c010b0505540101030b40240038282505a90034441240c02480c0c0f0201540090028220103a01e80c0380105100e00040c0a194142000207176110b4404000400308280302509070104075658000c1d0004100c007100b1284125103d001c0440a8 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 674956393 1250 674955143 674955167
    0x10e0706180506030103080d020924040306060501080f16140c010b042f0306060714061902040303080412111606030c0903030c020f1504060e04050108010b0907081b0a 73
    0x5403a000c0380c081290303d0580700701c9048030781c4031021902e0105101000c0c80a0340100071f0b607982c0210784020424480619050b00d0045180074102c19a4450551901a044490680055042180040400c41c041c1845000e00e030300020b00c0d540e60281c240401c0d03001c80304603c05c02c01c294648580894030700e00c1c100701500011f1303020204880c1030203010421400e14a61010360744280329a4100120345001a90b0071a004540041c006056207280190350386a40c41054501114804241c2c00031041050f41040d07400610594006803005614041c99034a0080c078182001d480544443d102600300d032b000c1c60150034180000c40c40d40056030a0958940034541144070140309660100b4240a545905c580c0315190b444140c0360f160b1074018400c0266000c2c06000c144854803150820681c00c0444c10710b2803640b001e08000c1c40319554520491018205000070781d0b80607801107084d41c1c10b0101d10001a41c80e8907200b540302103e80f905140d25620f481212803a14168006070310742c1d400004050201a900655541c95 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 674957643 1250 674956393 674956427
    0x1515050405010e04170a05090d0b0f180c061c0c1d09160f122c1203010608090102090a0609081e100e010b03060f0105150c0d03020c010e0706 62
    0x100b41e9a6101640c05103400f02c0700200010001003690101191240140c00030521601c0d25034208903c460220340c1d000c16041040d503a41c402c0350204004620944212503100e400c0d500309030288141420b09a656400161019100c0d081c003244500000c40b11740a44011181c51503001d02c240046240e0103400c050160000085081044a0701c1c6a541800440349011302038040c052400405c141d202152a681c0c07070100013007009980d49039800c010000703000c0c008070000861355441085011100d0405400c1c240041c0488681201c0c0101c0e19031040c40d001d1700e0440d15541000f09003652203100c00e6009201c1c403151030b5400015002c02040b0158071036619000e0b203602d10111014000007801c10040d0340000345200f801c0b54890808000d41280641140c04503000340030021841c0c00960001a04000084810b4000e800d0002e0042029140c00c2e2420303d2960300740403400e464181c1c09500107441d2070103c0f090b0018141c0025a044101e0320075404406e04c44900029220f08940b10a8000d00c042d00b44418204 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 674958893 1250 674957643 674957651
    0x402180907030905100b181501020d0c080a080c0c0304030f20030c100302070b09030a091a090f1305090109030905030106060804151d160603050705090d15150504 71
    0x40e40c02c0c0240b241c0c940054201000380012080e60000201601c2004a40d541000d100c0700505101c01108000070b0003280c50403248402e20308203c000a02d000004e541500822030b40e0b80120010405031421150140c0f40ca00d0440e039269508004400a03200b004e40c9010f49110009001044c802d01d0100001d10900c14105850780c2c1032001c0080d0940041459030650540080540c101903260659200704e00b240c0500b00581018003d403910712501004444401c1250800513030484869400402040074210220111301070103e07805600201d401103034a494041c0f01d442001103040d56034034128a20000c5903c00a01c1586040c10105020b012122000c50104640b000c0100d41c600c1c041c014078007552540c1d03032542d01c0d41c0c0e195202c0c20142104114500c0f0355641e03d48a14402645910400c0080003100f401803254040c031550307290100e10154040d0040601d803200380700da1503900804a41c00c1c0c00044480e540f541400f0304120482d86103100341074448500d00540c4007114032130341000808540301110204 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 674960143 1250 674958893 674958901
    0x70b040c05060315010804060b0d0c0311090403050415090e1e01080d1d0d050f030a120612140f1e06010f060516050a020a180b0415060c020f04021809 66
    0x42d4002035034100c1d9500d031800d021140b1540304000b110b6001e4003c1d10302203010300b400c00201c2c141000d005001e54800700c1c0400140144440030380c000740740f0031065030003c00c0d034034064074020568092401800c00030004c6040540c481031140f6000c03009084c1062020005041c01910600c111001d00250701140b07400c44000120050003291080d202142c90f1208062000106801c1c135460700b4501c3c0d03596002614840100c0403e1040010540000014000b180d864402c0c0c040a0300b4282c101e0840980c1e5401c005042c0036038100c6e00c600110465118450145030101c0c0d03400c090401c06500d002c0300149c030607000c10f6084070340c000300a520034503640300a0b111a6601c4003c021203220403805400c0101e082080060301915014605641440c059404c0d01d41540d026800540313003e1542d40480c502d2000c42c10350241c04199846541c04220080f142041840b8801c03100c00350345102e078403070001445140100c05081d9110720350780c254a600300030003c40d500c031400c43c41c0b0007000c00a01c0543e80a805042e00003 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 674961393 1250 674960143 674960149
    0x821011412030a0c1a07051b07050d1203021c230408030103020105130e0c07060e0f0d0f0e0402030a060806060312040b070f05010507030e060c09090a020a0311070b040c05 75
    0x5030344503003070060195107070502000c2c003610800310074901200d0011614540031075500f82c001926004485030b0342c840d41d882d211241c01e0070402c03185504010f500e0b0001c810401482c3d403450000c0e00c0042c2d000448030700410055800313a0090040414003a0340078042c40e403c0c4290182c560054030341c00340e044d14040e5020000c1c081040d80a00489c0c00601040e800c200502c0990b00400c054103071703001d09001030042c4648803c200c1c0380f0403505441c50700b070040c00450749008120882c00781d0702c21507607d4402045200c0701c2424041c0e480d08210000d00c24010f081c2e40503011a4881c0f840c0002500010b0000d55030784c2010704008005001512460300729004490118466103004a6030403000d02c40d10550a0070a8180761403454076600861003114826100071306070f40047e8080c02030760321844c1181c0700003070740908060b403107400c00400a000742e1300013108212104140d40d989a0498000014100c01a1212500304065004000c60885034446010101d81042009800d040d01407046101b540d509440d280d07a41d0034 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 674962643 1250 674961393 674961409
    0xc070209041103010c200102070c05090c0912030a0801090903170901150b07021206010609061d18043806040b030303090d120605061204020f09190e03090d020d08210114 74
    0x30964903503402c0801233171521403242500801e40c2c0706000d1400c0b06650000e11411040d88030400280c102084810f80340b50400c0387c10f401448101e5040c0145411070381c0082800080030b0030889225079003004504bd4142c254443d000c2d81481c420804855501c501c1d10075050341000808034816680c0441459110384046041412942c40b0748807a00303c10f00b8201d040d103c000404410505140c850580f101c6c42ea0380d2201009a4110031805018a07030030f250070074001c0a4014034411845001d207603810a0740215000d5600034510810309407200039121b900008010b0010400c06a5161102005110404802203000103440016481c0c03c00c2000c401c003502820340701980f00702070340020140050b854007410a620f899002d071004005507145442c0100040c40c4900540b01598003980c0004d90300d28a40031407164011449c1c00000031030411907184001b858070030941383d00034001d40100e600c0604015042041c1d41a280000343c20700c0002000d1400d10310070040920514950305c403610b801e981142000e840c = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 674963893 1250 674962643 674962657
    0x40515090a06060c15150f09180309050d0c0902040e250903020607052d240c2802030901030b090402091f0f0308030115080c070209041103010c200102 66
    0x4800880110780d0710361000c1704040d0840e842100d625000301990580c2140b0100015000c561410071740603003821803140031503c0081076044c901c0040050348000c079820280c420100c4504031000e4078003448500d044c0f048542ca80c1e0048005600110300031840f041920f0b038082c41030344499a81e0000c0d241018001c0c800342c2d21040300c14081a2003001c03d00240c10f03c4802081a68094070803200100d1101d45442c9041089071713940c8000440002d01e80c0100902801800705036403103a144549003030341281c0f0795483d00d9005400f0620030800000c8500704561b281c07588240b0001c2481b43c0395012001114065180c1e0310444503540080d15240b91001c851609e8160640a01d0b00a840340c00c1a98501c0c07090b0786142010703002c0381c1c881040500001b401007044032204000d98401e600e1281c495140c060b41a1030f540c1801001c1d810300500c40100462402d00e90305172502d039901160030015a454604200c03200f806107100305505942050308025059401c030303401c03404540c1da44000011104400041500f00d002d008 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 674965143 1250 674963893 674963897
    0x414180f06060703090e04030804030210020c19050c0a030309050f060708070605070318060614060a1e2d08010803030610140d090302070f061701030b0a0b040515090a0606 75
    0x1012075140d0800001a100c1a032013402c00d032101944481d030003c100c40c0d00300c0b01200021a04810002015410301085030400d03005801035042c0302c0311001c003a840d11b40c0078103856604014580c05d0323000d0040030003541c204000c0141440700d06a441e03041c010404c21150040900030606a040b25426090690848000b550440801420171404e40d4900e07020300760240041d402c258a0344040f0324580003224800c45c602c0c0c8209000038940c3d2030184001c10711200851201e00c20f050500582d4542600303d016800400310046c0c84402d40c08411405031200c0b02d00300d0038400c28500c10080801000307880e02605680c514980c540c50050ba0741d54141542e030740700441e0819040743d42103404000e00c45c0200c0c0b030740c100002c80c2140d00d401d11079001090000c440302400c0680040c0d2100b0400c110f03403a175031003501c005010a40b6102c560050b5402501c81320510601c0014070909014000400032807441d44603680c14030005006000c9420800403210907800101d5401e8441c50034a004258260250702ca48412101d140d = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 674966393 1250 674965143 674965171
    0xb0a080a02070f050708010207060509060c041e0e0a0c02100902060414030307081303020a08070b04030b1510020c0a050936070323160b030703060506041418 69
    0x126000c40c003070b4224100490700e10040b8400400016000c0c03101e64068003005c400140c50307403000e00342034042d80c070060b0006c401900314005010141c40301e10304880c240d840c00f080418421604020206001013150302c203041101c40c02c02400381c10401ca400c00c0300b2440b03031a0300b220700a18110000100300d4011b0040250b001404010401507521074021010210030002c0540e814003460b6180c2040540c0800800543c4141c02081801140f41491014004d001d0610040800c90b0505811900900c9070b0700014214001c803c001a0600702c0000781a43e9901000e00f401801c540c1001c1c0181d0344680c00f80c401803044203056004031b224140701c1c2c0c40300d10800f000707600c60042c10500308408090b18650605201c80f440e0700c003550618584100000d400552103100406c81010003038480307148203100c1100d031401c01d0300441f00300907951580d480c0d14825508800c1c0050b07582d032120001900108440e51007150082c1000ca000502d000301c074240c1c0300c80040c040e1024100b2181140400341a503108403202c020820304 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 674967643 1250 674966393 674966401
    0x609020c100c0504030203030d060f06050301120b061f03050f011205100207290a050a0902060a0e030c040c030e060601052106040207320106051005032a03100b0a08 72
    0xa25001122810307054180a1300e8180c40c1c0e00407a05651110061a03d6551100820404400c07002500c5000307082500c1c0c04e03821075042c140f15aa5186040d4000b40c049110b22020842607610070044000075441c110031441c00c40d20070040500645000c55880c500c0d0b40100300000f47c80c0d20141000f005c5a8be00c17901500c00e00d02c004409100941101c8419140333012035203c881c0404105031b2104000803110054140c42c1d1401d805440103807080146641080741c285174801c1d0041e220700c82511503110030741c1003a03a05802d015010070700d4040f0005a80368000e00304a042210190140e0007147c45d41d050390181c805640c0c44200640b6103101d000480301003101c50141a011605052038910b400c110010005441d210719034555110849060528110309907003003400c201500c9009020700c1a501c150402440320301d00c1d000008a031241c903840d6420912600000142c04000703c1c40340807a8501c00c0b00c940c1c2030481840003001d0740f55001114140c440741c980c01404a103400c1d1400c241c1d031160700c00b40d5a401c1c40f40d035 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 674968893 1250 674967643 674967673
    0x9070605030a0f0c1205090328030b130c020f06070503010e090f0a0b0f0f040213020a03020c0a05070302010909110a032f180f100f0c050f0c040609020c 67
    0x80020001c10ba0295a02151600c0703111a018200740d5000030b03a1200700301c880313020307100d002c80700d010302000c91551040000200f030300c044106030184440003c4d10011511140b003410b6018246047e400c5520201034040613400c2e2015078080e5000e41c41560854840c02c50080e040c565940d006d80f040c0d00491f10900040044507000140076901540c80300036140c1d41c490a509180c03a100c5030420848007854104200901d4900320381c160f982c00304081041b4191801c0c9500481c82c0070360740485d081d03080740c0c0010ba070b85e41e258041e804075450f998060f0215000c040321410a562184614003007240040c0d8455800103020103e40900c01c20389441400e07207440d00760b8944094000f0066002d180d1014419994104140381500c07035032075030049040440d04da031001c0621a414114402100c4244503019041040c241915040602a550081420f115078086100c840c15200011000d400170298824061081c20b4001e0120f00c0c0c3c903141000b038400340940342d1030307410b103100340d0140700302c044102c0e445a07100303141c00c6c0 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 674970143 1250 674968893 674968897
    0x81f09051e010b0d08160302190606061106070e01030b0d0b012c07080a0504021804050601051009080a02041503050d05191b020f012a052118191d07020609070605 71
    0x2e403003230045410400220180031448202d180d81a04c8150fa540c804010882c0c1001124040e010b1403400380010345003d1101400d210b45042c81c0b82c0c10947d40d00f1061601d81c4401154641046c0c10440b100030941e034a8103008a0040102103401c1c5107507201040e804480070810550340542c2c025110101107a46007c0180002c180050003641d01040d0014880164000341c003a41d4022400b402c041c0c0b00d60740c1010240240740c02194002003c00c0451001008100f4010419404540d0f04581c0400c201035900c01c441030f0ba20040c0c00161140c0a0780b1080f001d03981e00b0400900d0424002954100035141c1c009054442c001c0e405045001250101c601e0801403400c4008204502d105040c1401050665405207104440f515814040700e4191094581408810040741c0c602040c081d440d18003011580c07200302c02c1c5005220034040f0700090341448c02129501d1010017044280420340340010155982e0002c441010040410b485060100c404502d10a1000c2840c5101c0d00ca154024070001c3d15101044840e9 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 674971393 1250 674970143 674970187
    0x80a0504060f020d050403140903070902180a0605040602070f0e010603020a02280312090816030c0503030a090b1303051803030d09050607020d09081f09051e010b0d08 73
    0xd1640c440030400102003501c0135012080e001c43c00001e21345450701d4042c1010180003101c03503081c00140048042640c0c00078500c0261040350002680b0342200ca00885450b00070001c407190b001040b04030119819500002030800c0762030560071166071950311840c0000c00c26a901540182109450050000c14000d40041072010380c588102d034082220f1146d002a09410420340c6002c2140c0c00710144241644000e0540f4200f040d10020130400710300f680c844940e84580d054928054140e84018024980117010f500c84042e00a81036039580c0c98060000c50003403d20316011100809041c021030706015007416100c6c407155240d2202d170319111169802c0000100312916075a81480100400e40303043d410f601480550070721a2000b804981083c00d8080d05008030680500100f083d101c50800504130006102c00c140d2500307041e42d940744202603034054040c041460020b040d40c400c00071294000122405100d080201d440c0080180e043d400c400c00c10750802c00326021303080c01801e1088d01c2900c072200740b00f10703c4 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 674972643 1250 674971393 674971403
    0x403021305060d061e14060a050d03020f010501060f0f02030a0c080d06080709060303030c180501080709080d120f0e0606090604092112060b0d0905030903030d06080c04020307080a0504 81
    0x8070f04100da581e074095801c503401c012080844259204983c0d1090301075084030910030241d41d5001d00c1c2c180c0104410040d50303c525403003594410829000e041c0240000c940b0b015030140240f00710f41c0c4030080600712034410004800060848101410300b248084180c3e18022225966501d01c903419460300d004a4020140000c481d5545076000551050b04115040c0208180340000c03a2132451810040d04031284500103006103c8400321110300d40b20a03a60107400d440c02400e0a440c2130315a8070044800039110740044c51710707128a000050159420003000c440d2078a14810610450038007150403c01c2d980b03041c03c0010198410804106189040506180d018801038000a80ca00040d19074084003000102c480400d085181c181e500750a81c0300c021805a00c41612050182914002201c8028442c0000164415a4903900f10003041018004c481100900070112501c5014008503800242180e106640036485401101e41c01800c09009507881034149807a01c480d141d66052007640546030007403085130 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 674973893 1250 674972643 674972659
    0x10c020d0f12050c0c031303021c020d060c021603110f1002030a050705190b0403030e010902060f1303170a030f11030c0d140a02090910031101050a020c0d060917040302130506 77
    0x400584c0400141c6116440a1141e20b615440c6006000c003000d50b5041c00d0052b42d0420711030001503180d8812140055034070040020701e58801106c101e0822508091000001007114400001c2c006c9101c00100c0c49407089070100c0d8151080340820030700700c000f441042c0158000384009110240640c016004880c040c0068800c00307648008440c0e10001510070403114540b0560900087c540d241c810400c50007140d0000b00816003594000442d240185241c0b441400e00000320001c10b46d43c204141c80087d503010320813041100030351085000c6908401d00c44030009140040c0080990054000d105614240c1ca40003440c1d5160031001070b04c5d540c003000070100510388504614906854111440f4410301c0900401603d031100b1000b0020f0324100906084860203013000c00f030001c501b003121a131100c502c1c00d092140d9241110901603082074217004000b0743c484908601038060102d5074000c0d0240900c40c0d241c01800c40924070008007540203c0c00044d41002e822765214444d500254800c90708280002c1080d1 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 674975143 1250 674973893 674973907
    0x11010e092404060609081204270e0d020601051c0b010501080c0c160501090602060f01231305070f0221130e04110a1202010c060c050408060405010c020d0f12050c 71
    0xc1c03d07240941d0141000a49410041003081c4c021300005030108090310541c0d182a180040c008480d02403420407034280e0703c1c5940440c0350960154443c1c0b0700c954100c402d641d07805000e4003020b5100e000074840c1d0f50145490442210089000001407402198070004800180c3d00f440300441340c000f8010b21a1106e104200304107071100301c081114004082440d26000b6803541440001001c14240340d2000e02507600510500005a031070842850640c0d041411314021200c01c5491101403200c002601504100c0800d01812070002c280c105901c150441c4d00d0b09483c0200010707040743e8845401c0c980507501e00103060b07584107010466001b8100309009036007544500392540d00f2160311a6007940e0440d40060000c0440d040c41c2080034103074001f419465070500d1004180d4001130449001d41c00700800c0030344d480e0007281c40240180103a4002e0003d4200b1210300e4506490082e0003451900c1105016100300c0c2490103040d07204840c03564210405585640c2d280166003180400750501038812048004244155 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 674976393 1250 674975143 674975149
    0x3060402090303041e0b0304080a03051005330f030411010c06050c09031002090a05040b15220b21070e061c050a05010510080405010f051311010e0924 66
    0x41c2021788159861070340300003207a00c0a00745c174900a5000d20482801801000049030100c0c044d55180b0100b41004901e1383c0c1c030503550f0b0408841d142c00442d0b20684ea20040141e1801d4905804030800c800c4801e40d0361440c02ca06a00117038041c0c0300c507001e8544e0007040028005010884138030100a0181404c02c1322014554039031040d58000c9500b860300c90808509404546010412001c982c0c155480452610701014041041112140142070050303465103000c52040d110343d03040c2121100307030203051925501211903290701070b180300000c00d40c202c2c0c0c00500491302c2c450100807920813211120600c1d111b82980c0d01ca42443d030000405480c2404501c0081c80065101e420040400b40d641001c1040c580c01081a1182282c0028000500152030071005000c0f80e102d04403103060800807420110001da60710b01d091400741807003a041300705040c00d000901181d1042c0da40c2c0404121312607410166004401c2004444014a0181c0b41d41d00c040184046500044000d084003011512803041c90702c0740c9501008 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 674977643 1250 674976393 674976397
    0xe030412150203011d10080c21072c060f010c020607020414190504110d1b030309030611031b030910110c06060d200a0909121206030f0803060402090303 67
    0x400a10003030017441000038519140710550788600d0201d440c444081c1001e5500c0e5031050501e0b440d6005650880000d0108030b048060900c1885c0b4031011961030b60340b50b05141070609114840001240306002c061041d560250415500c1140094009400012440b004442840c114081640c02127410007150001d42c54500400d50348a00000d000120382c00c1080621665021643d18140803c0c41c280601000520152150407410401c4490b0600c0c00c140741000c413101d015081050302c152100e50000400c05800565410841e0b025140c2009196138040030084244000c90b5445101144d488a44a034100524055500291546c0c2200d01141c5885031500c21902c01156030075250030302040c8052000f1080194070391200044c4c82d0204001070b03642e203040301c5a45c21101c800042d00c0c40710140e130098560740e050301b0090140000c01d2200549908000750b00c4041100d12000003210440005940d034218010300080381c1e8000080c0c40140f00315120b105458002500c05540a074081142d08051b50307007040 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 674978893 1250 674977643 674977649
    0xd0f0302181f080a0905123108060703020a0c0609170714010506041e050603151312050a140304020d0b01032009071b020a030507091e0e03041215020301 67
    0x144490200c880c58006440d1580050021070303c2400c00030024000fa2020510347c0c003500d80111195207560075041d00c00882c400300221260f0043c01950a0200e02c0742081c4420f0451310b0007030580ba410740f56000100c2c103900c180c07052070000c2282c10200c44000b44c01c40e400703d8400e501441c4441c011403000440c0386243c1c3d11109040da000404d00d140b00c01205001c0c4105a0400790458003008001c080202d5010719080313180100c45226507030fa0003d501c9413010f000d120f4081154407409040362030101500200c903095610191150b440c6440040c000c40d02130300403035010031810b844018600c40c0b2103845c8070f5282e0009100301c1e000000700c034001001031000000180030718828100d0106401c0a03811004014030031748060340c880c00d002c7c400d0045190708000102451502c20200d10307000da40500111b6050480d9500041c094841c008000800007103c1d4032840b1540c10710080e0300d401460b0a4180c0781628200b06540850b0b070000c0100304180e03002c800000046503c110301c45260880b0500500040760401d034 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 674980143 1250 674978893 674978929
    0x270a030c060315080f0c09250c12030b0303041802160c1514090d03020a020d0305030610080402090a05070903050714041107050715020f012c0d0f030218 67
    0x2d20350141440100f41c0b000c003070241c0000402500c000d1044003541c540713070081a54007402c820004140700401140d0070305031141140066480700296840001c2c03904402c403201741c03500e015209030708024511038010715002e0f02d8010015411b2a00f0b05810400d9a940e00a00d21401b07582081b4248078190914142c81c101409021302210207440c1c541c540d500b00d0f90030850641005803200002419050302d40c01d8030080302c0155441d2091341d0641c030b4143e01d0a45c1c070003000b80d400200c0061100c00c2580c400010342c85018151038844032904401030903540364030189c4009500000c607074005404801b40e903000a80c010164941114165580d48a250904110360403085100d441c409078000c040c2411301138600c0f070a60b145400c500e00025a01c41d162140b21500a0210b8034803c0300e603220400d03208002090100c1d0150380200000515101c00c40c01c400c10002c00411b83d01c00c000303c822a01d200205031100d003172859894a000c0f1011a000881c025071143c00c260004642083c1d0400b05512010039a01000e1520 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 674981393 1250 674980143 674980151
    0xa0c0f080d060f0803070f06020909130c080a03020a020622080f1c2001110c07051f0903031404090e0609010b04020c0a06050a0603020d050604031103270a030c0603 72
    0x4024094182c50181d0050070700c00b14030f0403080061010000403030700199003000303520800c66842d10b0a18081d21503120950f9002d60410244074250510420074400035203e00120320070140e440e850f00781c961300340c1000074001d600011600800340c20284001d00300ca010078801038140d0680750051200515941e00083c0c0030782c3c480b681200d4055001c01c140c801035500020702d08488601d01d2070051075a85080ca54002a0756030700750001d2041c00035004440126480241c007519522004401d50381d81803280b04961090400b01e0321900e0310000150b001e10405a10750740c80c1c41680c03c41c3c40940d034034000d041221500d40001c0100041e0f03110503100340701072007050001a1146040c0341d140b0034251081c01c20782502c42c5204000b40d00d043c0c0d20008550110580c060400f0a003507440340200f034005c184030791003e5006018015800104107000c11014842e910a0700d0b141003000c2d052003125030324040c450504800c000614000d1800764480c1d45840c0020200611108407030b03480c1e41d02c0d03007138a01c42c2d07512540100c0c2d00e03 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 674982643 1250 674981393 674981407
    0x50103081903061223011e110703091a09040c05070308151311040b0c06010f090b060703052503020705010207061e3f180213020a0c0f08 60
    0x80701d80040504002403506100c0b5508110051a102201800041007814210800200703400c0c4c650001c58140700342c1c03001b000742017103c03010300400301000b80480d04a03a01e819a001124403c0d0000d072154150150365a480c4035040c0030400070745600c105000c0140360401d205504150f5110b016a8010404503a02d85489035a94a40a448008081d0100c903038911005c1c10110782e03440b8900d00004400b843c03100130a01c6000380300e038000c2521598024080c0f00d08000703600d140e11000001c40b94121620002c1200140380e4800050080f11030110415601280c00c20283c00407900c1100030300420380b0320041d25510810315441c0d4005842082c030b41140035801168040019680500015004103136906180510401402200d021056105a4141440211070003a483c403120202d0381c54040342540aa2903e0660b842028201111031281141c0110700f05800002c0380b40c4104180c41d10641c1c094100342c01301c03741404810194224030a51010418011024004038024010300d90031140204699650b07148 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 674983893 1250 674982643 674982667
    0x12030a09060f29041808040806010f03050309040209012115061d040e030c06010905010503100b18150a0b07051501050a0b0a03060b0307121a13021c05010308 69
    0x581e00c001c0c021071801d083c98901201c051559202100a8006644616440000500103244032440b01407030405100b01c0c0010808002c0003402521540d50883e0040d81e40c0356440c1e502411140001403158200b801040c2c41400c3c20303005012141c105051065060080c26800620001c110b1421802e468541104002d1940503010040140003107103064405100010314a042c603944492465003e95550805a0041d20b010310a99194901c560140c1d10302d96920003d040c0540f01c03c0c001c2c030788a4000c150b0100c83c443d11520403000f4451001c2e04044820991405540890707100410920341101e04045410066030341040c0d240c0540402c40b482034440a160400c2480c0c0b403410042c1100e40c0c2e413600014440e42da0f0303007640c1c80c0894803014541540d40b086600300b00c001e404568040d4078001030200c01e20140a07008071241e20001c041c00020050920140704500010909050780b0303130445017408060300c0300c544640091500c0c0c00c0c064041019400080510000c64209900c00d1320386040210b59120300c81 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 674985143 1250 674983893 674983901
    0x70308092e05061e0d15090f050106050901060c080315221401050d021201020c03040609082b0e04020418020a08090d050a050304021c1416120305090312030a0906 71
    0x12015100300c02030000c600b406504d085184c414041c07207040301a0080c0304100a101070307000408040c034000d10501d40103181400c0c0756509404121001c0d401c1c2000800c02d8200307600824101d60060b6503035100002c0503203440780341c2c0d440a0320340382000100e954019100d0f124910620042d45200b00450b60b580711000316001110300c05018400b14820400040002d41c1d1000c115130155601102c0050159810140c00ba0080c80b035400c201280b0301020030b00003401904100075000311407120007541c0d070744014240d10141643e03466500c01c0c15000b0300e6115070b2017144a010794410081019000626154035100070001c40d6190340e200400300742d0002142c03180640e010b12000c0c1c1000101c00200705c01c0001200290407405805900420800302000080c10f640d00c0c05440840c0c1e120f0031212111201c00380c01d20303090019654141e11154494044885a00e90740400a102110551801e4158030500c03650300b01c0c0c4580c0b08a049c10303490f2080d146200701c40300c40e000c021801032245050005080109180090640d = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 674986393 1250 674985143 674985151
    0xd02090703182f061b030714060a0f050f04031409030111180d200a05040c09090b1002060f13080a03020304020117010b0a080c04080d11060105030111070308092e05 72
    0x800e2032032050b50116113a042c169500f51402d41030080c1c001e803e104481d45103020f941030243c01c0031400245610901008503500740110403600301030002001c03040000c020b403403050b03500c810031090381400100402c3c81090a08413001d11148103e2600000c10000b900391001082c0081e10000c0018840c00380c1500c003245805211001c0c0c45d000380c541200c2c1c45081101d40804490000e103140c090900070303507980f212001806000300402c1004900100c00f80200000310300c2c082d55000526042400c8214900305160410b44178445d8000c02596540c0707030408a0484010345a0040515090441030004060b60064140760f030395070341c0050301e900d03180c00010700c24244000310b009147d135004014000c501d604400c845411101d402c004902e901d40c541690028802c07544100c81034081e040410141940c081e004003094101001240e94503600ca004243c2280e094501c05214102c04011100010380603040781360340081e240d400d81e4000301644480e9190f50230008100a65401690101200b8660510441d900 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 674987643 1250 674986393 674986463
    0x1e0e100215010905060301060312050901030b19090b18250309120513030c181a061e0c061e180606010c020d0210110613020d0209070318 60
    0x22201e40711200c8150490600a903d0015201c60001ea400d8074250890001580d004100e040c125880b914010300c02d03004421207a00090074082d03824402c0c0f0f4119161001c802410544054040ca4104500020402882001c0d0006086421070914800d00c1e00d039103200b9004c02c4c04503100080031420a540c0401000c0000023414070f07240c04030011a03195415482e400c840c0b81401a51400c40c401140161211503000601070005014046655020346807002e00a11f14004240b02d4022500740a03104800ba5103282d07600b000050292842000621002c80202c0b810810314500d48091031075481d040c040e045031090386821000c0c120504442800000590180c2e02d000340310b00c120300c10100707252241006884641082003180c010400c2d944c841d40301e2340b400c0d607005000e800c08802420010b85200d8504000c0e210a01942001070804a10110490851a4028802001181c60390b080055602000c0c106808141d912401200c1c28023444030b10210140c050401c1c1d03591202c10400030300d060580301d13100320341d = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 674988893 1250 674987643 674987653
    0x70b04032108090d0e010c0c0807050f010c020d02010315030602070c030209060603070e10051b251401120902030124080c010c20030a03050a1b0809040c1e0e1002 71
    0x4640b880100d004d000c0c03c2020715009280d007091000480f18060321500c00b0b0500b0b01c0405001038103030000612101190750903148503820800440040d5080d441550020b074000549040e8100150b12035804140c1150546188008640e200c1d01ca000803071b001014101c5007030781d05004c280190b1501d0b0440d030303503c604101c508a03d50300d05010020040e980c0d0b642c841d401110409102004140944280d81c1d03110381c1d40d0070354541d03500c082c41300582d5a0a4500c840c3c00c814000c20540c000c0300e4401543d0001d0351030030001c9041c8a54003070011901009071900100710696140d0641005980078010b011a800e1010000801900803003e506458070780ca42c8091420361107c01c0c079124076600500303043c0b58150000010b41a000b0310351410041580c200f00401c0d898020303c01c5c0b80c0101904000178103100c4070309650340c0c00c8608021011090b610b4101c50007820105050210021310300d81900400200d40075031410710348204110b01a8400d01102d130b0032100200b4400909a146170500d030090701c1d8440080d2009003 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 674990143 1250 674988893 674988901
    0x160f0f0506010e042f030d021c030e0d0c05010b040504080901080609092116080424050f0c120d091a041e0303090203190308070e0f01030e070b04032108 67
    0x1241c44d04400259068054007051442c0c1403002e1040345e41d4461a0140036580c540b501094001d40790000910321106148140c4a0600120701c684160404c02c50100010020088a5081078440e0303000c40d041152590340300c20031021903403541e005040c0110300c04e40c2c40c1c40c0c84900d2100090f0044e00002c042c54010161602088915000081c3d5100018100e00810018245828500c0c055205400d8046581d044840c00b610030405861300600856900d540c00d9042d50b4081c0707a10501d0038040341500e07000140305101c50140f80300d0840003009051580c20071100c2440c0307400e9400c41c0c240c0140142650302aa110034840c03c0c400501c880480a60490014440a1900c1e56402000042da0510013880002910102040501982c001c60100d500241140d065007060210092501c040c004208c0008171124007050308223000d0000e180060070003d103040400207421004400078003101c1c6444400384200400020340c2102c00d0b00610203103000e00d110310b000d90504c56401c0380d02d4800d0101d04003040341c00c500700 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 674991393 1250 674990143 674990153
    0x6080c0111070501030b0609040c0804030f020102210603031c05100803040b0d1e020409090309050405040b0115051608040305070605040e0a02030a09050616030e030c12160f0f0506010e04 82
    0x301c151203007400c0005902d07490101144160180c1c038681d49d001480d20100482094100c03908074403852003030b940c4d00d002c032014030804c0b801d0340185a00302c0317a034110145080c01240d40003040150700500160403030b0f00300030001d655840b05041100e0404205542d901c01c0c803e03940c800e0f103c044050700c001d070010341c502450000304200500c1240a00d20000740d442c602003000c40440d840300e8100030180d680954445031210701d1003008012004048001c01d001c0040000d443c2450b02540303208030b811841900712a0705e003800c83c1d214444661507803030800c441049441c4031708444142140c2c5150103030f220141c5440c03d510f8401c5c0b61150342c0d0001001c2c0030091104200c00143c1c1e10344603601150a400150300e80d01c0709041d030406031050001c01801c40c0502001c01c603510348001d600f02c01c02d08107950309004690310f503248140c0fa03209000c079103119074000c50b00b20300e17101560f0070090203240303078030b41e8118007800c0991100742c01d401c241034048405c44401013242d000e0201c01c02080313014000d4443e0007142424180d0794 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 674992643 1250 674991393 674991403
    0xc060504230a0c1e231e030a0f02011803030801090c080f150301090f0b060a050f210c060a1106010509061011010f060b090111160e090705030106060306080c0111 71
    0x41c0741166141219130700035210081d030601c001030160007403036004101d0b680710ba188030480c4008030a02840e0b25550002a41c000340680382c00d4641c000d07015103803c40032915800804540000240e0500c2504001411150589005900154029680c0c12041e505095140341501d20300340d942010800c0c101c0502034001d44c0070740c10580180b10041d00120414555002c28007500c201007020f0241504c6030250ba060100b1145134511410003125800c243c55100c1c8100020340c000c900241b6089048010f201c20b180c0c071840b480c034004261003021151101da000e40099115801a041000090506036040e0660f950410215001d043d04071032603142440c1401c04100302d502c2c0380880c40100705001c035400c640c2050039800b03500c0072140e51805012403170b1500361010f06940180d0342103001542c040310041d0b000f040881c07142842003076109400046440c00c800910701c02d0019000c0d180324010890002040d65003407090b2801420741c0e0b20040b599920300f407902800d00e401c0309556810700581c4448201d908001041e = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 674993893 1250 674992643 674992649
    0x2150f0705032824081f090605040f03090f03030206070f030209100504050a0501032306060c150f160807030e0307081c2414010c060504230a0c 63
    0xa400394803680c940002e0008100d6006100b145507200f00c0204206800c40c0c3c01c10142d8006000c440103c1410200c005090b1030701e6885640340980103550b689221480c0105101e901c1101c524021900c0c4041d0b44070b050840d0000d48084841b0310341500380208241c1c121100000410006502a00b09803840c3c030065141d14004023101d0400c00824a12a0b090f030199042e1794161002a10001080000d12405481c07039000f402818400c030a00703c400140f541c0b11b4056400c5903100c80d0036503102071086034545115924050310720740c0c1c404014007901c55a090208003141e5403503031120050205040001c217040f404800508060052017080c3e1503091416000206079801158529001815203610b00040d403e5002d03004000b4012034000409824824091024542c0400d00480400540522002414120f8040c1d900d48143e81f412650412244081003242081c0c14030604203202e510010ba66803a0884204843c110f07444034072118105802040c2003a032081e900c000700001c0040310f138603440b00442803000348 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 674995143 1250 674993893 674993897
    0xb031b0304151517150a180212031603030204090f0209030a021306050a0602030304060e010209031506030a08121009230903090306510a0b0c03040602150f07 69
    0x1080e03040c0300c1c0c0c43d480c2103801051441e4001c0c4100310846110307916001c0d5440c0d0b41d880c2207040e402284c140c21303052040309088105032a071907810000c2603091040080304031500e5810343c0801d100b916080604446986c01d224400e0380d00681e10750410303004c04c04841d01291110140e91045c05600d02d1510001001741850384c0480709441140e01c0070058101500c0140c0143c6d422451072000080c6480c0c0000180d80a0340c41160709118845d01081068207c0c02200c00c041d030b25900c00710980b1948000c01440a400040113016121900740684960307045a01c1256110551807001003000310b511180301041e006400103203414400d0503481204003004401025149281d1401d040200d41c03800c20401c101c92205002505460961404411044250741c59514070001410001803c12401d40d40b01d240320000940c0140c00c9403c0d1a000d103040202490f558412a040000e41c3c00c0030440341070400c05004286101d2006654440c284200281410103000d8108502c41e0314005114515400c5241654407240e41c3c = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 674996393 1250 674995143 674995151
    0x280c0305040905090708010f020a090e060904020603100f06091d0106210b0d0f1709010504060e0d1b0603060905040807060c021204030317070503090709050a02090a0b031b030415 78
    0xc4e556003070801e0079650240360150301e421042001003c198001d000e50015903102d041000c0e90724400c030300c000c030780403228107a00c4030f2400d00040052500901450308100b8428142640c9621000e00c001950301a03081640466001d80c8204074140c0c400d0280c502c0316284160b480c40d01c1d40b4201c00505009252030002c1d502002d0314048a18001c07444e4040040c1400080099460501904040f1440f54181200350361400013542040c01c1d03180071400300c400d1a401a96a10b20f03044c80c1100480e240807000907819440200e00041c0008520101d00c005c0154401e128107100d01d40c58102c1c054119116540400303140d508003410070000c0365504081d03d031510341101001c5401a96000121300385115004441241c80e80441c0c00720a05611681506100364240c466541c0c0791200403059610b40022a0444000c0c0e0244109000101d25074000c5031700300e411086c0c09420403e000c0002a010400c580021003002004030400040d0450f0595422504038144130f400c1c038504003912545054100c2800c007005060700c03 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 674997643 1250 674996393 674996401
    0x30c022d040e0f0304090609050106050f0306061b100509010b030f0a020d0c1a040303090e04050309120c180a050a0c02120f07060e0a02090703061511070b280c0305040905 75
    0x14820443c0032180202500d07915a05c1c1c41c81000100458007c4400480c5020004141d80e402042211502501c3c071100d942165a074004004595001c5a081e4108854a0800300b054000801c41d10902000f0200045114502145894211802800c459101e58028008174080b000c000c55030700c40c410703010380751880c07840218140100c295155501c0000e03c1c003100e840000e203804407440038005582c0319540e0030000030ba170750340043e9a000040e2406000c0f900208072540c1c80f80707005003524510b50b0b080e0050703400105110b80010840110b4241c10444803201d407040207100d128a1062952184285e0000c00c000901840001d5952414000400490034001414403c1030795410940c0c001030351006050100d104100021911502d40702e004a000e034144d0404115094041c1c0500030a4801078403a030444548000021107809a18003040500b41c0298480400c5c240c490030018030000d00000c140c41d0b95840c1d14002d450300980c070107009104100a03170240386c1c00694860b00306c03070031140036007800324031521 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 674998893 1250 674997643 674997671
    0x61a0f130b0a0b181509040506010306080d0c02151e03090a063b03030705070f0b07020a0201140a0504090e0313030b1504150512070e04030c022d04 65
    0x102429003140c0c0450726540001d080480d00005111900d242041307200e00700c80c1842845400401d5002002e01604140205c81da242130230351055600c800705140224800f07175903001c9903003403a80180e402c01c00a42e2980342441981005030000c2101c084004080b072504480000390141c10040c10301001c41c0d56000808114645810061000b03a207802007420800501000c0c01a551403410070001c00512400c008608a98898800c81020400601015500c0c66842c000c1c00c480aa011050071034070f000020f03441401050078918140c1c801c1320300da001080d011400b800090402e1480c051081040c1c00100482055594804103030b400300c6000803800b15014110882c00c0382980507120756004007010450000051040741810b4038001d2080c4000300c0c19840100040c803050300c12150344a4419202c1780c200b08214102036800c5000310f1018400e407101c164581560160030001513405130006141c604111040d481c004041202440040401036034400542200c1c81c02000462603a074461582d131814501004 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 675000000 1107 674998893 674998901
    0x60e0313050112182603130615030b2e0602060c0f0c0330040308130206040801020a110d02030405031009150603030c061a0f13 56
    0x1a400c00005540304003a14030384040c3c60356582414804404901441d00c465489004502c0c00d000c000140d10030300c0502182c0200001208000b4808003504075909500d0f295401000440d1024030810511440e108691010340500c1c02034003000885203803002c400403500c001c1c101c25258081040d403240b258040501034400542d002c88040740c502c00b503280240a13040141e4008500d01090b44081a007140c00250400c10b1506006c10a9400301180118003da019030354000d015961030282c40041c4400b102408005010043d6030001040d900c45c001260090021a030081d50340b0b00030000b00800e200404000f000e190f025072541040c0442c404400c0390121180100200180e00088414100403c116803080b1001d01440d81004210046170113010000c6000341c9441e00c0d131203600c0c00d01c002615001c0800b0300104c4022a00050281da0303c0e9000706c1043c6050b0340d52084401c4541c40c2200074 = true := by decide +kernel

theorem cover : BRFrame.Cov 674820143 675000000 := by
  have h0 := BRFrame.cov_init 674820143
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674820143 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674820143 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674820143 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674820143 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674820143 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674820143 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674820143 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674820143 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674820143 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674820143 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674820143 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674820143 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674820143 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674820143 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674820143 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674820143 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674820143 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674820143 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674820143 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674820143 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674820143 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674820143 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674820143 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674820143 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674820143 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674820143 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674820143 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674820143 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674820143 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674820143 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674820143 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674820143 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674820143 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674820143 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674820143 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674820143 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674820143 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674820143 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674820143 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674820143 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674820143 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674820143 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674820143 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674820143 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674820143 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674820143 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674820143 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674820143 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674820143 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674820143 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674820143 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674820143 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674820143 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674820143 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674820143 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674820143 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674820143 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674820143 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674820143 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674820143 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674820143 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674820143 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674820143 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674820143 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674820143 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674820143 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674820143 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674820143 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674820143 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674820143 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674820143 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674820143 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674820143 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674820143 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674820143 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674820143 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674820143 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674820143 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674820143 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674820143 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674820143 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674820143 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674820143 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674820143 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674820143 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674820143 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674820143 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674820143 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674820143 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674820143 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674820143 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674820143 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674820143 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674820143 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674820143 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674820143 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674820143 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674820143 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674820143 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674820143 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674820143 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674820143 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674820143 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674820143 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674820143 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674820143 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674820143 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674820143 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674820143 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674820143 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674820143 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674820143 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674820143 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674820143 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674820143 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674820143 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674820143 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674820143 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674820143 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674820143 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674820143 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674820143 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674820143 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674820143 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674820143 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674820143 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674820143 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674820143 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674820143 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674820143 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674820143 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674820143 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674820143 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674820143 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674820143 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674820143 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674820143 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674820143 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674820143 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674820143 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674820143 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674820143 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674820143 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674820143 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 674820143 ≤ n) (h2 : n < 675000000) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
