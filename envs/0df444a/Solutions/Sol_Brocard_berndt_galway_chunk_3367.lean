-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3367
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T09:27:19.815784+00:00
-- url     : https://prove2.me/submissions/33fd5ce1-8075-4254-9210-1a983e59ac9b

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 605395683 ≤ n < 605575539 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 605396933 1250 605395683 605395697
    0x10f0e0a0906022709130809010c1b09021e0a05121909050f0f0607201015080d0c0f060527030703110a12050d02040f0e011401030b10 59
    0x24403441d41c04030380d45801d000c078126400350050004c4a09403411218030304d100f07940a401158005141e900d4488855400072101c914000b43c2800643c0e00032075061007210f5981c140741081c0d03048102e02c0f00100040c0600c0c40050b0ba00c0b01c1c000541804001c00000c1d51038a4003051140c80c180c0c913840000d0307030414001e0034042d0300d10361a4201c2075014030304000030b02c02e0780e1401e0400a5040103008540c1e00c800c080702c00102c1e051a1010f190341030326150308075601c1000440c00c024081d003d00207a484c0040c00c811880a44400c03009000c5060b00341d504800840740140d12040c0104403a0300c0801c15181d46003002c1c905806e08454030313502c03400c1c60110b915000c0d01c582c1d190710205010a80040d1023103d001381a441040126002e44800c030749075004004198046188020000349100c8003103403d000311680b10300c0c0104184450b0600b40c0d8135030089132038108051360038480802e1010701c4070040b00c050032082d26031202c190b1400909004050030006007504050808944c40e000e91903038050003100000c01c0c2010a = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 605398183 1250 605396933 605396951
    0x51c0b0705031803071203050f280e01020a020c100f0c02010804051609050a1401150302031009060b1305030c090a0c2d080129031329010f0e0a 63
    0x3c200703009100318650350100180c03010411a1038400c45112100340d071400c1c0243d50766110b8500b0210000c50781c5030140703501e5080c014202c01d20541c0e20442594280320002e01a54112500b6089130030020581c001369112202980241c50055a10140300000e46018146a001100e00501013805e2110081c14415103001190400c2414807400c0c480b40c505911450b031450756800c0d00c2d00a4002661001485c618246a0622102c0c6c404541ca05a03030b24908001d180a59629048000b9400100700040c600380d41100443c00d14150301410004141c0c0c80c01c92529620006411010404150310a07031295104804458140d00c0e2100c60356848100d010b000162544158000c0d00e0385501302081e0944c1d03c2c05050380320504d484501100c0419207403a03039003400c160380741d0312200200c2e00201c0408182c2c2c0713a00200303c0e015805410007945e1003030030703403c10784d000c41c480da907601c40e2081c03828411000411090061107415148009210b0040064200e50f0101910f0028007421010001e4a4003110648500140b = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 605399433 1250 605398183 605398201
    0xe0a06052203060c120b0d03200705090c03010f090b130b0a080703060f0b030106080604060e12121b0f090d05070e0c07050709050c0a200313051c0b070503 68
    0x103100071034006500b4846800100c030000c3c01d117140c03280f406501c1840d00e000680d580c04c0c44009034809580c1034803a800c4048124065481c181940c03c01180170b1701c10a0404202519130403051740c01020305105994681d4140405d1100b160318540080c4c4056180103440c00c1c940d9a03084a00c0d40f00c4443d8207000929080b05c1c4045210520aa08044881d00c1407e2000042004962251003030b41000101041090704040c01c040c2642e0080c400e1408940c41a008100442c640750320500c1811800307800c236601c2c14032030444148607800950700b401030000f100c820041d00040d003003074020050200c2001589080c0c600c4c0c1d01e0031901d0181480342030103001d180c040320003000350400240002c0c0803221840b0801d89400000d000080e48034007801c131058050344000040100a038043c0700e01803009004031f28103080134440c0c11904c01c0080c099200301c5018852030803020003c1440180310010b00d80300b0001c0315905000c00d214102c410509280d5500701c440c0b0200d0301082000a006810419618060f5505c2d2242002 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 605400683 1250 605399433 605399497
    0xc120c02010309051f1b17090a0b0103080a080f040803190612060b01020f06010b04090c050d0e060106140c210f0f0307030b0f13240e070e0a0605 64
    0x20080c018407034800b01c4500c0441725409444074038000e4405003c00e0241622002944041481e008007094038145c14180b005910141ea55000440804403035500389983c80d120494082130740151500100052020710a540c440d800c0c9078044004045c02a203401c140d51040c1082c400204181005907401c00000120755954200000030b020f50b80c07045a10404900b03040c0014001342071000c4c054410941d50800c002c8000ca01c413030403200b0254665040500d051880d5001d0401c040c040b0041250402410800203030306d109848404281c0d40c0207002941c100780001c0c0c1b49808006614016407001c1c018100e1007003000804c110715508421452000484601c2004081e001c0e102c26507138601da000c40d030004a014070001a40c4500d1b81030350180600019207061005c849081c2e00c0c42500011100e0741094a007125400c41d00b045080042c400384c1c148010f81e85c111691202d81c000c0000c04101c07100380141280c1c040e91345034a140e01150740092076460214003805038820356610302001c0e42160b40d0502c00b0014402 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 605401933 1250 605400683 605400701
    0x2f0c010603081b0d080a0c05160c03060f020f03040602160c0e1902270a170705091b22030b040501022701050d0513060603050a120c120c020103 63
    0x9020031034491504075219008031900080e00f405410390408122800a820090803840f9120b1210b141c40e416400000392a2000600f01404410000454640d484c90841d0281a01559021541d0703411480c088058407404004034101e540103204402e00341c0c108008498105a02410041e600c1d81c0441000720740b40e00308940a00b085038601400500c004202000d1440345441e40713544c012003410420008124021540c6218001c41075000c41c1001540c1c5010f5800c1c030705070041c0417100141da2082603101d0400c4800d0f08140740d80108500b0451b5082c10303a00c4035003087c4000ba285061590b6201a59043c0c0681c10b8514a41580600000b0228210003901c602441e080381d1a80d0040c60941401400f07075024080c0c1c0c02c0c40b50f00d0158441805035245052044095052b5561407610092610300400f51034098001031211641020100002d8614441c40307000310b10079809020160107500305000f007014454000814024103000da00c0c000b07006194002c03094801800c0003008500140012001010481 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 605403183 1250 605401933 605401957
    0x809030a0c020a21060c0c030504052806030e0f0307210e03010f02031f0302151b010204060201090c060509031903030e0609070503071208042106021206040e012f 71
    0xc604c400c000c00c0100140700d00580150000c0c00345840780d010403a60104200170260025109000601030fa00e85984c1644000e607a010042d480c4a04202032001e091419501990100750b8400c20354600c9002403280c5145541035001540c01d054541d00d80101082a01c03005415172244a0038442000d40241181c1d8100c0324050001c016503141d250001000790f100356140c8401c003c60740c03500c401901c1458811400e80398064101c0c008086913451005641d0480003081415140c01032100c0114042407000d08001c085c15070000c240a00b05080c10303aa61045034114008000c000c00404443e0f40740000c511010034442402c2c44814034140c03d084008200d0050780400720700806003848000100083c28106032a01103080c0d4003e903568110400700300882400c0246510003c3c0810024030708c04960b142c88915044001455a49490f03131590100c3c1d01c200c03203110701c2c41e00701e60600c540c50415218038404000440002c2041000302d40b4071040003c0e03408030002c08401d0500001c2070181442c02615a4a6128 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 605404433 1250 605403183 605403209
    0x140408060c03060a0905040201020c0f03010917070c0e07020c0f0103020706051608160e0d0c0b0d0e0106170316020109230f24030c0403080a0e100809030a0c020a 71
    0x1030780c44992090f03070040d103e15928000403c00720807a119690240b5816001001c82c01c4800c8240070005100400b9281e00d5544d81510764081512443d40410360388040080c42d564503018a040c3c00c006802e03030092418200d801042208098000819a00301001160882c15035801040124081e104046004040604050500001d4185825400500081900c0710462550341d4410310300024214030f100310000d5941c0c00d02c20340034140807074003641160140000c8100e81d1b846540c10105071740040c68440983c2e9481c82038001080c0e0030311400c03001d0000c0b1740f010303410b120088110039a01d0040c81c05002440b5400d400070b004581c01116198020302d190581c4080798000c0c4d4110b051498107103801d05004242e8404408600d00d400c02c00c00b9000340c0090011203080c141e1b201000125017004000d0040560200008030101c0c00b903c02402082c41d01d90390b024501401d04090011000c68480740605200e80c0c102806602c1c0008801c2d111054041c0c501908040520700000d9410462540644080510 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 605405683 1250 605404433 605404441
    0x30c0b0a1503031205090610030b090f06070206010303090f030b0c1c1518051003120c060f06170105090606060a0c060e0c090c040302090708041b0e10061e14040806 72
    0x6041c6003504844c40b900b00015030361410303500d440c4e00c8100e622400744e10003c4410700016800c009006d80005480d400c80304040c20200c001460120184d8041d07003d0380c00b1400400c00c050784213a081018005810012a2492840ea100b45003101c010b041502c20300004105902030210305450280400d59040040c469181d9841c0343d200e8151541c051025100000040c95003c1401401680d004441d40014604603510396291414908a0204a80200102802d291002c100305026181401e0807107000000d06a10b480601040d44001d000c17101d0050741000d040000415010840d942c1c00441502c2050b0b440301008001c885508044200901c1c2518111b1411a4400c0007c0e41a40c1c0ca4010b407864041903c40c02d0b040030150245101c025800f4650b070001a910b188503240e05d40d0001d200d6048200c00c10411000404240519002000c41e44040c00030412a5100018188018002c6d4140a000b0b500c0861030402ca50b20b41c21401010306c00b400c8011081c0a004504890041606d5416030f8480d0030 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 605406933 1250 605405683 605405687
    0x9020901061d0406081504050a0b040b15090f0402120f0102040f06182304090503070317060a0e0105060903030705070b0406171905040c05101806020109030c0b0a150303 74
    0x215100200c0860070711244881c0b1900346446018284c0d1341200040095241e8038912800303004004208a8482c00307110f0440f40011592901c05020743d00c00c02c00701c1410715000b02017203071841048011511400f008814011050003841007203030026010341c1c98a82801040903650f02c0c01c588480140c1e12580700050005060021940d100113175181c3d41d85030100751144c410003a1094446000c1c03801004018203030f580d00e0ae00c4500010f582d10b403000c2d00100e010800c8d611034074103503000648290045112a100340080742c4403103400a5024500301c541003801c9003070020003050030905000d0f241c0205030000344540640e45c2001901d042c50742c0320301125186601c403070078010a80c00c03d100c0c0c0c0e004185061070f03031007440c0b20204101e4412180b1707000303605034001e5800f6004068240070300260340c04141c000c400b04054940d841c4c400b01a50090701d591945001d5010100600401980108211b91510b0007540c0080d9118605c42e00103600115402c54940b110f4081c04001c00010b8005004400000c1001003090303 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 605408183 1250 605406933 605406947
    0x6070501090b01050a0605030106081b18131803030e1213080712110607020a03020402190809060601021c03060e0f07080702060c16240204080d020a030e060a02010902090106 76
    0x103403182e040108166614004c2c440f04400364060a03012070002d000601c0400d101c0e040d01e5900a00040c40d0343c100000d02e040000075681b102d501e42e0098255a0310050840c14490001e01e4103c0020004200840f880c002c420100400050001c0816440d07504007491080c1c00c00c241141c411b0011822942c829011814951079800c500c42d08d8224004c00c0303000100078449e01e041022941d001413180c2c2403001e602040000550000340c0482c0d102c1032101c1d022000d80c1b00c6102400452803203651010f00c181a210000d0300305400203040002c80d0340044100002e90b6400305014034a400035074005080030303100500903406499942c200307402d0350f0031140c00c000e0701e114040c586500503401a168503c1030f8484080498036902c04503440c0b404200c0800900340300707604201c9020b495500500340658600008180b0689407140190390f0800550042401d00c090394050104514121a500080400710b92680c1c0c05013802c80018540c502c103a01c0400c0400c5064001c1d045544107507802046100550384034000a0880 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 605409433 1250 605408183 605408201
    0xf060207090c020703030e03150103111203130e061f0302040510110604080a11010204090902010207050a0e190209130e1c092c040302010b010e0906060715060506070501 74
    0x520440e5000240025940b0612180525990181051a0550f1401d54000c0c030103030040ca03098460101040606240d8141550107544103a51007000607044400704032a1400501994034103030420082c11281d4440ca4441e4000c681d8040c202a00780d555000010b05a42000005503002c90040d240d0b0424003039040d4001c0050b42c0d011103102903e040c45100448400340002044149980142c0110b000b0a5500002d44858242c41c81c20750960b081c000340503820798015900c03900c1e009807550030744800c543e0188001805410180d4000c0003840c94184031004441029004581d8a2001c400d911074604041e0100c1d0300508000e406012034a24440b2620014101e920b8400c045000e00c00c4030341c4c1170303010a84064025082980d0760340b034502d003080d404d030b05029287e01d0002001030940005591b44c0c0d4452102d02c0c4035500907000043c00454840c00940742c0c4890040d035274402c4901c00100501960f0341d1040e034040e03940001d44188075460821a800051031550800f40d8070840c081140001c01505410103000 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 605410683 1250 605409433 605409437
    0x4080f06091902060915160c0510022409070509090604020f0f10030b0a0e01080708070902040506070f020a0504021308070f0305060f07021507030e01050702060712090203160f06 78
    0xc0710390b80d00312000755524071403000b035002c1e60030044103455240684a0010000c40020321501d00154021407020b0002ca41000700c0d05541c501d84108030750b2408010505081e4030b01e001514003c02a001c100f44aa41c4c21401c3e507150010403c003088601e02e082104101500014017442c20b2800c0c10500c203550380034121380880c8144c1040c600c4900b1400e00100c0d921150b44007074035a2a000800c6c110540180642008041d0841940d050000c0d11602100a20b4024a0500701600714071307003802039250400d041d9400141d4590700402040266440b0740c011501c203160003e820500f4404103100041940c04958002a4085d0011131503d41e00100c54031010100c8400c6400c9400142e940d2000c0041100340f803102810030b4000c18001b82071080311060465101103a03105690180c150607072112030781c41090b201003001954418808140c3c8609101d02138102491f0300041c0028505071500034440601100c0022a003610385203030604549040104000b000c4108052101a5450f051100d500c00e40781c0c440d442c0 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 605411933 1250 605410683 605410693
    0x12080c070605041712250209040b1b0910050d09050f0d0e0a0302100309080706020d05040618240f2a0516080315030607020604121403010e060604080f0609 68
    0x4c1000002074022020b080c4044043c24404400100c00340422603c00c9607904480c0d042c14880182d50700640b15104506c0f03030803c2d041600703000300d81710251a80c4114442540c202001814410f0303507a02400741c840354403494901e41d01c01d507806206000d00b100500040007881070003162506030201083d000d014505543c1d44004004804081002005440c440690859584440d1002e420320942000210340d020b0604645812101d0b602e9104903806800540c1c4403e03030b600140010005a8089c10f841072003501302115010506444481144c2d0070900588160340c3c00e450b4031080240640c1120402c000c6404c42007006c245581030550500c1740030784d00c0c2c540c070411070403641d10300c140a27a0589807031484004900325103403441d81c0c40303c03226800641681100c0e018520704035030950b41041000e104030300c254040d01e0203003090326000311154241c412120620107000702c0c0012710781c4201f00381c0c2c2c111a03444004088989a81021581d6481030ba04450000c0c00b8200c103030308549800140c45401003400f1400c9403 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 605413183 1250 605411933 605411969
    0xf09101a060d1a150d0c050708040909030815090708100801060b04030c09022802030904050c0c070503190620030103050303070e030d0512370506030d0912080c07060504 74
    0x8180710b031881c04134950426061104030481c031056030002e5450502c6052451810446850364500c58115038040420140c0310000300080541c460315490f0840c002c29160203840300c40c140000d00f42c440081c800000c1103503210020721100c1584011320010300050008100c90b54952624039829030003400141c4141e01a11400035803040300d071080320000002401c40c90407615904010f0701c1c80000d0441310308118401070000c0c8003d6910b03449440d000e400980d21195540041c0904c4c90306091140c3d10180c480c3d0409900c402e498074102e420b03001525070056000410440201c49218160514079001d1001b100100010042080c00001540a0310084d20b0300b0038440b1800c001c0658501c1c080c41010300241c020300c00041501d9403000110340021150042501203074007165904081106400d400055100500d110000320078144a04c4c1d4000300d007540034001c4900401d8018021483e103120b00c9044104080050003400900015542025440c400382d60410740d8401c40213141b034129004003051950b00c07035121 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 605414433 1250 605413183 605413189
    0x70507060e071a070f12050405030118081b010908031602060a0606120507120e0d03060b030f060d0515130303060e10030b19230f09101a060d1a 63
    0x250040300c0d44112102e00868644a20007100e0f00310341011110b400c582c51711940018080c40300b4080f01c055541e40d041d1101e01c0c0400305070075034854069494425078000d03074004c045106101110141e808204400075241c1060301d03210300524202e10040d040303c40110a100e007000c82d040804014417000c1c0c0c2103030401d8851449000071568a446060045800c42a00d8035440002e070b0002d81e44130010707003800e8112944401482003a900c1d1501c41100d550414603119026981510403000500f481407078240c154075159001c0800e4000c050181071180303150304002c0742000801c202e50000c01c1c500052120040c2080141213400f882c50700c0044003c40d05181c0702017103001c202d44082d4482e072080e00415014a00d0f54844481307080002c0c00d81204010b010480b10307614251409403140209400c0000800f1101890f4008014607003d020304c81c1c4501d00605014008000040f82004220412400201c02c03001e8009900e040c001d03c5c0000340c0200e0702164030314404065500011694842c1a0b401e07504408040070 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 605415683 1250 605414433 605414443
    0xf0c070314222d0f03020d03091d07030e0106080303060616022e0f020a02010806041b090e07020d020a0b0c0d0e01050a0c030b0303041a0f07053012040614070507060e 73
    0x307119500c5401003c05c001500e0046585030300ca6010b403c0121819440f252811040748000c001c1c0d00c4071150010a0008450341441252100e81c042c5000704011810702d02c00c41e0300c03844060200b510903100421214120702d11001c803040d206030f000707155440302d92444540d105100b010fa000f40d000f1240340801a42c000c0c0c09860086040441540581401865a030054070b0000000e401e80d81c00a99906440d4000d10041c0f0010001e07071919100c000c45149410300181001c040202588115049449480d000b2500041d5000b03c00d6482031030103541b9580c80b00004260f02500b040c020004e81070454090b0050f206511442c01561260b200780204150800c00f80c0030b5aa4004001e0f80560081208100e22410410010fa003070200000c46841c00fa0080403541082c1c0004505580e19003201d9080c060300c0001445a4000300c000104c5d103428410201d02e01070141c02031421840040c2c9410340001c0c100102e035441554820710030980b615003070402210080540c0c10882e0200c80d11440c000c0c1c007006408001503 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 605416933 1250 605415683 605415689
    0x20304020a0306090c0315140901060602030406201e0105150105030a0f0b03031207020712330e0c010e0613050d1502030109050f0c070314222d 63
    0x2600610710301e15940c01000b003100020581d8880c3c0012004030014030b86016a2981514000010408400080d00c02142460281c007501c0103030b16080c000c00026802200340c0d02252181d0400718007110505010802900311503440340d0590144480c010038070401d240020021014043c02000786955844100c5401043c14805c00c0c00303e070701400082d113400382c0d0307070408405a0740304440450415411004640365408c01e402d4001018044410442070550401142b030040c0f039041010503104885403102c5d0221206150195400111500501d5841d00c510800c070035110075030301c010000210242681030710b41c14034041641c00200c4441c0017002c6490180160340b180050140343d02d8a552400040180f121f2003c4021141005282a0b00202c0d03519403006c1d5000f0300420780e02207614a052800202000070080480d6140c0e80c0c10700c0b015020035403010704590042c2c0044540c07641c91040280401e03030110070071400c52540300c4400780031950300e04001d003401c411403115034044901440e07100c410000540b240 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 605418183 1250 605416933 605416939
    0xa0f050307020a02060c07080a0b042618010309051015060905010e06132103080f04080d1d0a0501060e06040207020904030c020103020f0a020f06060f030a0b100b0307120f02030402 79
    0x50303000000740c81d2045c01040070800e031030201c0300866035805c2c8503801c1201d620810b4424580b031104110074000d120081c01e0041200d0400c448411103a0007107214140a1250812141e20800c1410031003640640c1c041015070f5048411245a51b101c940280f019020952140740708459101c1c00040c1e0031300030b503025002c0c1c8405071101c09a54181c2e506100e0300350098100100740389110900094840088842941007114540b01e502018209040c00342c0100c0015000b0b08450740b0040820002c11071400507200d654a130b00c0f0000c11100040c0690300b044986440440e41d4034020301400d00200441588604120350b1003d080311400e035103010400080340500c03c4007941151101e4002000a44518010b03000741c1d205042c01801c010000711070b0b00190300302c9102503025900c105528100c1020400011b070723124800700e64a612100501380413a84940c612100200003d40e0000400d030f00e401321074401c82c041e10500c84055100d140402c0c0051280200c25050380490303252000c044540e41060084910032600a = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 605419433 1250 605418183 605418193
    0xa0906051518190e010f030309030210020a0b270c01090303120908070f2006250b0708010e090d090506070501151404060b090a050603041a0702030a0f05030702 70
    0x80c5032985480e6001019012500e6000e04602c2c6841d5a0384920a007000c0c1c4180b8201c04150030003003c0f50805106070010b480300d00d80a101040040d901150610551780d050740e0001840d05a8001a840d24060220061142621404119500180350581e0814513400c2220150003049000c80d1512100440b00c003d0000340805403d00100b4090046c00d043c81440d0400029030300f010741c0f541186c0303800c001c00c12507113410b8403141003050051701d014080e030740f210403916042810090b02c006041031050a070f020b0348001440f0806042c500444868010303068001b00078003140c1c6064540201080800d005000c2100ca034000031400c1c1d03500004511541071034507140e085080c4e080c01d04200181e04000401c440c990349800e00c04503424031002ca8200223050008244142040c200304005c2920b0054101c900c00384005d2210090581d41d803800345003140c030b0a036142d50703886d203c6084c0209198180081d03007000103440306c140320307a0b030340d001004001d01c500d1603032200b01900c3d174150201c95511040d540d8800503804 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 605420683 1250 605419433 605419459
    0x117120f032d0c030f010b1c11040504180c08060906040b150d1506050f010203040e0601030902031902040b010f0f121b120b0d0506010e04020f0a080c0a090605 70
    0x3a00d000007060701c201d5041e0004102503107000c1c420310b1034101e41c12481d0020210a0100414658440c513004d8483c0448171401c25021501209051842c000c82c1c5030091b448410058407914030741c04071006800d0242003401080c210042d0102c0681f14654101d45018003d0030000784100081841d40c0581c03080c1000e044903444903241c02e540c01401420442c088c2100742121000c5546002c0a480c1c2c80c0c1c441c0c85030b400100e0442c04c850702100d00a600140c010070900410000c9a03902000b00c4066442d100001c0c1c50644031b08004a00901e40c0540080d05403203050f09000300002a05090f5034a548216001d0009410f01001100c8501c115807807400031074401e0f02c04502560203101c1e044090229008001000240f04070150300030b011100b42d50003c100c2400c00c010700c4001c213014510300d5840c2650301988418040ea1001e581d60414401d503d004080c241c0410708656800b4590303044490000c1070681050344852029844456142c411347c402c3c00840750004800700d05000d03040440d1001844d6003000a0 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 605421933 1250 605420683 605420701
    0xa020309030d0903020f1516080a09120c05010c0c020603040807141c0908030f0f1c02070812090a05100b041508060f181b03010b090117120f03 63
    0x340c2806030a000038458540007030b155106191040d4000c0c3c1c02040c000c483c0c551030505004c4000085064100118104003038004106018490038529242007491591544229001041c04c010000d0540188000e4141c0080c0d0200350340444a004100821140710b0000b025118014000002034101e00140001000706010b40e0252084600803c075044402800705003407070500d0544505150400343c00c12a0200c40c1d176001481c2c00c00f42040c08000c2d071400035401d0750f0388081c0c003850484404854000528400e0020303001c11401c641c0c00010025500c4560074a08048682c0140d00403114424400c00014000d12001036280c08032074111000c2c006004044a20a0150111070034003034206440355010205858041680e000509204011b08998100b60390450040b510240c01300300b04504d80d1018151905011515894203542c640030f6140d002c007500c011074050400441090742c4148035100001d0104c10046105044080fa0802d4844010308503080c4041d9008071154100d07030701c1d000c0c400038101c24 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 605423183 1250 605421933 605421937
    0x10e1005090405010207060e210304080409050c0d0c0206010603050c0a17180a0501091202030c15042102010501091104270e0f0c030d030b060702090a0e0a050715030b090a02 76
    0xf40600c0015152013800c0c1c640d00113072040c900e12201503501c84401000c1ca00c2c0c00f0400d9004191403580102d1450400e5102c86166020300c0c01410b60b256541e2011400340030021003164140f802d00002880001608903000c0e450b20024840d02011900b82000031b6143c042c0d50080710751a440c292aa5511800c0c6400071a900400040500418629818650160301010421756001c0d0f0711440001c10350310068038010411901001031003080d54028850f11032105404150302c01018101c0b020204695101d04041c2043c10741d800300c5c00b00b4500c1c800303000260141c1c10342216058444021050111102170100940300348036520901800d0001610316150744196031842000e8403000c86c0c0041143d107020001982890541600502e190b800454a2401e50500b4000030003003d8450408012039001c4c48082852071041150092040d10342e24001103043c2c5103a400900e810307100c101100c0c4045014a4107507590350090042500345e403204020381c1e414a00c41d001d00c034940c0354040c040c1c0c0102d4039512007080180d = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 605424433 1250 605423183 605423191
    0x17070e04060b0c071d060a0603050405011107030f0f090b1206121c0315060f12090c170601080c0303091e040c05070b150f280303030c08010e100509 65
    0x152141c40c00102c0c25002000307803002002640c00f030801c1520307014402990f07000384803100440d0620700c0c1c200404c2d0303950104040102c504908001c00d1913a03c502e8a5030041400c816030284900300030034088141684428900c24044698480a10710040707940c0545011b8420700c241c103100581040340ba039240e8108504c2640204002c3c12100050000003400e60801280045104000520b110320301c0f002036050240704441c6241302200c03012581881070083c0207040d030384040024014958510040c0c035085602001103560800d07038000350a0380b0b584054140d0740e503105450304c940c41100004590000c0103d900e482440c40280110300e49525031080c0b002c0154600000d00c61380d00d00e04000c1a990300c8030300a08030820342a0b034441d0b540e40854a000c4d4005a4082c08420b0411030032600065140c440c0100f100402004550b50903981316410010f402203c0000c003000000b90004000004040c0c03d50480c80a00189442c4c42c40c2680c1c07522082c0b5400281285e0070460105817240400290030000006500 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 605425683 1250 605424433 605424439
    0x2130501020d0305101406040e0109051609030803040308040f05070b091813021215130c1e050609151801020124050105070305040e040c0602071202090609090703050604080a08010617070e 82
    0x1050381d90081d027602c042d4268000c02c003054482c420010907610300d2644840722100c03424010a41c90558580410300d0100800c02010b0084030804107091280c601070000030f1617400022500c00070b0f102ca0740c01d00307142c10032a01c2c680503602444841c0080c480c411203480c8143c00140642034220003940030041a440c00c40c9004501d400345000d49802604002042c91140343c8404503050451a5860801c401d007009511424405030b10340364441d10a0b904c0f090300c00c2190300c1110165181d00344440003e00751003125018504c0c0f1107000581c1c1c0101004c0c1403088000c06800d030001c00c0442e01c1200c8011000ca0486028020700e40c0d044014000e540c000e1010302425400391038654181a11100e2209800070705803002d50b001c00d913042081101c00d07810400c20000d0882c0740c1c00c00b8085400d9a01081c000030003d80240d21405807100041d2031114104001402560400301b00c46003410641031000d030583c4407030f0380d01c0d0006441c0c500115446003d0503000c440c1110040e50341400d0b83e14800100d500700308681005038 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 605426933 1250 605425683 605425687
    0x130b010e0303210601110d0309030216120b01050603010e0406020307091505030406060b16060b03100914010b150d090c0e07050406020f0703170f070602130501020d0305101406 77
    0xca551800c00c060300807105280020801200c503000889080103004266604208004a0a03010030002040c01d40100ca2541800320b6441e20030315040c2d00740320612490181c43c40c06410001b80b2440007012a02e5450301030110b8107542e90729101880311510007401401d0650140b04085070019200d1b9009661204540c0f41408156840d81114000035181e03c400d580080d00c040244020b00004c1d00c1b6034001000210747d003904c2d1002c4503d11100401c421a07001d080345035210004c0c290b07511305001d55886c3c101e401000f001440160305e0110781c0350000d00022030196107480509401401d01050444032034082424041c240014040b00402038a24507008880703000d0f60300e10004000b41914200e500810090b100c5c2e1b0f0300d40d8103100d0000d1806880782d09080b155031200381c003080810441e441c0f0324905050304100310fa50300118180303417038584511680144903504c0020036244074840c241032803017590000d030b09440d62200c4101c0128140c52081c1c0d18409482c0980c001040b0200c48004038000c0d150024000c2c40c = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 605428183 1250 605426933 605426957
    0x10902010e130b1c03030e15190f060b1c110714010902221406060316090810091101170c0d060302120606030c060a081b0d1805010c050702130b01 64
    0x256001c130180c42c00742e4140520944542003507054050301e0f40c00b02c0104001d0850285100b18034547d110003500d0000b08c090f00058803190180244c21682c09042c4006003488881c1d5107040d03c00050b44034400f01d0110000820001c2200c0080d80100000c03c080c1d01401410407a0350388954164191400554074199031710b55850005850394200211042c0c18100508d01c603032254486101075505c200900c00003501401c0400c5200c0d82c400c030a90350440c060baa0343c02106006464155461045500b1000c814070403440703c98400283d036040718140a216546d01099083c4c040d0054071030064001d2010000d0344884002001c05607440d0207000b188400c220089010ba5903500804c10040c032001200c5e0098102c90200b0100341801c0103030102c1c0d84001e031050352401100e02c0e8010280074014001c040034041c600106881d8450317060540b60302c85220300041000c9210749034039140b81c10401c1c100326055401c0040b401c007100d0040c000d4130302090f000703010000461403100030300c0f004180d0b140d0094103200d80c0401c88 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 605429433 1250 605428183 605428189
    0x60d0305030a110c0d082706240312030405011a0d0f020f0d0b091b010f180b041203020706093f12110606210a082109010902010e130b 59
    0xa0850500300d92210f890382d0030700200e822010303050047d004601c810824407000c0076140000d0318691000c403030061148010382003a0824511800110642d615100e0f21420b030400310152801180113034402c030001c101103a00507610349904101c0d81c1e4200d9110700d8052080000c0f40c980401700e010b151009121204110040380003a03040701e140c28007920000495020485841010001600311140308110060001c0351807000030018459515a09c0422900e07941400050824004640140c03400c04510740c4c5950326840c0003446601d50038030507401031041140c0026098040c10b201e0054444132020040f00c0030358a4000d041c40e40c0c400b01c24900c902c040303c00907201884011080451144240070310105040c0d4803400801c00502800074030358030340288050003960307030311400c5a4400c503281c81c108000c591030492a203418003c260801400c6900b0000d40013005d00700300c51244c03540001c2200546816214540d800e82242d21114000340458240404200146014004501c0c0034272580800b0540300409008 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 605430683 1250 605429433 605429443
    0x60301140703151e0618080102030705030601030c0905030c01050a110616120501120f02030a050d020304050103180c0306051027050a0504170d02161a060d0305030a110c 74
    0x100000180e5520300c3d54044540304800c0800070701c030112481c041d1080100721a61140050b120705400e00c00c2c0703064040010720700b9803400e034010602c80000719224a451240a070480e4422118640041d02e0f01402d0039196000e000b1242c1520320240040541300c002c400152410381c86140c484042c08004240000000360400209125920300391041d111120910400f070014080912800310460811005002516038038003511040c60304000030421355146800440d00701211810040d100b8029150580a01600000100200c07502aa0304004001001010302c0b08034a01c1c42008140d2014001c0c2040481c0035600101e82000f91440c49100385035460384043c10305000b0812020000c00103040b04404511548103ca60080b15a60240a6498960b481c000341d030040030142c9005d040c1c0410b41c449224160f6041d0707081e41d18168004002b001040c2460861062998003405048050340006a254103000004180995054403101e083d40c60711100c002c080c0a00114082c068401801400440c0c00c0c1040 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 605431933 1250 605430683 605430691
    0x30e0a0605010f150801060f1b02091f05043e0d060305100504210e2e050f070b06031603110a1e03030e06040803070b072604020906030114 61
    0x507401042c181307040c2d41d107409a12280e25050500400400401ca1503030400c9004407030920920701441d40a40000070404e89c420380060107500100c405080200080c10003900504013804410940407590b41c850401040e44c0188410349c941c92490520303520b480b80080066003900ca020040044880f448403040c09842d04000403200340a51102d804200b4454103002c4500149056841030200b0724ac40d4680e030f45411036081c915040b448107080b00860441c0b00d080e0650401100030b058110342c03031028500380f0858950a0700d0550080c11200c1c00b6034507d0080d0102c801c03890a154081c0c0c20a20242c0759800108402460700341c26003d10740c22410100c101c1d00c40c010280d031140313031070008010510303003408462101a00055101803550300414101c000414204085a03030600d00850b888000070081159809241e001e441c09100108051007040345002c92544610a15aa400380300c43c0d4105924480d004090007000400c80c00f4408200541055101d16601c40c0d03020300040343d02d100b00004901032100c111 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 605433183 1250 605431933 605431949
    0x904020f0711031209060a1809091401090b0112060b0904080d0507140301140f0a08280c061209050f0606010906020a0b0a091a0a0f0f051501030e0a060501 68
    0x40d048041100d00d541c0c500408030250018805008044504c00c80c500c10302c00403520030b034808942545e12500c507820b85961241c2d44c19094050756a5001012301030012103c0444c0c00904100030b0903008401403040c0506507030810018002a46003941c0c00702900c0700078501341c2da07560f281c1000c01701e1030322031065050040e84240c010f42d940748081083c000031104090b08400804c02641c0d0303582404016001070742d064503400042c00700550410800074510b203404581581d000382c0080c00000e10148081541c00d40340c0344011018030841c3c248420094100102e82e0003c0070b641c204402801414414501c401100256000008109a10352209807504855a02c1800541c1c095000c00c503143d42d0117200b6034010811350004150010582d521314404040051502008036175942d011418018402d078442c4201001400c001040e003042c0340d140c00903191007126076400c86d082c02c0e036940e03459001e449441d101e0841e4400d501c40c0315103507100450181a103020750741c04510900700c0703501c042200fa120303060080c0780c40 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 605434433 1250 605433183 605433187
    0x4080d09052b15060e0a02120f0106050a12140f04020a06020a0201021c0c080c030405040b18070f09180b03060601080103231606020a140f070603090501020904020f 72
    0x12040140d0380101c15000510a0b0b00000c04102400c00e001e14418403550140c00f9090302801d05025600510340c6030b110030300c04245c050902c001301c942030740285059100d881160310280c3d100b01101c0c0c2d44900c01e00c00c680024070100002410a0301c130303a001000c0b100b109400031903030100140b0040608007055407913000c01e2003490180021442d10600110080c60140098040ea00c03050f00049d4803144c000280055046000c04080c481c3d0303100341c032002e054ae43e02849098489902c082d0040c4d60350000d0264501403460551999101e01c5c0100c28841c6c5194641d1042d0780c15176416078200c910402031068042072056000740401e0522260b41080c001c1c5500d140000b4045540b28201480c103400980800d041c08a00d000600c0420303614000300b5004541d1401c8038a1490446030300d103180c03007a10501c03401c00021a01021500a5000c00c1e0020b00e98019401c124103080b0b110302158640303503690503c440a81c41400204003e07400f981104c1045409030000505000b07842c404102a40c0c481081c180c1c1c04440 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 605435683 1250 605434433 605434439
    0x501030305040e1506040b0903071a04050409170a11061509041401090816031803080702100c02040f1a030105091b010903060507020c090c03060d020f1309030f020d11031603020304080d09 82
    0x101b1100c00107050b0450bc050580c1c41d01034044205200e1801424012500c881161050141c82c40c082003c5040d998400c03940c40125102c010a65803106140072040d0140e0f102090032704800c41d043e0341c18100300416003400354503246d4a210070402c885946c18082c1d500c1c0c500d160017007400e840c040c20b60820303440b50050076105a841c000300300c543d81301000340b04550702c2c0c201440861504000d40d682b41e03506952440f5500010001038550b900b4071200207501906044030010b40c1030703c0d50402c1914022550074030643d078107082e041500f0388604076031507091540100d40703425188510021501d904035042c10f006080d140c4a072103020640d4803c44000002d44d100d00414641c80c00d02c070042e950700281004025013182018000030343c20344250140071344150340d040c003d206150755640100490b070707042c11010401c0175241d2030003401081d02c045038078000d030103442480f082690050090445030120000075510389540800d07218000c20750f01c1d03070940c114481808041500141000783c61100e500390344806100310310f = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 605436933 1250 605435683 605435689
    0x60405060f1306090c08041707052b03050c0a0215060604031401021801180b0714030c010e160305151e0c0d0c030b0607110f0d030503040204050601030501030305040e1506040b09 78
    0x2245e074400c5810010240204800701c0d1030b5202c5449000702e072951165991903141042d80c42c003040b0b11810742401c540c00b82442e40c4c1d03d51040d400b004001b4287c80a0000345d4611440031102d00680d02000b000da004400e07441d0000340352100451340314000402c010f05180e140d4481030400e54000c8000b00d6240c1d03000444409510a0045a20b0800000d10b0100d809004440782c900c151300041c411340c10003020215505c1c003085000340000d40c091a200c400c6a0300c0d084003020b8140033f8080108400c046d030040307410383c0c1c4070528504a8042540e41180c018400240d0b81d03036101c8003e42004015114423400045030142d602141003609014900910000d5150701d07280004000711a10040c0d01410f151502d0301002c001e889110942e141a60000c6003050401503140100328490007400d1035552125032454040f08144c0c010703002e14003590003a542044244d403a0320041d001c55001303010260102d48180400c01ca0b00081450302c560165810b90460581002d85000c82c3c00b0350884d03001841442c1000c04c0d050314500b = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 605438183 1250 605436933 605436941
    0x609090c03110a05030a060b04181a0c0f1b0c100807090503030315090403020705090a1d0a0302072c0403122904020a03060b0d02030105150f03060405060f130609 71
    0x798103c50350f01d85145860000f80d80c804000200601d0a51188884601341d620303a07008244070404944044100d091034a080c02c62030030703103c0e0800703178074034240e000300300c0c1809464240c500c186410172005240c00403912640040f42c0e11441b001d02244036070340e01080c3ca912a2004401e8244468981035101c0c10300301e00142c100c40058100038020740c0240104519108450505581c038101a03407190000e4485080880c00d140e8207400c0390b504510290240030094002d9032103c107510711240c00300c10f02404903440381e035210181540041c0c01a0b100e45c030180a891078460504501c2301d0b440c11700c011b4003119a200e44050080446066000c43e503114182080c03040300b40902c4020803008030216640a911014031809903c03100811401241d02241c4400c80324001c0c0d10003005070040d000441d07210b51282100c03001941c002d01a150040f07484d001200c2c407a90000e01a42e04202292401c40e00b5561a80c0a10004140c0100026841420420080065140c110b0f100f5818243e4a8000c04c80d03078103003040708041d1 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 605439433 1250 605438183 605438213
    0x21070221060609070807230712020c10031b1b1202030405040c020c10080c0705100522030509041802102f060f0702070503030d0e070609120b07030609090c03 69
    0x2000c940c0b03040040141c0d01074807d401e00608244020f0003180c1c014403410040c001d100c001004129402c4407000386580000c4c400c0d0700702030f046a40344000380101a045040d00c4100301115044440010212070084c000c1501802a00300c1340280310380d0b45801e446481240303060b04107450240e00009400d1180d41014082c07040e03824120b00003040040d1078000842c6034041c032070050000b08180000400c1e1030740720b00740403101c40c150007008503041c2100003034802c002000c0c10344405403240c0241d600c411100ca28810390a44554050b00d4880c1004940018040505140b4803441d94030f5424030105030040c2e1f100c490300c54203910750755500b031120b1004803081641410680380e802c0c50641c10a94012000c1d20000794280e03c40c00e44411014245c0380c140040c1e10706003442d04840e5141c00080b035540c030b03d001c00d9445401c0058100d07080311040d503900c11003034030840900d018504041060310842404a0740c0c1c540c141341c01c9a440d103400200d2694540700c1030211807030000c013214083c921401c10401d028454118800c9 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 605440683 1250 605439433 605439437
    0x16120b010605040e1303020f15160c0c0608040c03080d050403090906050f1504091107051b010807030b01020f01060906140402030c070f030306352107022106060907 72
    0x9003a01340f039181ea00402c0c0050142601c40030030100c0c002014070900c882c6110540310700460704508159202c20b94501001c5569480d441068062501c14030f1088071080b0485421050800c8194104402160000e1b80140147c6400103050030000c000340c608801401400007509002a02d820680fa00500c8010a90f10500419040c00030510059554480302c8416031021158550000c0407520010201e001c2c550042070309521344640100090010300c002c0188074454025103510141a00f080070707005030040f58940c00607955100040900d8003a60095640c140140125440c03944290101400c0d180d80e83c1240410713603201d050820007910800300c0d0b0503580c0411034041d41589002e4152000c1fa02036401c0c0501060311b20303072048040c94003aa00c04805020700354002d1900d0800350380d00039413600c03c920840b0b0f407021541c91503403039a40002c20b085400d031041e1845c030890360b5441c0c40380c8001900701840580e400b0f244607120301d1a40400118245805220314003034661843c4c06400c01c400c0400041050382 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 605441933 1250 605440683 605440687
    0x30702060a060302220e07091b020d1b021206011514070b0c0f070605070e0a091b03020a0212040323191509081c18150e16120b010605 59
    0x142d607102c0c61495840c0011105514103550071030f020002c0d00d06c3c1d0308145100d004d0f004022407800d1064000c807940d407640f1940d90702540105070040360313240444031104000442c2d224038a504040f88bc0c284824803400140a805600d070440c1c15a400c00b08280e0008200400303074003002608642108030550501c0060200d2410124161190312066800418440a0003000108401031544003001e550b24990414410805807501100c06007040389400d04480c45401181e80000c0c6005540c0910003040524000d8560f8034402080242c01a401002007101503005941054010f146550044d100035030044208403212a4045407040c1d08503000000d00501713030455060024505001d83c050030420303510142ca14401c02200700050010b20b1980f000030003070200003828400c0c0440b242c807550803d00c14043c0400c41c04e6030b4001c1031001c2000c0148010604103080c404003480548680c4400c214800c0f0105407400c01c448101d460b030204051342c1081c0102d420540d41d0340f06004100c0c100300e015140b2418054 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 605443183 1250 605441933 605441939
    0x30050610020f03040b160b13060609050411090c0c0d08042003120a1803150b030f0a0303020915071b140a090c0905130f050c0304020a0e090a0b0c030702060a06 70
    0x60f203a01c03650003006011072000684182502c9407004d0071940a030844200980c1e410041c030700103d071401e1000c05542450421201040c80480c1b0710a443c0220b920404501049a240c4180a044040248540501c01c07082c010944c0044003841019244010742c1d40380c40d003603c0d1901d81059400c210340d01d020404250300c103c00c0305e291400a084080048040755942e255a18404100c4a00768900310170000d034644898000100070351070a4404080a80b1b40080c4607079070312842416650745495051401c2a44035800140c0440c0c00f0f68000c0c034a44002802140910354484506500e40e840a2000c0710800480040420300d51100000c00b806000f09001c11342250702c140c400070b070b110a058000c030b0514680d103800c141c040c1400740070688005c00340600702c1c0284a490364805c4000b4407020102060300307401c01000605410a80302101d00c96a40100701003425410481c0b10180c50b040100441d0035442080c918002148100850500c50b44015240950340c2c41c01a200a09060f005040070078020b007403001c00c0c = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 605444433 1250 605443183 605443213
    0x9010b010c02120102190903050c0306041e110a03030f0f0801050a03031409101e480b0403270603050c0706020d0e19050c013005061002 60
    0x211405940448409a450110500603030092051105130b450501340d16106c1d051450f0440b94641c00c0f1b90041c0261040c0380d000805158480701e045a00503d100e80c1c028010041d00003070500b6800f42ca000d03030482e20301619160041040784c01d0760f820a40c0850641512580c2d0f00c2d41c001120b4064111500e440401c5500d803902280c8042100d000040500011300e103204c0e8207083e144143c0d4080d02d4000c200b69103c0c004070320054407846e00e400b286440c500a42c9041d40c480d43c0103426440c260078011075a0401d070403031000380364001189420907000c08005142c00e080484900200e141c000c1d405054000c035103080c41d180c090300310740c043c0b07100600e4004400741c0300360000035040a00c01102d00604001c01e8980d00c1454003056031003102001401b00b4804a510950364505030302035144035442400b21002c2074180354002c8140404210020525070240c0142822948500201c500c1e05540158516810000e12594400a1b1a00103500d8080d980e401c02c024040ca04223484400030055400a0b207000182080780c = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 605445683 1250 605444433 605444447
    0xf06051c0b060609090f01051005040b0f0a05070503030a060503060a0c0f27060201150503060c1c0902040f0f110a020d08060a17030409050606091804150501090209010809010b01 78
    0x301801541c4804002070194a400c82222072900000345492840d1a00035074417552808280210381c020390340610689240d0303005008440035107582c0c591395400c03ca09051428140d90041e03171000f007000703805d0001000044082000e140074181d42c140200c0c02d41d00304230606140800080103c0d0190b1b040502e040c4c07400c1e03004114482d404100785000d800e40c0040b02510b0400b0200c204000c6007400c1003100c0014555411b40c0205c00c0e2020464040c40c44039520410580d440c80141c0d0807484460f07041280b0328052690811005000c0b505010200d04516030740c00040c1202d5031b98580002c41500c40b1100f40d101030703e5120343c8034803400350784401d070402d8609a0300135a07502d461608403061103e03003800304240b581c1c0c51a4000c01400c0c02d90f004c0d0443c01d000c0c0c100315140d070014802c4203120b82c240b0011a40380d1038040d0650344a488041c00300030802d850041000003da80181c8260f40d03c00d40410303480310000d130714001c4501030202e46a002d40e8654510000600300c0200608a25260f45052800c04d0700341c0c0c0c0009 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 605446933 1250 605445683 605445739
    0x80309251d0a110309010c02010f0608060105010f120c20070b03010513060b0d06061103041a030a33170c0f1306080c0a05090708010b1b010e010f0605 66
    0x50160403540c2c1c0d192464009118800919250710b4010003000030398401500318005a0074907900910600c0b00075034102d02510203c0c0900c00c00c1d60040c0c001404954407500c2107401103001480d16000c120025a00d24045501a500803800112042444e1900b0121400710909600c200e00c0108001481e14003c40100e00060003600d121301d000d1a50710704d01880036001400548903a5900a5035600b524850000511a41c49040c2c003064401403860b40a030004002d6070100c40f10224061480c80158601440b10b5000030401055156103900d0741d82d2448000c090f0425003520000700f50b105d403e072a41000000c0d101c903404180c81d1541141040c4041c18042102d5221400590305040da01e80700d00002101da26085402c6080649000c100040d1014000f0b81d1103401101500c00f13041c40703a165014006140001c070303612000b140388a070041208541120080c071450144000140742015615180c500b55071401d02040d80ba41c0d140d20343c0d1031a040031441410020b020481d5998612005011110000a6070321 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 605448183 1250 605446933 605446979
    0x8010b0c010902190330080601030e0d0305040b0606070c090c05070f08040504110c1504150606170703090b28050915070305100b0d060308030925 64
    0x11030080100c29007500401d204903030051041400007510b05625000980034801507480110704ca41c0f03884a011000c11078454410555421460204501c10580b14540007401860401d40c0d5032003d05000441444200308804082e40c2c00b05003402e05050940a400014290030300c650070400c02600080c2c28807109808807030361107102052260810710252120b0088500140c419900c0f8887d0030108a001303001402a9281121b04000d5620100011070706030081079440700d41a0b02c1000c44129041c448828240c0c882c2c85680c03602205130081d40b52034255481c0e40e00080206001d0b1402d80c2440010950407a481200d514041080c1110782c0c0311201944000b40c10340015001041c00c1c2045c800c410209045031210682062102d0306006407010364030705043c80701c2161041090013095003d03129018403800b50003120360755400c05003031680c0c1d1095507028070000404240c0d600d1002002529404c00703140714088401c040d222890042400005007808120707524420b0024140900840708040300c4890314181d08 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 605449433 1250 605448183 605448187
    0xb01020d03150915170102070305090d0507181a0f150a050412080702100e0303030a180f06050103151506030902011205042009010323190b160e0108010b 67
    0x9000b0104000b0440c0c100300143c60500d9400c0040e1101c00b40c152046a900d00ca480040340c0090000320300300e00a0314001800518100401d2446d4a4981141d1900070b018005581c0d10a41d140300b0640c05020000300c1040d80782e1a8004d1281e0312024810700414030505482100c9002c50701400070300140200c3c0580f105451011907030f4501507204400390343c040c1070345030700b50a40202035080c01e07807254111107005c9100e4600d24200584042c4110a00600c0e83c001800179415900c480e8850005070440c042145042c110405500d4041034945c800a040365018100c002120350450511106822010552071011424a120200c900e2500c2043c00b088405074940001d00c06140d00c0107e0b002070500207000d007180d0520301880140101c0000f480d001004e22092000c00a81d90300600800070801d1002034652920030a82c614441c402c2045002c00d10b20020075907031051400d0f8503400c22062a0340c3c05440401e0790030100145a5569900c3c000d00194504001c2040c146c41c100080880f141402280000400 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 605450683 1250 605449433 605449451
    0x1090812040507081609060b0c0703171e03090f0313032409031d040c02120d02071b03020411030411150c010c05190801061d06120c1c0b01020d03 64
    0x10a2110364094010013003510703156182c82c3c4a451184031a07001c1c6240c524901500080c881c00c0040848074654000c10290020b40d1468407448a0010280c500303429002c0304020014411480c1281c280032a038506c003000c0d40724240780c620145013a4a410040015600402000041c04042d2041c07000302d0fa4884811002e540704016001e461400c0e01c0001b180700c03400e101c0483c041540003458440c000004541201005186808000981c0d904501500141c1c200c0c103015806074040000810200c42d8901c0e000d40360400c10f030b50310110f00129402070f00228030010030038003c600d0a80208088444100001c078118101512001c0d214122075480520407201200d402d0040c600502c2583e032206c50900c02088503051030840600154000d09107002459031b8183c910964a015101c0a07051701c00541d10020360004006424101c400c00840035940000103102100c8143d1208000310300c42c074542401907864501c00040348641c04403036001c410301541401e5807406140d900240c0312000220780e1a000c96400d00c = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 605451933 1250 605450683 605450693
    0x2070c1202031c0302030a0c0207120605180d0503341215140307050a060203090d150c030915060803090d0c0323060109061406090118060905120109081204 68
    0x80014180c000b000c1c2d24031040f1481d9426a01541c860b1084c0102407260702c5044904985840c118001c03004521004400c11300411219440182c6c4102c466a020b014901c111004603e040710000803c00041e41c00800c10016030410840d0000c491940f41c81402105047c06804d0b509480301c8000c00100845100023840305a0103412200c3c83c01c0c045c01242038115220748801200590700803145002e8811000005400e0501441180032130341a90702444c10400b8840402130342e07848003102994040410b072608944026644610304a5903007070745000a844480380b400b000d40400e514135000846190032410404150040700701d0f0410481228000c1095046280c41c4d898040c40c0d03000540091f04d10038618030511040100628100c0d0003808480d01681c1e28441c413010740303d190180c0e41a03040c800b0518107090410f4005454000d005042c01105400342c2c0340d100f00f0024156108000040c0c5540e400c000c0c03070800100c503d00851010b0000e20016416031a203201520a00300c00c0c07440e91314000c0000e02404 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 605453183 1250 605451933 605451943
    0xf03091509040e06010510020f061b0f0c030307031d060114060409050c03072d142812060b0412050c0d0516090e0c090a020c07180b030102070c120203 66
    0x85002041040422580d040c20f0756581824001c075400303244248000340200e400020402d1641401c64020301465a44180e41e02180c5c680041402d41c418062200e031001514407409030400c1241c0900450b140e20780710800034156250880400d0651100724081d451420000c120b01703055850484440c000c0300442e10114027030b8895a442140120b240800340007150304280e000358080d07542650303041d1900c4040040598140045041d841c07a41300c482420500b5240143d01540c9490016004541481600c0f0b001e0124003045510340404110003000481c0043e1308055404040c807980340701002028200540b10540e031145000e070020340c81d00b840310401000000c001c9090400405403010f501c2c451a491300340d554405801c41410251251a004254080b403031081c031580f042d1500040006440e18418010039050145c5891103264082000c00c005582c1000400003c0460340346134801800020001021108001d46541c071a9004020ba44003290b8441051015550740f49043c1d642990203100280c80c0c5 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 605454433 1250 605453183 605453197
    0x140a0b07020622030206150a150206011418130501180302010b0907050a020706030b061b0d170f0408070c03061109011101060609051005190909140f07030c02150f180f030915 76
    0x27100c1d1000341001c0d5012030018100c07030000328014111480c0004020841c40404900301c0d22041050004080c02c50824071805040d02510000031100c403031600700c03001001001810307030160b0746590130070000b82851046151302c10302c2d42c0381c00380c20f01024020089d1504801d2284404264440c041450b0559510b411680c440500703061042c5008400b41401da10380b00f16884140215075412900c503015601541c1c4584140b04446110321107654543d0362140316040034500f0755800090420101c0014924824603400d40041070010362100e803120b00040c01c070584416420804c1e410200300300600c13a080a02041038a40844180700c0c14628884100c68a01520250744001c10306d00146001d0b49400265203001e03501d0b00d07442800295000d4603d28060325082e2190307070f9400c2c000c9001407021032180d071242d6521910340c03050700e04505d604904150000c60544554008030f108005220340c140103468138491001440c0081d04045c2e000c410900e13100c2c0200c23020b141c0544034800c404030130034048104582035 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 605455683 1250 605454433 605454449
    0x30a03050301053c090907030c450b0d26130b0301050f030d140904110408060604060e010b190e0d03020106030b070203090607140a0b07020622030206150a 68
    0x4038201c42d40c11342c0c3c0b40050658820340500309020104415500118101e01601e812180c90200580b400200360205e0b200d40e40d180841c4580292603030085c03900d02403180030000c41118000b900450340300f01c0704115000d880c1003e00c9901120200800a40c0b6100900840001901740c102280c0b091100303c4041e1060301f010b2544d0788014017000c034080d0320410256040c0e03107080c2c482a1985003a0401d041d0b42c1c1204290300000b15441701e0a0701111011380c00103009118018001081e000b21301e10079103160350060b420904294001070200007250a01d44644002050051601301c1d0952618002042074440c1080e19841c4020f6050540802030003440a492103030000342451b2506481e40c10020300074070141c0801c90748201e42d5004100418400030544100c120020b24542c85c00c070065407414119012919808298050071201d1404603a81e458030074801d9001d43c02800301440c01c2e50004085444180c0d1840c8800d034001c10110200b0750015801d07610100308043c880150140500060f55011036602c00c100d = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 605456933 1250 605455683 605455759
    0x120903121b150916030302030d0b120a05031b031306030f14090f07090203071d0310141f0e0619052d0303030610080403170a0c0806030a0305030105 65
    0x10600542d4030024420048034040e904242c110710740d07002c150522488041c1c0103078414417890000306026482040e001800411001c280c50341c00c030b07155087c8484003038240d6480d04040342c100c1d69002e44080e20200f40e445440590300e000703c50040c040002d08280507070010951341c0e00041040d03001581c044d2a000030b0040c9017501d03600d0005e8031282e8030702c10f0b00e200c180280245d500c00070380c803000c0380240e81c0140f0240e00da00f0010710310701c1e070402d4a0070211008168140301c0ca80400142c200d02e0301c180c2403040c001510030940c6140c40d12500b10805c451620720311401c4402001042664603441c00e03541c122600302e840c0069000d001116040c02e480d2608a1544800f14001c410940060307004c800d00c01c8400c1024148214407440c0406480b030104071042078102140c603466868803440b54034116031080c03003800d1950038410000c6054441d503000326028503259546407400c0e9415074002040d964080412401000107901035500100f95000621805000c0c000d10040601c071300001860300030000020300c1580c0 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 605458183 1250 605456933 605456953
    0xb03282019090c2c0103060b031302031b0105030c091906020c03070609140d150501090f050a02070f0b060d02060d09030e0904080f09012a05120903121b 67
    0x204080c1840c0300700307a00140341c00c840800290207120580d210040079100803d8410070003c1003084159221340c910b040542e15040407840320b1810024501035400003400d064500060b00c1810310f0415007140c00c4c2d5509081074038a9800381c0c0d1110440354405640000c654403203074140301051200180e034042211150f0741d9200482c2d2a94002110101c0081c01c0702103c0c103640d510841039604110901906951020401020745507041410f00c4054180c410b40303001000104400c1d00500f210401c2c0c00030380741d02d40c40d02e900d050001c1c268000d494201c0e0888600310329145c110341c4c0f15581400c89041c01044503a000c4001801d81c0e84c0c40260607082e0785c0207404550344404000e500f0b80200702c1c404088000c47c074844220100e90510400c07403846150b204504601d407a5414a000120b5002115401c0c100305c601410541e40f0142e482c41001307401e02036402e202c2015002d2800505010703841d05088000c1c035060000d511a503078002416414035020103d025551070390045464000b8810407082c15951260b02150 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 605459433 1250 605458183 605458219
    0x1020d2d0c05060702100623060c03070f03090305011d190c0504140906010e090d080a09080a08042a170a06020f0d1b0503040308060f130b032820 64
    0xe5648901c5c40d61017002090745500c040300c0240365009520740b000b04005235682003828914010700c00480900100d0b410100960303a40c180c1030011740c20071030004000c01300030000c0007424024241c0148102d0b0054440c1803910218550303961070b1030800100030340c04001d01014000358070001c201500c1701510501c0344000702564901d0442003942c28452611a100c0001040505074550340d00134000540030740800503201000b100c0046019148030209944c2d4151000022031400c010206000592560940761074503081001940e0403034910503d6083c08a04000c0162420080b4401900c03245d20009180300006800d181c034065038040000c00c8588002400810401030101501160301c1c1ca0000f07001e04030340141d6030072440c1103001410010540030f101140010740900142e81d4050000780401060650307042c001010008400b40c000980e40e66607081c04010708013844103080f1088120021400b240070158a81400340302148060541c03401c51403c2c0c2d0a50f0301071507180001e240c000b80f041d00683c00350000 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 605460683 1250 605459433 605459443
    0x13080408010b030c030d050307050f04150e040c0201090809010513080f0102070b0709140d050102120a2705101107050109030504060e0d02090103032307050c01020d2d0c05060702 78
    0x6510030710510303184401d075103170000d503400300c0c03d03600e0351a2825074507050800e03105500001481825280240408030f4039081400003011a80240e5030faa25480000c00180001c54283c14000421a41170207910404551210116014200d003880c00340e40d18400458080c1c4030303080a8000030010f000c1c0b0b00c140f14010b0015005050114000c0390b42003c070380c4a07a00b040e1032a070600d11883c01c03500035070854428946000c4500c0b881386409440090b190281c100c0c401a0b44c0c24007110a0140e07903941c0e64490000301010b00000780040405120311a142c3c00b00d0315440ea40d0b03103400c4520b195417074451100600d03040d000415182065400802445540c0c42032401402a070840e0181031300080d4107001c041c07100d1400102a01f01507402801002c0d50b0b90964500b224551000c0e4501e040b000c1410301e814490f4050306000304112b0340a00c01a00c42c2e4040715000a0030101c890b5603100030050303401102c0811303403480074595841d51058850250b1050603108203641c03140e00007101402902031070007001022600414 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 605461933 1250 605460683 605460701
    0x4090f02071214070c24020316060906060302060706050a0501050102010209010c06020a0c0b0703091e21140f03040b0c0307120b0102070b0301081f02130b031003081c050702060105010c02091308040801 88
    0x70300c3c4c188050b1b65030300072656030045003035100a0540540c0c094002c1260769004e018828000c0d0004503160b61030b5004922a90301c401801c46c0c049980d0810003460031450b10545025100c00d100079840e1580e0b2900003040215040c0c4050a615800114041a50700031941c1d0040d26501c042c7c0e055a6251104001d00208500c220580f140c4e01c0211040f080008201108500f80d6807082046446020404070400343e200c45d54200018085502961320820104a0140c11241004c4440310368a00e0302d880e10094808015004080b60307503040c028071642d6070f0040c4410b0035011546000142400c240c0e40102e00e032101c1c0781e004040001c000000820310f5070000c15981088085038218010208040c00700342d0403403065071a010914050743e48288021114a0011074210703040842d0f4200480e00c0391204040c660114002414110201e11912110046030095070791140c014000303040c05601d8100041d0001d000540000e1203000b28200003064944440038840e101500015000c1e10f80d503c0f401c4c964001e041e554 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 605463183 1250 605461933 605461979
    0xe1b04240b0d0605040c0f0513050604180609050c0403080c0111030a0507020105060a0305031e190309050706080f0402040c170a0e0c030610050105030601120e0304090f02071214070c 80
    0x882d13581050b014000881d0001c0d5114080714034903000481c2c0a401c10499010802c0e1a20300000e00340c0c0da00009400900380d503012502d519031102811004460141c0d102524003410441000001251541507400f01c98000341c081d41d03035140400d041d5005040a490403d4401408401e109042015500c11881021190020002521544104100005140300084c100d80c01000407031b182040c0001107400c608032240c041410140500342c018030074a8003100010019684084c86802c1c41005c0040350004c0c101401c11840c142040405a00c3c142001000070340102e44681d081c1248a10841c4c40b0300c012650705400a0250400441007405403c030f601c0302c043c045c030504000c8101880c0c0031460500070745501c0d04c09c5800501d0030005403003e4100401c12414441840c3d003c41c0120054007881e0400c00e021809190349130704003d10360b02140e85a20860b01070394070610040c00051400c0d208100c0e074a00e0783c10310b42a10300c00161100b01900c10300c1d10082c820a00c001002808200c0c16034001c031403810039 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 605464433 1250 605463183 605463191
    0x1c0c0507120219060b150d090c060f0509010302070c0902160212150a0e0c060309210c06060d06060f0906090c02060423120c0a060e1b04240b0d 63
    0x1068040fa034600d03100080901c40c02e01e6030550f400064866000c0d4140c420f0207090701950b240850034201c0c440c3c0200310284090b07078a480d005001c010710081804003a00560604600300407000320002e0660059680160606900003010001d125039a0038840013041120400d540c1c401700c1842108400303000d220102d0041604449480342905c01007403c00106030590503901783c41d42c0b8215040094065824403c0050041d4201450507844600045200e03d0003000103010410408003110b140c2e071080108a503520606010a042d000c80120f0200d03084102103d204071512014145440109901e600c040801c1c3d407940b5001602480580019003242d00d8034504020420034110306907200c82049400800c1c0c80c42c840501026072401406501c030643d4180121001550144032410655000da145550342e035002901110410100707004003002c0000c03640150031501040c01c01a034a0030070360001c0300e1055450300d50013400700f13400c8841c040740c03c90601032095034145e4458160216501103044580031900f0 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 605465683 1250 605464433 605464463
    0x7050d030e0405010b0a0e19050904030504060e0102120403060b0a211b050907050a140a0905030f0d05030a09020d050a0303060f0909020d0206090607050106030506090709201c0c0507 80
    0x8445c25181c20001d02c1e150ba0300d0505a02c0c0c1005003209410302c81ca6052003502d900441c15845e5130882501c56840303626034503901c07420000c0280c0380c0f841800c451411588200140c20300c4014020035039045983c0104080341403080000003031045000b0b0b401000081d8800b50720030000c040d922440e00c039810700500d100b082c8015072205090390501d9601850382c0003e903500c08617020764030072401861000c01c2490250b90950003103207040180cbd4000c401d480b000030729084040c001c0349402c0c4940341e030802d08030008051228602802502a00000300000f0300c90f81d0704e40340501592100102c0c2d90000c3da020081d508061030790701c0e000d8001c160900a00400700310040340482c00698034070801c88a2500141241d800381855820010b0980c80f403a56241c1151090000c540014401d0140c000503500c40d20142c4040d1030046c02c0d031403a003075041c0c0c800940c050031f0403040800810f12f41d1448240c10084016a6901c000b04001c000d59100603007841e141803403800100703c03240350340718006c1d02c074251148084030446a0 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 605466933 1250 605465683 605465699
    0x403200303311713080a061b0f030506060c060a051b0a020a06020306060c0105040f05011b0e1003060e070807020d0f4e0b0910150207050d030e040501 66
    0x245200d6810050b002180202c40400c50036100030000c003202944140c0f4100f1100c001a040034025031182c0860744c007420130b85080080038011a211001611140d01d01e405030b00000404c0b84c03014244403001c7c150f851004c268587c80743c10407214a031100c0c000301d0f082414044c002d503000700303801c554911241e180c0001303503030b00000070b181243c000c0c200c540c0c020b00c01c06401c1d031104002944040e0440e50700c91410031000c0980a000e02449210364055110790030788580f01d0400500f5074100c14100000c003496124071034034040d000311025a02503402c0d103000014006a440c1070b001026240c0210038082c2c1c4c44c0c000c0041a6a110480601c14040e035401d8a0196007007140654844115042180108440d1034a1078640418004203204040080400140d044420921b051030f000c441c3d03111821403c015451440030f4880d030300582c40100c1c0305991041c1076103400d0303100c81074070009400b03109507105440f0003140e41c452082011402600d001440410351050381c1c81c024010803003040e84580994202400028020707 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 605468183 1250 605466933 605466991
    0x1e021e030c0f0a560109050c07061a0603090a1704030809060307031103070203040f08030301030803130c091a1002010608250b040603050103260702090403200303 71
    0x19600418080000c0c018815250480001d0180c9009242c0344e2040c140003407401c0000400b10720341845140320000801c4039110700130001600180d840600308000e0121301c65102c0c04403065035411080024101e6010b113034010219540036400d41d4071240c0442886407044000c5105141a446049280b00310424141050b00e0b50140703110113402040144110380749410005c00075a0320032914500055514078078908030300c00e0f40041c3c680303100590010506203c60319041c880750001e800007000441c00d40d031456031000322601c4010940c121100340740041d5400c200398181444090080d542081c00b8400c07045060481c9010401c601600c1500c03a0b01101c0e00f1075006205140a41d100d44000d04016060f40030346110306400648036000c2052118000174440166101500c042c000300d580c0410729500d14100b1445010302e2210310030f107011590710010340c460612400c4488465040e1040007440e61030f81020b842c2c0110111140d51980e01a01e59086021400300055200b61a280000d0b14892100100c0358401 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 605469433 1250 605468183 605468203
    0x7240b0108040f0809030d0914031504080702060c0607050703080a0209092d010e090d020d080f13050f0606031606090506070c0f061d010309031e021e030c0f 69
    0x208403200c0128020660080c1c10503c440e00441e24240761190b4200407038079001e4484804400695402014064420151100319008000302c00800c0484078802e1484524000604001c080d2040041e4513030440d1104010359400c55040c0d404e5603070f5850040c030003070625448020110006140600024101000c038420740d192200041d00032901c0e5034440d80b0a20000181c8080000d4919502503030310351100c11807500310302a200d01c0f4a510a2410402211843d1941603121001950070a030780c142205a40100245e611030300038000450f15032100d48608a4008039482c002d03040c0d01540c1c52046000d600000c06a00982d0194102c401c0310315106d1076540425020b000d07403000140d03454010085032a04101607c5960302541e040c0305007d13a506070100550200360b10030b001048062006840d0101000c010b14010300302070070306001700c01c80b554004048e541e141c03180032540100e6115143ca0342c2d10070032007610b5140b076920601920b5512010345666030b80200c409200144104140140303d803a01089034008 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 605470683 1250 605469433 605469437
    0x507030203010e040b090c04020703090e060312120403030b04020406020c0111030a0c111f090602060f06010909090c1e03060605062b0b0a06120b01081005010507020609040207240b01 80
    0x22a00d50799141c0f0b40c24040600f0701151b0f407003038540141ca1a901c0348000c02c00244242c0360034070080d02d8203a008820820040204e88030760011040ca07882ca0030030f4001c131161119000300792440d48c0e0741e515041d0005d004091200c0d40003440400c000c65415000125112182c0e0243c0710504000c4114501c0342d640c3c03007101c040700c0005404035103860014a9046010004440003405410850800021f140850001e41c03844000204005020490150140070300d81e00810300c0c0070760003081d25000002910000f110700c9108441030303995085405000004d1030780030142800c0700c020310341f001442000c15a0100103001c01d48400d07140c00c100107038900e48102100c880c9080c2c100700504d010041000f0340007101c10609410046501ca950844c1d15036a4140f880c8090052604d0308810100554061012a40e441c4c100c0f0703050240300400c3c031014102082c007410446d002407902c070b5500c881a101044407405110200b540060004c9207690070424150b0911101b00d81d00380300b06149656410190055030800303c04c01f80 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 605471933 1250 605470683 605470709
    0x3061e0f0e070504091a040b0f0c03010302090c0309011b02011b0801080604060203060d140115120312021806030c04090e0d05071104020705030d1b0903080d0f0902030f070801050703020301 83
    0xf0032810142c105c240c040f40900828403c4680ca440410100c080480d02200c1c1d50950b03c04004081c100329512580091620502c1c600710342c19640403441d4010050b14131044090040005044e80c002504644407581e420152920303080c911070000ba0192141c0c071030b805d40101c0c01d00c04100b0b03240d20410302c80d8102d0754100c00802c0c598a803622290004e51015040e03a41006103042c00101280e0842400d0403415291000050b220401000303e03a241c2d02d55030480f880d85100b404050012a5100c80d140c4031502c03100b500141d03514110400071400031442014503030001c001004005100841c000500b0884104e141d0074420241c1280016848145440c44500401e00c28443e04001c9020300e20780000002d4082e100501c1d054050b1502071860700700c03162402000b41c8811a80f1074141e40d483c01c91151552030709005410790b08540cac522807507000c0d0800c1c080800c0e5403007000c03040340c0c0c01507040142826000f40036981d910600b20506502c40300c142c084d1411560901c000f02d40e199210380700b103d040f600c424070611 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 605473183 1250 605471933 605471939
    0x10b18040b011701030510050a020315150d060602070e0a14010603090804050d060b1201110f071a0103140607090f090c03060e010b0928120c03061e0f0e07 68
    0x48014041c1061840c104102c0c807400c0010040e0304580140a540100300420704501400001000d48000900345400580140280f03c07084400b000c0103681908112403901307192088ca5002d83c0d442c041d0100c600c0b0602d080050026072950040b07403140595a10003044001a940e02080c0d20903600100c241c0b42580b210f00c001000802e200360b014824062144125524142e40c800000e50040b03251760050b24126551400d111462a103a03480c8007038064034100a0200f800c038501e028070342d8010400142c2c0c14410014840041189117041c550400f911b4007102d143c1540c490400602102080081c18454031035440841c402c580a800840304640e50b05440b00d81d064106450351001d0002c60202c0d40074103484d82804144042c2c070840303150180100c1041030751156902c004000c9002802c0c41082c401110206003020701c2c0060354002030548603c2010b0410400f00c51400314404c00c125031025140c0c900d001c0d80e0321030041503900220601601110140945405988184102c2d80341c034486101c1c0b544030410030 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 605474433 1250 605473183 605473189
    0x181309061b020d11010f05012c06032e0507021c1103031819110a14061803031606050f0708070206040605220605061005070f0605180102070c0806010b18 67
    0x213551445807a0000300d0038016002501c820342d9400e07003110091280b202c003640182e12001c111030101c0c0c004c5000f440c07014108840070035141c04540c800346181d2240a014141c00780c0180030403054211b44000d08000d6454240c0d4002e450740e1031402182a44820280d10150040c440c201d422030703120402010710701d1515543d90448044042c00c041d40220f00404589601e151908000410a18082c0d500d141701c08130000708001011910360081c00f009450300d50700011710303154001603803485002203411804446003d0006440e6010f09003030b00c0c240e8000010881e0401c009034111a0083d410607509005641b0b85c03140c152000003084172208010780c4404005400b091050300000d80003018041c6c0c0094100d201c080112407042ca0b40340c2039801c80c0d102c50910003103003001c0c0c00203c100c075a6490114105005030740da200110000b03e03000b40c51942c60340049032540504464007403091840c0b6000b15a12845450302075544d180502c1401c0650140700e000280b01d0380800121100524021040200300c46a1010 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 605475683 1250 605474433 605474447
    0x503010b0a0c0b04050a0b2838040c03060e15211e06100e06040b1809010b0306060117090304080a240209060a05181309061b020d 57
    0x50010088002c0001c0003081450040c40d025038001d1000c1c2c4000c80d80790901e0700f42080050b011380d002c44841455071811034801c40f00388040c842e00304c1d00401d05903240c00001400e00b5503c903101e403240f01500241031004010020b0340b03040e07800035a02888040312218041c0c084805500c141e03202c0000340d8000a4801c00078031600100d031500102086583c0d4008110000030040300d003d14035141e03010381c140c0c030000e00b108800c6c052000e805100401c0240f80010440070b51180e01c3c40f40d8070840300cbc600f0101d04a9580d941181080c4a0085c0c05090ba807640c4d033036280f8408005542ca0001c651030580c61046904000c15158422201a19500710388842002c1c1880e100600408120780c501052001003940c2c0d6050042c03002c2a401482c00d10908200b0780e02c4e9401032403001e500c1041c51781c4100071035503a0392240340960342008102d080880d01c1d071030076a00d2040c01c01110315406901c5200c800000010540355400180311900946040100c6a13000002c05294092500c00e03101590001c65140651403007582 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 605476933 1250 605475683 605475697
    0x70905040207170d02120f0103030c03050705010b220e120418090f0b040209090712060515030d0f0e090906010e09100608010614010f08070e01020a08030c12010509070503010b 77
    0x604592543c01a900004041e00205429103840e07400160181102000c03202094220304c05196170ba08551459801509110300008024144000420300b8000e0000a51060720030160290001c00a082860031190b030b040a00c03400c6241a40c9041030300c500d40d030300c00500138034444002c000d0345203840e0500c1e1003250200c03114012008803c1d1107802c0800021500c0006040d12407007803c1c000841c1c1410300c104030086c0d2008040d415194481082004103154031864030507003d8010000140c9522002a100ca80124841c2c6158052203051102c1000660010008008400c80d645140d00c00415004014142109650380300c0140e012200600c00c145007110b201d5040300600c4122001150031089900645215910010890b592100c0030006070302c400c8518031028a00b4a00b408111030070030030252800702c010b04054200310031907219007001d034020058244c4003900306001545900c0d00a41081c810b5110211200000c0400000080d060034407442139800b420407270b02c2e000e003981e0034081c4002c03060300025 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 605478183 1250 605476933 605476943
    0xf0b0108040213062c0105010c0506131a0709030b0c090a0320121b0f240d0f020c01110405010c080a05040f06121103090a23060708010f0e070905040207 67
    0x2200000e02070b003c50071a91440b07152603682002000020300c80001111705031312190501ca011071200b03000610224207194084041c24000b11124054146200700744000a401c1407224104414082c070107404c822214110b910854411000d07903a01001141a401000341c4c0d02d80000c22148e050000400c40000703401c41c403002c0c4243c1c80d4200455000290700140603254a16a50401d1305020005902d032100a54041c5040c0c0d900841240580301040010a0102d000c0d01500301e00c1d003200329024403034400c035014024103410500081348417003c4d40d070007075101c01010140d41d807030700200f40203102400c0280e0f400c5900503140d0340c0076010140c40d0807031543d10849130042013110410001c10710002030b201401c060002d55582d14980000c9044440407207800d03868031215044240708000c0c1024001500049099200c2d40355803001890741640100340900c10501e60075806108100040b455002031454101c5016440c14407030799a450700c601c0041d19094451000280d0f0400c414411810140c008100051040c = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 605479433 1250 605478183 605478191
    0x809071e05130f0c050c0c04060b07152c0114100b0a050f0d0203011503110405120a080415140711041107020a030501020417070e010e070207030b010e0601030f0b0108040213 76
    0x1480a010454440745100e60200310041b4680c803084004110010254106560800402c2d0404070307004264000c0304001800c0c6680c10003801851030b200c1e000130028400340e04501111150210503000d0300c40d103402e00e4089079840e03c6070084650711031460090044074440483c61144c3c2c1440a0781100d54003881000c0c0030b20000b042410400c65400c4014501030308804401622541414040381000801d80c0c03800c010103061400c0521070008010031941128022100c400781d4a00d0481a20300f451031208024000900c007280016210160b090804a00907582c6e8402007110003007101030340b203401000800780c807164507811030040c0ea0500c1d520031000103d40681c4141040c4403070380007072542c00c0240c0085403142d4000c00d0820002446400da039000c410100b02902145044c40c40034407103030b801440380101181c0b00d540802d990500034080d000c00b540c0c000480b43c803d580c542c5851144903105485d081d0010f854201403a211210500c87c102c044c50b816520201e02d5141c80d02081442118400da0a00b50344d62 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 605480683 1250 605479433 605479451
    0x4050603070b04090515030f0c06130f0e06010801050108040b1314030a0201060602300304060b030f150709140904230106170307230316030809071e0513 67
    0x21807003e4002024105004200340c40d0000d02c0c0b0b2075540740e80c4a240d0080d400030840e0000204e000c14400300ca118151130158680750a6200b595408500340e005043e10b0340768103000314183c2421084544144020780f21080182d0fa1040112202c030000c840180c03c1096002c04961300c7c50b19030040c0852140115240c3d800c411810850900311f6108944200240c0e41d034a5003008940d40501a000d000300625200408550b10342c0c50807001034842542c42030305140000006010030000c5d50103a10340003001b400712071428a1142c40c0310b0751024400e1940060003105400941e600340703e03290711000c0c1d5011489907000d84e02c03007006100e000c420180c011111005007200341740315807281c075208001c44003c5c03600101c2d209252454400c85411a40c00c800110380041014402040d04980301c1101c8540311381080c007a10300e00c01d0165065024030031821410841c0013028800b0b06900c0312180307026049440540740c3d4240c0c0c4000f102c0f02000100c80740b14020365601c030b040010785070041c00c1c0c041c000c070030781d10118250f0b503 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 605481933 1250 605480683 605480699
    0x314070807120509011103090d170c072c01030c150309050105130b010803030906010e18010504030806010305060d05100b01030b04060803120f28020909040309090f05150405060307 79
    0x240451048006400812080942d41e40940100100c0401b800594a4014030401040f00d40304003041c007800780c0002d5000c0601900c500e8080f0703000558241d0a070341e422611408581c030130f40103101c0240c3c552990780b03070709124030145000c010b8100e03640600000d04507442c18882c18a160074510b24802031598407060340c40407070f4081c040c1ba88103550407107022051160526044812505c1a040341e08564010300400a100c20001140e40c19145050120141c0740d0b47c0c10820407110100c401413250a5080c5020b001c10941c029488900804003628140066a00d15041c000d43c0400713024080d1450344610003203403102c0702507130001d18141e40614012030400d0940c402304007565041e034000e131410361001401c000c0711140c0c001a16044421541401000d003010307030140e81801043c01001e504044803540c1c110621420b54100c130410000a000c03a080c0e880d06d800d001d0b28041d070a00c242200d0f503050004040c00205548600c6100c0c114012609a0001c0080207100050200a00b003a4243c410303140c01042c0301c0d03 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 605483183 1250 605481933 605481953
    0x703060503150a0f0e1c031503110a0b07051501061e18050a0e04120c050607050d2d0c09030201020a0b040c05090103050f070f0815150d06020702030d0c0314070807 72
    0x50107540040406c403d10740d074042c844611008840e801c15241c072856007160b11101240c0011650095507032030280f40da91001410300c054a034846d41c40224000388000030450301281c10110025030640500071a80d954109076515424248881d91001c050700e503458215018000302040712500d4a0040ca00c0c0f521040844c0700180700d17420181801d030000d0208400c011103140c54200411251a100401119960f0340c240c0c2d5070805802d01083c0940468420112203440c2d0080b02c00c0c407001c0100d44140c401c0e0040c0c40b202c0c0058200c0030351965003031441d6102a075029000d0501100c0c2c2c103900a0940e48040e445403500c0c0031018008951180c00804002000e40d10810344a02941c02900901810313800c4404141c60f0080640c80101c03c0c4000510410107903501146241400d03486221444095a60415895010a81c041031030341c0010790642c440103000e29603002d821003500c264110b40040124410503258210304c00b0008000614240f9a0380307099203017030041c1c00310300c2c4100041c5080a00b582c1e1520009 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 605484433 1250 605483183 605483201
    0x70203040f0e0a061d011401020a0c1401080702061b03060a0510181202010f0f11010c18091104061d0a090515090f0703020705150109050f0703060503150a0f 69
    0x10000024003104a03c00c0c442e0750000c040c00c0c030030207243d0001800d00c050383c0c050501c640f0303403003660101a0040e107900a1101118013944070014a00c841d80320380c004902c0c00803a001c0c450018182d4400549107500009000f4000c0101860318110744034201071440c42c5510040c50950042a120b90005090715181085245440603071940c6490400c0126548812402a0301000311020383c00702440151760440d20078003075400d162030a42447c00c0428401d880301410349401d0400e0350701e0400c0c0f1148055010f0440307c460302607011010821a5500b40c0402554030302405880100420002003108034068030600c01c03c3c3c014501342101144d420000260440c0c40340d88154049512002042840003c0501c210100c8400300c8903018141080e014045850b2002030911003403650024074074007440420045519090340d1400d4801b03d079a194900301024003416140312441e00050301c046400d59000740180c00a03140041c00410042003a240705c20030100000d450045116525859090500c000d4000d00f550 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 605485683 1250 605484433 605484449
    0x26060a0e100b1c08190504031703180d050414040506101112040f1d070207060e030705031e1c120f110d090c06030b06070b04020604080f0c010311041d070203040f 71
    0x2103040340917502c17004000d0b14505038204001000280000b6403040c1000c070000c550741d40c02d43e8482d590b29103a0098240c4520400b9064030406c40300b101226072080084c004e0f181c145240103010a030300002e000998105440c05a4002c908080d002e15440c820340c1001158030240084441c1100c22803603c141035030003038200c1100183c00640601030254002005500f00181304420a102c1c13410302d0001751114468000c3c0307420446540e894101230350742003040c103014001c001c00f9584242d0b0410a00701203260850304291281c09a61500200b0508a1807015222230040c0c4070400794001c1840d80d8001050189141e19940ea83c651048403e046410054201c01170202d0001420444609014082041c03070340c030210406090030026841d6481c0c010640e4401540954642000e40761440005e0440c0035680042440c1d100d20b4070f0715000c41a001941000d841e03401e8a040118003a140795940661141d405910030544039801003105100d1a5007916a02c0340652043c1e03401c1507241c00c0c20080300d000c0c0b42e1207280 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 605486933 1250 605485683 605485687
    0x1051605010504023f0c06180f031614030717030a02150907060c08040503030f2101050f01050c0a080a02160f080a02010809010626060a0e100b1c08 65
    0x114100380c40308015003200085e800684840c6815010088807000c050049000c0e2014181220001d0800c07101c9107110000740820748868103800640d101c6032050481d580314040001890019084c0803c9400d0745030250700700e1000d10f40c1403079210f40741039084040041d0107200b00c010000c0d405c8150785462050130042c03405103542c1c510f0300e800285042851030125400051300310074421605000a4440d0444909003810218101941000d90860196902c40350f00b5000c00144014440c214a00500307030f0200801c02210700e45509110321080703201c00d001e41c03500401a03006a410b070f5805030380580256400c105c1110401c00c4180d40300e01842d0805e900640140c0d00c0040164016000c504400c030284c0403100400c002c0514001000e40d5030301150034080d0500005134003181d801c0d0390030341010018015039099480e800400f81d01300100c1c0c1501609640842c000c40020440042c46030069682050001005004089030480000001d11026048640c4403039032040402d103000c8170b03807050281d10340250400c44d = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 605488183 1250 605486933 605486941
    0xa061b0b01090902031005010f1a0708030117120307080a09140106090c0908010b0307030f1b0807171b09070c061802011b0b0c1317070906090204030c030f02010516050105 75
    0x1071406c05500381d0404864144001484022240034001040740c1068001c0c2c001d5014100c60410144201100685103040000010507007004284410b100b102ca00d81c00c881d00c442c941890b241040c00203445110005001c203000c0b4001841c0d41d01300901c094001c4e1070b85550540701c10305c80350845459512114109031524a0186425000501c2000401503030740240301d003000700d01c0000d0300c1c1c4405000080614601b15003003000d12880c40c26180a2001c0884180300c85904c60507640c0d95049544501460b01e4103149040d15100004034000c08180c1d410070f052071110540c0c0d41008611480208131104011140d040701001c107202c1d003e0041d5085120783d035007028011a000040c8000e00005440c0d5407001d118000000040352810650381c405044070419468003c094413100002ca416801140c040d440303e0810640d90384d0218120003200c154120030480950741e002694103078092840701071300ca085100c004002107040c06d040481810310502d012890108050302c00e600c056000305003650030382c0d034481c108 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 605489433 1250 605488183 605488189
    0x18040f0504020a080a0201081303110d0504051519110c0618030106090506060f220312090e090c1c0204021303060b01030b060301051e0907030209010305150a061b0b01090902 76
    0x1c103001c0d00e40301340504850a03590300040c0c20160701401c44005510f601440c80705041c850144d2228825103071059a54000000070003c3c815041401600c0c0310b242032081a46131034180304c0455a008502c02c002d07030301d2504c0c208400e440e80e001c00c0d1945074107400391444020036507460070000d0243c045640c400e900c00708150400e160854101e80c1080381c0705860001030042c641d50302400e031001d48240041c040c0d540c40854041900d20310941403001c4050142c941c000c410005011104074415081d175a8a161540da0340ca203110300200240c40c079040e10741240d120b0588900f4080c0b0055400401090554000c00855002c40d040b41d000040304030742e1502c2618240100f254501a000b01c0340f1003487c00340100656007000840070301c010300c10284903400c15071120107144402c1c2c03000d4408100041c0307019942d150105003d0041e5100b104410f000900d4080041c11051a1018030441a07030050810500903041010503624403031742901111440f1b0300040490001521031005602a001d1034102080400e070074414 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 605490683 1250 605489433 605489449
    0x90305010e070806131511030a0c0206270120090102161a1b01110919030503030103031812051f02090906090601030e0a0b16020f060c18040f050402 65
    0x4041140c2c1c00c1102e0402200c80c0005680f03411000a4503000401411403400020303070b6120040780b1054905000f03090a924005501540c8554a148400c0c4203140069004030707118401152000111a544140d0720389020640b03030380c050415410300c00003c9803c40d00d10a03580c10301c0c0d44248100505000149140203580c10b0184200c080c602c8640c446042d400e081074400110704c490190b80c0005808038146202000400d8040700c484c03006402040f1b59107001c82c8000940d404001d00e07038055074803c0300c920b6038034030048070301c1302204e8000e00a18116421560b003110b0000030880c20b241d014540320703030100d001c0d2584049a2400c074850002091031010580c3d1650184170041c1c01440ca013032040c868680140c41c0c000d89140d10200480d1307501515a510001680280800b060710103542c420581c1d008204500d100301130303015a41c4d40024a101c0541410101d0b9a040d64140a203119000000402c03c11a0003a010b00003404045450940c00c80b04200483c0848800100b4049181c0c2c651042c44103500708401 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 605491933 1250 605490683 605490701
    0x1c03030c11030a0c0201050715150609060203030c0307020109050601080d03050604020306060a081b0f030a0e0604030f08041a0c090a060207120f02040e0f03030117030a1d0d1209030501 81
    0x1800040503803200c1c4140d0b140d004043d03c040c01e118242c03000d0021a0301c902c04469201e68008140550a00b0103844200103010001170100c1d00da0840c0008030b907040c0030b85a00b00c00c03100e42e9030055156590b1040f4244054001403c4030055640782e180c0c07480041c0081c0959406040c0444c001c280c070a40703450004040d201c000c1c00d06402148104140319849d210300c4107c8000680c0b0742814020b0380c0f00c002001c0b0300300d0608040d800030180081003400740c2c500181d00960050040c4003050042080d00d9503001d0311014151030007004205148643c0e1403050245050030340c083d029400101c5640300b22810588148000c4910403241203000440c3c03907161070300c0c1500030040c01081c8000c2c8022414005403107810901044080c1009100b01400411992960072a05000c08100240c50242c40004101996a0003c2c021004200e204508010740b500000007034862500c3c2650341c0300c5d031b0703041540c400869600c04003c06a801541c40365110300440c0c90300700059410700707541c0e41e003003292381c5541000c82c2102c60206c = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 605493183 1250 605491933 605491937
    0xa03061b170606040b0a090b0307120e0105070813060e060a0c020f0c01051b0a080c0c10170a0f0b030a051b1503070e030703060e030307140c1f09021c03030c 69
    0x1e010701c6115150381c41900c0595502100d5603580f925601001d8501c0e006075444100d6a9100008005034694040b888502042c0030080601600310600320060070b07141d044482034001215080018081041c00f8180c400082c0100000211801c20000c56410424100c41c0803104684a860203031607240c2c100030742100b007036490000c0d041ea40050f1000074558802d86100c0142040012580341040d6002c0c041c3c0d61616500115055407214500c2d44140c64600c0011000e1151403100c844e00019401740751015002c500cbc550740607445598080c0b03868018070f43c8408004d43c00f66078080c1e00c03030151070800407800c007280a80300401c0c0e00050003034005110007104c01643d002c8e445050241d02e414100c1000d0326001002c500300302c0c0c80c460302040072074035040031684007600081c104008a00440380100c000c6005022555442000844440c0c0152542c072803840304030f034a5800055404040c007021400714103840e16483d0b010407010f10b5038000039546041c00c2d883c04d40031444004100b0401d5014486c4c12100031440c = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 605494433 1250 605493183 605493227
    0x9030c150807030e120d06090605010810061b061404120f09090b1504060e01030c030207080d15080111090913020d0807080d38030a030e0a03061b 64
    0x4980060070844003420710410b242d110b00155581d00c006000e99482c0280c039880300703915483c81501c140090942403141032a4285031034004074095200e806032504c10700c00c2c8a0040c1285141c403004a5a45004103030783c80914400900b081c00040160043c58800094070714805190309081c184103040c85550300d8010305120301004200c14035a001888442150762210001139051003000c00308501800000c600d002d00311002a02140765038101d00341e2100a07000381d0b42006441d086401c1035049124174000500301020920404400080c03540086075020201401d140c000e40c0d69044080c02d40d490340080f8403500501203507902e070504040381040e80c00960000c500d408203001d5004034009110b0010060030300f50000a200c0240071281c0111640c050b80680200040092900f038100905043d400c2020704104104090004a080b03107510300010b000140500410041c655040c1c8041c00142c1c0c0d00d0350000b4024074000040744042c85400140345451088050264840c0e400801284505030900c90b00811 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 605495683 1250 605494433 605494469
    0x909010b2820030408060f0406180807240204091410150f020a08070c15080907060509040e01050a2414040e01180c051512071b0b040309030c 62
    0x101c1141800090304001c2c0320b40d032218400b01c0d0281984525000070f00303140300d04d074203010507025140d00340da01c02e42c004c0008105000c900c1010002407801c0980150940e80140000e0f00072415000b1005c118003104841c00c070103804800e94600690f00a40d0281e591240ea42c0ca080c401c45204034071140d88402082c0c0229a00d5040000c0040a0354001040d0401c200b568458a040c850003000b071850090f401c41f1019880380024617140d054090240940b5002c5c02c2c6e0301c030041a1171802000858014024800580811414240301b26855003040460f60790150710b9020300c48410303100388101030003010645408144050181c3d0142d10070894160112a10030481404120010b8101c2103503200504c02c85001c10400708601007980036003007140845035004140b681d69420800031410000882e0f50540d5041c40e0445544035501441c016000490346a1030300c90300040d011440b900b0750510698070358100a0740c80009031980c010007401224120b000c40c0c1c030b0840c1842400020070050004211040c01200c10b040 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 605496933 1250 605495683 605495687
    0x4020303070f080d050f0a06091b08060a03140102180612160c0b090d140a1e030920190621020c010207080715050601020706140909010b28 61
    0x42070280151480c440c101c1007a00700841c06088441c00c03081c03550b05010f50b052015a2100414042c1e540000c0c0514050380007442d243c4500441011500510b600301222501d0403068a4a910081c081a803080c06441c01000090f8178007190150101c02400058a4a4803010b140d6640550dd041d030900c100418058040c3c4900d0044061341d00503944a9002d0a811402c041030f204803180c40c1004140c002050704224400c54001030780700719201980c3da910038181c209014620f5521031900f00c0c00000d0700d1540782041d41030000420340d0b2024041e140002c2c10080b0340e00e60a05000e10500d5481380f103c8602c1c414002450201041c0018100860034403840910f0709001a11010428400c010000c03607045482915500590544001c412010002c2d5034540741d03450072540d42d40c13240b242202c1b0041102035584c2c8114092180f2485a8410380092004030705111b0705503981002c20f20342d4007403900100010001c1d030300d404490500038242ca0300c0840d01c1d844000070001c205083c0c06913442d0700300c100e04030342d02003d9 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 605498183 1250 605496933 605496937
    0x2a030d02160b090102010902040e0c010305150a06140c07120c060503072a1b051519050309010f060605030a0f0b3a030503060307090e0a02120f06010902190804020303 73
    0x150101d690160f40d091264010303030150800603400ba5110703191403084078003403e01003544802070710240d80422043e60390040681e0b003541091500c0c0c0c2c014440d58402c1c030007280035031515041010208032080c00c0200c0d4405d154a0b00c121038001c184010480c05042c82001048000d04001e05000c1c03e003e0700b0351800a00052800004119030004403c000000c820642d070804030141c5100d4101e50202c0d40540c2200d09a038900c0300600c40c45024980c0700140b41c0e0000c18503816104034040d001b180303400c0000c3d407500c1154950005001d0440c0f41d5a11040e01c0c04100d00d600c65000100710300c0d00d600b6142c1c5089070190040300c4056105503902410260750510369603a40460b0030a0000d141003104040062074111150b0340ba10340350120401602c0150b0000b4160407001851007148100d0456600d580c44401102c01d9400b01b0710f564201e50301502c4030200518007540f900c41104500b1007200d2a18040c0a0464680307142a480041b030f0950006071941580d80e1940410000455418151102c1c100760340030903524 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 605499433 1250 605498183 605498189
    0x14101419200607301b030e030702010c2103050601030b040516080a1e0f06050a06020304060509040219030b01110c0303030a020a090b0a2606061b2a030d0216 69
    0x20b00c069414011450314100c6080c50402c50030805410440c900004d0007850410644c0ea608600240301d080164860f000711a145070101d405981842680e070f00561700156010000c50305c1ca807254003100403449044d40880e074140b006580c01314860a00400150480d404950034030f025504100400c4484001070b404021140c20307902e40360303205d41e4070214020028461036001c80c1da4403071813606105100c282504062000050f040c410403496603980c082110255681c465100540c100b80300130440c6a000e1700c09055414009800949408001e00103c108580c181000380d0129070b68500440065070b20174140b00c40b401e440c00091084943c0c9400080d82c90000502049540d40c0010b4031181c0340d4800c0d2814802080030b90071150329180904006402a501c8944540e03448442c18201d9840080040600c3d00030200507003114a050301002c1ca6080581da20b4107030100382e100b10031000d00e003035814582c0c01c66a125145003030b40000d40d000301010b082005c4070008000b15848500c0a0a64140b010b4a0100f2 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 605500683 1250 605499433 605499437
    0x5060702130b04020403060501030b0c131802070b0702061008010203100509040f1a190501050105090402070204110a11010e01090b180c0a0e190614101419200607 71
    0x22060001c800340c1c0600061403100760007500103d000010055240c0185060768800d08c595400c41e5101c94946000d8081e4050036404074035140c40030040341c4006c002d58050000c4015001d840c0201540381c1d504403c030b05030307012001a0700410401c0649a07607005d42c00d020700540c000a61460408680c00c12044c941d80c0540c07031043c08074001240400440300c405400700c5a1000100c404c0140710b580b40e49040200725030600001c41048a1642040072620071141600c0050b1901030908107100103000094004840c00c0b0f810035629901c9210381c1070540f010708400c403956540d2403020010ba01c0010309690303820791846c2c241c0c0e06040100e00010800300c0c00316442a000103400350606411843d0700c2c586402030b496a0f030004250003004c24545080b04180e0310504980d0000d40d10782218130744081c100c88892207810705005a40c0104032452600e00507a50144004d1300d84802052842040882907074403c8106140d2400000340100c100ca412450001150710101d1580d80a200642c440039240c010081400701 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 605501933 1250 605500683 605500699
    0x5060a15050f12040503120c041a0304061509020c0c03010213050121090602120106080f010303030e030d050c0405090c0f030604020906191808030a050403060b060c0f030a170105060702 81
    0x194210351006580300c20b10031001c02d10032420581417094407940904251000c999240c800203451102074030489085502e015032460014090b4013403010a038101800c1181d9140d1240005a020040d64801e0707c050103001c8030040e0b0303990811001d80c6c94052000c0c0d00d10f000341d006010f180c0540e0748103151305086507004c0c20a00d580c1070320341800002008039000c00c0ea148030700d0f16081c0014405c80354050845c0c6802c0c200d0090259894001c151414001101e5075281141108c005000103032098101100801034042240d040039410140002543c800b102e0103540d00300042403c10803441e042c00c0003074000c075000b6902c0e0703d4003000006a6020384001800180200d4001441d07000984a04003220103003500c1d01c1855850410281e001440381403610140d5444680f03d9401003500c84010040301c0c6030700c940340c0302c0c0361409165603184e0025000190782140e004c141407150301e60005c07062010402c42d41001002d0b65031010034000140140d40740700c601a81e1441008010f02c13907500e503c01140c9003650100da80c10 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 605503183 1250 605501933 605501947
    0x11030609060a120f11041107020d050102092e2123250809190c080d020d030509160e09010b120c0102210403030c1401150905060a1505 59
    0x5040000c154403040f070f00d8000c015071509200c92050040d01c07140c420f4528000c8070007044100810b5505800400c0d41c0400f080103150014948643d00f4030140740325000240c206442c140004910321045d400d1003041003501e010010302d60006007a80700902005061000304801c0c20248004c421088441e903002113686d4010100c900b16402101070a00e03c01b242c0c80744054a0540e1240001040042d588260525490003181e10709001d050414071485a200040c400c0c0140300203001c1d2202e1144009032010b102008001c901050180503a284000c0c284c5c000380868001040c00804556004108043e10b4210102200c0c01020b44595074080728143c8540da00325880300750413103004049004403194080f696602c6841018030100e22154040c0c0e09800707035280321220327181c3c42900e1403002500445281c41003000340002130140d0940d61a07503004400300180c10b00340003015070854202c815280341ca10883c0c4420803020310f0703500074580d11070303801d41d4000300d43c52030b000940c10801c0d202c12000052001c080354007 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 605504433 1250 605503183 605503189
    0xf0c04090c0c050d03140c1303050d08040c0f0302030601030609141b040c08061804150216021e0919150e040221030a0c08070506090c131103060906 65
    0x248014094031941040002a0600e01802141d40810121124080c4040c07140c030041c0648142d0789000d29a00d6a5402581d5400d0300d14400da120003c1d10201c009107542c0800400c008001c090b440b00c4494407070004900307180c2421601c21185900a80c0302001d220780a0005031004a8484c0c1107d92103640498101035030319101008000705035040c4c4003407048008080307001103030030290112080c045e50108003560010b136085074081c404aa055800501c03101d81200e01c00d0f00c0ca090158494056062a03040723250b0020050185d900400c0007100040e0080030b064254a400070140c00c120141d1111407501790020717000300b0312000340248003001d01c422080c1064900f400c01d4102c2c41908905d4031004104a41320105a62141d0095400f60f0203410480303800940f440200c20f005c588000080004e605200c0040d00881c2c0058040f94200c4054000b0b10000700060400c04c4114010030030030020703124400d1800240400f00703140b0301050701400e0a218142072107008000032250000700685984030343d075640c4804 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 605505683 1250 605504433 605504437
    0x60309030412330e0d02120901030b060307030506040612031707021f050108010f06181109040e0109062007020913021f02190c0504150e36060f0c 64
    0x4003031046400302625494810402c80c00d504501d00f0380d101005000e02c0d0340485655100954030f910091b038000c3c032142e50364410800290006940524000c15440c00c980d0214009400a44002c00840c1d1180c062141c4e03450a0302a65002d040b904440c210034540c1602c0040c4180060741005015158a401007403030284280a03039643c80c00c0c00c050300700400300300e110034000528007449000711551800300380755000d8801e07020b803a0464804801070034410504e100c0850003024021290840b100040124030aa52a14020451104406000007502c014a030070900e05455403030a01d2805c1000c3c902c10011041d00c43c0050b0385003541c05540300002907851120646000110b110007940c0a070001d050010888420501500484415800c1d111103454076400d1005080b5449401030200307040c51800d2000b4181a4007010214041eaa12100035030380c2c90401c00c1072140180d80f01c0024034000e0702d090781e130400e041e1a0a046811295065100050713111085a107803031015007410308060b586804a0148400030003 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 605506933 1250 605505683 605505713
    0xb0f040509180d12060905040809060c0f0a060b010f021204090b0f03010e0703140f0607030b01020c10110c0a08073c1d0708010e2205070e0105060309030412 69
    0x41101c10032019000b0261401c2d0141031811101802c000000c03c07188064007d5a000d00d03400843c09082000c440d00700445a0007142d10b82c1070511959415056040c0200104010b40e8024a0002821800400010b00b2501200070050940d80650b5902c6c1000400f003007201c00302d0342030490004040c12180d00050a640541a60a40c59824441d140c00c9851000c44e030001100c1c45041c40f90f59210107012300a458405848859107690015400175804c2400b03a0000030758000c051055500784000c0c10300080b9002c424103c010300040b4201d120f010043c508003c0003420500403034220008625000d155903130740d115401040580d1040c00c003000c034101c0c151119012103030105813200400c3e030008482d4a480301c0803841602240410040340c882070b01464040240500700959610702981c0c00e00310210503200c409000d00c1c100c400c88524403804205443c009284d0280300d1005000300d540f420026803142007040e08900d20a503410004d1028202000003141c0458081170489400c1182c5403e0034030080402513 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 605508183 1250 605506933 605506981
    0x301021201091401060f0c2613170c0303070f06110d0b040605040e0c0907180b030117011112100314010b03100605182d07090b0f040509 60
    0x7145210b040d40140902600d040741d0180700383c0c2d07100021a04546030980301004201c013401104045407824070100012440001190042600f00c05c40c0050381d4491595a13541d8203d85409000c2c407035005c150007060003040c0d801046019480800640c40381f1401c0341c0149130014040801c0d00700007180c1c0001c6007049080d06025112042466180054010281c0c0380b4440c0b4a81400030a452604d4410855440080e100a08681203120b090200000028007140140680e254504405580d4401c0c55009400b1101c041c507107d51501d902d003d840091548103080d21390400300c074001c0e03804013003094800c0380d124158410b0b03040e107511585030441c0400b07400c081e20800e6007030348242042005401547c840c14080e42202c01030170300c07083c54204440c0700c0d00805511010103542410780f031041c0c900054004d04520600300980d00c024003032820a54880303041e0060711001d40100214140c120010200510005004a00e020155169804548154000c19101d0b14000d070110b180041030f01a81c2d40030101103 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 605509433 1250 605508183 605508217
    0x2150603070810052e140d03080c16050313030215031317040b1b0624010c0201180f08060a02070308071409041401050406170714012606101707030b030102 68
    0x8106a042e201c5500e00551b10800c00c00040041c442c00d010344004074030b5030556520302032030300c0302c0d400f0380c1c056440308201c5020001011040000705d18144018100840318a4002180074034510600981b805113401c8451101020f008101d40ca800204070703000e07880e40c4181e007070124020100d070710b589900840c0c101c0f048003507010030240482421040c41e034840d2441001150080d07a12641c68074400d59022101d01682041c0c1309003116654001c18800d244a441414003815000842d1001401100580d20085003150007080421910005105468000c00110000c0d49800c00340d803409411400040d2a0b0001c12900c0400a05040d0440703040c0c40d24000300500030b000e009145802c0e44100c0c0360070b0161611403860b02500180001194060a0103111428040c10700685042d040c1190140403000050510695880c01d48155074912100c01e0707406d5890240c1d40c0f0500340102404880d400c0520309805000030502481960414450347c258454013524002c28401c003c000444d003e0300440c900400d1480321 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 605510683 1250 605509433 605509501
    0x51c06171e3d050712020309100c02030d050c1b0a08030402011805032e0b01090b1608191d010c112107030203010e01020f1b010603080403030215060307081005 70
    0xb29007001d0300a0445a80c0d15080d20001000142203200546901800398070031030740d0703461005d03594207c016081c40c0e40c01980e05006035200c0c03d4080e2038080341c6410200c2c0000039004c0b0640064050010301c040301000400240c1c10719503070b00079103203c058000b034140f226040b40c0001302d002681c1400060305002d0141c2c0c06004450f000ea10524088031102c800704044150003602c0042c013840b4028220720165100900149405400c0c0e01c258860342504003030034a1540b149000c20b0807003005102c0202c800d01c40d900d0302c07403c0c0079000b0903c150740304035121210108580002c135681d126910a92060308030407880210f45c85000052041040d4810425001032100005105480041822011680207030020300988500c01815400c0b80b081403014006031109200700d12101203071503854071109803031a00010380389440f51035403101508294000c800580c0304000e4203c410007a00324075034200b03005900400c0090300b418503042e1503000782e0001c640c0c03040d9a4000a00f00100e191020310038408400b075a0341183c58 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 605511933 1250 605510683 605510803
    0x20a1809050c01140414060d14100909021f0215090d090e041205030915191508060a090206090904030906110d020706051c06171e 57
    0x590a0390554160059440d144410b5004072000a810080030b0a42c0b8940360a2002e9881c40d24170001c0040d030803c9003442505114816441826103082e2524544900b52070801007a4a108103503420000340b403070920b05140010384844d030020001c4e80610959442c2004024000c034944004c0803051044030113044103004070540003240003ea040816030750202856101e80f440920044241c3c1c000380001d820251200341c0030b105002454101e0380f410309881e28103106210031a5200303016203002038080c4400109a03106900c40c400c8081e034050001d0182c1c041c80c90302c01616120700e030080c0024901c0e03031179180301e508558410b0100c60081400412541160409090090146550703014001c08522603004072449500c001a024800d801c10f9801011180c5c10920202da15410060000200301c9151101520700041c600500d005800703400311598030300b20307401882d40c900390000c0d450314090130920601031106075002c110b1301c40242d1510341514128000c411010310a001c1c1124402e0010640200040350603 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 605513183 1250 605511933 605511941
    0x130f0605130b030607032703020715030e0c0418150501151b0213141807060f0806210601090507091401050702151b0a020a0602030403170304020a18 65
    0x1510a0703031401c0d10701e0140c546a0003126401ea1041e5455031081d000919054400d80240c05540d107100c84100f109540e00250b000500c00c142c00880158000c00f005201150441403c0e411050f0a03240c10b0000f60034510740c1c0c0340c49144a0140c40d00503900c1d042d50120030840d034841400d02c164004e800c0300143e0060007541000b040c0a000d070b1140081d07070031b100040c01c0384070f0b0504449004801a4039000900d1650800c99250344002c4d0300264180c440091045091081c0c8040d8810031250203a10390865a0740749150501002382c20100c00c3c052103201440e9401c0e8810b03145940800c056071190f407105070750350390708603203400501440200b80305600020601d19215040301e07000b81455202c0100ca59142c1803002d0307803000000340f01030009105020180151800a103146241d4003400180b07458996040703204103298001c2040340409510a42c8010300314104a10b16070014203c80c40a1810107095030703503c540d541c01c4e1075880035030b494020000c01c0555440c0302590300100b907280c04d1811388003901130711080a4 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 605514433 1250 605513183 605513189
    0x1416031d180a0c05040305120306180103031e0f0909021606020c03120a0203010605030601030507091a0a080a1a122d0d300b060f2505100b130f06 64
    0x60343c01c1006158649001e0010341d07041d41d62140141c8001c3c40d1069091500e1b4000900140d03000c0000110b4050004007942027a01071406035441000c0c5080c0c00d6444130310320034810025410403e944005c0700029a00081c1b203070a580002001503500c80d120869001c0641e880d00019203201e1000030081c1c03e03800000000e1000d080d005040c58203541d0340701032100407070109200d941d000c59010000a4143d41c443c0c4d1103d5840059400e104015079110a124610910750110200c4c0300900000c820315150781180c016540684403450500010200c0d1080544404032502c4190155048074002a5881da080c442d402e80f2000c0781074189402c00d003034401030040001095400a5034080c0742d810144c81072045203802c1e1108a034000450445603812480c00501c4541c1100030401c40d65440818581d03516080100403001500c0d15140e154001c5618140b0024038400c00e90401a0b908421003000400100e031501da07451080900203207800c800b0300802c00c202d00c0030990514880c9007049406038600164020429 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 605515683 1250 605514433 605514451
    0x303040603140a2a17070e030f0a051b0612070203030406181101111207080304050c091b0d0f0c1206051e060a0c02030f0d1416031d18 59
    0x560303103541a001c03085821860410360007103a03c04c040da41920411019a507001602e1900e10380180000b480003480003002d840e0f9a00040d1000316114140c40c0400010365060600702c00340036404c2090780c840355601e682c80302d0646d200c00009100107141d510131054038043c403a40b004d40a05480d01d031000035104d038008c94080b1220340c1f410142444441c0403484200e401a4032014050300d1740d40410054403232034502086080e840c8144070080303040303041081c040d01d0054840c41c02e0304d0316820549841030034200d11039035450082d5038010820031141c82c0d00d5805d202854140e0803042d50340300d030480745d04007402000010303803216410001040e042d03175400503652030000f03a054403c000054441d0b041082c041100c1004030511000c1c540e41001d0f6181001c010200c2082c4c0d8108480c0103070241c0d0100381440486400e0b80741c603801283d055850140c2008030780390a84403a00d4002c0c07810ba11071042d075410003500c10020b01007001c400480c40601d044884c038412585401050568a10084104404840070480d0074140f = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 605516933 1250 605515683 605515721
    0xb0414191107060905070e0c030601080408040b0d021c050f04030c03031d0a031d010f1809090807170301050d030302030403020708060a060816050d0213021303060b1e010f0e010c020303040603 84
    0xd051400d240c1c81034017070034148c1ca1882c50364442c04011a910b0101402c156091f5034208000541c09540078010a021140c403103002d82c4810007004100c3c01441e0117501e400741d681c1800c040061a5101c5400c01b0303130156242c02c0c041d00d01001410b0480040100e443e10701100d40640700c111030041d4000800c034164074865550300d115070401003c601480040e001c8602e000c19022803c1c003a03440e001e403122104118185243c150507665545200c004d0303502e08117007980c410a000903510300f072120032141c100c03083c0b00f42d203c800e14551400c004210205444507002d000c065000c40407804152007808428001e00040b01201d40e0303414240020340c02401c052080030074501c03821001d29a401440c500000403140014222800ea040a400380710803e46aa040c1c003140d1a420040f0049558601d00340d00301450140b000000c60506100c00e010400707201e441005c0941c4180d064020340703aa80302c11150040c1da070500d001440c914040740182e40e0802605d500079418013000c1400720300154142c1c081d0110001c10300c0910 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 605518183 1250 605516933 605516939
    0x60409021c151203030e060a15060804080301030209130f0305180904080f0f130311094206190e0114040902090f130608010b041419110706090507 64
    0x808a404030b40045251a0900e4010450040480b074a000d856001c0e0402003141e01e0111b9015080100440350081055039540000d01d80d428110407034006000c150a100f0302c1400c090301d601c8580d000510009206904000020300300310030030b0444016080e80041380b00d20b4801d10f45405809a0801d11180c0304800344424001c106261980e6000d0082c0c0d0846450f62070b151208607684600da0091150941d0180100000c47c01105036150340c2d0003c42c000e142c03483c00180c100040050039070000e0884944000120400e98140c40740915154502c02c0700c0040d40c0d82407211041100c1c0a102c2441d4683d84804042110840509020007600301803425696085481045100540310b00900e01c0d84c025a1145c1031105003d400d50540c010480c840c1d00820300c80c041140c00000035a100118851541c0c4241c81d002c0410104101b40a0224000da044400340107a148a480010451000925000724503001c80c1400b10a81031036403109460070300d00c591055540035a8280716010701140c0c0c0301112203200d050000 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 605519433 1250 605518183 605518237
    0x201121104090e03040f08030d050f0f0612100f05010801050c0703020d050705121606050c090d0209061503041a090604030f03150b040f08070f0806010501120b06040902 74
    0x920800540100c0074101814402440700401c5240c5109110f403000b003201080780c2401c0c1320140014104c44004643e20700d40d2803452000d80710094601035407101d008013404521080c2c0d00c106948010240e413206050b100a284040c9071200104a405802d132074091000302000640e08054143d40303104000b4002500e0f8960b040c80e4510800c0340240c0181c2214400d5194144600e00a02c0400d0103102180c0e50210b20002440b0568068066004241c00c1b40f00e030482001410701440e030340400c11104941c28a000c1d50003060800b100a000244104210f100154055071110901c00d080244001129102d1809180210380614031301900c00700c9e844010300180188000003000c510540d07043d034031020880d062150a402030720401ca00c50b010040c0000c40444c513000c404020344010201c203078140e50720903e04004503062680a4102140403862a00e061042880018046044500a203440c410320010358010400400d009005160300400006000580600540103170040c4804010108241c480410070 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 605520683 1250 605519433 605519441
    0xd090c060302070524010e13170309010b04060e01120311060106170f0601050f0903011b1d0609090705131203030603030f0e0a050411120a060e10030312050c0c06090a020112 76
    0x139143d05c5400a001440007a0703407000b9413500441e03104140c0205030820b5440d5651220000300100030240d000c410840c07200c000b401032401e9002c080e907040100c0b500305454450118414001c117803142800c0d14206013018443d400e034008091101c410358143e56151180184412000031a100c50a090440410083c43c49405111302a420584440e0700d0540302c50750000150b04048900341d40340d5030b139900c4008444800800c0e120248903c0e5078440c91303071141040c40c0244100404080d40500020701042610b0380716040095000301c55410400e03141c044000c5250b11a5030a5005909110a04820b0b80d04054243d000b4034203880c442c3c0c40d401c0001c60784903070846130102121a04d030703484000c001e070401c01803c0c103511000a400240003d580b0380700b100e1130285a00030007565000c0c0c400750345800811800e86041d00150300011881c03442c005062858400a08041152000d8000d1558880128500442e0842260042005070741551020f181c4003003460b032162101da02c26408250320400ca20246034a5100b = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 605521933 1250 605520683 605520733
    0x616140f0631060f02030411040f020403110d1110030509070509130f0318140f0603091515102f101104090603050622020a0303050d090c0603020705 65
    0xb075003202403840201c0380c2404110044080d00c1c02d0360303111540703000032482e40006c6109078003402d0a084107240890901c011524581c0d010b0b0317120743c4140030502c001042c61503400d14004088590040e43d130401e00b009050421940d05003644000b045016004464050f0840c51040c5000410380724007075070300c3d428402020012a164101d95084039100c0d000a041c5880310385d9210b010b0316001c0140c5600c01d020f4032521189800105019140d076480d2000380c0341c0502452888042a180603066040c66a0300703596a80d103508040e0100003124002400440c013100380c002a02000401074040c001c16400090100c9400d0f040080803207070b803000c0031800da807800303c90442440c502038002c04000701041c100c04020b000040700c4d111085002c2200051403496405074002a50040700504468145103406031030060546040340010705440e40300c403001da07440300024421250541001d07070784d803000007070342c1402025000c00051114000301004148564141c1c00360441601c10343c200d82c401e1182e45003001000c1c200c20 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 605523183 1250 605521933 605521981
    0x3040c0506042c041e0614010b0d060b072303070f030908060714041502030415020606270406021c1d0c03120301090b130c05030403120506010e0616140f06 68
    0x404001039020030407029600b9006c0c180005101c600c160340440180802e0780700c120215008200b07070391424010320502001307058a0000300c1c50f02c0700a59940c0740031151105140203040001008504007041401207860203640455190025191460040d01070700c0c150007400384501c6000005004035014440051003114444840c6080510b060b500b810010001d1301c5050440c001071100090014004014600308413280c0c010b44820303d0948103200b200741601d401c81c03964103100006580809400615075421a41029025035034400008031108034000d42c8500034441883c12020b260300380803a6122000d516141826103402c070346c0e2402056512051040412030707480c42000104002d04081c0c0c40380c0a918409020242c0e0124003107a8401215505040340c00490f030700004001c1007544c020406550300451600c104010304103600001c007807012900078a4016040020071058013072aa082800307403268028041149200c11203807541d2110081e00d0141040d00c2040041081c1044c209051840c2c0f10300a = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 605524433 1250 605523183 605523203
    0x2280203070b06040c11120c01050f190504030c0209100e010605181e0a06020f0c0604230f030d1d04050402030622170304142103040c0506042c04 64
    0x80f10810000b401075006450038882d051040142c028028080c2142d8600c1c02c100940d203c1d0340b100509400d40300b009000e0540d0a140764100111022070381c00325103050682c51400905661580b60a07276070003800701d002070f40c050329410070041030711501d1603005c05403244081100042e9a81d00c6041d81c00340101c0501102c1400d4207010302009042209002084d843d940540c1005203684502184946179590032060040c3c11007241120038050400c40040304607420760308a1b1805180441024107081d460101c840f101c1100c803c10300302a5100780c1448509440101900c110484084010304141a1080c005000c05d8120000914a1a003440390300d10854016010301000d5880c901c01c039512032008807002c0e203c4460075034450302013255800d021400038904e00c8600d540b03003428101940b6458003800c0310400b039481190b0040541c85003040300c902c4048440651074503500c40b40781c00b0041001c2600515041200410000b520f00000445103421100f00d0207100c9000845000c0e1030306401d003c480c042c11103000 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 605525683 1250 605524433 605524441
    0xb0c1b041116050a060e070f0e060a170f070f06020709050f2715090613030e10030608121e0903060f0411030105010b0c15190b0303040902280203070b 66
    0x10200004070f40300e038054402c0c0400c240d0f1003808484100910185a62000358144841008800c010002c0c00e01c0c0030f40c40c19940b8080c0c0000307001d001c080c00703020340c40c041d458402c4200d000d0800c540e800c071450034026284c1407504d400b00307050344003101d100307003801841544030000e107017865803141a00800c0c2464144902e9982c4410b900640e03484460070204607a4403070b01c0b800604009000300c00802c900d1442081250030300c058a0303850004040c045d01000c18204c03201d00c00082c1c00c5400004610415140c0c5080e801c201d607002d0b001041550701c903844601a18007450b00d5490100b0081018040d101145660101c00000c2c00300c1c0360241c0390310103416070310900100c0c410701d006140d903c1d481348c0b00e51075201e0044481d802203400d45030281d21150b007410012030400380350740050000c020800b540c403161086e27904e480c1c502100341c4c0d03001c6800c0f69071b40c5a4411107a1802c0d1828400c0760050b00000009550320140c04030b0001c4520f080c41c011034030301c6884c41101002d540c804021100a01c2d000303614510980c803 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 605526933 1250 605525683 605525707
    0x30f0213060c0c0902030a060302040b0108060f0913080319050c041202132307020f0312060f01200322050306240409050105040c050d03120c03060b0c1b0411 69
    0x107150b010340e59903c061800144d42e00050006600ca044e14000200b84a45984144016645900c100c40c1c1401850400c108860300c0390215034180c244215200301031510b494150104c440040e20028060038400400c000c12141c091010245030f002c04d54041006985419403160b407400f8901500041c407900c40b242c0005890b11050b0420086204800064001404131070152034070110801c10961443c001304010f00b158050100011542100000c0c524106901d000c0e88130b51300c0010700f050f02c602e00100515015034440e500c144951408107040c3c2d02111b2001482980c0da400c18804690041444050702c0c1035412805202d00c11030380041d0081005480b040c2210b44a481c200780981415882210301030b4441d6224050350301400c0c001e5000060900305410710711101e461070340049000b40501c425070000641c0c8131040002d02c2040f0000041d40e04a0b1800440c090089030b03202c14000d0318041040c10b031801c404a0181180c0400344c8030025040040d50a200070f40f400c050b40c103104c142040c0301080c1140 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 605528183 1250 605526933 605526947
    0x70819050a02130e0f0105300a082152030f0b1c140c0901030c090c0206010b040b070f0b010608160c05100207030c021f030f021306 58
    0x3401d601015040c0001d81269030706070000399000716090f660070024410842442020280500000c0c0d800561040c030b5035400200210144241d03142a8609a840c0001c0f40800d03c40411010b50100c1c210b599020110441090f08080060751800d504010703001ca598013800c40b600400708845030b65407200d4a0070100f2010b0b84190354840202c00c25428043c4940712010034000704130050007940f000641c800c0c14910307050464062410390340c05880d4104164240c02d4080b0860f66800740d2148038040000f207608040781c10008049070503604a070440c4000310400c0103205408080d5019a04100201004001c0407a950703107003880340450340502003006000600910005084a0303014028001222040d550350040c0000300340d2111000402d2503040c44078000d040001c803c9020f103149070100c1801c08546816855000310b44000b222940e00040800030180200600700c40c50740c00900c060880202c44031400003074292840204002032a00b16000d172000168420345800c600c00700003c0f8021402d040007074600c1 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 605529433 1250 605528183 605528191
    0x1801120b100e03030c0d0807020f0705280e0f01030b0f25030213090b010207120b06090a090204090b0604180b160908030f04050f01090501050d090804150e0907081905 73
    0x6020400005401e20400c012158146c000303a0364510052400201c0281048103025040e01241c002440c03c016654407071412103d0400e0280061032800c49d040d0f14400303100e21070741c403000491002c102046400c04d0704602040c100c03802005032040130b954449e10f01802c03100840d0312800d03040c1005500306130302d140140725426001e01e030b042c0103140c01d09030783c0003039800f00c6075a115503002501c8100809903943d051103664002c21510510043c2014595101604400f0060105008401070303000101c2d1100f40c0d0b0400c00c0c820790040c100304800d651909000c8410103088a0007401541481c2d4000284074541e942040e0f03268002050245070348490102c049503002540000c0100719240c1d0001c500ba000900003000e00450000100d0703520351a15083c48441e110014074a03060010001c010041d0381d0300102202c0c084440304100244c80155454500801e020720f40140200c2403505810000440e0010600500088112401805a40c42d10021580c10104481030302d1050440d0284030b002c00c01681000b500 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 605530683 1250 605529433 605529439
    0xc0611100c030b0406230a1a0903011104060f0305090706020a02010309080c010c02060414010204060807030207030320130b1e0313120f1106040512070602040b1801120b100e 76
    0x5880f1000c0000d0241c0310f103034001c10450704000c10000003400c200b001034140c40001b601c0741d1060b54900326400c841f21041d6166001c50600024094955517000e40c441501d140c02d51035120b85664580c10300800000c0580e8112022030b1900010030104c1000050090032184d070342d401000a40955070044025055030302c400c8540100030b028120081c54207001e81c07100554107900502e4030b454141440c01000204424003509a44100000d0010301d60001d0000d51059050402580d2415180f0f0218001e00452500200c000c4000544440040c0007034010040040e404e1003440d00240c031002c0805c00fa1098006250704c00c038155281451070301402000d10b42c00400c0044041a40780180c45040264a070784454500150245601e805040e0b00003003103c0c4a058075800400c268581a42d030b81d9643c20800c440c40020110200d01c8030100f1006804490103481022840350f298810f1001000d046003400c2400c2e40807038120200400e40100520500a040070000c3c4500085180c043c402d6445502d400300141d0 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 605531933 1250 605530683 605530691
    0x513061809141c080a1b0e030a0b090d030606020705211608030a0306140306072f01020403030f08040b0c13090504050d0f0207080a110109051008040c0611100c03 71
    0x801544144101030380c0a5085003d010400c01144008048120040a00c40c070b07580790282c41c550034070030503a901803010303880d003819a00d400345100042d01c0c0c172003520720007030006030000100300481c100440c0d4800b6040460310103210680e12070b40306036101d101c030340185a0810101d80302290505a203c0490301e821440c40251014908003c200510711700b0305400007400760344005002c0c94856458415400205480d406181007185940300180d118103000d8050020840281d41210042d040c41f000e40000f21a007901d001c00d050456064280030750004d11058010480810704103001d28081d0909911842d440660801d250342c42c070075224a0364004140303041645610303501c0400c0c86ca1991007058002c82c0501e00a00c10700410a00090031003d920f04190300b1034003daa030411003e20700042d02524141e001b0351114042501e24012120500f450380521303070051503c2503040d0181d40151240e40250f0081d1000c0d031203280c40d502c0907505c651400c0303901405507009001600469100b94054000c004661070085 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 605533183 1250 605531933 605531963
    0xa021b18040c0302090a020c0607140d090b101d04120c0f080d050106030e03070605061503011e06020c010e060901020109060e031b1203061c17040513061809 69
    0x1500d03080841e011140b240c40400d0900035894543c4411303512070b0900d64150b02d80561420070030f441d094058000c00600c0248081004040307426015600c2e08102180c2c04c01407580300b030401407050b410650300d80003624056400031400da0700b452000036070148100b5400406e07440300e40e9a102094141c1c612101048480141040011845a45000c1d4140031b48050b6884c1c0050400000440d2010703803040003814641600b40b04401408004d40c1c4c0944d400400010320790341d5110200316501040314004040c0100000046000c503a40c958004180d0a800c4c54648110f40319501aa5070366101c0161902254003414000d846d49402402401c07060010b01c00810040e0f60f076541da00540f1078085503281c494202180b401c00704403142d01e003801116100b60091011302101c0802d00c11911000c0d040600071030400801039042d000d180102215140d012022052611032210302910540150003114490007400e000858000154010503081c2d59110840c42803c84114000400402c401201201c07801c1d0a0207040e = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 605534433 1250 605533183 605533219
    0x203040b04090504200a0911040902190207080f0705090720071a130312021507050d05090c0a1503180c050103180f060b060c2b050a021b 60
    0x241004203080b11010855040510341307080d10360041e100340c12801150039410042e030341d11001d0000464082131000144021440320100c024810f6030001358580d400040d07001c200405040c1d1040c440c0e05150b00f555844c50b00d81c0011619074142100501c1c0680c00b61000b4001c034a04081d0b455004403d41c1007140c0c10058029854119158105804419400c200010400414800140010071640b1800140340c5403000002e0141d6405900014044001301004001c20500070003100d40441c000c001c4000740c61030411802050350b030044030421491410f080105a036154001074280001d00001c1c5a0328850307003000e41c22042000b0100029040545410345900300c4003a0038114021540940e0000c1c441c0c5080c00d0001d41515113034a1540d0b10310003030079440c0f0041040e49800301a00da0340050042100c2c07603a480007401034003c0000c1441c0601a03001c124800c000d1580504802c000301142e51000301c0600c2c54240e4a034010705000d003025810035280c4003101d4a98541050351070600514002c0b60039200c0c052 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 605535683 1250 605534433 605534437
    0xe031504151b0906091521241508060303032412070e06010801080307080a0311030f2a04120c1a0309101118040603120210050a0b0102060112030203040b 67
    0x180b08041610108203112080e8001c03807020151209004010590102e0100205030320000c01c1036040c0700142188606954006400c4406a04400c00300c42e0102e003042c1c2c000e0b80c800b1205120781030340e042019080704240c0340a010740910421000300a0b604583d40c072206c10018102010980148000044160205584030400600075640c0407008003ea01d0038125980c0700440040e00d058103028425004205c0c400c800000c460762a40d0041480e40c85e2010340c0c2058004e4034aa00f46d0703410061011041000f41010f500155120366130756100300886c079015401080c06034040c10f500290f51a005c003c148184901c0450110b010f511400005074603030350f524143c61801c101e20b880703d125454004184121150100008500700c440841c04115044903c0124071252142007041003201e4568641c041d0310741cde140d9000300d0040d03800818043c80440315903002503c2c1e010050020000034509004110002014418030f041800f060300101030f26401e0040005c0c210300c0f2120b00f107085210400c0302290320310b50713000 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 605536933 1250 605535683 605535731
    0x80403140705120309330d060e010909021306030c090c02100203090f2104060e120f060a0c09030b04060b0622051305070215090a02060414010e03150415 67
    0x4013440c0c07074401d11020081413903003807000400f01c03c1748004408005408070214580304910508800d40e40c41e4075041280151105601c018040c1c031036103000103248682504814001c83c8203c070f2000c02000c003039030740307104640c1c603800080c18840f11042e003442000103550202d03003101e107680112040310400804030405d9a000301d8108509400002888004882c04c108884102010410605030803240c3d40031490540914450301c42044005840403035543c0782e0600551f006070060007a130340d54440709403030a9a00d0b001502c072280d1042c545010307510307410b01c01e03102e140c140d96115950b402c80351106d4480d240a082108103850303010100b0002d52250b22000e07040000da203401052900390891410041103010100000302d41810780c108010001940d6000c1042e1088810800c200801a110301c08558a000c0b243d034802500182c0015001c51000344017a07181e0951007003680d80a0000345200280f43e00c40c4000319003090700e0703c004004500020445648000c2003400810005192181d8505c3d54080a01c448 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 605538183 1250 605536933 605536969
    0xb1206010f0f060807021b0f1c0b01090207021503060301111903050a0c0203120c0f0708041a07021e04020d110a0809030405011b020a082d060103080403140705 70
    0x40390420040d980c0b00c159900420760343c1002c010034a06180c019442c0c07010711454551b490a2010158419500c240c4140c1e1804005840608040c00310140245d000150840c1625440c0c200400004c0550781030007181d4840740e000d040c1040080044c00319209079003001d0b04a07503142d52645018082140040007402e07801c86035080c080c01524803050060304803800600441d15140c2010b110070002e503000000c8641e100759809880003266600410030401d405856442031004c0800107882d41400a541e0103402982c04104a00c40c80168036000803002c1c1c4940d000c0250072802892800c4801c0b1425555800d003864081c2000d8a441d2903e540801101c1502c8115009c81001103115401c183c0d201e031605505c4400600218941420030f40041d048503a00064100c03000c1c0401100b100f191107408108000342a8481100c0540700501c94140c03641e8000000702d00c0e084a0580c8184000c44001211070482c4c0e04001003038941401e43d10f540a04c000381019021080c800d4030000906a00c82860749041041c141c = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 605539433 1250 605538183 605538209
    0xa110c060307180608011a030628060e090f160201090f031707030504111e03071215060321020c0901080d140315120a051c03050708190b120601 63
    0x1c1c410740b06107140c083e00540c007001020070041c01f5000c21a90448200c3c501011400e803070f95502c0c000107c0314205512404031200d001c5c4445401c0c260060641800c0da01e00b512003621103100c400501034640303400c40e00704140c100b840e00850001a1148225240c4207041e100105498165484540340359040c11030840008180320380748910001c0d081c00720b40c4c00c84858a410f11090519444040071400d5010700a8464480101ca881c0c2c680e0004281400c0c6100c0981510645070780c541301c2d62500c501804060320044600824440d140c5118403c000c10b03258000045403981d40c00e442c85020360fa0702040c0c600c065104034803501c034180d6a03511102d802010501e0041c0030051010310000c1c028960780440e108000000d0080c4000b8644031800540030180c20f0f140301c40b0706080c08100502d003405d8150050030b54003600d4103c20140f4150008201603603180c0d207090201e43c03035a050403100380b031003229110589040021802004003050300500c40d0140000c10000c5c12201690040341407032400e910440c104041 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 605540683 1250 605539433 605539457
    0x180703150f020304171c090606090c0212030f22060b0333061801030f0506070804200301021b010204030203011812030e1c05030612010b060a110c060307 67
    0xd0340101410364403190015400c40c00d242e941e01d850a041c1500d050038030000451004c25000d840e010b09030321007a0900c000d0000388804d042100041070940141036100d41480c806d4400980005407030202d9000403403d807803641da0341c96444407090601401000c020705018004802c44801c6d101980540d0303009100c0000c0e0210746004045c5131586000c0405d0141c000c101c4d420344102e4001d40c10380c55022100d160341c00c90381c0d40e00c0009075880d44402d00d03c0d0703440440c1c80300101c18082a5000706020754072400895145840360b8000341c0c0c110004a8000f800500001490410030705090500c040549002d0005420034095000f10468284074030741d181c1040e98046007c005501e424002c00305910707500d0900c0e16900c1700030b4071115406008e2038040801c2c0350b101c1800e000b00344410844200102903840100c1070581807490000d14550040d10728511139080109008504803040c41503103900d40b0024032a03460318803401e10a40b0b21341c41045010301d244c0546c04c0e2005203515600001c0d4425a02c80c2d40e96607007024 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 605541933 1250 605540683 605540723
    0x90a020a08010611030703030b04111603030c030203100b090102010e100b0112230405070e04080301030b0603120426060405030408070b030f041104151403010b03030f030f180703 78
    0x84160300040c1008130074114008004000300c00c82e81c283d07825190102e4a070307002c400854080d02c603804116180c00e0000414051212141c14000f100911a90381400510712a0b0021000c1c0c3c0415180e4404901c20407034200201d4059400600b0440f90600021030403103d03624403241002c200ca00c241820b0740d2580e10045e0303150783c001503420180000035402c10841d10088190b845441b00729907100c2c00082144081402d002040010500070142e03084200100d240c07915001e1020740080c4030454440c81c0600104682d4940812140d00507808215540c4c1418580064001c14110780280c444d044040003c1e9003c0d0000e0901606101300c1c0a00c00031a0380b2403030309003014500f41060340f24034140340060090017140000700203401e81054000003510003c80c0040000303401002c1c80110001324207080040003c0031403100440c0c81440308101e0013005514654414581ca034840c00010002e1200c04100003a80c075030b21002b02035044411007555254280340e075500d461402e400c581080d074030b2003004c00d4491480c030 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 605543183 1250 605541933 605541947
    0x10f0e0106050a210b040302122703012f0f1201050f010c170a03020d02032404060303020a0b0903040806010810050105010e010c020103110c071701060801021c0504050705090a020a 79
    0x801d41c41c40c8060f01810400144d081e80e004c0c00080c443c03a00f10300420207243c82001540a8808100440340d6103001c03940030b00160140e403580303400c02101ca01d041e01c030b030600d4103200b2441a220307560100402c000d00c1008554502003940600f00800c001841486000408a0040d04680442100c0b041c0c0b254105401c112105100c00c08441c10412010040e40000300f5402d000610000d0b441403080c0ca8088014081c1e0190107290f10340e2980c01d10101c01c0000d1007150607002e160180c1400024400c0b80943d105210580340c0170301001e0b0141e80300084c1d05001400300d10000354070008205c2034134109911354511904202081c0c4c4042150f5101c0708061880141d144900d50040c282401d051076001da6010010b400e005110b08064185030f940d00b004030700100070104842c5100d2961042d154100d4540c89a140c0058081d0541242980303007113001f0804c0302c014800c44000b040b1103540c41d01c01031007806021015000051040b0341d03034058041c1c00a19a2950a6164022a5040c0000d03031a11030f03c00c0014100 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 605544433 1250 605543183 605543189
    0x12040c0906031e03020307060e0a1101020721020604030c0602070e100302090105041a04050c04030605090c01020a0213140103060501031b03020f0402072108090709021e03040302010f0e0106050a 85
    0x1146802410400954010030a000f070344a0001d10b02c04424040c2426811400340110103800d4038100903100403072050100d60b89d84001d10513404203800864a07401203a844160340a0440885c0c2c42044a400f0320b04190511403401c1e200420b078610f01501c9944034004043e0b6039008030003582c01801c0c140301d01040c180c0e280e6070110420741d104c001d00346140c0003c0e0410006110ba580101d66a44101d04a010b85100c861140c5c2006031040c042da060104205913580c0c414401541d40f00e1034040403507a06040480c51005103001640102680e0005800b00039105003400f140711f40469071035050700d41e00c00e2201c103600c0c000c40c000c1a0004241d803441c245440000490072101c001149602c2c41440180d60f003040740511620140c1c0d005880e5591403509590100c0400c042c0c410001c0d00c0e0440440b019403060785103110714084001d0318600c940d03803501c11040c1d001d0b843d500200c6640340c2d01c648141d6410340c0f0143d503200e03029100220300905d6070799041c01100c00140b00111071748d442c1e400c28052420034034503000003 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 605545683 1250 605544433 605544449
    0x1a07080f03010e0115171510020c120102030103020f0913060c050414060c25050909282105040b180307060c0804030f141e06010b03190f020f12040c 65
    0x1440031285c00003001e910341900c8544012412501240044a42110340800000043e0915070340100045000c0d41ea2000340052510544041106a289030018000e03a412650f028010240000507202000700d40c020041242c082c066440042d103003c261b1902580f07407000300b207450761540e4900300f9a0b16407800380d40c4c01c141c40c00f4013010044245503120000c0c0c0e89074068011b01c800380a002015034110308441e41c0d58089580300c0030950500c00211400728114a69407810070032549045003444034a180030306445030244c80c040c01c006800c1d4019050701c00c481e50600e12031500c2460640c0301c0d0003002c001d400401d17800034a21408060080d5904080100030060050f42c1005003221900d0350351410b0511603400010010f00d2002c1b01142046805292a0302c10070644047e5032083c2032104d0901144081c1c00060a070728031480380001070001c124800c0380d010b01e4444501c40441c8040c0d940c0b03080a808070715580300314140e0801c007407a255802d040c0a0a480c00e05002e02d814981007605080602c0a0076400400c2 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 605546933 1250 605545683 605545709
    0x50c2407030219110310020a170601050d06080127021f09030c1403281b0308040b0309010c09150804050a140703050c12030a12060b070b06040c030b0603011a07080f03010e01 76
    0x230815030002e603110601c0c19006407032006a951140101c9140c01400a001081418200d01103050390040d008100d44c0c0d04c110414001c17030300303401020a01020551101a4000280c00d12008011a1075050303010b6087e042c0c10510b000a50701d903911172041a96a0050540c2c01500d901c50019203400c0c01480900386415695000d040c1c2100071442807000304040080200340e9000324841ca803034028206400658100041d20780343ca41c1d541c103481d41a07000312180c4c1200d500c2d022880418600910bc48401e585030751400c410307800c0005405490b5010040c0080c0c5242c40386c1080c00e030000c0d0003103502090110000c00905881c5146140031454140309058103071040b054445e002e441020000203a0349a01502e1400513860980791a8010080020f40c015103240400054080d0074003003005200f40c09441e080d50104145940250218100e60009003401e07400031041004018051000090007106080a9070b4545400000d82e91904540d00500601c03003402008001080a24400c4504500400c55448682 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 605548183 1250 605546933 605546947
    0xb09060108010611210309070e0c0301060309050102091e01030b01080408030a271a0f1003140304121a06011b03030513051009050c240703021911031002 67
    0x70704180700c1400f4032010000350200d0341c2c2d1000b1040000304800030003850100020401503d01e00c44c01d61084481c82c2240c82611000514402e440b00c0f0703244034210240c0d08905590a01e20100c016203a40c03181074030107640070b001c044241d68840300e08800d42900c0410000d5607c201500240a407410041c0c0e06060100d0b9100700004070311803d00300d0b5031242c451540050600c0040f51051507400c0d117070740a00002200000f000e000c2011140303044010070f500300341c1803009998400c04290b10300700407075444400d000420010400107440d4207075604010a001c042d81d0409884040010401c6212401507031000c2e640045016400c01d40e000040c1c0010080c6401010241041d070800c2009040800c010304041c4c2d5900040c0c00501da0301c98494607194010252000901d00003000c0d40a0056403005035414002d44400d18443d241c20407074003000d211012001e10401850714581451078100150990075401941b80c079600e05014805c04640d1940304a141030f20048111f014903103401104141100c1180c8100068 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 605549433 1250 605548183 605548187
    0x20103380612130201230409060e010b0a140c0d051b030c06070c11090711010506060901020a080711090103050a0c0803090108060d03020a1b050108311406010611010b090601 76
    0x80e5806a0345404400140d0784a100481e03407406c901c91164407110007249001d51580a900042c07040301c1d403c240905c002c50f01c800110300103000a110340c200341103080000f09001c40c061510118100741e0650f099041c05020f04250b4100b005403004000017580007e0079040c005c1e080030300d040803240084002c5040103041001c0c1581c900020300f0180600903a040900c00f00200c1584040452902401d001070505000c80d0103000c000080301c030400c4c0d135402c040018601f030901c5c00588889540590090900410540311408280d024490944a50542c05800d010544848030b15600852140b8004c0040c1c0e040341c1030550311100b15800c800b006030010042c0848070380e8444407481c1c0080781183d150600341a145800d91400040700d000500c074084403034000440c112981d01c50000c407442030b00c038080d86070f49440b01000c0b448078103407041404240101d02402c040c41c10724480026144520548842585128a0b1a2920b0426441580024403c1d07095a84420080c002c2040850041e82c2280746810030f2800 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 605550683 1250 605549433 605549467
    0x80f070501050f0c0f0a1a060103090213110d051006090b04030209010e06010c0f030e0102070501170a0c0c170712031e050a1d070303111f05040201033806 68
    0xf142890340c401003425298190140807140500108104460003010759141c210181c0c02c07064410a01e0000d40070028403194028061007002503401072200f40e52980039000c460080404450000304503800b8043d0400c800340d1403051601580248028404036407820708010104450707504080ea8030003080c0004c000603261051441d055403000204185941d48520040356040454900504074409452540c0305058011411440303924080c1c2c2070383c2c031054940d0010740f50102004040b42c034000344003000076141c481540c8003001e548100d1514a84292068580b818040900b81c190070140354001810410000240104681d980304c5090900030b00028a074480490058140c02c600050348a00000c1c01448565024103660680c800d80c20b4030244040c5080ca58900e00c44c0411404141c42e9001d280107844001145210b2414215150780c21300d12658001d0003034007010788104e05240c1c41e44080d0544042000e003624040d0704594000c3e81001c40d02c0030b220340142011094600078001000000034040c01282 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 605551933 1250 605550683 605550697
    0x907021609020f0c031c05150319140d0f03201603030216080301050f030604050a0318030215030906071b0b0c0f0f0c0c040218010f09030c060504080f07050105 70
    0x40140c68000303d403000781040c41825138683c154000054404000b00d00031940050302d8104010400056407605d0306120591101c100d95641759100725041003404411035007929030188240d00342021400003001281c0341441078601800800c4000e1441e21f0440d605200c1e1069089a00100c6502d00600c85201d4816200b003600c0b140380c4000e4462440140340c004d40450f60055a0540e2000080826040c0b42c0d01c103400a00503948205044411541d41d440d001401c0e41c0600e41103c0500001c2095940581e5141e00d4a55103072840c4a2030100000580d49a0f01040c0d65006403403070741550f915040c2002c2d410300200400d20b005002e004090140b51000c02da6480e0440c0b41d200c10f2130700c1c4da520b5034560540390b03010300002154004c03400194075a803400020081d00040c060201140c81e019407034800c2000764007503e07800017811090000300104075803065100b20101e46041c1400050242c0702c0d219103004840540200012813000142004006000c000b54581c400f40b040c080c04409003031400003422880755072 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 605553183 1250 605551933 605551949
    0xd0f09030c031d060301080d0914010503130309090c050307020f0d02030a0e1201150e0a0b0d120c0c141005131a1c050435030a06030c0e040209070216 66
    0x200e01d0f03e16100044480700750782e0300402da55201d40c0d40d00b01c940d6680003030289080002e0032001d0006039446840c0500b1b4400d00c2c0c1611064195035500303860794043e060404c007ea04024003000d000909038294480c08903004683e41d2165a645441000645017501080ca110300d194020038064280300c1c1e003c000c3e64000811860248415401c1c000010040031111018588951808440c2d0304212180b83c3c00004a410310003040c16a03656403110101107035800351810b600007a1060f41e000014800c0c4007984824401401d00758001e00c5a52a4905030001075000b0a8170a080700400c10314520f0720900d031800711041841d01031301d400441d003203900e08a2003602c2100075030f240d40a40440745006210584212201c100c100700c0d0b1410300142214080c16081da0283c1d00c80c0050380c00903800c0c4010f40441507a180c0404d203100240c81d0458145480d541c402480a442c05684400104c0020140340740f00b4014600e800060045003818010440200000341140c800d41d4490040d5980390100000d0034811a0840 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 605554433 1250 605553183 605553197
    0xc070e070c0209072c011116030507120314071a09060a0f02090105040312020a020603100f0f03050303040b06011812050606060a0c08090114120a14011404020c0307050706050d0f09030c03 82
    0x1800061b11300e4002001f2610305402100c2c5064548100c00c150041160701500840784103c0e910144140c46000e007003030140c00506414210000c2035100c1e07004008091240107140000111041034070f01003035050b01c0700911900001e0030701c00190118040c0080d01001904210310382440b260011f04140720714840281401d0614607855001c500902035100f01a0b000f4203140e0343c9240a078080c4000d029203002c0d0b201118582c03900460000c03100300ca0001640e41c020011450f5417201d4032017001442e002050300c1e042020404036103510401601074800106a501c040440000c0b0300d26040d810107100602040c0100400e2161502e80d5501c0107000400d1600000d01c66500d149200040f648040212903110b54080c0018542110300c464164080c450502804100007a002d420514045c2940030312031031040306010507901c0c0d81494194010690489403000b16441e16816640300c030b09082d21a480000070840210f154001990a030260714241005c140040099101075a0040d0034a616900054108510 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 605555683 1250 605554433 605554517
    0x330f1005040b040221040314030402010f0302131a04030303050609090606060d0b0333010e06060a02071706040c0b03010602060103031b0c0f0510080603030d020c070e070c020907 78
    0x111390484051911030410000010080903280c1c4056130b0a807000c40014020f03283c5018040c16040540b40207a50503552555000c40403d030840183d004400540d5400d8090b800c00540d044100d505034995102d603071500b40c0c4961540c1005000c841000303101c14001e8001b0b2040000900b80403504561003003080ba4800c0c1c4070230841d011040204071400e011500362040320302c0124054030403000c04901034030858075070b40361054800410344401c10038410350800e0758000000c11420300c1c0400181c40c06180c4d510440f00d034290750b00301c40119420007651411043d0407071400d01040c820200382c0d0502811301002103034070f9545000d0000355203502c14440a0200082c1400303c410410340d05154161040e04a61000c0c42c00b602d440720070a1000c07042c40b40314032840310001c903000c0181c025a000c511800c0001c001d9070514010b260b0301c202940c0808010299401064400b048800d4210442d074094040355807075040c242507520520042080240c0300c5403e11011906501d5010400c1804000144203480b859a580c24 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 605556933 1250 605555683 605555689
    0x3020d30090314030408040e0610020606010305060d05100203061207060c021302070b0a0c0813031707020708060708040c0501090509070c020f0d05011410050d14330f1005040b 77
    0x1010f0303d00e00155900c004148400e125120303000d0001c1d12810340303401d080c903205e14003001100000c1da201d880150300003400040056029601c810743c86200070340030414040050741e5881c03c1100c2c411000030300c42d038040188a0303241001c0b146120300142003001000040d09010b009081c01c0c0606000034821102c00d07244801da01d00b1a0181d441072580b0104a504038100701040700081d20341e84d04240001000c1a001070400130503480c00d08840c5403d61079034000070300c00300390a45070800c5c0200010103521400100190040007045102c1c820a11540c0d404e401c1c3c24249848144501c150344114104184008140304503541c642030103407c018181004100c18082d4030110340c1c88c1c480f0821682d40254420490400e0050641148402c02c40e02c05000e01260750742c141c0c14542d00140d004043d00100e2180c0c04400013005500c0800d0009000ba04494000c014000d00c60000f07032022050b2000c40c40b403101a1911010712428041e08190919080b072802c3c0f501450759201c286c0035209040c85140c8540828005807 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 605558183 1250 605556933 605556947
    0x40e0f011a16080403050f25032306040b10051504060e041b0e0a090c1b05012012090f120d09020d2f13091a010303020d300903 56
    0x16901c403441c1900c4e95134900f0a02d0300c2d4002e49018400501980440880060448090138682d1246a00310b044840c20342d100c5071003129a4200089804034024100c002c03241c000c01149104601c6070041d029245000c0c881785030b80031103035401680102c4140008850081c03112003542c06684082c61310041d0910810001000b47c81c2d164a209a0500381d0003020508550019907074031840707019100005400d98481440048950140d8104000351100c40c04034080480d140110001c0341c010303400800c40520b020910f40320022041c40e91035100000003241c005a07203005420b00da119083d1405018084203421010b0b4880180801a10b04101c0c000b441c040c900302c0c1c07a4000340605801a02004545c007162038000c0010b100001d9194102805a04c0340350310000301040f04054010140010300d951a6856207000074002c2614212400f055100001c17000c0c0c244d85484500075802540117002d04007a184c00640a04035240c00340c800c403400001c403800f242218101b0703403c81c0d201c04140020a140c0c2030404603240 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 605559433 1250 605558183 605558227
    0x71d09030d18020d05060105030d1d06030613060902070303051303020a0b0a060905130201201504020d051b04060f031a07020715210501120f030e03010c05040e0f011a 73
    0x800101303003c250074444001611810380e0f40c03c0d021107880c0d8042540c25100741e40d8040301340e02000d484500302051402c1400c003a581004000e0000c00500794a80f6000054a109030008100e840e4003041030424180d240c040d10303820082c1060041c001d506691402521100c86100182c40c483e0001c0200c0c0459881c3d601100080503a5801044181489100015900d03100320b4164002090500054400c0c0c9408507440e031802071079070050400b0a00044800e294070b800410a030780c80029120150045201800204040001110f01080c159808002c1108841640d0806100b246030100d00780001307902c0c103c1e140e0b010f0480d5414200e2903a14000100c1c500301454020401d01c100c1c8c04000e107e15500168804a03040d412500807044824104d0448111403092040c51101c115804000d40802c2e00e801c0d9102d007503030080c41c000728149814800b1909442c10074a046000500025040000d01031440f40660854880d03070b4403500c50751500440c4d290211052941849010780040c030300d0701da03041c108001c0c542 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 605560683 1250 605559433 605559439
    0x7140f090906240a290f1204080403020909060402130606020d0804020319121202030f07031d01020f1c02040b03070809580f030f0509071d09030d1802 66
    0x1e2136884545d102c00c000e440045041d0000304030600c0907003d01020003501c0c021140080c2e1b46041102c00240c103a0205c8005d0015607104030b0400c030100143c0c440c044d06500c00c400c808010852814203106010390080602003002c40c85182c140c00f40101540440c1510b441800d40ca00020241c560b400000d04060820b150940b0381d1124000c100101322150032040314040e0103131502460704001003162010b071302c4126420b0529000d044005000103001343d01440f120740d00b00440c0d404520203846610b0072648400215801c0090101c0d1603030442400c00e92540a0090040c1c0550900745488894040d9000141414043c031462074000346000a0400c20607050302e4100540d8103103d40460041114100c510154036041d220b454119000c00f0581500582d110345a50b51300d0701e0a00d2044811581c20741c0c11507415007055107070030f03032800314400501501e800f9040e0134010781010341c84c241c03081960340307900001e107542002d8190030002c5560307020090f103010a040e403c0109a41040c0418440003000d40040254 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 605561933 1250 605560683 605560699
    0x513110f0702120d0306180209010c0201050c030706110409060504091703060d171305180123090c0409060e250c020909010509070b07170a0e0307140f09090624 70
    0x204c0264141c20040c11909000c60710021881c200344800140e1242500310303808213241c2d40301d11005520136802840900c18072000d0b00d050044a58464068811403010f03d81010800308090200000d81d128504c0100f008680422400c00310703a03201c0200703c00558407801d0400e40440000c4440c0c0b281d07a03440103d1030740100c0c00701d04081131b0422403107a500300d25125844d02d00c5400000c83c9a0501c2c842800e1a06282d08543c03400340c2c41c18100d0700e14480c201c45444400080308c03d03171075043c5d26946201c60045804002043d00e0f0342c248203940701190307283c0d84110b08034100380c810310001d000016103034003010700000d00e0039034200b1049001307552140341640000d400030342c1d4508000d406003040d48134500420341c080690f100607540c0c03e0010f03598042c1d1308014048400d0404800e000d54201e0f8018000c03001c807410243d440c115150300103420060701c0da01114070145004810b14280c0741812400c019580122049800c60400320522581d450f40200504217615003042c140524161007038030406603100043c0390704 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 605563183 1250 605561933 605561953
    0x302070c06170105040507120e070510110d03140411220506030607020303190515031c0e030604030c110121090b0f04120f23040513110f070212 63
    0x1000b00c4500c881d04081500d000002082c2842c00d03000b640d02404450760350301d220400209400300108002c5060780c1544c41800400541900c4991540480c9050380d2215100920000301d0a81003011a03400c1c038007050b24154840c581d2003a0301c240346400c16006054910003c1e1108081402801e85041008600c0d45a03800040c8000042e00071a100340d0090382a07079199194840241ea5a01098a010004e4840e5a2030022a803626a00242e8424907071524000c41404407801b003410320b01e45480c070100c602e504500e84640315400a00074503040743c0a400401c07040c40d0030f0710010301681071404020440c2c5c20314000003200780e104011100c107142030042101030300508284044004c02d03030314000701d504041c070100080008107142052407080350440501030410141020890700300c14500b1040c030500c8000c01c0c20110869801c04080b03004c0c59407625481c0c1e62402c0078208050000c1038030845c44a58180300384084511030400a80f1804028810b01c11345520702c600c0010b10b22255203401c500c040c42622015 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 605564433 1250 605563183 605563187
    0x507050a051903020c0a140f06090904060903090f030308060103020f0c1204050a0803090f041d06040602130806060a170309060c0601062007051003020f03040f172104030302070c06 79
    0x1e900c14865000c071400c05c074081e800e10a001e006403141901d0900541010551810300214402c000480104030a2800041100107014810151401c0d1000d40d5910100410150071500b014080d0400407040b011070380c515070b00188002001020141016004562000280384220a50b10031a81d0030041d524106100442594035400c1031041c14071913003404400040081c0040111005a44040d14003036241520074240001390141785104c2041022900041801e50300a10916005038850340004d6540c110601e044080c0d8a0f094010801c0340e0400d0f0280815551019000310131505050141d9694003407907002c0c94258060f1600303181c1c100c4e0f40096030145046000c15001c2c180c4089803914030141c1400e12011440d812000c5600d40a076100e050180300c83d107040e158582c12280c3c1d601e00545048600746d00d18000e6041603604448603241041e81204004800c1c41d07041041030326072030042c18a400450009042440700f00000c240c4000d2401250915120340c044510070ba80100f401014255100f0b00 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 605565683 1250 605564433 605564473
    0x7210c020114040e0a1a0a0306050603160608040204150b040909060509030c030409020c0a0804170609011503170d0c17071407020402090111060108070e09030301050901060507050a05 80
    0x400c03030000b005412014404000c0c00d059800340c480e004140d203155952103141400512100042800c07420224101c07002c0d0f03554000f051006113109040120b0039052400c203051400701820400004144a00400c0c440030340d0003504c00d0707405901142d02180140c40e40c040c03041132051982082040c0c020020700401d1251898108185070741c407800c810041a940c41a00c02c0e1070340a00540707030100c0c1c2c200304000c1100003650b40140c14001c8650058500e528107540d25400c0ca43e00561100441417090b10450a10fa1400e004042c0c0c45001b0700028040100c0480800c21840302500000786900000710380c50f03450122060581e007600c041c9040400807480003c4003e0700710003e0325821500750050783c00185003188101003024150210540d5035050085541c2000060340142141e04e041182101c07140c11561020003200d8001d111040c050708255050001c030980321107000304000e440e94000c1004004980b907140803a4111015441c2403500c0b04c00f10320b412400c02c01000d00180140c4140f5402d808031803240c0e82 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 605566933 1250 605565683 605565707
    0x103110108040f150c090503061003021e0d20040506130f18050a02150c12030c0d0908190804020a050103091401050403081006020d2012030426070807080721 69
    0x660000c000e031f4500c2011394402c4c0850780c1201c0303400008400c000604141c007140d6440c41283c2c201000c440f400e6408075051200c088002d0f03501412032144002d503110113041400030b01c082074505200b40d20748103000c00c0d40720f1588001280302941d070b001c40300198007055004418881c10040c0d00b559907103250030301e269104081c900580c0f0815030101441d4041c07910008603140c950901019043c50118415490480d800c010718015206004000810310303c0918400c4412241c41051240e03248c1007000c519000d48001090014240800c200c2840056562007544200703d803401d20340841e0144040c03810f4503000030b0204000643e503007020140010585c00c20126885068101034000c1d501e640e03190220790b10b416070380802c2c01180e0450003101e6240807040c41c20403052440c030110350301c2c1d12070b1100026481d48219415110b031500c0140070102218030b250b031034412848008000d0306101017034513401c0e464403d00e207004101c03950024030401044154120003080104040c0040324080c0609130284c81031400007 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 605568183 1250 605566933 605566937
    0x2b1419050c0304030c020112060512060708010504060302010c080d060f080a11040902010f110c0d03020c150702031002031e012304060807030f0f0c0609080d03050103110108040f150c 80
    0x20000940715031401c01520300c603607015914650020956001521b804d404600303c3c0040c3c0c1c0e1502c4010448c3d840b46055489194a007200525840c541408002c05540060300620b115605000e03007040940c0e071042c3c031002040d07001040c00d9503801010604c20014403040e4003c010000c18600002141140410b50321a100c2c0104002003443d26840700304012189550b00c000c3c0495041002900002d114402035442e0b0f0700e00070119000c1030744d1000091450019800110011f92005038444181e05001e0040140c1c8050920200d092031910750000362107000350501d150032107a0200001d1680400d604544d1400203c55007241415611003850796480d94103045c1340703403c141e1144000310f05414a0303c1040103c41031580035101860541e079550492180d04c21090b100590b070200c2c0c0c40301003440340070800014034203070300c1d1801154541a241401c241e40091800185483d010041000c10307a1120001c010180074a44103520395208c0c5495000000e09c180c0103051069641140450105554003200c0028130399 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 605569433 1250 605568183 605568191
    0xd0203180f0915010903080f04060e0a03030207031209050d151503111e040f0605130903020d030b040e01050108011512080d0c0203120f01030b0c2b1419 67
    0x340c00e01203820303101c54600d40c00020040c0041c80052071034140c0c1c640400145440e28009a9a440369100da40010a100d03a0301e0200103030400110360403026400404009580c559040d9182d62400ba40361402c0d4400504001d101000e41074002e4440c0b481c07000904802044801e02d080e541c284090150368241c180e05509140c40d81010300d2405654000301260340c41031110181c0b202081c28800d0600b04656100c170743c0c110400c0f090701b03541e0381da008040d040000c10300c00013101407a103820014484203000403100040d283c05101d4002c2640458803041c0481c040c01c0220340b0300d0410010030002d1401a4900b0301c19440d14001080c4880190001d480c0201caa195201090340c44a8041804982c003035402400300c10104200c10b140c5020f908090100941030058a06210403104210104201216112740c100c00080060007004401c0c2210382d040907400d4402400c11a00c0700c640c002c5c04100ca2211040020010721050138018a50000030130341c20140728111441c10016520140f51012840e070755034083c20 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 605570683 1250 605569433 605569477
    0x60702190602032710030b0604050d15110c0304030f0212010213060201050106020c010206010e040204020705060112061d0606090613110c070501140409020f191107350f0d0203 77
    0x1007a00d000210b203c014006500345d09503940a4005040d4000c42c660040070500c800940f81d036074001c2c6100b07454042c02d205c102004035800a0021100c11044120382e000d010701101040ba400001502c0941c2e501211190b13040c0303074a000161141810311030180f00ca40c000a03000412080d00819901255a950024001a42c80c0c0f10141d0b20307512a2940c1c103006a000c84010002d0400440c003081c1c0003400600010f140c002d10303840390f0341441c409800c004900503c401c0300c90200403080c0725500d4950f001428803413030084070111050326914054105445201c400b404035040b5030f50084042011080100d04001c841d0081c0d42d0325460350090250000300d40288040000c155019010380e80d0b04402e03a1b0704a900d8030b810300300140000d4101404640c6200401d201c56008644400d036545a4404551681407040a20008091a00782180c00a600008404009035001c0440300c1c0705d114800c000800f603180f04001110703414a005020b9070442c039a48107403504e50348069004401443c0720b9512540f981d05000d4 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 605571933 1250 605570683 605570737
    0x2030d0509062d0a02030406090902120103290a0c0801080604080405280605090f240703020c1008010e0f01050609010c051014011d041106070219060203 67
    0x90703040c000d6000302c41000300541c4440050300712610050301480380b401200070260280f141380c22015007440941d000003401e00015070404542d07030040a20900035440d2040350003651050003810f100040500807844500c508a0000c1c2c2104c003002001e10800707007201c4c07403c0c02d020b001a0014005e03401c0454105800400c1910001c60724502c21f42d0444603c078542440c0405010034213020745181554495100c610000b842c44100e0701c800104500d503296511180803408101e81c3d154018411481400c00054800c401040d100c1340300c441905418205886040c98101030b4100320020594543c4050000b446d00301e8190090502410785819000c5200302e40c0e6400080c1900c000280620390748248140b043d440310b50301c00c0030700c1c8003c0e41c81a000d0f215940700e44020b04041c0c42d40c0007400200d0030740d514014004902401e01d413485401003c03402d10442d040c80e4aa4250a12101070300138000c0b90001501c00079516154500740d031a00c05181c20038585980e88800039266001126100390b21622400c83e009a09 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 605573183 1250 605571933 605571937
    0x30303020307021f1a0303071208040807050d02070e33011b080304121d0906060d0e0601030302011a0a090906021b010222030809090a0f0f0e0c1014090604090f0902030d05 75
    0x158040a27412a003030000c8010740704400024002c03901031004201c40d40c009a421300c4422010b544a400415400d81401c01c50301003004010003000c1c01c11303180e10203120405445800f42c02d96103031207120142ea02c5004001205d20084c132040e03d021b44c1442c0c0c0200b00230803001c41c00031031296004408000001c42e16480c00c1360030fa0701d030b40b000c1c040a030284481d01c0ba10f4940b00381001d8101c0c05c0141240d181079030450191098407408410718086401c02e60041080c55028020207107080d4034100c960310035000e8107000942c800204d021f95403607140d5031840030741081203541c1151380780d0501d03101e404c16908000114078043d40c84150f81072001e84190b21105002290030528609aa50041806080480072018400500001080c1c480401e444558101400b00b041c0b2400a01d11000b02c0007164220100c0c050078035041c030014909010702c000001c0c2c1108181c0c003004510156001c007141d69510f106c008001442401507400000c103c525040b12079145108075845250550b00c20f40943c0c1602c8024141640d0078 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 605574433 1250 605573183 605573197
    0xf15300c0311030c09011706010803040f090b12030c070911090904030f0221090117010b030c0706270605060d03021b0406080a0803010e0a020a0207030303020307021f1a0303 76
    0x14030a280d4040c400960040c50100c4804000340031a0351882c15000000c1003a40c00f1ba1010150328184100410180e80510101c3e014007456401189000c0c6061900b0310721049511401d0001680c88080307641981d941d042016901441000700c82d103d01103444903d4444a0301c0c45108070052902c150301d01c02850350819a6000040100000c0140d03580380c6054a0681401a014045000709a68410030b510851003a540100b1a00452610317100c0f10740c009015030b90090004441c208100c1d0042010100c0d10044907481490600e40035103074200b078901400a4450740030f0415600480104886d0030220f6284481e175080c1c0514001e201980b00c40050204c1850a040041d0040c0c1101070a1610104c81141d801420100500000344480d40c4807645070030410380f880101c9051000100401c0650f1000304010b0b044000d4110441c82c1000e141c5002e5582c0160f880300506044e004030002d542c070f5000307000405c12200f100b90b0100e00c00c840301031503c00030520500040040d04110b40c421910741000400d450320 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 605575539 1106 605574433 605574443
    0x405100c0306051005070c08070605300f100b0f07030e150306130f0c02070821030c0705030702060c03070204200d0f1530 54
    0x140ca40340c0480008060800b10280803503034079802c0054a000880c100180e541d20b56107400b40f42d000c3c00c1d600c1000d640c0a1002c0003c0e420390004018079170184100c3c1c0140e800a006400010480d0180c0c1c9100703030796002c2c00300040003001c42c1000b0316085036105040c01d41041c0c2c1c55800c104a640708400b4502c0719800440c01d08101a08000203100c070550448504401c0d1040d000880b07164000104528881c601ea43d094001c0c0654503405259a088803040030700c03504140c1c0101035500d8401e442884440d2003801700c048132000881c4070250700da10102503100e185841d4207444842e150002d1405594030301040000b400142d403113000504c00c111405018680301e44035401044210760100f101e101181c0181c050f0810300400c0c44088400c071914003240080e8000c8100aa0802041201544e000401c14000041081342d10805892040701089010740c610314003680030110391501a08000703007 = true := by decide +kernel

theorem cover : BRFrame.Cov 605395683 605575539 := by
  have h0 := BRFrame.cov_init 605395683
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605395683 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605395683 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605395683 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605395683 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605395683 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605395683 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605395683 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605395683 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605395683 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605395683 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605395683 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605395683 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605395683 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605395683 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605395683 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605395683 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605395683 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605395683 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605395683 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605395683 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605395683 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605395683 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605395683 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605395683 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605395683 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605395683 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605395683 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605395683 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605395683 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605395683 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605395683 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605395683 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605395683 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605395683 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605395683 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605395683 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605395683 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605395683 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605395683 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605395683 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605395683 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605395683 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605395683 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605395683 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605395683 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605395683 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605395683 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605395683 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605395683 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605395683 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605395683 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605395683 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605395683 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605395683 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605395683 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605395683 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605395683 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605395683 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605395683 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605395683 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605395683 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605395683 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605395683 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605395683 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605395683 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605395683 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605395683 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605395683 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605395683 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605395683 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605395683 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605395683 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605395683 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605395683 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605395683 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605395683 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605395683 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605395683 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605395683 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605395683 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605395683 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605395683 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605395683 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605395683 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605395683 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605395683 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605395683 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605395683 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605395683 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605395683 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605395683 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605395683 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605395683 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605395683 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605395683 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605395683 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605395683 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605395683 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605395683 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605395683 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605395683 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605395683 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605395683 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605395683 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605395683 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605395683 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605395683 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605395683 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605395683 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605395683 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605395683 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605395683 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605395683 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605395683 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605395683 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605395683 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605395683 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605395683 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605395683 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605395683 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605395683 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605395683 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605395683 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605395683 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605395683 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605395683 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605395683 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605395683 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605395683 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605395683 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605395683 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605395683 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605395683 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605395683 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605395683 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605395683 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605395683 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605395683 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605395683 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605395683 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605395683 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605395683 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605395683 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605395683 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 605395683 ≤ n) (h2 : n < 605575539) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
