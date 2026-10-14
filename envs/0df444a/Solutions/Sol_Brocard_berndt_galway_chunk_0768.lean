-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0768
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T22:40:32.864674+00:00
-- url     : https://prove2.me/submissions/b8d7c9fa-ede0-4c3b-9e6c-6926d6746931

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 137949640 ≤ n < 138129496 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 137950890 1250 137949640 137949649
    0xc08010603030f0201050106080402060708090306090319020c06120c0f032403010510090c090b07060f0506010207180c0306120b010f170601030209130f06200403050316140d02030306 80
    0x2100303642c2117a00d0301004000c15a0b111034650342050f81191455030301c40c2d10341012034050003144181c1d80c1c140508007e1006000c0004010022100803580302c3d4403203648181d0a0b030301d40c032822645070b410040c10446095240c103200c240301e9002c5108a6158240360782014540e0719900112515240d1592052803120070360140c0f0401c5c3d8000e40120020711413403034281d09450303040f01c01e0b104070742c58240c0310030301c45811601840601020300591107609071900344a09100d805009081010320556281c42c000c9403465102140d800d0039a03249204c06801460203c6c81800100003400414041555a11010903030f5001c00d50302d00c040313074001c1c20844450350514a6200302d000d013580c000841214500040050594045101c81c1100d404880080469075042c0d162070040c3d450000080620048100100400c806a8808001603210000d00080103845001031001071040780400b40003607000348186c102000c04a290701c02940d10074507120f955a03c40300390540c40d00305816900740158102000300091401c0 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 137952140 1250 137950890 137950907
    0x20c0f060f0a05061c1707030302091c030f0507051509010c030507020d0903020f030a0f0f0317060603040618150b031006051005031509010f0303030b091b160c0801060303 75
    0x42c00030443c07410441c0025030f90308008402d11113074181041480d414407010950000b8003140072150b40340e40302800e180050013503004019903442080d8180080030500a4074150a00c041c1d45502c950344000c54042058071690040348007281c581c49021000903401d00100708040c0250300d54400810f0b540c05a0a0240c00d90f03c0081c03640045502003800c80340d8040d8028000c40c2103940580700e82c00380d501c0c200042404c250007800040d0515a19001e0702c001c2128030b402d90580e1500036550b465620303841581c600080765042c0d440346c0c5c0c0301e4070030b00110b008201940d01c410520000c0c005103180c403a805950349221361001d0310b20852055501d4045011504041c00045400c16194200300b10880c2880d001034005581181680200200800001c85124400302c41840d41c400040101080e5070b07480c0004080326031203000440000741031503805816030400c640d5040c080c031a01c8404a090760002990140345410010f100102c0c01c2c684041c0f1004545207042003005404e2680000c0f4940c0d040d41006040880b = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 137953390 1250 137952140 137952151
    0x100518030a170a110109230601061707111501081501030f060c14040f0306060605160209130204141e04050309040209040209060d060311060705150604020c0f060f 71
    0x4101e021420001819070304110000094159000d03221001caa908480700d8050f226100d40640c40c2c0302c01ca0701448030b10050505010741e82502c00031020708000c10ba689074407082c807e003c041015034040c000c800100304e40703296104542c1c0c902940540e21841d14945084c0c181d01c1002c0000c8192401800020014401c0d032140729680a0034802c44e524603511000c0d180405e55024001d240d9500024100d94450410076400000c40c041d115229601d80d041040700c1c0400d403004403030035031401000041c1e090040303082c0c40c50040075081c0c00d134589600c2c0c2c0134030003400c0f00184201d00081d1301400e81d1005a8031841100801da01c03619013000d0920300310002d0041604e0f01001500e04045040821000910020031102c540308141c80158031074004c2c0c1c0100e0040d000f02e46c481d85d84001c0100e50034114001d2036200d0001c680c0a10500d4507a0002d040034013061b40719108000d0081c0d044090f0004189569428440e00000c1c0904010324141501d000c0e0f908103104004d210146400c45801e0100115a585216800c032 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 137954640 1250 137953390 137953393
    0x70b0105090c0c03070212120304060f1a010c030e22050901050105060c031602010e09070201020919080a0201030b0d061d060f0106090323031b070b031b03100510051803 74
    0x24243d43c030000daa03070041190003440741c805203014502c04c41c418007135040904c50060b0019100e040518201014100780e00000c60100d1900d4552203080b41440b00b4072841c1324040c0c540b8400000300d910700b161601022018180c0103c504070b6543c00c450a510320402200c81c1035036000a290802c1c1300b0560130742d2810f030f02003841074200384155160b03404080300302e411401c8464004481400340744010380d0403006017a02e4035480100c400030400e4054040d0024076016000b1148000c52054180040322501007600407005d19501040c03074400154045d41c422040c1d000000c000b440c04100c551381c3e25085d0742011401d01c9412200381807071412410100f12550f000500b2044041540d810700d1b0380204850001c4c03001800c6c1070034148000c2410820841009800030b808400e0b60350b103d0000458440103804803060540500c21000b00240f14880d8005582c001c01d0440000d400c04000000103030703a642c2004d4030000c402c1004000010792582d54500301500f40d88903403580c50301c8481c8074400c4181003e0300d8220318083d = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 137955890 1250 137954640 137954647
    0x2030a1407022b06020d0c1e2c1201150614090402070f120905011701030809010f120501120309050405132406120611040e0112060b0402070b0105090c 66
    0x41c0d41c3d04030981e15191090468802540008030a90112400140082e0049200041c00581803441d50440c00c00300e01c241d01c07208112414004c00b40401ca142d805841d0009802004400e8070384012108402c0c4990f10900002400d074172000002e000400d25205861310f42c0d900c1101d0800e00d000c0042c500b000b07003040d04100c8002d0120f2070b0100450700c1408541445560300048840c02c00c02c1e0001840c044503001111070005c12400358001e80762550340d01609011501503074019040391085410300c0d06030303944081e2050030110304400554081641c050700c0c0c400c0c0301e842801c40e00c0c4115140300c0d9034020000d051260042080a040280c550b120071340040707000b142003500308850300c0039503864418800d03400704507850b0f100004001020b4032211100c0e03491078542031103c0041c4640102c80481070503409200100940f0f201507030701c0380b0148a50b1084d1045e003d120b10040040b554000380b040400341c0600c1c4007080a220200c0020100c2c1e2106c2e8044810003440d0300140803500b081900c8641c403405c02e01c040c600c0d = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 137957140 1250 137955890 137955893
    0x3151d180706030908070b1602010506220903091205010f11070b070f050f1305090f0402090708040201090f090903030e0d020c090408040e0403020607030f0c05030a0f0b0a0602030a1407 81
    0x11252a1801804240744e241c210340020041507004032042e02d0b40012156604e400e20144200544000d210741100540c00c2c100482c40b14600810340c0005005241c01c14505065040c5854000d4000c07620254184801000000366031194601c69203c500e1040c000010005207900c903413408c8400d400508080000c0610411002496428595801174014101a8805003241c1e40072102845a0110904100c0d4041613600c03a0420152032803042e100100c0e9080310725074480d50f40d0640510201e40c0691f204101e4000b007101a401104855041801031402914051300c1e0208100541c0300c95121111080d90b50ba421020b059040c820000d52580f500040e00011884440003961610800c040c82d1040003120302107810402d10404580051490140688080c506401c019445150440324440400c2c1003a10350700300c404041c400c28500741065156907085407071380d000800003456615401c01280da44c070503000d045ca6448140c0100188000c0c0d000319605c0c2d02550004108000411011810300c005010800 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 137958390 1250 137957140 137957143
    0x103020108010e100f0602070303030b0612040206030a0b1e0117070207060f020f100624020618030706050c091201020f0f0a0c120e0405090c180703151d18 68
    0x50444007204684410340d1a00d013140d0000e91a80d40c0180c00a0001440000b442d54010031303a48102e0703000703803030401000061806100043c80356a4134007540156410014005242a80c040c50300000c4903400010000c94490104409030000081d002c4001c00c01c0703212042e690380c0401c2508850090002c181280d08010a010b9075680cd58004c00f0b0511000d491100d440e0303842080f1500c600140c070011901d4040d268828040103240d14050441c0035243c81442c105041080b04503828048400d500400c8195121a81040c40290a030020300380790200300841000b142190051601400c142083e00d41d5801048007000309100003140c4880940e40103108000c08001d180f4185c40368001c1c404903440d0340e50715000c8111200303110100010107a0311300781900309543d40e00541c40d01041c1000d8a04000c25201c2034092540e441c0070181c01c65000b0903070500c440380c20884403045500980c660401003502c004131103124614800f00e400c0200040266103505500c140c0c3d581110340c00001c141d100a0f0104081540c1c0ba = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 137959640 1250 137958390 137958407
    0x41109010210050c0d0609020306120a050601031506030827010306120f0203010e1005060406140f0409021309050102120106090605070b071206060e030106080c0a030b060402090402131d01030201 85
    0xd204880c1c1c3e94002810602841c401c40d0b540c044517000400100b41c43d1800d01d00290402e40d4102d0003010a4030007842c01d804002804009540c001d0010580c5a1030341e99885009006000c4240600761210000000105808060700c1c240e01a20181c7c003902e80004030034419408c0d00711307026040500b048010052010041c00d00f400d81908001241040d03151030000c2409050300031010816481240c201c0c079648000340d88294081c01040350188246595050480480b03008030031041d84c002c1007042416407a1806a0201d003002d403000c2c050240c11b00c0b60f0401c510848a1a000540352650005059a0100300120941c3e01514050070542c80d00f606000c0014a20b002e5060014034440c143c40108101d07034080da5000b684903001c0c090904c551500c1e900000c010307408074070150340258204440460810300101e0041700b0f5080252038120803502d543c4845030007400181c00c45801a500b040190159100d500080440310180400c0c020594500018186415028481d40500020760001030005030f9010129 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 137960890 1250 137959640 137959663
    0x8061c060f23010f09050c0301060804020a0504020319060e0405030403030809100617010c0e0f0609011e05120a0204050d060e250602070b130902070c0f030503090411090102 76
    0x30840d041100810080074a940ea07240307041042c40c1c0c0b902400c0c95480100741a68000700300c0304061980e03059003105888040d074603040300100c03e000520403e4442e68415600038001015500d840750380c1e0f0041022030748190380c0e81618004450703894000d2017007406804010180c03921660700714078007074503403e07100e01a038000101001100c6002c03d003040e40c200040c10380036110500030401e290307440301003103602c4c5c80025100c0890f509082460803070a02070b1000f00b1100c6800f03400d4442c9011102c0801403da4032180100c0d0512020516451342107502c85c1440001034a40d840d021340e50f034402400b20301144130081c102c0720a036004000c24800c940365841d80e4018194809000b050f55042022901d0800041100d8100c09001801d00301204046140d5000c08843d01a0291048161607070038543c118428031480c19281500c0b8041004050301c0c82d0300400031507001d8480c0c0341c001521035500f0340da003070740c0c541c03081d52103501c0410030018610707092007081c1c00480903a517070a20303012900c40043c0d1900e0348540e0 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 137962140 1250 137960890 137960903
    0x1208030606040801050c0307030b10020d0f12050c0702010201140403050d05040602070812040209060f010503040813081213050609011d0102010b0d061409060405030403110a030606090c08061c 84
    0x1040041c0c071a03400351006401c90303034024440792604140f440f20942080b2901c40000381081035138410350610f070066541c58945c5030701801e048c861a600035a04841e00c7e20503a0700b04462110007103441503091080500070300d0004041540c802e101d000080c01c2d1406484001110b0032a0000d100c0080d40000484450710003200001c5407513952801c1c40c1000380210103018014000c00514411819820002c20348154801c8540d103d0725241d100078032021001030a40e09011400c200301150119403124042c1c401040b140145000e41f07506e54500c9810124466080710460b080030403440780d115406129a8040c1170f040d19036a00b841b501c040000c08030207030b283c104514510200d045600c035034800c6d084002100341c0940306004481031031800340010240c402209040101b1540490700026005c94028000e6070001e0056041c10f0441d12080d6070801884080e130f1b400504038500000003030807405000010300f181d0348001502c40e0301d02005080c640d40140b50038032031070048a006001045010034003804540005 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 137963390 1250 137962140 137962147
    0x618080d1e09050d05010c140f04060c0503090411040f06020d1d5107030f09030f0b042001050409020f070818030d080c300a0c020c03071208 62
    0x400a8400c04420b403c50741c0c101d10266140e400b800815040b000c1032201301d60b54030401001a0000320000e01030182c82d0503030150100010082c00348600d071070060700340c00b5900707403407504266800003802c41d40d015030304c0201c05901141c20032252160327010f40e20082c0014005808400030760740f0010b100407459071a41d101040300ca0401012500c410040d00d8070500702c0700d00c00c00454a450030305100300c01030065018000c80300c1154900307003180e44181004274550804029082041a54081d0b41c6e4142c580030207420400300c210000042550007407040f0019008820060090070305081816012103904031002c50340142480c654501d991001c12a02240d26814006071520208410800303030340f0800201600c01500070426044003e0f401429001e5400101c080712400d80040d0701c10746004404035100740c1b09110a00108095000c00c00c9421205030590040700e42c99103c400c50107030020b4099030b100c03080940e40c00301d1189080d0100554101c8040440060442c6841d0003841c84400c1e0107004000d26280303011 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 137964640 1250 137963390 137963447
    0x3060306190f0e0709110f070f08070b04120806180a050705090406090e010e1f090c0b07050f06130209010311060c2e091e02060f040618080d 62
    0x140d110301003841c03500b682404215a030050b4166207103c1c6000322200c01c3c1c58614412603140380c1c50200c41c002ca680c50380c1541031104648483e044108444015502da0008000704000a03990001c03040c4114451094007a1103202020006c00d0040020040c5001c0c500000030503561185660300983c1c8400c02240c042000c0d070342c52a08996034080d07041c9860f08641030a401044024032500011804510b40008210010480301d06c107903610408402d0000302e400c070240000e10f0103c140c004003042801044805c40e042d50701d0041825540c00745105480d076400c0309500710700070101401010342051a0703801184102e00d443c1c0000780881010b02c0018061848404114200d443e014155141c145084c0306a0345050443e40401c079000d50f01e83c441c8a81141784021801c6040c40c0351083c0088660021382d44030181a0030140f82041e00ca81c08401c3c0d034044010700041c00f110a4403001071020344072079612801c85010401d4908591111034101410580118001001540c2e10440780c0c070409001c441d4145120514 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 137965890 1250 137964640 137964691
    0x180b091504180f060c0e0105030a09080f03010308090f0406380a0809010507050a0c0b0901110301090b04060b07020603160905090f150d05072304050906041703060306 73
    0xc0401c44010500c40c6a41c0e001d2000e2184403d1003180207500600070021500c10855a400840d00da0b140407030070038808191140346030b0744131070103d9105400c281d213800250a10022142c100743d1080720099000552000b0b039060142c846100214165018050b01b810489005422400b81400c500c008406142c500e494000744210307a168030825450307071940c03003110b00002030450b44111000c010a6081c0710208032030070b05c07400c1110700b026080d80c3c0d44a4004a141da59a40011003d414400c041d900c4124480944070401c0081d0700038140100c0000e41c074000e2809000644c2e4050784800084c00041c0a801c0140e101d85044a0703004584140c021580000342c02c05440d14500794200b80d4018044104005080108170a01800ba4210001403445004408200001065070b0b05008242d03400003071041040c0c010300d41502d25074010240010b00307240441c1c00800c040741e100310348000e0030398410000c1c4406d006069164500c0100040500751861030b080001caa59414041e01915100d141b20a0030b207001c40c01d = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 137967140 1250 137965890 137965901
    0x1b010e0303040f0803090306220b0405101104062322030b040b010938010203040305030d06260a08090111060708160c03020c0418050307050304180b091504 68
    0x440f080c000301c1d119068180c1d607030031161405000740f007000041003140580c0e50740e0300c040202902d10043e14040c5070351003070780101e8041d10450b520300c240c8541d0401d102d454081c80042562441c259070b100c2d0300d021001004011140c2d08003080d0303640c900c2c80e0364421010004580541031000c00303611105549041c9124017020035400901100c40c0c642c180002c1254440181d4103c68a400c010b00803603000c071171108c480690030155496124140f0040c029042d0742d200b0b840c0003094050041d2802c25659458003811680310040f44480c03542d485400344100000f07011013a8482603d030010164694490300d075117070388064090024040c0d050108201d81660321a0743c0320501740741e0010540b031007810000b002811021050700c000101c0e400211216000d00c1c801d84220300e020390590b0044c01c0984c0c44100340001070100340c0d040b1294403160540c14010540c108001e10381144078100139940c0d0351402c0b102541c458042d00c14404410704003644001990f851f600955081020b0351038000c410000b40000800078a0f = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 137968390 1250 137967140 137967149
    0x1e0a1a040c260603010605010908030909041e08120703020921011107050d021b100c0f08131802070c06031a030607020c04050c041a0703030e12030601111b010e030304 73
    0x301402e0480d0030518104821401a0400d400030700041e61148019644103da5014003001544140903500312031a0440c0c9a0b0340150142c03d02051143d0402d02480c030304040e10340240c51141c000641c1c0521600c4488000e030344074681d46000c60400180d1340000352144401145410074145020007131844280030342c820003041c0d43c0e0542040c0d403604a0f01d0890b44640502e425800903008404209061642c40c0400a0481c00000e00e0954208200b0b003040e12a1400200280d0345480d003801c1000018004000078100e03421000c0d10030440d94603100303048181000ea80d050034003003401072204a000131310440307082054170514100450074102000001070801c010541069062050b00c0c00d020445402044c42801940203031802c0c44a03507507410082059110303034031607200c5507140c3c621510060110703e40a03040e543e01c40c1c600801c8401c080c038071043ca441e40d400d54158501200206102c881c1d80c0100d40030400038200805000c000c481394480c0a00d40c4a2001440c0c1030040800c40600d499500340100c1d8040c2 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 137969640 1250 137968390 137968427
    0x40e07050907180f090e0c090115020a0210051e040e010306270b06040b06120106080414010e16050d21020114010305030318120a03020a171e0a1a040c 66
    0x2280e4440c02001301c2012442080c90f5589009036090b03004a0200ea04220004058200031550b440c022202d0030441c7c0b034400000450245009442c0143e072180c00b4610203c110340d07241a1210a690b581501c0d0011000e04005035200801c0104112120408070070b04403500004000f60600800303401c001031b4018210030036210700003034001004100c144030b1102c1c000c001c1568200060b05011043c00018800d90228448005410300100015445104d00316881442840c0c04000f0a072218105420f50701c2000c401c49098002c10f010060140c17006aa40e001071508480c0c5000c0a5560b444448500b6031b045a02c40c6000201c1804d005654000d42000100c0c00b00c0e408045010340e0342e4244192a80c0003524084440e41072408030900c4410001000c0c00117a128101079841c0c040802e0703054000354032800905007071001c4401c660b400742090400c20f52054511100c100c1580094040d410003641d401442c01c0506883c10394482098032286041c140748280581d800261044000703030650b4058020407040c0c100 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 137970890 1250 137969640 137969687
    0xd03020d14070216080d0c08030a020f13050306061c1101020c0a0305070e0601050703140d09060203070c060506120d08191104060e150d2003071d040e07050907 70
    0x10b440d800038003910520a401203810b011900c880c0a180c44503c034040d00400030700000c0c030500225400e0b1000f960020151800107251200d1010080c0e9a608003030781c28489440055020000c81c02c045c812194000c904540300c14200c0390200200130102555640034203840000d00b44004164020071070b030303141203000409200015940e4904140e8031480e50040d80b14005002c0003080495000d5030503110607951544500103084403149020407507800500480c6409038a0361030740004121944011802002c090380d07000c000304024100340040c3e55029201c0c601031001032140440403900030443e00900c80d510b1920021036106c400c10100c0441504e0301c041345052604020600108400300140101d40d02a103515a040300400c04100200029031103109954904008242d44110142d0056240001c0515041c0401520303182501d5241c1044883c1d102061800d01080300c9065130303120f052141503048400b40300081c801041c17261281c04500c5018000d090442c0460307206030154041084140c031030842281c0 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 137972140 1250 137970890 137970901
    0x21f021e0109260a120207020d0b0108060709050a05040b040b04061401081608010e06040e07030b060a05030a020612040515040f0c1707050609060c011802100f020d03020d14 76
    0x821404100712440c07245041c0d0402003c0d07201c1c0c1031100c018402840c403824550550805e58101e1040701044420702c1d400c000842c0140d41e1401030f001a28000e1120501642c14170140e03615000010700b645003408030800e000c01c00781e6522001c80003034403030541d404107030030144c5008075024001c10b134101907120b400d020010990011515040007ca207007680c62498580303d0300c003840102e0703018109450011355140b0061026108240c91942c00c00405000011120301d10004581000702c01e030011103100290704c00380302c0c5915212070f90f038028103011005071400c0000ca074006034442c410007160541e4080c01d400010709204ac00c1c810000c0f404c5484201d4507561409190004100709118400c0707840004441c408150440c5014a15800307111040050266034203060403c2465003105030007a5210508220f4455016002c1c042c02505002c0102c0c2c12000d0f607403910400c9295445c625880041241a8035103490050b80000c1352005104181401a52002e0039502c64010f0114800f40d40300310781140082c0107 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 137973390 1250 137972140 137972143
    0x1206050f070516021903060911040e0102091e0a2303061806131401020c0a11061e0313080f0705010f1109011d0a0b0d0f020403021f021e 60
    0x1881846040c0d400d0310107035a00e00040e152801046031080042c55852940d4006081c0380d41443c000120003808946840d03905e64901040d115840f400300c50805113100d0084150a241c01513101010180000f0740c00e09035110080b881c6001c03070304041c445090300d40080f6240d9484401c940f00c040c03c18074800c004180c85000615080c0c0c02c00301c0c81c07a8001e105007800200007207018044031058800071800b81c001034803405151040595424002d89c0d07032a100585040a1003000d20040c09008906006410310340200d040045140002542c1140120010018a228814004c41e02411605584031403500c03503c80c00c101d06070100302d046005101e46400203122080e094245d014203c1c0350320480003402003c40ca0b41680e0705031924485422000c900038400d600556006800252001410407018604030741d42c00002001f80c00320f0741c400d1000c00d00c006405910b04045000c1c410004202050562078186944d010030720204450800e9201c0c26501d840090f0314900c240802615107107030a10555422480754605c9 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 137974640 1250 137973390 137973401
    0x5090f06040608012d05040f110a09030b0906010e0c070c050634050d05090f0a0b0403141203010303051810050414041103070302031e0906010303080601180911041206 73
    0x141383e09540c481000748404500e03805c9a040044100e02c0c84402850b01081c003002e081805010040d050315500d100004555886c05406034440b5640c0b4440c41620710300b04480d2065014165a02e2a0000001448200381c244403c41d00f10211140603580c0e1459410035080c80c80700790f00260317070040d40050907451071038040700e5101c0003e108900d080d003420700c003000144011002400007042600101d0881002a00a4000c0c060182024201c0440645803600252000d5200d0300807000c0101c01280510501010035103140003010500c008146806e8130070452a21070105200040400c0400100d000030443c0c1000042310480001d803070005030f407019040180040d0824003505490f401c041c1d81001c2c03145014000d441903041e0600b05680b4580b260300c4210040d5000511810341c05010300c201034030105500c0d01440c40b03007482e10040c0a955046280c000d20014019140318100515040c2da0316141c00d4500f078007800c8032a0020005440c0254803120101ca006e5588000758403185200000103002150300318 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 137975890 1250 137974640 137974649
    0xe030709050a0c0f1d13090b01090c02010b0303030f1302131415010504030c0e040c15050702010207050103060b0d05180d020f010608012007050304120f02040c050f0a05090f0604060801 81
    0x1305801600b00303250031555841241c00300240c98512405003099401c2c00520044410342079080400d0f01345507502c81340603a18003a4405980140d03980e502d001c0003a0f0a02c910700350300b0011030140d461400d201000d06030750040540f00c50313074038108031881c141159103104540340d514461602c03e0184a82c40c13940040c00340b604540110500c050341824803400d610038011207007a40c1c0e102003c46a16403c00c069000c40c0303000144100c88542814802142c8403820441c2482d410030950b94681c0e682c012840020b08142840d4130440c149420b1000c2444160441c40a803070440022500014240d42c0d01903004091204425402e182402040340000b0704c558081100e56604100e0002400016900c0002c24221510643c2c070818007040041c2e00c2c00d441c040e00c0d00070080c4501130700403a42055114451090041c401d594100c80c0403401d022101304506260042030790018840c10407505000d12006004640d1180388201d100704030000407041c03151750301c7e40480c00c01100082c2038030703458685450b4090b0031400c1c207009 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 137977140 1250 137975890 137975897
    0x2301031b060201050108030d02070227190216020d03020c040e101a01080103030f0915050306120f12070221010c1803020616030309240b031c0e030709050a0c 69
    0x2000708006005000c0c2c581246d028500461422109485d050000c0d04112400c0ba4032000c00418480e00c0c0321514040c0503a80b2580008100e00c0c03c0520401c054010607000c03010741503006004040040c08141102d002c050780544401c6040e8078585000ca06042000b014a9032003844d100d04105030400009240f00d12070356072902009412901150141a03101c100c44a030700003030340d440049c400a4455070740560381c1120341c20000903c41d125688000058501c120715000110007204200052070005503c0c0c3c0401110f40140c0a00d600f0246c0250301e031800f60840320b000850005190b002c64a903c00e028400214a600f0203288443c4420442d0290401c825207000080c1c41202462007140c004843d40216135000f82003d02d0311581a0990100342d04584085d03007032540e100300680c04900c0b003255403944031500001c101048001e4001c01070441e0100c00c0c82c240a64403076424030100b03021641c2c0ea0641411641405010074042a000038a0501c1d503030495454141460b003886407203035598109101c1d00c8038545 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 137978390 1250 137977140 137977193
    0x510090b04090507062607031b0f0804060203060f0402040b03061f0e010c03030b03160e10060503040f0507120b1e04030210050a060b0a180f0315230103 67
    0x104000660b100d80c04041c1a5401030304081001d81c1c0621502410300c020103083c1008130064501c808800401140c030080444c1d20343e0051910030407180c0070030003446071038285004040b240740c1009240d004014001481c1c1c55000001c00e0b8580d880d0480d001c00c41000410070365031282c45000014654109881c0d9900074040740000d11401100c00f2520440d4410b581d99102d06131081f0310044070390400e60750b41a010705540b041c1c1c1c0034583d2030521042c0c0400d011440f014058900d00200c00402010007070102c040e140003001d082c421640d03c001144d4210f81c02201c0f0305800b0f102410202d00780700036948031030307850060b030880d100401090454041c4507860b90380f00804403000c2401d018211800451b4002c00681200920300303000c4c002980300301d4000311130000000d42203440340b200c100c0c254803208040f000b085285601246550700da200c0c25028080e21520310000b1071440e41c0e1281010012a24003c0541c0c46024008505446a0403404000007420180d015075a42c1e00700f12098052400c0e08061011412 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 137979640 1250 137978390 137978411
    0x16030c0b06030c1e040b0a0b1c020903030d150b03190e01060e07081312020a05300304031205010b0d05090607080117030f03070e03060115020a02100c0501051009 71
    0x4100d0b44810035000c0c2400b209130905294801403103807040546540560b603262440655210304502e540a000c052480390b6452080c541d6040200089040e41da00050041003161800d450100c160340c100f01c000040440c4841103021017031854407a5030044c070414440407082111034800e241011500070311040041001c0000c0812460990750603009080094040c080800d04c514482d4140381c0d4000760070035080410000a684144100c000348658030700681c8051461411721105018076600d00300d041c00d1215881c0016104481e46800959102404100c040001410b06004441c0b42d403041010400c1000b642da112409018903400008004034034074079100008400010010b0b40d0350164110b6200c0c401c070782c2c0c070b417900303030403161440312001704442c0800d00c1603500d0b040f4204042c50250300700340c40b4602c0c980c02038024945030400590008804d017138405445c185035600401d004c0072140d0180e800310300707040d030b08041907500c54910f84006250f50f10301400c0203c01c6d64056805015189488801c0c07050640780e = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 137980890 1250 137979640 137979643
    0x71a040e0a020310170a020609130609021b0606092d010801091203180206090303040506030a050105010f05040b0f030601210506010305060a0308090607021801080105190501151416030c0b0603 84
    0x401440e080c2e40e100d441c41b40058a44000645040c050040030b29030f0070400c0d05040c1c01582c10f140d001c9585640c001c92580d03d400300001214011a0085000305910b18094000a04458001d4200b41d111681d442c0171205000700304400384440c030300501444826507034500d0f005000f060340600c10b49800c401d42074904500381c400d00500d92040321000310240481490b40070800c2550001d00fa855161108000010b00c54403a44061031203203000702400542985000005011044200c480004100080000340b1800030581c059981c60000505c103140c03a83c0d82d400050300d8680c1d8121004140211154406c84203e0b41500507a01c01c020030380c0d061042c1e48940003440350707081480c08018042c0a040c4000b0b115810a10090100240002d000307081d0a80241c0e4400e1002c9001e800c4030070942d44503400c100003a600c41d20f03110400003024100300101e41c50190f84420811001003031408129134000c418850b140000140c803c00a0b81c0002c4412071489860040d00320304007500100c950300e03c1000041c15038a030 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 137982140 1250 137980890 137980919
    0x1030506161407030f02030d0c08011a0306030a0f020301060506070506041208060d080304021c081b1204031e06020a03020d0e1c052104060c0810050102071a040e0a020310 75
    0x2404481e6410180556000d495800f030885c4c1c0d56045200c2400501051010360241500f614800d8030f820005504101b08445010714603400f1025044040050054135100000e030703188056000022408803c21500c002805403480361b008551140d0007081010034450003040d42d602036480303094030100581c40d000040d110310508688003a0b0001c400c84540010889860083d0b82c403600c010140c03511482025401200c000c0d80a509403042e00f400b18030030031086100d4014140c04c03007500000b0085500e40344040e28240c410745c000103100c00b2081e010601114801c0d02e072080020b9100100399280e000b0400010020740044031401c002d1400d03c1e104107048540424104070113800510480e48040c00214261100c0d03000e50020515120707498803c041400000b032105009503c81d880100e000001e000c0028810030016148400031140440d04012983c1c0004a01b006c441880031281070b0f200405021403c940a02c2d80210f03810710b8810204803007030303940398000c511822019108080c070a8541d01400c24041 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 137983390 1250 137982140 137982167
    0xb030f07060c050c0306070c0b100b0d0b01030b040e0c21030307030b03030712050406030b090f06100203070203060414060c0717092d04230a0b03010b090103050616 72
    0x400442007444001d01c10b0115141d0a8020400c80d50101e2404003c24036000382110380400140c4120840d0013041006002c0c107802c81444d40f2445885802d00c00c0303494846c8509440341d42040da0b00d00303a43c11345034020340003911021001401000040043e20300d01d522540e00703012441c4200244598400810350b0340c10340c40c0880a00d50002d5085030350791a070a4000303103c00300a0395418481031107000c0c0050b6002d03942d0920481140da9464880703161a001078140da4aa003040d5101d60440000c12088419000d4a247d00030030071200781203459558a0280d0842c814040e01030740602807042040244900c4600340c801a091360011201207666400e03041c01d9500801c10010041d80501d90072814030a50342015103602240142841c0355002d03100172040c80d050380c40d0010b03000c1e5075014200004031300e010b22070340c8174068400c152034990b140c03000324000708140d005011240c0955501c0441c640c40c0c41c254021004018054950300c41da50b1a418a1617480318110764050350341060640200c02c0d944a14010760551 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 137984640 1250 137983390 137983393
    0x209090a0503090d06090209100e0a0204150e15220501030b090a3219020f16080f0406350105010c0f0c0b0c0f010203060105090918030d0c030b030f 65
    0x1410080070860020325060058488940346e440660241e6a0654080d02861034003298800b151706d800d14410248000805442a95206000c20018943c0480346030240c034240d841d14818102c060b800007804d49408014222403e01e001c80c1e44102c000d0304003050314501032511a850102943ca2004409607400e040b4a1034100d12004041031203c01c0a4101d1110090701103004a107441180d072100c040244090034203214000007005002100408215030120000100429442c00141c0401c0d50158420b03e4814141024034407801001d10120005a80e51414070031000c0d0703039850743d40380300500e451002540380082032076004100440b0340c01154040703000d401280c80390203181e11303180040d00d0001e10f441c4150b8141c1112403d8400003108030462101400441d003003551503218115000e4580084840380d503200e0b81c4100113101c42c42e82c200d800c0c0d5404c40f400712400001c5a03190701c803008459a00c0b100d09800b502c8045049149507810386c100031105481c0e6034042100c8004401010307a19144016940c015 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 137985890 1250 137984640 137984647
    0x90601090b0c0a02060d05071d011d040216080301050a1e1505220602070b0705070e09030d060f0509060f0109060503060303070c0b04080105011d010501051b0a0f0209090a0503 77
    0x80704000c0282c480301101d041502d400351015000f15005074040c81c89515819940c2d020400f81d9030308100903110380440d602c000c032004020306001034146400c100740ca521100c0310780341c0509156101e80440e0303003d503498903103040c1818203403504c915182c00a0182c913104044d9035034045902c012402c05503c103600140c00950400d8a044203900d0140c103601402410450f00300001002030540110b494223010001540110562414400034101807a6801008048000b0021100801d10015025056031101c0c0200c0e8010f4031002d40b02403451007a815480c0303ca070300740b10340001c4801113030006500b1142d0544281280d940c40400300204900551080c40c04a2411041400014414005180e100101270304980c50310007a0f8903012241201580f00500c0300728002404c2c00780b07400a00031070740188500f1140388802c915040020700702030414041c0300d042240200324480341141410145c0322201c2c02005445000d4002c0c1000d00f0300d1207401905234042c5003604d0100700c050f038000802044164002001e9402c = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 137987140 1250 137985890 137985899
    0x10908281b0b0411061305040c020114061c1a090c010c0b041704090e01050a0c0f092d1814010b1c06030203010c02030a03050105030705060301030b0702070b03070302071109060109 79
    0x841401070300c00d460038070340001c041055403106001041d000c003c0e0764031b182d0710a19210412007600c14030501001164140792030101d000c2e82c05900203822000445800002100c140a1400894032500c030140000102071090303484802044001e0340680d9120301942c001c00414001500c1c0c182280000030040201e41000402056400c440340180c0ca0380324103c9440e0640d07500588064540d441450021a59284148030b0001b16034454013504c00f40c542080c00e404007030900050005401c0d44680315070b030b81c001c40760202d610b201143d1200f1182400d68034282002d03101c9203403001110360201003200c8a440c10000c1007102d41030300c100704d0494000b00d80052408810b030025080001c2c04883d02904c1c161113260200059600303002d0f8042191045c0d0003940c40360580c4800900785c6d101030b48024040c6d00700050511940d100c2000700d90542c0d401040e40b07805616101e800320310300412940005030202c0e001c4140640e2035459002400c00500511300101001c0d000c504000151a090710280c0c04900101c50801 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 137988390 1250 137987140 137987153
    0x70f03021803010e01021c060302060405060f16030305090c0d1203020c07090c02010c09150f141225050405061603050c0d0e130e0a0311010908281b 65
    0x81c0c0720380c1007071500700740e0501c022a0a507481c0c20140340a43c1d4020458401881c1c48682d01401000e8600303041c40420715540110b00240301b03901419010303d100190402027403a03140c04903842e082c00070220200301038082c24000c0041034141d803111003034080d08a10034400c0c40c00003003009280360001c91103900c820007510190020741c0890309a0840d805448000034a8402d1031150144030059134001103003100c42e0400003410112075401c41c0c010024a0010784120a610009020300c5400c3d502742440d8510303409201c43c441c1c0c00b48111801e01940c6600030055017040f200c206d000d116040500d8042c0c00c251040094509000341e01a05820807418489840e1b201071811500240034000c0c20240c1c980701440c3c090a003410109203040010841000c90f1617043c2c10030380f0403018140c440d800d04020305c50f2402809501d6901d442d602070200111217507082d180001c00e50051503403a0748035204690301c0202085844441c400b441340d200740300c0e48002081c106070f40101e105180c10400e45462955601c0c0d1380c0d0b500c1 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 137989640 1250 137988390 137988397
    0xe06010e060307090614040b01050a021b0f030d0306080c01020102071e320706050403020607030c02190311030c0901050102060403050a02190602120105150418090203030f130806070f0302 82
    0x5549803183c0c103400254409a441510080e111504244c0040c103000f0092000743d42c44c0058260410800704044005140e0210f20a29000e4503c03c13600f41d194401d000040c407000c45881e14691500520b640003502c80e801d039000c0001c8861541c103507070407500d440005900303c2c050000003170700d680711000c1c0c5c00880e001d00c0006081d4140c403650800d5840d012004c0c040b124a160070721000a03030b0500c2804c02407608402c100050041105145c030b0b5141c98215030114480b402000c07002400e1000c4c03149440110360340c00703850a94581c60020500c5c241d95a900700485a03142082c2420300074020300e0394041c068103200d0346d03880c16690182c0040c03071607807580e99045401e40d100c45003410841c0540030402200d412214501110280070341d07000741e02c13005400181003c04070181e01c443d00c13415000002c0d0203005010015030b000c0700e040c90180180c0e905c03056407020240a030210000e42c14040050b03000d19a030310700710140c10303071004140c07070104440d40300e00140780c0d0b50a06032003003004541a14941344020380701c0d8008 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 137990890 1250 137989640 137989651
    0x120501120224040e070809030423040e120403380901020409150602060a1a06070305040b0f03040c060203070305030c0940021801030509120f0306040f0e06010e 70
    0xc0e00c45032181d810b031801640c0141e0040140141c180381406680f0303500503900c5030080d5440014501d001d2409207541c040710402950b0b80b00701f05007042040000e95907940141d004140741019510b1440d4204020070700c1d68014001110020051003500031a0890441458024032140c2c0c0002448040785010802220380103202002030b640030000480c07a038080f070007480c0e140e0898000d401c40c110b05010780641800401040040404e1401307107034002070800100c0f0560f103c0e0080d42c001c1c1c0d65a80f241022510b031b00c1135405c171030b0a0346000100caa2041064038001e612942c052400440d007580ca5240c1240c6034468020017500250301400818151050b0703000030f240342400105000302c0f40300340702c81c0c0e0f000d51507200c000051101c02c4000110070000c1d810400000050a40004626201c0d807125410804140c0c6828107040550307070000a1000329040040290000e1100c002d180c8401c000303510740026034012141c441c0a2420b0901070b8980325003500508a007030034040c000c0c200b607a00b02010400201c000400 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 137992140 1250 137990890 137990929
    0x9090c08070e040215130308090d0b09030414030d051213020d03020a0302010507020a3503040c0302011d010806090907210c0e010803120a1506020d1205011202 70
    0x4001600e108100070107401440003001140c40c61a083c0104510945c41c611820348198040080f514160310301c0d0f4940382903d6101001e942c40c2c860500c00702d00d8000040800601428521061151091000004d0002c8a5805040854440c0540e09158079030807019510f00200e881840320340780c00c944040086034813001e000c00f001c14080302900010000c840d00da80030343c09078114a40301c0050660a000750b6600281d0f600042c05803001c20741d40c0b4907110750441c40220320f02c1c0800d203038900714900359543c0e00807040e001418192130341000c1c2041c50009145201c100e0103e0302c110078600c1c0e90200d0358044a00100140c5400d40341e45e5a0300284071008400500b040707240d014810000c180e0241c4036100c50300703d8034180c80d180c505000c0380c9490005249150450019410351500420964000000b152500b00600442c91210b8840e03810b99005041d80c0d00199901426050011400c10f42c00181e03040c0903a0250b40d040030410707079072224204076082805540e03206106000703800f0250808003100c0e0300416400c075 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 137993390 1250 137992140 137992163
    0x207090b01120c18080712060906060509010b04090608060c071b080304060c020301060e090a0221030304080d0b040b10180902040b070201080c16020409050c03010509100e160909 78
    0x6080200700d90f40100c5103804150810404900038090100c0ea40103880709400a00c12030381040398003210700e0001c0300c0007000c1e42d458901200400003130340c010b9001040041d04203a61961181c0c81b40e01e613038025006009880341360090003d00c1e8540000c525004189510b601450000c441c0c0b6020390000b000c40c0b00510710390301000c0c0003a1060041000b0030040c02c6540d00e024044c0710501c101425180c06601c00420701c0034903011304c500c0f40710115036544e081d03604407190a208210300c20310144200881c2840e42c1030340004000c11040c02140c00c000c0000c4100d9510030020102d40d20204003c580144900680180b45038103c140f17a240200800e0f03c6110340d199500450b1f81d5500106400d1760300c6500560055100410450110350300002242e801c0170301ca290b22400c0c580245248414040a000003900c03e90f11804001e09000060011703403400000035009001510744900c001e84d80380c081e1444600340300d1920080c1103148501103280000a41d4100030720010500d042c2c5410042d00b62100d007560b2554185 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 137994640 1250 137993390 137993417
    0x30402090a1a0d08070c0f1806030c14030a0804080105070f0f0804061104050607050102070606061706061303020409120e1203030f280903090506091c0624030519030207090b01 77
    0x301c0c0400080ca00c000500c007009051a01000308c00c0c802c0b00440c190781d800d122080c000920404161010341e000a82803486060308400028a0011a408090040440001c021648a5040d042980f14034002c1e1128498080e00301c07401c4500480c6040790000046501c804940007680b9904600c0032201110791450419460740002130320755200da4070881d1981e500144000c2004042d005010007803810b401c1440002060f075140801416008141520402c000109841c0d040d2001d0349180117550090300822850740d030343c5002c00c80d03561200340d0040840c641020118091034008644841001c0c0c0a0295041d5242e40d04910040760b07020340010018404000d0b090560401030710420710740340c414003020596140604015201d0801c5e904524011102007104c60b07240e8607150340c1c3d0002000007510f0700c416a511400c1070700003040b5007110f6420a40c03002d25a1140080e11822090540703020f001030701c100700c05103904071244810a500040158021030400c000860450f804903440e80f4040c10400e10b40c4100 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 137995890 1250 137994640 137994653
    0x100804060b0a0e090625030e01090f060e1203070203070f141504060c0f0e06130b160b090f0601030b18010213080606030d080c0f070b010308030402090a1a0d0807 71
    0x29000303c2070403940c0c40d007080b204407000c000198112450010b140c165130805004841d26108107413502c4d05042d1507600014400310250722801040f500451010b00e0700c5400d2410502601d80c400341c00340c1d05c0c4102c10a034080c1041c2c14040300d00400e0315800441c03605142d0341d1040814111004241d401b20307104031588030700c0380b014000714440d500546c0c00b0b50101d10f020710b031003030466020503481e104100c200d0b00c0d40702005130405017800d0f401c00c00700d840e1611070840c0e0000d88103c0d0300c141c0005021460114122000040000c1400207070351080c00204510f03500c9007291943d81c1c0740710a401007164810001040800c0f60224000e0300041040ca416000ca41c2156600f800d9034040080f44d9009215030000f0007030900700b0b102d5580c00c00303030807000341c580c02410800c010000e90014008000c200742c005003800501d50000d08881d038481e40101e02040a41c0d4a04086c40c090f00300325030580c010340b0700c5000101c800e407041c481d0341041c018041070200345072030440902c5024a540a001c8640d010104140e0010412 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 137997140 1250 137995890 137995909
    0x40302060a050712030b10030e210a02010f05060f040905031e0d05010e061305070507020307030b060108010e10060f110a11030d0201060f05040203060a0f0803090a0b09100804060b 79
    0xe042e100c403903492845181400030074040c98580c0040514164580806603683e2041c2c00c01901c40e8a80420740c2106404124207088640020003032248495820490194554014001001d880d4000b04180301c040c0b105401a14001c40e00030340d200c40b414031000d49601d8a68000301d0058020000c80713050280140031400c11030b108103403011107120b01003030b1003411850500400d400b5050340121607140f4100758005c80c1c20115460301542c002900d0b04d0005907054810030030384074529002822504401da60b07041941e0215401e440c401e00056084001080e8000320324001d07400f4115400300c00340c0d21481c090007141d00e40c410403003600030007410f8102e001d48064204680001d540c000d044180c1199041020585486036444005003964103120041080720030040d182000c0f56002d44003da1b0f02e65034140000c6440403d034004c2c0301220106600030941480c00000350006550a44050301e28a444510129060080c0b0301501e0b408031200030f40011a41c4540003442d0800d10170303440400c0302148180025100300c2c = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 137998390 1250 137997140 137997157
    0x70510030b030a0b0f070c030503070807030e0a030519080403090b09040906020f032e091517030309070b070b0a0c11030a020d081005010806060f0c0102040e15040507020607030902030304030206 85
    0x11601c84c1800305daa400351440c650000303030505000c60020355664000c3d2207800000d222034144840d59000840c0940682c000545500d1140151034002c0d00c503103400340c210380203103a0309480d2040d900f0072810f100340900a0540107039056120682d00a190966049a691011000b960807030388038940701c80000d11500203231507000d503840030803600c80c03400016510500a1604030340c0d220440311b00300d20340c601042840c83e0082d200114070204401038040042070113100c06900402900e241c180100182c040c002c030103180140d8201c3c058458a5544154240207030088040141c00ca05520000c20a6030000d98045001503c981c10450290f12060103581c1c2190230545400c0090b0f040010010003441d44140c006070700003106249a42040d080c4030008003007020042006d1f004143c0001d184180304120000d58049884150003550b54a03245c5120351900706041d669041c01109510004003540f6190049038804c00969000b01115980c0b200b080700a441400000d0307030107000401c00031002d612031000408218 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 137999640 1250 137998390 137998403
    0x90c060309150711010e0714131b05071719081f03060c030b0105120105010804240b0f0306090615130912110d02031e0d05070207030b0a060602070510030b030a 70
    0x100e943c111585c00e407840c440406134940c120f0320040c0b0130b0381502c501000110b6010b5601707807540c0741e1200b002001041d42408050400ca40441e0109241f540304005080844c49074000110304030300503603da0100d01494480480100004450501d00c902c00c86a1650003c900072841000035440c9400048102d06600281d501a03250f00301c403092940c040c0584150b0b4017081c03034003910784841c0c030b42032042000d41806924100290344001c24148450018161071441345403030b801c5010307041c2c09038010040003002c50403402114900140034103440e02007035a900c1001c800e009032009036100c00c80000b441030140300030b03503014215860500756500144502e00a0500c030308440341d01c070510301d0009003015800c2840001c0b15401603005208203a03022096070450203900c02c00c0390400007a0320b03182d06280580d10070780103201d140500300300306540c0c00503401c82103a004111500303035912001c898200781c940d540501f00c0075a000990403c0103044c41901c0c040c0f042401d1900050450414002a041200181003075446 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 138000890 1250 137999640 137999657
    0x5060d0b0f071409010e15041e0305060127090309090e03030a0e070b04060302130b07210201020c07060804051507080414060720070b031303090905090c0603091507 72
    0xc0d83c00031100303007016a1281c07410381041032000c002401e250342c21182c90b000b03403064400745403055810304c2501c0103480700410354030041404080d0052442d11030710003035800344552000005d580c40b56803405d644a400d00c2e20b00c56121b40400222a001c0d0050013021002c00c08184d0b000a03404409100b804d042103802c601031552820910710603001d5504070704008540f40c226450400841980804590403520700e07050240e180c00000c421840140c1242e40203042d007450028a4008101000d0000440d22142903044113038189021070480c201d008500c00b0207016809408207102045c0203600440c0d0244c0305204a0700d5a88840c0c00c1c00801d400c0a0380c250303010807000c50902c000c01010b01e09000070040b40800400240c035040f00010b02d0140001ea01003a2620000c0c9107005202c42444400d014291803040c5503030740c0c107105030520f02400140f0700c191b00040c0e10501c049900b040034000c66010f00040c1005109000c510400c0200662002d8030340ca50500c2a0048400b4140041110b81d11512490311070030003 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 138002140 1250 138000890 138000901
    0xc030709090219080115051e0c0106030303050a14010503030a1b02040e010507020d0c080306010833120105010f140d24060e0712020a0e03070f030606080604031205060d0b0f 76
    0x2600d0044c0c1107044400d0750226012a43c2d82c0c1f20094030503609070240a0703030b41c440300000c000340c0f507229100003402e031542020780100c00d041d05a08801d001b0049003408021088480e0040c041d85070b4207000c1c160749900b007000b20000882c8150003103221503103110b600c0004100607600080071210a0001280d07d6511002004000d0760140824081e141e11b80c00c210b40207400304c1c4d950010a01c0000d010a05000c0c00001090740b08424402c002e4081c40c5a880700001228070041c40c000054540c141580b10709580c85a0a6880d5818060141210301030401002250b0800764180101e51013002d40303542204003801320700e0200341c0170400260f020300d0f4000360080290907500e04109075800d50708001800e401c0503003400301956000e9100c814581c00b01c6001a01c40d000c601088800c2142416102d906201c0c544e030103d51101c034000035030b080b01c2c4100c0082160302c1e59001000d458030750850f005008204048040303428180b4541005a110303000421031004c580d103999aa608601c400e50300c0301c03211220701b010081c = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 138003390 1250 138002140 138002147
    0x3111c060b0a020a02101709010f2409051308040f030302010510060804030c02031204080303010f05010f02060103031b0f0803040b090105011404021c05131209030b0c030709090219 79
    0x9019165041e58245407000032540a5980c201e00a00280580c0c401d030b41c40300d02207105803c02c0002074004c0c2420380c12400c003a5100c6020b403000f1840465054a0241e126183c010240341240b9400003201d0711410882c80c0031040070003000024101c4034060705400340d900000305280010000b41c004059204501c0742182002400c4940040c0341146060400d4401c1c08503c0d040105994080e07890300d451804005640b021030b040c01c0110b94420080c000128001c01c0010340403000d503041e18041355065503081d50318401120544199030150015070086001440868800e0300514546100360000c560a405159070715108051074003401e40b160600401800b0410190106103500488074000074007695041624410fa9501061041880307994001080c40010240c1c0c0c020490f030300c0c1d014104000a203018a50108100c60064085642d07421954907012603d0141c00298144d0b6000100c51001d0743c3ca45240001e5a40058014030500074050000902102c2c140014080881302e0510541108042c0034041d = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 138004640 1250 138003390 138003401
    0x90f021608041505090607021311300106081605090303040f320f1206090319140406030f0f05072105090d0c0c03120923010905090703111c 61
    0x202000800c00c2178030764640d0f4590650b9001c58040395110000700400186800901005115007203003603000c92184030180000c41e444d40c603203e109400c11001c1e641c100504c3c101003403d00803100821280c0c00440d000a0040d00d038207a948200d070030005d01d40300c41c0100180c55500258413280a030000f00900b0701200c000300c2c1d0a4a01e9502003a00361052030034110780c29070340d810060100381c002c05442001c0b5456546003041c1d0a910704103030742a82c0302c60400e0000640c4a5100000714815003060345003004a581c45441490240141c20660a0130941848802c078050841c000700450a103031210451601d8500138800c45002e04056121101b0040c1c054805210300c400c54a0701e041c2030362a2000b001103961000c00e00600c5022646003130742c0107107001d03d480d01000a280e0000b500d006910b4071210003003034204c032020040d09c001103030085000c2503c104120940c10850341c40382c00207201c01130400840c142210200c0d0440d41030308001c07900790301c40d0058240b83e400420040e0300d076080d00390028180461600c1031 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 138005890 1250 138004640 138004679
    0x90105100506130501080703090812060f011713062c010b1903140111071101030614010c021207150c1e03080f04020d080309030d15050109090f02160804 67
    0x49a007000c81001c0408001035052241c4c505210a0030700246d407062081d0701c41c1c40c800343e014001a4031000046a04003c402c41264550300400040f40820580d40c040d03070343d103401c080c81c02d4110b454541c0d13070700240c4000071110601164101d4841c2004c1521840c40c0c5589040c1c880c2031480f110601000c580594207440030b8081582c06400b406004178141c155003841b038420b403a008808502c1d014205409280141010500d040c2c070160042104001c0052010f070340074840e20b0036a018070600e0345038102545080120b41c842d0b40420f8450740e2003801820035500b0341d8000640304080da00890f581d00110f454a009000d0300a000a100b941002e04120203a40301d400005586c25400e600c0d1007042d50b000c1c0c055080900081c2e00070b031040d40050704554a0160103c24682d2040c40781c4c2e103c3c1848014595245c00103c5030220346801d140600400c022000f0010042f00d0059407018909440d180941c00113003080c9128401e1140c08024a15688481c0342d00703d804c20b88a2801c1c1341d656494220800050b4140d501c4 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 138007140 1250 138005890 138005899
    0x30c0512090d27050409050a0c0b03071211070609030e040e0c03060903120420030d030f0f0b0f130603050307030206010612090c0506090f090a05070f020609070608040215030901051005 81
    0x10f01580b40011001c001091300c000f55800110941541001840c03c80c001d10024003100d511400400c038040444041c2d4040c06a41d140d80d4464a6041e409000b99032000314110b580000604c10640443c103990440342149019044c00000c1e486c060300450152078031401c0a601c00e0744100301038001d50400304a042d9021042d04084c43c20050b40300881a0b0710302c1c0103030000c0c1944036440020020350148041002c400d0500404440024001c00000350190028003020441c0b18904520800d40c4109401202181c1d540140215100c2d0440810061000724008001c503401d940c3e00804000614108020302030b01e8001d8000302207940c0340040040c002c071340c1500801882410064614009805004800c054603801c9803080e46500000021420001e0007003580d944c001c0c04001030108030303030160b0301a9014084540c0c0302c03400400413410590b5160070944240c0e005521511003002140e03c40c0c500c040e0002d04c0180b654014500c8403035078031226082520f103054507954a00078071200c0c524000c1705030000c003020348 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 138008390 1250 138007140 138007187
    0x100203040203120307020f0f06150303180118030c0806154c0914060a0e0405040807080c0c030606010809150702010b0411070c06140a030c0512090d 65
    0x501203511601d0700b0801e0071407000f000c0081703066a8020711400c1c840d4081c000c220790303c4003109032000b541c035203054908192052038403010031414140401200d0340c0680c0d19520103810310301e090045030131303280d00c1d1101e0308103004407200800066140c01050005143d000020211405d1119241416415400d04d00e403084a428446e1810300501c00701c06d020003804004a00000340400c6000c5080a8442c00310400f0b40200300140700400350032070b119505613188407110f905a052028140001c3e80303c0d01400d44003060801c1040c00091402e50040703a803040c0f1a14806041840c1580e41c5003064000807500708482e0800f0161400a0504104c010b500c80000d1800003c241001c0284c00d4076101c128002d581d400d0300510000e220303a03000350800506140b01500c20010554400d91400c0c10303801000c1c040301c41c410500c000069041c4605405040c1401e0b50b01326503d404d50110302580200004906041408401c0c400000303801c1c644c0c071449104541d54000703040b205600e000020017800740130000421800550 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 138009640 1250 138008390 138008393
    0x807021c0b0403080901021912060603060f03020402090a030f0804081b01080402010806010c05060c0c100e1c02070b07120206250e0f0d030e030d020c010503041101180b040810020304 80
    0x107954960000d0301802c1460644c1c64902000c4e01910a4024164000007586400f00049900000940c1e59070200d4400f002102c4c0c481c0c8007141514600d105140c150340300c5503400d0000d85040d90051140100051150040b031741d4a998004040d800700790141d4000340042010041c0c40024080c5918000c95400c4140c211141c660018000345000b420180c10071054900150941e4000c0c1c2e01f04111b10b400004071580c9140c0075901140613030103008007086e01d00480401d02070740d03031303ca002d1181100301c2e0401412401010390340a00d00f0882c14800b010440c13040c4440009c1da080e0000052800c54041d054500208a44100103031810b20b01a10b05080442c400700c0d0202c181c060b000d40c040c0e0b064054a807020320703c02c0752000518040100107125500c441c1445c80c4208164102c041c0703442c48001541a0340b11280d1080781a62a0300c040454580482c00400024000600441004c808120141402415014401c04001603d84560015512500c0001c2c0c240075260040085022907900900306520b1031429 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 138010890 1250 138009640 138009653
    0x30507060306120b060301290103420e010902131202150306060912061e0106080c0904090f050703030e06070206041703090637020309100e0d0807021c 66
    0x80d650050843d00a003000f00c4c00b565002c0d0004070140c10880c090301c1ca00c0c07540203401c0420400c1640d00300c9c0400d00d032400328903400400b0105402d00031079507442d070041280ba80c800308108458001c0c500b0b162402c1c103c404101e250070075940364013900020800588441520b0280303400c04078960001070b1184607400a00005030b03030302c550312003200440441581e01d0341c45d0074000c00c140d406904803495000e6008580780f02c0841000030b55922604000e141c0c0d02c48400c60b44c0003060651000c0c024040010050320005015503010401440e10b50070281002481e08910b0312400f4560a410300100c1c2e103500005001c2050652020440c0c2c00341e00f08442485c5009055070000700184a2485078030601d44c42055808200b88060094520b4481c003d4009590780304465000003a1450406031400c100071000c0610006600c2c4071030311180d4400316001035141c000e10f0000c0029140b50100014200310704030040442036201d4001403011984280c1184c2e032241114810440303011100d8a0070341d482c2c400010303035402145e007 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 138012140 1250 138010890 138010919
    0x605090f0d030504050a170106060509100305040c0509040b07120e030d0f06030803090a1202030f0313020f040608030a0e03030712180308070b0901050a2c01020c01050c04030507060306 81
    0x2012503500d14070314214501a1058059a4841640541030703044c00102400e2100d80b8258561400c0f00820071746807160f1080e2803078002c0c000410781005203d604950458042c0d0304c07442d0040d00884240c600e150740c82c4001203207490122021505100c03078000748100160017442c2c0e120071745e40d519814800108403111242c0d50b0b000f04494900519140c2c44040d600380d10a03449103025541180c1b141c8d50701e10b4510320702681c80c03085034400c484c809085d071078200f0b4507480842902c0b81c0300e5a8202c503a1958452030044071190710380360790a90b40102014a10895a680e6109200003031032000041d41c0c0b01c81c2e0248c8046e006000c0303031403414000c2d08104000030000305a4000081c7e0b2010720b08184c3c1340050030b102d94503080030041d08003e00b0868001014418400c01241c424407416801009100d1a03030f46480c5102603821501441d4051a41d40704002e401c0364007594200000402d400c001030905035035040017800c0d00da0035602c400040400140c2030060080901c603030405000581000e01c0400c0c90300d0640e40d100711 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 138013390 1250 138012140 138012169
    0x305030604240603020a08090a030c020402070204140a0509010c050408060c0f0c010216110d05100f0e060f090c011e05070204060305010e06010f1502030304080705010e0f0a0606060509 81
    0x1d64038003100d0681c00b440035200800302040401111210b460303000280096200c51002c9000c40c4803100000d4400b440002d80400240e89603440d071548184550038403010f034100d80c200301d88c01030311015180300d4000c94452603440307100b00500210f0705050a0f0b64403421206e02000710010030204000c00c0c00090710018507160080b00b00031403680e4a4050640302025402650145c03001540002030403002c0011421001c240c05004007440d1021500100810042411800b00100149c01800d5100303802c04940e804a8032401d0b400e4004100b000d250742501c0d0900c941161074030800300a80c014051042010003515200040038208699410030f031f034000007440940b0403031540030010001040004c6449540003003004651240003400101c080300c1803d0345400090044c00b01d0b110468000241d0030075541d1340c40d1454281a005145591519103800416a2041109036910340d01c840300303821900400c004045004441038050641c0100e10b1808100f52245640494100101481005d510b591490b101000c1c03030 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 138014640 1250 138013390 138013399
    0x603012a020c03030d0f0c09080d08100b04080604060f11070b060a050d060e010c021b04051012150b060415050a0c050102131d010f030308040c1a090f0301060303050306 74
    0x10306010004a150010102d5403035014040410000251512a04188907114510030280111a03482c00115a0783c0d02c00d1040b40c000d58401009014403a000d1001d254002e0014046840481d44400798100564450784c8802d02a5100c0c00401007409018810200781e001c2800c07060000b031008003a4150640240a409806410321401240144e81d80c403000c0d038000c05026001019040c0139003804e9009040b070002180b40382d400d040c1c0a010903031010600304003180d42d10500c842c44ca800c103000d202c0104402400750042c0c0902c1140401d801c11400340045443d48034101d2200ca1020345091801690512000c0f607004090a20080c40405003021460030417150900e03089488880214040715030384000f00020300070754070020303075000c0c00e40d1010302503015101480102c81c00c0300071003c1d440c02108404d1041200420149030103100091081d984c1640007030049030181ca569480c2d4070b10400040e02c01340b0001c0c031000c000502c3d0440b07050403d40001d40d6142140200722261a41d02c01404c01c3c8001007103070707109 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 138015890 1250 138014640 138014711
    0x10507140a0c0609060203071b0213020d0605031e0d08010b090103050703020d06230901140402030c040816031e05100c1206120303060f0b0904090206070b0703050f060301 75
    0x5100d002120b005070707009402400000c101c1c0c01d00900940c420740341040090400c0403203540d000881d16040b850242e0141c1a130240303141ea40c1300c0c04029000540d2480c0001e80722880003c40c3d0740c1c00c005400c01d20041c0074819400c1c841c0d071b02c103c2d4031305503c4402000502000c08010048800240b0960b040740c1400c2c20f01003541d583d4030204034000c0c421460000301c07441c54080040ba030900460707825050382c100d6400c03001d026424030040140c801000d1144165000100e40b0041e1542410340145170803403040021141800d460700825810840000c0500c0d0540007648030070024410780710005c000184152159170156909502c40b151030b00700700e041540c00307103445090804415101c0e42c440011440c00310310412040e81c0760b81d401149a411064140d00081c10501c0108800030307084dc2182c11170b0072103000a0324011103903003031102801081805980c070182c1032003000080b4040000283c86405956800551407038589241c000d021000760075203009a1400f40782c10558820212100810064034503199034 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 138017140 1250 138015890 138015907
    0x1080615060306061c050f0106140d0905030909090c01030b0f010f0309150603030503040204050618011406040b03010603020306130c020304090509070801060b03040506011514070302010626010e01050714 89
    0x1113034400c0faa9003920049000d030042070f12100700d50215000c1c2070311700d10145060b43d84900448a071826007111400f9864100001a0321701d40d25801200810b204000b40e13410602c404000991a6400304c1d001c01094215540d081c1580d03074103109400004008031000760b4132400120008001c3c0e2101d543c102c1c1850b580c0d901d0202884242c000401c1c4403030800c0c42c140b00e02030b00c074900106182c0090b90308a010394284400f24a0a2508020b201422201c9800c7c0d1105a86040300700c100f696241500070b80c02000801010900300340d800c0003107019116544015950303041020510003626580f5017031b4183c0e40e14203103080c01e202d079002c01241c08031004040c0104040d01e44444907810022158080e18035580f92180011710049d884000c0c61055005d00305603031041e80d880b26082c10011a8403036440004000141e0303003107000c0115000e04002402880009045900c03203202090003410030a10301c40d41c1011004001d12070400340200010b02205400a0080f800c100b0005440b00e84007480301012124003082050 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 138018390 1250 138017140 138017149
    0x1b09070c060b010c1e0b0f0112030c15060303170f0c030a02070303060807120212060f060913120e190b0a030209120304030b04060e06040213240905090601080615060306 74
    0x10107050700f01715030a04980650b90750314842003080e5404c82d55a0188000500d10042c44480141220411404c3c0c6010007850f0b54100c4025210318000c07501500700c1c4d0000c810102e450310641d40a103200380c80d00084440b018804c102d41440081aa0556114600410544805440507690030aa68950158444030549000c1c0e002c2c1401c0e422944e00d604c00c1c588001801c0c071800c45500210350003990700107560881810425292001100e2400c001406003002c2070480c10702903403c42d405030f07042014111050440d45d0300502d2444000e40b0200041030508010600c0c60001d1403e06500000341c14440140c0c40d00320a180d00380940c1c040002810360201e550070b060f454401c2092154075280080c1c0b581d60380c6034544840030360025501981c410b0b281c001900100328001070440d004540082614294054041c0c2c480c01070f2000e6140107502400c60034008840000d8501003001500071200081010302e0518262882d05105034882c000350340c003007400d000541d040d4003c010301e5140182c4030b20303950742d65210106 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 138019640 1250 138018390 138018407
    0xe1302060d0c0f09030b011202120604060b0f01020705030a08070305041e06031805030d0f0b0307080307110a0302090c0a031404080a08010803040f0b070501060b0a021b09070c060b01 80
    0x40c0d04003100045407520424907602c00c011440d001d454201401078200c41c102c40b103090f140030003820364000344018000210b10110b000b5000744014400f00e800c1068511450602c0c2003690704540c50703600c9078461042071400192180c55420b080c130081055500c1e0000007030340c2c0d41410320060030200f030015221007810b11640c200e4011340b55030f00c040d400d0f041000706100385111451243c2800a4900030038003510b07443c1100d480042c1500040258140307244440008001d10080b58003a0000355507814050301c58509120007402486000b000d142c0725601805c01100701c0c0e060f00000e81c0302d8400002c080c00166120315207035402101061070540ca540440c0015001406000c0080e001807034103508200800000100810010101e0381d10091641da90b40d01140e0340c0d0281e4040d910010f10030560522002481501405d0740c58029000800d405a4840d00210940e0201c0313100360050300030303840f01c15102c00b0025044070b0175882038440101a2800d81c0008081c40100c0c0001005c190b15044c00d68180c4e131103107002 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 138020890 1250 138019640 138019643
    0xb0118140d02030106080d020f06010f0618170123090303040305130515030105120c01020c0607020a03060207140d0e030d0302092101020307020c0306150904080d051e0f0403090e13 79
    0x7041602c1d19070910587e41c02c0200042c030018422851620040c20700032400504940e4501d00321100c00d0b0401c102500c10a0084061200881070210001140d0f10200f032007180f4207000c0c0c0000602140c0001c20345044080d2400581101c5500d103052003101c580010850b9402078042c038000d612001a00c030501140407507030380071560002c8503002041c4505d6880700154122071085804807050001803c0c51900c1345040c46286016800c080001259410301c480107103c503030310050444111175100d0b5641012038010f100203440d000f4440303101291541d410030102e0741040e031500307140403408100c0000036521003c2240c0035042540218200f04140c42c0c2c00304140750380413000c1c2045c03803074401d0f0080c0b50700179002120100018481c2d032090b048103003404a21030303024044040050000301010800c1c0401800090002c680300b000810045034011020300c1400d0150804604107030f503d03801460946040e40d0050503075488046000240b00000c2e8000340680d007111441c20031402c07260380d035042c00b0038a208980030 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 138022140 1250 138020890 138020893
    0x103060f1104050f150408060a060608251101090803090303010303030605180a09140604031106160503010e070216030302100b0103230705040801020a180605090102150a0b1c05010b0118140d0203 85
    0xb03200c9412700319044030040d102281e480108a50b10300000f441c11849003800c542c02107001469005100b0711800550f40c801103075400100d03a040c7c159596801c150300864585240c1e41004c0018420103503d40a1103000344002c075503540342c0f206419044501d200025121041550356540300404100d03514000e8100c5828410070303113101d0b10749820b000c0c0c1200503c8070b0f02010b0b07002d40000250542c24191200c0300c903544a550b80c900b944e007440080500d024018000800754414903090309030340324010a40e10081e5109a000c1c001c8040d41c0c29111065503601d40c903d03414141490304041c64540c000c824a01c800b581405000556100d0700000d490900c50341e0070009895000041001c240760700302c204e4034811940f6004a6a401d0f646803030803581c90290034046401a0080300400b102e009040640a8014400841c002984000d0b100015480b0505140540c561403040da00074040c00400e110b0701500d14428200140c64110580d01c0340c3c11030350380d402003269070402c2c1c600c03000c010f48501101a41c0c9680c00350 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 138023390 1250 138022140 138022153
    0x4090b13020304030314010b0315060d0207050d091502010b1f0c02030d03021213080f180612070e0d08040501050c0111070812010909050a0b06030f060103060f1104050f150408 77
    0x7001000761049000301d40303101c1c050100000b23000191008491203102a08101450b240c62001041001c2d1300401305440c0d0240c0a2101d01c002c180203010019a5101c59258031103c10b00c0c0028a100081e000c0c0010303c01d41e4940050a81e40d81c4400d680d40c2c60000d0050041d4000c2e8160100680e18603410b5030010790540b1403040004d01094040c2d00404107031000000c0002075640b01c01c1501450341300f0050041c8840000c1c441034004001d20005000050201140e45000e1510740001c83c05e10381114550383d2900c5054018031400a0f0045030640c01700070240c4002e081244a030702e40c80c0c194030541c030603d4100000021540440c1d4803e5000c0e810003003055801c0ca503958120704000c403142e04460750181c0000b1501000149000d014401d84044caa401405411004240e4840d6043c841d0010140d54040c025048807091101c81402914007861140000150712240c03c0502400c6130100211208038800420042c402551500c01105442e80100c8401c01e4201030840038005600541c2d0003100d2030310400 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 138024640 1250 138023390 138023393
    0xf171c020c040b061c0908070602070b04060e0d0c0b07021002070c03020103060b130e04030507061803020610031502090a0510050307021006030b15040213090b12060c04090b13020304 80
    0x11078040c016039411503083c0104190141000603c2c840d4400120210140c084515240d82c800d03040741071160b00030480541171010390b84404059038030072541219040c081c1c104120401003030744900e210180c1b901303000300840400900058502c00d89618007902490314040042e020520800c003c0c540000c050006544404c0c0a02e0310003504510383c00224003090400c140030551900d100250f6403008203401d800c4020500d040c610421042010340258104441001000041003160049502411016610011170070403410300038200800503000040411241108101040001a1548802411307030401079a4001c842c0000e540c8890301ea12150700b007282010103d05c1c20307401c0700203148644416001c3e6106440c86144001c1280e0141c0401886910040c1c086505402200d01122020702c02800c01864030403c1300743d140310203905502280e0b08980700c041781c540b282841d94041d5052402d0310014803560504481c4c81c030107401030b4003d10003050341da1403070105280d8820541650311115941d0456813130605 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 138025890 1250 138024640 138024643
    0x150905030306150307021c020c061605070f1202120a050f030406080f10030f0201030b12030d0b0306060109031713030c06020c030f03031609030c06090e09070f171c02 73
    0x1100d0b00c0744211140f9904022040042044a01c205410750182c9510215990101d01b0f0b840000a00401c6108802c10a5440d8640700000c14000f03e580a4941d01000b45213041841c02c0110b4001e6803500318000d9040242100580300b03112015411140314100003403040b141c5141006100c0050b0640c811425020803004001c80284140c4101d651486c41c0f0f03586010701e17040707001020364944005c024140310400c086203640401a82c2a4814903010a50b170308600000760003510f810306400c80c241c000041803500c5104500c40d001100d0815000b41c001c6161480010f49400304911010b08191b000740c0d0780c0c195140081084400400340804012034094032402c04d00a0a1a00d00515015200d606900b200c0c07880c0008a00865001c1c1c1c5008510315900c6400d50210b1071451500d20042c0320b1242c80101c0001c10140009001d4482a650b0001244c42c00f03150441c03145019050070125008440117024a036035100518040e10070081075004024030703078a100c034500039109015500e8400c0040340c50551070750 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 138027140 1250 138025890 138025897
    0x103030c05060a0e060106080a0f060f080c090c0706090503041a0904061712131206020c0c0603150f1c030c050c100206060915030a1b0b07020603060d15090503 70
    0x1c0c0100c0d601a03440310382c0e0000b00c4480b000990016405000104400b030311440510b60f10001080010807440d00745003070f650a8560a801641212040303032814854850100122680030f10100da41e4010303404d1948007502d00e40b08103400503004644603075064013403100801c1120010a030600100503100030030400362409403c289403d42c815070402100240008000301407010305080c240c00340c000c413407032242c41c840c103036005001e1444860038003280010002a00078290104502541000d030351924212102400c20742840581482007100340b003845022544000a0440400e00380c40e5041d03540c2c0b1000024820041e0000104e81c006405481c02e02010b90000118001c58482d50803502c000700c48030300308000034007605004401640118000bc415291443c0800d030000308003c00c0080c0028140c01003070034002c2414056505000724101001078460707644140c070040402e16891400e01c1400d500084aa100c00341000b44202804d640d060306111540d488a1540c00f480e050800c20310b020361500d0358a0f80c0 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 138028390 1250 138027140 138027143
    0x20a080c0f1626031e040507050a0b0304051c091203020102090904060c140a0f1b0602071b0603090b0403210c02010c02060a020304030c031101091b21020105300103030c 74
    0x594080b0384000302c0e03150f201900e000c2c011001e8010010f00404020701494071005000341d4880c414168001070f151185181e450140c010041901c1c0c0c0e915041c10078901d4610078503075004c04a003003842d00b10803240c0e20682c01c03c00e0350030703000e8400302101640c00e04902900a000106030310601090034082001515070040f07600350442c0c1c6403d003180707000040c0c078041409402040c0010917034615807a421944180b6607980d0301420340703518115038022071320340104a80140c6422203503101c003402c5801080c0100603080f00117000900d0184180c0c18980ea030a42e2400e0054002001c0c4002006c40c0d0880207100105ca502002911004203d001d00d03411000340a8001445904098050500441e18546881c002c03680f041d900b41d100d240300348449030703001c0300e00140240c9058465581c1d200c0d06000030781c0300d014154800340707940485420141021044900010861000010f103000c90003d500141d0b0000241c400c40081c1d091580e440302842c0032407031904020484d40503418000a0000700030140c10006102c00d00e0f = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 138029640 1250 138028390 138028433
    0x12090c031f1802061818041115030108070b0d0e0f030d0b090919052a0f010309120809030705060108010c0908120315060c0616030c0201020a080c0f16 66
    0x402070070602d0a201005460080d400a100f040b003015503000050403d051318402610902d1070450340940c00c0c001c00e80170344040341c403960001d0420350186010380c02680b182c460000c08a145514006d0040e58545a5100d10401c108020a61031000026648402d07001003d00041c4c0e445030341910b441c16140e41c0306840c1113190b83c0c80c1c42503e9055044c0507400900c20b030a04401042c09001c9038654000e01600001c04842c0c074402c8010b13000703008170b003117051242034860320a03c40302403003404040204416909502904161038070014030040703601805407812004941c10900b010340c58580001e821441040005411840740c0400050403aa05600480300841103665201c2041e0702e03a0856a16a20340901000d805803051020035208400980500c1400800800040c03a02e04150b000380c3c20800c048a40110014864140c8000d140d0503014020400c18248000c610706409800007030007440002d13005420690b0b010a400f503030960340c0421140c402d01000907030002501589003055103051920307403a2120 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 138030890 1250 138029640 138029651
    0x414070807030e1f050901060321090504050705120603240f06060403020618130614010206090c03121c05010b07060605090105090103020603060406091820010512090c031f 75
    0x40f00815004504400c1005501e00380c2c036030640c0c2138080c0a01501054440d5603401c0000001801c000e01800c03280c0c0045660b000700d00444001400300e00d1141e200318080e900706800c0101003a840400c03a090714031224a40440b540313500001c01e160640002c0550000045084440c8481da98450b8617071041301ca0aaa104150f901c0c038042c480c180c0203030310000b90400f00034008841c01a401200c543c00c2c2c906c014112038203505403221100161652a40030440c1c076402450303e00368035641030240c1984141c1c4103000b03001010080f00403d07600d0003582c4807840c2c00e81e00496095141c0840150000d0800c070854011b101130f5841d1b1000900c00ea00a0384c0032039100780b5102c0001360030700307001c9883c034100d4800a181f081030360f19603004d00009600c02450564060343d03580010400702d02500c19050810351580c2c0e80240030000740b400480e522145007107401d8102c041c40c803a0354681c0e40f02c01210301f18000980c082c0103980303803102038030b1902034841140d0741d05014076030442604002c42216102c42c4c10620741c040c481d = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 138032140 1250 138030890 138030911
    0x30807050f030336060c2209090b060108040804120311060108010506010206070801080606040504140a0c0f0803090a05100c14030310151e050c1203010801050c03160e041407080703 79
    0x20301d00c031000480c2d00440002003d648080001d480e100c140d000b42d1f0005407400c1c000c00500310030035801c641c03a0345a5690302c90082c40846000c6641c01102801d06086c9400c00781c44202d900d00941c41990070745005801c50318101446420007618084c4190112545540c4490403180031304011980f06005208450009481c6842410712504844044010b40744940700c0400384409044000c0c000e541e8040e2231900c81114140400c884400c4a02400326010000d04040440d803405106501000b031540c018000000341c0d9680100500031039108560034200c8084807071091300c40b00c80000001d02100301030707000b04650120100046101d4a07421001140301a00d80440c20311a40c0004419800a031002c07640d1004210802c1901c02c0d44600c604080d41080901d0804500e0116004981000c8910200c010032411400b4003540da002004101001e00350328180b410480d6503c40e41521604001600809410380c0d00c0305d40c0300c40e1030a60000d4036004145801e03400503000460584031000083c2c9001089003 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 138033390 1250 138032140 138032221
    0xc0c040b0d03080a05040c0305030703090801051602060f070e0306012309071d0307090e030408070f06020613021302070f0c061809021b010e100e0115030807050f0303 73
    0x2200d42c0340d1541c08158441e80c000000030070300203004030340e06001041c02201090341080580500e511940e07440000e0750030240010f00750750020b01150720f4044203602c03c842e02c940100340b0b41d0b40020402c0032000c20b80c1d1000c41c1103514056101c10303183c25018820001c500d4000c212201c030100c031061203042d800454440d0500008900446980c4001070f144000c07109080280c4d1400d4280000040c215406280c8804080044444080b01803070b40e0740c0001803c0011440078002d10004115028940340c016240003006134a545e4010103400b4a1320340444642c0440d5580382c00180078501141e01103482c2c048518002c20442c01c034000c00d0b15580039a038000103203688100721001d0f40204224520320320324944a804006500040580c0021203000182d103611541c09200c0d0440d025503410092982da40b07030742042421100e00d20006105a41002041c00c601684d03404540c044a52081c541ca540d904141003040c18907040100c1c01e40d09010001c140f00400c8031100d03a040d1002c0e00300c4540300c034001800041300c = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 138034640 1250 138033390 138033409
    0x10603051b0412150606020a020306011224020c032b0902150f09031501030b01140904030c02010302070209040b061e0f01080711031c0501090b010c0209070c080c0c040b 74
    0x1031090701801c10060000020303103062540c07401c0c0300c0c08100da024000c00301e60b10706886503a0040c03001a8000c400000c00e6107400c01c14140107094100c266000700c801c949070042c1c031356078649420322200b4030a1000c0d0407000ea541c1c101c400c094102003d99444488440d9004030300c40c5603800580101d0324003020a130080380e1901c102031200d58001c0c0604811b0700203d030009000c2e080340c209100811002d014060458405001000c0c801440c516900306a60562030a01844030041c0c0150310018001c4410740501d840c1c07100f50030b4201e505400d20491590703480c1300403000f80c805c014000b508591194244001c000f006810640504800c0741d00720410b1070b00b82d6400464a5005d8003182e886031002d41994215400fa4074640e8102e0050b181007001d8095002c40640365600c03504c1203e4a954440031000840c5805101e40360240c48091014810541200c00081c1004144000a03110381080c02c00720341114010100458115404000c068035400c81c14801170716000c211301130901407414180100940c1c6000c0703405c0d = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 138035890 1250 138034640 138034681
    0x1020309010c121b060e06090f0705010e0d0816023f03210402010f26071b0c05040b09250e040e01050403170c120c16080301060305 58
    0xd180a460142c1c4030350701050324410044050180040c2070b10128500510902c80c41d034007400c00450006c10a00659103130030001010540e0a81009003c1502c60f00045000e4044810034a4645d80403648140000c52800114900070801000051a0200e0000350f40c0c4d6025468022221b854030081043c19044200c0f200d842002185100710a4900d48001c20490664483c014041280c0c00c20f008407404900ea21181c012907030b41102d400042000719a40282c2100410265160030001180e850f410801c9070342c0f00e22080110050610005610b03c1e00c966564224003070841100d041041603414801c0380c07d9000e001707050003207061548004031400c1c5107154a0050740c00c0b90342200307055148180465501c0c601e40080081164000c0d1b9190315655a000c3c400c1c00040c8000001400e0420303180c040c1180c0802c804003d03100110b901040072045914042e02c843c3c0c0d110103110355180c0d8984582c55481e100c4d014603001c04c40700c04c40e085001d02c041d03e80914140e82583e00e042200c1d44603c80e2004503020200070 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 138037140 1250 138035890 138035897
    0x5090f030a02070b1e12010906090209130203070c05060709050312040501021f0608010204031a0a05040506070f09050918070602030403021c03031d030904200901030c0c0b09010b0f0102030901 84
    0x80090494034001440c2400440d030307041604459078404035001c0d90000040396146d510304401132204086500c210390081809842c218a0800b200f030114134000d4001402051503980880090041070140000d0300480c1d6101099540c24a04140c0250211044e0700400f8040d2245140700103000306028111819650b058005041c003040f1501c07040c240350b0114115003402c1d6101c01000a1170907090000d41b000d18070030340850780d207503290028a48090700d0042484c07107628140703070074031000c1000443c8254001146241142800210513401d450422080e403085030081c82700b41c100401010480201d1481e08040d1003078921840c2c3c0d80304102d13503034011400003070741c41244142560403941042e44414501423103800c01242c0c0d80c03615140380ea0041da0340c140b10b0a0715000020340d41020b21381480b40f43d00c1101a1000480d40a8414003101d28500400c0c103100d050554a81450700c001d406100014041c03170380140b100d4280d16040401e03902814454140c11b0040c4c00388003002e0940d40c00801501c421400694 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 138038390 1250 138037140 138037153
    0xd050f0304181503141c0c21090b090f0d0f050d0c0309050423090705190e0406090218040804031208010602030703080a0e010606110d11060f15040c0305090f030a02 72
    0x2166012803103c1c5c86201c20051103400214094043c4a40e0300c0d0f0384010142c1c890580401450400790180c408442040d00c80100300d1002c14001500316109506450304666015200c0e00340c1404288044151040c1c1d6500107041e090031030421a90050440100b4804e00c03d076070740966185416a28013420070b42c008c01003458a8014080386c10300b603100001c903c00f0025441c060391090503a490b41c6100649500c0702c1c03604402001d10407402d01501c00d00c2201d001c1101803001a10384000502d04043c0648010301c619141c42c920403c1d590b5001e0800d00360622440720b05007500300382c0780c401e14a03803140c4821039098031410804000c41d80600c07900d078101e50341500a9032030910260740490340d42c0e800601e40003205984020041c0c00074401d1050402400854480600300b03001d0300f96040c0b9080e1102c5521702000840380d050000710101180c50f941050002480341c400d5120714000d1180c5441c4025510340061401161030801e40d4075802c5a402070422074169009403c54528068882c402c05d00c034003016030700c40c4c0f = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 138039640 1250 138038390 138038393
    0x19110403110612130212030301080d030e03091c0b010501030504021008040c0e0c1e030103110d05150a020403061404030f0c0302030d020f0a0212120c07020d050f0304181503 76
    0x215118540740d0001d040500d004009441030b12020002c0d64500805460300d5142002c41c2040a06445507203220801181158500b800c80c3d0340c4d46084020001c01c0540320050640703d010201300341c03443ca02008001c0344c5205505120f0b900c9070342000ca41510220b00410000130f965001c1e20030a8021a000b031301c18204000640402d803148d64018004490906441d00001040100d0f405003d000320301098105a407400001d0905900312416004004a080200010000106082071260381044151180d5a000a803824802e0821002d10500501d0000310800c00c6201442c03a402030096070312600c802c10032010880688000c90b0001c40d0020085071403580702e9007185001380c00b64002702e4860320449280251400c030240a980000074045c4c170408021800250681c1c05220500071121600f03441401c140c982c0c0d220848085016002c0065000d00141807400d41d101e2071100300001360030034200e406c1c034503107440340a80e02c0d840b5110304ea07072009102550054010b6103025002d10400b03040100301ca91400c5 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 138040890 1250 138039640 138039653
    0x20441030706051602030601080607032009190810020703170628030203010e1005010605070312022a060103021009030c18091a0405070501030507050307030509030c0a080319110403 79
    0xc1324180180c24140d03406001030703a0801000c0e01030920200604400e0403da0405404e4814120b400c580c82e02c940b0443c00c3d131601c062025603641c0300080781c11352029074004078001d070108400d0704041c1c0b05000d25240704e0b078403c202da0001c22132584203070b454405540d004011400c260509540456000803180c4503081c10015910304412000c0002403494406581c0f540007078212075214070228101d0f009002610701c0301c006440f0310740c010100307420b0192900c40e41e550018804107246005031481980411502c0307400003080d807100c0c01c01c2035106890b8240340c0320712207071603840350244400ca210f20080355013201c465101c0c0c0e403074508695200c1c0c0c810f138419092114070034000f4101e660303101120740d9445806000c41c0e644031105501c0018140030109900f06801c040c1c1c1048001d802050500d03050005101c146644101280d0340802103250000c1c2c60780b202800d0303074154480c080d104540d61160304406000e0161500003580100e0141d007506c169404581090341c142c44a142100038004814441003010441 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 138042140 1250 138040890 138040897
    0x3041101030209031f0b01050c060a020304030c0b0a0e0c0102010204060c0204020c0a0204051812090603061903050715081e190e0132040c1202010302044103070605 72
    0x1414058200700d420008030b4501260400c005c8410541e03c100c220221025224000c00d51030286015890068106407640e07035508003074081c40c0b01c80e500100103801c0c588104031442100794840d544900c1410000c9014005d44810070448006000d60201e01070b59600520031a8200c0e462504c40303900000e401c1d02004000d402441e10041c9034041c40134003200607503642c03040324468600d61020388843c4180907a040d14140c2c080d00b1810410404220080c1581da0343d00a499110008455030b8001c40c050741c1c1409010000e50780010b04034440c1200100d0a41101c1706966001d04207a503402c101075445010a100c5ca070310f440d69030342c002082c00000c50130f003400c450f0003c00500c2168070003041c00003002c41c210b800c650900166440113010103000b4482441d500400e510083c4070308200c0c3e00241807544920196141600c107a54008240342c03040310459000e601584d00510034079400c2d48000303445410035018007070b60310700c004814040f1142c1d000d10000e0301c0c11188000c1c0c43c054014107004d414a841910b5590 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 138043390 1250 138042140 138042173
    0x305060118020c0307060c141333021b09100603020a090b0c100612050606010e040f180b1003030f0507060f0203040c050f120a020405181507021002040b0304 69
    0x30b030208404020071004000030100280f0401000540440942c0002c0070050846140d5000c81c030700b080b6040500814802000603140d680241e008100c040c20079004230802e00400c04100b2030003240b262040a500881d0821040d40361000c00021480d00c001006401441110812040714028100740455403180e8042c10810500d0304042001c08e40743d01000703069411126124455a1080c08101400d03611070148200419640059203050f02142c0c1d19591105130003842c40e81004180047c3d80b070340d59079540101030f180380800410821140c0b50b0001c090020300b6807500381c2d8040c0f40320340803401205081c0c1c00d40381101e416581c2d0801c04440d400c0d0031950b9034402c7c0029580c041d03d6801e8044103440900c005c1d130040b441003420004441c5071106018601e004e80300214415101c1d20034025140c400842c00443d2542e0494001031665948180c4502280b07814071441c00714070030294600c016802c6898198090030340b98007101d5004090000e4403059102d14010035901610034000701e400500c40ba1040f00805 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 138044640 1250 138043390 138043439
    0x30209160c200a030804081002070818041104031b06020f0709090f080309030306030c06040602070501030f0609051602010e03190807030e030c01091403190518040527010603050601 79
    0x2100d44001501600707684d0000e403241380001604000c8580100902c41c2c40a5580c0c0044d401d000c0c0503111100341780905520406440200e402c2816165201e921004c811095003000c1038030b0300d46030305002c0780780c0341d8052003011450610807020a00700d00014101307189095500082c130280e41400e05104c081c20100380112100d50f5110150000035080d10f01940c0f15811810065850b07140880030140f900b18603c1031a40100c600700418010168040381c05426220300b0300f40454004400400c8200401d041e501c40d05890b0b1421040c0b00d40c810f9400d190580440c2580d000780403540b090040305880e80700b224920320010610b560500745184c005e060a585c0008141400150400b03e0040641158050012580241d40d00d02c0c0070410821031a10403101090f074040110b0030f000e00c550001c0b960414400540e0107210000c00c28420fa040721820a441a41c4c01910501480c100b01e100c04220031040d92020b021041d6080303400c0810341c01440741d0802c4079003010082200381d10700382103103008658070381520000 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 138045890 1250 138044640 138044693
    0x120312020304200f1302090f0409080405030601060512061c061b140301030c140a1a030609060409110103050a0e06040b01051009080d051b0604060501030209160c 71
    0x25004510241d4800c60203480141c180710880c1441e620391440780c40e082071040500000310151511030519100b500e20b0084001170352228001d001403803860b4407040d4030794020b0030000c8540c10094268040d01c200c070b005a0231201c141c0d882d42004d4480e030098001d00110002c5080000f01545449516000d00441283c030b041300c0d01c00724bc1c03900000d441820840c20001e1202102d9210001d0340f14013070056007183c40054905550540e66010381c0c401141c0306a100203c580d05041400b07548010342a40241011a1000101c00c580c01282401d83c004440d10391003404103030001611401c2c540130340e021440d8000160360b035582503c40154002c0c40b01400d06841180d0714605040d5006080200a0107075000d40300c007620a40c0f52004000080c1c0c3c4411400c0104825000e0410130100000713071400944a080c02c0c42610380107203903080f9100001481e10310483d0300c20310040c03005205c420741c041da060742c1c000d4402e010950380380343c50f4a0030342e0480b0300c5107400101c200c40138502048070f504101c801c2c1c1080c110710301d02 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 138047140 1250 138045890 138045917
    0x106120911060c06041103010e0304030f080405120c040c09030807030309110607030203091011061605070b1305010606031b0302090a05041407030b0306010f09020a12020a090602060f040b011203 85
    0x21190407040c0b8030708099108209010501100806d101c80013032040f4024011011000c00d110345900580c0710080c8170403d490b9010040001d440c09a4000d0403001d04410709007080700010aa4808580e441c1c1c600491400c0b0240f00c10300c0c405d20b1501c0540303400c03044c280e150140b00d035030840c020012040240c40003104c044040d400f66a4900042100c030f0b00941c0203645a1107170000b08410300440164442c1401641c4909000c0311070b000c20300c280d002880c58070740704080b4481c1d4000d4660303101d41e036030040101926201b000651100484008942070191000304030480d1160425002c0b0383c0d0842c0740700e56291865501d2041140300703400030064202c024043c1441e543e61b410108050300c270858882c4103a035418208100030554103105100c0b190101b00c0c01040d4651620340c41141c00305c5c20707000d04011740d6000140299020300070f407030000b8100c0640c41c0c00c5555a00521000b44410403c2c050400117029001c0810701c04000d00107054002c1c4e41248414207943d01c0c0900c1c1a2804c01040811070500401407203400 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 138048390 1250 138047140 138047149
    0x10e09010303120b03121213020307030305160b01090e101406120f0d03271a13050a0b07090b0c03030a0e1603081305030f0a0b13050625080106120911 66
    0x31b041410314020945400005003243c2951100401d21901c02c0640c1c664032006d41da0020741c0204480e05800c00f1941c4164a18583c5090101c00601501c0302172604000036401c40c0e290300000300a54a0400d1380d1509004c02c4c001411f496075841030b420303075072081c0c000f203021864071800b60b16107010340300300300c5100d9205210400c3c142100c642001010030f59035034140901c40d1b0207034240302504c100d000c0744034001da04035520400c61b015418100d00d0300140100014801c6410030305201c10700d540002c01c40e400390007140b40150300010111009070028503080c0c80015051403104c00e5441000e0840d0185003590341d5204c4840003041e0220740c80301148140c64116000f04204441a0301450042179110750702c3c510b8000621000320709500c8580039502150701c0021104c40450304c442d440394000f11f100c40e00e440d0502d001814112081c405010307801411709202d9459580342e501d100040c208501042d0a100410003521108801d2052001050202e004c1d5541c10040c0d901501101d8400c51900303051005660119 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 138049640 1250 138048390 138048403
    0x2070801140a0b06040f1a0d050f01090e0307020d0b071e03050a0b01170708180d11010b0901030209040b04150204030f0c1a04030213110a020318010e09010303120b03 73
    0x802207400e1002403040d00070550264030148002581d840d46001c1c504001200e0380c02040c4034510290441500c110780e05000981102c440a020400501103818101c1051154090030700c103503080d0b60700c0c11800300d820540100959000d03c0d0010850340c0e600341d036505d5400c4000c0c4000e011000300541180c17000781e00f0603101c00c095640007142d50005210b00d07051000400b1182d010401c0303030620045200c0b10245001030b103440c9a0110441c5000b5985851307000c0b42c180d2826140c0f04102e2113000e81d018070814150720441a1050084000081c0540304044040c002441030a000c06500010b1900016001c00d14106003a03410601c41c616a001c0741791070305c41d01812600160812a124010400008107000003040800c02500ca00c816041410b0341202e890300b240d1042e07100090180c107004900c1c580720100f0b917021400b207441d0000541d07916209901c0c001c0d2a540040b40de02c1300e1080d00c14041215520801c2c003a0000c000103000d405403032f4295102500c02140e483c2c4150717801600d411a03000c0700d403000d2000 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 138050890 1250 138049640 138049661
    0x50405030f030906040b0f0f1f0f060302181504030f1110080103050d020601050a061805040203070306031401020301060c0609050a0c0e1b0306030309100210020708090111010c091502070801 83
    0x5130045003414a80b004112002500c0020014054020320000d24450320b01b03160002c00342542244181c00000c0304005100c0103600007000c1e117030403a00014075650144c008105034502e1821142500c10b54204201560740020f2030341d0800d240a00060000501d07040e01880400d005240d20302c01c2c06041000204032420300c0d440400006c0741c29004004000007004040c00e01c04140c000341980d903040501141c3c002446105400c1000142c003410881c1d0210030100e14080c0601600c00e41d581d1902c2140600a88203e00c000c4070882620286084c03440d5040c42a28103941c0f071551650003a2a4070f440d100c0140020400541e11402280510344c0040c010010440c01801c01310f078420310a1420705035014425034006982840407401300304200c6d03180c0e4080300315200e451007200e11205203041076200302d1500c04400b0280718094400180e40c0b00b4000c0c4031001d80300d0a4800d80e01d080d68a035501c02c0441c00d03524641c0c0c2c8103011454203801442035070245504195100e240f84120303400943d4903040136081d00c0c801e600 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 138052140 1250 138050890 138050893
    0x30301030807030e1f0513032f0607030e0910050d05010c0207060309080714070f0815160503060907050c0a03081807060503070302130506040b1c1a04050405030f0309 73
    0x910354100b540082e015613000e203007203c001492003068814421031098054041e4108000041c10b845100da0309550075000d1600076451903000303100f030b0450303020701e020040604641c146207096100701498404c046600c0c40c2c2e419681d000407200140c092190780d40014210f080c0413540410040f50350380390542042541409040085008201184068140103080d0040000c15061150441c0418040c5044650607a440816081211280001c1904204032a00545801c2d02d05a8002400e8000000c020302500a40007840c00161a80385581c0844151400010041042400022014174104110315030000450420720300e4403039000ca040c0d080410000040b8003007420003082c00b280724822100500a500c03086c00405441e8200040503149010081c039280c201074001500801e115228414107000340806042d06c1d44071a02c5416125942d0444010341103110b1a607080d0252215443c000c03240941030494400200e104032030309100241c90001d00c00e41c1c0c01d00c41008803004d180740650041d44206d10040 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 138053390 1250 138052140 138052147
    0x7030228080604020f070b0c0c0f03130e01140609040b0306011e08010903200a0203072303160506070305040e0c04030b1b0901031e050106050301050a06020a05100213080303010308 79
    0x5401a11407400506114000c03032040c00507070090661842103886040d04003402d5146030340d039129001715a200b5040525858024600703a000d8128000000d44074900289408602e190340b2000046244c4009104d481201d4150640c26038175410301d40018042c4400142000c1010341d903e1010914214081e40104841401d060012030310454545840c4090042d440007802175081e40c0e140201ba003841540003004200100d43c0c0c10521010820107010081c0c0d026003a142025590081c0010f01e0164620b1146c50402100c00c40d0000d2a001c100c40c400005401e03d13900b9500d080c54240125034002c184d0480a00100b00404180f809840780050703c125086134010707030355504615210492880281080ca1800109034420070192045070540310181001c1c6800215240080c415612881c0f1368200d240c105407900e0004145290f02100035070582c8d074245c450f4240d035503882204999031900950041c0003a00440d0040602c084185c00800c2c14110318400c038500d4070703112101c890070b50b48280d004850545000 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 138054640 1250 138053390 138053467
    0x30219180909051203310606080f120c101e1104060503040f0204060306090302060709060e0d06050907050a060c030201061a2a0d0305010513020a1403070302 69
    0x216552809040024402d0001c030115a4880380d80c0e040c80d41c01300c0503140f0040006a14020440c48202c40e620240003150709032148015080840c0010b01d0064905074144100490410f10010b145055042e072240244100d4666448021803500410704000c540c2c0100b4130f034142016102d0180d010451103411210065a0b103001110088607410981602c4040c024401000115042420789611942011302e0100c03480c0d491000400422885c1c00040c00c03a450301d08207071300b0b1644c0015201d2040041d9281c0c5244140c0303589058520801d88581d0580c07100520741c50704001401342d003050740c10010301c4086403981525200043c06540c00f580240c0c0000d014848460181982405010020701c0c2d012424045505c90340d2091030107100d0f0040313604051a00c081103e00f0106241442d8450003800d00a4481210705414010080e01081c441c091043d007100714001081c40740c0e482113508002d81512000f4003091941d5500380030384c000500800034141e0900c024030454143d403140110102940041d114240d651 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 138055890 1250 138054640 138054677
    0xe090408370f050a143006030c0f060d09020d081804050106050d1e0608070501140309030406080714030a0507030e0c0a12060f0e0705030f0a051c030219 67
    0x841d441004205503041c84031440340d0001c04641000f4224030300007000b0410401645020320862210b600140558100c01c035000c40c3d00561480701c10111204c90342e19868010805544d11701c1d15034031543c44064901e64003140e1400380e0080c2000d0403040401b142d00007440d00012281442e006060703034460b20000d1001180f44c040380c10100d03002c6c0c00301d0303040000d941041e200400c1401011034440c09141d5428100d03507100500300c42201d107000e00820a02c09640c64044881c0c0780c0c002c3c1e1060301d000c200110b01814803019020281e9125559a40003981000d00c0c02008032503611014002009002409156100d540c141200840c07044000f8200410b81e0306000034018125100c2c400d42c1265900590422800ba0303407011034160803038910402c00034070b0041c03a0800c007000308207120210122602d402d4921480b541c0100d44141202c3c400c5040d145038010034220141c841105000050150700303c0605907000005082d203980002000d4680141801208804c01107490041240000030501646030038000016 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 138057140 1250 138055890 138055987
    0x703050312100909030c0b0c0c0106230904080d0c050c0f030702120a020d11040e03210c03130618050a0606030c0801060605030c0906070b1501031503030e090408 71
    0x21110f0704121032810b80e10300406c1c4140001d40281702e000200003144101240e441a0740c420b850390700081005035981c488030610718203003081d4255200280312500c0750524101d03e10501c04c0d5000b0b03001030329010928401c0001004030406010030300009005060207200304126003000961071100450340c80489004200f060058260448215840030217118016151140310102c1e06510560b421400895180041c01420881e4405003542c4800b01e0450010201a084640d8a0028000040d020740719605d003562244004c40d90b220101b00c9440540703001865a5000c400d4404100d140d4a030444001e54460742040b08488080c0d5440c1e484d401d080c1f05100041608000514180c03008000c0103140a201820500009141556004001c02c0006290710b031001120b4483d94852015501e40c68910a012884100c2882980c0024a0320120600355010740d44410150380c1c044c2c4508a81020301c00070401180c01c024011144900284030007100e40c0d00c81c3da840c106d07229081d401d10000000d41d20351100102c5 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 138058390 1250 138057140 138057149
    0x408031f030201020c0907020c030a03210c1d0d0c03060f05070806030c120f0706081b04061704031e2109120c030309052a030d05030a02070203070305031210 69
    0x854032000c10060380c00050b00003103e8800e4030048120764541d00b0903070419425001c801d17003502940000c80d00b01540300400720580004800300080018440c0065400c8801c543c2141010420034441c01c1e00c0c1400110401100900c001d0102c101e80c025030313480c07441601036070313108540640d00c5e89a141c0c01c0301e2050061551000c580d06e000f0b50340c0c0c030b00b040000b5681c03c001c4500358054841c440782010444400e00603440d8403080ca100701c0b01001e50707a400c024000d0204844041200c49502c1c02c0c3c001003503190040381c00301c0701f082d0340340760030741e02c4124021204090180c03049007446191019480000031460b005401c1a1403611800d2241400d180060040b80303662800c0c0a18520380904200010b8040c00c0070058045945048030000021345000d500030054220040c1c00b502c60350030085241412400121102c8401034081c240c900d400c00f0900d40c0e191a1030320580301203041400080c425021701c0d80503150541c0010111565140d513612400d0450b4070400003030030800f00780c1040040b02901c1d4040c0300c0090 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 138059640 1250 138058390 138058441
    0x100c020c04050f060409050111070302030405010f05090d0b090307051c09140901090908070506040501090c051f031e050a0632010f0309060c020c0a320a030803040803 73
    0x1840d04481c43c50164200400c2c041c481d95881c00400c042c800258014403c43c1c844520b06680c03200e10b070401a540303030400e20589001503522a00d600070a8455801d817418103178003170020346034103100b5980c0d031864810040410015100c00d200031310108a04026903200260b4501c02040390b100300041c010b14011581d0405a00d55001c12401103054882c1a2040c3c1100c0305e100c400681c0b0885864170072035511803902e02a12030700c61301d4213010a100041d840300398003078401c2242e0080345a58500b480110002c0d2128510311008014070703164058040d030081003895009040141c0e030520041600400c641090b60b032a1001607076200c081c040d00700c4107408440106041441c07071446406a401100016070b80d001114104450003001c000c2c46802500880200e42c0e01c25402d000052071801e000350746101c480069403050300e81e5100040c0c1c40c40386e410142c9540d420709000060300c0444a040480a4900d440d00980200d141a00000403d40c0c40004c3c500540c85041e090781e8038207201e4800c6141001403a40d600a1 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 138060890 1250 138059640 138059651
    0xf130f0e010b0d0b04020a0506070c21120f02031606020301080708010b03210d02030103030503090d0504060207060804020303070c0b0304140d090603050402120d120612030c0b090708100c020c04 85
    0xb070f03903599440041c000da1101d43c000389542d4134400b091b4510844e52280380c0200c0e000c2803080800c490600d040095840d09100035055014180c800e06c9103152041014052031407400e00058040d1042d0203442005406004032440d00306102070701102020021401c2e1002c503804401480f018001784030203c02010320b00024032140d40b14030700081d241c143c41100c50224462681d80104200071213019100c004681006c115180e6940e4200030f440d640c8200c07a00b403024000d041c2d038604158081c0c4262016100550300070440c550802006640303440015000340d92612003402400006484c04e0100405045040c048540320b0910340703005190481c100d02515400e803c1004144446688120344200311340701c500c1d000c00c85807140e00104a5a1102048a0805010713040d194801c2c0c81e000135540418900700202080f1380d503602c100ba80c4c2d00d0041e480000703000406040070007020036a9905401d42107074a007001c2ea040319995104481c80c00c440248507201194503003c1c2100110b80500034107881d400151414040d = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 138062140 1250 138060890 138060911
    0x20f0c0a1a032203050a030b01110309060d0906180213020f0a0813020909010209150301030b01090b12010606091815090f0603020303070c080c0117070e0f130f0e01 72
    0x5403080001c1c4280e03240080400002d0b40e50f25501c103604200703105030b144400301e00401e0800a155a2044100c90042401c0ca0500d803000d510030504c120a64607604065401c01c002c15041008660008070407129860301c4413540700206045108d0708946c602c61140c50804890244188000c0d0742102d410b0781c0c003051060101d071701c02c4000d41c0304842000b000e6241581895503003090039000e03c006040c000c0d4000542d10100655050154003e00c2e4401c0103c40f2010445e0803000f00305c0540c882404001d040d08a044010490a80140c000703400a510080460300c4100000d01c00b00c0c03c454040d8004800284402010007600408440141c00231034900e900b0b00444000d81b444521064031441800c00081d81c1e1006040700c981140d00007005160700400b075030f07519400382c240f81c603443d0000e001d0407076280100c44100300ca540c0511904c240c600c444008044c1c20b80d848a2090751a2550b01c18901e07041070810300855040d40e141c210070303115840c40c2c4000045a00301000c0302411110341c6801c06119030301d440c003003d2 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 138063390 1250 138062140 138062159
    0x60a050d110d090b010512030a020304030b220302010605010e1f0f03020417030c070806010e04150b0402040b18120a080d0e061e0c030103240e030a020f0c0a 69
    0x2050803090342800720350040e0703810800810348607030001e98116520f8280310608101030156401d040b11801c0310b01940c008811408180c50f4424064044c000d640f080004000040158540650013039210101043c210303042040b200c15240d5050040300146d40d0790f282444103680104121010601c10380e40310301b2810689804008a0200b0741000e8207001c03900d03a2609601c0c0c40307034046a010f0300781e44880104205070320303000e03d40d281c101c0040c41d0120700580d41c000c07880c40400190359041300c102801060741c0792284d07110100181038080c00800720541b00e20030b580141c0c5650000b400103010902000707607180c51a241d01441b0448640c51648585400300402000c02c50002c0d40c103480c603400c054156541d4006070840700c0203060824060409008007801c00c00519007061100e440c8140003001c5c0314290340d0b82c2507402c0b6603100c24003000f40740b21140000950300110f06031251000600c101000108110404125451500403180980050780301110741000341c030741400114921031040d214110003d0404061a = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 138064640 1250 138063390 138063397
    0x50d0f0b0a110307120f022d0a02071e05030d0c02091e011802040e0c0705060702010c0f030209060d0f0f0c02150a0207051203010305010218030604110108060409020a080a02010e060a05 81
    0x8100300624020b00c101d000c141e5501c006000b10b0200c104669500c418840814083c0502308144130b055411141e603a821004c2030704a840c0400680e01a00c145818a500810007030740d00d4803c00d00c01840c80320701080944080014020302d101e1501d442454165520405c58072800007090b101c2c150700c202c80d52002450740c0c030304194150380035501c01030210400749003400020301595220901039a86403040c404490b411000908409004009507601c60741e0300c40081c0c0c2a680ad080d4903000180800c456180a288130790301034440140d006000525103200c03a203041d0180c03800b07130020748811580c4013102e806580003845110002c01c0140040c24a0740c0800f4507030007104500034042d07402a900018003504208c81485003400006407402d0392501c84d6100d041c424000d41050426540d000c1d801180c8541c2444c000810502c81c1d039011514514403404030004540c07552020305580d420544881401c0016524680600c002d0000c1c0300c0144070001040c00010001400d44030010f025071001c0050307401c400e6004048 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 138065890 1250 138064640 138064651
    0x616080c1015080c0f06090411030a05040317101413020a0807020c1005040504020705072103091719030311070510140105090414070e0f0f01050108070504140307050d0f0b0a1103 78
    0x15103171901d41f1040464003909040307581ca0341c40c0c807000041100742e58080d40114001c80c000c2c0e40700c1040d030b050b00800d05244107084c1c0e1980300c0c1c21907003001000002011000184082c8024003407030440f007105100320051f41c004410450200d40390400b0411b400e0b6040081803d102c00407104080e815000000142451096006513409242c0014203c1d0521200f080340704020010aa1843e8082c01403030901c0541d9440003a0450020302e125000040c40c080300c6055400014550300a0074919518003046014401090300880030705440e0040740d1072041d0b40c0c034007504115020703c0160005d04002c20f660b8041f40c21394030100101d910b411005005c140c4074004425071165210004501c14001c0c40503941c42d0008591095088250ba6402c1000b2401100803242c06604c20310012038859132110010b6840d0601101e0b24400910140010441150070b00c400032124207000d03056130012501c2d14085220f08844c078106940082c42c980a04007002200342c8a15401101e450042201c1c403e6441c650035030b48009800c = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 138067140 1250 138065890 138065899
    0x15060a091205012703090b032203120e0c090a05010b07081326010507020708030a1b080703050705060a09020a050108190f0b040b09060616080c1015080c0f 68
    0x200000708002548688026250100c1e00c00f13000644407541d125038142003c04400090241b040000c082011006580c0601151382c0c94010600400224901c007040c03c1c0d00980070441800d00c071600900c914071170a0010049000641500c102010a10200030f40103024501ca403850b120041201280d40130946058030761004109a8401c0120b0407840702c0e101d5074005d0000d1000501c030515400c50500003101d00021524028413280d510303a030060f6118074552040741480c1c0c000700884103203030344204454220708845046064010926849002c019000060100e01241c1c00192540510000f040601d038020642c140904c0200d03050350100e000e2900e10f200e0141840851008a100180040c442101500c009a4100b1041540803a14405006c600c03009900591810004070483c1c2000d5100700e00c42e59020780350034904814044601c2524900c5441680c40c0041409500361505042c01000712030b008103803010420822894149020108981c000c7c00c0690019031114902d07280d203803c59160403000c88 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 138068390 1250 138067140 138067169
    0x309011107120f0507050102030a06180203041a060402070503030114011e021203041103060405010b01080c0702010801051918020c060c03011805060303090301060914070801030203070905071202030a0515060a09 92
    0x41054440d402170680040442d4000700810107a10305c1075201c2800c03504e039142c114400e08185429681248014ad0300681240418140011003e81c65800380390051f4016100520b410b225031111811a0002e0b000005550480e110113182580e000b8840007400c408040e100f640c02c800b0b0f50000c1d540d030148103114802c41c100800000d0600262a507010640b800140546100c0c1c1b0309480c013540207098070f89955001c1800500441c01280044003590341c60342e81a10360b20026400d0408010010b20600342e0544600780300d0b28082849102446034000d440d0020a000d0380ba603c41c07002c0b0b0b80c20f01030000e0540c612100188010018000c000081490340180100000ba068a03900007003800c2d80308500466400d5820034500182c1c1c0b0b40251300000100504050310305035602ea102003260030b00c1081c030020754594840c0c0c1d018021103400b80e0042c0d41126003410042c1c00d08503841c030310100743d0f0421600c5140d0382d07580301d042260f075004e40701501300e4000e0211140c91401da01588090020307419802030f12800001c10 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 138069640 1250 138068390 138068417
    0x20f04052424030907090c050a182601050708060105030a0203040c0f0f06090e0402030705090916120209070c050d1805300304080604060c05130902030901110712 71
    0x2540e600c420102c030010080c02078060301031001055000391060940c503c11500700141c031880314030501ca8050450340c3c8051811252040403200c0308042030844a202403101000607414200ba03501004000c0320301490700441601610036800c540d4001c2240d010b2100daa810803280d6a4000c00700c0c0c0d40248103046c016101e40341ea040080112000340c00400500b10191404951085460041d6045400b01d50b55030000766161711820f80300c02e005440003905035000500900007071425881c100d40c003243c8181201d0000e220312110000c0300d41e09038405030789200010313220419811700103c225405121407e0440d114000c6a60303d81e90342c1c0c100204002045003640c020790101c100f148041008110041c290b070442c00c46140340443c0e914800c0201c10070800601c550045a03100801560b00b1140300c000900910380d1941c880c48041d2406440c01003c0040800c010f49440502c0a191405002200e5006849242c01c4240c2421100c001c0703083c029201040c061180000d5039401040780c010102e20707140c0c01000c1c00 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 138070890 1250 138069640 138069649
    0x1090630020910033602010f1806090302010e04020a170907081e19031409130e100b04060305060103080906070804030b041a040302030a0806060d020a020307020f040524 74
    0x446075803960002c0b0183c3c0401d09143c0c550080591404a000011440150a603060408414680e02c19201c80d503000355140156000383d9019034803407940d0600e10031240717095101034100f1007180c10080100b198040b0903c15540c4c003600040140c4000e860440c90500c084501410700c6008218060054002e4400120202003d003c1d20009100f58400c50781c4007000c0d00c01c5000207402c1d43c0001c2c0024800d0440350340d00c1e00e0b101c800708003a1a0700f60b01c0382c1a01c2860792042c05429408100c190703420040000c492a0a00c200d881847d041c03025900c050480c1c030840740070880c1078420551100f44503d08040c024030125001066150440ba80107034029940c140040100d040c9010743ca40190002da00454000305004402d101c00f4480d40c441c2418090540020042000c0843c0980b030140069006001d00d0394224007070002d040c0c2241c4000c0501e4142500d60303980b0700c1640d12050031000140c20214201c4114108162805801001224180300c1032908104c0c0001c440302904d1100c060102402e8054102e488 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 138072140 1250 138070890 138070897
    0x30203090414090f0a03081303022803021510050103051506030c041a0316030e0c0316140d081603030b0604090b190303021f020408030a030b0109063002 67
    0x10241061182c486000d4110070000412109100c1c1806844140840c034000403d4440c65150f15849001240d02d9039403040100c00c607900021819032085040800e0414248107641e50f4010319084542e214090b80d00d8000c0c2004c0c200403003c03203425041010b004031801e44a0001d42555400c0c47c0014690b03031041c8403294110144003025401c0322000080c0048003000000a0003603c44900412802210400c0d2240d1184000c0750b150051f0700403d194000410710035000034031280359800848004490b1600080c0c201540344164144005440da0100062040c3c2c0c440603800d003000f00c407001705198198560071aa07119038000c9400750000c00b501c200805000754041e5011030801760085031603d4075203840c1c60081c40c01c01145803240315030307e581c0703512484080c203040203030380c0d243c1d002d8080403101907010010380b01e07002e17040e051180e000d01020480c010104080d24808405980100d4041851400074000448079041b0b58100a00300b030780020380c0400081300b000c44a044032440300d84042055403640c001d01 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 138073390 1250 138072140 138072157
    0x60705030412030e031501030206070f03030b031005090d020c030721120309030e040b0d0803071116030c08070602061317070f0204180b0a0504030908120a200c0d030203 74
    0x100c020102406041e03000214030000c1c0026001c480320b01240c0480d8442e2071b0003d12000b98410402c00080c0c001800c1d410200c0c00840c46400c0203c0c0d4660100d002900780912100c001d41000d0b03650080001c7c941040010003440d00f0070340043d04039a540040402d071500c03142d00030300e0f40c0d040f0b81601790045450680c14072104960041d0040b03902a03803441009001c3c080a401c16000a20036505114072464203118176010720b50f0042081d0100c0c021aa034000c2c107504024040c0c4103000740310a0702d130078441040c494000180503044038001d0890841c58854143d401d0760300701d2100341d4080e020a00c2001c0c0c0000704141c000448000401c001e4509207004910020100510200d00c600820301004020026012540b59442103070103000d10310000e91300e00414a2080c41c003800c44001000400d85ca04819400310380c0040c02403800380c01f460746600e0120302d00440f07d5180328011600283c1d090010341c2c07005c40700c01c0c0501090031400309507260007551650f407002c0c50401c3c0d1007841c1145503d02054000c000b180c1884 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 138074640 1250 138073390 138073409
    0x50919051002130b0f030f060a080a0201140904020d0212091603060e0a080a030b0f04020a0207060503060f0909030307020f15010e250e0109080c0d0b0910050c0c15090304050607050304 81
    0x45140117030903450350b00261189031007a080200440e80519103242c0050039140d10000500d10052a0f400449101c0e00c40c281c01e607020041042101090b440d140000e10340103208680260392001c0842440c0b070a250004e180344410b81154410314140030400a565040302d400440104d02c4a005044480c00d1000500f401040080c0000e020b4111581503003069110900484420611681c14000d002c1070313204000ca50401030304200c9081c0716040c0948059600120003400c920304038040750001c5045810300b65140c070401c1d40b000c401c0007007d81d410005e0440324600c003000782110a005d02c91035a001c0b04113003c1e40d082c21441000161600310030750060000d6010704020301061140c40d100c0a0f2a5070b070311a10035800182130320303400b10b41040300196408503c0340144c1030540c07400c0903440c0c11406002c06003148115000740f001301101c0c4d0105000340780c00303072811880050741c8040c4c811403d46070207940101c40d415803207440301708442c150000c01500e0448106440c0680d4031011480d00c142188216045010314 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 138075890 1250 138074640 138074647
    0x9061005091f03051302090a0c020102040b0c031c0204051008060d200109081c0c170a020706030b1801060810080a0b0603070b03092518050919051002130b 68
    0x202444003142c41150205520100441c5c0c407180304181d166280713a0700c041e41140c0c405020071132400041d40411a540e180c0d2000605182d1280090351055014040d80c000c694004240441040c080c11010038090340241000c5140502d00008284220130000f842410f02c45400d00007030322074880740c0070802503a51112401e041c50309102e0a074074048001c4000c00b40042d005820100e502c40c0b001501c0041508911401080c0502e008000c56901800c48c404507a40300160159808074804240035000d6040a50003401e40c513814190002e08540c50302090f80d10074900c94554a00100e18049401d0556001d45400d0501d0384c0d55001c0041c540d0300725440746003584501d0340c1c02d04c14064104101c5008002c01c4090343e03100395a4040640e4980025070f4449030725000210801511001c0d504503081442d007540705040681c3e0351f5070408114155803101204103949031000c000001404ac8900301506456984111026440742c407a01e507607070000d081d50515950300150701400030b900303001c041008080314500107a8 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 138077140 1250 138075890 138075919
    0xf06040314010e0c01020c0f1516060605031216121806030b090c041a0703140301061e030216020904021206070c03020d020105010b0a081f17070b04050906100509 71
    0xf007070b0b1a01c400ca818007031030f140310742c9a40c408076032001302d03001c020b0a59402c06d28034020000000c0011010240d2840204551400129012036642119015440010703000b403604041c0341c200504c0c010942c05102041241034007072385004c0412042c480d0451046d18490050400c1540e01141d40e00c0004030314559080005030784c69158002d000d0821080d5109400da403543c0031080211b002c0c030f00a0302813003541030020035840b90b860b101602c1030030b009150041c1c8183d8000c01d15003281d402170300b01c180040c068000768014003101204d13040c180101803800b1841d081c540d502c8108102d00c039200c020321651800c40030409541d20082400087c400c0030040c0d030715505100304050110000c140c0228054001e45082c8030503d0f006114483c1200c240c05034040c5800789542e021203040c07400800075804040712440011460020311101c0d0003800b00006102008819000c0d0300c2d00d000059803020703281c2d6008000900140c2c440c04091504172500f9078a08003441082d81c01590b40c0d000e520304154101c41c1da201c0002 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 138078390 1250 138077140 138077143
    0x813061a0310061a22170c0108090c060904140723090907050714010c20030408030711030709090c050f04050403020a02011b0c0b0403030906020703050c0f06040314 72
    0x110540d4040301120701c00500c50344040141c810601c2034012103046030204032a589001c00041c4090845004210000d0b0501403e038030424a442c0c0000da591181c2d1181034101201c1008102c00360202401c2c03000322454103a014a03030303908210021074001c1002142450940d100c2d81c100e10400c0031048100c440d10f10340560700400c541d008041000c003549400c2003c40350701c6030000854003407217405020141d1503603c1e603c060300c0c280d0240400326400c40c0030a148400d80700083c0300750b004203209583c55041d0031180c2500e241d504044260500c84940040000704030002c40001103035041c1e40c0c05110b01c0c000500120019090842036881280001e003005000c4041203100d4400e50155038048461000103086101444100c40080710024050303407024800c50050360040c61500c200c03401888082e4003446c0f5654032010b000019620405443c1d10103c0c0131b00c201908440d02c08003500443c4001d00006155481e503581c0c0700c000c55a000d02607003011120384140c1d202c090846002c2c5401808374561145604c2045 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 138079640 1250 138078390 138078431
    0x4080c0a050a061d060c0109150b042a17010608100e040308040b2203030f0f09050a080f040504050106020a0302010b04052a1b0a060e0a0f03081306 65
    0x6104031050103020460b0b140414020701035824955071020090f10b141507400591101c510070a40c4490f0512411100140034001d403102644948041a5400c0d051201841941e40f0341d6000741c030032401d22400c60000c1e00240045844030620b101000e000700c642c41d00503500c00036134007042140040034200110300a0340261005024802c2d2112100c04980d503a03d0800c041d280c15a00200010301440202e804142000c00c2c03183c10803071752103400052a0795494280c4c1c1540c49050114082525813074900f071050114441c01c1420302001c0014010300d02555242502e42e00c003540e0050414002043c00c500141c40ca00542c3c01401c1c001d401000b081d40c580002035075410703038080228010341c2800402051801c00c0d0041c580688070701e50f800d0603412504403a1011080160030302d40a080428043c004039414080302c0c404000503040d0141018241c5030902c10140c07600c0310030001482d441911880009508005250359a42e0986452030311900d0b010518001150203e0300941080d040c2890010f0b04801c0382a80d = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 138080890 1250 138079640 138079663
    0xa0f0203010e010f06090e010b031e0702070e090106060e0d060608010c09031515050d080c010c0504050a0e2203020118060e010e160e1e0109020702011103030609011a0405060408 78
    0x3014404ca60b41c01d000c175218a018010036039400d1804004009528800001c1c0d50409100856000d006c400d0f00c5048816520843c1c44400580c4848410031031440c2040d500340d04a00058000d02440e418600050181086020710f40c0c001c0e00d0030b150358401c0c400654485009001c6040023844104150b4000806413150750009681c4050b04281e44004464075100301c19460841030315901c0c440d132a190400071400444001907408a504000e00d400340b02081c4900380003911103403034081c0c59908140500c20062115040389908650340310500c219540750046503100300e09441e032911b61020787c1e443c041340900140221512841d008036080010006241c0149400d01a007000070002a071031444190798641030083c002c1ba60404101080c0480b2215013146540091403504100018450760000340d030752802688052220382d4041070780011580d20884c03200021492000440c110708102000980244040c420f407140308a0002c90300401943d003c00b0b4038000c0000428550b22903581c0e003452600e0b203040ca00c1 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 138082140 1250 138080890 138080909
    0x915090a082a0904030e0111010608010212010306060501020706020c0409170a080601110705010e041d100b190302061603030f090b09060601050a09030605060303072001022808030a0f0203010e01 85
    0x2c2c890b0b4603040c82c1854501c030f190565541194801500015510040c64100c2d60086540b5845c0c00b0512003c02d0006004404404c40c4000c2c456245082400490f074117500000c0c11500071440810142d40d0002e5403000c10401150700044110251400100000b900701e1103441982000c1880425584c0007a9024171030582070f241c40060580c0311400d81e4449455000b050f01190324120410840d007099031004100c40904580302c2440c2114048aa28061000c0c1343d00e05e40d152a5103020740581032681e6804120902c03860450314250031035000403ea809001454404002510902414188660000588c16004080410023200d1908084034010412244018544a25408034503154401e0040f20a140013917a11801c1840c25690f0300009481d001d00780960500c4244040c20102e52a880041c10021001c1e40700304645000b84000390600740c1075904031b0074103440000140c80ea11000b035600b40c8219407007010145c0d6a1740d0340103142d001308080d05204403e54804400071a5269543e810f9070f040c0c0d90f001c1d0 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 138083390 1250 138082140 138082213
    0x3130209040303021e090a0620070f1502070b0a030c0324050a0503150711010b030706050301080f0c130906090f1101090e09070e061f0203130b0915090a08 68
    0x481159486c0300d0100940e4004040c0c0204006640c03140c01043d10351100c0d810465810310040b0161854004103030405039009c0b100107410400955040100020004c2d10f00140c400946405d110760310701d0003510b840a040c140c6034140601c0840c03003503011522090b02074603400014465520044100744c030f540116806040c000002154900c0e00284100c0752140480350075500e5910310340c04131110007605c09456103664a0b60010001d960b014070070000945826520701e9144d62600e4201460411030302016a541d80108031185c1c00e54681c030b200820b007506600d9000c41d0100640c47d0030401880e40c0ca4000e042050341103080c00030840ca107204000e040000360380301450070352603020240001905640d0703403440c1c8d40007940c00c2080000910520f540104000c00d00081c04030ae070031110540242d103800450050b000001c5001901440808250281160b00c500e541040968000b00f180e404144000344052000070816030104d03504d00040c0b5020300030f04804d0f00c03030b007000c442c04900c2003024810141c024445101c = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 138084640 1250 138083390 138083437
    0x30c051203220206030103080c19060b040b0103090510154208040b0c0c01140610050405010503011a04030203100209032a01110f0307050c0a0515040b0313020904030302 74
    0x5403000d1024940040c4135510f183d03e5070b81c441d44140d005001c9101a40079a00c0c0500c0140080c3c070250b007155005400104010744c41004000131140140d00c01d50503d882c28001d8404030750005142c0d01e01450010002031850002200c203c110521540310440e1782214a01c901c449010403440c41c155584a503a402146c2c00385491107402200c1c49074410310024240c1d00c00180840c8070498803c6c0c100d424401d00c0c3e464070740540c0304e40e8259036407280000d00003980b0005212081c108441c4a000b840c0c92894050300309410100024010310041c42045460280c4510304099141c51204407001550300404803001820700821407400ba42150004501c43d0141c0d90f1410f0b1045030f074600c0c568000401180c1010fa4010f008010744003500303040f020705014410000301d44003c01d420030007030694a01810003000000380100c200001490700340c201c5406410202d4115061703040f51401d8406441001045503143d65a0b0040040c1000c00104069401610002808241500740e0300400c61240c0b201e5400642c1204c8 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 138085890 1250 138084640 138084691
    0x507091401050105071b03020a0905061003050705070308060307050303030f160903080d0510090501140a050f03070512160312030e01060e520807020a0f030c051203 72
    0x2d200d520301080c0304000400004800c0b401d449400003031382c0c2084030340030f8480e0086040c100c0e240d0002c2c2070440d0f46009003d00351800380141006409985000c0c8240c1c03500c45c50080c1240900e20004043c0058900414060798060080c3c0d8090000034044030748a00e0042403104101c4029a203608405406412004032144203524141c1a6600701c2c0c0c7c03081c5072440402401008000007401d5003c1d4110030140440c41d0b80c00340c000d0310700070096180d80341508198a410400f0040e081d600c43c0d07204944c0314160505a49020a403803086400c1113400442d038206490100b0300345650400c201c01005090302011040044121a412601595903000c008248264602074202c0e0400d000b80c80da820504000299101040140c0240c0c81d00244000c89000744ac50700448d15281d079008050509801c1c00c01e0000ba42000500f18032520702d042c0ca400c0800d420498400794407a1300c060b402030814000ca00200c0d05040c06000b4400ca02644072044070740d4809251100491600290b45083d803104420a02d901030401 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 138087140 1250 138085890 138085931
    0x3102d0c020327150c0d0e0f060a020336012c03072304110310060e040b030316120c0c090506040e0609150a060305060a090804080a050709 61
    0x125001580b40110480070030b01490001046040c0d142c03108043d110040d04c83c00d02c14a01d5440210201d5103071301c08030302d1841c10403503039040c10010400d411b50048101daa811284140d090b0082c0d075410384d030317042a030310490542c07060140b4000d0030803a80700c10502e4050440381030104460402c0d040003407003110000450342c0c0d0b66188065541e82041d001c0c0080911041401c0034003241e8000d04403400a031341e03000d1419103000d40070b44d0301d8660058840d2800c8a0704150241c40703010015488128035502d040f410440404100d0302903002000001d840001007a21180d12500c1815030040442e6141d680c403205050b0540c080500880c1c120400300e00d003da103140110411002341d07510403240390300c05061412074401068001c2a490348951180c100c40c3d9a18001d1010f03038020a0804d02034805000f00d444275021603600508403981c054a018001c101190020404035003166860700b02150071011800d28805901542d00894054010800714208000d00020300c003046500121081c0465130030880356a03610003 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 138088390 1250 138087140 138087161
    0x6110606060c06160e1009030b0a02040302030a0303110702040e0303070905150d05090a140607020706020c0618180c040e150d0206031e0a020a11010e03041403102d 72
    0x500c000d01240075181440791113148404a854400c0603580c1203400613441c98a0050854041012a10b05100703014800403120f500854184003540380c0391035135010035070310a007001015041507a50f41c2c640ca6101211000c0f60f2601e6001002800740300b031304200b00c1c0e40743c0d0b00a851940c045860040e001a05042c20040d10940c500100d03229418080f241000c40040c240040c401c440c18003802c8941b000003900904d505200d500100010f141916144102900e00311040d0001c2c429580003407840c0301d00360781d03c03c03c5407145c0741403480780f04108800f240410405c00c04142250030441c0400200320340491014003034001c40e0000e02c1d2041c00d980307501003d20340400710544440c0c0c00054480020002d801c1410007035030000c0311018001d9021545a40a5a183d5002d4510010198000401d420038940c40090418640240790081004207203806015999114a10035525944030307200c0601240d50f020300c03110203840c00160013480514000e0000f14901c0c0030100da209581400f08500072102100c52041302c1101 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 138089640 1250 138088390 138088393
    0x90a021012140a0b280504020a03060302150910050f04062a140c040506060d0e1006090501050f01020f0c1207090f090303140702071202120f0a0605011a030105040902030309060406110606060c 84
    0x403070500061001950042703600700c09240d1620310000050f1541a41542c0809000101a444007640c2d4104204e18001060f44020400207200e154032000340302c41214102c801c2c90030100618041070541800200b60baa200040341c1c030502104200780540c024001d090007055105444170914084200402c0714010354096402a0052008040c480030540c00720444040150840c2e019640144884082c0c81503a0007032400c542e2142e0040003181000c12081616000c00d001800502011000140d42c0e070f0308510035a40300300340d41803402074204010301294029094151092140c072207100c1d42070001d80001d0703004400080c40d0040f55040c1c66180307030342c860003001580c1c0030300586c038500300c01684540300300c4509a80c446803c1495402c4041d0070001c0c68041040f0030042e0024080c203040c102e08550050f07010510540008030076407034454200781101e066940c2102c00280040b501d0004c20b2550043c0150b060700f0550018021403110f40010301000640003a000303ca141da60f0700000d0100a000c3e005000032907 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 138090890 1250 138089640 138089719
    0x510060f03080f070c0b0c0a020108070f27051302030118060605030c0304030e181e06010e150c01020c1c0203090109060c02040e06011706090a021012140a0b 69
    0x541483c0240165401001181035082d1100c4a00383c01c0d030300c614814400355000048103021035800103003c0c0e9110030b150a200c070503140320141c0501000c00310703041d03000c920042c280c0241d1130b0311141c039109010b854040c2c21021612000300c01c0704000c1d170081c007407413401404090b00141400c00b40c0c064001a00d0090f50780c2400c5071a6044002103a40014004030180880c2c250745d1a244c0d00c0b10300c1c0074850390030b02c00341e0a1003504107003500003540d455403840d40481840920400000f41d07003044400c54200002c0d6006505801076001c902d500b0300604401400035400019001600314001403500c2a06010440712140360005890580e80e07480f0b4100ca107404158118805c00c002030054201c40440e41c00504042060184050740b107060a400b60014400700400d0140040c0d0000100078080d0700000b56401056105075a40020300e0f0f1000000071031080080000161454000c2034000360a4604240089051801d2440003c3c025084a03003c042c00340403d560440403ea102031108a00020342c5418a100f = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 138092140 1250 138090890 138090907
    0xa1202150307051c02030406180b070e010c0f0302010c0f0801150302070f0609061521080309030d06060f08241e0a0f211104090c0b070510060f0308 65
    0x3840e0708014555401c0c40010300c040a21050150854100341400441c016a2480c1c5880c0050482da4110511490903c035400507100103941c000060b500310317a240c20020000a43c050040f0f549180310b80d4003d280e01c080c8642c603070415405402024000c682a180c02788000003200f000c80f0708203030910400710102c80340455401e126002c3d0b8000c09070b09008203890310080e011a1982d600b5520102011180c140e5204031415a02192100103005003042c204403241980c180e40c50810707494240e1401422061002002c130780c04180800c2181c04e001c3c60a5001e0143c2d56540c0c00141000504001301000b00380d4070030002d00c05118000d080401400d541c030203001420684010300c112141d9a2120400c1c0d091048118066951211008c1004240d2041d115001c141010a9807400701055000100d00480c6500a0800900d15030001c1d9a00482620005641070590401d1400100383e43d00001c4000c0e00000c18509000c00030510610030800741000b480a05d90340d409102e0340c00054030014082e054140700148 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 138093390 1250 138092140 138092179
    0xf0c08071103030a05040f06020a180f0e010e180a06060602010b010801060807080c041d04110d051e070e010603020702030c03060705070807060f1d0d0203160b13140c0a1202 76
    0x6410600421011011000b00d40d1920708903400f140c0241e010500c01a031500718500f1051103080600054010650f42c3d03403378010b242092030018085d400d00704610600003181e1940529411054106440c1100d07004186400c1000042860307000350030055007414640d041ca940141c04082c1290401d6035030042550716240221140704010740311000300d4004020008444450842c0d400e400d40c0020705940b05810030b032800c00b0341410040304840c000e40c000c0080001160002c41c645c2e261515070204284810510b01070310741050f11641148500c010ba200010030595410b602a009981c42074080718850254001010307982c460843d440000680d081049900159240000d402681e100380c9000c2505010020f41c441036911040400426101d01511b108200c001000008190a158000b451500750b0001d14900c0710700d040c1001034080046280450141040350f030b280b01c0c0340350700321003a01400280c983c0c0a0742c4032841426070038483d0340c0580c008100c02400a4126110a500400070701e1704c03902c181e00d2003 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 138094640 1250 138093390 138093401
    0x51e060d020907091e14090a0b0409082d0f25030e1503060307090e030705070b03010f0503070e070305130803011203030c0e0f220f0c08071103030a 65
    0x254100c0112001040103071140b8803030501400544e02c5142403203040900c1c0100d0300b00300c0007221000108180d4100701e202c03451910084658003d80b03641545580f004140c0010f400b9104030341c3e810503d0412001e051003003020250250b0000540003242041c03624015000b1a41e01440a05c200c18040001150070030b4600020702c3e103403910a100d82992100d41c81c1c000500c1c0b1601e1400d0740460071a43ca130100610f800c2190300740301c2603040b400d01d00318180040420b585202c0c0d40100500155251086010003504005440703e070b0780d1001c212851107848101081e0560006c3c4240d19002c50081404915480d0100d1032400341c4520302074030742c440e42d1510400c0f00038240141251800300d88100c842d00114400c680207501920007155800b100000074034008044a1002d00d818041048115049056a89481607040c0401d011a4000e420b20842e120b921440e252580103c017003e46070102882c140c00c82038100d0b4890520b25110f14640355114601912000341d43c034034060b8903402c10800910840000d6120 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 138095890 1250 138094640 138094651
    0xd110c01020d350a0e0a12080a0912020c010e010201020703022a030709020a020d0e0f09041b060903060b01022b09120317060102071503020f0c070b03090d03051e 71
    0x511520f4900d559690840504181401d0910301c0c100108901d00d0b205005945d500c3c5c0342813009049000c01500d0303060072000203101d0401002941e03804122118040e400c1030030100d81201a10918082d40381c4007035940d1300b00003640d030301140440c0c0300f00346d081d03006100762001641c058000c1d010700103034080c46103042c4400124a038481d6924540c0d0640c25102007001c2009010000b900503541d04820728040e00c0e00203202c612208001c84c0501c00034440c3c8031904c00703244403c41954030408949492502c2e529100600c540041c40c26410a80001c540c3e0b489044c92040364003030b000400c14072024000484c3c0b180e03041c40043c004603d5a2140b0200c4000c4007142400004540c9451b40c2140d40307070b1500341d10314024001c2c1030b000a0100714080c000140b24800240d0002401d000502040d4645070103000b003100c000010b0b00601d0390108148000c138090310125883c06610100341c581c0d240c0c49552010b8640c00944299666205002807000e4140c000c0c4181409103cad4948450f1040a10700c20f04041080000d00 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 138097140 1250 138095890 138095927
    0x309040207051011040608010e01050a170c040507050d0e01020c19030903020409030302040314010506090a020703020f1006030308070c02010203070602030604021210090e060606160201050408030c0d110c01020d 92
    0x110f03120360a02902c124040101001d0314160354502e000740c02071014006070002d03801032031480b00400c41c1d60303a8000840300311012600c0f0320021505109656080010050007242c002d41408200702209500100624a240d03240f042000b81d00040388040d0700b02c0c00323404012541a07010082103031410104541c410b4039684245413580030305440340d020405480384031a0440100340c01050500070044401485400d0741640c0d40204018a81900043d0580c40003a0511b000c10360700142001c14140300348008026020420708441503000c40e5000d000092186200541c0050002c0d004a080644034800c0b80c0d0380a60140d00031810600c041c0c450000a5202506882d4402c0d401c02805c5004480f1403602442a203801511011240ca886840000d60b00d03d403480705584c1d000401080713000c1e9207500c140e50b40f072201c40080c40108446440141d80a1055400000081c440842e5441c2d8407a400255410408803d542c5c130b840200040c080c641e540c280e1032020708e000d0313009050500c188030311814030000003521601 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 138098390 1250 138097140 138097153
    0x305030619080102031006052b110304110420030408030a060e0414070b09010813110d110102070609240e04020c100b060906031503160e060a0503030309030904020705 73
    0x81500c141403644012850f0750040100a015510542d00030f000700114101685800c95103400440504144c0840e108407c461807074410501c401070744040c1440c0300710003200d40d03207003081d0502503d032921150005100d0340c00c114191070038040e4000711081d0030081c051311504507201c0c0c1d134030208180c000402e2484419681c0030700150b002041984a0f01031070140b000751030002401507003d420a40d060b0042e40c14403d042081c402e503640d00c56007080c0d120f440440880e1040c80c09103061010030319600261540070740d001d00303d24180580001d125500315000d03000c9400e802c0e9130382815600384005104003e0a03040c101940d0600c015903000049008055207040d84e10180e0010000703040340c201d0f0300b01c001c50354402030405c4401c45880c4145440e20400b05c03101421315a02e10002941440018015079a50340704403090000364400300030264081904284034021207440340608000144200c2c0c07020300c508901500020faa04000c82140d00030403d90000d1854a402407043c00040c0d840041d08440f10310489 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 138099640 1250 138098390 138098419
    0x60b0402131d07020607021b03121c05090a030507030804030c05070609030c0509010b040b1617090913080928150207060f0203070228081c020601080a03050306 70
    0x41401d0000c0e011078181e00908842e290380071129054001c010308150350044041c04151600000c0d860b030600905484d421500010360b001c030342040c0303d105200d442a0301c0440c2c10b025a08110046608204420350300b048141e0351450303240d80e90500b456000d8003165080000f400070910501a9650040c00f07420807541079a13180c2d9030f81d843e10300700d9441240025901403080c0100a14804000c00504040f101140303d941000f1030941148100c2c131480002040015091005049070898443c0660300610495841318180c02c80380602e61141949521506a10000840b0b441c600f6200302c6030300b5040302c250b41c00c144032001070000004228004621105400d01e1070110310322807542810180441d02c011211346240d02c00f0103440d1501540250051042c02030072200d82c00e43c000196000a90100e61007032806002030300c804016440400c0101100401c0301020400ea031000900c43c3d15064140210402d11404080403a100c020038003d4141c00d4101d03000c0140882e214101464100500502604403c2c100 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 138100890 1250 138099640 138099667
    0x8030c0d02031204031b0b0f0709050906061b0f0f030d050906040b011406090411040e07110a030509042c0618100903271503091505090c0301090b0f010f12060b0402 72
    0x1148c0070700b69400030408106070710350310500010007082c0c00e407900c0c1103508190001410b0780c0200c1402810803020a13041c82c041803010801c20a1456452081d16010185001e03000d44076413103080d0000501d42058042604194005005442980c00c400700c0002070b401c18114001d8140c1d4000580da0000d002c1c4815241680c1e58801c250780d0810440c0c0c601d94440c03074201c480da2010b500800501c20f1080f0744a04140562010035241c0e885941031500baa44c8144220018004209115480c02d81c072410a01000c000150310848100c0607101200f2603409a54a8101e64680c01c00d01040c0300c0b45401c0454000c69070b08058000c40c1d0014824144020182c801c2c05044400320841580b10703114444072401088002010150101c0d200510702c1c0600000300240c032800310303c1c0b82a0513801c8029560f40002490790381c0038001062180d50080003070000301d03031908050302e84a00642d6441c540c10540000041c02601c1c204260003140e8605c00410300d4031400c0e88806e03005080038181c80d0b401a03020032054100000 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 138102140 1250 138100890 138100913
    0x70504090501060f02030702040e030c0115031203050603120903072d0f06020a020d0203070506190f0f0f0804021206070e2119030507080a0804140607020606060d0e01020408030c0d02031204031b 85
    0x8803100c1090b040340c3f6505140c0507a0080c140880149483d00c414080146c134046948a980c948001446a4611400e03011901c0d2500c00e5000703ca6100c40d0350070314216000c00e00003d000701d003001a40c0407241612086032844240e058840e00b4003513801a1151801820a180a190030900003000e4800c03556039100484c01d9580078520b800e0007104050400c0001d80d800c0410b520010760036142000211081c220050485a94042880b09024400340050304540e5141c140681460480e0241c0d8080e040c2200050030b42020140d540380b084c86044200c03600c43c02c0401d100000e14540b1802460710000c1b8205080490300c0e4a4001d8040000401070140441d018030f00400241005580749101440e1605101c601d801500788034007080c0c0c014800384407885900054040e0030600880e0b20b5135440699000080040814510745041c0b940040760000e0700250110142010426050548840200c0c151080b0788a00c6030b805001c2d513038080c060205010038858507641d2140000c4403400000d8542c0c40c0c54041d500711 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 138103390 1250 138102140 138102161
    0x3270405070504062c0d0519121407020d030f11030403030f08010504150302040b01050c0f071d070f0c02060405090412030b040612110414070504090501060f02030702040e030c01 78
    0x104005410001030780e1003440809401c45059054030b040c0d10310140e901c5e2000c4044130700b511500a020114040c0181804458089420b2003e89091200d0602d0031555001c8034a04400110301032045412500300b404c000c88084680c010142e0b61501c0195038161107200c1441102c204203c0701180c1140c04040800061010b14040c0c0c03103000303025200c800020420901600018090b501349411006409005a124803d9a81c125000701d41c030781030780700104e506000e40172001d82c1c20300c207096104900c00404151a0142e50000b04800c0d609000c0101c3c510949005a680e08005017880403254a02445110001c00843c070046c44c0701c0c90603035500c0019240700025102034462004c0680c0940c00c054051142d0511f0101c02d035014000a031410880d00b00000300344d00064a101c600c1203410742c85035955804801000912101d030f01c0ca03402c100308024070310740007401032040140ca85030010070840d010b180104d0719a03001c5d03030081d8506240c60b070900002e8620101d08140398403043c0184038100303400f80900b81021 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 138104640 1250 138103390 138103397
    0xa0b0c060a09031e05040e060d03050d0c0302092701050301051003060b01090f08010509010e011104090914030c0601140301022503030609110901031112010b070c150c020915030327040507 82
    0x240c7c1410840c40d0702c6580501035030310070b6058a4220000a130000c040c1c0d400034445600010700d0440c080c00a40192041512040d80258554000c04e240705c030031160850644a0b00c1c00202c62684c840040c142203e00540f00d058280020fa003080001900340c0e00901007500040c5484e805503a55202e030303103c0c40c5250380c03c0181140d44920401404d00030900c00c003e01c006810009100500803009040b20710305c5a801031900b4540c4940c01101031000030702482d412a1400e904681d41c81620100c800d4031a0300070b0140002d1011000c078409890f140500aa03030704070380c81031140a4030500510121460080c1d003403046060640b50313140002d00100c80d1080410103202d41074110360383e14400c40010202d840502045108180c28491b0b00d1404500100c0d880c1500e501e00c4c3e400e5680ca0280c00c141c0394030742e2107600078140c02603003880c42694203620841c912815407003520107100d2030311030802c4002440d0501c40d0858050b8000d02c00d940900750b03524020715460754070004030b943d006020030108040c0e480449111021 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 138105890 1250 138104640 138104647
    0xf070f030221030a0c021e030405030717060c070f02130e1002030c04060807110102040602152409130501060803031e01182003150a0b0c060a09031e05 66
    0x24140c0522081407160368161103010300d00c9000c010070050307000c09070060f05481d65500070070314114020800010460007c6e00d40c00080c46000e0a4140d51782d00030701400c0d010703024040c4000b581d04400800c3c601c1401700038000c0c08044c1d950b0f4540c00c425420440742600c0c465914a50311000d6150b9490b1410080076400000c17a004801c14030444c41d2400054000c0000f52040081002828041d0103444c2540d4491030210300540340c0d0f5800310780c50f801c000d04030089544005030000740981c0020310f0342e20b803660026200c04c103607491001c0b91040c81c40c201401a841142800c01c0d00aa140182c0348940c00502c00404c40105100340d1200c80c02c41c0c40a82042c803160b8800000d1049400c2608046d80b1022300d65040240036605180320000354400d0b2000b5600c02c25210031840b50a2401c081e03281d41030307039800c0008035209e142c0002220030748560013043e140030724015600416a4603a90085032008034965000348856218004a00c00408005805400b04454011071030a04015a40e048003043c00c02d0382d91580703 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 138107140 1250 138105890 138105893
    0x1060302100c0b0126030a050909010b040302030a02090a0e1f2a050903120d0c0e0405010b1c02130608041e11121e0d110105010308040e0c0f070f 64
    0x44101c0e2100c00744541400200300003061884114156903a0020604550320a40003520300f0048042403a0b0043c00003162500380280c0c48809800e04801c21106610280d0742d032015004144a50301020350150080d1010f030000d030078000442c0d90000540c002c0050942d8003580c0060030801c8511b021503000c4840d031206414400b09011b50b0580c00b802440c1d801d6280095a4101380c2d0030f05c0111894144540800d0001c01039509103e00b40854526203681030381c450008001000a0001d0342d000c60114204140c41b00e66810b040c495141601c860100d40d84c544001e0560460b48070005000e42c1c2940b40d000c1007040c903a01e41c0f10a0841c02081551100a00c070304041c60010042d050070000b00c3c18007048003c43c00f010443c552102c0d00180000c0d079009044030103800410b42042c1040d4000e20510080da50040405900010940c00305404caa45640a005800075143d0a9600c03c2c440038148080920040c00703003825a040b200d420603c851605032a041d0080c8001c40c082c0c1011909075411003c543c400320 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 138108390 1250 138107140 138107149
    0x2e021b010c210203090c0d0f050102071101110a050c0f040204030f0c260304090b0301023c18150d050403080f0105010302070213180206030108101b0f0e04090b0901060302 75
    0x1c800d54100b980070b60840c90094021541c2d00c03540810740e0b20405411040a044c801001411a04140c108000350750312051414030009580300c11180500050314500029008580444d1280c000d41e4000b019043c07203510307001040b00f0041d80022481e4403940c2080300000160140f840304440901c10544034070b580e803601d845200003092a038008654000c0310f0003400d04220020080302d003030b9003010348002100c039a03000120380240140708000414941d4110410201c604011022080d4428400b044008000580000c00d6074015841429034000742c1d0030322100ea078503240e642d11f4080815800b0721800c1058205074001919002c3d00d064002c50988420f0042c0301a51070151400f400c1c080c282540b4205055010810410882c002c040134035542d90064104040180803548000340c00410040c2c4a58440030700030b4440c05102184401e10345804041c2201d07148040c400069416507440b000c0c20180e4220050b40c01c08031888a0590050b0380710282c00024028559031401f80a1520001034824298410720 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 138109640 1250 138108390 138108437
    0x8010b030c0114040e04060605040f06031b030c0302130e06070c051902030c090a0608010204060503060a1e03030c0c09020d0e0106060806331207022e021b010c 70
    0x290b04000c2c601c034074140076242d84000c4504480300300080201980d01d07800d100004040c103400088c0c0c81401e2001d012070b081c405421042c04c4d070340030301600090b4510505001461401c1440b0040c0000c0494030100f004d0714213043c00d009621240000800c010140c042c6041c0bc00508a4244020603250001d4400b8440101701124601012507040410369150307400103a620901913141c240300e4401c0703800160911496820010003000303190025034485440e1030307003e001030700b0031134010307000b0000341c1400070743d200701c501100e07109441140b403580010f415034a084800c0c407011082900c034030344000e03000076070b40540340f0003006098490040000c250070801c0c0d80d1402c4d00c0456120300100180101030144a43d9192084101308000520586441807403400006011001124900000c0b50104000303014114100d0030381c0c850700803507080e20302140f07c072290140c181600111b00207090180804107140c0b5070b070340d5000f02002c0c03216a103065098a4651146425601551802c0002820b03242c504100b003104625103 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 138110890 1250 138109640 138109663
    0xc0d020709020f0f090102010b031006140d0b0601050a0903020913030f020601060504051908030409020433030e0c092a07020d08090105040902070501090c0509040f03141308010b03 79
    0x2d5241c0901103903d0111070148042d001003c1d0720015060703141d03a0003580b1020302184080c09644004c03681082c50300007000a803080c030041301c504003503140300392400b4054403d40780d902901340362658803800011906034001da40f04405202c07410101002503a960490750f446030080b084440d80c1c0c07500e14980282a40080c0301007000795403241c0c0c0180030141e040381c1a5030644006858014088030a100145141001c0e58803041003130200041c00f24401280d070300180706407103a0f08020024428080341d41201c02005030014040600190900d01d202440780c0c100700c1403900c5040032106c00c0b03040c030740010704d80312025070f032400d4149820407180344244e051144510509580c081214102140341d000b1901c4041c09000081c45d240000400c035121744c1c0240103680180081d01411900e44280740782c61802001c0d241410ba4546202d04000115482d00300c0500c4e1145501c0201d9122051080d41c06503404a903c1610182087d024041c099030244c8072203481000b00451000420500d4001084c5424450343c10309 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 138112140 1250 138110890 138110909
    0x62312040311061e13060213030c06050f03060103110c061f090c0c08070804081002130f05010c20100306030b0606040503030a11010f0c030203041a010f050607080f0c0d0207 76
    0x420983c401c0050801a00c98400c01c03c002117079980108040e40100700281c014515032012404c4100815040301b0641500c0c4111810743c4201d40340c05003540c040c09070310a80581e0203003c00000362254030030b411a0701080542d5803298200240c01080500300034080f0f03031601e40845180b55120b142c0d00080b0b0041d0040500306406c04c01c84c102c5031001400d280c03001001034540180018580b0400c511ba9085a00415601041da00f1859584603503c001e98040010380740d41e40d810080115840d0b150910140c2210016114604010040c3d69217080d81152007010710f550800d04040964240c99003154240c1610f0b0654002444504618009007c00710117000540039160074407041c0110340300002210381e90300180c11705013520301b2259201805801280d011040c00c5060864804441c1e4054018601440c40360340c809160620360641c003e02140248103c24510010400801003400d0440c0100189401004030502d4400f200340d0f0201f00f42c2c400e030a6200d40745c0c010a80ca500b990390501c040c0024000080 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 138113390 1250 138112140 138112153
    0x102120711010e1014090d05060c04030b090705130f060b130e10030f03080901060321020c01020c01140c0c09040f1e020d060c1b110127062312040311 66
    0x7200400040305c00120304040c0100151422080d0f46201208011035404000c0b1101ca1429040c005070640003071008071805080c0794041845064041208002d03104080c3c41c03289000c0c1c126801030007402109042507001c80d52010041841aa41802010480d903020000c10000e4070303210b02c014081c11f0080c04000030381c20281080c8001072000040300d0706c9640514005101d03803902d0480b0b81c0189480d030700007060114115504400000b5402242c20702d143d1580035104150440001641c444000800381800034a105058840248071240a000d24540070000c48003521480000f203101c5940555003603501c1d1a03225035001c20000d00d0005020340440c00660740d203614883e0b40c0492580340e420301c0000c2800d601c03202030640451107100b130b800001e4a900e180494556250070311168180c0107400142c0000d441d00082049145901d40140e01603003003891000e8940e1508104450941416010414681083ca84a41009410000351500348260b40d1003079141d0a081c41e01625400442d900c1d80b41d40e40101 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 138114640 1250 138113390 138113419
    0x301150e0f0d1703011202010e030d08010b0c0c0a1205060601020a1a060d12030605010e3c030a060f1d4305030c0414010b090102120711010e 62
    0x500715010094007070356660403603089842d01d80080311460340c03020141000400001201341440c2889601c40d4001c1e00c0c3e98882c4402101850b0702da090403140e80010454003401040785039098001000008001c105403012a140c002c0010142c02c410741c8038a1148604c021101c0500005105250b085031007400104001c603660399903454075031019064003a4034541d410000b865a01d03a0030103804000e13800798284001c01c00307807080135001b8803c1d03006881c00112002d08078003003070624409a902c51706281c6107500820103658808108945400c04080103c407482c1c00e8400c0c951820003840841500c14280071070702c0501400c2c050129181021f1070136402000c4168074528000c0481c0543c1022070702450301d800904601488140040c200c00105401424040700d05104050903030030303809581089003500c1903000342408220075562410a02011406440010040e02c010310004110020041c019106070183e07c1c00c10041d1030300319a10960b4114481644d031502903a10448001c0000402c903032900491090 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 138115890 1250 138114640 138114649
    0xc120301091a01090b0c01060306090b040b0708070c11041107121403010b0a0c050c060c030a02010e010c170403020c0901090f1b0509060d0e030327030405091506120c0301150e 77
    0x314030035401c0c040310004c1d180d11b01500030740050000c2d64000e00c0a00940d05103250400e9490011101652100d0242c00480c140c01d00c00d05900b030040700e45545001c204885a1280692064200b041d07642c03165481540c403102c801e41c100580300c098000c0081c624413150106000e010b00b04003003d0690072103010401884000090003c1c2c0f1480c4007146000f0412026a180403880c082844c03040a0384a4800700e90003400b010004000c0440c0e40c0d49034020300440a824006909035464000d4200118030495a000c000c0c500b80109298001c0c024411542400016004126911001e810400301c0c19103070064208402c07040e0007441509007034000d40030440d403490038000303182e4082e82e0440e500c94600003444411099103030700140030800303103002541d50368109900d1525004d00b103e45070754880720000400000380c402c003105071800c58038040e0150340ca5030f44448429030400304204144d0f602240c1808200d41c1202c03005200c42c41f5102c0f40013016529410710141d20328102d50105a1420050144110b0949854 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 138117140 1250 138115890 138115907
    0x108160905010f09020d0209042d05040b06221a090603060405070306020f070c09020919030809010509010302121f05030a03021203060d1415010e040209040210050c120301091a01 78
    0x7884e80005031a19400071202002e40301d04400c00e68894140002076030340000e0f03000c012500421140d0b0042020012294007030603034a044a014180c6500540010001d05240c00000d0003912441002d00c940010341000100711a08194229110540590000c0c1c45046c01044190007176000c5000f020b2614181d80c85540d200418000141100e8000c14000c442d40c00000a840b007590b80031301903120307003611208a500250002c1d500c05100f03c02130503002e81c5440341c9080080c01e590300003108a00d881a0100152003d1380180c030a5410503600300301d0b20030540500d90001d0b00807010744032101543c4010f0f0f0b490b5103e0716980c0e00b04a1007070f0040c010700300c0000e4001842490840354090016100d9451200044120062120181140c0140c000b0312011003804604070b99a6080509038104c0743e62143c40003e09200220b9009410050500124000d440c01113080d840a50ac2864114940040e032200282882c4078640d0f483c410010210051100d00b88a02560424003121001c2107040c114800c0028042c18 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 138118390 1250 138117140 138117149
    0x10b090c03061912060207050601050103050103020a09020c0c0904050c010f020118170909091c0e06040302060d0608010609023705280905010215010501020d0e0310050108160905010f 80
    0x40c0c0c501034001d4a0f03003860121401003448030303581c08540d002e505002d400ba50003004229254050400089000c0d8080d11078181682c0e00070344805000b500b4a180100258085030b0300f21418403521924416640d02c0740f6005c0e00ca80d102d0f0014085e42c600910000d8000d4400041c03c1c0203590425a54500f108008816112116041400c0010b07010a032115a03803148a1075072403581041103031080111882e03001400c80c0b103454500054050f01c10000e60115542d42401810b140d0040e41000100054580360014104002c0501300000e40659580c404500f124600d60000c10703695004034401c0c1e808030621810303001d074040007001c2200084c4007134000b40841c91000b8050052000c041143c4a0120200c030794088806a4554081c03400d00d404040940b14822900c20940144901081c0110410200d1507140c100c541c1a002440d4000080c002a43c0c24000e500f802e94051041d00340f4084040c50a015860090011901500b03050b10341c0020000181c00300d8100d01807d41c00c040040050003c025401411607 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 138119640 1250 138118390 138118399
    0x30b010e0d080d0212101403060c0d0b030109060b0a05011106011505070c0f140409030e01030c0302090a120318081005060a1d06091503120a05070210050c010b090c0306 74
    0x100780c070b14000ea614051840c0fa6800e4a00c08a140d104041035100250b004980d000c0320200c007242d40301008034442c021800240d8040e0030410100c0c100c00420000307045c0c517100304600407a0b2602c8031004a82180c012400540c0d2030303915120484e41e01d0600d0302004c1e001e0312003840c0141501c1182e0b2a4980d0b150010f10990b00c002c002d004915402d01d01c07460a072400b055101c0d590030f8216545038210880c0050030b0003403450030a01303a0700f44000c03443c1c207104800c500c6134151540c1034100307c00c00041d0b00415005008805058081120461569a1002840c00b40141140d0000e0340315590030000c00440240c1000b20305003080322403d004172030000a405440ca400d407540031803665501c5003c140700040300d03130214425080d0728113415020058980d080384118420340d00401213907110f00140300b061410300b20454041c1c1001a40c00240780002008141c40009030624503c0e2808940c04640c5c0c951400003040300107000442c1f0303500056000c3c0109015070b8007c1b999400141000c5600c0c200034880a088203226 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 138120890 1250 138119640 138119659
    0x1f08011403071205031312020315071b02150a03020d05010503150408070c0e0906060102100c0c08031f06050a020d0e09010603050a091e02012007180b030601091b030b010e 75
    0x4010b005c0085905111103003c124010715640d02542484c410f540a00324801d00a00e1b402210b20b6528070300c41c134072131861992180f1100c8070000c2810042450000c09a8015081e0018411369070160340c0202071500316a980183d485442c03c503820220b0300f040e0001072194021222490f44030560800d5540c2260700181813644da00392514100721454103a61111150010000c1048441640411300b6841040281c01b0307101600101d21410f0115500000300c07401188401c40d003003011903625405154440c2d44824940c07514000c0b158000901840d6520180010b5000141e8444550303051100041c00441e90034007071800040700d40080c00c2103005028500805950b00002840e00358250060840d141e00414611040311031074030180c44013220880141c3c0480c3e1244503905601c3c10103a2914841a03844002e4401035082c08507010741d0551a4448a0b00c4540310106610319503020b201850082800c1400001c80f43d049005105c449021525003e052501d0701000381196604008403a00c503850843e022040b = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 138122140 1250 138120890 138120893
    0xf3f1e040305010c1e0809030412020301020c0a0f030f0c1109040201052214030708060a2a02060601081602060103080c0a050303130b060607051b01030b1f080114030712 74
    0x9900455102411560130041d2000715a034211412103190a982d102e441c0c00c6002040d810388441c2d03400d0700e4415080d07208010400c00c080180078588203807840240090301e0000040340d2245030403c15541074039102e140c40d008408068001c0e0f01080c01d0551424008048c040a44901d61004000d881d0903021f0f0514500103011a8807030011250300608a0010103081503040d035000711201e21a02520104032900080c080940c0380008091081710710540040c849a924614144081e01c00c048813810000988101d00000d08000c1603400c0c0700c01c86641c014046494400d00040113810054140c0c8000f800000745201165408921941502d410140b95a030b602200c1400914089030700801074440e010100c02e10480300d280f03221180314140078841c80a0203844120800201d481a940005c000340c0c8802c100031480e20614800700c07001c182c14103000980c4004803000c174004180ca4440d04100400d140741c122252500a101d003805807040075040da106c5488800400d950b44000c0c080c0c010350b007448207500c0d030 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 138123390 1250 138122140 138122197
    0x8040b060a0b0307030b040b010302040807050d0204140a020d11190c1b170c0609060301120804170d110c010f050d0f09030908060c030f0c09030f3f 65
    0x1e009042242405030f481c03a0992000b0020300c4001000391050382000200f807403540c400d00030b450544914401034000709107400104440c4c070960300f508a070030641700c00d5400e6050241228540c4203048000026039641218800740e000c640c2001141c2d07406050500003015000500710307030f0506800450030800461402410140f030b051440e90917811810f400d0900200307001074400c805038081d01d440011208843c00810400c03041c1c0c020024000c0d00020b060004110b40120314a200400c14081d1400b2440c05449165900e200542a000810113070f1102040403c066071210341c07881010982405002600e0450000801417400c3c0561802008408203e03020b540c60039030b11512420320380710f80c01c21a491480c44d005e4680300f11403240c0c101c54002c1c9000284551050421a441a08112800039141d52880c1ca42e04441d004504056014410403074160b207851002c00090a124071458625480c1d9403410815220715403402052511480f00103a50f04410b4098006480c0e803401ca007900c4819224002c0600c0 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 138124640 1250 138123390 138123409
    0xf120f03170109090302070b0c1c03020906040b0403151401090c03060f1401081b070311030d1104050f03030909060103020304051f020a0e010c0309030615031a0f010503060708040b06 80
    0x60030703410514000014a160281e0000b211688240c00b40d070226079540c0c010416500070000451b12a41292800302c040b01e41040d254401071902c1d080040c00c0462a00c0400e8140e00540c00c10425810001018800c1c45144446071409005620046c02144002c003444071030f81c43c2c10f02c0391600c4d80d40c1351070b642480d5a000307802c0b01025108040d2080303981d660394201007001e5480080e00720701003a4801c0115040700882130751600c0aa00c801e1413185811075954044a0a4501c182021040d01003808154400ca0060141e290021180e01c5a9626035040a08102244041040c1144664000c1150880716110301102c194425024200186c4a94a90070594100600010040400000740c4c41000f201640c5501034444100c4682e01c140010700b0401c01074580c46860000500401e580c4403003040060a07a400541c1002d044030b080c1d484c099034954508040c801050b0517007000082402c00c0290180c1e41c1441c050060030210010300c405d0400c904081c00e00b01780034001804c0e00701404002466501d5081c0c0c0d0 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 138125890 1250 138124640 138124667
    0x100213080616080709141507050d09080c03010c0c020d170307020115050f03060a050a151206050f0f0a0b010207240305063a02030706050705070f120f03 67
    0x240c40d02842c0800402070080380042e540d4010039085404964054071554107103041e6a069803d00c0a101031420800040a18030898520307410b408002c1400090802c0c40306810b070500588600124034203100710641001452006280241c2c944a4200480c5500c00360810805805a81c04526000d65040034645c1034604c2d00c20406ca07081c00028041b89541c1540840c030075a08070703500e14510546890801200d82c1c54074a22962503800603002c280b000302030758041a000b107092a40050310203400c0c01c1d5500300c8011640900c4034cd841c2803048000b030003506d00400b94401e40d540b19880107031810041e248009280507000c0c0d1800c0342c1e0f541d2140200d0b4000c1001380c1c0502000303c121302c015502e01c9101500d0507402031900000070704100100c1d170320b4284102441c003c440f50040c0c26645429100100801a002d40701d031003150700b0340c0c0403003102603101030007444003030101c95903901e80d00d40320b909041d0b00d0506194400c00580c4406c0d2001c0003010b52121210351180e81c450003000e0041c2c0c090a080f030750744c0c114000 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 138127140 1250 138125890 138125893
    0x100e01150e01060801050409020d02010f0905090c040518061c03020102070b0c09030f0106141021050f0709030503091c1505061002010b0a060305090712051005090a020310021308 78
    0x1010401c1140c07515514102c840c15038a50055a0300c82d010f010070340340c206400a40000030303030023440c0c01580117540c0900101e02629040c413450341e03141d0010b03603508816110300b94400d400042c28461410701c0030b01e911884081010b202c8560405202041d0f45000503216080300038a0000c1240c1054808c2d0100c0d009550416a0400d190a1030550010302e0307030082c08058442d1054191401d44900c0c18081c5100f11840c2019655001050f03806000e58a40341c03a16410800001010003c610a069400c0109004940000050300c0c50008021030510002802503014807400322420000220004100c50b41c0443c01e8680d80000304c14003504408000105400414810704142c410001083d640c0c00584640c5040390800c01854020b0700c142d08889113801090f8009000003000d00c0030502a4010640141070b440480b50034903a42c6070b00c4000003400d11402c440e150481c0d1440c0d4220102805030300d40080c8000d010b06664a020703070000b40c2d901410308038036031219000300e01100b40e10f07040401080240403200 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 138128390 1250 138127140 138127181
    0x601060f111605130510030209060402090402070807030f08040f06231305011a0f060f040513020a0305100b030a050c0c0a03020105010824070804080f040815060111100e01 75
    0x261110403a00d0740d01481e40130f000c6134810360b41c04101d24003443d03000c0d912170200503284a0543e003c0c001c2c1c056006280e150456003c200d01c0000351694030007422034901801c061a210900d5150080c8803c6241c034401003080b90210034040465094410181900d40c000c9000900c890311141c1140440e9840740b02c0400740c43e0b000704004d500c0a51046100e040c40c070400080055103442c1c890344400103118038100740c00500303114294001d414810003c203041ca5810104a0401d9a0340e000107030f4024801d10758401c407a0700419103072103868250181070b4100403034180c103140f481d0a1000036000341c000101911089134482022420140710902105c00b0750000340c0c01e1b034040150031f042c040c0c00b0703141c207108400592141c54000641d0640900140303d10022807298590340d903c0d41401107d5401c0044c0081c1c92541d41008007211a0446c40000d00092542602400c141c0b07803004145041800020301d958140880310b0b404420400b0041041c4007890045100011001c0d90f829000e401440e5a011840c0c0605402 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 138129496 1106 138128390 138128413
    0x1006290702030106080111040f050103090b04060f1401061805040b2d0d0c080d03050621101505151303030c03050712210e0601060f11 59
    0xb000801d410b40c40301001800c5548000d010061518005020400f0b1414204803200409090804002c00c41d1240c03070381160b00700020002007070590784004221005002e030740400826154024105819030b140c020180800c0700d1003130500d0030f0040320000000c15180138080c2000801008d0721501340b1b584c03807011910030400d41420740014000d01c44111081c64540c00420f50b41035000717084121009161601141c244a2151180d1003054141020840c1ea500e8070100c0c1c404002c900644614500d40d10350102e4100701e29200214011810b280c002c0c0d28105032502c108059800480e041003c112043c44460703d24814000d00380e200c10382c41d43d81080464010388102d00018041d040c5149006004d40c0c80703842840d141c91141012400c0070400112000c400075074600a41407200702002603500084845644100500c180c2040241003009601c803030b8801c04044600c26104000c0705d0321603c1e032 = true := by decide +kernel

theorem cover : BRFrame.Cov 137949640 138129496 := by
  have h0 := BRFrame.cov_init 137949640
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137949640 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137949640 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137949640 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137949640 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137949640 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137949640 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137949640 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137949640 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137949640 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137949640 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137949640 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137949640 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137949640 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137949640 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137949640 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137949640 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137949640 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137949640 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137949640 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137949640 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137949640 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137949640 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137949640 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137949640 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137949640 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137949640 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137949640 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137949640 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137949640 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137949640 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137949640 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137949640 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137949640 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137949640 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137949640 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137949640 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137949640 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137949640 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137949640 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137949640 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137949640 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137949640 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137949640 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137949640 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137949640 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137949640 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137949640 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137949640 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137949640 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137949640 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137949640 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137949640 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137949640 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137949640 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137949640 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137949640 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137949640 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137949640 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137949640 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137949640 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137949640 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137949640 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137949640 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137949640 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137949640 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137949640 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137949640 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137949640 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137949640 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137949640 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137949640 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137949640 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137949640 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137949640 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137949640 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137949640 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137949640 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137949640 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137949640 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137949640 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137949640 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137949640 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137949640 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137949640 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137949640 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137949640 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137949640 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137949640 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137949640 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137949640 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137949640 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137949640 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137949640 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137949640 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137949640 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137949640 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137949640 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137949640 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137949640 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137949640 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137949640 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137949640 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137949640 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137949640 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137949640 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137949640 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137949640 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137949640 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137949640 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137949640 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137949640 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137949640 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137949640 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137949640 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137949640 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137949640 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137949640 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137949640 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137949640 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137949640 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137949640 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137949640 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137949640 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137949640 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137949640 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137949640 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137949640 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137949640 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137949640 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137949640 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137949640 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137949640 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137949640 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137949640 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137949640 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137949640 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137949640 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137949640 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137949640 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137949640 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137949640 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137949640 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137949640 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137949640 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 137949640 ≤ n) (h2 : n < 138129496) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
