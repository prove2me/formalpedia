-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4792
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T13:44:34.731698+00:00
-- url     : https://prove2.me/submissions/1fbf7016-8103-4be0-92fb-50dc9702e4cb

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 861690647 ≤ n < 861870503 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 861691897 1250 861690647 861690649
    0x403020f15150d1106310302040506030d1d0d05011a310e030f030c040503061b12090f03040905040b090601030206040603021c02040803070b01060e012a0506010e0702011109 76
    0x99041c0e04550013007400103041e0740240c4250310240e80c1103c80c82d0b450f0340c4107000d1b45040e41e464642c1e400103078800c1d0300d841c0208031240f42c0020808112005600d4000011407010303804001c0c94030311100d49810200b071000f0000002d60078401c84545503c0003029169100c014414001d8079000c00c1401170520101c54803908072690302e070811481424040038041114640044a1802d501a0648a640380c440100500000ea5a060090b1050310f0702a01201e01c19034900d0040389611100180011510104025204500080e2000580e00050610444040021501d0b4603481e5038890340c8400100b9a50700248000c2004408485411080e42d9005040650441d000070711248958800e2606050380090198004800d4000d9003030707041c480f20b1003191919a0740e030300c103900d903408080c08460b589a00c000100d662802540c20703101c82c80301a074a03298030207110014111203448405580f210107111440d40000500200300260181c00c00e030410380c4150400c80c4001e070030360f51489003802c00441c0621004802e = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 861693147 1250 861691897 861691913
    0x30c03060620010617070920040e06040b10050918090717070e01090f0b010c031e1e0f020f030405030a110609040f0501061403060306010e0403020f15150d 68
    0x85002d04005800b6101909440368014011a0700101462580211220420b100030400750202e5542800910503020511045c507240320350301d44112070284041c001445483d0540003015803003803010303000003031840b00c00c3d000405000d642c2c0e920100107403002600d8581c13401c103415030305800094541144c0c182d041c0342074910b854603040e010300e000d094401a10b0544d1440104100402401c000e51103184c40d50b11054210058491464001c81c1d85003032107061082548615042161140c259030741004452030321850401c2803010000e0302d002c1001c504011070250811000c03603400d102a83c0c85c0d01f101040c017148044c0c20710740d00c440780b40d2041e0001c3c8001c02c030b17644022a03072584195004144031030000110001400c0c5000b012001d82c0c220f031818a030361f50103091561059041e030340b0325216181c85041200030159244000c40c2c1183c3c06410820040200032601030400e500140700e070050312442d10303210307000d1482e1a801c410900084002d50040c02000d205110080c0c20151003030310ba0005031042c5441c0c40d20 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 861694397 1250 861693147 861693167
    0x2e06080d11070906060e1f0906050d090203100b09010f140922230a081204030c020904080a0e060a1709030c0703150b030c090109090206120a0903030c030606 69
    0xa00c264581034952190081c80580d0203080d880200f080782d281c59110040043c0000c03501c25000e008161240c0c40c2c4541c603201542d036401c7c4241d071500442800c004040340c10b500b00320360030292070f0749070000100180c3c1c05108942c040441c2c0400042c0f81210001081141081a4411b10703440d001e4030400d000c100181d8920b880199030948010b2101e440340030500d802c0034034641c00c0c000814a0f14800004004c01c840042e812111a40d40c1c3c000d0072003020172605d4075042c44200013060032204018092021000f00c040781d42c072038000c1c10300303659000181d00440c6200108403002ca178401c0001070034628154000004103d80c860a0326840d0908000f000701514030300d010400c0e8404400001c00041c1e00030b1003041201c50288844050380c075559624030300480600c80e0701c0c0c0d080c004c10b4140002d19905040008201117898402800c802c21a4603000c00030740100700c4441c05a030403000802c4805030704408030303620700e00586210130b00140c1402c1c00c1c14010125120401d10104060404400b00320540d407101d001d00c = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 861695647 1250 861694397 861694423
    0x40519051b060d0e061e070c060f020c0703080a0f030c17060f040e100e0f031e1608040303020607030b030606040b011205070c0c0e040b07140c2e0608 66
    0x107940c6219120000e50140201c5551680c003e0500d079050368440d07008a0403a001e643c0c502c2000d00705554030001c1c035422520880d03900000a4085200102143e41d0b40c0100c0c0d071100030034100502c0c04824480b894140301c0550419100c070759002910f03000b06640041302c1546806a440c00704005504603a0051145800e2007241110f03440900103d0601c2d540c501207030144010091040002c00c04c804035a0340c0302da0b024180c024246241825070b418205021a0404207003a82001451520b900c2e50040800180c1529a02c075040e2000d11140c80d080b01002e0b8844a168003c034107240e292403035490020b103030040c01420801094244403d4050340e0b1000101c25402a0303080f64041001c400400c0101e440c0d18a250b00d1a03552800c0600b401420354210311680000c0d8040c110907402d440d120455505803d0064a00034410030f40d101c00510020310500c5007100244c48003c0540c5404a02c01c240c82c40c0482d40050b1035417500910341c00a4021071040c01c01c0034a5100903005006081c6012180340d150300400350a2 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 861696897 1250 861695647 861695683
    0x6031415030c100306080705060c030d0e0712051b0619080903071b0303080c03070f0c0f080a1e0e03060103080d0905060403030209130b100c2904051905 67
    0x41501941e0a110400c608a0b0240c062180704018140040103405640704a005501445c080418107003070000449180400000065150a42c09031591006140f80070400c2420300500c1b801044501c1100c400541840c080d500509503039600b02d0a40007148410070641c4c1c03041404000d03a80d0b80c10565103d14200221908101242d41d0b1040102420b51007002002450f00080c10840201302c0b41d400031744000d07a80603135140b052955405503051020320003a41d01c078012071b6100e03a210318090300c10201829030310700c2070740b03400500035403a500c400300c0f6007010544002040303c4d0b00c49051882801501c0316681c0510f413400011150a0802094450006000c060920b0200181c03001701603109801000740140d0000c111042d5142500300200250004158944210644040042e0101780c0d8056031211103801004030941181c640000e0b103001e404080c00701c0c1c564007480310000d2a86c80548040d443d2841c4004a40d40074945407424500304001c0305241d014030b08000c5800400b244d400180c50799840c0e800e03a54 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 861698147 1250 861696897 861696931
    0x30601060e010c2a170c0d031d0301061802120708010b0a0e030a0503042d050f040c0c020a06090f2408090f060c2802030306150904091b060314 63
    0x104403021880c1c003c800d81d640044c8103000410403843c41e12203012041e00c4081d1440300c400e0a04110308800d0400001e00010002ca02e58944c407030000c40e40150301000100000782c007956400f0f00300d5045000c0c1d0301803549a0703404100003508541c140c021030f600005038584268030b50b0400302000100d00401c2c1d022010455011000710880d03d08000e01c1855a4002d0304594a5035601d405001900c04006800c040030240d04c1c000502c481d41c41502d4500703030781d802081ba400003121041408000c14004000c90304110147c420f030000760316000b96080c007030f02c5643e031010281418000f40e45a00741300d541c082000002d9103030344400c0030901e907512450000800c3c501100c454031a03424540ca8006c100b0791000540c05220180510f01240500802d503895038403c4445010b0051403010f40c030404460303440f0340540c104100103401031902140c0400218014201c060802d10154003150880c1d5802c04110341620f031001480442805c030701010002001c2c01d1030144041c020207515078051140180850703078040380e8111 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 861699397 1250 861698147 861698183
    0x503150a1a13050904060510080604031202090102030d060905010924060e0a0f090510050102011b050a2102040302011103040f120c0b030a09020111031206061303120c02030601060e010c 81
    0x142e400d0080900418190320780c1400d0900034021700e810f4540c21956004903000140050000c07640c030788101e4150301c0d07000c40c07420080c0d41c420107907004040480c11800301b004040e00d4512184100d101400c0e03100c02c005669810180c5420032502000c0d00c00560b250400381d540c181d072880d0f0b02403000b41c44607860031010810b032200c0400d035540c123181c001c0013090700325a81c0070891540503400a4895507449414407841c555410040e0700301c80c00b910195040603800303055561201c1c09500101a00380040c07a200183d0f1881c20304c221341400d019400414041c0d00000c08200350342c2d110314042c003503400741000341d4a030518180c01c1c1030409440c2d120b80d29540c0c5802c0c005805003e05201e9000040920400e8140e69150100c0410000d02001c46d00f2400b01d81022a8407440303903400005c0c0c80c210f01c4084442038598860404005143d0050301e03000001c051030040200000380c5400c2c030451116400d40790005110821310400d0f0900005030083c0c0c08020403c940209a41e920541030310781d107500050410079680950b1 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 861700647 1250 861699397 861699427
    0x11030102120906160503010305032b0609050f06060f03070c0602070b041b0806190203090c0312041a09091f170a0302010f110417030d0c0503150a1a 65
    0xa0560030700d242004007008100c2501181c4184600a120b007210114180d0000a690a010a00000d000341e4000e01c060b4070324040705554540d407014240c444d0392034000e200e2007080540e84180c0200030841e0b112010f04c0304665603d1041a003000c4203d501c0c2d400e12482f00b91301101400000c184a041049480b8200e0900200398102d27101300b03400c6201407109240608000c0d0881d4054074001060070140c07080000c09140c04107140d801488600c60641c82803500507403880c043d41014108072028001c150500c881c030303602009040380c1c0c1910300d02443c0d01d035460500c8142090082003010a140b15003007041a03c95582c42c3c1e0b03050b92140580032056417648900c00780c1c0100003660780141e64000d03280801c40600031070005041c0700451080d4000d00108609a0140c000d035244071000d0090804180400c0c040620030f80b502000c0141c035002244d00f04859149100b0030b6680d800e003904045280003081c00300d400d1380186000090300c000c1e06d42c7d13400a460300b102400e94406400c601048040003145054002d1528 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 861701897 1250 861700647 861700657
    0x40603030c1b0905150f0d02030c04111201090b090c0a0507080f120a0204090e1513151e1d060c09040609020706050a1508030306091005060a09030215090d11030102 72
    0x290010442442c250185405032100e440a45e8407420300c100c1800ca09142c004140703079440c0e03400f80107005074150724002c2c0400b83c04007580f50b00070b10b802032003210203400c0ca510740113008240f001404240c0d20952428464611000b8003c01160b1408005414205d9002011207003126032001030983d454000020802d0507024800721501c503400a501403140d00b40091b0094800c4e0361070803408209030000c0010b026942c003401000c403566101040001642240408241010135006415900c002c1d021001c04a00721904c1200264a110102c0417a010100807403041003010062042e252108001c210910f41d5203900041115040401c0001c4170b0701da80d110398102ca1300500102d082992214070318034240c0040e2504444800e009842c0c05956814500c180e178429040380d050382c002d9851511454284605d134100100311020b4000410070004054076410018041005244d490b11109411481080b511a4030a084010700401c02d1003442516540d90402000c1f86500c444010311081a1b840840d0280c021 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 861703147 1250 861701897 861701909
    0xb160837140a06031e03020309060a020601081e1903230702270c0c03160f0308010f0b180d0b18010c0c030c031b021c0b06040603030c1b 60
    0x11100d0000c10380ca265421441100154280c016900e039222041c50044895504c40600620756034000c00d04420600b041680d46507000e84180c91400391002d02084d51380e0b00ca113440500503409400100041c0600f408403d00680721070302c00c2c00ca003050f901062661850b0501951000d150482c414008060040c0444d5050300d40804d244d00e01102807000501c01c6070041d0348168000c180c0c1c110314207210b000c154402800405030401c0b03010540c035840c1e8583c009400520b002d803a24481005180c45410511b8020041d0a100c0c0d041051964481d2038000c102ca80306034480c01a0307010252b07041c064203100031b05444541184089030203c545985c40002c580180e003000292110440e04184510440d55038003034150900440000d2040e0a003965003295994440b000c0640046c10011070030380040d100e001001c00c4454140f4040c00c0024203a0001442d0614042000200600e0401c440e820003040c0312415910100c100c404001840c40c58030080c00c103160b0050000c008903241e4400201e443d4020a1702070140c00 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 861704397 1250 861703147 861703231
    0x518040e0c10170c0408060730020319270606030605070c030f0512011205150705030717130f050717011d190b06040204080a0b040b1608 60
    0x85240b1000c0c03c1d1042c84400c26503014201400103075910720396421601143c91102c001c0100e40d50301d00c001c4405443c03005446c00441c1d604000c1003058444c404c0a442405504840140e69003041ea80b581344412842000d010281e08041015000500c290304003007080f290403030100c4c45a4081e2a1440080c44290401003c4502c0d100502040980c02080940083d00c41d44414001140c1c4d07190542e103500030044084201841c803001806028202012081c0711840340703003101c03a420745616240a084400301ea01c0c5000403808410800c206900000341164403078510300d03850b610306042001d030021030313418007016000c000c60070399403810850100300740c100920489043c40140b10010714601e000c3d080c0104409a01420411a108041c4020610002c850500315001681d02c010703070340b03521010380c4c003c0440f64426828880000e55041c11b02420000341d00c01c15149299241c54500380c114420090711200000d486482100c22481d080942c06403c0007098048000b0151440e5130640c4e07803043c143c0c109074102 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 861705647 1250 861704397 861704419
    0x4020706060e10080a0804050402130b030a0c0909091109090a020a2c010b03040f150f0e070602031e07110604030303020304050f01051e10170a030e010518040e0c 71
    0x503641d0030443e0042c10005142201242c0c2d07201059039883d1200c1010744405410002001f10340b62513401011018829000c01031401d603560b4050341d09030400c403800340b10b890721840e4901200e6440140f08d0302070407602400f0030a080050300c41107900c00e1000308040c0507900340b00128400400801c9031086055004040c0304a040c3c540340c03900c00540b020710741d021140c40b000045050b81102c5090350ba0680d15000742450455456448040c090f503000c5505969030281c144461040e00614080e01c8100d0030391000c0401c02c2d402643d8058a0300c103081e0b214a0464100b8001190251864408074140c00d14100c0c4c29900d03040075040c0110300720f181408940e84400c00107400804c141e01600550300c241d0040301a01c11141c1d02c40d02030b60a0301c070300b2644000b000068140001d0f804e40c8030741d11030b60004c65100050803903540392040d412800360740c0001c8000da03510103034030f00c000c15622a81c034000d0042c080c41c01038142a96096181d07580102c100080303115507200c5180065408040196207134180000b0120a540c07 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 861706897 1250 861705647 861705659
    0xb0415200303190b060304030f05090a030b1815070c03050c070e011409070905010207090c030b0a1706150a050609030102162108090a081b01290910060305060402070606 74
    0x10503d141410282c0a00740704407607103d40380c4582a60f01ca1a00342c0c840d00d200324150442116194803a954660384000d074010080003082000d040144180b000c4086400e055410044a624100114503810000b110440401903416440914007101c82d40c94241940c6480c06803c1007400c1084542028817800264000000c1021010f40078050703400b02503d00300da0507240c00000f151809400e010380b41c09a4840e02d8100a800340c0780d4003442c43c0300300d03600c0d0010b0200e000354005690804030b83e0202403030013958008140c1410f41840281d8002203032001a41c10800800d02140c540442441120300c074020210341c045068900b901220724641d4552048040b401d890f01d00403020010140c44081d40403110f41010400e5030240128500406600e00185500c24082c0d640c0881c42d13100c0000d05054140c00b0f61003900308082402090818060010500d06508482144d4075004a055904c40e10400420050140c85070701d120f24202901c09500d0302080503035410000ca0083d2040050007418103107050400260 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 861708147 1250 861706897 861706921
    0x102c04060f0b030f06060603070207091b020d11210d02121006030c050318010e031902060a05011202120c15070b070201050408030a09020102120406020c0102070b0415200303 76
    0x100301c0e4009070410420300040203241c1e80310221801d0244039805440840c505113820005541c2c00b10252041f00c9501c1c1d120084841502c1c10541c01600300c5015090115245030181304292106401d0f02d044040346003000012940d40410f03c110380288001c0b010042581d0f0001b4046030f031504078000042d59280701102d001c441c004001c43d085003055000c010b0100d840c921a0241490501c0e00e07640d103904540f031b520201c81a045501c03500960565940e07220810090b020710207003000c11292031064103603500b00e24010341041c10081c240c840c050721f010014000345c4041c07943d804c5a140c05a882090070300c0140130440c0b0b4450b9801c180303a448408003141a00c010710a8000b0300302980702d00c1600140e038071001e070160309850382981d0007001a1300900c001403201342c2c04e6101c918068014412900301d4107181816400d180c1c8181c1003100103800c2802c0c000d08a50b0100900b10060040c0036002e80b60a260042c40619040b908070b030742c000c00014900020003140401000c0601c828100160303503580c1489140f4002c = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 861709397 1250 861708147 861708161
    0x803071806050913060f05010e0d0b13140c090a020a020106091505011101090803010302060f210109050708061509010507080408070503061b1606150608150603102c0406 74
    0x40300f41c2c030802c0400200c1c0c13114050300c400c90f62010545112582050019a1141790f40700e01b0b6500130603140320b084003241d00022014000c482c2e6034103035000c0d40c1d414107040790740c1d01c80d941440c1c4155200c14502a00c68490342070b12603200034428801030329506201402c03405044141d1184042508080c00800c40e11081c500e406c0c01c481c000d81340e5241003000c0c000c01c58242c49010780d024252101c280010409070500100501210308220340c00c81c0b0348a8010704070180d01b44083c1d0507000341804000148904913251242c243c10410909001019161040002d4081c00c042c80c4000a81c10002c111610242d00842c29580203a6200c01510303262a15094810343e50303205441030500c00d11412002c17406600180310115a52000031a4446c07a183e04101d030071601070620b101c126281c5544400c4440c0100c0042c1810014040c1661781b01f0290a00031000012400758840441c03051000b04140010303000d9404103030040b00d1915620200d0903030310f45240440c80d84130030106151642840200002c010a07640034032 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 861710647 1250 861709397 861709399
    0xc220507180f0b0a030207020607150b0906010e131802220b010507110f0a0905151e03060a050c27011e0f031e020408060f0717010308030718060509 65
    0x148540e210b0030109020140e124060400718100082c0b10740314800d400405c4030a002419952038494181c0d113024116015442c685089941c0e000c080e00380c1d140c070b0007140d90010801d01e4a5400500c0610000301889840456030071030607a035400e20040c0c1d101002242c07070059001442520074030500d5242c2242caa04500004002e41c0c54000b194110f036000d54107981402d5080b007045440780d010617050010f081c43c00740000d5440034015100003580c1d01240142442054a0743c008000c0d809100d0601020310380c0445c088401c450300702411880368400141d050303880b21821034040b035640c8803540303085c00e207204103000120b0320320110000c00b42542d003109140e03080210aa0b12603940c60510720605500c80c0000380303400001070b00402d01e81c0381c151180d040102e00200000c1e480f010842074000803070482e44150710a03002c60300710b9010041d50820003000c4961180040c00c00c1141d41a041c3c00040c2312079414040200440d001002181c14540300c3c000f81e4545e1511240c0c0e03141c00f80d8880d030b40036040d900035190715 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 861711897 1250 861710647 861710687
    0x405011d1c03020309042301151707021b0307300807051b01090e070509030c061804061d0103032303010e0114150a0c060f0207080403030815030c220507 67
    0x81000c00403031f068261210054034105d006908140742660780742201300d00c071420000d0108001000e5045021048e0082000c0d400901d01c03c4030481c0e0b41464100100030292080e084010200582d00442c085410048040020300c0e41c0c42020342080313450181c2d40500506420300110b902410400e000510200605900d010031002042c7e503001102c000c903a501a03c08101d80c8003010414060055002d82448040102590740602401000c40c20540010b46840d10700000c1a140f60203a0420348902000b51a15101c41c0b1410f0b0a03010382100c0b02c01c01031000500300850074812100205800280f09440b070141000b2079076950f969542080505c80a01440d044c03d19280405909403505000c940152000c4440c92420603281e002c0548154481d40802d581c0c0c1d94440e00254110b81c901d20003806564422804143c489003541402040010000e01403520410001013002e401e6400058061a511007110f040051b002c5910701500071007051f200d41c40300c490070301c0140030740c40f5000301c421030402489c1994 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 861713147 1250 861711897 861711911
    0x30d05100806011d07021504120e01020325050a0c09050a05071805190b0d060602190f02040203070c0b0a09060c0e1c0f120906090603020405011d1c0302030904 70
    0x200d8484400784a44c04284141c120900300008040c01425844000c900607103045507121120307800b4002d000c0340e044642c0d1400c00c2c1e050345810b4002e401c0d0640040700380b00840c101405031107aa414804c40c4481c2030411101c0401e1311040100400000d80b007a6404034440c00003e5032600000c1c0078102c10345102409906000000d11020310030300c08034080d8040098500d001c1440c203014040e000504440044610103903600115001c4003220003080c0003040f50f44001031492405000900703011801d05614107002441c07054034040f40d0700203a40001c0c640c0441c1d0050303a9481e641c2e030964114401c40307002400e00c840541000244100d60340b05000c1c541c01114244080400840111070b1070250b450711a40c0519552185528004040c03203040c40e080c0718101c4441c0880341d58480300d2051803000c3d20b038800150f041d031040c40035660110303210005160605043d804c3c1418000041e117510010004104142d04500301da45107aa19242c20514072041024841800442e43c00d0094403588910103240c09107041c03401b = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 861714397 1250 861713147 861713159
    0x1002070308010617160504080f0c040b090610030c02011506030c122705010e03070f14010203070f032d020a0908061e07030b0307171515040209040e030d0510 69
    0x41462070426103681e1800390b40c445a000000178100110b180400409001c082080d0340e04010301e01da40d0a03113000420301c00f8041c1e020042980da007041068040c101c0b050a122803a141d00d1000380c0001ea5908000c00c010800950403401001300701c41c5000e90500e00c60340010b0b900d4060748075600d804025030355420546011200351080c0e90303405040e40c146808000c400f01c010401111a44143c5101d04004103c020009400e94510f030032902c13003560300018840d504420040d0b03c8560108880035800254114609000098911a0300c1c058480c1419110341819403050010052245150985110100c0c0c1f072692002c070178001e4001001c0180410078662011480c0e504c00101c041c440c0403030611450611914002044001901038040000d044e00d903134030750a0585d424040403020300b41c041c21400d83c2a940b498810300c0c0203100c00c6030a450000c2d82040c00324258100d40c41d9085d1100c02c1d200580d65030800000725000b86800f03241d01c3c429000104198a42520940090340601e8282c1c542a00c3c20b07440d44 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 861715647 1250 861714397 861714407
    0x1e020105040215130f0b03190e060a09020619050316020a0c2705091f0e0a1209083018041802040203070810150507060e0304050310020703080106 64
    0x20700e010b5404108085204040b9801000600440c0c1d1000c1400c06005d6680c030400c3c51000a40c0c100c250003203008000c00c50795032070400c2c0408440e0150841404170300110600b1940324400901b07840400398445040f68203640320041242c4004003c01544240c0c0c0c154694020400c0d081942d500480450007e009078100b03100241510b5032a40114401c038010b0b00d4003c810b020302944030f0100c1c0c0c440c80803402d64034040d49107209482c8038a1500c0080c040007012854114452100205200006480c2121202c40c00340c0006401c060aa0b03c102d017070807a24280c54066403401840d03030024072035118a0143c0d40109a1280501c0c2c10500b1a00000000c40d2000300b51640c14000c1c00c03c4c20b80d04104039018050f01c1e2401e504800d1031005501d40e20003980d0655000f04040c1ea204a9004010a00a10620a074030303048208130360003080c00301d40a450790b29241e24018100c0c441c00101030301254448400c0d0100307810038000c0380d0003048010101c0303a06a070b8070042c1344041e40000c40290045484035000145040c020 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 861716897 1250 861715647 861715651
    0xe1003200a051801090b0a050d150b07230a0c03020f0105041811040e070804031e020c06030a02160c23010c030f031b0504050906060a0203070f0303090f031e020105 72
    0xa910b5160500740c40100700f1142c040c850088034100041413500184507007441c00141503002580d03032269a550f00c03108a100c10381c0c03580034421212403100fa000b000031003080c1c0140c0343c0003075102507010424034030210f400c40d6050060209448900822080710104803400d007551741224401e031102c0c10028241c038011358060041e40705401411983d02c03a2040031008603802142c502082c80c407810300f01603c0344221400302c14106c1e003410104401100780800e06030000e8220001d1002c02d040e001510400d030344000d482c1c40072580400c1c010000800803401518aa4065031840e00784000004400102800c21319419501d0307104585000c00340c06010740d40c48582c4003041e05403620603100e00340c441e800340e0340c21136002c1742d01500c1c0c03010155100c51840101e19200302e40001d105481e030f201c1c2d80703d50a00701000805c200c05070249119000c10095040050b801009556900350840b81d03020070200b00d810181e0103065455801403080180400304010580c0102e49195004c01030f02d0451060221310300143d00700c0b441 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 861718147 1250 861716897 861716917
    0x110309010f0c080403080d0b03191203021605100209011106010f03030c1a07020d120e0a020105070c030b040b1503160e070509090901020a0806220203070e100320 71
    0x510110814281c042c00103020224400d4052501c4e04c2e40d2a200c0c00c07403542104260f009407c1d01c582d030340d41d01440e0801c0b0740c0c4180000c400c0002420511642c44c0000b080072a00d030030050680201c0c404080045018042070f40c19000340070f5900b2581c092a04200960241100740c0c04521fa4401d88004140300241207070589501c4002c4135022419034606581789501503104072040d40082d200e00f00c031034481000d180d000d11050b8004002d00480540d002d4010015400d03207104a5290248120f441c10000800c9030103a0340a080a683d140c126080c1101e9521403504094005040d020502080241703418100d44035409100644014240c604209a100d14102440c1c60303240640e20014000b125a205055401c8115414000d16004030640820401d000417203800c1110f950115045068503084500142d2141e4121500c43c808891103800b80c2c9030610111002a42036404400148040c1c0921014004140c2c000d010340d585a10944009015098254030618550400300c1c1010080019500791505814 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 861719397 1250 861718147 861718157
    0x30912040312080a020702061306080a0c02070b03090f030307050703091406030a0b13060b0309010e2808120c070204060801020301060e240705030a080601180504020706090b090a0311030901 83
    0x10b541100d00102c090000010b4076030800c0158011703500d41009004881c104202180402c1c43d00d800039094080c020650590070f42404034480209501040704004d542103081c181d07441ea22140021881c00c0d00e0218950883d02c00002409640c41d0018090050341d8030a40d1031000454482442005040c1160000d94004400307102082e9442d00980001d40724034000380aa00d0314170704207062141690b020b6808143c1040002040c040540c0080c044d100f2000c02c1d240041030f91800c50300045841e1078030f02c44482016110b02c0c80d58402c1085441c211806010a506a600d0f03e04040412000c55441044200d10461400b48000303480a018000e903070480b4801d0311050b00003000a0180200c0da03510310490144221010b607031140081e41c40016181c3c031405a001141c443d20340c0c600c0540044809002c40d41032007100500c0001c0d1804080f02e50007540d00c1900e000d070326100e40d80760203009080c0c0c030b050003030282a910b02009040b902c005a80c1d10f201d80255102441810300900c2191244500391034203000071 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 861720647 1250 861719397 861719423
    0x91a0c0a0f0e01030902040629040501200a081207020d020609120906040e040525050d06470604030c0e130b040506040b010806091f0209040905030309120403 69
    0x40c064001191041c5044c1000f003001155640010111105a0498070520b072210124a005406d19119103180b80502200300b882c09081ca000640381c0c0172005001c80c0a140340070701c06030313609030b09021409100758494034007900d803a074070106544240703802c50301500107200d40031803015542d00c0002d240c2c0c0206044406010360003103050041c403007640a00300064001c00300f04800144480744621180c4902d010307901070300000003180010211003050b1005490342c000003840910041c1c0c0c501650454a83d40000300042c2250016001c0711412920101d82108100b2a41c0300404000300700c001c81080050120440c009001000c00c02c4210b00131400701510003030245005101510040340d01c45c1d0090018100307140d580c000c0d82da482c0100703c0215030403280741e0011742c180820000001c40e15800b60102e000a003045223800480c061755500302060507607d10480c115078408c1d20600d0b604841902d003014100380300603104c038103109982e6441510543c10f14415000c8100c107001d42c2205580a49620030b07001c204403 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 861721897 1250 861720647 861720677
    0xf0c060106300e01420f0e0403171302012006060d0807051e06010501141c15090e0c030105060d080901050d02180103050106020f07030b19091a0c0a 65
    0x2405540212921596500c190600000c030b100407000c00400705e040d90440d40c45806800c0c00c15540300175541410401c401005110f00c038a0b00030303090140d52610806c45d40e580e80d94103007103604e840950500c00d80d01401e04180b01c019040c80c600c1e042c429000ba2580c003144510f20ba50030b800f542c900d85114415402437804644c0c146440300c0e202c40c27214001c03210241403044d03c0d03c0f8242400411041007800150480b0f50700800f031030038000b40b0300401e07090a10110081100342588076900c5420301c0e0000d5080355802810540c90725a020071048410b502880360700b00c0d21803082400030310304138890094500c01d00c03400036610716050042c1445014041d2010000d40059560750400783c1203549c07a10306004060040380c02854252010300740c1a6020f0300c0e0700889410080000d4201d40c0183c1110046400c0304c50300c8a54000002944801c4a0307001c02000700c582d60b51001035811001c451005000740b07040a00c29014402200e45425110080505107403417511041d03040e4445120301032802000c0360143d40c4079202 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 861723147 1250 861721897 861721901
    0x10225120f1a010821210916030305040302040209040f020f12090d090303230a0c0b070306030201050412030e041401031407050310050c07060e0d03060509130f02060f0c06010630 78
    0x145c4d841c0022130341818800e225000105d40740000b030b0305084034941c003008132201d03081000c90015a40b080320a02080d0454178000d100d4410303804040c0c01140c0000d002e0b4802d44480d8410f20340300d0000c40045464241054000086910112000d25500f00ca1004200c00c5500400d01c0603001001d5204c02c546185140d5054981500b0b0f0302080c074640800d900c07500420011070005291304c50556a404400c0d0010745071002d011040034100808040c9003140500050760400121801e46a14180b02140c9101c80c1c40c0842d14480a10381c0c1030340240c00c04c128002d584041d031210b141a40d100343c6413101c40d40d0000d10b04036901c000c64452103a060780700c000d4032504181594000c5420004030b92889140041c50b448000c29030710000300171451039010b0810342461076414420000901401c688035040c600b081840724418140325071000c1c09802800304036004640c1c0741c00445000004140c0441d41343c200400203140c03195400d01c04d80c800310700c030b04440c0030444465400f07034840a00400c3c807414441444402c0400 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 861724397 1250 861723147 861723193
    0x320090618010908010513030306060e0a0b1602040f090203010b101407110d1b0611030909091e101d06041115040321020705010225120f1a0108 63
    0x810f000d02083c001c10112020300600740703d0317440a0f01180c078a4105250042c00c490682e4011010003800c01002031040c1d03508040a070031100a04010b54440ca0344104020700c6600e0050b00a6115285c010100f10b10f0308142c103c02a5640218001c000d0400c0c0c000600c007249001c0c20f0004005007440c103403040300d41b881001030300406000d864500c42c1d40c0308140c08100411203160041e206084210740ba4405000c607030540c2d0000c0c12040ca00b0401444c1c0406110f9980d008420070302d413144014070000380540c0810001008103c8140319201d0800100d107d100d40c842c0515004161114104003003c0ca03810100c40e0300e5084030079600010010b55803262a4004140310041c0800da206c807450100514800c480c0d806440a14003468244003d03140403683d12603401500c1e141e01d415500f0202040209a0300480c417400c20b84070b48911081e070413441c0c800d03251402140d504022107400c1d50b19001014807244041051110748520f0005640c103c0d102c650307583c1001c0034420f0000303035442500d004c00780c80c20080d030b026 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 861725647 1250 861724397 861724399
    0xc0a021005121b1303080d0b010201110409110f0a1d0604030f020d03210621080703050a05090d200103060b03070c0203031b06041203092003100c0320090618 69
    0x13030401d030a5041e8424011801d81c400c1d1241c0e000810b01c0400340b845481240120b8100740020807507050b070a0b81080884c0078502c18164401c2d5500f0304101c68580345c000310362a5500ea000e1140d1b0b034281d0b11502801c1e00105415a80685036041414201424100c080700d081c0d0b03401c911341c0340e008a410b500b0403285003040e030412401c1110303403112400d118a0044915801c3c042c0d216005c51564104079410058580314514411013102012215001c5200d6008a03011241c042c80c01a41c6c61094420654442c031400e140c030760704046540d242c7d200384002d904181d0194004540c0010900c0203440045007a81c00320700508a00c5d441c1040400c110b54000d0321a0211244080c060700c0c10140d5803001c45c843d11600b203000e100103401400400041040d5281340d18070070400b5040030040c000440d04d80501c501c1c1003007800240b540420910f00545d075020450051703c1c00001800340041c00d21000000c000c1c01d443e00c4546031140f55000c128207185c000c80c3c10380d803a40030003800160405010b103240410316a0248055 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 861726897 1250 861725647 861725701
    0x20a1101090309051c020f27190f020310060503070c1b0503010e0a0b1302010e12010c12020a1d06090603040c14010302040509070c05070b0c0a02100512 67
    0x5451045401c0c058810054001d03119407105500d81410300c0700040303e0a604170443d00c0350203524401695003040c0c10400d60382c107450f00480c2c64400c8c9000d40c0340a011100c850301060b2444104070440c00001a14000400340010501609085a00300d4085c1e01055501810800c000700e42070003282d2040b00a594000c29a15204c2906c655039213502000071b4207101c4000851201c08070034045801c0902032240d180014200a150103c07140d1910030b031444018040880e5600001108819a03100e21196900031600030300c0404055039104009008101d40c45464011070003d100151b80d01d040391094540c8003030380d5121400342c11501d1711450a0440184d80b800e1f48460148100c010030380319440507502c01c42c0714000b0b80c42c02030700300004e40006010404010341050700401090100751120b03264240c01c00c202d8206561811481c1ca002400d01b206a08600240341001c5850510090006031842d2094000e6600885000f11014210fa551013100c0c0c003040d54020340004101e02d00e442c28640000104080d410b = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 861728147 1250 861726897 861726917
    0xf0519120c0509040b03191103010f020c0309090f13080306030a050f060a05010e0402060d0b030a120f110f15041a04060f0b040b03070605090604050415080610050102070504020a 78
    0x4440c084400c0c0050707040000d800800c0307401050516101700c6010480881c014075441d0a10011905aa204d600d001404141701810408454800350001400031404640641d15110b401c100c1035541d4128160192041c41c140007c545c2100c0000b07222405045440c541c4954a6041d480b4903072654001b6090a4061080c00c041c40081002030007030f000d601d110400900f0390360424090080580304180c201c50350b6481c1ba5070500005a07184c4086841050658a022910400c4400002e0400c200f840700a002d2031350700010f21000325401240c4040c104a1901c0e0703078007180d08a461030b641e18811052030750081d6101424914210060300850741c6c1c803d11880a042001c0c0402e103020210680585040303644030f072034020120b09011180607600c010713070041e00c0c00c0004074bc1c1c1100003650b503055841104c0c00e00000080c00e21903510794100b141c010340006003050120703080c003001d000885030b0b41d8810000705004520201c0c00380000003440104840f8140e009014071800e003002c1100952100748500d040c002003400f = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 861729397 1250 861728147 861728177
    0x207120b04030f08090a0b0406090b010e0a06060c110f0316060302030a0b01020d0207031b0305010914010c0c0512090a0e0a0603060b011407060207140a0605040606060f0519 76
    0x11060800620906080c801410145405041c0b1445611441e090044480800481100c0005d4442d002500311380100c0564440741002001401c400001401110321389c1e0003c00c040c458045454001d05003d5401c010103540da810071100440d5100004055101d01142c9010364600641892401000182034507086110500c0d4100001815407001d0007107038000c410000070b0b2025104203884464280090071208588400080d03c60b5154000101080640c0e030314441c60140c0c1d072a68030041c5610130002c01034242d441c10101d1491015207107050341582019010080a4810480d5003101c1d50300100502000380c1140b20880c0b60740054103e2500300300c0030413001421000226050340252003082000034120b0850078040c0946408810540c180006c0e408583c50f2000008102e850f020781201d001a206d030b03100d24050070240d0f00c06044111a1084003000800d0141c03580c4401d0285100e254200a10b0356920826034100c00703400710b0070012400074414403900512502189450307080600d0102c1e11891544 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 861730647 1250 861729397 861729419
    0x40c05041428060201060b0a02030316200102040806072c0409060f1a090c0406030f06050d0812090c0105030c130512030a1202030f040f11030102120613060605190207 73
    0x2c0258001601d02d00040081070340a1117040094910044814505002101302035641d00c4040c040712260303110510300c1c50b0420320034030b65a010640746000608a10300740c4001c16000c0c1d00180a2180640a45000b1500d0140108581082100555001034915032900710344c101c2114000401d82d0016280c46003100005c1c22403164022481034174100084607080ca000309040c0d1241c0e04000c50040c0084414860a5903019060310126115481d02140300b61070850398a01514956125a8001e2440c142e000304000606024103500f204402030030307146a40f0b10940c25a00c2e400007510902146003080824203000035500206003000c4000314a0b404035599902240c107900f5403c05c0d00f0003e400114030703811004e50243d034094914211180560440c2882c0194003462074001c1e100919605111400303104001035a1a00140800002c000b19110702e400c0e542112161000c40b02c4902c10f030070b040b6204e02c92a0080c484c0300c0030790f4020ba64017401e00d00075541e00443d0130720f2a803100c0103520034100c000039410802 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 861731897 1250 861730647 861730699
    0x91c0507120c06020d140d0e030d0507080712020412080d020c07230d0506060108071707050301140d031d030c06160b160e010c080d05091b040c050414 66
    0x20b0241e6280c20340703031480c0242060300091510f82041600103560401d460442c080d58000d416038100081c102030484890b600e50312841e1415203609080008110f0307016041410349204440c1500c03002200c114a6005600f02d2240d401030100205c0b000d6840c6001c204e140c4080e140140c02114018a00001c1d200c0300d0b07117060711552201d2660b034440441d11991803582402015204802d030ba10303803000d1403103a442580b103000c02401581003003850350008106521a080300b00c07800e41208124280703410301d044014400d501c2401072a000c0400f46001c6d16840c18000c042c1c44296415035909c4101000740082c080c9002e50654020358588070b06262200c5641d0350400912102480d80d10340001c0c0540b520308079080400090090020118404600c0a40c5421802c1036990382d80900e003811086040e80b602001070b00621249240c4c03145040100314003400300091580921481c00e46c0400b4100721141000160360f4071201000002e40107000c1081600486030b401118180014031020705080a4100401c0994a03 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 861733147 1250 861731897 861731903
    0x20040b030a084005011d090f0912120f010e0c09100905060f031b07020112022208060403080a0b10030f020c2401050a1d100506040618050303091c050712 67
    0x1000300c00700450768000100d070322000340c2200381e100c286c03c000001649140e401401c3e41d8900c1514000107051500c103001c0c7d5500c04401a54446d110b4a021100701c4020508031020b040860004d800490b14454541e00c8503c144010640280343c0442e40742400480392540913064140042100b022581e9558403010702a00c0524079000340e120b1401e46511401d9441c0780a00c02c0c280700c0108100405070f6807000710403e40c030a01c0c9070096521074010100204030b808110030300c64440072605002c9142080030a84a00660090360340c188641c5903aa6000101c03000d00d1021944034845030403c5203a180039420100b50101c071b44200604010300e04101c01d09001080202d440090181d151029144004050b0305024140943c0c10040301030400300400810b40000c0511480048843c00007074420204020110140c800a0005919559602000391002c0080c80341e4240c9a8141203022403030342000000d50b200c402c401001000d1100b944001d400016000b000243c1d114042d200c004101c00501003011119544 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 861734397 1250 861733147 861733267
    0xf030506090a08160c0305060109020d050c0a050405060f0d0c08191b0e0103020f03010618120203100b030109050a031d04110301050411191e050703092120040b030a08 73
    0x1338019140811244000c1043d600010107100340f0a50329441b100f940e05036801502c46075034039950901e842d806c5010380c4807910a42414000b0704003001d0783c8200014011490f001182c11426800310289080d50b48800c90220003500019814040c14484c2500c0c01074000e040c1001864908926038600f465070098000c0310104154850507008a400c20405400a14851106000c00c20369580080c0d242d0640303000a0035519114841c44c000707030382d01f9807085401c2688603088600346440307071401a1410440440810f854007c160807900d15003454022010f5501881c82c4103443c5a08180800008244480807811801c10500898654160500d0040380e80d0b089612102c607040c0c90384805441c203280e10701c0b840c070811505001c0380c00000d070000c4150090b5804c00038881c81c48120340c503610900070745010340500500031040d9080e030500c070f200f1160810f40c5825941480f420b03107040185a510303c00b540006150f54030402c090743c010020045020400c03031885a030300c2c1c0b41340032082e4014032036074812a4101c0d000b4 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 861735647 1250 861734397 861734407
    0xe0307051b0604080303010b0a050415031d0c0d0f061503080c010501090b011e020c0a0303050c2407111c0201052505040e040206040506040f030506090a08160c030506010902 76
    0x1d50030a422100041085444034506403d103559551a80010320802c6822000170a801214501540582d170246c5412403a48401241d0084010050f003c07031400d030007800c507944005c000c1c454800b180b0034007008005400144019040e0351290380d001204100bc0d03030001c0d030703c0001e03c1d01c42d0b2424880500560043d000a80c07202e035624480390841d0741c1a4455a495881c150280c001d41c1d800c110050130208801402440a008201041c0d042101c0b15415941c040103080d0040105078100020f48184a0400225400c0e200c840c07448c41c41800c0c07425003800e0000344880000d000c5510401100c40020000c0064924542c1d0190000707190b02c1c10b00c0806030160b5100d80400c200310307500c400031804100b64014208201011080040d1003172042d4002c01c050308101000160940d2168070882c0c000f03000140140c0c0d40c803a42d0700d038260188881408121114000d01020562000001a0f45a00c4507000501e90349024038403440d1310003501a442c4112250161420b00101180d014490316000f080c11070009a924 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 861736897 1250 861735647 861735673
    0x6090c1d09011212170901151502120f0d320402010516060b09090706090e0402060f0d1e020a0908120d0e12160c120f11040e030705 58
    0x1a14120119006201034401004890140c1c41246620f582004110b107080c60400c40480301101120361000204401c4001d001b4501d40540c40302920354564180c016501c5e031102a80c60410000080c00c03001a0312130f10088801013500001481811001c50a240c5011020015a0b0940769501d02d980d050203030390485014008010b01100c1008607001d520b104131464580d00290407806062521000b03100480340c020108402c81d84159404003009041c41194642440000d607144417900446000402c080c00008046981c4142940199401044e650401442e0702180c40700380c110700c1600d903040e03860310410001800001d403a14041c00014001594440300d90720090324402c1d844c0c2c840c010a0348490007030745c0402d00500c26102c04943c2a100412900c4001c00c0c3d840c507040508403d03640c10180090340411010b25018000392183c4a020103414142e0b450340e500610104100740503004082002013100041d10100710105040801080043c1210314001c0d25441c54201d080300f142c40e035001314400d00328 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 861738147 1250 861736897 861736937
    0x703051005060a080d1d010c020307080a050d090f0b09041b0e09070504030201120b0d12050304030f0825140d02030a06050906030d0f12050906060a080f190606090c 72
    0x686000c00003003240c01e545d030000034182101400c0c0050360400d40444203a0f541c1c85040c800d6034190300217041f41c2d2501d40312106039845001449084400381719031081c211005000d90020400c4441c1010029802450188071520342d91021042c10b81c01a07940300301145200d507041044914603d55581c01204080500070b002d42c002d0f014207484148003083c441040140c0c1d008218450204406901007120b1181d080480d007144250320000704a010340b480f925000961080195124902070b90b5080c50703c101041d0256140c04d0141d070310170200e0201010030002503014454020040d085450f0260480050205400e05500100301c00380415400100b070048a098a000e0100501421100d10480341000800260b80c4d468014410080c42041c04600c00d50b940122441d0618809040e814401440c0c04091981c4914080742d0051003041005000f080020b400501d10b003a40380c080c0001c01d8480c95040f5030440c81440c0c40300440b10a9200c02000c61a107826020b032111000d42c60711022142c40100d030f64008 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 861739397 1250 861738147 861738149
    0x91a0a06050c0a02130b0306010b0a03060906120b180316051b010923030a0303020703170622060504020705010e061e040b0901090c0e060a050613090e0703051005060a 73
    0x1041101c244102e0795006030200307511800350360440b90498020000b8412501400d880b0603055032600490300005201e0485a00825440c041550100900c94031000c00e001114058003404000410f164201800290417240141d04802001054486a00c142c804503245a2151010458228200b1101401c000080120180e80c1490100091420380d20000013070070000306106582246484031412080b107180d0040703d11907000003405586031140e50b0b0a0107006035003c504104c001030207450030081040000e03010140581c900400004421002000c6441200210720616011030380e244000181a0784a1004004c5d0721b11030310012440c800d140380381600313083e401410a1001d6032070002c0a05074021510343d45a105034046038140707184e00c1d440c005900415000000501c14100da4101003500c402040619108503000c642c80101d05850b03006210303080c02a080c1d0f810081c07105400a200c00b043c682c1040080102c14400c4500550303603521846d02e8041d4409a030680d4a076503409210560030071b0341000d8 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 861740647 1250 861739397 861739409
    0xb0405040f112508030f160813060b0f09010905070f0203030412120603020d050c0a0801180b04050a150c030c050414012724080105180c04091a0a 64
    0x201c01c0402d654414612a8400002502c032601c01d40b01400f08040304080c56203038012000703d86a20b0107522040c03003c58241d44d1030010039850166900303201c3c490005903106e0360004c04500c0d0003d03040d03540c64002c5d0048001150f032000060280300d440b40c940c050158002c00c0b005101142c2801d02d80d034060a800d00d0f8034205011900200108801b190380c0100d04e001099140c90101c0754a02e140c0140c5000f42a244c0000303504c098600d60180030b000000483c2d4400c040d040b0742c200c103000e03659041e8074220340780c0b40200460801c3c0050850041820002c00e0ba62150151082c2e0b60b40b940590341d00c2d241c000000140703040803a903401022804503854460040c0261040c01d255150034100040301005015024036541040a100d41d8a14261904400040b201585d01c00103203045803600c00304d0061010301c4c0e0318100801807418818060910231010345040310005084401110f000c42c407100507941004000d00c016042c100720009205078a032144400200610500000e2400450208060504d0562000c = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 861741897 1250 861740647 861740651
    0x230109060b0a1e0b070c2105060702010c0c14250311010504032a03150e0c04061203051b1e21030a180f0501020918130807020d050105010b0405040f 65
    0x202101420030f541500c10344000800f82c030b44480c80d600e411403464001d80c210001c4030429030405d82c1340520001174890b02e40c4c0b00d00d096030504e13604e0301c3c000c81c03c0300ca8201c400400100601e5000e408203918107111590200500e00b5100070080d40c14142c3c050400180005c50040c0250400304240200924580c07241542441e2491402e451900c800c0e20304191180e24400300c0c81404140c0a000340718004070001194080401d00c41c1750014204600140070100e01a5001d00a21810429902d004e100700803d40b4030006c50006400d0564404881c0c0da0401c0511001c49400d510000021040411644c01d2440c13204446e815000c0200c419242000e0003e0304500b4040b1000075100d0201042c20107483d4000c0303500a00050400c1c509020003c034070a5070801a140014010b034810a010041d001044240c00603a0540420904c02020380c811000031641084c6030250134804600180000c0300070310455000400c40350b40d01020b43c81e41400c43d40c003030707203e1022000e000070104141e080138022400d40881008003 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 861743147 1250 861741897 861741929
    0x819090e010e01180e15090f0c03070503030d0917040f0302040f0b0a031e021305060102010615090b0d020405040213060e06040f120203160e071e0c230109060b0a 71
    0x103411880c04102a000750003d840c0d90b00170301d14403410452840c04003640c5559081c14102141a1915105484840a054000c0d10310315009801c0c0010944211580034006501d8031540011900040a54a90444041e507900d0004011010751074043c1000d001c280000c0c00904e4514410081114415000c1010003420000d01ca055955400d00301c0341101c0e001016424544a0b629200780c112a80000007540401842c000000c0007000785e1101348214802c2c0c008211386500c50300340980460342516076400052400720b0500604881c0710107004030130760440c005400d040d1a400054240c1e08141d8200d11030003c420800c02015601c030380100e06214003541c01528007403d240c4030075008881d6006026400319240000d20031901d04001c1c2c00c0074143c8040140358040e845102c02c80c140c600641c0d900e800203034070280781ba9003c1106100d21100c1e141c1a102c042120115640380340390700418000c051115408041d01d0441c0711828020603010074031845d00001c44422a20421983c84040d400400c400681401 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 861744397 1250 861743147 861743159
    0x109081c0e100b03011b0e0d020303042d080a0c03110d060603060203072307081b011503050c190909052107031103070201080c0c01510b070819090e010e01 68
    0x18030031004020b44802074108c0943c00484d196208552100c108268103100d44401008035120a50030820000c40214105584002e29607640c030b00a80c02800011001c0004c0000610010315100c4a0074041c04c2c003101010181c440c03408540443e407095419a40000030007402030750103882617100b41e03190038980c20040c205064484081c040d0002c001d111105c001145101e07440100b02260b0100b00c500000d100a4036400c0c03005912440b82c0c44115240e220740804905076150210348590303845207000e05554410310340131044011b020620000c0d031b4980100b60341c4150000313103442e40710f004289081c0040c2d941c9055141c020220000740c4d00c3c0717102c07681043c41004010b071381c000c4034282c0200e81c0c0400640c40d001c00400741c0780104a01c490701f0b0700b0801c0c0c09003606203180308180403024010170040b0f100d5082c81d005a5400d10540d80c01024050004160014807402141d43e0290201d0390040b0446810b05010720180310208a50030381643c0800c50a03202004800d00da200c100340500b9043e5860041949401 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 861745647 1250 861744397 861744407
    0x4090510080709200705010b090c070201050a0c210e120f340e1e04050a42150f03032001140f090109081c0e100b03011b 53
    0xc040c003c181a01e50b142000380c40b2104d0180600c56940c9450a80d44180c0f074905036000b080e001403000d0190041c80c001036821034241c41514017140d01030311742074500401d0407811500c0c2c4d00f001000b1100f4550848801c202c103403203c1121050701d1180d840d45e80708481981304000c5100782c5100011203070ba200403d941401c1e123000c40c128401c0b41e846000c0000180001101c01e0314900790402800c2d80c41d406581c0012001c2c071500c5070034007404410360101c100f9000d078001104e40c1801220043c0c0141c0c00080c00c1e03400a1056481c0b410b1038417030782d10000501d115905110388008072001c529841d040c608441c0c81c04011144c4507404800050114045082d403800c140880d815103640300140c1400342500030428140000c101504003210003500070400c403580c0c1219802d5508054a075580c00d8000d1000007088104148100d03801c242d006100542001c040307000040a00c0c202d600c059103115150b1204601d0f4400c00c11407800304c0d0139a41c50204038206958181800c544500444025190179406410112900300f = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 861746897 1250 861745647 861745649
    0x411091b0d0b01140a031e05091b0111010c26160c020103020702040615120e1e0c030607020f0607180902070c0509010906030c0909020f011d09040602040905100807 72
    0x1407a000c1042000540140c5151040d8011080304400010340c0600540d030650104405014000e4086928003c140042088a0040741c40f052554050740045200c3c1d038424069403c4403005260100c1c414900007411800d6558407081030b40030400300801844101d46060f04000301100140302c001481c60800d0112190a06200400003404040c480c40c005591107501101c180c1368014006004e8240c1d20060001c413401a80d101900080c50307440613150101c050f015000510703c1000052061040840c501101400b0503114120139115074038500303c281c0c80c00d00c41e00d44100c805401400810a040030701c0e40c00c11000820940400c007494490621651811405805032030703114000584403440c1349050003c01505400c0b0603403005100d40000f6610000b43c10650660344101c4030103540076658011101521000305000b540102c0404a2902c0d80d48940d10611801450381090b400508218012074141e001c1030750141c9400d0780025090015800a0041d2a005414030a010100310f1814900310348584c01 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 861748147 1250 861746897 861746917
    0x1d090312040507050d150f0b0622030f05060f10060219061d0f010606140d090c0306020c1e0607020706080916120209090d080f0c040308030411091b 65
    0x4000c010a090000401c0540f0140c44064000e80c0340c241c1a0604031000080e030008000900d090101000d600e04040c0034600003c540a41401d080c4002048140d2452042140c0c15a1417905d80a000001c9144503400d1040c55008201501c078909240c3c10360b421002d8010034000b000050203104121403540092000e6044a2100106401c250b092514902500804180d0000030105640c107030004100407401e5084526050003c01100b5a0f03141b041e9410300d502c1801903180d040070300c15094141c0d140d070403e056042c420541030074483c1c0c0342d56904040b60400d241541040d80072502508585d016000001c6904040074010081c52500d124000d640d44068013500b800c000410010a0035004200b140c08640c140f0764822080c103a85400b600e21802490b01c0b42079201e0040c000208030010400324600316a60b4003a5203e8503560349004490080d00f03009030144020340700800002011448071401b46004078030468495000b03900e201c0420440c003c015141d04644d506041020507031540e260212898242 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 861749397 1250 861748147 861748177
    0x50904050712110904030810080f100b01030207080c03070b0604050c0315130614040c050c0d110304030f1505180a150b0d0302060106031104060918060315061d0903 72
    0x1d0740d02c0c0c18103e00c0c0c0c801c03001d15080b02d079040a0008168011f48414407c8400307252280d22580d0302c58400c3da0380d4108030051011034010003094407810986410070503a140c818140907140540c0303a81c44007055808405080003982004c12803008100410444507004881280c0c24419410003e100380c1c81c6100240010b007000c2d01d0303281c06c4401602e070004882c04043e500d0504218680e581c40381c800b042950032042a218600e00007000c1103c0d0301880a40303103040702e024000d040200d4000d8080d141c05101a842e9441880280070010005400c0071000020b03901c9810076920340701141004da002d991014202403d40700e94004000701c0610b0003d8550070840e00709181000952001d50390400400408564076004815900001b0a06400007079260480d8500e5404020511034002d5031149805240161000241482d0b0704200300c8082c2c007503003d160300c40342c10000740090741c90b52180c64191482461040490321440200804078043e01880800044c450040c0031a00e40600010745a08c140644568104 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 861750647 1250 861749397 861749429
    0x50f0703030609020d0207170307080610140415020c150d15091113060201090807020d061506031b0311030a09050a051b04050c0703080a1a06040f0509010509040507 72
    0x2601c2600580020441c1040455803410340e02c40c0f190180d800201c1c20b4850100d040340d010700603040da40840740f140c042582c1c3c003610394454008211407040ad203042c0808002504407900085442a0000c000801d012036a5288094030300401a00780745440d5001c0740300321444110300310719101880c01c075141c0030040500055160b00300c40d1045003040b007a030400e0701d115103041c031000320595200b001881c032180c255200e0030201d07070388880c200e007130354030510700100510317414440c00005003040810030a45501ca001c0114080c000040c40302d00c605040d40c44100002c1d241e1243c6001590a01402c13211a221480e050202450480b000803142c84042c002c8011030b41d440180c40140320f02800020780a030f91000507213661900c1210301c0c0c5d906501144285118500d40f0340494500001881240c3d00d4561544618440380e60b503c1c9207a0040c40c0070001d0032140008141c0b501502c2d543c01c0010005440c01d407001005c0035081206028074400140c0055004da0080e009000206800064481c203c4001d00f0501d42c1b00 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 861751897 1250 861750647 861750653
    0x1509023f0709051e0f09030406142215181a0405130204050306010e06010206060111010b150c010b040203090307061503080d1e05063003030c0a02070504090201050f07 73
    0x4181c90b44881c10750b038540000e201041003800c61444c10f8a601501c030554a45454603035101c207250959624101c2c1c3e10404c001c11015000d2400b101482007260304c2e080c02e001d204208014000c035a855442d001c00b58550f818000120f4039042c0c42d89501052038034030030414100644c80107803011401000d0241c14440c130302c111240d645400312801790801804030315440e10608000d5020f50231a0003070510074050000041202c0801c070a0b035610070b900c146d004000b151205401500c7c00c41c52021790044039501d0710800b042540380d0342680d004400c40c50700103d5444c0c0851035100e0071200b1044400780b003140100300380314803414004159909250414000201c208405a848203103050a5100521580012403039041000255006600810f1244400d91501d00c00c28030410454404540700d40e0b121466212100a620301c240c00654080400d07840c100b01c12007241c803500c5c61900b040360320b94409030000131742181140d41801204000d000558080c4888642e5500191860040307585503481c4200109081c014 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 861753147 1250 861751897 861751903
    0x3030c020a0305070609030c08010515120709290901060c080d020c060c042d150c150c110601030c0614130303030204080c0a050307120503071509023f 66
    0x641c3d201d812502140d6490070050102d840d1071100395064030f2a401c0c0010f1081301809280d201d1721040e20071680f203003c081d0170001c1c1400c016099004511401c00081a000b655110344092a0000301011403500e588060b80c451040c2c075480101c0c001c007154001085116045410726500c0355101000b40e0310341000898840081c000c00f0300341600d0b403003080c040c0008858840300400540d81840e500c00c0170728000740070781c03205404580c440c102c130700300861010080b070191400d003410403514500e00480c407000d840c0c4801020914680704540c06070341e148042100c0c140c111510000c02d400d4136016109c0c1d50b1541e241da06030b0a40d030f80b00300c0c414440d80c404a903280c280d4000c00c40d01510044030b40319400d2a201e040c010001d411900171000c1c1ca20814030744110518040020000f1034100070002c3c544035040103068a0030325102981201e0f030380b005001d244005a01c0c2e40d40d4030800f07013400304000303940d54150042104421aa0035244014600355011255550b01e10781465005c441d0382242d10f1114030300c280d20500e = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 861754397 1250 861753147 861753149
    0x10b1f0c06140a0c02010b0310020a110615040c021911010e060a0c1101030204030528020d05010b0f0103050f0703270501060906060e010909050705040e070806010f0e0a03030c020a 79
    0x1102600d41149004814002c641e0a8020f000703402c1d042081c100381c0d250582c2214194049036034035502456190000e940356030000c020b42d007902e240001c408086961102d2400105561a0740e2821040e1076110345401e0074400d4003803400441c4003d0a0419501101d521000b00d03000014190341c855110307242d4564021500c000840380040c2095a65041d6800d00802c0c903c4811741c02c441002003480008440c0d84a802650190303500312025203d44455074004901c006040141900d000050b42064400b595410b05009240e6009134000320340402000100705607540c1c802d41d414141860581441100c4c1c0000b000b059106106040003e01000c080d1032203031842168200e14902880ba018a480030040d064002070225100d002f0706200858441c00141d51400302014600d00280c1c12030000c011031103490b00203d400c2040e500304540340540b41c0c107802c1c028000c204c413014041100c3c030041c0281c550340301150500382001450859440856900081c1c600002803001404010407110550195614201940 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 861755647 1250 861754397 861754403
    0x405010c0302090616210c0b1006050f03100906080f0f01050717130506070c05061b19050903010c0e03060f10061d09041b12030e09040305130620010b1f0c 68
    0xb0a118502010007403c7e2440c103101213503800c400c00080b0ba1490089a01813081c2d84282e00c40a0610404c954103281c250070041c03618008a00700e000000300042103120300d001411200d00a050240b0070904090320b40004024841d010b40c0c5001c003003212441e0301811507086080181c800164503202c0e1100080942c0070b0a4010302180a00018049120303045950407001d54440c40c195000d9a5030030b00c14131124000c064042074440010044014001c0480e0a198280180750031300f2030600d2340700c1c0c0110303007161011402d090100d06041003098240c5020820558000d41043c041441031400040302440c0c910144560f80900c20b0220310340c078001440d502c1110020360041c01488d6180750609110105440001e04940c601c52180d002141408244041044064050b02d0b0510401c5502d0180004580c2c001d100b5000c0140c14040a40c0c298292101c4100a060581c2c80c06400d4003000c04641c5c4824a140340e03003101e0781c0340c1410400315458540782c1c440808050541c121150701402819210040301320401 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 861756897 1250 861755647 861755693
    0xe0c0a3b0d02100905030f15070c0215030112060f0c0c03030c0212030a05010312080f0609061309120201150e0109020a031107081903020343080405010c0302090616 72
    0x34981d6a104c410780048950403001c869991090454a584500d44145469108000380c0000361806024400d50040d4510107006d0010b02d0340c42480604864000383c0245041030b540c9228881840b201e0700420182102d1b0410420216083c000003800c80c0500c03090040901d030300d401000302103c2c02809040300c030764a507a0b010743e500d2402c0c03c1c489008210074007040700c00d02c0c0e007007601b0408244144c80d0f0f10300c01d400d10086160903032201010000b03c040018175042c1e00c4000780c045007041d0805401420000ca1003803022455444000a02900303688910110641d0004420020014001c404c0c071410b045850b01400181e861030501c808402401d003506034815003582c0016501c08103c0301c240200304484140c09a05210900442e048082e448162901c0c0c1c420020712000c90b104903640885007145100107080d2940202074038524444c0440c1d5900c5c0c000c049a01201000f05000082c0181000081c092400318600007441d00000c4490058212002e205940642944100080382e040c0025109032a042 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 861758147 1250 861756897 861756919
    0x30b040c020c13021e130906051c0804030609030c0309080c060a110f0712030906030212040311011d010c09091b0818061504140405190c0e0c0a3b0d02 66
    0x3002019a02c01541c4888804c06d40078005540542c500c9a101a20001040c04543e80c400b648401d501c1c4c15117950544060740100000000038081c0d1040c4600244240c685503241c024909010f8900302841d400401180c1000464000c550349070307801c03594066030604100c6c1030314000072038061a02e1703112241d02180d4840d0000100750a64940c420301f081743e129035a03448a1907240e0b00c08500f42e010f0b200c01044014038000108000074000da006049984112000081fa112081c8141c8892107498503803110595444010b12441340d44029060080c108c529002d000c5001410054030400c080c0c0b40c0040300f0003120f60b012070002124000e030b90b8480c55014040f80c1da941458a801300402d020803130054821480c00180603000d0040101d407510645d00400501040b59000c1103603444001040c40494100b040014080f48500b40c19013054041d40050680b0b50301c641800350041c1c805406502d103050008082d1a4110001c0450b4220759400c6100811142c1d80d1070203903020030380311b0f0742da910700a520203a80a0 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 861759397 1250 861758147 861758197
    0x30905030d030e0f030408070e0405030d0510061b050a03110709020403200d02031c090803040f0e0606180f040912030c02011d030f18090406050403030b040c020c1302 73
    0x11042840104007030f6142c00c880d070003007117650380324601c0384500c070380c00c02c1c8810004807000081c0180e10602610035a841c0192045030f1504039030342102c0c2c0c410301d030b1501e040512065910503651407004100903a40b54905200361206a5246640d040041c00c001882c2c203040c01c480010700c1101d00808040c1010b40d100e648924040500600c119400c0750480d0f2045000e0245203014845400305a40160140182d680030420308040140181d860b8410f00a49050000720b80b541040103000a10340f0742620113840c2d0030030881c02d03055600600701911441c800d00a050741c6605112194001030004c4070310050043d00c10010401508403460050304440814680120440e0190444a014001c41c6e000300035402c92034180001076141d512200740190310510070300e01c030502024010700b4100e68102070f0340d0703c114078800020070b00e010071501100c1d2184c45000307002c1055010b008005940000321010b0006015a80c4001c3d40c954035400322600c101c07a85420200100d116074101c40032098072007440c00c02560718070 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 861760647 1250 861759397 861759401
    0x41e0302060f07020405060a05011e030b10090e0601050c07181107061a0307140103020310050307030312060e130807061d160e0c09010c080d14221e030905030d03 71
    0x91000c0e0f000c0c2d0701300000a01f82c7e1074580440720660718140c682e90000c0e502682e4140b0741c00c00364803041c1d080c103035102c48a403907035680c01c807643c0c001c01c90560f40c0001c40c07404c0085070b00f6402405800c7d241841000c0c0f010324a1180045184402d454407940f060203501098901040608540104201030003000211201802882d41105150098089401d902e080020f01816583e180c94031030040a020f0052681036a03603c40d80055800400021076a404180c80700c00080c100945540104c022800c4d8105541e010700c1c840c0120001030208092082081c680500c6c94200c88181c588002c01c90200091841e0411145610041040e02003040480240f007915110356035401031600412040105290b0002c5d24041681c5428401c03103400c010301d800d01108078015070707101030340710f6080301c2d1200103110304c211100c030900c02c000c041000400810800d041090200e03612000b032071001161110407148400125440032916075508000c3c0155026801003400c08482d580a03d400c240d61502a804802006981c15 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 861761897 1250 861760647 861760657
    0xe0c1b0106061719060e27032a0303090304061803030e0d0305070c0303080117071203050307022109151801110c0418030306122619020709150308041e0302060f 70
    0x18910101402659031451500d41003110790081f4142c1c81088014016801c00c15620881d0340c0c5043d203844508001d507501d90031a0411100761000fa800450208041071307120040101624009e0030b0044080d0540d00c00424411076021000d0041c8141210380c3c0030540315000301c4119541101120318801e85030702d001000c4820a21812403699040d035000600d65034007003503260031035108480c50140005070781c2d010784045d0001000102035028082c100c0c1991040d0f41140052000c640d010590795001d01c208201e02074207075400b00c0382c024209100c06a1480d87c0415060895407003428118440e0b0501d03000c0d1442d0013481c544498015040c079061200c2c442c07110113483d0302144643c030140062034554061480c207044440340906403031107500303407032101c4203d205807480d102d14003401316490104003485040f01d0f0b2001d040c041e80113038080e403400c110f0244184514954140c680c80511803032031864590300998001c9014842c0404401c0000010000b28a6640002198041c04030b0b91508201c005200940d000 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 861763147 1250 861761897 861761911
    0xf0305070c061d010f1404060e0a0209010303030c181404090501150602030421020a0e0601090f0e041407060c0204020c0709060b1e07081902070e0c1b0106061719060e 73
    0xc00500c040317090706038000c240ca19065034509911a5840b61103035009414214640c4103903010f828403103405a00d658968a02a42c081c2c1c0f404100141d48050080c4102007914091f01001c00501060015142d001640070030203d0032900440c0c0141c407410114014000015a0f00302100c2203400010340940101c050000c80300044107135a1030b2200c42c0300400401c144054001e5010301c1d02c207070034419045086a4560024010301d4400c0c00c2584400c260f54a0360510313004026882d84120402c402c00501c1c100729549181148080c0084616014000d0070082501c007000744142d4010481c0c41034500300300030020043c04485424450181c0d0f0f146203180c02d60040c09490b0000042d0a681d0241c54804021640c501d90301c0714065141104c806140c0c000302c0500b520010850155920000b4454680d0202c00c4c06023040020b4296540031116000b2564a41c03c0c10b80304190341810401c000030394100b480380c00051080710f202c03001580c80d4000760448021011901220514004005c02e00c408034080c118400c003a = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 861764397 1250 861763147 861763151
    0x6060711150310140a0b160c0510031b0f1b05151f0e09100915051810050903040b070314031e1311062a0d0305060a060f0305070c061d01 60
    0xd80c941441400c80341400b645e21040000c0010074000e602d10507c5080c81801350b039400c40c4868a4500151084030200e20440001e500c0711410143c0380c0704117010204183c244d080400e103e68a5240c040d10f03602d20650803c000410f214400e10520a051104038a014034501d02c12500d0301d0f280c810b98030351800d011001c071140740103800d001c29403203180d443e014010000c000040440c02d040080d07950140002120441e950f02541e07080110200450094a010383c418041540324901621243c601c0c0c8003180844020081c100014010004d4000c8121005d44d1a400c2c0385560b10902414240e81071034400c0d011440b000c100004011340c2604a0042e500794141c000c0380b40340c0036115551000b07203440418502511510f01d01074480304914144009003070b0408598480b04400100640411002e01252506c6031160080010581c0503036041c42070a501980444868200030b00b0620001d010b41e9011064405041da60800700d43c8240c060500d002c01103a106c02c042c050144402e5030504410350181290050398 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 861765647 1250 861764397 861764429
    0x5040c080d09140d0f0503070609020f0328080c070303020307150b090a090311120c010f0e0a062f0a03050106030c14090a051512070806060711150310 66
    0x6114002d9001242c0300d0308840c0b02c50850300300400021140b09901125106140c01e04900020414005825560301a0740000b462880500601018141c1000010f2094018011038401c03170548100140a8481511001c000003c1a150000680c800c403421410984140000003040603800401021580e206400740050b0000380c011540640d541100c550380c1c84055000065081c0441e0351005400da4020b02d402c20070b020300044c480d0708100c100c0300145145680041e220315040e00902481d85140c0b20500100f00e2840c450f11401d4541b19915001030035207440303183c407000200725405040300b401c52251690790350f189200140212035020f00d0385800480d04180c000606903000c2c1c811420f0540040d2100c1040e40c14220307050701540c0c0314004080e4411102080400c1580794000fa203c450700c00385003520742d0b511140c501040903c8009203102c2c03c00010008021081e1584001d903802c02d41c0c400102402c08a910002510941400501c000e00b030501201308811645d0050000341214501d0512030115 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 861766897 1250 861765647 861765673
    0xd050f041709151c060906050f060f03012c0c0d0c0c080405042003040c0501142701030e010912090501020a0b0106050c07090204060806130b0307171005040c08 70
    0x140120110954443c0340400d4604030b03140024010a0701d0390480d1007901070301e04d4000c44074080b00e40075008800f100d5a2400c040c03001c0e00f07040d411100f40780c00c00c51f81349044c03002801c000000c41c0301c1401000304040c00e54144881100d101541070b52110302125021055181080d44001550402540c42001c6420002108540d50042c01001c1c0007607000341e00d0b0352030541003a05101c01761041c110400c61440f424040040c0e050640e80107140100d100b0032134104143d1800000404c220904d068012403618204010403041e040654001d505c52100a82c04030b01c0e0001030011b0300180851a0060519401c0c0325042e030410540c0780d00b0200103400380d141c0000c1e07141c40700012a40c510004000811841d031000040c4003060140c40070307080b0304500108540c0c610303844400c100d080c1d802640c09075020a0907042405010f02c1c04413021400c41038484820401403941400099036100d462150781c01e4014900360038501150300b405449900400c0101c240011f06091811105403400c600c1060042e000d0b40030101c40c0 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 861768147 1250 861766897 861766943
    0x807090b03100e0c0417031e0310051011010203040f020a15050d090f050307030c0b010902250203240a06060e01020714010e041e050c0405011b080d050f04 68
    0x1a044000420000b98203002503083c81c540d019154252000041c00002507101502c40d0100040d09a0800fa5456200700b1060014450203641a480320130020b004011441030302420410407207208a4000c07e600905040990300a555031407100c1c020b50001041100344078411051004681c400d48807000220750304c0d683c090780682c05100300c2e000954108241217030425590010920107010f91851400b410150344c4442c0b0b5548002422404215034001d50380600c6641da00f00350040043d080294500380130000074401311446003060940c44c40351002100c0541d00d0410100000b0281402c1c0748103100615200010f4241d130071a02e440d0341a04002000c9202e610509100040e810180c00800a00303040581d00c58180081022450410254001c0d52040da0359600515440350105071461a402120210000607200b008085151241c0c0c00c210400990342d03c80e04104801da41040d02c411040d041c0e2030408458855030413599140e6040c98107010000c0d140982c654051803084520311030031211444c03e500 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 861769397 1250 861768147 861768151
    0x6041e200a05240f0c0f0d1d06031602010b091302031603020f060a03110a050307020c01090806070f0e100503061003051e0c12090c121f021b0304060807090b03 70
    0x1219566030f504584a244500b00506101040d400010342800e0032503014074030b018a601d580740f51991102030a0b501c010342200e03c0044d80d00c00107280784c01045e4580003040c9184400382800300403550384140700c50f010f40300790700c0f044988000030070b800c41d06e04142031440443c0490001c1a4840c4c06440b000034070f4540e04290590450f41d02030201e6101e10100300c10004541c00a80d004028951100c08840c1c1c291401402003006058581301e007034403401c000300001c0c50f12440c21006410700086480604c0b00300700c0020070341d52154103454201441c2e064220201c0d6180e403d0904242c00540400e403d0036039030b402c032001d503100c0d01081d210142101c207000400c40907260161200b000c20b9219a0b5000c0d50b2840c600451644240484005031500000380441c0d00400701c22108541c0c4c40d04503201d22015864030402c8981012640c200500c0030f401c1c1902012440c000035080e20505a43c00079103041c000804140f1815022650300036280ca80d0354900024000100c05c651403800101d0322400451900156008c0d40c1c = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 861770647 1250 861769397 861769429
    0x2010c1e1101031a1f05070501020a05131202010c020405060f060c0d1e1202180d051b0d0317091507031506170424020a030605031e06041e200a05 64
    0x1a070322002d098051740101d201c2e4051804105081240780701042c0c2c240020f064561040e0f44813595000d9014010103000b1054010080d80400b0005010250781d01a000360402901110300103400d461314000110f801ca0302e20b480366004100030402d64581140807030340082030b412580710110781000081c0d641240d42c022600100128142141c100300a520a60160138100007644d4013030701d4145031100044207441284811a415403248904d41c0c1500d01c84070354400c001d1820780c2c49032006581582c006d808c81084011088803d9850400181c400504105940702c0383c120071144000f1b81402d1030028040c0541520820380002000340008103184580700d0710110180260b40d03410075880e150307144c07032102900030341c0f000c01d0800c4610b40782c943d0306081c40189142e40c0a5200012011b2401c01814200402c11003950103040d50141041c0442c040402c0c0554003035409050101c3c0b100000c807840010000c1c0c16400b40800d949101409402811940c0750321803400d00f160b600ca0303116039a000b00140d10b0701c194062 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 861771897 1250 861770647 861770659
    0x4020424090e120309100f05070c061107080f12070e18091e010b010323072a060c2316030507050d0906090e07020a02010c1e1101031a 59
    0x42090905542c040c402d40c0c03256100381c3e54058811600d860290b04282c401e100b0302d411540000c244110326101e01402158039000601403441d1590003d40001d29080c1d01400d010344904481c48103200401c1226000c6512070745641d1525110703c5420300d0742d0810b0550b4030801e407841d030104049602994a20340c100100601c2189140030400000000800140c0605014072424600003070002c0e09003032001003a00201c000068021014000500351100000301801c4030076000b0745400140014400d5030390000e22070500c400781c0703842c40c845480c0441304c009052001c0340e5003a050108001440d00320800c59a40365841d01880c2c80286480f40c03090588444505079000200304d44c83d000c2455003100504103002c1c1c2019402c00c07100740c5603d41091840ca405100046018030207000c03003604214150090b00c103d942054291a00003c041d688450800010b17052190604d101000c02c041484804450000c0030342c14840340c09145003403449091403141d4640803d0074400c151803000c119120200d2903000003810 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 861773147 1250 861771897 861771899
    0x207030b060f010309050609010509070906080a08070201140f0406090e091b011704151b0c081803010207050a0302120a0813050f070e010603110702031e07091404020424 74
    0x1049002c1d074021020606142e100c009000219170217000c40b80c8100a80380011134249000440c903030804041f50000c9602500c3d103a414801402d00084548040c3d0f0302501090344c3d54080e00068501e42d2415140c020a4500010440103551102024004503401c50303d84d000c4503a00c0b602c1040e0080c3e02205c04400ca0b52040c1840d0034550003202848051401c103041a01600c044c482d4143c18010040f641030310350300d61007004850510b8603840790040c505452000c3c41c0c880f0124202c020011118000c01401c494004160603225003941001c4940c0a007009000b19070f40c541f030389820b948816003040f00b50b015014a00c0040e0000c1000c004644050149079148441e580d40d011090f150b114864009690a00c00c15101d001d00c1c40d4104880c4002e010b0345240b25100e0341c54000020166600048800c1200d8004e11026006880024400f5850a000101c440701c40d1000e00c4e800d0314100b80e41e40400c1d403007414100710f800705182841d1110301560003a14181302c0360b9504400c880d2002c0a04080a481810f040c80c = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 861774397 1250 861773147 861773149
    0x80403170918060a05040e07080d0c0210030e1e06040204050f061305040609060c0206090d090b16020f09010f03170c0c0904060209040606050a1d010f03020d090804090209030d0207030b06 82
    0x2c4160710034001085039013440d8480300440d007150f400c5a03005206900943c0c0c1070150780c0042007000241c0c0340614055420007119400710b18000780700c00d05036041c16203070705544010400a0000900c0d0744850300c0804000f80d40c556149070341c2c090a8800340c2c0034074500000702c0e030748198910205e031103140c0c044c00c1510440052030b00003004000080c4252112aaa01c00f14130000c0c4c0113018040d03030b24105034001c00c0981400040141000760482a1601f48400388404124042d003210036200302ca200d20040002c2e19a250000c908c2e0b5041000c40e0a600402e01070000ca2010510f8a0100c02d98ac0142d01c540312804035411509082d00c602140b00300309900050303010708c4628062880c50b500a02c02c01b0054144462030011809850544c0c0165010403070200700c22060a50003030700c1075010800d565450100100381030000c4c10401d03200107a40109500001d01c41e101e080313250000300c0e1255200000c1035450b41d80e520183d00075005004282c2c0320b4060710000a00c180c0c80004c0400681e5040b0030712091540f220740c = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 861775647 1250 861774397 861774439
    0x405090d0c1a01030b1603182a080d0225090c11060a091109130803101e03020102150702101505030a060c09050414042604030804031709 60
    0xc1000c40b41d400422220100020000024a000718400d040084d000d01700241400c61142240800104252500c40c030004003000340601c2100c016000161b0420300300c080c0402454000c002c0c44d080042c010000c1d00001c00b030800042c1d03150010403d0f801d40328281c3c50207065040e1001d1500440d88400c1150f50144010320799944440d406160f14103204404c02540140d00342044070803102d148000b60380d03c01d00010300115110440c40d45008603400a014685051910355104040e10003030188000803002030f0310408500030040142c2212805480b0100340304940000d40c44d81c60000700e0050160208140321845040e040314041d040980240410207079801000e0003c1134040c20150f00820764042c00a4286c905000000c9042d020b001c02084a14000c00003070710350300e480d0340700b01d001c1d9103490540703074440c2240d2030240e0b04190302108000e920641104200c41c422001c03410116603000014002040201d1000180210792080c105081545403007050048039000d40404240c00214034a0402c4100d1264 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 861776897 1250 861775647 861775667
    0x904060c021609140601082403010b03010216051005010b0d0e120304060b01110c0a0e2a030429150109090204060504090609020a1e0c021f0e0405090d 66
    0x1900c101c5501c2608650401c098030103550000c030007507503a00d4a00c22014030072051302d0b51000f02801c10031140c0c2401c0c0307100a0005e280c2110300f40076100c0b440701074140d03a8081d00019030b0040010002e548a0903218080400719441d248112040d224044000354030301018016241240d0300b40b50301500b00300a26400c14050000c0e192200352602600401c0310600e41800051409503024100000c0c203e9a03140025001107040c1c461802503600412203400f480d942c48118400b6100141c5101145864208000340c00d12039031224070b5402a51702d481401d18160140142d8455400b0304c0c000207054500440442c652080207a8a01da072640304000030f405c41080f0700000710445018541003500302e56640c0c0c982c00f00c0e00241c00980005e00005020025140140200307405002845011450200e08010142c00d0200d610607022440220900d800002030140c601b2840840d005825611440600d80b00e150940d614600581c0c08110786402c58609402c181c880d4a04c94080358000740b04510000c0710640d030001003 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 861778147 1250 861776897 861776921
    0x30a08040f050a140130051509070905100c0c0e13031d180606070b0109020c0f0102040f120f051510060f02070303030509032701032007020d15020a0f030b030705090406 74
    0x1b1000058034002e110703c1145e00c1012400703140c1000900c040200054900c0203828203040140c07209090105a680d1805040102d006003441d00c610600c0b031030b041004945c2a402904400034000c20004104103030f4444103480b0384aa650b9202d02c130110031990182c4451804141d030019070b0413489030030038401c42c88151b80041c80180ba49050154503035540104e030800f40c1040c46401d0700404c40b800e00c0740c8208503d200310f4486038025410300d800d001208001400310b10960460407a1480004144058060355900ca1a0803100340c84141e0140000000b00d15010f468503181d03800e05210025211b4402c00d0005240c15081d806849002e1031510100e0207000090102800780c00100b114014a01120886041c4d0711450411802001d03205000036084404009020808801039100a03521059002c00c494103180d0481d04030b21600401d007000e4100301c481141405881d880000e00c103010640085141522444550b401e002d5039015030280750310f60001d0701c192034000d1078903004034000803d160031011407604 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 861779397 1250 861778147 861778217
    0x160c080c0606010323132f0f03011a09220b07080c0703050a0f0905181801060503100e030f03071808010e030a050304141905010c0302031003030e030a08040f050a1401 73
    0x102960350440d481940300d0021000880d10107141c00b60a041070502c848c1c40044000700715070b003502c100d2030803002d1481c00c8852142c1c44131800203410900c48407400e09000c10007030f01614034046519041e07000c580251003c0300461790280026100014882c200c0d140c1603416510319092116444055855504064054080c0018200b0100b0161030b480301d090140316100c0c80701c005c80d0034088003070070090710440303194811a414440240017545000902c2080d40d0090400064106004925142035010b500100060401d00006002c58180c0c04000b403059082c1055002400303d07520706410342280c0f4600a0000c160b0001d101e03071042a40100061036006000b00c00303900b41e0a50070280340707003071108012000c2000c8662202c0c16084c01ba0900c0b541215000500301146181426a42c281701154980720040800000455181050700c0030711640e980168841c50791030302e882d12031604145402a03801614010312a1040001d00441c80d030440c29215401a182c004405525a4161190741600c3c201030000350 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 861780647 1250 861779397 861779423
    0xb0c0c100c0b0a1d0a0213020903070501141306210c020c040b04060302030f03030f0f040c17100912170114240a031b0f08160c080c060601032313 64
    0x309203000f130b44400b5034140a0004140300b0f204006035005002014803059105010300076281e100082d250080d1202400c004608410f4204006218442c0c9a40703411502c000c0b03c0009032094111058141808140c81d1440c00280340444403001c13103080d0390181c5d0050f48032200c1e112312070410354002c0c00c04401c007801c0815070742c0d01c0b0703008a468504400203408059000200b00410f000100c8846034010790711080405a41c182030b124a5169801c9000c1c24500c2014081e40104000c0100040307011001c01040510008106007400510405006030f036601140a4804100c18204680400790684980c80c1101000341180c0052126480085d2030802010f09504075907000c1081c1c1c2000b414481042e5507010500714100d6151603181c0041115090030701494185040006800952003030b03000001c251681e071312040f201001c407203541c5020400341c1801e4002801041749080840d42d14400d4100780c0701803018004040300c04001001e9511403001c1356800b0f0f03002c9500c0580c4000c181b0300c1c02d809004446142c03 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 861781897 1250 861780647 861780671
    0xc08060603070801060f03091407260706030b042a12022503261b03040b18120705060103051615080c071406090609060702100908070c0b0c0c100c0b0a 66
    0x400303d9200c18035056400160b04100c0c100b10080c4503002c0700003032861b00120101881d25155210001d0180dc0d0038162600c070031810341d44890340540200c4004821054034850b0300143e1440380c01c00c0c50f40d20030024081e220303680102d4440c0e000301c40000049502c0031001d1500b02d591450b05090340d000031020806041110403500100d031040c524941000307039003007e903800c003442c0c0450b010b41000881c0c00d80060510802000c204540d402036405190340040c140e00a2103010624140703e50041040e8032850007180c948103202c00012504e0580c2d10031011121a002c204407401580e0021740700710950205024441d2003454420040c0d10380165100000c00e040924a40d0303010b42405014000e061541d1003041006012070080100c00c1e0803841c008090090b901304000029110030051261241d116100c810400802101c11b0480e5841904198648110354540910702141e6100c0272810265103e1514000c501d450310301002d500803102611000e1202d440b03a0ba401414003c01481180b4540e503540ca0700c154 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 861783147 1250 861781897 861781913
    0xf0b09040e030a08100503280f060c020d08132103060f14010e10050306041505061303170a05030a050a090f080901201005040f0c03060c08060603070801060f0309 71
    0x5104025104d01820386440070020410b907010b0b0b40218400da205188400710409190504002104215000101380b040c50414034103600d2030703040041c0741c0392800d0000740e03809a0108078003c1e41102076582c0303126512000c0d20b0100802e07036034401030210b0240c040e180c041b504000441c070964444508010070503698a00700c1242c00c00c9154052031020000c14050300e840c1d0b038402024a81d400c0c0842c0c00c00d800209200700140700380001800d050140e6a64441740000000c180207800041c030004080c1c50f903868000d01c140d41a6a00362000300d400c5940c03802004140e54071501500d24100f180da4138035085684000320b20024040280c03840701015914603040010500820341440d6072801251170666400c440380004002c09482100d00e1480060038850801055001c04d001410381902d02000ca0b02ea220390429010072100c4000040c2003520313070300e8000104505d94210010701e09082d103031103071140e5800007400017600c02258100000b58010005010a6004601109190040c1c0c03600040e001c030107a9440701 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 861784397 1250 861783147 861783157
    0x130603051b1c0b0105120f0d0e03151e0106110d0f140a18050a050d08090301060e0f040209180c010c080d060602100609090f08031504060b0d0e070f0b09040e03 70
    0x40c00707503c00e10050107507040580c0903001c0016590000c2200c2d40d001440140c603440801422820080510700c41d41e01c41d5410044a0a1043c0c0344000344086c1c24034503000c810310300c0203e00c8000c00701c100074000682c241c0507408189440340008090140c11a0105049690300050006030b000d10094924081c9075245100187c00104c03080d4454443e203500613094940704034091350216106000e414002d0116840d2010001d007019842002c05480350586400240909010b8009001c907070410000c200c07292114034406800b840c000e440800d01911409003885000d440381e0340030100c0b5400200e400742c241d4030601c2c010810602452019040c035500c4094807081d11556400f00006a1041d4003103241740c4214031030800144124402042500055560302e05000c58414010300500400f10018101e422103101100440900420400499448150507131041e0081842989071500e00b8100c070008100010707000c01074034900448a06010300d0a04000125407060a4142c6c1044d21180a250042c0f4101b0240c0 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 861785647 1250 861784397 861784403
    0x60b0d09020103060509060a0911091f030f0212040f11031c090503061e2d0a0b0d0b13080f03090d270b07060b0d05060105130603051b1c 60
    0x3040900305400010159040780d044188280c3d41c150504c03003c0d59802000307808507107040801054a07120680307401d0040c0104806280c10040480c140c0f1035200c1e0100c00f2f40314204c00c50f2810030586840064241c220b005040741e00400b5841000400c01040c03030f1030344040000344603c40000e000b20400c03000c00e06141d820b084420380290b100c118941010341011145000c0c010540c000c01152a1010b0746100c0c140398100c08001c3c2d80300110106540c8843c2c50b400d1504a0000c2c40441000d80f02034004020b0f01a045400c01c0303126207400400d05042c034250015420752030700001c005016440c0d03d1460303a091001c1c0300b4129407503081001401d00b226100c0000c0c51081640c1000b500c100500c2010280c414404114604280344200d6504828269613040201c240c991081095482c0e043e60300d0a90b000b00400214a64080501d020032000c01400050150684606032242030f85c00c544800300d00c09507086800001c000e6003020f0306e561062000400d0507165040010080d08022090301d0045d140540215416 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 861786897 1250 861785647 861785651
    0x120212131e0b0915150d1b0b0a030e0303060307060807030b0909030405030f12071707200f0406060806060d0603120f18030b040f0503040b0a09050a0501020604081b01060b0d 76
    0x11103601480340c18404d00d46129995002d19021504000c2140e440407102d11400221106c0340c103110082ca1440102c4004052102d90162920040c003500d4100c41368020000e410a0b0701030402500220a4a02440700079008080c90750804000359611400200700d0130070943d607a8035001d8203a0310844d0075400b50151002455035113090209250038185070360000001c036440454111034a44c010800c0f291455001050007403549820742601603503100e000f40c094105c42824540d001803040740314900c0c80c0b2140884683d0398600c52182400b00f5208144105000b103410b4800007000f505285008201c01003081e240014141c0d140c0d501c1c0107131890010b50303000c0004c050400007000e37942c02103030b020030004000303003080d003442d166503600001321400030001032500320210302035810840104243c1d40903000480d0801c1d1106808000104024640e100350742c802d000c64036001603954000300c2c01e01d00458010444524040300071415080101d00c880503086199603070480020300c840c900d0003400000c0c40280300 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 861788147 1250 861786897 861786901
    0xf2a0d1425050315180309040f0245030703060207050304090507090b0a050c1e15061504150e040606210b09060f01020312010303050307120212131e0b 66
    0x240d80300c0306030641009000c0d60181390b003140401c100300c03c02503205100046100c0c10100c1c194189096000d80310030190000e08202c1e0220402c00030f60050000e013880380130921b81d0110100000b40500c0030b030390140e01c1d91003041c80c003070045080381010b4540010000390407603102d00d5807aa2040f0891348030715400e8039181c002040a000c00c00300750048a4000d06146001000a400c20400301081d10070840e03141e050050004107005024000e001080103500c4008105080c840002040f9880321048030b080a2980124030008401d4076001080900b10f2004000e0b20f403d0909000001e45100c0c0c1801403a41400040d20070701025645901071000907004c00da50340800aa100445c41c00d2039507804003261011800d1100c0e114054035861585940040c0403201c08071046501401071b411072054030100c0c00040c28000c00402031507001801035008807440d43d02d400d07110814600b010102d005840d100715078070940b03101003540400705801c035046c62805041d80d405000c0190344220000103a03400112508514101 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 861789397 1250 861788147 861788203
    0x60f260a090b0a0905031c09151509230603030c0f010f1d0a02041509050c04030b0609090a02010e0126040c15090b031b0703020f2a0d14 60
    0xb441c682c020f03052a0341840304511a954040d241c1c003454140b04011203c041090300d0140507500f0107080b00d50840a01041030840070350074409400c5001d210541d16a07040e00005000600744980740d100300c802c0703005102d1084001888982c203000900000d80c548400d21800501100a03c41c070b40d00c0d000d280303000180006820020030161680710081c80d00900581c0400504010301003002c0440550403540041d112840c0d5003101404a090b800c0218482e241404101c414408040288240d9011300f030080da450341c41304204406054101c4219030300380c100031046401540612542c880364441410803200c1e031241c035003d45400c0344280c800210b81e0705082c4248010700040d07400603c040d01e040010800e601008100203400ca007910321401b00743d0003001000403021036000e04440c149010b00403021b0380c2c0e59400c3c1002075540310b505c50f8180c201e016051031402d450800c3c035211030001584103034031006843c81f10200421002c8030301040d21000c0e0301e099a014070480510882c00d400700481c8420b003902044207 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 861790647 1250 861789397 861789413
    0x110405031f14040218190204090e1b030307110607152013050105030c0415050d05062b1104180308010b1e160203030307120b0a060f260a09 61
    0x40844042400c110b0700f40009070722100d19075070391240c0c808110f409540f038011403809031880e60000c070f000c001d10110300452401c2c0304d508020726011040084a00c00f50b84852106140c20428040562513401000301ca00007a140398425040b04074000d12160a101c01038950b28414603542c01c1c060b25141c1d99a030b590a000c42103480d010120440247d065003009001c000e072109004150241d1414480c01000207000903101c04100c03005000c00d00a03004199104040c09080c940202120400990401c0d001584d80d08111200001240d2420541c00541c0700140c8407401c04600c0c0c420a03513008020400d0009140c540d4000d2400300b9550040c8859214001d0800802140043e04120140714040001c20200f20f803840c00c1030000200e14040980c0c803007944210030b0358243e1105000350580004410010b0032508880b00c5003100c1c1d4101c20500031441c070013040000d040014011003002c503101001c000700c081d118059260003040c40d0308101d06000000c2194107888030089980c80c0085850700341c01c10800c9524 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 861791897 1250 861790647 861790661
    0x30f05100906021c110301050d0c08010e160b130b030415050124020609070e0c0712030507030c030e0a080f0c0601030b04020a12030804060917070620070b0109110405031f 75
    0x24420045401104445c40e0148410f01c00c10303104403807001420007803103404030304000281001d5000b040741040b025809900e41c03c00c0a1241c0900480d114005284c003000011105413000c1c4940301042203083c101d400e0f19540000d8070503644960841100517102c7c68910449020300382a8811440c1c0320031104c0c0401021607402c07070107000c54206605020300142c0000e0140c040e500c0d1070251018a1762401c00c03060b014003450070094504901d50300066a102d0b0035500c064080c180740d0340c06010200350040c0035070641d01e005140e5030142c3d00c200380701c5011801510103000f920481e41205880d24050604052408030280c1058607100084018441180f90015241004008020f0080c40c1203c450710b018080c0500140041c0285032952001800c101001c070003960300060942d042d0b40c94001c01e0811400500880a08400b00c8001006060100e60359909a0341c070301e86d0000150340700740e0902103c20060310b0140c0382103003000c6081c0004541540c050282c101a1004c10507820440900a40320318159401 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 861793147 1250 861791897 861791947
    0x19020f0c070317070b040f11100f08060a0b0a1d040603061509050106050a0e010e1c05150c09131b081506030618040c0803031311030303010f030f0510090602 69
    0x410040000005c1d26000c1c07080c5d00c40d0300b0511128100b1442c1c1013000c0d1445424010350b500c543c078001903841407134102a019030219616511145203641d8031b024090780040ea03010762a50044103200c3d8102080c4035a610005d1501036100d101e264007040350101c0c0c00e0f038001d0741080340d29580350480343c0303d800c4118980000820300d004d41401603502d4918080d1803841006206010172078005100c0314075034050508003087e03000240c90700c4400601d0110441d00705000a008403842e00cd8260210360410414403c1401181140c22140c9800c0040d4204140c3c0e01c2065080b405240d1034000b40b200140b0700e00303941c0c620818151140102031400c0107005c81001c08030502c980c8902e000b030081c40205d1300c03101442a0102c0c00c49100460549030b5003440c0144500036805031045110001c200070452a09900c0720380c1c5544640f9a01c50151013203800c25440340000d00407181200519201003010070640348251514074040d40c10755404400c50601542600e024010941d21181c000403a14081c3ca088000200b840035 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 861794397 1250 861793147 861793193
    0x1020a020304081204030c060804062301050301181112100c020610080d090e1f060203091806130207140303010803070b0a0902010c111201020c160501050304050619020f0c0703 77
    0x6c00c5541b15840402c0301c2c0030310800c2004010000c0d04000c110360041c005100d212101821004044454030140002406568004d5080a06905002d4a80824068a06e03882070320000043d200c038003841815140404448500d101d0142c0281d0046401e2144000716511075003d0a440e14140e41c0c450109041988011300652104075080c2c9084e078400b0503081aa51804c04010440d16100c00c11544414559000d913003009810b20300143d42e603000801040004015601c2c00341143c004803810081072012900030b40c1005145018400c1380441d80c0c01080802e2040320070160940203d0305c600c0c070b5a00240c2050f00c3c10f40c80007503207400384202206085d41c084804902480901c4480d0b000034200c0c500c1c01c070010075810700662100e4890740c564064100e00340c0d904000719100c4c003007100c0c0c0ca9030f10b4104460791006004000c20100e81c83d4440c2c02201d1103141c11034000c0a158903491400034007a401180e18154469003440303541c0a40c02c002000b8aa00d1003403800a003951401c5040410310003101c1005a0745030030b = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 861795647 1250 861794397 861794399
    0x1103150102070e040b2716030201110705130c0c0507030c0608240d03020c042306060a140306031501091d0705010e040209060f030c1801021504022101020a020304081204 74
    0x380318417425680103003c4045500b81000c09403002100e4014080e0603400d602a04c480b4039120801203508004481c001d81e41d04540f01d20310481203032558101e004484d0441e0701c444000034440c40e41c3d005410842d1741441e1040a004084d12a542001610b070400c480303014000000300411603000110b13503001100c1d14201c025800811090410036460b0308038860040302c04030b11420500d4000e109454481c0c1e0054814080808030504071480481490500c0785400000c0010490710b040c80d0041e60f41c50161502d5000d00e01041e6160415160030080c401d603418072401c0c4600c6149a0600c0714540200911a070210f502c1c0c018201581c42405d08080d10310403070348514070400090ba40036448120880050350016030350680040480c110740b0a18450180c16003001041c003d4424122000b0a4820300f142203419442018000490726044000e0b21914602ca480b8007042c007525040ca100640344007000300c803d2111481d44031460aa070000118040580c00214007027100541c10b2000140c55000c0c482510310389 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 861796897 1250 861795647 861795653
    0x15170105100c0f15060609090204060c030c0609050d0e040e060411060f04050406080f06070810090c2d0201200304061d25170c060d1103150102070e04 66
    0x210303209030541c00400c440400c11900b03000840700c01590803600f00900034910040d40000c1c0000d04814400c0c030000405000b030020b100456482501d0599881c2d40ea4070120040c2610100d44403c0c00c0c0038141d82050b40e03100342a0002c0d1040008020718038035078030b4400303852800e50100b108440005002400c5504114100300c00107208160b0b103c2c2e0103404031409600c440075080c40700c0c410b015540003950030626001002c102548009200d44c00603c03104215500381e80d5020045601060945440c250025940402e00000c000d54001d00d90003c0740f403900f001c05500c14a00d9100e0074046802510601e01c0c10030202c105158203004800b2007042d41036000c020110080549103540c030000b40081c4c4025039a00071100d002c3c50f480749160030b25034a4000c40300002d201105183e60400f894503600001c01e0140c10020f801074040130700304041d10b9840003400180c12a20203014403a8000036510172542e0352004c00001c91070b0020041c43c0601c0442c840030038960600c000180c034020440d000028145c42c0d000401c000 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 861798147 1250 861796897 861796909
    0x7080609062203021c02010213030803040b07051303080d020903031b060907030f150b060703031e18060b13090b0103060e16061d1503070207051c0b060a080715170105 73
    0x104e40600b40385e6204004810080f4024040d60076100c1c1d070040003000004c1400751400c05103000b04c0c041c000c1e0903104d4482510940d8a40300310030142180904e51402000450303840342c00340030f003001344600151400d03500400190a5601c071034000d00c0e03440d580c16800000c103c0708005440c0e11001801c0200656400c50311400300c0001003050040c1914021032002e6441da00c1608480341e80140900340d00c1d1582403c0ca400b8001e041d4041100202039607244482228544078003800c4031090040c00c03101c551181c00d4072074101078801c8a0320690045031031143c031f01d1030b00d2440c0700740e10265014000010495041d45442001d854114042c2d807a06d1f444100e200d03240032545042c0b07108440d03c600700060042c40e0351260820240d0764281640c0c0c000d401000c10200b071103040000798030800d003603030940d000f554541003000201040d034607810082141e07202c81c0400003010b8000207a0400710007081403400a50b503041251500251740c1191014855138075125000f01d4004a50b19490b0000d04544125903042030040f1304 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 861799397 1250 861798147 861798163
    0x601050d05040204150b0c010509060f0106080711060c0705161d071b060b1810150908010e0c030d0c0f08090402070f2301020705070501030209030708060906220302 72
    0xc600d55980108003199503641c44107904030110080340851641e200720051258005040c004169401e03c000101c400f200844c00702d12600302c0201d080f0310303079003400c8007183c04800060501041c092442180300039440e040040c00c1c4241c00003198150346507083d00e0001d06190001e1180c038030640d90624140008841c81061034155112100b03503008964442a049409180ca2903540714440000040041071020340e41010070079100c247d82040190000c00507516200310308444400d00b00d4101a8240305001041a990305100820f2030b045120359151032405017100c41d04208051260701001520003a82407d20031807400760414242144000b40580300c03c1c1b8040b407013010091103000001182420380da520b84c148c45d042600300e0b80303043c07a010180c070b000e9140c01800b49812584243d2102c1d003200c584014002c544a042e8003901030304025150000542c0690807801c402c80d41406072160104030070908011040c40740d04000b0080c80541010b0a05480c200303a484ca4440014030501c1e08840440d40008401d0 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 861800647 1250 861799397 861799417
    0xf07140d1713031115190e1b040216020310060e1b0403030e011b0f0308010b072006042715150804171308010b010509011706030106030b070f0215060105 67
    0xe803406102e03d44e658108280c62040e06110340c1a60305000710804030704008a555003038044c003080fa140c0c0c2d0030002c560710f0307a61200c4159420707010450110380e81882d8018204454039072004c004010100d90020781803440078401c10022507501c00080003882803150b003a54102a04000001814400c20746003621849103020160600061740350f41a26070340314010602c9011001800030448850700e147c0403c010300368640c2540007405540c00440d0701901c20044a0320a54071001c84044011011412503440c14050b40703055010100744800181c12000310208034a80c071248600300b240b24140046002141c2c0e00300149007400042000600c003075400480b40c0c0c64807800ca0705000020303640380d02e0b03c80c1d0081100c1204400d12080800e654982c111803480030f1342600c0c3c0d0a0700034461405801c004580c5405024a554009807170804c0404003400c5154000f504042e01400214100e6141d845141701544140c84c61000500c1c4159814200d41d03040c413405a0240fa03000d520000d07400e22a000800a0280b03e64003 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 861801897 1250 861800647 861800657
    0xf0c100903170412030c02010233040c050d03054801151d0f15011b050a2a030c05100e04060905220b0a020f07140d171303 54
    0x72001c0101d4400079900288441d084030903404030b04c1d10f40144100c40100c0100d0152007001d8001140c0a080d000400d03009400d1000052400c1c4030784100400150b024206a83d9002004800f040c60b0f11010b01c050300c0035000351540da983d108a140c04400d000c000e140c654484400c4030741c00b107002078860000710328624180566002e00e22246c5001d20f00401105407003102401241d440052007540500f441e40d8894005007400201760760301d054420100000300c2d1201090310311035141c40340035800340360194040604090400780b095081d0f52541e1520030164000d9a0b003542800038004121002c0d85110720709031006084c581da80d8230f159a215212207a1380039107441050301c141038041980c4661801504400c1c002e00502c4840e030b507075141c074006003410340e13407010103900c44040d4007080001d20808a41c1d01e5800240e151240d078a082402c802508100c076000c02d0020100419800300d04242260306080c000f240c040c000005401c01c0240035060444e074000400044c1c00d0410002d040b041c14070300111501802c2c0 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 861803147 1250 861801897 861801923
    0xb0a0f08060f061507050f0d080702011103010810230903040f05061329030f01081908030c03100506071101030e0106121e051002042c07030b03070f03050f0c100903 72
    0x1403c0070511f4099860030320409000705444d0340e004000c01c2c000c0360542c00810140a815005042500c001d006500040d4407000503031413200300561005440c00c002814100b200381d600d03508289491303400d490544056002240a0050081d01d02500008040c02c451891500c0954010780040342d01520a21105400b6140d00c03020042d070060004400451040e45156246441d0084154810382802072640e244258648142c0100c0c000c1d0401c0708890304080d07041c0c21030f520407090300c4156200034240fa0126402c5440041c1d1900d0302c80283c9505407140c030f000700c4451500800102103c42003261440c6584c100308003005078150300c0c000220307400c0e0070018802040308001c03030300110642620401082841085d10800180c405540904151480d1220003120f604c000c554900420070300f028107849000b03d09000c41c540380d0003a484000c4201c0301074282c80c015903a50402100c000456841507805030049403034140c030380300c0038000c40e100210100c1d207030a141201c1240003081104540401000c85040c01a = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 861804397 1250 861803147 861803153
    0x405090f030715050610080c03060a090f0f150f06050f090901150e030105012303010e0d0306062a02060f0c010507170702060f0a09060b0a0f08060f061507 68
    0xc0818103240c010100d07550798415103000e6450703010322002244580d00d05004a901854450151440c4110b40c0e03852811a8039420a000410ba0000d048194002d080340400501440b09000305c0503000221035001508425800c21101618070b10002c0c040d40401e041001d03c0f13001c460800c014151070441c54030303d0301d606103030701c8030303403042c841c0f02c07001903100c020b0100000746003030400d1000c000c5e030965a40d2164050a500145402e841084c000c0c0403203030203800c0d0121b001100301032030803c8840c0014000304030031714040c10940c240b460148030100040d440704c9040c810136030080e401c00c10382900d2801300c0d0f8031910030003032410150070b1110000388507040c0066140070040c1c00d036050318070208000c1c000f00090308000b10040c00c11030301c4101da0b003d04e21041000501c40c0d4004900725200e005001c20f155910f0b030302d41c03107144002d03e20508222403040da103202a000c207031100710100010744220f9401680b81410301c2c00b02407405a0040200d51002c00d81c008000e00c5448141400c203600b007624031915103a844030700d = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 861805647 1250 861804397 861804403
    0x303120912180902130515340b070807090f05060301052707260615030703020d0e0309030f0f030f0304021302030a0f050a09110d03030608070b22050f040509 69
    0x151083c0403980c00440c003082040d2040380d420b01292000c449590503103100100f01e01190061090507032421000402907091071174170314a03c004819008440c900c54000395a18401d40c268142c0303040001a0a10040106058004042001814000384481c070301900d010005407251105000300d80c01040c201001070000e02d460044c400800c0510030202801d45000702c00180100c80e4541e20007541c3e0188220000f0000c0c0d80804540511000341542c01640c2034940340303000e160b2028200d04200b50303007000129000310281c4121481d00541c1c001642c0d903181e128042616268083d4000d20300d81d000500d000c8030240c4000226503007407403000b00036516a9110300004100f05140c0e140401081d00000030400c11264a520400c01d10070460003c011580b14086018121a0780f848014030a180d5010000070301d1502800365020380d88207180210302a40c80e0000a41002c0c045d9214050003207021855168240385400d4030702c648002d2402e0182000c1c50200000c407600b81d60841507019682e60800324044000034 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 861806897 1250 861805647 861805649
    0x10908100c0e0402030f06010c150c0e0a0b0c031207091d040606270216060e06040302100b09070c03090f140414160503090f16030312091218 62
    0x1009951094096128140141070341000110000c2e8a2500071a076528180c402d03203010725103405514030140d84030707801551541110442500d0700c03004008482920845d50143c2541c120943d520401d140175030200740104408070350084140d05034280300754000c055000040c0e1300780d202c0030f5841e824213071182c003419144c10080340c12034182840b00c0d107000c1d81689030080e5418080ca04c83c6030100303c002e55481c130720f11040b1040c00201510082050703480f0499030098010780708035481050601c065811690b200ca080b2120b054031901c582d00030500f00002c3c180c061040b411058040d00081c0102c0c4050000503881460040c607140070f20807078403240d9044c5886141e002c03028081c0018101d1760aa03c444a0070445541002c0e140d2207036051040011b5842d5403401000d01030300442000c00850700c1000e205441d80d4000600112441c401d819030615080020003003400c0748000c80300315214050941c280201510984417407901d03030500700400680051034075140383c84051410f1425001a8002d00a013070685040c03 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 861808147 1250 861806897 861806909
    0x15040308040312110c0a091e0c0c02030d05160f141615030908070f050f0102030c0310080f071a090301020d0b0301051f05090c0c0115060929090109 65
    0x3150200c2045403d4001420721045502c8441240d01c140744841d0f5910f4451000e281c000f2403500c4100701e1007c284d00100404141403615481c544050090b40048500302101e91000400c3c80d8031a2055080034405290023401c00d16009282410507403103c007007402d803800000c14400d07800490300284022103940c4280110400240c500d203400011804003a01681e0081c002151075400c4000340c002d010344950100154420700350707820b1100c00c0e00c0d41c804003240c400b0207407032a0103054040b00a0340c00c00e1000307601c21092044840e8480c2400c8260101c2000603402400865001d642c01c0004040001801c400311483c043e401d500a8060310400036950207040003458141d8008100d221915440750015044244107900802c802e940c1c01281855400b44680790b141e00011070f444c140201c0c01e141c03070780720303030144030890000d14081c1d00c0c892040c00c50303141c2059200e100e07609803024480d840c0e003d950180101403039440002a000d22840038030217140740d00195441e400001405041590244001c0e40c01412 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 861809397 1250 861808147 861808163
    0x2f0c280210081504021c050405010b090a0213050414060405091e0705030f060712090309120b1902031e09070314061609121b05040219030e06070e150403 67
    0x10900060b1120b030080e640d4542002c01842d03c2d06660900744255110074500e000000c6640844454040040502034019a815500c518049040380c0b220090240038005040e00140c5e960101a0301d1884d00020fa08403502c19030030300726a1400c02605094007034210504480000d503544070440b100d46002c07074820b044c3d181d01081761041020701c4000702d001030460703c055058600c01c1d2481480c4503114041200d5003008201b00441c0003000d03c42550042581c2440707824a14045621000803600303181504c1c0c021200f440303510041128041c1398075035400c460703071079500c0c25411030509058940403464460b811408031800e15002414145041250f000190b8100300a4052004100d80b210f8841c60704491b040041e42d05a961030080900c02c00da01400c44490109000e061002070780ca4541c81c0d06102c0c2c0032003c0f80d400f04008680c40e52140f00801760901510f06800d45000707049400b4003903a42120003d00290440d000704007109030041c100e4551920100e4120b80c030046421110a0980200d800c00f429110b = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 861810647 1250 861809397 861809419
    0x61804020d290f030c031f1418150606042706030609051e12030a0e070605090a0803070b0103080a0c0b0903070309080a030c030e03010e012f0c2802 65
    0x1e0442061a2a90380b401d9038403150031a24401895981e8001d07031882074046d4854030041d54407108030481c0d030702c2884403000c01003034081e09400d40c80e4072041d09440c620994441d40c1400c0e1058801004102c0314050f520701800740c14a0410005601d41c0100d00c40c4041d083ca003400d10403900d2a9108282c40010740c03409003023041f551281010b03402001035030000c841c0c83c41282c0e201070082d6000d403041c4c0c0c226005d900042001d0040204804084d800103401010341d00c0d1500420f90f8100414040003001c1c00e065918141c607681404c0c204140c07190a80d02c8102e6a400420420300460820f0b50720506403500300b0301d0140c0e01c0030035042c1102c0c00707040d5505c01744c180c01c040000e001e0404000700c001e00b08076000e0795421401c1e41d01c07044075503180c000019004010611400e11080080d004254455010340001c000086100c0946c0e001420364654248034040100d5190184500d462824185030380000d140c2813890034035039040b150f46da841c0c054441d9104183c5000001910610000c12100c10003540070b442130480b4 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 861811897 1250 861810647 861810701
    0xe1806150319080703031104270e0d1e030e281a0405061803071401060825080105060a060c0c0b0d0c0909150608090c0607150506061804020d 62
    0xb607000b0300822000a81010890954030300c45809540507510451074400c002041c4150307414001156003110301101e0346a00b403855010806100840d48221903894400033101c2d039280b80200081002e8290342450f180404007aa040ea0008030310040b0245100710445400c0d41c02e028074507002e90322400074100c9000600c01061a60340302c030002d005910034400c490964480c0800041c5501121140e10f90035030041c170103680403074075500c25044240700d540000105940c641400b182014520000340300006813003c21030000004200001d0014194440200128105080001c140340418415201001004c114080c00c0c8100180064004c2c8a9114601e03914680c0345a101c1c040e05400b4001c001107140136000082507801401030543c0c907003031035002d1410541494401d8400d410064025070142c411041440e000e511520000d000e003600901c0414502024850340d00d00f0380724005c000501410040c08040c03100514480300c03600c1d562080f200542c840c02041d510350014000282d410104050145441d41a = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 861813147 1250 861811897 861811913
    0x41b0b040906050405040807020603040c031202010b13050103022d100c030e010c030e100201110d09021f020a11040b1e03012703050306030f01050f010e1806150319 72
    0x31507a100390144440b507a504104401c41d00f0031a8040c0c9205030400490005107400002142d215110b0400c44072040c2e00ca889440c0c150f043c2c48644800f50307550f00850310051a00c4a02c3c0401156a004140119070540e4045060310094041070f070501c0e0740b2400f19580980d185924000103440c007800c0761703650078841000207000150500301a0007140e1440c0e52503195510035404490202d805071580c101c4030113a40c0070f11400f265100c901c0070440d540e0728102c442540c07020000380481c56800c0804107007040a801003003150100c04a080300318040110903d20b08036004103070850101e070000403106a410243c03012401403d80603034050f521101e11162400070010101858038200416402080403006600c1e031034881c13220341310b42c1d0111440030085460010380703d0340003107511400150036075600b03807500041d903401e44000707885146510400303400600032032404900c40c42d4018203491003030440901e00007016480c0c01340580b040c03026049201242910f910201b1031302425180e0b070b040c00d425035492824080300e = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 861814397 1250 861813147 861813149
    0x2b05040b04290114040f020708130501050408100209040e0d030519111209070e040807111c0b100f030c0510051c1a04020408030d050a051509041b0b04 66
    0x128580075000c420032254501502d80101c2c1c815031a00d91559080c07002001d804194000869809070301c4040008504501b0f00203401560f03c1003200c55264100070f0905800c010554101504001041c04104040344000030381c8911120050303401070742e5a1550f40410042d24800c2c211011500c114222203800660650246202d14030b01c0d6641900c4601210400f820340741181c400d110500d1080c846c020440c02010300301d603004020401101c910940c3c0c1c41d40c805449104441c00e485052010640d101030000c0c42c1031415610710110b5071809a00030b100070078410000310b19405800d40c0241000200e200d5401c044c400c010b015090740c1401c1503075603490003141c00c010385d014690080c40e0f0040c810380202d00403c20394404103004d01041407d8485001041c0c000d00e81e2580c10b000090842040c1c4039142c60394401030002e410080c000d1955002c0740a10b01068880182410240c98908001c11552408504a500b00c4450456840c3d1654135503041041003c0003180d0700401410144070300045038208900148 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 861815647 1250 861814397 861814403
    0xc0a0f0b0601120b060a1817030a110105010b0f030604090212070501030605060301080d0f0c06112109190f02060c0604020108090a0302070b0a03020d05070503180606062b05040b04 79
    0x90f0024100b15203110036a440c400a40781c101c1c4080c0704000000b40190510030034891102c412002c20ba0791580c0406a1600039030110b80c01e50400140348603000d078010031444040703007140001d00072075160482c0c00415224031303403502c0c0100310088003044065450303410100400d0740003451201001e50780a901034681c0c0040c4030b000c0c0883c1c80c200c070004031820250140c9040716809005001e5000c84200281c0d050402c2d4442141002150108000040c48511400e288000b503c40380703070380700e00b14110160552140c4180100c41e80701580d0800812200008000102c517250007a101999080c600d050b09103840080320095100f140414218041c041c00900644114000d03a1482015103c00134400d448000340307500035005800c8014140408031003a03005091649080c680107181204140402c02100c10170780798480040c80000070b1014280e511403c1510441c4210087d00343d60500000141c0345205c2c06404000702c103290102000031444840640b00c2e0004003403414003403880c151030002101d0000311011 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 861816897 1250 861815647 861815657
    0x180612010b1e01200703060c050711060a0c232b03180204050a0506131404171207030c0f1718120406050c0705100c080c0a0f0b0601 58
    0xa605040050250041c200e1018003030b0405045105800300d003a0511900241c14040c40048980501e44030200d640c40a09100300a003003181d00310310b041d0b0207503002001c2420800c01c0510146e000b0408000c5500807901c0b0844941d907407482021401e880060031020050b0290341c5140c0074a03442490a84511803035a070340c01c15a0604042128801c0b01c1c03221401c0c0e0320441c001810380070b1508074006d03801a00e00c006805407083c1c00c600704d80d0000381581d0f0103c90700e40724152200103025040c240300c03044a010140ba0384041c00710f4049403041501c210b5008001030310850100c5642c62100d2561030840b000800500041e480e40c2c5480c90300940a031000031844400900003a210011380762082c10301041d1000e00c85c0e43c0300866180c0400d01c0c0d945580816039044940651020000b890051100038002029107440315622480e074070000c1414492140e100307500800e00c285641c400c00750704c85000b11889070300802054550044030a8903240c000c522500070040040c0070340342c4080c003d00e00f4900d03120369803d03070754 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 861818147 1250 861816897 861816919
    0xb0c0a0b0a0624020304120f05010b061e09040603080c030408062d0a0e06010f17010504080a0c050114040b06190636030c0302031621060b1806 63
    0x180c400c40e40d080c07240e1080006001a0f80705400558031450043c124180f04a1382019103a825032000d0a80d040c000b100d1400b9541c00c00b4042120a005403001d1002c11120182032209803544c07000b00c0f002c1b15074441801c00001410a10941e91503016101543d0486045030b1114680c1c828141d40380c4c000c0c09030f00c00c3c6210b030100064114102c0403071140102c03d4107642048983c290391645800c0303c00545880c81c044d4481d003c0300100c040802103140202005a48490824904841101400751003590b8242c0303641054108000709512008480d4842618a0b180c40b040c0c01e40d080c01c40c01420000720086004803001d041c00b041c404004070a50003000b08943c2c0c80400742c030074640346020a0b624403030b1b00d002c140000c0040d9042030a03000006485001d01c0c0026002041200007154104011b400c215500b14241e20240254107003000b0816441c4103012001154070f0906800004150713008400000f445e4180c0640801c0000507000341d075140801520f600c04034000004a03445445003192003601a00030910 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 861819397 1250 861818147 861818161
    0x31305150106050f03062e0f020a0b040b06010903080a0f090501020316200409051b1e15120709080d0c080d02090f0a03050c130b031c02070b0c0a0b 65
    0x300e66040740e096486842c0303829242440012250801482160300030812540b100d1591603113480d040000b0000d40302c0d90031500d440800a400c17940039841440440d803000b005c00c400a940c44042c56005504071141c032210750b8440700100c540403017a40009000c035402052590000303821046107003445586071103028a241d1210012a0b5074010003904681070b11104100f080498031402c2001c02c03283c000c80c00c0c503500003d514081401c1d0380c180d900c03c8803650b110425032000c0090b181040c84422030112103581e000f542e0450f92951148124103070381c0c4074128a01010301540f011000b114034407412801806007a140860002e1700310502403003118000d00812480014030351240c20200f9150350703c00041c9040c014107a00190017500074035540e0b90001c0c2125a016200d80c0c680c0d03203000055115100815081b0300704030070300c602000741800d2400c00d6414034174050b0360741c0d4010540103411041d036805030079203008465080b45000d000d5171140c188a0b40000341c0020005020400841440c010341c21420181c41e007403 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 861820647 1250 861819397 861819433
    0x90b010605120f0c0d150504060e0c1b03071202010c0e040c020d0806190305070311060f030103110f040c09030203243c010302180f060103090314031305 67
    0xc500c039020124510b0018034880c803030518264005800501c003e0030541c40002580c100c4842c41140c0c40409815017080140d4503141c000d10b405040248208899420140c5000302070380030f41503c7c904565141c02445045006c00c20a0f116417640200501481405080001e40207125280d9800002031000240038041d003014001d020300d038085540201052120034a0440302008040c0180b6409240481189099100d0103114006140520060035990f40303549000c80d4402240300201d030040009105421a140880050b41d044035005081c5603600024080016404510b0709a01e07a1f100c0e20b0000c034400100d500000140941c2c0c403d03811560207180307a803280074002d40c4034010001e0070608031000400c181c0d1101180c62244000e2401d6204040b10311040300b64803080c590a000c0790106400040040d80303004074403040170301c40001004d441c0e4248503041001548000744054103054580031076104043c442e50207540120210701320180c80c2c0c01c00c161000800701000005440500c00d1282120395040c0f40c1d = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 861821897 1250 861820647 861820657
    0x30c21080a05040c120c05040f020a09080d020c040506120a060209010314090d110f010507050a0306050f0a0b0c030f0706091a090304050d03090902030703060305010501120816050102090d030201090b010605 90
    0x1480c6850f655180ca08a60041c5102c54006c03111020309030400159034445000c0ca041c00000f0750b20243c1c030340c95010300c010910940350b88010501d620044942149a401156640040c0303004d55010401d65510700c0801c1040d0049200c6003c1e40c0f244004000034030069a0141068032026602800041c103800e440c2c081009040e18800070359000030040c1051b00340178903040800d0603c075009980d008110000e10301c0c03c4410417600000031a00001e80703180c0700d03980340c4155000341c0700c00c485174168400c0207000b16503840000e0086c03030b082c8a400101c403415058200b0680c2e0f500c800c6c800381e65503140d03003a01d400005002038400891341061a0404d08032080003001185100da00e00c40001c41c2840e00e000304000d50310010070000e03814070440c060003060443d03881c0010341c49000c2d03903203010900390b15500d001800c4440591040c1c20350194001e010001609082c00c6488291800d00c0d80352904625091440c0213120701c400159005001155a004240d0190055003160740603401502060f0303a1840150703454462 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 861823147 1250 861821897 861821903
    0xe161e140d05160903150b0114040f1508160c05070f181a0108070507061503120f020f030d021c022b0507080a0203150a1d090706051204030c21080a0504 67
    0xd44220000f42e84287d5100082d800c6052511800344400c4a0000241c1c0c0e106400444026540e41810b021820508409405100c25072130520b0b15450070719628800031544100c10303400c00c40c031000d00005004041000310050a1016070312244a07075511254000016404107030782078141002107081c0c2d10800241103074402181a1245119950358010864003940700c11011141c03903950711401d082403010114204080c41c82450103110107a040803001c0d007010400d09151045502c1946809120000071055a1407059480d00c0540c44440812009142c4d0009159019519101040c0301d0b64500700d00365082441c1b940c00c0c080c03103034541071402d200003540c004a03862404a40d407200400c413200303801d900440e400f0b195800301001d440c801f84c0004000daa840e030300c00342240300700448100c0400944186150854880d90080c460b940c074000000c0d065002e107034248103141000c3d00028062500507803201c0d0809900100b80c1040e1103192901450704044181c00300c0c0055161000a500b0041e14440c0300e000d250 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 861824397 1250 861823147 861823163
    0x2060a03062d1a0d05040b0a050f071e140f0301230d032a060c0f080f0a090c08010e01091106180f04090602070503040e161e140d05160903 61
    0x4203020440c00c40e0303444681d0343c5107510010400490818114464203004d1807013020008041c0c10103031050b0040d1034028000001c1d084600060140440c2c2100e0400401c0e40aa50b020301c80e440c40710700c1a520814901c10100f600c5030001103411010f00154025816101c07641142031041c5110602c2c0c5c0c0084800c90f4149130002c0c0001f50070b101081c0108038001200600740c2c5c0001c0800c07401030f0680f42c400004036044403010748034120400d410750829a000c0c60260a8a4010601c0c40d00600d41001c550005c1e021440d42680d8490f51000c0c00084520701d400b6021b800b0081c0104040e1091050003071107079100980d00350860500b00c01c80da140160460390b14607414201c421810100c0c00030046150403c40b08a0390080c0d903911283c0024020380007500d0300c44c0c016009941c803203140210b1380000c3d050040c0300a10200002d104245419080b0ba207035103201030b0140218480715682d200039a0358504c001a01000840d01048074071810300b503604040d1140301c1908900010010b070752400d0724407100300d0100400904c = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 861825647 1250 861824397 861824399
    0xf1d0108031c020706090c03021203091e0607020306070203040e15030307031805190e070305010b070602090a1725080d0e040902060301030c0303030b100e0f0d02060a03062d 76
    0x4006440c02c000440229030011328003c20b955884048491480003103c0c644102d640030825850060068040b41c0d000030081c501d8400c01c100040d03004600d0800d0401501c80700b24000b61a515098143c032000c03680a01251001e05000c04040e640350031900c540400300c003808000612540440c02c000c0031001005c0c0c005c40c00e02030b0740da40c2990149840301d0341c200000d880880000c0d0b10780e1010307001d1100308401190100c2e440c2c1007a010389440813005002605240c00c081c010403080302403004072203000760003d40042e12a1501c0c1c001031110b40040c0c0c03011548441100c600702c614103001c1480306000700304d41403002905041180c02480d400380c5105004460b04003084842941d405810809804080140300041c4051540d002500c0e6070000c2c0c2050350f000480b100203004140c0c142c890043d1400c03045407000714500c8824002400d0300f4600e0a028090389118a600c0f6542e240d4100d40020292b0040400f9144c3c144064003c004051034411b40c0784079005240000c01c0051140104481800180b82d544502 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 861826897 1250 861825647 861825667
    0x507050a090611120f09011808060c0c0f06390a0c0305090915011211071415091605010c0c0915031707020f010302130504240f1d010803 60
    0x3a03c200d0090403207601841000050041c0144003c00c80a00b0003003000792644c100d40001001c0c03000020350303030783d400f120004144010300c00080c0aa038807100030884543e031408000d1805050038000c07155582c4602c0340c02d080c414030340b81008219503070900341e421902c85248003a84034a0986082503da80b00c52000b00071100005c1d115034071511245001e402c200d4900090440424654002150980c0b500e400c0c42a00842c02e41e4042c1d641d5421f051031507000d0140d038201c00181000c40c131480c240100300c521540101c00361040140b100d24880701e0240c00306445481c0054885031550b03d04074480e241414820008200c81d07010360165160140c03c01c9420035020304002400008001101c00c040803002c07186000030004d81e00425000072110075490103500c401641c41405801d12110180c6030606006000480d14000d100f00d00c0c4088610413200070a000481070540d10285483c41880258070807680d0010500348810f18580088801174902d00407440e02c0307600e01400310002070140500c04d800802c454551 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 861828147 1250 861826897 861826907
    0x70804080307020c0d080a02011b020309010c0618420906090f0309060e0621070912080903060705070b04060b0a170c13020405153a0507050a0906 64
    0x40b000b1140125802d26030b450f000100c024040e000111442000050042c011030b90a0090084120070b9483c082c00082008802a449004007020581004511030100d820300020b0341140c1034042070aa04107580900341e083c08564400540d910880642d03040d01c1c000410002081e0300394100d407814080b0304003001102c0c0140c000e030009150584081d6220251000812181e042000b000e910a48402044c9464010081d1090380d000403441d03c00c4009000156161121003c4031090350f005c2c001e141d00c917a845110179200c3c03560a0304003d15441c000d14480c020043c82000812010790f044080707900a980c2c0e82412202403140110003041d0b0944c900104d4002562600b1403103100500034042035003281c40d800308031480c0302c82ca11038408039070140c82c42d0340c03140c2402c100c1c05401c13282c00c02043d4501800c040104c0c5000f00000045042c032100050071840c0300041d503a40c44007414900c804480c0b41401d419455030a02c1e845004025480d1800d4007141146008500710391030042c01d40c603290100341c030b07141082ea5 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 861829397 1250 861828147 861828151
    0x1020c0a06051b01390f0f0807020f070b07110303070c030f06060305010c0504170c0603070f03060b07050105100609030c0501110307020405070306080c2d06210406140708040803 78
    0xf159900d0b902d290a50b03505004504528a000000821301070030355420180ca4032807020042014001e40c1d02412400960254040c03100e11003030304101c0c1e542d07100c80c2012442c002d070306180c162060098080c00703e0750408610040203001c1c0580a603060303c034140b108050b240d12802c00014649140c43d0b0b41040002e0264904010890080c45d002518039541d031601c90a5070140308204001403c00102031011034401a500d018080007039008042e01c03680880400c2151001402c01002c0c04010750690b403d1034402e8202a02a0807050103450315080c3c2450310074003a040039181500c0041e0341c0c8502081c0301340704d04441800c0b2038001c5000100710703140c0001541ca21644514408041c0403c008100140e259406128041c480035034001640600c0c050303078141080140500140314610008024111003588418000451000d0007500c19540500d80081e605104c0d80348801034221911403d409103101c443c004506ca240a5801804041d048420051080000f1a10900464030300404140410501b2010315 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 861830647 1250 861829397 861829447
    0x31d030a0c081309060e0115020606011803080c0706090e04051b040207060905060f01090b030c1c02030607050904051b0a0818010623040b1804020607060507030b01020c0a0605 77
    0x262500c03e6401c540c00300f040c00da400c980c140d1a100e040c01c100c82405d5168403401071856092000c091210660000d45031800034000314108809440701c03a00d0a002a201d4070b0055030311500c0203039a031106007a0b107070312a401d921038000803c4460000040310b0401c06062032040b076101e0050038400c0204464182100311580d00c25402c29401e0000c08002001442025541070044000300141c0c41c00d1403404200b91016013040b240e0a0400c0750451142c0c90002d080b0104010403030324004c400517510745e8102d50b5845550b004e035140c400d29003840b541541100003410403000581d01800305548884d00ca50862039114908170011500f0441044200c1c030644446801008006601c0d0041c00c00c210142c1c2920015000b40c10391061451450603070b002480340b020303000102a036080c8040030b845000254117118456a0401da0001c18000404540c3e404040359141d541c0071000308454141b4031002001407c1001c0301174054410700c004950149005010b1a04844050b900d080c0f4103100211038540c028030185a01c = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 861831897 1250 861830647 861830663
    0x604120302190f050c1903060506150a05070302150709031416180b09041a0c07020a060e09060301060315020c0708030d091a011805090a0501050106050901031d030a0c 73
    0x107400400b410450b186280c010b42120701d03180e0841c201181010041c10106100d0140142c2c40900c15610511010403a0b420000000b001d96954010444044164500a000c0500041d20000c015042005040400c0c00b990031621460f17010340c40800034030026110308000c111105801c00004001e015452104a4032500747d0303045041080c14110405c200390010550300c50a0020301909200305d202d0b9101c0040708503966985418581c0b20302998800c1541003500300000344000540341c0b80c0501c00c841d031040d0f000e8600c00441c0e94850004010703645105180d8404c01603030010441502e014042c01090360323000103044a110324441d401100944c0032400c08507841c06440d80001d5800e8090000d024092202c110210b47d07090f49250411140c2d041c07420070200c0c0f02012005018014403001d6403021842a03d0f000107403070f1a549042d61900c0010302c0000c03d03075800d103000400c0080d4080c0140565240030b880074060380c040110140c4a154151082080039841030040b0f540c0d042c0310b981d20008150040c416 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 861833147 1250 861831897 861831913
    0xb040b0f0d091407081b0f150f03090c040b090f0a05090a06020f0d0c050f09151209010f05070c05150a061d04030e0a0e04020904240f15050604120302 66
    0x10782004004404400f8829000350700104521142406032000020501c0032100d1020002c41c00942c85e900380300c0c080e5004012118048241310341540c112903415844260141d2249001006c0aa46019a00c051402641400c0ca540784500306400030340d0040c030120f1010311566840c60b21712002420700508800d041e11424906101058030761000304048980c45c10203640e92a003110141c801c0c0c0d0400c05114040050410088202e80c022070203903162500d08079810880000c0b120110a5540144281c0f4404102c90304140031030038105600081d82400c280398140105d0351244030584041e0301442c40070740950081844c90125804811100d40d001c0302041000840f15115049018840c4480c2201c44400c0001824442419007004e1038a050f01c0b070442d500500343c5e05109511883c15000b8100034011604030300840c0401c0799001002c0e0445054105001142c2d0107910b007900940350154501480929004805042c0320700104c224041d0760b0007419849c80c0a24040500309504501c5100b541103005403c4 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 861834397 1250 861833147 861833153
    0x3060409020a170c04110a0804242922020903011506080f10061b02040e010e0106031a0601090329070504081614130b041103100b040b0f0d09 62
    0x1411028002c02d80c00601c0d0740313508601032004464400d0400343d40c5400902c00c2d000c0180d4000c00240d842a4003190009000403800d05c1c100100b080f503007000004905210403c1200b02d1483d150b400e4450a0142d10803180070820240a9005c20b116a00c000070312050b1000c8003019882c0c0c000300884040607000260088603604504c15502442d08418002407002080c81602115507503010303040182406900b032a14a4030b10040d1900d0303800890b510240302d5400385801955500d0388401030000840d8002c0c0040784400310086d008050501046840e04003401c110214044c0300c4405901c1a0303810303162070643c60f041d515079000f0710542543d45c0d1456145050020100c040c034080403070141c00c490f11055115400e0281846c00e201c07202000400c201500d61080003000c2c0b8081c6500c41801c0300b41d40100100c0041a0307080003400c1e45180312608070b820240c42e50b0b84500f9040003144180c40082860004648450000c0e034180f055104401240000703020441c00b0003010002080400c0031000d0008031548555 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 861835647 1250 861834397 861834419
    0x509031801020c04050a0902130c0503010e0402121b04061e0b13091419020a090303180f150905010207060210051e0a0f1a49020a0605030c03060409020a 67
    0x106c0514015840303102140441c1032104140004d00d180507814811019030000081450005201d40e004103800340300800e0554032405400c45180c0e41e100c05403050f2036545901c0c1c0303480b07a4603420010701481c80c010b80019094030121014450078030b000400030106180020038003541e0010050302e81e400b40000b1780094220018422910900c0e0040350b0800d240c90040b415a6240e042000101c1070180100b1940750010b03441140c031410f6a6141c02d06001c1942c1c600c0400e042e0030410782000301c0020710007602254050b00707800d808460000710350307551f0700307140c0c48200490b04c0d8003040c45580302603844140b541024142603048268084042c0c1d0690a10128921007d243c1035401d8a0415400b80e9030420314030b440d00750b801791007928412032022124101c152004a00307488020601041c20f80340030030003c8800881c920484d40384003503d000310302c002c070381d0034038492014a0410b030300301e1241c40c100b02c0000314140a80c0c1a607104050501ca154159039400b028040540a8902c0c02ca0b40221210301c0814a50250 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 861836897 1250 861835647 861835651
    0x2210f0d080a14130f1b080109052506120f06030f0b010b09030d05130504050f0106081005060405060a09091d0f0c0f01181a0304060f0509031801020c0405 68
    0x1607a0340d2600e8104814008100d410141c1e00300448030b075030b50420107104000a0b41034160b6512003d8201044490709000300300e6007403656040c000700c507070090000d180e220540201c2d050a0041e01503d1810761100070718034101d900c5d01d11149250071410000c003c11381c0078907400f4800101034800841c0c40f044a1303203c501220310079041140c60400c0c0034103090038480940001805042241d0703041c0d103070087e601d0000b9a070f1112501640101b010015640401203003c0a101006100c0a4400e10442c2000703448041d0070310007400b03030600003411f10001441d40660180003804841c000751100b880c1604140078001d00c2d0f44101710107003c0c00b00300c03a0005a452468440e0f642440307842c8a15070082e90044090604000440d43d09003442d0744085100c03402a03a485096241e00303c42400c0032081d1071402c2068814031189a80003e140340d005501c030102c104a0040210300c101d116480420107002c1d40c828100407254203a400c04002e40c009c3c081e40342102541206d4806591050045642c50f102d135800180a45200b = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 861838147 1250 861836897 861836923
    0x10b120424020f0418110315130905150903030105011704050312070905100207030c050909100f0c0e0d0309061d12010b0a0b0304030c020d080c031911030702210f 71
    0x100250410002522119049040007154030138019a81100345c2584d0501000d401c2c40c001c41600108c0140c1590380c2d030081c4562040007002031101c09054107280d9200e080a240c030388030b0a403564002074401c040120880381030703031300585501500002550b400b40000c280284211000c0c481001001400040190140e1155040ea6034400b40c55003070200380f0110490803ca40c1d800e55210710410b000144107095007005a0b0381c25100503007203544411036149400321903810810703050301d48856004804142c0d0086801c1c0102900e0b032810010201d810302c080122004800340014600c0d0000340800b612070848500203007002950258403d600c6000514240703a0845521000e03035440e107290b03040e0f042c10148100142402c00c030381030851410707490142082c980140d00074450526410380c1000c001e036000544420b0500203040760303213683d491400c000c00d080c00c0150600224104481c1405201c0c000001c50311103941c058419802859801c0448200c0d04002610390303c21700079803070005106c003401c0001c1c00d08084 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 861839397 1250 861838147 861838177
    0x3031d1e070501020a080f03070513060e0f18071125031203110f07030504030f030c0203011a1003090c3201020a1a04170c030c0105010b12042402 64
    0x40e035101554070381203055110074159007054940c41e0103c0c12001c2622110041c100d859036507551256411145d80c42400f03042c0311078420700d400204010b503014100022103142925154000c2c0d14800422041d4044000540c5094900c100001c41403480b480c085008504800210b8003079040081c50031201076042d1540e910304200d883e004205200b02d5070345074441400242010000c03181c907003050240303d01c15610707103c498050004403102014071490848000710b1308225040c07404070840c60014081c0200500591096003000c41400a06104c1c03100304c15640c1004060203960710080300306402030018072400307407180d0b012040c0005c0d18440403c954226044513004081c6134011f0b62032a1403860132203003409411980a000d000e00026203801d66210f420361a651a6005607445280107d80761008280395941c000010074a092424800006081d0465120000b032016a882c3c4402c0310300c502035000050b001c0c05284001c5004911401003044290012302000d030302210b44410441d007680d11105110524036 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 861840647 1250 861839397 861839443
    0x1b0b030106270602060106050a02120d05061207050a1406070519030f0305090d05180a060207061121030c0d14100e090714010201200c15010b0703031d 66
    0x26040000c501c42c088186401e102d0840d0400e00f0080d99210140920f006001002503010100750003000281c208503015403045a442800e21200009484107540309400b032006902e504080e440041408815108081c10564070a85048640b1200d840c1000f8182d0304504100210b40c003141e82032001103401080a58064406a114a0020203c01c41c90a0380c004041c070f0031040c00450f10b404554081841510314000343c4030034500745128104200c00580c550b102c140403070001101500803841008031346060302e4032101402145a1544c07648080c41c80720700c00c04918626031147d0f0340c2d2100a150440c0801b84800d041401e4424003a044501c9a4101074030072059004100764400c1c451100800b605d0f01801105050410307000b4665104018000d400c40c03000584c58070040c5902c00d50000300881d2640115242c01c807041c3c0c25542442d03102090341905070045590060648400102c124101c485c640203140c0390a07020385003280106001031b10307101d2900b00c1e04d003a46030f200b030304200305102e250b80d241c004e06140c = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 861841897 1250 861840647 861840677
    0x121b10170a0518071d060a091a09100f030602070f0203120705160b0d0b15040b04140423070c08120f01051903030c020a08010c050c19020d1b0b030106 66
    0x3410105107080560051000b0f2040002c4251034000c4000485c41c005520f407140c02c0040d031000c00c070703411804800d032511040c24a40e2050440d000d407030120980f45003509403644031541d04c0300070315030084040840e00e01808200080c100e07401049218040c200301c5903040c102d940001e007040b103000e9403480741c0c50001c5a11814400c060041484041030400224840c9107000b40e642d0141c06241d40700a07005560314a980b140e078a501d410000005403403c9443d50303881e118070001c41160001e02070112038000801c6200010b00301807045014484003000c100381015042c002c40071141600808003030401c151001d40d00d000480d00c03400f4000c601030300e40d0100414070b440c80002c000000c05a1019205510810314450140001c544420540c5d8040c60f0100300c40800f800410720003050b6911841c410361908003020300c0b19a01038003600700a510b02085d6825566494804018007900c010080c4d030000c468010400091018800c130a5540106042c006c0311130390360b090080071500242c0c4a140881d444064940350 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 861843147 1250 861841897 861841921
    0xf04110f0315030d080708060a24091d011a040e04060603030201050a0b150703020715090303140c1b01111005010f0603051b0901120603060902121b10170a05 69
    0x81040300343c004240103400e0140080c0920000303094038092058103004541a0b03114100c2c201c0c064160810401403000f43c85600d0040800d61b417070b096001511890001c540c41c0174190a5101c00018030102e170034541d00b048100c103902d24444c021500710080801c80052032103145481c0d40d204038080ca03000511036181d410040e0a4840060108400380d180c04904002030350340c030b02d1070b101e000038226010b80c442d07602c0c2c94140d1514100781c111501c035601c0b261a0f100d04a9000a209050740d1090303481f90500300d000d0f880d00000b40600325441c48a900003040c8000007030019090840350060500d0000714064089214600f07004035002c007124001d444400621031240442c01a0b03008106a180401c59440d041d903610301000300d46d451a242c0e86500085800d5103a1146a86144010002030208540c4d0368910b0544020251440204d000300c201c012640f032032000105007500c0306256102c51051801c090010011200410302c144070034481c0307101a00c0e01012024107060710484140c8000929420720782c0140320 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 861844397 1250 861843147 861843181
    0x510050708060a060302090d0203012a05040b09060306010c080d0e0c01020c01120222080304090b06030915190e030408010501120201050a030f2003181b0f04110f03 72
    0x38070254074203202041d1201c003151070444605141c010707110600d11000901080d25000003035070541c00c045800c0c5138500e99101c0b00104000361141403000c105d00220035901c81c0242d205009140105000306603850030600300039030b40700750140341211217000e1304d1340c45c145940c100c01c1960340c40d075642c2e0503060094881003080241d0b2410034002003003880503880000307240d28180b0075840c030541e07000300d14240c920010300c540c1c0310641100644424596180d01c8065031307940091082a440c14101010591a4280310b021240180c0c4600c1c05096150400100d900c41d00310003030300110000000503c3c440100505201c1d41c050300c02c03408055175035586005601c500352401a084a00c14008601820380140c0c1c00108817510f031405420003041d0350800c01c01441c001e0001030000400305041c0034400f003000001030001c3d0312a0700311001e15600d20991044c125907031900ba0340501500000d1300c00c420880e02d02140c803000220002017020415640c02203052183e0340100d0303101000c40e4404018007265142c2d00340142 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 861845647 1250 861844397 861844411
    0x110c06150109080d0309080d02030415060f0b03060405060d05160603060f080703030f090302150307080a06030c0603020f13061119031403062e110f031b0307050703051005 75
    0x4501d03d0034420903540380c54502c515070f03040c541d603500d0500070000d040007903c030082d01ca00300454807850142454001a014124882c1005103030003001303c1da119012100405a03403961a8040c00c55443c4418000101005060503a012002e02c240c400094800c00c002c00503904600c41d1203107500e14000d0050141e80d9983c1118401b02c0d40c800084c0b010a0340080c034441244d41500d082000f03d50340c14400d4460440300d80010350404466115106100c2d2207900650041217260b035001819a83e03c00400d0446295020051526607162001c101a51103a0050300c0c000c4107420700c492404450800f0b281805c1e0f91540040c01007030801221003000c2c40300b401038071184480f98a9916080300c207a540181048078014011080080c00702c0801e029850301440d014013008110604c14030210b0009a696950040903400e80018000b09110b580b101703000301b107007500581c3c40c070011402d03c03401310400084090050152980d5100501c610380c040b5408012510080d40520040c02880c541c0e49221401d440000705070f0 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 861846897 1250 861845647 861845657
    0x111006091b021504080a0c05060c0301031104020a0906031a06161106030c03070c080d0c0216301a0f04030e18070c3201180321110c061501 61
    0xc0f01c02e5082074182c2c869171148880e80c0d81c80f90071106440402c07100344090107a100711000c100c0240800c100450589010324040040103c48c44208816407007600780b0701d8000b0390881000c1042c14004c0d041501e00c018a0602048550815000300e08035402c503203c03440c800180c0d20820f10071702100342c5c04c214202400755020f0703103075140480421540380f1002c1c1c009800c21510501c00c4090202c107005682101c1e00d8942d01380898005050000d5851060f00d14030b4440d4484500300042030300c0a403915402c804408201c403240d1a04060102c50403614840007920ad070070141800d00501c245540b0301d5803203048007042451503820309080007002011400009070050124250803901a400d602c105036000c0e9051414039030070401441e001814081101103035030305808003c0215006a10789000c2071f0301c01d05010080002c0c6446010100031820085405404600c2c52080c00c2044004900c00c04030b608a407001c040f540e03401c1e01c000c050a56200c11950215078200506000141c440014155040b100910301 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 861848147 1250 861846897 861846913
    0x1170c0c010221100b071e020907120501050909100519062904050d020f0f060315031204060e060307170c030402010e03060f012304090c1d010e0403111006091b02 71
    0x40601e0306e200b51800a0105840244825624a260507580000f140c0c06010250b583c01c141c03601a201d0403c1700d6003c14824200400460301e410400081e5118075034100c021b1642e92529400f5400a150240504071143e9550355290402a020b00a20380107002030b050440d84c42c100d40070210140380c203e059600c0001801c100410041c0d07182d0b142c1051091701203c1c1d8810a40c9501c00040110781d0b40380c09103420800100c00c10140d07007422214a00c0041c01a0300707407840f40400b80540720883c8035500510010400c161070441c81800c2000140d030b0310012034180000501c10182070303601c2d00d00301141e00200180c000070400c011540d02c030000c0b501c5808107030003c000c0c0b4104141420340b4600c05004900d110850703800e10030700004100b00c00308580b02000d003040000a40c0d03030400f80c1c0350384014010001d14225095904a13540c0a0104880c1210700c0840440c1058445036421503980c003801040014600c00c4820315102880316101304802040f58040028400c0d1070391450703134685554910304009542004d80 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 861849397 1250 861848147 861848159
    0x8010506011d030309120318031615020a0807060c030e0c0d121817060f0702060402060a050720040c03020a0905090604060b031f09060501170c0c01022110 68
    0x124280d05400e014262902002d2800b0119141d809640c005642c840c80da207800d40e681c59800f1008180000411a840000840740400c3c141e480f01c0c02140d41040b0001c0d04d00400440340e0311243c4c04140c10107881611880300b2552101606500451415036000d503039071a1156004c0d8051080d070040030308240140192007001e07000a188074400f050080d001c2002100301c12061f40c0b0403100c56410b100340c0e00d0600019130b1140301250903024007603a1125984100c4001c680f0f01150380103118400d014540c0100120340d00da60034012039410640c1d168045c00028020140090100c074501200c80581c1c40c41414082100020030081d5180c90071500c041c5841042150b04079a80090310703005440040d41c0c0d9010540b04d600101c0e00030f00055000b4030944c2c0c8003005000b140c5a172000c08207030f40c0448000340d2011640350124001122014803420b40440c1c06c410702103180c881e0903402c490f0701c440c8405800c0d091038030421240c0c0c00d81c6c2c40024030300c00ca50078023148221104110000680c011b07000820710603449003070070 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 861850647 1250 861849397 861849407
    0x911270403050922051008060a0e0708030706020304021503061f0507020a150206010e0903161e1203050a0209060301050f010c0c080a03024803030d050103020906040b03120c070305030301030812010801050601 91
    0x24001030840da4030b2b581402500801001200000c10700c16044079666030b00d60030308400940095408901c695003100240d0070301c043d40b0060340e0043d0700007400011704030030141c40d6260b00d400345403440d418060144082c00140c1c3e034026a8000a15000d0a005045102c83d900241080c905801400d4000c03010700c01d20000078800425207040c0d0405181061110b00c4d1800d28441100441050a440700c25a544c01020007031501018410a48103407030500854440040101c03d0b40031701505d6607040441030004204500d08801d01205206040c1070030743d020381482e2603c1c03070301c841181c1112209500c81d001c80420182c4c1049443d1070300b801e217802943c04d046000b10206040340e44000450001801300c412403114903426030345080c6110000c086a9580d4200303200900600b6003440164455074000d0300045072401d042c0115411000000c0242c500c2e0f28084141d0207071500301e403050007240d03c5019000f10002da0200001c5010f5070241404580303035070417820101006001604401c480c0e90400c0140442030b41c0107 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 861851897 1250 861850647 861850651
    0x120c0611040b25030f030b0109080607021e010b010203090913061d1009050c0603061915140304051203100b0d0b03010c090e060d080f030406091127040305092205100806 74
    0xe0710b40400d8184047c5c004845644050b0819a154042c04061140341c60700021008540c088403a401c203045c5c0e99000440342214421158140560003c0018514900d4001e41550340038240d40010401c048081c0c0f0796908880f01c01c07520088076450010454034030b0b40c081000361390b110302a000034812403050b9507a4540740c42c00f008140f806101c0110203d0030596a01450392040d03501c0d044562209540c0e0254840054604641d800200383c500030380821a200d60000c480c03059800a004280014025030441069031008101901c0c0c0502208003148d081c0a000003000e04811000012402007c1070003018211440d0444103820300c034012400304840703101341d250243c0c0100e003241c04c18644100d60410700e08030304c5004403064030f08030000200b104110050b40020480381c001c40300c00200f01090414480224050301c4400740746040c103c3c001120001d080c030b03070307aa00a00ca0f2600c5803c10f5071482c0440c414071f81c0107501030040b44440d008689050b0780e0f44580c6910060302000c0b8100d0b107261040281d120320300 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 861853147 1250 861851897 861851927
    0x8010509060402090303370903030801050901031a0604021e0403020418050a0809040207020a172802060706090c0609140411070210021513030e0a03120c0611040b2503 73
    0x72070800e1f004d80032044207180b01c83ca2241c0c000c0c0004c400700442e00401c17851081c00201d0224150000101d002c2c00d20514682c142c0e41e202c1524050780343c50505440c0300520041910b64020707000c03c0b402c00d042410745440c11801a4080116894504601c10003043d1140741e0040210701e50082c81100c04100300250882c41d03950000f526964510001003c03a01078811020043c1d0012142c13000050014002d00c40d081d1048520016a2100d003c803041001201c14148055020424402c0c0110094600039006100c1a48900d00001d200015039a4010076a491988540080340c06c58904020070000810b04200506044074200949800c0000701010350280c0080a4040c034070410039080d40c00c2c000c01006401c5101c000c6158564074058844000c090b08000c401c400049400c540c60801d4200010594140c9910100c503184412600328211366060320000b0544d001621071070008164080c2c003000f880542010318861b43d44450042c00101c032200605001500000d564a0400100368841102541040 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 861854397 1250 861853147 861853177
    0x60510090605030703090c0620010b03060c09060d11130602030901020601120204021c0e0c150901080714070c1d0f040615050303030a0209150c03030118021908010509060402090303 79
    0x2a0013404800034020614001e0080c410780c00b0100741503812400407201140300d01700c2d0902c81074488c0c01c51400d81c1c407500350f0756405900010200703d400c1c075803402404103d2070242c003490400c6c5015600c801500c4985d40d03943d02c411000a480e5610700807020041010345a00c0c001146000d0040c00000d6507140c05204003c0c40f1301c940b220b1407003156241e804980707841d98007240e00c180300c010050800c0018021800282030611500c0c0c01e0803078a007040342c07084240318441d41c2c460742000442c0340152a17502c0000c1c82c04042014003503102d405118164040c04505004010310640710b400c5c0b404040e40c10100c0d00d80c5c03d502960000c100031209030560190341c1d02580c4000d0110b5103496000c114519500d080c1c110b5603140c0404020000c1c11a45640900328500c8201c4001040440c0101d68403001c4c49081410480354108200500802010119200000d114500010703d886010844007410701d0314403601e44002444103004011307601c1c0140400b50886401ca400b103191024103400a9502c0c4206d0f485451080 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 861855647 1250 861854397 861854401
    0x5210109051e0114042a0f0315120b0a02070b01080718060b160203070807030311011b0c062a05030f0c0301150c110402030903030a06090506060928060f0306051009060503 75
    0xf415040880d00705121b0058150038161b4118020f0000e250000c00d07480001d2030904c01e09124804411400d048075444000140c440101e5242e900c1c03120401040c00c0304a40d000c00020b0000303442e00c003e1078000d00528015055190401861031000d0000c1000f041103c0c3c02e0800a0102501c40300803030f054000c5023144030480380c1c5c103440400c0c1401c200341c1c00005580160070000092541000d040b030710b5400010001c1080303480c555144045000f401c0031001c00140002003410000d40e560f4404070a607944030b88641440c0d13a107001ca1042050f81b0b650300c2030000c0c3c80841406a8040313000149608450007040050656041007410040d0050618200c0108040e030782c14441800341150071010b05c041d0241c025590391401c1c1e02182da40f640107496400e400351400b040080c4045803880b80034015000101807503c0c1403a003404004032440c0d00001030a00e10703030641115015003400031882d0002c00a0340c55502c00b204000e980501202d078154000c030701802c07902c81d07407001d41c55128046a065508505000c0c0d229 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 861856897 1250 861855647 861855671
    0x804030b0c12011e240e120a1e020a030602090112060311240a0c020306151e040f051005030c3a080403061b050c0d05210109051e011404 60
    0x800450385c400c460740b6074480303410082103110004c1c10014040c280c40b030122a800704410712414010020400029401030254900000c103040700d110585054a22000e03c10b0216800048101d4040c0c0c1c802c48185a00041c50629540c02000d081c075012420070040250a20350348580c450071104111b00391058501080946003c04007243d0140310102130340d50300e0303201c5003c0c1802800070459120103a12034072454002034040954030b1101168510007510180412a040001001a8489100b9a030340540c940002190100c202d2103040c0c850b66107020f11105461901c030500d8100b1005042503030007102803002d0446420201d1040d420b0b0908400051318100e0494a150001c480f00c00c0d00007030400f003002030008103000082d080150001c091600c200138411103524103031007034450707407000c050030780c2102c517482818501550207000a0103541c1080c40310410b2244802c46461000d03000700524641c0e440030f1207811801c19010182c00c044445100c030b400e5050004c0d482e0b600b111084014440d41d00c40c0301c100d0f11 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 861858147 1250 861856897 861856949
    0xa0e0a0e0a110a080f072601050f0f010801020403170a020a15060f090504020d06110906130e070201050402210a0b0a0506040c0302130303050d0b030304030804030b0c1201 75
    0xa00320a0000e5805048103450505030100d01c40c03254074442c0c2500c94010552090228829501c0000000209405071906030b840c5283c0d4016403030004006048141855407180c01c0c01054030614819000c500146804102501103d9043c0c02601d8180e00c10302040c00003c10f0702c14200300d0610504a8941c0700e000c0c0c00000c9203000e5098100504910b520a900c0e4507810107504031000b071301c0018044404a03038440c0c0494048900466020354003440d105066404221590302160003e1007410045140901c0103003c80c0c02d552081c500a04410b8440c0410400c101c0c0800074160048001d20003800b17070b4285500010501d4035000c00a01300300b506601030741081441081000d0903e903100d03030340e8039281ca4a40b4001000302011a213141c025810b04036511b100314407a20844160102c60054a00e80b18150b80b02200c0540160001c42c1e100e965403410700070556000c10280000394440d424541d9a2400c601d020b0b0000390300a00500c00e0b0800c2448022800c0d4149680305055031144400c000b05041d414440b400307 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 861859397 1250 861858147 861858161
    0x1c05070e09181905010b01080c1210090204060f091d010b0a020a05010c0302040302030c0d030225030206160c0b1c0905100903020106170609070b0a110124140a0e0a 72
    0x280d0341c0300e141480d09001e011034800c0b8120f40d0183c0001c10000c0604001901d84142c01c503140a0000c5080000f075205808110589405c402240d080d5a101f0361180d403083d00300d90242d0003c03008078103054030000005a1083c00c1c01c0150012403124085001d41310040201d00d8018010740c41d0603d00801c281d092944204400d08020790008000d10902454030380280c02940903001c264028018240660380b08c3c203024400c201c8080d416070081205800201780306401800f5000d0403070a150310303124004050398800e80981600c2d40794940c855240a450725091001070056801103100c1c030b009002c1808441c800c03100440030300740c84d0b07040412407010382d00e030142c2820410118007500300d141903140001c0c5941503110ba0b043c0c90210500f044402c3c0007260640e40c407a01203035241c0586d80841c405014441d0340502510400da5a414402c0300700700e80080c02800d4a0148008441c919019080e101c0300300c0300f11072000000c0491100503c0d8241596002c10b4011100740100e40c04002c11102049660b1480d6018030 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 861860647 1250 861859397 861859441
    0x30b1e03030d0f060e01080d0c140a2315240604051f0e19030f170c010213060924050f0c0604060f0501210c0b0a051c05070e09 56
    0x1243c900d440160014115402070004201422001007108540007071540040c1c5020784030071580c104a075990704000090b0b28102840f9006401c00d49000950034980415001c80004013420307000b09a0b0296481e00204001c150002c22101c024450081c01c0101c1010741c0c0d5065580401c1e860314410b021038010300c51540006c1e080f945812140440c0d00c103000c0c9101c4c2965840d0b6070614500300010401a01c14520049059107408010003080042c007880c00700000c10b880781c01c50003010340c40542d5451154100364061207003650001107640da002d1107810030300c2c003a10007070410b1150306081c0034503030380031080548240c0c0400102c1042840d02500442c1a02c2c0c0070020302007030726030352804103d0139511a82c3c2a07804444081c1014690030f1524160b00609058601e1072101054600d00c03010b010703680300040413043c2c170800034109011907d42c100754010800750030a501c40c0c5030384031025070900d05071000704407020044d03e25100c240f001c4141d000c00781c03056410044403010110b440744010a00c51b0a1049403007 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 861861897 1250 861860647 861860651
    0x180201053403050d0501080105150f0a15202409010b060a050a03053405090604030605061008220302030909011215090b1602150c03090706030b1e03030d 67
    0x10404250f4410000d00d40002541401d10890366a041a142a56410f51b160600d1540304500034055080c114454002e4a8000b452020710990b20151f150518140840407c00522101300107050508115145100c2d4102e40f00200000c00204583d00c0103076280341c0c0000001581d40c004680b10f09403d41001c041c51100500003a030740c145188010b40030307901c520700000109050100140d03042c046417070720902d01d0554240c20800400340c80221914120010600380c180402440852450744130310001d840903512402d800505400c02c0313402c1000c141103135620201004261010840d50607402c0111140120181040e00c2d0701e0304640c81c0c05d07810360041440e4a034001120000001d40780c481203003036210850180c0010318a4255000c110000e071080302001a00c41d180350350105280401c003a80700c800c1c510451041d07030b80d007240300ea1101788840c00541d491340d6081c6c03001c400e220b0b000304c05010a90083c58281420002d82c0c0440c00450800500c0d500040003001c1d90101000c0c03030351800c0c8110f615403a20b41d002 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 861863147 1250 861861897 861861997
    0x603070e130608150114190e01030b04060e0c0117060a1d06041514060901110615091f0509060d080c010e1e03180307090f0b030118020105 61
    0x110500815842c820466184502e0144c0345242a11101e0315060301e13540da0300614841405400c1c40160507980541050985045e1030004802c6a001109400703503109802040e503904085c20008251014401c440e140c03508840c05640e120303078004071b030f0f00c172081d000750f040c1e4040c0c0ea90200025440560342d80803030000700d032106400c4185003080d00305a118150441d4204040e440c1381e81e515454030518040c5c11300320500c0b0b09d4090140e00d8200080d0030744003014503040780f046041e0780703140c0d041a500307480180d0075088120252a2916101e8903a60784119440a0f10751103031102c1e60b45104049903441254040d0f104400403130032079160004121000d903004082d882e0358501a5031780314000d040c2e003c4c3e03141444c060310700c0c1c400305601d0301007411003040e41d0704006500f0100103450741c1c00040407245001d54144150440001c0c0c2140502400742c1070b01c011507002890111800038582500c1e00105c02d01d020344456a100ca0040c2e03084400e80d00e5405060a504012078814402c200b10400070b000c0c100c00701c03160220 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 861864397 1250 861863147 861863179
    0xa061d13141c0305060a14030304060e04020912010f051b0d0207140d021605100e040c020106050907212d061e051905030d050a02101d0f06060603060603070e 69
    0xc0e8001c0c0c500761045040780b40da0f01382c01224003810031f8640d42d064004000c2001340c9132046006488241c0d000b0401450030040400291103000d00207140c41441e5150026514a806103209030380d030040d0411194210072841c620800101c0c4645100201096400300b10042070115041c04007562100a904403801541008400303075680c0802414209186005000881e141c100300300ca0130070079805074840d000004891310420010304120b503180811990381e050002055581c0109090090f81582c03192602c050708003e4089817400e040744a00d125030309200101410030502400f01e5100c2804a405122590340e01408502400107580a80581c2c0c000428003900310410b03c144004503402142d10381d00d00d02c00807485400d0602244280f40d4160800c040c4294814000e80c02004c82160520545800c41c0994044900721030b1004050603000701f9290b18585080400c202c81006c601514004040c0c9240500018015100c0100741078001c902c080301150b0703124041c150139044171400404104124040e81 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 861865647 1250 861864397 861864401
    0x718180212150a09090c03020f240a020c0103090c030b1e010305010c0f0c0c180e0f0c03010e0303091f0207210e120a06090314030a061d13141c03 64
    0x4924074403c1070444000540c02c480c500c288603100d980f0006600c1c2c01031442e002c00c04502c82d1140d02d43c0c2c200c0d0312094020810300030219001e0410b442c1c0000241c5802860500900d002040c1d8841e80c11701d0718000402022822580c5480304a80e8041c0c0c54100d155036420700b500c85200c100301c0b003200c2d440c3d030000040200403064000803c0180a99608030103e0444102120080381c0542c001e040d91140030402d01100070101192000e400f0503e1001c61042d0740000290726101e416075500e486900204e0614042d031600307020b01c40611703007140021811410060081354903032198a002c04804400b029030849484050340607202010b0300040b070411604064082c281000040e01c040030001480d40071811000e28185601d6684805070030b0083c101c40019943da1002812201020b80034001551f50b0110702c105640021881107147c604c020a0862400707103480781140e0400c8000c00020005400c000c21f4551151390038041d1500400c1003604120075032240d504003c021241a00042c0001450090040e019 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 861866897 1250 861865647 861865681
    0x90509150f0c07021f0216030206070605061c030305040b1018230108060613180f150c020d02010c0504050f01030c030608010f151a0324091e0718180212 67
    0x40d800f51590400a115041c2c2c0007041404000c0d40f06400707010040100b3381d10303403025500c0f00e0003510510100401c40311211501451250403000039494404000400c8640d0190740d4009a901598800c02c0e41000c1c44043c10903041c960500c03115a40c1d15600041c804c00c041014541d07441d8081c00381495844000ba0350310b469048408a0240180b0014154824200c1c80f0703d40b0303600c5914090307a400164131703500d40104424401082d10400d80c0101c0411220841d88681c0042380940d8008004224422070007a00323655110450100b072080610040085445aa40e101c0b80c41109190000e105207000b00b05034004d05813a00105001d620741015012002d40b50780c400280110000340340c1c100e860340ca40c060041c80702001c0fa107a07094541400442d0131081c004034442595284144034100990142012a0200c901254503039010740070001070301c0100010744015038000c4124600070380c810721508603c190300b0b80c1c1d5100308a8070703020a148550140c01154140e80d05006100c0d0b09509508146000b15060080 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 861868147 1250 861866897 861866959
    0x31a070206131113020405091303020d0c050604171201090204060315051809071503140f040302070e1801060b090307050d1e0201091707090509150f0c0702 68
    0x1280d0200b07494152034030703810084581c07120205504810703a400b405400c0445400d0320150035001d010205040c1c0d103149009102d0034041d207071202000d02c0ca080080c50304240000c0381d828170101000c2c071000316102084a540c8903420a9421043d04000200100d151040c4403d1041281c2042c002190a2600b40c0041003100c83c03907078060000d0142c000903d907001d000740c85801e90080415260414816501c1c0718503074001c40c1c0350180c902550740d4940c10b60b01c2d45000005100001c0c0d98903001800301c2640300384150018031200c0701510a20341a90060350782c40c901d0042c2c1c44040e4003200000c58540011600000311000b010080c02000e59800b0200e205030801060039109000d14207000c110380c00c100050501c02c54205034004604840003000508002c0b00b80001da04200320b604010410120b00210501842d0a000003031140394540440e40d822a40e016100e01015003100c18128034080d004202240c000d10b46040d200842c0d10390f5000074046107e032a00081d007105951000398042100340141c0390f44110 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 861869397 1250 861868147 861868153
    0x2070806010b121303020a0203030a181403031215030d0513090e060109020717040b18031c03020309070f1d06100c0b0603162705090d1404031a0702 65
    0x602c80d820110140144080c000b01e0329004000100980904004000d40900034010b9074040c0c8040d80101e070855021080031008a1100c400320b000380b50140c4001001420402403174000f001644000a440c3c1c8218410749503800384404c04a0b145c1c2c06903100f00928004002e003154040a01140085c2041c5c01401c84040000340b070f00b400089514650044035211740400d03000e0702050782000c8040c0029008a4415148082d4804000c0e101040e4034009101501c4a05185615031101000202003001c0c0703071544a0007600071600c00b075070b44c0b0300e501540400c106140c100540c403603890a005034a003070303841e501c01c020028010b600024001071030b41d8090044a02c0703130040d4440d43c3c3ca0300248051001d07858000000541c070f1905c4100400c0068010356000300004081e00c400310084240c095504000b0340141c40088204800320b00004000c1c00e514558010628040c04503150040a15845186000d40c1a01307224101c41201d200c0202c0c40b04417005194001d142985522020218640ca0203046403007001501c = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 861870503 1106 861869397 861869399
    0x52a16061b03020a2a230301110f0f16030804051513030f0e030a05010b03010b0a050f0616060504080a0306060c020d17070c0806070e0a0b030f0411100207080601 71
    0x51591b0303950031042d0001c08014982e1a030011010702c82c1e071400490790216052941a1181c1030129840c540d01c0341c00816407056184207901501091022030150b010402d44c220220b680500c0c0184102d4140c0d80380301000b241d00e214150396917022403014049520010344200541101d112151510b05c031001c1c84000801e10740141f50404490a9440340082d034003506007449184180c0038222805400d0b039241c207011403140c008541b25580074a0700090306200c0010103c6283c0c01183d840107040000d0300d090308005c10507030043c40ea048000f03400c2031000581c40d03105404d941c21040e0008c3c00f02848854a40e55200c06029840741d0b410345900c01d20000c400725550036403203c02042404041c00417443c0c040c0c801420040c411001501c500001202884415100c00079242d20480118140d01d0036125400c0480c45200340c20101e66201c0052500703465510340c0851003c04443c14001220001d0f = true := by decide +kernel

theorem cover : BRFrame.Cov 861690647 861870503 := by
  have h0 := BRFrame.cov_init 861690647
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861690647 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861690647 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861690647 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861690647 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861690647 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861690647 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861690647 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861690647 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861690647 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861690647 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861690647 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861690647 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861690647 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861690647 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861690647 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861690647 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861690647 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861690647 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861690647 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861690647 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861690647 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861690647 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861690647 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861690647 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861690647 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861690647 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861690647 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861690647 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861690647 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861690647 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861690647 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861690647 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861690647 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861690647 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861690647 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861690647 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861690647 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861690647 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861690647 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861690647 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861690647 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861690647 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861690647 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861690647 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861690647 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861690647 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861690647 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861690647 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861690647 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861690647 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861690647 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861690647 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861690647 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861690647 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861690647 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861690647 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861690647 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861690647 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861690647 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861690647 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861690647 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861690647 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861690647 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861690647 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861690647 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861690647 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861690647 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861690647 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861690647 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861690647 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861690647 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861690647 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861690647 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861690647 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861690647 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861690647 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861690647 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861690647 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861690647 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861690647 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861690647 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861690647 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861690647 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861690647 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861690647 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861690647 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861690647 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861690647 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861690647 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861690647 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861690647 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861690647 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861690647 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861690647 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861690647 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861690647 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861690647 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861690647 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861690647 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861690647 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861690647 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861690647 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861690647 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861690647 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861690647 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861690647 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861690647 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861690647 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861690647 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861690647 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861690647 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861690647 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861690647 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861690647 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861690647 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861690647 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861690647 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861690647 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861690647 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861690647 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861690647 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861690647 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861690647 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861690647 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861690647 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861690647 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861690647 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861690647 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861690647 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861690647 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861690647 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861690647 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861690647 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861690647 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861690647 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861690647 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861690647 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861690647 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861690647 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861690647 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861690647 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861690647 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861690647 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861690647 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 861690647 ≤ n) (h2 : n < 861870503) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
