-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0073
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T17:41:43.208394+00:00
-- url     : https://prove2.me/submissions/4ff8e352-aef0-4d10-9b91-ee4675cce5ec

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 12949647 ≤ n < 13129503 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 12950897 1250 12949647 12949679
    0x1504021e0319020a0c06020d020405060f0c060703050115030b030705030303101518030303091109010f030201030e0607081303090806010e090606030c03030a0513050402041202011206080c013006 85
    0x244003c500c1e104540e94080c02010701300300301804140d804241c102c03130000b90343c0c1102d0280100400054803000c19102c0d030809642b1100000c800341c00b0310404180b01c2e40c064003c0e241031b2411502d01c60140003611104400410515119551612442c1000a02074406000442c0100f03511000444110b0404c5a042da4a003c80d0324070604201c4007281c42c4840e0807a5600030002d680c0d140c5808030710742410307040001d10352454210183d8022100d80001820301d0700003203004d0072a4404e0706c3c14042102d55095894640c0011640c0c4400324040070009a213000e1004c0c0c1c00346215120b0b05140744561340710900c962510100340c00850044880506200500400308a0280d001500310010942d10305000d004c603807280104840d0000b403000100d15400c4810110521703501a001c040c10442d2503c0e9118000b0040045500e0180d021900c5c07030120085050712030241c00700b038130980001170061890a000440308420760b07410192804406288981a9442c8050740180000c00c1c0031001c00d0013410150040800006 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 12952147 1250 12950897 12950941
    0x10b091002150402150904050703020903070f0b0906030903070501050906010603052505130306090f0b0f09060c0d180507030c06050a020c0405070905030f060a0b0a030305031504021e03 81
    0x10100b9030b07510551100c40660280d03041e9030352140c03111420b5020155014445141d41d101e8288001c0080a03641a806000084003c42c215078085031750320312105811209008a51404404210050903410400001c0d074210380840e080b01c1c5809031a0312150300b110350648401010343c03c0140100003940e03143c0241604108207402c03814005071055502c00c400d40c0c15881d8103040c80b81c00301e0186000c02a00c59280c0045402200610031300c2030760f04d0b0012904036014403c6074604407503004200c214126490241c8035900360f03402801292202c51f00b407a540e030819000d000c842e984a007110001c00f010755411140992142d001080c0480c11841c040004078801d80201041010a000100702a9400111609128010f81740042c1580750b01c54111402c0c10f06400c513941500c02d020980c004a0400690f09200e4203d414041200c80380300340401c11020368921002d40043d01c1400858068404942042e48402000300300610342001c420300b840d000001d6007100304a194007c020000f01991906425045d801 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 12953397 1250 12952147 12952153
    0x6021206060405010516050c0604080106030b09070305070b0306031006091a0f010504030b220803070905040c05030402100e0a08010903080901020306100c05150f04030e010e03060604020d14010b091002 88
    0x200f4000001c000c0d00450414450313280c406241c070802d00000b03000740700f4001c001822455403140c540c46000c0c060204c5210449008143c94001201c0341070101c2c4c0e07107054940c040302038040d2900d004005160b80d04042d20941e818060038688031280d4800740310305c80013002c17660800701d0940486030008442c8034503842c0c4640207a23143c02170140d10760b07440400c035816241d01101c1e056090b01c841080710301000100a08100d00c50400c041603040c480b40c0d43c0511302c50f0b4000d0740c40209a603210310510051b200c1c011401c802168092012600618058800b0028a540d920700105125102c400090f03500405a10204090b552221418241079101207659800000e08009610703504005020446801d0b43d9058401002a02611a410000c09004c00c42003098402d0246209040c11440c0e400380d41c070180d5044002c200c20300d0309031507594001c0324543c1040000801900320b80d80c5030b10501c0003952040f8661006150340d6442c40c4441d80081d11180d004c0d0900000590321007840d00d090014043d1810f090b201954 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 12954647 1250 12953397 12953399
    0x5030c031f020a0306080a230304030201050a0e01050c1608070b03010e04020409080c060f06010e01081b030a0207020409060b18100915030209150102011d1207030c0b0103060212060604 81
    0x3030320340504402611104001a0f95208031501140208061b030001803190143c44424030a01031a2900f00c2e0401000001001c5400510308109944c1e01c10343c48001d01050741800704900c1940203801a00c041c13003060500c5071528103021451420300100420a440e14080001c00344410341c0200300c1440505800c940300c9166504111400980e500018002481381d0307143c2c0340103c20072155400f41c91304400d002003103860b2414640b50314100c004c13080300d07914001200750802e5501d039031248c40e05030701034003030000c00c54a00480b0b0301e400301c4154001403080d40305079020031003000107840780e1041c582e803e8000c82001441800070002c00a000c3c403014040c0748601c02c0001440700044a019103201101d140080026900c07003403100c0030b0036269081e031000e54440800002c006d40b0000400e01c02c17440c0d600c01d034003c000700b03400303600820708580f40c060288031a9840501500c01030768158009003a0140030b07050401c224540c07a6110710468009800131141070750042000c40ca03e142c800c01e489d40043d0308072200340c00c0c6 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 12955897 1250 12954647 12954673
    0xc0201090c1e03140c100804080304020f0109052106070f0503190b0406060305090d050a02070302010806030f03030903070501060b0304030e060d060905070507050f060f06060a03060503070f05030c03 87
    0x1011900494505108100e802440300d281e00c07800b54000e541c81400c83e440030403407400654075185018140c80c0151414a0b098003068410380907240b06581c4518298150340703640d000d21142d40c3c8000000e038144182c0ba6404501c942d01c0264022001580d120790121000d001d02010f42003900103030a62081c4113500c90007aa00a80040a4903801a006605403100e40803903040ca03030140a0150b1100c3d001454070b000414000d81c15004644964203243c200c40c041080782004880d00e219002d5111300680000105000540c45401003e4000000404940c3c90350400c41006047d544190342c0800c40790b0000a010040040c03c0c01403400608100c074816096107002d440c05440541442c0c0403500c500000115246001c0d561380c03009000c0c01c4141d604001ca481c180801030704940c4503100580e000d11031301100d460010000207041d80b091800e490f802545460714030500000c1e0704940c9c9580249503d0300380215407a00d0802c5107000a00c1142e9000a00740e10302800d142c00c0c200c6480d8001e010b078011134101005 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 12957147 1250 12955897 12955913
    0x8071d0106080c070c09020702031e030a0c140d030b12060106080f070201090b0703020307111b0603070c1b05131404020f0303041d04110603070804030804020a12050f010c020109 78
    0x119030141c02e00e41015910412908030074440c40400804001010101142e500c440340c2c083e15000d44280d044843d00030b9114417001994002c15041b5200e40d0007040b030703408414441c54002c44082c0c4209074550988198064040c10481034104450009940b42084030f02441c05484400140c11440301901c220750400341300610200340100300101305980c1502240002d8400d50014071042d410454039495418400c100801a41c41551003800081d0b48142c0b5144080c0c01180b0f402c0054a000200728441d8160030a004c0c06800007000d4501b0700c4a8014070b500499404806c5000f00c1c2c206008176100079081c0300812505200d1a091074130039034940640c10b0964019000f02c0d43c0c015070119204911000d014000a00e1441a50404100c409451004401b03540104cc0054060391103100ca400c8101c200c00144210741c0412a80c500025220340c000c140400c4c000d80d40c21360824000380c03910b4841d503111a95064001d020700e40444141e80081000d540308035003032290104042481c4000c0c00030244c03d44403409 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 12958397 1250 12957147 12957149
    0x90403080714040509040c0905090102120a0b1203040b0403060c050c0613020a0801150906090c080a0b041d030304020f041b08100e070203070501060902040e0c0a030914010608071d01 80
    0x744014082c203400c103114801c050360001e000c0208880340614152074070403014032031071054088484c00c000101c0c070890010700a503a24085403000c03100031561410f422801a0035140b80c250341099680c5612091b958041c401400a00010342d801ca686510b180351510884d0310a1054004101c010321800c003005e5004602c3d140c105540b6010200291410300005240c0c01c41c980c404501176213048540103440400c16203010484607400800c2003001d580b0070284050f9500b40e0260000a111400011000a0301d80e03c018500c0401400000e040d201d04400344c0107140031001100c40540c40070082008500d08860924584001030320103000054032003403810107a582a00c40d020510150000040314807036403403c2e5400416096520040a040c44080a5160b600c049411f4840d9400c0010105540c2003a0007100c0455084402182c096038075807040c07a801b0f81200d0f16090800d40c81d46910000b2910700348854001c400e400300000740c04bd14000d03016240c81c9041c0e0080c280d071142421502c0ba28803488042d28 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 12959647 1250 12958397 12958411
    0x26040302040e010b040204090905060903040308040509090304030804090b0f0a0f0603180f0b01030c0605030903030a020702010c0b0c03011e1a0a1b05030d1d100209010e0a0b07030201060509040308 86
    0x40346200b205400540902103020b441d82d0003920120b0001500c41c00e035080ba0000c0c60040048d05d405d92105818a40c1b01c0c8140e00001d403443d2800c120800507420064102c0b680505000c00344d0b400e041d180c0c0d80340082503025a1140410645881040e0f82518006105111510ac21a407041e6004c0c0f5201e884401d641c203030320548060643d6194525046c1034010f01100446920680294024030705e45410741700c4080030302081d46e400405603800304080d4010320449001d10b0f01e0074020b42c1142c2d40c1044800280d4001482241040341a07000b24001618600700603014440d85250240c99604001c41410000c009040c1030f00a111410000c10441500d09020811200390603803455a0b10443c3c007099401030381a5021101641c0000740c4101404800b02c09005400621801403121030a107001900d4940c00d4081d810900750083c003081ba054940b25402002c00710303810704080341008100400501540d1880e800105603242c00101002016420710507131002c0d00046131041514101518020300030b80e0010700c1c1c4 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 12960897 1250 12959647 12959651
    0xe010c090306050604020f04180506030303040c0e070c050d0908010b01090b0409090819020109060614010e0103050a110a030e160b0f030403020109020d0609020901061103070303150503010c08042604030204 90
    0x2c1505501e9a4041f03d821a88156259944660310002c7d810700c400070740445103469240c00d0105e481441e0100840f80940c0d0401714040310f8034100740c000c1c848c448016002c5410301034100f1416000803024400c050360066152110001340303280428a030b0946105034401c42c1040b00c101d0b403d203c1040c0400c02e903401d840c1064000a0b0610552410030094400d0a10341c00544030f0b002080540151b0540118105520801c0f00744580c80d9241880602c070741014440500ac070350301a0310241d05511a0f03000d180d001c0d103440c4c0040759014848000785240e0b8002c050307210000b40c450010810554040101a200154042004440918103400c0c0f154a0007850f44080403000c0000100342814401d402520381d260300285011440484c2d407030520b006116020003240a02c020320000584036004442840f8490226006146824040d07a0200c005006031981000104841c200124550f01c00340f040190345805a1148141800c0a05000da000c044c0000000e900c1c036403190130404411101001d58049030f9042e280 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 12962147 1250 12960897 12960901
    0x9010e031e090d0c03110d08040501030906060306110903011a01050a0f0201020409050c12070201090305030c1308060106110f06040309030f050c0d051c030207050303010311030717100e010c09030605 87
    0x5820750b40b084000280d8400388480c444028868010518012248609941b000d81040f803400d01044091450010b81100401d000402055010380c201c1c604041c418240020050707120740d183c0c6c00301d0303803d0400e140000c403002c9000036203030070244614030030010750b10568000e070f901002c0001d00c24401c01d001c3c6002c10200d401160036550003501954068036107010144003d2401803410342007600440204c072680591040840c1c00c050061003000151901907907114910340d030754010704100798080086003034020a05c08002841c60401d2100074060700c1242d981450359200392180b81c4ca41b640351803d0b11280e4124070203000010303812010380d100302c0340e01040301e0b14100400c2c141541461441100346400161240d1010204a0007140202000d01d241c100031001c100c220070b0071001c9020380c02004104d540704100620120b180600b00203c0000003c08590506850394164011100d070840f070207072203501000c9101451030b105d008500006801170020004661500c2e801030503844a0710003e04020787d1900 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 12963397 1250 12962147 12962197
    0x19030201050a20010c030c0516021c060504050d020601360f020304140f010c0905040902040603021806090105090601120c020c0312030a14010515210f0f09010e03 71
    0x401144100403a80440400310001440c0501905c14400b000b00003929200d80035107550300130340c103580b13600200302412200c803070041c0d0034810100c001e6211054045454a90b06001440502603980708038800e001903c140004020003a15120701070b001208411407909814800c4d1480d060203402e0540711081c2c84103550311142a880013407110860b4000b0442c0000704200520041d2000c03070325401904821103044030001e40c0307800d01f260214941a80098181c140810041c40c01e034000742c031013500040c000074103c2c0e620340c0050318004103c1c45001c040c500c507008004142ca01600c01030b00401c000c0d81d4058541c506072000801c001a0b200c0703801d43c90342d0356800c40da001c40c1c0300700107803444c0000160032104000200c647c020340710b41040351a051614101244004082408501a412103802074050909458410314210454000d0228125507140441184413103c4a030b02c1642e0203041403c024113110b0034030341c51904030031034010310300340880e8148449950040b4000007201d0140054410360581504980c0c = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 12964647 1250 12963397 12963407
    0x503040303090c0b090108010618030809120706081e0402060304060509070302100302070c08030f0405010f120609020c060f090d141603030b01020f010b0f0d0206090307032019030201050a 82
    0x1040540b04111401022800c51004e0b8001d004a1200f601c840c129a079071020111030580d10402d60a00d0403030f49640400025225902038072084c0401030092000d9070680408618080380d0b5448240001d82c10400d020301c50b2601021a40f8400504000c0039082c6410780201d1514400504000c1146076550001000d15605221003c06154004c0c0a50751416011000a0194106500640340004101000900c4a0700002204e0b43c005401c1e2405003031038903090064440b2004066050140302c2070310030000c441c1c8910710945014180c0d020340161904070500034145820001054010000c65960138032065000004230f44214910390b291a000401054441c0c060901494400c40041000c60240404058040c3c21242210400f81d0848070300c4003070140341509807031170074080799042501014850714030700b0800e000082c101d0010b008946800e00e07590209142c04420760040d103420344040701d0800f03044020715041c100c20340b04032802055800081116000f0000c0c41c4002814042c00190f070b42c0c1802d0040d = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 12965897 1250 12964647 12964661
    0x50607080a15080105060a09050103020d06020304081213030e0102010b01080c030a02121303110703030804170705031303020a060302040e01180905030301061e080f0601030c03020c010903030f050901050c0a0503040303 95
    0x5000d0b41d401e1595020154043c001c25250f4901c200020344011030703c3c043c43e11905040b07a400803c490407003506600c51900a50012300140c40726a0100101d80b40000c0c5045400e010f039a04d21000520b0044908004107401c6182490700e04690419500b240d09aa0181e1110303000a183c02a0741ea032911540141d400900c241c0310002c0088140c40208400e5613003000800d80f00c10f0180d190400c851a561903d5529502c85002c000c01140010011a000c01d82c415802445042c940e0101e03403500d01c0c203443e00c81c619001041d8040a08880200500840c10094000c10080c000ea00b019401c2600300702d00801a10710501440c030b1901d81400a00b03142d080f440d0001c00c00960018241c0340e0340d507100c420082030196000a4903c0c04411003055408051189092500c00d80d00000a08000e03200e1100450180040508100406809100c10821240280b05141c1e0061007524002601d00d80190a50103840c1c0c001c16642c05a45442e0070881502c10000485074200340320700d40b1650302e507036518040d8010300e50 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 12967147 1250 12965897 12965921
    0xb09120f0109030302040302030c04180602030718180b0301020f0403061e0e15090d0804020f011e030b0a050301090f030f09030606030b010e0610090b0901030609020c01021e07050607080a 82
    0x20300c41554149a0558010f1098a000f49c0580c2d0a4040000a000540703070402044503882101c3d5040c64081001c690107590070081030324100c11811f03200c017207010b1001903980040e03e0194400c004c03100081080d01c50b0040d003d070160029403d0620301021100701d0b020b58413000e05000e0719001c582e643c8081034004047d0080740328408210300c2038400400c40e540d000d01c440144510001c0d00105040d51400143e52100010690fa102030b640e58075824004658a6014414140490351b04000b94000483c100a03080e100590760004a22000c41d04005004449074071060190740f51040c01004101a94540070741281c0504050f0011140d0074001ca4103182c0a45c00580031303616050b40803003001148807066048840580440201c3c1d01d514003000560709a4020180124ad0f554008006080e2000c000e803e0a8005050002d54103035103407588420382e4000b2081c1512651f000400e07100c03840c2242d001c02071441302540c440b401e00348079a650a9662802030401e40a02c0345040015926003001c0e000f0040701c0c03803 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 12968397 1250 12967147 12967151
    0xf060b03090f0709090b04021c02130b0102071a181c06061d060a0303030506030c0a030f0b07050408030f09040e010c02060103140a02030c04050c0c0d0507020315010b09120f01 77
    0x2524522607516007190350342d082040d025407403000038861340501580c0003454002444c400039803501e0b820007006011000085501d44100481ca0b00903903640c8032696034908516401181904e00c1e84002824000260410404c0c0c0c2400a00d444034842c908059580d850a04141464481d05803400504569443d140301502e0040d5401c4220401c5181d4020000300c0c0c101200303003a00100000041548504200c515541000701250104003103442508120380040c0b01a0680b078941c440b0b240807602c0c1410607003041e15a481c80300c40c403600304000e95500541c003202d03903d401c5060a041140d01da490307102d0302144040b85040400e40d15059030f85c9a00902038845150000c0190301d0505001a4942c5024403054444103140c0103800c04032035000c107100030110b9000300a005501c01d0041008020300c0c0190558440e40380500c0510b00200341001504080040d0b9268161076408620425140020000500642e43d17584401003120346640b9081c0c4421001c1103c0000402a024050502d44410417818803100d42c = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 12969647 1250 12968397 12968401
    0x80402040b0f09190c0e03031c0b0a0305010e070801150306050709090e0607090602030901050f07060b03030304080c100c0c020d06140c0a0e031605011101060b1207020609010501080705040f060b03 86
    0x1000084c9144001d8003a0b920a00803102901c0c0f05803906560a19000d4140c1c03c10416400c41180b1005248030308903007c0000200c0984a9002c9006422540c0003240d86a558440c81034201004102250080051800a019880442000000003a0144401421103488401090750680103064550150408a908001d41c0e6102c21405640e00d00c180d4010022441d848804146c00b0301c04411200307203413410b841c1da91800784070070407034540b0740d10810059812a50721060b495240d43c0130300007140114046e0707011a480f00d105c40701c0c0904048a001c6168001c52405030314031000d84d00b091402d4619a01111a020240021b01300500501107248002da10b100c000800c0000702051a405400c005013555120b01c1100e080009066a805903045c41902840700404100001e40c4a000402c01d9010381d803001045440e612106210207400180040554401460800c0101a4100801d80e841001c0000078881940b40ca802d80d0744a62107406040e01079034450f1140200d410164021800800c01040035640e01c0c = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 12970897 1250 12969647 12969661
    0xf0b030a090506040c05040e070302060414030109060608010507020622020114130608011403030715020c1204060203040513020703090501030c02070812030402010206070f0e010302090d0b0703060305010c050a080402040b0f09 98
    0x38085500850f0f04c601c1c03402320917041c1c90030700150703800a0b25405010b403442c0a0801d81c180149c8140b00724242da15640380c0302004006020740c0103240c014640302c130010034203003030a21300070f41411b600400314140c02ca01840028150031180120310001c0b40c082c04d005400d00c42c1a626850f90748104000d0300c2120781d2010001900d140c3c00700081d0b04960703c00302c1c0800d0420a1004042c0c90784614130003d41840c1805000c11810341d020b5009041100d611011904d120034100940d60458016500c140d0150300003140c20441814480340302d145280881c00c0441c40d055940c4e60180814600340070f054101030781c3c0c4680c0c0d2460b5000f001040c0c0604001c20440b5410840040c1c00756065000704c60407030041c0a0301c030105207040d015816101d88002281ca4041a400e0510011402500700302141c65105c0c01c80740303c40011810101085009903200c1d81c0206005086062041c00e59500320484001c21008110101e0550303400306640303030801c0e4120340100d0b00310000b20000707c40d484020142d42e0f00c800040c0611a903 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 12972147 1250 12970897 12970913
    0x6040f030c0822090c02030c031e04030b0411090a020c0d03111b1e030a080c030402010c0b01080604031e05090415050402040b03100801060f03080c0f01020a03090302070e010f0b030a09050604 84
    0x4c4640303150090202000300b65080741c0364002c044144032540c2c41441203864400c4800464100074900301e124604013a52602c44515440c01503505030b411031341c82d001c0034010b4181a4006503015045400951400402049050b0b550503009040010559035800c0c038061300b4425012070b0000780c0304044007003074030482c01c0d4103070344a40e072201d5000341a06003030b603094050740c00c040141d07001c480145d107403000703150f903074180100341644014402c0f0304001c1c2c4000351200164406d485d0038064034604004014a1500b45800b0341703450402e1034200030f03080a19452900455000e01190320b040e40540e008110722440c009200362044241d04102e80c407a0011801140241c3e1050182d03120702c0400510781c1c00030740e0b40c403151800ca4581c3e01036000c0303000707901c1c8040c03000c20704000040443c40010310131100422220ba0103c0e089801405450001079201c0000303d003030650410014010703010b96855408554900340c06070808007001d200d55281d030540440025111a42d075400342500743d030824107503a0300749042e07d41800 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 12973397 1250 12972147 12972149
    0x706020c0a0515040509130203010504030305070807080103080301050f0f0303071b0b040e0f130b040b16020601080304091104080d050301030210031e022b0c0305070206040f030c0822 80
    0x40140452040080d02d4a40034035203041c40803811108910301818401071080100d40104031841c0034525000180050b142480366038852802907400040c5810494402070527114054240300400401d2401070003c20f45107000c490440d501111101c00d614a0607000c11003d12801c44129810700010411400380044440700c0d0504402c140e540180c01740d12611f01e030507507000b540a416800e14281d8001071585666a54081c0c008030b11028890071004031380c0c0d410415000840f0101d42d0521814144031018240c400100141c58850018103415030412900664900651107920b20841e115005603a0f046801011a0b018003008001e40750101c0c2c1510001d841d940c02031000302d00030b001e048085241e041c428880c40304520800c0f1000d2550601009800e8080c1d00400003403000210100c42c1030751030741152521640303208800310300440c2c60f900d10200642103c0c8021f25400c01c0d034101804110000c0c0111403046051f5078036040206000105040600e194090030000c0c02d2495103200041c0172800c5c140380884 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 12974647 1250 12973397 12973399
    0x5010501060206070c0b06010c0201050c01020d0605030606040c170615040605030403021c020d0e030f1905060f040201080106030504080d0203040f02090a2913050c0703020d09060906030e0a050706020c 88
    0x60360f60b102e03420308491031803006002030300c0c00003078130040f8185601c21603240000c0c900502d0804d0030494245c2015089a1007580c0f840703c0103549003401c00003400c060041d01d5110070304407000c00042d10a240007605184d0b104444614010119000541a5460514442d007808020300d060340c0782c64460030094800d40c800d17901500507115001d007410b405010020340994519099020b81f00c407444102c02500c2106500488035450f000c1c3d61103007807a082081082e415540c144402c9805504101d0401c5400c0080c0074111800e50b40342c10b0200005030342c10503450b0b81101c2d4a0319000030241d0315400c1600040c014908900040c500000500c81405030f0490072040755802100c0001098440030383e008110348040c010000c401040d203050052042c00f0f4240d101c103d001c050100500b202d884480c50049034000c484409200314007007175140a0540c1003100411440072400e04408190400101501e80c03030141c41041c040580390b041c4510342d0b040920601c0c41142d03100c1c0851340500e44441d400303510381384240181 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 12975897 1250 12974647 12974653
    0x10c020d0b041b09020301180c0306050613060e0603060307031e02030a030c060c0e130c0e040504031e05030705030a02030a0b0d060507020d0813030e0d0804031a01050409210207050409050105010602 87
    0xc07130760040c80d00c01c4034121080d41d08100922231440c03803400040d1840c484000241983d420b000501611413070010310b076100f082c6105942040c10f0010190200016504840c01801c060081060a03200021920107581c2c1222080d402e07142c101c00f03801c0c0d008480e405c0080d0540500b490b180c04150300b1103d1580c845208150610503900741c28021212008007900b8030f64402d00c01010b00b003403280c05500884caa10b00324540020002003817004102034940640381240000c40c180c2a8100000c0c038000e504203140a42d14000780b86007442e900007015400f010b01140c015650010210f0403000c800e920581a120340901200c6413105c240c1003040c02444210b4120015002d10350071540c155204180b02c5100310700380700280222404a8508480b10503040c281540c0000f107041e41e48010901c514040c10003544503100248402070000f101b01910340e03060f40124000d5003896110300c005409410340b03c4909980661220303c03648848012890541c03184d10840d0050b1914109a007808010342005068403819022 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 12977147 1250 12975897 12975899
    0x70608070f020105061005030612030408100b100f1d0d06051602010908030c072619030b090406110d020a050903010b12121309140a060509090c010c020d0b041b 70
    0x1c280d080c2c8034203d60260744201007003040d2124038002d00c0515085038000d0848500300000a900900c1c40d03210360000d207000e501000c3c10a000c41e8140c02840021803054032019820b64a81310090410040d0303002c900300b480040c00800291056801420707144041c0185000000e07c1c07141081001080261500c514030103504502020481c014042d600071194031a9a040c40d40d80d03044480300250300505002c4811320420300b0152000b1380c2c01e0012030700311110007503500e035103802c0261145940741d1016070b0202414140201c00002d5a640c032602680180c01070700c00b1494403452140e14410f4410841c2890324548003055004890340c0c000e001d414459000d8008102d0404810b08000043c00c00540308a03080d404034050200d8428081c000d040c182703002e100d10240c001c2c3c880003000705440301c01080003400c1d07080303000b04209401c0d14001c1100404099074101c0307242c01c0c0402510340341c1085001c82418001082c0b526811915212014006160086080341442c14140f400b0030106910b140000c218010b4950 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 12978397 1250 12977147 12977177
    0x12060503010e1203040503220608150f0d11030304060c0c05090c09011805030307030302030403021603050d051c1107031d01080601030b030309040f020c0106080309060d02160507060807 81
    0x21a81c80502d203070400511462445500301510303a84010300803902c6000901101c0e0040c281d4454900855407200320807034206081400051100100400160464044c02c00134030503502c5050f113958680130151071400d46900075040640d9007038001c4000503054440041c0c00618141d0004805000c14416405071405588e1217007003005450003510100d00c2500100210881356001e500341e082c0501198451204080d500c0c0002811508907580c141c0110f90004108000c26905006100300010325141005105003991245550f451030707508200e041c020300088440c5045400039443c20030394644503043c000b401c0c004071401001d4101312012408148186400100003096002d00b0040c00e606179517800040c2d40d00d20044025000001040750180000c20807001a500c0750301079050808116030000d603490303601e2011039003181c01650000240350000d108528650356a00e00710382081c071040c800561a0800c420003c0401800c4400082c9144204c0c1c000141c9241c005820611580c4540c07943c2201800c000 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 12979647 1250 12978397 12978401
    0x190f0215041502030402030a050601091d0a03020c040f0e0f0106031727040605030a0501050603060c1611010504080703050c0102010b0105030112120302090d0c0f0501020109051005060609060a1206050301 89
    0x80c400411200d02c03407000c10303042d140650103154000e000404440080415880d254117143d400e0700041c80094507184071200e1010840300009503540d00c50300070210341c103190320020340b0f035074032525114840c54440b610a0540e0309550011041c42031030307109490410028151040c020440e1b48800c403000c540c946070152046c0840015580090304d4596040f41242c002c03100a07400b2800d1820559001d9502c0c40c4c08642a1000c1240c0d4600c0c52140e8000205400c1c00820035142600040140749280000c00009010300155003a0342615a408983c03180d070301c500c0340c0045e1094062900b1442881c42030603400400c1c084005040d032541c50b0280c0017004208070020044803584001d0280d4074146000d520810300003500384481182555842c5401418002c95030000748500400030003d5994546043d01842989880407001c030040109000800c03500d08107035261a01d84041e4180c5042054ce5440020520b031280c00031218034000040440795100414140a0301c40a1300c0308401001a140410120f02c0707003014 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 12980897 1250 12979647 12979651
    0x50724180c140a03121b0f020a080c01020316050f0303040503040e010f0506040501081003061b0305011202031510030f03050a0e03070f05150d0f020405100f0e090903190f0215 77
    0x3a203d0014507055450f0001c441c0844408902082015518207840c50035402e54036411a1150358041060007040c0100700d080000e80d00320300c0240d04042d150b0300303a503030b0000b08980b80300114918106260743c0071704000d810004048000c2502c0e0000204010420401000801c140c501c0407407844035690301c9008040d80f1b07031800e001e003d1b002003003040103210540c011590a60b00440c813940445840c1c6d1070fa503a003000c1e9200304600d50110a62081d805401c00d4040c080d003400f402c0e0f503c0314614100101c1d00044d60307550000f8641e1085140f21404211040b04441161011315000500007610424515005005602140804000500c0ca0002085e81d14001c210002281c60b41085050320340c0c20402000544401494480c403491000c011020740301d22203018603240d04a001c0001621645041c0501c15503a102402c43c1e010006090080d41c055074020a10465100085c0d072410791030f5940381401ca14510919803c800348212800c0042501c907445214800d01078030503826103a8002c1c84171b21242000100f = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 12982147 1250 12980897 12980899
    0x50f100507050301180e07030303020406020d0203030613090c090c0c0317070215060609030a050105010603150e0a051503010e06071202040b030c0304050a0b040305030601081303050724180c14 84
    0x1000100b20b0905c026100d4502805550f00000b114500145070900d4404594030481c00b11b9008641040240d4050104c0325a212090000d18654503080c00010540358214601c172100c50307920440d07641804881c0ca000c502a01044030104850030b42c02c2c002030001010100d00304c0008040c1e071003001c7e0010490090500840340e640062854000480300d4040e4000001d010a8220509100400780c982d403c12100403034a010707100018440d4100b0b000241540e119039154540c1c8c5071018010401e800f0035028881c0e010b03e101c2d000180c82d40b1600c840768131828280107181d50540c00c0070045441da88000c5081c1c0d00944054550801c2c0034440b00c585010781c080c2d84202420890244001984100c030705004580c440c0c4580b0980760704a1043d0343d880700100099406900203030000c82000703e01e503000b00d00290060780c40074528034480b0b9141d9000b8414440d20000600b049401d420b4984074804160340100300141c8171409010390904048010250b40301c400c4140c1c0d922111000c0010755040c2c031321002c2c4110074 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 12983397 1250 12982147 12982157
    0x70b0403060c0f080a050a150b030a0605010f120203041502070b0a1a0d1b080102040f21020f040b0a0302060a170a0e0703170f031303170105010801090b030a080304050f100507 77
    0x95005d98640c0109402406121080e89403c0c46503100c0d000210210007030300b040c401c8103440f401c1c8010050222041500034905100d00214007120060300308110760080d201a03a400b60f5203035254640040039840c1c47c0040d50030700b400481c2d900104441c200b10b0a1196240110420890001e015940030480ca02c441c2c0c0703030b000702d220702031a00850b5619400301543c48030480c3d80c00c1442d40c2d401c070560880c0e0055221480442e8210300030310054103814154000310f1484d079803d003040b410761340001e221107481c245076600c501c0e030b0759403580f01c0c40e107441c0315010003141c0040005d030721140c440d4006402800f00d20b81c5907400c0c820240c00280000020b1003a6118810410f004000190031a6280c00740041190203802c03603c481444040c03078050b0240002c0d4132a44090080485140851401034403080c1c0c1408541c010181d22001844180d0303200c04841d0440344c1e491804070301502c1000219080c40307610700c40504840800400c010174050700040c560f10900702c540c1204e00948100f04100211030301940d1800002c0d07 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 12984647 1250 12983397 12983401
    0xb0102010603111201060e04050d0801060203070503030c0c01150609140103060b030402040203091204120c120b0601050a05070209090c0a0b04030302070e06040612050d02010c1106042003070b0403060c0f08 90
    0x403c00b0340a2404c1c210b40003000189440d25140c0704d0b036802208450403240b9510040142c20031b1030f40401d40c940102032500003181000c1c00d6035105510ba000081025089990200e00301900d400250028503615003081680e0f41c2003519902e004011071641d026042c4820045201803a03554880d100307040031684100401421a11180c0c2008065400075104819900c11035200c9018034460400400003403c544851b26101201480c103600600d1141c0d006d02800f08041000c100400c01d031040640c1e10000910b0010303940c440708001502e0764041d04201a40040c408070800a080c900000c1e0b02010034002c603010220165201e282c081644106c1c040100142c210340301c100140808407400320342140b4003c0c004030300503440e42120712013004508001d0380c0c07a17403203c5c507268000b58080c0704131001c3c111107140c00b16a40b0580303480c9540e902c0c0040c0c401803030040c45031500500d8a81c40e44264000c1d070030060603980e58035550402d04060350054081550810b00d0890a405800c0c060011040100b02e15100c0b96519 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 12985897 1250 12984647 12984649
    0x3060506190e0c21011a0a0507030c020102030c1002180d15090809040e0102030a050603070f03031b0512030403020705030a0c0b03040501090507080114090a0b01270c050405040b010201060311 84
    0xb228082c003032001d060360074404d00f04201c0c1c0c03600050300c1001c1d001e0f0140450f985400118100f11011145002010350200100700c40d240d40300c0200c48005405040c42c05000c40309100403441c601c2210204041c0b4003030b1003003040c035050f200c4c1c00418889004c00003a0002040340810055500b80ca90001004100d55050318208244103402a030200390294280360f0400007600081380540c0c08840240040e07075400000c00c000804036104064000c00c00b540284005401e02c20300142c036210707502028086c003803041c1c0880f0358480040c02042829510006a071045107800507071440e00d40054034200c01600a006c000328580c240062050403130381d001103000803524139003100760480d40c0c40500155100e5403110b5800f40418020040d943c01001034070000550801c5010040b40745c20390280c900091508140c181201040b002200d40b81560024200c110900c003c8180c00c20302e000f80c004c400341c84182000d03c2c490a02e500000a0070880303e0950303080c0000f00c5880012400ca5443d800005c101070106507414280b = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 12987147 1250 12985897 12985919
    0xc06090a0e0711030a03060312090e0604090615080706020d0302071e020303090a0803130509010812090102032b06080309010801031b03060906020304020319150b0414040302070306050619 82
    0xd4107824080c0003a0041c80f000d50a640c131030307103280380400d4560004004110218030000085001840d09501e001e00b8100c100012001c00b510441c0b241c1d03100c1030303820280b103050307444902d413044091403051281e943d603404a621030070a0b04c01c01015016160014084034003d0085400c49640149103046001d50015140070042e10b400c0701340c1e050310050241c1d524540750443d444002d0700e5200001c5440382c1000f50206514401c40d04002e004080c43c400400040d17400088031064121403810040d19a40700d040100e285018800568040d41c51450007002e00c8810781c5001c03008103020003800e109054451340440d80e2441a030007000d000030944030040000c03443c44000000c80c802e00b04105004c1c940d403519401f060300d0114200f40d50f2140d0000610045140c10040c00c0c916880483c1d085040c46d04a4890341c0103c24a4081200e1007501c640c50060b05903225842000802d4640540303140d80d09203410001c0d41c91f074983c081280d440e440c2c40041340d100d20f0607000c1004040300000b0110203241c101981400 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 12988397 1250 12987147 12987151
    0x6090506010212090120011e0507020d0e06181e09060a03050d110102190504050a0e04021008060418031e18030303020d020c07060f030c0c020609060304050705061b0c06090a0e 77
    0x1440104100f406c052a14082c0141012105130400d8455801000e610703040071280b01a0464043d51701481e00040c200c0d400078401c080184d0122500d580f035040764101c5402a40008098075840f502d941d038400e680c80041c82000511560940310150559078034014080304210500002d4084c0c2c0c0704c51423206601d0310460441120487c200300141c1050040300101500c0f4800c0761940001c19800f103018491810301c2040300d002000080d409a0f09420a50007040242c60441c4400080200301c4c000920b5940b0390b83c101500c514404070310040600101c0c20010080070420001c040f0749019080300700141480303250441711110945001601062441d0f406600950051305111013a0307800f448030160103441880000004c15507500c804500350061320307004044820b003949003814000340210030000b589031802500c0398cd500940c2c00b42d56a0300c0e981041450035900758031231644054009804454100d401400d040c5030540c00c012250744100080c04c06c40e070760250341d2142e23411260340ca4041003200d00d0700007219 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 12989647 1250 12988397 12988427
    0x20d0918020a020c03100e0c0a061b060615120b03010b0105030601030b0307050405010e010302030607030e03040302010c05031e0d1401030209040209060d0c0605120604051302010809010b1201060905060102120901 93
    0xa81c10a8001c4007203814102001c94606c3c0e10f030380c1c4820380003004100380140c044070030003181d0300004581003a2014200407504820b036540300d8040301d003500c104100381d40074802030030a0a408091407100020b0050820650544100c1014140140d6200904050140401c5000161101800c50b690000110010304800b841a80c0c1031007010000285511039208041c080e2540f5603071a2410b6065005043c500300c1c01510a404041c9460070740401e502d40807041c2c1e415640e0910b03000c09401071500300035155000d0000380120301035684007010303107000024000302298001e8a005005403c0c003060700c3d100c3c845003440007a400440200000d401483c002e503c95a000310010500c02c04c6401540720f00c07840344210313000071012030000903150300c2041c801c4095a40c0301000715418061480c007224031402c012030481c030081c1841404004030340052420b411041e01504068400311803011008402c501a203c44e202b41519145442d0204200394030105080c208031040d445c1007823400300031b000110345201c5d03510560 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 12990897 1250 12989647 12989653
    0x1061d0f190e090a140313180608030a03050610020d02061305010204030b07050306031005130615080a050102090405010503030301050105040b090a090e0307030f0f0f080a1b0206010303020d0918020a02 88
    0x41402d8010282c56800341d41c1450061104d80810300e0b040e0b03921480d283e888410760b4018050000044a030b880c488003a07a9559040100c1c00384400008400b030052500a5202400041010085c0b00d030305a1020b80b180760f04594181e82502c50800598440c0c0d5800040340c0140c100c000001c1e51a20740000c0c01d186d1303d10403800103282540c0d035200c84e1181c0304241d03440710014400000340f1459190402412001000140042040d410802c8003003400b06aa0f240c001e0015840e854840d0210103c680303010014001c20098860108092410314001c3d4410300c45a44100e00e004000700b11420000190f034140c40c1c040c0c507040d1605050171341c41400d0350002501c003540000000c0010450072810b02841c0821981c003c01941c45102030b103400340243c107000d40341c6401c2101e000085d0f1500c0b90700c8602d41458990340d0800c0e100e00d441e40d0202d80042c00001000561100620310f0031207916900054550489001760701f41d07010003650450880e10380a03644209500d50413100700c41e180d039162960052000c60514011 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 12992147 1250 12990897 12990899
    0x90a03060204030b0411041104030b06010e041a041d03040b0c010207020402070c030618020310020c01090507060f020706020d02070306050604140c03060a140603040308070c080706020301061d0f19 86
    0x10301016607000b9041290340072048024401008440c41815909940031141407042c01d201c00c1c01100c0c0c5005130301c00a400030450a021a00d903034000ca141d110040009841804410303400c4011503540b000b0310603001d007c0c0d490a62032203190240c0082901507290300801941c545403601c0c0d0090f00580107500400c0c0341d55800c0041d0302c0141d99500c02400800c1c42041c110030300310b2550410310110f4032242c22116030365003074802c2c0d000140e401050700030101c0c040100060701d8140d80d0300003034010054528010304030300c03030418046800d980107200000b0505240d82120b14458442004030380350800b0381159809130703012050910004809030003c59200c0c1010f0130003c1c50090745101e130b9040c29010b5130000c62071a0004180401030070000c52440180030009000425608a2804248144801003014082284a4002c41e02091040b00c10125a46d041040701d40c40c0d00150030400002e5100b803080034041501d00e0000300b002074005018090001e00100b4a151251141050103426818028150039500320500 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 12993397 1250 12992147 12992153
    0x3060f100e0916060201050402090402040f0e0109140601060f05040603020f0c061321050306040c051204120f0804020310050901150305030409060509011203030f140106020a0203060609150402090a03 87
    0x81040d100c1c41182d001083c038000c40504002c0344024603040700d0110790502c001c01c40235890b01c083c01a0004e40c161400584600d00202e598000c2503124040c0c00a5400e080e807120a002080e800e10700c0b040050002c0e180540d80c0c0b00c0090b5100071001c8000408100248804c0061074020340c0035019103c18102554902400500141d003481070443e041c54140210081280511601c6c881001100c64400342100285150510140840c0070007014188550744500100c500f42c0e1046055545c25120141490481e04107442e245d5002611090007000241c0d002844074040c920035903109000e07503000b5001e0205012450800809014000c004103500c0d900c8880c00c0303c8134441c0f50040401180180013441c0c442e42081f50b650203803a07450380864810940d07100140304000031520880580756242c1000100c1e024840ba80c2005000c494203d150140c8801000040054000c10845a0f41d0710850a81c3c1144d42c4040c1001048882511001020702403100e810340b140c10680c0c01005010f40050070303038031259600c0e9 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 12994647 1250 12993397 12993419
    0x110901091208040f0b0d0507180b0702030106030501050711010c0305040b0c1803030427091101051c021305040c0305070509010c080d020304210302040806070e040e06010e1f0503060f10 81
    0x107440601c445c2c40018040484401510566030018403628141c1c0040c92070506549a5502c140640c42e5104030000d007041c11581d00f540080c0017164054024491860f01041c003800e0241c140b21046e10f15424450308180076882441403902c2203070f0054a410702512a1001c200054000d01c0c140254009003164410440d541000030340001d01c800796120019804540c00e84c10800c0300d044070382000c02e05002860700003991a0740c944a0b201000c3c64003075116041020f8241041115540c1d080644d48000ba03129070100d0600c8544007528400e4905010040c44900110100c400071180000001c2040c0801c401c00d40c801d04010100ba070003146c006042617191100101240c0c000e5604960881d08011071140c40d00640e1403081c90b41d030003401c2c2107060034942081305446000041070582007010842c800e00b05a950307588101d5100e45040304a9410390b860701ca1401c51010142c44200784200505203e0034080520805181034450180180006803548139942c601c1071005840d03040c54400400c40818255090 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 12995897 1250 12994647 12994649
    0xe03011503080c01140c0910120204060c0330050601090e0c03010e09120301090203060406090207030c02031204050303070204020a110f01050103030806010c0b06010c03050c03070f06110901091208040f 88
    0x506002e0b82d690405920150031103080143c03100d421014501002400b01100c01a9039130a0015200201e00700800041168402141c10000c02200d20100d0040741403540320001d0140c07103119131110710100c8846850480c1c0b01145c1514402001d800700030003001c0d100d90345c024642202c41030400345070381a1948500c040c0d05200b19181c1d54105808401001010510411140c02034180030282c20b0030002c0d20600380c640d03c414040c5441742900000450307415110743d40500300038401d8000031915588540341c0140a100b409400341c1c443c0c030958a0321607425104804076422a40024021490010f09600b44800b94004040400a010502c181e4100314101444001d00c0100d43d000005583e40c103621300640a000040d100c01e04101100e0340b5a00018035840e90720740c0002090030a10800030891a04039100d211703e0f80641524040410a00c0030011951740c003820062140c8014040400b01c01c030f111000e40219101e95000500415040001e40d074001d50091005d400f81d401c0c0e071716080d1100000a98030540d = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 12997147 1250 12995897 12995903
    0x2030d0c031406010806100c02030705100309060f05060307060c06020706020304051c020303070504230604080c150c06040b0c040504050106080405010507030501050f12070905010b03060a080a050601060e03011503 93
    0x11605642c120440e103004255114000342003491003414050082a99012001000c40034450700102d554103650302000410700801d40144806501c58090400402404d54850b007140c2c0340b803d14014141e50b0260b4000c685c8207900141c002c04400e483c02c8822035554409650076140d0a40c00c01210011568070300007144100d000300000c0c078280182402c0c030071035083d45001c0281190014018020340a52100c120b80484050100400f8000c010007806182420040390035070740070f80000344c006822040410801040807080380d03688d08544508054045512444604110542115001400003206402010741142100104d98200354443d07001c02c040b65000c0c2c000001042001d410041084024000d0580c403d100307140030300040d45400081850340010400451080c00114003103d507002c4200000c3c0d00600c0140c209010035603552034040c08503441602c115011b02c00141c3c0100d108240052000340300e07076200005128903860650100e031080983c1191543c59500c0b00f041035101c0c2c4250302501c02440c0 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 12998397 1250 12997147 12997151
    0x703060503070b090105040b03070215190e06100303050a02210d0b010507021e01170a092901050907030b0306090c040b03070302030312040606030209010b0703140301050d030f02030d0c03 82
    0x82040c080614081d8039600000c401c041c100800c50599912400780d030200c0c1c0ba03a9204a449480b040426814003903078903240102c0d080040c0401001c100080d083c20898203480c0c10070803840700304e100d4054a910381120344007844405c0139000c20019101c4d0300107111707050b46407041d0b40b660341e43c0404407410643c4204041e10245408035450010099510922038052401d09240b45040c60680c00314405000d00403541c00f449aa200c0500f102d64051040c103400d14a401300da00c00546041e061441c000d20000c21309950030004121010007034050800e460600024080062059078641410081c484100400803010107440c1c4011800b261020807220b03010b21915805001c0b54207010003880304491543c40040e1090740040c03030820258501108a03903c855000b6458865030780d803401c1420145c41940d00080d0004103020000982000c05070141c81d18610a40d51808e10030328101c200036207030000f0300031140c2c8420965803032030000340107510320412032060380140d904061098441c0c0c4111840c0130303669404030b9 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 12999647 1250 12998397 12998399
    0x80d020a061b0c02010c0615030503030a050606090603010e090c0d0506090f0102040b0403060213030b04051c0302040501081315060f03020a0b04030b06060c0703050307080a020c010314060d060605040203070306 92
    0x20a0302d01601d1007a00d92480c0c5a4060540e0b414010405580418080d050002c00c0c80c000080c064681c01c00481c0c00b050030344240600d641c0f8a0090303640d0384221030340c0703034640d00c0c00e030115840b89024002c0300c4283c200104160700396420581095849107000d8800c400500c100d01400760103031560050281c06a00171009013886240032840d41f41400003034011111681d10400060041a000c4829074081e80d40142e00180c9480d52940203d00100d0580c1000d001c103003031141040100030001a105c0b59001d642c10480045800000c019802e0b8007a6000e0280801e4031400099151070740b081042400d603008010041d144580030a401c03080382e2403030700314440780718660700b09000303509005120b08001c00310794240d10315103440e58a0f004072202016000300d05c00d00340082d0071400c5403403c000b200060b6810400b0341e43d94040ba89411111a8001c0240d03801502800280f400158003d2044040e403440c0000c0042042d91084200f09024072101000c0b90070369602d05010680ba29540f010b5407207001c083c1c41c000ba0907 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 13000897 1250 12999647 12999653
    0x50a0c0302090708060901180e010e061006050309030d090f15060503070617070f090801020a0201020a0806030c0102060705090a031a060a0b0f040302010507020103020405190320011e0306080d020a 86
    0xa00004000c0410b201100c014482c171620b4055400b030440c0c15581200415200c2d802d60303440a0150712803820819801c203140407040d0b000110324940268400300328504103a5582d1780580d00b0b03000071242c92040707810034000b08190703032042d03007240d0990307481402550300100c040d030396020003010300d003820807605d1366609018081814104841d001404207814000c003110262603070318405c014018615003c100402041507800c50107481c021001d06030000c0207644400450030001d000b034001c0b20081c40064024408211070f8180403915000c0340c48181e000d80007595a45500303807480d0340300103e045e822503c0c1c44070001c01b00709094a061840480b96019115030b040c00404c2180341c03d017a82001224034000c101c0d41142c071400000326421280e082c2003141d01e80860b400140d0090142d80e01180d044445561000c12000040d101d00c3d003500c5c450b142e03206221045403805104c80c2440c1c9591404200d0340411030001011070a00a03250401c0d0746008184039484d02895401c5c03101c031810107809a8803800d6030b1810 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 13002147 1250 13000897 13000909
    0x5060403020705040b0603040204090804050d060b150a120908130e010509071106010312030917070203010c030606091a09150309010f09020f010c140601060905090609070e12030403050a0c0302 84
    0x3d1034225020300210031204000f4010344000341c00280315aa580c8840e4082241c0038003500c0c010400240070480d40d030458107040740a00040d80340a40300d41454261902c004e2540070544560100a0303039405e1484112011200003005401e02c2940c41490603c40410401c0224103071201900c0c5807c0d101c0341a500d40818443c1801000c0c04680501070009805000c88000294190440b07130080c120004941b80030506400401e403143d80a00108070403a001100c07215410000e0480a100360020000705d03800003811412074400e8080d2100188801c0410022114440c00c0021f110503000308862403c075040c000105003c011b002072901221002c030400151030303c01c3c464040c0706c080d1040c0c14050146a540041c2000100e410354505020300082e9190a00c000c101520000c407009038200d507000d58603510054901b098620400744904000000110b250030800b03201401070038580c6400003148180e074100030700400310b03401145652006205c0000400c00c2007041c0890350303004031003614025045d8014010 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 13003397 1250 13002147 13002149
    0x3050706030603110f031906150608061815010e040f0507090302011209020d0308070201022208010606170610180b0306040f0b0906040203090c06030c0a1b05030a0f09030f050604030207 81
    0x305c41d4042014002c440d84000c41d000003904041d05c1e52245100141c0340c6030000344881c9148140e4a941d160000c20100e070003080642c000c4008848811000d20110490019200b040700d801051141a11820701117502800303c40940d21002400882c000100c40010381c05c8070802c030380100c0060303402d10741003055507006840a1030304040001d0910000d4030310340104040d0a2a104020200922140000c104034801c6d416254146d00302ca0303604e42941800c2c1003028610309a4003640025519007603001a000b03000740e00a030301c6448184002070b00f80d6505810000e200710400c6400040c09020445000050112400c1c5000f40180902240e142c1c00c01d10140001c5030a508000e0545034500103507c0c9156450b084401d5200100312809a541d0361000c11003403c207014000d40b59003082d0701209102540c0341c2400500594070a5544072060746850402c80d080480e4908000b5040350420410b00310840c0c8520010b032520071403400c0206501d541c9550b10b510360b4101c00400c1e46d05401c0b090500c420190705220002c = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 13004647 1250 13003397 13003399
    0x150702030414010516020603040b01030209061c020607020402070503030711011b0203120903041502010203040620040b03071803031211031b0313021c0b0601050a0906080703060305070603060311 85
    0x5040505200c07007070410390071082e10141032003408100112000d0712845007030182940a4585034490401e85402c1c0f070400000c0c00124440c820200000e54141051042c5a402e069520040c5c814a056038080c4143e07980001c9040c0c2c0c016808000e211f010440800c010b40c00780d952031b654000c8403880208a02d00310768581140c0c0ca401c0210320355200e14290b000050315109880e0548000244e101d0a40031440d503c0303294800d02145e401e50365040442ca8066020314492401110107000703a044070741b11003e10300000c0c9141d1006040900042c010004180302030f6034010a00c1c01c040c9140d5060b982042001521680100d0001d5003c61300c2844d1081c05d4042d40205005040c611400c5041c5012201d0145028601c040010000400018050100c50128108907600a07051410981e515043e403169141c1c1d05805444000d0000040389855105030100c5543c980ca903503a40d88441d042440440d50382d800901840105900c0e10382c0800410030a000010051000c0d0728001041491480d2040c8040c2d0303c89612 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 13005897 1250 13004647 13004653
    0x2210105010309112e030209090108010902031203040c0504090c090f11040504090501020d060e06090c0403020d0308040201030914010203090f06040804090207020a0e0103060204090608060405070501030c0c14150702 94
    0x44002035401c90b134107064107504840c5c1c664203084513034000181d1001c0310001032003001402d00706812181c069006041000055404000e6a0303203c481c074900342c41e0342039030003900740d400854891555076000e4043e54100e03103d40300090300c0e0355a40300040c0076079181400648814040f0002007241d0220381c8940d503e640c000720424420a851044144860300491141500680d03d41a40104105003941100d00041b0258000c1281e50b80316020a1500f01e0b088500301c6c040c0e644240403078680160701c41a1030449034014480010b6002e25036040300c185102600482c149a00d50102000085140a0094107182413800058891400b420b0031403818424489680d5950003400901001c180210104c5040d1005840051b0f40c0d614075102090701c00c8038a500c01d8814400110012041141c0b0303400401c1101c0c400c4006002c0703540c45442c142c1c0c80d6842a20010300c1503010643c204204e500a4200c00e09481e0385003040c9047d0140c40e00c40020300c510302c40d17030b40381240c0040f120b1400003803440c080c29030001c40c1c1e8801 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 13007147 1250 13005897 13005911
    0x50117010e0a02100908061003030f0809070303050904020c0303070c1b08060105040c14070c050a09021204020f01050c0111030108010e03030f01030605060f0a0b070510051506090301020904022101050103 89
    0x200751500c0000102a004c0d42070440102e12060145004000400301c0104440c8249030401da404010301640c0001c60014000c8400b20850a2149403181d0081c41c01101600f1000d2460340c06440660040000640103034080c000f00c00f000105001035403096020340c4500c26890424504116210303a10321120102c010011814056410005501c1d81522019100019040c2c1020000c5e5000406c1d0100080f100800054038400c004800032480c04464042c2c52446802d42c542c0800c800780d0043c10404510080054001400744c68212104020408103050003460086541483c500f911003200c280c1d00d8240000004214400b003d00c58000800c805c1400385d400e604010742c600c40c9071070040c48007030505074440004c070b0203070794030114014109480180350000050340c61601d20300c1074003d07000a495900800a0006007403486001d08c0344141460f90034414013032a06c100708000c80e04070080381501903500748031410700b5455a00c0202084524078034840e4150700105420081000c05800085c100740c18902c03 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 13008397 1250 13007147 13007171
    0x1203090b0705060604060b041a071109011205060108070e04030e010903062910080402120c0306070809060f070e040f0204090905060f0714090904020d020d06020a031104080304120f080403050105011701 88
    0x71010149046042c41b5032b51301c0147d400d00c004103005500c0490b61080c0284000140700d80468480003580744208240c89150f80c2e1110403985985841c850b4694801d0a8000140028400d03040c5400595050400b180500d032a41c07a52021035401200344000b15000c07051b43d40d401c05600303404aa00c10b008031000f011f02403003520b000744001005030009014500320b0b40c003400c20550600000022410240c100c80a030b103441c24008105010036260002e940c050440442d00b5800b030b1034034080c81030f15151107550032842c10000f40304c000d00b403000c0d01000c00c95082c040170550f80c00d207002c0c06213040d0181004001500300150b4440144002402070401c0c000d0b001400d8154030644820346004201c12528115036a841d80089034482d440810000c0d4084101c2c61040f04008240d40501720702e00d0b075541c3c00c2019001143c4480710707500c030300c2c025844568010300c4108040040d01c440501114810142d181040129170b542c0c0c00b40750045c2d00101c405944450051001c0328103040e00b90200f00c800c00081c050822244 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 13009647 1250 13008397 13008419
    0x6050903010f020c0c0d020a090203160305060d05071802041205010b0102060601020a0f081315021b0114030109020903010b03070303020f01230f040501110705010b0a060203040b03011203090b0705060604060b04 92
    0x2940c5c0d409000040e5040c020356440c226134000a00040340151341e42d140100c2c0b01c0001f21440d030a1303900402e15000220303440c0e0070300300c0140c40841e603c007004003845800d100154100200000c480e400c555000c01c00400da1080c1000d850358918822030002c10380d903040100190418100078070080c1194020564100441e0200b42034045480d005807006d0360320351609026000d100310310342240d05010490455403540036400910042e20040c58006110b03100361100045803000f03800c07051501c1444042c03005200300b5540d640109803051004000041c00903885010a003000c45651040d03001d6003180e00d031f0401400003800780c040c5100c210a640000841d1000c3c034010400b03000f920204a84e05094006001c0100c2540f024a003100b20a00d8140c0b01c100500d04240138000d40585103004411000d00081d00794000003c0d14250303200d071350403142181e003000060903401c55050420350401c118890300041d001010402400c1590041c40070303000c82d143c80c8040c4016141d50b580455100001080704111a80742e1b9 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 13010897 1250 13009647 13009663
    0x102060109020d060308070f02040b060c0a020f0d050717012a0f0e04240b0c2808031006022a0628030603020907032703050d050106050903010f020c 65
    0x81d5800588903101c2c3c14100c00208402c0d00010010040040d40e0410311106000000c01c20f4030807601440300b54240740500c101e90081100c00500c42c1e100034407150041c03074610305c0b501c82808060655890b8040c2629240e1030200c01d640264115107041540b2080810300780605035181d8900e00b01c4c219880900a811002c50381481c455800b0411285803210381244281d08180d150b5000910611410140c04084e07140c0e83e04c13012444000c0840504c0010351440d40c281a01c109034031103c050321001041c4111005400300050000403000e00b407001801c0002c1c00d00000d980102c5020110031203580c04c184020f03207040c1481c0c486a41c01800c40d82403020070100c107121a040c00300251500d070385038180c3c1440c1c80d2146481041d0f5820b49806440e400a001e5030541c401800ca900840c0c1c00748040d00c0341c02040c1d0850305403c135076103203022004540222030207c4010143c8118030915040749016030000c0000110b5800782c00ca00005100000c000d03520b460240900c85200300072070700c00c5180540d5184e9841d6180342e0 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 13012147 1250 13010897 13010909
    0x60106170c030c1201091506031103010b0a0c06090b010509070203030402031c02031c050402010f0504030b01051509030d030507140a050904090302010e0f0703032006040308060301061a070b0109050601020601 91
    0x18a01c1c1d09100c142c03040c44070241e0207004c0c1342d6101d2080902070148100d0425120142e083c0000d44203200703000b604050300c02210610315503420802d83d000d85038481200340040c080d640e21100002091441141b41c12405191903080650401080240d280750217400001154014014000565400301d81d0300300b0000da400840c04424a072800a03411401220562002030f001c100c02c0210b406200c0d080903219038800daa8040a1005004080c0c031140a50700000c0c0443c641c65006020f18201880e00c002d2041c076168015041030010000203241024400340800001e49840078420900d4000b280d1420b100499401e840c14040c070983d0003410742c040d100302d50b40704989a19400341854000c1d03205901448004003554008090500e10660310140b80c4030440000c1c1c0c00405480e26184042c09855409030000068512034866450440da0210040d042c0d80e032555071345000007072a00303040300300c0b4000c0c0b00a40c84240e2174030018240b8000c0020140d20220300310f4106010025181c0c0e0100e5440e0650381c0c = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 13013397 1250 13012147 13012171
    0x30a0c02010908070303050705010b010309080f091503011d06010f020c0f0d050303040c0806010519060e01030e01020406020106051e0a050d050a0c060816090305070501110c0301050f070206010617 86
    0x8a00040b07408903450750120850340940c24000c418964000c3c0103003140c4e4007810007407044a86250044045454807603001c1cbc4242000d00104400805180013014454401032a00b503460317089821001e0180d00130707800140490a0428080030701c00780080e0580d4006000d09100d0704020300c0c050041c0d1034050b1003032002d22907120b1080c4040035980da5420030300515080740440c2e8a80c42c00d0700e0001d9012501e400780c0c0e0854130404000040ca49013005044d59a02d4100042c40850380c5403c3d0280d030405030540c0c010341030544030510109820800d03c041c0c0010075080d4000305d00c481c504000c1c0045040c4825024095001c950660401d645070301c4a10012240192039040440b801d60400703e05001c020000144140c0c5c0d43c03e000182e143e440030b1110b0080da06104440e042640440342520040720512001705260010f1004114540c052124502c1d40c0c2d00d0f10058800d4115510006400c50750b084606103e06840740c020302c441264104852805805141031140a0404030106000c16480c01004000048 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 13014647 1250 13013397 13013417
    0x30c2e0201090501020c01140906070207091107051b0f04021603051b0109230d020c1504090204030b010906120302070506071401050702060702060a0b0105030105040e1603080702150c030a 82
    0x252003503010700310b1240c00c10000c648a05a00643c1c60191031072840e1081c01d5850403003c1215007e0100b0300a015a4258005000071442d00d26210007504840748450004141030200c032011403001d00010354203004100352070340d0083d104810014000c444064850141d48107001c0c54030f10503020b015418401c2d0b0581450303a218241c1d945040d2201f541000030090a5080c94123a00400480f641d01c64071507900d03181101407650350310165aa680030800d640c0c0005a03c255000301d901e041c14009848481812101070b494140c640428000340c0c0e2041d0b0045030001e21910040000300640d1103848094907004011011241c642e440c000e50700d0f611405030600c64200080c0c4c0200f0030000060b8a5440c541e044001d011902c0d10b42d901170f4941c1401c540c0c10016024410001c1e1604501c0c0c8130b0340000c80c405868140c2164244000c0c8001011065410020361040c0411550500603d0b5140c100840c0315000003640c80c02c0500c140075504107035a0300016140b10070300880040741c1d004002c5d15010081c500c2c041c0b01075 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 13015897 1250 13014647 13014739
    0x5010906060207030b2a0315040207020d02041a0d050705030c04060506030708100905010303021011030603150603030d0e0d030e010b010504120c0312020a050712050604241505030c 79
    0x544146c004550b01520078480b07000c0c00070701c02000d140720303034410500025404044010312090784074841009510401d00520140103240c0750f0302281200c1201d0458505648480b00440c6800702c92003c241c1c1e4a40c001a0b04002514080010198650054030706119051078403001c92520302000e4011410301c05800005071390446243c014000030540d04209001e1560341c0d003070103511900314800041116043c80800700c0079440c1a01207a004070700240061070b0090303060669074495840034003c10b0b8507010800c91362035881d102d40545000c40400fa40645461120340f04080c080b0385e0110104a0341d039043c00c11810850b1f8000003610202e07105489105c80010143c60000d00c800c01a40008128903602e12560401c01c3e070000e00e201204c0c1c1320310b00703c682950301e500400160b0442d20200400c82d074041000280000c50070b90030001500c1c100310662081607607010120382600c5006800030a2400035410030003180c9410800034141000544003801482940f54880c00c3d5851820318001003407040d1000c0c07804c1 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 13017147 1250 13015897 13015921
    0xf06080901020f070602030618010f060c050c030a05010c1803080d0902030109020a0603021b0c06090103150312020c091e160e03060a02030402040b0109060e0409030c0b09010c0305010906060207030b 87
    0xf486054003059950050381c6440c400a4006403450390180051021440715501c407215006d06a40c0700d1011007030303001d15000049440c898000b00454040c000c5100c2208251000c1102049203807091001103203841751104001d0120900e500d20400307943c500300081010a0540f8200c03194a10200404580c0140500100740901700195000b9000300486500081c89a4582d000c5c05c01c207000301050340c0b02011350002e440c0e07035020300e4214140d00c01000c0201c02c4885d8020791003444200d618040701918280d59803668046150304100d80344c0541c00003c044030703181c0380c00c406c81076004080c2c683c1d807004d00714204512158100028001c3c1844041990040c3c140c90281c0800804108003c0449000b440c0c081c0100c406500240c1d800c81c010b60410b040c038060366000c1c0180d00d0913100c139562003900a21b1241d003000068400c3d50020340070300921b19041d0010400001c00c00d8400c0d5085000861000c03050705d0300400300c0350141d000c080c00d41d240140c117101c0b1980c04603081084a030442100c030305036140e005007030803 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 13018397 1250 13017147 13017157
    0x2010318050a030908070f0b04090b010908030c070602060c030f070e030111040609140f0603040b0a0908180102070603060503071208040803040807030b0105030a0308010b1809090a0203070b040f0608090102 90
    0x41079202e0085004100b580c00ba00183c280d59182d82955040d03592418000da545800d8080c8000d01c40041c00240010034141d844140d0a076414504042c0060f03603014503d00310761102c003488105401c081018400641c0400045401c540803469081c55071a00000f03205224074090311450800c211500b0369003241c2e80c25044044401c8898458641c0d5551b1140e019000f240d95110384010040d00364140d40c0740d882c00d514482601500070300f41d54078540e00c50b03031a0b40185500a0448901c940c0c0c404100b0040303400c040103031071100c2202045030110f22500b000a468565107600400070142442018480d079100843e00504803821556003150303c000034506000c00f80550341000390b8510012a0000c2c401e04d0004e240412039003e002100456601d450505489000a0502802165020004003c4e0703142c684002d040e00c080c080d081040d15a0244c002501400054851a18680c400c000759000d5240520540f4010503007124802e01e000e16010341c40b1908101c0e4890305041c81881000900c10500a4040755 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 13019647 1250 13018397 13018403
    0x40e06030109060218130203010b040e10080607081512071206060806040c03020a08030c0d050705010906090305040515030105130c0c08030c0a09060503070903020f0604030c08030a0305060306040b010302010318 92
    0x142d02c6020a0414480b00c882c000c080034403c46c1c040d000307036221403054800c0328142c801142d407083c40c107420030a038031020707030300240050340c10135080d450000720b00e00207002d214010388c0103075109070060526441c1c0c80c40c1e68260b84443d612540d81c04400d070307445e501c00140724421102c3c0000028440003190a01ca030082003194048031150040104220030003e240320350702c0c140d0740308903071000f0038584604034680c1e60302035103074100200e034001c0304c1b800703421401070001e040401d128400108801a00340d03216016144216822404107070086003c0c413880c940f100c0c040c421200c88502990031903140c00001039031560055907401c100c9582d0140c0089440c417659141451a4202000640d207041c044890121076202d4074080000814456020554500c00c000305e071302030a0740e660f6082500b400c640030442c0d00f15a070a40658821810407000001500101c216802850380340c001e0b40d121035080c403000e0305403400100345600c02e030800010000000c0d03070240110705480e02842c00281c02c02c408041c3d80c84030f2840c06005 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 13020897 1250 13019647 13019651
    0x803090904020121020304050d0216030c0303080a020c0d020106030201030608030a0512090a120e041805030307080c1c09020306010603090206030a0506031009080a0905030607020307080f040b16050105010e010506040e0603010906 100
    0x90060000d030427500351074182d084807100612a20004881525400000e01d01805100c0420100c0e109a001d20781262503600014505000106024981440b260919005d80d4407400100150340c1c05104d120010294040514942001d26000034840e1080003c02c44240b80c081000c10a91030341000300d01031280d400465a4581403542d03101510159036005244d2160341080f408261100303640401c925a150304c00000c5085031188501910300410041c10712100510a0003400034000e103a0000d81000c0c0d610b80350000e42d4100328010301d82003c9058003c94245410306031008016103440c01261ba005c2e001220014803522000006400e1080058043c0102c905021804041c0500c40d0001c2c100104d454950340e6059540d1814180c076044101d4440001d41c00c144250700109644100138901501d131240983d1170280c440144050642020b04100e0150290848040410109215040c0075004910798401d496140000003099446a80150080c404042d0040b40103a14250400c040d00c580c00801 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 13022147 1250 13020897 13020901
    0x50d1e050702070f08070302090402010c020321070204060e090a17040305010507030b09090f0d0507050c0307030516080109020f04020a050d1b020d0e060909040c0b1305090108030909040201210203 86
    0x100a40d80c043c43c0c003814285508806000881d16000a80001280c1e80500510555a40d0b81c0054482081c60340050f44c250180440140103944080c8100740c0404040120079203074071403401071000321808d41d040300d0b500c0c0c5489004d10218400005a441e02143d20450391351904d451a0200c1880303010700e0380024069802e14051000203505900700c210252000c1d1480b04180e038420a096581d403146246903022500280d20180e07480e845803004095946c01001162036136444140400d00c1c7c62010350050754503800c040940e100d29983d00c0c4a201c01801101e009001c011126000a404220b0220030144120360000b41e03082068040c409550b031031000c0440401641482c172a8141500b10b0403c0814014012040b00c440c840d401602a8484501d004d403615003031060b807a040c044070b820060007c2d02c0c3d9000d10400000d5100801c0001c0143c808440800c9229a1414050061b2080c060304a41d41c02e03002405240203584070810700c958010380900e419515060700d08001c0f8001402a60000c02440c00001 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 13023397 1250 13022147 13022161
    0x6030c0c03030f01032f0108090118060203060111071a070c081902011806080105040f0e0d020f010605010801061205070909020a080f0604021c0903020c06030109090b090d050d1e05 79
    0x1149504072030049144000900200c1d21110740462462000184850291400011b5500c615141a8015200800010100d58241004441c1110b9004c220388442d000001c101d100d5900910920241c81484020608942072400390b10700c803007030985019802e07100030540b0802d02030641c4681d00141400d506680c8a02c01034480000f152201c0c5006030302141d00e12106162910365030000300c0c11103003035954801040c1d00300000c00000d031089801c0b5940240d207030802030587c510140000d052101c00340e001046489034030540c55003520300340d60000c4d050000300c000411901e90002c0540c0007240d104100042c10781c0c2e03410016102030089401c00c001107403001c40c20000756904000311034080c0d107006105030642d9407050104401e1348a104901c10400a00f03908003481c074005600000e48841c802d0050310039812800b00450307400c1e082644100b8105443d80a00c07000e104c1519040c6405c000c02c04040c281d000c0444001400b10300c1900900c0d00c0a66407450354000700b070045411501040e0f1024803d001e5810488 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 13024647 1250 13023397 13023421
    0x10b0a03120f0504080706030e030c071e091109010807021f0207050601090e0a02060f2104020108060301050708060d0809040213080609010c0f030b011209060c1205060a0506030c0c0303 81
    0x40c800000314010500700803506000b1004d443c100c8070011300a1032190309000c8114050596000c2e14a014030007441154201d14040c400f1001402c03c207208080c2418410002e8015a0344581c820461649423107000700380400d0f61000c032440000f00382484801622224070407450614081400d41c4214203183d251120062250000d18410780581d049409513620760307a20408440741d0302100b0310280d0125098000500340f45000c1c10702080d08407103090518100c01e14980d041c403c04401c445e01d000c0018200421076801601281d002107054008010500c0c00d03600181c0710032400f900e6240300702088480f00c0c080040d8101110910035020b482952a1003007842d441340003498a01a0007110b0080d40001800b46505101c2d054500340e01355242c880700d03209088190001c2c062a1500ca0411a284039242c800c8000c500802800c10701c02c4038001425400510010969075070000c504016a05240511040d03545555114081d148212009a40d0342c560070b0065240f441490784a01107030002204100c0800c000c0 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 13025897 1250 13024647 13024673
    0xc0a050303062e030903050408030a050a0311210901020f0c03030601091a031501030b100f1206050d1104020702120c010f171902040906090902120a0c03060e010b0a03 73
    0x603601c01400d140b03900082043e100f900d0040000d1010301800d03a8141e0740c480d401c9074510318040c2c00c106141c04d03261202142568000b0007442c0c045040000c0c0000401e074548901110320260b504050b003480c04d041c1c8101c442d43c400b010380a5001d44110080f610711602941152901d40c841045280e0704c0e452108010348039001122094040303580d005c4000f5507901c202800600b802800c1985901c1d40c1d44040d05468802d20404850b41010f545021100ca1501c0b04400310b16000d00030f880d45501788100c2d10300105a03072550202d444011381040070030806600c566109042050780300d828455a80240400b15009009610029600840009410241d503401050441034a130007030343c9014084808110644980d200783c080c105c00c544401d0300146100202c100e2032440ca0442150141c903141c2d031109518180e070b0882e0019440140c0c0c6000340021481c190701040540040314010b00300c2124991249212486240310150009460f5012032242d0394080d4400c02421800409196416490703051000d060340034 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 13027147 1250 13025897 13025899
    0x11070b0d1b030606050a080a090f0807150e19050114010f090c020606060415020a02040204180509010b0a0506070609050706050702040b030105060307120804152309030a02040902060c0a05030306 85
    0x10525a089140b0b2080c0680d43c143c40c41602e9103071500c454081c007155081c1e00104818009552948110009022903a0311080301d80280101600d40c0b4140c10440700440c1c01d004100b42062501c6022a9142c03c003042e59038400208520004803c0000d051950240130350030f640b100c0c142c10300c50011803107009120040301030b1102518104a8040580000c1e603039500203960580d4482024001084003403070014202200e0f039868415150340901550104050744c026401240c0014000c0c7c1252841e404a842100d901c409110000d05c0702900003008100010712a0160602480c00000c3c01c0f001d024140c1c000690407035110044036000765844034018890340100300704a00c15410b00c9446486842d05004950060302c0c02806084010314047c01301c5511012481c0440c3e0380c0c0c00610000404c1d001c1c11040140768a43c580700c40a0f000d4410001030448044000600100b207801d0000754003948000445214481c0d055070300181c440c40900024040d802070340d8010505106500003142005004009913008286c = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 13028397 1250 13027147 13027181
    0xb0703020706080103020607080901030e06090d0e01020c0d300207060305010e0417030a09060e06040c0f030302030a030b0d020306151c0203060402060906040302100513141011070b0d 80
    0x9150031080f910100c0a100103036205506001c1040460300e038600400094105050021b88038200f1052142801c108940218054008400340e260440d08001d1031500c140b000d10140c141c298040d0300140b2229407450025040c1011092039855807030302c480307402117003100200300b455000c0785520009588013402d000c1c0200282c2400000224105840744d4640266445103c0e401240444200e43c0441e800082c8034228864845503c80040f8083c0e126401401c001703140034000600e0b140c101881d40a500381c7c0300208040d4924020030219a001c402d840c0c0301c440714035000c1154030100c00040c142140f000e1020354103009100510190354201d840f0007030b10f00410348815a000251030b240035a000220380f8082c1d00758100c80002401483c140009105003880108154140348d2690080360340d40024550013000305130001800c4a0a60000c00c2601c0182a4251740c800ca0f0342cac450010070000d001d0209a0000e0016909020b0006181481440090103514604c1030f00c030f81a200d000800b40c0700588081901103 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 13029647 1250 13028397 13028399
    0xa06030503070f170a12050c0d0e01060e0106050a0f030c0207050a0e090607020d090504050a1b050301031109130803040c0806090a0c0b040b030f0c09090a1a040515040e010605030303010b07030207 86
    0x800203c06917884071038030f500c07840c035502044403480d000340a0081c081220ba640c1040341015900f240d1280041101c0c2c1c110001500c0e604000b400c4d1142c902c103800c01400c1c440c092080c0c6142d0ba500020541d041c4c1d540349004202000c1030101070f0718000064015035800040004003084102d0310484151148da1401c0031506a0303240c0b80420398561640c06800d0001070700a180602550409411041c0c1150040c100051000b0320a0025400d002003086800300051000004009020f6403803403500c5106400c8440390480d09006415903640b010041008007288800300004040c010010070705401040a04191038041c030b00452115150010090211075030b81d5102c40200c4c600305985c0944040e1108050f203103145480e00440c460943c00700070a60400b02c1420400b920440d214558010300841d10083d012481e10900204441010b0b41c41100b0303409546000c0400070464840b500c440d9010380203480016151188a02d8680502504d4100507094440080000307510200c00000b40f01503130013035095800c0d503 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 13030897 1250 13029647 13029683
    0x3030c020105162a050708030c10060e0a05130f03020f07060c05190c030507030c060809031201060806030c040e030a08010e071d01030e060a09060b0301020705060a050a06030503070f 80
    0x5090f15020300c1e40013402c98284081890802805400300369009000c45403400c101e81d6505180050719045018243c01c04680728082e0300040100c668111880c0c241440100e081440c0c2c1d00410400401858400d0745581c0821030280c404119203c00e2500012081cac072070026401c000c0d580354a4080389041502c940000003c500744603442c80044654850081c05110307447c00340c4400d03200c0e292042a510942c104400100240d010003400c00294031900e4240519464584041c04c003680040030b042a58000f0810039094030303181c41c545810346901d0b04141145844810200307260403e18425103401501d004100300078400000b016026405240c0c0d10040c8585e04c034103100711022403d407010700200c1c02c0e403400d0664989110402da84111018500024204003000455244c6070040c0d0b40f62400a90b0703107050f281801000c0c0600006914281e000750f10b081711540d6200c3c3c1e0342c00b0003040c40c601c86990710b0118a0784861500040300a541141c11291940d041e400d181825080c0d4250440700e10003c881c9601c21 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 13032147 1250 13030897 13030921
    0x605030c0d0519170304030905030129190b070804030204180201140309010f021c0b03010501050a05060309010605030307051006050a180905100609061d01210c0506030403030c020105 80
    0x7407180d0240203481d030001e000600a0b03090407007000c200d41d0561003040081c03078000c0c2c01e0091032081d4080c0c0d5800c01c05a04c3c25083c1401c4512038940c120803850801070000f124100305a221901140946441e010051107160310828601250001d00c1d00207000150b0b00709219410000e0301c2580e008640800c028450360100120070940321400070302083c464240c41d41c1d0048804051035000180c44000300d01442c4070350229080781d0044086051080041f8410101815135100e0b040d81440240d000700002d504000c00107040c85c0c01c2c0e201e890b104140000c00513000a41c2900007a00508014080301e440f800705250054075150081410b0f654140380150000701890429503501c1101e1100b0119a050800b04102d180546660b010a640c1da118214095a0341d40040c0703d040700410f200d840c0010058109413602d4030b0394403007400080201d640c1400602191440f9880403203541c0b558101c9110910f500e142481c00c40d02aa40220303404117010080005154064000500d0000194020483d680c0d03602c6103046 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 13033397 1250 13032147 13032169
    0xa09020408070b03070203130e22032703020607050717010b0d02130b030706180b0f0409090510090f0605070309050a0201050310050a0b040905060102120a0c0201051c0605030c 77
    0x1c01e079400040104509181c100c021340d0800802d2041d00d25100c02c1840881c5800341c0ca50001c1480d11000080100c4400c1c4038801046948031046112101c07001a00e000300034102c02d0140381035074815200c4081e02d132200f2205680c02994003510260b21080e00b428400e13120312240c450711001003c204448040b0540c1842214108a0003c1c000c0004ac1255000c5c000854805103c5180c107658642084025503802c103c1c40000700303c0d0b40d8550183e0300061302d0304c1544031a681d01440c1d00f0350050214001d100ca458064405540001000081903205802e2842c038110242c3c403554141440d01c0200700c00d001c2244a0b6401941c0030341c1c02803165071a200821011103100240241441e0004100300c0300661143d0001c44e00300001da04a00c0145031107600013a00e0b800103a002c0342e449000001e0400c42c2010303038081d441d0310183c2400038151199a10113004020b02c80c01082c8810031982e00030f140c0c216801b4500799030b48107519800d0105284d032200c44140042015024951080c460010303405018a44001d01c0c071 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 13034647 1250 13033397 13033409
    0x102120f070c0914010602010b03030408060103120c120903050d140d05090708010612060b040501030b011a0f030a0c08090105070516060b101205070503010e010b090a180603020a090204 81
    0x40c0c034110561401011540050108441c26801c00d2400100600a40950f0403440d124800102040d4903102010b401c440344224120300980042c40b0070000d518000c41e0300790440c0d412030344200708510a85000c492841d61a107009100a04c40d0040f503034425441130440081e40e2050b0101c0310040c030b42000a03102c11890541e400901c07042044206d22a40403608000d4204805100311703201e994540c952982034a14a401142581510a40050500036030340610311850009490410042d41191141c2005100c1405000a06420004480303a6004075a00304d51121659400d040e889082004821000c2d101020300d080002e4802004503a9010040c402d00e4011409501c440e843c004000c210103500c0b80c211007040d90800d07070341c0c3d2031142a915045ca02d02001803059484900d4424054580030031540c0c00303080503080040078001480a84034540125064030841c60a15440f80001d038006107124109401c03154078888028507a40107451150860415a8070171079040f090580c44460a004078000c1d44a00 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 13035897 1250 13034647 13034683
    0x6021204060e0103090507060e0f06070201090b0a02070305060f0a0e120a0309030e0a0e040b010806061305090c03070303020f01060e13060207050a0f0b070f0519030b030313080303090c0102 83
    0x108280740c010440c45400d0324041c1030214200700039848681c1042000c1d4400404550581d40003001403400880305c1314141412a8042d040c503c6a800080000c203043c0202d1013403207400141031180b83d000b0000d010085a0010803542e00d45056503600705801d2055910086081c00c00c2603a0b0407544000c109011900b4680604900f0007505810440141080401c181c00307000020402e600140c48400d44180a00351010580e80c9a0030f2600c1d011240300c005901c00715494000b0b105000c4680d484c209d07010184040f90301c0c0814941c070307540345e00303424401c07410151641840782c810000101900841d515206494417802040040d590700300c030760a00e51003181d59140b900c04105891000030082e501500c2a14001e400320f45003540680c2c4c40400c5450f462030b040d01d0f00c1040d102000005035020b820001c40702d5081ca4541d0410b4901100b40111071b406a0408080c540c803180f80c4c2c40140c90070800d5407240c000c104e00541d14650345018542d221703403003035401803414001c012000f6829400040d114007038650000070 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 13037147 1250 13035897 13035899
    0xc020a0201080f060103090b01090603030207050d03020606130e010207050a020906010f12050903090307080307060501050d0809040c0e0612010f05030705060703030f0603060c0809163006050403110706021204 91
    0x440f081e0380c08001c1c1020705050f80c5861000101b000707800c90340c0c0604100c032000540c0905608000c0d1400d101d0381d00640c81403500b031700c3e1400001e901044040d00320340191240e034201903a0100c490050020030869089035880131500c0018018002030a0b507031140291145a102d88400004440b0158141c61450100c2c07440c032005c0310503000540c000703907002203024103890034100c450001904043c02c0b980503900590000c102c840a1002d04c0c0b24082c0189421100c01da0b10500ca0b64550f4a2401482e083d01d1160360ba50307010b51426130182c1c2040c01c8440c8001c002954654103203140c0104621b00380115401c9201c100b00c045042d00b400a00b50040d694001c01160414400790380880c003a0401312882110300c1e80351103000000503207030b000d0565500c590b500c0b880010710340035903a14038140d10a0300031492003512100800c81e030011100f90070919a030b000300110241c03041140d04941d00180b010002c0c2824034140801003030550113102d00b800000c80f0380079a4a06a5154030403660382040c451032940415003080 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 13038397 1250 13037147 13037161
    0xd08160f080903130b07050d0302030f0103110a090507030603060608150c0d060e0103060e0c03060408040501050901030209060d020301030b13110103050403020c03150106030609060e130c08070312030c020a020108 93
    0x50740d26030103002c1c142100d00e44000045960440c001c95444050020804100a400c0202c00d002071004600503140450962800f01c0c41020450818030000c1c0c6994080043c040b00c1c3d4841090b8800030f40f00c07241c020302890400301c030001c0c020089403005848180c9007507c0418035804c00714680d0488040d508074003003c0e89074851090200d40c088000d5001260f074680000807030084030301d00d05000314001e610029801d2102140035090058811115100c0c1c1c0120040000041d40314040e134056420078078101e41c58507410700c0180d000b407141c540f440354410004178650f0100c407401d400450613a4499040003a05403039004243ca0005000351004016450350340d40002194401d41c80554018002c1c07044034994608240400d00b0488030041145810f43c141c0e005200168044c021240184801402003001a00d00103002c10f01c0180948422240300d1071300c82041c01e1200768620500540203d00c16545090342d41e00c0e200070b02480060401011908000181300100d0011840184054042c3c50b9500159a621 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 13039647 1250 13038397 13038407
    0x501030f11120f0109140f1507020309030a06060914040f0b04150c030510050102030c070b0315030d08150607050a02010e150705060906090d050d02030c0f0c0d08160f 73
    0x400c2240c0c2000d401420b1040b505020003841c2d11405a40000048014403801c0011a0001103c02030340107501282c081d0780c8075a400600740c0890081408210321507101c0010481c01c622400100c25418880d000c114003d201c00b03079100704100c1304960420071802000c0d22107041c103158100c5014003400590209000403800314010b00340e00501c1200d01e0302e2807c081424110482e04450320f2003001950341c508001c02c1c080f6000320407010704030900007141014200c1c641c956440707982d4005c607100a0b0002c404611b2185202040d00701c0000020152a03840301814001000d02d481100c00280c1e8105078031000c840d605245084035170300f9411001404c02c0d9015074005648042006c1ca1454001c4640100110000300003400303000941d05c82c2c40680841e090080401d1b1030100b01621040e05030304490459114141c004085076903086420340c004da1642d440e4400da6641d4082d442040311018400100707501c1e043d00c007190400d01c040054441c0345464580c1049804281040c1c504400416142108019254054 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 13040897 1250 13039647 13039673
    0x40806150114090d06020703051305040e19020f0a06020307150603080f0711220b030303090d080403050d060f050103050a0903050306040b0f12010203040302060f0f01030f0201020109170903010f0501030f 89
    0x913107950f1407441c45076200d9040b603020600c1500000c0000c0b4484003441c140624600c01003a085500388021105004d9040c1c07559441d40304819542e007002d10035021034039002d90344884a48000c104100c1e403070303680d18080c0d141d42c400305045801c840f00079051450345070148074010949400c401d040341403080c00481042e542d48120703415200d100344142d04140c17642d110042d074407040c103000ba5000d007100c07103180050080c0c80e0700180c03040c0300e0381050040000320400000d00d50b4000c6506e01c2d02008542b140d08060703c1c00e1043c480c40c104400e04000010548607000e0099504a0f0002c0e81c0c00c11042d560082603401712a0310107001800240104045005407505030000f6083c8003005111004440c00c2d40e00243d09004500d049c4074440c0d4012040006043c6c040c002ea550000d0070703c548203041e203030610002c8160803050100410005d24205c0e1507066901c00d6010034030550b44808104208030710401c1a0001c1d8101c0001c0511940c200302010900307080c01d0007828101c0b60b00070048030041e0785580d603c0c110040c035 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 13042147 1250 13040897 13040899
    0x2071a16030e0a06030209120a0818060c0105040501021209030702102a0506070201051b0306060d1107050c030d030908030c03040503070c0b120a02160b04020102010f060b04080615011409 82
    0x40e10b542c034210b960701c1c08080b0000740155100141e4510045052202d225050300513130240c4c1c2c01c003e4800340030a9803201201c442610252003c07c12014420001c3d800340594480708075650729140070001007100550080c400f1400000c42e02c0c1c81561168a69540c07803169410003900460705030f12241059004052582030804000301e6a00d808911400e41c0340706c41541c0c2c5c0103541550003075060207840c0da02841103907089410f0407032681400c85a40c0c9030041364403003e8003250107000d0000c0c940382a00d8443c0e01001103015081019942c8801c0e50510311b581e070600440e02031007401030030000e040f0036000c0d205425038140d00101c0c440c103564481851007002e4200500503101c2c2d000800020001a4504601a014003640e00466864000100000b01c00020003015921038600c10002d006069641001c60308200f54400c1101405542d5440100e02400401030600c25050509101160140100c40644255035002c4c0890313510390b41e5030040301880c40301c031040c880c081081c840000080400c000028010420 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 13043397 1250 13042147 13042157
    0x4050f04050a061d040c0605041d130606080a02010f0509031b120a03020708010513110609130c0f0206060a0501090b03040303060f060302030115080105030723030604030c0302071a1603 81
    0x2a4402134000e00c060075290154944800c04108820000340342d0b210f502402d11890041e05141c24040c0c4400f10701a0b84001d200c412180030009007050382089124901950b00040a1084a686440f01c503034440c220031040340820010722000282500c90340c15075482da01c5c018001c0c100006410300030b040c03003600c4102c03d0b0740040c01e1042881003160100286604144a82e008001240c5001c100c103007140c0001e4200041e0107600c02088011606014145092660865096903134040c40300000701a0324035024520700050801c5a2000e500d038000301c1d4074240c2a84c54090b41e43d140d5a000401c2400b4411340a02408104200801d0003210703910409075170f00611900340001e8090700c82000d00c0005a03a64840d2000940020042c02952001241c9400700702c1c260030b0070505541011700194582e02c02e0702849003205100d00c90b004034084441c11038440703410054180c8100d810981002402c1903001041070300548280007001403103084a0902c1c0d216400103403035682c01c148014400400d1400b00e0f403819800c001c = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 13044647 1250 13043397 13043399
    0x150b030111030405150106090b03070f0e030d0f030c09030f170c0304080c10030509100c051201030506010509090303090307080a05040e0910050114030304140d0507092004050f04050a06 81
    0x703400d00015030280b40a04000c025048110710344104045058000c003003003000841c020000a0148015650003d40c5400c2c00c1890300c003844000c0700da030440121456450311880440d000700a42000e0340390f010b0f0001c0d0b50107004301d581c8410165074045040c4001804103500381d4103500810700210442814005000d102460302c64000b07542403540d085504140f0f5140c00c10f0100c1e0055240070f00040140c11114201840240380001105442c0c110305000c60300255252840c40701510300c50001c50300740b11801c04112104d941c407030900c182c0c1e5100034090217009644080c0031035034000000080e039100e00d0015004514004580e6034854441c1c211034621014414281310210301c0203501c8021500c22111030000f0720b070701681001c5220593310103a200300d108190b0000030100c81c0c2c502000f200c095424403d51001241e5440c000701d001d1908205003e8a01d0080c4000403c841619400c04500211050800400b020544070f420040c1c0c4260b20816a0145d03513680c55810505081c1c1285174048101c1c50001546 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 13045897 1250 13044647 13044671
    0x12090503090a0905010501030f0515040b060f0c030d0608030c0a0609020d0204050906060112022106030a12050a0906020705060418090602030a090c0e06010507140f0d030b040c0c150b0301 82
    0x40036000f00042c103071940010b0007a96458881d01e007500d41100000d1103e810030982c0340c094402402d00c01d0740600c0c2c5070000d0f0940358807450111040070382e600b504103660744070f50388046849401001d90152031b1414a100014030a00000a840030100880702410341d2071415981c480040c07000e003000f00d070081c440c040600c015a03030b1403184a201d400d042c8041c0c000780ca40480014280b525a8146400d09841800346c1000c0625040704010030400ba080d20440c6500c0e8100024a82900b45400400100039075810a0309280d0020207045007502039102c408800e500c417902a070f1170f510107009140c0c21007814003003081004401442100c0c1d0b10018600002d5000c5191100c40c1a0b078001c8405a06503034480d110781c0200904c441c44a0020803010200403040c0c2411400241113209102000e0012200801803c504203c10300000c0c5a030745051044030038410280101901074501010010302c501d1a00035070000309801400c50451041d40021141041c40344180340d040104440441c15405641c0c0f44401840 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 13047147 1250 13045897 13045909
    0xf080a03020726030f030a0c18090c02010902030102030403020c0901090608060601050f12070504050a051207030605220c06030507050a0e01050f04030f0c05040b030708030a030203060111030a030f05060f011209050309 95
    0x540600d045c035160b880c80d26140603400d031140795103070104010b03d11208030741c000e950001c0c0e0390544100e0030703000c10703040c4e11140f00728090701c5907020180d8513520000510040503000940300401c410155988030840e0b0341c490401044524900c148100c036000380c030015445620940017411907408052549040c460044040000c002080303517440046100094203020916007030201e00010402242c0e40c142951101c450f107900c5011a00c8002d00c40c80d1160003150682c00000c1e01e0005040c182130a44000725034500384000500224490b000100745000d001c0703485140302d00d0440b51164490b8880700f050004541c01102c030b9a00612072004040340c1400040002410790380700780c0c0c6250140203c0e52005040904201c2291052000a44664041c010410400102000f03585440342c860a0040c2c61f580d80c04c0060300c0d81541c119021025000008000c406181c041c0e004800c0e209112504009c0ba585040c00d000c2d0000220300d81d24081261200580400030b5180c01103104280300700181c0307041c0413005000c60302e = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 13048397 1250 13047147 13047157
    0xa1b080304200a0b0708030601050c030f0a080a050402010804030806031006060302090307060c0b041106040b070506160206100504020d0f0203040c0e09190204020a14130f080a0302072603 82
    0x129581402280411900685800d1070380c01e0044442844440c1381c140d1400d0103200750b100042c4040b501000092941c0c1c090341c296007d82d4a200181c80cae545c038105c0b20300c100300e9000141c9100420041030110300d001c4024441d1a1081ea0f040c1c640d04071544039601c0c10b650701c03036006100c690302d807140303e000f600505000e000392401440036450168a42200904260605032503412080400960081010106528848091704150080c0c243c0b0303000b00e04038003c1100343c811604050510403000424030200840080c01ca132007911601e20803410540d50b000120780781c08081d03a41818071440e1900c00d02251606174010310216000c0200002c45100880d07512060340c104503810b480e00d00320041d04000451100d441d45a210300d45002a2800c04001a03244040ba404d00354007900981d40460030229160160300130709401d89064454641b14001c030b065100c1e11708000d00030411000f41d000c100040b501e4001800d800000d0303140d0090440e01d0309003940d54070010342403c90f4125180203100004940081480104 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 13049647 1250 13048397 13048403
    0x20d02150c0a0308010e040b1b09030102070803070318080f0a0c050a0305090307150504121401060b0912010203010312081e0106020307030305010b070507030308090a0605090102040303080105150a1b080304 90
    0xc020b129400d02901542d01640800b10112009042100281800ea40c05902a10400e850000480501c6260b0a64026112100d40540c8000782030400d2103014005944110400e81e401e0207404108501c58118401c10b11000b0700b006818404003145030502c0b800b0b0607010301b692030607540c6140207864541c501210b109040d808503400107403c99030750500b84102c4d4082d040c2010480d810f00150700009140748180e2041c80f070040d02c1c545082d400c000380300041d60304c1c0f02c0c2424000e00c41ca0b40c880c0350721041c0b68018465284184d1520300040e54182060095074105c0750030129074400300c60480d006443c0300d04028203240328000e8210080c1d07103102c3d070500303018084c104039402107440f0a0980703405800c8a0701030f00160a0114207004e000c000600c00506101600d9040c41d00c22100d80720440340d20702d00203074000002c0001d0306000400c0000001507014100f240d0080d561600d050743e8072000e1010b0f450344450503400110040026a0b40300b0302501d82e2081440900c0d1a04410b10416202c10505400070740c1e00f1 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 13050897 1250 13049647 13049653
    0x40203040f06110a080103030e12010c020601080c040c0e1207030f0303021908090c190f0b1206090708011715040302010902031c09060e060906160302061f03020d02150c 74
    0xd0240030b01c5124110b090040c82100d54038000c41c222002d041c0b014144402401c100000d40100081d41756118031b07181e030104e80e4000380600b42c801c000c0a512407000340503461940c410f88240203241c0c83d05018004480611341c032010040b6007032905101c1240504141034409201e002d00020014503905206480e19000c0e5a0040c2c6a0300a11413000020308803866000800040c0014000d1010000c180140d402000721041c40ba41c9041c5280c090381d450142d07001035094403140c94000368002034280205010058148441419a580410032010807030507242c1c0000a01501d00600c0302d040d01042d40505403005a0840380c802c065400c0000a0001c08c44003100140d45400c1d02008500302004040e030324444016040070384000d1200001d184058074800e003000c00002103401e1002d91200000c0b0380401c14050000d40d03030346941c040032000c0c980c00003c0440040c41044001441c0c0041c42c0036404000e81d00040c4460030510359003c01c25030b10085041607900551222040445810042c010480c040011000d = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 13052147 1250 13050897 13050923
    0x603230c0301030b06030105040206030a09060906060f08150903090d0602090303030403030608010c0206010b0a121401060305070f02010b0102150a141006030c02060c0405090702030d02030108030417010e060a05130204020304 98
    0xc100d104c50030140038540280e0410707090100603605c4409495002c0a00c06001032242401d04208010340800b420180481d881d210001c40d00559811441007510084021a050759008510780304440c20220ba07100c0036a0028008c9603100e15040c034100c905680134000c058200054400040d0444d4000d0b6411000f10ba81d4a0040112540a001c0d8060302507050010702503a6140260000d518446ca074400420450f5a41d2080c0c042032080e0f000074443c0740d081d400d01c4015a181c2d8800340c010b0800792540004074441c49000c4c48200c0c41401032008038101a8090f12043c4034040c80c501c0010b20140c0040e4489480b281450910081ea4030303e0b07413040d0f50b10845001190b20b00721001e0115807450b40300104541203441000300c07100d04a411101100e02c1501c0c010302c650340392001213003140035408188031703068000400003440313490003c0070300160744854408602c11110f0701c01035822244039544036000c41d00020005117650580d80d100b9580400c42e0400b101b1f1480380769000400700e81c822101141c5201c04809 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 13053397 1250 13052147 13052153
    0x807060f06150201021804020904060807180e0601031707080903010c03090215040605040314010902030f03040e010b0703021b0102030c010e030403060b010c050604080c01020910021506190603230c030103 89
    0x41440c0400b06000840c5080d115010b40070405001240701c0c0d003c3d0381c00154101e01c0f6100c2b03500c500c00504402c403e98075540d490306528110100b40d040408501c07410000800b040c01ca0101c0d409040326400301c4000134001414055081941192105446a0600f40211a41502e0038060900245800d6a0000e0003011901c1040148400c1c60100c000d180c0c0c042c0414414079070000304031401d0b43d03040701c9031060017420070b44c009000d8100036400139014001e400d0f901301d03030340f00000180c02990500035054110381c1e04d03443c4071000c0340502000500181c1c480d41c403415202040d01d44c5000061410b1054a00e89954216503509417203c44540c8443c0d9400042c04205000742c611412080301c100b403a200b080800785444141d5a0040074002814042d80001c424400d58030950403030301c0c41d400140641d8501c112a1a029448070442115400280d003030b100051700620f04807101200c26034002c0301043d001418071030114010049250300d5003c1050139050240ea034100c6008191146494460f02507507581985 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 13054647 1250 13053397 13053419
    0x4121b18050703050106050715020d11040f05030105070f03090609170c06060402040b04150c0f080703020f151303090b0304050c100315060507031b050c0102010e031905070807060f06 80
    0x6115508044c030f88001804030a610104446000341c020754402e241003400789904c402031003520004041c0c0f51034400351505117110318000d401280e40c21481300a005542d0701c00c1c1400c0e55030031900b140028002c04180c1c00c0541c003a078027852199005150004200e00c0950300d4000200d60a280d4001c0f8003c0860007004c035040c00c004141e44150141d0741036080502e000e003449694000c2d40580e001541041d000500b4852060740c0c3c42d2209a005203185090095900b03090290323511006040d00140249000f40c40340032000607401401d00308481c0a00ca1075501d182088600400059040302004005200021100900e902440c041c60103040580041414202081100240c844031103080c5410b1041d01d001d40c000030f0b0814803c44001e421b10075070320440b81c0740c1121b00281120b9006800c41700380c24403000380030000421490400d000c3e002000090701001140382d4070b024030115083c0043c8030b0800014118401c0018050701446401e01d642491074a644240540c0c4240e0410b0080c1035544104100310390440c = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 13055897 1250 13054647 13054651
    0x9020c0d090305060402010f020f030307050909090a020f0f030309120c040c090303080708060406030602070b090712020303090d050c0603010801090302070b1c05040c09020705070f140604121b1805 86
    0x107080008496145559290b140d40000700040e043c80b401142c0148824002d0100329082c101c49400e03a6900d107010540a0b000f50007060040d4010b0b42c0720000129050b90000d609109983c0091080c040e264071071041180b000360761070b80d154240c003050145000c0c079103078140ba00341000c894801403c1c15a0780c400034001143c0300c0f0811182040443e9104001103600a00d101d80c000a087c989940c550f907400c1d0218025141c154401172400344006140001d00407807400d400c0c022605141507402c020342ea2800c00e45149840032010b989074000300040d500c02d03d800f1160705001840f41040c3c400d4a81c3d2000000d070543c07c00d0b400500b180e510386007600201941032102c103026100420240e810103042c11351005215000d06411481540c3d03c0c00450f041c090b240040b0002006074001c1950345a0307107890819252032140c8a115502c40d1a10000700d08042c100c02d4070011410003500c00c2e070605151207440701011864420a40f003d02d0b002d02e40b0040420031042c1c003000b0302070b201c0b407200c01c03500c0c4215002c00f12940 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 13057147 1250 13055897 13055923
    0xb090f01050601170601090302090403110f010209010f03090c0b0705030c01061d070804110603011409151f030603080f090f010201290a15030516030c14030406090c09020c 75
    0x50074040249036a00b103101c800111121300c800d010700355108401a030f1155199003020717622111010403c020036074882440050100078409440800404103890350030b07805907144050200f21400c1400c020144a503101c810518012050564555a1104405410750103c4802e5030395800009201031002d609001b02c030010b286030b80301c0b91464908520700c443c116002400107401c11030000081824041a400484910f020040405581b0b5a6461101101100c40050180a5901ca4000509038118050602c9071382001070700c1c00d81d03034080001c090028121140001010305583d0303500400071030b224030054200c4403400740c0031b03079600d8029004204004000c0010709046a0600c1b0300b680581a440c0c4084281c09440404d0809580380000050151092030300070036040200c26280c1307021a5850340095000b40b8024100d041c030310750b021102700c0a40d08035880420116081d01c0d81c0080580c000700c02150f10500030080041d551060382d80b40780b60021103030b20458401e0713008140c0390000401441004400300d1 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 13058397 1250 13057147 13057151
    0x18030809190e130609061406120624030f0109110901120f030e22061a0309150604060902160c08030c0a020603070201090c030f0c06030b060316020c0d0b090f01 70
    0x450400c8103481c03aa0014041c01400540351802c904110160700300c1c210040d1b0004092200c1141c000c11a18072040450300d140c0700301c500100d400414440460014000d40545c008110784240b0a6824401c1204442c4203540500c2a01e90236030b107840b801c0c0f00306000340c0e100b54001085e421100c01040311090f0103810001c01d84451a2183c0c000400104d2290b14280d81828030f036032482d91043c0003072001c541070500014090384a4010070001030740780c0d000c0c006603400c080c08551090300c00004195203000484041c02d5681c031421880aa581142000381e500c500018004100d0903143c203140d1007640c000703d1411429000480c17081b001c00007000c10b01d40140c240140213500300b40728001d015036101010540a400f40d2000004941003d100b9048100301580142e0f51001851f0741c1d05d80b00400111210f01035403030034942840801d40c5482406050754213180148010304586954018001d02626590b5480a611681e409000d02d5140c4507080312003d4098080c80c0404e1410300707000d0341003c210820040380ca034 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 13059647 1250 13058397 13058399
    0x20c03060702151b07110301020f120402041b02031206150703020115060f0203180406090c050c0c010f0c030f09090e070807090203090303040803041a01030f021906080a0207031803080919 82
    0x36444000c5d641c1032600014078004000200b401310f8020300c964103d070030341c03000005035000711807001c0c00c503660180744240c82c1005981086807100c070101a800c50310740300580040050001c41c2c411032070f4080c0c101a0081254640094409001c08a540226005c50150f510382003902400021200190700500e03090400c41125101080000c3d283e00c00d211042680c80c0118080880d0341e00c5681c02440030300410f9000300034500c50f03260701401c9031308000324508203407182c0600c2440b05d510902c00b1210303140c03180e03d91513601030460b9029158136510300f281c1401c100030504002910380c21805540b0b030015400e0003400f810b03410024800c0c01c181c02c1c1d40001c1000c90040040c45100080041283ea20507003080520341c50391518a48441584420000c3d501d91491080c0048144a1030840820250b442100c600746615042c030b1412124404510489012030742640000d108001d03a40c0040c07040038484d14000d8428902107200890520058000b0b940c036104c0440c440c07005042100040d21903041d09685c0070481 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 13060897 1250 13059647 13059691
    0x40c03120f05030a020d0905070f0821030f0601120c03060501090b07080901050c070e040302060601090509060a06030c0c050f030c060906010b16020a0914040c06030207030509060703020c0306070215 87
    0x9103c090050001c4650003c2c181d003110b069503100350282680201640d018030381d614840c443c0f100d000c0c0124040d6000301d00c206080a00c115880e0310b080c900100c06182503686041603040035042c010400f44c1408040811140d44070360700d21516180c0d04154030300190b030a0401e00010720302c40c0345803c004800c1c0010002d0038041001002615481802440c200755514401d510840c2402201e90181c08422142c4083c40308064001c9085803003401c0aa81e0080c06035078074400c01502000680b0070baa000b8155902c140901032103604803c58136404c1b0700b4406500446942c502e850198002c00340341c0160404111580d06610601050b5001000c4100411655040210000c1030340f00d0180c0d10710003903d9091225046403030320821b8400401c40000700700b2507010b010700c10400d0104201c80c01c030307010395401402090890082c400c2d503142d030350542daa2505000c10402408141d81c0101c40c16011352050940c05140c03690108000c0d881052140d002d440c06107403003402d1420300080070b88414000b440f0400d0000c1c1c0c03 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 13062147 1250 13060897 13060907
    0x402031e06010c021f09050d06020301061e050a030f1104061214040203061906030b010e0613111c02040e01120b060114030a150512010b031504170309010605030105040c03120f 77
    0x24040322006401c0282031508281c8101c50113907c4581c003d642003d0580a2220f182e0265049599640b40c04031040640f00c814140c2d035018440c541c0c003140c41800030f021001c0c403a5118141810b0f0558001404540080c03d03402c254109602400001c0c500c42d4071040c505105015040a5480341c2d01c40014a04090b40000d0b190b50b0000c08550020a181c00f48013909030040d000301c002035800c10030086855840c1c10710b07104c02d400100c50540c01601c1101c2d6101420342244250241c41c1d10304889603040680720420522920360641149050540902c80405d0414240c90039900901840d070b90108003041501d003254003850b0084c1550705010140303405500c00100e00c0110307035003e034422000180c41c000713608040030038102c584c0100d90002e80c506056140720105500c1400840c90440c00c0340c600d62210024800003000403100107044c948150701442c003d0115101640e01f1046980010400e59151000b003400c4840440d001d80b03030890014400c106010321084d4004402c802d902d00207031820200180501 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 13063397 1250 13062147 13062169
    0x316030803070c0516090905060907030309061409090703090c0902040e01060e0301140c040810110403060c02070902030708060a060302072001020a08071b0b18011b020402031e06010c02 81
    0x8107021040d86031000300201030001c0c5c0e85d840751a580302420b05459400c404010840c11038119000d10036440030401c104800a2a401240d6042d5640820780e03041c00401c031000c0c001d441c001c0107400400e02a019540c1d4031202c1591143d07280d560005810f80c213600b04144404403c0c1d20501d0b43c24030401060248078035414a20b4191504c0341056540d10050307101090040c44212001150320103440103004c2d946844500900440303000c3d000312080b40400b01c0d10300d03085411034030304441902004c000c04c100007500c940020341174001d80d006503a141503446484101b641d008803404000103501c002046985d02d4544124000782105141c210300704410b035618400d41c65102152400b03c000045080030b8541e10030800f44489076401201e868442025140007881c01b81d10140102c0400700c04500450b03019140015211000801d2801e51500710141c0d00558000b604196114208124408004090707142e42c0000c1d4040c03440306080032400d40200c00030381d6440703002a00d001d040006034540368003d60b5880c3c06140d = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 13064647 1250 13063397 13063411
    0x50403050d0804031e0e13060609031502070803070903020102010f09080d150f090212060d02030a0303050c09120a03090510090302060c0102160c03050f030412031101060b180316030803 81
    0x1001d42c0b0740d0b04060361060141080c41004903c0e514105c80d016602081c1c550403480251600b00c42d0403111030b120003e484060154a0014105c40b50801c04a1840d00a41c01401e441c90001498084d117501c030360301298001c41d032890201d01c1d0008100b0455034240b254410103400e51a080000010303e03036030017640c4c1c400d96900700c1c4079940310909902e1940b0340c0c89080c0000d0004020303800c2099902e4002c240a07411217106420894003040c005039050500104400d00198000c029001d1400a03907019002000050416207200d801030201c800e05403141c14402c0401d28150000304014586468010a9604650889806102c50307518001d0381e079030840303516401d803a811a5038a841e40d00380030300140280a80003a120b0301c050740140d0007060080c6122090280c80c0076906844005890700b038602e40d28481c1d44169040d41c500400740001192240316107160320f012800c00400d001d5a2014100407075000800b1540468a601c50540003c2c50300b000f91421201e110700312680c095103946c07509141303400014400 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 13065897 1250 13064647 13064657
    0x203100512010e060a0b040501080c030a02190503070b0d0c0f050a0507050a050102040e0f010b070203030307030203040501140a021309060b1801140c06011401030b0a06140705060a0c030b01050403050d 88
    0x810081a000e4000420f00c6200000b220b000d4a000101c1e50060100d240e240c41c0580d144c900082400c0d413020818103000c0300060f00404180d201070f402e002040140d2094043c7d061003a4102140c10395007030001c500101802c0c1003d9403242d503000003040c2200c001404010510524404a148284c1c11a081d80c0d10764006017041034484105050850a15414a000030143e5100050100e407209004441c0d41c0541c0c02c2c50140340c002c0e0f032540403102d070342c0c490740350003079410780c014000112514031135001968460b10840020504180c07002c4041310520065072004101c035004280007150117620304040c1e00a02c82007006000191900c80722416510601080f0040e00d40580d010350116400340c00350711082442c028072965070311307103288149440b01000c6c0aa401c404c2840c0c44280c001c0e61203801840d4908000071704805030175160240907035860703401180d680c0005005005e06d5002c10341c1403100e10b2046401440100740403410300303c01803c0310801c01b5201e051101c24001480842d90026044582510f24104 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 13067147 1250 13065897 13065919
    0x10504350a050408010612061103071710090c08090606010c030c02040e01061a0c0601050a1419090c0302090901050901030b0708060f060706020717040b180d050102041d0a02031005 79
    0x1c1101e4502c00e9801604044d800c20500190154000b02c10360300543c00741c03400f00000b5201462003100c500c000e440300400120741041c0181245c450b54901504996007003602910a66030303490702c030150ba082e0705030480400e014404010918a080c04165401002442d0002c80340c0c8060350081d080c0d11600e500a4000c1c1c3e61081c10700c958030001d40c850009080c868108044080b580700302c81c401540461021031442c00b54500008184c2400c14151042c1c80480012004440c02035003844079000011407250240050303a0707400210030201e0301c107080c103000d115500540ea0f0b514075014032041ca0410b0740101d0040d1b03215001080882e82010703149411030b07861700e4184855203440000030451510f0200d0f03503901c610001801410040f07158004c0c03142501c0340c1071400c0011024130311071146000e5840b91092000d030400002e419a03c600c01c40c541c0da03a00c0207200380c0084a0301c1c1c48140c03c98009801803940104103000d1501213900c4019569804a20500107614500d40250007119000f903d102e91400381a0f1140 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 13068397 1250 13067147 13067167
    0x90f0f0e0a0b0904141204150c0309051507020a05030f03030c0a02010908040e04030e010309080405060c0304030b010905040c090b0a090b030c030114160c05120a11030a0201050435 79
    0x2c05900b42c0001007520140342000e051403850210500303c0c0c10003510844581080300107018050324103e0b03513042c11703c3d00807140c1c07041c0584980f10307981e00481c01c000f441c503800306059071002d07900c41c02103032038000c580e85545180c030501061751003540250b8071a0340620b07643c0d2310580b800011030b40c2c0403030741103901038551620020507805407081d4500100201c00201e40480d5190010320b200e44030300e0281d5128882040e0340d500550490b00685070145c02e03001c0411082c03000b070407c60001c1c001c14408204aa2815a8a4950350701860f02078000709822a12070080c0000c0c060055040750240046034810030080c032240d80020a000514401c11041945414000002e9038043c80501584600a0000d02c507111291100e080380e50320450300d03540311095500c400000b161080d0801c80103190b00c0030051100303503005603043d501c5810a650032010846003d2407816000c0381440a00302036107480e000401c41d400d051800c04541d01c0c44489003048030384001882d82449800322800d03482c0c01c0b148600141d50390102c0c1 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 13069647 1250 13068397 13068401
    0x615090f061504030f0302010209130b030a030f0207090203040501020702090603160e060a050409030c020a08160e10050a03030203130603050c0306010c1106040f050909030c0303150303120115090f0f0e0a 89
    0x190024003000c517209030784c40030f040c1c0640081401480407601c015040465949002c1103d100311007041d01903020072540c0c80040c0c0602e50b98180075956004551690703070b40c0c6c41c1d0300c0143d174400c8500300daa994002ca042c00840c20091440c3e40c100e0812400380480304008041c00000200612544140c0754000f40414003680322042604050704000d0024800390b481c0e0f0034094512400110104d0240d41c65000002c1e4680003c240819201e03500443c41d814a480c080e10940c1440002d044880c0354040e0850010b0503548d0200c0ca8401144240c0155845901028442055290030b41c0101c0c241403c080800203a003420764112948400f090a008140015a08000100131207051315507411840014001c644580c118a91a003122021104801d89a0342e200ca226128050414a0b0030306070710600214601071008802d0000c9400302400701d9003030180c0b034004031a120380281d1040c01d009080402c107100c0581d03c1450800a0510038641e60240d500d0300311041d00c4032900b8440c000c0400d541001180640c1c500ea = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 13070897 1250 13069647 13069649
    0x1022802041d06010b0f0904020928060306050a0b070803070e1e04110703020712110d060507020c030c0307090c0504080105040507051207080a020607150e0615090f061504 75
    0x10340100309484428851207594022910b164141e8465240001241c0308604101c82c108601070a00ca410402d840d42448080c1d0040c203016507002901d0301091842141e0750a444180c0001802402030161030700d6805000c885503034200c00d008403c0a0000e10003c051a4100d90f00c00c0d41c4809131603902d82d18035104a0f410040100b00f56841504c40343c644881c03443c00700c2e080c00007200403203041010a0b0503598080191240c0c45004015810000e410440040e400126030302d0180910040e808910328900001c4041039000403c5039503650301e00c20300003403a5040104004110040c0e008104c03100c074540000c0d60300c000900c80c0380c04494030f84440c8100d19114406980081c05403800030b10043c14035142c42901c40c0c44c140a4940566640700740321784850341c0051807004a030008000303441c4842d403913024409a6404000143c2c1d070845860340f030b005004054465040c4d0710707c034800a8105402c0030007000c00c0b89115480c1c054070503405034090010007a10028205d80003101140c2480740d19818008040340c038095 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 13072147 1250 13070897 13070899
    0x80a0c05130b1908010c1704020f060d09030306060e0102030c060103080903030c01150305010b0924040e06040506010302030d020307150c02070e0109140f0103030f0807030209120703050d05030601022802 89
    0xc0039210803c4816812412420b44403d00024459030b070f070290088441c50503069462039900c0206010501600302902c442d40e0041c0041d104901d41070151000105640d50050200c0000ea9103038030803c242030b4007400207440c14400340302441c07a150b15408101d030b40c1c0f04103000c0502183c80000c2c42041c00c2d0b40410454403910758520080c00461a101c003070b00742082c80b82c8004e60b869402e14071100c55610300b43d6075081c8107800303c6c0790317801407032107508440348040300d241c10700720b03046036685100c60242841040801e10652203980142039941c1103106243c2084c240f040681d06641c02031004000240080b1010215000da03800001307501602d6480482c0b41c040e07140c0c080c0703c442c2507940000c99844500d81040c6443c42d00d4803016520398582d8005006005c1003403001800042410b5075180c0003500c151001c03500103406250240c02c100d500b000041c040404024000d00940c0404c900b042045014080d110750400e40b828aa821458003400203501c03141210014018848207045e0505d1204800c0c84c0f6405560b0 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 13073397 1250 13072147 13072159
    0x40c03180b04050606060c0d0507020d0606030809010201062103110709020a050a0206100e01030803100509070914030303040506060111011407050405011e05091309020607080304020a080a0c05130b 86
    0x2580c01c000410040a07902501c160241c00001074460805004686007800d4003402024401d241080407202c0340c126860403640b207850030200d0b0000c51040e01416001e54040da80141e95403008100181c21600030740c1c01050114140300380c0c0040a4488008040050f8050600c21317034827002c0c0c102143c00c048040e08548107061020074410540340c0d004019052690854080b1440c6c0c4e10b46918000030400648074001100403400c0042c000a424440555088000b0410305182c5546550011b440c40710201d451100003030002004020170a8035507030340d0244040c25000b440c035508207034a031103448480c01040ea5050042205110b07540d80070940c000340d050148403615071040d003420000200303160321a203d128002810a1644500c206e000901d1306015500d6894480c40c00f4600700521014501100e0b4030604143d071044101c015031141e400a043d50341c410040503a40340b40c144100840755180d0703003209105d03600c043d049800150584075408180d44044135110004c000909801026000c80414550000 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 13074647 1250 13073397 13073441
    0x8030c06010501110705030616020309030f030a020c0d150203040201050c0304030b0708070206091506030703020a0b0405190308070303020715090b06100e01080a0b01050412030c0b011205060402040c03 88
    0x184010408038181c0c2c500b40d8550022080410b00b13943c0d200c0d40c9000d41541600a0702c04500352014504015a01c0c11240c016a4184210f00c0002414030251503002102a000000c0c501d84040d418031508461a000312101201aa610b0319025614001c1e0440215950740c000046000e40e802001601d509040040c00c0701e0ba01c80d120300d8800a02c18003a20300001040f256808610354500214000b48078000b041c00619854a240107a40500c1a0103044581c16008110000c005030b01d6200b2403001600d4202c41007a515031030601071020b1080010489842034100d45428000600c2d4801283e040f940c140c500982c589290707007000a442003420030303695013191501c031400080010701d0324903070300c00c0900710340352858001c801a0984410440c03500c0c090004198100140186070207a2151000503010300d0900d0a10751180c070341c0c182c00c030340c1c0344d90a5010440c044a054100704a0140040c09024007100401c01088039a03034050b0b46002c003400081c440c03621000203076140c0e03200354414000c64618002032100c2e2 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 13075897 1250 13074647 13074667
    0x31505040c0506040906030605061203220f0e0906010f08071e0905071106090106050a1a0c0607111204050607060504050c09070309050c1903030f0e09070e010e0108040c090f060803 79
    0xa010350f202c00c545150809d400207a0a10b04000c03003103156413442000d50724003100030001c00244d00b0300403140b0008009150010030000c29510042000d041d02c00800b250b00e00b8031404851034404144c1c40700c00c515843c00b4040c00011000301e1a48112403840d20950701d031807609011407030080c005030401c2040e1450201003004070ba80c401003000400c07402030140c0d03060341c40fa48a010309a4980340241a00040d403d40c007002084d503180c5483d03161211004206040c01c40185030641429000c1d07a4036400902e422101184422050140c1d080c4c500180381031a1500d850f08000c035265004001c80942a142d5810010b010b004040c8142e8002500040048070f40349001c0c0f00c05402007400c01e005a40ca4403d100000302181048090003041540300c400c5901003a1079030b903040742d0003220740a18104200c448c10b05066103848144415014000c80c2d110341c44044039a070001813112442c0307001036040280c80000d000200d03420400c0300003560503401002c11141ea0300105d800c081d20f40396000c1041440001141118 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 13077147 1250 13075897 13075901
    0x1020408011107030e0a03020609010c020f06040807030510050106020d03110d060b0a031103090601050d030c060e03030703140f0415020c0604060501091401081203040f0803070801031407031505040c05060409 91
    0x120030304c2510f505041080580c103001d0707004824000290404400c002c200f0166006120030600d9600c000c025070740400301440411402c2c0c00c0355010740080d60200310b007801001024060003034440c05c5070380104059894500000d41d01c24901c0c1005090541c0c5001e002a4403074004211344030040000010b11855664034041e01c003552000c400100064648801e45a60000500c103ca01038020000106a40d9080500b0002d400744004001c906002c1c018a200000407464007070300c3d4003074208001864a81c50003942c068140c3e8460048001041000410800c0014046a506401036008585800200c0c041710180000b40300700c2001c803090f0301c9550b080000b00f01c1150842d40c1620342c0c0d8441031010b488070100c0300c01d406d0402c3c080c07903040350080500c4c28840d985c031401641e400303030003514240403a102c262a0004664019203043d00040c40c054018410310140118001c41c0b0b42ea20002450030500e1515050500c9a11642c00d4082c0303a120008202072100700d00c41030000e050f00900c4156215529690600 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 13078397 1250 13077147 13077157
    0xb07080105030304060c022106011205010513030c030c020112020f0d0f0903050315060409060b030601080906070e040203190e0d03050f0105090408161403040e01080304061e02010204080111 83
    0x86100002041904002c800e0b602100d80649604480c0304a075801c00c40d442c2e86410300c40c4900303034509100f0203602400f00107150080c81d001d0b4811100c10b40c80e041403030075503800030000c00d0082c01c20200c00000951042110b4551901440c1007904070b8210710040315035a05444000d240c01d80081084098503040e64000d101d030560381c3d0010015106540b041d2019174000041c003501040b024400503040000094480c3c45081c00180746501e03203611b8031461411144c03e80c01c0b04070002ca01004114595800049494104d8445001000c0034075125000600c4a41e1000c0f00b9401581c020001c62469079a001243c007110300091000e11424200b03200c43d5650b8580d808410740040d00306004250719044040e0070b039050301d0000e808030804d99039a464401c020ba00c65251300c0e0b0000201c803400e0000c10854042c0300d51100d4040082c1d940c0c2d524108800c1c0c01d449e0103800090040d0410402040b001d03400102c0d401c1c541c84a40115000d40c075294a0590080c010340c2d03c075034003550904183c84142120400281 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 13079647 1250 13078397 13078411
    0x20c0a080d020c190b030f010504050603060f070f02010605040501120507150f031d010906020408010b2e020708030304030c0c060305190b03010603081305030f03030403020303060f0105090d0b 84
    0x26591640d100c5069a559a100a5440240e0803180500c0050309150600301040102c2402d40c0c45034550f507210980c5264001c440d2441d07190340300c0005024601e03190140981000048000f0a140d007422440e4080c0d040d03000d015542402003480781003212a00070340000008060042c003c0005696501c054a0204180e00d0b00300c0e40da02401c40d010482e0307800c10b882d00f030b0000420780c0c8601000144070030079001402d015518a982ca8400665070191704824022181e005101c2d58025890302d242c10641400e583c4800401842440fa01501e18015508200e1a17000002203603104441d100c4000d006034141101034100b04035900001040100f81a00001441c801038425684001090380e210000c070b0886501f55170420b10140390200315041c030b01e90fa403c000b102d880014000240541d0b6503071100d185a04c0300302e03598440403400808010038a024000292091081d070081c3d45945043da070000d45a2000400712131240c000313400e0100322644680162411103c002c2c0c121800c44a00703007840348012230100c0b852 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 13080897 1250 13079647 13079659
    0x2030103031b0f0b0606070b09070611010b061606090507060c120801030201020d0c0302030f071103010c170c0309070302120a0209090c01051e0906070b041101080f07050c010e060106020c 82
    0x941c0203041010800b1001e40c03c02d00400d6000c0c220390f0b850148840140ca9654040c606214400200f40c40c2c4007124086c50309030008124039482d02e0405004800008180d400991604003420090f17103c1c801103070040050350505003038900003840c0c000f004192501020703019114031100070480940204403054620301903c2600c1d81c130310300741100b2207007c1424040240140c02c1600034440490003505c8070040c4500c28019207040a690317009c884501d40100a05842c1d01d460315800e44000e090a1003541a4820302e8500480c1020a0300508400c409001d048507051071000000141001d0050084101450f80100404554521610110b58801c0081c5e010383c070588000000c6481118001080380c404601a181c0a0034680e102040c03102c031001450705040c000c2802c02c40f448480e50303600d00402e405403043c0c66071000c500300b17410305030313000303554480301606103c01d0350140887d00c140d40300b0031584005203141041c0d807014034103071107805032028070748840701481194008116190089110840a0340659031 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 13082147 1250 13080897 13080917
    0x709030303061a0d0207020a080d0c060f0605031f1103040309090b010e1012090b09071a07080f070302160e060312070c060804050307050f1b01021f150b04090203010303 74
    0x164604543d85001000d28102c41004203400602e0309030080e120311800104140c00e00f82d40c1c2d101c0c4600304007100040c0360000c0d201c0c00c08030081210900c1401d942c002d140b00108043ca04000100b551404401d14501c07a2144880d1107405000741500490319015040d0300365a16424286405024040130340038060020b803e00f180d2a015502c60b81013a0841e9030024820708200701400340c00e41d5960261142403600030307110381c7c890340851041e9003010300801e100401000c21360f25100140c0c4210720044a0390165400411240e004101d268050340c03603a40200d01c103d0340c6c410040c40c05902e00b142204212025002d000310018840810300d206911400f02942900d480060507045c2c15003a126112000f006000010743c14070595210b8850164098410001ca03482c01c451500d81714585006507001601c650f03c65401642126150346170385a08500a000405128151058440c0400503d44114000e03640c0c1e098003280402400907032030028001c44d00d12a543d142c48142c0d100207175200b404140d01068501030 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 13083397 1250 13082147 13082159
    0x3060b0402031501050c030421030f02070e04061e090c05040b030106050a03060207141e0706050702060d0c09170303040506010b030f01170109060e010c0906110d030f060e070903030306 81
    0x71288070f0000080c056404a2050740152266001071503201d0652000f40004100d018104001846910010346c104446501e41d240041411400e03104404c00c5402c91072081010b544d604203110f8000b5030104011034600040b4008075900f80c621524802c481c1c0c1082c019106209141c9032101c20f5401c103946c24040b0007026824507003a21068031982d900909850000c0001c1009940a8502e0324416103c80c0c146004211300710707107000f8140190401030441190f10005d41c800070002d4000400643c14541c0c00d00741c9903000203032140a00844461840e4440b00c204142c1c038840e80c0040c1c00360006940b0039010788610058661303070750012101100c09114071400401c000f071443c02980c1c4900d418220482c0e950382400c428150301c4e0a4444400c40564030b5014070300000710a0b0194241c80140040002140c000d074040007405801140d0011042c4554645401001c4002181d0401551002e0502103406205441c0c0c940041c4000d6010031400d030050424402804e0784220440212806550b0501030544c80344 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 13084647 1250 13083397 13083401
    0x702030c0304090b0f090103031e0309080a03050a0905030f1209011b11030906030a020903010f05040302060a11070f050106050108091204030b150406082404020a0308090a03051603060b04 82
    0x580c1400c40c0d58414001000044a6600150700554018107040c136681c0c068808600705c1030081c2c2084000c10b840316218411421882d0080181c42140d1a040c40b2568094650000d54480e03010290101922200010907031500f54000c9101a648002140e98410f16112015180c1d0409090358141b100210080f81078164140201c031050b8031103039040c0360041c50109040e11010494101495107010900c19001c450b40c0d01380180d44180f0b01640d001d69030342e0a00040600b1a000200304041640c9820240310100794005181540a00110300c006801c64022250001714000e1090007481c0e41d06d420700c403404000041d00a002103800c280c8441d8116120202d007680c0f91104200f801c4ca80c0032080c0b0007040030921405084da0040744140110025442c0c800104069980d40d4014410b00c0d0b0000d01890300c00c4800303000041c804405400c4d40900d508140e400104214520310010308210320205030340002d030b5980f8001100a40d40201180d0144c203030900c1d940780032001c0d40700c15118103107001e0120040341064 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 13085897 1250 13084647 13084657
    0xd0e010b0604060302070c0e190608030307080406110715020702090708040f03080c04050402070c030b06010905030601050402090f0a03060e0c0628020309030304080106050f04180809060d050717070203 88
    0x40c107039800c0c40d00f401d0f01200290440e039415104600c05c0c0c103001950722603403a42103000e101ea180840340b424084038140f10944441d603100541d1a4800c0007041519036020510980283d401300340441c101401075031041c6e050140690152503200100b040d00a20122a4020302e005c9100395200e20b00e65403008000c0e18006402c036409040702d180c440300d0a0001780700d0007d165000f140140b500d4281515140070800301c2c3c001e040100c9641d06000c1040c818010182c0800398806070901e0075901684c01e00010a032683c8040c0700d03440c040c0783c0100706402e0303996072414400c00302c036809046c0101d1340b40d803800c206d00541a00607000c0000d00508000340a1030918804551907540c070340715401c400102401d0080510702111071507a04600052145480f1030350180010303c0141a04400032038180c1c00d010800c030311803c030004141d00c21072510042030480141c10400b0103039103811042064440101c030012810520070b402240400c10700d01800c00c1000d075008085501084103250215002d66103070380c01070303a40b8421 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 13087147 1250 13085897 13085899
    0x170c0a060215060d0b070503180105011d0405010f02030f01030309060e010c02090405070e0c040509090a020a050d0305040b0f1902060708060d06140c0301051002010203060d080f091003020d0e010b 86
    0x2c42c2c00d807405001009400d4000344050861010052103485601c81020290fa0740400102e000080c003c6228907001410001d5100380001c020a51600c84602640d1024104080000d8014400982404421741c81030100700040316040d50740b0f14040c0c28100c1e100c1002d01044002c90351481d4007041c4903100d00d541d18030103101a107811000d81d11a400300500050004e004450320b115440c07001c02c3e80c500b50003850340180c54110a15403101c1c00c020410441080080014117264030551140c1d01580d558042c0b00c08443c81030780d441c0c14a52840c10111150f218940006000c2800040c1c0c0088181c90a4000e0408a902d135508030032000d5002c500b286ca0b400b081c1c584400040691000c90180c0c0340c10a58005c0c080c2c0700301400101c3c40a40194000150804c0f20307542c0d2009000300040189082120b80d00c59624034a1008510f180380c000005202007820000c058801c00001c1032014400c00b40b401151802c2d40011b10759a110360000707200601a40c06003080303407000c50800040210220050141100010b4 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 13088397 1250 13087147 13087153
    0x60408030a090f05150108010c020a020307030605060a03060e0c010318050d0e010309150515120303070f03060504021305040f090c03060b06160308060103050c04050f0d110a170c0a0602 81
    0x58203121040500b01010050399054150f001d03c800242041005244e4042c400a81c8040380d0301d0f101103030b400c4900c060b07504000d54200d000f140b4016030340415244103503984800001059228000841c200c0d0b069900000d11141c0342c083c5205403200000790212500c1c0090fa028400c044088502c003143c9007880c2401041a0b01044c418242d442c055a080c1400c0c50041c1340c0041c1510305501c400562040c41500011308580d140c041c0811144810007045a8800c182c503c0480340010026007503403444018802002c1042030456211010f12070307008900100340c02002550ac94680840407aa0380707021b849128400c5261a0404000c0441806800c0034150094541b040203448c60b11a0400340600103013855004408021958000901407580c1d4803481c040e81d0348402d0f502c2d0140000d4100d42d0701038911401550140b004120a545214007194440e4042c3e45400c10140c85113003200600c041082c4541d84101c011901040c8e0120703000b00c20000300103c00813036680303401010600140200a001d40c00042e0 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 13089647 1250 13088397 13088401
    0x150702010f03020f1305040e06070804030c03020307080d1e1a040209040b1c03020115140d0303060f0602160b09010906050304081204061415011209080c0d020d09060206040803 77
    0x36010300c0800891150070b04025142107102d40c0f0300342c019404007000031500642800e040c00710381094803032007911000110040242d0300300210302510b1544001c00050800100301622401c061007031042c0c49031994080c543e00c0c0c403a000c00456402801e12a040310140c0d607070008106e037011515000d500341d1500c45c03d070010244110801400065030041e2035a0380c116413108142112601c0b0314100c500c0a0b00c50014541950360145002420b4400c00c86404030600b0b5035540612040d0444481309181d40c4084800e945400750398038041d40079220356480081100000140000d145801040303181103251000880c03042d46484004d90700c068019408042c1c0082c0914006102c000e00480045810a01030001e841c10b1604558010000b81411039007100c2581d00c40e0042c591001e00c94081c2ca070440814030601d402103a07030400003040341ca242d1031501400c6486608003001e12400c0021140300080b1441510f00c11503030010f019640d80b1064001800054800380005160fa102141d0306001d160b020740403070315507 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 13090897 1250 13089647 13089649
    0xe09250e060a11280b070e03030414011101151401020601180c11011a0a08010b030a0b1504051003030f09080303070c0305040801020a09090f09020d0f06110a030504060b150702 77
    0x8000e10f101d400405104583c2c00d0b800c03200302c6400c441c080005020b034206003400c2502d0300200c0000040d241e04107000d52480c411806075004415501501c22680310003a0034900c000040700d070212103c00c0840254038140145082d001d1030024130064400d09880d180e40c00205000484e03440c1403d00c6010342201411a8204000d04ea60300f00d070b0b20085c1c0a10300700c1c00d4510203003049400c4a00524002d410130a1400b19139480c3d0030a554400000c180c3e2000800508540c0d030086501d8200308040180800c00841c0040c2e004007040006044100d07018200700318a00d80a00d027420808510b0000b44c0c040340e403004501507254440c00c1c01d1416242d054000e513085860710f000c280c2c0c007152201c9046060100030302002c10002000d1003e400000b480e65645010107180c41c1080085403c0d8440c890825424523003420f0250321800e24040c50294401c5480d41d0888581c180040205038242070789103100400556000e85c0c83c1d15030441c0b4046d0b4007a003420014510b542d0100480400010030140c801c4000f8090340c809 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 13092147 1250 13090897 13090907
    0x20904020609060a08012402060f040219030c090b09090a0f0c030818040c02010c020c01050c01020c010207050607021603020f04050a0608010501060908010501050904030507020603070e09250e060a 86
    0x800d2000d00040d0810b26540001440ca42000451000007016903004000c0598507031030b20402064820100e0f0550404100029100c1d000103200c2080c1c3c054050100d4110740360307502c140d0682d203d0110b001d038119840c0d181580b10b14665108200c0683e0404201007103a00d840405180504403010040c03040c80c2a959070341c0440e0180b44002e0301d010803d1800000807400c0703d4000c145000d101000d1030b400c070179104e040200721442401820116890080da0b0882c0c6070300001c2c0446446000d00340b403511603402000c01030180c4201c1c0494881135001103503460400000241290240d4616002d0700e42001180070803d92050982c40040d500000413540700710306051580c4941d400c032140013004503c041c1c9601d203e07030035903400382d1140340041c21140041203424020300c10340f40904421a1346200d00c0c10551001051350142c248041e01c50f40002010a02d82c0e40200c0401c003290310042c26160303903441c0c00c80d51881d00f1003200c610700f03440707c01699800c90054410041d5440700c1800502150400030001000c0395 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 13093397 1250 13092147 13092151
    0x6010f020307022e021204050118030606060302090126010e0702190308070207140a0303030e190c0e07030227041113030c06081509341103070f0209 65
    0x20660000704044000b68540500e5140400319002d980c030b40c004003000d0a0075001107854048070464006e844a610300307141c50021542100e40900c0c0503404405e410701d41c40342c6081c16a00081040307140c007000041f2950035130050320381d03028240c8405c8a070440004100c0d0003a42030100c0b4604c00449440107010f9185c031a04030315001041072048030b10745540b80c800e52031000c8003080c0c2940800d143d94104605190304001000142010b5a0120712000c0d80c40040751080d02d0340d000040505803203e8140c6001c580070040303120214028205008558024146213403045401d014034a804440480058581802030084854161407040c20300181654224041000303403101c004541e0142c1c803040c03c401982d104801519002d040b215802d51003d1840c80c0c46080541079500800c1800840010030030341903172450510300075a90503207010216660f41111034104400014621180c001d1140720f000303030300081000601c1c1e400283c0d154103a0700007034540d40c0d940e2405a80c10080c461191400c1800060902601e80d40d = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 13094647 1250 13093397 13093427
    0x31703040c0e040506090d0e090408030403031e020307170106081302060408010c0e0f010905010906110304270501140609041505040e0a031707050328020406050a0311040803030601 79
    0x8003641e521544001d080d080140c0301544c041d0301c007009020900c1024400701e100d020b07240c241180105084008507403007600041000e007050700301100050a042c0240c2060211644195162103483d580140b00b00080d002a01c501000540710342182c4040700c10171051a040e84c020362102862641c030035640c0350485524850403604017a05100000c0c0c0c42009000740c1849010584440410f04091014007080301000405207041200c910000c00030360743c2140c01003080d52078900d007041000c0b45480610f407071440340c0e0740310040c103c1503144011344682460440030300071b9448003400e0140740d0b601c1400e003a0a40c1002152548034004011000c82e51909502a8242c01000769a21940c6a910340010b41141c40314515040230780c201d1100b48040591264010103030791641c040c80e0509080100c401001d41c04024406034403030015444040e00b11928088128080380d064034103566070341c0c42d542d0003040c3e80c0003501001d021a04002481c44000198002d54054524030001075066a036600011a46950100101 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 13095897 1250 13094647 13094663
    0x90325060f1719050c07030e03030307050909070201020c070303050309060f0106020705060901020a120305040b07050a0509060919080709060605040503030a030b0a0909050105100608090706180e0f0109050105060403170304 97
    0x2030b056000507001c0c480c42064050720792506c1d5140781c2006000e91107092905c61098008100308640f664104041c0c0700042425107207450b440d038808805a00a1142c00c1c480480b0348210903000080651107001180b090140d60107581080e26809a141d114001c04e014000241c0c011510034042c034141078001e000d4000c414812078490f90302d551281c000c20484106040002500c1e401080140b01c01000c2c410b40051140ca4a00c0c41c05c102141e0003401c0d4094180b00902ca41000905201e255032041c4220f501c0314000c080c085003050b990015075035242c2584c441c0103002030902a00042c4030b806141610101d0380050302540c9080100101200107001c1e10201c29400780401e1070100b8011803e01c0303600c01c4148110000201c0b0709100c000c0722819455a8424010018024100101d00c000800c0d404200c1d40d00c0e040c6900c00c1c1140b0805603c0b04034954001040139481c03030702001140c00a18a00904903824404100000d07600c0b407091001701c0c42940000303402014507a0401040c14a503100450b03000c0d0080c204 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 13097147 1250 13095897 13095931
    0x806010903050307060f0f02180f010c06050a0c0f0206040b0a0b0a030501052509030b01090f020c03040312080c0a0c120509030a060f11030c040b0a020102091507050c0105040515070206090325060f17 87
    0x10f0300084074003d481c0b80c41040c0d512107600c6c605c00d40107104611c6080c0240020803641c42c00c2e40d210109024014042c81700075407100741184c0d01d5203804000300081d5078014000d100d5464980e19525007a030701e000500040740c03d207030201607030305000b401480c007541d400802d1080a6800c00c0e00e0100540900182e506009608100e00242000103001034009540310304042d4000000840c2c00420811000d4501203851070100700405005800880d415410765000d6a44969001010000d507030354007954241d02c1e014051030400404000e8168042c44032030a4000302000300000020404400d800f0071a14806802006c1200f0700c02c06c47e00b030002c2c0401034624400035283c101c80c0004920003410303007010700c000b80501240a404122051107001c0c5918820301c0c0030b6040a18080000d60100d140c1c4011603010030001807000103645500b030458001540c00350440381002e4029000c07000c4d0b0000c440848412420799038022a28034424032811098001b41e580350041d1805940014050a4014142c0381c20100380400d = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 13098397 1250 13097147 13097153
    0x215061908060a1103070801060c051c03020405030114040203030318070302130c020606030a02061804020d0501030507050307060201020c0601150e03010509030903011109060a0806010903050307060f0f02180f010c 93
    0x11840058030100d0081c2565090003c20907041e120f203248003c010313400034000c000c40b607a806034506044584a01c2c180c0c40420b4181012402d000b401507010350703101c8040e019002d455800d03800610481d2001d400800511103a0001c0c500e5654003581d0082d4150001c00208180c50b441ca5000e40e100c10841e400d650201d5131340d600140c24034a040210300340550302e40300c00003540c0d40c0502102e94801c00603030191980a00b103a0010303000744560140b0500c0e03012010310102007030721107130b05a03058031081c240708120755612410300c1681c030303800351082c54400d100d080401301c2e1a51042c000d80342040040b1f00241140d90a02d13290000c03245121250404002110180c05081d90702406154040c01e152000b640e500ca05031001d0509460405c2180f180c01807042214030003d0f15618101d5000062514040c8416200c0300300490340e040f801d52001e0720510000c10a48107000e01e60703002014510651204201030002c4444c100d0903802221002e12561011200b4845142440d070911807403d0b0052400e00c4401103165 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 13099647 1250 13098397 13098439
    0x50f040803030f040627020603091f060305061303090e04020d0f0606090b030d05030c0c031603050c100b030a02041a1206010305060a1104090e030d0507020a0b01050907021506 77
    0x280e4440c80c02e00050188001e10056124543c04040614240c60031420082c01d4500c20240031b0100030300810f0300000150508006000404441c00c2c8080c1a43c06481806000301c050270309070005031101d0064002049000e0350301002d0041999054503259501c0745016001c0520308070040041c0c0e040400402e4110014a41e80402c0e08500e221718400035001d400c1503501422109258942c81c06607001c5103480d042c840d000425260b1181e684880c1583d1020702c3c0b01d50034194002e141c901040c80780e081d2440020950002c01611b03180054104a44240340a1082d58050716489094180c058101915000250900740c000541c10790310b410751100d02e4460a4085501031100c5249000c05404c000010b004001c82441000e4000340403000500403080a0307034a0034a103124600c60480c40c20b40c1c8003401c0c90208410320545d00c541c1c604000401035403508003c06500d410700e0000032620544c1d40c07400032580345842160705008006503801400030440c140c50a49034520081c125950005180d442007031045021 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 13100897 1250 13099647 13099651
    0x207020d0821060d11040b12030a030506040c05040303030b04091b1d0c120714070309050301050601090819060b090703060602101b0503040609060f02090a090516050f04080303 77
    0x18404240e0788591404007120904290140c414540070482c041c048660348a02d4004040d640018851091840d8400000d0051468400e03140d0400c00700e60700a440024040007626250003191400e02c038540d51103080200319164880d0300d2011400901041c1301291003030340800502003010f440026038038600c0d12008101c1c00c810000c60102898040240820301d452080c240078486070800045140c20400d42c2c000f81c4e406605521660201c10600059101d4884c0712880b004441c1d00d41c1003540c1c1c3c0b2413030800a18194150040328000e60a02020403910352190207514200c2d041c0e1006800c9030701841c0b6400d0700c0000c045805642080d120044680b0954400300c00d85d00940e0030b80c4000510750f14040000c0c1c14015a0610401924a03115083c2c003044c0c021048042030061610303100d41c1e02d40d01c45c42c250340209401c620180c60b541c42e0039042c402200d55079006200308002181c001d2403031365490520320142e03541200d44500b80c2c0e40802c0c0b489500c0340260040c1000e02c1254103620700f441e445d030300c14600d15002 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 13102147 1250 13100897 13100903
    0x30804060c03021606061401020106030213050402030a14030304060b0d02010206070f05090a0b130608090601060507060f0e011509020403050c0f010e03060c04050f0d05061803130b070506070201060513020a030207020d 95
    0x11b070701030401803c00390500b40c3c01c07501ea0078002801620318603000601034048602c1305104458032000060110b580c2400b00a44466001504403070350018010401e5a80c0c2040fa41160110320b0096503507018500483c8003c0a0b41d03050b40241070315518982c0403a0750844003140401442800e00c017008180d0b541c5881c03040606184001103403261070700b1a040d03101121650041080c000004180114140d011031f42c2d5054a183d820701c04e80d41c4130705140c040300030031100000442540c03410414510404c01900f0408a180402540400d030a0711110000105c1c0f05034400101942d00c50340e80d040b501d0412201d1885600c80c14180700030014861404a8240007048409009454000800340000e25002400c9051710200340c6100a8000099858035075900024002d00142d01c908501e00749800380400861fa5441243d0f1b00080545942c6d02030000d580e0071925003210203009813400a600148148214401c903403004044200121030084540002d40c0058045030030103800b04039080140e2a400d07402483d0500c = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 13103397 1250 13102147 13102151
    0x4050c210a03080405060708010302030a08090f0a0902030a0501061e11030c01020301080607090b09010804030309020d080a09080c09100e09030c010510090c020106080c151c0203090f0a030804060c03021606 90
    0x34045c81d10904002004088100748600b4400500151302d00042c5440360b03950103011070f0b941362280070005040d90f2480c200240e012000c0e8101080c01011500a540145071107030040c817041c2d8031408141e41c1090ba65000c0200400c22003850440a403181c0080c0380d041010300c2c25a4501000799545a080e40d01c00d803c500c0c1a644410123002d2200e501c0f42c000001000082550350038040c004000070894107001e0406410180c40d80e81250070b41d0750340c1d244c41d04c12562003410079640300340509000c1d102400034403540700f2a0003000c0c2d0b50301481c1800310450b4414000c8048160a19081c9000d072140c03500c0140c9031040703610062042c1c201c0c0030000d104881c0908004c0c644400402c0c6041d28540070f4034100d52400085904050f01000b03c202c0c00180d000580404461000005110841c04a61030041c4659681c0d02407940c400c4501d4400e80798001c50081209005541c121141c002d040c070750740d003101c490040010b00003c2c0080d01140d819409458403403c2c5180c00340c0b40105005500c1d8200040311400d4881c5a = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 13104647 1250 13103397 13103401
    0x10020d0807020f0604030f032307180b030103032304091508010e0606010e01050705120901090e090604060f0b040504050f010609060602070b0c03190e0906010804050c210a0308 77
    0xe80155000358007140303500c001e284541c1c100701d01a888000280c0010180806119002e0f200c174000d0f0814540c010760400b41802200c888032203890b0010013500e13410f000c25680035480c2040e10003409140140c81c21340e9800c601d5070f481c0d5074080f05e803410007058103040209250024110988000010320080910500119004842d2800c003550786085a20803100c680c5040030780000440c02048403a88013a003400c01ea580707002503e0044e9610321581c0401040c9000f00803100c2c018200c420042d00c3e2502081e40c07280c032500e444403c6590f2062040c0c0b0790700c2c41c5504c500c0001e8006006c5170000c070b40f001110880415516038990208041e03d2017550107c5007030300101c5072800103000c01d2180e00300504040d042880864503201020b5114406400307901150b820000c1d01400040d800c03c1252403810a00c47e54081040051100814020301c01d00c280380300b068200d0100d44158410f801da01d000d25006000f0780841440700c0c1c104a0240e00f4124941c0d2220b070740d05102505000240404903000380030380c488170024 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 13105897 1250 13104647 13104673
    0x603040b07120219031d0304080102030907080a02010903060b0103020904020f03060301150609050607080c0601150207060f05090603040212010e0114010f0f0519080105010b0702030c030a021315051002 88
    0x2405000c4242ca82d481404003141d0741c600002c21001000243c10006881c401c03404001e000b02c201c0583d500700610000500041d40380d4154011803080d4105c006481590752036071200da407600d6110702c010740082c0d1032000500108045a010b58080c1605040041c81c1c01001e0001c54141d8000d150032114900011003084207604085c0113444242480d6103441c000769007041c00281c0407062074045d10f401070002180752420049807034200c40a443d80d0000f1141c6940c0c1d41c3c4c11980128001031f4030403005004112002400700d00034004101b07031200d0b0b51103041c00c1564038802c1c0001e90700f0060060b6441000b684041e01c040400b8460344040590407400840c00c020341020390000c00f00103a10014058044080400a074140c55a411040c0c4008542207002d0540b0052090707400540f6400c000038070352a08000003004950400184200303442030741607401c1e18050b00c2c201030311003005071000384d0007512034256018404500d6000408036200d660032a950b82e51106c01091982182401c1070000d6842584c0001300 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 13107147 1250 13105897 13105907
    0x90501050708040c1202060903010212041a1006050a1209030305071803020d020904020303070605070801050a0b03060d1202010905030d0b1203160305091c0308010303031a03070e04080403020603040b07 88
    0x400201402c04070010b08041d0b40d01400061039106405c29000000784401c1103549406c1190201d80c0014001d540301d444c0da1807082814041910100e840d203590541030840d40700144000c1c0d03c2541c68200201c50f15140c83e0342031fa016800012441d0801040d42d414440b0b0078014456041ca050096030002a02c6c40c04101c041c0c0404035230010020b030b803903841004000580c0c44c10130b060030345a4141c40031041601c9610201c0d14500800302c004100c1401d03c420003401d40c1c1d0100c1014125001181d044121036501c10506a452005984031707a00134070406c0c1100041200c0d040d031403600c0c6c0301610001406400b252119402d6801c060310780305502d9141c0d0b940d030600c0d10342000400556850344001c1c41c40c100411511028076031042100034180000032800604541ea400303511030001c0f070090171b00d8039050304a10703008166140c2400114013081c07034a20808a071144203c00030b6044200030707000f040d0507800c08017020001c60005008403031800c020000440103031914400345000e24410040c40c2d4840c10f2058001d05 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 13108397 1250 13107147 13107151
    0x1a19020c010b0111030c030f07060b10021f020309060f040302070801020c0709150803070609170a050304050d080c04030f060b041e050106020102030c071103010b030105090a02040b060a05030103150209100309050105 94
    0x617607100f481160007900c4044103e07080c901005d94455911021450000080c10300042d146500c80d20459400d83d0f16034010607810220391159a552088820120602040340810303031354094154002800540800e0342030f01c10941080c0640111005141c3c0c0c0c841180c03d9a10031040d074000b90f00300c600e0410201009002d00c13803156084510040a007403d00020503668025040081c01d803c2e102c0c40b080084c40103d21542c144051000180355890302c0740038008d4015130041d01c0465044c07261941604d14076214207070090140861118840c030306031079911004e0441c0003800c402d8400c50765842e80ba51499a480c400c18080c03914044d05560802c002806020031680168000d50559004100300011000030200f06c80c40c15500210031400c5030401d001080c0180100122150907610704024064445400101280c0091080320b05020841e10181408001c0c000e45000a001c10003c0c00180002210a000381102c00c02c5c841005060941100c00034002c2c80190440741c000c255212100428041c007030013200e07 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 13109647 1250 13108397 13108427
    0xf0f0907020d0806040911010507060204030b040b0f09010b01050f0a050c0703050a05060711030d021c0507120f06030803181219080a0c0e010503130206030901020a0201050906041a19020c010b01 85
    0x1b611206807a0145d9264400d0102c034100031001641030100b05180d03040d04d010b16042942d6104610701454848a0070900340c2d1070f440c24800c6000040ea9014050169a8200d501a920030342081108444440c1c1c0d90462180c40084c040c007800701720218241048080c0080d0f00460091092070503908110781452800741111081000540d0615a20400001103e0000706c0b0030400580d00d102c0e81c42c111a58207483d02c241910780b4141401c3c491150351000c602030808105000c20010610b00d401030720212842032000a007042c00500000f0941c3d180c06142240c00d40d804000c2e1030340341e128240b5820351940b10340308589400c038000b15200ba0155204840035807103169460f0402040c03410f80c5018008021480c90241000380c00000900e07044100e0208009403070740901403640300d01b40000d2550107504031403056001503281c00300054120400203055406185c00207064030503660480b00c0000c41680060101c8540e000143d05074491840c4c1e403000345000080d810000801c8160b1030001444446204c6880c = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 13110897 1250 13109647 13109651
    0x4060209180106090e040606080610050a06110c0d080c071206050a05090307020d0501020d020703170c040501230f030708070306080d200a1b030303050a09110f0f0907020d080604 78
    0x50090f290082c0303000c015210344164030301a43d81c40380f41010103022543c000321514000c4009100001e1320001b1007000f40c43d000c5840b40c0c0580d4032018204d5040d84851030500c03298ac080030a0422505180c18001d0031103000d00205032504898207651450002c050307208180f100710417002e600a1000324410541c10040156090010340bc180700040e1366802011070203440366407031581c90002c0090035412117a120180c00020b5454101a080281840e546480c40d40c0c103410710710b4001124602840c00f01c03415100c050715414001c0c01d041c61a1001c000380309040c0c219170b0324200a40115010200c018610a941c142d4400c0740c185044080241915815449200c090740641c0c0701070f903055080040030300da89614007002c050350128001400d28200d81001e000e00725049040c802070707003001c100c4600300c1035078000d84040c0110703290262982c007240e6900a01805240001d2480505803400b80003240c80e241e030042000b147d203021200003490045040d03171001d0240c0d00501ea983c0d6140c1d0420082030327000740e04030f41c2 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 13112147 1250 13110897 13110899
    0x305061e01030c090f0905012d0509030a050a030b060315190308031504060302060301090204030b150d0206160209010f06020f03090306010911040902030703021305060c07061407020603040602091801 87
    0x5450842c0002d4003c4001130b548549280120151175440300e03c030349410400070b01119603401902c449004140c4400c0f41000c2c4541001c103808490f5001e010b02451040c4000c610744540180221899003000090b08109502c0340403500590307444101960044403480d4034601c4484200041104083c800e4065050311100e19104202090044003607960106105846802941c030000c0010014160b98000a610640c04800450032200c00d030b000d4403d03644900d04946440e144e5a00313070b00e862180044034950054800c503030300c1d0040c2041006000003c113480c201c0541c0d140158000b91000b00700360404940c3d40342441d800c220711541000242c410a001d04080e52600001d000802d0720388405000d41241139070ac4c0c00901e850500c4040443c1c004180102046480c0c0c10719003802070280d44403030040840002030ae1004102840c00d80110307000341003010010140f2901d804816220310720303518011860000c040c408000542c8442c07000f11720482c032030900166a00e410804000b40030200c4000d082038030b001000 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 13113397 1250 13112147 13112153
    0x6090c12090308010501140909090a0308091507030908040e0403020a0c0914040602030603071505040e011703030403030e011e02040f0b03090d030f0f0e06060111060903091c0c0305061e0103 83
    0x882d1138103441e020710303101101c601d24950092080c0315a1034070541101000c42000001a00070900c071800d580301303549001d8140c890407082661080d10350415240c0d2403e40300460000d0f4040d0348041c040700d00c40c080306814035a95000c480100c0004640c180c016802c804440750802080046031006000300b0780703042040b500c40402e102482c03100148003d00f1a6400004220a9070303041096600a084600100790068168000140281c00a10966020074003410003c1014269003811080018101c4011400e540d25610110060305c1109035031040c55513500251441010040e200c0401d08a8880025070f076580303002c00e52050510035500c03040e0a90018024002109800310f0160000c2e00286404180f401074040705e0b000501146002c081c0b80c0e468454209014a804511540b00314026204c41101400c2d0040c503588035a800c0b52a40c02a400c100a0040d03186080d115614174104200102511900f03aa0741e40c000a4050342c2080e1001d5003e00c04010585840080040324403200001e032402030f51546d9 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 13114647 1250 13113397 13113407
    0x121401060f08030901030b03030f032703040b070b0402010e0a0603140f160807030b04050103060b0f0f03191a013b04030c02120d0302040503010e030909040b0601050d06090c120903 79
    0x40c0d1564109903d480204c40556420000d8500c580c00400ad0b450b0b0781d0500011100c928014014203ca0201d20340070300c5448460080f0542e82110554450540380401c01c1e6186d03c41820000e004a05201c0c80043d10038964481488400140034036440000340441c00007508004090005c04041c81c4503000010484110003c407074040c900d400c14280202144c035084800e8010305210460319820600c5c18000000388000d50308000c0752204180c1e00311000e03120440501000103445050260076a012000c01078843c10703981034071060540119031940c0700d641380311b41501c1100303001e0b4049290a241003a480b054143c0300e42d4142c0074a284c0b40b20040508100c0f4004c264800d2000340054140400707100203800f95212459003901c034107004825989010500300020340250824045c05002c1c3d881c04070303120701c1004004211400c8e80d10040c8120490303034440c0d507042c4055000030711136410000c01740441b1060021a00448000e0401c5800214001c4090f000003084409107145440d000d504083d00f22000c0b903000 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 13115897 1250 13114647 13114657
    0x120f0b030c010c05070902070f12050a0c080a030b04050a0501080d0203070c060311071a010311040e060a020304020301020f0c010516090620030c030c07030c0b040501050301060c02030106121401060f0803 89
    0xc1c00c00f001e1031202814001c0c200101c55001194a030b000245004c100b1004190b11008140700c0c629500062200c094101d4081c00380b010940f0100e0b000070505408a4a010041c4c4927a50003840c01099a03000ba0012a098560a442000e1b0881d220310041c040ca0703105004a4496003860310041d1b042c0b164940b10000c5e035003001d02c40c240c14996240340011102c1d20060032940303129080a06282c054040118151081e8401d02c400d80d801d010400b0070701c52900e814042e00c003001b82d0b0b840042801d51074844c6084007d44c0040e01c226855075003002034105101e14003004c4c103440d00030000009035074a00110211005221f41500008114400d0401c0c45403030380100f04860000c1c0d43c00d211001c106500103c051852091005105041c400499000d918034400030740802176078810903841c550a0343c0e40c1c2040345540510300680380800c1090005200c058419800c0d100c900f40010004540113944c0c0d40c40c40803201d00700106a0320360800c031a404444031824002c2e0b41c028a90f0303404100c4040c2c940010240c59000c3c03 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 13117147 1250 13115897 13115899
    0xa020f0f03040606030c06120e01020406050403020f2106010825030b1e0108011a0a030b0402220908070209090703050606060708070c0b0702151306031e050106120f0b030c 75
    0xc00300100b014000d00fa400301000d5980100c043e0744841d1101c40c050b201140c0007291034110f03428181c101024113010300948048841075128181402e046a08108103050202030080d0408215822052048e16480081129001d81d10150040b541044885030030140391110050041c0c48582030f0b450a40c181041d100c040b40e400c91180b18103510340c80d6203461070901040d1040c60f590503100c004503480c04194403004a01210409442da00d454a01c1400080c400c1c910015010309003040c0041c0150602e82c0310b8001f14440f160f008800b02852000140c1100c6851030705403007211001c200007085003440131000c0d8100a1040080425074616540d10b591640c004000724000c0c040450020100480e020a40f000145e000002d018101c2e00c42c9402141508218810b9204d51248103800701401070721012500344242861640785035034204071041e0064803819800620b00a666101e041011484e0703c1403034085d1540340d17a0081e6400003600e40c5416521610818040180341098001250fa4001000b10300c0d410 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 13118397 1250 13117147 13117177
    0x50301050d052104050f010207030b040305130902040b0901090512060411030f0303010e090c060a0807030c0908060703060929040506010e10080601020d0905030604020d0624050301050a020f 83
    0x600c0d4640581001005030414a4103c91842140b00d10a45a000b80043d140d00343c4207440803a40340001283d5070115880090081c21180380400c0c00300340300d00001c20025040420620815a840c80084105d91041c0d01a030015a80811400c15961784900e402c8002d04040b9090840e0052400c178017038a42d140035000602e50a00c020350b08196807000c2c003a80c1c880d80101c8081d6500d079070b503489010b5041d103001c4581c0b01d003038001c96150001034903004060300c08085d519540d240742903440c2c134001d5000b0115030803032030107020100038005846001000010711854055401151251400c902c850580c0c009400384000400c07240070901011104150304600d1480c21500414951a4200185ea01552100e0450780240708680709440d002d0300034041d9030040d0001c5e801c94144d90300e8000d048485055070b00800e94990003200215001d8a8039080c0c1c0c0342e80a005090016056861004400804280d20102001054101800c10240c0303000c0c0f0030b0316130040c81c03148258544440c0312080340240c460f480d10404015 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 13119647 1250 13118397 13118419
    0x10507031b0f02010f020d0204050a060305043903061a1002030708071506032303070c270c020c03070902030c0a1d0301051915080601050d0311060709032105030105 72
    0x9100f504840c403c1a154102150f80d2600301544a000c4d522600072075009501d6940006051437182c4145403056401800c8040405042d5904201c1307030151070790740d080242685c03424065941d03191400200030b42c8101c20003c2c00b41c4140c50540140b40000d9000c0348036036207944960500329004003c4910450388070700016558190b80c40d1268000314000c01007800d00f45016404001c21226031904400e030307144406010b000440c22009150740b880340700ca0083c500c0e1860101000004451480581d02290740162400b07190a4038040000b02d4940c1500d00d0016441030380b40c2c3c280e6003002d00c0710001904420380b0942c5903103072006020100b031051000d0780c000c100c5401e070344040e03840c03c036001c601210800070000d00c079904044403540b251109440c81c21060300d2600d44002003541c04a0608411a4184400f4000c103038038107002c012009100a50550034400015450701a0b1002404054850450b075201c41c2036030381c00c500749030201c0f1500340c0e041c000c000880190b1510503034006c02682c0c110b41046402035212 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 13120897 1250 13119647 13119677
    0xf1401050708070602030405070b090a0b0304020301020c0a06060f0602060103080301060e01021c02061e0601080a020c01090b090601030302010e070e04080901030225020306090d080a0903020a0206030106050c010507031b 96
    0x501c00c24401070107515001c500d60003001882d800850107980214122100d60791030b400d10618078414a0711456004082031410004d068820014580c802c1c0024001414003801c0ca448a040c030070040e504658080d660a000d100c1c1081c032459038000350000c0d100801813981582d0720f04586100601035801841000001d80030203a208005a0112100c02400c2641c4a8034022010750342e40d50595810500c0e20308a54614840d41d15408454410345059442030b6007600da960802c03000f0743c40f40300340c0c8905540b00c00014000c6071040c0801070191900d6802001250b165040090840d4079020728559283c000b90b4040000c3c420b058003094000e600818100e64401c44d03840160000e00c11014240c4101240c1c4820020780140b9005900ea441c0c020f60603034140b80d44110715030b41c40e8081d150010010440d14004121140e04691000d94600d01c81e0044403a00c0046400182c501d4009a01c11400a40d00043c5940840b10a01941e600b01768281000c0c4448254042c005001040504030142000101c1c4592044 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 13122147 1250 13120897 13120907
    0x1080a0b060c0304170601050612040308191103040506060607051e0304170d0905040507020a060b120304080a06060603140f070909060b070606050316150908060c0304110108010f1401 80
    0x14044000b4216680d40f0360b81d0041c40121340600c42400b01c64000c6000006007420640119946000c200050200703954030b5503002c0d20035403006408140e00700010b41a1541d0608280304008060302ca40c2c4a10b0b40364601864024503040c40103084030b029800600403100020300c0001c0e00f10440881911108000103443c0c01246140507641c010311454030a13000080c0c1c1c040021405015103100303a0303980d808a07500d030070a0009680d025240140140c0c0400c00c4040859910b0703001641e1144018880420104269072262664229070014070442d0414120b6800b004020310070352000308418203080c4045550100c520146040090038591030708800c000140041e03101e4a102c6000d0000d5020800040b601c0382540c0c0116001481c04440709d6141603c0803485140006502c4c40c07502e0181142d4080c1030801381002403981003881c4d2042031201c049400315141340188400b82c81400d030a52001d4603481d0900f05038120110b41e054017811300400c500148a441c00040860003940c81e2a42c400c0040d001d54801212 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 13123397 1250 13122147 13122157
    0x1210209090f0105100302100306140105090103020c070b120f01080309090601020a02040903050910080f0c1b0303070507020406090903080c031b040305060906070207060e0f01030b040e07051201020901080a0b06 92
    0x1199413810040107540000004002e00b41c0303000b519001946000c203a810780881d060781c012025403000015460352070f90300c039070010080c00006140240c100044403031441d1400d1150b81000400700404030340140b400c501c0c00103a0f41d01902002110000d5450010903a84a100b903d40040c00791714603000050099000b004803041c059406401003000c0b00701800c00802d140c00130700f007a0b8410301507202e13005003c6110707000c0d0b140944900000a503080c0c5903c904980245d000071081c840040714045418221641480038611910594940070b68503280381c4108130850b4a2138003c01003951501c00c00201103a030280d04e041e80400c110755a59a02e449419038142c118a03c0700e414402e41c203001601000b00103000c90b000e4015100a400c481464039002c10603600c420160040400103011001c1d030160518000401030701050040c1000a1035002c9000800c003600c003488480f038000d5208200400107800c0034045900920100c0c4000c50400d505000001c0a03c1ba020704002c0160780c031041d00c00c000c1c1e03485074201e075 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 13124647 1250 13123397 13123423
    0xc0308040c0e0702010e190506060d17031003021503010e04030809120705010b0f0102060c0d020307050d0c030b1306050607020906040f15090501060f05030126030406170121020909 79
    0x40340e2500f250020f0103002c0c103603c500210300070708404c0303d64503c0301c46580e240c19034040c0c0540300340d0740c0702c0c801d0081c0445c480701c040d5810440c04401d0100040b03000020340c05404901e0080c40c400e0305500510243d0708807250f001017a000300700010005d81510144e41508182d05240021140d15100040c52400b86a142c9104403004000354500c02c20005610001006e41d09642d4029041c00520040ea01d90204444508030424200720b01c0c010304a03c1da0041d940300100d41001424000001c80c01c1044519119031080420380d100d0100a46151035984c502c00c44000703000c1400410304103401710b4224042c2c080001d01400440000c0b13442c0b40c3c0c5a82142e4011180410100b00c03a0341405054805c0d0b810622610a940703192000100d401c510903406c070711082c54a0b8640d54590b0f440c111a05451401d50b0130b0102c0c0f0000c903400040c107408400d01c0207100031700503582c0741d08021802101415012a043e400540c140e208007000c0000c070750312018070200c2e098040707801c80403543c6c1c1d140c0c20a080074048803000d = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 13125897 1250 13124647 13124669
    0x30a05070c0c08030d060b03060a0303140d050c071515090c09050907030203060901060201060311010e04090b0a0e07080705150702010207030b041a07050306011707050c03030c040501020f0a030c0308040c 89
    0xb080c3c0000c00005802c0120b80f0780e5041c0500c80e65a0501d680b148015505260010002c40090010a01803a440d80c04407030211340b600d1505000000482c1110415550f6004400c0002075000520503407000d00d40c91103403100000c221542c416070540025000511a400781030351112102030585001e2024038004240290849101c2c0c03400080c0103000b0340c0200d6a00f449088600c3c004104107105228841c00e41b0750100724005c21544e8100190750300c3e003841c1c0b00c00b90312503200c1780c4440010301401e03001400341c8a24103020490703002c1d610340b203820052030341c1021055901403441003003243e5840600f06203440c491041140e6544184c00100c5c20019660005460441c13440148400c0003a03c05040c55610013044800f142034a60500c02c541c1072000380e891034002401c50700c01a5000009048468100109085c400c3c9032000041c200c0d41150800c450000c0c40c0c20303020804210b556018404401e140c07426101801c2c540c0d519580c0580040a1004c01402300112280040c2c00c03c01d1100c2400302808030f100c21 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 13127147 1250 13125897 13125899
    0x60111070801050405070f0303050a120e010212060406140303030a0203040c0e090304060305010b070206120a0f0c05030405070b09060d021e0408030307030614030c04020f0d0c09080705090705030a05070c0c 90
    0x740d14082c00054904440d28482c07200c0000d00c03a0040342d20507090303c0c0d15075182407030403001100031620320744820000f070b00300c603034071055032803d076200b48001c2484403945401480680340030410441260096805400e585800c00307201070b62a41c000c0300702c950042029030016140d490751b0810407216a103079000303103007241018418000b010b10000041c1044031490381d028050b5a8079001140d07960702448500942212003030058030300006004111a074403d90003600010840304610210090302d850074052000708034008184400e102c0140602c2d009411600051031806d5001c0000c240d0a00c0340d8031007e180c40f035003c903011151000707800d24000c3c0e9a401000807500c0d039880c0e64100c1d80320f506c245c400c000464035060000503400022200c0c942c013440c004024100d414022401e00c00694041609010300796810030105418401503c158100355400e9607600070400e0030030212910700755460b00a02c3c481c100b240c1c10441d44c9583301048075030003070003404003183c5522009000d0301e901520320401841e500400d80 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 13128397 1250 13127147 13127159
    0x130905010603210203090d02100201200903010b120c0918070b04090b151602060d0905060702060f04050601210b01060519030209030c06030c070618020405090c030601060806011107 79
    0x320300320b083c01e068040d10718504500081e81e90713100710401c03642c0041c83d113600400945011141c0603501c1c41c590001068007143c0106541903092041c0030300952100101d4000313241e007024400e920340c2c07403410b443d00a000c15401e9a00da035215500401c0901c1501c45600040c00f40f54150076038400c80c08081d049499241d2510841c09881d04280210750740245441012066858101401100003003083d00d418902440c0304800d5601400200f0240d0b0841d00810203d110400c56100344a6a503010f040a4a01402c0c5208000c5c00c1c42c001619005011451500340401706101107840b0f41141c0c0c1071250300301d05900c01c3c2803600d041020582d024100300110030002420f40e82010007400100300d0010030600e8101c280c90154100d010b942000e6805500c441c40a21031410b00d00d00a41d004403010118074140b440c1d03a51040203071002510005411206024180c0c1182810b00406800c404040d000d41700d807811080210340c0e03826051003000200440e82010642d80d0f401403150440041c2150141c540f0251601 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 13129503 1106 13128397 13128413
    0xa05040803071203060602060106080109090606030501020c06010e2d0606070203240a0b0d03080c090d03090e060402030106050301060311090d03020d0305060405060609130905010603 80
    0x80049103091082025005051080c140e0040071034240c5070080550b08103a0241080d58000c400601c40076400c040d03520705480e130081000400004908040010740519400035285510004500d21043c00c00308415040e68402e234001c01e40c940382c11200500c0742c0c0440f1810034501031031641131030a42002c4048540c20840083c0521700303145007500000d0030026459424080c51040000d1055004104000c10307520040214003000581006400b242c0650140a0014200075407400000c0040c08003a003580c110b403002600c0d94690440078070380500742c0401809020920319003c00080c03100c2c80d00e8000c5030b060728147c0d603400c5d0542e4030b05402a8003502c15035040c01414002404183c1e095141c1110100e0341d28001c2e802003800140600303000c3e04a034406024607000f035041c04200724280d01c5020444580110541d11240d106226401d590001e01031160024080d5081000001c103024041c = true := by decide +kernel

theorem cover : BRFrame.Cov 12949647 13129503 := by
  have h0 := BRFrame.cov_init 12949647
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12949647 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12949647 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12949647 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12949647 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12949647 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12949647 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12949647 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12949647 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12949647 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12949647 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12949647 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12949647 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12949647 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12949647 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12949647 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12949647 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12949647 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12949647 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12949647 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12949647 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12949647 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12949647 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12949647 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12949647 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12949647 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12949647 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12949647 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12949647 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12949647 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12949647 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12949647 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12949647 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12949647 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12949647 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12949647 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12949647 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12949647 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12949647 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12949647 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12949647 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12949647 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12949647 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12949647 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12949647 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12949647 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12949647 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12949647 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12949647 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12949647 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12949647 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12949647 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12949647 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12949647 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12949647 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12949647 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12949647 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12949647 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12949647 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12949647 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12949647 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12949647 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12949647 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12949647 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12949647 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12949647 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12949647 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12949647 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12949647 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12949647 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12949647 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12949647 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12949647 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12949647 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12949647 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12949647 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12949647 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12949647 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12949647 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12949647 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12949647 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12949647 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12949647 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12949647 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12949647 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12949647 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12949647 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12949647 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12949647 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12949647 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12949647 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12949647 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12949647 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12949647 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12949647 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12949647 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12949647 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12949647 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12949647 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12949647 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12949647 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12949647 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12949647 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12949647 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12949647 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12949647 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12949647 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12949647 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12949647 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12949647 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12949647 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12949647 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12949647 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12949647 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12949647 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12949647 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12949647 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12949647 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12949647 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12949647 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12949647 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12949647 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12949647 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12949647 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12949647 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12949647 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12949647 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12949647 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12949647 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12949647 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12949647 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12949647 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12949647 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12949647 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12949647 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12949647 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12949647 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12949647 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12949647 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12949647 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12949647 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12949647 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12949647 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12949647 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12949647 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 12949647 ≤ n) (h2 : n < 13129503) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
