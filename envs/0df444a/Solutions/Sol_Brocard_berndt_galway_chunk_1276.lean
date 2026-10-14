-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1276
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T02:07:28.747581+00:00
-- url     : https://prove2.me/submissions/1fe79f62-b0dc-44cb-9bc3-0ee70dacb1f3

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 229316546 ≤ n < 229496402 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 229317796 1250 229316546 229316669
    0x30f050d020c1009060b121011120f06090714030109020a02070806070f08010e060105030a09110a08060910050f010909030e0904031d010e03030d022809 67
    0x1034030360822078400020800c101c0c040c1818035415010451901c0e40c1030800446e000c0c15070590186054000d030641402000c1a1202103040141d00003035188102e400440080c090030030600704c0715412105105210a80b00c81651003450100c0e80222140d85010080307950018006101c1805441800184121040c0780c014206540c0d1030300c111000140d588030710500d003000c02d95161021a181c11181404140e0000c1c00c0c0c1d015100c04405070881c0d052581c002001444000c242c900401d9490380c9441c05c014410750240e411020051000443c0358451101580741d010958000b0410b10031800034003613100d030f0707030065500c107205155050035183c0c60011103401800f01041d0450801201407c0d2a15a43d911100e0307030b00443c0a03643d4030851402080e52804c01000588429040c00b41c076885c5001036070b8000044640841c500303800503884420014602c1c0e214034800940d54003078540c440c2d1a000fa0359000c0e0211003221b03082401c00300c68411075030701400c9010204841d400b62110310045000e680101e10071520 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 229319046 1250 229317796 229317817
    0x7021b1e04050f160516081b06011412070e1305150705030402040c181a071401023006091504050c2205060d18080706020406110a030f05 60
    0xe20840e4000054200c440488196259000c00d206002c20103c02c2c1c80702c0c134001070150034018589046500301e001c2040004000411301e0200203241c160040074941860801040941103e0b6156194000d0050005000400c0c034000e444004000703945050014004040341c01c1095141c119481b4050010b5003401924426a10b620460354012100fa903110041071042d0500e41d1b0382c0d80c4a04052040100f9583c008a0740c10070888a004c2c1c110760503000304c251600320f8000d280b0000c818542281003120501079520041d04828410710300354003102042d0014030a11003401441c030036040c2500711030900e40f8407034013000000f016040d0018109042c00007046410100703440d607650748443c2c62000103060380c1044070078180388900401c51000042030b0204101140d1078142680c4015803d090101d2400c0c050007242d0403141340c64140000c0344034124040c1e03d0744641c0000b05d10b9561449420a01c010b94460300c244000600d005044650400020911030301269265a03803603d490054001182c80c1d40100080d02c = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 229320296 1250 229319046 229319089
    0x203040c0306111c140105030610140112020f030f092a0f0316050109210206070206120f04050d0801050d0b10050a030507180b0604090c09030b0114030607021b 70
    0x80c0c05a40308041e034143c503c4d145600400c110034255000112240306a110314001e034407080070b011950114907244000c4d100c0c1d1510500c0c8800280700100e038500101413514054901c0003803c4c45011281000461080d0040001e9030380030b1321000c240c5544e85403d03580046134844030500a4944600003400c0c1070061500a021402a01014000905001008100850090082d1010006940c00655800040c400c07016900f600420f07a902c844064541c2c0b050092246400007056011075a40005455480203080300582c6180361000c0c2850004005a03030540d03c0d0700c202d24482152a1040c03001c01e050302e002401c00d42d400c60641c1d07035924004c3c0c07010f071a03251003004595002c0390315169064000000c40c0034400034400b1600d4001216615080390413258500c41c1482c4050b072081d1910412641220040d000010718106088405c80780103e40d13400091078003e145d000001d881d002074005008002044081e69210b449441e41640d0b01d0006c900c0c810341c40c07542c80c01d49195910b05503030030003550314140452 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 229321546 1250 229320296 229320307
    0x70903060f0902040b01020601060c021908010203090a0614160305100b030702010b0f04060803041203090b0d0b0301230a11070b041b080307020105040e090f010f0b010e01030203040c030611 83
    0x11682034605110070141059518140702041d841c1502824084070340030300290280b54140003008082c0c035011003029005d07088104150011408114020b4000d0015000841d100d00380086c0d81ca4640303010320b030159500c900f080c9241c065416106038590207074000c0090300060000c0e18909038043c08008100d0340301640f20810005001c0080b100035407007450241d00014030201791070b00b0810110703e182040d5014900c0c01905028040e000011101507852800140b4080d8080d4074086402450903002030000710004100300b08107800c25048847c440004a0003440006840c806249140800714206070254006001142142045504c080c1036a1a0000510328007006602c80048490040d034080b0340c0207021400302c4400d2801900d11002130107808010718544821500001c0442c011350050b228802c6a000102301c50720403c10101e00c0c240c007104d000307110100214107040300512003c1402804200a24031b43d0426602c0b038801c40c0d20855102a60b03003503050554840b400140030b0260003e0284100300700 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 229322796 1250 229321546 229321553
    0x512100504030203250209011403240118020901082a03011707060503010e150d02090a05100504090317060411030103060c020111070302030a0c21080609010f03020612070903 76
    0x20340c0e441203000e9001550b4514030400040c51040980d2541c05902081e0710120f401a0345d0f03100120b044420070501c4407002c850350360020b410180012001c0310000d250115045031501c0c5002428100e40c02c0c00400705002840880f04001e0344200610b40d400602060700046280005451190320056821703010800015aa800c0694550080e08400d240382102e02d00203085620410400015165511341300d425949042200c00706800080d00e0069054140050700c422503e1300e8000c458240c1d002010740e17206040060014000349010340300240c89800542c804551801d0500810308000d50680d40c4202c0d03003070088503001d000b0a01074240c2c1d0303129480c1c440780c2c03200078031010281d40614083e400002c0c2d41032107198041c2c01c451429004202200b828414040482d03004002c0e02d080399028100005004c0c05450441111280d8146061303020603107004c0445120350141e84d040c4241c5040d2a03030404c0c1d90300c45040e12400c50b11840001d510020401a201c0015849000b036a0441201d0414225164490b40c = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 229324046 1250 229322796 229322801
    0x221090615011e09081902030124090207051203010909030905011b0305030a0f020c070e010909020a0b0702130e010f060512060c1b0a0303020d0b0f1e030c101e0315051210 75
    0x2415001c0a40b5402c01072429454280324000360250344484101c0c2b08018841070940c00c0006224285006a0120300d28003406010702519140c4c60382c070101c4541c0c96844143c400e00519840100342e0004003007a8010400d94007401c048100706541c2060504a15000d036030031203081d4070027880000450b4450317000c003100742c10303500140007200c03c100c01415000e17090440c4500e0540c6c05921040c5001e05102c0a2405611110b84510544489442e065a102c0d100d001180e100042400c4040c120307032900c807040e18000382c10f50211042200005003440601c2d980d0080020010b91850084410340002020600c0c100843e07004060052010380d417030101a81d1150944e081600300c04c4e050707021980002d0b17950b20b12030062090041c04601258070102c005039000214103030710385190040a516280c5880f2900340c1c0ea0030803681028801c0104a8150461000c81c020104041c460002d003182e000b0092003184907009004d1840b43c4504c00302e02d181c4a5252804002140004020440d000d001d40500480b03140c0103070 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 229325296 1250 229324046 229324063
    0x150a021b06010305030714030301180c0c0510021b010b0306060f120d03020a080105040e070e06150f070317040b0609060a0b180108060105040f030b040201030221090615011e0908 78
    0x4c0b4091a1165841d0504220030040c0143c505c0302c6030010401402140c81c07140e50081040880e0b480001d0100400710151982d982408014000d4402e4034020200d19015400030501c1d441102540c400c5500700540140c01d03148542105981600044000b80407401c20750310700880c0c0440140a1200a40684109400c100b07100d12544002500000d10001d4940c0101d0312a005043c1030700c1c10002c51490301c001a0326002203009035412490754101041d9203944102404210340044189a6520f00b414840c42561b036010404c11030200e611071600018038501c00075018800da4200380c058003251b8900d03040114080c401001c5652169000c00b010032554400805445000c03015580341010000f008000340c41408001c0010781040410881402040400f241c0702d000c40e0b512122901c46c54031544010b802074001c2c40304000d40c02e1004502100c410004810703031809498000c1c255401911606c0c8030082da003403650015404030748000c000d42c0d00200343e00e9940052081c20329000003640d8580c0390203030034220072 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 229326546 1250 229325296 229325303
    0x506031c050322050a06111b0a150908030103060207020402040314060603060f09100203060f060f0301062304032901090e0f0604032a02040f06090e150a021b060103 72
    0x8070400003158032881d014258100c080c80f0390301000a05035680b0781d450b101004c00400650711030607100484d1113218181d50200440d040c3e030000b020301d84405070307580300036008081c1c1e020200c08008001d800403c0c45a07041c40b5400103c1d40349140e09588404010b0f6001d00070482e0810f030301300310010219809107448600b9814100140801e4100603080515194000d843c000807880c5c0001400310b08000050030b00d9a00303600d0034001d40c4079540e242c0000c0708850307014540c54102c030340000c9003180200707500000c40c11390301103840700c6803810310740c000e00c1c48882d0701400c1e60f03e80300c41c00b00b2045c00490266003092280c7c2c0031103901035030681541c42600b40c0810081c0d000ca040d031a1618001e8016010512400e828100e2440040c80c00d4a019200180040c1600c5528521110902a403040d61003c10707030202d90040c0c02800a0042ca451102000c000303001903c01c140482e1302d403001200cae42d03400c00b04a01300a9205014407420719203408005c04006c0d8850024030f11141c1d51855541c5600700c080c440c00380254003 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 229327796 1250 229326546 229326557
    0x30a030c060b0405070f0c020a050307090c080705030c072d05061503031c050415090302100b060a080f07031d011d0a03021203062101060303180b04090506031c 70
    0x200d45000c005840341c40c20910321450a080030000201c2c0e110030403290700546803402400070304040c00400e10a82d12600174503014090500c0101761840d294001200d0f5428550b28510140d5501408403007030301007074805510304042003001c00049043e95410605000c29118100444042d40b5050f1080607a125805c0f03805400500030428603200445405090580503405185400c09030101c41c460f044000182111140d80c410115045c82100d0201583da08215141000b00030482d00f806540c4010815080c040b5600385192a0002d04020302540c0701030001c0e0b101d0f100a521034400301d80f0111401803010f010142d403014140c49403070311800501812882c203c00065014016804030440d400c20010004070740d072200c1c01040009070300090520a0701701060404e5125114100001c070b5107500c8010319180a45038030703c141010081035100304200e034400c1c1c0311000c680680c0030000c401e820440c07003180c1e64900203000401c0644070540003258405001401e880100c541c4900282c50400c01c158030364001b61 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 229329046 1250 229327796 229327817
    0x307050f1605160e06330d0605060c1b010311130315050603190303021309140f07020c09150904030507151103071b0b0c070b0c03070c20030a03 63
    0x4090010140304100f00304100c407281d04200140070340d000013401c114050181c072940203510080d00004900e000a944070780021594507021205810b03017015040700800c518000b00014580780500c05c65002d003420402030031420807070f1940e42060480c0110f0039414152541030304211107290a00070104140c0c03814082c400c403825414507092803e40381e00086889454501808040e990020729100c07000100303454114035008500d011400790142400d014121040040301285590440d0070400307041c2480c0300040041c1d41c407500c000e8062441503609038050380200c41030501d40c3c1828200c3c507511107040d0341d003509942e411101244400804850660005902040b50700411074400300c00108410b0507801808420300018001d5540d1001078a01000e0140f840002ea10310500c1181c8418040e420040403d80f902d081c9603030142642c00a0030849020020b04001886e00c0030100980340107406503a615030100c9480c1d560b9149000f11840800d05900e001c40d2400300a50f070801011040c58401c0d1785a120a8 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 229330296 1250 229329046 229329053
    0x606080901060305150c0d020f07060506101d030a0b0f06210309210604050c03010c030e1e030403150b011106070c02010e04060801060e0405060612060c0307050f16 72
    0x140241400340541d0510100304045140003031a001c0f400303420711280800e52a419840303000c40c443c50b441c1e05e451500210320502980c642501920140d40501c02c280200c1d40c55804000e04564500020b8020413940c804a10602880d9035407822520b4000c0d08072800e00c015600e508081400489405061003480d2040002c941444034003841004000840c0104010070324a82644900036400350314010400c400c0460b029040365164005020000ca003650b2181c2024284540c5802254a144d0700075801e0111035000c141c460311405030321480b0a03000e0120500b240900200d88021924400801e100520010010600c10508080c03116030b0b09000103459680f08002510144900384661160342041d400c00000a4000070b46084455091801c0010b148852000070004d0441e0340091245618040000ca011443c9401035409907014104994840e03507000d04002c0000c100392050451030300003602054070307851520081c41c0c01603079909045052419100d1448055000746c138a141522822020510a1 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 229331546 1250 229330296 229330307
    0x18040504140d090b04150302271507050709020a0302070506071701060302070809040b01090b0703030902191a03041109040f03030501090203060105070f05102a091202040c0915030606 80
    0x1642c070038100b160f089440c0c004092064095131080d0004070217118104c804040c420750483e0b60040c030f900541c0500d0088060214080315085c501c0b580510040c1e214820034885140548120f190b200d8010640c043c14150320034040d4000341d4000301416000e0140c0c80000300306204240c81040700350b480218040d130196400e0a9584107a0080090501c10801036000c6550001180c1c0728104c15107010030140030303200c0101d49169240d4014500e20030081f96500426505402070b01e1105d000700c9840e0304800c900d18208050880900c65004080304055480c1d034518041000707107900501a00c44901d443c000c1e90041010503800701d80c211070f407440b01e0218904068041c03040e54003400e1460030031815840c1100000e01a4890b51a01a0600c00d070481d8900070807400304010711005811003801d0045091951000010900200c1d09080002c4600400d2400742c0c410414074003110032010540040d10040c0c0c00340001854000c9010042104009000c20313407040c5900100e040c0c0304259400200741e89000c2c8010308 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 229332796 1250 229331546 229331563
    0x807030905040504030804061d011d12130e100801060b030f0a060e130c0b0d061802070203030a03020f0702040e1609140402010f020712030f09060804171804050414 72
    0x225510b03000034440486d0380000d00942c0300e40d0001000800038a10241e0202100141207035094139824956091040c034001c440000144018104032040c0b940f076205a0755040c050110f10200c03200e0030200030411a01e0500c1116048203203584090030641d00ea0304202e00351509508a055905000400d00c0404800150340d00d901040b03001003048824240101145405005001403000c002c1c1141e81070705100c14410341c0001400070119140d41da032801002c80010303103601d1082d203a80b05511240c084078500d1500072540b0081e0300401540c1780141c0d100069000703400000d43c82d40ca09c0d106101200068849100e62060850901c00504900441c21200c107080b480faa00311451450900c0f400648050744c2d0f940a94000b0350909000d120080c0b084c0c01245096010b0780058861000e2070000c2c014944c000c014890700d05070030354034503e2568682c0e901390350800080d00c0c0106035884109418800303441210207050b03200324050f00e003c0c020100c034001074195181034405440741c4040c9201442081c03000c200a04 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 229334046 1250 229332796 229332799
    0x1e05030c0607120e06060108091e01090215070b061e1e090a0605010914030a0b100303020d090602101a030a06050a0b01090830041502010c0306050d29040807030905 72
    0x1303440101d014490300c49001070a100d051102d44008180500b6050011900d00c5502000c3c00c000e0418100445001c0c002d0214140d000d0018156103220080f10f40b0100d415541d04002c40142580b1010148980552100c01c011003800b900c800c42c00041d03440100d0301090441440c40f5403940c4003100b04001c0d0005015050001d82490041304220b00d907040009141190030001d22110a001d5041c0840d08020211000400700801c402c100104601620381200680303001e94201d0740b0102083c00c0c1991021000d0107400003617809481062806a10741e0020514054490014200101402c003c83e2070403106c0701317045419507214810030031804c50714801c6001020382441d1130710100c0d181140464542c80003039180c0d199420018042002e080b04041005045100440c5c0203a80d50b98480f03102014015601b920341c015420002c0e8015454403078040e0718199400200040e1281d0344d0717030303a540b0001041000300810300e0000c400055243d10080d03c1310b5104030b0081480302d07600c04652500501c03191854001c40d = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 229335296 1250 229334046 229334051
    0x1050102030c0c060706020405030111210106080f041406160210020f030612030405100e0102060a09020303090112111603090f06080109050a020712031a15071e05030c060712 76
    0x1820070403000a2a880f21000543d0810fa40750001d0030804040e101d01c0c6c220540540c00c01d4032520007400e030080217001e40e00550743c00d201031217140450400700000030f00c21640042c1502c408074904000364000e00e500244140306680d07420003904019428464126902d120440704140f4000c5400e805100c82084401c41400861601340707040c1c01e030045c034003002d0041c1d405081c08203985040c0c880104100c601601c801080030a000f030205000600c001c0d51200c2c042c1c01405410301040b00c4000900580042c1540203000d1801c2c03405043c01101c0502c903405d000e400b02070700e0798210898941c0b02c20007002c62080c0c480c000400301d081e0781000f4080f5421540640c0307002c41c110b4030800540e68820491819603601c1d00340828585c50301e640c4d04001e4054000080d0501051140300b031041c68055200b10f02022001903403000001d445410000000c00074004060810b004100c0003000038181c0040c0d0302d4009088800403590202d0391650b0b840d5802c0341e800c0365815030000d030038050003a801494404548036140c405 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 229336546 1250 229335296 229335307
    0x31206191e0801050c18010c140c040b09040f0602090109030614041b080d0c0f12120b04140a02071a01080102250503090f060913050f090303040503030117101109090105010203 77
    0x3804024801c810038101440c11b200d03010709490b84038514003520560000c0000c0b404a0446400540b42d16080007c507102e1842d0041c080128108a1091849541c0080c6070102d606855280d4001940c400c03d00f20381086079810011000031014460601c0111100d17032a654589400d280c0700d42e1140b00c0c100c2500c0050f6003203a082040210020390311460000030700c0e00c11010130355841d00c0301e402001104014500c104003095503107203d40c01860190b50070000c0d0011311201e151541070108450f1040c04c1100b01d500c1280004120343c189800070844580b00d04000c228054041c4d851910750b0a080e0003103907045e5000155000f1900c0031020740030850760310900c2502020b80720303a0b07003070b940e4400c1c42006401f50711042c241c90181d94600041c0c42c0260409803140c20750303201c220304580044c002200d15403081c900d144041400e003200002500d1117503500000440c510390030484a82514021881c0519580c42170408008206200e070041c1c00720000000030994407008100200982240160059030466205211 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 229337796 1250 229336546 229336561
    0x4051915210c06050d02190507060c090f0303051b010914150601081914090f071a07170403051903020d0e0105040605130504020a17010611031206191e080105 69
    0xc2e0004032209400c10554031904d0481d0417001e80103107a880f001c9456841c026094080d0024000d11141c0d11905007008200e030401d9050b500200b50f4080c2c0c4000d50440034052000901880060002c0407260716008444d8074518007030f13800d4443d010701c210307a01910f101d41a806080c0030091180c2c031182521050405184c00e80000b008924010104040a151074002c0c0150401304c6d88035001c5101d10800503010342c9801c80d50941d48503024141080c10388130702c600003c0d2411440c25821075404100980c2c0f4a401016158541503024071400d03082c61141c10000040081d20402c4022043c401ca48484d041d4440b02c0d0a002e13041559116441c014081d110101c00d041d607070b1120440302920341c00e003440c81c0c645007456158028400b03e038004540040c800150302612541001500f48074000302d4481d40701982c1c0702e003411107500449900d86c0312664800c0c0a072209108441d01c3c070703592150340034062441c1c02410a01c0c140c50b01030107a014a407000607800c5a50503a60a510102c2c01078540103000b13200b942801803 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 229339046 1250 229337796 229337813
    0x1409010903120b04020d1a210c040b030304090f0f06080d0816031104030b040605130c0608130206030f07030605011803110a1d010609170604020405191521 68
    0x10b0001e4840c0e40f195498515607581e415a102c00c2e01004003000100003e001c0300308600000c10000388285131200c2d8140000141c1a50150300c101908068006a01c0d09400e10003d01035806415515000c28000407810000d07034452040035903042c103800700320541e269500300300312040c0e85c1111005402007003040408a80080d0403681003c441440b40c0090a2804812001007001032540021f0010024000050216150030a8003443c002d4a04001c103407034000c441030b0705048603d802403440d00f10303c004001c101c1c055905030750701c4034110362004502c070a19030005820383c2c03003122498100141d20040c404a254540b103004003178117083c03c0c1703c001220101d40440d10360b003285c03200910716502d1a0394800d0b181c42d00100c1000400221041e44a0b45003005040300c0c0140090003104c0002d940f0300c40024400d074a404103000ca643c14140502a1502d42c0d40900000c3d180041c0318180e00d400503004030110045501c50031203500c1039100b0011003a0700789008007d40165400c9240028445451508042807001 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 229340296 1250 229339046 229339067
    0x60a031205130e010e04021908071710231f0b070b0c03010b070204200c0a06140f010e0703060816030506100806220203100501140a0f0605070201020c04050702011409010903 76
    0x111417440800800d188040c0c81011142c1040380703e4001e40b440001c106490be00903c0c090340740d40f01600c40366081401928100c0300c040c4002041da10340240d00c040d181c448003842c56003103060204024140000d1000c000d0707402100d0b038000451400300003942000c2c0541081e1441e0081034014440303186500d00111368449001e1004040c3c440c1c5e9817604200b515140741800ca2001041104200f03407a605110b06e400d0b00c41600380415940780c0e003024507140141c418001d180344160300f141d00e00302280e42000000d030b03180d00c1c0041c030780414907540d51004111000704005041c0a49801c0d00f1102489080d40303800c509000c00545450040341190b0b8040c41400c00100790641c0c461400360018549000301d025181d649035405102942502410400a07107a41654200a058486c10030a0355900102c0c0f1003800041c05087c40b07038503030810700c1e1001406024803c0c0010080d942c0140b046031552a01040020304462080d0340440140c0c2d950180d0030513058842c105680e010500c040204140500764030050040d03080c1d07 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 229341546 1250 229340296 229340299
    0xa1a15030d2703240501060c03110f16060e0904080a080402030712050a060c050a020c120703080c01060503071706040312020f070302070e0603010b030a0209060a031205130e010e0402 80
    0x9588031814524500b80001c1c00c80e280a140d8508000c1e9070b400c0a0b552440103240a04403c04d0743c1600802000b4640281d6049800c1a84c1d20300301c0e0080d6460440301d50012000261702400381740300c50118404200701ca00c0d0300210481803110304520b4944050202c038400542a030044403564200404103200e10103884c03004515040c902c04d150f0b69407002a08280e00358000b903181240d58045c3da001d015001651401003071140c5010801e640032041c094405001d041402401071348580d00740c0c038003402d120071103180c500c540c0002c0310340690700d03a500c0d200307207401205204520ba903555808202d0b52030100400d0780142032041102c603414100c0000503440300c00051018040c031410304141403006445504076030b00800c5481d516a181c841c00d24009441b183c02d0b00c01c08200c0005040840d00e5840c3c107102e40f620140000b0010880001d09d9801c0c8451840001d10b0164481a22407000000c0741316007041d135078403110700e996403a510100f40121481902007600180e005400820041c40400c2386082001d030080c2c0c0 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 229342796 1250 229341546 229341557
    0x90a0e0102040806010803070c141e0301110c010209040506011b081810030b0405100506070b040503130609030b070f051206030a0602040603020405040506100e0d050304080a1a15030d 80
    0x200108020301900c40e030340c0103503500d1062100000300b011020000c1c001482c132841c0c190710102d60b1045081a003030300d8400c4e41940070002d015822141d00301307000b640b20f02a01c042c0000c0342a410701320480c0881e400c1640807814a0b500000c000d201d45c1350030b01c540d50748141d003420101c240c04183c940b02880701c0d0740c00c0d2004082d004005a0000703040a0282e04d1209210018034140c1e40122a0b10014007030040b40300c0450185041c4008142c1400c3c0c40c02102d015640054021070918010fa241d42d10f6400e8090300580e0385000411081000c0800341201078003601d12500d403151114030b9490140030b1507070001c01e004200040041051041ca034440210384600401c42c9040b0744030740780c80c030000c2d0404811000091869100160000b03206400d900908102c503011501007025a44070b400b440034241111800340c000030642c698680c8249031401c43e050030240604100d9041c2600e034100e445c689061480d0696406010000c482c4000703104004040d44810504c54401c010080100440c0d610900a880760f418441e = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 229344046 1250 229342796 229342811
    0x80403090803040f0305160311010c080409060b030105030d080c040302091e01080d020d17040807080c0303010e0612030901090b0f0705061906121104050606040530010b090a 76
    0x180304054010181180c9415641d60302c0d9501418101311503544812111802220759030701000303809081c89401c03245c00030f001d000328000f00307801110401c03807815044850303280c01d21010072680040c3c400c0001a010141c1078a5481d4100350800d0324060f070720040303401041340000401c80742e0314084042c1c404482d8161010009512206071484400303001082100c0c201c4a00400011850390000f01822552029000c4da001000c2800c02142d0b0a80340c0086000c03010810804200005d154000420380e050040c90a107007840e0101c40c4003400c5034821380c007812440006406001d00d9141503405040c6000c0a1401035207060044c4002070302c034503440d00c9101101213020500f156030080a50840e0b9446070b00005407a1949004041c0c03030a100750780281404c10710f00d803000208070050501d2683c3d107215000b04d0f1035944070398104204006040c00038881d80d0840c0c424400000c1c651144400a1291100306483c0050f8007101c0c0314194a00002d480c890006a04240f400700d515141c0d82d5180c0d4001c02201c50120703404 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 229345296 1250 229344046 229344053
    0x60312070206030c0910020706030501050307030b0f09010902060d021c050610030c02012c070603050702071a04030c060c020427060b06040f06050a081612020a03090501050a06080f010e0d0804 84
    0x14085d40d090f9642042c81c1007070b003514aa90100da40340580704a610100026601d410615039500700a00000b880c0d019002e0200c1c10082c00d1485071640861294004541d002542d80412501e8204604514209401047c0111002480c2e444480d85080003c0d00704034034a8200005103e0000590710541819a20078034541c400b07200b03400c01e00345030303074646008581031319455141c8040d6004c84094030414040e81002141c002d109000d11030080c03c41780d000700303062401c051042c10440904030368140035110400000001442c0743e0403400050a032615600316024890042c402507038162005141c0c141d1100c1140800b035040f80c5070544102e42c12210008011140c003012400c644902d030014462802010f000082d019030090040003060599505d00380a07842c5e20051810009802880c40d01041d25080500b1519005ea400b40c02c2104003858041500702d083e403252800c407071013580c0000c0c034192114400d012a400800951070075901030300c020481d899034580c010740c440003c40121810002c802e030202c0c4c2030 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 229346546 1250 229345296 229345321
    0xd0507030e131a0a050603060604170c1801080d0c0b15040b0306100312080123010c1403040f08070e180f0d080609090c0a0303052506090b06031207020603 68
    0x18224410010060510000d00f40c0f660001c900c003200d4070400c1180e0010075075007803000503070b8007441014150b18140b0341010012009040103c0e41c2c0516407007403c074020203030380c0c1d0000911800b80c40508014041d50410070854244601040c01000307008500d03001600041020100a078000b00e122a03814003200b0314030024010b031400b0342c0307125894031955051000d0040b00541c4241180d04c5050740c81204581410240c0d5800c109201d51110545290541d605080e1350f050071032001e00d41490071100307205480d915000307450005401d094940e44046020300ca0111544d034590060401d48000705003031850807500c0040000d0050009040c00c8841c0d8100400c07800030442020205c2c01201690080b400f2100001c0607400229505441031400341c3c0816038100000c154841e25210140012840f141141c6007616103904c071240342c8501c0803915108020780b96103650a000c41c10300c518004176008540741070128620780043d0859101f0740100c1c0c00b0805003041801110f00d815030603035941d6103980c0c400050350030 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 229347796 1250 229346546 229346569
    0x101d060d09083001060c0807080a030509060a09050709020c01020708071b15050306090601110106060816020309310515030d0203040503120d06050d0f0309080d0507030e 74
    0x40007420140d1460802400300040c0510001805140c410700e410b204407161040720941e880a0801488001409000d2040801c004910300590040d49040c0003603541241d80c1c0c1c44442584000b90b0360342c060280390882400707140e400c1402d80406200a009a481d00c54584000740300744044c1d60750006a042560a00b90180c54456400050760364a464581c00c100d50400c05140503985641c1c2d00075800310318001540d0540500c5032040c0d8845003507640788024030007000b0010b4142e9060005155000301c041100b4040d03240541480d0b52441c116042c01c80e00e49a80740c42c0e10f60800255001840301013100c0c0c48411180c4121060003140d00700680d1501d07414009204003c140700d0240e42000d042104a0b5403030703000340c400400e0a40071201d40000cad50270304076181d020f1401459490b1b0404001382c40a41003c501800442c0501400010785031b659400080040c504000116030383c9000c3c01c0101c09140d000050f6000510452015105884003000000e10a1288240044c18090220110425510346181c0d00c3c0 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 229349046 1250 229347796 229347817
    0x1704020a031a0709090c17060109081c031409120a170c042102130e010e03071a090d0e01030e1f0b0f06070b011202031f0902090105101d06 61
    0x240c05240b407035482114000c1201c0010100d44d40c00000034480d8828400c004504810b661040d00c103103503010010316024005131049040106c140d070086469401030000070303040e4032407803047c68440080c40409401e81e07003510b0072000350840000400041e2800410300d03000620003821542c2c1d0320015200c003943c2c071a03804034402c2e491034081e5003000920f9500700000d10a542c401411040f428482c0b88200e100704110200c021740280d030b02a290707052100c554020710580c1c5407010000c41c004e01e4089902d4510341080c1c0045d01c41000c100341206400032081d468a17004040790b400751900f42c2a401d4040c1c51030380400c14040c10175603a4007125035510300601c228001050f00740c10354099606c00e810300e41d002d0a810745804d440ba40403007005216518110703040300c0e11998440c01a8411b60310f00350905044507a80c14040e41c0501070603240d040d2101e880c04030301c081c86161420001d82184180107115681205030403503070044c816031203002001504109c441031240c2d40030f10759000b1006e4120128106018040d40039 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 229350296 1250 229349046 229349063
    0x60e0c090913141e010516140405060c010b010305060d0f11010c140607110312040f0501060317030906010614071202070803070501091506050a03030810050a03210e011704020a03 78
    0x1d00c5603d1000c1024604400107030700b0100f0688490701040c4c200d4009940203040f20740281c0010803814000c482d21048510b01c0e410441c1400d580c0c1c0d01113a1594404031021f852070355034902c2c0030520340e010720900c1d40000f0241d030444180c00295580221300382c141040a04003056080c03801401d42e00c00e811500402e075008422040e4040002000355039200150340504c0032410142e0303541203a8200005540b2000e802008009141d2219210800f40c1200c05409640303654a9001c0400442c7c0c8000c030107010b005451f1621544e0346804480e090402c58180c00c0f1504224101c0703008511700c1c20000646440310340000c1e22003160151001c0507464429594004403003400041600300c1800b00c10741c48264030714043c5091001c120381007070b013410440d0b006014481d03201e01c40d42402e0012078416401355038031401040444103c0c0d900e410005101c0b88d810351084800901b50b0340d10806c0d40b03181ca0f000720000102c030f041040307080d0752403800a406003242d01452202c2140650025082d0341d6040301c1c0c5801141c000807038 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 229351546 1250 229350296 229350323
    0x20603190902040e0a15021812030c060f040311370c0611010b040903091505040e04081c06030b01050d210f02070806010b03040b06040902130f060e0c090913 69
    0x413681c5560b0300c0b00064400032800c2c8240c4804020900032203142d20440d0103091140781c0d00900f00440d03566800c8040404d40701c14402d03844d11040400003603016200040d08049240703003520b00245505141c0c04020056005039040251f0520802c49616144c480030010503841031000e05500310410030000050181c10212000113103807500811260700a0712800d00030722000d24041c0621054510445004000441240c000c118410a2042605401c4018276105141580d210361007403089006035804e60700d0384070008040110800982c80030342c20039120001442550302c0c54481c0700c1d00400c1442180c0c00b41c2c0c62030a4260030052181200d00c001101c10301c40c0d138420384920b44010000d000e03500c503039400740c403501c000401c00100001d0010b0480720b10446251a60743c6640d250f80350060051f101942094450301001d0040c1e4a400c00900b082001c45400a00c01603034240c2001901c20079449107070303e40010b10501c5003944116048555058003641c1120712600c1b039159007140412031120140c482074881b4031 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 229352796 1250 229351546 229351571
    0xe030a11010e0d050601050907020a0b0f0f0a0b130f0b033712030207060b090a05151009030602070305090a0902040810020f0702010c050f01060303090509070c02060319090204 77
    0x2810318102a81c07440000101c11091041401c0d01c094094900d911043c0100b2461510f0b444041d4410810300c181c84c418802a40c4100c8605400c0d90b0000c0c101001608101d0028100c405441c1d1112010303005100b030110820100e6492400c0c41c1501d606a900e0b040741c440080d1103174000010081025080740c9100c013452140e03100100301c012100c2c400c48500e207074010a0390381c0401c1d603a14080d044491505540f4540300d06030001d501401c82140c0c150740705e11408640d5600c455607039100d8003c8210105061404402c003000061440020901c03541090b24102c4041d50700c681c0b80c00c207580d4001001030b5190350078241568035005401d14940e01c900351071008100545140c01503c12560244211820300300b030580e0203403d0b80100449603589990520036074025600c240002c0c000d0754000c41c16101c0880e01d00342020300b0f5600300c0e04290042071420004201904286080d10f6000b0310f145070035a80c01d05141d00140c1e0317910000d0b00700d4400103800010050000815805607248550080c001c0100301d40e5a030 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 229354046 1250 229352796 229352813
    0xf15040b04030507080105010b0d0905070e07020309040b03060c1e0915041502010b01120c14030717060603100e0c090612040605060a03051c020a0606090b0a09020f0f0a0e030a 77
    0x4071144d000d50303440001c968005015043c1600c2c0c2c0d48220078102051002c00600400e0410000d0351240b08101c1c1c009102c044003a102401842e80d0b9010b0b5a030b55040e0404d01080c1c441d02403429000380d000000b000400700e00750003514450904c0c4104442c0b8440e1020702c0c40d0050140505003540032040180c94030007003c42e54020002c4802584036101115254103017a803c035031103041480d0114121a0101829882e03550000a0144103810800800c522190140d08560001c454036000b280340101c14507102c0d01c1c8100040d41c0904100c508618510340305004600d5104176204942c1c1030700800380071400c851000f80135285091005010940c40d00802180000d42d07000a84059800038500030101d009400e081010900f503903040303001011084101c040c440481d0007817201c40c0046001d801200c0340021094020400200407402c40451021400010420390661550003003a44074410000f07205109074500c01d907004035a07100f00094580c400d481e400d423180d011581a1380d52500840300314004002c0c651 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 229355296 1250 229354046 229354049
    0x1603020309150912031e21010618080a08090909281202010c0f05090312031914040c030f031b1b06020a080f031e0106081e060d020f15040b04 62
    0x8640e0201e0303413000c1c50903654076403007016159400d603c3d45110f9031010001803802014031844550040c400d601c1c0018003220030b400280c00c0b4400040604000364080da142040d0701020380b29003c00f80c403c04040e5921040d640c810b401446002d00f4034076001034280c0c2c0080c030800e04200c42c10380c14044008090054201450b036010403c40e0126150702040030b10713510512541d48050980d4032003800c1d07000241d000740c03140c0e0002240641e151094081c1c420680c05403501650003800014420720000180c0880142919940c18a000d4031084980400020940c4174402008994201542105607035160800316080189220440d0540800c002d014082008000f4000a0707155400114003605485e06012070300e400d5000e4003d005594140b005e4108271480d03d00440d002035031280041402c3d1001521505d41c054242d00a50102e1130010803c0600180c1c100d480101c518030001c183e0f0140b030310000107101c081c2e01200103400354621154030b4090361220307102090286032410029450380da035824240103c0d8450f = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 229356546 1250 229355296 229355299
    0x50307030e100e091b0f131701050609010b07210c02010f0509010c14100e0708010b0d0f030302070510020d1a030a03081918030806120d0516030203091509 68
    0x540c0441d100081c071882da19400343e40c00900c00d03000c0d83c64030f542207105920010b2100703449142c10080540b058074840000d1905100d01f0103552401440c013440c40760300420480c1102c100d64140ba00b003003c0359480c80070103419507505074042c50301d682081c141442c6450030000403500324055451016003403604080c1c2ca007102c9100342c0e903654080307402c003104584500648d40141e0100d603c1c60303c200005040846807212103c54901143c0c8149030000c8000251383c601c1e008680d440d086420b043c80001c80a0190340f045210613182102c1c01c2a06a4030744084558403c805003c144d03002c00c03503404001c0c0a12170300e80c00b045043c0096413113580035650030004242c10000c442c0c201200e240e00003c0e80c207011070320032402a003640740d0210703d80c0c82841e0baa000445d143d82200070640d4030700e0f80e5a0f80001e100d00005459019a88040061a10005108031003c4029100c000c543c0200710644805600500f1201e20710040c80d000c0200121900d01a490750282e411019800b9668800030381514078204003501081d0070 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 229357796 1250 229356546 229356559
    0x50304061b0206060d0f05060408071b0b0901080901150f060e121b03030f0403120801050315010b0f21090c12060103030804320c040204050306040b0c07050307030e 72
    0x758404001c4141e050800d2210141e000320001030725920b840c10381000080d01034900500020f0241c1d44d02d500f00350085504417022240031403082c05010550140c2c0003000349003540414401d061620700455800b03501c80e00360400500c040007a0501c0350a401045050000c210f440c110036031544500c001036182e601440001905085202e19076140089d643c00b0610719880184c102d0059800d5403d507500b04404003d6003520081010010b111121001071005500480700c2044429405800500801041c0c0c0154130980c401c0c0302007694130b003002030b8060440b43c0e042c4042e07135a03c0d0a010340c070755203001e1042c00c0425640760311420105c2510195019205624280903551004284800c2000040900342c403141170340d005900500c00a4010503429800a0180074000900c490011610500740c401040754201014041910202420100015021004100d038203500700f600f8100800d0751820000c10140800d00d442020540c8400a4801c607411290084103480ea6020207080c00b41c41c417410096540d00418 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 229359046 1250 229357796 229357811
    0xe010915230f06010e090a0b010806090402010206070e150c070806010b040b0d0b03030f04030f121d01030203041703041a0c09090106050a030f061d090105160c0c03021005030406 78
    0x3603080c03810011401c052071411058840d0312003041e040600410b071505224860040d10455510811103c2c8910105800404d00244800c0011300c0010040c0030179003d002e0100034800180e0f004100980d1000300c900d0100647d000543c009889010000b030140ca281600140604010102043c3c04060300c1502d01100c81c00e980c0c400e080020382c4528030500414410a008030000020b90740c21420ba036040c02006c50b400c3c1070b814046540c46600070b50003118280c031030841c45010829a6484001c1c40b5046003024038050101003488038140400329655410554000005800c0145d586038007619240030042182d140c0c9003038900039000041440c1058210f4023007030001902c2220b50030465168990152041a4a03481c111041d181d0341c01044a003003e140d1915018018043c040c4a0f2400500b04a0f080c0f600117001c18036010500400079001c0c400e01e034100000c1002d840103e482c0d2201d51f000c2464404920b01d03903030500c509000d03541c0c0c2009500c4140d0303103104803025a005c0051400b13280039003020042c40 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 229360296 1250 229359046 229359071
    0x30201080a18153614030f040f0608090c01020615060705030c0c0a0b0a0507061a0910151b020f1503010b031015020a020f061c090501060f06090b0d0e010915 69
    0x2048141501140345084114440003603030000c60300501e210041d040f2400c001e1120341810305a042303034004500b01d500810003000004d5118440302e0700050910040c00d480d9040c81c000035107540000702000c2101440265116551700d9030802c0f1201c2d141c0250940341c992034003804003601c9403800e1001d50301c03030185600046452810582110040c0c0c110303840701882c1092541d511009401603040c1114103000c0d402c03140d02e00703841f164045407051105100203046036050044482589082c034078a04108919142c00d60b4420040f4410000041d4049403240b645822801c00541000068a02402ca00c0004000014606440c0700994011000031044100c21902c0c0c8007031040100c840100340e001a800320780028098244600305400384500603092138a0040202d0300c1400009500e9590a521552030154805000080c41076401400010000f01c9806260502c000d01c111031901510441e03100005803004079249543c0600c1e0b40945880003408140640e00b010703008010303014001144541440b8041040 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 229361546 1250 229360296 229360361
    0x3100e0309030f19110a0b0703020c03010c03090c03060914030d1a01050703051605191b0b0f070602090f0405090a020103050703021312050a1a18010501030201080a1815 74
    0x10400d84c4010014220a0b42d02ea0402e0850861103c44d04502d6080011601d003050b1801058114004d80041010a02000c01e00d8211207080000c1c40425103004400000200141c00c10340c1181d130000408070b1441c0311404c201034545841c1d89840c903644800035420b00c11a0341c40d00004c1c40e801d9800014900e6419201c01035807c0d1090302c00040004608100c902000d0614070000002140a6003c9500301082c407422180c002007100c43c241d800800c540c904803540624280b614000c2c1c400d92443e1828075443c2c450400f81809004001090a5000701e180d00240d103c45050041c6041d00903c20b1000341032521006486594441003a80080d043c407000910580c0203000300e420511501400f90b100a1504480b0014030a50041c04c80c0d140c081c1e440140003007507811600d100001401c1350011201e00b4404c46840030410385c9012200c00c4e9051100410242c2e030460003190f8030019890300403880704510341a80381e5144008078014564000704038800c6515000364401d5010180240c400c0c2070544850700c58012 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 229362796 1250 229361546 229361563
    0xe0709050f130924060e010b190f0c0b0a020702010e040c080c0c1f0c0f0905060702010e0414010905060a08010e0606100221070c0b03070c1103100e0309030f 69
    0x20007405242e606448060154800f1078401d0150040c0d01403400b0440000c00614010043e090109480c1e00d01444038030b0b00e0702880c031300601910110f40d240c445650303240355036902d1900000d0b007441090b41c0c6107200710340280100e20007158400341d43c5003a440c00c500c00e00000d403c00c00b01a0700259002200070b8180c201442a0b0b0000005901d88502a41d9030004d9080c455008a61024140c00f034902080c05400914910242000c1001c50101d000d0440f0b0000400b81054102032030700b040483c580401c010345500d41160401a02860000e01069498000c5401341c00b00124000601407010000a04082d40d070b070003680104022203c42d07068a03510000c45003603c61722006c00020b0740000000c551145803624002801140c01d0054503180040801d1008401119884126160000184503000c111080d1a8840a8015084480c1c00e40c182000f005018014805000f880a60451b420510f9503408010188080614000a02440f4015000c0a40300c2d000701e040e15010f48a030540f020406280811603da = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 229364046 1250 229362796 229362799
    0xa11160f0b0918090a140633040b120a03021501053708060106080103030906050f07020409020f0a030f060b0406150c06060f09020304051b0d06021c02040e0709050f 72
    0x100b040d603c0c2c012148001c94060028112882540902e100165500042e115846001805071000340340c02003000110200509100d20444407003500481c1c42da04920134090340d0750b8191400690b04c0201008168040303400d40c00b0380024401d1581d408201a4005038110b60b44d2000c1c609200310340d903180141701c03205110b4401c601300380c0e4190044e8045000d40000004102e403541d02f40c04810b0b42c1e620000d9003068400c0c1c01c03540c0000c494400520a06030026603017001840c032403170903034580b919030060101071b130081130ba000344240d840305402000c1d50348688101c101c07550020013195946a8a04e00405a151618011070341700d41814034662140c50203202d0709040f40e40240141c541c005140d481180e01ca0b50200d01151241c0e0799007804030b08032181c0c5400c10060141c80e00c00507074030b0030b06d41030061a00340c0e5500c1c240040014030502c0443c82d00c03907610080e8801d41c000300240c2c40c0d445407820417443c0080000002c0000f480801d00040c0307200f16440c418010a241c0d1520420180c44a0a1080ca9998480b005 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 229365296 1250 229364046 229364059
    0x1f02040501020a11040609150614030112080309100e0a020301110a020c130e060705090316050a060c03050c061e07050703080c03040602091305150105030f04080a11160f0b09 76
    0x1004503000d640d000304c181000400021b500c50300d400346001200c02040309440300d10752165040c4039454001c20710701c0c982d010f0f141d0b070141103600d40210030811001c03040b402801c00344080302089000c0c07410030843e03902d102e918005000102c0443c02c0156241c5c03062038143d01c29800d05004001c11000c0c1030460710f0040956000d0080c2c1101c0c5001d20852082c06000003440c1070b0b0711000c0d10383d04a400d00c140d9000b41015501d450ba260000f008051509002500d43c80c01014805001c0205640320701c0c031002180e0282c1025010340c03405040c150f49a025070300c4204410b004ea00100100c01101c1c4088119a007010b0400c0061a11a41c0045a440c054240002c002c81c51950110341c8400f210700245500911a440151500a030b000106110382414040700d0505501d643c14030610ba07146040c609403030802803038420b05600e4018030b40d28000c80c000d0400fa141d6000080c00559041c842d5014041e0b0389541801c5030007140c03601c021040105010700c600c1d50900908500440d549418a08940450701d008092 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 229366546 1250 229365296 229365313
    0x105041b23010f0203070b0109020d06090203100618170304030c080715031a1e1309051e01110705030c16081b0a0f0e01081b130b010207030803091f0204050102 70
    0x56071805010f0f402d0300194030040c0030103000070343c81c41e1001d8080c00c8140c1002d41c48501c010441c0c0240c030000c9d00400440303401481040005c036800200c400440750795144c04040c00400c80800c0701420902d42241c1c034411140d0b100034414020020051085074411203041c400c1a47d03c3c0c2110f900d42415004514101c034030326040d841038510a0300801040300340d10444000c2d00c1c144900144c413607205142002068819095051034610b02001010642034403904140300c03030325055a031652140b1101e8815812000406108002e8042c2548011980040106074540d110340c41d081c202d03600c0c0c11075444004180328850302040030030030f40030201e0200d078484001800c00454100c40c020190901c10340840c0c1103a06000d0019045641180317040080c45c40c420f0080d81c55040c140224101008142ca03000c54464a45541150303440f80040b240c50545a103034001820405900100d0070b00881c1d503c060101300c80481072100e5802d000c2102d2015001c2866001407190154100074160301a0740300d00d0780540c00c4100c2 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 229367796 1250 229366546 229366549
    0xa030305070c090c0f030b0105091305100b030f101d010e091002030a0b040501050402040515070c08060a050601020c01020606090106030209030709020a050c1504020a0501050903030c0105041b23 85
    0x340071024442c0c0d0b40580501e0b103c0d0720381c4086510b03130b01d4443d001442c5451401c81454151140100088084c81c02c14500300b0407802080c0742c010850400640d59503140f00003200790f80100120800b5120040c1d1a41c0d0f40e0900344c201d110000400c1d05c48103c400440c0000203410301c2c080c114040d00d00d800800030300d5680e191820300d2907605001802c460031070140355441c020002e82440214450703103408200142280c003500912084a00503006107001d144100800c0c41a50350f01e04c044400301c058540c1c80c950b07845041c0f408042d40d00442c3d100801510422082c09408007d5401880c8640c500b0380c215105d5680300001243d8942040c0c03282d9402c140e4110050090510940040ca070480b805012201419a01c4d41508120ba00001003500001e0000c110390b40d414400388080b0059083c07051801d03007241425000541c94888500c140c5050010000b00011142c905000b9a1054203d00008110920703060406180646034160090b100224a140c00300303c070ac40a004640305140c10030041d800e00c00c00e220 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 229369046 1250 229367796 229367807
    0x1106070e01050918181605060d0902010c0b040c051005031612060e0f04420902060c16080d1e02030f13060216150309110301020403050304031a060a0303 67
    0x2405600003c21112000401180c0f102c101d016682c051580b00c00089884003550428010f001b0000400105d00420446962a8016584003d4100c4030000d0f40038060b1005079101e000c1c0c82c000910000080080000303004407681c28404880c0161404800c00c60701100031a0144022288001810f03d014064244c1911a0400401c10440308200240c4562503401c0f80c890610308640d1115000003440420040208103c1d25170081c4070101c2d004000c8240d40c02100c24045411101c604401c071191403054001e0300180c1251b0412a00506155a0703015000016511403103000c0d0f101c1c2010f4600540082c00c0403002486000422140e95041801c0c01400c12400b120841c460007803003144024068038403121b5a510040421030307481d00c20007a00510b084000703410007540025444901d1076402c0100540f11a08d568402c8501c0e1501d0001048001440c01c00381945940800356010361001c103020042110010040c01524041c2e251464148aa26181484038104951180d045800030700200006800350 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 229370296 1250 229369046 229369057
    0x4060210050a0b030f0105101d1602160909031d010e0d05070312050d1401030c1509080d030207170c030901050d09120306050f011403160201060e0709061106070e0105 73
    0x2400c1c040f41101915000a2408005e0101444d030380c2d5540050150f50740306000e49500900018013403040c00f00c1c0480f101d1080c080b006049211a0511410445e4200d20038071a0b1351303010007030703242c0a01070740c1d2201e0041c1c000709003400046000c034002c07103503596808104040120b0710381b038165150710140d9500c80900c07000504186048035540700b02c0401200061428408000007401c560b19a03846074403140101e4244c4565000031800411200010300105000b104000d06903411030284582d0758000314001ca54484695105420741e00811400100081d4143c00a11416004003401c0703a141440340764480c9140b00e00ba454051580c02001180074550141e000391590700c180b40000604101d654560340000d80c031812402c000240d03145001d100b2031400c28010b1512034020b2814518820440c11455002c0c407014006102c0e01480b0a09400f0340c510075040300f4040d2803008101c80481c10060b2002c0c002401902940f0003090011158240c403640014145110390040c1d030394101c400d54000c006440c5075000 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 229371546 1250 229370296 229370311
    0x18011511031c061a120c0c030702010509010c0506100f050f0f010809070315050f09061501141b0f1c0f0503040804050909070501110a020109050907050c070f03170406021005 76
    0x1a90400140000145484224204c51629680c0d8800c08072102200d180d100500700c142d5110b00344940d507a03014000007501c03003443d4282042580c42043d003006076040a00306a00602c40c0c481c8508003e40c2c0480125070400700d60204c010540291780b03540400c1141d51601d0302c1550403542038582c00d05c5031340c0f003103200700d4200d92180c0642d031451344c42e5190100b4100000b08d502d9030f80c2e6211024080b1504c16800b03405d92005400003e00000e0410101c550101d0000c0842141001408034a043d1242502c40481ea0303100c019001083c1140c120a0441d9114025007907c0d2000d40185076036101010b04048801202c8085030380c1c2c4d060803c159001c10340c0c0640001e041a110306006101c04500c68071041c248600404a802c003d00903103241c03c00040c10245010131402c11900719007101e40051743c0100c115401d452044036407106985e5032000465950040c4408802144125034000400c1e2041c40c2800381500d0042400f03010441d20503201e80d00f42d01c00c601c150801607020b0401541d80420507401507410104 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 229372796 1250 229371546 229371551
    0x70e0f030f030702190803180102070e010e0a0b0102120a020604120504060207030605131a060301240501050c0f03190f0201050c16020a03020312041418010506130518011511031c 78
    0x11112204c900d035402910701401c103000d554110060a68040000d48020401510390cc0300320342c100390843c02103010140802d200b481c0c0381d03269083c840c0e0090010190310340001c0d902030b0325043c10000c001d69030742085e201611403240c0018000e1840340b140c030441e01074030399a0b0000c2140e0380c507594a81c1e008000003800c2806840001030b0503070000b40b080316007400d601134030b101c407129030b0030503004060031111807150301c0c44079a000c200c2c0d01030b68034240306c0800c0c115102400c119459621600150341081700030480808980030000d5a241d12804104440e800a540c0340d0300e00c0080310790144142d08844081e58a010040c50910200710740c4802d900440c90f000344045d054410841e52540801e20700400c141150540070070100d4207114103d02c1004100810b0300c1103c0040c0c268120810b404c00740401805141c1c01400000381045428001c211220010000034004080d540e2155183c0010305500703000b8901c0d580610551400305c1445200414108001c40001d1480c1c4030303009041c401031408039154001170300d8 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 229374046 1250 229372796 229372799
    0x3060807090c03050f0403021b04020904020403060e06070c030207050d020d050105070819110f090a0b162a05090907090501080303090c06041406070807060203070e0f030f03070219 79
    0x10301014000386001d040201c0c1c549141c05000d42543e00041002000c4c4540c0340c01c000c08070ba4000780d913481000c2664060035400794000d000c40d0103403050600041c0c210340005000001c01003a60700c2041c0c0c0c48149019130300d087d11516011201300350300c6803000e4010380c0201400d105514064000701115440148802d40801c1c003907a4007030a40308200d560b940410045c0702002103a980808002e84c100002e440104401c01d9094049a0301340204001c0b203645000115034410140c40d0581c0040260401c007070340c203803117081141400b001c0c1c010220b130407648030f0f00d584a030004074228070303050900c1031605010310501f01e4200028007000ea41c00400401d080c0c82801400035071035a05d489818003038242c00d80035654a24050351901d2400e00f44081e098007a0380100800c12002400d461149900141122041d039034440034108010503000d4541c000d8002440002400032480d0081c00304890400d080d2025040086010105502c8944204900c840c542042000b04010304d007483d40c1380401c0369005210740c60036 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 229375296 1250 229374046 229374059
    0x30b1f030f0c0801060605040e1f120b06150f1801270f0f030309090506211e03030115030902030a050604032c01050403080c010603080d29030a0201050a0306 69
    0x450a80005603881c400a01c42480b00364001c4c05804081c00d080d01f401490305150060070088904000c1c0310a100c0503031320a4803a1107040c15240000180510b41d120398103403c450406440c0808252203803441541c0d8283e28404021400341500d410640014065080000302182d03005641006807044c1c2c100074043d00751490801c3c101c0d02c0d05d01011800c80c0700a1b0312034103100d202c000024150300700701e80c900280c02080000039401640d00042c0c580c1c00501042a85811011507040900c1c030824107501e00c07201c120251310b02c070001000407004d02d903410482159000000001d480340b100303001d11010700251418499016010f40c01800d5150303c09400c030b4903d500c5548600d81810001c2d40e0403400a084030026001c00c80f6442504070660710004199000303407444c040068514462440000c05a55000c10002900e410a510107002150440d03a0307070fa591441c1d4a80480186a065408180d076003000c4c21040c040b1805200050901c40c0250040041985540040d00d890b00001d240c6c0701010f441e8200400da0 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 229376546 1250 229375296 229375313
    0x3060f06080628080106080a020604030212160306141015050912010203070507021504210203160b090411030408030705070212010c080a0c0219170909090d0306060801030b1f03 77
    0x4807820f0a000c0c5041c00c100c04582519941d901c0411251300010703194000d42d0303810b411101103ea0484106c0020b0880165007070400780100d0f5550000d00026400005000c2c1d0380d0813505e107264050710b01c403005a503001c81e1505130440d140a6220f2103c50303151b5501030640a0310080959150081400038140c03500c2d0302a601b60303442214560002140456244110b003000c0c01d200301d220104090603410503081c00c2218110345044100801d800c55100032603c159101032009041030300d2981203803d43c45803506400c510544c014143e45000341e02e040c410b4a500000d12064900030f079031100e08540740d5210b055003111150080101643c1c08a0300341c0f52000304100c24800c01c01c0a000b1511299881c0c50101e04000461310f00c402c030f441c203540044198213801d07525002c2d07084407268409200c1200317278074a0528103828091507495641010144007031201c1c02c4d01c0041d511848065503603040c4400d80d2200c03800c44040a0a11008204d403401e180840d40801c03c0710500f041c180780c420b5a95070f07203980c0c2e038403035511 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 229377796 1250 229376546 229376599
    0x60a030c18060b1801050a05070221070902040303090e1008060f010317030105030d0804030302160311061015030c020c1c050705060301180506030a0b090d020d03060f060806 76
    0x201518a1180c00c1e6074155902481004041c403900450402c140207501880342410039000310b040010016418a41c60300030380684140d15005409840350101c410b1080c9000145000140d8580c4201000020360079018001c580a480d4503a0b070b010141880e103854043c00100c0a04900480c03a000c990219002504100f0f8510550441046a00039407450401c3d411481131100c1c048080c210410050010703840000d03406003800071510340341803c1d54590400320000c3c0a40c200110b030315420000c0700c0051540c0044641c000708800010744050361100e50168105500b14420f00340c0e8499404061540c01d8000d030b006851600407030041e02c8c400b1040300c00003242410f01507480c4012282d400f401c2c0c030601c2410844540070740410340303a151855041090480304e00395615004998241c49100148640d00c0a000d14840d15600504040883c10b1041055071168521211480148540140b60054511900a0354205c48020f00300c4d841460402004844542c00100385a8001e01d00d414002c1c00890345c003c4400 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 229379046 1250 229377796 229377809
    0x2a041e05040920150901050d0b04020310051807081801020705070b071a04020109210206040902070b07020705090601080a1d100e011401090b0d06020c03040303030b0306090a0b060a030c 81
    0x1084054803182548246000f01814021200d14a10200c130382121340842d44900d60900b099a220f4203600404405012007107211a0458004018800454800203411041d40ea00320f41d107800705850003c560b00c100f03a0440b00003000504c004c01088803000d0b441c40d8600e01c5400000054500b03055903d41c0d0b0301c0c113100c1d81e0118040444c001081d40901c0440a98480c4c3d592128940040303d09164000804407143d50154011604500c0c12000000c1c1c40d10b10030084640e40504019103036a501c0e0034410003504098010b42d0318400c00b500154003a4408500d54007036910041000c45644c0b50078004494040004000000640d81c0715603244c0c54081c0c40c0031804c0b980d48120001c000d150111031000f019111815036080c03840e070500c4041d4480e0304160340000c1c1900c04801000131441e9160000404400f4103180182c980b134400074507600140000b00003482540e0082c0c83c1030280d4544c0005259960000b15840040703038111550007800503010101054000100030300700b9070413540b203032184014503d00d58043c1 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 229380296 1250 229379046 229379063
    0xc0e040206271302030921070b0c0915040803030a020310032003100b0d11010509091f0b0a0c060c09081e07060503100b0d11122a041e050409 62
    0xc0c046850140603610007002c43d84010744c11814800c46a50340c1d1117003882c008051203040003041c0400c5c11418240c0c1d20903a001020b40c9a907051003050b0380540e90040c40c0040c091b03e5464410300c2c80c0354102d001c882c02c4441c0c42c8029480c580e1a0f4207000000d4002400003c0e0403105c0e50400000315040110307800745690b580380c0c502d0030341b1040c0c000c1503d03181440368210105800c180000c400b9580b00c0b5600624250010026508007c1610048030248a1180310980c02540b040070701c5a03910b6900708010000003588000103000341c07200b142040f140146c820140004011a0001001582d10381142d81380705818200640702a0315901541e0419201c000d084503103982d074036031083e20203408100480062a00c0d003030940c0342d0b0800350480d2140542c0750007040c1c900840040c5007802841213502610746c035100700203515140c4419068401800320140c1d080500d40f801d00d941f61700404020004060607260000145260500e4040e080c129504c00b404012414500a04001020348403402440406407084180 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 229381546 1250 229380296 229380367
    0xa0303050c0609060603070b030a1506020703031101090f0201050d090605010b0a0e090705071b0906060e032a220914071508360705010212070c0e040206 67
    0x72145442c10060618400c0d5119074180969502c012505005171030721f68410950381e66401940201a1030b5030000d480c1500e2001100103191170b40425810290303803181d0b594070320750070090010500741c1d480c1e210060301000200b08888015070081c00100444000042c02103204a600d8403203900b103490991100410040c00990130401d03035800443d450070440200ca0300c140c2e50510650080840c060a14020b00010610b2403160030424881011402440740c0c0c0405d016858813144010a41000181e49078000d10030340008000702880c0c84078181418840c034903441002e03c240e03010445c021003181c0c5140480100d42641803001111405050300f50750090705404101c091140c110792910051f903000c0740007010034052245006500c00d22454100c02c0c458041d100c46043d6482403483c81c0005260503001035003140d4020700c0ae440200b812400ca0b0b000340c082c4c42c21004040038203059445081c0740141810380007403040c00079804408942d82c000d40090000b03414000030300398100d00201ca00c44990f4001c80c40d07165 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 229382796 1250 229381546 229381567
    0x42d08250606081f140a0b190311040e01020c1c0c02031207020f0603090a030c1703100906050f0f0d051e010e1e0a020d0201050d0c080907050a080a08070305090a030305 74
    0xf4012070700c00c044904116103044d15074100c41e00036001e0321b200078035602d0742e481c11401c3d80c50302c400c900754094903417640c00c6480e03030b030701d02440205005030741e260060b410100c4a8109103410310a9800c251200ca000d4400e441d90399059200700c540252500c030038030480401d9000582c40411048503540c15071107441d0743c0c60f134090040007000d0092640562164104208100040d0004078540681e2989030500e008641000d240403240762103900000c0c03d1203e408010844890031014140d022540018400c005468030b50040c0300541444243c003a8200c1c150140300310182c201040c01e850f503240103c0c10340e00709084804500c0303d00081044031482c141c2d1200141440a20b05101000344445a0545c030f204a0b2480c818041d2950580f40000c2e01c03c8030310b01c1c50241564020021070700091501a402c2101843e0807402400494060350103840900c6403120210f55030400b51200003e50701c01030002c008a40b201c7c0d8801c1c5441d401110708808101041c040c03250300351240c000ca42d000d0b43c03198a4042c1c0703803800400b = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 229384046 1250 229382796 229382833
    0x102040f0f0b160b100e0f0601180f18060e091b030d08010e0a060305010221090c28030f080c190c05040b06070209042d0825060608 58
    0x8004030005402008400790703c258651502486a07030150b814a11903a4010281d0001942ca51200f40c04980201c01c0101c040c0040082034840c0b08262a40780e065031002546070f0031074080e07000e01110001c005c0707818040c85108152031900559040300c02300d109525441c1089440d8402d039a42040b03a0f02140702001c070500290074207000144194010031b0174071a1400d005000308818031035401d81c5c0300500b0118940361055003080c4080c6401c07000030740d615141002515150841080452500050600800c07010340c030100320744041c4030b0000c29080c1c244241403050303408440d0222442d40580f94210340000020158002000d50034000e5030f504e81c89129010940307041c405480600840b0b4544588030100244401e001803003a02e00680d4001001c40024020500900c681342019612025240410042005103100201d0542080181c0c1c6024112114500c0720440482402011900188100c190040c2404400c055801181402003085003682d00e40204494468125501a0300003c0c4038060510100 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 229385296 1250 229384046 229384049
    0x705010f0201050c03010306020a0e040507200c06070b090a0f050a1101030e07140d0213050402040c08041203052508011403030405090a0207020105070c060206010608060d120f03020c0102040f0f 85
    0x1d000034401c80c0b03440040300c41c1e517100c14040104095404500b0594aa03c0742c034000140351030242080009050a100241c010341c14001c0340c1c2c200c0020795a070002a200702040c00004008080c0050307041c41240d996032040354000074205100d5114a41c030000225080088044505002d28043c0610f01c005040910f52480d40e00c244906041c03c201c0c9040041c000081c501e4121000c4004031094120540c00148400742c982001a5000c1030540302c800d1540b4003a804140503500c01c0f0740402c800c155076481901d007240c003100c01429040e820100c0c95011070080d00600c0d400f12040e0001016003030107100b40302544401075402c2e0009955200140954110b625500300e441d04220025070400345031000052504900421015146401103100c608690060041c0d0325996801440301c11403544681000b542d81409116990003c0c00c03540c00724003541400310a0342007460700140c020110090f401000d45030340780402141e804055003000b0181c070444083c4041d001401d505c00d1403104451924110180d1030001c3d = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 229386546 1250 229385296 229385327
    0xa120f050106201204060e18060603011a040e0f07020706021c230c0f06070e06030402010e1503010f0e060307080c1005040302040c030204090f09080d0b030a060e070501 74
    0x40c4401404466040800c0c01d4103540c420b01100c401d000d60512003401e0090040c02d48036a00c401080115900740c01c48114495840c050b10710912844940007825803044094074900d41140302000144400060001d09004444803051160300c1c01d40d0f1903418881e0300d03004558803072170881340505100a071a410b0041d40e000302100e2006107001c201c10706401c0d096407001816801800300f09840240000c2c40c0348040a14591415145610780b4071001d4a20744070020b0b48503e4105001302000107250701d011b040d00303001004018203101e0950f5611f0b4015120b40320000c801c2d40c0c0c1300074820700d84044030108800460282c090604514000b0b46814413046c03000c3d00142c4027900c2904075003018001c86000040c120803501f0125084c4030304051004040c2d5580c443c43d04042d400ca800c110b501aa000d425400800072515101001c00c00e0740c0307244100404072078507554014032103201080741071041e64482d000203003d8000181510000f4038166290b0044940402c10300c191508501020406903804c0b44100c0794007000c = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 229387796 1250 229386546 229386551
    0x60f01090b2409041803260412030207030c14010b0102010e03030f041b1d0708010512060c0918180f0a0c06050f0f0a031b050a0503040f020409080a120f 67
    0x50b1040c108400c1826545031030740741080860b22010581d501d0700718807202405a41003d80c45c040c0e90400074240c0b0910304604040070706103600e001d0041d01c03080c5003e01c520740020002e0000c155070345040300070b5400400d0640130003121440240c081105980f0209a03140c411000090a8004000180c01d4410401240b0b4158200340200032a1040900c00c0c2036104e80c3c040c60303c8001d010b441921450031003080d0032000b4426410a440c3c0e41c1d00110f9100c050140d0010b84600c20381e6030380c940810044005503030425401d07400c035202244a095005000e442e843c00300500c00c040d50b1850340301da0455250111685038584842c00032a990070b082c1030052180801c0b451020380b014107426140c4c410b081c905880780e00e00f08900018a0301020003510b05a0303100e0718036401010381e2208420402070180000c002c0c2c222556144141d1092000c0c0100122074610303406071502801d541e00c6484060394400184400e82c0c01907110398984000420000041030090030b140c45203411011040f0070403041741c3e00c40428112040c0b = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 229389046 1250 229387796 229387819
    0x60d0c0f050909060d03030e060901050106090b031e06010e03010906020409050709120323071209081f0905010612031206050d02210115060507060509070e1602030c060f01090b 77
    0x110b83c07540c0c466101d02e058850380b00b4402e651504800800980007100241e00504c01404091360042d0015030480c0d100c1d51b601080c007a1901d08500359803005403040441e81400222185a0b001750700401540b200d0141010b05040f808140440c0c2501c4e001ea80c1280e48070b83c0000c1c280200c0e1031900c140d9410103c3c40c50700400e2503041801c0c44110406956010342407280d05a40c1030303030078600400e00d001205102d050706502c03902d55180040b094016803c148000c210840c80c08100b20a0004d18040308800e540004041c03c0d500212403001070000c15800c0e2001d540f100808a041c60042c60001803041c40380d03681510b61450040c40000300c940c140c1110f8032850980101c0c03005640c038800010700100b12640b05603080c50081740224010030025402080e4014501000103c050700300c4046e000841c0100c2d002d0090b651064101a158900c9001d440b01d0782184d0f00100e021548034030346051803015940110391a050102d0310007407501d803040b00ca0382288012440140298107440c010341e14031103030039101074074580d = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 229390296 1250 229389046 229389049
    0x2010b2713170c010603080706020a021b091303140f090102100b060909070c120201270c06080709211707030e010e06270103150609050d060605060d0c0f0509 69
    0xe05004407900d031038440840c0081d0f92041c01c0d449000110360044846030f41c1c174800d2070040301941041c0c1d241c1015000c1c0c4c00ba00f280000342c0300440700185500400303190780c980d82c1c010385203610128041c0c283e0801540c030211855030200c1074014141d0802c1000c110740c841c41110002854035a90001c1106400e0828107082c100d6200c00041c3c441e1030b10304656920300b0b0b6551200071142907a1000c00a003981c2c1440a80d1180240c0642c07008000a401c401e01510810741000042d080c4060b03404010720300350101c00200035641c401c0600c1a0000c0c2a403814089181c0d813410303540840d43c41c0401305120050840305040070070101109510590117640cac1558200300362070310050541510741c1e2045041c4206400e060781c490381c50030100e50000c858901001d032000d01990402c04002d032004011030210380f41001d03503501040b00d2104001110619914041202d0510f4140030220b40e4015046903400c2c1c4841000c5495540c50000d0284040018000280204800001007010303001030803031008d002007003216035401d = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 229391546 1250 229390296 229390313
    0xf0c060a320f07050d0c0909050a270201031112010501021c0f08040212010f05060f0306010e010306090614040515010f0b0f0c0f06131b1404090302010b2713 69
    0x300c0d803920216203003640da009040d504c9125402e4020400c601d00101c4002d6030750410350303600549040e00010420740d540d00e082441251184000780021003100a44024408955402521030600c18075002c101042c0070060242a5000941d050000010040050049590420014000501403031210484a4043e080036082605905600307007003044000c00541507440d0f442441941803004802040700d107440d1681080105000d40e0501d10880d01700413803488616002aa5078141c80c120305c0803840c0c40e442e6648a50062007100740484044d9100c10000550030400c6844922070303401179018100f10f40700300c9041403818005821140041c00f0318101402140005420ba030318450103250013950350343c3c00c290760300c0c40c00200f04904801440369a0402914108542e9241881c500ca04820780d0444189048140c241000740600d40c4802070491000e1401e1510740c108250903402400009805030b100d03070208600d13040e07000040c0a0719035409008105800c00e04c6250790712031110000d510100240303544d8480c0 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 229392796 1250 229391546 229391551
    0x90906010c020a050928060302030d180e0f010302100305250c0c080d090f060807080604090f1101021b1003090312050a0c0e030a02010909020f0c060a32 67
    0x1007100d41d2031500215216100c050b406403500170000c1c4d050340740901c03960080c09454045c0002c0c2c01c0c01c0c441429000421409040e00f40ca03401009001d250807001811280c5090901542c1003c002700ca00008203424400241d17800344810104c94a82c9604500501090124800342c003030405241600f0407002c00e0719000310410352800c0b10b00c010140c440400d000c0b289e1076884a00036082060382080021421000507540d048448291903006003c0da5944102c0c5200035070f8030a440209046400084a9a21032240a80c0c0004002c000044c0c01c0480c0d222014031403100e0404070351208100d00040d0301c3e5a0100310300d080481c030401145c1504a51080450310340850140302100307060325000600308042c003550003200801c43c0c0407001c210502d08400c08402401c4c1100b1a000407840704480e000a90401140140000b901a1640c0ba4103d10704501600298414240310f800224103004415005d18103000d01307402140303400c401054645152525480862640499113088000d03101d0310b05c0f1099000c00c00d160f = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 229394046 1250 229392796 229392799
    0x20f180a050910020408010b030c0108011a0906160516080f120c0717060f01090203090c130f0f090213020903060f220803070906050405030a1142090906 67
    0x20540c680021052500c1d8503c0315034060303c1d00208020442d004154000d20001400324201c45495a66900640b1910310138000e000b078050021041d03c1c0c1081800004040c1e030300c409000b1501d0f041d01000855210680640100c40c1600b19100b41e4111503603025500c0b02074000e081c003401e00048400c044580d20550300326076030340d140c0380811400840d81c818405503000342060400504051340103000107440701c2c03080307030001e500450040010442d10550301c00e4a10609071070004013035100555082204660106a2103101c080e102d05034250a40b8560160345610304002d0000720f1552200c0c41041074112810305130041c0c03140305204100781c1d03550009a183c0c0bc415410355503901074965001065844800d4482041c07070200b0000e031802080300c030300c00861180302c10759180c41c240c2e611440704072000d11842c072800da4107130f02102e05140401c445e1600c1e0701c49c401008120034090130b040c200406c403140705042740d04240305c0888986003020350002030382c14189407d04d04140c60b040c14140011700380300b03014060a = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 229395296 1250 229394046 229394051
    0x40807120804050409210203040303081305281a040201050306091012080a0f0215071413060c02150307090927050106051e09041205070c060203030103020f180a 70
    0x280240281c1d142110050000a131052054100d2401d007100c82d460781e1007044405094005d41001035502c0407007a1800d0300e51550360651036440b0b80350003040316807004000740c2c1c0900607221604a0146002c41c008041200c2e9680c1a41032070b01801c117044601129203074291400030f081c04110050707034010100c0b94004021a51310030503885190500d118080c00350441c0e8102508903c4400034007949101403d0440c1c215540c0d00c551000e170381000c0780c03101c2100207102446081c44022552040c09444e00700d00340000d101c0b40c01d040c0143c851020814010b503a1000c00468502e480d180154200082c3c034195000071400040d00d9414487e1000b800010941700e580500307588c03100745644032030f10301040f0441416000b40044569a260501500030401880b030a889030103581c00340b05a503600c0f14156804142c004041c40c0b800d5031251558034000c00102247c0d801c01508008490018000360050b1010304141d80c0299165815403051006400a040305a8401d00700b05404018030046081895444241d001c0017 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 229396546 1250 229395296 229395329
    0x9110901050a11010218040b0d0309090b13240602030301180b010504030506180712051c0207050a09020c0105060609100f0e0607052b1205040c030204021801090902040807 75
    0x1210f03008107100a010080d4000200141c415860f00c0705120420012501041500b00850402071b203521480c80c01000709007031040030001c5c0b6030558400c0f030849801801c03845206e806903100808a40807058410604031030b6000c1520991400715146c800340001e40000d40c41c55040c00946050101c3d01a0300010a07520703024000400e901c2401034400855002c1c0c12140326040002010200074444415104984180ba600081025603400618503c5e0b400101400604c074140c44038403c2582451018800d510030070f10009201c1e268100d085004105844005848401c403210321070a580300585071a215400500119805650386510006608e242d0304102e0800c001da52400d070340b00e554074076032242d0084021034100144640415800d0098141c40003c4103440b10344156508004040312141d400210000070500d07003520b141d444590458001c20032852829920350001c0c0580c0d00180300b40c1521000d651084859580150140e0041c5c403042c0420750805080a00c2c0035511207891049404140c1101300 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 229397796 1250 229396546 229396567
    0x7030b041127060f03010c0c1104180f050c01140a080a0b030601151202040b12130602070807030315030203030d02090d0c060201090c1712030a0e160f0911090105 71
    0x1c00500c07240e182d2203402d0000c2040002c0c0d001500121000342c0101800140100c452a0600c42c600c4001c0c1036450f00c3e55000c0050b11350245d003065039040d6542040c0d0f5070616035480c0d84401c94031070007580300300e031544070802291030705500f05601840c0d00b41c140f141c0c1d00b002604059040095462030a52031500b4400380e82e540a10f00c2c0134180724612a17400d80140000030801e1414421044c5044206468599403d66003211400c00c80c81741c1e106418001c4824401000362a80c200c500d01e80103001200307998622100d684800c0700f00c0c0c2c0146003c44412600003006410075400d070007071820a1501522111341c880ca540c01003034482c859a40141d01440c2e001443c90041d984200b83d881c442c0c1e8000b0900c0340380c662900406030080170070301e0050740c1c040e8200400181c8000c4100a1004030080328010380021500455071181640010302240b4020342c8507214620801c40c20041800c1c1c24541c903c1140340249028030b410101091a04000051410000b0455401120b40d04440701c0301400c0c41d056664240282 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 229399046 1250 229397796 229397809
    0x30d03022811070e1b070206120708060f0603041a0a1e1a030a0f060c0507060212010302040605010309030203120903040509070f030f020913050a0209040f09120207030b0411 76
    0x900405150074000d00c804619805002c550554804404892941d5152940000480f41c00c4848201c0e092100c54404100300d0301c10040c000c0e0504c058081e0741014940d240c000c1541c4401c5504c3c0001441d59020009280703000a0385050315081610020b1075030a2907106d40c45000e0004504c80c03010603403075000c41c607041030a81c071002c0f841281001640700104444021400b130800d00021001c41e643c10707c000e000c0c2c0d14003c50340b04201540a94210010704069545a000d080700d813541d1014008284124008100c2c41e00040103045031840c142e0010350b056204004c00c80e082034002d581010b181040f1031000a03000011038058000807041140590b4520490b9481d61086400c51908982000144041c680e0803003008400c0e450075032024402c03c880c2d1405030303080b0700810420300d500c551400d1041c0c80d640b01030361156800a00e1024090301e03044100c130100e000c0d9200c2c00030046205a58880716030504c18080441c0d0420a4503202802c5050f145072070700001918090005071052003e0700d441c9400d5951403 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 229400296 1250 229399046 229399087
    0x11215050301020a020f0105090d020a0f08040f0b0d050f0106090b1b031b0613200a08010c050706050a0b0603040b070302091009030311151506041d01060914030d0302 73
    0x4000f03540e900d000c110300a4541c0c24413000200550708040c0400c040e860049034698405007280e006116401d542d891305041316840340c000361860001044003003007102303090b0154000f900548035515a05d1803c4100d040890704010a5050081240d20040c4000355000001c1c40444100405075921810352034043e0345400c080e03d08450343c92200040440d03064020340d5000004507031250a80d1070981d2161880100310b002800700401c510280101c3c9902480c0d02030800507484e030701802d05024943c6801c48542140e940f1030142000c0b0318080741100070000d05008850b4010341d0f200741030100f0720662001c00d1080c040544020f0641b0601030000340540d200340d05407400164000d02e040000f00c48264068010501400309600043c0714000180404000144011143c0c06851004545540d8038803103952082424000d113512500400c000030340f218417500c0303510081255090490065141c8500036001c401c1507071100b40b08541c2c0c070700400855034012440c0044000030303040c05aa100042030f05024011340c0d0 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 229401546 1250 229400296 229400299
    0x7140609061603080405060702010626011e061502010612030e180c040e01060e010c060b010908030c03031f0b070b10030f0506090d03090209010302270108060610080601121505 77
    0x81c40b403400140b6074030988850181d8001c2c0240d070095191000120f0985041c1c0c041d40381108145404510060b04111101a4100070100001800c031101c0901051500700e0040e11142c1da900d8810500042003465044004110f140c00204201c41c0350021141041c0c1c07080700c010b014000019110390039074541509040411340a49058038441c540440140d41c40c0d00b01d4000e1181b01254800042801c60040c941114026416110011000301a5481da0042c102c411004e904010b0340b9031001030410703001c1018000f01c0c248503002c0c503200e1503c05c4181800400011409815140d0038204000401070381c030480f08040c1e000304040010b83e0b50407040903a40c44056000400ca511402c45030780c107008010880500400402c002d480140044e42c0d0220251080f0040180d405040c49004100501d0b08019280035401d101003041180e0004d120b101c96290300036800784005800c08000c0103241e1400d510700e813907100400d062202031030170200b00081c1845240c0802c4480c0300d5480020143c021000001d01c001001f0 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 229402796 1250 229401546 229401577
    0x3090a030609050c01050304020627040903031a0d230313060305040c0605090f0405040609020a08060f060a0b030f06040e07090c030b0307030b040803190603030f0807020714060906 79
    0x240d074a0001e0080800c690155980d0180c0d0050072525880740302124025500207000c0c504041428044003080d200d03608a400c00c40383e09405102c204c0c2c440b4041c6003a840e010f41c40c00244242c4140d90700752032a45102c0d150f4440c2d08600c5400c400036411341210103542e141c1c2d00d0010740811040514a24510a030b40824501d804070010000c3c80359450342040344928031030000c40341e04c5503481e00240e03002c1c0544011258040004424072a207030030a6400b02d9809400307944086041e200700c1c5c0200e04192110b410a09a40d0400d0b020000713038241c11000e2540084064400c5a455803030030020201318000a8004403030a14980081081036907150855011402d50400b030790500360340d802c82c074002046554006004242807010f400001e1502040800850381c010007078403078a50345d41e43d0300b0400d50b03c020002d4241c4e6050441400c0902079901c1190b018510070b440788101c0f282111030280c4840b800070448401c541c4280c80070301c00068101c04111035840d065076031585071030b14800003400c140615200e070f004190 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 229404046 1250 229402796 229402799
    0x5040b091306111215010807020316050a020402040e0609010e060102060414030c07090b27010902070c0305060c07170a0905010f020f1f0b030708060601140c0f010902040c0e010801090203040503090a 87
    0x614a5a010b030055000b85c03c440d40484403c03005641200e0210742100160b08244901c0f10541d004046c02c00c40340d4840c1098449440d0b0543c0050b00701d810a03040310340710028000c1045614100314a03414050845841803a16914010300000c5d501c2d600104000d040c0d00748510340710054001001500c50744030294003600c10300781e143c015400007854403000319440b945503002203a600c44071102c01d0381c0c181071000301444076607820180d00c84d01a52180c0303070450300344815400c0040814002c2c02594000c65035001413640e1061a030500400c50401030410b5000d00004010801c201c5421610320800c0711001c1c245026200b9074031500f030781420303d0310079207001c41d00038510b42d088a020040c82106194003401d03410807000413042c06156035180f25000e100150781c00100804c101e0340c010310009090303076140c1301d0385403400500b158a01d0601e00f03001c0111505a448400400442c902400351a0f00f10000e0f15240c44040d11940008210039410711400c01c1e40340d800008282400028000c80b10162009020000b510303 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 229405296 1250 229404046 229404067
    0x16120c02090411030d0c0203070e13080d02030714090d0b07030f091407090606080f2703030f0c03060a03080c0102070512031b03060105041401020a0210030f0605040b09130611 77
    0x20800108404d20030b02030341034000ca41900492090000c2c0e900030b00200081414900506007030000a040d400d6007840f121410301c0000d88040090450040c440c40258890a0a80d40582080e0204903a03401604061042001e2a1982c68035420042d4104a01404139111003030305800810784440600100d034200b0741e03e42d0074032480071443c0300c52a02c010203c0d0400d9544c1c03119001290a94014440052000c0c00422108483d401d0303081d82008041105850308030742c030442d000d1071854410365018540c03c0030041051558a00700f500364006200c45240c0d185182c2500000c200d039000c1d00000305a6000802d41c0038921200b54103451501d07606c80e0071074000c080801020302d40e80d001202d03003803e40c80c00e41d20348540221701c035030070780307014034810b8680c603082c2404e050050022000c65100135045103c0c1140b074901603555650240203017240d40d20001400405d0703c070120240d80c1c1a17004039000318145441e0300139540b5194101507124505a1174030003403d18910380040602300707c205a0361780d102d002c9858a400c = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 229406546 1250 229405296 229405313
    0x6031505042609150c06070c1403120105040f0e030306060f1903090203101506080403020f060106050d0c0c020306060904150f1422030525080c06060616120c020904 72
    0x200b041c03c844070083ca0b0001201300340280305071000c2203920b812000100f400c640c0500002d8081521881f01d808110035043d992618603000b4002441300d01c015900100800c1c1490701c604c801d00700701808244051111140e202c0d641c0d110213003055001d4040003c944c0304d01d215100654a5150105145030113007490301034020003815820038203910030700072000990007011461013101e030410780d0b8041511200d4901581a1803250000708244c00b0741c012080c004007062003c2c00b51a01800c030741d8a60507110380d8000644003c0741c4a2103040d20510050b00b030520f003d030350001140340d80030508440420895441c3d15080d04910a041c480c60030417414850301c0408100c03d0340198250780b407004042d0205c0c1e079590a080b03890040c86290b07100310314141d06108010074407600040c542c0d1a840314101d0002c40032001c0001c0001c800b07100641d5424008030307000307101050511015422000c101c90540c14506032440320700c00d064568400405000c40610610421401917a841c58003540003002d0400b02d14050411072035 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 229407796 1250 229406546 229406557
    0xd081005030f031e040e0c0d0b0924040e07050904080405030601030f0b1605120903090a0b0301030c06020102040f1403010f0609091401020a0e0f030a0503071b050103060315050426 79
    0x502d9891420340740c030a0b0942c13410780d0101e40030007262850a445015140c4450b0f07000030303515500c481c0c960041c07a0945d01d40c02440e5020b41241710308010380d201208010024050f40c80340722071080382005e0014801140000e180025103400302d034002c10341d841e14501316003039200b01e501c141d800d8041c40700000140180f40c0d050020581c060180c0d20340d00e80c0c0310346103602500c3c080b10710000807030818040b28800030640080564072403041000c983c60603144c0800103242e180e03154041035034110000014001c2240202c000402088a4002582858100001c03541c0324052401098070b4002c0021110038140d80075080030000d0440c4400c1080101d484410180c090031036190306580c1e0b18481104103c0c58041442105c0c1200301035600d108070308401900300115401030024007a854481e000140c00803a8041c4010141d1a119141c65280007150403031045405030346074840d6050519004e000c10100e03e803510144550b02d00d118000401c2d5407145040001426680c201e000c40e80c1081c094a844807010000820 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 229409046 1250 229407796 229407817
    0x4030c031b0f0f06211104140f010e060c1f020a020d0c1104020d0906140603100c20100606050904060906120b070c0506041505090604050d081005030f03 67
    0xc40c074544500c80251000000d2140c04240c501103c410080d4501c1020604000a13407404100b1420f444580260b0a60b100900300c0202d0384c40010f400c0000c000b448001c2401c0920543d401504041d0042c0044c0c4208030801c4000c1c001d0500249142d405141404600f20124244010b03081002d00c180704074000b50050903180c0094441c0b89540d1038201d0003444e10135071040d2300200110104000009000103034000c10304800300b19854020b1701c00000d05034090010b52008100b2620428509102014074003400312101c4d51720580352441006200340d010004144003260b41c2480c030194205100d03240e240044500c00307110494540500441d40991000040c00120403c4505100e469110030515003104d2040c4030314865904000700b1203001074a81c030105544240c080c04c084020100d07544906080030821542124004880503541182440d98800d494000a040c40203000502e8113582e505d43d60000c8010a03001d0081d0300002501490787e0462940240201030182c0b240c064203000e440b5500d420841014 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 229410296 1250 229409046 229409093
    0x9060601120e06010b0a030905030304060b011403090322031a09060a0b03190303021e030f010f06051c0e0d0c172b090629090c07021504030c03 63
    0x3241c801800e4068a11088040009055564640303a01841d01c1c0d801441001c085c19107920320740000c200140040e5104500400c000300d07001d0300310700004200075140d410724407880c1c2d014802d10034401c200105440341e03200c04806000d501c48882c804410265555400200059960008140c0000ba001116405154148122030b074640345d0307140d4032040c0c83c480d114240d0150b00c1840c0b0300120340c04100104a203030740a402c0041c03400019003010362100d00284900000c1c411b000080c0240703841c20340b00582c01411a21281d980c003034207100c0010701034400c40c0304004507441e0044007035696400c140d0069a990703030000201c403a075032400d403000792900c1e0210f4415502d03900d00030b4400300700c1d0f0400c40c216814600000c009400410500c004000d0044c40302600599907a9a0440071f40000c0c0648550610b00c01c0c85081e0b40d45142000228610f4bc401442d001c6010f0740082c6d0510036600d107108207460003550b04071100403d003404070101020300d0169a20240030440c0598002044c414407803a088070f503007500c072181c = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 229411546 1250 229410296 229410317
    0x20d050a0c0f050721080709060c0803010902090f030303130303060f05030712030e0d0f0605060301090305090d1e0b0f10030803041e240c18060c03120509060601 71
    0x80e03045450500c038050104514403055100c1038030400040850520600700742501c02000303c07800c070680c000000410003180e01202800f105a4101240c10000c104914040c84000415074031300b002400188502c61120360082a040c40700d43d211000358401001c098210382d143d190000e814005003041580a07008245040b101250002c03042142805903a8042c0040282a141400b102d18040400205504125070001141d0f00365803406001c4400d51b0191130304c01d0103034034a414250304417203002c0c0030702e0321031384c50400b03480006500a0207503841190b044810320802c0440e400c0000d04901c1002c014030555111400520400000c076010340c1c001e10400c01000c00c1640c40202020312980036003c00740c0b401c203007880007900042d00c00c218405201000103100c0b4079800c8996070f03400d5071070000b44030a24030780e40b02e04203058880c2588100c4504030401e10300383c2112101c1a042e031400c180c0c6801400200b10502c180641414080c0c3c5250740c000403940010442850400092510341c181940d0480c0081c501c07124 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 229412796 1250 229411546 229411561
    0x2030d020d090519050d0f05010c020616050c0c01050f070f1a0606120c07020a03080c0f0d050405181e0c0910030b01120b0f0d0b15100203030109090219060201020d05 73
    0x301e52440804480c6542d41d00b4144400c100d81090396201c2102c46030040c0047d04005072013801070444c03a503890b400801c004c2c1440c2c0b5030303a000060125101e0007008428084821186070005c0c1411340c503c401e08103182e072550811590200e5109410300a85514901241d60f000c120680300456003480700070440461503100c10b01001f40710302c909211484014250400304040c4400d40c07000f0b24000c1c0c0b008000074141da66a5170ac0d4440c40d005406528200c3e0808c920f0403171280c0040c08400301c0140c403485c1032450329040c44001b60421841c0919481807000020026a01a4018016506044280f4000180c501c1c289000305503c0d0710045000f4059540d00e843d01c14100d021340622041b044058581013606041200d1900080034101c1c5d1040d03020602c00c044004a4882d922882c00c00780c0204c01e44506807030500d101102c154004010580646070203002a0130140c0e010090b40d040d614002d1020500441c10b00010f1800284e5461807141c05e058014001942c0b80c056006007014a080c2200740207990b00c041 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 229414046 1250 229412796 229412809
    0xf0b040816080307060b061c1508120a03053105070b03010e04110a0509100e01120c1e0815040b0a1a010c03020f0609010903020609030c0d0507050a02030d020d0905 72
    0x714820b2154020711150b0001605608100901c2d80c000c0e045600b40f5548407958810320020385075805085a55030b101d503092000c0004028054640305004002d0700304d0031904011144a1304aa80f020103075940301280c8101d500b020b2a030000c00300b0622034041c10010809041c0d0b8042c0300c000c11580d0784111000040d885104009480c101c911203c0112207075a103a45400d40c2184c20540c00640c040108000030595a5840c095203004903e15400c401703c3c030f406d04e91108414101a080b070100040181001d038006040c00d003d040c142c400d4035044103e8a5102d00305480e00c440c40d074110400b42d01408443d2010142c01c14850780c031a900880c8070100d10f0315103c01c500201e0750840c1458081100c3d1508d501c2a6500034168140d8891281c811070f03092034001300c0c045041260a442d0f0202da65190307103030b6405160341000b00d03d4000d140c01c0c02462400041d43d85d8150344601c00c070396101c24003101007401000c0c4a014851500307600d40150540b58101c50042009484841d03600c84c5070040741710b10030003145030304205c0f = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 229415296 1250 229414046 229414049
    0x610060203090f04150311040c020c060a0e03070806010b180603071d18180c031f0915090309050909010b0904021507210e0f010c020d08040f0b040816 66
    0x80d00a5454041424107000041c031030500c3c09070704030f40c94840e450400000105a64001c41c02000e4800844940c242040241d6854580b100f00715803082c4844001a0b07104401c58580050314180200302c525a038001c681401640e611170ba006015907000000e17058030010041519041400c450740c0d00304003000800403a0302003038440100140b040266050302801c016001800214010132018554400ca031504000302811100f40312503451403032070b56100803020803103580034680c2240a4891201503100d41402181601c204180c80c80d04d07466440103200101009115240d4402d0043c40906e0450601800b102d40c1c40c4903845c0900c2e60302001a5103a070781807080c0c04030b084008001a520345c856800b0011801c140c4a07080c140d0240400c030440c0011900401000c01140d1000660350041040d90060100c00ca10840c003409a800b4809840c03c0d80c0c1d0020a22440c0c5a0440313009441c0e600324140907038a806540c010f1803421558043c04200e0303804880c06041140e07240b0003180d840214402d0a9400341c001c5 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 229416546 1250 229415296 229415309
    0x5010f060c020103091b080c120106060804060c03111209070b0408070b03180106030b091605092a0307030e160e07050a0513030602040e06030604080a030f1b09080610 73
    0x400301c40010b600c25000000d1980c003a07040c8482001007440902056202980140c0c000e5002941c1c135641801c04001c51102d204161000f00035080c980301001e0449000103200406150355200d01241c0b43c2c0c00395105251189104529680321040000301529100003510300350180e20901c1c1700001c1200d00c240895094602c1000505109454451030300b800340c0000c0c107811999500d400d02000407103400d100e080d00841c040c44842c86070341080c0500d141881b21000b0080d011600300c0c2d501303010a07101c103001e01e90440300405041d8880d801c00c5810402108248041c03054400740003084c80b60a9a254001c20240d80c0e141080e50800510703416800c541070f20b94030510600c5517040000038074150040307000c0c1c401c00640781081844e00c14050340000d00100c1e80d070012500b46030f0218040c0300140304c80240551120096000b4070190a1a889104207409a015024100340d00c4500a00e007066880d00660742070704e00020b024246840c1490040c00a090380e000c0d081861050301d00151180390307040d4031442203654 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 229417796 1250 229416546 229416557
    0xc0613150504021e04140703020a1704050723280e04020d0201030509030c0d1d0301020901020a060b010c1a07030e160308130b030a050a06050105040b0f0c0f120d05010f06 75
    0x2c11050040144d01d01c1c0692003680d428201a0444101041c54442c401c01d5600580c0d0310702e8040d0140c13900083c02003400380003840d2410000001c1002922000742d07100100056003000035012410501040c0d80e030020340080b051800184c145454500c088800406281308030755840d25006142003007501154060b41c002200b03c030600c05940298449504145801d0507079107850030078841c0c01d180503421400000001c8032015801c1e07115039044010b079600b003c00c40003903140c1050140000c0d070302d242510000e030440b60b541c48241c1d49030303018000c00301d409584034003200311100d8245000c01070014100d0b41000440d04002c103980c00d0410110300704580f0410606c090703e61500710b8031240c44036042883c582d4007000c450a00494110501d402440c0f1071103914401040c00d280008002d019180c040d0301150601900b4003050103000415801e541e200e40f41c1c2c443d070071345920003801d04c145004441c000302c0145005078061102045011001000241e407080d82c14042d603641c07980c080f4110001485140c0000e44d = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 229419046 1250 229417796 229417819
    0x20c011508011505060903010603171809060108150a18020903060106090e01060e13050a150e09031c0b060f03010311150909090f070b090405010807080c01050a03020c061315050402 79
    0x50310074060480a034007d00001001510782e0303150010307a800d070280c040c0f024002117555002c00c1495000e00042c1035042c0c540320598203007a0006044650060120340307009042c6440f041050310740100490003012030f0b10b903068005e0402001d003002503000011075030183c059800080f50403800b400e0504100e6000c03400520395a0301e0300ca000c0351007049020300660b00c130096111480405959000300c90040d48040c40001d03400c07400c40000303000303012654000c2c0900c8100c801000341160003c070a59a444904401c1d404030b10300d4203e29000140b100003131003a8040f001150841e0011801006035040e28400c07141c00c075850b80210108055541108909544180d00700800700503400c000070603a400400d0501102c171010f080c40c80bc18100780c07507500104003600010508081d1031929001c2c0341d00421414000d00034060034410340c951520b04142866060002c000b4410b0b80f203511980c11150081c42c80300c2a505c0b1802e2904c14200046440c42e000d48480e945541c0d8411502ea95100d0b007401568020081300d80c01 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 229420296 1250 229419046 229419049
    0xa050907050405130515010216060e1206040602090102070b040e1b07020d0501020309010f1503030c02120706091401020102120105040506130e030901020601150903031809020c011508011505 83
    0x2200010880303820031400b0312002a990311540d2032a100c0300450340c0042094a886948401e04240f041421411940010035200580c48168407400594003689031842d0803014410211b81c40c103e17690007042c110f200300740800c07080c03002c0b0350b01400c4100300c00d03400d4612240e6206804002409180100036050700c1d40000f14a00c1e0745a51407138154080ca11054504001c0da640002d51055101802500c00c1d075000810082c00700400e101c0c14804c100d8100041141114180070600c0c0812a80030003801e00c40f40131440750543d074444d114948032001000c112650591208401801170265204561144903c2c2c0d62030000c030341c010300070750380c403038503128007904540e8a0001008003500b00035111680022600d6032004001d24603021341c00ca0f001c0c03548000c4d03940e910000c00080c5890340580c44811000140c184070800c0541c800000b000303d0303400d85000121031404100403680c0509a50040b45d956100082034088a001034025440c102d201251a01c4585c3d40e41d08014282c1d087c030070340c0386c004084601d410702c0903 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 229421546 1250 229420296 229420309
    0x2102010b09041703060409140604020f2e0309021c03171909080904020a1706030604170309010204050d03022d030a03150e040308010305010f021e070f0506010b04090f02090a05 77
    0x5c03030083c00030415218503100c003002e50100102901954109004210943c10100d840300c403002015540a01040e420765610490103101c000004e00000d0107500941c3c0403071103500500403403a00100001490190840081c0c203516552404030b000c208c800310307400380b01008050450320441c144810120b0740ca10303008a0f40010301010f1030445612405010000d4240c5542c40a04580e240359241c040c00c164180e80020b02000c0020200e61296118100f004001090540303000014a40a5003850301d03516920300c07150282c081c540090790031a40214821061650001d0040d2007140420b1440554a04505640c844d107104016110100d502c00c21083c101548603030b001d224500503d040c10492152101c0400078200c0c020750b0281c0c0080c000100503c2807200c00e11071603050407910b105c114a071116600000d020100c003101620401030000c5940c1042c0001c00d5651060580e000090790490361f11150f200b601c41e045800307264801860103503465034004682c401c941004000514038450f45280000300f004 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 229422796 1250 229421546 229421551
    0x1e07060507032310090e1f0902101b0204020f090907030603120c02010c060e030a0f020334021f020c0d05031e04080105090a060e0c010e040e07032102010b09041703 72
    0x40d81d82403190000300502503224003900030140c0c1000d0400e4021140507101c0387c20300c003007480580d607160a018800694070038059105007002800d18050814408140c0700c030001e00c000340a900940005542c000c0066488010f1494610444454031359494450341101100c4081c04010800075074142200e007464000c1d00d4904c0c240f0700c149401c608800f425503035907013580c0a40c41030308496840450240041900216640c5038607001d03100a50030035121701c0e0a6607000c10110611080301520300e031803140c3c402c50f6480084040360060451064507070001010548202c11408410050180001246407864268242c81c280c40c1c100c001181000c0d00300361800c0d05000c1c2d065604802d8042004001000b61080c003419100300007010103844030190380d09040c0242d840400c4060055009060345010a0f0b07044018603954590903a80001c1c0b04400c2c0544a2400400341c101814440d20154800c02141003440d0402d45c0c100c0c0ca9000740f00c8002c0e24018011031b40c5050740e00400c3d0885102c80b1040d46002c2c003001d5503 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 229424046 1250 229422796 229422811
    0x180e06031506030c0d110a0e0705121b1201050a080f0a080a0509030a05070501021b010804030c080d021305120a08030705160f0b04050c10050a0806061e070605070323 73
    0x40005211130001910941c0240040344c984001c982440d525142c1184034000030172210030600518038100300010300d14455010081d500d81864008100c809003c11910301d000c2065100c1290f4408070600d0314186200240310700c602c1220b072808081481038001c01c03500d00c1503600030000c104c0500103580314007003a004064102d080160a1046200c0ca95041040c4102c29014202400d40c840c1007e00090404030110583c1103a01d0f11421070307041c0c0d80d9101c811160b001d5018907103a00c108640b440c4c0800d440c0f040101c0c1e0742e201e80c00801c81c0613481803840c00400407a1400ca4246142049c5144c10544480000340301800c403d80610011340c02e14080e0340200701c019201044404417411540c0e80c00c61315540d02c90252204a880780400081100030400c444140034225090003a503036240c6001046445103440f4401005010700114201da143d000945412400e103c1c11a9010004044030140c203402040c8141c856605050209041e81d000f8820300c0741e4210101358401c4150412750941c03d1a03074000c1c0190 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 229425296 1250 229424046 229424053
    0x60a030f0b1903051009120507031202041e080a020105030112060603060203190b032e0e03030a0e06010b030c042606160908030408280c06180e0603150603 68
    0x180140e9030b01c822100c0c2c500030034040030030380b14114201149070095441e401800d49103068011004260205000522520507291031980ca1240b07140803a5110a00c050140d445800805c000c42c01c13643d280840064940a00b0803020955602c80d05940e840750000c070b004c3d02040003003005110b034600d20140320403494040c03800440c01030f90781d40d0386408136030003180c1c1941c08011910f90200500440d0150010081044008010342a000403007040710b40d50801001c0521111044084007551668005803200c4102e4030652342c9a14101a0240241507400900440d50003044000300d4511070341d40c20b90340269070240b40c080c00c190500c04a801c5085840c2c4080041e02c403426031540c080f802c00c00120b03215501d0401c015810034043c0201070100700b032940120016800034401403041d62000209040e110002401d0065004401b589100c4080901b0001801e060760090000c100180c01516003425842008024072030310795968100d000b07204c4107480f640c1d4181c005100c1c040a000e030400300681c008400400f41c = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 229426546 1250 229425296 229425311
    0x4050a08070f0606050d030905100c050a0c06092304110c0303130b0a140406021803030307020d080f0402180403020106210b010801050c04031e0c0306020d0e0c060a030f 74
    0x300d0308250040301c0c040b1070010b00b450310082000300b203000d03000042c01e054404190a00c034940e005002000c0c98018075001d035030501040c6810900c1503400140040d04441951509081c82c10703d003240f0900f81c010f103404181895400121b40381d4a080720080c6541c6010092001442c2d1410080a04402c0ba9050355080c03042c40703614150f0700e007440154000d060081d111314422180c3d1420b2583d410f00140a005414a000c14804186803141e844580c007940c41307800169640c11141c66960440c12002803281c062001004100c1d07580e13000201d0703080100c2c080d02c8841c01c0f40d1300d04070b45000c81401181c0c000e41043c4001c0c1104104c0c11481d02c1a50402c1c401c0c00082511911182180d0100c3e001181e000f0130341c10200b0740311042c00b460800c1d480c0500300e0315000740064541208005418400c0e44402060090040c440041840300e400c40860090f43c44024020307205c0c0d0300c5c2000000b075040b4003100502540b6100d00400040c034005515203150001034503046c100044d20200781c00921108201030724041c0c84515 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 229427796 1250 229426546 229426553
    0xb07090b0313020411091003020f040801090b09010b0301110d1a030f0304091103042303220503012f09042a170c0405120307020904050105060f18010b0304050a 70
    0x25620030b00d10031161110756002070040006031030144451341862802005071113120307107690800d1640004103050160340e5580000c0140d1043c4500e9118071141c3d480c040c0c480d401c106076521040c0c0210910320081c420f40e1640d03000c140c221010101c7c0300c0c0404404001c000b0106200780c00c0b9105c5129114040c5003051140b0021030f003000e0703600601c84596040000d0901117160240300755004000e02c0f8860342c0c114501561103403c81035861000e40d80303100f000e41d403070075405d00c04004890642000380c500d4070900d0101607241c43c0d401d40d20b0241500c69428105a040007001c107010401d61028500c50400030800400030a10702940202c0030b9581003030302c400742d8089000d0786481241c0707141284100303c1580c42e0b04000040034004c203842c2c0c00413040500000e1080c0148094140d034269078044400a60300700070f206c400c0f444d6102b00d103402074200c0d07091030410081c40b4041d80080d224040980b48805000c1d44ca50410822810184900c02801e449a0040c4840500c1c8405164007034800c108407001c200c0d0684 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 229429046 1250 229427796 229427819
    0x15060702040501080708210d20070305071112060402100905060313030e0604301a0108070902090117090703020d061e020403021f050d0204060903020301050705030708040b0709 77
    0x2006030303020394005c51703040114034000c011860480c50710603004400c0450080c07410400748100404514003039102c0c2225118030303000d440114410007107292a00c0c0c0d561003c0c5406880f503003203030f08107589000b810b40070904141800440c048107061032802030042e41d40e640e400c000c41d0400c200444001c00210301400300e4035450308801035000b0390b0110001c01c4031510700c2c43c00030301040b52041024017402c0b090104020402c0400e4034102148000107108002e50003800d041c4101c1c090f01c90340645100758080b40721000100184d0a641070b43c0c8500180c815040c0c50381180c400f6489030018840c0000c46620004038003070f590154240d040030b0b007003003540c0c10036980b41c001810075115450300b658156070310800400350481c0840c0802e5910341e000b0081d801d0902c2c58001405c0c0300700c41034025030426403490800e40c525100d00126042226020021502c1e1510344900915a076010300080707000c3c0d0321704001301d450103000e181500d120342d402d6a1443c80c51340e038598031841c03043c0005d4040b1043c0302d0140000f1900300c0c03407903 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 229430296 1250 229429046 229429049
    0x30d0606120509010b2d1c121805040216050111030718060c06022b02040e0105060c07060c03110a030e1f020d110a0209010602010c1404050915060702040501 69
    0x1c0d41c03280ca500440701021801c44074041c100700c1c41030b854000b0034541c589a107031a07005883c05e0740c86210851900958402090340b5285451a407218481e42d84d82000d461700001d121010f400b8844100501c43d4000003540e5003500d4415650031124400c0081019203800c0c0c00414181858000c0f0801181c85650b4042c2503850414090849010200c1008000c0f07500042c61102c04107a14440c0d00354515001c8080d00038412000702410302c640004030b00714510f00079440300d02020030600440c03051101c0341c2c44241c000d41003401080d60900d0104c00020b25803030200c041e076881419035000f41c1a001c1c070341441503030341c080004003c8041c8207808011a1a0a005000600e1040c1c02903c0d54503810b118102084042541310f502203007010303481403502c0c07502c617070001d0010310044150810081e0441000c407000c0c906558490001e601c240c80d8400811100e9040d00000d010032841d485401c051280c080200704103010383c1c0a070a80081e5140000780c2c140540700c0507034500740400741c640c030f00d0701d00342e5008181078444c01d = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 229431546 1250 229430296 229430309
    0x3040902040302120d05030408030a0e06090f0f0a050705040c091a04050f03010c17090f010f02130501021b1302070602071112190b06030724030c0503010b030f09030d06 74
    0xc01c0c1042507041200f4026403200318140a000200b0406401030721034040070304003922006020001512071406903010340d940500708270403100e840c984801911707039450803000240c24902840f510440b05d444000b84c0b8080c215480070190013480d0402e010b00c001054140d07611000c00a9004001465442e0072001680b480c030945c246503544e600340300034403040c80c7d41080c5140c0281c0c0340c80c1d200b414140c0e010020003000420392002c290191101e0780040e2501c4600c60310a140e03546001b2a14030740d044590f0007000141140810080220f030f80d48010383c1c981e58541c0861142100075801c40d5402d1411450640e44c01c280818014140f0800b900c4201c06c136081704174102c45400f403190381140d4514000c480004101c038001c006000449840d02c031400f40400c03860008240c6158100425803c2e501405018094810241d011104013801c8501001c29140c081da148007081c50401c4107200c552084048906981e01002c0ca94616151040d038503001500c0149554040c0c04148252890118580100c1000302003 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 229432796 1250 229431546 229431551
    0x61e0907030902011403070e04050a0b061b07060f0504060324030f03020106050f030c09090a05030705060f010e01060e0607050705090a0903090b070302190c150f1d060301050d0212030409 82
    0x100d0b0f20014008102d20300c0c0210483e402441040706e0550702c16100499100d003628040f990b5190202040003500f0100d1004c0e902c0340002c00d00341a9485103041113410044c201e8200c82c600c0ea6241420303078200740204c40c030f400015010842440081e009400c194a500d41170340d400d582c0106001c0b02c4d07904820040d001107600d6402c401900050541c240500d0026000860b038426940354000c0010395a412482d410074000c0c8050740c0003501071101031040100043e0400162646c2d55024030f09151555000c40d039400010a4400012850412095410303040c0c9116898050b40645a40700300242d58110003003c42d09845036100c085010303145c8044190040011344030203c1c440030f10b4a000b4203143d03656000b2203400c020a00080011941c00240c0c581001c0c0410110320001115062a041002194000594103204140e4522100d45d2180319448000850b50b6041c00103803a0400c041070102210f01220390103101800144280d103881d0b8600c6906920080c018140b941c5c00a07181030950308a0351007280c0103135 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 229434046 1250 229432796 229432811
    0xc0c030c0303080702010608030d1109040609020c0d020613062a02060108010b120303010608071b1a0a05101703130f1508010303120504060f0e3003061e090703 70
    0x1900f1006407034014035140020b00519007400892540c0c0c4c090360210040391500ca1906090941c0000c01b00c5800d16005001813101603102c84014003c4c0d4032080c88910240705035a03c800d0261f20104406000d91b220048192115040b6103400e009410580b1580d5402c0c01c040102c42d2600c2c03820307200b000f40500540c0140c025036141007002402c5544040000c0e028003503840c0c40700c00b5010302000b264151100c904059140c1d0700c8141c4121094541c3c1466811680003106191041c404c0483d6131070401281c82c1a004925650071554074103903a810390b900035040417a46030502c0700c041601044004004c2e52811641000801c158101c2203880541c010f06141281c42c0c4203109071100107031613410300da445080440c100c0d403455800401c0f000401719003981c40b654850205003003101c03a810641404031401c00c00d0080c648d00030403040d102c030300ba46145402c920843c4860141000c00340c580100c403024990300b05056035904824480c1d40c03584411940744002c00c21407003104640c2d901c0c00050055095540c00200c01 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 229435296 1250 229434046 229434053
    0x30a060606030509030f1e042303070501110303160e100806030f1c0e0103061a03151c030804060e06070909050907150c051c031a0402091f0c0c030c03 66
    0x5400203004c42c40b16400411440041c2d0041804031052504880004070051403031241e02c1c0d005004a4103d01d48c01140c0c4640c01001510045400c0211682101500c9a0b00d0381c2d01c006640201146050080581003400020f07616a4408146401c0400c517090450450910400003580c0c00d40c014058400701d0b0b040750602403641020042da2b41c26140c01d000814030495280118100361b09505811010030901d840071128a91003a0085001403802588501d50301d29140201c0c0c2a9810460f55000010560400c194103864250b1100c00c8510001c0680d0000030b010b0b46003140e444200500c00c0d80c0181e00c0c1d1940d4103034600c0410080d03210b5a401d07a40e00490a0a0071a000b040c0c031400b400c880302540c4440801c2c0604001c02e440c1300140803030b50408050031011450002e0038040d0868442e10a08030007041d020001e500f40d088a4511000c050107046c22200e424108412406100c8403c1d401249005160b00644100007503d4821a40c5040000303103c0c1d503681d0340f100ca0001c150002c40d1540c04043c0c041040 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 229436546 1250 229435296 229435301
    0x303080603070b210f04030804120c0b01060509010e01181203051608031803030702070b070614070809011107120e030307080c01020904050a0b0102060402010f14300c09040506010509030a06060603 86
    0xb01c00312040e1170460905440051440b94041d1014142c0f2144103201a4100e00815141c0d00781075008802c40034560b036030200500f132030304052082c9010418a20750440c50750b10456245030007807582c400d040c12003414100c01203180014803100303c003804401c2060b400002003000607010480d108024240d40d030702c1c180200c01d03a33040380a101320905510600c10311012580100f860000d55515200e0541c8504060410001500000c1c0340c80c45009010400d001c10f40398400c10292040302c0d913500a0001070001400703044280f05010000e8480905e80340300010340c2d031080c0381c0341c07100c003c1c018101c81c140305282c0c90b00d8580da4001c2424861b0b50b940011040c2c42c50600b07015107a8400118007080019504050011f034891000030b10080c100407115240d0350341103000303e108860f800c00708082203480303803810029111a10712803001401e4039641c0c6642074211001c208c01e041c0c49085c01d1380245040c55075020901c000b5100140103d0b0603c103060090f0040394508000300006503004110106800d403030300310301a04 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 229437796 1250 229436546 229436551
    0x318020402040e041b0e040204050411040212160903030905090603030c070602240c0702010e19030507080609031303080d0609180b07111b0f030303070908011b090303080603070b21 79
    0x200640c50406c001014200c40150752042d01524042003d90b600c0c07408100c50350a0084047c0c0c010320128030312005502d074000311440b99030307909070344900490081c0042c1e4885140e4130000700014403000060201e03051001c001c90308903c000e401c8a003030615040401e4217040e0b0341d800007001a4440800107181044040c4807043e00c6036500f40f60b104d07038181201c40c440d480c40784400203414000446142829130329900000b0b0551504a840c24849070344a00d80951581c20303030310400e29180b242002141c281c078400320485904000c4915171105c0103145903150b00786504481400e8802d540d44590000c0c6144090240317850040702c90842c0d0230003400c5031802035407019029125004100d001c41d00b02c14030030400540c06000c40711604043d81203051101c000352a03078240c10500d80d050f00011091002c000d403c50002815a06503000030300c0076410013440740c401000c4103100c10300020400c272002c20120f1701401119400c490040c0c240e9950755100c54500c80c207640480d070078025100032407001c100c080302c14030803854 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 229439046 1250 229437796 229437833
    0x91203120a0c050405011b050105070e01080c1216140a050c1b0a0b071407080a03020f0c0102060117010e01090804050418020f040e0f061009050c07120318020402040e04 74
    0x440002c9160000385903024900500d41880f05000403050b144144405100c0c2c2e0550010090180b03141280b402002181141e190a01040c0c455001c41e0441c8a05800d861207054400d06440140e9030780d0940c035440940185100050008685018000031042e400401218595848041c0d586d0400c2415614101051040ba9140120003204074842ea030348541d400c040b1071454a00075281c114500700545200c4030320348004410f1082000004044c803010400d4400c981c000d40035245482d440c018101c2e01d0b00c0c45031341d0541c016080007006210881000c0b80840d11000740da0000528140d281b0826802c4490703440d0156402640480d040003d46058028800c0c403024854201c502440e080e4040b44180201004e002c0c4215240d0f425000041020003400070440380c1607084940300d051084481050000d18003074611018200f60004051a444408442000740e210440c650f034004000e8046005103c8405c0102c0d00200310000300c0d0240c0d40e1400903001130040144095624149031900c0d1052103140380005 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 229440296 1250 229439046 229439051
    0x1205150a05010f0e130609060f1e06080c130504091a090106180c140a0306080c0a030503310806011d0403050f161a04030f02010e0c040b06091203120a 66
    0x760f04540d0040050542000988500405c108813400c0d2101404182d0008180c42d450300400240c10085818420100d44403080000800c01e80c504038503804a50f00d00454012840388008101d01c0007540c070041050b14100404102080c1d154030016065603090746050b6100000c0c601c4c04a007060011400c3d94004083c48000c028240c507161040300b107104001c890350303402c1d55640200040d90380104040c12240400d480a01c0c2d032021030003805002442180101080b07449401c0b480d0f40c0c80d04080c603210f0156500400258104130207900c1c040310b04004420303901c41000f065002e0740841105821520082c10340a4003070a01c560400349005180c1d07035030041c2c0d888006126070610001c650008c04503210700082d0680341c2e503039840040e5450050306180400420f9074051004028200f02c50b10380b0140614441d03562b000c070821810b5022401d039407014140c03c0182e000072180e0007492400340d114000191020740264103084152000404072050550042580d400014064010058146250758400c0004804 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 229441546 1250 229440296 229440317
    0xf0f020a11030114010e180a08090609030709020a1d030105131218060302180307030b15030a1e1b120809130c020c030c0a150309031205150a0501 64
    0x25a80e944491001d051200e00680c892002c0c0c4080d04204115220500c9034201340d652503003600c200b40000c0b680d00031840550440343c80c080e41c0119148100e180c000300140d0510480404100c02c3d85d002503080c0da07251083d031100007004a1180007424074012a515800f5402000e03c243d9880c07007001043c054803d902d480e0401c0710420881e401501c049402c11150300003400d00442c1528070002072005148040390000d40000c40d90740c150001d00c0c0000d020200f01e10500d50403000e15030f8a000d1800b0040030a61040c0c00250b8511400d0140504940c008080b94416800c07900c80204600c00c10205221720b08081300d02c601441003a1860007418015038204000c06494a8a590307d41c000841c4010a0140005034401d41d550300c60034201c2e401c49045e10300700015495800065038440c81c02c0c0d03050b0302070701031110301e050545001c4501200f100c00440a0810541c0000e0b011801007103500380c11024072820b240d60000900040c4507151103000b07913588036069014200104030104805a000b141000500710781c = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 229442796 1250 229441546 229441577
    0x60803031008014227020901080426071b060207080c0f04270605010b0c07030b040305040e0406050615270112140a06060e031504080f03070c030f 64
    0x113048030201440e84281008846428800c042c8080c044407a80300820800404d00f616510107100c100c00300000ca014032480c0f4962020180e00800150a02045000001401007004140100e550b81d016400389800600302d500603014030b03009a5815070303032038031880c0c01001c51102e245401000340c0f883c1d00003000c900d0715105989903140d107150f6010740284030a03801040a62182d0304540514001c03200300400d01c9030b001620746402500d00d0400e0300c00d541444000030382d03d00038200b151590350100001c0c0c064907045403180c1140c200090b00c110104402000300164400300852400e0049110301c202141c2420884108081401d82240c1e01b5810300c400c000e100410601c9140e035101d40320305180b007096140115801607800c11140703035000004a04002103104030002c0d0020702da00c40c60405500700055626030303c0858016201c05071954165000780341c0e803000340c80b1400500354007600c6070900ea413800c192044040c0c5e50340c00c103940700008034507500000e80c00c140c0c0108201000c0e101d0381c601694109201c00 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 229444046 1250 229442796 229442831
    0x31a0901050d110310060e15040b010f14092215270605030f030a0908060717100503010207060519050609010627030b07020d0203040608070305090a0606080303100801 73
    0xc40003007280c1020004420992400c5c001c08a4800f1400c20410401d03907200f281c04400354040f6000130882e441110903440d645003034450f9251410040c1d5901c201180303840410f4410282503039201000a0003030003040155544c042010000a640c55400341c0e0080c0a801e990040c1e921070105100d1a0240c181e007480b90440c819a600c440800c211b800600405502c03c0305401000070750015900750040084820503800000005e00e044d40d0503541f1740d1903c03175540d24010344400b0b0590752800003403010307120b2043c20030588014981100440c0364485400c1e41d074400090882c2c0c40003000f22800d82c0c80d1030800265a0b03540c83d0787d0000e0306d02002e00f4482d40c600070001808480e07050181c3c006100314000c20880c0d041c8010404014104400c1d400f01003981c40c0e0818000d5540c08481803401482000720111006101000b540e0440d002a1540525a103522600303901a01004007224100e00c601c0b074174507020404078002ca8005042c98000386550b818440e282e10701c101700d19000449140e06250141000c0704408 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 229445296 1250 229444046 229444069
    0x703031e08060303090f1801090515060c0604020409033b0303030709090e07030f080d0c17060f0d060903080108060c0408060c0f040f0e06100e011d010504090c031a090105 75
    0x1103402101484040000498294002c4044501070007c10000b0480300702d42e038801d5000c0d0b032001c01d180e905100000200f0025200300d40768211181c2190021400605041d001306600d01e00c20708010310701e142449a034140705100c01448032520142c54800400c003d070011a04410110140c02851031803614140107001c1018501c1104411070703030b890b60070085000501880e409107900514150a007601030030405290b400804203074296526140f82c100d1038501640390310200303408040804095941c0c1c2c0c000c010702d2039050044140c2003155003545d100002e0440c030880d20028400e403615001541081d00003071408400615089414808200910090500040c0396620002d42c0079015510091165200d480c3e0081e684000c08026520700c1c08a241e0609400d032900c02c000907503039041c849010701001c0740d505a1210600d400308011903054102d0515a50038100d04032010306109161031f540303d070890202d030180303489000000d030b0361007584c1545040840d07490000c0404a4010110394140000603000c40a04d = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 229446546 1250 229445296 229445299
    0x40b070f090b030f04050f0a0f02090a090c1404020d020f030417030108030d180203030a050403050111041211010309080c0f06100602060c030912070308070e040908030601200703031e0806030309 85
    0x200300005c0400c4030420000c0441303d4038800f41c40d0ba440262400c0305600e610707000d04902c43c200c84000121501058424604110781000b40d0301020392030400e490043d00a55441240c100360204030400d00202d5034002010b2040700502441c0c0d5038501410045580c961840400060b40e9003000104075803078001060b244009002c00700015010304c0855589071010103020000c1d0075020202d080f00d001a0090301800880c2e004d81c0c000e000703600612000700703414411401401c03044c4810781c6460000c10301c405400386120006050005480440b81c446c0011500241d42c00803032584029020302008600380041e64020720300704074218030b42d410f01c6030103901d03100028a04076481f003000c0000703090144104081100d200a643c0101d54030340741410700901c41e01d401c0300c41e800450300c00080501942000d1052400303030f681000364942181c0320700c3d00464184221032822062606540341104100b40305200080c0214440e44400c100d0b0710000c0d2030b0500003a440b0b0b030000103001021080140a4a011040742d261010 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 229447796 1250 229446546 229446571
    0x90312030c0c050a050127150c02031b0601090f140f1003060606020d09060c0b070503150411030906060d03080c0d091a070e040c0e04050907030506040b070f090b03 72
    0x211a01180c80c0b8012100c06005882441c40641c2400390641c8031400003042c80c45c818000002030a0814201182408001d06090250b0351902c0b401526502c0b43c0002c4002d413040c0ca2030540c03483c9841c9544044403841c00d10740c0d042600100b1100105105642459181030001d02c040c402110042900e01030003800c418507401d4500008940e6030100120342c0c0515841034007041600d4445800030741e01c00071040c11310045462a0f001103501e501407001014055442403400c8031950790320340c2c22241a0806041c45584a5039116890310507620781c040d82d9100c9442c26a950745a1524441c400d140400140803540038110224903c40402e501050495120344030400035030b69000c10821043c010141c5001c0039004c40034500704d541c2900c5075480610f008104a6441090000c2031008000031512082650404160000b104020506194200d198032102d040c0581c1c1655650f52541400c14404460407a280786e00c0104214003140c000c0c0320002040705c1c3c0d10b0a45105030070700e011032100303100180890308030f2003 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 229449046 1250 229447796 229447811
    0x108060f0a0e07030603020d0305040305070b0c100b040f020a08042d031d100c030207050a2303012a1205010b09041508071511281a010b0309060709031203 68
    0x41c000d800c41d0000303581c0540741c4150088c403400d00030055005030004a807140980c090001d0552545810798110035072003406050303140d500e2904071000309946000144c00035200e45d0301940340003842c4043c0c4903005860300c82110b5440c144c600079604860a4404412508000c0c4100903004d0118041c1101d8552500f4074041d0442c3e0840e070580303004010f040081c0d001c04500e030348010050f80000c1004c0d4141c400d03022900016211010000c1401090182c6a400001e81e0324110a0443d400c034882008a07002e0000205030964811407949100f80b92048c0c28841c91502c141c425081d804800b6407802000e0010801c0594101624001c41e440346100c0d580c4141e80710390343c3d0040fa0380064204d0004007901401c80b00030a5446800800c180341410918020400318442c0341100e03c8040360311050700540b05c1c450603d00740d68400e00d203588104d4500944d10a80c40e60745000b5412031180d4000c4c0a0005400800c2d103d00d0581d001501e09007000780b6420800c84442d4041000036107000f000d00040c90941030200341d01 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 229450296 1250 229449046 229449061
    0xe01140d0204030f0b0a0504050303063003120702030403080a0e010e13050106020d0e0d0f150f05060f030a0c06080903070609080d060e070f0305070e030609010b0108060f0a0e 77
    0x3409801403003041144009000010810041c0200c90400e1003800b035100706541d00c07903620080f0340e07048902a15903041000011a9441c001686580d41c11089c2d50700c0422309401140b80302c111403441041ca01c140d0001414258520801640e95406040e900c02946001d0031aa5044914024051090300b4011250b1126202d603010f44111003000c0c0d809011000803408002401000d80803c2c45100054040d44104548140c8140c030031364003900740605400c2030340d42140c0d40c0300b10f5507650020a840c0c0f0700c1150f19624070550f0314020b403d40f542c1d00c5000800d03141020420008030a00302d0040f0707031081e4012a100e500003068500e40038115034640c105086640c0d200040e060561007440d1f001480546401500401c02c05110064030f07203d01d44600c1004030a4946c05420055601906c101c8080b40081c1d9104003664400d8002035441481031610700084804080030924241003590303500000c3c1d4403074000300075a580c085180d55000b0411654038840001100115000d20030394012000301000d100d0024600 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 229451546 1250 229450296 229450337
    0x70b1003170f16050106050109060e090c0a0c0c03030c05060106030c021b01030e070b0403150603020a091a1203090301110a0c020f031923060c0d050a0b12071e060e01 73
    0x10303400345100700f4070140b640c4d26000c2d00800650080c24040342c551440880d6451007010300d09402200a4046841030707d80015050b11900305c5c0c9610010040e00d0f100700d81c00941d8006040c0025031180e2100c2030b9000c1203150560403c00b050308500201071600340c0640815078002208442e00700f405200360382201c40d140c01200078000a401801541c0303d09000011100d240f80024800c40b4011040100d0b0451180810000e03200e051001070350050703201030240458880340c0d0101054120380c0d6240c1d1110400000818206031440340011402d0b04003048429082c1000c0c05640c0001c441600001d140c000c900b00040e0004c094603030080d01807441c288601007642ca041041e62080207800c0030100141d1143d00c1c101c0c00000741d4080040b40d0290400154410b400c1c009081402044c04000d103d0030302c0c888a03c40340041000405041c000d5840d034132400115142c0840860540750900c029281072802c00fa40740361000c0303100d041040303601d40842e81084103562100f061300c0b1050003441c00080c4080031590380480b = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 229452796 1250 229451546 229451557
    0x1050301031b0b041511010b0d02220903050403030f080402011d01090914100806090a020402090303190302250c09091b150806041503110d050f03070b1003170f 70
    0x2000a070000307012170b56991420000b0303c0303c070300c5960b03901000310910412070a8500001e85d49401803401881100186402490000400c503801949800041205a200240c6014907410b50104100140078024568481210382030741074182440e8805090603030000704a00d610002007003581d030045031203171802da20540381c04008144042d001d0203034141c0071031005800b04d01600c9800e01c034140d15034000341a10020030305521400341c200161400b01c2058003030001a40c4000c5820794140410010343c104610346040c580c82c50f82c937a40c1c0041e203e000e00420030740c00d9014004843d00c1c40d01040b441c0000a07240903d03010540c3c080b00390219482149181c031000b036070114102900f41d8480480d001c1380da4604801e0701126030030703a540d40c841d040c0c480d00180000c440000c00e00a051071030600c4140040340e800345924240c4e0b000500314000348142500e40906101104a80580c1a040041c0c0042484048402c090b00f24030000544010f0341c0c03450361030138000c002c420002e08545801082c50440512580191f030b2 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 229454046 1250 229452796 229452809
    0x304052109030f1e062503140916120206090f0f09190f061401181a0705010c0801050d12030605061c0e010e0a110303040f031a0108030901050301031b 66
    0x500d41c442d000707545074844020075026804c0c00e00c0c44240d01c211600000b1090700a00300800b05040c0601c03241d21402054801c2103051080c151120400704045c0c045c015261300c1003840700060204c20070100d81840070350b4190f900c00460700c0821a80c1c031000da568101110103180045071140881840da401241001e91403280c640c1e40b007420403040040d0100010521664501032500802c4a017601550381402c4071003a00039031100d8030456908000c9075000e48e5800c90064901011170f2130740751380d842c1c07811502c00081802c004074541c0812184100f09090098010b0428a401c180c6059818000440c4518002d241c014280790551000a00010300a070301c024041c1401800c1d4595840c507549041500104000107039000381e00d48201c044004106204907045000210090041c030713040340d2500d048864103840026814001000b0014198070026510b100540c4100602c20f8901244800811161816400b04402d81c00800141c1c0c0c40c1c1c4ea0143c21079054a50111700034005141124044400400340e03040070 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 229455296 1250 229454046 229454053
    0x130b010303120c050a140717041413090b0712090b0c070b0702010902060d0e010b0402040909020a0608060f150d0c02071e0b03010e130501060603020717030405210903 73
    0x841810781c405500302c0c100801c8481404082d0a6500031100c9209051660f03000505150581c8204000178005140e1240940d02d42c0615840d8a43d07100010b500941c005000315850754040d0b40319040210700b42c98007040e00c502c2000709902e42e031031360340419030010880400c11100a80f808010b09155105100c6550403c02c0c3c00c146190071801c5034810b074071118080d502c80d1401c900181086105010f20002698040c00060400d1558800c0d00d02030111355205400654071042641c0c0551124030103800200b580c108042010789580c0140118140c0980220041115000400c501904c4856065040b018141e4080300b039150080744680ca01d005501e01141c8031820044a9505a64002412019981507407070341516101da402d121008502e25101e980c00b002401d200400400c105910190350105445291058080702952240c0c21181d150f080100400d0313020485100f4071882d40c030644114200181c03528958205900d81c00c1d5074a626042618040026040010030b080c01041514000200a8100c = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 229456546 1250 229455296 229455299
    0x2070e04050307031e021002090303070f0515010e09030415030204081b030d030c1d0f09040605071701081509030f04090f180818150d020d050108010e0c09130b01 71
    0x100d80b01e03841840240c00050a084124649800f030101c494841c0000c0d4005215500b4480c0603d400b94104022842e07040c082400500e0206000400301c03c1043c0c45540640760340450b204140c500514180c0000303008034800810010002000001c50b0203039000c09070409001191a84202c6c086c2c0700d40e810180c020300658100d901c90041000003420440001c17010380350540203000c01201208c210405260008d4078000c1d104402d060b00149146208002510b6140c1e10a07000c00819000340d4169800c41d5030716520002c0040c12540541c24040c0200c04800021a0754034200c0344e43e0b030f40d582003407441170340410010200e480780c0700800454003001014184143c4030360b550540c403401401c40050500407141048000922042c0040000070b025a12005080c02d25644103803000703500750b919055030380040c805004090074030700c032001500056401c2c090159507000c1f8150260180c8030180c2c03010406a0400d241000c2d260408036981c00b500b50103985185507662a00840e01d04549102c1b006011150b84000 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 229457796 1250 229456546 229456553
    0x1508010b010f020105070c061e05040f0501140c1c06050a170606090c071509150c0e0d051c0309020406060513122001031d06070f02150a050702070e04 66
    0x21020400000b40ca074001c011880e800141c2c2a100102d502e000051108043c0713800145aa5028080240340038842000001d086120784040b1481503609035203840c41d15000d6810048240104481c0c5a14092a6156402d0000d21240c44d03008107008000c01940c513800704040c100681c0d000c8401840300a192000c410795600c05411210001d03152100ca5008180008105040c5071a6250107012005072880c5048000d80302e002d400040c103420765200302d071104604408248055010b51061990b00130014524001d40c401504200f03008034158051000d4a6104003c65800700f2440200003040e807410365020380ca00c404500800b0302047c000d601514003000890100e0f4000c0140c0580f8020032a84a034558a81e420360b040d103603201000618820308803680c034103224504114500400b106041c08600482545404441100a00701d000c45a50195040210030350344074200f41f00640c1d041c0060314417004281607010705aa00106180f14060304c40020070f00107442000200018810240fa2010f1411f0515 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 229459046 1250 229457796 229457801
    0x4180c0b0a02070b040e0c210a0b090a0519051e1006020c03120906090604030f050a020f2704020f0d0501051b0c10090618060b1002150c0706150801 65
    0x1c004001403041c01d0000ca00310741403404642c15100f40c0c100d44180b543e50000c8425281d0702c110f540090f29421b5914080942c03031035108441c0241c0181c4c0021030240c00b0740c1c0520005800c010442013078103081505001e4080821003881d00385a6002e0404103103641c5100180d440c0c17403800320390b00d1001e0144c0000c101c440900c00c01c1c0704003501c00c2542500da42032601820184d94800f50703d2945004002048035102a10740b01000300f25a04024102c181851f940c0c2d19000441e00420106a40c030780c206586040851410b4180640d035180219003c0d03865200c0c2140341c0071000c400b0f240d03100e800702c680b0b4046420340d03603400d00d000e50b418001403c1403120001c5180075806402c05694440b503401c031000d200743e40b03a00c4803c02d035101820540c00500c1c0403940a00c85401030309601000b9580a66140c6201018210211010503590700845000c82c00f0310f040070a100c443e40a09080b4400c6400c410789042950b1450805140c00100399610b542d203880060130705d48020309006013310380008108400056691064 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 229460296 1250 229459046 229459057
    0x81e07060b04150e1f08150f010f120503070f0f060b011e0813050706030b01080c0906091002010f0c0804050606033d0204030503040e0114090604180c0b 67
    0x149000c0c49001d004409010540c1e1003090300e80038102c0c126805200080d68400d985910540940503501103802481c00a0182a400c2d0000015600203105551800220300c101c01d030402a8000c00000f258545420051200e100d4064000d040c045204030b001844400c000340c889281d00010408003418107450702200580d82110104ca0543c01c1c1034110300c003907001b140d10301541920590002e9201c841ca8400311120743c401030400d4510782080740140d0116000f00520f2000d404103440c006481c01078100090000c6e0790080908010f64001c01c210402c41c5c484d0780580d28903020644e051505101c4c1244180d02410051030754004207450010403615082c0d019003140d002d14010001d0382e4994440c13005040e01c0b40103030684400f034050990b18032542980168079000c1920b600900070482c00c0c13450070030304ac10ba91142d4000c1e9595400420284005251040418010100c4454400c450600c0c0c0c40440c03090500145414400e41d07841c100700030300792084681d20754030950200d16420301a480b0100384e84e6a4014 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 229461546 1250 229460296 229460303
    0xf06030605090a020307050319090507090e07050a0302030304050613030b1005100810060f0504240f0f0f030506040e0627030412020d05010e1c03150e07030504081e07 73
    0x1000b0116464490520840b0301034000f65a40c14a50740d0b4501c44281480032a007107860b10181c0c3c400300e6402040060280c2409415401070124030703040d07004501072030401c0c180c0100388111091002080183d6000003200d04403003003566a681c40340e030400d602d9103501c407040e40090130080c1218204a01c0c01d06121009c81540c4080b5510b81c850508807030115031560003101c1e080780601c0d013240240a80383c01210030756120000c500d800c518240d218200e9011541526401c80d00d41d5185a07a00c1c9007454011702034070441443d624140400940380003008104031850011101450358840c0412410b8946270041d2140d140100304a5074981061295603074004041c1b218040c44115802c10001c2e01c4c00c0105c221022035040301050601d6030110f0702000a544c42450040320b02c0d40d03076145000000b41050040500c4070011010030411600c0166024003a82c001c0d8900210000e0b01c8442485601d0710032610a400500c0c0e031800045980d03c0345807111051080f001300e8031115403e401c000d8110f089550050000912 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 229462796 1250 229461546 229461559
    0x12061413170901050714031603050301170a05030706050c091e01030c05090d02010305130b01030b070806010f0f050a020a0c2d080d0c05071a071b0e1b040f06030605 72
    0x21403411100703580c0070358014540022000c000b0400401c0210454404407500c14007544d2803c01e40c0415965500c84152044021403004801001080304104400d0344004111019041907000c0b65182500c80c4944113009288070765a90114130380456120136150b0340640034203a408000c04a40c00d144006642d480d4241c0001e00b08406072650600c22401c2c0c07041808090b105c0054407a140d401500508001000034181c41d180898510201d008407111500850040081010900b401d034401000c4440c01407040e414888001049d000705a40601c1108800c3d10385c0c0f4000d80c64220048003242488003d020203020045c80e11408681071100c010001f11107110354125012208030b1821040071080d052084900c680c02601c41043c0040c080c0070000100c0e80300c0e01c20f6681194584030003200c0d08140744a221003024000c01c00300d00b0080134004081d41002d04038070802c01c0b10300e00900c00907400c9008201c0000e4004840a9207182d0f10880c00740c802802400c0d45a2040d1615464014001d0141e40308261040300d = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 229464046 1250 229462796 229462823
    0x801090b0307050a05010c020105120c03040209010602010b062b0510090e0115090209011404030303050103060c0302030405060103020123030109050a0c09080a0209220f060b01090501080112061413 86
    0x150002c0c0b42011110094100c111041c80c040054810555218050b4180041080b05203440c0c107010141512a17000d030f00c4502e480c1d00f41401403260101c4142c2050041d68501002402d06a890314182e2706d00103564071f01038509081421900502c220041642e1231017070300f00380a00075030f0300d007101c0c00d8000d031a400032081000c148104015030a0302c0704058800401180301609014040c2160000d020001c418107000c06071000740c040181440d481944140c0000b036031000107000f0480c69018019444001e4075041d0305508040c0c8030141c880606100090500002c1c21039041011f03a0b40c04440700265010707106a4980d030792000c2d0720b4040d000c12601c1040803464000b8020840f4001d118134030903502054010455407280ea07082c0544aa009460850720b418010301d9528415286006442c10502c200b00d25440210715190410a0b80c7d0094201814000607010a002c0359078480c40450448030700b1720059a5403003840c10b02d070009044190200700038400e0300c030411019031020415084182e1142c00d81e02d6500 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 229465296 1250 229464046 229464049
    0x3080a0506010e0a0314010b03030711030d0507050c09091204080109050c0a030c140d061b030b04050712050a09050607020703170901081612020414090c0702010c080c1c0801090b 78
    0x5080c984001a80086502c0060006c6405003048580e82d0304070800005074244076100107851908600d10460700500c04071001503003030400707200c40c0b0544109410020304051a9a5034141c848840303d51041c00303100810001084288200032102c1101c4805401e2581c42e51070380040350107480051020340303062040c40900c4c2128104420040304980e0001d4256401d41e00380f076007405c61151070b0048158000c04000102e40031481d42d02c40c3d00c0c04207510342141402d10b14021005010f480021403441c0c40b8914040400c5103d60704086008145001007400043c641d980b401c40d41d005191021019000c1d22515003003040e429000100c0c0802d07240a00c002c0c2c2000703080000c120009108400703140f40000d40c1180403402da00f040700180c5028242034202000000c0c848031402d401c0b60001c0e8400341642000030000981410300844080c3c024826801750b624158030b580000e001c82d21500720041604100240007428410f046c0010100e41a2031a07082e200e007450010000e00da0b02c0b0a0007a403004a160240d110045e = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 229466546 1250 229465296 229465307
    0x13030801050f0d030c080903010204061d04060b030a09140111091807090b2a0d0e0a03050a02090c040f1d151503090115090608060714031b040e0403080a050601 70
    0x785800030401200f144560b603088401d083e050204442c003c00034090720700d85507028006813020341001d9464801803041403d81411030f414006403d80581e02e000c3c802d1042a03c503c044951201040001080540f054580a42c401d00100d0107075445518022455026000500050440050403503850b402400700204e00300d42420f060350300740003164402004000e02002900a005400c41650040700758500c1c2c400402032500c07203042c00c400a60070817080c43d20500d0f000070300340c03080d91820703500c4440307030382c00c5554136560380b01c00c800041d1040024600044c840f040340000c5901400034407030382008090b507401c0c964000418142c07221110115440024164035040a200100701c0c0d4010030408450080c800d2601c2180d00c040d04401c079554030b5110000c11444007a2001d0014012124005084c0e85840e052a05000b4058240c0c0304100120214485c1c50100700c0c26250060100c10090034400c1c0800082c4280c0c4c400c80d4003e10580c0003110810060542000045108900c0d0302800e21482c1e0b10000110765 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 229467796 1250 229466546 229466569
    0x20301030b0c13030f0f020310050103050f0a0803011205071203090f050f0609010c030e040612140610060311040302090f0406050a1b0804060b1f03140709051e04051303080105 77
    0x401c01c0c0380f404001003110f0f8486950004d0280d40e110201642c1030b0042810025440504c01c2e045807110010070800904006240fa00101c2c0406030540306019901c0010511043c81400714049402c2c1d1064240041481003800405400711080f400247c3d61070060904e010310300c960700249201c0c0da0001030070b04003542f00914520008095030f18001444005440030300403e07a0690401158000c20380c0d241d19203100e404041e00d826246900e190a0500d00300d243c803034201c0851031040d0003074410310440d44081078005058800c41c0c1000318000c0e051090f00b00340b5010303980c0041e520510f540140002c038801400f40d0740c011801840103110b2543c0300c0c6811000da4880028003807014034880741c1241c2080c89003011303130f0300b2511582000c501c030101d980c0020002511030401031440407440705190192070b0103110380b0440c2c0080e00102801032802c100c0245c0100f816126850043c036540c08884019508500d59040c000c0c0020800c100c24202107400e6245640f496108402180c83c41d03001040768a04100d0080 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 229469046 1250 229467796 229467817
    0x1111c02150a2d0e060915060609010c030f03020c060c0a1701060e010e03210c0706030e07030b1e041b05010914040903110f031314090c0a02030c01020d020301030b0c 73
    0x64040349200c01d81d1030b071820055100207503a0f60fa00c00d092084c1d041481083d010320034100003041c02248020607082c031200c015040b1807040c0010040b40c00d00e40d03004011320780d000f60181000107040c5d540420a401a1041c00380100150060324108003c10000d07401070500801540e855031031354204404400754101081c05001c010803402c600d0040190710645224451203000303000d54601d500ca061800c0c680704113054490b040550301081c0c2c001c2c0b010040000000074004d80c80c06001c83e410404400da100c4002d800040c05c0c114240c0006a007445c0300c10340072510152101000801482c2a0810103c20700c205009090384104580780022998031404900e0f0603a003400d000d4801101c8918104002401407081c03c500b03010001121050100c010301000394a00c450318003440d40e6918134010903c91641c1034114841c08004051004929111801c2069208071009010b5980d50188070041e8558024014000350725070000032200500f21084e0007842c102c0e8451092115141c032006c500c0400d9000784170545 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 229470296 1250 229469046 229469081
    0x90e07110c0909010b03030403050307060506030a11101704230102040e180a050d050403060f1a100207051002100b0108280603061a0a090c0207030201111c02150a 71
    0x20046207800b201841d0080c841e000006072080c81c1c6004241140c000c0da2003641c09400100c1e401c8240200c43c003400d0f03807062040b400b510300c1180d83d5a600ea8104135209075030b8092080c0614540d1001d00495600c00141d07000b491200c4039240c1031500311448018084088072996503512420300c039480c14003d4505849802d50220541d5583c5040d211001c42d60a08110311486150a5540420707424401000001000d0703440365504c3d400d600303004e81a2101c2e004c8000c00a494607036188050f0f90b0540d40a0b03410041200e00c2c1114440160b0100c0c58008039801c9550301400b00701040b000d10f900001c509100c08000d10060140400080054950700c5080f070340703ea04040d405e8425042200903204600d00440d080342c0c0010b466131240c44102c22550030000b00c403641811418042481c1c6090b43e2620010080000f05008070018540001d460320005e1000174148448424854640da0b810300052f1401485200409601c0719036102c004d60b41c8041507040150404900003007a40d03d00c0c940108046401d101018 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 229471546 1250 229470296 229470313
    0x30304050f190212031201080a0c0b0901082701021c0501120201020703020907210b0f15220801050a0b1203030714030603030705100618020c0a060b1503010303090e0711 74
    0x240542d280740e9044e1640240020401c2d000b5000c1c85409580c0600800801070101c10350529001c002140180c0201d1f03981c40c0180086461030781e1060040350f1045500c440b20200b003c04990b15002118500c0c0c00c0c004d43d500202d0541e0b8540050102c032804049071781170a11042c0d980b00c2c030030544c440e00000040c5c0143c00c03017482840035040c0014020340114051070848003001d0481c1110701054503503401200056101d002c1c10b074031481d148084001d004811034042c0070401045654021a202c3c0007500207072a4210100403200c4200403100d0f40040c412000244814600301030502c00800502c3c02907031282d40e500f5500c2088440000a59220f9007144c0c0f54018404e48005072030f10250801080d06a0503c4200301490025905001c1d03070b1160700800c44041031850420b0601c426100810590380e1100b48148240e000d03021303000401441c0a50016400200c0a4440022844082c0081648035061000000010406038001001c0003100c40300e11003c0200d44507054110780104030b06422881a0f0b000906 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 229472796 1250 229471546 229471549
    0x601060309060f0906021806040b030705130e04030906170601020c19050315011a04081510170f0601151b0230010b040b010c110109090c090f0504022104170705030304050f1902 77
    0x5288000c1d45901880ca033b04d42d0b42d0600b090300c60007103604800240c140482040b403140c102d400c2c60a0100b0055154003e80360000000390b841c689117085600c507036401100781045449480c0124080d00001d400e6900d42c00c050b00c0c058901c94800c1c802d02480d112840c403552903c00450701503600791031440011307025944410512001002c400343c507c84c03041010f0314000401d501258003c80030a810344024145900e0a04005c80c202041640144649820365403010314060f4426100c0107160700780031280140c1840e074004220000d00440302c10400705240608141d0159900f403a00c50440c24100080c04040c85039002c0c002560101c0e2141404901100d0706007002a1940004050040c410702d000f00c09103036640119000e035141e030300354003000c202c5003441072040a07801c201c240040c0ca82624151b02d448501030a034254200000d1644202d484000045020085e003a51014125004480030720b0311502d103820051703101e030b0080c2e030100c0f0746114500d00340d8141c000210f40054030394410300040000c00480e40 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 229474046 1250 229472796 229472807
    0x2d0309010203041205190b0405060f150402031005030f100b0a0e040209090c060d0204210f03050c011113050f150f160b0709150309050601060309060f0906021806040b0307 75
    0xd00466450044140c03680c51b03503a1880f02c41070698090040304003181824108281400006003001c550244201c041001c4402403801d51b1401e001c3c1039030010b0b0780780d490340149507900c07003540c0003281d241c0941e6844840300d0070300003003011505030390724410042502c922003002100b035aa0b104c1d040c00c4500c0200000d0152801b440840c0e44000d482c01170b40d900c1892800001c1217540085d0043c0780f8940c1c041010701606641482011403184e0344d80d03000c1807006043d114040a45c020460080c02c000b000502c216000c070080d006254003000a1365069155079503c0c103400c14001e0140151070007044c014000e43c0c6149807016204650410461403a460301d04c007003c0311043c03a0721101005d01c05450011150b4001400d0720b00540c03289070f8555a0f01c5240303050002c103280c0303808403030071000c00c240c2420300c200c000c074101062150445200e070a00051010792450a00007400c840d40742240c3c3c40d0300d0010a07900340001da4008018196051140d00f2800341d51101700081e0b070045000304c0010800504c0020b40060144 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 229475296 1250 229474046 229474079
    0xc090115050702151e03090a0204090c0e0c190e0a06030209040914060403020c031b0409031b03020609070602030f090d020406030c0801020403052b0e060c2d030901020304 75
    0x5141c038510b80400c58020640364004031320070320080140080c9100900c8400c00b0340135042c109403050326265040210041d650340034241030107031095680d01d5000b4100903c107034408000300310003502d1003420f1401d400b40070182c0d00284a0b4000300b50394803400010f26841044004103070040284120001810280d04074002d401400c00c0e160003a80da5a1104080740303400407110140040d13207004104c0e0b40781030b00d0001e060400b0341400a0281d40180100402550840c101d84121001650300198080c01b505003280e1a5004044401c491220341d50841d040c90f60102d005442103002c0401ca9a1440d0b807810102c0c0c1d248074181c400c1a078214281300002540c60505040003800e07000410115805459485c0c100c5055072551215800341e600140400402000344084403100198070f10125413805841d411240a0400d50301c403404121046441d1700490399484161528003568804a0f00041010a841083c0c2401c1c2e82c0c85100060b6401d420a6200b1000400c4440291060740a10301702441c000c0c0480301b10300780 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 229476546 1250 229475296 229475339
    0x120e1009060b0618040b01030b0d1101090b0a0e180105011205132a060801051507051606230307020706180305100507170f060f010302040909030503060109080c0901 72
    0x2980d01d0b9070256030b07a0304040e1810600407844003404e000010708000c1129019a02e49040c1420501b006409644840544000c15044035400b401c03200c0d00740040f02e04051607041242408800b081e00a0525404544034401d07400981c3c004c101800102485205c03150b09214141c0040c4010301225000c02c0705820603a0080b4040c0004030b01e8021756540c0301d44c0505c0c1c003000340c1c032050f9001180e4030075001e641104400a003001d00300342c209541000085103a0000b4a81c184800d040c00007410010803404011840c5c10000d0b045080035065215140248074030400c401c041160482c041070700140c107102c1c000316809144603030010038a0b9480c0c50010b4510714100303e107240c1d4160100e100000411014802101c4010301c2100c0096203140c0080c2c040c00d02d07080c990603207148070b0039a0100306201c56082030080c2c00c19030840d031100c1a0007003100102d02a110790741040c041e190402050b1001c1681041c003171400380e502601c41045158456542d80d550700303c00ba41050b8882d0381c02c00100403880300c0c14840ca440904 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 229477796 1250 229476546 229476551
    0xa06210f02090117060109091518060510060e031b010c0c0806070509040501060c030f050f0f070f050118030c0b0c07060c12060501050403080d0b030a05150601120e100906 75
    0x3550740002c2c1c2c0c0c21009900040404003100300d4400071100c00d1010703502400000d0010400d0011944070104c07100c2e1342568403051140d80d44e2140164500301c0072a403154230f502c0a014000791500f280da81c00a10014414100810f00c5400072030310500d0045952810070605100108080c1f0742500115061003020b42c1c10340352145602c002044d183c00074409036104003950380f18150b4450012003400100ca10581c0840c040111203500344c070019500c40e07208035445000d45403040e240c410212500342c081c800c140341e180342d854000030000100502c080701000300724011030080000d07001e0b01c42c060650f20a490350080001d01141d50b02d00000d421210040e4011500d1051306052203841c0d661501140c44100d624000b02d1303c50020240382e81c0306409050060602842c11030b040614594661205008400150500e181c85100d1120300741ca081062003003054001301203600521401c0382e41101d009058501a00080c40078020404407055030050b802078081c02c1c4010090010b014882c180240040d082c12111582c = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 229479046 1250 229477796 229477823
    0x6070f050609030403020312120a152309060405010b0304080d090602030a1d031c0207050c0301020f0a12090b070e03010b1f170c1b0a02090403030b0301050a0621 71
    0x1001001403030b00c55181d00b001569035a046004044c40c0031003003000b001c1c01c11070410000000303440d450542a003120f20100003184100006e00c0c551185125504203552000c4264150f411000d0000310300d403c004402d5400b410340b91165414003058074002d0084254245040011500080d401c00003042c1a110304580026040020740c1c0d510141d9006a60001030280c94031108803007400c46070341c00e2071600100b00c000c40c50411300e030300742104869184504040e2254045009401e00105021000c2034400080007159a40ca00c407800400e542c0103c02e407a000100c400c02c94030508a414031803900700741c8d000160b40e00240c2c0e81100450301c02c0b07400748045030103540b0f42c81140300e11386400c0700300d000c1c007811403a203030142001300c00d002040d201582240c460013103d0b0506015245000c1340490f1007042280c800b80c640920601c201d24a00710302508004c0d0001d52040400040c075900d9408001700d14000c4000b4007903500d4126008054800c50301446049083c8145940388020480c10f04010355481a0070042004 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 229480296 1250 229479046 229479053
    0x603021f320a09030b0c030601030c0822020613060f020d03020c1002090d120906021005010509161404090501050a1203140d0e0102030103140114041101050304030e100f030507140906070f 82
    0x31002507a00c000b2014000c01030141e03568050040310bca544075450f140000707190000440c03071004010a040c0c02c041400025200a548903402210440080d003410103240c15030b144070082c4040c4582e46d5000c018040d05120849152181c002c4980d500040303001061800400107451000f58016000542d2008490592400113050b03e07071021008042d0352141c40416150400185c206034a40450002140c600b4005005950f01c0c3c441064000c80100560b1101501034203080d54103d04000c00103800c00000310300015084840d4110b06d041c0c0f1000d0703801c4410b0a542c0c41c942030b666950050020003107507010b600e43c1d90420030480030380b0915100c000c000ca240e4030300d18034080c02c990080c1c0003500d599052010030485010240118060f410020f08011010b02e040c1d201d403880107441460050400500101080c10305100b03020309016245d00070401c116101162401074482c180e8040000c01003130030716000404450054080f040d8a4041c20b01c0355151120750010040c0d154040036040b40d050110b09005e8020 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 229481546 1250 229480296 229480313
    0x60f0c0b1501030b281d0c0c0c09100321230f300103031e05120c0a031a0d020f03030d02040308030901110316030903030603021f320a0903 61
    0x214500c070303500c040d0b800e10b2008141200b034940d904138511044040c500c0000c034082c0c10321200d47c8002ea0800715a00e42c03448062060510103040b1409074808081d80a003c0c41c1e46810581070f086910843d44444041107449080380140e0000d007404c80803030040401c201300081d201c09094401c041d14846075181482e2090807031305c5134020545074206030004202d012510103822034820402001071f070008a01d98510b9500a260131580744031000d00041e11402c15801c00c1c00f4005a41c01d20341c0e140d000303100d00e140c101622111034022021107000a42050b51043c5c141007100c40f011306141d0050801e0b00b00e00041c0d000e221820203800c10458041c07108004da6900a142032000c0c0010318410300d84190b41c0d04000d40a0b50030340304080b60b00e482a55003041804a0b0046e1405207004a00d9141408244d040e41401e090b0014401380e8070280d003025404078850f144283d482021140404a40c86000d000e100f5004009410305200b80100344d20007454919142c00c0703078480040c085040d203030f1401c20021901c0c2d5480103903 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 229482796 1250 229481546 229481569
    0x412032018032b021014010b0706020c0703030507020112201303080406020c030f0106140108040206070c030501020a031a0f010507081b1b0316051e120601060f0c0b1501030b 76
    0x1115005001003c2840d810b205941941400550600c02ca04281c0c4000b40c081d01e040c415066500d000144100800c0440d8050f1420101e61a040c1d5828942e0fa050240140d403000000300c0c0044d030301c26000c12102e083c611071041585c1c1440c2510410280c0c0c00c444034901d91145051410741c0400060000010300700030700800141080d54041c160450010b020b05240200c2d2141081050b414444240070200b4180c0650054401c00d05c1c0406c440e131124000301c2c08500ca40c0b1005031804101000c00701c244101500140007031202582d040001e0401e51a6450200c0b65a56a5551020900c030302c200c0707298825006091071038000c0f0001481c020b00d544445840d0600000d14060b0341d04050849500400d075115000c203402c1e0260054040848a001e005601510900031244500015a4403080c02c002108120345041d00150400c40d07a102d25805e0550348490901c241d20018a21800741820644110030488002d54800407480c0c081d02c0300304000641c500e9508001d810907540309024001d03540e94000c1242c = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 229484046 1250 229482796 229482853
    0x126011802090301090507081c021b0a03060f0623060d050c040e0708010f0b040b0307030c1103070b060a1202010c0f03030b0603040f0b010603050712020306030a0209041203201803 79
    0x205581c509023080742806c1421903048060f46010600759000b83d0045080503411059070ba040643c01095800110815003070740015210625102c220380380310059034080f00c1500c40304600103422020950305103094a9042c4007503074000209100f20714801040b90400d94000c0c004a2030181420385803202c580c1d545504958980020702c060340100908503085200501408800c445c0501c3c00703041c41c1c0c0c0640c180c07101520316420591746100020314144900305c0c0840d03040103041641c0d40d07a446810085201c1009440713562056860700400210703040480300f074402460781038407900c914250341d0300c41c58004089250203030145a00d460341c0d070409070303141402148200e07c00c05020f9981c01c103509000c075005105802500070305141000b0b104d09260002d01000d4203041482000d6136035500d180101c0c0c109100510001d410041c03900500003042400141a0b645104680d820810320001c0c0d00c440640452828251100350410081005915080c261801807810040c00300c0e44400480e40c03a0b029007410a82145 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 229485296 1250 229484046 229484053
    0x8030906040b0919031b06020a09030203121e130e040f050d0206040503041a0c0115082104030f1109040503090f06090a060503130f0f0201260118020903010905 70
    0x11003004102080c1c0c03a0810241c2e4002c0805210713001005268220f40788021742806010500c5507051001e10300c1012110f41d0020084d0744a06a0706070140080d009400128400c0c002d040c90b0701e40c0d10031008259076107001c0650120520a0303c40c0100801640413030300304420150400c1000ca0807035040390845009a1064401c4000541203040c80ca042c842600113642c04c5410060030302003c207100105503000d6410755215070682c42441c2da6019181d00c0f40c0041c0c429554245040c0000a4500c0040481180e0700c0205941d040c203660203c901d840581d00c024543c441d40b00740070500204109200e0381d005144100407000c60030510341d0010781070301021581104c0716840081c2281c0c0320300380724010040c810019a8100e0130104d8190008002a1082c00348a081141c0030001400101c11280102003940d04501242182c0038142018110030340c403001c0580c0401d0200d03000084201080390361000700f8500c0c100c0c200659007000303a035011170b1060f080d00341c02036502400b03013801c1a6070a1042ca6605031082004 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 229486546 1250 229485296 229485301
    0x30f0c060609090105070c080c07091a011106070903170d020d09060f0b031213030c06020a030314041101030506041e020d0606110a060b01050d050c0d050901020421020d08030906 78
    0x300b1602150051958001c2e0341024140420550018000c11007181c0c00414a81c0310400031034903500e403107501c1c4e0000c0c0d070045c01e08103500e808840034001c0203a144c1085e80d4000354521070280e4103607185401c1d1040300018480034000c2000c10314226110909146074201e80f0302c1c05102007260002c1c0c1e08419080c0c110315a4406410007000403901c900c11100e4200c42c81840350928810000341c41d9400954400a00c0b02d001543c00b26030046d481c499009160b101d4441c0740001d407034901c001e41c0c48801d204100c0203c1c0c1b5101e0010070203a809800c2c14801d40e80000b05d4050759030540011009420068011500a901e800d40005d141032081087d00d40032007000740040e21000300348900419165070b684400e00740500007170180e41c0b003203011803180082ca4100f1000304042c5450401294140300e00501051002d1504050140c1d2582c1d0a00409442031440340600064898440007401c0384110311400c907400820040480200984504094500c1d00040c1505001c2030140c49240b9070368422982c0da030058102d4000c = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 229487796 1250 229486546 229486549
    0x71503140a0b01020f16030303020c030f070803090105091c050a0905030f0d030b040b09011a0415030c0305090d020601090e01090c09090b070e030c012a03110c010c080a08040203030f0c0606 83
    0x450010a55811700a10301d040149007840030a600350302003e02059000034010034a0102001195684801e211840380c0c2d8200c54103100d051600f050380e8000c2ca075400e11002c684a03102c0002c1030298501c1e19150720000c41940304040c0c44079400842e12101f40040200c000603280c0d42488081000100240502680c18511074020b04032403008000900c0307140f03080b642941c5600d800c41e5040c15a0384191107a0a100c400304000381e650300466001303000c0e03484d01c96a00d0058a516800160348011591803c0c401a181c0c0c4403140d444460300b8017041c1c01031f4000c000401402c401034208102030505940001044141622a00c500c40826004143e016844034030079810041610801540a100391030000c3c26a0001c000180d00d0311400030702a8100102d0302100c1000580128001015400d01c0000e0040d122441c58041d00340032201e641d14007240134100000160b94022100107000c0c070f0340041e0051500000e400c040c0d403200c401503c1a6050701c8148000240c04030b404c0300411a03040190000c1c20350b46410b40 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 229489046 1250 229487796 229487803
    0xd0e040c110115090c171515030a09060b060306030c040c09180204080d0207230a0506030a0606030b15040504050c071703010e0c04030312091103030a03020904110903071503140a0b0102 81
    0xc000410940f00c9a5524017042400c0044d004010a51012041c1601f1800500104c400c82c0e615101c822000050205c02c05042d0310012029124500038009204038100304001d82c00100c82c00c030303090b4102d070240341014541503101c0c0b486000349050500600da103840c05640e51508003040e105416070b000406210a01080200b4001c1c2580c6100418030503042400044d949280e89124110307071444c1c4102000250788107101c00c030107010045c01a07a2030b890030200c80c8005d04036500c0340c000800d14150b801c1e201030803c201104030801040a1841c81c0c0761400c07050100500005141c2c0c1e011103014001840001e0350440b040151036080c3c00855100d50502000d2446040f002c2d068402501e0200f0041001071740001410344610810b000001345039080f814200702400d080071400b941070000007014848903405a001c0d1043c05000d98007044100341d1220100440c0c402c0001d0f82d58103603c01e030710403c0720b007241020b040e007801c03041d107030124102c000440c05c032a82c48010380e00e040c00345458915800322540d042 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 229490296 1250 229489046 229489061
    0x110f090f0406031a040501110a0e040614010c020d1e080a03050c1c0c0306150201020421080f0309100515030d020a111306030b0103050c120d0e040c11011509 69
    0x807502008500e00d1541c0d0640004025003008802414030400541801030039444103d0741c0c0d1800d03442d40d0340c415442400811048c903100e00c00784100c0ca403000c0071500c02c0c46c49801d00b40d9220107840c2d114124005400f00419403690342d03000c5400c85034400038869807041258241404c941f01c0c1c41115241c60010a02505503100180084907000003840040f46101c1e4064100c1460200079000140e6100c034030004030081d0680342c000c40440d002441400440c45e40c154020030441d8000218840021003c10b00513191000c190313800340964005020044e040c2e50a1030055401141400450741417000c50500481a241c04407015540d000f280c1e10600011705081c4403150903100c40348040e0800c0390f02603441407040803010580f00c0c05000e10f03800580c00c0c11304c1075100d0b10141d60454641442036a51f0314181d0741e40d4801090340d60148040114024190500280c1c1c030200280a85590110442680601000f0142014404100801c481b102185240f0a104440340c8602660364080e4080c240014072041e20340c007 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 229491546 1250 229490296 229490299
    0xb01050306010e0f07111510080c030307020d020f01120e031902060f1b070c030c0503010b01050a080f061809010905010506190311060f040f060e0103050903090108060301110f090f 79
    0xd03804004003541113a4840c0e07400001070038451383c200d8070404a503181c0303400384401c180500100004d0144100d260741e200c50803996044106c500c449450002c0c5503c902440314000d401180040c4503100610b0702860001e254141131414507280c08040d00c0e55030648943c1303540105242c00001c0c2002503240441d02c071580030a5140024902810000e216002040c0010700f8110f81170301404c403000d091182d04080b1182c0b03d4000045007a2551a82080941d5001d544075051180d0f28112901c0000e50144040d6604030819071035441481d543d0301410341103064014a40e991004142c003121008031501c442c3c1d28007483c804800010603406514220342150009040d45204d20483c2040e40c50841c000d40091059a9100081c0b000c0c410100f0049903e50240345000c121484000c500441c100d001040176008032001d44d42c80540e41c9803036100540c110341d0306641412240e00b04002055095019289071500b0583c09400044e280f8070848451a40e0340080c0e102d0400c4040025007050146003060b0182c1c84140d0 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 229492796 1250 229491546 229491569
    0xf030a090c1202011209020f03011104140102120406030e010b1203070c0f05060904110c19170301061b030e030732010f0c060605090f04350919030b0105030601 70
    0x80e800181c4005c0d42d440c2c0c00c8007440d4803411040704548401144a845200c0a0024407640d508405c0c0f03d00f207034009010701d10000e04002c541e0a00c4d50302c005450500c8403d000d84e084c2c90103003071a00840103040311110341c1410b90348642503510b840d10360780741405d07104081001a544829080c50f1509410150794006606081000d105000680e1004202c40086c402120001a400d03047d00080340c1d0f1f07000e603401e140c1c01c50003032000580700d04030034425490704a4030a00780d449180910b15611940b0340802c2c055100043c035401c1031b01d039a5100d4007200c1c4080c3c6001e030a25039010312040002174034101540d080528a21aa944006140e003007120782210004c031080c1c0382d80c0704480c40c1400205408a01594842004405040301050020b10340c0801e002d0a4060001c16807854083d00700b080f07446042c0c030210b444490f0f00401c402400c1014480460040c1502c00e500110301c01c4607000e01c00360300064001742d03000c600440c0f2100c0705481000d03441c2c000d40c4a140a5000c40d851309081606222050340200c42040 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 229494046 1250 229492796 229492829
    0xa0908040b19032007030c0212070f06030207050d0318050106061101150e0403270e0402010807050a020606150d021c060f0308040e0c0d0e0c03010c0903020303120a020f030a090c 78
    0x20400700d074801c49000c0c4804098172a901ca080032128440000b1003e508011719280b82000304002240600075035024003440100b00d503454204400f284110b08029080350490007500c440d461080c0c000e00c1c1d07009040c85424180456503225a421108194825070125001c28003800c1090000c1c012030080110340341014450920b0a120000c401c03600400003000c10104400c19240e8407001001020745011809507600c009443c1c2d209194035040640341607010420700c0c00020740300c2d0f1151085a658200c15030103088142c50b04000c0c400c4403c022410b800e11710509002c0c1c050142c0c0c8a2001d0441c54942000310000100000c03110320840701c80360401040617210311820300103c2c2d0000211400c40340c142e00364490980c1c8010034800f5a000b80d400d500222070070b080100780410700001e0390700e4001400720020425903c00c02c40c00d40c1c0c200c0007071100940540040c02844114000707021031a81c045c010a5025141c00310741c0110308620790040390494034486e42c404554051000c4006490040d14501d00e1141d07244 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 229495296 1250 229494046 229494071
    0xf05010303110f10021e0a0504081203090c04050720150a27080403021c03140310120228030308090106050901030204020706060f09060515120f0a0908040b1903 70
    0xc1c03816002104084c1c2d000190700c456407000040d4a03012418039840c540c0c83d51061400248140d0252141001d41d2140c10b01403141d4036070540469000b20052401842110403001c1400040c0500804540500c01030385102800c420f0407103030418103e000680070748400c8080f8031041d404d00001030708600c0c8092801c40c42d11408480b9454002482d04142040c804041480c40c0c005018800c0c3d42000350042503a4048041091a07070b10407040c0d25100e0348880040700b003a1700417202d141c0402c80b03a90503200308000d0b00f04070b8030300f40841d440c000d60300207001d422000c425114a0700e0601100705003041107009101d810070605912044464010840d04022712901d03203000000750b80c00320107002c040e201e0f960000e070385000c10080c0c0d07001500522072420602000c1c3e9650321480c0080c0000d1083c0303409800b0500d42c1c90300320340741c000c1250441c088003000b40707241d620348400e010044403000b0202000c1c1d541d03500c202404941180003900081091030a2266604070741c10782c9599005081040720141820601c2c2c0c060321 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 229496402 1106 229495296 229495303
    0x5090c0108151e0f0d02010f030b01050403050609060f07020610050933010f020601081513050105010b09010f020c03250e1e01080a030c1b090f05010303110f 69
    0xca072001c40c10300c45c90148000c8001e00040013a58040c00c0304c0d01036403100d041494180b41207070409407280c0e940b5143c010305903007200b1907038005401c2060040300101d0300d940c8401c582c80600200d040c4091030380c81c4003c15000d268401e03459900040d4100c0443c4607030301848d0401800c1c400804044502c002c0100c10611916400594404d03004481c9500000f0b13810b040740c1854004124204804800b4041203402600209000c000a00b003e030208100340102030103041000041541d9044400026110800000c0080f0641d000141454a19a00490045001080485040e122144641040035402d565402c0084180145001d2240c040380d4110020340c2d6882030030303c40041d642c903424010740d80d080c10b10000303000421800d20703074000840b564454104401440702d024901780d03d030841c02080d2006402c002c42603940c0d44004101303150b88a0300b6a12100c03460030161881c01c2c900d0081544 = true := by decide +kernel

theorem cover : BRFrame.Cov 229316546 229496402 := by
  have h0 := BRFrame.cov_init 229316546
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229316546 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229316546 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229316546 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229316546 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229316546 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229316546 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229316546 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229316546 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229316546 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229316546 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229316546 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229316546 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229316546 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229316546 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229316546 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229316546 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229316546 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229316546 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229316546 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229316546 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229316546 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229316546 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229316546 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229316546 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229316546 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229316546 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229316546 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229316546 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229316546 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229316546 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229316546 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229316546 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229316546 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229316546 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229316546 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229316546 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229316546 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229316546 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229316546 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229316546 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229316546 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229316546 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229316546 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229316546 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229316546 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229316546 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229316546 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229316546 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229316546 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229316546 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229316546 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229316546 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229316546 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229316546 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229316546 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229316546 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229316546 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229316546 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229316546 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229316546 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229316546 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229316546 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229316546 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229316546 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229316546 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229316546 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229316546 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229316546 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229316546 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229316546 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229316546 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229316546 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229316546 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229316546 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229316546 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229316546 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229316546 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229316546 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229316546 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229316546 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229316546 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229316546 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229316546 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229316546 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229316546 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229316546 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229316546 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229316546 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229316546 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229316546 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229316546 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229316546 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229316546 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229316546 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229316546 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229316546 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229316546 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229316546 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229316546 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229316546 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229316546 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229316546 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229316546 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229316546 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229316546 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229316546 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229316546 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229316546 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229316546 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229316546 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229316546 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229316546 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229316546 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229316546 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229316546 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229316546 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229316546 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229316546 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229316546 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229316546 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229316546 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229316546 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229316546 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229316546 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229316546 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229316546 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229316546 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229316546 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229316546 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229316546 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229316546 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229316546 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229316546 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229316546 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229316546 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229316546 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229316546 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229316546 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229316546 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229316546 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229316546 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229316546 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229316546 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229316546 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 229316546 ≤ n) (h2 : n < 229496402) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
