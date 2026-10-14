-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2682
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T07:25:37.710293+00:00
-- url     : https://prove2.me/submissions/34cd5d14-fa77-48bb-9c81-052412616cf4

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 482194244 ≤ n < 482374100 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 482195494 1250 482194244 482194253
    0x4060603052401060f14130f030503070c210f060615050408061005010819023609010b090402071502070317060108070f050901030908031513020708030f220c03 70
    0x19050b00b1003800c03c170021741e0800080b90701103410644003403055902559006040d032031188402041d001190a60b80d031040010801000100400002d40202c89000c40c0c1529551120f500b1000c030000150b08035280038000002c1412520312a034818030824000a0361561103c500e02c1540c560721800c0c0208501207020000004148011a4850400100103040341e0405d00081c046d814060305503008240c1e10b03084140c4000c1107a0460303150281ea400300074002d4001d0031240b04d05011001041040b1054034000b0207044c14600c2032641a11400c9000506207410780c1c00b8070000750482d0409581c41500e1154501e44e00c80700344010a58207000350350710300005042214481c0400c2003d040c0d81d0402400d01c00b04104035600240c03140e0754103030740c6c5041c90741d40b821800120040c00b64a07101a000d1900001441005407014000824030801a135000769081c440c1c40d5080100c0c01168070107400d0020800005081c0411411919800300d03924100c0c1c03042040c1c100214140c1840768204469800c4142c07014020702 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 482196744 1250 482195494 482195563
    0xa0302271e060303090622030f0623010f1e0e090a0209131e1505010f0810020705061501090911030a0e06042012010203131a090d080406060305 63
    0x42c0640003035251110340004a43c0e60312521081145410300074400190f50010748031010002c680091420104028070304003080108100c0000107803070303070f11892201c0302220b007000198105c803920b900b4244a5842c004804140c02d460952018022408140100708603403643c0110b80590403a10003010401d41078418030031910000b03861404c2607110018144005215020160710700c04038212100d221071720901d0000e202c4940003d24180711420080046021140300c80f603042210740c3d0001f113801059800c4040320480c0b050180241a94210304000b9403007070031214458013554018500411005ea0f210300942c200c130f900104840b030310302d0004203100400c50740b4055060164081800f404441c1081c0d0f03035a40001c1d80e60310341c01c4107803031100702c01211a640b206281e140c0010014000d541d285000c0d803103201e903610a40300407156040c0504e0b041c2e1200c9921454144030344031000084c401c848140005035080c03007004000704ca2050b00d031480840003920034416840b22a69200d5036650b22854030100d00c640 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 482197994 1250 482196744 482196751
    0x3030c020708030319060e0f04060903110312102106111605030d0c11190204150603091b06051209030f0a080609360a06090c1703090a0302271e 63
    0x7018115408d00c5240004940b5140c0c11590103000002e0a0307038186400d444090400b80e5043d1035000c007140d0100500c180c1c1d02018422121400380300b46d1640c90741c404240401103a0406000350703007003204180020310366501800f00c001c4108000c1e41040d210401c00100700080440455480d00049002928203003e4020310325241d40c642040105c6160652041d5610b908d803045007081240700030200c0c41513449070b03400424100042d02c0070310341840d1541c00240107007840748412154800180035214608248045036000c1c0c41b4166038440c64100003a01e060344500010307000c0ca82500080088201c1e04100d00001e0001c0020741e11400c1c210300d0810100709405c0320013000345000114003a000c1e403c120300904041c10069444d94800c0d81401c411844615100e1002c0d802805240380180800a01000708000d00444940103415840c5281c0c070549540c6038060f8500d4190002c203032000070b200614240e51a648816003007480504250003080c00214002c0f4280c84d22078007401c0c9000311a0452240070f103035550 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 482199244 1250 482197994 482198009
    0x31101020705062b05240f0303030402010c03091d060909070b09040207060608010c171008071401020f010c03050601030e01051003110604090c03020a1e0c03030c02070803031906 78
    0x180d0610305400b01d0468071590741a90780c1c0d0b104c40e0090f10406481190f03075000400d6004002c01003460b000300c040080003104441074110601d0034400d814549840c0a40e20001c04010b400b031401c5807195070054420b82840c10049081c0001a440412500081003104202400072000200d080c2418418400c05640203060510240c01408090050380301e068100c0b80d9840c0c0a41c1c0050351001c00303007492802401d207074018010f55400c2142d828201544400340701014080b42104850ba5100c043c1101d040007003030b00c50f542142d041945c04105584c995071107890040010700540f4030305a62080802c0c01c60703050021079000b190703a1f28180300c0c040d64076119a100e000a104000c1002d414180450a01016079110003403617101c6044600740036855a10503140140003044c0140800404030b14013030003a4104440c18000200280c40722280e01c0c1c004240b01d00000f0b40381c0c4a046080c91644c80441c054a002c151350000c0d4454040700003681441003004510400002007005003500004024405850165001c02c0 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 482200494 1250 482199244 482199253
    0x50117031603080a02090a08030901081e0406050a18051b030703050606060706020c06090a21050910090807140301110c070b07030201090f03030203090105071103070206030a060b0a0903110102 84
    0x21088074088000341085805043c81400c035a00c000450001c1e1080c422002e0b0441000500054268070010107812000c00c00d80702c62000e9a01c070000e00c2c030b0080c01e4460034681d02c001c1e0360110300810400e40c8010340024490702d02250004040b010514000b001c1c03041100d441c1e00090340034011502d1820703608607102048001d000001d19644845580b108023a10b5248500300026144080007030039411254074440f140d00350384861030308240386521200001010341d0b02c8079035401c0c01d2400102607032103044440b01c41c0e1105420001c8503400e004908490100240030300403202d0011481d440d041000034003e01d6800c0f5070318030384040c0f00b09050030740b859010a54800c1d5421711810b8000b0170302080c00f00998210b11809926665282070480c05400e011501074000410a02e500b02811341c950000c61081081500078844c5444002c411210b842c0928110f450a07003060290000502d010780086820404c40603000c1007590f142e401350502540428072007004205800c004100700302c054400d119400c0c1c3e0900180 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 482201744 1250 482200494 482200507
    0x180a0806091015030507030c09050603010b0a180b031e0c0d0c1203120606030b0f030f0c1201020903030d0b1906090302090a0f0603030e0f0a0f15021e0105011703 71
    0x16903071846866050310300951603004004207000843ca0800081d070b0060100c0744d49075542c0c103281500105c0c5014802101e41000001550350505005101c0103900291500700c006141c040c140d019050100b6070f00d40e803ea110b480c4295256810452000c030810b02c0e0281008603000c81c2c0350340780b400181000c403a0240f85450603020101d4a03080d0020203d440f5000810301c2041c082c076044440102c10300c0702241007842c2c0f40020503060340c154414962154142c661000d0540e903441016610454000d070300c110380d40000d00690103410f0150b0101c0400d00400c00140c00c0013511000a4155001f4454004c0c20f06c2e41c1c1d10240b040d61070314030265810b00d100072404004080c14480c000f8410a81070001900400240c80400c0481c400c55008007058504a04100199901c03841c005010441c00c40009100e10854468126070b803400000c0801114458024000101d24041f1405d000d840d00f0400324055010b01c00d5480d821070358140b2041c40b10040200005000e6041a090306c3c0d21810319040d18584d5442444003 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 482202994 1250 482201744 482201761
    0x150f141905010308030c0f0c16170a0c05120a020a0b0d0605090f070e0a030515060a0602030c07150504050604120b012321030a05030906060108060d0303090611180a0806 74
    0x4681e01b04400001165880828174000c5000e8424220240281d114010101c41250780b8044282e0540e100101000c440020729800103588001c0c40d100035051440071801007005240610040030400d41c3c80040c0c07200210035070009203411095901007045000c0000326014820114401c04010300801c0701c580c5018200060306000f003500c014185c100b4007922940c9040703a0f035201d2500340c0003958407008a6000038600c0d01298003890042d85c0080c01001d030703400c020902c0c034000700c00c0e02c88200034480180b44107881d02d07035841c03c03c0708088407040a00004100c04584c640b545d10041010f801c0004a10b1034924541c9030485905105900240c81c16100039408010140703070074503903400240700320303000a4400d81d000c00c05d81c08440d525041d121144400680c106900f900840a10310403c140002c3d0750072903480d00c0040d0754000b02180d500341c1c0003c000002500181c00781d0300c0540414018000001c070074040c0010f48115900c503000c003420501460484135064076201010307101514003070b0040d04150401640 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 482204244 1250 482202994 482202997
    0x40c0f0c021c080c0c01050c0a0201140f030708091204120206031e07110f1b01120219110d0c02011d0d02060f03011719150f141905010308 61
    0x10440400040406940c1075585000c5140c05040c80e0700c0b0120000c0c0524a00801c0c50751040c200039100380940c96900c0d0745903004005851480d6070050141414020b03607030045459182d031010503000860188000e202020603040558411101512940c0240c2800c403121071400e02e5001c4641c0b081d440030081413042c40d50b14440100c1c001e5040c0d841d15126100c1c60080180040000d60348448158080100552aa0300c031481c000104043c605641803030044011050b242c2880c0c00c01003034203141c030080035420317940706001d015104981e4100041c24000900343c7c141c6407150007801140004e080e200c0079003420109001c02050070803282400d06441e440c0c0e41c00688503010340f9080d0707031038001128004a83c6440b050805c1000542c001d007040d80d9102c08080d042d0440d0000c1c040c40c018051418001c1085100c00240c0000036070584110160711005961071921034034508070301c13030962601c0b1000340b00094014000c0c144503e14285c000500f5241002c698204040c20200540c80c0604040042010450200 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 482205494 1250 482204244 482204267
    0x1e0709020705010b091611160b2503080105100206070e1302040e04060f0c02060c072619031a011715120a0203010b04020f09010c030e0613080c040c 65
    0x3584401203420860b004000a007200350300042076070204200b50169030940a50210740340c0b00c4c5541d580142610580d940c100c02c05564400c1696003040c0000c41208014002d1600b040080401c1900458884c10002c0e00341c6008030046020280144007914009002000e451014801842c2c249448400140701480700d480c8280501124051b42600580c40e030115000b50451030208102c070b083c1840c00000a000d8200078044144c0781018101c0c04520100307080b03000c3c1581c44c1c54a801c00d000ca484580b95241c0081030441714103026405c00600400c901c01400955088400d42d201c440076000000d0182c0325010038088a00c90311421611140c0c0c2c21003020035a41c08944d561030400d030b0f10b010030340c0c2e051a0b0109007154090288001c0348000000002d95280342442035000784042d00741134090005900031120411505502880582440d510074684051210f00918082c88020301040c00308215030f10844080000c3c160007441405009020080740d441160181c0e0208903000c1d24070001001000d010 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 482206744 1250 482205494 482205509
    0x1611040f0b1c0302011d030c0f060603101e0f15080f030d23160207091404080a090512030a0806030c060720041e29040b1305040b0103051e07 62
    0x5624400c20f05100750321050044a04201a415519045400645d41d0f045808819214480c030503904035550000b00d001402502c000c3e000340344070352141d101c0e4000381003002251300b102040e00e540709044d60804e00a510800320000c4000401c41045a0364440c031005503000003240b0ba0040004020307418000013210302c40103400c41d001400d070300144001c00c2e00e100070b04c0c3c046554410120910041c000700d6400308001c048560210b600b9640d5490400043c0d4601d8480104101c081e100060b01040808000b403801041d01d01e8100394071038642002034000249183c1409a580c40498000c1d480c2d60401000b5400210440040c005802d1a1000541610801a00070308085075441c0070103040b0790b01c0e07110445503880108180910000b401d03500d0300801d13101d00940130150524403092008606880b5241e0900e8842401c40e1158081d8014840601100c41d0a55000003001c060a0f160942c0340c86524000e91141c000f21845515504003a481d003008850303a007080d00c9403c070700400800e000003104401ca5840 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 482207994 1250 482206744 482206789
    0x9061309051f062f0c0306010906060c060e0c0901140f030c0f01051e0705060406061e030b091005090c101d0f0a08010507020f1207031b081611040f0b 66
    0x4c854802c5040300501c40218040410681c8040802001140c81d0030002016400c544440ea81d46455406440c264403518000c42e0001c03107010041500c5401105d6183c1e142d40c2140e802c000124040b80301c03820241d021404d40311f00400e00005526007030100007090003003200180509000e0100040414509a20302c605000c00010400e20030200b040d0040d03084c0f810f1154540c2c07030b00200d05080351940f0040301c0440f455441c0c202c3c00701e41c0e00020450243c0640003200030741c0c4000d0850391000c0110b040980041c0c2140b1624200d04500c2001d0701074140b1131241540a050101004401c0c00b0400001165900a000701c1034240d0150140c0020746aa40c2c9100b1258a03000c01e01500103c1c2a000c0c25030408240e9500b44020001004e400060031b10300300000c0002c82e251030700c1503d280c142c940140000100020b100000d10030601c00b01b4401005154020300010380b80000d44c040c0300107520880d81c400c5070088242c4801c0754862809114a100000b888001848100d6800300002d1104941391211006403d4 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 482209244 1250 482207994 482208017
    0x30b0609090a1e05060109091a0405030c030a020109060f020901050d05042409030f0f200c031c03060b070c05061e0301120b09070e0f0a0209061309051f06 68
    0x1e003041554181500010781e01900c0d40100c0d02c01000340c256201c1540c00d446141c0002035400340a04c2102d41103a0031884204c02c4030940690b44841601c09442503074248800d02640440030301c203100904c5008020f80000035204510b10348601903403100a00384ca8035074818007482c019660008210703800200700307000018507540c85280c18806803e004142d480a62020f21214041440a074000c0d11a140281c940b10700315041c0d5003080725a100541500703030018081411204034500800d00d4403048480181c01e81e5804512040440e2600b154204a509a0940e000c03016000c1600b40c0300f540c01a0610342c40780f914110040e102c03400310b01c0c600e01c1440d020b0380c0b00040d11401420000400349480404410155907940c1d200045048000c1812041d2284650b1401250800c3d0700061418101c41c01d2494003425552000c104614540005001e0b4495940820284a0f95900c000c020312110100c216140d4500d818407034000c040340c40040452041246151042c85a07152010200303086138080d1034400002704 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 482210494 1250 482209244 482209261
    0xa02010c050708031c050f0601021e0a020312030f0a150b0706020d060305011b030504151e02040602030409050a0c30051005040c0c110d02061c090507050109030b0609 73
    0x101d070ba0003000f05000114072419030280b01520340c85404405042171005448009466044a406503242400350340600000010701e0710320074150801c06824000e4811802c80798000c40c3c01c080c8105040e0010f1117000081003007506804079a80d400054161082040e00008401007004904078010040d0790040400d070b103001c01007a5012205040c407401c6061003142d60344c1c80c2c01030280c00000740e0754040e440f0740c0c5420b02c0081d00c00d20035a4400d51b086070f910b5580141858103000100b0201c03a83c240c0e0042d480001c15020100c0d40000d20013400140c1c02141d986107015400720895001a121181407818a00094011913028496012205a001c14481301e00104245136100003907216000214a08080810884030342c2c8400d14411944281c80c10311080c2c0c60360004845584104800030006814040e419510341003100b60314021510241044d85000807459020545681c542040c00d00303103894000250410100303010400007040c0030f090048015003140d079a1604031030000c007080c2c0501d252500095824 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 482211744 1250 482210494 482210503
    0x7050d0b090f0a1a27071a0a090b0a020109170c06061012050613111c0b03070b0306030a0209150f1f03020c1009050a0311060103081204020a08010e101406030a02010c05 74
    0x2840c3c41404015000ca65025480d11242640329a0107111aa0100c03803807d221004101d074455040c582e0742c1c0d801d4034101092034030709400400c0c003041150741c0c6180d51800100703001f840402442c002480c854032081c10f00540c0c0e15009005140e80e005035040201000200c4d0040c0070006239048002c5e001c1656aa80030101d035001c185e0340303003180619003003050313040c204002d9000a144210031072001c15683d0080040180580e2040c1c08901e81681c00110200850100c1001554000b5001020b844d8010100d80010f12080c0b0151001c485040400c0c00195152400c041381ca00000805d84a02c0f1016950b80c08014007030511550107020301d900000c5c4800c04c500248028a40d88840304010409800c990825990312414071004802103004100da24100800000f681c504881d40f0184e502e00d005801d00d00c2d00c0c00e4110160049800144400001c0342c910380c00e014464611101c00001c0820f602c5103811001520311600812254812440a200164901087c07517019070b41c0a007080c81c000101498081d152 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 482212994 1250 482211744 482211781
    0x8190921110616110901060f0f0203090d060501050405090604050606010c03090308030a02040e150619051306211a060c07030803010b04090606110a1407050d0b090f0a1a 74
    0x100c24001149074400788940c88100080c3e000301c0c2c03049610349401040c0206150b080c001d11002c14800c400c24040e6510420440407000d22780d00c10380342042410b40c04200e10b880201d8044504d25102e070014012800d040c81031543c80901d07007004000f9810b00e61101074540d50064070081c108142440030b00d00703150003400e1030002980d01507403481c1e9074603009120034002d4203d400b80882651641011950742d200e20168183c400c2030080a0b00e1820344010342580e4591010801c40c070610606000c5025152070044050008108545483d958044259050980c42003410100d00c5803614085110280030209152030440312402d48040b40d4580ba0340134000d1a0030307000c0d40010f002c06000000850110f0000303010340b0464040440c240a00b9440d000f064030a031007c04543c840551000f000340000c150403100ca40100c855420549103a42c0e00c0c0c0700030038000d4a12020640300e0085400a014960208005920380182d03140068a811060b95842448004151554203824400200824094001814903085 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 482214244 1250 482212994 482212999
    0x3080903030702090901090b0c030103031e1209030f08010603020c0c0d110d060b01120c05030a050c0c010609051801060302010f030507021c0806030f0105070e12010902030105040819092111 83
    0x1500d1034900703403146c080c0c0614070b0200c0702d9142d003101148803e0f0a6a050701c1c10b0300c0c0c2c95200c010681c40140b1010b5011100300c2a55000c1002e600d61240003016a0b104140109000b070b80c640203094420701c0040d15081060b400a0101031041004c05100c0d8008500c100c80d40c0400c40b500750f211381302c90908140a2102404075940721007007203d241e00b00702c0554801c000c0c05d2400e88440b6000087c000c00d000894488901741004103e0400000311030341040d90000d68400c4809200a041030412140c240c2103444c0b0381c1084a005581d081480914510300040062840000d00203008a03070466000a0004600e00214004d058903200407070105402070112001d41031903019029580e00760700c10020511b00080e20064001c0c02820071815012070180107440c0318040c5625000c600346c600e04203009540020360b4030061195600c4e811600160340038021540a117001c1c9084035110400601603070010b9809440300001c0c00700340c580400038140000250303c0726103d0007609140301480d03420300e030541d0907400c600d959 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 482215494 1250 482214244 482214259
    0x606040b07022709060411060304020109060309051e01020406121107030f09050607030503060907080103170a050d14041208090703020f0f120303091b090a110f0711091f03080903030702 81
    0x1500c0071380014854840d5000b800d0804107011940d003403280c2c900c401d40d000303030000700b4881007404518081c0c0c00c10580c107446030044030340321000442141081c141c61440d00c0c2e0165000141000300903401340b1060817142e0000740c200a0800d4003040095148601d000040611201d04842198180039040e18801042d02520342079640300760b46801880340d40120781181c400d0a0013004960640d2107150001d041c0ca030302c00820100c02c00420140d013034640120141804004040124480032003550007510452030b034403044e0121030b04080c600130b0803c013540903210701002180010440454000190a000c0300c0d01613601583c1030849030040b881410700e85003096003020040030140000480003004500c140c10030fa05480d0043c01e450466030000240103c89a80000c2a50200300280400d5100c80313081000708022a250050f80001c51000d038110300f0040e01c0d982495065505036051504000c4d50005070307500850100020302812102d048035600010301040e1000c60300d0030107600c0800841308a290002c001d103 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 482216744 1250 482215494 482215501
    0x6011407060c120e06010612380303071203050402010e120604030315030f02131d030d050106031103071103090d15141e06030705100f02060606040b070227 68
    0x4001d81100700c02003000403030f00d00c80203000c01110301c81d40c540b281c0701801802c030507440d111003140c400604080d41421655225209140d030108201419168820710700c0070404165001400d624640356100c40b24000e4100300a41400034403564113000d51100c290800003030341d40b2030307000490304800001c48075034000300ca05441401c2075800251051256101c1e580070300c590398103101300b2642e40d4240c0c40010102822007111600500c0c042036208080c45147c80700240b8021003203000740c49250302d106080401d410000e03884050311030740d0180d140503003424202408112410501508a40310003000300040018100000001c04800e0003181c40325a00140b03403e07500e0b0b102d8204101c0514138510b107041c1980c83c04200c0e9101245040d0414400d8201c540400c02c4600012100426000b0042c03a01341c0c10b0080f02e4002c6483e40e1001c00c54140d030b00440d40c031400380810303451000c1d2038400050507281c442c0e00d042c8005c004501f1004115403241d40c1c1035602c074200070342d0b0480c5c600a400414005040582144040 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 482217994 1250 482216744 482216753
    0x207150305091e030f1606110c01050a0216140f0f030a02010f0c140c0a02030111070b07180902130b160309090903080c0c0c0d050d0e0603160806011407 67
    0x14a010b4815041510074036460805800d4500000380c0540145801c2800301144a80484003d45146040050803191002d1642d403080100d41120810100380400840c2c100310f603001c248522a4800c141503000c52501540b05011030001d011030000401d0a826410461a01003050046d01c0551040e0380450700d4012038405081c0d01c80d003100d6024801507280c0300004003024003902911540d102d49880311f00c2d4402c0030b02d00600aaa10451401d01c05114144640c00142c07800d208103010035180400c0c0c1900d521840c6022413680c41c000d40310790304000a590000c450a1013000f00401151401000140e03690041c456205080005074040b15203440e0200340b61101108050350114054401c1e506c00c0d07501525440c0c0c080c2142c0c00e0800c043d00241250002418414841d402082c850411204450460751500300140503d5840c0a003150b040c0c1040c2c1c2c208001c1500403000d5001d2007011561242940b40c40049214068070900036070302000315940114240c0d034014403040401d440c14511789580e92159051 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 482219244 1250 482217994 482218001
    0x7020d031d0306190b0a15020d0305010b130b03071b05030733020a112a06040311040b12060a050702060c0a020d0c02060d0914061803071202071503 65
    0x40034005802a101c0e5851501103091886080d142c101c2c182e400b614040008010100c1c04d00d0181c10951280700441c110340041c8030707c1e41004007070340140108051160014180c07001a4022070f00d05a05009201e0202e1a006540050742c0e611101a5207940d80c4980032101c08192601e00f4004880718040c920030b01501100900d1268080d0841c2441020504070075009113840908612031045007900140c1500711680003851004c0e89880c00e0214502c10361400d40c2004101c96409001001c1c01d20104080100d1868141b20440c08403020f0341418035586601500041d07004e4902d1144d82c0d12102203400340c2d590f800803000f52800300202c0354035152a8485500805c0141c850001500c100d40006d48c49040703900845400f0b43d89a400b43c26a80c680322400d40746036800c070400300d0b4003920500111513129500d2180c100014010301d0045c130414040c0a0780e5040004c054280d0b6001c0c00a1842c2000c4081c0000850380801d500181d40301e0b06824400b801ca00f031003820703040100703415212404801c03016407540 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 482220494 1250 482219244 482219267
    0x7141909150504030b0f2703070303060806070c060b130c1101060503010510120606080f03070209091207080a030b10500405030709050f01060c0b0a050c07020d03 71
    0x140301c19540c03035245000d85080c00b552100404010541c000991801020502603400c00d24005d0406091031440b56003642900c12176640342041d9101103101400d243d0f01d409640002c1c003100d40a402030341002d100040c951f00120201410084c0c9a100c410610784038055062168954400c08100380c4902c0b55000b0f10781c0c410258055095070801c13002041500c1c040c424540114090726583e81c4480c1782030880c008007426500b003990420398519000824060a000c1c40c5400310b038080165990b044a031040140703800002c2d1009401e540301c00d484403000c000c10720031503505075084807440f03407a80c0c5003000850240881b407501603000070003d2140000d031a08000f401c240300b241171100300ba00703c2c1c1c00400151107400c41e07860b009285105483c074016940e0b0300401071460045180303a851800e42c96101007407502e00240c1c00080c01d650f41c3c0c820448032594100705180900010b1620b0b581401c56501c54007a0131070301408c00b08005594101040c0c9c050113102c1125403c40d4040c100024081031401e02420590780b08 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 482221744 1250 482220494 482220509
    0x301030c05090c0a0801140102030c010908030711070506030c0705030d1109040f0203070c0201052d03010f061103090910170c01020105010801153615050f0907141909 73
    0x5000701e06900703c031406803003001c1c0c1d040c1e48401c020380ca418007140c5510b030380100c4207055010400901c001c03207c0078010340c400d10b40642c0c82d480d940e0030b011800401204520010300c01d0ad030450001030106554220440781c2003681c100001d61511440e0a001742113100d590500d01d011417a2007900303084070b051500a060442c0d400c40e420030a640322034103600d013617110885400c80000c0300a4004c10040d801240034001c81985400c440d26480c00c680d180035903500040380b030b80c00e44145c040300400002c81e1280d8944054106446c01d04014440d10020070741d01d010340422140f050160b080000c04050461600200a14501901c520004111010291034000045c0d480e8010350030703d800802c0c2044140144d0703205e40117070034860450034604808010403050b40d800c0c41c0c1060346203082a403240e4403c8e191500041d001450001114103400c0c03412215109258030240c020490203c080c00ba5540340105c5d107502980030308129410035922040114640310b04e03610324610032206610105c40b590f210040000340d5080c0e = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 482222994 1250 482221744 482221759
    0x80c130e0a0618050402181f0b03060901150918110d021b0d0c080d0f020703050315090c04091802060d0906150b03010605180a0320010c030f030902060d020301030c05 73
    0x1e10240c9013a1181140d02039005901c2006042a103219002050303071007030466080d50150803801400358500f020603803160b00e03111408400d0181c20316042e40494014046441c40703041c0c46001810103890350340680b10b0140d80f40c2c00c1c0c54003900c1214043c0c1102ca5100d00b540c0c001680c403411000080c009401c25841f011034243c01421106a50000184007080c50103103842e05c603841c0030b5555030586642c0c031112761002c013140c071100b22140c005450b00190108611070f0b00d4a54483c94014a84200900c141765a140700d0400702c0c0902620380d1042c001c48080d10103820000ca042e141d01c1c1022901c50030b100e44001c4d00800c000542840c09012944490307401c500c116170500104e40c1c480b00c007003071049142c05030341c00b00d8104100411003d40190700030020608980070303c001250019000a400710134070750080c2c540036004030130214440604106030384001c1c03003400d00a15103006500c00510b11807040c40464241580c480c040d20941d520310040e40c58500d50f085c4295500d42e128076210f6445466442000c1c0035044 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 482224244 1250 482222994 482223029
    0xc03180706020618030403080403030c1e211b0501020301090c020705060406030213180504030f02030a0e0907020a0501050937060c030902130b190501080c130e0a06 72
    0x1011905008446050b4020001a261520760040d59040d07815164030341e01c000c000000000780b00c030020b8401980030340c0711000900c1090400311300c030407032400300036010060005040c0001446160001d0110310302007007c0100e55056142901c0c03407901e040b02c000c5000d01030000c1f0303020480150021816105804814082e82d00c05010999441a1500940741e0202c410b0200b1f00c4114070950291264024006480424507076032480507504056680a1245c2c0a480360104000d03d074110601228400040c401103161014070100104044920f2620703030308c00d001040109200c10b01c00c1245507101a0010020065810008081d84d034504da900c15103095000302c402d1107040c0c07031482010114507000300b044005850a2942e5400001c2c285640c80b90241540c3d00d5442e40541c440b48484045245038407000541d5504650800213607801204500c0030607007141e101400103036445001c06403c86a02013480307886109110000c143c5207920b4000c0c1700801c06503410401c240c0c4c004d400c4981281da00346040d030761094 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 482225494 1250 482224244 482224291
    0x60528060503060a05040c270b101d0406090c02070e15100e040204030606120b010e060d0b090a05011506180b030c0703140408030a12020c07180f050c03 67
    0x3200c038031078541d15820040010300c1c030100303641040b130340584a038041921150f11141a845240c0100c0341d881510603041c06052a0b081251059000481b03003200e0007154840c3d603a00081948480b2403010b00090b0718a5031207000f039100c40c3c2001d00a4121020140044e01100341d0095895407544580310041e50300a0100303600c6e10200c0f840000542c1c002d80801d0030982c5141058440d11200d8403880d1b04a0743c204000808500130303110b14009410300c440341c003645507007a0030500c11181b0107801c60494124881c0c24800180c0da8011100c108a5110101c03060b6551901d203818140b281086001e413042d401d15541e84001c010421000080d500e0907201e03040b10030200301d981282d00005000d1f46106400400100d10b0340740901000c6e2500d14460328081d01c8146c401007080700280c00c1a403084032076070300120713030692a541c000190300f82646a0b54021420031012801e0581d480507988101c025007114035048600b40c447d0341e0007611000103c444217000c3c6040070200c000859104481299052034807000e903a000e83c = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 482226744 1250 482225494 482225501
    0x31f0e070203070b180d030e0105060108160c02031f060810090317060f0d11041d070501200109052103040f0206030703061805040203070b12010909020d060528 70
    0x10149980103500b801803130b66607684030309005000c5103a0402d440800e128844c000700020006003203a1303500404d01080040344142034880103022075040c00703204000c0129403c0b84104240c880b00c828607201c4507104d041c0c00402d0411001d54040c01e00b4a1014009100481c4d468000600304d43c41c2c0001c480d1030b010f0148410048529040d0000c0015a96969500100c01e00003c80c40d00b010300205440d2a440107140020303040e55a800003103810384941000d81c03109150a100704400c1407110341c00c13001da60640c1c243c0d15440345080d008240c180820040044c400d420310303460700b00d503880f425070080004031058103156540d0901300d800030310007500032403000400c0f03200401628010355100c65004040002c40d800c008413504001d00c407008160350b6240008080c900d0465100300342807002e10025680c2444c1c0181401c01d0696081a09054401c0042e00020025411883e0448084507070004450516200040c03c0d014240d030046c000390300301401e01440e04a00e4210110b105001a05000724920b89400325094 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 482227994 1250 482226744 482226751
    0x2c0102060601091a032806091b02150c07020d0b011802071a04031b06091208040c0909150219030e010501060c060b0406080d02150a180206090103060b031f0e 69
    0xc0350011420b810030308581e11301564001c00030b92001c0e00d42c3e00381220f03a6078030600c0401449141b00d4407800100500222880781c0f0039100c0441090003c0d00c10103280196889103145103081c01a030340c1b50002192107007154107441c6c03c55801004200b0002003030804000c404400e004183c0b40000b240119008081544211480103900c1842c4190a268084500c200b81c0d900410a40603c0300b42141440b16449000309030b080700d4458400002e40000c9401c2416281d50761341907103414840700744280004139041d210300c041140d4040e0404501c07900c003490440b41c1c2c0244d510999103c140041100c0204040c407507207140405c242c903903040180b2110f0780400d0b402e0301e00a05c03c030004070781d08198140216440360000317240a440508049809641c40c91140e00e41004415401e0058228180326901c62030210085034002807019818442001b92601c0d903c140850210002d2040d00700140154160740030303810510003411992522034076840e01480c02e500c8120000300420f5007aa0102c004981c00110102c07d501 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 482229244 1250 482227994 482228009
    0x60106090302010c0228170303150d15110a020f160504200304050a0b07110d08070c05071e0e0c03010302040203090a05060702100f05040210050a2c010206060109 71
    0x1640c41c41c540042d5040c0c03514030070507030304104440c0c0c0c035040880215112440c103103003001782c0650151612041100310701121030800c074540c00410900c07800403140000c021035250700710341144e8203401c01d08d001c0b98040180e41800c800b45040c00343c0c000040f469407001d0480000341c0c2d001d9807030420180c200302d910790480403070507481080e01791004e10682c10254007002c00c900c40074181846504603201010740a810031101200c65610051002d130401c54808111500b10119003003e20442c4150301041d611126441440d100708484034000920061160b0715041e003d075000019505c086446101240c003446082c00400041d0081840c002074061602026501c5002448811130542c3d095508110195201418021042c49102c07241d0022810500c1220b0152550350010280081c210461800340c80c6030030300c10304030386244c5004c200141e106d801106000c0940b40c9415a078405850f001501d51421000002c00ca43c440341e11808200c108075542d06280100276003c582c401c3c0e44000044524407018098400c = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 482230494 1250 482229244 482229257
    0x11070b0c03190612110a0b030408070812151c031e050c030a051305041109092a04030b0c03070c0623280c1d0d0c06021e060106 56
    0x103100106420266410110700b840003241a07003040504019203c25400150440d00002698410000245805252010240c5507403028901d0f1440400e001d000040001d40344010020311541000121800c680900110124410581c00d00c0001403140c0711a034540c0a00032185240600c1d40702d03100d1030841a5440d41562114440d1128002e42e2481030508840300c001c3c00424002c1100c2c1300341c28400352001c0c100656400380c4403520030f10603044403c2213500c842d00552400a820907403100d03400843e0b18110080d518003696484048445000044040003a00503e211080705076071800601d0042044a00503019040c1549403a0282e002c070344410303070f882004500c081144400144554022000f83d6800001d0314807111a4002461000501100c149411b61800e00c0c1c10f2004143c14500c0114100441504204071015620054070f144413064000e8034403100611005207a0351180340008049521459820f255691100082e545070101d14582c41c007895905505000c0c800001940c40c12a04160b0740c4c507 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 482231744 1250 482230494 482230501
    0x30901020c061f061805220506010e060304060c090e0c0403110609090112080403050d0e0102010e07051513031505060112110a050f0d0507021c0c080316020f010f02090411070b 77
    0x40d81c0ba826005d20b00304181717041c80c100190036076030680110383c10092040c3e1043c2510b011514601100c40040419040c000c60040c1c2c1c3e4000c2e03c0ba8401d45c0d41c402d078032000000e00e0086001091740c460301158000800120a403040009490070080a00100c0307201e2804910300301080001c0006070300038582c8580c0c0084000b0010084200d03104010fa401c2030180e04400c1c40e058681e1143c83c1400c00503941c000220b8800112203a1559092217030480003800c00021f050485c0c20034001410780b04c0c10011025004001042d8480c66040c207801c0100210f6007c4102500d200c18851058085c22044a0890200b540130f0705030881d5203610300030082000e04010650340340503032030310081c1c415400010a803076500905102c0b14042001c184202c84c0900c05a400801e0710000075014103100000d120300d1101000429000303000014a908107807a01300441c00c0e01c070310320000500c104030720f003c80c0d4048100341c540c01c2c400d51100c03a40303065001b851004003d8809000c0004407890310708282c8108c89004080c0e26601000 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 482232994 1250 482231744 482231747
    0xf1b050a0b250615060e1207050f0111070e06090f0c030705032d04050706030b0d080c030708130810060315050a1d030c010c1404180b06030901020c061f06 68
    0x804070400b6084034a514850b9900c41c90115600c0c0002c40c0702c250400b510521105800130407440c07032404101d8180c1c503014a4548007a40380e0500d0310640e40588000080c40d01680c1c0034100a05c42c1d03000d400c080b64030a03a03660840d5000c002080e644d40d80140100780200d625020310f400d05a20503107291040b180355481d024800c5405034402800400d0640c0d2003210085203058201c84e04407486a000c0e42d0004500300ba05050f402c100c283d80c031102c140b51030b101c100d25003926090202101030f034202410b00d4031405514255400d61140b80d000500c501000160b460094000c242e44d502034a007000221240302c16461003d00c1114403d00014100f10411131503060034621075000703170764001016403011584c048960302007000c0b13030b0070b106000355a5000400d03620181c141c01d04c218004c20f040b5140500c842407085d030011965104d180174039030341202c00781c5200c84401c1040e04507911064021300f01079581e00d01800070034001d41204000703400d540034200114a40c0c00410303449000c1401d000b0341040c01d01d07152440 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 482234244 1250 482232994 482233027
    0x90c020a02060403121704050604060b040203090a032001060b0a0908030a170a0b120a051b01080403050a03021c140a1a041a100e010801060c0b0417070f1b050a0b 71
    0x20100204609a40a1b40d02c466628584030301562080f0014015070409152441c15a0006140d140c010b0344140200604480c6c0060121445501824410000c810004241200074219a002c2e80d4a42c2400d4001424540207402800d031300c42e840c5d8602076895160302c0200c3c1c4a11404000f90b0000340103003615100c0105030781045400419103003002a42c0003050700481c0b0710900b2000304c10655000312503960706001c2c0c240485000c00e070b903145100d0340b08007000001078080c040c0504060b041040c0420b10808a50080e0304a400d0b1035220800c0c01da510307800c42c02c014040d10300544400030410083c0c01040340f40300380d8081c0036a0b21f00280c0196995a00c084140402400d0180e13000c40c00c80388400c601c0c1d07884d480700d10a400c191841079032904030b01d955a000250400d41d040e844413040040003803108010859003c00981c00a80c45001180b6110074220400000d00554201401d00628042d0740d000f0070251002d40d21451454000c0c00200ca540c540c104882d0b000c1d6803260304e41c0000d0800548034040007510 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 482235494 1250 482234244 482234273
    0x30b0a110f0d0b0901030302030301060306080604051506030a0b040807060609020306010801050f13141b070302121303051c0905010509030c0f06070c030b10050d0f39090c020a02060403 81
    0x88001441030301d502c00144c9020fa00303030b0068001da00f00000501007541e060080d8005800100018030150800b90766180d5a0b000c1250040428041403010824a64090045519180c0c111001011904203828a028280d12101d01269190301d041d0300000c58804030b00070380c1c3c8240b8050310384a22aa1071301080c04209003a04850301d07803069520888542d0b1080074030400d2540c50000c001300301c56241c0034009002002c200c4004114001d0244648400240d0000e88803805d00ca0461001c1d80350b0884600f80002c6130400d410040c0580501c07840c0034280e810106c0341c46240c14203540c68400050344c4800541c1c49115503081c0b160160800c81c8650080d04207048050301081c005007650b03240940a4940078100300158204481c4022887e0a10004040d270080c0380000e02800c031948542540f042d43e41c20b01c00d92109400500035600e03e1141c0032110544d1400c82800c1d0b00c9a004c41400059680c1c48184a8086001e203220140c0303040f6810305498400140b4051441e07002c0c00b05442c06086443d10061001c955 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 482236744 1250 482235494 482235517
    0x20d290d06020f040603052a0d0e0a08040303020a1a0903040504051e10031407060c0219090509030705331b0a0507110d020f1002032101030b0a110f 65
    0x2004690004209400104010401c0d41d400064604040c0003800c254a8526030440800010200c10b02340c0800040032511204104900082c060000701041402c0c6200905d01030078440d400b10380002419000b061041c2e4052041d0501a00d5120413040390040d60307001e0fa0300d03001a41c010300c0140200e040503072080b60000f0101c2c10000b02e00888a0045410210880c0c1811b90b601c0d4156080081211a8016009a1903000040c10341c40b414110300070021010701a0103403045d80c1141501008a0019040e840980121002401546800060b042d40c0342d0000c00215828400d0015660030b007a81c1c41242114201c00c5d0f14010308104503024500031032032002d0312002a089a40c2400440d515a882c0200000c1030644c4446881d01d40d0340c00d0006a80f58441045405030130b04035040001aa41d483d8600e00c0c00b1402c9980040350186400203c0c0f1310300401d80c02c140d95640201617000b1103085000301504880c4035003000411580c2d407511b03400643d00107018030070581c40300780f00ca0b03035214560788041c00c05111413 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 482237994 1250 482236744 482236747
    0x9060d02040509100e0f0f070f03020d0906320606030402011b391e030212010506040501150c11060f121501020309060702061b030d020d290d0602 64
    0x350b0740040d281e42c0c0140d07100751125038400707000c000b9081e10f84c00d1580e100081400394511441c1a4031060100c600040c92182007040000107a4485070003070341030320b10b0290120700403c1220810316007a80101000c91003504070710346c103001503508626030703d60150302c9500c040585221502d669062054035000a0b200b28180031040b4a4100070114851a0008183c00707005000149000ca260108404038451141d030400c402c1c403040c0b8440b031030300ca8294104441e0350340c4525207068000b07900074003011940d40001794041c0c80018203400035401500483d0050400710b40421103a42d80f014100c83e40300c0650311420100d100d000d1840c000c9003480c2d10345c41003c14090b01c642e28180700c0402504031507000c0ca501201140d030282c2441000302000c0d03001154900d080c0019840c20300d017040003d80303600034100000c1c03098600044148071001c1c403030703685058060094101d03500c1d4201424000e0180d000514807440e518a80850001c0c102a400c84103070042002c4c0c01030410403060402032002c0070104100590350f1680 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 482239244 1250 482237994 482237999
    0x20c060d0e10020319050c0a200a0614010e1b09010c1e0b071112030c090303040e0106030b0103091a0714030115170106050f031009050408071407030809060d0204 71
    0x14880020104200300b001a940c0c0b0b4401c01019050300548248190207180c2001c0007800921101200c02d02c040724100b418030500740140d00078140e580390099440358010b2991000070030403a03402c001c5000f000300b00445142c0c0e0f260550410f07a0903013260701d00c07503c0546031011070551800718000d120b00c02d010b1505110706501a100c89400301403004410a09104010341c00040c808501d00c80e503000030b802d10303000040c140c2e5911500e039075100783d640342e0144100000c0800c0060081c40304030340b807601d0007500f500e4554bc2c0d5104480d0a0690074031507900424240306010310b0039803082c4115418664007450f15000004410303241d56640c000201220306001d0714010540c2da000080300611b000b0702c0e040455020094074850024901c60390101e503020004d034448014040f03135070800107540608804010090f16923a03134400346008100385500175420b8518090520051245040003080a18007420422410740c007007102c8550703580c0a03440050081601440b00c1c01c59842d2880052103034190681015040030f4 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 482240494 1250 482239244 482239271
    0x71205010b031203010e06010c05120903010905060a050108060a0506060703140d09060507090b070809120312010308280e01140706020310030201030c090608010510120e0d020c0a06020c060d 83
    0x280c201c00540f0410084010030808007003090300c44e4419420f10b04002c0c1511255240c175608c0f0400404101d43c00000300e180d14490f03d0035401301c84000c2d0004222665410960442c00041c07100b801809103a014680000d001d440b82030041a00858001c1e050a2030440b06807021282c6030205031040a0802c0108840d02004105d400b5010000b070050360001454103194102502c0750740399034001e500b062028420900452514410f0702c4040000381c0350180301a000300700c480c0c1148294051269415000d80000c0705125800010b84090420804150748440c4034503100000200b0202007040040e4001114000a5124000a0300002104201a0304218542c0ea4507401d80e00201e483c51440c1418040400a540e4507004c0c000041c0d0040c1060183ca0b0708055008018180500895014480654001804500c0360103a4a041601c442c0104003103102039079207d480707109607140e0034018803450444180c0340ca030a01005003200c40300c2c6c004040c15092807040c49656000b100b00b5070700c01d643ea007410f2071004 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 482241744 1250 482240494 482240503
    0xf090c010315080a0c05010305070903200d02060d0504062a030e1009080903070929010512070c020307050114220806040318080c0906011d0a0b07060f02030603071205010b03 76
    0x261003045c1030901c0300e003428001401c03140d00411310700400940c2141000800d07090b203600c0960454100c1c0c4a03110408480100340c4002501500a40003100050384050030841541300b140180d110385014801204075441c0d0710350b01c0351007140c2c0b070405128441e228020703039009070310400600e4200d6046e0340c24250401450301c1201c040d64401e4500560016012284e8641840608058250441e04001c1c0403600c0020b81a201082800508151070070303803060749c41c0c0e0700940503924540c2c0304810a0145151042d001880f08200c490201d003c0c1c030401e28045015801242d42113503c11a40d5502c505051390300d42c031580c607410b0005540404010122011901d620140b12103072241c0e0103a00e80c00c80041c855070003400040410340c008845a0001e0700340c424540d880e440341941185e401d1034004828000c5001d005030011800b48030302d030700c440c2d0244001001800c000103042d07041d004940420174240c203110540c1c03c1c3d1208440882c2e1580010000740f040000c900b10100c861401400000b81d120030000100b07150 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 482242994 1250 482241744 482241763
    0xa0201020705070e0c090d0c030c0b0c06130519020f0612011a190509011b120210201c0c03050a0608010b01020c040e10020f0d050f090c01031508 64
    0x140d400080d2903003405020041d0b40d0081c4040000040103191642e109400d5006110301c003481507400c900390b10113008040a816000d5034001d01c03d080d00561343c406118985d0b021220944650154000003542001030000c003030345598110740580a1302400c528034616110b01101c089910800310800c2d50b20b00d868890280c0b201051105100b00154104003109550070840d16000d401e40d8020004020b100c02c14040100c03d810301e034101107840361042ca0042e40c04800410800c4100382c0084116070074030250b0090702c04031606a07000c1e122a140300000d00300541d0b1100e0f140c08513080f05070307035554031510b1880000c085440160f482d030781c080300c3c1e03415019044d40c1000d8030343d00010341c5a200b4000c05000c5807040c0001446c84000800108054600103520f1303451218240c2d20540d52185600d8885505100461040d1441c050071982e464075901800324a070004030600d480031780780400040030700c4030b0341ca07944d8000c0070080028070b401480c00c0011800380540c000c3da4000348007020000501c10001304108200c = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 482244244 1250 482242994 482242997
    0x3070b19050f0702030d02031009090308220b04080903010e060109051923180313141c060207030203130e0f1015120b062703150708070201110a 63
    0x2088040e50600d00181c41e030240038070784207000040500c0600303900003048550b200b40024001da241e60760390105900c4d40303940b1ba00c120411424400d10344100740e4440c00440c03292020001c441585207910100c036108a040d102c0c003c12150b00d00c40400e010810000c00740c07582050040c00800c6440c00c0a04203410031100381e0111000c01d0f11541840b40000755020603d83c0042006004c018072061070340c955141500b00b0080d250140e030910041030724001070380e49190000300c04404070382e56140310480c82c0d8404103640c0724001446045c0002e031040c81c58500c107101d501200d070806c004c06001003501c80c00000e51010604506510040000c407100148000018005002145500e13440349803504d280a19400e0040802030848181c01045c0308403000c19818100a420b1407070420740c15100d012128008000f8191460b5012a0110f001501d0f0b01c1243c061f0102c50700620f00076115200828141075561036980780600b440d2111400140b1a00c3c030817070155511102c2440040b80505d000415103040d603010034030460 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 482245494 1250 482244244 482244271
    0x1104020f0a02060c0f03070807020c0a081608030405010804031b05010f0c020d0207050108010611150a2f040608040f14010c0e090f0f090327040c0c020f100203070b 72
    0x1801d0703540500078258860803d0701d03034916007118410350240500c0011700050600c0148804618114802c00010343d0304403003e01710200082c1c49020403550707981c9040d0411041c4844030404103030740f0310200545044a0303040e12500c00c1526580d405890707010b1140b4008403194030307460084000c60720901421140c4103803200005108503101c50002e0500350882040015903100b21020807060342d10281060464a543c43d1042c2d03101081103420741000c3c0380c6202210180b07034110900084002c00e0b0b00114804d0078105403400022032603040b80c3c00c00380300d10010012034002440100700590046200700e50080c0306030b603101c2e0703201c44960b03850842c0400c010402045079500e400001c000c50f04294219498041140d00186520b003020304400d104000811a41d159031900002c1007102e14100251001000b002c149000b050f14a14a08403254098a000c584200d013030103140245640104500a1810780140050502800d034009000300d60340c0e03848152003148810449080421488011280203400250040 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 482246744 1250 482245494 482245507
    0x50a032d1e0e090c0a020307080c01060602070f0f0b1315091e0503060a09030912050606031612031d0a0e04140606010c0f02011404080d0f02010203061305041104020f 73
    0x404000d41e88a500510580e2001400d0030355070b02d0310303084c0e12594140602e40d607028040303c100d00b1401a42802445840302061070310070f4010640102c001d4520641c21a09856503d01c89150031400c40d105803480c41240103010300a81201318020103510031100c88107181560369a0200e4030f40c01e14410150006145213000b4841c001182407214490b090220048002074100400030303880d1030024000600c140d1752524040708140c001c40d9200d0040c42c0441c04030f01e01d0b9a4904101e910751400300c0d03c8601c2401600060740120984d980d204040d9028240c2d400220109954241d6044840407500c402c09030780c1c000e841000340e0b2420146400707000401c05003e15400c003440c02c026290301c800c040c05616001032081048030b0f41e10a0036020165040001d50420040c0c03400141c902903826010041100c100203000704030548000b455500525655489042c110b411942c1203080b40400d861243d030144100c0c3e614440e500054101582007400350300020781c241207030310016040303034003001800c14140f401003940c = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 482247994 1250 482246744 482246777
    0x53105070f090b092518080304060c05010e0a170c011d07030311030a0c030c0602070b0c07141f020703030608031b07061409041a12060108011503050a032d 68
    0x2e158020301c176282e1a24001c000c110900c0700e1500d480c0c0703800d010070544c0c20310a4685280b070001c041c0245210000ea0360703569242e010040c03d24000d600207448542c01c021402c0300b05400050384807480380c0c01c11500c9003d501d48804c0041158400d070309508281d9260280545071540c480c0d550a103828024008100d0f80e855890302800c0000301030201107540d0002e00c01920940e4101a1150349550705103820f044900161410200a00603810050701c13031034040c4100490500307004001d00860b405070032800a03103404090515903840491200d4107103c80076048036542d82f007868019000440c032a0801051640e2604c614500d15004030312014003503840c0c400c00d014026400d011081c06001145404202c4888025018050340310b810403040c021560345c0394002c66030344824003540b1412801000c18800d905200145507407900280134040071940391100c018001d01c2c2c5094094122039000000e000c18022648017170360f02c01822040d51054400d22820840030020421a004a01e070151300c0f51f5800c0a43c4000 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 482249244 1250 482247994 482248009
    0x7030b010e06030408040b1303120c0b0a02070f080c07050405130c0602030c0304061d0603070305160207060225050d08070b0a02250501021b10053105070f090b 70
    0x8802c1c0103050400600c400300d03043e2030855050300c40d98008a5540c54121900b855184815400540404260b4180f00307002130307002d402c1b0384080e400b40e01018107603180d12500300c00320710030000300034a45010b0703030380c2070300050f1000c00900300e94040d02c41641e0302a41d4400c04102a1481140c009481c214454541400c004025404074060841440194100000300703d00e507984e0300c1940900030500ca01021224a41c02c24024405803040b009040360f074603820100c401801801c03064585580c81018110340301d8445100040100803201c266004001c601c0c454100500c50800340603005074514234010300401d06860312034900c05128031400c0300950b41c5015060525443c1000381441410600401142001c4910554960a40764001900d501400400e28040b03009108090504130a400c00828072205220042002c03555850038940602240d6070380610a80500c81c1760b03a141300344030065921140c46400c8403007400304051088080b2a941910b0b84000400c5144aa01002450741c0320b010703000c1c070b5080000 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 482250494 1250 482249244 482249267
    0x111b040507030501030c0315090c060e0102010e010b0109060509060403050102070f031101050c27090703151406040e0c0f03040c1d040503030c090a0306090f021e2d0907030b01 77
    0x2d4104a10750440e584c00c0b0300c40100d480050450302c6205400d001044495000d041a42d0b842840b00308800d075100c0010700008a8a10034074055403a001070309c04003075418058406019016510700c1c285030709101e41560740b6088520f205400120620000c400100c0074802000207600907c8840380c00751280c9401441150303201303410301c0c1caa410141482070b0408038078281c031003548144543d2000544003442e4032003203c00c5003031031342c0d40201e10311300340b080e01c0790590f201000040582210b000c61a8441c22000c8182e8002552030f500000308010801c8100300da0003d01e0f4002c0052805603280034682c0340c5c0c1d911150400e4038280d40c400444001004200c10711005130300008119081e1004170f24150302c4051712400001c0c0b03d88060140000e6901c0c0f0b982d600358204014541c000010050400e40d8103001d8510021038004900400c450f042c0340c07103070401c4800482d029000050400120035002c000d4604411041440046140b200c0000da9001d40d03a0440c91034490100c6640c005941c0035100700041c040160308 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 482251744 1250 482250494 482250497
    0x102072102070902031e07090627051212040605040e061e040b031501121202070f180b041a040501050d030c060c05040f060504090b040c08040210111b040507 69
    0x10344990801a00441c0c0c100454042c981c005881c0e568003901c205150300302c94080031030444038004010481343c01c00c0300802038800765074642140c1005841e0b01e581d2000600c071040c0c080114440c0c100450b1a00300168504084504203940c0030b2003d0341020b0380c06411640001020400200e814085004010400342c3d01c2a811103c0c000b0b1018920610070000c080c1020f4980115103980c0300007241d44040180c01000698030300901c1456948003601482c00c5003440044804a00000c404810a8030020359035040d2414540c0108240340b80c08000c0e51714201c07031035510200355141e1300880455596441803103400c000c2c80300b0341003460154200700012214140c110510a0200e101c584000c40e520800101c9219400000002c812000060544140c02158030603280c2c20000307500440c025610001a0003205c60365003082c000e51501a040009948400e45140001011800090058030b03200b8140c04c0780128508004002c01041400d060070f00d000c03820080c24031490615103d909080920501d644440e0345d = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 482252994 1250 482251744 482251793
    0x40909021306062102090a03111806031f0b06070f0606060201020301060e120a02120703060b0a0e04230f030406020c0a1412100218090a060b0307110c030609010207 72
    0x181072010b812043c0a42c03100c11384040c1075030164000c1d00280d0450704180d0004000148099032031400070340f036039400801c00340100b024885c0702038880c40c0e100c0307070700c2c0140d43c0180a00310b4400d046560a0b62000d451207060805038543d04614135a032101801030003914016400c1395a440c41034240300c0c0594150307a0015046a01c100010025580e02c0012120403080465050821800460401e40341401ea60406175229029501031074680900050380402c60707100b908140300344104803080002d180380303902c5401115a0b003480010001070404611114041920083c11540107a000030301e8038142c02c00607154216440001d060021580400c280c422450701120001407450a101c1112000d580e81c51035540244180040068540014014441b400f40c0c10036046480782c40041311101c40440340820140140075404c041400449103014400c00c1e1403120038001d00d56207031140211081000c2720781000d40f0b03020760b45c2003214a580038040980510704003000980c8a41a80c10001c81400307840210301c0d282d002 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 482254244 1250 482252994 482252999
    0x30920031c0f03020703231b01020304201c061505032a150c06060a0e1014030c060c0105090105070f1d13090302010e060a0b09011415040909021306 65
    0x91090b081d42c0d6100c07141c980540c5640c03051409684845e022148000d094155800410366640070501414a818080c00102000304c410030b029800c0344001e41e80506078100d01240341c14a503000300d115a40320384000c5c2052007455010021100425031000f01158820307160100c003a5660035500412010781011006402941c410038007403445030101c60400311071001c05040403601e40e80c48108014034041050f203066941e00840034403544500741100d8041c841d0403c40c4000c15440c00e56107401780705c0c0c0042c0e69904245420202d1aa013040301c81e441c0250300d442040310680d000e8482101904000c03410000100740c50a080342c0c040c0c20343e20300600e0f103000c0001509496054503030103400799031440d0100020609035004200400c0d00a4030064024000358281542d000c10150f055000001014540c0141c55068840401700019100714002c03e0340c0c0031101100600c1215a0743c0440300304014000c2c8414840c00c07031141c40e41032540103030740031511441c1d581142130b0039828502c1c841400c200403078004000060 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 482255494 1250 482254244 482254247
    0x7030e030318010612080d11040e04061a0607060905010e06071202030601021018060b011110110c070f0608010e0124020f030d06060e030c0916030920031c 68
    0xe061110072400c5120b04041c5603000c1d07000401815121045c0c15124409040c0001c80e503000510b60614585080071000b252110322090302c0c15146041020078150b242e079101c0401611196070000a80c20070481c20a086580e10f40c01404060320510001c0b031040d0b05410883e00b1103080e200c0c0c40f4403580040d0100008581d1180303219405250050005031030307448480040340740400740550aa01d040c43c00000c02100144800600400b41c0b080b2024040040e42100441e80c5440491031404550301035a13260f66141d000b50001d00e28408588042800c040000f240c0c6450041203504c519030311101d69100340840e0f5446078245016101c8031050034a25450701c100c940b071300c2c00b040004038503500100c2c03510065613100b440b984103180030410880740c6495540440c000145090f100d5040409d04091514515042c0850300201010000f816042250743d4540c6185c00102281c021070205980c41e00c0800000b040c2c1001041403031044104114240304c40c0f01030501e001d461504c06035400a09008032010356 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 482256744 1250 482255494 482255497
    0x9081002091c0f020a061d010c0c151701090c0906030e0309010c03050903070b0405120c0603070e060d0e030315040203091209010c08120406060e01080703030e0f0d030c0b07030e03 79
    0x24020452842802d00302410254500054144000c1d480b8900c0b4400044081e0300c10004800c02120450500c0785013503180040d5600c6602c400010103620b4031070720420988045440381480781c052030030100f00d41400421242102c0c2401d170010f42c00c260765550309500541d400110040a40440d060800049002d104041e60b43d00a10a40f14100440107042404141c415015075000c0c00001c1e0845802544541c62005150821f010300760044004c01c2c0c207100300e00f100085451010b6800303405a8912380314800308a4007111014034039900010704001e04404241103104c1c1c441082c00281c0550703140d06003903905000b040810000b841c4114018020300803203403404908070442c200c03140740c001d640e0424540103841170001d07020080c01012000c15256000505020814440c0744100001c01003641c0b0b07045480401c0d4400e0240b520150301103801880000d01468200c10220705c01009048030310341d01c0d400602c017104104000c600040c078400b9034104101c0450441600215142410300c03003a00044583c2e5030341e = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 482257994 1250 482256744 482256769
    0x17060108121801031d01052203080a1d0d17131109060324011a04080303070305060a030606080c090f060d0f081207350402010e0f0901060908100209 65
    0x54600540c00ba0540c2c000d0780206503108411080a100d01c0b004035181c0d000f407104031400c2d50740c980342c08c20302404140c0050075404604c0c0d040d10b0b200800d4842c1040ca00040c040901e501a1101c80c142c44050311a07400c1007941900501381c0d0380ca46040c40f4090141000e51009009070445c009000313502000203188002da540d80d03002c10782d61702c03601e0343c1c5103000030b032400111017035032103512041c44c5011144a20703941806058070310b50010740d0780501031091085554400d0b44130703044040d0014030214140314401d030400d90b006003000300a41d03846030b1a03450b030104503541e5500140c610751100c80085078600303015010503444501e0701158410707072610502294404210001c003c1000c1070682003c4200b0201c40d094074101c05440100482515100f02c025180d03002c2e985040c1b8181c0b440103650701201542100c07500c0d20b50b80504103800030b0345a135401501c61035074151083da80704a200f0120781032900e0f0548000d000341029601d510740c0c7c0703141452842c1841c00a800307035284540100840891a10b500754480b00 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 482259244 1250 482257994 482258017
    0x1501091103100303180302040e011a09060a03030f0c080a0512060a06140f0705161d1003080a0c151a0d020f0d17040e0601080610020d110c0a1706010812 67
    0x80c450040c129040828005e42c10095000f0301e0651480150481540b1207443c00f50b480e06d0b0b1040748501d0608018584000b00c0c1c08a0b03108414040510000384207400100407011581030070b014000d01541d404400340c0101c110000041d10226112020a5180e102c0541101003610020041402c0c0a0020030700514021000024580040c1074405200008100c9501d1900a1700380c1c1d00d140070010b8020190070b014400d420400ca00490382041d18046540b410b80200008500c03000168a16622820142c102070403030b4003840030081008010407413070208007003011445800050b6984070f003060100201214106c0034000c1400319400310061b1151804444907110480b03800c01c5054440c58104445440b443c002100344102080014101c401080e50a0080900347c944c44142da80c0c2c442070007668601c449005005912034400100b1942c080d0b0541c0c0083d07024541522601092503000c5000100c10f58000803400c5524080c0c0041c901046c0803641c050b20010b4060700e4030301d039510749034846406a0882440c = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 482260494 1250 482259244 482259257
    0x2001050903120c0f0a1103070b0c0c0d17035e1a070e040e1507110a051509010203070c1506030606090504061b210b031501091103100303 60
    0x125030110820034404003000e06011031745490054980b00010800d0580024000d00c1401f40101d031100442c010345240090a03001449140078040401c02480c1030b81d201078410700101c10600ea54141004021446045442c0c280c150040002510b0f42c3d000d400340e600014000c0c204400046152114450b4414000042c0101000540030510485060300303401001400713040301000b60103002e26400c01c8203114016648941d01444005014081520010030000120f9000315050003114080c400b011504000d191400d41038190354080c0041c0380040c0d40c4019151540220280c021501002042030303402201000254190300b081003018000001440005142c03e10103c68181d009040fa0300c03500085030002c0c0e041c01020754400840c4014601540d080d590b050410321407500d4003111802e907604c040c0540da070314812040b031032043c581c980b00c1200c140d84025464140b01101c0307079410001d045c807181c078112491080c0c1d490020203108880001340100a5031600740104203001000f071f10107900f00c0b034041c103040 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 482261744 1250 482260494 482260507
    0x5030c1c150507020d02190803060d06111b0c03150105010c1a010923010509011202060405060403050606010207090b03070e09150420011404090b0d0f200105090312 72
    0x80030780d60040d128401c00c1490101041206580003c203121013404607029251114003a208101005a060201170080042000860018100160700441d43c1b8010440042c4110054000024541c00030b80c00f040859441030a14403241010f0140c4841e41408030010409902e002c10701c860711000511401e0b05000c500366941c8148041f907540c50241c003541c450414041c2d03851b1100040100036004d40203030484030085c44201410f4600030680d0603960000d0014030301da071919450040786d16440340c0882c0c10280a01001a4035200c1d036010300055440380005e85940c1c5060400289030065903404890759500f07100d04207060381c0300802e890050b258480d001c854540e80380340005140c0001c4aa03003805404810040000340701e00c0780f2885003114071110740f4560507000744d401110301e10f60550034408021b80802c000c000000956000850415019047d816251140e440e182c0014200c1442907407809504d00781e91481d00c07440702d07050f905000c09081c45802c0c9008280440d9a4114540003c42a980005080e = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 482262994 1250 482261744 482261753
    0x20d0f05010f09183807080a0507020f0f03071106030103170d2a03050702010209011b020a05030a0b040209010504020a1d01140f120112021012061208090a05030c1c 72
    0x40118240d0042601c01d42d590b240c1034141442611140c09000c00c6000301100d40441c004105c81c0c5000d86501e5440d941d440d1030b91400d0f00010320018001100394412056040242d0340e0a01444245582010185484464a040a4506145207030805102e107104000510025408a01004454140c803401d9a155540840038200515003291700741d04000101c0320046455402d09840702c03040304d1340d54080c80b05446500d07003a420b0b802040180d5010907101a605042d1101c0c44900d501913500041c006207040365a034011905000704144c0035510710020300e00b08000e41c208132030000e0052109960451500c0004600180164075000f0051034618a00340841c456a110b071460f001c00040c1003404603030316104021001ca00c0d9000c43d01021031701c100c502c00003804441c1202940912500a000300340c0060a000049403140d41e00442d0070500c030f80c0c511000c0303007140310b0b00b8000c10414881c030009980c0e00d901c902000a0b02000e039011031700c00d0384203010912103504d40c10382c1ca03070041a62003122a00f50500303240 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 482264244 1250 482262994 482263031
    0x60e0306070f0e120f1501120f020402210709061403270106120203010b09040f0213020d0218040f05040201120f090203010c05070c081507120f0f020d0f05010f09 71
    0x3055480803201518008403800405c004d00d40051500441380305152480755205040d109120302103070724400c2801e100c040350a043d00b441d05248002c00c01131511072000d02642c045850360018501d0942c2c0d01c1c00300004560001707c054080c2c2050b044c13041c9094180c01440c10390b40701c01480010b9a556400070208285200d01c51065440350f0a802441075a440d800c1c096909000001c1c285d20940c01c10050b58900e00300b0600d2140a190000410710303403084a40c007800680c080025044c0070080c0c0c00c000b03018181a145c40a8001c481407070700961924007130704040006072280345282045a0340b4150a02c0010317030300700b004003080b9800d030704000c10041440110b0000a06001e20069019400d040c61021b40c0703584080200032407841075240d10011511040f0b8282e484100e0300d86927081007820000b02c2d0b00745011300c4035005988025003010480038003400301001034030301d0103099040780c60300810800d615000d64026149403021202c0200940d62406e00d0750007840c0d4040c41b482500303550324409007407024003c24 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 482265494 1250 482264244 482264267
    0x109080115090b0f040e10290616050105070f0801080105060901060315121b0b04080a060203180f070305010e0a1a0a1113050f060901020303180f160f060e0306070f 72
    0x307004000401c40a0394540d1100301d445480440c1c2c0d42380c050308142c042c21084044150080c08000d0403130059568052040550000c441c44401c000031100c0032001600034026188904031550b144e44001c03001c40c0d405000790b40c0c1a04003001590501c4208140c907102d10000504440c0d26107400700b02c43d500e02c5496030f03e5850b03540168048561610304070003405000b1110300b150b403103628540314400740c0e00c0c140e034000b41c048c82c000d4800542002c40140049031054018642003850302c4130110740315260b049418a480c00b0000401020341041c0001c10500000380700b00d6254401c0c0c0300c0503220030132a60f40e030743c0620071552101c910142e40e88008602d8840c0c1c00c0d84000808441d1424059440200405c0305000c0e2405229840c41203c0740085d407101c50400200340c0d2090141a001903080d0340b02d48400e003c030707001942e0340b01c205442441c1c03210380041000c1200b4416889107840ea0b1400c60b042960f81d03a02d2040d90740201003404039501704403002e500e0005401e58801400d00d04240d0405032143d04646171214003 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 482266744 1250 482265494 482265499
    0xb071b24061e0b07150b040f020c01050f060a080a0b0406020903060c0c10020405182a040509010e090304031202030c07060905010305060d08030a020f0705010f05060109080115090b0f 80
    0x4540481c0115040c20102c1d59a00b1400701e40700e04a64a1609407501e104940c8000c0096100321110780318003505401c82c20070140018070128000104041005c00c0303030080350320300103180e44460030300401a0b64810001d401c402c080e920f16010f641000c03402555003042540c0207003c03907010343c00a0188083d43e81078595408005060300e0345401d01d0840c203130080d002210a5505801005c27010820101a80300700c0c2c0c121800030f0710b0501030000300c9c031913401920340080c000d214002c031740f909442403001520089403044401c4080c45031030314140f40900a02d41d0050b0080340d01100300700c045c8402d0750400419601141c4c0e004446034107030000303400124198040c82200c0c180703603c54240003046080e00b0140420070355800381e0341002240c0d42c04081016130000b0040203804d511341000840c40301d2078260028112081c02030b210a16005044d40c0300d900f11503181800a09040e0b481061107a2036074001c10307030310041043c00028042c03001c00002c02842c60751144950210640d07500c00c42095601c400104094a0100 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 482267994 1250 482266744 482266751
    0xc0f060417060105011701060c020f18040c09060f0506091c0b0106210203040f0b0a060b07050307030908340b03090c01030f150b03070912050304030b071b24 69
    0x185207910394880007030040501050110342d00c1d840c2d0104207140c03a4122140c2d42da680344c141c00d85800740074900c003d014806400406d100c1c082c03901e03500390103049400340748250302d1058030910700241002251043d4001980300521108104010f030381d40c000303680d01140100c82c201070b030b1060240c1520b603154500d80c0080011f030300100001030507074001f03041d0401d240769001c210038150070305d009040891200725001405182c01c076840e074010603958240982d000100f10b10000c0c0e800d4070f480714001d1541003004210341550000503c1c1701010b0b44040118020701c5500c008100344001e68103015a14400c0c060880707200000680c1d550040003031013070f04c2c1c401403160200c4140d0313a08014551175150140c400d02c2c540400d00308001042c1c14501441594a014030030072049000728285020540036900181951003040044440800d500e11010918020680308030002d40ea120720b98588400380d0309004145c2e000344548002c2418614226000d07c201c90707035006001c000d594070002c104200c6070900954002c421840c = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 482269244 1250 482267994 482268029
    0x14060c0a0305090f0d0816030e0406090207050d02030301052b12020309010215070504031103030928050d0b04061805060709080f12041e15030f0f0e0c0f0604 69
    0x1000070040c42d0f460320070b503107900e82460400180038285d80c03892401048588200095541225213a2550a01601c245090000e43c2007072000101510510781208000740d43c005110004c01500308405205000c082c005581198500360001e00980b091003018800484c0d002648600031003413882c4500c00315484901030303040350303802c01000f9500e070030003d202070240c803036520501030010690003168841e85440e5100c91502e030a41d601d440b4602c100445e030380e8040c8814006c6c0f00060303035503a10400c490911004500f42d0003520340021031480340581e020500903035040c042c18000c2552018580d41c815000600803074220030907030307000c0b0703032104800d8000c2e2a5020741d0040c4a9040d074000f241100301d07911601102d056501d243e403003c1d1a500103040c042400300040000304440071500c43c04113000c40b5074003201c10b049547c03001010f0f890b260b09401c050001c0d40d04d041040e14240b181c42a2200c00400480404c80303404807882140c0d03200d0141c128207200d0102c100302c15080f640c070750382118003510b0f408200201c00da6 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 482270494 1250 482269244 482269247
    0x4050d08030901050702070e070e0103090b04083403321b0316030c2a090c050c0a23030f0a02060921030423060a06050f0a14060c0a03 59
    0x401c01d85210280303500341004281e1551000925100742c403500e0b0075071041074a07071301801c0d038035102440a0241403580305c0f02100301051101c002d0034440c9000e8810720395100441c52055103403c1103030a065600c2c40c00300d008100a202170341c0700c0d240542c0d454101580e804012104200600040100d0b01c0c000d242e814014000210580000e041c03020711210f40040813081c150740707441d140d008500180c0f00040c000b10020010034030a4090101380c1d402403806540b010841d40c14008030100e50300d180d4001880f2400e04002403442d5105142d018001c074500142048100190070703403141c1c1d910202401c0003016805081412920054600b0040c0041084a6907a00000203030040764205441020140c0034600000301c8485000c01e08085082e00c46540002c0080c14024012041d00b01400039501c070040180c0480d0b0b200c034290844840c200200c4002c02c0075190421444080e02c84070340015000b09041c5030503a83e6a00c0b02d02200040e14042c1e0022a1442c1140c0c002c980c881c0954401c1d10181e103d620384100605 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 482271744 1250 482270494 482270497
    0x20f0d0e010506011d06030a060e09060708062d030712050a0606050906090f1b070311120a1b11040908030f010b0319052a0a02011a091602010204050d08 67
    0x52000c0000340015614100199001240713506541c0600d02d11040044061030720800569010005600000d20207485045030b80c0a01d50858582c4c1e0b8562010050100c200d4219002e0303580244100c2d044426101e8080400d00d03c0000888034103508481031000e40c1c42e41d0390a0003104040c1650440101e4500382ca400c1c06a901c0d040c5080544105140c05008502800c145001d0b52017241e0103801b006250322800040180e60100510000030710815601c603400c041d03035a000500c036490103641e0b004038041c0303010640d505140302002001d1064504224420301650080c65042d9100c200e501c80d0700c140095820403180018a090149520518002c41402001111005903010742d9100036207060310303a00c85420380c81030720040d21950210800449542c0c401109a085158014000c070000d190311902c000320f01000c4074494043c610600c001050b0810102d07824400c011200844120710071450708960b001c21a812006040080d64054030b8074119890b034000d4044400a041c060301d000c0d0750b07520f1410300a580703 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 482272994 1250 482271744 482271761
    0x20a1e090e16080f0606070b0c090a030f14010504020321160303021207020c030c041a0307030c060e0301150e040c03080a020109150905120c0703020d0807140d021906020f0d 76
    0x45625030010581148000130080e129100103891a85041080c3d140e4052320fa00090101030f0f001c0040103103954640381d40340918011445280050b003017040915011004070075224590005170f1404040101603030700001d81041c41c1c04107038255034200c0d403031242c7d0345a1442074900100d003070320816400c00105070f807680c0189120760110403e03c916031602e02007240c4603418003001030b901d40c3c0b0030002070744649416400745072200c880c50b00c01d40030381ea0404042410412a03520a50700700c0342c50401000501c5d048a140136464100301d0003080904501c204510001d05240666609410381c08005804c1007003100c01c0801560b0012001c0b40c40d4915204000e01070102800300f290010317091040c02440b0526402500c800a41c0700028000310300c2d810b610402c035900101d4071081c0600c81d405001026032280000000120b010300c106a554142c03508000760406052841c020596008a40714000300341d0106600214181e1800c0c450460030b05410711501902031103054010310f101c0019441101c9000358440b111 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 482274244 1250 482272994 482272997
    0xc040803030f0601031103010b191e08010306060b1227030309011b0c031d041d03040314030702030d080730050106020c0303090103020f070c0b0c06060301020a1e090e16 74
    0x300d0030001b0710010b01da000030b200320213207550180405050f42d03144070564503108521780340406800a00c00c0c01c0c003088515102100021503080c000510030b000182c00cc481c0540200c00c00726152582044409680035030083c103a121000052030310b50400340000c0310304c00444440000702ea4603418900e03155402028113050404801183c0c0102e0301d5224050420a03404e190151034003c0c2048034040300c1b4400c01080381d0b40c0d6038050b54070411691100f00240014034000c5076000190749407030440c5480e08507843e0050320b502c2107074014054040142c1e40000c6100600310b8925094003d42c5445000350352550740441041030811601c40b108904892243e10b002c8900040f2000340002e076600e0b441640c4034520544080c1d01078104028010740c550181e00105034624401c08070764605020750300c40070b110b40c7c44e940155012250003c0c54810051080001d02d41020044000314a0003090180244c201d41020407004c406200e00003c150459000c0c51401d0300a00e5030104104062238041d00200284130350030719900 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 482275494 1250 482274244 482274251
    0x9050706020c18010e040203100203010603020d1104080a02150f0301060e0316080606100c12110d030b3105150a0e04020a030807140f010f060e0415050c040803030f060103 75
    0x1500d000c069200d80d1a440d400b0f0410140d082903840f1440a030000c0c4240e03014400d0355440c510540a0340f009500030203040e98011b0300c1e81006103603101900c881d1000300d604882c0a02050100200218441010950444041d4a400104044d0030341900800702400d614071404070000840d95080440c0031400751046050f03c05540c91807010b2140483d0a008080c0c0e19400180002c2441c18215012113198929003443d24802482d035a86c0c4600e5509140136000040d40003083c20708086003081030f0702c0300100030300f414821006c5440100e221111158105600e65001281c00e03051b0030000f0441c6000c240b8445018062482c040344c4009911115071144e6000e00b1301342c400051419042840a402590700030030440c41246942c0b241941030300017190958000800400003c1c11400c10820b0f00c40c0714121400104543c00a001c40b98121001a0b1000480d0b2a525040000080840c009542c2d222040c4500250980b40c9842c0c0d04618001d9400120882c07000101741f004840d071301c001141c4952026030782803 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 482276744 1250 482275494 482275513
    0xc090d1202150f13031b0c031109160e0114070206030f0601080109150b090a0e010e060427060c05090a06050306090a0c140c01110721030501180203060a090905070602 73
    0x5143c4150444c1e0036001c6058540003407000070b104620543c000007441d09031446008540d1070b6000d010f9400c2d4411a00c010b0007500340031036402c090341c48690160129201c210903050002c1c001d000040c2c1208aa410080780100380b002c260707024010354070402c0c3c0140c69680ca07071030620f00c0d00d0340b1070005840c00c5000c81c3c000400003c001e0458007584824505400e81c8198180c60880380c00000d81282c80d00d160700400b4184041660b42d0a00d8100b8000d1002c23101a041c0340c200b410611080b5068002c0d81410402d00f2200c80c0c81c18181072a18545203039002c0c03c009201e003c0d5000c04c4880c0d004450034580e01c54850700d0b00190260740800514041c0e04100d40c0200c0a8523503c1e0484119020301400c40007007201b00812606d90b01c4410082c00c000e050030000070a062840f044502810350111100302d03404030b84c11514488682e094235244194504909041085506090004006205d003e148070016a00040002c59a84071828a40001e004400052007000154940241c507000903000301c000502c50ba1542 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 482277994 1250 482276744 482276761
    0x90d0306091118060f03190f02091c0c083a020a080d06090504060912030603020901090c030b03060c0a08151f02010905060c030106020708030309060c090d120215 71
    0x34142210008140070f4901003401c0d075026a03512a07110f4040d40301000340711070484181007034003d502c138000754100d443c80c000003904d50b10104c1d04140c640854080c0305010f21141500d840031084042c0e00d68051280c0e26201624107118040e060f50046041401014a4458241c00c0140700c8412003440030726000c171080b4000c840142e1a50a80250300c0103a06c4601c204000c00c0400b0010700c1600014400401c40941715000a8140d03035007560211011a40d900c2c1e104148150706047c200c2100081c80e040c46224034540000381110300c10300171001c3d41f50360b5403c0c00100034080d5100720042c40000c0c0030394440740b40102e0f60006c690010a030000110710304c80b00060480d26280c00808403c0c80081c00c1c00310181310403450001c0b21024008a0b070a565840400201040c2c0c1004150f00c605121405540d5035030601c14001c2c01e00d0303003a034480f04990f44244144240d1b0701d40400c0140d8400180000f00d6150b1181c000011016807400c0400781c41440e4081c02c4841c500c0d80440e043c454038804406000158540920 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 482279244 1250 482277994 482278001
    0xf01050d02070c080f0f0f061b040e0103030503040614150f0a1e06180e0a0f06031a1807180507020c0604060201060e13020d0f2a09060e060a030f0515090d030609 71
    0x16000d40070b412000c005444009c0d1810019000e00f007064005003025229446642000c5007a00243d01046010003080100911400b4841c000224603030458918203000da1840e640544655410348520240740786a00262550281000200004148142c441e0000180c00c459144d4034010715000039405400c50901a069403c60003c81d688051f151406070703100701d0aa001007a06c203000c0d1140a46031a40023001c0b4501100484007120003450342c518a041c20005c4194100d164650099940c00420041005a0f251030040300c0c4420840000310300b55450000403410101c43c8225140e112034041004512950305600140984501c42d0311600b254441c110901c242400c02c5200a5010180c440c10740c0025800388071091a852184200c099100103186c2421403000d480200c400d80540e8442c3c0410403000103000d604010729500500c248141071000202d8281607007400081c00350f81d516401c150410004202030341070b003501c02000c1d4640d810b09520703c070f4540558036032580c0045d041c61000f02c0c28100c0da20 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 482280494 1250 482279244 482279263
    0xf04090c0e0901060e18030f03090c030c15040b07050a02030303070c11010c0b07111002030a0911040522080405041401031a060307090f090204020c0f1b0f01050d02070c080f0f 77
    0x21480300055840001c0c0c06030200b070b4818502c90b03c7c003041c030610100c01c0390070001d103001c1c4220501404444450708181031400c403000d28460303c40c524480d080b0500340440800c840a0350f40c4036003400d580300c6207802e0152818801c00f90007909440300004001100d070340100c1740300030f451142003414441514900110b03000c1c1d0030184041c0c28450108007140742c40e13024005413030301a036105094510b4039011070307040c8040741c10459504101c2920313010cd410402800c48010704481d44222401c202c2800d000260350a901c10551807400f039416002d4032007040c4581d920075107000340b000a006024203648040d441400c00c5081c442101e0810f4244e203607039000f40580e01d00070300c5240301400130b020181c42c21741e000c00980114002d14800703655891000b809600d03607000400e0514000002054980102401580342c886a6807200380000030f032403112900703070344c481141300e2081c8000d103451500d4000504407800280f040940082580d820302000203809440460741200404110040d18010001510640d46440000 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 482281744 1250 482280494 482280509
    0x906041418070f0207231c050105010b0403110103140601030c030e150405070501090303050a0503060f040203040c1a1206041104031202150a020c031204020f04090c0e090106 76
    0x9220520014044030032803604808020002654049881c800044240d000d9a8210025510000044009404100c903100078070380441980d0700700064604a482a40c4500d00c103511400620100c1c900414182d6607a4101d42d400200801003543d48541091842e07101e0704c012201e9848005a8844640c06403040601c09544480e00c07415070703641c1100440081c107410000030240f65886c080202e1034201046021703a440242d04030b8100d103061a060091802d14a64070403410000111014400258070809440317004055040444d207a840303020000d20350203801c20360303aa007081c80442008280540d1100c1001201c480360354252200350884640d1035a482030104200c03859602c400440d50f00e0905a014482ea003070049260790a05490759074840f00114258420300041c1e00160000003040c081c0c5040c150860343c00b0004500d000c6c80724140326241c0c0110741d00722400700e40c540300007003d544402d030705440b01e2a80140200120511440c02d86c40f58810b50040407054001ca00001d031192005224050944481 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 482282994 1250 482281744 482281747
    0x6200304210c1410020c0a0203190f080a05041505180604120b040503070602070c06020c0a0608040b06040e16030302150402030312071809061806180b0102030417030a1101020906 78
    0x200e032900c5410780c0f8010319005480c403c0d074001450001c128400780100142c868054400b9901d1801010f140030081c0341e0810481001c0c520240c006104018003944e215070002000d522861010703029079080c040e42d8041d14a48612940c800501c0e0360020003461003056002c03131803280000030b0341845040c0c0540d0064040d144841c0d00328001180300d206110741d120388510200d92404401d9510311741030b0303005404201c0b546511844288885901400140c4403182c007901c102130194a4600e0040c02d030f07070740944050a10380144021078179070785071500003001030a0018215001e046111101c601407410303c5c4029001400b501020500325441c40e01014041c0b90014000c40c2051b42903e1021a04d0310064840d01c2440040f13082603c0382d001c5103455100034045a030f000141c8910301511900c0d0302d5800b1600d408080d00c2c00300300b401725a070b40240e0542c064a010900103a8000d007030005038910f00c626040214003207005869003841c404000f0003062607078000e9a07a0f1224081c01600c460a0f4040d000050354400f90 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 482284244 1250 482282994 482283017
    0x90f010c06062736020d1e021c0209060d5717160e15031f0c020a02060301090b040b011b020f01030f0903080912250620030421 56
    0x6140b0031038a1300c10300050404428203896030303036183c44214400d114150303001780d80380c1c50040d858007600e98144000614080310114180b5400113050343c1009200341d100d041d280700d0704814810100294401060944800c040c01d2100c629094001e251002007d122002c01c100001c01c00140d0340785984401c04d1103e901c40c07490b41003188110341201c103503c1000c01d51044072120f0030902c520303d020708010000c200e00d0100c10700386149150b11451425600303a000b903100806000086030115a0100640115000001c41da004002d00b01c1c180036900c44042c3d4080300100001c55601420b80c800320b90018211420040c8100d001c0c019251010304030f028142540b4451000da0140c20711141e509000c807014540098a002c10b03e0400c0201c44161000f41d000803145020885a110b00300f0400641c0c0c241907408a01340303000c100403518091241c08000105c00c0d8a080705008100250700318002062500b4519440321a04002d1042e0b15001100c06440100d56002c250309000384150300e107400c04180d9070352100c0c40030 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 482285494 1250 482284244 482284331
    0x71502071203050f18090106030b01080609090c100216050102070e37020c0d0306051302070f080a0f12110a03090f08030903180303090f010c060627 65
    0x407140318041e410310004009508042602500030b000d00145c0690004c503540250041c4200e6240580003136050618003141c0303004e01da81144d81982d0102d421a41c07050350781e072010406130524008846041d04050340252440e000358000c6610b00d4404c008124038401c150b612001240da0305060f202d07840c0f9040046c1d000c260340b07540e1303000d4448003c40d044050075459544850344040495036104609030f81540030800c50b0514038180000901d0700310320f2405210040c245400034504107001000b1880e060360010761f203000c000302c0000780c500803500440b020703440703072071008014003c450390011520014184840d0031021902c9846040c00c02c0002c118814140345c2210380940083c85401400d40d50b401d01642c030200040d013010001c51042075030348003450700c41000850074880e111604041c68440d03041070100c0c109a480c1c10300098042d080074a00b50040a4950030000f00070711881d081034a000d0f40030850040200103075038400d200c200043d10104201c0079508964003210840b8543d05c03240d480f45103403440455 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 482286744 1250 482285494 482285519
    0x20603040f0f0c1701090206160c031406010503060f070801061b0b04080901030b01050c0a06050606041e03030e06090307290c010501050f031504060f02190c0507150207 74
    0x1841518aa040800350362646100780154a0040f81c04200d548410303c03030311040d490042a11a40300009000c03034007850b030000d1300c140540341503001c40e03a226811082c2800880059200290f8000956020154030090f850f5250032003405418024401c2034049500c2c1c00386000003910407071050351912050303400d04030129a558000d02d0b200040480351051074002c01c0d0141c0b4200d0040384282c490702c1d030705c2c59044005000d50f039107581e01e20305100003032100030b18500020801041c2d555000f00000b8203941c1d104002800d0303005682002900811180760064400020b000007426603003c0e0300e034a451006a0360400400d8840c0d48031040e0960020301c42089001703851002164103401011080b0743d1001c0006044110341c0000040c3c00881e03440d400100440c0c10043c10401d0050300503800b5042607100f00100310824100130780000c194079522607910f071110303803a54103440d08100c1200001403000048800100201c400f590261303514001d02c000040c841c0511030f503100d031000d120340140074068900240c0740e444 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 482287994 1250 482286744 482286751
    0x90705031609260f121c0e10090501050c0403020f010f02010f020a0915050a090e0a0209090717010506091e03030705070f03060c051e070317190b0f0d020603 69
    0xe2010b00140403c001c1419810040281e10550008031041c440040e40c0f0325140103c030b800c51113900006602908034103000121781c486500d0300f90b91301224848200e582d008119901d049540d034042c1e1652002c00c82e00ba0b400c26514140200024802ca444000201c1107510035071000a501c10b481000600440d40591013041d90b650f080c0c00000350702c8035440315a100f03990000d000240043d501c50300500400021132090118040e142c500507041c5004820041c00c500701c00e00490900030591000555800030300d0701261241c03403029080f00520305000402810542940340b000351441c180000200c4c1c541891803d4400ca844024010f12039800b00710f6540401c00034441da503030703010b001c10000720002c241d04100d082c000b000c80c40742c00d40c80311f0301d1420810120f480c0c000d119070400100300714040320031605008584040c000307511031640d600d900780340a65000a000090100f804084800c01a02080071041c2c03260304281c148040c8270000080381003209400c440c0ca40d0542c0200300702c18103409814004080d660 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 482289244 1250 482287994 482287997
    0x3050601030b120f150f04021c080403030f08070f02031614060106020f1b010815040e010e03041802040b030a051f080c04060e0f0c0c01110d090209060907050316 71
    0x10040c500320040380d8814604840c000b20307a0710611385a001e0900070414180c06003460801040715080a000d00e200e03408000e08080e1088070710300c17941002030010f40c5101418517486142c0a68841d40c03458050b04070840c400c00c0d90041041c0c5c90004042c01e004880b6604031040680c0a54580814000070080c141c000500c10f036204200803244c410922420840300d8041c1c02c0540040c0500c1c070000c100185032199001c4c4041020041429000059802c421f540742c00640d10300140c4000446140807130000c10020800b26059070a01c10140c3c0c2c50040800104250b0300f0f52071000c1141202071500790103902c540d1051101c3e4000400000d410000c0a40c0842c0e0072034081140c400000f9010a10703295035441d40d0b0089c41151704035900600c0c0c0c81c501031150400400744c070000c0d40d40300e1030100750610200c8801445010003080000c0c1c013104014081d840381d00d040544035030040e1101d5036030322650001c04603c4e100301d0044c0089004200589421712103540315007559030310703a0700d90b60702e8101c02e80d00c22030590428070 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 482290494 1250 482289244 482289251
    0xf02071811070c08060709030c09020901050f071a100e0a111c060e060a03151505030d0c060f050f0114040b060301060c02030d0912020405090f1606230a0305060103 72
    0x12007041e4048000e18480d40a401e2101066040025180c2000d401402410900154080810000e0740501149045800c100c03030060f00d981c101c10044c0e80034401c2c40c8640002100001d805000c2000d00c140310210b00d00d4200c5200c080e542c0e450a01d20343e6003c0382c01a02c041d603a504002800403011504009510203800d00c40c40e0410b5035402d54403100c0f102d00b00c0d9440e0402c0d150101801041c42c400d503140d5000b40100d80380320400d0b1440d1038203683c0000d00b0041400319900c03a0501035075100514401002040d000d411a4441c9090440041400007a81400c0300c516080c080c07000321190301809024080d5002c0c2a0410071640703030a4121004018034100d042d003254444c0302400300b65842e40c016500800c41526100f2255141d07104050402442d0f5140000340002140c051200c0c2d645005815149a41a100051171392148800103241c900341c0b0b09280704911854000e5071140100392000380441d11103464003420003401c1081c0d00c3e020002e00301c0d101c4410784240407420340c451107608800e4100e1010705000 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 482291744 1250 482290494 482290511
    0x4030c030807151a1e0303310609180603050d030c0206090f06010510120c03051512062205190c301a070e01020d030510030204050613140105010305070f020718 70
    0x1a0864110038404c0360507800c0040040d402c000c0829415400c914402345098030070307080210181505401d405100c40ca50644007542e948246141c0c00080550b403c04202d07014081c2c044401009803480f07100da00010300038180400c01e0b10000080c9440c21400790030152095078240780500042c401076549200420508109904c1c1a0303490303116404800c042c5590110310b500d40700902c84000c1c0c0680e0746080c041e811007602180c5a84001c10501d4101e02055424903402c6002c0c4200c038600211044090454014030350310002008238081c200f080184a015044c00d0299980121905d0240e00c155440011554860b03207030740f4003004c2c90480b1550384280019030071482c0c2d620003032002050840d600c5004c940074a880d90560f60301004601415002d601d030902c050300d40244400c07507003411032200a0140e42c480001c031307101e513441681001c80000c140b0002c01800013040c80348560030380b0a2140d41c4c0841d01d07080204c0e05082c890740c08405c200102da0002c000c107a01c0c0c0300e001100245c00038004901d01d81d40ea0010b = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 482292994 1250 482291744 482291749
    0x15140405071b060902120a150506040e01150905010b04080a031b05060f0609011403072c15041107050c09180f0148030204030c030807151a1e 62
    0xb2180e10360282d00000b800d0001da00c140050119003249840c1e09900c16120303c80007803845001d080f0980c00c0140085001d45480c404103024081110460942c1c0d420b0411014940312100300d41022a107150100b400245d988502c0d904d0280328038020304019402a07481440840e010b1803480c81d000340340c2c1a00340051601d6468540c28108180d805600514400040c07001314506608641c0c05081c0500c00240c10080d9280040e0b0f403004180300d171846c1c3d101c2200c1d075a8804c03491088584400060176113901000d1600050000e0180400101c1c01e10803850300b800100014990700964503080d0344207005004001003502002110b00c2e00804001400484002220b040c4c10244418070346612a0b10000c115056004241c21195548800c10790524001004c6540c0080e81c24001364400c0d0185200300002d5854035070118040d12541c0c00103042c3c0300304244000108100c203002000650b000e03c115044020b107189078181502c1c5540603468811403059141c084038075000c14811150800c0c10b06844801e66100b01 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 482294244 1250 482292994 482293037
    0x906040b030a1406010206102d120311070e040809031c0f030501150c121b030903060e0109031d060403200907020c01120e010f1109041514040507 64
    0xc41e4442e40341c8070100b80d039a16568106041d0405001d00241c03c09240c01c007803500c0d02c40100c3c880c169000d564440e202d0fa03031046403d56100c194078103080341c1e8000d60b11603030010340348201900d0480019032080f011008000004c1045019600d60301030341c01c02916240c407403d9558221056256042c003d280012440e07882c0000c59079110030980d112001c41105d005000307401c44005034003c02e04c0030b03110440245000d52000d4218041548000202c0b000320060710102c65200780890440713414101004002e0038590460000b20071244111410f00c002d001d4501c0490a844030004004d001c02c400003607007110140001d10fa071801d1400500010b0410b51b607500d0b5810400300c684101d00c000449080e40c039195042c242d80c1280c4c01521400184514003c80300001c0040341d40d17541080303081d0b81c1c4181d10f507000f0b5400c0d0041003990040680c14016400502c4c0305030242c3d4080040d8500c210714000e442c00b0700300a540d408008880319a40c0ca00b0004004009000203070000030049002c0010b10001d840f4400c02440 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 482295494 1250 482294244 482294251
    0x708030a0e1017010f0518011203052d070c08190809032d0705010807020c0108071403040515310501020f130303020d0509130c0207050a0e0901060b0903070303050906040b03 76
    0x1c40208925191009020001c0001e110022049001000509c00000910882c5214603490301c0c0055881c00340c00705c0322100c60b554208901d035103440007071102d681285141c041c1c0189130054a032284465a29041660340b00f40f20000c00002000440490300418800700107446040c0010b000d0307450b611007a028090340b070318520a44607185407051401c04008101000000050002800d28181e50300348440301075510394407680c51038100311100001403a500e22500b807132254076032820340b50ba0b03e03402c06103841900c0c0d4906010308600b071620000042c6041003580140c850403030765240307100c1c13004191070200d1828036040501030710700d5902000350360044d484240085c020b4400214000d4505811868000d090100d541007181c100403007801004516502c41002c203014100e07080000900c4009100c040e42050040d42c07151307500800d074890004d403541c4e60015441c070405812000300300858946a0800d464000e0b4050700e40c140d40701035000e00009000d00e00a01c1030300380060550b401c0550310080761946a0044 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 482296744 1250 482295494 482295509
    0xf0a09020f0c0c010309021e19030b061f120905030c1f06050103062105071701020a080906010e070f0c060f0906050609092a0301090605090708030a0e101701 69
    0x42c910702c2e00e9070706204140000c6002d00e014444a113580d00000c00d10401d100a20900e5100c5061a0f0155560592200458802e1346100300c41f0a959040400d01900111840d078020018504c807802084c2e10b1028039107010320f045c4c849e0480082048040801080c207418100c60390301c010040305062280400458410001042d0030042490304078008404bc0d84040d404141803504000c0280034002c84960507019010211003480f4851300d080c180949029803541c0266015104106c0c10801050190018400b43c60780da1203441450b126011301d580e40e06002d200d1109500f0049002c0307054984201d414090025191403c1d02400169845550031208210b41718071880d6502c0d0041400c000c3d00e800b6003640080111501c8881d46064100c0b191200039046000450840070603540d40c80306010b1030200e030412009002003158a40714035064000b40b8083e51250024840c644000440d0040002140d00c460000d954000b80444041c0501c14190000c401c1c5a0030301c91384210704140a207880c1411030007030244 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 482297994 1250 482296744 482296747
    0x307210212071a1912020904060e09070503060408070f140303010e040605010b07030906080c131509081c03090309051806131401050f06071e03020c090708060f0a09020f 74
    0x8155440c0102803001c440310000e400309001302c640344500020000781c000c2c0e09080c4443d4109000840794002d10410301541e07801460103101141c240003071201c003881445c1d10740032200c88688400405965100443c1d0090807008200b000d0300010312070a0080c400340c0e12a10b04014812020840941075030001d0b002500301004040812040c45424090b1500409071a50305516040070f9403001401c0312002d0095a0038018103c0104110340a030340110ba400d400c01c9402e660685848146a202800007229074800258034401d02051502c0701160200c6445584c511800f418141c0c160182c002c1c02c0000720503014403c100100113003a071503c01e1070303908401003d6080e80d000d28141c810800600d040c0171b449040070740343c20042e414015560000505480d41161602041c10f81040040c6040c4a0094001c00f4007984c2c0440c80e540100400d031070301030300c1d109400b500c480c848446d0900420140071690f6200086100011502c141400010040a010301604032210583c031a100c01d003ea0340700c0c2107040000c120 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 482299244 1250 482297994 482297999
    0x2040c0e130b04020c0f101802060a031d01090305070215030c0d09020112020f07021923060403050106081513021f030902040c020d110a11060307020109050a110108090c030721021207 80
    0xf2030322540441800b6a08e59102e503207103c0c1c000c182e190060344001c009050f80c490032a1103032400b60000b501c020740360300024040100d0390307c1d0007071594202c1e4404034000d1141031101c1d444190f0540580e440713484285a42403c2a0b001200f44000d0030b6800400c1e4184800f83c500801e100100340020074030400d803040859940c24091040c42240010168036a410a1201009010b039000c65014590041c1d10a9401000101c000000408511481d070005005620740000050400c1e030225a080c1c0244461455040301e5451981c1c400ca03800e02c400d0000d5003d8940c20074103011030544814010782c0d0768a498001045003095000c202203410f900520300159202000c0751a2099114a480d003420007550003410000c0c00f2551141d022220401c1d4042c41900e02000084080d4401d40c01150034075041000c464200c4210b0070300b1102c81c83c0e0101c00c0c5000803c0400000c40b40000010403030030000001d4001e0a005182c1211100080380c007030040d55030150482419005a6540c1785007402d40c40820014044261 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 482300494 1250 482299244 482299273
    0xb090126010306060e13111306050a0f031209050307060522080318010309020d2a030602092106060108070e0301050405072111090601031407020a02040c0e130b04020c0f 74
    0x802800706e10010340850000544080891f92500b102512465a100c0e5100040c10160003541c0010b6009401e15000250343c210051040301100d0040c640e81c413016800001c1180d208000c2e004180c0c040d03101d900304001c050301c90350003000c50078400300e844007105444042c1c07014200e403554400c0f6441d610100743d45104d840c4246803946c0074230007400c0410402105a001c907078540c1c0d440c40d0192100d240031885800d0010850009030400f048160101202500e03803400ca03000717400c80c06045000d242c03c40301c4440d161440d1542000050500070044c2025500c071001160080c4004258a00b0000030400c41b050300c1d00e090242a00592003035028000050070b00d601c48416040001030b0600d038052020509005c555214105400b00c0b0003580c001d001c0e070b41e4400c0160068001108082c2d04c5111a01c04c00150982c0450014041807085a0902003641029401c4a4842003842459403044044000c3c68801c11103030300074601494082c00241c10180001201340c101460741083c00c070690421404150301030b = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 482301744 1250 482300494 482300519
    0x306080c0402120f0601030209030307030809011d0303041103070b0d0905120403240212040b040b010806070e0609031501030c03031704030822021f0212040b09012601030606 76
    0x2054103540450500550030600520200f01502c800c0392040c000011494591103501119a0301c100078044a59542c4e241c580104244001c495032041540780c034084c0801c2003e20503010945003003840c015411070300c540d212510720380c000001c015403503c00c090703002840c0582000642200c4601c84030000e820880b6050450600700c00e08506012240300300418000030300d41d8540550301d200042e00c1800c6044055035100001d01c1110000724030043c04c00108410030071305030755107032256104d480040881c0e6669a030980d03a0f000165501404103404c21603410080c1441d0001c0c0190490080c101d035102c20307000031081c00c0c0500070307042030b2582407003850140f0900d03030040a070718007880002d0440440f83c602514014004400a408140b01540c0000b035807003010702c0d54a0210303256800030306400b425160680c0c2034080009a403200d50140c02111000045842c98000390f9044131010f00e04c0901e4110347c90011180340c00c00d160742c031440c0c803d1f400d8800034080340301c2140e0307010390301c103141c002141d03801d203201c01d03611 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 482302994 1250 482301744 482301763
    0x16021c26060a03122703060b040902060405010f050f070305030919081206010507050f0601140105030f130c03060c030507110c10110307051203071112160303020405060a030608 77
    0x421200001c0c00607940328060090704594001c1c0328415a02c8514074115129560003441480e4080c1c080d84085400000350802c0302220300c6064200300a00705c403c10b10007540c80b0101c01941c010300030700040080c0d5000d80b041c646400101d10300700d03250200140300c070551600200c2064002030004001c0040c1c140003045104800020990307030360184e0a8980c1d54031000d01c920821050340715003800128a250340620150f40d0815808070035a001e402c40025440da842101344101e0491841180003483e03254010303011680168031700b0312458465038070a40c0070340341d14a0b1828200e4031540b0040c00040415103910030f214008005541c085514203095100800070900048022030940019980c00030a513110055011a100c0383e09142559107000324601c0e045008952004c0c205000748181208009004401103116018640301e001070300f403154040ca95a1041c85400c5400c5240c208000700d014689074404d460028800e14000d85400d840744046070a03904187c4248020070344804090080460070300101c004e = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 482304244 1250 482302994 482303057
    0xc080d0612060e070f121209090e0609010f060503101a1c0510020a080f060102030d060603052203020d030b040b180a0c030203160e0f03010207080d050c03040b16021c 73
    0x1c17503030914120244425110900508600d002c1250166150141ca0008020480c0da20200b10394000d801c0d900782c4400b0b007107820303500035441c00c00c120900b242540301d00025207001400610b0581c07061089075008103c1c40c0c400c9021400c0d904144061541d0300016000781c01410018010b81420500d0070314506002202040c158034014840071154aa1000c915075000d6252030b00c021003030b04c070000143d041d40300d004840d407941802c0070b10100d00150180c0045010f4000304085c03d200143e0102c8405c0e6500c1b0342280240146c10540c03035003032507034800d8208460040001304001440d0304440001451425081250443c2003401c50070420240f82e54401c03008101d02e281006d600c5e40c138100b4006441d150001500c5014072000c00e0f80c0008548407604040c0d0300c000003030021595409503003444111074000070f403c2040c1c03a050a0005604040d81c2e0140d0b40159480300ba4184681c540d29028584140111851011481209001c2812540039022000350412548801403240002e40f00b504940e01c0c2c0c2240d461 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 482305494 1250 482304244 482304269
    0x4110406020d031b0e0d05011a01020714090c0a050c060112020102010509060708130303090614180703021507060212070f02010c021b10051b010b1f0c080d0612060e07 73
    0x132101c01c010f012906034565500d0103140e481c80c9000028502a00100d004d0320f558a0103103080203132446540c06000c1030b0b200341c0032526000d40e0341d400f1094000d00503214581060499002c5591144004050007542c141400d190b0706001603107408500d406801d03030043c41e0500c0d0220858040d540c080c0f1404d81c010460002505044c0b81c1100041e0036180040e20b44003413860140d28036810b16100c0c7d40700d00300341640910140180da4451441e9028080e0030b071142d2904596240e411081c5980000b022011247e003d040241140440c070b0100700d140c2c01801040c1c80307103078080000903a00c0c9040602188206500c3d22901030f0660320590081c00c455100070035105540c0803a00007029903d800e00d5a84c28010101d030704060300d0140d8402103d190003003081000d640c80940704001046501900300100d11402034410f071030540700364464180c101025070010070200310300f420b022010841200003840c19006241c3c020070751541e0364604a40305d070721155040e0780082c1d0b1804c0c088010f03d410701c10304000382029140365 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 482306744 1250 482305494 482305511
    0x41505091e04110403050a0215031e0a1107030f1101090302120304050309031507080a050601080a0b1207090603140307031e181e0b0f0901030504020f04110406020d03 73
    0x141441d00014607003189514040c14003062552103030043c030907000a055080351916030300e2a0050703858001c901d08921910501c421049491150300a9a110f013200c2c0403500c4042e0850301d420580004040d0034100380070780783c405000c0e030f08030050001c00c1802c1c480e5440d400710001c1f40c000240303455404402050142d04044041c000b10382d0009030080591210074903e0f549032038503e0528614402c0342d01c01c98041c00f510350322041005034040514480d11050301d03880a140c0d5080726500031900101c1e0518040780d50a804907000e068a0341c0720800480c4050200b40003400800c011510f48001644100b0b05640c4a1b5014020010501c20b0384403c4400c590046080c00070b15a4090a00c1c0c40140d0303100900070030260b100b20031a10542012000585c0000d001e618651508140d800c07118684c86414424071100e0000616400d0800803200068040002a410101ea40004401a00024000742e07403240095030070b004640d07180e215104460340516080340c1c2d594540748000c5d0a0412400081050528080741d4 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 482307994 1250 482306744 482306749
    0x90f07051e011206050d05060a050610091403210403020f09010501020322050913060c090e06010f0314090114010f120b04050f0f03040f0f12230a05010204150509 71
    0x300d061075a007420480c11201607003540400401c4554000d071760200e40c03840f17104140b22011950038000c494104041c4081d035070b02402e1245015148002d0b0f0000340c00481e0070040201d182440100d040b50080540d0250080041401c5a5155400200001701300020b02001140341041e40d80713502841c1a075803000703e5890100023075164069020000c0e4030342c05008143c92141442c09490018040051400003181402c0300806101030420706d08440d00c61800b4038000c2420b0162202c0e04c100d0b15903105511203542e8040044480c18004441c020903d5200c0c028248014940b6103110b00c10400803000050124000c01000441c1d04107900100107200308aa003030090001c400598000143c000c2410042c2d61118940f171803074200032020400c1c840c0182907031683c00c0c84000c4001c1c0119400041c00c640390644580442c28100880e03c40c80c45081d100113140000168082d400c0c2840c079180e04481e611480462003403500740024003a0440b1941d500181c280140000106141c194040519082e42050300d907001 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 482309244 1250 482307994 482308039
    0x1507020f07030519080c06040302061b09220b03120702090f070504120f051902040b0312070f051203040c03030305070c02030307020103151805100605070b0703090201050909090f0705 80
    0x10341d042913840d030200b59041c00120000c550b450200701e402c80304549032605000b502d800041c0c403c07a0301c9504100b00300500c140340b8010303544110f100601c45170100050403078100f00c505801420a014640301e037500109543d052090030352011200700b415680ba220340c4100021180700400e00c0c4580c1002c0021302a210350f2200c00e480a40741180e0010320345c00f406007400503050f844044d0080aa01c6140c5070040b00c125072814070001c8034800c0ea024866881d10104068541c072010350b80e0405c51005010700000701e203111020317204613809202035954a1545601446c010740c0104c43c01d80e4103400b450340410426500d4460a54449031a141c00149064036500003512845104c0f40a4101070311203482d2000f43c14984100030080c015101c25060130445c900002000e44000c0390713035928200c841d41c40018242d0082045450055201c00301c0007403940c0e080c806074000d00f00200c0c140c1c100201808148056110700322014001c1c5135003402804820a5088844e01d0022140c000a0140304c408812240800700100c = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 482310494 1250 482309244 482309263
    0xc010801032303042301090e130209040614040b220b040f231f090b060607050102160b04050118050303070518190e010f05150901111507020f070305 65
    0xb81d94840c00007400708107901c0c40c0120741108080f009a440707001001c021140e21034210400a80720ba048071961611007040346501210840c0c4124020381029005140c50b030f40c203070f81c0b10f40700e8440010b0015601d544003000f0a01214100c8124100200b4045030204400b103040300b600d042d1200c2d80303032084035543d0000c0140e0007400040049480001800821000c001d1080031100030050340c0c1c2a070140075200329600c0244520201c04840e050300c7c1210303030b21352a0040c40c6201d82c129060b822140c03640801e002240d40070310002d4899560a0102840390b80310f0001c201e0f42280190654800b81c02c150a0241c01c5a03070402c01c650b01100507100c1d00c0c0000e540442a280c0c40003103400d02d15221541c0c0c01c80589010350004100341d101c0080c9201da16802e03180b0b0040820796001c9180100c40e40c2e01c42c038220040f41030174000d0710f511480e4084949a40d42482c801043c0c80c10061415270304044122194034070b86400c4180941134100000308200d071041c3d0400140c64400103420040a030180303141c80d01625928046c = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 482311744 1250 482310494 482310533
    0x150f0509040f0510050a0b090d02061b070617060102030c0d1b05060a09110d051002030c1611040e03160b0601020f0d091401090305030a03090c090213080c01080103 72
    0x8185445141c1c1d032607101e44280c25042c0c50600041c5448000c410301040c1501985100d00c400d00d0740481c0e0f4098560036948405c0000d059a220b48025800b0080203400640e00a01e41d00f10b200c131101c0c1c40d04000d1003071000030b1250b51a551901c424500c0050440c0c4002400f440c111360052060310b0501800141c8455498814140140e801c10003004860150781070900162691041d070052100e0500140c1c405540380b030041501404032203100f03040040200483c000540241e115070b410b440f81c003866034000e541011034038408525100d02000e50025032400048140d0b0f0161000e103000341c580c1007a01620b004e0b800c81c40051894202000d0b0b40c3c015941c1c0741c81014011107042400603696900030401d002003109803c00305c03010181102c000400640081c0a03031101d4403803400403001c03e940181c1e50354040c0c82d401000345040410003041100180840300d8199840e94031400000340820262005060655010205407010341c10402894603000c2e5445015040007828001080801c03100c04940600c118039 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 482312994 1250 482311744 482311747
    0xa050a0c02040605030304060215090a030903060f020405120a03030e0c180c0f07050322060507080a09030c1d01170a0b0712050a051e0103200112020a0302070c150f05 73
    0x1074000b04008203160f40045816201c001804241c2580000346904501503401071064103590312b1900a441d0050701c400240402d034184000c0c8005801508014441e03ca0b5010060910ba64bc00000b4801c0c40310749850211500400c820030281740d070600075090380e01c00c200010402602070501060304103602c500e151042e0b84000e004980480104802c8414201d46400d0440d20303400d9071f05140c1e841c0e5022201008401c0a0490300c4842100543c4842045401c142c44146c00c011072500c45d003886510003905a4100400b030200800020081c40c0b203d4007070588404c520664007449155030700f01e00d00603081100310440000d2490090350000a1240300f20341d10810100302e545900d003041e15082d00300d0000080e02810b2008000344080c150b8040d610980c108440414140503c41803040412000e02005d4042c0820803007405101441d0450426001010702d80703070441d4900c8a2000c400c0740c0203071752000700003500003030340b40c0c02c0c054200182006080d443e110802c0c031921940015002d8403d04401e40103201c070 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 482314244 1250 482312994 482313017
    0xe07260c0c010b0402070606150318081b0a0309090f0e1b0102071d160f020a020915090405010c1e0801051c020315040209160e090a021b0303040c0b0a050a 68
    0x4003908000c801c3c1101800664a41d505460f01c2000f8040900442140a50b00031036000c4680c402c0c0581082c6182e848888042220140c40380e00d01548a244050520000c0003d083e5102e03408204a0681502aa4a146015051030302180a80d0f80050300e0845281c104402e0f02e1150202084944402c540c2102d0781500b00c100c800182d08140e200d922400d5040b40c010f1101d402c2e00803682d0b1151043e010149400000507031042c007034542503031030906640180d110440800060a02901c4180c000e10b100c40ea90400111324000586090700032a0101e4160351655080b0b1b2156820000110b00d4031990000350081820b00c0320010120141481103030711540000700c0c000c2680d442d55924169581d00030b01964480300d8500c0c0e000409a2058a0482c02190248009042e0624501189864004540e10308441c1002001080320140000c1d0403969503aa00b048515808818100c9540c035051a020145469182c40e08001c0b0070100203902034140d0240070003030b2005c0980c0c028100e6400c94018100303000f2008 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 482315494 1250 482314244 482314267
    0xf06180510050303040f05180126031917010b090d080307050403020406030b041101110312061f110c0103050c031807030c080313080111121f0e07260c 66
    0x8a40d02854150100007400700e824001b4650007003d03644242e40c0103981840240745240c100909100c1d440200c40c412a10390261442e03035980e80d21070b844840440b424600c505074080b050640d152480b03804901064402c038682400503042d40e0051440d064070314117080030040819071220104800501c4088004005600c49002d402550003070354001d0403c0090b16180d1801c0701c000001510291003000e1010300f5140690b2181101142d9102004007039405c00c9804000f96890880150080b503001e9484c6034441c121001c1c803200040b01000c02d81c2c60300e00d00304031300c144d003400e2a28404d9414101400c0c001000748204a01d42103a810031207115001c0c410382d0404d220ba50030f000c100d40005102d05408900000c1d00c204c0040501840000408007900c081c0e030b2420756034203c0b980d04d0090103d007101804071740403244810028942c0031a85010040352615000d40703000b94031082d80c10080b05a82ea09050009643c1d000c01011040c10310007201d9000c44c480403144000000000b4a00154100f00050303469025 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 482316744 1250 482315494 482315521
    0xf0408130810020711040b0307090c02030928120320190302011d031c021308030a050a260c0306041401080c120a11010c0602070b04060506040f061805 66
    0xd01d004416120400089a2060043d600c01c0700151040590710000204502c0d04c0c0c402c05940075402002413088600c0d000c410406401c03078070807a5080d8041841030382c40c1c1f0388821805078840c0d004441e083c8103980d45031099220605144d08019000030082c4090000241c2250f4131031100051902d00010340384c1081d02c2c003803401802c0c120000100780c10481100c10903805404c06850101540b511103013207110248030030b41d280104091038909071001c002c100b0744803056500a02c202e44055070361480c050f459405180c0741d58082500500041c4000071283c201e6a4405a4205148054910812100300314182c1d101e01500140c069075044a002001c54581da803940d0005000328101169080b5035a510319500e03844007181c88a00e40100403204540c4c03400c101c003003259031603260311600710803101080b03100450307101107800c0045900560804c084000b0607828250340d8400c1d0311800f80441c443c07034540107202c252100006110441d074100741092002d801c08070282109404458800070711a81c0b1440c4a0003003 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 482317994 1250 482316744 482316749
    0xd05040e0c0c0313030b0112050304170f030406080615190305060613030c0e1e010b0d330503071a030a1518060807050603070f02010b03250902030f040813 68
    0x80e1100040984c5074900d8010b895045038081d0580034416070703842d10b031803c25950808000f081074000704004e1050700100c0d11a007088500d224211818501011056490355000360040e030302080c205420046146021480741e94140d102410031400c2040f10a0100308219540100c0c105058445000541780e49806003611003030f2901d110303030059550b542c1c100200015068010032005440000001d0444e02c5094503e40d4010f6125502d40810381c0303044c0e01d00c0c006401c0f00810032030258580510b4040c801c0c0002d03484103070151a05407003040d0450386072000400345031648002c4c0a608510800c010f2022900c0b0080510f5503c140c402c3d940f03940700b8854000802c0801d0110150748010480415001900118000d82184411081003100d0304c990710995101018401d1983c8000104000786015100701c610705000318042c000882d0f42004e003000a4200207811241643c140c840401603a100142070039000001c142140085145041c1321f40b074080e4120004001810403c40007071010207001518076240700 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 482319244 1250 482317994 482318017
    0x7020a0602030a0606080c09061911120405120d080105010e01140c0703031d091b0c07060518120c0418052e0b01020606090a0b0405010902070b07020d05040e0c 70
    0x60b20b1401e03507881402800540a2680001c040d000040c401c0c800510849a440500030b1140c0d00b00128084501404141e6032005001c01030046d0a16007240340c20400b20700e07200c40603c41c0640711030500e003d02c010030295105003a0f071031348440d031035162080d008249141550028070b00f03100c400391008010b03030f0b04030780f103141c0058540c0c1c001821200c0c4c49000f04003001924401e80c0d0b0f4a401c201c004141031030308629404e255600110aa02068541c0040804907501004c07242c80c1c241040301c00b10340c0a0900f4403e0340601301044000400d440301c1c00c03d078200c894080c0f2048500344101488001120340e50038540f20b640c0e015980c0e909003848520506021211050340c4181168007100381d480001103201c552640040c0c4007000042003a004000310700980e07502030300681c000c108036a02c0c581000308880c0700cc0d0404640959501c0032400a4499014190181602040151343c1d8000307803500c00c1054200810010841d003203211030a10311541b1904a8003140c1e00b10705452001d443d492285819407203118503050 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 482320494 1250 482319244 482319247
    0x30509010b03120d050601210207060e0a0b06090a0e031905090a06030f0b0901030b04030c02240c060a11031306020d090609120539160312020c10050307020a0602 71
    0x245403c100314024410b90f400424107110300c1c1c4600c0010b5403070342804829003001071061810305180003030960107044441e00941010480d0b06110610380c0c00d110b003a241c1614048050740400c03100e030420702130340d41d00500c03801d4003004151945500780e5100d018000e400b19002c2d12030360207014030030322400a55403940c1c4002c1c1501e600554800001e00103007000c0e80b601c04094102850b441c140d2030019000780c100c83d04103004201030350b20740ea000c07a0380800100080303a000400d0302d00c1c030510035050820881200410310700d45a48600d0100c0c65032920700c00520110429080501d04030f0041c0551054035040743c40c854030182c0b0081c0500d800d002a00a02c1d0300a1149490034800d4030921000d904001c5049000f10480031064080c1d0380215014851088803150582014038041d40201c8a410142c0041c14080703820040c00d100006050704004d9800144440200d200070180144800310b03080c0010700c60680020200082c0f0f840204d1020952a690b6100348000800000c0b001c50091005692040d4028801c5 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 482321744 1250 482320494 482320513
    0x10110904051e01050f0a0b1b03160201080a060602071505040801050a050402040b0103060e060d02121203250f21050a1505040504080d36140c010906030509010b03 71
    0x31001c0c1990002860708402c81c00000a0701e04117500c01e4510108003a00c18524a800d0982c00103450703111040a0b80303c1d1002600021050206001034a034042c002459a409103506000041c002440600818000d61410030100000d41d00010001c0c225000602050842100c0b00b0043d200c5000e258405d00d159400c190810603442800d40c00700348202d208880070040d04480c280118110343c928000c4034008000b000c04038080b0300d440c903814032050b44020710b0282807046003185d442c1403481044030200801c501005120341140c10f070740c25984c44640003521001c544d000301401071203074000b26011414840d5610601c90110301d01100b44481c91070240d01488207040c054048001000080c41c40002e0305035042c004241032425000312809a50044460b03810515055034020040c00c01c0b1641c008800140c0d071410140e01d407403d0b03481c0100c81d0346405403010091242084c040c94003140103805500d4009c040074003120ba1f0013490410aa82041c42d0015141e03440c600f01c00c0c018003103008040c3e4503100700d2521 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 482322994 1250 482321744 482321761
    0x70314210414031203250807080f06030a1a010603140c040501080c0c0a150c050a0c080c030913051009050112030c061e0e070e0c120c04030204060803030402041a031011090405 77
    0xa500180c2c1b004040351120761010700c0c215440402954640001103100010503c40b003040c90510750040c07001000d8031001d05042d5240380030001c0e40261b9820301070300107004021180d0503110300c0c600044842105180c910301900300c0303840c6100300e0081a0603c041100420300040540080e259080c04410031540100d9407800c02100c42030014603040c1e00c45040c11079140311144101e00341c0310010b4194a82d0708071199560f9032500390750066403c200c4184020700201c0c3d807550b9040844100c0d00b000756800209414403000a0708400c810703030482000390b81820700400100a4280503a03054039094a0040030354491450100003514101910040000701d030b504003c400203496000c00308420408045550103076807610440740460088a82140030041409400304013104805419070104861820f035252503180d90000d0b007164425081119a80c0c0080704010850900c0c3c42400181103550100750101c01181000941d6201a61110030301c29031a00300c4144941c40b1017040d140310301030041040c44203282c01d820 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 482324244 1250 482322994 482323021
    0x70f0209010e04120e0f06030a15060507110d03050f0d090b09030a03060e01030512071b1706070212180117130506070801030c09050711070314210414031203 69
    0x341501d1303260550f40c0c000f211900035540c6950041c000760820042003a00300c1000034507000189017007951502c40200b03845603003103415400058107040d12020307110381072424102c01900041804900074203a041803007012136005825110742c8200c1c400c40d0707a40c0700380c4107064101500d90200300904004554081c8101d914012003d0862440241d0b010480c01e62784140011031041c003840054802d40284002c0a454681c41009105060090311615100c06080d8205500300000e42d0125080e02404c3d0005240d8050612040750006107e20003421669007107049a581441140110780050394800300c41e9401da400b4001581c040d50315503d06505a1800741e00840410300b07490b070100c40d1409501d001504080c09004142e069942111100f41800e0800c0841c600904000e00b40e0700910001d180d03142240c09040144c400590321440e000307504492644130040c0390808281022100254000060174540c02c524299000c54401c0030b00d80030000226804a42000403948401c5000d0400000f00b01d000c000240303 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 482325494 1250 482324244 482324251
    0xf08011a1b060a0e011109010302071a040803040c0801020a0905100c0b04080702030606010207060c020402030601110a0f0c0f1a03100b040b0a090b03040308060d110301140a0b061608070f0209010e 86
    0x103418812590a107044031700700ca80c40441001510340074004245654442e501800342c0e10310440700000403400500d02a07450fa14200e90480b4020310000400041010340400100104005002507060008901020704500c11314050903004101c20700e0400281e80c40750400301c44654002b5141c2c5054202800c104085901010040e4085e11074040464080d5100080c800200d402c55039520401030315981c2004040d5001a0041c1d041010b100c0d5400d050080502c2400d850310303c5140b40402c0c03000c09241000e03c445040e84000c40015940c0c0c2e0030007081101070001c581d01c10743c0068241e925a40e0a24040c4c0030240c6410440c00c408000c200883c052806a008044010254545600460ba00ea18900e441d2004980003000580120301050306424404101d800d20b510031740305108900840d4010a0848042c8a0850311580118061140c01c0d4110f00c9130300300c0e24070b0684000303281a03c501c03c04002c00401400040451000282030b1040c8005501545c82c01d6500400b0001203503552031220307a2640081e03 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 482326744 1250 482325494 482325511
    0x260a0e0a050f0108070e061201060f0305091605121207150b040b010918272a0608252109021011030d0207030f0f0f08011a1b06 56
    0x540101d020300c0d11072181080301d081651400040d80e0b4074001115a106c5102e8038640166040c0300390a0303817041c20007400d4060002e50340c5018000c03212400c0103040da140070304034850755080039290544007500e0080c158256002651640c400ba01411322031441d00b440032603845c0c4212004a07014081142c10501c100000c040c003038081c040d10911404010032a110f8800450204a8161703080046504104004200e2181c08000043e068080e078160402540091030401c000c2c031000b40110308120500c00780c1c0812403420408030290b240d24074888528202d2500501052281c0000011040c2054010340c28402041852000884642030b00c040c00e2b4117080c1d400c03030340d0100c0701982c890220480c0f845001c101300e40080c410020401c02c1d40068442d01001562150031b80000c00c001c4902040c9030009012461181d51000c031184203845005012070059084181040800042201ca940e0700c081014191014000d00398011000c0000c281501e10901290880000300707244180b82510001c40d03250311a90702e1 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 482327994 1250 482326744 482326759
    0x1e03120e0a06110a020f0d020d03120c0503041e05070803040b040e060f1e0112020c0706032901031104090f0507080705040302060403120311030a050103020102160e04260a0e 76
    0x41c0d500942d03406100c0f00c070906242d80840c03034810152030803500c50071901402a100c500324200c01d8000c118a241c0a181c00d501040c4116150300c40c20f000c41c45200f45100a52410500b1400c0650b50810304aa1000344030384400904900001444024004540180382a40c00c83e075440380e4490080b00e0300e0300a403107880016100e641c001040b5092804c000300207904010044101c0c0016603401c0506400e084850a0411808070442c213510311441c8014040b40c00d41100070580c1c98a0300b100141a220010344da12404c841c0c25143c824404114480590807036402d0901065118444100b1714550195901004960741002e6141003440850382c0064083c00f00740e696814540c1c0d800100381d800c0c2c400e6100094110400300410404150304c900c0341041c8804501c0e02082080da080441381d02c0e80c105890154009903684010004c5603010005c03e514480b2402410900c03034602000210100c40040019005410300e2452001001c80d50328500101143c1342a4907495100080000b05503085a101003801001c1 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 482329244 1250 482327994 482327999
    0xa022a0609010b0a081c050405030a1505060f060403060b06070b130210050f0a0302030c07060914100b0a060804030e0a121a010b041203110601090b1c0206041e03120e0a 74
    0x10903c03880810f40c0c85c881d005042d0145840801c00c09081440411000c220083c04007107003568043c0700b8502d1007802200104128100130450700222040a02010301c106107040014a450f120038058604aa0f045100007400c005e882020480e54801c2120040003200f40c3e0040104261144c04150700b0240241c5074003a1b10701100c041500d4a10440031005a0084140a04103410384207800440d40807080704481400c10b10309a42d4a020748880f1441100d41c90f81e102d030200c091440c10803003001809a614014080030182c0e402003130724800e00780610420880100c3c0050141402503071202995640940041002543d400d5080c6d0300c00d00b110b00c211807010050041818402d00070040c98140d0b00d03d198520301c0c051400f401c015441d446001d048080c450042c100a14400c014480359000f4405030b08040360a0b01c217101080b003510014554080e0001c0207410040140e00c03400f041d141500c05e4060b03690882110300c840c0511401440d03200401c0e0010140041041c0c41d48a00760341558003095458401083c3c = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 482330494 1250 482329244 482329249
    0x60b010e030325020607141612080f090d23150a0e0a0c060825120b13050a0c02010e190809010c060f060513090b0a022a0609010b 57
    0x1030020030481d8994000c1c02520320007081003100d219686040b01d240000d8010941c00f01e0781c1074018000603120280e00402c2480201343c180000b9020360100150424a50b040104001000c080002e0240442c9000320b9a0111083c0503000c80e0301c4007200034841819400705141461300244503101191015a000880c103c2c000c1001407030b0002c42100f550314428a6440c500300724010700714513150090328441d9074a100007140c50420328901401c01c43e59100c245203040039a0b075042d820965660b8100746110301c1c4001a0642c050801c0b0010103c1d08000303c2c0380d08001e80014802e80c00c140344034403164a084180030000007203900c1281c2d00d090390f800a0143d140070011301ca44501150610100306e1060001001c001401d4070005d11694405040820070f00a0540b80c00d402c444584010160081c1d54003c14881840d00800320403402c03004603030a118000d0f03181d85080030550090000c031401c0390041142c410407240b54401c84884c8280f03964516210384440151a43c510064480700025407074a0000c11590 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 482331744 1250 482330494 482330507
    0x6060201020a0815011e05030604060b030702150703020f0c010515040b1003050903070b13140706050904020f0f070507180203010e010b090a09150305070b1216020721060b01 76
    0xc0d500c03522031124a030b0b640140404503100034081c485c10404588912040303140f0704d00c106910440d81e41d80e0152240381c9981400222482e6800040780041c09000b01f04007980e00046e103102e000d44884050792181c5030b20f20107070040c0c011044004540c207000f290082030b4030415484944541010001e01c803a03030f0554018002158410b098041d04684c1c0c4c40001c1400d179002e0707000307680c010f41100100c03454850a5101d10398103050a42d102d49690031041c9504040c8207410304103121851058014021591070804040c08600c03e405003140640e4001c43d1100f1011000300549641110750303d03180380c0c1d03501589821601c6d20454083c409002581150a095103100362095074142c8002800c041503076400c08141c0866508407114480d84440348000c0400c180c6030b04c1c0103a40882c2a0844114138030b60a41c80e1007030900fa1a6003022203940c8041c0041000a00074005240e046603201d40969075291703107400d049040003110741154031310315800303030102c0c20a43c4030300112400701c0e0080000f0001590300c0c00044450 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 482332994 1250 482331744 482331757
    0x3190c2d03030b0a1514090a03080315120618070f08010204051207050f012a03030606030b0f0d081308120403021215040303020c0102042102100f0f032c100606020102 73
    0xc600c0f45c54440307507118000c0c0f10000004030b410201a061401c240d00040140600d03800c200c4d014003000c002d2140080c0500607003400c40c90110369503983c00e00d00c030501b2990303880001c208200c0906810700300a0000ea050201102620302281484041d0f40c68100b450b01075401803040c80e0080b076024440581d1003601107200802c1e2000280b40040300726440d8011038210390340071000704440c00342038004000c543e1400c10380003405100703444c0410581d20b45074010303017180c803411078450050480d0400c8800c281da55887c00316082c0d520003a00c075101c0c4940c0055002d26031154120b4906403103842c000d01c0c00200c011003c0c10440b4401c072160040c4010f1012000c1d200c8446412511440341080080b50019005c0d40245c404443c00c80001400c26a0780e00c46d8030540c10400c0750786250300816a0709001541402c00050081081a0403d00400841d0b540d0060068110800000800d913440e41e11003011050070a8446801c01007108072440e0f41e01a440e016141e02c856101058207500e400c100189050042c001c0d2901e = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 482334244 1250 482332994 482333009
    0x1104140a080619020f071b0603020f04030b04051906320a0e03160b01050913080f03130f0305120f101206061a0304050f03190c2d03030b0a 61
    0xc0d16401455600c003102048103d4034941c080c80710b015051962005841c070305010b04003010340d40550705d0f0b460600301d182e5008201010f00401c031003c4420350f4a02198112584071402814179a02d90a01904003030011020f0008200030014903004e01c24980c0150102d0100700412191040c101203481003940c10700e903a100c072800c002d9000a21116010b0740b00c00058410031040c0e81ca0705141c5009002112a003900840d4480d98080052100703007032040090382d1082541c00180c3d94540c0c0e503120980380c0e0148001c041070390b00c0c000000800c00c108080c2d0303030400c0d141d100340c40000c5025035190140144c2c001c944440d946016a00000312003205041790309001e441e0050702c4519a5040c0142001080c04076030080da06241c07944000107d11444050249452150088440d03c03820f103481c0030b601f040b0600d441d8285c82c0c0d1090000316100c08502300c090800a06609056401054501e025060b520302034080000c00194a070a41e40090000c0c42c1c0134007140d100e41e0301001004803040c10441d12800c42d000340031 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 482335494 1250 482334244 482334253
    0x6050603042d050f07080f01150b030403180b0a02060601021513020d1b051f021203090c03010e161d06010809210a1706090604021c1104140a08 63
    0x2003084026071602419192242c50614400030a0722a1440d081d0885182c44003544482001c0040613814001c1010312130f0254000e0180c0012000c81c43c0c1011014007403048203281c0040810200340c000c5984942c5c048500b40d0151941740d4030f015070f003019000440c1c00c0c8090302800000802d950b01c04600401040310310000d00b0344d0307601c0fa041c0070051004141000c80e001864201004003050015943c0032800c1c24844400d042e0030704001c00e1204046070030009002c000c1074018940c61035034002c21807280488408035100d85a5640180080c43c2c01c0b030707514261341c043d4070300750f0401d004420200d0002c01001e440f80e00c40d41540c0d40c541c81031800030060005a82130350b804c50003003401984200c0c00c09410900c280111206e07060003000c0482c9103014201c0725990848005407468440d500b100c408440400f80f0700c1020410b2511340042038140e14020582c0d886a40e00003030110740000c1292207003640c00b9103e9400c01954021180a03105039005001703018005100854104480c03130011400303400d82e07400f04041c0 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 482336744 1250 482335494 482335523
    0x30114010c0b0c03090c032505150405100c080a090e06060715090813080c040f021c0f0219030207020909010e030f03130b1e0a05010b07030804330605060304 69
    0x10180f900041c1c00c810a0f0700601c480c44103141e8081000546d032083c10190a0490000c405103041c8c3e8514582c0841e00030401c818051005982d044140c2c2c08590041c0c0f000e440740003000d50201c0e1200308100c4c0003810703804045542800c4030f0340601d00900359200d0880040060701c407442004024001e94000070904c2090613031481c0800c105801050000e0b1190300c030542080c410b00141c3c1c50b03440040c0c010380710030360001c0c1526080d45010b010f40c0041c0c0b81108401c5190583d002041c5100e00c0e02540101030740c80e19070703903018600340b02d5504a0b0f000c0004402c0074000700314211001006584800000da12030601c68001c944102018030505003a4078581c1c0046180c1280d806040285030001802080c1c02e4600d241604007049c982203441d44210b80c890031004400d9041000601f82490107041002d25929140042c840c0001440865801d1505414440c0c0150341d14603000c2d000841441c25201e05015001d01c1e024040c2008143e1500d10721070450511000f034a0700d0510241e4042143c01520054003803a51 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 482337994 1250 482336744 482336761
    0x9150c070b0f0705060c120606070b160207090c0905030714031f090501050106050a0323072f011401120c051c02030a14010c08241c0503030114010c0b 66
    0x914000c00554041803e05a054640d203081031021179803884022400200c8051040d405040c080c0c0c0b0003821982c20707003010303610303281c00707200d42c90003095075100140d58604a104907008201340401040e81510610203c4d40490008142400d1071044500274400d1040200316011400c8a100c50410040c000f000030300000d031710b900042c1410b5040000055035030402039020603400c0c0606406480f060720f8082eaa1081c0700c07001030894558840c20003030120810142c614042e81e26002c0d030340000040c600710f42002105045d10226080f03a4150621124035800d0510b01d1a030190083c050724100d20b200203510b41e80e00c10101c5030500140b42700601e850140342c4140098a41031640c1507080d401103884071509242a40881c2c070700020324005407400406c008130300384401c00900600802e11135514000046040030b40c0320a03245410034510301c84c82c05103281042002e454030040765456504103640d0040c1c4104908043e52a6130003030184810580095004c6645540281d00883c0500e030312480008155490000 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 482339244 1250 482337994 482337997
    0x27120a141635030412111206041203291203030c070f151404020913051002030a1b0c1109071209030905041d010b01020606010f180b04030809150c070b 66
    0x42150799002c42d034035030010070a010809803016101c50044018010413908000c0380400c0f4413120070b0300c12403613100780e00340000000c5203007074001d0f41c41f5003882c4843c0301c0c441054026007400602988440110200d1400c40710005a815001c0c02041c1d40020300c002040d400280c40303120407200441c46a00070000031b80080d01c030500c010f840d035001d44442194500c16071004c0c02a52040200e601c0801102002d0006600d42907000c26004500011059000302c002c3d0f951541307a800aa560640065010000072170168164006140020f4800e07041c40d04501c201c0805414507421100031303a40400c42c44140c0c03003542062407480780a004a0f40300d540800c52000900b4005c0d044e2003200700c081005500f40000e00b5100d0b0b01660a60300041921001e0b00519809000e085414000126045500c00c506012103640c0106600300d42a286140404942240c80221220031601d80e000c044c42101c006000418050100050070300c003070040755401d00011103410141d046024407444404150480030b010001180b8110 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 482340494 1250 482339244 482339309
    0x4050c280201020f0c10240302091b043017030712020a02070509061c021e09040602030103120f021e0115030c0e07030227120a1416 58
    0x1c00545481020000c0c00c0b416000600c1c80141680030034205000c0740340d14002c03401000d16914000c400c55117030143d4024940c8091202034042c00581d0003064600e01d2000d000b1030a50845150941c2e03480d5900740c0c10f1000342d00840103a40b49041c821401c0400440b280c48180078540001d00301510030410040358240c3d501c06020398003440b030b180c0e1040c050030302940003418400c15107801a0045500c0d20040c450590001090644601b200041c40001d0500c1100102401c54041e20a0b45d074004009800202c01030742001ca00f684407144004000421441e50000e40c1038a10800344604414509817041c2d030700148a07041d00025030000c3c5101d00c841021328608d03669017407902e0008500e10141441c46481e40c0501d80003030b83d814210034014007214241d03000c007540042031071034110314200101c0d50700700c8208103081c03000007000d00c001d0050701d03140d84004800d4001e4180700141c030131141c814030309290440001403540f0b0060007a0340c100780d100001d00c0205012100e06108220700c03107600c200300c01204880c0d407 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 482341744 1250 482340494 482340497
    0x10b0a030b0609030106030b0601030c021c03020913111b0109030f120603080f12010506180108100302120a0201030b010e0105250503040e07020705040903020d0c0c090f06030204050c28 81
    0xa0081d0f60055409004841c0118010710003204281407000005062f03d106460a42c15035228440c00402103c2c004d071001c00c10f1119140042e12245241c00058403003a41c0c100400e42c40341000c40d111811100032006010003240e10010306805061003203034034280c401c1e401016012907404502500e94034043e9130b048442441c0700e10700050f516201d41e2441c81c50b4001d500d045464000100c0c0e00e40c1c55000c03045070117014080854110f400c040940c08490b00c040300749211176040000c5200428095a840c20342e800c0555030041501340003c6440b881c0c281d0f1840601c82c281d002904100c2004480d5000e645506400881079462030f1030211400a410030040c0d0681089581c010070100c2c0b1000b00e0024406800a04084005404142001c400091030300c50141c2040f03120b2403805a42c0c60020360006200c0c02c1401090902a0100c030715400d21041001055002c115003904200001e141e001c030300ea1181c1e058034402c0350100115210300007a541a1301540400324801e010034510a5014040b030403590190750680e = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 482342994 1250 482341744 482341747
    0x615120506031f0219030e120703020127020306150f0409020a0b030c040609060203040b1804090227010902030906010302090411040c110f28081e0406090806010b0a030b06 75
    0x101d10190300031900240e560440c950b0301050341c0b52400c01050541d05d801c12585002e2001d5061058030304d44038030300000203545034240004d201c403c05000f07400a103a10385003041c2640d020b080c01c1c07208802500c01c03004e08a11a00070304c00040e05910441000d04c05041700031b803003082103440038010302004005041d401da078812415000091090b40000055101e503510079456a2114500200908005d0740c6821110a6400a000a01405114070103940c0050050082c0440070f13074512000c03800611090002940043d0602001003000c44200c22004401c41f08402404c42c0741e81c0e82e02c00c41c0c201c0c04203482c0b07228281c02481c010005071801c1150590440d0045210248c901c070000005400c031101980b02d100422410b0603041040f960521070740d43c458210002500381c0300803a0501c0400d0110115644e8284da40845001d0107015892099410b9020101c0c1b9848040e000403d4100440d00030344a0703000005c40e030203804960000042405412140d6203644942084001c2505074060b061064600307800000 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 482344244 1250 482342994 482343013
    0x2009250f020114040807171606050a14070503070e0108090c040e1216020f04230c0403060207080c0c030304080a0b060d0b0a050f070c020d020d05151009061512050603 73
    0x20403d445400b440c419186250754481c03502d0601d110350030b40f1400b0224400e040c44980b11061004440b16038403980040300040990700d010a6100030f0103030307030b40e41041059950f0400026036040401035028046a4640e0050b1100c400011a0109402c03180c2114982200c0b40c4e1100034201030f004440e00c000c0c0c030b00580390090180341d0103484a41190400300342c8801010001c405608140045000300d840c242c500b88080080000c90b01410b0f40961030100328a0413820019080502c0e401c02d07a4051940460300350b40d62103540c28104100d400050a405141c0a0f00e04850403601d8000304440c1101e085001405a0700350340d44500d04440f00007010180c102039000e0f0114001340c1140c180c60701c00c031a14840020181840010280c440070010200390034040c14082040c05a911008088d94407581240d0100da0540c1919249081040c4006a0040800040c081c0036020351f003180345105a50164400300203442d91201d01c00316a2085400c0d51001c10584e00782c1710400c1049070131a40d40060042d0403501840c4 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 482345494 1250 482344244 482344271
    0x90915030d054501050c0a0804090e0c010909020f04030c1d06040b0609130216050a03080f010e01060c020d0803070203180f1c030201092009250f0201 66
    0x40c0010300941c00100006101e0321031190300c0710307501803918070101110454100351292a103c1c1510880700855140200c2814090341c5c41042285d01e070712000340a0700c1305485140780c00026038010b405244040b230308082800000a10008001ca2103910503520020654503100402c4000d5001e0842c89500c92010880400410381d51880c003401400d40c03070000e0a10440203510101240d038003030310300c500c9642482c05805840e941c080680d10000011510640c0800014414000a1190700c1808141c1001e000c1100305010b404941c07030b04c103076010780c1f100c1046596901400300100c0c0c00b4003030b46101040030320051180c1442245030030003080c03000d004005003003c41e0f180d0b0071064004880140040c6d10006481e481c11417032400c02000c0f243c0c141c0d81d108602c04400001082c0d1450075507601c0032000810404014903100350070003105683c1200784000c002c0603140951000035542c01106c4c0c000e03e0388038042142a108880100d150007041080b281032402042021074941c0043c6020004640d01c500c078148010 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 482346744 1250 482345494 482345503
    0x1805060304030507110a0506040603020c19080a09080109020a03060c0c05010e03030a0c0302090a060c0206040905011401030c0219110a0e010b0307020c12121c0903031d0d020309091503 81
    0x50303020f9214240c4540081c43d01c840040d0703070313030800e81d000b41281d107410030581d100c04081d201900e806040150311800c4510354030b49440c07000a240450901b04c241303924103000c143ea0041440500e55a80c004005072240d044600b81c03909103000a4018041c55000c0021500a50045d00b4400d01854440c14801d51900c1c1c4901792004810941c2840e0000414859003026621803031405500c181001d40c1440e5070365000402c80390442c0310b039109010b500c4d100c00c421036443e5001c5a000d41a150010071240d610341101d601c564401d120003030302091074100d80010241c00000c400c800400340c9402d515121046548103400d8030240e42119421986c0701c0404908001c030782d10030901820404850f1600c9141140c4020b00e0440b91044c2c0314000d40c40c0b4244204d4005011803403980c00f0715649212951642c800c6032910443c1e0409c040d20100c20303d4a1050f404142d8141c1010900b200081e1040c0106405083c1441d1103002c14018a400740c0d2003001040d2541c248801c600d90f00000304500715020520540119013030 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 482347994 1250 482346744 482346751
    0x9010e100e0307080a0209040b090102043c0b090f130f0902180910020c0c04020403050c040b0405070c06051015020601081c0906030218042d02160318050603 69
    0x101d98030316600c45050600300803210040224000030203070301c12940c02164081001030405015410b02170000b400181094040301c0081c11b207000c940007005440707001c1d800c80c000401c46400c0006c0404081920846c1c231a401801a103030007005491420300060304200d404182210607035004002408105100c2d0321a1041008186c910400440c0d40b00c602e2040005c010680f00114601c401d041c17041c06000e40c0300140c008011004000016a1191804851803505907481301c61503200e80001004410480045190500d4250035142844541101c0040100f81c80c2c04440c4580001c0004e40c000010903419003280d078201e040840c2900049407600c42c0625603070003141d800805a0300c22001040321840400003140ca090300000100403e0f41c076050020905062803103460101500031903240094011803841c2040c00c0d10040c01044401a59541c503d03050002c1c0b500210400348010000c5810001c9008a807011940344503041c038007580640d019205114862480322250100c1c0c1004181915102d005502 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 482349244 1250 482347994 482347997
    0x130b1602060f0912010e03030105010807110d0e090a1a01200102040e0106080a0207120c051c030606020c030703080306210d05180301150504020307030b0901090b040c02120f09010e10 80
    0x3911030f084020b010002000d00420313041a0301d449281c02030f0340404802d0300d0642d542441c041a098907203060464080001a80e4800d09006216024800c03036000329a440161109030b40100090762110620000c440e12008160002c000541900c90b0944c4654100b10080004c819842c01c1103202104190880c0c00640106413100084c00040c03144c184c001030165030107001c0010a6140c0301e0142d031030704c80c19007006810000780a00d4085c40070410900303200d0400c5032070070684020f55000001c0e40040142c611841250007500614003104a641008140103050780d400c42c0b1840d103135481d04020b02c207021040400c0c518900c0c0da42445850250001c0c171080803a4499660303000d03101d0f41d908036000e81d51507240312100e201c1da15101d44003121100f00c40d0355000311801100c1c01a266070316804142e01030b0003c3c0c140c041c3d00044c1e600000c40c1c054090b5100100c1d981054030100310050850b401030f82c0c0d507070548840b01d110b4002031103d81c090200e4070006024010042c0752a012121076100419035801d0310100100 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 482350494 1250 482349244 482349247
    0xc0305060604050f091005060d0f110108060d030212030a02040f060f2a110102070807080f10050108030304080d0f020d0e0f1903080a0908031806070302130b1602060f 73
    0x2092820f401038a400c03224007019000d803410010b070302030303a01c1102494a1051540300d02c001642651001409004039400c1b03024841440e4003071070080542a941c104a50109043d20302081542c01c000a4903854550f05400810101f203140d00c8a0b03180e904000c1c06030b8030f02e98080101042c44514541c10310700510840d140c01420b02040ca0019180080d414100030b0158a40d0203003122908082c10304010594001000084038260f0800407170070175046403c0130205c0c0c4104403000810305000903003462001103182c191105c1d5000c054103101510801e01c0b803103015030300500c0460080760400005105460b107124000a2030411848010700362381013000000101940d80c0c000d41100710741400354400038241c00014001140042c000f0448000190304054100040741002030311140f4a5401111080d41203901c0c29103900d07040031218a203140640c40c00c44240240c101141c191030282c0241c9a60a14090034115030900f041c071041d2064201000201413040107110381c002584554001b400c2000740e404416 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 482351744 1250 482350494 482350501
    0x4030804080706140703080402010314070905030606030d0e01050f271008220c050a12030f0905130e0309040626060c040506090a08030c03040e070f090b160c030506 72
    0x440c1050243d900030000e02100c1c0020010390a00181100c400079071604080700a034807503000480c020f201a0466030041d003898020f010031150815010400c0b94000c4003210400e50b0380780c2c20315803100708032108200816580c0300140c8480d8001e001a0220500010005062042601d44410010405a280141c2c0390300511041640e0902c1861070a004180d4201b20580c0d090905064442d9400d0070405214003900c1d1240345c0811801d0340c000802004000d150380015038484050851150707110008401080e807008001c4445800707803581404844d001007941c42e00310004c3c901c64000c3c24440694514500042204207803e41d61b61103044040e00e659580c60b8048989076000702843e20b1003141d04009544468108042e0070002c41c119400e5400507504c55072510010300c0400d5070f42030184c0000c42280000320f40c0351800007002000e44100c034003402c0088070a888080c0252080340b4030100c03075400103e4480042c000408218003c00e0701c0a061030802c0c0d40f00302d9540300e1039044402504200c1c1d20f41c0166061 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 482352994 1250 482351744 482351759
    0x50d03170708160c0b01140607021906091205150c0903010c1215180e0a0209010b12070302040b03041412120109050a0506031b030705090c211e100b04030804 69
    0x140103c3c41042d04104a210440c1c0d01e4040c0070403070510075288400310414020585885040070741d860b85c1e90180c500022003600c0c0c4d2050300c4540072400ba0303000154981400040d0110072299078001d45401001910f0651000b540d5541c1f0010300801031100030320100721040140e01c007482855a0f241090341d88000c41c00707a075025003040e9001c0b100d440d102101c0014041c0040f2802818408020288510000d103501400003960300f00f0180240195001c001c2100004544510328002d184c000000c0d0f84c0007160342d44001041e81207001d180100103e0340d0b8284005000640c3e082802d540480035203085590030a03001d100851280d10403407a040d41a030750100100044801350107030b05d4010305080d2050180b85402c0021946d542c40c0030100d07014017041043c682c9126102441807001400f0f0280a0320a28502140b400c60194004030b910107805c03013034082603015140b0481003580a00301185d840c1c04010358048880c083e001c0041d110071451329400d4400622015081d0080000354031030f451441d03c8a24000e03c = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 482354244 1250 482352994 482353021
    0xf061d0303061807090509060d0611071e1709031507031a0406060e1504090515010e03010b15090402041701051014010203030a020a020a020d0c0f0b0c07050d03170708 73
    0x800a4030f010988050158032900001c0f29816150706071070f02c1006a4a2030002103405000d00009405180780c00e01040101070078030000e044040c000e20851100407603111800c490303c0300d0f0010103131103410714440c00800340b260034005110108004013100c29100c1081ca0a8550440a48440003c00d545688090b000c145200a40c800f90380f00f142c0400c0480c0c40c0c104040c294508010074240302e0100484144464545038060303801034900702c90704110b1031821040c1100c6c4ca41500818030b000c50329026065060745414000c4000c05600034007a541030030558180c1581c00e810489425620640900003c20782c80c0103140d00700d05220b10b003800401c03e41002c01a0b00400b08958100b07038040200b6940303000c2542d800004603500003007030076001a5a1901000c04171300302401c0344402540007800205043c24030007050203000030b840305190421402a55400500300c0f6110303000d20b14525400911082116240012640b140a40281009880e4040d2841d441012843c05c0700d001c40450a16401d00c0701c0003840c0003 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 482355494 1250 482354244 482354269
    0xc0d030509030105240d200307030507030f20030703060c03020f070f1a0714090f1f0906030b1309061424011d040b060f0f0409050603070e040f061d030306 68
    0x940031000c4945544801c4030b0b1060021f040a047c20102c0c4003540c03d51001c204d070030700a58000064505482c2c4901c0d01541d1a110300e54155210f10440d00d8a050506507030b125081e40c05002001070040134511b50300d503006040d03c91481010300d50300380015080240504001c0c8541c0c1e214007600b115184091030005001006060080e5485864000304080c99401c1801040030280068145440d00c020f08001100b0b000714260241d00956244280208406064400c038001402900e81d280d40945821046049452206690b41e0018210040003e071000c658042c1414600420011a03250a01c6551a00381202542d15400c04100d0104016000130b0038072506240c0d20091810308040300d000c520100e29054840841842283c0c0c030b5a803540160340310300807244051854181103441c0c2c44a5408440d40f0b40181c0300d80c0c00420300b0007000502c24500442c251094901c41d0541381c403c4d40f031b9919040d4824100b28412200259203c0c030319007a46e8845150130000a020000550303591074010280310a410410 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 482356744 1250 482355494 482355499
    0x305040b0c0129011b11040606050702030d21051b1315030606090e100806100305010e0303060d080d2901030b0a0e060d060207020628050c0c0d03050903010524 70
    0x8001c2c00c4280c1ea8003483c810140001445110172402c014107000d0304140720601050b80c054601031b00010b0550b0000040c0024038021815220a00d62040d8140d400c500200c014100c030a8401074179a4176065645d2110307801100240148491041e082400c000c10b038000074a5061100c5034440400480c408042041071345281d82c070b414403c0b5440c0050160210f080b0380600b0b4080e00280c8000380001c001004400c00030484ac4046900508045845480c0081640020780e0194285440e085028400004882c02608054024151111076441310b001a404c4041076006040c0c0702c204504081120449410700109082201019050f80c10005001c581c8400c40440c01a10403560802c0407440203185030b41e20030016641070320030131260b25061000340b244081c02036202c0030110340700788000ca100d90001020344a80031005008140000d040d9200d00843c0b580d20700662003002409400e003050620046118843d0406504100e500b20029094400895024120100c2c00101c5222807604400710310039017506 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 482357994 1250 482356744 482356811
    0x10f0f060503010b070813061112030c09120717011b020613023105040b18061f120605100f0305061506090a080a38040305040b0c01 58
    0x4105000d40700d03000504c1030529102c000301d946070074400113408545680c0f056205441c6001d840704c0d40030741071200307200c030b40b415071304c41e100304400da560810f030031030740108920f0001c81c2c189410103081060300b5201d0345c0c0c400300c0e0380144600010f00c40f501803000305042c9140070011941640e5401420151a007500c104021135019406100719203281c1740d40c121441d80c040d074508012103626a05500207914510201c0400110309101049192045d1b1085008c3e80c80b070038180805803580041910540e406284a070040e81000012a0f440c402d50002441c4c03c0e10980032000140d41d48800040e900b00c01003c01b03841040d11042080350341207002110308040c00c8800780c5a000746045444440d03a03807800401700e8141109403100e00c10281d550000740c1d1000c3c2d00c0200940422520741c40380a440381d04401045031414241078046044240201c2040c88801182d211200052469030230141c070044040c10980c1480020030001c107204001e1002081031104c180d0000c20f003141070020f442d8094a440009a842110 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 482359244 1250 482357994 482357999
    0xa15060506070609050106080d02101125150e0a0606050105030c07031107051c051506060f090d06020331081b010204080106330905042a08010f0f 64
    0x1c1d000103481071540c10030400511402d251074014014241078004914602c100700c40c102c11075900090503495110b900d01e0074000e170300001d80f5a500c280205001d18a09040000800c41c5205803458400641401784040c00340c4c521420b0140f00c12520381d80742c400780c140c02008484061041e24000d07400109400c0c45c00515502d898101c0ea0594020200c00038100402104003510b60841006814040d0000825902986ca4081801801d401c0403460881d06030150a400e100300c910b2a604284c815034001c0d010710b240502d01500078007207621003048641c4c070101d05c415880100d0301510185204003800c90090501da2041020026019004048401c046031040501030005800b0f41c143d030281c041a172031900100c02c210b07900e90b0190040d40c202000c25880c056001a5601070b8001c43c41c8140c0d0b000360030702d2401350b2480394058444640441500403070b01c0354804200030b05003603003c60301c550400041044032006214585100303030004180500000d45480060080440c0c800e0f80d0002020b81c9001032100311b1 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 482360494 1250 482359244 482359249
    0xf0403030c0b06100509010f0e030304091b050702030334080d0b0f0d020405041416060e040c0e100509040603050607020f03043005060a2403020a26030c0a150605 71
    0x1b082e04a21810050141e0918110b24001c0940c0341d410f2500609a07504c580d200c5c211040101081e56031179486022102101c82c0c540d000303c00311010f080d009000b941c47e054018104c40c1014079005004c241d4982000c13201185890300c104898601c921400d03550355950450880c000580719a001010f214843c90340546000e9030380c0801c44a4540d0381664046120703501c50810200c10101455110611300400d12403d10f0702080720344401c141d445c2d07a02c94243c00f625030024881221803035000100840c161404c6a80c9519000d8242c4001508a240c5249010010004582918500c2d402201c590388040306000485405000310032080c2c1604000303506203442c00c42d4180201c072400b00e400034501e00101c00840f0354541c296a0700c60254014040310090304098034140010301402010580211001020120280380310440008481e0010910b095590900012030811661400c240c107401107807907030680715030001340050440c0d281210082c140902507414000c0310000554044d4481c2494604148101d0717 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 482361744 1250 482360494 482360497
    0x1005100e13050f1903021b060a120f0f051608040807110310050f04030e041b0302030a06031218050d020604140315090a1406010b1b030f0403030c0b061005 68
    0x540c10315090106554034280a800c22a010904203c5402003003141c04544030607030510f4500c940301b54221814500d01c62481300e071034030700444025800001000900c0b40e0300d00c9101507951200b400c83c2d0004801d071841c04002e044a1602c10301c000d0700d5884004002031001c1048003407800b66150700f82000381c0c0c60a07980d8142e81c0e100d401402040c40417422045038454504100840d0b070900404020441e605020100240c2e602c1d040720214002100c031544080303107081a0041c010212942c440c040101480c1030010b80203500b0007800101d003240e951000001090407201541001c4010746c8030000c18590300e44d1a45801111504141c2c0516a00e942c40b0005881e0300044038100c459060607a0009152000000d003860140e51920b0b048040c09028002d82a0012488050681c4140895410000801415915900244a4408501c03001d200c072595440b440d0010450903000801524a40076048030350303021980103a00194006540480d9410400180080070b6401c110708a9005101508401d03004125 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 482362994 1250 482361744 482361751
    0x120a030809030723010b090a0f0b030f0601090926040f0b04030c140409140f0c0405060a0308030402031e072102151608040b030601020705090714030c09121005100e 72
    0x11208030380e90345542d50000c6d84400c101d03840084c20801c01d41000f0600c50040d007a100c044170389061420041c0c00d490703c1c0000301110400c0404014041907807a2803010f10040c03c05107000c0d00c10424011107010410b034614282607076000d2049000703443c1c0d810403189002000444d04407000003c7c04001c240086051264002c2c2190500d21098014840e02000b10307001d4816100000d0614140c1d0200c480741c89004910300e2800d1503503008490f4003d0f071107010801590015505280c00c80c080410a001090845c0000e550117800502201c65015820700d1000160000450706612a0072034001440750b42421410601d2440d08a0320b00740080e000c980004030715100c841d01d0f000350b08100040e003449001051090960980d00020b200b82c44236030325403244245900840f0b88500500072007401040710715002581c0360107250203a543c0410100b484204e1181c55202a04c4004071001c244404c100341c0d6200c2c2e0381036002c040303010050f00304031142c41075413801d0300c00103001004904039650083c80511244025241d1 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 482364244 1250 482362994 482363033
    0x20d05041e0b070321200309031b0c010207061e080910020a02061902131202040207200a080106051311090607031d01050304021c060b120a0308090307 66
    0x40705140d0a164140c9960715800307082c91907800f144100506801c00c1e10724000c408660341203045c040714404540210350035001e010f11a00c032100f070002c0000700814095070740540c52404917442c0821001c9650415a0080c6c0e030040c440d4009000e000c8075583c1445450010582d03418007240240da050f0024060a25408182d010425200f0024102510800c4425404485442d045580701002c8030025103c03070382140d66045503c0c10400c880340d85d810314800c035000c11220415540d981c03402c1142403803a050401c001660701540034801407000c0342c5610b101e8405000f015112012060f030311401d00c031042501c3e510204581c1d02d0940300f0021078580106000718894020700c0084d00d044c00041c0903616000d2600101e400c20030119501c410143c0200e41c0400041030520b404079000d441500440d81c074132007110001d420003166151406045815100b0942240c0704001c0401e034000c14001041e20054007a480c18080d5110000c0c0009042d04440d8091b0010b090001452400c1c916450748c0c040e44154021564 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 482365494 1250 482364244 482364269
    0x9080a031515030b031b0901030b1504021317071a0a1806050a02150c04170c0405091b190608091f0b04050721050714030405061006020d0504 62
    0x1003240c103200780500c0a0b181104526035007682000008004008402c885070082c89254003880e0501202c12146a400a005110210683c250756030f841502d80040d010014508030040d0003041a951070001d081c8159000f40d00c2c81c085483d041d007842e14090120502c00d410381007500c0c2031060924129011145404400200381d40e17451880048400c101070030b00c00031841030804404601c0c0c40d40715008180c2109182d080b01c4041c9002220325a0302d801c151503401d190501044104890f140c4940a028007040060684c0e4000b014080424152082200c500045800c13000e80704a64a145074900c0c0c80548007900d1004000d2203a902c10f03500029940a1076081c4035800d000280c0301d200800090040d040043d00c014211010300d44400040c00382210340920603424072000036142e9100741914007101c84440c0c140c03e000e80304081450002c0102804d03080c1001620520444509024001580540d11402c000e212902d8107840400404415070042411900131088201c00c10f6409020356044d03403116003441 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 482366744 1250 482365494 482365511
    0x509160e0d0206180a0e0106050405150d0e0a06050907060804060504052a010215091c020c151305030609030d0213031202060708090f0a0609060b0a0b0c0106050409080a03 75
    0x80e16078001910000d6204400154103c403241c00b12010380c01400c0240c1d1981070241d11071258840341c040074040c003c00541c00740010405441c1900002d04500d104103c03a82c80c280544095005642082c2ca480c10b050388005070344810031840380714155001351a10003401e1002d00b0030700300030b00f040005080948925126004078060217000d1006003001d900a030708118490240c0d482114103450380307900050140c002ea00c240c6038040d03510800c00f0b120324042000b8161101014a404508803040b801e00011403050010090942d00c40003c20f01030041070394031040c2c0760307442002c80d0b03520000160030540c003c7e0000c00138002d600d80000305461001c82d03152805070b00d603090902179032811a5141d20140291048245084450707801044003400f030401303580d03a20669912082c03555582c40e2211015541e40e0b110190480200761140d1140008900c540c80105d01d200070b4000060035001e03141c0114078604000900300d046c1400921a20004107400d8a0500c4943e01544500019014418240081c1911100f51 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 482367994 1250 482366744 482366749
    0xd150e0a021e2d0c160806090106060c0f03140406030207020a0909081c09021e041d030a110c030105070e011e1718120c010b01090506032809030203090a0509160e 71
    0x3510303400d031300345002c69900384d8014a4282260b881d0340b090280324020800498054038060107030009580c03454443d48555052980c40314139030030300d240050741080b000da010004c0030102171000704000c0205aa01513210700081c0104010f0001550003940f0040ca0400130a00142c00c10050340c3c420125a40e001401c5a03541a80d8402340c1507180000390302101a001e0004410b4030036245401c0f2480036142005400f40340b00e822030b60341400440e0150240d105000c0320849921408458040c0c0301c01303400340c480341e0f4904030100c0d081d180c0a03900c03400400c0240c44001c600d564410020b000030354030001e002e0700500c004800905084808c1450801c0701003000000b6054040c0c0c074160740901895003080750482002c10080c807501d60007034112001c0e00d508001d1620010742c887d40820040c0c4100030700091850f20b521304401d5000040c00c1c10111040909854020308181307078800d01c04200c2c00794014641e01c00c1e5000030443c825000f42c0002d880382a00034203105400f803110381d1202d2400003a040c0a100741262200 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 482369244 1250 482367994 482367997
    0x141302030f0606210103060207030e030c0a090507180315050906160c0f020d0c0302030708010b1806030c030a050d02100504080909062103041503110d150e0a021e2d 72
    0x152613a941c031070000008216241d8010211603000755500305c4500b960030101512038a40083c119031100d500c4609010201d141d51107030b40c224006003006641c44442074842c0804d1291540165082c410800285640000c81e014440e84403101902415440c500401903a042c2c06050b40340d2010019030701110010030410b140b1118150b5001071100b1988506407801061141090000b24044d0050709000a070b8104e050259081d4407200420303504803100c5480c001c40d012000140003540c148a03440210a02da2400d011400009010f480503084150803980040e1800c912500b4000d0075500d00307801c20020540351001c0c0c03505c0c1d02c8111703005c0700c00f078480a00141e4030300c404032618031070710303041070f4108040303400002c000c1045510300030304220a040f142c0c9065049603001d002c50041a41c04224542c005c1a0071f51022005200f003605550010b515620340c500203440c2100d00941c4541d00041c1603e1030541580000ca8880181020510f4202c000050a441000105120510b404260014480c6411640 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 482370494 1250 482369244 482369287
    0xa050a050c0f031915050f100602120f0f0d240602060105010804060c02070e010b0403060b0a05010c1e050d0e09280e01020c120405100e0306041106090a141302030f0606 74
    0x14403e000e24100001f4014032040c00381c82000c3d01240011001a01b58004280403074100000b8650758242440c5802c0854291700440102084800800c02054120b07036034030800920b06a0010f03204965001840101d00c4070000360050410341d40138800411040e03a202c81c0700b56002e42d0010000c6511001204203910300b00e004d400048800c24800008243d12141c2c001a20440340910001c0c40000741c4a024001560071a0192a0024011840c04004981003140c60113a00311206c4400c40010b180b6294507050a0000c070380388000407660303035900c507451a10b03600103a0007003081034400f20b03152081c040380d9100c0d81c41402c10401694466007540300d5030500b03505803a090214402558a410341e12a0382c4038040d4441d0280d50b00c03501c04569600d4030300d4411000100349a03c003400504c240d8449071944142000a102990f60281c0304020819964890800010003001601907106a009045c0e04001e200499401071105440c03051003040416010120080d40003801514401c1d9a2105e51074050174600c1d401 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 482371744 1250 482370494 482370533
    0x60714090a0e0a06090608070b0901020304090216020f03010b1e0d020607051c051908060604180f20220305030714100c0c1b080a050a050c0f0319 64
    0x8034001845146045143d2050315941d404015240c1c4030029201100e83ca8001c2c22056032040b8030a110054950000700580641401104e0805076202075140c203903400501542c42c042c000748615001c504294030300d40107000d401c4009000c420007000100c0c542000c100c0e5441c404908176038221900340c551552422400c0e0300541b0303042e0f0700c0364541403680d0f49010418040d240118540c0e40b000e069489041503444040e40301c4040d075881c002c003013021900075134098102ea1b40b1500c20071002a40d8100300c0d101c4920465064000300e41000740c90203010880d0345944a090013440400365400c0d00780c852200f181c80c500801f813400c59950030403400343e428002c03030b07508020b09078440001c001051180c00020f01501d00701303401c1100c4a46440b00351540c25a102c0c100143c0208a8a40ca1440026480c15a01c203202404030300c0c801c115540c03060100c0c07501c0c0410700706644a4110344600b2050000500c20300300c00d50402e90b12000e00010803400309603903550300903c10094945410403201086914001c44003140c072034 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 482372994 1250 482371744 482371759
    0x503190606050d0b04050606090705030414070f06110715090b0309010e1621030801060e030c10030906050f010509010e09160e150103060317071401060807051c0506071409 75
    0x142c68404640e207400c2d1411b980c1481407030000781d607620f001c0010074400c807807964070306003151113980e10150346403002c824420242c0030796500441e190040f00c082c40c0052165645c0c0d4042d4581101c02507042c501c540d048000c00c41d654070103d81180d50840c0610303003110a00000c0c02d5603542c034090042c0c018540d203145102c1c00c1c000d0700d24841414104140300d03c00c0d0f417250300c0c2000c2003004210716611034490b0300000a012588401c01009140d008130414403c0303c0700681543c1c080c0780c083d4001502c0340c40f003041d11401b0075a500e40c03034014402548243c079030010708050640d915506000c0010b0780c4400500c039900c0382210080000b92015014006080300d03001d4002505003540e01e444040d0140f61044403c000041c0f95040701e42c103507612034041d007002c40e50080311880c201b441001c1c0d540101c0c4c1c45024291440d9a8100d01d40c01696000d100d03e50040590030043c0010505050810a40a441d0506141e10088200b41140490000309446822400358241150b0700040004840c205020320000d0581c018007 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 482374100 1106 482372994 482373019
    0x20a0b0c0703031416030c02060103052806050c0406143c0d020a110a050d08040c080114012615060102030408160501090b04050319060605 61
    0x38500400c0785120a139040c041d0401c1500d102c07449604c40b05083c6420b0307506100e88002d50030300384050001545192102c59450380380b0700f00d0091203058541d10941000540404000507035009500744080e142c1150300325060b400a20481012800c6000c0b014460f14121082301c1511005c0c0d00c4600a1a03922030400300840f5550440ca000c00c046800060103442030300015020301e4140010142e03880500e00703002043c960030700200b91007a0740803503c1030000843c0860050300070002131500c0c49040d911030905040c0000207074068030a6501c1d05c90212100e14800354854142ca0354001e00401c00c5100013400003030f0020700280808141c00c80002c518031072a58000058102905104076414030344c862004506082045e0040030b41440105420465035030000d41520051006011007410031745000086030b280c228149141c82800010103691003040701c980c1c00080030784009840c101441d074 = true := by decide +kernel

theorem cover : BRFrame.Cov 482194244 482374100 := by
  have h0 := BRFrame.cov_init 482194244
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482194244 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482194244 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482194244 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482194244 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482194244 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482194244 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482194244 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482194244 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482194244 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482194244 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482194244 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482194244 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482194244 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482194244 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482194244 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482194244 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482194244 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482194244 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482194244 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482194244 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482194244 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482194244 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482194244 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482194244 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482194244 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482194244 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482194244 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482194244 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482194244 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482194244 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482194244 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482194244 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482194244 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482194244 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482194244 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482194244 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482194244 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482194244 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482194244 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482194244 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482194244 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482194244 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482194244 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482194244 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482194244 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482194244 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482194244 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482194244 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482194244 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482194244 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482194244 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482194244 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482194244 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482194244 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482194244 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482194244 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482194244 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482194244 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482194244 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482194244 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482194244 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482194244 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482194244 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482194244 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482194244 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482194244 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482194244 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482194244 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482194244 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482194244 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482194244 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482194244 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482194244 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482194244 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482194244 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482194244 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482194244 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482194244 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482194244 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482194244 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482194244 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482194244 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482194244 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482194244 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482194244 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482194244 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482194244 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482194244 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482194244 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482194244 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482194244 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482194244 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482194244 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482194244 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482194244 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482194244 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482194244 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482194244 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482194244 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482194244 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482194244 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482194244 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482194244 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482194244 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482194244 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482194244 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482194244 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482194244 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482194244 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482194244 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482194244 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482194244 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482194244 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482194244 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482194244 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482194244 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482194244 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482194244 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482194244 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482194244 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482194244 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482194244 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482194244 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482194244 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482194244 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482194244 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482194244 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482194244 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482194244 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482194244 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482194244 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482194244 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482194244 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482194244 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482194244 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482194244 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482194244 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482194244 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482194244 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482194244 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482194244 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482194244 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482194244 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482194244 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 482194244 ≤ n) (h2 : n < 482374100) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
