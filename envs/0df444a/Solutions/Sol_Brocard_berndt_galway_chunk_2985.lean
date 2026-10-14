-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2985
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T08:19:37.661218+00:00
-- url     : https://prove2.me/submissions/eea99c62-2686-4af1-8862-37e0ee54d8d6

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 536690647 ≤ n < 536870503 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 536691897 1250 536690647 536690653
    0xa02010e030310121103100504060c0816180510090509010905012303010207051f06140303180a0801021207080c07110f060903031603020606011106130602040b030405010603020f0f0102 81
    0x18410320100c860091032880c171a007250910140c1150010740b90003010080160b401c1c0c5c03604100300401c0300600880d101c16009052031840b500741010301000c624480c1c2c56020810170f00755005008036000e18050070040030f014080e44580f000c80f000040050b16140a802d0042c00800c00000c1c4842407072044a040f00d110700100c0c20140c0b02c0e091044001104084203507419902031162002041c030900c5088180c00301141d509404c8110707001203d042d01d50581c4011841c00d9000c0f40320803e034034040201d41109801030074210f40c004505002441540b29608003208541c80440e440010b0380714100c116005640d40c0d11084e003140c0d50200c152104c3c0c812000001e11031100500800c10300c0c2000300002c02c03821401032045d420007200c000401d2464020402d0746000d03000112040c0c040c15018000c958200000780781c03d0050b4003042001c11790302d01d0090031074444c040440d01d62000340030b0b05a050300c1c05044078084413543c0307003801d01381240608583e000681c441d201d01c0314420304503d0010840d030407219043e005 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 536693147 1250 536691897 536691899
    0xc120f040b070201052b2009040f1806050a11041d0c0d1814010c0c0f080706050a140a15030201030902040902090403170907031a28020a02010e030310 66
    0x11900503000090b049060003420305c60610011000c0340c0c07488980250104803414115144054411b0fa00c6c04454000c0c0d40c207807050f041c01003035410b02c11603c0d402c00544001c502600004500d400600c0a6940301809840104640080200c9900301e1070160012140601034400328500c1c0075172501c110311074900c40784000300394200a2000c080d200e5038410100c0200c2800c1801240c20501a030325000e02c0b40b074864650124820070018028080c030351201800e0002c00480b01d003218080d2101c5040c020161030003001d40c01060030401d141045901c041ea000c0c07018011424800440d00241030100510143c0f214202d001444032a680c2c0f040340695020451420005407858005400405004000343d0b00961200380500250302c1e180b4a15008910a555040d0403d4848450a140c60000b0300140f0032504007240410101c0c00c25030f1192000c0020014080c156181d03100c03044600c21102d0740c000e0bd030b44500e100600000440e613010381801e0000390024420744103010a02c540703030b1104640d588464901010 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 536694397 1250 536693147 536693159
    0xa2a0b0409050a06090518100506090415021903140601171b04050a06081609080d210504060c110f10020c0f0114101d0c03100306060b0c120f04 63
    0xe5070820410a80018615160305d0b030b02d0240c030070455214042d0040c00a55038542c1e0b03410089040102000c0c4c10400103410114005804d902c0040c0000d404a1000420000b290747c2950450340b488020b8002100b80c0b41001c0b4000c2c000d000844a40c945a00c500400101035500440c2000140c1d20510321520142d038540f400c1c074002040002a408000c02d09020116594413032022100280c03c15466512880c03811107100585001e03480100810880781d0301d0100441040091102440f00590410001207460f00078104031f030109100918800d203044c2402d203c2070000c1c81c2e0260130b0b510000e9607002c0d00c014100760225610303144030900c00201e91204a0010713040c3ca41d40c0c060624245820281e0b08881d01c0740c08030500b51200a200340e002e6070b00300c605211004a912040c1e40041a042c40c090078004c0080143c01e10228000300680381c00c040c0003001549101d40f032144400074660040c001c201c516241c000c5030f00990082c4a5091852298266a1180480dc4402d603030210b10203214117072615003000 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 536695647 1250 536694397 536694401
    0x80412050d09080c0303041e03020a020d080f180f0402091f0c200102010b040b060a181d010e070207080d180b040b030a0605040209100810080a2a0b0409 67
    0x74100107075240d5603814000c00070b5075000042c441c120b2038100446d243d00b4a0b080502142136051042035035402030341050000203402240c035004064045584002d010100c2c1000c510078400c2c1c2401c0303410b03950002440345004180302204840041c069640300a400c0038041400201c2c8a9141c4aa6000385600042c08590240d1b1410042441540c5082c8030340d81510782c0d481612280c5000890005c815440b043c0710304d035a0911485216001c215000c0c0310b062441c10204001e803103405002020064000002403540c400c090320b210040c41300c0d0100208a41d6900703498200380e0004e000b02140884007201140c0003031320016540e01540c400710060308086003901c106071880c0281c1c00c01450000c0300e08030002203030a80354005d0001405c15588050703032860403040c01c004a40d03260300310b51710851050041004940b1640b8184c10030021904201c15207468150140400003125400001144521000d40c2c003000001c0b0142070b0f40003241c0e502182c500c0c01c02185410303031a550b40101e2030034140c10b10080200b4000340d = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 536696897 1250 536695647 536695657
    0x91a03071a07021c1a09060712051f090204080c06071a0a09020d0606030b07020708030307030b04110307180e0603060406052a040f0617010909031107060e090708041205 74
    0xb131a03080c3d0720b21a0f2182d101035004401c410307940d00f07898108580483c0c041040302584404030502030b100d24600004007825110b0300f021140d00740c0359039400051080c4a004003024000b00e41110551005030340d500100080d40c40350089400e14000d01c2015042400e0007010750b14a03590284142c0f8544041440c000b40c1a54001c01c6410b005481d01600e40160b01c56411440010f800f400d03003c90a01e0940c20540d0302020060044800c55000041c200180c08001c4140c0c1d800c0f82851401164070a00900001d0140c240b6050b900d21007540002404001900812142e0a0b00031442080700b2560340e07500981d5202d0300031641c07960141c000750000b0f07000565a5000e19809030403010115100e03490702160002007450401907001c030758000141400902d020400d00d600800c10752912414100311140b6800c82900103103c1d030005180c0b901038800c109030190000c003d05101c520200c0708910364035a00100103141d03400015009543c400c0125049901c5003c540d4443d40c4c00c800301c051103141500c030442e0780e84c0c48 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 536698147 1250 536696897 536696899
    0x504050304121b05010206040b15030304030b1005030c011103030403050703090b0a02070503010b0409031409031c05091003090203030702011805030109060f0509060105030d140d06091a03071a0702 86
    0x10070080462810000e065015070305009164030b0b108074080e5101c40541190703d4104605641c0b080040200207801d40c40c03002e80c020007682c90390b038040e0b000c900424030318059908010b1040350080e00700301c2000082c210b5602101c00480031504036213006401950788400000c00000c003500200001070206e130241005040103482490003c840340ea44805440741500420060001a04108420821850240a400d0704880110703004c0082d608140d0740075008500d42c0d0301910740d041c0c0105003070300142e8040c00b802440c07035029240c2e2020f21110030300c001c19640c442503c003845400b21000c200c0549210344180060141e018006601d0207001d82c0040d24030320000030005024a004110100b1103403000c5c050b220503648500c3d0082022804034140600340d0382c0c010300941190b4003505c010000c9541c005415103500c076480c181780d0320013010300c0714800b9a4840d18030703400780c004e080400010b04402503600c04034031400c52513080e44002603108101501c0b8500b0303104166420038414140f44001407410024000184 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 536699397 1250 536698147 536698153
    0x6041106040f060210060b09060909182b02032b0f0f0207060608061b0a05090a0b03010512070b0d0e07050411070b0112170c010e12030709060e0f04050405 68
    0x9511040702d40b2032182c9400050060704100c00391076040d1400d0140e400039040c0121194104100c0304089015030140b001e42c1031240c0884030200701030b12580f40d0703104035084040040d01c005003c2802045d0b00b080c003d0600044071050380b2401924688080183d80c19410a24402141500344800200c0c10002400c940344150f47e440440c00c00c2c00700b1500c1020503524100101507114402d81c145002210070702e51025880c1e80005c2d0801c082c2208129042c2103410381d0781c0b9a2921602503440859903070103100e040b80d80202000030003182e442804006107040b101d08070354a910a480030803542d902c036020781c410100640c009000d54412000103410a0842040d40404c81c2ea52958820000d810741700c0ca03201c06c0340a0100000d480050060724020180980341c424860051a00203554041c0c1003c0045a860510300300031a178090302c94070a40140748518808030444805402d8146a24004e038003d550180105130042e0b4005402e074055204410041c400509a0f580301106000b80030151000500441c0c10b40 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 536700647 1250 536699397 536699399
    0x10513090e0c060405060d02030c0403300c12080702030c01050f0402100f0e060d020702060c060702010b01030905070b0c070e090102090a0e0f061e0d050604020a0501110604110604 79
    0x2150110014000d0020300004108001560703040303401c2000c200403840c0900401c1200340000e0303c0d0305c011200c205007420b07001691707a034400c03078150064019900001c143c0040000095a104070003d14401d154408005400c540300c10312f8816645650006401000c10b20305419642c1c28902401070305e503100c078150054034503040004507150b0071942c080b03c1c00c107040c1c0300b800c0c00e010a40c10a1960000302c0e40c05030a00827801c0c0b502c140c010780340b000d034200014420b190029092504036071540544c0d40d500d0b03010309507585801032002095212181152520300562030010710540940c030a028010207641c2001c040c2103100c1c1070200c00017190380189640c0c130b0a44140140002d55800f405400380c81070030740d4000161030b091440104601644039900041d800c40d4010180a0140e110380c0300070f50460000c94240d80f400340c0c080045541c1c8902c0003d072907480301c140080c2c0e4041c0100801c03075511030742c803c0707401c2c503140703600c502c0103450042c203000702c03d02294407100000c0c000521000059000c0140180300c60300301 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 536701897 1250 536700647 536700667
    0x1050304110d1b0e09070602070305060a0c0e091515031005010e040e06090a060501060509100302090414070c05010f02070f03120b030a080a0f02070b0d1104050406030821040c060e0105 81
    0x64203e59104003000d240010800031505c0d010300036040a00030902c0902040e034655101c1e15504e84010b88660300a5035500702000b03209004900d0310f00680c0000e01a40500d20300b00e150841071042c88041c040c0034680d0311080304100940102201c0c8038000b01219001004d06000044400e01500c1d0503981d0015901d40c81020a540b041050784d2007410f050300240400c0d031940c5060703416100103038042030500034213101c0c1c1880e03030385d40c18001a040f11040c0340050701d03191042c0005000d80034110b0740c840901180018402e91680c003d485032242c60181d0028840c0c040799510100407071041803005403d4040040d200707400688194000102d01140740c401280311180720001900b407200c4104115540500010190165604019a0301d00310700180080c0901a1a004000700148580940d410348240e030741070b08048010041040d24040d00d80500104886500c0b40740c5400954009030350800e011404140740c001c01a500081540300719444500b8001062030000306641541c00c03482158144041444080310b0 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 536703147 1250 536701897 536701943
    0xf092105150412091208030c19030e1b0a140a0305010509060610080f06041508060405070317030705040506030705120403020a0b15061209010207021306090b01050304110d 75
    0x258240614102065041500c0e069400d80a501c0d0010203101003001c2c00c00c00240c802c601c0c080040d80100130940d0301d6551000800d458480c000c04400400c018102c0d07500201c1cad040c1c1c80840840100301c11110411041d605140165036040e501550190300d5a030140200090f071030b18400103076009001803595035181e50382c050a4400c11101001181d000a00304641441c100350031003100c440c01d08000f41d040c00d200000d40c82c2400001c0240f030080f0b40304d880c44841d421040d68120010b0103408103644041c101854040d48074405448107480800003400300100c3d0440707490403240140c03000d40f40d60303240c00d10700400d2003800c0d04020203032020701c18240804040c0d61007014429200703900c00e030b001e44408849031600194102001e400c1c9104840704204860b0983c0b280c408407080365420400c0b448059031089a040e000e8030403024029048102da11520088101542104068818407407043c0207031900000110740304d0101702c0b07018010103c00d100009850a102a90700440c50050a2510082c038002c010601 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 536704397 1250 536703147 536703163
    0x6050303040b0702011e022e0903021f0507270b04060512010801330f06050309060f1504052e0302030106050402070305070b250504080d0f092105 64
    0x102c0d04100251500440da80440c120310b03070a8410511801c4c1e41d4804000940e1052507050580106d0040d8440540c1110b203149500c44c0000f101600b803108c040300d860700a40b500c16210288608211010819068400d14081c0e6807051440e51fa8101c0071a018144405050242c0b070302c0b403c411803424102150383c00e610030050000d000030780c032040d0b51108641304c48000110141e1017205241d2411a0180308002640154408152502900b10481d41e00880b100384040440d48074245c410145400050b0254100000c1c505c40c54854040d40d0040e520701403180d200071004c4680c0d105070800142c1da00418505680318541090903c03401d01c0c0c0b0600099004031342104031010018510007403c03010405c44c54240140d1f8060441075030305505150060354090154000c003071008002c00031000008146c07290071000c06a080301c98031460004c0004009002d03055a01501445400b406010710a061003402854800e0b060071040c3c0e54000f20030300e4420500b8a80c5a0482c010101041e0b030036051020680401c00c0c0c035 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 536705647 1250 536704397 536704409
    0x9191a01090518070b030711030910031d060702061b0d050403050c16030b060d020d05010911010e01050a140a0203090d060c080615090f130218090106090305100902040605030304 78
    0x2003c0c18a900d4091020700c418107044440c0c1d105600c180025003011054a4100c0303207500300702822072140482030303007140550790a0a401248034440d040d031040c0d0640052600c24018030205d40070f5030402c0741e115107641d0111900c102507030140300410160040340c07c1d071150440b102122a8188001c4049606c2aaa000d0780d050b00040c1010035610f55a90301405806020b01100c4045848249503545020306513400030001d034401c2450f50f888000350740700c42c2440382100b41d02c84005c000c015040d14100030328070b140302000d0b8002015000f41c07a100754058001c882c003000d001e4036401d191180c50504408658800100d40301140414003078001561100303030078030081a22030400850070411a000c001c0120034010170541c032a1071825101701c0c824015804440c0d0414040d240c026041180c040031580c198607000e503040c0c50707a100080268048a21420540e14a032007201d14540740c1c0d0381d0300021038041d0103500001d0026081803150000984c0e0650081c61010310190000c6002903446000908541043e4040 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 536706897 1250 536705647 536705651
    0xf1206100602161a0703020106030203030a0302030a0f0c080402310509161a030a11190305060f010e09190204180f09240608010218120609191a0109 65
    0x500000780c041c000c1600d95001c2e49880c00c3d41c0e615111400d00e41800e50241902807080c00138100302854030030741000c0051500602225541c406020703000b0b0007544116810300300d007498495070a080e03000a000700308100040355070352800b9032100d400304903800c0701c41c0000040c03041160310700b06815003810844080c4542c0070f0b04000f58503c2c00202550800d0700c07641b0024030300310114409000034202c882d00c5801030307030090400c562a81d58100a000c010300c2c10200c900304002020484500c19a46c201441b601c1c03104550b030170f100c00d86500d400e012105e07040d002c5290115100c13035004149800c01400d0319520426807119100d10803010100001280d101d038100441d42d0700c007004440c402040c94020300018034101c01c42089000005c0e152512141918111040544500e40c0c001c0700032039958003d500035002d980000c55540248607000c8480f909403418450148521809044c0d0218020640c00c2c4121580006490328480080c40e558404010100486402c003d1624040c04050241c1e46103001c1d0400744c2c40 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 536708147 1250 536706897 536706899
    0x2b06090207060e060402030a0305130f030c06170105091303050904142a0322150f0c03020f0a0516050105090a110d0c17010209040f0617030403080301050f120610 71
    0x2c80002d60740e81072500301c1283d03c02801c0c0001a24001020494103403d4500a0f48070300c0d1407175030212400c1490b8044038003400c00034004001d2151403854075049030b103070f0b48030781d122810031452015030401c0c01d00c03480e907000c2401800694078080c8034241020152082c6401881d01188400003011221440c08615a1041000c00c1061603440041408507a203240c280c06907001d0700c40076000c0340b184401081544402c0b00025400c3c00121803c0c40301610700d40c420400581c0d0a0104a50381c003c12130100500180390038040780780444c4e80a4421100c4251601915a02d050003250042e03d0301d9010101798084446e041c4008800304c4c0081c45003d0082d8904006808044000c1c20142011311003c41214810004ca01001d000540c680114404503541100e1125904c10100d0010b80240100282d6a402c642890601e1000c82500c1c0d100000741c4030406000380100e4140c400070780d43d90040b400010465031082006010701d03e40b8508136100c2103c0144401004c50170044c071030341040310a580d02c0141f0b402280e8 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 536709397 1250 536708147 536708153
    0x503040f0e060f1e181512030f0d06031505040b010f0308160302070b130f0b0c03030f180d020114070905062226060903030912090303040b0301270507052b06090207 72
    0x1000c422186080b2026199021480d011a49030710070407212113109c15002941a800d0811500701c1c000440e08118240c03100d09000100f18064001140e08660b0764840f403001081142101c0c10110940707400040560411030854040f0092014407a410707402c0d07105ea0003000031aa8903090007004150f44c500d507811a0a80303000981000315405803c01000314105024803042c0c040000b00b179a9001c3e0301e4510040550f2540d00070f21110036803e40c25540a030050120040440f50150040981064203440e0303021a980c4241d011640d00413070340120340c0c1c018001c110120b01c061852909448448074202080561070750342e003032241441c5001d68040c203980890900400600d000340162580551000c019519500d030022482c4d032914002e84c06015134050200750b908154804200756070103010300c1e0340015569612040500c24014001c0c036224055001201c4070000e18100d8002c09000d0080c0780c441a08203400d084100e1003075080e100c0d5a18010790b0100350801c0200e118046e01e00280701c000300050740c45200741 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 536710647 1250 536709397 536709421
    0x9030417011103060906150a020a031b050a170c070e0103050d0804020a090c0507050d08061f1d01030905060103030e13151a04030501090503040f0e060f1e18 69
    0xa03141a1a41d00d4810840500c0100342c0c00c4a0b4803d00440300202c143ea2050002008186521815064090f0114000712410340000320f102910780261075110820a1011542040000e10f0788010301c5500031400c4240000c0484805155425010500c10306007000c1c0c58046240207410f50080a0b03820303c140040040c003205001006880c8003500e0210305510b07060300440c29801680c419140382c2b90380c078400c40380d026101c0c0b4156a0305a5002080e220380d0030141c20010f01c58031080eaa403030b102d0302007044d000c000c8100001320801011842c2d182c034041d400d041100030540e881c1800300e0606050710b4200140001704203002c494041e6120b511828a0700ca00e00040c42515403a603092040c0c02450600c0300b05009554502c110300b201c0051222191301c0c0c00c41601a0118010b03640001c04a40c2022803460800c20003002030000d40f050482244116aa40e841032105007005031019070304044c80c4005040c171801c0031003440390240c1c20304010004107000304011425200800307003480b030000c00100520030850840 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 536711897 1250 536710647 536710679
    0x5010e0402030c010e01020703170c07060f020c041a1207080115030b06060711030a06020c010b0a03030e0f060f120105030c0103060614071a09030706151a030c0d0203090304 76
    0x108040085480c05030301082e65a040304101c1810b1045415505030107a100b08400d40c0a50f60103a5821100d480d4144400c0060300605c840803510f024040010809901c2180100281c940710f030b00034503521082409100041840070600c0c588002034120758099921841000d00c50801201d00908140c1d29010456085802403081c071050201d00e24401c0020031341d522901030708401d048030035a950305018a0510141284d1001440d01405050007840038019150301610200e1913501c001c0c043d0a100c042088407076696400001d0104070210211201410240310501949801900c1c00c0d1034120045402041038200d03130f902c4141b1304803920061005040a01040503240420b0800b84000390030660064030028445a4485404e00007091000c14002d4031280c61030001072941c0381c00200c1c2001400030744c681d8010842540d8890800001c0c801d0f0880c0040c4180848a001160604003003504042c000340c1d51003c0c00890009209001ca1001c0803620310007107002d010341c903000f50b40d030f01d2400185440203121 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 536713147 1250 536711897 536711909
    0x40905030309150714180411030708061807111515130203010b03010b0a0c0b0a02071a09030d1802090702160e0105100c150c03020405040e0708030d0213030b070f030501 74
    0xd070060182003a0007121001d175250b0324208042d1184026144052035491880c880b03580142001d51451548480e132000b180503900c60356a2128565614052000109035890906046118200050355551048004000550450b800d03a018400c000c0300401c0d83c03000070f880c1042c0a42e80700429090a05d07107580007401c1002021002d42c250762404403550301034001446298912400080c210f6a1148100c041000e02c4d5804401c54100d410004800f034003c2d0485041140d401103255200c03564644111125842580c61000075840c140c1c82190300d0000d800380802d481000361800080e80c0c0180c1d101c0000782d00c2400350394003c00010600144200c03140f0309960004c120a20311100501c441d8803003403040c800c202c9946c14441c040701c00074680810250b1210540c1c2035054034240c000d220190b4181c00400840308101c07000d2000241080045031140000e20503255554820482040d91581d135130042c05100c10542c04a0904036940d48403481507100c01c941210004000010400d101c40d0180f00312805049 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 536714397 1250 536713147 536713183
    0x71121010b1c020f0604170607080702011e0c030e0114090c0108010602070b09011103030703061404020f0304140304031703100f0e060112180503120702010209091506040302040905030309 82
    0x1181902c0c00c0e0781c1d03032508400640030f911201e1607800c0c584c607090229070061200d480c2260300400e07800c1031941c49031029604580011208030109042600c1401002101844402118015207840403508024050002c58205040cec0721000000082d43c03e10404040d00e41e07126000d07002d0b103401003a080c104041c1890090500c40d00fa0011301c51950300040d2801903640c50140199103024150040e1000c0d00302e202030245500c4000308000ca4980d040e08940100c4d6160f00764a1041903c540400080e03016041c03024050f0b04d014030002d8045035003010618040140c02060301c4c5003d07200d4860a150507032007604c0a2441a0010910001502d10000180100740760940e031045141002c8030540340c0d4901800c804e04000200007030f40c64010803940700009817038a42c00103c05040b01850420344980110220780c145000003000030701e2003070060080711100d600050400d030b500e654841845a85c2c0703406004894022009200100058682e48640365200380110010340d164038081423503502d041a0b0580c0c0c2c1048032 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 536715647 1250 536714397 536714419
    0x50d08011206050a09080304050d0e0102120a05030c070b041b090606050703050901021006140301150807030215210f090703032c031501080d030606090506071121010b 73
    0x50032500a0201c56030b8858000314541d11800800c001900b418038014000c00c0000051004000300000e20083c400740585698a100c1030080059032200385103605240c0140040004440c21071040006542c01100700034054103000d442d03100e510084200b11801c44d0b60040344000807003850f02d2038912000070805a1011701c55242050f000802e070b030090102c004c0c240180411081d2443c5e000b80092500c003407240404001081e0389e80100300c2030701d071540e100c10f00a52074403010909483d01c10745040305803083c210050050925650038030003440761030b002080b01c0344c0c0140903401442c10072400301d003d0102041000b154a080c008101c01d803503031002d08100050b0b0b000f03a204000003608810728403408420b04185c010711140102103a03099101396840142d15000c1c650302083e111600d140564107807000c1d0720413100740c0e940503007003907040301d00501511012070740710b4204110b03030300c1e00c84000e203078040c401c00c0c011011a21034400714481c24a08010312240704a50030342e104260b01c09100c1e810060b042214034213201 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 536716897 1250 536715647 536715659
    0x50a0b120a08040e040f021806040b190e091e0304050a090506030c130603050604080a03140106020601051e0301151403030741030d0c0c0210110c030304060c050d0801 73
    0x10f03200b14400d11188041000c005000d0000121040604540190003011542102c800300900f2180403a00d0a20503841c18103840403d0130410300d00940050303400c0302c0700700440c2005070030310300d0400052407404a48240c081002c01100b00204d800c2410440c1401982c560b0300306020440040b400d0340004a1a900d031604114644e5030008640d584401d0980c2c0c1078000460740340030140644010380001d085403040380f00f444200700001008000007a03244c0d8003005180c44030032129603800b5082c8940b4006034040d200500541c54100c2c405426480484181c013200134469000ca800d440f9407000c2200c00110808041081080302c2c0300051a890040303002c3c0d40340c107000382c0d207070703001c82401040212010130041e2030032119035580d5255110001034130030326070411101100640d030b90303130b0052580ca0b0541e4148550402c0f040e028480d2606010707070082030340c891040025011074250b020409a1307041849924000400f0761400e00080019202a540d11081207540c1d00340039240002c00d125810821441000410903 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 536718147 1250 536716897 536716913
    0xa02060402090a1413030e030d0206060f04140403051305090f061f021e0709020f070c08010903080c0702180a0f051b07080a0302041a03010806090c1e010207030501050a0b120a 77
    0x1710100305001003503a20420f060407180c01028111494041c4268102440c48030f8001a14a21901c01107910600110200013408140c450194100200075070300c0011400290144010f40741e00100c030451102d142c1d540e0b84c0042c684810944080d001a890b1800b4004a4100120b4501c08a405c2000e060001001504029954070a20703007415114010200b03440c40c0000d0510544004050544007503480340b00100400551341d202160880e4000400200054411018029041c001e509500e4250300c07603036817400071100c40c1d203c0c51040781d118800101c43c2c50002070742c0c28410700502c000704000413000d040584860450b030002e0315400d1980b4940100e40c0404680c442100e04495000380c0e020740f610300310707032058000e801a0340000051170000044182c00c1510709002d11304a804e06812102241c485409603500c4c1d0100401c05030700291070324070070ba404021044841e8100074045c41100e10069994440360b00b141c406881511620b6111a010001413070712000e2500c9100d4108050b2981c00c040b0390b03131240 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 536719397 1250 536718147 536718151
    0x2001080702150c0c01060e1f06020606100509060705070303110118080d020703050c0607030c0f0e010c0222050f06030d08010f09181410200301051309080a02060402090a14 75
    0x65860030004018001c0842908010007c100d1140070442c00c1c104040c8081ea01d06c2d620b1900201c09894080002c0c02d5440018541c0c01150b001e44a1504003030703281021280c43c0d02c42000590061760400c05417000810070480b90006602035504e401003054900081d42c20b40307500007040244201c0340b4052030045043c04040321003101c2c400500603035404c0701e854203503103a01818041c020540182c1c401c00c1855500b5401c107003140e1049981d0314800030300c010000d0b2042e0100c100c191703001950140d0b0300e000504200c0f1903051041c001c440300100b45640845004207a82080724002618040807080c0303d2141402c200d18404c0038528100300b070b01396062526080184400b8450000459120f19110400136001324181c1641500a48968101d8854403200340d81c0e80ca1083c60328480602c0c01c1210240040390044402d007480c20028004e141d6440d0404001003070f68142c0c500b0381c0056030f943c02c0400181794980140748200160300544164a000d0041013440700c00205600c02c11402e21a04010032501030034155 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 536720647 1250 536719397 536719411
    0x927090c062208240a050f060d020406180603060c0201020903030a08150d03050a0801060f17041a09100b0915100903051f1d0604020108070c200108070215 68
    0x8481d82040ca140181d1501d803a8000c816038002c000f013001c0060500c1c00e80400c404401c18003500c1c070b074440510f10804c0354400c0322001c07a8291400c1c0459503d00c1d1914048a83c24001000851103540715610082c0003007150b9441e4200541e10b00c010000c11011307024603004116940001c5080c0030760f4901098881c41100100e00822022800184d80441c160380d188900c0e82002c1c0c10280c98592525014005034040141400403807590000001c0551242141d04000c51031540e49410110100c964002480c0010340211042c1c0c06c01d42d1070050141c43c0c42c0341103100345d441c140141280d8101e45110320490f560091540d0080c012001004020302c10b00c401c00c41c90300020740e01146041185401202d11040030703000182580180110300700118502ca00203024408030310403c1001d0500b42640c00c0c800b0100f03003500340304c68200790300240141d0b00460885511a201d400c06112a07460795460928407001c501c000b881031600c07500350030280e5902c10030441d800140d50008082d000b281d0070143c226807100901036 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 536721897 1250 536720647 536720677
    0x1911030310030311010608030703110625050a0e040c09061202040b04050609030102120a0506011419082a0415170f0601020c0303041205060c0a0e090703020927090c06 73
    0x42c503119042548406c0050041e9401d40b9100e1003240350080aa1400000741c1075688501d8000c07501000403400130402c00094030f025000d0840f402241a02d035500580003200038095100403100c4291a54050004800507660703408441c0b505080b8054020281142014182e504c140f0040c44014650000c4030b040d0358084600c00d03199801c207800139000e40f080c4800030f4000190346040c4040000c060704011301580c0240c880c40922109500d401c00c0f18000c410016a10714050580344c080503018140c1550401c02e10342400e90810822030b004078441d0302aa5214803107040c00242040916414089415104070a10b84105101402d0072040c062810190454500d01c203001e0108607a80e008011711f001401c0041c054a44441e0740b1186001e06500c0c4040659050160000048146958204580304a400342e00c8202d0000f43c02e1042c81049100102440c050690801581c3c1c003d40c0c030310090440380c0035070100a0102c84070303e801c6500080400380c0008441d174003002d00035615980b054280e410700000f181c11 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 536723147 1250 536721897 536721917
    0x110301080d11251206050a0e190204050411060408070f0f081c0e0d061b030c050a08040f02090411030c060901050d050604140408070b0f04020a030809040e0319110303100303 76
    0x1010402c3c15960114220030951800941000030a4212a1240300781c50001c010b413540307202d40907446030010350b078058005c09900c0a0310700601d0194040e5400600644200c3c2c0e184a0201c0400c103c0c0c2c1c007541160506510400781000001503422a4001800c0c2401c1010704552401c48402d03038400007414075115500040d00d00c8050940f01e03407000e9087c0f40d8010b0040a40c51550300f8500300406003840901801d10301d01c0d20480c12103000303000d11a2484900c0c1c1d01c80d840c04103c00001c48840d500504101c81300d442d0300640501694445103c2800f03640122480b00003070303407002c1c105441c2c5103185200c640140c0080c131003d01181c0e0040140c61121041c0080031440340d646030001001480715803110b082d040c10b00d1050206000e8018050040c2c50301c95080391299072140703d13182c400ca21048900a60100303030b8490601c001038450024000f924409000480c0c2518140c40e143c1c00c42d00080c10103840381107200003c001c5954006c0c01e032542180c07103802451850416a4420604510a010240c01e002e05121 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 536724397 1250 536723147 536723203
    0x504060c061103181203040f020909010b0d080d0b010215010b1303140a2a05130b040501080d0e0108010b1204052803080c03071e0201020409110301080d11 68
    0x108882440c03403500d8659603454030984c0400f403c0040c0c0494422441040d100d05100c400d41c4e41201d0045401694102e01c070300c0303594200600341e00c004003030203015520b031101002d5503291032506880045c8204082d07078850550100c1d030811200c48035401411580300d41c400326466240424428103440384002103644d41c0032101030600e074080d1641d1005069070100c80f10301000b1200031803145c22245c8141c0751400203a0501c040c0c03002c1101c141024802c0741c2da40000401c40c5250515000d000210b0514004c90541d84800018084a07826032007034405400803c0c07601c0381d99602c000c907450032000c2400d0403481541440d000c1c192500842c0082120f286480011038240710040004180d4001040c840083d1400391002080c1d0b06056070764124040b03a010404903080c0041f14054912944043e9200c1c0071055452f120940e54616520601c025550f01300804103090a1034010300c40501030301c0307499907a01c0d4982004145425a01d045110400000494001c520300006c40c0c0c00c944a140e4004500c0c0244002c0 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 536725647 1250 536724397 536724401
    0xb030f0f060d060b0d050303010b0a080f070504050f0103062706050303070302032215050405011d09040b04021903060506030606120706050f0d050a05101509030206130b040e0f01060e010504060c06 86
    0x517000e801e510011000040640d480002080280c08076a520f0b41182c0324804040310458041c0d94160100d5002d000c00d001d10706001900041048051401140e0503603217140306031031101c42c2d2803001c1c0006050110320705401c0e880c3c092007008140550007140342c0007860310000c1d03ca01820014600707030b4a81c00b02a0480555881e100303130107000c00000801001d0941032015006038094429903000c9000246411020400c110280b0604007018100c40750380e5541c0e0381d0700d13880380034010701c2260f001e070080c44c0e1030400d81034242c1d904000d5071180b0000506410080c04044c078006000709294403401030003030180500b61000c11038108131400c0d414012780320b4000000350002c50082d1039410b03c056190604000c000c1c0ea0b242c0100c0c0c040e003c0b507902c504a2035110740060541403540d03a90784021031500b078410001400d0810080035501c8401c403a0300c01d40c0d515003c110009a10542c8500f414515101c00c1c040e207039003004800e5004102505240c10071100940010300305028a22944080c40300c10510041800110707 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 536726897 1250 536725647 536725669
    0xb2a0607270801140708070203090a170f0d03020702030129060c01291f0206150109230108090a030806100302092808011811031005010b030f0f060d060b 67
    0xb64024003c0c00c10550030148006021103010001a8144020441c0e080c0080110f50017280d004d404800000d00b0304028142c0d460782003025071828401e00615400c0100700744810310b080e24036170b5405030792400180101825544440080c8096802d107003040004010100f010081700c110560702103803039aa0010101d401401102568180f80c4035070000d901048280084c03004045200f01da031403611805603081622910340240b586400360b40300e04086400200d140181141c000300c145800480c480e1501107021100d406005100c0580e03c0e1003181c100f580da00612410f80c020316000007420304141a0710001c000c0c15018090a028081c4040142075062183e01200c00c0c5680c040c14400c0041c28020882510740081307444413408100103100031a00a9040c0522984454504416104c040300e82c0ca85020180c1c441c1c1089905201c0d001c040d40030a03800d4080c079030013058084039640c0c0341d20381070700c0401801c00c00801500c055031500e0200700c155520349100c3c40301141c01c50390009a03103982c500441d002c8540 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 536728147 1250 536726897 536726909
    0x30b0a090c050d181515092c031207050c060402061c0212150a050906060a05070c140103180321020d060b030a060f03050d180b2a060727 60
    0x1084c81900701900e10842070303081c10340704030101c20920900c8000c850403109105200c0e000038243c0c400810081e2120341062410036030325800c50008485000c001003104030075155074405608042012100d4484c088100d561001c00d60608510308180c0c0080991078402c002c100074850b030343c0441e08420810440d9070010344030620704800c540e01c06020703040c5841d10368211074044908a8400003242141801600c5504941020300484a01e40700c2d8030402c92140c0100e010202080300910a04001c01c001148403401800d40e0803034800780c0380c81d43d8001001e131303507a00d450000c950080904c1000020340c842a000441203641d40b040c01e421400e10b041c1d00281c407030104070184060900c01d002c28a25126001140200c5071194200005030340c071022108241014440507091340c220391074032810076004101141a0301e4618911100c031644500c4840c1494200f03c2a6620702c01c681c6031200700d41c150304490745408000c964000d19a500d00f00c07000420002108441071036480801030f90b0f080380c03115409040041c0003 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 536729397 1250 536728147 536728151
    0x90c1209050609070b0c07061d04020703091a340c0f050910031110050c07060e090f0606040506070203120d1418060609090a0b07020d0f030b0a090c050d 67
    0x110320309126940b1002900d2800c1e05000345a000900f01a90000701d440805003031700608071544c038090041d13596110348030082081d40d000d421402d1440e603c1d4402410442e100b9260450001e083ca0000700c040065400d28074140c8102b04110040442c07505030742d42c542c0007140302084214081950b1b540c03079032a04050042001c4408075001c01c460080d002c001042d58810b4a80080a035510000d10740504a540702c094014103080301c1180d41410315240f88025015541081490010340891651070056164452000101180c80e0b85801e40b81050441382c000031a0344040d502d0703062210000340c0c14443e81c03203894441c0b4400940c200843d1024081150107017034807949a40c03900c0029035001c01514a54006292550306280002c0c1030b0141e20f02c04280440144006000a0f81c480044c891901000b503d12825840f8510149000800011130320340310310081d0b400707081602100b0308080c1403080b138000d41384181800c0c000103460589880900004a481d1200045030203442d0400079162031149840520071a4 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 536730647 1250 536729397 536729411
    0x506060c07032315041b1707090f090c060809011d06090c030a0c03230307060e0c010e1309060b0307140901060c030c1209090c0801030b060613090c12 66
    0x1000c9a0070744000703103c503840c603a15156030440a03840d92110812020103c40c1500802d021420810361901904400185884802e8580204260b4008001c01554160b484410240181606405140b4013440d000c8070611a00066648001d00c5140074010341040103949030005403d01030940103c1c0055100e40341007082503040308121a11054225040134091051344000c082034200002c146000c1030700541000c0009085503260001007100c5552030160001110307548140303880c180014803019101c2d500029842c0f005003003a41c241148154468140006a61414056160080c00c05522480e220001650032030307034039120713006041d00c03c041901486104001305990b01b10101303c1c403917890100c0c0c0030034691fa40c03854200d5620208580040009604d05440c00c00108015003000c00e82906052100c840e0351102c04400481d0b01405c50300300002c022800404c284130880c003d480e041402a6030f8145084000041d07000001c0c0d60740306841000780d99403d081105849071303103c00600360620800340005 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 536731897 1250 536730647 536730653
    0x406051509280807080c180f09010f05010902090916020c04020306040914060117030a0903150b060a1701050a03050327030304030309360f020714070f08060702030702040506060c0703 80
    0x1441e800d01600700103100d0150403041d10b10b8443d030201011f441e542209221984c451040341400c8070003802c6880d5039900e403152412000c0181c054a40a404c5c03005d001600c591264042001000016200201c902e0101d10202030301c07540895109008641a1400360707580d1250000318004020100b00582115036039086d10345500d00c089142c0e4101d5065401480401d01e44031095600d0303201340050b10020400900003000000c036401c1d5a544028441300d00040c80045440c0440e12a9000c032035890001001d000071180042c00303261101e409814103075149084141507030380e060745d20700c4ac0008084500d544010101056041c07201d81c11100322001d425a41c40301d0792480c0c06480b46a250080c6001107207811503603030241c12102c2140080c070b600350101802e401406070395407006041780203801450940800c5448089104a9905c980014414000388001490f1081d000c0c109400ca800c1306010360025030600030342c1a400010b0383c40040e0102d400040544560f000115548900840550540210b000000034 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 536733147 1250 536731897 536731903
    0xc0c08160b0c0a09030f05100e070f08071802031f0608040b01080a0c1502010209030106080708060f0735100303030c050f03150316030f0204060515092808 68
    0x1041c8911541556501c5481000d502405102003080000b03006500c1040403856488400440902440c1174800b02100b417440c9805940f42d61090a9196105110811850070301c0c548410017400c562000c2c001c21410070059008000c2c1c22680c1a41c11500400855003000c01c9005190401c820604d00c05000d13651504042d2442c00c0864003030f00c0001c0920000128514041031140b00303280d002a44030041c0e4205204950040700c1c00181034115075091121107200d40742480b501001d0040b0300000e10802d4500510a4079285009085032a0910301c3c0c8240500309800000c041d1000143d0b072071803c14070344188644d4a00c119407401100b0380080c00b50910103840b02a1380c12109890280c1c0d0b0501c4203c0590800f500c003442001d140d0340150310100002000c0b603071001101e400f115002015140c440d107440307200200303a0741c081d00141d400b15001c20b4001c0451502d4411500203010668103a603103080d040030303a00c1060140803690b601500306600b80c0030a09485020581e003c01c110b84a89034025200c41449a07 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 536734397 1250 536733147 536733187
    0x10e041103010b2107020c1c051c090f030f140c0d060911060f0d0b01091d040c08120408010c021c03051b130603060504050f16050c0a14010c0e0906040c0c08 69
    0x1005810783c1ca05109800424800c0741c01003070300711000380415400c0c0459002b00701b19a1500004024065401003581c0b42a032412100a41c060b0804480644190034211070751203205d4600c54080d03000c49800802501c540e014940d503a0340203500061014100d00300300140105e441c482e140d116030001402140c041d01070b0080d029030540280c0411100c8d402c50015900044031307004031070580b61050150804e00e00d0740d4007034030317441446440d449803d60754036802c242c85d00f51202e25107001c0c42004203040c014030703100f48070b400b607810218070092482c803803050801a05039802c2d0f18140700701501d600c0000c61010707054000341d40d400c8103400300030b1381d600c1c40f03a001d4003c61049000707042c0007078207110000401e40f5042c00354501682540c0455081600c0e403400b000c0c002d501007404403041c850144110b0f10800c00c207110b405c0b903180c010b4212810b120300d00c403003050031a81040031a20500c00c0034408814642c8a0301ca020764004020380d400030f162900c010098407050040d00006000100014540c50540c44004540c4 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 536735647 1250 536734397 536734399
    0x90b28050c190906120b0301140103030c032c10020c1201060503160302180702070b0c0606100804050601030b1003150906060b0309030708090d050d0206010302010e041103010b2107020c 81
    0x624019510101110f120354144250000070f8140c2c06034441100066000403510700300140000750b5101c90754089840d180302603000313401103400000c2200605400600240003540e503891200e017400200302c480e04c2c4004030740d24584d0150001d03148001f4841e0080116142c41c06000f000c400314480300d809007a000c4c4c59607020b80c5000e0b00039215420340e016505021300040e2980102601003140c01078900c1018148002d01100441c42040360010341181c10b46d0017071034445201e20245c402403502c42c1c14400858a490030070b030704000c042010000410b501140d038505482d80300c0240c8425031982c2da907099100c02c42d500080d142800d8081d408000351b0f840d0b0b1002c2070203445000c00b40400c50707840700e1720245400119031803426a04100280000154100010032041c10000c006100205203502c5071468408440340c1c500150740720314014000d40d82c00400c0110b070880e00300c400b40b005c0000c868000c030741e60206110b241c4030240003150300100300a014045c1c150641d10b01c0d50007445854040030081d51600c00c00342c0780b = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 536736897 1250 536735647 536735677
    0xc0f0a0213021e0a0e0a0e061c02010e0f010e1314090a0507030b091005011707050f06070209040213090b0f0109110301151e020a050f01090b28050c 65
    0xd500c00390a000751803c0c1e4420703008003607400c80c6580d010724480e800b15803482c0c20420002c00b45041c3c0e5498417100d00181c80b2410340e2110524140c028403014202041c0d200c590700501441540051fa070207200d0313842d1a0402c1e00e11568045001005030b6400d40c482d039966602001403901c00d03a1101e1513500c1a5154103411460b5135090b1901d0040381e80343d8410600c082c140303410000c0f0034800704024580301c540040413002154001300302c2d903a0510440b0000c0e042002c1600700b000e04210200070030080040904811a48031f428114184002038840c4110040207001d0030f4010001410365a1b4440811841d050082c8240710084240c54183c540c1181120042d03101082d0400102e1a03440c0c43c4174071003d0010303982166103940d00307001014440201006e814003c00421030711a449504003070680404c170501903002084903c0c010f1404900344120782c021000103a24144a44010462210b03403203410205035409c18000b03456420980d841c8045030030780c0d55180c50400d018000a58200401045030796038610300 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 536738147 1250 536736897 536736919
    0xc0106090501061b030e03030f1b15061c0803250c02090103030e030c0a09150b0f07290916080616120612060c031103010803120a020c0f0a02 62
    0x400c00300c4000303000d40e00003d24200042c1c180c0c80368080d441e08a1a01a0402c195140811000240395030302514100300300b840c0209070208046811030150101095135005442075091980c000309003242e00924940c412900702859004048600c505585001c0c3c126a9070742d62813800300c020f564007090011a0140c04010041c403010414400c141d5158403582c0100038824a905c0d544044034000344501d04507600d4043c2621401ca40e960303100755813004129220001c030b00394125451100115a1035072290340044010812018422504011104000e81c0070242c4024625118a080e9215420440ca0308042911100340107911200083c54901c0040b00440c4561140d01c03000c0d4180c5564003924003102404800a04e84400d40c010f008041034030304001000241903503244484e0500c12081e20080e10840c1c2d07203069807080c0c1c5500d4040c1c1e0a81100d582060b13851035141c140ea036a5244180350300002d1504222010030310000d006c0d011504907000140458030b61602000082e62039409800f001ca10598145c40 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 536739397 1250 536738147 536738159
    0x2300103050f0d0503070e041803180906270204030c1d0a090f0f05030903010c080108010c05040f0b0304020a17060a2f031b160c120f0615080303010b0c0106 69
    0x3d1850141c0c0c2081d522203003140c450030002d4078904540d4804552160711105803201c00504203140200c264000d540303095080405503c0c00c0606502c42e04600000c80c00c2c49814007138400404103004030004481c214000414445004900902480e00000c01c00100e40200084105c2882c40d00044c0c0c1e4441e05000e20075031500e500350400ca07549070100815020b20201c2c1030010580c2203d004003110302550540b80b518412400290840b152991020701240440340184694442403045140404181c1002490b2908084e16000000001d21416005840000c000740454945c01c030080c00030183e04101207000107840e0203240d16440100c90500d1040d20f0524014400340c1000c1848034502491000c0120342d50343c030301c0402c40c150f100900c00e11144003602000880c6041c9980103007070a600540301d60245421a160001c02403d40d94846074000f40c10048000c0840d08800720106034a5212400150080790003181d42c84138542c9621948080c040480002443c81c2c013000144586a14000204040342d00e40c6 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 536740647 1250 536739397 536739403
    0x20105010504060501090b030402030f0609010e0c09100b0c1f02180f0a0611011104030c2402070605160c081609050c070201030203072709060e070f0302300103050f 72
    0x31284c45d000898402c41000075510810055030042c0c00a42aa250840120300726803801c0c0c01610b101045070341d1030140c203045407824420408041c5048400d29480c0c10110304060380d8080758011891035580014030342d0f0182e80c007080785444843c1051541e400b010b400c40c650b40c000b5001941007041d03194882c0c042c20950314088165440b01d80c0020401c40304241030080456644001c1044c40c0400d40d600c5c140b414603406048054401144100241d40c82079007001c00042c20b880a40480c4030b030110490222510700368012816100b5902c040c50019110305000040b10024010114060440d0014a50100d80c0a4022a02004a480c2c19095501d5190b803071951104440080340c4000c0190000e1020400540c840c0c0c0082d6004070081ca07190301940c010031641c911580a407110400c4050076150b04201c1d1095a02844006241100d8052568500040003400d140c100c500010b0070190700180c0c038104005e031941c030078002d402c0210002203c5020084940c007820420b00055a42d44291121410445000 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 536741897 1250 536740647 536740649
    0xf050a0504050a1b03060218151c05070c0b1504061d150109050303040e010e0f071b03091701051e0408120402041404110f0406050303040b03041a01080d02010501050406 74
    0x1c0001c1141207402d80b29031801c0e004c071041481440e003011030004046000b5001602d070040c03803040901c4a051400c2d080044d00000ca00c5940e8424505101c03407115111480222408c2000750700003c00e50369030f60001110309001c2050010210321000e8140428a00c02a0a40c00c017010142c9007000102d803030b420034406104a940c107100000003e0b40c00a01130210b141c10f05050702e40d041c10561354180c0c40d480028216040340d00880f205000a400411400310803006442c0c11003061804040c0504200030000c0c030b60074264698102107078911080200309440380c03407100c3c000e00c448a000d0030b030508840c440602034001a01c1390400741e107115a04002d5032040741c419a015640c845545440c0250315624044030100003001130f44e0155540c9c10040c0310b82462070072584283d200e2078109102032501d808000322038040004490050745014001c6c0460780300001100e09440860164a46075070303503850250b00d1074030558070406e000d41445000003046280025446506d1045800901941c2e0700c90040c0400c841d41 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 536743147 1250 536741897 536741903
    0x90102030d02180a080f0a08092e0f0507020a0501050315091303080105121c0207030b0106260c0a21090b010f06030506010519030f0c0e03100603080712021608010f050a0504 76
    0x7c8003807500c1c00074400e00000c000d80300018040c0300300c4804030752081518503000124000e84400c03280a041c2e0050344410705810032485810554240303040b5802040c40c040c1940115414082c001002c0740c1800d5000001086803070004003ca2500d24118a40b2500158101320807804030b040c450000c02c080c5020701e02682d42c200e8500041542001030b260b003068140d0104071080550180c64008000701300b4152102e40030303150a8480b40808404107142a0b190b03011101d002c010f810b4a5010301c0300c0c0507501c6e0b0031120454540d162403e21400715004007120401d1040040d09250301d480541c2c01040850394106040380c020040320100349541c3c2d0700507001d1b20021100d840c0000c0e8100092481c40d43c1164605a40e0b00403403a00240000c41010404202d80360103aa05012800403504c045003450204014030103605554803d001951942c0e5882c0c0d0709019028000300840b60340c0a45030700311072081104038200310580005078881a07860342014000c04154020440030380c2400c0000b20181d03951b01586014070781c = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 536744397 1250 536743147 536743153
    0xb040e0123060d171b030909090f0d12230106030c020a0c0b0a050f0a0e19210501021201090f052503050c090a030809042708090102030d02180a080f 65
    0x380d113644940c8804014000d02541403c1444001151039444412015540c00c50300115641d45060f0100035001c0b0000b02250700c2c0303902c420002a8250b4011a018a41032290309141c10030307002c0c0c403860101825115a40180051250001420440903c0c040504031540b40d2010070400c0c000510803a15135000d0740010389140c81e400410000d00c24104000c1490001d103151075030a02c01c000010103120f0340010a0701000031901c1420a005150129601426800480741e00341034615025610300014441c065064210703181c0d40e8070005005003074044580c52042034201c1e8070b40b036845100e4800109440e52010311194504800243c5040310070504035070300607040307201c1d82140002c850121701410f0018032814040c0014098206e403500d40c050700c0405540f061006c103031511514400d0104841401907051141440081c20381c0d502e20241c9514070009421840681ea0f43d5034110050b440c41c41069040301d6610301c00603401050140307584440c0343d20001110b0129a0696641c80199501e0340f1100d039100d103030 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 536745647 1250 536744397 536744419
    0xf05101d0601140c0a1703071b0204020c0a05031305040908160c030c0b0403060f050106080412090b0706050117011b030209010903021309050709050c09090402040b040e012306 77
    0xe99241610307580000140b4000e000300f06800340100039500000601e6020b0b074017454004080220041e010350020420310007081c02c503d041c64004002c00c40924200e910000940a80015900d40d078045500350341c6280101c1e15400450325010b550380c0d0194a1001ca035040e403420105003442c0034007402c20382e15044031415050444801c21000c8101301c0310411202c0303a05a001c000001a01018200010315101210710f403141e02d5401d11301d05480c40b450a0a201c03c0c50b007401440440e8000c00a6500141c00000790103050881120a560304042d41d00071521400021401d41c00300000303500114180d0f100310904882c80121600d00743e080e0707110f08100c0010b10f2081408900000d00c80d90180030712110501d8606c28503941d940220305054840542815210b807500191420311804000325401848031040400141c5003d0054000600031a40c42e5072103203802d14045001d554440c2c0000c130003840010300400c11402800701041c000d00007811030864084084a81d006c101c089101c2ca144618070240c0344038500c1d = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 536746897 1250 536745647 536745689
    0x506220c031509050106180c17010e06030703050f01050412020c0a06050c0a02060706020c06010609150f1403130209100303090e07051b01020c070f120b15130f0510 72
    0x110000403507040040b5561010303000802c0c0b00740101402040d1074401c442001200021447c00e9414200403207050090654444144804400a40d411100e42c5114040c0507114800041c0c10292564000f81540c4260100c2584190065001c940142d105450440b8070510880003681c4607641e000d03250350b200902040c04c204841c0600c004000c1451360109a60014403144e0004001d50861b10042d20901c0d40480c16081760701003044002d024060070f092404003289044000c0e4000030b1141c0e13181040180e524403c0000d280200a084000821401c050f6268030f0000180714510210b041c060340310301681d4000c902c2c0d444241032501c040d260180c2d10355154030300b030989881c0050070142c2180304210003000401203c2e0382c3e1801c000c8081d18440005640d030706007112014900b10b41038101c209030b498041401c11a076490702000100d41540b1080b0200745568901041140c1c41c00081c07410b42000c01c1c0182c1a1054007207a024013a0301c030006100f0002d988900701e51941c07910f40c1b80590400c00810b0344210010b = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 536748147 1250 536746897 536746913
    0x1409070203091003240e0c0a05040e070f08010605030903251b1401030b0609040504051203010b0408010f1a090405030409140103020f010c030917030c0a0506220c03 72
    0x11201050040301c0c608010100801ca008060141c40d80010b076890342d98410128014102111060724403e0702160142401c110308140c810140000b0038402000400c100f025008500351001402c0c12804e0b01814a030225010300810450500440018140d400110310607028000b41d17401000401e00660802c43c2c2202d02501c48842a00074003d0a6003803041030300040c0035034034030306851100320000350341b09464201108a41c440342c0071140c0c10316051100041e51038031035900b590101c0346c0803180414586c40d0350500703e0402800c4541c044020000000209001c680303030300140101c8076204000c0111090010052040b00c0c040c1004040c003100d981d03983c410714917281c50078980241c011030981e454603544110a908541c0c201c1c100000c44900040100154640b0b54080d0142c10805c0c200340380360081980c1e00401200c2c203402050284c10380f02d00e1a0201113410010f83e071031502e42904994480300c0b41c0c240725680d1141107a480c142400d214102c05185015000d5840f00150f00c402651aa039083d90743c0c64003 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 536749397 1250 536748147 536748151
    0x50709140604090e160b0703020c0922050f0d02010902030a08130f15140a08160c020d050a2d060c03090f0b06090a1109150c0708150703061409 63
    0xd4084000e0101044821144c8204030080603030300000c20600e0400740c8445807150b0198014000c00704140300d50004660081072040b1015012103109460350b8600880302004403800782c1a840c1e19030542030110030440c0008500040c054804102d0341400c02c0382c04100e0030303211134540c006c0d05038000d566106c0025401c0e0000d0311071203070040091044980c803040080741050f0554000701a515286e250002403079084888605040380b0305a9561900301c54070b46c040c250003030250082219170a603800d80c3da425445418104a0180d00400320120309160742884c0c0d540c0e103180741081c2e90240c0b60b00100d05034071612010007001584e00444105010b09e050710345400800c03095140c0300c2495259070794400014a00301d40c042803a4800c145002c0c8500b040030a00a8410000388080001c62030302901495681e00141a103080306070440b400043c401e000c92101c0001e009040460841d8410a9800302c1c80c0700000c91030840360f5a480700140b400f50f43e10070003102520003520400810343c1d01c504038540070b41811503441d5 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 536750647 1250 536749397 536749399
    0xc0c0f0d0209040804240e0f03070515070b0a0917070507170307060b060307050702060c010207080417190c170a05070b0408060a061518090c0e0f0405070914 69
    0x2003503500150049030640c10200d504a031868000142072005c0d1202003018803904140c41002c503940c0546c00c5018010081000c1c0da140325034824444040b45030f904100540c040e0001410590b07617503031840c2d100c6181c2e420407001140e01e00c41c1c071000204080128424003c0399078002c8130313a0148624020500d4900c1d4850001642c5c0c03030041c0d0902059581e046500c110055805000540e50346042c1e007000d008582c12074004900c42ca50410910048561007000d40301c61580481c1c03040e507030f4031802d10340a009118a4000501801010400107800348003811840c00d0f08801300c0964141015403240312404203c020001400441001402c1c00300f081c190000310000c6024074225600d0100a0b1515032902402d076100a0340420002800d2000d00c509104058100c0d80c400c41c280241820160310902c1100c22001403000c11a010340c0c41c1f44d602e122a900e4100401045e1401c00040f200b02d24001c1006001c510500d010b0b02c2101e94010040c10144905440343c001543d4043c0701c0b078104480d0702d1612040840031 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 536751897 1250 536750647 536750659
    0x5030301260312070314010302100f090e0a060509010801063b0a150b03310813030210110a0201080a110313140303010609053109030908030c0c0f 64
    0x307400520420001401d0400f240d0750000b07020325000300002c081c2c503000b0126450391800c9400400c0140c41e40c0d03104500d45041414403800480904000f00e58241d0035501c10032020441c1d0081c44001207590b480902600c200b03880100003682c03211165401e0b1607072441040b51031509006001e001c515030702a913520614104201e0003400d004020700d1210702405541d44000199180c0140443c0c40c084444600142040b40700b8a003145454000000c4100d07450301a035254010341100440f42404004140165584c4084c030180c076110b403e07110203001d0727269000c22030040882c0701010901d0fa000e401d500300c90551060040003a004254011030b0710705c4015001465141d120440341042102200185101d071115400c484c2d004045814944005560054100c03419013041006000d8654049000c4040c0c42044d80c0b03000400e50f41e40050500071810f81034440c1d42601180d03d4000b01c4075660403018600c5d0182e601d1251840e11403541c2c0e41c4a01c101d00311003195601191001c0c2450901550300040c001e001018 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 536753147 1250 536751897 536751959
    0x31c1b080f07060f061202010806120a0506010902030702100227030106050a170d0804080421120e1302040503070614091011011401031a04020d05011107030e040905030301 75
    0x3441d110741d000420704030380598079006026904602440b50000600b00003010701c00302c1c00c0070f400217001c44c030703010b040207001d0786900c00c041140d00c0042040101541d4458101c40c62907a441d40104000d42040d1010f10040c0506865241140400e00a0700c0525203440030540c02c61650f49ea0862558400c084865015500d0f2200040e050355410036020050001c41c0c140e031010406200d40c1c608202c042440e0105000100080c230003c6004003045e1016160801810202c400407400703281000c6080c001d00401c0d50192890740c034011035200c80401c01d020b5099420b05021f02c0b200300040181c2c0680d000700c68150f8425070080001e03d20600d00301c090409040f4081d8038084070036010900c01c15880d2140c0010481c078010b501c2c00842c0c00d20a00d004010074000403c0294115035401b42c2c900300c1800214401c00424011800307640d1206144107400c0d501000802c0b26006140030092560401038003038020980c111a6200c0d582003c0c00b5165035285e00002451440e07007007005007040510b242e143c10086184a4030 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 536754397 1250 536753147 536753167
    0x1d0f060d0608011a01020606100c140f01020a050d0b03060f160516030801081603050606120f0601091b110d05030408160c090e03130303030209060d1103010302031c1b08 74
    0x803503803040d0144c10514092181c00308001902c1c01202074150f6025044003000983c50b95400141f0b41c0042c2e03488070368001c003001c0c040207a9180004880440c2d4055100103160910950420b000302402a01c503501030040c440d5620070180c40f02022603416035030104050000340483c0c0090b044000b4000241030250920021590301a15500c019008901085c031040040c40346420400050001502d204102c00c80942982d4969449150103071100703001c0c0113000001d0031443c106004503880e00840c14120b030080d40e543c0820030701420842c4105a03000304804140302a55109820000d00c01c02a980102004001c01108458a510092046c0c07541c01d420b010002880301106c000303501540c044d94410380040e05241c100d4007151000100183c10b030740100700140c68500c13902e5200c1c00701c079010b08005031252401c01c04110f00c0e100386881954454503020907072551940702c00c01740d81a240207034219603030542c0e60103550110012100c2444082940e200d100180c241500c451000c0071b512801c0840c2c10403031022 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 536755647 1250 536754397 536754401
    0xc03060103061d2212050703142a0f1c091a040f0b070f020405060f040906060305060709063f0e01110f16080c0303070804031d0f060d060801 62
    0x8003a41002216000340503504952091407002031851a148038500e8800c5d65600100f81e4025216100780000171803a02e05140c000e074411600a41400d00041e40d408210303040c1d0480002c0c0e529140c04c0403000c0e421120b28050005a031031203c1145400070442c00071030342c84050007a030f2500030860402c40900030204514440a50490042ca9441e04450300d5038180358802c1500c0c2c14980115003e801c1c140010700204402c0a9210780654050301c2c00180f5440740c0d00400e00034004407040581013403e041042c01000781552151084038003e00a8840c20703143c48500301e503801000d215000004410306182420b58031404009480040d0401030110140e0070000400c0300110310303240b180035076603170340d41c00c808001002e001303406200030011545440c00f50813450806090140719801c400446882c400709080100e420700b1a0011548441260340740d02e0704100003480a142141c0440000340c0004900c0070f01141d00425460b40d08004140b11905640d407018805550421a00707035440c0b1741c0310344001500701c60038 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 536756897 1250 536755647 536755679
    0x220509071809020f0f130915080601060c080d15090608030c0723011103090307090e060709031e0510020d090c0b0705031c0b0909030405040e150105040207030c050d2309090c0306010306 81
    0x8202c01d048c085e150410190401d10140d000c18148020481c15000040c000c1e011240407160000000078001400c10384180040ca03203400000c203c504c0c04402058489001000c0c065415800341103c81c41c549031000320401d00003095524581c5600e905e1540c0e0755602556480c070000c114403003203d04014103a8001380c501700e01903104054040d81da0a59072025181804566408200c83c207003443c4c500c1c07450f510402030758640b4401152506a04100c1c40c1081401d01500112004c003d2080d92910b081200890050203904001c03070381107850480015203000c010702035030714441d00030f0702440c140910a241c10050300758000315005259a43d840781402903680030350050149038124000d544540c100014401281c2044e408034000350721030b64005044a803100e585505541c1c042e200580c8414140c0f0f000d41e940281d80c0c4004083e40108400319607915444a00c11030220f030040c071781403160448110fa102c0c07a4407410b1380c544d4220968000080103c100f441c010364100b00d041c9000500d0954031040d0000c44200 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 536758147 1250 536756897 536756921
    0x6020f12010509060d2d110a060f080601080a110d0504032703110102120f07030207050a031203090c12050f060f060303220509071809020f0f1309 64
    0x404110918502a0301880c9409844280c0d1046a541481d100003448408102401004a41c0154410205089100c094000304544100903119421240703000c44d55502850004e50144200040004109100b400c0c002024811030b1148110364407424011035864600030310164000341c5035410702c658900010001d040459103c40001914109842c00a012000c00c50f05905520280481c040c2410082c41c8401d041300d40c02100c850510765441d0061703003000d00d04064269440000300d4900300c0b4003414001003030307035510070b600340d8007807507128402c10002c940a40405800460300000580c0300d68003076807041201c2d0703000c1d010001402d1341d60040310745044614401194141c100d4000c0134001c2c1410804c030740d08590461381c051214a82107011030394034094405040850011000900010f583c090301010103000080c0091203a4941104c0181007921040241080600840c000103901280c13031083e11641502c224100d03160621000004400790841c03002a55034103424000068801c03e02e120391025640 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 536759397 1250 536758147 536758177
    0x20a020a12030201060f1d0901180c1a1c0e0a02090115031803050901080a0b10050304120e0901180e0610081b0d03050c0f06091c030b10030506030a0602 67
    0x110351800a00b5203840c0d034004054211b8603081485440c2d0a4400341ea8900906185030400d5500d41e0610342c0540000c0290203107900c0024010301c18004c07120018019220f440b8030807000c4c2001110600328510481800c0600c0301504000b0550842c106c1e003100029842c030800701c2d4000d040319000a004c402c002c0c0e02004035006840712029440c1d8140c00345020b0030712a0f907250b009070038141c1c8010740103100303480c5414104481e460002e06100100d40c02070000d032902a010f00b008007003804008d4415401a0b40c2560001c4c160b081000c4580d00ca0710070b4600510000d80b02c11002c0e4038040c49030700c14440050200504079110105c0744812001005801d01c5881c00c5841075490624000c02c1c18101460290205841401c03e41c6401c0c0d1900e41c48080391000d54980350007903596907039a001c6420518001c0703000c0e403c0c0c007c0c0c0c010320000501c001004085003104607410311500300d580e2016400c440c48a18266004414000c58282c401e00a61180c2d0380301c080174081e50141c0020765981400c0342c0c407510100e50300720 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 536760647 1250 536759397 536759429
    0x151814060601030c0219060507110102030906070e040c020c060f0d151508040f020108150d0308060108100e0c0304050f0a050a03080a0b0d0210030e031314150a030c020a020a 76
    0x903a060091641140c03017070000e48030308080881408102c005500300a02603544403004201164816044000c06441d103030002c64a90a20b01407168940320161507601c0019485070821000345042d22583c420494540c0040a00002c04824010681c000408841d0700e12000d0080c0004460540204036081705684206461181440107400d021071510040740100302c802400c01c4001800c201c0312154298090a10f00b103260f94102a042c10142021409504001203447d20410560040c58080c003645003622610120307031380d050b4031920b24480b0348540c6805203440d001055810102c14000d642060040050ba1b40306032070030007407528091050008444561041d83c18105241d4040da029410101c0300e242441402ea28100003500a00c801c14060b200c1c20f028100904664001c0c0d00000c5040d9942d02980e07140d201070180d40c032458410348607102da240f246040c01300d02d91528600089103034021664440c10844000002c070010b2440c280c501065218808041000d80d544d220070b4030042c88903401452280b = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 536761897 1250 536760647 536760649
    0xf0c03060703090b01090b040213060314010915030602030402060903070b0406022406010f11120705010644160303030c0306030309060f1b11030f03071518140606 71
    0x840d0008001000701454a040480001c1040c03080ba0304540061001080025054002500078404c906901d000c01407840310002d603140d05600320200880054010b906941e0ba41d280002c1540c440e6a402402142d186005000080e81075014540050001d0314039818a2944400301c1d01e0300702e40760082c0c100c962000c6002c2090340c1c6d040010b08074001906111a00005400c4400310b00c3c100d019090314148a40e50741e5000541d0b00c100024120319004038100da4040d140000450816885400140e465500340f10300403c0b8500802c40e40a090024814044281c280c4038050500800c0200700034020501600341703a12003001c04005985404640030311f032102c2c491840c503010342211205808102458104401013010a400c00c010a08690803030416024040c1107007030413980302c89442c2c000e840c412454a0402c040c8400010b0700310f410b8200303404840c6041410710b07070250faa000d100401441c101c42003030110351894150300240c22075a001100074561030400c5d500c40c4011010f2001604403984030508115032 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 536763147 1250 536761897 536761903
    0x10e0d02012d0e070f06021207120c0c03060e100b220e010b12030c0111030f06190506030a05070801050d0f0b181608060106090b07170c0f0c03 63
    0x104814002040701d60598012a007122800381d0150022002544510302c0b1051150030441555106209980d1035a440301840b84510680e8001c0320014851000c4540b0a120180704603114a908400d411110b240344440440b6040104241140c00f0b404403e0008006a01400f880e03a0310480000681800503203000c40e1000c41e50b91464aa2181d282040059802e8550300590302c10940e554101060480a014540b030240c08003201854001c0c42043c611440d00c03c01001508014a125001f4032101d020300e4040240c3c0e000c1580c1582503400c0c0000410454a80b40d41d0618030400020009000155502d000a405400071198520402d44940800c000b440c0d000070801d001d40403c884080d80c007446511020380e4810b10320001032941810030013042d030310809a50030307903420301419003140c01d0070b8031103078116102510512801c00390348a04800030440c5c0780610041c4040c4c840c0f0b5084035003400440d882e0f00603d51415150450220010051040074480a01c2603034100c440d104000c10203c0b1452050501d = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 536764397 1250 536763147 536763163
    0x50303042f0f0301151205010c030213090b19030305030f0604050106020d0302030406150f030b01060306030f03180302120309010815010e010c0512030f16020a080415050c0609010e 79
    0x701180e240d4903102545460141107118040099882107074000d01000420300414a03ca00c4040801c6070000000f240000861001901c070b01c035000034844008541025400e901448080c46560300d601041400701d01e00550121000701d100800c40211103510381c0705400300d0ba030a604141c00081c400010410760105414007141c018805440401036989000e80c002e480c0e03c20000c80d4002c01d500080480d003400541d401c9140f100007046440350340307150f582c070b10b01035000254482150703d04500c00000400c0d40c0240714031011207070810f5034080700c4503850b0380842e04640c071620a03403444800740300c022000d1307103d0f8a041c11262915500444c0e89410f07510024015820040189a0100c516800c406160741d103e141d00019041c00e08140b0703030781c5442d0315200b824210442103900443e0b0b000710030000076400d00c0c25424002d100364020840011202c0034100d885d03580705a009000c15004000400161184424801440ca40d6140c084c0c00c00007800c50380c50518205407000d05181e91038141c403032001c0e08180104a = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 536765647 1250 536764397 536764433
    0x50319200c130222060e01080108122a1b151c020f0d020f09010f080402030607080c0903030c07050312180d03051908100518160512010305030304 64
    0x900c011074000001d109400072041d1000998022450782005400c0c408880f4010003203289a042a94582500400c00d481010b481d40c00510780d00b000013400074010580b0301c00c00c68401c6825240a203070105603d40d5260400700070001c0302c0300d00c290341d01e10103061094440821080d0842500003003004200028400384030b901d404010000c01c44204090940304070500340350b020300700250720b5850b850440e2120380240c08c4800718aa00004401d05031010039030061040c0c2d074007621100121007030400114bd04000860340203400d98004c170003080466000b502003951051001040c5890100b02350003080c01e54000110529155124034410321840c6810f00100c00c0343d11001429a051000c41c102080c039403401102d5840c09078161107070403424503210301e00301c900034488901007030716800b030301d540c0140044000c890032201207100003030200e9649810501c0c0705aa90501c09459016240e08946400143c407540c81c2d03005003c0104191308420f00a041c01c54000d5000300003440c2c80c0e1a05040480f1103d0800a0329 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 536766897 1250 536765647 536765653
    0x90f010605090115030603020603010905011d06030d0c05070b0408100605012606040b150a031a0a061b05121305040605182a0426120705031920 63
    0x1070100707880d0314103524110b0340032140040a16150f040f00760b00800c640c0d0000b94008100000100d81035610342c00c624120ba00205440001d9618040c0c4180d04a0f801d0b240e039541500b11034030b96401c0c28418416015190f001e4400e031183d10303035114280c0c001a805980001c4507604404400488020144940c9001301420300b040005d8502c506009072f82a001401c41c0c0380880d580e8404960103854541c030005041c40054104080c16580400005a940044c1d550400190504618142000462840107051b09015200d60801410800250390b002070117031042d0900a060710f003140116004002602824201c4a51141e8a80004651410106154103c80c0c0142d040071820404c81e01c81c1102e0649c000f140d20901c802944030801030007003981c804181c40801c501c0002442c00810030780c0008100b10f51454060003450080c08107820300c400074440c1c0c8614141c024450086003009804000e01089100304162803a0103000080b00316000d650200c100e000990b01144c0c01219000784803500c00300b10b540001 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 536768147 1250 536766897 536766899
    0x303230c010f060e0709051002030c0a0f0b13020105030a11090d0305030103020102210409050a1b0305150a030b060409050a0f030905271501030b0d052103100608071b0b090f0106 78
    0x1029101c8106e030b200d501d00542c01c40c0b4402d41014420b00648540681c86003d030303221901c0314200f40f500703407403405801c0d14480301d1113010070140301a10090180055060f19018103640d1400d094030010401001c00070509402000300382e82e140c0c1c84040001840740300780c90303141d240d5045000091a0540c40103d1190b040c010040d03102100010760280d804a609078040460306644224104010701802000074507250b24800348884450b07015001382e0f1007400101c04c010ba986904204102400e0114440a00048007180203d0b446062a400040c50103000b401201c60280499031810b090328981d5030141c0000f1300c007550521291400030500448a0140034540c1012180c407141d0007092500581283c51205c2c00e9400c55020780d000c3d802070200003000a1041061401038181281c6030001b082102012014a8040e103c2c5808104252406812070f4815400454185002900c0702d0602030302c244144003440048101c45a8030440d2800e069100303510b4083c5900709510110700e00350b46010301c058940d0620320 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 536769397 1250 536768147 536768161
    0x801110c0c0d03110307050a0311010b0a09020a03020405130c1b03051209070513050a050c07080a2604050109060509030a0e01080a021306050a110a08040303230c010f060e 75
    0x958103801c070604440c180030b1100b240c5015180055401c040040742d01022509005002010034004130f568003c2d01c0340d010000280314124220380741040f0f50b590108042c2c0e414021141d155003d4180e508050070014030302034580f00041e0407001c50010705001c80d130b00e9900c071010b400d600009440fa6140819a1868bd501903079034090b140e07019413541082404980c100160750f9160410100c001010080c10700c9880c0c210840c1640c2c0617150484122000d1800c0034080703103081c031141e01107a403641d400c07001641c10300c41040000ca45040d04050310341c0f49126440311400b02401d20041c4036004c0e034481c000000d00c9041c0380c54490b05503800203002441d5a00203001b4208441d42140510040002c2481c046045584915210f0000c0c050207480500000c0d140001040c02038100c40280018030351521503055001a190b000d41c0e849000c508020f0440c0402c1c0002c2000901880360942890341002d00192800342100241c0c2040d000500703a001a0b0307464111800e000304603440703940041d03c12082c2494042c64007003 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 536770647 1250 536769397 536769403
    0x3060a03080a2c010314010b030f0712020f0703120509070501120f020c0601030b0f04110d0f0f0507050f0d0b1b0c060717010e0f041b030f0c0801110c 66
    0x32201030441040000d0300411280b0441c1100415405400c0503028285020442d801c160424200c40b40400d01d0300c0b94158140c60f983e54014101c2e030f8030030411440c41d520300001c6038502e08050412410b119928425032035802c1a4000f5003160b49945114035120802410010284503403541d080c150240741c041404240c5c4008540304003580d80c03c0c202060032500103002c2d140180388499914601c18404504030b840d100011400a04803030103528411100d40b60550b10f107051510aa500824500c13500c8000041e40c2002e60a83c16600c0c02007450343d82e40c0322a910f5180001c00a02000c03929500300480901c070b9890010510314406000f40c0e602e24160085a0780c1104501d005000e61084500603004a5002100c2408940b44841c007402510b0341400c0018026048204001000070044046c900201701c0c0d03040591054400c100040c0690f0407520380752038030420442d07101100b20444000f5200440418207a00c0e1a10340d041c0b0600c41680790500e0401c0c42401c44150030714000e44100308105600d07280c0400 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 536771897 1250 536770647 536770649
    0xf0203060a031b03080d02030f0903180f01120e01050a1b0210150f0902071716112b11040b0112020309031312052e0905070506220b03060a 61
    0x46900c414188803e00e0800e018800d565200501454000400f01711b20561500a940650a05900202d103a1101c85107107440380200703885036001410b144810310b814900358009459004040c105009044044525807040d0b07201d070740302c00c021a0f4580c01404443c00b01845910000420307407007610115031040c0303c025111911205c10310380813500c4030b02e074a6820b07401171420001480d510716000101c5039070b04030030f2029401240040d21440106081c05c820f20700500704a03901600322680039200f44820382d546076408404000000c3d00001042140c00c0100400c0380c917440c05450485403030801c800689840b440b42030cc01074411780a103060200c61030391640c004883c05c502c00d078208005600c03550cc608100b45503020b0298012500f117501c0800003800b1346a0215200000d008505407007034101d0743c4175150036001000e0b022000c1c41a00002c01030368401d41e0fa228140c668400c00640c0c2c041552000081c060341c201c3c0e01c60080c9400030380242001c03000d100103403500610100c1300700c6056140c1140081c0c41c42200d = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 536773147 1250 536771897 536771903
    0x6060114041a0f070507080709050f0103060c1218020310110316030b031014090114160e10050c06010e0105060405010c11030d030b030c030a0f1101170a0f0f0203060a03 74
    0x2d010030114601c85400c01d80301c424880310b4155450360703060b042070355913203c8500c6454500c0c00b8030f060100d0fa4101d1800740900c500b1040400d100c2a0746160b072070500030040055007100304840c1140c0ca0042c188c02d0b002d05492504606036180c4444103d0040500300041c00302c000c081603207040c45021111507810180d0ba031203440c0382a4070f684d1514100064025240c40c088499140c040c0c10012088402e450f84024a0f050080c2d00d000c1082e91040d00d03280c222400f0b003201107881407980c80010b4108a040e02d458600c00e80c180360100d43c0788030003c0030503694919010540007055002c202200f0082080012600520003919426a154944004203649103e1806000d0401c00c145400304207019001d21202c1010030003800700c4006102d8420700600405048004034030a004a0b0f400202500c2d00041d07039500a0b0b00000d4501322230724a43d4a119180884040c29814440c00340a480b0020001115440c071400780080045040284198440110303260b07160b1208a0510500078807000d80c4550810000b90780c2c0c = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 536774397 1250 536773147 536773169
    0x1051204060507021009030207091107050c0f0103140405060406050907061d010c1401061e0324110a0e0f040603030503130822091406010c081e1b0606011404 69
    0xf581d4030100d0803e0410321500d400b540c10401c2040c1050b9000586900b04c07a0b00c00700c00c00c40256030340d0300c18100344a555406000c0d5880001941050f141010001c504540b050400151483c824180070081c05000c89003901d00c1c0c0c00c0182004188116805004d612030b81c0e5401030404a0b007400000f03440a6003071803800010300c151841d508441c1c3d0242040d861100d80091031482028444501640640683d0207003110311003694101c0e0035400030f04a00c8000340c0e070b41304281c110388001c084d0284540960a91080100f9620b804d0900c00410903900100749808595032104000040321003071207040b8440d4462140a14038060042000c039501c881682d4001c0e200120310001d5051310700341900e01c2d001d20803002110714000f003d41186000c00202c02012280c8080d000d00180700c91a01c844e01494040301c0180c0442d4982c0c4c0b4140c0050b403403200030000003035445421001204100e00d030b040c503030f0000000c0000300c66040c1c0c6140c0131030f4401c003e4076500240910b44120412158102a100380c00b6070f101c0c0340708101d = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 536775647 1250 536774397 536774401
    0x30c030209060c0c011205190f0204241803080403020607051e0a050f0c0d29070903050c03120a12060e0a09120906020c0f01211a010512040605 63
    0x28400c0d0100c4a00e00d00061859407a2410b0040d0152141c4000c80080c1c0841c4d1031811203103001a0500603240700302d0070302150201c08514000c46038040d00780600101d00b915030030400414504d0143d10301d070740e040088510295881c4044440585560035100044554201d0304204200080c00c2a081f20140ca43c190b078156203450a03172030001c5c40d00302e100c0c4019031003015600c5000c0c2d4044000400d205c7c102d00032400c46040c02c004101050326103c80611158015140c6035041c1c0201c1c0410012203450200900e00c0f0b540c248004002e150184e9040e03c0c00070020703454030010810b01000300990a900d80d0f04070083d000c0f024401c0c2c804143c610652182e90107008240d89a41c0e000251940254001c0901280c07821851401404040040581c0c06089804034400c804030b80c4803910440296041e0760480d001400011012810003100d600102059410030500000b40c4030158900c07a41106040380d00c101c08111210344206042c000c000101000e030401c20180500f49440070412046d60700702d9006030300050f0a03 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 536776897 1250 536775647 536775671
    0x80309011b11010e06070b010b0a0224071b050615010905061201090b031e0a03081803033402010c0206010801020a120e190b011a03062206050d06060816050a0603 71
    0x1034014140087d18585405000180c0002c18400920300c085441d82550003204003032004203003c0d141040c03401100102c1c50001500d45018090288031501d16404491064a2641e520f9280030b100b00d808495029a001c020700e0b40c2e50b0429143c0300542401c9402c00c2c1440300011100903500014410044119100c2e001070b000c9807003d00c840186407071524a03c940c100700904403140d86003000f0300d0460020350288001103900750360040c80c2904003050005189980c940b1040c2e400040a90760681036044404156070042c4e020f0401c181211284680020a0361800e00714003900b007441c140d1145820341d0041100004156200ca0000c8130710000c0040094190704041d1082d103044a505420b901d045e54048001040c0300c803006105048890110846141082c44a500d4100b40016100c4075045074044545040c040c450121001098072545000508142c3d20800900e51000841c2e06440c4940e80e03410a0111240900c01c207207014500c0c0c940d50160302d28020224214150900c10300d020542c0d6015034881e0 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 536778147 1250 536776897 536776909
    0x5191a2415040803040f05151b070f0815070513060507050a020612040605060103140406180c0b0a031506020d0c0503041a09010e040e060703090c050a080309011b11010e 74
    0x104440140c00c40d02d40362680718190740d907032041c0121000c10a42460000b82c03440c080101c072108010820285060000d211482d41d83c0c4a4001d071000064003800d235001c1101711007060001d00800041000348400d40c14020700f4040800301622650400c4010486085655218940d0600701c5440e40307089691a60281441c178285115070800a60003c40099a141c0c2070343c0c1035141c4e6005070f00889041080e44c40365401034040b140030808600784410081c0c00500801e4007540408414444240d0f1041c040c0181d07554015901800d41203141002d0703000c42c02e800910360520071607000b404400c40840d4081c2c01c210010395030300e2200001204100045840a007042030134002d40d0300400e034444000030a0f4001d41c210031032136008105820f00117075450250745620301d040d000e90342c0c6130044440a8111a1a00c0350210b020340400c1200b51030032101e4400c00589612401440c800030840d90300a191164501130004180050b07060740148914540d002740c0010403da0880402001000d081c0071500794190404192 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 536779397 1250 536778147 536778169
    0x1809200f06090102031c05100b12010317090d030206090114040213020f0421030807080f0109020c0705090a020a030c0c15320709090e0a0b06030a05191a24 68
    0x224000800e0080154181b1900110b00403400c40b04219801e036200c0c1d1403800903004140100c1c1007500898010408030b600341000a02e455802c207081881c0070421000319105800c40c0100b180140d10090400114034000e01c6004d407600700c1d0880b540e00d40d040580000b02c1c0341c400004035022540d800180d9412051009040320014424075480280c20240e0320841d01301c0052502055020a0244001030903161107000190310507504007504040d0341e420040e8100080d00410380c2c4002512410302c01144a6886030712140c814500500e015907103103800074004080c0c0746080218018440009a10000652000012440c005034401c002454100342186c800844001c980c030008091035000c0311500d0000e400d002544101e4032601d41040080d52841d4980032107014850002c21508120002c0303001851072400a908098001d080f20306550503520f4090411504070403000c0c1c031002e11070100003040002101407411601d05650031f1040e01d070024680141d000b09092002e80b007028502205815690000e5200c = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 536780647 1250 536779397 536779417
    0x61f0e0f0702151504110901080412030f06120c0b030601120e01090210020a1101020c2d2d0609010801090c020703080d0608121e131809200f0609010203 67
    0x30415041c80c2d984409060b134101c1c0902d005a00340703860396440480300000c903031400b04181c1d282100355403140c507411808d00191044c2ea080640311466003030503003130b01e001c1c1c0f401401620740100d0910720286446544410305900114a0410510800107160703000f0350540c22100310904081040705e0880d002c179005159110000b03500880f000c0d21504010350004000451510030001d010550100100680c0d81d250010785c01a40305c2c610080c581b8a06901d20a204642d22000c2c20240305000303840c0c0001d4070031a8141da2345881c0c014100710b04080514040581410480030303035500b45400d94003c002070000d6014080d059031651580c0207030142c68400c00040700110340042c60b4584803460108040c1c00340a880c4502c1803075100d1341603d41e104101e42000c50300139a01c880600c0921614100e15080b2903041f143c41c103442a00c4003240000c5c2240b4030a8422220b003440c0c0d20015a5401914002240701c0303440c02c402a075403040014480c0c20351281100f54040d180f0403101c1d180c5490007440100c7c51441555402c1c = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 536781897 1250 536780647 536780683
    0x414130b090121051b09130b06010c14010f0b030607080c030a02180414070201140906011511010603080a090b03100902090f04020433020309061b030c061f0e0f0702 72
    0x1702080030100182c101c0c51510031110b00b04030391901038509805050020016108940b004003245456005003039082155200d556040d40a45884c0d480d58219055400c41d41d40c401c0c0ca030091140a40340034050f00d940300321907042c06026420004c90070715103408010038a0400caa80020703240b1000500c6081981d070348900a00c24030003c44c400e90042124130050798420059070900ca841030188086031451032045681c100142440c0c0c0c40c00590081076082c0d41d144100f80152050142204a004c2c0102000340d80a001d805550b00300bc10b10040c203c1c0c101e64084940c0309000d0080c82040a00344d510081241c500b404056210392201e8009500040300f0180c5560080c40081c4c001050f990712034140e00c01d0400b2003101e014800300e85000c041c0c020090305d03000c40142c00c00c0004402a1400340b011b03207241c85000791782c0c02c03041010b42002c43c51030f400b440781004903510140c00c00c5101d400e0001801c0f45491021058041185407007214020008080c01c40b0f06003500280c0024451032003042040c00341c8034040c2e00 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 536783147 1250 536781897 536781913
    0x10b090f060d0905061302060706020a030e0303070305070807050315040b01050d14010905011d040311030403060c12110a0203250b070507201819020414130b09012105 73
    0x20700b401400742c040110342500540380020024810410200510b68000e40050b141071f180380e555400035800f9140c40d00034190760701c5100c0300c100400c0020718841c0741240c50029150a15030805881d07180010540c0301048000c008001541e819104800c1142c0815200464250800c80040e11980600e06040c0c000da8588201c0307d0008a440d16001d04030785490b001040142d0300d50036405d4002c9009042e218280500b1004140081c0c815200403d1035402101520305041e00c0340d5406041d074500700d451030002a603081e00f0b841e0800d103500c04d054181c207400d01d140e89024074660b8042e482e4011b4440c2601085100c0700c1d098500b145030150002055805070549226190410015025401031305003650101d4544c0700104420030036014a00228000802c040b61480c003840f40c107840700d44004c16254070041c1e01c40701200c00003943c0c0090005001820410640440030b441401900301132900d80034559824001101c041d5159040c03c2030644034210040800725003000c1c8652020000c010f801070541c030030155 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 536784397 1250 536783147 536783167
    0x601120203100803180a050604050d020d0f0819030b090108060106030f020913022d340303052d07030c2007060e030d120e0a230f060f010b090f06 64
    0xa000c004840c102c40e4222410f44447c1030243c03900a501620b83c0000840c0e09600141ca000b01d420400640315000105120b22aa501c000b41a0030000c8188401c1d04044110407e640d010b006c0e5004901d01a00d46150702d42c5056034141d582c0343c0c18461181850f6480e0304200141825404a03545107801030605800741c000307010034600039400608103020000000003983c401a40400c01c400e001740b50003a02c81d0410286507070079409035103542c910141020a1391a54440041117081d039500a80c081d03100081caa103440360400000d240d07113403a441c40d000c1582500d50800f840003550f180c6c0112880c9000200b41c120450241c441d40368010600024000030000600d40c6400050043d09807410b41c3d54104810418900381550b0b074441c0010500030804585d500746080303c5507800900080148402c850401800307480d544104d16030890b100a001c650b00202c3c0060341000c000d10b410700919003004040300c0c6004680c049900300b0600520052200014100d4215503543c1c3c08280000e17002801c40740d41d412031708 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 536785647 1250 536784397 536784427
    0x60606030604090228121a06010512090f06090109080301120c0b0d052d0609040813060915090501090b0703090b0c030c0d0201020903071a1306120b090601120203100803 74
    0x392035817a580240c1501080055807007405100043c1d2200002200d01c07101d11481c000c03520b00801150401006024564422001c091094010003a10014100101160a00501b07240c0005d002d04c14503070600d07801c000014100c0007182c2c1181e451181401c1c0c1e019844c6000355005d07d555126405205010803000c546021030f0b40a24041c40c4c40c00013505080e90f61001c0801103c038241c0c58140030301110360014000d070510700c0c0c425a0051141c0b00c4103140205108000100201c26041308000851042080c80240500c0d240d5901c2c40c1264100820124079110008004905600810605100c0400c2c2801098040da001e003002e490000495038540441c0c03d40103640c0c0d04104100212307403007220807848140d0b0062088900c112030160142c0310f01402d1408551805610040151a0003c100b2410340c4140320b0000c03240244c10300e90b80d074501104000c0340200c155107562003264421101501401951383c0c01c46076200d02c40c8101b1001607125035415242e8001c818999000c1003040c0400150001089205 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 536786897 1250 536785647 536785699
    0xf0307020f01050f071403130213060305011a03030403020d0302030c0340060507050a172d0904111e0c0f03031026070b03010509060d050606060306040902 68
    0x1100070003d41da610740c4030207070381340c1e06403070030008a0f40788540340c481c0b6420840115885440c41030030348803d10490340410034524003641d07100c45803a610202882080000e005414041141c0540410301a59110011341c80380706900c8000d100d00c1c81c00040d0000c0500a205907004400c80c201600e4a4101c4048145000c490b40c1e120a0406804142079804041910410300240b0403080c400764030b202d080a2055a00d51b0204005840510807603040000140390f0301074a204181110741025142c0700885d8014014000c0c00035449240581c3d130300c1c007541030400a4180c882250b01228003286c188400c1c11b0200b424421892001ca00c000d1802c104c447c02416800100b501054400455500d14a580d00b60780d10780c0002d49410440d486000010801007110032007107800031022032618562107043c1c0000d90324004990340107030040c84000c0010411031a25108566122406951068801c00d603540c0789502e1710b03401400c0b9441980c4c040080384042e103032503100140311507000d440c804403640c10408804a039919 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 536788147 1250 536786897 536786923
    0xa030605151002030a2f01050c0a0806011706130908031e0a02070f080f0c030a11010b0a0303020c090a02040909050312010f2412050103030e1918050603030f030702 72
    0x498103044401c600c0001255500c0b0324a035110000d40c1542d4a41190402e006d49031032030400f4548200c030314010820721640d0f0007980d1030401e856840d42c035000701901071080200140c1c184407a040d0700f1036202d418014221741c1b103d030840b40c0003240d980c202103000007061880d44c00303403200c90003104000e00300100c42c2d40d681c0046180c2c802070321955079415482c01a445080b1004240c100d0003030000e40050319a002034200d01800f0303045c05051041c0154010702d10303044070798110005058003881141602c0280310390311403404c050301c04007561401c64401030342e00c000512416008841207000207072820318980c142d9014080c00a000c0c0b0801001c0d00f80749550b9000b444240440700707118000050130040c010300110031100ca20040180c0303400000000502c3d807007201c42490070700001c4103983c41b03852140e00c9100d002c0d51113904e60b00d00c0c0c64008000e21001021518a80c480065412028030a0b584c5809000307603010010180400d440e50350703c0200e8154094025210010f6201109016440342c0215144580c90b80c = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 536789397 1250 536788147 536788159
    0x15170a0506060901050f0f03011b020a03270605090a03060203070e18060a0e0705120c07211b1a0c1b060c07081b060c031608060f0409020a03060515 65
    0x4a450410182c240f0a201d85540428965420503082c20003110204c901c1100074000200c01c16045005108200d083d04101d00503008800e0003000c0540008040e41d11820160b0f80c0a14800348552803409242a8001d410a2200102c1c0454407540c0d2040701c01c0155510040542d00c0f420a5078018224005204c80c131885449003554041481120104941c45070703000078100301d400c503d010001508001d002e003c1508002c004c03c041400031061072041c42c050194040165515516420b15070742e65440410045110300c50b90703001203900381e1320011508075001411444d895440c8189095068001501d80008040c07658404003e00d08006001801c5c6440c8242c6d003102c80c05403084c054035100c0301e007258035400d140003c4c401c60022651520140141003071601c1ca201400120b241503502e4104200c1c1d00e00b420200010402001564010f51050b00703080c00e00741750030682031900c00200d2100c0b00d81c1c0807500650707a4480200640da0380c4000031008580000d01088a0304206181c00352a812142a540c0121 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 536790647 1250 536789397 536789401
    0x314030c1204330c0c0b1602010e100c110a091a01022b0806062b0b030a051c030b060f04060207050f1c0201032904060803030108030304030315170a0506 67
    0x412802c842c05550440ba1040000c80840c1074040d00ea004c84100107403900303140702401140d900e001d0b00082000211030f40070382200c034110b4400188100c81615a880c066020782c3d012210058010f51460002c60f402244070901066a10102e40894001d40c400d5084c14104007010510110084c048041c0c01c60070780c20360b550010128842d01c01c82c200f490300c140c001c400c81e0b41035a6101c0d11485000c0e0f0840002411740d0702e04502410360050040310307091241d8a2401c00401581e40b81d2240c41900c410079070580280c1f40041ea151200364603003103070211508030b42c9400b211407111503200364410048075800400e840d490308089000c0380320036003050040e903000d17200d000e1022960740b03803e01c640d075907103503005103901400030800344c04041418400030f00324141902d42008412002c900c451020800c101415480c2848032208200000d954180d403101d513140d041080140700804021003141c4d442601400c0c0424050b4400968041551555020903083c00c806040e5100c0d207407000c0f4907110058081c004a41c065 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 536791897 1250 536790647 536790689
    0x41701061a280212121801050c030f0703060b12100e0c12040606080d11010c03060506030402130603020901090212010504020f0a0507030c0b01060302070b070e130b01090b07050c1203070b010314030c1204 89
    0x343c8d8250394900500c1c90074070004d030505494501090780b00f421b03880c0106829a8410105107070780c10400c08005a41c02c90750802c03a2030071106461100070a561004000c0074104032010000310720800b00d210b65403800102c00101441110781007a001000c89404544c038010a200e00101004210000b1440e15401c10041c240d80b5882805101d080d01d90082c003007441d42d12a5420002e0440800d560041e0064a030900040981d03128a43c16000b05150000560340781180c010b03540000e1701c142c00081c800da1040c06540b000200341710a450040c0b00601348160b80e0080c1e400d05643d6001e1214004014038032440c000714a896164000d400081e101d03d080900a482d5910280c640490540c039003504400c0c080760202c0c1002c85038201c2124144107040a407c025241c84825915a118071010f80c1c040e880310f10070300121306003d0040a0180c0c21b180140d0f0902c00703281d9039030801d940c0c180300182683d01150181e0340145814001c640e440e0141c141100c01039410601c02155a800ca031061005440c4100c03014600 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 536793147 1250 536791897 536791901
    0x18030a060b09071d3001241406130f080a03031d0c04050c120a0207020118030b01050918061005030c0a0305070b0f041701061a280212121801 62
    0x10088141340441140d42030302d05108403110340f03503503d40041c40c014003000710740e1203000300500309445500004900100c044c0840c002c3c25001c8a000310701e0001622040042a5004882090f9407404880c02a0b4035085083e69002036001a00326403000c0702820ad0004444200003045544580311381c90900c41042c007030b4544200c90401d01ca02406035080417078044d150307141542c007540e0320811603400300e070501c02c00741010481c21800300d030000000c550000b614000c1d1368004201e02f040980c19940581c00301c2c1103940e622030000040c884c060040a000021032805c43d0703081d03c07010140f50000c2c01c944851900c2c60301300013044c0140c40354a00a020792404002103041c01c5150328103490700400101004d903d0040352010f80d0b07008107007d840103003080c40041040740441d655920300354412000402c029081003000c2000c411202c2542042680030000c1c1c0822204100100c000e2110406018504240040050381002a00b401c400f0600000140c180e0f03580d5109220a40502840c440d0004541514199142 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 536794397 1250 536793147 536793167
    0x3100f050402090f090711010c0203040315022503440c12100f03120207060302041a070201180b040f050607020117040311100c0305061807030218030a060b0907 70
    0x501320418a4041030582400e11482c1d0300000744e403800400040301c1e6500d0900f1941c281d5942001038000003010000e101d68100640342c1001c000204501c1d0945501e51101640d00e050805400e681c0030410490a15000f00004141000302148080b20300c0040107011041301e480010002100c440180b038500b02c400e0401d6810f12582c40503d8813403030508001040c0e8111400104100c0c0050810100402d030310400301070450045101e203103c0011030f214140082c1c02c1c80c0035500403008051040c4400c10110555031031640350350f1070301301d0b03c1d80c0e0b00c41d42c0d400121103460240b07492200305802c03004001115a0000c006000711351007445460100c41e102c1041100c180f0824802034006202400e0100000c001c0b0000d060300240b103030416020fa20303194048542014202c0b8120030260380c0da60100c2c00800d030140617495002c841150610703801d01e206460003510b06070103801e1808041e03001c6405086078807101144000d013600181140e19150130b614200024008043c0c04c1409580c00034040b804da1401001105 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 536795647 1250 536794397 536794399
    0x120912011b0c110301060605090a06172d07050d0b01140301051002070306150e090c1003050606090301150501030c090305060613020d0f05010f0609081f0204050603100f05040209 78
    0x100211508181c11030300d4a210340020f403240340002010804590f0244030351801010b60380c0320b103501c48a0000c00c200103505642e12007030510840d18011025081c03210f8409501c00c031000842d1013000301410214125004205010b660640b800c4144818141c020001d01110312444600f40000e115800c01155440d154039015642d1604c2800140050b2170800d1880420340c0703007841102c0c0116642c6d2502c0090340c2826055000b200340440042c012406220050b07544441341800504404031034501040299a04806540c201542c0c0e00210704075a98000860b4243c0000800a10a02e5003844c450720807501c0d141f140a0210b45010342203010107018003280c804aa41100140c0401c2d540d950920801001c240c039405030b0381e40e08025500740c102240c8100e545d045800c403000501d940c1050042d25140d8240d17001103043c804054020000d103600015002e100c403481180d00c40c03c0c40c00400c5c20394040d02890704104d078031144c003000304061071840480b01c008a580c68100d090801343e89806002c200c3c4280290a = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 536796897 1250 536795647 536795681
    0xa05091c14151501052209050a02180111160902030915060a0e0901021b0f0705010e0a06110a080c1510050f0d020d12030f0f0b010806120f12091201 65
    0x1945940c004280c03100e2090f041c10300030303d4400340d9016440e600381485142d248208440c8002e01a40010348030b90f40d4445807240707045207002556203c0810300d014290741141000503080b4400388100043c8004589141e80c000f880c0095911000300001941040320590541c2c4201401c00000d60f000401c420b003c1e200103442c0c0c001207410721941072040280145503400d150b4007088050010002001562021a15100070701099081000e003c2d0501c03142d50302980c100b128500520360f45981c1d4032015011078440d400c1c481c04202010f5411400c044035060040d00310480400c04c404659000700b14541586801e00e00803070140e0f10010019008407107809903a40200403c00041214204040c44401f5903000401c0c80c89910519991810702d68469211840081d488900b07030651390f469800394400600c1c0745202841065801c60000b06241c2004008034440e21081c03550302142003080c015000c05940c000265031690020401581d0300d503001d4003249000e03210701140c1610845061080c01101010b10b242 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 536798147 1250 536796897 536796901
    0x609030318150509282102060f09150307080408030702030c07151205040b04110105070b0f0414011517030c0f0606180f0103080a05091c1415 62
    0x4858404445402035604246000040b840d0a160341508200700c0700c95031507030b94640300c0c802404010184143c00700d121028000d480f620340d070340822080f400d171a045a00d8103155540d422100c46410780810001c2e41000000403046149201e4030014031580c50b06540c001e03007c0c4d203106120070040c4402c440c40740001e40e10704080380008800300000c68101600744120307030500c02c2145103181019010380c0811076981010598071142a00304003904543c26480b84200010310341621802d07416030000304000e02c031100c42c0701d10031350581c011011340c1c980c00e402007002199480c154950004100081d0750a5a41070947c40e5810000070050040d28207a50708181800760841c030700250030010307104603008088607000a005440c0402d404001100c000307a60000100b140d410554180001001070a00250f00c5681d0729040185900c4480032050440f03034481c101c245e0741c031500b4204a0b6540903481800b0792010f00900700c00341c100c0c0302500040c0c40ca4013840030b1880003401d41c2d821613030311031441c0f030810711404103840 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 536799397 1250 536798147 536798153
    0x303080c130308030a060e01080d0212030a15030f0506060402031522140117030c1207030302070f05101d0d05090310050907060311120604020714101a0901060903 71
    0x4040c020365160040c0700d1181e0754a81da90311542d60070460741054881c0d9100c4007000440c5005902900404100024047c12211610b00070745a007038141c41c3c440840000000710b6035220345a0310500ba5030010400c418512901d904d400608040380e020113403018820a00812003910342403080306d02a8010000a00080408000703101114241c1403080c2c128603500b4249841107071560040e044100724140c00c0c0225503041c680090300000c0c0c9a4041800c0e54030030f110780d01c500800002c482402c070860840c00f548a101a18048020384a0044010680c10610401c9010801c00159040303440600c6d400a02034004001c950403000d484403c0358040c25031007000340d41e55a038001c50090120300c401600f41c51421035280c52300001d803081520700b100c25034020b80c42000300e01d41c18424690495141d83d07803d46088041d0750241444400540554801c3d0307800035910082003144000c0d102c58141c050300b500d5000f100780d00f22070700400300c00030b000107290401c41200800749000b45445051311000d8032164001411a1 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 536800647 1250 536799397 536799421
    0x51032010f170702100e030c120403121103040914160c05100b030c0d03090608070807080a05060402071401050105130b09072a2103051005120c130204050910030308 72
    0xba040300301354040d41c00b4041003d500381c017602000f840107000455503220f0f402c801500c2c003481c140c0b083c41c0c44541480244001003a00074102c0281c0e40e9490882c1c000800d00100d5410742c41254401d00c00346281003800025108908825413242d075888084411a1001910503152902c00f088020000d4004500c4150360071015404010044409402c4541028034000407034568a039074882076000c40c40c00e55040060341c1c3c4c0000035603840031880c40d1400712824078900180002501401d2080100e0302c1d0070000d46d6586959044e5212030343c01140c0705007103045c40c1d81003038004c2c01c0030b02640380500c0e403880300707078994100b60700a00c0341e0082c02400c44600e960321078400f2103c08581e41000e00d1861903010f082009180384640b000e044900031041c125000e60710600605021800c148800c1c00d060500e0104802052403c034024100c1d1020740d40d82d43e42504c0031884504220072040d2459002d1912904840400250360203041941c1095401c1b20251b02c03440440d280c42217403444024000340d03140b00000d198031800303 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 536801897 1250 536800647 536800651
    0x70f1e03021212040803031b12060f0f030a0c0501020105090c0a0b0f220503010b040506011b02040627180510020d09060204030b04021021051032010f17 67
    0x20b002580c504840c1240f600285900a601100c855400402803211038148040900e044a01c4e14144a1a280a00050822500c8000d010310301c215080e030014174003500c80703003051400c9103401019100f40c800c080c42c200b0021080703801501c2c019031034900000d06455000800d103d8020008140500d924030f040c040b00c040d80e01028514401f020309002400054284000403208079080c03050000c07684e800d05083c1401c584800c0d64041c42141400180450b5903041002111508000c40210001240600100d4040e14240c1d100b10890b402d1610160302085525450350041520000e003880782c44804e51100e44884141c0c0e40190403500001000c09400740d1507401410120320400b400301e510002601c407501241c01640c41a04c000b1480340c1000301310310302100d0180b14102141030000e4660200d01010030341800795207012070081e50b00c2c0c01007107205200c408007074000c001c10b20440d401c40700500034041204c944403035940c92a58140c0b40c000010f6020b24800601884140e968034080c005c805401e8004c8040 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 536803147 1250 536801897 536801929
    0xe0108120d06082a041a060c01090b01060207061101050103080316020703050a12080f011a07030c2a0f060e0105070312110c120c030a05031f08070f1e0302 68
    0x6200c2e800581003406015800c0a91943c07a0010401d202488814400c2c108006070544281d1400da0a0038000003031190311901441c003910b69940751140540468010140e54001811003034107103000060303140c1c2c001501010388455544405505104001d9103098440a0000600680d01440050700c01061031400300d1003070b441e6104440505035252281d504052440c0300c283c800e118030f000804041c03038000da00c16030046040c4d1591090741d0314020b00709540d114540c4e01880403075000204a01030511600c621701c803582e00500c908601a00010003c00012a0488044450303280d11070000745007004240324004482254680980802c1c1c80c40044902d540302000481c280101c02c055450006003900c2021810425028190b6440c9400c5d11000d107405002810000038043c10402c3d00841c02000c000d507240e101081c10182c0d100d4440095405420b403641c4424402080c21340000a00d08400061140c02c550a1010b940001c5860f071108080c4426000c0900805804480c0108014248482e520f249600 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 536804397 1250 536803147 536803151
    0x1614060f04030303020a080c09031002030c12100e2d06060f0a0e010e150403020409050a051f0b010305010b031306060510050903010b01090513022a06100e0108120d 72
    0x90044050903490300035030000d40c00a070b80414801c2e407894002041c560804e00c28034040d414121b4540c0000c0c3c5d250f548594603c003141d008004a038801c0003842c00d81e41842440108a1010700e04004418100c80345449201002d4441a02040c240984800d1304c2110362899030340380c040425640003614a880c00a0080c035005a010400e6030101410400640000c61440c0d40e06c0d85200c04031400181084c05000240f4840c803da1803d102d4440b50700303c100d508983e4103071008900c40b240707810b100e42420000c0601a000d400303600107100202c510710144222040d5205402c0001140140044017259803d0240c5552500d0400c086101a6901ca07490342c00c0c64030448011404070381750800308449a600403000c0c40070a40200316903640d86028010b03035844640c01e18001c29510700d04400270740d80c0210840110b003032950010350000c034080801420010000002c6120706503020401e0180e540c0d003170403182d450100c1c02408006c240300000950660403184e100c0020300c0740154109500c0110307400683d0580b0010707 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 536805647 1250 536804397 536804407
    0x3010509040602181f0e37050a08030403140a030e0d140f0a260f13030204180515090607030c033e0a02100c0210051f0602161406 57
    0x1d80c0e040d4070305d6110036116611111a0058040250103a1142c0c424203201c0c158207001c0c042003040c4014406c080b003642589600c240d10300041c0071004160701c0d410082d004046c104002c540040008001c0c8110380c8914005007501d0b2050000c0d9491b80d500c500024009039520031a0300151800c0c0e98001c811038000c00581d03441c080b410110600d010b07c282c2e48040950011106d0300c1c24802c03990300b000d2180e40b81010b15100c42815040035801e031300c2281c1c0d081c00707010303400700301b1480c031441c02d910300006980c4c040c0041040c03a01c1e4030b0075400d44841201c001c80b014890b03150f8034001000a04c0c0b00b50b0140081308018400d0b51540002940035040600301c0600301542c0b021503000040302006504c480e13140181140017000d10000583d0b000850841c0002c60100041140d03101d0035a0024001e9030f5114040c00000e98181040070417420003409050500e401400d02c0c0c240500002c41c0200c64616892104850181c9a540d1400b03986896000d81409400f0b080200300308400c01c040c2d65150700040340200302d24504 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 536806897 1250 536805647 536805649
    0x7150b12010c08180f07031e080c0615011b0303050604090203030417071d0105010815030a2a050a030807081605060105011403061f111209040c050301050904060218 72
    0x5810490000000650007010b0140d2642c80040011460403980042c1c0b11703207605c41400c2aa82e012503c4000c200700c804610300041d82503503512914409600079244e503901d907003120029503101c0c07081e540c2046213020b01408803202d40c040c030340350f206a9403c44841509040070751015402800003c0145800075201c0303440c200140d60500c020700291541139507402e2400c1900074050724040c03480d003040c1c01c0400d1800c0714a040348025684241120401d03e80092103541b28105124080c41d2400c030f080d0103100d030000c42010810005101c00d24111581000240c011041703420002003070451255a400150b0410b00f0f0010a014400030700c8614004c9042030310300001000b131801449500701341590b031034010a0051040e90380c0140e0034008203020305081c9080d42881800a4089520008a1541c482c485064050745a0081c0740204640840405846580c54900f405011592004010a100e249083c1c15049500d0251042d40d058510203006901c80e80e41e00d90307803400254030218001c07840c0b01c1d5602d180506 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 536808147 1250 536806897 536806901
    0x50406030804180b0102030403120527041505010f030e03191d030114060607020d230609060c0703110304030606030807020414160c1704031b060507150b1201 69
    0xe512480c1803594803031804210214014003000d0b501500c40c1080c81c410702507a4008103440c10f6907000484d003603c540004070300352203a100726405640032b108002c00c4220104c4001a26800c1c031f40f01503074103005402194004106c0310b285030084078081024023001c201c00a110354859242c59564401712481d240952142c0002d8080e40049403000038401c00014108035030100030031000302416802480501000c0006201d0104001c0046000700c0c004540d0206559a013010030b0760440e00100441d06060b00034156203042840390b11074007194803030800425940500007505a21915100c140c00f42007110603074013164002040c46000209100500010006c0380c101c3c403c00c00110f125412560351142244180000e8541080c18556004034007810010200c1d45400d2006e142314503841c01c10010f6003e8502494209401069a04800f10106000c01040091180000d80400c004c0510400d550340c0c801c2150b2a03c0f502a004061100c2c903440b41d4540034040d00a9000507200038654400c004401e0704141c2 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 536809397 1250 536808147 536808149
    0xb1f0212040e09100501030809010c061409060a0e0f03041a040b0d230403120b0303040905042006390a03030c032003040f051504050c030d030e0c1306050406 69
    0x403506a0b103000b400340d44182006000614012000240219807454a4a100900540784002d061115271696041040309550204603c0c0c0400203c40510341442c444141c0d4440007281c031018000d2401840101b840400a41810902c0391500110324040c2010400340341c3da900400001001a004c1c44042403664002e0043c00c442000311800292840a821010b0b9003000c6e00c0c40d111806645034412701c00420ba00201008011030340640100e400d12601c404240b641c400e46d030090300001d1400040c00f0400c01e0a04c2c00c40e10150121007081c0e0301d0440042080f0702480780740e104042040a42410311140b0103c40701c0c80c1000040204a02442444038008078104000304100720002540c2e110004001c0790180f140030000710084c0c01c241c0d42c02500400716001c83c80040c002900c2140c0410840040290401108000001e000d02c00c641d11700b018907000d41c1c3c488000940c04d1190003009003400e5064400d218240302c0c10700c4d000040010420080501c00e62240c2d05407918074040d00c40001055a40301d50180740 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 536810647 1250 536809397 536809409
    0x506040e0709020702030703170a1e05190909061e0801110d0c0c0f08030f010f1a03040f08070b09010f020906090d020a03060c11010b0334120b190b1f021204 69
    0x22b682c0c551813100200494501c10740f410a500154803501000caa0000c19250340341680080d507681c11311035a0095807200384940c44415010706000e008181103401d600c919100313280c2518a442d64a44400c1040c0c240c5807070302a5416014418401e44500701380c190081c2d0040e00c50740c01c00d0304401299881d0140512140b001c1503404040000510440c0f100d85c180a41c01002100d001c000400c0c1450303001000c01507402c501243c451400b001080502220b0804c0000740f0b41e020040660340c120b42d280c40e0406507000c5610080a51030461341c0380c0450382500848200200003080e4910b000306c80c00c10804800390300310b81070b0f8120f8519540800003940d40d1003180721024460700c4120040b111400c43c2ea09485800d90310318001c0d00180301042c0001c00d110081000b1240060544107070340d450350703482c959480246d400080e02038108240c3c50700707005229070304a00429100251182e80c4030302030390140655004020080c2c105400b000c003070f94071441030201400e0091042c41643c50a4040104640c1c242e00940c0102c = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 536811897 1250 536810647 536810693
    0x6080d080a0b0a230d05070b0a020106080d030b09010f0b1b0f060a0501171507050c030f0f090f062b02090a09150509010311060f07020301050405100506040e0709020702030703 77
    0x42403204113001c1c6002101a04941004c40c1805654a40351150060310541402e4100407c503070121600030741004000e080c0030000c4800c040744d1800f0003405030a60b40c19960160405400100b08065003441207400c0e02c0074258000d15085840d60032901410010310020010b000701c080e0b041402c41c00380403480c0541991070000c2400c1d41401d60804031560520091512507003c0220b20764240c1d0010720065212070135003003140e12440c42c0302c00c0c41d06520905140541e0b0340000903142c9856100c42002e0902070000f80c409100c40008002400558810011007040350324582c0c810b402c903040000d0803a007094030300c26001360030400d90001140034103005402540100e41c1341e0002e02d041480d01800440184070884050440d545140c4607100c6401200c10414000c0600103504409884180c040703d84050780980200700c1490700f414601e803140f4002c44410902414440828070910302030041100d4000250090300501d4500079510340250302c1680200c1c4c02d40101f180000c082a0096600b2a10200c440c0380d0f = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 536813147 1250 536811897 536811929
    0x309081b1e1e0a1401021c1e0804030314010b070b06030313090906231803070b0a0203100605090109091e1401032d0201080a1e0207051006080d080a0b0a 67
    0x40061071812030700244008502100c614229030307030004187d280d04048084003460902d0700f110481e0058045404401d010000700241201640e212043c94402da000744c0e410400c201840030030f481e0056003132044045200d814805a00400c400d03402d816004100107045a1618865000c040c0e4280c1440d4006102160b036103a90006104085c0222010a8905030810004c250258502080c0d24009000c502004803040c40203004010304100b114507031500003241030030740d1030050030300c1c4041d600443c0d08440d0301c003100c07400280c000d0003903080d038400c900140c4038a064241806070200c02002022180300003074950481501440040b445165803910341074a410013a0741c11818500c0d4801102c038a9030108c01040740c1c618100c00755600950407101c0d42440c0c004081d0311452440f401500c81d040d0b81d6141c0070314584036551030043c203600500b50503100d4000d0300c2e000c0f40d46805610440343d00c1d200700012900030059010286105031191075015040000006100c03031750308c0c00710300ca041c1a42c21600c00b5191781c0d54 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 536814397 1250 536813147 536813149
    0x6090605030f010605010c151e02180a050303030a020901050712020d0f0c0503030402040b06130806010f09050121030216060e040501090b010906260906040309081b1e1e 74
    0x440303222081e640d0302c0280089890480020414000010094030f46286280d190602e42c10903007007981c10580418141e41041c0ba0041c1c907500035030126080d01542005802001c00340c1c205031208504070b80c1c008001c0c41c1160750b401d100d42c0195201802c0d071b07810020304120362b00000700310a0a506603017070994000d003035031015814080e084080c15400181800200326000700010400000c40e41d100740d05450214041949402295040c0111224500804c0e080310f8003241d00040000c642d0304070307100801c0c5400b60958030524207003280c41c28041c0203042c0c46c0c40400c186440c2007a180341c0d12401e21910481c1e0320721203204d401540caa881900320b88001001b0003d4010320b841c0ca80503580c0541004c01f03007000300104080001c1c000c00c4542c840d15003400022a15000d00071035083d0560022201c40030301e41c0c41c0d881c003024400e840c0c0f0700c201c4040f8082804030001090112001841000f051920700f502070b080155002004003001d0004030601c010010400000f11544800241203540c800c0348000304200d1075800 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 536815647 1250 536814397 536814403
    0x30201060503060907060f05071a0402091503030904090206041a2805070b041e0809040c09030201090e09160e060f0f010e04050405070801060b120f0c04060f120609060503 75
    0x303071181d0312950080c018405031316000300d00344040315501e0400c010000700030340d41640d603406603c401400700e5442860200300c69660820641c0b0851007240c071036500e41d44142080305030058085a185e01039009110a1529082c15070041c8030040c001040141480c2d95030b014801440701ca00c00b804030307511022403550a5040c10007242c20700000400c990580081030144001c00034054843d000e401800040081814420a040c1d030380751034404050740d8121000c507820903160310340c003403080c050140307203030a0904803810702c6007111500f560703070596818003080d160103d020034210300581040543d00580c803410004600b98a0048000d00c4c1d0104103605501e00b4004000c0400d1142510500172080c0c0061034129a0f44501a0943c14808640c0080c0716201e50802d03070300c0d0402a40103180550b00e01040400c0d0800820050004c09019041d180b207903995441441d0581d0400744c50840c5402d03800c2c041840603d019110350342d00816035280c4015510360f200d40c0f002c16550140e0001c4c80703865844400740580c2c1000c0c = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 536816897 1250 536815647 536815649
    0x60903070b0903040b070b060f0a1202030705180c030a14011403210a03020706090501060b1b0f060106031a031204081213030f020102031c0516020105160807022803020106 75
    0x4400078505043c03900c14170009520500000401c030b40c00c5c0400088840d65440041c89031504060300c3d21a05a803070386c800c4040940403800507486885054400100e915120314158103540500c2d0624290f512941c40c2d55409070000350625a01c03980300c1ca0b240c4041c107007165026009000009401c0d083c404003105250420380d00402500246203411a51a8036900c01c008491040312640b0b0016982c0c00c039800c181d0000d0000350030082141d400c141c000502d170880b050107800d4442034136024203010807400d00c64960790880d8100300012074000030300400c48607000381e01c05045411100a581040c44c1c101d00001d0402010242c040785070800400c003400305000820240e06c2082c11000410b00c0d02c1140141610007a16a01c4000c18109214410000f164401e00030b0700c0599544403032000d1070340a450120006800119203100d00c24092440300e0103050310502400f40640c942c0704002d200b50314107080c110340003100100360304150f00c9104500d11540700500c08a80741001401c000e48804562458000d00350740c52 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 536818147 1250 536816897 536816911
    0x141603020309060105150d060b03011401051c09020d1505070f0e010243050102160506120c130801050f01090501030308070309170c01020d06080d141b060903070b 71
    0xc1402080300080c0000390090543d1004c5407400042048484140480d10a0011003141c25050407000074030040044085c60696994103032401082c0d800c0c0c0011946400b6906492029a1000d002c02075482c00a1740100b000381e001070007a80c03440320705880303200701120f4424060980c5030b5248100000c1c2a0f108045010b00031107882d03d0a01110400d000079641c84910742080705d48220030380c9540f00809100c0c290664100b1414144c0c1030760003410400040d9403481e1042074003501503442c1d2901200ba02c030a140d42a03550060495042ca0f4a007880104800802081c4036000c01040081c4240400c050040500800b4840d0002c5054580a1480520030906900000b22641841e0042c030009800100c9103a01151307919002984401c207013070140da09031441d0340c9031100c00400a126508d001e41034004000700313a08050180111507a03540103a503241c0001c521200041e03044a4454120803c0d03800616080341452800c0700e0151100701c1981c104079044d9000b00d0b8030341c000100d0b0001c000c0d05981c81540002 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 536819397 1250 536818147 536818151
    0x240e011214030d0e0f10020406050301140307050303040f230d03080a060504141806090c040f020c060106050304050706020601060206070305070c14061b090a0302040b0112141603 78
    0x1140400d200030a801848000342055000303106800349a004000343c07200c038441c01e441071004c4960029420b84a16040b080741c0e400f8041c440000311075030100d000f250300316050350380c8062850780f8220168440c600081040e0394180210706e00061540e50400103040076000100a00d514245020800c602515413400c002c07100f0444442d4540691b9070f20190210403d805041c03005660b41c8600c0024000c2101d604059841841c10616194501c111100a40704900140950860101d02410700707958130342c01c540408465000b415070480500f01504041100c65035505c016003041c1489221600303100c000d8000e00c0000348080208801d114041290300020100c600150440e5410864009d446039001040d00d0706040d1200041100c2602c60340141070059048105828001c00202483e5150b0f01d0617078030700d00750700c2000f0030002190129008464685400074080a0741c10300d15404c0c070016142d1100300c2c0c0c0c103201965865803050701171405441c49446000351250500d1904240e4411000020f0403000c1c100340c = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 536820647 1250 536819397 536819399
    0x8090a08070b030705071e120f030b0a14060d0f0b0f12030f030c1603171e04022713060501060806060d0e0c03030a180605090a1505070204240e01 64
    0x3042040f80d810059501e05140e580342503003030240c00100020300d405c12400c905400101440b549090003011054196903400034050ba0450131003d079103085035100c3e03200024402c00c220080d43e0055081d14000301030700581c14291203940780401c60310700341e0720304803e0354072070808281303500c0c010b401041800c40032076406000010901c0019543c1c020820200ca0049000011494907681c64003a01c0018140441c91002903d0900c0c0041441c56980050b081d428940400b1422081c040c6900d0400c80351104c400004030b075150740030402c010340c2020807141000c440543d040055030b0311601d158494400074485d492040d002c1e2810b10100d504c1680400b04101850050010503a030f01c2007141d9003582c030391030045258404d000c4002d0400340c030070110350707032610002405a040d0b50b001485255400316102a5800c5070380c1c0c6103800c1c1c2d0140300d106021903210844a0050040402003c0c80d001c0d101c02d18540f0904107040c80d03012134112608866440e20b6040300c1c3d0184c01104940c0b686130300107044814a026100c0d = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 536821897 1250 536820647 536820659
    0xd2331030b0c03040519030201150b0309120f0c06040f03080f010f06050c07050604090b0a050d0201080c130e0408040e0601020c0112020f070b041b151b08070f08090a0807 75
    0x210000e002e002c1001000004a801d00c08208000c008440d00d14420100c0c600f0b19160290007013402c41c10b10781c03400c006190001201003103401030724841e0211001900800c13418960722174a5620021240006c02014000c14800e02d03c00c0010601c00c920414880c2070524841c1800341418100603c40303003950300030f180103000505403808136000712001810301c3c0b40c407a1484c3c4411800c10075140c00c0550000004640050b410b8810740080c2c401c04419206208105c1c3c950062108a1180140280c042040306001c00e0510070b034180188502047c9400510601c4d403101083c802e6001c09480a640d181d10120f800e0020360003119034203811100034001815080c045500103000c1003034408a5519880c0c2c00b06010424046400807221225441703041302d00c3c3c52800d850243c030075080b55007030b444507280b4072000400c65011558544115440a45810805010b94156600c42d115a00011117216600b44895400204000101c0c0d0049200d03203242038844ca0100184008208258001040b540c005c120400031 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 536823147 1250 536821897 536821913
    0x31409010621030c14010209131b08180d0f0e090601360807090e0d08011202011403180d02071214010b0616031b050d233103 55
    0x19410880e403480c0901825003010b0f5a07040b1200e5025041341c41c040360f610040b40047d4010321882d4000c0b00e071080c0080107c03409108503a40303200e503280e000c000307a0f50941d140307402110a19840380d020b021908444160b03419060402c0600c1c603950020400344919428595080b07001c900c0b00e45000d070340314403841c541400020328440400900d81700005410031072040380050748501703604006050070781d410300c240d071a0036007950344c7c2043c856607580c6c600d40411040040c1010130f9013a801c6529645940c9280d00b440e44140ba10b1001140481c1801400d10440001655050146104e0618040e0940ca42c1410b82da42904092080b010754045402801c41885504c90300004224940c3d04080e50355401e80c0e004908900511856010b99408000442c44040915800320711030904c074400d0761480201003890005810082e0050001405604000000404107126040b500c244922401c4400200002c403000505a9400003c3c0440b4407070b4158000000310306030448610700c80c101c40030000e141502e5510f403080c1c = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 536824397 1250 536823147 536823179
    0x1b0b07020d06051009112a07170118030c02030601090e2814160902040f090213170304061b02090f07110304091a180a1104150314090106 60
    0x2002c2c41d50381002c10b005440d4040e004001d0201901c00300708005c4407100882c12600201c40100075140c00c0320300b0229070309500148030400020840180b81c00da08041012092403483c1c83c1a1800b99643c80366210000800449000401c1c040c2d22078400b201d07120b0050500301007058009108507030520202c0d0141010008500552001040c0f070b056416003000c080c7c070707041d15001c0c001a1900c030980e44d920074030500209058030300c00140c0d09100d0415584402000690160348940b900f100300000c8208884202030700100032461010450b840040d40384e01088141e400100340103c0c43e42d00100303080c400142c001c2540b41c00351404035040f42d04080c6640c00a140c0300f400425000260900e20040b0784414020402e042120b0241c00c01c1e292641d40f240388a00040486822154510008002c4000b50303080040c100c070401d41000700041402e94a801c9400043d203450050003802c5030081000094501f1100111013281001d5980840c803000000114011180c01805150b00350740b400d4000c02c040c02450b03065071 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 536825647 1250 536824397 536824403
    0x150b031806060306060609030a020904080901120c1211090a03050705030c0901030b150102190b040b070e030601061b060e030702010306060521060d0812070f090303051804060f031b0b07020d 83
    0x247d44407e60781c0424180908040000d410452040074030003081411006085050003e036100490904404407030400e4a000000c0d42e80412512000445140c660350080f0a00840100c0c2940c078001c89007002c81c06508460f0300a0301c464024080c20b00440c074007804024070b10381c1c084812110700c1d419070315806030101d0041c1c800011420f1600c028042079000b07200c60211940d000031601d100051905003006283e50840d01254050160b20025103080c0c0542c00c802405440a8001c06083e030130060f09644201500ba0300b1345840d0401d0f148500010304501404403c3d8426801440e12240d4610001d02510303660b0300080306006080c40f07101d0b100410300710440070700420100c03032302119201c031404111544101c82c0003412501c0f00261034181900156416401140140d903108914614288226148145404000d000450030003101c8407107400800c00d50b2100c0c1c00148006030603540c030310f4000f03420030144d481100c8820091003d5a48444400c03e0000107116444606c0e03c1c10040e50300050a081c0180001 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 536826897 1250 536825647 536825659
    0x204060f05030c040c09030c0611152202040b03030703200303010308120703020717131707030f0203070b0c1b01030207020105030c21190b06070c1206150b03180606030606 75
    0xc294106c1c41402034030b0065030011a814002600c460340240010720214010f02e23148501a200700740303415a10076440c400c0c0308405420000e04103c01c440e11181c40321b44001d1ba4060b031240c0e030041540d40c05200611041c0d220b074445a049610f5000c0b144902d05000402c0c50721a00240300400100e03044104544492451400b0740440d9500d015042d4002e0003040802b6020303050720021610b4482c41c500081c1040ea886414522a40d5512100d51603081000703210444180c000c0602000010074031101500a0791004080c0c40c410341d1610318910b40c1ea00940382540242d03202304210210303c4401140350021603c00c1c83c0542c60401742c2e400203001480050700c01804a140080c2c594a200c00381403100d064400000c4118106040000b40e1000f2034403001c0d225500c1c203150040799105854003200b1a0300007a8001c0386155101d1610100c1e03c48030404403030560350759481e00c8052882c0300b141c0c81c160010b030150660b041c5e202d04040f00d92030101901005c6290841d0302890520070555000070711a640b00008940c4 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 536828147 1250 536826897 536826911
    0x3070509040f150e0604030c1a010609271a0a06020304030206040b0c01291309020d0602031e13030e01020d202503060b09010303050304020906010512130204060f05030c04 75
    0x18080040c0030f00c0420301005d001e84000d10007003550017100300740888c0c00b80e03446000d101c40c100178070380900c0400c0c85003c0100c0d440000c20000c19144a0502540020003050085054004400e82003a00c11650894030781a07000c0119000d01c1ca807401c1071102030f00c0d0501c000c506040c15a80855024892340c0500450190003142c6000914025003001103808a09000320340c0c0d10010308140135030702000b01a1a0300c074488002c501011103d1a1189002d4550001c0041804180c642c80b268000d50000d04a0125181d40480601c0140c0000700e03042d000f000300b030310a50300700741c014103000b810414000ba200d030454108031461024142e200002600d008420728400081c455810b007442d103401c1c132059400f580001c0621814912014040802e000c0340c1c058207041c04110040000c01403416024000100401d000b44081800350400b41c540d180c0c809010705000303192596240c0220080d21048564081038849076174210300318185800340b400104190091403000714101000207403101c800e454518002c55030703090 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 536829397 1250 536828147 536828183
    0x150301150f27170a030905032803020c09010f094727010f08030d02032701050415060602122d0d06120201090902030603010e1b03070509040f 62
    0x9092802094140f8250703c406000e519050745905100c0d0b029404074441007030020704c5081c049490710965078034080d00d0208210306543c0c1c0300c540710242000e070214072400c4100d42c510345510a146010704500c2100384d00c1180340c00391500070345203600600100c036010310a000061007a030503100724020b03030031281d214514032420400c949003c1410640d982d114050f14980710384808500f40441c500000a0200c401c0c980e20751480e802000d6081c480c031002a031080045d5031036403655a000d15088000351030103c0750000c20702ca600a006100c504a00c0060355514140300400c00412a0100000c24411080c0452460706c4bd000e501c840c0c0032581c032181440c000a000300c080001e46800602c168403030340d6016950f50320518888013a00b1429071a20303058500320b40807070301c0c007940640e04c2174030743d4160b4803000c80a040c0174000340079402c003620440d007664840550124074138040c40300c0f40d00c21a008514405010943c0201b514200059110034080c0503c28280004510980030327000202ea00560b000160150140c = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 536830647 1250 536829397 536829467
    0x171b010507060504030e09130311060103170a030b03010f0e0d0e0618040f020c010506011206150311130320091e07260106080939150301150f 62
    0x224060303000e403140c1d0420008e100c5608108490314040e50b00e407034408140e100700e0382d0703911000e00010300241c980821500c02e04e01a50010440c412261901084003d5100c01290a4a010303a01407e100c0385c41e200036290104007080110072025462030516038150080300400c890313200380b02855480265401a01e0710036140ca0b001b08100244000c0b04641e80c0c241220100c1c006c01c0140c07046070000f601202d600c0b440000714002c0c1d01c29603034512000c6a171004480c106400070100341400d41107a0205100e401100030004200d800114054141c008944055441400218076003101c40d5100c0c0300c070034060090b80320320241200c160f80b19600f02c80e0841d888000e003e03580030381c0e0002d8498045035540704440e0401c003d681420704a607100c1d11509aa80c03151045561924404010041600d0034244514086c11112103c104507050803900c00640d00010408242c01e001840c9081000050000c01000080c1648003032101c01d03107283c42c040c40703041000c030401040042c4800c902180300840c0b00742800c80040302 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 536831897 1250 536830647 536830667
    0x7020a06080c1303050309010e01020a050d0318050a0b191401050622060203040504050a0b09040f0201090f08011b050c03120613050405160603060513020c07080304171b01050706050403 81
    0x11003e00c50045580c0e00d8180d58903070003506620f0014202903500b00e541e500008100780816031040103000c204442c038400300c006006ca0a5071104640d0459141404903000b408410180c50166003184a603141060647d000595408000000685455030311800c000b1200c1040e0706480045940310b0703035071100c1501480c50707456400201d10130740c186150000322950000028001c50700291010f2055a5440b0751002c01c440ca10003019402140c404002400103d01803080900d00344141000c1880c2620350043d200200f20b503030000703400d0742e5413a00502050b403000300a81d03800344d4017031500030f1420209015641e180c0c0030384030b249442da12044020541b6592054550a071000b0ba01c01c00300850f1401e1b040103607403070070302c6426a001c00258400c00701d4080d20900a4800f50f0380090800c20038100705180341d50084d8050791481d14580600c42d400304803444203000910081451040903002100c28280c0070b820030003242035000701c3c024804030044085c0d0f00321041d81c41d015008a0300013034a680d6802c05885141030 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 536833147 1250 536831897 536831917
    0x20f06160e0303280807081005060901031512050609062203110a0809040506030d050f09040e0d02150907060c020d0302030c070303031b03091106090307030c06120f0207020a06080c 79
    0x4903210a1101e1200304100034140c0e00c01c1c1c5c2c0c032003416071140faa0035110842d0070b6a90400b103000c1c10405120604000005140c02079040c540020341c80d0100070b9580b0b01e400716401906a140200f103105040c45000c001076a0011300c00b00240c1040d0408c001c00e60340b00c8082e030b0079120724501154440d906250143c582400c02a4070b1005540d101061840d121200b41c0c410300c4ca40d0320540c9010082580c0e4140061140600e0009855940c80c1c140008031205c503a402c2000910ba100d62180511554000240700c100034000f12500104a0300c210328541c03074860a001080e80c800b55101600c03c00000e540801d81040b20307901a40c1881e07496905040072411441100892a10307403084940c00000c05605501400c2d2240308000c1505085c44140c4046080d102c8000000e0710310a02005401c4492604500500b11102d000f03080300c000316500c4e0356464034002d00f40d0000001c100d50750000ba003900505d00400070440c0e048001149403050a074001a82c40342d05019150800440e440010742084c1d00e001111100c0c01 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 536834397 1250 536833147 536833177
    0x50c16051606050c0d14120c19020c030a0201081302031b09130f03140403060e1608010b06120a0e0a0506061c0b040b040606080102310b040e060d12030c020f06160e0303 74
    0x1510581d0000c9544c09408202c1041032910a200007d902c046054bc0010348010f0140c8502c24003a0011a000c903009040b03000c400c940c209501c001a07a0401007688084910002c00e0210b00d204c40410070302030070040c21062003da042c0d00d090700003100303c0048011240d1509001c0725846000110b010780b4025038000900051078030302224005640080c0000da05055425540845a02d90494500341c60b690844c00703420000c24000a149038400c46041f80c0d02014041e0001600d4603040c20700361400c0d80d016020703101034010406201180c03e00368501c104a00f45047d41d02c24103059540c4017a41043d00410140000198901140400c201c035003060b4008d000c0c0400030b540754003400d0f09940400c1c12500c540c801010762142d03154011001103a5010440e0f504420072420326141c21030000203118003d004030780c40038009000d400015400709503040030040a035400100d150401201070300c0d080500c0e20050b0079a202100300505110070440c40031050300b032071501d030924500c440302017840d5008407102d00700006 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 536835647 1250 536834397 536834401
    0x30c120108010914011109060d24030b01082121070e0316080d0c06090b040803092a1e09070807080a021c050c16051606050c0d1412 58
    0x801500400f030203a001d41415800b034030a0b808028201d403036000c0c1190300c3d9201817010041e540b0303000d0081c1c200aa15064089820201001c01c80000ba4800c1055407101d41d1601c0d05000340300c144480103014051882c010311a04440400c1c01d2403201491402d140010390001d00600c40e20303140c113004003421140404502d100d0a00c0c16015164078445540b040c0244070700c81c0e002c0c083c000c074840d51104690921016009a00826000300c8410543c600306403195a100c1c2c42810005101112a44c8510301802001d61a411300c510703030f80c0c1840c107402410307948100641c2c86e43c1a0214140c5084400d203400301c5400a400740180507203025a8010820664030441c070b541000189600041c046100b2800340c3d417400120f54801d0314a804038000c400c0b07503480f51801c2e004041e9280010341d00c029088500d1344c80341c2c0e08203c0e038810401000e81040b1000c90b8143c0000b05071440c803003d0114034030098641c5041031402d20403030300312890307aa00111400c10f0401480303000c007030151400382e0200c810310080081010064 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 536836897 1250 536835647 536835659
    0x180604030305061008040b0f070c0510020304020a270b03100e0a0203010e071a0708120405010603051b01170402210102041e030807030f120f0609050c0c06040305030c1201 75
    0x10002280c3d000c0c001c0c6144006500315034400c00c43d451040f81d1040511045840c0c84c0d030240803428000301240240310a203c15507010a2041048500040038101d0150742d900e454418000c0c00130b0241e11848803201d25048258400c00142150081c17460341c002c001485c8201c200029284ca542480c400750030074a401c0041d096040d0100c0c40440f101d00a40c020712448042200103952140107100348180040c20181002111101d840100129406500c6036400d00e05004251140782000381e03000c5401341c0d510b271010410442c0c14010942040c3d0201d940c00090180e92001030001070b0300c1c8505805010082d40080c00315981c80f100c980711080b90110441490303c4812055000350303c5400380c0f03155940d90040400400803207642e03180581e03500202050420b200c6a41c2030b1050130503840c041c401d10108140d1440080482c1c440e6085a850400010414a20700561001100d2000c0d1a07038003040c0041003407098606c00002e00c540c2042d0325150050b42c0b66203580c0640218007442038a240c500e10548000205 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 536838147 1250 536836897 536836901
    0x225021c030801051507020102120c0109061d0d02011e0209030a1a0a0e1b040c020703021005070303050c040b04030318030b04150b030f060117030d0c1e110a0602031806040303 77
    0x182c0380251030005d40f07050784038648802d0b40a2428000d00683c419002c40404c1d81c0e540c1d016110350788d0483c0c00800c2d003c606d99500001d03074a280d4070050b51000000160134803c00c0030401d130328811a00340000c10010600d080350740100046c1d4a840c0301e09a40005d92805141c42c00c00c03c900201c0d0b0484005416040351003201c05103440c05580702e50b42241010040743c2403800c00f0845100c4c119210303801a100c0f208800a000c041c0c4100184141135016840b00000903840708446001c5407102d130341e20b10381c3c3e40099183c00b80850f0000740951031389403403d0005100242907202101d042c0c03034060508489c02513060403104001401604020a01d51490092008102100600300700c0b000c2466828030040c41c0a42c141035039820200101010b5521540040013880c8005610010081442c0f040c0c03885c1000780c100c80000da810084224000a044050141d40525000030b0202407002c01d280040c003c0301c1040c1890b0b500c2c140910081e020780e07800008601c00c020041580c0c1c800c12204c0341540d40b02d117807074100580 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 536839397 1250 536838147 536838149
    0xc07030c0603061d061c110901090c320309030f0d1505030c2805030109050c0319080a051305040e0d0206010609241107030b0412030225021c030801 65
    0x10982000030a86444d28502c8100b40d84a0007025001c0350020a502d5003888080022800a07541e0862403080c1d0510f03525081441c502a0641d9030004c2a00e0107006e1004104803000c010314105108403198410719480b04a1100320145032010b5003a490b61201900d041c110720401da0700ba000c00318002003080980400390080740300d00405042020f101503030780c01410b84410100e44c000381d01c481c2c0d0b1049600d841d0036480030090961450f4844400058644d400700782100d84180b0240c555601c0035a1501c81c615003041b01f401c2400c0258003845012a403503660076214040c3d40c040d84240040030864404150b131014000d4024240100107000240408511a440742c018049080050268200108042d03000300008401c035481110850407040c0070240c101d600c181c102000c40204801944500314040d030802c003a0026500902e0b118016042629080b4040149070f00f01c0824180140501410400e110b40204002420a03e044196403030701e1000410442c079000c1015008140345442c04141544082c6043c = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 536840647 1250 536839397 536839409
    0x6090f011a0907030f020c2e020f160201170a090c0602010209150702130608031305091005040518060109020405090108030403080a051605030f37050c07030c060306 72
    0x4201c0341686100903081200419078210b524200415a507138400e9010310340e0b04640301c2006040244403c452400c1940221500d041001c05107192034000385030380541320302d04400c07440451401c2e140c8818600540100000f40045103d802c4401c2d0a40e4050a250030030300d440d404031b0302c441d8502841a07200400805a01b03503a1503010310340100d1181d00510841d4849070b801802907600c00d049038101d4071503902000c4100e801c4903843d0400d40c100d42060142c41e000d00350440280d616510005440c40300e1a00640c0410310551120050040d8034100b1000b580c169401528040f8080d50344941d9036903185070b01007030914075110350000014915215405070080c0c8a04645c039410713603641c0c0c11900340d5901841c0405007220070b0820800b600e00d40110018001515541c0d114103103000d5907204d0502319005045601100007001a0951280d030098294414084404031404c00d8440345118078501e2001e801c4c2641c040c080300084d024801d00c0c08202d14002103901c4449044a65182c4100602070002c5100c0c0d0 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 536841897 1250 536840647 536840651
    0x308030a150b1206011103040b0703140403030e15070b190b18100b03040b0a022d0405040b1903020f03010209041b14030705031512060403020a0312060b1b01060806090f01 75
    0x130400541c400c41c1c03c414901001d1000351304150408007680d41d641c8c0b101208038140146810803441d28400c59020340021402501d4541c00e00200005005403402e600058001102041050000194412180d00e800008441d5081c40707005403c100d5100405214031055401040c11645070800307501c0300155031140140b0a0382540352541e581c2280110b000995005140102c110002440185507602030721601009000780b4105a8000c0c0200c24501101c01c40303504816000278080c010b504207800f42c0e14800070140e0341d00124240280004015110a0100034441c51031840110b000d50f400b501a02d52801000b4070400208518041145034403060403c0c1d1808030354203042040d100b83d82c0d42e09407031050005d0f0b01d90381e10315a580000024041064425242e00c4a5540d012010048040001030b100f103200390002c2c038000c83c1504016107040c950b100c1c080c200f00d04203c0180b01000c801c1e03041c0c40c3c0600e85016203d01e0491a03450b402e0240107240c20001c154440c410812400e004000380d4008040f00a0b002 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 536843147 1250 536841897 536841901
    0xf35090c0303040303020a0807020a030b0906010305010b0a060f0e06091207030209090d08070305090a081b0708120d0b040b0d0c240905060307030e0d020c01090b130308030a150b12 79
    0x140342e00c03030165100103000760300020100808100484001c21005100600110307095460fa0340761041d28900b95048036032a40300368014000c005092069100c282022140032161a01e44000100414001400380d0700300b0981c4040150140c0f40c900230b817202048010400c2c20242506950150303204042c0c841648aa5500740210305500000b02b40340156900d01d0343d0b03890640d5200141034016050141ca400006c1c880ca02e10500854101d5015251105d0718446100c100c44101d07d101e40781036056001900c07990000a10742840f25984030456400c0307802d9501c04160b410000c4000303801016858221908100381c058050308101740f41c240e19003983c05101190036002c070207171014580d894825140c2008200070322028405850f00e2030145900025a180200c5c0101680050034106110111144091783c00490b54810642c1c00c411000040c0c01100030403820726418420b000c100c00060320001e00a410000042002c0c410141c1090803e80f2500f6800c5a9555803000303011050b90024100400c00d014000c0 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 536844397 1250 536843147 536843149
    0x10618020a181a07080d110403021011062a040807030b0c12010501030b030309130605212508060c13120209040b07050d141e070f35090c 60
    0x10324501665050b0503021a800c4106003292aa640002c009445030b031402d101d00d103c1813003140111f03410b0742400144162500d10b148140321104400b490501c052120402d40c407514140002001c07548040c1c0a20000c04203440454000786298400b030000307491250010f40850040800150f8000316841500894000d44c3c41d00300c159180e024000340f844030031070890010001980b103500048442e0000400f540d14048101001a480c0b0011000e00040151142c50030001c500d856284241c13410040070040c1c0030110440c1d0015192040407940d1800610003881000113400850410b1016280b50011a0791908280744143c0d03003a041010311040540c4082804140c8070101910015520307805004040991580d179241e20604600034001801c100c0b05019003a403418050144209010b00d0b070245090341d0501c68024480013010b413418001c3c1c0c80d420424008010b44c00303189000c02c2c4455181c08002c01400d1842d200c02c18101d0a0a803001d40c0707a024800c0c45a00241c0060350003200b10b0f100700d4103501c0003d0 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 536845647 1250 536844397 536844437
    0x90f1b0807080a1b0b180103050604020c072d0308040812070302030d0c03020f1c1116240f0b120c0f06070204060e0108030304030201050601171305010618020a 70
    0x402401c50b1500711000390702c0000c8000044280d80301c004411003021030346861840c5d100d80c000c502142c105814540c4801aa0b503014030690380c0004064405500d00468910110b984112a01c80c9131200b1002da203039821407080350407040b0000030290850481e6280e481c184107004d90428010301c80b080c0070304466501400c00103070841c0d24240d8182c01a50800d1001c0100308018040e0310b81e0b0809158003000001056441c0320002d00707244c00c0c84140d01040d1500d95081504543c2c0e0030f10050a00c840802680e114140c1c2c000200c000242e0140c80280c800341c000c504d0460710b0030794041c0c2004440c1000840303008290b00e9000100702440546800e40c00700802d4040c2c0d90f03114240f08101e030f00680d1261081d0700c54280b040040081900150000c907202c4d55500300c4034a20380c401d900400154001106102c00c042d820b0280076000f070350034038101c48034810010300c404003d00054102800070700c10200d15400c2082c290071a4006105550092503200c40104c420400f0354410039001000401d40b6103407a1031441e6032 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 536846897 1250 536845647 536845649
    0x10c02030c0c030d12240906090b0402130b030c071208150904082d0d1d0c030304060f030f1b021e030304060213030605010f150503040201080c0a03090f1b0807 70
    0x90352161104003150301c10700010a080400b000c0210440c4180100d010020041000241001f840000d0740c1d625081c805000c4445080c1c80300c0c410b42c01044240c401713855096042d005d4072060110396a480d200c03102110810302c15004000c10880e0492544569a900030303950610400d08030f01c456241d0142501040b003960011100241111000d10071080700c02c0f0250a12403501c002410351b05902d00c50b0006a031450b03045030303a0a04035a03441e4a4018000840d070310100d059011090028403400d509030300040d4803400380d4003602c81006511a02190001e210ba0000e030712407075400c4400c024060f41c0b91400c0030000c038001c000e140544901c0c6000321295181d15070104014000d24061411506e071a40c1d008081d42c441960000300c1e81281c4004004141980300f6a4000c0a110603640034047c54251140030032401807400b20240b0400788100000b503600301c008183c1c0a43c088859550f2207180c0802900140200480904000303503a04100e002c200992021103503410398103371100c0c6042e540703003462030343c581403 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 536848147 1250 536846897 536846923
    0x1006030b090a0b0a0314010b0f011403070c06110c0a02041b080408031017060103021309021c050115180e010516030e0102040909050102090135040212010c02030c0c03 73
    0x10306001425081440e032120300f000304000c0c42c000600340e0f41e840b40400842180d0044111b659184076805503460400d08605940200303080040d2103600142340002e81c2d00000344a402400f0500d494030003000216444070030003c58544241c0e490b00031030081c980c2d07522050481240114030f4011904040c4014004a500c1744102d41c1e90b1540a9441784e0b5003441d9600b0280c402403112641401c007245d0030401a2003914648020002840d09625500400480341c4207200f40b990300901c0c0c007400c1ea000d178588110840c8040060754130390345000c03071519160b4010003907112000000c2c01355020105103410f54049180c40540501400c0c030600031120b041d1400c0720340c00c0d070b80c034803005068158454905019800030702d11403842c0e100050916076140070000588004d60011101a54001410085581c00c9555407600020000242000b0b090050340e540c03101020088914114040030000380840d558109440503000004001b4491010344c48000b82d40e80d04040c1c030280090290380c030035020340d060002e0032607101e1207 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 536849397 1250 536848147 536848159
    0xd02130f050604091802030d021501150e010f0207080129090c03040b180706110d0f0801060c080409090812010801110904051e16090801050c090f010c14061006030b 72
    0x1310b005546070003032600c0300c24417101c25845042240960750034404001c1d20701080d00544180d014064203421403000503000492982088140704001582c0411481ca030f0300800e0030012106a0005016403405006602002e50b0350309040e008450f0f601e189440c08a030b1403610103d80e813900d559004121540000f00d80f9030075038030010720020b00402d400101c0300760040c1c0000c0034140599806106503050803002e8005c0c1011030108031400010b42c0080080b1045c14545107005106461410001040003506201310400c002103183c8000500c12070600f01c50040c06000c000300110122454885090703000600d6403d05000307200000503943d0410701801203190b0448440c0c03850312224034108001808085c0c081001c04000300d1420b00c0e14603141003818015180c04888182031964000c1c010120003068214403043d0341410b00344070032898400c00f9a031900c1002c4400d59034000604004a880184184001d041c070705c40003080030415400480c3c0c46001d600040e0340900c11940324407069080d503c5003111143c000d8 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 536850647 1250 536849397 536849399
    0x501020c03150c0f1b03120c090f091008031201031106030702030904020313060e0a1214030c220b09041107111306091d06010e0103020a030305031b0d02130f050604 72
    0x5003140140607a94095138064200620095550603205c14051030300101e610004040301d440c03103191103007588002c15429640c6001c859202203034401d2090b03000280121480070101c0c00403104503200801903e10f072011651a01003480d031000001500b8807003911904200c2c8801d40c801d09000b4202d81c0b06002d142c00541c50101c0401c00e01000394401810106003803824940d081c002041400b451030b40c0d00c80301008010014081c1001e0054000d1151490144641e041ea000308100005042d03e5204201259242e1954030010b5502184111440074007070110720848080b8900e5400d8000d40555882030310108078040e8044880a20f51180100181103545e02caa00b5003c9413800c4030035080009240e00c804105141c1d00c100030029a118003001010b14410114000c80390134080042030f004007102103022406500d942c001c520014070a010140400000000050244007100300d0b106510a4140040b55201c030440018030003034100c0028030505484c11100015881c00302141c00d01a110010031080c03502e = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 536851897 1250 536850647 536850661
    0x3050316030201021312060f0b0f0d080c0d1121091c020901260d17090a0c0609060e0108070e0d0201020a020613150201021809190e070501020c0315 65
    0x940d01101159020800384024001e41da50f6000146108484000c0d4112030f407801c03509440001b04526065031034544d480d9101e5891921500602c0b2041d15a50495401810840784602c200c0d400d9160742c1c81400740101d0300c039078031a040c0380e101d003041402d54076100403581c0e803150340c0075600c60340711000e807002d104603480c92800050340c1c0c1c401d00312030070540700c01442c59022900d0400241e02481071504107884085507042d4460360200c1040d9464080c2c1104020b03c000a0320710f001105084080408080c001139481408219140409811582d040030040e179031000144100b505001d200300240c80e0a80c0f500080d4000c80b1b005002e107078140c4984100c900300005210444070003160590442c0b081560007405070f1903c10003003080802260381040010300340b6042100d1750602251030740440e0710400c481486010301000040120300221134000058542060510050001c0070381c0c1d0214078a8001c1a40940380d00003940310442e802a02501c1074000316004140c0c039a0107081001c80907203c850002581 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 536853147 1250 536851897 536851927
    0x30515161e05211905040b0a09020a03060e03031009090c0611010b1e010e03030f0d0b0103061d06190605190c17070b06060903030d09050c13060f050901030503 70
    0x515040e40b40040c02e00c1961a1840c424901e07120740b00c1d40c8445908103004035800a241c409807500c140310070511031030501c0d664202030003000800c4030017111b03560040c0c1400c640c0d13070000440c0110303080b280c1400a2401c40400750b0300d950084e0340000d50503810040001d00c090740c5026000c205030b040040492900e18107402610744400741050400303203550b00c1c114842c00c3e50b60007400d42500e9a82050034001c0d000e965001418001c01e108941e0300c00e07032052000c80101d40f148030444921a10b007541c0131603110515801030340640380380d8212891000f40c01e80304041a2520300f070002e01c103800490b10f0110040c0d900810301c2c0400d50602803074000400401a0f9111004802032001860016181408420881c1e403a04ca106018207003480c081d043c1c0001348201401811103056400441c102d40c5145071904210019560348280c07009150b0740303929241c280092203024003084400c55409001444042c0e00000d11100904d01c5000f00050303002e8401c40407409080491401e17050300c0e030160045107000384041700c00301 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 536854397 1250 536853147 536853197
    0x20f0d060204090e0a0219120609060b060708120c0a050921030c0a0c05010f0e19050a0f050103051617040f02040207060615020a05101509050103051516 67
    0x94465000c001c0024a407140d0310450700300b0b1130f454002e400d046580c0d204024003504030800902e84030b55845070a021a2402400031380d003442e07102000140c921540e01e059409000505040b690148c00415003600340441c050082c0048141004000c0f0319a8030040380f80124024405508001441032020042d00d003099024210030b00b010b0700614103589203444000d865a40242060401ca400c0782007404200507084800c00040e05003400c0c40025072240c0000105440d0207140d4882c0700380c030a6124207410300c03035200f100f501410014011075025500d44c4c565070104000c0e8403030540000d01e02000100d604851217012003144100c1c1e48c1e842006242041e03550700c04500036100307803444c01e000d440380c0006960742d100500301c140c8108000b040c024504a9500141c0f940340d404003055400c10590007001400200d402d0f5500f6821840004080d820005440510400d940000311821318110001c4144a4001034041120b881030720400602d94840c40e5008003183c1541619001c2030b1081251501026030954800c = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 536855647 1250 536854397 536854403
    0x30f230c03120a0c1815030f0e0f070f450f0603020906301009051b0a0f231e030618031801091212090e0103020f0d 51
    0x3400c26402c002500200c1600b6100d180002d65201c3e00100015000031000400300c042c82d1112960341c0c5444280800c10560048500401d0355582040c0030310185603000520540c0c9501c1180c0d0751080140580303558005600501541248140d00060fa0111001c061005c40b80340c100e940e240c42d001c1003080b036820b080c00c000116100c0f000300d03003101003040c00307204004491108100100f0030500c0c40c014041081001742203a802010098600c00c003043c0e83c200c007e103030903c1241300003e0300c51a0044141c14400030949144d079803800c0c100b640050040c0000c0042c0c030286003015580d464200e003420480980854030891603040342c1c000d010000300d91200d40c010f0000c05142c03202c00c00162880d000802c16004400a0074180e00e059100c00c04034141000719a034442da1008000c1b02c4624002c45440e500d005d600301b4488002d014200c8684964891210380c0003c142e100c41000c8010389500e00120f6040c850052900000c1000c40c002404140c0c840300a0b040765000f41200200052003001e00c01003031020002a = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 536856897 1250 536855647 536855653
    0x4030210050705030d1b090b072a03150f021c0b0303041205010c08010e10120c0e07020303150d080d02180a06030c02010b03070e06011b050106060903030f230c 70
    0x1c103c041c0b0041440752118040042c034050040c64405c000c1c00a0f2402e4410060885010710030b14040604540f01a83c00c8401184411000051120485c0061418541c6024010400001c202100031540e6914004141c18000210f0070280c990490003010060001d5149072084904880c400340e10510f070141c80a015a0b14007511032140c0c841d29910302c4030848150390f54101c0d07014429805560310b07003d010740400407501c6050001c001100d0030b680f40200b88248400500c403008105c41546403a00400072505444003520300010007035201c0d04101c07000800780003403581e100c480340707010501d072200303aa0720800c2c90b402c0c0200720b04000000d4014140e02821101c24016608141da118480139000304040d40d40070a085034040e80083c2919000c00415000c0d5105034001d0204a0b022a140d650000c402c0c40c058000c0300a0900240c90800e40c0080584554688032003c41e08030b60002d0300c030b4146d0b4002d80307411426101d4201c044814816000c0e400701c1613200c10703a00b4150320f001c183c020071300240d1150031 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 536858147 1250 536856897 536856907
    0x30207080d0905091014040e1513120c03140307030b0d06050a15050a09051b04030317010803120a020306062206080c0a12021c150810110403021005 65
    0x2114a460107190005000c605642401c00c49440c11441c0aa88500035459031505689400e20820302c0e800111340180c411a21042c1c0d1000080c4200030203162400f0b6005015810b0410746269000003110142c291000c0c90818150b0b000e0b18000e00080c01619819603071741e0300014042144a40a0300003a03c4203041544901039a8110355036038003001d00040c0074600015580c10070f1070b481e0f011281c060030f5011000d10800c00c100580eaa8507042c0e070b01210041d800c003040c9581c4034203002928a00204007072102c3c8174040780c0070040c15400300c41003c07801000410b41c012a6282c01c03000b640ca000b9012405801035541c0300066a050443d0051500a44064a02800c000150307480c40b4030750303e4001e110340d000c0d0304801040002e82c0c1d02045103a0001e4100e030380755251040301d4030010401803a1110405000c0d400050b04d250100c0713882c540e00241d01000c0d00c100501043c2220442040025202d111001d2140c04c01000c2050690f2007641c44e1100301c03280f46480e10340355a081c48416000030b1503000a000003404 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 536859397 1250 536858147 536858159
    0x40513050d09091503030c020405060f0901080606090121110f030114091002090a0311151204060b030c0a0e0402060c16030302160605070b06030106180c11010e030403020904030207 79
    0x2203525201185a222030220b103080c2002c19003151414120561080f0024400b0404030750480300c21a141901a2030114203279440001044464102e007103031a800c2000720000082400d40400da4901841c800c9982c81141d90384d402900345d074070b2100342507601d0b401c030048142070004440e1a17038054110400b0701642c403c000c2c1c21000034210b031142d502185800400108001c0c0d05a030a111202200f80d04006c218280f248041c0403401c0c070061400700419440c0001d0721005640da40c010200c10401d21030030607654800c4171240d001600c1c1c0094800b01e5000c1d0401404841625010a061007241005440740340564980245026441c101030416600302908200155080e2010700c80c90700394181444900803407500d585070080c6002e003903d45441142e01200780a104490f403203400c640342d0700d07004801c00d149a140c10000900428190740311045010b00005420300c01d9040c3e402c00c01c101030032500e82c1355035900d010444c1030036a800010403e01365041002b06000500c4c0039202260424080e204a91300b0b40e40b541c07 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 536860647 1250 536859397 536859403
    0x50c030604021813090203070506120c0a0519030b091b09010302070609020301050106090f060f02060f04061415040609090b061018060509131401030204020a0c020a0b04050406080f0c04051305 84
    0x12880f514005e03201c141c510258103003000324400030081030710034614060301205024070600001c0d0021049410004240c0c81c0240b140043e01c4162130030804400c80e82d1013595001e001415517031181800356001340c1c00106219250313003d2801d5000307004626468204144011070003076001450885410341d0f00c210f110302580b003d10402e40641203e0300ea4112840c2080750881d04200c02d944601c04000500103074054540e400300380d140d084071190b44800c11179143e910b049406001110351716907018840030104002421140301000b2805000e9504014254440e0b1416094881c0c82c1c03405090180c031600407171034030300700041c09010f4904075203031180096508440e403001140d12980320740d00003540418005284d15100301f0b0290801c0f2081010051300820ba00c2c484100d400511020744103560106081d01c03c04d0040000c0a01d090b801018a52159202d000b072241980250195074004c500d0904081680342d000104071503440d420740002c0440306000010030024107401040307440c0c61032030b050410300050420 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 536861897 1250 536860647 536860669
    0x4030b040c03020306160203090405040f080d1a040606270b0f03070815010c030c02120102040e0405070503030301060503040f0503040b0a05190807050403030c110a080708010e01050c0306040218 85
    0x4858010207203145004051030040003520442c002c0910041c1d04164580000c1100c0420106a40c00f08440e80e450034061402d40400d640a422500000343d080501005540142c00fa840c0d070050002c00403241e0000c4c481110818000ea00c040703004640d5014201c0c0541c51884586040d1a60400700d030f6446080e0701c0401d03006982c22000407d404024010307082d03001044650300100403100c01595030f9015000a2154504103806402d02c60f007001030801b9034a81c00c091241c000389000080d940c035981d0380c50180c000d1500303c409179128003a005001ca20780c134001c01200e0480f00300b5a5150708548441d11091034020409004030f40b544010040015405500c80c0030b401c1414040e103c0baa100c03480c1140070110b181800c1030201c00c00a8104c01c001c91143c000065800f03690700351800240b01912450541c90450031540003d41c0030b807440c00300003505c0030000386080c2515140c1c0b00074088001d00c0c0140c903003a504240c80300c1d040d406c414000600d881c1860b601030220b604d14034661490101c12980883d400c0e03041 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 536863147 1250 536861897 536861903
    0x310030219090b0409080901121b170f0c090111150a06090b120706050904020d05010e100b030c041502150c030603071d040201031d030a0201020d0c08190c0504030b04 73
    0x1980808115801c480d100315022443c050b070b0300340300f80c41c10707070b69844010703c100d0f540d8074180a03400184401c8081c0592205643c84250b500035103e5030306100010381650902c800700001c503010030001400034030304110f00d20701400e16882014280b165903001500c43c0700d04903040000314414881240341214848523414040c403a007980002d88241012071000a903140242820b0203031a002c0903c00c510480020298119410361400d16107a040000009000e4450001207080803400c00300041044032003c842c40f40200e0503002c14030f030856542d40000701c280c0012201c810702c50fa018441040100c0110008480854092041d42d140702c4820686d80311042d0151000c2c00e150002000f045464101001360b500500200e9404a6014200c0910018030035801040203042689580d8130003032417480c00312111495260501602d03125082c5240c001e00135007200740c601c240d00d0b0500030030354025030107030600500036030401e5a40d460207000909500701602880300c1007030402c9420400000030071080054a1b0281384 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 536864397 1250 536863147 536863189
    0x3061c0c0b0d0b01020307121d06070812060d11210105071e11030405120a050604030804120305010305150705160303021c0b1804030309120c0501150b070803100302 72
    0x38140b449202226581d00b038803070540d4420880c02002ca410119941154511454a84280000000c103d62840d0b24884000e40250000c030f0300300204191180034200c0200c407044540082d075034036410000b01800d158000303403240715080341120240c1840000740f4424040d18010700a020748244234282141c000300c81800010b00c2d541c200447c00d080003410407810003003038500320041c4100440142c0d2240b1541c4502d0b0300c2101e0303400c143c0000701020f000300e000701038001c0113032542c91606003800b91848e08200d808a5040c40b01b10b02ca45c101c80c2c001d1040034140d9412100400c403100c12440c4d4400b0745034014084100744002802031200d040c2100e12005a081e00c01c3e54003503111450141101d00c65480d844840400c10f0600c00a0011078032070388680800442100808a6507450b1414140e006019118000e001090410403900740d4541240c615400c8d03a10940080044001d1002c01483c00b2280b401070724030551381001382c0b0010072800805150041061300780800000e030307250b0004010341d801c01381155031b4030 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 536865647 1250 536864397 536864407
    0x507020a03110a05030321060d1a07090803070309030f030e04060f030b0c0a140a03020c0105011d06010c03211b200102040609030807060f0f06141503061c0c0b 70
    0x410490f5006004201c180c2c02581041803040402070300c0b11000c4542d402c034041e558000f41c0d150380c1d40c1820101c2640c010341c20301c500c2e20f4070051043e1035201c00c451441c041110720b1000500580300200b2200da0b590142d442d03100c4203003555503e03c0f0354480c801d400d40402801018600c52070b43c0b0b0b48180070092600d901219200751440c40c01c2e01e50310030024100c40d410138050010f802c65036017280c699104c40b0220700116641d428001c2c0154028010040e084402e503207071000110b80e200c4400e1708420f55030705800a02c0c5081e40c1d0600111829107101200030f00260300c000014840350303030045030a04101360a081c080b444d51414a8a0a64a40704a500751f0018107025440a0011407c000802401c820003009514007801c1110240c03000f9850301c0000c20103000010403100b40720940d8400d2608000440301400000b0351f002e45000075020b903004145c030101024030f002c1c00602d0f2084040d042d210501c03030b1f1507042d41e64090406c004140e048100d040c3c1440811015070001d10300800a80c02703001c180c101c1540307078 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 536866897 1250 536865647 536865649
    0xa150c020108270123060d02061315020d11030306010e01110f0a051b090114010503100806091b01170118090206030c22120b06130c050403020415050607060c0507020a0311 75
    0x15a41c2c40005c10b10084000c0c0c1408480d89800c00071154a980503500a9030310b00d11080300f141204001d0f800714038415441242c3e001062790100e403d4200c0102917403202e00081947c0c10840c1c5031321060341d034240400d00d007240180b8254001c03412031036044e500b4029140404c0895000f20709003000858101d605810800f134540e0000c03480a041e200d03441c401c2e601d0301107640c100060080c00048541c0802d061040200003c0e90019103100c111014000c40401d0b5249414035012495a48488284450034150720034212011940700e1442c1c410340741280351008149900e0600340a04041625000e1100c19498502d00405a16007200460052042040c0c45076103250760240400d030140310100320082409620820030101e0134142110610f02d42103540b50800e0344a03500011000e070107100c526a802400d0400c240c00490b0803501030000c490003510184114280c08150106001c018062183e02541c2070181901055044e409000d480380ea5003805840c1c01170540000b56041c115500803281c01040c140c0c16401 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 536868147 1250 536866897 536866931
    0x60201051015020604060207110d1a07050307090302010c02030a0206120406200703031d120a020705030f1f0b04020d021c1b14040506070302010b0a150c0201082701 72
    0x41c44541c1c1c00c1c0d41d01da000c80c1e0b0000d407a92000383c4082d0841e5004141c05082c001445280b00310310a005102115926941c90598111603076214039441c2c001c100350005940500460403a03100d44e44541e903091086003580e005590a24180c7c02c11307a0184901d540c6003006031280030040c08540c55031181c01c249480c140c94608190f031256102e042041400e01074070b00071458641c0079150f00c203a040c01c1c040b4044429412101c075800e42c03182140454032905035001c030711301200c0c001004103030703d19401d94002d02d1710380d01810b5481c03904075541c00d00c680c0701e2001c052400940c0320304078103007090b1080c01050040070b520003c1e00307a8200700b1120340d550303034000340d800707035100c0e03509229031100000d0041480320b94080d9441c0f180401603800041c040c0038445140c0c4000f204014200da01030240202500d450300001d00b4001d008080b011200c5000304404800031421842d1040400c00050301135613000d03101c0000c1d42c0115080a0040c24200e01e0540310000d00400354242d00810300d02211010000a1460b841100485 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 536869397 1250 536868147 536868149
    0x14060c0c070b1c18120f0e0f03120a1b20010206041a1315050601081003120513050d0f020102070b040e160c050706020c01121a2101060602010510 64
    0x1640300d004000e43c41d0390390781c10190884000d20004001036007041101d40500ca03120161401024502082c094801654002c1754a010109295540702a991241400d21030503214200c0381d2980f66011100001ca8200d076103005158200140c41c1c410800f0f50300b6881c0c9101000c3c95542122107007030300120840100080244120100403d200909641c00d0030b8407400121958a08540c0900c62400f000900200b6120041d524289d840521a0400c04071554040020b010680e51140003c0110b804146158000c051010030b407500200c0c68140d088181030142d480d580043c0b0b482c0481140b2080008d81b940d40e82c0c01d4000744500842e0b2003c0c90300c00320f02c002030900e09075400421190009000a000845620800540c000d0011004141c00301c150307401a6074106d020180107000b48140740000c075070f003540480c2c20032940c8800e890b0b4044000010480105468140400c0054007050038280d00f41494108001d1000542e424411f28070300322013401d500d0a407003541c1c11000250391507609006d040e1480f200080 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 536870503 1106 536869397 536869409
    0x804020d0203011806020c24131707030c030e03071802070f1e0308070e1804030909051e0112030503010b1b070e0702010c0207030507050d14060c0c07 66
    0x280d489400031302014000c4440802401c6160501e840b049400c01c0d5100c07000b03540700d01c00c09e11812a000720a544584004070850440000d20000b415024004d646075071960f80181000303040c0003a29116030b40a0307840003c0400c080759020700900042c03d61103001580d11101c1c0d0500800c0702d030b0780b035002034414202d450740003800058031515840b50911a44644096a680190035202800502599500f00840742c4082d010300c0703008000140d01501c00d04112140b6a10344c940441211f1040b05c0f11541072480203510301c0700c40000d48020303004001822001400141c6594001c1042c007040c881e51240c4400400e2440c52820224540c060200304801101c0d02a40c2d01d840041d181c8100351103820144d440c02036424084d5101040710b03070541b81c200004081c12803400050007400f0018960640f10458602c1c5509100007050100c0b82c0180400d89070a5154a94841207600b4102140e00c00 = true := by decide +kernel

theorem cover : BRFrame.Cov 536690647 536870503 := by
  have h0 := BRFrame.cov_init 536690647
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536690647 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536690647 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536690647 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536690647 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536690647 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536690647 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536690647 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536690647 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536690647 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536690647 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536690647 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536690647 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536690647 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536690647 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536690647 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536690647 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536690647 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536690647 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536690647 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536690647 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536690647 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536690647 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536690647 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536690647 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536690647 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536690647 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536690647 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536690647 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536690647 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536690647 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536690647 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536690647 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536690647 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536690647 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536690647 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536690647 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536690647 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536690647 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536690647 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536690647 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536690647 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536690647 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536690647 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536690647 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536690647 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536690647 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536690647 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536690647 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536690647 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536690647 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536690647 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536690647 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536690647 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536690647 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536690647 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536690647 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536690647 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536690647 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536690647 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536690647 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536690647 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536690647 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536690647 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536690647 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536690647 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536690647 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536690647 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536690647 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536690647 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536690647 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536690647 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536690647 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536690647 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536690647 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536690647 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536690647 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536690647 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536690647 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536690647 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536690647 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536690647 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536690647 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536690647 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536690647 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536690647 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536690647 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536690647 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536690647 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536690647 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536690647 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536690647 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536690647 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536690647 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536690647 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536690647 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536690647 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536690647 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536690647 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536690647 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536690647 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536690647 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536690647 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536690647 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536690647 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536690647 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536690647 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536690647 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536690647 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536690647 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536690647 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536690647 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536690647 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536690647 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536690647 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536690647 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536690647 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536690647 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536690647 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536690647 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536690647 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536690647 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536690647 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536690647 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536690647 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536690647 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536690647 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536690647 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536690647 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536690647 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536690647 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536690647 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536690647 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536690647 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536690647 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536690647 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536690647 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536690647 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536690647 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536690647 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536690647 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536690647 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536690647 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536690647 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536690647 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 536690647 ≤ n) (h2 : n < 536870503) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
