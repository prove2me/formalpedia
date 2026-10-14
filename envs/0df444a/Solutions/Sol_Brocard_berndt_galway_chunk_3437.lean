-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3437
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T09:39:42.636303+00:00
-- url     : https://prove2.me/submissions/14478449-e04a-4096-a437-df6d78e412c1

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 617985611 ≤ n < 618165467 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 617986861 1250 617985611 617985617
    0x50d020d1b2d0e1203070302010b091006030506012006040b0a0b031b030307050a0309061b03021c110a06060503160f0e1f27050105060d0f0b03070b03070f020a0b0601 73
    0x2035103180360300442c4031440b4003c0040449004002850519a581d000b4039420f0b0019800c01a20b44618105a001e05029002c240c2c030a1003a90f0411806501414010384010304109084c614528048920b458000c400e906502c0a007055051500740300301d000d803020f000741400358500000c5210691300000c05003420110203040c0322071001068000303070450241280140c40c901031845002c00301a808105002034a01d103898610701102a1380030b01d0388a110000c0020301584c0442090041415448400701100c0d0f1640341c081803c0701e01205c5a800d2088000d0115440740d1112014802c52506100000e0700c1d160404040d44190324044d80c0c2e201104251082d40582011080407680ca205003103d00b00b811410344c840003409a941e01c1e0324120380c2c0f81c09166800d05160b14034132495682168050720341295001000d20382001ca0100240000349028100c0100b50303581e401e81c440c0745440c01e00400c0300510000513040d449180944c1c0c090b044980024000c82150003103180d00c8002038401540a800032020320b = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 617988111 1250 617986861 617986937
    0x50606160c03060516080f0408180a0b0a0c03020c0d0b06060d090b040f0b09060408090402160c030f02090903090102060c070809040e030309210702040c050d020d1b 72
    0x42411020300c9519000501042e044c00100040030b800e68000d0a022203441c1d94050f6681c0c0d981421142070079040d01c000340303270450800c401004548000b000503020a0005c00082c0440c1d601e5503c070400b0340c00075084002040d09104000285a0144150b4070411010341d91038454004c0766840c003038040c3c4000e10962045001003015040100c0c0d690002c2590fa5000d001014207007010b040000c1c1c10211100111425480000080c460840101ea550b0046901000443c102aa03060400020f50042c07220303ca0182c010f15008000b082c0c000c41580d00841c040c1d01e080d61000c85500500c040c0d000000c0113400554002c0104c000940d034002005540f002c04800740702c1e00c400b101d02d0a0a07180c450a00d01e141c1c03140c20140c0c40d520200004c8021406a51484125546614070304003018480803132104084580703105001d0700000d414580c000c80b4050f400391510528240c1c100a91404a811501c600110729a032100c0b2000141c42070401c04480c069182000d12003030396103051030281174500b4034811075250110 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 617989361 1250 617988111 617988113
    0xf1203050703050409060906170102070b0a0c02190627150203220303050f09010b030c0f2407050c040b0607020f030f01020d020d050a0e070306020c1204090c08010905060616 76
    0x20b80c00da1300a0120101d040c084203070f8800c1c158024084600030a8041d0030250180302c078415051086a1100390300008804c0b4540c0c40740701e414010007040b03540c40154001c01d20b002c1c0f603024100d07510a065600c140b500180c0c400742c84910707070120180314043c2c1c2c1c003400808050001003038005501d85a290409000540d50f0303070700c1140301d5110307400703212900d0034407141f0248100805030150881c501c07805498004004a0b9a2031508501341c3d1803030001180c040d0000042101542861070500c43c401c400a800c5060821007040d20042080490031142881f03000411518200041440300c40944d110448042c0324101d50b0800187c0d45100b520002481421070b0b040d01078468a040c0520751407d020788000f107407581e64601e101000f03940503010b44102b89103403000207030300c110303e510403400903410000c002c0c110a81551364510082d071010035040014440c90507980b6060204100400c0500340100003c01d108903400c0c406000900f068001c3c0010078201001c1061341e8444e4400d0340c0c9800780381c9500702e03414021 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 617990611 1250 617989361 617989367
    0xb041d06061b03070302060703020301320a0807241d0a03020307060306050a0b2d2b05151005090f09070c050f0307052d0f060108070f1203050703 64
    0x5240302d041d1400c1081e01d16001c80900100107032075031601a800781c401668442c0422022403009000e680b200c669030780c2000c2410200502100008251421407800b821610300c0000d141e4420b51784000c100d42d0047e20244441401d82c400d6282d10302080220f07014018050030050304404511240b4101c100d000c8048803201e5540d03043e104011034000d000d440d46207131141c40050190400703004060250070702c0c4030001071602120085895050740d20782c42c00403800c060361103074003030021000381459520410b00c007186480303080e070407642c01100440d28060b00f90107141c2e101c5000d5900041c5000c100754400700c0e40e0700301510760442105080c0c42e6454182e54a07504203000410701c00d205031b8099001a080d9042100d1241c0003504481440e0044044400d0318070302c0007400f40d90380300fa0b40009015070882d0380350780521401110082c50358100710100c0191400c0301e28040b440d00c402010907002992040004100c0d204040c0014009001e0305c0491600c00b504002d42d00d10041c80c01c400080822078006842402e040c8 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 617991861 1250 617990611 617990617
    0x609010f0e120717030c15072622021513090e0705120303160c2108040c05010c0503030c070302033f070804120306052101060b041d0606 60
    0x3100504002d402440911400e540ba11140108282d945084280c807071114400001d8581640800004200111000d40c284540340000741403603050213080c4124258418100202c0d2192200c00324035143d0501e049210004030303080b001d5050000d00503280c45a0701586440c0741210040851020301d41d92565202980307902d42d4410750121f40d400345800014140f11101191083c203d510450700340e0042224102c11a882e44001d03900a0001c508911913420031070f024000440f0b41c41c3c0030300c1c8401004030880f08504440c5031710824040000380824200010400358120040c09403100303190881c6004820754840e50b4a00c0043c0445441407004038801342094802c0049034070b43c0780892500a100c151181051484902d00b050480050350f21042e240075400c2c0f041100c9110303185958460142d80c41e41d40b502401f801c894030a007820961941008100b60b10740100007864000050071004400303040c140c3c111300b1030b805500300c0507003010200000c1050841e1036003040300b4844900b07005511500c6e1400042c040784 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 617993111 1250 617991861 617991887
    0x20906120f1e070807061e0201020403020402070f170c0a03031e15060210021306111606050409050901020408030f03101203110c0301052203121107020a06030b0609010f 74
    0x220490806010841202d85001002c1c900d040c2250581600d405240e0b4640b070003402070740b00003000c41480c2091950444d2080d0072103c1e890000500c2c198481c3c0102c0c050340d02030300059520503141d85421080111103030003062102c840340c40c01420300e002442d009440e000f00403800b5003055114100300c2844180d01a02a1140072110300401c110305c041110025007410510603900540076103c501102c01ea5030740210f6612301c0451744801c040b58100345042d0780c9145400048515440769124400c84640785038406000741c042c80e22000e0b140e0b841c10803014203440300117000040e81d90060004010800d40001913466903c1c4160781c440e141e56506d0160000150030b54043c1c030074215120000c00505800c085a20010704000c0d0a44010b0180750303051501740d0340700361422a141075000c941000341c8001c6021905110b803082c500800d000e0030350040d51098410b800903401510390002448421480c1c5902100d004280c281810301480c01c0844c00030314280140d0001d0b034140f2040b8a1079101491040c04040c00c40 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 617994361 1250 617993111 617993113
    0x40b0409061715160309051203090d02010e070b070f060c053004170405032523040b040b090708070315080318211612020906120f 57
    0x59996210640003900c541e21034050001c0c0e030280707107401c40030000c60a0600c219a041590b0140c0d00e0700c801c4d07010403040000c004010155200c10550006100784016110320800c010b10300d80340c2c101600c1490412410712407072015a85420940e002c84000400c45808503907010465a441d580e8a041c44904001d03421002850207103401c0c448002103030041c010340750284408120601480c0c5400f5509040800d1a40350421100600005000902c1079044130205140407101103007410790300e0010a10b02540c2655150110044030794034079400c046500c0901c01842d24600301e141c10040d104864041400d09509603010b0717030b220074944d052902c03550010340d110240035000c00c08a00c0c2441d0014a035540a84003100001d081648a2201c444000904070540b100790001d1761801441500c842d40c5041da442844d600b20785e0061145074005002c6900c3c142c4100c0010240c034010440103141055408103400c1032034800c2110980f5805600d070061441e40c00318042e60102d009040c0025024540518098400d0301 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 617995611 1250 617994361 617994367
    0x5040302060a170c07030c24060608011d1303110c0d0311060603060105031f06080a0b07030b0103061a0310091506030605090906070c0f080301030c06200c15040b 71
    0x342c1c0d075105800200703e03440c4014549094640114003030a500c560f40300940001d541d0008400411810010424083c01c800390f05000141c0440004043e83c0fa1644a00e000c11400c0b0010004003200d641c1c0c0709901d107003c914942e02480d10004220300341d040220054100403d050f06090041820848510880300041005e00d14103460b1500400609942441c1c54160061034086585810700180c45410b0701c10050192443c07880030074018043e0424581201180ca40310000040d41410078000c240710103000c1c034044045454104005016039404c8480d41e0304061800808109da541003070a400d07050400c00411079a40c2c0c48244480c0d01f1000c0503041124420300d05120031500181c00410401158480e44051081c01d82d14401c01c200a281199041d81c0c5400160028040a1142d001c004e80d0503c01c3c4490758800f4181d4451442d250000d030002c071070009c2c07103034002e00056800c041164200c164103e01216240000340401b92585c0d004c00c2c8240c056010395110701c540d6420b1905480180003018101a1 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 617996861 1250 617995611 617995627
    0x40b090a0f2a5301030b01090b040212040302030702010207080a080d0525020309010905090c070816140303040303110c10020f041703030a15081203070c06020c010b030f01150e070504030206 83
    0x40002e6903401100810440c0c503c1203804000544418102c9070440b0301d40006078038086c8224040c1910b00f85855020f0350070801084000c04070503d441c0036a0013039000f961101014070005e880c0c6035140d0011802c5510004170400050929822a484000509008500e0383ca4000015510a081c0b11041006004030203619400c0d07980040030b0f106141c0242e9510920030382d00d4003070080841d02a5505958038000f040a80701080301e10000341390400fa012412070b0a070903107480d07420310480d1043c0c880ea0700d90000000c0c0b1003455414010074009021541c900b91402c450070000b150740b5400c40102c900b02d81c0e0042000110011407a0665008040c1c4080720640b090a00b448039071240c1c01102d0044a4038508200b21b0803000c05d51b0080000d6907210300c0101600f4400304238104150300000c1c0b52100300f00c845148000003440d50700191410020303110011420440c440700701402c20f08514030300c40c03071030389032000d146018070110001d801103c0c9510080d0036151100307507003100e5a10580d08041d401802c0099010 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 617998111 1250 617996861 617996957
    0xc2b02040e1302010f2a050a0503030a060f14030303191b03050906010b09030712020d1e0b010b0f07030323041401061208040b0306040b090a0f2a 64
    0x1010103100740d0390301700c040310440b10650300c150500c010344c02d4810390b0300c981045a02c03d0200240036a4060740c11202403a21644d81c0e00e00d07550048810103403071074841034108100186094a800980007285c1c501e6400070850010035601e00005080c034a400c008050503140482065100d6940c40c018903c91001d180c204600140280c0003d03035000c2d030503114410000880b10310850684504a10003409003003068034200c054034224410420585c2c1c04030300a00c1c0540020400340d03200c070f0b0304075a90342400500400c9040c4044a090705a00c8020410410400c80c42020840004c071105180c0c14240010310105100803003604103004821008148909070501041c0a044007615071543e03201d60090214a49400002c82640b420990060025030188814130a10140c2405141d100d0005030002844074440700000c0e9000c81e042c0c40c040c82e00c1d5940c0541c19820051402b44424000200d019407510f0044200143d0111503c210100c0c02c1000d044070b00782d4010620303d007140b1200300000d010350074100f00d1502c03c = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 617999361 1250 617998111 617998141
    0x51905070c021c02010206160504050307031a070f09090905070519081e0a0b060409052e0509070515070605010f05010e041e020a021e06010603050c2b02040e 69
    0x40c3c0c8903981082800c07501018081501000c99810790103800152070f6892135032441140d040141c400e11030180004103551b1400c00c5904021406500c210782c192040c5c8030f0485050002600c46400c00011041d458560360b005000c25040711030712000000e400e2070504007903003410044e80001d03a100d06454000010320b036044204805880c1c04009580030170300e00c07154011102d8041c240004c0150404040c24002c00c0850074056840070020744042524003081d55042d02300795200140d2030b43d1045107228640b0409510b0101c03084240020010091030a040c1d0409640b060a48902445180f4103007008068440b96015185410343c844028003155840f22240b04828449020781c3d40001d480c88045ca0040c541400707500d14120720210101d002d6407009a0b510080d520036064031040d0301c102000c002e52150840031a024040c40300000d00220350500b034004003621b034080c2003622070840a004110742c1080000f500340c81e00078110038140c000340042492074040d0145038803041c0100802c40c1004426002c260036 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 618000611 1250 617999361 617999363
    0x206090a0305011508070e071d01170a06030b06010e010903061821080f04020f0405060118061106070201110f0a1704050102070209060619080a0603080f1b0c13051905070c 75
    0xd844042d0303100c7c43e10361107915040390090009480760310900608908034810518075201031515070f03118540000d00400c0c01c1e00c280c0c0e400c00090b6440e0010014001c0284155030440403d00c0c0a000710010003000901c044454040a02802e0381d48960a030202041d10028280c264480301c10001e0b011400500c802d124068584c40c4045003401b00000c0c20180203d140d50b100e241e000b001f1021a8010000340700c0200720081c45141486840c83d40120307600c01c0080000002d10994cc0c40b8038001c4040384c016410312401800309025a81400001404000785409031070382140601c07034140d200c01c00c00300c080f90740c4694804202c04036105501440705109041d0018129240203840441c25500d464052058510030341a03c2905295110545e1403014820b4203650381010542801003859a141c0d190380d00280c0c40802e10385056031000480000074001101000050301842000d04031030f00c0f0726804681e6002003103001c82c2e0120b5407040000d0400d01895120f003031400301403208000d24504000090095140d03008 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 618001861 1250 618000611 618000613
    0x90503030d232d0402061603090b16021806010203040b130b1204061503240f0e0f070603020403050601061b05010609020a0908011806110c0d021c02030a0c0206090a0305011508 77
    0x9541030384008803d00e030b94012540501a03d00d001038445d100c028030980d8400440c2000581000041c89000c0440500030911004041c0c206000c2c3d5407040210380c2c400d103100304d0307440038440d0104180c60b07802105680031245010080c6a5500c461f04940c880b0307108a4000c8800e80001180c00f030362407880500501d1043e44a54402c001d8075603143c0e5071000c405c8080c407000780424070020410740c40c1c00d0b500121060749000743c44003142c4065100010340603214800440266076100c0b014005141c4400c0004c43c008241504003107140034210384819407100c405008000500240e0001c210a030000c502c441210380341c0001c001c10100b030302c8600e00030195200c9101c00f00010030283c00480e0741e00e018418074501e2860103000e12504a5a90703140c0300035000749018481c038140c1c24004000704090901101d103800d42c2036400761412a035924000d27401a406c2e844004110351051042580315900b1402964501e6011103041ea101d000c28000144030b8000c80d00010055404c1000501c5c450000d44c0340c1d482030f280c80e10 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 618003111 1250 618001861 618001921
    0xf18040f0f0f150507020313033507211209020d061d160b070609061d0c01080708011d19020c030c010e030c0703111306060f0f090503030d23 62
    0x3090490742c0340901a84036109a081c074400300000f403130103001d0164054402c40000080b03cae44040000c0200082110208261400107043c001c0220340b1905c0c05100c0611940c0448a8080e120002e0404d0019404846c2d110703a02e05608065668070b40c1c00c8a121a800b04c1d00384603000590720f01e032050385849444044180b0070a00b03021014200d0180b40740944151181c400d0909440d601e404021b08030740034040d141d26036154a0445402046141408204140e000901c2c0c0e06101c40001800d60350004c3c074001c1080385500c018004140075a01645415165503003a54a036107483c05800042966201c2403071040344000351846030303030202101038211810707140d0007007061070b01603050b081d124800d07443c100c0e100d90002e031400c0c000030f012403215900a40c0043d10102003080700400410884140342c00c00d40200c0c08103c00a20301e0780c0c0c040101c540d9a6490301e8031180355850711001ca41e9034020780c450008055100e031203c3c910310a24444450780308140e0900b11000341000f8031240580380000ca84c4100b00c208034 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 618004361 1250 618003111 618003121
    0x20a0209010e0601120f0b030d0504080d0309080409020c0f030315010908070311100e1302070219030c051002191b060207140103020a020a05070906050f18040f0f0f1505 74
    0x408a442d1084030181c640c0c1d00f607817215030070000003424000050710201d555441022440e480801c10014515001d45403036a40710f0900d44228a8001e02a401d141054100401240000c01100589084aa8900004d61202c881800d458140455070f21041060f10000c020080325441e0100928000c00e000e80380d030b44145813244140c5440d42500d000150000f548014466964104540b1680014110b0b00c0d000c0075102000d400908910159110110110303000310b034002c00d40c03500d58044a0304514903200c0642d817624580d54054800003611805200e8400b180d0b0401a9038002d20861110200d540c0d8400c12508035482e00d16824088861081c2465003094804100c0030300015400003a50003142040040c41c0c003920045002e03601084208085003e03030b50381c0400003001000a5005071000701307030101e1102d09120504c04008004003100e03100e69910003080d50000c8c85030f010942c0061300500c0b0961018500d00304800309144101000b04541181e2039a40c0602001061102c0704414800051105031a4 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 618005611 1250 618004361 618004379
    0x228090501030e0c091f0608071d031c0509030a0506180703240e01182109051504080303040b070806041407230c07050a0501050a08040f020619020a020901 68
    0x1c2c01d003c440541c2c0c8661030b0901c00e86000c3c00307001d0780003080c0240c20b000740b041d0518161050304240d20004c0420b0641c401d200110741c1200c01d0009450b20600502480a0f03014000380c0e656070b2040450300d81c1584142e40300d206620600896050b05070281c02c0350074662141c41c0c640d1b50740000300c50115404841d0710240d5194103000c41e60804980e001515503214019020002c0b840d82e85141c03610806651b54032401421403801c1c040c10340c0840074050f043c2a900d002d03041a0035002c44030700b460311000e801d1400d45200150032001110a0b0741050740d94452609100680d03100e02d00c0703180c00c425000e200102c204420032a2426140d413043c08980d440c00074544402c000e210550305100503605a21689400256001e4490002d0084003200300703281080074201039010845561004c2c0e4814600c2c3c0105c0020700590506a02c03100c0141428a040c510700440ca1000030300ca144040e000a10002c0182c1b06502903503103400c19101a0307640c5000d5201564603080340a9560950200d00301d0245050b0000040c00d090 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 618006861 1250 618005611 618005621
    0x30d060605072009071b0b072f15090a1e1a10150c0c080c0415050a1a0c0d05030a0c0f05030c0a1e020307150e0c040906022809050103 59
    0x501031300068154984000c00e81e0840100083c00d520310217100000008122514440c500076805520b031100e000c030341581e003400074107100c1c61054003c60380103440c0707a074144001070b0204200341e1170720038141031781c0392414000d040000b401c0d005040340d886aa004034103100954003101c0301c0761040310320700b0030721910f4441c3c2d541c1c007041240c00510b10046c3c01400c0000c200b0421507901c8481980c1f038000c640c45100c0e6030b42031014500d90441c0400e47d0000d080140310f42804e1040980307951400001d00211403501c00006c40c2c80d0014003d098070b1403040300400e00c001c01035400765019404038a0540709811811400208590002ca588407100c50402010202250150b100d501c120b01c11965000c0c6145c0d62181c0303d24640d4020060030781081801e461011418400369840b050302031865001e996500302a04140100e142c18101a9a1251402401c100ca401e00018030307490004003543c0c003140010f1070741821002401462050243c4144044011800c20014803812950420f203803940300d6416140c400443c00c0b50 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 618008111 1250 618006861 618006923
    0x1061103030106080402040e06251106070e06040308120a0b040c090302220f0e0d02070f03060c050f070609060f11030402090c040b0705030712052802030d06060507 72
    0x3400c00c00040c04142d204220711380c0d026002500100d00400c15128051030a00c0c100c038006035442109282511005072480c00000385034042c94481e44d0000004080d0f40ca6080c0640300b44184458102c1451150316568140c80007950808a42a00ca550303000040c0d52154040705e64a0425140102d5402c175450280700d0348d00f402410b6551695024219402d2004820f52000d9101054540115a01c01c00c5414043c1070620f81d0010404200c0c120422303415840c00400c83d800c0c40640d04070401c03c0c844ca01f080340449040340d802c10340105000350b80010550b107521405000d015406800181c0c43c081c01019000102030900c80c070740c1080f002d40e036134914000321940813a950340e44030b10070004240949000c8101f6900000041c1c800b62034196100c00b03002195000c2441181c03a0f070000704042043c08503038170400c81c44114605141d40b03007083c062070940c00c00280e00000c403040c0c15060312043d03855108006454501a40305410010350741c50304406042a0804401120114405c3c0788002d0940c0030041403000f28 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 618009361 1250 618008111 618008113
    0x60301060c0b0f0103200a050406140f0d15020d0b090c0a02070602030a0c030507021c2907080a02070501091202031804020a0228020d0c030308060d120c170a02030a08010611 76
    0x207480b4000c84105200c00c0d0340903690060949001003003a640d2440707920000c1c0102f10302e40307070340b14140000d00280c0303a1002c074001e100e41d5210a100c0045080c0c08441001c0d82d4070b508005a66007042c036221030003454986c4e0050b03040030001082000201034840100b440706c00710b800b02c42d0801c1d070b540422641c038860310b500c042c001610100b034000003d00a07000f40c041e41d0710040c80e40c40c050703204ca21520441040a5005d039007502c8045000c0341c10446d51010086c10341111502d0101c1860000006070040b200175102c2505203900188240610000b944418226a88200c00800c00769071014001d64079085410003658841c03c0c0f4907100312925042c82201c0d464001d68019000700310114442030803406414501611503500c20180070016641c02c5480500e00e407003841c1d081c5440b421820b00502400d0020100c6002e184419818004039148d00c0a1640140452030b00d41c00c1c2014518000b040c6d15035007030386403052500114001002c01c1e0080090158100380b582d404040e41c1ea13a210480d414080405000c0711 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 618010611 1250 618009361 618009383
    0x901050f04051b0a151e0206010b0324040c020d020705041803050c07090204091d0604030c0b07050c01150311060f03240607061e29010e060301060c0b0f0103 69
    0x11203150401000148032008001d2840a03680380390b400a202c400c45c041c13200166140b0b80711403241000420b01504c3c08068030007400d40358103060750b5403070612018107076241c1e81030900100f481780380c48409917001812001d0028456000c01280c082d503a100080c02d804054001d1f0b5801058030b0519106504950781048040d6403039210703644090780c1c554403103801e0000c0d90003071010105842e251b0b400144010306440e10001010762801041c007080d12907500d03003448582c0100003403102203940300c19412416504001914000d846280054690703200d00e6903441e030070b5402c080d1010542821601c80310110303401036044240070350840040000310301c66901d101602210500101c1d40004c0e000000d03090306c04903900c511902c42c10900c0001c0c225004204200c40703081d120b88144a440d8131b1078400b840c2a4642d1502804400079140f5401c21514001840c8200c4036450540c2014683c4280200f44001401600759580d82d615000e0040101c0c800c000b059403482113400c0821744011121401c181200e03004410001 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 618011861 1250 618010611 618010633
    0x303030f0b03030906211005090f07050a1409031009060b040b061c0908040e190b0a0509060301020d02160b06010c020a03120e0a180f2310030f08030901050f0405 71
    0x705c2908042c2000030b0111407940e044c2d01c0c5401449105000704548001c4c00005403905007040fa00c040c000b425501c254100c00c041c0031003e03820505440e000c201030700301240107441d800c90041d40340c012200155418403803d5581c0140e01140da1100d0b800502580702881840720060034081560117841241d90014800c100b5186400b2a0300300b06038035170311000c0e8003140040c01c94542d2160b54115030000403011b181c11040c411400d003000100c2c504614130441c1840200742c01e000040b00d12440e40b0459009060702c40004280da80c0a5040720070f415100c01c42151141c0c1000c0305440340d807104207801c490341d407031440101e603403507002d190052140b507070081045503071609655424804c04040b501180504c140d800550b2110f54031440700710701414040c241c030458811500b0314101070f90034040009800d02c0c640074074107100e0b1070380f510103846841840e00d0b60481078a4200f40411728070015400686060410782415080118160040d402200114000e1115854080c040320f40c5ea8025240141031b64400d4003c0c43c = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 618013111 1250 618011861 618011869
    0x20f0904180c33030b0907091802071505040c1508010311151219062112050d0207051b1c231e19051f0e1005010303030f0b030309 57
    0x8100610501e4a4940c8403840303c03816141440c20061001c01d0f103440340d114081c1008890154882d20070320708840c4e014030300592146585051054241c21540020b242d00520120244100e41c28111500402c194502401c1040007411603000c2c0f40000b424080d51f980c44203118200a6060340c0d0003540480180b0701081c10400780c680d010f0a404036481c410710421314902e06201426118013000c4070681405c070740c0800310204495441d0444140100d02c46603080f00d1102d406030004d295980300141004844400390255030398011715035403140c031a000080410400802003980300c0408542e546001d02d040440040006e07801c0c00240d1440c0c008c0003502c00d180403505804041054a001d41d8407080c01000c0110301c2410300d00000305030303104000340c3d0760050743c801c1041250010a465000038032142074016910107813503010f4100812005940c03509503961211065120298100029088546080e48081d020024150910040d400f00f8235182480c0301f2006c55020310300d025100200690700d00450b450400c = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 618014361 1250 618013111 618013139
    0x1080406051e0408070203160b03011e03120e0906060a08060603100e0a06080c0103060503101a0406090e0c03030705030414180a0c02061503030f0d0608030f0d0c09060801050d15020f0904180c 84
    0x11059840c00c030cd400070200380c07200b60381d803210142551180d0703100540d142808040700c00540954041ca20400c00f00c0c404a46c4001001e402003012110345503203860750b1f80180f49100090f08528284803190701402541e050a900c03c0040315020310540c0c0a06144030019801c54401e40324954143d04182c403000e004050710b5014507805409068a09003503820100401e0072101c40d504621361195640301d6040303032000e080110209010040700190301d000e90969401e0385a004501c0b801c1036030401600300880642d90030085400708040c1a0724100c1c00e1603c091145d003e0300000701100e0150043c4001300342c27070003201c00701c28064000140055140a07101240f03005190312102c00d00070200e5a500003c81d4229050008082e00d1405800d5191541c0c0842c1e6a03034200e4202d014800b06101c3d01c00410415142c00c0200c0c20304450048402d28183c451909144400c1e440c8007104115940c400900381c180c80810501400402c1d07001d0710104a541e16210030135600c00200300014005c05080714041210707940403001 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 618015611 1250 618014361 618014399
    0x40c05011b0210020124030506090303060a03021e04180b061005031b041e0e070c0b06040e160f0f051203041e0e0906150f01080406051e0408070203160b0301 69
    0x1a4181070606e103d803004a40104107040080300d02400c2050140401100390000322100c051403442c10480d002814034551844001d0049c2c809070381e10a0707d005408003d166882020704244800444940c40c0700712904541800ca032510071307050200c0c5580c14070300d00080c4c1c000066101d544c0785880340080c2c02c002c02c0d04109466041c502c1040b010a4005081058045490784507014140351400c00c0d040140c8594014040f10402440900e2500032442d48061542c1044090f1000580d5203c3d404030700381042010310040a03900c4203500001140e4002c501600112424144000c001c140c8440c100701c2c0d9401960b4036910254018003003400090864808400c00c95039943c99001003940c1d41c1280404910100c0e0648002d400240c10001c1d6003102c0700c241c0404500032140c0c08181607444c000070307000d505d000e8409805156240009018271005c403040041d002c01d4002d1440485c0f40900d0301485a070701c8204224000c0c022040b05804007070000406400fa02d0581030400c1c1140e0034400b43c14403a220400c4 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 618016861 1250 618015611 618015613
    0xf0c08060f01030f060f081c0503160c150e0d0305070302090915010e100513090c051e04170309040c03060302100804031412040606060f0f03090f02100206040c05011b021002 76
    0x180006c1c4040c808185a4018040c031406002c1086100c0582c145a0a4210b81401480410010010115032001500e5540e8140b4107020600100505080c0b5030400404148e4109034a0590000301d00000003d900c59242c1082c0e80c00d009503a55a0403c4042e03008085400b50032030b440e500810641c42454540103e490018500b4828071816140002c1000d4510304c2d080d0003003903000540b4462820500940805450a443c2c00e0158042c01c02c8024254030410024100b10f14048540c042d8416200b005c07213009100e0f5000784503800982003001c41d141c1e0b1003105001e10861804002c0b10855000740501d104a940007491400d00403001442541c0d42200104118200b000d09400f42c219101400c0144c01d0490902c00e11440ca850586000c40803030f01c0c1600140c0c140414400c8640146510008459210b0058500421010018982a4658102990000c0d80701060403079409509a0015040b803040780516289140031b031340d440c01901d60340c4181c002e0a9052014180b07410140c00d0000b6400c3e107000e4148 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 618018111 1250 618016861 618016871
    0xc0f0d0f0f02032505060405060a0315080f03090301240b0a0e0d200d050c01030b040b060f03071418040e030c073b070c020303120a0f0c08060f01030f 66
    0xe400241000b1342411000c031004810350300103805003555000321020700000e96030185050700305400100c1d01d01800a00008140d100d0340c9101007444e0000d965001401a0001c468040042c1c580d00f5449800c04a0001e019610308620766001e0090b0f03492800e4494040765112803428200341746030718294031062803001030000314110801d0035140d402038980180e00a0340c1800403592615100324808104118040c0710b07031445aa03440110f100414455412002400d0000b400445e0a0108015020a4400d175901120100c0c0011003c00baa800551144100d81d40f910903e03000c030b45600303806000303146011944550001c4d48076500e050550010303a500052204481c140468142070600e004101d401c41c41000f004202101180d261108407414036100845802e40c02010401070041c1c1e80400804490801c13105250356025500c0038421103106035412121030803d46054041400034044000f0348058a41c82c2219000081e03101d0720000e0700491000300a0300b0709040440045020b4620f586403c609a0360351 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 618019361 1250 618018111 618018113
    0x14030a171e030a09030e040902010f080711010e1e0a0f02040b12010c0c14030a21060b030a0504050c040b030604020114040909030e1201050403170a06090608010209030c0f0d0f0f 78
    0x1080186200700c6a2203401300382c8034042c1c40e000b0b0994210301d8200b0300541c100150680140c2c1c00c0b0703052182c01040c0e80b40103180b9584400342151051924a01c140540d440e22410a1050001041001c0c022280300c900319035901807001202d503280d402c050b0140505200003126801450183c01001701c6c1400105085403175504100d4007821507408240b0700c4007081035000400204443c54090220710381c95100594142481000301401a140c0699070001c0e011000e8500543e00010703501600141071107600c1c2d151a442c000f002103004001c1a201500c40c0c0c45055004103480c60b04e401801406803000e000740420b80c440750b0054400000e884030b10447c1d600e05010200303118100d4454114030751b001766200025403010106101061441c500400341d0342c0d041108001c0426000441c500007070b120700d00c8180f80c0c1c0c1d6501072814024411904001611800d003803000400e042d05401411020784128196441c2000c0c440c1000580e4240c841000d4000102074100c20216041c0064100454000d4514541e10409 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 618020611 1250 618019361 618019417
    0x101d0c07060c052a1518060108070612020307090501050d11030702030702010e0f030601051302041e031406070e0112060302040203040f0b010b030c0304140f060a0614030a17 76
    0x1180c0e1a200001e5000709800740d034840d00d0465014406504c10300d407144407504000142d00c400100b128a861102c018003c038402408010302e00d2a5044010280d80030f55848098068946002e03100d01c1c40000c02603880c8203400c4000384203c1e8080c0d681600c6282c0020300e060010368081d0444070b8000c881d039a0b00d252180ea0620980c000f980300e128254040c60340c4e00f81500c009001d008401d854140202c07403503c1040001e171000202d5030b0560320101c80c3c0c5100b21a0030014900079110300d40007d00318001d80414414000c271100c0141c41a21700c902c0c50028540c0c4224809581e40c4c40440341400050303008000103000754080c00720a128405108404610320751203801007400d0b0b074000c2e40e0855502c0c0002c10000f091095003219507001d088040650f40c40c0d0308249010f5980c074000a0030141c00554190200c101580c4104416812003203071f0426540c0038505900810000c00d01445806c10002c808140603ca510b40401c4c81e00c051035104d9040e40034070100510004445d000114412030300305c1502180344401c8c103 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 618021861 1250 618020611 618020621
    0x9030a05070906080304030c3303051806040c030219030c0f1712180a082d07032f090a1b14030a0f24030506101d0c0706 53
    0x4010300003095100d1a000d003075003c60f030142e03102c220181c005020a00006640c103030890b04031250744101071459440a111203030140744050500c1e00c0c210600030880405a01034000d14422080d0354102c00004140050003626010101d1b4000c1c10907800400c00c4c001481c0940303500410200013440a5901d07510b95541007a10031041c2c2164154099890081240c0c80000c03d05000e0700700550044c240190301a2450013041c020741781c01d600344440b138980d00f85080d00e0f460034043c02004600304864030054120542858050449503500c0081c0040403a80e506900000356002100d51110309091401150204014005c0e880c4400202007941002e1a800b9684c40601480c041c1c0b88030040041c3c403605421960035078500844079175003071006190b06420440110b00a981d4000c5250340c0201e002d00e001c20b650001068000c20201c03806805008050b1030309142d090840580c0d10a6044881035202d442030501141500e1041164001254050120700c61a8603480c68201d01400c020a04110f8036036104c1c01613034 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 618023111 1250 618021861 618021863
    0xf070e1201051501090b0a0318060f1508010501051e03010e1c0f03060b0415020a060510050a050a0b07150e0703141b0f011409150a02071a040311010509030a 69
    0x107910350092010b00f40d81d0f0282040c0100b000d080c040c1155240a806500c03034010542d400003031544d20382c60041c0403c4108006440c0941c0180c08001c0e000740c40620200400300c2c16000025a0101500894500c1d01441218107a8200404c0521002258050032814130035541e0156055500c42103052110765042217201030402c6880003401d103241e0000f0307005208522007000d000406081c0300d410480c80181c5401c5600b030311310251100b9a038101080003a4034051080360010720f468174050402007210800c48882c01a2401101c00300c60442d50342081026401d1103000f04074011000304101030002c0c03502142215801519030380864521790800700316080500710741c4150340501003290891500b03002800200d04c40c02080d80e60548079442c0d0380204910030031764200d85052010380c10005403068090025140420401400c0741602060a45c0300e00698102482c481c01522a1240102e900e21030800212175050070000740c0350034217140d034603038a080540704540c09041c01803c000542544e05c0c103100b9001c0032 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 618024361 1250 618023111 618023113
    0xb0d140c090702060105010801050603070302070c180b010302040b09010c140105010b0a0807030525020106091b02060106020307240603150608070503030703020709051f080f0d14030f070e12 83
    0x140600409020341e0240040c0240c0864011100500c0a60303009007903141500d0090380d00341e48036070714488194028424414003400c050390b11440007604081c492080d1203400c402c480140044039603180150142e00481c011200c407018240b203e01d055510402400700f820f070050121008481507180801d00b1100280c0140040060000701c00a4860300000c1c05500702c5803078a0204043e141c044584595509204402d0520140c02202c02c09014800d401840103418458810072083c01d5950690100304456013543d00507000d00c4000080c440d0000c000d0701c204a80041c00500d001071840c1c1500c480403809444001500e565810120208101909144240300304100009030715082c5030116181824a034029072080d4410440d00002950100e0014211059500d003c04c603502e94451403104001c419081c1071084228110000319a0800108421009140804d4070703000f500120048550741c05101c0350b801c0103501000482c80c00d4a1642171594003030028601801507103e9140010000004882c071410a = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 618025611 1250 618024361 618024373
    0xa0e090a0603200112050402040f0c021627020c010f09060e010605060405011d031929010f12022202040e0f0601090e1e010b0d0e011e0b0d14 62
    0x400100741d500d000e002a4910184114410f110002001c3c80010050006160744450100302152a9904107451201c2842d205015048550382d00940d1410644109000c0e0951440d002612840c940344514070788001c404200100d925000030803003e584076449aa10a6580d010700e01000c01441c0b01c0d950341c0d14492803000c99075500c8271150310300f96011504078520a01003000308001582c1c2144032401d45410b100c1d0782c02d0600009400080c100401d000342c0b240c859900344803610410140c0403840da0000328042007205603007c0c2000d5400c2e140424010083d6942070010203002d4040c800103d03141042c4000c0800c04624401c10105203c404060101e00c8496004030b424000c038258205499800841311910001601d4070030700080c0500b1452060b110284e880c040442d80001d03900b140d03519000200360003000103580d01c4240f581254441034001c80c0d02c80c604510070400400601407c3d400c28001c20240f04611000060328008201e1700b030040e036001d5111000c0500058951042ca40d9480b040e00c06004 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 618026861 1250 618025611 618025613
    0xb0c070c030b191a06030a0b04270c0f0302010f030e031e0c0d1803120c140d1b02030703140102070f0f03180f0e060d0803090a0312140c0a0e090a0603 66
    0x3c1a01c000d1403003504115882c5080c0c10311034a80c501503d81c4258244800300d1048100b10200707005203036200b03401049291045801201406940c0010901c0d446580701c40d84a071395070540d00368a020107010081c0001d00141c00701c01d00038400c0e003000301381da000306060f646040382c44500c54204454201d0884c191000c00708484003071031401d122041c000c2d031050030860307c90130141d92241801101400002e00c4040c00c00190224540f007030b442e01070b02d954810300605014540200f00d03540c03400c07601a8100040c5190440141481315489004280c1d41d000c0c005259542c1165540740c0b509142c0036102a030b0f50741c00d10140002c204841c0d0040b4505004400d10120301c16141001048043d00004080030510000307003c0000c5070302038444500b111214090000c198a03124005556102182c0000e04500004400c2c440622008120a03d4680c0b194880d8100484221142c4064600c00707420058450381c0c04000443d558909030040c10503400341e1500c2130198200350001000900e00b138804880c001e60b6050180 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 618028111 1250 618026861 618026911
    0x61505120c090916171609020304020910060815010212070b0a241401141c0606020607050a110708031b010b0114030105060a03110a111204030b0c070c030b 68
    0x160880180030103130a034208000c0b2100d800320000d03c268001810f0f0040c10f08904102031244c4605000300399000b210407540c650200c0c01940007071710164450110140483c0c2a1600040c201c402c948168894100c0d664500580c0f0590200c40840c081c1075008540782e110700030010800400c6207500c1014000145c2c01c0ca85d4a0400300c0740320054004034042c0c84400d0ba040c10984181e00401c80307078401028000c041700c2ca00101c890316048095042c42c00e602203102590b0940030030708451400c1e00a48200205540c5503402c80c0c0d2004241c8950001c5001080b00c54a100e1080404000c0700074680101d8a01d41d94442015141d584920b805003220400c820030302c44c0800c001e000b000e035a6a000d190a0418100d4481903103118441072040b54407030390740000d40c5407006010ba00011050003040ca0040c0d2143e0190f407018115440c130384403229040c017500c8040b6012840c400291002d880d041082e00800395180d40c03509406038011401503030b000b01240e00010014a41c00c80c194450b0241c01900c86180c0c003d52060 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 618029361 1250 618028111 618028129
    0x250212030a020a150b030a23060103080a020d020a020618031e030702090106020a0b0c09190f14041a04050405030c191103011b0e0d060f020403020922061505120c 71
    0x450307091820491045d02aa400140c080d1220342c101054280a0110b42000750184982086a00c014001c9200000502407503001074213550615800f501c012140c06082261280c3c0c1181000794896814403240b03511127851415044075000141c219035130307112100c00d01e0700b03504409090001c880d0b00006081c01142840b1071400c0c01002d0500042803607406540d1040a041350050042c10038410100300c4403107a40c0c49c20034096403140c0001200000b55101c001c0c01944000358068040c9100c0d69100b40d2030a818140b20b807070a01c3c800541490703410307140e040c2004040c010181044c0c0b52484188031465940f4000e0000c0d1400d41200184900c444049190040800089010a42c402d901d410381070705088144040501c40c80f003003032601040d01300d107050004521600019010b002c061805c040c00d9100100c590040058038001c0f40d0101c0d4940c0d0b46001004c4242d40454105010400e448a40c000a00c05401039485d120350903044041464407180819105803440c4c0700034010754481064110542411030354 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 618030611 1250 618029361 618029393
    0x302030c01050a050d02030a1409070608010f03030e0904020127060e120a02010c0507082d030901021522060207062a050f0f16050c0105250212030a020a 67
    0x6042c002e4054024000b4045c011400c114160000002900902168040c10565203003050780005824884081e0f50f440c4618082c1c180405d01180000c59034011503080301c8101c9a044e9962f01c01050b00f002401940c040141c0100d05001495518400200804009200d85100007110150641c034200c0024800d4004801c0c042c0a500c40c10500c840f581c5e40460301c51034103a02800c10b100c50810500d060b03480c24a950344810807078010502188200c43d1803004180240418a800d13500440038001c42c141c4234030422400c240541c1c01a0f05445400700c1000392658441d4000300d00c0c00a000c0604500d010210f594001241c0960340068084201701c003510032189546030f6001808000340d02c8080c405402441110800f043c040c021404051114100c82165100e00c0300b4402291250200905185410000d060032a9140075a01000038503500c0703081603035210440002c0d01c9a003d481700340940c0449022030341c1070303800500341c9260111a00e0708000419000c070f5268002c100c10034060401481c011000ca01d = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 618031861 1250 618030611 618030617
    0x9010632041b03202b0e07052103040303080a0e01020d090510092f0a090509060c030c0d0911040501030b0a06140f1903170d06090b0306010b09010e090a060302030c01 73
    0x1680600248951045d14410301001c02da00744440c014a4414880401140d004001c46084c0b0f041c00c030748190045410310894500361107540b400354900054100d03201c1e501b4602203195000784001c0010074031030202240c014500c0381c000a00c01c60103c0502c1d017640c0c44030212440d8542c03181d00500402c24200304140ca420640e81041158000b00d035070ba180c0e040d011420019040266806c091414038041c02031102c64040140902405540c41c3c801502400c401c45441c0c025005900005040d400040c0890b8070031801c10407114503201145400500034000c01e1016502d0368041d00409901d0b80302c5109030740c060f44c069156105245010f01102c0141c981a070003005110300f1040c401d270501c0e200e0b80401c2d505807504484629000000d4526048203455682c00076244007003402a042504440784020310404001c64818000b0303603110a40e2000b5110703020400c90309035102c0001001140f91003800f42608040525082c0c0b0740c0781d107000c001004c4181c151883e000740755444e001002181b03010024200100130a007 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 618033111 1250 618031861 618031901
    0x50304091d010c120b21010b040e0607120911270a0902060423060a0302090315060d031101110c06012324040f03030e0909010632041b03 60
    0x15000505020007005036a60b1503840350b5400c4d54940d40c04e0024070010124146c02c0c480311a244c05801c0c043c1080c241c00714081ca240c40c01100340c600300820301500c1030480740c0360614842c10060710200109100d1200b034941c19440000d203002c0760382e000e000404507241d0700e550743c203940c40000410550b1000a440c00c000e03540781a9001f8010381b15002a40d046498003d4604110481001c905c0002c040090900e80d00030400103551603529010b5028040c00d01c0150f0450f400140c0074004076080c02416510030394062242070000c0d00084c4100000b240300d24804001281090783c03407000e00c203280c11200160159070407200051041c1d0380410f8000704543ca0880c0341c0d5590481c0d4401280da440c0300500400942c091070910092010800380c2110f0090052a0758405010340c0c904004140201e0081d5852123580c46c18007040028005000300d0090703481d03a01d0060701840700c50100c58540d02c0d69002c600f03017008241081100c0c3e9940c0b03214031008005900c0f6540020301e100e5400800b110300344502000c4042c0d400c = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 618034361 1250 618033111 618033131
    0x7170f0a111908014713140a180c0e1c051c08070513030c030b0f06090702030906090f030d090f08010e07141810080706030e0a021c050304091d01 64
    0x50000312402c0e1950300d44040d240000e855500006900c41002401c1d000009061017135000c001c4e40754000c1f20600242120100c080000300041000d1074418061050034031100c20500b00c0b8140e21501d212611401c20540c120784110101e802c0083c10039251820390003109030f000034403000f8040f40304852a10251410503a0004201510012011b013090040010205030462224410780c0440040d503002500d80300040c2d0360380350010310703203204072a80300c0c00056120100d01a03050851081e80107410540185003410020301c18070a058210981d502c4d4400e400c0d1500c42c4031a107060005011a0380c0d1544c032403460900303080f00030301c5014080c1d00400c1c00380e143c02c134a0030b04001c1c04102c1e101075468410081d2413204103900042e81018041c41000c42002000043c0314401120b441c040e000c0711703401015030300e100d583ca20043e0308507030242600c0890f070340002c40300c200189802e018a6440c10210304030041c1c0050151038542c913682241e0440010603176030344500150b02000000c02c10b10110460028003140a072 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 618035611 1250 618034361 618034409
    0xf11031f0519150e0606041e21050a030302030a0f0e0105040318080a030f03020c01140106090501020c06090910080a052a0f0111010f0e07050907170f0a11190801 71
    0x894813400048003000404543c099452100700c800034408040c20f042012914152100c0005051085a000d0501c00c518414415907030440d081c1041e4100001e4200c913603c580f020745c082d610081246690726580e18125201c21000c1c80b8071148442c41000000b240d00e4280f6001d04400002c401c00c01118075590410000702c03c0018940f840c00358580343c120001321242d00240d01902440c802d854581d401c1250381c5940212070300866048442c00d0b5550200d087e5900010f9848204140303600e500f000e02040b411070a4100000e9080d0018014030041c68195a80c8001f43d0800b203441c02c0448103a0002e1110b00c100480b032141d00310401d80e441c2c140b0f401c2004103c2c00a4080a2001d140905015100440030b034000d8083d8130070200304001d0007084c404456204403032612001d8078094a4030070030142d4049800140f113141c22882c1a041c880e210143d5840f4445020300048000b4503284070b50fa280d0360042c880d00e00e21780140680541d12500c400c25001380c0d09019184540507000f682801003100420700120803 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 618036861 1250 618035611 618035651
    0x21010905151b07050a0b180d050f0f0309030f03011203031407091202010201090209070f0801090209030d110309030d030b03010c2309030f1510120f11031f0519 70
    0x1420b0b5203940c0d078411407440d00b107081c50b100400240504a003841000101c00303901c80b0b64040342080c0c0041c0c03442c8a00102c01540c0d00e02480c44600415401405424070010141c0c00554000a101d8100c81c144000c503140201030340d100360010040d10000701a86410550980154813020744208a5081989402c480050080780c0c50701c50101224482c041407001d40e4001c1d07004040458004d824130060b4540440042e000045042c0740d04002801e020001900002510a0f0303044850018040c00d0700400d0804100d4406071280113400709800f08106401d8156020482112a10801c0d100072518000304804c060849900b914218140034101e00c1008401c0c00400705c50110494031144291501d92000100c2d203800084a618182c501c01c0b404280c1c41c00c5140c80b4480d01c1000b00396800d0003002c1c1c4813207024542e8403942c02c00401a81d6000241000945401c02410100401030b0480d901d844050341050841a07a012a01e02202c0c1d40f0360502030801159200d849820300d80702d01c02d0203414075044d508201c6078 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 618038111 1250 618036861 618036901
    0x20c0109060e151c1a13051b0f0d0f0605041a10120f0513020a1203020a0303020f0903060a0603021207030b04120c08030a0e070501090303050d0b2101090515 69
    0x200d800a00701540c88105181d8903135040c46281c00300000b920440300070f82c1e400b24183c1410712810020104490981142c0200f070320950300109a00305007403042c41c03004010b80140c0040d1195003000e11508400303010343d05c602c01c0001428500460503a00d04000d00c003c56084a1501a8040421641e80c0079908d030881140401c504034035240340d40c81e1303544150100606500400081e002c2c20b100c144400d10703c40c00d0428103400d00840d85c81d940b180d0b42c2c0c000205800c0300500014096003001e050030000c240654081d10019600003204c600c0c020344140040e0602070116004100c503a620b400074000e50030000070880c0700c1d461440040046500710384070110084c80c001d100030045240300e8011101303a84100504245190300207920ba469080800750040a040c03180e02400f00c0f0b00c0b0b020f900140301d602c1170b0309420403260981c807034614045441c41a000074000f201040f039005821811900500c550f0014281035809050000003100003403483c2c80c3e41403002c01402100d10b408481c06001402e840d01c40415101 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 618039361 1250 618038111 618038149
    0x1b0619020f18040b03070311091003050a170405090f2e05151e1b0705090c030601140a032702060912190b1e04030509040e0304030c0303020c0109060e 66
    0x804002c030009405000e900c00d10907014040d400b000010004040c4402200d4407044614541c40c0e62924410030b0307400d0452001074001d6010f80e078110081004107811601e0701c100060b100c4d10706070b00d50f0003180d4503200070340d104044005070b0402c00105a09071000782045030081d4110308030307007071440401c01c170800903a005541c4580305481c0c5509000e810b00041341e410014900c00c0074541091441910240d40140e0228044d201c0b000c07800c1c03540200c1c00701c0c4100130f9410040542034283c03160070428010780c20041c803050601032030801400300008520058681620030b41c0d00410001d9002c81c258440510030049a800f043c0c411040c900181c0e61300c4c043d80c1c2070030010354a040f0501c4001039040d00e00b200000480380a941c2d000744844c140080445600c2c403d00c0e1403045111003146080c00340a45000488001c0e0008d282030040311540d15180d0041c4c1c070303140c031450112800c0a48903110111070504a900440159200b8800c170a00395820102d8500285054180301c8006401c800106030303c080d00e0752400d0f0034 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 618040611 1250 618039361 618039397
    0x270e0117150a0207143c0616030614030d0f02072309010509040f0809010c23060105010206040f121b05070302090606130b0f1b0619020f 60
    0x40e90004001400a40c1c0381800d0800c0d440c10311904010080d4003801d42510041103001000440d1180012001400d010000100f4201001c01c5121543c200c00060307095000500c0751381d02051000b0420005006105d1212560710000d00d146029089604503849005003289c550758801039903901042d20b61080e0302c6400c01030030b06202407900702e0030f00c0c4558004c2100074805002802030041829100a1502c400f5507015071140d032510304002d441d6408650040c02c101010482d0350004030b805006e8001d000040c18022419105070760b8072220040f154080001e026040341c01d5526a0b44100151401414280041d000a042a032258050420780c400042c00040c800748448150350311032109905400c1071002c680c40b502d4414039100761074028030b2005031312440014021646038607054003140c81400c80c5019100030203187c1620340d90a42c100e0a40707554110410f0262441c0440c000c07150b924101d10301c1010306001d2800144643c08142480f444041d454414050b174500c48080c07004a4450300507062131051 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 618041861 1250 618040611 618040649
    0xf130903020307020a0f050a09061202220204030f060b0907080a180209090105071419211401082109011d1210050a142205030a270e01 59
    0x3107940309412000350001d441c0c00300091403804019030070044e0781c008ca4a10800300d82d02e40c6da98080d0785040c000c24011600020740080149406299071134240068208060300c00b69002011080ba00564010344020007460070400404c82c4501c24002100e0040300c2440d40d500740740d4001041c14600500c69041290740c0c040b203010002d043c500c0c07981901d50062000440f4500103001e03034041c1106540980100708480c0d40e8a0140f503001307040e44c544d0404411220310368404048200c84000080f540440105a44c000d003150351305290140712000440c0500fa42843e514041d020381c900400c00425064590507139941c0cae50200f01b1075003100c800c240246420042e024820400d41d0400700d0000c143c2c1c0d03010303400d640102c0140c940030038107916405084400f0001555200d94800a80e4058000118200d881100041d28903d07051002842e002c4000480d88a4a405a44d96031440e8044c000d40e001052224083c00700303104010141901c5c1d420740c451070024091a00343c0300e110a039018065074245c5408400545 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 618043111 1250 618041861 618041863
    0x70e04080c0613030e0a1503091104090c05030f070f0306020304030210050403020d1b2a0312050904050c0705120c0a050102040e0f070f0e010503040206040905041109060f13090302 79
    0x821540461050321910305100c0b0f42d03004120706040e811004a06264082c0541e450b05451070f4048a00618601c000702c94540b40844c001c090880003121100551031007a202c5464611415800728031604555003054240344c201490303d00744580700c076200d500c00ca0382444003d01b0b4400690490b41c0c0188096220344444c9001d80c10641c6001f21341047da49444100000d01d6800600360302d030100d480d00c50700f007002e01245a540e004c60f5901d0000c1c0800e03504403101c003221a50903100300030f42402d40ca529000551250b5901052825020b4080002000451500401c2c64075100389a0408650011640340150b2a030740d1a41313950043c1451007060402040e0140d03001401c0c45000b1060390b1002c000c658442e05c03528103105003401503c0280703401401c5000903500500031180310f440360702640c440c150408000401100e5643c0018000c80c0c001106220000760980c180c000c0b0707401144200e05945d2410201820310410310030040c1243d1145d17001101d4541180c8566541001003184141c001c6061502c6060603 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 618044361 1250 618043111 618043117
    0x2150c033a06180603020105190c0f0804080601050a05031f020f0c0a05010c0327050304051305070305060103020a0c170c07260d0905011107081c020c030609070e0408 73
    0x4003681c140025000c664440c8079841031041d20b10301c2c118201c0d40c00020110310b04607803d50000074081581080a9501c0b030170b03440040c1920710007514011407070002a40c0d400109427140c2c0d008541c10790010400348a403460520042c0d024100c01e03a1200c25042c0b90400181d078038044a0009428150411032350700a140c0320b034048a10111516001a642e41c00c85001d056440e40404002d0390154a40784042c0f420340e00c40d00039400000b00039503e00e40b910751002c003a480c0e031000381181100c80d0710080000003140d4036100c2c0201d458084000300083c561812030385c043c0540700010700c803c2c1090300c1004007100183d0411044003483c0d4022540580795401007420940c10310501c061401c062280840010f22030f4407041007000405540c030401030a0741008582203691b00101000c1e54080340c200d0105013315441480c03222203120a082c211031074180d649080c04c3c01e051000c07900800c211400c04080e64120340400075550070082c29001040f803480d15054803038030740d107880c094801070768054070105050000352003c0d = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 618045611 1250 618044361 618044437
    0x150b030102030117011802180a02071203020c060f0c0307050d0f06080c15040b03060609011809050718030b070507050f0102030108060712020304030206060103020c100e0a02150c03 79
    0x85541c0c0d44c48194004401ca2000d40f505440d6007480101c44038000304841c0c0110141d030240040784c1c1411180340786d0820401c0100f9107100c0301e07420302c0041c0209a0361880729484090360f0b2001a600c000740701d1360f113040600080a000759004540c040c4413000c0250411030342e0100031403925a0300e507c12071000c2009040941500e403042420078001203800d5401250198004208440e443d002ca00c080c0c2d00366480d1302035072080c00c0e028641440020400d05003403004202603003052405044514070030f0320610395003041d43c0040c0e181a5541e401c01c6002c68000001c20f216682c9181d0b0300f042189540c3d1030000c42c1200030003a03420860040360781004c02c2001c00c80c01102a034898009c3d500c03903840d8041580d40d25011201040018545240006020050f108483c001ca4065014150380c0d50b5580054010f9070000c04190f150340300c0d5804428001519115200251017403070043c0240c500e07a801048403100341e1b0f0500752600f460030014014140000002c81d540c1c1524040303e0400680e294035040400011401 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 618046861 1250 618045611 618045613
    0x100b03160e070e0a1202091b031009180c0504091e030e030709290f0a0b1801090509010608190606050306100203130b0912010e1e0a080403150b03 64
    0x31010401c00c1c560507038544105101d603107101c107800600c0c0400405655902c030700c00340c19207441643c1c0050b05199041e83c1e402840080c0420007006110307030148040d80121504410000d01c5035040c030030000c2034040c0280014110304050001c0c00c403900c54a60b081c2643c0701d8144280e640e030006000f0408440003141c482c00d09803041c41c0a980050130043e041c07245d003c052512038010322501092103d00782c413a81c03c4040e03580d8824010701c0344064440c10301e40c0c201c445c60344d4003820309550070025a42e5019100080d00e8644101d9441700f288012520388030012074201410b201c103995081c0101c5e283c0d4020281150114501380c0225100c00e14030840940c02c800c440058a8240040800d40e1a0488001d50040302e06071512080214074100c01c03038603401603c01074107840211003410840c60038114058008490010311941010148403801400c485101c4403181c85500040440141d1440b9155240d10301c080300c8000d40701d18002036507122600d00c030768000140001529042540b00b0745641d4000f07846914013034 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 618048111 1250 618046861 618046903
    0x4050f0d11060c0601060801051815010c0204020d060608060904050a020d03140304121211090f0312030709180c050f0a020f150108101b0f1211120108030705100b03 72
    0x6503c054803010240070380307004900544000980c0303041002d03a0601280100d02c01049640350302000720b0304058400c021a04010360240c00c440544c2e5184020300200c400c00f038001035201d1805401074030b01800108102e104214210400c0003244010400030030382541120010f40c050039500d03054902001111505806440100402c0100682c2c28085462541e59445850840020f51010b00c19200e0441c55911501d1040c0151652420015a491025800181502e041c119a00c4610b680b5030001c407000d000113100010200319080ca4919a0788503a400300e07101b440000f09500f40a40750707200700941c0c401820000140005c00f14420b21a2900a1001070207070380d80400307500d026415049080c000c40d03895000344100009940d00ba40700b40345860001a1001807203001c0d030b240c181c0e001101c894242c8103105030901c035044581180e1146141c000138904e0941c2d11800003841c440c4210905030808946640300308451800704500241c203580e0120784480106800141002107800c1201c0b038403074803814003151 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 618049361 1250 618048111 618048127
    0x320180109030c03081215130c020a0f06050a0605100206070806040605040e060a1a150d0603170304150506010c061a0d030e040b0d081b030f071101030e010204050f0d1106 75
    0x1170001032030070030003180d1031910303c2c1c40310044e1655812141f40c14071b91000c5280703404485c131400b40e00680410f01c81c0b801a030b07801101640351040c01d4007801e941120b540e40d542c3d00b041264a840e10600020b000c0c1900c01c03004183c001813020b50b464001900d0301003405040350020703e4541c0c0b1a040000600350141090254403000383c0c2a983e04d031001d403038030032000c1d007032250450400510015882000720020021141001105d000c1d603e10340c00300c0010030307031203860740008800310f914403007801c2c150100c5001c020341d24500f504181c0b148840800445078580c1c01c000500442d60b921200070781d507803500800c1c0006c500c1d000b000034034441044810100d03000048448008141a0810f141250188040d10180510b24400040007d03142140b003004002940030300841b80c0003002c44d15040021f244201c1160b192003005003500c3c000b5040018100c9070099200792001c525681030280d407a5007500304009604040c141307400161090700c000240d900a8002408200501100c292a0600e0308030150002d9510451 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 618050611 1250 618049361 618049373
    0x60f110f130504020310030209041a090a0b01121128090c09051c08030702071d0403020f070b0a0c02030307021c05120c0a062f04060320180109030c03 66
    0x120100001c041d6071070070005541c1440e00860348a046016480075007141598200181580050015629011400c52811100c1c2022815a010300300300c100a000c4041d4920301000f121380160400121004010040c50000340c14070305441504030b048a250b480c1c020f00b51800100e41180c502c0c11015030042100c000b5200810358002e1300450019a18443c2032900e5409104220384046201744211044894040200e020200659004459031040e1484150b40746030314001c044079455152240344903d014841055010000100303002c41040c054002d503454010020414001c002c040018801b94129060440d64240202c1d050580d00400841e04090300c04c49000f5054030707405040701c540c4550a000110e108107041990501d00424008001030855551a02c0160000c407000d403181060750b240c0d8610000408002c11985160080310301d88551401500400f43c603040c0e01091000242083e40000c640500d604440c030650201800e44c80b60b400010040382c1c00c4801c0d601c06010422640004820404 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 618051861 1250 618050611 618050617
    0x1b143f070c0b03091e250b0f2104032307080c0a060b0307032a05090708060108060d0507050d0c051009140f1e0a080f010506030f06090307060f110f 65
    0x865501217405243c490704038161081d81c5a4201e00040d03014814980b051032030780d10350190704000030144004e16039a41081c020075800107682103007041d501003520f80900009550440c032503019001c0f248503900b095200030f403a0594100b107450030454010508100d00c481c407021201400d0b072191000d542c1d10010403038662512401c000498520f0305180b0010381c90301d40083d0a5059940240c09a15581e642e0014050940003010548400802d610400542a510001910b1041c045a11620b616260041c00100b03000001028244075a00c0455039402003800002e400c1d0503038106403050321000702d142c00c1000d6848100d5000381c1c2d020100100304c405282c0c0c002d82031411281e01c001414144082c22081291480495488541201d010040c5010707001d91b40480704041c2071701a040001407a03d40b40d103d070a003240c480319040c4680d101d0b0248402801c4c00c20841c00b00f2032103940541020706000c2c00540e01c0c1e01c5220b60150159441b4041d85807010103550000070f821800c600c500c0c3d602c001d2040410b210f90 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 618053111 1250 618051861 618051871
    0x507021e22090b0a110a030507031e091401051006110a02030a3c0201050706060803031f0e0603030921070e070806100509101b143f070c0b03 62
    0x201030300100314040f4250144c60500f1703840c0c0d007a031070401d100701600300d00404000707100a0030941c07a8041c0c401c460002c151070b0f500503010321801040f40c441a0074140f0801d0034220141e135080e0f1516007048503a40c0000504000d4904034980a144110500d80c110700c0c004404101a40c540501861300c810045d82c2c89a241c0c81d205220180701c08102600200c680581070000345034000407407003005600640c07040c1d0007840b0b0144a00000a045074039542e00d00c0c40c41d002254040b000d10040b04484005040808c3d0990041140171080c500d41c0c5044804a900ca000c2c08030381c02d0182e51240003480448400807400c1140404c844112a0071942c0e400130b2420b4800e0075110400401c0a010101d0f005040a06802c007000c030f6540c50f07240c5840017000038001204c1c02101d01004110310300445841e0301034801400224103000d03a800d1841e08680420941c18103168070304081000c40c2070348014100c1c2c003241d10203e4039008511400c210010309290521024401c5120061210280d501d000c075948503048040c502407 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 618054361 1250 618053111 618053123
    0x601081005060306190912030c0e030a050c0d05100c05030402040b01170103081c0513030305060603103302010903020106080a080403081b100209100507021e2209 71
    0xd01095a5560112041568036540581103032000400342c03001c04107518050b42d1144400141c07400562a0015035012044503540081e440d9103450b4042a03010b40d0240ca240c0086000d01480d08065035020b94841241d1000c0d401211910101c03c1840f5046c01003840c1c24500020a20035650100300c0140590310481d0300302e206614108030101e02d5481007404062552000704c1002c4aa4250744880915070480705119076000351310000c4229021641c01000c1c0102c003804000b50030048a0f00e005000d50b00007d006600440c020310801400003205640301080302e4003100002d100300c041c002505203005810a1030811040c58542c2c1d007100550542c01800524020f034000c00203584c85101083d15060365440107481c001e402e10061003c20000002410002407585801c0300c4000c500405071b042101080d455498603030b004c240141142481c009420307a880c8a840c0c15407030300b061236001811400e01d480c48030075189840210b03118a502e0749270107020b45069445009100044420945028040b1140203e0b41 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 618055611 1250 618054361 618054373
    0x1203090c090204030b06010815180603070e070507060b0112051e07020c100509030a0b010f030501050601020d050703030c020c04020d0e07080f06040209090c130b011d0108070c0602040e0702060108 86
    0x8074507040e200fa101500ea00401c0038134076486100044a4805000d031000b52801060116101c842ea204022a420005564038030043d92070031104040c24003c9642c04400d03028032a10400c80d40980c840d0440709005d034060800501c0d0030104004a42c4070094000c142030706413504090060403095014002100300c0302d2990f465040d510364000300e0b11941c440100c5a040480c0b141e0b202c468500400c01341081e803034060704550b89074415440d481d4a4410a0780410f40b4041d41610501c1842028050301c1d0b0701034000c2c00200109903074004001d0052240c2c140250030103039141c0e420400c3e03503c2072280b1300c0801c00041042d510ba280f0800100001c00d428400c401c441c4c070850500040010011809400c1703c0c0100300076000a40d12502404041000181061002d004140e000c401a50b261790b1190000300040d440002c0542d0340900260040d16203130000c100008000d43c1414031070fa405400c103075000049107490043c9041b07a1078000040d000e550040f59000708920f0030401c40c654002780700c0703040721410005c0f241 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 618056861 1250 618055611 618055619
    0x3031e0c070f170d0914010e03031c09120207120201080c0d0501150905030c090f04020102150405010f060605030405061801060503100e160305060f06010c050105150a061d040b0d1203090c 82
    0x5620301035100d04069041006a04a165800788c54204c00f101005020749181004004210181c200c0d07400800010b51750380ca802c1e10610801890a1045492034002440c456080c660b10120b010b03506440241040030440010f025040e00d44151281100c5c0e0200c244010350716514001c010400342c07258200015400980015507290000d4100405c19000c1d00c581c00c0d5496159500e014a08000c2c82641540b1801032422074208584004500c40c0d4000c0c000010b05400030610542915407a900640c100102441803202190021a0320358004255402c0c00b54600300300445079000d051180e0007990706008006200320010820b400a000382c10080086d01c44004031400c0c00c0003801e0040c040580b56501c0400020030315005008000c1c0c0104050501408108031603881d51700303540c030441d1a11101c45a1940c5202503091045500d0301400040c02c000c4132948941c010b80b0340d045010a0841d110300d0702d03084003030101e0325204a514051074110816440b11515118040d010300310455007169000c0b20900001 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 618058111 1250 618056861 618056867
    0x30f030c02031c020705070b03040312140405100504020a05031e060a020a0c081c061409070e010c0b040f0515180d0801031b05040204080c0f03031e0c070f170d 70
    0x43c041e00e00c125820b1961008407001000250004001113a862081390b5001c10f00100d030710b0165204910913940c01e01895105038942003924001a5100c01a1300d0b00d40c02d20002a001141483e0a81c03010140010700e66268000103000700c025501998050003506a41c500915522001d0381545040c803044842c0354503900402000c0740324800159000890a003040c00c0040c0c0340780d006090300101007100c2c0b208102042c0404c4115452940504408200c1c010b0003c4241402480507a0200c900d042400c410494007002030541004040c0083c040c3c250a0001802c104034004c400f00455009412940e010561654100021205450208980221030805900d400300000c840c140c00304207944507400c036461980d40d4410000e14440c410211803c80d071000c10701e905d41b44041c20085c6030907002070252214841c24014400359020001d80030b90820050440c10f20000001521018044030801d5652003c07001301c0303070030450b241d0001081d041400c84c0c00116141425003000104030108145d60b00006950002c0d = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 618059361 1250 618058111 618058117
    0x10e040f08181c031107140d050312041b08030708120c0c1501060909111815120f07050703020d030b0607050a120818030906030703060909030f030c0203 67
    0x1086010840ca40c60005903100300541160500003400d1a030a580c02c030001102d82c402102d9501590503480e80643c1455880540c2c2d00700b900f40714001c2c006080c10614800e00b14001c02c03c00600500000d0030b04410040d040084421210270003860384000d00f0145003040390342008801c0c9407081020b85602040300308020040380c0c15543d01c4001c852600c0060754410002020003007200807151418018501e10071018001d42c9640780b90b002c40f921483d8107280010300021680e4100a501070300e40070300780000c07031490300c12111200500c4511341e203500c4050001030491100c0f00400640100081803ca94048240341224081c1039a0822600e1a82d180c0c1011100350184071809001030317010011440c7c5180c002c1e4000368441c000548405d2a09909484052400401c04002c40f9161210103886907150b0b8084445078211782206451403210070b01d1518650fa074020301c0342c010301c42e00f00000400c0790903000764064001020004010b01007071020341030280c0030120310044600400d0a180d0029820b070b10100032 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 618060611 1250 618059361 618059363
    0x207020901051c0b10181e0c0207050f150c060604061a030a0e0304080d1106070c0c0315061a090f0103290d170c010629090f120f0105010e04 62
    0x2803902030001d40e131509440d40070058581c80b2a50390b03011011540160809428120074800c0b103010603255078841c10400305882090080c1003c0b4900010052990307400308201d411504112249202d4400041c0050381c45420891780d80c0030f0350400241c24a9684010503507510403801181e0030480103503603121503143c3e20141e0113155080641000000c166540950020b100f280b846d004032810181c407900c03094a003100080700d20340840c10418a0704038940741003008650100c0c96240000180c44c0740d80e20301ca03150040740401400c0c3e582c010307000340d0030000c00d500c81c4d4020020faa9070071503510600c0c00300a540703620000d0580e00560051003001450f501038080c1229103142c850444120400082510602c50300d02001c0940c402c000c5040d1a01003400c0e0801030885040f018015584c800c441403070b05003184e0007a40504090b0840541202142c1d0902000040c0bc400c1201d03100d64a0203080001034191440c40c0140364810f6500c40d18044d0010001481d001510048e8020003150b6203641955644000c1218 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 618061861 1250 618060611 618060649
    0x270402040509010b031819061104050a03030528081614030c0d1404061b020616050a0318120e031f091b0617150907180b0d020702090105 60
    0x2c010040111803500460380108404034032102d1108078a13965050030209481c19100b00d03a21a80754041c4061482440c0e10132000c00300c82d03446c00b031421010034401941403001805010740810054440001b0003682c10300c00c080750030b0804c81141400400b40a50800b540d12050f5403610390204101c440c0150401c00c01040b902107a01d0442d66588000c13402a8040420fa03815180c44100380c0e9011042000c585000b98131880c2c01203800c0c004825943c1d01e1200400c0e001c400c5502607401d0002050000d05c458100b01218034203103a0710001400b003130300601802c428030032109011880c2d01c0c00f80420324105a580001d9aa0750161719409a010185c0e40c0361030b2101d1a600c0803d46c001900c44824990082c2d58841c0305102002c42d07040900048a48002c460b0711080101d030320300078001d03250f08200b1440e56000512a10700245540c0c04008500755503002402c00e014080302d00850300021044481c2a0010000d294142d56030345449886180030f908800d2080780142c03000350010440b4608404040d078030410b011 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 618063111 1250 618061861 618061879
    0x1504080105420f090108010e010506060a0504090b060c030703080106020d020f03040e040c1d0402040510060c0b060301151e060c02060f070807081210080c030a0204090809062704020405 81
    0x40780c41600302a1151141d00510400c00300483e078544650050003085030030000541c50294003005400c6d0360b0024640b621944041069101c13241e003000685060b503000c0480054085080000700d9064820702e00e82202901c0040344c0001050303070049850b4140e617401e43c2694994000c2e41d000343c0c0d981d4a00860340b007a5420921041c4000c41c0542001c652013802144010a840d41e41c21892200700c010b0700c50310800c000301c2e108020950a0500803580c118000804241d280380c41c0c00801025031044090082100c003820020a01c84d541c2500004c84500b02165910001350703440b8400c80c10101410607038210fa07145004d00051141c051035070307050515000b60985151540c44140c810700340d4800740003241e0128080c402d0030040780b000c2014020000c0701c000040081e0800c1d000c030300c01d034070040d61020481e171f8000445070005c0e8030080741c02c1010ba64144c41c003190448840c940400b0354000c0c0d00c542c0703401580229210105c00080070303029014084215070303108950354900900c42030344228010650445c6ca40 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 618064361 1250 618063111 618063211
    0x91e01170118181e03090e0c0d0903020a02100905030f0102251a070e1e0f0111101503030807141801051c06080c010e030a02040b1504080105 62
    0x1504251011038100c00d0825000200f540c2d16220b40e40b502c0042291056404c104500b09a08407020b072010f402e0307034408240c003840c10400003626803040c014450034003925200c1c01402c00d8000c000c8440065401040320100c0e80c1c54402c020f00750041c600c0341c1c40c800d110b4170401c5001c1d0301c810b10803210f002059084014203184124bc0074805d14440300c0e4100c0349180c032001da84400030054011240100d5569032401c02411801e401c002d00d00a54030b82200121003944a948559601e00350b000c40b100300f0a080c0700756201c501c1404c45042c08070001c1c6019086e400c00c01000601151900d40d60150f0b40f0030744a80b111a181c840c1c4c05c851311061480002100101003041050114100400c40403107401490030300d180c030351010040c044400100c80045a1203450700700034003a282090000c003c0c0110b0030700c1c1080c400404003000aa45003403510000c1d0248d962400b0350b800f81d0702e40c0b08245218100c1d81d010b450365150f84180990007440b080b10b1902a075500d0001e8044010256840003524032689607070505400b01d0 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 618065611 1250 618064361 618064409
    0x20c04150504230f15120a03030c030906020708070b070503010e041b081b0f030102071a0402040e0601140a090911041e090c030b010e010501080a02030606091e011701 73
    0x119160089079688400b19860f00300a42203c40e100740202d05402040c0c0c1000c008207411008484210740c402c0f401400e0704032595400045590703400d07415240110350010242c0c41a4000c1c800420003501c1e4a00000d2100b0512035041d0041c07218600c14240d58204da514044e088859000a0003040e82203004040424041845c48291117440e0075960308a54646540d140c42c14680320340e4416501d001c03801c4070190904c52405610300020403400741d00a502c0c040d096507030440354a0508050a46d51804031000c2819511a6403220b0301d00c8100c94112505c3c2c0d6114070b20112201c02d060100780c42400480b10108800f81140102510b81d9440556408415840810400038100c0040c3c450908003201b148170516a40c0ca01070741243c03e02811410401600b10f081041440300140c11445103020a040104401c0c0d9000e560180d208140040060b1251140c000080c224800c400c881c0b0b500c9170305100c008026054a465040d00650300341c1703823002c03050802c03070809141c0741c1c091003050a01c0c154005031810b0301803 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 618066861 1250 618065611 618065621
    0x30623100b07051f05100915121403030403021005010b13090b0d12050705011103090303190603020607240911060a020a2901140d08090f090a020307020c04150504 71
    0x111039030a98552088800c0406064503004400f0b007402c035145c4040c45581c665035003408010f01b09600342071119900c0d0401c04000130348944220082c0c850b03510940d50900030070840c420310100707410042e603542e03050509000303680c0d00c41842d010030400c3c90100005030252049080b0390407038624011000c4164a0070103044000d11505140c1e075008141c045888001803176a14050340c04500c03980782c0715100d40150602600b15064050f03900700d2038200700280305004500101b0340f070340101003c2e1642c40300c200e00c0e01b01c407000e4902030b032000f5040311021411008008600030300020200b1a80d0034a440c0040c202c0410782580c08501c40030300b131449207111b2101d050811000500c07042010340101d078084440b0765240403005070014211520102d001c3c1c020446207105120050051590300540d4010144000004480b500314490003403514000050000c80c54072001c5940f10400741c02002c0041e00e203001e11018029500c12150800140640ca17910f50f06490584504816200c2520222911900b0300f814000140 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 618068111 1250 618066861 618066863
    0xa031b08070c0306021804140112170c0c010318030c0b0606040338010b09060715150806100b0702060c011d0f0c01090303050a0e19030623100b07 64
    0x108080200c0400b14010310003180003148204001a0742d48101180443d0011280000030f1045090006101650800520b80380c1591302c41c08c000300040d00c461501d101082e22141021050036800f040030100c1740c0c070105040000b06001c7c0c0b4203011141c0b16816109010b502d01100802281e03616414001055480c00c4040e880314003e04280d1400e6200d846031034455241c0c42500c0541d4800a440c0c0a10880041070ba4002503800215044954102448221180070f8480c40318019a000b207900007d03c541003581d496006075000041003046084207004021801d00d009a08451040d5400b0920051521185d2421190000000c0381232104075805c00c00c090f400303041022003030f641320854203c0d5001c07a842e0685a00e4200002005e6074070b41260349909042d0a0003601e4140460100f0420121b40c0040440e00100f00031318101602d01d050200146414245074001e0f01d6403c0005001710030880c9903800071031180009001c107000c40a28040300380d503c06044940f40150b8113030320020804c10140c1d0300548881 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 618069361 1250 618068111 618068123
    0x705030708070e061308031e0f0403120302041d0610020f070b09030312180705061e130308041e050427050309060f04090507021c0c0302150c0301060f020a031b 70
    0x4005c00680c9442e40b0090f08030412542001900718111101c5164416403d17210200c10740c18034802600b494010b00440c80041c12030305d40004039142048c42607045030b000d005040d0300e5090305e0155400c1103080010403a149405428100c00d9110a10300000780307001d4541c00c02c0b000b80002410008011056004440d083d900352005200441c031441c5802555440381210385400c4a42d511803034036107450041c041d0305c4240030b400e00f0813100c184840c0401e203180421078402d181c0e6613034906548482c6015202a4000342206c0300c08503005c2150020859545c448080e031704141981e45440e1030030130049407125001c181461600903c0c3c0213030130481101c1c0d000f10718003a0b400d49007892050b0000c00c1e2198040484101c5400c0c0015042c088003801c0e2082e25042010b0384000c0060302551911070f141310038018151800e2240483d02d00b41054400c11070711860201e580398003501c0b42840300304644a41c0003070140c24049134036544840c5105100003441040b0540560320504d000740b1042240720311514042d020391762 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 618070611 1250 618069361 618069367
    0x307150e01090b0d02070519080a03020309101d0d0e0612040302120f1b060708041509021c0203010b090412030515030109140106090b09060609010314040605010e0705030708070e06 79
    0xd480c030b44074060004c1c0ca0000c2000b5940d0041840d10300d0910215600180c5c0310b540010107540826206010364a18042ca070a006030750b900c4042d469403500c007182080042144c00c00d10100d05a00c05101c40301240c00d440d100b20703084801c0c800c41c20b07504801d0380c03407405411030b105000740322890030a899065085406401543c280d4441d203100900a40c1c06440011089200090318000b4140d00803034400248890f032014003040d04001200511841c00a400a04403c20b00342c0a420440019800309038016401080680385c406440c03003010300d41c815600182d1082d46403459009450070804003203440b03a41d002c401080701c1c001d011020f400808002c0c00e407032100c88600000085c02e0300c0c01d04c6583d8049019900400b40e91088400755401d6480540112202900f0140c0d4a041611505d601c01d411402c2107a04a88130b01c11200100d004144803c40c1c105016544401d11040c040c540c1d000b2410380702c104240c1003c903a102a015101440140c44020000f01c9030700010702ca040c030a80308600102c80061280c1c0c9 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 618071861 1250 618070611 618070619
    0x901030b1008160e090a0b0f060a090306060803041505030901150b0c0105060307080c01140702180403080f040b0a091a0901240501050301030215160609050c0307150e0109 75
    0x1d07a81c86031261000c0410005014440540e19140c00500c90300700a00d8901400701c00c107004104940e07006000e2036001601c42d102460796a40702c030820000f100024064a0f11000902001020f0809a202c1520070900d803420128815101004980c15a500b90800790f2102c4402441103400e0750004180003815543c6250701300d10506680750718401003038a032a8403038031031040984480c00c44002403d414846e90040508020004020980811741d200901b004c080f560006c08150005200f00075000790700000041c00c0e106007402d4600b80c0781c0564025501d140042d524032090101c400c80940f00035004051945c0084c024a12540005903401d100303000109070410355502c40500118140c0cac0030354880e5180c0820b07100c0c5c41d004940c01c040594070349450000651900300040c1440c40107000c041d0051842004000f50b40c140030046445480c499a4440406030703050400c0f0000b41554541101d15000f40e500c00d20040c540040d541007664900940c81d000400000002d07100a11445000c03418415400d100003 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 618073111 1250 618071861 618071869
    0x50706060e0c090909011a0409051606020d090b09010504030f0f14030307020d08100b0903030705030408010603020103051e011503112a0303040b010909061b0e090c07020310020901030b 81
    0x1c0c050242815042d45806944040015298006141405d1a850484012510f451051401e800b01e041620000380e404080c0c2410b50502c0300c0c09007540040f001d51900000c5040c1d0000d010311140d80e0341d03600d255005842e100e00b151544600021540040e03010f01052000c1004402e072150341c0b41c46651040b2206045035200d4030441010b1461b09001c0d003001c0b003001003054051003403480c001c0192034406c54030700e00303401d0603200841507010b8042d41100200d02c40001c0d440400407a48150380050850b0340304c40c0c0c1c9024082c0070342460b0004030300080c2040701041e90f01d4000c00c0c5001405c0c0c150f220b00310b50303603080020703455160103810552010140c840d500c21850004072001040030302c0781c480014000c440f080429060002c800903010300f26510810801020510f0b030101181581e421744004a05c540e183e04002c2c01034030258043c0840310540440040c641608114000401481500c0c2c4000540c5c038648a082a4055060060341580242075103984030602d5a004100340041410002a80070121000c5 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 618074361 1250 618073111 618073139
    0x303230f04051b1c0c03050a200604080d140d090b0f0c0723070506040b0a090b0a050706020d06090207240203150607262a0d05070606 59
    0x3680d000e5000018002030003018005035103504036140e2214803005000010421510004208030304210a00300d040742000100c525407002140c0107070440354494200e007042c02c2c4d1030901303510b500a118004590702066081800c241c80403103540700b000e00b840c200c000909884819a211814031045000c021030015081c0c1c82c070070701e40b03840e00450207010301d4034102d20a102c8a240c003400d810302000003402214005003d0500c4d10348001000302c040e00041142e44011485c085e1a90480341d4400404900400c5003160000545525851540e40503c403543c0c410f01a0810700c156070841c00041d0080215001059580e002030400c2400203000040841c0c0d640c00a01c2203812408088404002c86004070491400004000212a0305600114554200014500b003900f52405280d4000c441c042000003c3c0501001d00038802806404140c08030540302036103003019481081d12049207400c416110070391b4000b444010301d101029800804210a041ca4241c500d908015400c41e006525040b0214180b0a81984 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 618075611 1250 618074361 618074371
    0x2100501090e0f1612030306080d030902040b0a06021011090d1a0a0b1309020f13150609030c1214070305010507030b100f0806030c0d050303161b030323 67
    0x4002008400c5100701400c3ca08001101c00080d030100022100d036085041d96441210503804202d0039014040c41c0030f074041c1503164052400c0c5d00543c4211220141c0640140350120720032a8200724050061080282ca030745207001c0e003c01a805042160101850f9600c240c2c0c4460742c488616052104100002d400f04090200890348650702c1c10740c0f030401444070700c122a085403c00300248080c140d030b4800714081c040700c00400d103441e0340c88140304025515445e003619100e203c00340c045070100320303100c01040c0a003507441c110755a078580071640015200d1040e620703503017600e503c4091161503500d400c2104408406105003600c41444985646202100400442e00158800c200110305407a1040c005030031070b1000d03641b807401080c00c4865034441c503a012206540840d1281821445a01c90b40d000c00e180c41e444a1405810003c9105020107104000024505c21510082c22080020394100e044a018030344206c80c55100e079040c0b1101002034029000b21078110a100e441d075503840000703507114100c2901611 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 618076861 1250 618075611 618075629
    0x140708092119090315050c040314010507080c0f0301050d171c06050d0203060406050705091005070204110403230a0b16020c061e1e0301080f0c0906090703090302100501 74
    0xd18009545000002010360182c2c40c24030500281c51600c44020741e060880c10b04640e5035803100002d074910003000a4030051078101e480c3c00c004030601c00f0381c5402040c003554000003141c004000140c541c4051421640300a1481455500b1640781000f0f204800b1100710040701c0a0521a00641071910300002030580b42c050030703003c565014080d41c0c030312003191225008a400f42c407a50348a00050386001070040d0700103034441000990303945c601100310f81031f01400c03020607880341420806110443d8402d0250201074003c0b41c2c01c014140740c620000c80d00384101c0c403000b407003090000141042c0c1070b881100034a9506183e1700351502c0c1c1c070542c0c3e82c0300c4c00148105c9607520340b03840ba0400106074907410003c1c40443d80c3e056540d41d28048110000d41c108100c6102d60f40b0400c00c0010311140042842c100003d102003010220070303200d5031654050790300d94041310024280c900c03804219541500d410920540101406050076089031144a0110007a0040070019000c8d031103400c0003002240058070551303008041c008 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 618078111 1250 618076861 618076867
    0x20619080106080112020d030f12061e1e03030518090103030801030b0a110306040f02041a0a080f04030c020120060103031808060f13150204180e011407080921 70
    0x60014040d80f606030042c0c0c1c8500313242d1345ca8000580b03030070900c0d003540390b010304004d5000d07045406c0454818101040742202d15003480400142102c03020a9104401c503680203c1803c5900ea000c200c0f141c103500d03014000d4100c02180d04101080c0034030000c15440b42030917018100c1441090101b00140b00a0340110005503d00700108103001d50b1005560b0810180b0009101150203550003000b0f0780000750a0030b118954a07055090f01050310350465008041d03c003a03155400081c09588031075900118200d8000c1001e03c00000c1d0001040402540b00b2549510b400c00406002e130011074407890705100c1c20025440c4500208a2820100000c6008500c42e039148042c40500d4290b440300c0e403c19500c002c4056100c1800d22041e64004940180e203c00b00101001640c4200d0038120002a00540741c02012031001802003a5403690314202103825003248018417600d03409076665800c0750425809040d64003118070218585502c50252960040f41180c00c0b145146c4625903410340c4500b01c040700919082d000 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 618079361 1250 618078111 618078119
    0xf08060c1b071d01090513030c14150a06080f19031404050603040c1401051201030b090a0b0702030703091d0a0e011d03120601030e0304150516050307050c04050118090206190801 78
    0x51b00405501015441000503d8445650081c01450358108010700c5104000e41c2c0510b607000802c49504074017610714860307402d804c1411005c0c00400c0c280c0903403a0607000700d07100110301d14800511000d0900c1c041d504000c4090980e00c007181c1ea40003040c81046400802c00c000243c82c0d5400d00594081c41c001c2104a10661820380c1800c50180381260003810f020007400403541c03050895101c9811030743c0183c180b14041d510100002d0800081c80c0c8020040c0802c0c00c14080059800005045298030075200e11900390748500901e03480400001a002613000d245001a120450940040c410768540708008075550b0480030400c0300040b02410552103d602c04500610b081941000103500100207003070400c401c4105002e0b03240c0303e00c0340703009a0604401c000d090403050381c410740c11203c1591401c07000e4805000c65207400d0781c5135803080f01c0035603151080300000110792a1500c1024100c800d4144079143d80c256002e580c5014011007041030340c1c00f11080c40b10b0000301e810809840e40000c100c5e50350132100d40c10 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 618080611 1250 618079361 618079379
    0xc0105060102100e0706030906090203190302070807030b070309150f2c0c0607050f160303020610080c120c0301140f09070b0306092208040f08060c1b071d01 69
    0x80e81e4507620341c880c04c2800d407000080001c640c2e03d0a44e01146000b0680e02c000d070400c60702a090300c0303a0080d054402c00c041110641c48411071012594400c1c0c0c01d030350f0001e540c1d03181255204010b000141a000c0401701084101e4041c0e4000602c041c4a0f400100b00707040060070762021112801202d45980f0780307980b82f145509041110700c1344040c2c000c50b89403200100c014055a5103610054629008182c001080c41c140f007030400c0741c905007400e01012102c00191490304a800902e1130320003140580714281c085144d140410320443c040c1d41c031420080540071400c0082000c0c1526160342040240108414828207072000c0c010a1600040050326140c141007078440b641c0c55040040403060548c0120341e06110030448a802c994000b5401c0301d5950041d2603d01604283c1860046810609021100b000c1c0c00c0182800113030080381c20140010340c86030399504180380c030b42d5802c982950844004220800d010030300380c42401a603890044c2100c9030700e0b40390b8091251031401003404004200c018801046100c82c = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 618081861 1250 618080611 618080623
    0x111002090102010e01090b0a09150603050d030f0b01230c0102030109020301170f03121503030a030b280302090c0c0f0c03071a030f0603012c0c0604062a02060c0105060102 75
    0x481301c00200301d10940b03034469a04804000e084400d25544076003540c001c0c008091001d1404480d210070400c00555030385402e550382c1551a4a000200303040c0700380840641d4041c45100341410060b11000b070103a03880c68001e04002405141e1018542c8180200e9003200c41c248055406081401e40050ba25418226403001940043c034800c489a400a80d041d04600c3d000b00c1a540d44211100b0315030040d84030034901c0c83e0f014100c109015091703c40850140070403a4140c00c65000c2d507009039001c082045403c00b801c82e0040340005200c0451181c81d000704014107040c2110b0354410808182e480c03c0c80003015615081c8010b101001049502c000720b02010342c03400b400034100a2008184c4080f03001ca003c1c95028003400b0083c8070403017008004001070403c0c5c90070741000501000c60324007010310080c04000010340909403c1499030701e1080354a0000542082004c96080e51669114180100d40980151f82c060060409900d08904078030b90700c400580b600c20142140c640f1110020443d8a80503000a20f899 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 618083111 1250 618081861 618081881
    0x3021b0a0515070f030b010905060a080a05061e01050c0c0307060807022a04020702010e030d0512010f08120d0e0312011403010920060708040e0601140c07050904020111100209010201 80
    0x80e89050a011199811050003020200c15045c041201413410005840f5007c0d10b034440d623000480041c0651280e64007081e01845410b0502080180d903c0e4001440f1021001c15802d1103e2500100c1020701036001e00054517140350700000311b4000c083c10001107070a0002540c010000301c1d4106081c00a80c0d034052080c0d45801450042454010010125400204443c07545850280358006034207001e591203a41e803001c042d4006011645001030000005080f83c2c480c8500d044d10444110020812107035848645e0102c1d11020014003820505144840703880d440401150502603031072041c2d0480940c144080e05001d10004102c829561502c2d00312441010b090580f5482030f4900380c480c800042e210403440c000c08a008048048020325400880d640d841042e1000c0c11314100400c000409261303082807075104040c2030b03075031079400056032280d031446020349203281500d030f00300c40c00a00407401d050000d158082c1c014500030550b0701d14420528241000d8000c00958140c0006e02e0403000e5809004d9040c10f4 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 618084361 1250 618083111 618083143
    0x8010b030d02061e0703020c1204181103010e090f0607050a0908010b031005150909010f060812030610091d0702190302070e07020109050d0201060e150d1203021b0a05 73
    0xd1914007400440304001d400603850002903500805c0003030f80300b54151000c01100c0d10440f0f40c00340d40c003200e84005030004d2040b15454902c040301402070b4034140c042d4102039480c8402c128150303405c001d00d207005010001d001ca103044c81840b410300783d0403c0406c0105d014003c90b88465603207403c1c000c40100381420642104095a04003048140140c0700002d0070002c4a004507400a01a22150301c1007103000580c1d288070351b00a1911003481050581076200b07040da070710380000801032181d0342c0803000e48950030755200c016603000920000d011030525000030481c2c3c0c1d40310b140c0442140d0310341d486900702021141a42c1d080d40c00e1403080101041e010090007185442c001c03407001c1d5500180e90000d60b80d004900800c035500043c6004a101d1900075040019066408025140e407025083d10080c0203040500c541c21500c40c10b43c3c0480d100c000c4080704c0210812000c1e11a06040c4580d44400c584068403032100e10030903608004c404804075111100702c41d100c11090107444141140d08000345082001d284200305 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 618085611 1250 618084361 618084373
    0xb010311120a090521040905090606240415050c0d02010b030a020120060405060f071e050306180c07020a090219080705040e0a020c0d020d050922020408010b030d02 72
    0x10a800110403154000c104401c0856064202d143c2282056800b0100140300b2050002405c008600c0d5006017040e144482d01c20000c9955009805036500015074809401c51400c1902c400032000e643c0c101800104440c0c400d40c60140d9403903400003807130b54800d05c100000b1004602c000c4101814441800c0b4003501d44000e01c0a2419800041e880d0064054001d040c8070a0400940c09070702e01d9164010050100000c0e01d0703180c076040c02d2680d200c40d0100c07000f28000801800040c1e01c10301814001c81e962020030030804983d05111015a400c1d4005400355520142d00115410103903030340c1520910801f0080505074440c2d14a2051010060701ca41000b0303685801480400651349401640009440052030301d4040ba0301e03070f43d80c02d27140d5102c0c58100381e01445003441040074100441d00184a1140281c04440460118a00c101d0b207545610400c2070004504000030340c2c0d94905101408001185030400302443c02100407003500b02da1055101700d1159440c0c0c00c0c8003107a07281c103110340783c00c98000d030010f400 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 618086861 1250 618085611 618085627
    0xb0306060915030c0d060b0a0806011208210a0b031b0607080703050f0315092208031504060e060301060e01030b01030305030408070203030a081b0f031303020f030a030b010311 77
    0x3507155009000e81d0344002000c03005900d5a800304500c40c14900c010b016143c84888a0400746c01900110f0609801014040400100142d0019285040310803071003a07049010525682d1000306e80c404400e80390079000035203d440004080d00b4006001e95090303900020340f00004400d040c00d00085405e59040d03200b07090003034003090f00e0720030032101c42543c04054035544e48124502510240603410ba40e1031500c070003004100e56840c0c1400c000f0030b2954110ba04608642d16030420800d00c1c00c11203080303640c41010740301c070800040c190700c007440d007000107000341105111600e408038048644550141c59107441e00011f21185e8202882914040c28040c6030b000081d6046864051201c0705c180310040c208000000050280a080c000380e420095000b0240c1c4c0e950311212400a00071141580e55010720390207607400110081020044415000d40d0f100910b06590f141c092055010050150503410350040c071004446008041c402000780500540b0300041c600728950004003240c0203040400c008602c00c000c100 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 618088111 1250 618086861 618086869
    0x7081b040503120d15140a0504020918270703060e0d0f051608030c0942090603040503041e030f0809010e04050a1d07051c03030e06070f02010b030606 66
    0x140504034400c2e0030b13520101c108291000700030010301c25003c1d5044040129144000341450406243c00711000101c003030320340d401c0200300c0c841c0804440e4054841030003492000b807100182580039800e9451324011490041c2504524441030180803c0780d0014042801084510f110b41181c480901c0020700d450201118007400c1c2c01e5590301740400744480451500710544101d800312050303a41c0014500c2e2241010101d00c410358100315100e0384030342181071044000e01d048400300e49842c05265580300c02103840a02e100496400c0501201011004100e03445954403004020340c081d0b4421001140d40c0e61400a5103002c404070000c100f1950020b0600c1040451400005081025040b1940f02c2ea1011403030010b940d032001042000346c119040404004134050140d01c02c105031005414503040c10040410540c0d20b4403058007401d50b02415180c0b0658180e15480c884100c454441c5c1000942d1420030000949080c9048800b2000103018202012040340d081c0034440d07082100f5802000c060030100009 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 618089361 1250 618088111 618088123
    0x9230708040f110a0f09050a0c200f010509070e07090308041404150806091605130203090a0b0a0603030f0815040510052d1c0b04110907081b040503 65
    0xd40200955a205810f1100000b1554061280140342511541e9112072246104000340314100c5024a0407000400c002a1801550001122652549034020000b00140c2c2d040c040340c050351500d40b00d400c4522030f09010034891580160441801800080e10b4000440f0120b1001031120303007045080502040094683e00642d000e44400700503c0511078901c0300070034005c003e0140000040c41004400203081a00402d086004615180c00d0380c0302ea2800c00307a501c00c40d127514801c1c0e0703810a024034606d6443c08943e5004d140c01800c2a420340f800e4040341e444031844068117981d0a01c0541c0d862004204058100a40d980500d0720303820400310740e290990b000c030149459215030700c0c01a92a0070001d00c038100000e03400b601401d0018141070200303041190180c0f407800508403000301c903850314440b400d03030340341451b181d814074a0700e0481d5403903034142c0740d030b46001c0d000e8094001c44d81c075100c0000d00003640e030307404282c14802c4d40740303030f40f03c000500d04a82e003030890f2a10144d609d40812010001444107460100360 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 618090611 1250 618089361 618089363
    0x70204150927110d02100801030b0112110d0c0308041d060405060102100c0207050307080f1e060a020a030b10030c0e0103022d0d050c0d15060c140c03070923070804 72
    0x40003185800480404e40984060340000c0d400311542c038040c440c10303401c816039030f0590b4000c0c540e08180c0e0b070301e40400041c10740708410060040940131985141610b080440c00301c11520448902450070f541c0d40d20641c10f03800075044100200c0c6640320103501050146041a4071050403503062056040c4080084d495541140303440401c0e54855803019071450003081001c00030300028003141c00441c0c0e12400c06881d00081c0b010240d0b640039502807a0350800342800d0b8080c81c2c05601001c1c043c0d42d1141c3c88440000d50200510300706058480311030100f1030752001c1c0b0307003140180f240d24082103c5510341e900800c41d4403010312080c18148140701c0801d09110624458600c5114108030380c0c81001010101c00450041c1c241030b48105042504000a55000070b01600c000c4984000a2202019001d000c1c10403034241d010360780002e00949061800f040079219015101102c45003912214a02500401d081c2202500709111081d09e8501a4905000425006107100f003010104840740c2030002c4010254440900 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 618091861 1250 618090611 618090623
    0x10050c0306190e1501030518062a070317060109210f020415080f0a110411090d03020d120209030307030e030f0106030516240f0203070204150927 64
    0x241c00d640800c001402e11024010121600c40f0900d0034502e01100b1a40252100d03000034105004580071414040d4220700c008a00c07005855070341e81d41c2d6440c00d40c400044c105028420b40d4074907480300440345480180f82d464020741e144051000780541140f00c480020305400c0c1048840341e4200002d1764210200c851100840e00c030703292014201e080c0586142c1c5043c002a5206140c614560003100741d48600608032000e81d000d460401803920081511104031000140003c40b100c42d80107542c0ca0660b1080801c604c1c6040018141034580c40401c0a0000916044000d6809104840031440c1c01c05080c00e81740884d2070f0258a4008117201180e22400b842100405115540085095035901441900e41a0b05000020001542c0d01d091081d901d01840140644980c4454400b04800f0252651007032034490900110000e00e5107044100d408140c048070300c1045000c03d211042c010b079107a0007038020490040f205250f0480c00d0003c20002c4a04010160000e03800162018024111804c60510300c0c5030400303 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 618093111 1250 618091861 618091879
    0x6050a1d04090606140306091219051b060a0b0303180d2f0f0103020711090903130909020a0f0602060f1308030c190f0905090c040e130510050c0306 65
    0x108001d0300c0b051800804050074000e02103807039025642e8410459000f00e046500c0c684038003000030b44804943c129008107503000c00c0313490700380200640000201100b615042c0d2800d044041440151b95032000c81c14034070340004050245009080c0500e8952440890240d07150803078050402c5a01c140d440c1c1d0650180c001e8201040901500c48a032000311810840b0b00c034000d5400c940500c400a42000c9440d03c42c04003040c0d00e50140d4881c4c030a40d19004e60051000041c4804c50007005168440100340440c2d52108224100a4821383d071001c0c1c0c01441d9800c004a01d4800b40e00c104401e044040c1c0000040b0303001010104145540068000c3e0014410710b00c10010b0f0700c0c0d80d414401048900d4002a00c6010000140000010b843c00104006245450030602c01c004d052000c860100d28103c503c0700154101c8801c0c030071031906213001078009000107811441c182d5a840700c1c05070100100d0781920f10703080d038007075020602000b44090705002185050820861401a0005455020107491180190030907 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 618094361 1250 618093111 618093167
    0x30a150f08030a1b0501060608010905070323042a17061b0f0403021c020112060810180b09060105090117030703140c3c15062b0c06050a 60
    0x4082c41d44c529030404000e01c00381e0388a000141440d48203100c0c48842038604800101c40034440d1007004507014a001d90400300b49044000c802015001500c16070f0140208142c15103000025490181621248098242124a0022400001e400441106031250007603c00c001980e00128059111480041e5900d0f80710f4050811604140c0201d801c000e400c5400d80c5c02d0010200d44090780c3c09041c501c00d0380e4a40c100a0301c0c01c5280d01362602c40c4100d079400ea10114001c80e107140305400c54292441144c0c10205440440d80741c002094105a510303040b942c001c0c400511440c20104501030142129540d03603920f1070300500c1860b03030381d101d40c003400760030018903200e02d03540028204100d460800d882703002c03580201d000051a15440c082d1980d2800c98002c1c9401501d658500e1040811074400f102010740801c1d080043e2000a16a0050096a2144c004000040d2080002c01410017a04000000340a10701c5585400f0b0001c0e041c40d0040b00900c8418001e00340d5595010f40708100103403107240000c42100741 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 618095611 1250 618094361 618094397
    0x51c17070c080705100c170a18030c0905070207120221100e010c020c060d0203060609180a0c0c05030910020709060b090333130602030a150f08030a 65
    0x2030440000e0001140d000002182100014440c0a03540101d40b0248841d4252000360b40d03d220491340242100407601d600280c90302d51001610281c1ca940c01c1000e00d1000b504482030301c048080d082110030700c510a5050198519502c540c07940943c0e140020204c59041c2507100c2203000461034028420f100010001c50a01400c000c154441e001c80c1c0c003140d100340500c405420141c1401090100c0310740c038011060764110f1000810800e000c80103805145410b10500c2c85070041c0d40014015608400d0811001d1560380f034004058609894808000365507051110007042584d0f1254207200401007201e00300c0d000b00320003000f1200300c42011038103002040c0284ca403d0303060248075400240c5641c40d1000004000c24040014162090101c1c00c1e55078182e101c120b000c0850b1010011001c031100701c100c43c280c0107410820f041c2d4000400b1000c0090501443c0d481a043e40e00403981c1002580d1070340300000b030f2a0071001d20340001e40450880b5084003824080925503034000e1480903400c011447c48940c4180c40 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 618096861 1250 618095611 618095617
    0x1103180102150103030305090f0d0e040207080c03161a0403090e090c15090411182101230604110d020d110412050609030403020d030e130608070609051c17 68
    0x20480007031518561352030034041c000b8041240c038020389015840402401000201c0c0b5030b105002e094941001040e0a0b4040c40002d401c504011200d44504010707201e1003401c104050200c13200c1e2444034403801c2416140020804d0307840c0c204140c01000c0c43e4103020000360090140d00a582e001c00240c801560744000140c504a4005020b540284050901851015807000240b015135410780b001c0c00317032011202c9461b00c1481a4909000c12104100000301c1602e0301c040300b007000d030800d240101500803a503842c480c219501c0e000d403420200c82000a4010010408041d241d209a00300d4082203d140c184282c0d0392607201c0e115600e210315600003040d010b416055440311000603c0902c1c40341c0c80740e85a81a400c0b0580b80d1000c15180752041c14005080b006000040300e00b500c0c0e01500c0300d84404102d5405881c0480020507a0f42c1c8032600008800341c05a06110f04c034004c0c02000001c0c540c4a140c1030014010345d06d00c1d0070040c0602d0080355002c09510100449012059015190110001c401000d001d2280 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 618098111 1250 618096861 618096883
    0x60504020d0c0f051005040305120a120507091a120114061209010b03011d070320040905010609050601030c140901050f0d06050103270b0c090604090504060c1103180102 74
    0x1203846403011410f808110790080613901d040c1c810003184117592800340c88a00680c40300404a6002d9400c40c080da50350007003e00410b161a04094100741e0619602c0001d4500458100c400203412040402280501052500c210724140721180d103010025150303c03244c42c40c1400f44d12034501460001d0f0000d0b458240407143e02e66450503002545007010041039000c0c06448000034840c0d030804402c0070303203100221814640381070220000d0100c1480c5555804078456070850180d103c0c00411309511190701c81e801445070091082000044041c100402907040b0382002e000c56041518095611600c290803d4a12803000a89540b2a4849410b00d004840303a114500c055886080701244c0b40d030f682c1c1320f660401400c1d100246c9051007041915106180340d4021940302c2d61103200c62800b4030000c10024054150402d01d82c0702d005242100a0300454646c0c3d20941c000c14a66a0360000c000c280011481806071080741440e08401800342c1c50051a600e00400c0c0950411040d510090a5140c0c02040701d891b0340 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 618099361 1250 618098111 618098123
    0x11071203030213050f0612060307050418060c0f0f0e060d0207210c021503041103030307050a180602031219050a09051b0a170a0f0803070f0c0b04060504020d 69
    0x9a0640e00d401006904100a40f90708455000000319603841c201c8612000c501300901824280107811015031801e5101918960b01401a00f4000c40c1c5521507010700529900310030140c240314059844c0040895611074400400c214008032522040c2e54030100d980d0785010203245c0354030181220800540c1d54030608640c0d6a0b02440050780000b0001e9902510740e003220036241440c1c1321141c84a06030345440380c1d414003c1d031210100b000d00b031000384800702664000b8041c0da0035045070800d19000c6403031071f402520900c0c04a100411120026540003180d400100305ca2000200c3c0340e0715048020f0354074042c048090100300800700000b48101c002c12402c1e078502500c0c60040c071980c1031000c402c000030402402c041d201c1d80640300e43d031940c0320300c03241254005140140080b8141031404200c0040e50300c10040c01c040714007030700d2030080116102e031440003001402084460340c0e90070265409002c0408024030366050004002c80d001c045021030440340c2e84990403041c00329043e82c1d03c1c03001031440c07044284000c00c0 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 618100611 1250 618099361 618099389
    0x20a1e03020f0d03052502070b0309160902220e0f1801111215090103120e0316050103200d050709090c080415180f050a08070311070b0414011107 64
    0x140366819003005c0d00802c0d4204040c07540078481c4898000c000e051007024805a0701c0514104404c03000c6030000d59000d0700b400b00769850380400c00b545007010f03c0703698030441815802048040c8003008000070150140a9011241015460000c0c001c5041c0e00003044081880718000c0020b2035a08000c1c0100556007200d00204405d2600040401031900221b000380b180200c60301c00102e04145140d41709001f900c0081142403542e2031540e0700c590b02580004500c040206484018201c0c0c0c40c02c101403035075a45d0030b4a28030f080ca401c000005080b0f841c085000360b44120b060082040105644045610a040d607410216083c2d49400040d05c1d4080c0355070004102e01d152207201344005600100c040d001e64402c0b8808100181c0700381240e01903510200300b4010070070a0407000000142640e22200c2488d220b841a40d0400304141c6400c21039400c0141c003030740810400c03510341e121030304140030580250001c01c00841c00c00d414142100c0c03140722001c0207207040c000c61400091988400b0083d00000b0596403c1c040d034 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 618101861 1250 618100611 618100633
    0x9030509030a0b0f0f060d0f03090f030c0e16080403030905070e0f07020d021b01030504060605060c0d12020708030f070e06040f06180510051303050a06090b07020a1e03020f 76
    0x11003000f0865101c3c080d0b481120214248074446554580200c20051480781218165110000c200c40c05440880070700c070700c07e2000560300203000d00c20340c01075000300c030070700384080c94260300c8000b0140060403480d41d20700007a0506a046d40100320550055012301e00003a1400c601e10b44140703441111703005002648004000c208410824200c11446014a54292800e10170486000e03607540081d85861003015000300740400b80740d48070b0392010b98428025403002c580959641c0100d40150b108540380c2d0010b821581c4020061a0800343d9841403902c110421841c0086684070040a40405001c40c04003500490108904500c5803042080400000b088240e84941d0340401c05041c204070f10903c000314003210390800314024000105400c071034014004c4030541103991003c0390b140e802000c98030b0444644032800b102081007088a003d00c14460344001030b80721954244001c038440010700310b10466005402a00c00110346038004055042009240030760141e0a1030140d00f40300c06010410001d1007074451440d = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 618103111 1250 618101861 618101873
    0x5031b01020405061c230703020c03040b0a020f0d0206150409060f15050a140a061107030f0b0f0f0417250f1103070605040e07050918071d011209030509030a 69
    0x101c1c0c004580001000b81031107400c841b490000c54116100b89241c0703081d00091106000e82c00a216400d0030006481c600384d140c1075100160f4102d13103420401607000c0e0f801b0204030b04080051410001840c00140868540020140c0000007103100c01170107280c80b0f10307400e4208022900300d045403140401c0c09011406032060340c1c404002d118483c0e10300c156614140010f45001b640440c00c40700c5000381c2070301c80050030424207a07000b03a581807080c049440392110001c0810529a603440505100b554112160b00b0010410b40c1c010a015060f01580c03c0c0c2c900030b010000c1c0c4a03503201507260071405100d80d01c40c0c0c3c80c0d054201d1403200c01c1004a0b1600829a00700c03003089004000400350512800f401c1e41d550300c003081419521242d03401800d010a01c00c0205001c1c0c460300159055010296207041881e0601d8407000c0307510204000c0019441030841c2c801d00c40f00d181c1045084407050b000303c1c0d1040f0900c00031000200f040f02c5c02c0c00015446941c0e4498441890702c03c4048a0280700043e08a48125002e4a020 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 618104361 1250 618103111 618103147
    0x80312040618020d03110c010f02060f060f06070309090f02032a1b010e011a030d0305190c021e1209040906060518070e1e01051b0727050405031b0102040506 69
    0x80c01d01e0081e502c658071f003580101340252141519500401c0285c0e9209090104013602070155648200c1d40503207400d90350740715002010414403075901e0b0581c1d01e143c40079800c15101941c0b452118a030041c001c1200d01c1c840c0c03c03241d0f20249241802c0c1314501c4120b98460360548641d82d200c05a9640c8031f425038806c0c40054102c160003202c0301c0000c0101000042d0780003100014010101d5150700f080c0e84500c6820f100b8bc00c03071034001041261100720326000c07512110491350501031150140c1c00c43c8800b4420f07100b441444403040900d00005d020788041c010b098034210301c101c01c130f06446141d4400016007480041c3e4002e0300030341405081035842d41c0c00c128182142520898502d8005a01034071031004d00d082c14050402e2000800b10102141600907005568a42244c503010055441003800080c000804200240040190b09140011601c411101030201440101c442410034100020b21001420000403119202c01404005504049048041d80a841944c0c0080d070701c900d010402c03243c540505014 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 618105611 1250 618104361 618104387
    0xe0708070801060b031f050d0c1508280209060d05010f06031a01120f0518121c050c0d0509010b33160c0b0c0601080312040618020d03 59
    0x31100d00381d030764400c05030a0300c1c40d038000d844100906002044a034080981e2182a61018008120303036682c8480c003041c00c4003000300064030420070b003a204200304107a5080480d14003000d40381524441c030b0071840500d0020140207202c03010f00d2000050000c8440305905443e114100200708581e50a44c2100d0388020344001c0c000c5204542c10b016001401c1406071140402d408cc0388004030b1031944812006444900301c0c82c80c0c0c2c1e00301070b845d10362204d002c004a100301441411158405a16503154008042c6030902100813008a07107000c1011a841c0510040c3c6030441d04960f12020074643d031a040387d40d00714003494403529151405e20382803100451042d0070009500c4e50940e2010b58800240c8114095155040006503004510340c105802c04600704000381942c1c400d144460b100c02c40107681307042d0072284a5100d200500710106034a0400314040c000c80d401007242000660401c41c1c2c0b2088284000c0c001f03000240020313541c0002d00d5a00701c002d62503c8085400518886241c0058200504a0058141 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 618106861 1250 618105611 618105613
    0x11b110f1606030b030f0d080c070b040b09070602010e0a30021b1c170f0a0e090a020901090b091f120e01060f050d0c030b070513080a031e0905040e0708 67
    0x501350415040000d92400700c8030005004041e507000500041d1031361304d0042e06450340001d0401c5550040358045400c107000c2e9110b440072107841c0c03400312840c070b003440d07525081001164148012031404c6400001c400041d0364000510081c1c030b1030140201901c14040e405114202e0100101070341216801044910312030314000340341a2a0350014041104224160011101401b815582c1070007090001c0034008800b0401441e0714540750110443d80400d4100f0b16003c1c0019840301c1c1c412015061415095030060300e03890082d4104000880081d0540407a40140008a000849c107021070f42e450603e0414816600e69451140310a0008014041d017080d1040d8035015040c8481c86400c1101407040d4011160348507032a00fa03084c1031030308103c8014154481540c400144000c04008a881003c88038007076035144d141c0540d602030340c00c0700040001c850341c030192454000340445004241c012340001c81013094030a0500030040303403480c00c0c0c4040c10a40c01c0690485d280142002009000140d9103058800000c = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 618108111 1250 618106861 618106871
    0x14100c0504150503280603021906031103160c0501020f03150907020a1502090301150902030105010801080303091b13060b0d110301050a06030b010504080d030f0c02011b110f160603 79
    0x42503c0510040d58211220700e2181072902540340441d40390880f00c40d00c0040414010f9807900007a02c4801104c0d04106802ca400034108051501442210905041031a07400d041d40385c0000e4548000396841c0d07104e001d0006d01d1082d075013000320070360454201500f10114503403603080036150400d101d0841d9034498004e4000001007641c2034000200700000070f5000301030344504000c135240d850113074006c0400d00d41c041d92222120b10a0b402425600409000321000060300c079850316000402100040e40251600d8104005020981c07101041c00620702c0c01080c203138109004250041a0b1070300a64100d010030525241c400f0905100b103000400d0b100010f00c8041c0320180c100d610403c0707688400c0c8221507024580020030016907000c0e070005000304005040c01400c0603551003100d401c084c080d1000d04000b95a40100400051081c490540000002d00c000c0081e804d1b01300090b0003081d0155040c03014040e201715003018040f001c0100032407a00c2c807101540d042a80c0c5882c1c007410a10780f80120400300c0c3c105 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 618109361 1250 618108111 618108149
    0x3060c1b050601270603060b0103150e0109050c39032803090506090604031407120c0606210c0905100e0411041d070501140714100c0504 60
    0x2960411003240c0c0220251007603074a09003015400e0801d0040c441020150030384d85081401c614440e401c01075005810109030301d900c07040010102c400410340b0410702004d0080c2445520035180d45141940e003a408002501d88602c03001e00c90602500411070f00c0c840d841d26220701c90714684004038103a8607549440c026603034803d00e14a6182d0090b9082c04400c40c40040d0004450204810514080d041c0c40c100050381e5900360b02c4050400c0c00840e2003a44c141d001c5400e000401d540a01d18008080c107010201c3c0c1401c4056517005a0080c1340c0200344100081c2d844400188440c80e03018900070f05e1440a82207000404285110b400120008296013013008040300140400c9180a001d20612000e45114002810b1618109580001520549250804808028560725948100c203031960081134030007100b50004110f18641009900b003075040042e02d0140040499010081d1a481c5034800498040c1d084039812161401c80740900300d1031110304000c0b800100310f40060041c0103499014075035420701810 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 618110611 1250 618109361 618109397
    0x403020607113a0f050a050a12030203070e0105091306060906120b030a0213152403060f050d11060406090305100603020105180d02100201050108010f1b0f1803060c 72
    0xf120400440016410412106455920521103d071841041021310b20b648130340340c6a10303100903518200c1b16a0300c06070380d440a120383c0b180d640054001603c0c0c154078501d800d0b003008000c0c1c140301d1200c41c10300401282e806001e0340c03240f2045c030007074032042020481540c0c7d640008029007094402c01e808200b45055842c662034090140c08000800a00208100c2c203481e424000c460300c20428002104c3d42c0c4510842410780ca0039070700c000030b220051401310003101d082c0f031404a0300e510712003580134540b41c1041000b8813134003418100220340c4100d0340c0785001101401d1030768200e88800341140c1d004000240205d40c242d01702c1002c0d819280980c085480801400b00518225491400080e0124109100804500c0040302c0760f80e881c0940a0032807801082164003103846208490030807000f40c3d451384018008407400b4442c41c0c0040d03803c094140110186490254881d45801141c1001c10100c02c4151411034002c0b50709060410402054210039a45d0b070816100401100720381c540000c2181c00340c000e0b0700316 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 618111861 1250 618110611 618110659
    0x10050d0b0604030f080a0c0501021c050f07080c0f0f3702070e06040b04051e06040c270b0a022401030b0604051b12010e01050904120f0302040302060711 67
    0x160058071491540d540341c0392000380b50406e250341c00c104081c0b2400303240018401c1c005406003e40c51601081c1000f448003104040d40c80003001402580030030b01c2000050b5602c402103c0d00440c54081180e0394002c00210079000748501031007481d032006d0024140200440da030080c002c1c0405800c41c820040d40100501e01d1144008503603540040e40858030501041903d074480d42d81141c030040000400c031050304d010400b581c00440d52011404415884160715140c001135140d4482d1048a0800c040c203c4060082c4c582031b4050201610185c0c1c5d10158803026454850344409005011852030311b600c0b080d04c0017983d0b814152200116a40c282203501c00000d650041503050b82d5114540b019190b5410007440000c00c2c004000598a20b11003840045460f034520040c241c02e03003c000c0e0380482e5030404003605040301c01a13110314026801d03002084081011300d500c03001c0c005041d142c5405d01d8190301600700d01900668101a5006c4c100082d90f1040142c0b00419118080003903c040700f0b40549004505401e40c = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 618113111 1250 618111861 618111863
    0x10e07050f031009050c1e040503030f091903050a050d0807050a030c03091209051806060306120c131d010b0a090f14161101050405210910050d0b060403 67
    0x3041071200716015803100c8040c581c8580c82d0450f141250740c0e1005010240e4900b5a003400c4c1d0104000303504031100e1905001c080064070125145131401c0c0c5410701180c0d50784540c0e440c542e901070340810940002d540707680c0c1e0000c503200d102e165103150070b1322400d266844840c04007049a0a10030b210b246039401e07000d10b800320720444440c6c0720203041c41d0089106501400c11150050201552486c1c000e0001d0151619400640300c50b940f0300019904060a1158450341c61400d043c0307186c0f134041002220303035030030301200c0d0300c46c4c0c3c1a1180b00645c82020196817801c881501441e034030080b040401038124102d540181c00a40c0500410318260104600315822508013a0b44c1a4109041c01000d0007214066004007000d240121400900340030309946030203200300180e40e0700701910a454050152542c0c40381e03000390002440c00080109050503980c0580d1142600305880320180c82d110034810142460007a50900f4070043c3c050310b28108091401025984044080c0512502e80300b044034450903c0030a0350140c0b = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 618114361 1250 618113111 618113117
    0x5010e060d0e01050f1f2913080606150c03090d05030403060c021f1401090e030f070f0308090d120b0a080114071d24130f03060c08060f010e01180815010e07 69
    0x81400803465241d00b08000000d0a4609040207903910035000480381e4402840c270000a4080740c18100304010110607211000072240d6400e21101e04603500102c1210046401210468506401494014194007407640050002d5143c03050300c9290540104103c402c00720345101410510345500c02240c1110762900c002c09110385048014485140b003684070f00610b41e000c408072820301d5485e44406159034841081100c100c500c04ca0071404041d00071a01c00e42003884500645600198210028059440340c0c000400795512814098000d49403003041602400403000207210b001500003500500c8001619140000740072102c10290800b02c05801c0444682c00801d0b140040c400c05142502d00d1071001d000c070903200001c00001220480700e0120100500307072120006111032039814424215071890844c20309000c00c0d45d003008202d580301200301807212404d00f090100d002494004880d40e42c4169040c642105003410045001480010b84c280f40e808104040001c40c0c0e01c4040b2010100030a80d10603000c = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 618115611 1250 618114361 618114389
    0x150a1205160e0a120819020613080708040302060307051309020c1b0414180f120d0221010b120603033906040803090c010905010e060d0e01050f1f 64
    0x1d19100301020801c00d540180280c9003292600180c0a41c020b00603012141c0040016564106c030f4485840300c900c0076901e00142186240c480d40208013034415001c018081c041c0090540100144082130b60082c64015001c7d90310b034a06246c01915640c400660009401502c0d1400a1612224000c91f052055520080c080f10300c03045407008017042c82041c00c1d59000343c41c3c4c14040c2081c41218920791140500206030105a110a08054104100070b000c80300b503030f00048200c0310b640c2203020841d115100400b4005175034918001d5000422004800b006490380d142400000e252440f0310041c04044005888068158480a04041c1e4902c1040400d056844d001280301510301000750b0885040c802e142c500d0030080e00c0c014a41d6003000402c882c2101d240c1004030511103012410002946180400c0c00d040b01040e06100010b010078076544004c51043c1000110031001072031b50b8020100c040c2062000340100d04005243d0808d1510480f0345000800b05269032003000c815040f00b000c21681007060b6011 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 618116861 1250 618115611 618115651
    0x3060b040606051b0a050609010b09011a03010308030415062601020301051e0d0602070f0311060609010905070201020706020c0c091b090409171809091f09030e150a1205 74
    0x1034000d81202c120a010702500c00c0300c2c801b0074010f2001c20700c1488600000a10340c2d40d0a000c000035100103801c28030b40c5825541501d8903642c0c1c0882140e05403900540802e8580c1ea9510b060708443d10b40d400ca840815040040001d40e40d00ba403035082c80c1000e004161410b201d03000352303842402c0340401d110300e61b0300c150220300f13448002000d545101c20a003030242040700c08650b16122001640c1c4000c00c200c440400405000007803641c08100e490107804a9006410700342480300009038010410701481002c140d6810114444600035070480342065800001552141c0001180c03584541090b04018010401140011801d00301c0e081500d0f03000301b40c8405642030285402c180401000062803c80e8440c00c4d003aa691140341d035050240c02c11200f03400828000c00c4500b400c0c0011043d01a058210591002d184c0201e0344181c0311146031451070310080058410114101200e03400f01c44085650000c054485041094036106c008190545480e1240742101581005c40c00440d103003180d0040f054001024051 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 618118111 1250 618116861 618116887
    0x80714090a150c170d060918030806010306050a0608090c0405070c0b1e040609060e0316061a0a030506070206011406040618090f060302090906060a120f1a0103060b04060605 76
    0x40c1840b070b0741d1a0655145840380e0b1842d0a034a00da8001012025000c25080c2d10034005000b5800540112441446030160300c950350403980d00036585c02000c0c07200c06000698580d01c81c0c1d01c004001d1000030244040550b07114006000100c060313494040d40d029070704001c0010304280c00b6250103115103580ba81804256516042c0400d04050584030a0303405103040e00090206103400180101e00403c000180704900f894428101c801082038003007240c0080c071a0020002c1640d06840510790007030f07004950851081011a6001e00d0414880d61040200380d02000744400007448a00c08c01c21902110030690300c40c84e0600c0038040310319800358005400c02050209601c035940484010854010204801d51030f455603106a400668070540c03600e41e105410400d52502d44141c40e049014080540090304041002c25007035240d038006c8481408a03010030204000050b0010480c003500040302e404c4440f461011b1409240c402e100c1030b2079a90400c20301e03140ea840c061094008680054481c6498450003802da0 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 618119361 1250 618118111 618118139
    0x6130f0b0f0406080d14040b1b0d0c0c140d0605040506070f1e0e0f03100e010c110d0806030f1b0a050402120a05060d0f0f1b080c0925080714090a 64
    0x454038171b03202480002295040c0c0f802810009990810300c0e1401010091540d2814400c1c607204400c11019031541c90204e0b91644a40b810b8803640030301c80c2e82d07014030313000130603961450400010100c03841c0c48100414400049031241c00b48100e0b698014004402c0e43c400c0311440c038841058801c0890b81e650010800340250145800c4100107000e408004d042e100020b0300300180802400001c680300c0b242c070129150b00380319545846466050811035022041d8410340e80b06160b05040e4103020b02c2101017035441e036082229442f601e4803442100e020502c2c41e82c010382014414007440d4000d40d651380f000704e80c91900c0d0003501c0340d18400c0b0300d0b6421296980800311024040182203150841e015143c0c800c0401d400c0002800b0f61400391580044400c0c8a01c1c00d500035160300c4100001c880c610003014408000042520000e000c0d04644010701c035200c00004540e40c00e8400190554191001843d00005400c80c241c0d034071400280c3c0f907003400c04540e40204a1244145811182e106d40c0303045060002808400341 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 618120611 1250 618119361 618119387
    0x8030c0702010903020303131514070602160f0804060314070e1011030c2805030d0515060307020109031409101107030804081c090605070b06130f0b0f0406080d 70
    0x28544044e40c070b80200781154498917001a80c0d020000c2c0501c9800d18011002c04d08111768946640e0140c00d201c011125400745800041c010b50b00040c4400909445103003001c101500b0114074441086580303045c0855902500c41c0c0c4c03010904008491000384040840b0710b01c81c28403515104008070720b51082010900c0440f28400c140109800e5944148004202516184d81000b0040204251082e480c001d8090305500408034460000d11203c0003600200590f51a07009066000c100303038544410515840c02c00c0c480c41c50300b01c0d40100401404a88c150003d1400034020784582005051048543c1c0051003a1004207810080321250a0400b9100d400c05140f5028800300741c608070b42c1ca03a511000c507984541d001c07640d1075201000512800800302c9402516820313600f050760002d4601040584580240c000151124086000040c0d60703031a415a00095800c10400403c181310048420350001e1545110f201e001e0096409580400c1c01d0034440c66095030152001401d0040c504102250000031b1100 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 618121861 1250 618120611 618120617
    0xd0602030a0608060c0c06060f010c170c0307030f12090804140f030d110709020c0c010c150906021b0307050a0204180f0f02130b0916092d1208030c070201 68
    0x10000f0540024085035000c0c8a000721641d5440190b481e4203850920054036070f80c0b2445052030107000c142c0e0014107a0b041c07503a204a103042400300c4005035030b69901903c0031444450000103040820160700c1010440ca184c0c0903240c9408200016070160101d4070700d102c004190040400c0140034101d00c0c032242e03070002c1c20700410358015014800c01180c10140c028003c40080f40c0d4840b1001e29170102404071501410703400c030046042c80b015200c210f0f03480c5074000d0700c00e0610059056009c00c3c01aa10b00c1035a40b100000d10a001c180300344e10b0030700d00075402a03d080ba900001c1301d6070710345000c90100c1114102a0020000c2c0000d20142d001c01c0700402e40e01c02a20011614610084005003041d040240d0041c002c1040440210940c01403010700046540401180c614050502c449130383c030544603031b4001400d6400c0c1c1c880d1b012212420b640320242500701042c010100101c80c990703150304444510701c100740d05000c0c050095451580f00700e0041003620080ca264170a01c005040e811841024100441c0145 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 618123111 1250 618121861 618121871
    0xb090f1c0204150509060102060415090c03141b0a0e040204050606091801031502042d081006150305060303030f0903042301021513170f040b04060e0405060d0602030a 73
    0x30740002d080b2014010507041c0c1c4101c103c0204401d281c10229958045028005000645001e07a5045410780e45086100b1903281d94914200511040244a00145601100d84011182401b0615a940c007010508500700003000c02d0041b010b052104186040fa0060080d08040b5291907080002030a0b0040010343c01903000d0048002c40eaa03142200400b01c07502701c0b814101c035411800c101403000f20054040315000d004201c01c102c103140c40f5100350401e040032114140c00c82c4011460881c401410743c045141032148810541d0f004030103500c41e1044414500300b40e110f08003040c80c2503040d118204d40041e4140c0060000450038149904002c1d800350044c02500c1ca4651980708bc0000100380701d200d0494001d5900c01c00c0665601040303501e2a0050303400c0280b081e4036100b01c0940ca818050000100700c8804503050105844000003520803100d0003140e03031074440381c40c3c40f6107829941152180300002486480380703407204d0400740308450148030007401c594280c1101c3e4480201075400035040181c4640d0718 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 618124361 1250 618123111 618123113
    0x1120b03011b051206011409040504060f061d010e100b0d060b04060503190b06030112062324010c0f11130506030d02030c0309090702071703040905010b090f1c 70
    0x1c108078942c850450703100c40380c6811140c0005206128001d1440d810b0010301d1403186030820690f026904a08800c80c0d01080c0ca0b651444e000d009030400c00c444030109400c1c01c0010481645945408048896030070705075400ea80e0701c54981c25500c1e000c2d6407e41c00c0704010701c004e210381410140208103083d0384031000304220b5034603042402c00354841d03845080000c20120500c00444602d40b10200702c8510201d0500049011500203030841c0700602c1041140140c202a6100b0001d040e0423192002021500441004d14540c900e121104400c9034600c4c040000017141607040305040c000304000c030301d060b92509800c10a0365104034111040b94016118000300d40c4200c00b090303440c40110301150f000c00e180850103081070b0b020b051403c01009114819908144502c0d401d4200c00815200001c4007100d038a03180340c5030284180d0610203a5006060100301c441d0380d101304084000001c100f200c8060608001507a03860b0b0030746c510360141e0900d0513840400e00b665501a03240504c038100c880030100c041d020140c201 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 618125611 1250 618124361 618124391
    0x14040308060126010509091b1011120301140306040b06064b0403150203040c051305100603090302031621030b030d020303040309180f050703200901120b0301 69
    0x4100001c9030b140c0f090303006000904142074010742114409004000c94070300310402600da0340034950b01c41c1c05800c10040360555070f4450601040c0e030740c20700016580b070711400ca500b203c0e20754401d024080c987c80d21040600414140010002d1207290040c0e0000720540320001080b0007a482441c220441d0341d21000016400700e0040c140c00040100c2e042010039108012580580180c00404000c54400f4140001c0000c1034460186610b10303081d211005a0ba941c0760b1414414443d03481d000243c120350305000304c8a41041c01c4d40618010041c040c035400441e561381c0021001d0707d425050082c016001031101c0814085c80880c0085070354420302c01c52200580303c8401901d038500000840700029110504070000c1d0409000d0034406442500c007a61031850540c4001c0e00d514014400d6500c0c200d48200803100d59040303507001d4007040313020759000d21039420300e44d0004000e03002024219642d40040c2800108404040c4121003445c401a1034101541010301112801801c01c2081c00d505552242010349840507 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 618126861 1250 618125611 618125657
    0x3091203090604030207051e01050304170c03040f05040c0509010e0406030501181703060d020d03050408060c07050f0c030c0d03020f0a051e030a140901210501150201140403080601 79
    0x401c800c01850b0b1840d007818001e240c4601e960196016029800c0c000710012044a00081c481d0303002c1c00c04948d60f07103e030f00e06402c619a5240b0484107900002ca8042c21400c0e0100c020000c4400c00c125241802d603e881c10001103401038540a00815410072000700554095096240d000310000c0001a820340c0c2d9407211406c1d5500082c16444007003009131400200000a11880d0700b0f1401010680d04524001c0b02003003000ea168000a88100d5030381d9450400c05210390100d40141c0418001e41b162070800584e510320903003086a08a585008410f104980700350002a50100084000c00610380d1615401c01c0c010840c0941c002601140070756007000e07015141c200f02509829204400071b00300d1200c14100b1070558200d110207840603810420100700e2440d881500304101540c05c458442e0f40d0244607005031441042e6400202118035405903924040405510203412142c41d07440c40701d07101e006180100e00300e0380c1032002c0b44810304078030703000c2004a41710703e6046034015010b050440c1406000100150248 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 618128111 1250 618126861 618126871
    0x10906121508100c0903110603100815010609060e0307030605090a0503120f06010f270e07170a020f1b070308070506040c050909030d1505060a120c11060a0203091203 73
    0x6846015603205608044c490804072040c14a007094109086650714024403c62160b6948190004000300701d4110f9500d50399001032840108684504010400701d0b19180004d00c109008551180d00003d4890300401d4205030080004000c2c100250941d900d2000501c03025025003040d1080c800c0b0400052003c1008284803006400d407807481389000c40341c020b980e200081c002410015005052003019800001e0b150110701d0110881180300f01001c0031050040d52540100940b1440c20180309180d0341201092010b0500401819040d03610301c041c800507031084403514040484208010a40d1000e0300000c0c81c400401003003030750001540d903124600190088142550300750404010302041180b00d01c003900040000390307104020b03441d1003510f880d00d84c012200003881e0207490f040e0544c03c1c10884c0724040c1c0641002000c06842c6d15040c10001e11641450380700780420781c649606105002c1c000c050880d0120302e9400242866999802440041c0d000941f03555001d120321003040803e844168040c5101e0 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 618129361 1250 618128111 618128113
    0x8040f0602071404020c06010911091804141c030b150714070807030210110a0203070b070b010503061312090b0d020c0d030c091202060c010603110102060a0b010906121508 75
    0x1043c200400b8418070140c1601c020711880c070401680601900204800d07044031001100014030890840304030f4210302c50042d08071340c040318080c0d01d0100010310340700140c09540681d9251443c801e4040d82c0f43c2d958002008001940341c105039030a04c1040c403a4101c0c42079004040c1040600404402844501c0d0300a0441100e20500c0c403c200324a100701080160010f0158000400d482c4d4a581c01003070104241c0380040c4100b0158000e0280440010401d80060550140c00c070b5031107c0d80c03090350b08415080700c001100d40c008075030000600d43c580010b100c4d014101c01400c10081080c1d40d9640208042401c0403681408640e40c000600070039484080c21907a81c1101c405039481102c245824204400c411400c0d0a141c038141112010341e81c0035036000c00341ca0806400048030440382c00010110b0084490103056036082c900d0200810150303000b038803d820703000c0c0c00701c0c1d0407a2210040e40c0b00783e5031250315983c00594001010055175124660145501101c0c400014020191f442c0c0348a240c0340d00d03003110407a = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 618130611 1250 618129361 618129373
    0x20d180210030209090105011214090d1701030819110313181e0b060f0c030c0f0601030b04031202070516150311070809010216090b090610051608040f0602 68
    0x80d410184181c0d002908580b804603d440d14010000340203030010300806040002c85840001705860680c042c1782000410406010a46460b0040954070100800f004001a41c21a099010741030820700d41c0741a00c6e40043c409042604e030201c2c00d44103c0844c11510100640c820b41c86507011014401003664005110014100504281c4a0507521312000f03801c00805150251140d101021400225091000d200d8082a114944000105a070040c00e01041c650000000c460202c414000000c0112171000c034181c0b240d07410304079056501c0d8602403102601d046901c00c0010700080c03280038400c42003040d5001c0142032408540f1064640401240c8092100203881410b01c0700c104400400d0b607c915061078280b10b070000b04102e101c098018940300502910022848448581c0288000030201085080390700038241c5d5000320303d0282c1205054036004074480000b240340c1d8107007243c0715205800952135941c500300304201440c0c0001d8480c407041e1450103060002280c4074900c0400b6200a043c25402060 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 618131861 1250 618130611 618130613
    0x43807020306100b030a0f0609020a08040501051612020310030c060c0c0905070c1407032a060806010903140c0306010602010b040e0a0b280606031a030c0a1503020d18 73
    0x1c50b00101810307144810006400800c180c0c0004000c50790b1103001054003080000c02078001d60007405d82d03a00420780d40b5002203000c181d280e50000e4041e100320f0044000740b10640b51350440f031410128041040340010900003004882041d0790f00159000141503500d1806143c4d2901e0300b00f16182141c00200001d1400e18550301486816020b04001e0442c0d01c0040185041c01c1a0203084003080c80c8005040e140a84403d1200c1181030007001c00460300210000f0218940c00840c0050f0781c1d0811605150034014880414081c1c4144042c601c22213040e1150851f00c1d0954456042c0c815161981945a100d0001540c94548003441094000d107510340001c10154104410001030303400300340702c0341c0700360f070050000d2008600c08401f2107402900520000380f030b02c10f1602c09019510804111450114104440003641590651000c907001d02100340409640d6051420503031a22148400154400700106d01441610f18a0745e82948030340c1c07181030041c5003544080809080c0c1d12103180e40500c220000940c04 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 618133111 1250 618131861 618131863
    0x10612050609010c232208070902070218040f050d0315060503160e1302120403092111031e0a021f05030a0f1116140102040b0438070203 60
    0x25002100c0c04001c0c045500003100042a6166003c0245d580007929640c000007650351004a80034040c03405160410704c02d41d00c0300b030150320b01c20313218a40c0244a2540009000c000e0784c826104410b50040036064900c418004200030000042c0c0b090324107251511000f0005031042150b80b40800d410389001c101d092006200c40d488000903403000c0c040c05403c004106d01d885544481001410144c2030008064402d0030108108090030602c808184d0b20000e00314000001c81c200b20f5100f10301c680c1d2207040c0a0f440300034007140117400000d440c1500c40000020400613040101869861002a007190b4a10b03202000400440c41c801c0d0f102d0245401200c0c036202035080c9a19000e90700d80f003510986400420700c52001b45284001045406099651160658140c01580100502001013002e05131235100302d810803040f030041403508407200341941e04540d1040d441802038404072202c0b814100d05041c40c1c40040c01c1403410b41c06c0501b41010842c005489030345c0381c1003071091074021940640340e2500d4683c8185 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 618134361 1250 618133111 618133123
    0x1032c010f0605030307080d060806040f060c05040503031c0209041406040606021f0510050a091b02010b010c030e06190c03080907030c060f02010608061f0902070f020114070501061205 81
    0x1411003030038540c1c24802034800101b1940c005902048150740e854003907030400d000702000e0b000310040340248010701050008069008502e180108410840e02841c880140d03143d00c102d2203019015041805140b140c41e401c10740001d643d001070304005d881d01c2040c00c0060115154803850522402140c4144021410148282000780c0308038001894001d070f50200e007104603100440360451498880c400070b0348038908949900001c1c60040d0900703803803176240e600c039401808140040030111341c206c40d0103140c603c0c4140555000c641c010b84651035030110544046410000600351240c01c210704014010000f0071741c0c40c0c02c1d0000441c80d9038010504d0218900204800c00103440a002c0e640400302c24404100f00003850000c540483c03c05200c444a00c1c001a070140000f07038070820180c000e41042011008010302c04024880306a10f0041c0c1060704c40c1940800c82c06941c1c009043c00074004a0000154010074000044280c0c03401c1480c00e2180c2540d40700d096824a81040c07180110f42c00d400f20401c1010415 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 618135611 1250 618134361 618134381
    0xd1d0d0e0a03230a1a090d08040c1a0403231605150a1b0308220515040c0e01030302102a0305060105041d010f0b04140d0201032c01 58
    0x4254140c0e18540b503c1999481076140c407800d0304078412440484010030007480d035199a00c0030b41d1403401c1030620420b051040301201c00345124014018505070151091500da84603c3d44109148000740c01c0044207100781c0004000400d07400001c00c00800030401c802034140d0510800c0401402c1180d14580181c1009426aa8aa5241400c0c00d080c40341d0b9030f0303074001110300319480b89005841d00030400c01100d141114095002d02a400405080e0500d40e22070210740c40707410030f01a0b00d68510480d66403400800441d46010700aa0000002011200640c0d50704641040c0200b1a00300c40c25103407080b07040c84080a070b0048016030b20410519080c00e03014080c1889030342030240034059203c0e038000c07100c0d51113406c20014001c0656860004149078095820344000e002030742ca840c440410140b82003010100203000d070f01c47ca00b401450014003d0f510340300b118240d90401400007403568050003405a04072a50004a05042d11102203126109080855902d901180e980810038450680211800c58402102d = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 618136861 1250 618135611 618135619
    0x18120a090f151d09130302071a070b070e100e0108070e01020c0103050a020415030e16050a03170d020d0203150a05031f0207050618010f150b0d1d0d0e 66
    0x10021100d420b40040d9103500c0da42001c3c1504401e541c0f100c0c103c241d050f6001a40103a01c0d00c1030050b540b0341040c1c80c01160340710341c003299100341e12100402c1450070400240c5917a8501040900b000861b0b20300000d805c40030608022442d1032400d0009403850700003503001000602c040740800465a802100c40750400000c0c1003048588400c0c0000035102c50544002d0f42c180340c0c0301d90101e03c4004655046500400d2440d01684d0b190804050040180081c4040b401140c45589001440301900c0301d084401c4840c01041002e24a140d0f64414203030b0035000c8052911160184071040b18416640014100d80d410074400690340d25103a41c0e900c40548a0344c1021340903281d0b82c0c0041c420307501c00003501c620b68890300f00051024640344d001070b40130b0b1180810003042806103c050050820701443c1444819400c10024401140c0e00b0030958203c51408100340015200039070b00300b046001010003090080780c81b40010171030140400380304110307011000d0280c80300d50100080d09600c80e0322240c07114886004039 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 618138111 1250 618136861 618136889
    0xf0b0618061e250b012105030c0c0910080715030e16150908060117030c010e0304031707230c0301091211120a051b060c0d050106050307120518120a09 66
    0x30300c0d80c1607420014098050800c8010035126011001b10450400725603100701201d940390a03520701c13262103401e40c1e000c040c080d40302d0501007101c42e01e6001410040c2c5080000810700d440c905102e04c40d10940c04600c0c03a040c035640c5e4991074800c9c00d0034440a500742d0403083c20303542d00524204c100b821a2158801c00410400c042d0801c0c0010440441c10a04581d400c9140c5540907690352505402c5105544108095610786407506444070400310180003100d004070342805074200042502003103480b82071002421000e982205e840c030303102048585900c0e2406034089808041804000c03a00b101c20043c015506281a02401a807243e07000241404011325030300584100b0385100340ca252503000349039801c000d214001c1011012803031a40d0821501002c0d0310222045401c08110000c03c07988020500c58609003014000308031640104c00301c03070040b800c1da41c0d10084144c04902c038000511001d003014400f0a01d011400c00c0c8000c04005036500000d444030499920341201c0e0001c5e120300555440220311714451 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 618139361 1250 618138111 618138113
    0x504030f0e0102071706061216050415080a0506150a031a13080f0406021c02031210090c0503160e060307030e0c040f020d0f0b0618061e25 61
    0x11402041554103418007061501548005030308040540c0c200715126444c02d800c00c0010712000480e2809880700b6680145501030003d40c1d43d03200c0c00c0a8642602c4c449c1081d00421450402c0e910070900070841c0003410442c00d0729001c0d11400c01c00e08450654241d03206205001c244142c0c1b04404617010030454501c0750007440c513500c8890f03c484040800d40f03c80e02c80c1c40001c2e050480f40700c2c244c2c103440c0e1080e0341369541c00a00d038092000303801a00404005200f50350112041c050030001224941e141c6800650405160211880c5560301c000d1075640c1c0d1040714440003424660350700030b14504000710b464164680c41c2c5840e8140c1c8480481c0c070f03170104000303851031242140e84401007241c4d08907a0503e03000c6501c2c20b01145451420340323030181c841e41251516004415000e5103502071300140301c0780078042c8007490380843c24109403010140010b904c5034040101d0304001d544100c10b8210550041c04141c1002214000f0310b28241c804500400c3d00040040c4680c0100158031208241c0340400c40c40003205031072 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 618140611 1250 618139361 618139367
    0x6050709120212010e01140117070e0c030402030705040203090109060b032805010b0907080109050a0b01020d0f0e0d0309030b01081b010309020f094204020a051309061701050403 78
    0x29402034002c44006000e04001e6400303405c1900341000da03e009000b41708025080b12503070902442090140c10842c0740c50740d030860001c0b48541c115200d1a51070900d41c0c603441c070700d41d216a0010300120380c188521500003806403650300181d48500e007118000902e0701414108001a00c4149062510035007000901c074281c401e0002d45001040b240840c1d058404080340381083c0100a1030042690007030091041164180d804000d030307416100c0d401818005601d6070003000b01603581d928115405030300b1052000c1581481004908041000740c40d103071050707210200c0401e00b00c0344042426800929002c13014414003070008885401011004001c0c940c8504450f00d0450030f0b100782504c64109500d5041180039541c844100301081040102210400d08110b0483e4090955480c40d55030300c0301c0e403481c1041010400e119074a00e00c280080c0f0010200c2422410803009510071610b480600800b8403110a0100d0941080005483c20b1f450006000c1c0c00c00001e40703250380070040e2489142e0306040402001a80c = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 618141861 1250 618140611 618140639
    0xa091b030507050c07030c23010207030b060307030b010801020c15100915170604031d01081b1303080c061501050904050403022103041103030708180105070c06030906050709 76
    0x5403480e0005290b01c510504440c18411091290304c0c5201d112408814000ca00080f00201c56400381c06910944004201e4004040b00400e0907002d600206400c00100c0c4003400016400200201a5102c90307440e41d07104980704100303030451042070b0b40c0400d01000801081101b42d0005104614075080352401000808201c1035074016403489a89400100301c50185892004c0003810718503a1000da03648103422556070340c1c00c04503001c1d80003d114400301131040449400740290703608180d40300303440e954410a20441d400000d020740b020101d410480000010310381c0842c04041c0d44191301c0715566402e4003480c245017005c0913151858021881d81c040c0d0a81e0f03080400c4032242d100984000c1484c2e500e604043c0c0c1003090300144003100c03801d654070380d0008002c101c00031403040384180122401540c189081c50356900a190000b0f209403000c00070000d00010201301040104014940035280000c6507690000c001d0082e800070002c070352921041030822883e4001e5541c032912500d0321100503032411413116030680c = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 618143111 1250 618141861 618141911
    0x21504081b0102030f0c0606131803210c050403050f030a0503180c0307090f0f02040501020c010513050d0b0a1a03070902090105041d06030609010b0901091d1b0a09 72
    0x380341d907020080340381d00a009481e00f20031401c1c10680c0320f0f0f005030070301529040308586283c4140205d0249030b5080c01940b188001d4000d0b0401051540f10856500f0703107141d0014541c5c9055002c07524060180c41c0c1e8113000d8011040c45603a54240c842d46540703022450181101803850f03150b041441001c48496124080d66485006074140d6103403a047c0110301c508191880030b25035018041d140b40803414480300e81014101d00a0f20008004e205040b50300c00d001c034051402181d005070400e80528095600c254003a100601c4200503038040710b0b5682000071801081d030041141c0246844040000656440c412411100440603441d032510281900013615809540030b10b4000740d40c0410f940910341d10031404d890251040600c1000e5040228410706500325003242c440c1c0c4680300d104005003811006002d03080b558100901122056424235450a0281900380c68440c2d280a203440380c3c03c68070303200308030041d801c0e0004020001404001010f014079400160401b000082c2400c03110801c83d42a14401149a = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 618144361 1250 618143111 618143143
    0xf020702101b17070c0b0a0216030f020d0528060c0c0203060c0f040e130606060516060504080f0a0905030106060c02010512060a0b0403110910080c010c020103020c030a0305010302150408 82
    0x481d032400c1e0b0a8124010b1050180c03a0590112010840b0907005c40280802d04854088990199509e8040520086e080c00300a004821206030b5400600b008041100d500d40b0460544030030104a21640c0801c00203071442d0b01d445030484140c0301c140728052003421098003180c07904c4154001c0f142c0200340d50b00c50192848140001c0045c15003881c4410743e082e5409031180c45c030040c58030b06106468a4604a4600044d507281d49050300010740540100c00700c840b1200301e00d0b142035085100e912820000e01000b00196074141c03040114045d25180c010090002501d03a8941c4400c041c285400d05085801a4002c1d07401c0c0300f40c01c000c0c0009130381c200042d5a44243e59021b42043d50303403071601141220b04203034000780e2800d03004600401084480304048980000554034801280e840e22034001000b411845414929007214400000700e5100d0322101e01c41c94018180903203400d144c050014a10b9010f40705240001340d0f03840041c01103241100c20341c2500c078104000a41094203201200d51518460380044c100 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 618145611 1250 618144361 618144383
    0x7080601020c03190b011e03030c0213020a050309060f070c0f0f020904050303041203060308091311030901061802070c0611070f0303050a0810140d06020d0f020702101b 74
    0x103a1082110140018014040c1c40103400380d501c0b121105480d00c4011a498402800007080d95100d200156810f0314030f084001c4641e03491604e00351122410004160b8000d002c0c9800824510901c0c0010101034101e55180ea80e01e281010300c035820080e003d01244407490444d400e000005a00c182441d2180e030b040207104040e50700c2d51405420350607940400a4000540d82e0802052100200246118a00a460025a00344c2e4020304408440280c0801082c0315814000f800322424900000e41303460211540001d0058181d40c07109603030b0f82040b10300c4012030303454010074031024512619003e1504900c000542c1071503256510b600503180b49025040422400c1404014901000c01c14980181800c24480d14074a4907410010800d5101c0c040c208041103044000c1508030701040c00500c02c03241c0906810031101e84001c02c01440ca80743d10020b441e0a90280a801c5030b03c082c40c41070b50603181000c0001641c51a4600c10702c11202480c0584100b070204103002a105648914013810071241c0c00100406 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 618146861 1250 618145611 618145621
    0x504140307080a292502030d06090f0b03120d0933141614040305011802030c011416080708070302520305060a02070b01050a0e0708 58
    0x7140c18440e0b44407400c588103409098040c0034042d00c0c52002ea51040030010340040d80001c500d840344800303507501240b00e00d004404002161041d4440b2041500d5841500d15010100100c04190368070307508001d00050381ca500320300c103801d03991007002224003040d40075180c1403194101d803002d540180782202c20500d4a0328810b604004280a60403620803c0380045251101d9020340c003407002124003400c80099107003100380e550b801105100b030b920945c001034050303c03c1c2180041c00c07909200d607400030044442040c00040700090080c050203e9242404c41c0e0500d85c495940109854144060301c0c0605118400b0f2320806070301032074000c84d16212154514412145044c3c80c0140d450f2044242c00b404910380454410201039004ca0549607a5050460300030a11041c0e558420445000c8034036074041d00c846074030004198003003440d041023148103011081902d9030f0700d84640b030804400f21410400950b0010b04141041100b07002a805480c0a450000300c551c2402000f42d045c0c44040c110105000d441d0700014 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 618148111 1250 618146861 618146863
    0x705010c15110f0301031e11010f02011d0f0c040207051e0304051c03020c0909030d0911060703200312010e060406051e03060c091011030c0105010f0503150705041403 73
    0x30030400442d03000c0e903500720303811502c92960000c4c00100d8500d0014083d280518811007103105040e5040318440070501424401510405102260142555258094101001c039000c4810b001c0d8079454025100c04004000b92909205208490a01c190310502104000c1140040c0b0701c2c0c01e22015400e520700c480c1c1c058a0680c40c5004a03800b49501c0480585e0003a80302c01140d446601d403d101c4d8003203d803c0c04601c010808404412260360800d50f0007401810352402ca15000102d0850280c080201e40703070b580c880400c0060380130440a07030100d07101214207041091000601640914888061400e08031112180540020180b1448100001d000c001c1048c0343d68a80c002d9004001c004c2c00c0e200c28100c040710b80e403200e0a134418a90320900805c00041c200b0307812030080f90943c1d8001840c0c0c04600795234160035910403d800480700a40e20041c010400d10200902c9010b028045202c030110400707290404262401c4c42940420a4840d182014080d01035044015581a5403c0e92090001110b40d5004a = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 618149361 1250 618148111 618148121
    0x70f12170409050109060503100c050d020d0608010c03020301030b13050616030209040911040612050601060f1806030504121d060a03140c04050117011505030a1415040e0705010c15 79
    0x41482e03e03d00780002542c0d14040d80405e040716800e82c181c900c0c150203050740e00d086810007072401c4082001040803130f0030505a0b40c01040c504200707980c0050703500d0303c8810301400c44943c81c410f030000c65070010051043c4881140300c190300030507a000c4e00081e641d1030381c0c1d0181c50b010098249000c8030141f0700c51290321b40c026010784603030000142c010003c0400710b0422000c40e02200407924061403400384081420700004102901e45a000b00040c0196441e2000c2115a03516a61400d4104040303d00540202072455442e20f00801051368041250304090030050482103182d00c041060144a220034044141f1219241c0002c04040764040d4a461803074000b0b50142c80c000e0b041200b2451680100500b107a901c5d405001903d00a036a028184d40d41750584036140c060a01404501041c1111a1207032030384204010f5034044c0103c20080707881d203a002c000d6040b0319402d0358a00550644c129a660701414076114501c06048900d00030601180740c0b80020b80400c02c1101d010300213050041d0805c600d50219000 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 618150611 1250 618149361 618149369
    0xb03040f05210a0e0d021003062405070b04030e060d06061407110f030313080609070801060515070201050d110c0c09010609031103030c12030106030f0c12051b0307050c070f121704 79
    0xc900d010034107c1d0300080c014001d500507480b22900011502c0f1001c0c6001d400842541901d8070340c20711300a50f0b078031a01420000180100d0800681c0801040315468040207407903000201c08010509904108c0d0290011542c5d100f8020100814002000480d03850b41203031050f8682034601c0c0107445c082d100442d007176115000a4201c03140591100150343d0b60001017652040c181380c0d040c0c904240d2a4905242625405d120305644020502c1465060049001c024006184141403083c0380800c94820308050310001c60004419003070120b2a0000307814107001e03002c0083c40031246402c0640c14044080c00c45542800b016091600c503045003051510104111200001d5860071501249802030280320168401d00807a40000e06105d141c24180c1200d001e030200c9107000e92103a5101c90841e0340300000601d4018160841030320402003652400c1110001507001e0705413561000c1d591001ba010b060324181c040d030310500e14800d61420401c0304c10751446491210703550280031500e19201c102d80044090046d030b00 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 618151861 1250 618150611 618150619
    0x207021305040f14070302091b0319150b0a03051819080702040509010c020d020307031d010e040509030904060b040308040308090612130b1e070e0102070b03040f05210a0e0d02 77
    0x58144c0c2080001171040441b0310898502c010750741c07881c240d0301034060400c44024101c5010b2001c01e0a900688240c6100d95050080000d16103106a01b40e090307140069101d41054100054684011035050065540c80706800fa1031206850441c603819aa0f00403002c04816040c4c0c08804190070004840202e5200680042c02070000c3d080061200313000b07000c4940c03000d0140c400e9112980160b400030017a121240e070181c0b103028609044807449021111000039090400200141c4608075030380394840c582c09007030408000c40d101d03c03c0e803007400200c03149a00005001602884100005962681201e0590307074400c41844c1c40300e02e02008500076028102c802c1415025250820020b001900310316159580528038001081d1070310742500c071050b240140c500c0c0c01c05165000050260b4004c8070300c1140c2d0380c4184125200165500c1d80e005c441c0e00240ca003101c099405207120406d1240c00c008854407900c000303a04088030f10740509043c8851207501000410320203050f40d0200641e42e806000030300250050 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 618153111 1250 618151861 618151883
    0x40b0c0703090e0c130e2d01090c05070803040605060901120224071203090209060108070e01140c030d0501080d080105030a110310050a020901020d0e06040315023603010207021305040f 81
    0x2003801104680c1201c6614126541f4480034601c1d6400c4d481042c00d501032842200ca1607400e080c0d55802901850004805101040000800092901c0c00440c4918080c15001406081c00400c0010000d13042c1e010f2810040008c10400259a42400c48003022507442c1101d1135003691806002c005000d0311b0030190520000c1e0300008002038051f0005144a0310850b4003a00540c0d4000041d20900c1c03042d1004000140d8620100e092540686820400e030b1054540c01420b004401d82050f20750390082e008004046d403220010000c103101006031801030106424000c800b581000701180d50703980d1a5101401a011003070b0b29180c2503c003130000021425034048241b18600d00103020b20084d6101c0c000c0f140c018840e03862208003d80c49140404140307500207003014902442d6846000da2003c0c5505040d0f18075500300903103c428008040d02c82c2d5507825051aa00e4002e41c4203a140403900c2c0103040b96070081e4010081c0030016038809043d158051a40c00300010152154203000e00e042d900101e00070b003500c0601d = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 618154361 1250 618153111 618153119
    0x31c0f0902030d080108010605190501030506030a0602130807050306071715040204030303061e0e0118230f010b090a03030507050a0609140f070e130212070905040b0c0703090e0c13 79
    0x42224117043c1c03030322040248000c0f9034400500540e01681c1c020100d10440b994000d000703542c440d400184c0c000000900302c89108005e43c50b90801c9131300c0081182d251160700c0740100100b07001800520010a411005400d161510203030140c0b8144080c0184030141b1902030014a03038010702d0340c00b122446000b810071500c4039201e140290090080d030140c0703c240c0300c49440c804c5c03040c88110710100a5841e07600c1100001d92801040c008030103003e0f0000d02c0c0b07c94440140c00740c1c45100c0448150ba9407002d5201c449241000050b202c2e04604c181c02071401d040c02000540d1103911402462002c8035418540380382d82c2d1081d41409400c100310001c00030030080c10407840c00706000d105590f050b00340c0c14120a8541d001d00a18584eaa5030780c00d81302c0c85044c2200c1034000f988100e005003145c10306c0341c0003900c10400c43c820109441e043c00f42c0da070000d100c134580c0d0700e0038031061080c520f103465800f081c0344141c1c034540080e9440c05458407a60340320700c0c00700750f41c400e001600f0119440160380140d2080040705a0a91311 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 618155611 1250 618154361 618154367
    0x109090e030310050d050d05160f05100b031924020c010b130e0c040e120318010b09090c04110c0109060e0d0c0b010b180907030914031c0f0902030d 65
    0x9580c01e5000c00f1100c0d5000c1001d20b0040c1c00b0780800307076105001b819540701d0390030180c5c0d8540100c1c5607a50381820000146004c114050b103000304044c4940050002d4269251b4600300300c40141c0e408601a03032120640900d510035006100304000d400a25000ba08071904114080304000744070080480303800031803489a01d040540003405000700c2220f01110001d4002c0b00c20003280ca1360a40c0c1c207195880001d42e04800c0c1002d074440c00060303800f4015110350b110f0099007505170391b106582c2000c0c0469072400c5d01115080c01c2c820300c0d0030310004844d50105410851000e5954030075401000d4031a543c1c0f0f1801041034805981100c02e00078400009201c0700105003002c0c4010701e20702107464418050348281c1101d041c41408070a011650000d0a903503c1e034200234020021380c100070100304500000400310451981e52102d41c40c420341c11680d0110b608003da1901e00d81d0203003040c0381640319a00910a820180038160340c0f03610064000d100c00240e2441007a01d110150000740b2010707405005d00e10040c2c070120b40c = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 618156861 1250 618155611 618155617
    0x90a06060905070806041e0209041b05030a0f02130302042c0c120601050105270a03111003050603100c02150106080708090303090a03270803090a09020708070209060109090e03 77
    0x580f07038603076011030341d500414407080d66800701c800e21514021181e01c000301da4507070780a4800e40001400014502800016104c1c100c04e080d4010300100d50048100700480345140203414885038028810f500300a503c450317018400a1501000f8840d6440d685045001d03c04442407503000b110b418020710701700388003050319512240001c001c2800783c956105008200d5100065490480d241a500c4524141111800105450840da0070340b61306c0542c4a00a20142c2d1804441c2d00079500a05844d080b64003504100b20441c88100081c0c1e046c1400e060802c111a03070040b964001d8242643d402040840d10f1000c22401d01025004524008650380b002103803696203c0c0707045100d00c44644500d0f5640d260b042c2d14039624003048506c0b00090f480200030b040040c1c8182203902c824100450740c0300c41d2198401200e41c2d060860703000054558030118801d50103152140070040105241141146091416260110ba910a9043c0070b0b02500d40314011803c2c1da48114254802446241c50030003042c488500c2c2c0d10f49a074 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 618158111 1250 618156861 618156871
    0x30601230405120601050a03110a170d0f0f12050603010b0301020301092c0703201023040e061e0916030b06030f0a050c0906040611060703110d05090a06060905 70
    0x10303d2401c01810800c40005100b4141c480080070301c0102e0740f0795030368600e1009614041c030b500200000c00c002800c00a2032071341c2c00405010005030004030540c100c010108100280c0b0b500030884010424001c040d0403040c64050103640c01d1010566030f9034640440e01404d00e140389603400d507100100015101c80341c0d40c0191500074007010140c8524000c40900c1501d1704c01013081c41c5268000703460800000d9429003132600301184401603c658070100d0320010300c102c668010018049050a4010384c4a44908a075481c00c1c100440c1c6074508003820600d42041d006401051140108404221403581c4c1440c820220745800009204aa5901d480c0c8010581d5250344c4d640003010a05016140500303142800c2030b0303481501c5603a10218641c1d54000100080d1401030300075117001e902004104c90f2a04c0381001400a032501e0b455088a0558503051540b414030300600e040c00701444d002401c048443c981d0220780e00485901d5011501d51107000c8010305191080c04000c0840b8500032000903000810742080b8415 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 618159361 1250 618158111 618158119
    0xa05061c061203140a090909032f03040504021e04380d020703030908030108010c11070605160302070b0409050a0b09060303091e0607030302031009090503070602030601230405 77
    0xc80c2c0e0702e10203851202c0c4403180040125844d100466032004a00000d081c07514801c0c43d160404a50b240b051100712840700394182e001641c81484a00201110140040c0340d02d07140340303a44d88005101c00c5440c0c403405180500361282e03030002540703c40015404a42c000c002c003140c841650740c69840074070703560442d1000030100b08250b00c45c800014400c101c0320310542c041c501c3d8500030703d414000080007000b0360281a089003810f0303030703040d0740004125800082e41c0a03150307510000658030a0100c0c050034203000083d108501c0e50013002c0511005500200390b420100300300d58400710307940d10b07490164200707511900414030301000803c000030034040d280c2046014400b080303000c01c802142d030814404075440c11035500c2d401da8820840020350341042710301c14100c0c6940b9620380c4160038052002034151361068506900103900801486400c0c1c591143e044001c0c007610004129031400f42d1b480076100c0c0a907103000741c6441c0c0d01000143c02640100c0c40750855152000c400b43c0c40d40b402070418a1250401e018072401 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 618160611 1250 618159361 618159371
    0x30402010912120503090f0105010806070e15070611190c0c05030a0b0423010e061005010c0308041e02120105040c090603020d020907050702060d06410a05061c 70
    0x80740721491440707080950844403010006200d83c000341c441c0c3d407010700b41078000d02c01d000d52280e940100303100309400380140c4805080701c2d0900c00801030024082242d024070400680c0c0b1891081c0501c1c00484280715880a00820001c02680c010f003c0d5020790607820300c19039002844c5024155014400c001018420907a480c00f003a00c8200781a030743e035411080101071100d04400716021858142c140364405400717444040072004001f44603800d4a55460000c3d8003a4403080510021011400242c401381600b840d00da81c1d2884140c4005103004800741002c1c0c007200400e154100c0d0030742c903c00944074144e0042c2c140401c20000104540c000e1800711415251f1407c595804101c1c44114000c9000322600100062880d060700d808001500101030010b4082c85000c002e03500051319803074040d2181c1c1c0c01211000030801d1900b01010340040d040140802c2001024048007029541254020304030381c0400116a800070700500820250b00058100d5a4040800304611505500d20600c01c000b810400000740f01c = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 618161861 1250 618160611 618160619
    0x3030e0a121427040e0d050c0c01051204030f09050904140f060c0702041509150303030c0c0210032c2d0a0b130b130204051005241e0304020109 63
    0x418002d40d000f44480c020211082d08803000b907015400c6402e40010000203a8160784555589091507001080d408100003081854a1000502200d00c0c09032080c01d085180c1480c0980404204e44010070040c18032419041101c202481411190090b26020b801c03841c5900b0107043c101031503401c00c600d040140c801e048070211480404282d41340034401125566042050070b80c201f0019050010384406119000800000c1c40c41490040c0d020803400701c440f40350140d0443c24010b040c0c0716440c0007403081c0304042048100585841207040c10704803a0b41f80014009645c040491804500054070784068100d48081500c9010081540d20b80c600c1d01c0020305006103e00100000c1c403d070096070391034207a0001d400c4080403c4003069050b23846400f8410903031a0300900e650b440c3c54008195440c41c407506401d8622402c6041038800c00c0d800900550040044a10b0800010f00507140c185221022010800d42e00000355161015075401c2c5404071080ca104a4040484440c2c83d04101c50590014620303110003d = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 618163111 1250 618161861 618161897
    0x417010f0b0f01050a03181101120614130b1008150d021819020c03070c0b0306150c0c18041208040503090d0c0b03070c06060b0f031303030e0a12 64
    0x40440101a1020201c2c011020064030182c002da4841d000b410344503009100b00d80e02c2200c0320b240d0b06216012041c07000300c590f400142104050400f840320070340313000313000e103c0694004001e9071886000c031445030749640103403508009010300f5030300150018410041401c0603900309801074072407010000da10a4100221041048903103e0340c80194114004500241380c5240c0d040d403d0340d01030341c42115100c2a400c01300c00c1804a130310500c40040c82d60804602d290070020300d18001c00080105288050039801d103880055a140c11184400a9810b80069840c80080b8180a01d001c0908014441a102c5518041c1c400700200111822103099080d032448203045030003081c00c1e60059030000021410498000305210704644103500540d248041048001001001c00e401544038960640d61203004410a2900b80d00b076994582004644100031711850908a24400581c3c0d8000c10046107084401001d00302a002030040404a054a0140c003890b00240400e01103e03d03e2003503d40c0e120740c02005041d0714a = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 618164361 1250 618163111 618163121
    0x12071d030111161e030302070c09020a120506030c0a080102040e0610020d230a030e0705122d030307020304060e04140f0601091e0f09110306060304170417010f 70
    0x5128039083c00302c41e41d42d8100c5540c0700e21480c030428103103903003a4101d54070300760500400d2000c0f00025000601ea03020400c1d0102d01c0801048008000d5082040500c005484458140d8178048100d035907000160741070f5800c0040c04400600078082209164650303034168040d52003401204914031045003c10181c1c24035010100008500c4d50141c890703403802d000215007280001c1d01e12000c5600d481028072030442014002c2c044409180c030300081e41c02010a03401d00b0459640c2c4001d10031030014640c848412f9007c100d5079840012009082a08010346001c0310408412841d022154800481000701280e0000003d10070b0301e0301da44030321130281542401c00050769488030742100102401070210307a840c482650b00302d81041c014100098180e440d10084418907030085100807040c1914401000b41c074101100b5074018000c00d050900c10300c2074038006200d1600c4043d0843e400b40c100000090184910640c0320810700004058403580e03540d40e60a00e100490f80701540d52815445c22050b074020506610903 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 618165467 1106 618164361 618164381
    0x140c070b0709051e010e0a0305030f0a120603030315091107030e0d0f062c060f10120c0317090112020a0306120b0a24090f0212071d0301 60
    0x41082429a1841c7d00580d0250420303c0402e401204691b21044030000c559580c034450344c0100e5500f04074080442c4014a003c0c0003004065141d0060040c4070760501e09008443c0e118a58002218048007019108200c200801c2e80000d009442d0455080401495049483c049803100d482d41c103e0781c5022141142c2d01e064604600d05404628204a40102540c1e108000036140207030751808058181c0405000080025017400300502000c0060032800020594031009460100616040f07400115000b0a00c0c18858000c03110000643c2c2c00684140c0d904554152070070000e60007903100403298400c01d9110032020036110b050498250f0000d1003035000d02254504001e000c41200e1801100c0d0341d00700c101c1c20401c4083d034840980b010540b080c000d0300048080c51911450000d01c15072002c02e2007030085800300554541c001d0f0034501e60182c605c46080c444a003000806003210b554610b = true := by decide +kernel

theorem cover : BRFrame.Cov 617985611 618165467 := by
  have h0 := BRFrame.cov_init 617985611
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617985611 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617985611 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617985611 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617985611 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617985611 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617985611 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617985611 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617985611 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617985611 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617985611 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617985611 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617985611 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617985611 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617985611 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617985611 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617985611 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617985611 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617985611 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617985611 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617985611 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617985611 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617985611 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617985611 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617985611 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617985611 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617985611 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617985611 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617985611 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617985611 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617985611 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617985611 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617985611 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617985611 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617985611 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617985611 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617985611 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617985611 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617985611 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617985611 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617985611 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617985611 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617985611 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617985611 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617985611 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617985611 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617985611 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617985611 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617985611 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617985611 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617985611 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617985611 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617985611 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617985611 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617985611 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617985611 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617985611 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617985611 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617985611 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617985611 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617985611 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617985611 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617985611 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617985611 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617985611 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617985611 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617985611 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617985611 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617985611 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617985611 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617985611 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617985611 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617985611 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617985611 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617985611 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617985611 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617985611 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617985611 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617985611 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617985611 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617985611 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617985611 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617985611 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617985611 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617985611 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617985611 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617985611 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617985611 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617985611 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617985611 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617985611 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617985611 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617985611 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617985611 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617985611 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617985611 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617985611 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617985611 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617985611 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617985611 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617985611 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617985611 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617985611 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617985611 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617985611 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617985611 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617985611 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617985611 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617985611 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617985611 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617985611 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617985611 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617985611 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617985611 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617985611 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617985611 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617985611 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617985611 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617985611 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617985611 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617985611 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617985611 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617985611 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617985611 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617985611 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617985611 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617985611 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617985611 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617985611 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617985611 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617985611 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617985611 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617985611 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617985611 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617985611 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617985611 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617985611 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617985611 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617985611 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617985611 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617985611 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617985611 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617985611 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617985611 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617985611 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 617985611 ≤ n) (h2 : n < 618165467) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
