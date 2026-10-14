-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2399
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T06:36:10.542137+00:00
-- url     : https://prove2.me/submissions/0c7504df-8a43-429f-b5fd-a659154a25d7

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 431294964 ≤ n < 431474820 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 431296214 1250 431294964 431294987
    0xc050919150c0303061d041e050d09080c030a030c1e080a031e1104060f0216090b120f0c010f050d06080f1e0319140a03061a0a0c03 58
    0xc0402400554486082841041592500e40022454588041850342500a010040c108600f000b61003544640a84c3c001402c058401420042031000c0c1c8011f50b58001d00389051541c0050a0b508440ca400e00c0c0500445402d06c186659030040203000d81041c5030104840b50707055056100d181021125640c0c0264600390303060300c5842c0d006403d0214001c20181d402801c48005035483c00655100e07a01c1d45d182005409003c4c140c00075041c080303840e120b40c0da07a42c156400c0b1111801d01081701204408240e08210240c200c1d80d442c80e901d44800a0030607890340000c084800300b51540c1b50796034072614590362540744a4039400001d80c442140c02066510450310003120301054078060b8204800c1d100c031102650b1865020511540c03141d444126249400d100403503010590340001c1040d00c070300c4058a900c034001d2401080d415441d403c150b200c03840c020b081d140075040f4041c0c946070713403041180d401a000b415a070140b56200e0300030b00c6030350300c81d4060384081384d40c0e4101c0d503181c0040517152560111204112032 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 431297464 1250 431296214 431296249
    0x140a06140c0102030c27100503090f060a061514030f041e050a17070f11040b06070f120504080a060506060c010f1a010801180f02160305090a090c0509 66
    0x802070106400c00030b01c0658014480104155943c680161b08040c040044541c0c5d100c0d03070844408684881e40c5c504000d14424000341c00d246031a80e50341648581442c2590244003076038000c11040021040d1075074881c0040e13800c80c000710400c10f4401d080c121a404517100c2210305d00402040031860842102400540c414414018505800118504007003002e00400084466501040e0890100b100d07120b840006c2d000c07550344660170003440c0e80307030400c40b80714408018080c0c0901501c120100c0e1165040300c8030140e000f521560750b44c0203600c3d0810740049250429290041600c644465061260b0111000c51380003c0041c4034400f49521a8001040060860b5074044010884011024400e01610354220116400020030316407a1810b001069000000d5504102c0240018003403200d000d600c00c2d10300d0300070110014040b030703040542100a200380e21041d03600002001e4000100b40d4802c1c0107006984041c2e0317210300311640ea282441c2c240c0f0300003140000880c5040c880c0e00c590307003460703400d0030142c0500 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 431298714 1250 431297464 431297467
    0x80a0f06060504091503170d0c0f140705011404050f0705010206060109091e1104060e10091703090d0b01050f12121c023123010513090e07140a0614 65
    0x6c030340d910001d1b85628042000101c401082c614500b240d1346c45940c00c15030480c28100b001d1084003000520711040128103030910140401c031007080c04001d5000b02e4420032407040b0411282002c0c18115070360700c075040344100c062058000104055201150480c02040c06840d02a42c3c0c178200f0f0003e6014205034030700c3ca001240880640360110071940990203080200c900142c0e5120f050480c000c1c54800000e040c3e6000c0d0a504401884940c2c1c000d0f176000448480c081c070100c06c844880c01c094110b06c105441540d01040c0e00c80907000340074606c255981200c4040700c141023a1b4918500f4840680b0807904919000c0c3c1048207036483c0c248420000300f02e80c0246d804443c42110001071100100c0e0404850a0203e43e40006115006040904800e44603490f01035110143c031b1402c4a1066111180204142c03200203440d508200741e4068020307030f5410081d41c10800030070346e150b0680e64010100e00c140044c0342e02c650301001034140c80c40c00b031030800040c0142c048a001c60030074105545000c6c1d010a0442800ea0 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 431299964 1250 431298714 431298719
    0x80d0302071b14040b0307121e12020706080105030f120307021603080918100b0f12090c01180612020f07050a0804060e0901050d0308060a0510080a0f060605040915 72
    0x180031542001c1d180783c0c0340d02d00800c6040710600003158442400c880c0039510101c8103100d0102005259030b19258041d46a52403200ca105404080070265440100318078402817080089640100b50304041c1c0381141d5461011b40c2e600d608050740d5911507405003025800049040700e0b09807590000f1236100205004540044c034803031940b0122420309a20940e0904000324080000e4545101c3c008202c20350701074203106c1c604040628914014443c030403130404040005410440964460a41e43d0445200060079210701d4100945500c0300c410114844c0041c241480d104103d48145e4034130000c0e16115500c1c110050a00a503240007035100d072408600e0343d2828801c0d0400120304000b850324a1340b14000198803180b42c494043c0078058520405803081c814840103110f95101c010002c1103560305494054810b0301c55001003200b100d02c50700003a800102241c145a880303a00080c0c0140180342e04201042030303203e82404c4604540b00d6005410010b1410401049128841d03081141000d8019448229803075 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 431301214 1250 431299964 431300003
    0x509011805060d061701020c150a0603061109010e1c030e06040e181006060507030c14030309070501021005040302300301270506060a18080601060804050610080d030207 74
    0x104070031424800305848071300c14001d900c5543e11189041c1030342d100070745c2002181000c490300e8540300e140d60110b1800610002e10b080310650450f00003103400c2a4204010080849101140c0d844080c04038040751280c1c1030044c2e00e080c40400110003051030b04050901d0140703503504403443c000381d044003a400034043c4000b29a43e150072511074015502003100010440c01501a00c0c20a07880c042450b84a514140040048a800008444000f0703494684290f9503c900c0c940315415019840000103a440301000704001d02d00000744079001d42e04241c00710340e0380d604c0000500d42601c200300c81c000c00503040700c4001000c09081c040003d40c81c81c2d16038071501d9040c002c3c0744080d515400c00d911140c50340048000802e00b45004d04862150403961075400d020900d0704002182c1503103e40c0c5003400400c05203070502d0104100c60314a05020341901c105540465035209002081c00d0800d8501780c0c0e560041c2000b04e86600c180d104148101c0c2c010000bd0310000020752001c4e00290408507054030b8030960b007884451040c = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 431302464 1250 431301214 431301217
    0x8071701050d02130c0207080d0509220e0a080a032f071712040215030915060a091404021f0206010b1b1606032003040807030507051603120f050901180506 68
    0x50041d50040c410142380c110814604a40c1d000d403101404020091420300381c48003210501d540039200b42418510140580d42d6004006060075070340d50b8090100e8900c2002400401001c9a40040c1e4041c880030405c00034020850f00801400c2070355041c84640c6c0000703900020090a440e41c000d461910521200c070b2803040030b03a806a07107420800700d0000100401c41c60b000c886081c00b0240c40c202c1ca4214a0300180265440740c00c0c0c1c081030360750f90142e00001d5480d994201080054001c000041c0401200391600c0308058909550491081d004148081c115900c1e1184000518509600420183c1d2801c0a284020740c041e9400554030510841c280080301c00c100070f0031002007140c100344010310345810802411a090301e42d00f00d80c0080f482e103400444d01314200039242c00a82240c5070030360b01d441515003034916214183c8020814058011584400740c03210b41c481701124080c41c0d43c4031900c1c00484e01204c004030396460150101d0014844081c2e254402c0d0b8050309000603180c2503200c80350300c58001406a = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 431303714 1250 431302464 431302481
    0xe0a0b070e091602072421090305090f10050d050a230402090702031623070609031a04030f050d14090109030216060c02190b0d060608071701050d0213 66
    0x20140f1200700001201d90420081005054110603803e000c40300c004c422241020a01c01681005040644800900c0154000d2241e5244052003005500e0151070040c0483d0040c20340e01d03101c3c61400500241c02d0901c1c1d4000d00e81500715039180c81c54501403401c0711000300809030140c2c401a584a100b007009a10041224500f4000c03400d11803c01d01d0148104504c8001c000e001038215001401320a0341034940820312410325074408612242031900301070303051210100c0c2e251034a66201d01080040e440d600219000705480c043c606846103140c2a600c036008540085c2d80080000384108901d0b280c8034844c1c00941601c800d568400b144c1c48602c54202c0d1f001010540f503000c11650368003680410150104209194150303450070445a1501d00711000c2c100ac1044400a8004e280814004e2a000c119104c030401400d5012166501c6145070844500100141e0198002281e417400214810b9406070020096103c942509400e041c0c0c2000140701d82d100800f2001c9030030844020034841d903030350300740200b414 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 431304964 1250 431303714 431303731
    0x1302150309010f06180b1504050103020c010b0a090c121e050a09020d0503040f05030c030606091e04030906030c03200c070f030605092b39150e0a0b070e09 68
    0x45100c0a0031781081120b171000d200c0c030302c00d02442c8010200060950140c8080391008d003001a12002100394142c0940201504254441d0512001040f80d00700390780440380c225407c2c0d8418852808004061040700d003016420000030369010103440c002c00311600000e62181a105000c81d0081443d03001c5a89808100c0c0200c800d500085400c0c00080055018080200030403002096040e0a64000c0b945855018004901428101d070004d00304016036500343c0001c2d524042c2c603c00310710306818001c09400e9a8050103001a0500c03241c521094071070f0142498124501c0118803000700c070000f100c0c2c0c4c181c0c840120508203010303239200000d0240d0850142c0f80114007902002c6414a0085801410039100c50b4408841c100041ca04d41c1181050f050890016011810000d80d01d003490300a942011105003d400d00324210b03603002e44141100040041002e41c49025404c40b14000141700ca01610316444181041d644100340c50b00c08641c8882d0702a4005000c1e00384881c52401000204503240340407900000b = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 431306214 1250 431304964 431304989
    0x1203030515010c020d1509080d0f1107050d0e01020715020708100606080c0705070504020708070b07110307020910120c0f0b030601080105041d0313050103051302150309010f06 77
    0x940d140d4503207514640000d0034030300044152190744c000380340e44054207800760a5001e25200b81c0700a0581d40d100202c03260b04404c0841e1a00c00c0b0002d03074030252213502d0126519608105900c00428020300940d11001e9000014010390309144404585412030080043d0440c820071070001800c030040b043e55203110300030f0340c040c0a825051811592420758100301c0c00713800c00d15103401080115070208140741c2004a0161072540c0341402e042143c50480940c00555001d0700c00075801c020080032100504c4543d2150100755030641d190442a510780074140d07502d02141d0410070403035005143c0200c01581c01801800303030601c542c1d20380380f4209814040017402c5a500c01c0301d110502c40054a084400300a11a00b86541d05d1803400d080000c010310018070403e4009c0e0b890701c200564680341409016140d130800341c1100d403200501503441c00842014812940828500804070301c00c01042e481c1c0e000d10310740181101c0c10038240e58082c49031580c401088076515560303440180494150034000c0308000c00c0b00d0b10320750 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 431307464 1250 431306214 431306221
    0x111903022215030c2309150405160e09071d012f070b030c0403021c1205031b030c0a0503060a080d2d230f0705030c060711071a0412030305 61
    0x8501c9003103400c1178400ca034407041e21008100c000444001a0401510b401c8a60746900410b031030884e600b803c41d6980141011304110004083c1c14030591030000c030350b8450030640b00c18014001502c400b611a840081c00300d264000c2c5603000c690b24031403a1386c0103161041c805c040c0c03416000150341c000c0041080301e085114511003000d004000000180c008612a21728500b003800c00100c9038804c070f100084c05041c100807600d4044045000c50f02055800c00d05140c066100e12100400f590b10032142070200c280903500105c9115844800d03680f08072405007000d450501150819038154100600455020740c520784e020030307003440c103008000d181308140d10740180c0038a40d18841e41402c24600a207807604d0f194490022103180c0e1044903034081012500c0e04840c60407840140030400c1c03061000c0070b0903510000518204012000005140407142c8a0650311961a041c50841e68548429030b1851503512400c801e03c400c60100504419031a040c4854502d019904d814008803135192034030650110343e4a8080 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 431308714 1250 431307464 431307473
    0x218040203130b18061f0306020c0d2604020d052b092c091207031106010608040c14040204030611070302070e0601051206030118050a11190302221503 66
    0x400e8002c005142d11134112090744281c0c0b50745880041c682c1d001c0715041035862410035040e242c0c0310091034000c1400e650310004290b140f9501c4506040000004500000d054840c06810403040707114544135102100949498081102d4000341410998080c091802d0010681d40821b540038210368000c000e05150b481058009822050254407443c1c0304003181c0308884040421040c2039400301c5548403105c0440e1100c0302164074002058030044244400014440185500040400004003100044030880e80c0c071244100c031450703000c1d2401030000440032802e10005481902c041450180a40b00504007903a80d1074400940700705124050382c80c0740005000c828035a0620505005c1e00b40314003d500381d428001d0009055204d41c1c903d0710256800314020172000d42e802e41012160203000d45000020403c0750811030746800754014201d91007540008040920300342a902e000211700c54034a11022107203103800340480744451001c8200c00048218030000407420903c101051807003040401c54009080d40f41 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 431309964 1250 431308714 431308733
    0x40f06061206091107060c021c05130f06020601051018060305010e06011103180103090b07050406080106030510031e0b09010b010905010e0f0d0c03050a080a030c05090f04021804020313 81
    0xc50307a0313060000f0341c2040421007040b0340001d603002c07100203210511004102c1c1440d041c95410240100d901010b402c0700daa108014000c3d100c52045c0404051f40d0b541502c91a0300c12034803031000960404001006980f61000c01101c404a0b00d0508148144480700200c0d408107890b003050001c01c2d07890006100301000d4400d1668095002e00f0311161050038881115924012000d001c0560f480c03010004d40e241e4400c1e04000e8041d64021100301440c1012040513080d500300b07004003030014030450000252244607024250007081c64080c0362000c03600f10740320319010b01001e00c0240d42060844500c02d000412000d01381e0b10580380381000040e00c03140d50000400d8490780e940058100300c40801004542c0d42c9802024000281c1103c8040d03440d02c00b0b1501c001480e400d940040c00c0c50143d28100703004d00c848a401000342101a640800075050b8400040d141c500030081150707008007551007006e01d1410315074000c14084142c8000c440d0103e0240000505903401125901e421141003501ea608102e41103d = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 431311214 1250 431309964 431309969
    0x4051b0c0307140732150f0403200901120314040530030418050a0b0310050405070e0c1905041e090501050105122806060f08060303190e040f06061206 66
    0x840017408040b0544113040300801250840d2080324044100c0e4240084e1404441c4004240c1401c55180d55036424180340d0740b541c0c0200c50402c3e03860345010f11000c0c034080b807000741650704044003101080740940381143c104a00c0b05a41c449224108000b180c00d030b503009180081401c0410301a10514076034018141200c0c510f48071035810b40c0c0184414451030134960441c40c82004445e0001030f40380c0c0d0b5001510003070308031030700b0682e014011403516080c01c0180340c004500c203030b000d0320031204035543da504130002d81d50045460514029041c8041c43c5200024000c0100d8100140340041c14980c480800c0c9081e0100d40350522094841da0714100420045801494010802400c2030b600340b01d110500c04619030780c0108000051040000381c0c0d521081002000d100302c80c0882010004551502006080e0014010703016010491520000d8042d00c3c000044410514001401003205c504140e0161002c14070041842c0e80581c0b07801b0410790302da0562090000411179907a45041300c00441c02604101c60198 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 431312464 1250 431311214 431311259
    0x708161e02031501080d1101090b010e010314070e0a0f111c1805120c030409050a05040302010e060610030e120d020415090e0f061c11030c04051b0c03071407 69
    0x3c004020310500400d142da0300c0071240c202400b031092038003803503401008890700090901022100219240c0400e200c01da050707038440c4103170106a40500d410942c1c0d60005110301a80b2041078000202e491080b80c014800562400501140550f0001c2c0001a142c1040b440e00d18076600f03c141d40305004849020b000040001e00d001446442c0340380d140c444d00c803416214019000000024200050b84081040b6030040640800c01c204900b08090b081c005032500790b605074010b600740080d030078900c64007240184c00740200030040115030b8401ea4040d800303040601e00c2c1700d0150191038174404203034840b00001e00c040c2c54600c2c80142d54504191a60400c460340d90002000c002031300c4014050340c090f010286070020319243c036803111a07450000080e40012450200129500400c02c0c070800c02c0364540d02c45155074030071820345208410038018031085070400c03150b410521484030000b04c07480340d41030000d080c009100d1003903d00d05662034030f0f100d00c0c041c0c50105220300c583c4a258200204406a1002c5850207040d = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 431313714 1250 431312464 431312503
    0x1e14010503060a020c0312070302090f06091305071709060103051501030804060822050105060310020f0f0a0512180d08041110021609150f06050708161e0203 69
    0x6090119603911401032803c0061036001500780304200082003a078030041c0100f03112485030720b40b03034900a020b134012040340c0c1c0c000c01c00304080c040945010015500403035400f07021a00700c030f09400313032210103041e01030030150901c5040c107940304209184000840c4111151401040154990301d07040d4038280005104066119603c001800080c42e041c00f01c2c1c044850346d00e0070401c0c94a82d21440d125511582155000e40385542902d0b0342040010341001e4030844c0220f00350b0707240d05188a5100168803e107100c0303d00d604810040c0d00b541d1320038003024001d641d080d0b140081c10312041a0042480031020f030b0f1000c5416480b032540403840f0000300241344441c0c005140c00d01c1c1904265070380c0006c80510240891240c0041101502098420401a09601c0c00e202040c04111343e81c2c40c60b0f800806020b000914401ca18010110300010094080c5c0201c032503a9807014034141c6c00d61141c02140d00700364200c40301c08549001c038a021400810f00c0449030920152580c80d071194a1042520b042d035911541102c8003103 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 431314964 1250 431313714 431313719
    0xf07140606030604030f090e09060412140a050705190807060f0b0d2301150f0f06140f0d06090506090f161206030503040902071a040f031d041e1401 65
    0x10041000f0781c015500d801c00400c0080b400000307030740c00c40c01504059080e01d41d840810203005000248940150b020f040c86141d2440145422601032011106001d842c0c20200001e042c418407440003820b01500038010b41d5200140300152613100c031541da60503210108041030b80001c2c0411480b65600743d6401c00070401c8507080c00d070041642c0d42605000545080039000900c41e0f02500c84001010a02e02e0304020003c0c0d20100c20b10350813004c028003c0103400a10400302181004101003618252082e41e22190002104240250025400500441d444690074400708000c505240030340350142440980100315464000140600382200070101003840507000c0901590111084041c80f9030802440c180b84e09586040c0802c1c00f401076a4001442c900c40010b00282c0b50506034050003149211b20504030741c40c003c0c08074009018000751030103030200103010b0701b40340081c0c0a520440a030078500d80422005040000008044803829408441d0680c0410001c5008103054810080d00442005641e0110b50 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 431316214 1250 431314964 431314969
    0x3080f0609061017070518090c040e07021608030301031203140615090613061b0822050301021201140a12020f04240302030607140712050d020f07140606 67
    0x40c07020300402d01403c00701c8a640c1070340e4858a2100110b114580810744039080c5890020003039413100d440c0d0400c0f0032040460350a5071408181c001e01482c0c8210170303035040c1420440010304114000d03144500394860844540b417641480741c2c01c4c074003d000c401d02440d140c0d807450034070007108885142c07031904241c6048924085035115440c4250045420f0b1342546081d140605860000e00c40c03011a50350212000c1342c010380341080304420b00151201c40d82c0307142d100c1650346481184c00c0d806c3d0000030000001401580c400c001400d01a010050740d80c3c003451007403030f52000840d0880e809000c5aa0311910000014400d0703001d1116903094201080d18520b081500e003002e00e80740c902040000911506d040c8110b801d15130f849811410b1000d8405140540103035a000c040344069030b01c2c1c807080b40203004200c000ba00c0d10340605041480340c03202e40206407500c0d032240c1c1c0d030140094002e00c00005000082c8032014100304107201916084248858541d038561050a00390342c021188540a00300d1703404a01001020b4 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 431317464 1250 431316214 431316229
    0x1b080f0319110a0605040201180b0301080d0c02060a4506020d020d0e0d050f03030f09060103020a05010e0312030109061a0304020609060f04050d061d06040206191101020406050703080f06 82
    0x70f5030071520026954580d440100d64942d0544520b01031a4604c1201040480356903004504880e02c0000304c0307040b1240c0170340c2914204000301010354420420301010800d18064a00c0c0f1000b440300e50722000d04030780c000b815001c2040134000303000d500c581d00d800c0342d21f0310c0d00d10103001314042c040f10300090a000c0703551800250745141c1c0a6005040004030310202029440d401d942421041d0300006442c000311580d94025500d410481d0801c0b10002140003103811a540410618182d9070080c000e0702c0240d08000c015150845070b126025010303c40c600d400c81c1d50f0700d0610007a5010300b00d11741000c05c01034941088040031a40442010300c402a04005220041c0e03201c038110b603200d06003a5400d070b88442c1d14281c400c000380107036030050b608406030b0b201074801c1001641c013104441d00783d051483c1d003400d04651013540c3c0c0c400440d8020740102c41009590741045050704007070510700061805209000100d0303009070980e04550320003004520041010010181c0101a02e41d2000505c1c6906546150010008402 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 431318714 1250 431317464 431317483
    0x1103010e0f1b0a1211150f0301030308070203072a0801020c0601090902060f04180f150605030c04050a0b0307030c0810150c08120f0105040c08041b080f031911 70
    0x811403442503641d58807005030100c020805661103884002181c2481c03103940d170085594502c02e403041d07000044000341c1a416640d003110541301c0c69007103030709507075041e0382440d0090030007402d521042c80701d5030023b50595506501d4541c0c1303000d141d2000c006e2819110b21350f0001d0300400c00c0d07a40140003001280c080065058111103640402003000541800824a50300c81c0050403403620400081c041050108410450001054102c0030007041d2805410007086401d00d0300f01c1000f600d662503017004858800d8000d542c001c1241108189400e07034942c00107898248540c000c00503d030000c030411001c143c01d0311519402d1800d60070a022103140601c0106040ac41e00e00030031211040c01090380044c7d5109040300083c4590064400e66100d821340f03a10040400300300d90700c4103034a560f007001113002d0400d4003070b00000b040d043e108c120007915241e99490440d42d099001082c00b03d00008000759008003003003046d03061300403180a50340e66800000e81010301c0b040c81c1050418414200c000d8030340444001f605025 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 431319964 1250 431318714 431318743
    0x901060504050106140909041a071809060608060409060609090b1f06092702030c07051e0d03050c0909280b152109010204081c05070b0c0906071103010e0f 68
    0xf80c2c2c0ea546089c108041100c4003c0d1080c20705c0b80200256981c100032048109001d0003903417009a40e8826404044c0c90780350049400003a0042d012806504090f0030906095200344400700b14142c9230748030401201d1100c80180e810303100c0e010911980310a8410008100e104c075640c600f0302d4a041ca90060481e001520810036480b00c40000f40c0090300380200681e0b50389003235140942d6a8181a01001300da5044054283c0721400384e0300c44000034408a4251150340d0300c600d00508001010140190014400104080c202142c10072446585a8900c20b210344220390998a00c03040740040408620b505900d0b600c41c034242407600200400d191342e00024102c2e0f05903401c900035540c0c0c46074401d03141e640e2544c019650382c0c0c6c480c80c4e0a0000f02c0b01d040d005072040d19620b100b11454402200c103418000014403c2c50b80210300300300000c6c0082046809503d621028240381d451400d400703100403440c81d81c010002640c03000d1040c544650301d0b00c0d082c0502000c00c1484c50080041c0d0090702c0e0950344035071031540c0464 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 431321214 1250 431319964 431319979
    0x3020901030f0609080d050403081003050606100e030d020105040308090a0f080c010f0e0c03160b0f130308070303060509010e16081305161505030709050607080405060309010605040501061409 84
    0x803c14a600030024a5900c2a411a190405041e805000e0003041d074003100032400000002d403013801039060b9841101d4001005000b2a100d01c070034000d00b103101e9441e034010002070180715105501d04020304d4010b1000d03580001034a1801c0d0070000c04645014040c90f81c1c40e007005880001023822458401a1990040c1d481d540d2922101030f80790041c1003031030300d0109250070000d8a0740122000b04441485500540c10394259001d540070808000303010780210500d444050050207010b09011018014024074492881001c0d81c5a84600c0b08542250300c1c114002600c51005100505210307080c18010442c802a024803410f00c81407016016540000f0041000100c0000580714081c81c0395000c141034001c0b0650303440e144a01c8042000720344601030791105403007900404500600c0b9500316841400d544d5209807406081108014603644018010345100405100c08a016603c42c80158055001ca1000240f010b1510313050000ba00d5050b88541c040c0011039070115034803040f51080700d51500c1c04441c0c04 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 431322464 1250 431321214 431321243
    0x70915060e100f0f1e021e01090209010e040309081c020d0306120f1704180e0f060f101a09030c030705130e07120503030106030e0a02010942080c040302090103 70
    0x444422103030300c005c01030403074209010b0004503401082000c10312110980044c8480762960025090303d0804000035045030700b6600421241d0705003464a41c002d40b10345800200e45503108030741c0e4a0284464884001164030b680518445038040020325011102070609211f05490140c0080c64002d516038041c1c00182c240c65001c04204004590b000212140d0324403a031680e031185124001344901c1e400d940c00181c50300348118021400081c1046103d29400300a014a40d070304c3d681484151005001e00d0010448800d002c078841009100e00b240c01440344611984031545503082600d0401c0b00c0f806035000382c001e030000b801a42c03a03041c0d50b842031042100011500389082c90355075280000c01d03400684007400085440cbc0c00c100d0044010b6040328480c2c0d80601c0302d200c500c1c1c02c00380c4800b1500c400a000c140240020000d511104064042d001d00c206259075070041450a58103420040c00c5c0c41f80070041902c4000c40308150020700154005003640c031b0303190030b143c10350b4042036095606000c0a4001542403031007 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 431323714 1250 431322464 431322467
    0x510051606060902040801202802010e06010321111c05090301050106030603051b0f0913020a15031103010320030712080a0917060612070915060e100f0f 67
    0x440040c21541d101315a601d6517070060b14001c101e0120803072480042603014110103001c1c00f0681c0e080c3c6c1c4e20110042c035070b4412202d03c4611448505502019552100340d008480750007840a00d0007140100d180300c00784103c2d181e1b8417904580700b400c02010b00c002c010074000c00701c50014a24180c00ca0988a504000394104001d0351300d805082d041c198598241000401c0c0701b94580c1041c1d080303902c510200c0d020a21059860720803108401070407908001040c041541d607260410340300f50846d0005450b107440103c29008074010b4121500004911071800e07002110080d41486500c523120072481210741154150b41d2605840b007100310b031003103c3e080d4500d81543c003940d080c44904014102c00d0562014040d0074a03040d02c2c6a0410038003a80441c40d00400080c000ca03554a1075a100d04419000d40720740c0c0c3d550310401c42c0e05c0c4072064035507440d4030600c680400c10000700d01c51f0901810740c0c080000c58240c513188000b040e04c0101c0860340d000320514101c1500898008580c0c400d44175560401d081442c0281c8030 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 431324964 1250 431323714 431323721
    0x150a08060f04020d0f20040b1204080904020c0114060111190c0509010914060d02090a090512071b1403030f0f1c0507021b0f01030b12011d070510051606 67
    0x7003040b03440d450f01c90740c042001c0b025031100c021010708001c101c511003c1e43d2001b07440d60140c2c2c4107500c940141000070a0001e00c4c514001c13644544198a41400c10100502150032a0090384008080b80c0d502c89c04038500d244606582036008500b40390204801c003960a0054590a881c50090100314030310802008200068460b2000780002a12202c01903030748941d90400380400c0311002c1040c414800200e079071820108107032103405401810840594881d0071a401c000c080076a0196014020100b00302d03030003911070700200f010034081c1c40301040e441c003205146944602644d018642215a460900389540c801000b03481d032407240201c0d110f444025095001586208044030410003402d910030f18404070320382d5031090f801303450306a08551202c0f8401945102100c0a0104140c1c40ba101804800440d8071030f8100040b40c910103401e1802100c2219070841c20344140f05003245a80d10740f640f405c140400304000b07010007014102d801546011a142000d440c0d88900900f101d030000c11443d01c141405880d40 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 431326214 1250 431324964 431324977
    0x30f0c03010b1606091205030a1a090112031416020f04020403021f02070510090314061909021c061d060601230903060106050306360402131a150a08060f0402 69
    0x3651b40020034074288009200350700898044904600c0c202d01c02207004400040b516400c00050040281a424061070760040071110038100d0421101003809000b446000001c1c1481850b03c00580600da40640b04120f18410b02c0d07034a26014920501080016946400c0c0b4182103855040180024501c2140c040741011003d07082103402c00b100c00e0149806c140d1244002c4210b80c015106000d000c400d8034186601c5032402c0c2c0d02a4046400d07840d910146a20710360111090384e100501d070400c43d588403a056a012038401d00c00795441070307640c450b03400c0030400b104c1440a4802c000000c2d1826182c0000007030f0814a44010b02c2c0380c08129002051034210040e0102d601b48080102202c641c3d40c0e48000003042540102c5006020f00141d000300a5041c03004101d4000e401e200c2c950a0362280d4030404031400c0504010b0042e40c0c40340710000d81144000f264410f4281303014030344c6c1400c01014022400d205200b10803869445640c2c0f02080050502c603405051260045c2084138a20102003e0034000f401900900 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 431327464 1250 431326214 431326223
    0x40e0a23010c02030306100e0d080c030c010f060602060f011a0d060e040f0c06110616090b0d060306060e01180921020703111f03020c01150b030f0c03010b160609 71
    0x21440c000e80f074001001d144190412552014000b2070364404903000c10f011183e5a400114003010240041e11041c082c0c55036a5400088a050031003c020090948101344d80540d00c241e581c01c42440742c1d5505111b942e41c00302440a4061095260582070441004084281100d1000c08290780b002c0c0c00c902d4002000415008099068509090a0055520f0f440d0f44080322199040c0e500001c006028080c40b5424a0b0000c0103440150f40d10b044081e04501c009500000b0032040d0007000ca401c1c001daa010709092004503000084c1a421403030300404407060b03504217498840703405c401044034800f0203110f04003240340b0707080108a04c0c00900d4250401c002d42d200d140900d1280c0310f85408142c0d800251902240d01912508042d109200c050102c8680ca182c890040c580f83d01c9460500c160081d00103204540407400005030f000188120720f510514190040303242c4003000030902821740002808181c12506000945195501d8035603498905d02c140b00f5026466080c40d4800d0003400042d074410250039402c07 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 431328714 1250 431327464 431327471
    0x50904020f121515160803040f05010b040203040f060b0102120408160b280c020d080a18140f0d02040606030209010809010c02060408161202010209030c040e0a2301 72
    0x8001c0c403814a40c1141c070030180280610300026020980403c15043c103028058982c0c00d4500b8500342d054002d610054250350240342420f086400295140015031086024440d024041c7d90285010750030b40e020104207510032070041c000d22000c40e0042d1650710b4010f0740710f2800034481ca130303d40060741868841d0410b1154080c000c10300140c404400700d98004440b105a4180020549422030741d00d05000b4100d508446250580d00f40e580030b501000c1d007880384407a500700b40e41000003a50010380c4080710310b001280d8800d13001c034000c038441c0d41203160454a41511f00510307a6242c02c22809100c0021000301d00d520590395642c2e520029190f03c1c28a0b081241c0140041c070041d500c0303a90103806944070355100b40c009429100010070294042c851000c424401d0790140600c1e4031280c032081556081009000400d4003032604034400120400c2e210b030350a1009070000358803a00700500705403d10404058481c0668200315940307840c1e030000300e450420a070f440081d00c1e1000074010280382d0201400181c1e00d49942c038 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 431329964 1250 431328714 431328727
    0xc0a02150a020a030b030102130b0714100f0608030309101d0f060417070809010518060721030c050f031003082106121504060209040603080913020f041505090402 71
    0x240340e00180960f54032074034180b1010b492542418200e110310002030046400303018040c04411015002811030b207009114130354100d11901a00c9003030014406058017165980c0c1504d010342d08040c003a1600400b1000081c5043d8030f05080c00345c1d1640c00300000e01030404da031501550395840450913807140030b640a070211918000600b03503250f076a040a0b9810f440b01c68881d900d03d4514030100c000c6410059020b088503003048100801900c154202d01d041d21256100d809442110761200d40241c9150b500450501c10100840c240080309091046900c0003007504124405200e1078200c0101c4200524280ca0f00355240d9400006080410301e58200070201000001d00940b0b0301016192240b207001054002c1c0040e031201410481d0154800040f0007113500429860301002d114456100c0d0b1080c01101d0140c80c0c04040d600284c2181c1c866002154184400704049040e824040e0717008001c00c036a800c045140c4041a041d01ca402e015034416112000003000882c41e81d84d204006a4001100c054015529040b = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 431331214 1250 431329964 431329981
    0x810020c1510170106140a05060d02180405040b1005010e180c0403020d1b06031b051605060702030a0201050a0504110907091d04060e07181508071d0f010e0c0a0215 72
    0x11506c1058645d410b5401d03d080b00d1314001810800311000201214075240c1c40344103013000b070b4010f1400400d9600005410382025100c6003c3d5502c030700d10640034000545032184543c05402029004541001000c0703c40d1b28060315680e0550089640014003031499554542608000e481103070402908010040002420415512120800b1900c400c24101c04c40f9203800080381160030011029240c04842c0914100e8240158010a03001e241d000001c428180315403038103454040241c4040300181d0000640705096a0b0a10071070750004610700c000d010508080d100d12030400c0c1d0304505240700b100c0200104101c10f0090100c98000c10018138038014150210200e003c1d0540215020345810741030004600c7c882c070002c14001c06603042c0f1003c130100203a0051100009001d03400d501d51031009022004160007508000c810001e107116002c510600c0c0030365419000c0b03c04003600240380400800014081484a85846544256140d80840c0c442d1103d52080313182540d41c80d51101c401401c07405101626 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 431332464 1250 431331214 431331221
    0xd021506041503080a050903070e13110301020918100608040c1502030c07080703113307060e0a2f1009121a09030a080129040f0810020c15101701 64
    0x44210191542030b80c3c1c85400c001c804ac011501250b4513191850001d000070703448440b9a28040c40580010b0070103180c000400c8080c2080304000d01880310540401c0310640d80f20ba082805010145041c403e241899a06c4140d461854019106101c04400e4080646482042510511000101240d25090741c5a203c152140070901043d60142c0d41c0b81c030000000c1c1040d019401007517210000070207000308600070b07808091081d00840c0d080030004000030b00101c0c40d00d0141d43d04210056025250090171468240300c0d240940c1c5154040b14a40c1914000c400000b9078040704004080c2d41c80d41c407160002e9070469800616800005944c240710040c20207100b01101d0342c46c140c00138003050b40c2c0151134144001e5928060728030481c00044d407900c010700c003040038106040084030290b01c14006114000081b4a07858000c1d800c420845030032010100103d8804125000c5500b084c04011841d010010600035150702540401c20441940314005c94044e0300400444401880c4103034400030141d01c007003107580c042d = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 431333714 1250 431332464 431332477
    0x905120f040608060414060d02120f1513030c030e040902120a032019050f010203090f012004050904051608030a0206060405060607030c210903050d021506041503080a05 74
    0x34190400050b40c1d030405d80715412031210100c030502050f0380c498041001065035144100d1308005c10b030181d010038072001c004003461864070801400500952126a6441500045c5141000803d140740c0030701090b004074240c072110390540b5104140c00d07490f8000c50b01600e82d000d8000d40013103c1e2071140e00d421101080313601341144241c2c1d0f01040382100150000c807078880c1107000328282d0001c507081d25122080101c820320f05031240054816a484038088182280c00450b50007a180d007208910342a00442071003840070450703603c0c02844000b0031100102c000c074041e0b4000c80b4001c0a41da404981441010401c071843c0180580d414801252904615500d0740c100b11204001b40c4a0300d0007255440c9424040e180c8901c00140401e03041411988049030346440258060f1542580e002450314010314080040309140040d0301c40c0a01030303155181052614009001c10011904411483e0b0441c1510441003074001000301d501150071601015101d48034603030307680010100c400002d4002d0b80c407600003028041 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 431334964 1250 431333714 431333717
    0x1116030818010908030315030f07030302010b0a06110c100c05060a3905031906060504180e07050f03120418140103030c15110a08100b0408030d0905120f0406 69
    0x800c001e080c0041d200d500460040c3c012a41061000815101c0c1032480f26241403001002c6482c2c850401700201e090148940003a80140d454060a10031807c005080c04003c15503450801c02c1d000441002070340720388022120314170030044054440450b038400d12407203891581010940780c560501a50b140000d054400b500c900700c41c04411452154001c00229141c80c0c140220544100c007068202110f5540c001801e43d48880000349228045503658490f0f007024050707540307d140c0c0d03441c10100a01841c8050410b0b0080b13543c2802d012038a84131005c102842219016617140340c010641000103810010aa052120300401c042000940080016032007256986114420040245a07080442a07001c090002401007010b03422408000384010502c01c0003011009000510b034902406c8215240c2d005106400008030104107002d85100786421000c000c1040302110b5161031301e00381c03078107840b40245550b0f421080e0b96031140206118040c0800d41510890120003640e441840c2d0110b46150001c0c0504070 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 431336214 1250 431334964 431334997
    0x103120509100e040e0f150c0c1501081b031c031e0203041a090d05030a0209040e030702040e07120b0c130b0c011815050727062d11160308 61
    0x500d0040411010f460900302030251049003900c80640d030307c64902405100074400c0030802403001c01d1046c4252140a59550740380c0b08994900701d040d40c40e05280140d6400d0303281c0400e1860380a980c0002d050940580d084650300c0c8500c0c01183c0070f6000f003a00c2c95010a080e6080340351440141402e500071482540309000000d04072541c4503201c2402c4000304c4031100c880c3d2220b02242d480601070005141e2103240c0040152520000c000843d098441301024040300b41d00104032041146014090000d5038020382008100b05841e2003404010f41c841c40c171000e0103800201002c9042c454403002124140d400c0258081d03000b962700c0e800c42c2c0c81c6030700c410205140ca510307049109050f40903100813500016000380c0e50702090350f041c0840000804000d080703036051141e10081c1041d0141074114203014086044d00710001c9610b0b00001400f8809002a1002c5110b840740803003004081000c01d002100c1e02a1402201440e41403244a103040d201044c2d00c0c4004180e40800000c2090140c02404400010f070301d000c = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 431337464 1250 431336214 431336231
    0x30b0a080c01140f040513060902161505060906060a020f0a05060f010603020a020c151e03150312030403030e0712050102030430030e03070204020c030a02120c060103120509100e04 79
    0x4040780c0c0211380340310342280380401003080503140c00c000007540e0400c04c2c800001c16a40e1015500120b03400165030502c07070160000b00c042070012115070700b20703132449502c400e2000c1c0c0b410400140383c04100074640e511802001c02d6a40c102c034402c00c0304040300504071040310b0a120300c41c03c2c119980d0f20100c0b003081c40142024000f0503424800d00035111341180640040c10303042c02c020200b09441c4044c1803414400c810a0182900e020343c400c03500380c03495155498843c0e403410469086942c140b10000b40c0741c000c2c0e000103400000002c0c00c4049a9002d501480c00240c4012440704090a02c103044d8460b10010701408018410300c0419401140240d10030020310001c1c80c1d03a5800030300d543d00440511001c4440c48100425007a020b0b8000e075100c048114240d034580f00031030340098200d8000074036030303606a80041010301260346c0420070005111a0845030380d0030185c41440382030b0b42e000c0502000b8807168488487c0402c0d10f00810a90340c0340b210081101300205c1c090f100042900e140c04030304512460070004035 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 431338714 1250 431337464 431337497
    0xf20061503070f14040f0f0b03070603090b04021201020c0304171506030a02090910020a090e01060c0c1208070f110907080106020a0305090f100f030b190312030b0a080c01 75
    0xb04040707441c01c00752440d40516120780303184c0ba485000380380b07030b002501c65500c1030340b942040c032039811100f80e540000240002d800003818503002c06a0408018180360403210f0f008076004021080d809981210010141341880307051602901900d44d00c0d08041c0300200780852060003c0781a148020f40c001e048800760811031903010031903c01030300c025405401483d2240302505161380e00340d41c05100031040350543c0c82c1100c1c2040480e0f1022040000140b0080c0040c030525040c10545130041c2001d14150742c821078a07899400d0012683d00c11281c0442900a0340c0080145640c01d17685a26000030325502e40100718101090140c0f0704980b118412182100040e1800380100442410303948140c0c0100740d10a21581c0c182c0303407070740038000241d44901440705e07905290751880c0c0d01c80d0101c80640c0c1c0344244075103031010140c2514111800c0c1c0d4421120845040b440400c0b2285a00460380c018500e404c41d4448490298020402800417a8010310300070401702d0b0a20340024000e036060320a03601c034861082080c00 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 431339964 1250 431338714 431338723
    0x9080703230909040b06030a0209011401090806060f0111070506030a0608060601031109121230040302122203050c1201111815070c0e0106050a020705010f20061503 72
    0x2c0b07a684100140702040204d0803004034181d1015010b01110100d04541d000101c0c0440c0981c40240c50030380b02c2c03035000425644801800020304140004200504142d03002406c23000004c04502c1c10045c000200007044141002284024039029007025600d09120840a000e0401806a42003510070f403004500c0c154420312904044075107194140d418200908200b040c2d01200700f484088901c2002410703a00503a04100601641117041d80e0030705d105101c845200440390102e1413103d43e0039510380800010030703004107080254030340c4244081d6813420342c0221030b0300c3c3d180300058100a8251546010041080004469060407400c4810564496442103034a090307901000c06540380080510211110390078003488201001d06c0104a881c0948092a02e080748d90803415095030301032000841086902040c2104502620113480c059140c46100c52000c0d59400b1644600c5041010007003811824904c0f40d024092880a80711840941f0094040290344e500707825100150a038030f4203064000c0303a140009 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 431341214 1250 431339964 431339977
    0x804030f0e0a0e0a020d1a01030b0a18020304030306150221070f0807051f051b0307021b0406080d02070315090218090c0904030c11060f1c0908070323 66
    0x104507001d42c5052100c007030083c00c03010748400a000e4003032200080317501c3c0394010b00c0524503400c4855002c0f108040c00060036100c81c05102c6003d1103400f1820700241410840703810380c03050900c802580e261181c0c9000c500500190b808003000d9403407151043c5070f0070760202c0c8102d0b089404154000140002c0788226000c1d11441c24014041c0641c5002003000508003409025a00d02880c180c1d0000c0002d00b034140d9004854001006440782d845042090415210070100592540343d48103500718174003050040d59400980103801c03c820110424190160383c0c94002c1d001902d042015a9145030781400080c1d80e034012808110784020025040c45040480c5100d00107001e42c00424010115240190300c000700c010182824032540500c59120f40d4580340d003000070340980e1003582c404100c2d51041c140079500c0903c10070030703900c540002c100310407000380b00134259668103110b62061540c1c0080100c00000810702c0344070080058501007454824950880c00710b550b152045200040b0030303000300002ea105c501c10b45 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 431342464 1250 431341214 431341219
    0x5010c0302130918060501030b090f060112080c0a12050c060a0902030a0b130b040809030c03012906090409030206010503100b0303041406093a0b0606030619060804030f0e 75
    0x400007040a894103400079900140103ca13100c2100380551a61400c0d51000d070000c1c2c42206055080c030265800800c54031410225440233032060b54108080140030f4200040c000e405148042084d0818442c2402111501035210464182c02c80c400c4801030841d810060106903103000e804001810900107010b58043e091303008020f0f1030590a16076440e03410602c0504404412040615403c0c00a80c640710180d024a01682040d40c07a19600d0081510300a10070036034a00990500703240c1e01130101d10b44270000c03981c1c81d1401c00d40740007403401c40071410b40d00500e4080765220341890300400500da0003151a60684400364161240c2040140c070600c191a40780d9190f130f4255104100070003031103c08101405205038000e0405107490003840000d14400d920040c412440f8203995003100d45040452049501110032040d40c0e555011580c0b1400c0b40100c1c01030003140070310400000030b800c40d034a194446d010082400000a44c4540702c4000030004c000485045000c0f845c655107814580c0d0082c9102c00006000 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 431343714 1250 431342464 431342497
    0x31f0e1f020703050f27010201150e0601020102070b040b0a0e0a0f030e010309060c0e04180c0b0903031308060108070b0c19060213060324050904110102071a030405010c0302 76
    0x240030818009600000c4154108130042c0301d141d0b00f4500d80340c0244400d1701802c0100f290495801e450840c0b2901c01e4240301d0543e85488401c0f110114020040030480e120f04884c040ca980c1ca8100603406440f9407140207000c60300fa44104000c0250503140a40141c0b50400300304030140c3e914100d1941d84c49427601c054500c1610748117000010b403041e0f105800c9000d061402080d4480180ea4040603106071803405000b24400c00200065401c1600c0317101c10762031100310f80710f40080080c0c4800d82e203a901070181c54401140044c008420303813010002c551200000301c103910186590b0b0070401c3d4880f0428041e038a224000d2420001e0b401002c00103403041c1120315000741a0980b1440c240c00902201c40c0e4080b80d040b9020700040c02c1612100c83c80c2001848a40c40c003207200071107079940d0700e0451014001c1d0540101d0140e8144041c0d103490030b8083c0d00603803010880e441c011150300181e2800c041035000300c40410b1001c08002d9246015809540500c0c4518000c4c4807800400e41c0c15816030195014030410201c1 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 431344964 1250 431343714 431343763
    0x5130b1c0e06220c260c010c0206090402070b0103080721080609090c0909070e060307030b070f030f02041d060301140c0a030219030507090609030209060d11031f0e 72
    0x1038150342d022441e00c0800c8041041c1c070ba9a03006801084d40e200d000507010042c5a0082c0c807a011200c01c801040303201c081d00c15220580c1c0040d00040041c1c2d00a8010f20b000f050500840e1100d41c1100c411035000342c00c2048035030352481c101e0119400f10004560f405151000041900c0706081c00c0c12030f42005413618001603540406100706507000800d0700003240720b65010b0048079200e03a08142c0c0500d0b500c0c800741488600701051004080c0303016101c00d0099100c4130040010440c1c589856801005900d40b1403445900701e42c00314041c0420800804115200080000e480f20841e40294800e02261b2506c0c046660b03804c0405003259000d41842a442040000089002e03464100074421001a424010b0908151240385000c0c4400d00366107601107075442e001d10071419008550440100308514100f1655401d41c0d02107501c1103c081c040034006d000215028003040400244090704140c0a8115907200b03440c0b06000c1039000140781c010408510305038400040369808101d84c6100342540d03c01e10020340c0c = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 431346214 1250 431344964 431344981
    0x712020a020a02041b090e0f04030e190f03020f0d15180c030c05091b1c0e15010302120d23040f0308030115080105010f030c05130b1c0e06 61
    0x18416264030007140200340304840140e0b184c1c41641c0b003c10541d82e070010070741d6003041c000c2d0005045400c02d0400030400790130081840105c1140d030354050383c10300c0c4c103100620130031004c680c0c641d8414850302d400d1104c040c40030600c40c8007400c0407000c480c021148030380c0c3c84010b00f09019a140c0e5030310014260300d200046030607031200d042c0c00280e101044001e9400c26901e650721012115003203a0421510441c6d004010000d07464800f20685d0010b0801c0114210800c1c500001891031050811070f0a800c1c0b0b0800610740d20010342d50040d101c94280790103450501010030450b852442c1c1c2400124481ca05a01206403050710000d010680d80c080341d11a80701000304076500c10030ba617105503005000c0700c00401002c202c90401c2035244009500c5894100d880c0d5042002a541d01008010340c2002c00004600400c00c50303034020b1100d00d911165003000940c018000004407140e10a050001c0d0640b0515400060403040a10007488a00c0c800842c0b000e02081d00106030044da003140b03403804155807180d4042941030 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 431347464 1250 431346214 431346217
    0xa0e01180f0f021c050102070c09050c220b04060e01030c03150b1810090801050c0a0e12010608070f08010b1c020120060c0315010f0f11151303090806071202 69
    0xa80c0000c4c40303c0c0300c04651001404440000b000110b4543c1d4020030300d40108500d40c0186805403d5100c0103100514000b10740f00e849014ad0280c11010138580800154044541c01921019002c00180d8541d035544410300505081071503209240002d190803030920303216110b0b20511008441078604010600d1524a01c0c1d100d94001031382001c450345692540000f65618445940307110f1000d51101c107100b5160542c02030031500b00410003101d188082100620290307210000240c80e4504032a4190900e5142c4d400c80d0041c0300542011007a48071b50136002c6094800c1071303c02022220004020711060301068203100c4240705040304074464134049894400150300907220304c1e4160610200021210402010309850a01c041d00c112820031000824059024824041500000801e00304680c0c1d00400f00310003440012080491010012200101c2c80383c5142030048402d40caa201105800508000c0c80e0300c1c450007252441180420400e1100091034200440c01e14400c0d17200d5111008107681021101e0080d = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 431348714 1250 431347464 431347493
    0x60321031501090503011416180b07150509160602010204030b0a050705120408040f0815010504020a09030f23060112060c11010513230a060906140a0e01180f 69
    0x43c0300542d00040382c00d8a0074822492840441b5450210600708210340c40d19121400008404112210304031580002c5d203d5038810882d08400c0002c0c0c0e0780c44c05810510890030415a10745200e41c244014001c85910010f070402c1c12005082420080c03c0c0c0d1000160700f01c1c82140300c000c200c2109480000c10342d0b116540242e0740300e01c0c241000383c604002004603030b0141c42c08940c01c0301c405d000404c05100d44440540d8071030107806c2110081c020b80000d8145280c0c40a014401c1a103c0e94000660f494880d10a501070801154024010113134926203140403154007541816081d070390a650080f400c612400052454100c402500f078a080c428480e840301e10140500380e501c4020f000300340140d800041c800b442014860010050b0003400c50340945040300140000c130003800e1815400d000c5840c4030001c00704c0c5801d8260f5001c1c100180b488090f140400140c01419900200c00541d6001c01c00e0a2000b600414071481c0d1080080140d0f1440a07561450160b2070040640340503144101c000010306002c806c03980 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 431349964 1250 431348714 431348717
    0xc04051e040204051f0b130522050c0409110903061312180e07030e0c01021605040b04090606180e19080c010f2d0b060906070c030515060321031501 65
    0x118061810308400300c4086d0780300301c018100c0007c00d00f907107c1a00720000041c1000b01c0710317134400e51650f00d4500a002c1c1c00300c005010ba665184045032042c454501100d0080030181c60034000054800c805200a80007041c080b0700a004500c00207141c008441000c001160748034095030300203600c00c607080b28440c1a01c000e60500718800307803020624006201c5000c0c0f090101c1d0350007040814144a407141800100d030500c40c15580070070041c036035840d907811490b4103881091301d000034000f4203a0700040c0546600507010780310f01c0c9000c4020136800248500b41c00e104031600402e014000880300f45030340d00c010500300c15503140c0690100c4400100700f0002048030030503610010640a1142c5112000c6880e0f110595a03180c11b007050080280c0c1c00003804160082081404008040400002c05c3c0c580c8104100248102000100102040700d0f2400380340c080c54010040307036821815284444003078001a920344e03119200c2c042c205100d0044400201d03100c00000d4030079038155251084004903090202200a0 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 431351214 1250 431349964 431349991
    0x11030c0403231516090b0d0b0102010b040903080417130308030705070203120408100536030d0605040f05070c060e0f060c120f070507020d0201051b0c04051e04020405 73
    0x405202c410040000c038500300c40242d00050811805844184155420b810103008500108101c070011550a81d41e54400c00342000c02d80e035028400407401050320760581540149801500c02c00c2c0f641c840c0405209511855055030002482000d0007281c2c050304031655904010071000344002440c03640074541006160400a00f0b1250b55400a41088101001c254032210042000c0040c00010840802d0342e1005190801090801054014a0840f00d103980030b044c1d19100c1840010300c10001c0d5040c0d024071810b0569444a181d001c000002c0c01140c45851700c05c130300b08543c290307140381540304079070186459482d2500200d803039a070341c1c401501036420342407642c0c018440e641240050601005104000240340740340c7e1856410f0501c2d48103003000d4400707003c100c00d039810018503641002c200c0783c115030111907203414180da078401258640304000040c549103d162500c0381e400d510028400d00380d40c070115000d106560b0b4240542d0881c90308042d02c4e000030b00072040840d000d4140f030341c486500072641d9208030 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 431352464 1250 431351214 431351273
    0x1c0c151a030105130b0606040303021e031b03090411030708270307150f0513150f06060f0e100e0d050307060905240f0c0319060f050411030c0403 64
    0x1c2c1c21500e0031200205481001d101e4007040245100505910140c00c42e4200c1c18141540c8000b0754030140d0492041627081810710803201da42c810016103500c0d0074214004921103440d00440c0340c40f40c0200e045540220b0070400460018500b02007583c0c4100e05540e20159107541d61260b40e001c45819402e05214220341c41802d004080b01131000702402ea0160101c41040781602e40000d003120350380401044150301e000b060040d68802c201031003e0b45034004801e0560700f108114001c004211140c1d280302c55a140008c0090ba040d0001102c495003400b03603d41041d007040f09000c1c000040d45034a40d2400060000d200006d60b858120640c0170180d02803011a410051203a46100449000c01c0058507964828a404820040304107070f03410100400190040360350a21000317401c2c0281c0c010f421520348000100000320600c001c201e1803c01c000201c0b40a224160740d82d544100010000d000d681d010728100300d1f405442c01c2403101101c3c024a100c01e410b80c0380034a0343e140c90b88140c2203812895502800c0d00c0c1c04 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 431353714 1250 431352464 431352469
    0x31106010b0702090906010614071a100303081509130c12080c0609030f03060f0d0c0b0d0b150f0f0d050108030d0606170a0b010903060603051c0c151a 66
    0x20940a03185800d401960b4a02d01d0040140307010000b410710040d42d03c000014050a40d00450800090740c8e140032035515140030f0b2404007040850004242c0d100c0040c0b20404c0444c1000b03c1600f001c0300d000b9110a81c06031111800c16100003443d010040e040240140032a01544810039251555030185c420761810316226030742c900001d0b52501d420764000b503012070890303600300040c4007007900080100019071803c0d42012003403120703000041a03103204400b0032518040707586a0003c2c0c0031106500204440f0700c19160310f01e080ca940c00c00d000d040c2d8000d103071400c00c035001c1c01c018031481164030541d40c8031410940c5105410302c056010310345104030808184406080400b850040034040e00040003c0e6840f0f0a0f500410011281503501c50b00401c044006244055903031401d01d036410800c40080070444000307860041c1c8006c220382c2d0000b8401450000000140140400e0082e1122000f1040a0a1001e0701c1e42c1102c11440080c005011050058210741d514460b580c0840c41c2e41014404070705190628100 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 431354964 1250 431353714 431353723
    0x2040305010203090a03170103110118030b16090501020f0604120225150302030606090d03020f1f0501050105040807140301110a0f03060504020c0a0b13021f020d0206220311 76
    0x113020a96900000034142056080000300c0083c10b101c00703004070598599281d0798000312001e03800304d06200a06401c10500b5011a401e800516040119402c1c1c40c245180004443c1002c03005020008441c101d000c9410361000c100c0d106002c900b0002425180c442e0385810494003140c1580300309510400d0300303640480703010700c40b43c403812035054400c00380040c034204090310300c98802c03030143d0109441001000000e81c2e450040d103a00074400d8508135000420352500ba85000c904801e02d0314184a614800d0b885503032600c21010f000c1c6011324080c8035a99803040159001e004074010344540307030009001480381100200c0c4070741403d0720040010031251000c0a2076074156100512441c0060120840c3e078407040d801d402007100400e010b031000c40c58028440c8001c4e8a401d441c06004041d0040306000c1112100181415803078103030000c0c481035000c200a03065416420144980e04098050b640100020f03a001251591040d400d103c012141c1d60004000b011200b400340f4400c07410302c00e0842c403013a1505001c00 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 431356214 1250 431354964 431354971
    0x6120c120c120a0c08190618020d060b1603050c1606030212090703080912010906110307020f030a0206510409050d21022a01050603150a02040305010203 67
    0x4440da28140440740d02d189080c0100301c010320508044000645690084d00b03207610200e10103401103c0000281000050101d991102812007410080d014102d2210b0b0300a24180520700801c010341c5654919410081c010400018400000f180400f004a03001d07c004122100300b41e02660070500c0040801c01d0501525002640000c1d80400c4c442d14103000025610f401c001a40c00420080d4550380e50320343c0d148641c500490041c601050901420b0000350040c10401c1e07400b4506012040800d10a00140d40040721007000500ca45013040083c0d420100884d0407225807940a4a907581d0b450443c1c03150000d0415420749003e00150742500c140c0082040759040b01480d0701e00306a1001803a908001808051710742601c514580030400300011000a1500251542401c2610013000e44076a0f20a066052400100b060381c00041d800c0003800c405000b1128803198032041616625170556414200c440c00c2f6091905940905001c40c2090380e03101c1c02ca03622502d008400340c5000d440703507285804c1e6001903 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 431357464 1250 431356214 431356231
    0x10203040b100e0405120f0408030f0c0118151e050a0c091a041e080a0803091908070b0402191409070f090b0f0f03070c020a0b0906120c12 61
    0x1402602918400e110b4010065a440360026083c01e40341c20380c40784419000c2c40820300340011003800703a400c11700c252002000d0314002c0d00d496a6043c90a0500d590007221840740e15442d04070044004800700c0f0000009035007083c564205101010400320003850b1a44210403000c500c02081440c510071402602e1003900d240c0c0010907001003140001c0c2c07440304181c105109010007241446000c08102081d50101c8001040c12144818102e2036180b0710401500b00b904540194180c01c4144140200114041c0c00c070001129110b10140758000003a80410701e0051452004004001c0800d010b100c1c111b410600041051003036110181d50b044400c4130f16400b00c5039403200c840340000f041c60b002101e01e60028580c10f001e00c490200c200c0085c4031600b68020700003104400720300085c0e030909100a0702d02e0b013400301c544560341742404100500801c10310f0004074844d42c1081004540e106000054030070700720010303010f50709041c040c031040e48903030764002c041042a90040c0310749100c801500070301c0c1c0e0054001 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 431358714 1250 431357464 431357483
    0xf020d050106180f050102030906070f1403120c03010302011d2b0308010909050a02120a0609080903010c1706011d060706021207020c1f051b0619050402030a02040b1201020304 77
    0x1210010b401c00e0f502c5600c050030300c2c43c0d2001c04016a0b600070040b180e01c8502114100d40c3d03400e203480c15400b00780c06600003401d0f00c1208808030341501d0001006003074207a00c0108000243e076401500c44c00c10f200c01d010080c006034041c5c1030401c40c540c01c0c8400001e0301100401203c1c0400e540c614100300c10304501ca440509039030794170460043c99085a0000d001d00640002401300f0b0301d03a900d40f030380d85103090030f03000703004900108031901044d1050002101c40c40d0b0102c802d100800c0c442c140078034a40c0100242d40e109501c1e014111000074081d000c004010340e40c81000c03e00396030b50300c801526525245020400c01600340422000c1c95543d0a00400c1e41e544600350058882022451000c8840b10060020041d9844541040d409680f007406008107003070f1214409181884402045a0310b02501e880c422152190f807031031114220001c50f0651144602da05d401c0345543e01ca2202c0c80980c0c0c400c4d1400307901600000c003d00c005d81000e0700030b543c00c080f02a00e500350480941c00e101d03007260300807101502c0800d0b4 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 431359964 1250 431358714 431358737
    0x20a0201051810200102090604290d1d0607120b06070c030c031109010b032202060a0e122d0c09070f1e0203190e030d020a120f080a0f020d050106 64
    0x120030a0013140040d0a000031400c1c0541d410104480384902d004003c2c040d544007601ca280a820b141e01e001020402d14850754450002a16a10140c0702d81498441760903072071054185008400102c441c8a5480313a5030b210200340121030b8240040064981494001c00300300702040204254102c1c1d900218407403901110000d00e0f50a040c4540e03246544064460b084a10040000082803019603400004040ca11165880b59940c01c007888400100d000f50048408505088200d4209500c0c1c01255003c0e074035501030034211510503849440f0601e0024600c2034003045810880114010f82c9500d00d5443c08403240204010001083c0304000c5980200080c0d108040114103507011881d00090309000007070b441004840c813000783d00ca000700300f0180c811400c2414110400c40c400d08010403a00030280236140320402d5204000d4031012140402d41c0e483e4019100041c3c094424241015642d4580d603420340152501c81c50f0001818003110807101e8a6000d20610382691494400c01e40284265140c0452111 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 431361214 1250 431359964 431359997
    0x612010e071803060e0304030f110a052b02030f07180b0303090907080a1b031a0904110603191d0c03010e06061c05010c0804031806020a0201051810 65
    0x1240105071070204041c400b050990100303103a0280003901d03400b01020805ea6500d014191550050b68070280800c88400716040603c028011115080c2205a4006006580343c178140138050b40c4103007402803c4a82c1d1007214614400a120700483c1070b10007001c2d030385140d1181000e00c2c42c02c40281c002c110050410080d40d100c101540c0b0801000c4074058010b90b080c00c0481c2c0004d0302c00c0e1001803029040c8005c20000441c950324940c494a00c0000142c0300003449031403403078010000d104c007400c1001d031442c0c41d2000c48190714068800f140b007280c0c003044400a0040d11014443d0a40018200c040507080c1910010840380144c02200f0500c0480b0b805e4911184100484910b0805508a4a03020741d1501400c1c1d144030101164090b48180e0907500b2211800e440c2c3c1160484003100d000242c00341d403900c0294660140e00569181c010350180c1c2e14144440d07500c0000a80c1e0b03000a1051102607801811244010b50185010707010703500d010491001c02c0391004000c502c004100180311000186a903010b141b485 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 431362464 1250 431361214 431361239
    0x11709030a020706090e0106050c010e01060303050310060e130914010e0606090a021e0f091302121605030f0403050403050105070c02031b0a0308090f0a031410020f070f020f061201 79
    0x20b00051a01c0803003281b0b018030640c407451060054604000300019208400b50094101b0142d5092200081110bd980e038200100107803c10365129031100807403003000031a00d12524050031030f800c0040048100e41c0090b099000181078405049030039010905110311200001c2c411007018a028070f0180205140000800409840083c04030102c0c9205001c9207110542e184003404000f60401c00c4140c0e40c0d038096191a82c58066164030f20b034080c05a540b2402c0c205065000b0b45414043c82402065a4468140c1d0f110040010484440051824400180b50380109417030160094000c0c24042d140035242c2c0c58031820f40390111603020225803038401c6402103080801604444803501c003440008a0700801c00035158190a1001500444011030300880d00d40d01c1e086400214031008124840090344c0b17150440081200201c004194014801c103000340442c0380c02151b41c04251064903524289441d81c0d085141c8200b408241e8020091002007900e41e11000d0080000e54410000f800c2a50314000380011034 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 431363714 1250 431362464 431362469
    0x138060c1f05161e0804080d0f0b0907090303080f070c0c0b0309100e1b0a0b04170c01080103110904060608010e010f050115090b0304030e03061503010c0f1409011709030a0207 77
    0x4201190082a104000b03a581303100d080615450520308503255410011014043c003d02840100d00d002c051034509005035018074940741c01924400309039504c0c000c098500301c0322840080c0214800304006091484440c2c42c2c154044100c3c1030103104028540c464161001054000c054841000400e2010320401000009102c0382c40c040140704c05501c094405451b070842d01042c03003ca82110352050904e54550450078058500c0c12512a259951945101d155407d0201d450410b8006d19114500a51041a1060603650849036468050007041d041c0421100024001d580440e500e200204103070030280207144400d045a000440c0650543c0310000031544103900c03090f15286803c688000542c2c0248002c011036410001040d1a41d40e94101030307500703880d00c0c203002d98140507003c1002043c000c900d40310801800203070000c1221181b10901603c0c00704401c0402004121110b040d40c1c040210f160040c10852700616114110b1081c1008140700c082c01680c4100d901d80010404c2e0308803c0e0b041121400 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 431364964 1250 431363714 431363717
    0x20720040b0a080718290114070c050d021201060b0a110105040f060203061903080703110c0904020f010e061309050603030403030509100306080f0138060c1f0516 71
    0xb46500c0c1c840203c0d640c0780300388500740c11900035004010100c2e46940c441030b0051115100d0280070900c0141411000c1d45003c0f007140420341405d903e0b031a903040701c0f095a0029901005542d40c040c2413604000e01001c03001c070201c1c0d00c4910058a000c08075000c1c024080201111400c0c40d44415100350090a40e450601410b071141c0e00d00070030400451041581d881e042504044c005940c0c0c0c0719803010802d80f981d864070004050f242c0c082c00100f0056604001e00703003103011b9603404402c9400c941e0019160150000f006512152440100300940b0b0148000008400b05060489450810030081080d1b5008100142911081002d0400c01425503018403544414214061482c0600b03554000e010783c0981c1c9080d50091800e001c0000c480350003540158050440c81c000c9540c00e204403000203000e030200030280f40110701d24025403011600f19054890315003100c5200300300000e084000740036950b00400d85010f8140703d100002c0300e9a80c96000c81d030390fa086401320085864a058480f00103084101c518050 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 431366214 1250 431364964 431364979
    0x207050606011202160b13080f0408100506012f011812020105090d05031f08011505090c04050d051c0c03020613030909050402040905010203070302090a12080a0f03020720040b 77
    0x1d0171071412001407041c0e00010a6900c0d40341c43c0304070040701e108000010140000020201004000340010307000b01c0d4000c1c012142c03174401c0042d0380c0302a140301ba0340c078a022034607820395a0304403000401c0c50307214441100418030540c3c0c1070034030b0907081d904100317804013001c0c4e10b4500c0e41d818491002003058610b500390009028a04020304195960f0704110302c502c0c10800d000c03021035080d000303a110702c04140742011403080745242c482c00400d000301740201d030347c0b0740342c2540b140005968203082404c2e82c42404241031060401e8948000e00c208003825500842d403500410050340e0f501000b2101c0e030b0200403001d13607070460603020781c0c50040d20b0950301402050106aa40d003622000a60020109090750081c0001040c0d60321141b0214010b0103c8c071700001d0003540044100080d00707030b055000c0c048655003111083d0103581e81e403076100070b12a0b2046010300070b81e400300700005505005201c00c0805034181c0ca030041c41c1100a8544005208a60480c151b000c000744c112942546854082d01181041c121000c8 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 431367464 1250 431366214 431366227
    0x504060305060c0a02071203030203060906040b031011090d0302071a09030d05091309081812060f04140604030305250c02011b06090b010623030114130207050606011202 74
    0x1da58440008141c032400030f10025801d83c1c02d0b4428003000740100310102c07450000c0010f600d00600030f074000700c400074040e010300400a800c40c58030740107007056448080c0160403070b01ca80d008036030044c0c24800410b403c00c000411010040c1d40b83c42c0c4c076000185019601600e051403c1c061610b21803141c00420b00c60545050280030700c0c0d03503000300e0201c440c0070342c13030070620b0765040042c000c82c1a43c00c0e0640a50982c40c03805060741d09004210b0000d02032180c0c5000c4505502c01001c0c1045001c03030802405640952024000451103404854800d41041c05a000c4800342c02c1c07003842240c900601207800701c002a48600900240311440e0840c1c010400e420000040803440b1210001d00401900501074100945101401000085520545c458a820650030302809405042c102280c0b9021b00c110400210f0380b1103040d041d8510103007c0c929103030b002264a4550b0f4601009000b900c3e552815883c0d115283c00c04100407414140b0040c035105d4461400fa040516143d8009800d07000d900f10152507403401046807 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 431368714 1250 431367464 431367473
    0x1b0102060f012114010f09030e0102210d020705100902030d0305060d0210140406170c030c1b0114150f03030405131a15042310050a1e0f0905040603 65
    0x7070449080c1580f80a0815210908004200c414048015411540780c10700e217488070f050340d4003c442054000e07180c82201ea00580012a501c1c03103000d2400501c0e2066402c1e54602040c4080204104c0e1910f0001505062158a07020b003032075032246000c4100c90f40c4181c85011403d050018034a111150706040007903190070704c00320b80303040700e0200002d00c100b640b03890031000d85000b68401001c920240e40c415031070b03a48825024006041c0f64213103450842c1c0540000c1c2c130101c2c440d030849202d520070180a5042003130314100b55a009010340c0d200d04e00355407074a0120b40d081f00c0c000103003407150903d14840c94400040b40e0a0210048503403003039a0003600b04000511198542d0b0203840300003001c00100041d500c9010361041c407240c01e0403c001c0c0d44103159122810450700840080c00594400030342d1000c0240e00c000768560010a0540859017155000300c040504501420203803400f007000342400700211660034110700c01c0b0021a00e8020105003804580d9040d6a802903240f000303440e0946080001e01d042d070f110b = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 431369964 1250 431368714 431368739
    0x914090403050c151302010201050903090a0308070c08060c03041b060e0d210c050d030207034103011d0c030a090309030b01090614010c2409051b0102060f01 69
    0x400303000c1c024000f4481c00d000c0000c00c0700781e204162038600054241001d83c0703840314554003540c00303034015820100800c0c00b020380031040350030a002c010102c8440b1440c580c1d030380d412904008810b58050303000c1680059180002e1002520410120310021ba481c541854249a400400c400e4005400c030304900c1404020f41001c000c18110608540c0d012380c00706940380c42e02085c010020f41c40c0b10071a1170041c80d0000c6800c0503440380d24a10440c1a5194440c040350210228002c20380e020340003c401d2014204444604c00704804120441891100c840e4801584400b03400c17130500180d54800c4002004103d0580401e00c16103941e0040d215140b1036080c0000380345250300001d000300b088280e403840701d8000c05000ea40c1b404001c6038001000c0c103a03986d45446400041a40b8401d00414100b6015041ca041d072042881c02e101d10790141d00c025103a400c021900d0103101034000c4070f0321403035900c1070450041442004104c048040d2490030300c81841c0c045000904007000039201d021054140740040c01b0740143d090 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 431371214 1250 431369964 431369971
    0xb0a0b0703140c01020c0a0f02030d0c050c041109100c0308100f03080d02040302130606090501051603030c1103070b04050c0108010302030d12230618090c0f030f031306091409 77
    0x103202d030707803a0014044a107009119080c1c02140718454a0f08120406c40d44880d0142d03018000c805a8400301405a415a54518441c00003480d0344c01081c01c50219242c19840007407181076a441c0700d402c0084e440041340400c0b00d03015507000480c0e1070004400405600c40c4069900403115908022054980708a000401704107000c010452400810075a4101040e070741a10011a001841c0c540c407080301c04415001807140b8098000020710000000c0f407594082e4048035503001c490a041000d02d102501c084005006080c8910b0030000c50034071441c0035134010800303460140d00403000c0046900b061301c0d1040ca001d8414100c107051110340b4004001698001c20100389403d05400c0c241c00302030150b40814000c1104400402c6489000c00ba105901d42c004c14816200c1c5605403040401e5000c6014030283c2c40b10f00325006641d903030060713101c46c0c81e5060480010254000c0541124440013894400c0ca08603001883c1210503090813850801440d540314224030b005007408111002ea1b0410b40000c5850110000c = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 431372464 1250 431371214 431371247
    0x60804120504051e0612040f1103010b0603040204090311061e091c080405011401030c26071e0b030708330103050411191d01080601151e02010b0a0b0703 67
    0x2604d46083c2c65540490f101d200d8070320030501291420b49003140c46480c0211080d141d418002141103403d080c141710741c103501d480040c8468110340e11603082001505034910104c041200d0b0030f0b0a0700d03004900b00f02c2c4134000d0f8a54100c210320410311800d030411a010043c00304400b68424100481803044003107020007040498900501556100c0c00c243c0d0250126050003031401c0304100000090003040441da0090700d40303c030244c500e45031650b0456840d000306600b5140050b0080740c400c210198000b002d030702407030040c4031116044a0307a4215088030354104131012004100d400d420031800c40040c00c82d5401e1480c5592440344402e2081c801c5000400c007003144203040c1552600801c05010f038409c01802c4003100206901d048094220400352420302c00e101e0030001030f050701000b100a452080707209041e01d030032400600d0940e1a04050300c05982000d502002889203c0c007410740700c90001c200e0100b42d0007094001090011412043c0002c2440c158850f021421040c800103000a510004030003070f0340e844 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 431373714 1250 431372464 431372509
    0x40501050d030f020304170114090a0209010524070602030f0f0c03010e07030908160323090d03030b1c05060601111b1c0506060a0b1603031107020a06080412050405 72
    0x3640e0f4242c1c91072041d034010300344241d083d0030034002a150541140320440300c4080049030b02e440310205030703564070140d50000b940a500c520043c4034504204124014200180070030505086d881c10340c004955011260075102d0075000410802d24a50300000380c1c1d04030b110004501050718107a00781d14494017060190140782d80030000400c480070f2180d0028040c00b5007180610307a482c00351064220007402402811404a10b80510154686c0720302c0c0100d05455416201507850a5440800c003c408080e001c1c0c01c07402e1690380c010070030b0540c032060b46000c0c0c3d082c21020603c00b61005400c006181c5a80100b41034100103808803d888442000714003c0c0c05c0107007880039400c41c0704901001641c89120000300303d0481e4070740786411060000c0041c905004110a0340c28548698498507101001d01c03e0035000040190600d0952000a202e944400c680801001460b8200303015913000802c59815944100001350b090400e01c000d120108221801c1000c0d00e00b04545000d28103000300304e1640c208003121390413849 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 431374964 1250 431373714 431373737
    0x703021f091410200a03090f0602040803040807090c05040303080415050c1c0c05030c1608070c06030b03010608120f1b03031006030c0e12100c05090f040501050d03 72
    0x960304071028603079100450000c0009405880c0d541c80680d0740d1100b01e1582055030310040c50340c801200d600194007594103140b405c050300300c050300070f04912801100c03482007583e01c8401040040c80075001811480c40a15603c074548441d403071614455401101045103000c0340c0290135a0424204c80880c0d038103081084040c0c0d151f003041d082c000074103402e00b017000d418041000401002c01e002058141c00064200c041c41c0c100049000498098038011000709004001040100380341178043c1035510610044200e504c00c940d036030b21090750014041140c003055a41d41c11710a00da018007544580410640081021a01c0c19030325981d100c07a680c10602c0480000941d20720400c228000721081280445c1c4001c0c22205030203e100d50380da2003140c0f54514042c2045020a42341e1103806040800409991180807600c03090040280301c419140c080003244c85121054004507105000d90312401c111a158140c13520402418402c4103452041c40c24071035072510006001c20380d5059210251981c0525040c000c520 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 431376214 1250 431374964 431375023
    0xa0b0603011206140c0a0f05040f1707030812010603050106180b0315041803180b0d2a0c170c071401020106051503040614011401030b030102040f060309060c05070302 73
    0x42284800c9106101c500e00304038403680100000d04035040151f480c003240550520044501e40101c0c00740e030700c2010403813004110100a100d40342c0742010626007031741c01d107e0380da0f958200b441e488840029171140f0750320010868182c142c0b01e4140101024100419502d00b0408007410a201c1406500d06039171011000c10081080071a03003010752a4090002c007c0ca40c60702c1d0942c03801c4062038408900041c44206d8040d4004c0019100100305c841c0c0020a80c00d0542014030407020301500c000c0034001e40c40410007610030500d40c6070208103407511911075250b420a941008045111080d000105415040104102d03514000070b002c404c49044042000c4078295810040340036144660141e603100d515400080c003a01180001103000ea40f28a90411407582d0542c2403001d4158244141d91802c5120400c090085d4007a410011150350010300052a0070f480b200311043d0452150428000a41ea0300802801c00c0480c0c0300303840104616040a07030400d21181d500030b58880e6020b0740100741c400b02011140020 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 431377464 1250 431376214 431376221
    0x1e1b0303090601062c220908030105041107030c060b06090d110a06031503020f0406050a0312020105070c110904060603120320070b0c1c022106010305013204060b040e0a0b0603011206 80
    0x602030120030b207e5841c0034205007250342c100703006142c0b1880c17511300c94640360f17800302086a400c1d907403585a00940c1044d07502c50100078619100c400c0d81010040006118607542c07002407030041841102200910007a40c001d000c2464855086075080c907203800108142410f600b0b00090403a5030403107041c0f803405000b00108001d0100c650000c2d4202d285a60040100403445990351145540b582c000c11496440703000884406c084072a0150500000400004650802109041d40316001d010301050303c690320341d2062030043e4030740d184070006a074070300f6030921051604003c030402c030340d1040510341485401e86480111034409080021100700000304030302c801d0800b4041c0b58048051076001c5458003008154034000c03460011017a0701280c1c840c00001c0070f540c001e2240381d06a031a4503400803400c202c140100403040c040034480e1904800c4243e5a000241c0c1c071409000058420a415641c4071464051550300c400d40140000c2c000c14240342c04081c41e504d0f000262811195101c03100b030103500c060f0034400d004 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 431378714 1250 431377464 431377519
    0xe0a03120209131a0315060a03020405180a120e09010f0b03071b050c04052a03070e0301060b0c06180a0f060204150c0b0604021e1b0303090601062c 65
    0x1810f040040d11130725001800001070040c41c0a500b6580f0503640350700102c0701c00c4c80071102d140c0d01142900c1d0500160400740e0249a00080090013400701c0300c055a00d8910f010300e00d000407200f0214078080c129019a025248038141403080d04c0030182c95041c4207886442d101c2c607000f007041c240004000a00d04910502150001250700c1040c03c03900f1900b82000b50b01c411903803010a01070360414020078508001c69000c0340800020032006044c0c00d100c0c0113516400d51018113020b04005031038401e600903550038841c00c0c0007001040c1c80280c1e5007882d0455182400001040d400e100e909560a18903140c1003c510103085585c070a5003400d42e00200c1c50f2150017402590080c034040011041000c0c442900020100240390160190b40e40c580d41c0d01d8104426845407441002000c088101c600ca54890548042c01d8422407403011600001d0408070810320b103410441e00304c4480d910110040040136000707108040300c02596040c54441071982a2051500c0c88402011030240300f1a00d1007440000b002c0d58001071 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 431379964 1250 431378714 431378749
    0x30604050705091f090b0c03090f040b04060905010314010b1c0204020d050702010209032533020322060f051e0d0e010b0d0308040f030c050105040c0305010e0a03120209 74
    0x854601501092410f020713010800108407040d1010a41101660503281401003100040d880c180c400000d0081c0410704226440d00035844001600e02c0b83e80d00d0040c0c02c00707807a0344000090300f903155060040b25903189800c10317611a4901060880c16807035840c0070000321010712080074081e0180d032001c10300a104500c80018414944002e00c50901d41c103400504040301c00300c0403546100b0104040414234061458844c4004603c654100020480141c907100310040c1d003e0000c8201903560507056180c40c0e5145048016040020030416451440504c07445801005144295060804202901ea41d11a1004c0c5040c0a008200e10414804e2501c00059213072044181c0380e240c140001041001c1c003100364480d0159400d2600003601c80c1001d9804031000e81d0180e80700009621540c0360404011b0f410030b81601003046d0203860101143c400d0280a0056100d06101c49c02240740d410003501711007080844038480d400410110001c6603100d0303d8110500c1030850010fa4a43c003042c001504034010089030741 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 431381214 1250 431379964 431379979
    0x311090f280f0314121801030902030111121302060f03040f02120c1e10050a0207030b070e150c0a20090109020d11030c040e150d15180803060405070509 67
    0x511402c0c52034000007100c2c8980403004190440140c3c2c5511203072a03000991101006118541100c0c6151812014260b81170500086891894020a0075034480c4c00250768840000620f181c900c020b000383c6603a0000c0e18003c042e1180145900040e21031045a02c0c0706402100803011905100d02800301a01c019402001c90255000c41c03000b450316429400f030380f240300d40000000340302854041d0014200a24008244480d4040d401c001550503401a0303200d87d08511070031300c0100000340011449401806030740c0340e8010265185082000d40d50b0107503190203080e2805d0241c1c8014520004080b507496501401845020001c955070000800c20844501d900000300000092825840e900418143c00010800d202540500c00907504522007541c07000001340d0100010001d51401c01e90703560700980d142e4106a00501083c1c000380302c480c0c8104007680c203e40b0300500784d01c503a40248031710009545a0900408186030549810f12a400000c010a010320344810005044620072001c6400d5004002c2811 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 431382464 1250 431381214 431381219
    0x20f0a030804060612150b060405030a0f0501020c0d0921020108190e010906020318210307050f0a0e03010c0206010b122d0103141603061a0604060309030311090f28 72
    0x75035014031b901901280c50703031410f0403c480d80c0c1400c1044405548002d0002c01d01010555504c0c0c0c003151b4142d00a9500d95428042003044200038041160044c5180c5c0c5c91511850401c4c030041500500ea01110041d0b008007465100141d800030301c11036000342000003036000802e2074407019000e0001e6002d002c00325464403854008000c2e240e40918011551070703004420f142040c5905907500c0c4580a8031280c0102d001c482085112190401984d00810f246425400d000d000c240001460b0414080280420007034080040b407030400344181c09440d0150b20041c5003552422107925001e1141d41e01d1516807a8981e00018000250180440c0c1c1c039180d04100c04011543e581c0d60171085134400e00003210340d804405d090385c595050001e070b03c11141a03080c04a4440d246595944401840d100b0800710328940c1e0344030492401d60300e81001d80000c040903200402c1d400940d10700241150a0180548140749045c000188182c0f250000902c04010940e203002c00460150f030742c90405103010b40020340031101103902 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 431383714 1250 431382464 431382473
    0xf011211060406090905011401080c0a2d12051b0d0204051003091a0402010e090703090f0b09100207050a03030c02032b0501060e01080403030c090302030303090106060906020f0a030804060612 84
    0x140d00807203120717081c10840e07030741c031a14109807c113101e038038160008107107101040e031041940e00144500c840c507040c4002c0704204030038004c2e401d0b51614099034600c5050100b41501c950880340d92114030842c440c00704030915041b28a000c43d0030f558160781e006100c000c50300c50480812a030448020340b00041ca6010800c901d0304008000d049443c004440100005041d46d01c4032860303d0a403070107140c0c16101e80e640e0741510020300a07401002000c03e0304054030b0710b5140e8081000c0700d51f8107014071f00444515200d031170000b00d054030f090b040c442580c0c80503104201c9000892030210f4400301190341840d02013aa40e1400400302c0c03450141c2050300c1b80341c58811584030306940d44407140110080c10b01d40c0600050b079907007200340e88031642a003803503001c9459940040c0000b0720039400783c00855180e003480c1e5440e0b5145d8010a25680088500340f1480e1b54801c41402240d0304400c3e41c10061185100802d04a6400542d080c1c9405103404000c040c4203c0c03801040810505800c90302c05800341d00021100c0001a040 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 431384964 1250 431383714 431383727
    0x25030602040b0414030d021b06040909060b030c01090506070f030311041e0608130f021c1a0c09010207140d0f060f0507030b0a21020307080a15050f011211060406 71
    0x40c90302100e510210a80d0905005c06e580401154580103824050240b20940c1c041c410071401c0e507584480100008102188139104211603280101000510070340342000b49480c1c11201c0c0f501c10b042c0040200c007001389a41d540110360800d64031a400d814405c0303082c1b0b0150041c2030001c041c902018408500400c221108650a1040940c0d00d140d010318a9139400c42590a40ca05442c5400311510b08814200071852810000b0343c880d10141c50b25044000e00d440210b400140441c080780c0440300f02c4480300c5480744030000190440d0010500c64582600c80c0000707560b8080d0361092407111402d200380340f4503903540c0810449801e038101c074242042640c41c0c0f0703251006050700058040e200d03180002046c5464442e11650500e000c01420194541c3c0c1015002e0700225015041d0950700140c204080006850621101005046a2009144000741d6140046203c0d1950a40001003031921040050401d0b0581140f411501c48120740e960b0240b4905000200e140d140908507000200020000b90f00e690050 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 431386214 1250 431384964 431384969
    0x1806030b0103051c05090609060901020723040b0406062c0904030801031e0c0b0f070804030b040c0b0310150e0d0c090f0908180d0c03050109140f25030602040b04 71
    0x1101e04001103681340295280d010b50440325810010600001800d4108440142407200050040b101d08940d0380c16561040c00040d03002081e65a890f241c6503c00c1d0130326000f0040c6422003258140045410140d00400c01c2000d03075420700840c080100a40614504214111900304000d0302c0207540e840c260074003400ca58001e11003207400c07030011924001c420002180485480354020359a1102505d404a0070070560172070b5603841050042005200005071550005200541c8a0245d40e151440d01e42403001e5105c400303901c0f940c4120303020030812038590605803002058408409882c1c0b0900e00c0b6210071a11070b440414016041070301d0f0300303100050144818502c0203d547c4400144840040c0150000a0f21700400000345064014403d0007000710040c40c189001502c06401c040c00041c0c9522644640d0f00c0075402075940780d40d03e407841d00502c141503c4400410302000700409021034080c50450b0341f000350011a0071801c0000903454207001c1d070118900001d42d0401c42c10b6488584a140076603c0c1d51051 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 431387464 1250 431386214 431386243
    0x20105040c0e0403090510140c07050a060c031e0905040509071401020309030a1e2901060503090c12100f051e090607030902040b06210a02090a1806030b010305 70
    0xc1900080c0302d500c000003948116415503410280d1032070311051014040d03a100311902031104500340c410307910144502400c4031001c4d460013803602d18541002d205080b5150b42009041006401031400420b0304510100c801c051590800d840820400034102c84031011070b0082507003d403e103400e0090481002890206484074041c000c81c01007050401640c1e24030a190003583c1542140030b0040204a0741b03c0122a0449401007901d280e01d155030340e16601120307509080f8800c914070341c8a101c19038103011499001d0301c414203046117581042386841e540c1c1c0c0022601644100d00c40e001000040500b0321255100b00001801440390b801d00c0403043c0d024000840700d505001030042c1c00b201020000d130901c2c50080680e100502215180d40d4800c901400d281c0e88266001500c1d8850302a9545540e4028500401c0900c041d420305298441c041384420340c060460315105005120608069135840c5105040394488100103000007640340f0001c02620880c0d0001e00038015040c0004203004e00402d003900707100b021 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 431388714 1250 431387464 431387483
    0xe0c160b1914011802030402041d0a1401020405181b0f071e2d0b01091b030b13021305120f1005040506010605090409170a0f0306030209150a0f0602010504 68
    0xa40d44400c1a8110910601504d8072540003148401800e945c015038010340082d00203d4000c20320202080110820000d600d450b0b8840f66101040c0402d00650700300c03034400c0c00c0c001c1d0b28040c5003400081509510b9600d08180c003c1c00c90104a107601c8410308403031005039070210b540e02d412109060681603001100b003503070200c40080e00e440345400dc0f2120982c4541e446024070500041c40030341d0b00138002130082c06641d40a00f80c7c40303000c0843c0f001440c1500900d80b03220702059940c661901c0c0c68510005504450505040410790304441c0d850381c003d00d0700c041104c2001600c801048011011510b10b5610580d00010b0034070351040e01c220041108490300816400b101c0d81c001c01d4003240b0f01240c5d41100d000d04650004401400300034880d600400c0e030640001c1012032102c0c496140e00d4884101000c900851480000302a5059a0008002e141109140c14204912440c540100700524802800d0107048028458154030a9031904559000703468441c1900c1c2c4550344800b0064024030b400d031020780b0304809 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 431389964 1250 431388714 431388731
    0x313030302011a040524220516020c1f0c020a0f09050112080703120f020c0105010e160816031b0e04140402100e060d11070c0b040e0c160b19 62
    0xa060107500d01500c0301c01030b8220100c0d07003540498180030b80d013203040d64007d40c031407440c0076803451008150081c01d01c0740100003440d0034040000c180586501100a0a641048040c854140d640b038504202c880c1c6c246070090ba01144410b000c98000188600081d03201c0c0c000d110114100300c2c05074902040e078100c030108200700d903258a03604c1560b6941d042e004001840030048000040d1040e118044401120440800c00c405c2c0341c0c480740706a810102c40c00032580e6583e001017002000c044030054201c0040c15581d03010f42c07401200200b412400a140039021402082001d4041d071103640f240d04402a0f00c01e050f43e02e10045070004000d0715400301c0c0940303d282420108203c907900160400d014a90091006541051086d000c0d18981090035171260300100c00e00c013048800015000381130180c24100007581d0340300d032149003038810800190400d03855000184814000740d41c03060030007034000d0011100a0b03181c5000c00d841d0102041002d074002c05218070182408145403c01d4101c014118014070306205190 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 431391214 1250 431389964 431389969
    0x30215090705130b01090b070b09010c0f121e0c090609080c01120f0f18061a031e010603050d030903030f15051c05010207030c0b090705090f090313030302011a 70
    0x6540c2c0c0122a8016040c100b190f00049072039000071311190041c10822460b07a681e49040001d0307000404240c440580400401600c00020b20940800034410300308150b02c1455480e000f810041e050720241074007a500c101c4410380e05211110a021066400028807100349100e00090082420f48900e034045501804003045420011400081058041e5103120a006400d02d030032024111141034035922075510b90b24044200711a01841d210302414000b20325454042c2c4c50b1050440700c1d07405807240000f4510710074240e2030b070b00030604040500a00c009401035100d0525550b005100e594030050140c441d1080c850301894042c5c10403009503011740c908200d40340580400c1c0042d90a18500f07240b040340c542c00240864070f000034045440380c0c40b40ca50f1001e400d40e0382e0707181d5003240d01a000c25404504080040e0342000460b5200a40c00400300000d030600500c0c00300421040a4041c0c00890406801400542c203014108269414444203903c11000ba650324207000c0e000307204201030359902c280d100300d1142050 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 431392464 1250 431391214 431391223
    0x4020a02030a0818101a030a03030c0e0619140f0307020604020a06111e0115030605102907110405130605011403030304120201090813091b02030a08061c03021509 71
    0x4404d01d0010309a114128400000104185141d8440b6902415402d2055403010000c120b03c0d10312035140001c0d02c56142e1400b900c100c0071300407003a200c1ea004000b82e1029070200d5810301503519503400c003030399000032014125045001d14484203800c6600841088420b6500107942030040e8000d803a00c17040192034480c100c0381c1900b01060030700310303600c606e421100c1c540c002014140200417050001940f80c8800c500350103905130700e80c02511041e031550107100800001450032401000e41a02a4004881d030006012561840d11050001e500000c511541406282c042500f0f4400c03008208101a103040c40b440e800d0130b407560310142e410a1030303c400807804408076103003020301d410000d00460450341c4540da04141c0d1800c6040752011552138241c840c0010720b0400280214060032540f881d001401c01c070030001101e1301d035414062040c1c0c10314171000c0d085401100f102c9014400780303008201e6a9601000c901c600090030051240c8007583c03809103060550201d2402898000401e020049881c0d0300b1109a85 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 431393714 1250 431392464 431392501
    0x70609020906040e031209070801020714070b040608071202130305060a111e030612190302100204030c0e150a080f0606030f19030e040501090b131a0f0f04020a02030a08 74
    0x3154410008410484d06c04028103034407000d41d00484a00c5515407421038266044000100d50100c48035404440700c04003030000c4805400141800c0341041e207810002030000750302400303107000c0c1b0552000780510019143c0445540c5005402190540e03560383c034050b695101e0449210f403286281180020340c43d024074084581c42e01000d101d080006024454103a050360003c0c01142d4400d410700c850001000c41400840e6035010801101c0034000346a007006400d1042141c4040162841001309000040b18003085900307942d0700c21490803080e07865031580c2040d01c051040c0c03543c1c004411500003c030b240000441c00c89280d003035011742c0c055481e00414141e0340c040d09038562040b0b400410207d141c08610081d00c0041c1c5001e4a082c600450540020070100c900a0704803800607a140c0a18548034109031360f40300800320307034038000f000407402110140c0125494840034030301c03e00c0616142d0040d0b9541d0b40130074071820ba008000f15600c4145100c003035039a9201003000000f142d0910001402a01d554421940 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 431394964 1250 431393714 431393741
    0xa050411010f020a06050a050915070203030c0703050702030115170309060301091e090807030815010c031202070c240801030803150423010e01080c0a14060f07060902090604 76
    0x3206525000152441d01d8000d00c85400c6101c0c160200b000f24015000c1d49014610802001555041640c150380c1012449004c0d40e11140264050080c01d650001c11640d201076120000ca031103c00340d2400b100c0b42d01ca05000690700d5030038420b9440030030fa07100d044503044529001c244442c0080c12080e0640b24080c814a40764001c2040c00100b145600355084980011003010400c440f500c0d4602c642001c8442640c0281c0c3d0420307010a140341056000301109810080c49800c4500b642d164500080110178000c2005081000041071900718022a030151400d0582c030400014480e81c650444801520040c1d40304030030301108116110200b0f000300d042030305036500004032601d140da07005031500e01d45a11010094210780c2c1d6046c90031524241c4400c007800b0790008850804e2552600409850340c0c041a00042d4854105e444000195a54100142c0885100c58000910032000400052140c007911000c3c0c000e9060014080d4204100355001c5000540b00300c8094070640c0350002804211010240c0064 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 431396214 1250 431394964 431394983
    0xf0105060a031a070309050703030201061e12022110090213020f041a07020a06050a020708010e25090501061809140c0310030602210c030c040b0a03020f210a0504 71
    0x7004286283e0081da10510f10b04000c96980c02595905151940300c2d44164011703556100c0a02030020391105118000c0e07030303d9038407002040c00d080030f450501040c1c0740000e1142d418184100c074a80741a031418603018000f0340c02c2ea05440070440c0d6400c0030f02004101248501704440d0003410002951094401030190003080c41e0031310307013084d030703030000040010200840b6107000f80300b41001a40c907000517201030841a95041c0e1a5120703c0b0b000303071525150f5002811103904000428941c05400124410200543c84e40e2400b040700b0301000c41d0448805411103150181444004610550412038a10310310101d24034002c5155520050341040341c03105101d05806034032600100b0845500d081c05141c014610504611a4550360380d0781104070ba22a0310741e0b2031100340c5003400d0300a900100302d15a9110680319406840d40c540760b10808003520841c024901400d8011841417034440c441c4d4151400c5c0e049040e08030380d561704070280c511003196914031030100f49240707000060700400481c010725000f035a02c00030f00d5 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 431397464 1250 431396214 431396243
    0x405070207051e040c0c0b0901090809040903050d06030c0602150610053109060602010e10090309080607170105060a0c06110d050a1406100207120f050f0f0105060a03 73
    0x1a880c002d003143d080500a451020f0001592980b140003d041740c90f0b00c42c51045038640c640819001001411070000781d14050b020408205001c0c101d80005a044078000b820301c0003460b00b40d415004003201d2032003507031900a01108000c1180000010381e0110340840308a644d04600e04c031042030b001c85500d034120381d44844062606000d5000b034040178482001034004c00301c0803601403121040c3d004005175071100c00d04c0200b00e03040c0b00384202006814188001d0250002c461030165807814000c078601142580e40c40410103152050903120003a010280543d040e07400c0560703004040c5440c0490785051a0004000012180b400c1400c6890294940d00c4103d040000e03601c0e8100240070307000306540d8506003044a0b040c0000b0b144500f5210b00e01c10b002c00141074005400103080542c000344143e006000c00d855514a054000030503030200e0f004081c0e030a0b8640380d5030ac1c0c5942e44200602004009215109101503001404904014100d4950000300000d60f01c10041201850075840003070440c0c001040003 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 431398714 1250 431397464 431397469
    0x72303091c0f201b150a080103080705010b060d0b1906080402040f020c16091b05040b0c030f120f0603031e0d090c0e010905060a0e160c02060307110c040507020705 72
    0x2e80e4000841d43c07450301c4008120741c84180c01c11000d00a0044240c43e10300880355030b45007003060707078500e02c81c1c2108007800c1c22181400900003103010301014210003008600d01c41000002d402130b0008050250281351a01c08403182c0001905404a0f500d101d101c1ea100303440c550100140d004403c0f03a800d40c4d035511450301c88d5000c0c0401080c1c80180b0f0700d601da808002c440014141046801e0b0030207203540079900c00c1861700180c2c0c4220f804248020902c01902848207142d16404410380307042d1501000c6003503980174800722581c074510805a88000d07035007020a41051009880c3d680764400d14401d41582c3c042e84c0e07520101a1a07110310008011210f2400c82300190900c0b545015108003100039a0004809145481d642c0403801d99030310160449880000510404185003d019000402035850142c40c0d8184070580404010003081201001e070900a5805002d100f244100c0d501031300984015500e0800b5003008140030b110841000880c8a25041628241858451288a00c8003a03001d0324a031401d106c02c = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 431399964 1250 431398714 431398727
    0x80402060a0c02030d210b0a03080c0f1203011d0c0a18050d0f051005040804050105071506091d0f0a120c06150e09010c02070608072303091c0f 63
    0x29000401182100b00401600c0c104111003202c0c110780c03510010140d8201c4620741c601c8080058104803800e100900142d52190303507088081c2c1768000149515445807520807890505030392015121482100071580403144240d0040d03058940e041400401070301d04203c1c600b0020030030381e121040c400040207610340c1c288c41010754032501c11141d104912182c2e56800010f41340d541440f01500c50050140640c4104501040340c0214994085c90a0146140c0307500c0708840d900440c0700b03050501c400028081e040007803465542005806015040041541fa007a121008107160501c2e00c0c4043c40d20507191450b00d5000990040079050107005243c440078503030ba1103140700080f00c042000d020003007000b500000c0c100c0c0180b01c104403406104804062602c0c2c00181e00440150008035540d25244604803165804a501000d44001c0e0811403a41c0d124079404888401a0768400c0e80d00011074009141070b1404000258066040c031400c03900040e0000100b1070281186683c40004100c3d515140f1070241d00800 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 431401214 1250 431399964 431399977
    0x3070317070c1701270605222402120604090206040302030d0e01080606030c0a1107051c02091e1305030913151502030d0509030c1204091b08040206 65
    0xd54480c1031418070b66030605012041e030810801a01e010721803880d0301000344240380b141c00c90320798101907078030180c10950594042d850f4043e100301e1f104c00018040b00542045000c0114201890180391070780c6040040c4201c2541c0480450300482c0040195945954000d5941610b482b400f03c1e010380c1c070b401c801c010041049050403038005a0034003000015944c180013003183c3c1e4a154490768503019001000400da507100038000303845982c00f0300601108130100307002d45001a03140d0400409030041c0c103000e00c1c03506420b07901045c1c0c03005d00c0020030b4007105044403002200a10075159090207403928140107982d09601454029003505280000301c00040011002007164021070507286401100000300324288802008240480c0d111034904034400c840d03e01d60f02c02094560b400c05c1c0340d841101c01c004e40728402c90940e102155215401b19a18407028411500c107108600704594800422400c2c00029170414030903c0c40c1103291139400f2a4400401c0340c281c4204d400c980d58079400760b035981c0c00c2107440d40005 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 431402464 1250 431401214 431401253
    0x10e011b0203030708040305010c09150807021510090f020c1203100f03080c0c010e0901090c05090604061e050a02060c0708070b010b030114040207050c0d0201050c15070306050d02030703 82
    0x80440c0e00561000d000404c1c0b01402054082d1341d0742e00f14100766080d51103542d50314040000030300040103030400d01e648506041d5202d141035100d5455180c2e049281604079004203034a40d41c5102071010803500d0308041400c0390901a02404101c90b800e45070012406010103000704c640000702221994001d010083d5400030764203490642c5903440e40e042c400c4248840c1c0049400020000d0100542c03001003002c0b00c494042460158000e40d06000820a0040184900711800b0344a02420518038010300540e80361590292540f9211552640000c000b42c508001c50ba504801486240d0719117031144003214407070401d64000340f50700c1c0c5691622120b10343c44080261100f141c148500000181200000c030300034002d1829050f00c9504000403100c52014450703849106520400a600002d48003290268409008441d1032200c0e40b114001617034588031310030100c0b40b1405104c42580031014515007039030181c0140e0340c042000b1501c82c0d051040340489001e02945c154020501000080c0b200c00c540c581c0300116 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 431403714 1250 431402464 431402507
    0x20706021605010305090f03030c04090b0306072c120c040e030403240207060207031e03090c09110c07030b0405060a020406020316020a0f03081e0f04140102011503050606030d0905010e01 82
    0x240140702e0239038100352080014024009801c0188507924000d01c3c24810088002c1c004c41d044c43d4201030680e601c00031500404039800c001c080c2c24150341403524084500003901d104850441e0881745900d4050b210800b0b4032461070030090070380200300002a01c040d01d600c144501007141c0a01074510380c8401203040080200c0e0200907a4002030828009052118400c1c0c5510b1175001200e0308035003040201c4040c2004062800c800e100102d03204140f507030120b850707429001600d00b814403c5042030f44540c088a400758461444000100400e02072400d01c11070241c02911891345030601c1322030681c4035500c40c10700140d20034000c5440482007140d024680303920003844202d40c5a901c60f03408030004229030003036940d0309000c02d2030440b0100044070302e9000641c4c5c03000a03250089841e11000140140d005800881c84403551001250b4000d40c0628205601140d081c920582e03240f0b45982e4070202115450f02a000e81c091100c40140104040000d40d80d050316200640b1fa058401160a04254080709018004 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 431404964 1250 431403714 431403733
    0x810060506030f04020a18021314060a030f0212010810060e0f041e060507030c02071e270f020405130c0207060c02010c0b01060c1e0804120812010b0a02070602160501030509 76
    0x103018100644031a1302d280540c45d401e2640360207005080ba41d0001d03404503038440c480b07d0103507030300bc0440d81c05e03000b00d0500180d00c2400c500c90000034040c01a40b101c50a24074000868901000250b0750000c04441c40203000c0c043e192620802d2600041e0380b1108014403500c08100051001da183d0b9140f191200c220004043d104c0d29801c00744d440a407100b20200b55640301c0030f00001d030b0510130340300030386040150760a504035105400d5071604124828044800d1004101c01c2000d000c0c000840c8001c0a02d0105100600ac48510100258043e00c11944504036840c0b007070041340c40c1405550400390107a0090141c141c0f400c0c1040c1c7c2e903074902c007401b00d04019540d0030100000d0511900700340a0f1860707581e003518101c20351a01496049200000c1017110815101031000298281d0840e030035200c03500340d03070942c0d490300c0e140c080c005000c0c0342640040c3c42020400427601003201800b900e4181460350883d40c45e075a841c44140e0b00c4840da00010b2800d1140e9035010322043d402500b18540058481e011518070fa0b0 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 431406214 1250 431404964 431404979
    0x1c0212010e060319030801140a03020312160f030314060f0307170f070e0615030408040b090a09020d0506130e19111005030615030702031c0e030a05040810060506030f04020a 76
    0x40d280b241c05c81c0442c100c000140041800172000960a00741907400e1440c4a04680000b680d80203001c10880742200300281401c0669a9046c580382e01c1903002d41010310407041d503d00900a0156846455a1b0300c04041c005440c9150140501d0029500500075000060505510b1011800c00c06549c2450b40b003062091001c2c00c008001000050a08070b04a003110f003411001c0110011081c080754910600c24000e200210b0903120465003222100d10341d965461480d100452214445980300c110352520100e44040213882b0354000920a01040f10203520f040e0401d100c0300c0441c0c0e552220005640e101240f00e507445902a000018524060f10581c80c0050040c4001404560081074003400103801005002241c01d00318100704014000d504c40700e08520381200700070341e24011241d050480ca081400e92000e0141940d00c100c02c00541402602e540703814040018003207070f0045c0b00c0c02040c2c0c800d02000a4071540203101e02c2c000d5030b8004200c1880c0d911764020500b9a8407024000342d9011521071000907400 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 431407464 1250 431406214 431406253
    0x612051314210d05010e370c0305090d0504080d05090d0c0f0e060f0d0209040c0801020f0408070e090d0804081c05040201110c06090409150e031c0212010e0603 70
    0x3100000c1d03207155901d600e03c80f0401520010b81c014880e081c5800d0038403170740c0d404002d00018002043c20215090f01c099047c02c80c020200b0103803003800b0740d180040d0b101441c0e9040e00114841d1004404680d1540c454802c2210380c2e01c82d07841181007a800c080760200340540b044c40100000140280313542000b0619855005400c01280d01c0081c1c04401140e007000039a13303841034a0340c0040300301e480441d19401f42c8081581120070142c000e20801038a400141009242c01c0d00c0000303003c40c0c00086403151014070890142d42c0c0b05014030030360340c071407044005014402164400e200b000320300007506000c0c00721402a5060380010340300311010f00d030500c2180a0400ca08020b83c151100300071002c10361707003030500025040c00804c00110a076a04012120704440e140d0804683e942002078400050180f030604000100030f1140e03411038026818100e42c403034117410020260030300c0c100030f980c0f80a00940c0114020103d20600030428a103040403401004550b410000050348a20040c0546811490031440d11100 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 431408714 1250 431407464 431407513
    0x608071202010f0912030c0203010e10061419050d0c150f090509060a0e150301051003060e06090d030c0908060a1a010203090d0609020a1e0612051314 66
    0x10444001440d409560307108807205201c03a61400c26415542c107250900203003050408000d028400c08925072011500c0075440f10146443c094140c501d600c1d0a010a480030746401d03c81e0328281d080c40da01c0001903280c101040b40121014501d407000311446c040510502422542040d90f140c109a940062000b07100301c001c031854485590303120080c01e101c0c00050449205600428040c1da00d07034041003019181d684100003035035000c01d1400969650880341503010000b4114041c1c065091009112600114403040d00036070784140410311500c0040a0055600c04c1d086418404560020100c00c218a02039442103105400c60302d00034075001d448515403450180141d49400205944200c1e14030b55400411702503242a10900c06540b60600c640f0009902001705071004c1d1102d41c1d108c1d201000c542c0c031081c40b80c00130101902502c1502040d2000448038007441d20404000c12001c40180850354228807a0074030454031400052041c0042e42c0b107903484c480c0d00c1c202005e0340d131065034040c2c80705608503c0d02102 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 431409964 1250 431408714 431408729
    0x70f081f0f1707060e030a0215040b0d090b07080609010b030403021e1605040b0607060209030705030a1217250908100b031005010b1e04120804090b0a06081801060807 73
    0x2e400a810b4107803407500c4101e41c0003004106403507582c10072a9801060074207600b601120b10070f24000138840c0a07030482c80f40303074018505c8030000100444000305030713000411000d000705c0d0300c0c103890b966103c0c09640c84c0d101280d250f0b501005200050281544032000b07181c1150013441194185200280d600c102400072010315000c65000c02100d0034540d0103081901e000e410243d030140022880c04022130030794041d07110001d0905401190324681074a0401c1304100a181c010112901d6124900302046c41c2d000d11030b58080098035048040c0c410301d1003984082d004004e501460a450350b0b00c80300300403034681c0c4c0c00f0f1400d041046031a000640303100100b04011626201c9000045c6d040d4141d401c1520b02100e1150b40b155281c2010f00410295102809654000041c00e4442506440e4510548014851900006040110001c5182c103000b4603c0107002592480c0408000d2900d06a0801c0800e808900c10040028100400103c103542d0740943d241c0b02103481000450030a483d015000d0400c04103401154 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 431411214 1250 431409964 431409989
    0xa020607031e0c0804051003090605070807110309060a03090201050d090c090e06130f020105070605040305090a080105060d02040b0f1206101733100e070f081f0f 71
    0x10024140d8461003003400b00d20f810180034011081d03035070f01c03860301039441020300c2000e5200940d100d8a020b604a10480d03940104104220302d40f40034041d0480c1d0058070310348005400000301c022040ca00004a4640c1d060040c159401c00307108a1040740980305c180301c201e0409c0406e0005c26400a15409011416071080740c000c442a800c211016044403000e07401c044860740302c8028401c080080900600b10550072210885000b82e040c0016200c600c68100300134109480c2004200c10b042d88940a000041d500315030342688642c0e9040100d0076200d094503640c0d40a0b0540e01198014501503200060015010f0300c80e03060605d070100082c08860016200441c03d070862001c110071401c00e1030043d0041c1c5200c00714881c0306205480d6195443c5890381c0f102c8030030f00090a02640064030304e000f07114203458900c1d280c1002c0c42d14042c1155020b0b610700c60302038680d980c2004500d03000c5c0980b18214045005a803102043d998580310381c1a03100128204841384601500d01040c0d0319001c01148015104009410 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 431412464 1250 431411214 431411237
    0x71b1532040510060e0f0405070e07020d09060c0308070c05190b04020f040c20011104060c03030b0603130f0206071a0115090e1f1503090201020105010e0108120a020a02060703 77
    0x49003440f4010014110180c42c210042c0040c141c03c540140d00100030142c4401c0d16601c501c0c2180c40d11905d0740111112200751810404029400038070f480d40f05d000395070350788007043da240c0f03081d074285440c2c510040101e070584000809041c4284201d401d414012030455100d40304003981c50b90341d20001a01900c0340e4401808020035410101001204c1d1981078074200810740c20300c07000808041c0ca1900d0b61000c02c140300103013400c0007401d400500e03424000b108003c2c3c3c0c9030760300c0c240a40728285100d42140420b0903c10f841009161100689100d140c40880303410380851242d844150f03012039181c0499204a052000341c0c0410a880b03a00711070f178032419215075210b504042c7d0780900c0340401d2034400c1c10024004001d000041c81c2c3c03450035410080441720641c0b2103400c2e0100c5e4180403820f4006801c3c14002c036032213240d000e40c55002284001e0007078000304540e903240c1d64418000c0c0024001c040f4260f1201c0e0300941c81c1c0c0c3c0601c00500c59a010b0348140d40380640d03280d0015a095000d804250001480182c0c0c8 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 431413714 1250 431412464 431412473
    0x20a1b0312050106030b1e0102061b040e01141e061b10050a0920060901030b0f28090e0a02060c03040e010906090c02031201060f0c1406071b153204 65
    0x407660102000d2070340a151382100340c0001e5984034014580002f50400380d000c2d212411400c801c0d54080c00c3e1420310444c16684801842e98070080002d4074503c107c1f01d001d00c13100c4004498030f91460000028110610300701300c240042e5603021002c104c81c20700c1c0c410204910328403c41403085501600540ca030104400303001e401c3c40c1d0060402500001c05500942c2e80d40c840d2a9164021140040d000f03003400303d1042c03215030001303020100e8030100c1500240400d400d9050054100c0000c216025000200660140c45a4454044500c0c05040368004c0c0e000c0c000070009880c108016020b050601c00c1201d144c1600e036001402d84080030303400031030710a03156941400030000b0750040150214641c4000c6040c400c81e0b141c41c0c1054281031142509100c07030012000c0c0c540d0300c1080c0044050740c118110b0b04c0f0a500e0b0040150380d0320f6044400c1800103000c610404c95807018007545184240d0401a4aa0b80c42e4481c5164002010211b00d11a40490081021141c00c039200700040300200c000700b992240b030301c2c0a040 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 431414964 1250 431413714 431413729
    0x7091506110f0304060c020d02090a05160c0203031204050f030d06060f2105101208040918020108071215140a05040203061305040f05011d070801020a1b0312050106030b 74
    0xe00555004820b00340c20001c0008103a038100d41c0245000303134000b0021700200d04410060000079420000784000c2115440164000d13600070030480b40b651440d61090381c0100d402c602d01000c0294160020000c00d03a1060040c00c010350814003070802d491003440030000c12899940302a1020447c29103c1d48108240c0c0d130451800d01c00c4408600344814112090300404c2959050858801603056407040490840d24035400030601a040680342615044a80e0400d00040d411621442e6055418050000e404012050400030003540c1038584034000d4030740b00b205032104906e0948443d006940e50416910f0240b00300b0016008019048040814405941c2031285001494201e07074041e5004006007e4a51541d504410010f6600f110005007611a4600a40346207417105000e04250309064030941c0d1100010000b06800c81408101d825083d0307505502401e0380101d20f0098082040c0d01d540700003c04c500369005032628840d2801c0e000009241c1c1e04081140d400f03806c0440001e6071400b40c10085c0c1000207 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 431416214 1250 431414964 431414987
    0x1180b010f0b09100309021009090e0a11090403020c030a030c060506010815010507020d0c150906020a12260f0108010b010306080a0f020d050a0f0218040f0b0907091506 74
    0x45100000d4140b8030001c51611403c160030380580704003042c0414070784c072079030080c1c40041d0f004209010b8014800d000600c10b04050054074004d80c507140851f000c01d02c2c00035400c144140d0010a090304061940100090303944010002e0f420b41c0618000413145540901c01c00700001c4c481d03211000151307424200281250340c01459941480044024000390350504a9200c0d01e00d0700c03d10b4903a503103009038404a0391542d491100200360740d04440b800b0500380004031312264920070f96034803541c07400c3d40c03a4822aa03034102c0c0c0001510030400340c0520b411140c45280c076020080c180c4142d002450315803400c41044001c0032a9101c104040e030343d0050010140a016500c1e075000700b46410b102550400d14550b46808484100030308074105016941c0440d11032080c0702c1500b58015090341e0304101c4905100510f5110044101c0c412003032500c090700100303c0e0a030007500035900144000c500d66480c4e81c60440d4514083e02d149880d1203100400600c100f09030050401d02c042d4103480c1081c09141c144050100076555 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 431417464 1250 431416214 431416229
    0xb0a02031c0527030d0f1407050720210f0d090e0a05071b05060f01050a03200f0d1a0604050708160c06020706020901120c050f0d0e01180b01 62
    0x48103000400b542e0680000001044420008000d004070084a1441c8101e10300e4117011802d0003018410b54405610012010151410000f2541c1c0e0742042101c0030701c00e002c03004080040c2c25050186031880c5401d000481e0f030000d0542641c121110001c441c030001d0000b201001580506034a0140d840705100c544030603082820840910b900342032282001e820000c1c48005501d40d00e00001e03640b00c0c824801080d40414400c121022525207090654070b0302c0c011118001c0a040b072000014150030300b046820b048903000703160862207203024042080100c00c01d02a070703030780415401350b5000c06076500816810400c0c441d02c0c58005800c05240402c240c1e800003400c0d64451f61903e401c2245c10340d0456545a40a5404a0201c1c80d000c241607059543e001d040b0400b4181c2071010405000300079166009010b0304800340c035000318821961142d2410388131040c90b080c001441c140001c600d040300710b40141c541d02003080000719640c021407481c0b6007101c400c007192801807056141c00b001404401c5810a01600c42c1 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 431418714 1250 431417464 431417471
    0xc010525080f2d0703030906060b03090a05011512030e031203190b18040f1415070e0d02010e0609010e1003050f070503040b040b1e01091a06210606040b0a02031c 71
    0xe2500305a40d038004e418000d41130540301d6115208000a03a07100d45c01400c4490300c1e180c0c480c20110911030391226a00c030101d86075840c0140701d0080004c446c1003801102d4420001d04c9100301c8c1e0365000c45419050710003464040c40341401e8803000c03013040d1004c2c502c00d4849035180b5400c20752844100d410750701d02d505401c1c00344110301c0e0440d0351a503410909640c0550070032507040d16081c2904d800b060500794260040080d001c1c20014040759040b81c10028054681c95881080c4c884041040220a000011000780441c0c031500307040e20300317050030000b03002042014108081001040b00c046103c1d81030605441c40060f59030300c10885500c59070740740c5a41088032441d0550039880d00da40c40d400c0302200a80041d010910000018254002615020160400f02c4c4040016965603642c580007801543d600501000140b041442141c01d004066036080c0b40c0c40c0460100030316020f21a955010b81c00742c140c0fa0048800c20000c01c10528040040c00146580c0d4021030b40c42e142c03048190640f0700700342445070081c1e05 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 431419964 1250 431418714 431418787
    0xd03031e0b060403260c03181c150605031c020d1121160c0303020c040e060f060307031b05090105060304330e060103140c010525080f 59
    0x1152402d030f8040d00d5005018589684103030b190a414079043c0c28656102e4940041c1d42001d64801002a0058002c90302c8400365404541080041040c40d002404e12004d18210305980810007220144140ca02482c0c00050b110f80c984002c40e003480c2e958007150341d000d180b0508840c2e40795410008072150320f1081ca4101ea2240c0f0001005856060fd03809001e14040c28000c80c41d00c40c003003c0304480560110b413025150401ea01d14002581d91150710094002d0b015101144905042c20b0090000403000c031006480956131304110300d0145031020b840548c041c40340420100003c2c440c40c21a0702c1001002c488481c8041c40d00d03007001300480301600450f0086c0418414840080c01a60401e0000e00743c0ca0500c200301d0791000c441d41c40790920780081c84202400c0c06079001d880200032901178180e0340924103010505051000e50765507103140004043c0094020000d0725042c4030b40000007204c5c0b031600712105140ca411074699031304035007007001e00000c43c450019010400740c0d10b1010b5490030383c502d07000b02051003d = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 431421214 1250 431419964 431419969
    0x1005040902070c0f1d071b020409080c07030b1b0f0f03130b010603090b0a090b011a040b040b031f0b0405011206150e030615030316030e0d03031e0b 65
    0x124800c8120311900850118100b16030301c80414043d0455501c0b580d041d40d41d442e03481148103501c0c0c0d00c00d040000b12002188055114951100c0c450340c3c030a1581c0e1131034038150700307001c000d201c1d661041c0d0740101c1c207102c0c0c050040f03401c0c808800254042d83c0b11808906081c05440c60920303c1c94003040815004011401e20b8080c03e00a55030100e2802000c2c80d1255101d0a100040507018180100b2a1104030004109150958032a001203405800c0444069807080842402c6521411014149002c0b8000400440301070290300a0780d85500c40c134171402c05a940401c0c81c01703600710b03401108103210f01004014401c0003c02d00700440c403402c2d40002c2d000916056011042e4801d0b070042d18100401002c61240c200216080030009005024282200c40ca41d500018102c10300e490b2002c1c4240a844042a0b000c000c100c40a070721454010b02540c41d0055620014a148408100c210244544c241c00c210b041d594818032a80742c3d5004c1d442c0071500d0780485400d0f005c030580a20308480b802c0d1402031014101e4 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 431422464 1250 431421214 431421217
    0x30c1107060807030e0a050a05060915250c0b070e130240080c0f0607030915030e0a03111618090201140a0309021e010f030b1207060513051005 63
    0x4500384c00c00003240004010400c0c01c00902c01d2000d000391090100040c200440061303290720034605071003540c48c1414203049202920a041c0c0f400c40d40c1494207408100d2003050060845880368950a082030940d409690320314680d50225691408182a603c6002150400d0402e00d5241c0710030038400c51900c1a1010890031030096030390444655803030103c1d40c14001205011104c0481c04500c50b024100342c0e20b40f111541e4a001082042c0a5928071401ca041401c1860540ea1a140c2c0b51300e8001c1040c0c10b068014004200c002042400c064a400311240c141105000740214240265100e4501c00100752401d4a020005ea010083d6449107030020030000301401d20041c03841c15840008600e0040c64001203c51400d6610034a1440d40000ba00003282c917055406140018401d032807007240c0c50101c000d80c25202100f800c103540401d0f0820401d0b9a000d200360301044248600078655142402d00484061400c102500401c0128500041480311294009102c2d0020f001c11076400144140402c4020041d = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 431423714 1250 431422464 431422471
    0x20030106170628060b0415021504031b02060705010209090906090a0809130c0207031101030516051b071511060c0f0304060618061e05091501020109060c030c11070608 73
    0x5010300c041d001d03002c0c0400c00700d07891002c55034071418003850740c441242005981c00b0f0b20881030307400c243d40342d140035007800840c2d81d40503040c803d0080035141c1d0710ba4a080d902a60a030140cc14070000e82c542c0c080045c1d43c0d40c1e001c2e00c40079024100058841c42c80c1418094288405003001482e54419401c11040324000600f644520780d101c2c4c038081d29100f00b90b002c9544101d8108a15001e1400e11800ca1b0007240e0010704041140d028106821400e8400801501100c2041c1d82c0d40084400304040045080e00503002800c0342d03921018015880b04110003542c2c20303c01c164100c040c841200c0d07180108042e503c0101e1803c850368040140c01d41e81081003007901c0621441549404028000c4002024800b283c0e001400500403946a1038801040d05000801002c01d40540d02e000404480c0b000d29103540e04010300180e400252281b4010b80ba40301d2105180130304110024115034a9240d10f40006515003d0642604040e4401249000e80320320080c280c0c100d44c040001855010031001c01407203078000780300c580 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 431424964 1250 431423714 431423731
    0x5070f0c38010305062211040e0a0204140601091e05010e03031201060e01121b1202040b0f0c01050106021504060518060915130807120903200301061706 67
    0x20004900e00007549522080362001c014050294000024020701180c00340c840e40406540c440b401101ca004000c0004664101406134001407003020007605150303204050b401d942204680c3c40305d080790300140546a405c07041c1c030300000c0c0081c00d010356035800106020190500095540400d04406d070f002c41d43d582184150307410000310f000f02c1001928107008607a002665010490140c4d03864203009171050912002480c0061030028094140418510424a04480c12107807130f0041503242c9001c81d002540c02211b280116030812002441d1071965000380301d408814565944c42d10841e115450849205900c01c0d42503410031011800480354036000b2944c410742c440c1e40003942e602c428058031800c04140424590b070303210b05001e1084070840001e014074064440340c10010690743d400140d0101180c2d00c18014141d030f000b4002c43c1c3c0000e41c03110852800350310502e404080c4640d41e8980102d101c0c0300f003d103c080088802c3ea00c010508083c042d800151021014074030302e0220000300f460340c0e00343c003c02281 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 431426214 1250 431424964 431425013
    0x102180f040b1e06070b01060207060e121e102d0203160503040c0b0a05090a051002070317190f02390f03030f0901090503120a14040b0d05070f0c 64
    0x4406955941c05c0d5018290080800b030290343c0c50705030103950b03601a0f02405000c81c22552045c440c0d45008031071045100300000c00b414143c43d950390905180380c02c1410500c1540030f1a03000c0185d440d00c91088082c1c08048803080021440d020030a02908852804901d0b1514010410400807001c151607009400146141007aaa030b501e41c144880100d5690304004141400000d007184100d0303110002e0f0444190460ba154213140d5142c04210071814450600c00c007503001483c0400209001c43c00001c18407820400142c9007910300c0888901d02c0c4941d080380700c00314103e00001400d5a90400850780c101015107000d03100d15086600d10354034011400440034203442800ea04100e0b648884d55018500a0702404880e1650140d81c03003410150480140070380010707451000046e80d03242c0007900e812000c07100748a43e440d10004403001c44000300d01c1c42410306005c0007000000340252a44d030080c0071280700c1c5400040e0740c7c20250001001001c1140c3c043c0c00f00315080b9010004281084078907810910911a207c = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 431427464 1250 431426214 431426269
    0x90907050d020301030602040306051806130602040909050708060a060b04051c02031f0b030106051c0c03170403060b0904050d1d1503150306130b060a080102180f040b 73
    0xc99903882000718140a841c0084000801c01001c0d4001c2c0040e00d00c9002e050080d5580c2001c0300e45070380c0071441c41c0368655101902080030544400c04110075076004375800352030281c6504102090740c0500c08225015400f0031400c008000c0c01340701e025001000c5241c28426540b40c413441d0f40c40b50181d4042c081c4507103629034034882040e006d0842000e0b07955018055842c8070074400c2c65100b03001040104090100d0070582c49205070700d0b040c1300721415150000c02032074003004100a0b41604000c03602c4100c0d1203608a0300c010010030300142030fa80301d00301f442d003071182d44504600d0040b054410544409000b00c0c00001403000040c1d01240d135500741031f1280b07020ba9000314000c50b65801c44142c4400310b5042441d4080c411002840100111310ae80440c0060f00701c034030701c10820f1594601c0c0441d03405049414011f0002d0005e45020142500080010040000d07680c4070f00c0070600726442155008540865007001701000e040900c3c07002d08507102114100704103100c200100f010a1000300c0c6000000d00f1080c0007 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 431428714 1250 431427464 431427467
    0x61203071a1e07120c020a02010c0602030c0c19021305070807140415030f0507021504121e02010207020f030c010f230a080709140604050616060e071d0c090907 70
    0xb100c491500c111a040c80382002d060340800b090707094011810100400c8600d030002854103081079040e90780c80200e0345642c17210002900050030350310000c0350802001c02100c1c0f0800480f48000000381042d8000043c52040216102000c0c1d010380e541c030b080804006c0c8980d0401175069001d212420110f1168282c0035030b088040c426604810048200c0c0e6541010969141d88a1601c3c0800144200f0180c3c0307031a01d059070344800034101c3e021a0048500049d0010b000c400440c0844001410a0b40f01c241446020741c100c0b490001031440180cad07010130348605618100c40b5550000c10700340e0141018844590000b8a4241c1e448050400e10023170901005840c08102482074a045100b4401d42e240c1801140c0100b820a00384c400c00d00146083c0d5020480c821242c2980d041c81e800246820301d4541703000305005142d00602101e01e104503002c8406400f0034498015640f20342c42c80005404003d0800c09280751042140300380c50280800002004a5034107224201c40100780d0440701c2040d243d486820 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 431429964 1250 431428714 431428741
    0x70801050a1410180f1a0c0c010f0224041509050d0e0d0203030c0a030206091227090a06061101050907090510080304030309050a0902070c0303030f020c15061203071a 73
    0x800c40b4201e0f665070001400d184211070704816183c00c80b0481c008141b000e01c40d0f01182c000c041c1528840e4000f14414002c41d030040c002d56605042c6070040c1c03548614241040700381c2c89440c901082916150074104002c01286000b941000c5443c80020801c4030a282c0f41c2a6541045000c420140581c4005031400c0d40d69440420a1280e4020100c9580e10100d10301c40b526804891421409031140c007010600003d0f0104480340b42c040010001e80c00c11a01000042d0284400e0b001e880a940ca2554052000c1d1240d031600341c031a80c00000003082c2603141c16001400d1403505400c1c48266454907040c0300f0003090200c1c2c000c040f00c4100801040e1501c1d5031940340d1094103550b00208091100040000030160010300350001c981c2c0855080c140d96586907020340681c811210001c0c02e144203074134103200190007075020508039100c2110040c14040c4024601c0e04e090344403103482c0a10544402005410b04d020508cc40801e81107e02950030404c842c1c0d03403018500d901c828a0031142080341d0015444021025 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 431431214 1250 431429964 431429987
    0xa050c060f0c07140f010c03170a24141903120509090412031a090708181005040501061e030b19022704020a090905180102040b03070801050a1410 64
    0x42034418050355814180a44c0703541e80c100c40d008084514a040c0298050050540c2013509900c0700004031000c000302c444110401451480d45640da1603000013030002e039000d440b22036003841182c80301d0903040042000b076071700818000620510143d0035600c296000c1e05c000a00f01c03540101c0181c018801032006841c40c0c00341c5860f0b1908651440104410b218403440d4a0040da003440e1030422000c4140a0a900800b2491007420b4000c007410010500c0741c0d00c14800c665020a11540c06c00c0050071580619042422415a901c0d070b03c0d4566082c4001c0c403000b0b01c6203100500700e03042481421614100c03214043c1c8110701c0098801880c00000034402d0384814201107006142c02c03070071907540a01c140f200340d00700c01e20410f241d00c0107000440240d45003850709c00c40c0c84030462511034161091510309401c01406000304079100054000c01c940c42c1c400c03403d001400c042c00300a140d80f5280d01d0304220040488205030b1005200380504002005940900c0ca192101240162445250b501d842e41094440e480b290 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 431432464 1250 431431214 431431237
    0xc060b0301050717010b090f1917070e22021c060f06030b24040e070803040f060f05040308090d0201201b03060103170c070f090b010f020a050c060f 65
    0x1010060745130b600025503244d00710008212500c5076240d11880f078031070184000043d004042501c0c03140c05490500324426418500c0e10404078450b8807080a003200380440c0d003150489901c0b000042c0125a8030051003540400041e1014070781c2003007600010049080d142019001d96010f01001e41d1048208124500003504038001780400b620804154004101d603200c2239440704030440c00709940d000c850420407044109131800c401c2030f4040c03104200007040300d6924840a0b214004002586610a00143c0001c01d030034411020310920b000380181c0204200c0b100081000001c100500000d8844404d4446251060302d0f01d01e490717030045c0700581c3c02501c02004865060101e0328240b1480d480042c484500d44209907081c1001500030041c1551010213000040010a4100d0000c0e00020200060103c4490440c205d407481c2da5225144030022595400199000381c90b00841425560841304441d440e5190388010450152585c507655101c121f18000e0f54415030300060102c08030301c9440207403025076089 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 431433714 1250 431432464 431432471
    0x50909030c0d0e0f01051c0e0a060908070201110609030d020d02040b0d050103062316031b09051518040e070b0c03281403040c0e010305100e0309010509010c060b0301 73
    0x40b0140070780f00c030f240c030295684100c0c0e03500c80c140d01a511070029901c2c109011451895003801c501e111074003504d150b601c9020340c0d200d9406034501144040c00b40c0d460b114011100c803030ba0f9401c24000100982620f80031503401e03600c204140659502e00000302c91450411400068a60494240d000d0291003141c3c0480c00e02e0f00c000c10b60840c022065030049040b43d11400c01001070720090305031803410000303004003410012640400504403040342d2078403203030800c3c051400103080e984208023000354201620031800000c21403030301807255040091281c82905c03940900c590a00202c1184200549801020b460081d034440c1e0324043e0f1100d08001c0013010303003100410745031164841e0100d00c6e034036084014074840c9440c003503015251103164026000305001c01e1783c0d181c0a403240c1031240001154005802110610a80600051030a501501883c007851007040502558031300e000d1080c0a440f803c065800c2a5041042000103981e0050215904a90f007801c01c0e941c62105418200020154214401e406508 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 431434964 1250 431433714 431433733
    0xb09070b07060c18080a021212030f150d0b01030618020907020c0406050f010507030c170714010c0908060117010603050f16080109080d050c0d06090b120c0a050909030c 74
    0x100d940003400d000b00303150790320640c000500f0420000130300903114044c02a00400c440c1e8000d8108850244500304510341190642c20510b4000004ac1d8030480302d0042261a200c02d0204140300c204d5044d0b5030a030111643c0c4040e0601d51a10f154501041c0f00c0100482c0e5030f41030303003110b070000e1070381e61703003546030010b088014925084d00041e4548a11004461045281c8280850107140c001981d4004400c10794441e400c103000c503074060703a049900740d8080d5000c090140721000c09000c1513005040140c0300b0a981a44900191009425108030182040c1030000a2406102d00300002803980d044039610309054108a0940030b045004040a80002d801e500440c80740c24a82c601c0000c2c00e00f502900645211801c80d51354045d542218200240240403490410148202c490b01d03403c0250401c00f940c0340c243c940b01003503004008690407a402802265100c42e0b000300140741c10b0030f8400e120700003600500191a2602e0024070140ca46000d014401c00d054000706441181c00c0003a58940120300003254107981 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 431436214 1250 431434964 431434973
    0x10902100905030f060c030411060c030403030302120f040f080d0e060901090c05010801030c090209010e0306070c061a010c02040203040302010216030c02040f18030e0609031204080c0301020403020d0b09070b07 92
    0x35150b000d000d009108080710500c2d4543d0008095200e070307000c50101800d544490f621030940030303000221581c2c4000180300e03804c500c820910040008610a0f20300580d2103c8042c503c1240b01c3d4010440c1101c551203400300004198410fa04c9102140d214100c1c41d601c00d8081d1201000b4100b0b40308a11180c8598410805e00030015408080418000c00d1004a0715940d2401110a60b009000c0100300a0b05054100603048030358010307003554001414015208582d51020078603042c1c1c102c0d440300001742d84554840a100a40c4100c0525010507894403c0c1d40a0a6001030950410400028001c40c1d00100007403d0600c01c0d41078405800c45a417070f00308801c6803802c001341110700b4104181d2040e450000c81603003008580c461420f80e4900c0d140490050807040d2001d503507401402000580050040000000f2964107000c0300104c41e4001030420f880f54207180c0c003140b82c200200c056902a80c8100000d00259580710310081000c5d500844a59542d90b40643c03e90815a00b940114401040410007c0401 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 431437464 1250 431436214 431436227
    0x1b0906090605130228020c150a030c02030c0a0209061c0f0308070503060f060c01090506010f23013c05030402090f06130e0106080a050708070b0f16020301090210 71
    0x742c1c070403a01d1101004201c0c090008910501c12445540360407054070010f48002002d545198100d07034010b4400b040c0c0350720b000c600c0d801c109498840800303000007205200160580f080820800080c0b0080d41020400903102da076a09a00502910176103504002a215585001e034a400c079000c0284a81401851307458138282450411000318049801100002d104c1ca11a00036a48510b0004010002e401ca0420a20940740e208030140c85a075502c450002c00800d00411103d8001d080f8842c0c00808a0310344000000201101c00002c440c01c03180c14202c411907a845840b011000c60130000c142682c80420006c600b000c2010301d1860f4500000043e402c03115600b00002d0751099000384e614801030396078520048102c2d40110303000da60042c2004014080c841c005d50240c90340200074000028110388441c202450850700e40000c4550354440f0006121031002480448001c04000764110304110100203030f1503090103450455241e286040c03540c030003035684c02d401c11400c2503009000c5c9140d4850855000f800c8 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 431438714 1250 431437464 431437469
    0x50a0501060e1f14030109060501080d0908030f0405091008330709060315090e0705042301030f0213020a080619030302060c07020a1d040501050a05131b09060906 71
    0x802e0520008141600d1201c01c42c3c040c48511030058106800d10091290520381410141d801d5035803160000006100b034403032a8042c01486000b4043c0c5100803000a2201d40d0b9030308102c0300d03900103110030490030754880141e90a44008403405103042d551306010b0b880740300e01d690002c4d8141c45010b000c2038a001d00b280b030b060f03014100c903181e107101d50909010205182c0015249540014000c090400102c1e119501004540703115940c151452503407410704109440001c0d01034001500094410403880c6083c2c8200d50352041800b6003901084003408403c462420148009014040c04082c00300c215039481040201141d1150006c54448070307140c600802c1400e0031075500e8021041c1814800b03040681e84401c50803a54550b006100e9995682554507854001d10012071300b04400a0000c1540e0402e00c03030003610990511495550740c90f06007403c81c00d40d880504440f800702c2c0703004240818142c889200004071078100c1c40d00c060030107078050013034602996540103180356443d207140401c14140e00d4208804 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 431439964 1250 431438714 431438729
    0x110a0809010807050c1c030605030d031e09052104270605011409190905090d18060c0803041511040311090705070213060329100806071b050a050106 65
    0x100f50340d0700f032050315584248041c0010aa1060402040d0400c04140c00ba210001c90b14021594658601c04240741860a00b48900826240c0202010540002c800c403c0700040d000c00c20300541c130440d00c410392240d407540f03c0c070b0a4030b41c00580c00c0000d40804204903402800070442c4100e4600075030110007440c05003810039610b41c504140700041e040d0b1042d100c0340988408442c0980ca0501000e0400c0503000010071040441d400ca00c00000d101401841440c0c412940c100103007821980000009006601e0702c50f105018680e541c4003800302c26403159511907003581c4028003641d01d456500b40f24201140c905c030340d20310060a1544a660800b07a902c09001140d02c508a03d05500040808101c92188119180000980d0a11160f0007500c0c0182200d42010007200e40000c51503141d07124400980385607000003000380c07410f40105070750315041c05459500c80581080d40c3c001901344681943c542c000501684c3c204615840c01144100c150b1350304415250f407110444401d00c0e410f1400a01a0045225001 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 431441214 1250 431439964 431439977
    0x7082d070605180a0302060c07060b100306050a0b1c020309010b150a120b240d05040f1a1308090f180f0c0403050304120c0504050a0e010608010e07030b0403110a080901 74
    0x103c044900003007044482d9899000707880c0740d0780c9001400c0303166044a9000d0340c0e510b40314280742c01261103d50303200d0303c181400d075004503515041506008100340300f40d2000541020810080d041829000310560807440399050169485d224503d5490142c490345441640c0700c46022026206550312100402203000d0740e0f00c2d00029000140c0c0391004540000c280c0c0c9421800f141620040d10303080b04040d03a4810090b05186040096041e442000c07030f0004c690440d40c60708e041c1304c114144041c04d1403024031403d40711042d03980d030f1800742d0000c08941c022000061800201148110b0320b580d0358a918404c5000142803035100e900c040071074031450401620030f118580d00500100e10070b81000707407c40b400c0e00e8029000798940307498071444111400342d204060700c8810110402103178039a140d02646009074071080d00420000c0e503d820050844080b0f501c2004c80da80f61468114480d040031405030b040700c1d04000900003598503401d00f66182c810412101c00b0f107004464000c010003c10710f01802c0c2404003a40c422 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 431442464 1250 431441214 431441251
    0x31e150602011121060102070e070804030e0607031d130c120605010306121b091d0c09100e060d0506040c1d0708040605070c02030111040503060a0207082d070605 71
    0x504036403040c01c0a05038004108030100c1c040c44c0984040c1ea4101d4010302c1240ca20a0b0790701886044000265051400035018405000074980c1c07103199100c6030038013141c501c1d140030a04c1d6006445484030030b00e0351841101e002c010802c540e0310541040c0c0c01980e401001d100070300304968001d0040d5130980304622580c0c90302d400450154400d03c540820707207007492406050201036840c0c1d4008134a02050b8840c030181904008500d8a5030b40c0140c036101408092841e181081d141002402c00c5140ea800a0068076500e040000c0c00c245c0348404400c65101070041102510f07104003050b881803140c00c3c05441446090140401c2000340d42000b0b08940e80c200268022504c03607642d49801010a691010010740c1902c0070401084540d03110340d411a805081050301445264081780c295084012040520000451300304081d003000d0080340c1e8003070030700d4034214502851513a07503188601032590041c4c46046500b020001d0301c03d502c100041202080a02961242ca142c83c281014160807500c00403224030b90001c8 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 431443714 1250 431442464 431442491
    0x60605090c0d18022b17090103050f09030307050702010c1b0e131109060d05060708010f08010b0a092d0605040c0804200f0d0b07022b031e15060201 65
    0x2180b032084e0f006001c0b02c10b8010303070910290041c1c0d00e001e803000d49504080000000650607113a0f02d05035091101d5654a800c10f040014045407030080904822010210403c81d5281011080740d5003c0e5a038200700d034455201d4001204e00c10541e820040c0045007454445083c070186082c44404c83e01d00480c0e240040e81c0d2000c4d001000036200f2401040c6081e0448045928a084030041e0760110001d81400c0c400c02d465184c0328174208094421a01241e2600010720030306624000c500090542d4000901c0b4034000d56003c9500c05070300c1d105052400355240b12646c060320b1102c0544d4040198611084041035222a88100510051003440d10451424040c9581e00380104103032072045800041000807944060140e00d4004001f080440d4004401c4510341003d60340d503242540e0389801041d1100807031620240103490035003c0184005408a03400902107000168a4955082e0300a40380100d05500a20f1480508402c06151221558104038001c114032003e400140b048840c654001d01954541c00304 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 431444964 1250 431443714 431443751
    0x3011502070b040b070204141501030b030c01081f050d03050a0201060504230703060504180215030903030c0f0f07050a06060e01080a0f050309060307020d0801060512010909060605090c0d 82
    0x24294404100340020004e19a074000504202400600007184040c00a003100d801d070041205c1e0340300d5092500356a02502e5074144100071880000382d00414503800c480b0006401900c009026030550541c411000c06040685040040181405040d01410341c109203809840e98000303c42060040d0b1800c00c0000702c80c60a03000d02a482e0668204c19030030000c01d0700b481406008001d0035007003816180c0c440010141c960380b040f05044002da009180b4450388600c100803038000754007801c040d46e0106105200b400d80012003180d402984044149a0350380084818080a000d10b0000b0400c0c6800070803064240000420400c0740745220b400f0400580e52100340202181800f80035002c915480300428400040082130700c01c40309801141103130300300711440b400200250310443e0554011b81085014130f011581000485000d403000d410210300b020384203503c4111950051154104058803145030100340300c2240d0215014210161101000b45003144042d0301d660b0065100d88402e92900c41c3c954181e80c039801 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 431446214 1250 431444964 431444969
    0xf12070f141f0203071407062d0e070b0f070c12060c031515110a02060723010207150c0c060507020106230607020f0a08070e0114120c060307090306060b0301150207 72
    0x1142d441c43c046e400e50342c18034103030444007046902c3c55417590341036980100010340e421580c002d40034001c04010596204815a01c40b8102c440090348441001e0080403000800e845400d0403950466484291505041c00d214006500000c083c2c3c03070480c111070600005070000310744400b140c2c8081c090303001494a690440105485524018200700e0a00c0b421035100340c4d0038944c50a08202140d074001841c0d0000740c0c141e408070303c1c222501101e140a0071041d0f099114408410a2018004c40c1803a000b511030030403280b42406002c0f039159a9031180191640149400c14041b50401410410303442c0040d00a402001c1ca40140001c020812140566409078005400f50791800070b070905040c043d659003486041c100310000340c0d074450b15111010607492020040c000c010601200402080e515000842814203041d187e40d42c00740d100c08000d0205a90005550350190318251801c9650355a0600210f5142c0c941d5000100001e044c0302c000181070120788040d505962400480509002c103039a4142d980e40c4180c07 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 431447464 1250 431446214 431446217
    0xa110d020a0b100506210606040f0b09040f051911041a03071103070303091a06030d0e0102010b0a030605090c060a090b07020f0402030420030f12070f141f020307 71
    0x800d200006414030004940041419412003500e6071204002075151b000307a00c105440b030746018184800c03c0040a0401c0d00200d095032120b28080c14000d245e001034441d800784c1c1c641c204c00000e1000c00c98845a024506050084008100d00e00309007401c05541921180440d0080781416462080c0f64000300450713049406090564900c030a0380081d00d04141c2006011070103221207114400541c00041c0010248941b190b9400201e4142500c1d140d4250584100840c5940380c00d01c08100151300c002489a000000b182411850900072000407800b4104191545400080c2601d000042107030640025000d040305009076000100140c0c248070403806010040700020710790f400204032030010100202403140c005801948001c0000010505070b074000c2d00c0450380e00c808040300ca00c012690302c1c001480c41400300c0141a8005c01540519600c6c0703008201c0071400800010040100720041c10040f145030360003d14040aa0400848951103001131003001208501c00b00008501064510071079114031080e = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 431448714 1250 431447464 431447473
    0x103062c0c010c0c050a030516080106050a1710060909140d0203040e0415051503010e0109050327030105010b0304170301030512030703090c090b0a06080f04110307030c0602030a110d02 81
    0x8072004403800d07240b5020079203920071000c102099988402c00c201c8061406600140106025210741560b04000c03940400d05036490120240065a2444d9004085a007003181603010451010710050a060741059401a43c0703150020002d44041989c00618125000c2e080b0040114800a0380c280c45941c00e44400005030000c00043c01548001d83d0025000341c00307408424405400b084441c03085410035500034050b00016014074203145024018079000345140c01c020301c55100c1d15940e0320b50701d0041e00901007040e0226a1402400000640b1307910340c10134020000e212a5a41e4206d4172003a03403054074191000285240480a0404541d00701e904903a0b000005100c1d0448070141c1581070303000a0240000c02d80c0300c01c0b00c4008954005008000380400b000c2c001a403c121a0030405002e071070b5404a01130282c421b08004081d4880c81005170700a403c40508282e8800010000e030600c84240c1005241c010b05900c01f040d4035600002400510032152180c522400d4181d01039a03a0740c008040000040c2d00c03 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 431449964 1250 431448714 431448733
    0x5150f01170a09150e030d06080a02090a180203120309060606040e040308130b090f0c030726150108060420130f020408010e0610151d03150103062c 65
    0x410351140180f0703400b52045040c40c51038125202c0c107070f032040030328032600da440072410a0401030184108402003d00c0c1d001498405050340c013051001e000100210010380e501c5011604174480741e104156a0b075070080c166501280c3c5090381c1d8a1903082034070342880502c0b8450001d00315080204c03c5030705641c40e014800c40269103e584c112807080c402480c2450b07214040e10a0800a9a548800e40c040d081981c0505100da100c501400d16181c14404a50310030b070b0194004100120310080d030750b4144265090342d4028a020583d200b0300d0b04000320200c04402c0c2c061000005c1c280c8002c9402c1d401503201d6140040d503182c0d01200758003005110031a2980c4030034aa0140041180203900401e140200d015002d030500340d440c88000c2c00c40d2a08030f598a40c40e0410300030044010340c3c044814020300440c1080e805800d1100200418450014145020321505824010031964040141c580d000819000742032a0f50384070300d4150b001d4805d101158907030003001d080301820780700c0004080f4052481c11004280110 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 431451214 1250 431449964 431449981
    0xb120a02040f12170c03070b0f15090c090d12081b0409020304262110060f0339020f0309011d04020a0c0309061b020409051005150f0117 60
    0x21001d0101c60058110f1500002c0e070020398085c00880ca80d400c0510b0715440c0b01e081282118000811000c0303070300806020400d00c6080c201003c1185081942d852081f0394401688005600c950410f241c4d211042c2e0002c0420403006980c00000c4a20039a10020a0744824040360321400e41c00c00ea4603082c44041c0018003040340c165015550080c041c005800600120100c01400c0c2e000c4414010700d0400006031020f640014218041c0103c070349450800740d18a400d0007032620510882c00303003404108420000114652098001c4034409002c400d4185490084694000f81c02c84118004000364500000340f804490021580445104004000c0c5141011140044842b16003101c210380003000c6401301d1180d903407120b202034165480340d622041e89c031400c2e41c00c006d003003801207a01104c10403500720800200315504030810880b40354160340200b40104030b45401410800501c03001c40041d4500820480c00c040780e4008504106001d446005034180301400440e4910a29004000481c0e91a8045680d02 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 431452464 1250 431451214 431451239
    0xe01050d060e0c040603030206090d0c0b04020f06070507060e010f110c09060d0503070b040204110a02100908070b0708010504110f0313030311030708090717100f11040b120a02040f 79
    0x282030a07810f481c40e116280000404544ca02e80040c0c0040c1d01402c1080000041000713410072800081c14408201c02c1c42d0743c0d8082c03504070300030b000a0143d40580302c05001c40d02c1e60f0081da241c183c0e11209648840e03071a410010a40c09160320424001044007400b69000c074000c408030002030500c040078149600c0450140500c86030040c01d65904001900b03d44c00c08120103002a00d40c0381e201b060100e11a080900411054400c00084882c030f248013000503250142c2c000910000347c075004200422008000d0400419500848102610f0b13400304c5010401a154010101e03816503008a4003003040c1d01c40b842c0200004e004160708042c00c1d040401c042210581030585a120581c404c0c94081003a80c1007884d90b41003604140c81030030210f00042c0a010341c00340c050003c1c030083c0600c44424145040b51400032a0384280c05000c20f90035075502c440801d60f060240d00210b01c00904040390541d1195180b101c00c5155004184c03000c00b507803820b008580c051303104d40202e9040300e680c165040d4899062604003600c0 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 431453714 1250 431452464 431452481
    0xc06070f0f1812030302120601050c100506060702090106030902151e072604090b0d08040e04020a08191b0303081f21030e04141609180b0a0e01050d06 66
    0x7100b4107000040e84180340c07203114800c10b1203035401686030a20f00050034500400a040981804800c0c0a030440403d0002085100260700388008213070381d2a0507010821600c948a0082e400078a004004114107415801101205100b83e4505030001e07142c1601103490b0142214000c21074111800954441540b80d000d05100c40c014041c0354451196014801900b010060034070701040380c049010044800240b080490184c02558102e60007943c540d2802120310481c06019451408100424159218508a00050802c5100f124070100c106039440081c1c080705034013220b417040d00c5482c0b8528480e1607859001203e070305481b18851910707911169440210f6480600d09141d44030500010b04103103241d000e111482c50300e00c172038043d015241030080c00301a40b4507155016074180708001c0180031000e8042940101016842c540b01036504400715a0480e15612019007010b8032031128495061641c0059020b910440c1e0101c0c641d6a10455003035080000d200c2d89901004507002c0e980401c04603000341c0c02c1c = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 431454964 1250 431453714 431453747
    0x23210f010323120c1c0201050106080601030e1608060a110c0703060507020f1506041a1005090409020918010621110a08031201031e02030327060d020c06070f0f 70
    0x84502001c9043c08680080ca42074805901c0099500c0c001040c8040c15081c10340e1350700c024440c3d0340c1000c401034511032000c2c00c0c182c100365071010f4141e04418140103008181c43e0304036045100c25a180f22142ea03601041d40d41444142c41c03c2400c99002d446c40e8110b965562050000e03200d0b0f0745c55030722840000c003c0105020305601844804180f03c0b203081c00201c00d10008840c10202034204401800104c491003840d490180b4203400e108038540d6036005031644042500c0c41c082c0e03900c04100c40070401520001e00d00035044040f5606019240b18280300350742d80060010000c00825640d4849090a07000e88030045100d810315607003c030f0108003000c911680e5500050070b42d04030150350b1100c40d031442d8400e003010000341c40300038014030400450740c0c3c010b108525101004154110680c00194581c0f090f0021001c040d10214280009044240c0d01c0d0345520400909058540508503000c8010750b010322070b07940441c0100e80c00101803500070914462620751310703551703020800502e81096074558407006180a = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 431456214 1250 431454964 431454973
    0x31f02040b0316081509130204020d0e01051f051003051b0a080604200a050c010b030105160207061407020d02010c120903030e15030723210f010323 65
    0x718828030308015805900704400344a041c080c1c0020003828110003800310852052644416000c5030340e40118142c020886c0001001400864800900240315155181c541c0a0908504075400301040d80082e101b00001e00c0d00c4454506a0906200c1104442c00ba01741d1102242001c0c0210504c6030f4041740c0d0150400442100c041844030750880107420800000f40050f50300010450b40c0d050500070104000c500800744032981c064a071200b070301d038001e504094040140105445102a400750040d5045040c007030000c0181d41005450119145500020040980700b607031030019800b486078640c48409004c10703244c5424061503608001e1740d03104805084e810070103000140004118000046a60340825841e072a83c00f41c514540600840c0070454120b102d0741100382c125021034548400c0b070798069030602d04100d080f1030a41c00c00e07004041c0c403c0d0311208980c0208180f181315089405940c08240300e0381c101521030341d4a440381d0b101c010090200805601c101071182c00340740a000c02600011000b1341c19074 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 431457464 1250 431456214 431456219
    0xc0c08010e030a0f11010203101d070e2704050303070206070810030210030e0607051b031603050912070f0e0903071a0705040302040f090b07020303071d06160507140303040302031f0204 81
    0x61342a40c1040d150790f10380e032150f400304018a8000d042c41c01141000201d00c01cac00303840e2124010303100c164104500c0d401244c1041d03201c500c0719595556a14024020b40c000740840c00c1604080e0750340d400489d0110050710502c0b0100310b20390302076441c4c0741c8107603010241941e819056609004240c09034007000400c0c1764840040484c440000e1102501c03415003940c032103458480f046c070f00e66190f2400c00134416840d041004040c0d0b45203c01507502e800141c050400715502c0d801c01d00818000030070500b50040900806c580800d154184203144800c881600c0c40e284ca058440b480d440c0e88a211700e1038010000c10001c000701041d03400c41d1010a03071043c000c0c184541416540c1c0c02140a8074040d101314840940d44d14640802c01418240403508400c40f44011411403070030440c0601445000300074402c40c40d00121081c140d41d513a00b400c0b5031a0a852200c9010501d9103031400c20368503516070040450086001c06a41d10a040000c01c1e030782141c1e0020020113145007202112081c201c07000c1c0c82440265001c1101 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 431458714 1250 431457464 431457497
    0xc1d0d170316020c150706110408030c0313060e0603040f05011e09061b171317030411010203030c0f030912070c0e010b27041b0c0c08010e030a0f 64
    0x7a5100368420305010082c12012100203080211024011307200300443c2424007034221540c011344d081d0aa0080000a02d00c0100040e001136000b0b65106541510000440c2d2500d200d0210250107401c2a407c601200b4540f10042516008101e5224a402035400e10000740464202d00000c41481d0154000182e0150035443d5140b2069907500e0403079480d80c8481c407807020001d0074855003045200300d03900303a80e0140382d480f401004219040b0f440b010300441d810104084034086c20000c62a503511000519a80185c4125040729400c00c0724282c61505407201a000c8030b50010045900c035070a03ca8269150140c180120340150304042c00c2c0c00003500c40c451548501b03051840081c40c811f405102c00341d5010746032506d401d80e1034105030804d00d503405c41400001007480e51801c0000c0007410b0352083c840c0e81070504003c54001d0254281c00701da50120546042c1905801191040360280901001007040c0d80741c0c0303031881c20380d00c2c0b1010180c9140e10400c0594901c82c4034413250700c020510303807030203141d40104a01e0 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 431459964 1250 431458714 431458717
    0x807020f040917040618050f011202040f0909020f0301091e030908030d050906010f12060509341e031211010911040c18050609010c08070b01090c1d0d17 67
    0x4220b004500f001a080c80402d800c4100b4500030341c0ba08061079503550030f00c008a19407428030566181402003038070b0014422419901a00c003d401580c0ca40f210340b65503030909501902c0640300c01c0c4d00a01007140012218241070294200c803d40120740040000713010b0f440c0030414200b459060f01003001120011410340c070284000e12840844540c0400c0d1400c142c1001420280d0603840200c0011103d0000c009800c1ca801a04090035040000000d05a988403c4142064622100c03e20a0341303580407502400c80c81c00c05c60000340403000c01070703507155038440000c0f040f00781c1440d01c2d406006031502820000540ca244100007001303443d01d440000b0a584141560039584005003c0700d04080c002025080c6003090302c00e01042024500c2d2070300b03d00304103411030b603c03041850080310301601c0c001690341c0307039640640044003250b80d0010355540d84080c9801c1c0682d41803030a001c0c0d00c2203e420f0a81d80c022031442000c001b14403040701e0000214000d0b81c0020000c1e0068051302c112003c1d51071810701c081c684401710 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 431461214 1250 431459964 431459993
    0x170115080606120a03081306060e04060609240504020a02010b120a020103110a17151210390201090606030609021503070f0806030304030203060c21040807020f0409 72
    0x80078103040500400c20300600503030120056910080a400200382d110400c1038210207030180000a001e564140701002d017400c0d4100404622039881440100004c940c03140c0111904c0b1501041119030040711304194460804020a4004034100c09202c0c0b8a02303503000304090b01c403a0000044c2401554040342c02c011000d0041c2045402020080d82556018000e95602d0000700d0882460310412020207400c00c00b076402c142c503806000c440000c5d41202107980b60145010004c1c2201107100304011620340d42c4801000c0c4d8200e0a003001c080c1c802c189100d40d200c02c10f0000030000d0304039016078005194050085041810110f42d00c400c400340c00f1030110311803200518020b060125a292050061082c000081802c41080e070a0810800c0107681d40700c2540714580d0124030b099001911100e000a243d80260340000e941070245000f4400701c01180c0c4000c00340c039203c1d003901101c82c010a0b07165146d001011500980400710402c11200189031241803015030304001030000882c10900e49542d012030101c217 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 431462464 1250 431461214 431461229
    0x60f1315030b0108010b0f1305071413091103060d12090b070b010e07080609010510020a151e0e060403120906140106020c09130b0702120a05090f0f0109170115 70
    0xb0006000002c000c1c0240700c9003071070644038440c1c00714a0303001180020311480e03110001d0320768600c00701e1078881c030500c65019084441c5013019203403000380c1543c0c040b8440906c0b550810700d10b0040030025811945050700c0c49000000d105462022041e19100103c880b82c00222040181d070707480220b0808a51740103007181a000b10f40219241d13041c034081641d00d0001420441c01d000300a020840e06030341e00f5580505441d07060f1001da8044144035000c2e403815004010090010303074240c01034a5404040d51000c0d60041c2004115020039405050a40854204c080781c1403150301b1140004010034011080d00c9500c514480e00000d203184591115401c40d2a054040c242030342c83c000040014642c1007014010070181110200960304103000303243c4420819800040002020000040c081e40c024061030b40e40d81140c804440e640c40010000034443d40c0072003c1d0074851120000d503041c2c5410030301d4500c401610180c4800c00800e050000c43e05050802620101c010345d21a1501e07407200b0449441ca034000c00b0803 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 431463714 1250 431462464 431462483
    0x10306020d050f061e041d0a031806020a241a0f120304031e08030a090c32060d0204060819020a090e070306031a040515060f131503 58
    0x60300e80381c100381c881c0607000c030074645402c00c10f01c4003550b6400014407469104001120071076807803402140c0640488010030003508214603d9140448001c10320701d40c198429074500781441101c0a524000240c0340c0502001070348000d41c041c1c0090406e600301911107000e8035002c1003001807001070340e05032191003100d00c0503040030103955440c40c10600461000304108a0b45181f4201034040c01550324001c80c400980108881d00103e000c00b188018100710b2103400c0035000d5130302e28101110724040d20f000107044039003810050300007c1600c2c603400e1002101c80805501410b2003180003400c029a42c8403400154000820000414000814401000100383d00d032644038a902d0480110b802c1c3c0260340300c44410581c01003020200c0071b503005810700140c0c0d2000079451800c0c0c540c0301044001f0902900010100a801d80c81c01442841240006100394422012140554504044050282400d0700c0d00b0341c00c00100c0f48121030b21b16022040600c100604000002c600044440d40d210481240c2d0080d252000c8 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 431464964 1250 431463714 431463727
    0x30c03060f0c020d0203070305160219080c04090b06010324060f020f070302060a050307030b040c05070b06010c05210f0f0c19020a06030e190615060206040b0f040c0e01030602 77
    0x11140280d00e4030740068006800c1300c00100d4006500c9108901008080000c0000c200041c01d05024106100f550054042c16015401c80301c840010b01040c040c1203c9446140d03401e091500c4c26005130a000c030781c0648107411584403e801036014064507181c2e03039141c1310b00c46141d980303040c24224600b00420090b80c507200c4010b88050007034106403107030541040907005280288050b03180c540c111450b04c513243c54000d036259a0b0050840080650000c4542c0c820b0800030101c0030f855006018150040c01000120f4064440c00d005407241c04000d14001c2240c0c00c40c96612100710f11400d0750711007107256102a9131525203c05900481c0354050b81c5002c0d0600c10200e6003114203001000310b00c0095103078600913141e442e40d5030005000c0581a201d200d00305500c411409000c0981403000c84000c980b41d8060340314072840d45c40c095002e007030b660380e684114060800000541130b1000440c07502898001d0301c401c0464880e041070440c440130040c030940d01c800c40090001085500c02a40a0003103000f80c80041e190a03 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 431466214 1250 431464964 431464991
    0x2210606100504030209011a13270b03060115020a140706020607112107021e011107030b0103062a020d030f0501080c01210c0c0c0504050c0d020d06030c0306 69
    0x20340141d02504025041c441400140ca92604070380c15500042050064110440c032481da0754030485c00292440c5142c10400210f21300325000c503020041c140403800304107045015100003202d85100f0801d502d548520010855518004011075901040c0d01c1514042c844944036a2410384c00c10b80344050542c07005000f0013007594140702c0d65800440500d00a1044001100402d540301c0041026030f521008a000b00ca4040118400b120416a400b9091190001400c0620503c181e0185081400b0965007034101c281d0041c0030404400fa607601141c3d41001781d08544485001303280c5230313002c040310740c4400c9071000c0500d880c0e034040d44640c41658010f00d81c1c442c074664010192440072030f019810f0b03400e2a006104a400c040340d01d01094500b0703e000002c000f4403894503594174282e6003070301031018504248144099409000404014082e41000040903542c41c10302040322412600740e10b61020502c60100d00d10415001001d103290300c0180465015183d40b103e60b100210744c0c0c011507096640700301010550 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 431467464 1250 431466214 431466229
    0x1f0807030c0504090b041e0213020306030607050a0c0b06040209180108010c02190212100c26071403090a0606060c051603020609060a1b0c0f08070b0f030402210606 72
    0x705000c0d141403018400c4c1e582c402003a4200944000c000000017010b1f00050085584d61400e160f80040140b46c8490f400302e0180e00079442691694000e0084100041a840c001c0702210711142070350361088042d54854840c2d0003411000750141d54480c0e000c01ca45001586c82c0d170840100402404910949540350032421821201076040314400c0d90004040c07180001450080700e030b5456016100110387d48035113141749007007400541d1480b81840c40c0c00301850500d54440418100110555010750000300d540341c62181200c400c60310000043e40b800c400001100c40d41c405160841d00081c101c070b2000515030703112015152580c2060340000c3c4081c0d860310900c00700b0040c040442a1101c241d0b0742150840d0045005846001030040c022a4002449425284510081c0d1030914041d049580c0d14106031419119046941c0304049410441d030502192403000030482000f26a8000c840c0ba05c0c280208401540030f4000070005d0f81d101200d41c610038500101c0c4800340f1400c81594028004520b494410400d54 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 431468714 1250 431467464 431467469
    0x4020f0d020c190b0114030109060c02010b0a0801060f0909020d080412021e1509060d06180c020d020c150c1501241202032208030703141504051f0807030c 68
    0x5111881d505040468030354108141544c81b2078115680c103074000c4022031301402030342000a041c24585072a041003aa410b5111614040c0201c484840450342c6810302400d0b542d0b2030091004150008a00308880620ba600122200b44081c0c01c02e00c100070507403600141c2d90000e070711442900c2107551125045141c90030040405a0ba140101d24052450402045080402c100301140401d40000e90b840b65640720300c03d0307601c124101601800410388175048440885050741c081d66010742000d10074072000e800030070b80840901031503000341a0540381c20104503c0d5086200700c0400484104498681c519080c800c0b90501c1da075601c0c058400d9450a07502405100700c0d8201e4a807400c1c001c50b8402451584084002c004000301c040150b229101d40380c40700c2c0e850806018100030036910780c0c0c0761420054010007544c4202542d4404022008160b841d84088a000f02c03440c800d010020101444c0714a0103610458001d806442c0c0050300341c100e40000341e40589160802c0c0e10580c0090030401c01c00c000403502401 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 431469964 1250 431468714 431468743
    0x40b030a0f0e0a022e050c0f0d08040f02040f05160e01030204050303040909080c06090f06060405070c120e0603010b12130309120f05100501032001020d0e04020f0d020c 74
    0x4010080ba00d494151080300284036540d04007480e403090f1010595004803860201002e401c0c2c081c1c2d000d010f401c50f07020f40c05121190064040c1c00b4841500441d21480302c0e40952900082d40d40d8a503600c0540045882040f68070642c0d510309005004074901c945031180c200450300708420241d03840003030200802030820714109401004107010076200032040d6400c0b01c220071804a002183c41c07500320b81500408155a00911441c403c00c40e4003440050070750909901d01c4166155134440740c003480107a42c82141e040010504102400d00090f406000300f4000400134640500e00e4803240300000c0d0311707a10030391280c0914100840c4100540c04581215a0481c0541044c164040419580640607040ba4403035228960f40a9280c03000b80110443d81c0c2d40341b43d50080c03c0d00c000c5161858568000d00c000c0c0401c2c4c40241859000307120101100780c12044903401600208291204000100d8440c211840c110350800e0b001d10000f002c042c481c1c005400c00240d04070001d0703110018000d205282881446070080b = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 431471214 1250 431469964 431469971
    0x1e09030706020304030323070e1009031b0e160905060a17040b0720190c030b070503010f0b0a120e0f0a0807050d0f09030b270c091b040e090a08040b030a0f 68
    0xc03001c1c2c100c60843d001d54070903540f0382b00449401d1403d580d010280e03070003e04500c0960800c100c6541d90002400207403442c2c4030f210070845e11111030308880da4407031801e40c00104003100c030309002c2480d1100150195408074984410740b14008420100003200655044500081d81c205005440350010440d1101c20240b804030b501042c050304d15580e03a040103c1c48004480301c0c44620200b40b0280400540c043c581009102940341001900100654001d1240c449503d040c01004034141c0110012103190507200d56030f09940c2291410300900070080720404445030311a035070900801c1d803014810411024040d003005502c07043d0505001d4200400503c5007400c100516017848106a0400c82140c00c0d00d4100c03603030108903076400c00b07000580c4820340c840c9061090a5000c0c0498240c0024111038070b50b200751b4405420381c4a000e013801e5518400500000384a00c05e00080c0310600d0710700115a8451094000c841940300d4545880d8001d902c1a0000e4981503000020040200303003900811502d81c00c413200c1003 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 431472464 1250 431471214 431471221
    0x30405012d031407020114040209091c080403090501090e07110f07030812070206060a06111501081606022808090603071206080a0f0311010b0604090b04050f1e09030706020304030323 80
    0x88080010048c0001e200d0482500854a0010100000c08859014420703411545001c84000350400f01d00b160110006030806101107000c0d4030072141401203d0030394140b07501c141c88011084d01c6c00c041c480103600c1240b0520600d141c5418041040c04000c0d8054103d4581ea400c012841c03055025008102106540c4a04280107a58949000ba001100c040d0324110684a10b621042c41c2440c062204003588100000d0010a0808020a8000f0f0110102c0400c621142d95284180e0b00c8028034003804100800ba41005e6645060643d80c03606014030507c0c1c02447e14007139500007002ca41050356401c00140c00400500008502841b54101601c800001000c60018560303c00c148044100802820007810292440c1c9118003500100380e480c000030b089a448507100c0080e4401800c600c0b64081c826070400c804600c00151130100640246101c160224070703408001111503a080002e80000303140d204c01c02c06d0002250191020398000d034441d07500865010b60007031101900c0038803000415500f100c02000c0c03 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 431473714 1250 431472464 431472491
    0xb15040504140f0708040602040e0106050c0d18170a050735031c0b0a0602060a0c0513090908070c03080304021203270319110a0f0602030405012d0314070201 69
    0x20303e50300007181e00e03000c03000d41c0d40d44c0b41c40c101a0149502c420707104881600082583c40d00100500480e00110080b034080c1d80e9210422a140c0c1412809280451102442440186d0b2050910921069814219001d103105136580ca460120380341e010710600550101800c0f8800104104c88440315007800126010a00c02c0684a480384203030100d01034262001d40155042e0441030b088069040c01c01000244c03d0b80e07483c0b00c00303505c4074400c13500018160b2900f8610101d041c0100143c9840035402c15400040605000c199401005002416140f00c8424020480040c0044405c040651311a17030003252a03080034418004031a40d0804c00080c2c0c0c0d00140b048034441581c130f940400c4a11100902000b40300c1078070b00840c2c1050800300c40740c189c510b144a000c800b44001c2c80d1301a41d020105481d445015692440c402002046a010b4040140c0041108000c03c0d80302d000000b90710380c031205240c2540e2000c2203910880c5c00d80516043c012907210f24505180901100005a108009000070b04c0070391022500b = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 431474820 1106 431473714 431473741
    0x70918050114061c080d020a020c06040305071e0e041b23030c06040501050a0509130e0d08010501090803070b1e010e10060311030f04060b1504050414 66
    0x3880c132440d10500200540d4201e05480d041010300018500039500c00c80b08042180301d0321103d01c040c2d0f502d075030007040110f105000418030b16150091200b0780d044000d07100d403200003220504018810b078290500341d200342c0c0b20a2080403005503060f80321016016030400781c017142000010800100d1203140d20381c2014822000c41d00351041710300410000384110701496000a400348002c0c034138240508090000868002c00c6071400d0b1140103618012201c040988448540c41801a40c2a95800c05081800340000b031818081d00c609003c40c0740d40d24414400b00801202d0513000040071089000d8203003281007034484e220f01c0556560140c242d103121040e00c20f0034280590310400a0090300a100740400c1c0d40100b05403500315031780c818030041f04010040c0240ca40d1a2510074042140d81c60704030080154140e480c5d0a43c450303007084180b1040340c10f1aa03200958510440c11b2099440d002030 = true := by decide +kernel

theorem cover : BRFrame.Cov 431294964 431474820 := by
  have h0 := BRFrame.cov_init 431294964
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431294964 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431294964 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431294964 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431294964 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431294964 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431294964 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431294964 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431294964 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431294964 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431294964 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431294964 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431294964 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431294964 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431294964 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431294964 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431294964 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431294964 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431294964 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431294964 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431294964 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431294964 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431294964 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431294964 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431294964 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431294964 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431294964 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431294964 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431294964 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431294964 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431294964 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431294964 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431294964 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431294964 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431294964 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431294964 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431294964 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431294964 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431294964 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431294964 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431294964 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431294964 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431294964 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431294964 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431294964 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431294964 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431294964 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431294964 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431294964 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431294964 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431294964 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431294964 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431294964 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431294964 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431294964 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431294964 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431294964 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431294964 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431294964 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431294964 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431294964 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431294964 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431294964 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431294964 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431294964 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431294964 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431294964 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431294964 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431294964 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431294964 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431294964 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431294964 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431294964 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431294964 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431294964 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431294964 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431294964 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431294964 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431294964 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431294964 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431294964 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431294964 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431294964 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431294964 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431294964 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431294964 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431294964 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431294964 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431294964 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431294964 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431294964 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431294964 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431294964 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431294964 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431294964 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431294964 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431294964 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431294964 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431294964 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431294964 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431294964 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431294964 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431294964 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431294964 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431294964 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431294964 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431294964 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431294964 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431294964 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431294964 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431294964 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431294964 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431294964 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431294964 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431294964 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431294964 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431294964 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431294964 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431294964 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431294964 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431294964 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431294964 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431294964 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431294964 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431294964 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431294964 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431294964 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431294964 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431294964 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431294964 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431294964 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431294964 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431294964 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431294964 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431294964 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431294964 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431294964 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431294964 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431294964 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431294964 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431294964 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431294964 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431294964 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431294964 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431294964 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 431294964 ≤ n) (h2 : n < 431474820) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
