-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2863
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T07:58:17.923896+00:00
-- url     : https://prove2.me/submissions/889dde17-f67d-4052-8f52-a37ae816a040

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 514748201 ≤ n < 514928057 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 514749451 1250 514748201 514748263
    0x8010c051204080d14010f05090a0207020f091b04030c090f0b10120b061210060507030807140c01090c210f02010e01050c150402210c09180609 63
    0x2400690308102449400880c000c5090700009214144c00081d000490841c030024180a100c3c09038080e510302181c58400300035a0600c504d40070f50022400b04111316041c2540c1c00958460a1880500e0054028000003800a4039095101040b00300e44141252074a84d2071510310b061901a000e044520790820200c94801001d81c000c482c003010008143c00700e0006c480100302e940300701411032069882e40351001080e030750322414000c0980301c0c108880c0040301c0c540700c80005090070050703020104020040100c0320120382c0c08402103410410714500f6441c10b40c03d80e5244000c1d0300426141d84250b5207014080c508011009450900301c1d0702019920040c0001303458088040782c42c240015010405003e1404010340c0305501c032444400c4141030060070719401ca040c56103460b4401803001c64404081c01448254603041509002a400400a0b01e0a0074441d946803510b0707000780e20006005030101408240401900a52402c43c4400281118414030f0b020b4207030b0380d4030704860001600b28000031005042c2119 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 514750701 1250 514749451 514749457
    0x201150b090a0e13200f040203100e01080a0302010c05030c030c0307050f12010504050903040828140d08061f0c0302010b131b08010609061d0d0f1103031801080603010f05070908010c05 81
    0x200424101c1c1b5008454280406036100400c00205024209804a03070420110030042c00390035028004c0505515501e4003a007102c01c8124003505200c410700c100104101c414045951060f5100c80c15600c0e61680642a00c0d03e002e09154000c000c2e0303000c65960840f18030340306818100c0c2c408607014040c0d034813008034940d2280f050340660704550704666101901e224030f01c1c0500301d6445a4800c0182e0007091500c40c5aa82d04082d180d283c040c3c1c024100c2900c410b588418602d8005c00111112041c140c15402101803410106200c3c105008102004505140c000e500450000344003030f040e4082c0010941500300144007005010010313100004009134510b11800641d4161403154807510021414028103031001007955107485148240c0e03d0300c400e9035864030046034160074424a140c1030140d020b880d03c181c4041000c0c0081d402a4001d01c154807156071403034071284044d042800c0042c410b864800201b800740c0103806003151143e00308018401c80c0ba602041c10001c45880f070008000e05080000c0441d141c1c8 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 514751951 1250 514750701 514750763
    0x30c1e0b060a060f050d0b0307080d02100c0201060f03031206031b050a0b0903060727060509031c0f1d03070b070219060206040305030702150f06040c0201150b090a0e13 74
    0xd0042c41b980080150550110401000050454403202d5440310756034036041c4644014401600450786c00d83c00b40c60b035130181c40304061203400244051800c0c0f030130708440411700c0d01c4081d081000c1c0d04e0300340e400008140d10540c099500300441010010001c60100e06c0e01070240301d07071405903444080025410a0200035a24030800c001c0242441d505c0e149d400300c17103e000801d40d030b03400d0249032466400b100505c8942030008281546400303440c0d0b2412810103040a40c564505140a800c81c000c0019403075016000050400484c2448401c0000b000c404079011440c1031812509445122000b15000485202800b4028402c44d55511071a0b025106065003000c1d1b841100056880a808200060b0180d4051a80220944100c0b8204c00003a050759041a0064440314030038503040c021301c085801c4c54066189001002d00080c0001c1c4a4250481d40e06100c506c145d034920140410006d11950f1071580e110018000001900c0440c21b040a2503124001d920b502101e04c100242603e030311840c215240c1100103 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 514753201 1250 514751951 514751957
    0x41e0818030a0b010510050f0a090512061e0c0913060906051203030103060902061606090201020c06040b041a0c070b0931090618081c02090d030c1e0b060a060f 70
    0x80d1741781005000d602e0040c00c0304041404014400071041541c0c400c00741035202c0e4a90342c0c400d1560f01d04000d1000100441814007603035003080b002c101c5400324035520f80030007005140140b46556952802c0c48641d00ae202d801c0c07503200d00700c40d000740303008241500800c090703401070041003016680d0360080001081c40b0a4038403180d50001d20040020480070751200d400d840c006003200c0d01e0601003d5a06643e02c40108c0102d030312075540e01e0320006650341080300690101c42940c40c0751900c0c4c100000103490b07020300e2090280c410000150700131010f20030415a0100340044084511107030701d9201c1c5102507004124114090412014070540c000040306101001800f103030030080c000803203009108041c19416100740d0f00c0c83c1c0c540c0c0100300f8803910952404003460181c0c2c00305480e52100034010340011941c00f106195a40140444000f65840300c1c001d40901d503260410302d40f90803062070440c1280c0f0b8000d200c240d400201c540010107009d20202da180c402c000849440021030307118402a02c403048003003410000 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 514754451 1250 514753201 514753223
    0xc070e040f0b130803010e1005152514071814060d060b0303030c0a03050c09032509020409020403060b030d0e120c06030702030a081003050c0108041e0818030a 70
    0x300b24511100c03900800070403200c242c00b64a40c4c07154182a4400c1e800b1008004d0060100004200c491002c040030b024125000d4089030700000d82011340e07004580440152a4040c01c0d05150841c50b040455900f0b540003001d06040401d0304d41440e1601c04902c11801803240e0030041d070071440111711403061900301e101100700c0d0380e03100c9109010845840404c2241c4503030b600c403007082c9a9038041001d54400c0b550340b0f0500d940d8409400b801002d850002e4103a96410301e003400f014410741e402003110b0b03000703004403a610940c0201d1264040c500d01025800b5080c81d9100041c0450450004e80040c415640103102c14055202e19500b415601d02002045c480002c0b0141d540e12807500d0900c680d00f44103800303081100c00d1504100300044681d0300a494107000359000080341e030440340c1c0014019900160800d1100759541c03440c2c4400c1d4a45a5192045041106060000b070801107070181c035041444204200c0403541c113891400400d075a2281d0403811050a1200b0102801d00d40000c00380542a8000c42a002d = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 514755701 1250 514754451 514754453
    0x405010801090b0409020406150e091005010e03031603030b0f01020d120e01020904110703030510030804031e0b1e011e0311030703080a08010e06040608060f041e080c070e040f 77
    0x402004084403055209461740310359030143c0c4d900d008610140c403a045c202088001c10a80242000c990b0200a034020302c2d40c10100314044401c1940c040480d44203003040311140c002203001a08521510381c8004440000c40c1d5883c007415416071008640c0c1c0c41c1a0b804004da58411720042e6603c101c00443d00c0001a1071000c040032901071134002d4080c1c40c1c05000058108034407400050150351000d282401060740106a8200381a850300032150424000e0704425a0541035440b081c29030703c03d41c00b018050420180b02c1809119004545404294100c1508001400c000c0b541c2107091001104c1000204906d200119207100b0151440d20080140f2212440705071841c0e4400c000c0d840c184000c1d5606005004002022a00e907070024200a4034a65a00740d0642c1021001100d00002a0485020b10300d8a81e060011010002c0c5c4642c00c4050100742c2c0701c89955514050030b0b8400591240d0000b031002c45440020800b43c60042c06c0081080ca0585403820780329203803410f0701c00d022030703000c1c00761102407001030 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 514756951 1250 514755701 514755719
    0x40f09060605030919020a090c121107170702010504030c060f021501060917120c0d030e030a0c1515091e0902010c03110f060411120703030806060c0f010905210405010801 75
    0x1440d800c2c400b601f41e015595071451140200c541d07488900001c280040c00c8910211018441d40100210810328641072207031949842c00c80710b88081c0051720101000540c8019603000e2010354006607400b49200f0880c031f455620051201220f0320303191000d48201440701907407200c04510141610340c903a031143c070b416182442d03424080c3d1610440d180c0034028854032a0071440b4100c010a40200300b0401807010b480c0041d002030845404a0201e80d00c0d80040c401062078913440400340c01c1c1e65802110080c42904450407110040100c1040c02042d0100c803000000c1c5481e0304c2d00800804130f0300d104e081144c2c0c400010840242d4150070342c000e0016129036488800a4040e0310060b038124071030001c40d0302e80b10007107100344d00d4643d050b101542c1c4031035541d0303141660349807591280c8803604100d0043d00034589581d4001e03000700000303000c1074445c060118401035400810032109000d031315000000d0000071401e04000d9100c503081c0001003444481c9554401c1c42070600001c503011240107950b4550342c3d0780790541c28 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 514758201 1250 514756951 514756993
    0x1b080c0a03021b0109030206181212370b0a051f05070b0f060a06051206060a030e03070b0a05070f05032a1c0e0f0304170102040b040f090606050309 65
    0x4841140b0f02d9400302c0880824403980b0009442900101080e00380270b10040385400d4240241c42d4160303c243c45008604416006991007440c0e0144c8440c8a0b0301c0381400c048a0403032808642c0381104801864014043e2070044010f01103030000302c108030444041041c4400d0300005d0040c5900b1040020b8240da07491000d20b00360341609200d2414504110660b42c440c4010310043d41d01c007110000020901825240110310000104442d0401910b0b04804143e48a04014001c0c2000e01c107800104401c1c007502d000c0e421000d140c94044c03003541d0340c0b80303e28034040d075600100761020619689000d002500c0940510200d20b4040d01d00c0e151242103a4400d12012140c4581103050340440b0602451524074101110141202018000381400159842d040c92012140074004a030142d0740302d03c11060b260131740801128141d41c4845070860f014003054102c0e501900c03441d88980643c1f41d0000c1d00285411401c03102c0030544140ca50140b0000d503a50100f140c46000c181c90b040002d40050300281c404040181003 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 514759451 1250 514758201 514758217
    0x30822050c13020c030304142811060c070b0403120306081513020909032110060302030a0b1009031104090b0a0b041407020d0e03060f0c0f070501060303031b080c0a0302 74
    0x5440d01392031044503810340c3c10944081340c0924640090f100684030601036121074454002e901c00c3c8500c1c4005100c5400415607401510300000320041d011152078040403688a00540c00455803300c0d034580c0302d18540e5115200945880126030040d83c95140700740642c4040365441c10080103a80210303505001503240c0a0400b5420701030184003100140c8400104178401d030700c0ca070042c603220b5580d0050003200310643c4080f10402d400b02c0080185080c50303545a401a50514540161a50340354410340c001425665211640070043c00249180958402c10b400240c0780701d00ca40c101525010020320091304c00070f540080000000c507000441c284c00720380c06540803080c024408107000c480c02201d0702c140241600c00e003005800c22002040000e0300710f0b2205031804402d80007441607140076603111003038134809480c101031031b00006042200d8211140680380c4268029000b003112542c1c0b40f90190042070109405680072080d52081042e4a00a042c00c030321686010240510380300345504114000d5210b004 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 514760701 1250 514759451 514759489
    0x5280624020c04050705030a0b030d0f0c02041d0601050109060201150302041e050a150b030c03040f1a09160501020309010905040f06090f020702030f030f0415090b07030822050c 78
    0x114611103650f803800380c140681110703255613550341451280e8806076407061a5190103035006c151210300082d030003017005031039000504d86801e0303041c400d10000300540b041c02c041803e038401098880402000201d1382074101e4600b40c0758a985207903510010790130b90b00b14209101c1c120754100720030070250402d50030420a104103002d00102d0025495803580031903030242c0d840d40600e603482e08510041030b4604030100c050704242d4116800d6252551098209101c01480100307004200c030101d40410015086d1080d0440b03441c44028054504001c0999803080640d4840f805030790b5111002405500102c102c844165040e529000480c1c1030030140800b4101d0b082d40028150b540e01000202c0c845030b803090b085110240040542d480805004151501c10001c40c1e410b002e0300100b1007210f40c09400002c41f000c03161700180002d00104414820740d03030001c040c1c0c03140d07080440000344101016407260340d0500c22080c9401801c01d940208504558500641034000c00d43e501003541c1c0714941c13800900001e892403181c8 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 514761951 1250 514760701 514760713
    0x60d05061504060e0a060915140402090f030d05030709090e0c0118151706090106170c0d110703030c09051302031915060206010b03160806010c060528062402 69
    0xa600144c0200304650020b041030341c4003814000440300b03000d90000780196288194503d81042c0104004069488200740728a500182884461700c50300507103216502c0080a0703a809800381c2c0030242c80c941c0100c1700000000d803031a50200300d201c05803103034a42d403d00d00d00080c081507120f80c00640d4200300b110401802c000c40100d001030a109142500c00200407540c0d10f20342002e24000e461581c0300e40c06800503220301d103080c0040c810940e2181d10205c0c080c100864503a0b482c2c5030712a462025101c2d4210000256040142800c1848001c0d401484240c2c4a40d804010010b440003045400d401140202070b070203520901c98080026854019607045410201e200301020542c105800858610b140d0b00b600458485104100040e014484c5e20700500c490507441d4690318203014a08030400c0c3c1c8000300d200b4492180080341050b44200b1070024513590100c81000030b418460603d03422511040d0b2525242040f40480300840c50040c01058100d803401e507031940041c19004d0f0288540c014030140c40003140f00e46 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 514763201 1250 514761951 514761959
    0x100f0f020c121e0606090c160206040e1518060d020102010e030d1e05090a06090f02041508010c030218090603030d06180501050d0201020d0311040305031908060d0506150406 76
    0x101406040300e044041c002c200720610248000f61044000c4011562a00004100304a81c0c54a124440d800800700704465561000e19610b4040c1c2002541d02941025020401003031403807041403824010442c081745906240c0c0034508020410300403002c80c0045500340b1020408c00d0130900402d0500c1e41c414000440c400c2c1d0342c1666203146410201400c40425114144a03d00c00100c025013110025418801d11182c40c08d004a0f80c1e48100300d28008204c030b50b0320f038040414042601c1801c0c032034550080042c018081d0207211030309480b9035030003045919403a101341c60051700d0207442183e44402151902d00754019201c0e04001a00c14010100c58150104001c1c0d65000202c5200d41c2000d000c55414004000e061200300f06d0484c4d01c1600260f0003800030440100242c5e800140f6003482018902d80440c0940c44a1011141c5004d164802081072201049004200315a0300704c245548049645541041d40c03400304120080d00040806072003a0081d44c0415001070b88120480041400604081116503070b03 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 514764451 1250 514763201 514763209
    0x3031a060304060c1e09031203020903030a090807090b0d1502120405070306050705040b0316030f090501090b0a02040e0f07020a0c0306050906060301050c0d020309010905071d06100f0f020c 83
    0x860b400c45500740c2c1e507820805210303000300b1135602403140700700000880c038652540500441d0660001500d118410790f610f0918920030340446036120340260540352142005036026000e281c60340500d80e168003c1e03c80200b00b604e40c0348205000e0fa1402050f07001000102e44900403010360102c04000000d8081050390441000046641e0003984108010550030340385040500896801a00c5001044006c00c402c014a0099005481d000300c0003096460a684500c2c0c0300b90024050f80c1c103141101412f000c1c0110a1003010f51052115600a9004d502a59600c554000880c0305500424070707030106010200b1003400344a4003c40d441090f5004075076028080c1c0d2512000345800341d204585141d00e84003000742912051000c1500300c40150028081ea0a001c12038012038004c480d0060300e2580e02200140c0d24030025000300600c1608070050b90265601c5070714841c849140306c0c404442100c210004980c45007030050802c18021042c0c1d81f000d514100425040f900413490b000f441e02180308200380c10f429a55 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 514765701 1250 514764451 514764457
    0x150b0406052805090613031203090614090706081009021803010c02010c0503240406090b0108010f18050612060c0309190209161e05070201030e0307020d03031a06 71
    0x1281d19003503101c144661000d041481502e4100601600320360002c030042d50824260b5034a0881200d0403900c42d80381c82040c90000180780d0000d00440d200070b407004405c68056000c114401d01400c070500000100c6450360050200c181e07100e01903a407181e00104141403050760000d030082020144000d1190303844a0714400e90b04003c00042c20b03031a0320124082a80790910400f060141e04c0d000901032104558005422030000504d51346802c0307100d540c507810b1000000301603001841d00038010850661140825802044102002c80c0840c1d031a40000c64400001c44148048461a0410500413030340080014050300c07010b402943c006070303000945a011001446a030344114024220a41c9900e0151411843c1400c003042d102c4070407808402d5100507071150030146502840681000d04410211a0300f03d50100003482000d622002c110170b110b8059620130020005207000b603806000c500c24982c00907445c0c0c030860100a5010110141120000303000e90002d070351560340e0a2100072015440350225250f94 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 514766951 1250 514765701 514765709
    0xa0b100503010e10380a0819060b060408010e010501030618052109060d0e1002070816020d080403050a0c170319050904180611030405070b0d020d06030f0b0714040603150b04 76
    0x145049001e05d0442c01d00d221200c0040100800411400701038144000038050741c99030140541f82c5500002c1c481c8e0312580111002480d03c01c0081080322400c480075402000e0a0104566450508001c02504110b0094901003150050094081c4040b40c11111300c504062940d11844100140040d0020b503035404040c0910510360b071400301e603654440080714140702044640603015407041c04000081007459056541150600740e040300d00030034500001d07403a0315031030700000c00300840003402204102020486d41d48880c8100e00d040d01e102e450700c249003d2480015090b001035403052041502541c1e1700141d01c00f1501882c182030307141c101c01001150036035040501c6401c8510130583c02900f0007845d1f1050340484c00340421900d0071070a19640722a1034000c20f00c0303038644150700800e6524000a069040310102c682034941003000345e40e2450401c50001c5c4480013500c00c001c0b0003000419031400384110611030107800e0912443e15007000c03410b074010a440d0003200003101c0d142c035005c00c000781024000c0000d8 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 514768201 1250 514766951 514767041
    0x302071a010b1c05011202040902030102130815060102030a120b0a1502030c10020f04060c080408060a09030807021c0c0f05010c0c051e2d0a0b100503010e10 69
    0x100b00000030300c2482d54007070f40301020280c0b500b00108100003440107a414641e0341110080740c0101035000081c0a4020304070709010900c824180060000c4001503403060b4010b1540348050a65a11001a41c482c042c080e040404107400e140c210201c80255400120b08481c000d25410525840e0724182006400d0514070002607480010240d0b42c4c440c00f00b140e40c40a13803000506514003001000640306134000d40c4150700c240f0804055601c01c101880040c2d4029000d098101d501519103900f1391005400e00000a502041079030011034556071011882508010304440800c441c5040014100c40416800005503452101002c003500050b60078042e407a5029442e50781c0c405103180c00c1c182141405010074160b1015043d00c00c0f0510090000b0520300d105c01031740800d507801d064200041c9001070030008603450041c0190b1211408001c200503106e809000483d420304031590b2200281402c81d64810360068456009001d51050300c400360700401d40d0300311004060504d040b1054150024030290604a2500d = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 514769451 1250 514768201 514768207
    0xf080a02030a29011b120305072006040b070c0506061c02030106140f2e0504080610090608030f0f03090f06090d021209061c0e0a06050402040e0a120302071a010b 71
    0x641c2d21240c140480446107104035685c00440d41c90000094007020034605041d1030b200000c4002d40a0a140c2c0c1210602c00c0c0526401c481c5092915100c60302110202c030b86614250119410910501680e5511a17000e0001c0c245629602c0c00c0011502002c0c2c02c181041d14020402001618280036480041ca84001c80d400359912010800c4085076900d080e4501990070902e2010034024040c81c001c2080603c54002d4507a40d816500031100c0d8429070300701407034134410300040c01120041032640604503201031204002c8152141c08454030f0348286004490701c04030500c44040301200003002942c10045d442d04442401024010041c1404022601c103601d03034011041c5440110b40502022800000c4440314034540440000040c9150203000a00c01d01c821407101d58503d03003040340c0d005410000d505000c40f0003440d51032511030003819040300c049010b64140101c51400f090001032210071540d02c00082e00d210903121100324025044a00c0544030b403640100038289200400c8801406004020a0340341c6d = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 514770701 1250 514769451 514769531
    0x11042301090506040c050304030e0303040902120f07090f0e06040605031f0e0d0f0f03090605010f08100b010c0f0f080403061a0315060409051006081c0f080a02030a 72
    0x70889400402180c0100c0c100109140707001d602400700d0344d1241e8541841e803181d02240c0b01103891402142c1000301150320004900404250604446d3300c55a00541100500d59401200316001d052a00c40c00300070003000c81051001c3d190f44000c481e8440303009440042d502d035641000920b0440980030300c10340303034100040380342c284001e034040c85210f40550b81c01881124400c5800521140701601c0403010400c2924499500b0307482a04403a94040e00210301b400256100d90358400d00714802d108601681c400d01c8001c0403041418010300742402c2d8141c4402d01d60500c55146e04407002c030110802c4030b131600c450414000180b01c0f140548003840c05203400045e8824402500941c2c20200107803203100340d1000003a03030036142107aa5070b6540b10b00141d0b0081904a82454480e103007049949a00541c141848404100100300258218170440c1440d0a007074011700d8000151071151600110000143c0140005549901107030015174000c800540c001a86503044000c10725041080c0b80100c18120080704558 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 514771951 1250 514770701 514770719
    0x91802090612060a060c080301050607060b0405011707120b0703051e040501090c0b0705060103020f03101d0114010e070c02011106040f0c060207050913030915030e100209030a11042301 81
    0x30000d0105428100246c64694541000d14001403117a5841804000b40344420002345410140e55504003410174052075841c2c3e0f0b01c5202c2c0d164060003110300c0e8400c0046c0061030042d00d060750b5000e160800410700c0903803504034084002e441d00815180b104101c070180007102e0503984408038807542c0100d000285004003480c04c00014032580c0c0c00010045e4042c4101c030003080001c1035250450307074100e4602000c810890301003401c142100c10a034610740e180818038004602c2c4010344130b180c107402030002c011006201d070ba503000c5000c003070103003081c89095040020160741c0074151049049005040c210065403641002620703002044138112600044038001c042040141c0070813901030300542c006000c60794244004224200d81c01010440d0403507044411400381405814048094240305001c1000007890f0000135010b071000c440d0301da04500c80c261404a002902d4801ea0b08101d6004000e00720034001d90700c0e541011108110341a9000da540c0c00c81d8a59451070720004210325900d050403040a603d045d03811 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 514773201 1250 514771951 514771969
    0x804060206281a190512010e1e0a0b0106030b03070608191104080607210603032106050a140a08030703080420030d03050a0c0c0309180209061206 64
    0x505007951507074541c491000159941103000107003000c80010060351001018600c2c24428081941004900b64001030b40f44140708900c0a481c0150341b20b10044c4400500c01e42260f4400c004590f40750030440622045618a840000c4c101264800304c845040b0203483c1d45204800c2a07008c1c0002c00d82e075205180080c102401518010019810440b8040c036101603000c0c041c0701800040b00a4503a42d20014001c20010019a0040e1010504840b01c61916040241c0000400c942301d09111900040e0b41c0441500b5008240a0f070b9070550394000c0404000c1031040c030b114280c0000d030741e1850f2140404640790700c896260100601c441d03084144c02d28424020f02c41b00520320f810072080c80c3c008129210103c0c0d001200c15801a6000c6400080f114000e0a107224a0306d400d0b0240358035004602d880c0150366850f4003c10300440091008020030803440c1c03007d40303007070201c258001c0108803e44000c009408004018040b1085540e40151402c40d0040020701142e0000d800c3e41c1200004006204641c2820085 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 514774451 1250 514773201 514773211
    0xf0201111006060c1b210501090b0a05060a080303060d0b0604090f0c06030c0801050f060a14070818030f0a0305091203040902031f180203100b0c2b05031f030507030804060206 77
    0xa48002c50704000c2450314000c80388030400c07290f07000121b44070208002507000403041c4d5080b0185452504121003200c0c054102030b16198840e100180700400c0d481c20202c2124041c0c0401817145940541c1d0b60384044c41c0d8507000346660340c40750341d420003000800c030720280c046040c40c4110000ea04403410600e0240890780c010345d00d8810410b04034014001511204c00810b03440303604448440e122914142c04564030074002030403110110001c52240100034800b4041c20700c0e07070411020301040c2c8028005240c1d5850300c0302c2e80080c4562102c440c540110340128020310440001070302100907000611038491039a48140d000b5421240c2c0001044007480c3c01d04640d5007515075281c2c4c500105403a207410b0201d6040303000d1640041983c00804114810340210b031410040428600c0251201091020f890f1141c80300700d03010900500c1c1e00142481104c5500b8148800c3c1110344030320f400c503101c124a6582600301340d140c03640c4003610b0305400300109404100500007907124000840c3d0315410103c00078240400504 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 514775701 1250 514774451 514774493
    0x1e02090c041409060d05030406230703050904050c2511030c060a081f0306090c05240c121c0c05270102010f150509130f0201111006060c 60
    0xa1281c0c0450b252045407100040f070301483c154603001d001608a00030788400038464440010001070355a005a0444a04080601000500001e110400b90740c0d00c241c01d0000c0c0051010440407040d40340c66400282c01003890302c0e5950500d07000400c48000716803074901c40203a0300085107c001c01c0203007005403d400380b60150040c1c01a884080c0120344136002d914000e00a120305c3c0000070f9200501e803070115034841c684415075400d0f650760f82800802801c2d04d103019201c10042c0b540106090410802c170300c8000e402a500074050400c02c4088000382d402440c02520280101c0340c1980031401c0500251002c114401d03c4a070300c0220780c0c2100821242d50545d00414271209005c01600c2e103000d07034501c92114440050704100d001e0305071300407401480d0042c4011500d80c40c1c9220032440000c2c1e201e0801c240c9030140d03071000071074985411078103002d03104080080c03480c0d2650900324010b51081070003810844a1034211001d05000e0140402599000c0e0032800011340400302a005101c42103048030341403d00c01c1c0c = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 514776951 1250 514775701 514775707
    0x4062d030512250f060e060108030d02180a0e100807030b04060e0f0a0605091b060711060d051f121a130c090c020d180608040f1e02090c 60
    0x565516201d40d480d40152036800c101080c080c440802940085890001003416001c3d00c520b80d2800d075205850010040d41d216103008025800307000002003642c180c901740720055042c150603590400c041d600c0440c1384440706843d1002a8070644903402c1c0342014048601e0040020b01e44901d020900c840c01e580303c0411580b1545003000441d0003500c0c4070b500305800030b00203d0810300c0c4800262034400e00240d91003861140b0203c1100780649540083d000b84101da0a540704102100700c0450950712a44003e0380c0207604200c4440003e0b00c07058100c40d03c040c050520360074100720502807011200e0884941c455201e032018160030840d40d001c89040902111111404c0c41b030f280d0f03256441090904030200c1801420f03c00424402c1420501c00c2d082c107644080311034415511007000710043c2880034903100240c894141510681801080f2000d00f915180400708074131031514a0031a0303000000f60003a200d101003500d01c4c50200394030b4050310b000c0b0450280d0450b1204194414044a80802049420500014 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 514778201 1250 514776951 514776953
    0x6031403070c03020906060403120c0209070e01050412061506020f060606120a0504080c160312020d0f0e1f020109050c0618060705151e010b04031a0703090204062d03 73
    0x40100805403501034a803a9181d0742d40f2030101f9442e1007030380c00c0544044040002000181d40c001c42c0704a40900c03e480041c2a512110803c2d6001e144400d446808140c040c8403d20078041d4a10031040d140e405207801160002800202214008540d000750700141c10034212800e21a4080201d55000b040c281c0790589022414030b0000c21058024000b4111640c4a90100701408500005d031020350100200351810740c1c02260720703c0313140e00891100322103031804044042c01e62800443d000c43c118401d511041050140014201d0322641c03d0880c80341d010015415100b43c480d02c005184c2914101d9800005400055040a40c5130102c440111072003500100481c22104401c1c045c0a015400c0070b0703500c0350b12110f15180c8907080c141d07085201039564603c101041010511040b0701d10703460f141d40c000c001c0940d803103c980d8521442a404007801c2802c50151100021001000e034a9004200386400184402d0741d6002070143c542903404607148004181c1c00015840c0d140b001d0324001c00c0d10f074410004131851 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 514779451 1250 514778201 514778213
    0xc0e010f0f050108070c0c05090a0f06050a030308062b06240302010e01140405120c090a020c0c270906071d0d080f041701020703140a09050f12100603140307 69
    0x5d020a081007030641c140c030100080440307440098100180550b0107845e200307006800500000800c9854141410000141424034441002c01d40c3d8140d030700c1201e10b136a48010300a40e03108241900c1056039462544410003c1100070310340349580704410100b0003400340f0002c01c111003d402c00480b100b08002c401000180e800205420ba001002c0c2000000f51384161003613030f0a0b001c2c0b0390240d5000900c1d07034500007400308041802d50102404031080110f507120612a0b4003280545541c241c0254480101000107213000101c00801c92402d5074100014109070125245084c4242c0d1b440e80b056205c8410311190a80011010642e400021110290708110000050078070304100001342003800d0004a002c1040e0b0288212005401d201e0858800301003041000e034003d52101d1801c1e1700080c0c00500b82c00800ca40310f0201c940a806a80c4d403840c8050400003045000c002c43c49195600020319400c1c003250020502040c1d0200420341c03c001403051860500f4000da0500010301071407a0000c100d00000903207 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 514780701 1250 514779451 514779467
    0xb0106050a030e010b181816060305100e1b0c0d0206071b02010c2a060507060609020903060a0f0e0f0f071707060c0606031a0604110307090b13030c0e010f0f0501 71
    0xf403003220300c01b83c1c4505a02e08400b034590605410380340101c0109182c003e01a4425070b080325030542c4e04025590791651164413a860354080d500b40d440180c004101d214044c8440300295004c0c014100c3d25101203541824603104880f0f600d4005600890208000c10350002048208842d03120002d03064401c443d800200884d0503540018a801846102e8200305840300414a40168a41c402d01a00035180c45021f8032a8101c080110780e440c0c207000c80822441001e00aa400000002c0d00a0219885211502c0c01602410010422166a0f600307624440300c401c000329420700320080068260030740c2d0610441d083c83c2c0c1c2c9410005074034821010b080203290b800112794003164105d180c0f201c076075101c4c3e00d00540500b1041e80040c2c19100d1600c0150300b24118243c0050240c10200ca0800240f031201c0d110090f90301040f00c03241e000c038048035070800400740044000c024222800c07020a626035100da07200810b46029810500c02e00300345000500c60641100b051700050400351003020304507444d100c0000c00e190 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 514781951 1250 514780701 514780729
    0x5010c031b0815150c010b2b1a0a0c030b061224060a0f0320040504090804030507030c030302060f060f060a03150b03060a1d040f08070b0106050a030e010b 68
    0x20044000040d1019000040c18045480003131100701150384076040c0345a1600b1800c4030320019460000b1044007840d0600d03084100340c503c440641e0303011207030145860b41030140310025900390300c00544440100c0b10640b8118861041c85100107001c040c003110040845068011481c042d441c1000344500e070040014403658402c0030b241d41d42400411004226000e09201c0311030301c1d085803010804d0000c0c5504910350b1940e8841c01d40c1d00b048031506c0c0041450000da41e6580401d01c4640401052000c2d041a40098008a010780c0c00701e0b190982d81d0b40c5551409030a64402d03181412404010700400d581403080b5604409400445e586600780400011814070078010041d1180400068804607640240c01044005241e0880344480a65a5462103602d5004945071031095000d50f201140310400c401c95a800340c10f5892040a090365695100c038540180c240060307030b0781c29050141c1d81c0002d288100b2a8040c100c250340c1c050721014a000054151400348003030304001d07418119130b809103444120410080c2 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 514783201 1250 514781951 514781957
    0x905031e040e062106040501050a05091501030305130506040e06030c090405060a05060d14010506030d090b030a15050d080a090906082d07030f020909030c1c03230405010c031b 77
    0x3180c0c00a000d07032144c00301803c1d82c42603004038001c000510006501003842441180000d10850395403002e02c4e0b86860b45c500404040b000c01c0c6c0014408240710700d018280c8400c038000d401201d191104001107080d00a170784040026042c4070200183c4e400c007403020101115040c0e0710705416081c140e40312521201e00038600d8484594079000954103956480954414a40018054083c100351240880c00780070704842e018001d109a00760362002c0c07403140c503504084941e49a021130564462000030409445c2e604800c220a01c0300c000d0100e81a034800c2d000c0d0090907c10b02c0d4096403074021034405851003000754040300400d450511704001031312001c1150b00142d1a404540003900041a0800b01d84115100c0700d044140710b0b950010042246180078494168000c85001d041da03511903100c29541c2c402d00b410000340b42c008640403040c2000111040b40000d0543c18082041e96440001c26600b45044c4080d10084582806100503c0000c1c8140c1c1804040d0780782c00d00180c06489048440f5034014007071030b020 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 514784451 1250 514783201 514783219
    0xa08011d06090a112407020301050f07050a0c1403040b03010f080d0e01030902241e040303021e03070b0a09060b03010c08010512010f0c0e0901090603020112050414010905031e040e06 80
    0x2a07a03040c1c0701022420a0810000c2c0c1d00044003068500c039041b0400890080d8a4440481d607841d41d040d040a10509203650b8407882c001d851a0100c61700c0f485030300e00b10348099043c822141c401400f0f00140c405882c0e8201e55035102d45c075080114821054980c80f1500310b40250307641070310b110760000659425000a08002c203203554103101041d0707407000140070b1401d00e0044a02c0c0038240d680000c010b000d43c034403400c0c0c0300d0303080c1c00806040d108134412407100a01582c080c4880f0b0151f055401c01000c20348808405490130240c1035256031030403600031207400f4507040e0340d1002201084054426180b55aa065000f0401e5541c1100040e040b61018080d1a00c2103d2150f800204d002c0c0942101c000002c0c1d00b4002d005650711200040c00d00280310740b40d60300c00e0a10100105a070001c6210f010126501655141c0e00a040c03582101c008020180c4140c42d2401c000816000c900400d008450070a481007005680e1140c580e00701508040402550300d60181c401c210411003107903241500f90308108201c45400e4 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 514785701 1250 514784451 514784483
    0x161d0904062a02070f0b2104150c0801030c06031a01120207080c070302010905152a0a0506010807090e0606151e070c0923150a08011d06090a 62
    0x30440040a01c02d01c1c4000840c000d88000d281e020541400702c0c0c41d041070210403651103280c842480d02440107801c443c03071207044910000181c84481143c01c24000c5030904001d060115402082da050b02d0007040116610400400030080b0314500307170009100b03a25080007103000080030b5441c0700c03040340c002d107041106400c148800010240d04a80c86036078414038096071440d85030f40d440e40b10f244c54031041e40810045580005d1500700441044000802803440a151600e0340618010745180080341f084154810030680181d02c404004429080303004000a0002d985005076140c03400100ba00301d02945800c0420b0300ca9120000503000c3c0d00144111202c00505035081103810300e500450110350482e248450034002c034500058020000c190242c03504400b0305481c1c0e5140c80544041c00380c11403501502001404c44c1240b080d020580126041016008011424002035020200c94000901d0390b5501d500b00154040005007600c1074aa00c0005416a40341c0802680e031110f1050740080c04007180114002 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 514786951 1250 514785701 514785731
    0x806010804030f021c020601090507110d0810150305190b030d050304052404030f09061b1b0603020c070503010b0102030a050309030409090c05090615030c070218161d090406 76
    0x1180b2400d51170fa00300c45d5000750b45c03070080d030701c5c80203100e0040b0f4a40303410b01150250b80701d8800800c40e500c114000b846400c850b0141210380e480010245409980094004510801004c0e000c0130303101456034001c206070030049251400c07040807a40141c4040e00e4144c10740c886031004600819a407510382800d54481e5120f09002c1e0a0820514403690f40004000040c62004040000361740541d000b40e0b10192220356069082c0c6100c401409110007042c0500d03180c48071005100d0b40718070560303c00e4190750b14000c030b122540128002c0710b0b000140403d03000320381d0102000e810003490f03008010884c020f016044410340040c2d200d00c506ea03d4002084000070010303c80708801c20458000f80304000d405c1080070000d04100004400e00d0180510960800020510524040307405402511a04c14494915200c05545d220940d01080e800c0b80c009002c4615401000c2c02c1584152041814285401c40c0183c19100285100c0c500316011001f041c5600302e0285984482054561060344a0030028948404000360 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 514788201 1250 514786951 514786963
    0xc3a2309130204030302060708011d0a110c060406021815040e0408070f050330010506160b0a20160602090d0b0a0c020c0609031c0c080301090504120806010804030f02 73
    0x1140503900000e0008105a40054014440c0000790364112450b41ca800d28241c4071901c0b07a40009400101000cc10b403d404690b07c0648001031803041503207041c005075030031403c0c460f0842e0240d07600355000c0b0320310050100354210301549890856030b41032052140d040d00c1e103582c080e17801404807000b070010000302000368400484440c40d8214900c3e1180c1c1c2d01518005680e9402002000320100e60130900c40c0d030305507280381c00c4407400b910040720030070503030901c0c2c10721a03240c12010444c0a03d2904104c3d04000c5804039203401c3c041c1d400d11030046841e1058408140136240d06138002c2807213403010072298465038030b00f5004036140c990040b8050380e142200310006015662000b40a001c0782580004d000b181340746940301c03861601c010740070303100d10a883c03108121850180c6446c280c0c16030000c010401d075042ca5000d420b418850241040124a60142c5030010650400d801211441e0703501c009010a2000706030b190b0400b8080c501d0700c030701a85000e4000030f0201401610050500200d11710303011281d4020b000c4 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 514789451 1250 514788201 514788229
    0x31104320303070c0306180b0415150609230306011a1b0d02010b0405131b1e060201052a0c0a050609010b040b0607080f0c3a2309 57
    0x480c0d0b20f402c0d0f03a003030520103c52248003c403110f43c82c01c40b45002c1600010148030704d1540005d08104280c1da1a224000c1000c0c542800030240d6986080b01031380c1a01209140d40a042c0b10f0342e03a00d1071981000c83c041d00010742180c81c1c00940c600c1201180d01580c00213403003415542103203145007140000081482c403600170701e1460310200e50540000c07c1e41e0240016404280e40c11a8001d001c0c5d80007042c14801107070030a4800030751094000701241c0200d60b100114034880c1e4091501e8000f080d5555110400c40300c0800c480c090400c2c81d9280403c2215424020300c0c2d080f50845000306407940e1b098410400420001400c403454070004118940a000d051010404694100c025a01540380001c5c0c0d42e0700800076008124422803a1541c0d5110600b040416640d07503d5201048a160069400c6c501325103802c00000751903144900c8200d4007002c000310a0807402c0140c0303002c074a880703250200708010384e8000c0001c48600b0000f0071140156840c44103554003081a01c448545540e8118803400b044a0348a0005 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 514790701 1250 514789451 514789453
    0x61c1104060e1c110112270b10030203061b04090501060905030d1803030c150f06090e0303040812060a0f06030c030c080915060a0504110d0b010807080109050c07060510060311043203 80
    0x100a002407c604800030008a11500c11400f0660740c4c0741d100e0081003958040030750190300c008d00144d912101190401c0d50200b20302a1070341041c0d500c19180c010b68009821100014110340020059403c082064081e400e91908002d04034018800450100c900d00340310240c10002c40100c45401d209502c1c41100c0c00c0500c8450038440720390110f4408028044034418449458a46034450035900d901100792406280c2c009400c41c50706540d901510301c8084040e00c015400f80c8100780002e030000285002c00002c005940300880d114a08410280403510703c0701480c0b00b8005001d041040c404400710300021044007801c0251103d8446c10046807078440590021500030740b034015240c440b0314048024100e02e001d8aa4103003ca610700c3da0045441c900141c0303015001c10b400380b0040c4541101500840d60111300208207604100054507600b05072541514803070803442c00e0341c1c402d201c49681400740d40302542005402615113403070300003001c501d404070b6800903203031400c1c201000035541102050a80312000c010 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 514791951 1250 514790701 514790741
    0x60c0118020f0402040621140702060a050f1e04060b03010e0f0708030901210b040c0509010207060206091506120106030c1e05061c1104060e1c110112 66
    0x385002145401240041c0d00c5a120480502c1c070310b00e0b160007200c0079110030f0313510600c004030000500e1903007101d2100d91030842c0c0d44030788241ea855241c0440048c850440c684c02002e89080440079041203420240079191214038003410046040c0d03941c40d68600c407401240034001e5035561410610010041c1450440e415400e0805032019500d0001c1c1c100d08581000c41a110380c1a80c0c0c0103ca0780c1c0e8850f80c001c0345c0c0030407056104480301d400ca00a036282e04941000d0046424180d901c00142107522801807040400c1e000300d22080316503410070807140541968001004581440c103402946c803034a21060070300440322200012a2a10f80b823402041000040009100283e00ca1906510200180c0030707a0303440c1c0c5030484040c408440004894012140050b064a00e859003003c035080d04810505182d42a103034580f540313a502211120002c10081a544c2e44040c40003415804001c00720f030080f914486003c0b480c11180012881300300c411407250301c013401e11a0480c0300f038895040181088210700e150103c0c0a03 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 514793201 1250 514791951 514791971
    0x31e0615030a0e062a04061e03060f0902041701050919060b0907090602060f0103021e0f0904060b1201050f01140a080607051201170d1407050a05010603050613120c02060c01 76
    0x15040c840c200b0203203a284900c50806110a1000d94017640c0710f00400500507239039203903408a170301320300f41280c504918020416588802501e030300030040d41d000c506125800601040520703918001d01c24140444d800900660410000141e07490802c00b07a0700b90ba50b0402c01315241040302c280c0c000c40300144060954005032501b00c0003d0660385082c850b00c0054001c800010713442c1d943c8081000d041e03c0d8010844882070a2200c031140c203094180c07141c3e9801c5040f59840e80c182e42e41d0484403030b1107203110315004104100e5000600001181c5000009042d80c104002d20100b1402d40e4501810b4030b0900304580c0103110a00000b07010f8103442d0303001d10300301e0148509100c9025840802045d8900944102000c0d0380d903621241c449d04000c11150110980100746603a040520400e480800301d031841c03030b1043c2000525129181031149400044510740c0d9248402c00810906000503580414400741250429401e911092501c0c40050302100402460242020456a0742d009541602e52500002c22a40c405 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 514794451 1250 514793201 514793221
    0xb0612010f05010e07090602070e0714120907140406030f02060a0306050d05010b1905030d03050c0c01020a031b0507020a0308090102100504030f0e1909200f031e0615030a0e06 77
    0x80e1144400500c045402140311400015400100e405580300e1070ac442e40d80c54021030b04150381462030301100c0000c20100c400e03c00604035072405055228040d006480c90030b0071134070202e15402c111070301a90403e0000c0000c9828001c002e4000c5030181e8100d81c2d01c0388403460440003400580c108503800207508041c481840340551140c010f581c016a00454400381291304d11151b075241d8454030794154802201c03442c0b480d20075000541c02204803102c40f41032444010200d400c0e80c00441404c000241e99810720006e1008040300d81d0a02e8000d810102e24040d166004144001d0242c0406054810001690700040c0d10030864501c220320080d40420690400303107001840881c4020b085400129107407a000244d15085c0b250000075025030314000100c1c1e2a00c001032001d0002c0f0003000340d079040d2640a0360b80c900121001094012080803007542d5038544002c0300d80710135108400910050400000708229034850010061851041c0c4d14850749aa0301d0803510805004645100041801450148411302070 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 514795701 1250 514794451 514794479
    0x909070819020f0901051b030f071112030901050304082b050708090c010e0f0405161103070308040b04061b050901020f010221040201200619090b0612010f0501 70
    0x910503514152010100c0720900030ba01820300480c2d100c86080000341c0c0190f00032001040c0c051540c109150035000e50f108142d0440d0440d06040b000000e00141210030000340c529070320805113044440100c041034048200b9620b00502d40780d01e050000000c04035090007660b00996110b042d0071140c0700d40c4820a1040c02140010320a4502143d50408010450b0356009290492040800b1300080050110b11b6004481c42d2101a08042e00034550010f01805c548403030103858483c40743c00d05010503044401500030a40100000c5900302074209100e00c1000952110b00907030020340003403851000d1b0f21103041840003400741c000c94202c58900d610150580c00d8114000c1c01258000360240ca01100308103184909038481d149401d0000201500103030a160280b042030b03500280189040900b00c50078030b4101c120100074081e501ca4a42c0000104141700340c504140e40080b98600c0010300c602449d03965081d030782000207041035106611914041c07060b0f010035403080c201e408458034103110b1940e6460052030802c4d = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 514796951 1250 514795701 514795711
    0xc01060b1801020303280f02070f1208040812330108010b04050a090e010e030c39010c21120509030f07030e030c0a170f0f100209030309090708 63
    0x40581c0d00342204079800842074902c9085504014140e52940c9000319101d644240303030107882c0e281d4810011007000c0b4248064100c944c030440d00149140c10900700307414801c43d014001e6081000c1c650410001a8a810a4a812031000c0c1403540301a214108446003c07800ba10600c1030401803440581c00d0040e1550b2040d100310801c2e240c41d0310760703600c075894244640705a005940e00700700d500c0d80801c010440c6a01c0703084007400c298000101441686202411544166036008166210300c000750a00a86003c10250a03495000008001c01c0d08650000c00d144802d0102e90511001d201c281c401e0000c1d14103039480d440c0d580084540300c0b91600318007610011a25a03800c0d202841c00e400075042c03007070000850b418003001c424250305020140e0360485140c0c510300c05407a014040d0f0078030741c00d050f02c8444179000603207140749444a001c3d1a2841381450304c0c80250001e0780c25402640340c490004004108240a600001c90140e59406e0307401c0403e00d58030801074601c0e0410444000c000c0070690051800d1f0042c = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 514798201 1250 514796951 514796977
    0x140921060f0604020c07060e06300705160204181202030a0e0f0a030206030406090b0a050411010305160e030f0f01021306030506030c060715050c031614040306110c01060b 75
    0x9515241d09010882c000e890804140e617001030001c0c040c080c001e040c150030a410050a0340d16181c0440900b2046c041d1203001c0e000c0004000482070342b000e01009078039921450347e2801e80e08096140c1c0501d81004c00d42c020290007541e881044080e0388100c0b0540e20b08207900300143c203500c1c0b80110f80003981c3e6400031390808009058492070440304d107480140001151030040038130300301724103540030421035030f001401c11220b40c0c1e96018000d0006115210302c40c0f280b441c009002a603031a107420400d4035100a040d100d0304040c81e01d0104101303280e400000c00c0303103000603103406528184210003003454103441d81d0180e0542d2103200100c0d41d201d0015002000081d40714901c030003a241d07403050709800382c2d6000e0301c680e40c0c0750304642414011410407034080d0100c2e602610042d010000c0121a0030704540b401e84004071045000401c00401000d42c00a50620080910b0b10b83d9106d01d423203003401d00c54080c5000c01440c50fa00c448104d8040d603118002e4a90860144008100c05540c407180b17008668003a031489040 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 514799451 1250 514798201 514798231
    0x2071e0f05120c1204120611043615060f02010b0612150d0c05101403040b040b06030705090402210d0206040201030f1803110115060917030a14092106 66
    0x3d440d042130156001c40302c00c00c20565185501e50356400c040c28022040c844010340c180070004841507a15410307140460304075a110b0880c00c10308410701c1040004c120300c181710350604651400f8810300031088412590031b81741100f10112144403ca0142c5000754401d0341c44140032809031402c58800115600400890035000d02500e01403041c84500c5e1060304015018000d4020100600d040c0342484035100c4840e45400c00c00f0703488503161081c01c0e0300306890a88071003540900304010001e014440a070003140c11170040120b545400000383c44044001d0000b806100044000c282e0a20b4034101c0310003280c01907003540c100c0300031303520002d594010446041e40020700380400040101030601c25105610344c513500c000d1070200241c400391010300c00c00107010075175903841e41900e651240342d01d402d802410307003503486550703041c5010350500d0b10042400110fa1160010022142d40c00d130050040c04241c1200c1c04190307229545400050101030454071000074030740703140322040340784580030401c80c0c810710b0b801c502118 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 514800701 1250 514799451 514799473
    0xc02131406030f0604020105190c0f03020f01110f09060706060f0605070302060f1303050310080303160323130c0521190b070c050c030d0c03021002071e0f05120c 71
    0x544c1e60015903001c0d0116008010785000c500440c04600306940d8103040c98034a4080076507a800448a40c8070003034006030041d104100d0591070a020384260700380a40e11240c101004032a00007001c0c403c2807810340c4540c20001384142005804c0d0041001000c0a404910f10300c0e40d2060084c10f59404a4004c07801401283c0004a64540c103c80407401010311881c1b1100404560740c05940a0340040c001300090204031400140d0b00c08100010342c4201024402c68520303c0305444080c00755400070706680300c4150810079050115652201c199845a091000804102200d05059900348002d420854010411076401d4103410605806041c4448000b021a034028500c40c50007420705056000c000c00c8402010003140d1018442c401070009240140143c400c00f010010020380381800d0740b03800e0b07800700303803c038041c1420b0540602020500084424042d0b20302641130303887d880003660101d0003070b8804190405002c20700c6030310784000b244079510104450715402d1000310803141b90407581001c41e0500c00c00610903 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 514801951 1250 514800701 514800703
    0x306061809050c1e1201063803130c0807061214010308030a0e010914160602030306040f06121407092c0f1029100c02131406030f 57
    0x141ca00d5420402030105803102c401004410003003c0781041d84030780400783c04810ba0b076440807401505041c0f040005246d42c500b100d00600014202c03c042e210011101d80b04405020b44095440ea145200c0c1c8403540c0c0b5518000000c1c021506010090051114010b000c622000d00003281001e961150312160900401281005c0940703d401d0509044004c2200c0100000f0b90480080c0d44c100c820030401269071400d007816103084455040c030590b00800307541c0091442d10b9043c0001e044129104c85143e40241c10840045e540f84800707000b650003540e4034180a59a06030b141e01c00d00c094032400c1255a00040070b428040c030000c1e06030b40e181c101385c0140000000c101c0703113501c00c001150302440311801d01c80c60010a40d0740a480b460a001303071070340a0f245030741007017440500585410741d401c2c00c0d000a2111280030840d91901c2881046040420103c200d080142e5a9110a4200b5900c600e042003110045101060940010020050100b800c3c800780b0b800c0c7c801c140d001c0c248034030802d404507088221101c2c02e031 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 514803201 1250 514801951 514801961
    0x1501050d08090f01030e0f0102040302090709060c0f0c0308040915060206062409060a0804050f01050c07020909070512070509100617091203040803060f0901031502130b0403060618 79
    0x1c000c0803041040b40340a040140e940500040141800a40c00c040102c2060510802410050a0365030005061045140044100f0b812407060302e0411110341c200500038104a40040001e403000049006440402c15891000700286500411054641d0b640747ea0a0014041c9414100401501c4900104940f4800614280b20301001050640290704100444aa9121050702403a030b00d0400c200302c10154403400001e01c203201d4260f640000614150074041c2c24540320070b859030581d904010034005c01a0400041e40e00d0550112180302d0103498902c00c852400c1d4003a8031660b0030125261a14140030804550f00d41141c10945240c3c0742035655900d4504012858007a00000c21418215021241040c1181c00d60182ca031800b01c6151a110200b00d03a1079403c100d0b02160480c100108202d42807e068183c0d40701c6071003c0c0c0710019a54103594800260701400170352002116404107004d0001484000040018410000c119580b0764403410315001401d15030141180c1c4e0010120b01c109180c00521070 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 514804451 1250 514803201 514803203
    0x3010c08061c050d110709020304050d0909020703020304050f01030f050408040f08070e2a07080d0b0d1208060f0904050604060510030f12051c15060516111f021501050d 74
    0x281012113004242a0740c030b1a00c002c0c04220f03521410101080103a070510055000b035014800404d0000d02a940c0106030b0641e54100f1400d09005010000009400100b41d43c1900c00031030703481c5804041c0500481c014100c1394902000c0b0b03420001070009100c0c1c14030003007080e100017800d454086516410307510f035a0842c922401c2c0303c00520800141c24020b40c403400341c003c0440c0d0171426541c1c840c0d0701c10031425900b04060540da0124001101c00d024420752264400d80d100603194240c016040340c0b44d01050050302000030052001070000541c10b50b40d8102200e0b5000c074018403140302e0b41003608205076a00e404540844400d480c09020403407034850400c0d60011658045111492034400b50b44503c09500c5040c861005d2160500a900001804c0d2030301c1030f00828101400200344440c1e02c81c2c5d41c942000b071b52110060140800400c4c1d03c030000c0d000309140d003d4000a9080e0b0f118a0000804e603100c82034481d1429849000480e81c028942c0031a030000d0341165159030b40241d03600e503800c0049246407140 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 514805701 1250 514804451 514804453
    0x703030e16090b030312010308070503190f0e09010b1b1009060e0d180b0c0709020304031e0302040b04140a120c170d080411041b09210804060804050c03010c08061c05 73
    0x400010340307804022b00b0718506c580143c3e0306000c03480729400c011640020540000c58894024500050350015408020032011520640c05502d000c805500038401c044016882da00f09003400a440300042260b00e01740c011026082080a406080c02d4000740303c41400404c4a00961541d0030000344280c0c00c842c0841188042d00c0c91540c900549001c0e260b00c1000341490a000340c800008000d9150700c00355104601039240c00001200480401d0452102c0c8c1500009140c03050000344009460310302540c003a03640d03204c48912410103c0001544914850740300261a44410043c041080740f00c205820480301030070440304c15130f40d030103100d9501c80319084881c00c005a0f10100040c040340d850810082d40a001400000d502c90109884074151441504076001150004400300180c0d03c2d090001000789071001d11050942c2c030103541300f00c014031561003a902004400e0010a080c01400e001070303d08010018020403111201410203405000221605807190f0400041501c103000a0035110404a81c010 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 514806951 1250 514805701 514805737
    0x9030901020606090411100507020112050c1b1005070908060f061507031b2012030a0807020709020304061a0d020f190801050a14060a0e01030303020703030e16090b0303 74
    0x414007412130780061040c1c0f100d0083e4030002645896a81c00144807901d19038420b6621040c900024180a4032030049040030f610300810400b2103c01b10013500c0c00d100d440e510302d103880d12040d04200c1c9814003c2d403030380924038070f0041486903058100c0c0301780c01250031034410795486a0f500e40e99148440011070341207402c180200d000c10b80518080e001050340f248207013030050501801ca602d02c0106d54056400711190710180c100b1038460799007c2040c0c441c01c0c8044030041104a41402c2003500c2c0d00400c0c03203000c28001c0910115140da8002d10620000d4407016008645038545814000058181a000e1a500826a1407040300f0ba080c020111503180707401902c0028060300c0441070040c841c0c459100c07940d61510070703540403901c81c10038001c06019103108040802d2481c0245051000503070040d000034810001c03240304011001049000f181100c0c0c1500380161201001d08007900504003061002016002d9802d90108e15008400d81009070740d504107040000780084000e01d41d0781c0c0b24505141a803c8040 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 514808201 1250 514806951 514806961
    0xb031c0c02040b21160f08250503030c030a09090603031e0e040903110106050102071508130606170d0806060909130c1508160516020111070b0d05090309010206 70
    0x550003c0c1800e80c0c0240c0741c05050304465084a91500000c400e1a10940250300101440000c51041030040c090181710b00010b145058001a0b03500381c848035042d05070103011040181d214074038241d413000b0b200c060306407039565002e484990b4899000858500100e8454a0080b8441c100e603c02c032401c0c0e07a4103480708a0060329150840308003040c5600002d0802021541c0c507040303601c1703e01845052500ca42c98000350b20600000003030075101141c10450456104100400001f00c56080100301a881070904040b50386692100910806000201030003039400c2c00400030b02407904190070031100f8109810303102c040010b40011216a031058420a610400500812a851030520440ea42000e1114905210060346a03100301424410f075121950034403541d504200400c1e0008003040e13101e00310111008200c0c2030345602a0590140307585801449400b107208500716401407840321a48003d40044561003580c404080c082a4000320740065168100808510000300000a442c02408143c010b131071180d0720 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 514809451 1250 514808201 514808209
    0x50406060f110712020402070f05100b0a1a030402120a08040f06080a05010f050402180d1202100510030314120a02030a0606030e060a0203130c030b01050f030c09010b0a1404090b031c0c02 82
    0x4050b0094270001c51088200c0000b6008200402404036008000b06580041300d003000103202d042e6111000030f0740c03095000901280700e42c08480d44254100c81294504d4000c02031185010400040100760800009011031601d0700007c0801c1160010350700c0c0340040e91a2069441501c40a115003240070b0b00d00c54044c0030910b4103401414102490400881400696400240d02d520602c1c00c241c0b10041203c000c0224180d0600c10700c80444010003050000e800d0040301c881141403584030180c02c10400e56030700100e062980049581038500c45080c0302141c10f110601d04000c0d84207541400300036140000028040e03029001e031442c18600c030009010b49680380c0c4088130195200a20f02c4c114501c52a25800000f0302d9200030001850081d00550015810305007841032582c3c2c44c2c16114032a07407110700034000035591440c035241515100d61080c1d85800c645501901d0007a0901c51340c10f1034800104010500580c240c0c400440060201e0481da1404900700d5003188a095005142c0d00080010b0520005410 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 514810701 1250 514809451 514809457
    0x3070504022b02040608060307031a07050d0c020730080d15060504080705010329010e0a080c0306070f02100519050a020304060e03040b090103050c04050406060f110712020402 77
    0x2903045415101407940941c402d40c2880d140c8000300c040b941c08a018040a80c0c00b000090b4010380680052401d1410354644034624108403040e10b50702841d00e400a8807803032168090b2006560384c503d051006580492000c0e4898125008a403c400e10000101c0300603a0228004400d07039000840c4070401007215202e865496208444e801040c03600c0d4601d10300401136000c3c1c0b41b00106919500e450f10341c4d0400c8460341c200359569000504040c1400b4910150341e070000d000590030020b02001d00d00c85889040180d800945070a81c2c503501ca03442040000e041c03072010800c6170781c81d00c1c101c0603980f40b5542d06034156005030b000300c2c0350001a48a8800000c1c2c03d601c0d40d0003d9040070701a042c09181c000504064400c0c1c1341c080b01c404c0d4501c0c1c0c02105100c2008054040c11311518030b204043c40c2003034206401c0c1c005500800301240c0c100360704e4038041283c51401400b101c0240c0310242042c040759480790700183c600d12100c5801c10001c0c5004444881c2c4180100d1f010342900c030000e0b455110310343c80d0313000c00010390 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 514811951 1250 514810701 514810717
    0x30615151305090405060406060504020f0d020705070e1806090610030b07020708060103060219020106060e0f15040f081606202a010e0103060503060c0f0f0313200307050402 76
    0x9050101c08112555802d01d9944100e20450007841e052030546410010b40361142e015a0140e0f005101402c9040c021406690042c101c82c1001600e8803400c2c240145002c100b40d0140222500a005000c2c0c204484960385107a15007203801ca9034252600c0303414580d0faa038225a10741010100440c140006140b64900c16005401c504c100c50620382c694080d0b50400800780e000b01d82040c0d0004e40440318519140740d011141101d130000704481890000085c02c00c80b141c0d010303548142903444001540f41d48610301c02821955015101e5200c945030071403150521214007610445d40300e2400307141d103001d03084004802500d500d50b036200080d00c60f0101c180b0004103504015521401a10822103007070100800002c1003042c000f82c40f02c030100318503002401d8602c1a16071103040508110091002d500e0000355603401400700584c0c1d654075110b5511141d614040e02d6607000d010700c00001484100e007a01100051a140201c006401500710141075207208945114040d4040e040080700308910702c1c103a40981032603 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 514813201 1250 514811951 514811977
    0x110a0e1912080d02030c0409140712021e070507080c0913020d08071e030e030a03050f030403090f0906030303050f0127200408011113140105040308040603020903061515 74
    0x20f0310500404007641c0040b00c881c0c0b0210310208041205102c40d0003500c2864104101c0c4e5600c0c0d06204800811100201440d0b0b40c4180c0c0005041c000300090302c403003526042030aa00035440d0b49a80c501183c54484a108045451140c0c2c0c4290382e2902e80b240b01170b4026103860000b00018250b95003070040000900205503440e80040c0400383c041040c0e80a0b03240d03104548120b00000310400d00d4003400031000c1c0b40c1c0c501d0103a4012002c1c000001d0f001001c440c0b610018800f071607200e54861a0850b071500f02600000c0e40b6039404035000803c201140c0007842641c0c4207403000e00c19a620750b61501e007164030903ca01c403500a030710241039019038011807075090200031072000895400f11098111303241c0001080c24046154000a007001301d50740070303c034002081035400450780c80d000a503a28244000c80c40e000d80c0001000002e020040d50b8004c8048600541c0c0c42850140c032199101c00140081d0400c01c01d0314068052440000c500c0756014041d0880300e0801811145c0e0710750900c20402a5070442804c3e02c81d0 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 514814451 1250 514813201 514813207
    0x1060f230a050d05060a050106140412020a03050d11072408060a1e1706091507021c0504150f0207060c02030304030b1510110d0305070e04110a0e191208 67
    0x4980c40f400722010303000340100700510660410300c042100300d0303d051340013801304847c4000140f80d02c9500c10480d012500d8050095051074000d0001a00004056100500c2e0744105090012003680224103006002020002e44082e0359172180380420700c10542000c0b28103c0c0b814500e071a059030180e007413030b44c0105020b030680e8040ca0319182492134012890184070050f84070514108031203072211807000c041c3c6481001826540c1042c4c21525619000c501c4040d840e445c0d003c0c0040d2070305200304001042c803120850070701079200c1015400341046d44a400f6401d07400700c2034006c480e942801181e10310320308207035030b0b00500c1518506042203448a00c00071080703900d40820400040458006804240200007402d00c80300401002c1c070030002207000d40c0c2d01e100c00f40300180820501c403600205004000c0f6183d81400b0a2540d24208102e81306071480c00ca2980c010b2034400a079005c0e45840300501898080c0e526021111880a4108417400c800ba4502601e8a1400e20044c0040e40041c039111450034400c551740340c2 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 514815701 1250 514814451 514814459
    0x1e090513050f010e0d1b0209090a0f03170a090c050913021314160f1b0515061905030709090311060a0203060a120b0a0507021e03070501060f230a 64
    0x800c194000c41110000e0b134450a80e036010202c00e0040300c01c80500c07420050004c03c0821072610321101c0413100684a40e16032400941580f03000e00601103401d901038a074003060141461b000e04026005000030843c5c205000000fa5040b010f8400c0d110318680286c0007208691500080101540c1b004040000d032806030740c410350042e01c0e10303d10301940089420000c81c80340255140c0e10791940c2c0083c0359240b43c641010110240f15007012070003213045c01c540381c07000ca4408080ba46168100320301d40c00500910465036500c0302030089808150281200b02c03101d400d42014130f10601042000380c01019810780000300304100003000c41c0d0106204500c40c0c00c182c514801c40455040c180201140c0c01d0794030503000400c2044c42d203401080700029010300c0440408840e841c0d1984003805600a28010f0542d641e00c4c0400c008074020800f040240d5042040070300a4508c65030303216100e8200260886041d802c100740403501e4503d817080c1400761600b655642828226001d001943c00115034101c54008a022001203 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 514816951 1250 514815701 514815703
    0x3300806090f0631050702010b0d080304170f091008061008043320090103022208030711240f090a0b07030f090e01090b060d020706060f1e09051305 65
    0x100071404070307114110f5600704c04480b0040e910010200c600f103914200240f00e0351351700c4910300d01025400c2101a5100c2e640c601e03020200c03200c00c21200750240000f04068076690054802130085200a680030f91040d401c86405580c5100c094074603030340c008503100e00c0414075485540103d5105010301c00803c6102581c540a040d0402140545880000c40384006503903080d0340c3c000c9800c2c200d00903a0056004e00c00381491843ca0180b100c0d02c074101034000500c0d6290f0032b00d40c05900c0c501c905412a4140c5543c1d02c00b045030307603580840401c9581c802e4a400190091612500c060f55411061014403030b4800300d00d10032500c980c00140000140d80e01444507102c0340e00e40040b0301e030103445901c2c0c90981d42c190b1428044c100c10504880d401c10400c50603000c1c0801064040f084d411100107100124640302d1601c0014240d000b9024180640c901c0455204207008050300f00104459951a16442940e03e0708010448a07040f034122503030540c900f2808226203003565100941c400f80c00f0b1608070b1091a1643c483d = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 514818201 1250 514816951 514816999
    0x203070c05070b0a021c2007170601030b01030204090c030c0608010e01150207150c0b0a0203160908030a1b050d02010903020c040c02101503300806090f06 68
    0x40028190109040800104010000181c08a1843d041c10400b002a00940e10b1020645490a82c03140b04003403400d09004880300e03000d600c42640403100c00120078005503500d0283d44140380b0184208000503a1000340810f03101d051741e81160703540c140c1d030b800d6400f440003500c0e503900101e03107800102e1000404603005409110290000d0b91310590954034000d612640b0071810703000068210340124030b005040c2c0d000150340086450504005840d00c19454050f0741b416840d441c09080f12140b01d007004140000c035070055208040d0501070040500d040030085420300000c6c040c44200d9401048080c510f0342c003c03071064441c151009481200c0c00329a90b00c0f1401d10281d2403614015030346420850003010b80501102c0d03404502554104a96101031000a540d4910800b00503070b40d071b9442c0e20303490b282003559141c20084c6410240c4118117031a0ac8000e627010a10410041d52905561190301c3c3d01184984e01507800354000800440701e9440b280d501480e003200190882d0f41c8003e580110390314009450000c = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 514819451 1250 514818201 514818211
    0x1b030901021c14071101020409020d020405100c0f0f050c060c010207020f01080903040902070515070f080f0c0f09040605121b090615130302150301031209030c21060203 74
    0x160b16104110b2540b11400200040030034064280000a0319a00700749088580c0032086140ca000780b4442c51182500901c9250001c403107160002031400380010103a0000e1003181d03400d48a040d1501840741d01100c403000c5105005090051412080000c0b5240f0444aa03065029006580808500c03000080080d441582c4401c00343e5004100c04055203095151045690703000e007820105403914500090300c903c0786021f50300020380d0205210302882000c0001791203034800010b0340c41590a05501c058003c0101c0342804c0b002481c1000069150310514070440c1c0500b10400700c0f941002411500340906401040340d158106541e024001925516080722381c254025000103840d000300c07030aa50751002900c0c0d00707081c0d02581030a024000c03e610b038072410380740342020410250307140e8585034040c1c0c0d203604207030780060b5014051810180800c480c2400a40c102d9105c3c80419410451704501951121b02e40e11002d444114903010820041100e402c440c0520300c0c0c5032060415080c16603a540701280c200303540e = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 514820701 1250 514819451 514819453
    0xa0b031b0c0f07090c0318050303131a0403050310150207030311030d050c130506070b06010c23060a061e14030c0a0807080d11062809030e010e180406051b0309 70
    0x46640031681c0c25101d10700b03008002100840d0428800d448289c2e4070b200240407081c1103000300b21840e082c081e00075005c01c104031aa02907101c00d4100703410300800f5500701341c81001c00c0c0400c0100000e80c034890b101d00c0c030468060a80240c0143c80c91a242901d40394504444041580000c01c0391440b550128410030b84034040500c3c14036100c40d03000c1c0260b010b2080d150005400382808012800110b0210034549900940034646800c0d15181850f05004101100c1c0780044440d50804c003000500c0c4010031264400c00701c560b0108035403555032b52080c2d00c0809070760303201101210b41c0c801881804110006646003100103000c94400d801c40101284a2103050ba000c13410b03607007000c00148071802d0144040511030740d0511303050405100d074040740c6484000c060030740e50510103d410503003012001c503001580103000704da0b402c011300d00f03050901410009500391a1030014a07800409590380c5002d4605071007801032040b03814082c0c2d80365a107100c0100b0f0080c1068946d000045036403c0f002d4130380001140f00f0702c1018 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 514821951 1250 514820701 514820711
    0x6052d4014150103061d0a06050a0314010b1e040c020304170304031406101502011d030c1501150806030304090213081b0609130f020a09050a0b031b0c0f0709 69
    0x150000c02990100c0c2a20b50402d410700c03d08011a0161511001851507003400c8408541c5136030b5810b400a0110b50301558011881e02c0002050016101d144090000d0000c028442d503998001040400a013a0b070400305d110110032600010b03810158041c410b03840240c01280d241c15100c03800d142448104070f040362021f80c4001414000c009041e42c50701c1d1504036410090400d400d01c0d0f20361440340e213268000c070340340d0140c0e210703002e40018400d41040805042001001103001100c554941d140c0d4021540c030b031098868034502420301080c0820803030480d00040e8014482c86820786048844000140c9925418031092102080030490348c80202154965200300000070b80c50300d5501810701c942c8042e078028841e11000c03400c265481e00c0081311414102211400e2240d048084400c0c001d03d06a000d4030050351002c19080b0485802c2102c180c20b590003116016001c039581d01100b030051004075012030b9505c100c507241c2d810000d40038002e0005140c0400940309501c0b1500001c0d850311060383c5c800c0f42215114 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 514823201 1250 514821951 514821961
    0x7020a03020306010b092407290705040302120f030f28050406080108060c040b0306010215090705130b061b030f0a03020418020a0c02011206052d4014 66
    0xb00c0c20a47e1280b40c40c2c550480144801c0010f014036005024018105810440420f0080b401c240c119500100040d4481041c03420001300050842d001404100c1c01510300304c107100c0865000084040031400030000a44c0780080ca0300040b0002e80060f01c0c0b03803243d403d40d04451002180c42c03205d000e00b601c20a41d0b490340c503140b0b0081c0c000d1003000181c1c0b1440054001000b13000e80000050100e400b5541c0c00007085589031103000040340303003020002d02815072040601c24450706500105108003214012103000501900000c0800d0441e040e5000a030742c1b240080141c0da0400c485040e02c80300b48051201541d05000c0001c0031102c50758409580c1c030000a81c00a0141711288810701c18840c036a02d13403441181003080c0400e000c0d0a40303c0c41c41c400f9040c0100341800302c0301c191a0760050780c007400c0041c05180c0030410707031035101d0780c9609006801c04649100c0d103241b804908292614109110811a0030b40898903990b40c850164030040e080400e482d2a07005100c3c41c215454040d4090144081c070002c0b00b01d10f04 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 514824451 1250 514823201 514823209
    0xa0e070503011a010225061d060304062a0c0f06020c030d061a0306030a060b1507083a0506040f05040f02030c1e01031104080109050615040501030f030507020a03020306010b09 77
    0x40c0424284143c2c501e20340b4022040b6400001b0015030792203003020400b005880b40b18101d42603601c1071440c0e00180008c2080204501a04900740403001302e00000d04401c0380d030050b010400c25003210140000c41c000c2200d00440c10052403c8103d6000324801132400074140342c07080c1160b11200141c2180d6898420401154822110509040f070410111314114241100040d48a142045000d00041d458030002b08507a52844144140001054180c5a45144525000c2141d030008400c0c0d80181d141d900002c61000000301d2004800d0110074400d0829a02c5420010010400903209039041030f92607003007907244032036442864007907030103840102c0c110f000d940b041600d070141148406000744207124074100c44128040f25007040c0c54003420042401da800e00c1901c5881e00850707016050135030070040c01070700b800008641d4900911100304072481450781c01040c0001d4860a00c4010004051b20046402180c440c4010303100c881d2000308226182070f603e0f000207140540a801c05400030000080c01d8000303140c = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 514825701 1250 514824451 514824463
    0x12060117070803070201270b0a0903110402040501050a1b1a090c040b030309040c02191b0b0a02060a0f0915050115090f0302240d051503030c060a0e070503011a0102 72
    0x2112000398031346042580020010070041d40001c241c0b813001d07040c001c201c42c06010030030050018081010b0b12545031090042c0701c0f504512065403054500004100141021b0086800b55801070b10341a16181d0301060441e001c280011f04828810740e080329440000b41644508109840d401484960a08090554509002c0130143c00b41c4154900500704255440210a43d10082d0089800003050031500500b030f030500c40304509090702c0289443c400030802c000d0240d44202000021441e00f02a81c039a10807031850310401d81039401590008000404401c203079040300c02d0150300c042010a070121150795550420b40806040ea8030302e03480394010b0100e0541d1340261449120b04d460000c04151528041100b0314846000190184828920221113041002d403111461402681859a1070703108103070350383c01004c0541e504190f80615440c060342d44e05d80001503a282e01d003000c000d0601c42c0c46003080c40c001004d00155100c41c45c007034500c001175290f032b00388600da0822460115a90051030400002400e001c = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 514826951 1250 514825701 514825709
    0x90302040e06070806210a081206013605060a0806040b1e09060607120c020a09110a0c03090b0f120105090106200c04050403120c030c0516021206011707 67
    0x190001c1e081100f402c0e0301080041d0000801d403004c080c40c0c500744010143c1440030b042c011800d403141505960420050800518151070003510109440d254140112a0744640c1020b40f00075120403001c0310000560488111560007001c04448006992100401c1803600300c20101c40c080703103100c81008642d0a05008091403c1d03c00c84000d407820705050301c0d85001d407456486140c0074100f810f0004100ea19118102c603411900101003210043c1d07003142c002e28190320385c4022030007000c001200042c104800c1c01f03035910020b01c3e0040d00f42005d103491030032510801c5d129800d60400c494507400280c601c507914010540448440021070751006204200e030304190040c0d0000e4001c1103032030b0040143d140c0c40080c1440c2240a030030680c01300002105000e203808601801d03154890f02d440c0603c0101a04030b011010505c481c41001d0117010b50320403003030b02103980c80340420000c501708000020042c0543c401d82140380c0d1008148050004014461500c0c0807403d030040d91003494007158910101c201000490010 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 514828201 1250 514826951 514826953
    0x30501050f030a0b04110607080c12030709140102120c010c030608030910120b04180210030903091a040b0d020a1404051305040602121f0801050c16050f0706090302040e 74
    0xe8800200390b454644103000303050b05400030041000c0003140c01514405600040025440d0311050030b21270304a034803103c0003203982d1240c2c1a403642005003202c1030700d00c90140d40d11400401890600204003102c600e003d101d046006000f00c61340903250101c050903294a04d1700c0001400c1c1c1c0c0c40000642110800d40082520b41e10031300c2401c0301e503a07402c600d01c4110585d03407410005006d030300b51142018080030545980d104d818140601d941c0e00060700d8810066001301e46803046070010080a404035205004060b00080842d81c05000400703c45184030f0120100341d22451420b60b6501c00003c65800c036811050550390001901006d03168016405219494042c2006240510b0400010707482c058064840d00c0480c2c50f40b00140c18400349606070f40944442c401003a1291400c01c007802d1041e070000c150380c413178500594004504c0140520070140710b0030380000031601c2c0004120708444000a0b040301292039104060081c18140700038404e4100600e0a5200c0c00d10a81c02d520422090b2901c1074016a11 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 514829451 1250 514828201 514828219
    0x408041502030301081e0f030f0d06061b020f06130806041403030106090504110408030c060612071d09010207020a030c05010306211205040504020a110606030309090a0f06121203050105 81
    0x4001002c1400712000c11004901c480c0340d000c1d4160f8908060800f00740e0147d07800b011518581500e856401882d070341080c2001008840c0d190f0030b0588500c1c0407004004941c80040700060014100b00c0111100c60200428035030a040000951802210858005039502e41194044c0010441242d1060143c01c4480c4095421907050910007801e0041d14030410b8407490f19440e20040e103000080480e00500742c48002eaa65410042d0901503a820b0300360b8403540180c0300113080d011004404038000c0142c4423401000e01420000003050400d80e031002c0c243c0d4215540c00c006010042e6904000240254481e2100070242403505001400311080c030f6201e85484094034103075210b040c210309090902c5a0384551505906000e041080301c4da8001c40e0801030b00300384006007584d4000c0e00082030038a120860001c4400e00c0e9110418036440c2d0141e8900b40380c01041030f4020840400a54100700c21001c3c44040c001079403030751207480d80b10f030000e50316040d10281031782c0c0000001c41d5454060107014020139607048030 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 514830701 1250 514829451 514829459
    0x70504090f0b0709170102090a170a080315210c06160312063606050315251e1701050423010605130e0606030604090f06050408041502030301 62
    0xd004801c091005120840c030074000340007180151204005480e0a0400c5151644c200b17400c503000b0740c03003008554802d90580000290709980035001848014403980604410886a60382e07801a40021b0481c41c401e80ca0310b07010340b1240d15442040c44040707540c0b07004103c42805680300301c2d041803044150980240c0c1d04001c101d11080703003c040300d00f80d20b926140124403024000103410003007019410400d569045a044071003800c0a035810507000f54840316590000c454100700f010226142031041940540000b0024001d41d003200c100564024041001c01315254100c420000c030b844084041d00011494000440c542110303101c0c45100d4054642c106840d404140b2442038007018414400ca51145840703148030040d44400350104110300c1400071014850b544c6611002c2c009401c505030ae48807284a01000203181d00c40641c926000311805403580f45941c07110300500c005010028800c2d00d510030410544000503010381f0409210754050350f2040e031500e040a0304011441500303107141045510510041c0 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 514831951 1250 514830701 514830713
    0xc18040207060c17180a15020706090c0f0902070c0b130306050c1e0909010e15210f060705091302070b0a0f060605040b16021801030f06050c030112033e07050409 71
    0x4a10a401800611f60308444102d0301019124207403005000c42c1c100582c2034200000000c410003030307a03002c40c0e914211740d4079455010224002c500300a8941615400d0420007524080d0040c5403441802503a444041d072a40c4a00d402da0320180da001c0d03659000040c1994642005081c05c005c43c0002c1e583c0680f61481140c0013030240e105c103005810700080c0c114041550300d42c0140320a9803000014282c103603c1c3c810142d401034a42294602d00b0b030769002d80d8490740400740c0c0108129105103d5500c0b02c9003846401000d00000c1d2403441100c8012541c2088620081810681c075188030700e40309140031410300718132180142030f81e00300c0d4422000d010042c04248506182c00d0242c46d8064191410102060044c1c00000d81d1503003151031100692120740008003e00c103050315100000c40c010311061042e9203c80004003d184002d200d90880e2100c61041200028415144021030400c1d280040754081460519205400014105030340909400007094261071420310529000f003500700e1742005808140d490300 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 514833201 1250 514831951 514831963
    0x2707090e07080a0f090b0a0515011409240307091502070b070f0c0e10050114030a022128051b07050123041a0c18040207060c1718 57
    0x14009020700700b0002040e400389940718070000c0081c244144405046424003858080c01030714039100303c90400000a82c10700228a00f044540c6041c6d4030440c070000d064141c001c40c0d8002402d41548900e1000410781c217a1603030419420f00304026030405549061081c40a4074030000e40d4008105407064090900304980c01085c80c03411035a16076071141d541c05c20340ca0300080000a40000030401c5920780c00c0417a84c108917035021803091003810344d6016001d895030019540d6488503560900c1c00d690400c009400c0544580240c80f03000f0190383d420445070080161000d888034211191004160a040110200700c0d000703140c0e1505901d019003c000d541400c0780110305d808501254140d41d071a000440745d003040350952082241d5201001c0b0011211105d0080080044090b1030a4803100c2c0860360214081803030001590050003101c0000f4a8025101c50001c0007080d00d64441d80e0140e800c0c0034581c08240b26028400b0010190744c1c4203415031011403a00b520100000e422941003a940c00d01c0d0203514a000200e03 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 514834451 1250 514833201 514833211
    0x30e010623031c030b010c0c06050307080c040e01060c02040219210e070506090d0606031a0c090102060711160e0906090a1101120603060f06080f0d0c12020a022707090e 74
    0x2080f958178a100588814003d0007004104d00c24900380000c0e4a03600c040558050314841d81d480d080d54460340400d120354041c078052920b40050020040040301e025040480c030291001c0c00250034401140704220108104008082c0410441540350540f8240060740c124403110603002086518082a5140d644042c14015a801910005031112617039407040d51810130240d1110f02489041d44900c0d180e4409064841a450b4500050000c90f0101d40c501c8180e4011300303010303030007012a40c0d52003404a510485800344080603015894407103480898000000000d4030300720b0840c81c104d042c24251145480c50051524045030030140e840300009242c003030180810341d002d1919020381c15141c030501000f09000e0b44010308081c80c125083e050306106801c12002c5075000c1c07054a405400d0040e4161711401401428130024440d20340100000380280c000c465500c00728412240308041c40e60209000880900c4030851551015103003a41d070104001010380d00c00071138986103070311303902d4000c13031648076480908 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 514835701 1250 514834451 514834457
    0x1302041a0a031b030c120603030c0b0c0c0a0807020f0a030203030d020d02040e01060215010504020f040315020705031201170a03140c010b03070b040801050c031510030e010623031c 79
    0x60414425200303810005003d0300414405441c2c4825080140040200c1c51040022603649010524a04428400d12044a0701611001b1262a640e6143c0c0c11299005114034038000042c00321410040741084225a0244640c002543d50314140c010400c0580f217170090306224000c0c1103020700058a012058880c001d4107404056191445a01c030100640a160802c2c254481c3c0e04000081082d80001c44003040c9a01e10040d4071181d032117100b17210a0b80b1554000907020b040c00c0100f000054050131038800800d01c140801828080d8950314107085500600403d00c00c15191030044c0070303840c0c024589210400406008000010030382d540030700388100c5407440c000040070205031040f0f482020f4101d100c1c440001419030b2810b41d194500361060f03410900a20703016610b44400034101680000c2280e006c2c035512240c2401e2448007004000c19031411140307000c109034880c500d0904030782c824041e440182c8240720300d08040c00540750241342c00c4810180b072a482031780151203181005018025280205909107 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 514836951 1250 514835701 514835707
    0x203070b0a020403291e0105100e0604030606050a210f03170103230a05030409020901090b030c0405120c09010e0c040302060301170f0a051207020d0b10051302041a 72
    0x3440c8900203002d0f640c0040c000340e101207404c1e100f0440c2006001c9035144104e840400b40d45404950021144214203a1124107662400500c00352800203030301c100c15002c0c1e18084000c19416008544140c00c02d07441100d20340c0e240c84003880701c0c3c0382c0313611520080d1030a02c9900d88411200308907240e401b00b903080003034928851650a2400e142c422641003008101034040c12001d035a40b881c02040c00c0005040440540b08400488582e240000c559404a560840e0007142801e04042c0354000035844800c5c840d040c00202c40300007404012300b40140d0b120305909040541c849150105000401032581c8034682150806a5400740340d07a1910b1000b41501c0c1c48241d02e1141d56191058010180b08682010313601070408000055884600403030400c06558810a0300c6800345601891aa1500e140c58000c0050300504d00c0c0c40342884c1d00d400030300070543c00100800400180c60f10340809040096840c9041a40d600c201400a82010100d00d02c0302d480c441d808510702880e006410b0150b901d01074071105006400 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 514838201 1250 514836951 514836961
    0x21509070e15040507020a020f030a05100c1814040513080711060d020c060108011103010b070b061c06230c0a0c06110c061515090108100f080a0b0a0c0203070b 70
    0x40b42500100016008001608080ba0069540d40e0386040491045a521004490300d003404038480c031546510400422003907626605400181022000c62003c20110718050303500c82000100700c0c0014403540440c090321201c0da13000d1000b0b90344005c000d2002140044240383c001600d08045903105a0807400007040d0000060000f0440c1c0f02e0103000e505058000703d1200c100c02c0c40410b9a504880204000300240c3c0c00028041d4582c0c0002d1003603040309036043c000c0c4400724a40180c00b0f903001034028414003961146801c1d4a0250200000988040c1d98440c1c1104501c1c1c0c9010906122107064a00903003e0f10b80f030000003925209402001d0304014142d032004003084601e8005403082d5a8900f40c2c5503c0d05032128030b541c1c0d20481101c200c0e43e240d15125441300103051100e207454200d8424521585041741803001580d9546c4054010304029000d440001080380c40b9145400140c40303036001510504281c0c2c14080040c25002e01010381d024900641c0000f040c0c6c0000c22190080d03030042003034000b5514 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 514839451 1250 514838201 514838221
    0x30a0b04060302060d1d010c0c081810091d0103020609150708070501150e0f0a1d0a12030c1b12050705030309011407020d020a03141c0903021509070e 66
    0x86034002500070401181d200380c0e5242903002581c0705071800e00c044101c1c0d00081d001031f080c1c885040f02c0c800482c18607101c50010908050080c150751202480760210002d10401003180889130749288800195850002e201d15903e41c03d14200d403442c121110140d950640e000106588102c0b080c3d644288044006181c28140c250140c90940da0004056600c410803410003038040c1400c445200a45045007401081c198651101580604102007200c10342d0341d00c100317000d00204419200c08170002e1002801143c02001000b100b8509403050300ca4540440c40c86401409841102155505101c82d013040b050078010414440104a604180082030032201c0581c01c0d141441a034030083c0c0240000070801011840541000c0f80800080b00510810307a5450003c907110800c1407070b94401038100207400408603100f8101036801805805000d840c00f19401400000e420700c1170740000a450f101c481c810113054060010780000c600380d1296601d20300d0300b24101621001c2900503800813100d814040303050415 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 514840701 1250 514839451 514839461
    0x3051e0601030c020f0316110a06090b0901050403051b030111070213020a0302090d0506090706030b181807170f030f1c09140a020a050a080c04050a020705191703010605030a0b04 78
    0xd0b401d0192030340e411002c010044251844041911a28061b030008c0e402c03420003403000f404440700c070b94990221908090040c1c86660001d0b4815040103420b00000c008248140000b01c01c942a1485403010058088181402e403015118540b0801000784581c10242c0c80f5024500c808854005006035620030100c002d030020b0183e221295082000c51040c07008100300003400c54001c0014900b200d2409a0f1148100c0540b000c2c1a24660001c1d001a0a034400007c5c40208076042001051a49002400b0320740c00762600c5d0060f4044541c1420042c3c044291190600018a40340c0380341005c0c2d0310301250120152068856403102d040070000c500b10b031081d03400c01944001840b95000074084106500e84405590340d00000b901640300e4403115100082038030b0240d003010216110007001e40a0100702400300001003400030301d90b8154940800840340018414800030340d10320031a400b2015a19082e081000601803055144401010308000600c102c0f030b0031105580c0e00500080d03000c10000300780303008200904 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 514841951 1250 514840701 514840723
    0x30705070b0901230103031101060f0329340c12020309030307030503151801050f0120150a0903091715160e030304030803011a0412060c03051e0601030c02 68
    0x805109940d01311400b80e0410075040764007035aa06214406141c01203800c079580b9100c0d1041740440034004200144410003801c00c100c4c0810070703225841482d50900e051061084904004032039615404082011005001e41000080c2d40703800000e02e4a84c42c3c0c0034240381c5410a018162074101c694030400c80d0301c20401c440032980d0180a49131103030340c1490007402c2c9401c180c4100d03011000e43d1920a2032428034030340004c0204607002d03401030713140d2916052101030fa24040c2c0d0181042900d03800f00b1200f0728130250b100000b9010354010440002c044400c0d40d8891405440800b08504086e00c5001195002c2d0040c0140d50070174100c05812100300284514043ca0714035503814007010f110400c01e2800078826070a240034501c0c4c58207000317a00500d01b00350f140d00c00ca000040c0060824001801280460031400024500710101030b03203001d8480800d09000c0c44180d02c110741680d2070700701c84100564180240c907000340c80341c04000c50070142241c0c0c000350034500a14586c100756650b840c1540c1c2c41d00c01c03c10040c84c0 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 514843201 1250 514841951 514841981
    0x3090708010e0c040b27060d080f0301030b13050d050f091f0e0d0c0e0603010209090f040312091a0405011805070312170c090114120906070302030705070b0901 70
    0x599011030b00c01c2d80720710b0816083c1e4400c51421010000a007021400d4011150f8510442d640e40184c803581e10806000c0034040c5500700038501001c80005045000600f01d030180d030f101c900d840b9895894403c403d01c8008104084402d06462a80300144000481050018803800c0040d00d80e00d1000102c140c9001d41c1200c0380d4030400d0068456001d051218200e9007201080d520501c40301010004e006000342d030040014505d1420580c1045126588101990410310040015190013500e90010714502016244142d0700d80328a401c3c40105500321000b4103840300b585209000c05403030f58884804142142010a40101d07031480010104070082d880174000d10416040402c1001c018280a590f603002030104503600030380145850000341c00346491351118007404111843c0c9507203d06a103006904580192818041d420701015900e4030704001030000d8541c5202a001350780391000c1c00c0c91030500d002e82104145841002844501c560003c100d50950750090782c031070000d45807002c1c51401064906908412 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 514844451 1250 514843201 514843211
    0x50304020d0c0b0a0e03030c030d0b03102306010c0f0219050406171204030c0b0d020d02030f091015061d0301050408030603100501060806090403170405010b0102121206060309070801 80
    0x40d150b00c060140c1080c03030700ea6580032040e450405c2403503924815444100d000e60720030311001c84080e0706a0014100b1103405020749404141d80141081510202d0b600990790203817147c1e4045142c450002201c1c3d00603002d19100c0c0c142d039015255116100041e000107806090b00241001c400028107003c50700400c006041001165a9a00c450a2142c3c0341444400345004070212400d000002c0000e8a00352900a4101c030101403810410110317075442401d6400b0071030340a000d00324150030240b0140d4452410300340d54549611b44010304504220280c1c0700d80c41d416282018111204440101410a40748181400d01080d00d52150030504064801500c5601d5801e1000300010410f56001850240006908880861062884000940700240240b4001464510000e01c45181890328242c02c1070107400c10308240140d029100380e010340308881c2540e15a444011945040d42c0c10080c071140480101d851a045c40000125078000840c06012180b0441000c80899146c0700117009550090000030000c01c4 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 514845701 1250 514844451 514844459
    0x17160c14010510060e090f04030210020712110f120d06050d05010c14040614070f061805060109060509010302121207031710120f0c12061a030706050a050304020d0c 72
    0x10203024122031030f60010005082c00186140a000e2048030644014511328241c0d540c816040c01a020080007641107101c0d10354040c204507606d00c0180782441c044e00c40b41e60f80b4484044058125a468407800509074001c1a20402004c07004c034800c01d160440440c02d0765606000e0b541c0700080c00858021641c000d40191000080040541c07280f075403941152110740a4030fa040300035000301d000358407410000c01c001580155111f6050401080107a11134041211000f07107644545046a80d20210f245043c1401d0444005002c3c04200040c01002d54500901483c1d0415012403140b80d010320000340540da110581180d6030006000b4000f00e054829022521480320f801c0082040725a2070704d181103007000d500400c17075504690140300d040d03078110902d0080780102c0e41d480c820f0038058810152030110ba05800421072200d00034000c1d418500540003c651100290b40d03104004405858191107584040000c00031142c01a0689660300881d0400c680c90f50380c1d0740045002c90003071880081402c01c80c01d130081 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 514846951 1250 514845701 514845703
    0x309280f0906060e010203030a020a031107030804110901080a02060f070501050c0301090612080f071505090a0507050a080c01080c09150d0c21020c0703020405100e0717160c14 77
    0x804440c281c09091064668401d41942d107410624039a0b40180c008000050204c420380d0001c2090b05d21520f4002564440c10303107550419080103004800040c505020301c0140908403200429402007142d1004407540741c1104c42e681d81d00da1160081c083e40740440d071222814045010350361160f421800a008515211003044031a034024050f2114440c900030001c1500c0348440e4107621041d5100003001c0c54108003007125001900b107203800b00c50b1600b50346080b014800d42401958040e041c5040100424400d41ca426410900c8035049140154000b031001c1040f080d0003c0d0340ca21032002800c0030309594580d6551507401e03100d4030681c50340005010800306620303142407008050441c00048100080c0c80020070848101403c1a421071910441840510580f1619402002032541050031580d10b0350f600d80c08102510000c83d2480001c2d9282d0004200c0075a0f40407100e43d0241046c038200f041e40864040b0991041c40140c09102951189030425449a0145a11000c495000702c1e80040c1c000d040c034586 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 514848201 1250 514846951 514846979
    0xa080415030510081b3f03070309050603060402071202100e2b020f01050f06120c0a06030e01060906090504020906180708040c0b03091609020403030903021306120809030601120302030928 82
    0x103103281520903516a40fa01d00c080261030115270705590700303a02c1c80e14000401c01160405024250300c144c6c00c10800d400584031508224110a840d0050700c01c48405149980495408040301c141d160488404407140c1d440418840c40c46100500780c1d0001425080d008a00d8401c21031302250a42d803a14040c4241020204801071044604a40a210010090380340c561140310400300d054106160780300a00c11a40a60400203103030010200010b40541d0318a910002d6a41a82c05100007554a0040c0f00a508044605590184007940c1b41c242104a09146140c6400000c10705410030072120089001c11040c0c02c44200240441e001c541d031281407034407090340c035a40300700062080300c05144000900e20740c560090300d0450741c00d80c661038401440c1d81c0900405a00c0b450142c0c8495a881501107440e282c072030b40742107141d4000c46980d0785440d8580c080c9882d16106801c00010b95040d82e020400007035001089900c1380c1010b942c0300311100c00b4280ca0b49041b02c04841d446102c285144d5003c2100003402000c = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 514849451 1250 514848201 514848289
    0x609010603060c0906170a0e300304120e040f06060f020f0606030703170c0106080f1209150901031b03020703140a05070b07020a080415030510081b 65
    0x208100c000204801036400b44518417881e00801c0341d0b8003040c02070060000721303a50f000120100c04a0b20203444c01e502c2e81404448242d900034092540240f2107100c3c0c0c19032000740548a1109500d01d142000c1e2070b60086c03242280440c0d0300304074000c4541482a02c80b904042c410b161017001c184003140d00c800001c1c1c070a071102b8a0200040c03045101c0d82c1040f81d0001042d03401040d014015020043c20351304c841c41348140c0c072181040002c008001c1641c0f0028240f00381001004650080d14061903030a400300c0c00d104540c42200e071403010501c07802001d076030b60380403040000b030b2040c4d00c0c60303070390461040140c028081e1100300101800240700d10301c011540640003040c40f24481e94600181807d0f800c01903034140070f440c00d2400061020701050002500024100760020801d00407100380c580319607541c84d5107034800d4201350005845040545005500f5008035070300b050041c54036002d5281051000d82c0d5a81e8400c20220340310107160400c403801c0d111845075404c480342c2901107500f103045281080014020b000a = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 514850701 1250 514849451 514849463
    0x1060e1e060d1406041a04020d02091507120311090d060906110d1416050306180a060e13150b0402040f0f03030806030607050a0804020a05041d0106052b060e0609010603 74
    0x40040c8082c0780c28800c6d101c00c811000e0031055001218803c1c4002074100340710058241c1d5003000b00d20700d540d40b500707440d0140b01c24143c040b55843c90240740ca03003403603081c84486005060030489100d8039420301c1003c1c0e50086400352000c0c4420512410480090030403880d014060364586520810000d42d58001030860361604101480102200302d2041d14100c0d040381d5082c0d03d003030703440c00a0001030b02c9440110303000f0000410341c9036070702c400c01805a51480c09544c8010050365800c0300b0000040580d40c040da201e03840795804202c004454540d04148c0b082c4003001c200055981d2550050ba9691342c0c1640c020f401d8280d01c2111054031082446500c0c1182e001c00d60105a4103000244980380000c0e503d44585c22135511a41001c0081c40b050340c088a0160040764840344140012506031594400c42c1244900c03001c80d00e042070742060540d800c660203a00140c2c080d05030601040340c00040741103400d008003000b0704030f00840980b5003001c40040c503810030399130b0180c0118000d004400300150085400e8a001c1c0c4 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 514851951 1250 514850701 514850741
    0x4032103180506060904020a05030601090e1b130e072c0a2a120c0e0f0a26031e04030b0105040204050a210203032d0301060e1e060d 58
    0x401020703400362201c88000c00c1640310030f00198940c1070540325983c2292010f000065013a807074030700180c01c0100036000181155a6030b280070740c040008106843d24011030100c900c0100d903031640424034080181e000604c03555200c2d0040444483c1c208000c900511440c45080411148040750b4801c00f81540707048005003000c8400b1407d0030140f481400350001d84090400141c407607613030682d081030f0108100c100c14083d05040c02c106030906e9019880e00721405645031070b4029200c0080000e24041041c0503400b50086503005d1214007038044085212014540588040711074541425256100341d40c4504544010034800c0c900860854000d0400d8a00c05c1a5403003003a038803402844220b0040780b2500b80d204040303101c20003040c0c4201d10400004a440d020381c174500041340c0c001c246036600028080c0b0124100303610b108841da40c188040c00c61030410140c4285154500a001003c212220b160f03284211420422080311848081c1e1800d000c210150030b0a840d0460003504200078020380361340f03012038a054 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 514853201 1250 514851951 514851971
    0x306050109020906031f030b01032f03100216050706090e0106050703020a030e0402070609110f010513060806011e021006080c0d0602090f0d050307111e0108040804032103 75
    0x6402074440042c4003030301c0c4d181141d8032000d843c421026441e1900e03800c5006a80d001c40071822400455020750b001703d1000b10b28909984110345000d03c0000032010001d403240d0303611500e580108404030f030052502c001589800e003034540d91003020340e14007008215104810000601c99000401c04040710405241034550740e903512015146803080c50700003801a0081501c000c0000d026074030201a031320303020b0401400c2c03240301d0742c62000f1904590000c0e258038804580d00c88003440c18034107074a0341400c02c0c40c1c802c0c1004069072070810b00240a0040c041407000c1c40d00000d0039030f4411f81501c15031402d04003030400d1800304440d019490303810a10302d44030b030a42401d40109441100040b4060007007400340914a5001540d00c0301d00c0290003100c44039500c0302500000c1d0b02d0b580e45400d00b613481540680061a901d14651428100340b000015a8901803441260075442c210a000c0e81c102a011081c02c1401440d940e91900280c680b165400042400f41007280a0403002c8e0051962074a0381d403103880c2000300310380c2 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 514854451 1250 514853201 514853219
    0x102041403012a210f0e0706050403030c020d03030e0a0c090c0905010f0809070803120118090f030c080f030a1d120405011b1e11090606030a0b0a030b1003060501 71
    0x880c124005400604030340b4020f100f0200c500c55049061303000c06101c002c01a42c6400c0d101d201541ca440b083c0c0710104503042c5002884407000412351401c1080c900744c9940e401415070600c52201a1080c50801e08901c00e042c000c2c1c002c82940d0205105440d822505443e000000c0842c900442c400b0b146803002424040b07004007040004c3d0b41050b100c10101003805201118200d03402010b25006026039240041c01e940c0810250404008050801140758180240c2110740c3c441c2800188006d41808243c2011a50010141141c6a01860101da600d80e09090041c52441250658000441d0000c1045501480c03a0301c00010a80e80080740081e00c65082030740b507a43e0030490b000d003600080c04c010070496903020f00d001d1035007021000d69003040103220f6140c58500b030714900c811044e2510041c034810100000002c10701c6900c2800c03a0b014009003020408100c00d8007005005000c00740d03076035a500680c0e03561001403c0c001c561007034140249141c62001d2181420491000f01c3d4101d080800100e58281 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 514855701 1250 514854451 514854491
    0x10501050402090f040c0c020310020a020f010216080a0e0a150e0405090d1b0b0702070501261b19031b0905030a0803041a070315050111070b1308010204140301 70
    0xf8010002410011290104802000001254428080e101c15402c0060300d044c4100301c00c00480900051b151140c141c4040c0c1000d0703c03048944202d9104001c58a00c40807405500f654085d002078009446102208003690991400da140e141d0001c1811000a4005d07501c407120b80e00b43c411a514005400500300074401030340c80c140c0703440b102d50300960f080704c460f0303807050400400300203c0c05070011000300039489507000244280c86400058018a00500030b958110148248510207440e51003990b40d88809002c40c1703040060840b0308291081c071044204048480203a40b10350703040c0394511010b540e68042c06801010f004c4000741d0314204903c2c0305140103000f4942e80080310302c00b401034500c1c01c000c0c5ea5000c480b94802001140c08804142d01200c1030074007448024450100c0d41c5000401129050118282e07200603806981048000d42882d2107403880400e00000b01c0b0790750b8060b95158030403190346140c201210740112059600c04038000482e009810710900c41c000040d0001c03c40080480e4141c05038070 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 514856951 1250 514855701 514855717
    0xf14030903190f1d0d02180a0b061201060807050d020a030b0f0f0a03140307150605030c060703120b030106080111030f060d020109060507020112110309070b0421081218010501050402 80
    0x15400d5003003091019100000e011360403030300400702c0b06104035650000c0c4500700f04030365829000365444204102c6401c1c0e4802d01d0b980503021a27185040c0300c03448201100000c03050188a04205030741e000711f500c05002c0c00a81d90714603a41181503403511000a4024010910310300110310840900d444507410303041104555111080241400002c05d0450311510180411460011780034481000321502099044443c010007111203040810190b1800080624015148c05c1e800e100e0070040200b0700c0000d030001c003003800350480d4480129611181200203401009142e1103160554203080c200d009901c04580213501c9007071150110b4000f0341702c48050011840901c400240441c210b10000d000090045c006060740794414074040c0501c440340000c24096540106220750b2105000c028040d0039102444643d000d40000c0d19400d08007403400c01c9620301c030700302c0b6104850021520100703641442180400c0355030340d050010180c178103803c104000300c090f00c41c286419140e030f5203084004a0f0301d2404e0b008440d8a9 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 514858201 1250 514856951 514856957
    0x30103080304055101030c08060a05060a0302190b0301060f1404061b0618060c1704030917100203090d0909051501110a140c0406090510060f14030903190f 68
    0x138180801e015103030070348181c2c2e040d881040c1c1c5000c0703040d00d510888200d010b180300b0071315440c0003031900c41242e14181018201c0703036205081c0030030400141c42e030185003000c5a40403107c0f8140140c072411a90340900d5079030401c06e48000c00000100c0c0160f08585441c4440b04160b44010407811a0700484030b1b0340c0520300540001464001150410465100d0704001181c0180d40000304400c006000d0440119001c000300c43e1036448003074207803480e07411900f00f00200420a2100f5461300e06542c1c0100034242c0e6002d8400c4041000110900211042184407005042c403030013196642000c5070f074180c1c0d40621000da6030024a0400d4040b030b190300140506402180307083c3c559a10000202c0054402400541148106100310000c0402007018900185054219400a4100429040207000c1036901c80e4101200050a010038040b001c200d2182c40d00844c0d0591411345001d00000304200d0b02e90044100706a02140f0120038000e10f88004001455014062401000381803840d003c1650807900c14903144003c = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 514859451 1250 514858201 514858273
    0x1509031c0f2c061903090309050603042f03191101110304360f0509030a1b05010204050a030503090406062c060c1203010315061802090d0803010308030405 68
    0x48036241c682c0a1054400100102d0130144040f070300d001c8041d01040544006034a540001c03080c59000038400014207020742c0e040b8998980f6460b02681040820802c004103030a401c0e0b140c1c034403400da204a00030200c000b002d84010b100040085c40b1402443c0500f03450308000402414559806108407031802c080100155040c00c1c43e07c0801206a1008544410101d0042c83d0b03c403c1c5022a80a28100b14940680007400c154549e80d084100d4100a00b00300307951b88200191172086410542004c0d80310358103292005103014034a001c601a001e036910860704403000e1400403082240200284c00e010406030b80410505c1d0307403a40211403081203820480d62611401d980d0381180811403100c0c20b03e44030b0192600740b074010b610004a1034400c042d03c40b00d010501c08001841084411040382c010190100c0090080c2400c00140904801d0003100e1170140c2c66000403000003903154050400e00103500302040c25205d6035a400e0005245e4000c80341110140102c000070350500d419040c0300c070380da402e2220002e04 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 514860701 1250 514859451 514859507
    0x100b011107031e02090a0e0105012c060a030b070f110303040c14120607020313080f15041e030309030201180c0b070507080709021b0a111509031c0f 65
    0x103d00540c40840800d40f990b00004002d131302e5505d8094000c1e45482c90000f040540700e0112402c40e001a0000302c0703000c040c0302c205100c00d1002c15030000d94a50000900800740c4410f0001100c21080340d00c01415603400c0341c10440c075944c1041d03920311560820348601c8003480c0030005c0c0c0c6440e403100300c42c0149010ba00f200c0501440c1d00428005410720005040101091420314201d0f103080811500c2c0c60060f400040c504130b4180e428500071008101c0322005001d001012071425031911214980140795003001e10005041c0314074550106c84240075003074100440341050400030301a08010000b680590f007081c0b134402c11009081e141301c6146030481d131010007141c10310704002c0351507110441c2540c0a200e2502d01180d0844d003030010714002c00b01050010380d10061002e800459000342d0794840324039006503450001240b40b114a82c8181101103d01346154030a4103c0074a070f60140700c01842d0103100e19440b80041202d07400c0d80700030785100d030340302c81e1400c00b010401192050034800c1c8004400607c404000 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 514861951 1250 514860701 514860713
    0x4030b060402070507030605091501080c0f010504030f1b0e040314090102070e010e1618031227031b0305030d0203040309170601140103020a020c130209040e100b01110703 75
    0x3904848000d1000d4600300a58030b0303a61402d84240c0056031901e60701d8081c061050010410700142c043c0c400c1d0400841d43c13414200e961592013526040380641400c195222030740c2e00c1002150095684501d068800d50194244030043d080b0040d136203032034032050341e0022030360030651a20180304d25490356030030b02620308040d1071240340e42052000a041d07100c0c283c404540690120756480c0a030584c14054020784c0b40c1040410940c4000d05508802e01000030000960703510150448000d6a40244040d0204035407080220380c1c0d003203900003600805c52511458401c081d05250706070102e0380a024188081a408501c10011a82c5840002e00c994401c002628415842e900a95802400b074106003501e5a9642c07184c551149000f040c078100c40d0011300052103481e00c5910f416060070310a2a0440c2401001c0320080d58914102d48941c2c403c3e04402d26412111150340c04541c0ac01c0740c003800034042a10703a1014155189280010103c10f1414411410580d512405042001e80300035001020341900c0c64451b4 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 514863201 1250 514861951 514861973
    0x60a0b1c0e01020f09040b0105030103020913021f020c0a0b1606050c2b0e0105040b010330030605030c03060c0306060d060e0c0306011107081c0c050a06020c061005060403 75
    0x459003094a40d188007104400a101610111100c40140e9641e07040d030408105c11217030b040701c0c05814480107000610140c0c03a82c569440d440300708001400640f62140c000a01c070303600c00b9a44040100420202e602c1c055901040e98440e0000664251040a072140b203044194010765030290303060810125003c002c600380d03400c80c5400c0054038114902e0401c5d00c042d089400180d0008403499101140d0070f01d5120905842004030002a0100030080c0f41015030f649030581106110141c5450700f134085503040e0400c0500c180044144440030700c504051054400b401801052280510900490003a0041800d001c1074540c810b03035021040c14a550307611002c20956401c100f80044400796216804112103804111903401086a10b000075180e1a06000050140d0485003c2e1503151f00b040e03604110403800010b4036501668060600d0540c1034030300340d0407955031140202c06000c0384505004201030080c298001c3c0340148154090340c10540e03840a0420f44a112449400c3d0843c104020030404280c0b00560 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 514864451 1250 514863201 514863247
    0x14060f010806070e0d0503130518070c030309050319110f060c0a0f140d06030b0a09110f0111060c1201060224043f14030a15031703010806060a0b 64
    0x7880d0805017140c1c460a145d50021003030401220240c43c030a00681c03415141d00d0340200d19082d003840035407400200040c1408950b200007007c2c103464204400800205100340c802e2075440c050740721803804090800400802c058180d8141a001d4850031081400740800e00500c2682ca0950107490141c0311181280d920005c082f0440030082402400138001c64180010900e07901042c102003400c50a5050026a440d4040e2004100520702803103040000c0d00101c000044880c21250101070001c0e440c0140e0307000802c0c1c00e12001e9402850104114180e030703a00031f005000307401110501310381e032200000da03a9a500303251040228074a040e42c20010f001d455008560180c412a8803000c0680c0d4017810548030052840b00c00d85020300d00c501c5140b031101005414444048030b1600d03240410b100d042d482c106100142c00100700e1034407060001300f1401300d403405000855010101c0c41c018400d0640f500c14940080c010714820b03010345004501d0134940b0b000e100d4255903120300001c1c5800b44169a41c0714403221084 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 514865701 1250 514864451 514864459
    0xf06040e0a09030905091303230d150e0903040e070e0402030a020d051501090b1b030c0d030506030a15050703061707060e040203090613050c060714060f010806070e 72
    0x8404a010350000032200d020707001041c40403400c4031051070050300c0d11405802071801007100004014200c446440047c502d55003504104401132041c0040302e03c00d4450100a04107142d000036140302210032507120180c0134030710441080c44262070341041407001d0703026140c0b80f130198401c0c40180030213200400c00940242d81410003861940c814804103080c2d810032070f41c4c0c1e0051a8003242d0445820103a000711036100940325500e5041001040010340404001d01a005035200c010410010b5030030b014101442003103450301140d8a03400080c1c034966a40c05400480c400103810301021911320709001503082035496100c20f4040602c03100019190003001d00510240805071a01310018802008108180415425102034419507041500180c4421300e01c2d41001d005910410400003c1074000c00c510b40c0101c0d18500480004a4900300103141a40780c50541d68000f000081480030050342c14180355107400080144c50540c5d840c0c604c03400070702d80c0074424400150060000500da03684529410f10032024020 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 514866951 1250 514865701 514865707
    0x807020f0616030509010e0715090506031003050d17043005030a060f140d0c090e010218030f210408010f02090306060307031a0a0b0d030e010f1d0f06 66
    0x140c0da181c140151980d0310020035001d41196080c1c0c3c0760003003951002c0c000c3e009007c5406030700042540d80c842840381601d1400310140c00f06031548642041d00003032000404868a81c144140f15581512440c8011510703441280446408a4001c4640c030200d4411440302840c40e503941d8446e5145200744458407524821565006024026094980c912854280d946c15490f441c0030000081180c42c541c0007061602c0003004100901c85102c424aa5013020a41c0c42100d007503c5d515001d218011240c000468150501205840c90401540605543e054507450003034000041014107481e40c0001c0003d01c410f4120880d00350060101ca001d849d40f5010350110f00d458a80e55848650849902d41c005004c5103400082e08801e0749010482542c1041c03084004e803149901c0d60303030b8490b1542c0c000b0741a040d0307c203003038000544c1c051141d0b44440d004001c0604409107400951400406200101036014041011240304615181c8100242da40035203c1140c24086c407408142040007086411101a0b4002410 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 514868201 1250 514866951 514866973
    0xc0a0e1906080d17090f060c0a03140103081306050337020c060405010b060909010608071e080601120b0d080d0b0402040f06090e10180603050f0a14030901080601080702 74
    0xb0040003141c44030980e103070840140d80c640c0c4240d910304060041e410781d038080b61261b0403e2201040181e0000741303d81d0425a034545050b41980641118010368804502040c000030a11400c0070040241c5003846001c4030317040762075031015181d5000a644c05114a084520f0708a0b01ca600b003007601e49180d80c0c01c1d036480805203041c031510060741d2000400c0303d0650060360a000030004240120442c3c000102c440a043c040b00d5001301d100d0b60b005124000c1089013030000b0840540c0205401c03a290004540641c03c40907118802408140301500c44500003001140c504010740c1e400d214082c42c001c0001c0001405410716241d054076600070900981055940e020a2180b5544034402072004200030408031b00b10a01c2e110019280c07454540c091401c0c0c025220812416408002e40c030402e0351351654040050082080401d0f008080700c4c0c000504070b20402c0c407280345459000030400d0000d172041c40e52460b140c00d5903580315200e004401b04180400c0c1078102150381903000c2d11180d0b9100c52988100c668141e86 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 514869451 1250 514868201 514868203
    0xc05040c0e13020a0816032304031d0f190f0e04020a1d010504090f020a0e0109290123070609020405090c0d080912100e0c0a0e190608 59
    0x18014540c008142158440d08060800c40103484a40628010440c10000140006824414014814200b103000da000003501c07240a90300007052000c00d9007140d100c010b5051816900000c0a4400342c000c0384184e00700c95a1500c5030702000f942e0a5015124a18801d0900140200600704030f00d0701080618203180882c0245410a44000414080b200a8154100390041c0304084c413032904151181c22940e9420340303060f0056520103044490a8400042070812403c201243d0424100025480804000300258240c40010054140c03040c5480402080701c003040140050b2981c200c2203480000e0075a203000c119070140c50010200084d01100f2000c281c5608400a81c0780d01c195400c4030195a201005c03c1927051520a490b0700440d103d0081ca02060400d002a036100340441d401001007400052052458481c4410041c603511b114080b01c0c1e1860403044000054001e030007030840c0c1441904140c0049191a440302c004481041000c01e2031910b035451444840b10820f0507020440340c4402c00080c160030 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 514870701 1250 514869451 514869461
    0x100f11070b03091c0203070803041115030a0603140d0c06020a05090d0501020408070e01080a12120c020a1b0b040b130b04151419080402030c09101e12020103090c0504 73
    0xd0f03094080c0c071214502c00d45012400c074914401c2c8045501c01d0100c2070004000d20704903038000b604400c3d01c10140e07603100c0007d0900b1071200c82c05000c0303d801000303000c00752102d13070454002d507407140000d00f20000c02041c1c0c2507600c2001c61841800281540b4012000c11200d81c010142d95070b9501d00307185021010404243c3c010901001151269400101002121000e000f14000751101d401c1000031075150011080d59a030341c106002d4464000c80080c1c0119074011404231071020700301941070040c1103004501075198000c205007078503d880c2d06001061030342c001001030001ea0340381f00c030f00504103410300341c0c480c1c41a0449540528095010780002c6410440e07500608020500240603c1c20814101d02c001c1040380000c003a00c412880038016000030910304105150190214907001680b0740d142d000103031a080c035001d21a40c0004034802407016101e240c281d18800d55a07111410440c402103042401c0c100d144a102c8c0860401c440101c00700158842e80103142c0c0d142c056151255195111800078080390 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 514871951 1250 514870701 514870711
    0xc1021241d0403050a0f020115080c040b032404050304350106061421162006060d050f12040609050109080c0f0607050105090a11100f11070b03 63
    0xc0a034501080024682480c1c415807010344031404420742496a03026125001d940121070610200003401e01724a40b00b58080700724800f480b000c410b500c541c2e4290040c0c84070340d4007000074091401c1180d0541142070000311244c007111104100e40080c0240042d507420281e0140084880d400100720000d100c0000740e46401a45040c440102c040b90790b6a03007255040c6015080348201c9074100681000b4154110020503518021020480c0c0e0380d00303450400191680041000b01000d10780b02d800c0c05000d03820f0790b418000d500400e0f190603a03601d400b450300040700541c4000782c015aa0004002803043e040000468519610801c203d4059141c100d070101d081028031560301d440d1040200e02002955400203411004080c2030030315000c0d46041c109012749883d420400707180950741120030800c040e03c80c5400c40b05030310313004002001942403914015841c3c1c0300b40907056400914502e091043d40c601600c0da4441c4110940760400c1013040800241c8044d050121f11030b40600030342d800094030680800041d4031070 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 514873201 1250 514871951 514872011
    0x140418050a05010506040c0e180a020f0c06040606060c050309060f1612090909150203090a0203030a1d09060d060903110f07050307090605061b011512050c1021 70
    0x2e1501d1401e0004031080d20001da810880001e049190741d80351740c24440c41e0200c221031142040e5071a188880e010f84a841407402c21490006010303e0dc4250104206009500c5072100740075150380d65404a0344003440c0700001c0d04d1038104001e50001803405c84014010b00341104002ca04000f41040c6801060501080942c1c0e080080103541000b00e41c0003080714042d1410a0081003c624552984050700e2481074460400c1c95001010600181c400c12000301401d0340141269035504102400800800d8010b003412002c050f410341c0703d856481e01d088068421040035068080084864441d00050316511400390103118100b46d55080150040c4189554088441d0082c06c0140c44c20702410f1406415030f04c0107141034a000028402503803980e08640341d00030a4180d4940600d460050540108010000300e0ba44155031140041d4004000078410301c054018003e45845280c0c50081c002c2c1a00820003040005141d0040008040c6050503c0802d00044000019900d03402e007050300003d03a0303403001c09444 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 514874451 1250 514873201 514873211
    0xa150c02120a020112050c0a080c090604030309090f14271006170706090b0c01020d140105030f0a030e010507050c04021b061003030e06220b04050307050a140418050a0501 75
    0x19960002c4405ca11006940000c010605c0c05203040c440034001c400b024820404201c010410610700303003041e6080c1c00c8006100690b110390ba450301410140c41c074854455130a017003a44100c4000038a2090340140300c071007560302000341ea03140038910400c10f404042e294000103030203007038020081c10083d00019840c0c140002a1003404c0050b50803d80c89031550145d4a0383c01000305024990340310810b0000c40d411950010f8840c070503c044140a400380c40c045a1040d13182080121240003034002d240d040700d4059064500860403405026203a60a6400290205640d1101c0c2c51645d44100018585c4900401c203641700000150b00041c160f81c000700000400300c590f0a030340c00c0841001c1c04007030b0300030650510b8005800d01d141c4d0040c0200a8041c85a44903810104540b21042020300614002d00c0142001440060311042c0c0c110b000c5d04580200c500903c608403001c5018108440c3c075000b50b512160001c9600d0407440100070190145402c0d40c44400340d91030301580050010041080e50314030403000412 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 514875701 1250 514874451 514874453
    0x80327030a02010f02090f042a02061806070905011b02090f060a0b16020411040302032b18031205090315040b15090a0e010b0d050102071703060a150c02120a 69
    0xc29524140100e40e0060700c100b0400721b19581d007104d40c43d4443c405550126000d40c03500c08c030118035518203561f00142c020403030040b0035041e4041142445042c10400c0040c0005840c544503a4610044504802040180906102660241240344680302c00088113001c030181729030200e5100903080c0c903460103142d0710310148041450b0484411014100b69401e072400c08a000540c1301c1c11a4502030040d000300d54075510540d03c00804d10469000d160041c0c215a2001e24040d0300d90205001864203071203521100d0030814410307104d02462000b080d60321703410031071030f40c250303103e8070070ba4450a8010021f01c6020008600140c409200c84a420700340403138510607601c0c241c208a01030701c41c01040c420088d0103900303c1c4200c544d01c0030081900303c101352400007044554108090300500459034255404842c28860000b00708054000b4042d0b0791048200f6420680c6985501030540000c2d109076502045a81d0203000c01401c041a80c4581d0700c80307181844581c00d4940100300d010985880403007041e042248088 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 514876951 1250 514875701 514875703
    0x2031e042013020403051501050d0804153c0509030a2406060503040302070602010204150509130204080a0318050306042a03030905091b1801120f0b010206010e060d080327030a02 78
    0x1d004010076142640c1c1c1d18400c0d600c0c000c051265000d10075017400410340a0341c0b050b2041c0c1a041d100c0c107580c5003c078829801c0c4007a111a2800002293b0300da40500035414442c0740c480c0041d11a0440050003c10301131030350b9a00c40e904c110805170000380c190030707c404021402007580100f0340205103d855855880c1003e00f0000d0612400d500050156801008100305402480c40301050344601d51034403a0b00e40510500103503960740c2c0815140c40090010501160341c1c5404281103e0451107511820810441104588040c9816125040d815005540041c0219041e0580003908880c0d040044000082500071003014030040d4000f51f00040102d4002d21580c20800d00c81c40d0008500b0645d0309071a1914820302e11540f02c0c1080901e020000e80d103010b4416400751620288068800c1c00a1007143c0a08040ba801081c00042050040c41080c00020f60015809081c80c00307034402401181e000c848035128002142c3c4050440983c18461402805452140d41010b0341c4900c000e01c095a03941c0c011100003 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 514878201 1250 514876951 514876993
    0x150409060c031b0503010b04061412041b1a0712020f061314150406020c0c0306011205060c030717060f03100c020f0c030c0d0f02120102031e04201302040305 69
    0x41804d001c001c1006000d03030031b5243e044d02d003100e05038500b018543c070301c231194003400d40100c504034003965217030406110130818200ca4603014003804d01c44142104e5a5801c0c41d41002c40c8415500407064030801c80040861545002400850300e1030044440d94009420b401d4948081107501121011446120000300311000c811421b20b0400395004000e00c0051a000041c4030f40e010744020400d0f07500040000c01e00b001801100c030041d000405441c49580d40c3d20506111002a41084800340900d90018501114a0080e64003805080c1da40f1000080b1417010107107a000c01a080542c42048130f4a501110751b410032040c1e00f1001100c01c08a030800b4103c0010b80b41c000142d0b0001c0c6140c01203810145c00e902c000600d00c054102c11074540031181d51909081012400400003c0e4000501e844030407103400c4150011805190035081c055656020441500c500400036140213000b4241110009100516010480f1119400501d00403140f2610101001260300c5544115035a030004d03901503044058925007 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 514879451 1250 514878201 514878251
    0x91003330b1f03060b04080a15060b040311150301060309110109151d09041b0803031e092b031508030f0a031e02070510060b03150409060c03 62
    0x209000d030850940000da00b46aa0100003490b81c1d514030040010b051083d048600241822110b0701d64480d103c44855448441d07421040d5180002400f00c441e06140310711401d0120742080031540d00301429a5a280c07050080401d44036480000000c2d400c40350000703c1c0003507000f440c1680300001ca2003802d1901030f20f003850a4405905001800208010b0200d06a000060000051900c0071200782c0340d24094445418101d00d140d08603900d80c0411040001801035000c9003180c030f01600440d150386865046e81c03440704846280c0320384c3c0052541560105480c0d416904a00b401049c0c0300000da17400e00e00203030540303802c202201d81000002014040c2d905842480721001c05011440c0206081c15030586d41d0744105400c440800100140c02c0060342d100368400c040f413941d110107400d1613001c810b03190b00294000c440c06403014040c03500c2803609029548110000c60b080d00d26280d0a598170b00e9900b0307004241d1904226080b9807510203010005086120704070b0010381d680c400180f444003178120180b8070102040 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 514880701 1250 514879451 514879553
    0xe0d0e120606090c0f04090908070302060c0301150518181506030105211203040602040905091605010f0507080706060303020708060403090302090705090904050705030d0c020a05091003 81
    0x209010701512200d0010b0f40c064500c0508a545e9211115114110300c20340d4045010315140519880405c0b08150003000304c0d60090742280c4440c0c0303c410303101181e8402842252003910041d040004000d000f14040c0c60300d40041c21507200c1284c460804508a009040700e041c0c9640a0b640801001d02050b0080005400e4256500b03811907041201050b040080300407004032284581c90301942007a020400d0700108000c0e0501e5645a0501d454090081e400a0245e121750609000008040000015900000c600e100c0d6002a15034a032070700544900404040071410800200080d40115088c07100508500d886040009509403660400030b00f001215009a81150040000d200210317a001c9070407801da030740449810465440303c4006407240e110f0501080d4118030f003902008280b1802080d010110340095043d03030080e01008904031911812024020350000c0344440601060070104c07680381e402040f18880301d650b0307502c94494920004a44452038000003007200e40442035201300c00347c030a10f1210340c4 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 514881951 1250 514880701 514880713
    0x11509061b060f0e07091d03041e080a03020d0201051b0306090a060b0a0c171315020a0f03080405250315180803220c0302060a0314090d080c070c050d060e0d0e12 71
    0x7d400d80d1248500d00c40c1c00703038466044428904004080c0c1b6001c00600c00001207507800c400500d0080c0d22184101d07000c0015502e442c000a10010411100891120101c0307100b038a9680c4002c200010040050030b440c282a60360407020840210040050422450b20385410804140c1c070b01d44814002591103a01210720002c2c041c01030f4810030394840300181d421038004010840344203032007245008043c61018140d080c81d0620031080c10307000408180514050b000360f4880c84440100341c110b4903e0300300b0b01d44488092450400104425402c1909414031102d07000ca10154000c0110a01c809944000e560700a0000203106401d4580d010162410010302503882808005444402803a905444043e000d00f000080c50000103100364802112041414480b404604140f00181e030b5075000b150041010851501c0454080329004040d5408243d00038074044440307060105020782c0181003001100e9040e21403044114040045c0450b501400340c0d5699003000a0300c400c20850100c00d184040c00f1135070064 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 514883201 1250 514881951 514882001
    0x12050106261b0a0501111c09090507030504050d1d060d020a08010e090705151606020a090b030405190807061a27150105040509090303011509061b060f0e0709 69
    0x1583e0790004480302401c12245040d00341a100d42001c550000441540003c400d02c01c3d0740c16008030020080c4c0703400d003008100c01da4a0b080240c0454074143c5014000754001c1039051800392184100d4810302e00a031440151450050700829030301d030000200340204640200e5092000c2c1d601151440c010054807503500c120f410100f500d00d03290540790061a0147d035142c1038000070381c0301d0074046451002008021894103e294204000203410289102c000940d0303000340000d1110410040d05c1c06a900400a4030040d800c0c5003d4803242c50003000300300c418500c00d0080602048140c42449048681710400e844c1520b4001d04122114240004122007018100c00035042d0502c00740301140e112254401080354650080d0058503240516888654003440b880104020884d0200286040f03a5030209080ca0700e03800440c06646101c3c00b80914070010b04020b40340004103001404030f80d9090b0149100241003a2582d4000d025140f002d9480ca04540c44258200444102403094a1008260b480e61b88510f03441 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 514884451 1250 514883201 514883209
    0x90902091012060203041406040507031709130b1c030203030a1b0522050d060209090f0609040b0408131502060603010623040e0a12080109110412050106261b 69
    0x81d003102a055613030100c0020100410351242c1040c0d00c0c0346500f283c2042c1340a1506540d1100c80c0d0104075401420f0388100041c0025200c10f03220038160082248203090b00080f6240018003009800c588d011103508145002c80c044142d40c07a80c001d020390f01840e40c0703203402e01141d000d0f21036100b6403c031887c0340c1c64410341d1040c0c0d009066808140703030803404141c4050400100d01d402450764106542c00170940b400c180c2000029401000810b4003a1260700c01a551110807400d22242128419000501d420014000913900030703005910500c101995030814000d0541d08000540079005212800f46601804ca5020340400070a5400341040b4001c0c00305c40c2c00c003410003400d010b0740c0d1440d40300f05c507040c881801107640340e4002461000c0c0314001c4524000540c18000d5004603200c0c0340700301103044440045041e80c52805148000142130206a140c145040020b80f8200307013024050341e580d5614440070070010348102c10090000318891507200b070196800d07411800c02107400345880190320084907011950f11 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 514885701 1250 514884451 514884479
    0xe0904020f030c090c070b090304050a03020108360f0c06180d060e1f022502010c0c060f1215031704080d051c020a0903060b190909020910 61
    0x3505480040c028070440000c40c3c6410010301d0b0b89903000022004102c041c01301180901296405040000c0700e54454400607516032040c1c0c02143d400c2040e0000c20300241d4007074000150009030240180000e1710680791001c04002030303045480d00d06080f5042c60280c11030104030000c02c20220501904401c020600098500c1c4100300d0000c2c00002030380142c00c0c0a0b03a45048a4400b1500004184142400c7c40f07151511602002244503081d0602001c40c090300083c0d01c2564410804110644446040440e24158010700c9a05c228108000f044010300040c0442109000a0a81e138640a00301d20909402808a01c42e180c0c0c1c0904c0c3c01d01d45410501c050303005080d0b07038007225004102d80c0e0308000c1c803001c0e10702944210703081503285115690f0740954076035001d030003800d00d000401941c1d03011004049030030050344150f020784000160501070a00c0070502d581d115400000c001003402c0d400b4690110b02c2c050b2031180e98010901541d650180c00154181902c000d40d012903038000e00e010700ca06011101d103c2d01 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 514886951 1250 514885701 514885703
    0xe09010e0a11031504140708041506081501050a1a04050f010c2109090e061b1e03270616090302210d1e120b062106010e0904 55
    0x24021000700d0305100381644000d040b9901c50880a80c1c901e4440040040c480e4404001d50185d86803d4038021000640c01001d40030703101d1940d07052100d44442e00d0f4911403a14400c0c44d00300803079031001d00055042c1c00300864003a00500710300040203989020b00b006440c01460f881060700402c80075200100c8403c0600301c1d0113a40003110720903110156040105e4601d140000c005050060882c5044250588040304030742403143ca517182440d030340e1202400410740c4d0006c3c99002c026032103000840c00b105002d2480740460000e810301c445c2803d200d0300209454134001200da06c00c2c60000401d000e10120841420440c00c00c0d0090340d10030103089141032982e601d0000381140105616a000d00e800c551242140c2401076400030920014003000c0501e9543c9030f203110f11000034a104a108803060b581c00341030b00100c1924581c000c8949140f040d00103480d44e159503070a08144036901c010a10103562018041c040703044c00f0810284090342c8239003c201e0502e5000d4075041c144512580109000e0b0b5132040d40f65801 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 514888201 1250 514886951 514886969
    0x5030c010f110102090405011e06180509190c0908060a020429071505161106060f0a091404030f020a02090403030207061506030e21030601140415020318010e0901 71
    0x21a2242e540c80c028010b0380390701d0354014102000001c0007140408121844402c4c1210085040d41d01e2805480d41c80300c0780104409a401ca00c820405032501c0c40207990700815409961030240c54520710841222583d02044012a04400c005d1102c440b00700429544480701040851a150800d0703074021000c00300d0318803654400c8030021840000501c0400780c5d44c0c5207138891281c400d14040713458010090541141c440d4264401c40507280e40b098403486c40301d80b025802801800700c5440b06000d10102082603c1e0098001d0004640004c006040e03100c0c0c000003400500b0000d01904152600600c000380051241c02194044010080075a0b6000c01c0c190704070358103090050f034614461801c08090120029a4803220220200003c0e41d9a01604040300d80071440c07055074440c03d9980048581884036404061019000303000145c40c0d075002e02000350382d8510300d02c05142055510030160100c010002250701c0160804910541003a50070640c5c2a0030302d409082224102983c2c0002c156451014030910680c = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 514889451 1250 514888201 514888217
    0xf1401080d02030c120c1f09291501020c061201030b0c0403030210090314030709090501050d11040c020c1f020d030204180b0a0b070b1e0408070f02010e1f020705030c010f 75
    0x4040c50030014219060658480000701c071142c005004010a411236041c1c3da0300b01103202c007002c4c0c0e4030000034240c0c01d001c0c040c0070315482d0744900c503402c1c00300c8410b2000c1d01d0540c41a851084819075a11002d820380400b564075000081d0304500c0c0284070800c000e00815400442408103000103600442c01e84002e46c0c010200040d10002402c0442d80e4104000c08020a14800400c1c0103a0300d0f4407074031010650348124018403642e40d03644140000358000c2c0300003803d6903440c0c06082c840b916141c1c0150f405228242304603003c0c00c0045001481089407070421035204d0244500039501260140f10b83d4141c1852400e003181064079024040b0b45044080044c43c00311540d0b010402c101d556000c08500140100c40ba805480d80c20307a1504a107100c000b69048030010315180202c051002c9100c00092041da030220505d0b00b44200c2d651045010300780c1e107208a040c010000c4032110710b900c80f0031192400d901940c6170280d44001c021400390516005801c004e000303400680c04522640d81003101701c2c01c007805510344045 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 514890701 1250 514889451 514889467
    0x30207020d140a0b1f051507080d0902040c020303090c04061208070201140d06050102070e0103230a02030a0b0a05090c0f060d020c300702130f0f1401080d02030c12 72
    0x70800408203801031140ca13084042c02030105031516500d501007600c48810b80c4035519141082441d941c142d40c100f112880c10007241000540d104050305030b817072100201040702c45d01540007505590f041c03400307900103900c08030030050f9034103040001403402601560200081403e0610001101070043c030003828a250000e64072085901c600943c041d24018442130a880d6040c811648028000d603100e2140180300d1100041411030b0085400750403658040000d68042000c0728007244c1c20003610450496500a2403030410245c1c50511000303410620031031507003200e841c001a20000315080584038120542c000c072120b111035202c2070352040c0c44000c211521601d4801c8147c00310042c5c402e015503080c8c0c41c062080600b2030510005501f1a10712590041901c1002c0916404c1001d405075a01c060f601c19850103100c1c02e0a60180d21055480c1100784010992400c1c0e2925a01640c160100034408800d0036170040000039022f20038a01c200c0c0c000d1005d58680a88000100d503124240d00c0071030040c410000d0510 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 514891951 1250 514890701 514890703
    0x1206010f14040b0f070c03230708070e04020102070e011e080c10110a0c0b0a02061b04151b0b061f120e0a02100309030f090308121b0424030207020d14 66
    0x2520142d0f02c006031207251601c7c2e14041030012000000c0301c4040310750012900361028040307034140a9501d90b1740140b40d40c0d0b24000c007610100c04050b005a065006425010500e0503c85046502803c41340d0186014481084000d116000d041d0b0310031621500041c000000c241c2c1d030038182c000d030b144142c600540000c5a401da500c0c00c29442d40d5000708a00540d040c00240d080050019002c8408140c0039110503907201d41c10264a50000400402c01032802c0209105a0345002014500024a4038040e09804150503110482c2d111844050329a4012035080108925240c50000e04682c000c03071407805032190110f00a000d4041881c2542106615005000c07503141c0b0402c03042802a4000f0015864002038510140060410044c15000a65180702d20201c40d40a11143c8040b298044c120501d0a003049a281e004c0c8500078010341e10b4040500c0f92030714485074440c00391014020403030b0039085c1c6c5442d00b00807891291411111b0824180103110010140c5e07a21402d16440c150000344010103007000c1c030707602 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 514893201 1250 514891951 514891957
    0x4030908160305061005090f0405150c0904060504180f02030c030111120105010f0804030804030e10110c3003040e07030f0b0a0e0a020903030903031206010f14040b0f 73
    0x1030303480c610074029515916079400804104490082064442e5038440c681d00c400c07030310300d64066942c0040c80c0b40049101d00b00040310a652040c003a4064a4070050504207801c1800b0080d502d100510741c0200300d002007480c00f4440c44e00103000450702000302d0040c0740c11108030310846400c0a804905034003007072807d645040c0b0216901c40d80050003008580e6004000c00b000c6d4001c07031200c40c0840f03000c0001180c55405800700451240c190746a808030303507449e55000c890142c0c00820441c03c000d1a0a03000c425a11904001c0d44c0640c100d845041944005043c2d42d8500500c0c0182e8620440030000b80c51035080810f0465800039034481c043c0b03c50700c509148424074522444e844001c0140d5840b0400a07081d9241d80044183c8000c00c00501035007d03440d04000d030000076405854001401c40c0041501c2110607802841c4560018054a04000c802c40000341140c100550f8400f15920940c00c00040c2c0d03034014810814112203040030f1200000d101e0860050b40564003c0620000000035846001d038600815 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 514894451 1250 514893201 514893209
    0xe010206010f0636031b06050d0203091e030405010f031119110712020a0e09250302030304030507090e160b0307090306020c0f010b0111033106020f07061403060108040309 75
    0x4500c00e13041401445413440d243d031009480405c040c2082100003c00b03c0e4141c2d04882d190342d50355040c52001c0403000000d40c00031702054500c0c403801c8045000c1c00b4411081e0140c1482e00350103103882d94502000540354068170041542090301d450002100040e0640a4650b13044160600d038800d00b00118081e0b0b400c80100b00300708039a2207896000106d010705204601c13507140c070036241c80741c0c00c540d200d541d0040d075001a1551145904110380c0c0101111541c402e0b0315021400070790224960b45e41e0303001b190860344075804c251500d40092100348415130700c80c0944440343c80d10800804100e4407040c94901000070600480d45042800004140814441c01c0004080d41c3c00a20855550040b80800c542d52007200040108030b5007852580300d959030041c1c1c041e00781c2001e8000690726094411005100001c2c10003810443c100340c8100314000b240440b440f800c041c0680350020582081c1d407201091910301c65500040400c041c000741c146880703c00805032a0810400e00740f054481e1128a42a1141d11040d00 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 514895701 1250 514894451 514894517
    0x1090503180102012307030b0406050a091409061b030411040c0203090102120a0e04020702030a06020f040305150402100305191a04050c1216170f070e010206010f06 72
    0xc0c200d401c0311100c90080e6a12800b600200400e001e00502c0d0800c400d40da5210050b544c0f50080010300c010b000340c07c401d03100d10000704000380d0340f40c031100041d071240050b4005035400d503540c980796504a0b4082ca07419802034160001007409142858000d8180f030400060280410008004907040151072102005c19a01c000d0007030000d4040c61030f0007980c9800c1005404d0051181302e100d001c2c0220010110340c0d0f6100d4030398680d1500341c0d1075018800071303602203001280c0611625410501068403407026003031301101803100315942d42c65401c0c498600030981202507410050501030000595a0101114a407111405c001c50640e0b01c101000344030440c1c22100160f120b040041074084100f85002055a49804481c1001980c807440c42510300d50060020643e01c403907070040880e8005d10700441105001d0080d00e000281c212940081441c02c10040c1e81d0401e004003490140324400d500f021090074191170030300c01829558035041c1500643c560520880d07040c09105d4840a03181d000903001c44100d400f000b4 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 514896951 1250 514895701 514895707
    0xf0c07080d1103040201030f0605030601120524011e060f030b281a030603030711030307060e0610080f0a02010e060c120a030b18040813051e03010f230901090503 71
    0x6410300b001a40122400c9000038038084103400440b09900c503080070b686001c0c000b44003603801c0c84900c10190a0710001503a90b4410b40018400ea01c89040c013441148188070394400c102d51508802d840345232200c0711100d039480c10302041404125800484503501c8007942ca00031074441d2485002c200c5100308410200200200c656a0f4607004110440681c00c44805024855123150f40085941103408182d819131381c540c00030000000032492140320b91030700c140d009007641d18003031440d40c8100071502e12030b00300c005d660044801c0011180900d03550f40300404480001d40005180304a61030703184e0f21031500c02414030040001c861001d0b10380c0000c2d21050030000c001c5528010b220f0303030003824075005141c55400003801c11915070309038104603080c1686e02c10340e04003403400c0c0d40311955000340c07036000403c4842c0501180c80001995a4801601c0c401240c0c0307100b000c502c010780d10402e050941d489443c0160089042100b129003410403528600702c800c1961002c648191a500c1c00240542840c40014000d84004 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 514898201 1250 514896951 514896971
    0xf060a0216151d0106030804030206220f08010605042a090914040b06180106051c0903050706050f10030605040501020702040516020f070e06010521190b090f0c07080d 73
    0xf584408243e42030a00014015003041c601507080e150307603000092646005110810041c109070000d4526205074000402d41902190000e80212040d94019103800400c40c50403c0341c08428423402c40a004150741c00c0c003200c5e02c0c2e2800d030b03124040e42c04407102c150503c030040030340e84a100d055204050207811000b807081000d4081c0045007000150703001e5420b10b03070305408203005180c00840356912410740810108180c0c80c0002c19101c03a000807440c005800704076442c074065040e151092101c140d02c44d84903140c840341e640c10407200300c650042030845589814014400c45074a03800c00300f012240c2c0001c2c041003954031840c2c9680a401002002234015007043c0070f02c25021061210f01002103251340c02c80d0400781c00428842e903241c88901c04c2e600340242041c0400c400e54071070401008031829040034054400105049101081c0c1d0440341d40214420003005545a42e001e4050804101002c44060a0724102296136509024014051f040513000001f0f45108100400707081d82e400c0d0032200c0c400c01c1040701c0 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 514899451 1250 514898201 514898243
    0x100f0905030615030c03060115121b0f020c0409153603111605040c020f0a05010203150307350a030509010311130b0c100608010c0e01020f060a0216 65
    0x10400f003035200340101d05d0181c1240c180000e009040b03445050104040700352011040d14041011108000a0341e1240c1120a12004d14240600d1180050b913035070240c0c449225009091180004005120702c0c10007400001103204039031030020b220008070b4005500c0c9070902c2405144410200b461114240c0b4030100b441e0780e029a03c040e422203000351500000c0807040701030940c03500340c1260080c2502080307160500543c2031035031083c0304c0b10800d401241d000c030f41880d4240d071400495120807215030f9000001c000f9444c00018031220003141c16001864070606144d4840c5140d58030422485110303022a000d07400e0b041c1407099100721001c400c01038078450095810000c0055002100003800310b418050707000b010510000480d2042e07148807458042160501680c0c00d119440300402e10054072a41c1190615860b02d4441d0000500040340001103c029100024000c5000303030380614103541007650302108540d00810b0f2a640145001401a0b40e03c828054039003940c11140400b40c201e400e000e40d16449620 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 514900701 1250 514899451 514899481
    0x70216090b0108160c1209030b040b1008070513020307020304050a0305071a0309211c05010e0603010e060a1107080a05030703060b031905150405040b070815100f09050306 75
    0x1c080c1c1c0c480190707948a02040c4a03101e4801200400601389250130400720380802c0c041030412103546400c0c0705840d0f42e078a864900150a840507540000f00c1b0b03082c400c070885550f0b41c000003004250041c0401c03d28060000d0300e04201c1c05100c011207a00000060500c2d40300340100d401a15001f494042020740307038100b050b503a005074081c4c040781909941130354085c0c150740c1054904c00c01d410401080032244100e90240303140c40c0c200c04481008400c1c412200100c1d1164071038192121440310000700c075072402c0001c0302c500c20050300142c02a45800001650403002082c0e06a01020305480481c031010151031403001c40c0f0651802501440001c50103162065104000710300a001580e4140665a294840c1d000c0d14403003691200095a40310300c44c0c40f484903494002903804107030050441643303400b210106043e644111004ca40800c0340d4810003000320b8102500a800501c00783c44080050403040214500d40300045c800700c1840139113144542e68601c141c4100d009014042d0a49640d81800502e0001300e41c = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 514901951 1250 514900701 514900721
    0xb07050709050c03160315090e0123040203030417030f070803090d090f060f0513080f1006050307141f0914041a0405091002041d01080a0b0f07021609 66
    0x1801c01d00400c0f40f0243c6802568043c0f4440074031a1034018055005a0040070807241008803554141e200041b4001e6510030542402c007904004900d030001000e0141d0f40314070340794030485a00407c500b80409078900100355402c1d41c002101c1501c61803034000c0d4051035405102c800d80ca12050019440003041400000fa50041030b500c1e00711070329006181000c1d1070130b5040d40120500c007030821108203c014803030201071440d524103050443c17801480b00341e07240c2c8041107a000019140c1c040010000a1042006920703211641c0481c20000c650800b00020344400e52403098404800b01903418511982d0340c0441c59240b03a0149100490401c901040074201903070070b11400c01055401030b51414942414040d200e00d003c807a0034083c1c042c59106003000000d02015012220a1140000604100070030b84021300217007000180380902c0161554147d05059416041f0049582003c00041d0005140008a68100c0b140c1000c18a40e036940e180100e150130b9031101e211040080c0094005407a000035032100d4468 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 514903201 1250 514901951 514901969
    0x18011403090a14060f0708060a181406011106010306090221010606140c0c060c07120606180608031c0f0606090f0e0615090613180b0306150d0c0b070507 67
    0x7401c086401980c03100005c49003d4107560300500001d01462152040541c4044001c01b200d02d65a11140c14441c10740b164001c050311113690b400d10040c202c03060a2071070b0f8020024079001c9804c1d41c60028803600c070301061000034103d545490728a0b04564800456900c010074283c0c00203100c19400c0700d0280a00031520521000c10001038a81d8070740e1080134100e90b85454120010705001d0401d08c1480601e9218000c00e401c00d0203528804180030000301b940d11003546c052080401c2003403c009104890308001c2e100f140700285040e6080007110408800d80b8145c2d98001048090408044a040b000c0c02c1c1811000845a20b03160000c90040c0d00406000c09541d2208080d0a425403070381045101910152191940080182c0031106858a242d0041c0318811010707003c00d08100c61070410030b010080325000b00c0b188000c000b5000c00012501e00c906130090310124000e00407810a070301541846c0b4003900c9894028505662100248111000c03a540140b980c185403075a1030081e030405503120030040c0074902030 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 514904451 1250 514903201 514903223
    0xc020310051f0e100e09070305060c0a030b1008040f021f09080f060421050f1204060c02010911150405030307050105100602010605060901030c020f010e03130803070818011403090a 79
    0x1a500d04680c1c0107100b58880c11544004d142440f1070b01d0300c841c0c00240700c3d44043c801d15002100040c0d042c40924011410b00701d0007511400c6d9000e000d42650380760841e10b4000e0044104070b261050b4040f0030150040d8200d40038000e000c2041c00440d100030b42810307a926852024000320591183d0003079100302281d81d40c0007038840d9495080040358440b002078174040d18484102100042480000007000000320490a240d0b180869508082c8200e800100d01c05030f10503905010042400302500420300030700e070a40b00810514110381c0d5500050a220a4124090300c20603084401e1102c254085902070000241282e803985041d1030840e001c2c18080380c207904500000c2d00c0008805005010709410780d90300924403400c0140c02001180204603400d50002148130342e0348108510381e4280b14000d9040100809940d0781c08540312800c030f46840c81e80c0310061661040080c400411660001c2d2007524500d02124844041356000403103080f40700c2f40000c05480d100106200d4880ca00166100000c0e106d11110f5070 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 514905701 1250 514904451 514904459
    0xd020d030b0d1104020a02100903031a090702060f070203070c0902210f07030203041a04140706090503060a23010618151d120304030308091209100c020310051f 70
    0x5103410311108010840f5005800031401840e041c1c0103440c4c401000c1c0f048070314040310036042c2420349840720000d40210343e5801e100380305120300c034040d44c41c5540300781c84450160401e5000256603072001050b000d1441258004500c4251007442111115904800c2240c00140c559003070400a40c42440c5501e81c2500b200c0c0b2040c04002c04032600b074484c040c814030f29040c66a5840f0258003039440140101e40200d03035480d41d02c000b03002031041d00740141c0c02040c825185031058110780d85848000c2c2c0200040c4680c22030104080e5074002a0aa440301e041c04c0b02013940c07070301c400d100301c4280541000b041c3c500420310000b08000354008488403240c68104030946020703950311a4280500081c044100004071401814140700220b060040d20210000d070a18072403040c0c030189541544c100e81c0003140003944410500121801c1005070b5088001e80230390081c6045500e00004449032601c45000c4144a00701010200b5940c0600c03d110145030740c0c0d0700c140060b19240901c01030a000c078a044c1240d2100c0000b000c1 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 514906951 1250 514905701 514905709
    0x3120c07180b0904030c080909090606040b0a080703140a052a0108010b0403030305090f071d1b0a0c060b040603080c010c0914060c01060b1b1209010215060f030d020d030b 75
    0x40c10092024151603e681c540751000c581e030b04075401041e1503140d402c01c154982610b8101380305108415000244c40b01e8100720b010002900c2c02c200105100e030210020030f00c151400850910201c0f075100c1c6010b6908003091003010b050a11341900030b011341c012141032058000c0c240b01d0f050303120700c00b500f42065150400401074034055401c6c020b401203018103010a00019001e40d01040d00030400908544079a6141c0304260315100346500b00041d1010742c042c9466042155801030b54000c85d03096824400700c4010920f034034841c099800c80504200e02c07845940c06018266001c4451440e01410900406031079080c44078580d40300d2411542c013503280c4000c108041c5d21442c001000d0701d6886c02d4203902c1c00620b00402141b6000030080007021b568403e00000ca150180c0010004a100500c02c0800d1401d8048030030b041505940a5030744c4140100a12140350ba400b00d860728450810004110564131004c01140c1c060b200030301e140f40c040c0b1402070808801c0c1d07000684800c07120b48695040c8034150790a4140 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 514908201 1250 514906951 514906961
    0x1090501080d030b03031309060504181a2508071707080105100e061b0c060c10050a09050f060a0c030c050904050903070803011e0b070302100b03120c0718 68
    0x28080b90416022001d415110740c1052026800060859003000400307000e1008030b000356405410415601c540802c031504060044164942c0517012500e02036141d900c503966a035165003000448200003900184e0407440000440780b203e6104050300715034100544001d4000340303060721184049001c2c1001c11003903802d600b0b180342c0f00c0c1d40f00e0750310810680d06e400d05021f1141a9014074406000c0900040712181d103c41002d4080b01500030188549401d000500c0d41c10301d1105081c0314000c2004001c000c9074520f001030015004049000c00188550b203081e020001002404001403603405401c4200d220480c00003042800b80030010003c10240003800003d030202c414110384400410424020580b0710b103030a5202c5c5d03611140c402c0c240e07450103040c1e6956a645034426040f12a5481080134550200d810300507140010381051038601d4a442010740300a56501454442190340e0707521190500000e0710240403240340c10452004150302c40702100011502c0d0411406403604442440100800038003141c01340c = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 514909451 1250 514908201 514908209
    0x1b030108010e0c0f011b02061903090614010509070e150d0b0103050106031e1e0c0903030f1701030b1003150f111303080a030e0d170f19180503070302070e01090501 72
    0x1a074103006d8024620a04400b503071002c2a40c2c4400700340302c0401c482050144000394601280d8002a0b8030509241640072100f003506002c0034060700b803005111540720124501e40002c11803c00c2a242c1d1040000101003001103145401d0010002c00c1600d02a04650804100786009890500103a03889400071822610b54a0700c076a040c0d04240b00d0f140c00d05105500c003120b03c207421441d03200c100d844840c00405542c10b0007807510001b140c0940030414564086460a101082440e0048089854081007640030806000c00340c0350714441000b01e8040d03000e4041e5000110340c80a5000c40d0351103240e41c400010084881d490782c00e00e082160040192580b035003100c046600500d040032805042d03844010307945d0030812032542415502c030841513400108000c40802600140d4403960011241401c0030102c102c0500705807001c018260503ca2104401c3c032909060018031040000c6001421644074000f10384098090441c0c0000a02c80091583c0441c0c09001d95001105082042e6603590520045603401d110f = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 514910701 1250 514909451 514909457
    0x40f02041104050103142a04080f03030106091a0304060c11010f06090605030c0d14190c03140105071d0303070b0f0f0f09153c0c0a0c0206031b030108010e0c0f01 71
    0x100d400d80420f0303400c1507c0c2e050082daa1600d08080d1215055468101c00d244a40f4255001200402440e0340c4510070703d0180c036020218080181c2c107000030751f100b0f01000e440100400c0d124028003034154407a5884110b680c8003080240b00002ca80391416004202038041c54407540d06010340802c66040014040004500292441c500c80402d611041c2191140c1803880d0142d004442c54564a00c0c2402c08007801240a201000c0c411465454051559140e40c2c840c000264106070802240b0703600002c91a0344c101120590228130002903001a04510950b000240404030140921002c0720700844240d11801e0f40c1c0100d64543d403202e001c16600300130f00b141c502415902681c945107491906c10b48950b0821954814101d0b041c0201d5401c1000710003014004420307400303056881014004840081d50028801c8465514048601d6001001e095a8000107405010008081603003114444d02028241c20300100032512941c403406414040c0c420251102c541d44540c800c1e5081501d801401e0303000051050b1 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 514911951 1250 514910701 514910731
    0x606040f0603050d05121305060a0c030608010f0b04112521080702010501051005070803060d05030705031c0203010f09090f061d060a0c080f040f0204110405010314 72
    0x10400025000180150903525219a070000002d9400c014101020060382c880301d48401d0448000ca03900c91000f4003080490030340c0b0041001040010074126001081840c0105031004900000d501409040d0b10be0159507203040c50751048099154060a0802030403107041c00084600c0707403242d40034085c0d1021511710400b40c001d03046103003203800103890465114a60000c0003054441c020207225080c45d040001190307041c0e0810910302d0717080c4585805001c0c00c48281706000c90140c00103040e8000c52800600b4401c00002003003041d62850090214158064112035960000d4a0b01e240c480d04100044540c00d41d0b465030441c0da001c1c2c14000c1d01d050703507003000148454a25018050300070b000500c00544000c0f00004600d400720342039000303070f0304401f00c1c2080f404803801d42000d0a42ca0000014000c07140c140c944424008505c0c1c2c40200c071a005070740d200451700d10f0307100c60400709460544c1c104001d41c05403911105d41d850980c0f010281c400c5541c244c9081180786400c25220703a840c4002c0360f000710381c00500 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 514913201 1250 514911951 514911961
    0x803090120120301030501050f3c070f110102040302011205190e06060f040228110615040e030a0206010905151e03120406090b0a0302280e01020d0206 66
    0x468580300c420601c0750000700c02540511a541c02c007000105012a1202e0000052040c1300e024080e01d40c00c0103007517540700c3e5107191001d22400903100c00410300b004084200040c5500c450300c50118111400105004429070410340c0c409071400c100015680046801e000036241d80b05018800d5404580e0107071100f03040d4180c641c80b0b500040200502c50407510069580c00c40285d200c1e803050b000402d0a0303000401150900e00100300342d45d4400204244114010806251a00c405403002260f8030103001c9203002c04440031001385d402c15041000c00c081c512130308041050144100030740b200030f00e1041d10f04202840842c107642e6180d1080481c1040560301010040240c0c004e1940243e602a030050843d0140c44c2c0182d00003440307800451030b020081100c50300443c03180d1030240030302d20200e40aa01d0b15840c142c41d004000d0240c0695104400700303524042010754056001ea0126070724040070f01004008022608914000d0b1003d079102040015585c100700e00300f55000041c1745912049540080c0200c0e660 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 514914451 1250 514913201 514913207
    0x10816050a050c031908011a22150c0303060e04051b130e1612020d03030b03011b02010e060c1e0f070c18140c03070818070f03140708030901 62
    0x3618207041080010420203800311014005088180001404546030310b812420041580307406801694080d140700503c1c414050302042100c031513242c11380c9019550015000c404d22032008980c08403984591494588211030351041f090341d0f02c0c80c403d03201000300c00d4842e036052001d118200c600401503488158480660715850004121041008007c0050310141384858005e4448081c50003001c4d510003000f201c10701c3e0045046030082c0503145480340d014001900055502400890050f0a05035121580b0155803420740210450111000c0d007001350100d0300e90001d009203d02124408030b40035210224610300740100407110307140398201d0302001200d490695622143c1c4018040d000440c010040c440000d9064410715005000750f55400d403102071303c01c181c0300503103003100140007070781c8504000c0156400080003900e07040045480d0026155a030b800c280703d820080c038242c3e10310a10955030b00243d01808640c030a0180e0784544850b040720581d4000c1296203048034010803180d50024051a00d942d48 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 514915701 1250 514914451 514914457
    0xc0518030f030f0703021908040506070804090518010506010c0309060e0a030218060901060507020603040f0618061b080f0f131407060e01050328090c0b09030c01081605 74
    0x4000c0c1618144450038101918507440300a00b4002600040744100074160140a072480041c0c13041404180c1038016034808149100e140562031040101180718414080044103441c00350080410400003801c00c01a81d0914000444004480c0d60a0100040140d40705541c685031003680758540030301c081e040c260140e503403040c142d01042e0400400310002003da0740300050010719500131080c64074142000030900080b0b4005801c40c90500c03c04005000c0184c940100b01c0f42c2c4240c100c05c0d40414400c15107403c2c0c000e0080307850308003105c40300c0080801c04d1010302e50001009409011500c680301c10010406e490039081141d00140041c0d44800198045254450965016482800c85a1007220039030726001c1c3c58032070791a42d9150354030421080c4501c54004903402460707042400c2c40c9066240000d9440385d09180750607804044160907880c080c440400d60409003003c1e6003c0ca110b01003603100e925a0307400c0d42001c01070621070b2086042d0340f40b85501030251a13000300c0384030702c0c0c04d00300809111003500e09134 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 514916951 1250 514915701 514915747
    0xb0901150512040b070e030a03020318011e02100b0109050a0b030603030f03070801031703040b1803090d0506040c120507030f230a05060a0b060a210504150e010c05 72
    0x1200308844102d0720482e5410510840c07107141c181d0081d04000c0c0b801040a200b40c83c1090096111140290101c1d40000548280504c20500381c1e00d071412680c0100d42c3d80c404400301c003d406d000c0c84002500e450300030030403050450b0581420400402144011103200840d8410a41c004074001024019021010b009540c400b40280885c0d01c0e00c0401501c0c4040c65000b240c00600181040005008020101c421000c00c04685c42c44c4600b907040a40b52001b80351030250032120403030700300d402059400300d00340251340a00f50020002941c00c101400c0c66911407908072411101d5800fa075101160f0050a142d548d00440d802400800f4194107644c0c0f110341c060860001035404020a80c42d04190700307481040c8000000340c00010786200e10b13851400754130340310000c0c10300c00800c0d04140c07612107240c4901c0192100600c0501d81020701040350741c01c61548060b001c1034416001e0602d000c102c10310a00f0b40c1a00007060b00e041c0c2c1008420f1304048041d0072901c003900044002182088142c8001d290f20301c1c09145c035 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 514918201 1250 514916951 514916957
    0x10b221109060f0c0106060507030e09070e0910140307060e010f030b03072301020106080d0c020a0e0702010203011a03010b0a05030a0b03010903120b010e09010909031106040f060c030b090115 84
    0x7100703a0a00160054114180c07105040500090036085507030f0a0080200602150a001c0e0800e1180d5501a00360004901140d005098150000780100d00c60208848042c40203001c013540390800f105400c0c134480c050300404400048054114a090800242e4002211010707650b50201e0100e401c01107076841000340000c010151290014a1565410f00018005000082101092203680b502c070b02d0344000b0310305625041d6403600004114201002c00c194020502d9031801d0003803101c076031000610700c014a410a850039107181040003a0140c0541c02141a10203034050344200382188071005000340b03c00d000d8112408018001916801d00440c06160801000000421044201c902007821180701807000d8000805202c0d61a000c000c3c03920444240c02400c4ca0484440c3c0341c1039020403441d80040c0300d05003540f90f81e440381c2c40a040c070503614030340c10861110035241603003020300740401c501d00c00030015505503150841c5224090700910030f10101541c05459145141e207019411744c9060100007000081c = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 514919451 1250 514918201 514918207
    0xb030109022209020322022b050102040f030201020f060c1204020d08030a062c01031202010912080105130c0c0f110a09090506280203040309050a0801050405010b2211 73
    0x9220b074802440e0150039818401a00da01d820240400502c22510601c86003014071384c00d00c80540c82c0c10702080620b0f420581c450a0920090442030440b098002019040b54800318011a2440d6401c600d82e0482c8e000340e08035012a4080c184564644e1400c0d02c1c5154607034820000300031041d110201d0030ba80640024040180448030761500341c2141d00403500075001b070340d945c101844200f4242c85011200d05494012400c0d900e004644100c06030810700019200581c910388001c0b506201b5080382c80440c0d40001c1c1904051800400070b06600070a002c0d881c03164400b8811414001001d1140802d440c605a80d4010024039603260446818900a000e450010444210340c0b8151900c3d00a90300800e44d528000640d4105ca0400a003800000340181440e00c03000d8a00c107400181c0302c01049015410142e0050750f0307031038070314080e140c059550b40400d0300400c18000c0001c2d864010340c803c6100b540160024001400c14201700000101c00c40c203441d140c41050300400d80c603419a80d0080c0d80c051141c00000746 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 514920701 1250 514919451 514919497
    0x2130e06030c1f0f0e102a080403030305071e180b0a020304030203071d0105060d2304020906031c0f030204180b0109060203070c12030509120c190b03010902 69
    0x1000052038103088201c1091500c000ca0540c2c49844c041d003001c400e2a000b00460304403000554550415018542042005506184444192420080c02c1c0f20510b192114200851501c114160424801034010a1414001a4406000c1c44d40c8001403407903000c1041c103141d0b01d120241e400c2c01d21700d61780c0ea0002c2080e02d408101a03405c41c00070039210060783c0095403500e2851040610f84042d6410a8012081a050180e01c1300c0c010a4100d056560841d8015100c0000288000080001d164040103038400203080b00b05c0c0c8071480d01594041c1e8000d4a00d45066951035060503965100c606101c0d229007180c00a8200651160030646c0c04000c40d46400f61625986001c4d440c0d440d40320003445468550f031402e0320000d0350307048018030000345114009142420181e0320b03143e40305103141c41503941e1000145c1c0c0780d0040520820844141da0300007800d406001c0000c80740b030759a0b8901c00003c2405044401014a032215000040401b112981c5400da4a10b03824056804007a4000d4011000d4816290307440c04 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 514921951 1250 514920701 514920709
    0x301120f050a110a051e01050c0f1b04050a091a0c12040804090c080705070201030b01050408030d05090c010215060d03020106150206160306230625120302130e06030c 73
    0x481103002d01003e2400c010380904000400040340d002c54461210491500b81662103560144010f003000d0800985030703070450050302d081c1100e1008000c0036014401325810401e8a0b0103055072400e10030758003040250740e2080410119220311901802d12407a0b01c250403500b9140791030f05035226001c481054142101007890a40c4c2200c00c0d01d0840d4600404a014003215400d44210090300403140307002c0c4034a0034094006051440303a048068101600e0b0079641c2a503900070b2088170020940a0226a55101444080001071406a504020501078801c07210320f5580700040c90030b08070709804282e07800741d10b0350000c0142106542404074199500c500340051300c112500c1d210032000390b80780c02501440c82c01c103030000d05040c000c6c00d40c1c0c0103140c50b00900b4000420380e155028250803034042d20007440d440003400100c4a000d0448208102c1012014004241c8a0040981207591080d403c41c2074044070031105809030700800d5468800c4c4045e40310200300c1020100c2c0300c1038000034003405039071165110340041 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 514923201 1250 514921951 514921963
    0x40b040312060803040311060307090303180b0406020a171c0b04110408160807060c0b0414030f090a0e01030b060d031205070e01110604030519031d010507021207080301120f05 77
    0x2e00f103038001003410410b114a00e000c402c04020704807403403403440c50b203607202900c200d51a020190401c10381254924805040e0b40564001e082c107043c2c465251540c410009651303000c405000c07101c4d16450100214010303049030554205101007440c006440b900c2c40d01000c02410400082584181c441c041400d0003880f0707000401c043c2485002034620104100d004242041c1154001071940d80214010000d80da8814841d03198141d10200c0c01c4aa41c6071400d01441001c200c21050800d40800110030f104076460000074203000c0f20669040c6c8200b50b0358010380050303100034031015105900030310006115103080f40f05990b05a01c0703410003110702048810035030300300d400480700d03840801d03004030326140150f0b0404400d510881410300101080e00d081c1e0f50080c4680510001d40002c0c14444003110007041c002d4004000b00103031039045080d0b401c01c206299000e8907082d9054130260140007007880910420710103c0e441d2070b41160300c05145902e030594102580114100a60300c54000502c48000604c0030300107 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 514924451 1250 514923201 514923209
    0x90301020909010f1d0105010c03030203070c0507060e0a1e06051b07060c0c241211130e22031d04020d0603050c0d02090a050702032803150b03040b04031206 69
    0x2400c1104e030030103000302012003a84041444408a19004101c036a0380b05403d030b4921689864090303102c1c0ca4960080d43c1400c04000c005010380142c0401041140d4446404110500119000d5140035500c0301d0010486140e100400214205a141481501c0c003078170080c1605012141d6506281d031198845030b04007145500008000354184c1d880c40d040c8106510000090800d114400404c5038034450074441c0804d000300c4103001c6c440e40201c00b9000f9102e9500565805140306030b129a100f402c00441c09003902d0602850051a05e60004604440f070301d01174a184031800c1603243d01180f4010349080e11152180c2c0710100003082403d14424060f142c0c1d002820b98a1810300c00400c2e054110f2605608205000c080240508007081d000005a40d90700310342604140d555400084940b21040d08a0442c810185035611810700400501400c001040001044500b036560400c44101d081d12030804c000701034414201801020f02c003103404078000000960700700340b0038100f041100c15400c00000981c0c4290340 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 514925701 1250 514924451 514924469
    0x12040f0e09072115021204060b060c030705100617072702040b1e0f0d02030603012406090506072102160f0305100603020a030b0702030c01090b0702190b010b09030102090901 76
    0x95440802010409142a40012407030075410103101e956031b07000c1c249004101801694031034101405070f441d00303811a48010740701c40075a43ea80c185801c24580c1c80848480e18621503183c030301d0001c2e081a50841c0c80c2d401d1140100070388031191601c2104810411aa034a03840222881c800c1406003410510041000303100440071251101d00d10b00051914510003101030081d20400c00ca403008007100a401c8074503112001e800140c5984a2102017401007849204d14162030144001002407803181030040400c0343c2c1603a80d0600f1180e00e91090120341c4c011010014110b0031681d00706041c2c222946a03803180c00b081ca104a03508110807161800411450343c0c041b1100e4100c40f034040c403e0110a001c06603500c1e680000034450b5074615400b0910841c03052101418231b108810120355600d10a204a58040301403500034094600c5504006500c40c4d010345222002d0f00c01d1040d02c001a880141c6030b00141c0c0d40104220b41d823a0301c1c1040034a4154020043e99525543c204401900c5595450034240a0400341e0 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 514926951 1250 514925701 514925759
    0x10e0108310615060905041d0a081c09050a140a0f0b16050c030d02090a030605151c1a1512010b090c0c0c011d030102070303050912040f0e0907 63
    0x20400c00b04841501d601020007012400303040c4002900081c94000321081a5000514244125011102c4802a000c69480c44c007070100303660f0601046402500320401c49030701c140102c130b42c0103445101722648960300a10b40d070000300040c4040381c41803802c581018841360035600b00288680d121101c4400301c0c02c08552400382ca500317100140714401d08090a003501410702500d801d040c80f80c0503989000365015019410340004007400c45449418030f00000316808a414031460811034103000c099020f101040d400b50304244142e00c40c00b00700401c02c0820940000000c803c1036244c802540795032034010046d45443c15920b80c902b0040c0c0321085004d45044100780001a604003c40800078200c5001e000c419807540c01380480d45d0242d1340414150241d074401d0812200807424108160141d01080b14070b80c1c0d06500c003042080505415070000f62041181d9000e480c0d45181c82c0083c820780b0f0149000e0042541040d200520031a0400b080007600031103443c040340c050590f25104802d508000f045404038480e204 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 514928057 1106 514926951 514926953
    0x30b0a0903030605090a0608060a02210601030e030c01050f07050a080705030604111602030709061a03041401180507270b150c030a1706010e010831 65
    0x10301407910354071b4005071140003001540b0481c091402604001140e8050a01c01c4400c280ca0f014014a181e114620303a914500c00000d01480c141a901c0d00c95030300c00b031000c10140000b400d9880011138070b85040481c5c9941e0070805044102449000c0c0100400f658110f800c640d440119460026200d655050018001e008259610303815620300181c10b680e511400c48100911b140240c048440c0c15135110952411582e441c0f140c800394020851858841918260095070094056000c44524001c0107041500f15110588800c0f001340f0540c201000b080410b000342801403201e20284280314010310314601c02c40324500782c04801e00d99a041e520b4141d80c1d030159502c6500d0300100882d5202c81400c4c9810366039610800c251404219007450000c1c0404801d0a03061007000c06940320340c1d03810304100040d80c01c130f840a40f401210403145001c00b80b03c1c011090501642c0c4110f42c444851000030303 = true := by decide +kernel

theorem cover : BRFrame.Cov 514748201 514928057 := by
  have h0 := BRFrame.cov_init 514748201
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514748201 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514748201 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514748201 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514748201 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514748201 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514748201 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514748201 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514748201 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514748201 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514748201 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514748201 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514748201 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514748201 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514748201 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514748201 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514748201 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514748201 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514748201 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514748201 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514748201 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514748201 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514748201 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514748201 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514748201 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514748201 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514748201 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514748201 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514748201 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514748201 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514748201 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514748201 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514748201 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514748201 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514748201 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514748201 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514748201 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514748201 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514748201 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514748201 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514748201 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514748201 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514748201 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514748201 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514748201 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514748201 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514748201 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514748201 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514748201 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514748201 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514748201 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514748201 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514748201 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514748201 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514748201 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514748201 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514748201 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514748201 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514748201 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514748201 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514748201 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514748201 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514748201 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514748201 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514748201 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514748201 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514748201 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514748201 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514748201 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514748201 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514748201 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514748201 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514748201 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514748201 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514748201 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514748201 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514748201 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514748201 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514748201 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514748201 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514748201 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514748201 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514748201 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514748201 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514748201 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514748201 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514748201 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514748201 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514748201 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514748201 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514748201 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514748201 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514748201 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514748201 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514748201 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514748201 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514748201 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514748201 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514748201 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514748201 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514748201 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514748201 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514748201 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514748201 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514748201 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514748201 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514748201 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514748201 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514748201 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514748201 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514748201 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514748201 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514748201 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514748201 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514748201 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514748201 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514748201 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514748201 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514748201 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514748201 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514748201 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514748201 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514748201 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514748201 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514748201 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514748201 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514748201 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514748201 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514748201 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514748201 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514748201 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514748201 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514748201 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514748201 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514748201 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514748201 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514748201 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514748201 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514748201 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514748201 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514748201 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514748201 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514748201 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514748201 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514748201 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 514748201 ≤ n) (h2 : n < 514928057) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
