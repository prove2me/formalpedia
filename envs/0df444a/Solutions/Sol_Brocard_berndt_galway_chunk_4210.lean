-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4210
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T11:53:34.899843+00:00
-- url     : https://prove2.me/submissions/4ed892c0-e72f-4302-94eb-b67586220ddd

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 757014388 ≤ n < 757194244 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 757015638 1250 757014388 757014409
    0x60e03030918061207061706060403060501031a06062a0f0d05070c170c1207030501021201051e01020c1c02060406020304060206010e04020d020127080105092118 71
    0x150031546480b140038506076076559540c4070300700507644c68048403410b120150341c40c1071921859010803420007078041092030820150381d21040141440e45040ea13681c1d105400c07540c09034800e13038080b0015003c80808403807410003550800e00481d00a82000e2580c0722403842074140144520b40700c048490b010009800030b022003100a180722058816215105001070500d034045a41140e41e103905101c08a1200699211400c488803010020244800d10300b0600000c0b25604220305e8062091050010006409000400000a8010000d4040c1d450300042c482d03408a865400201c46254035503036401030341e0020300c240820341c0c1203d10001601c00c10070b11500f010000c64010390846000100031407a907800100038000c507805a403c84406a030b0703401d500702c010309099a0003940300c030b9216003140166204518011039110605034243c503200c0c0c3c181d0b003c041050541e2104503242d4440b4200207040d0350600c0100d00401c69551854038a150a8100300c0852080c03010740f00c6007103c2d409219101d51501c60481 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 757016888 1250 757015638 757015657
    0xe030301050904150e031b03130b0a0903150c2d030f14040f0c12050d030f02040510030f0b0a060c23030c0102030a060b120a050a1104090b030d03090c060e0303 70
    0x100311701e4054684043e107990121401492140d0303100200540003400104031071401c1d100c010b4402c400b0b400c1c48442102a07000c01518002c01401c2e44020012075500c0d9a80e0103403485620b400151b046070070001030100401c814008000c20003c52904d2820703001d04c14400e9521035240340c0016200c542c03141e16402000010400303500d0390b250034100010840c0080c500340000c3e00415900c150704d9951801c14402421049009086030081e00c84200243e0182d08a8016042d180c07001506043d100d0300402c0090f10003042e5800007030f4075800301951010240c45599021841030f60b100c0e844c103082480c0501603055141004005001c0d10010280302c0301a00c44880d452007003c800c1d241d694000c903030110b000c6e41094072014041480c0c031600145907600031044079006000044041d455130fa6086a080040c41e00070310310688981c681e8880b001181d480f1004201400c4840b0340000e080060800741840e00094a10b01c03c2414600324011012803001c44c81c0e070084400d03600e000d01410102d040070070b00b103020301746a6 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 757018138 1250 757016888 757016891
    0x207090933020a020618010507020a0f030905121c0e0312071a010b130602150c0a020705060f0703031821030204090f0f0e01050f22080f120a0e03030105090415 70
    0x203c480c065800b2400b90301880d00c0b00030001c040507102e0003842c200c0d001a65640003690142607070074002400260004400d600078140080b03026542c80100d4181c000b00b0b914002580c101144480308a40c06030341d814600210740c50031400c2c803155040826234495199000511180002c42c00c0010098900d030355062052902e6409865540e50315012903d681107584c0c0d0020244c201a00454107501c006505112403c2c14420307000c0c11b8484403c40ea85607400007011204500465a01203010703201c00b001040000d91156065075600c034141001011130b0360000c041606000b01c52028404220840003100010880c168004881110380b41c095000303110742c1d801411128100b04008518401c5548450b2640807907450900000401c0404a402c0fa0000c944004450350710030007240034006034030401c14280104400c004081411519002c3c1d158200e403006041d46400000e940d804250300340103013030300298504818080d0078960001140c07640414020365000c0c6902c00e00140504c080300300d0210306544800030 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 757019388 1250 757018138 757018147
    0xf0f071b08160201120509150402030307060e0322142b05100513020901140111060a020a090515030f0606040308070c09060f051309050a0b070e01020709093302 70
    0xb4a03507140050040280c0c08207150900a85a0407064058184245001d502501d2052507121510a1100001c0d1007642c0512045c030080e40010390030301c1640404054000119156408060640c2e8500c150040c4601c400d20005420884e40c01d103810100d05c508002c807407014080098641d00d00f000403440320071050b85100210200107120b800f107034800d06d80c080c1340003d110380e60310300d6600110500c410400a420250400040000c2c5882ca4081c580200e41450700c92056003402c49200e14180054505460710f1341c0c0010510355141d0081003040040600741c2d040000010f0440c000c0c1702c03a0200926001c8449400c20001c2d4050340c40f00115030255610981c02610b62181d82441100d13109140500011680382c8500403400c1961540c1640071036400910100200309083c2d0a00c010340140c1c00c04031004d00c00d1450784000240d801ca1001e10800c02d0b5036030700301200000400249001d8075580020003503450128a5008a1700340c110f0402c1e10016800d25071042c000c200444000ca24500400d090340510105 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 757020638 1250 757019388 757019407
    0xb040305030609010b040e060d0204150308040e0f0f0c0d140108010c02010501060e030307060906020721030f110403020405071421100e040f060b04050a050a050f0f071b08 75
    0x9540108003e441c2200e1980c1c907450b001049200b0750041c1c0307070440324082c00135007589040703020031400510142020980840c1030000070200c0b54103070811140a000810140403a004c0c3c0f880803640040940c982c0c0c0c1003428401484141c6420150449100500008503400c4400c02504058480200010b42c0009507030340c0c188071402040881644801542031200000d01c06204d80381c541010000140594075060250791070310018034a000341120619001e0000001048059203801000d5031240d201d0400e420302650000c04445080c1d210b2500d052500c0c2902280101880690b81030781e0381500d0000707540c2c0b249041940c2e51030f00204605a082400101402c034080079003003401003403035600f440d860691142c40641306000c030240500d000a405030030008003c10740d200e01a46506009150023b200200c0001003010781d02c0c12544e04103420340b208240240b0800900c42e169104803c00c100e0788003820146c0c07000b405444d01400c0c01c0304001808807621401b0182c80380c0c8990b95a806030816940c2e81703c94 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 757021888 1250 757020638 757020647
    0xf060509060d0f0c06032304020f0d031101020301293a0e0f0c0909032a0102040303170106032d110d0b0a08030403050c060d020d051905090a0b1605070b0403 69
    0xaa110340c0c00300d4030403141c810b80c080c3e601007c180210b5005000404a03800c01d0144170b041c0411141c1542080b2281754000301d404000c0c4020740c0a49500b1950b5400c0c24200184421464144280c8640c407034000c005416810603100800800c0050b104410682d1604504580110510703402404091524080d0100c41c4003500040c90400d0210b8582a10451140751040004c00c4d94100c0d16221244c004001405000207050b1200718403076681c50f032413000340101c00402c81c22a009074000310046003101d0304a01d0315510340701a4038010091f5143c24000c14540c0d5103584d50b4a808000b840811541c480024801c2d102c4c82d4200340c00307400311020901d03240c03215046400040c10b90940300c1805501020008900310001104407016250803a00400903c1400b130140030650307010340a58028180c0c01e100c50007c142050090500445007000a103101401c00010310301211030141111080c0d911103220b81c40054003840d8841c1d400080889400140b8080d14800e8501d8070134114010850100e0034100000c06812 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 757023138 1250 757021888 757021901
    0x30e060a0309050708070501360f061403070e011d04141b0921030f0703020c040e01060609033203070318051e0301060306020a050903010f060509060d0f0c0603 70
    0x40c02110125036840c00010303141c0915000b47c500040b070050f480304000c0106528141403410250f10404509440071080c0c0415800d80c021104020108200b0000340b40d10809911f01034542f0300d030181c0fa5044c160320140800c5c00105841c0d0510001c400641245501c809034641e048c0d0317000c1d0090001c1d402e0000708004c03650044640d0100c1c1401d00500358000e15000c000e80d041c200d4040c0014403c0d41030181c3c04030350021501d0002500c2d05c02000700fa01e01803500009402c5841c82900108105040e00c0c0c20401aa8415805251030340e1604104118050344400c20314101ca4012403000d02c034440403120504181d40011009051001c04184c4c0c00780b88400000922806010303655084462030140325448039501c451180e5039000a820101b540a8102e802a018800200400008607917a483c0d641c1800c0c0e1b0850310041000c2500485c03892041c3c1820b0181c604000242e8034200b290700c1c2044c0021f2807a00025042c18010040041100b0402c11020000d6841e65007000c81030040076900c03103009001d040c2 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 757024388 1250 757023138 757023143
    0x11010e030a020115090c081f0503030a0906021504020619020a060c090e0709050303070b150a092316050a050705060a052514030c131401031407020c0d030e060a0309 72
    0x13201000440740010320800410001d5030340ea0a80315240c640909501a4900c81441084401c1e0600081c1c0e40ea4100002d1111605a842d80d06140d4a80b25001c0d090034510109003c1b0603e00340304010040c2c2c0c0320000c4600341c1c500000346401c0820f8202d402c91030044603031001494140b41034982c0000b030b604007001008442000e0b12840b0704e035490103000c0b6051000c43c85801d405500500c0004006078010b003810b6403041418440c420041410400201c00c040c26900583e059591156002c070011540c075191a081800819800e100341864585a080e004280e01d0f1001000004100c03036041500c2402280c1209810500315452414584518401010150f40c0350100076040e42e200305102e940100784400d000100e0b02c400001c002400710900e070a600045c8651041d400c100644254015030015203800b0342115107580d030080c0b00c1d03040090210303003c100e28080003010794000c0100d61980040c4001d4101010344600c0100182444d041d58003000303240803030364808000b03d0140c1c2d60035456400032601c0c50 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 757025638 1250 757024388 757024421
    0xf070e011e06020d230d0518010c0503130201110706030f0606030905101d0d03050a0e0307021f03020714030c0c0402190815030a05030a030e0c0109050111010e030a0201 74
    0x740c001c00c81c5400c07074001e84160409030700b2601008010754020310040c0a13040c00482021148844003400380c0d0b0b60343c80408000d502543d00c40a2007405103500301c901010342044030080280000610b0080c0030f60000070729603001c42080e140e03c1b20440e48511310171105407211000300c0fa5500d0b1190703c050080e140b80c560a001c100c1c0340c0342d40012054803c0c091000c1003608007001c0d10b2b403428100c08200c040d10721100481072000442c1c0e000c1240300c2041200c142500f050b0395001956040c01c4d11541c054036480d0031101e480b94010303c0400c0160b03840c0030846542074404103407040256079441d010b038068081c6090240510300b440c03c407a004d600e004001003c2400e00502901d0109903400100000c90142400d0180640a51b40201900601610001e9080500c0d880580500d519020001e41781c240c0c103060072204d6400c08034100d41001c0c0c041c01020341c1ca1030000081e094660540000a0080116114940c1003001103c058404450298032000c101ca1403030060381d81e200000c005c003070b001c1c01d06070342d0405290 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 757026888 1250 757025638 757025669
    0x7090312020718050612030c0d0e190608040f0602040306050601171605090310230a0b060d02030c0706060308040807140307090b120304240f0c02060c0f070e01 70
    0x1440468048255001034507441d006020f260407400040500810203504038099940b2840b6909040001d8000040300d800100f4042003e450010041200500040e000c1ca81e12111820300d503e1140404064a50383e1801c1880350791641000d241101c0c4000d4040c2c0b004d44005004401c1c004c05410062040d9030130b886110448a0352414000041c0b0116400a041d1441200c00207400e8410b00052484640040c112003e0b01c000700744010450f5055800f4151600e98440486041c0d07100b45111640040045010003415581c0c4010611910039444108005540040094a0035102c40700341d130039041c2c00c41c8040000c3c640b240f42212040d0312078064080d0341d1060312400603501501300c62005840380098040c0003c0340c5480035540c0604107107a0019400144507419030742c0d00702e080002d80020f00c804441800ca10358a100080301d0021303105040000c016002c03860301103040d00700088141180d07041c0c03211540c0c0c1d500c44804904045e107080030a5007901616a00240c11211144840c0c140c460301015210303036 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 757028138 1250 757026888 757026923
    0xc070c060503060f0120010e0304090c11060406110432040204030c0e0c041509030204060510021e1606030504060c020f0718110d090b010b041223010203070903 70
    0x1400215109a40a50f01d8064980d465124010b611800b51105c80800640380c010046c05c0d00795107400700d10800c50360010404200c034051074002c5000d6151309007000010455000c2d40d090311150010009090719441d407001d00703040a0038400700c6000f000c4020641c4000303000f0a05120109034440012007058160540d81401460540300300c50450b0303132091107020f10b05d01d040156800107100a004070907a01b814080001d00c407030003aa0224145500340e0341c89900303901750f10401045031410b412081c0666440180071107142d4000401085000294401c0700c01a01085262031030f05410a41c00d480d103d001c0c90300050016010740000b03008a00c200b20034010740c9c0c01c29800b03c0c0d94042002d2051aa94070440d420400542d80e61840d885480713080d0408100d4881c0b0018a11700341c0d1201e0310200340195510324000505c04144005800b40c11000c40440c078161500c500304c0709941440b0800303000484010000b24041d030b030701c80188045001c036030025512031514260240101c6068807050b650b000d10080403068 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 757029388 1250 757028138 757028147
    0x3080609010b0714101410090221060411130501030f1104030f06090515061306060203090f010327020307080705100516050a051e0c0d030305040503120c070c06 70
    0x10b8031081c0e801d20307042048503224440c010080c1c0401036041e004d400110000800c46014103c65203508a0301c100c910704240c0400f81e03140b00075503c03140f0007901c1032000f50104813020040c500c00c1690240c0700e20f03554440000240c000c0c0808101e819002c000015002d241c1c0c0800c00700304007203400036241001004225100d420940300c50b5440030b41000700400050001400c04a0207800c9540941b0740007031003a4443d62001c0c81d05038100030b80c02401d60b10000300302942c94684d03102c0412055540f014031510b07240108c00b0395280180b08d0254810401a103000348540d02ca5840f00408482244107624011702d0700840040c45020f03035105034068082c03604040b42144002942c0000c4410240c030010130300190107000c4880d0303000a00008011042072001001043c010099803001c280107030081d00c00c82d0712800c10804102c03500c20700d04e02c2c81c1d0010f03e070340003c903610074402103212a01030601240710354483c0703015403c6200e00c6040402070050745c414420f280c02c900d809403002512a15000b00f049031240001d44 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 757030638 1250 757029388 757029391
    0x50c130c030b03210f0c15181b130905190c0b0708181c1a0a060f090e030c120405012a110303040902070303150b0702090c0915120403080609 62
    0x28500c03841e0104104c4810350050541854104449062800c005801070410100781280190402d0321402d10010341481400c034203103041c60b41c0c0180340c40d15002414041c507200640d1143e10503820380300d0415515203039411000040743d005090b5024072980c80012030440d03546003000c2e80d04050301719010540090b4002140d6555402c40f10050600c1d0720004000c4498640050858101d4200303040001c0d03100790b00032140d00c03d6100c1c0c00144103100304000c070f210b42007000602401c003040c103104003048058119241101510910340c4045004011048840d145103e1150303e0542407040d0214200840c1205014100366a426a950b07d0601205d01005110305100940301c508840b100e000600050041c0626005402c1d000c0c0070759003405e036a08184012600b01e1401034012a0b220380b03441d00c00c8250001100c02505548001601345038454002c074032a6080103050010b024000280b400700b680d914003603400181101c036400e684d100904020303184034441c2514110003140f80c801c0410f125243c48580d40d03 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 757031888 1250 757030638 757030663
    0x1618120c050d051207110a09020315030714040213031a040b011401050d0903020a0b13060605040e1213050901121103010605060f090409020a09060e1e040f050c130c030b03 75
    0x30310800c442c4c000e00042a920000c02142c4102401081c00e0141d02c8040b501001008802001a01c07494014044d000b10514909007a1094000003c203105c100c000c880ca418203902c050394010303202c03404028074016100c0300d41c1003d0309941440700743c0115295040c4c011403240d4030a0b05501210f903a1020781d00c0b8050240e42d0031030f000c035200344028141610b0580c08020580c3c080c0c812126122055180d20383c1000d0141c40c295004480c0404044c240038a5000e0304000b0001650108400d041c0120460344a200401c202d8141c1030001a600d9255481040107502900d40144a06050b5a4440713808150340c4000c40d00322101815020300e0302407450184504400c5075005000c1c3c519000d043d4080e03a5540e4401c1002c20b80c4503541d903002001507290801d0315005460000c80004100b13041c0910a0b0030900000c1030805800300c400840c0300d480752070390342c05500503521100c50440951545000c9007014000d15520781c200e2403c0902d507030b1040b41030b00051090356013502c01700868101107080c1900e41c2001d081c1d6 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 757033138 1250 757031888 757031893
    0x3240207020d080f07120906020d08010f0501180801020c1b01170105040c180b0d050c03070e100306050303030708070f022a040608120a02011802091618120c050d05 72
    0x50b0008900f008008084910110400d18940200c55460388491021410f8020018105101c00d03c0764980403c00d400d20761000f4203082100307600d00140f4404c070070b443d801440e0411124890307540f1409201841f10014065070402035440f1200460380135a00c0d003030715040065400481c4090496540541c400d101c54900c1c0c0494209507030309010501000d0181c004102003002410389240302600c0e00018000f015040306000ba543c3c070131000070001c00303071100071b800300c801007100b0424444a10780050404005020030340d1404039480c00c1d458140d00424a0380c0c4440e801d0f000000c100000d03103134408800380c0b09071040e4075100d040b0b10804078202da8036807071004e120043c0910598002c1d030003002d1107020074541d20010008280300391150341941c10001403000d00c81201d040030030040c0145d502801800c0c40d00000c151400d2045071281c001500810f0050001d0207803d00d00390380c12415a10488400689240c030382c0103c1d070000c2d0b50315402030705403440741d0b02a11854507004010905103094140040440d402800 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 757034388 1250 757033138 757033159
    0x121103060f09061c03050418020a021908120c03090d0f12090f020307030503040e090109020f01120609060f0612020a02061b0c0a030801170c1509040f0203010324020702 74
    0x5200d20b40700c01510242e0700000e4807490041c2a03030000c0c4070307120703ea10981e07689468901e0074810706c210394400ca02019406005100c200e10081e400a402e40c8484a05c12010000d1030380713810400780b1445040c5405a8501b100000c00a52400e03444c01180560007010489030301c007400c22011103032401040c850a0000c1d020001d00185501290080b52400303024861086030b44401303a000034a880c031244d2080712190000b0504100f443e24407980c80b54040c2c052002404a4000350f40010203041c0c01d0010103040c410711100d0031483c039003240d210700c0140100b0070b42001103030b40303035031a5289500e481e10030240003a0a0110b113400e03142e02802a42c40312086500102000c0e20340e12140d1400ca00380360700c2e01701215814040c0b502e500c4010031009030071a0103603c400f452035040103841c007501003035680692556804207512594644402030040649520080050303140d000010018010b000c14020603000700e8004400442070000114040490508107075404440400c0341032464140d005049020b5800f10030007c = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 757035638 1250 757034388 757034419
    0xe0615041d060f0a270b0a060e03070602060705030f040812040809100504030b04080a050c010f02070b01080c010f0e040e0f0c01031d0a0305030c091201060806060a0f18060305070612110306 83
    0x29900d4141e2145d5074003143d44c801046c0480c9000440e5030040d0001050201c80c0081810240050405004248040d089601e0501e0000e81540310141122010f500907030009001e03c01000155030000b0390300e10046c0742e2414203040403070312504180e0705144550a0369110500280c007403c2200c2c00c41c0d510000c5804150380f0b82d05d522909400900c146000c1c400104201c0241030002c0c850207459030611240140c030f6000d43d080081100105030485030301644542ca4821542c1e0308500d00c042ca032141480e03e0b042eaa800e101c00b0801501b15001003030300078880c0c0c0c09001d440306408251284212030071b903400c21618800b03e5142c4000d04100604c0302261b00080090008284281d00469122140302c10161414001c1400b00f600c40590301c2e541c1105035541c060a11000300184001c030b0f000002168003a104509129400d03640c440d03588240203215402c4a5072020b000d040f80c00c06402990840300340e03248540c2d94a4050b14550240d4030280146180042248040d0041c4080e02c1c0220341c041d00c502290440c40 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 757036888 1250 757035638 757035689
    0x30801050306092a0303070b010314010c0c051005101d19061503020c010207020918070b03070203040519050d03021c0c0b040209041a0106031a0a0e0615041d060f0a 72
    0x790013450f05404100030000208244002d25402144115905a65042d496480320700319402c1c0a8084104030074103d102020940010f09081c3ca0800d90800240c0b58451480e040c1040c0425807005040000060300f804110240c10f1526128244012940003808882d40200080303408a00614007000790400b6000b8100f440f90307000d49001000d14000614102c080c0d00080d80020003202c00c290003a4441c19030a421315400d02400c0002c141c00030410341103003000000691070340600d00805000d4003550340c8070041c04680ea980745c002004007030000b07840c0b6042410001d46a4243c040e0002c0e0480084401d0402d0510410303064002c990024100b0109844603400c12138805400380051796003494501029105160b01c0186074000c02c0c81c0c1c0c90001d0080e804220b0a00c1000840480a00c103501034403040104140c0c0303840725035004400701c45d1000203c100e8101002140520380025807019007181000114012980c0350a0040800301d801c4038480c414001081580c07245801800c0303660020582442581780340 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 757038138 1250 757036888 757036963
    0x180e0f0f0a11160203010c0804030801090c02031c02090901150c06050a15060305060109050108010807030f0807151e020a0f030b2d150a091a04030f03080105030609 72
    0x201e0401080300c46011140340b000380c01000314200030305106811801107103001d101c0d40411000a050020680c9441e40340070300003c90501c10f440506494480c0301c00041c2c400e104030380000c080c400c201c100c1c54050800d0b800080d0001e540c0310f8051804500042000c401000242500000c0d5a494071501c600316a1680050710001d48031b40303e511740712000140d458180c1c00c03030140a41140d580025003031030700e480014100c0c86280e0050303061000340001848000b00c00f04410080d00e07000030072481103032014034103c1150302c1204400303400514942a01c0201c002107400403e0003107062091544886100c845000481c821500c54001041e068100d4500c124041d4211080b804002050810844505074240c80c103403840f0504591000010316a89800c0d01d0000c8407008101d0074035040900700301059402a203524403078001e0201196005411407200c00244040b503025640c07068030001d480b42d66103405483c010b030a00483d803003401450005082602c3c001003620314410f035400c19140c2214140c07080c0103009035 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 757039388 1250 757038138 757038151
    0x15160c02130507021c021c0c0803010e01030c1a070311030f070b190c080c0904020403140616110d0e1f08070e010206061518040c180e0f0f 61
    0x20500000003503a118519150941001c010114161810300c4000741044140682c81e418a170090f003024402c0c80e8005030b100d83c00340c04071480c01c2c40007400380800e847c032040030b11000b814408004004100d09504c0400e040c100c80c0300f003100840b0140c071000c5049610b080b16044599403082480b00c1d401291180204100c5242c02c941035a01d01100318401044681c0a6117050b105002e8040c00e11081c58121f212448141c6c8100302d0400240c0b50f00b400c010607009014014118501010070106040e6039583e04490007982d1040940582180080c00c035602c0d00800c42d82003100d05600210310f00742a008800c20255060540c002e0165841c5058003502c01e80428440320f44c0243d55a00c100e08581075540340500f400445845008042c50403403030050070302c0030740c00c40395045400070400e0120b1501d031020300a2540c0039501c04291a0392032924140050110400d059900074180f16420000c140c04c559a0007000366030403c050401c5480301038150041c43d06540588000d0108400100400c60107002182c0107035 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 757040638 1250 757039388 757039397
    0x60409020a030b070309030e0a050d20130603050c0f0a1802070804030c0305060711031c1b050d060f03120c080403050f3403030509150f0d0506031516 66
    0x342c494448402c4204115440130101b07603603200b9034040c941c104021781c0c034015080310381c01c50850600c0f01040c015011344000034000d128581401d807030740707110703005040700c02c2c5000e80400d007081d041301c51401c09031503a4481503d00303010b41807240c16030703090900403101140c10107003c203080c2915003444002c0e41025160140e1000c0c0d820b001100004000e40010002076001e110041c071403e0071420080e0900b00c0c00b030304003818402e840400c031003020004000e42d01280110741c0c1007450369038010018006080d51540d801c2c1c1c9030001110102503150014040c0202c1075030306030200007040c2ca03502030029040c6680005025800302c8171400403114803070301d25900100d106101c490b0426030b50350340307441ca011a00749030b05290360007094403442e11250b55114002c01500e041200c10b81780040c1240700c0b03540e40e854000a0108003000494941c42d441d41400c140d80181c10480e42035459182c114451042d0f0824046080c0550516003c59882d203400144540c11000004007050305480c1e000300032000e4001d11070b9180070701 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 757041888 1250 757040638 757040659
    0x1302120304090f0b010206011508010e0402010c0f0b0108100e060a020304020a0b07080c011131170303090d0e22111204050120040501050304170c0a050606150306040902 74
    0x4851601905030b0541c41c910f0082418907425001a0500105070011641114180b8601041e41c5d4414130351411251829110b04071501d403030004031007041c00c007480980402c6892001d0b00420502c050b03554102c3c0c0103441514200031018016505940d1014500d10172640310902050b51006190300944c0c10a00c02840a4180c5a4402c01800301d900820000d803116a4042078501800c0750178080c000c18800c0f04450305250821022000c3c0ca5401c14484c1100e04400c200b107015850704000501c84090a40c01e81042c10b0a52a13510702c03540ca510407034542007a4060b900c60060000e01030002c1c074944510090144508032040385440b01d143c20b0039100682c80344e499005882144101e04020088000e81e0f0100e42c600e46450b003802400d49622450103a07407201405094400c10300100180c8090b18400d00c0c191703542e6241c60410362003580340c4911403201440001125110010001160100d151245040d01c07041c0d500c03c000c00a001546214007015507408000044980c5015132042000a10080030080c0c803 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 757043138 1250 757041888 757041899
    0x30f070803130606080a06052208031902031006120e0303071b0602033619030c020a1509060201151205011e050108011401140405310b060102061302120304 68
    0x1604d1250340705d02d189030004c1d584e032001d010305805510b5000b40c08032110080400341e04c070242035249005030040c002000220206041c41110703284604030041d0700320299141d00b444440d1442110f4140300b240c010030310840b10070001300c069000761a41640c0c03080180d410b6076107030740d019240101f01c0d62406105980e03040e98840025aa440074502452800c11250341c0c4003a501c1c45998104400d0f13220614592561000c40488807000800c041550070050305178445143c50328080e540801040802548401c0415001c10301c80c6003001c0c80e00c000107840e501c0702281503844034168221031a20040d5103a4540d10001840002c01a115951000c0e1055000103811a00100c031203c94901c2804032001640e110001081007041c2401941002c283c04100c00ca03540d40b44c0586040d072500d00c40403842c02141c8510000395010041c81d0070201d110200403080310f94002c04460011800b4103020101e491190090216640754400a4041d1040360009c25500360043c03146c0070801100089000d800082c841003101146 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 757044388 1250 757043138 757043141
    0x4080c010e010606090b120105011d031b0102060c040609141314100611030706050a02040e0108030c0d0903120309081b010f0b091b03060402070b0720030f0708031306 73
    0x1d6801c40000221242041d400414100081e400542c214505002d411024001040428111340f000d0800d0b40490b80c0150100220b040154100b951600801e19414411001d103040b98510610990039207031350b517031030792200503842c00380b40900310014644100a001000000c45920342c03c00c0024107428800d010b00e1800400c0e5180380200d00f0f0034030300140c00e0014800303000c080200032340090b0410b2100e080003403100d0781e5a400b0721350010301210384036070124032050079070f0341143e015008100560142d0768403210032955130750000d05400c1c068072072401c4515165103d102c019050302d03404404c117185a985803000320302800c9043c1c0240c5000400b0400001c070b021000040300404200c2c400003041100d52000b8800480f080c503000c641c00348502da010403450b90701032541502584c6504800c942c0b2901c6c0c0d840414020301172110700600000e4000240302c1c0c426000405030b00f00581c4800c00c00010b2130411119512402400960404c10074140040c00024440c4000756030b00255036141803280850b961110070 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 757045638 1250 757044388 757044401
    0x3110702040906091b08030d02030c0405060703090f050f010c12020c0907020f0105010914060d061401060503040209090109020f0d03020c030a0614010f1a03041104090b060307080a080403020904080c01 88
    0x40300159280961001c00007004070702e8030b41a0445c5080d03200b00b03240c0f542090301e9101d0303a040000c000d54000001940c4025013000c0e10060100901919180c00b0740b8680a80050b045010784045482d5506d0000340600e404506e890f48071030180c5d03440f09000701550f11449610b0794181c000301940118030364440c06494030705400748260165401865841501c541d003130300710360043e08140202d80c207040c005280d42c071200e016250001002d031132030100182507081c8a001008040c1c0c68068800741400006a5107621802650145000300d42c1e40105880e4195400d088031034030000250041e120920b105e20600e000d841c00c0300e44034040e005031101c070038980c00003900700200c580c0202c0300c0c1540e8640d0080c10005101c2140d000d42140d04c2c1c0001c1c0741d400e01d0a00b001483c1890710080ea0820000005420042e912904000a40f000381c0181f144800516219104070802c807001402445070100c0040c3d807200008502500c0354104401500d820301f1502801080807000b0030585444074100051012100d0034071400d03 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 757046888 1250 757045638 757045643
    0x9020301050901051806011409090708190c08030c0709021e04030b040309080601060504090510051c0b06060913020f0f070c03030315052809020417012a031107020409 73
    0x713000c0c50301001481d60f2450080c007503a09030b031160006112010101480d4581100700301c80c014845d0352008030701850055503410881541c082c50501400b848080c1c03070b039110003d101d40c10b44000203031182d424030360b01d000b10140f070091070780001400c1003825580e6004101c035140284898000380641c4841d81c1080c0d10030f903c11107422200d00300708000d1541c8050040040c1182d00d01a00055140500c020014041c6002d16428241d07510042242e0074050b00c0440e00406c400b500f69860210035503a49000d6000d050b2058030b514500000144580ca407901c1122000303600208207244201e00521b101e030083d0007080103400d41640421180701000200310107042540e03c100700402c5070605618000301a00e08200c02c1d1070303244030b0b028010312107940d68004001d050500e0720103030749034005490001031040201743c0c0710300c80303843c40003d000c603d22089404100c0013490f0103000384030041c1d400103a4035004c14078180744440044102da2000c1200e110342c03c000c02e024442030300c01741800002e4000400300c4601030800c = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 757048138 1250 757046888 757046891
    0xf02040b040e0901021327060312110d2a05070e0a0b010503060d06021e0a0c2105070b1b030c030117010e0606010c020127210305070201080a09020301050901 69
    0xc10009140c2e4a020b60302c520400c00030350601440c8000401040308034042c80c0c05100e81c800e001c2200d0f040c882d00c0200b80030110132050040590f40c0c1054668007500d1507488001414800b002c0b81d1520303002456201c00f84656640040203200c5070040c2114960400b240d604800851000d01c000c14410040d40f4060401c0100d100581e0820702203400481d51002d1426041c014140208030031542d440715004400780d045400940e40341c0d0a807100b2111710011303a400100315000842d01c800d0043d8040c02e10581ca9101d20020348101c07000a20b071041041440c5200340000d441048140c000441620b085500b04843c011102c03e00c0b1000e040341d4405070012150341c00080c9010004111244504880030441e8280340004c10250181000c1a51180001410281844600703203442046901c01c040281c4801700c1c40d091807010306110311080d0a01b503810320034040c0c460050404441c001c1d440c281e01d03858655058807498a030280715401510700c014000c025407803d5555000020140c1c5082c0641e51160004000 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 757049388 1250 757048138 757048147
    0xe01090204170c010504030f11041b020f120a0302070311030304053d0e0304080a0c08010b100816091503090501180c17030f070b090705010512190f02040b 68
    0x40c411502c945900c522072869001c03c52540b040e0340c2050459095070b80000c40c00c00c41400d1410400d802d51140214203420030300d41008000d11790b503035080c1082080403a500380c502c480d100799802941d03030020014842e072400080000d0344045029a0080c01d115102e41010504800b2504d43c0c0750450300122016a0716402106854240b06509580055184000524540389082400031740408140720300b1318607200d44d9941750300c18811204006617001011080308423643d000b1645042c0c0c0c0c000200d4441c9103155800d03d051800c480c60100d030110a090758a554280d1140c0d00d10484060381381c1d0b100d14850900c10402e01c00b0466250746690710510038030035100402d88082505e4914210340340c14800ca038100c1d00313801400e030004030340000c20000c6501c030014002c104006646403608500c1003040c1013243c44400102c03a4100481030030310902c185801c0050340c0751117584600545040c45046941034074020540001070071500a0106112413414070840018145000d5045408907800b923009660210320216 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 757050638 1250 757049388 757049399
    0x12020118062d02030702040905010b040c110d03020316050d0b0d0302060403081b04030b040804090e0f010c03092a05030106060905190608060d06020d020f04050f040507270e01090204 80
    0x10300000c0e882e00307590074000e1110078024009482e80200d4800a2003175031600422002e02409402800c200c8100400070411002481c40c00703044140303140c2d10741c0c0c0e190003048510f0354014007900c01d6a20603001c0e0780c441c446451300103104aa0035481110000400e075034489203618a03444d03945425003887e00ca9001003070709007400d003400741c4007030340040026409891524210701e1052450050340e044a03800301c3d002c1c0d40d030b84841c608a900e0b8002c5400c00c0001910b40304841c180c2101c0018210b0b0303c00c000c070000700140d05000c50102e09586140e0000703000340c0c8140d85d019000c510400310864144209858820402c0d032950006070948009500a10001d207090500b070200e8500501c00d00b0448000344c003070400d41da01c0c11002801848000f072901d48603454184d11340c41131055540481d02c81c800e40031000c43d0b580c0304520250f00e0b50b4010f4011140030303924200031820982000e200d890f002c1c9403242c540001700d4502c01581c0c41010803064405400c000c10000002d03090301c40a801c42d000c0d00d024200035071500c2c10309 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 757051888 1250 757050638 757050677
    0x1012021303110f0906030c0618060c01091b0b0405090601023a08040b070e010c0f0303060e0a090b0103020f03010f060e0115050f040b030709120f02120a05071202011806 74
    0x41e4400c5109030400400d02c80c05d5500051540c45505003030f120308e9100c044074860b5006008080c1c80c01d6402040000700003100d8001940300d28400d038802e01840700d11300c00041c010440c0241c68080d510802004001c2032140b40f420403a440d43c0140305204aa10307a440050002240c0f82590040380b0b8100d52190643c03240d11000c90501f40c0f42d06e05031524428602d099101d800c44031101610b482d0620506280c0c01909901c01d200c000c65140d0000501c0c04a943c0c0e9140c024020400b51080000c039400403000314869000340e025441e1103642154000503282d08503000c0000380e100340302c0c01c2d03a410f6607078a420500b09051406500000d042c1d5202031001980340c0013828071260807040720302d03042020030020011100960410390301910701c0c11116640380d58403048150b4000d0003e40200e0901d0180d102e40e0302c03c2212800c064441c00f0310035a40411170b03442c241900c0e0f41d900300c885e900078017641202200340100c81c4d884544040040c0145421403220480b410700c1c50b000d110907003002c1c1c00510141040c0c200180607 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 757053138 1250 757051888 757051909
    0x21204140f0a0623132f0f0609130b1513060e0a030f06020d0b010915030506060405061231021207180603050c040902101202130311 58
    0xc600240500c00074001845466044001005040960742c0d40348108842102c02c00055004640840103814101103241c04a100711700301040b120021000300c134400014000740d102803c0240c4140700442c5880a904005401200140c81500710b14140041216642e03100448543c00c04c007418002002c0c4040c80601582156146a5242c400740802c0021034440c80d10241c0e008031181d510b45401c0902d042c00019005580551000c0c203040c16007590f6074180001c40c1d00034001184020420017444079040c005581d0360000e842820b030075007050116101e0050190b0022540500300822003840c0503140c900056594000c031112501c000c038070104002c0304000c058450418100e02d0201d0840c4260095001c50180a010310001d02034000c81c440202000010401d1001400e00035a9000704003203411b04a600038010791000340e5640c486c103026281603003494868206115005042e00d01a185202015503882d2030240e8442150742d802c10003c84040290141400607610a400800c0c00d07084101c10059003040c4d = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 757054388 1250 757053138 757053173
    0x52b0f06080c0f0f0d05070306020a0306051c05030a03020903070f08151012080d0f0c0e1011100b0604091104030212010e070e18060108060402030f0723060904021204 73
    0x10800058443c3d80d01c0801d9100d12000454030409901d081d4a030150070001c6540c00203085600226543c41c4041c4c140d0422405d030755003903642c0c21090820080280000e402c0c104060540d41040000491441c40307900200044100501165506a9910aa03000d0819254005003041d00301c00c0010042c00c01c1c1142d0190842d0610b0400c845c406d00380041010399244184004064140000d07040642c05d42a4110305880c803600c203410802000300c0e0401801800e83e503081141300f0700c0e00584c558051030040510b2100c0e600228011700001070611032400080000d0b40300a035000101f4400055108118055000c0c50340c0070f0140070792101e1551042c4807207800c135001c644426905082e140800340c0300000e520030843d401144204020f49917014127540d519204038501310107010310b400101d1031400004805001c0d074800d500721054100d0481c9682c1d121085801400d80002a003504401c200c1c85544070143c80000041c08149050310356000141241d11020400c1e9402850008000c140510003d66104050 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 757055638 1250 757054388 757054399
    0xc0a0e0604031a2e09180f0609170714120a05030f07031b020105090c03030a20033c03010b0909090115030b041101090501052b0f06080c 60
    0x1d0541d034400c0c1401100340141a000a005000203070035260f444420914841503070314149000d04e055841c0700f0290050701030601541c0c14001120305004060f80c256008030b41052070082040b22a5665a001e13007035180040e00c1000302128004006000b020084c990b041c41144004080301c002c2900a0600311414044420442d0034040003da81d5000401c03668080030f003002940c0a59900c0f00c0903401080400c1c21002c0d0303900040110f01c0000c3d01540024014155481116190360541080550700d00c01d400c980c0300010070301c03005100207107480458001e4030460b02c81074908002120030b030340a8140c5030700024080300d030001c2c6800841e40683c00140e0110030601e00c55925541c1452002a858031812580718091071401c00004c00c070740c2080d0711515a020b0302804107400b040da03d040080840c9802c3e5000d41e40050882048410340d8001e4240b50111901070b1151410f02030000401900b00405684500c4e0b90150860001c44400c1a8030824800051f0500009503441c00e0031201d9180a1001d071940d070081 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 757056888 1250 757055638 757055647
    0x61c0c0f050a030209040f18020a23062b090b0a060f050118080f0303010515071104020c210d06090203010f03060b1203031e0a090b0c0a020c090c0a0e06 67
    0x856200e070442d0025103650802590f99448540820024060f40107142c0301d80c1c2c5003203070b506a5801c07040c41e4007403121b000300e9824841c103440b036000e01d01000004803001d040c2a60390301c1c540145c0c1001d0002d00304c0d40205103004a514240045140d440500d00342c00d80300d481e0380d2001d600081100d6110003030317005401e40c00d00300201414000780d034800c102d042c05003070705003d07401d030041d003a82c028118444060410901510801104074100c107584c0e802c00e01445100e806500501c101ca401c0c483e05031071a01d600311013078003101a1801d090000a52111543e40000d000748542c4d040f03818000b40c41d00d003a0b03050810090b503803081500c0034101203411503009012000c0c0104010010313800ca49100c0c0b401c0e030382c00c1000003c0c01801c43e00001c0041c2d596010a4140b8000030003004845082c805140c00c003003012694041c0c0d5940c45581e01400c490300e100340208030400c544081804031030100d01170070106007140101c405204000c00040e80b03010303084560310b2025800062180040d0ba1003030f41d04400100030303145541030 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 757058138 1250 757056888 757056917
    0x2090703020c1b0a080102071208070c05060105090c07050307031101050a061a030907030b0f0709170303071107120506040c0510021f0b091609060e1c11061c0c 70
    0x25400354001016055070090320083d2203540c0c92150400030108039008560b140b040785842c81e202d041c03001d074103c080750380d0348000b51040d40580d482d2000164803501503c25a030034401040f018070301c040c3c8160700c080303414080750000503420402000c056010303032141c1543c41c035581006401d42d07800801492009003085000c015103000c40583d0882c5c01c403400c003001e483c0d5841a020b5854842c4951018003032242000074400390042d42229180580304541d0f55450aa4540121a034600c00c48111045140d0003040061207452140c00703020301144044d800c1d01c0031a0340e00d1903444482140301d60150303203540100050004105201c00b0341401014141d940c10707002e840e0f000c4069190741034280c0000c6894103c05c0c80808a068960010301c6e00c00707004000c10b0341814011100c2c407807149400d40b07400100d030100401180aa01441019500c800020b04030041240412590601042812012034450004403c111a183d0fa13070b4019054020182d04042071004140e4096400c0d20440c0c00316030144815103c44401 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 757059388 1250 757058138 757058143
    0x1d011b030e101806062603030411060912070906091401030c060503090f060f1806010b04120c0302030109060510060801060e01030b011b03050a031a030a020f03070b0c070302090703020c 81
    0x4140e249410006514143d90b030582054004054001340341c949001404108480c50b011100e040100b0141d64410b5149181c80c100e54910080c1c9010b000a0480c25022020786001c1005241c400d00241111440e611468011803070070820360000c0e2007040d00c400c0b0a001c2040d1074880c00d5a000300c50802840e05525584580d4103030049802641d0801600100040076248104001e402c1447c4050456219280c18502c440d2924002c4d140c0a803499448a0750b10287e090000f000390603a58903c1c8820705e05460518003035074038824000111034280a0010000c0543e5080c450504d0751400760902088a2030159001140420a034101c00140030f0301100612000d60301411100c180042824000b40c080380361801a10900c1003d48410b2140b40303801100404c16034403034081d10960403540c07003d100586200071100f0344070b8080040540c1540c0036504040152030545070060403500301805403010740741c42e540311111907030022911001c0c50b4083c8004000f1401c200880c40d0b0301041502d030850a10b200440a1134 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 757060638 1250 757059388 757059403
    0x709110909010614070b04031707020303310615061403090d1404150c1506030519230d1404030206030609100b1809070e090c0d1d011b030e 61
    0x1401c00440d510345100c020244d2003114607154001400126600d030a140007043c04580c0402d080e02c2c0761513040465112400001642d00a203c0005600b0300c2d654000c100094140f01b00c4544680d0107148040741d400b08519225588003146240e1502051604222000e400010b00000c07c103812801007040007076440b130100d4845c0d00c10a5510b49204900d503840342e045d0485c0240d030015500408950f072480702c01138102842a103c148224000d1215088044141080342e00603c00900356410070404200500b03080076402460521580c00607241c41e003014441c00f90448401a096100c1d07009015131800d40d034000701000e600c0301341821030301c0c41c0500315070103d4040d0101600003070003050719001090b0700318550104000648480001e6985506003000d5400080701c02010142c051444440401c00c124803c03204805940400761545c089511042c1c8210801c0e40000002c0582a94594031030b21200707040c0840351088010380e800426610304400082c800382405a03516410f0501c2c101040d02039210218407039 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 757061888 1250 757060638 757060649
    0x207090207060f0c0f031505011202030a0221040c0e012313020f041e03020916090803040902120921130306020c01091202010b010c02040903050c0f070911090901 71
    0x160301c03101c0615011014000c0c221408004508007040c519a29501c0805003a542003d55004d11114107100105401c0402074040d03203000845407c0051200b4826400964201440c03800040c5064284000b440f4014605040030088003400010b000070303c072a80031818094943c820440300c26514200705603844100100780081c0c895034031484004146d030b805a50450310407107035405540c0c8612800351030f4160340c4035004140303c03402c0e01c01d0014035414400d9200002e990b8090250b07221504c810740e515030300d04003000000040111304000031581c440280040d000409403004007503160584409200714205c00200090b0b484c1e4840ca14510301d490340740194681c807c09a00031603694400610400b42503079040e41002d040c541c0009100c01509505511140c0228041c03039001c5001d65112404030300b62a4185c5080380080c000d465918054034069101c0c010716846802c0c440e1405410000e00b03414001c80955585058028450400c415203407401202c002d2000c94510030715203410400001c1c190001070240 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 757063138 1250 757061888 757061891
    0x90303070f3b10140a08060310020a0c1109090a06050a0e030f040603060815010b0a031b020d09080d080f0a090f0501150504020309030306010c29060f10020709 70
    0x807a000102c03040641c0c1c5001ea10580c00c1e1003000d0110034812166103609141401405090440d10744030340324516801d540f0105604091030401d00c4142261100c0e00640165858002e001c407078000320900c0e1000702801c0c1100c2e02c58504508160409810521101225600030280d4008001e1598404125245019442900000d054444100240041c211018900001d00c4005081d80300080c2c0b01015004807001c82c0d03014045292242c0d4940e48481014244040703400b0010014003003501d04401603c000070342840c002a03235038284082c100100740700b891400c025030803085c0328140c050703070114807100075010f2070b80145020300c10070340000c0a02d04001e080c3c1ca1040c00d1300300030645114241d04414551904841940500c00d01414010b00074040501c080e1603406000b10700140ca41014002e4910034851080035504690743c2030010348240009200031101c46000d15091484050083d260344c00320142118034410324581501800010030400f001c00c0e01c180c60000c01c01000c3c0390b00045c400299613020f0700 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 757064388 1250 757063138 757063157
    0x806090402010e1504052827090813061d060306010f0804061805030d0506030601030f02012f01151a031f0302040f02030f07030603210c0b04030512090303070f 70
    0x80d0841070f8000d40d0056a400000090b108000c9147c0c6c5d01d40381c000d1016010340c2c2685642e5046003402e00c081040c0e02040c500070508000340210781e654041074585001d0b203111803400074603031100d181c2e000980c2c0000e804100051102d26200c0d4a001d1103034111a000e603641880c1d82440720001e030040200140450030000d00c20300140400003190012800ea1244a450744c2010a46217030081d00c94002504501343c81c2e25100025100e071600240f114101c94001d070403040526000c2d0011644254600714011100528000061038030318070324001708804014400024203e1204072130404192020303800102d400401c02405030043c020352045076000400300c4c09000d0107801c0410301700c11410031640080e6005203084c03682d00395400b40c2d8000314032420982a10b0a815a43d40c4001d80854040380000381240c21605d00b1030001d0b000c030100c0c1401c074005c5420102014503180d681e080c1a013404440480000d0700c08135600320000340511f9070907000f49905020710b08600d132000c1c0040010401c00151000c0096198 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 757065638 1250 757064388 757064419
    0x181209091416173103050a180b03012c0103080c1b0f061b010e072414090a1205030403020a171b040b090405011b02070e0105060a031811010806090402010e 68
    0x400d484190f0751800300400d220400e0170094015000f0301c40540100300710390204010324421032101001d903094a003c01c0d06690070178000c24490410030b5068407019814103907101c40800d010100c00d0007544141e04580d03482c13240b850040d0078008007032000030b1643d42c1c807260344046030b480400607842c001095451a85980d0900220a228000b8014450041d480e000305003950a0000c105101510b141b010b0101c40700c00c07040d001e071514241c000e1306400000c1310f0501c440300020750f00006050300e1000600e640b103041d4803148510414040324004540301d44c00005c0400850038081d014000401d4110051440805060512600c6101001104412969510400c3d00550300c681c4001c1d000b84018000003464680740ca0070a00130306645240d0f0320003070b00d038921814405100103190320035900e050345140c0c07041e4030702000d10240e600306081e48024141c441d000103090080004e0018030150003024803241da009110005091240c003e01054040c0420008000160760416a5684840d10550306041c1920101 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 757066888 1250 757065638 757065691
    0x61603061206180f03111606020a030806190609080f0609070b03040501090b2409060607060509190b071413030b06040e03040b07021318120909141617 66
    0x8100203081388500d44030369080c1544406049502143c0800302e820f0050640f600400082480c410032005a05c00c188810010303106100c2a03400c413601610100c0306840840310460302d4005600040c0000b6051740c0104040402041501c05200702040540120700b00348400903140c6586003e0000c4046002001c58108002540f08221954010703003c14582c1c2001c000c0b080740300f8a0a08403400008841e00302020303d180504000b0300a200085c0001d00c0d014480d5102805010000c0146695009503010340380c42400c2c410100032040d2140010711040c2c50032800c060418100084809020481486000c1e028501000102e06880d000410714803a643d400e0000340180907605982400e0340008a1f00085400c0e420016200c100c0c42110015074152611010900b10340b03195041c4030b0f01e900100080f1000c600e022036124490080c5c0e1901075229a1104a1038054580c180000004003002004010107091104960a1280103d00d40341454030074110758070204140280c03c0d101006e00119000c080c21184 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 757068138 1250 757066888 757066931
    0xc072301111006060e010806010206072c041104061b080a1d0a0b04060e0103090b0403080618010f030c090c120f061701051f061d041d061603061206 65
    0x180006001c004e844000043c4034607100c10103540412000008280c8560000c41d0b21481a0f01e16900e2513001c20442d034107140c0c00041411000e45081c8107a0340c04005440343d00408984d00d0910703503981e81e958544032005140c082d0390f12940300481c540d010b804001686490455041c1c00031840c1c0040e0b898481d61500001601c002c01c020f61014940301c0000304ea4825802400c1268501d4a48a0079030014000640a5603003140d0014030042d003ca002400003805540c55640008000c0c001174007224030002c07420140d007420703005010049600803040041011000d100d07800380101b003c090108034042c281c007521400300c11044250885c1c903800c0360200802694400b4000b4410450702900070f0129115050003442d0a44103084410300c0783c0c015108910360b10401c02e040380c009586400c0840444000081e00200c1c003242d1651040d1190041c100340800c13a101542c009440c0b00c060220b81c1454800001c402140141c80300a05080c07032420014410103d80000e0744c4c0d60000d10200302d11246501080840d0350 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 757069388 1250 757068138 757068163
    0x50a060f0305101d04032c12031303080405100e10081b0f031f05030303010b0f0d02040b1803011b260f040c051806060702030c0402030a020c07230111 66
    0x10110320020441e002015038a0145e4041d40303c60300881c1035800000e0f441885112406000c8694030180c902c2810200e41e10403698042c142902d080000c0716601c800349119036070080e44c04d5040030405210901c0e25494110f00e800715402d1485540c00c68002080b0080b40e44640c05043c0405440040c0c203400340440d0300b01e00f4026880020381e6505042c80c603180203410030341c0d0610b0b188143d052000c80c00640340d4080815184001c0003541580c2c6401c900c101c0544c080c40c54281c00c51401d1000a0a000d4a4000b80018205941001e5121700d10f2000e08030440000c061251b100c5e80c146503d105291844141500c02103800740b410110702c104000b10ba8080106440b141201c204007a800c115003204c002082c00d015520407201d0810361075460007044419454204c0d00c600f442c88980200301c042c0703010760042c0010391029065800d284502c600180803a001161000790054000800004200782409038001410802401c0c00043d840e100500e0340d03a5403000196414482c3c1d9080350446200d0401c10961100b6 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 757070638 1250 757069388 757069409
    0x20615120705270c09031f06050a030c030204240b0702030a0b13051203070f0305040515010e100b030c04031101050c0106030809041406090604020f090405150a050a060f030510 77
    0x80c04450384040310092010004100c80025000c44c0c1909010400c071804440000c00518070701d0742c1e203c0608118400300d003030010803690b15a00003c130303602da07450309000540c0104141c01c004c5280d80188820703910b0104400c0c800d00303024a843c9440031b0001d0310078404d55a030f200e1401d41340c1ea440d1010916258004802921901e80c3c01c0400c42c1d41200d02080440080c07048003615441d41002a03a9011400190350140103e4017407107061098610960182e5841030140b01101d240c450340380e407044500c50007a003003a020941242d00700113000750f40c14682c01c010032040000902e50b107030104804270309020302c3c0401004138024800014607a8410740c00c0d1125040204003c20103103540b85065001035100e0714140e80200d06001048078103410200042c1d120300400b030981c08407561a401000000c5d400800d410f00e00c54014400b08901e603c943c841d45218001141201a4403800c0800b001201c4e10aa40114807920030400b0502c01306500105c0d0700c01c0c44d80700e418003040c2c686892402c03104a000c140c01030002e85 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 757071888 1250 757070638 757070659
    0xb060315010b1902060c0301150c0803090c1005090d0816020a080f0115051f02011112041e08271302030624090112061e060e01020615120705 62
    0x44640d00d0081400e0b0b030508110510f101c0340c952080e030f281c81c0100c0340b204007082d00707100400043c1c40402030720b03194050a16110044101a5170b980000c0c0d08103a460070300340d504c08a1600742504200342c0580310707010a8100642014441d400080080c0d1160600820407400030a04008038a0007200e241009940207115114458680380da40340d540401e140910001e6007131080701580c0600c11030b8ac040130381d0b1019010200090307031000e0183d044601d1812020442d941c030104888030315050b90142000d0600004c80e096181030900b04a165841c0500c0d040400080c00058103001928400c211202a4516061140200d1075083c83d42c81554041107001d4008228803414a94440760f5030040d8800c080803a42c003d2034200019a080700780480a021240041d010041d181e42d42d800741c4a02c202e14080241e0105101c2d072150011003403d0961124200c1d060216581400210340040010700300c0c1c0d0080c4014181450882c90000c20f803807030b210009001d0301c07014540783c24218090000502524001c2e1600140c0c = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 757073138 1250 757071888 757071899
    0xc0114040302280201051c150503070b03090d110c19051306030809191208070c06050f031602030c010c081f08120309191a0604050709030b06031501 65
    0x8480848007100180205a40e0b452540300c81c40d00c0040710420744880800c100f800b41e0064500e540212500e1503105040c0300038400c842400d01600c00c00620f14101d0b001c1403490b010505103400c000b40c00c030508106040c810400240c1e030004805d6082c035040d181c1201d00c4034141082505107051803c000d0b4110340c0c07007050310051700076400c0400704442058402d00206433503510500d04482990000038441e0904000c2c218072494900491412007942c01946c0c0000c03540e4148461a5030001441150403030700104111043c084000f10000c01408641421460314a00ca0bc3e21806440004c1141d21000101c07201702c0b481c0e80c400c0064441440c000d100801261106440242141c281120f203010b40340082040701e40351094520725601100c022400030428605284502c03200740d040282515050302c10b034401216541c0352900c03d8080f86000d00c49000c10750312030a101c4500028000d01c8940140d090000344810254050240c10440307400c01c40300e86c3c0e00d03240c440001c0c1c02c0c2002d214040301c00104c0000042007 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 757074388 1250 757073138 757073171
    0x5070315090f0c39150213230f04060810140f0f0105060706022b0c1107090e0a0c15080a0504020f21010c270b0d090305090607080315030c10140c01 65
    0x414082c0101070f51f40b040d901c26489071000404103115440429900c000300180c14a14000c903142c0c0001000400c1c0aa2545600c600e000f05003800c00544540703800d555145070302001c00c1e19401880303840c3c0001040c035000d000c400c803521040c803034180038150004001c0107100c16070b0705407095102c0a030302004039200401501c04010340e82e002c902e22034a1070920403d8005019290b640800395010014100107807811028900800b550101c600342401780804442c0041c901e40c00c0040030b003480b103074003440d00c4180400040c101d2070014031000b4450302d00800d000159581009009038203000301c845500300f0b03840070707445464080d40b41c0d0702441944c201054440318030b4200c04050035900484c020242080c3d003a072011010800c0764410312000b0141082a12191070b115042018000d01904009151407807940124030182d01c001410703903500d130000c8103002c10000004904e0001a0041303000744074508038400050050848610600140458034040408806c6004250784000c501c41d0020032020700c10031034090 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 757075638 1250 757074388 757074397
    0x11030a050402030c040e070501030f060f06180f0e060607050a020a0b0c100203010b03010521030301180e0d120c1b03090e090118020405070315090f0c391502 69
    0xf8864094010740e0001400d161007503103800c4408000421a051410740198010f00d40312070501a1345845202c0170880c100c460030b032540140700954841c40c0501d14881d6081086800740c01c511126140003100300404a510070901b9040702c0202e03a0303140c1e1a605860450b14045035848002d402800d48400003810101d003400bd0000094407800396441040c5419095003244800d00688100920500041c070950508480c02041940001000030704d1801a211a1380755030001d9011550941d4a074401d96400f000600549046403e108003d180c500840a00030b1f10041d110880c142c40256030382c00045455110300c82d121494414000c04221719101c03824020300c0e1007158010400030303618a1002c1140d0220501c0340812040320707184d2806036030941c6d600304805408050b210000301600c891861049220203d042c10040a00f5080000e5411407103400c1e2003500c80e56070900080c084004010000c0102031081401c04a04104401c00804151300da80400082c49040150180c0102814a240d0000316401031 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 757076888 1250 757075638 757075643
    0x10608010b100216120201020a05070b0a09080a030f1107091b08090d0c061112090d0806040204030201140304050a083603031801020316030e1008060904030507030311030a0504 77
    0x250b24009941d0090382c1d51070306400e511200d624500d03804c00c080d0380800d1300700e441144144103503502c6c0040354941d5403800c0125041900700300e90018000c2c00c1b00c0c1c0c110f000c21006005440162465040c07985000c1c202e00d0607000b410090090403000c1e480304882c01c1c40a03d02400084a007002a10600d0b0304448406080321071000c08a001140480c0b00325100140c14801e081456031030303192008803541c80e28098100c2c800d807142152405d001c80b0030440d1290704103038032404a60008081d4003121070801041c10102409040c0107510402c01840541d030700c031904071484a200300110780c0e6074a9070f02d09a0701e0310074204000b030702200011444880d20032901c0d07144d034080c82d1000e04070f0070590f8440609450840c0c1000106070301d984100914984085061104500c100301401564104440d481c82e95a00081c0c40001710000b542c100c6c0040c144d8500408410141d14440c03402d00d100303107130440104883c28405400a000e100c8042140801c143c0319800081c80505030901d550b4680c1481c0a10b0801b0304001e9804 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 757078138 1250 757076888 757076899
    0xe190f15030204050a180f0201170f0a110c0a1e0f150f23040f021c0b0a020c071a070813060e090408031501090506040608011505070c26010608010b 65
    0x441d000000c58060f940e10150780301e400d1700e01c041c1140d51f1403000c2d01c21800100e0500c0429808000812001c1007003500c41d18061b21482c0b07851030546a0b40c81141c09081159446180c103006007074410300e0000d140941558080d50000f000c1c145c0004d1420300108040004200d00c003404010010040c10b10a0081c9615132003e00b40207100044ae5030f41c0070781c0ca01e40c540610001000d0040b401e0100350600540e0445d0088651001040700da4001c00c8524550007079000c40d1040c0e00f14000200075409016aa210010000442c1030003000c11049449110500c00c1c07580051000d584100080c0840b02181c841c66481b12170503564840030403243e20504543d200b41008145100c049900310308010b04420301c03460388a00107600c0c560714507081c2c008118a019000741041032946010604d510340200a101402d001d858810940d850018940c000d8520b95144200f08013060201c00009181c2d00922800e0741c0e050785e01c0400304503500f4644540300d5603500410019600304140011008030660040c0300b0360b003040d5007 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 757079388 1250 757078138 757078141
    0xb090409080c1e0c03030304021314090f103c0905071a0307090302060c0a0204020d05060306060307080307080a050d0906200c100207110d1202160e190f1503020405 72
    0xc3c019128020780481d0398040c1c10800001d001458030103d030000b14900c962000998100c0f0924101810b00101d41c1c240c1c140d4044101e410b21088100718030751909410400600c03910030a4007400d0004854014040408500b500303804103003060500c898a4072001c150000c04c40540242056503542001d03101d544580c81c0d10420003a0b0146981080f80e2240200b511404552441d41c2d0a0219541c0310075450440390082c0c01084005a58900082c901c0c0144190086450b0600c01e04141c2401406000c00741f00e9444100d0400104c1004000e5410050700030310165282c6183c860b00750341707611a043e80c2c7c0190500c1c001041040203100e9210f11125560102c00794241200302214082500c98410002c18640c0100c1041e0181c40140e00182174442c070400b0025201080b0030003190000030820400c907111450000519460380d4100030111000c41d07240d078107215080c54008400d0380c80c84040e054012030b00119140c041d0480701e039080781b6001c9090f01810426145100900034414183e408103e100e10708100 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 757080638 1250 757079388 757079443
    0x303230a0c0e010f0c05011e1a06070308130501110c010c0206010b0f120604021605030c0c04050412030c27060809070e24090a050906090a0c0b090409080c 68
    0x140800160b18041c0c5440c00408840a800c3d16000c41d050001c541541d241c1c02e08544c40d50046c9001700d05000c000c000841c50403201c0d4080301c50b01c0c04000425009a00c24404040400d40c03101000750896156000104d840e041c0381061405002c0f01c084608807074000044244a019056010f1261501c040d0700303595807a40c844071141d52a1140d214014000c81050018482c010340c2c01d01d516400610003000140380544500d10600c0f030403401c0d00d0903a455040440d003040e0028060201007a0110129020086494580d890101800403500014101681ca072a01e0b03603254040d4021500460030313088240419402810790302c0b80403140d402013000150409001c00d08070400040d8902c2556222814203000790381d40811102c400b85a410070040c0e02d80800080b010984440b210680503c1701e1050118581c0b80496900389410380141a084459010403105000300d11850750102c00d83d40081e2060713589003d4176000401800b00b0010107007804e0800281d00310300100020344810120440c4c0c5d8090004081c00 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 757081888 1250 757080638 757080647
    0x1061a070318060e043305090a09020a1404200406180f06111f02071a100504021e030a06031208090712060603120306052103040509040303230a0c 64
    0xb07119900108141036030000042ca89600f100b081d84c1001003210041d802c510040c000c40a00c118042405039068980a1025050900480d03274032025640051002614550100f80486e07a144201d612140740824010fa0694403a005401401140c6072070220000c050302c90090544c0c4188545408120135804040400b90540e601100701c611405180504900e0000e040d614150b940c903010700c4500035a818961241da0700d20031100042962720300103031030301c2c0c03145070031030907d0748840880c0307001042b400404c02c4110404500c1425a001500d000d0303195900354101105200c20f00d29805286000482040102081548980100ca004085860500380019000d440581d025170300840700303410400007400440d15180c090b10702d4a01c1356200144040e901c1d00c1d280c1c2d07007210b900100d000094442e031703041100e442c01e010200070030156404007040c500c00c91034603641c1d02e2096110305405540311200240916019910110506e442c0d64500299410385200301050f0200445191144910704080010098440c = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 757083138 1250 757081888 757081937
    0x204092a05100c0b100806010e16031e15051309170702090103060c020c04090302030d0c0e030c19030605010303051e03070e060d0603140d0e06090603011701061a0703 73
    0x54444024030041500d07000d011500c0207001200d101c41c80d0301c0011ba030b40303410402c403802003806020f000814284408480030f04203501043c0c034101410000b400880d050140d922880c0c61909400010700c88124a41081c0401c0c00c6500c031661050101c12100c0914002c1e401082d0154420042c2c181c1140300054040d0081c000d03201d0280d00300140703000600001c1d40079070000800c241c0f18012500a00d51140000d1305807151108101d00680010500081c0200103010b001001c130903604009680c030300d04a0109550b10962813041d8490804c0b01c82c130340b00d81070040d05000051a04aa0240101c1d0b031a070401402d150f2000c590307280744454181c01120a01001405c2c0ca01030101a6541d40403005210104083c640102080c20b032000e540d14000000206007121031100900200301801c6072017545440540f420081107151340c050a001c00410000d6901c0000300c9055490f000541002c850121528500503c0c290b084000c40c1d800c0d501d4500e249029a10282203103500ca903580c10820798081c000d4000403840e = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 757084388 1250 757083138 757083169
    0x2010608010903200f06150f01021f0b06040f03140d170a09140d09061101021e160c03030503062e050c0309221d06060d0204092a05 58
    0x201c15070050901d00810286660000700303404030f6092003d543c4105061901c2036410b4044502c1c500306035030701f600f030941c00c00f02d8501090000d03200d200d0711030b5104144030140044804901d42da03488996030f00d656075000d403409401c0b03002c50922165200d14081c0c40310b949500b844011840751541484050f40b06c0c058424008203400d5006e442074852603d60780c09442200d40440d00e0003407080d500c000c115030420020b44544000c1d50340c195075524004000c5d01c030781c8544e440040071340d00420062070040401c4a51030140002100510355a0b1031b056001c1c4c09500040303100400c450b46006001081c542e101e0f01441c0036140458168000344c0d40380d030745100703064207524019640c2d100b50054112454011f5000d01515950101664a03100341341002800c550030300c110b20984904034501e903049003060f900c41c44400e496001c1d40800380f0344020304210303a5124000c10040c850002e070300c02c03d03045494641003500919400f000c0581050307031200d03040100c60f00591a028441c2000c0c1c00c00207080c600140310141100 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 757085638 1250 757084388 757084397
    0x13060b12123a090602090d110103060902090913020109030803100501140a020c01030c0e03030c1c0c02032509140714130306051305031606050a0b09011205010615020d02010608010903 80
    0x7030b9050301200152145001c25200b103982800307600201d840711400d0103005403240866403484a000000501102c003690884c0d50040d20512044565444500d810f80d002000140300d00c3e88000f132031004a5030f49146400082c42c0e1040401071000036150365184400307898098841b5440c0c801d1742405d00f40d2274000c1c40001d20050307020b01804c105c0f03075020b0b922502c010b5005152891180001502080c555440024040c0440d88400501c42c244032500086810107011460301c40c51001094000a5540015000048240390010039010541c01819161001080b003000288005070410b040186030600c00c031001000f0510f50780700116040ca0300c50888800d4030151160049013410340e00c0e02401414010803140004a1200c110004910104081c2140246d04000b404506500345002c2c41a1980503141800c00c5090140340600da90799103503064103481c0c1000b803050b80c20f61641007503070141c403840d4050900c0c1201c0410a4048590114031217012900302c0d002403004030741e100a01402c1700c6110300c002d80000c = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 757086888 1250 757085638 757085737
    0xc021003020d0902122112040b130501142a041a070b0112020a0b03070e1003140421090f060e01021006180e010513060b1212 55
    0x490080e400b820480007040c2d0001890b007595030105069031034284a000305984213844002c1c41d421807000380d195040c0e04000b21350520202107500869544040c0c00100062504800901113601140d00c185925801000034480311070348680010b8602801d0b01c20401112510803004e051044d041c804100302c54202d8141071600b40b07030040102e8142d41900000300084010000b0b00045680e15903e24064105200301260a40d114410480c070000280c3c4003201e4440103004003c4440e4000e250011032203000d5540400e0015964402c034000d1000c1c0074510120408002480280042058030f090320f0841c00c12150400440c00006481c094450302c250a048070300d41d1410311082c0d102d24440c107601c03481030044807601c103951000c070420786086402060f603400006400c0720110b00343c3d0144418900001d40200002c2c10f00216101508030702140203031000e0b4803242c0742511620303100da60f51250038852003a1002d12400210741e480c0d9912840e141483e55400c40c1c2070040d0303001d0010501010300c2547d00c002c06507 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 757088138 1250 757086888 757086919
    0x406023001032607060b01080115050306010c11040c030501090b03010209030a2a060216060912030c0503090a0b03060427120e0d110a09050c1b1e0f0606010c02 70
    0x111101c0425124959040070b608140300c3c03200c0014040203441494041160800321000420a01c01603105860802c20440c59204071038002044980228080c80c26014864640c10010043c40821600a810a2501003107910381585940050f050703422040c0240007440004c0c00f01801e03405052107460380340e00013584140001c0c01c8007030031020002012041c3d400481d81d0038214854480b240d445600035801c081c00004010104807401e00107403000d818554046401e104030f000703060340e0011004003440490300c1100c06010b010020340310352900090134006050f07144e056a0f04160011f44549005038144030220b042c40d140c0c440e000643c04040d0280c42e020780ba05031515041c4070650702028052141c024541c1200d62201c00500c182c950080e10704058814100d03041c426000e14a90080312420318050134450410503080440340c43d004003030195100d171821110b095092510300078001000042c1c00704044408076011030011500035141098500c0c903985e10006441008603524025442000e510b4080070 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 757089388 1250 757088138 757088153
    0x1003111204020d12090314011a0402071103010c0507030e030a03050a0c030908060c4303031103100812040501080f150d030206092a040203070c0803040602300103 71
    0x24000e0004101c0b20083c20b081d1502034200700749214480016481030401d000b4840c50003e00a00c203064080200030b22078000c00c0458600500040c4c8510450b0005400e000b4007820380300310100014024002c10618003040030281141c1c0c000c000803400700340725074400041d82c075011445204058042d190140740401c0c2450481d20741074071100031018001a0712010440d5281086180d100740004070300c0303c3da601c0001c0418a281d8443c0082c210004030780e1800f401280b14010168502552109000c1c5d140101c580340a83c060b0080e00c0340e6020260001c4100400e00480540c01c2d42103031300b4081940d50800c2c0f01d6240306003501c254000d41e030100d08050003040c0f0b0484000c000680c081c0c04071351078106001d001d40000d80c0104000e0720503070060b40400203100c00c1c1340c81442a8194840c80070108010504d002440414000006001d6031140394040000303510766020716070b403400140d03015030b00d19641d141520f019070007500b10300c812500c03a804d540b400500640b1540c28030080345040301c03546e14a0b686980d40303224 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 757090638 1250 757089388 757089391
    0x109140603042301021e090307060813060e030301173f0a110d211104080618061006050304060c02030c01020d0f0e03091503100b0a05070210031112 65
    0x50301462040151986000d40d400d0070050f031094000096950603400400c190742c0595054040d03503402c01000110050780e400501034040340d540b401d10f08100e598691480403540075060f4080c203143e05003020b080d218000400114103986140c041c0c1d02c01c542d840b2581c603584855071450100444804002040f2580c00814001e810f112200b060b02070201400328080100d401030002000416122450005030b41428030142920600d180307803620303807810081c03081c1011000c01000080819940d154850420b100c09080b10007034000903045031540e051101c0c00c545002641c0b00585000c0c000c0002054582060018903000ca0300183c2e00c1d00c0c10f607100c6031510700007000c56a00100941c8000c02060110100a00141116592500001800303035010a80c030801c1d034030130070500c01e4103400800c8144510b03554815003401d60b0b50600b5100303440395510003008240c110281c00460302580045200500325902600905071284256803409030f814190702c007034094400072403d40c46500703014010b46110014609c0030a = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 757091888 1250 757090638 757090643
    0xb0f061302041d010902090607080c0c1816020c1f020a1b080c03061b0a0201141602010e0708071a070213060e0c03040c05120c0a0608060102010b010914060304 70
    0x600c40340c0c0c08240144126030241d804100c1c502080d110044007101c41031100c03401000c00010a45c680701485001840c18800c5900041c443d940100d06081c0c20300c4208141104918054003031440000c2111048640310022611560a8014010503440b06440411510226000540640b071500c22007070302c07031401d481c041120340c00314442c417071401c00407030044446000414608010141040c0c2000c1c40c0508000e4405103850080e403240d0140641500403d1010805011070040d560b20341b03009410890240007100c24840d0042c500c0018400d02c0411ba0030403049020194001300030400d6002000350300ca4180d4440c2214640200304104502c07040000340700c0c29485581c00c02c03442c04041b42c0c0041c920b5032150286040c50f56503180148036200450004940140c200e11f06d2609618040d504e4142131106801000c6c0201407000c8481ca441204000d40115007000078aa40c4802d9100c480060441404030380c483c2c015030800f030040e40194010391500c1e007514118107040005011300000c6c0700b41c692010303004 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 757093138 1250 757091888 757091899
    0x3050d0f0c03020306030c01021924090819020607020c01031d0703050a02030c0a14130902180708010b040b07060209190902070c14030a02150c0d0201060f0603090b0f06 74
    0x140654907100e10141c822a07902e0068803414050103040c43c0c814800d80c8141998041489903a055002c080000c9019038840721005d0001d201c588002040c01150480c0743c1c02c0d0b41072902d00d104016041001d000310740f2049402d18108421b1034022680c0c6c1070241c46650250308940440d6509500c41c3c0c00008681a111010003042a41d00c2091894400954007d0750103400c00038030001186801d020a1444035021903003505980e081c400c0c02010300300090310300c0d807152041160840c0900c405802c901c1c10941c00508088955603403040402954000f1500340307001640c860008206c2c4041d8005031010340e841e4080242c00c19065030f40b000c0c002d40c803c010659005002d4032010b060890f181c60720b400600507060340940c0701c00c110700d000d4100303005070380006909070385e100f0340c3da02d0f01c0d2000108021000e404603070800c1c03000c80317060700301003944103285202009014003070070040b00e00e40541201e012a0743d0040c80a80f00d55454404404070b41c2040801402d0007030301c50118800032000c1d501c503a00410018903 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 757094388 1250 757093138 757093151
    0x10309020a0518010801060603020a02030d020a1b0308090c0907050f071a0106050d050a020720152101050f010c0308150a1403010c0f0807230d1d010b0d03050d 70
    0x10300300d02c040f000a02c0c4040d02840040c02841e10030b000d0403004060703034242503041145d01e980180d01c0380541d1610414440c1d0200d03003440c00754850781c0c40956403c1d0f14008030780d80c0300c0d1038180101009030480c3e0011840c803665942e01128180000610300c151425541c460a084211403511507550100c0016074408442980488070a054000001d00900301601d89070381d501d14113503c810a59a005007000d101078410b0008101080c4440360384031403100e0700717401d419004a420002544060004480c2b01c80c0e001f0105940c82070400c8110300b40c4c1c042e4400c1d4540364042c0c0c1d0b5881000405096142d0850000f405000e0380303800280188a00c030b4010541c0d00520528014200c0464060300d03095010805212040407003181e40d003400c1c8280081e01241d460088a085d01c0d5560141401c000a001001000711000403001d0006652803055206080d02c41c245540b160074901c2c00026000044a0101100c20003041c50100201442400700c0c1a80140c007000301d40c0388544041d0740603040507441001c03a984032107 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 757095638 1250 757094388 757094399
    0x110d230703080a050a082229010b0d06080c18061804030c0204050106050307020d050306030304051c020f09280f0905061f030b16182309070e010309020a 67
    0x7001c0d00e40e0714603558407103444c1c5d00704107001410140c01400e480350f104810701c02484540007d042810311035411607c11305114130381c0050010010324095924000d10741c010004141111100010141c8030380320710062041c0c0d41c039240c0c150746504808002c0760703101c0001000e4116a600d003400c0b0b1030748110010820741511085207060011464100c50440000f809412028110b15041c031900e80540070901d081425490150b1000c0d40d1742c104031012405000003c0300080066400b0011140039080c0900101d0f888001c0c442c0f403c0c50846080b90481c0308a1443c1044031075401c0012031140315087d0100e420112003040d218011085c11040f494840503034031040203400088050241d1002184604000d000b01d14117041d1101d0b42110058840111101d009020408071300300c0600c980d000380c1300010051481810a0701900c841e58a0641688031850b5020b000891a920000b01415284039407400b060400f004010030411600440710314011070002c207000655540300c0d030b0100c0080da2005e004c0c0d48401307440c0c0 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 757096888 1250 757095638 757095653
    0x9180507030309150306080303070e3c060a12020a03090606030b070923090c1e0310060905010c0803040204060f14040b0303120106140d051003110d230703 68
    0x54000760b0200711252004c1000c0440848071541c103107540d103400c02449050222403a101e1001078101001c1000714401840e00c4d903a02d1102070000c801c2450000da11720301004007140404950f041001d20b0680b0507480210608244041303c036030b2103041d03841c0318640d4080c2020500079080017000c4010159200c002c0400641303148100400385000c1c0d00c030550701c0d140c40704c1e00130001c40c00e0f5006660a46549100d041001489130b2100100000884009580766100e00c400d0240d409968503088500306000d818915109038940154009d82da009180c011654603284240c80c205035911400d40069801c0884c0c1d404210200c1c0070795041480103101103101e50740c0712559418046a40c00544603001c44d030002c00c0c2c00780340a02c00c0c00c00f2808103034050350400b58401ca0000110005126203820f1001d030b041d0401e044207141040f9802e03e81100001c2000d8104280724500255084c002102e2008000600d40d20b6458846c95088105901080c80074001c0881080030348000c41800030b000c0b10b841030300d00c0400044c504 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 757098138 1250 757096888 757096903
    0x3071b06020702031009081c0e16050114120f09100603050d02011a091b0712030c0e010c0c0b09010c061821020c010507021c050c0a170601091805 64
    0x900405a210b000302c0c01018140000000140744061815002400080d04003041d20036854489110b4405c0300100030302c020182515800000b014000d080d85540303400c5620b03d010041c0d403000c0c1c4c3c651443d036000140039121445600f2403015101da0010000d846105100e042ca984007038924191200c280e1201000c90a03154542c0007290036401040781c00740029824852440b412348440c605621165415010903101103015101840c40210403141c441c202400e1000c40da8580d501c0302a5815001c10120010b00510985806000091882e1210b0700b0b103600c00d82c010455507800c03102440440c1d1801501100e29404074012a06220a0010007404614944221915064600040344d610740e120f203003440b454580b114003091143c0400b9156000a540010480d010008c01e0825541d142c1140c00000c0d2102c1e00d232450300322104200d6508004102c1d000c607138170f964040d083e100301000c1c0d511045599051405201007950540c0107100400030b4000c01c0c2c01c04841342112450085414995032552400c2004 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 757099388 1250 757098138 757098143
    0x16020f210d02160302012106050d05030403020a1a1812030d020409050603072306040b0c0c030d08220204140c03011a0702010509011d1e0414090604030503071b 70
    0x2250400c0da468042c082903c212290200d803200280c25940040c1c13004a2040e805402210007083d40c65015030660300c03010240000070204234102e8400d140c02941c9508c103010881c06103020200c0001e040c4030400038040150700103048982024904081d034082e54050a02980d8480440500d906581070144020007129120038005070351181004000010307148058043c03030090340443e400f080a488502d800c9004000c0f64401c0d800301580080c0003400351b0155800c4901d001c03c0c0050394407520780c1c00141c5603828480503004d4681d801480341003038a8100c012030782410340c41150140107488114403450074410900c002e10001d0b40e805032003044607110700210b800d081510b0300003006010400e04142030450000c08860b4591815009d64002001400b80702c150742c1c103000a07000d598030f00e417411117055201904090140380c4501d01800e4952103102e0101d844500070b07403900400e614403845103500d243c400d1010344c00821203500d641e9021141648010011401c11940c25a0b0024180c40c1181d0002143d0 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 757100638 1250 757099388 757099393
    0x120c070920030f090106050301061502011a220e030a0e0a08030703020c09060d020d03020c0406050301054803160302120a11040803030109021e16020f21 67
    0xd050580d064112680648a03071903000001c103a915040340140c0c1100d0b842450511406481d40f2030000c40e60140100b07800a40e4513500703010003c80c4960b49000000c0a544495000707204401c0c2e080c0509004000c000038141c1c00a00f5000b0b9084025201d403c000b20003051410002010501c94400509540001c00a1000103800f002e032800310307242218803030307015041e4030000e18904049550041d560342504004c0034010941100024101c0d598000d4103d070103a005040b40045071036900d4000c2d100c1c80d0340c07400b83e4070481c03404002080c41d040512420344036000c01e045203003880341242d80380202004a940b1105030ba0341c80000f1003d0021a1560410070542e4000a40f038403410503c8035000c0c01c50b0140e1003502010701c1400b0302c084c10098084031580040c0c0c0704100040742101c14500840c10720880d04940c040744800000007920b02d00b41c1d4010120300c450801d84040340b004030141000507101e040380320401c0c00500030340b103c0036141455400000d81e4000f031001d00e51640b001340c40d10000440b0074482802e45c = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 757101888 1250 757100638 757100653
    0x10302310303021c121a0d0b01090f140a02130302060706050f0f04123e10020a0206011e0e0f04030e10020a23060c04030c09090c030b0405120c 63
    0x3680401040f44e820a003103890300d01d41d02c0602d00040003600c010740100c0c4000d8031000d41100b8000d0b106000700210b003002d0030007030010702541090039041d03a080c450000c1480c603251040c68915200d109590481d541a66110303955200d07080280e0180d0400380c4007801c860160700b80080103030760300d02c000d20300c0600c1000041118a000c0c0283c1c0c0000d0360003003c00403e49555420040041d40450356114001c0440c00e2000700701021041a14403c000b00c034820700303e0400180e6100046030b1513100002091101021210b05103c5090000140d01401c804640540c0c044c3e070060148000440014a288680000c900c024aa0300c0d5465580c141003a00c1d40076100382d0107014042859481038480c128900192110b00328440300b004001d41da08149000503262000d00c0c40c540200d01441e0b04100304014030f80d03044545e10308021a05060540c030621003129845018680001c01c10464020070a020b5004480c0325400342c95034440c04009a00144200c41c2405105159020f000c1e101c1c0180445054220082011 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 757103138 1250 757101888 757101893
    0x1903120230070c0b0105060a0e0901060903170c071502011b0e091305060c0903011d071502060105010504090c05160c050a1d0c0702030a120305070e0405150103023103 73
    0x20184050b00802c20030006009034000704e80000009811190152070003956164400821260030501c480f1b4250b11124800000441a0748030b1211815a800395109c01d00c08480100c120005100360f942d0550a43c024800420180252603441c1084070a1400007007401004401000040c0b210082d40b2404516942803100045c10850101a8040c069540644001c5e2194588641d9010004e05880d240000011900066142034100c0c003110070009604150220140c0c211039180c0d00c45014a030f6181d41c10b0b85012450074400100c00e4121241070312800d02c0c0c02e08040f560000313810809042030600c1010816546020085c00c0f401480d10f004508480009080c40c040082c1d024079130b40514140000c40b507514100c48440d2401a0700321082e440365540e41c09191011a051465000c00540000440f211040c241909600028405c1e0380b555203a50303002d030001d400c00007120780644032013a0041c2a151100c1081d4066070080042c1c0908101941106150441c4071a0101c007125005c07502d610203500c10003c = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 757104388 1250 757103138 757103227
    0xb03060708090a0b0a1b0e0108010e10030606030804150c1a061f0f021903020613061803030f06060c0503031b0f1303110a1a03100306020a080411010219031202 70
    0x6c90490785051540d01407101c00082910b84180240a003076605039001c51800c2e05120946001564050003d2220310740d682401c03030098005100f03103e0360303c02c450500c0c0b5800d80304410781403401d0342c0180c0032580c841c02103a059031040701c02080e45030800c50f00e45503003000c0c1420340e86800c42d84901da560b0104484c042a402403d200c120300048181248070305880d40082d1b000301d03810b540040030304185406c4106034104403024080c1700b071449851071202000c0354180740d4181c0008000ba103800d0790900009540700400c4800414100340500150414070118480041b000d01c0c414641c010044a00d043c00c401500488413644003c8130442c0b03040c1c844030100100040c00d42c00b00c00f04a0304a030b40d040360500e4408000924040400e1183d000301d000400583c15400d21030021001d50342040085454200048018001003401d80341514803031000caa128034070703620015100c989402007a01d0803c2d90a020754080d509441c2160581000170303000d100c0b4003007402000b213000a042c40002116a41c41a184207100c030f = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 757105638 1250 757104388 757104431
    0x190507060f0c021218011d09070c03090803040302100305070e1504170c0616030201111317060408090f0f0904031e031503020603090a0c080d0e040b03060708090a0b0a 73
    0x454004051140e02405c02c01d20011003904802801c0054a404500d264003a90515040e1440d0740811030f40240245568020780080c285886500d409042c9621610402e5981c003552200a502c10740d01161804002d01c2504041c1d082030f02400d05c03a048507808400111031000f000c0d1220b031010400305040000c40f4035010580d24041150001d052000c0240d800f04070940b04521802844540007031210341014400d40c04400c12114041045490354070010300c003a0f40c0440e0307110341e518051980002103844000032038041c5c0295840380301245480b180906000e24610000e40e05680702c00e58041c003505079212034004620036446662240c00c42030004810070340000310654072804040c54004a0303840212141c15241c16a5011a0882d48a0342c83c0c40f86d452400805420040080d42c10f4240010158800181f03e4010241038603814003c2c45e00d103041c4800c0f0f07465040100c1e030680c402e08c01306000b60302032070701c05400c00850026645c405559496a0440404c150b0340301c500a5a030fa03928508040b503040029 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 757106888 1250 757105638 757105663
    0x3130b071e0b090d050324030a0b0906070e0603060a06030b0607020a1805011502070302041d0a030f0e01053f130203061005060304060b06040f0602210906190507060f0c02 75
    0x1501b1411301004010132084146011204000c1c12040e038003181e5010860074110a0b0300503045e6040b442c0c81c0040e55200c030400d0702e444002c82c00034001a69685044001d5a2094401410882810349880000c4000c0c0170302826142d040303c410003003400580c54101549000d00402d203605012050030717903032080403100c0591125030543c40100d05503030744560216400d01281d4040b503001c1000d0360b0b08980c0c0c100303c00201c00c00480d24428000c103803080640080c0c01c0b00020085848101c40400c41d04015111840748040305c4081c4080e0f8403408402e001441c81458455040c0302d42598003081030326464402c0d040c19035119551009200854045107000c02c4240c0c0d20141b028007032510303146450003090443c00098030017030441d40c9908600f8120344940007554002c050008121040d40d599050103501c4203403080e0030f00d1203a42d103208074a600387c402c2d030111342950340b000c4c06041c03a0151041c0c513205803502006241003004010414040403906d2401002d2026400300000070f00481090f20281c03820594100c4d1 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 757108138 1250 757106888 757106897
    0xb030105120c0a140301180f02120115121a040f1101030908070201050d0b220f051006110c0402030c0c06151e01050d05010b1b03130b071e0b090d 64
    0x300b400395100c200c1400125060010b148001e0f4071800000703130140500101080100d41950900c3d01030092010306609000d000303440310020460b542e02d0b480d00b82e4034606104c1140c0c0229920400142815181045100740130f9603803200c042c0c2e0420400d1190010584e001c2e038031070a1402141090250302003041c0f01000007400c040024085555880e100e500801e84042d040c84000b0503401d01190f055005800312010051a03049480c408088a072030754204041000312035447e01a403801129424803a003030240e4150841d460902d89400001c44003e09a03411100070750046240700d201944650000d18024072620132006e482c0c110344e8012a2034080c000700100b0045050011b801f0086d00d60420790910ac0040e81c040461459040005a1b42403040e10001185103141100010f0a008200094120340c448102003011070031408044035642e000d4490286501d00748080c080000f000c1281c01052070901c20884418a03083e45140b5540410f9107010640310304000c4801c000b8100d07401d1001014088440c140b = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 757109388 1250 757108138 757108153
    0x52a150601081329091006030503040b131a04030b0609040201231c14012715030212060402041503081b0c030a030c11010801140d1b0b03010512 63
    0x1c003807281c06002070f50120703841c102003400d01c10224038840000d80d510310051a00b030000c0b0704059070044202e5540c070b1940940360320303041000c4190080d201165003041c0214141800c00110520755840301942c111110042c3c03d00244454450005c03042004001c070400362540d10350b003441c09800740020079040c0300740b80480c20800140c0c3c1000e00030010064900e400c680318258038282214601c034881d602c5035035801200c240c0f050b200103904056604100b04040420b1170340c1e03c0c0c0e0006450050407141071180042018900e180d003c49511480c495031128040000040c0c0d00d402003100101106443c3d1040d40207641007106508050140323828101c031340008641c1481ca140c58800b96030145440f40c4031800350040820800000c20814501d1944004098038070325181c0789409820b0308013401c0103c0f44840b90104c008101e40c09803a0040c120781460508101c1418940c01304004442d101500300c40560024240c00c448040f00070610014201d00d40c001d80c1d5070b504100400040b0042003503800c8c595405540f = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 757110638 1250 757109388 757109401
    0x51908030a03090302013b03040e070f0306050a030f0c05010f0504060c15020c03040911070308010e04020a0e090f0c1905130905010f06060f0905011e052a15 69
    0xc2100d00c03a0025140c0024180c90b10700e0700702d014051801e00780e12010720500000310740c00707141c2001030030b512140f144014101c0041c940b242e490740118895001c401351640c00003280140600b485c0260714400d8500080d90546600015160045641007640e080a03910710034003c114004c55240c014140c00d003400c181c0c460030b0082c010304034860340c0030740000c011680c01d207101003082c0c00e01d40369905c1e61311510544d00c81742008142ea0342c1e03810910075080350700c1c00c0404000280352003008540c0c40075090740e40c1c80f8080c0c0c05d03c0c100607810000544100c1e00034041d14000100c00006410140c010800f08016000008010000601e00300641c2401c42c455944264aa6400301350442c0c083e040300c1040d2100003a0700e00c601e480c40c000b0054070502a04030f5080502c0c00e01d200511340d0001042d920280c03100c400b011441c14040721550424056940851800b110765124068a00201c4154004a182c6140340c40c006180c1c450082c0083c1705040c40140400300302c1c0e0491602030114800b1030401103112203c510f40007 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 757111888 1250 757110638 757110643
    0x50c0c090402090106112a090109060f0504020a1e0306060f0e060315060c030d090204140417030603010914070806160206070806040b180a052a160219051908 69
    0x18401c0c242072101440641031b03005000e01c04044d1000c50701c400784446921b44c00080082010b403014242c8904801030000c030744044144200c0090300e000c007030301c05603003824402404000d50141c00c50702c3c140613105030302741009040386600306803044650303401082c01440c044c00508084c9032503070300c9404c5c003900b964220000d450b48410349a12800a04401e07030a1070101020031440d1040c00b440d50344502000030f0803000da84058011a015a2003610104010034001c15074151141080d01c00070084a913040204d882108070790003840d0410300040002541a4580d0766401c03060a00b01002c6105070014030082209807021700849600c43c03103140d09071840b094980b031b0003904d0707080c02031421061084081c0428905d44440d4440000010302414448603103071200c44107840c8a0f01100c5003807400c0e051000080000d090085030010651040c91101e202100c00001d8801d01d8010202150402a03410114005a86e504289150458a440c2001400780c105024003484110b035460b01c440c41444080b04018a8000 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 757113138 1250 757111888 757111891
    0x6050711281a0f180d061506080402030d0c0809040614100318170d020d020d050907140609060705010504030c0501050f04020d020f01110f0c0f040603030215190c050c0c09040209 78
    0x200703100d0301d036900d040d2604110390041480b01070f17800c45a00003078681081155445580000b86601e0507541069a0305421240c08070f04030341c02034150308000044030105002e440031a45991168a41a0030b105c1144049404c40b03090350f0103040d2032040d10070424141c1c01c000c4100711101c80c1a00d000d10101c011584005a0000004030007000b00c080d0701002c0550501c000b05a88176440c120034255600c1c070b050300c1500040c2d04007034804440d0f02d240202207601944002011411204032810041140f5003500800034250000d000712908050304100c05800240284140d40c031551180c1c4401007180e0080c1003050858500400348100302200d1004d010250b42d8808001d50781660441c0d0b1807080c0c482081c012600c451200100d2246481801400c201441001c00d2040705042c007035825120400d0740b5010442941c049110150150700180000152442504c8802c5e900c8424200c1c51145111406054412100c2c0300310024000740001c5814942d0000600075049201c2c01216030360034604048e000169040b40 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 757114388 1250 757113138 757113157
    0x10f0f110f0717120a050105180106140a020705030f030304030f030902060706090204020d14060f01020115120206040b0a03050f06030a0c14030f011103040302071e06050711281a 78
    0x80040543c1000030a500031240c0484c1e04006824450800d2918040581420b0090b03511506d40302d09140004081510b0342c030304a5030182d8489401001002e6803d01940c44040410300b1405000c01c0801c1c0b9403010840d481d104c11414008503038a181c80c2c180240001c2c01144003034101810024900c3c0982c0e01e040a0b241d410342c219900050301c10451000400922940c001c408895050441c0118920711800c03400784105410340c0c01c013108a21400049080341c08000010321085650f0205208441040c0c0e8100c003458805071503585415200d41c40c0e480607801441030140000c7c3c0301c20401041d2804426119001a41600148036600040e0f86074501d2000c2809180f14020754000e291040703a6041100f4406942041700070004440c81e10751048282d4400c075002e030054811444000350092036442e000c1c03100c400001d030400c2003605001003124a50302070003040e201440e4005280f1010703920541c14011b407680d000d91442d00e10fa0703602010510328401b980300000101c1c84c03030000b0030340f00780c00400c8990489 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 757115638 1250 757114388 757114403
    0x15031104051e1602060a0b061209070e0f09070f031505071b0803010503060708041a07140a020303091b010c0b0a02040b0415020f16060507050c03010f0f110f07 70
    0x1a40c1c1400b5580740c40210701500b81c69200b90701882103482100000d1009000654240c405680d2010804400e95500b89140ca42054041250001c461582c0b00c4494016415100b51084659100210260b14100780c2e210060031001750144000040c1c02c002d07410040c0100304110360460b1450700c85114074185d015801e909241c42e1800603410318860245800c030818a816000000d15043c00c05034013581003401258002e115590101d0019401420010b1040340d0181c201e5100e100307600c2c898448940c002d8441800c0c810711020071207104043c6005008208015401140c40e03150080f01c2d223103011045114a0812060f0326070320718143c1d9000078481101d0b038111080c0c070f0858465100c88402403081d50b0040f001c0f0b240205010843d50000c1d5101211006981d0880e10040c012021082e11788180d9100d003852400c2407901007103c0c5000f070380540019402901581d084070b24040100b42503440003144030070000d80c4c40d194490841d00d03610a440104260115060038601020038400e0207100b418000b4001c00c = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 757116888 1250 757115638 757115641
    0x6030c030e070609061d09240a030f021f1b050309040c050310080111071112060727051e1c08090a0b28230d1503110405 53
    0xd01030340141c100405410300700c03450160b5800e8014024111401800002042070040b03c244100561070109401c0000f04255482c0d16442c03a801c80c1700350300c20190b2030311941250419289960b11071110008500500807030309100441e20400c1003032044203d46070442d118554541c660360364403031040503188011440f210001d07030307417400c24901e0b501510008540c0b1504041c80441d4659100014501900d000380344a0420794480380340e14241c0f11110800b4003814030500403003000c5200034030801080000501903d103100b40d10300714581064000c481c8000440e80440d200d084101c02c0e61301080c030220702541e9000900f03003014000b550440024880926514040c0507404c219520b030348d82c81140d400024081d807060f40e641d10f07020300c05800c1205402d1045194180c0000c08a400404803464116500700c2034210002441700c00c0c003070301068103600c003c00001444180c000700c0c1e001d0a4801d52118040c620b0740300c40c1e13a40c50700002c1d07840058200c1500340920400304002000c696103400d85440c11207002c40c0c030b07 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 757118138 1250 757116888 757116911
    0x6010302100219060c090f0e0406020a09090e0703050d030209090c1308030c0d0210050402030c0108100503012a0e01020607030c02150a09030e030d09050f0307050d050708061e010603 80
    0xf0120001900309508426070b11100030071445178401c2c1c10001291b1035030a841030b40c0e203007540905d00041c0b180084025002d00041c0002e900f80d80240849080303400c0c45915039071074a60768001c90b0440b01200e18150f02c001c90900170310404220b0100001400e1406514000240000c940384610103441c4000c0e150002c0380a21100021042d060054000003084940325400c81c141140e84a60035050b40016004044585001d0342e010f0280f584180d070040e000300624010301d0011035803160300400d20400500c0061001c10180d8080c00b0700588030020ba003a248400944041c00c0030010810300b0401e0a004110241000503600070841c164400190f090002c2c8510b034415041c0c0c2005960305914580640303000803c211804a50711420007d8025a25814484080c60a040d40d488803c580000400d01032070042020340307420000301c0c804100241c2916600f90b0f4500c0031400c4042c015004503a80c1e001304030180810034040018641c0700b440950310801c40b0820030340b00181d80c003040c01240700300754565144420 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 757119388 1250 757118138 757118143
    0x3050a020d02210129070c0f06050d050c0c060105090a02040918050d1818021c1b031a27070801090b060f0f030709030b090319080702060103021002 65
    0x42070100034809556828000759822540d01441d40c48100880001e0001319900e464054110a509001507044c0d84061034100001e0300c0e03420001e411104400b21741c00c0070520004d41903090b801000c01d03403101c40e22088181d052400f5180c004003400100a02030044d0320202d10002038090443c0d07030a484607201500c400d00c0b0400a48200d810034000b542c2046210f011001d0341031141074070320780100251848440b000200b04e50014040e0f41900240c8244002400481240c12001805040c0881c006103411a0701e0b400c4140040050b01c18201c2650707442d000700c901e107080c1c1403604a4110520707003001030f10071007840340504500c40c2d01068090350900d8001030500e011403200300c0c2004811540b04945203000e050003030007071200b402000205400c0a500d00f6641c103112040c0c860404000c000c0c0340c245122032001c00c529030001000c1208200041d13000002068540103818001d481e4031015590b14103c0899045e4001c0d170340c1c040d082c1000310300c504020885034040394145c152981158010f0a054600703030220b1 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 757120638 1250 757119388 757119397
    0x7050f0d0b1501080601030905122d0a0323070c08040b0c010504110d0507090906020405091302100f1d040b100206011703031b1e07030f02010b1e0103050a02 69
    0x20804040d01c41805980e105030380c4402d4240b082640c4c0c114071542c03140011070075100c041400504582c404500180c0000464018107808580e5250100850921240c05d1280e0350b912156045807840c00100500701681c1070003118009882d0f070501a42010b440304248200300c0300285000200700500d00c600301000800003c0b10010542c3e14074168440d82ca4503112402002c05a800f102c0002029580078694180101980a260340110140000c14030b0807559030301410720032800712000c545c00c020100d1183c0d20014818014007036000300b000c41d40c0c0307644188900d881c140d02d294024440a0340c207080f060356103c40420042058210310101d1148400c0100307000c0c00102e1440c41c0d01400c0e0304494070015034000352080c1203035a64403182902c1440c0520f8180c82e40b20a4926890781411135042042d007001100c01440d0144014440d50910368600c0d54220302c41c2c0120307508070001244100805e0072580c2c24040c8400c0d1b0704085420400070782c0d011411500880c0f0462aa50505840b080010384001c12641500e = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 757121888 1250 757120638 757120643
    0x301090b01050d0504050c041a0f06090a030609030f110105010e0c130b04090905100603081909030c060f08100602031920060402011103070b042a0602071505090307050f0d 75
    0x140720178141072a0068465542c2d41c0c1c0a405285041c0300401190001e0110f900300f80340203410000740d18542c10500815074411241c55401455521001001807014070445282d940640d4441f41030f40c4102d04020841c100c2802c01d180107a0411005122081d800c0b00020381002c0c10341002560340b0b00344131395800da6a0312a80115803c000c0450000f40c01e540c15044611403e104500341c0d030300b00000034400422600b1b6030101a2103800c0521060b040b2030040c0f03e041c0c00642d0503040c180300d880d640f0765402210725001c0c3c00c07d400050100b230580103410b411514094100302400c0356842e8241c03c02e08000e650340981c10090404500e80301440841600035047d40c0c5001d0085c0c5080d00205988034801a41d840098500b240010740200300c00058000110507150745e2540221941040d40707594451600d000c07942c0c1e040d040503502c807000040d03081540520200091031503401600d02180703800031103210080f61450714818040200201c10361030741c000c9600c40940d1003c81e403881000000c040852400300e1000b200 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 757123138 1250 757121888 757121891
    0xa060606120b0a0f0605030402150a0c350a050d06090902100503070c06050c12040f0501050603070305060c0d06031202062d16020c03030d060f09060602030301090b01050d 75
    0x411110351201c0a0489010340e54414000460044140a4581100d2003103042c1c4003c00c0d40d00f803100c03a2103400250b821900081c03000c00203590b40f07210355005600c01449000440c5408845500700400c3ca041c0c0100050014000380ea44c8a5841c1000d200040381010140c4d50527000405100140c058810f0f5034101d041b401c8200300721912982010000c180c108000d034800d900040390f4a000912440c01c90b840f030f05c1141d403003000320b06295039000c01500c4083c0080c01c03025410b03c8a880f403000000e203090300c00c80c010400c920000115081490840e803010f40703101e011340c00046050000c50302c00248030740c04c4011025a244d4a412212180d40144038640009142917a68200f11031003942c00109107001c3e6500403000704000341e03200c0305900381021900e91091981e80405c00110603c0d00001e00f014210400c2c010303a109000c010380046e041da8844036050244a50344d82c003d12191041d01c00e440b02401c8000401c001503414000065034a001c148201a44d680d1503581d82e11541c0d00c914256040303000c21100 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 757124388 1250 757123138 757123151
    0xe0d0e010203131701050906010501050d0c020705060d05040212061b0d24061701060c260310061706011e14070b010905100311101403070306080f07080d0f020a06 71
    0x1341c0d415030095210b07130034080d070a00f40403c60380c00000c280c1d03a040320700c161a030a241c40c1a82d02480040d001d00103c40e000e500400b60006442e494610040c4081c0090301e1000890340f42c68810040720b080d039020f840481c0d0780403e08010b161400c0405d004014a401280310340c843c400084035601a1000341c82040e10a80c80d070005a20f028400040b00e0141e8059844512708004034a1b24101404000d10440c000921000069004a805814485801e1b502c1c4a10004150f410540c001c810341c0c0103480c00610300244d040c041141650103440728031030155001e1075148600b41100000d1076110b0401c1101103c1e02c9100c4440c407010b002d03e070300300003040d4102502502e0b445a8100094120707024814917003e182890001441c60440c01c28103000d036030b4041041045800070006000000590040480034408140100e44a01c0c3c0c1d0340c1c0103923106c0d01c403da0740441c0e080d003001d840c0790405a02915040d11513006c030105004038400822004070816031468030041d40c0c540b21500724030300424031102400c02441c124 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 757125638 1250 757124388 757124399
    0x9060b0310060810050d031715010909020310031101020a1703070e0f0307090b1306080303060f01080405070b180d05070314070b03060906010201020714060a0b040e0d0e01020313 78
    0x18040c5228584401c4808400d40d610102900c01031412110002182c4c0000c00c14400c0e1319050b00c1440c2c400b402480c0601c80c0d02110040203030100000c1d41d095060f500c068104070f05035030f0f101c503c0f18081c01a050301581982041100406440b8184c0801841c481403a150419164400c0007079080c0325402c41a40c01d45214110b182c40c8084d40140c41360301c0002c100781c001b0396503810440c5003051035080182c003d00e80140f40407990802031a048203001da00207040d80c3c115942988030700512002d0300e01070700a590743c0c0c01d0500400c0b26400100301d0b11418401b0000030800407800208204046454164206950790f10a0100308800b9034200c220030703408064003c00d481846000940c48058901c14070550702c0c0c1c242c422907078a03900c0030640310340102001c08100095850a01c071440030780091060001605004841d91490000900c0c0007003110030380d111800b00301000d8800d02825041d410305450400c003902d9101022900c0307100d007420400502c022100d0014080e442042101d86000110038031824a80c4c80e10b = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 757126888 1250 757125638 757125659
    0x30d080a060b07050a0209180706120509160308030402150d020c011409030403030c020d021f140a050d1e0227042c07080712030f08010b09040e03040906 67
    0x5503844401285400004940b072200c5204a8020b1500440102001125982000051300d40103103100c01a204034041ca0744008000c1050314081c0c00b00f520342c45d15403410000302d54201c2d100241040c405500c502003043d900d042081e62541500d800003412a5255036500100781c002070f08282c514002c80e00016a08071308010b41c1e000d00181c011403002440803007500301ea405880344065502600320f400c100001c0002074003840313002c1c060380d2020782107080d81c503101d800041c1c40c800c0c030b9550302054000c184250315601d640024840107001c0240404e80c108000c8010041840c060820301101c425514206130407503450301c1406030340a41604100f07554482007121245185240c60400703003000c0402d04105d403c10302e0b0134003c191810402440c02e814039072040540416107034040b69400f4007405548000314000409103d000701500340001c5d0940500080d00d4003c200405070885402001505801885201507000884030600030031100401c1c2e211824010341d0551040364018a24035180074400500501c24 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 757128138 1250 757126888 757126891
    0x30705071e210801050a050609030c0301020a032304030f110327040c03020f1e070c030c060809150115210b2704060c0306030f0f0b090d0504030818030d08 68
    0x50074551000b094080700030741c0d04800038010107900c01c2a4000c180440c1c10000d01410b50180001c00701c8900303154080c0400c3c22039002c82c4001c0c0001e61110749143c000c0152044961752952181003040140c5403d03140144143d10346601801089107030f200010240a04006030346405007005455490010100c3c0140003400c5044003050046040c40b105441b014040d2003a80e88080300001500e1910401d0040702403020320960000385115018800d01e8003040d9008100c5010314072580b06008110702384507002d07268440c01031035408540e00c007001d40a000300c1d0140c4001d044480c4820809803162820409031008040081034080d0b0107000ca18141c00c540f03094202c416001025105420750300038400035818074010013907810700081a8500402d00040c4240c1c001e11810043e8600000c000f5200d588041d0910340e542c000b1740f1800c7cbe4186044052022401101d60407a81d10b038001c000e1107030b020b01c014242d03004511010b0b0841c1c40108070084070f543c0010054148070f1004041d1079840c41106400f8144410 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 757129388 1250 757128138 757128173
    0x17060f01451206050907030f0606300303110c12030a0e030c06010311010c020d0807120509280f08030d18150906060f060c02010809060c030705071e 65
    0x100404200c1001c1c0851021805641081c0d00c800500440c0341c4950010b89006059401544581b0394004049150990840301482c4030381e4001c504c081c03a00c19040300074010780300104031061000d8000402d1594400c0e03c805c0e03103036040c20301080c0714540c01e0b03050065000e040c60490203030145102100e40c41c0c5440e4000c522a0740380300c4040000c0031109078002e5590040b003852504590100c0c0040c808151048040f501941051520020802007540840c0c5100901c030800c0301e030b2840215402c5e080041020300c81c0c41e89031103841c180b4100090040000d44101c04105103c1c0c450119070285100301d43c01e400d141c1c1c041d1100000d500c0306103644030700c0c8075965400300310a04e002e02e140001c0c440028402c0ca05c10307084140c1200701000c4040102140d5001403080b04c40482d41c141d07454800250032001c5040321402060141c07251015201e15000260042c44001c1140000b504500c042001c3e018414055030b400a09620300152100d102c2d203006400d0942d0788038000b14100b00c2c401c50104105484000144205 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 757130638 1250 757129388 757129487
    0xf09020301110f070b0a020c011b08060108090d0f0201020c2509140106050307020a0f08040501120504122f0c010f0201021204140309041a030d17060f01 67
    0xc004011220359000f25281d0404912040080764081001d40702c0c4641c0100036404e0062805a030601c04ca8211408842c002880c40c4041072500410303034003c0e00440e0312010030b09109140313181186400d0f45501428000e1004e2003101600c0d807030450b1007503041d02c0d0110000d20840d8440c00f1a14450521600205002c201d80720b128100411107094338010010f5201140b007041071264200501901c06410040c402c0c021807081d600c1d0840466958101c0006060084006903030380c1d820040010014a080d200c205510350800081c0800500640c501200c50059440c00010a03902002006010b911440000c0055511400140100c83c00403078100c0808000f6240c1d440185262a003da00741d0081c06103071000150808005401700f0b444403100741c1030f94012400c0d60b06e01a08070000800701c0d89000007940a070302c1c7c01452458941030401440403002e000c1e0811a51000f1468494001c0130760040100340942a645030101445e4002c115140d8850200d10703514a00d0698102450310b12070708210540e0700300 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 757131888 1250 757130638 757130651
    0x32018040b01050c0a11060702130f0e1b04090f0b01090e0c011716021e01020408011404050618160803090a05040c020d0513120c03060b04020306010905220f09020301 73
    0x150f0103401241e5401d86440040e000500e0701d03850f016200c0118146054202c40c00700891001a030b07511040e4000232104200014001d40d8044549044615490680405602011071152448000401c4402c6200c0496000c0b4900c00341d880c040980d03104e075100062280210400106004015400c15200e00d51040c0858420950400045410040d07007510304049405900204007031421080c1c0c41c0000352001d0044820079031900744820300e494016031003e0348603540490b09202041c0203000d01d1307105800340384201c03070b02d418280c44254503090060200d148070041c0d41030755001c0d03007801c3c001e03840f090b007010b0108001d00e83c1d140a01c83d102e03400692442e100e030070502008180da20702481604140d180030b500a0641e2540c0d0341003039400754040210150b2101740400006031940c1080380c11b442141c815144548550f10350b16225050318041b16129105500500c10008180d900c011074130107d030421154a1808003419080c18682744001c001c24100741c2c01c1c0b9548030000001c035003000c030400b80700307070000c0088 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 757133138 1250 757131888 757131911
    0x3101e09080c010b19030201032409090308060d050d211e1803020601120534080d0509011d030607050c1b0d0f021504060206150906010f03201804 64
    0x1070212224445c03140192140c1c1c14400f55110b075002000b20794840611140072040e070340f09034940c100b10381e1240c1d104540701d80c003140c100f542c40004140c120400340c0e2820b50f00d1207a03544154071900c0384940d510402c0400c0b40340300403508a10710b81020300101d040d0100000301c003c1e450280e541c0244c0e4024410300c0d0400054074549a14401e03d244607a4050b40546080e9081114140032542091020b81713540c810756900d80380c2c0d0014a03144507030300ba403a212803849805500c104008445400d901c002c5081c0c000901c204041a008000c4035600c041c2440c6c6013000266240040031030111581c1025010700c0f41d4000c11600b41d4000000700890404441200c00e04400c0c40070708501001481e0090f030300b0501900080f07001a080c1c3c8164020b592004008100820740006500080e4005600c0301006902c51410f02444083c144040a9007a0040d03c012120745002c03070018129100c480c1c4c80804259849401c0e03041900b01407400e80a141200602c20396590b0802c02466002980206a62050740b07082868243c = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 757134388 1250 757133138 757133149
    0x20d03060b0a0c1205090a2c100308030a0e0d080103031b020109050607020d0b090a15050103080313030216030c0e010f211511030a0c02060603101e09080c010b 70
    0x40801040d83e90005401040c0c0e1908a94032201403100184142800142d1690355040450406030013050501550103800035010361003002c610740301444000c0103c1c18448820788414811080c6d81e04041086e5803615030500c01401400700b0444a0554051800030640e03083c3c0c80701d1498103c80c060741d5403403015104e012801c04101038400d070080c0811203d4904001c1418084068a403045c00200140714822064072618010403044401c05656049040364204014004041c03482901c0340d44406c01581d811582c030f40d4098407000e02942c802e850109805000c05100300f1401d10702c02c00401b01c43c54010b9407440c001c0c1c1504000e0159021001200c0000300d8a221401214170031252a200b0100d00b03010701c084888004002c2c0b07041500d50115000e007201184009000706280b820400000c2580c0b4640000c41c40c00300c41404c610300003150442c0e400c0c0702041d81c00096202520b41360000c0040d1300800506080c41e400041808000b515042c440404103115418000d44004605503000b403091000a004001 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 757135638 1250 757134388 757134397
    0x3111030304062106080d170112020928060b07020924120a0204020412050c3109050f2104030c0608060d0c14030d02150112031e020d03060b 61
    0x2c000694404905280044141c3d200360040703042c0b1400a540e40d01c42800f0b60400403c0040314001c83d81790364001c9500c01641c000d090040c50312081a0303035a102983c1c0015240e05c406000e2403007019a03d0b0110015038075141d0b40501c07460180200300a41a0359029070906a00a030100b0313072144800100041122240b200c400020690600130b00c0040134034a403c2119411421400000510031210098010784039440180050441d62842d41a011f605213010b602d00141e408026002c1d03052402c601172250740000d580c05180301c98072080c40143d51180054030040124600140040c0b14801c804005002c012407240d2498050384042100514000d43e500c910b8440c40c0b0001f400302000360003c001841c130454140360401c030300a1420280b0b0b0420340328000d220b41e403600305403420782c6003280240041c44c0070070111504048a00113480358007001507511070020340510810003a008840455020141304a00064a110020180220002d62118001e42d10140b03038840401180c9841004504c41c00c110007030300d = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 757136888 1250 757135638 757135649
    0x2301090b010e131403040906060e0d030e040905070e04020a080a0b01051915170115080f15191a121503100603030507110a1d3111030304 60
    0x110250303440c10b9040d0203050001010741d08100442e45070000000c41c070303180280f00b140020004549407030820300d414088500d05d0344110103100054002e00314546401c00b030b05a0301034050034034409010800b404503000e007100840040c202c1c00340311008258140c0050415008600035107032858a25201e21303210f955440e41c0400a03002c6c1d104180104030514110000d05080085d24100e0030017643d94143c0ca240c0c41000f1241c2d01c0120f604601c3c54118850305425450043c42c0040d40e007400c0c400d040c0e0707003d40140c1028007114900c2c40b02d0400038240f007096040c00d010f858409848400c40d52030b40144070450507454001e000380700340f41083c2400800425020381350311840d14803025081e0b4541010024122200385c0801e07415000d2258400f02d4080307d48150302c015400b070b44460b565009a07240c0300501c00f101000c00c51141065032818070190345420109180040c405140040d280c8420b100c030840e10318207000d8801d881400f915000c8404001d02c3c1401015403142820940b408460b0003010b89901950084 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 757138138 1250 757136888 757136903
    0x201090c1a0d05091903020a0308070302031014060c03070c0306110301050609212505061303030f121a01021c121d07080606150f0702040209010e0409230109 69
    0xd80020380b5a03806640c11000c510104e030601c06200b40d00d00440d1061a500703a01580004c1d120000703040e041446640d002c41a49001c502c0d51414442c1055801404d002d034800d0f9804104440d82541c466804950340da1240314210784e02c45205190030a030301400c80c0011582030781448224405942d03110107a90603224010001d505081c40030b0140603500000d40041e0408240c8000102c00b090014043c40d03065441d40c505600900403040404495442541c0c0a18001d0204001c44e0214070700326070024040d69031501d42030000d00d0940d070080318503a4039005140f280031b00d8100060741d045400c0c6a0381400703031005e8003a2000c81030113a481c408004484001d03a404910602c00300a8414100d0388041d5000080300c014080701c08002081303515180300f80c0c0080e411680300a041c400949014450b50000440c400c035850b141c261001d008004500030108004e00a580124903094268001e030104949080060001c2045100358100394045e800e1061018560382d01900000703007401c81c113008140741240c01104 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 757139388 1250 757138138 757138147
    0x1b0512161a04230a170d05090c01030e0f060c0a021608070302151e1303050102030a050411100207031502040801020a030f050a0204050a120305190807080c1c05250201090c1a 76
    0x1aa40700e2482040303026014585e08005000c003c2e602846810700809450340113140c01010b0b100003600326903990010010aa01c461051048070200295099001d07100008064683d48940d4080c0d2502c3c00d01d42160504000000300441c202c2070015a10089038000c549181e81172400c103040000e039116540716524884c14450010850038030074001045440864503550043e01d90300d440301c3d401c9030002c0e91001c0c8003685903020300c01408400c01040e28a03460484401c520036003200c1c000b80d5601c00e50300c0010055440081100c0400d000303681a1401041c8140080d075885000010060040c14065125120280b0b400c0100328000d08610a40e002e549001d0002c5004504002c001456580d60901c00c07020003000300300418902910507038826007403501e911129002c1c10881d4000d044a00c00078070007507529400f400a600072540c01d40d100840e0708003007800050070b0303100c0000703441014280000294400074142c2a06070392070390549c4440304071801940700d4110b0607180d9110b00f0501c50441d0b0041100c18040c007 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 757140638 1250 757139388 757139393
    0x1b0309020609130b03060a0e190f0f140f03180402030a06120804080d0f05030402010c0c030219050312090d0213021c0501061b0512161a04230a 63
    0x92004a8040c0024115800c110142001403142403a81c2280f02e402610707001c0e40340c03d50508010303494000701d80c810203200c407500307200d501d60750380c102e01c081340a8510045c40220240440c580100020310f811584894502c600e508008031404c0c005041e100051140100d000e2000e100403060300c0e20044802010b520241c20388042101a401c06082d07016055502c000004103440100e0221000340e1045008075203d13850010090300303201d5000481c4c400d003d421600349402a0b400812650301540c2400c080110700032909180400560540000b50020100340044025004008031441161011400c03651558040808481507016204003940c0003114400c0d040b0061030f0881080421030b500c05801402d0028041d00991500c0c1400144000340d0780d17035001440000e0b880304140250400f20b49400032840c901d41e503515503e0760002d03119181a80701280841e030101c2105114280e07542c008007480078048039644100030005043c1c1d01250b4101d5102403240030b4022900100d91213100c00809080c85003100e4 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 757141888 1250 757140638 757140641
    0xe0309010f02070b0703020d08100b07060f230109230109020a0210020708091008100b0c0f031b07050d1e020111060406060f08150406111308030903060a1b03 69
    0x24101d10003980200c04000c60781c02650380140845a001e540140003e88006002170006000a04102300c1540300300802c1c020043c0c55002c64544541c800800075140084009403c000d001c095450448103400140d404160123504480506071207901204004018070070701c2500482204032020600c5451010042044910b20340c040c0c02c2c0301c0100e0041d92614042060580201d070f000000480d41040302041c9800035003410540020216603500b0318281d24100134804200441c100d00c80c00020240c00103000103c142c080c0f24903801c0c4a515800c03280c482d00040d17014040440b41c9a010100d61090394400925880d0140d030030109550440710380a41c14081c01040a05030400c504141c2c10f0000500480c402c501041168911a034001c0c034001a959007080519000c1201035401055035500008444c002a544500c01540155200d000002c40001c0101120004d0090703141c818142d40084c480081c01c404080018100103000720700b0340d00d40ea519402041d040b640842050110120004401c8004130b000c0d = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 757143138 1250 757141888 757141907
    0x20315040f061d07021f020c0d110c24040b0304051902060a0809030405060319051602190c08030403050a0b07080421090902040f031403181909050c1207030e030901 72
    0x403441906c68803018000d04401014a101051400c40c0d40080d024111010620a43c6000f6605103030108400d54011565503454a02c1d140b400c0c814881d0790381c2c034003030b0480307040112080c039013008109030f101c0e5901c09000c0d000350400c860545842c0034040300765402110368010b003520a5030081405007000311450040300e14101c010a614014801008041079651b10740c4003543c46a081c40e40007001c07070a50840c480081d6100980b0a801c034074a02e18254044940200d0010070101d4aa5107003601d0001c0750500700c6284c901c0e540082c545000000d0084180400030904102c05400f5050904040c0c440f0b500850b18803204840c06011511840b5a500c001144138080c0c00d01942507191030007000b070300c42c0822022030340550f11101418010103070820404c000214841f1001110300c01039820164100760381e880512000101c1072191001541462010505a0300c0c80301404400b1420403903807901e480c40401503485040c0a581c001c290b070000650f1148640242803040010001543c14103e5050040d1941d240 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 757144388 1250 757143138 757143151
    0xe070b04150e130b01270b090a051002060f0f0c030a020d02091306050109050301020c0309010806120d050a120b2b050f06010915080601030f080d020315040f061d 71
    0x1100400c1010fa690201c203903038891505140028090007400000d040c00005416405c05803c5c03a844401701007001400d02000c1360700d0700c001c050b500c040a40010350b416079107404c82a8095620035086000560000e032a51280c82c00c40744d03824403503d9041c5802091501104c0007008070703004000066607402280c0103407142c01250321004d4242407004002401030140012198046540c03802e0410841d030740020181c0061400798000c51410b8000703490705889105258949050044034408607503079883c0c40c50b002900260030340940350f203e0440c80d00108107074040f80801000540d11041c5800406c4244201c0c003071480300902600354040500c0084c85039242d800d44100c04c2c0b00d2002d00c4900410014454003903a5903084000e000e0790360402201d80222000c003c10118081901c06091004800000c0c238541503d0f045555601813413039034078282070984541148101018004018030481007050352036141c0305001110f0030312021b107200c242c03441101c42c130740300d0a81c0400c00700742610300f01c40d81001500d41003503 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 757145638 1250 757144388 757144397
    0x70b03042a050402180918070e040302210a030b011403040b180a1109090c280f060e0a0605030723040e070206090f0715080702101e0e070b0415 63
    0x60303a842c0064201e820000e00030142e0b02c0078000601c901d14058140b03036400384100d81c40840c500c83c401e907601e42d1150607010300361100440d07501140c04c2c9802045460089255001e100008074040c40300d064441c1c00035108140402d0414203e008950700a0340e904141d843d800324454190396840e1204049480f000d0800741c848142e078004c07240b40710400d1040046040c0250150301203494072105100d0701000c010a0fa018a800804644030070f66180380740d0100380d1004400c50121150120b4400c1c1124120781c0c0188205c11300c0b00320000d551074001d88802043c3c0c1007155184000da0b503d01007034555210864285000440d0304100140b0554007151905580b400d8424413801c168403040e000380c22a00070f6a030310016034807460800020f030300b08008201c0340b148e084014055091600440c1300003035903034402c4082801a21303400164070710310030002c205031620261000e0056074075002c1c80003e5103100c0807a410619060015100300300e4800214001140c4050050030300d13040c5803d5030071170130302c81780303940c807400c01 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 757146888 1250 757145638 757145723
    0x80c03060120071e03080702010f110604141606080c0d020c0f03030121110915090708010f0905010b030c0702030a050a0605191a0105090d08031305070b0304 69
    0x81d0342c80d010750009650300000d16601c1e040901103200380300d80d0010103c1c101d0507084103000185284069480300340c1c3c2070811010480b6146025550862030b42040c1a40340b00358820802408060b000300482103801000381ea0409102986800851000780555030104402d0004100c80302e80f040001d24118600e04001070821031910101e50030f11400c0c0c0e0001d051031744040014800100444841b500140343e00442118621850740c2e00311400024200d8a8481c242c2100001c5c0e0081400c000400301010003068103d091a24510240c0081028001c40d180700340301d040301281c112030610500d41603801c3c080006045603604c03441c0107410b42c44030342c00720707018051a0311a9000440801c4501602c51050b5800b040c103143c134000c0c16140303042ca0340100c84214208545107540220b5505610b42141083c07034507555414407280410fa40144003d8020481d090010402880b415442e1004c0d41e024450b10544081c82d0307407544c0c800d451340000c1d1806002200c0c040c10428030f603541d00560500001d600000070010703 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 757148138 1250 757146888 757146917
    0x270209070e031015120b0f0a0608030a02011b030c0c23071401030b0a0b0a0c05070f0e181f0e1f09021201061404021602091305070b0307080c030601 65
    0x5103c1600801260f482d12441c50042c0782c0c1211070100042c2042074201c000406a0b522600c0605c1c81c090221084181100c01081c5038050030b0708001c01911890003166601d40482000038020318203540402000601070f802988e265200c0e000d9038016244542e07032400300f148143c803113035100c134000d42040c049410613490310380340d10209001d01c60041003032008403480d01c519000098165940600c28a208000070740c01489040f0a03002610745070449031a01703030450351442ca000c40c07078407a19030003100b04441500300010750780312000191840340d655a00c41c0030101580f00029a40c4441210700011000c4006440d0305400d02d41d903000d503102d900d2003011511960b01c00f4031400c1d40c0503803000010380700d952144290800c3d41000302c5280c05c0540644001c0200c1c17442d05102480c006d402c514a144130703e8000a0aa4160100700070300758109070000c00c0200c15040440ba508601008020102c2d00c50040440c00034003604240103881c8510071588036000300c3e0b45d82c50030030708840c2e0005010b04d05002800e03540661 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 757149388 1250 757148138 757148143
    0x90703170d05071e0f05031311061606060b0405090106050d060e070909051b030705090d080409050f130305091c17180604180506030304090f02030a270209070e03 71
    0x43d07801502c400c0045001803881e000da1807690f80c00c640c00c0c81110f03020801010b51020407640e100b024a00321050b030080d07914141d5681c2800305003041d40300d94013082720b500742451281062030181c0300da10200305a80c5c0e40c440c0c0341c0c040c0c0035600c1520707030001c1c40d00010800140100d000303100b04003540360001915610740c1e4444210311800ea60242c00540d607001d0034410035041e44201900501c01000c500c1031051680c074503440920004001c40100900450380c07084540761145000282644100032980340d0307468940343c1000340301c100c0b802e4081001b250701050100c00350340d00000d40d2540550b43c044c03510360820244902d101818900c6400d114060700064042480410303804045e40003c03081650301e20600418000790a03031004070360308c10314042108200c01495068002c4500c18a07500c08106c45d69194006419030156500504440b81802c114060002c0b503a0700440c464038848204210711104e0180034214803404040400c0c1003164101c4000240c0307810104568082c07018541030300381202d2080031030b0 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 757150638 1250 757149388 757149391
    0x8011a090c250204140405070501050a09030506182802090421030903031508150a0b09090c0307060504060e0d0503042303010c0c02090a0f0207020a030b100509090703170d05 76
    0x4040003002c1c04108114a028055181ca10100c951880f44604040d03c03001c0d1600b03160b1242c907050240029030a6011401a140c44000f1508681995001d03d06841500b844c090385800708052802180d6139a8111031a01d1240a17001d003840c1c000c0c2c0c002810302e50901c0185500030708240c910004100c0e0107801d10f6100c100c03804407000165400314005007186801303000e8a41e01960520080d030352190611000708001380b800305528200300307402210340721444440001e100694080b900400c40008100005200054031b6060304029000c45d080e0300ea030780104135010b02460044500055400320071011b41d01c1d041e191840300c2801182600e01d040d5882030700300d9001d51941c0542841010070300100251385804e10400c0d1201e405c500740181c44501039800902041c2c0001c103001540c9070b80f200031035005a116810349005540c068a06500c40c2d07264103200250500c2101e45518049001d40007065606100401d140200090030040a0490855441101004d081070100c20300820621651020400750700656 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 757151888 1250 757150638 757150687
    0xc0a05090a0f0b070605010f080d1b050105010f181b03020a03062105070b18010c03020708070b0c0d032f0d02070602070b07020a031d1206100f08011a090c 68
    0x2244e030b504061409500740c1d54164022488540d01403400c0007107480114440c0d940b82004e00c4d1009008160480c0c82007010782d2038101510661a103000414500140c042c0380d4260385440d1000c0f00d02d2001c945480042c2c8186608041e0804074510b0600d0f4424003a4003d410040710302c1c2004100b450f00e603110403907403c000701e03010307803002c01e0200c03d01003841002d00004001d08600d0040926041060f1a000841001e10f0b002d0342c1001251801001454803c3c0f152001519031001920708050361216900311a0f00704041046a0380111541052914040c0c400c1c00c11410310003069211160800249004002c2100600082240208204240d410482c4011f1001c2841100c0050322840d05041031203a4800051209096510545820011030b410005981d08071061100e6010824080720216000c551906107441403403007044144034103000500990302c1500c611541d00c0c2d0a441d5a03400341c90a0300c22802d61a1825400d82d4a01405400c1120206602c980b00e00324442c5420081d50104840b6103202c0d040 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 757153138 1250 757151888 757151909
    0x20f010f020405150306090105010e030709050f071e0e04050c040b0706150803130b030a0e010e01060801111315111507170c09010e031f090210080c0a05090a0f 70
    0x30f00c103c0ca8182c0483d4000315041c8807032403c5181c154082508184180101810701040c100e0007641a41c04000c100c0280a0301001482541401080056040400d840d690007007440d50340716801e40001c00c1c5140c100404a0381d02e035081d814090003800300415024207980c00004c020440401c0701c2c407202d4000c1c640140f04032000104a4034148d88083c946549401c0302c021900304100140040385040250401e0350710382600241c1eaa2203251501001b0001c030b103140710440d4248002034940c2c0380190b02c008111040d40c03000f480f021084400000300351003080c612001d031a044901c01d014018021207000034801c06401c04a000c800b281300003624040e222003c024010401d00c0c10407244581c006580040c8000c05050000d0904007a0070401c854062718607101e041000f0f9071b11900d00c0703540420801142261090503200140b01c0316640802030800d0550030390080200201c2c81c80312502c1218190b2003074183e0110343d410903920390000c46103a841a800c00ba4407210758000419240c030803002c860000c1c0001d010703 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 757154388 1250 757153138 757153147
    0xc020709060f03120e1302280e0301060603060602030a03020c070b1201090614060f0c0a230105060f0a1a0403120801090f1407120f180209220b07020f010f02 69
    0x610150080b002840e11080200022004800717848844040e01080746d014000760b202d4518811b5428036000a01180d0074000d82088080003046d04078401c1c1c102440c05400a01c12180c41e094254150307902d500c11032005900401c201c400c0584250301074110704c521034080d40c003001c2da96401040903820541c0302510150340c14004000714a458880d04005000d9222601c08030030394040041c000c0d005050f444480840e0006125a5a600600c41d010380a80d0111000b806141c250500340d8514604a942290070341c41c0a012841d18034107441c3c18011404000e2500b01000e051a0036016551181011300d45a00030500022002401d03290002451201a40d01c1051561400c03016806941e90107642c02501850310701039556420708428250381c0201941002a891a010f03007681c0300500c14011018012480c24843c903440230207491031001314074022101c1040d240c039440600304816614180391681641055001ea0002d080e8100e015441001c50050b0784002c459100d05500f902c10524443c04001e50005 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 757155638 1250 757154388 757154393
    0x30b10080105060310020a051603180e0f0406180533071d0a05120d0e01110303150f09040f02100f0518030319020d080a0209090403030c020709060f03 66
    0x116200081160000a01c140d040c40004a0f8031215400f04016240e81c00283c00003a00340076074100c0e02c50945d400d80c1c1280b03044c0c01c0d04009040f009116004444131044a00c0040e0350110302c09028094000c4158040c1300d43c8a84da00d1000501c44c1c1c90b14103c2c6c0302600c407100300204805010860580300d100c5440f00e58600c03000940d80040d040002608d15a0100744d06100029a010494882c0f0b0f260380340b420b100c403261b203a0000300420025400300b0342c000c480340d074404203402c80401c4080c079102442c0c0350180c2c0010000d0040d11984c0c4d81d4558224182d0080c00012004402e9000c60101c51001074114100441c07980d0120fa00094100c905560744600c5000c1c003c03c41c1041c2c1c130880001012813402c448181c6107680002d01d14130401c00303407003584592800d181d50300d0381e0207000b203404012040250a0740c0d00308654002e51070b000c5c4c01386884045007041c000107200c4c4e401802200c0300104002d2011546581b90381d015002082803009040441c8604071010461992310b1003207501030800107a40800b143d1851 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 757156888 1250 757155638 757155661
    0x10c0801090c09270501050616021011030408280201020d05090f09010e070e040e0d03230412080703140106080426093f01150603091e0203191407030b 66
    0x187d00440c05520108242c040040110a5020402c0c6d4111018040d200295104403105403400b03045903503d005c00100010b040400283c03040740d4030350540406404c8072800d00490402c0c40d83e100060301582040f1401c2c80458800c07070040c0648000142103002010508010402d21002600b0030140504404248403460790064480b84098000312001c0c481e2100300328085854860920040084c552200d401e05109000740d070020b0059000c4854000c03951809042c00c806488410000801203001d01d030100310154800e0058006900072001e095420703074a400403c030b5081e4001001901e441220030070503c8130030304c5000246190002c0c54842900d0b488150200f21409640c00421340641d450a0031400030102c0600ba14841420340c40e800b20181645038903000d015004a034440030000b625100041000e50301688410b64440c000ca101c1d8034040c0d001c2d02c03c140c2c0c2114075100698543c1c011200d9400c1a20302009002d41280309030203210038519805102490844543c000711030030414201086448001d1 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 757158138 1250 757156888 757156891
    0x20301090f0b0a300f0f020a0f030c030b07020129040b060403020a03080703142109010e1509010e12030a15120f0804030f0b0601030e010c0801090c092705 68
    0x2100c00040c1c941c070302008440e805011110100e61118440f081000e50b00a134050a4002c5400004860358510140b505403524951a04200e1150101c8540800c1c3c120303003824240b081d2644041c2500e00c050441e01c031000620310003010b134811592100f40d0058081c22100341c111642c0d802a0b403503510005600100016510100021401502c0510042025070345074030f4410300b2650031185140d544c0d00c042c00c0c2101c16105082100d60710090002c4c1265aa0b1503500200700c02c000400301c5500715854948203203098403a152281413140c0d11081580b10800b18001c903241c1c100308080c00004541c0c0600f00a50704020440700d40340300542003c000c0000110050003031501d07102074210922019400c0614800c102c824500028107100280302014081008110172180a5a00180c107a0b0b080c110034641868440c0080310301c1c600080c01c06006403240e00c0c05000340003c840d401c1d240c0c1541c0342e08007110600200102d040b90000c22020200c002380c2503020074135006c004180e6540d075803c465031002c038803025501f0 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 757159388 1250 757158138 757158161
    0x1e21110111071101020312100e0105010c0510050c0405040c03050f061f051c1409010f0209100806040617071d1302010507020328050c15030622020301090f 68
    0x141080410041c0149080303481d00c55015001c580318026600c0100d165006001070341a09800741c40901954011100b41682150032601c0704e10001d1380ca900044070380f201c44a4008240790f00c0303501980d40400d613580146a000c1d030306424050401f5500d20000b03040e640501143c1c00460758410030700c8400b40b0051106c41e48414240c5148424540c1c1c5511520314061102c4520704011020400b5034504601c68400094044240402c0c080240300c2419848903202c1550381010325840d045940c0600c05150003601c4402030b00511010100030fa0110a4502c1d403070041403194040c0e601d4401083c06200f1119802c000c0e4804c40051580c51b0906131042d004603030b04454a01d00c641400e04010340201584ca2140500f0f03420b181168440c00c01d440442c0c6003011324466503006542440c04035907002040c1070003e4043d40590b084810b038414010038420132444100310100b62001c100005031140c1819200001c90741c1030215810342ca042c4800d00141260000c1e08048541600da5007250f0001e4010f001d910f44005 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 757160638 1250 757159388 757159391
    0xd080a05071b0303051c0f020f0d0c030b0f0d0206090a031b0b1c18150c12050903040608130b0907030210020c0d1e021509040606020f0a1e211101 64
    0x5003140c801409038003d401b00e0031174a40b40d44404101d807001507005124070240d900c0c0c09545950305c0c1c2c1da0044840d0850350b43c4d0884503140c04005e000300ca2190041e01c070304c440c0c007511144100740310a09101081c1d55503001641c100c0e400700a0401d6684810541e90700640c001c07001201502c007410b6107000d544410342d020380c2c01c144c01440f05840543c010410300c0c0318940214000034028482c44900560005550000b410310240800d40d4183c40c4801e4000400c040425a40c40c21140841c009040032160103683c03100c940d0707000741300600c180c030702551005802619031003280814083c3c40e82d0300260204200c3d4a8105504483c2c410021403e1140b01892003000c0d5001130494290038401103101080100c44c0508102d407405092a8214011548503081940103400f0058000413240c160701640d211a401300d010303901d061300001c0e40901c0490b02600d02e542c10409481600d00c1d5807900f4014660501907203100d4010041203200003000f0f008030441b95810a00030841d05200d02c400074020510094440365580d = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 757161888 1250 757160638 757160693
    0x909151806080d0503161b081305040b100e040c0c05120c0c0f10080a020f12041104050105010936050916150c11060c0f0c010e09150d080a0507 63
    0x140103420084091050a00e0701010030140947c42010080c82100b02809800c40001d1481d0413902c600c1c0960259401958103020044015081c40100d00c000d002207400904006503040e5540f40c02c0d0003006c044480da252840624100d51112410044010000e02502d200081c1c0c8201012060003c4120340303200300e48a683c40030350b441c041403403486903075407150400440d480050701076030b02541078414400003c4030184d00c91314100c4112141001c240c41c16190781006c0f06a80210780340c42d00131141a25410b0b51a02070b06031902e008020416034840d45441021100d03103448035070b15652102e09141c00302e03280303000c2294144224043d0800e0b04100305030003c403440040a100d14a03000700040a04401031030300d03039040903641c20318092060007050801d600c040001078103040c0c940001a090200488070017950601c0d0407110054038440c00c0d0440341034002c0c451100003002e02242e0b220b204080c40700600400c0a0031890742e03d06440e980200c202c000460b4011078036809100354071420708141c0000440c4003152 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 757163138 1250 757161888 757161901
    0x515090a0903020a0c090e06011707050613050301020d0603110904031409011b0b01081b0307090f140106230f03040b10030804030506250909151806080d0503 69
    0x8004008003606040d94890300000d0800d4400c100d8100900d0b003084121004a8441c14104040c2080044040e071301c0c800c05d0008902d0f0038521248501c4001c407100245502403a000502c2070a0b08006040540d00d042140c000800d61800e0005211090601000099aa040d80b0b404005c41c01c09950311409000900108000250402c1c40300402e18442d000c955140c11413040100c4801c1d0180840b40154060842d441040044c5440c0c944e041c0d86038801614036581c200d03550304034032800365074145605a004000c10403600c00b4a074400303040504504000f20b550321502482d180307000000c0c0d0101d0006241d0031851117120100381c082e199a08070308401d8901d041c504110a09544c00042d01c0906401a201d0200c3c049455810fa408000c0d03600046440d03c680d52810000d40700c0780111f40e00202501c54081c13000c1c2d600183d05444078003451980300d4070721880c100064403004107049444103415101a44020030801c40700c80c40103040d4208280c1c04070b02c940c00c000e4001c1c1044100d0745104140081482403002 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 757164388 1250 757163138 757163149
    0xa0c03291c060b0f060a1407081b070302010f09081f02090a08030d05130b04061a03030c280f0605090304031e0b06090c04090506130c11010515 63
    0x103105108200314000441200000d021428a04071074407050304501072040401c022030b0030030b8202c424210b402241c20101a02444154802c1081c200c00144e0104c000311032084000340580311b0140101851814080458000c0150554004601c0c0c0c0c1d60344031034400c01c2151380c0142c452580111300d1800b2400603140c4a000380e41e40c41c805008810820301019807000c2e111017a8140c41c10303000010640001682e481c0320860f10395020414200d689420100050aa001488401c0b1401030340849041e0b50341e40c0741d8136600010002c02c07596070001c11100c002c16025540800240c02c1c040e000340040e0034108013452403c6440c00c00417100f078810a5120b604400070914907020b075444590859000f1429540b0005858218401d9800050068010004480c0c82c0484140803920181c81a0800b6070070b5229041000700300141202c0d0400c036484e04002c2404000642d8000301e402c000c014081c0c0c000c014032179180f402512341482d000d00c0001e440c01d16202c0e404001f402110741152008946103c003040010200720b = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 757165638 1250 757164388 757164431
    0x2041d0709060207120203031908011a031005130f1b0207080d020a080f13062a021f0e13050f0c0a020d0f0c0c140a1a070308070903080f030a0c03 64
    0x3017285401d00040340a5490501c215682c0b0181d004030300e1959540380c1d0014206071403c2c06001d20500c00710396002d1501c0bc03044100d13030044100c0c60000c2c0070b0601c0c0000b002800c0c1900104080440e86580c00103600070b00d68069400d0603a281380080090361035410b002450301030180c1c842a020380c800e0f0600041980c021404442030307500001001d54910160201c84211b118280030301040c61403021001030701c030382d00450002e1111340012611084400900701d24510032070345400a5444040b80d514245080180c00d0050090041d508103054150000700000f0049c0d600b0981d90007056407104100031120094038070050780412441d40c003071f0400040c0c840c02540c46141001d1501030165054041000728001c03ea40c0003515801605002d08079199447c0c580006083c809440c0a05802a0007140b030004915040d9202903205103082d0030b0480719241200e02d900080e001a040c05008070340440401c440d2402442048084d24010f0342d03904200780c10f0021240b0801c1e49000f09440c0020204801403038201d80e0 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 757166888 1250 757165638 757165649
    0x1104090f14070c031707051c2309010b03060406052a0910030209091618120f110303070302030712050c060a0b01021c030509062206051902041d0709060207 68
    0x1e003000c41e0f03038030b0203841610b165441800c1c0c6211101c104090316602c00b00411140320071000080310b00450703c440d101980c20039101803207075591002c0b1072a2459507051019610406100001c90705901800109007005416103054840e0358880e02000301c99520382c02021842d0404d181c800e005642c1100071224a4040c0082c007910504000c007481a0360352181d0190346c442500200801a1801e100c2e014803010030212900e00b011a004100d002448980d9408520443d0034076580312458407003950324084044c2d9204130803111002c000c038240c2134030f0f00c0420240c140b40b4441d0b00159683e1020b03081000300151520598810808104021388040c03002240198000c0d00940c0082204411500140d0034820f4032400d00075a202c18000a54040b54580c100a01901c6880180c0d50f6588540c0c030a09801d4803050208854010780d07031002c10000d034255004980c09014203c0001c00712044030860701c2641c2c855800444000c030920581001c07201c90102e200e8021065051024050f490301401a44454551003603 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 757168138 1250 757166888 757166897
    0x9070302090121171c020309030403061e18050114220609120f080c0307020d050c01110708030a0509060f01090b030f06010f150201090f1509061104090f1407 69
    0xf1141c0d0034005050040740c295000080002aa01c80102d040850304115806000402031101c480086515071089901030044900a14a0a415070700d8110180010801b0294450350180000c09007200c0d910400c2404034107001c0304003043d40182000ca0a441601c0c182d40d030304242c0d282c28050092030300c5055410070749030340144c0d402181150805130018481001c014025000e032059814980358015410b104106482e15286d0858485140041039400102c0b80d0b8809a8404841031030140d0041e009009020303403580022802d00d0144520080c150011042111051004401c0c8964980540a0b003036204400780c008003000d140403005000b1141043c858030300900d03922408030050340c4080c084008403c000c082228515651601003030390f080c003d841040d0a0208040700b80b112584107018032100316400103902224010243c5500d1000941c80d10243c200c4d9513078946201c0060401d000e003020268034074880a4880d80780c40700002c10303190a1068000c0c910b11f0840d00761103080f004440302e0380003803041c07a0 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 757169388 1250 757168138 757168169
    0x1030b09160e07030f200f041203020a030e04050f01090e010225050606030319030c0c1b0503060a09151d030301030f12030e030a14130303030b09090703020901 70
    0x20300d24280000d030303840300c10400c0303900a0215a05040c1c403902800b80005950801904010b080c00b40d00300e4101c3d00350900c0b0500300b482103d460800f600050180000030340300361850700c0d5403500c1310521000b0840c01107025802080d00601415046021403da011080d1014080c2d8070b0a20744150170b01005000c0c40e9219907a400c1c090a07004400d5040d95800b0048030115510303541c00c015140c2c4d0040c481c1c082203480d8401c020000c3e506e0300703021058507211284c62298501055164a0a41c0982081042d003000c00100d03280100209030840c00e914050112000001590750601c1c007894248040140205640d038188440c0c50f00040a0f50840f44100e500042c0002c5c1c0c0c041920580c220551012084030010721011001009000070f04071555000380c458040c2c035100c11505103040c2d09840040e400551282c105000300720ba030f28080c1c1c010501b440b580c0014649010412004440d246070950829800290740715104d0f200c50428001d0030740c00030b4109001300310051469002900d031100501480ba1884062034 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 757170638 1250 757169388 757169401
    0x9180204200a0306050f0a0b0a030f15062006010b0412231c02151609030803070f02010614060f0a0323040308060a0806010b07080705010606020706020f010b0901030b 73
    0x21103440076100c0c0310038855403106084001030284c8814010309120ba0000d034052045407600c1d10280044030b0360901c94034200711030b1a000398000d165610740e619030151914086c008400e0042320160181c091903c0700030340840c071382c042c0000d18512140f4009481e0310910041c00f0444802054034221902c03180c0e850114069440d040c2040107020042203c0d12040c00c0c01c02010ba90040b0b031610001010304028404180102d50072a511440d101c0c00480d00200303c00401e440a260304484100341200741045000c80750340e9551103001d41d10846803000096101e5040b100e0f01303a42070081c00c00402e80341d61200350180b00c0300f00090030f9220b6032280030158000050807518a41c0280c00c14180304442c95964035441b0744074410740d90b47c081d003144d00320000746030040003400900c2c20415681c203941142c2c0c000c014a0307003401c11224036907001c514165207404d014000100019024091580601160b5001c0c0c40074502c1c10b00046e140016030000503500d40d04040d0071201648400d04c0480c1126005080f1140746e03240c1c503 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 757171888 1250 757170638 757170671
    0x200a030506190e070602070503160e060f03010b1e010f020f102c030901120203040b07080c1b0f061b0a1202040b0310030c0902040b03011a0c070e010f09180204 70
    0xd50840c0c643c0c3c0150240002c5098000c00c04608413a0f007541a104500c61075031414800080c1e0f030280c640441041d00102c1d4207420030a10029040c400a00002032562103440040c842e02000c4c2141d14a95101078400c60035560f001029450440d6107000921541c040c003e61f168407542c80520701d2904031b41e100d46400b11200791000000602ca421169104517415602c1003540782e80c071403c0c070036001c02c106261480c003c4003070740b080302e1050341c00108501e11034444810444115002400c0c4912040050050710040c0300c0110344490128010801059211300044460b4289100200103038540c200e00f16201031622030400c203c032078a9841c0d181c00c1506135030139604040207000d0f94100940c20340000c4104050280d8860311601602d004850184d0070303036541c0d0003400c02e9120764011304501c00002d00040160000340301c4c03030706141d0031b619880904010030140d045140407060b601840d5983d50400040000d002d22280310f00c01740414000c14400002c1c1d13965140442d01000100a0241b90398944019900c40c00 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 757173138 1250 757171888 757171901
    0x91101021f0c0e18040c0b03010b07110103151d0a09121b0b090607080903040501020d180909050703030810031119240909050403080403080a0902040504200a03050619 73
    0x2490341404c602e40d16000c3d520b1800445040700d9003070079284042080e03914501980d040341d043c80c1c02540b81c00841c1d03503105000009542d483e41172513101e03526114291076243e0400083e05440624a0545400b04600c0d10707005406050604564030742240e85d80800c0071000221440c1205080001d4040a042500340f0b400052440c054504490101804450000401c01900495240d0b982000c1c603200d9445003070300c91140344540742c00b5a10040110900500504d05e0b00d4100740715004514400707075141c000750295980c10300100d80c2c071341080c41d040c010190825440b070740000c602c00500c200340d0300750b642c1c842030807803c1e41917207100e0100c600e06400c00e200c884051101400e1911450101c0c40510003030030400003100309141c008550042030218200f262403140380d00c02c98240e9030303904807910303941c80503500341c0c10203031503d00c0702921513000c0409a15030b40280c6004500c101c400e0301e0b0244a0403007840c80c540c4031064440c4240c040d0308003040400c60015080f900480880c0d0009118143c020045c0001e024 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 757174388 1250 757173138 757173167
    0x62409060d0f0b09010b0307110a021203040807091b0c020409140c03070603021e0309030c0303091006050409020a09050613060f08070e0702120904140a091101021f0c 73
    0x800280c0c019505400341c0203980b108040480c2404500000703020010300c440240a0250850024030006180c43d20a00500c910904aa426074805401e2a00030880d01d904410300c0340310943c40040c00b040190410403c2c00e0090402c41810000440358859540d802c800e08100c62082001c07203010501596156401000b8550788440a00724045140e15101d48a600222209200707002d0410b00040ca00d001e4001c442202ca80035680c44114031200c0e4044246820107030241e0198481400004494401000118003502144000306252a100d80300d18064484a8110a004a041c00e10400068640408280c29560310180200d41d5650714000b11780041c121088050f85141007500004510b9a440040300a5400d4941580c01c4151154100408418195040d0700140e100e00090021165486e001d000c00e258021300c040303500d10a503074030304001042c191004038151b55121340c110100003e10450114202c820f001420036889100d10680c031b000190550942d0681d2615040d241c10ba1043c1d0f00c03003402e0718 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 757175638 1250 757174388 757174399
    0xa030c151103040f150c0206041b05130203090712020303070b06011101020d0e160e0c090103060f0b030702010c140909090304030602040b0c0706080402060d231617062409 75
    0x2a0070b0601813200091008240e03601c1408449814032111640a40701108a6540050102c0d49840c0d4509540c4400c0d102180e1540c0003805c0f001c0b446503a050210703d08800c0341070000d80c4030b051002e50f090900c4280c0c1d100082c400c01401c80400140c901209481e0071940200c1300d02d0b015520040140d858146140800c0364952000031801e182c14416400258605500d4007121007034941d0948403c60008540900e8400c00c54043c0060111107500c0010070b20140e041c507001c00c0c250341c1c500c42800a010f01342c0081102e00c1e004420014000d42c241320b044000c00c182c0c074100c075004810034009681c0d031046c001602d000b440c441000440c0310700108100d800030359003c041159243e0b59883c0950842d00011030080071401490300000d103681c41044154000c2c2d40041240d0314000380e0b1000d660007800c04a55030b040700d25a041115040d410014111441602c030040c441941044210008000c8444848620140c40f891014407025031070b11100c000081550300c001229000c21003c2c510b0090141c035040740d6104c3c = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 757176888 1250 757175638 757175641
    0x60e01031d0706090b031026030d05060111060c0307140403210801080114150f1503091203101a0f22080c0108071b1502070b01080a030c151103 63
    0x4120025080086070f809558103141c660300c503a01411540300542d440d01500740310641c1400196502106044419550007091a80c1048801481d046401038054800180d55440030811103503004203100400465110290007a881d00b0000f19002c1c2c0400f810010420400100d0501070741e1360441151301454001401d584619661024040071071524888080001d00260001034805414040c0c12210403003600c038081c1681c2c130204e072030301681c004e0031041f42c0c08001011346c072480b611040038a098580b00d08210507034919001c1c0340b080c41c20081004030305440a0420400003102d20f05500002a62007101e1039105492160402c4401405955804100213400040d180448880324070203c1c07440300c50080b0908840e5950500c0d0b03442d00764200a942c08201d6a00006480034441c0600707521002c1c600704102000c4800740c40d00e81201030340390160140306900141d41c0b000c0c4072030500c02c41d0040c10404010108036900d03580042003a0720484009080410904400c0101d14098000040500d42c40c61180e849 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 757178138 1250 757176888 757176941
    0x20a032001060f290d02130504051e070906080f0c07050322060804110f1f0e1216060f0516060c030f020f1204080918040c05030703020a060e0103 64
    0x10030300c940304100411300b450342c11012400c118020752004025100c603d43c24405090719440296020070001c84600140b900301040030b90340c07032246a0046e4820301e10303007100c0e0085028010360030030702a0080c1c00b0b001002d03030100502c540c0405c0150b4031640c07800096001e0303103410120384850f00410800801502000c01c800180c90840540135010382032005035600c4c1e43d07948003020380f03000e502500d000c1d100400c4a40d00164a0600f80c00c81407904902811506020031494601c50081c041903056200107100b0709622509131600e1806400e404007a400640800c0b0480042e42e185203510f88549400c0c4411142400c480324040d006a41d46d85c0a007000c030501014051610100030f01e00e40802c1c4d004640fa080d01c100c40180b00d4400d6610b5548030403c0701c0d00e4803540005002c404d01780108101e5110204012401140c3c881c1c4040300b5801030310300c1804505060a1910003c0080550080c900a6000c42020030250351418841c404480c070074200f80182c0f003040c0c00102c010301640c603c032540d0303400880c155620 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 757179388 1250 757178138 757178159
    0xf03010602150703140604020a0c020a081005100509070c0f1a07080708101202040b1c140d210b0307080d020c0a0b04050910030606030f06050c030403020a03200106 72
    0x1202181e886080d0b82d954880b0103604650800b620800c078000180005019400d155004182d00842828886807507082d41d0300003881c41256812800780c0d60043e078640052481d42d40603031a04060001c4412480c0c60504011039005040200b03007804000500d50b0410a102480d0075002c580b50b00124100358500c007641d2406a4001d0542e254000607443d0000210303018850140c190144074a4160050400e20345850901c41d200c5695050780c2c07080e515281010079549560140c1001c102165010030b00311428103001c241d1031020f000c04c1ca180d41240030921026544501f07502c90074440070300164182ea0f81011b10703000804410800c190140b080c24404504481c00180900411001d070b404c40e24802c4a510a01501000a10900c45500010302040c440c500d000e0240303030f500408180c2008181a030741c0d00c0e12015036a140e40150b0324489002d000c101849018094640c0c0040307001ea00c28514241954000d6071410f103c0700150030046070740c0d0140180c20700000005081c040020003071200715102c00e40e055 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 757180638 1250 757179388 757179403
    0x703050c0c061006080c0c0a150608100903180f1a07060504110301050604141305120d0b1005071104052e05030114010e1918050a440f03010602 63
    0x2c85c0200d0000340220343c800088801c008034210142c0300c004d01039640d03620a07100420b401400305440d0200451001d02c00c200c1b16800b00b440e038401040c04801814003412004405d030b4504514500118244a0007100d208401c0c01c45951780801c6181b03480c2554045090300541c03034002d1143e41001700348002d000c000d441207049082c2c200c000f00900d03210001000115600f04400d004050300140028801901010b440030341d66018100740c0d6190400d0a244c4025a8132410510a94540c0c81030210308900b4210007004054665041c500d02d444000e0322000121f21404260900c25500c0e030000440e56407071404101e1440c21003d80c00281006022a25140d0780c6036402818002c0d071074402001c40103484c04803524100c0d400b4580d00d030b40c66210310071005443c048040f05078404e191116041c18648402c0404880000d018402500e43d81c00d035880d00e09003240820a600c00320f03040c6400c03c10314605480c3c0d04010302546880c00c1c03014004030051500c0b81400307550b40902e8100e01c040000a802d81d00402d005 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 757181888 1250 757180638 757180649
    0x150e1e01090f051635010204121208010b120c070309082409191506080d0c050d09080d050a1211120c0307020d031a0306010303020d0908150703050c0c0610 68
    0x24005030305c42445030280e511569110100c0c0031030007100304031142e01e14840043d8441c014000740c80c2075118100c000303645a0f07201c0115146160154042c80456210b03141ca1b001d04039a41242c0c0c07906d80d80109031180080c018086e80b11030000001c4001c2098001c0340240010401c00e0165500010150200c10b00348107420002c800c0d180403200010816240070800960084e007a800211034502180c40b1044985010000e01e510280e4507000840c1c10b4030100000307480e4607003564500d0340c50525490044c2c1400c0c0301c14200c0c01070000000c01401803880c0410a03c80074000d528255848852000c0e040b1b07501004030640044191800e10656900765008000f004c00c0e91181600440e507444541548005104c2100c2d2070006800c00f5903621070161082d0048009a00580400969405139000007402c1c12001e0380100c0261303020801d00c045058000015000900d940e001915201c0c000e84103400711003000405845c20503903100009040c811010302911043d00c500c0046034018a407100d1443c0500d419805103 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 757183138 1250 757181888 757181923
    0xb061c0b10050103060815181501140109120506010e071407060b100c0c050f0f041b0305090304030c15180e040c0b030402030c091b1204150e1e01090f05 67
    0x11441e250300080b500001200041c00014a5a51076055005034915210488d400e001d440d2450515440110070709018200003484901c0c485407110000d840200b103036100000302040c150b550f00200d900401da660460b2807c5c40c5000b42030352080c4007243c24440100700010094804102c40d4207101c61070f401501c0000c02a2100b04412140c01c1e400d84100820140040500c1c1002d10300348a1401c1070062955492409089032074401403803000281502c0ca07400c0d191210b0700400c100c2c0241298036014440e0000c01450240d4034140c2503446200762a40e441c041c0721104400701e450f02540a202d522a8011040721003001c4e1002612104000c8109d001528140d07000400e20b2008070754400380c00122030107654024024a0900300030018070220140c01042800c80d030000c007070806110300c0200000e1889501d45a4040c90714901841d01c14003840c034103c1002011440c05028520740040024440050708140c1d441141e018101da80701d0f405005c0710080117041c001e01c1c45a990820030700141d8000300c680880003 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 757184388 1250 757183138 757183151
    0xb18040210021c0e0102070317070614131128150203041404050406090204020f1e0a05042105010c030209040f090b0a020f13060e100302070b061c0b10050103 69
    0x883e60740e00d078001050480c03460480400f10280c01056026900d000c18010303140c4050723030790304d6040554800c0c640310411a0360000c0c0b42c400300801031091600518404a804446080400303112011080d01d03507004200c020282a200003541e0f4128280c0c80d142001e10700032810f07407801e22050084030164428072003030f0003d1804940b407103400441514144d803201440c0441c070070f01d00b0007004040c010140c400d461855507100e4110140c1c4860005142c0322000c1064241d44440340d010324240d03415010307001c0304090b90501244030000d03400401c9404460400d420b06600900b400c6580c0c800c2410040000c0a0b036291100108030150140c000d8244504101e07010030000d01d44148400689941000050401e0043ca00040c80b1500c581e0241010310a40d03541d5074100411628494500e842c030350480800b04081d14503c1425141c05014102c41c03100e223282c00e5043c01a581e545c14500300c0c0151440380b003000b81c0c070900350710300c0403d0b018180060b4110105640324209902c05944140080c000d8900080c280b00 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 757185638 1250 757184388 757184419
    0x307050f0106033309110f0301090f020909070815040209160f030e0a0501020c0303040c1e030f06020d05100503060903130b030403050415030b0a091e0b01030b180402 73
    0x1164108407078101300980d03c0300d001c4145110340d01200d00c1190b10300003081c0b09100c031a0722031846511995403003800c26801e0295848200f04203034a03490401c030311980c105800680012030400c1418281607040e1050f28864446608c01820140c4a03002108607110308005421584109000030707000d2070090756109807a03225124035960000902840358042303200c0303451041c20380313210b5800700840382d0010301a1841d803600d5a450a080e41d204811040d0315600c0481808140206840900b00a10501403042c002c190302e0005018051082c7c8405802000c1800e00c00c428005144c0407900141c070b010504104ea0324101030518201201c500405001303100350800a2141e01c40081111035404603080c0c1f000016140588900c03142c1c0c4000c2c402c0301000000c0c00005100340b0044040f044108031500c0128a0903990000c0c4078449400d507104080d5641455015848400c0c80308070304425088814002c6000c560800c0181c01070081c1408081d00207142ca0b80841d0104002d00d106030080e80f01f1201e900e1149084c4 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 757186888 1250 757185638 757185641
    0x22d04090308040b04021c0b0a0501141e040f09050f0c121506030a020409080c0105072102090409050303091f0b1c150c0c020f090c040b130306020703020307050f01 72
    0x10009001c598008089001301c4c0310402c90381c0e446840100340c10903030306001c2d100041d964604041107400600c014280302005801d0b02071107000d0000442c400b03603004a402d00082011042d4801115844400784c01c40340304d504c598000400f19a88100f084c090700000e40350480d5a0801030200c2c203060301030394000b00e5480c9008800c03401d4164041008002400c00d541842500380f50103043d40b80e05202e1902d502005071034a0080e41c0890b13016800240d2110501c91215003590001880f000400800102c0c4d040341b0600d01091040303c0780a800c0c0140c6078059400400c00a013000074018003248004000c0011244000404650707441c0d60958005a400040503200c058074174407000150b020740d16030840c0f00b0610620074181032403030048a000c1c18000c10218010101c4a2480c00e16000422510400055041c40300c0103040525060b1140d0155140240c10746000340901d00881003001c1d4000b0b0100c0b200580c6242502c041e64118008554402c4949400f07942e2744d000050072526401a00c3c5913103480e00b010b = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 757188138 1250 757186888 757186901
    0x2040b030d09090e0102070b0414071205060106110f070b090406050618010c150c09140d030e09070c050601080c091e0402010c03030207060e060405060a18110a03022d04 74
    0x7180c0710b00102c2801e0008100107494884076040702e966081c010b10003c1107445100901039401003982460884030041c81d142407021981010304035905003403481d0300081000030000d0449525151a0f182218405515030400808400d2681140300741034000c921180c050005280c0c01c4c10031607040249035981c0c014040e1900414500b0041d000c40d100b139002055004040f0104083c1c0700c1c52076840020f0003004c580e000c80e02d1080c1d0050001c1c244410500c0390340700802c0132101c404030482d80c0c40b03002e1140c0e590042100c2d5040395440d003d00c04180c040703421240143c41400b101d44d070004c01c0c0c030301035070311031416076034074410b9080c81803141c0003560100f40000c40000c00a240b025410582c06125641c3d9001518003d07101c807000c508042d0700b081158080b8a540c85070141c506244006020942050305040d4686400644403c4e43e00d40b8100d10030404060928135219025400f40c0460268140c080c0018802c20b00da0784042d420032070300300c1001c811880400707140041d42d0b0100384241d12410f01ca400e220072280b2 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 757189388 1250 757188138 757188163
    0xa051003330b03040807081305040b060c1e03040503251a19050f03090606040c0e10120608030c0a05010e060105092a1803011d0316060b10050702040b03 67
    0x807030441400301c4445035000716889805403000c00e2900c89140d0703412802e0b900124001d408807181c40ca090049140c103000390001703902c00300c0380303a4107040c40d4049007615644481003001c0b02406490300c404180800b070080d03c0c0204001401e5481c4c690203001c8080354003c0300d140203000b520104201141c00c103d503407102ca2142481c244040e003030005803101110151040103c800a03c0b4003400a4807192011500451080b41d0880140c0903908080c0c0c00c2c04251051600d504080c030500d1030105805494002c0c5102c110201450004100462050000001e041c542c0105080380400035811220340d40000b40c4100d060320407c000c002d0880880c1c00c0d00e403603510a0090660019000e0046041056480d42c00400c40d0805600e18100c02d4011000c2121a030103802c0070b00801c1c0c4c03e849803404619080c804d03580f0313078140450451569030b1a40040b5450348101e4414151074140e0780c0d818001d200042d8020540c0d28000741a001050354000c0c4080c0082d084414128443c9040c03402e54411402c010689581c0c0c0302 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 757190638 1250 757189388 757189481
    0xd06050303040f15180303111e1009061104030c06111b01031d010906061409090d030e0f06070806150903100c020f06040c050a080a051504020a051003 66
    0x10f090640d812001c900c042c681204201c801700002e2003482020103104002d610a403506004a040d140289040545c2e15200e02d083c02c1c031102401c200005c011904200c02d11081c000000d0030041440c040005000101241d0540b01c8003240c04070800440c0c2c3c202d5810386d0318031345442415148804a560307a802022102da49052030660446510b54060b80100e040c5102140d007040b08411504a41c5084074980d40c0b0a46415841c1c100400c04105026404141c5480c1070b10301221a1070000c42807665119020440c2040569855548107500c00600629441052a209071029801e060800521040f02a101284590300071a030610350210144202c3d129800060f01400401c03814490f0800145200750a94042d40940d1003043c2110310140420742c8202d1240c80352450341814402030000700310080d0007072401a44a0545100072800c00034669100b201082c030040500c1e03880b0b2002c901528815401150842c0c1c6000840c0312442d05a00300c04103200c05010500c040c41c0c4464942c040c0d80030304400405a05 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 757191888 1250 757190638 757190669
    0xd021e0406231507111504120c06080919230d080402090f04051f24090b0105070203030d0902180106020c01171501272603042610110d0605030304 64
    0x50818080d642915407541b000306090075590002d00c00a440440c0088801c000b00010034480c00340c0100d5a16082a0000020600001c180403880305511094201a040c484d200c00140707443c1d0100c10108071849003050035203d0007601d0940242c00200161400c901c5018984000340d4050780400e0442d11540d000401011803c08515950511102001152200302d071035540c440110341d00708507207140f00100200320b40f850b64500510b01d411201d80142c2c03181044010000030000d80e6002090703900c05041c075040010a840c292000545000501c4c2910880a02d41000000c1203500440d80445c0c401c0d080c2c0720710b0f0300c020841c40d25106038031080f078a4000601e100845503900d0b51140108403100c103a0380c0c071030402e0800700c035008916012007607102d584661845003803045055168814001c0d241d5448000b1810035040c22102001c0913071100709808903156a02217210207580c100100e4440c51214507080182d50300070500c154646c0d008607541c0f500389091440000b11410001308403802c8807070f80160f90407032 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 757193138 1250 757191888 757191923
    0x604030b090a05010c021e0106062f1006031a06060301061b051905120f0f0a1b08030115110d0507240504060b0d021e0406231507 57
    0x801038041d04040c0355124040c074120029001340700c0c2c4001d04c0c40742c1d0028020300c50140e0b4902580d1680038034568485e418070f4010025190800303680344510f0811124a2082d84c1d0b4070421360010446605051154818511a000314480c15480201524024503141c0f0550400348a00e0003d110151009a04440204010071100d4440c100840f038518000c070040e5104442b41c1c858910301921980e41c102018466800f54040100c1040300221462040c0051340c181507035515280603502805109605065000565180480c030031400d44c0e0b01804070a40d502d181c1046800d040515410134003968161240221200c05c450340520420b0f8007458240c8001c00b10b000d1803800807580c0d03400a01085907407040c142c045624001c192040004440c800300c82c006401e01c2c103802c01c00c042d03462100991b4000c118900802000d0303124090480c401d00ea0b042803c00180700c3da480881c004001613400400000500300c10703881c0e06c00302e000e01d102c10404212440c16001c0b42041c2291f2103441359040c028000d001d07000c454800c = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 757194244 1106 757193138 757193153
    0x20d050906070f08040f0c15080603100b0f041a09090a0c0f0506092e0c020a0906060503150a031203021908070c1103030f0a09180b060403 61
    0x107840c00003031406001541d003c0e201801842c0c88908039000d010213640d0349001403884a11281404c040c0b280010328422083c1d0f2b081d403083c000c1d1459150500721502462007090002060f81891910f054100001001c20861004e40b41e026100c201c401e0b0b80c0c0301407480e0701c03c0c04000c01821030340001307150003900c608090300200042c200380b10007442030b5180c220545922038030a0b10354035a050b4000400200002d004600e214010505a52100026900030500c0e9100c0307100352505d541050326491354000340c5815000303038000160f0500006408134003c6402105082c0050401c0d00955242c0c0c9440115010500540002c41c1e00065441080714081280c211f0103820351030808c8040c182003c000303022000156015003511004016041d09640c113000711a88c5a01501201d5981c1e01d240390042c281040c40c0c820201e035180c883c07451f042005014044c00007074040040000b4505820f550b04c0c01c1 = true := by decide +kernel

theorem cover : BRFrame.Cov 757014388 757194244 := by
  have h0 := BRFrame.cov_init 757014388
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757014388 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757014388 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757014388 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757014388 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757014388 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757014388 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757014388 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757014388 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757014388 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757014388 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757014388 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757014388 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757014388 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757014388 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757014388 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757014388 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757014388 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757014388 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757014388 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757014388 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757014388 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757014388 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757014388 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757014388 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757014388 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757014388 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757014388 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757014388 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757014388 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757014388 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757014388 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757014388 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757014388 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757014388 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757014388 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757014388 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757014388 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757014388 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757014388 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757014388 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757014388 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757014388 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757014388 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757014388 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757014388 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757014388 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757014388 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757014388 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757014388 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757014388 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757014388 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757014388 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757014388 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757014388 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757014388 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757014388 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757014388 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757014388 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757014388 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757014388 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757014388 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757014388 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757014388 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757014388 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757014388 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757014388 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757014388 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757014388 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757014388 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757014388 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757014388 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757014388 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757014388 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757014388 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757014388 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757014388 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757014388 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757014388 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757014388 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757014388 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757014388 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757014388 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757014388 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757014388 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757014388 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757014388 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757014388 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757014388 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757014388 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757014388 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757014388 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757014388 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757014388 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757014388 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757014388 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757014388 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757014388 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757014388 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757014388 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757014388 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757014388 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757014388 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757014388 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757014388 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757014388 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757014388 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757014388 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757014388 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757014388 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757014388 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757014388 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757014388 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757014388 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757014388 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757014388 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757014388 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757014388 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757014388 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757014388 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757014388 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757014388 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757014388 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757014388 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757014388 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757014388 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757014388 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757014388 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757014388 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757014388 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757014388 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757014388 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757014388 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757014388 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757014388 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757014388 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757014388 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757014388 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757014388 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757014388 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757014388 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757014388 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757014388 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757014388 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757014388 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 757014388 ≤ n) (h2 : n < 757194244) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
