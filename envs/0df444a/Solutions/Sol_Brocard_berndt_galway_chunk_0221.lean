-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0221
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T18:33:06.742512+00:00
-- url     : https://prove2.me/submissions/e6047fa2-2aa2-43f8-b290-e7d553f862f8

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 39568350 ≤ n < 39748206 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 39569600 1250 39568350 39568357
    0x2030f1e0d08040803071202031e0705120402090a1e150b070201051b070506131508130803090a020a0e0f06060307090b16170a030b1905040902010e0301110a080f010803 74
    0x80c1600c8004000544042d100c7d00340b1890384926007000759282d003400504000004150390866102000d854000b602aa100d2015600080c048092301d442d20744654003480b804450103450444400d4880070b0729503403802d17004080150f1164021001504c03408982d030301505d038521904404010241048800c0150303a202040c0d581c490680240c58226004900006280c041c955000e079070000c00100f5051031040305010448100c171003206840d20f101d141c4140459401008942c60a402c0100e0820807000c41c19540107594002240e0003102c81c0410207400103110072040368803005505400e042000a00c112410328142c001106541003803c3d4180003e000d42898480d0180c0f5a2030345001c03556500c1001d190030390520361900048400b507038005c0d414002203140d102d034101401107800c1c16214181d40c10030040c11941c1e001c42d10941401c29090000b04000303010703842001ea04100810324607100300e990a11508403a4045600c20507518010150050005080100701d100085a081c00403c100700001c000c5 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 39570850 1250 39569600 39569603
    0xe01050604031a09012703020c0603041208090a020409060e0d020607050d0b06120702030901090807030f1101050c1209010f090302100c080708040b25151802030f1e0d0804 75
    0x942142e42e071042201e0040415201851490b042c0304019049007807206c101d04441c0d80a5829a4000d084203014082e4900c03054500901c000000300c07044102901c515041130300300f0100c40980349100101c1e0002810b035504010b06454aa0340c1c2e00c21440300840c200001d03030040ca01130000e410039203001d141c060304502440303102583e042e440e040c0d107156075030b071b04d804441096000d1075007404580ae103204001c3d030320b4103d607000b503022415104002c5080c000c0041c1040840e0345c13080d10784808072881c1e0313aa80202445604014103012086c0811502c0103028040c403024271070070049a0385c96035809400101105601031401c0140407421300240003603210a03098150004c09814a40300744041c43c41c000b221031003643c501a1810300e02240218801032102c00500340544410500ca8155a400150620195484d0001070010002010111581e811500a541d4202c20b82c400344000c240f10345c02003420007078030382456030080d0418440b00308822108060001d80e10038140041c070504820400c00703480303401b01030300 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 39572100 1250 39570850 39570893
    0xc031a041104080307081902030c120d090503160201350601020c0307030c060801090c1d030708010f0207060e010903091e051809060f0610050706090203011103010e0105060403 77
    0x15040700800d0350004039401004400c0403259907219909206043d90806007140310f58013100400040a05d10000c01d0701c4550380818080c0c03d4090203009a0b08030b5502440117900c403141c560300d1001c04100c00f480034040402040c4ae10480c03050480c400100901740d009800b420100c41303ca064240d2450401c0403040030821200405e900351910310050b80307031060801082c1c1e818411000080100400c0d001d90400f2140603490f03480903030b40c0728000d21094507084207a100c001109400c1420381c1c1c2820910807451503c001e81640d00c01a11051200d00b51608180c1c031258280e0001a1181008030510500c195654840020081d0240565004056800a00c0b6414aa4070381c00e07050880b100590440e800106801440d48000b00a84505150309813022604101035010f00750015064050024005104403002030540009100d550f40507951500700c1c0d00d094800594410089006860912590303c0b03400c0c03481c00f02c603181e61403d494800018016007005000350000d001c1000001e540c207420108042c4050f1 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 39573350 1250 39572100 39572111
    0xa0c02090c0906030c04080114040f0308100503010204090c02060c04080703020d1502030f0411010e1c0c0b03090601030210020c010503071b020315150409050a02101106010609090c031a04 82
    0x415420700e60003160b0b40140d12042c000184820030b601440100101c0711030380020301000303503a014442c4642d081150302a0034008025001d00c0040e01c651300003079101c5440e10400080c01d03102c801090880c0c010350400380300700755109514240c054041107a030f54400c1d400d02100d8a0306c1d041c078451544803101c5200007402000000010400c00c83e221a00c50800c0502400464580c60544014000e801d001d85041d40c036502040d407059581c0d4414808070300450400307043d0307078503000ca0071000c1404500150b90940e03c410400c0b001081c0c03182180015405050100010901941140100025203034500501010340d48401da0a900c072f66007120903a0380c400b03d00d0038112110b41042c400f40c1c016000c00d800003503241c01a16546e03034030030740100310980c01343c8040004c001c88844070000f804201d80c82c0c54030280407175003c9044500107180c02c440203166a840c51510f452580010382032030386040c90a030401c10205080d80d006100b48400351042d500309101c0c0e850b0a01c10306541c0844c04044004106400303002d070b6140c1c2c = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 39574600 1250 39573350 39573361
    0x70e06100806150a0c110d020904021309050f01140601050c0706032d050f100503030d0203040602040e070203030108100204050f04150b0f0306030f011b080604180302010e070b0a0c0209 81
    0x803001c00c007881c0348407602c00707540f03400c0350030000c0078402103010417101d21b03980004e000c40074148080c180c0c2d646a406440a11a9180d0341c00300190030b01100795015100b41c03103004d02c1000a509004046400742603000100d003010380c081031040d074010000c20480c1005428031440f941410f000448604488060400081d91904a40c0b00103460131010315110b8407a0340282c50741c03414441c5912152080140d48030b92030741520b4210402c110030310300b07100e840d41c103034010300800b2080240381d03006682051042c107005181039070364074410811050803a03421000da017022004110300c500c1800005450206c04004515181c04d280000b25100c501c050928015544c4051580054546e41001005828141e60b11030300d0f20400c664504d49688121601406406455200b02c0d40c00d405000d00d45d801821144641900441d030361045580403030042c0500d9000307450300744080c500c500414080007501d000b80c4c00416104c0c2d0b80300310f20340351800643c0120b01030707801000507503203d0341c0c40000c000c0d066074112400b00351038964 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 39575850 1250 39574600 39574609
    0x30b1c0503040f0e07180605180a05040c02060114040504020904030c0606080708030406110c0d0f0c03150b030d020607050306040905010b032b0903030e040f0e0607080702070e06100806 81
    0x40e500305181e4495100740129241005504a52107490959500d8103d21281b00c00b54480028604c500000318206001011101c407500030000411480074024214055031100010151021200c0c00d40140e00b00100510949a420144c40c0028400f03503401d0186041c16804a8860407004101404010003843c41d17400700301803030b0450b000404940301180c6543d9142e40c2d01646030b0f03100d4030030000455140c1452042c8000040b0381429020343c000c1ca2030460f8900c0e40c0f1115644c0410100464002e1410309010000801801d003c6000c03111080300080c40c00540824141380c51440102c007030035940034a0411404590100850342c0c0403005071800301d080d150a1802c980501041d03c203585d0b041c014441d80c480b141700300000c00890721500506165030315032000001c0c0d840f030b01140000340010f6100201800c841c182a0071017480030102c5c00d00002c00e1242c065a40c0d0030154140d4101c00003031101e03001c0c05520365041004d140a000c03c44150400c604001000500c2494003680c000244001180003c50aa90307 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 39577100 1250 39575850 39575857
    0x804150b0102010b030604110f2b08070605070203030f011d07110a0501050f09010c05031b16050102070f120905090f090a0b0103050a0611030601020a060510050402070501150501030b1c0503 83
    0x68112806c5041914107046032080c2c01d0640360040000d80c1c0b0907009454910190b00d018202c0351004144149122400d0f240f0204800302501c00850401014000501c1071145521a00243d4082c6490381002a41c001d07207400107900101c03824400444020303825025155058220406040c55003032224003003040381c20070001d02000382455181008200807400100c0b40e075031240f00b40ba0004c20000004a2081c0c545000c10b0364000c3c000c082c01d2004c442030381c2443d40201031400c44030303400c0203684105a03591800e90303000300e000700d4500302010380020030040900c0c9011160051414800c0103541840d001c510344c01d10091094001c503c1120110f84003507030078489407140c1c98009004801541c0c5a0915503500d4490402c2220281d140060346003250010302d094900918059000d0907071903640d034407031002814014103540c03005019800300141e555254402080c02d81d100b8030012400d1480c0f64441402d00c1400d0b40b00394141402c0c14030690300c03030759260407058902c62028890038511980b801c10514501 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 39578350 1250 39577100 39577121
    0xe060d090c0f0609030b0f01061d01180603020703120b13020f040506040303050a0206010609030c0603091a0108010c080603120702120307060908040305010c090b0a050c0a050a0609120804150b010201 87
    0x500c100000c80c40d0f80e031003a00c0c1e005072801044500000d4440154080490009100d02c034001100900e1040004101c1c0d810f81e0300400051407d1001d56606888007c01d003910f13070f4041d501103540000c4940403d508802c816014040c0e81d5170400550080001042c1031600d08000810107641c0021008034410380c05040e40c001d00400382c00ea0752100d499240207006940b11103020b00251080d0360000544c984280e071000c0c00c0e2503100f81080d4005140050941c06040007090444825484808100601081d1001d090003400f011001080e0380c01b2040b13001c2d2940d80040c0040b8080d4110312072810079800403100311200325a054859129020802a14a00f1030040c40030050906040880070000e22030000301030000d817405040200050022201c00b0395400c5890700c0344800f019000d101c99510180901c01802d0103105100070384418002a56070300c6c2c1085140317141110555030f5450414103020350141007601913403040c1001651800d29841d032032b401c640050310215005480b8a0700a0059100390041000c00 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 39579600 1250 39578350 39578369
    0x803180a05070f05010801080102040b090d0203010b12030a0306080c030601030318090212010312080f0c16021201091214120a09020d05010b04050901110d050705130902090f010e060d090c 82
    0x1103032190790f590b580e802c8030b1003140e00003465100081001306041c400c0b142100e1010164528008c407400031311446440901051303a05550f41c140740c40907521444500360190703500102441d81c521151802604554050700814900c0c0c0c08221101d500d07440c0090700a043d00d070182041510010302ca110032840340340c0740d04004075a5001040a1202100810155042e20300c0fa4400d110040404102114060400c40310315a10480c00e901043d01d0301d0005c801001ca40410301d80d044206c0c2e6541c3c01107005003070001070200d001ea540e16142401c2c094202d11444440c6488d01c0c020320320030604148898107005124201c8882305041011a60361780d566442400e50b84e60180c00910400c4070750034050b0080054021440c0a1410080059441c103070620441c8203415540442c42c1c28204207a468200030f14000b4040c1d02407003010016651821501c00401000304142a00941d0b076040100520030700c0250b000c4211305000d03c90f21041140e507561401e85402d0010b065001400c2011424101100140c5501c24001c5 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 39580850 1250 39579600 39579613
    0x304030c06090819030503061e04020a0c020f040c090303050a1e02010e0d0807090e0612030c0303070e06070f120e040e07050a2306030a020909130302190803180a05 72
    0x1c59008060760044800e6202650354181c00c002c25410a41240e40f40100015010000100b403850302d40f03801c10b0820440080703961840301c40000309049922444e0601d000c10750081c102d0085151002a100710400c0c1903c00b48901c4641c8a0040c1018110740170040503c000400c0c1806403d210700d288040640001d00380c8100d5444410020b03000304280b004841d418000c843e1022940307401043c0385801a00f503a90b034001c00b0f51602c2450081c100000e044541c0c0041c000940c1021a14108060545656090042e44da241000d00c000341c000524010881e01840003400f41a000c0754180c43d44650b10380d000030f20b48180098902d0f04a03000300307004080b0b5500c103250240000003a0030019540f800d4400c282e5102401584441c80381142081c5201e6079003038250402409417550030301c080035541140041802500b0800014006003541a040381d11401017031110203008141a0b0400804800108500c141c0d804c840a540f60065941f000900602a28100c0c4000c19404001006560a416040400d43c0c00 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 39582100 1250 39580850 39580859
    0x1090209040c060f080c0d020a03060509010906150c02032d0f0102030901061a090f03161d0105010c0c031e0f0506090c190618030b0702010603060507020706080c03090304030c 77
    0x1c00b10102d010390800603c40c9220042e040780603003003a0380180715004580f0b09100901851802a500c4812500b00b01500e54000040c00d455000071a40646158440410080c2c1010201c0303455000c61014a4100102a090b80002d61404104214038035141c0c06c6c880030070f08507030103e5414078486501019092250801d2882c45803811340c061401030100317000030310403966500d403158100404820107a40c19013041020b1a401d2030031582c60000104043e00361031240c080d402642840307520a45c000e4580a055400701c00901c9a1001024050202400c4c0030700c60116980710004110341c2070000a1150f203680b182120030443d0004007a0b10250b007c4400a2854198070b0004c0d102c050542d105602481407119042e11454a48402099960390104815582c0d01d007a030211a0342642005010540808000200124186540d030903c24000c41d000485d001e4658034040044a030000c00711030864210803828004180d002d02ca20360000c20b20358400d45c5176204c04080303c1c258401c1380e0006010940c20000040c = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 39583350 1250 39582100 39582113
    0xc06090c030601050f060f0703030b12010c03110a0c02220e030408010615020d030f02040513051006091214030904050106090e0c0f0a0c0507030206030108010f050108010207051507020109020904 85
    0x84440300580036100030382d0380c1e802404481600b41d0312690713101c0000d1020900c1d841c0c40c40090880d26000c0d15002c102d411a1001041407854108000711569440d010015007550b094040c00000a00c00b044061802581c040020032240020000074030841d108603039110760310140d1b4600c5074040b0000780d04000011510542e00c0ea86ea000e44aa803a4950911500284180c111420301400c22901d401030884920188030440040c210704100416a40d428040400c0350307201c401404d01540e049250000b02c60501c03254100281074542e019104000c8a098184245810b0345586241c0b503502154000ca4158001c003140d0960041c2281250440e103081e0000500c0366000142c401251000295500f071501d0b06080c003800c62146a003000d9202d8400c110050712075100701c012081d100c0c000d00550700c08546a50006071164001e9024424583d100e090000e002141c510801e8014840880210316141a9581d11f40c0c40c0d11038048403881300159840040c860302d00039000103e4075a401410710755146407a00d00760 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 39584600 1250 39583350 39583363
    0xf021c0509030c090c13080c01050304120c0821060405070504150302070602070f150b0f0d0809030d0809010608070807030f1e060903030c0807082802040b09031203010b1e0c0609 78
    0xe211b1403c00e003400199210000c40c5000c14148107a5480e89117030388a854140c808000c2c0340811003000803000b00711002c02d135110080d200b40b2612007655a00543c00400391314003100c015104501c6545010f09108100303411204440440309001240c070101c0c441340700203034002c0c0035032100509468000a00c6008201071186c5132043c48e07100b440840800c800074054041143e0043d051103070022905200524a80341c01aa400b09041c41540344528000c05200483e0420600324500d03404681d4000a00c26101800e01410b130281080c50001c2003007a2810f03179280e503102154440a0030000d800c0d8180e4050041180385044084050306007032072903030503901c1c0142c010401c001c0300360002440c0c0710340520321a12410300c2c40e0088130349075100210364840ca10b0010004141c441a0b100211010440481c9034841d80041c200078840880030544900b0024141810104c101c2807804100e42c0401c01406020301070000e40b009502100350034070807903640c03810b0400c552046030b03a003001c14864503003007000448002951 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 39585850 1250 39584600 39584617
    0x7170f060a0f1112010905042901080105011401020a110415030302030703030c050408060402220c02010b0901080a12080a0204170a030e060a0f03090218090a030f021c0509030c090c 79
    0x8000c20140720703c5903c40b5020b0390303d8480d002c40000c40100510706941d0011f94101c5e004a0345180c0600038400d000d89c08140c01c2040751b04440c965401003110210a215103401000130029240c104040307500002e4480010b031744010081c0d1908141442c0d540c4407540310000da4100d41c034000410301e4603403c0280d502d405c0444110000b9041001c107900803441502135404a400701401800305480300d9080280381c0c003c1102c2ca00030034002ba041c5691381d0304903004141003203030a5000007503c10180c005001c0e10307a8058100710442e501000180001031040c07a2940140c82a62030803151f13503240e100c2c030758000e407140b036022030540034200d49240c01c108800300c3c001c00342510944802460b031040000707201c0c141c01040100c001007025482039481e481d000c2d400400b51140b004103150030708164044400e1106105680b600010b6000d1444c0740300f09074001641c00c00391445800248814003200740701c0c0700c02140907500c820411401103000b0306292400c0240785400740c0028000383d00344c580300c0074009094000a06 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 39587100 1250 39585850 39585881
    0x30c150207060905100311041223031603050705060103080a080a0b0109120206070606060503040308090304050a03030c0212010507030c030609050408030117030c060a140f070207170f060a 82
    0x8414406400011070100326592500d8a1101070300c3e00c010003001c2001c49000c0740a05440f991142c0c40c0e2003c4400900240050002a12038000c41c1d08110700008540c020f1006000140390900c0d80f940e600006072052a01682caa200c1c40701d456140444160007803281c018514458000007001300102032000d04490340440c4c2c0c2e00c01a5a0321004140150340d521112a40883d4541d142441040c100458002106002800091414105540e8107017240d099030710000010314040103101c101340d4880038594000041c1401035051a051a0004044041070301c001403d20440030781d880115110230450142280c4000001c00061501307040c040c1c0502401c3c150b100c0000d180550101d044041c51051500071a041900720342980e0030070303c0501481c00c80500b508007904c420301081109490802c24103200342101013001c196190450561607031947e0151034204144461020080502d50010342482196505011b45030103500541546040145008103600f45015080c2044010307411a045a001e0041c00c070b4 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 39588350 1250 39587100 39587129
    0x50403060513030c03030b031207110108010605120a0b040f0e07080601090603030e04090203010e03030114090f010509160e030706050c12090312071502041205070806071407060b030601030c 83
    0x750740803010102c0744000e01041a00c00c2c1000071034440c0d0b002e80c12804015080718441101c081c001c0702c1c99088403a0868010487c0400300f9080c0d6840b40700c2c1401400386061003070030140724001000f40040018445007c40e0361300e406c0e040700c0d5602d035045011900b0040200b00401c1c400c4031080e9495045074042c040031440384000000341e842144c881e40301240d416a64070903145502c0c030300704030203000b40010581e415900c2e43d60f001d40041c000e00c01980201801c0c0c400740f41810200302804541e0300020a19100f44003650300422041d100c050001e94094045144402c60710210380065840d903180031100c40e0940720b1803001140c0705030040018018440080c0403140e40004202c100006449084c604640540091010703120140aa02c003400e0460b00c540d820213002c00c411208207049800642c003007410409200103200034001c041c086240600b41080c00b038070051801070400390030050ba2540b41d09040e00300103440400e2020652040746070100050a56900d5652802c003c140321100307000d00e001c00440701 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 39589600 1250 39588350 39588361
    0x2090a0b010906140a0c0c050a060909050105031504021012020d061409060d12091d04020f0a05030607050d020d022a070303090504020d1503051609050c0304021009090504030504030605 81
    0x29841241070f41904601c4030301c5c2c9001c0c050122a2035400d4031003141d140651240204460b03685400d40d00243c20a0340d034695440f450590403800399581a8025402608480d1000c0c00c4541c01c01200e0340c1c4903405407107458152100801c219240101d045000c88440d101040184c5040c2c0c1ca030308880b04a480364841000000d58010402005400076103440d5402a100303101000011040c00f140c40120b14141412400b076a551890342024018204c00303400080d80303050810046151900c49482002c88c07e4908041403810280469564200070300a1014040040b9200c1e8826030f190301202c1070725500e5079056446071036044040e04450000c50b4003039880891640404a61607000038684220390f016135440c65007904d4402404000c7d032210012039840354071540d41e050105a0404006c005500c20001008003075a00d40b83c0c064486210340100301614100024440903198001c1074030341050b0125112400b404039111f0a4450700010707480b04043c0d5051600300b10905801038083c0040b07a024407014071056444 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 39590850 1250 39589600 39589607
    0x303050306012606011d060409090807121e03090c2904030b04030e030316030c0204020c0a0507090f0b030307060b180c030f0105100516030306051804120302090a030312020702090a0b010906 83
    0x32406c07080d0071040600040002c3c40c110b400c141c020380c0c05141118a0030b00c20752607411191140c1c20300e10001c250340440346101d8602d450204580c0205910701001041704554841c92400102d1164070a12030b0340740d480b0202c85c41500004201e008151300029034a030394078074040b090980c1c119800da01040608404805504010040325034019408100d0550307200c41360703001c0c0d40c4102c25100c140d0b001542031100304012101080b0000080d40a04002d1000d0340c90310240c84144ca40704a1904000780c1000707540411524008190360340164800c2c808504941c5400104203a41c0030700c0d2000a40200070400c0c0034101074114011409400d0080c8105c6180c3e0300c0340284211400110b220000186040203400d00c94914030700c0740301c2e2041c428507001ca41c01d0380c4d07040082c4d20705115203004a84c00000100784010402e0f80e00c55110b01103003c0c18150304290b8440000b0341c520002e8480642407000c4500403460002e00d60f4110707160a9801000e4800d60301740742c0c0f05500103050764541d890108640b00b0703000c90403501 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 39592100 1250 39590850 39590897
    0xe0a1508060306011a071205071202010f0b12120c01091b08010b03010b06030414070b0c0f0606090105030613061e020414240f0c030a020606030d0905010207030305030601260601 78
    0x1205d07403000e140500a6841108000040c154070040180c2070240d4000908000910500031155070b0001c104011b01e0741040703040360b003103010003807190301d0a808503006141c0210344010742c5142d01880c0c1d500d034402c440c880c601400410724020940d50003080100e400c00508a103030411b50b1400340c001c10140227208141400c1b542d010010310b51280043c800240003c4080031006c1090f000102036621140d030300d82c00e41d091a00681224400703034224403540c1100da90700704100b40e4440d00c2140d10044a500d0305c4003103074941a0142040702c840303854804020900040d500980101c07c01c2d10440355100801d0b528460081d001401076a5840200e04514032140c94220946000074249580c2c40701160790381850b00300c5607841403c100820341c105004c1001c0481d02803015080d540d000e41c014141510340030341050300703148403080800d050102d030b8a800d11581e40d00280741070a80c1e900d800c040e5900d80724000140c9540b56690790500c048480110084400c40800100c540640400e0301c9070300d122038040c5500000030301d = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 39593350 1250 39592100 39592139
    0x10b0c070e07030207060504031d0405011508060604030c060206010515090307060e0301180606030b010509011401032c0f01060f080a0f020121020304030e090403050a0e0a150806030601 81
    0x601588060081552212041d600305800381001440c26000b652802c064860440301540824011500b103800403c0c0f0031600082108121000c00c030940c180f041c5650441203000c0044204015040014415100c250482c0c1c00385403c030b0802061143e85070400de5890b40b09019440c06601e00d1074820a201082409503504864006c0c05460b070b1600b0100d04a075811340d016a00c1e540b564070342c140052412419078510010358001e0708085852030940c10000203010069200317074015100140100b06c030200c170300ca010310544030910700440c408118a040c11103444600981d020803019248500502181c00941b075810320303910b58028041c1d00d54400c185211401a4890080543c0080794001d0008030701800004c1410b1050402c0c0807000f0984c58101c2808010180c9404a607038000301f84010f00da00940554140c20040300c200b6000d01c0d040c0c0e00100303c0c0c01181c0a21040c4440c441c0e042555a40c0c4121500c080c08192100454151079101c0041c2122400c2d030b0f1030b40c060300410b0000b01d8044240b404d14441d94 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 39594600 1250 39593350 39593353
    0xc0503040f02122805070b04060c0f061b030213050103050105360408040608010b07080d0207111c0201080903030f010303110f1509150108062a0a02070e010b0c 70
    0x7000e1540a105200812004a010602604000c140c503800d40c00302e004111000310010865402d01442c0240c0b4100c002d4001d01d034a21000c0c881080955031106d10743c0072140d845403071600605d03c00d24000002c1c1501c085d000d045401c081c01240c40255045d8041c3c40c0b070a00c41510380b8100c50341d0b480150211a0300380503890b085107004103044490101031105a40e03265450150300d44046031101d101441900c280c0c0c00f103030100303000501001016440b806490245c075401c0c51461406440d0b6a03403411521680403c40d00254000c14503506120340340c0d01c1c0340c2502500cd000e640b5000810b42d2003000700116041c00f24041280d88021034000300001081d28426525441c0e6980c0036421520141c0700200c000c0b04220a40c400c0901d18820342e0000e0100d5800c00f95070000711035070340c1800a101e0742468171034400e01c66036500c2e40c001008586000a10141c01007002c4044617095098201004034454501a00b105507200002d44210100d50000d48542140e0902c0c034072080036600c410541c1500d101d0400c01c0841c0d0b = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 39595850 1250 39594600 39594623
    0x8150405010f05040e07030204090c05030f060f0a0902010c0609030302031801140703020705120d0204060e04090314030604020f041403070e0405060106030c0c061508060601030c02030d0b0a0302030a050c040c050304 94
    0x460805900403e04402043c00706c3e20626665400242550802d040c00c075000d0a17941c0c41007140303003010043ca105401e03031040500b100c0d160840b0b1a510001c0002c1181049a0f2505514415640519031004600341c100b081400000c40d1418058041c2d4800d6441840c5925a14995000d01c0010712078640b5452892a40002c250cd4400d0704801a40040d5416180d9000f0070a4040c4a4440f16008141c03c0b04114005600c4a24100029120700083c0740c0c80307030046051903c0c0c42c0000f90b010a950021261904559484e9280d200110b00240115a2801c0c003107400024080b40d1756044a800508070001101211240c5844400c10490f44409541c014602e50015005108940c0250407481104000307141030b00c0744003a55194002510a4414142200c1803903400601041300c0601549034003100070f09007805000c0c240d0000079601d00c1180300411990744c2d200c800404590720340d03049000868004007101d00074091400d0041d11280780d03c400c103201d1071811102a0606018205481c030039a04011502c4a = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 39597100 1250 39595850 39595859
    0x50916090b210f030316030b0f030307031d0a06031d030a1202090102031c050603331b0a0807030506090c04060c021f02070e130b010b0f0906040608150405010f 70
    0x1d4010302c0e0502c01c10600440b004900340c44003c0015510a101d01c0c1c0200c0030328484040040c003100d072040700c070754000c1d0402402c9142d180c80000c211003400c0c0e458039003010700480344840a4005d80e800c800c43c1c0d07445807945000183c5160300d81c010b5050f600300c00540b54900701a2020b02d82c1c0e2803140c0d40512000c111500030904400803640e001e42888001801601d1809482025103448814040e40c0b29040035542d106005060034108070b1365030424028051703141c00b40d011003824132840f05403000c40120a003000b40040c002e02c41810911500311500c07803001e13848101c1458040d100220490320080040d01d0040020a1880c0ca92031440c041c429104100d860581480b104850181040300c080e40c12184201d2400d10b0404044400300c44484a5030141807010700340144c0c2c4103680f00c068031110100c81c0b00703240940450525a074544c11a4803a41a03103513100c90340142106540a118010750788140301040000e04540c02c40c6110348954260880e18120300000010002110b00c203009110380075449250070700 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 39598350 1250 39597100 39597139
    0x706091e05120a152f090406090204080105161e030b09040501020304120305060d020402030703180615120209060904170a05090406051f051c06080705040b01020f061303090801050916090b 82
    0x983c01251145911b141c1008a80881c06845550340f1040c44154005000c10903030301c080c0f2a003500401d69a180d80c3d0302d54142c080081c014261040100500e2003d40500b0a140c1d003e54880c40b04800c025220852928090402c14000d402c00c03501034480c40e0810446040c141d1103449414400c1c0d80c001e104426121894080c0002900010492024980e907400758401603482c0031801c01031588107070f201040703001401181550100d4243d0040c800761543c06203000c010b9403926406940b064003510301503030950740d504202001c4090300f101700c40354803000030303138040d50b558488000c055590b416a4107000d4240c0d240240194031381401c0d03c2d040c07600c1e03840c2c0b1a0031070117124000400614105080c1600074807424800c04080318402d5100034400e9100d20300401041c1040c3c043c2070212030090001c1c2030094001c045550b214000149106080030800382c0e60700805006291100141c25410000c02c039900d410024255a0020407400789110070440200083c001c210340120085144c0243c1000070900c0302d01441e0 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 39599600 1250 39598350 39598421
    0x50106090312032003040609050111040302060403060b0114120609010501050a021005060a090608010f1104050319060f020301080a0201080604020f0d050a02040306051f05030706091e05120a15 84
    0x2c03111104400c080c0c4c1c111000001a502560240b60300140310801480c2550840c2d00030900c800b41018180420400360b0b40300c1d81918120382e08200042403079818400103c502420a26100d2218040459901c2400d5000c400c5144551800d072070f1200547d80300c1c001502c580c002c2480d664016440503090100814aa80029030455800390412603031903103c070040350036540790b5002071b03807a83e40d18004e280b0088614081d070250f040c088000b01c1c1ca0309080c07002181d1a0010b100da100c0d440440240e2403010000e459101030306242280c3c1c421500e03540c641e1000303a19807888000990003d118100810558507091003100c1d41000ca407011140f4010302540518041c1030000c100c401130310390074440003011860301d001d4603115080c3c440102298120620500342a0310f1107400c03c074000c1d801000c0900905400c001d810054031440751901100040e0303261240070740b485030b81049410030400c00c200c25041c240054003074046c13449917000d0003905021600349411194522200f0211b001310304904020800100c801b03 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 39600850 1250 39599600 39599621
    0x20c031204060e0a0b071b02030d12060b070809090403050d050c03061e030705010c030207181401090c050307050702121b03010c050909040b0405030f1804060506090102121b011a010305010609031203 87
    0x4207c04041c80340c0000b402c080d0a250403d020600d80383ca01c450b149028402c490103002c1640240c0d0600364a83c07184a180e0061503c02c1c0c2c090554080407409050040c0143c444402a0301810f000c46d01e060808504a82c0058030064020f56042285404442d0340c40002a407c52003c3c0c020102c05180600440e40e040000c1c20550550090030000700381d00c0341e011405000b50811440c041901d4000c0c00308440e00c4101603104417051f1703190a90910750b441e480411207800892514000c1d4403042c0302d0002840303000366407001400e20b108100107115001d00462a007216403100f20700802c2100b03540c40c4251081d20a49200c183d001c25082e000070000303442011a0303034100b03000e0300c110b1b400d24604003400d124503409890064400071070101240d40f14074240c003454018280590703655052100d4040080d50b2a100345644000d01c0402141404e042c0520003007020510000c1d00c020300c00024100c56205d400081404507500203814a8004070b1118010403161085170340c000340d1060040318a240840c000d180c8074a1 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 39602100 1250 39600850 39600887
    0x40b010302120a0203100b030106140f16060605042f030a0b09091b0103110910030b04020a03020702040e07030506010b0a030b090403080915070c030e04020c031204060e0a0b07 77
    0x1912009a0840b0400e0302c100100400160749082c070241502c0400002d07031008100102c10070042c41900d505c0b4030825000000c1c1c04206440e03902454002c40e090051003030300c7c1e00800c0b60505850078008613410800c201e803810b8408000c01c24918902c1d91075484d039132a44000d0b001e1022038158000f0600e100560b032021607500c000404134a484000703885003100b81d0746103245034401c030101400c80606003a030001c4020242403c00001c100c20a003c4e4180c001c000c04284140c85502c190710415010f07801408a045008000710354428809002800a4100c0b5100360f00071031400c0503144442e0400926002521742043c0103107121ba19017801911680e109030784030703020142c0711006080c0540358075501c140141d2081e1141c418a140005005141a07404e61004180918003018401040c1d0400a030300a11509031811800e02801c40b00414040d201c1d40d8410820fa21001910501314024206081d02452141c9410300c545007005c85200d0390b070f814442d0060b0050b8010004256032900820700781d4140700300c607107 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 39603350 1250 39602100 39602107
    0x501060909050d0e06070f020906010e030601080f0106090204031109100f09020703020d020120070218070302090315010509010e150a0e07020d09080a0311100903030b120d0e040b010302 81
    0x80100c203032034a07007008540e5940054a1a254160400e20722080820306071165400e04101ea150240184d100007400b074065210800414a2a4401c0740c07603640c003141c040d044801c95650390300595940c1e4000441c1c079007507501e807020110b0b1441d650b008440817290000c4214070ba01105d0307010091211000340240151340074003100040d20700c007031078003190060001100060310364165040c043d0070b050290350100116407402181e028112444a00399040c40c0224400648800b202c4c80414030044145401d0601d9908101c20802c0280d031580042c0b600f204142d055a490992000d40760f0305040c002e00409078807121050041c00700c0c0103643c1ca001d40c080400d208000d80100c1220220b5038506507138001c280c80c0c080081c1000f00180d010812039280041d9841d000910701e203806191900c40451010041c10072400480c0030914450810032502d49540c003100800194240d403802070010a8a801c2941c00707404d14074212004424041130015410025880e141c0c4030b02c1a0108100041190400326410301d035003070 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 39604600 1250 39603350 39603359
    0x40807030503030402010e04021905161505070e010c03080a110712020601090b031209130207140c0102010609020a0206150402160309030507090506030307030320160b150109050d050106 81
    0x20000000158080d03005035030ba9042500004203950800c0b51800e004600400c40851a1005081c841ca0048200d1070201d49541510001d6088400c0f040d00c0501140341c1c240d910502e0815603445180510f441d84c1b14080c11802e283e0064030090084c0902030b0100e4107480004460000c0e5802c0028100c40030030601d80341c41000c1c0c1c0ea0005501054680c00c0c0181d000e00010300135101d0310f02c5080c4060b44118000c00c01400d900d05002243c5c86000c02d0207008844009440600d0209601500c90055112550094001c64024496a10f5a50b2604d807801503080100028011003d44215288a011703a806841c256481d08070349414100c070812000c0d0040d5003040800301400040043d01851441f81c0d441d80c9a5621b1401e00c40d10740300854100080301ca18060a00c11166000000c5904141d454200822078070b0b0000c161080c1100c18000c00031581d8000104600c1c0c80501c089020a00d610a14840700d1503142c0008a56540c11010322590100e560100140031601e050035440f100e5600c500c00210b045903c5 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 39605850 1250 39604600 39604603
    0x50d032403060203061201060810022d070501180b0f060a0306050702070f080601060206070c0c081509010c0306030213110f0406021e010908042303060408030106031a0303030403030c050408 83
    0x90381c0c400c0d500c2c2035010003800082d2501803d1407146404040c02400450304248c9240d031154500a004003049a00148606011084042c1c42162100c40c040c190340c482c0300c001c6041101c1d4030800d400c40b9107500c0c2200c94140441d11400e0b461000c0d4201412008030355600081d611891406840c0b00e50118100798000009906405481d200f007260354080d0596a24003807101d4501c4049401681c03072500030300c00602030281d0002e401076000c0074130300e007903000c0d01c2c0c80b41001080e03070302c060b0000b00503405800030780d201c0000034191850090703441000800c855005200308400701e85442c040254800340079449080c1c0d4900c3d039005101100f0740250444c0c5400c403624a4403109502c00d42c80702002d60410344041c521481090150301085606030002d1009044a640703007080ca01c51402007420810a203095100600f80d2690040c0c800903000d411a02a070900d8205040759030000d20031301000a08084c1540070480100d481c83c3c0908401500460964a032980e094020708800f00039802003100034040042e28000 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 39607100 1250 39605850 39605921
    0x703050c0115060f0203180105030606040b0304050a02011b030e01120209040603110102120a12110403050109110321070609020d0b011512091a090c0402040b04090b01020109050d03 79
    0x502c4514011090302d04180030702000342008480043d50400d001b041d80451250f01d11614a0000b468029900d0f61641e00051440c011500403035540301001c0100010040000b0f00006902c0c000d0b20b555100d80041c09504160550340d0f60020009810030b440409a540079a80d000c40000041c500507040030f804901007802c0f40c40c0303540152403001d044140d850780c658041c00342c1d9060840d101030345841c00d818101c0180c200100c04807480c001c030381c0e5080d40d142e040241c142540c000d160f00000910407404d10741460324580c00312122161083c040e1004001700d00c050740c0c0d600c0a140c94098015403c1c42602c0e1613040091061700c801781e030410125441140007a50300303114035018100703002c610310041d85081070007030a6502005a80c2050b91901c0071200104003c80c1001c41560407212004d0320710381c0e480b99640c1c100b50912005076007003400403d0124040310318002a200703581c09100c1c00c1083e089403038012400c0c0e9050314409800c0390448002c18220a2213a0401415504071ba601d2286002071819003441c50030 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 39608350 1250 39607100 39607121
    0x3110f0703020f09010510050304020414010b070c060305090c040207020406080304180605031f2d0204060e0d02150703021504080a030b12070605091f02070303080703020c0a080703050c01 82
    0x40003100184114906680c45602c04078064900745581c2d0b04007004111941048101d08092090100000d400c41d601d941204421042d03205401c080c3d940d5036250101c0b40e42009904031141270615402040030340c805d1007110b100b03840c12001050034081d1081400000e50284606a030800c1d1034850125071160100002c1c8001c10841500d0885c07625980e000e00200d44103500f00314800d40051080a1400c0c002d040050030b55118280009180107000380914088078040d0071a080c1c0700c1c3c00b20407000f545806503000e407086405e0354481980000c15070302080482500301800039072012000c030f41508101d079990301600415200c5e00440307905010140c0c440d500b802c0304481c212a80d8a00240d1221155858000c1d4105504140c42c03510318021010121a01c61000340204001c01c14041003c0c0c0d210350340c0d01d00108400100c000841e40c00804400c00039205c246070b0200303401052125001c5040c1d5071183c0300311604030100c24082c00c24031005982d40809540100019004c02000f80020203426070f083c801c04000c407 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 39609600 1250 39608350 39608353
    0x20f04080a0b0112050303040b091005010b1903060b1803030705010212060418110f01020c180702010c091a0702040906020d0e0706020f030304060506010908070303020609011b020c01030903110f 85
    0x120715520b400000e01038143c219005959503c000180094000001c0d00d4003e60301c03822070070485e5500740c0b179a45032088100d0720744403007801d00c0000100541400000c008011620482d9080e2426050050301035404512411001040400400c907650b0b076085100741c40c0e50401400d03030389403404648905007a47c000c4255400548046402c1c000185098402e0045441c01c022068a41c43d01c0c07030b201c50f001c104292180c18041d0415000a0601342e200f0321030700009040c01001240e00d01c980519200a03090220b43c2070002d5031a20380d00c142c07445e0003042500111340401c8100e2540210308101f00d00d10ba00006400c980060f04d0b100b078100010000e001411310f00311451030000b001264080140c1c90509603912a800399000313a2101e001002000c0304032544079401c0500400d09880340303c0101c489500c1540a20980e00510001100305030380030030702074000c1e00c458009003c40d8000009050210152070f1840c4050381c49440c1c0f14109501941090840314080d003000204104500001410b01c03c01d000c441015 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 39610850 1250 39609600 39609613
    0x3090109050f07081b1c081e0d060f12030302070305040911130e07090e090a021f020c0303030606040608060102120d090b0c03041101270e01030203060a090507090f020f0408 76
    0x80c02d804c01010320500c05c4981d00d884c03c80070724400300da044c5881c0c061840c400840c1000c84400d1041c040211200ca549110604100e0b507c000184070040e04041c2c40401083d050030790001c5c0f80012848501d085c2e072141d4a250410300e0703240d50180c1c000c3d07020300700c110184001031000089411143c07150b0100a03550400440d59074000030700d50022480c194024060a4003220705020358564044000410b0301ca1011210700b0948480100504e08858100d0081d40300881031007441380c0150040c52104001150303000c50b55008940f808060710f1340811141c1d29003140040c4003c2088510680106070054018019503041080b1000d15a40c294483d0b405030311066100c02c410380412a2060340e071980400302d030a500f810741c00c16644410008501801d09030400c02440f142174287c0c0c014001050310081070310107002d400c80d9500d0802000b030100b403005038864000e150000301400344074001d0100c103590240103484181d081041c1d6030000c10000700c581030700e25402e1003404c40c010030f40c200401c041c1a03030a00403c070 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 39612100 1250 39610850 39610859
    0x1e0804051c0905040908040305070303170109020901080606030402010e03100c17010503070312140c06010e06040212010312110111040509060102120706020307210b040c020f0a0803090109050f07 85
    0x548070510a1459201215088a0006561218406003560070866000c12000914201000c081c051600068145e010f20310340002056003002c003404190f82c031004608626070782c4100130030403405200700704e90200e181c02c40040c2c00d41c40c00800039540103105043c052080c04245010a140a00b052500000c45a50308a001070b40b5400500741002c0608044140e081581041d005c40e40329121484000d01c685807920042001c1c0780101c40c84100081503da040d42c41c0d481e4a511a50b0f06c800c20b10554101005200101308541045c0c001c032909442d02a0031102c80d640782d992919002a41c000783c04040140205001c41c1202c030a000b058402d03160200500d8840d030500e000c2261658018100c5815944240e546070ba1505484054801030780d00700c440182c0b00d580d40c4130241c44c100410328080c02c0d00c04090341c04014260703050b0b02c06001100161810001269803017030590707850f000c1101c0000c0070761100300341c0000a44130600941c0e000008400110b20317070070140d40341482c201c5a40105941500180414030 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 39613350 1250 39612100 39612103
    0x1030606080f070302070816030c061d030906070c0e07020102040311040c1d03030d090605040209060307030b040308130206070305030a06050901120609050a060c020f12030c040506090d0206030c0913060b0405060a1e080405 97
    0x3000c04100cd288200d80040349800f42e40ca12800b2070a0303005d07000100d01c840500c103005131100c00901c0480c2000e81d0754a0a0103009000350b200340411503203507404000401d06801c0c5485541480704c0140c98413461030326050340030708804400f01602a81071008108031908000107001c1c0e078010602c9240c0c045540d040c64070400c03050100041c00365009621112042000c038518940301c030341164260510b080b80703448880c03403c0440d0241200203900320304002540000c05921030019846050404020011940c81d8010001d0321a0284591a480b0044201d800003250b09907001c00340452190003103c040c880035a0f10b400c02d07140800350b040c0c05a0040350003038204640c1405460b0b2900015050b8600d5842c2594046070903005034020503029440c003141038241c03521208210f1a4041d00100050703141c0c81c10a613800b110740c0c8103c1039580128a80d1107000d00900580c0190826104181e00c110b080070f0404040c4035494020811030310803c540c110b214100115801c220041c010103903612447d840c5018207005 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 39614600 1250 39613350 39613361
    0x9050a12170604051b0d0e0601030308040302060a1a01050904090b0408070309060c120c02190308090f031501050d0f08070503090103050f06090103021203041a0901030606080f070302070816030c06 86
    0x5078091400c14040044003160000608900000c0b0317804291221080ba451800804d8901000182c0b40300d1702c000801459008170545221300d03c02da0031207520340d941d03003c01816100e82d82d00881516901d10070800340e56004001030800d5240c064000500e00a254440303200c826000d0300d0507145503a002480c4414187d100f8100009084039051400792440c66658a074100100324a0300c44c200400000e44c5821903a400484044508071044140010f548030b01b0010f02952005000c1c0d0b1145940555024040c240800c1c0c0303a80741440b101841f0641da103845c0134405003060901c4215004404040c1217800103030341802501440703000d0700c0150f40300d548900000d0304803036001c1d000c0403920f6100c0c4100070460783c5885480d13054941c19604030304220300d04a04107203103015035000044201c80c0e003a040000325521001504000100740d80c148912582d07004283c2e800d0782e00380c6401c06801040d0f03002545d8140a900280540b1b071060080d00d18020440d01d02e000c48828540c800c90015505541400c00c0c80400d0245 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 39615850 1250 39614600 39614611
    0x90b01090b1201090903031b03050703060501090303051207050c0304060c050601090e0a1713030f02100507080d110d0f020715110403020405100e040507090f060b03070309050a1217 79
    0x1d03403410003001d41c00c00c220401482400000ea8542110f00708051180e0043e500c110a445982146c1040c00d4101901410b030464410b40041e2408000103070641c0319806035400c907038040d00c52500d4000e02c203d4030290100010300d4541840020003030584045400c100070f000070a170320340e110700000c00945400e5040c100d042c0d0100c08803d050410310280c003403000c01c075092010340c800510345d10120b960034003010b940580d1202c0040900440000130600c0401c070001d1048074400c6450841400480a0a83e22409419400740030f0070014440000e0881c00c96100c1e844107048400e060b418041980303481d0003618002c1c41154040c940125482c002c0210703040c0f04102d01421aa41441203640403881a0054000d5201c044d200300e4888010a485540900b40d140107401c0d0040184014a02401c01655507580c82c8200c0906504d03050b00b1030040c5080d84901801d031903001035643d2954640000450242602d05c90a0b00ca038098000c403e800a00d40781c42009620005449440040403040c07060b0b01504c000800 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 39617100 1250 39615850 39615869
    0xc060507021c1b06050a090302010509010908030105010810090204030c0e06030c031b01120507030b01020d0206090a080705010f0c020c0406050108011401030e03070b0405060604060611060f1f090b0109 88
    0x7000c0407194480010154084030701d01d4010306102802890152200003c1070141c0424900300a00c088807260390800d2a01d0750083d00280595140e15800d18201d4400c0c000c054004903041c401400340d580310b840f400350000701c4e103000f1703040481e22080798900301c0e400303984211040c00c2501810040500b005031820340c0700c00c1c11005001c0d51410040440d4540410f4194480e0340b08240c200c0040702d03070040765080d400c0190321104000504d01800054020319038034a100c7d0152044610324000180700160703d900c110411409440c402d02c20b662203841c0ca4002c140110f07071079500c42c03040e100300307180602c581394a01c1318980c010700710b5060140a2100702d0304250400360400a013440103004900d0001c031400d03103140007880c00044003110181c0b114154041ca202c000c103120b0040c0306000510400050769409840e08440030490540c1d107038000d0392200310051040b0541d0b0800740009014110700c042080e401028054592000d040407618528190b40d2a0080e00c0800c1d65404421000c1d40c3c06440d41c00502866903 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 39618350 1250 39617100 39617113
    0x40b0405150a0209270a0b060409020c010905010b0a0b0406030c0c0813050f030f0c06030403110304030b061903150c0201020c010e060103050616120e01020708030c090f0a1a030612030403030c06050702 88
    0x92101603005c000d10a181168070307500460501d4031501e0071a0020300985a0841d00c40c0300e41900d00340a004590300c103855660900007184106d00e021180001112821080b183c038140c0380003c140c1c064807940b06000c05104e07025045c1004241c4103001002e1082d505807214030207a09103820810780c0480520944d010707500210040008503c001400c0c100b2070003c0302e072942c881d40ca900d400c55030b964000b04050f849000114000042142c466062405079608840484140c6a00c6100441c11007841c40007070f15030b00003c07606c1510002590302c000c100e20600e10003d4a0b19960404803403cbd40c40c0030600180325031116004206000050000176000404d40a052100101e0b84000030040b00003412a01a804d5945111071031195096040f80c513043d13806880c40b6145d251541e5205100c0d040b82084a0140e007103401c140c445850805030200070388804e0440d50852a1a40d500d840030b5401c01000641c000154000401c182c080030009031000750311a50322104480303d1403425005231b980203800c2030103551125 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 39619600 1250 39618350 39618409
    0xa090b0915031b1201090302030c1207020901090207030315060c060b030d020c13020c060f180109170906090303030109050709060e01200c0405070203130b12040b0405150a0209 77
    0x310312001083c04442d0700c04590010100000c003001e4020f11540e03500c0d0300e05000b1030308140c0c000c00500802030903c4180e5400c11902000c0903e03901c03e1000096100403403100620043c40203070b024002143c000d14000501c1c985041003044003941a800c182d01107031150400344100010781c0118a00c00109070041c1819006104000e940d0300c951149030391140d140010840d10303500300ca07410785803804800d8048804505014140c03911481d01507a420101c504000942c059071441401012542580a4210f042160720340c034440a0542007480e00a9015038100200091541c0800144d40a460785440010b80d904001401a000110300d40c000ea0a10801c81042003d80c0c3e002a80c82c003103081c40c010000303284216010100e007010b52804142e03600c18034080500c4030030b0390f0000c040c0c80b02c8007104221020301c0e40c80b002c580e4464040c006881d180e05400f000003a00048901180301d4116108004807600c0d01d0780ca5254440940040719240440d541c0803c416102d0b241600703000a034907800d85075103409602034 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 39620850 1250 39619600 39619603
    0x615051e060f0702030a060213141210020307020705040504050c18010e0103030302071a0712060603020c12160807030e100f0203270d03020102180402031003030309020409020a090b091503 82
    0x3915034030182c0040103d482030664400f070292407039550f1b02c49800c6548000320650064002042d02600c0302c0c088415842103902e04115102f000340750a8000103100920070000c2ca9030107035000405100840c0200c10380012951030381d008140c01a44510083d150007504030061011604400c103640c600c00045000401c18500c4010480f81940d805103405a580d80c0c45040000840c4007592080700d2608060342003048684c0d012400d800c283d114000b0500000307a036654201c0c00d1340110502c08543c2d400030f6503206000c450100041c03440421142d20b503d00e8035550340300c1c4c0314103401804080d00403844580d1202603900e090b84000e1000fa201c0d0030a50080713120031000075502c4c0200000000c5000c000e9817204d0203800c030040001c5002000808a1001514620b0004d01039000014121001a810221185145041c0c001e8078032500704540e413402c00c9490758504401034909181c0c2070342c0060395a000500541c54403000b10019040440003c01ca03244c0c2d0405000015800a0005052000f40103a46030140d40 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 39622100 1250 39620850 39620857
    0x14060109210206070209090c13061511010608190303150b0307050d060e01080a03081509040308070306050402040603090201080912090f0102071d01050312030424090615051e06 77
    0x16a003004481d400051020400510440902940c0300f91030f02d040102d040c03000664541c05140030750381c200c030716118045604145d4486000350080d5455234a000c040061142000a607090b00003400801c134566210b42c018281801600d920b00d070707064409242001d140e010b014203e0100c20041e16030f80303400e150200000160101900e054204800080e41c0c0d4580007054105001619294410f5411565920095a601c40c4451400c8010038045400180962103040c0c2020165070068581c241c1c41d6211b030f804540b9020010b102c5804e00d48c0c1c030000480c1540b6180302400152400b900c00244040d450b00024006401c001c000055541c440d000307801c100c0e5540c5050301e245410644030000703000e241c2801031703090250316000b20549400b0140b513a00081c03111200181200c00c158156411440901c95820082c44101c50161201d0940742100c3c1750f01030301c2e501114100c000f40d840060540b8040d42c42c2400d6a80c1c3c1c0c00c400c2068207450358140503c0c0352051404881444504013600e0202d20200403483c40e00 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 39623350 1250 39622100 39622139
    0x8070f030c060302071103010c0f0306081c0503060111190209010806060a090c050c01050a020d0e0a05060c1303050f06070305010501050403020f040203040c05060c060411150711030f010f14060109 86
    0x5401017104000c0003c0404411000d5400030f00070310080702c0a4100800f0003001c4901000024241000020f0420010899026081d41a0502c14045d1002c81d810386841e8070182c5018100112949203400c86c150030b001d1141c20041f0b94454411607152030042010258040c2c000b141250846030070b01800e940d814445600701c4102e40404150b1041d0890b06850301e0049500007040b6500b898104031a40102c0e500408424a07490380c1081001c015000d900d90710301881310000d002d03620000105014101000c0034091209004108029650312941c44034101601548201d001341d0044041c0180f0a405002e2140901020310f806402c0c00d1075034000a0740b0300120510a40220350000104060040704c03100e00d40904000b41107165500000c0c11086d507a003004540c00d0328540d000301f030560b50328a000018070300022035103022681003c42549540d0382001c07000c406264907118121402074064030070b004003020b80401d179400140022150400015000009100c2410004820000e000396655254040c0071035 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 39624600 1250 39623350 39623357
    0x60705120f0601030e0102040e0603150705040608100513020d0b240f130803071403070f110a1e08010501050a0302030a03080a0f060f05030c040905060106030207020d060e010608070f030c06 83
    0x161120b00068005211850f8203180325400050003103401d060010046015410a078100c856090a0391001c001148090700c1040c0050010002041102c0c072440900d0707080390319034070023421643e80c1d00d0020f140125400c2c5110849900840c0c91004ca001c18450304603030440c182c032a542c0311a0741c05c0c0003003c0c0155444d1480c00860000c200e105140111000360b07070080840a6569000311b072240c0b0802d0f56500903020444031400c1019002c3c40289022060300c02a0f51b00c900104040e220950303c602c1581d00b0400140d4004203e85070000d90507101061a13902503088038024224682801c403400d00350b40051300194002c0e00c040004000684001483c1d41d1455054a042c550a40703901855401900a10256240247c242000450036564162001382240c604408a4000c01d2031034003400b00f581c3d000c540190803600050b004014450107a001081e406100814800048d0425a907490480e0644100c40d02d003a991850b061040e00d0003003081c100070303200080d242e0300140e2869130b582c82030030074038000d00041 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 39625850 1250 39624600 39624631
    0x5030405040218031501030506070e030a02010c03050c010c0e0307050405010317031f06020d0306082a0103060308040305070801141312051216120b0109030f020a05060c010e06070512 80
    0x3580e2440c0746001c0001d500900b55030540b0f032205e051190100080c082034a01c0e0043e02d01003034415005010901a0001c00780c05800d07000000e400548000e0082c030029000c0c45010000c0300b4040303501303200740d2070400c81c151101d1003001da520302498603000c004d805c01c8ac0514134200052011503000300344101524107081e10305980750740f00100b103540d10540707140350401c07280019004900d0a03000301c1c49083e52041c0303540c200600340e03562040c69130302c000c0c01c1041d04150f20300c0c41031401641110900341c2d42440d010305001ca1115500d80d00d02c9216449544142d40b00d070800784c02480145c000b806071008130303061002501d01c02d0405a8018000700240c560090903a03e01c8a030701800720b4010415690401d0107141c460340d892401400032158900c4120303500b00024229202955030f9a61032243c000ca099069468101d40303070444d6240d6034280551082641c1c400d00c82038001850759114002400c81300710300c000100d6a4136008641620303151000d440d91050080501c02c0b010848250b000042c1c0c0003140f187c91405 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 39627100 1250 39625850 39625867
    0xd0804020411041d0604050a050c030f0405010204080f01020d051f0b0918040605060108060a0b07080f0c03040605040f060c080f16080408071a0406081305030d0612110904050304050402 81
    0x42c441c42c0c4c0104100c48503618844002c02c070302c400701d920510040d5406d021542e9604103100807078070f084170001d000d00c50904c0030a03a0122070031052a400b034030910006243c81d49540c080d62419915500861090790005000740b1105102d01403980c2145004851156006121402e050344044038043d01c10207034008200028655202c0f800070450100090384a02c4904243c140840940401c48107540030400040100c0d0060420303280040490341d40000c9141403d1583d55070340503e9002030181c1d41403039002d015014450740d061005100500060b00d07200d60b690b146c0040d204158403281d21900901c214082d030780000c91030b0701080b190503e011611507079035843ca070003021004080000c03018020080104021940c40c40020b00702058807041a41d01d0110304240d00540014802c0d4002d100014082202140d504009a46d100c0001440344054a040141402d4113500b01c1307030b5640c40226442003400e5000148140c0401c2d0141843c4140c503003800d9460161901c50307503886144a010b0007280d0000c0c0450 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 39628350 1250 39627100 39627131
    0x7050a03080705010605040c030b040b1f050d150806010f0b04050a0b03090a1403130503030712080603070e0a022802060f060a03080403060624020a030e010504080118050f0d08040204 80
    0x2c6d000040c030070002403076640d200070300400185146a0146203000300c01106c0d440c01c05403000c608407504004c0c4a00401240003214207412500500441c01d0319441d180b400c5d94640040c4e80003400c0f294000307150661602800b8000780c51300703510440000e03c1c01c000c180002d858400142d40ce8504007810699203031259810390380b80050f104009000300700341a10441d9a00ca001c00104003e003100740e03044003265298005c2584911400340000d02541c03803054807581c840d0080b560941e01c14001001c0e20301c00c696039510b031080e0500840340711000316400150b03400c100204009440100d160504402e01d580342d160303400b035031340d0102800c5000509403075000103d5554881d000320000d17540c0046d265496582d43c5ca0188090115402003003080005104042d21980501101d441c03100e0059005140280054606807220120481ea2a040080070080030800c0d040c240640072800350380d02018046030300c041c10700c1800e26110a03400100c580000b0f03160b0b01c40b2503000041c40e801903011a00050308000b1400d141 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 39629600 1250 39628350 39628361
    0x613050303030a0b011107060e0f0f090703090308010b030f0f0c0c2a01080903070b1e01120203120301060f050309030408060709060e0d030c030c0c05091f0807050a0308070501 77
    0x240d85444004200000d040c00e6802503040000281ca496900d403a0890b40360b03446072442d014000006a20741c1e070040c041d00d0720890070028544040c0111220000810101301c044400b1105003002c2070f20341e03244600301580554568014902c034140d07541142050b070007021650700040c0403500c00c101c201c07011944a2803048222030503400d412080301e02031a213402d004400b000c0d5142403180703911003015801348554010550783d03210f0308441c4095854407481c0d0f0b0380c000b0a18000f0781101226487e413000302c000c54006c880000d010304004000025800c14910405141c94059824051668000e0004012586d08842020740c15202030030040e885c0d59500d0600c074650b00881c0d004c21814440c43c0d090003841034201591405039a100d139250204907a0940a002c503440905400400152a4900c100c3c0401d110b605081c018910440114100301d584100103501500141d1b040d202c002c107074070b058900303e05200604c180180781000c05054020728000020340c2401080c48003030940702c0c0c005040f408110084d8400b = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 39630850 1250 39629600 39629609
    0x405060307080303011512060302061902071208030a050a090c060f1e050a08070e010e011b02040905011b0908071412010c03090303061d010611070e09100b010903050604020613 77
    0x2c0f60780700d40e035a11288442111258452020800034201e245030a42a4040e40040c0c03900642000d01e4815149840d00c59000c5508901045004007400804d4007111200d98202e8540540c10840e101d00703020340c4000c115007000d028250f03035915142c28000040c0800c0c140c0030071107615040c0a1000045c03031500380c0e0b042540e20b01e195151380364504800103a9030400040c1000c28403e079118950340c0e84000098440c4012411b0301c90218446403e594090f40c820395040c90201d420038080c8844e00c0865010030180d40b2113150450305030b519a00d10380d05044060603842d640e28140d14180585d140303002c0503141c070f6244c1030061042d003901d04ca2001038551108182000e558448c40020005003840719401030082842d4801140060f0a042002450308a01c40c921920983c10044a0015920301902641c2c0f100c2c1c480d04050150282d000300040d02c000c81009548110711060240801c101c1c4144200200d070031b50f00c1c8490510900701000d00120f50b0001d00f542d80a40e050340c64994424440c0c4605203420000d520 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 39632100 1250 39630850 39630853
    0xc0801090b0607081b0d02031c020a030b0301020a080105040c0513050f15040f0305120301031a0402030c030a03020105150405040302030304080a1704050f010c0203090102030901050d0902060f040e0a1a040506030708 94
    0x4815000800e4404000c4488020301c0c00e0301c10b1050811b404a8581c070507044150200c1601085e14014988d00ba40207040881c000e007800200300ba042e40100342641c015441d288046201e007001044681040d0168000481e1285402d901d05142d40811407000300041c09003a015203402c0300a81c0751512440e020b07003440004001044c6d1169641c82c00004110254001180d040c0514000c800048642e0710070f490503607a0140000c01645200307401d424441c81c006109a130725100d0880800520b0b203003441044044c502950022540b45042401038080800c0350140314042d502d04020040400d6011050707a4100d0362044500b0764500070440b0450310071603c10021100001d25000784020841d0008008840111000007400b03491003113842661a40614420140075800801c8292090361182c1c0040c0401007903140000f5802201c0d4010500f140c010441d00802e811000a0903c0340718400310b03e0302e600ca10448820f00c000350162005003014a2114a034501640d1100081043d59030140001c0d405002001c0 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 39633350 1250 39632100 39632107
    0x2121b030d020f0301080c060a1b02010210060b1210050102030f0a0504030203010f09050c030109120c030302120705030702070f03020f0108090109170d0b01140307180b0310090b040c0801090b060708 87
    0x41509100c4c1d2003841070140c1d51160000600050825070150f40c0281c9054039004100551720025640000c031441049046001d1560030a5131007800c1e11624028124020700241c45010117040042c40c840c0117054407000382103c0c03508200ca40ea0000c2103980e10b442540f16070392030b005c0d80117060301d040c0101c0c0c0000b03506500b13000c0d58002105c1d50384d03c0b1184d040e029504880307480170a00145030889181c19000351607003100014130302da031900032071081050a12074500186800400c08001640381003e4480600140d000410301c25070580c10000c400180100c3d000314810107145a0015180c215440113080c14401d20b03400040f9103500a502c000445070300079081e0090300c82c4481030100c1c1c030380c05840d00107061450082c00740011752203a000c61510781c15501c0d185246448011040d01d076640714241c902001c00b078900c0c01207041103040c005540144e902041101440d410022100c0907181d4a442c1c1500480c0342200e1050746c1540f1586040c11119646800940c1c10040740118070580314480d40a0700052001 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 39634600 1250 39633350 39633367
    0x12070e030a0f05161d01091d01020c0a0209010503151909060c020c0a090e060a0f200a03060b09010206160e0607030e0405060d050318011e0f020c0102121b030d02 71
    0x1c9102c0904c0c40640844036203070313601c80140a22040d011040300901c101d202c03005001a035034692000d01817103c0c0f428143c0b110000c810803642642d00800c560a0160844883c4400b1410030f00b411a01412084001c0c10041d5032584501039283c00041511844070707240c08031110343d020300307901401501d0b8003d001481140303103d4001030f644e00f40d61100f5034000c5100c05000113941c4442c0c812886402d1421015240a8403a4107d00000d40301d20140c11050380d564090348608810842002401c5184480d401da88511a181014003180c0d840d90203401040000c0140302d0b050380c2e0104541da408155000300d8100c06203140400c1340c1c80702092400b20b03004680050b103074041c103400040204154804450902481d41c501c024001034005010008105600600004403603080c6200000d9403000103140480195817220201c2c440138109400b40800300342d640729041c0460380c3c14080092800400e00040211201814995035503204008000103a0495814040b00f07098091080b691982c21784202551245041c = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 39635850 1250 39634600 39634603
    0x2030d090219030b10170709051008030316080a0204061e2c030c030304030201090b0d0b100c0203010b15041203050d090305040e010e0408030103080f0912060603010e0312070e030a0f05 81
    0x1781c0340407452514014000038003075802c407428100d9400103030103400c034107140c610154041d1a001d0828011001043c01c003040c1040d080014611900003106190420401d10f0006011010040d042d4503da40c0100024800d55800407100034095010016050741d9025a0004440c903107030102003400c0204902020809000850503480303058030040b4280d50711200c000041542d00d229a100080c04110a58003c010400a0f0005803281034010a07010450440c9000010284910154180081031803648940c09506007449540c4600c0015644101144d081001c105958062803060140e880302450007070042620910a5461f43c0f4020b45091110310300900c0e003e00203400c140241200501c140000050000a003108140a103400071400c91540e42982ca4004059200c0381860015a2040000e210307191100d440002c0c501d94a83c0180c041810030004141c01c1d9124401140c03aa03078414091103410220100016401605c64200050304045010100b809e2190000014200420509022050160 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 39637100 1250 39635850 39635873
    0xb1e0c15090705040509101508060702061504021806030c250b0c04060c02010302090f03030d050a0c0e010806040902010c080c06010305010b010809030912070b04140a05030d02030d09021903 83
    0x214442500c052940741c8040c442194003c942c0c940e59a4000c0c048107c9100346035020004461054107040f0f0301c42e40700e04c64079151103815118180168080c008103c07054511a80254940004031003d61800650b01d00c0b442282e03001e00c03d00e610844000002c03400c400450812103413542440742d200178011000d00700b0b08030103044003c400d664030b00240002440010003601118240c5401c0d0300c1c1c01070950a10b400460003504218000c42e0407001c5a138500555070790400c0540300445a00e42b000c0303010f280c00c100340816030758945800350502002c180030700002c1e038014500540c060415030b00003c3d40c00003800121a415682c04c0701034074105000403400030340840410100c0c10380c0c3c01403000307220f60010100110380200341118082034070382040c00081e032145001724529819910341030807034007855103e81100940c0e5109038010404c070700c0d003407010f00180e0a00c4140c0000601d0100d0292141b00041c0c80c029490307110b4280703c15503080e40e80452204541d01c1e0090348194102131100c10440c41c0c1c5924001000d80e5 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 39638350 1250 39637100 39637111
    0x306030506070203040e0f0604061a0714030a0504210803010305150f0105010c03050703020114071101060b18090705071203020c06090705012019030302220b1e0c15 72
    0xc1c40c00059030300c50000048808540054890081039524032a03881c403d4880500321590180e2280d10004014441441040d61204080000755503890140f81c004250b00c895000a400d40c2c0090141806c00c80d00b041c1501c00700c0355503000000d0000c4000d00000120440030000a1240350048004801d020b40000c00701c52819580c080500d8035114030310740304124002441228001103a4000d004001b03880b81c40a0300d8464883e0001083e21003680601d801200c0d41102c003e80020606100000c07912000d006202c020030503074420a240015984103480440a04881d0078090854040410091482082101c5210b900004d12101c1035103020340040c00703544901000c981030300c203035804140030002c04500302003141d80585500160100b1b9a02c0c0b200409040c87d4030075007070300408500702d044a00b010000c40c545846950010303a0f410f00300d569031004207485000b0300b20000e1160014001c1003d600300f1640c034903101c03980b0185c00002c49030031031000344103a02001c0100e00485500b5440d08108120030380c00345 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 39639600 1250 39638350 39638353
    0x2090a0801020c03160503070b070e030114060303030a150807030b060a140f040b120703060204030501110301031a06040b06160203060603120405041a0a06051206150a0819060603060305 81
    0x16940d8503206801d07800f80c0043c0440540017000f4000c98410f0400300c03485510f2042056a00307044030394548444240c1d04942141c0421079242c1c60340b010b0308e020306c110a01c0321429184840c00c3c0c00c040002c40e949000040c40c0c01e0040d6900d880700400022082c2c1031000600c42d00c011240400c0d224a8000d59030b41d01030350b02a00070380f0201004500240a51000000418007519501c03001004408010103410010001a0000035100548001280510428000d10300850000d41d80714618580a42100c6a0b02c24614914100f400144005080104101d44241d83c152140b080c0703440d8240010001d0443c204015031200300026140f40c1c040050400b055244c0c000c40075038030b4507618a0249500d80300152013080c2c50303550030041403045140a5115540c0141100c4c25000506219800304038220b11540160011880101d0a507014040140e6040c4d801082660109601810405045118002d9944c01004d001d80c19000604030241c08038001807501000c4c60038030603659118009001071010740070a4409 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 39640850 1250 39639600 39639619
    0x702010b150702010516020f040f090516030201170403090e0103030f09050105043008030f010312210c02010f061215020c03030118090206070308190615050706020408030d0209 77
    0x25200e0700c4280c480c0150180c41da1442e19200505602000b00d2070601240d205810708000c0d00316071200c0c411100d0820301c01400080018160500d54540040030810503001da4203d00c0074401070341d000054010182061038102800d486e5464152014060b9401101da80c0c0c851100020a0650045072010403102c140c031441c600d25111801101c640c45140a00c4000d0010301c4086000305804901d5144455001c0c0c02c0b64020315120750b1a046141d00175a003025604102900500500c000701906801214403030400c20700c4019000d00100a904c40d9000c0c4000e81c6540b41840c0c0781d428001c1d000b103441c81192540402040707442e03400f0690f01000150055a40102070140e24402f051148229032014030300e02c00450a41c0e190640c000480c0100d8601c070920640c45580c0b990043c1c80d9000a49103640c1300b034451440038603000d00041d4501b211110007201d0315090140400036562144084550400c56107045036403100d040c1800c2c1d000c0c1c482c65101c140c05100000340028540e80540c05082c2d15401159100203 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 39642100 1250 39640850 39640879
    0x8010204150c151b0f17060f031005010b040513092d15051803130b031b0c0102120906040209041220030405100c050c010509120604050609060901200309150702010b 72
    0xd42c405030206d00040b00c0a500041003151400c207001e113464072402000c0b40d40c503201046011003510400e0f404610b00750004101071041e460b050440c1c810106040c04108902c1c641d98640c140710107140303045014038540310743d034440003403084821006550fa08541c8811048510403c140004c040403a0030840780242c5e01e88c0421000710100844041c110382c01190741303080b42010401d540c0c981c400760034110742d442c02c15040354002101e0406001d101007074000050325580d404005030a0504000c0001c0b055401c1101008016070b0382c0d80085401ca50002141900c240014005482040c401c0151029000c03004040034030000d4004004d109881d029141ca001848168800f5615240d52000c010402d4210078442042544980c01078012590003d0003052590001c0d9a05800c0403029181540c0a80048040141503182006099000b4111134001c00c0070456a01116921911078602606204400030203d80c1103002007090582545154401400c0c0341403601e00a8001e18842c507119000700340107500c000e0b = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 39643350 1250 39642100 39642107
    0x31020108090a0b0a0c020102090d05010e06060103020a05030f040602041206090212030901050409050a0f111e0f0a030902040f0c0807080106080f0703090f05010f0c0908010204150c151b0f 82
    0x840c00c3e40c0003895008503103d8010007805070044600c44c00440d0350a0050a04d16030b60b01c1d8944060900460000590800c02c0c41c0c2c003810050001d1006050600411035500120303403040840b0743c49414000024500e80702c502d0104083e00c2a64025a011f000f40314442c0181710990b0f00c1101102c1c42110061009400080c1898481c081c84030400e0101d5024041046102c1264000b982e011048500002c0e0140034031103280204c3c1c114803903a42000074040f46002485883c0400c03030310100071080f01e0a0508040d01d1070408144030b140041d00c105601c0c1d84081085407260f400c0414080c0c20040305000e078080f6060f000b820042c2c09c440b0715002034150000098880c0c000c030b940390b000e03818440c0741d100303650f0381c89100382c0240004440458092102c4000c3d6000b0803000c0c0300c0d800310425420000325952080000003022011305401100780c50f4410401001490b10307400e80081d40c0066400c25450029807400c008171348889030710440340c1f220704000d01d203417024042c010920104481501c40b42e161500508046 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 39644600 1250 39643350 39643363
    0x60e1504061814030307080304170d0537020d0603060207050a02030d0509010203090103090f0c0e010501030b040b090a0513050318010f080906010303200102040e0108010b0306070909053102010809 86
    0x183c4c042c0c01c10020003010846030b40082d544a400f0f400c01304401402041d8042c26648547c03291181580e0726010300144008111001551240e481c0443c000f40509020320351441d90306c03c040c40c2d80c6950001e06010118440d8001e000196080141103440d035050b414495102c2078581c400728840d0140c42e401c2d002982c02442a070340f50f44010390095060010082c01034004110150007590845034400300540010700c601aa10301501704a12200030783e5162a002409980d1405000e030710490408401d98110384607620343c9036003c1b003003c0000c10740741c645a060503100580b41001130000d0000261040e80000c40a07500c440009003a07a5580440c100c41208854940056404400c0354020800400110703124203c441d07450b0361208296001044004109822603100368005142d100504004000040d42803290441c02c140c1075024003070b43e1601c844001c00c1000740d8092143c92680c4c580105040041540600706941406403070402200c4445190500c0309202c44401c0340021502000142100b2010410 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 39645850 1250 39644600 39644639
    0x80d05040504090804080f01151a07080307050418050105030c01030e1504080d0204080c030d0203040b031b0708030106020a020f0a08070303050c0c09040c1d060901060e15040618 78
    0x1100d0900303003072000b04805081e1840f419119448107005c00300d1111028400014070b648120000903a1300700924004d00c203c0455444403400e0004e61203e1404802d104040710071242d0b0000002e5569a11514143e609000c2c0d074024050704d2034802135000700380b0782d641d2105040c2c1f5011011030303114213103150045003580d0030903e8201d600d410502d420140815002d42c4035400074415542e00e03040600e2340c2c102c0c00c03c0381c2080e80811a00c0d4050f0280100c9814180070280a000c100d00c051440c15080a00480b03003407102070225420550081e8904055290000644003940c2d03010411580d83c1d42c0da940000c2d40c1e0701001100380d1240030200080b54040c68241102c43c211486c1c0740140441d20300d10380f001d40300c03600075110f099031500591203054099601c000305180710714032541d110100a400d00c030303140888807040d8081d5802802000c080c000c2c2d940d078011105046401624044d0104003450740030602c1070030b6803104543d100e0301c0806c001c5040fa0f082a491072041da403607907012a04550750340b01e409142100051 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 39647100 1250 39645850 39645857
    0x40f080c0109090902010c240501090203040209130305040302030303041103010b01020d080a110918160302070f020f0303071704060e0108040c050d1704080a0c060c1a070e0a09090201030501080d 85
    0x41000110000d130030159a050050400b01c22200c01c94541d004e00c56904004655a10b00194040030000c45d903105090240484000441c158505680828034480000c3c000000f05e1500084130f0042521890464010b9a0b009e42500d460741443d00e81b03c00d0b1b000d54920305922a508140b80403030301d54800181c46038102d4155540e140c6940780c002c01e02d402007400344504229040208000b00c0360341c440c0d00c101000b099510707294034524541009080d4034000e9000c40842050b004110348804a03c00104003d8000c0d0102c88800c81c0b07039007180000c1e11314451003d0080c61060150000c2911600324005041103c8150701c2d1850700064040044440c0201120b0040a00b40c1b9903100348100e0070401e03c406100f600c111120710010040d0120441c00350003c0e805a22682d200da07000303408003e804511070008012900f0040040300c500c0e600c05029140d96840f103070310401100006021a4400c0d070341080342c0703407025000c48101925486180060b0191f440141c1c042030908000203040940014048282c21140d076 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 39648350 1250 39647100 39647117
    0x20411030610081005060c06010f0e0c030402011b0b090c09010801110d020901091a040906090915051f060e0907050f030c07020102150118050903090f012303010803040f080c01 77
    0x91042c1c82c120806000b03100e079540c11301004201c2c0d0f25800000d00c80096150b0007800b0341d42c50003c06020803045078108030800780c084400d22140b562048140c4c0d80081c1d09082140d200820140000310300c3c1900d0201401c3c00c0441c505100401901145e0544101e0090f46c4806040c0c0c3c0300c000c20f90a803a00801d0b03010741d10000700300980c2815020b601030541000149001d040142c1e07211840b686171005412039030300304100050100039a0006204070303001008655028081158070f80c90340f0311080e18580c5401c500d25203d0740021884003140ca020603c650040e24465642912010001c1c212010007120f28001c0c0000030104141038000c400780e512507290a43c280d444c503601c50320b0f03500260f040207100301d040d44242c020145002445c1d020050107800e0054110354012124501c410a90f40b001c3c1041c03205420422440110703484000c19840914803e083c20f42c12a590412508802000d14188020841d004000400d1991000c030040c4120740c9034240103002c094441c1c40700d6880d0003120501601140340034 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 39649600 1250 39648350 39648379
    0x80c19060f0c050c0a231c030516050904020702010c0c0801020703030b0301060806010620060705030603150403050406032301083d0c021c0201020a09061d040203040f06020c01090204110306 83
    0x68085112062982010488101034a0b01c0347c5800d68450003c002d52031200140c208050b4076203e40e031307400207010340c0104841040c049c0140140c03040100300340c0110340000b511000c3d6409841240140340d4000200c00215907140c0f0414000d401041c011130010341086040d05541c5014020a401d8501c408098001c0c0e0746418010340e2040c002115885003004407158041c400740041c421144034040544a0342c0e52071401108050030400304400b09640307001e2a1050102103035000e011384055900c1d0303040000340000080c14441914140c803007500300381106000041080f843c0070a54240140c09900c1c1040005101030f400b548440c440c10500180060048043d42c1000d4560803203842c0a90b1401560008029003c00352907500401d081d40d00903030b4000803490205a48916044000e0006140181079684414034070400101e4110005100d5a00400850184001003952103981580304200710764480c0b441010303902800c4800410f034401d900d4803440400f011800411240303d0107004110383c0519020 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 39650850 1250 39649600 39649613
    0x601090b030f070f060908011a04050604180812090303010b0906070305070f030e01080702030a08010b0c03040e0a1506030504020f0d1103030f03011802090d080c19060f0c050c0a 78
    0x1100389103030325100342c1c0e203490350710361003806580c015110508840801c9400e104000c0e20340c3e0702c4c0f41e02c003655580c5014012a1051005903030421a628111000719a58031860001005081202c4080042d4441c00c4403003002c01c079004004144c00b1541d285800c01d60383c0c1e01424140c42e40801d1181345c0500004000c042c0c442d00c1c01c2c00051161a00c03c0c200981450542e454450794000c0c5440100e000c40d01d80b0307556214943c0c02544442d0321080d80d00c015460201119002450203006105011304640049510b0390040c0d800c0c001e035006040109821a2280382c52000003029100161940b1800301c012100400c420703102e405414072032a0013501000d0b07400324075014020200b10500065426060800340200c0303d075002e00c0100108014050815160350421440c480916180c070300c012160b910400014210351244c04140001a801030465521101e59100c090304142884400a4440c2c81030a8102c08210703059000f2104410255801c2005a0510100f0340d000e215100710700200d540803a0b80040003554 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 39652100 1250 39650850 39650861
    0x3090203070905190509060a05180a020f0607140319030612020d110301050a0b04050f01050a0b0a18090c020c0a0e0c0c0102190203030103050d020a24090c14010f030509060109 77
    0x140413054220030b01010000445009035442c0c211a04403a080c0f01600419009440e00b02c07645503800c54501c0e10003140b0035030b45c104051009008140e4015070290329901c44083d203031000e030801c11a4180c05501c00e044c0f500d039400343c1094029802450840700d00c0e5803003481200305444260441180102c003d4003000380e03503501202c0480300703c5a0309c41c011039291000e0041034040c1280481c0403803001d44020403c01039500c01801c039007c801c0c01d000100301cdc0d950b80e01f07010001c48070768142007030b50342c12a02e00c206c0b8442c048003502e8501003480d80340000d04100e01d52280014820f55070a5414042c865410080800c030700303200b56441c04007480003080740c1016610040c02582060f4000510344800d800911007544110400786e00940c002000400901100f4006d0701c103204418405032451840c180c5d10954440c02d074510400c407401242c21b5030901c6100661268066a400a0700c1c01d94841e6a891312090781e40d00c1480300c50015100c0d07028201014003a0040b103000c1c2c40b480014011070382c00c00d21880300030301 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 39653350 1250 39652100 39652111
    0x40503090d06180b0105041113030b0711070308090a0b0a090302011409130603121403040b130506090a03020c01020f0a0b09120301030c08010b01050c060406200d0203010e010603090203070905 84
    0x150f86402c110060f81c000200d001d03850748540405000e42d03140c03000b00000c13540340103440c520000082111689800f420780030701040c2e0307038800070840312515000070840355440da40c105c558141c41200380c040140017080001d003d081000301c42c0100d2541d11020b03030401c0d50043c07043d02808120a8402440198050401c003010780e5100594242054485000501e099520a418407015944c80e2414000d00820500400090000e410440b50341c00418181d03c1c002c0c40010405080c0c46545004514609810079000002e9a001000c072a094204031b0240c54032120030350000c501500c51980d4803100741d4008034000020f0030008010b0320151009407108440c1440c010401d00c024001c0c550100c2211a06502540c0a54056200d50501c00d05000304242144d6881e020305061107020300c00c40004045c0003031016482a800000420f03001c648880300000940b005425445101020030384600032081caa01a504a95800281450590380e5000950031642c0c0c5280103034040e04140d03800e011810dd2a0001508034 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 39654600 1250 39653350 39653363
    0x110a03050c1323042409110102070501050304110a0b030a1a1c03030e030906070f050106050613050d02040906050903070314030606030708090307081611090c04060f020a06050f040507060206040503090d 88
    0x9010400030340c0600510b928580c030f9006c2c1c1d00c100c800d0a0000b01d104610060078203000a00080707007004000380490000030001418034000b9405a0003e490b000200700007007014116032038407800c04943c480c01807d09540f50100c48000c030440702c006842d0a11214410b0300039500798004520700782c2c8040300945800c0b18202c000380300420149509442e904000c22543d801511110740c8044640340c05400d48103a603102612902080c80f0b420a078400b21803030b5000b2244111486424000c4610224000e07001031103010b00b40520b09030403c1030070b80002c4003c1080c42d21990340c55481140900104266000a42e070094000c501400051001801084a01d40000c0100300316420040140e0b40c0b00e2080d80006003010b03103803507440614400c004001c9840d0000f1482104d101d10640ba05035186001c42c02184903100c1006610840e40c50b03058000c5c010505403a400007005c2c0001d14004240944140090780c0450b024803440c0d0000840c1d40c808209580200c1d481400f65180a02000401000c0d0100d141c3c01c1e10781 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 39655850 1250 39654600 39654623
    0x512160602030a0f02010e0c040f09050106240507200d05060a020a03050f3304050103082107080609060105041e080d030204051309110a03050c132304 66
    0x10154892145001030840e90700441e43d0700c4022000030300d44079402c0009801e5a040085603108540e01041400741d000080ea40083c20019014071000074066180c0003030820f501c0c212021515102d001550f60a000d1107a40421809083e07100c101d40b5445180d40241031204868442e040c110b101d10850300d0103040c020082c200910b45501e44a06220043e40c0c40702c21164001049040150540035445d4072120340103180220345085405503c3e10000c04501d02100b50524448030112140601000641c400141c8108419a1203180500145d841040c28880c028000d04264140204c080b11048c420a0550788030384940d10717441d00b81b0a00178405407489050210501c0041115480ca15840500e0740030a1100360400c2d141c0425a8104a0000100003c250040000f444151103614040c01c030f44068100016841c28141840300484c488803000981c80110400000280300000a40344e10000c42110986481049200c4000c202d50602084108420003d541030030138044250006602a0050315078919 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 39657100 1250 39655850 39655873
    0x8041e0305030d0e010b090c0d0507031b02151003031b1509080a0e06030601091403010b0604080d12021e090d0b130312020703170a02070602030f060405060d03090512 73
    0x210f400040d0201d140650b510480000603509000d810203040b41952031141c103041070103624180b84600b6000e0702d4105d4840001c074110901c41c1c1d01103842084251800205a519004020f45490400b001490a8025240400c0035003005042c40c0c02202c0c1e1648034032008029200004000c40a00117003520821840d0404004410f0750f1f000d9001c481d80b040c0b0989035141090b880140c0000b038068012801344006004000c1d00340d0300b0200c48010350319040c0018444000150000c1e000d805280c440343d030450340c00b04000682176400214140c60201740d40f030b403c108180d140c4150049000325071028084450714095402407000c154000d01c42000701404202002c43c05840301c207111541a1201078a032a100000c03c41031652000030031010303031842c45003903161080540b002041d202890708081440e16010002c5050555290704403010641e00240a5481e807601d40c04540c081c2400700d070498000c03030606000440500c5d03d600f0880d5102d91548405140c41d00780b40500c00118200403092000d481031506008 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 39658350 1250 39657100 39657103
    0x11070213020328200306030d0206010302010f030b030f0708011b1407030e0609040e07060e0906060405040c2d030609090b0f06040608060a020a030c090806130206040b0a09090c050708041e0305 84
    0x113150b542d500e6001c0e03582e0411106040c54148056015070442d00042e00610050380c2c800542c14051704a860040f4207603040000003401c0c0081c01a01110310300c01d400b40001c2d01c40301900294000c480020030100c042d200d01905441201e65040c2c030501d8250108928400213000d51900c03007103950090400c1707040c140f104010404a44a003140c500b182d500003142000141d0748155440c0c0c00d808141c1e0000018100100800c1203030003a40103003840380d521010080099881800c0f4202c060a22281c11410010381d0040d0030b1640410700603090001e42005004a5030708103030700620049c40ea01810b0700e1169a940c425807000030401034581c692264a81900041d1a00b0400460b400391070001b10042c0c3d0380c80e001c200502103c024076001024001c015904204420780810035903406905d8120b1002007142130720010700284911340095003d001c0101351440e030141e010702000b0554980003c1000302660043d400d540a020b1644010b0a206040109015070140903030f20440a00840c0d110740300d010745079500c09 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 39659600 1250 39658350 39658391
    0x18061306090906060801050105010201060608010306050c1c0504050c0d030206150102010b0d11090f090706030f0908071202100e07060513030206070f030311070b13020109030611070213020328 84
    0xb0b403060394444d04244500e44081c80f510b40100000d00003002003a15259003c3d1070f1020501c8094621a602d2002494024040f4100c0750703102c0191010300c03610343c41032900c60002c1c0010345040c0d400f403080e0000e2000c41d041c021041d00081c0d405800034941661201402c8040a6246280604654940c0c190701760f162180300000b40010711030013600b48907540d10420700c5a03a0b20010800d580310850f01003031020402c00842d641c000d4031007918000c80c00989564100c0c01420441c04000d000f00030006000c424400c100340000440300c0c541d400e0f10141504035204006843c1240402c140981045004001c0103002e20001d00c010001240083e480603682d400103002900040030603148a011810003504240c0d15104100015a07104003107410260f0035203603001c44c0c01c070042003080e0b40403001d1010402c2da80501407030f10046510410034407075402080c00e00c2d0143d4111983c100c2c040e6414030009080c1d60464001d5a100305a400111030030100000100c0040341d250045200d4203543c0d50604000c41d4228003200c = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 39660850 1250 39659600 39659603
    0x10507080307020111131a0a0507030c06060302190602061b0d091403030c0301081606020a08090120010209151602012d020c0f0d0b010b0c0c2d180613060909 69
    0x12445d960b4074102c4007e0002c1c12000b00c0c0f260905c010841102100d4106040d03518482d010714010b25030740d10314900b50000700342d0f90300040c5d0f00c1003002e000d640541c000792580034261001075080d11aa07845d0403416400d00c1d1150608110088000d01c54011940025480000264000c001505904031080c4450382194826104002044400001400f00080030481a802d5a001040038501d840c17500708025110030004400501c08000001c900c850380e03200700007403c0001792960303e001c0790112600c209130003076001203070182c0941482c1042d54010301d42d10f42500c884110508090407240702c29030044926880c0e02030241c400c402c401501410841d000d8101003400780a64000f0300c403809800e000c00c20665401800540310f0801000d04400241e4089641411a000181600e40361107402d900c917800c040380d0350190b036002075071040440c0716000a00d807009250904078021250011046d01403000d02d411601c101d90108610f00081170b4030341084843c0c6400c1a04010303001513001e403170340740072800e6900e032450 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 39662100 1250 39660850 39660877
    0x4060f0b061c0b0d030207090513050f07060909020702150d0908040e1504050405030904090201051b010203010e090705100c020d210906080121080405060708040801051005010507080307020111 84
    0x1d910141240354400c00c0040f08040320b0781e841c40e0034103540081d5222280c1c05610126529000420031001c1c08200c00f0100c95071000a84a01c4ac654081103940c035042c41c480c2a002031210900082c0c14000340c400c41d100240c001c0d004a40d4008111080f0315a94070144d81c01f40f403165100070060118503180041e2024002d049040c0340181808050001903101c4c451100d40f2a82c076003018000000e00000c102d80d003410050360302081e00d50340d9000503120b44c0102142070100380f680040b0b00481900640c015410385950100030390068450784000b80d40c1c3c44d02c0c8e010341034010700305202e240c055500a000c1080620320041030901c65142c40e60714141c06d09141c0070203a2044d01c030030382d12800b460b41043e00d0740080c02d00382c84e2001e56036150404100142081c0541c41010b0740401034064240480e510032503020b8140035000a64980e030515010240341e000b0b00c5040d0f0994680004100b120382d80f002a48102c40c0140c0d42c03142440d103180c0342c08040d0f920160000c41036643c6d48035503a030610804c03c09021060917000d03 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 39663350 1250 39662100 39662137
    0x20708040e0408180618011d06030114120109030804230a0303020702090708090706140c0106140a06090303050418020904050103050303220c15110303010801021305030a0b04060f0b06 80
    0x501001c050825140c5551003405c092103074071450005032500d0150b1318000d117448407640c40d100c0003c8680b0103901180c19002003000001003402085001103002c0c0180581d04030400c00004564a803c0782d41d00c0b000240003580d40004503010a01c24000b4444440b503442d0060800c01d1003905140c41c16080c2e81d07044001c69000324004082d880c0c840e40ca0755115100342024451803400c85903484d00e81806010359014058855410800300307030f4800c25200070b080328030000c00c8080e0700c52110a03210101c454005d4030901c80d807500494072a12455014040b603505031900c5d4207140c14540031460280b0603401510320b443d030030b00c420700c003580d0780307002d040e00840c011000b440d92401c0c080034445089980c03040804001341c2c01c5809500007152075620004035120342e002541a003018902c212440d0311111302080d004e20002c800071820400642c020401003e03980c0d0410200c55036503092548500043ca4040c0000c000c680028002c1003503070704110b03d600402400040c450400350001072054100c0d40f00300e49101e551a = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 39664600 1250 39663350 39663367
    0x306090308070e030a030807020a0f05071a1207030203060103090803041208011202010504140303130b0a0306060f1e02190c0906080307022101230a0507031b03020708040e0408 77
    0x1035194100d55580740c4400c4021480f804650f640090100003400c0246010000c2ca1280c03017030240e200794590108083d41b4058440c20314a6071440107005455043e403000c00707070185460300d040031240004600c450300e40d6a55500407059000303400040c00c03d1306054540442c0c4d00000d08101c01588100c1c4600508072180c5500b00380101a460141c000076080840030b408a000750ba0000281c50803102011500001400403501190545c02185240400da003408200030440c4103128001d044071078981eaa040066540c1c03041c0441e9008401d0090b1808900d0385494000781d0903111000d0500030104d401283c07040800181c06414602c1d100e5001c5d0780d0841075001c01c2c002c000030342c09100c2c02054041c3c021402c100f007980001d9460001d032180144412149250140525000c1d048042c1402261003801041c15a4403100111500f0032552103034914a8280050704450003446071403100c001c501c2c601001d819103017105130025409500144c030714441c00d02001800e0300700520a140b156100304c843d00c2d1586002c = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 39665850 1250 39664600 39664607
    0x10030c0e060a020309060d060302030604050708151b0a090b04060905040608010b0303030f040515151305100b0d020408030a05130b030105060702101b030e0117040c031103030d020403060903 83
    0x505080e688a410200b000e000c84035800000d8810210b021580d031946c03140d405c5030080052100e907000079014003c1c00100020f000f004a90030b400c5412100039240e01c0d10020710011042c00c000c44d0410340d07260840c40c1e40d80c91040e2460140104604a04100c80f10719160b0049481a400c41c4c0d02c0304001501440051040341040e0080c00c00401030340d00280100c40743c2c840000e40ba404020a410412000c01e0002018080c2c00c2000085036003c10341c040c0080e040c45415a0328000c4110010780c01a280320041c068203010a218443c41075054961030200d09040c0440c1c1c46290340140080702c0403d4080c040400c2e8008188020400840c503620f0b1190f031a0301d8090b030380c8075070152a030103100c10000034401004207032120812502e00700c1c0d041304c0e214441c0304050000c1d110303101c44d020010b07001c02d101d50202003010380102c1081c0001d403090b08d42a030900703c003158506858004a80040549080c40c3c02080018a403528155807000002d050700c3c14560581d03441c0040b40c10580c800c0e0f508507119015101410381 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 39667100 1250 39665850 39665867
    0x5130807050a09020c0d031e05090d030e0307020102070302010809010f0608030703081f150c06092d0206070f0303060803070308190908070308040203120408030409050f07080f1510030c 81
    0x51240c029401d220f0342411158446c00b0b00308084043c1134403104081d0420310104040170000759200ca041115081c1861940e99a032002c40041020074501280110a01000815100c05543c164003e00341281547d004440b4048080c1074680d1325900c520f20045900b50701d01030b060240240741c004503181c080030f0034018141003000d0800808a0702c141c164444542c014008030301603071300000801003000c80280d0700b200c580821400c0a4042031402c0450300401c0340141021041e2500c6213050010284d903900c3e62590302d10204002980f1290800100340080c100d1844407000c94002c0c10009101d0340c1e00c0704001d045601c44441280002c1600f070801006580d0002c05642100c0940410032660116070b442151600c501e94019050001d130000150440d0313410042c1c0084110300215440d00c540d6a1102c0079665009401205181d40c00c080c00100c0041500c030b00c69114030340070b544810301070b254144256800f40c0d000e46005000701c40d50b080d091031354941d80c0c80ea00c8009001c0c1c1e00090381803504030006003c5103 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 39668350 1250 39667100 39667109
    0x6030d030216030806210c0406060503010807030b0a06170d02010c03050709090203181006050102062a030403050c0303040f0b060d020a1716080303060102070b04120602070305130807050a 82
    0x107106009802c03140e440700c1c00070072000750b260402d10916168207002a01205c074802e80301d8004e070b511410340c3d4a02c10340800c0b401010344040d541404040d072100c0c41a210384c0400d018403286d0707511105080000c00c602400d6030ba00031010113030000e4010344070841c03800e0080c01400803000c1540708010402000364248a00c0c84c0c85e49282ca4204240d0070071800c0102501c0b250310851241c25000f10100e1680c3d880c0c10b03041244142c04004440302444801404009080c69100b0240580582c600007071010100b040844500c0500c3e003c405600a1a0291541d81d500003520584c10072109100104a41c0070400c01103004900921000c41c20450600c2c0100d08000c0041c1118000e4102d040d007180140c81e80d6486100f6100400e514214901007050598a0603094009001c0850110200004d5480f808001940190300070b81c20384610300d8642c046840944a42c3c8560114680d46241c40c4000c0344003540600f104a2003450704030302d4403003e10300c010f14a96031a008014150028003042003e071a20810a00040 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 39669600 1250 39668350 39668357
    0x10f050123030705030402010e09090607020d0201050105331309060501020d020d080703140c0301090615020309060306060909040c060f0c0203030301150504081c080105010c08030415021b01020306030d 88
    0x141c0308148299140400ba00c0d0001344500071000c20210381c05000c0f445040c04c40a08503034100d2405498142d601c0790251942809409080d00d150591131041c007580d41680c402038005042c011481090a19640c0c500c05c440d2442614a20000c01900b262002010300404112701b40c04401d00f8a05103504451241d44040d0556000e5080c2174013541c4c010900c0703100703050350342171528030340c0d960403c150090310403800e4000000310700c2001c02480700a041d010394141d49074020704019241e1240d100101400707119290101582c0f06110762507051030b040c0000c66010170064001403c11015901040d16a24140c4040361081031058050083c26800f80310041031101e60300c2d10501d10250307500881d031a0304c4180a00e00e41c2e00c11b4194180501c50040040720b00500591007103030014201500e480e0b02c1c0c00703188000400022041c40c00021150b2140d076102c5c51040d0050b04403072950321155030303000c000c010300e1107043d416980074401030280e03c10a541208060071072000141e62454a40101414682c1594151052 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 39670850 1250 39669600 39669647
    0x406091e02012a14010f0e0307060f06030c1a1b010209010e0307050f040207020d1e050610060909020c01090602040f0e1305030403020904050a052b03090b0a02070606030b010f0501 79
    0x180724544003a0f032002a000512404641400d0710154050702240b006100352509103100c2c0c4035440800401803100360700a0808010010381c8070200300c240d6106101c0908480003504d018444020300c40e5040b05d22071002e0074040c0c5404400b40060700007030f0034190004101c1e58086502c800958000303540d00340ca40421030241c45040d081031300240c42a02c43c18a524010703a40880c44404646a0404050009802024a482d0701c544440c00c440d66807408802282c00d07006403c0480c01c0c1100890304402500c4868072030101143c02c241c0c0e20002904070006411140d03488602c48000308050703100620240c251004e01c00260783c141890103101c40d10280420118242486200011501c08010b071004c1c0c0358112030010090300c503410454030304141060003070114010403c43d1030388081003030380407074504a800c110341200d031039000d4042c1c0861b003070000d0250601d40e8410000745a103d203075000300750300340c0706000010703580c2d4807600c82100518090b0454071650349a80700900c40b42d0382040904407981d1000300044c64 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 39672100 1250 39670850 39670907
    0x80109050f160c060f05040f020a0902030411060a020c130f0c110d0309020604030c090504020a080303060a06030c050c070b09030609030a020c0f011e020601140d020102070302090406091e0201 84
    0x1c2c1480031501d08410400403074410070412925400035803a10300740c60703024070580c01d1034280101180d4005808034030a0b28030010028041c000c90098034030881c0c000b000124280403641c01e02c01268442c500c0c80c0114000c00210381160764411030f2007049070030f048000040c0d110b0108040b00841f0114000001071106e80d030030700c1045074400240030080d541f003807070042903030826803010a0180c040d64100504000c5240c0001c19100420384c00035100741e0080352900f20031595002000c3d281d10040c0ca1450708002549401d0000300d0198010701214221460030b103140003454004203003486040d0700600d102040c0054402e101c1d160030803103242c003d10035401071450a4041c01d40030f551940c0c480040d5024070800b41c4800c41c2a800354160540100081d00580340d03540728040002d40320603090081c50350490000f03604000b0307400c04841001c2160780c1030b002405100d045030200695200020030440f0703006d407101c144400040c1c0081400518503402440c000d000c699074030024000c0d0240b0101100304100d412202c05 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 39673350 1250 39672100 39672121
    0x61003020603061905060c1f02030103030503060906030c04090501020c0106050604050d20130c02010c0801050a0e150604120b0106020d05030a0b0a030206030c1c020a020d110c10080109050f 83
    0x9422640440e40b458a400300e1302c90350001c01146601881e0700c44000f09140301c01c4000480c41d01000041c02844450400d500d0031120100d00003030101600051050000030290b080c44004e05030400e000400311040610048005010b0b100c9200c07085491340d40202c0d205241c0b00090007058003510045595138101403c02e0089601e50284400280400d2181d211400c8540080c03a00300d110020060600d01c00c9811418101000d03010f1891414010340c81d00b080c1c1203600d80b1480b40d1905a40009000d01c01451030f00480d0003810b60080c01d071401c2c980740e6000000051b62010300400040c2403003080c1089003846070508841ca10700581c0480c06540056004900080d800400c59a000700304000000d007400041012449170f1859810081d08900000280811040110082d265401801d070054450340f200d440b91000380c1c000c5d0600c00300540d01201309800340b180034070301d9100c500c2c60f03000c22a414404a0340010b4029084810304001040340000107104001c2c2c00d01031315901c4458509042000d051004450 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 39674600 1250 39673350 39673357
    0x30c0c1b09070c06090b0a0903020c030d0f0e041508060105100f0509012a200a0b040e06060708040b04090c030c0c0201080717090d111b0904062c0610030206 69
    0x10200414a0841c03020807401c0c1e800b43c17031013940140700030105d1f207001c3c1c4200c1d000b444010002d40c0588642007007501d15290004285030001d03e584d80d82520250200c406540c040341000011703500c541c4074100140d000700d80a21400040007a04000c0529524140500980c5c40e910555181045040c018124001d40c2010888250040a203800c11003000c1406e040d840000865408003440528a00014203004803420980d000d01c0e14030801007260100e50040003520a55441682149074050104100d40b1540783c3c0300c0355004a000d4001860301000e65504d040a0740290046800d8400104e01444441c959100c2c1d0b40100446040070406241e40342405001200302202c000c0c10045803100140025102c0d88a0700401c803100410249281081e5035201c0e00d401000b544500003071f108014100750f03900001000341c1c0c01107032000380b0240346010400348820b8842c010416507410b5212202215100d004030310010004d100c0281d0005950728001c03403241494009444042408003c200c14000f50f03440780100c = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 39675850 1250 39674600 39674611
    0x509040b0c07020109090c0201060602010b0609010c140304030f03090e0c030105130506060c0129090c031f050603011404060803030613050a0605150304030210060f050d02010201060902030c0c1b09 86
    0x3602e6880750303c0121030700e00250b0040d0300428200360150f0045ca40542240c010b44d0490780007070003c84052010301800e801204c51285c0040c0107c52020003040442d554440301440b0f441c250313894161030b621002d42521505104400040010404006440508880c0f44d00895402c542c60320359454a00000c0c41c03454416402ca040d1955940803d4031039544004907508056010b009000c00003a01408068043c0d642d0b07100344182c88200c1814040703292a601075803150340d100039214159110a4101500d41d01010f5440311102500b4001007000d80d60030000d14004d25184440c1d01074a05e03214240400c0e5002c0c1d50160809600078000d00460380c2c0c90b0300141d541c600c1e003d1000501596030760012000b81c10f480c0d00c02c54200010300d0304140002e0400380198403c41c02502128950b0300340341614022911144101c29201d03145c0c18003886245401210604054014070004c1801034844146400b00e900507101d80b0703212000010062a402010701c50b0180c4003180c1e08214003408207040100d016441c000b0007 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 39677100 1250 39675850 39675871
    0x20703030c02091e1005180705120c0f0d051602010b0907051c0204060c1e0201020a0803041406090309120c0f0409050f01020c0307110d03020a0303150e0c07020a0509040b 75
    0x22656050030000c00200800e00c40c0d104d03902d080c40604000001010701805009621440e104c041046000e070031a4000d00099031010310b81702c140142c58000c04000f0f41105100d0004210f038164103107002024003104921034034001500e0529440c211101c3c100588410b00f9641084c50402d100d07900c501d070943c0d105a690400e80c0e034803400703030b241042480c48844001c00014404035010548980c482c1c196141b4a120340084000c102d10f5455811300e03010f00c00b5000b40180e1080240b54005074200029680040c8034100c0d104551500801c604d0900c0b9086807880201d50001c60656428030300300e88070810090702d09000c0e099001944000c5141e00c1c001074440c9003d1307603ca000200412600f00100c1e000e5403103110003103488001002980d9141d52005406560304280124159950718120100c100c4182e40341e0011b01412059a034283d01624000090701880901c1080000e280004004407521030124408001d40d01c507070900c10851256116001070307000300f45260400000502c0b18040ca50084030004 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 39678350 1250 39677100 39677119
    0xa0f110301060f0909030807080103050c040f02070501090f021c080306090402010e03070b070201080117100c05041208030117010203090a0303020c0102072307061d0405090106120b070906020703030c02 88
    0x4000c41e0150a155000c0500c1d4a014400082c207401035600038002203101c2d94615039580c58212088403820b00a00014281c3e400c40c240800462400b94001d00309051070030409410300b03a003030300c815084450024003500c00d520f418003103c0440c50040800408800160380c1443d070084592102e409a0000801c614069000e40c000309042d680540c2d14041c140710000c2c00c80c1c0101d80c44001c120181d4004202c101c1c0400d007050300218491042035000360200c6103802c020302501e8908800400902140019030f1709101d003c201c041454900d43c1281d00102d80070b11000c076039a51400d201074042544616601c05180d2040c0280000450081220711925406180160b200c20740c140c82d06009101c0c51078000e01c0c04a83e851411030720b19840b003903001131542d4001512312036540c503102039407105d0440d00b00c50502d26138920302420a180507880740307800080701c0c030001580c41d4031100d1620001c0713148130381558212191420000400c0c1d102496a0241002e48003810740a4555500605224401d940080c460b02210 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 39679600 1250 39678350 39678383
    0x81302010804150908040e1005090408070201210903021006060f0f03020d0515040b04050c0f16080f070203060109110304030507240b0406080a0804050603090a0b07030b090105030a0f 80
    0x58402220040f6420040022640a20b04980c0c140c0c018070401369040c0d00400092011400681004115040505040803a0b84c4907603528003203031721040c0200d041c841210035100005c00410b0030304110310301d90074002410400c2800c0c041e18000b0101141441a42494028081a40e000d6607264005842e424414140340704104258062300408100c0050103190008001a0507417203815a649070a0a507410407281e51071f036003800b05484080301c03820000307107081040403c0e81d03c0580c0101083c00c281e00300303690102c806680e08109640141c030b615040711004158101585030038407595005143c038070005c02030f0f4281081c448036140001403000d0103000c0007042d0030040c09800490550540810b161214442824806010040c83c40c4012207004601d4000040345a207000241c14079520340008541d800d0a10744010014075600042c200c0ca031501404a60a0001b10450b44540c020304868801141d0f004000c4103120146030160b1006210750b000469030008680c0001d11401c0c11900600b400039040c844 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 39680850 1250 39679600 39679613
    0x4150503180307030801030317070905060a0207090204121a01060c020108070504080a150c030b011e0903050d030e010c0509060d15080d020f1221070309020402070803090607081302010804 82
    0x681071092514040000d034403003003660081e20305060381c0c800d0701c4409400402c500180400f80040340c0000114480b00000c2c8024603005025140001c1e162048540440e20b075126030040e41c10a600c40c001c005140c012640400a00d8840050a600c42c02410a400d40c58410001c15030a161017020b8180410f00000c039104a100340226405800b10000321440c120742e610780810003d003001410030394146800c0d0920340003032190280c48107812050707407503072140003189030f0701c803100c5001c0348041d0180542e2100c0080003640034400c029101a80f40c4002a1201240440509440040701424100001001300030555500c1c03c0c261592000d240c180003544001c042e880b00050802500508000d00c1180c15038000d8030f500003910940003001e001a1207090f940581116590300035020208582a0b010400c0d140c000451980c40c1d60140c020701e00840e524505030007160491340507410036580c1c00000810400d00b40b50820100c4d811a005240149041c0341101c200c560007030303070070000904115000c00843c060004 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 39682100 1250 39680850 39680881
    0xf041a0d05070f020f1b0f040f0e030d0b031501090504060e060a02070501150f03030c0507090606030c0807081504020a090314060618010305031e07060c0302040f0b04150503 76
    0x604020001e904010780081d05040146043c140144502e6440d400211000b0502d11184004c8040701150441d459082007035850342100416009940d41901354607019082c0140d110b00071003134018503500e451486c0c02d5004d54014401c201e001303900101e01300b061010400c00041c111443d00000041549a524004c8058040d0242003081c80c8204001e0145081541e801003034583e02c81d40080043c01c0d014500c0c05045640c6114220000610b0b81c1d0400100340107049000100d88141e0036645815119902c1800b101d000f0382000c400281d4841c244034070240c000c550190002d45c0c6040009251410028090031203003100d40071030069801141d010303080c60054508101641d07200c034194290449441075151b90300e07403c451407031190001c902c001c1e21072401280820305881c0c10402071403518103141c2022388911458a6004c000c50070400404c0042032081c480d4854008056401507a40c501d000d40b010100042c541000c42c41500400c8100090304004120080b0709800d420215225500d0004803c034001 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 39683350 1250 39682100 39682117
    0xa02030c0a050c040b04091e03020708011503061a100e0f06040b0d050106050309151005060d091b1805041b03050102090108010605090907030902030309030a0501050f0a020f041a 78
    0x401c0c0d03812881049000709080c500b605041c2c0c1c0402005031802c003008103481414401901c0f0014944244400003620403041950314040d00440f105941e494003c1400c5400f001100d0400d81451a81441001058000d203c640540c005801500a1051001030710305641c505100301800940c0c444080c1c1520b40d400319411101000305003a407200e41d00c0340c1e00a0b880c0c1c4032070006c40c1100c0c42d040011540c0f81c05481682e0145030808003c1440340d8002201c0b28448002a00040070001c040c0700020359540d0f800c6c0140000200004003040b509000c0c50b00c202004040381e10a488030b0900c1c0d01c01e020488081e40d070140c1d0200055000304540d2603c2c100003050180204080b00d0f4400855008410300c1815002001d800c40d01b070343c8807161a80e98990484e0301c0d000e0503161990010ba4040071a142a00c282c00c00a043cbc0e000406481c070300254000001d24240c841002258944d454008100d01011410100d035448200303540c0661400a134890080650b1080e8002d01c01030f030151001c1f14511103012003c1c2c41c03664 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 39684600 1250 39683350 39683353
    0xf150a0b0d0207050c0d051513060513030e0f010f0309110409140d09050a3c06020f0f070b03100801090b06130e060a0b1f0e01110303070807050a02030c 67
    0x88150400c40c10103540800f1054030303940303c2c2110036105401c1003440001d400790000d01030845402d51100c2a1001c44c0043c1c00144203a0102c945240400c501d4454203004000021040840c14002d03c0c02034074102038192440e02c541200b080000b22030340c04c000d141c0c40c0344040385000245050149800a60540b072000f145c0d400070b242c94a554100030110034070450704e20454084a24110703442c1001c460891441c010503400004030b6000b0401922180f0f050808042c0c0d0301054101111041c0400740c0c40c0401c0c1d000c0440b0200190020480c00b601884480c005050042c0605212800200103940e6040b00b44225601001c001001918030800e044d4032101810040009001010107400d04245141c0280d5055110308085501101048014441c0c00c4da0000e001004d0611039440728050001440d4019401e0342002e440c8110b5a51410500148424140d40e912602229400100010849060f154010782c05078801c0040c400050380025680ea0721410a01d404c642c1c881000b14200c1c114013415214403142e = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 39685850 1250 39684600 39684607
    0x516140a0506100e0601020307031202120403030501050a050102030301140d24092d08090102100e0304080c06030408040e04020d05030c150601020a080403020402031012030c0b0606030f150a0b 84
    0xc01001082007400b40100b00740d001010f945a4481d140740c0001a00c1890141c3c0c000c008600010b0701501d045001d06404500050a10100721540042c2000454044000980d80c400601c018038120744204003030b00d07003031005605560401c1c444080f54660301d01128403840118104008000c2c07146810040023907910700c4403440000e22840e04000e803100890031204000c0c18280b40c1c1d42400b0410b0300c9003e010708080d110b03d82d000c454480301e02540c40300840a045000d0188043e041c4440760180c400a441d1038002117542e507103401c082a050580262060b44182c60400900011032040801c1c1c4046d122001c210074010b80b1a44000340980c903568030001c0490001143c0c0c003680c000d000c683c0302011451280d5a00075992240012a00e41c0100d08005010240078081400507051940c091548808003103da034103465180c105101418608460441c0021220305240d030402c02d10800c25904501d086c0c940030b0943c00c04660410103054020300420b46400000000c403070307607680c0404184c002c000e0310781c00655 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 39687100 1250 39685850 39685853
    0x90c0714030c030c071202010503060120010c05070606060201050c0f0a021504150636090203011b0306050409020a0e07020111030901090c23120109050601180b0306070516140a 77
    0x889030040c03d130304c0ba0180a600e500055646000c0c10b0343c0616a4141c0d20140766a84540054403003a41e4004050070a01c10110003a900b0710003481072070000c2803240c6405468250b58503000302500d080c2c1d0860700443e41480140142c004e4610259442c0d900020502905c0d4514503501320b01d0f00e1003a15440070030002103020300c8240164551000301d0140a1401801815169010419201e84d10109155042d00021800000d00c2c08080749003620100840e0100c2c1d080e01c0c940020342540d8941c101154840000c04140500356010721030000209420b903418400e0814a1300080d4104d00c0a108a20b148010361000401c002e1003944107400c101c0e40b440d880c1e504c0c0d08280503064001c000c0d061044402d0410440c0200b00701340724041c52122a407110240061000803c024070110550b418800c40b04c540d21444c4180c001082030004074041d1607001c50000754241444601801e072104490454025040b54060114081e4000204c1c0c0403413100b9a40703a98184120314041c10340d1071100b0416046402144074200 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 39688350 1250 39687100 39687103
    0x1b08060105100c0204060b0403060c020601050303030a0e0c06030708101203050d0b04020d090c06090e090a020d020a08070801050613090213050c0705010203010e0603152401090b030a090204060b09090c0714030c 92
    0x3041c0ca000b0102002f0200701544242e0b690300c003c1c003640350316600520019403a020380b50810386603d003552081d0340380c0502d48000f00d002c0d074005485c60408036040c1030810012003080c0c80d01e00014504090802100070040c1c1703014015101c0e440e08440450349a5034588650f4855404070390803200f01103420090744049040c1000030318010f0251000054144c0c0c4000381c2884e61000c814054141c03c00038203501c842550030081c545107510f204030b0300050811000070b022201481104003c00500c40003140791714020f800c0100ca502c52010b60303200503103016002400741e21030f052070482e0741c1c011600008598031181d21034074080c05644801000d56000100100f1110214642140101c00c260204e030b41c400310124444020031000c540c503850782d6480c10401c41d0035118203031a480c240041030401c3c0641c04d031a292500e1b1341d90b00c11505401003548650340d210450901c0e104040c001c001072126581807000303504c00992030060203071040180190100b40041440f40707414140903224000700449541c2e40d18032a815 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 39689600 1250 39688350 39688357
    0x40308071403190806030106051c1109070306050406211502090a12060506010809120711120a0219080c060c01110304050d03051015031505100c1b08060105100c0204060b 74
    0x400005060f01c0201e1040d01b4140511000c0d03910041401208502c100921041654a040182c400806000d0520b56940319401050b0044e00c00765000b03c3c0441c1071030700b80025070b01582c1c082c010009181c2c04c0740c3c10004854056000d5142c0c000105001e0001c071382800c40c003a006105e40c07254071448404001074680c52190040180920440d4144940c1c0c1d9454015200510100c0320b0f2520b54110711119404c8824076001050143d22801f02c081d04ea02e5400042410403650f00058000e51748074000d107006610740820078101c148103006e46c0d1344005080c101c0598540c0748050400e8040c1101003014200a042034020540d81d030180c01400f501c0c0d29040c1032003541c1d209110900000f0a240c00007086030b0040705064881030710750a1017850303002148a001140144044902d00d0b591035482c2740040381076503c1b41580c1c070405c5170396500c0920010003402c010001104030504050456800c00d0100404900421102e04480c0101c5043c0311100c0e040d102070f1414108284025032040ca00b49010a1401e4050060b = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 39690850 1250 39689600 39689647
    0xb100203070302120f041503020708040902250c1203020f0f030319110a2001050a060501110102120606070503041a1b010203060108011404020f03150123040308071403 73
    0x8603201d00401a5101c0c4d0760b445040ba014400503400c1005000915003222506007000e151700c1c0041c40d06980e03131903000060708942c00c507480d110380000f29117402ca034000c01c225413078001400180f68a01e032140d0303480720b0001d022b203d9400c1062603511408141802804500e46010b000030941c0c002070318100c2819269442107442e02c0001e0100f0040d203041c046c3c070b03220700603800c202d40c3e425905e01188040140c810174021450340000544035004110064420300526000d039141400209185080030005401c4102240c0d00240b90380c1305102c049031090b89400065081041515815614482070034031070304500c2980c02019a01c050280316840306403500008105d0b40380d0860311208055004004c1c1402e0340310540b04640041d90603c0180070100e01c4001044681100610051801c02e20300c064261640088401c80b28041c0900204403840d40c03c00e102c50940b0791525288003603244440c2041640e4003803404003400f0000e010480c4802c010003006507010005c41d510440c0c0c0c5480a026445150f070041421 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 39692100 1250 39690850 39690853
    0x16030506010f2d03051603050d0c0f110d021008061507030806090601021f0207020a0e040201090b07030909060315111305010e1c0309090c050a0503070c060b100203070302 75
    0x5641e00c0322000c00410784007000c3c030075a881020641c140d21201d0503120900c02003903040c0c0c000400038804000509029000412044165103141400d50900311507064440900c4061800e65000841c410b01703402c081c65110610302592900000032505072007281200a4020390320500126006401003040c80c402e000441e5a40390341040302e00085201d0069510081c08074a04001180c103038682011410b60005040c4104e0f242180242d081050b01004245043c200c16030006440b4158101400c03014040c1c0001011400c4a06050340000c02c20450340c45180501c002c04144070342014400c0b030010340203110495040c04050b44074240f110040c1c500c3c1440c0700c862450708014108801c145029200c09030380800e14000118505001034a4080d25030a0742540304a203044615030545040b202070811500950316200c04a00b0007450608544010740300c5800c0c00414400fa61049500c44112903108180f13207002541030029283c080041c10b04091400e40c00300c520700c0c242501581c000083d00b20507020741e0 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 39693350 1250 39692100 39692113
    0x3110307023c0603070309020d02040606030b01030518030307050f040509070306080c12120d060e01090603030f030603020a0504020c0f010c0f0201060609080d03020c10050a090314160b0a0608160305 87
    0x1c01100541d882c0c190300e5420079018000504840c0c0240d1120715620300203001c121000100c1d80c0010100e404a40207900825556003180885590500c00c65900404201c03aa160802039111039039540d0000030010410402d002400c03501d2451500c09850007070402801a1303903541000c0c100039000e45214000e240e014410109030101c149041d100c0e0342c04501000c000b8108080c00180d0ba003400c0e0780302021410304071781c940390006450040d00c0405402002d0800c0c00140030340c110300d4020482c041c0390700554100341c1418010310159680003005000c5402c2183d005940d84101c004007410840500f4901c151540303016058000c83c5d0f008000b01c0500c59482d8020840c494032071a0a68800d40f0a000b03100565001c0d85010b103641380a6401000307811000c0088502440c03600454034151501280c0c6c0700a0251165460400c15800c400c070689400c00b850040d900b0540079007040710361682403a102510070101c060100304010520751050014042050641d03110600207081d1903200c0d02580320468081c811507 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 39694600 1250 39693350 39693439
    0x90203070f05070b01051c05060405150603060408040e06010c020d06150b0703081b070b09100609020406020303150103110d0204050f03010504020d060213170f0105010f0b070311030702 81
    0x700e084031143c1d5488003041403140d01b0802804140c4085181440194404000100124004100d00d0744510f21610007004401401d5080c50900c40e4003400490096000301c091000041c00c800a64058484000c00b40c2c0c09540c1c0c40b0b004031080950b0307100c080c1d003040c02c0941900501074a81c02581d001403410041800080e511010002c840c440d060002d000110020082400c0c2207048460500c0c004100020f2410402c50792140a00b2110540c1c008410754040d2043c8a00000c143c05910001d141840d402c41c00c07d0300e00000a5100c3c0300080101000001d0038003000e0040c0c1c06075208000700241c0780323a0207458078004100c42009502c14000d0070300c01c85200b0075040c26450140125881903a0141800d9001e9100341e03546070280d000b0016045c5211618000881c540b507031501d2440401d00c000004101d802d81481d50182111410b03003080904991380d000600c0700001e420211001158549441c080078840405028114019160001d6015007500c079103140528000050300700010004501000350100c8 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 39695850 1250 39694600 39694607
    0x605090306090c060403060203130501020c0607030b060a08070503040507030b13050f0309010f080411060a080a0e12040b0c10050108010b030607170a0c0c120201020d0c05040b0301031407080106090203070f 90
    0x43d6031180e44400100814000079034141c024640001c185528595030740c4843e40c682c2d003a600b08045140d825482107003000742c080e03031500440003048410390f101850070910640c0105203441c0241910240070000003c60100801000103100031500010f1038105814045104100300819820686452241d140101440301002c001c49401c900305855048000d410110203a450303030001002601d40e00501c081c26215610303400014035400c90300f9910f1a0f207602e80b2550940c1120501501c40f502c680c004040480002c890500b260b040da0a4900300c540c40b0000c8900c0745203080d42d410810602581031200000344104d0541002d0b40b00b1104405840d165690320388101c550550311070000e0840004c03800800d0683c01980d0181c60303201100c0c40e020405200c903446034481e500c1d81c0070048005039400991700c5822605031180011044c1145072180c501454450f4006a600040c00301900f40c00030302030300700b01050040003144010071503a002888285c1e55100d250740250003ca404001107000c000d86a00c00610 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 39697100 1250 39695850 39695863
    0x219140301051e0402030f010f0506040e06091209031006031a07020607080a0b01050c19061a0618120d1d0a05130b0f0d0f0618020d06051e01060509030609 68
    0x40f00e440c44055108022466810094426070300f41c0224410440c41d00c0303081c011460b0343c1070403c1000c90107040c10010320040350f55020074160340d60440418400306d0800440c00201045550180507100d0004900103400c2807802c40181d80c0b181d240c02c000000f00143c10344541d03200d1203105004489640d0703185003661142021070b4107d002507000310004920203ca83e120220070310781803400c80e080c440300e11a0b503840c10810280b0b095101c100000c4200400010b401b50200c200c7c10401e811000228203000309041f409100991615184803030701c4800503440b4500345c55101038281080b83d844030070205002d00001d95a0301c810f4000a41203461f0f1680b800c160040724101c2c2c101a1200143d0403806142070b008040d45080158040024000090a50380700c1300d88410450041c1d0350300b041003c40d4540072049940070341800d050300540c02c0912001d60355a0110074805034008402003141d903141659013540f900840c0d40460b1542c284800400d660758058083c0003d04420740c00c413003490310383c003480c20307540c05c3c = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 39698350 1250 39697100 39697111
    0x6030f110f0109150203040b04080115091a0603060411190201051605040e04060b030d0518030706080105060c1203180613080a030f06050a0b030402090a060308070f03020307021914030105 82
    0x80f0292020050b041032413002c0740f14019948181d0741031549402e04e00c81554440c4e40100500d80d1246002c4051550080700c60000f0306002104005125800c8113900901c031401c046244601404000591140c0701d9400c48540d4402e407014895860b2050200502038040c3c18501c00010740c6070900080020403510200245080b1580350641454500006070100c114001d100302e81458840c0d0880341c040e10104059a80000d050300c0300c0b0389a242d001303404810791001f540c46510036800f41000700015074000341c459055400564106d503559010031007192070041c0c8401490070780030000040083e022205006402c9030303030416042e100c084e03c49683d01c0900182c2214040c18503401000a141614065404441212200c44000c42c4455a480c00640c513103401f640b0180311a2400030401c41140b4003002140d86c000c9558104001ca030f421074032220003900802500402c01c000d40207440d02450300800075906200d0b4010302c81400c1d40d2802070b210034003521a108440124900c030032051141d10341805417601c41c0 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 39699600 1250 39698350 39698357
    0xf010f060206060409020301020702090403050406110102030f04030c08070804030606030b16270503070906080f0d050414040923010f230606040b0304050c03071a031302060405030106030f110f01 85
    0x1d46881c0f041100070030000d4800c030781c95982040840010380b1559411840b070340c0aa21199100ea1801d20040c19080c0c440c00d04805030f0344100308102c2c0314501e10101540050b05031078000384403e242c1c80d04134a40d114114010f4060400032038000100803040d04610203030b0344981c2103410317640c41c2c003018408a50292aa42c2c00414003100c00560440f006040c0f541d039586035052000505591180441c0c1000700580003030103015107400c0203103e141003c100d0380003c20355070710080800c540c0c500300040c654022409051400b43c03540c3c00c00d0550340d903550000e8440c1a084200c03c40b0740401407009461000104007280c00d25400d000c0a400c801d880b91040000754007279080c0c0956100308040400c0e4441e8001407034150300c05800c0c07001142c240c0302c01c4060b502ca548140e000b04074040081c007c241c9054a03650100c607a03204031081c0400740d14004800e5941102e281c0c42d100d80042c10310710000d040f44c02550000d9805618040c400014400303140320700e200e11070060003681c0d05e99050b441440240e20801c10001c0c0030 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 39700850 1250 39699600 39699613
    0x9060102030a031109040e0f1905061902091201020a030606180e100b07030c050f0606060d050601020703050f0106050406050411040509090102071a010303120603110d020301060506070602030f010f0602 88
    0x2143c082d4002ca143e41e4484900c0c945000500000101115000502d80000e03503c403d1980c42590000c000c2000050070501030001114801d031741da40da46050081c010421904110942c103202503680d0103445041000a00c10101c642ca801540340c000d4203c40b0449002905007140010f83c103005d0303a843c10020b40c508420600c500c0c1008040c844a240180031500d10f41e91103c8001154a91900541400c500c42eaa44800f03103130742d908065140002940b03003640701d07030851014400ca40c1d50384022107201c0ca4016001184998440c070060341002a0f0b580040c2c030ba4050030b1701b030b52070203c81035000c00207440044404018042d264030900c0112032000900403000c1200300014003007417804041403a80403c1c20300005d86801d03078030ba50f903200b103200c0080c600002c139200500520400d40c200c07004200c00d2440c0c42c000c10140d0710755214135843c254401c0b40f550041c40c540120009648081d00201c0c040c0101034100c981d1100781e440c1040081d03000b1500340079804030780c00c00402c22420201d100c03400c441155008100 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 39702100 1250 39700850 39700867
    0xa11090708011404150803070303020c0709020301120308090c0901030501020319020c152205061509061305060105042402010b0a030b0705130909030e01020c0109121502040305160f050906010203 85
    0x1c05c00794042900300d01c000d60b000101d1301d4040004000d10f500c44d550240c0c4444800c00e90600d414101d820000c1c1f054014001403100092107102c0c440002e030103242030411600c5600b0101c0c10f0240200b072450300302034090004800d00c20150019070040c0c1154801040e014210300425049015114280f12207410800c1e20926022034050f8690700280d130300008152401e8552120030960300900ca04640d243c10100400ca040107007014109403050007942e0800c0d6516041c000940c1c0d00680c4074005c0c0d039682d9124003081c8183d100f04150342c00b80c000d4490f080000184528600c84262828800d03100540c242000303010541001d8030350604407984030010700015205d20f0b030266081d030000d0401c0385a001c640d030030001700c50240c2d0040800140c080e032039000d040880200020700f858001c0301c1070341c148801403100f007006404074030b044070400da04404084085503d082c08400039101d942d0004c2c243d4031901045064182c0c2d1352419a0480b24400b2200c0d64441e680c5c01481103080e000c071081400358101740a40340 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 39703350 1250 39702100 39702109
    0xb0403080307111b03061501081611010903050403020a0803070c03030302030a020d0207060504020301060e0903040902161b1e06080f041b1401030f110304140f0a110907080114 77
    0x641007840c50625814203c84000040e01d000c403041d24030102412042d02c0c0b001c1d14101441403d821144502c00040303000c0481002034502080a400c4034103400ca8a102118a140318411000d00c40b03510f44000e000002c0f05050081564005001c242d00c16800400002030182c0700008643d002a446529048407900c2c50701c0c260b0081d0401072400031641d40070011292000010f100404405104010004450800e070050508560301b40d040b00400004080c10701c44050000400d48040380c07280c00015039100901d000d0300880800006006121402202080245a5503a070004013940d0000b2808200c0305110160085031014500c0780340081844c40f000329206541c0140c81d03540c000c2c0910b120036282c1d0b001404020343e00300b05500039140d9042e00c40c101411580d05005525203074040000c18440c0d0210000030a01621010b400203000241204042d21110001c1c40004000806403050b03903802d1075a4101881102001d800592040c60020300042d042c2d03001b400b105040e207282c85c890441c1101100c0611 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 39704600 1250 39703350 39703357
    0x9081507020a0b090a02030303241009140a0b040b030106111b01080403021c03051b07050316020114040303020d110d08010e06010203040b0408070501110d02100b04021c050f07090b040308 82
    0x2403a1a015005030301e170241e10104000c1d03004900c0d8800c110002c2060407600407884203081e18640c424140c00314503003100e0382c0c1718521000352140120074503440d40c42400041c1112039190b00071481407001142c00508604008082c50485099803540c4003005101101162610340b501c0c41c0000800c2d241c2100420b030f500c10081658418400e004440c1ca2031240e10351a28081062402040080e8607032040202079444604285940241102101d0612860380d5502c2d8a134005d60400340f10112400d404181568802c4508644011000c1c030100da9454403030400039164031801c548200424940fa500d542402400184655124210758540c0d04907400c0c03600048014602030304842c1148005c0c0310100c1c280d0207100c0140000d0180e10b000344801890040007411511208440c1c0710a0303004440800c41c03c540104803680000340b01100028100d50740d400042c000e000c2d1003030302450304610b5105c10038401c0703281e40418060016042058502d6580e031302300f1160303841c0c2070007401c03400d102c180820400650070700f001c1c = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 39705850 1250 39704600 39704611
    0x5010b010305090a1a1306050a0516020703020d1b1205030405090f010503030a0c0501110a08010e07020d02030a050309070b0708030f010e15060d06030b040c0f0e01150516060c09081507020a0b 84
    0xb1507054400c91f00c4440c10b5074801d0340c124412503034480511241c1021002c00c07030210141400a440d0140c91a000034440e40d110031000f0300b5030891004201c51440c00c204110024249250340014090b125082290340c0381c0041c0a00d500074001c0c00007069a04544044990403100b00400071460700462071703804c40d05110300300700445456484d05101e0316031412b84405016002035039078032856150301d0b04640625881d0054017010030364114541c40f07402e991740030049440b06409418050764a840b1480000e1504255900026030990042031140030001e80c0360065020380c0e40d10400c2d1416980316100d003003030380000351004140b803504d4800400c9141081b02c060704000c2c1c1c0d0020300180b4a40c1da9200d440c044c3c0001c81c0c0840710282110300502504180994100207007001e04686000d543c1000401030162044054540600c0804600e911070b802c5402c41070300a103a40501d040c81960341c1c8080141454080d4050241240a43c4111011110348149180c3c80b0b003549500030444c103e0a5101c80700171640c040c0c0b2 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 39707100 1250 39705850 39705871
    0x20f220b0301090f0f0c0903120908011e051e0a2304050303070813120e131d0d020102120a151a03180f070302040f0609050405010b010305090a1a 64
    0x3512280e4001840c001d1400d40030200d80d6006180e040012154082c0c0d848840d42d10b00084019944d40c880c10b03010235030b17610074044c0d0010f800103902a21a145c0913400456950b08294201c100e0400044185000701c12009050000791035810381d00404000c0d90030111041001c81001513803200c01030300410204043c2030160701041007000c0701034001700d00458099615030700000911000943c00411b441c0d019041e161000071003d03496603584011071383e41c0c21400c100400c404e00503206940e1815020054042190b0411880b003131420f10741c90010003138038a58880d02500d02402c078140e0060003250000619841281c1d0169141400700005000d91846001c2c1d440320784802040780e908006126000e1040a0000d503140c0c030b4907220041288507540124411900309681412048800007009400d40390b04a40104201e94081940340003031078a5405034580e1030a08050100313000e810342c451141c4800a90b001d010980e500c4035565034400903903000906070301e10b5003460f01145401c00c49450304031040d01ca = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 39708350 1250 39707100 39707167
    0x2030d030213030618121b0303020d0b060d0605090a02070b0109020d090c0b122214240604140f010311010c0b01091e0e0d05070c03020d0b04060609020f 67
    0x122148200d4202003000d0303140020125a05c024000c41810803e6075010038581451000618085460b10b107548134401001c7c9600812100040c5116801508581e0f07030184c0129240c240c890b8500340902007a10070140140010b40c045014881c49008403421240c00c01625003507039207814502802580700c1e120a40390250340f5814400040c40c6210000014401d244a00da21917820084000c00c2d20030203407005800012820481e11a01081c40300002881e0300b0042e1460030b0709104489600745488070100c42110000e100d2100921100a1011401101e044d5001c03c11f24681d403001200e50b0800b9224240369a008000403c00980c000d9801a101d20041c5401d0241d00c9150f5a110034007902a00070716072403512944ca19010108440c80c0b46880b05c00e2040c1845202d60014a180d210a02085407800b040b6000507480d040c040c5003e080e100450f070182c074461b002029410001c0b402c410640d0210760140c14043d00040541003030003078500c030100c81018140392000b245514900c40034210a81445a4802e8 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 39709600 1250 39708350 39708353
    0x6090d21020c060714160815101404020d09060626060403020c060d060f09020414010903030813050102090a1e1e061d040516030c02060c04050925020703030e0d02030d03021303 77
    0x3140030040000e80f00500c4901c1188034070b6845804c0052424509c00d05c82e540800103440e01e160000305146080e500103a54200b1614440064440391401070151340c08c0c04000210a5280caa0840705e1151010038156003403496856591204030581d0094011307880405002003a26101000302010700b240c4100050169581c540307400718019660100e0405076000c10200728608020041541031b0100346403a5414038110755019101500260a00c185020700c078103401c1c100203095044850651000b888941c2c041d5071a40440f285103c44034840c45400800e403c0000c80014441002e00d2900404642c184064141101116407007031a0f103880e4140d400b500c0e11000c040e111031103154080c00241e404824a416140002340903980c0144e02c0500b1584444108070740106058143e905680044802860948a9801c00c102c03201844000c8100010946159225181c0001e0030b10b0407a8865196030b000c4001d48401c2100803404a071020750141c01c00340f01c01c90514420fa00524883c0a60142c032141103882c3d = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 39710850 1250 39709600 39709633
    0x1a090408090d0c0f0303080f0702070e0606070b0c0315030f07060e01030b10020a0c0609060e0f060708120402030c0a030f0b0a0e0a08070b0c0406120b06090d21020c060714 75
    0xa0b134061110610035220610905502c00071880c0e120200300a02c031380c24180403078002e60340c112074400d031181d4014080c00f16096584030784c1261400ca07003044241e844e6003054007405800360b10075100c107007550ba04000c0c901414100811005400402a000703000c00b1450514181c1d0300417042401c25040550751000700d2403d0fa02d0300200c0300c21044507802402038840b00e16080b00a000c0c5500031070705124125008100c515403002c0e10b860124010340f903410a000c24030b00441c40138095400000c0c0074000115807020030188282c817151003103000300d0032144800014002e10001c00e20030f0001503c0741101c02c0345000403078841310125800a1058100051361000313542d1043c188110203600700c9004e80700281d5002031040550b07032141c010203680451490280381c000c020303044c1691750b8031402181d9196040c84d095541c83c0e4050300d150100241042e00c1642070303480c0c040c0800814094040c20b40303400d0104240742d144000352148006002130001841c3c011151a98900c240c044621a46144500c2200c410410a03 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 39712100 1250 39710850 39710873
    0xf0303060b07050619050105031f020d0219090501080103030c02091b0c0d1101050f060112020904060603090b0709050105030114030a02061305090c0c030403060c020f0a0c05041a090408090d 83
    0x1803c00381c103060904800c0c04c2a000f004000d813203140c0e400d200050046503000300d01c080503100f030038100f00308507a911440c48011340070703148088642a10100b001c030b040040084c0c1201130500300343e4900342c50750313102c00040d00d441e1001e010180005408821007001030401588141d0041c00c03180855010800d9048803400715844605603501c03c0d041030034402e40842c4c11000344803614003560006c1c0218680703101e6980740aa0000c000c1410010201960145503040d0745c121200c82001520034032100c0c2e110200a03001d45034104c2d04076030020150001070b030220310810114059540594900d4916460943c692494040704600d20383e2500a04922038010ba40d080b000f8075100c5a05064243c0c21450a0200301c4c00380301c0108101188407042018000000000c403c039030551f03034411400101d0300b01c441003c80c58025103103011b002901c80e1045503018421080c6203001200c80450303080c8404000b03840810315848a1f040304d1508403c01c2c4020a00240f4083c01400e011f180140051840c040140c0b40d0b65407400 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 39713350 1250 39712100 39712103
    0x10f08210720010e0a050904080f04090501060503070f02010e06010b090103020c190203070f1401030c0c12080a050a0e0a0807020303090603180601151b0318081b03070b04030f0303060b07 82
    0x2c580a5610a095800c00500c640b03040085031880200c134544400f0440c01d00c0000c1004100420000d10206846904e00c141e40140c45460030421856031901e13030141c41a0300949510010851015070110618414050582d0000115014290b02d9207010b0f8081200c2c2c000d404a42d0505d41c00340120710300e480d4200030960100c00035004005801e02280145420020340340c125a401c40007004003405030709075000c04000203400a2030000f99100c1015003c50f410041d00340010720420038000011445503102d42e0a50203445141010400c6484000c0b03142d08450081c61500d2054104c0000784011a002a020308400c900140540c1d26100714900012030390b60080310140c0d04042620000c400c806003c220f231a000d000d030403c9044442c261004050104c40c0449066400d2149030700c00807040610440c1d688102440780000740000a85514540d40c4500b02d03c1d001c0c0c518001e81e10480551450700140c01011129000da01c1860181140c035042c04c5034001c0b00c8281c09258880c030000800c0401e1000401e12903 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 39714600 1250 39713350 39713393
    0x2061e07020406060203090312030402060403120c03030e010b0f0105030a020c01020307050c120708070602130e0a020405010e09060a031511070b06010e0a030206091e0307080114010f082107 83
    0x11040d520422044916941104085500501051403281c030009100643c1000724080c44d0b4582d912840043e01074442d9400c010401d04021080d238107120340182100c07151a1103500c0a0212250341c46070b031422200744010444d8001040d4400c0702076035004400458114038015400f41c07803e6540c218079030980c0d000780d880c440004d1001494803544802400804000a01c11060600e0310010ba218041c440c05541d02c082c1c01c01d540001c40c06001c860280540005103a8072400500c1840d089904000a400511896000c80e0000c5441020780c9080741d030342440b400001305404100e07411611481d9212140d69180c0b0003640d80c940c00c0d82050402040503011135482070f90452010b1511000040c1200c09441d4510b000724075400040c001696100c080e45c500000545200222090100340c50380f07000d980b61183c3d03404d0302a120010a0108040d0801d100b00310111404032056641c504031854010554031455249800501c01000c0b0904031701d011144846151803aa41010403503101c0c1069172a83c20640c040300c = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 39715850 1250 39714600 39714607
    0x1060305011404030206070203130b090121061406040e070513030c031203060e04020d140c0901030503030103030e15091905030d171806040b072003090103050a06080a020d02061e 78
    0x101541000b6865020040384060750800140b540d08a0040499001c0c2d010bd0f0180425a03840903485000a030410400700120790b43c0708840c481c102c9008212034010b411500a17510308501c00c60501e403040b9411500c280342c1c58030b4255100032040766a50486022403020580b910000004101c0700c211078405107000e41c1b11784540060500c070240c200d0300c0a61100131020b603a440ac110141c5d03a90f403c62010990003a41d03d000010062800c0c60400081441ca10b61010b0840c0022083c03280000256050b24400d4544903c40c2c440c4908022494218044182e50460100501035250801c0700d5004e80c0c501040e155190a02d4541000a05001e010560080043d515502c0c05e0000c0c100c40c160903130441d1a500c4900700d8076515299040d2503410042c006040c0551040100d08214481c80000c100c030602100007101c07200c816442c541d100e51040d101140024100703800b0810501e1288105c50441d001c40004203c0c03540709900f480708440da23568090364841024404803012400700030034101a070340002522940d = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 39717100 1250 39715850 39715853
    0x60312080a14010e0417090307080708060c0403020a1403030403020d0506040303050c04060f0e13020708041d0f04030f020a0501060602011e020c061801180b0106171b0c01060305011404 81
    0x4aa26002c551091a9902d000401c00c00004924550700309402c140300814511440d007140c400c0d40b1441000980620a42c54001900394020074207038241ca0024058803e207171500c3c11044094000c5010180d40721066180401a40070041000f0195030300c042e06407410180c1e2900040c641040c007000c1074680303401c100100010543e00d4800c9503030021000c6d420a0500f0f081100c004c04852009005005108020406055566668100041c1c284020500350b5a84201c0e10f00602240c000d0b1103402810111041d109203801a03040e480d42c820100042903816695403514101c501d80001c040d810150701440181e00b02040d0203008450282c1070030340020966140d984080035128150300c14000382e083c818451901d941c0008035511b504500070303540203070b001618151078500400419800f00c41042000b000c032070412400d1101ca5040340d011b44c40c2c400e103004031241e41c4a00c0d0407003192640100e100a580011100b040803018042d141242c200015180b5282d903551400c40d183c504180c8107200e40d0700700300030 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 39718350 1250 39717100 39717121
    0x60507031a0a0e16030e0a03090305120c031608070209090c0a0501080f0103030c03021203100906060f09030602030a0213081e0f060118230405190b0a090606031208 72
    0x25101001e0310442c0005240220300c00c40d0240280011042d400400241520302c1e209801c0601807003c400306442e420403085c50081e210f5140b031b11048074640030b0418648003080c481c00a561014100402662411540750b000e10418051500101c490510901011001d40c4400b404a48a50640d0300201024518a004c00c072804880d5400035041000301c90400989032482b8404a0459505090a40e0505180d14041c0d0a00300081c0d2507500110380031080000e4046020982421a01880402c03c0041d4503000100ea1042c001e0b11480003003040410104001032042c1e000355417005040200600300041901041554174103644610200c1e4455000b400c140f403a1281d0f03a074030441442004140030020303651382c0e50b00d0b11030510411820110008240b80492700d1504684807214240440300005180504500f43c5448180c806035414800c4c82a9101260040c07a1440602500300400c805107aa403500040042c0604000c200e0308651241c4000000030701107240001151110b48034030081303250490240 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 39719600 1250 39718350 39718391
    0x604110c0a12031a0a0506030403020111030a02071b050619090f06082d010b0c030d05010608070801090e1902130905060421080a0c020f0613031103040501021c090306050703 76
    0xc14006070340c1316020346250780300c2544800b05c82e82501c590351030b9170316401c003130740100040252686407120000030016850a04e43c020b00380d503441a44c0c6c0c3c40d00100000140801e01d0164000e140d002032040221000000c06000341f02d101010619000c0102e0b522004e00307090032203181c0e010303202264181d002d01548440e100071001c50065141d00c10f449540b84e8440903110040180300b218444400001c40c00c082d828280110791590744070fa403052080d965510750040c8200c030100c41d2500046d52000001c2148030180c010f124a812030600148411180032914803042d030b840040803a800307230003410509182407507800340d24400c80c0200c0142c0030903e464104990307100182c0f5103504080c440c401100c0350382030304800750302d8015107800c400040280f11918203074540410118103400b00d1050408001d2100c00103485644003610a517200c0d8036540490045660700d0149000c0e040c05a0040b1803ca6500b0b00c01224031040c010309441c0c01e042c0240e0b203460f01000c031202070707405034002a120904c6000b84000301d0004d = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 39720850 1250 39719600 39719621
    0x7060b040b150f0904060f0302120a0302030306010f020a050a0303020a0206070f08040b0406090f050d27060f0c1401061401080f010e10030506091b01090b030604110c0a1203 76
    0x1801180a03403800209003120080d03400c106480b0100e8480e15050306241034841c0d55034058410001c0a48611075001e582d516480704034411503804c461002804804111410302c46c1c0d240e0011411501c40c00015034900030f03640045021441005080b03408941e0420a00c0c40742d030b00a480040c0c6e01c440b0018000c7c140000108188280814044107030003203980500c03d107a11541107a03103010b0300e845502c1d000300640303500f540c0a040c041c540d4600c0c2c400e0210115450100e8195911800e1030000c041d0008040c002e5180c00b4520318401580302040440d002d8820b0b895400341510f001c00c100085990703041380c0c40c81c0100110103981c1d900c1e601440255101e85a0b050341d14070900304402c10789003041c0d402d5100030050280001104580780856a0801c4e15003209025551102c00c0d40c20306d00c0c24900f981c0d602d8801c18256440c004440040c0001035001d81d85c0c030000e0b62054901c10b4507540d110014400079000046506078686410013454002c6035091100303051291041144202c040448070f002010348505481c03 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 39722100 1250 39720850 39720859
    0xe210f0613060b0627032104090905010b0303070c050f090c0d0e01110a0201051504140f06010c0605011d070905010203070609020613060801030c0f032409080a030207060b 75
    0x34881d521485005010059a00c1500810700b001040e004c0fa029000d02021059a81c481c2c0e0030140c1c1c200c0c03292050502001c410340845606440d00b4075204207914407400708806404080100340300d039901e190855004540a080007203806c01541c2c02207407850340000400d4800420840043c4010300c6c2243e410041c00400b2a1412100d0601042e40503031840341d6000210110f556044114900c2400e40013660458403114000d03072070701140704020f8045c0204a511b40c0360f40c0001c804040e000d281c5480740d02c42c507540c00503030350350f055480c0511032013001c1010300000d0500030340c1050880058440c0c0a114040c18109044404031240018202c1c0c41c90400741c82c074002c0c00321500b014000350341d000040e600a6900031002040c0348540d80041071451181c0f0b03074030301b10710f48091a000c640c0035004403240341203074400c09221400a40c1c07000b03150b160014a0200404400312010349220b4140e4298140031003402c401000200c2030403070760f100d068a50105107400003098000c2803003814008030788101ca06801c82544d = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 39723350 1250 39722100 39722113
    0x103050402010503010618080601060302040905010b0c0c2106010b07060b0f03061b0f03010b03010315090503040512030c1f0c02010615030213180f0506031605040c0e210f 75
    0x1e0000c0d181d80014001c1104001d041c0c1c1c00d40c1c0e160200c0714004c50040c00d80c1c0d8141d512550311118001d01035400750013186120f40c20301e0300008181c0c190f0400c80d48a10282c00140000000c100100041d409010100e051001c41800400c1c9450b07500748105030007015860020355403111545004130584240c0c03188644164042c050b0781101e40c078081012a0f1007122229110813040c040c800408007400340488003802007402100109059400304010742c180d900641c4c000d08815652540f00e0706680504400510a40040c04104042e00303016085036426440c10081e2814948103410306031070b06044481c1c685240403130500842c1e0340403561051070000700300c91000303101c0d250510340007100440c0c88200350420550300080c00b200f0754800e14949400b926118a4860a1449058090000e448440a4125501c0c68400826414035000038074000c0e2031180c0030540c4007581381400700002022070781c1d40602400200758000445645020100c401e202401c6240c0304280b03020040b2a24003400724541143d150301c00d0 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 39724600 1250 39723350 39723353
    0x30506010810170f01090b0108060c130b030402130c0806010e060c03070b06120d0203070b0a0b0306040303090203011112160c030206041b03080a110f01050709121b0e0906010501030504 81
    0xd2030090aa0301a4032096003801c3d14420766903c1e012004440c901a0351800c480c410803c42d009190700c0c121400c000c101c815944070009043c200c0d120301044606984944003040050718001d10203168094001807180b1001e030728041e2204150340518030325000142c0d015017001030946c0c1104019168001c26500103007042900c981035542c03440f4481020708030007a4140001d00c10341c0d4400141611079071410584501d90a207801c040c1da43d030041001140c801100200040e4260300e54800c082001e00014002c0c20300c5d44480e18180c00030000c414003a60076540380c090445588080d44003c2000001400c1ca05215142c8bc1060504071404c44803000100300c0080c0b582c9c80400c0d40040c6e45030708150000840d503010070450070a2a03903510580d200030080e40c0c010031b41c1214640c0080040701e2404048056035003a020b1209814202c80c8121081700c00b0400801d002c2c002d01c00413200c1c249883d48034400641180721007001040315000607a00c40000f2040038400c001d02408107101d5940105030030708041c04103040c02e = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 39725850 1250 39724600 39724621
    0x30f080a030e070513200406020604060b0609010c0b0a11030c070501180804050613030b0a0b100f0f030c0e060301030f1202030a14072604140303040807060f1806030605010305060108 80
    0x10b0b12031200c400d9448002d11143d0310039400b020040f1103000786e421640e840e0340b400041d45880b4119800d8814602e0a0710700200b0b410400d084645408051395850500c6031159601115444050321189240355100e000d0103c0c12112401036000d03c540c5100303107803519000e1900c10b003581c42441c0c5080c91202c03e00801d000140b1018283d034140c410440e007140e1100769820a05d85002c48540c00039049108000c203000100382d1a0b40400482d00050700c3d045180041c0020640d20380003c141404006055800c824550501c43d070310045c04ca0300c00d07240804a80c545800001d0403904203130401e642d05c03132500743c44008010700045070b00d03400c0c2c00c0740c00550300306101084043e00003000303103039105a014000108141046170280c0f100d06415801c103c1140d101054188108042c0c010380120a644c64050004607100c2c9000400d440840b605080201803440c02c116046400c5242600300c1002d000d21443e0b651482d5000f4912123002d48446d40e00069202d1400b4001010750300301030941810300c480e440074071903000360 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 39727100 1250 39725850 39725869
    0x708120406030209060d0c0c0204060509040b060402090105070b09030c160605071b080105191808030c0711030601030b0403021615030c0210060e010e090c01021e07030f080a030e0705 80
    0x40d802d0041e00c0da40008007180c2c0d81c0c4104100502854500300d015412a6040070b0598000c038029102006603036115420700c00301000a80b0080d200d101c0750f000060152405800500a0b000d0626000f401c01740f055a61103e82a004e50386088250004105100120010008611321040071802c0880c018508030000d00303588655213000e0403204031140d90b0100e002c44803400b40f0040c5201402003045180c015512449008400c10008505082001d00d0101c040364240b4481550f070444840c42c0346803640030364820320344e1040400b115149504a460705103545c0a0160034021806020b0081c92407400e483e009040c4038501c0c07c105003098034010305001103a0b001c843d200249003d81030000345c101e954103040c1e01e030181094284c85514200b00011488102c9010540d040b00c00c070003068001c50f10f50704038480d290140144c0303450042e4001c0901c50102102da84014005040c00410743c0c10341d0f52a601d6003003004c1d2803c3c0c410b84070f84000090350884a80d051140401165400c2c001d4510107003840e0010300b00301c4c0c = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 39728350 1250 39727100 39727109
    0x1a030307030801090b030a0f15060e0a020a0e062517030906090114070f0302070c0807060f0e0303040b2b0c0302090f0916030f061815060903050319120501140307081204 74
    0xc0d02d04071000f8844083cae0200001e0802a40e080c0300b0340c03421101060196004040d030344009668160364a909040c00801c1d0303128150b01004614100f80703c102007400500621100ba01d00c0c082c005a15102111a080118046c40c500f40c0506050b142c101d89490071340321854166140307a40c04504001000354000254002a41140303005641c80d14141440301c14401c0e80e0300724040134050080005480d680204a40c0c8810300c594480e036145042900400d0f40720b0041d48103641d074502013003002c200c46003400302860a01d0a110000304807407a020b048036408036500d85040c00003203640040e0703203515860300301c141c6a030b004811211103409207080c0aa00101c2e86c144c0d610031090640306c00e20208900c11640203400070f0b11207003084220703c0800d86ca000c4054003080701b071014030031040d50010540e00d1060541c02d040e00d800400951610702d0140c04a440c10080a11102c100000400807182107203960203440d00801e0b03601000303006507001500b01410006180d0010810790711070300c41e41d99032902000c151030445 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 39729600 1250 39728350 39728363
    0x1020309060c0c03070b310501140403050106090204090509010903020a020f150c03190507050c010810030206030405011a03030901020a0b0912040608011a09060d1a030307030801090b030a0f 83
    0x1540e402c10b0080c50008103442c6903030715008010000c80c0180c590000740001610301050107514520140701c14405a0f0040041a581c240f2004c052015502462412140e10060320f000d5203050354a445072800c603622074020309000e0b50006010411709442c0e000d0030f0342105001c1c00070000f04c0055900a036032214810303c001d004009000d59a0b171a0b039030b504180101000341c819542d5560803010074041c1c9a03448250381410521b00e400443d11030700d02c076009030341402d0361000c01014408094001540d060500901140c00c0c900700f200044016210032001c0d43c0110701c80d8001049078500031030101b841b4160506224081c1c1c1c02484503c603180e1780002e2060b074158011301031703002c01d45424030024100303ea217082e04141000300140000b04e5960240049049a040300d0141001c855003614100d1144910525180d1041d01849141499010341d031250f0210303c83c040e6403114600036040400d0458104072400e801107814500104081a05400756030003541c003c4019080e88102541c52442d51150031a020384003 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 39730850 1250 39729600 39729607
    0x10c120e03070308060a1d1801060501021e01020412061a04110f03040204021603080901110301240306080706050c060604050c031306020705070f030218010b0307110309060304050c0909030301050102030906 90
    0x1c503215000148045c0610800803440d01c26910f01c4002501c0023035032038044014081ca40003c0320813040c420072060305c074141e001c2c24403400d003050241c2e483d0400c2180c0f031126540c00c10000440007500e024065105214050100d960828145c540304c0c0640e0b5460480d028600b0074020b003100451100494009101280e040e6132661103a00101e0000d004212540c12510780902041c41415001000c0e2486010420000c0c08000d00620000034207000a01c6243c840c0c100170303010304e054002c084011214038103075442c00007081551040703003a19120560340120081480041d135855003110030700150390703c00e0059805200300e003402414131546100080c07050b9481e2030140e108504111041e0101c603481608482241c4602e41c82e048030340e141c01102e01c022807103080701d1000c89900c0062026071034101c603202c1038214290751342c000b0300351000308840404130f44a000403c0700048030f50f1040055800740740100014a40561042c090218004014240b800d00b64018001040107a80c00002c840d1880400c0e01c031180c6 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 39732100 1250 39730850 39730861
    0x50106030206070303060503070b0903030d0903031b09060207060206130f0f0c0b0a09140904120c0206070803060405060d0b0c0715091101030506181302060f0a02010c120e03070308 79
    0x41455800c000d41c400703000180e220030305600d90040b0060301c50031400d0f910750aa440f0036200c0244140030358190543c005200c1580031101a9220a003894003e0401192080c180342440304a1280c5600e00000f26056aa041c48040c0c0d0400000f030107087c00b8001800e1a003851030301680c11010380480104061017280d400020040346c02503030820a54015100c0070016110403a0b11501d821800f151000074414400000e0007195694880d0100103010f449141691a90b440e8214480341b038040351014002c045120320016210329004000c81402105007540303030b003400f00030802952400b07042180310314020380c0607002080384000c1454002081d040042c3ea145024074080041c503041004007000c941c90020902c0a00c0543d400b080c008030000d81e010400c6507180e508000d08450b040d841d51542d840100c000840400d2034660412105000901c058100350b4440c003075039002e500200c4034000603511a040030f0055071f00300724103103002d804100040c0b20b07003088040c200f603680c0a1510040c040001c1e0b80301042 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 39733350 1250 39732100 39732103
    0x20a08041e05100203120f011d0408040b1606050601110325060c11280201031d0607020a03020c010305190b01090302030d09030c05060408060c0703020312040b1617010603020705 78
    0xb01005440c110b90340000c00320207900ca42029110740502422000025400c2071403502543c1a14a651850b03200404090400780d10040002c00864520130200305c04140030621801614038030040318a040c030300d140c1a20b4801c0540350081c1800d81800340c42040416820004000d072110000f51088500b500510210050494920b00c000505003500c0c010360011241e41c0921000c3c50205994200d402c0a030020354036223040c146080c490312400d03408a40d883d0040d0311980100c551480b4101805804001000c0f80d242007010a4a006025a009802d15420582c040c01580c40e605002d090420003840c011081c0c0c000940c05840a00c01655554203400041e80030380070700c01c0a19006411603d02d0484510043c0101d000750000341c481800320f010016592401f001200e003a1004c040141049845815100d10903800101c070840a5000500c1407007501c0e03610649451041d80030b10014401c50030104011000c840031031400c4410003216020340340280000d415018110768480c540165070302c00c1c81c240305 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 39734600 1250 39733350 39733409
    0xa11030a0603110307030507061404090f0c0206070c0201090603050603100518070f03110105031b0c030d050f0f04030e0118150905060301030309120f020306091c020a0804 75
    0x40004140120038800d40c448580c1c0300c0030a0760310440409500d05500400c15580d01c01c05d220003040c5502ca0038050000c07512071a4140503a1001b941018241034442b541c0d60306841d2200b04400c00c0c80c2e80d41c2c42805c011503042006035004a040c0c200403e5207242500020403800640c0103e0042c10b0b25400450a00d03141004098422090440700300100c0c10302245181c2600c0f0003019044244c0304140d00800c0c000070f00074541084035840030002006940200044d2500c0c5c02c005c08908000c1e03003c02400d00c0102402009164002106001c0c60380d0399840e0392580101c41e000b47c040c40d0520b0790380040100780d0114180c16174000c0d0b0141411150900d0540048460425940c038502c1068050100011b04a103078440d1004001f029440e9110310a4540c0b0900240340001d10010b0001000900100403040b141644044154014880301e05200705a4010a14044007951075144550100d1042541d510a00080e13113240b143d0307880030304181000c9442e49030300c2e030040780904922500220804ea9484c420b21a52 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 39735850 1250 39734600 39734621
    0xa0507080906160b180c011d0103020c10060e0a0209032a04020a03050103120804170306030a020d050c0112060f0311030c03150a050a02031009021c18051c050703080a 73
    0x200d0360f1054191404114001041d503c2c8940c0c0316841c0b9030f0750402c18000c101002c00c0c00043e99161444810109501e90300e10004c44a1414503508000c14070319440c061114440c5034130480004501e0f540b070146a04040e50004140100d910f10520010405580204005040c554402c0164400c07411080c0108c0040240d280c10079446440014803e00c19501508050704990180b00142401c0c0c440940681c4d02c107004403002031040f204588500c1904c00300c200910740110014007100c01e0940b03194040f50f040d010305481034500380d0003099003100f550303440b03c80c6d412450000071081c003840f8a80031a07003669640a01008048400079042030b5115202044041a6001c1c01002c651480c00000c20070341049400b500c21396000d90810340092401c1100e8000c582c0510390b41001e4000003032410b44000d00a42001501e075140c03a8580c00c0c0410141414015a040001525222410034a81d494624680100c11806c0001c0c40c10204014030903c3d08481600c03030b43d98140c2004440e640e00c0300c01c0c1c000200220600e = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 39737100 1250 39735850 39735877
    0x50406090603020f03010504050d180b0304030806040b041a040c050c011802090c04120201121401170c03060402131107060903020a06060918260c03070b0c0a0507080906 74
    0x500060008954121400b268000c0e50b070304010490320703000e1500703a4108940250140d0b001401170081203108403078503c0400740300c0500169068541d004052141d000b42ca00307800240480301408402d00d0144035030100389008450812900201104031083c0c0900303010564495a990026040341a0240045941c9003451000070008142d82c20020030b05811070703010a070701400c24100095416141102120b0070349140c0d0000c5c0b034028545600450300301501d403080d80b9203507480300d103d01250443c2c14005070180618507c01c40d07a102100100c1d61904a24243ca03904c00c0d0701c41400d000168480504800c1040401003000c5050380303646100d45da161240b603000a08030391600d0709900501d6804135180701d0052090605000c003035500c0407840240e401040c401c681e03001411410000255205039901c0c907004074444580303210300421800d0002d64011b40d0840d12030742c000080900421102d41c0480740c1c0324500385d07503850500681d060014524098010001c080d451300150818003595130310159003010150a0 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 39738350 1250 39737100 39737111
    0x5071a071b0506180321090c061c0f110a0207140604060e210303090a02090109050402010f0804110a03030509041103010f12061b030b040f02031302010c17040803070507050a06050702090406060504 86
    0x150380101424086a43c1f00c458042e204107040e9914120048642608008064101e4100c181c00300324000c2c42ca1443c40c0e05207503030f101c00c820389202c3c0b0100034051110254005d091420714011031840c40d00380108814bc032a0b081040240665a000030142e00341d56001e07500c244260459030604410548070b022001064400030003044580f400004243d444036209940e032880a0361f80b40c81440a0b079800ba40d00030301040b903002148801c9442803594680c843d02410907000c0e200301c4030b008100d4807049a00f007a400103074000b4200307000c0d00701805103021240c50359a00c54510744c034040c65005400950300403a20801000100d60042c004981c10048a04200795007441201c0035681d07028000704001e80000d0300550420503007440c00b03041c03031007034034482e040c0c0c102c01c4108042c8070790044035030482c08038040340c10740c040307400580f90002008041d1019020358002180e40b440c070380c10500e185c4202580003511030320b00d05400b8402c103031b17100c000e46010942c1501d0000550f1240c4c80c14a000e0306c01034100c0c5400c2840d00 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 39739600 1250 39738350 39738397
    0xe04020903100e07090e07090b0f0a0b030402040b06041706090d092705010b0304021c020604050d0204020f03040809010215160c3017010506071205071a071b05061803 73
    0x3203101c83c1111984102000027441c0b40301401151207203800050760040141000308042108a402554401c1c80284001507484032600016482c0d00b007170700b2128041034900030340c0998186c00c0003901d400c000c441c00200302c801401c0000600d010494011614000c07c6448402800c2c0e0100c0c07401c0d80c14a800071814041585c654103840d850750801ca130240d105030850304003544403450111110070042c1e0094441840c0c18109014046602185030003241c20a40c00c01a0410010a400c00b46004920450b101c660710a0780d0381c0024602107003038000e50824016042880a5400f02d40100510002c003814206100b41442c100414003511030310382008411300b103400740020010000701c800000c050710b848118610002000040291200f401400d401c40010403448010036050000041e4003d82c0b450031503c0d2802c0c40c1d4400c002010340e00c1505100030071903003c0c8100980c100c4c40e007441e83c034040c00a4181c03820300341c6c480c20b42d500310181109117241c10903815a80078940c14011680c410494900300c15842000 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 39740850 1250 39739600 39739603
    0x409050609010504090312020a0903050304090501090b060a020d030f020c0f070305060c0f0d0e0a0c0306151401020307020d03020c03120409180302030d0e01020409090803070e04020903100e07090e 86
    0xc403092846030380c1c50030001c80e561505105140799a034041d80c42d4440074a66105000003580400c0228050048814001000510800040c000742007140c80105855151144c8441030710b04d40703404c4500c154402d005900615070700098100c000409440c4c085001c640e400e4980d00203100300c4420186038002d6903000403292a000401e882140c2c0306600329803150341c9204040c01c20f0b004d03204aa02188004102c03040380610160071625580d621041074902d0301a035990741c601c500d02181d2084504075100d044512800c41c00b034400c2c100405901e0f201c05c6591075041c0c0000e443c0d00c00d0200007031062441600ea401414401c11680d100058080c08903082030769a15000010358025110380742509051200d07880c2d80c010340030103508543e0f80c1034000310305019244404002501801c0d954085540d4207102c0020640c54600480d0046030064004070b0362030400e0320000701520f07130301c05509014600400c809121603c00060290301c1c408018400102540351614613401c1118644c0010040da0802100e070301d22000 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 39742100 1250 39740850 39740861
    0x170322030e01080601081509190c020a03020c0a06050a08090c0a260d0207170102121e0f040209181002030903040e01060f0f110a020a0b040618030b0105010509150409 73
    0x80c00d03203e4040590713501c001140c2070f02040310765501440b801030405241c1d041c1500e407190070100d00c0740b0101c42c2c101141140021103014a001c00016072202103404103243c1c040c400b800608030b0507a01c2d03a0881c0c4c1032050203400303885000504002c100c0c080c00026403090307041c010007140a40007054101c01540e243e401d0f0410301c060351030404000e100342140d03c40040d0300003680300b81100b59402401c419441c0900302001c41100c04040340e007a540801c0104414001080e8880c800c12202c00700c111600da1009013000c10705801450034a452036084203020251b42d400003030329800340000140b41141e440e808009030502492001440c1c6071400441441071004000c00503000361418181c1030581680c1e40d00048840c6400a0054004540c11b0f0709122031aa2081d20710b028114a140100c4091441d158080350781d2402c0c40e849050300ba0030110301030003450f5004600c121020035800c03c4403212419504c2d880c075a0a01031241a050207000034090440f03440d0f285082519405a08200352110707516110b5101604 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 39743350 1250 39742100 39742127
    0x20306150a050301090b130201090801060609090e01021e0a0522150c031205060406080a060c0206070302040b09040207051603050106030201020105181b01020c12010e0709060317032203 81
    0x207042070040b0702d50070b0511805000701d811580003042900c503040a0081a40d28102c20380c10001040d102280c8a202401035100a00041e92082c018500e040308880855940c42480e03031076a401040442c501401d00580d60034000b048405041e40c4581049080c0c2d41480b40521111101100c0d848441503400480d01d4441141c0440d050500301c0c60302054201c0d01880780c050020045401c1700c0d0f840c00802d405a12040d8440006070001070800d0300c80e00c1c0149890040441129119102c070700c0840340c281c1c1408201d8102c4c12a06095090070300b0155411854018504994002c2d030380400c052052002c1000fa604c411031080440d0400642c41e810414060306043c002a0f000d1340c241400308000455100b04080c03c0c6108402400d0542070f005800c10201c2405401d03541148641c230440440daa903504080d070b43e0484c7d5013000042544540e10700760304140c0d80e6442102c1c005d01e030981c00c002251005120b05031401068001542c0c131350741c1003c055100e00074a0204540c00351344460803070802d600306ca501d80940 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 39744600 1250 39743350 39743359
    0x20108060a08011518021608070203010f09050105070207080c0f04020f09090c04031a010608010509130203010c020c03150103030c080307020102040308040e0402011704080409020a030209060a09151107050906010c02030615 97
    0x103007081d80e2080aa100d03107088481f07480503000000d00130800302401b400d05548010008a92000c1c6010088103680b41070b001684c059554005012030560100b04d101e00902100014140c0019888000307901c04105002d210300a68001440740403080102c012910180c1d40201440c03202e0501c0b2030003010607001800215141c8690030f005400c5940ea009140781201c244d0b81e07400a0700c0e03003040180130456902911802c0c030900c940a8000050358280190540e0b80c0d115030080c59484500c02c101881c04d03078000051b50740b03150740c80014400f096000c104e90703200f10b800500706070782c3c1e4030b504400704d009105075407024008080c0800c0c0811401401014240513a000346c0c0c41503070b0980c81c0301c1100e04a00d41540e00602031201007000b0407080800d50040c1c41c99030243d090040c10700304410b000c40c883e83c0c880340c400f0700060190241809038520801c40a41400b4184c5004590502540c0c05195034641d68041c42c3e1080f086c0c480003c4050b885100900e1956502606949a0b41800c1ca035004a9441c00c1c180203104 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 39745850 1250 39744600 39744629
    0x150130080c2406041e090b0619031101030903021504081803010516110703060e030301090501081b150706021318110301210209040b011a0304030c020108060a080115 72
    0x601c2150ba4501c004120b05221107070395180c5000300002030007440c00c1c2c000303002481016102500a540701c3c0070102c0d402140c8941e85461704000300a0501064803400907019002d0005002068252210b981c1c800400e0a0004d003e581c1d500b0305914048030000c00030102d1414108000801c9601d40190810840307800742c11203c04481c50801d400c2e124111400a803c41e510820710040d00e1040235413001d10000718013501d55190b202d40799001a18805070300c2000a50000004004001181c030409004111250107054003400030740081c0c00702074100c3d66031071040c0c0c0d005c051900d0108500301259815503000c00c0c11551850310030b0b40b401030b082c228458059541042540d1500100c0300740240140c3c400e4003510f0614680c28143c00305081202c804018008000421440d40103850b4020000e000310f01501495805601d00061000c0304024259051000f070800d1043c4400280c01c1001c080285a090034802c501c1d5076114049250703441241e20a007515801c0c84800d001e4482c00d03515001c2600c0c21120002070 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 39747100 1250 39745850 39745873
    0x30403050d05070c050d0201120c120e0102041502011e090602090907110105010602030405010203041703070c030b010305211603030902040f15080304150804050f01110912150130080c 80
    0xc4c03146c107031040640441c80c0c014100346d191b2090751140e4140b40c11802c05c82d075142003402d13221040310305004441d942c0c0d80d4005001d10151501021008074000c00f17100074411407030b81ea0001c401c0c04002c0b41c3d40c00311440e00d5100140410040d03406684d04a400507011186c01e26100000070301000f005150859103528202c0041071991001c821a8151081a002140b825180c0b1420300768503250401070441c41d000038000d4a00007000e850301e00c401140203070141021541941403440c1481c0c0e50382200100b0004c0110207011107a0224240c4111511143c509182002141815000341c444210000d60140c50071400c42089030055108072845072a007000c41501c65101e00040e942e030301c903a0142054054104a401c0c1c0c00c24814010158040d1048090754a0000c102620034250751000c887c65950020100d0000c002d424120001c8249840610041407541007010130201c1011041c0112030b0780180c0811412121084800240d0007544044407014143d042030030085091b0b00800400041409602038000303 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 39748206 1106 39747100 39747109
    0x120705030a1706010c0b040f0b040b0a0b0402030c19200706030b060a0801090c0c020a0b0c0606010503070806090a091b030c050607050a080903030403050d05070c05 72
    0x15201c10080c14060103410341c00d0892040303070021800700080c0360790222900040030b400100d128040e071600c0c06c080c00c07402a006000741000c481d0600b440100f0a0070228503114a04580b401c01c108220301c010401170b80b209542c4100300744802c0c03180c500ca103400ba000308440301801c1e0604103448045034800040301c082c545a10a110340044104010003605405516203881c401c403640340c50050500009410785d101800b8044160344e550810300781d418000e051200b0156001041880030640d205002d00c0241e11002401c99117000744004160313035501640c10350340164400d0320b500200d562820b0074004100002005002400e44400e0003101080302802d85d12400c440e2500c96105071421414001084112a844503004520400224011070700202e0032440f0560300c084225560110540000e1441c0591380000e00940541420a000550410000c0241c02e00ca00e2400007115034a50411 = true := by decide +kernel

theorem cover : BRFrame.Cov 39568350 39748206 := by
  have h0 := BRFrame.cov_init 39568350
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39568350 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39568350 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39568350 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39568350 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39568350 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39568350 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39568350 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39568350 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39568350 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39568350 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39568350 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39568350 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39568350 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39568350 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39568350 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39568350 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39568350 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39568350 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39568350 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39568350 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39568350 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39568350 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39568350 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39568350 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39568350 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39568350 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39568350 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39568350 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39568350 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39568350 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39568350 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39568350 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39568350 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39568350 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39568350 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39568350 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39568350 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39568350 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39568350 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39568350 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39568350 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39568350 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39568350 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39568350 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39568350 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39568350 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39568350 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39568350 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39568350 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39568350 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39568350 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39568350 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39568350 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39568350 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39568350 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39568350 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39568350 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39568350 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39568350 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39568350 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39568350 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39568350 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39568350 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39568350 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39568350 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39568350 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39568350 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39568350 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39568350 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39568350 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39568350 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39568350 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39568350 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39568350 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39568350 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39568350 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39568350 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39568350 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39568350 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39568350 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39568350 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39568350 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39568350 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39568350 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39568350 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39568350 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39568350 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39568350 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39568350 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39568350 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39568350 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39568350 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39568350 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39568350 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39568350 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39568350 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39568350 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39568350 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39568350 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39568350 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39568350 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39568350 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39568350 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39568350 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39568350 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39568350 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39568350 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39568350 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39568350 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39568350 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39568350 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39568350 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39568350 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39568350 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39568350 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39568350 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39568350 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39568350 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39568350 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39568350 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39568350 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39568350 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39568350 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39568350 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39568350 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39568350 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39568350 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39568350 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39568350 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39568350 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39568350 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39568350 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39568350 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39568350 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39568350 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39568350 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39568350 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39568350 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39568350 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39568350 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39568350 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39568350 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39568350 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39568350 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 39568350 ≤ n) (h2 : n < 39748206) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
