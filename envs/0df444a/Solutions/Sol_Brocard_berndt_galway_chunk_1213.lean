-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1213
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T01:47:54.881826+00:00
-- url     : https://prove2.me/submissions/52551263-3b32-4241-a2a1-9f404543b0a8

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 217985611 ≤ n < 218165467 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 217986861 1250 217985611 217985617
    0x105010201181e080301180f020702091f18020408010c0804030f0c021f0503060f01110a140f010504050a1202160312020705060309070501111203040f06090807030903051b0105 77
    0x24200b444800303c805032504403d00904914006040c94a0003c000702d29082d5004e100c0d011580350380d504000380c450190340030b4120300440c003000b0360040c00c08012507007110036400f030b26100e00c1c8900c030481070040c1d076940515a003110800f0b815018a80105042204040178802e6400c4d01606003400616480e056030b0007084881c510000d101440003000b90308041d9203804811354901059009400d0895442550103400c2da0070072240070b40304500050b54070469522440e1043c8a1542031401420825103c2c2c2d41d80070104582e15060080348136500c1c80c400706440c01d00480d402076005601400784800c9500b000c04412a10749450000d650142e844080b00c5040350103144200c940051140400301e240741400c90410308540c2c0015403001000c024490109400310700c41e070840c0e500762101820300c03170200c141e552504003450301100640c00a100150109240001c070002691013000002694665941c60480a80160300b0a80008070f112000b4030411008019044149820502d0120240ca541b030000300644 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 217988111 1250 217986861 217986863
    0x9030a0305030a11040f260619090204111e0909060904021807110706021b0f1801060c0b07030209090606090d020a030f030e0105070c0603091e0507030605010501020118 74
    0xa40040081d00f000b8080c1c0c0040182c00000204075650703039446a0a403a541e605010702e00301c40e181d0307540510b510504202e09240c1d007260413001c0c000c0da90307942d81080520346003013412112098803110500c1c010380e141d1203481d000760040200c858079000110303074451840c0010200c6020f0300404020044450741c0c5c2c481c1c801d900c0b645c121520f03e92a62284082440c200c110801c58199a0f10441440034141d085442201008140421242500d949110032641c60219040c051700600c805810315440c0c0c10700b2a00c0c0d00c0c00a07000b8000340c0280c036498400d810000001d80c8070b40300264180c503038081000505080c003a04107805107815420068a00c000803e5194064540e80c42110000341c403c0f404d171101301c50340314180d400030500e5281d00e9403410814044d4075503401c11400289400d190400030b44c000c405032000c00d80c020108030021418003100f078008085035103081e24030300648803500e4094a03014117415503452046011f460300701c1c0303513103800d0080c0d59041c0c00171030569041000c40b0b09020816a006a002c4e = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 217989361 1250 217988111 217988117
    0x50607030903050303040f12230d06170d020705010801211b090b040501081507030c0504090609021201080607410417070501120b0f13060602070b09030a03 68
    0x942140c903081c1c4808205a000030301501000c003c02c0244002e10683c0100c0c2e40c084d04004203005400f4100b00c0c1c002d90416881800000d400300c4806c014440540501549100c01500082158581c00e4544030000705075101440c03036000b03107010f24407a0b03414000307130000340420301b1b181d912541085038080806411158042c0b03207001c1c4100c20b43c05d11008070001580e05100700821080750b921800b551018142901406000d80d00340342c0002601100003445503481c951010502d8425100c50340110050030201c0c2d01c1d03000b00413003480003040540203440752000802c03513070a00503a607860743d5064803e085030507840b90245401040403c6240c0d900155003e164418031049c50710011008041a002c007ca40c107078800001910244010030510001c0060017a2001101a079845484030341109965007854000c41e800205440c0141c0a800c205401601001d8001020b001808a40001250108004860105102d52205001c00200ba0140440c501a103d0106140d2034034a0754004285d4803810300c0001010 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 217990611 1250 217989361 217989367
    0x2040b0f0d0603061e05010f140d03091d010303081807060c17041e080706170a3902010e1207030212030a09060e06070906030e15041407051005040506 66
    0x362001c0e0761024001c3c5030b01100402c090030302c0c01a9139030700c0c81e46058000c2d0b0003440c007030003c00c2d5141d204c513101080b500b01150346072084c85080300f80400b0108440c001c4050144085000c20f45100300b84450744a602ea03110b03034003942c0d031560400409080b0f004d0b140d00c02425034411802411800400d0442c26079505040c5400c3c3c00030705103804900c00d01e4160980145400206000c140450303200209a4480e5481c4090004952155100351310f90540384281030114903959444c2d8036005400c4c402e40e82c80449084001402d40502688004d04800c0710075003004400014040305028030000405441e200c0c90344020000301ca0412a00e03a40c804012211a000b41c00c0131a02c0801c151080100382501a03591a0a64403810030100d10f40185c40340000488a0074101002c3c90380d90000025401c3c4541d1599480324205454480d098008101d0580521404d00522900d1203080207000c4030207014034030070380c2da4814403010505a41c1c00d158047d00603a220350341e2540000a4035500c070041c0e0702a94401c80707480b5a = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 217991861 1250 217990611 217990627
    0x1903140309011715270109051006050c060109051815070f020714040e070f061701050105120414030d150f0815012d080d0905060906040e0406021204050f0c0402040b0f 73
    0x104d281708101112840b150000042144281904910b000b4142d20000201d02505e0310403e40c0c0c0c5014100000403030b68050340042140500507001590400080b52000d54130124034600e05042101e000c0d560170080405400744081d02c0d40c040a004061100c0344003401c0c080d800d00b8450b40c6403003050769084d0b02c115129062113514541c2809503000070000c52958040c0d00d9a075400140c000c60306020000c4000014400005141d401102110b0b54582c1801600d4003941ea04d035901c10079405004207042d15440140a501c408100d6441015000c85030b2a1540040525290210031280d02c15000715569402200500840e404c0646169041d00c40306040d0207201084603403d1041c1c2c0a803480c0041c0e40c101034800000b5059008250101201030035520119425100ea091080c00e10500030302c150001c4040004001d1030002c1c111080d0810310840003d0324282000703413040d018010584007590581c1080210a00d11101049040c000000a95042d4182403400f60001c0850040852030303888480d000904039 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 217993111 1250 217991861 217991899
    0x60d060f02130e090105070806061614010c0509120d0f1211030403081f0302010219030e1e131830030501080c01030e07051903140309011715 62
    0x26001242d1209400215a95203100c61400905896101c0907500e02000b181d03d091181c10365610a40015000f0786c0b4000c0b030385400d100c450050003020355031a60781d1542400244420b000750741110000b55105911349940b90200254500040301d403024543c031503240800c0d1680c0006003d4291382080c100700b0142c40c449002d06026000718200c10100c6600002048201500001488e01428030041040c403200903c04400350b03078500d1408003a001d07038801c0034640f160042e4440202c044511901e00b11b5500001e88010841602008000241810342c1c015020440e04100c0e8091007641e04640040c8050a00c96040c00d03d140251140580030725110084540b281600081c10346070505000e68030ba038116034020004000b803500307000c0c2005500440400000c1513100780507401d108124880589a10740ca00401c0040203042d045072410700c80100341c000400700340480601c410303004621014503a51507500d00010109464103040900241605051220340c0d03070401c09000350000d050740d8104661480ba4847c0b = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 217994361 1250 217993111 217993117
    0x318240c0412050307152307020304051203040806131104051e040501060501031b05190c0203100510060912030c05030c01020a18090608100207060b06031e060603060d060f02 76
    0x603110b00e90524415400c00100000600e4510700407035940308424101c1c414201503412021403c1201c0a50b41200d85050514403441070b0080401d00440c0d103015910000705070119081d58810a050b080030074200490078007445000e902100d00409580a581103aa8420030b01d86201c0301a40115a940c1c00140701c1c2d2445222250b6800804c44103100c1445d107407900a001e001d1383e01500c3d0000e030400f2444522102c030484030a0403101d803600c2e40c50401c5502e540c4000c852580c5c40d202001c000c0c401d0301103805a01c05200215007800c3c403074000b04a84c0340018404845602c1984200200585900e08001c0400880940c00303800da414504032009091604101d85580107061a412055100052408480341c10030358445c40c1c000303c0c05200641c107940350481e00c04c480c2035101d03101098125901e5004d0350b020340d0b0b00a01602c0e03c640130014a1000c408007190b460340084a0740c424070503a00104441c10014003030060342c80031080342e40c44d103180307400008980085003d010041065032190340c0761480d8009a016 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 217995611 1250 217994361 217994369
    0x12070e0307091802042702010e180106080f1317030a09080c0a1103060708042307061d0a05060412030309050d0512070318030f170108030318240c04 65
    0x810310801002800d15091500310080485c803503031a0444885e00340c01c000e40c4005145400c28842c1c1d080740216001500c2c00c1e4000d07407a6a90002000144a90203000a038503180608907940e94503080e490904d02040f641d2402802041044526402a00c00104030394481155501a0300345542c03243c4810002c00007800b5181401410300c03202003056418510700007941c0748541c2c025850303e400401d90301300b4580c44003420b030f600d1000221580d00180100f10b4041c401c00d4006040d84003c030201000140e8182080309039003010380040e808040280d445041c510302d00c0c8035490100e03914030969190000240700fa1107207110350665402e06142003800c0c18005d41c480b4220942007420b807100d0b2000c00348011710a600c04140d15504a0724003002c6511076100748100c0304440e09410607030b500b010280d00d040c0d4041c1c10031503104007040680c0d842a5003200c41c94034824000c280342e00081d91281813403000341840003040081580c1d0366020ba800390841e5200070381c80c0c44441000d0f80140c01181ca44d00752180f494412a04 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 217996861 1250 217995611 217995629
    0x10f0f121110020102090102011109150703020312191407170c090303040b03010905010b03010f090f1d010c08091b0607020d05030406020c0901090b100e040b04110306120312070e0307 80
    0xa40302d40c494040d00105008030b401d9008000b603ca5100182040740520802240c012482c60b00c44842001c4410050100d503029004690800c004844611400402141d10100300b03002c000d1020400e4125008568415149000488551505507c001d007440445083c0a0310303803104d60085000f4450100445d864010094140c03a51a6100d800300c4215500a02c94405140e240000003c1c2c04440103081c0ca043e1605008910100352501c200d45001d001408141e1015664800c100342509040001c5000340b64103c400200b101205580081d20600d0014000c1c0215003000321080300f00010303022400c80101003105c00b56250f2000e4000b15982c6010044010405d01c0b00150209409400260071040302104940302c0d0f1581c0c0c1c0702c0529030140d551144815401c203100242c4046454003a008411041401a2000404c4a1000005007d5a4481500c003101d03090020a01c815800c1c41015508068540c900841c03405400c03500c00c80100e00004c10b8030b8104881000d644242d0b0740c060100c0d03401804404 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 217998111 1250 217996861 217996879
    0xc071b050a1706010506090a0902030a140112050c010509100309080403080307051206030d05090f010c05010204090204180614010c0c080d05031504050103260408031908010f0f1211 79
    0x803211500706800b49500000e48101c01c00019986800c0c1d0484240410151280100d6490940d0b81c00c041d41003d4400720300d15884003031018100d00c3c0c140486008040400602e00000401d0402d103041101b03015029042010400c10317900c00d5180c0260890030302049240c00110600315040826003400b0b550001480e58400009220b040d59219018080c0d242182174000402d4851004045e035804681401c03801061040c4000c1e610383c40d1142c45400001410f040448407102213035030fa40d0072a44181c00a206c96580410b0511407200403400014002800c60800c00090382407814134070126005808242c108010094550300b00102104903c005001d98012a2918410400041d0994000716110b950358901001d0344a400c0c0780c00d0042c079040303d03044001400404a0201c4200603910042e5400e201c09030b00f0080004c62031410002400c0c0b284400001500c00700c0702c41d5009004d040b0690040100300d01d10041071140700050a2030600711401c1c461041050840b624003400702e030183d0324101c0e52080c180 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 217999361 1250 217998111 217998119
    0x111c17101a0702030f010e0102040e090604120305090a0f06061a070b010306090f0c030515060301150b0a0512010806220b060105030a1d0f010c1d040c03060b0d0b0301140c071b050a 79
    0x150064000cbc0c0715012181f00c0715039500c0d51120380c1c683c1e0848001e46080e11104001d26658066801a0340101c28003080d0307035031a00f20751601549040e07181c030b045800d19a0f90100b000000408103484840c0c440403034285251500545800f855100103010252150760740e210040c04000805814a066035405122070880a9a900b095910f5545604405c0341c10400b20700018060301d018801c0c0b0700c0304958210215405410100e61b0b000940256562400b88070041000394800c0481002e203a008003d650002c1025160000709003440e01140d0581c14504040000a040010185100340f68402d03c207203841901c03680c56a5119014000580142a002c1800c145402c511280030900c0c501d0340318080000e00000c0f1110108a07240c00d01074189500400700045109400d03d025004140019014600400d902d612071260041c1176020703c4501007000e48c1d0706140e041500302030042d10440058580c100045182c140c1c03114a036841901c100034800008514180246281185100003501c3e01900c841c0c051074803 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 218000611 1250 217999361 217999363
    0x21e0303220303080a090515040201020c04090c08010605040b09040807020114120708060316061214010b04090e03030c07030305041401061205012a111c17101a0702030f010e 76
    0xd9000680c0040c0001e000038074003c103203018006c102d66001000b000b0746048054803002d040c50280c4101d0440c000d0004078076480d81c5a010f912540e5000b4500322810314617014015003140c03660f0707201078099030400c401c050305e41c2da5808203954806c1d003141c102a41e48506200403660b00c644009221006a008121507440c10344110106110b00c00b00d440b01e0f800b88d140c84003015603500c5c40408240a1414002c1c041c0649480f07807054407045c0c0c011110125114615611403000c011098026141e07501c00131408000000f00d0b4020080a10401d0001e54a54200002c100039144160103010381419151408074080144044002c010103a81000070070a103521001260b00c1c00f020104250741540c201520024410b6100800c600c2540414440022034403000f401640c140c1d000700420308c0c07140641709900c066052280c0c041403100724195034160300c05c0b99100c0551981900a00080840c0000d00c07420300107111a41c05d03480440006c1110a030b1100c06038400289410150b1402c0042c550030071882d1800294 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 218001861 1250 218000611 218000677
    0x200a020a030614100f0b1e0301060c0317010605030f220c090608120a110a1205030402010906050c0a060b040e0118060b12030d15081e0d030207021e0303 67
    0x84085088607484041c49a1200c000302d005e1000b800d991644100000200f900083c90811000801e155040070340b05080222908240e002201141c01801e032101090341c4031401c1c0520304060034010070a94104003000b0414000200080c0360345565001080c840c02c0301c5111425803040242d8080e0b1081b1040c0307003228104c071039441111140743c00c0a10110b021003020440003440810030f80b2890510030009411980380c8060b80003083c05020b512034900124803e401084801444c41d04c13969640c0c107007403000500d01085940100200001405088408680850010310094108102083c002010000600204540b0040300659031900041c0c1850040c258540c000715401100c080000a01d00b90a206400100311034016458108121100c1c91514a601c1031102c0703501041420005502d42c8803840ca840020040d408550790780064500011408100d142c044814910701903084c0000303135000ca6019140e442c6400d0040f6280d9000d83c465403020015108042c50301846100500030310b40f100e401c0b20f0717 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 218003111 1250 218001861 218001881
    0x210051314010c08010812120402010c050f010903140313231009060b010903020604171c02011514060901050309030d0204030f0507050117061002070e07050405091501200a020a0306 79
    0x203003404d00000e1114400314807516101401c1e80ca05191014641c801c0550200003082241408412045000030400800c070b501c641140b90b500020b002e42d02420090081c80301c1c0d031780b90515078108004016411524120b5080d05540c4119001c1c0460074000180c846070550040c001014410301c400d41c0c4008141d900107040d42c9001c1d000800010b014000112202c162074040070303400050403c4100716007a4030b10b2007907001e03982400c250351484103051209607810b900c0401c5840140c1d114107074203c44049a0312180c004101c205e001c440f1150070500482d5140c00b681595034181f02011000548282e01442142c0c0046c02004c0c04558076512840c201100c445448001d5a40b0320802c0b4002c101540a101c803c00b1070403841c03c036402c3c6a61080c080140220003411200110700894800050403148224000d0080c0c80c2911466100c80c10881409081c840c024a40542501800f840ca01540d8201640003210ba40340d41090200303c154250f21031806050400094002d25503810000c01e000050b44407884103 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 218004361 1250 218003111 218003117
    0x91b110c0613030b1008210d0c08180f0606040f240e010602071a0702043c0b0612100317070308090303272103011d070210051314010c 59
    0x16280d80025540440c8140a100790503401000d180881200715406141c0c0c00d201c01f1162460151040300f0a416104281c490780b0208a0038000e001e907e113513a2201002141e07000d4003c0045c1070900c0f46590380c2da40003400980c0219981c421034564071600350001c0c1301010300d20203900c2c000c0c04403600d050701d03030501c5120300d00000710b03100004242c031072010612400f03c8600b02695020706400c0307081c0d035406500800301203a0041d900c003500340c910301c41d91b80d207481004950112082240c3d0100d000c0c800101501521540b503928020181555035900c8050f00d0310f418800a00c01080d545040320201142031941001e480310303c081928202a44403c001040c800c0d102c5c1e920018980c07118400165a4001039801c241100984d10043c03007414244e0311103040c2000307118115404d040000307200e05010b0081a14111940d130f0000b0040c000c51a11000e891040c8032894013483c110300c1d00c803100a4494940c030410449864491001c00c0c00ca20b40301217034108071504413410200800d1034020250007004038003194408 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 218005611 1250 218004361 218004383
    0x9060405040221130b04170714160603060b03010e060406030b090c010201060603090312050408040b0403030507060b0612131118060906060a02100e210d06091b110c061303 75
    0x202c00b80c107504c011180d5030100fa01d150b10f13152039590900f424200500d2102000301070040e00042481f29000c508038861a40107001d044031082c10250092240390400340c00c0c1030406100308940007401d011203044801a00348003009803205000503016000a0b840640500c41d610184264504042403a8100c8c51090b0002c02c003140d41c6c0c1d0415004e4401c012005804920040c003108850590b07070304095841445215500d01c0c040d29002d52401940080e002a80000c1c804142c8008004d0f80d0310984c03805010031a4605d0402c1c1c070003800c031031031800700a0011000a0800e6450410045034214003210200d0081034200c2c42b0040306141400030a04880c150322070502100400c006091032000c8481c1110680c3c0502072a00c864000314000d007014204003e624450100c500e0036122084050359505031100d00080d54902055400900f940d002d078100a81c03091030243c0041c580c5240c0f88101d060380d1940d0525034141032007801c1c2c85003000600003446030403590000e00003a604580034140800d4078403e03010141c03 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 218006861 1250 218005611 218005621
    0x30a030f0e0d020a0504180507150305090102030606040b0705010f021204050d0f0f0302070c1a07120f05161a0a0e0106061d01140c1b0906041503030509060405040221 73
    0x2d8400d44060081d411010f040000d01c40d03414150030002418042c1800c40c2080505a6070b810304d030042561010801018902000c0c0d11150b00d40100c64201c200300c80203604500b014030009605200300c0c81030703030700f41c000005d442d1080100079040600d440410010840d12094107094600154004980882d1540281c0d121010158001d12114515140035690400c0c0d09039003482c15802984004e0f0103807220f803800c4e900018141c1011030b583d080d51041148058a52a540c035040344102544070144003803000540c01c0c001440e6129003500c00e0202520310800e20801d180c2050902c0241c50b0003200310300c00d0103400300500304905402c41c4006001f198002c20401d5510141100c05c0c450110103141101c034040c011000940c41181124501c4000701d420510b0007808039035240c6400145030075000c422860880c0c040303513860710048031688510300740d0701400700c80c0c00300741c4c005050703280b038000201400000304c1c8080e85603ca81e0300365005040003400855503031380d01c1907400b481c00c84a0702d40b40c0400100f51300040c1c = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 218008111 1250 218006861 218006869
    0xf031902070507050f04060308030c070b0f070804060903030b06031305070b120609070203042103080105180f0a0b0a030b0103020a0501050f070b06030a080307031506050f04060804020f030a030f0e 86
    0x280c1e101d90410050100141880c00700204c84048814560340591594000b0000c036126100440c010319000f1001e55a50200745482010910000d0100007503481890812920b00d03001109036071b000340e21200008054000c0d1030260000c084695116411920200030002510028441900c5190240b01103401a03036442e80103000512600c40041ca800c00b115001c6104ea0a05e00300e0140c000c84980140c0e0705064549904000c03400494000054249600c5207881c140343d04095040d0140a0990f20452007035130320b007000e2112003005000c41d500141800d0028201c58000c1d488142c0c0007d000709071103291a80e07400d008170380c01c40a001c160310521019070001100d41c0aa0104c42c1c0280400c01ea1508007000d5407207528003c4802410250980616111070b000035000ca801140700e10010384002039038a9090703400b00360b90722540e00180e0502100b04080c2c070720440e8a905503400c850309403410f541c0d26511880442d03e02d508205009815104500790202050342003501e06820389034070780d99542d01c0d00ca50320803c = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 218009361 1250 218008111 218008117
    0x50903070e100915031703010321080c07051606020f010e060103020a03020d0309271a0306131707080a1805091308071b0513061a07020102120f031902 66
    0x542c80d856450502000206001e4005020300004280000b07045642e035143c1c0b05010709600c01e6503000160010040c0f04021004000401400102c0c800350a80e00c0700640240500001410000d4107980101700501006401c103c181c001d20502284c0c401130a9540700c0196485940c0f001010495003414114140c0b4800020194102d036002810040341d28910b4007440700c050000501582000311401001c1861484c00050079140d442803070507001130007003000152045401c5c0d2074886d03070084542030543d040c4e03590015115030042014480c03070140014a150070030010f9242003030014010b0012403454141b00c150006480340c000103444120207042e8016940e4020306203402143d40c01004900070034080600030050b116010300c601c100c01d2510300a511420805e205800503002030009050060146050640700c444441035102ca061001c1c81c203002403000b4210307140b400010b0300d40c0049201004d5a201708110158520350f01e030142e940c1ca0032843e600d400c540c0221200a03903030700039007850500200c541c822 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 218010611 1250 218009361 218009371
    0xe0a14071e0b1e030114040605010206040209060906010309060905010204030c05030601030b071b050307060b0a050a0b04090203311b080c01030b04021b0a06150b0301090e03040e07050903070e 84
    0xc14901c00c1e081001d10140b9400c400c0002200008062100d0140c5010b075000718042d041403584500000f0ba884c04000640700305403c071a04541048080c4801070b02c803680d00a80019044440d43c00ba6551803004030b004084111014103143c1c1440c02c040d0a104040d40108180d0380612914503e03240c644090594075902848000e040c2440c0000044d0501d100d42d280b00618880320144112040782030321294a581c20a0406481c0f05603200e001800b545080f04180d4001c110641c4c1021403141b51402c88a114002c6224006400d0f400000042d920520b42c42400d0b40741d185120420581c038030403041c041042d1120303401107400c4114242c1b88181000e05083d91811650903c0c000c1c0b030740d029848011000340100b00f0042e50800c1d020312440c01c58441c50248049030750070043c000c20400140e0709080c0d00ba00d104014100004d070b44d96009004009036507046a0640d813002030041400442e48028915501c69544000641d1105a042c000c1d001c1d0300000815042000300d0071030710b6072a10785c00400c0c03140c101070715 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 218011861 1250 218010611 218010659
    0x303050306040507080906181203090d030c09050a0b09131803020c010e0616021f050a0206060d0804030b040c050319050124170a05030c1c03020901080112060e0a1407 73
    0xc001200e12441220b00c42400122100b550300b0550041d111901c9e5400645442c2c020f41c0024140a00e0300c2c0c0c0c18400d40200318250302e01820502d00d4100450b528001c6406980d0038010000380c0c28116407136850184c402410141700401c403440245072500c0c0c5207005000c048005020311299541150310608442c104070900509051500c0b45c444041103551403c00000c98201e403000c1480d002c100c4c140080c199240f0754a460b080d41e0307010300580080c01e04c80c1c005e0000740709840222201000ca4585016079040da0390109030640c0c07544882c20f141c010840e880d40403560505c070b400d08915240c0302c5c882c0185a03c62080000b4003409141da041e410b5a1140c40c00c0f0b51002ca06480410844596001c500001c80200e00050300c0c1141000e444040c2160300c407105d210760513888842e8501d140000c500501c206502a40360442c18081c0c1040000c02500041c4070f00180b802d282d810100901c001d070f90041407098180d4040311300007541c510702001961500c1401080030300900c0c02c0000d16104c0d100da03161924450030 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 218013111 1250 218011861 218011873
    0x607050403150b01030f2a02060f0109110d1509050c03090607030c14040f05030609060106020706050702130f050402090907030305032d09100c141e090a03030503060405070809 77
    0x5200200186802103c55040644500c440744104100f4850042032090086e4030910030041d0ba040a0441c1c1d92050b035001c115031018003017101c0b04003031510007810741d500c114000c01ca80c4c170011038515181c0541c620800006181c00780b841c0344410213400701e200312101c1100501c0241d98800245400b0700048600811076085000003031042482584030051102050602d40c08401d1205110f141c940c100e500b00292001003202c0911261404200955208203a0001402c6540c1401d400079101c141d40d12415082c07020110342d19085582d02c80c0c010700e00d83c1c4040c0040011803405241003010700002ea90a80c003504030f4502103200384901040b40d0040c2d98050700d03082e00d5515000c248800c4a401005403400302180d02009200c02c60107541910f01038281d10004100e2126a0002070003212120301200c014441c81120096650754000169880b50f0b10741e01c029080b0718481c4402103514403c10f03041c2035100303803c10008410550881c0146000f6641074070208019545e03048140c03003c480a541c4100254052 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 218014361 1250 218013111 218013143
    0x303020634120213090506030102270303090d030e0a0602030c120306040207020406030b04050111070c030206070204060b0c03040321080402060c07030204110702031b091305011410080607050403 85
    0x41021200141181c603103908240c0c0c920380b02000303d80000910924818042404000c03812080c068546c00a134102d0003103140c00b440850409908a028441203100041c950b117001141d0b80030f0094038a030882c06802000400e58910b0000c1c4400300c0c9501d8107110b0040064041002c0741b0020503600c490500c80010300070580c45840d00400303070700000c14940d406502002400016150350040703c0046100d200c1a181c0c50400e4a0181e0a45080d60f4204070740078000c1c40120003051034a0410021a40c05030380042d52a1011b00114005c0c3c481074100340200c01c2c0008810710030010010041c0200c1340601c0e004401481c60300011815002040505e40001c2e51850100d0b0140c5440001032006042103412a00090780d43d034081001d480640480100402c808100e138020350405012049842c1841c2c0b580e107841485240001d2043e420141c10380c101c407030a20309960100402503010b140351003511070075921146044180c5205000f41070240440d1409940c01040415014905681c03d5a0707114070545a8141c41c = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 218015611 1250 218014361 218014441
    0xf050d09030b0c130f17210702060304050a0f050d0e030303090606060903030d05280c0c060e150c03040303141902070317100e07020c090a0e010b090a0603030206 71
    0x4034440103101c0780304c000050600803420b0b80c80003c000452082e007041e011204002c0c01c2c007030150302c10313020040600005202e21442d1011190700640c119a103030745035121803e140f880d120003203500502d1000b90040400c20700c4800100b6841c540707581c2c1c1d200000c0107014000c0c1600c2c0c3c0400d94220130103a11440c041a1149400c4000c1d15418502078110380c00c21045014800c151001580c0c0305050359100d40c1520412050340d88a4104924101d8041c000c08900c51401840c00540ca90050040c2d070740e410400c405903409004209a428004400102a04241040e580d19510542e02203010a2500d200c40500c9000007285910031004d00680b403447c0d4021206101c0a03500c940000c508001440c0d0240c40341180e0300151034010280c2d80d40155113030381402280344889501030706110039940f0904003030015a40d19891103a00816101c008992400d005685034058009a40f0860380140c0d03c400308400e02441c0c0d48114216030180e400c41d0f0140d115403100c210f03003101d826030740c4822000100710309103002e84c = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 218016861 1250 218015611 218015617
    0x906060909160e15190603180510050a06150801050907020601050913020a030b010e0912030114190503030307020d0801060f0509010513050405010602100510050a1203110105040f050d09030b0c 84
    0x10303810004000d0981d004c000901000807003502007100070074850302032110592610a42c003082da200000e00140d080e580e15019500c0202410604d105038558000814400701c580040004050603448012044030280000d0143c0c502401064041c40306000081c154500c009001d07812690702404101940d2200d4030051101c00035684266002040c03000300000048a0310720582c000d0030341801058160801030301c1036091640a0f0603119280c5400c1c001404081a4180c43c0c10544030300b01c0300003400101d01c400c3c590720f0f000030f40c2c4000c0d41070001104000100b900814494904107076595489450703a02c0d00001e0b0b801a141d41c0d9031100154040c8a400d05075405000240a041507410804030100ea85400140544909820100058000c60150246d618090080940008585001c800c3e0241807002007955400c0501c1200e22000c0007200c1901414041c82000c8402c03100b440003172000d0300d03180c100341007218010141140c0c140b14003440140e004d40302d002c000042c3c2e40e024081a000d074035070039034844045e0 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 218018111 1250 218016861 218016871
    0x60114030c0a02251e0b030c070f05100b100804051b0111060a0c140a09050607110301150609080f0c101e08010311030114070810180c0219080409230906060909160e 72
    0xd0b04d22b1000a004c01c0302080307030304030b01e90880c04040b611542c0301041c044004142800c1f2801d2214040500001420208456584500c0c400c00d010004c40524012220b5205684060665004d0181402907005194202c11601c1ea5203807246052481d4008000945124a014240009080000610943c0350040040c04007501420466018200c0d02c000039003150b0000d05510008143e0410810819405c80d914100600b030b81000f80102903041800c1980b5900503001281c400c0da911034250001c140940c41201a5182c414064001f02c122200081c0c00c01d1020b02064902c030b81c00c04c13409100c07403505005d5000b01840e8010b10280d03584801c0c0b403c0d05c25200181401642060494000c076003c860a620316026119142011a04591184010b42492034021130000c150003240586804100a817080300c0c110382294400051000d8202102241e01c50b980007806030441541d0107104130070340001800e034011001100c19003000e072a4014501d66402c02103000116040c84400304002020000803419400 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 218019361 1250 218018111 218018123
    0x30804020d08041508090d050a200a080301080705011403010b0904050a0b040f020d1d06010b18120f010e0318040b030a020415060305060114030c0a02251e0b030c07 72
    0xc66155130001491228030742c0d1850001ea1404104000e04004000700c140e440c0490400074907251034510000c5c50300506c062003490082250280764203030f01c1c3c100107268403550000070a41e12540c65030040350700c03840e03544101d50000304030040001102c08000d0441c1e0403128804500c61620541900344006400d0040812008540d60b05404285440301d0040e0303082d54100c0b44005903a80500708129084a208c0081c091480b021120010103244c8000303030580c155150741201030f840320b50040303003e8a0342412141c00398200d409116000d110400000e80480007070044030081c130052002d140850b5a038020b801d00c0e400d00c200072284034031050401e50b00040d50540702501b81d50b280c035801d40119064561601c0d9840c4d02e044003400c100a541d901d84151a00080c0034601007e92005034002c50015000281100403000c0c400101d01911a00802140001842021041e0800e02c0029140c40e501200d610809c21000340161244c0c0412402500314416191210f00702400e5850302100d1541075000504102c60b2 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 218020611 1250 218019361 218019367
    0x304060f0323070f110f030301060c05031303030909050a0e07140a08030a09030507120308070e0d02030604080d0f020c07030605040c030f0503030a110c3f09150403030804020d08 78
    0x40881016a82c0d10071003240c0c840c86080505860010701240e03c01141285680040b01c1603401d0610102c200d80c110b50040c50480114034403800d2840c25445465298020005801000010190003504020880340c94003c200210b560782e004102c06c0d20856a400095600211005e01c0303840410b07520080d02d02c80240000b0341241e140c1a440b441c551160448901281d00c2080410810404001103400303003c1d080c1042050400301d543c0a8824400684010b050201503200d8000540703800781a200b01d503030014200e502a080074242180690f000c42008130721103042c0a00503a04020314000c0350f08040c4410002c6c0b1a1600d5501c551004180c0a0401c9503000241c1d000080801e04812032008280c1c00380000d95030301e0614003414021240c01400903001c0100070300650000c1800031a09010600110000e000c0c41011030381d80303144c550041d0990358060031750302d1507807050f2440940251940c000161140340c80078403c00f84034a224092031000a00040903600050010705003580080307242c40c8101c0c41a0f003 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 218021861 1250 218020611 218020661
    0xe0c100f0201060f082d1b0609100c060b1002030301030b0406060f030c0f21060f06051306210f06021c0e16050415290c150601020304060f03 62
    0x1007000c44c41d4082829035001c01400804680e450f00c03182d443c0c0b425008449844464600c030f0548901c1c420100c20300c44203a6295007170403900c61808840c0d0a9400805281140003000c00141008685840c00d0710500d1074185d40e010790741810304c207440100b401c903002035045070b103140d440960001c0000c4c02118090789074000080d42c00d00b9070072440d01443c807818140307460301d00307040a106203c101d551002c0f800002c09403807000320344054040b4002503900280089007166241d00540082c2225a00c8150850101040c60350b01504950065056450801c04148400d21201d8006900d1140410160101036821301d14030000e440e0340d00030855200401e038000105085008110100c0b0340b004500541e580025441c49801c420010074800074082c2120100300c03003180405448000d00c22800f400a2090305400100c80340201000103250312130f2441400340d910701011104984075906140711900c05417043c0013003061580080152030507038915640f002c002c09503e03402180a8411300300009d03001c044614940b1 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 218023111 1250 218021861 218021879
    0x321041b03030f080c03010b0702040b01030b100914040603051e070e0f0708180d36064107060501090c0e010201090804140a080a03080a0e0c100f020106 67
    0x340007035010340c07101d003542200320401a005242c000c10001c0954401c0006100710301d0071809480c0b5203501a00d001813450f4001e80142d000b0161b038080c4682c0218041500115180c0c8400d246040d942c24801c402c51810b100024041681e0301d03400014060707007100070045502c141c94020715501300d000c4d104848100b07070307601d214543c030810a440301c51220404904019600782c1140400d03401041c0715459114148811700f4868880011459040c100400308458051010a2002c0c05c00f001201c12424502c81c424031a2040781020a4814040841d01a412030b003901091521030003209008503104c40811007985504581c07101501c01d0544c03481000340000404114203100c0c0b0350103840110070009514000c2c62001c1d000184101e0350034116810005100b000030030741415141207a140c03100030f131080030900000650403a0540c0040101d4810103045906140d400b0b00524050b050f400001c0111503180c4040e00c3c3c61301200140b40d40c108142c026a060954401e0071410b0704811280f00005032107482e00c01070 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 218024361 1250 218023111 218023163
    0x409090516030b0a0516020601032405090a05010e030f0d0b0402120f04020102060903090d060c03020714070e07030b0303030f180703030201050f010902130b030703110c1509032104 79
    0x80c2c2d140390324403003005000300d03d91081c02d0308086c03940c85000c41c000e0f801030b0003540c0d007105020060011284028000c69602c02700d100c03c8010349a107105010300d03c5c18802c09030740c881d1044400d64256080c084040241003000c01154441c41050b10700e0f5180402030400000502031031860542c0195080103e01101042d95204e03901803106031141c0251411700d030000928100002d00f4519158004201040160307407040354641c92154450004214000c00c00f0040e0024094020090510111840d03000240500480c0c0142540ea010240440701d4950110031412200c8058609401d6031040020070001d0400b101220381c0700349040503507044481c00264240c1400f1181d802140540e449100703120b00454800d0103d405088844011401c2610364800b1100d151001e12a40c203441d0030000c0030440c1e0501c00d400240840000300d5510f80e841c07070851030711903650710180c8078000100c9648010820001000c011182d8841c0c20348003400b010119a0b00244852901138807c40e007524942107882650200000c1d0 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 218025611 1250 218024361 218024363
    0x206030a05090d051606181b0305100204060f0305060a170a1515030215390705010210110c0706091706040b070806060715022d040909051603 62
    0x71805080034000d00e8602903164a000c4180242030140b01c10711003103110700b4500c02d508980d010481010402c1560700704420b10074060040160201003040700445100800c00300c911640071503681c9250022014224004c1c2e0207000700142034881d84003c42882500b01a070010340003041300400913903030b22207921140a00508880c16402444c9001c05020301e061030540c40540b202d0303060001061018000c09032880c1404000d128200c1c690541914000d0340040d82c9081c0728881a82602000c1c40a921341d030952443c0d15105040031710440c990400c070700402e41070f08030b801c10b03002007000610481161000c7c1c080b00450030070750007051003002d0512008010310402095683c86011281d41096243c11040202d407803000c645500201c24070000900405465901082504e04103c8540301d09000440350700c2102d40280100c550148040103200235a0700820029102d00f4030840282c00c189482034100180c0f000302c0101d07910500003000690b890740c01c448031a510403420349895a15407440c0058010b81604 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 218026861 1250 218025611 218025631
    0x3091a150112051506070c0b0a0302090405010b070c090b1201150303030617030306130906020a02070512070608060f0a17060a0501050604050d02040c1218060c030513030f020a020603 80
    0x405000d2541c1000e10400004060603081c441da2510300c0020b800d0307032a025038540c001e2100150040c00d000c0d000000d01c001c0e140c0c2182041e41d962202c100240613402c1403075424440c40c5050000035440010704229000240c3c8413135180526458000020000d00d4400640364004c3c0c042a01148051828800c810720400e5001400034601e082d42001001c403040c03508680303580c08e06d24012000884000094039403020044801c1544a000104000054911080010109800452000c2c4140d401084810540703009130707a00d005082c072083e07032103a0725103035031080401085058000c2812400c10300380c407006501003d48020300c030f00d607592040ed00024030000807a426400c81c1d0b003440200d100034068a401444212241d505080c00d01000a04415002000034812a59103540ca486940200c11100c14600b9090b410003054810303460401460842c030504072007007480d104811813a180640702e090301464036010b649001c200303aaa0f080c1d60141c1c0206261085d0b00c2405039500c0180c0e500c200440c03140d04002 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 218028111 1250 218026861 218026891
    0x30705010207201f0e060f030403020609030f09010e060717030702060703020708040513150602030c060604060e01030210021219110606060a0507080c06040515070305040b0703091a 79
    0x401d02848081e07001442e20b0100c40b04501074400c40c3d03600002d00d0f030284001041c2c9030803440718080c01c2c5c418040740c1107250b400c444007003516045a04801e018522480c060b07002c0c0c410568075461003e0300c900c12050203e41e010070030300607885d0552056068603400040540007900e4105141c80b10080c1100017461030f034040b8000007c01c03c00c10b905210880d080003d47c1429414142c0f241e60710f011a0041e4050280210b18070064881110b003140c000718541d104050308001d19988400d0000e440c0d41c865604440a4130641c1c0210340d85042070702c14601250b505c074001d2105a4295401c004401c090745010404501c42c49490110491f804401000025401c007803803103150301e15160113403801800112260081e00000308010b00740d140c080440d2605803151502e2540c940c07891a1030420390003004401c10b118441c1101f00010808002030b041907000700d200c01d88005a88175207049098410071030300100112303544400f003003d09001e40c20a03c1c005101e407c901c2d074941803040034a40880011a128002084c0c2c40c = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 218029361 1250 218028111 218028113
    0xb04180b0415301509150e070506120115021203090a02100f1d12070e060103050609041a070c060c09090501090b031c02120409050103020307050604060813030e03030705010207 77
    0x220003d014103500850159040d4499040101c103203c04100c02411862101c500002606200c1e403013001504d03440100c1d114401ca1450324036000f0405d11001903121310881201007110b19005044d52043c40ea01020a05240c0c2808030400c0040000c11140c0d0a501c1401880c8000b40105c001442c03048803550001e000c200142d004201c24581840554000c0c03080201388840e000360300000c1446c0c040450444882e102c0000d10105103030b103809080c620154050b080340460b580258164003400340700243da050002c3d88411041080044042d50000c0c542c10461884000c5255032300540c030fa10201c0d605111042c0c040d2a280c1405480d400c1e4203110004215500c1840250598030605014041c824000c10150a00002003542c0f0400101e5481c03001c81200b00c1d41040a100f0400412040d200c03c60300b5458560741c44200010301305c2800100d02c80d00034454042042e06004084e01e0490b40c1c1c0782d03204215911405442c0c107141079401e1080d803c001c107604850911351010002018094071400c001680d030308603 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 218030611 1250 218029361 218029379
    0x3020313180f0912200322170d1b120314070219081b16030614100e09010b060301080d110a0f1205040503010906020a080702070b04180b0415 62
    0x568148603400b45003c0799040822820788000545040609142411028049041c001c60024030942c0130786210000f8140c131000e543c1e491501210058411070380c1603036203c5105900d00500d07101d138a0425400340c0084000da80c4508070180f051070104104a4000c1c5284c1c641a040400d58200103001c07945480000c6003c10780d0090181d40541c803840030306119580050703007e030045441c0d000078042000100e1070b000c546006452511070022113004507070340c15640b00e600d10980c11036440180c1c2c58070300e803400b0542610300585040e4070419010313a08000722828400021990350b0302401400c107642d0b0312191040140ca40e6001140a001d181000b08444020100c000744902ca5841e1001045e400c0151028005941c3c0f00940c00f10030b034005040b2070036842c8000201d40314051507010340d52641c2480140c2d024808039500405030640c40d90390711100b0740e07610441a650b41d241842503003c2c164082000704155403c40c10b0781c44c0d0544010301d01042d8a604a0b00240540d4000304860b4641a0b5502c010448084 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 218031861 1250 218030611 218030621
    0x9070f081f1212090311150c100501030b0108010c0e1e10020c12150402010e120105040339021210020403080d050711100b010314040b100609080a0f0302031318 70
    0x700fa4606405110308503600c1d808008500329003540a520a0740510038110381070800d03111130700d400b18111030f04000003066200c082c1001380700a540c0030301e042c000450250018080c0c00315080b070a46401c02180000ea042c01140e40c842408a00300503101da003903140d00e541c0c1d03084581e64010075070700504500c0d07021030400851290440004d411503000c20900c1c48031250100740d03031307910980908001007003200c00700214282d110b03220240401946408200401c040d003103041512941b985080c0590102210741c81c1c242410301081c8480d410110721034007c00146020364502400c0e0203000242c032030007052481d1020983c1c1003508111813910340820120005002841003984c8102240344c014507083c00038048984441510b01100c10890b214101c030312040e4042e800c40365002c141d12443c5403041c900780c1460881100d00756100c40c0c007400d51080008845205031141c171700740c903400e10261942162030303542d02d40d02c1c04141e07800f04d05600003841041885c00560031010001d04030660714a022420f840440c1084074 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 218033111 1250 218031861 218031893
    0x17040c0e150102070302040906090b190f0b0102060414071706060f010302090a0902030603120f0909011e0605181207080c030604031b0606210204060509070f081f12 72
    0x10320700580301052a070303000503e0003c83ea019030f40050341e40710b0750900380003070300e02e07610040c3c04201080c0600420300c8400a480c150605045000c00c442a440f80001d8150382e82400060b005178000f0000c10049801e0901403210400301e001100c40c5d0f0707907803540080580200314111001d107402400030072605092002c420700401c402440c0031031805170210002010340038140143c4262907404400602a5101040306c210348800046220f0348400384003584480d140e02c49003200d8000c44828000007041c003010304a40c0d60301d0010301c400b0303080d103401c059044a09401800f0407030902d00c1c00300d102500c140c03034450524214075212009401124203000f1824035189408100c00e000707074400020080440e60000800c90787d043c00003800d07804c4030304600f0701c10007038100f542222504160b100100390f0540414614190100d10941703050010550300c0d420016989801c88484c4042014007010355030442c8a00001c0d580900700210003102009d107034074441c6410407a50080341805a01d0503582003480240541c40b2050 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 218034361 1250 218033111 218033131
    0x7050301060602030a0507030e0a0b1804090b060d02030106090c0e19060207030320011e0b010201020301030809060717070818030d0e040f02160507240203120717040c0e 74
    0x70b494010000c1d500e02c80e01c001da504001021400100b09032207000c004480c101c0051101d51103546070112210103038054601901103050440e0010300c03905141c01000029074010801142a03914907040c048020100c100c2203034913560750383c8041026402c40c4a40307803030b00307440f0b55071051f05080907001e006140031080100c03014049000010003006a0018600b4107503503140c80c0c06aa00f0a08110350440c00003900540c0c0d5141d42050300c9944803c0240e020310a0f82c2409420078402c0030101001680cc070300c07080c0000303007400004004042c82c6d401c1090081250601c10050030040d03104c40401c080c4141c100200803034078481c0c00915080c00c81c00101030600c01e0101200600304101d2083c501030884400030036a1070040d900d0b100d01041841069041d90031303181c441c5d40e010401802900d4410f4440070313076000d48a4840d0004200c0d801004c41c0c001074070041c002c40c0d0019880c06070301d0414614003030b900400074410407080b006a1501d0a210401060040c0d200e10403650610741011b82003028404010700c0300f080 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 218035611 1250 218034361 218034371
    0xb180304080712060f050f240a090207050c10030c0206010e0c12090c030a1b090c080f13060f0c0e010f0f05130b07030f020c04021c051f060e010207050301 68
    0x2041c000c01c0031012074090340d480c01c0a20b80d030b5280800182821402c5915541c0c5030034100b221008a0f030800901ca4150f07000074800c06001d40400b204c407400d250f451660090700701c3e4414449280740c1d42c01004414003272011150701201c0c901c001020240c09405140001c0e4031071031a04011601048550302424081c413007680780b0700c0c1210300729445006d44410341d08180300c00c402180c024902801100d40010003d0140c035080d0541d0b04000c0d109029400d2500b184a041c03060020716030b4454800d180135241c5a607140000c503100c28071031140755500034207581034074425060b89200007030310780c0b1911007090f024110101e42045004000340c00c8141c090400d50510612202d40101c2c44d604c418001e1702c038012404c0003611140040d40081410b030b03881c1c2110340075035400a80c0806043d04002011003c000c03560032248801c1d0840c05000c181d014008102d40094413410054003503140c660040d5502048103401c21026018500c000d02442080760701800100da07480318031002550781840400003504080e402484 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 218036861 1250 218035611 218035619
    0x5040f050604030308040605060d0203070b090a0b0a0e210d0c23030d18050f0a0c08010608070306020a02011e0209100219110619020d1b0f031b0204090b180304 70
    0x7144035002400240b002355200001121650381c2c01c10b00c0d90303131500901240c074216101d48020140b5407190600c50b1103201103040000f4107008400446402c0d40d150340da900300c840e11504c180001544680d603154a4280b00c151181c1c1390000c10004802c40001c1c40d610100345a0700c90814240c0300500f10501c8039500500044049844000421102c10b041c0b110b0700083c04841d0701c880300030718208025005215024150707003100c40e2100000d800183c10b009203030300c800480c0d0305c1c4840c908841061050712440c1e08105400c2000c22455405044440001c0c000800c1e00303d129421b0235000902901c0f000c8089501048900c0c0a00b851101c44a41c0c00c11030005050820b0000988100e000b42c80400416921720004c4c5490b240e201c02050b551551010400704182100703001010351258840c0140c0ca0004081d8030240340c03807900b025241180d45070040d074000c980f00c07034a840444009607801030390400e2070601c000010060312a803065250050145000b00240d0400314a249a103820140300d089a55005200500c = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 218038111 1250 218036861 218036867
    0x1030c05130b03100905010308070b090a030c0303050714031311010912120c12050301081b2815050c0714090c0a1202030a0507120203090c0904061103010605040f0506040303 76
    0x203095a104210ba6520fa680f0481210031031350440c1c2000340b1840c1040c0002003045000c201030f1544600c608103655103a51030b5070384569154014000030740000c016a40c800d02180c041c2c0d109c650481024a4004440c010306004c508483e4019990440e0f08210541210700b880100718170181d04c28801d10384407044e0b900d007010742c01e65100301c200c0190410900801204240d8001c988095400c0e074003c83c0d144100c440b9440241c05e64000b407140e500b180c0201c0301c5c3e20b018452050b070400f00501d00100348459204c00700406a0100d000e10200c1201915100c90110b01103c500301044003484aa030b8601e40e99001201d011401c017032659000041d80105100d112001b60785110742c4a600100c01500281c46040c688000c0710111107442c0c02c0900e25100105010101c68a600312920800e20342d03c1e14060003d01c03900e00003c07844215588080368004560f03190700ea24200107825001400f464000c200364100e803608442c503030300a80c0004c012075000141002038032401413a00d00101400c480d01d60610385543c41c05 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 218039361 1250 218038111 218038147
    0x12030507120e0f06180606100f030b0a180917031e0c0702061602120604080901110a150501060f051c0b19090507021005090a11030a06140601030c05 65
    0x1040400352282001c1075844030422100001c814003c0441d002c605201c1400d10a001e14200000da083c001d000c0000c0c00b90500c401034010090442e40c4600440201550442c02410240e240715442448000c00091041d07a240040b180e00f01c0078400000e0150803803070880104c8150794082c400b1070070140704120b0032007100040e000c410380b001c010000c00d5030b42d0b843c20890030b48942d00380254440c90104144c520b100e1070a081072032503172003520025283c05403e80401d5880804460013041f800b800c00502046520074041f200f00c0d001c4007812520818100d682d440102e984c01003808844540d00e000401c1016070010008101200c24100b80e45401c403848041044490405010301c034060321544141031541b00d20314004090549000700f00c02c00394642400c039014060030340c0c1d1280148034009000d00106001d200b850300642c5520010070280031503548100f940c0826a000790750502a081041c40424041c4c000d114510101404102c40c03442d040c400034044603e141111401c00c0418800e52800d0303c038541d15 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 218040611 1250 218039361 218039387
    0x50f030709020a1205100501090506031b250506070305060a030308010323010f060906051c020d02060906070b070801120b130203030d0207050a2a090507090e070c12030507 75
    0x20140c2c0d00c0c12903d00664401035012010958180741104101c0700400805042090b00c0c000da80c1d034800e1036590402c1180c0c3c0d000a60b4030031081218411440c004101c5030000b000f00a250f040961070041210004070784004450509075420303040300d8108803000c2e07030620035030b540f002044900b600c02d50f0842e14010020001404020303c01400990b54801d1900b902c060800c8009070700000f40320000103010003502801423442001d203001d09010001c2034901d046081c202054401124071041c0c01c800d9000c2204400c81c0c80345c140d070004030400c1109580c1d12100010b28405002d4000407041d400c1180b401404c2010503404084d02d00011004000000c400c0c060490704002c1c80c0c003c80d140300f8030b0340c000241548108840d03200224800500c00e420401d01048800109000c1c01560314030302d04100c8003908203286070840c000e0081c1515014040c003000341c1d000c26007050080c90103080c1951600b042c022007503404e680c4100403600170003645d010090614107804203000545070502481c10030700030240c500c401c5a00 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 218041861 1250 218040611 218040629
    0x2030d0203060a030209011205100209060d15030b0f0103210c030e0f060d06050f0a0602190c09020d0204180c02061612020a0c051014220609050105060a050f0307 71
    0x4040741c8a5521690000f02441c0c008040d400d95503034903184802000c5020000b202d940c0500018081118017500c2500e800c1c000c01b0344482e1030641112031590041200200405c2081054400070020800c1014501d21a002e130074091b484950541c208051201d81d148690495445441032f001d0180394021380c0040c107554141441d07440d0391007810001308401555823000c0d0704a00c000c5140080c411550b0080802c403402a80d480c000c02d02c42105118000740b5501400000d80d004109607141481d418883e450514002c600340506d40751100c0c0954141e0b40000303000c114407600844c0600008080b00325001200f44c403054100a04600100003a4443c0c50050940030900040d80c44003401c0e0780600c00101580c601420119952006403070050a05243c0c540d09a44522072021a9500c00b520b40c81591007100107115880341590341c58000300e01c607410550f480000300d1825400d110004820307001c0e00d80090b1041c0d0000c5068038150b03051092014490340803520a80c010b0104209a0b07c003c030b0304509490f5800 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 218043111 1250 218041861 218041867
    0x90203182b020a200316030602030a0f1a10020c0604120302240109090204020d05090a110409080313020102070512030a0201110c06160e0307120203060f0702030d02 72
    0x5042080c4210100c40814114059040c107104154401c00780100040410034060041c26409102240d9030310284500a04c80f5004824003951029440311902e00d800b4020212903814148a61450760515564001c4030f280c1d40110500045491600500c01d80e850100c400b01b009904060f08501490226074010b40222501160300f86814824440c111410201900e86a0b90f10b0741c404001100340f80130b0b9415001030080750002d24820f04071a444110140f04055800c140c0d90034240490010130790b4440482e8090b82c02c0104890301c030784c68020a44222084005001032404508080d01015840c036080c510451520142ca800901c801c000d03a82c01c04005c03510b110305240c4a00c010f1f0310f4903445030003480c0c2c0f00f103102000c120980300010051510b070300980c1c008d1100d0708182e00b12204c1801081c032030300701e075811140c00280c003000181450b41c001155032410310300c00c16240c00400d040c554607410100210710740b003d1080541c1030420800e600440403940c0b01c2100c0c6020b000c002c1d180c4c0179020789156042c1e000 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 218044361 1250 218043111 218043121
    0x5031504090534030b04110d0b010927080d0b0301180303020904020f0f27010f050706060e01080102070c1202010818010e0d0302070201020f070f170f01020403050a05060a060b04090203 81
    0x6100b48000c0a040c0301007010610713449040400038508121001c40d4100e000030001203090602c1010380f40c0d183d901c141d002c21140d0030416404045c1c05038403604058090710301080741d15444141c11600c4941c2c0030b0140c7e42d41d507131607c420420980c0d03600e12405000c0da04014048003d1480d840309148070720740618005071a03200c05270004c0c0180c40380241c5a02c0b0146c021962240c02409800144640240f5541090000e4a8120100c80d00e070500030a03240410003400403c40392034068401031030094441c07580013030600e4440c042078203100000c0e040380d00941e5000c00e030403040103524031540010b0900e00307400d4610201c4a038002031030100020541d08130240014400014040d00350801c1000b5101d010035a82c4104142c2d100800030b4000e0082603005219000240c03080c8400460460140e44c074000d66190390302c2c1070400d074045410b801e0a0100080c403840c407102c0d5641d8000e00c090005036101c0c0c00030b004a4401c81c2004da10f443d1001c0d10310504103103442d20400c000c0025500700c1e0100c4230307105405a140c0d0b0b10 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 218045611 1250 218044361 218044423
    0x1031101021617033f041509020619020610050a0e010501030c020a080d0209090a05060f15070c140a0e0f150406090f0b1c03020a110a03020d03050315040905 69
    0x1703105a04a5109024503c0f400180072000000035911501c0c200104a1036a199004a40c0041038502503d042d40410800a607000150800d401d81c41c000b0380907601c1d082c41703101c040c3ca000040c030328680c0c01030b0409818040499860f88040d002031408442c2414400e040250301d220403841840f6240c141595060007600860003030262922007500243c03550348803080d220307010300a907101c0e002080c45000204001000084136110700c40c01904083c0048800b00c1a0130203202115201d0100c2c035a01c20400e0051100140c001d120640140c16081c803104a0020100c00744004000c440c1c022104000c0054100001c030070012440a80c4907403201200584001d015012500600c0c003500650703005410320b200d00010f000c0e00d410041c0e00c10400d40307107a98060200045d00041410072080100142c02c0341d800a0701040700c00c04502e0020700c0046c03e6a400380c0d5a40d0015482d08488507017103000c103d001c420032450b00d07040460400d03542c2050303600740b1003d0983d594860303c9045008440310402000841000c3c0001c1c = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 218046861 1250 218045611 218045617
    0x3050717062202090406020a0e2b0602090303070c17060f070806060d0c0c03020c0f0102030f0d021902060f06010206010f0e07110102030106090e220803071b0b0103110102161703 78
    0x90050302074407450511b800d02501039400850041c000c1100c6012548070b505141038410000b66030705006041440030131202900003400d690302690070603002e000070700c5550340174402000d0b0903129004018030305140c00b10f1096602d00e0301100c41c1d1541c00c440c04100d16603010100c2a588000381c0d2402d04c6455540d0f2001807203600a4000c442821460401c44402541c1c1115061001c81d000340c0031a0303ca0b801140402c14100a115160360040c2c00511006180800b114003400d031500a40c2409801e24003141c0401d120101c1e1a0b80da400164040d42c1803110302d401135141d55030054030a1002d002e5560502802101c003443c0c502c1142101141e000004183c14411000483c51104e401f00a554a59540388000d10f00540780c001c881e01c241b4070300c0c04100318060300410720034050380a1040c2d113a1542d1645070201a40c02c01013400f814070801155980b801400e403070b40700a030b281c031540d0520515415820001107403100a02100d06561003965134070481104204034004441c2c511104204900d482e1700d82c2400d40c0 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 218048111 1250 218046861 218046863
    0x2060a1101051602060a09031d010c02090903040f08010e150a150f0603060f08120901050d090605330f270103050d0c1101080604060302090907030507170622 69
    0x546082c0030301c00340c001c0410a0f0201d0348829401c86000c2d1300d0300329a007030840d0103602000380460213090300d030103445c184a00c1c0b0044892050500c410200580d40114000d00c50860f031203502d0b600000b60600221703420714411000350140c54003c10125160b560f0365660703082400840d061007488400050001a481e400c15842030030840da2484500b6038030038a180c664495801240003290420340042241070044410800725400c00c0000cac050815005980b0280381d004d006000d0400c10100090701c494800d40c018204103900c20040003481d0f02d4500104803203a041807102449035040178040c1d500010285444129a00003180d2540743d0316921400108038100701081a040307600c4010322244510700d4410740f14120380c003c40c291141c2800003c000c842484d0520720040400700301c227100302d1065110321889680494007800015103680c07244c0014506020803682203c16500a000a00803c003041c8072200c010400c86035002c80c10022501c0e000e0721030000071f10030801034140b624441428109030781d802d4041 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 218049361 1250 218048111 218048113
    0x120f03070e1309050604060c031503290c0405040b010504030308070e061b03031503010e0703060c030f0617070806070c020d050111030f01080c2d01020f031801082202060a11 76
    0x543c1c240d1034032039141c0904a4040d5802850010610a20350080c025810340924510843c1c0849007943d45103524644130348460348200071081e032182100910316039020301034403c4040305521076290100f00400e83d0003003042c0904002c401e0000b0400203410100b190703001490f030b00307040c204a0310480200d1810b0085402c1c03d0f0240d0b001ca1948810800f01000942c0504400400d5030061482c1c44141401e840d900000504c640d8440340b820000310b0283d910030340c0c23007030003520303000c214090001d102c0c4080c2c400d0340c1c00015180c4400d1800c10b420902c00c001038401402080040d2285140110000e841c1d0105050041d01030103026004900b0444290700a485010005042c2038070790030031505a000c992400d00a0700c80d60321036120280e485241c200c2000c0c50f1212040703054080e04845aa0f130a2004100d2603074035055220b1081200010300041c0007801c980e24060054010841310000014001072000e03020401030800d5404d4140016035107130650340065010780e8034694829907050200c541e02002e440c020b5035 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 218050611 1250 218049361 218049371
    0xa0f0c0510060e0a020c1c050904110c100b0619020106030209010f030b0c12071d0a0905270a03050c030f0c070302010e030309010c020f120f010e120f03070e13 70
    0x2075469a5030010058942a075560f0706070f9a40d0b52481c8040380b08190704600c0c1c0f030748014110380e5132101c01d00d0815001c82d80c929045090a14410100d8181d070f541c0c0b003407a00c0c04d900c081000c2c42510300400400b4140003403180240700c6000080003190381441440c403140104441c031443c2850060003500701c06d0085070701525000341580d46074000c144019281c002101d44120507404102120421400e41d69002080800c1030040c0d03c6d815026a01c0309642c7d03d02e0000c00d4207a80702020f290382c0d2001e58200804000c440402c2034038000d142c0c1d003151102004a14070f0100107219408000302c0020358071008a42c1428003c1d0354002c428200e40c84c41c01080301c2801c101d400010010f50724140420a102200d00c01e0b00c40004a1348420b040580301d00a00c1ca0150014040580c0700b0301601d85014590711000c40908885140349904070070500340b55003040c03841401da4480b0068807154800300415a4000010349403541403420b00002040c542c40040d003201c013001021030210400e55200800309601c207010820400c6 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 218051861 1250 218050611 218050633
    0xa080c0d021e0a0216080d120b0301050a050402030c040e0705040f18030c030e010c080904050c0c150417040602100e030409020403051015050a05040905010b0603070c0b06060f0a0f0c05 81
    0x2e5103a001c403541c02c006000e8005c9440e040307208590b455094a150001404c29a109060200e81c14501d00e280c0840244d116034040c1e0098402f03104880c02030120f030201041c240741030300601d0318100c0b040035024040c0d403804600601c1168045058020b031503086038041030300c0f00c0c5403901b00080c045800c2d06074803604040d4109000c044e085100384d400b2038841d440d0f55000c108854010f541c0540361440103043d14008200e088900d2400751300c01c1e41e02502505003181019019030b006490400c0004003501007025410501c400d01401800411154422101c107031b01e800d0401c00e00940b5404c445032813081c0c4644a0b11202d211440510a0310050259004115100c0c1e41d41d0416950b11140d00804085892400e800c2d0980748840381c5802e810380340c020703168014035403070321341440010311901e0015030307c556a40c106004c5a41c3c503c8001d41c024245541c07400000461801c003400a5100501540c2c8104810480081000342400a56824032101e0a100e100104a050300745e81c2400c40844c01403550041c1d01001c0 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 218053111 1250 218051861 218051917
    0xa0e0901141e03010c180b03130206070c030606060e0f04022107020a02030d030212060301050105150702041107120207121a090a06050403030225020f040b180415110a080c0d02 77
    0x2c41b910703402a43d82d41c820f95910b0074510544010b650300325003c20544d21082c09828164000d100f001d226000360040f1940c3c9840c3c41040b07558681101c00003400b01c1103c00000d281c080c943c943c081c0003c517811440c0c2889094680380b165020a40c540041240c4000100850b000b8484048181e4020741a5021602c082e44010000d5201e02c40302c0710034119500118a07a801c1c14030400303050751409411146030300c013211031940045c0c0101d0003c0340e01c45c2c0c803401080700c7d221084c030241030390a108a44a851032070007100041c1c1021030380c1d0440b510b0a0341c070f01c0c000d5000c034442c220061441d24001c01004001e480e80d05202e03003010120000070702514145018401019415401001c25040044611408040d9000e820a02144101001c0c0d80038104803070340449440e250b4440d07070100e1002000c2d540c14040b404203607a44076030100c90030f59445e00100041c00340c1d9211070180d00f2101c5400c1400614000c140b884c007400c00310b0301400c0c9070320101002c526107550708031603030482d90490740d00040035040180c8e4560003 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 218054361 1250 218053111 218053127
    0x18050102030705190804030804060e011e060e01050616120e0d0f02031608152d09190203030304381006021f0c02010f0c02030a0e0901141e03010c 64
    0x2400030001042d0118105522817070345e080c011030f0b05a580c140c0c00e4445071902005000c00d15070b00030b0700307550300c04068a00309205c0d6032203824180e01c5032011810925004c0712081ca048140d02803802903404015003000340000d02c4031070103010b0b40180340c03071100c16a500e012551210440e01481d041810701c510b403010b001203400300b220814422011100c20018060756402581c1d9282f0911034154000099550228aa03841c0c1c40c0c1e2044c031180102701201d400d40e8041080c0007107003030310806050386001440826802030000e40510004100140351100055012076074030300c001007028040079954484880341c0750100402c0d08043c0d0000c0792504182416100340c2c0e0100d1401d803001c1c0c5201c1d540180014410740045000880d06041c020074201a80501c012036028000902c4443c00f195a20100903c84242c580301e03407201010a070340150b455001141e0083d2590328071910b01885041050010030090000500150003240181c40d2001c0040f9010304140c84881031801c019455420003540d08440c81e0b00500e4 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 218055611 1250 218054361 218054377
    0xe04140a02371401030506030139020109020a0314150a0b090f0609011e09020d0209100201060503060a090f050601032108010509040b040f05250906120618050102030705 74
    0xb482081800c0b080700400345402c1846144600902819054051360183d800f441e8861805800454608c65601800c050070581c4448900e64014904022800020560000950300c2c2c41f40020007459000750005010039003540710040012012200c007280d040b406200b01106444130704981991401c0540881c0c01902150180d14043c100b00000149a50a900c50041c081e4802034003040c503d0f400d07e4801d21507610514169140000700510009480ca800d200400c040440c00c4001078481000800300254407441458440c00c5a0428000f40404d40d00030800c03a401032002034000482d4a954605580107446448000d030035401075034000400d100b00c1204c00360344c0940c1543c01000e511403003041030310110003e0240071f42009404e0b00080014081003250354100d0700803044500f440c00d060352041d00d804002480080c1c615500b4403c080d40201c0e0628050140c000c52000b804840d0521642401056030f1490103040c1648810b494280d841e1014030f40e940c001d030000001c1d581c2c1c0c0b8040c0300141083d440040 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 218056861 1250 218055611 218055679
    0x30d050903041d19110c1f06080c090c0c190b040b0f090607030203070e03010914101109060f090d0302010207020f0609094b07020105010e04140a02 65
    0x700392404002c850300f80a100340726011110710003c070250604002806240400c504000c01001110b182100402c0300070750149420355107485590081c3c0c000c40942d0f0300c542c4182882e620001042c000340e0344071302610f640040f01ca4112a2107080450401c2d1400303520080c2c9803581407442401e0418450210499849036029280c0244161221211349038040e1044824102c0ca820000100b000303144213400554126400349000d040090b903020000b42124032116085622030803100c17601c1c2c402c8109100c0c01070030310540041000300c1c62210588203030920a450030180300c0e42c00000d03a0b1040c41c103010141c0b07003107850141c00d22283e00b415282c0a4001c2d8085841039210b05401201d041d0140781c5030f0308688224802401c00c062945920702041001e007400d142c032035914140c064080c02d0071034a0030407040c02c0c00c8a20322140981c01072101d01722044880a0990021039042c40c0051000c501e041d8001508194002000d08100303810040d241d05080040c600254880700352480800c2510500b9440300f08508066 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 218058111 1250 218056861 218056889
    0x1213030c0f0b071401201902010203070e010e150a0908100603111306030b1311030606090c0d0603050607030606030b010e09070302070f06141611100509030d05090304 73
    0x40c95200391a624454540c2610040007200002034070700c0d6807564440e04d000300110761401d03408078908038007480c0c22207070901117008203a0300540c0e41010b03038080c01041c0320300085107181404840101400e88607036546040c0000900d04181d20380b034a100075045d8220802e0803039103800704024001c109000912070842d00c1d20480410150145007403142c0d000b00c0fa848080410751590000c00d10111142d02c2000300c50b103940e82c17000000890a01042244912034420a000c100d400300d11b0041a0115446507550103540700004028080d16a0301c032041e001181145925243c0c0040c05182c400b600309900014064040c01c000d0003510354044d0000d0003a074046440a10581d0710101c01100d00f0000024070b00d510051480c08a4ac003940640d004085d00c90060384180e000440d50340343c2000b603480d03900c0e10f44c405005e45401c01524028450518803401c1803072404c400d014242c3c1c0348680d07440f5051005c00052a907988082201240104200c0b070000310a44001c0c01a4544501c51949039002440f50704458200300c = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 218059361 1250 218058111 218058119
    0x60405030901230406080a02070c060207081204030209060d150e011401080a0b071101090206040e0403030b030f060103060f02160f060c050c120a090f0f08070603051303030504051213030c 82
    0xf4090315a038803502203615401c1c680307040710445020001070404400142d0800000010030f0750803040002420164004085042c40c20310040e2504040500070201e12206120034001a5641220b240d002502111203100c5410b03203040c045950601d40490f14a01440d222451003141410b41108052801b80c012041c0b803030380da60306a00e0b120200e4040c0102040c0d403441c00510400e000e240c034110500100c00000981070305070f5020810326032003508903030407066401e010071040540c0360284a483c07450690140180c0942c101e4226038500042c000144030f00c0e12441c40200200a550546844008400031207100510a040610031364042404c01d036141070921101c1c2e641e29000b803003150700b41c2031214018000828518600c12454011102c0e960400199200c005040102c12071440090403030144071a8540745047c0103103141001c83d51003081451b05050411241c8103003400c02c81e0b04103030036050108899036140f50960500a400540c18842c400200e10640d202c208a2514020b691003001c40f01303281521 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 218060611 1250 218059361 218059397
    0xe010501030e0c01030507020f070b120c040303080403050304080d18020102060a061406071b0e0118090c0302010c0f060c020a02010210090f08070c090207080d050a060609050f0a08060405030901 85
    0x6a21421260b501614070403c69511036440640d000000d481034a41d01031f085070010f414010726600c00d00c03c0d25808140125507c9081c004160003c100d101d0080c0703003501d5941e010304240700041001d424802e0200014051182610858020180495042200b0620b02410514141044405034010303c41e09000500e007111500c5000c05888001c41c81c140c55000d240200700d51940107903070848000300301c405000018604800e0790341c090720710722030410419030400e00007443c01d004124840c11100e09280002c0c000c50040341810056a070207180c1000c034400c0c14100720343d440c22800d400900b02803801a02c0e28125601003481c01000b4800d9080c1d409907919a41c50f03030281c558081c0054003500c413040d0700d1000a0300c1d0300c0c000c20303a01e0700ca00e4180b0341d040d5450a00108030380118005541e48400041c2d40b0103803441c1846116440002810308220311410100001c029002a0285500803042e00c2c0801c120f80d42d409003064010420041152528a0640b9182e070b00d0741c0002107028045803101240030701e0201 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 218061861 1250 218060611 218060621
    0x18010612140d08062413080a02010f0c0b0c070201020312090303071419180806070e0a08060f04060c0c020411041412030f1303080c06090f0d02030910020102040b130e01050103 77
    0x4001030107107085da0303440c2a04424540d00806071a070540801c0104041c10000c041c440001003640304007611000394240005046880d10207205420010500c03003100008a15400c0c0c19000310440440030b80303400003071005038618440e102d28500d10100e441c0070084680c100000840c0302342001d544d154039400300c100314003045004440c015076240d01030401c509111489481021502d4a2a44181860640d1503240303605200302914100c000401190341160541402d07020318002b084480014034841c070380b0013001010700754040c00c01850a900e0b036420b13521040c030481c2d0b075880041c0c00030010441310990307031090030040d80135200344c28500c4144840e001d0716241401e00e00051390001d030302640c07030140390158110155000700b01143c580d9090307401c0440489c031071001901003e44864020a85402c205402034a040701c54403a821b007651000380c042000d65404810b4902c04c510070380f04400322044403002a070190045800c0515100c0b0041a00c0700e0700e00441c1030000450341d094200c034420366214001141039078 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 218063111 1250 218061861 218061871
    0x503070302010512060a0f0f0e130308070c080c01060b03011404060f0608101a0a200c061810021501050103050402092415070606050a080618010612140d08 68
    0x503405120500c141c6004841d005d600410040c03124030915124080e41c0b4a40200360070102d0004050704041c40418240040103402800c01800250134413040e9400030b00c003141c000c01b0541001020b40d0b5040810801c1d03000e4602010840c0c0080c0681e03600e0741e0040d00c05410034460820900080d19190390355041512504050352640024203070711500b0401b050712010702c06412034814600c42c806c0040d012050302c1c0110100816400c0c42640d032200101d0040500540f00300c061240c1d820403d00d001801000240f2400c0c0d00000d59080b0380310050b01c2d400d402d9000308000300c1900030718503200114513aa4040740b580c040410480300010540d80340c070300450840300c0454000350004049004200019a5200c0c0704003c7c044030003a4400d40801100442d001d070420308031203203600b00c01181c1c030310401c199030203400302414043e40c0000c2d005141c400081c1d40d540c0c0161410714000b60118581d03040050070b401801c01b41c0801c1c2c21b050803141c0b0354648424108080c3c4c018610381d0140035980e4a21502c22203802e4010 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 218064361 1250 218063111 218063117
    0xc06030405061b0403080703050d05090106061d1c030c0c060f090501050f070204060f05030f0318040506030f0708060a0b01030c140a05071403030f0f040804031b0924050307030201 79
    0x2955000000711020b4010411680c40340410f0100000291b415030050004500c40d6452030f46034510400d0810564901038080c00147e410b18005000442c1d01030080c903540a0b001901d0170342c40703013044045148490131080415100c43c54001070820b040e0005d0f9503901c10340c425807008581c260317180000c40d0784981107946040019000701d000c004a6204201900080c010001000c1c0382200c581d000a0448440e584000c0d00400c402c68104200d1030240300400c001007400c1c000d18600805408103c03000140034031044c1c03003183da820100d295524100000448030340744404880c421500d4010603070340d90004070f5030704076a103003850000b4609500c60702409024952036140c15400c2c4941298808a27074000e8070419003004010b02201001c114140b40769100c202c0d03044051966414030034015690300d01d000f0620099031a08405010010b41148216003c507900290898203241c104c0310f00e04112111b9500102d0b141e410300c2c411079402540100c1100842900202628a8558a034203154440d4928800a07000c = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 218065611 1250 218064361 218064373
    0x60606180312080403050d15030507120b0c1303020616020a0603180201121b11010605040b18040c0b030403080906010509061305090705030106030302030a030f0b150903010b0604170c06030405 84
    0xa0b4600540255400610074184103081101c5450340c08100e0750526604c3d0040d03500c0238020005e000c0305001204c003501ca0303000d456116031220f880b610354007a00500b81010300000040c00006e001420340000e130256500810082da2620005142c10740780c00c640c1000e9204003a20100021400d0080c0301d03d80500c69603140d9503d403505690015262100d80144120440e612185020410901501c15000302c00742925100507041c518460305085840301c2e0044e034011032800a00a509a88002d00145940302d0381511810725512407400c114055150760007000c001c02d0120902041641081c045072080300325804444040e81e1314002c000414002380c42454002100e0741f612404420300790007240c0d1040c60b403c01c40e000581d55030040307800c44490741c1c070540050300b0108204080303036414003c3d288004280c05091060b4002d03840007035030024080c0d02d258040d1400040450b85500c0c2900500c61034440201480e464542c0d038142400b02101450a5001038000c10621180600d05402500c1c0581d41000040c05 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 218066861 1250 218065611 218065643
    0x1090603051e1e0109111914030a020304120c020603062709010618050403020d032403051f05090d08060d08030c13050f0102280803040606061803 64
    0x82801070151400c000401040c040302d82001103074a8010100d000c442c031110301800000038000101a0400382451341000c407250b20010450041c1c0b00220f0b0680c000301505d45e8841402e49043c1c0d62540a10b20100d40801000030540312980030303521440c002d440090118002e00400c441080140000960080c02030002c9411410600001c030403401804004a40202d51080001c0030791408503642550f03a0344a00c01445100449061803125000b841c1c0c00340100e05050782c2c0039440382d050520f20000c0550300c2122040707110718036105080b42000c494800751202e4507400c015031034004107880381c00821000340f05090040840d20071580309036134078000707055888040d0004a40510010300120b80c0281540c4901012880c510011401128000ca01a41d00c49000f491084840740030f43c49240302c0c051000c941101c698011400c544100300c0d0420000c207030001c90341400c2684e100200302500076040030040108220450b4440c00540b4074039110750009103103681104030b000b4481c0c00002c014461900d1004 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 218068111 1250 218066861 218066867
    0x70c09050601021f02091309060c1404030b0a020405060d0c091a0409020304020307180b010306170619020c0f010e0111042301030b040c0c030e010f0905010c0c27050c040302010906 79
    0x7013540620721805807034a0400c0303000440380c0b241d4600d2001d46940d11001042007006922644108a03842d0404402100130401c205900d40100d200190020350300c1000076000007003a13412200900f038001c0020ba203902c001c40300f00000700780405841e0082200f8050205404410b80d2440b02c4054142c5015460700c0d080207040030103500040c000700c0c1c040c400c080005c5034010705500c1108618040e000c00140c80e080c50300c00102030f560ba5500030540c51402c00c00c0000c010b003001c100d2991203082c11340780703d070501c0049082400901ca4041c400c0303458040c0c0c01d5400511171041d08400710303c4034010000c0c40b6586021401c80301501c2140304000c100c0a4140c54220300382003181154100e40814100050500c50f10008030301980d682c0044c48000070081c1e54003804050700000b1040b100362080c40c0060f101049040d0181210001c0e0080d241848214403030ba2003004462000400a48100d94006081e081c0c7c0d00c3c03400141a1b40c0600700100d46040070b0005003181014001d0394201c0f50169114030100d0300d007900036 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 218069361 1250 218068111 218068153
    0x105150706090b130501060f14040213080d0908060c190c0303090f230a050601090902030a06020406050301060f0c151805060f011a0c0d0e030a0b010b070c0905060102 73
    0x445000b40c6070b034429004522100308091007800d2003665420341d4440d03441c085003150001d0b0408590051018000c1c13081241141c1e03034812264068138010b07a5400a4071074a4404003841d80719102b0b602c228850546c001d540244104121420b100031958143c8030039544100500a90368100c900c198084054010079103c3d00c81100074900078240040c1c1d0090603184e0001c42d05594905840300c4041183c160307c442c41d081c020544078440307078002c0c0180c0d01c3c141c0d0b6101d407928418030a0304201d6450307000400030742d94107004140c2c040c2d0744800700b15603c81d81c40c81c015090350401d01c540070201e1409000400340c1c600a5039108030b000ea0010815a03d103e91074a0785e0000e0504418001c089405180440001081009454060007142d80103409a616092042c00b94250805894090503001e101080c00c0c01400a03480c500c622040c241240c030912107101291070021a440040c0540085030000214404400c000780407c90040002d0098503481d4000b02080c0d502c181c1301c81e40140e00000606054110141ca8 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 218070611 1250 218069361 218069363
    0x1201020919030f0f1407090606080c070c0e060609040218040507020f03030a020a05190c0b061206010b0a02010908070303050108060a09080910050c1014090c0102030403030503060307050d05031b0601051507 90
    0x780000102d10300308041c42c0c8031564200301f549947e201028450107030090700385079101580d0001c2c10728000c182d6542a00f03010292148002c1041d111000c149070340d42da5800c0d00c4514a014000315250850290b4141c0624a00140d480c00341d45404003081d80544041501400380241c04000d61442c2c80f450620002980712207400420003d080c4680010003221200480c0d100155594101e4502ca0700d0410066042020341050700c92415042813051800010a110381102d948000040d250a1007c0050703014080b40b050040602d039000031140c00305505540114141c44a01d03085882543c1c9862000c1d040b5001e0b8480074041e500c0a20001049140080140c0304c0e02226113041c0f4180580000503030701d0500d02000241410b515040081d151f4540e155800d44e00641c41401040c88440d0300300042c0d00d80c070841c0405420480c00200040c03c40e2800c020000041c80d02400c4000040c6041c10307c3c1d9220b0300204803420640c45000c010750441000091014143d03400142040905980c0308103013845540300202c = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 218071861 1250 218070611 218070623
    0x29090406030c03050d02070608010602072c19060602011a0405151e0f0607030903030c0303020f04060c1208060f010c0f060608031e030c0307030e0c1201020919030f0f 73
    0xc80480041c00488a840007548998014544090459006814803805070400c3e030401c02401c004215841c0d0020b0080101d4034000c0c040071220203e48542001a00d00e015400e115031030690074011401e82091a02e04445039020701001800c0d142d41c803c90a85d080700c02e01a90700581c03080150907900d071580c0072a030026101c180940b140d040079808a54a118034402105107640c07020041c0360b482c1070020040c1d45000c801c90b82546406042c1d40e0241c0130007642d02019040200c9010f4600401d170003541192007403034821075003685071a41d440c80106100701c200000ca03011040840003c06260050034800e014900040c084410401b1290044076444d4054005a6080f05484007d402282461080e40c01401521004e980d441e03506104482500c0801c08078000c400004108015200440f0307410b40340c204000780790204e0310054141c1041d281c103079408a00c42e4042c2580100c0700306140c05500815808070151407100c4c2004452144030126042c40c8009400205452078420024051440b03100c0e2051240c2 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 218073111 1250 218071861 218071871
    0x70611010c050301031e050a060e0d080c1927050a09020c071a090604080c0901050d0b220506100501031b0503130804031b03170a05090f150d0f06290904 67
    0x14499a148c00c108250903202c0a540c0c44005600041c244140c14103400303e41000c0200e400c01c0c01d4162040d01c1004c80044042c0002c40e005102140300c2d003116031401c2c01c5220001c280901d400c00f0003444031000d1142c0da120b068200350026402c09a4002da500c040410405071004134a002d00c0c40c00701c0f4030400004404000100b00000450742d0700c90242002d00002e8008001003e05141448400801038003d17510407440701c001800014902000c0e00e80c0304040c01449440505a01e40c0691280640400205180900400c2110011001141d801160b4007681e044c4031144407010b0030080b0100360018100003407420800500c8140c910041200b00380d20980d200d40c07400c0e5894554041d141900d41c03039030380c1001c51544104140003a003aa4480c0350100300446d28942070358200080c0c460f20500b00035502032104504040c07070540d81d15480c122a6401c1075956603481500501c50001807480c0100c1400e101d05d0040c0120701a1a40081c0029101101d4540c010030721242d560803109800c030282040d4055210 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 218074361 1250 218073111 218073113
    0x90e160e0a0b0f030f09060c07170417100506040e070e04110a030503030916060c0209070309151d0609030301060c11040204030305030a0b090903030604020c010605060705070611010c050301031e 85
    0x514000d20000d0f8a94140503143d007070922a0080100010781000e1880c0c0c0604113000310b41040d102160040707507000d40142d10303ca074101488200f900640d40312241480300c1099a01056101042d41e40416803500000c015903940d8608100481c1c02a1040041a40c42910140050280d03403001c181c200340105507500b182c0540c6400280449920f400031135060704080309201c07007114104605180c1003131800580103024106907004142c0071642e100070f0b22407215107011484640c0a80d012400c410341080d1b19000c2c8424119070755028042540c50324111200306607089050080210b2007034007544141c80035503c0c5904e042c004681c806a510030982e0344602c2d410183e041c2c1e0b038441c4000c04c01540f10381c45054492600c8031301c40703003180d0880d04928010710422041080444000c0212030303110008507401a201c00000b502240102030f60b40110f03422400c00280301040c404005645000c844050350340f055005801002c01e803d0768521548003021803401e000601c0000e5052640d40707582e4000041c1801c4003125 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 218075611 1250 218074361 218074379
    0xe07030f05070315020c19142a04110a0c020a080d080402090c0903060a1d0105010b04080d02030c0a031d090f160c0506191b030c090e160e0a 62
    0x8031035421641540311032020010828030203401d80d008084010b086042190029125856462086101c2d810121500c401c4c01005113090400c0100c480314001c54400c1300010914034080b00320590038803007841080708000c41d00d160174090102145024800141082914a01900c10408000381241c1c0151300c41c83c0401c609004000c4000c2e004031982d24010b6904040c014000b5490f000f408140054408220001603a00e0016406801440c0c5481c000b40f8080d60005007103480b6441d0921000650038800001500710000c0c0140040c1c40004d01035410200900100b80c1e524411402c00310181d0300010084c001290080b0840a02030054444908018001d0400902150021142e070079444292200380010314a0328400201041c00500b800801800e01c3e44600e50f42d0b06000f440205086018403400381c0400c8142c000207000041d482990641c001c880201801515101d642540003d1551100082d00e0101001e0f2074012400941040d0800150b0ba1049511410400a03140c0000740c680c1c0c002600da907 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 218076861 1250 218075611 218075633
    0x709080a0b0f0a0e06040b100503010608010209100c0b0115090b0d02030a060602030f0409050c041d150405012d0503060a09020405060f01090b07170a03020c011d07090e0703 76
    0x407080040ca031491502d10b03088180410301500e00314240c1e242541440c004440080e8040d00703c0e42001c0100015601c4030300544038100d13140c00058055092140c0010002d80540140c581150100c95243c80444408030440b6400080180600350a0b00d4100400441170403c1c1020724010003464616005030315030104040387e5000180c4404840e600000708040740060b84144c1001e04241d00c045c600d401080803050340540114010515541d80d2840860618816441264010401102281c074641e064402500180200321342220400c40254044c0030f1a140030701c03a040c10f9808242500c0c031100031000103044a01c0c50340340008810390362460702244d40c2e80e08001c2c0070710400c028030700400c0c003003218411301c010b5440150901e809503080303415440890780c01c03280039015511043c449075155400c0f0b05040e50081c407140e09010300d0017000114807500b01d40c1074005104180380080203010811f000311800300750480707110604c1c105800090040c80444c4107900309200040c400c00c00c81e80e80e103440b0b840d049600700d = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 218078111 1250 218076861 218076863
    0x90411091b04061d04050f070e010504030c06021e0d020706200a052a0a0303030e122107050a0e0f030a0b010807060906090b071e1e060b0d0c09050709080a 68
    0x450482c40702044011001381c00042010a44092016007042440d0310180400076051600f80f0407000300790306c003c0e403207507094800940e00b00074000541903884602030744400312480f240b0f10040072a06013a0912a00080700c00c48002e065004158144c945041250f01c00714000b42140191500f070140140f0b034004001c026942c0340160058403d1043c0c030813800624922411070003007213540501c00c001c02640c554113018102c94040c00d0201d0050001000301381803010304030450b034414901060a088e5035840f1b030303c0c072466a0715210540995840c0d80d42d06640500516100c58009103d044001049007006800c401a03014007404030b40031a881542d0b10082d4420980020b515640a20010040709500069880c01040d0500b0400d035a1410404101164402c0400150191514900d0582e40c0e140303000140344016002018000481c0601d106813840d0104100190b44090030b01003010710614002e03001416007607001030381d19499071800c4829000b600000b82038906001c008c2100041018003440421030003 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 218079361 1250 218078111 218078117
    0xe06190302030f010e011a1e03150c071b0308090d080c010204030510050a060602030a080c09060d0b010905060f0d050405010e03030c070506010e130b09070f0801060501020606090411091b0406 84
    0x604511700315608464800340a014100c9028030b10f54960b1300e41d04602281a0511040703100700e1703444100840e1524100e04009149449582c0400ca0071110700405071003d90b1083c1018502040208503541e040450380c04064640e040030000b05055140070804820031038030960701c03241804c0583c40c03d50300720780160f842074485400040c0c2c04000e0003010310910381e00c01101c140422401c1d0030940003c1d82d0f40100c10740c04051003442c902081002000030241c2e81c880d040146103603075a0742c031940944040c0c07540181d41d602213442140c003c90503180005c143c90300070305a00000d5050086441c0304001914010340b0aa43d29580c1c1c3c600582c1c102410b10046101d541a1007205954401c640b410502c0c10744141d100582860801b401e1024810982c0c05580c41039401140c1c016942d1602c2c0c82131420700546a002410950740e100c40040d5000c1d040d040340045a100b6029191140d0380c107418080004c00c1110002c20100789454010030a14103100150b8110440d0541410860304800701d00280e40c0c410380210004c = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 218080611 1250 218079361 218079371
    0xa0504020c072d0510090503060103080c100b060313020f06040b1c060509130201110d0807020c0607020f04020f040e0114120a02090f0601270501030606090e06190302030f01 76
    0x4601e20081c07a0f80b0400da440305a000080c5851240f030400012940240c62194140007005004c1da84242c0544024290060654006503503d1405410541c8401c071208500e0203480008c02880e4900c1c400c44901c2c11010340800e1a6a4601a880e015840d0f91307642245d000b004c1003c0c80c0e0058462b8030190000e441c030400c60035641d0407540150440500c030007900039500c07800c00c0381c280121348402c1c40d5560030007081050104910440d200583e050440740e0030401840c80b50b10441440d550748407072102d000d009903809460080352800144a110300c6480d10194000d40e40050717490041c10654011b01d03400b0001e039025030a1948401c0700307001100e0280d0141e030b2a24840140070001e0b10301200070320742c0c04e0608001020fa4400d1036010a011180041030900746103038040014040740d00815490000758181d640000da408440401e801e0f1800b00b034001c0c540080c3c81c4c14404502c09006840100c01da520f034211242c4981c4d074070020030001c1741c4600b07d40c6131030010074400000140c40400c0740f900754411840002c14 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 218081861 1250 218080611 218080619
    0x9120f03040c120f0201080a090515070e0d0b042a0303020d0206010b0307120c1e02010e0c01020303070c080c1c0206040203101b030e01020f031602060703050c090d020a0504020c07 79
    0x11010600c2d040941e81003d518a9907001030302c82203404c1241942800c0c103070b49550790780803100d0051509003c0170b012800f503800e03801c0c041107424100d00d100f00c0c0c0d152a02c3c003040d06224280a00101c00c8100100080c04120125000c110400d542c0469401c10910250220920241d5103421078229401140541d00048410040c3c0d501804068050001d40944a00310300c0c01480091007041607041c025041c03665001d0a004e07241c400c3c0c030b01c0328040ca0b2550030388051001d400e4000b40282100c40b0503214030300400032000240e6201008403401f450702e036070380e210000201f525118401e0f440705583e01907502c107502c030b40c05060040d0301c0760700b494900940140805140c98018581048d0b03a4100e405000c0c0e180103280907844610543c020160340035894006001200010346c0342c024811a1450080ca030702c08000c20000301d865000c0310701d02c43c1c0140c0c00e5602c41e49034020150203440c01038400c86000c1d281800501c80e181485101ca006060004040c4142d00340c0c1c6601141c102c2e402010301c50000c1d001043c00340 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 218083111 1250 218081861 218081873
    0x703050d080901021306030f0605030d120605060a020c09070e030619050901060f0902070f0206040b09011710030605040203240109062304020901090306110304020f040203071709120f0304 82
    0x6030b03114440000a510307140301d2800b4100d110325180504424035964407180303100c0260036400300000e00380250071503161162500000e4001080e80e4056820207040180229880c2001170540358102819001009035019180411219901c01021a41000303416080403407581d600f00a102d001c6c81150003800d1070b041c820b11264094500040c000500c0341c0c1000d9042007a80d0010a1217000c483c04058010b0f15505649001410740c015a800030754051030220780031801258100050000d440240c0701c180c1203513560180301c642d0002c21a4000d07140703039400c1010008294190030440e4441e20040540380103001801d043d6240290040c070604501d50070301d0050112085d17911170310700030784500c5410040452564440200103024030010700d0180350003141e114466406129144091544a10180004100da070000b40980d00201d0701a84200c0342e0340c03a41c4419090510869000d60b0703d0356030341d0307002d00c40c0901803002d0724401801c1050644143e84411540004034009030072003400303206071705a4a00701814a8 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 218084361 1250 218083111 218083127
    0x31e070f11060f04060c090f03142503060b040f0e0f1212010b0d18050a020103060b07020904020f15040306052a03070c061d0604060e0102040b0904020d0204080703050d 74
    0x485040e0303004900784140c40b0503d850040d8001e5005102080c1c0d02c141c85011502e6119541c8140c41c41c58809401004000d0403003650b10b100110601103038096621140c0328030701c3c4e001001c540051603009000502c0840d1103a0030071040b035070001c0d0010030691104810b0317004461020600d4a250f411264a400e00c603d0103004011082d0910080c450400200b82106898148103108170349064000150b01c2c4c1d007003001900080000804403207210a41009401d000e07845e030080001c224006494007402180b0038642d44103851f440340c2c018100010325640c03642030012081030a1321480d442800d0f81e108140740040d40e0f000f04059445160302203582d08013242c0c042d106040410350001000c0a004800c46204c240c0d03016668070580d14903180314000c1d00e9040c550300401040364107041c07603246452580c4903e5400102d19004501c81c810400500e8808a0710b507080380160700407030810810400c100f042d24030301600640840100400c00615041d5103103802d51401180364400c41c5c09411500d808a0240d4100340740f = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 218085611 1250 218084361 218084387
    0x30708090f010204140108040501060b0f03010305070506041a030603100e0d030e1b0d111003020910110309010e01090f06090314060103020307210c061d03010902030c06031e070f 78
    0xb0740c201420844805007681740304940364100600800050140002500200001d003540c2c1540340d610000346e005100c455100340429500ca01c603401000926042c0001103900b211318078119620030b500c3d50b80341c140456201924450349842050512078000c442e074400c1c886500d0f1030b0402841c4155500801030180d81c09000c50101c00e4001105d40601d0b0aa94501ea40868504403902503140c2280c2c548528402c00800e03419030018100d000e80f4000c1905a8020305c0c0e0090102c4500703903040703992202250840015402842c0b00d4005104440c0749501400c1840304501d03050619001e5540c894950807080394071340e03000400044c0302c0c403c208107008508225101c09180c4001500c1c04d5811500800c0e40c42015100d521420610745908156101641541403400c2d580040c0c116449603844900800d03407500d20040781c1c010240784040c0502c500d014400c0c3c0084c02c2d805405030212002c00e00803c4215000140340c80f030801884019900c40c1207280205610800381920789000702c21070804018055a10880 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 218086861 1250 218085611 218085613
    0x80d0305130b0403050f0f0403140d0c031b1b030308060d0515070c060e06060f01030614040b04090b0a021818040f2d0501050c1903021e030708090f 65
    0x40c40028110030844414840e000300c20303048036888034134080310310384140c0101000c04e500104200d00203081e501c0c010710490b4024010780091100c481c800d1768641c820705060401107020200704500007401010404100d4220000402c0e0040054803800c010306005210900400f404d0ba405104140e0030260903a040300c401e840c0e4074841000e641e06c10b941d44c01d1201c0e41d0310300c00c2c2012001038000c5102e200c0f4081c801e580142d0510040d0040e5500c00d54a80c4141da0a5104030241a111307030303095119100314800ca03103010817450741040503501407000400e0301c001400c0d000364030b507108800414601c2c64034a001d02e060000060742c070300c1101030a140165251007040c0c4112803c900c0c80307032044a00e01000c0d81081c0c014682e00c180035014038021117800980c2c1030301483c0f0398803030726451000c0b0f0001d90026860340c001ca0090240360385240360700c0030750710601c0d003020106c0f10020b503d001214440d90180c0341c0a02c0040d449030b41c0240843d80e10b903058100b2119040000c0c0b85408008510000744141c64500e54618 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 218088111 1250 218086861 218086871
    0x14070510050c01060f08010c0905030606030c040506060403020d051c0302040b03041e0c0f0501120212070503090a0b010b07021c020901051504031203052202010206011a22080d03 78
    0x14400c550518104010800c0105005400d850b081d03200030010903e0640406003240d8426140d4064a040070000300440e070644e81c0010581070100e851032041d07400401610980a03103100300301c02444003410380c48d0003820910000c00140c649038a5029060f00450051103580fa02480e02c150803070340d14440d4810140180b01c1045180ca500041d6600b040c2d100114240c8070004082c1040e11300781d042d0780904901c22a00d40000e5090048038040191503080e80c44d01c04010340341c0085c3e01a44588400a080c0c1e42e603079400142070b0b600c42c8000d07540114440f0300f500c40882c100d03166502c4540c02038114950b440b4000520308114507000e1604009204202c4003034200041f56000036183d6401485198060181080001c8100c0107031070448010319403005509647c4908800e001300240421508444044d102004041c080405102c8540f13031154168014a0b00f60300306254084003900254000b0440c000500601c10800901c1901464035984c41c81420075031807814400038030b040388440d61101454548 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 218089361 1250 218088111 218088119
    0x90a05010f1e0b221a12070302091306150302090f0907173d06030b0d1e0b010503070b07110604121104061502060109020c0f06011d0a0501080a062a09031407 69
    0x20007a2156100282801c1c05d1b2aa40c841082c1d01a00c00c1b088040c0d402511018000c0070301045511000c103440c004075500110180d0420150124131a03101515807119110711100725503d00280c0141c1d01c00e02510342003a620f80b00701d85641d030680d01564801c0340f45481c101130b0b21049007480f40d81f03810b003102c0d003101c841254044405110303904c5881c05854205910741200700c68903211040706121150307000302c403143c0003070752000c18100310044604100c480340d080c0300000480345000903400090311209210170749806000da031243c2c0d000010b08601d0750400f105101c0003484d2481c030b03520101514082c2d003070030000b040e0b51000c0000300d91494002009550b49031002d80e45150b400a0518107480c5070500069031030240c0441685855400701900c0400d1041d4800801c54601161003c489032404954031022510341d842401c05444090040c0c101c1c0f0740c002c0201c00c0100d0255040800c54012190411421241c00c003090984e009070420080701103000701d40c0c10820040c841c00c403496003000d0a40600115420 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 218090611 1250 218089361 218089409
    0x90c0e060301081c0f0e0405041b0308090405010602010603080d02160c09020a03140714070204091202030a09090204030b070e0d052a0f0a05060c07050607030c02090a05010f1e0b22 79
    0x2080511500481d580c1001404010003e602008040311142114400c031340d580c50f2033221f0358041030909001c0c034105400054003e00500580c0c0599602114117818000038030540c600941080500201d000e584070805404107250381d0a82000c1c000e0740c840036039500c4140700082d05544140e0114904021410200100706a022040f1001d54519011070703580d440f4540001406414940c4025044c00f08076985480d50a4000004103100300c1d4071b441e0041410341d1010380004030b008610020f00040003080026008500c00c5411008108004002003101c0316103844036464030880c5444249842900c00d40664070007896520600040030498800381000c00f40c90200300e0a4800740b0441d8012403010820700544c2c038040c4881c0025150284c4501c1d00d4200e47c0c24006c1452010f60000da01445603840441d84500860241605072100d05121200c0d691900c44d903d42201126010081e0030400c0c6000403a40040c400000c003600300c051f00d48600089901d0408516240d000da02a08a8030403d400d6a045054 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 218091861 1250 218090611 218090627
    0xc031d060105130f05011e0b0f04060e010201090501060f051309080f070c0909080304060615200304080106030c0e0108070e0402060702040e030c0d030b0316090c0e060301081c0f 78
    0x1c0183c62040c0c907095052081d1000e820350b4002d81c1d80f014109000444da2500b2800e080c01c1508a6030344101e40c80d035407907480b01981c0c440c40410511034101080144009405041e046000001c18400000c0a0b036142c0c81e40ca00715400c3d03401c190f51403000000200140c1c80c3c0003562824000c448642007017004c280740d654003c940309658400000c00f20108100080c4100c84000000401c0074020a000c44030451070480c00f5640100d50840d5254030784000810150f0b071049845841200f41c4e241c0f03030381260104400a050080b1701000091030310081002084101c0c4c01c0c043c1da0000c612641304030120301c1c2004c03403000d15000305800200c42035121000800a580d20400c50981041e01640c9180c0c0e9002039002040c080c0820840403003181c0710000b50b00041c07034000656104041c0c00356408020840b00c0c0342c10140c40b00340c05044010201d54010b030a000c0c04005522201c80f1036082e05040811000711408550302e50004d9200c0d049541100c0454410130041d214400e82c8040e45144c0380441070320505014021603 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 218093111 1250 218091861 218091869
    0x131a040e100b041116061404030c03080c210108070e0c070b06030c060406050309301b01110a020c0402090109030f03111c0e09010312050c0c130c031d0601 68
    0x5846502d1070185441c2c0340c1c0302c484899040c01c51207a885603a0f095a82040c41d26441c03c40300b0b289482d0700c003803800c490011002d020301c2d4950340b80d12601c801d64030202d8042c6805080281e6908041001d400c08a40003d421004440d006401c40394661400e0400784c02c084184c4d0055028040f800200203a040d803c408855815038840c940c010b240c0c4840000c24500981d0b80f0900c0c3d00610000741c0418030075000070185200c0c0589604a030f1240c103070005080c0d079011820103a58240c001c8a500040d101c0c070808050010450b66080401c4440440007940342929840302107820401e1001070b40310961a030510400e81440c01c2901c0940c64103003c42d0008101c0a00d1780300140080d54962604800c0500c02c0010340d0085a4442c21280c0200104030400385c81108180341c1750120344142c005405909004468504803038005082c0c400700007010200307540b6680700090742c41075405095005c03070783ca42d10050f041d14141c400050004005a9801001d0210344054010a103000307403290103941003180c00603100303042d1 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 218094361 1250 218093111 218093143
    0x1e0903090e0903120709050901060e041515031e05070905120607020a110613090213050306010b0a0302160c0609091404050d030c051b030304060605010809030313020d02131a040e 78
    0x2c0c1d95212006c4941d204150495907016600500005070650300207481024500708880400044400074001c165403119403088410901e003400b442200c1c0340c000c0d44031400d01d4003164104070503034402d14912411104111001c2000c106907040611150a100c0454011703841d241c002401c05007070100b00a541d030345030000001d140541441244001d51540c3c8141c502907541c4041071404d49442d07103c050040e402c1160200e02814203a0000030b424600090454101c6403404412803030b00c040380718114040d500030281c9652129080080c2800510302119800c001e210541d9261003160030310341e014040d5859a00c01c404411844000d100100e41c0201c1d8030b0380c414100d030138000352403400f01c54113983e00d014442010f203942074410015201c26902000031032150b88200000c00c0310548a400558204030181d40c8070609030300500c0010781c2c40c4403c203c0e000c00b160005000360116030899001943c10400891210b06190316101c840003091610b1207004401c113000c40d0300340640040028015681d105040e071890324 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 218095611 1250 218094361 218094397
    0x3060e2a0a1806060216050a090203040f0c0602030a02060a142802040303030b0907031e0f060b07050a06050c090d240c05041d06090c030a1e0903090e0903 68
    0x40c1d5a440c0c0c03100000340901d0b81028050a05400b440000700341c0c5100d20005806980b0301c0e0b041c0c03600300e5085007080d908010325800d105c0303082100d41c500a400080048540400c915944404144031900703280051401da4019a03030341c40480310003400c1003c06000c1c541c1c0c05062291040c00e0516082103160f00005c010300c205440c00c407a907850203a158441d0031a1208520000700070050681c150008207181c00c0694180c1241d8458110441c2243d0aa0003895058042e000d0640140d0071290031501e03810040c6031000c80c076280c50351b9240780ca40d884000101e500354040c00c2c5440410100c1d000f80c9038823030001141603007891981004102c094406903002010a5540c007140c50300e9603896010100c15000310f010800454034201c001512950050040840d800300115031058522000c180c10f9100300c2010380510b000307880d40c40042103241c1000c0d04c00741c001a2101c03c0003031521407030083e0744290710501c100031030008a241000f800d41c0e41c0b6900000d24402c0317a0410403a10010000440c0c00790000c064031020 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 218096861 1250 218095611 218095693
    0x90d0e040e120a0912021f23040e0c0406080c070305040f0e0604050a0516051b030301090504030206011202010203120702100f0c1403060901050111030d020307020106051f090605031005060c0703060e 87
    0x1300d5503480c038404552491aa032180c0319026823440900287c1e1869142030b48141c036041542042d50049224400005801c500003038100ca8852010b00303401c17880b90a04d14109510b40c50100c0b00c10489401c1040d6884ea841d040042614150040b82d40100c5508000c000030f04001070900341600300341001c241406030000d81d02100d0440102101d2100700c0c064181e81d200e503194080b0501501d020364054006125590000c100d521210706032848644c6d058000710f00d00b60b4400091a42c90390010618000c0d40200801d402c24290940188514502d0540c2c0000d003003080c1c42409080010502402c0c60480001e0040008070744072500d40394155030003400c0c1200542c158a4500b4a98811192642c11060021051040c01c03074054122100341d6104070392050b001da03814007400b010704030174504150004841d40e80402005004070000c0d0781101444ca001c0d192140c80f50007156030f541c0701012100c041e80c0a500100103014007486170340d00451020000d0318103103540c0c40d8012002c1030b802d6240f080801760303c18098 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 218098111 1250 218096861 218096867
    0x21051914070e180103080901020d020d020303011203030608010903030e011b141b0f0a1e0230070e0a05010b090a0311030a061d0c09090d0e040e120a0912021f 69
    0x80469a240802c6040f41d0b8403860140641d4001c05241070140c4111416a086180003080f100c4a800700355000f1401c5a2a0580d082c114488094091b824140d44e41c07004600000d082c00340b1021607009031400725009510740350403800c60f1000740d2407007068030588140c81c030005d90010030a405c0321902d80c8803e880e0001e244102011482480d0048a00c1c0f14070a6207481c408408101c081c40d40740140c10311280030105600345680f602045000940c040d1880c0300325201c1d8070561500507401e26030720b44030001e840014040213250101c1a004030240c9031a401c00c0101d00180350080a0150902d4480d440c10400340b8400314028040c1400b0060001c62045104032321500c0810816482c6034200720240051f2071100040d1001d04081d81da03660f41400344411038002402c2642d592802151b0040081c08090700800040f00c0859450304655802515201c464a550341d0802203081e580443e586d803d6555091908040c1c2044050342c001091001500c42c90340150783c03001032940c0c85045107001c605c030448540e0300071 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 218099361 1250 218098111 218098129
    0xd050106090920040204030308060907110d020a11040207111203070213091e02010e2403040c060f090b0d050a1e02041a03010f03021021051914070e 65
    0xc500024034040181c4240801d400380c0c40740444501d00c4882c080b0f51820240300c164030032800041c01081c0c641011078942e09081000daa4440c2082c540b40503044200d403c011b040041c3d4020310001079001821f6402072000140d0044404101141d00310318014050782d6003d800d07444686107031305c250115801c01509803001d208459529a006241d103000014106002005041600d81a01d07028820a0140d80c0269150308940303800e0b405031510301940b230b4034008009072207551403a2440070324040003140c0c512482c640065030256109548100f0082d0a1240040c02000c941c09103030100f12020500b00488802d5008440c03001804080111b001da69040c071600103407208900c0340401052a05c0e080000d0b20403903006d4400c5d5180e410f103040c80c2c84540c00100e29213003c00c1c002c9820700003004c00200018940540c5d410040b800c107040000800030a10841c24000c1411281d01c042651200e08002c18520320301903010b80700c10300440800c0b0110300c000080038001801868001403080302d07040407000350307102121 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 218100611 1250 218099361 218099369
    0x302031b030d1112010b03060406050d200a0f1a090d0b060f040e03040b071703130c0b07050c130b030f03040306050108060708160302130e0603120a0504050d050106 72
    0x4220031440c1010082650307503000008940b20245000030810780c0c1e450801c00c60b0b40b1140d4102100007107908103845144258005031146910583c0d4074000103054440010200c601809070070020212040c280005c10308a01f5044030700e201c0c00c5c8440c02401b04c0d103840050503081c2c6008a0410640018070400c803c0c451042d000d2041d80812040240810007031a58007551180b40c0c261150580d828a0310203103c16200910050032264105100600440712503401424801e40504809034160588402c054070651080e00e80c1d161241008500d41d042c00b116070181300081031400d40451401c501030300d440740c603020090145886580c1e49480280008250303080407007512001425604a03906c03060b051640c0303a0040c80200d4404c2d003450000500b149020030110b210300d0b030a031291718103940c0d42e20b02c2144000780c0d0010b0368181076080c000201040328107500030000c0c144109480c040760402104152070f220107024030030202c0d4400c01061140591000c2580e00301d90080c0c8000008a91924141d4098865500 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 218101861 1250 218100611 218100637
    0x12030405071805090f010e0a0201080a2a020c06280c020406170106080307050303061003020f03040809030f21090406080f0c180103030905010c08120106110c040b0913030203 76
    0x4103030a422030150340218040d1500b41c00325019817075040070759400c1c0d640c0ca152030070403600080d40080155000723191850344440301c2c240003c1c80d0000303440c1950818241c081e205c0c48a90b65a521001102d404000c4100004411515603042c000011100710100c54501c0f1194061695a81c80410507070180f00160000e50b40140244541925004240041c0020748007400680d03080960025503518088210f4800d5a001005180781d40c0e42c3d4420300171440b4220a0b0041003590820400040030140406140180d1140c406107a071210500f04152400c0e413909000c0030260001c0d1500074050302e8040404085a046102180c0c4038030034040020000d080c01da014451034081c4001d00c0813980000700307041c9140300d82140c04215500e20101e0070400b81e682400010b0125514540a03c0b05600400c003104c503462250b0803544c504070700a46615441d18080c1d010303030003042000c12803140c4140140960800340f44265410072110782c180c0d000403038041026141140681c014091201818804e00032544210007000c = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 218103111 1250 218101861 218101889
    0xe010b040e24060d060203060303070606090603020103061e030605060102031b010506090c04060203030708100b1c0501120c0e13170901020d031e0f060515030402040605040903021203040507 83
    0xea199100e098240c0425044200c42403103014044400381c1d40b81c050440500f001d0031024080d07507114001e40c400340c0250350511042c495800000c1c507a00421018080e24000031414a2031440050261002c0303400003821020381d20140b00d240109418640120783d080307400030035280c8134540140d0441c07084d9814001454048001005400384c15004103002e00c905880b6646203640306042583cac0c0780502d00a82c1d0058100b0008141c40510651000780c0011074100003203180c1da9518072800c801d501c451003428254603004a81c512141080c4101c0d070051000d101459107201c080d070303201c48400d0031038020043c7c02070091011440441041c400680419032100d01e0001e03c60b145403c092983c0c0004009900502c240c03140401554882d006805002e0340344139891700d10641c0800c2120281c1340c80403207440e01598582001440355164200c00c036281c1c0380030250951342d060a005000650782c040e0842c9021310304000e49800041e90005030048501511003e454403901c0d03a2804c103003410029401036032045005 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 218104361 1250 218103111 218103131
    0x20f100e13090c050904020a060c150e0f010608030f0403030507110402071406150108040b06040908130518040f02090a0e070e071803121115130507080a11040e010b04 73
    0x550b105100c0940078085800509580714200030240000300da00071340095414000300002400b400c1809940351017110421b42c994400000070003100d020f602c20a01030f03441405202c50200080c1f20f04005041000042d524050702041c0c07140c101c1c4a80d110040070001d0000744902031000c40a2040d1154a00402c19560703003a480c205480380c42c42c0c4400000c141d0081002040d80700c05e0b403200100c0c1c1d030f0700103031245d503011b6903591200000340d1030003031802e40c010f612100514002440034008040c03603a08188006052400d00c401d0200444000020805c1e2482900602020510841c69005903e5044a00324801e13031710328000c1005002c1d81020710280341314041d40481c1000e5075140e40e5100340311a0b51ba840c648156a000d4050050540c400504152010b41c49088100e10404804049100798812503a0343c4410021401074800c0441316614200c0000b0084c1042080c01c0c003010004140990090401c0c6500b926440c44603090f21014030b22455403007444e903840b0300c420342114107403000003041003144c4268 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 218105611 1250 218104361 218104399
    0xa0306020c0a0b0c03100302041a03060a0510060203030906010b0703090b030103030503070e0415090506180f010906060906020303061c0501090b0f0106020106060c08091903120318020f100e 83
    0xd070b444226500201c42c1c002840c8400904203580c42241c01144440b2039920310740910004080c54070b25031f078491655044040c03064408028560141045a00000c0c0030301d00120003500403011500502c08540040042c005110700008440c1c3c1510078410034195584a1498152400d41d495800000c80440100002052640003006948503000300e03115076606012800401044455070b240a0340e85810b103000520074101690311150703000e03401401131124400c0c000a10b907000075048a030011a0a2450014002c00d120b23030203010002d001c00d046c0441c8903410100c01035240e00004014900070120145540392050210300805e0a00780c0010081100710758604209103105011281001000c810074000140e0317074414402c540440d00e590f51040303a082030a03039032108298082e0140c540d101c207824110f40d0304008407a0702003005620540041c000719002d18805815228001501c0b16007208040660340980c481c60700200c0c1c1044120b540c210810b820341425548480454882034002d008800003460b25a8 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 218106861 1250 218105611 218105623
    0x311220c0e010c15110c03070605181606121b081b16060902030f060c070303050906060f0103150f060201020703030e0a030509120312040b15010e01020d0e0a0306020c 73
    0x200c1a5181c48007410744100658583c80f5040000b07010310342d0044090440656070b8000880090300e40b07407031440c0c014990209444d68200320b0003615070503541d00a201d2000c0c12082d04000203c40c0c0c00103020310015481e83d81d074036100a8414401404540e495044150601da0700c02c004040110104403a12501408020020102103480066140c1c54800440324020040c05030303040e05002e0800c1c42070382c0b07640d9640d0001030304d0b42c90320482e0940301c0c1220001d0701480900890b8444e4007600001d070f4903410141402410707550060002e0071250802c02c1405101d4407103102c210b02e80708d000e0030003107501c462080540307901120a9103c45000d04640c40c011440e594190010045640640d400b44511403072040c080f6240c034100fa4006002c108100115003c90610001007400113101c8000d81c1d0600803040c1180d17503903650441e41110010502c070704001010102242c0581031b1a004e10f004100480f158001035074441c00303c46c8920501944429066640d90f40802903c0515030040d0155250314000c40e40e41d540341 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 218108111 1250 218106861 218106881
    0xa050105180907050d02030c0301050f041e020a15121d011109030304030318031b0e010801020a0f1b0c080607090b0a09060c020a091503030e0d0804031122 68
    0x28003880d4041101000c0d0710446000308102c0c0e024101c1a40741100700305090340b03e1101217825005804000102c0d81d0288030b00b51041a00d40040030040c41c152608400300f003404050b03180003548840c4c1100144e1615003d81e025601c070601101905000b095080d210b6214000300d081900d03090182400043d140000c4120302c0e809120b00174031800242c802c179980140030b8901d00b1a0103900c00d120400c0400d105219004c1c42d0b8410300f0603040c1d030700e0b1030380c64683d80c805212141917401a110a4104040c00c04a01107500500981000b1030070810005c100824030304244d20380310100010710803400041d00c08a525079100a9000078500e00e0716948080064540c8800c035918800700300b107000f0020320340700800e0885810035069500c1c01105420301d02d05480000c05004240d801120480010441c1d50440c400c0c01d250b040300b2000f0000032403440c0780082980b03c030508107134011a03210301d03401d0001b021300c0241c4065070fa1114010b00f4031010100411110310b00c0012040200c2d00026501000108aa01490801c = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 218109361 1250 218108111 218108119
    0x7050d020309070e06010f08041502040330030e3703030b100306060206040b07090e090a0204050903090105040e04080705030708040f0506070b0c0307090f0b09190509040b040510050a050105 83
    0x9561045c0056444400480c25140440c104600103400211a0360f0600382c40c5101034401070410342c03603403180b443c181050b09803507142c88044009001c501801d1000440c07030031a507140c00d0011402814a482c0c98270300c40b164426005c0b0140040790340075112030404401c10380303400902400c40500350030020045d09000c00a540201414580a00c2032840790040e5000e55506800425142d1281e5640c058400b80040c480d108000007200041900720900203410302816060006200b0310310707540100011030f0300c081c0003aa0564001c002042d0b959801c1810b40f0211044401102c6040e504c508000e1403e02c21050700500030300000a05c1e400300580d02010b4000e94800342140844203448005100107442185000f4111a1194000540603c4a180115400303800340c60021a1142e4407801c605182000ba000204030316400324103804d09040000c10540b00d200201a0a48a1440c01001c80c0d05c034600600301a003034140307440c005814850300300041e401ba4150154100224500502104000d190a000f06849 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 218110611 1250 218109361 218109389
    0x310030b0907050307030b0a0e07151d0f0d020102030c01020d02041d040213050402010e0a0e090c0406140105031314070e0a0b0325030f0614060105040303050901030507050d02030907 80
    0x161000940070b001c0da10007400a2010605684402031041e2008050446190b1a0094241d4010702400080000c0a41101c00a00c503013445c840a0320700b4003a0018654030141401c5a00748666401705d842c640e0300c90980c3d00b1034100c2090300040f401c6205802c141c402039030000810380544031156004000b00c5000c10014107070781140c00c00c207800068051718040e51214100022040303042895001c941c2007841410450390b50440340004c40c50103040c59003d089000980c40422016403401d100712003180300103c07800c204060401c0760f40c2d01000700300c01180741000008000280a2900107500c5074480303401440301c0320344080a080030356550040d0700a0138146e00103900450b5020181e03020f058800070008014007001d40420041000e030b04038141d600c400c0d2034040c0c8400000b251800eaa01000f09000700c00c00f04a034140401c3e40700c01d10708060300341d90410104001c2080444e5000b001d0b03c2201c2000d107000306954030365460890701809514200840180700105202c102e50000845400312345078000020b03c = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 218111861 1250 218110611 218110621
    0xc0c07050d05030a120b18040605010611060a020d2d0c17150303090d03021605010e10050906040302060c0d09050111070b030a0212010807180515040c0c080310030b 72
    0x7030074540c10018050f602c1400304400040c043c040d6158020f043c4000010380c41746100000b04400030b100034512182250101303100501206000c0c103805004203060140d01348540c5201255282c0b0008d0600150542c04500b0201c0f900141c0c107c1c0c0e1070050b00c04941c2c003030212050304080c4840610100d00c0d03d010310700010319060501030540c0303000c06640b04191801c982d031065178074941e8180250300a585400104801041c5503074618240c04070502950040610030281421404d00080c4c94000300d05210203584124581c1c1c0e150f52515446810a207000754690001c18003040c00742c00b5030f0700025800340021580d00c0e501900002c00400104c080e07610041c805540f4801910b500c107a9080355005a001100c091044441d00070085130009840c041c01464900c100086114484003a0002c0e2510781107480300300980c00300038800310307803803040400200120304003000d80c1541540011809809603454021940200b401500305400c4a5009041c055881c43c01c541400c400d902c43c1d010032900d01c840c00c00401e03 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 218113111 1250 218111861 218111869
    0x305210405100f1109040213230f1e1003060b0406050d0b01030c050415020a0206040305030a2727050a020a0f11060a02090d2117040302070501110102120c0c0705 71
    0x10200c1c00700c4030101c03407810705c0380701c00d20019502441b08081c082e00d10700b4001540d2890310041032030300340703404054402c1100ca10040024070242a010700d8072445030f80d80c40c3c88a80d0442d00080303004041c12074050020469121080d005400503900a40c8940320200300007400941240040443e85041401002140c9520f0019011200340800590008100b8882440148041480151041c80a0049910070881c51f4001001c40c0e020703800c212115007000c40c0310101a9001040c103010810b00090300311024194101e0010202d10620074105410204040e400301040c001135002c07000c20369540700740542e20f804005a03000e940312986200c0025140c03005404050f00c510740c865980c41c455806000f842d12101c02ca0f07000394203ca010340390300961a8405600103104c10742190010f680f02c5403803a000030040b0b440903142101400321800f407058054108170000e43e003c030f000015280c00742040d45042e0301d00d20079180203004060910501c010b282086c80781d0554400040c1079081c201c20121881291230798284 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 218114361 1250 218113111 218113121
    0xc030b011b061e050c0c0c0108071b060f0504060603030e01020a0c0b0904021603080906010b0304080703030f0b060d06030203100606090608040f020405040b04210c0305210405100f 79
    0x210781c00031100800c050004080d50000d450004420b4503c00341841144251421500150382440d6401000100490010801c0c46001090102403d02c4092440c003c4c0c00a45103800d03100c8417001c80d207245402c000421460b03034024154450000e10400c1a403809203081c0005100c00c2c0415808a021940c0d803401640c400500200d8050b803000d0300040c403514002c85846c09400100c0e54075401502401384c200c046039030740940d44149019698154041c103280c1601400c2c1030068000c001c003014108201300204020404a804480d458600026841c5d00c4046003030040c101c040b0044d80c0003030300042c4014599030a42003501964021410380340760420807455141156641d120341c0c0041f031120744080006038010001143d01501a17004900f00f0341c0564000743c1266030440f411121505004d06020138461590121a1444d04c031880b07109451141d2080a0b00003200904000c0800c000010041030780164000699001008a0f2552509042a150281d00c40110240e00071083e8909001000094214003c2d = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 218115611 1250 218114361 218114387
    0xc030926120406060317180303041401080a0609050c120105030d08011203050c07230406060207090b0a03050a03030204030209090c0f0906061201081b0603220c080601090c030b01 78
    0x5400c0c6880c038200c20300710596500800030b48060350340e0180000811081031241640d0703640d54040c41c1d540c5a00846180002d510700107614081d5000380411700400c40804c0e2601102c400900f020040750b9610501c0801801041c1c20001240d828181881120b0f140c08014218600421071514126a03c403c14582d48140b0100312000140c5180010001c1607003070180ba08410b4000e1400313034136000c482040c16241469641c007600c00920403000e60101d070081c0c1c00c1d411200d6001110240006440d00400a5642580d4064548810f0b9141c061351029038030a02c0b0301009552003405c0c0c461042060034094000d4005200c160300416200000854011000c910700344545002000c5542000b401810301140440060041d80c0020342040049000c40907160070303034001c181c02c0e80103012040784140da031124843d080c2c000d81e01401c0c0a1040c08550040c8214192034050001d0704952040c12034108201e01c0803255200c3e5400d070203104008034a50740c0c50f4201141038141c40d1000e010031101c07503004403280c0c3c07020b143e = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 218116861 1250 218115611 218115683
    0x303210c120b040915050c04030b04110f0319120c051e0607080412050d02070602070b0105190810050c040e040803011a0c0a0f0302070f1202030d080708040f150c0309 73
    0x2281d81414446a40229080303c400700e01503003419200c0da10100903080032fa50030b8450742049060910305d8504003003c20420041500640420800d4101045101c48150801450711110050f20b5002501c03a00145040642050846284100f1070f01d064031207400400c001d90032070081000080c1f02d240181c0f1410300903640800414140914010b045405402030b11425103043d070200709031800b1a0950000d05082801621011603652611003000b1103410704c030030804441004800d081082420204d4010003644444001282550b544031b0702504512a0750000030801a8100a02050081032005181038941e20801400ca0000841440a4074021003441149a45c4490fa2500c0051201c0c85240d0240c0e2003401240c1d03845440d81d0303181c40d40001607000241d00c0b1715585445415854200404260701025050080c0182408500200740000050000e00341d000d01e44068010043c0c1c0701c0f1800303520310f0300800c04c016000319000000c4c0a420310b180d040d0380c0c0100d4408091401c560340800d0801e1218500 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 218118111 1250 218116861 218116883
    0x10206091207020f0604091a010f05090f03030d050f180a02100e040e030a020c0114090108070f0c050d0504031a060f01120608010e0f0715090303210c120b0409 70
    0x101e0103100c140e0200744101d03003100042440c0714454a4840141025080d8960b0205016000000c0b5455104100101c00e0412003026801d9884580280c126689408103569030410080e048010a141d40701c1c1400e00c0007180d1509081189541824003000e01404405020388810701e21440b106030368218400c4065030088000c580c101c0d0150090324800890b0300040d1010816129484105045070006801e110168000c9211503440b0742e4481010007000346403030f61403410701c072510000030002c480c018a80024400c1d60b01403c03100ca4042c60602100981c4001214403403004410020141c0e0480e1208403044115601d280510100c07096030a03115607c083c1404507035030345910046800040688584580640d28400490558020f01917220190001002030900e468000003440c901400b0364012800d9075082d0781032030221079000c1480401c881e0076181440307003111455916590560030021040080c1c1c50015410300a036004006c505800c000094100583c249803801d10003038541a100080c4084011 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 218119361 1250 218118111 218118133
    0x1204051b13021c0c02390111030f03130311030a0806090a021c0209011106011809020f19030311070503030405040903030209031002071b030203030d4701020609 70
    0x10350b0241c28140003081d50704484030802042d10040f40c04a004450058200b0140040102e0b0105000400d654840300a980e8200b40c24401c1c0100a104100b49410003414004c2e82241c60300c100147c46003140c503585c025a490400d00807581808410403001c401040130b109000d80115004022746403921455124224250ba602c0100580080001e000c007800b00d9003480074108503210b40141295100c89141c00590320303a0010000340c0000405010358034603a1201c401070010540110a00e4044294100b01041c009201c1c4001031003140d81214a0307401c00c0e4800882d02c078440e0b000d41d0403400c032070090b110b03103090540c0314041d81c2c0c9a807002d0052a4056208010412284c10030b90b000c51315107800707450010300b444554000a41000300196040c0b42c00e0303070003013645d03014000c915240200c06c0300b82030138480c601c0e49107601003500c9000e204018040c03103075692010f0360003943d1003002141c0c01d0382440103c2c1e00d4001c0b60000c8007400e0078043c2c40c06034810074542150320703a5000180031130140e110540144000420 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 218120611 1250 218119361 218119399
    0x2220303170c0d0e0f07030804080f010915020304110d060b10020c0102070303050306060d1d0f0a0b1504060504020f070b0109051510050c0d200a020a0b0d0e031204051b 74
    0x3510360340d00b1306480b030000d1151410009000c03007005188a40da9007a45d8078a0f05410341d10300200350410004a03490440450000b4140382100c1c03098001c0918003507242d507103505200d180c00038103560039504405a84100820408154894450103508403a4a048000602c03002c86e5103502032109a401359100800074004240100060369006000400481c903150070034108005840f03408008094140702d143c802c0704c100b1428400381c3d90104840008100302000303a103901c044000c000d00700c507220105e03850030901342c2d4807030344c00c5a00075050180003035585091440c212800c0760b00c220301c03d0b5541460740c400481c01b402580903442c00307140c0401e0480c0c00380080e2400c10010030040626a000c0c40001c10000140b1102032221446803980740d2504984103080b1907920700c3c4c900807920800c82036003080049800680d9441401300546180103409601c86116080301001081c04e042010154400840c10006d400480702030301d407065100d08107441d0042801c4681c030079032074401c0e940c00d54400030000c043c40303d480b2 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 218121861 1250 218120611 218120621
    0xe060106110124051224151002100b030109050705090702160609060801150c060c050c0313050a0e0f070e04090b04050708070b0405061204030302220303170c0d 70
    0x825079000054840c0100c254020700030848820200a20510b4420012843c0c595851440d4012041c0580440c0c1c40c120b51440d425005089010705020016010907501ca44204070002407003409007078401c4901c8000e6010b561070303080e44100003020742000c080c50300f982010302445907a40d500c04000c111050a0908114818400800160441c819580c1c0782c5048103a240e020001095240c8960204504000004140c0c4805030040003003400007081c41c04c1d006a02a4400f031601760445030000350f41c26105002c41e05840741580d81082803001041480700d1a0b0582c0d500c2c011160110703680200c965559694800701d01c030403a560300d00015594001440940035100b20700c10b42c5401800003034108025600d0440580081c3c0b415661a8001a001d1083c080c08100700300107410784d00d03801414949000e000420500ca10307004000c900903400302040825001c1e8040d1201c41040308403501c60341c0c402c610100d801c20b000340b00580000e10055040d2102c5190b1751850340c0150901103d880c82c00c42100c40c5d80f00501 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 218123111 1250 218121861 218121887
    0xf010c030b061206010e061204050c060301081b06041a130603050702061b07020409030e01080f060d0f0501110412060c09050d060903090b0a0201090b100503030703110c0d0b01180e060106 82
    0x1b13841c3c00c140d00c0c0b83e0b0f52a00207040c14840060001094109401c00c285040f20743c0c581140513090820050000500020b69442418a060326101c1d20240b1180414004d0003550b10070004800400541d051200710080074080301b45074500242d64140d81c482c0304400740c50081d0340b45805a00301c2c9020a200300e410014038a00d666503102150311f0071102c0d502082c210b842801e819400206010099103103581e200b0030182d0007034081c0c081e21889042c074200040c251b04041c1002040d00d03d640c4562410010207401903403200440d03502258440b40d4540c196060b85800c82400c4900030310b00a030741c0901e1800f8801440a4450103008501891203541e10203000300107030f240039018000c10880000d02046900c0040c8040101d950021038002958030b0310803400f001c0a410014201000503050110741c80010580300070b02e4051a103198280c0d520301d0600c0c1051000c40360b02d90007090780e00a040510a042030060704940c0100d05242c0510184195403088800c01200d03581d0940045004110036446100004104 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 218124361 1250 218123111 218123117
    0x15050c0a0f03030b040b03120a0507020310061517070503130602120114030d050f030a0c0903080403030203040f06020c01270905040f0611070b01050d0309170f010c030b06120601 78
    0xc00c0994403206441c20690004400181d00c0b2020501a420305000b64280c1c54001e0340206421a2601030410590090350b400008024000c00c002e1f066640c100908844143d00c05403c010047d220080c41c009210b03500c080c6004035851168004410f9220303100180701e0880342d81d0b17050441d1500303c001c0c01000c0c1c1204007583c480e0740078001e5031851540000d0007402410803d00c0d4078803205039041450b0406032107481d2081403100511400c10b0140070801104e0703001e99050030005d80428210800c0d100200d0580028201d010081804410503400200500640b03664200c2c060380c40d030303462204903030321b1600d4044180020441700c803030b100d103000d00c122006080141c50400800140c84480c06021218200c84c207a81c4c02c06c40f84003801c20b100c164071811010428500a07903240c4000b5485000b404e52040c840d0601450681c02e54405240c402c500c1c00c8094602140082941582150280e64550310a00d0201465181c00300f0280c0c2d6602030b00c10420141009001d0340d051035696541c421151600500c0d05c0d042c = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 218125611 1250 218124361 218124373
    0xf0903031620010f290d0b0402030a0b01060c0b060909151b0d06050a060e1c02040603060f02130509011503050603030d06060518011803020918072d15050c 68
    0x41500b00f030042203022a0030030800100301040d40100d0180c50a100f082d020140c04540c0c49010a0300e45141c201003240c1c016030107040700e80300c0d880441c0c50b01011207401b40c9440d203a00b001040c1294410301641c6ca090246000c40d01d280c0320003003003104124061f100c4c1c2007140d1040c2d10305010b640040d011b41c0d038440321442450358000203a0000d540664407200c402003030705656010501c014074000b40c001018010b10700d03040c1503040030580400c0307480c1e00b01442c1000d140a160036040465980d034002c0030242d5807202c002d00c204048120310304c000c0e402c4064415001e143c0039a001c5030078101700d805181203031905850311012011810094008042c040c04023601800100842c110411039405280d0051032070b640e0f410b82c0d03102c008001d22451549420b10904012001c01d00d11900000041c20307a040d05e4040b2001945600c40800308200811143c1d0903010314069040300203a010740c500c80504081c00d1164046079241c1c02c50361030104c614518054900c404003c0d00740c00c0780d90b038800d001424650400000f00c42c2 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 218126861 1250 218125611 218125667
    0x30112150b040c021e0f032d0406080a0c080c0d020d06150f1106040804090515040501180b01030b090411030a151a0301020c0c060a090504050f0f09030316 68
    0x640e074624002e0005a80990381400c88040d15012010110302c0c1780020301003c4425400d010380360b01c2030001069213400c0e00c801c8071010080800a110b600e0b40c079100d600d0f9840d940c8a102038071003202240c507490f00d1340c0303007070503c0030228011502d0b144030340c050b0800d60b0724001e00102e0315070094104811850700c81f40c3d1104040f80301031001c130019818080c20b40f54409208008030f0300502c40d070481030030441c3c5600448144000216040c007038030203603003031054045006d580d500040907440340004501e83e4024200300001500c0e50903c0310104e1250a6014107119400260300194142c0740a000881d4201ca0800006404100440b91032548000001d043d10130401244d16590401001d5143d81c4c01a40d9a84130251108600c138001c00c80001020b50095090044084406444883c200b5805002d280001109055984145054405420014001c0010b41054095240703942c1d01203038102e0013200341c04086602500f000050b41c3c442d8020b2226403040c007aa8640450f140b94420043d01111002c00000e95 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 218128111 1250 218126861 218126869
    0x121205010e1b13062708010207020906030a0b010621020d0b03010b010203070f0803040809030d12150303023c030315060c0318031612120807120203060d02151e030112150b 75
    0x20000c190311b00c005600c0d0b000701d00410a80741d80107800300740700c1e92114980500184140301040c0c1120038500302031a083d8650b40c0c2441410040341010a440c1d8400240900750f02c485501010203c5415002002034001c44001640c0e2403080e010050040140c01000718006410000111b0740f00788140c406500304801580420700c1c00380b0103000315010a05070300780000c5541a520800280740e4102c1c441420322880d41d20045c0d1111802020350581c2e200e0040002800701040605e5586051024200d06c9080b03050b0801a449030019199854001540c011601440c503140065034035030a002c1000e1880c14071410141d440918810b07085a800d80900c4e440c10003402c4851412078010201040302120303c01c0603151200f00c3d1000c02100006112a4078140a40280d0012110b40a000300220050f521746400c4000303209020b038180b0096025516501526442c3c14202c0509981051220340c001d0190520002c3c4280740400d0044040d514449080c5502103a101c00c3d0035018240d02801c0043e4400350304000c5 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 218129361 1250 218128111 218128187
    0xb030304090606050c010c0e010c12020111032403011109240315040b120706030c020703210807050702090604050a020d060b04051903050a121205010e1b1306 69
    0x155011407000314401200210a001f4034007030789210f2421100d51154000042c080c0c000704807010381940540c01011030414000d50080761041e441f0150182c0300d00d4585d0005d8180c6485d041c2c002070203804015101081e00301401810302500350b02010f40d04040145080c0030034014030381100350300350900720940c136101001c1400031401913000506803051071816905000c1602c0b0003000c50b60244000816486141c1000300d8014107485035031802060003442944100e2512000350009454603540780100c100c042c40b0040440384162083c0c0b2500000c3e560003805580030b010b0008081c0d0000d011600140b0b041c90315501203a48000c02500c01800c1c0020001040c1c2102d040750001c05000c90005001d1005107007900041c00c1a0340c00384218001743c1c0c1944c0c1c032036403070305120040100705401c0d00000440c958000c12203c2d0b40341d000c4071010070166944018098224001303581585e60310b20009000141e5495010445494680200c000041249829811501a0000c01010f003506440801a0346010004640 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 218130611 1250 218129361 218129369
    0xd02030403050d0b09070806040e010b0603150405100f0303050904060314010b0301150815040201030b0612100b0f091e0a06080a06120302100c1205040b042a090b0303040906 76
    0x2c050311141a103001c0021512a10700309031050300144108000d490780144015032040342510045000010600c0f01400351072004041613104034080100140c0519280300d03280995011941804161181e00c00d05201c009103008100f680d2140c20b0302440840e000f40024440766101030800250305960742c4990340d0360407200c0f54149071070351a4112410185030174003c03000700034003400305803014070701d00880c0301d545098603203140070f043c010341001500303680c0603034030900849101400b059682c1c4080c1040c9080c401c0100d95a01c2d8083e040f010200d07081c10b01e03500b038402c0201ca80314050300c1c0552a00402103100e00320603011440c1c12003091104c070f0f03e88460221a0060495880e0310b025804d18882c07030780541d051500500b0341d0080c2c00480001003036001442d03142d800261071000528080428080341d54034940070079030008508120922040000c0604802c0c415030160fa00700b00800c403030269103008040c00c01c00d000340350a01b6101c02d00c901020349c1c0c0058070000c4020122842c0c140c0d10701d882c9003914481d0b48 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 218131861 1250 218130611 218130617
    0x717060403020d18270e031c0207020f04180204020d0c030605030d0801050d03090503071403010b100819140711100e060403140705060109021803070503030406140d02030403 76
    0x200344420180c04200d2035802c0e11031820300355a5007040c918498010301081c85540380a90b4020490344220248240150b091000d90100f8800480e103102c0403556a80f01b007a03014045602c91949a21106541c820340d41c100c0d9000306000302c201040000c10024100003084020343c10f02c05889000142d41720f10080c5507019441401003220484240d0260442e0216800140a46c002780c1415401c0b5030702c040101c1c151041104c000c0d01d403030701504023101e2003c403035040389415100314134006c02c0c002500d5103031003d0210120024401d000c02d040600c0071501e804803030400840c1000c3d0204a030f2261072035003d01c2071040a080098101050200c142820b1001d44502d004100040e000c00d06040303081c0708607840d8207185103041c040c6106810b04035a90700340003880a010010f0700390038410440c00080c201d41c5030542000c01c848032035071510f0703140c00254401509940c0b49445070000c8406400d01203a408100c1e500180690b050a241000a440e6902445441f070070744e040800c040792156031148041c0d40142d01940d = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 218133111 1250 218131861 218131873
    0x3060402210a0c020609060121060e07090b18010311031014150a080705040b010e1f120b010c0f0f050d08190506031e030904060e041704260717 63
    0x40002c0e01103070351103c4440304540004c420080300400000d040340c11a2001c0c2d090244007900780541113082c4a543c24020f01c0c19081c500c219a29940000d520300907101c001170700300007200940080000242c0a50300040101840000410118a1080d00c1407031000e000360a560078000d00b03019980440d03281c400d6240c21424a0b10510000703241c555240c0d0001007003076945034100b83c00c5c0000e25a84400d0703407240300d10594413009841e038164800c614892180d42c0280096028004a400c60720039140b40d0b007001c0c0001011081a105100b01134086d440e004001a114be8100008c0703034440b0024040841c80030f442c0e0f03100700d001070310009804000e5440115115580d954607400c0000c54190f49180e5655042e0081d030030042805801d0f0b0700822244d0f040c1c942c111a00c403a840d400d10243e801c6001d200002035005103040d0000668000b0407a046105600c50301517190704084505041c9000e0149020708801d82301d000140d004030880614200c51013001c81001c40d414150384500040a8400345444034507650852 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 218134361 1250 218133111 218133121
    0x51b07050610050103110301140f0a0603020c210909100302120304080f0a0b07050c0f060703150806040305041e0302041a01030c020109021507060212040807030206160c06020306040221 81
    0xc56010381c0500f00902c1c0a11070001c04c0c0d8030a00e114001070040003110100c0309010105503562048070303541c158025081601c51552000301600131b400041080ca280c0c000e0380051011049034601d40d80e11601d288074503e082100200c00d00880f100d004100a01d00940c0f40304c04805030ba20f4202c0d040ba0101c40200656880b402c2801c100e082c19501c201c500495800600c0d05000101d00045d4903a000d441ca01e0059207400c1c2040f102c5162a10b0845103110074000d0398140301c6051350603000340c5201c6244482d54000142d56a5801c4d544a070119400360000754203000511400c95200c6540f95482191220a03404989075000101114220624044c07825418a1412000e58060007030b0791403a40c041c0000c00c0403042603000301d0000c2035141d68080690100154034000c0125580c10356400e0380540340030916501d000e141040c402d40c04400164090720411000804604549109100c008943d1b44c2e87d500304109a42c07100701a40025044039030058083c450500407a040c210943d152404103d0024640e00385 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 218135611 1250 218134361 218134381
    0x141c090c0315020906040306050606220614130e070507060c030b04050c0a0c030302030a180b06031516200604060603021005070305090904051603050d0813030c0303051b070506 77
    0x95540c1007a01c0c43c01803020003400e940303010690b01240d81003076001c0b0b9603070346260028446d40300720245201e0001e290b20303550785070010301c003600402d862003178541c1401828021034160140c01142d1900c0400d107900c9805100000311060707a10b4000c4454288981014a10354414066a8000c0480c2c000a562030f01200141d1909000b03142c0c10003151000700d0302c0d2001811005000302505107018045c1600080407580000456102070b04092030808080c0301d2900074500740140450981c1c100e8800c3c4540000c1c0f00501102030b1001e800381c06030880c0907850800d550010769151400110350860810081c0c00341c964588144031180c03169114600c001281815031040021400b9400415010410240490300003c0d40040c2211080c0900b181e0195480d40d4a160042c600b01120160070803611203030341c00100704100016200300130400748c1c941c900155a41014001c128041d0640030340014010030480c80802c0c0a548000d400c07592450090115680c0e069070303441d850340700c0c220031602980280101b02c030080e1 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 218136861 1250 218135611 218135633
    0x3030601020c0d0f030c0804080a0c0e0a0b1e0a17030d0e0c010e04050a06120f030e010e0a090c02120a050a030b03030306091b04081606020d0f141c090c03 68
    0x812283e80c160300c4225180c804100c40c2400c001418804145020014440d041040e80c0041c0841c4088400180316490301030702e4030340240309002d00d0700440b8001c1110a103082c020890003100c00b40c149000004d0058200194180103000c082e00400c0c0c142d13001c1001541003440c1941d03006da0ba0f00841d650040200c82d1b030100d074201414924503400904003458241e03032003c1900304550085038049019140c0500c02c03001002c944c1d00414951405650004c1000728180c03a0310034140c02074942c4110900210010340b0700c103880c0d00c51540c0c00780c081e4405111362070031544480d04464281c8119403d007292903202c16802e50040c074103003002c2903001c04d851001a52500414558590036801755040d41402000b05403001c401a0041510a4008514260300910001030300c0003044524112a80780c160365600a2103a40140a540018010100c80d88074841c05419029620b030f1069a030311742d400b641e0001d1810b03590004405018501030142c0c3e40781121009010303401da014022251001110300d50310748188200 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 218138111 1250 218136861 218136883
    0x1060c02031014061212030a0b1c0512030705090411130605130303050906160b0f130f030807090f15030b010c03020718060e04050c150c0303011509050603090303060102 74
    0x3030f06100d251840c064084007090307040309082e0341024401c003404141609001010b01c06000c80400481000451101600101c03500301d8262150500030f40740801c0c0c00d5511368200009440da601c06a41c00c0c0c4100300384030045902c5507107427a02d141882c00f120009011f80f10600382401002002040e140e221410560a140040505060007491714413501010582504e407440081c050204c085100b041d6900c9074030840300c6424404491200340801c901c2d0100d10b0110589261a41d003c840f030014800740c2440e050b000304507402203941841c801865504440000c2c004121000300f0410800c00a440100a28004050040340703034402014200c1942c001c0443c9c0301340d01c160b410000e1b124142c00200340c01050000c1030f02c0c50380c001c0340a4581ca004070540540000e6006014011401042100303216021031291250343c4215032800c0d40502d0400e03203204500565010101982042004204140c1d4080f0a003040c000e4600f0f2a8020366540e00009045030400c40755014140c00000c2041529030341481084010 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 218139361 1250 218138111 218138143
    0x201030c030b0a050f1207061d0d08090904080904060b2104240b060711040b0307050616020409060c0503011e0b040e130212071406030103050d12090b01060c0203 71
    0x145a00b50001d240f04400d4890940920080030a0744100d45512040000003400003080300c80565449000600d03201072200c60040e030750ba000380113150320300d4018416490582c00c030904070705100e10740c400c10071400e6001c0c00807103050204005a542c50740310743c02250014090180aa9112070800900e0308902c001080390300380310944d200801c000680c4c0401042c49404450f07a211030700c8520a50084024244010615842640800c2c1d480410100e44102215070b801030300c05000c46000041859030710382c0d1038061294005000c0c4400c554040ca0380c250603004600044c00070944440540711002100d46221200000440000041c000c5400b060311518446142502e078010462802d00c000019000e18090b11241346061790100d0b00c203186000b43e2040e2250010040031803296481c108680c0c403559480780c102000c43e01c0ca03c10802d480d190f01682e04a0340c2244c080e080d92804850212000140d0408001d1096036030222503000c209681d521501901d40d039110f904103074030f4500400d8580b0503040018041 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 218140611 1250 218139361 218139371
    0x9050610030c0902031e04110a0b0a11060609060402090105090a0e01030c0e0405060c0a210c020f06090c01030c050d02030a0f05010504090c03111201050c0a0336020402120901090201030c03 83
    0x2100c2001b032081004611a9400110151100e2503e0345080b9100410507500c2001340101180042003907004000c3c0c1d565a8640d81402c903e003448a5464000445089a001c0c041ca00018030b103042c581c0080c00b04240502d8200d01c0c120350f00000500c0d00b20359405c00d901c990382e8640140b00300000119010003a00009100e040c00385851303039505a4030440105070454404003c9641005d0038042d214180b9007581c4880e01c0401014818501001007004c1d410010041c40399184c140c50b2580c020600b18003030503200000e01125460b01c0010740280c10801440b40400204000c000c0501c1d0462001c1c60180c030403d00c001c500101503903000002e890040e08842d00c198a040141c0c000140405201c178201d070760040500304075065810000f120740c890861081025420041008041c003010070080101d01201d0300c0030401c0c40f418141d5100b010100050001b0300742d9400a4070440c00c034049410b505a05d1008002501d00700c10b6a40c5031084242c10b0350030240d50b80d101d40903d0215a014000e03600d41960303c1c42c00700300d = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 218141861 1250 218140611 218140621
    0xf0902190e010605070602040312110d0f022d03131503060b03180705030109080c0d08010b12090a0c0312031a0d030e0409060903021501120308160309050610030c090203 74
    0x84180010301c07400f03040c000000380c05020406583c069900940d0450303403880c40000c1c120b1b4060406001a0844055401011040c0740381038004c0c080e000c14603274550b0080440c0060b4400548c01105803102c02030b140c440309026014407144c10030090440528251114001c00d1400440f800004141c00700007082c1418841c0500820004009407940301e440d0815a04c000c0d006541024203208084e00f06940650902c822a400d2010b01d01c001c0206a40850884040c07549550301110100b1081c017030740b41c41000070450b146903800080c05c01d580001e20301c400c0e2101c041c3d07039035240e1180b10744540c4115611440e100a5881290b014070800807041d40e10146a007240f101200040d000c441e542e0401011310000c035100143c5600c8903440b1004140c1e0140e0108070800003410041d6a03100c2c8085c980f02003280c800004202c014103851103907a03295064840102c0c6481ea108981c02c5c85003c81411010503a031a008900418020400180a4100103452840503425418100f081c111980c1011001c2401002406 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 218143111 1250 218141861 218141879
    0x21f18030309020406030203070f080f010c0e010804050114010312080603010515040e0309060c03070c17070e1f0609061103180906060f19030c02150c09060d0f090219 73
    0x210455052600003891006803000034018056900003a406104408010542141c040d2015096030b854404036554100d5014045080c2c2c0d0a80c06104001340e00c52442800139400740c440c1c5500a4031510022990841e401d100c5058a6400d80c42560f49840b510381500c1c4843c0c2120a960b0440403c0d0003d014a20701a00400c0001c4506410603004682d0b07050341c5003c541d400d100ba03800c80706001740701e196110301314094980d40ea0810202643c0d10b4401407400105003104880e60703040f44107003002030101145001007d107031a80e00204a088580903007461f103401644e0024038800606580e07200c01042c54144100208140481054007455503c20030980d40f00007550501032082d0307002100d0380d80169980074041203050240c001528510180810035a5060700d000c0501881e08110303640802c03200180c144200da9542d0040344180c0713500c4e0141e000c100d000c4402c0c401400c0301d400c0501a03610b810007000b110801ca40704141e20240e500d5491184101314504042030075200b0511040502a00741014662 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 218144361 1250 218143111 218143151
    0x7051e0f060412090b0304110f060403170708040801150305060c07020d0825112713030e0a08010e070602030c0d030e0a08030a022d12090f0706021f 65
    0x81e103d500c84000c1c140310030b48142c0448004e440e410b1281d58a0342071a00c0c140301c0201c4018403e91150001c81448062030422605903811250445400c00c4c903d00d00c0d040c0800b81d50b018034070a03a80d081d0208008035007010309003d210803491100000d44100c038a03506002d403c110010b00070004c01c81c01000754001694840104886a5801c8000640c1e00c0b44120795400d000a549140700c0603c00c5200141350910aa00c18600c14000096412440250154074089020480c3c0c02d0021003030b00346080400c004075980c4c1071580010f4807900b0034003540c00800e0000303440b80c0302540c0000b0b00342e0346504034080c1c680300c00d100700d50080c41ca0340011402d1208114045848601ca003801c082059030380e8150b038400500812450a10f40c0d0004404c40c0c2d01e051019140000c0e6101c000ba4004010300602250740254441a5908200c81d00000b04ca081044a415040468030050314428440c824011307400320300c000a201860040036680c0092480521140c0d0142002282e442c01e0300c00140307000b0100210108151107 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 218145611 1250 218144361 218144363
    0x7051c0e0405060d0b0106120e070501050706020c0a0c08011a19062303010603051807061d0f040507090812040503070501080403031b0f1103040302030c0d0203070b07051e0f0604 78
    0x1002c501a514040450440342a580d0083c0c642e5500400000c4d030641c1052410040301107900d000c2c4241328107075600595462080c8500c41c001a4204883e1021501c194003030149e504041d000d85442c44040c0c0c40d0700c60100125013001101d40d65400004503020018031000040311401d03a40d48800440d0745c1e209809500d501d00c50041440620102d02207aa0914450207030030580f24180b03079840b0b58694030014010311044034600c20310307001e0340240c14540400207050702c202c600c0c55660203c0c0b007424034903504c0e00c09015501980c1040d44a10041c1c600c2d510390140d28030131181a692803000d01c0c034140190b45890035021144920346000c100912460314049030102c1a0b80080c00c2942c555210762070700724000c00314108004109c4580c0707a11440500e40c07000ba00102d88006550707110030054140784258481c0325a01c0f001f94541d2100b00c00206d541000c0c0e81114000340000e003622982c559551810065170b00c00b1b4000c84140d00034201c0c414010700d020a0050602c800280181030100384e860000c0c1e41c444001d00 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 218146861 1250 218145611 218145619
    0x402060c0304080615040c020313060f030e1c0806011404060c030e030a030c0311010e1506030c10020303041a0702060f09010f0c20031e0a02070b040b07051c0e 70
    0x140c0c540c40038001c00032100140241000c8a02074038000b507a01c10310801d13440c1240e200380d0625a201146031b10002c1560f070361340d6028100d610a2451b000342030315194084000c000a00d5290142c5210340e542c2807042d0151084c200c220344c110440304510040217041c00074016414817003a40100441590300100f1303501502d8040c141240d040b0701a0a040d904c0d2180c01501c5a814803808080c0010580d00000d04450380348030b0380782c40402049201d952404d036401c105800050307920004455030000c2e0500c0215820004c00f400b40c822042d00c00b0045219190000c0907000580e1000007407104100d044039002049007000d0524514a08005034029186c11000d020304e036484c1e210700086100020294064a16101107240400000d1040c40d4060900204104001c0301ca2070540c244c403404203400f004445d152030306114030000d694841840180c40c0d4000314420300440c85080c6c0c0c00324018103c40010b102030030391444000d4842e4124a0b0007454408a05000e003081c0284011a500290700000341c0300c29444111 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 218148111 1250 218146861 218146867
    0x80406050702011403010b091e0d0f1104020705030c0715080609073e0106060807050f0705060a1d0703020105180f0301050a0212070c02010f0c060222230603040206 72
    0x100041390790f816060240340d440c80340000001150340c07200f001001414801c0e11400c00782d111542d0510016101d000280b90401c400e2944100014858140a00d51900c581802521032410702c000c00c04036080300e0340855aaa100280c20101410b040120100170111601d100f108281c0c1180d000f001070502928030ba00900a43c0301140c1000c0c0a030003441c00d1910010381c042d044032420040d11800920a42605d84110008850b40045034010f00840c42518015102c000860300e498a08a41d40d900441300311080450600106000a005100d81c501842c102407022a079070b0f080c010f098207562144040d65482e0f501100b01080142d030001c050704d2018480000400c10518003c011039101ca01d02d1101d5071707041d4a84420444155107541c0584201034068041e140e899403600c20a50b403810410b400071b80414514902a02210b04c14200080628420980541442021081c00000600440b01404202c440d00303018018601340c01482010402c11045054281d024640818050300c00a84060b006100c00 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 218149361 1250 218148111 218148113
    0x717060409050f06010f051f08070512010f060f031a061e0c01150f03081e1b0a0210021906090618140c0609031c090521060a02070804060507 62
    0x10307a01c0400e040c0d40101c2a612542d580000140e2601003d0182150f0340900360404909410074120329043d4100020308050380701400c440540d8602e80081090080000400018150407180c49440340248000e0000d0131202e0b05000b80a0210914942e07803000305132814103225656800c0448002c0c58510940308507545011401d034130104159002071903084c40d100002c1c0762800400552000c24501d180c0d540a601c0c940d290000c04040b58003c1c400604640780510107101d00c814844d4170703d9072051034a9200d40c5000c0703201d050884c034a646007403902102e8100c0c07070420341903040c80260b4802e4070160b4800380888855a0281c45050408014003402041d55104503404014030f43d40b114824980102c0302a116004600e88843c482e25034244100050140040c804994140a002da035501180207000d8010340700524103d03108074410004281c100800f50b140003c05849803002544c450501e602050000c43d40b4540c02484d0810103011440c24601c100098804180f04ae810340f81030f50168a8101d964ad00a = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 218150611 1250 218149361 218149369
    0xb10020a03030e240a0b06090907050f0909012603130308030a020f0301081b091501080619060309033e0f0709020403020910050a14010c05011404020102060f071706 72
    0x120405014800004051414151203d0b10744d885016658001c0c8001030080307003804964000c0c101c0d06174202043c000403c6882d80110050b04040c05d40d102814200440d590000e003c3c004280c0c00140c1c1c003203070300000d072009403074084106411181c07100080d40340020100d00d801c42c5a415100242c48110f020005c030f011040c0340c0d0101e41c10030341c00d08080f42d00c9507112009141c888180c0c0180019002c034540042d162800c101d8080c1d8442c000200c400ca0401c94100c2c01501c03034480040103c0c2d4000803c0203022400300307400ca04070024041c03a0381d00007044103030343c900642146040703404074841002100c00b1036407046450007001e42c0b844d980750011618800c8081c000d49031507014078080215000304680450080100d03405041228022560b64090340c640701c188204a032003e000d1150080d40d821028401c480e50b0801d4100a4070040c944005001c485417075090840d4009481440924030050601c011742d030b410080b00d9044050b8200800035802c250a010302180400305501015040c1600001c4455075 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 218151861 1250 218150611 218150623
    0x1902070305090907021f050f010506090409053304050606150d050f040314090f04020a090e01030f0623070c0609080705010c080a02090f0d0602041e090b10020a03030e 73
    0x30b000d030080e100380c10641d001a444560502c14031006416607115005003a0301ca0003424051480d04090007003590820060021940c4a5454250440c0d21440c00f100050710030060141d441d02c85074003a040c02c0403074030000740403812007550f4000404200c01c1800040340d80840d040ba04591704441a80c4c1c51010b16040041134041d078030141d400c182c502410840401d200ca0030307403403081e4440daa03070b01c0c824000c01c0c031141f405020302d00c50a500948000b280c1d10060410794001c1070410781d2030411010701941c5003010500085c0c00d800444071640845212401c2000c0c6020b154041200841c00d4444404000103040d010040200341c01e003005100e50242003840855800307601c00b076400250f06540c030602070174000d020b012903010035000180d1284c0016035152140c0b083e186000c0c2e0042540d2a04252001084094026402c041d03030590307820040050410280300d09001d1003003941107070481c0c0c940b52424003022508441c0c0401c4c01020440602c201590b0302241c03c1400d02c4d031608001454000481440b4a002 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 218153111 1250 218151861 218151877
    0x10e1302030a050304080c090114090406390314040b061906050c060708060607080d180311060a02040e04060213031b080c0d0201050f0a11030d09020f091902070305 72
    0x10040b42060010702c103000c0000c0c0140d4aa0703008a8145001071b00500c410001d00740300e8842070310f81d152081d49651420b80d00803a0480c4c060780c804244e112003c032415083d00c83d084201c0038094130246490010620b1403685505602e000d0030308002c08014041c240d120701d2001440100601c9043e03002072803035611304052103110b001e081002184140c035040050516400704100b00b01c0303441514000f607462846851914803648010b025181403402d16581d41c042e6070002403051480603120200301401010360686904264040c0c1d81e595620a154105241400009800d04030040d00401040c4004da525800060300690301440c01640c0714140c0141e2604400b49802c000c21444e42610403213051041c0030000d10a446072071060341e95001081c000c0040603504400c000b808100c06008060001e10703c0c1000d0f0204880e24140840d2800380710f031040382541d11070032420054070380d00d900d02003e6041002c100c042c968030070744004401e0701300020350803406446080816012070300045c0000c10140b007403050701c03040303 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 218154361 1250 218153111 218153113
    0x105100609052e020f100f0b0f03030d0c0309120206180c0d0212010f050403090f0f1d040c030f0b010f0503012a0201060e040609060c05030411090c1908100f0509010e130203 76
    0x85920340340340d0b80c0605100300c000c14126003002300240e0300c0d10300032919510102c8001c005504e0701a1203040c40002d400030641d85000d040e600c043ca440401c260070324251140f40d41c3d0f8060110f0386842a600e1a607080400380800b8a540813032590803280e2100c0351034100d0143c040303c40094282c1000c060300e02400300c6104548905e4101010b000030507400035882d00c02c1d5210710328040c076056104c44603442d0303514040c803c401d05070185c031280d90255500040301d40e401c01e001d1340b40071103200d80704e444503e404503401c2d800311210200000108180c1070b2031401131000c2c0c80102d0080c42441d540705101001003d2000c04608900c1c04154040c00140c000d5100c0310050214441d00306a6280c1814a0710040c90007010984a00e8100078491511030b104404072407042da40301c4410402e980c0714405010403241e0050500c0300c03400c000c00000b050300810400007091654580ea4282c114602441b600c226604181e208014420740503400380b150f6540c69640606440c10200703400104e42d508000c1c00e01201a8040c06501 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 218155611 1250 218154361 218154373
    0x50c010507150f0e01110a05070204020309030705070308120a06052239020c13020f070204090b0601090f08030a08090102070f030507170306060d090f050105100609052e020f 76
    0x50f00c98103d5100f420001000b002084198050300400c0d21504c0c0710840041c03803c2184c840140350560142d50481c03c003000f00e83c180031599840c6450100c0d070390825507070090301149580c00101c2028140d94001d10246082c23082a10b0100807a00d603602080941a5802c1d00e6401032208441030341c002140827180803483c50000d450800440042c0c4604428440d03030071252101480d542c0c2c000030300141c0700503020b007000074a10075030025800250008203091850307410410040c8050703541c030700aa40d6001d0148481c2081c0703051000003d03040300c12680c4002100060803004101c4000048251050380c0d072142041105a035030086007c0c028412a800180031600c0000c3e0701c010b0550081c05040c10034429000c0b4440c080076000201d4071400201c40c03044c0d022320104a40d1074003640a4000310034481c13151045540742074003552040c1c00d664048402d51690f51642c0c1040000301d0388907844c0c3e0018101543c840c040814000140c14002907031054021081043c0a42c2ca1341c101d100f0000209904113100c15910 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 218156861 1250 218155611 218155631
    0xa140111120918150d05030708031e09010504110f030a080408031209030c0d0c0302150a02270306040303181a15030d080105130e01020301030c080d020a050c01050715 73
    0x95682c124984450044255441909030301d80c1c0c160038036000c1d1099409140344007402d43c04000c0381c218050f10032103483c0018016140043c1c9500d01843c000c500c0c2c5444201207400100700e8494000d401003584050b81e040c1024040862412490840d2030042611740d1030040075140046031030070308001401800400005400503c000c004806001c4071440860407003a00c0e12920f840e15580d00681e100d42d001038000140102201c0d000b0b201c83c00c0314504c24010348104002000039101850000c4408294468000941200c50b910b140090f0100c0203198a0008801c40101c000c079991352402080201816038940074501c10128240b00446441c3d0b215161550101869006407004003040d61002c8400061280308403540c600464a94501c15580c0e6805055a1074002004000d450051440d14941d9842c2251a0084030a00003180a07500400c2111100c030b191560319490500740042c49400c54120b6400c00000550201d2010325801c42403070401d480e40c3c1c860809400a10407011603180241c80d188843c0 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 218158111 1250 218156861 218156893
    0x30f110f03150306040305090d0614070c0b090102070305160201020c060a03020c122b0f0c02010e0d090f06030f140a0903080f101e0b04061206090b0a140111 69
    0x1501c50060b000c80d440c12101d180080c150303528015035009011a10500000340c10b8200781000c540164060440455800d0780321340b11510324042610042d00042d0340f00d01c010180403c1c0e01030300742c100c051900214a842c1054a0003082c60265128403008911010f0000c025a8820045654904002401c0b03d555640780117000c3c000b51301203600b0101c280990b503400d07540c8807540002d07905048560300070340301c04840c00c44028284d4075a840c2d18480d010398414400d2a4004540309807140c00e40e03203030000210001007140080c41d09010650040402c85001c005000b00d220b5010032004503100f0f41004160b50700b0600340e000203031481c07001403003505800008001495403181c02031080b40d4025214211b080e2501c40c1e20110301e000403030305007510310481c07031042041c0030446940c4000554a180c1c4030344195101c00450005c0da000d0b034001c0340051086941240f8070b624504c11400103008e010000c10100042c000841c9000c01035105a8001c02562b00324500c459000d038480103080034400302038622000901d4084 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 218159361 1250 218158111 218158117
    0xb0a0305030423041e090204060e0106020114010b0403030c030804030302040b030c190206040305031f0834030c050907030e010e0105070e0604031e030c0803070801090c1e030f110f 79
    0x70703c40035812120600103420544241c5007050006600208901c500c0e0314400c016258524080303130016036800c40050426035440c0700501030b0900b40c1c000b0401d1100080038210604c4181c20030003516004001c208002078105811200450b80350601c070f075072541c0e00d00341a0000d0059511080c02c24a00104116241d1100c4004109150380310644060325810b200700eca039684800c890007808540c1c10004610f0030340c0c0c3d014050311100000f4651694a545400e4198145414043c4030740f4071410b0042c100c0480000c0e0414080540c5502c0d6880300d0072071450b110f0b020700346034030300c1903900441c0314401282a40b03100350003198409012500901800c808170141500034542222040c1c0020503400e031a0a8914051040b1021039030040001c00014000412a001c83e482403d02102440180380b000c0380003c820001031441114a41c540030f42d0f0b0362402d0b4102c0103545455040e00100400c00c0301100e081a654604011005028a000620400c90005c590002c220005107003503d0880803407a681118440401 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 218160611 1250 218159361 218159399
    0x30f0209010b031009020f04121101030e0f1b0607120c030206010506270319050714040e0607031e0f02030a0b0d120518040908090102011a030c040b0a03050304 70
    0x50030329941c0c2c0e00c00d6001d615020a0355900300d00351010800300015100d40d00945141d451794010145003a9072003000c205400c3c0c080c6021a80000050024401c568140c859007140c0f14107000a8101c41d100160460384035041c040e54030110502080504081c0e440d184181c07800c542c1d00045401081d800008085c084010006089005203e600000701b81400c010041e40c4001030420700c071040801007090004001000300c50023641500c02e64200481055600d0817140c01039000e20003a10901d800c141800b40c1901c0000c401c18000d900f00007040e580c0707407000688198804c90314640000d401800b540c40d103142c120070258001710181800001680141c5580c001c50148145d401c00300003559904091141850071400007524450b40c006500c40d0540c011401000340e50211000004440b180030001402c441980300240c840b444007040c102e0580d60241303e1078810b403444510070381d1119008400650b0b00e40c508440d0500589c1c80b000d6003030150321001d03c1480510b41c49400c4e2600d907134036400054408005158 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 218161861 1250 218160611 218160619
    0x70e0a0c020715080a0e030a02030702121005010b040f060509010504090b0d08030907061e050313170a0309062906070f0b0108030901120606050304060504050c120c040605011d040e03040807030f02 86
    0x901b00d022100300000b100c1c0c01201c0c0b40c0145040010303e408101851103240c3d5482e185024045120203820790364402c0f64007802c9a040425211414240402c00071b024941000090120800c182031081ea0083c099038200d038224600420150342400101e00d80c54408400102442400310070702c002064041106070641e80280e4803000409645240c0d4000450301032007460105000f08049003210850014180c04a4061284020091f08244000809600650042c00000d59460500080000c94003840b00003110301c210b181c40d41e00c2c1034022003581c41004040140314040c00580c40e800c210502461407510340c0c1040e003003c0c0941e59240d60b6622030b840309183c540081d900100d0700300c0d024404d1266074251401956a2400d6a9442e51200d000701005441615948500170680c0016900c01108500040d1f62101400590001e40c0a11066842a400c10340c113005c010005a00344116659010714034010488022881c1d94640005500714829500043c01c0740c042d03620302000b4401c03000c007080c40c0039200356 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 218163111 1250 218161861 218161871
    0x41a0c18010c08121803070c1815050405060418061505190608071e020c0103050c040803090933030601090b06161103010612020a08070e0a0c020715080a 67
    0x1110308400c80072004001e440d00703002d9203041d8544c9071015948844540f0100b43c014041d4800980345401c4940121444a03980506020071030b02c0d0302d81d0642c180e210420900c02c0d1015500d240070340196a001c2d85002c0c41c4d80b88002041c030740d503a42000b26072003007121610744800e13a5401d010020f4291500b8000d16985200c5c4001000d0800b0301c002500e2071244440c400b07486042403021a01102c001c1c2100d01080511042d49a61342824410010f40724031540040c0b103860302100002d426200001c1c6403070100c1809010811164202108071004400115041c41941d40c0f5004410300040c4229601d4860300000daa0400034a6250302040600c120110121101070787d030361049200380e880e64000f10390408000d0203220080d1650310005101984181510100145198046400c44031180d1011490b4001d01c400b00b425820803001200240002c4800340c00d01d00e082504200701c94102400210800d641c8ad6181b00300303070744284220400f620034256010510515010001c01e211001c0d04d02a50840c500 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 218164361 1250 218163111 218163157
    0x1080d050306100e180c0c010e01060b07060908040806070f031b0e1002100c050706060801020304111302040906030809010305070c0b01051e030a060e0f0307030503010905041a0c 78
    0x50001e680c030a110080001100300c0c0035080458042e0b40c00b003a51030f044808000320300003060300c0000c050311965802c2c00040d03c0740c00c0c0c00741103401d43c3c0d1030741500e01070b076454898240107040529007200c80c02c2e60810320104007a0310514081c03003030340700e07982c80034140e40100d10900c01103aa024403008261801680e0501c01c1c0080d08c0b00c0207840c4000c002c18000460234680c50700e0000e01b0410410701e0040c009005a50b22041180085d07000c3d190008800ca002a40004581042003003c0c401c071000351015000031429841d055580351408100004a148a950300c01d080260740c8806804807009068103103c1804095a00e00e410042a00403009181c007090400000841240c4110180c1c030103587c11204011f000c1c1d280400b8450000750031091503803040802481e642207620100001c40d5614810f800010b10b0b9503410361a542820744641030b10607503030410402000440da004094905440c145000000c007038545151410101d0000400d102240a0712400c02000c80e81001c080d0818206605996961086d5 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 218165467 1106 218164361 218164367
    0xc030715110604261309020406080f070804150e150115020d020322090f09060c030204050d0803101205070315061206090219080601080d 60
    0x104600c0030406540c04141d44401c0c0411401400b4607080036070b80c0b059050b01520002588144c0100604034040303020088440303807062080080b01c0307581d0702c101c210003070340142c482ca00107d2070300c00001c0d5000c0c000301c5807544918400c2d680e000682d91296622902211032118241f040744c0e840c08282d003000c500304014440354002014241c403540c0b6110800d0314440c848090178086400450329004284d8000081d240d400307801e40400005d041c90755003d003200302c5075039000a4100c0d09001e110031140d250f541c00b00e40c9990181406100ca040e0b064025000c2e84120701c81c0b1500001000d00540105841c500a175411204040307085580d03e81d10790140304da81e407001000b56119004600c0070420010030b260744400841d100b0030705000961810301400501c95040001418041d121032051045503212880184c4260f518824941d2070380d15110480c3e9250002d000b5000d0364031420f4416200c07140 = true := by decide +kernel

theorem cover : BRFrame.Cov 217985611 218165467 := by
  have h0 := BRFrame.cov_init 217985611
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217985611 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217985611 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217985611 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217985611 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217985611 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217985611 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217985611 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217985611 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217985611 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217985611 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217985611 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217985611 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217985611 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217985611 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217985611 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217985611 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217985611 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217985611 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217985611 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217985611 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217985611 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217985611 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217985611 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217985611 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217985611 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217985611 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217985611 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217985611 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217985611 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217985611 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217985611 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217985611 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217985611 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217985611 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217985611 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217985611 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217985611 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217985611 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217985611 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217985611 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217985611 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217985611 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217985611 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217985611 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217985611 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217985611 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217985611 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217985611 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217985611 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217985611 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217985611 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217985611 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217985611 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217985611 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217985611 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217985611 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217985611 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217985611 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217985611 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217985611 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217985611 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217985611 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217985611 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217985611 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217985611 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217985611 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217985611 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217985611 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217985611 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217985611 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217985611 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217985611 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217985611 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217985611 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217985611 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217985611 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217985611 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217985611 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217985611 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217985611 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217985611 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217985611 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217985611 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217985611 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217985611 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217985611 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217985611 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217985611 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217985611 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217985611 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217985611 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217985611 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217985611 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217985611 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217985611 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217985611 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217985611 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217985611 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217985611 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217985611 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217985611 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217985611 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217985611 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217985611 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217985611 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217985611 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217985611 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217985611 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217985611 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217985611 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217985611 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217985611 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217985611 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217985611 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217985611 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217985611 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217985611 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217985611 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217985611 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217985611 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217985611 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217985611 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217985611 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217985611 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217985611 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217985611 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217985611 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217985611 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217985611 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217985611 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217985611 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217985611 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217985611 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217985611 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217985611 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217985611 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217985611 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217985611 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217985611 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217985611 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217985611 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217985611 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217985611 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217985611 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 217985611 ≤ n) (h2 : n < 218165467) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
