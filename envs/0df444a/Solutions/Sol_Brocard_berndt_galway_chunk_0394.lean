-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0394
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T19:35:25.477384+00:00
-- url     : https://prove2.me/submissions/fffa2794-2774-40ba-8424-ea51b96253a6

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 70683455 ≤ n < 70863311 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 70684705 1250 70683455 70683463
    0xf0e010b060304020d03081302060c0a0c0e0108151506040b0a03140601080a0e0c0a0801151d0609040303090812090609011517010e030a030507020d020c0f090a0b130e0708 75
    0x40394028414810300705641d80c00c7e034100344007c00204524400303044000142c0c403034a00034042150604050701550400786003107410166070780c0104442c00182801403091080000c1d501c205814801039020141d43d03440c0c1113075030075a403071450a42c2144001c0360004103848181c0c060020341240d500c0030301280d400310b038050400780ae003220203d0000d00c2ca10045100d01a069118508502d0076100f80c4517501c00103004079050a030f081d0b010f02803c0e0b40d0354000d8a41c05004c0b0221a0240096481c1c00c6140005a0480c0d0b1a080c4040d002c6403090998802003070070103010f5845001410b610020f543d07196050403001c401c1c50441150425841c0c01242c0001320f9440040c41000a4041120320720700d0810b042c80106120b121644c100140c1d5590780388040407000704104040c00584007541c0d4082020f11300f5410090403d440005803074155485520600c0043d03407240c04940b98588140c03a5550740796070300c040380c001800c08501904d8002444406401011240342c006185411901d0200d0300c2141c0d8440c001c0d0f0b52 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 70685955 1250 70684705 70684711
    0xc0f0905060a03020904050c040c0801060f0206040f0b06010c12050a0e0d0b04080a0e09040f0c0b0304080319141321081929040c03020a0509130608010f0e010b0603 72
    0x20203041c0550610051511505c80c980140c046d40417680300c9944407011408980c0c151007044040341070b101c01000721590064162208140030b02c05443d00303080039524009055402d01004052641c1d40e4001103081c1d22400000e42401d4100312048403940716044098450344c003d01caa0000904440d03a0742289003004181884003a510900400456580791500d5010760480e0399044100410142c62032030541d1540c1d50300340118003c080e00d03941808a403510381404403981c0e01035103164105204203c00b04420200740c80e8030002400c9810003d074401e1080000130a07545000c1c54a0038106014400355040f41019040c503a44035415520080488048181410a18a0050340001d01640001d1100c10320300c0c280d0880c005107803901155002071281e02404841030b043c01c401d00c00c100e000450000d460203000b20303d61051641811132503c40c01c800020464030540450900076402200490058005a80100010003440c0b0080207180c01c0f07180810098501c180c4413900d15030030061100703814545101202c1c0 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 70687205 1250 70685955 70685959
    0x5030105010c02010809030d021209060f0f070c0f1203020c0717030a0513050a0b07060f02040608280c03020904110a0c020111070807030b0601020d03050f13051204030c0f090506 78
    0x241c000b07003540110380010707008200302103501052100c0c0741c81c3c41c01400130b06507152035442c0c9001c040c038002c0c2003d468600010404000c41e4200e00c1030046000085010981005980c80d000c07444420b9070030641540701d5210001050500088415441a83d06078040c12a5101c010142c9601f95a66810304044d8030a440d2800803d0700200003081c1c44030700800082c0546612281ca000c003182c2d4440005010002c3e40c0d00c00760f040c110010305801000514412410500c1404500314103150508000030b0040030001c00321000074401135900c07000788060744054032020300f005800b80092901031100401035041402101c1c021400c1090350b0904107105800d035252003038a60746127009811190011101c104c1360f05185c41c0388c0e014400004c03032102e406001d110051802015021240e0411100081c80c20841c41c0d4110101454071050040c03228290801c0b076007000100c0c10b80402c030070301ca040550405249140d40704001c00c0c0020700004000840303050104035104074000d003010613504c0a40805a40c03003201c240da = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 70688455 1250 70687205 70687217
    0x4020102100b030f12070512040b04090b01031d07051c1515150207050a0b030f04080c03040509010e010e010602060906060607111306031401020c1e010e1005010e070503010501 77
    0x20941c01d055031184a41100040440e11161414400c0d00c0c10b02107413411021040c00300180410602004000d800c507540182d0500c0e62500d481c1ca04050842e0042d4020750941984030007407101c180e032190b08501c0e00d01e0864200340b00450032103005550354004c60311605015180c15100c0c0296001c0c0000e07110b0000341c0280d81e1451035400100990010054050303080c584262964011810103010a805000c9600680003018070a05100070014000640e0703020358440c00d030030004c0024400d4850010340d0020743c00010b030398403040f40812090460245070440361b081490743c070001950a4500d010141203408501d0401d015907290381c03040303032113841c00c4500c10f440d6070103000800c040381880f03001414885c0c02603804100c00400c500c0002c4244050a550100041e1201e009000b80300021124042d4114048002c42c5070204884c4815102d800f41071042050010611410311070001c2034014007201785410003035a140003c400600002000d0030f003d0034600b48a440c0c00580c0041c061012681070760740c140c40e40c1e = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 70689705 1250 70688455 70688473
    0x1e0501030309120c030b040212060c0405150403030c1203180605060907050901170a06150c020a06020c030c091003050715030c021b09041115070506060303030c0912030903190b07020604020102 84
    0x48409440c011f0701c02c90700710b1003039a01c1c40501401804118014803204907035680d03951901c8100549150002e103010b0f00380004101c1040082e030071842c182042640488140081d10061030103074014105008903491105032503641200300400355000d548150070440f5284a1034480039800c4903540694003142d03000c1203446990145280c8103903c0181d100a07a070501148407038442810140c2c0400103140c0d01c012801e0700103c8421890640003003006807019100401009000344006a03903405150300d154003a40100001c58400307403842c280c920146800200320307403099540b032003100c1003000f1030301d22200002c1c585030320412030610104040000c0b180061b5149180c641c041c04200c464403020300201c450108810300d42040307840e86100e00058003002101c5540301c0a00c0d00f40542020130040c481c0d48243c10070410450700500b21400d8400d4914280c94100c5075000181910f131440c45440c1c0e40c945d140c406c2030445001001009040c032015849002d01d090380d500c0e2000182d95070324043e10002d002d07820061030 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 70690955 1250 70689705 70689713
    0x130b030a080f0c010c082707050d02030c15090a0f050105070818030a0506090114010803071b030c0f090e0607020a08250c061814131e0501030309120c03 67
    0x24142d00c0e8100c2034100e2421880404007800c580c0c402c070100b80841c02002c2000715030a6107800410800c17201c44080b01001a5600341c240d21620070b402990b02c1002000d40120654608100540c582e19004e0300c0c1c1c82d0801300e80040c076a8650000c80e41a4883c402480020032b41091300e4210204954060b1541d40c2080941d036180c5103244c200030b2400c2c805800042c100300859a01b0490160310f1405200582124280b044a041c20741d20148100c0300038020300001046900d0b0000212a00c2c1500700c0e8104034520510050050a00d41c1c991001d460540d101d034020418881400c2804c0444902c10300802441051404240c1c0780c10084400c40b0158111050803004100c0b500c00502c040c1d060009192851000c1100c0d8070303240060380384140d5440d0fa4010084c01a038cd08801c4d0004032140d41710007840c6861425401500b1031405000d038501802c2160140704c1000c8064002c3c0ca524175140350b108101d10410050100181024841600003035441e10001404088400e07940c0100c680144950920714210f880d = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 70692205 1250 70690955 70690957
    0x4081e1506010302070602070c050405150a180219030501060e0f0f0405100b0a0c02030f060f04080a2d030b15070b091c0207030605070509010504090509100204090605130b030a08 78
    0x2207070714103042e0204103000000b9071510052441c2032292001038045410141031008607680203100000003400c0810351011031340c40030f00700d070708aa2814812030410380d03403086a00b0280c041c450034845004881c425481007d60542c01c083e06039141d540d90b58001a0b404001c0028900c0f6040946d41c1041010b40710001c07606040d0001c0742d101039150300c0000000d544d000310395507640c400c0c2d80800015054130107040451400f40101d03444c56038080000d043c981800a907020142d100a00024107020002580940180c0075014442040f246003100c0c24041d001e0b8200c2c2110700601c0c0860f10700088c40e2072101c100e580380071948201104001019a4100662a0385030891103d01401e070029901c510700900111a02d40407014a0340112076000e002e1342451444c04a05845024008006101040c8010f010607680701c0c0503101107521041c030200300d83c1c84291805050038240f0b9504041ca50001802003120240c68018404907202507036003070203d2050350f007517508030351044081c90741c035030054194400130900e440 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 70693455 1250 70692205 70692211
    0xa030e030120090a0e131109090606010516060c05030f0a060b1e0d1a0a1401020330010602010203071101020f043005060106120e1513080301030804081e15 68
    0xb1344503080494891030f41098103a0210f4013180c0d19102c0d19980c2c800c00c0800000c080507050240c80003402400c1c080301e8070b501d07540d006100714108171003c41c00400c5501415902072045801203000c006088429100802c2d90340100c0b04034105403400c0d00410190281842a90b08039075451070f54500307005058064400c07285900d2000381e80e4003000d0207807100508044c03045200050001411142c01d8200300144143c04c40d00354415520461f03c2c40030440540d0b004802c4610400c1030401e12444086280741c0340e15100e00c000e4890340000d161000102c1c9881d0154000c0d409100c09464016a80d841044031600340d20841400c071403409400d11082000d03e40c901240200020f0307140342f00704071510200380e04040071a0240251016404900104600c503044104500c3c81e0310b05403018000099015000ca070384071440c824a04103403074a5000148540c2d80d00e016283d80e140d0059030203540b540e4030304054aa07900a40139800450289043e22a052000108001c00b800c0c044c078003a00c48030401d4030342c0b22140c81c001 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 70694705 1250 70693455 70693459
    0x606030603010905011e060626041703041101020c0a030f06052703040e1e06090c0d090305030604060b0301080d030209011209140c040b0a17030f030403020a030e03012009 75
    0x40c01d40100007030801c0c00354581b040754000b4048500702c071000d41e20f410340d111548103038280020464203e0002c402c1000d0700005900d2101401980c2c0c445113802480705480e00000450000007005100c100442640c00780c0032910240d08075810b240a1508000d9030703c6041c40014010528046c0c070b9000103401d0f821042c0c0c02020100410b0441d40f00d441c980c0103203031440403180b2054200003800d02c504201810f01c550040484c00c4c1d030b60064892031550071380300303c4c2c003810542c0f00d82e8030000040d014528801c12a0044085040148600245031401400780d0f001541c01c944100c0c200040402d000d586902035a04880c0d0310300080401250b0480c1c198001d5000c0300500c0d041005003018440f10541a002d154121362103000302c945140038442c80141054548601184100d0510b6034407100d036560300e070461041c0d03013148c00546904902800302070300c0e600c035511a2400c00000401084140340c2c001c1541c0f04528080d40300c1d14000391941e0105030813280842c41000060b0100d0200c1d07024220364a0140038203400c0 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 70695955 1250 70694705 70694711
    0x9060a0e0c0403020a060c0c0f05090a1e020d020d06080c030303060d03021606050a030e0109120e030102091e1008060604150c060608010c030b010207050901031115070302060a05071106060603060301 87
    0xd84d000301d02e120040e40c00000c00700344204800b100f040502650f1030b00130000220101d40715810f040c00141e400e1800351410356a1921900d000e0047c2d0080c0c3e0080d10102141001150307a0b00401030750b000a90403101c0d001c490130340b502c400080c5210b0003059030241d10100502940c607664601c0e0030406a0440b049040c0c0441c4901060002c1c510b00003c80341d405024151141d64a40c0c01521008003a1140e84484107401e074141304145c00002c20700350010b11040f15030709108089200071030209009019400110750b01040380600980d210401141038914144182e8250750340c50341da01d9080d01e41c003a041e640243c00120801042200040b9150b46400c0700b483c614106d0864000764030740905a030340c580c000205a07556402d0321203030b00360544200c0381e8403442030011b8003120f03251500050304040144800b0b449130707491030b094016031b54030984c00001c4244880c0b02603464000b42d060007941c800d0203d0714094000e103420081202c01e4000c1c50281d084c00c3c50f400c024803050307880006100c3c1e981c0010782055010341d2 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 70697205 1250 70695955 70695959
    0x1022d0708030405030d06090c020a02150d06091a0102072403020d0c0e0301050619031704050d2d02030a03110f01181509051c17070c02040b09060a0e0c04 68
    0x16a00e00440c01140a4001103455210806c0c0301001c560442e444265007625008202040640100f18108455011580b0680c41000960500010322901d052064203a1500c03c02003840d40d410380c0305003000c00d82c4900140f030b000780c0840103990b2154240280e22502d0404400c0b1012881c3c44045113040c912030303160242c01c2c1262005c2d08416200e55014003008207410f000450071500302441041d90001d0304440c01860b00c0d0340281400c2d401c810764000641016203035801c07102500100400c84000707113405000640314107a1801c0c902000704500040601d0130450031030020880034885850700318150010041c000d03004199800351503c08920a14140c0c82c00340d4550544030314806e12071409860a24143c1e030340180900d01c1d140780c0c14070f03415035143c0680d07141501020208800040b03503002011916a003817001345080c0d8007559906005400720182c0302c50041000f0409030b1140d00590828401c0d9014000c1540034010024401d60881c0c0064010002c500e0411140d0b419038404c6420640c00408145007036 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 70698455 1250 70697205 70697213
    0xf0c0903060207210c050111090117100e011d070305060a0b0d061e080618150c0903010f0c080901090323090a0e010302090a020301030f2405070306090e01022d07 71
    0x25005521004c0030808203280380040c00003e00401d142000300e51061854464000000b910f05903c001c40410082c58141c0000d19514005400c9000350400f440401040e41c0d58413181481c2c0000c40c2c881d00c1c0c1c1c1d00300c0795010560300340c024020180601001440c1d500c115086c103940c00100d03080040940c016a80b81d1100041044070303000c0c1103901072000d07404601c0302402c1070501ea03d03110300036101ca11080c0c010240000b07401004598169500e004080d40149a00d82c0c0da01e03c40140105410700354103510b40744e01c000c14200158000c1c10444c2043d22840401e070780d40d4402500301c489001d030190105030360701c40c69580c003500a100c413501c000300036040c113081410480108003980308a41000f055220000300610941c0381441d07550350710208200d0154034660450303840d190300d40b0000800030315010603400d071803100d03550500d00d107074034281c03501030030009468080001030141546119000440c2c1c40e00d1110620440e06000715070701803000103100300d03510000c807100350080360146800c80c20035501400407030002 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 70699705 1250 70698455 70698503
    0x90b0a09061e06050f0d11040c02030409150302090606030f070503060310060815010b0f0a120209060c07030b070306030321060b0d090b01050604180507020106080106080a060f0c0903060207 83
    0x4501c1c0c41030b0002d03100341841c05022084004803003542c0b20f548001424000141c001848500744001900c011131405041c42d02030303265001d41d401c400001403c2900301e0340361024003102c2d001124000c40781140a61100010f000c0148000e955001000b19082d00245289008000840c1c0100c0007904465249116048070303c00c50704c045d0010042c40d0041c00302e082c8107404942d50b540c09860680b243e90b142905401140800340b280011031814030a52135291035083c401079068030745904024003210350721003a48009549a82d254041112807085090100300218400e21030304060700d5258036850306040040124080844490450400040d2141000704040001002410299070f1a00000c1900d0300549030000d0400f40580007240140800c0c80f0070803401c400c034044009010110701000a41d40c862001c01c03805468503800811482d8201200004c01046c00140c1d80a01c41c003510080140c05500c6102e80140d13012041c0314030000700754210074404607206900411001b441000d0300d038041007186507407841c8 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 70700955 1250 70699705 70699751
    0x313030e031509010507021c1803140604051b010905151902030a0207080d05030601030b04090b071211040501020706081906060509130902011b06090206070501020913090b0a0906 78
    0x49510b08800b40585000d0074012240c0211050010700382500c1c141c3c43e80745107100c500c1104070420446141c1c41da81040c515040101542d007000d02c108604442e5999180c0e0f030310003980c04035072a10441d0f8080400d1201c1d40c2680d504400140e450080d2140f40a007080301110410026070703c00c03601008180b40c0d40c0c10b140d90031022001d0503000342da202e540c0c2020180c14102e00e517210304031303a4010713417040000c03690300200b102c0d403114003400c00042d0f01351060b0200e17006240c090b8005002402c01c90500040303c2d040070b044240745400301800d004002100507640803c1c040e1788900c1c0e0159003c0201403090034000c0031541c0e40300005405405c03140c141b0090300425101583d2204c00410360000d40c030003060a002c0082d042a1145040a00100c00641d000801c01c030030040c1d461801905403a0150104411a00202d0345150014213103030b11020a420030714000e5001807012032044112900d0b00840c1242c500854413519004500244255502d01ca81e0020b000042000c440c0c5603615641254400104a90805 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 70702205 1250 70700955 70700983
    0x114070207030b18071502011b082e0302040902030a0506010e040b010608070215060612040b06190807050d02120a0b040201030614091f1508100f0303050313030e03 72
    0x1100910b9810b140c011080090005204c200c03100c07281184500d4000b80070300c101c0b000f44c050f007800d078074070200c00328018011400d08412a00c0850580c148155200761282d014841c3d01e00500e480b070a841046c841c0990380c89414040280781e14070100058501903100d100350714000b07010f5800390710080c0c4d02d0301d0400000b600f0101d002040b45062005200078002c1650140940d41000c0e421418544d002a54039038448203c0366605119900241b89030702d07803105417810041c80c08100e1840d4280f0f4a0820341090341102e1560140900a00c0c0000d002110723499202100d0410000e805054108020301c4102c4203884016a00150355505100b0a03039010051580c0d4240981c4030000c16082c86c7c070004050f926580d0010315403110002c1d00c0800c40d81c1e0414040e82001c113801c1c040c00c03000000400368465100d1640700c046100e281e10306102c081c0784c001030360b0741c400d00540404014180d21046000041c41c1c00f800054009242400000c4c266a4074014000f00c06010b4204000b0185603000064504000052080 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 70703455 1250 70702205 70702213
    0x414040b07031103070203090f0114070c0524042309090d0f03060819050f01050f15090121020f0303030112060f05070e01080a0605030102030a020a08060406030209061201140702 78
    0x200c15a075040c469140b030f20302e102030070134a181003050000395640251684117114002c141e8114415070b0007100c40c0c515484c2d00b80b2120b074940442342071030101030b086489403034012619072a0840205110084c49a034007a280020f49080c5410403011415018219a21400e081a007004120702540d42000d05881490301c140284100342c10020014480b10200314050306140c1009000d100318074003c640b003007030511460725110b0f007180c032400c0040c5046000340b00c000265180400703000ca402004d998041c8100340381c10020569032800820702c032202c02c0074402e04904020b05141c02a16202d8000260803043c002031400180711603c00c002030540e4801c0c2e000d041031202e480c1c1200d041040e107018101d660f12601c4001c100300d2031f0000001e03084100c80c1801c87e0402c40b154000604004056000c03002500015000f15101c1c80d0150b50354009502c038485401c0480c41e844001180c0b450103000705000c0e80c2d4083c2c05a40c10351035290a111054170b540c51048803a54844290b8a42d4480150050307215030f045030b000b4 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 70704705 1250 70703455 70703461
    0x70309150f0f09110d020105090d0b040512070c090902180a0f060812070627030503180c0d02060c01021611101b080d060509070201060e090a0201020a110414040b 71
    0xd2003102c035080c0100780b00e03e040c92024008140c224190000500c0d0969501c44e04d1003507880102c520307100300403080e83c0c011408045a018850200c0d826071040d0702c07030070465040622030140d40003140942c0c440117040d8150903009000185d103507088401030310b1029184c030031540c0e05a01031450080d01110181880c550300c00098103140ca042c00b4410050816401521076044808940d4900c2d10418170050031a90303d40e92a50032003c90f00440c20f041440004800d54111414500104154420f4032405c0c0707031000900324030007a0000801c41d002c2d0031a004107680c1708260f440d4240325281c3c12680c90b140082d58284801071080c0901c811568069204101c0d003228580c43c80e0800040d05400007243c41000910460018441c040902c1f001e65140c010803942e840d4500410000c010f00782d04e811080e0052800410710044540540016080d10340ca80c905107069038981441d20317680e000d4800041d005a004c011000d02007003680b050118007484c0640301003500703040c261a448000c03406550442e40c0d80c1d29a010 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 70705955 1250 70704705 70704731
    0x105070f110108070314060402091807030e0c10020a030e060c03040602010501050a090b100c020f060a0809060105090c07150209060c0307050105010605120a0209042009040e2407030915 81
    0x30f10b0754008914201040030303105c00702d800c2c182c440f00108011301895001482045681d514000001a20194140c1071010700d40a14001c02600741101e03c48160b100f14075480e202460032a4150f14042e400b64000d2000080544044617100e1018402d160016410444486081800d20060000c0e20842d0000704071035150006001070016540d110b003c440d0b1801070030201c41d0780c0b0110901c28010907890050034408042c00001c40107030300c1c09011036000c50001465016183c00250091150044400b52a10350307076683d0900070150390440d5602e5800d0001c01c41307100060f0302c040c07058410138505140142421041d10104d02c20303501040001d9a180c0c8086490001c0090034020940075000510b001c900740340400b2400c210b6881c1c05054400c03215000f282841d1151125401120390000c00300e0510341522204500d904903a00456030180035031b082c207120b800001c000140003980d40d000d10f4032500012410401c9001c0e59030b409400c20003059110b095071404522300441e50f0200345100c2c3c0c80011008841d0352 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 70707205 1250 70705955 70705967
    0x20c09010e0c1b0f010501060309020f090c16081e0301030c08070b03010b0d0f060308090a050a0506030c090a0e0a021306030b01020705240f07030306320105070f1101 73
    0x11040030140800c40400c162910315000780c540e0b611851140266040e050f4450078203040785400d244a5940c40e10000140242e450b410400049000350340c00e5420b01e0605051155240040b94403080407142005102d16580001d51380c180d109018510003800d01d0540885080e61a41e004481c2d101c00342c0c04030040c4148040308410307070010a84240141806480d213103140d04240014801d00780c60301c07000304a0500c04d0600f60040808000c1541c0100200c589070300c4d0041b607982191381c109002d0340d5400c00c0481e103410025000401d85000030b01450859540741824045640131010698200c04514000070710902142e04540c040e909849000d81c070755215a1081d2080880780d03001d10100b60800704000d4690344c000c103401042e1802512203480c80315954200c60792074000c0c1e0f200c466040000192490f01d5403c1c001c0075010b0144260780c00c0c4034496842e00300100300d45140c0500c10901c508034140100f9415841907a415520b01810300a08122980e19102481c8030700340c2c4242c400d07903031031900e4080c00c0d80d1000c = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 70708455 1250 70707205 70707209
    0x501050906060a1d0a0207061503061b05091e03060103050102190c0f0b0901020f041205070602070302130c030f020f03040201110d0f0e0406050402070510150b030708041a0106020c0901 81
    0x52041d80c9800e2820800c1400c0c3c2070301019100d513800541c0013094001d80e854049405982c3c0200003806108802e48110309012140e1105850803460803e9500c5030321510981200512a03980c0d0301420302d20b20404010610a0017051030500003220a4118165101445200e0096001304001038580956940044c41d03518043c02d92010484e07040c01000014440c005610310540d00440b19680136503862030300178024800c0404118100d4000303d0b0000301003a040b2b442031000352040c1d040e59180c540d03614050b03944140a0100139030120820381d0380d0308034a441d0313401000103800340c0c9000300d00c0c4d18903120060120303400301451019800002041000b50350704550220500001132000305071031246070740000c103100d200311000800c016940e06143e005560b5500174002400b4001c008554032a4a440c01e26a2441710941c04212241003400c00e1a070300b80c1200601c0115180da654552850341c0d0314000700d03580c40e1b0043c0219040c440b190b1020082c09070348029540a400c968008240f613440020410030031400503 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 70709705 1250 70708455 70708459
    0x9170a0806030a020a120203150c040f0e0c04060c03020c0409140c030d02060c0d0e100603140d0c0605070c0b0c09010912020f12071a0a0905030c01140904090b0103050105090606 78
    0x43d214410040e01c64032107410031543c5170007101e4181034092001038100728024940d40b503101030038418800d040f800307180184200c5444802e03000c442d03503032003ca8541114040714891504070050204101c1103014201e00704030070344644140d0b0040856540014101d6031400300a585030a940f03c0c0d603141a200400500310b241c40d00718002c0002201c0d22800030341c1d030742d0b0003020054802c01c00710701c00c540304000d9000100108203803c142d8151170141400a0010a40c4d84419581c00f8840102400058004101d81801450a65440c020b0302034a03200e0002804016200c1c40405c00350500c3c0f0400310300c520043d140107600241c03540303135503c4202c07000601c0d82c805078011955010745540d08000580d694403040180304000d50340d001114500c0100c03a824241c0701d90144624000c80360072424040500c2d80101446940c80d121403644544501c00d140d5110307481c810361808180401da500502c0c0d0034200103070a002400404c00304100525aa5040d20f00c0801c0c5d10480d281d81d1140240010520107105180d070180302 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 70710955 1250 70709705 70709713
    0x100f1707120c110607030e0a05060406330302010f0e030a060c02010c0203040e01050f0111060412021606021e010e03070b010306050c03040f0b040201121a0109050103050114040f09170a080603 84
    0xe40d43c07680c5a14000c0c1c041e800f4540d0b141700d02d00c02e0701414040801c0d4241c0200c1503840c2841c2a0405002401170050b0100c641101140400541100b401c80d002000348141e14142000e07045500540d0710420514030302e0103001803e488208075030f0b01044080d419074070801c0d002c90341c50364005002e425548030200440030740d002408140402c18a4a80960450b0011100d0250725441e41005a41c0c0c044003a5141e2400c0c01008104028840540c3c00620300310400c0d4200e41d0000100080312014030703c9400f80c2c1e001a003090460214021620312003a03403101c42ca5000007443c1c0400104140355500500b8225078005e1410010018059180b0405600806001c1c8540c039600d050b940b103000380e0240080081c0800074141c04501503910450340c00f8403c0450640c01c0040c003000190f928441c07140d140c0b13100c1c0042c201d4540071035903510034044d1034103e030301c01d52100c05614050000c00002e49440c0c039921190644c1d980100b00454411905030008021152078955207501d60301d8000c0c80c86600526050207640 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 70712205 1250 70710955 70710977
    0x605090d0c0f080c060403050310050a0506090108180d090305010b09010807031403040e0a091101020c0105091203090405040c06020709060305030405060f070507061d0f100f1707120c 80
    0x9000055203004079408070360240b0300703000c0e458075005501502d001a0054070030b40003000704040d0000015402030f4002d40d0b14002e004d075264100440f0411038011a034001d04140181851540140c000030b130400300c5600d0300d2042072100d0366075610b000081215070000403440e203410000d0200078072a8010303c0e90240c0303c9040e258140704869540d59002c1c8002800000140e000d40b00302042401900e0180c10165005031040c2041c40c6030350042d01c0101d1b402d070354580c2d40c084040e00e07541c00000ca52450b1203068450701c0c00d00807250208003100544004c0b031182800208201406075469106852059104065803801c1c2400c1c220000e1404105400140c507d610300001400440c4000068a00b100d000f1180240e4501240c0c0c801c000502034103900810078402c2e20800325040d90440840c0030300010b2078980305030041806007040340e611044030a2541040f40c03000c0c0040890310500140c1558105e07800c202421514608002c401c6030310171100c08000441d0300410912404076400341740c0070300200b8604481586 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 70713455 1250 70712205 70712207
    0x3150315190506280b0301080307030f02031206040f020705010207050303091203090a06020313060e010c0e0406050a150216031b1505090409032703021203041a070614040f0605090d 79
    0x40701342113400d030841c150354100034007418424245405064003107900d80d103e507500c2114a50342c1c1c0140a00702d000c2f481c69100b511105200006a4506c161f0070360811030b260315101c3c1407000a1203402084410b00781c081103e4004180300740000c00c0c043d41308074025681d83c40c0441c8070318200701c10642c5039204440200140301c0c680790005441911b1903001540140c1d240c684440b4010318650107a0001c0c281d5003003c1c0c400b419140c065005a0280cc003503200c11882d0f4801004000884005004c0c5e9a8004035000041c03140d9420340d0f103c403106c90744500441300d500c0b40d948480505441c3d00c2d48121190610700c2d0701c0d518074082c00141c0380020f0070110903050300c03a41c1510f0094900d0003000c203810b028540d01c1071640c040c1403003030041c644030350b48000000411000c2d54a101007400742c2c0740401d0b400780c5029011200c443c0e000000f00c5007250001c01c505000c012600c0b50490296100304070680d03c9603283d007180d8000f8178030350002070302851240d0041c10010b2400e1800380c043d87d8008104800701e4000700d012403045 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 70714705 1250 70713455 70713469
    0x60f0303180608090604060b030c0d03050309010b060a050f0319020c101a1e0a0b03090c030f0a08030f0c070602040e010810090b07140d020f030108070e0705070803150315190506 78
    0x1140d0b1001f008580d44104a012034035210300d5202450780010082c5e090400d06400100650040c2d800400070320404400c5400d10003944108005040000c404000d0100704400381e0000d160428200c1c04112a6a050b0224000981e0007030f203900016900040d0641d20010b40c7c500c2240384441c94403100c20400f20030759000500d242415070041e4a80b144010040c41990740355078103800508108041c00342c81341082072099a840ca609000c0c175011303215010842d0603000d0005404101d95620104041c5544c0d200503015142c0174000c0c1403c680740e80d051001c0000100e00380043d2001d07001b40aa80c451030b601d0550405e00d40302116004101061420790309902003141c15078020b40c481880c1c1490100c0041011640c991340c41070300700d031102d05032000c95940114124080114100c0b614401100c0d040b5441c1c00d0210502c0c801680c60f800803c90800017132000440c034134050350303012140b50200d0480045480109090010b000c90207200805010300704440b854090248106110510008000034030304a0042040 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 70715955 1250 70714705 70714711
    0xc070206030403020c03060a0b01110f0d030209031204060804020109090b100e06070212010e120a0801150c0212062e0b031314070305010c140703030c03060f03031806080906 76
    0x290038000300080c1818020499803e00796400744c2198420b141c8400300d84002e000b000c401038001a141c402c0701174803600006400d01d0701d1013131001070801d00c0e0780e010040e0020340c480107545405000b81900da910741590036001c0c1c0700031301e06074075038420318500351000409050098101300c81e06441e1440c8d100541c0c0b51525840c201d44000e060100c042600313100026414060725600942c0400c004404480d1048190012010035031501c0c1100c140c138019032002501d0380108a050000911500d004100000d12203440d500303011114105071820700e060380c000c0f80210b0a1450484903a500403010300103000d2442902c903000503030403440d0712143c9005a030201d046801a100320601864003001141403503c065080b80244d5500000b09101e440340d0041840c3c07101070301e00c425600e030b51828040d00d141074001d190092441d5103c00051385810307000d581c281c00400900c1003140c04c01d07590304404100d00450809080c003450180d01c5851483c5021510042c4034440f0750031100400c45a0780074855403020000d42560 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 70717205 1250 70715955 70715959
    0x30501050607030e130f0204030501090b0702030c060a0b13050f090f0c01050d150509040f060506010e0901030f2301060f1d040f14030417010c0206070f110309040507050a0909050c0702 81
    0x55600d840140040074001c89000c6d80c40c16880001c000041140c154004880284580400d040981d590b00c02aa203d00404030702c4103960700600002002a10140d01501c0103410081440035290b80b900c00320001c40d1400c440aa0054201e0403c1c0300340c0d14070800202c41c08824a100910398401117000080240c05051000850b241c3c80c0c5240501c2d210f207140c0c1c8400030f04405407010303c040c685410915111203444e00161062803400b00403400951113030015800001c03014111181c180d203940e0b6154040c0a981340b02740d030004503408224960740b1000092113400b4824400114000c2e041030207681c64074109900c12146c1c441c450307014040c080e107a610886c0d0320681240c0e40d4251100301e401c100028410100306001e041c0000034011880c010404060602c0000c1c8000070014004d003c141680d81e468195059008186c200b07040380d5079584540c0803603011080581c1034034140086080480c043d80c00a9030100003041012410b440015440a42c0200504103100d06100134100383d504588a8442c5100182c = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 70718455 1250 70717205 70717219
    0x110415240c060e07030308010e09120307020307050f070503070603150e060102031605010507120b0307031203090c1205060c130308070201090323010b040911040e07051c03030501050607030e 83
    0x361581d0041c01045001c40d00208140000041214070588401003404206c000c9100b042c00803c0210400b5546c91183d4481401440f0f5100c89020816080d00014140710451108111560001300140412269000302400811015042104142c1010460740252041624000072508440c3c03c02000808036145400800683c4e1158030040f0705611038190800380c40d0344202a032804001055010502c58205959069001e1a1070000316054404000c01e81e42c2c1a03104003000e00c04507004402800816007282030004900345180d80390008610070340c1c0421a012201141c400500000b404a40d5204040030300c4140380001071194505016840e000203000c8020214800e130869018055071405150811452002d42d4070628581e5090045212001e04950034258000290b00f454003521a80e030381d0080c11400008120028003000b000103600c002d00321702c12500005030b00c0e25018100203c8100301040c60f84090340b5800d01074143e0380180e000d90700bd200c1c10045080404d07845903850034856002ca900c5 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 70719705 1250 70718455 70718519
    0x2040903020a050706050c06060f0f040c180e04021002061b0a0221070203070e010b09060c2407030b01020601060f081509010b0d0b060a05070f0f0609110415 69
    0x100e28040c07480034020f0103407182e00004200203800ca4054901420640b088850030394580d800e22204d855400380b929042000b080c50102ba038502600a0004070066241c90464601c08400c94407546005070b0011014030400400d00081d820702210025082400c2e00040c941418000c00d600c0c03200c4003e001c40f14a801c0040b4080d8610340c0700b0b1100c900000b0352180c0c4074144030320f400744440c4180d2008804a120f40301c0c981c4001456001c0800c1d0390304032011071400500b407222031014050703954072095894a650042e903e148803d00314084080c02c40805881d00b24281d442c141c44080c045404140030f00341954003d00040101a0b481121043c0200300ca03e0010142c0d21040701002074112103220030303075000100b00004510b40043c18050301498135410002d10a034405501030080c0342c4108010500091002c1000001088203043e00c000c0f040c0c0b0654000c003c031000381c0c03a0301d411251905005c4600d40c85034151082c07140344c2401141d107456662822740307501034500500c0c651100d03540c440c5d0202c80346207000c00d = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 70720955 1250 70719705 70719707
    0xb19030207081207080709080c040e010e1b010801090b061801020c0406080d02120f0d09050f030f090907031404030807020a080f0403061b0c032a050a02100311030402040903 76
    0x5850209a1142c005074681c0108600c802c040501190801c000071411000134042600c40d20540046500e042e001d0300d0b19031140380600c8040c281c620180d0b0181d43d01c400110f00c1403001004801c01c00c6215403080019103602c42c000500d0a40180e012845223800d10347d00d80103039a50348085600759254901d449444400c41001070b403c0c440c208040591080c50182c1c00116100040740040140140f903003601d0480c140742030344403044d004000103151b11400500044010820f154441c4d428580548110358400001c09140c500d5980f041e44007510120010034480000e041c0106e146812000b80e04050154110310541c10501f010010000b6040042c03c001203000203009101ca840255001303030615980d00e02c154140d0b000f5a1151000b01c402919124030800c0e64602413100c0109000190f41d000c2e00884030b614211801e0350310018218288580100c001c40402000c14885100c900c5080034040e0210140104940d5505d01e0b1004ca0031b01d410000c5200240341180120383d84941d0480d4005071030203081c10 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 70722205 1250 70720955 70720957
    0x50c0705060d0908130501030f09200a030c06050a09050a03030e0904060204090204060302030610030b0a0b0304051f0c080f060a050618090c0c060903130905060d0611130b040b190302 80
    0x3d041598002001c104079204c81c5d00315000e0791b00030b8800b8400b8518000705003084030745c2a071024190760414000c00752501211080410361640082c1281c1c4025241e484074a0015515800700000c03550004031014910303004540e2200500301140e11141e100c1c40c540b40901a0b1090391010b91042403200002420465580d06541c05014040c10464030790791295030240080d80f080d9881442510082040e44c80c80f4442c1c041c034040040040c0a00c5102890440d0b00c3c120350300003410884640c007a03880c0320219890340020350009041c0884011486420301c1c6005028142c0c05041c44002083e03850402529031562030240b0202c64055031496a81c00c4500e03410700300c001559803540e40c800c044c2814440f46290345405030514501040540311580c60b0071420b199240f10340075048030b03821310000c420000b00c0381551005901003400b0b05900c558a00f507980d03076422124507198965400c900815481c1c4010700b0004030a02800c8004e040f949081e0a007222142c0c0e070b00034401805000c0400c5001d03094010301c250 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 70723455 1250 70722205 70722221
    0x150c0d050717070e090a02030408190203040e190e0706050f0c100207030c0209091504080a020a15050106030b0a0302060906030402030304171b060a0905010f020a17090907050c0705060d 81
    0xd0709015440c141840c008100c0807a20803d14499402503000c46c03110003143c400c8030b00656000e0344a51400d00820080040c40105403600e0003540030900c0005504e0b6000040d42c1d00c202d0034803410302660400484087c0485008000d4019540d00260081c8001c0d6003050441341c800d800c0e600840d80380c40c00310030342c2d528060088600340f01c0640003150410405821843c4500601c1c800c41d52844180e8035458059514440c1581d51280d01403884081008030b91140018925a00390b0710540d03140441680702d00500b4104500300c0c0c140030341d5072001001510b0340b6205189120004440516240b451070300011000e02800c02c98074800c3c03071b001010404541d010011a0000d000c0c90705210405001a011243c03500f640d05080084505410b80c44003680c500035013103504600d02900c1d010281c41c00e210045848081c902d107101c056205041482c004140040d110700c220084402d08140d88440342c500b03003c0c81a80c040d0144041c00700600ca0544c600784080358640a454080d1a495100d400300490840540150 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 70724705 1250 70723455 70723487
    0xf0613060b090312030f06060d0b030303160207080d0507060f060e090709060909021c1514100602030412200d110a050909030a0503040203120a0f02150c0d0507 70
    0x4414005500081d800180100401c11001e0303514140200075024070a03c011681c101020851500045451401401400f007915607403200061400980012074510350003070b2065070381e512144640c02d0281c1d034100301043c060004030300a05036004000700080c0440c050940300401c041c1e01d4005488452940350711030802081010811482c0303081c00c0a110380c980d00c050048451843c00c00c500450903031420300550002560151110990744151200303099165641c80d81220381da0400100450201c82500640014036803034074490000d828040070482d0090000d5100506540050004001e1002c03404101c0448541080d21840c04030306d001032030300d48051400300d070341e50014000001d00180212008010f6904c40c003500c20b070003010344840c10064003020031030340440907038002c108419019200717001860b00b00384090112102a100c50508081c1500701c110307142d00003010344600a000030b0381000751014643d80381c1e001c080c480c2040025001a8800c181854460039110f4021034940340c4a100c00302002000 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 70725955 1250 70724705 70724711
    0x309150d0603121101051603021c020a110c03070305030703050a1e0306030506060a080706050d0204050607050a020307090905070918060507020303070201060b0421030c0503030a09060f020a080f0613 87
    0xc1c2d10f06402900b40300e1903c40c001400f0b03048800010039052241340c1c0900201440540002510071089010f58841304080c1c0c0c4030302c41d40181c259032207014000307030080d00e41d903403102404184500ba12501c2e123941880f04e58426440710b8810404200080f0880c2c80060301440d00720740c0d400b0700e04c00613607a6113a02c400303440041d40c10175088201e80d585903204400f40c07842582900c0058840000300310b048160780c06403000c0c640246804111140c00392004101c0d241c0700740c0001d420070384d5490014034190010391080c1e4507504980d050740210300c0e05001d5240a048211000c00c00602c0c0e9858850b9110720038020740b003a044c0d4031140c2c0c00c0034a01072100e884405910550900461610b003c2c002e45a400503500071015600b80800401d1144041d41540c094441022a040010341003c01c40b600c08203401e0001d4090001041c6c0c1500030500c184000c61160f41c000102194404251034560100c03903491500403000c51040c4000c0107919031042d5a82d800c05c215115043c05c98036101c000880115218901044241c5 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 70727205 1250 70725955 70725959
    0x110708030301060203070209060f010917010b030a061d16140105040306020316020c03070303020a0b060103020c07030606140f09040b061c03020f070b031603020a0212040b0d0f06080309150d06 84
    0x98000001c054940c401c0c0c5210b49141c2700c4600b40441c9002000c090f502088085605000507140003040c2c15600007071000100d0750303a0310100032030304007a80008155802e6807541d1243d103080798202e480d00c3c01d411545c1c0040c401941c41c4070303400d041218140100a420320341d4200c00c0c00b240e0720610503107004d1500040119901e060000d100d601420b000c50300b100241c051074078281040d1078013041081c12a9095000b50810a2250751807405400c0000c100c11b06040e424400050081010004040518400c4000140b0319040241c400045000c0b054414800c009412180c42c41d6122030340380079045039200914000f01e0b11500002080c20a5075200034802190b1600c1900c18154000740741240c0b0100c540a83c1c40080d04c2e080c281c030146c4400c0f02c5180698103200d040e234400a00c42da0081280c07810038410b40d203540c680d045d9808040da10135889041500350210b5443e4040780d2030f1250380002501d40b802007283c03914090699440307010b2042424411400049580d005441d80b000b12005503015000070000d80d5 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 70728455 1250 70727205 70727207
    0x106030602030f15040209010c080706060308030103030c0510091e0314030c0a171501110708150f06010903110402070213050106020604030f0c020d15023a051611070803030106 77
    0x110110303081c0d000c0b08220004c4048a0034288202c803682c80b4182e659400e80320080e101c078a62684074810031500c0740d0703031001e002000c20094000b56010718801d035110040e00406040151414054588128500f46400f0711840060603541924044468003002c000f5644514101a10002c054900001d8809800820440801c4c03c40c03002f0242112992a03005080d00d03510f080c12011001203032591154a0b803504800010344c000c500b4050583d08500031500016290030700c8604080b1941c00090080009409001c00482c140c1112980200c080c6403080040d8030710f46440d500d0320480c00160380070b181e0000781001035454000c043c1c44420b03c1100b0501c42035035501c1009641d500304031001e400107040d105071011040d21031011039200c0c513002404c5088004060300c1d25100c41c0e40d455404140998204042e9501c03840300d00c4a010381111014180c0c0914044444c0c2c125985030864030031140c1c518150421040030700c0c1d100140c000b4102c0c0c2c07600101151402d0180c520306034640e00607059503c80030000080c25 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 70729705 1250 70728455 70728481
    0x70513090606030f02041805090703050f010b0114090109230402040803030405010b150a08061305070801050307060c05060f04030e03030f04050a0909021c05210d05010f0609030305090102010603060203 88
    0x40d5440c0e9404c20203500741040302c404034010350240c00740102d40025000d000444903001143c11880c20000d0721896503813075503021720b41078081e00390000d01d945904058000c0d68011070f8aa89000066100614100c40b10380020324501060040d00108016030b6460320001064687c40d489501d00030700210744d9152910516550382d00116001c4505600301003800905041c1030642c82c2500110940c180e04241118100362140c8000030036250b0070050443e003443c07620546028a038001c02c51900c6160b085e5041c00145810045250442c0c0180946d5100500c00980d0000301a903000f16200c09032081612180b03070031111003520b40a940d61501c80416007c000c2018000200100d0350104c1e610760303285689212035007c0d81d9051002a500500311041000b480b1002102d01e40e6031842001a82c02c161a100040718070001007030641100d001c2c0c0451200c888000c3c51040e140905480422034250a19158004003050880c0c000201045070100d211000c9034000d4101002460748004155280c1c0f0349111804c4070 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 70730955 1250 70729705 70729709
    0x605150d0311100605030304060c030309170d0506090618180a050f1b010519030902190501020606040209030a0f080c03030705070203010b0108040b060f030f0d0818011a090705130906 80
    0x402d024204500f403840c500391181804507000070740a9814a0b00d0f003181502c0c1640303503641c150141610340340c0c240005801550848030280e060303844961078441440c5101c0480d07070003d19180c0a0b06408062000e20380e1550201e4004e040c030200390709150340c0d5215140f406c3c00c000c002089813910a032226401082404101c1011a005d41d5085513071a01c81c40c482a51080b40000e04280801e0007003080340c00c0c0a040840005040b1407506000c210400302e540815004610309054500c1c0394003022040c8015a418001160003850880301035041c048050f00094031408200401443d1a8185028108000040003500d0032078908405503504ca142a40b0050010361280000b240309521b0468101c0596000780030b03c034007682c1c020b80d5410059a07a00203210b81200300020041e03051007071960300040b07210100009100190a41d940b124103080c445d0341c20140c04100014a0002d0341042907141c05145c20303c65441c00e20340e08494111050b15200c1058078148100158523908080340c030000305d0036141603081481 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 70732205 1250 70730955 70730987
    0x3070606080f07050a140f030d0503150108010b030a0c200a020a05091006180506130501031404050a0201050904090f050718060e0402060d0b0603101505070f0605150d03 74
    0x3510070301c071040b064a0b0341160080301d51001e40da00c003d0040750202e00c1001c10801003e0b04451250300e6510019180005400800f00012000010004010340641e807040320311101f0309290059504200d244011400014034105c1030f541da035501c2d080a14411190f0398400010080385850300c182a040700b0b0b48070403400805900a1500707080020309418201001c80c42031403c89500750a1506080c001c89044080c005862020000700b0800700c0c21341d942000408507000100c059403001c41c603020016059810074444520050b80960070003020410100d107500e0001d0782482e105603510a4000020014400c6a802401c40102d0b50704d91002c009000801a064804801c202d468801c0e020070147c0a6849038000ca07042c142040001c02c00604001c8040d0041c00d0055002180c02c000e04c0000c9501500212010282604009000c01181708130600c0010b0000700d910f0300341e141030150f4954040b5410001c00080c00c1c01c1d55480081e040e40c011403402d0b500244001c100e03401d10700782c030b04000340500306400d4212 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 70733455 1250 70732205 70732213
    0x5010306060b090108070c0201020c06040f080606040908030714070b0f0a0e0705150903010609050c03041101030c0f050309280203150103020108011a120a0603050d0804080d0b0f030307060608 84
    0x200d405a054010f4801044050b9140c0e07500c0c2c0ea64403821503080e202d01200728154810a412445c145d40c841c0080d1014001841c6045011880c10341d100b80b03420000352400380510b02c0c021605d0301080c0e85030204d071360104903070071f01321400c0c011810184200c2c4194030026140d0083e4201b03028040701c11405085c0214100d6600788080c0c4800c030655505c800306481180e40c403030700c40300d604407001000101400c070310b50006000050300380c2d43e03141300c0c01919030440700c04010320f400000308000c1001018403503480c90300038a01048441c41b0032001501c9441501c510703a00780000840013a200903010400c000c0021000603075882c2812105005443c0040061001c910030300450031801c0c8640c4c0c1144100d8102ea80580d03070000240d2910306020b4007004211404640b440741044031308101c12a0f01e102c036003c0c10005a000418602d94203040c0d04100040c644401080030076800d2001044004080d2580c051020320005445221500020030010380015504e8143c0004544401480310070b0303001404035984c41080d2 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 70734705 1250 70733455 70733459
    0xc010609140601090f05040f0e01050a05041718040504051c030f1a09150a0f18050106020327030712080c010608060106020d0503040303060b0d0e0c010e010207092c010501030606 78
    0x10b42e9044c455000b00041280d4411003045289425084a086c0ea9220310340043c41c0007600403c6425903c00311900441e01e40c449040c48200020300e89210001c6059040075800c02000303030082d400e0202d02a01d01449191a04003050501405014545c04080c0008100d42511101c91015000e003107411210b0903481d241030303008001085510f50f41c841401d4000d09020455032062030945c00800715261a41e08401005800704020040c0a13503200545641000004908411241c0b441074400503000441150030074050042c4964000110f00c1c200070200704680c00441e03058010178a0080380b40d02c0807034a41214012442030041880003001c400d14100000d114940e1030750b00080c5d07548028801ca000603480b01c0300d1300325690b1180e8040c64020780300c0d1a010821035a10b90b41c0e100140c1140014420070756462042c280d5800041100b07100014003802d00b40c20068600002035140d403014071a81070b600340ca40703c5c00320428080c1d480c2004414203420780c500031201c5003019903000b00802d00040796480e1501c800 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 70735955 1250 70734705 70734707
    0x5010b040602070e0a062310050403051e0f150610020a0206030a02031009060311030106080d0e06130b070c03061103011202040b030a051c1404060519050c010609140601 74
    0x448007941c03441c1d0028410b8a10340720291011000060840001c60782c0c900c808a0400e0306040000d5611901c40d81440c02034080c1c1040120900d0781030311043c28405c08003c02c100143c00400c1200022201c4841e00401c0d040c03c103425403d250b0340c1d0540300c109000745903801d1001a010010f150150700e096a902c507441c2c1d01c40d5000c2e42e82d45202e200196121000f800042c0309a442900210761010a4169154181d0740d03600c01304090300e54a4200310740b41400c4c0c46000070320341400d104500003040148010041e642800754040e0000b441e02111a0080c800014501162240784607444028500400569610442400e1010f01d8011314082143c1403070030072100048948444d010303030b4142c03446400b41e4407980041e07a003000000c1c10038003140d40e05400340c0d10f24a00424410701520162042850082a0b0502d513407500804041c4410080551800d00748414400d2940c0442507509000107a08120014656440c0580e004c2c00740600900441d8200340001c603c4a42d1070700b00d00301d1015107170b4012a5548600780 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 70737205 1250 70735955 70735957
    0x3030a090b0f040321020702040501060c022403190204030203070305030304170c0d0c020f0a0e150901030f0305160c06052713020906040b07080901110f0304031101050903060a05010905010b 83
    0xd00070f0006600301500000031178000c114844072129107140146055403990115040d9a002d034007040111382c0300e04020040d03040c0200c1d582460718280b1000c14000300c0c0004102014003016041885821986001000c3c0003a00e41c1214040c6400404a80c002c5503645481030b52644120b400719108000c1c00070022190780c00d0010707503149a0b02580640f0082070300304021100380c1d40f400001da0340140000007034921610b0365000140038000001c00c6490a01c0d190000245180d400d868107400351281000400204400c1c2020056442c0d1501d417040d5038803044e1000031845110154060080c2e591440c0000720590020004c00000d0254079640906c1d103916540e2501c1c0301c400641c203d40060b9071052001841c880c40d4010602040700400785428291502d20030505500700c00000c4034840d4001803101229a0010f6481c0d010b544950f00405098503082c405030740728007540c400101102c0340700d06c1040040c3c1c050010303516800c80140481e54541b40400c8200081c140c284035a51030340f40341100200740303508050 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 70738455 1250 70737205 70737211
    0x1201020304021f0912320706050a0806090408190c020f0405060f0d0501110a05090f190b0904060308030412030b0102061b03060d02030703080403110402130b07050f03030a090b0f 78
    0xb8450701130052401345003140a00b128042118030f440b900e031a80314001590076007078410040100703240c15500c000b00400c914025054000f03209000f0140120241c155110808a90121041c1c0c2c104007541c6881c0f501030507500904071800c011405003404140c0c40d07039114203440034580c02110142e600e00c10503c20300040f140c0c01d560898009501c0544030019082400b10340807542d00c113000010740c60804400f841643d401000d0310070001140010700c18903520b814401018440c1c0c0845417140c0340403903003908801da40424032170307410036450100340852240d59540c4203200647c0c2054800d030760391805180bc01407c502800321030010070303d003400c1b03c0340d254400260184503964030b22078004005441400c0211030740006151903800745000103001e0058400303010280046200e81d015a88983c107624000082c00c0d0801c200c0f80c000c510620035100d4101e0040804002c5808004a855407400039013030070b07414504603c02c150708511000041c0700c12201c40d035026183c6140942548080c40e181c480c06621402819 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 70739705 1250 70738455 70738457
    0x71b0804050d020a090501080703060f1a0d06020910050c06241306051005030f010801021804050a15030c1a09132307050a030e03090d030e0d021201020304021f 70
    0x140018402410300b408024070081c0000c00940318555120241000d03130340240c20030f50030b540180000b0010004640944100500407110510006c0542c1c0d02c420382c04184044558400c5082d0354000e400e201c2030f64111444060043c081e10305200c80b0b141d001c0c0840d40041c5114915129050000c0d800014581c0441c1c00030800c00040c1c40c44212003400c00c500e001c00214031020003940c9200000d900c0c0d49612084110898544031241c4030302d002c007006001124160f001070001d03401002071315805440e2041d0080805e008032000101030725200300400003801d01340e56105903000100381c08414440d0400c0203004481d00e060108d10502004282041c1a028400c606900125245048506a400717038100022002e440e01c22500300d45131510050129072400d441200100c0d10000d042081c5a41c54090700b4004496200250f04d0440800b000c82c0d5951581030000d402c000e000c030b8003031103280e4903103040c0da01054005003818805003846126074001d40c0243c40c00c030722612481e41c1d01d403008440603000c0e0183c040c1e1 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 70740955 1250 70739705 70739707
    0x618160906030203100308091507060f0b01020d080a0504061b0c06051612020307030e0a030c05060105010f0807081005100e0906090906041716350d0e120f03071b08 72
    0xd0760340c610391f40307403c00c000969000298503410400401100b014040300c5d40078402c08551540c02500010031103650122050464000900340e680254102100c26005282118009019030755400d00d0001450b080c0c0b401e068040040c0f60842c0c542e0343c06084404c00c0c6018050411441c1c540d4cd0004c00100c00e44000f103004960710b050400c45908035503000c4e640c0b00c626401c01141c154010301c90681420b101450440100d48100c0301e03030b02408410400d080c090030080c2006003039500003e00240081b10004c00e60cc04002d000000030b007025002c040820014035000e040806031a08500000c2c0203072460464007806601c0400006a06203041b04d136950040e603500000c2c1c80e01c0c0d00e858940f6200c100c201841140c2402003005482d41409180381d103148001e02881401e541d0702403000d01e01159048040c909100c0b040084280d10138001c8400860300303600c3d021000082c10083d106a45070410100c4c00c4c1d2140141c202260300e100000380580114170445080d0741300701c00c10340c503945a4055070303010f4070010b412104 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 70742205 1250 70740955 70740959
    0x2010201110316030e0102070803010e011a071707030309020a08100f0504110108091203190e1f0b0307050603090c120f060a0209040e06010312030b06070b0c03061816090603020310 79
    0x4000d178003905040e40c50700d0015280000d03c2d1940c050540c42a030021403090300500042140d02c07001c2c0c101110204400d1500d40ca01940b60300d0f4000d500c5010315100940420000d1b401d030401d4026441a080c1c10340c003410310040c19990303804540e103e144d41d240c0140d1207401c0075401c1800c0840f61161500c102e50000071045521001c2c0011a254403000b000d8480798800c840341d0241c80e03034800f006148240c02407000c024242c0c010746d041c2c03425101035280d400c01e968486800310001c1c42c01c804450001d508509400070762072400100180c41c20401d41d004030b400070000801d101c2d40c80c41c007040d0020307008010354642a035030034502c4405035640c210110188054100c0000b05403080526002400d112400400220b482074406103c0c4c2d080c650203030710403030b5100d07106c40c4903aa1041d014020300411354000c030b0b4540d0400740707183c55001410340001e206801c0b001c0c0c00400a140f03951080c007490b4050101011b070785841d14048544015030500d20003801f000c01c29410001818900c80c0c000c80f031180d4074010040002e98 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 70743455 1250 70742205 70742207
    0x10e031902030f0310031e0c0b0306040902061b190503071101030b030d02010506040f020403080313061506030c0806060406051806091003060504110301050105030f07120e0a02010201110316 83
    0x4444040038600710301082141c03004126035800076501440e400c010504c0b4141c594a0402506034414030845501d8504d4041c1501180d1030032480c6049038400a252681d03075940c440050003c04c1c0056000303500a8011800340d50706254441d824501903010ba013100c1d56503012030251050b00819140080c0705920030000000004e0303c42d40d10443d42070b8103043c0032a168180000003810f1507002800403005030b54500c1080902d14143c0103200d25110b209000314a01070668907100e1403480000c10800c0c003103914001100c200252580301c0c456454101255411071501e91034010040e1041260b40d200284000f0007050003458040200e90854080361541c503d0030b512004420300180c5010007603607014205215a080304e03102d00d60540f031070145580e070004000c0c1c10f100c100000ca03080b02450b0100c0c04406c0c0014000ca9800c4400c40350000001c08141740d581d501c0450072038902401038860403031a07007840714050004171700080d405400c80c401d800170700100310403c14125a030300044a80e01041021044155002 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 70744705 1250 70743455 70743487
    0x9081b0106030b010603020a08070311040b090328210917120c070806011a040620100212061f050a09080d05091503010806040b190e100b03010e03 64
    0x1002800109030780d075032610f4068071840c0c242d00000c042a00085e0b1101c04544c80001580e00044604080200c1005000f15400a0146000e404245100020300313100580c1c0802410b101c10821119801084681c0c42c00b5041c2921880f1080b51003140c02c003800003120810104900301f070180e0740d4a81104510f4070389000d03440b01400e01c618000d070180c44c0088541c1240d00e00200399601a000c024181c1514246400f450030310141d1100d15000c4031079410303040c0c002442c011034046503c1850450244d500310500c1599a0541e05141a01d9200340018810501c0072600a00144181008820140c2daa41e106016240c42809a00c1160f085001540c1020b02d01500140026000341c0c0341400e016629641350614011762007940c1c4010507030101b0300004626092842d0340518103002c2c90b4a0865241812080d503e14014000901c0310b0018000280514010421070100d1008800140096035000d0752098a070714170400303c1c1d14954100f014501541c1814061000d41d0200d6400851400b0a1f2032550316075 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 70745955 1250 70744705 70744747
    0x90b0f0402031305011424030a080a050c010614040b0904020904060e12030906040b01051e010c02130203041b08010209060702064006030608100c0e0d140d02010908 72
    0x1d034182c40a245400319100748102c0856000c5030400640340d0801664a60001f00312045400c0040c8420714000416100803800c252100d50000003541c558152020a80e01d078001e82c907604040f0b6181c60000101c001c1c0c40620b815502c0c0c03003900c0401c0100b0401040c8083d02204480c040c1d0481d02160100d0000384240d400703074040800e50419552401201509042a64001e680e00741066000b1020322040c0000d04944a004003411902844d0200c18110452014600d5103030b29410b01c0303031041030102513407225611406800700d0038004550340e1416140c907041d11805110700480710120003401003179100c0c051007103e502000c01800315060911903400c00034280d1000900100d5241015444070550001000080728010302100d900c0d003401088a9000c0c154034580d00600c20942401d60070014604003081c250b505002c3c0c0e100205403598060b0301502d00c0d010304221250061030f40030b040020f04c5142110912132500000c00c1c0e031984c1c1d0f0582c2080342a6004840301a02220703041000d00c800401c11050007403 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 70747205 1250 70745955 70745971
    0x6060a020a1704120609050d02010c020703140a06090b07022107020603040804050613150806010c030f02070f0801020406032016050a08070807021f050d020d0f020f070c090b0f040203 80
    0x214068030341c0042d0054000740b04c4201c80140d00c81030304100308041809207041801c2944020090301554400082d81c0e510b20b444050038100c640a20000030020620a49500b55040378042c0300d07401651078207401000c0c0490340e003001801101445090402007480710751021400d1251103080159540820003a0b07400a00100c400c0c1ca001c03c0000380c2900d941c000b41c401c01c0c11140440c00d820b0b103458401c50000081c14060404c005200040244a80c1c12121002807990036280c405007910350303598142d150500700d40042d180440010b0f0700280300e0205400810680d4410b9a0500480e1680b0494501d000c507140c0c011140303000184410b82403203084182e400b06450180c411a0f0758580d56444110705580558000d88101c0d10000d440030079420008035100c00303040c5100340044142086c401c01410340c0610003e407241503400160b484080112904805480003010320115a03804058201c1506031f48030302002c55803002d1036000010307243c030f66101e594030415000d0600c1200b40340340310400009610040082c0 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 70748455 1250 70747205 70747207
    0x905061b250302010212030405030a03090609020910080709020415081e0403050304030306081f0c11060108030d0e060f01050f04020409021204060b0a080a0602070c0302090f0403030506060a020a17 86
    0x1071442062000d01c40da44640d0a1a94161181580002800c01c00050000350700784034208280000500000121402c0796818a00003030681d6092400030050080404060742c0b20040b042840016207084085000b29001c0c50110b400041d507541c1c000050340a1480381023640c40f01e914081c00094000c4084aa05c01c00d03d00510090300c52600072011070b0b1405540c1a8001480801000105a0144a8000035004a9008100d002e5940c5801c10a4000d4804c00070b1034561202d000c10300d824012060301c11078030740540585803190703192a05995260000404e107060309003424000482c0d0301c00881c219000d0f03c080c2e40c4c5209141e0820080c0300c101800480781540080c1d00b00000503001c0002e101030300d40030000b42d1000d030480c103040c203225050b1f03110340580700d00c5440128000c01541d01e0010351102c040394481400350720b8070628140981050304030351019401104082c10050060000121548280c2c42500c08101c030352140c0d02403140a004600c01c10300580d0006210030041081d01900c0320300c9124a0640b9 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 70749705 1250 70748455 70748473
    0x612031b02060705030d02180607151a03030408060901110307020a170d02030109020a030b010f020c040b040204080d080f0109050103080307081009020c0309151e031003060504150c0905061b 83
    0x140e05d90752040c1180c1045590106054030201400500c210a0050403a40b0300c0c01d004140e01c0c0c0004000326000c3c036507141660b441c0f800f100d40b84002d031042013a02000b002d41c2c0e100c55a5010140c2c450000b190541a15480d2203100e940140c508400d42c1e000d5441c1c0e81c000c0c080a40300f9903d03000e010b407100115070f0307580e40d0600808510402c140000d6018282005025031500103083d8050140c0300c42c2014a418449030102a010a40d400181e1840041d0b08682c0400e20b1007460020034000d2082c2d41158a060003410080461180c12000450003141c2c1c051208203d0707aa18040e41e0304550342800010480386040000c9070b00b003403045c4035840d0080d164071680312402e42d9031610b035022644460282e010941010511a03103a04d020a40ca12805e0000c10b5680e00d480c8101c04c026503034811080b0582c008038408004200c0070b01c640c040c08005554401000c02280c20242440750701139400d90340400c6800d09016002c0e1030948a000c8260840301d02400f45400c05401d01c00401609401c0c141240d81341c404c44070fa0b = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 70750955 1250 70749705 70749713
    0x203010c0f020c0a080303240402040803040e0c16140114010e060a060306050a060507031214010e06011b030806011b0b0108010c090803070f060b040f0c030612031b020607 75
    0x10303425140c48951100d1103002150308001e81003420000d4194828107013508200100d00c0040100c0f5400b28140c00101e003c0041e9841102900c9413131122075070814030215010402c010000000e10544d41480555803081e50344a84000151080d480c44c180d03001d548640d20400244e8007481c0120f0004083d0000c100002058900912003e09030301c03120480d404039081c80024200032050341c0150a00d8507051141e03500b0000401d80005580c0310325010060001010014144590031024000b20050020b011450401c1c02c2516403660a009890080d14807101082c2c266004042024404030000164070844c506918203950100c40241190f040c800800c680390040c1c4039060915065602c1204607858a5051610160854800402103001d0007551141480101e000109468046a00114441680b9200d10b41000034007003c00d201703034101c0d0415040e2188515150030040100d501590100b00700c5903540369490031800e0034580580440c2c0280c84010501880807070f14100d60340003500c140e10304181661 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 70752205 1250 70750955 70750961
    0x70c090c0207030201030e0c1e010512010608070e0108191a03070306050a060e040c090e011d0d020d0e18060301020f03070203040303020606030a0305040b090a15020f01050c0315060a0c020301 84
    0x60104010b0708005818011503805205004144d07020500a0400f510b8980204101da0161030b84000321a440c000790794a9a031241044400104951011480704d50391124080c0013800300b07031000004115420303414030655100b18829417103001000c00b04e000e4088030b41c50700002814040d03404c41c184440600d41d10306a8a0030041d2800551184000090074030380300700400c084905940144560381e000c1c100380400715640d04480300c02c2d030307004000001750010210109401402c640f5607101460382d001140280340f110114010007100c1c1681c0a54143c0d00d80701c00c0c02c4610b00768149050307500441494412003420044500903602c240c016000501d00304c2040d0481d02540c0084803020010303800050244101070707042c046150040c0342a0018a180140c603039014000e40a035020381e003900072011031155099034820341c440c001030601c1d2181504d101c1c84480000d450310b80c0001081e50335828040803413201d40e00c14003102d01c600038925003240444c40d940200802548a03d44200c01c006101c0078141c00b40e5800c1c4 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 70753455 1250 70752205 70752221
    0x30402120708160b03040f02060a2c12060601140f040e0c041703030c070b06032e0c020703080d02070201050d060803030a0605040513060c020307050a06050601081b04030206070c09 79
    0x1100510f10b805010601c01c401c003201d42c1000c54000070501c207200001e04025000c84020394122202074407112864005c9030f00301204002c100d8088448030075440b146c8401d218800c0309542c1501c0810f10003091090b0580e890005a40b10390005000300310300b2005113003800140c0001c1d00c3d2004550300e020f540d607842c949803550580d10024031060000f001c0012101e00d1181800784e50059001c2d50543c5001c500815143c01811000380c0342154210004020b507505001c212105007018855000b25080b00f28607103030080400040d50b40c010301c0c12101ea034065000081d000116680690340910b060782400f400006034129840490501c041031250b01c03042082070060002818007403004548174503000150700c06a50b10b642c403583c0207a1805051014a2a203a40140300e1940c1001c03010501103a0220102d1071071052640140c2580103c1950390f041080c0c0c2d80015004040998800d95640c03a0700000c04104480c65101089c01c070010042040181007003400b400c501405410150070056880c0340410541c0c500c0 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 70754705 1250 70753455 70753469
    0x90d0b06270901060501021f0b0604030b0702010e0f011401090f0b0d050a031e0e0f01021c0c0506060f09040b070c02060706050a0614030a020607050109060c08092407050304021207 79
    0x7010003109450034803035100182801d1000b0040a2445c0001218070800103030000005902d51a4042854403080100c400440d405690f00c405490007560090081c6408100c444150140c011400d084240500440d800038001890030b18499190102030b400810350302d0341d810440c03078499902034034544e6139140d0914164050f001406c010700346854001c281506034403100103c02549802076012503440b0f000d012240743c2c180c0e03042c4034403011800141d01c1c02c504032040d400103100d0b140035a1609030703005500b03078440340c0300e00c00300d5038140c07240401c020b01003100303229654200460704c000030301081c1e07480212038006860f0b051022082c910f54010880d26804000c0c00d4841d03948800501c0103680607446940010b0500c0c00b0b030880326030199800251275180c0348078064482c440100310f0740c0600c5800e52000c0c0c41c0a60200b0200043c032295a8040e10b445000c41d00707207525010b001000094400424035070301031a403092200b0038642d903034481d00b0b44040c0c2014000782d0b000303401e00d03004130140007041103c08040e01d19 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 70755955 1250 70754705 70754779
    0xf060e040906050f010e0106170103080703020f061005090a020f0703080a11031303020c03010c05090f040209060d0605030d03020310051e040e0c0f030309030a02010f05070c0311010e06090d0b06 85
    0x601b20304060381501a8806820001e05003004841e80c0c80000f2100d041d03a5000d07051590b20031050404074500504008001c4981c01110140407401c0b0301646407a04540c03090b9000f80c955602c3c5680f480c01c9010b00c0d422251030040811041c400a4841c0d0130f00b59000301051000200800f84001c01402500110350b03031500544400c01030001c1c1a0100202c50301ca51080300288219118603200421034000c0303144190090a0600e0004c00b5692a42c050b100c3d08030020700807075241d0441318100707c0946918442d1500901030070301c10126062090085030301c90365005004040841c540018070440103131000c400c88154003200c18250b1a079841c0c0c002c00d4855031385900100111103403102000440583c0001d1640f00e50310410692142d07450200708180131503024200010001582d9805a0380380c843c90704007c02170030f00020081f040100c550140c075103011081c0e071341c505101e02035402e2111501c11a00c00a0b800015003818500045200c040103505c2000907101000a81c5185020703040c425502c5800445540 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 70757205 1250 70755955 70755959
    0xb12070308120a090201020c0919050c0703032003060f0a0801050405010603020a050d0308010e2a0703080106170415110d050f070207030323071221060f060e040906050f01 75
    0x4031884101c3d40040b0400c80c1041441d0032640040d5450b491038400c203000e92001400a07282130500340d011201040d585d4804d0140b8078110a20019540c043d000c104c004c42c1ca480c2c0c4046110340844001c4d000d486400220380c1c0740d070b100d05040001054111240c81d0380708100c0e01c0c011a0400082c01094096481a80081101d50840c410040c2c40700030746d0011070103517011240301d0003c02e5000d06c3c2241101c1d80c1c4604460540c130303100b54100111080c0d0409880c00d1300c0d6000010319800b420001014614065a21f020031a6224402200d26149282d01042c203c0c07000700c041400f0501c0408150a8503018240c000703480c24980c48201e41741d41010340752401c110754810400c0100c12180a0260b4042d1361480a41001d504546d000780c100e070f0300140d800c42c501c01403400c041000003185088410103500803a0141a001c100d11000345030041040c2406034140c1d14510400e11000540959810748142c1c0c00c8449500741081421101194a50034203a4803545501b4058045a19882154086c0c0e5071882c40c4200c943c = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 70758455 1250 70757205 70757227
    0x90d0f06231e090f030c070e0604110d0e2505040b06070b011a130b040501030e0d022e090804050108130b37020c010b0a0b03010303030b12070308 64
    0x1500c00300340350161811003000240346103207502000e01d80c0c2d00c02c2500310648514410790f140000c0c0c0100001107101c00180354221480000707007542100c2004460300c0c4580e50341c20601c02070324102c80149014400038404108506c9080c0c00c03084460076603104441760701072100075409203801d0141000d060b584411000f881142800e005880d004c00055840300d04d814041c0da00c4001065052044110030317103070801159000e10045007155031002c06401640703074407511280c5c00303a40d56000c2c1c401c40d40803a20303050141a14520100d20600b01c0a000c1c1c001e415000c6004400d5065a140c800600403258405c581065901c1c000d0f1007215a040c4c0113008031504c55040400250841d07801901c50b41e0101004a0355000042c0030f04222540805180241c6000074007180c0c10843d04021aa01058107401810103900e810f102e55003c0d00f0003081540c001e11030b400036070042c003203100c0160080b81c0c9000820001400400e0013a0030100b80740390050301541c5141c240030092400c3c400203400851f4100d000185010844e = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 70759705 1250 70758455 70758491
    0x303090b0c15190b030c0a090c02120a0206070305012117091309030305061903110402070b0a0e0d23090105040302030304060905010e06160303050a060909030503040c080f0a030302090d0f06 83
    0x4e8a0194010a0b202c1000c40003e0143e40c400d218001e412901d84100041640c824045c2c0036101020805068541004020280d10b40340129111b00020786031230000034103e400385101044884c0c0c00601020030f01c1d12500c51500c45010011600407100080256000315190304c2d50300b220f4031003060000105d00c2c01903c1c00a050303400c00345c941d610900b40b450044d15003000e02510744080302d901000c1c40d003a03c0100004070b8081c2c0075050000d440315420b9800c02000a01d6034100c90349403001c0c001582da401031402c101340c4d003401d00903401c105442c1c500c0c43e04801424000000304032038a0141015418241c2e02e90011f0b2031948550007510020346804400c10165800482c4c041026030112a00d074101555082d00c0d101884455102404160326070703002c21441420303039009001170f203207002041c03002900c5e0b4203018200758400d075004c40d9461104600080d2040c1c02103010141c040238000076212000b5180c42c120080d4201c4064954041101d40c50361000600900f090032440c6d100744404114a43c000d1865018 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 70760955 1250 70759705 70759721
    0xf0f1507060f09031202030403020c04021206030d020111090d05070e04032003070807020904030311030709060e03070302220f05010f030201020d02060903270301020c0a1401060303090b0c1519 84
    0x4a0030440f00400080d00604c034040680e90b10303c8016225a5035003012803400200e128540c0c3c010f480000c1c001c00e440e0180c036141e882480b090303045401c450500c1070102c0c2201c54240c1145180107082c00703030380c095240405180c1c40490091086440b0705450b0352601c00c403030b5406e890440120306540e4403c1151126500100882c98803000510304150039a01c4040c0c040c81210002885010508002820940650712028500380a45446512407903c140080c0c80318546004640110314980765980d5145000142c580943e503004d0024803c0d4140c800c030010360105d6001001c2c42d11911040044480d9810b480790f54004c210001030002c00c68a580006810281101c1101045400100822403001030000407220720f00341058101b286d120702c41f1000826800404003003a815400081d41a20810380011180c3d400740c060403c1161074032a4501d001e08031121480000c3c0400c00e805420420950306002500b5410017507001d4950001a00f03c160102e004101c400703543d40c071003c0c0240d007103036442c80c418929 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 70762205 1250 70760955 70760981
    0x51306051603030b01030906141b09062a010c03050105090603030705060106050a11061005040e07030b01060507081b1f0b03030403060c02030c100b090a05150f0f150706 74
    0x1c5410958050703007070400540c01d009018107468111800c2683d10030b6200000c0c09410175005c00c8a0003510f144001590340680c2e0070041000d09541140360382901c0011180c200300010403042c90311400c0002014030065100c1d07180c1e1b5200109991580c014420301490003101101d03540014158102001c109001c0000740c903450107640f040c0207640010714001010741c192031b101d041068440345045411100c40c2c0e00781342000910702424003406045401c1c007003008256a000c480501040c01103070051552a5443e120103028441c0010040046500490041880b14000c1d0303c024030b01160b8003650074902c502540e50021541c4556401600b1417440a214804010b00c0b9405100c0d01c0c1d003e1001940d03e0245003c06008240e43d1141c0900041c0200201e4980c1118a001d4544807103d4414110040c5202c6442901820940c00001d0222003617109051203040c0050360030b041c045500f02446141020051603603040404c05d84410349940d40e90b2a01d010407900b52400503aa52803920f03048041d6003400600d85 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 70763455 1250 70762205 70762207
    0x13030306090c0206060f190b130503190b0408040902030403080a050702011505010e040e07080d140f1b1237210609020a09091a0f04150504020a05130605 67
    0x40005501213507441c1c200c802180e001c551311464100240084001c1503200500c1012084001122200c850107011032515080348640201d42d20341c10301d525800001c10241000343c0110242c00080c04240016400c6802440702d5800d00da2201c0501049070b205582c103074041755600c8100000200140125640914035100038408846140c0d00000d91584500038076050000d040500b51040d07d480d8040c0a82c001c03100c3c00c880074a40e4908440d034079003201903071550010306400b01004aa801c00002c03100341010003c84145080000d908180c0c0b03010300f041c0680018012141c0103840091081d001e0180a00c90b250940e058080990b1407510f903003c3c040c030608600344000008a02c50307170030242d9503910004031402c0c42d01c0e03d03a00072050b0700200741076001000003610104034009150341c804411404d645a0700340412419460b046001018142840401e60040320070320709180c0d0342031503005400d0319a4014000c0103a6501c035400581660070441c0e0080005401203a400b085003000c2c5054002400941445 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 70764705 1250 70763455 70763471
    0x2030c01030e0619020712082e06080a0209030a06051e04110105070f0618031202182205011410050705101d0604050a0507140f04051b031303030609 65
    0x9545902006000c101315074082001d00002c0000c0c2d0301181c111603481084030a00020f405405000500103540c0d070b0114003110030011900c0304031010000384590020a00c801c103146004001c8504030300c003d000540464080c0302200c1141c404010344030b1000d110701000704891400d1016401940c1480e00110000d07510300003440041751600e451501d04c0d810a180084c0c0e10319141c10201c2c2000c0e002c43d80100740c10f180250500b014184040002c00d070500c682d0394210305256019041c0140e00400c0f251071041c44c00f0884a807590b18184003140b00c400c0802094240c402061039000003180d400760700c524190501c280c484020792904040840750710007942402400c03d6425181d1075030711101030f143c0f500c002c0c0c1c0ea10030084040b6842d502c07030a0403c1c003040448481d45072900e405511ba6000000480781c2c0d104034000854880020307810103124030006130921080341b005400b000082d040141102e012448604147c81e1030348044002184104c03507200003100702d06480d240080072907802e0303800422082c0c41c210003 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 70765955 1250 70764705 70764731
    0x302090109030204050709120809040c110607110f1b15040b0d0513080409090203060603010c0507170d0c021f1802040b13152103052d041202030c0103 66
    0x440740550383c040e20000b0306691207080070703996200c06130004980f0005020b010000c01180000a018411043c1c4052202000c915800d8407901c05108403000103410000001e400ca61203400003d0304280340004690044142c64201424040802402a03803294000300d0200c10b4142441c1207180d8a0552a107d40b81c640b620180c0c0259002d401c4020001a48620101d00b90f0300c180310350515003603048a80c0a60f80d070307a2071441200a0000301000c034000c2c00781200048640c5010b02c501c0c150503003245c6031a460080030b641d880710480181501800040c80500180040c14410b100300c04400c8480d40041585002201a04181401032005000c40908210040005c01c80c0c40d0058011240d05407808100d800b581e07000603c00062000c1002802c900e0041d80f004445c0075104480100d03800515050401c090062160310010707a00c00e40980460030803c400c40861040e1a10b101110601c030560704800459002e80310942c0d40658040c0030345245101c054410351600344106a1090740034241000721508040c5 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 70767205 1250 70765955 70765967
    0x937170303070f050d090206040b07061d1e012a080c0c07120303020702100503010f0501050313080304140d0c150506011707020c0913050106061803061107060c0e090703020901 77
    0xb6031804200c0007103905d40307aa400c5508050341080c0d00409060312140c071401c502c0c005400208003661800d0925141c2e0711070441c041f2a101c07040b00b200c030151290349035070f503180307910741000b1040c0300560b41d81c1d40304104e003a1102058080d1440354941c401c40746807110500080285002501c43d80d07407120200400d01c042c90300003078030b001290b0580e10b0007010b40c00790b81420382c028000d10748040c2d044048045815003196002c0c0007141a100c1561443c00d0094549004503107500003254001654805000da040220b101d110185511511445d4410803650a2009860500d8440710f001c0022a441030401000c200716540e09a200c2e03034144000b00024a01400028200080c2da0351100f41500300e8401704860078424402a21500310140a00d01c8500780b100030840c10400c44401500c00354603112001c83d41501c900441741080c03050a80101196055885400043c25140c400e4070b0680c0c410040b01000508034005c50a0390174407510741c021141e0148041c0501c640b8018000801c151040150310340e182c0c1c11603 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 70768455 1250 70767205 70767227
    0x4240f0207060e09181905190305070204051b040303030b031b0f010f02010b040603050705040f020304081b0c090f0a0c090f03110d0804080d0906090308093717030307 73
    0x4d42603d080d481e020403a4080044024044086018051481d894021112151900c0c01e01c40c20484014800e010f40346d292003110080000d0001b10700300074081c054901908055007129103803da842000d031074450420015440340e4011804aa110401c12801c0d280c207200c5408a28103483c0642c0200c042c4000045a41d000228170905200e9170142640740103200f50f00050590101510821000c1c0c0c0301d0800725034a50300b52160078403540c00c09403116400c0e05140285c074025948140d500e81040e0003451440703500041c001a01c0c2e01e0303100d1a07204940e00c1e92841b4000d4054840142c2c41c07229410403644e070394190303080d0110703540c10300c2100386040180305502401c0d681240e41002054220384600d0700041c0000c0c8070110080c00c10b01c00070401245420000c03d00400c42102130710b882000540d502e40031388207803c01d44005803000c0344c180002e044904040f1400c00c0b1306000b41004900e9518050130101c10600425180300c4003124450b420302844040058000e00c02d10481e00840c29444c080600410b002c0300d01c = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 70769705 1250 70768455 70768459
    0x1d040b0d0305132c010803090d170d0501060306051816050901110d08070801090c1706010e13060f0e1003020d030215090606011209050d0e0604240f0207060e 69
    0x2c0d00f00b04190204902c801030040024102100c080c2c526080780b400150024040010000c0000002c003041e00008a03140200d01400d100d80d07041d900c1c1c0320310410b007400002400c0805020890700146c18036522031103010381742c2600d001501b00e041c081401549030000c08600c3c00025900280403408054035942740c1c036a5041e180c15969403d503000102c4040c0034040185081d446440c0700f0124803a00800c416101d42e130241e594a0a0780c0c3c0ea0b0391031906035909600e44401045007024490030606103603502035030220040c140243d1000c8000046111084442c2d003401155944007001c1c01035024450080300105500030b405070003420b00004298040d1124800240b09a101000c070f9010540284000d02c03901c4000c0b5901d250a2a00581e1280c03540701c12a84a8005400c4481c40c43c030b614211303c682814942c0000040c400c9465030f00d4155980304c00c044001c2e034407450621000854100d400c0d480909089041501e20580d003004001034905030141440d074043d034100a50030300c61154010062003180d042 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 70770955 1250 70769705 70769707
    0x60e0309130e030423090906010308070213020408060a0f0b010f050f070f05030a030603031e1d0a050402070809040c030b0306040f0303020d0203070e0906030607140304080f0a1d040b0d0305 83
    0x50300410b4914030456006500005142d450b90b11007600b0341700310b03c500d20001c1d58002c009656014009841e0b4909000040070b0340410300c030440141c10110188070802100950052400c2c0e240c2c501e0916000c81224641441916030204130301c04503450049841c00032003800c10041001e92404080c2282c01020100030b141d08002c80d404c0c0605c0020441303c0d06d02504502a290380c0d517404a0024080d10540c0000d801183da18200d401503c045010250012445503507130280280d40c0003644070403d1080c07918198068403000010a2554841c4000d0411501c59201107030350300502c00a000c203035000c43c4c45400a040c41d11450a0103600c1c04121a035215611a81e266400b42c200d207416402406913600c40c00c2e9640c404010010301582004407c02000c00868400b100c80da1004100f40d0345500890748100011201c1c2c0107940300190950246400c64400e880c9a802d01c001d000c2480010740000c4590b0f40012404003000e0b481403010285417000c020f0035501805004101c1c0013042061404050007010130030 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 70772205 1250 70770955 70770971
    0x307050d092105030409060b0d110a0e090901091514090f0a0f05070b0708070b0a0e030a030902010c120305060a06111b01180306050610020105100515040b030f0103060e030913 77
    0xf0060040350064403043d82c0820107181c032445105519002605015082d40c0342607000f0000c0d07082e00059410805155071078141184000007803081d100701c09052400a9901e5a041034001100c1c01100c40000d041040002181050250100090040504861881c0c0c201ca0308031240c40d02e0214800f13000942082c5d4200c3ea108040c50b11a00d0f000b580e500041c2040d4012488204101c3c0c1c88004051040c0100008042521409240800c50300c0c1041c0c80c054640c406c12264501c64003a402282403079005050100b403200e41c9480c0ea0018841580940d000a9980c1041000d41e00c0c082214202424051602002241b6140c40341a0f9605800580c0c5104070310405c10008103a1040b090419504202c40c5824030083d601e00d407030405050180c0b0007500c585514040501028414400c81e80308000c0c0301001c4000a20701014002e0241d00341c00054003217038082001241a103003903801140694000000b21549601d5410075400b151500d1801402c1d9400c1040001050f55030f14110400d03080c661540002c140c0 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 70773455 1250 70772205 70772213
    0x10503060a1104080703150e0c0108011818060b0108010b070f060b0a0b0c010b03071e051201020702120a0314040b0d0e010b030a05100b030304061715040504050307050d0921 76
    0x3c000c940c031001c0709100c0e200c000b01c10414040002618203102034001e105125910007800c0e150402006858005241e0340010408500c01e283d48040310f0441d4500010007611520001c10302c900016800e8803d10f8441c0d000c1c1500e943e02050317160040c481000b000342054003641c0e03441780c1d410007144050403003500c2e80811041c0c1d5507110024001000c002101e9aa108020140d19001e070000401e114420b0142d4940020400c80d191040100a0980c011030300c021410300041001010010390108071965017802124010303210788e2040c0010030065002860604c01b2860001c02c1c801d8141045504040300b800200401201d40c0140d509500101c84045002180024098010710b5a1007055034588540c281c400d00740300c004103d8504100f2218000d000d4100f8500c04d141d0303203100d10f11810000502611100d0380c2441c5800e03649070404500b12459011003400000a020f491303040d207003901c81d5000012080d0130000104801880400d050503c4542245050000c2418500c841c4112a210b0030190460b0100 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 70774705 1250 70773455 70773457
    0x61d0a0b1f180c020705010503070203040902180a0b130503010b06030f063106050d0b160c06060e010e0601030e0c0d06020c0d0203030601021b090a0207050a1205130e010503060a11 79
    0x600701d80030010b01c5084601619038042c1070391039602e0300503008882001c00c4a51299086074803811454009600e030615001425009602203902c0d80840c003408801810655603a0301118000c000203c0c0080d194035600034200a03032070380380e403002d032280e898114032000303c5e10f038601078a41c00050789852011503a04c9034085003100a156101c28030205440c17155030012001c18450310311481018604218064075074060103059422642d0181c10f803083e40000840e900905d00102c4508541c17031a180d2080c1459580b000181d41306600710000c1000100c005201b0150b0383c0c95100e0f03010209103000e100346201801013540310800c068220f401650420f406409011140d01150822560141210070100c1c2c6c08030000c3d140d400035101140180030302d0442d04031100400344030644060f4000c04480e05512070840c00002036003e6174088501d409000001c40104043c01050354580865440321a50354105980804030319105800c081d406000c00320040c403040e02c0001c0c3c07280d4450700280d00080d10401130510704000e = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 70775955 1250 70774705 70774709
    0x601180e0c0d0302030a031505030a08030c1b0a03032d05070c0813030b010f03030813290417070305070f03050c0a0c08060106080c0a0e01030b040603061d0a0b1f 71
    0xc6000b01610a0030994000010800c0003000d540820281500d24400504007000d0b10079160302d83d10050782c19001c034200c00025500f0003101042c04c1d29080d100d02440d04400d8081802c0034440c3c2207550402e0030706800d80211241c81c599860b2114010700d102d041c040e00304c0b8410840e0302440784d4801c0001c190501514110b8030032608190960b88810061000031841801c5010803159010580c00001c3da00c540312850074240d0341d054403101e0256807150317501181011203e000343c82c02d0000c5440d41221044800301c0c4080b540f03441380c8400c00f6141509101c07401c0e104242c05480b014004002040c0420b40c0482910384c43da91081849509044905040b90076000b21502100b940c0107100c0c0c0681040035000440044500003c00d03120160798601c82500c0c002011914203481001c0bc106020b49280305412800518505060009141490b1000f29088807510381003181c0441d0340e104012506840f10703656101c41c4100500404204140342d13260b03d81d2010117003122a059110240600c00450317003c0c0c0c4000 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 70777205 1250 70775955 70775959
    0x12030a060e01151413230f06180105090618120d0c0f0204020c16090b010203090f010c050f1c090b030103030e0d060f05040b220c180b0301090c05010801080601180e0c 73
    0x10703020b602c401405006d10310030300104c0c40f0006c0b50f8844401c02d0810340e21038407940500802d482d00b009400070741180400c1e802d0703c0c164104001041000620365525014110000300040034080c80c524500a2080c901e4404155110ba640311421030072015500508020040d54006040f1a5106491010a002c0c5c05840c0c0c50010a000b4013022020317085c0d41c0c078081800c54100c0303030080c40101e00440041e0385034880c078440c0c56080842010301c2c45a6502482e4400b4095210703600b20313804100c0382c0c041581002c0a05146010302e489002004411a078801f180a001d0100145503078515459079030080c00d058175107042c071401010001c1c081d41c180401d03980849082c100c2c480041c00320380f80a1030103100c0840e04403890f0f003814400076066000c12860b0882d000b5100c0e4480c90002040341041898541d1450f01204e1f8030242b62503903c440c1f10b42e2428000d8250461044028400582c1818000b40040764140c1082003158400d01c01081100c600126a810751212a80005031140f0343c0108641420200311000c0c0d = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 70778455 1250 70777205 70777237
    0xf0d150311010207140a091806050f0907050a0815040c0b03040b070801090b0f040b190806010f151413030b0f0901050705070b0f06011112030a060e011514 68
    0x1050203403034140500078240036401e0350312294403299501c4414007840a0184c10070b284420a1240141c10340c0201070020441106000c0c071a1265584400d07900103c6010380b04038224030620451030750421207200036000c1141c1500341075081641c12681c408400040c408800c84207808141400b100c4030203c805401d0b01c11100e030703603841e00e400c100303500c080c0c00c2d2010000600040d000040c1141c0600c0f5100358050010064581030f60140e04000280c001c103180194070031203800c0f003005030800d20002c0500814103e00540015032500001c00350104c03040d0320140300d0510145290100580c0011184d16603200300d42140e0f100ca081c401c04680680c0743d604001c1c080c01181c01800202c500d4180e1461186403450000d109907620010110384c0ea000d080801000103801401041421701e401c482154080f4040c0f42200c1004800d8003664076101d90820007043c1c0c600004140207440c00c1900070607001e401c03040361316101c0e545096000d8071010411500c0004100300c1040d4001b42102460807190013460440c82c007 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 70779705 1250 70778455 70778459
    0x180227040b0c07150b0a0501030e0604030c150e06040501050f0f04030507060f050c07110307080d080c0f0a050c06010f030f020103150503100b130506010504180b100f031d030f0d15 79
    0x81c0001d0418021080c030803001c0d04000187d5610a000da085021501c0000e030501d501d607a0307015240196a4001207a4500c031308402520300c10440d2080c00502803282e030040c110390805060440c00c58001801c500003003003248003001222011141ca030758001ea410710b0410756400315400c0100080941c00c0754408503604140a200f41e61f442800a0300320b50340282034045440786070104265a90800b80700e1000c917500b03e408940f180c0b900074491a64001d440c000101c1c503140000015802c0c942c040886030011800100700b0035010318080203c113001d0500000c8121800d41952202c6071310003201c02c0024105500c3d940d910b0b400321401c00c420300050070080d04644c40391555580303607000b50200d14a00b50141d421004403200304080703070251a02401043c0c5805107058244a5806c03025140100c81c10b560b11f486022008681d1121824002c0320b13115556603040403c1072160040a9440e40c1050b24066201c08107200002d000100c100e40c91004640002e546d914180b207020005060f0b41070940000d42812040 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 70780955 1250 70779705 70779743
    0x102030a0507020607080f010b0901170103050102041701020903071a0c070303081803090901030206070f080307090e070c15050a11030103050a0c0605040815040f0204180227040b0c07 80
    0x12160064201d81c0913200503a0b11a04e045680c1d100c211000c0d003040011000411081c141540108000702061400d0320100c808654a00d00050017070788121966075000401700070002003481c0d0340c0d40000340180203501d0051000d0009a88091034010700c1c00c10400602c1e00c6480703043e0b2804031110311003d9019100c08550f01c0c2005413003100c6c200c4030030413080030003004400900d60105c11905900c500601504440c0d003950240b2202c0d0304511402c640014041c400840883d6841b40950300c81e14803980c1e15104141021003110481d500580303001c09105049004400088100026540b60a200100000c46650b088401c4024018026000c00020030000000c400c1c840c0116030005810b000d46008140d0a540307200c101c54a2066205034010740e04900e402511840010146a41003405401400030080c00794001a0803100901c0042d03c104c40c0200041d404c6080c00c00c1080d6142b85260540031020300302c040c45603148200200300916041c100000500004400d2b010340b2030064204032070a540e0012605 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 70782205 1250 70780955 70780961
    0x9050a0b06040507050901080f0a06080f030a02100209010215040204020d090302160609060906182601060e2a1b030403030e03070302130c020705060a031a0d0b0403080c0c0102030a 79
    0x2201c074000c40c1050005a0080c0c0120100e8915510682d1520340b960340c0e0114500705c1003005130201d4603030703502c0304400240d66404001d40030400c3e14643c041c641c3e400342030f08041e151600a5811590090050046c6101c076a00404d4800d907078a841c0c501a9445e64452001900a01c40e12a0401c4064513081800c01416070029540440c090b64003210345201d920385005440010152007104001400c40c034041c840a4458080962000311b886074814600d40c0319020701045900740c0c5519940501c00402103850040d00b400b484000f04102400f0b4900c9040811200d491411040d8000c01007004200402c84c016051000315851261aa002c03a0600401c20107100d499038840d00c0150001100300350b81031943d00e030105d8000c2c1100ea0040000300c00c0c0c6003076001e00b8094141008103000354003810303c2c0005c66484110080c0041e80c21550300140c01c440b04103905142c141d80b040000e010725603800783c0701c0c001a84510690f0b005505810110010364460001d81d5241c8107102d50641c2d51b500100620103480341e150 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 70783455 1250 70782205 70782211
    0xf0301090507080c0a050a05210304050418050d031505010e0d05070311030d03050c0a030b2107090f020c03040603020306060d060807031103061905130503030f152d010309050a0b 78
    0x19800380e505da644d18200304021100740609680040c0509401c02c59994020440400d803080d0419642466581c0000130202d400458103810a6101130800304108a400d00183d82904040d00f01080f03048050211282092201d004440c18410501c0c03440145030b58451600e00d10390350000464006648034503282d500303c441181032070701034403030800c00300d08441c041d004091003030f40321007000c0e401c1ca034a10104901400390701056940140d1641090104860501d144202c445000001480d2142c03901d2300500459918030714201000b441885a0380c2c101002008071012690755240140c0c49848104c0003412521840600381ba0f12481c0c8403001411003c0804c4510440b400b84140c1584101a0014980c4601040341c000001d902042c900114114440c0c2c801c1750402138202d008140c2d43d0982d91202d1071988184c8090310110001030401880c2d42c035401d16507000d90020360317008084000c5900d145584180b081c2c40d0f5884411b010701d0711216030f4865441210040e40010849900c0c0381d403414003d90400781a = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 70784705 1250 70783455 70783459
    0x706021b0705062713050a0902030c031506041a060304051f020327031b011a0102032109031c0207020103050106090b0a0302031b04150e09040b060f0301090507080c 72
    0x12080000b0309143c44425100c1480f014020303001c401441c03110600c640b5900341540340d485140d05034036154800d034070f200700381c4901d01e01c810000c3c2402c0b0500401d03152502d5041c2003803080e409411010010581c540344260800d106640101d4840340902c00d401d00070545680450308a04040200001d112002598070341c001d01c2c5a64406150002c94040c030103a00c002ca54400841c000e18108111035940c4107110442c020303000d82070300e003080c0403411091201c501845140d00c640e91680d1007003842e02c0201040d05402c5809000652070081032820b50303031100b02864401401c41d14002d0026400c40001d000303d401220004060b82d142d40c90204150000350014042070303000902e031000200d885405031380200151555038160604100100104402035070008141034080303141e41c4004980a100d12004d000a0002d80c1d44e45080e0453b000001410384c4002d2000c9403184407180300b4080454900c0311603542055051300c41c0407118a170513021902602c43c07101300a05e54070840c000041c1d21400440c1c550307820102 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 70785955 1250 70784705 70784713
    0x1b0804080c0d120c0e0d120c1709030f03090d080c0a050604030c140c060409090c030c0e01170a02010504060309050321090106050f06030703020901140309030417061018020706021b 79
    0xb441310110303200d40c40460760b01d8118082c6d4078404d0106941d035020525105843c035080d20250302a9071418280610791202d800342120100380381000d460240207100100a00000450178001c00c0b00000701a00001000a01030380400901406c0010051043d41540f0b9000700440f4040d0810b442d000317200002e0740c0411b584d2640444001507014002048114003503100818450409082851300402805981da08845040807034000000140daa4550103006249015085c0c42640c54080314040321440ca00c10b0700d507140c000c10150001070380c000c0260b6040e01c04034940000c29844030b151a515600c60107081c49281032425440e0551596a10a5980b003090114000d014642c2c3d2901800082004e100003140c0c00784062000a003140c3c4664003801c01060140f4150540007680114030b031056205803002c01283c0c00025040c0800e0349a070344601d496441401c002c0805180c410a1140148014051444c11001103403051011030003907010303211003d4000c1000c66450703021030300309606030360300001c086002d0203 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 70787205 1250 70785955 70785971
    0xc0307080708070c0305180d0c1716030809060f120105040b0303070302060a0203060f1005030103050105060906060703030e1c08040c0f060203030c1c05040b06131b0804080c0d12 78
    0x22040500314012a11902c80c00944d074090399054504ea000101790295021400040c07030010740c1c82084081c41d5501651403513201ca07042c10081c0103105094208068581e001715500820150307015281400c80340c01034042900c940212001402c548940100000d10b000c020410340004409603030414125001154100302c0362480c13005241e140e025034000034000d43c0017140050080c0040b40c001b1a44040c0050030b61203040c0c3d102c0006100d00c103203c1c0c9914000f4001000500821000740b184903080802100e0b01754940c0307003550010756940b00e000c10040806440344540307815900100b01c0c2c0c00c90188094024090800c0d0314000030001c5900700e4080d00c0b0001e07655000500394944800d0341d425a002c5a001d1459a950038803643e60f1070f400740341d1051040c030400e024444210983d208150065202d854107201ca410f102c010065504a0f0411420b0407510342062140c41c0b02141d9516617020041d420403441556460518003c540102c023550710301800b8820192110940c0300d81d4184049103c5803042102d01c1e = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 70788455 1250 70787205 70787207
    0xe01030609050109020909071d0d060905070e0708070207030c051c140a02030c090c09010f021903031b09050901060f0306031a07140304020904140a06111c110702040509030f030c03070807 82
    0x81c6903189c810084022000400443d41408014906480e02503c1c01003440c08190740c2700341c50404c00d940312207560174102050000c00c42e446903216421408510080590b02d00303644460911042d103106031071141012000c0b240b016120381c03860926240d000114141100b91a500b02511885e8400c0124030a0064030302101c4680b411302080760003103002400707060608201000555842d041640207030107504c80c06600702020111080700081d014807942e4007280c4000c540c50503a201c0f490102031201130040100003070140344c49540e400d0313044444074608020344d036903a25410340c0201115000540701620030b491200502403a8030801c1e001e10307210303564105080c81042d030007016408140d8000b54440400c002040100740b81c51001018200c2c0d100c299018480c096440c001104d809200075619003d000c209911444050302c4400cad03503500380f5042444503042c9450086101d204200c030003031241e0707501c00c0801c074075200400a86d4240094010f03010364074288a0700000544d0412190f11000940c1365000a51032 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 70789705 1250 70788455 70788467
    0x11011d15150f0d060c0306090b010806030d050318010e0304081218060a1e02060708010909030210090305070209010b04030c0f1401080c090a120b0a110a0e0103060905010902090907 79
    0x1282025005080e60000c40200212407042c4640968411503c94050000c2040d510950800501c9500c0010b00d040c54040d203a4213807007450722000e05000181b070400481b40c03001301e800b0307a22a005180003640c3c0d690310040d85608510040c4081420340c64414505218080000240f054440d0401240e8035454012501d06280c4078498812102c06104c0094031420309040c4007502e040c902030308200d00d10140c030f1000310318100031600c19000164001c905001c901038000d1803c0c0d0142003810018030282a82e40c81c041d598004905185900ea82d84480950a06115400b6509510f50080c4103108a503944c42915110b5040f6000940300d111000400040042004100c00c0442c0c0d03011004510450b00c0340c0065581d050014024250041e0410101070b06650f030440c03210107881f082c00b03488400146410f2091800030300a24000d07034a0f1801c1c0c080690444624143c80381402c6031702c0c01102c441c80300c0c0c004030003600b010303070100307079001d00b0000041900c00d00341d00904980d003020b40e0409895510340c8000c8500b = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 70790955 1250 70789705 70789711
    0xf0711030a0c0e060f04090506180606010e010c08210f060a050a0b07060609020f0d0b0315040209180d05031911030105010c0602040f03050d02070f03020105041511011d15 75
    0x25103030140b4010403146054244103503115500510340e100d005440000700b0152600001c0c00c90345238000f001009054044240360701135200902009040f84e240940c00030f007603240284109810320003011944c108120040040743c100d2140d941d4000403012040c48064600b40c4140c83d28079901580000091040c10200c0001c0b0442d40300030000b41306940340c4080e2101c00d83c011003050700c646440d1030012400502c0c80c00100301c129800d03480701daa80d4844415040868640003a0340f440f0340c0010038212407240c801c0507107513002074040318200c2103034440001400d00c21045c080845402e018a056512400341c00c94061449a54521000600140340c0d542da00101d404d91510700d81607013802e20051120754030a004d1401c0381c0d4820040149840d4403400d00c0500c14125a00c1100d180d448408951005503050116000404000300803600890a40d0700280103405a400341c01040881d40c0150b80310b86100c0c00010b07078900000b17002000244070703420300660306422869940701c0364480d41d524510004412041144 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 70792205 1250 70790955 70790963
    0x50301180e01020a090518070f08060f120304060f03090f12052203030f08190c02070302030a060b0103180503090f0d0204180606080d080a15050907030b1302030702030306010c0201090b0f0711030a 86
    0x1270607020302c0c00c0d600800702424107500314403240c10010042c0c9615a0710007a0000c60001140c80f1850520000c0048508a003028101401c000300e120006d084011303d00000c0d644024281e003c00084d54088480d400b51000022034851030709410008041c542104a0942c5e019546850070b407082c4000940c4e1402d41641c15407181c4d4914034814103c3c8919500024041da014819902103556980009280c0b080314442524465aa4071801005680500c6004000c410b01076401d600d52040e03487d201d850f40540c51050380118105e81c2101c5103541c0d900a14224194014000c0060700b800480c0079210000c059001c0b10002d283c0132010420319000190341c0c0d020801d56807080f415942d840c1c540d4010f484c40b82c2d244c10004d0890305000c68190f80b01c0d812584911440d42d030005041c6120010411203805e5244500050b520410500030540e81c040708990b4030041c2820802d00d40d620510040f100e451007948699282400482c079584090b9248000b0000a4001c241c602c01020b410700815840c6c00007840010 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 70793455 1250 70792205 70792217
    0x302090607060506010504080a14060a0b0108010b090402040f0305010e010c030e070b37021204030206070305220b1c06050303270a12030f080601050301180e01020a09051807 76
    0x307030001c2e030242c00580c0d10000c10700d400342c00c180d0b036182c2c1e442c83d0600083e41120850090388000260840410503598803003440b820522000c80c941c000031700102d0040c01068240100001e04000030384860b01220300420300310100c440d01d0343d540d040007070082c213124084422550030700d2041c5007c14401c1c000c0c40c109d01a100041e00581e03251105849440c2c0c0071a2014200303818040841032910004450140302c0003201500350000c59183c07034001e06001c0203040005414409000510150301c4102c141e5007110b0b498240035a4440c0c4a003429400300380d11000343c0454034460003000ca4401030b000047c00d031400082000f03050b0328000004400076074400d40184c540582c81030000c110001c240098103607002c0c5101c0b0709428081d14003008110324106036000118041c5444504404040d030045203031807004c00c5441e01ca515400d080000a10030711040c4141212a00d107074250701500d161711b41c041c15010284e0300085503114203001001c0c00c140554411103112303010400701a25038400130020035200f411039a441d4 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 70794705 1250 70793455 70793467
    0x405090d030f150609170d120e0c030d02010c1404140108071e0504050a0b1218030d0204031a0c040608062e02070e0603072601110f040806010603020906 67
    0x49008040d01d0ba405101c85032650b4020082c0010b0309441030241c0560b56485140d903061070b066800c0c1d0010200440c20329400584001940c91380440800d686800d00300012071040c2d80c00c83d205140252460006034140680b07140000482e8056001145c1141e05459202412003040c10461460140348502007000400d482401c0f0150301c2420510f5011010341070510a0030341000e40010052081c881c0000460300016041c0100d11300301a5140c020440800c071240348c19100c200750244040301030b060b0398280c0011035200844500a00030345444e43d000c40f10841d19180c1e00d040c00c6030899400c20f000001d0a0028000c5196508400100d50598446032600442502c2c0c100900003540b84036131a421040480d200317900442254055024003140f903507801820f2060815810030007074040580300070b20a034410340c8200240d400c00da413044d038081407040b02403071034076034010341c403030162500904815130300f20005000b0720312034810006007081c0d40c1030000300ca6581e80c03182d2041d402c0384030307401c0200e0b4048424446 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 70795955 1250 70794705 70794707
    0x30905070e1e04080322021f050f0f0910090f030f05100203010801090302060609010501020d0305190903050406090503070317030a060e09010b0411160b0c07050a0303050601030b0405090d 82
    0x151904405122465030b41e151520b20140045401550121802c8400006101021020702c071901e00c0050401a0780f00302079440d500060824070401210b030801140404a207805501401c20b90b00a0044c00b84079a0b5207840e641c60b100c00d0360344001c8030a48544203070180d4011041c0308060880c2501c040300c0d4040c1070036046443e6611040f1404104485030b1241c0303c10030109810034000f441c000c0a0060002c1a00300c4c96107400303424160020400303806103010000400540e82c1c0010903000301215400d0004040d11503042c010f00c1034803194042c000507820903680750700b0554408020303c00c942d01e036514003103041d884204060301c0300b03107501c000342030504200141868130303080c40001d60300003507200c10010f40d0071350b18000425810411a030b00c040b6a50741d150790006509090107801034454100b41e00034503090701402000b200010075280580611141000500b4a6640c401187d1605d0b41090072142c052030b40f4a4020007a0000312803103400a820500303034020380d04183c0903040c010880b1a014221038918594 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 70797205 1250 70795955 70795979
    0x7050607060204150804140a03080601050d0204150f080a051303050d0207020a0e090c0a0515070c1215060b070210050901090b0c0d0e01021b150c0303100f0603090507 73
    0x502990015420000010704000340701c86a070000059417220b03007080c0740904103034010740f4003c000214150400c954110010703030b010451320340c0410309003030058646980c2d400040081c01140c12201c42500700c0c42410403002d400c120004c03a135075415a01c503546a0340d1420701030300366501075400d00704050307207641440300280c0500d02074030740030200c44001824004540c000401041f0564060b076400300c24a424845950b6043c4407095924100382c4021440c50315005c04590888240031507a8072036040480c00504102c13007200500000e0502103904501540c05040c81f00d0214980049214618982240000c0b030103110301c141c2e046281c0040403440c42c5003000d82c00f40c1d01640034030070700c4e41003040c074010100307001071804080c2c5048002e080c01800ea13400b268a0182c0302c82281e10402d419035004070140345074906507440d0141c1145059a1075483d800341c060700d0000a0003404602d50349400701104001c103200740600f0000c11a004100d2403c00d040d1358007003c0d030450b01d803040301800540101c8000e00440c400d80f5 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 70798455 1250 70797205 70797217
    0x160308060d05100905010e0f1e0a02060a0509040b090106020a03030c1808070305070501020718090f021002031e03131e0f0b040b1f030605040f02030f07180e070506 72
    0x24103180722642096079140e050201c0309a080103107941d1011494180502485200300000c5144000c00b9419441940c4941e1120711040344441c0301200358040200110600a07061110760181c46036440d0303c0c103041c001c0c2141d040546075034041c91400a16010071b24000c6001030407900c968010b004055440d0b101240607080c00b00c10241803199009004400b441c1d0a502c040080c107805000c6c015050852404a0800c0a951720071411580000c000f4028102d1f00801d00d82d00d82404103000450074010304c3c28030000001e102020b940544098000850250003000910080c1c007000d90354401401041d910900310f000580750400d1000e900200280042c0940d0311884c8040f040071240b4401c85501d40c1d50304030401d0b080e2821104012610240810400c441440715002070708035000c03200102c8145d0403c0c6003c04207100150202d6201d40118040c88482c80d906510709402070203030b82c0b5210108400755070703680c07407482103445071300101090000809052146000c403030b900d00050701226181004204090b0094 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 70799705 1250 70798455 70798459
    0x307080a15030b1f08010b060415030b040606090305060702120904090204060315020a0f09080d0518090c18060309070509100803130501030e0a0b042306190b0616030806 74
    0x4402002007509081564440c046041c0800c3c001300e00d40401914801255003d0b05080c0c1c18822402030594a48040c0d9007680e007447c015001088002c0022409421030500b0700703811510b0440c010454651007014182600e0041c4129802d0b80c03181501243d0701c00300c40382d07009105401801035082c0e529090300640c1c01d260005102040103a02d0b512582c005280211512001070350020360300c2907160f009040ca2404840354100305494516000c80c941d10340c0300c2d0032030702030401a00080d4501201e1485031108480103024241c07000610340000020559400030301c10040b50600b10b506451507203003140449200d44881d0024000503841c200034010f032000054050000619601701c0822120803c1001c2c2c00008101d00350300700c0e4a0300d4a0005801c984c20000c108003075402070303001d440104044020840e00700750310200f400c16643c1003a10071640182c146840500368054007090001c40d2007060141b0b04406174802041003a0400001001440c0c8100b1102101c0342148100c940c010900802c0c010390701c0100 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 70800955 1250 70799705 70799741
    0x103050c07020a09020c06091506041104090935040510020a05100207200d0b0903040518010e06060c07090b040207020a080f070603020a1d03010e060c0a0e060307080a 73
    0x24960003d0210110764220f02000c44c3c2c007007075022911800300f01043e0090103040181c8500443c054a0f8080d00400408440c001ea440d00e03401700c42901010704440c000d002d4620100300781005460482180c00f0072204800030002009422000c50004c4841e4509070100501607501d064946410b0041042c50800198194090350b4600710111300c06024403e00e10004a00c016500c41c0903103090080e000d0048841c001d0400aa000350b041da449800c40100b00741e4111080c01ea040d030701c51020034550302c541e801064005000b80340e000d42c41c045034401a1f06a407009a54110150350708810300540380500111510f10b580018420010550194080166090301820240c034001154001c100511b901f9800b1400d640d2090b418210700010512051002d02140d10b001e5140102c0214001c040d8081d401035140032580309000d007504c603902540170703100e00c880ca1401d603080b62401c5503120740290001000800852902007540f113036440c112048071301c01c80f00c9407100380d43c3d500c4251511001302030030040034001c408 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 70802205 1250 70800955 70800967
    0x20010605130f140712060e01051804050a05240112020307030206070302160b0901020c0910091e0908030105121906021c050406050105010e0a05150c1c090501110a030207050103050c 79
    0x301c40e188142c810515502c0b4040c20300e900710450b2040750032071f80c84450071800e40d000600499903082da0074411028800364a030031079140c0d400e05604002d0f82030030040151080c1600601c2100c40380318444a009110a148101a1f0760340c055160b181e011100020b40c59003200000740010f00e400800b07450024064130440d51945d0011240e40c1403003019800c40d4141c250040303403d80d0250781c100500c4a0301c02c4181c4120b4aa4200803810f48503070517540c062821056100d200888413255001e610140e5000c018001f402804000d0800048940c02030048500070b000a03402c010710350500042c00090030980c020300e41c44448081d11400025000020700c0302600448103504801101e075401042d008a00685001030b40303526040c0050480c129810034140290020202000266500b260f00c2400d1040028990b65500349500c10380d0402e051401c1c20071000d0306841e005025541c1c0081004107403203007170321008002a1400b00c1c07182e8514400c6001001a408290705000e294825004603030826101a60310303003000c1e = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 70803455 1250 70802205 70802231
    0x7051b010c030b10020d080615071e02100c03090e10030203010e07090b010c0203030702060f09060409060515030c0a030c0201150603020706050f010305150405070905040320010605130f 81
    0x40035596001c1c00242c071040c01c0300e424900801d81e4440402140020a6401006140075040c604020905071142c015404038070441c40080f01294a01607110280b2418a0b2070500860030740700c48001d00f607020700745040180003400d01440c1c0008056030141c448006403484e000b4880305280d40140507001c00d050010000006031400d00400340e41c4a82c1038041d0805506140b20001180c2102c80d03c5810010620001000360710044121401d090701a02c80c282d94200c0b484907010107114403c04246c01c20300024000491000d503138010340070798a040781d03480319440305195030310121b0005a50054440004100b90440f05000c0d50201682e04030030300011400c01c1d0072404008107118103501c4600031a80000d640000c00205208040d030168094040d1805541107841d030a55611225100080844000c800f142c140182000b2010003001041d00030b029514041c90b009010000b00f4000751280c5080031410f20801c5018080c1d5002e80c0c4001c1d10300d244d012803000100029020300c000c008002961001014001 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 70804705 1250 70803455 70803461
    0x1021608010203041103031806090d022e020d0e091003061104080f030c03120a020d0c050c06060d21030f05090304030c0e0402010206061302190f02010e01090203030307051b01 77
    0x180300c0c030000142c07649468149210100784024000d03201e40c0080060204204240c14a07014000096401c140c69180724800b14071b21450322900a948008084944c0c082600344401740440c01a04014003c5104590703001a0f0b1741342074400e0110007141580c2202c044d24203000d5083c681c000c07c3d5508203036400d6a25160324044a52102100725080c40c0000c0c1400b00708410028002810280301c010352803d166140f01d40d48a00449142c1d20311030080070301040401207550141c40ca0840c4540c07040001d05e00151014100e03a200c0f01d0000c410303018510007d901440d04c0303c0c0d0740c40303420b800250704400210310f8000c0705040f0003046182028160780d2114416099813520400d4407030305110b0b0066980f9800d606104d1481e035010750010403140651010800140d03808240c00381c00002c1928118410800141c0e0031000e4042c80d101c0c06110f2030f8550321509450791140070746840100d43d03002080640c407038130315141c04e0fa43c81c9200650076600400114100521450051141040062440080d0040c8805150035 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 70805955 1250 70804705 70804709
    0x9020301030b040b19050c03011401080c031503030d0f151e0e070315150801081609110705010513060509010204030f0f0201110f06241c0212010c0c0605090624010216 73
    0x4506402300040c00b6041140604950001c07090074402502e01e081c0d40c07045401e10000b010281d4410061700d130022903803010802d562031488802410302c02d24400c1d607289002803c130b0b9030640e00719601031400083e010b03081d41c214030841404540800c840508242c5401824100506000101540d440032040032014401005003e400d4240305d0844650030011300400000c4180c2001c403a94114015184408011210b480101c552004000c10f6442c40f018100c103140c0543c007006889942440d00f0450740e000c082e101d1008103407080004115580700c6031000703400c070700450000500489030090700034003081414611181c05803051410540c003a0a8400c80da013410340c5885440010f90011040c02400d201803c5621180300314013140d036150303d12550006007201e103d0010368110319003014458055466102c038007518007408000a2000d642c0119001300000c404800540f110761803c1c0c0490000c1001080e02401202851651440203100c00d8174840e07020440c100712415071182c0c50b0180d509000368504400 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 70807205 1250 70805955 70805971
    0x309060f030f1f0e090c0607060b030616050409050606040302030a03090305010f051012140102040b07060623060c03070215030a0b040b0307060507150f02040f09020301030b040b1905 80
    0x207242d062542c100301004501a050002031118a1070500d200d0240c11074600450306402150000c41d101e0b22849814918001d0f03240750410300005090051007040d401c40280c01a054089034001d0381d5803041c06d100c50000314199400680204402c012181d200c0d0401034100d00000e04540c07405139070f580080e01d802c1c00d44908030040b90148608005021081c80341d0160950340020a20032490302c40f0004861150700e016941c1c00300030401d1201c2c03d002205540034400c81195008540c0c0d540c035001480d4640e0441d400860b60303c1d0400c40d0214902c06840c5c01c0304044002940c111141004c1102002000d4000c080f24090342c1c4000d20403d80960365040800c1e0140103100621356903070429001007030548250b4050b2a00490a0000300c241c2d944000940a04642c010b141c09a16a0014582501f030007410503604101d59003803003801076110308158014001c8500103040031420554581030744042c0d0009200161940f04041d00240200d000c00030207a900c0720f40c0540d080c0c07c1586010442c0304442050b10162 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 70808455 1250 70807205 70807207
    0x302091e03071a07030c08270a050d0b18161503050915060405060301150b030f07020d08010b0d06030506070c1101090317090301060f0806040627060507020309060f 72
    0x41440e0609220344000303400404020003c100d2021014501031140010040401020744909811712148201740d5403c54880381c0000c011913a85451004685845500c81e88101500c500c0007929140c030248080c10a84d0014003141d0b69500d00f050034041c84d8081c42203201c18001c282503103501110805d05400908400b489600244944d603d0040490b0401400c1d04000c0d0300c8105552101046048855130051044401280da56101d40101c0d025180c1484100034074084004042051001c4030081d52145411281d10b110950380c0d00c9089a07201c2c2550010b0700414070320001407007a0a02280188030311740311b0200100d04180c3d80e6a0b424649a41119000b0000354200710650400c07900000d0100071182c00d2030419403a5041d61120000742c40340b06031201e44480e0004150b88143c80039040b01004100795000304103900c0c0d81d10880e584440e4115000c903034041c40d00345441c4000c5031104004108002b8844410301050150741c0c0c030b000512000c0d203d8001d46c0305c10304c9501ca0f9662500300811300c8016000a807 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 70809705 1250 70808455 70808509
    0xf050d0206090705040204030f1b050402070c0e09030304120503090307150b0f04201315120507080f0601080712050c04050a08030304020d021504050603040f120f120c030209 76
    0x564209180c0b500321170711542c010801000890f111100072040c0c59000030007401000c102d80208039202c64140c2c0150b4200f40049100c50074000d0640e14501280c400200c003402d80c0d078030910b04075182d10084500a00c50b15420005915561103400a10b901c08002c0088a2924809440c3d100010820f18820340b040c2d46c94041042146c240141d45041043c0160390a200640c1100b15000f80c028180c6d41e419000c1070082400d00c0c00c8040861120010075995110164038600084000e000300c240c85e0410303003e1828480424051486061040d2040001801d0140d00b0340b611001102c64001c00b408010030031911004071602100c1c24450180680b5001d00d101e6034981c60082485000c01d0780750b0000f046070f0424000c00c400760322800f0000c50101c0e81141d04458195101c070070071496000e03d800982d041040441004100559a0a62450503002d030518070000c03071007040100c991010300b0712a100026440e01034031a550503180c118103000d00f05070501600708010800420b1240c4e6040d1200440000d08800c8 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 70810955 1250 70809705 70809721
    0x70606031505010602030405010f140304030225050609120a0b01081c02031602040c1202030708060f120c12010e0307080a200307030f031805070f050102011401120f050d0206 76
    0x4082222500c1c4400d004543c03514401a440340111700c582410702440228285a10384100b810300d032000740e54000691241020304001790340b000b0f000100b1040380300c040d80c98640c9a06580c2140c08031400240041d1400356480144845207070700480401e10703807041e4072a200008080f90003690280508000170600520242180040c0b50300d03142501003950010007040c0500c6050340c151464503501a98041004404c90740700312070382031130048015042c901c08405e00a285038014205030240808448500b4440d4503041000b801090558100c1917a41c09200100b801b800d00003041c0d203506424000002d40d1307035003580300c007800d550100500301e800280021706d41443c6034000e60561320052045030014044002e90107025500e205010001c1c0500c5006164842028801e8110051415078403e5841ca20a9140b0304150b0b0f8940c28007482600136124000403e0b1944144a03a10046018000541450346048180f40002d9401c101c203a0720440c100260f100410000c101d26450741d0302d2a8004d0000b8a42508 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 70812205 1250 70810955 70810973
    0x201031e0e0c0a060206060f03030705060a090204061508062202041202040e0601030b0403031a0a09020a0e01031503020d0c0b030c030103050106060c0b07050a12060807031a01030503030c030406020c0307060603 92
    0x241043c499103a52600740095980007030303119480f0b20141d80c3c021003207503140700280c5123014002d002003a5118580412003002c0c00c44d006841414820f03241400101e40310584c400040405000c8103002070301c00340c00a982c511b0541c410000080002036040003e2030015103a4060780e106070445041415200e05001c11402d051203200011a001c10103060076504660350f03c031041401a02c0542015201d02a41c0c150325440c40d0752000c00c9034010545201c2580d5520780801079000ac09050010a0881840c4c1031194000d00400140700e041e0000e0381d10701400d540c00c1103007032114206c0903a1244845407020510089041c0110701030a15007a855880b076255240103400e556903500a1000c0000c504d4901300000e105001c4203401501d142849612120503050488003580b08400c84072405080ca803000071038a0b408590745003501d0290413420703800441c05201180d9007500384001042984208002882d9081c1d040c0515040351140030094a80400c0d030380c40c4d41c51600540c03170a9590a603035000401c20884200 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 70813455 1250 70812205 70812223
    0xd14120a0801080111040605070503090a06080106080a0e0c010c110d030509031027140a06150915060c0503040f03050106062705040c0509090c0a02060709030f06090201031e0e 77
    0x16000b4440300003800c1464009011b24821201406400326031002000800d1085c0d0381640704c0070303040d1003a01c0d5448000a04c112020f00c25000419000d60100c3c2c01070b5100c0c01650b4440d0107a80c0203040340c5030103000464403051052000e850f12051000908010396400e0318181c0d50138003e43d240c90700c0b102140d04040c14503550504500c240c03441d0a054606202c04103d0308540c10600c0524070010071500d08001306004843c6602001b14050000a8010041582d2085801e1204600f40ba0030711511104248204c4c3e10032601c02544070701503c400c205840c829101d40848500ca28162070406a840d4a00801070708140c000302c0340d99445034020301050760300030305004000303007641c0342105100900c100c0e200b805011030246a00440e1501e000003026806681112034411340985044070301e10f081e8409401c190480d03090980180100008102e4062080fa901001d036174009080805900e540d0352004010203101c0c1303049051580f550100c050b5107aa44d00b01d4a02c49400c428003003003803040e043d40541030484030 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 70814705 1250 70813455 70813469
    0x506180f07080c15121801150b040e070504170309011d180714120a0b090103050709150306020714011103010b0d020d09020a0f0608070306060e0d14120a0801 69
    0x1a0004000502d40050010310102d015903858181d0141c010b04551a80300d040900d5101d552a90180401c03607103c544134264142498000b080403c009050003210290b05204a01c2d011005000601192103d25031441c2c0080d0a82045480c181d654000300421500e03d090303541c82504040342414080d600020704800d0503c811405844010603000082c017000c2c0309203401283c4008c204000b0300034038001c0351078131f1075a4441c01c40c070740d1502c08085443c4400201210b54041c09030400710010114180754074458140c80c2c1c8880070349030aa00304420b00780104440b945410101740c1000b00080400c41c40e200405115000b5a03141d9120081500f4035401c1d5400980c01c92034000302000108290906001651440c0034030382000369562a0200c04c85018010841001c2d5002180c5000015110700942c40d0408507000703515a14030607643d0b214142c045445921071000840c01c03071501c001141c80d003840c01c189190301c12200d5010304a500c1710500e1802c0a0175050041110300011112072068005440310300400714 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 70815955 1250 70814705 70814713
    0xf0305010609090b0f1903020a080c150309011107081803061006030b150c06010f0603050702030909061c03120b0d050304121a04030804061a030a03050c03070506180f 73
    0x1400301c1c01081c0005600c82c241c03105607201942c002a64400b40c2c244030b080f5004000481100301e428400035076034480d00c401c921404400e2000218035070302180c5104030001c000d0030701c883c01c10844007040f11030340020a8541135568415491030100c07124400342c21072600402d1296207407842104074207410329030b0100c4148a644414101b14003052100e20300300589d18a460040743c020044004101200c102d1988440c08000104040510301c4c00041c40038125050700c079612700d0141e50348405800300c0e501501c2d2500140c104004600c880d080c1100f10351b0300000086d054680b68039098200c1c4007076007c2c0203000c60004141000d40002c0504038019011034450481d414440c4912950300d0035568481d911801300c000350078030400810300402061001e01c1d1400300140d500c02c0d02d00343c0f0340108514812a82195641d1a20001c1401030000a91154030349101500070100c8110781d4a094646070000741161007503110030406800003070301c00c1c01028002c014002c0e00c1c42410003070316805801e020104203600c80c2640 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 70817205 1250 70815955 70815959
    0x110f06090d122f0409020403081206010c0c090c09050310050106030e0d0801032d0c0f0f0803030a050604020927070305070909020d0b10020c01080c0307050906130806160f030501 78
    0x80b00d840d5450303c0003011031682d088460800458540340515440315810303501c045000800c0c8a078603002068a1103102c0c121201d60f907182e00c0190742500180070003420103008110300b40041d1444d64024680381c0e1b00e90500941150342c0b00002403030503075505428004107032508010090540c05000c2d45451121100c050b02289840c0000184541d10500c80076000440c11512525074500640c100200c2141140344046465003134100400048460b116420f01e00502c501c0c00030303001c900007140b5003c0c3d8001402940c5541c8403800c4104c09844080c15080c0e025500708850308030b41c0c8c0c030300d0400f407221255a0039280f840c885415400c1c491140041c6120300345810942040001980004d9120507100c2c0c003800162240c0307129413804003c10700b00381da19030000c1319400f1003840e00380c00086050b540f11007607942e4105555070440c401418041079840002182081c0171100d02880c080c000380c081404442d01030f0790815030300c8400780c5c5032010695903100b2548248000c0001542d1040c0d07044aa100705040c10b11140d4 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 70818455 1250 70817205 70817231
    0x90807060507180605190302030612030a050705070501021207030807090b180a090207030c0209040302070f06090e1609050f01140d020a1202040e060f1815010f0e0a06110f06090d12 79
    0x6e022044180304244c0d001000491b15a41d5052034808622041c040b00d031214202400038010754010201684c492140b82c0d000a650b620018520b242d62540f108040c1c10007100f43c0d41a12035101c01f904d403e00380310100c0c10109410030084040c01507a120b4280442d2081040001c1c0420801b0310340080c400c0500420212010940020309422621382c1035540e43d40941d42c6003400c9050602035080105041c50001c000640540d001d000c000c10341e104a00e401c034560301c8502c5004100442d0154500206116110400503450021031089801c0b0041c140588800300d18005040b89a1211036407540d003030f5001c6a0100e007150b12251414000000c14411450b1070304000707190b0200d16005000c1031050203003403030600e413039202d402c010949400c080d60001ca5a04220221040040b4425040303400036800c0d108400541d480380f00300e160080c10151459110314280700e403c45280c01003c0301034000340300f019007400074904204034441c81505050050100f86070018070089c082410000700c1c54209017090741000541e = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 70819705 1250 70818455 70818487
    0x170c120403120c05071e050703080d09020a170703080a03061703070b070908060c030a0902040912080a1103061003061e090b09150f0a08010e0c031005010602060109090807060507180605 81
    0x111003410060001c03844649401d601c8e2200a1300004d02c007078000700340102904220340104130014401c46034500e10588a914034401e10f0042090341ca155480a642000410b6960005010024403460702091858482840141907a9290003081007a17000088002c00d001014400c80c0d00080a0700d4102115847d0060b0150740720809400140b5517803002001ca21807281c1940302e070084a0340a44140501d248606210410381391103400440482c1d001000030700682141c1c0306403503541c2c2003210110f08689440341404044908408030800341540c0e01004949083c10084a1011043c255140f13401141451414804d5918025003d4014002c20302031001c01c150201c0800022001962203040000410000400740305595114072955460000c3c180f01ca1400420010b08076003099040b9500c0e010103000340c9088600034850716006030010b10041c054138120b500141c3c1c18900801d07a26060a48a0b26248205e40060310040c0200b0102960b203d510383d0000d0b0030b00300038103403820200e00b0400d108c1c03502014 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 70820955 1250 70819705 70819733
    0xb0c16080a0206041503180503030a05010602010516140c061915050906010c02010c060c020d080906040b0115050c1002030115030e070902070606080703060e070f06170c120403120c0507 81
    0x4054958601710350061083d4801081001202c9450040302040d00b4101d072244e105840c48003034542007000200c0c0b80c038014050a40110700c42c840a11601000c11b400701d03400700000d41001c4c00f1100c00c005440006030b04001b00f600038860341e40398000d4424202c0003582200d2030f00010300e2602003c1d15040000707070f0781e111845600900a00f40b40758560310ba44012141365101401c002c00c0c83d0f01c0c7c0805409001d0303000540b1500b04003641c07903091813625107528459543c10112002010440042c006000c041c0d80301c810392041c100241401424001c1c0c18598030300300901181902000340d400b00041240c1da40900c0d0300300041c0641e003800c200040070250000d40b81d0199004107078a26400280711410010f090b40480c00614444080e0751060b40c40f8680400941240092025981b050140120704c4440902d81034084070542c5c6c82e0151410240811703034140050041030268501c001b804040600c508140980c0d10403846995181519030f005184c1c0422200340700074420410034140408000100005c0b92000 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 70822205 1250 70820955 70820969
    0xe06030c0c0a0f03030b030c040204050604050f01110102163302030c04120507140901060c06090c0905070e01090906080a23190501050a0207021e04060b0c16080a020604 74
    0x540c4441c10034007185060b008442c01080a000090404241540756008100e504400c60030b0355140c000000400040e13010f075001e12984410300700000c01c035524100904148015041c103050f400050741650040c2213070001c0300050301d01d80360710303600d10100f104031400d80300c0360644c4890140034441c804403107400c44043d5006640c50268000080340040c00240103450003404034551180310702d40d183ca0f1042d154440d9119080b2011254139030407040d4070348603000030b0680340c159481e000718600f00c1d2100e1001c0c1c00c8800342664050400d0102044170308807409070911655032519807164040c1442c00060440c4019403124100500c1c1507001c2c400703814046030807001a40c019444100c4000c00646040b480000403059a80c1c51286402e03a80481060799444a00b030390254000308401c2d500e07100b201c81640b1a40c0c1d402907020b01c0d03066000104c0710300c1c12094602142c01510000b9030356200c00822186510070405103207a03500c07076000c2184040700000840c01503da81e001130044141150b002c030341eaa0003a0300881ca = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 70823455 1250 70822205 70822207
    0xb011a0a0305091606090e0601020a120309030302090d080a08071e08060a0806070c0501110a17091507020f1006060503040f03110d030903080f042303090d140d0e06030c 74
    0xc0141904000c0480301c111403140400c001585c443c2c018080301801d100b44040c2440000000d4017540c004101c0c2e804050b0000c00740002d141c1100000c400034a0000e101300e0926901348483c003440d4440b01000c40d00e4501c1354a015584280d0141c0261034000000d228030100701100c040404009159092884880780c141444802520b41b14009252001741d43c020b140c0c503124007400c00400035031104904001070f0207a0020440b96240100201d41031013241e800c00080b81010a01507080040101401d03480f8514609580c04465010755510707083c0f0003580c0000041c0e20240300600504014403619a00c074144400030005246408000703031083c040100b01402040f0f50491070024540215075000c0f9030001c0c202a1020009144400b40040010700010707000140703501e0005170348501c014259801190800d544000701120b6501c0c001d180d2408c0c4240300c070940010b1054158549480002036510381c0314452585004010340541444e000c001e04041c410009052140742c0c1c2c0ba1900400c40b40c00290b408441 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 70824705 1250 70823455 70823461
    0x16030203070b07020d0206072d0b010506070302030702030601030b1005030105010515030907090608070612020324120106091a06031302010e040902030307030305010e0108072607050d0501090b011a0a0305 89
    0x1840c5e060101001942040000440c142001540011502c0d0962440d40001401704940c401001c440e1010700024002464100140840d24208000d444218030900c1202d2034800c00340e0220741414000e034011241040104203200c4110f502440140241c68103030001c102c5513141000081d021200642d0f040283c440c0080401c030030120034060f80d0041c06030348030144030a80d44d6074001c81c0d03034000c2442400b00040080440d070a5121003402103d005d649800c11f100d1240320044a9164140480d001103503015141c09100341d1164020301035400140b1102c600002c207030407078120340303640d00d040c07401d417148124070810400502035540988a24026020718045220f01c1861010400810080502130350611010941c08201640f6800c1241070f02c2100003440310690ba40e50000b036881840d809110003092502c400322045140d01c006000b03000d43d900c000c903642165a10042503c0d03038846d131f0742610965101c0000100348602d031540c150040500606081d075500c00d1070000c2c1d20b00c1c050001440c04264545000c = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 70825955 1250 70824705 70824709
    0x403020f06070c030302030903150915090304090f06180e0a290f040201091a041e050909030403110a0b1c1e020d110304030801030318090204060302070516030203070b0702 75
    0x10b9804490340502c55007121600c030306003c1e60320b4008601c1c4074428810210845010108496258050040c2c17500610200f0329409079188038100c02045c10915100c01c0c4000071b034640c03032030007681c503000a9214001041070611300d898a41d500402c00c4120350b00d0078108060a51200000d003211400c1d00319007580c240d141e0803903200c008401c00050050040301e07880309102c1450207400040740614802d8803001c101c0c0da070307400ba100c0c0004a80c00c40e40b44004001d000401c2419480c010762141146000ca12010311601c5100140c5904000c6c1c4180102c0e520208041c410840e040300a105181d60031107a203d600d624001500341180702e04070f400c82c24200c410420049411350341e045145007070a0840070101c7c18a68001d880003c9d00040f03001e0080c241810381da01c0705900c0a0301160301882c5c040c1c4d80d50005030700716102501c44884454005450929211002405182600c003400180000b0707030300503035118481d003085803600081e2050000030280244003000143d4000031f905c070807504c0411101e0713150411400 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 70827205 1250 70825955 70825957
    0xc0703020703290a050f0106050a02030903070e0f0f06060f0d02090a030303051902040503031b1603080703092c060d0b0411011412010905180f06010503060106140403020f06 76
    0xc40101204220f080c20741c002c00000d100c40000008603940b20b4210b42e51600c4407010344400b41c5848858203412001400000d116900030403040146004892030410998042441d010541d130002450700c00300783c2800309005a0b20645500401c0132a414600c50074a980095508d00c140021180d100c03a002405004000b281c0d01640d88080000303210344182503807802e0140c0030f8401141c1d04020b508401110b4100b08038180300f914203441000d002141000407008000c0b60f9015900401e2007944200b0451b1040a02c054000f180554440c9091a0f02ca81151a0140140220b9045403a03070780c107c1c4554200c01403804c008048002480c0d50000c5c6d65803030700d1004c00c0c2907a1103010302500500740c000400041c8046013102c0d40d031840081e0703070b000002c14541e410300c1030394001c15400c0708104402c42d0040008c202c094025a030043d24180e100c8016954150040d403070001c0c2c00764542c4054200d600100300501e0180600e07401001107007044601c0c00b04003030710f5800300d2089020080c801c00d59441c5180480c0c40d414 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 70828455 1250 70827205 70827209
    0x30c050d031a03030406140d090506070e0f01030c05031f0f0b04030c050303040617150d05061008030306010212130510080a0f0902060301090902030c19050a05030a08030c07030207 79
    0x60588288403541040100a0700c00b000d0090b205290607503070300d41c1c03e080001c219402c0b40d581d541c58551280c410f03250724086501800c5c0250250303032107944d4417011410600015009042c00c0d1610007403038051a043c00700c100020a15241814a000072446482e608003040303a9000c40c0c1108448044100c54007032405520307240d04030301c4852005e510003060211651008100380d0303000c2d91240c015240da80b01056600c0c400e6004007800039101c400030320b0901401801071508510340351001d000002c00c4c03c01240346078880000680300e681c083c8043c0700107042c2c0d01c0c00c0b610181010b94013442c910b2030185c002030741d64458100d20380038001001440e220358540040d1102c0151100414000c00c1a03800f08008102100c01c3d6030f204061860b001c00c80d0703030300c40c400d10a46182d10760140c901380c1140e181902e00c800038070f8090000e80c1c041c010040b01c0305066850054405030300420202505002d801c180a00440014036008035003c2c0d809070509901180c100000d0300d074801d141da424aa5150b146107001c904000d0b640e = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 70829705 1250 70828455 70828463
    0xa0c0e0d141c0305010f080706110f0111040302180c0f070c0b04030f030212040807181401090606020d020a1a0c0408010507051207170c0310030b091011120112030c 72
    0x3200600c0c00c001e10b030241c03454560000e56002d010301d9896a030344007039241451203600841d5200e40410441c070b0b4010250b0101c003030440c405031403841c100304c031074a82511403150444010940026081c01185850003442503170341c1c0030524006040c6010740d001c103070310b00c64604048041d01010030100d08010990005001414062413400c1e1125940d00d0610100c968400c0e084015004101e115040c03130501d141500c0c1103404900041c61450700c1c2c0041c104020400540301e03040302d0703240c0c451035400512220030b80d030080c40340402c00100d45143c005c0007410300c4400302c00c1d002107400c40c90742c003404280620008006000c440120200503200c00e864808540300d29400104c0f594200010000b01580120280140503925403001c206940e8810701200d4007900700704108002c030004804261584141c00103107502400c2c0b0101400300c42d849803107242c031040049a0b964034642c080c0c1c40b10721000001c0c0c0501310042c030ba02c041c41401d15034061542e1303240303402c14041c1e4400044030420303280a051042d05188001500 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 70830955 1250 70829705 70829713
    0x20f030f030706090c050d050c0915091003060b040b060f0a091203080a050f0702030d1a06120103021e060a030b0f060a0f08060a30050d0503010e0a0c0e0d14 69
    0x641ca8040d000d0481c4c90403e8403c9844c4143c0000c042c182500701c41185030388400034105040080c0100880d244c00940301901c0750041d12810f000c1a00c41e45161800f880f413444000400c0c500d5860450b00340d81c6881c0e6040e000e14201101341d80a40c03a113000b40e85030aa0f00086440e22038030590300072241184250710811620307601c0d20170002819001610079000c0c2e104000203024603500c0481c1201440d00544413280164010041540c80c0c03481a444094058a0115480100004080000c01d01d80020301c2801c00c640d01a00108110b14002460840c2600b100b01100f5015180c01c0004982d400390100400034580c803640c60300829502d0f0000311903400e030020b00700d030344070704044800400e0300c0e20b800c0382c502c0400e000301c0200e500d0303240c8813040c40c089031b16040d10300184a80e881024940345103c03000911014290105000c00076105102000c0d80340c0315a43c410341c80350301d1b120f144000004080d14204c0c031f003403400c8580d0795420350140e6504401d00c0182c540c14801c020a16210340c0d4403008a112102a0103 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 70832205 1250 70830955 70830967
    0xf0c010f0c17070201110a050702030c06030a1a03161206090204060e04060b04090203030a030e0a02090108030319060305150c0702040515011823060d022d030f04020f030f03 76
    0x40c006601020700d910b21051180d00c0d0340c600c0401d13170880750800303e80b0104903824070800042d18494402840800d2025041c1c2c0d215404480100f1803a03001513620071030154039006902c144c20034900384d2020750401100105215100340b6287d0308003803182e000e41c10800989800c10030030700c0101c3d000140c2c081c1d03010300300b0002503070b030b03541d80c1c01c042c01d42680c044540904282c1c0d070019625040c041c0c030a2503500140903502d420300c00f4806400408640c0020405400b071752007860b000d81d4586451034000c00c903120203190f5038900300d2850307420501440c0520790700c1807400d0024004100002010500c0d00d07090300000c04151101107420442c0d02410304c00035840740c2444100210480d46031888645040280c0300c108084880360b00b45800740e1003900410350340c23031440c04a09155100751800e08442a0300900300c5031074200600111b009a0b48188940c090110450306000c01c6c3e0f4030b5400d000155201e600a905d429400e08403100c1e001c4940141c0080e100701c441c0f0035100d605641c2889903002d80d030342d8141120380d81e030 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 70833455 1250 70832205 70832207
    0x7060606120203061806010207050d050c0108010b03010305060406021c151505090904020607020d0b040501091203020a080703050702011104080615030f03160302070306060608060405070905060f0c010f0c 89
    0x40014016440028024001c101d0540a14001e61340919401003440c1c1300100200c00c03e40352030748024203550440c070440c5800186a02c0f1003245d90319050117a00034000c594044000074001c520107178011000402c0400c010008200081031894002e5400078001da5107500422010403d003054003a04d01409203420301d200e10815403d14480120f030403600c050800c8510092040d5130324043c0c038510301c4d0400d500d03400003401440c2990041c51010310062818181c161242c0301e81c1c2e80c1c44000c850480e0380340c2d5206070030b8041c0b0481241e00c400c074040f580340c29403a1103a50f80c0010090710016103d0414141c0380d102107075045000390004042d621105150546239952000500d650301d0701901c04000500503038900400d01e00b0041404070001082400441c86c0c05202003041904014415007070301140501e2002000040746030140100a21407541d5004080c14040100320454501078033b120180900400b0400181e1103240c01d0f26005820903903401c0e00d4002440845001d00003000f400708040d40740c041041509 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 70834705 1250 70833455 70833461
    0x7020607020105090105100509040602160f03020601120c0e06030f0d090906170a0308070c08030f0106030f0b0306130c0e01240203040602031204050102160308060f0f0d260706 77
    0x14000300c0d802806076440b8010041c3c202c64045d214184070b00c22400d800c5c0454107010038440d4000b4400c01c801031a11910550b2000724240103402142d0444d1880002c0c1c003407581c10003a0714058541c40303e41081000480c1c0c0d805003400d6040c861860082c2c85500003c0c007a540c14030820007071000d018107845c40c29081250003051200c0b180600e0304010300c1c004001c0340302c114203141e1076a41c92039807000300500801c5031819603121f000204690308000e00710b40c224001400b07200203540a092440003407501c03075051203009000d503002310460b00615440c0c00110802070340c0000e000e642001456201c5001c0d05580e091181d142003464200d5039400c10a40300014440e44000c0088280190314401c4200394000c10504a0710b0b84030380d1003103600590091000040700ca4490a100d90010700c98000146440d110450034680c410210009401080302101001211704000900244400b411900350010f00703803880c005a0b02c01a8030001402d0341d0040390010342c0c00110100d44e90041d091460905840f03020b1031a01d10b002d = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 70835955 1250 70834705 70834711
    0xf05010e060c19140a03050603030c0106030503130902070b010e0a0e06040b0f10080c13020c160302010e040c140a030b0d08040f060504121b0f030602040306140c250209070206 77
    0x400140703c2d8103106020310844620f507000000e510898076041d00010100c01905001d841070707605000421100700e14400034850071008512a001070350711203083c03000000000c00d140d030080009500400c211000584c01e503d001d410b444000208001d030751075417180180205520712140599109140c10b1100f800091100070f17108008520541c101c6940d800f03140310100d042407040c02c010f0f030b008102c910064a410181e04941c003007500801410044880c0d0713403a140c81000c03280102c00e581d1a802c00d10565a01c2030441070007003016a0140a00700303503840300030100c8800c112003251951000c108441c0c5c0318401e0b0072100c03200c18002c01c1105c458015081c10030321030340700780706890309003282c208005135441c001c10503a81282d2280321100500d001946504a000c03040b0003504103001031000021841c8862542244060344c055480140c85a00354a40103084038089151921400035080402400007200001ca9004c0d42800e43c800700d00e03248003200001d01610407240298080c00c0349007006185a800600307944 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 70837205 1250 70835955 70835977
    0x102090312070210030e030913020a02010e031305091503070602030a0216060c08090a0e0c0c0f070f06180302040f0912090308030a021e0c03090a0602010501050901030f05010e060c 79
    0x184510704101407180303882030010094000924400c06010300d402507210000100107041980c0c68058140001500f03034542108040c005580851003080142d0b091044403850100c0600447c03404410b5050a05814013901c2104d10072504000041c01e06100305a0340c1e00005c0f000303003c5030383d030b203446210103500e9410800c114001031203001400e60075410180340070310440d541d549414101040c9900d43c051164010407001d60010344011000460280304640740e42f0801f600c82d8010b8555040303c8600e4200b00507001200c260780d002540501c080403035842c540041702c0042c2041c0211070140290580100031590000e50320516041c1500c00002c0c40d6040084102e01c10340682210141c03031101910315560500010f401d89405100044818520f54010200c01c050f0f982160344030b1400003840c030b006034403a003607045a5402c013080343c01540c00c2c0b103034030360f0f01804560009104035030500300410f021810511020f4080c55000104800380b010a6005808805842d419070b001c1e440e051048205aa11142c522700c = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 70838455 1250 70837205 70837213
    0x50f04200a1d011a040e010506090402120106020d0f020610090e0f010c020a021305040c140d051e0114070203070816080d0510290705240a050a06180504030e06070501020903 76
    0x130f0b4850032480446040e502c141740d40e05410703400c00040c003450740c104081041d0441d034204a540030500d6000c0b00341d8002c200d02d43c010207110b5582040104000040a00d40c425580828180030581c200800080151246568001340520322201e001c1c0c41c100000740b102025500c2c2001842c440343e40403c80095082c0295106180030b1140035005084510842d8054040701d01800148865000050382c105600002030002016501a46840d4281045885003008031002582031052044003030090a40c6a8420040d91015203000f0700d02949a01c9400d1004042c440001409a698018120f400d40d0460f0044106a00c480002c0307086802828141c0394424130a906800001d004004081000092100f500701680c150301c43c90341c902901c3e00726000488542c000d5001c1032180402c00305520344007442c0024115000d08245125104a0301c01401d81c21099040c240e041c0403012005e503503c500d0130601ea500054980d52424115031144010000d00e074801c0002417030005101054010f4103840008809a13 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 70839705 1250 70838455 70838489
    0x601050427060204050f0f09060108071110050105031002070b16050f040801020307120e0d080a0902060a020d0315060e06070c050405190b0409031e0302070501050f0a050f04200a1d01 80
    0x800347c40d0204001d10f40c80020000060a01d503c24a5800d4001840b400e01c9499020140d10880c142030041d0030301184569900010005490300708032181380f088030300008515221440e150803a003480001e1042c19420ba401e80c0c02d0440d213100d00110350201600015250b01c458642c2d8050b4082e500a03a040000180d0664000c008140113214404903055103100504600e201c0100907102074000404114280341e46007900c0016894a40040801c12182ea000d01000c3c058450080c0c100c0710304001d042040d03111200c05122494001c40301040c5c4050840f4100e4840e01d8502d4211a0802c0d41d4000b150007070b04000610450b104c59101035400c880c19003c00740006110b0790f0900c030860314102030140c0000e101e0450390188aa0482c0166030b40001c0346005480c007501d50b15107600352103003540c461308080c03003c80400c0314102d00c0b0710880d60056200740300d03010281030584404c01480c180442c40c1d4810700440701e0490310f44d41c030324040710004e02c505140f05000c080e000d00448490300c070034417621040b0300c038590b88 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 70840955 1250 70839705 70839709
    0xd02010c052d03090706080915060103020c03160c06110114011a040807030813052d0a030f12080907120816020d111002030901020601050427060204050f 67
    0x9800c2a1180300e586841c00d152039141e000300c1c1c0da118090404030389500701c00321040c01040380c0c008502c00c200540050920b03d1070540001c00c14000201008e0040e040002c800030300507200c9071100d4009100340303805030700c5a000045181c1188a03410f81d110140d45c07500e81e01c50403c200340340d0f6001100d0300d54564246009107500090300f601c950b840c0021301849031400500109449268203c03500d81182e0384181819211a40c0314901001c2d0b8000f13941044010410418052403000c0d200d019040c180c400309240c06041c80151010380d034903817015105503a010551032030b0780c0314016084015a08406810105105418074100b402c0000e0540000070300e2000024414101c00034a5004542c81d5280d480810b10769602d407070074544c101e41c440e0b403500141040090050703034403c000c00000070b00611304501c83c07140e800c0c10011404201e07a94441590800d01c40e100302a1b802048050448400351400300d2001b00414484195410312000d44c00c1d0484041113080500506a000d80145c0da0150b82c00080c00c452101 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 70842205 1250 70840955 70840961
    0x31501080d050a27180603170708071104020f0f070b07020a0c12080d020a030b090f150603091011120705040e04061a1c0501060e090705120c03070303030605030d0201 73
    0xc3d440081883c3c0501c0ea800000e0840d9009240811003085071520354a40c1c03200710488803000250781030240c9a41043c0188a0f8201c680b20701c01c0501002c09150034483c0d07440704900d02860401900340c030100425801d442d100e940491300d180c2c0178034420360754646e44148184010380003a43c0c29038280e04528009841c0500008040911541002084041519010b81e0328101d8003e24011500d0380011300c480b036012529070000d009206a0380d100440d0005000c0c0c00d00810a1005002c1c0900c3d810003402e1055841c140300f00d000070786100790386003aa01d54a5410580c03a000c0050f03110100149007490b14001102100054010310300b51140f160b1a5480e140300c02c4540e40210b00641d12040c2c00100403800090f5a54010380f030000314142c01d00e0b02c00c2d096000042c485190000d4021080d41b10703a000d0000c0200a2103000302030100030340811094140400616034650441c01756500074a400f51500684000800000c0b400210040c101c030307040c544030300d0010064051446940c2c064821241000d0032540180 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 70843455 1250 70842205 70842217
    0x60f080601150c050d0c0b09061b070c0e15090703020717030402040e07061809020c03070201110703060509011b030209031b010e030106150e0102030a0813060209031501080d05 77
    0x1001400140d0900c441c900b1814076254241c424801c0454075800041c00610500082607030300d0700e41940d000b00c0e5080030f0040c140003d00c8600a5004001080314640b80c80e0708101385250700034000c0b61501d1292500c5030b84c0c030a454020568000e4050100940d4020a0340300306200b2800341c4031001c90741c454030000c4e01a4090302c04020024980d4110f40e400c480c1071500910740c041e0000b840410228010300c5200e0518000e5044500000c9885c0d0491388520211001900180032000045150001010044e603c0c0e01034440b0080c1041640c0321040440e880c104415000786421560800c0181403000c82c1c01e0007401802c0c600c03940c80a80e8040e102c0100c0c007074420750340c00f5000580a0314044140c0002c03101c0c4140009d00c0b4070b05010b569175a10846840034410b0002412200e1000b0704040480c070005031111080c01c1d02a81107610400115030b145a10004083d0000f040c0c940481080ca0700d0f2030103032b000e40604c840881d0944102105c02c240f444955205174120340d09401039a00c02d0030815002c031002d20500f = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 70844705 1250 70843455 70843469
    0x30c0206090312360c0d03050409020703110d1106010e06090f041e0b060306250810031205190801081506030a0b01060801060f020105010608061c1202030d060f 70
    0x502020700d407a650545503540c00110589034801003240000d660307080508407074001c54090007201d01303181c4d014000c0105a40300c11003120b00d0041001e42e9034000b0658421070180030080b40d0086002d00805000307541030031441d108402a00c1d415400b9000c001c01c1807181d03d01050542c45a140001b5a110407010060300550010380703080700654034102418a040d40281c0215420003450f01c07100107046042c1d4510402034400c030034a640d60300340101054903004000e8507108920000e464800d2074211403410104140c00300e400d050035503075a007014a81003466143d00240c400b03c4044240100c0030341c0040106580da100b68480b80002d9842e680890301d00d42d00740941f811950041d50301190100020011950000c001000c84542003041d503100504540e00380c0c0002e000c81c070003100500c0b005800000a41443c461840204465850110010501c1c00d0103055580901c0303d0307060101d0b900a124189001c9907800401a4a111007490002543e80e44a5040301c9002441c0040118440340c003c0c100b0310485240d = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 70845955 1250 70844705 70844707
    0xc0d0519030903110610050a0e0702060f09010b0303070c0e07090501140f04032a080303100909030203070609151a03030405010e0112051e0c16080d020c07080706030c02060903 77
    0x2440e095004080d812016818400381039201180c4407020001c8a11507605d010902c0030381071038072040c001d5612190b005450000c00000408c03d8060b800204141d1248603e000c5001a8403504199401006110616601030100007079100601c041441080c00311100070510000b66669100d041f03451320081c1c010b6a0002d40400340800100d90344070050040718007240984e9103030030b40e2681e40e154401340925000c2c0c07128200d88042004418070f80800802440f204c000b551552801d030212012886090040c01d180f10b0362501d0340e00915108105880d032407944864100507919050400c10071482983e08241ca40d541850f002100004a6410b075400704040034008500309401e18005452400c40c80c50128108208840403040d000c005004050145405506d0466a6007100b00071407501c0030010b080100303044c01004000c5010340d001200030319140e00034200c142c9440301c02c1d42a00113480340c2004103039a441401c4003c102e00b50b0100d505400c13a851602d040003020b074000b200340d8482200f29012401508 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 70847205 1250 70845955 70845997
    0x9060f060d060e01030609020405090a08070206030a0f05090705400e0703150b04060806040b0601030f2c0607080c090114030103061a0901210606050909030c0d05 71
    0x101500980000d400c40304010680e1525602c681a83c0002603200340c48940d140c80d8090107508040c1302c0e190f0024422000792118429a454180503445815002030048100000003000c140740e0713510044560440d1402482a07050041d14070f0380d24503080c05540d2050f5149850680400911901c190400d00c0440c152070041c0501c1c0b65080481218110120000343c560032000213818003840701c040514414210011000200381c03c1c04101c4150002860150b8900402400442c0000032256441588002030203002c0d510781004802818160404000381070400e0541e080c00c5d480d254402440103d200d035078800c220110405281d4912007a1903e07004102a40301240c05444224001c000e001818100400403421024140d600c0f81d009030b01c00d40741c0c0c503516200c3c00d00520031001c01c8551401d044951901070750420740003c28184406280103030710018540000e080140c2078124200516005101010a1900c1d028241d203170350003040b03283d901780103030040c01400718041d209580064406c00c11a8800390 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 70848455 1250 70847205 70847209
    0x30c01020f101505030a050a06060503010510290f0915030606041e08060a02220302010f2105070e01170f010302010c0302031e04090e0f0c0402070f150c0e09060f 71
    0x14031150b9185244152100844c843d1001c03c40c0e07006051281004282482c1e0398100b00c0111451500700c039100345d0400d0140081390f402d00e80300406a503082c9405142003003588644011082200f14003140c1014049000420000080043c01c4507403025200c0c041c0c0c130b8140d00600215803208554050307212400340024000c45c0000580054403069888070343c079a00761644240351403c0300032120b0b803040c0354000861100c10f003940301802d005c581c5003004e841070741d6081d030b4006040c100e50002803000300180016607440340c403180c00c60081a001340840820550501307040081c001190090020b000c00c1e01940e045007110785e4800ea662103000e0701c0c94101c40c141d00750f60045402000c98070041d0210710051010014140791b69410400809014181554440c0740a45000c1907400c60081d00141e5003203881c3c00001113601240e0309110900c2101c0c0141c1e11140352800c0d50801071003800107001d03032105880240e0020240e0340642c02d40c080390b89a9049500c6004200b00107880c0032103001d40c20001144090ba114 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 70849705 1250 70848455 70848461
    0x4060f12020a0b070803100b0c071707030c1203030c0c0b0408071a0901060608010504140610030e0303070203030a0f0507020d080a020405030a150501090501050a0b0a02030702040911030c01020f10 86
    0x16a100505070011240d65400f24040c5400101c030586503880b00000f032000c2c6500032101c42e001031000c0a440b5050080541a44e502d1380810f100345040e014150740c0484224005002100145600124031441c05484000380070b481c000d07426003140031034a0b125050603c14002d0000c14005a4071200700c00490b40d60780d8130040d00e5086510101d40a42c1003004587c0ba40d5088040d161107040218000103226240001c010902d60b0103030700203030140780341c51004c41d01e200d10035400ca540524162102c01980901c0c49040b4020041550301d120304e40004001e020308030798080300450080c0304501041c0025041c1c0d07000b000c102c410a80c0c0703807000340c2c0c0206085030030b9a0148400a40c014a1a10014141669100480d00f070070411042103441c200c0c1c80303844100c92080e5104030782c050b201c6402e04214079810f1030007060580c800381c00b41d44840800810328481300c0d0302c01c208540c0d003240c0c05030040c03110042070f182100b4094820b40445210780100c2d140200c1c29440083d0082e40c80019000810010519010b25001 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 70850955 1250 70849705 70849739
    0x60b0d02030f06150a0c080702041d061f060e060409061502060c09060306040c090312030c02061006020a14030c07062607050919030506040302030c0607090b03010608071107140a0504060f 82
    0x7042c01030144e000075076203510500408407801210b00c07140e0bc2110404504103070f0014054000c840d0310b00e480c00c050000819503207043d030703c090800c103101d82030180c0080d0740c502840d4040715045040060120f044010f4407121f1816450710f07000ca030656201d40c006000c01d40501c03007919401002c1070001803160f03e81500491000c0728503040400320640c403070b00ca290400c0165200706003c2a01c42c52034020441d0704100c5c490340700003c4064201158103140c03009440383c400060103401039080743c419184505051003140c40c2a842d2030b00316407286507540005896401d00341807030803150800d40b0a0030b520021080386c1510614156030b03001d14000980c41000b0201003041e03103803014182216804000900200241d90299004c0d40003141c0368011030000354a81880180395404100d1111010030210000783e041d00e0645071039042c40b020783d5880400c03ca0f0300d414511410200341c414141c0000c2d0404450101c15170005049d40e0300d2250b1030b251002d10080d951a8030603010107014201081101c0404c10540b111 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 70852205 1250 70850955 70850963
    0x30506010e04110a021e060c03040212030a0201090c060507030f0305070203070206040e041103030f0703120212040c0302040e030c0a02150c12040914040b0a05040204060b0d02030f06150a0c 83
    0x140040d1003002182c211450f5040c00c0d014071100050700245180c040000d40c016001c0044c01e28440c03078004040644466011740840e08601000c0045000c540c1d4600616610464000403070740c45034a1220300038003038040c0c800181e51143d20400301140a0340f180c0308a0b003442d41c040e1a500f06c00b14151030101c000300310041514046000c24000706005031b032904003c00040185124000080c1001c0c1003102d5035008441d07415100f81e00c01c02442001030704620960b640d0580500345200768125409540e00a445510044e5407199511000c2008024030071503454140ca000392010008840007640080d0341c7e100d0f1000380305207a402845d04d54014a008c1074a84c0007110030080d0f017030404940034141807511000c252050a0201c1c04101402031134130038890000c02d01514403131298542000d40b640490110081c1a1035055030b01e03500000c0c150344568212900400c9103409a940c2d07541402400c400a40064a103400a0340480c2e02080791442e041581c1f081c1c59046414062a22005603c299181250701c14121 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 70853455 1250 70852205 70852217
    0x60c072103021509070b0708091009030302060f04031404030b0406110a091206020c01060e04050d030c0c030804060b0901080c0103050a060303080c0a0908010f09060c09060527100c0b090a020d0303050601 89
    0x4100c681c1d005000d8891f9a204603085521074802204110f8106040c001c1001080301011040011980c00500d0640005a200c0d204420b0b031079504040300c66101c0c0010301c20200b0000600001003003032014407144580d00651080004c3c00389000c803001c1620441c080d52000a072040002d2090806c40f103841c045162140d08014580014100702030700750751060340f00b1401e443c3c82a040005201c000d00c54404603008505d000c00203000001400b90a00d401280003400300300b0428000303020405550b01441c038102005084520300d41c0e44020242d9620381003a24603001070300b05000710308000000d00621054a03815224110603940b50001e0f03e050b41c0001011078104554044000740e02c41007882180685104290049803102103404e00c0c0c416074403c100210200500c0700810418182e126003501d001140c2c40c0103020b07081802d07460518800350445685030344240d25003006010160000510000076109500151803a6100034915442d8511060041e400003543d5190f403000911a6225a40c4014141815 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 70854705 1250 70853455 70853459
    0x190603020d090606080106030219211401060305011d061501031806090503070c0803090108220b0f04120903110603220302070e010902070c050f030a02060c07210302150907 75
    0x69800c0d1443c1d0750202817103941d0341c102442503052000896039000000241021041e107080f0041007041e9400c01c103919010130b1440350f181004507241c0d00348000c501500080c80240c0d200c0c10014001c2040703190101108046e81d0780ca145c042d60116006120700b00c004051140e5883c2e1030b00540161804501104500303682c1140d075400a41d0910519004900070001561a42d58901d0920f003400c0207904144980c1e4018410321f0003503a40710340d4140d8001d4402c0c243c04c451420001d45401c0c0c0192001004124402003010030180d916445083da11a5010f0054040c0307041c20204280c40c8208a0300020f808030148022500302814410011900045e01c0094204032208042100b06030303500300c410480041c2c0080ea4204041030322410850302504c0396690843c40c1c80440d84d00d07031040801074401d06004802c0308210400380e6409219031030b81d0070b4000c1e10007075441081e04002c6444030100d014641441c95060421002180300440d078040003035040e001045c5c01484c2e15070782c8600c1c4400610200c01c1e84964000 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 70855955 1250 70854705 70854713
    0x30e03070f140f030405090601030203040f240c021605040506060f0705030918062d12070906060504180c17060406090c050c01051f030b0901020705070b0d0b190603020d09 75
    0x4603545440c3c0034002d1510385007030408000900a010345114109030050080c080070a079225030182245602030380320910b1410506800c0a0440e0806110b0f06240c0381c8071032100d907a0b801048602c2030720811006800060b441e5001c0008880e010340e49203801c07000500c5028a0b90a1650007800c00c1b5000c1d104403030a2100c510005401810b900381c185d9101d0060701c00348801030618410b012411030001601811403a0708020000c41c01c00d80c0e01140d84176140c001c3c1c46107100c0b00103201e4600503008966040c8211901c0781c00184c000d5000344240411601e181801890328440c5100b90b885400469031405004403000b0780d10b0010724400340c8040da0095851000040c92400e1b40701d4800c4000303103500c1d841d03102c1b851000c599013100d0005000040400041d95803000c4079850b4041c01003581e5010081082c90b03120700d015a802070040740001000381c42089004283d048021015000f544004403003408120304040c00c0c0103529054440091016159410a20210b8001d03000341045070900d41c0000ba410995450b = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 70857205 1250 70855955 70855963
    0x1050109020d0513080306061b0109030c05060703140406020703210506040c020a0809120f070e0a0c050a0f0e01021011030a0e0604030905010f12020c0f0d030e03070f14 74
    0x1000501240c0d00050035a56100c0c0ba0050304d60202d00284820101c0300a0f4841c98464800100814401c08001030a081e84032804068100c16111101c000c00114545150107401c6044850060340c80344100300002e90128442d005004200504407101f81c0e160f01c1d990366240203074002c041e0403410f00c500c10120f02c030200c462950641c040c2c80c064034081084c0c14140103200c106d83d00021042c0440d08110380c1000800c2d0310000b02c1e50f620700f082d582060f03500d100c0d1070344070300300070783d03054182d41c1e5005900c000201820002d0308140504a00c601c102f020b0800400c0c107444611800f5042c0e00421040d4490301050b03409080b0403a03941e1418010b03150184008400c8001311030050f62a0500d140340801030002120945c032400c55071310000e5004200500301a20090071190b442d200b00b0f0b0401141c071a016020b103100d0740a100c452480d40710b081d9251400c284000e51101d80c018420803607889076201011500e0b1280c0241d8100c01d40c084050f40c0b600c2d1880c0c844440c000210320041d00d488800c02480840780400700 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 70858455 1250 70857205 70857209
    0x150307090303180b040b030402030109050706050a030605090906040b040c1e090c0c0312050c122a0a0903080d11040b0a02071212050304240b1c030206070503041103010501 75
    0x103a1500560303400c40c035000d05040220782c05a81035052421043c01095407103400c9606942c0c008130303082c2d126512840080e014100d080002000c5004110000818030b41000151040b18281d07202400100d480b402440214203003100c00f00107a910840100340854140c60304660414003a40c0320030760040c0c41e00048032694642710000808006880b404111511444c411401480d56501d4031461002c4030b41c90041196181c0c40e0581803e950700d002180071003036140101c8503100a0f0070080c4000e403611102c1440001d0107500354000800e0b058000d407411140b24030803a102e04541da283c03460312500390744921041d9041007400c50500c039654080c4260b1008528040c0004010b03110f81c117613450211a40080c1000101d41c02259000070f490004000115411040c3c44154060300d8095113035507850600c0d1a43d40030b0700310448036800d400300b60008ac0c00705540060403801b1098880b90b00c1d84500607d040410000b0003400340c016081140400c154501c1640116009402410700899402d81d81d80041d007140c1c020303 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 70859705 1250 70858455 70858457
    0x30201030f0f0c0c031e0503011806122003060613020706090c080106180e1005040515090106080d05030f01030f0317010b09091f03030807090e010306050103050606030a030e010c02150307 82
    0x8a559841096444401604900e00d00c10000100b61105400581f00e400107001c2c020010481801000d00b00d48983e01c141e004040480d8140b519001c2400c1180c201c00d40f103080703500705103450515046207040c000b036014000da9014050075040800f10a183c0000d40013000121041626030302050017242c540403030741c4050071146000080745481c0040480790341c0704003082c1c6070301d42e0f04016900850940210b015805100400c0001c01e103503079280741c098102030046098040b800307500740600199060543c005400e98107203e080fa04c00f0140c000782910b003808100d5a400c60840d00000600000c1c0032003009031000e51081c1051100124044911412610300360811100c0c0e4001041c000440d180001c50560060184c02d102648403803886190000c00a07107000c09028001c80d000401d80161145558800034058070b85603440e1941c5a01d010b202402d030a110130b40b03840c424607012030f09030303d0040303248071409906843d40342403400c1c03c9005603200c1e600c0cac4100761713401600c1c00951248c00300e401c4010342c410380c85 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 70860955 1250 70859705 70859717
    0x61918020c06010501140717090904030e010906050720011103030f0403030515061e0d06060e0a050a0b0a030f0225030801080d02030f09040e010204030510050916030201030f0f0c 78
    0x31074500e491600c1c0050740814104111082104201c0443c0002c0f130300c0907074020388200c42028140b8903802a51041482260b0040408002c05c07043c1030784103041e0007001b50240d0b180d4030215507034401214103024486014003da0000b034a0390080010300c0404c10143c0f00306042c08410041c98040035070641d041211680260b400341d01c100020564180b01d226400802e04c84466100126100412540d0107480e02010010600c80c0e401c4074601c140e2811b9034005107004105024482e04e40c04000d0580c00d2182145010b45170608011402c2d00c0c110042e4020398411010503410305020b404200e028001c03003007220305040c2c0e082120442c01c1808504201442118903800894030b2054500103041c807005905c81c10305904000c2c8030030b98480c1c3c00b00807a905403c500f02c40ca40c981810b44005030080c000030b10241855032000800000f000306c0802c2e024400301000800b040290381e9440d2654507007035403070340d8201b032000460804e100540c082d50101c2032801c80c949001550a20018011044901c402c501a011400b = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 70862205 1250 70860955 70860967
    0x5060a0c050c21010b0102060112020108070e1002010f14010303140d061d06130509030412020a0512070509070c0302060a111303060605040b12150601050705010203070f120b030606191802 82
    0x801d01440185d03d05c00c0c4000d2040350303d4409a2241c090a0080090410002c5408101c00c0340c454110841800c030b0003041c10b15220740710340d0f01a000780304507840560030a080401d510403401660a585040b41c0d0182ca58489040c01c0d415176040b95880309111058490f5103070008620810f580210038a080b5185003040c0160070f1003c10412590609103542c140c541c01e220410091040c0803040d01d00b10b400c4080b05c0b003d000440d10010700b104540350400c3d43c100d100c0707848402d403035240080c801d03041701d07030940d494151a102d0b5581110700078540c12010b00542d0080380400c0c2a01c405902140d908400028400e003000f07040da4400c2d0000752070b54411703285182c94030340074001031900b441035200c51103084031005115040140e000741c0300d120380320040301150810000559140d0081084441a030f84c00302c0215668a4240009010003036080410b2000424410321004542c10728401c03010400c1c0000c0042449581d408104448107004005111102c03005903c0094400f4402002c210408002c900160b1104 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 70863311 1106 70862205 70862269
    0x2010204030204050a0c090807030308072a0308040b07180510020f070f030c05091e0c0f0406020606090a020f070615050904150c0203030105060a0c050c 67
    0x5007800d0070080c1745030041d4040500207405417a0450581e440701050f903550100b5020060100c1c00d070340041a030050040607004a002580400c081030320015401080e20403601d440c00b140452035180910041000f40c10fa01540101e49260074102c1100c071281241c4940c20a01ca124050800c50040c80101031080c002081d0703101c1c0d614202c1e40c0a565440100304440c0c0765100c1503406107035800c0301007160304e41000c100740680014403001020401c2c17030354026810b013405040300c010613104208142c11913810002600017031103540c0117807020349010402d0000c0c0c16001001400454030411024102c1c104020545080c1504840d00051300c120503182c8000d1410740e504000e610800754400c100420030008000030305180c05420130f00c890305100000342da89000030301619500c0f21b0b052085010180c418400b10710003d0040084030718010b40c10000c2000e9002c070802c16500002a005104101 = true := by decide +kernel

theorem cover : BRFrame.Cov 70683455 70863311 := by
  have h0 := BRFrame.cov_init 70683455
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70683455 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70683455 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70683455 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70683455 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70683455 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70683455 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70683455 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70683455 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70683455 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70683455 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70683455 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70683455 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70683455 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70683455 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70683455 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70683455 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70683455 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70683455 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70683455 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70683455 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70683455 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70683455 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70683455 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70683455 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70683455 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70683455 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70683455 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70683455 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70683455 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70683455 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70683455 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70683455 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70683455 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70683455 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70683455 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70683455 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70683455 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70683455 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70683455 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70683455 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70683455 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70683455 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70683455 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70683455 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70683455 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70683455 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70683455 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70683455 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70683455 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70683455 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70683455 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70683455 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70683455 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70683455 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70683455 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70683455 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70683455 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70683455 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70683455 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70683455 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70683455 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70683455 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70683455 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70683455 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70683455 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70683455 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70683455 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70683455 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70683455 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70683455 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70683455 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70683455 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70683455 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70683455 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70683455 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70683455 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70683455 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70683455 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70683455 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70683455 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70683455 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70683455 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70683455 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70683455 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70683455 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70683455 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70683455 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70683455 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70683455 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70683455 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70683455 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70683455 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70683455 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70683455 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70683455 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70683455 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70683455 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70683455 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70683455 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70683455 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70683455 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70683455 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70683455 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70683455 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70683455 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70683455 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70683455 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70683455 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70683455 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70683455 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70683455 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70683455 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70683455 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70683455 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70683455 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70683455 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70683455 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70683455 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70683455 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70683455 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70683455 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70683455 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70683455 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70683455 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70683455 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70683455 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70683455 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70683455 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70683455 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70683455 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70683455 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70683455 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70683455 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70683455 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70683455 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70683455 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70683455 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70683455 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70683455 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70683455 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70683455 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70683455 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70683455 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70683455 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 70683455 ≤ n) (h2 : n < 70863311) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
