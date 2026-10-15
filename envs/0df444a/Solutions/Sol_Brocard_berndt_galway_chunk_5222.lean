-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_5222
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T15:09:15.562112+00:00
-- url     : https://prove2.me/submissions/47ee44c8-f4b3-42ae-92e8-70a740849b80

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 939028776 ≤ n < 939208633 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 939030026 1250 939028776 939028799
    0x1506081009080d0905240906010b03041b061707030e0703060207050a080304030c050712031e020705150c07080a020d030f23070302150f131a0711210301 67
    0xc403403041c900c1c0c2e418a005054104200d0700303003010558943c0c0c0000e40150703000c45c20205a5400000b40ca00b071216516104080f0360b0359074018031035642d5600c0008001750511941098080b44000f1803090300418a5a950006001e886220546c8038051381001c04117110a0280c0b080f0030040c840c802c01b03050380031310f1030315982c0080d00442420f0341c542c00784107449000500000003d40c4100c0c840c0c3c03507280340c031b0700c0b1814090301e008402e41201907c030181000e1480404d41058401d120308130080c9900c2000860542c0803030421800780c0c803482e004460500d81d151228504800342c1050407201c011074281664440b26281e460f07401c0784000c0e4011000d6551200440d210303844c1100b10041c1c81c10844001c8141a4120138196003090f2042c0c00140080317204020503505000950101842d61910052401c1010010313400c81c030040c150350740307492428500c00c041011002029146890150000c0407501d8a418050070079100114468100c3c05030099121300702803158100380402c0c00c600d2030b03241907a0a01128105 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 939031276 1250 939030026 939030041
    0x5090102070308040801052d0114040902100210143d030c030210050307080a1a1801030302010615020a03030b0609030a0c05270a1a060d0915060810 65
    0x45001c0e03000301001103a0020010001002e500d00000340c90301d80b04041030601d009100700241c1100b01c1030000c0c44035a03034800c07a2a0646940c4aa2642d0703049a1100083c01018014070007074202c01a070f044000016008201c88485480c62241800030101c00c80d40c14590320740c21070340d0403c0d80076520070000b200d032514030440102c0e80c1405801c40c034079a0001000b2000a1059004440295009805004506060300000da512403141041c500710304001201420034070b40240340382c66082c0d5032480450030001c104181e50b05410054412000d4080c000100503000d40240070940c09503003002c42c0018000014094800d442d44580c0c0034044000141d0390031000b0f86440310440c0d03840b800030701c60803401c0c0d078080c4586451144502c1d41c0d00e1190385054144092903090f009000382c07030030090b040317801102010b11000780c3c0000f021000003076241030a89040648606c9040179a085580070900c01a00c1c038a42e1b1250307030803501400100c038011000300d00840580d9094026440507400c41500c04003480302680141c1e1 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 939032526 1250 939031276 939031279
    0x7030215070c09181a0702120421151404050d05070305033601090308090d0504090e01180b010603061a0a0f022113050a1401050304150f0204091401030b06010509 71
    0x401c14135094503031440301913441d8020840c00210a051000141e010802548a80100340c10181440d240c14444200d1040304042044c0154502d0180340030482050140840a510f480b07082140700407502c044030800e001250211031502c94403182082e903e025409481c18030b6031581d509847c1d560b130840d60209000419031495580c1c0141d2400070741e001e0300c4040d020b0401000400000e071b0300c01e060400900d80040504042c0c500d800000204541d643e0010403030342910b0888030081042c181000e000b50040244110503007210500e81202c00410041c019140c1c100c0d04640d0b02401001d440b45003001e00308044001c080c85c011420070440b00490300851883c401428680140c907d034064505d01a00707040032018880c4100640010388142d100360b00800c040c081c2c182529000c0411b03080c107d0030b4288240e0300740d40790705004010001038208110101f02800c1800360203001d00043c1e03100400c080203508240140138045041109040748461010100c078103d90708009610f400b902d4140054034240c0c80100d445 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 939033776 1250 939032526 939032561
    0x70501091a091c1a07080a0905061f050303030c120106211107211403010803030703021b0a12031404020307030b191a10020706050a120204080f07030215070c09 70
    0x9401044600c001403d803803010354002c82c19440c20745c0e0024080d8800a0500c000503143c0000782020602c0010320303503440940410060381d9a0184512a403400b911036103c507604d48000020030800c40d80c1040504640141d04080030301d56601d400e0159800040c030050b000016000142c04070001103150029030001d900c1960891608001d603e8410350240c24960210300812002c00000c556035001c91050203040c0c060300c1d66400c40d418208a10b40380d2102414003010582c020445454050341180d100400c03d0025040b0b6051010a2901f0902160171a4145c00403074600b045400e00081d811000b14850355004003d8103c0b45e08681d543e05070b000300034044294000c024500d440001040303120307141c2900020262403011041c01020440000700c400c10302c404641250501b000903d41210036240c1c50512820100320044c055000e1a001340a6903100320000e1190f21100800c80001240c0701068a0080d58110050089110400081e204914004151503030710782040040e45642d0748040155107a41911 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 939035026 1250 939033776 939033829
    0xa022b021908030a09080c06070201050d0c1103120a1a18071202040315051302130506130c1d0109420816090311060319050108070501091a09 62
    0xc843c83c50700000403540201e10440424000b01c0c2007080713065040c4030115151890003940d980003c0c140d02808030301000058840003501347d81401030ba2404078078817148048949529101c2103c0c107150b03800b03542035038140746801c2d940c051111014541c1c41c1c0ca80e20203007000c0080d4202d201e050325554001032040c000c1000e001c0c1e084845018500040000758043e0020240071526107240000b1240d000d0f022621700980b10703c0400050711010440140c9030580c0745c0000d0a0b96580d80400c0008c00d008983c015558070300b148009900340c0028444111150105909a4004038034006580907000d90045a034035000ea4540c4081d800d216840703240d042c3c6a4101c811114480d80802c400046480103481e202044185c020030601403408010740295603254980120740d1881c5495200341e140c0c140840074003410000000820128000200000c1c40415400400842da910019180c407031036140103080c001403505000051090080c900780c55848401e41c0c1e030310301c0d115000007082018282c600c0015800300c0c80541 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 939036276 1250 939035026 939035039
    0x120504030f08190e2401050a2106020a170f0408041403100207030903151103040609030e1002010b010e0103050f0a0506030a14010902012d0e0406170a022b0219 70
    0x1090b441071802c4c001419203c02014210a100c80404541c030301c3d5040d80001001682d0700c201800080302e000810003005104802e4420b040103401d00c9000c0c004600000f0072044440c1d00181c1552030a1b20004200038507128440702c1c04060070240c07009002c50509100a1040308600d080c40038409000904440c82c24807901e000500340d8100c0181a80403944841003001406074940030410108101c54082005408140c0038040da8000584040c04072603982100d40105070107000b40001045005040500d44010844000d01070403201c41c4c084c0c0022800c20a6070b1080d402802034a000b0a1681c03408140b6a03203100000b4018000202141c0d40351096150f00c00118039a075900d4800c6481c044004107400103913000140880031010306080f00c000504140401e0072002c4401701700c0196003440e200201403030f81c800140c05054980c010300400b07034186200c00c401503000140d20b0452442544d03103a40741e161029035240e0706002450391034900708030042000300524200a54064481c210314030780c03a40c2900d41c03c = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 939037526 1250 939036276 939036281
    0x803071a060f03060a06090b0a030305070f020112180507050d02010c060e19080901080105120607030c03021b0a1202060708040b0a1d0c0a0503010209031b04020c1c120504030f0819 79
    0x1030f401781c1016a50f44040c04080040c0c092100c0380001600ca4814540c07556030700030410312803484050101c0b401c050b000301c02c43e8800c0316090348202d40803d00380501c6074810b00755080c1074a0002e0403184c4d4031400da0005030300e091140c00b281e62560161146080115203485000c0034000f043c001c1942c60003010710700b072841d100f0382180c80c140351b006000b41602c40c00120000343c400001078000c1c40c82240403034807208048a00090240e0702815034940481c40b40030b1408107802a00509880100c64103244641c20404000002d00d055428002d40d20000c40146801b401d90301c99105884000015108800040106250361100c5811800340f1400280540300060040041c043d04200c4503601c2c0c00080f0704480354640300c4541005003074124021841c084c03a13140040c0c0d54802c11815500100020340c42070800c1c1c0d50310b0741940c0251000405035601803503844031200341081601d42c450041681d01c000041e01606511443e0f2295506454111001c1c411030741c1a80c40c0a4000c042050b04000c0840d01c004180090 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 939038776 1250 939037526 939037531
    0x60319021201061b0c14030f0708160b030c0405010c08090901030605090d111e0708191704140913170309070608060f0d0311030f03060a0803071a060f0306 68
    0x7261a10055061a038010040c91603d240744032400302d09440329011880702c80f03640048414900300100f83da20748001190504134044040b80c500d0084600028030014089000c120712005010200c40180c0c641942e000c1074081038800144041081c40f007405903502607450680864040c2c00f4003400c00303c02600140551000340c201702c869948030024009405003c10910b15911a5400d004400ea181060700c02e0342c4a0059600d6014900c074804045d0381032009016001c0602106400d55400d42403100c90000c2610040c101121001c0c0d0710084140b94030142c01c1514180c452010f207003090003a4480422000c420094230300b0111050241c403040c0090070459250040541c070b03140d01900c1e840c02c40e040a04140c4240d1204050140c00820010560b5039420780c800003c0c1d00b203901405280082c00c0c101e07040c20280d94001e001d4030002a00c0d0029407462070207907210320030460f42e45012946400710141c0701c1c0a1140001c00303200c030741b54a050b02514004055540031402038490312441502d00000392038402c0a = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 939040026 1250 939038776 939038797
    0x8030408120c04061403190c1103030a140c0a0e060a031e090201030b0f180907080706110c010c15091115030a0506240f041203030b030c0f0f06031902 66
    0x6080184640000e05c41c0c200d4941e0316415411b51130500815140b003130441900b401019520082c41c420a4051441c038050b006c62101140c0e1240b50803a8410020500d18142c80075014034013000070700d03501414040324842815581c3d429190b240c24030070300459402c088a440141511800d1480d002482c52104000c0c83e031a00e84080b440041e14000542180d20310b0380518055075075507441a245c4e0701c1d0030002d03071111201050b643e49141d803000d40c002d0038010a40c0020342140910000040c3c2c0702c1d031101d00e408018003414203441d5030284e071600545d24080740b12802000c0c01a2540c0c0c0942d0340c0035552140349001d000d030703c03480000a4050000b0301203a075080c90760090fa00000c020322003c4051703441110751201050361a00700c00701000704510705484840140b0000d100c80010f4003600a00d8600603900145a0740d003031040100c4c4a46000b0703000e03050301c2071a02e010b8821805c0d0701c8402c1ca00841c0c07010441c034001c1c044411646205050000603800200803449c0c2e980700c5501c160b04440c0500c01065007124 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 939041276 1250 939040026 939040051
    0x513050d3f08040b060a080a022202210f070e0f04090605010605070b0a0b010207050910030203120306091b16031b03170114150c1603120f0203070c030803040812 71
    0x1e00e0701e13000302da004000d000907002e00461300061100143c0061701e520f9054040b19450a0028414016401c0414140e981c030001343c0003140d541103862034210481e04200410049140e666241c1c01c80480d40f0343c040f55a2000960340d8161400355080c00c650500701c10384090004540c824030b540715501940c0e4281d005000040300002e8240501012807403040c0c1007003c44005000003504100000d59490b0123014031071042c402403010507241502016400700865018050300e0f0803250001c007500aa0b0011281240100038810003e814864051411121049403c0000e41000180c1e03100500b0491601e000b102401071aa4090903e0316072540300311a858800d0f0380340441c1021034038540c65035100683c400000c882e202030701400075039201c0c184038644062103034006841d0702403072100c00c0c80c2904202982080312600a404000c1c031072845031103403444096484101d021110303001c00300d07500d10034210094900682c1500c03d100040d020710041d50014001c64150b414a0101c4c450131b180c810058516081211 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 939042526 1250 939041276 939041281
    0xf09010806011a070804060e0a0312020105250807181706061008010b0f1e03040312051005090f07020c13020a080f130210050412030513050d3f08 64
    0x500c1048203c400b40d0b042c060300b08041941c40120500442c0105000e00c030420302d90001c10388a400040b0002e580144c02130700d06090900c4064002d0000303071046071045031480d8142c0312640440480c20313140072081e83c0783c122036580d00800710741c08040d042003a80904408600050400c8840e84a40000741c5c040d40039000071706007401008030101605104d0b006000200d0010003c2c8540740f0306556181600841c0701b95035070705500b400c0c056840082812028a00c0100c140401c1c5130340300105407480c070f40d00141003005440315000349141c544984100381c0c1c00307040040061b80c42b10b2464105500b02c00c2d02e0044460010980d4005060103501c2c201558203294082032600d511a4014003641d003100007082d03201070904140c044c40314a020600c401a00500700a001500264843e100320350080c015946010349100451400030701c0c6a00560034941c12119819010035030b40780100169603006d074009614480044072007551040c001c0140040c03400d0b600d40e0008100c1c1800f01daa06240d0455260780d8108080c0b = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 939043776 1250 939042526 939042539
    0x23060705041d09120a02011a0316061d0a06030b041410030f06061d07090e150d05210c070e330d151803020c19260f0105100e04020f0901080601 63
    0x1441d803802244e209500042b20380c648201d4007044241a24101d01d03020111224401380c06c02ca40c140440e001b034000320091400141d40d13034035601c00000080103c400303111001d400b2581115586058400c440000c148034410000255840004280b0500c242c0011a01e966600b6003056220744001314622141c1c1d51400300405a070303000c400d40024280840c44c0390840c4c144006282d00302c1d076181e07040501031200e400b600b10500c1810041c10000000600040079641022202c443d9650400d02d030345170170380c803803408007081e58031424088510811f02c5079060302d140360032071000c03c1152056085020816561000030f001c0d640754840e10714803080c020001c03070144041c1083c00104580100c1c400c2141c440030014900c00103540400c40a00e91601280d42030f4a003881c1c05407580700c10300e030342d48031602400741da00900307034542480050030b52010404025600c0d1480030901083c203880048401d0750744286000da00303000b03a04030341d00290b40090000c0c00600000c031800c000b01e46268401c0e008010550300850040044 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 939045026 1250 939043776 939043811
    0xc0b1e0f0403140109110d060f050903210609040f0f0b16080114010827061905010e2503110a03090c0f0305030706110723060705041d09120a0201 64
    0x3c00ea0444000c01c15100c44e81c036510f1005068002a9104042e4403981c101801440d800c00040603039015400c00c80c60030042d040507501d0b03100b00c0880c014041c0350017808e18900040781e8050700c5944d000d00048001e40c1c0320b540784442e001000504507182080810000080b40380c00c0d24141c81400c1c070200c100001040800050802641644000010000c0884031103103664003001042c4c1185404514030b40300c91101004040050f440d9114041c288600d4013080b05c0345c0845155500b105040703102c01c2290f40d0325070004562004d411a0000360400554440500b15500d901c100d030480405803600007100b041c1d40404210540c0414070400c002511740100e4418086130700019002021600c05d043c203c140381d50390b5a03469001d516806007a041d40c2d4034540c25080c070040e0880ea091540100310007004002c0c4100302d00d01559038425408944140713800101c000b0702500440c1c040e25043c00c000203041b086001c400c81120401041010a806501440e0690306004005400011030a0700041030b2811060740b00c0c400e = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 939046276 1250 939045026 939045053
    0x507210c06080106140408030a08040618050309100906020714061905030603060a05091e010608030f030109050115090b3109050f061c050a0503030a0c02010b0d0c0b1e0f0403 76
    0x1217181042108103e004c0d00001192200a5a82000003451341d9a051400040110038544641c0788540f03d960004c208010004000e00841190404144020b8040888610016010f00c6015a002042c103105107240340c412030800041c010140d81c64280013030b00600c4141c04126502004c00c0380402404040d183c00d02240e9884041040c2c104920b107000ea54a41e5039003004036a400b0083c0849022a661200039046070001d80151000ca079599007403410003003c540d00900c1421509c500d000000701c0c8144103411180c05403142aa280c0384001c0c01d0042c0a410ba601c0340c40901010340300004000d010400c4520840b403c05120200e28000c5440c0007503850944030001d0540341d04007018010400b099441ea040000c464600d10410782c41c04401d864524070301018200c010b400f5100c04410402e500b40d240e040080589480e9001340081d101640901c1101d814600004060381742c4031a003440044204405001c503070819510000c9640400014070520350f000e015001e0707080300000b03010f1092001715040e610 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 939047526 1250 939046276 939046307
    0xf01050c030c1e0c010e03031602041b080f0901050f070809030909100f06030908040e07274218090c03152907120207140109030507210c06080106 64
    0x85942225400194480c80f0350b09e0744151040c0c0c3e400c5400255141e580c4079118100c10141c090318100f0311450013800d800d1302190a610034013110310000704030f01c4040c01080d000d00c10800e0342c140f203030300ca0030702c00e0f200840c0040140d000c0e440b040c0440c0c6855a50344102500070440001310500143c2800001d0300c5540e4190084824541060300c840b0019103100f04031402c440e10806016000c1d02d8003901150f00102c03542a648402e00c1c028900100d00c3d41d07000880088070307501c4007030201800c080080385010081261880c050703442c004000100002c41866140801c80380d0740f40c1108038180300001c01c100e202482d00800d0103140d0317075204c40e410590075210b1440000003494800041914003200101c003009091400c0220b14070500004d08500810001d441c0403070780c0103100319801c3d5000f91000707680784600c0c440d1445410505200800d2540100707a104162a0450080c0a00301c2c00c188804860310012482c086081e561202001c02003030070790040d00050101070341d5040281d490b200000700940c04d81d08010 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 939048776 1250 939047526 939047537
    0xd0204140604050a0216060209060f070c0f060914012a0302030c0706080408180301060504060905060a0e0c070f05030f191215050103050a0b03010f14150f01050c030c1e0c01 76
    0x41c40d120306c01145100130f03a030b00503000341c0d807041d401300401c21074020081842c520000105c0e04500704180d9102840603920590240111141d2306c540032600c80301700d8811301080c1c080b0001e0790b030940d5103e051440810b1281040002c860071b030102c00c200491082e0807040d0f0041e00003203010304540d4401d1241e00010b00b0285800150f41c105600c4400d1581316001582010252500c2d2094440d1401e4106200401c1c00920400c201541d070f6241002070b010444405108020742e130004620b900807019418080c1d5201a07070181882110350318141c59880030001540c0b07501c01032109030040c2c00100b00801421100142201c285250074030082c0042c4196251110041d09010380018080444007003e01181c90034a004280d5844100072031004120001121f5055401e11000d40b1404909801c501c407042a0202141181e44c0c410030609000ca140c44030b084e621214600388948598494000303452454250f60517a440d04e611141c14501e44092641c050fa8180b0141049003d203500910000c0c1720341a0a0902c03 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 939050026 1250 939048776 939048787
    0x90201032012070219030504060e03120f0903030f1b060c19030507111204061709030d0b03031201060201091a0f0c0d0b0915090c07200d0204140604050a02 68
    0x918002d014005540300394850881c0040c90082c4204001d450381c5240d07003801d040540f810700b402442d50340940240c4000c1403994103202041e050008030020000c038804072060900800c0c0303011092039400002003551601c020b01401e00440c0b169002000d448004040c00d10b50010160b41c22824036000070070810103c1000d000b140c0c02041e1401d4441032001092a002955a0715040151010b2105014010052103040b8410024036034803c014829205281c462410840c11480c60311009101201c1c90002074006100c010301c4101c40340c10011741000010250f9044c0361b000120306d0b00c0450264070000040c0c2d1200071410512040762100c0403208065181d202903880c010045104200020340460f1110000045000c04581c9607807121050946c001c0041c082410480400d0126030301d081e545500c0345100c14003050042036040219140150301040b05100310716201d0100600d80140100c9c42d421104442c20307a001a07541e48100310ba41e41d282680c0b03040e00e0402d0405e10003103400043c244a24540304001 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 939051276 1250 939050026 939050081
    0xc051210031a090c060a090e100303020705060a021c02190f15020901020a0b07050c01060e0f09010c1b021503090a12050a022d0f07090f05011520030a0309020103 71
    0xb4000100c07041610403940d981b00540d0201e50032039503a0b100304d41840e0128107108101c000004148101c2c0d00075821200069101c2040260b2482500f0001c400340c2e210b0f00c2e150060040103894162149002d0040c3d640b0075510207200c507031002511404951641c18002d9640030862020761071359085040039011403c1200502c0080d58410701c00c00080d00103000100011050f500c28011107010060107402441600d40e14021183c40d41070584549620740300c008000b4441034014803070340d1b0b400e410959a00c007100341180809a03028080420682e041080003101714a030001d20f40040d8050000030300102980d6206084c00d54004007400180700802c0380421105070701e01d40c0010f0014510303039403401026001c41d05603004503100c81c3d451601080c6004032100b0540e034041c0481d00c4811104141d50138448000f079866070004548090050100502c548440c04000600c51070040c151002c40303101c001580078211031910300c0c64000725040400240c81e03010000444d6494010f041e82c10320803c00300040a40c00c101d = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 939052526 1250 939051276 939051283
    0x1f060b03010b0711031b042304081b0715020c011805120115060e01080703090b07030e01200307120902031002070503130e01030b0c13090c051210031a09 67
    0x700d10300b0320751004a407460910a0340d007080e803520344009045996a9240048050f10364070007035502485280791448240303441c412648a206000f01001c0d1000e60380d40da680e1503150582201001d920108803601c034162043c007040100e000940f02d140b400c00315540485030028600326203180545e040090f0302000e820001c0e0b220300103a080c0d0303100b15540c00344a1800b16403140140318800103080c0e861484080011419004800d02021120aaa40300702555901d042901600c0305414001e21950685000401680c46a4044600b81604000118807802e8081c04031040d989802c1c05601da01400006004035a508026860380240c0264030a00200c1c0540c0c0029480d0751072001c0c140f024917000601c42d4108141802200d00d842c0c120240c1c040c0399511030100c58070305142400b0440c0d0070461480820120010501981c1082c03030750603000c0042c2d6040070b080f07002400206054006011040c46404100181050514800d24200d04043d01461a60074a0081c85203821040741440c0408010b002400344c010 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 939053776 1250 939052526 939052529
    0x140d02010905040f0f020d0c110a05071a0903010507080609060a0e0a02131e030501180b0610030e030423221e0c0e04150503030412080d020c1f060b0301 67
    0x40b1400140d66442c64006030150520b810241d072174520000e0300108100b403d074029091040242c4d01c04c1c88180f4108061583e40e624040007074840e40c0142020411448104000c8480f1090000410700f058041c4020074250b44069820401080c224810000c60381001030a55030b0012040f80e40c0041d0620300001c064110030040c0c107082900343c00117001c02084107d09080030042020b1a0030101920440314465009050b500040301e1550070010002500720f00ba50f1000c1c103445d000001d003502034880740104580c41802002140501d41c6603190300d8081070b07080c40136200070700f103078401f40cc00500e01030f081c3e900044040350b81c030b4480d020050b050854014140181025041e0402000a0300710b080b0b11807015400c054050b4048c4181003c1110072040e5200505c1004482c0031f80d014824100800c064a80140180c05000d03015030007071004106400d100c221883c030290140b20b1481c940903035001800c040ea0710411b145210340d405103181011400f10482e0b00d000c40540820100941800c00c9401401484103 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 939055026 1250 939053776 939053779
    0x1312080c0717041a04091404080a0e030a05070603060608100f150e06130914060102060a0c0504050d0b01050a0905010b07031110140a06050a141c080304030207140d02010905 76
    0x440b81a42603001c0444001c1e04c41400c2151604000600703c158a6006006562844d402d00c0c40701c0c4d070440c18084950b030156038041281ba05100720000211650010080540c0d4188100000403022500900c0050082c1001d035030049442410142c001d0304202000e04894015041c0e0001080740d8451100e602060300c0b090950140c08030b16000c011941215221680d5a0121001401801c1c016100d0300e5142103600500041c000340b080d80201e0000d070341088801074050f80040c000200b0000e80307507102340180d09a03170414605050316071002c1401e840706508102d500b447c0910044c045482d1200000c001400c01c40001e00c015810303c03070341001600610070010103002040e603280080101c180702540309942001410000989121701762050300b201900e5409905140075008212801d103441d0303520950340c401d620a42e004030680c0070302c03166569901070321071040c40b500d01d01c0002030100002140194026030041510324104a0b1070400c408240000034422500303040c0f4000180d8000701641f080341c00 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 939056276 1250 939055026 939055043
    0x313020108070c0c0e160e0102150a09140f120c1b060d0c081b0406090512010603050d0f0e011706100201020c0f150105451312080c07 59
    0x3240e030b00560300d003c01c1d0b1800514840882c940420690310241d40f1034821440301c02d08000450b910182078684900064485005800422050501c440b4020b50140c114207146000a240107281d01c5110070102e02c5c450103102900b1103032022420040c10841200344204c0c42450a2a1506c1484019510801c0017560341e90300c400f8140508150b5590700c00d40f43d514048800910000792212002080410100c0d43c28511850942020745a09040d4003914166100ba480e800441401c050411414100071b0407812070940d01c400001c03000034014807004034a0304c1d054980d501d84540207070002e04900c2c00d07010f0ba0390410940c1800e142e6100d51402041360040300994a644440c1400e2004a0192080b40034500803485030074000b0822450004041d50310384505403c0141c240d8071001041a4011a040b540d2200c4820000074150302451891a8080000092402e01b140340090349911840d0b074210703a15001d030080040d255080c0003d006c06c2602c10741ea1898003034114544190030741c060f4010204094501e00 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 939057526 1250 939056276 939056281
    0x1060809030d0c203f0f1e0a0e010f0e090903070b0f060105030712020706090303050412540305101506031e060e090c01050313020108 59
    0x240305000311006003889607414043c40c41d0250010b02014280c4820f07040f0341504140c00c0907000804910304400001e51058a0b401c0d1500c819041c03070511140c882c800550b0011003107114039103842c130002c00840000e0790b4482d03241c140f0f92001c01003907403480d01c00002404003000b9100c0716039489000341e00901c4090034440c0d1b1100c444101150002a0030f100b542d00311a0707400501c464a4000400f80c801070b84100e0f9019540e0b50350060852002500b03a42007800b1801c140301280c811409290001011000030a00600b0101c0c503841319800e4403402e00d4241d010a40d0360080c8814000101040403100c0382071306000b030303107500d1325950b2203080c4d4815182c4000c1d110304000e42000724076580040c2480c0c0c0f61040400784107159480505450b070003c03880205e41c0d80c8030300744007440c590003036010b02240d01c4000075102e003119182602c02d80191032440038008103c200c480401c4d004085a214980240c0003ca00c022103d24040c0a503920f03100301414245d06109050040010016400c240c040c1129070a20b84880f044c0c = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 939058776 1250 939057526 939057541
    0x16080d0921021b2205091e1506240a030203010f06080405060703020f070501061503200d02030714031008060c120a020c07120305030906010509060d12020705030706110d090e010608 79
    0x342129188590680e0170b150621400c45000036142107400f1803d01890941d40c0e620440954803401c0101d00a03114800e0800121645403400f58802d100000b00c040c9126250141e00716080e65004c0c624040c0842c2d808801800f140c2d4003207603940060304a5080c41003142c1019180d00703079144c10040c003860030941c00003000c0c50501c070f00000780c138185948000203022450b2039101020450a00c0b49011000a10700013032921002c0c100350007808041000d00e1520310307000018070200013940c40204800c080c00741040159481040d10001580f01701c00320183e403002c40c0d0600b5003c900b0803601030414004100c0921400a100402d5201e094119244403401640d950207007001c5414150355034400c07120f6a02208a480a140d080001184251000c0056035032907170325801002800c090541e42950440d4100810500041c010090b4018120075030040307a00c551f980e980000e28003252500300e440040c0a015454605081c10058100c0011160515400103402c1c40050000b6610501c1042c0c2080004400716006 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 939060026 1250 939058776 939058819
    0xf09190501180503040515070201051209240f1501051b070b03070804140304120b04031103040f08010b0a03020321040308070b0103030206180316080d0921021b 70
    0x80d00307180401c81c214102820526145d400c1440f542d4002c1e94070700e51440040c080d83c4201c0303c110341c2c161102c90a00b12a10261001c101000f06110818454400058031900b180d840c40c0c0e5001400356461280352500411030f044055000c0c10403102c0190450303508041d6138101c2c05a507400c98a01040791030300641c900382130b07190010952190303900000c00418041c5155206403418031650003002140c1c6940f60395103040c0c1d664400c130f215030403401100b48a49400180e242903581c0c4c22034041e141402d204604030a0302c0e82164029885100c0146552000300251103081c00707001e0800104460001c446460754001c02d455203040c00c140c06104c9607050000c01c0c038030300304000c2d6030146421a8180341c40f07168034640191a00020b00041c0c0244c07081c0800102c20a20810502d515148070701d015604003d8500760031113036520140c03811180c03140309000c0c0e401901150300c24082070500515004100403032000d90743c0c8106d80100c80700740c219000308039840e03c145000d901c04410102c081d121010301007900711403082c0 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 939061276 1250 939060026 939060041
    0x180b090102070f0602030a1b0c23040e011509150306020f0f0a050406110303040c0512030403060e100b010215070516140c090601030216021216030b0f0f09190501 71
    0x7810050843c04642036a00001500190185031140c1545001e8003522800c600c107005002071414030b140f041880920b04143e80c5044480c614001144a003150703d00150a9402d0500302d504a69503d014071003d07060f0702400d06004000002040045440b00400072148001a00002d003c45030001116100d4441c003208685500c0302e600e104032b440c3d4070a894020000c0d8031622600307000030403603560904020000300c11603008a505c10072294074685400d080c040c1c040d06440b00704400740410710000020030420302585484054150141c100880c5c800328110445d4003031851075045512074400103d642d413840d01c0880e040469410807540701d0f40200c005565070040400000d080c500780c48851000180c0005298449d000201c4403204c09030b8404004500301e00843c01d4010300c00c100c4032280d002509050302c01c050401080419078048804410f4066042486030380101c1e52854118100000d44c0303a104041500048000081c85007400e041b1034031b5582d090650346040200c1c406040b40c00030040b09610014 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 939062526 1250 939061276 939061289
    0xf0711090405030a03060f06020c10090b0a0c14060f0a0b0d08070303150515090609030106091508070902120412020735031608160203060109020702010f180b09010207 73
    0x1407a1515115440340c000035100b070f0120307041a401241c82c0d40c0c20514001503503c144d000f003922004520170881180610a032603020311042c81c9020501c0210301c001015441096110300100d28003d18100c0b0f41501301c40304641c02600880148000d1810101d10f464010200d0080441c0e2025a000000d50304112108001c040d810009060400c164158210860000c81d11511000d10350740c072424050076070307070180701d80c2584c0404001c040414940540682480751020707000240494403030b4815821034500122a00001e0000d110800403400204104401303410325040640c10940031480b04100282c2c040c00050651203607030a410a4030b8420040d9000030001c014900500d4070302280c1001841c52061a41303450b04401000c041300301398002003180c0c1c0c000c05000e2052241c402c15186c51805800416442031100394030300c44500035a50030485203000e41a0440010703a1a04684005021415000905c400380021005a140c00743d5891070b044044401d41583c4c03c0d640d1440400403401c0400d144c2006 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 939063776 1250 939062526 939062539
    0x20f03030426030c01091a0f010810020a0512090102190e06030408030a091a0601030606080f070e0a03080c03120f040b04110103020d021303020a080a120f030b0301180b18030f0711 79
    0x61b05006c0031940d1484c5002c00c14514100c1603c90005028103000300b40640c0b5a158001c0f01920302080c0c1a81c0200640310003490624200011050301e400c040c80d0540e0f03506056034001c00d0194100d02504043c181003038890410760714910a840101c1c2241c0001030000e0480b041c04800680e030b00c81103400104400b42d1110200c420842d01c1600030300720001c107030340381400645490b0001c07400500500000b4020100100f103d4019924031100f115080e040c0c01c02d00b42c2080132000000300081101c000761003075841c1c0c0805180c4580480d00003001c2c40000502441d21940e000d402d00c00482e24154172503802c15004803100c40c01da00c2500058020f40710f1070f034010510078400103800e00040070007003002050b01c0c400c80b8004c80d119540c0740750300e80c7c5025032003024248085282c04074107900d01600301d0250129031820080781950b09076002900711400c1c03403100809180d0b0004154100130200030f443ea406800307c80d480600355001d500440d568010210248450720700010700c0800c1c092443c128000158008190 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 939065026 1250 939063776 939063791
    0x171306120e150f06030c0f0d0c150504061b03390c0515070309380d05010503011a040504020f090c0a0f0503060f0f041407020307020f03030426030c01 66
    0xc240d49007421241011490003c0d808581189008550600c01a60040200401807103040800241c52030074401215005505140010030440907200002c10320f065850300b0340c44a261104c041c2c110401181c4581030700d201a0640030000350804480c00032500c0c249003403030b447c81040d800008820030b13107840018035810018100080280c60050f14080e034105488040103c8400c01070400c840c0504100100410a51721043c00080100c400e882c1403511100c804007084014500c1c42000301c000d402d6205c41e001e0700014800620100d501074540109001d4000300403c1c0d030382c00403601160110003102c620076a242c0f400302d0300f03540d01c0c50941041004028a14440742c240345261518a40c00b07181071201040200150b0a03146000b181500d20030640901111040c119020800490a0116540c203500036a10704450524910100c000703031140034030307800441d0b443c6546e00400c2844541040d5075031199008200c180242510800512800341002c2000b010441c0c00d401130b00d04500651100940360b40c6000320 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 939066276 1250 939065026 939065053
    0xc03090b130b0313140106140d0c120609110a0b1b10021912020705030304061838090c040507090306050408090f0f09041e050a0f171306120e 62
    0x125908151080103540c80d4140085c0015007070f80ca03240b2480e8060030344149014894103004000d42541ca01c40c03410300100c1500c1300d00281500b15007200541c5c005a54203a008108804074141d0340001100b1581501c05902e400194501481481d518010350120055005501c20342080692200c0a4480007503480351029a0343e0003202d030300c4800c0280060340711000c44481401074800c0304d86240c0c00c040038501d1540c40b5107489010700808401c0c2402c14401010410206d0a00d800405004d41e01c81c008010159007081318191040105050100c1d0800300c60902454410018140561080a0b1000306007079075420340c187c50303581c0301d81d00150010742090100702c10481e04000500e41c1c80b030b044450421382c1030000140100b081a403107200d46c010b40204c1c081400310b510303440d4071f0345002030b00c3e030a0b80b14926960b918641403505a000880703000d010900010304200050107214a2142040c0046050121180c0c100091144502c034400074420b1080d0350001d0140180c110300800c110000440308044010380 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 939067526 1250 939066276 939066301
    0xb1206042a1203080c0c0706140d050901060608060301110706180f0303020309070b070803071413080601080f010e1e120c0f0c040501080304091e050702060907060c03090b130b03 78
    0x10b0b0700300e00041c4c00500281c4030f00b03c424140d83d007501821005240140c10708030103031044030241c000d8400b0b915080c4024910f0200902506100309091400030400c03500e0050050164203015102500c41d9040006c0c1010000040c019140c40c90f4018a0204030890580710030315211240134070141c09819001c44203000d05425030001c500804110007240c4606a031010100d03600e0251080040540b402040410816071168031600440e4a440910070b1078845844a0415402c08640c05182c03180c200c04010040750b042409a6150035001c40000d0025220b45080b06d41c945082e20b14580442c94451112000b01400700940c039250010402c0d2503a0392800d01c010355680d034041200c0d45805100f0010f40000e9400c2c00c0c0156030480790301d10001c5090508050480f0040c001d9044001440041d440c60f0001c52401030050500500c8a8ac024248508003811040d0030040503070850024840c00313280c0c5d0320000e580072204200708c5206003440340c3c85007403003540850000002d504c0740407001008000d0054a0b03034602c = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 939068776 1250 939067526 939067559
    0xf0f0c0d110c0a0303080a0b0316030507050a0f0b07061e0b0f030d0905040c0e1306051206071b060219120c090e070c02010c0b010e0a0b1206042a 64
    0x2919100000a010744065a45007008805190010100c00041000a000ba084c031a00020311240100700040e10310302081c50120300c00d42c9040e03000c0b0300c04402c20a00900740820710250406503288401d61f414030702181080700051003043d000f54000100c0754148103440e030009500551642d5000c000c0003008415070007808440c00010b00c2403520130819480e83c50001109041a007060700c403902220303e08010040181905000700c020b01407083c400c00d0340b5540b0403200c1265501401400643c00d410401803010200416500a0141d03221b14240000140c103c4050090900700031413130004ae480500e0220040c0c0540d0829103c072050202030700461039007190340d09500c0660340c10200080341b0384541c11108914144100f912804a410200351120b2044102004050044c107040114540303540d288100da51090b4000c0d0503c1441e00c05105202c4802c0c0a15140e85100320340b60b8401441c10b46410391640000342c4002d00070038104890241c003044202d6001c0d06000e030407903000712055503443c0c580c246c1c0d16507 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 939070026 1250 939068776 939068803
    0x712020d081c0c03020a020d0305090307060e0d18060509090c090303070c140f0a0308090103140c03040302010b101b0519030c02090105030106080d0f050405060a030e120307140f0f0c 80
    0x41580758050342c4d01c244207442a00c1d645070300800d01d5003120750041d001407034090f2007003005010401a403004510140a0103820498483c000c03e070791248a0750062000203007503000d41082c0e200041c10050b199000d8280d51180710300315240c0f45a40c84489101c1024801d0000c034942500010440d001800b003800080c604031405940222040030340300d01040503003068202c080750700010a11091012030700349400303803901200c18140010043d500c0c08902910600c100c2c0c80301c080c0d13030f400030807c03040650a0007503406e442e405072041619640880d030301801d071440030b8908580d401a05c40000c3c083c8007080011403c80e00d070b00c113030f1116040c809042c01440582c44840590080d40c80c0400029141814440d82048840c140007401002c252906c0071111b10070046080707410028180004185079503650010b2000b00c2c081e0310002810703407940340c1c0103003800050318803001d42110030300800480c01c1d0842c07190309081d400890255035a220b151002c501b90302440114490701b02e800300e0b49111810000034200c00e403030703413 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 939071276 1250 939070026 939070031
    0x12c030d031b081e0f0106180b04060f0306030602040906140d02030309010807020106030203061e18060a09050703050106031b240518090403200f0712020d081c 70
    0x20108015000e4490216401d40003220000c1c900c20342c0e512030203519402214111003410b00c0c0400b64a440480708040e81c000510320807682c01004070070740013a1810301c0c8481d600002c0403032502d4521002e00310f0040740f184030280511101d0400c0c00e2803199200002540d03009104549581d1144030800c0103244a0044180d0300d2802044990580303840084440340550080046107404000001110318090240c00401950340342c05011005035000c0c05101c0c403804505070191350f00c01180003c60b4500f0710140c80303064800f0f01c003a448040702c8404544503a2041810310042190340b083d1502600d419002d03031019100313500c0d2034000320400051a91003079000e9910035841c0c40c1c241c0c0382d187c010a6480a084061440079a040c125020180141c002e810007411001e0000e44292807600071801a030005c40b001c03000100b0405141a074600d590070030803c0b07144100700500c41e540c40c42c5052030392801d05014070962550000d020302c2c110b5491140e15600c083d4421507403502d0308840c110340000e040c40701c104903200c0e50 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 939072526 1250 939071276 939071293
    0xf0c0e030102041a13030f0501090213051302011407050114180615010305041707030e041b021504110607050109020915090f04030908120409050c0c060c09012c03 71
    0x103414002d40d000e40e01424281c21040c0d0103940d071320000794425400314005070030301e10000020404141c3d442d41a140a43c0021031040858410040080750045150569514040c00d01c015211980c4519072000d0b4207080001e40c0d242003100103101030041003001000c0b9800d01208144a00031100154011101d01800c2c1e0350602c0442c54268540344120340244c2c45040c0100700011940c07083d080250841c0c01000601070070180002180082c3d4000801607000c154104c581c800c090070180b00d5a03c0605081d1029200503602030030094513203d007400904401241440400e06000041032a05001c61004105c00c2e0384141c03034a8810701030411000180c3c8620003480010b80d41c0103404007100341c5010020301c1d60b841982d03108000c80c546007005d0400d030700b044403910f008107002c1410000d031108200720000403516140340c903c400c5c040c0e4500a09030b0456003814132071801800000618241c0101740c0821650311241090012901207801f445c0c0748100104800c030301c40584140c0400c8c8541104140c0039542a00d = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 939073776 1250 939072526 939072529
    0x2030f030f030a0b01140403050c120105060127050a0e0a0c0e09041e020a09150510020a0f0311120a020118110f0d080d06050a1707030b04080702040f0c0e 68
    0x900681041c02000c090410015003000019405109520300504182c3c10312101c1c251b1042d20303604540c0003258250300490f0069078074580007a0140b26068060000e029030f10300b14000820b152000740c0005002a01c00c883c00c05807201124880018090180035042c0042c0c0d201c44400c1d1000c4180c4440c46150700d08140115818816034421041c8c400240c1f15210030389540c0d80d01c50f00d5208403003004038003590740d008000c0140c2e04c0f000030000800b4039100c007088403031140d813070200d072a101c5034071146c0b148003d413200070855074010800840064221240e0444d03084142400c2d110804948036800c218001d110341d03100303207088a4006c1c043c1c3c0441a400bc000e042014001e41601c4a6011350140050181200440c0c46151000100c07991400103000c3c1e000c10049540e5581c600d4001c2c15000031403603152402030110307040000807040100780c4500ca0003240104407660755141c040354080a41315402e8080040e0038414a00304542d880ca81c00b900c1001903906803009040104444035280001451000d09021103 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 939075026 1250 939073776 939073783
    0x30209070f0e0120011d1203010305100b211c170a050a021312030e3a0510090215040501050319061a0904060605072001030e03041202030f 61
    0x200d41d4980d0b8100e48445001500d40744c580341c05101414100001c0c200e8484000e01499101c104440015104c0c0030055039458100410381104030500c42041c00104045180020022907510240034001000404100400c00c0780c0b420308042803280d4810340f1414030408000440f00f01c3c40c050b01260003c035000b00c45084820711101214070805450300300110740070381c0c40c170303070089400451000005103040400f40030807007174200070b1340f24a0105001403206000e1680055280714003c40850b068826021680c900d071004600ba6100c10031314980013410320041e0011764507102c1c04d0036005000c507a0310b602c0303850100014200f0b166040380210040404070012070400c1d030135141555016100c281c25075941c0409003640c03c500d0000445003d8860400044410a90000500c60001c85540c0c035550f00e0080300707000c2500d0260b44120300700541084a40301040140314a10031401240120821440000c00101c01a02440d0002e081078000010001030f881ca0102035100060300c02e50560340c904c10010001c0d40c4 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 939076276 1250 939075026 939075047
    0x50703030501090b060d0b03100e0a02031006050a03150212180d140a08091903121a0105070b15060f090103060b1204030804080d020a0305060f040908091003090f050703020907 77
    0x5c01c8034092080410340c0400d9000422802e8001d8103c52210f0240c0d800041500d16080104130541c102100001c02e41c10305128400c0401c008084c1400303014a0070002c103a94044078070010f80310740e12804007900600c019404840701481c190b00200114202406044408400c04841506604c59445101502d5000725072180e5800c2000141d2400c3c54210b240545000e00d004100600e03600a511555014201c02e10902d821036009685213001c008540340d107002280c040c1c04425204401c40790100d5011f030703400800c440880364007504081c40da494080e440d8000d194003080c9194000000318010800860040181c820050709903014418503a031040354020034403030f81030424010500721000038082070040705041e42043c0700b410054036050314600002c1c07ca802042d40000066115014410240303031100442e10030380002c440c100f0944010790f032812003600c41ca40003640104810798200310011b021303602032100c0700d420840000c405c00c02e904e031858032010360340000c900c5194850701007548544540480303030 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 939077526 1250 939076276 939076279
    0xc09020406081e092d01050a241a210703020a020c061e13090e03040509060102062406040f030506160c050a06200c06070806040e21040e07050703030501090b 69
    0x1030700880100c00030700034126100000001564405c608020034244500f034482c0070f1b1003500240c1100300f2000d18901c0074550814a00c14030808006104400e41d44200c0311455864046440d40e0f4461801c1e803507408501110080d601c24407460802c110950107400600311a8801d50a4510003016001080160b0140c03040c030041c0101e034401a0882036000c60004d000f6041e0808107040200d94503220719043d5500c050306a055a003001c6010815800e1200c023483d044902400545042e24140352044904070307a0309240150000d500200c588252604022600900f0201c012174800310349a04005584400aa0f000510240b000d80749060807446881c129850981c8036010304664501511010082d054060303500415003008419041d42c4100c0c4030080c52510400d8003d040705260500c3d01400940004000c68001e038103007030806450000104003280e50f80c4025680700e018a04148886d4028001c50300001030b19038078501071040715a00140a40a40c0b882954140320030780e01e424000341515035880069 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 939078776 1250 939077526 939077533
    0x12a020307081605040c2109061b0e09041b061d010e0604030f051504140d140405092505031006170106051c02030c0903060a0b011403040c09020406081e09 68
    0x1d01c003c2c1751540198900307418a1405091060300144810010440015410034403991344034503100300902406420f80a0f0304684104111140084000d842d481c3c40402c1c5900c0b42440d940010104141d4625400100f000c05501d40d141c940c13101c50182a03503514850005828610f07940a202e42d41c85807000040c583da026110030f08240c6581d89200c034603d5030101c206d0340d501551043c60054030204030620310840c010700040c503902c6032941c650703814038846c0140c0740100482c074032000fa0140c140c0b00485044550549a450b419070780c00030880914035101c01c103409446402c1c03a0107e560340e848006940258441e2600c050a2390340c0340800d882d10200c0542100c928403921004116850050001d0318002c18070400502581c02c0e0340b80c8680c22640110382079802e200707000c9140d801c00c0c1010401c0a500c400b40c207008025408001001814803240d1400c5c01003170400010008041008130b407901c00040c600d298040d52660b0311440050400041100d480405541440f81d82c8102c1494080081c010008040038 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 939080026 1250 939078776 939078779
    0x90703020c0f0f1b0312040303120e190204201606090605070215070f140315030a0b0a180c03060b0112060905010e16140c0102120c0d05090318010c02012a0203070816 73
    0x1e0b10100742080c2101b50092f910802085445010701180c02d04030701902003500302c0d003001d10401c4120b48001d81c4142c11120846820210910140301304d95050204540190800b008c80c50078034050004d618005224a00341b50510020540010701c250890540b20005801a952644104c60b0354540307000240008111000c01d60b13001d03001100454000e1030030580c185650002c000440d1400541520444100f00300c80c0421840100c1032142c0c00d01099aa42c088080d04025114500c0148032800003400c07140e41c502c000c0d020b03030b8001e501c1e0429a42101c44144805980c500c02032300208000d1046940c0c000e603842c002416507086031015201d0342050744601d000d660704a50550340d00d404c030140d042e41e44e65003082230b00c1c0103d0301300c946e881c4100801c081c034540c2d1b000d041c0c0445040d0307003001d0320700043c81d0f00034410383d00113030303041050600c58030428a400c110380b402c50300040716071440000b00c8a9941884406000000c06c8191006c240315000f81c0442d00c00310f039501405540e501c459071810b90300c0302c5181c10 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 939081276 1250 939080026 939080033
    0x102070623160c06151d100f23030705091602060a090305070f030e0604030b0117120a031a04020708190f140c150108100c05040302090703020c0f0f1b03120403 70
    0x8a5032403185901c500704607603210300154040b40c0e044100d0080d1b140209080000840035135004034060a2412903040034189018a40c0c01c007810346041281000c0c144035484291030710304000817070051400511662450404e0b11031420040455009400140034050010701c0e40031040c0a000f4407640d16503225032505940d9101c90300b5250741802e0840030891304020700382079551200040e00145000b1071451f00c29525006a22000c000c18418851458000c003a8441d04884075200340c0f009501039050201d5480c01004901d460420290b04007a402880401e6000500c01304038060b003e800c2d0701c541504400c0301e01c40429114180ca9255100000d4089480c2d401030200e010082c1003003240d46400ca4648038a40c06a002102e002600007a0150744050018005243e940c000c0903072548460030020318090540d0045010440c00401460525800007141c150469080000c101c0c00a440001e8580c82801c007004d40380c8586030064400040303039280d1024090b51401003080c021324650100200c1c42d1518642c0c = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 939082526 1250 939081276 939081281
    0x1a010e06040c1e02030d1b0818010e0a11040b1813031101051518070e0405060d06090503031f1d060a080703030504151704020f030102070623160c06 65
    0x3145481040741e0452003000b0b101c0f020038501d40d0500e06401841c2c44417010305658003242d00c03003400705e4a40310804c06003000464200001d15048181507a502120310f0303154074824050200700318400260303c5501656000e21004804140040408480601554544104000140f10f0348100000c00080d4640442e00003e005282030b01014841e05007500442200307045c0300d003120404c441d881c1581c0c3c40c1c2000c20300c0c0c52405000014030b48850104007581800c2c00f4000610100f8405101801242e80f0030207e549551481c4c074148103558440300510038500d442c170f030541c0c481e04161000060380400c01d800250600f40085c0c1407007076075044102c54404649000d1542640c41000d00040c6c2c018807d00d8002c03501800c14041000914065114103039034a00c0c10803921f100010b1440303150108800c15610403402c200103030425400c039404a40d04040c0000c4000000d009105008005208500d4078000100f120240342e072400c13040320249040380040d510781070000c021014078000c0c80002561501e24800280703095 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 939083776 1250 939082526 939082541
    0x90c01110c06031003121704021c140c010f030b03060609070c1202011b0306060f080c19020105060f0d05060117010207080d0f0e011e021c181a010e0604 67
    0x3401118108040c40c808504168410358184854086500050040c412107404d8960304a40518241004c6040701380074816040c00608000d11a02100c5a0b090304a0710b0220158a81a000724080b0303440000c0000a0b83d85120300ca4000340402c40c00b41d40300b17288600a10800d034420b00044d000d00f00703541c4d4034410052852001846e0000340000104c044000c100e5448411880b40c44907000013038030340c80740300f0154048102511380344209801e0041c180080d9a00c10341d441e0b006a024107051045c1d441d180402e010300d008000d41c2d03604104135001000e1300c496054000301c0c00741906031810000007003407509104203c2d000da0400340180c3e00c000010030607204103000028214200c00001070034010b6070b40d640304981d401510317020340d0301d502c400d08011603d145109112400c0d101d00020000e06880710b03c107011106200c4072101225070702003000490110246102000385171000001c100a408500a6440180c403050701940c1000e141d03c2c20480c1030001034003481c180c60ba00c0a8000299940e130b81040098880e8 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 939085026 1250 939083776 939083807
    0x6150a0501090311120a140c040219030f0b040f0b13060e1f05061c0f0e100207320f1f02390c03070b030604050603070b0d06060f08090c01 61
    0xc4170500c10349003040c409440e1a6100d804800c00308521111f429113400c603000403107842507104000e01d8480d01548103503074002c070090b81404250848200900c500030003030390011541160030b1100314074800c0c015074010002c414040324440090020710320364a0803203040340980b08a02100d41c020a420101c156407800040c06441c1e501141c0640312004100306400c25103501c40151824030500800c0d0090f0702801c0c4100d000203000b009080d0310b10341010b0356544003c0f401908581d00013141802d11840b141c0d0701000031011a500b020720580c24404000c00d6880c4c8810149502458485400089003c501c000c1d10403101500d0b100803a100104060003507201041c4040161000c0082101c05030700e40400c2c0ca0540080c6800509007041403000c070b41841c4070b4000051003a0070004061018640c3c1c0030030b8980285080d90000f54654403640401c1c07518a160304100d52012010480d03003070310009500000c00780d607040c5d581c03000d100380c0103030086e510000c041d02c2054007500200140046544902000c0c0001080c = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 939086276 1250 939085026 939085039
    0xf060e1e09030a181d01240e040c1103032a130302010818010e1c03110f1b070803180405070f03112208060633040b0c06150a0501090311 60
    0x17512103458120080100450180b54041da0041000403400d100501314140082c02440210007400c9004141440c0d06016922490340c4503400c81e00640b2504e1000f8200c2c5520086950742d08000e4005082102c4407404103402d403c0041d018503200d0380c258280d4103950180d071810301d84181940c0c010766110000601c0c20103811041a2031001d030410074010002d074aa10f03040940b004c020443c407043c6a075012904100241418040740d200c07a242501e0803a814024000505034961416007a10781901b801e1601603482e41c4107114000c5100c3c02c3c00b2000700b89004900c0c3c100c0755000c2050050005644048074a00042803004010008803402034119404950941140c146060180015800c02c180040f06005503201da0820034440355800700301260f00312000704d494050141da8204071441150000c5017100018850084010f54040b0031003e440c05401716805041c0c586030380340c190399a83c800c101d40040508460380d039076800904140031224161681030b580d0000907811619001507031640920b0060b00032a = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 939087526 1250 939086276 939086279
    0x9010f1802030408091e01080604020f041202040f0c1809140f060112150f3614040303090b16050a0509010c0f1a090c010c03030c030f060e1e09030a18 66
    0x107079200040900084c054204600c0d146c07207503000401d11600104000c2c040c900c10010b2480d0301d02d83c3d000780c5023120007814811712550514030204001d0710346048486441d90a1003030382589190443e1940716180b40004c1405051591102e01c901901d500a040c10144103141e800b2801c000342d00d4080952000042c10429000c1c580f80801c501160140210070429811101c410700c141c5c104413401800425290800c0b0030313039120000b40c41841440f400741e419601c03400303d41c5000301005140c106544004020405040524080c00d000d805880190411130750300400307600062017042c0c048085442d80841da5a4142407070041d0b40d095500fa80511010f40c140681e1171901e1000400c03070245e1880042c4141020902c101c109001c0d0800e04002078034100b4180c1002d000c1da811664000c945002041c4c241c500070450800709503041c2c004107100c6103030200b224182140490f9030f00403102400e0042e108641180300042c0f460302e5000c0000710540c0d034041c02d81c004100d0890041e11842c0c250102c10a000340c1d0300c6820307 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 939088776 1250 939087526 939087529
    0x110307200d0f1d1c0c030b0f1530010b0a0b0a091211060304030e090925030308130602090d051605010c320f0c09010f180203040809 58
    0xc82101d10002082515140d6000e5401540350711954004540080e010f2032401c00200d821002000103a2642c102514450074441d480118800440d040348010342c0700d041c84a0390305e10b605011504004207246c0301184800a081c80c92101c14000c0182143c0c0c561031550b04901c411500350407201041a640f1452001190395804185100410503040c0450b83e0304046c1e0005461a04a5448000707404d1400c48108003040030308400103003161084541940d42d076510b01c1e041e510540000c4001750414074910410040010000b82c40241c061441c413502c40e01421800103404d1442540001000506060082014005103134200c0419610403500941001d013628041071341800000c1301581c0c3c0e5480000800004007424803044040d00081c40c0c502c80c10746450b1501d1804000078141d280f00d9112944403040380102100d134510310003004005640c000c21003000800c2d5298450364280b4440c1c99440000202e4103602003221044812289014030180c140400e1000203410060056555010410424842c0d = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 939090026 1250 939088776 939088783
    0x121e010b030d08190216030c0302070e1503060c0405150f0c1515030304060c0f06060b0a09140406030f0b0403050d110a08160815150304030e100311030720 68
    0x4200d403d940721400c925050034414400d4803981d40c0803082c80d10410040d58081a202202031400b90181418801c6800c140303000c0b07103020000d9100070f54045082d802d100042c0c43e00d44195440f14412800c41e01c0310348035400f0390b9042d4800c5d840380a038051152460341d081c414510340900105028280c1c3c0e0703410030540507500c40c20310900c025450020030000040140c6102140b61580040100f503000754145030404001504103000010003407e00c103100c00c01e810412150b50094400b5100d8082619203500403600301800100d13450055040850880701d1059403030825104400849402490040040c0140d446c0d000c52804054004e408015041040d8032461aa500840500da094411070b00da503a803c07120000c200d0742c2e0243c810004c15604003035038522071340d00c1040d6940010303c0c24141c22060403c000003407030030200c03200d2480c041d503004070070001807541089400b1410902902c0800c05594208022000c50385900e08500840303030184013048080f4030420380c2d0050446103055506543c1e1a000c2101d29 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 939091276 1250 939090026 939090043
    0x50306011701020c06012c06010c110301091718010309330203010f171b09070201020403230d05070510111c090302070b0903100902271005121e010b03 66
    0x1d000d058401c50185103012507020440040c4207c06048241012070001304560030040b0050118070070541c0c00c080c50341e070a50100c06001c0d0301001c80004400ba07030040e200150040b03982c14154040c1d490344203010f54082d000740e0401644c80b0b0418003400c2050345249109802a00031040b10440d00c41484d00e6001d6a48000c0d8080c203210780901034101d1070030007000c140c40d07c940d10220403500318115030341e903680200d0a11001100212000c080039503031fa02c0100d009025a0340060210006501031410014031700030310786142c1111b003043d03421000d02018140d45a109041008040d0750221000060000039030303004228081c942807041307150000c848030f040000c003070307583d0f80c2e4409070b985610301e20401d0f804100d80d00051050105050400b522a000a03480b40c0c456000d0245c00b6454005a00031907942d00710000504ac408103410481c01d000001311600385004640c0302440c241c00d62300c08612031400021341380a048241005207280e80200750880d24440c440e09500103190f403190401d00103a50b082c4074641 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 939092526 1250 939091276 939091289
    0x916030b13170c0115062f0a11030601092a020c060a020115090e0709090f020a081f020f0412021f03020901180e0408130506070804060216050306011701020c0601 71
    0x1902c3e50810000d03035003140c0008a4613099080c1710b0031304100e5140c0211064880300c031606000000005841110b80e620300340c0405480c458050305800d202008502ca140c540300c0c540a40c210340c03c036031321905110115080c003004000c0a850b55942c8541c0c0c2e07003080d95203000807101841900d00c0c85103401d0205000da04608180c0015075162000c0e058103605503080d51004054458081c8a42c5002c001483e4842c1c20314021014020303122854142409400c0490010643e405440c8041c019503860200e52107100c6042007000300c20300f03451680e117680e02038001e0320744225071040d9141c5070500d0000d000c1c945002c004400c81e00000c2244100b49032030884502c10f0401c25035500c01507a07801140c4001449101003c40c2607076409071480090120000184080ea4031551000da5a0743d6440c043c0a0202c0d00101a80312030380c00b210000b82182004405005030048820030b4084407c2c00b04860031406007807100b40181c0e41c160340b02500400c6816540d103081a8030640da1800180740020003c55207045c20403d80021 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 939093776 1250 939092526 939092573
    0x40b090a08032701090215070318031406070203071a0411130b0330030c0c0102070c0306050a051b0a0e0402040f0609060c08031302010e03010c080403080916030b13 72
    0x150f004140010315044a00005000f04203400250380010b4108039058440301c150080403401104150041c403c4460501c982200d03012860742d80e00d420f602401c051b04d00020380b4042d04011404007030002007034800d07a40e48019020000340c428445007400e4100100103850060701110290815110a411100d10002807000810000715507402d00d841e20103075681c400005c0b00440c034051001040c0035000000400d80d8040b42e030f600c0d2178004601d4094043c81da515038165100041000030011041c0d51541140d204841c10b1045035541300740039044640884402151a55240c24400101ca280c0d000300244034580c10940c01014110011030102e030031503008104551000341c01032000369000b2001900810f40c074900071f142e5081c0340c1d5a83c01c0300d00002e0010f05000355128012411a80103182c000c03034036032000d8002c01020241080040203d10b05450580100c5c004901051400c200851488004540c51540a05007455a41da241d28500300030076480005401d0001040050030400c005000c0c40000e0301e98 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 939095026 1250 939093776 939093811
    0xd02071e06110403030219051203090a120309080a11010f0204030501050420060a030b01022e06060e180604060506070c030501141611070801020d0903120b0108040b090a0803 76
    0x101c00712041540900307407842c01400200006a800506001c0d14901c0135564240080c0516000c2e2900782030500200c00c0d00c42c0842081410b20002400c0c1c0e0341180035a000350382c089a10941a401c0745c082c0c2c48040c0410400b0001c00340c805005198031003050140d4000020340c8090340300040100d030403e8104417003d0b51100d052100744620040c4880d0004040750403035028841003070000d500d600c00d00807288181034441021a00580c02401020049402d81c04e07051058000d84081e200b1030100f08103111181e9192100110750184603034103c19051741d0240c4800301030344460080300c6850b48010070309503205440d080007042580710000038100c0300d07104000c6244a2401c514003242075a41e08013000c00c000f0941c504102c2c03090b002c4c0300340700f24507009420060b0b80d008400c40045e0403d01d058202070515030000803d0001e90381c0c5548540000750117076407921a8000b8102441d015110416440c81c00200d110300401c000c2001030801c00d8001c41150215203080301d90f82e46076141c035001201c0d040d54185201c0c40 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 939096276 1250 939095026 939095033
    0x3130507080d020d0e04060f2c100501081503072d030602091008040812061f020705101706041d070e1806131b050a0e09010c0f0203030c0d02071e 64
    0x18044941041100c003403100c50b0230030303824444004041c40381c07001e41360000c0c0c00d43c914102c9c0014280c01c2d5030400d03507920300b07189415060120602b400d4411180000d01c01000240c812602808a2441103c024064400035187c440e03401c01114136100880a1005c410074880340011021b0119002540301301c00241c2c03500b001c0c00401c201038908400c59024000a0401c010004800e40101c2d1420f0144030003050302a180c1901085480078a80345521241d40d1200008403002e400061000803074000b125039803801940e1040c1200c1c9000c1584980c0705200c410404500c05240540003101c0f21442d11000c0d20f1880c1c2d42e403c0f8203190010310b40c403000b2050b10540a00c40c001004500d42d1800040c114010000c0c0d04041c1c100301500c440260010307150240c60708507140c5000070203500e8001400b000300080074040d214280f4056030744051301d9000240d072178100d141c09014010a507000764909140c002d542140c0d640100343c0d0319540501548038000b44d0801032030300015901218203128065403c07034500701c0c0b021442d = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 939097526 1250 939096276 939096287
    0x18111207092a0c060903090308030406050f0702030c030d0b0607050d0306060e12030d1a03160e070e030706050904090c090207020301150b0901050f070507080303070e041103130507080d020d 83
    0x10840d4103902c40303411665103058121803684007659100c14005125880c604044400800e650401000040d0001c03d11052011503017100d80200801141885e80361145101a039aa200e03c26090305990010300110520040d42d41c0030104081c40a0700381d91034800039642d16801d00d420301070751030082907070b1754002d00082d5400308282100d0001603602034041c43c42445000c0c0d6030b0003030b00204208280c980540301c1646103070804140d0001c401070122460903c90b02495403152076180908051817458a0000d01c0685c4101c00400001c0700c0900901041e50a100040b1410740c4800e0409802c262544150000038104121560041c00c0b403040060300e824880c4109800c0d50000e56004d0035890b0900b6051185882444c100c0e01080c3c42400c08560311180144034078104c0c0503102c005000790092160005800c4400700095116071507658440d40451a4031080100322001000c41d08000f075820310014000c000c8820014119178001c000b25007050741da4011035458440003100080058100354200503000b50401c = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 939098776 1250 939097526 939097571
    0x90f030f19090506041509030602040f1409011505030901090c060804230606010c03090b040e0417040b0702010e010c0b090d180b030a090311060f18011811120709 71
    0x303242c405450352074100021143d01444c0141884d504207280f842104a0007621010019648500c1c199115969041031682c01a1030303201e00c2540c42200030b070780c000e240b8040340c81905851155100d034542c0c0c13040200071a00c42d0002440c03c5000e650719652400441c107204001c10041440b6a2590414605071404503540b03454000800c49000f0f01392181140d8100120f4115440f40b0203281803400320b1003038101243c081d64039a1041c151281e0014000c2030304010324800c03611a0303000e15a08409035100e078043d02c41c18810784c4030b5a11402406d000d5100190b20510440b07000400524040794241420f4640007090390040d6070f07604c0d207a84116485440184c000300f0040d607070911240320210302482c110004c0190322005190700251550703611004d04250140e800c020700043c212046030041c1c03034044000c1d40700e12826210805280081e40070030032441e005010319038050403107141c0c940310040259521040074038076441d1507510180f00d00180d14026030030000e0030000d0042500205220086450180013180d14 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 939100026 1250 939098776 939098827
    0xf040f060f02070303080c12040602090405060132190e0f030c010c0b1e070e010e0f0607030e0f13090b150114030717041209060305130b090f030f 64
    0x103030881000540100f210f0301280e03003501b00b640045d60b4080c0f01c00b941744900d00c154002050320405010900040e58042d214400041d24100201d0315000e00544240c82d441502c004548407504034400c440d00c105100100c032081ea248014184007111075045a030030310300c4a0f070000080d44100654500e18040c0c000701e80541054000d0001100020300003801401c00800c068030080a802c0810011444032002080003007038545085900d00f00b003000280048400b442c194005401030865000c14a40b03061000c100e0315000344803038940009a5400c0d00c1003003016007010352009580542608946992200100740c00c0030600019440003545015007c1410241c146007905c4101c00005440e40d0304500444030210150301c2d080e44030342c2d4032001103c0d80403040448001d0329003040140401c0085a150442541c0c0d015101c0301c24207921f0310f008500322001240c130408200600c3c10060082024280600c0c3c100061380c0560f0106101c00030000d180d0340c00f10412f10000c0c140011300c402045419a141c5c00c80010 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 939101276 1250 939100026 939100037
    0x3180f08120718030605040f02030a052b1b06061707091b051606060503070f15080910020903120708030f010b04081f092310020415030e030f0f040f06 66
    0x41004005030310f0b810300e001c0140303070940e00c0d0085414001070302c0d26003010036401000c885030340785140341c916150501461078503001c2d030010f4135503171001110400201700c1244a54a001c1a09440b03000501c0404010b07406503081a5548004a0700e881e44100030b14076804400001c184a51a020100c0111102034440894510500381040a07032070340703c1d0031502c06114107620142c0c03040044c207011000340020707407003142c6c9442800700014a81101c0303e0180200c408060004011280b40001618180000c903038000303160704200034442d800541540600380c070820143c00c441c0c0d20f10070b4400c0a072455005600c1689e0021021040106c49210444018058508035220700d052074540b070f825540e00d504030040d4200a05501542d2040c0c0350140c0d1051800d1600300c0c0c0c9864045503220010749014228514503c1a8091a11507121b40c1c2680c2c0201c40490385001e10104e90b040300f40904030000c0c10003002030b000074002041a80508041840603041c10040c031805070707540d189060f00780c0030300c0c54160340701005100 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 939102526 1250 939101276 939101297
    0x12070e03100b090f19020415140703170c0c011503050c030d0509010c0f06051302010219080706050901020f13412103120f010f0603180f081207 63
    0x3101c150703000341c00601000c0590241c1c5c03100c02c0e403101e02000310720071400f089202040024400b500425030250a01964a42030000700c0e420f802c292a6229070140070b8003145803442ca4405150303050007803136071010341d0f601220b0504010380111425140d0741ca82003040300000d21024000e01401380980e060303c0c0700444c02020301c10b0041001520600680d0001814408035400c0c09092200000011200b154403900400003868001110488414810340503030041c4a010003500000c0410080d0401142e00711030b01703605203d019610780c03018140041c5030701500e540a0081061841a100103490441d451040026003a0f082c94842c0c010401100b090402c00020b41c203280400f98070840070f000e031080c8903007c1d0b83c0f007a1f8048400f26000310980d0103403060501e8500004060200c010003c0c00060900100008540d02e650100140c140301c28050355000354041a010489a4042d90241c12160300b250803110600a80342c0b40c40174240c3c070a12050752500400503411003680c01c96006158042c0e00f038200f811644 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 939103776 1250 939102526 939102529
    0x215070c09050403050f1207090f0b04090207050a0215030f0a060e0a0f0902101206050f0108062701060f020c030a05030a0e060f04031103060a05062412070e03100b 72
    0x3440d081c441c070304031030340d0ba00c0128003030603c10400c0f141d54085a0203881c0d581c045504213080403220494050300020010384000c503941c0c0c0d055104000b02c1c0c100c85401c500341400c18004200940c4100011950b03485001240f82c01038a41d19500b80224208401c1c440d200d1412810300e510f00000240808041c6203484800d104100b210034000781c00207681d440c00100b15004520180003480d1f4114042d5201407031500c0c14040c59807225902c00d0180c01c00c0340c2803045584c2c0c1c800380140e4124140c22079010580c1480003c0c00d1f03040211800c648a4584500c115906480b00d2003032102400030380081c1c0c001500c90001e00c040340c0e01048020b11203003060b4000d00f80020b460315621b8a07801040c0c541001c00000013034040e180d0795104141c1e4902942584a0745d511542e070700c2e11061080b00004c040380240a0709c0001544150503200d824881c043c0900a104171407900e080840c005074050303e58032403011090105000e0383d6000305025110b40020f4032131542d40c0f00c9a0302014178220b10b80c1146681a42480c01c500000d = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 939105026 1250 939103776 939103793
    0x3070e1f050d030f0201021c06090621060207020d0c15170910020f0912010b0306090d080f180616030614061905220e0709120b090102090d060603021507 67
    0x183d405161480d048240444100d029110b4010040b150300b01a14a098041003940d02290803900400c00400c0341c90f9035200c24940e0f03940c0216003071031145861200540841c0783c0d50002c01556100030480e0454a81c60360391100450000e401c811000c6420600314001d2070342200032607400e058814044010703807401c42603140d070340c1d0a140e000d524529004165240c4400d000401d955203d100205201411960b842c0518002c02e001c8000078030a110700780120b8a5500d000c10300d200e183c051a42e611307900e030750b680e40d14400c202c101400c0b569070181c0060b00704819440c280305280c044c2c014402408043e49907004010f003602e51175046000c04049550045c1d62581c2e410046403403248500001c0c8481c0c0c0b442c1c070802d0f102030140740000c004a079401950700c41410104030450054904510f02002680c0b03804008840800c0540203c4141001c6003211001061900e80c8540c0e00c9440c08001510f0710400380c010880403071400ca8110f400c19245d64061085140040802010010219196040c104d5a8032640d04 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 939106276 1250 939105026 939105049
    0x5030d0c0302011b0206091606050f1e161a0903090906040603080f03180a0201050d0e0a3318170906072307050102030409020901090503070e1f05 64
    0xd0001900810302090300079040030503603240e801485401403802c503202a496140441e01a4454000e02c005025440e0b2900c0c04101505d82c2a40c42c075080950280e4404650360006d9000d132120454544a03181481c16040144488205070700812024840c03072400303400f03080d85507078450710001d180b20410540110000641c3c0f005001101d0fa00103d8484d5804100209110382000c1d010401c001210743e039000103040218003035a06035100203041c10b10040155160000804000c0c0000c500700300c0c0c1003c40700385400000c4000f0055041e100020341580c0c8050174007405400d00c03401d0b0007211001c81188020440105110010080140305280681070340201c12401c60340b00514000f00c140503000440c0c0d0b2582038030a255000b50800356904140e04000030382d000465210861005681c01641d49408082546011904103070001c0d81814180911000623400ca2003a150412200d040300040c1d0b59000c00192009004d015150849410034050041e056000e001012106911401040007079442c0c1c511b00d00d8 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 939107526 1250 939106276 939106303
    0x10020609120f09031509160308070303020325030b1003050c091c06090f0605060d2609060403060209040605010519030209040e0f0714012607030902030601081b09010503 74
    0x1592180b000c8100c2419000f982d0140d501881800490500c0075007940d0498044c1040d54221140d41205402500c0070003103901004041d1070382440428006406030b005140c000c40d000711b40304000d909600f404501842042e501c0310000b038841d09428990b0409800b082241001d600d03003070000d8074007030324120982d114a030710841c054102c20714090700400c40710440103100c591150040c09400254144651440f2000c1c9040e5401490403020881c18600031810105256200742c2825041e11030400c00b01c001c902200340072101d45c03820805405141e58401c020b2000d584928030050310781420805000854003160441814040200140003c44144050240315841c05142c00343c0c1c1c03030b0038110201c0e024100192100d0224403940d1070091401c2070100b90101070b11084c3c2415081d500b072080045514040d206c0105a0f0219002d02180005000e0040d256114009041c08540310120340d012a26144090b44143c0d030940110f96500204081c00d103030903100c0b0004594806255042c88000fa80300c900020940 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 939108776 1250 939107526 939107563
    0x10510050708030c2503020d0f1b0501091101091a070204060504060308120a0b06040303081803030f10052209020a090203010f1e0f151103030106050910020609 70
    0x94219611450440e8892948014410344030f0400601040361504002420121441300507264a410b0300c80701d00050132641c1660091540185584058600c40d10390850f820070410314504940b0050034140400b01001c1c414000020103d51609140000410b0f0f2071045040180a003030411005165890042861031140c0d55240c0d107030110310005c3c0c01000103a11854000b4100030002003400f0300c6d08d0240c802c0c1c482640021341d4a5581a40520890340450340c1160b000d107042c0000d2011a01c0b9440056000c0002200998850411050f2500d50740085502607455822001000103001d172814200d00100400d8450741002c0028000e0202034107003000070645000d40c0c860050040d035440601c0c04000300010340c0b00310f50302c1d610b0b0b4020010309007041c01760340850180c4000316420101c1c20101c0e601215084200c071140c00f420034a841180501d6542c501003048400d007036400080b0305c2400150f0003000070383c8a0a99445c03801d0180940f03801110005002e41d04540104010000007140c44241d882042841 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 939110026 1250 939108776 939108799
    0x1021203090c10050715140a02090402040306090c0f0e13110d060f0f0c0804020d06021b030a030c0f0302070b0708130c0e1005060c030a0c02130509060103020901090b06030105 77
    0x1e20b0000c0c0b500c8655406514080810351141d00000184003ca000b5400c1c0110b440c0000354030340c156801075814081354052400044e2400c0c825074050a14058001c1000d8641a584d884040076150300c144141c540b2954078070f080000c55080b030fa10400070180c44c100c8020a16018902c4d8520103170f8000041d2902c3c1c030b0591440300c25509d1004003040d4980c40881040318001c500c04140043c02c040c8140c020007450314054001c1c5500801c0d100c1c5c450782c0d0052071001d4044541da101d0019400c080000141d1200a42c080100f0110620290003410798590380041da008002200030403400318058250f05243c030400401001c58035406001d0340c046981d08004d6000d4603000c22201c0002e030810806026840e40340342c08510a0442007074980196200c0103002d4034152600d04000072442003c032404442d81c01004040c1186004503507840c0346500050810246500c8130000394152002280c8090054016000510861a2583d0040c0c09010ba0400030040e0140c8000440d41c14803060148a02c12020b0741c00 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 939111276 1250 939110026 939110041
    0x270609030a030f06080d030501060e01020a02030a060c0320090102010605090c03041209090608031201050114070b13020a0305010509010e030a020c0f030115060908010c050a050913090605090313050f01021203 91
    0x70450003085d17185c0c12610300d03541000300240144000e0141c500058051014001c00750b200150300c40e2841d4000700580907201d44d507610f0b40001d04252080c0304c18180c4541c90091200f2806181c8044481e00100046d0f4890014000908498007034010500c2404220f06024404400d44113582d402940010384180b905000d08003039920301e0041c0e0007841c641d402d0000100345050044050030380c4042c2c008141740d0360707600c0350010366041021204011a8010512950011038242280d2030340184d803407542c10058062a4000c41e590780500d420503070304c5070344404c00d000c11528240308000507200304034081c5043c0750603001c00940700c0215681030341c4a40088079400050341c3d400c2d400441101c00b040c00d600d10301683d0f1240070b010303410644103603980c0b5447c260078903100601810031500c1e150100d950300c600d010103410411100c121616070080002ea07840e128140003c4c007510805000d1140300c00219117a40900c14803181410468004601a10740300c81b141d805c99030002030381c2c0700344c1945100e0b2a80740e689414 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 939112526 1250 939111276 939111281
    0x41a1308120706060f03260403060c1d0405060a060e01050d09060914060405060c0c030d0603030306090614060403141c09170105070f0311040b03270609030a030f 71
    0x10444100e60040003226503800d041600280302c15841060284007855503054101208016440702814070b00b00369851501c44c50350341c00e10400c0111249102d5090548941321704085900c610784000c085003907500c0110010304444c20880040b401100e082c010792130000080340c0310320094805d60044c080d010003444080d038090740a45510740340c50b210800c103450136410071030013504003d0019544801c1c42c2200c281c1e01000410014803a030b4001d40108529141c0c1c0d01e0b070881c1a0b20002d070303000e5180030a020703031a50780c401d5000f11001140243e40c007180d00c81c01c0c1841801207800c1d5604c103181501c00c1140c98040d42d12001c1c103aa044a41000380c8404a00c2480d00c200d08001d1a0034921503034510202102029580001100c82030b00c02c01c3c5d4100001200180b0505d00b00c40301503d040d000f103a282904449814800c0e0044d8000e102e80d003c507070741807540d9504071341000d03001641c4902c4c100d2049040c800e10050000000012040c10000501c010705000150355100d1103806455401c050b04e13099000c0d401d6078980c = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 939113776 1250 939112526 939112529
    0x603010f09051b19120230010b010306050f09070e03030310090f0e150603100e030717090603011208190503070e040e0c01180806011e0803041a13 64
    0x40380502403029107241941d2520382012402201004600480c03199042003030443c41190009007040f8080c50501650301401c1007008000c91b401410f05000c3c494481c0345980c2e0b414403080c0c899000c1c0401184043c0300f0f080d03400c1c454250b0304140c03400300108500e50342c001d550000035005541c250820303100e0a908450003410b00f04015014480041030104100d42c85444404507900c001c010880803104019001c107550070720a001d6141e9224222078070090300c0c3c8608040d0421001003c5403002005658040181c07184d180340e03505a0b03000403959405000c9021807900014802c641154504810180050041d000602921003040c02040c034000400ca504000c84000320320075110065000c0c41c208004100c0da2089892100041e00703040549210b003010b02400c640d1000170380c060081194076400448a0b402103170003090106152810000307040d102400343c14043d1100c0f8261800d24200e100c0b520581e400254084003140d80208020054066080c200500480018900541d65041802d944c00c60442c036 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 939115026 1250 939113776 939113801
    0x20606030f281a0109060b04030807030f0e03010e0a0c150917010e0723030c0a150306090c11071508070f170106052d070809150c0d0e060c1005060301 66
    0x101c000b6810a0b03c2c00d081c050486039024010300804e134035803142c52a5401544001803034000240003c0d4006805201c4454a100e081d282c90080c0c0c0e00b04100203429151451780413640c5d500300b119401c0030302825100050180079242c19400d0b400c0380d0340c0001000c00c100343c0310305046001d07032642c0d140c41b07440290071400304d110852044600c0c00d5250003402c25100002080024488550710009216046c0800c0c5a4408000104042600b92600402d001d00340121000300c02016924007021030003000500c200150140299643c42540c414a100c0c5441c080f00d40e000141420307802401d00e008503600400f043e51141d6940b604101c01800d030182030318801e5440040400c011640380c00031803141d40c4107014042c1000e400e064628031070100d8641a41c185003054000001540c1080407501060382e440080409640140000e840e0540c21161480e4030f80106540c0155a00411500c10b1250b0f8000880c0d082184204c0d013a40c602400e2a2000303503200c08920304003200d980c072800004c1c150350707080d808030154101 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 939116276 1250 939115026 939115043
    0x6050105090a303014030c0d060902030f060136180903030621060b061b0606010e0109050306040b04030302040503030706020c10110d09080403020619020606030f28 72
    0x105031030000302000d036100d00241031144024601030f64804030b0714807499284035500d90303a007000e40c48811401a1b9000510408001a04100c1d00152202e0380c8507140041450b03641c0142c9900385403c03030300805000a4007090400590941442c20300f06041c2c0e048428140c601203002c0c5811180542c403003034100300c1c1d0021030304c00000c41c60708050500e160000b00740103120741c3d0300300503140d201c42c800d103030309010210342c0310040c0314110800d40011844d900001c01440e0040030942010b034418400c044e24002c0c010300c00c055410440c1442001c2d42c01001e0244014005d00345041d945041030007007075803004000d00c0503084110540101c0e051501070703030444000d0305002c2c0940340c1d1946a8200b83e40a948603c2c02400c20b4421500c000c40000400c0c0b0541003114030400c0040d2400546a121502400c540c81c001c1e209540f00b00000030043e41c850004000b404100b43c0e81c8003840031600070190420300c2c002c0c0300700e0007604040540b039030801c0701040501c50284180314001c80b01103922500f00e8a07108541000700b1419 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 939117526 1250 939116276 939116369
    0x121a011a0d0b12061b0406020d050f0c060c12011d07080421020f300c010608070905160e091909050a0609051618020703050d05010b040906050105090a 66
    0x14400b0480905c9907020318500405801040c0d00c6002c0c0344213a204090058200d2003046413450b11030001020414656401c1c03500f0420350700b21082c1030003410b8403c02d5903880005a503852030098103481c91b0050104840413403051140705402810301a0013818182044001400582040f401a560264400170316030300851501e850b85001c0e5803103800703100c100c40a00c140d401d0510711040c9581210403039110070b46106a06421141e8001243d0050b4421800d10b5403030704408102d15604001c080c00424a108010409040c040da1034070b0324084e52007500040000007110403d598403440d903081c0d04110034222244000034424200401860b0a0f40700038068003886040105122994101c0c0040c14055419161007101d491065441103516204030302d075914032540b04601011103607000c0c2c9180790003410b00300c1c50603c6c03454154007290000d81009441c80c40100b410f0100106c00d1180f80c000e40001e0a11031301e41968400001c00481039071080603440c501c150031a800544207050786c02c042c040442194040d49 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 939118776 1250 939117526 939117559
    0x161211070801051b16020609010c060c0e1c050d080615030103060507030c0c051f0f0c20120904050601090b070303060503010c2c19121a011a0d0b 64
    0x280f006580400e202012030300c803841000145012034090010114088100c130701c69501380103403074210a05a0341401000018140403429034012040e21040907554020140840c0c1d041252115410504e80b6560304400440303c0042d01c00181010b40d0030081c1400c000507648c4100107080f038800c0651050310300f0f00100000080100a4010b607004035110f80f800c1c4070018a0160441d29249111005800c40c0d01011200540e405001e02101c40c0301500301000c00c8040580000a0076115540020f074000703040c60307086109080000070908440141d11000d8a0301d0308606801b041e80380210b0984c2c0740720342c1e07555002c100540c1c01880807500501c1724070013180d02c80300f0a003405402411184210340c040d500b0008000c100c503102c0d09000080c4482241903c5400c2e500005181309080b070003032180d4004507002001d00020503c2c5035854000c107a03107000d690001402c1d00c1c1000480c22003107141111282c6d40b1380180302115108100e40c07503070303207039100c0310781d1282e82e04075a00c0058018017044903044600e070550310301381 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 939120026 1250 939118776 939118781
    0x8070902180405060a170a0c0312300e0c042a0c12030903300f05040206070b0907230405070c052a060a02030405030d0203161211070801 60
    0x1c1c0300c050804541c00d4400420b2109940c0704560700f5501c102544e10130701c000418000107200000b2400304441c4420705903624031034186145e8200b65030722005414039081695002801c11091000c1e0503400707001e1360402501c0c002e450020b11300c0d40b0382207445000c2c0b440a01410010903102c2500200244000a0030400d4108103442d00100b901c0c00000303070901d0a55042c02140c90b0b4000c194014510303c180c00030f03800c08400401904c5000c030204050420b43c86854042c40c0c1050046655031509041c1c003840b1b01e180c1d4070403210566409141e19041100f0440581d4030801529055500840030131075a0340c811140d40d0510050b500a908500a12a42051441c0b81d11880383c9010f18159403c10150320303441001d407004c15030810014815403018000510f1848a41020004040361100a0201150703030030000f142900b0a02c2c510300180d101203400c02044c5000c00c024803000307005001441c03038265043e10707800703800030b4005c0042c10fa90b41c03090500c400c45203c0c0e0343d0f0101300142502600e80654030b4403044c601 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 939121276 1250 939120026 939120037
    0x1d060c071b090b12030406020303040b0924060307050f03102003010305010b131406061c0207060203060a120807080f040816180b0603180c03070306150b03011d0a020408070902 77
    0x2104d01c06000307410081c0000c2194190744507500103500f156901d03500d0944050000b003101c0d030766000c0c03540c01c41c4051070130b26404034800660303c008200d1484c2a0080c14540015544054810101c80700704000e1074801050f40c2c0b401e24004040440c54440343c047d01121403a2200000211041c000000414000194050740050004454030b2640289202140b016110903140007030109000720701050030b600c0c042d8000e04c0000405003d00d00381c0140d03114044201e0308004001d85002ea000003c101b114600012000090701031140c454890b80786684980141d0701078a84000e2660300d0020f1485182c66180e029140104030400c2200c40340100c0708031400d03034030816118000010402180322040300015002e0001e0038034000d004182159602056003c06a174042e024101c0c1e801600d00c0c81003948c074188004005940128404220640007a0802802c0491039000c401c41b28000d00060092101c2d040003032500c015480840d4180740c580d260703020001d114582c0484004c2c407071950300040a2186401521 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 939122526 1250 939121276 939121279
    0x1903090b19110405010f0f2f0622030302030603070e18070506030108030a080a0f0212041e0b0f04051006080706030e07050913060f15091d060c071b090b 67
    0x125041c844024103460141c1d0044e1800f0401450200c00824030400340002005814030705076200311010541c01006401c180c1480c03200c03a4048000704440b607000c104980c0c004084441c0e100701100420900701c6502c0c0708800007002c01d600080402e4070340c1d40030000000588444000304409050072001c02071198408d142c0e00707046004100c00002d0b54500b0400341c038101c0304888041c505d00400c1d60740c12510203400601b8464610b070fa502e8034054111407840030305000151000340703010714100b608114024101785000b2101c0e0303c03600e0700840e0001304034010b03040d000182e104500219031110f1130058280400300d000002c0712071804d03074005079070540058000115107540d10100410407280c52101e40321a100d0154641000d010004614407551100d00c03200d003903014840c000303000000d900b020f005448444110426801040d2000c0c42012064451031302c3e6000e102c0b00e103210722603400320616118034000b003900442050100d40031080c008014810036281d01880141c00c542c0c0d403503e68a0008050510340745 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 939123776 1250 939122526 939122531
    0x50606010201270812040f0312020301061e020c0d5708010e01020405040c0c0209060f0f1206010608060901030c1a070602070303050f1003081903090b19 67
    0x114a540107100c2c111001142ea60000c0011105030101c0909014022044a4806041121a2441c961003030414002e03481928001d24010080c100104020106c92205110318070410041240b56000380c10480c40324062180c4001000800e0402d900741200142c2e01a0050150002c0b501005101c00814150a105013043c122521016145400e00c0c0070701e104013003a044074a030401d14001c0c441d858280107904082c55034803c01c0d4640d0320f81401d6400a21036611240e40100c0c0038042c17840d11f40522189a8402c0c030340701e02400071580014400c0700000e014103001e064855644545600d4040514500c09001781000460003521307841155105024840c410024506501164851500e079000034100c9804c0b104c25940242007100701504150301042a0716958410010840021107d002605c0418066100081c40d8680001110554400100304500030310b050f450900000744000281c4070707140003402002c17402513902c0400354014168140080c2031504100d0402c40b0120119034403550340348403800305 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 939125026 1250 939123776 939123781
    0x30d0e03070b0c0615031903050c010c0e0d0609080409091506140603011403030d0e161418060409050703052803081801060b0c160e01080619060302040203130506 71
    0x21032070030f01940000580316081078000c101d84080e900007404a80c038005060f03458110304403a03d08283c1000e45c00403008103a0104600b019a0360030303c00e4070b20104041c1000045690038000145403c0341c148001418070356161001824046868195006440403280800c5030950350b003046181a000e8020308456142084030220703603008266610301d1640c40107815507040d40d080c0140000900c00e45068030782c040c8018440786803400f00710300038007010071082c0e0050310881c2e4400d803085440c0d00341600440107190301c100c2a4090b41c0c96100445040206480350075142d5110000090098010148050502c0c071614001000340320002c9240c9009042204c1040340c6a07416410301c000462800d04040d010581c1c8000080e00490400f92070310200c0036000000403180e48a880f002190f802030403c42c1d5460340801d081000f41020414001d010304400304450032158075044215641b91401090f00541759443c04544076600f100717401500103907600031b01c150744924180658021b460b1a2440640d824444c0401 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 939126276 1250 939125026 939125039
    0x14010c050c280f03080f030a140403050c0d0212040b0a0e0d11030d0c11010c021801061e022b180e073e0a1703010603050c0a0f0e0d02030d0e0307 64
    0x3641c004a035170040c3c00d5420704803e100c600030b550700300510241a890b03c81c103601e002d101980740f070148a58400e4070741c0368842c1070005d9501d00d0020701d40e91403030666200c004003601140540c800c0d201220803401b0400c0d6a20410035080300d44120261507182c00141a040c0300e0200000c4858540c40c00760150100c4004407a80c02e0300301e0b150381c804032010b0108200408425800d503c9180035145d01030014241e01880050810b11358403980707090703004d4400524001c01c08100c449015034160070700441303480104140c0a03540e86160b00400380e0400c0f07901b01e5045828101da140d02407140c0c400c0d40f040c02d200d8002069500c5006041500c030499407100004ca00039982200b01c0b800c00030f104098518880441582181114008540c03500c43c0c0c0800340318401c010301c0500140202c050030140d406410030311500e0b035240c000e0190a548000d01200780b87d92092084d000603640c81805400303c0304003441c20720301c440e8203140820a48610440060741502507418068580b5820001c4469a00c03001c0e01241c054659646 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 939127526 1250 939126276 939126299
    0x150f0607260304030e2718190209060d03140a090501182412090309050f03070e070e04060f080102180402191d0a12030f0914010c050c28 60
    0xc43c003c0c041000c10075070340c14508000b40002201c002d9401c0e07a40c841e40210f007201c50744000c101e414004040c40390890a030003110502c42d442c01441c0b842980c401d40000e59000881c8104000e2041d03000e003030b02800f00803e040c89844006940550065100d0350307440f0300d1200400d103001900461307001c107943c0c000c4180d5403015010002c00302e844907902072000c031155403034a00c1c0400d000250079003044044108400c0c814040d1290014480c441c3e15100300051034001400140708507241290b10a80000030100921241020103a510000c140340c1241c0c1c00306200002402064550040382e40c6891000c1c2c08601e03d00154000c6c2200d014171040600a14400d00c200400d92190410717810807038007890104000d80b8010483c200300700d0503036040140c0301c0d8402ca000c04d210003c0341e03100c100005800c0344c0c280180341e08600030a1042c0706900d01280042d0421818103050251100e0890400040c80e000109011090205800345600113200114003100001c1c3e500206920003541d014440400d10002024140740 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 939128776 1250 939127526 939127531
    0x14090106050316090b04090204110717041a03090312041101110a030f0c1e030f120b150d0e0106081e0708060a020f0c06040321050f150f06072603 64
    0xb180940076800d000313000b00035212a01416421a4031400f001c80141e403240601c1e15010b14120880e40c660045041020210484012041d0800ca0400082c400c002e0042c902003400082c0b8924540e5a440d9110201e10b5032261740307505800c0824900c00d2000b08401603c0004c0020002d0341c0b000202a030b070151850f241c181c81c40006010400c000710107030495004e4500515403500030032800d074403036414480e001d10400c5100002c40000c0d02c0c050408180e6500f20585044000d00c5800411456010760f0100d0090500050701d02c08000b00400d01640300041a000038100002c0003009104a0b07507250074156031001a0010404003076212072701540840b000244040444500720004c00301603c0b01d104040096009030408110f202d805c01010256010400c4502d01940c42560b40c40d45d51100000f00c0d240314000c03c90340c1983d5508101c107000d43ea1580d84071081e0400406c07540940101d00b00f20000f000381164666007900a5408034055061204e4840e0b0246155200c0051404803421040d00c1784051104 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 939130026 1250 939128776 939128803
    0x6090212070806120307050102030f1b04050103090804080a050c150a08011208040f1502120903060a050c13060509030105090a0201050d24030f03270315020904140901060503 76
    0x9030310004903600d100e9034a05400820240c40400d41c0320304030a800b42142d11800342a180380e9000030a000d400114100100d034000d8118000c141c0f02c2c240c200000b41c151040d03201c0e0b581095200e00001c018042c0f2901194000c02a1604940c2107600364904030740c40341c14486000b44541e141c003042c10748440c4040e049400b03541096459105aa09001d0710150b021078150007500d0000c0b00303220200360100e0240c14100501040c19100f0541215120b00130300e0685041c100040c2030405012041c85a10005011038001c007070001c010403907540d43c0099245030702492f8070b007089890044000040040c1c0100040c0035440381a0b000303010039a10a4007883d03591081e02d4000380040c2007080582c410307113203980c4000c1d0b2488101e54202c0340500303905065403402480d40c100782c03036418001d42038104064201c02e1200700500e90f0b00b900210720b616400b91441c5080c071b6100c06881100303d040751899841c5684e04445000d68010400c00c080d034172000400260071300072900b00301743d076107070100205452600203082c6281040703 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 939131276 1250 939130026 939130057
    0xd050d231b210405010b0436030806062b0b090a0501030506040b040c081509012406030c030608160e0c031b211906050f060d09030512010f0306060902 66
    0x14400100c06070b007030010030076129556603680d40c1d101695039001e40d1101921209003144030b68024048070807004010510303040780040c44c800d40000070780c20072100c661000302200c04a80314114680c01c4124500130f004281c1400b04e0300668000300c095181d0001d0309882050710b81010b66070b03850b1100c2044410a001c082c0c1603078440310004000440c50103000354801d00c1816801c52440d03490900900c5d2002c100304d100c0b50101d9070000c21203180001d2103000d07880d000071100c2d0350400000e070080900c07000c1c003401008100b685804528141d01d0090f00010000d010b2001103551280003d129000340650348d0040c1226200c240b00801c0794001c3e20030a59010b81c800162110341e407600c144040300f450384000300641d14070a24020f404409030020030300a2040291036260007819071079442044c00c841164000c1407013040254030741400307506c1e404140c1c0d403841c00c840800103d05c012400c0a5800f4001c0520355003e50102900210310300328075401810459108041c04c2c0603d44e110401a400c1e07009011100f5425007 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 939132526 1250 939131276 939131317
    0x60403031b052514070f14030a2102030c0f0604170a08061c050105041406090d020a151b05040504060906030f0215190903020901060f020d050d231b 65
    0x10007200701d100c071441c4036084071304440030784840440c00d11400d5809141c80e883d44140800c407800c060302c030a0703840c42c000714080c00340d407400e9644800c02080c582507500e012159510b50300101c2d070300030422255a000c145040340c4818614a80d00c95882d00211030445101030018011b100002410b819103481e520142c40d0b10b81c4668561040c0a00024504100d900500b5a01c43c0600402c2c400e100c1c1c3d60185002c2c0101e10483c18403606654608500589002640d6000480d896400b44d07004c07400c0c040099001700d0408100d00c5e60050301d80a801114490300d07160301c1c1880c00304001c681104c001c0007151010341d01880a00e58440c41c3d4411140548005030560030412900c000514144090214040000c0c146c94203041101e81900040301500303214402081040c1c4c014010361602103803031401050107190444880c4501e200080d110b11401301180140007021500454810352038108001d8028101c24a4101f031612904103103504d502034030521503c9500724003440c0260322642c1119404418044088031a5 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 939133776 1250 939132526 939132577
    0x40519051e060d0c1407392106050c03040615050310112109100b150c1501180e0f03070803040f020310060e180d12020913021e1603030518060403031b05 67
    0xd1820342c00d2090180c0352881200001272080c46040c3c05100da070750100e80c0383d00d0540340c24012101428a0824441c8030004108020b98002400894880c01040042880150004400014020065990301154100c02c0071810b00c243c500c2038900c1030b00c0810031581c0c2c0c503118601c031404403420b1007600360b00807106584101c0c201d110003000b060380c0030284d0101d4555403c00719480f05100000e80000d24103541040f030519000c40d046c01808403500e104c201818900c0c04d00e040c165580d01c5103031001010200c0220001c1c0a0200d95440c11421a802406075040512100c2400380104400d0044242c000c9644002c2200aa00d04d04980d40a00044000f041285a208415501d010050605035010385d002c001d901c1050711188010010100503001c0540c0300c20034180100c42207141da054601c080d00082c040a03900d8110400f1003100300e505424001140d4440070b219040c52640c45041300401c3c032951003440704050307140e44190000205101d01c840c03940050503007128103100d01c8101a0002c8400403c20800c4c = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 939135026 1250 939133776 939133799
    0x60610110f0309030631150f0e0c0108010f05010c0c0801060902031e06030d120e0328020a0f12120e0d03111309020d02040519051e060d0c140739 64
    0x3103001fa51078140240750306401c02c0695a08400200d034054941007001d0000f0810055900c618500b420804040d60408030f5103104484a40300712410020082c0c00d500a0140880c0240f024100650003407040d0760321424072074060341c0156207050904564a00040000c6a090f202501542e0300030040c1120781c0035141d08a512a51030400610b120f81d40343c1c01d201c0030307010410003001c031203a05040c1c0700b00d194440c403003020a07250007500120035074010710245c40020300020703815206243e12015540700c441007081c04403202e0710b4011890241a00d8032070b0b92101400005000803110445075014413000c8041c148031503460142c1c0745444100205142d0a01c5250040d40240001142a0800500300b590b900001281004810350528103ca1156000d0203103080c6240504810841d4810084000b88510089490361144080055085544945050149202d00211000155800c600c19150280c0f0300741007d4a00b014002038001c40c08602c0c0d03104462603131411048080c400c113000714a141d45400070b0084c0 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 939136276 1250 939135026 939135121
    0x1a0604090320030412050a020a0b0301052116030807050c0604050609120f0a142b03050411040f0209011b03050a11070308070803090c0111060610110f03090306 70
    0x107042c0070078813010440c1032580031034459190041c2d0007040707041c815006112240b4103c0c1c0084070030100c10001031001e40c5030710084400781d58480d5081105016804011810404856180007103010380c42e2001061280c290080c201240c0500c042e03480e02c140c0e41c400c0002c5032140b48609604440d05004068803840c2c00b504460115120405950003070510504c0387d414040301c003804844c024000c1401080b184000c101d16408030300c10210122840c5080181107103140014a81802010b884400142c02c1041c2c6c9094180d032890b020704140900200041c41c103000e03420458a0500103554440e09005c103602290f025641541c0545406182104041c0c0807510b00540e030782002e003203201d01c1c0341c0000040c00c168010010f0900a502198890428640c0f090400075001c8480d41000000f050025401c903000c40d03144d401c44811174074003030070f01c0000000f555903404040603100b95004481021001c044003000914501108905503842962a07081912620b01238114901e2540540b810401200b00021040107 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 939137526 1250 939136276 939136337
    0x61e0301020906221403120a02010b1909111303060c02070b0f0301060905060316050c070801020f040501080c0f0d02070f020d06060305071d060f18041a06040903 71
    0x180b500080c5800700c2c246034040c0b014001c030f80349a0304d0500b40315100c041c006405460882022a20031202c13000003030b0b951410340102408035000045002c100e5000358840440d414000c0c212820b005e1710310280130180800f0380300d00c80e0002e0a040c01703040d500b9255806c40f0320903c00010019040303811034549a0080ca100e10405043d4480c6c00310205010315040e005c0c04440e600b02c070b0f0f03082c1e0b69030418000602c070080c0e43d407000c0e0003000280284a060314038643c03d503044101915085466050001003246488402da0002010b944000351201400307000400170300644070700381c0f242e40b00794444100c1e0a0301ca100b20f05600300d5007401484112100c50154009203050790180705001031000325a00029505001310310702b02d802c40c0e40c564040082140510014000300551014006013680090303085c0c242a82c000d000c1c0388100500e41030040c1541e52043c81c0c4020b42c44200c08501680340c00c0c41c01400240759148010300b001c403a14006070703540c50503009081c060341c5c0c550380f040c0c0100d03040700201c8210203044040f103 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 939138776 1250 939137526 939137531
    0x115080c0c070e010e040210110a122714090603031801091706070906050a1b050f01060e15040b0f040513060e0102310b0a021204180f05061e0301 64
    0x10100c082c0f464140c06890035072000d0700caa0909204000c50200b81e0340c08403050180c2e03003030446010358000c5100241580c20000c22454210000421a61911407264404445011582040d8085148000c0e242a548003200b010407c00c250001c02603d241c084130995419807007040b0380e00d0500c500c2d880c2c4c0d4402c16410b040c400e200989900300024804005010f19800b0741c850810885500e6005920750020001c3e424050f103041c0721003400404500030301c1441c80d1402c14451780785081100800000c030080c0f4086008124907500ca4510154001c015508825000402a0000054602840b0320414258000c1a0b00360400b50181444080c11006061b08075010440c42c80c0b80100d1301070b01070b1041d03110141e000182e0320032842c1414500002c449004151520000c3c2c410081314441561074010380d0b03c818561622141d5018080b490300454a03a1185914000300c4d00050309119940101020914140c0a01030f41101000500480c0c404862042d405102c0c0542900c1210074007441040005014002 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 939140026 1250 939138776 939138779
    0x40b1b0109290c300403260f0103031b0204060e010504060e040b060d080f0a0e2d150405150711030f0607030506060922050115080c0c07 60
    0x2060869458180645281c0c402c5a1103400803040507080c1c01048030a5249003410342070903070502d0200e005400d4400300000c0d2031082c0101290030300c1c1c981051101001180e0900307241900e4000c0c510508070840c46030010411002900500f0180e005c0c3d88260003074102d00b1016131840e2000ca89112070350b60121460f01280c0320400150b02c03903006443c090110f25003c0c880652408052000310b41e8035038040c05240e100041400300194a101d91190420004c43d22002c145115003403808052040344180b00382c9000010301500e0142d040111031078000400c82e07c1c00b202c0030f4000c0300002d083d60000704000280080d00c4808046141071017019441c44d400140c030b2800c29480b400031070003074044402e940180440204508040000c2010b1802c0303030a2050717010740500180e1075035260b9a090041c04160906490300000340154683d1800c1e115021001000703640400f0100c10750300d01600402e0b444011040c10710002045940c2002e0340341102182a0b0b81c0c250450340d41e040d100b0310503041109010040d0040000 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 939141276 1250 939140026 939140077
    0x40b0c1b0d0903050715271701060306060b0c0316031e020f010501060e010801060f0302090d1a0f130b0c070b010816140a0902030a0605121605030111040b 68
    0x5004075021941d19429200c9003503041c103074502071056000c044101d030420b4110b1200b0703a003d00000b001c6814041406804103115528140b000c0d0b0b10f0b00a5034505004a0f10fa05001ca01500280222401050100b0031301e0307101d610a103414401d080e081c00d010b510410060304540f1200750b0442880d4000d240c0103011400601268043d800c06008083c01640800303107030503041c0f07800e01c602801800e2606200c810b0300c0f02000041c0c40d15005124a405120300301040d00300d03180c003d8045480c1114001c1c03210103090b0310f44c580b28000c041e103403401c55a0801040006a4a0000c00002c00c3c0140350700301110880d40ca6550b0b4060700540b0042900f001030b88240f24650024840c1034000d400307410030001400400c0318081070101860555400f00c12215410030300c0180356141c0d00c4048081e07913031405002d83c2d266160300000011f00050b0b401309400c03040c008082414100040340c030291428071410001c1d641d07552030702050700342c45050142c041c0a403410042000f40030a000000c12001c0d00044000c040d6400483c03 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 939142526 1250 939141276 939141283
    0x5091309021908010b03031e0c0a06020a08090d0e0a120218420409030c0b090303100b07051b01171501140a020604170d1d070e040b0c1b 60
    0x105880440d41d0b5020090000220a0291148580c0d0030380c001c2d41032002c00d01800510000c415101c030341d00e01c40051025001e00090110042c40d035007001b010f6648183c030120090101400b01c0b00b015080c040e420f1b1241c1c000d031040340b44901c4108024014a4070a080142324140c1900d081e40032039000e0340309502d907505070130040d40b21445642c00d000c58941010f00c000301c0700201c011160b0f48200c806948107480c642c48c04d000c02680c2c3c0482c1c0982c0c00094020041c98291080c821041d40a054011204100a600000040254850102403680398009030781c620006000b4004c84000921541150152a0340c4a5001c00b220750b0041c01498a0b03c40c5010300c1c031540c80030420544007401ca035004800d8000f22135800c10100c400039244642c01e40e00d00014100c0003074a846000d80001d054141031098070b45011143c0090350b01149103e00100710a00d4400001c81007200741d01207075245400b40c0e0b40d00042ca5542d52010724819a0071244850f1503580e004c3c2d45c025558090f8070440752840000b228403900e0700041 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 939143776 1250 939142526 939142549
    0x6030f05010f1407080112020d02030318040c0e01091e0b070f020f0d020d35030402190521100608060402040b0406060c03050f0d1104090507020c010509130902 70
    0x21000015504002e00044065600f034034a400380501d01e400620001c01d50000d003085c110740d104400d169907004a44009142d06a401e18060361611001c60182c15400b0a070512204607013049804010814441c1020354911070003060b01c601240020701e08011402ca0120704210300d01d001c6900c102615141d90b07141495400150080c2d0300a0021507003501182014100d81d80300340c0040b03030102d08003480341e4001075401d07144500041206542100350544249400b880c040500c0440d010007094074107140c03200240d900f00b107500383e04c1401003010420350300910b420008140c410191031421743d0255144610917510058007500c1c01d6118035100e00280010511030300000c1d011080c0600090b0406004120a03034904aa4981c0300c0c6240c00c408100d607030340240c951502d4a40c582010340d100d0700ea21100c1d803c5400394590f5031405034105034000011201c4000204240c5c0c01c03004003040b0903115540101e0f0758080a01e20503000c50ba003000300c0ea04d54035001d140503812100480011807020f01c1d80d130102d015071003c0c = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 939145026 1250 939143776 939143783
    0xb2203050a141c0c020f0f0a03090b0a020c100509060706050105011205010e0105040e01061e06120606020c040f0f1e0f0203150103020304050a0b010f03030906020606030d05090406030f 81
    0x40341e01ca1085500c82029000450059016400c11502952808185450072003110b01190340d4850a07540d14001d00c1030100100810302030b5108141080d602da80c480d140100308600240c132412001c01c024146600392840303030304182e009100b031610b91f40034003c81810200300d0205105081c00b50400e02e94600004020940c8035034804180341d4584000984514501015502540d081400502403074006016590440c0c008841c04030354141d44054603801002c1da80c114040100180a20980d2100c20090715003c6030340955800c1801144260b0a40c1200e0042c001c10006800000082c401894640c000001e80030300c4003000100b1b29070302131125048400c900741024600d01c9480c3c01d034104103d40e00c00d03410341d805040001e614528120320301c2c2c03581400400c9414103250f80400408c0c00c1c007900b00003440b04950b0000804525503190038581c00f0754085488224006104003002158546c404283c4074001d04000e0b00410300c410829100b0b0398960000c51880d5003056031a0b030b00101103000c035040741201c03502 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 939146276 1250 939145026 939145037
    0x30d11071a130f09110703020615060d02180f060423181f060f02060103060f0e0d0c0b010614070f170a09080d02071d0a0f05071d0306130b2203 63
    0x44c100034070064034040d041031400d402c011b04c21200071940105019a00c549a56604601d1001d4103000581c1c5004110120b21214804140c105451f02449500440c0a400300c03901c00c0502c0c2c0500804c00c04d40700d180034840308020014050720a0850038580e200403424004c10560020082c8014620380010841e1061070400303901c0c1c04518500d442c40f407228040d080d14038082001c1243d134880603590780018072000303103516600c150205500015901c90703541050325200351031542e141880c0c002e2034211602d10588818000c4030000032030130702644001c40240302000c421410100c280c3c41d50942c45264802c152824104d40781222038002041d03006080417501341c2c96070b889203030805a0152a241e1507d4007070040d0750007000180001c075006a85000000034100900d001541c4001000b006811038075200d01a0508050a20100c1504081c00c0409001d08800c40380080010004140c1d0f85c010a130303450109600c0304110040842c44100340107130300288044210350340640c840c140c14503840a410095002a0703 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 939147526 1250 939146276 939146279
    0x20a020d11030301081504050a081c0629030402011707050d1508031c0b040203070e100903210c0803040507080f01050105221e0b030d11071a130f 64
    0x541010700d148034510400000e500b03641c10403544d40c2d940c0c17500c03403030228095280c2d40c0060200314080160000035540000c4080d21043c80c1000c8080140321201c050b0409410044045030590040100b40760408201c3e4140f203240d0706820b0b0300540e551000e00107074100510800740b016030441c2d0045040c003419803a9201c0c1d1341e840101521404403400208e154928100820b803c1250400c00030035903034440c0201ea4a0790003481c0d5004840d0051011480c2c440e00306001108001a042d0440307000200d440d0b0a0707078180e0201b40010350484600c0c1050000078002c18101003619054100c944000b00240454104461140a0b46d110201c141e001114100e81c030394403001082c0980f07402400402d103a0700159000384060b504100000d160f140c02114952403030742a00c81c034024040020b03001085540a032402080444800710140c501800c94190301900074410340a8a1000611a802001c0c41c6454900600001801c0007404089c80c406840e410345840001e000800b90301c001c20312030034001e1070194281006039 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 939148776 1250 939147526 939147553
    0xb060d1a0420010e0a03020f1311030a0c0e10031802150702010e03120d050a0f0e150c120c0a170c03010e0106140d0b150a030e01050114031f020706020a02 68
    0x66041c0304460f041207800001c0d00620b071103140c0c0f50360030707070303904603000f040341074403c03021440c0c500d00382c00c0c12180a4145070380010100341d81d00045021b42800c120a003c1c0031103503130050320401d480d11000381d04008250310220b10180b09500c05181d02421280031404c402243d000281e45120b4410707500340700580041c0d003a04641e04101c0d04801c4d66002d4003e0b00c1a4030600020784198090700154032401da0325040000d2142940f45d2010b4408054200204441d00d9480c910f9551800d0100c001c07420044d180000c2401003c007a000c2e9440c10440088a42950303031900310084494000c460603a0034030030030702c510001c0040b00f40d90892050f03440c906200d4407903240050345400c0e804180e00c51400e011919248240800001c003c0340c0c00750b851100c020600780400e0000c18000401c42a64240081003c100018090703815041001c40c101860000e10507640c030760b210724450740d461400565046c3e2109081102c4c2c02c0d0106aa070740000e4049400500340a06911008281c0c0d010005010060b0408200175404 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 939150026 1250 939148776 939148823
    0x40c02030d0b0901060c06150515070b0a0204050a03061104152328200d0206061c030c03021906050405011b0206180703080403050d09120b060d1a04 65
    0xc0c0001202c0f414115450030034045d140d400c443ca40a445146c8039036164224206180c6d03103500620000d0402d90301180156000c10054001440446001102801080c80301307055000b52415503400600d89809a8910381c1c501008016050b2108604107042c4000610701d41d030707130030b50b5404080c09071600d0118020745205400c42d102d000d16809601113052004522801c0c1052000c0c081c22500440381004132008001510001e0000c5022030680b008100c28601007075020826141d803807410f400721401a103d00301003101820401600f94440300604016801180c8030f1520208035a0007801502c1c4115101044100d00e01f410b04403c1d1580c036100c800b171008101092240144140c07041481400d1a404440025110940a0126060038030b50b0108210388003024440c120046600c404080c0d034580d500d28105440741c07c03440250000c999943c00000341b1450075410309424503881700040381240e030f4039401c0140041040c40305072807a000b0000d04030b6408030003803000760080f030142101c104001c007002e008110 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 939151276 1250 939150026 939150041
    0x1f0305030c030912030705030d0504020628020d11150721150e100e06030718060302040e06042111010c020703060b0f030c060705030c030d060e1003080a0e01030209040c02030d 77
    0x2901c0d441000400c001c01d102105032903504091001c08031711501c650000071010300682e001b81003226030880c0502d40700307000d00800d100c0321340c2d0940070798803107210d402c0e0150f03500a10b1806280e002e07003000141d20310001c03801c64041d40c42009410030040301034030300106000c4600c0b0031001c40c0380c00c0d0740c4e1851000c00710b841c141581d0051031a4001c03041140740240c80003d40400b030344110508030014501040140e07405000300c00241030b40d881040410020f84080b60050b0400d8401179000d58500140482403003004100b00e8411a0030040f194040c0301d031120618281c1c400c00544030200034040401e04a00c000a010f070b485c4241c04d40c0c0c000c0c04401c4c11820300808032944c0c2041b403882440e90042e0203019450200d21150103000440b039803071702c40c01030b0f060060644c49402040d107054000040c0161003401035510090581d0010111443c450355085604d03100341c0358a000145c10014148841c244503441460301e10a440018503025061003e0940030505076082c4041d0f007409600041103000c26980a4407451a = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 939152526 1250 939151276 939151309
    0x10201060905070f0f0e0622050303070b0f100323010f1506030e070504020714100902010c0f0203070e09010b150f090d0314040e15040902091f0305030c0309 69
    0x30030343c145040d000c0c10929403c900e000c24450522642002c03180140d851101c0c150015100d40e0317880f1020420203202e403001d4450b400a480e45007802140505000069400f0258012210411600c8045081000400081404c600e035280c01c0008070000c1c84040c0107060080001d00806031540e220f0150a00b590303d0904203010340c610b000900c0c50f8420002c00014120f031042d08000800071095007a050410784107800064110f400011008100701da1803d0628500540000ba100c9030f5115041d000c0584003403640107030004003848402c001180c4008091240c191008040301c6e07a030365a40700d2a118094085802a8050b5900d001c400f40505111450303042243d4018145850024a41442d0380c0c0ca028116005008070652081c1004150041c49003a2402945100c00c1d5104d1366a400d0300819048100d45a20a00f45840410022405d050003800800390b4010503042c856541d4140c109003198226a08650490300070a000000c0f50060000304104400580610394400c804000d000e800080c920759003 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 939153776 1250 939152526 939152531
    0xb010201050a1e02071e05030c100c0507080315040f1a0d0b0703270b1902070b0406020a170f040201081602060105040908190306050916170408040807060207050102010609 75
    0x1d00e03c0494203902c06000200c00b110050b2030b40301c142000b2006020003c43c08241548003070b11642400000000f03042c104e00c030001280d454500e40e40f81482911082644000459010301c401400524070714051503008002d0040c504204003610005400d840340c100c4c0c3e28038003603901c4022000024082e80d03000007100c0143e481d406200700d25920244440c04c0280810205595000a03210804898801040cbc018000700000211815400d010082e050283c955080c0299602411040d034681802500e840a800201650040c0c0d0ba545550010b0f620030301004040128484d003254500fa2000c117114050240303d06a0134140c5401e00c009003c1030005800544d83c000a040162029540042c0b0070781503d01c10b9802054458603450700c3c8006005042d41c0f07480303991a40128181d0950f25a0041c400c0303c01c03c45200702d5a803105400d000c0390940c41103461001800340da4011861041c038840b42c542040c0300b55043d5203015960680b00d4101581600f00d04016007200c44100415a8240100805410400d208 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 939155026 1250 939153776 939153791
    0x100c150608030319060e04032a05031206061c0b13051303030b030a0b0103060c030506040b10030b12030403030503010303180f14031515150a0e130b03030a030b010201050a 75
    0x30242c0d2800000c020300203441e80c128406040034402d412071742c001d040305c1d80810b12500701450060b01040524003041200a4004442002d040e0052482d01c17416800c030020b0b500d0107c01c044415030501d402046a40c02003010060003603016200106503000480c0b00c100000c0440101c4100b2070354650941c5a800301605010510034000c041070440e4160503403608000801c0b810241c0801c1c10310071103000c042c003104203003400002406160f130051070b00404a0303a02040780b5a9004100303c201c1e10207200c080e42046110f10000c00d9140690b02c051800d1100601740c03140b0207000038500d480e56105801c21030000380084010000c0503088000f5000c010620100b07149481e041c104070341c0d070341001442000c10024002c2d40070810b03906d0a201e000b50451440407507409030301d0100c22401c0c401d0651800c650140d22407601c1020216400d600344c2e900c2060950300c50b060740d030400341000700076084d44180b40c8038a65130310b028815a690410003080845c4940d10301203583c54102d4000390845900800800c507a50420702c4 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 939156276 1250 939155026 939155039
    0x5160b120c04031a090c0904080a020d0206040c060f0c020a080312010902090919140106021b04020c0c0108072006040b010509040b0c0c030405031b0a320f100c1506 72
    0x243e0b01c840040d035800c40c0c4041c5c2d1115241072a00340c00724807164100c40d002007800b0511080f240106195042d54007210b5046e19068412aa244000c0300c002d0a8400c08440c1806039500c02d145009602c69146003d80380e050554000524512842c0c0c80766035264000120713081c0d03408a060b00c40f401000e4015003141404002c07400324004c00750081918030494a10440105480142d43c0800c80e0740240c048059015038403090069a50107408045001c030a003940319100c02031816008980350144408007030004002c043c4e00545035110064811002c3c0060a010a02810014000e40000c262944000c141500f01424080c91022060b04a01c1c01007504000b00000700700c40f0301040750002d500d4801c50b692240140055400c60041d5004a036050140741d070f03602c841c801c014003104180791048401c0101181e075a5078414803072030b400303219500040c0c03401040714260704100d081c078401c402c0190510380b90600c102c00140590884005400c080b555291400c0305020400c05403103801e0440500412806041c01c9 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 939157526 1250 939156276 939156293
    0xb090303090c1003020f07150f150302040c050913020d051003030f0e1c050106180b011407080d110c011b0c080f040e01060203031603050609040201080405160b120c0403 74
    0x1409405183c21840e00700350944680c1c115005005c2c1c001c5100e072580342c107240c00c0f180003a80d4402d0818203400c00c01030100d01004c611600501043c8035a118002c0c0f0f1540d424003001d00110b892000034040144030020150701e405100c0e080c050031800d00140c0c0e030165040744604550014012180c2e400c003060b024000290044041500080c0030304055440c920790000052441c0c1d030310550f02c2400380d4580e80a608020054004030141d80c00042da40c0074400f0600f9886048854100d18a40000c581c0d040340c02c0ea08031600010130805016242182c03401466000960075103a0155800020310400150031590780400c0c8111141c10455440000c4841406407008181032030714100036040078000921000c0c42c2b5503103411a802000c501503800459a55154080e489400c2100c0804080c11309490840040c2d200340f083c0c03441110010440c3d003850711250011941070000038000c84e10b03807180108903424400346240140007032146000d82995442c0f18858580f200c50060b046008442d01840148002220b80 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 939158776 1250 939157526 939157543
    0x31f0e040c1e090f090b0105040203090703120e030607080403081f14041d070e011a0f0304030c0b0405100f0203090601151205040303090b060d030e0123030903070b09030309 76
    0x50556807003049030341c41ca203074050001c0e0f48820b001c20700e040c9540400160710781000c641c0a000e801c1000140c0c2e0f031103041c0400c0c0d00c000c503050a040d4000c04001d0000130500e0300300911000c11403400d50000f11032040401d1410f41d05541c01e00c04034030340c0c10801040550003030380240d0020010f034040700f02071000c00c006603810401e4014021215428880120326441d1a4401c00c01140c0c0760801e42800b108400002e45c03181e40074000e0281c00022040049403924030340f082806811503200e1100e250000a025112040d040500104c2c01c000082c2001000300307010b50041400f46014202401c10030701d654814104448848003803011650061042083c1c100c40441c00f5030454406120145100c5072013101141c40e40c0c24400d0000c8202d10b03002c02d1006140c0d040c0e0000b110749200b00c000c0e5490352078640800c6603030f110b0907100800040401000b0401540310b00c58560021402048001d020700700c821b200d04442d00220745403c3c007540b000c40c1d4a014414a021481e421018001c0503510358284204195102c0d000e0 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 939160026 1250 939158776 939158789
    0x1e030801030605060612010306060510050c031c0f09060b041a010c1e0503030f041a13022404080f010606170a02130504020406050a0207090c05160203010b06031f0e040c 74
    0x210b0f40003a02540b510790440352403092101c403e01c02982c4915040004005500680c0e0041084501c4e01e840c4d00c3c011401c9400e0b07003a1803c000d5062038144000c41c800620310040c41c1c94013031b4035150202e078411054003e051140d4420200031600ea411740060000b00c550a4400400790f040e103481c090305590300040d8080c8003d400140d07843c140f00b01e44c011340c4081c2030302d80c0f0001d029100000c01c000d15a266400d2090040780300700c600c0406554081160781828806644900320000354105d40401440c1050035248200484000600c0a01c194800001150031980c402103403500450b13240501c0580c2881104045d0105040c2020002401c001161401c4001407008050300d9002440005c1040400c9410000703001c02041595100d03100d650050050b00080a49005441071a001054001007405a151000e60941c0c400381400c89582507027502c0c10000300d041c0c0e0035558800340454192200340c01076104841c11203c40703440b2500d61108021502d607942c001c1c0b04032200f0b0030074400000c5a82c088481182c3d02e = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 939161276 1250 939160026 939160031
    0x20d0503130308042a030c060f09060806030c060c011a09010b03011707080a030f0f021506011d04050703021b0105091905011d010e1219080c040306060801091e0308010306 75
    0x6491070b1400c01020b118003c44140c040c1751009080c02c4400c020090192489502004120340d0365160a8620b0800003142c1400700f0100c0e04244016803160b2603455201100500300c84445010703d01061480d84002807003515a5110000704e01c00c0620b1b0304c00701000c2c2400341c036a05119803409515070142d010600555100104540b0f100400c0070303041040b0b001030003145050710088402c500e005400c86013100240800b0032482c4108004c0b103800829003c520250621028003180c2d80d031801110941c0c45491004c13178003415001d01c0d003101d842c1c034400c0300c1c0f00740e146880041c3e0340c01c0c0032084d01c25081d0b21840211005c6e0b0409080142d18400854103100c03043d40000700d84c480909030329000d40584410052440f00c0c40305c1280130461004150090f40400d141c8005941840c40d000f0480745442c0f11b003054031042104003240315504c0601c40c0c0702c0070358008030040702c6906261701ca58480059079084d0380504c43c1ca81d10f0b807800d00203100c51070302d48139402c0d480c0c2c00141411800541e005004c00340148005044242d = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 939162526 1250 939161276 939161281
    0x2010503060a180f0c03020c1c020a060e0609010e070f052b060903090f0503070512011407030c020705012109020a080f07080c0628210b01020d0503130308 68
    0x860311415000074080040490690200c0d0b0f00030100102a006a032409031820003030031a004038007a101322071114241c038002d0441074000101c12004251402c11003030031485a20820804520b482c4a00c94000c0c80742c0001d81035038200050b03401d095840c404e82210994200074810040705113020318140c200e81040e1181e821400402c00020003170003178003042200407503060607030b002017200c41c0e88540181c5100f80c44084605848903820f03100035482d401804c0e09580102c03c2441289095000c12400b079684400108541c01f02c2c0c1542c502011065a400022903182c039441c95515070107009240113003d0a103040156801009240380e80d00ca194041c500b100b0b070760303800040300755141c081020001e403a880040340d00b80041c0c94034555840140384030780c8580c0c3c0901c82c0301000030f290440c00c403804020048028400d00d00724140c11790060321281043d10903c418005109100d0140300c0d400b200422000700001144140080064102031200000908000d03080040003c075190303000c192407229816290201c2150f = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 939163776 1250 939162526 939162529
    0xc04090c0e16270f03030c140105061003050c160b040b0a051312181403010e0708150a0e1e0c0d03141c051302150705071703120c030a0606050405030a0201050306 71
    0x12244c1d081801c3c42d4001c0300313000c001d05805c87c42e0f19280c91301c910f40d82c006400400d10b045088401c02d94185501511007000d0002151003508180d400030f030a11016440e0a8074000881c40c06891928112261031840d001c10003844114010294402000901801145084041c0c409143c2183d10010540701e00e9038910641544200c1060700b82c0d0313002c0394101c14055120312250862035002d41e656031196090402440c0c00f1800414404204c40c1920014900804601d1120300000d01c000c28140034980d03503034441c03000304038104244406020941c0701158a0f41c2000720341410407a804070036070300078011700d031000c00020f0740322002c000c4095a00014a40701c155642480488060b0b180003428040d00300390a010b08840c0c1c012240803d5442100d00707140d6802c0a040c044504c0c064824041c04a07003080300b04218a0444c45200c00c491007100056900c1d00e181d90780c0c40c05035180162100c0d80100d2020041059015080c800c0c00c0241c0f2180c103080341058588000250b032180041c1c4000d04014012002ca10346 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 939165026 1250 939163776 939163847
    0x90606100c0312062601060807090b030f1902040e0d021c110f0708010501120803040b070e1806030d090b271203091518120c04090c0e16 60
    0x480031000040c0121076440070f040304800310300f02490854890b004d844048400c0148a005c08488c190005040d0b0a03242c504000020300503542c00f55054000c084504580b4081400916048401840380c402414070742e0040c04111040480f4504650b40301c19203120045800107a03000c00c80140c141c6000b44189000c00c11100c10348000200c903001d11550360848404e103000304088081c0c4001e0b4000300040e1b80e0302c0940b43e001030746543c3c002d0000102080803c0204000c0c040182d401601410703e0b090081400c40864514500045810f0019180400f8800145800d1000204071211490203420b013a00b0032650041c0c0b885140840c01c10180d15032002105414403884107003000300b00400c44900340e03075880055904c0794040c9284500c1442d14043c5c0c100003400d407006440407a922100740e04034440e174000901000c182c0e414001c481a205000003103d0903625402003c20080c0301d40c0100000324605480d84001031000741612007012200490b52100561001048020403107082d144250320b426694102c50 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 939166276 1250 939165026 939165047
    0xa052505090d05070f0e01090e120d110f0708030411010e100309170a0206090c01030504080d092f0102011d0319140d1b030606020607030c090803160506090606100c03 73
    0x1061400c5c10005400304150700000d04a400d0136006104007a00124001d0b100d0000540084541d4414010b4007418a0141d01c40c401e10f86016403954640184403029002940180504a9a041b00002040100300d54000c1340d26213803400f070a00d08440c5030b1302e07400034811039401c8208001b0160340d00c00101c20310805044500020b090780c10803540c0c80c064014000e440301c40440d101c1ca9280706054042c2c0841d40700c0c1c890284104d800644d001e090070380e00110000900080441915280c031401250080001000c0d06840300030b800c89030954400d0040d4001909451130f108480c07c0341c00c1c074495241300a040200854030000d1444020345844103221400751680800c02c040200e01e0500458481c051103041e03842500d0a00000100079807114200c0411000d90b111380c06041c006801480c08914918001d1f000449004528107200311501c0d121050f5500d180c024407041300b4136201136101402402020700600d508a6101e201a0101c0c0c0b03000780109000c5903e00c2504400c0101c1d0700020020f05104509006 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 939167526 1250 939166276 939166289
    0xf2a0d080705030727030302060f01121104020a110601080c010e04090b041707060c050d0b09190c0e0d06020301051504080a020f04090203012912070e070c08030a052505090d0507 78
    0x10002e1b502c034200203585407811600b50101c920140f0010482202e04903404100c680e015104403040e407000802d100180d080310340107006004103480c86c00403009041c00101d000c2c0c1a0107009114401081c000180204035036188180510702c0c1891690100d2107402c1c0d000d62164206071036449403011f1001c00e60a5210f0744d103024207044d2502003008035266001c802885a0248141d081c840410b074403003008103035507080d1090b0141140d540051b100c00312842e002910030380c11714144203c50315121008680e503800d0880c41281c00e5540000188841d05e0900502c1d00c012421741030003420f06040c8581550f84001365030019100b0f1b01d2260246e100d907a150b410403003031564058000e004012075a00071480210020f440340f9806034803418042540d040c101810545101200c4c010002c80d803078180c41d40b012581c0a0006810070000c0c801d050f000c108804000c50288150031790020741885e14003001c42c581141c010342c10305010740c46884108015400410b03120395040880f0110300004503803030190320f0007003154820f4 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 939168776 1250 939167526 939167597
    0x20a080c0f070e060414060108150f1009150503060307060e0a05060d0209041b020c040e03090d0302031e04121104150b1206040c020d050f2a0d0807050307 68
    0x103c0c890b01e002164900840007a035092140180c501d2003107a181d0800c40e042800900242c000412121000c01c084000680150260740c41d1890100850003503a1140000c002148030f00e02e00300020540e003070780b0329a01b030340910702141103081000c0020307101c0009203e440108410143c022081d555030010080040000a0000c0e591300e4507048480b000c0d410a49480f441103141c8810040c4003215803c0d00d86032100c041d805400744180e240204401041c5999914001f48400d100010280c0c40751100d00305082e01980041d0340740d05140b0f24504110071044160340d01b40070f09010030130880e105000d07950701c120b074040e40c001c906900700d034041030040158805900740070110305000924801000d00502132080084283c0c00e01d60703580000d02c0142c0700004400c40042e401104858a980d20802c00717008034218107014149840c90b841c419807402000c0c0010621081d042c1094004845d0040146600e05103e506150002c2c0c034140c4c1d00a80180402018034050100c2200500e5611801c0d203400b81c1941406d0280 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 939170026 1250 939168776 939168779
    0x10e040602091f0f030606080c070501180807021c15020307020f1510050105030f0c0a140c0d09230f0f03150a11121605160f0303050a020a020a080c0f07 67
    0x70b00e250401c00040c3c00c0898640d20000103400d10030b00a000c2522888d4031420060b4a0f00b80110f0034640c8002002d4030155a03d001c00504400c0742c0072100c1c4401e000f141455120f54060040007220080340344000da45003201026000040c0c0803004d801040790024000607200d65840c1030076070070044004003041480c041d5541605200310340d07070300d620301074190100070b071041d60b0b01d460042d03403136210644021200101100000311238100c0c0f503001746407080c12450701601e010f00c0700401d022350f50020102440203400c14102c4d2074110f540b2012034030040c05007545800407900c04c9a02580fa290224140b103011700700213860341240d600d41c8040c1000f10f110103000c42d051040da40c3c140385507614060320007810a40c2041407001201d0f0065065500122074110788081ca0b480d889030a03e0841840c822601c10b0200a002100941202002c1c41d0341d8180111f803800e50b06415031a00508880b00182009401032050040b2061160700250340f8190a5000e114241e072003101d4811145049541015806940b050420 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 939171276 1250 939170026 939170059
    0x1e05060907080c060403021302071704080c0310110a030b190b03011502120f03060d06050106030f0b1207031103010608030c0f010c0306030308040b0a0f020a27030506010e04060209 79
    0x1c14904880102c001c0d910101104020041c80d0b124a100181d400340c103c211941c10310300310350700800d00300e8031405000c60200c0300b05041d00029041079005503003640110704807071000d0030140905d001d804407441d0b00700702c0b032140000003c002c0d025491910042554030040602e040d150300b6444002d07030005582040105d80e031041101c3d2958400d0182d88040382c2d04515011000b40005004004106048086030a108040c088003030541c01c0101196070140828064002242c1c0303920402740640400e540100e0b540003950b030785501741c0706110f50b0240200000689001c01c0e0070045a44000c0d42d51190501e071038040d6440020703001d0191500106401d0000140c4d03086a01000a02620190003c07070007440000c03403801d4140c4c01c4919920014010031054400240003d035000c032929809004d03002c00103241c956442400003240c0100a00e200422005061000c0100078007000c0c0d03641404a80284e00c5035402d55031125142c140c107100740d80011b11840c012401700525601034a481c0417010f0802a40040d83c00b0 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 939172526 1250 939171276 939171283
    0x30b040f02041a040509071112160b2401140c010f0b09010b0406090b03062224030f030804021206100f1d041103120409020403110a0e041e050609 64
    0x800c140300e0f142c042c0d000e5003080a95000b0b950880c2c0d001020107189039541c4005440040c10384070205510701401a07102e56003d010406064800c4600a00c1019a0781e14030741a6600d400107001010340252045101c0e40589540e1000b188484c001c0c60100d8140d9050310301c400c05405924002d441550a104018191a06950146000c0201150b05440c0d03a680c600300c8a0b580d00c190702035880020440c18050204d444000d0065030170040c040c0604180b103005540404040480c2d109458049407120040300d0000c81c0541c111100d442c0e07026842c0c9006246a0300d54a03800c050200040902071150300213403d5540b00c00c01070040390215800c1d507205160800b041010300d6090b008084120000045c0451441078849501c1c050030910854906542c50300c0c3c0750032060491a00c1d05650521550340034826100000000e080140000138000d62039a0440c9004510720f420a01c00e02d0003550074a0013003040340e5001c1c1d403040d04690000d44e0394040508000240e18100490b0101a00c141b00c1c01080c01104000003 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 939173776 1250 939172526 939172529
    0x2903090d0906080405071406120403081b0c10050c13030507081c08070e0a2114030f03040303110f040806041a13150b040c0c14150a0c030b040f0204 65
    0x5540d450340c080d4075002c1c10f880e00c81003500c0190082d03201040030300400800c0c584101440c0e00c02400075052901001ca900350b00203046070120005100b1109001d90720952200740c000321840501c0403820a100e00100560341c0d180e4100c014507680d1a140460400b040340411540024001075464900c07588070f040c00c50b07559000d4820b5003064400c40422030044e5030403100701101e00103550f40d0031006840d00901102c041181600880d48a040c1d05000103004000e00c1c0405640902c0f842c11000b03031600c0d0f00781038544202480c60655660020400c1c1000c85141034103d90b8450703414140094607008004840c1d4542c02108044040080b0000f00800d860100103007062090307104004c031400d910348000d23101c13291810a81e505041c51822210a90009610703079562007100c0054800022916006070001e000d07210039804500104447c544440284043e13400c4003401c0312030f01c00080c41b0025001c807003001c50b00001407400e090143d4608022038000d01ca500060702421005206014980c10b17000d4110081d40305 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 939175026 1250 939173776 939173803
    0x53102040b120109180803040510062c0c04120804031502071b060e040209040207050d0e0102060a1509020a050702090a06140f1003021e03040b01170115290309 70
    0x71030b00015403c011409520001c440c0112a00916146590359602079000540103d070b0900403160040d03000060340c42144000c0611000c14000040d8061840590103400100303400294181c0e410441c07000c070300e101100c0c102c1d955012981b12001d601c0c1403800d064016500003c010351181351203152024442d030081c1002900031480041410103500504d110501144517503004070389c1f0648801c2444c54564081c0000c10809000581380c8021940c0e4541810401601c4c1d8010900c42030074644556810000d155002d2908001040309203c000311240100295100b030704d0056400080300c0f080c4503c190250751840d64050f00440341030800d5160200a000d1b24000c1c1c00c0c1c2044c1e06040011149004040c0542d5104003801070301c4000102071040303019507c20103c418900406545002da40351218005601c2a40030300101c2200c2e5050841440202218140b00b00c06681054a512030a15100204d8802c03140b8048035000c201c0701100d500060303907503e0103551011038004410490324800219410328443c40 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 939176276 1250 939175026 939175057
    0x20a030f050d140705060718240f171b0f27030c0a050607050f1024030302190302120705010f060b040f030f05010b061c06050604053102040b 62
    0x116a001031202e00641d20082c5c0039901c144041542d03940920000420213103207041107401541c03140c0c00394040d070340800007002803c0e0f81c0c1c800005107280e1044075030003142924035000e00f400c20070a0044000c80006002024464452034500c114885280d044540043c19003d00c0d0392162200d0001c03603244d070510b0405400c802d8910f00c1b1a41d0340e19001c00d440c1c0c01140700921240c101070825042c40040d0b00a104203c5084c41000800040c00724100034085500b91520320100d103903441654107101c201c6036200a000c5c81c03c0c1e08101840065000300d0034001c0090b040d54003074006455820300b00e2804014250400c05800000f80c440c06010040d009405042c40c00130043c481d00c2c0e942d0070701d60030a20980c420055085c03240041800000ea0a20541c0f207494010b00c00440c5da0309000001030501c1d8000c80748040303100c1443c50306030b440206501602c00100380071240e250a003842d10b8041000600410808810040106500c0c804141c008440212280d03400d441152030f15103800008140b540102691000c000 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 939177526 1250 939176276 939176297
    0xf0d020105010f0e0a0605060f0a121e0b2b14030405062b050c030402040e0c01050d09140f07030c0b0307090b0702220c11030306100804020a030f050d 66
    0x18014001c460490f43d00090381440d4500c1c2c14840d01c4580030140c180e0501e2034541c00300042903950307a80039000744206240030710b6843e010f85402801940e184e1240f01c5000d0304240343c0080406203130b800700710748003040300b40451400350840018078682e4a80300648125540c4d0424001000031701d460341c880c2d20303208502c1c045600380c011111680c5c0c0e000d1441225804001044111400b0b42c0700c2e10500c0e140d00c0c442c8010107904c554424403038103449003182d907042c03204804420841507251901501d809400340380c0c06844141d00000c002841c520810411920082d01d5441d058104000700420a560035140c20603151000c100010041e10b6071a40d1000b61101d6800f20b50110720607180034100c81c015841c03500c5501c0310a00e010300f5811190070103c2c007a45c1c01604901ca814141c240198042e445000352040000d6100301c00310082d00c1405903c03440401644240200b1800b921489030604032048a030409070700a94070f9100044074440d40360001420f01040714a003004020700069811042280f54032840b0858 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 939178776 1250 939177526 939177553
    0x30c060e03150621030c061e071706060d18021014041806170a0302010c0e0f060c1f09020f1c030e030106120b1f03050a030305071701080f 61
    0x40c620000400c03040c0d000b46001c502c0519088010252000c1d15164107900303a004042101d0542d000b500d0203403141c3d0401010081c003001003103035151210b05c2105002265080440f00101b1380413449061019802050380410059500c24065510013000c8034820310006000003041d094880480204902902500300d100c00c100d8050380781041c0300400318102e60300701031900360348034480b0340303140300050a143d170b158400b10346000850051031604d2030a40040a00b00b4051800900b19005d00c040c00040041300c80f1889219515200a2110240704803045034664a042410700d0800d130145610342c00e11801002c2c40a0340b0161500181c9010380226010000406040e080c0440c000e1140c1030500d404403200045000640189a68204044c000c0c00001e109038a03102184540220741d0ba0070b45d240c2500070100001c507444100d800f5182044060310b03241d001d04d141d40700d80c0e9507000303040c000301030549800025007802e11503503030101300f80203d810211195075030700d5900e03480e140316003244010b074080c954140150 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 939180026 1250 939178776 939178783
    0xc02031c0902010815060d0e0c0a08030f160809060a18050303190f0c0210210207170309010b130207051005090c1905032410050d11010e0406030c060e03 67
    0x700c6406841d16404e6990f10380110b1044541280d505a102c50144400091600c03d032060350035000056005050402c6010108125031160740e00201256100b0400c5440704c1d01c00c5c0090300c110302c01c070f000881440c0045260540c03150061039902e0341c01c25808202041500c2d032141e000d240307101240203100c0900381c5540c24540c6030700c540c054608060303400f04444d546952045501c54003242051401800c4210760f940002e0120300f40600b03000000f5030a10704c4c07800c0300c0c40e00038074080b82c68485401185030080c140d940081d100c4201807044221350022000031418042900010703c0e00c40000c00562050340401b4000d0029041000c06170b0349031142c8c05000042200d41d00c182c0e80146651401000400440c2081102c0c2402008000310070302c4c50440001101d0b10104001c160364128060000c0000240000440a0b000d00400c0003a254644c0d400411054455160780c00301150080140d12030640a0001659500d000483c140e400c180340c58800000d100c941a00001603d20035a26601c4254585080658 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 939181276 1250 939180026 939180041
    0x30402030607050714010912110703020a1205330a2d020903012910051e1615060f0b0f0306030a0510092f0d0203100c02031c 55
    0x1059070004012484080c0240064013015100c0c10b20610041d000d64045820b6800140040f20b81c23100003210648260b4011041c044147c00141c0144021440e40d00058842906446002c9514980d1035404092040500c0591100c543c040c2c0d91014120070b21441014480703809196aa003d2a10f1f800700d031200085008541e650f1030fa1008500c1418221322018a0107840348406040003079003000032545980b000e0180c0c14403141020200c10001d149980911046100e4801d40c520444455140c484d000e50404251036480040c680341d2002254a4900c42c6000d109115100700c0300e8545001000c20040400c0000034034001880e401e114080c0d0320f0018040c0355815001d140c24524040c845a00c0004420004d0740d40410020100d8816800f2078584134102200071011030309441c0c890320042d05210401085028000c03002c0c05910102c10050400030301c180b400f1800a103e850040030010655a0820807480619071a0004000c0e81c034611101a50740c1e4010420b40c092401112a44a2041c1c800d100790003 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 939182526 1250 939181276 939181279
    0x12020102040f030c32130e100b1504030201050a1101091a070f021b12160308031b09061209070b03070f0207120314160f0f0b0901060f050d0204020c011a0a0b030402 72
    0x4c4080c401c440412260840c601b808130440b9a40703001100c2811810000d80d20140b603000f8002800300b030807030140404010b488048030b5400341d08010400050760f01c201103607030540e440d00e0300011020002c000745015001e0058050440f0300e10745008003007020140c803007500803038081d1200250360a81e442c06a8444d480c0c003490688146408003101c0c00703410710f03580d40c24500d04000c080d10b10b8528800790082a015103504107864480d0080104043c044c0399402c9207509400910819040c08036110003e60b80d4401c403502d290407031030b074400803809440c000c0100308058490980c1254603071500d04802030881000c03d082c03000600c100c000010b101c500081014000300c0d01950303060030000320120600f107264000e142c050909081c07070101d00c01107201c506090300b51501c5030011600d1041e01e4200740f071041030049c04001050349440c80400c540701340390310400221141914084e90040715800000c0c000c2c004e10745100707810750800d5080a14500d950070402250078084404800145c1c03a4035140000d40000c54009 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 939183776 1250 939182526 939182609
    0x60f010905150f0d0e070806130c05040b0d02040e0309010306120807260d0b0103050612060f1e0f010e070c030f0c020a05040c08070809010c0c12020102040f030c 71
    0x11461580e180d4010b181030030f2802c45032850a8034580c804011213210141050a0390045201482080380c2440596005100900e4030071003480182c5410950504e50304c030341403189544146c510880e4403801c07644003181b9001801000440d41c010100d03030f01c0e42d105a2481e40003d2901c9804200c02d2410240b440034207820540d02c0381003251a9139849807c03803001c0840802400300c0c00e405425106d50400401003200143d00110700c5411000014043d40c0001e4541c602c10b00e40343e0b10b44c10300341400003202a40030103038a045d40d8071a07d81962180c0c05060030070900c6201d40040c000c1200e518407840506040b5185016102007540c4d4980044031082c0c0702402c000c0028035000b0b2617140e06446003401110f5140002c010050080e62000000c0440b8030200011012810f40c500700410755403c00a40c2d07522140900003070281e1008040003d01d0750f104c188008048180303605010194620075070556014110b1842c1c1d03651400d4030b034141010640e40c24860040661015441c029100d90328110000c2c4030140100361 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 939185026 1250 939183776 939183799
    0x91e030503070b010f1203140a091715010e0105010c020f0418050106180507080112030e0604090f1a0112090c0f03150b0406061b030c0c060c0201020c0d0f023105060f010905 76
    0xc0203115032101000d8820440d281c140400d07200083d440003161800c1c801c00900c900406009410f9102ccc0c8164441020410694010401d07a42c204860398400c990440f220040414600c0004009040d02d00a01c000ba01401048104100e01507000d601600e619500c0c6035540070341e040340a002e8078011107140000900002c0100151161100c090b1611446400c0041080c009007000c201c49404c00d0f445015040c2d1103045020101c050b52140c424004403000b80b040800400c0b10020382100ca0711003900103804e50f035100700740911800e002c1030805006560b0a003500c4c980d6905082e8602c100b80300550200b58504800b107000b610f401c3c81042d0480b0100c0d00d900364141030203400c51184030807100007501800200003a05002036800480c45002d003015031142c401d004c3d400d000091514041400981c00b40030b0036249034011464201c41e000c03a00c0d83c100c80303600c00d40304051580c9100d05960300741689000c090004c40420881280c0000c0d20500303040d00d404032200710340001120030b824948a040c2c0c10040d50000d = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 939186276 1250 939185026 939185057
    0x1006030915022107391709090406050703140103051f150303030207150b0906060711042d090c1403030c0a0f02041103070e0f0402041205031315091e030503070b010f1203 74
    0x10000d420b2a1b030846100c0c140301d4490081041a01c04403412509a0381e1502008042c603054031410f69058846101c2da845507055669403541c8000d0a0044070703100381401e11122044405410003e18082d0802c5003031b03003003581e92902030045c1d04a4007003180c101400ba04110340c441060701ca0306c11000300007060024540ca03640700f032042c140e001c068155011080251209030039100ca0050350400d5600d855502180440304100c40c20701c0031103c1801510506003009038011403030a20142081da065900c4104e141140314002900d0341c85186c450b0300319406009400b01c113000505001c94080c600907038051054503c450382c1c103283c03407004550400c04620400b071001040e04000110f08813880700940b00514003900c41005e180b81d41c1000008030f4250740300103201088142c1008403c00103003031082185001310b40c07200e00039007102c2213801104941f0099104003141440091240402150824107070f0755591440c0c1008104103009001d0354144a0340c10307a0008040704042e0000060740d4041d0707640c000c070548207003 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 939187526 1250 939186276 939186293
    0x70503090f0d020402160605060d03090911120109020309060c07020607120302040b0c030903012a0c0213020a050a0e030f15091c08100603091502210739 67
    0x42415030001e50b8800c0d1040140c0341c610060407040d15018140541044c140343c07284c103440000345200e000b11600c240c0b1800107500521141d05070340c20b051004c1075440d40d43c00b00b0000c0c1e0007200c45800c000e402000001030300c54001d500550140d40958140c841ca079844100d000017502c1400c10003508000104401404208a10000e010080841c41c0c094505a030340c0085591541000d0340652882d000002c42202c1e0389001d210713242817540d0700214024101c03880c0f4021040c0c0030500000c102485156070f800d20456444983c200d14819101d641103440f00d1804030010002d0300916402c00220b00c2941c9180318074540054029000e20a81009080664031a240820701c0c40e80540030b0f00b51882a9940180701c040104440d003145c0c6003980c0d0382030003407401408104504042d54401c0c0c1c01c0c5440d00016601103120703006414421490364202590b0f03608040c0e42c01a00301c5000c0d00304180b0340401c2061000c0181c0c8446407241e00d0315012a6800e00752510003104c1e02280c090100755a541107445180c1c80000c1810 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 939188776 1250 939187526 939187549
    0x50d12020120040503070909170d020f130816030b0a1a030102040330020c010806180910060603020301050a05100c15060531020c0a140a050106050607050309 69
    0x500c0042200c2e50140ba04842c007810070a280032404001040c20703c4141010031440c0000c00000c1014010b8284a071507070080190100d5000c900100d00084500c140f0580d0380450b4407240349a1400e0740e5519100399103011084070b40c0aa1005800784030a8418500c620003260019282c009050314803640b40c1d031004100030402001425601d1084011040460360f0a20240c001580590006140c2114000b4040c43d40240003100402050510b40103000582d40011060744004080c28040121786850001a954214540b5a1103408250303c0820400000100b100544412405018410191584400d905902003401a9030300227034007000400852401e0302c400d13420072546083c1141c141c265074031403001e107808411041d200035486070b90802a604000c103c80070441a009a1002249045c00d80342c501340401c00124101c1c1c50300841c21400700e40c0300344588840a5030006019030005040e0303800ca40c9805070440305551a51a180d80064541000011500010740c010061864115000d0420608000700d = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 939190026 1250 939188776 939188813
    0x7050622060207060b04150602030405130b0402160209060a2102371211040506040e010e010b030607091212090906090e100204061b080d05190510050d 66
    0x2403461000400d00380e10003010842d02402c4003041d000c0c0c0310310901094516100e400d112841c82404100f00701a4084103460980d0412070b44150240d0b5903880000240890701d4220f60f0080c800501d503603419042d03a9410000b02e100355942c000c82e503100340812540c8050752148100c407004032043c4411320000c41c645643c000784020420f80c40c4800100400c40703910074001e02c041c10076054040c01d0340f009074550740100003044c1c40c00c5040c40b0150507545070460002c01d8640e07a40110b49420100700c1e25600e58018002000001e8001c00c80c00807109121806402c20000c4c5a020740100360200f112540f017292038400f9140121880c40368600207598144840c08003002d00400c00020081c04542034505010703000c02801c0b201c0c00031500c040c0c0c45a5503070401030340710380c42d081c1944108000c100301a000110403107407800610307464949241178280703840180700308540b1004040c40c00041003817126080c0f074510b0302e032045214200603035038544524440030599401000c0e40140005082d030700003107540c00c8491400d01e4 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 939191276 1250 939190026 939190081
    0xa03110f040509090a08040816050d08301603050a11031803040312110d17061309051207150204140906041506020d02250311030a0804080a060501060203070506 70
    0x465281d400058206808c2000542c2101e03400100741401c896000b030285c40122050501000300b56254441386c42005c041c2009c03807205104a00c0d05881040e004100003240c1d2a25081c2032500d800d003840008000d280c1c4201292828001c54001e01b07540c440d4152240a43d91214070f1070300c03904a01601c5840c3c1c0c007503000ba5840b08000210001d04000c02800b100046500c0b0040f01e446110802c90400f00079031079400c02c00c148000e01180012842d04800e404c003c2c00e94410080c41d102003c0500503028100d00a4880c0c8a50403000078500300100c000e001e22400340c1c0071180d04507641001102640705901c1b48001c0d03650b01c100b0403000c0d45800d100c1390b50403c074000d00004a0b51104500804850131a40c001000b50304180111000309405114410003040240c2d5105401c40c1404500720000c10340c0d00003d801002e01d42040710b415201004a64803075074020f0130f8540c650f940d620840e41e5542c0501c41c200d45190034074000281943c000016100e000e54007802514107961007001c0100300e02840e0000d5100c500 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 939192526 1250 939191276 939191293
    0x50d0e0a170f0f0f0a0f05070218100305061303090807030503180a030203010903031514130e0102270316030b06090402031e0f060c0f120c1e0a03110f04050909 70
    0x8a81c010300e40e45107038400085d1501841100640800c100604030402d02004020000040c0d46000c0350901105500e01c1800d02c58581c00078842c108030fa1900010524810039040c0300e00b980580310781c610440e2003544c4065000e611040e400d904d4103600d01c002401c130b03801030240e056201d034095501c80308040003401c0d0702c200359500c0e0002401d44040d5101607010a83e0745400d56251034040f80c01da07010702116080c89015075685408190002c00e441d00840d50159030f1b03064000241000e404407032410f0091a20748220194141d0000703400000d4210350740c0310381704010305540c0900351000d5850859400642854090b99140184000715000078022030741401042d2a6112405004206100f02030031071004208684102c3d01440c6400e20103058880c0d170704028000d060100700100100e40340500c000f181c061807901c80d102080c05501600c183c601460304800d00e2940d200306080081d08020f05a43c1d0240b000c040441000d41d0144500100c074050000c00f080140081c3c00c0c0801e0250f00a4820000c0340c4a84 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 939193776 1250 939192526 939192547
    0x19120201032a0806100c0f050316030801080609160b07111314010e152b080307121b1103040b04030b07080a0c022d0d050d0e0a170f 58
    0x100da5040780e15000b86a5240140000d948002140d603c0101500d0403145401619000f4005c0c0c0f240328402000030440b50003410400c14280141ca9410030700008221440c8040d24000d060303030000740600b04c118416100012180040003070111140080158030103c614248180001c80b03500c10716090347c1c1001070b000c0061080d2076980690050142042c1d0004810161161900052078181d001000014052040c0015209001d10b02a0a004102d80305c0740c032084244482c4000c41128102d01c0c00c00003044d0900d505101c4110025031080c00c0e55a17541c01d401c0c4507130f000301c1c08544c2d6a242c0682141400d8001c116114002da01c00e9115015910480c0d08041c2d50340d12450003a0b0041d0401c40b0400d60705418041495000740d451074100b0500381c0180f00c0c00300e5450000707644040c40382c0c0841300fa2609100030190016804803c01480301c0a200b56144440300c0c0001030542c1e88813010070200036242c02524001a2408076107902c4050b4850b680051401c9140c50508041c1c220503056952240e0400460481 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 939195026 1250 939193776 939193811
    0x3040f030f08071a090f01090203031617040311040509010515090a113004081905040504020a0c1106090117061c05010903020d0912030f02010b0a060309111912020103 73
    0x10b04019600d510302c45e103002007607030b420f2208a0615000d503a04090070440166000310986120308400780022002200c5401d1440405401c021a00020000000c010061041c0d461071503680c04004e4405000c0b50311014005030032124125034a443d01d15140348030a00910304410071682244c40c0500c00306004441c481081c03502d9000c5030190380d0106081c0310b40d19400310402c0c802c6c04480300303000790a065844e141e04d03014000c0c4100c184e03030041c03d406401000c54684c05141a80c020b040098021034440c440798802510754240c0000655a452030381a1035000c51416000b00c803015801039403a1341043c0c1130800800303c0131a0281602e40d02942c200800d035642c00d40c0316004040340d0302410002c5900510350130041e08090306e09003948100641c150083c40010b40c400802c020300382e030600e4110000343e00710f0340481c0104443c110041d4000a2150700150746e035450742145c550b150050985842c03824440302000000c13150314003094904450181c0800c0840e01e500c00200b4074034018140400d08082030700180340c0 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 939196276 1250 939195026 939195053
    0x3040b0601051e0405040e030c03042c01030b150a060e0603060307030f052b0c1103150a0f050c1201060804050c034201262d03040f030f0807 62
    0x2591012031308220920302400b0341800b10601401543c64400c840c03000940324416030044664403010140c000710300241c110313804240319022030748403111540c40c0d14000700600c00035100301c1a40c50174580e94481d46e24000d2148411210a611601c41102c20f03072081c41401d4000800956050003000000404030b0400c1e4401c52200f07201d40054103600c4101e0f41000d21141c03c104c60031094546102e001141d00f030300020959400da401c207507202c0440c0700f40f00020380781c400501c05051042d0760480174805000800d402c0010300d9254403d0900c016a0344009642640c0113540080d47d80300b590b00010011503011f1031449801502a0054071448544500840c6c5010340c3c540014015082c01c3d5808003c140043c0744881580003242170700d100c8600d1030f940062200b081070040c031002040900b04154078200e92502c01d003080710700c101078030b000032554140c039220141200499003c00c640300c2034500c200040402164281c41c1181581d0100c2c80c119240c100c024201d100c2c04444203101000b142d000b140d4000076419 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 939197526 1250 939196276 939196327
    0xf0712020d11070c140a030b0c22080c03010b090a02030408190c031d010f08060105040f030b0f060d1e1509050601080709090809040506010905060a0c03090f080303040b060105 77
    0x40d0755140c54134000780003203025440b801014204110055040d1360f0040d008003141e42000400c641074640c44071349210340c030070003508900010321065101503a1201c0100541100c026000395140602114245400e031002c2da02030660140c015800222080c00d00d60207540c00900504200741130404550801c003024040483d01804103507180250070403d030384404140144a04205001c1f415060000003a042e6100c4480600034410003d00040c40c5902c1034040d24020300e902e41034484810b6490509550301c1c031b0309075184501c1f9945100001c0681c20010201e600b610303400f5039214126415000c1040000f62005070840cac460a00308080e41e00c10205000754412240140c01034155545030090751894134003503900004201c1d0030101000c0c045102c40c2c2c150f07054400252408100360b038800004071340c02400c907040940d1020003c03034020711059120003403100c907600c2901d907541081e0706d5140915403918244228029503004100050001d58544015500101c044c18140d081c28244142c130112071b0f10b03866144 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 939198776 1250 939197526 939197561
    0x10203091201060e0f0f010504060e06130e030d05011410050d020f30070201110d05063c060f071b0305060a090312021822021803010b090f0712020d 65
    0x3586d503102d0003110300501b0202c801304110742c0f0780b210070800510010003240c032845030052000c40c180a10b03048032002281038415203540d400c949843e000180404c0c020340d10204114985404a403d01076800d40d041c1c0469200c46041040030f000340030181d407190b6010140c6c0a07042c800e250003079510300b0030f50482001142c48921600300d40302c600080d0506c01071103c0f045a06210b085030b00003400768210b9240008600c070204183e50343c2c1e00801d940e580c683c0151340c1c4483c0c3e9a200c002100c0481001c00306424440e1510301c04500c021f00820116024000c3c0d465203204081100800040026010402405003010a0300d0030320390365200d13513003000400c070744c06e000590303e88110104040c0d02500c500520184101c085041828099a40c802d80c2c108110f21400381e00c10710785da280001c849803a80340a4144268003996030340030740d54143c1c0d24100003030310040c0250b0070030054505510700400e00300d100f4016502100301613990800c1c00c882103c800101002450703801c100700c031010070260184110050724a99a0f = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 939200026 1250 939198776 939198781
    0x207180c08091b04150e04081b0a0203031b010f110c07060309080a1412160e041a04021e07060203040209010509100306020307091e060206090c010203091201060e0f 72
    0xa8072072080141902030903001400710801480c40f518001d84140d006890015081003124403080c1a03280940000c0c14510901040204028600c4014015010803605641e006644c50303210a036a0040c204000390b05401c140700c602d4502d040303403002120054019001050303a090078000002110891910942c070704c0000580003c813082c2c01c001c0100240003070302d001c208041c21910340d0075240c02402c42401c100001205d04881201142050751607003411144060700a00300907502000c0313041d6100743c190111780801c11700276980c5030912a5260240080c01c1070380d0300792010b1081200a40c0a030401051520042c150040c1c0c0984c0a0043c01c944c87c41034000513074a060900404c024207505a0109224003000c10070001424016030030302d41180d511220141c2c80781c540c807a094a80e140103801046520074407174100000301034144030b02c40032912035400340e80c8d040d111001c000340c942c80002886400341c1d000304100511070400010440c001601d060001030310f603031290491348248205880b1078401e40f410905 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 939201276 1250 939200026 939200051
    0x2041b030f182a0f09060e0618070e0a0b2a030901021207020105043219050613080d020f2a0f030a080f0d150f0b0a020718 54
    0xc0c03902140c00c42c4821104080560b40302442e00301c0b000d401500c0140340240314951000c1150071280070b032070848140005652074035100c500030074140c4038454552081401103849410100402c01401041c40408200344e80e41c00c070140c0340343c408402490742001140a001516844e054084c02c2d04446154041103403820080407040c0c0c031051000c070480c4542040000318150ba800044040030302c00c20a28142d00d40c1a54001660f40740583d40c02088103a001d507002295100000108d00140609200203d914000050500103400358030b45907c40481007a4400b84080c0c03a1031005014504100541000810f4403124a64100313003c1ca0b4044025900041158842d050140301405959460729956a081e0707034204000344103041d901e00402c1c040e090b94330091030380b070b1824044407203043d40100f0121ba4a10998044103815404600e03400001441c100c08411700740c400b40c1c0b0403411150f200c2c0c0c1c071001035030a00d20b00f8681d69210004c1d010961240070320018900c21280c0543e010f0068102000506208605 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 939202526 1250 939201276 939201281
    0x308070c170c090c040803040e0702070503030d05041505041e11030a03020106060207080a050304051203070203011a041103090622051f0c030b030604080c0a05030417010b011b060902041b030f 84
    0x9020010070350080c082401b140200209640450385200030440103a10f07580f000760305080307183d0801901800006800742295016410031130145104000110039006045811400c64000380d6006000d070400c60080220b04805c8603006a40c50700503070b40b003090341070440700091400784016422400351351583c00c10050b0f40e4040c45044000e140704030207040a01c0c0b50f0342d03415489110300e014080c8555212000d11079610010001e8411080e4050001c00816108001144690720102c011a2042d420901402c2c460300c030781002d5a0181b200c6600038036464580070b1a508200001074030112031ba4202c100180701182017040407a48058104d5a0445141c001141c40750640d41c0001003802418100048400562000102260b01c41d07000398101c0e41f00d546201c003035070030720325409005006840041000310300c8040c020b00c442a030020001c001c01c4840c8040c3c006441500804820b4800c0001000e00100410026084103c0c014801400007603d4890760021650000c104422100000d6070745000c40c0c010074192 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 939203776 1250 939202526 939202531
    0x14030c06070b0103020103050c0d0c11070b0a0203090411070f0c090c030218010804050313090203011712030f0c19031d06010b0706110d02041215050c040308070c170c09 74
    0xa94a2514000c280d80350b41c1842c40301031000904040d03595001460b10007000c02525600d401c114400d0014104003e0010041d08985910145a00030f584000840203140d03421540701501e960059030400c14084204002051407400501098000304070640001c0d4100c4005401a44940c130900c800030708264151044508070a100c4050603c102701c0380605c00040d111040b080c03030702403030200e01703d030b80b20300d4810b0950080070021a0303420103011001c10fa0718941d80185042c2c4002c05c04d180c86480d004172146549142c090b07905030103904200701140c3c0c2130314030b41503813503102016640c510f18098000d080c0c3e82000c481185031000295171403480c40e00304c0140703c6420400c1c00c00d420040480e5410140e850303255110b141c1008250070369403102d040c0c4511000d020341d15004041841151100c1da522003012200d0340440f012214080c190843c1066580c0500c551801030640e100046e090038107542d202c03441607000b40c00540302c200030303401c0c00201c044000c2e5079260001d507210041c0000b000404140585010301 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 939205026 1250 939203776 939203779
    0x6110c120a030b092202010e030f010c020c0a320901031101121401060e0f09010f0501020f03032404021210080d020a12181203050a11031306030b1914030c 68
    0x1303682031003110003040c03000d512084080441158a104e1600c0141c0d030550b400d884040d0140104019078400c054198003207040c0d00e03140d80a503090b640c10541089601c102501030341c0700b01128243c2c10610050001408034000486001148003021001d00180000400364000c90707030b940a030140d940e455640311003950659400400c0c288080242c04040d03507800003050003140701708641841c41a41964820300d020304807600140c18944156145e40c001c0308507020602517a4003610882040c2c1d4103142002007101d00c58810101d510074490318041246c06150a418601980b2a409101c112049004168194019626a802400300e10320345002a401c042200c14040c0564010020480202c4d000855101c0e48030782c5481c0805421041804a66400210350881d21003016030060840800d40c0090090040041c0781c3c03901c0d0b1400d410760710050f41d41d12504046840102d120707202085094003a402c02c2e29401002007020010404880403050a0400c0b94048505e248040b818100103040038040d01242400 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 939206276 1250 939205026 939205039
    0xf0501090b0111070b0f040314061f030b070c031e0f0f050405010212030402041404050102030919080a0c1515030c0801090b153105060604080a06110c120a030b 70
    0xa4410886441e4101413040c00d0705c3d034400084800c4011642c00488001d50362291080c030b404512038840720382e1088204d960703065941400401d41c07142071880b100142240d6210b40f2040c00e590718081c080b640700003070741011424010820840c00b800070480c113a80000c0c82844d9560754030700d00340c40c5009103411420301e5800c0030320034104010300081c0d074041a16000c100c0048200d0342d0f2900c2d07034800b2400400c0c21540c4100f040c50785205000400c8010740040d0300a40380c0c5411580c070038101d8403002004400c030900c014500b250400c1f942000c540202044102c05005140001030255081c0c3c0035010346031046040800c0300b41c00c250030300030807101440e800301809201c1e0003080100c0c2243c0e504400c6002c040d24600729405a803c4072030180c0e8a11045a00322285210f803c0340355420043c1c82c2c940c021140007008050760a03d0005002800c03c075046e1000c80315000c00401c040701075071725280c0061641d001e000c626040b007000f8240d99500e0401c5203108000c044000c49a440000920040842e1801d00c003441c401d02 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 939207526 1250 939206276 939206297
    0x902091f030e250608090a1703150306060105160323121e04080c07030203100506040506040c0503070302130b0f03040c0602030f120604020d05040c15030b061b0304090f0501090b01 79
    0x10308480350343c007541c0c0a418004010b454070fa400a00d4509007890041c2406001e1200c000d070f81d03600801542c042c140501c24011605c0b0b01400701529500100d51032070004009008003030071805000d510003900d60080c204802c82d0050513268030260144907450218041000840d03041d4107010503200d6611044140340c0d07510f4891203c081d60781105000e88040e0108401260f038280e00c00092000e040110350003811205134494882e1154082d1000b11500e41c491441c00c0300140c1d0340c0c2040d000740ca0090034280d5a0500d90b5907499800d900a421011100c0e9140c188a00d012600b11900002002500b003074090342c40d00ea20301031809010100a1f50407e17002c540045c880009400b03401c0c001e41e0746165040380d00780036a03a501c4c0081030085c05008101da442c01d04060600050001e026455000c1d40d4800f8000b950440d260003094050b00c1c1221800c4e82c0100c4200240e00390901462110140003030100160f80c6400d50340e840781810748004203210b164959882e401001460010f100d0401036032804e007090042c11 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 939208633 1107 939207526 939207583
    0xf120c08010f0b09030c132306091807060c060e0319110c130f0e1b100c03081812040605030415150902091f030e 50
    0x240304160010a039203c00c0403c40e440664094000c149010006050211442c3c1310018001070965035500c0c50080000c01103605480b10f81c140402c0114140130040007240280a00480502c45600340301552101d0007003005000c0700d600b4144036281c0041410064060144e00400c04114040003681c100078030001180c128541c03400780d803188061810307205241d68a0f410381c0c1000c2e40c008564460714a40301c846030014801c0c2210100003180d2038005c0c5030310601e41049030100e02c2c07111030041c2450300c0c141001d1088580c1c0541924004440c4030643d18060042100600300721070085203042103012568082108600c0445a0054980d8469032a03900508503001602e0440e160b5081d22000180540d80d4080d1505042e94078075150034851601507100002e6200c0400b8541240b564450504881030141d0368401202c260f84010800c0156101001c1c10030200c0901c481400700c810b00e0303c5024 = true := by decide +kernel

theorem cover : BRFrame.Cov 939028776 939208633 := by
  have h0 := BRFrame.cov_init 939028776
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939028776 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939028776 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939028776 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939028776 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939028776 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939028776 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939028776 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939028776 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939028776 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939028776 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939028776 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939028776 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939028776 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939028776 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939028776 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939028776 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939028776 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939028776 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939028776 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939028776 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939028776 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939028776 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939028776 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939028776 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939028776 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939028776 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939028776 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939028776 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939028776 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939028776 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939028776 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939028776 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939028776 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939028776 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939028776 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939028776 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939028776 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939028776 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939028776 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939028776 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939028776 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939028776 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939028776 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939028776 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939028776 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939028776 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939028776 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939028776 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939028776 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939028776 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939028776 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939028776 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939028776 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939028776 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939028776 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939028776 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939028776 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939028776 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939028776 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939028776 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939028776 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939028776 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939028776 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939028776 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939028776 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939028776 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939028776 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939028776 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939028776 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939028776 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939028776 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939028776 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939028776 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939028776 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939028776 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939028776 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939028776 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939028776 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939028776 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939028776 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939028776 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939028776 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939028776 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939028776 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939028776 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939028776 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939028776 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939028776 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939028776 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939028776 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939028776 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939028776 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939028776 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939028776 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939028776 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939028776 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939028776 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939028776 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939028776 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939028776 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939028776 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939028776 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939028776 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939028776 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939028776 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939028776 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939028776 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939028776 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939028776 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939028776 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939028776 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939028776 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939028776 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939028776 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939028776 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939028776 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939028776 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939028776 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939028776 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939028776 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939028776 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939028776 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939028776 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939028776 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939028776 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939028776 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939028776 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939028776 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939028776 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939028776 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939028776 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939028776 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939028776 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939028776 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939028776 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939028776 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939028776 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939028776 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939028776 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939028776 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939028776 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939028776 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939028776 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939028776 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 939028776 ≤ n) (h2 : n < 939208633) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
