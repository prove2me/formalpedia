-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_5467
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T15:57:35.199849+00:00
-- url     : https://prove2.me/submissions/07699099-c21d-438b-a063-1b9bc56c341a

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 983093525 ≤ n < 983273381 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 983094775 1250 983093525 983093537
    0x30c0108011806080607050408010f0c020601050d020f15120f0103020f040906090b1f080c100323090c09070f0e120c0307090204050306010807080a0204091403070606030506060f01 79
    0x120100101400040c0b680300310b0840821442d0343d6011060070124169818800141c00003030078400c01c0f4090284542880080000f0400c90400c664029110f58040c09035038402e030b1031506040295514402d421a0418009140a1440402c43c1c486041980000382d10050240520001030302d01d000031101e641201c0c2c02802d4481d213485440200030041007244012506141d1301c03412400801c0c100c03000c00344a0205540385100c505900303201403e610503998010340c0710b03030f1000740c44100f00e4072840c21114042c81d450601240410036280e6981c45110b00c0010110244030800800108100014915951035800d655414440c1c444100403100504000c0d1100f001c160f4280301c055031400d004407106000c03507210003611400507269000074180800c50b4454041030360041020f1000745003c0c403a840c0180245030080491500e00951280c591441c008042d05c0399a0712101c55081c80070100602806242d41c105990742c0d1412403618000800c002c5c0021b403203d101c5e0b04009811400c1c0399a4030480750300e05031078039 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 983096025 1250 983094775 983094779
    0x3150a02090a1d1510140705071505121005010c020f01091203110105070e010c060f3e031b0d0f06030b0702060703050f0c03090a0c14040b030c010801 66
    0x1500658445901c80ea0401d10b100c40024030700002c1c418020a03c04060b6101c00e080c01d22003039200c130b12111a8030591054504400c10021160841440d090342681410131603114600c50808508244959010582c3c1a00c08110303c4507182d4010000c0540b001c00c0e520280103034443c40900700c240380e1b44d401102c0c0442c00d012002c01c003600d00060545010f08052401400c41070b01e580000050b845400001c07008911400c40d2210307290404c0c05015408511842d02100341001440000c5c010700304c210000d400d1035561010094810501d4002899191010074603000d0100030402c0c5c0400390641c295540441448155910300704c001c8a130842c1c0c010b84c3c41d4a0400d422100b1001008842e0b801300d500110181da0380c40030614080d24038000d200045010f01c01c40784031840c107590064101600244240d0805142c03008000091084005803a0459000082d960b280d0751001191450b10040b01c002810840c4d41d82c0000401d00c8818001c08845241036409115004500f0107141d41c0700784000c00320307001c903500d0001 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 983097275 1250 983096025 983096041
    0x40f1a010b0a05220906083c01240602010506040b0f01031a0a08061905090303010303081906080c1021050c040e0403020105250207031101050f1303110315 68
    0x6000d07003050807460680c4c0342c840813411549091181e4480000b080d26080200314070f1070700344030b101c0040000c00e140881d09100b500c05040c0c1048402800b08815014021b00c00c0a14804d41c032020060b01c4091510b48000d999480202000030307203120782c000560038040092042c4c00e090281003100b0a02802c00300c9840b0001e401034003e814203001e01e03580d400018445000c0f55a600060034010720b0900003520b4503040030700d1031a95451402013000c050f103042c1424001c2a14002085a0450760507180140964a0301002021940c25440c0c940f645542801d402140e00c500c085807117492914110303484c200000201c0b40982e88008041031248500300252482045032000c3d0f00043d6004403454040c901d49074640500902c084001e48003580180e40d00c2e8204480b5443c0307001c1c16003819000095588103000c0321000203550b0412400010119611a10782e0820360b4050001c0e80c00407a1f1003a0500c0d00d60203002d03840c00041005100640380329400c02041c0c2c955080209204175216110b915556840d030350405 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 983098525 1250 983097275 983097277
    0x3140406110d180303051f03020d060e010e010e1c0203041401051c0e0105062e0e040603060b0a050a0f120819021b0306060307230405040f1a010b0a05 66
    0x205000680100b00481d5161445a124008411039140055052620030303080c0102141e00007080250901429507043d80031800c02254101180d904a52036080c5c2c1c19a4036155000d000c8900c02c0c84200e40c20034948920694040d0001000b030a1101c0c00c403054503043c0540d102c08494560504809a041084148000070201a4902c81502c0604200b49030030b0400045244012190300c007503002d207a81e54003e00c2461800e025640d044001200d42c2c404104040b0501c082d507a103140301140c0402608045030399102d00a491000d440c01c4020020825195a0301744075003d000f002405602c40e640300e03100414185400d03c005c0007038807280314070308400908060030300d070b80b03e10030440c10b4840b03640500c20030080382846816012608190340c0540200101c0d030011a00350714640036014865001a000c012a80d200055004125106100705400c0e618418800e482100486003405030001d0401c010030061100c03a0403042d2010740f0030407041003907403441c100d031a107800c10070b015000c05071000f00407018810344540 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 983099775 1250 983098525 983098541
    0x3090d0605090f0a0308190507120b01030609051503060f07050909190606120c1d012a030e01080705210711062a040302090c1e0a05090a0603140406 65
    0xb8084074900d0070402c0c515840c2146005080700001e4803032081003411042d011009601c11075014043c05079040c07125014000d426072050742c003d0341d507648030b185009a03c02e40007a40144102e0b0820400f50030302a14081d9984413800845010b0700c681c82c081419101e44084d1188900c0b0030b40d4896041403040c2d0200540c100f405090740c2c0c800000e200c80d41003c410700e40b142c1001407495407140f02c00c050381000160103071500c404840e401d1002c0903010380d0101c0211015040130b0758003460040304401c6010124820388050301040040c0078880d000800401da0800384078500301c03000741c0713400750325079240582280c5a2141e5111003810140b40041c05c1c03001e8031088005034028107541032100c1041d035440312142c58a40c04031140300048041392075240040c1005455901c100f03680100c03e510306825500420700100014140d00c0710040000707042090b0441c00200400f11500c0d08854580da0300c2c21100040c025002520410720550a035540041d015019100d000c030510364100140610340c0d6a41c845c503000301481 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 983101025 1250 983099775 983099791
    0xa1709030703080d0c08060f130f02040f17120301031101050a03090b070216050409111e1002011e020a0f030b01021923070b0304150b04050103081b03090d0605 70
    0x211000b000043e0024050030602000c043c0000b9400c403055001801400f0181050b07002e030b60092010f0034a0703103a40b4501000c441c0e0201012444150700c10004001703108651001d0f043c20650314001c501e00031064010601c00000c00c080722030b0004000f50810341e5100c00c1c0b000404000701014190203950240010704483d0045080029000e10b4035110081010000c403010001030704403412000e0342d82012076030340b0054031080d10b0422080750782d65075072805043c212141d107110317640e151000034048089106450700c60700017804030a03040d0204400070340644812122a003941c40f40c81507075a40e050035403007a80c281220036551400c1d256001c0c0e000b03030010a40c0154490441c0180c94024100e564109400c040581c0b054221681001c0c0b405082d02c10385040100e9440581c004010403c03c034450300041d40c2e00140c00a1030484242e0b1032111240060a0b4180529081030500000009011040010709079900c0d5201c01d02100d040d0400c513003030700d900c14248540d034050300d002010300101c1d81c41c1e0f00059200140c = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 983102275 1250 983101025 983101033
    0x6080403170c03040213021c0b0a12080310081207030e040f0c1106060301020307020a031209170403031b120c050313080a0c080c0607082a010e010e0a170903 69
    0x7a0009141d00c181080b1464034030361400206010441c24082c0100025080001045043c0508400d6101c0700039041d04e030041600361500c0003003555903a00c8181d5001808580400d800000c401d1409101540045036084030020550200140c4001d011400700c0b040382c00c041c40c0d0b610b090525079054445680e00b60016401c01d55501080781108414810b1b0710f01c10046448812440401219103450880c0080c006c5001b0b074010710034008105e80010b2201055039260030300c82e200600a4842c00000c001e1204041e21400c000703015800451060001401680d009545e20603030504d040314200e003002c0c14004014004e0f60110141c144403441804035501e4188900c0a580c41c000840343c4000305407103d500b00501c513801c140c0b00c0408000350543c1e0740e0000c25611000d85000618140010114012650098210440000c0110421814441200780d1201c4888050740070203104660b41c0c001c21440d00d00203030302d600e40b07901c031310000c5c40020349101c2c80c50f44480740e10405400c83e035020307200c3c3c4c20104009805110f = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 983103525 1250 983102275 983102297
    0x9091b0d110408010c09231306030309060801090903140a12090804050a050a0806040308070c0f0302100f060f18060503030414041109010e0f0a1208130b031006080403 73
    0x22180c0a105414420010240c0e11a81030a1030582124184540d0005210000b80200520f149441d241d1511490014106014000b4000406d40d014150041c8e020394500c4e01c40c000c0300305074002c1100307015549665201c80690781ca92268604403940800043c010404800d08149500803545c0142804022860320748000d542009042c00ac0c0d4403c00740c203c1d1301400108092106040452a0314024503007203481c00c0025162010143d142c03080601301804000c6d900d00041c5e00d06000d540e0f48440940d0100440201100c1c5040007901c60031480205041030303040c0110003210344880c0c0180f8080e6241182d130104000d10388041190741d20030392600c08008d5511100300003540d640a00140c8010220301101d5038020070440100003c9510240d0b1441c501e050a200040345a6844071840382c50060650b1003070b40404000e4006011918a40d101e0304010307400100c403408105642c4058030101800031240380784991910042d425a000840700301002d42146601005542d11522059422a00074180312600748 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 983104775 1250 983103525 983103547
    0x315010e10020c03010f150608041703070804060b03010506030705011238180103140a0507121e02100c0305270f15030c070201020c0306070206011a09091b 68
    0x1003441c00c107050260f00302c40d08041c140e007400c0c040c403142c10703543d140108071414503914401720213403c41c01100304212801002404200001c01c0401070704035154415a2645089600280f600b003003100c0450303030141400e01c80c0c216400c05004040c000e000060140c07020604041c011107007203040080700d03031010781c0301d001f01c00341d10394040c5040a03c000d2400a0301c5c0d50100300000042e038610309d0215503008102040034503501034144c00c43c05054030b90010303410800602c03103500540380c8182c440c005070060085910001c1c2d210143c041c000440341c41002038541008890103407a141007002c503000b82d00581000c43c800d400354460011200054800d003405401d100002e031100141344600c4c05c030150003206402401d401c1c0d10b8800c0b1842c1001c1011140c000d038822210842040e14000902207880450700402d94604680c0203024880c49810081d088800514100d44000e5464400717201d51080c40003038120350312207402200c0032039210810152110041c1d403551030b403038601d94a1070405500d4550050000c00480 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 983106025 1250 983104775 983104789
    0x11190807060c0c1b030809120a1406060114041203050f070b0c04061d0a0306110c060f0412050c1906180606030b0c0408150604060512030c010b0f060315010e 69
    0x80d07907540d03e610320740603a0b20300291080c144621040242d40b00380401c00004401038201c1d01e803030708185c5048804916880c00d4514060441c04010820020884000600c0c071001401d1032040101360380300c030503403906052602c40f140306900070080012040001d00000c0b07030182005160010719609481c3ca00185900c0e204196074060306c08984540d00094100310082d40424052240400306815030080c4003403030b0000707024504500c030041440fa00c4941d074030303851822a400e445040c0e2403441903030480e24080710800d90113030040383d089411101504a0203a000e12410a440c1a242000001c00000510040b408a1600ca00704120b8a040c4c65990440f011034260390100e01d290301c2524003080c82d0341940740c442c68101c80101601c3c42e030f06040c081000483da0015901c140440d80c01c0c14103480d9210703200810040c04480e0881c5030060503140c00000d42440000003440d2203400c0c1e4008000001e500f108101c0b0034007041410640c094000d00115480d01198103480c20461814140303440b4010141020980f2 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 983107275 1250 983106025 983106041
    0x24030816051f05070302091e270a0c0f020d03150b04062c030a020d05011b1805060304080702090709180f200f0c0118211119080706 58
    0x80d20442c010740038101181d0140c40d41000b43da050a40c1080b03c1e442c0491a01540c00d0f0110903914800303001e0500795251040480c2c40b046201140c0070795441600900001e125040d1b0f220030b9105d152200700f0150a00c0744d500700200601c2c607405050080400b0341c04402402c1d41c5000d0160301403582d080014100141b10040c0b0040002e2744800315082042d049001c08640100d00e1140410740306008450a0340e00410031b00111135040312084c45024031403d100340184021500f20080014000c902c4210355008141584880e1006500500d01512a030911001e80030666004040c11428007003140145428074180d5800340b070902d062000c565660340b114255120200103000003aa944205001164180c004e8103d018000400034030503442c40003c003d0036200d1041074001c020004912650244806c5d04064484840c81c4814402c220040c02c015000c070040d040380ca40510703a01c481c19034445001c0d400c523201820044018140c0703000103041c0340303429080c50081111490740c10400d28002074428800c08034 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 983108525 1250 983107275 983107303
    0x30406060e0604050603070923100503060a0c050d1e110c0c0604050612060a0803030c0a0f0206090d08150d08070209130b04021912030e042403081605 66
    0x148103240802030303040d02030050490b50003030741404100304207070300d000800908444a440000401070269041d5011650171540d086107980c040c0400e0203940300c405000303441560011000d13118503481c3e500480c41240d040001c034802003034003801511020100d6500410f1403981190524002c0c40700000040201c0e4860443c103842010041255400705e8401c000350221507105a85507443e2a0a00c0002071700c80c0a4099085504482007002079150388405098000600700b0030111380e1203040a0302c02900a42080c00688005156103200304e00300d900c0011301c2d50060648101504005c1d15552048a1242004101640c050211500c0030400d84410407801200c1d40541011030710340160380b04016050380c1c090640146103001e05105000b2411801c04035400c954100c8100e18105d80007040c40603840000d51103100708400c41050401450b0704002001208039044600b0405d41c00c0160002a1051102d65900744040d0950018030000e51508014007000ea0750030604c40208565603980fa241410b02c106101d = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 983109775 1250 983108525 983108531
    0xb16060c020115060c020a140a03140109120c03170403031b090f080c1807020106120b1038070206130315050408090919020d0c1107030b190b06030406 66
    0x801440126218002400341c03490045a100b0850f00000c1040102d0300452401810244e00c0d9040c8d03640d40c1d0300140055030310003020700102c0f0f590f0407014024101801c0582d03080707182100501c2d519108410108030a0743c151aa800c0c0c0c1060070309884501c0030001d10440605039034580703900c18546411024450030740c2596a034150f50f800d1106c8200301d1141ca50203000c1e240d000030145941591b46c400032145001c00c50a45101c16130301c0c00d0040b400360440343d1200026215000360407040c460541c039001d00c51000341d001820300c15a0790100407140000200100b040c210b08910b01c1644c01d1401c6908122003d50001c00ca05142854000030015070021440e1030211040c00010010440032803c0c0310388a21036008100901d203483d80ba12141072082c9070155104050600000d0394503200c12200d007c690282010441d22680e41020000c0100f507150b04120108800f60405102e400000a941c001e880e030010808283e62105ca41501e2050022140e404d0001c0e10340c494002c5075224500510702c5140210004 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 983111025 1250 983109775 983109791
    0x50a03061a040f08121603090f090204080c0a0b220e0903070510150e060402130314070e10090506030f01050a050f0601050703080c031f0801051f0303090b16060c0201 73
    0x10411250250321641644d000110041909140141503806e00084a94542010032547c83c085070400c1d0075400184a00300c14103408543d848281c0e01420545106104441d07000a5010400400b40310a11401099100800000c0854980b401850682001040c0b41c2946c40c1e45034402d0148000f4220344104060340041240428010104000c02250100400405c0301200c10650f421030b896581c050700003090314100100390710380c0712035040f0340080c0160030f901041c050301c901d001c10404200c9184440d09224001c000718240080d6410103000721000c604c2d480e0722510704a0440b0191500403c129818000d880f8000c10155080c01101d1144140c14800990b61601c80004816200080c21441c10890107101c00c41c00a074220051507009000041c03030741d84079500c07200c030308034181c9a482481c42da505000c0000127642d03105402c068041c2e0011a110701c0112203112080034030200c3d5202c0580021a9031030304000c91403d501c001c044640514038412100801d0f62500b01c269100c403d0400c006030354912103 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 983112275 1250 983111025 983111039
    0xe090d030b040207141506120a0204020a050d02031603060501140316050f03040f02180c0a08220c091103160503061305040b1017100b06070609051b0d12050a03061a04 73
    0x40e947c2d11100c00c981e8174141208090380c4c143d58141550000340142e60000302901c05034002c0003030b0350900105400540d528030f0300c240747c24003485501207180080f03801c2020105103507016600c002040b10319900b109013107640c0d1421180a0300c084014000c03d000e001c0120340b01140c103400046100364040c00300ca031b94489003407041c02078003550b400344912401c4507002840b484000920454001181520b465410b07034482d0b809a50400400201505400225040100400c64504a11030403108003000c1004440ca003840c03156920f00c0f040b00d04902c640d8407813800032001406000903580141c0058121110300690880e0b0f0b02c200d0b0000c1c0e5054a40511a00402c0320860649900001414440c20061070b0100b100c518581d8a07170b0000c03440b4010b16100c03c1340704500e0b00c81405903050300350000d0041c0542c120505000b07440d0380300165281310004408181c10000e04011300c8664240368017600d801460480b04034100c5994000680400070182c03240e1002480c16909401d400040c04140011550740745040c0c4 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 983113525 1250 983112275 983112313
    0x30b0409050607092408060909151f08030306011416020a270b10030c020c040203070e0901090b0d08090409060608030306040b0d050a0f020d05010c0306030c0e090d030b04020714 78
    0x10317200342501114003c00700d10341e00007016900100c05981c9020030391520441c003070500c1000d2044068041c000d104000c0c0ea00095101c06a5104c448950300c402151510804c1d500c80c4022222075021a810030608001118031600030078118409240409051806a000515401c680c0c4d0120144c02807618004c0386500d40c40301200e090802180301000340d400b003100442d4100340540b10704400c1c19521000c40f20000e009210364022010300500c2190b582c03400d041d01a09951160004a0207030800d0400400c01010707900c41c1d80714060000300311a540e400030344c3c0c50084d1680aa09082d8000b621180c045001406a01034403014164840166459103404018041260101c0d2005842003100c0c207406000b040e0b000c0fa0500400750460210842004580045140364003001030040040d860419130003005a490360003441502c0c03049081910955031280850120b190a882d04403060300841014403000740240c0c064100c088010340050300300201610b680020b03c40070000c3d006140c000000d4400c46c0607180d0 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 983114775 1250 983113525 983113559
    0x100b03031606020d02040b0f03070201142401090305190b0c0414090903070c090c09050114090f030120091206010b040306050907420f030b040905060709 67
    0x60011030038842021021000c02801c100050280d80d8001000741c09810203404881c0030f0884003002d0740d0381c1e00e00c4a00d14562039104403814801546096081c0b07069001e078108590060ba00c1d940c3c0d1040e4178080d01e1070b40740078602c1c0199160610206800c0080026014800c500c00c0901c1400c150700d1040140c280481c2610004256940ca00340421051000c543d07001e818a03400a801d441240090341c3e40100c1614601c240a4081c0c0015008800000e036554181c100c401c0f4001642c4e14481007540e200c005485d07411074180410310b0240207214103400e07410701401806500f44000c0c0007017044d8801e8502d1010459904202c41603542c0009480a00b50500f4811401500002c0e0010300540d0302d001200c4036180102d01005201a8845010408220003049504050241005003005480c041096000c0c0c5d8403a1504202d54860318618400002c3c141c80b00c0f106000007076440c5c0e2a480002e00e10100d005100001009a00ca59660404004550300304666846203070b00362a002012130810010b094031915203 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 983116025 1250 983114775 983114779
    0x403050a09180c1701150305060a0b030c13080111090d170a09050114280c20030c0d02010801050607050a06020a0e01090806162d0305060a06090f1a130602100b 70
    0x3ca004200610350106c8090105c02c5910380010192241c0c8005004282180d0001e181c0410101c140501c401100b00140407460a00108902c1c81e40c1d40e400550aa80300000318044100051000c0c40071400c00206e441c441a106080510006181401d12403180d00301407603d4000449461052000b541c00020840421030040713501c40c1000c01c0b03445900b581030100d000c403200c0d01c20428502e40b5924040d407030306544540d10100c142100040003010b00c08408080180502c030703100755800d8a4450810790700114000d501070b9181c10f8182e00b080c0078018503a03c000303812501c51048964000101c0d005101604a9025540c1c44180c01d280c50707000180540303c02d0304044030b00d401040a0110380a59046644283c1140b070519101d0160000784c103c8401d060745141d0b440c000b83c9050440b10480e810391096204600071100700d580584c85403022941d80c2400e009002035a50f240360144202c446082601202c026044140c40c60004610340394040368080780e0084001d6804800d40b05121100f50188100d51102 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 983117275 1250 983116025 983116067
    0x3030506190f03031b051c090b031006050c0c0a080c190e0a050601030207021801260718020c12120c0a0c060e0708071409100503060403050a09180c 65
    0x180080d66016910b01d1000401380201d10744800e441409111841d0f65454010303007612038440d825020325a69007203030311405001800003040841d41e0b008120176240a200102602c0541d1420110107844591021080125500c1500f070604600c0d914000e00f8409030203481d000d08200c0803928103104100c0d503030910840c3c3c5003101d0700c418004218280c51141d40200c50702d5020405850344001a0001e104030b40c0080d40181100c0a000c41c440a04030b0210304031000c0141400e40c0c0b2120b40344016103402180c1d9040c5c29908410805c1106801e601d018030b00c078030b501e14001460845000d205a1614020641010502e4000304855011504134002aa071181c48501150b14101d4000401401511840401003a9503503680d8004d01000c010010310f40070304400b000f110f903910346460b040c188e500001c118a910070304107040011841c8240e60a8242101d001500030260b0741c4903554140c85030340000c03c960701000a5074100041000040d0194040115044400505c507020058000e003e1110a1080d2802c030003 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 983118525 1250 983117275 983117279
    0x702100e070902361003051902031806090c10080402151204050d05070b0601200111070212010b0109030206030c070606031109150105040b0d1103040309080601060309020904230a0303050619 83
    0x540030b10104017000980380c001000d81d5501088011403c50ba0b01c4207540f81c0c03021007040f0084c4003000102c161218a1030480d102d5540e0309408941e280c01100f00641c000010902000c421030280000c1d40c0c2152000f0001580810a441c6d05052500312045100000c5880d005102c00e00c407003070081580101e050300d07005180810701d8841c1080c0d80030103003045040044e130360000324680500002801d1902c1c0c41c00e0007880000d100000c0e0310300325009050141d02c10807140449080f0804144a090145013040c1c407045c207214650b800f000640d4000420f1018042c00800c52100040c4491050380301851141e180b480103c2c00c100e0510261000062807480304130114070740c004050b80c105098501302c0d81010781c07007a551150003010f90050442c92148024660010061008041d0071101c0403082d00d0404046400c56030783c4020440a40301020006504042c04a000ca0b02142da80c0091110807440e60400c3e58200f1406801a0f00c2e0000c2d10005a0010307507150107128061514040c00c0210841103060b102080f8 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 983119775 1250 983118525 983118529
    0x100609050307030f0f140105010f0b04031220030309060109060b1e09032506140307080c09061c0e0105070203070b0a18020a0303050403030201050f0702100e07090236 73
    0x258043c00040c0402d0102100c5108004069401c0103c0e207a01200c001340c02c1245a0100d80602070a01902c01c0505a904000c00c40034002d4043d9400c4a411500c160058500d82d0016201c0c1441002c40141c00d00009240c00c000740c0307041009600804070038004025a602d00b10603001110142d80046000b40c01c20402c280d1186500749070921001c44c0407881d1a45c0722600e1001926012203c00007036110440b66001c241d1070880a820b207401c5038055155001d0440d4044001c50301d40c0300813102000400e03d0300011901400c04034001e070014050262249250001c408456000e1030000c0c1c0001034100d45443c00c08211030b100780070303a070313005113150004504010303090f07076044200740000f030100c1245651190712245001e02d01a140a00c560050b0080e034165481e424002e00e81e503c240030582c09507003031401091844110741d80c0356102e8446a8082c154420004030014003074440a050300c21903110b02c07840814421001d200a00c050505d1911444168106001c2c421171842c4194002034a040354040e101e03569 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 983121025 1250 983119775 983119783
    0x3260c07290a0f05090a0b0d05101d040201091a19050a020304140a0308040608090106080613021306080105090c0f10210e1c08150105180409020301090501051006090503 74
    0x82c0301ca070030280035500000038110b64034080c07245810ba202605400024021064000030403d040b8003680c14000c903038070503c01070a4110b10780f040d1801071640286071000c201a1480181c0c000d84145001c1540d966078003407810b103440856506c6009540c00050b000480f02c40303424088120580b03401c00500703002c2c208102940724025407168006d2400c555900c1c54484e07441310349003c00385a0000001f0b403036640b202e5008280070811203080c1c44e50741c600710000c03545100014129116804080500c00000e4203039090001000154800c0c00b051038840c1c0b0042a040420700915224002040007004031210300e00030071601240c03209040f8014446100011403241d44030464000c50300284010f031180035240c920380c000400344041c1d441064020003a16a02e655100226081e000102d82d54460712612644001581c01112000c95404500108924440756016a5110580110050002030401c440d600400e00352440c003801220140d55407007c12099420311f140100c0500401c1c0740040034903040030082a0741d = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 983122275 1250 983121025 983121037
    0x1507180f08060f0121020406090614010908150a0f0b0a063f02090312070303060321020a03032c0a0506130c060e060d02180a050d0c03260c0729 63
    0x10600b51075114086d03440350f070000c40c010f1501c035000b0001207603a0b9400c000b00090b10400c1900181244a0025156034002901c05500c10421104e000315102c51904000402c1c219198035203254483c18140f031142d0712013050400824061700c40b40b88454003500381c08003404001c1c20030380c11300c0f20441c3d44201100c48412003080f07001e1502030040e61001841d0009107811149031580109410014000042642c1900808101c0f84244501d007004c1d01c5c0070355001d03410105807404e030005901004188000c81e110343c10042d0381e00000700c028100d4500080f1303408000402040702c10b04940c001c00000301044402c01c02160710540c021420b00075002c6544c2c81020a01d81d51003044200880740d0004440c507542e036004c5401d0100c01400c00c6580d1400e604441001044d0702e02c0300c0e8865003051500058038248400d8050130952b10400d03810b0801c1c2581e0340c0c1c10074410600b590400e1440c0c541803004040c5001002403009207443d44c02010401d1400b240306c1d13a18491041c1141002c4881344400904041ca1425070750 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 983123525 1250 983122275 983122319
    0x702070602011107050c0d0501200a0e0d020d021e0406170f0705031c09150e0a0b031b0705030f030702030c06010807060c030509032a1e031507180f08060f01 69
    0x111142088c28614058105201c11300062079482c10b00741d1500720641e0041410300131546443c1060204201003101c80300728180080e4001c0440d4080d0001468515801c04a81b582d40d2031001d1101c100703001080c1150500e82203c0401040b110007a10703040e4040001c1310103607605c01c0003420b6490800020a86030700728203400d80c051100e41d0042082d44e50081c0b4200e80a400b001e0b48220552040c42401000302049002060040d00700d41d02c00300b03140042c401106e11480d2100030703880b107a40481459600035845400c080d595030100b13100b003405000340040103500403860340c2d0046480344880c03040c035414000180c0c04025180d001010400c1500e412844544116800d0701b41240c0714000500820b04200c1801000d040840242031a041c110a09600003000440c06580389507d000c2c10003543d800b0891510421541980040000c00c040f800b1a491070b54026a10702d4042c04840c1001a0f01c071090300a45c0098420316100b007402e02200c41d04010250b80024120100315095260070700c0e410341d841c02041b000d1 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 983124775 1250 983123525 983123539
    0x1e0f05150a0327030f020715050c030403020603010e01031506030302120a030b100206180105010b1b07030816032606100504080307081306050f0a0503070909050702070602011107050c 80
    0x40e0859019601c940382a8103800c1c1d0f0501c010a074a00c01008190341e00b54210041805401201c40c1c0c80e10005607202900d002201886030804000800d0314542c000d480303a200c00e440200004401a102c000186000745400d6070156515411454032070483c03403c804000c01c1292800b402000400e80c00a004102c001010000d00d41d00c5070300c0c5c0000c40c041c01911084c250816a51409801840d44c001203807031160004190859142c00040354050980da42842032643c130748028810711000382445200710f182c2d03100b0070f0101e50006035650740300e603190340001090a00d01c032603440c504010f05130480c140228600b0301250003482c48565407a18070a1807400340141340184148100680c1d800e00030301c100c3d00a840300e07400303c9071540064948510710350b00c0f410308007218041c912030003d00c0a000700301762810301d81c03018440340c107215619034205d42940006103132208101104e50b002603070403600e2041a0140401d54040c008c0729042040c040c0c29200c416103903840040d403c10555020900201c1c1540150100b152a4 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 983126025 1250 983124775 983124787
    0x5010e0a050d140f0106180f1401030501060f0b0327010f0f0e1213290703080403030b1207210b2a1e0d060f1e0f0515 52
    0xc14440302694201980201003082403209000507110361000c024107240c11603c24010081e8501c0c00d032012403290464601842980743d850301d00343d402c01404051400400581e12012600d0f8502072002a807041e03c0695480001b400204603220301c1d003018045d00020203285003840600d11540b40d8042c035503141107900a9007540ea44550030b41200700248e01040302071045407001035481c0020080350304212054810020f40000d140300c00030545488032940540604250320300728801c2c01e146411180d000c0110071112907a01c03421081ca010303003d900d00959600c8113a1400d482e003e000c940700000114494001d16a5181601d0800159403043c1c84040c5140240000da0440003c52500c0800004000c0070703036078041004a0020303811003c503408001c01c07034414203030509170104003503c0303a4004c4524001d0a2a880e803604840c01c0000d00303800004c0d4a0004103207507144001e00e001c1140350400ca020000041b01c2180c0502c1c05e0403940040c02030210911400c07071420000039800124800241e250030000b24072 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 983127275 1250 983126025 983126029
    0x20111030109091416140409110d050f2d0f0d0507021302030a0509060c0a020d031a090708150402250c03080a05120c0c0a0803090102130807080d140405010e 69
    0x18655500800c481141c0041405d00030080382060b443c0203940c00f4650031510460a80703407501404c241300741c11841c20781540810f503017846040072580a098841d44980030600007180c0d020413075080400003400e403054610f10395000f081040290703001452180c0d48045154041181c0215080b032948441d410985da40d80c2040c03000c56640c402c0580c0c100074440c804030411040d002160001445946803400303854050b50f0312000805c07140034214880006a00070b6411100f903500172b501660540701d040501e10040500d4600240100c03004603030300000601ca02c010302403202c411540d500d44c00e0741d00300c400707500305400442c0001601d50303000e49484030310341804d0321042845007070420f0101442c5c0100d41c03950340310b01c1804082c00aa00120703080304490302c8100082c00381d00303076a41691a90260070000d40400c40407078482c1c1c00c40b5000034041c240e840d54200200d0520b640c41c0c600e0f0382c0040030741601602c00301c0d19044005040500500c980b1003406130b6070800b51101c5c080300003214260791090070701c5024036203a400 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 983128525 1250 983127275 983127293
    0x9050c090a1e02090907020a032a062c0c1e010302190224010e0402010e060d1d1507020601060c0f0b0403030f0501050f06040b070807120804050d02011103010909 71
    0x1001d20100400b420021040d44594000704201101601c1003600c1c0d490300d820482c1e48501d410400340010709000500810030001d0f16201c1183e504c1e0184a4803c0e403aa500ea64040342d0280d100e0024984060541c4001d044c0c3c1408404150f64002016101d040c6000c0701081c0241e101c0e1140007040d000e50070f0260f003140e000740e0540d00d400e0b5407800b0380a1014129038000c1c4d03840c1c0d10514120010340d62441c101682e0391110344030074140c40106040035500d840c2c990054031501c42c10820940d05c007906014440054425200380300030703140c160030492400c1110f591818100070000940c4007000900d9820001025000140681100ca861030108401e40306810514078040e0488402080091241d0500c020302d5859004111000c0740a02c00308040c0c0d0703a070802c10052042103030740941c03c41e0061104020720b064980180c105140500850307860a1150ba46210f8036081e400c4174003010880e80c5042c0011711600b00b28040c1990041c4c0001c1100002036442041c0c940030521550f00302c103480b03005034010040390798 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 983129775 1250 983128525 983128541
    0x2a0206060d0b1b040f080709022a0106091104031703040f0b15100503070813020a05010518120105092a0904031e05030106030c030614040b180c07110409050c090a 71
    0x40456130315a51540101c449021480c42244950310981c500414030a04510840e1034564a034000304040d0302c0c40341c1801d582c4082c0e46214a481e95a03d0200144000f5075004840925000204542c2d4032070440c6080d00d00011041c2c03100800b0315042c010000000c40d0303481c400388001d80040404e109941d44400220b001f10702c1c5c503c604c0c0c1110700340b09810465038211010398058a0651242c0911b0342e0750001c072120781c0510820203940f00d090403104121b15400303a001400340c080c00c51601510103101d500441c89100c0248010306180c1e5403601044000d84041c0460a01d884490000109200c05141403002181411140c10310494841004c00c04040c00384202c1d010034a101c401e406100d20701c410015006800034402e65004ca801d207002440392610901c0b800e41a100199051200c0c070700d180342802300400440500940003039079007c840b2115980c0c880c25034496090121000d58030a29441c01c0b000040c402c000c0d090190b428451a030b4009a80030450111500040e00c84000a6450b0340044000d444c0340 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 983131025 1250 983129775 983129821
    0xe0f0c0a030b04081608180f0109090c020a1703011a030103080306150904090c0e0c121b040e101a1c09082709150a090f0603062a0206060d0b 62
    0x30071445c2c41049034980141c21560040c0850720043c02c071a0041c4840c8021407002035000851841091015400fa5400129000c409104845203111150794005d401c0036041801e0070030603c04001001440090100e44103040740b11304513182554510b039100445400007802a6105030709072000d0300301e1900c1100a0340c04202d0001c2041c04413000604001810f40c540b4003407024800c3c04c450000f420450702d40201da1564606a0308001140d4807000d20401202c2030b41c00c0b0000d0410700308000a90058000781c154011070340e070000494840d20300704540403500d5941200c0d51a0820034403101003415420b00c040210041e82040116010900d8980116140f1600c010007188460381100180c000c40908a0070b540c0c1c2c04140e4035460503444100d003401001d1034a0102070b80c8884946820700c2800c5a40d00020000c0c06080b00c0403038169103a940340d40aa81c082c01041c015900000409400341b9038180002035000000c2c00502044c0c2040004910500001100a440740e494200403c00c41071003424102a9070000b = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 983132275 1250 983131025 983131057
    0x170a09030803151e04050702030910030e0a1202100605030d082205030c0705120106121e080f03091603020306180a0606030503091008060a030f060e0d030e0f0c0a030b0408 75
    0x40c07080b0b0002404c2c0c0a40d04501640c178000000380b140740004116044c45000130010f1a00c100d4412044014103644560000705005a910404c0001c008a054400e02401500035100300d0003154101c20403940f035580304902c41e51100304001d4201f80c002d05034940003a20040084501c18059a030401d100d03003c46801011480f002450041011001c5181e0007550007c0351b0b40c61520741c48403412800c0c0c4000d4007801382021040620380d0b0015580b02160315011014513040c00e03001c00151501e1a0a4100d00501ca003016800810481e80a90900c012400036044078000544141580c0101c0e40c0e542000f8084408a840401980485075041041c4090994041400e00c122500da10b041d45d03d170340000241501840c107400c210508540154412449540e019020b600e0051035a11901c0080e4958003099030442d64640c00043c00100071f100b10700c0440610384020602c400400b0f0f90b60b00c1c0c0700300580704103625000070300414240d0741c0d14000c11040700d4000700c95140b692118140980340d0b01c90035205c078130501c0c0 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 983133525 1250 983132275 983132299
    0xc02150309010213140a1e17120301030c0e011221031104031a060a0308070b10080615010816120c020c090a0509100501060c0209180706030207170a0903080315 70
    0x7480420552081d1406c0da803030341040c1e503540d041c0b20004100c000c1c480c0b0307140c0e07041e981880589010343c6442202410101140c48401c034100155100c4c2d0300a80040d070300540f00c0c22003408840080b1004500401604024580e18603c03a150724921001c00d44464101e021541c0c0c100350381e14400c4e00060614541010f041d50740703070f03a00d01e011684520080c04551603c3c0600c0d000480350719040c00312030212504070904520f40703502039445524a81c001048070a4050542d000480d0240c010484076101d5160b20b00f000018103003040024017290300060103d2420f981d00110f2030310350b5620001c240340c0d04290302d10101c0c2038807543c0f50a9081190410307005030000301000030000260841c1d040b041c000c20442c41a0390b0460001c10000342565400d01070400032035041d0301c2c0c0c032005090104180390320118035190411509420080c440c10804254082c000098000c03032407000703014021001c0d4a510390700c52080c0b41740c10000c4001606580252101070450380000c0300152500386010351a0b11030f900000d0200016603 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 983134775 1250 983133525 983133539
    0x51213030e130e160305031603090e0f09010e2e020c120721050f090406030203100b211c09051c060c030b060412060f09210c02150309010213 62
    0x40010b0700f20400600c12100040b145446075407155058030b4000024500d0071501c0d0080d41404103c81c00114200601004001911070f03403c2d100d03a001d001040101000e03420001c1000303080d1507842103080f9068111041e43c8900c07190241540d6032180c01c118480808130014a10304000740111880092240074402c03010b04041301c504010903e00e44140280402500c0b00a001d0a43c0183c0d484a080030400411120442140f51006040740100040001c141c16803a6404641841c1d0406020307165182c03501c40e14101403412000074508080c0080450710051200d404540d6202d54000c03107000c03440e082c0c00503030800c1445420030030044c2801a003691091044908180103a03040d00318241c4041c0e00c0c20030502c145506c0b9000b03800000b0002090b450401e0b08101010400d4409418101d900380e41e50741d5000644641d40c01011180e9000d42100d0b4080f0481c1c8207120b050010f00e104c003108201e82d01040600507511b20841400c0d038141040090b40b00e07a80e000d56140240b18641303080c01c070350002d613200003658 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 983136025 1250 983134775 983134781
    0x311070f050d020303010b030604050402031e0d111204030f0f12080604060b090306070e0117010e0402030d0f051c0b030f0f0c060a1704020102010603080301090605010807051213030e13 81
    0x36501c50011282c000c0c42042089031640428010489640700070400f10b8520320305604184d81140c0000c0a0b40c6c011440303038003410040c20883c0b00280450f08004100010280c200b04001058254040900070600408440c0300071441a80070007070040c10920707050401c0c40031800c01a0350995020f003241c20000e83c0101c02901c2d0480454a03d480340d403c22001003084a240802d4440c00c00014000701115124007005654880d42d00341141d0400500d448001030101c003140410307000f0001c1c42d4802c4540e041ca8014581040004100c06081c0702924916208407076000c0c00f250541c24100040b0106030f003c0c04183c001800144e01004e80c50700c00d0000382001c0d6038010400c942d0b09003544c411104c188200b4018030045004e080072050209518170210074080100040080d40b151051000180f826100d9031580c0c0c450308282c02c206a1140d03540824002c2d543c0050324035412607002c0c103010b402d2113070054407506141d030000c00085d000c2a410030388404050058643c2210950000c00104071030007a4001d030401 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 983137275 1250 983136025 983136053
    0xd110f0d090b071e1101330e09030f0306041b1d031c051c0c0903050114012103140307020309042a0f0509030d030b01180509070f031107 60
    0x200c0308000b0910184c040d10f8519114024400c001102c408440c82c19115901a1503107403101d5501e48642d0304042c41a48800d1028102c01d511064002c101c07807040d014082c880d0340040400400d41414440c007680e0000c191041c10a0043c86d0b01c1c0d4a44d00c0d03102050281004040650000312680502803626401c50300d5103420204000c4204124200b120415070f440d56132282241c00f0300c42131ba1b02c0302e030854496002818101e6a05c00e481e1001d04100c1410800c6804490760000040e0007640b00f40f04001c070a00640265142c40792002c00b2650600c01d49404058801c2c0c0041365910810852038101406003101e0740c00c044810900d59160300d09400042d403698032050045102c0c030714200c072114010008010075078003400040100040c141d404001614055044125641404030a0117045503c6e070782000940075907403259070003150340c0c046d400c00904001200d6820654009103000c0500154a610350417a80c403e005203007400045d04030b403134280c1c0240515000d00107c5040016040e05000c1d0189030320607 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 983138525 1250 983137275 983137283
    0x2a04080138090112020f030d0806030d02070614090f1e03070609080d030c020a0b010308070606091a0603060a031a070f0203180f21070603060503010902060d110f0d09 73
    0x19007000400c85011456040031101d681c0071070420010b000d198002c40e4401d41c4c02d48007405405507010040d00103441d003c400820312001803051020840349050511081003101d91600040c041d1a05240c40980305643d10750448003e82c0010500a170f442e40c1c0c00d031900310740003809080a24503200c004031800390740b80800e00040c00b9204021000680a104103210011102640060041d01c10590f20490241581440c0704003144240b40c0100045446010081d001710b201e40241503072402c1342c3c80c10b002a602c0d02c0c0c0c00704004620b024004848605025106088240b044410907a01c1d0396820005110fa10142c1018200107446103400f0700602c850768516010340b0301c58443ea10b00c203c10240807a134920034110900909201201f8008103404c08205810703030102e0050043c4143c8041d0b0354100d0700e603400000c4444669004100400c10117405204a00c0644002d4000b408101c1098002c10641e04c91001c15401180d500d030065000703042c5440c140c030080c000f80d40010b540c1d02820902040030b0301040405807 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 983139775 1250 983138525 983138591
    0xc06020a121b0516060b060f09010807080c070b0423030403060b04050433020a021011131406070c030c06020d0905090a020702030a080406170c032a040801 68
    0x40c40032080c001d196000408183c3ea01da00c1c1c491014081a00082400310499a071600d80700700f0303555a40c692000e400507404400074141c95028003000101404006001c0c0706c01c0c0b21552050105c1200c0c0802190015508502891980d442d14034003000240c880e200260b014020a602c06003640f04040b000b08201ca0082d0824410241044200411a10140d80051000b603000803500d2981c940c1000d110440113091624001e0784190481040c161b902045601005801001c40d03015140f41500c100d208008050404030300b02443c408040300c009200d030207145400082d412100c04c80d503032070070112040c1641c04005200340a80d6894100f0001d0b003140200005401101c50310490507209484c04c404403075004002070040d440700302d0004002d60003210180d1705801131942890106d00100c0042000300f01c02c0c0d60b0394002d4042c100002c1c1810350050244000100200103101c0c81c044c1c485062582031401e414203200c1110258558925486035030b02c200443d500300400c11401051b41c0d014459070882c00c1e0946 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 983141025 1250 983139775 983139791
    0x3061003031d0a062318040e011406060921010912180b0d021303110a05091905090f0d0f0305090f0d14041208030a14041703070c06020a12 61
    0x188202c0b4140c0b15840d0040d56031807042010903c80d4102c2402d000714142403003070302441405200129840000c41448900c0108149905800c1a1151055440d07a01000b0019517496680703d03425400b000c1e02c1d03648030340303000718100384103994407200241e0342c5008040071111075034146e128030702800d400702040d0782080324030b04800c5085008444000041400139400c3e00c1ea642064a41c451a411840409e05040c2e0b092003050310210026011350041d500404000782240c00c4d01040044075003c540100e030007a6240018010ba03900c04000200010015407000b240c5680c52103592880e01c0c0c80c08401c10003074880d055598050a822800b48601004070743c0c1c003403006030359a00001303698000010603507480d54030880c22a401d80e48944000d90480781e0007040c1600c0d1540d5101035105801c0c030814180d5200c0703400024000ca540181c803904200c142020b80014072841c00381c81c0c921450314810300c01c00d050403000000410840c8210100002c3d50f40c00002192600c5104c40002d01e411200c0385140821450400a = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 983142275 1250 983141025 983141057
    0x603050a1a0c09060a030b0d1b080a031d030f0a0602070302070f1206050604060b0f0309070909080301170109061a0a050a080c130e0703150506240c07050306100303 72
    0x2468840e00711110b42a00d00200c1d1001e00c8242c3e030004040340d0425036504010344881d542c035072500c00c441d0700400620322500c00d80c11070208101040d51103941c40d0343c0100d003440002038004801c840c1c4080048a00c1b0302500600000c079003010f00202c400c0c192406100c0c0740900b0007440ba0b020789201d5000b60300303d4030070780d454242d0b42401700254080d07803450f681a502d0700300001e100d5030081035020101170004511710366545001c1030307190404001011107104c04410491004410420500140711a03442800b0620560b2503503001d034803041c051458801c90180c0401da80c80b50941010b101f190b402501007000c40500c5a24001348055802030303901c81e0104000c0050b40e49008141e40095800f00d101030401e0500300000c0018102a110302c182410380c0307421801000140c14042000203602600c0d01010400700981114119003004201c1031060b00340411400070201010060980300c03902c4010280d4480b102d5a810f440d190055000302d40c14440c4c0c40030803515110744104002224825194010781e0404084 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 983143525 1250 983142275 983142323
    0x42a090f0b070b061002010e1c0219032102090a14030d0c050c040903020c150c1204060207031119060f0e040b100509010909150314060630010603050a 66
    0xc00380112000c80d004c101d09180ca4080342c8007805890000042400f03902804504041c8440d1810300100000028000c81a405000d0600c1c90344501c84400169182640d0103007042070301d0306a54404d40c1d40c038102d12078200500e50440d000001c005142c000066641c41b06540e0780001425000d01030301400d0706152100d8020b568030040d8581c0139000e0401c0310312940902c40104500f03003065045101d84031b40480161071700b12000d540f809800314406c0e40c5850004541e450000d4100303407071030008020001000b0309a80403c021080d171b540600072012110403580022540f2307050b010004044044084005200d9400031468400002c032900c8203d0b000c5030000402c01211520100b07103401822140e50400202c0c4103100411200c5414140303014403030f0f2a0050042154101c03602442001c0661350240140242c221846e00072121682c020919803412201094500548a044151b13441d0820b40d17804000100000821304108994020042e84e03980b410890f80d40d82002d4003c0c0c52070b0107104204802070040d40 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 983144775 1250 983143525 983143537
    0x110901110c0f04020a02100e070e010503030c06070f050f1305150f04031e080d0608061815040203030405030f0a110d050706050d060509010b030402040c05031005042a090f0b 76
    0x50160903108088410f22001c1e40c401100001180244e071282c2003807803450f12401d00811148001000c0160401200200004040e088644130f5841800141c8801b4800542994051007a00d4001140d20034081c055a080c0103030540f00140240c04107044222000c020103035001c5803000c0b5481c0707034580d11a4904100d140718034010902c1ca441c003008144082140518081e00300350f146491042450640d4451a049810603c0400c6001da100c0c1001c003c940380402c400c030b400004800c03240340c1721000f400c54150790b60b0070301c10348bc0d941c1e140640000701550742c14801d4600500d030290595a50100384141942c0310800800111075034651801e24111a040c030280340d0881079801070040c203003a801d12800f5145034101c00c0070320001e0380d1502c03000704140d1204c0002e03c2c001c100ca21030b000e8890600f4810041a44c1c101c00301d001c1002000d20410408070012142c19040305c4003582c0c005020100c1c00c081a50821506400120420b502c3d06030303106a50740f2025a900b1a490364038800ca54540740ca40c6124203116207 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 983146025 1250 983144775 983144779
    0xc140d09091a0f0a050904150501060f0c0b0714040906080f030c030901080a110409020702120c01081603090b010605091201150902030c0c0604050d03140103020303030a050705040801110901110c 85
    0x644001e94542c1020300c0100d50b6020004d1403600c5950b9540b0028803068000c80e400c5920b1219506005194840d9000341405080d203401e109800702c20a0100130300c20346c190240a401c0450321408030742094010518200f066082603280e40d50785882e054000d0140c5803520901c9001e100c0c6000001d041c000c0802992151140d6a001d1450508000011140310b58003800300c030f00c0142d40b05c03030080e80a18190010030050450041c003603110001801000282510749021103d0b41e000702184001e180c1c2e00c1071849600103001102058510a000e80442c001c1111420040c540c0c0c444100109003984c00001a180400c001c40da607070401544003607581d084c0c84c2c41d00d5051a441d50403000501a516207038021310f034030549102000b42040103032419140360004c19242614207803c066101c800555050103864003188004c0d000444951442c1d002c00e91700c3c400100403032402d5640340003042400303220f01c08460080012034024820800d0304036450506500034500d2a001ca0654048d200360404007140d01e903515100 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 983147275 1250 983146025 983146061
    0xf0105070c030b091e150106050705071502250e010b040f090207030507020d030e1309050303010b090105042c0a050705220906090209030601082a010c140d0909 70
    0x6542d0f02c2803140080600121030a006807102c1c01e280001c50200c0380300495221004107403d44406844058800041e0005030810608110b0390011540014401040b070f8841495a2501d900a0008909110300b4507401102c040ca2500042000c241c94141c05042d6462003083c81c030642d0369881c0b04240d9119520036081e80429914082000c0d115a80c00b80403810f00909249180c0050f80c1c1c001405100000801c90202d0303903098081c04141000d1700420300c41c0c2d0b20010208001089500c82d00c0e41c0e400140308050b411500016140d40603481501920b00424084400c0007801845014010503000400907a40d240e8801a0015480c1d82150150030301502043d01d4030752501120780c0204000c03401c5180003c5454035200000509042e091003050010054010f005890b6580c0d41e00701401d184060b03001e4000b030b511900840c5190414090721108070500e01051501c0c05101c080141d13a21655010080d05402403140c4034101c00d03001180c25445840305a0b00d0842898071840100c08aa031001784080c541c0d00 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 983148525 1250 983147275 983147279
    0x106051f14040b0f1b0712170f04080f0123010302010e01140d1d030306060906160c0603090312050f0a09110303031602070b0307080a0b01030e0105150f0105070c 71
    0x30240795400141803440070031038078081d00d509007007019030f000124030f001e080700015a02c1443e04803296080050300095019165051900085c17074a09408098050a0250080e8071000240c09020440e9841c03100f140d0722940301d07036844145540340e111407075820301c0d036500b030ce2100745d03583e106e80c0c0c2040600c50035107901f5901c59007147c00448031000c44044c1c440c18880f00340e48400900110070041c241380164900049010418003100000350710b029485013810703600602c144856507842105807a0308480c04e0300c809413104100500319008540c400700141c9044420a404030b24594940c0100c42214066160086140b1402d021001141c0045401c05014210780c40070407403511941c3c0004c02941d0203a0000c02040340c002e0002811030740140c90b40d03481c1d6a0555411140ca64041c03011000a00b07448100e14298038000001400302a801400c2480c0c0d00c1e030717941000d1070300ea0007980108400503651000300039134602440c001c0d241d4040300240344e2041408680403805588203070112420f0f50751106174009068 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 983149775 1250 983148525 983148527
    0x210210c020102070f1101020c03010504080a230f1314010909180c0b0d0c09060206072d1d0a05181e100303200c0d06020d020403050c030106051f 64
    0x40441620300c41103540821083e00803c0072000300103241c0740107181440b0200c0c01c00c0c2c00a4580400c007806640280d041800b0803001c10031400c261605c0001a04003c0b00248140049550740c401c10202c0c50942080032400500f0204410007602184103030101f03118000780c441130322400c007503402d403109400a01c1001c010f0113060b517180c000c0490b22a40c04510b60701c0e03d8155031080c9950320b00303400049031b644010515001c0d02d500c2d4042c249221140d070420301c01c0103042180082d01d40c10000c01d1a4140000b90480303110340b00340129050411302e1407803d07a0308000c103c000d00801d156001e0140180483c03007444004c0851070440d10702400c07182d00600860740120712800c20900d40100808241040c10600400c003243e00e0440c0c4074a101c2d1508142c662012810b51601078000700b40c510201404900012004882c0c0600007061444547d007119030315280140c80c900f51340030307100398400180e40384d001150020420000042243c0c18142c110002d00019849805000341142c114541441e0503510030b420308038075 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 983151025 1250 983149775 983149781
    0xe0a060c0909021809060603090a080903031c050603070807150e1504080307050f0c0d080d0615090e0f0c1b0c031903081308030c090d1707021021 64
    0x80049400e1040800342d85016035012030b0041c81c1d09100750040d10445081e189008016954040c0d42194040d0441c2095034845d03a4491007180028031107040003480002d9030f50100142c07003a5050105468100840b03114029002c2c00b41690010f0081c8035082012a00074004036694095405041404050501c0240200d400000034220b454000c01400b0217108c0c040030b2200244054036001d00195924401c80c9030085c40c01c007a06440d215a5040f80303020500696549101d0805290001802c80c1c41c3c00307181c034500b0014180350744552041d02c50740d41c0c07400c54a81c00c00c4002c0c04845400d21031107001da841c0807040d1807a0004649401301c1c00d50801c995081c0e611030448a8030b001c1250350854450703100704004a890010302124400b10011100c01c7d19013003650248041e0b47c0600900d42101c0148820381c0da5142c640405008050600d8010842040c1600c503400c040e07252542100902c249001281d500138030543c4440800e9008562031070041c040ca0b801b03000c01d4400e40083c510004145484070f0210001 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 983152275 1250 983151025 983151041
    0x512071a0a1413061103041202060f0c06010f0906060503010f380423030d03180b0a050f010e011d06131b020d140720030a0b060102010b040e0a06 64
    0x5014211640121000111010f403002d20300240030454014104a4007815464080015460383e600403c024060480b0b035101000c020355040da40039407115144402549107014140d0b04010303030700c01d0100020f4107045040500003100c1007281c08210268a409044801e440f0901401c0c1d054050140c3c20008000c80c403c429450b00b030552075413149000d002c0c2c2c0742c4034000f20000c19004403513000f0a09029000700d03c0103898240ca124400c2500d25085135003c2525003140c11008028940e4408055410901c403242c200c0712503501c000d5940c800c4c94034880d02e0004140660341c00c4501000d980000c80c0d01c0b008412803c0c10390703140134803164000340d0b103a42004181c10000e001076004511061080030038242c5001e880010b89000c16404501c0603c20380091030300e07402c4c8282104004400114500a003034240440303503e10b030400445584000b001d84d044032003040c281011505407194640e801c040c400014060350050000364028800066a14100816550180319240241d003200390628006111544407600e = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 983153525 1250 983152275 983152277
    0x610020705240409020d0c03060e070e0415060216061b06020c160605180402090a0b1303050f032508030c0a0e1f020606120604150f0507090512071a0a 66
    0xca102c42e0508280c080d070001d502042000340c0104140322100c4550107005880a0280b404010962419a0910300d41d100a40b0402c18004264405c0b421611942c01c0300140280d070b0420a842d0907600c030f000a64a1051554069150a0800011030060f204400903405a0400007484680d1411500d61400a600c000302d900314501c20010704807024081180001c0050410b40c8507192121038100620040100c0000e170340348654410030510308a59110380040041d1860008660b0320340340a5481d0585c0100030b42c00141c0148100f1000345450390000005102900705119040a5070003051901030044104034030044c6243c106200240c2410b0b12800074152240ea54a010096a04d100002c9a400f6240100800768208284000700240c0d40403c20290030417025980710203020080c0032071540f103c50252001301722038441702000c44545416008100301c0c1c12611030400c002e0404010141c460121440380c58001d940040022885507004541c0340b04a5030309540002100129080030000303076002c224204 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 983154775 1250 983153525 983153569
    0x70c08030907050a030b01060815010f0f0302091305013206090f0d05010f0c0c0f060e0321060405060409030e0111030c010618050907030305040608040212010905010506090610020705 80
    0x54665450042000031741c02901d0040142d410114018884a00100040b02016442c40c120b202070f40c1c403c104200c080181c2c50280b0311441114400c4000c0e10901c08026403003090008803070000726075544101d040310490f182c0481100c4121a0702c070940e88a81c0040c1c000301c02c945020407214244203006041c4c0050007006c1d034860200440c00100701004080d02901e40384e43d241008407059206100720440e0b00c10f0f508003000070014030358541030010a0540e0003491039413104004031070040f080003074500c0140c050240c511158040a60403c9079030084614621550a204c0455660700b01449259200d641542c0c2d003542c43c1400500558484120a10400a507c002c001c130541201d0284202006489000540382c0109280d80740da00647e00042c1541916410030740b4100b000070781007022641140c1e25030820070900c1d130303907800060300304070700c01d09030645035424110300c4020050198002413040f002105c03c003c264440d00103005400526503401d0004d40d01103041405036240101c0c410b5082260401d000c = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 983156025 1250 983154775 983154779
    0x906020c0a060e0c01090e0a0c17180709021c0b01111b15120103060e031e0304060c0908030d0f0f020712020f01020304170a090302030619060e070c08030907 69
    0x241d10300701c400c86007500c8090b6541c1c0074603072129050003000c01c41c440918007480c503d8140308020345014005000350051a130380d40c0751080070b83e018541b004480b8060780300c0000586408140c8580c2403020b002101d031f05008882000ca1064850301c20349020805030540f004295100d8580100209628000e5505000b600d00114040110401c00e403c024045103203d0301d00640b0940074024200c1404625a00b40207060121040f80303600c040c5003c0c11290040008902421001d20ba203046124052200b40700405018500061180e690001d50141c0d100700b02c2046509510740040b02c8482c40e41c0070716283c5400c100640694100d00e0b0300020000603540c1400104110500c00c1003080fa44400720481d01079240141c07030418603805028000d08c080c8450002d500d1450140d4426500c01202e4005240c18500428200301d070500c2194280040c681c081d044034081e0600f80c0950ba03440c044802c82d140340340d0030604045000b04181c1741141c041e02550f02c5607520210b150f503070400b40d03410080c50380c25248148080 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 983157275 1250 983156025 983156047
    0x330105040903210f0e06040308070c2607031805030c1002070e09070602100c0509090c130b03190204030f0b06180403030f05220209090703211719090602 67
    0x101d007128080e0301400034013012030310945020f076401c01da01c048840e0408020040800d82122602e5440019403078a02182c2c0203910f024402c0300f071076445d599800c80700d02190015583e888002010b4407406034844a0207010050046138401c0110700846806412412010640b42851803400403503034a40e00541e555103031074403511940503600312420440e5034007034042003040d1501032100c0c40403e0756001d4203100c0c5a03008000548180b0850180390b0003207a14100248414aa0038140c80c0b0455600c005005074a958200403c100d4006840381d0215a803841c425500b0860340317100b20303403c60364030801c0455168a1911601d9119400900840d0403255035031201180b010104030540c801d522035140001c00c00c86001f5007200300c42005010000030301c3c0f280c1704242080c51504000b1401a4111134001c031940e114002c85007850381c203500051020742c030314a4183e0041302c41080752a0440351592501c0b410740041070015007458041d0340301d20920101c5044200c011040e9044900e9031400303454094a401c000c000 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 983158525 1250 983157275 983157317
    0xf02010f050406360807140a03080a2f030a09020d15060b090612060310060305060402090c030f07030e1609140609060109090e1608330105040903 64
    0x41e04a40c0b20355549001d0080790841581e001c107041303210010040b594050144060680e080c21005003150801080760802c1000d03902512480c00a410b05403914074805190180c1804010348400c0181810680140b0000c005d180c12a40c4205a030b20790f1000340c1d00c0d86100c03080503030300181084021548542c00c100261700c0d4816070084862280d58003042544c1228045401c49001e508444882841004002c441e951600140c40c4003051071200382511307440308030000c1e00e0500d02e0b00710391410504183e0000180400401e68501c01c0d40281c0303120580f07640d01f4401050510044907002c42c80c0c1c100c140030a022501c2036203c410081c40c03101c2225140740d0030301c400d81c0100b08a6800404090307122444048091900e454564210000390740c3c081082c24080c0018022020500500a00c160b45441051301480d0030803c1c0d40380c0d4541061620105500d84000948481841e09078101c000c1028030005507140a40b1304803040711581060214640e400c140402000c0d201c41ca400750100030b1180103402002075111 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 983159775 1250 983158525 983158531
    0x120e030c0d020705011805060a03062105012a20120910030b06180409020a0b0910020607080711150c03010f0509010302030a2603070206180105090703030f02010f05 72
    0x34014141e81150200003881c0c07502c60341142d81000007550b103e941220481400c2ca0541e01c08584843d103d880d0036504500420190744115020424110403802e001500c22003084218001c00080c030003103000301417040042000e0890840090319607400c0e01045442021403004540b21064040103000103104030034500720742031003c0070030745000103543d00040ca072040074940040c645080501ca14110f0364009a00d5002c0c080c40142d08240e80c0019510a030345507031014144581c028440c02495442d000d02081d030340c03c42c0d000540158400c8103a286100d00001e15103110300401c0d130b910640c958035585d08843c1521410001c07040c5200c1c3d41d100359215540d401d599846500c80e64440c540f658584505002c5011860740841c0c06880e132900103001689000c0317403c170005030700030b0081441a0781900b400200b179130380d11001150514003c0244114141d021504901031007500000f0b4290f207a10200c01d6088942c2610400502d51120100f0070000e401409505520b21403130000081100c42550510142c5ea011 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 983161025 1250 983159775 983159797
    0x200618101e0201051006170a0b031e0105040302010b120307061a2124061203040f03060603021801060e0111010f06030506040210080928020d1406010b0910120e03 71
    0x541304028241c110324480301c0080c4801d24090707140c0d01090555120700d51014080f071910a40b1009038443c686c900f00320b08507082c24801202040d02079107002c518000c00b42618120700650030006440d8543c90310340c40a011002030713040550302d0100540d8030b0000406031111008120f078a000c07030200460303955031a00300c84c25035818081c000400720031419505119644440340e8080b0303601e4048200442241b0b5a1aa00241c117403610240314030410540c0c2d10b1801558060b000d01e0b00081c0c0c02104202243d084002224400e80307848442c501006407a941b007a00c240070341400035482a41180440d071107511456900030b0711000000700709010000302000d40340c05800a4a0a81c0004148411800d00070406c03098810f4900d00030203981414020a504d40050504210072080d40026450405d0756031400101440d6009004460107009480c194110507402e180b010031500642c0000142551400101c443c1224010a49400069410000c3d28440d00e003094000900d9a6610b155550174000c0009003100124 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 983162275 1250 983161025 983161031
    0x181103090a030f050c0a06050405070b040f08010e07051305151c02030f060f0103080708132303011b050f131205070f0608070807020309030109200618101e0201 70
    0x1d02d0901404a18101400342c041140401c80782040140100b02143c803d50b00c41404a640d803224141145030000541042d0b01c074010006000a02c40e20605031034003240d900358024041c0c0895140c4680c1c0302d140c0c2d4414140c203c9181801d40d000c201180d8032840c0e20141e0115081021040e07040442c154400c07100180d1081300c994441242980703000c000c030020114603040103111901d840c10500d0942070040c48001d20b0400d0215111042143e07250603540d410410303d8903001038030368819002000108007269401014040121000075040c123000301d00c4004903022a10445401c000d00480f519031101c0000c611158060000310001c507100c1c0341c010024404015054000c1c14541841030a202c0160f00c2071070700c14810302080140503045202c99501030315504202a076650394020607411441405125603242d46441c802d2000c00040c1005507a82c003106040301b2030807408513030900a0510a07a2504481c03c1c000150100080c54454501007541e601441d18408820724103100c50580b03151207030040e0150351 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 983163525 1250 983162275 983162293
    0x3010f0b03071b050c191202210a030e0108060315220501020706050727052101090b0f07020708102d05061f0507020d020a08032101060e0a18110309 65
    0x85c00000758220b40c68590344007544d0a14010887c502d0544d11100280a0b400750f02e450407694125100c182442131911040e56070712805032400601d1508405860b40c042030f014404115541000030701682c028945100c4990a030310350a001d5015400c203c0c81c866501040000a640010000c0c000781245a105540c08216401d10a1000d8801d076582c10880d0702c0c1c0324120b280c01d507203408000b80304011150180c1e22006510711010050001082c0c17050f40182c1366092080300400c1000d403460301031250042c10207100d00c0b600c1d40d9030103d840712081d2040e49015446440c102040500e503034000c038180b0045002d820030450820030070314045550100c0351000701c0e03504c0d02002210709000e908180070101c02d094205d114800d0010180840c0980c120280c02910b500c0d01c000f04540762011400c0140040310100d079240c61314298440f8207c40d0f0041b11140e401c070b85200024226000f400c0c24401c12000a03c64600d141c2007200402d81c0c003010a80a4030004d45a400c2221001c83c15001140140b0241000d466414 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 983164775 1250 983163525 983163529
    0x1306050d06240309030309081206030d03020a0c030e030a060c0503041502070213051e1503100908030631060e09070e0a020f07021309051203010f0b03071b050c 70
    0x506140e010b2140105652140081d4040c1148035020b525454140011207a50900b4228010080f00030000e05180f00096450300889180b04100d203e1102101105c10100c2e01c41070407000c1e4040c1c60f1503640440c41107000f40c00000e00401e0010342d41a80070b0704a030544505626640190b40000e004000032074400803d00c414440500d4854110051641042d8500716240e404201c0e00e040960741c0b25543d503a40c0c00030803c2c17481e06103000400310008100e100113905100c0316035200b141c8100c4810b44030b0f1240c0120f00181401900a00d03407481d810084045c00c5036a00303003d000304100d40c0c0c4401800d4407504001550700304011804030f4010f8403201c20016885d41408000d100c4010081c242d02e86039802500104000d241d8200d002c3e0713100c500c00d5005600c421a1803288403160180b0351000754001403001150980000541c0200a01c0340150704441142c40d489500704554071080c010300c3c014200c065018040441241c0c0150b4003e11140740c503286081460180b4151a407003000115a940c10a4203250002c0c = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 983166025 1250 983164775 983164781
    0x41d07090c12060303050d0903021c02060a1505060301030f08040e2a030906010311060c100b0a0e07052a0d0f0906140702090901060509090304092702151306050d 71
    0x81160400070001c00b0704580300039001e4050307200c05003007d50b180d1416804040c420b01c01201558400b204240d03040340081000303922260f0864544e1100c40c940101120183c29003541a03027140e001604280c510f90031903c40c1000c2e541002005e60300da8004100c0055044805408113101d501c01c1d28460700c4104419403107a007040303040704168038400824030034010b0629001c05c0f00c47c1100d6001180944607021b01000c19070500505155049901a0600c0c8000e05a682c0c1c0180e98012001ca03040c01c1056250017248803a03541c19248240010002d2025100e0316200007a42c1c00300c4140c01d0b00014001c0e10301c007009460010151600b80000320723405900401c0316080129000070f0810342c20007218801c48848040750038007071007801a102d09403d00101d41c0b0384400b9881840a800c01401003815407400d02541580c035070280c42001c0240340703410002d0010a150b03141e4180c2401c0c4200208007400100d07001c001409801c00c8411000700002c01c0000b550603603a12030180203001d91b888451311907001141050071 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 983167275 1250 983166025 983166047
    0x4180c03060e19061706010f090204030317100e1306050106110a061d010e07060e040c0824031c03060b0a080f10180204091d0c041d07090c 61
    0x141420030700c091004003590b40c1596400003000d81d03807140c24003d95940101030250341d48032801c107211043d40281c41d0030011400c24141c80303c8510b80c040403503403118014202d219500c030103000181c04105241c000e00011403415040180390b8624450300d0b840c2d90990528090079994110b0710600000c1d05410007101d8007405006145500703160100c2c400c074580b041e848003181c0f50014417403a40d41844070340092030000010044110380c4002c0140c28665030b401d40d5602014010030f4041030b0809128481490240038181354010160b54110113525029030140000c154280140804440c40d90300381d030a601d040189516124218083c1c0a0b02c2031181d001030202ca43c19009244010070411100026a030090400317070b0000c080154181030380d41e130300d9030844105109810a0030700321410704140c40300b50016000f0340b05441506c001001603491040d20b10701c8e4180340c1c0201ca03225400030a0203007164900350f400280e40300704040442c6007802c0c1841c00756040400580200da401a80d4039001030500fa409201c03619 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 983168525 1250 983167275 983167277
    0x4050a060507020f030625020307050d0806190506041a0705010903121d03030606090307030b040503070b0c09030a060b0f0607060c0e031f1806021207020606010923010309050304180c 80
    0x42c0798180100c08000064103810307c41a0095091880014640308104541069410800750350203001c64401c01000320b4019240303244503865607100100700302800303a0000e048034802802d20f4501450000114000620081c2800142600b0700c440004980c003800b603800e0651080c0d07030b905840708080004ca400c82d2a2000f0407441013803400a0401201400412030390094170494100e605c0d091b0000c0020300d05040358000410425246c01031200300200000904070041c400c00c1104000c1d600c1c0340f4081e10600421844980c50b50040601401040c01075014008c0d0041c00717080c0340d00c1e2001e50000304400d5842107000711805590340c00c4121030590f000c00c509001110843c0034108604081d159044541d802182031080103640310345000d040c101004541c3e0403140d129034103540381c114040ca00d0142c4081203400c84058062840003c01940c8500d01c110b05440c80c55104005000000a403000c4818071003c030b45040c196110343c1040401d82c200050f100400c012440340562481458450b07090301c8086a00c20 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 983169775 1250 983168525 983168533
    0x211602070f120501020714030a021b10031104050d0c090606080f18031207120b01080c120c16120314060913020315130218010303020d0f0504050a060507020f03 70
    0x711079414549180350407030394404210100441107083c0f407070082c0b1484c640140025840c0c035990708000b1011010340081c94203a0251303014003a1081c0100f80149034a1080e0350f0101182d54503001141c020f511940000c25a02003160a0a440d940881c21100300b03200c00345c940001ea41c07800c001c008498001c20003d00f02d603140222160405003c4c1103445900a09040e9081450440d1800c07140c104000fa2022400501514229030174011005000b08103000031014400b400e111b06030400e075005000c1c0c01c0c001c070301134040c443c50b000445c2d10060320418094040d064102c4200f00340105519260b00f169031090182180702414110032502030100da010301c2c1da664100c0c03110800c12032165500d6000681c420111400321403408c00350306c00a03041c8100c60320064400f80b50305003888204d07003c81622500c03041c42910304201510f440340c0014000030003440002d005a02c504d40200356a44180545079404900c0c1c00c1035410680c0f01c0001461902c1160844400a41c004c42c0c02010b519000d0940c9000c030400390050 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 983171025 1250 983169775 983169779
    0x72c09010807080c0d06180606091a010206070c17030103060203011706150d051905030c0d0503040b160c0b01090f110a080c0f1303050a0212070e06130221160207 71
    0x45849008851a03a0710a4042d03001401c00d2001b1504400714800c1e1044501d4100205464580c004050034000c3c06102494441d008442d0500100180e8a104058000b0005956042c2046a002900110807101103958440c00c0c480c4150501c040d42c061440741e007015860350304041480c0c007107007507400c10207400f503000605000c800821b034007120801810541d00f1251160041c00e00920788a840e01c0d0f040000b0315142c0c91003082c044040054a0f0a00400f03098035542400c1400481d410301040e20042c1507a4900c5022840025203644001c56101443c1040d11543c5016211103403101c10980c041103c0f07503201e900c0c010803140944901d10018500304141414400030180040c900000200a03038031428002841040401500c003c1d610070020284600035400d8503440c08075240c01c2450000c070701600740301415220301200850801c05a8104044040503136503000b0401c8001d0038140d001c884965820090300880c030340000190300184805031071034015800e2081085101040c112441c0e81190043c03041 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 983172275 1250 983171025 983171039
    0x6030607090b0f0d0b030a050c030105060607020f0f0d0b0a1410120b0a021614010b1c061e0c030e0d08070210020d02190f0809012003072c09010807 65
    0x50b0344901c050110b04941304c0441d812100000c1c0000004944e140c0315506c1c1000c1040000504c4003c00035054009001503121001482558081c09170000d41c80202002520030038248a182d00000768001010200900307410740f03030980e2050b4203441d44d103140e0740c0302e41c0c61007842c007829808d80b6000143d4240e521540c62601070020710301c00d084040100840e203c4400b051b4079a110790140c5005040d81c044d890b20040803480d14000b0940364511000d03803035007011400d44041c86c0901c9000e6602845449106d41c1d40125030700d90009003000c40031000100301c500c2e40e10f40d0b10b11003403040b981906a20b440c0050100b9480c0c50403481c0c800d49268460412010000f0048416400300d90052101c90889001d600c500c40c0201100c0a40906d210700d810007042a0103003045070740d002c0c600240919145d102c0b0302c86501c401e01c0240c26281c84030070310541e0901c85d10300c180100c9440c1e4000c660100141c540410240c0003007400d01099501044030301c1ea00c50540c4040d900501c0c01d5080c19005143e800004c0c00b682c1c0c03800301 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 983173525 1250 983172275 983172277
    0x4030b06060702030f070f0306051014120a1a040303050a0c021c020703150c26040209190e0d020c040b100c0515090706031118060306120604060506030607090b 70
    0xc65000310008101001107440c00c000301a200c48850081c1c41c1c4603600d079100c0e150000d00d0307840f069034294140004529000103400307403001a80e0058125005515165003844902000038400d14214421401440f0224116076044403807100400160201c3e400c3c20f040003400d0b240d01070411148240340c40d40c2e6088070b980000c3c103a01041c83c0503420221060103070390140e007400216480038000036101a51b0755029980c5e940070000c14421a00e51400c491a083c820014003036110340d80614180c1c0344404a4054a084114654000c8080038196044814842104141c5401030803284444d03112039584012660140082a43d40390298cd040192005040002d600840d0301c0301c900050005851492050140601540d00c0415016410405504050041c0c950701c0f0707601c1c483e0070002443c045003210302e030421008403500a0315030714008800d00e000d5010002164400f62110354868004800c20a0800342070202c42d100d1400b5034800038181c5480e800780350401c00f00806040400c02051030501410808034 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 983174775 1250 983173525 983173531
    0x50702100e0d061d10060f0e07050703140f070506010f05150301050607233315030c0d08090f030f06131b0311030106090c09121e210504030b 62
    0x4003280f2003551007007420b42140013002032440c0d40100c02e04694072016070f8221704111014114021902c036510303505e800740a9416140040021800c2040102080c41210802d107452400f140d51890102441044102903002c26401c43e00f41d044840100700d20384001110754002c1c0b5003580c60306108a61401c10850f244014050640304800100721310040c0a0b16008004550141841e0080743d0591008815a03500880c02100d14200c41c4800ca040542280d5604d0b91400295444807412600c0b0302d4a40c00700a804422100d405110b422580c0303142ea50748043d295180c40c0a01e100356500c564007010b011662901c8124240286d001d141000c0d1003030000201581e210441c2902d0f003500111a20381800d0b00901c0c069118880c1060000c04003e0111071040c0c004d01c000c08400810201d40c0d280480002d4461038001d440c080383d070300003003084258907001001455a100741c5050300035050265804804011a20041c1c40c0910000c12206c0246003c1d0080c00b0900014200b590a05107555601000d1100013 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 983176025 1250 983174775 983174783
    0x307020405040804090612060e0a08040303030b0f03101d070e0103200d03050a171012050f01060b030402180919050f010608010c02010c030b0904060e030f030403050702100e0d 77
    0x41e800107061100000030380b005412100d50911070107a0301c4410440940160381d007035480c0d500c0c3c105c030b00103600800207c5284a0ba401071030107061520b181c6007a401408181d070a550066042c55101e00c841e82c0c02d03c259a001ca4140d1380c002102000c03114900d140c590003c1042c4042c0e0300c00502480348c000f550300d5480c1101d5221141c410389607002c3d44c1d13600c040c00e401d01c60503411003052080b090030580c122001c1c2c445160300d55100c8289070001c101c0b0102c101810380d12008040c00c03107a02807100d0650030f240e0030042c601502c101e80124030f406d55103030308681e800e0340190740c448004000d00c011840e04d07400164410024074440441401e1526031300b0340350108104401d01d80088844208204141407200fa202d1000d5000200003180d6500900741c06070810859407070040d440c02c0081710b040c600a11542000d4400500160103680e51951440014007240b06000054481481490468180140151b1086204c2d65400752158001c0c41805451561401d004080c001c407025115003989640360114455504 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 983177275 1250 983176025 983176031
    0x2090d1235131a0712090210080c0c07080105100f230103091506060801210b040606051e190b0901120b060d060312030e12030601090f0306290303070204 67
    0x2498022103074000354a20010101c1103030125101c0c15800600c605131007407050341c85800400314820128012512500b83c0250700c07400b00e55071219440c0c820301d00d080e404004951040e01c3c01050020145c03600a0580c01380000d42e44800801500080071181d03c4010b02d20707210f004100c80c0c04c00529040e030031140303129009241d02049102259a100303401805000e40c00c542c441c250400003400410160082d4050000403e002d4000010600d643c05050303d03800c41c494808104111080e60f85c416028000b03032040d41c0f45072720349002191503503800300301c040040d81505c01105940f4044040c02406511031407881c01415520504011000a8000301c8016460900e0045c00540828088400502e540044650040008100040060745a44c404010b9900840da6082a0304044008409440d144c0c0440c080c039401c204e09160100054802035504044141007918440761200030a01750340c2010b500954100b42c0f01e014145a80c0440c1100301107007a4240c00d1480806c41c218007213640ea219400e0000d0180391303 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 983178525 1250 983177275 983177281
    0x703030902030c0402030c2a031c1b09060f03090b01290d0608070b070c0b0c0a02270a090308011e0e01061e0206011404090602090d1235 60
    0x581400f65450350a0010030440d20307030a000c2800242c60300b14041484032803c2c88020b104d044440c2c140e20300031011012004502d000318100c0c10b041c04580d41950700a00320340715155034881187d0960300100c4148a80d481c0c5001500d4104000c18900c400796001c42890325144640c0c01003109505258150341c513041d0380200301e42c06a0b0076034000388140c1400300b444081c00300e06445540065088442101c50140890300400d441c0c03035141004e1702c00c10740c00614020616808003c60b28000014107401d041c03200c152840207e070350b004500c0341401c100f001034407401c00c441115100c0c40014419a08021800d0040101c8442070703a010b80b5102060103000c1602c41d00e1251444081010700010000d045260080401540c0da03540c094020381c0c581c90000c8000030b2807102401c0152000860a040b1780d204135940b040140c8400610005008007141074400c0c1d03400300601e60b0181c99103030710040028400e18034446621340c0e00340c00a06040b41050b032008001802c820340c50b5040701c840d180a403940c2440c20000400d0b1 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 983179775 1250 983178525 983178529
    0x60103031b0b010e010f090219081308030f01030b010b070c06080c1608071406150409031116051516021903050d0305010f0501031b1409180105120109080703030902 72
    0x3511034001c0050240c2c2c0000301d001516400f0f00c5040b6980c2d0401d00c0e502070b440d04100004d03802908580c0050f4160100000222441800c2d00c83d0407003000315858011400984520390036600466405081401d54401081040300100c2604d0041c02c00b02d07034a504142140d50b8100d403860b4107200f01c608014690740460070b1b002c0f41004450210116801150044d221854a100690000e00e01a50511403003214050303c8240451907612031702c84102c5200054070080d04001c01010805000c0d82081805500c984482c0300800c8294400d40c03400540112080c030b000f04000b20118010750208112030144600080d9030044000103900036411a8110026001c1d21290302440305107038409030103031051081415115416601660594100168500005454100544c01d44010040000c007116150700c091408034840d4420307480c125442c0c182c0500c0c10354510002001d06202d4803511a0f6100e0040040050346403c0016410140c81b90000303000805030358444102500500d0005011315442e03c6000b4119 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 983181025 1250 983179775 983179817
    0xd050c0412200102030c070b030a14011806090b1005030406181b060801030b0106120b030f010e01060801050c2505011401092414040608030a03091a0906010303 70
    0x2429150300c0038101400c0314200018001c1d12010444010b411a200400c000d510201c122816190b00740001d011440c07421490b9815640018030f900c0760156a00e03040d0144000b442919402007881a0340c1c00810441d201103681254201d41c0900030031854420014029251021403003440712180c1031090f165906e60400710b01400c84140074145481081d060346d0b0402041030181c83d90402e0701203602285a440f00c4003a1450f8000780005048104c2d45030041201900c50b81f11452040200400881c2440521004c285413001c00c480d0601c45944440d42d0b070003009001d04c00d040041c120603000340300a0800280401c201c0c400ca041c034a400c1c0300c4c070101c20f41541141034126000f40394000003c10010040d0900030031192402e029283c08541003500c201c500484420f0302c01c100701c2403034900c154445e103001d1020444214801c1501d8102e5100c40d000107036100240054400e041c1c10352000308201c035031491720401d00c007540038903491300c0041e103024442141070001d95a819650302d818a1841080001d9600d50b42d = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 983182275 1250 983181025 983181029
    0x10506180d0f031d030a02150702120f0d02030f031f0317130909030f0305070c141b0109060e011b02090a06090e0118020f120714150f0d050c04 63
    0x100c0102912107007001200350030b48007910f00941c0c1d5111344e1040c1300c0881c2c08455000302d03030035410f6011448880c090f142c1084122122031000040d289020714035800f00d00c140d05010001f03807064125810142c14204140410508041700d407014524014489031618028000504501c07200320501403503420046000725240040e54100340d20b41a503100501d628082c6d507010000a0520903000f81c400641062140a0b02c0001035050b241e031054503411050480c01408002c088c0000c000305110f409001c40c1c6054806c011250003840509840902d024000c041c0070120184581041080c04003041030a03406140300201000c00d184c0f8401c89203802c1910b180d4200f8000b00030b5488150003042c0210f100082c0e02140c21105051014030150001e0f0000600301d4613050305100340c010349a0040030052030654071900504a0080c6090200c64084000502e07200d01342c1c0180c20343d00402c02d00c154191034018128071000c07501c81d400c546080c1804600780d203540901d544040c601034440002c14103005211042c2c82c0 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 983183525 1250 983182275 983182279
    0x20712290a020403060b0108091e1e0f1902153a0506030c1509040f02070b011e031a070c06020f13090b0904030f210603110d050601050618 61
    0x5504101c80329000951007484211862881e00c91110030f0365001d008441c0c03280700c5110183c003550740c01d4440703501e03452010740d50780e841c600520b00c1c015028184101d440801d42460380c02442c01034680703041d852500400c1c0720040550541c2000d12001640d4544500003a510000342c1c103a22030740d00250040d0444849503411200e0101c480b0084496149078020300c0c8501c3c0c100006000c10b80300e4605260721001c034010380c0b68114505140c0080506004c0d0018481d528010300700054038070301440381c88120703001700d40202c0351150603400400c10f9001f0885003800845a01c0a164401c6d85940c1d0390514107806083d024052a80080000321014001d0440e12074041e0051000c0d5503401028040c10303050740c840002c2040c3c5400b42103011910042620802003940c40241c2074001585036a2401d5404e0040c052080042000700c00001e1030303000040f21090070400c1904008194181545010171400018030249405050801c103040003040d40002c02c0c80c1112020340301165100e119038030301c50b4034002c1914095 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 983184775 1250 983183525 983183603
    0x7110306130605100e1b0904150810060803030f09011b1206060305010302030c01110a0606080723012a05070e1f0b1e090315011401020712 61
    0x3001c541c50081950100d28441c142c2084256151103506904480b40d0180361001107807040052860703001d040c12906405c4c122003207203041c0b03075501c40001d054821402d00001c40d8440c04400f04401241040b52000030201400184485814041103070740c4ca0000401c4414084410004200d101d0341c00c1d440b42034400c04981e09580030b41819034000c0d017804100954007522610344000042c00c98820b1190b00d040c0c0344e0003000360009005607001110101400d6416030128010781d0001d00000b6114400c8400a0072a04050070002e49440c019041c81c130346058100c00c000c031603a070340c9a08030b80e030004070101c41c00c0040071941200511071041241302e800802c0001c02500c0303910004108500440a594440c0c00c4205640c0c03070300392210388018125040b522402c2c60012040c0100c505c07010907100302c400303d800034a0159007003003038110000786424600014140080c0700e03c00107002d9000c3c001e5846c50024401e000404900b0b1411610305031101081c01c010f00300541184070008900d1000c1000390000800755001c4d = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 983186025 1250 983184775 983184781
    0x91512330e1b2209031704110907030203191a040c030203150a08030a03050613020d0e0d0801050d030c060b190e0a091505070c0506070207050a08060103110607110306 73
    0x565110030680201c40c10080000081d04280307001d2000c3c440e60442050301218424200e900c610240120860403400e000c4000901c564403a100004144a1405205e8060005048034207100b4085005000a030402d40100200020480c0c01070301008003080003140050554074000c40058027123030102d80d06074813500b0902d92800096140c4c000d540510507255420b02c0c8412484100000300442d4030810446410502c140306915001c0c0e4032041d8070140c05004a40c2d103101e0401e4980480c1d110000c1040041d42c1eaa42c442d81000302041500340e40300e80c600303141c4c1b040e50404001868400c0940c50040410103120380d11010071815030481500303180003518251809002807040ca40014041c0102c29a01c100700d00015006821405000b81550f0001150a80302450b0041c12000e420010610400e00c030740640024001001007003040d00c2040613501824009007031900700701c00d845280c1d0000074641d00000051001c1150740d034041619200c201c0d516a0703980400e24003200d941100104156043c0504010 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 983187275 1250 983186025 983186051
    0x120c0e361806010e09120c070506040b0c0d0207050102190303140a05160e06040909030e191a0415051b06040303090b07180b0f0f0409151233 62
    0x5001d001080c4109462950703889103d054a20842114000d182e80e100c2c208201ca110010b900424a1001d8001950340594070385000ca0a03950043c1e11050012800103800b552410b002c0c05000d005141c180702411200f03241000003555007082041401e03505410080000425010360710244607081108100143c3e03203448010000107000c1118619094000c05212a231a9403140401407104140100b43c01d00303282c00e0a800c000107000c41314048051212000749000d50b65284506503074120b030b8101541d80c9140c1000c904260011000548154882080c4000d204941c54000c9012824000d49401d64071000e0038420102400348640da41c100c80e00441083c4000d00d50b05422580e210380c02118142c00703d44590718102e0300000903040d007541d102e90001c8180305503582c4000501005040e840c0d80c3d418007140300c07a06d400356481a4880040140d5518a00700d0320200340c03021000030440b4102d00c000348081500e4030031200303050100c20480f440c018802841000d01e42c00604085c1e900013203082051801c0311507 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 983188525 1250 983187275 983187301
    0xb0f040e03091f0306121e0204060308160c050102030c10050c0412050105040203010c080f070c1506120c06260601020316060b0a0b04080307031b0210120c0e36 70
    0x103414001a01740f01020813909003141507810519031141180c111a80303248030685910382070b03031002c030f0b44951039601c00000b06170400050103210800e10700540c440219403404829015042d03107c2410f640060000c01046580455011401242a4404140e590780c40b880101c1c036202d03071380120321101da0300c9076007070103020055010520030380c0b00340c0080005000b9860241d1b4046022519494240382240004000f14030403850241d14911a081c086601b5080c16000003c0d10400d0700310f07442c260081031541c1c0034401900c10141c0180900e0a0400c403682012142812610700e001d070050f44488070401140403130340b01700b0803290f504054600142c400003043c5070503406460b08814072486202c42c3c90707012400c030090070211001c1b00d50f0300b0700562801d90036076000d82d043d8400845200310140070811000161b01d442c0980100b04440365100007025040400041c122048521684100400d090915016442d05110303000380c44522842c006800c0030780e41e00e0884c3d0068542521003992003000030b00c070316040848 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 983189775 1250 983188525 983188579
    0x461515030f051005300307170c071e0824090c0a060c020609040c031e0902030d1b12050315030f07060e120d0806040b040b0f040e0309 59
    0x2650500803190181241e01c26201c1c00e540410120642c29010042441c241d1150406101c04070b010300800c03e4038680c42581101140d80d60b40700b40e00700103002400c02c59200200008048071441c514240700c9501c031069a2549140110092041d10380d4110710002510302840c0001c0010004941c180c0f0000300141140484901c0c011042062003c003240c1c0407100400e203161400405460200194541501120100000300042c0d070800d20030400700c1810b1711a809a44220030a41d14046400c2a21066420940480d482001311903490711100400596010900e610502c0c010328040340c40a01002c0001014201440020f0601e10380d00c02e511001604400035510440191100000c00c8041905054480c07043c0706150031581c000c0a8144402c0f406160720300d88600000d4464424000c0c1000782c1480c101c4030144400c041002c2004206207403420340550200840240c03002e0001d9a151404650311f090900e0070503200d039450f451141c522500810584441d298014988009201c8130501d04088140302 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 983191025 1250 983189775 983189777
    0xd0c0512011203080a050604020705030d020403030f230a1101020c0d0207150503011208040512060a051608131115030603010509160b0a1b0b461515 65
    0x203200006809505101c201c204a03401d0f4591045070f6075003207580310081030010304440d8025800d010302400b240040010707041c181d440c03040060b0f6031829420090700021030111990104003c801002040b80b0380310250000c0341e00640d107501e031668080e101c1074072840c03d1981900040e62001c507020002110005409903403214a40030780e00c0442d12111480c002c1e404402c02140441c40402c01040090101416030841900805403d03040680b01c60018004200400b600b103841c1c2d00800600807d006a44281030300044000807c0c0b10701c1c0c2c8038820140207254003c00840304105040c84803824000c0d40181400017041c01014000c0c4200a03c44c22111504144d030514002d40c030308000120a40800078042c401500300080c590102e91800c00f0505942e030000ca10001003102c2e00400a90b00d616110054109030f20601c2011070354505184100801e000d080661042600400c1c0150004414204906000d6007280d200340c6000c141c008a92004d490b054880c1081d40d1140c010000e100405210310858003403e07 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 983192275 1250 983191025 983191057
    0xa090f0515071404060e0a0302030d080708090d0e0118030b072601030c050d060906110319050708061e09041109070305041110020f010e0d030c0201060f050f03030d0c05 74
    0x9548811682d001c900c3c20610a0500c0400060003030b1382c01a02c4072422400d0041049007030300e40720ba0200b8200800340500e1400f04900d81d050080703042c0c0183c1c0c5a68088240d500502150f00a401c000300075128206034241402204260b20070701c012490b481e00c001e582c008501150500308805c00034045403200801e1440d420311701200300080c40e04502d00e03074126600101c2c0203580c64244020001442c41051040300d50a646441500000340540142c0c5da001400c07001c407076120718000ea045540ca2011031103908850341b601c010030843c1e50708080f403640c0100090310141404840358000c1c50b4114441400258000c446000300002c11409442000d480802540c1802580e01d0b81c044c1074040c2c4106441c0249061101c45118011781000355194140c000e1510480303181810f5440441d007101d100e0680c07001c3c0d64201c8510308000c10b07010b0260118500e1144000c005076841c00c02585103458550044c0c61088110b504402115941042986c100820600d410006102c500350007800a0340004001300d00c00390707 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 983193525 1250 983192275 983192281
    0x16031103070609350708010903081e0a0b01050d0216020f090723160c05041d031605030f03130c1d06240c0109140d0f080a090f0515 58
    0xf1040000004544c0181c01420090002d00307810440041400c99500c165292071680c0f1038449410400300e070003030101c60000203824905050003400c00d1401401c81e45c0b41c0f000c1041c44008100291906948961800c0000495001490048569121302d07140448a14000300d04c48210141383c0c203101041910031983da46d00c4030520810301400000858280c4081545520f500000298440e1580084007070014010b00c1d010302100e00107940d001046055030481000c0d4070603c0241000c1c860104440103d01c10b00802005044081ea0f0b43d1150494898000c02c5510b103010070007204100382c440443c840c1c10f80a46a00d403092206200c030705207050646001e08550030000c1c00c410140da041840d8802c94050648950790314090000c000701440340c81d51075041c00214201c01c00344a00c041c00940c0300260002c11035071b81e6410900842c1d000b03005069580d1308840d076140b40841c2c12003a0100d8607901401c00308031554546003401d00900e0494800f030030f001d8040c803403d82080740c04540e82c000c3c045001c00d070400c0c0361 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 983194775 1250 983193525 983193527
    0xc032003220f080d0f0e12060a050c0315010c08040b0a0206070e0f0604030303090c090f020d1506080420060d0e0105151309060b040903050c070b03190e160311030706 73
    0x45680d200343c401d690043c80c45074010500c501e6004041d0015414081400c0c0e070300e000400c40110300c041451006801650900002e04802e000e419080007140d03000bc0d05509000700019195034244a0707203414003055a0a80d81000051800d8a0040003e40c2680b80c03a2604560b01075155a011108070000130351420301b1001070b24210701d81c1302010b0b502078243c44c00d190541d40c3c19030081c0708045080c0c4d4401240a800240c40082c3d000c1c0100b44400c0810143c1c071038050b590300c1030a58804550074588500c0c51038040c05060340c8060a680d003c0c3c3c0042d0006420300034034030350704840035501d14143d0b013000340010b40071468400c0740c001c0c0c80d810341407000804c000e9860702000c0d11603950b0110f1241e80024038104d0f41002c542c003900810002400f403040000d08840801c0083d0841d03400403811004070380301103405440c1041c1400910000c1c42c4a4800914514014004c050307070380302c00207030038070502c0e40d41144d442c0b407000c01c014024140c507810314514241364681c00d203d0541c542c5008a90710030b12884c003001c5001 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 983196025 1250 983194775 983194799
    0xa060e16021b010203120106051e0c030a0c030c140d0917120c01330501090315090c0e04050a0c0803040602031e13140102120a0c03200322 61
    0x40c031241d4060060300325a031440600c0303460b460801d0303411480107110608451400c52050b034020b08031038035041e540d5080b00070581d4003412600348107500b01000b4090745e241d201d03000c022102c0805542c0b40c541c1d120059854140c43d151840000074186044084902c51040c00000321801401195190801c0c95541c0d0612040c1c0360004c880e01048a40200907071180e0b51340c0400103442c1c01006000085190200c40d164000030741d1250500440284803854400c070007460301000000682000e01e056003c15040d621012820490111034801031542e490703050040c03051811103600500380301da482d0940350505041c81581e0308508281501c0c0103030400300004800100100310ba00300c03071254001d1820aa56003003964444a0110340d030850000040110500010f4009103120203031032101088425445014002071030311408402c5480d507410100040451a1b8005050340f800603030615202148009000b05801504400500e030706440c4000308202c5400d03180c140380300007145c14007248801c85130b944803202c1d404 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 983197275 1250 983196025 983196061
    0x4050913050d0806011418120627160b0a17100522110c07080607050d05091f060501020c030303070f2a1109060f0a05061c050a060e 58
    0x1c542d008140580200d03014200d42d65000c0710506082c407807401041d9040b45181d010202d0001245680d4420b50f00301c1c9010000203025000d8000200781c00c0ca4480e40c0000e5200010402c81c0c952040705205044003101088405030361035581107000781c807a42c0d0f24804591608108a000302082e424400800b100602c500603500c141c050658000d20070f8504014030468400040e004415800c05030f4400203480442d002d00c4400c910b2124004c0c2d540c030a610b40d4a41025541d401040541c0c110405210714180d003d0107443c80e64065810005041e220400d42c1e600e0089038407180140c9091003c010820010781d54041c45c1150b10a03000e4481901000040580b02d2208842c01c0d00071902904046454038490a0404102c2c42d00c0d03449104440030240e2408880080c902c000c44031291400070060040c102111000c2c2c11180540b4285880c050b0000020840c0a041c0a407502607000400d6002c44241c01c400030881c0880508070801560900000301406440c4600070328501049013804203040400010400312 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 983198525 1250 983197275 983197283
    0x30605161e02010608060c04030c0602031e090609091906061106041e0812010f140f0108060d0b040f0b0610090e0c040305060a05180d0e09041403040b04050913 70
    0x480049094245078801c40003581150360b44d02011964410410240e8021208171100503202d13841c51030540c07190b58094001e0310841d0403d020800f00d8507841c08a1071442009403100c0c1d52121000c4c80403964034090022900d500c607040f40d0500400c20300c0c51140007090040f00006000290721f400094130310350361500f02040e169001c4400500400e190301c00b48418580c4100c40c2004600d000e885469454004d45c0310500c00325005001003000460300344240d00101904081c1030028064440040c2c4146c110090403070501c21042c0000e1b200b565458100a606070b0710450751003090401d400e1892180b036003041c0480b14451114003103101032130120001004aa0307a60340300e8000a0500180c101d03012070103040400415814000400094000c1c410288500c440f40000181490002a4410720614a03441c018264000c0b00155001c02d601000a074680c220a41e2400b00c15111454904042081c0ca9210b000c0c6000116011540204420003070085800c101c441580720b1303d44901d03441d55000410310080c = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 983199775 1250 983198525 983198537
    0x1401090515090612150f15070212010e10021c0501180905120f03070f08100b0c07050d03080f1e0a0506010c0209073501061409040903080103060516 65
    0x20a001c51000041030441c0029003801d0420781c0d4410305048a81c4155844e480c9425516004400c5081000038030709449001c0394040c1000070306070381516a6105580b0040c0c0aa402590700344100d5400350043c0001d0040d9a04640040c050140680c000703400a01082c84005031002c24840c040c20180181410303186203400e022160740d2081480c200920140004803118044c2c1003d40640040701d60152104103400800e09035a8600303034100034010716010b0704480501408505000300c403448a0b64030401d4500c00c81c2181d0384d9506041d1076624154450b80f00700e6000c0d01600001c002c00da03001c0c011a0040100c4ca06c1000300b03480e1136901c0d071182c00122000d486903041c0400080d02000030b03504017542182e0181400c2035081003907004030f58610400c4800d000030400040220300c200e01640280d906000c10141e0711945641c5001009030154018400c0004003d0720062030456644034804130b841805009004215000f29480c0c00f801441c024030094410a15000c0011001c406650382c01c040500c0b140c0e00c00c = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 983201025 1250 983199775 983199799
    0x5070f05120318121c0917060c1b010b03030406020a1a13031b140f2a121009030305191803140702180402030c0303040608040b0a0f1514010905 63
    0x101100754442610502240300d010490003148403401c11304c00c20f1412680d9031b07151103400d0030850031244415511034000c0750301860800084074081e50a80c0d000d0070000e03405500a01c0c030101e0450141181c0244664540400100043e0241d00050341000a6101c2d20142d50040070703130300451484010031203500301244460170481000074811803406110700400612211051102d403500b624a0025042c0098260f01c441240000c031401040740e1114a0315940c1202a1310525400b01107040f9000e140507406400d0090010b0250781702404400040f8a400b4401c0002001a04000340503117400ea0f9050b6095a51240340c2600070000d015001b13007944841e030702c40100c0f090303690102d42c61a4407080920029038144221001a0384210080002c040f4903080c119842c105401058240008030b40c0b5103100b60310400081080c240c201076031550154001c41000c140c0c1e80d0b080320000190090400740303540546441105030301403001c08002c50594403000301041e90040c00070010350b0b00c1a440d00815a009600783c01d4 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 983202275 1250 983201025 983201029
    0x108042307090f0e2e021603021005090106030807020f0102010e03181507051f020c0f1606030501030b010303030905011413030207050402030c040b13030813060e030102030601090e0603010905070f05120318 90
    0x82e030781c0c805c0f1489070051038426109003400d0300f40001c160460041c1c002010140030500303540560f54100d0a501c000300011490360b0f641c02c02c03900c256600280240003116103032444da8000e500052841102c00160703641c8013525403407111800c0040c803c00d8031502d001411000140404d0003520207980e8803d00400c1c441480301c405a500210110100240640812044891203418003000c0d2090320500010303c1294589074040d1034503102e9130042c3d0704140c40c0000400100c2c8c0a440c9141c1100e800d4100003030003540d181000c41c007400c100c20a140300812030f40e06018052106201e0002020300075420350f51030b039032940e080009a10003a02c0c03502d81400e06010511031040d8481c0100148211038080e080c1b8540d0703d80d1041190341003442c0102860407030f01070802c001500503914043c0d0000440085146180010000e403021000303004414420000704001501610250f0112901580000444901c15928414213184007404d00689001d03110310700980c000624000241d490301d04104a444200046c4482 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 983203525 1250 983202275 983202343
    0xe0a11120f060a26010f0b0d0b0901020f0304301e0203070606030501060f090212010e06040b030a0c090f0203090703030810091103060f0f0108042307090f0e 69
    0x2c402d55012407071100010300c188808a031040d18112441410142d049100c603658215038015000b82d007001c0c108602c8421650f80d94249200e640da010114908a40b5107003415402070242c0c0c0c485c0b0031000e800000b0b01c02030041d000d10810345400ba41080300007088030f00e10149903011201d0031400107d1121100c1980d066440c00101d0640100d51048904160b0a0740f02d500a6070310642c4140c0305655101c2c424404d090104929601801410340151b1400c0280c40c814031414030148620440b89040e140030500a50b61500862401e14009040b81c0c640440d90805c03107000809440384900491030075520203c400828020b0301c0c480c03c03000c00a440410b140d6101540ca0f5400100704030303810668030f0740114410360380e0b114521200801240064030391420078140201040101142803082c02403807000701d0300da0780c448007866002d6400307540d954065954130b1308001d41c03244c0441141c0060107410008107a0058a80c050b0149032a410301c1441600c44500d00f29403141c546241c50824910885800d0b007403940001 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 983204775 1250 983203525 983203531
    0x150603021303620a14040518090d1b111207170705090412031e0c0c0b0c040e01170712080d050f01060203040501180305070e0a11120f 59
    0x3011070f51164200e092102c3c02914102e8101024000080c91503e441a40040780c64016283d19608180f5010088103440c081c05002d0104081050001c00710700b4218052090702d0007801c0180011428051a603060b14000e4411201d000c8180b08010b646426144114044418421610003810300403084d51140190f18201e210455080381c1c03d0818508506030402c0040000c02c010b9800d840c0c200a8001a54108442c9a00043c400c00e940030a03c00030400004520483c0101400c002648010700201c0c514111300c0344a00d5035219181c0308582a80b250006c03442107400d40300d190041c485985800140d6518029802003070a81412100188070f000f140b04444000d001107103086819460769110680f028030f41c9100111640100815143e074222103a000350b940140c5a40c84a41c0d1644c10110025901d00880c4a15410824010030300c100c10078002e0106000b4603004001d48180940750021000608020707100c110f02240b1300030070003610042d0300046d20416641030440c08016160004a11851840a = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 983206025 1250 983204775 983204813
    0x10c0609082a12070809010305130c06050c0606041a0d060204030c030c030209061206070507060f020a0201021902010504050c011103090333010305030406030528150603021303 77
    0x304140400701c0c0c0b03041d082c2c158400110055024008500d05043c0c10261038244403503101405112850000d0ba40300203503450f498080c40c1c0014150344018402490802c9401d02600d01a00c03614040b4059070700400514003540342008440036070f00c0e130740144021201000740c1c44400900d81000c190581c50100c42c40c0e45140e00402c0c005d400c181e03e0b906c41c412280d145610840341d15651803020001c40c00d02100c101c0e07010704211002101d55401680107522114000c01d86400c0080015041c820400c1c690300820070210716102c1192552002c050107130003036114105588091440e0040220300c98814085c0c03d104030360080c003410351f08030000015034100b2015858480300703000601c202c02c0c0302d440800602c142600d0391081029608504401039a05a500316141d0008018400050021031400003c440485406140000c1c45546030030b56907481e1548d02500c0c1d0304901c200d00c107840c0b04c034510b40c0101c0940c1006000c0703061060f51310001901240300e0000b03046186440789100300041011102060644503003 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 983207275 1250 983206025 983206027
    0xa270b03100801110306040c03020313082b0605121f0b010504030803071d040b093603030108060a0605092e0303030f110c2a180906090c010c060908 65
    0x1642e02c41e0b42520040c00320049030240c040100720051405000d9103440f0145c030300301145181080c030020540211b041c50040c4c00e2078400603540c2039090610742441c142c00728161220140c1c00011640901500041c42100c4c4a20740d000100b845000c1e0100b168038403058008106000480001000c41c0600310790348403503050000c10301000000c649113500031b502c50910ba65a190032002c12803100702034030100e011b501d800780b860031030f4400d856280d807001660402c07403442070500f160181c8142c100c243e1040c40300300d01c2c26505610520b0115400000a103043c1c4603140c058400b02d5039100304902c21107215200f070f954009000004a00c3d190704220441c8600010b00700440100b00719090200d4600b0001c0d442140003d1b950000c04a00e206603110f80c1c08000080c6651918007900d0764082980e84004082c43e06049109860000c030001d0005a40494588058030700c00b020108800c1000031040d04450b002c4c098019240040c200e00d03030103c1c101d03c4181050711194108503003510350400804040c002120740f068 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 983208525 1250 983207275 983207279
    0x120d05040c05040f0b010311040602030a0e0a081e010b01020d0903020f01030603061d100c020a14030c060a1a0a29120406150f05060708090d14030a270b0310 69
    0x22240100008100004d401003105204030f000142102c0c00d4401ea240008420320043c80781076404001c0b01c40c0715241c0c0c5040c0603260000380025040c03e80e1035005052510076044106c400d1212001030482d5182c0c1c001c0200f011101460040e40c98068200b107410000d00d03050400d00040c9010441640c0105042c90000345264881d5200700444810b03a41a02e03130b500c40783d200c3c89001c103810070094600c0c00781030740103000c0040301000103982d420b8031002c010a40d102048124810315010403c1d9000742c403c40c0222031807400d000f80000d009014103080045030102d047d80c004001e04000c000b400c2140d4011038944048100140c1c40d40419404038035100d0303c0003041010720045a61048564010750003010b0002c0d02005030b0061f0300380d115541d4807850000c81d0031241009031f80d507040c0a44110b1034100307400d00c0d582c003044000034104001d805001482c80c101d1f9655083d1504001001c1d1000c408552540c0d04000c000400b0710049221400c180c180e00071005000340030740c204100c065900b118002400a008035 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 983209775 1250 983208525 983208529
    0x1207050127111002100e0c0a0603061424071b120b180c2e1b020f0423010e01080f2d030c15070e1f02031e030f0702120d05040c05 57
    0x608440d0011b28142e0100076040c40078600301001e0030081c139460904200042c07802000c1d03040b0800310140306105400001a9420080e00450081c0011000000040ea90541031400c2541501501c40305984991001c030042204c4548081522882d07070003d40341d9003155590f9201030800c010313002d0040c945000f00d004201003500da03501d8061400f290141240410705500268103080c040450b8035004000746940040d20500c40405400400d5030103541d408240884000454060540000f0311641c00d1000f80007502c0b0b50032280117042c16500e100200200030390f40d81d00c2e566076806084086c0342c3e280c1c001350b40d41369428628016403142c4d015509241c44640c80845501d80c216003214048140ca500903990703010240480500300780d4001050308212038074040b808049420075031030115916261604940380381085000f0000d40d9414030b541088180307641c0c12054613500640040d1040c40d20940c800000c12141400030031442d800e08441a201b43c01c0130380b0760001c03c0c060030001d0010740f90800c21a102180f15 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 983211025 1250 983209775 983209781
    0xf04081e0909060409030c08160b0705071713090221090303040309120803010306020c0106240801290a03061e03050607080118020a02120705012711100210 68
    0x2148025068544904601c424400d11100041c1903034811890a1040000284c0040d0180c002c15000010142c9035110724071191110900048080c1803031f501c08003003003d0341d40c0c40001042030602c2089405000c80c041080e5041d02d0040c1410790001c0310300302d88140030004507540540322131041100c0c500c0b22500b255690000110b070580302c0c0580c64000008200c00e060300400c3d444001d124021910809004640701d91a0a002c10b0000401d8241c0000d800004a5000d40004001d001c1e0151506512584030031401c1e11008001c08942c00f2401d05400003c0c0c16120300f00b081425030400140840aa24130300000b0300f40d6100c005c00b00b00313041e074802d80815030400c810f55824111103401e84c88403d55040d814080d203410030081c031280c100a14040103100c2d400740d5000b060800c80b202040580c5903022078400780c0c14007590100700c11019002007084004d000c0c0540020062010050304004460006440307100e07010700824025005c00c201202100003030818000081c15020b03c1d1050b12944240c50101c0d1080e = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 983212275 1250 983211025 983211067
    0x31b39030d09050f150307180b04080a0b07030b030607120c0302271c0f0b060303070f020f0a120b01060e090c040b031b0c010509190201090509041e15150506030f0408 73
    0x1a501a0f5408d00e0540b2000e544030242ca8042841424540b03854515943c0b0000b04000a103a10050070109031001e000703402c11542101300405881c0ad5150200b0002e0001c005600c00d810028100315420030f1840c000d100701c80c03840f00c03c150a50546250000d50120300fa10701c04c03c0361303005909451042c040392004041c5400c424450300d10000c403800103050042c60003501405052094000300101000210008601407080c7c0c0d040e280c980c03c4144040000d1500c02055100182000e000300400301000607020041d8182c03000c1d80c94103600442c1e004240420b01364200d9804903c654104828020079036950043c41d030003501d280c40360714003040d031801d200700a406c445034410321030307441350b092200c1c0781c800b07111100800c3c500030340780e802070049900020045203046c81601c0c000c1c076000c0c002c05c041c001c03164046d2581a480881e02908084103140c0b903e221200196040b0761036180264003091003c041341c1e00002c441c03008020310b00719290100c40008c1290064411241c194082115070110990340c0c8120003 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 983213525 1250 983212275 983212277
    0x9221208060102150906040b2a120115020303040605250c020f03010b13180218010e06010905150d09330e031b39030d09050f150307 58
    0x2089090620000e80313410103118403018032000711410400360680005150741d20541008503400c4507200c1d407101d13038032030741d074a01207080715410724a805044824204010b010100c1c2001d000c02d0180c1c2d85a04c194900c07050b407841400160030030401f05000c18043e4002c0c0d600064040408000170704101c10403102c082405000a006c2444404d01d5400e51a2102c200f203000d000550091010740d401c480000c00103a0708070003441007107a94050445041c0340c0750b802c01014544c00750002c1d141140400f0108040402407240050110800e000100654030955580085030409040c510029000151190440e0440f00c41600c1b0070b9a501a4480481c1d00e4601d00800180c0703003d180c102a0444a504200d03d1030040141c511040c2028012002030400004a4841d800e04000307002030f500a103030905045c5a00e0948148a00030040914181d00c401180807115000c3d0a503c1d00310140345030801d160701c42c2100c1c40e4032008109203200030480c1d8140401c82c00500e500003809900224901c0c90008442d0b002600c00030 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 983214775 1250 983213525 983213537
    0x80c032101170c3709051008030403230f060c21040c0b030c070c0807150309120305181006050108010609030b1f030b040b04060c0e092212 61
    0x8045800600c440000c51002d00c080c20548150f800410250381c5a1154103c140052001c55911a01d0b0691030b6440300d21440e00d00c00550f0f03034440d00030010341410f68580070000107510000456500000071a004c032a446450b44d600c102c0034100c401010410180f500c09140264500081c615405015240c03095165645050b00c0e0b40f0140c002c3c1c2d0305001c0c0c0141102049012070140000300d007030a480001120032007000c5640c3d80d07552000d40c520034020200001d2003810444004142e82c0e0000c10030606941898101c014481600003044080d0303450010058442180c1403120074455110750020baa002181194440c2840c803050000761601e40b41c2d101e0041c0c441d0340c42c0002e1003103603448a1260b00500350f62401c200c201c0d0540d183c4c06072540018103c00c03581c42c2c9004c1c071003140a40300142c0000135908040481c4603450142020408031000719070884000303107020074092040340605d170251059480a88400101e0b9520141e2002c400c20101c802038000048902c108001101060b4601c95440c2c0d0303503106 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 983216025 1250 983214775 983214779
    0xf04090e06190614091b0a09090b420a09081204050a15030605060d0506010f081e04020328140a11060702040e100c17060a03080c032101 60
    0x1101c090105801c4518142d0414400f0000d414481800400000d0120381040451b01c5500a0032202e0340203003000a0340c8803002c1103060f0701da40c028501604070b419648042c000080e0b00001c0160420b8429181c0104024540c07107000c86a1122401c1c042c40300c09041040480814107400500036008200502e0000d469071070107004985090142004114500c000b25060901b01400649146114010f032060b1505030100e1041407446074004200900010b48055503518003072001d94041d042c101c514a0119010a220380040341c410300c0d82d54070840b4000c1c8440307a000c24000e800044410060f005030b80c1482206030300c019003500c061621001c3c10018000c50380708802840c000003403205403503a40d007080d04544480b0740031074222350210365001811a41c065580402c0c0c40003c00070034804000c10400d110f0b008082c1098802c40d80424102e9000ea01c40d561081c0040310204803550341126400c0e00304007115010000030b000c1c04044d204032000402580d0400028600308002d4041e510a80d0745842e44032401 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 983217275 1250 983216025 983216041
    0x31f020d150303020a140a0209010b120f060a210b15090a02070209160c140d110f0309100c080a080f0c161101050f0418060e010305120f04090e06 64
    0x7010400c420000c055041d0a19545000c1d480d0410300601510ba801d42241015100609110140040f98000c0090110b135840ba1013049064000d0103203400c82032070900100c0c01c800c40d01c0844c00c2c07141c800140b90900b03003400c01c1c50340b0f014641b030070341800c50b0113020654400c0051062064548603184181040001801030310811101d490090040c10031644108041c1016845126855904c801000303a0000a84002e0b0300c01c540500512202800c02072503035a0065003210040740c00707400820a903030b511164154102c4110384480c02c5020304609980200326113125410000503c40d2144581e090503010140c1c20340b55a415540319010b514002004a4200310b0b1000300c0015079900180c00b0b203a02c50500140001740401e00d444c00038068481800d51001289980c8518111072040c04d6944501e52900d0355814241410010000c800818a041c06004126400d0a20f0300c1c6049039008030080001c90411120355150781d000c0941d08849060821004c620700303c05000c1c0102c8845007400800c03082c540584 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 983218525 1250 983217275 983217281
    0x21f180308090130021b011803080c0f0d05070903020a030606210f0b0402060c071212031103010902031015020d030509010b060403060509030408010905030a1e0518031f020d 76
    0x88201c0010102044000940300e440e540d80d4034100c3c9210016030300d48565078168910720001c110703107126600741101400000300540407820503904c22b4860340c2c040c1e11844c010b00745600a48070341c83c40ea07900c00c0c440d820000300141c1010741c0001150134184d01241d141c0d00401e602c1002508140c172426120002040040412000103d5034194a608805015040d503102d90b0100300018000c0c0c805072804021030150750310002201d011001100885c1c1c980d07a611750003a01c403090850001e6441000c080c1d030b0000414081c5c06013520380100400502d245a00b07009004000f9000940300c10301110202c132001c198800b010045c61302c4e45d14160000c2550000401008003079074401000078a641c4d040401c605880d403940e41c15282500c0d4405000f041c0355641145183c0b0b036010b140e03c0741415600b010301050a2120100c020608420543d84528900100c07030305221094a4500c0804001182040341d95070800100b00718800300500202542e00c003450042c28000541640034444500345c0c0c0c0050025520b480c80c2c4 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 983219775 1250 983218525 983218547
    0x30a090c0e100e07051818091b0603131e020324060d05070504023103030212090102060c03090f07180b0414010302010809120403080a031404021f1803080901 69
    0x65050b5a1894211300003801070150031666040a1a4080740503603941d02d4403041d13103800c0c4680c00c506886150611186a5650810301041a11081c07020072400b1410041c003142d1280e15009a110b01c3c026440c0d07541c000c44e0710020b101c1c0d006802107121010040c3e6003441300041c038489002010340444403c81c07180d0305071703080640918030419480241e080040e40c00b1a07880c0803110116001602e0307181c4580390b0400968003801d51001046144c515a95954410315242c4c150ba00941c05c0314401c00c00e0031071044c058400c0c0c02040d0301690229000800c1128074030010b6038000d081005850b18a00c03013061942c42c00040340c010f080180d05203c90040b01844601c0b403040040000c40b81444101070501940358801d206000c00790410807070314001081000104412072621103882d140c1952140d07a8206442d444c1c10040307190000900b00010031210f29039404460b405a034000b0300c4081520111007100e04a900e01141180a000915009061540414140d103000b1030040741d4150303070740d0840750006110709544 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 983221025 1250 983219775 983219789
    0xd09030e010e010806010c031b080d0e0606010c050a0f060e010507020f0d022404030212030c071b08061311331e0c03070b04030e0405070f0509010302030a090c0e10 72
    0x403130108002680c1c046851145140c042c20440318504504003104000782e285007010b40140c07000510104e1100503640300e0701c01c28a0100a031400c80e2180c5004440c0000400009071089d07105880f00700104450b6208032280c4c0d881910700003460588800028252607007250321701d015812072403a12034051020700c40092000c820340701030000c6c40d21a07040e500c11b84000c000ea51000e0308178007000408045c003c0021030620541c070811161680707040840b40d40f466000031000c503940e09583d14078020b001840030007402990000b4001e00000d81c3e4542d0400d002451440d01500e2550450b807003844242c0ba012040b22070981d200703260280b020301c00c1180c6803000d0004494a4190501004120100a1145003060b2a4103003c8071095840c0c04074481c140c918060140058902c0701c0d12001e000400d80c221b030440106200984060005a80e820401d864517030710150580c000c5042040b8042182d8400d90041d0b621541c0d0002c0011140055119101c281034560001c0c000d061507081840317418001007074108010008 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 983222275 1250 983221025 983221037
    0x50105041b0c0213061502010e0a0b010302060a0311030108010b01140405010e0108040501020c010f0509010c080c25060c0503070219021815040e0705120c0604030b07050d09030e010e01 81
    0x400045000755003000e507a6401c004403610910304568074038100710085050f6603014401c0e50f0f21111640c5889140303948400142d0701c1d0103504104a05c01040082c0c105411051051181c1e20b15028091198000154041007555804a40714040c1c01d0b000511b019083d02800010186400400588803084051761013000450a0004010682e40884c0346071180000303180c4640207072100d1400a019008100c0240499400c00c10400102070040e0320080c480c00c1d01400034446d5906400041c0c07489a1f00f95100001e0f40410410f000c8802301e6032104010990030001001c107803170101c0d00c0d180c04865503602050001500001805035480d030400107002d035110b11021400c2d0001980c0c3c00613101421003003201c8029411400010b41401c00c42003013812143d0043c0051140c03200c050090754840045010b210304c01c02410f020319100000000309143d030315501078405442e0a04549a5082954004000c401085001c10024010002e5806064a050701c603440c0e9071001d0342c002001401c0241504a00303030402c14 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 983223525 1250 983222275 983222291
    0x62d03070e0a1d0c0d03020a060203041a07031b03110708030f071701120f02040f0e0601061d09011221031b030b1f14070f060b0409020a0902090402090a030809030105010504 76
    0x2c130b0300380c10001c01280c3c000c1c904000c0c1d00d02039003401d0158001074002c6101108001c03c0c020329422511a889289041c07d1803a41d4811041d0101c418403c2d00038003603c2d0007440613443d0ba00983c0300f00c5101d540710035810708007851551502160f9004844082400c0240c03410f100784143c10043c0154001d09000040c103441d8101040c030010501e80e00006000d0306503e900340c00540d01c030707603016184000c0300c14001d0140d6120668515507509082c0725400c005610442c510720424440020041240002011507882da40b80c00629a89240c1c040700c2a1151203880c2030141c100e20030442035130b0111000e500c0224060181c10186030100f00140c644600f81400c204840d0010740d240c2404028500542d4600000c2c00e0b0600000c8134054000303a03a04000603c002070000601c0116101c1c0c0204920800c81480850f1991040c44140c540e1650f00039000000004c00b40402c1545401800c0c07403400160005081402d030000041c146070172603005581d0050001207902e46ca04082c01500e0140100b544c1c2409401 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 983224775 1250 983223525 983223581
    0xf0a121109061903140109050906060f1c05070e07020a1707030c1b051011011a1f020c06041211040b01140a05071202010c02070e062d03070e0a 63
    0x40309a50703090401c034083e0303207400401034003e92242e10418290f40042091b0b40e164000e9400600d41901d2020b01d510440c000078107140b0307080140a201800241c00c82c0b00b4401c0d08541c003042d50043c8001290103016607280410790411659120f8464031007640200003000302ca0400d10f0380c03100007071202600c0d001c081008902081d00102d001d1061580206807a50000c85400e404a00814a4004c5a40b2850303050302c04545552006900a071503401d40002c000c000c02203110984161500c2c2c036450b0b0071584032203a1002182c0c150700302000e200c0e03860040d50760072001140000c06940c00703508441504502d42e100c800500c00a030b03c054843c800251401c101c54904100040e11215205c0488005501c0015000d60201c0c844c500b0340b20015400b04d001e0301c038161807a401901034200d1005410045c030501c0d2002a040101c0030030f190244c0300142800030705403022a020310510312010459800b2005101e00a4803d8508100c40c41c01014010004006418580700031f80031703076400340c503440720202c0203065804440d = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 983226025 1250 983224775 983224777
    0x102120606030402040b030601030605010504110405030d030c23030703112b021303080405030c0d1502030a061e0801061e050d1b0305100c0c03020d140f0a12110906 72
    0x98045403099203903a200d04c0014041c0103050074060300350040b0000003042043d01e40096040c0c50040b60140902d12001401d1620b40c0201d108503541540301d00d5041d00316500a0307210000d0b260030b03458415003030109a03c02040c1025240c050702c5220500204201c00b9a070703d441001394581101421034500704601c1d5400028008072801c0c0d480503501e4010000c040c028075412541003050800881c40166a01c0c10044c503107400070b10480d8000d00a01030224010f1170000d01044c2c1d02c0750311001303034440017002061500094100410508895582d01c00200700110396104c980b04034501d00b4000345696007459502401c0d220241d01a521001019805004407040c00b18a00700f92003094600f01c1c80a0360350304184e904210301c08801ca8444602c1d600c08170901c0408100488000e111000c244aa18100c03035088820914030000580140c200d41d0814441910441420601521400c40c850078548001e00e805400d5100c02d03076220103d08602c00d0702e0301405032400b80729036162660b8030301400d11307a40c05c2c081032007 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 983227275 1250 983226025 983226031
    0xf0c051509070f0605070606080303041e020a0b30090706120f0c05070c05030703020105031f0b0a03091109090304031412040f08251208070206160212010212 69
    0x20441503040000c424010400841c0d0041c1403440c030602440c1d079100800341042e44011801c0d0b03052810590041000304c070010480e8012940051304a07880320b0040000d54003c010f2120482e445800c0480000d854000c0c0c0c0090248250308a00100b0f40c42d80c180405001c0b52202e101090220700003100300420100040390901c207d800905100141840c11b030f18000c001c0940866450b4468503003503003d18503a40c05809088140c1c41038249602c1ca54a460130180d48282e10302c00240001c104000017840740b0762103174001d0300d0020000e482030849074075800715a04a801002d1b144001a541301d01c840c06000201d06008a1a582555144654240381c0314442d00d0303208501024001014007400b02c1206482080090844040a0b00b40d6460300d442d05031800310364000781305d14604c0f40320300c2041c5281c031070726080c0c11a01c441c20304907124861807030900c005000f4080300c00c00b41e0340d4031024044040940c95540c01007035040d400e84034045100e650b40c81007011030000741c5c110303071250b82c814010b02003010401041340d50 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 983228525 1250 983227275 983227303
    0x4181509020a0e10030506010f08030a0e040e0601060815010305090c0f18040f170901020a02010305060d0b090304060206010e10212a0605120f06010905120a02010f0c05 74
    0x10300c038080ca00201d04055a542d001e002042107074400c001003440c20148000030390780300300b06441c80c503646c0e00c0c0c81e00700e28030740c501031400c454008020003482c0500440320700640010241000c2403001d074032030030142005001d92004011400507001c04c502c001c000c582d0802071100c2403e0821907804c02107401a81c1e002074148a034022034a104583d41d0960713030001e1004010100109149281c80c081c0340441a03940c0141e012141e480c22154000112032081050301e84a24069005201c0106a6001100540b5001c3d00c450303004824510b80c400441d00b030104c031500c1081d4402c02541e4136843c0510080c500303d01684494181caa0040074403111844114040d4110380b901d20000d0a054211003034500e0345001807600414045c89110712a0350500c0d08950004004480700c02014030540c0d03148207980c94070440034a0629511090002000d020006003260b400600600d410b800300c1d5291400324522030155807290203a5444000168115031f400b0803210700d02d030014640519845840c0e501e41c1d903a202c0c4810a02 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 983229775 1250 983228525 983228531
    0x11b03060b0331150b040b0d0f062912010504030c0b09121c06080f0703170c1203040c050a0e06061806040609031e0b070f0e1e041815 59
    0x2c5898442c282600c4801003d00c0502c00402c0325071504c2c54205a0240c1e80b40c8101e828428802c0c09484d081c420014654030151500300703001096030790380003003499480d000c4503c40d9490a81a031401e03140d04030030b07000785030564214501070a0a402c02010822a035091a00750703040508000001c1c0d0b001d4100d101856010000300101c1d01c5000e00070b41000d40440d15071b1903048010441201d940f800608003180c0328a030010411001e43c0b10401c803900c49a05001c400312640c0285420000a19620900c4018245085c404c40c00d10b1200c0500c2030401102506484035000c0100c28442406004091400103040860765170042e0340c81c0c1409031b400b1010040c0b80324414000495607003d1418010b180650f81d610040c1308607034543d181d0101500b08031142c0003e48050f41c1d034031003410052850701002d00000d50004190a210307502c1c00d10898022a5605446007000721001c11802d40361200284101817480110203807034003440c044c017480308550525180007480c660100b034a80100e840d1051500011202e16804 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 983231025 1250 983229775 983229811
    0xc1406130f03050403081201140103050103051207110307031202070603050601021b1918240512100f05010e06100e100c0512040603111321060e011b03060b03 69
    0x907101c9004d640d01c050039812000070b40d4805101540800c60603200310800340031404950b0300044045071024080149207a02c40c0c00301c2e644da40101030103804010301c03842a4542201b0840c01007420507400341c2c02291024054070f00a8507039601400800701524103407404000600d48030000070f660f61864550a041d42c0410f50182c4036076120800e0400072806903564203d00d00b69141d10200c00300c200b0300780145140340b8082017410503540082400d1403070018a041c42d4183c50402c0d04002c140017a00070003c1491007080760702a6000d04601581445240c2c0c0e00c400612580b6145a2030031442c002418103114441e0003010800c0641c0180c415035001d44103640d0800007803c041e800307444102009002030442d1003101542042c00704003900500c25102c507990240b01507580240c550000703000b4290400b02400711507a09202d13040212044802c1d0019211411441c540705482d503200301e03a5500031001c0710765180ca00908400341c0b0040d62a810309d880780703820007055290404001c1103010182011954402d0202c034 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 983232275 1250 983231025 983231027
    0x5100801151124071404090b0609090702010c0807090b22090e010203090c0901030c0b1806070308151f030209040e030c070911030609060603040c03060501060c1406130f03 75
    0x101c9400c9034045011200012403e0036005a240f299a052404003409030340007075405442041925044200503850f00d0405040607400e202501c040c060713254000c2c1c000d0052660550310310980342c0c0101c0c12500005041e4540c141d005040300ca0003441c0ca03052010b525030806c00c80d8403140454401100d518540121030345901e85188001034075500483d00103041541c03068031101c0650007180107003441002c075420340300ea00040c044400000d20014010590221040203200c2c004002451100310450074800440c820303900256050300a0303141075000035214010007140318019107100d4406081203400210a003169140c012903d06030003004010150049070160594440307030411b164000c801c1003620748a1401c90b42c160b40d03448039442000c000720700b00b903070040381850a1804c503401484080e00d1000280e48010500006a00140080b0b0301c1c0c132900e680000c0410030a10845002c1c1007960f81d042480c0e08103082000700c800182c00105040d400c0740061019991030340500c10b203001c0d88000c0002442509040c = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 983233525 1250 983232275 983232287
    0x5070c0c05011706010e1915090e07020d05030408091c02120109230c150a1824200d030b062109120301090b120a0321060302041b090510080115 63
    0x7c2c0100e8160b508a010030100402c1f82d8200d03204c0e0f060703903803240c0050b40d841d2024940b6801382c500d9409a0010a43c440d143c500c990019035215014502c1d55161010102c04602c568481c00c07042d00104403030758102c40440c80d00b0388a102c001c1801000130710480b504d64945d000b40400301c549500d0103182c01c4c201021041e40901480b601103000510700401480c00310300d1801d45906c000142e000280d0414030000c541d104a1240e6001c1e6110248000021a18000d15a00440c101100b001c14811500c441410164501070345000038905100039281440541402802f50350a20004611440b428000e2041090f01b01d01e9800c0000b0300c0c00140001501c0f0b0106060520a00c1500c0224540001001140c0c800e032640040720b8401e8203548164805801465060310344000307590050010b8820640030020501403145503c02036046000095080d82e0703030380028211030007010070700116140c0550701c1030550740002c515401010107075040c2c04204070324a401070000c001405240d03c1c40c0b09100307a490b241480381d4 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 983234775 1250 983233525 983233549
    0xc1e0a0b18150f070801060513140109091a15043f0c030b0601031406010305070905030f1e070608040f0602211006030c020d030b120105070c0c05011706010e 69
    0x540240306410300c201c5843d00c40b5811115000403d0f0581d000040803885041129030810401500403022070511030950101103d011070241045100440403500f0348180c814074014852007902140101c00070380901801e14001140c21404290903c0100011030321040d04d60941280e4a900b042100f1081141d0422002000311a030042e1a800c0e200401f0400802d10440070340340202c2d1038041550740d0034011003c0c3c1d440142c07403c02421001000c0381c580d5009403c400e030080c5183c0ad1000040340c9401c08645040e844401251196001c20b4030084101c49416810040c120190042d101050070f1200c0a00f55000c064802030407483d141700600280411035045e0740e855400400d500042408141c03488000d0f0b182603e40e43c0ca400c040c000c000a66074020312503281d0024103500503002c1c080c00b01c0815001405c420481a40005045120314090b4000388100b5224043e10b89501004282d5030800d00403040b80ca8006a0500002e009421130f40c50045a44650001003441d094010485d0000803c001203c90 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 983236025 1250 983234775 983234803
    0x1b0417030f13080f030316080403090503060703061a0c0d08130602030408071209060207180618150e09070b0309010207060c11010b0d0206220b0c1e0a0b18 68
    0x1107480b200310000c91450742d00319901e4100302d58041c03882d111065140d20042d144070f2000c3c00341d00030110189008092142c0c7c414001e08110256a0395500868141001110340a0003c0c3e07482006008211110705291810000c00200a083c011a8000f0958445001c0d5101080c8080c0c640000c0c10690354055060b05a5400711083d9100e007480d14000740f0b9038104401c03c907500c441c0050b1090b80280304d10580303012280d0542c02014460314005240b10a507654444481c00103440e220045000d42c41c0b600304044892401300000340080d114542d0b4922540c00d070308140078103242070050042c10f0000003190010303120104d50302c0c2d5030ba4032800f02490091080c080000c1c030a6041c469582c105075001740c2200341504c031080003840703003880540c200311003040f1100e00254028003c1c01134031a003458540c3c2144540c401c0c0b110f5000135981b034140802c1c541e0040514142c155010894250403407601d88503504100407180d0082028010540d10004012001441000300300420340f01100e4195007000036880d04e50b58 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 983237275 1250 983236025 983236027
    0x12030a020a0308060616030f0c020904050a1a091c0309120c020103200304060c0201150b19090b0910030209060708091002491101051b0417030f 63
    0x610200a07485900544058022454410004040341000383c125503401c403403000d1031403041c0310f1030341c003541d03c810010540c000304800030804074016122039041c0d5008901038401400229014945545003481c8902046140040305062001d0030000264018000410103a22030bc26030b200b04085006203d010070240044424203104c040707664010134540c0700781d2f000384d8061040410781c199041e0404201201c03d201340500700f00160126034140c5c08440303410128400070511222181201161080751f4102d818040070008442c4c00801c04900c101e2070404040c2001000da5203000d080c030b0036a0190422081c0078408440140080b14465030444140d980020a1152140e1090070510035035040a00000c2c0600b40841c503841e0018000180b18241100040d0501d0445032050b0401c000880382040c0e041c004864a103080301e5048514a155080007029a03c112600d2510300d0313442c2c01d4800141c0740c0210300c410360345078620301c06030507041358155145003481e84081c1540081e0b071451841032044004507054 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 983238525 1250 983237275 983237287
    0x180510110f030a050702010f0c02030412020f1f030c030c0801030b040f0b01060905130b0a0612060e0c0a1b23070e0c12070201050c03040f290117061608061203 70
    0x1d10f6074011401070007564000c10070404001030380d504581d07084040f040540c0c000d03c000c0244594058944003141d00c00ba202843e11038401c4007052104454400a51a9040c80301c0d860350303029403501c40c40c42100550701e0180700040e20305902070030f0007506000c01380120303850400103802c0c09040c807000d09801e54070002090307680d0307034502e4010030f400024000d561084050700050182ca84081c020f654036880020080c460251a002040d5a81e14020450644068841d5030001300c0410101c6224030907058407041656640c0b01a000915454120400c6c446a541500c1d210010647c901030900d0380b10004584154910821070f049454000c06074800c4010f00c0800003049207050402d4041c02002d024001400c104d503e9100e0180d023070302c4048038800d5203618248000340204104a904054450250003800704002105111041604900362200f10081c1c41c1700c01041001500f90003880325403180b0001d84940e0901262413460080300d0f8260504020b10030001c01c10395990700c3d50030141c644414045a42e604 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 983239775 1250 983238525 983238541
    0x20610030c031e120206011a03010b090603070216090501050a150804020609030c0d2a0608060d0609081315050c031206040e030d060f14130f0b061c180510110f03 71
    0x906c00f40141034010011041581041880d002524141c811100c107440c10004000140411500010708200852094200d00410340f4000d008c1100580030f408004181e070740c1004144801c0c02e400c1c0d0303c0041410303025072502c081e0960180005802070780c121103081d034a201c103c0000b89803030b03000701400350b01515440345602080102e01c814046203001092440c001e2807000c15a9500c1c050381d101710004a0038000020300c840c900740d144400e05901c40e40000076420200e4403091085c0d0000164202801d0a2100c1030002c0011310245404038441850154580f0100d429180e803207029102d151040302c0008c401117240c50b501c581060780d03031440000c1220740f10b1000c5848030021300403501c212000300203151400328248000507650781c01d049002d41801441808500220010000b010b0689603107950340d900559903a942c8001400d011700c2c0400b502005006041e035040c203c83d044800f40e050790005114440c0003c0b400310360380c1c2e81c0300300d400c0c0700140d230280d060082000c0344207c2184528280f07001041020031 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 983241025 1250 983239775 983239783
    0x130602090319060b0603090a121709030307030b040b0a0b0d02040902030c0d0507032c0c06040602210304210201060306050f090c0a063204060807020610030c031e1202 73
    0x10b5402041c081c07064100301e205106451106892100e001d170861116640882d8000c0091000240185007a140c0185000b0003010110b4003503500390b0392030704004148000c9640c180650150316000b100c040203449404800101a8486840f4101401502180340081c020b0550b05503401411040c60039540c91511045c10340c0c0a90090510354034480c42c1001003604244240305070b04040c02c510b6510407440b803208001d0810400598140c000920603054028041e8950001030402420590001c10b03e002190b404030b10311400d0703040b000b003070307000c0030b004203c0418114001e055140400c0711184044094001080780900b507990000740850f0300308030601c001c02e41080700007481a424801035038809648030f03040000c5200d0506c20400002e0301c05190200b00b59003050f4180824120000100800d801d0035605682504540d000d4404611541d080040a07070b014400750b079010482e00707400e042441c01e50750341401400715800050940140f8a0241c030313400e903c1e03520070002940c00004649040c1c1c0d41030802540c0d = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 983242275 1250 983241025 983241073
    0x130f02040e0a050c0405060f130e091e03040b0702011b08030a1b14030a0b0310050a0c0f050a0c0812090c010912020906091b030a020a0f0509091306020903 68
    0x200c00404000072640102481000c2c0212125828071745403516110400080750401440c083e8250810444036550241400802d40104070071380100030b80d407602c2442035080c100310f400da48585841d0300008035401500407080310705840000482e030307071035000900049030031524044020b00e031000b140060a051000507005180b0a1151a205000f112100c003145041e6a5403d44a01d011900041440c0c0e41e54041202035544218540c100141202d41200007906c0c000310584000c02141c4e441080c080b00348131078024124a140355040200d21045444001001440b9101100042000000301c10b4100000a800c80b40d400800710340c0d10440c2d0404840450300c9242400c0141c0c04104c00080000d032940c06107201d04195a0002d0045800b0382d00c010501003c205d000f081c4190310b01001c0e0b00c8a4010303422501850140a0100b001a200e50030b144024010810300081401403280520204500345e44800c0d0881c2d210380c510303135102500105481e040019018194600e03526008600f501000e58000c10080d185c = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 983243525 1250 983242275 983242289
    0xe2413020c0f06010503011b0219021521010509160f180b120f10030b1302030d021b0117010314010b1c0b1308041a130329090304090b130f0204 63
    0x10121901008c1c0c00e181036603401c10303080560070039040301350110f088012807941d29002030b00c0c100c0c104941d0145032540394401c1d21510710500c0c1e0801d240d00100c850b003405501505098500000f00c1c10890340692000d00030f03d0344402042165203481c012a4401d103802441c00d800300c042d0060170390304c0c0c20018405811059148059648080001d0f0b41032403132089682c050070461a141284c5030454590300040c000090070f00c00100142c4500f400181c07810820100d02805560103051801020072404001d2045c031100c031810008a1500300000255003a6883d0440e6071000d0700310740031605104064090140c507001181e229000e039018000180c0d552501c420700c1f40c4907001200b0141d841010714044401440c0011300386101c148418400ea240580e110151000f1805907a81402c0d40440c0c05c0580f04850b800441e002c8840d154100a0f040c4043c1c2c14050881c110728200f10340d8a000d100c0700d940c3c0c1c007540c81745211454580c40320020585a40d07900d8410a600084140150040060702d60080c1d40103104801d = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 983244775 1250 983243525 983243531
    0xf1e02040f15140a050a0902040810060503060a05060d21091a12070c0c081c02010203091b0a120b0f06100f0806040609090c0e2413020c0f0601050301 66
    0xc14104a105401c0180e001150b0008014141104000b40046050401c0d4000c405120040340c0366403a40b42020050604110240e6114107000303001d0304001c5802100c0d070055041240c00c3c002c030340c1e0100b0b0103640500c81320303000501c694460300042d00007842d21070041c021084061103580b492030345c540c44025210084d112000d40550b034100e4107103500440c2c0400c14a00034180841144100c414030680d410030f81e18500800f40758020f80b941350401d102540010701680c000302d5140380400346a031005100c854580003c6085150140801c0d8032045c2c010b80d00720400401c2c2c0c90074000d82d5640703190000507040800c0c0215440c400da1411406800c030030b03210a0840440d12000a0061070903003803015088070303159561045001070100070f8036031030809000c0a50040c1c441a02180381e0303125100740b020580c007400807511202e15002c0d108035403080150100c110f9000c010070075030104d40220018480400242c071440440252109504000c0c010b524502055014038440000400c03000101d96040c0c40d0308074020 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 983246025 1250 983244775 983244791
    0x130f050709080d0507170906030a020429090f061b010509070f032319060c121104050f210703050d1d01120e030307180b03010605030c070f1e0204 64
    0x8540d9040340c2c0460000082e003c0145ca0001400c0c80c0405101030031403003241d41021001c500069050f001140c040150030b5010800708850140c0c0700444074402c0411220f5140301a12850002d52885402000e41c01200561902c54950b1200c0b01192407544c0801c2c02841a202c500300d10387d01814050314228600c0c410310401048507100d480080c4200d0340d0180e06207030392940040343c480c25184031250407902809410202030314a120075040c0140244650000214050042d002800082e5024005e141c21480c020103082003030310580c01c80f010f4035000c9441800e520300040000e0700c101c0203801403030640c001030503001e01408800a210401d5034072642c01e8070703547d43c140c0900b1500b41c00c0000c00c070180c0c0038030980d06071000e50080d9002c6141c14241c420210781d84031005003007031844d8000c2c0d50510000d0350b10300404007a02c0d014074512000c0c00410243c9403555141400050403400050407a070060709000030b40e0010072491015070900c00d40c0c481c0081c101c228000c1e0034103004550344107003a80039600b40f00700 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 983247275 1250 983246025 983246039
    0x2070c03061a090f071b1703040305070515042d02060409050907141c080c0a0b0601020d03060f0303081e010e0114030613110301060e0a0516020f0309040209130f050709 74
    0xc1d41c41801c403a46c4280d59091090804a80c0389441a01030b603c4c080e01c0c80c0c1a041c4160013800841c881d50282e100c595850314680750a518003140e5104081004070000280300024051101d0b8002c13455038200c0c0810010f0320b0411a061041290000070346c412000100000c00e10382c1d54000501c03d21705241034964540c2e45e40c0300e241d07c1800801c3d03007950090740c00098952841c0704a0560445074040d2503050308101c070710219280381429200e07041e03943c1c1004e64100b19941d03904200841d00b00c00ca9240901416140c0350701e6417071140a43c0402028807002c6000a00c1721151604c0141120194000200b0b039560b40e00c00790b140b0000d080c003c940205130710324441000d03801c1c00103403a4010011051070040c81412a201c5075812007071104215859500e130000003500c03020403d40c660040d885804001100e0030f00c0e009a80c081040a903001c1306640007130700c00d03107003140012098030780c01c1c041600e000d40da4608060005000500d0b80001445051a1035030080d0342003140d90005100d00459141c43c280b0b01e4030b40d08 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 983248525 1250 983247275 983247301
    0x5041a04060f18090c0e1918050a080c0a0507060302030910060b0912010f0f050612070f060c0206090405011d012403020c1c08041a0f04030302070c03061a09 69
    0x286800314008400c107881d0b40c03c1e0a034400740540d800703a1912108103485540594041d0340c180c0b480210790180c1c070381e4180340448601c2983e020101203401d01103505419a503154881b444688090034608000c0742e4403804003418003810030069407240550783c0c615215000640250010b13074489041d0300c103ca0144851100340d200d41c4090300c04048000c1d080c1110b40040002e600c0c0460300340051b035500c41e151410341001e64000d203600c3c4d6105450104052a0450900c0000a1045a007480e50791200b0310070041103146000503410340d0f50910f072803020704400c0d00105040703100e0f01e00c816030000c1c0b81100004880b00d000110865202e04c03100e0f10481c99a844c10380c20401105a0050545044070300154003280340039900601104459000361801d8000965502e001021003030810004585068200420007010010138900f0f01c2c43d1013a0800b990800c0b0390b000c00b411000034070007000e259001818200f40700400c240500110f5024000740495091200c103a4415441405043c1c058140e103800700f120700c0c0c0206 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 983249775 1250 983248525 983248529
    0x209090d080a02070206040e060103060e13032601052b06050619060801050f0a12050c01120501080613031e02030d182d050703061a0409120f03020405041a04060f 71
    0x380071b20b04150400c0e820b0204100054407481c180b5a940600040141d02020918400d840c0d00010320b88120311401c010b0b010500c02c0e86801071082d841c285e007460800340c5020301c070b056507070a660080d1024180100311014180a041804034201c03180c0b4034008004441d00818450f80341510600d10403440c20451902d102002c3c05400c2c08200c511005001900300040b40384041140141218140740e500c54403184002d8404205944503008650130114039600446403044151000710f0030401e1750700d08070401c0e80300c5a015100c615501e80e110540d07002d052258000f0100c01600c040801708440c2e0181d000303503899200070340c03c0070102d00300812409190308002c8981c0f02941c02c0303441c0c4909515603000c407205c02e01c017210000c8100284800801b01041081104601441c0704013070015039008640300d100d200208144c660f902c210708041d04030300028038087c070410030828030381080b118001c020782c400e030040c2c016a0403040d000327850f05241140d0340b030300c06d1640c1d074000909890801440ea2101c481404500c418 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 983251025 1250 983249775 983249779
    0xa120c050604110607020402220b0c0a060903050c01050a0b0102370f0c031a010509011410111618020a0503070c080729090c031e0a0209090d080a020702 67
    0x36800250201d8440d110f4503a101c40000c00c0e00d85000d00641c0001c041360071100c0446000458404a071b400f101c3c00c0040100030300160103919007410114901603076a0b1800c6900200b059890328104400c041c01541035131401c030795402c000c1c04285010f5005134024031001d00354500600c500c0e00c0d0f403400c1d06d5000100640c0e941c040e0b075020760503415070020ba5640201114003128010035600780d1001003054074000d540610312039020b0340549010427000d0700341e801042e00118461040e2100400c00c0701d101540d0401c01d030a05688a0284640201054072400501142601d050155500d51940103610018120603140002c808003030503da4030518008038025100000c01040702000401d241e14041d41e43d18141a2044002910704030ba10f503590100e00103045e0080001a004503500c80c40348040c40349141e03120729104001c102c44e01c01d40d00001e0396400d8504002c11040e414545202d0610424810f5481454000d8001412400e00401090b503481c41110000b000510040c04a44640b4140c001c5030805032700 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 983252275 1250 983251025 983251033
    0x110903072c130c0b040f060915120b0301060801090b090a020904081303080f04170c0603011a040e040506090f010515120f010c0e03070906051c140f0a120c05 69
    0x4400a0801c2200d000d004046001c09400265000643c42000710000d0000008010344551a000c1890128001078210303006202d041c3d20280000b0380003110301c030a403200030324203007a17a941188201d000030300800b1810390300f40d402c102e00440c948005405c03102d038a5110703849100a070356950380d0722600c80041e804003d500110110208000c40c0b140405080b0301080c100fa844a195521750b42c44034598004c4103807020500f4042070400c010207c40d00f001d810303040018017809211748500d00040b100c0c44140549404d035840c40c0c4407400d2502e0b08100380c80c05013484602c280698141420f1003176880c0c0d01190100460b1195149100102c0c406004082c01502883c50b4a01c1c4040404200141c549805401d0169480380f642c03105200c034400d0180001c4544651600490a410b0710281030414004d60000d00e19682461300800850301c840003821800d0084c1c0c0000b07485114140b0740614180900610f5410520501c43c1c0700c403001c5c50115803c442e2520031400700340c5410744104199010300440e00007801e03c1d00 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 983253525 1250 983252275 983252339
    0x60518040614062a06010e0105040212010b160b0103051b0d0308070f1710050901060e0a03060e0a0503070c090f050609192c0f060c0706180611090307 66
    0x410502800c0960507007410b4904000960090444d448012070815480d0362100d80100b0510380c2e202403083c05014240c40a5191400d12800c000c00b0150602ca070590255001400008010754600700c00342c0b06520298041d42960340e424000c1d9160054680a1848640a501320089140004088806560645911215a49c3c141007500c03011300c00c09014080c41700007500412003410300c44049100c0c81c540d00ca40400d150800701070001000051700001c050010b50451090039545440b00201240d5000c0c90209030300c080c01c00307000d003002c21000d4003d000d17100c0841c800d81000702440c080310603220062401c1000c1807a00140c2d609840069610030f402080c84400f05070703411510001c1c82c2400c2103a400100d501d0400440303001455018000e44a00c6d00b002c0d146800b2020414442d0940c0002400004c01443c201800c080c1c056124004c00101034603604c000503d4118000d800c000001078024600b00048444007a2180f056070044dc21103200e4043c448011540d1190b0340c85907042d2201507688103504507 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 983254775 1250 983253525 983253529
    0x1060506040f060c1106041511030901090e0402060c01020a050a120b010504181b020a030e120c01081503010c0c03022a100504050310020c061b0f0a0513060518040614 73
    0x1c500321826116008003d150000e81d0b1248002400104040043c0c2c8d1040301003204010081c0e401c08901c0342d1150420041429941e0f4000702110a0b21012041c3e08038589030781c0300041c41d900c40c40865860550001c03a1002905070000050b00d078014164544110320300910000d00c085070a8444c88a02151007840f0034011841c1c020304404040c0c44041000420302500e070841c1030060002000d6000603800799908c10201a8400741141d050b12058030075001103000e401100d9140d00f060007031141000385010008810708000d1111442d08103014008001e45060898020106105a1400d4001d4071a104130b52004e03081c641e400e231180b5107050381e2001c00c04405004008400003c281c50784d040080074000800d060b90140284144616402c1c80140e07548105000c81c0c0c18424010300d908200b8448600045211894000321440600c0d018801692241000d80c2034540740581074810200c1b20440001140b0a07401c0001841c903c0400b0480312056548102000185c50380b0b4000c0c0e51080c0b140f501d5201e198 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 983256025 1250 983254775 983254787
    0x80105100e0912030c1605010501060e090103020303030f04030917100e0d120e07231906020303160309120906120e0a0b10170c040605091e150307140301060506040f06 73
    0x4a00043d060306e182c00020aa000702070002c0780d2055a19035910f070010490b00b50001c984c5e0f0102e07003080e10191130a600d5500060307201d01000701034218010710000000e04040c402e248401c054026121900e04041d41c0400d203e50300c000490303d42c3c144518100304800c0300c9000144d1a44030300c1c901ea80b0307284000751181710b00000e4081d141007540355210310080440c40703021400c120450300c8881c2d00750341c0c00508988104480b1914441010341d003090300c2482440035a034003008072907006078800408540c104d940340044006103241c2070301070081150884540a09980080d64004541c0703a540ea6502005e0145096811920850105401c0d83c0c0503080303541c0091884852943c2c41100742c0320000745a40e0b101400380c49091824090201900107c0c4d0f00007a6141ca44140d401503c0140c543c00941e06d4901da03841541102070000010b10464000091154003594030f4400c0c000c9800b4013038035100380d84c0350304c0d510429081c0e100312442942400808165400c0c0300040d18120b41c08030701910002d514101d016219 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 983257275 1250 983256025 983256031
    0x309030e1c020f1924110604240608010516031b030f0e031b06010f0b09090a1e020c06060d2310150602061f050f04090c080105100e091203 61
    0x2100b010300c01d4503500000784081009140d004030b030895144995960109848045c100340342801410002c0960039900040d4060344254014501c192142615a04411803070781012004103840c10302034046121034064006e68014449441861240e52078194140d094601c812403943c00b050f44400103495181c0309030001840311121500009a2211915800b42558080c10003d40c2c0084221001c102691040080d1401401c00304610700a0030309214001440e489000401c2d4421801040441c002d031030268000342c40c40d42144502030303c03204c0f2203008001a40100103508441c0c001c03e00011890b050007149000030355030107201c4101843e1000e80840514500b40c0300048503100b070b11100308508444e0302c5443c0d00545e42000031070b401441e0007002880e161000700160040f1000404140e240c002d004200c0c03050f03070002c07203c064555481002150080904e00c3c00034040c080c03e110000742510065102c28010b003080c0d098072600d07a45034005c001140c8400d4441e051554040a003081001c08540f01440d0 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 983258525 1250 983257275 983257279
    0x17040506160e030706020c0306010b031b0703031407090815040b0708040311030706020301030c060f0905220207080301052805010f051918050d0317100b07030309030e1c020f 76
    0x480c2c004840d0229141aa0a401c41e02c05644404000300759443c0c01c111003030050000c0c0342620b14505d041c1003003071110081e16252500d0301001049032010140642c002d0003075843c0400400b240c910300b80c0001001c2603618030450031980035111044504d41d0348480c42520032900320569a9107034030344410454401c034005005030100620040c02c084441410b20007019021300890f000b685035411401e10b140180f44a0380441305003c124583c50300317030981002e42d8000f00c076803c4910000a050005014109400b2000c2460b0038038400105101007000d1600594142c620039599a02d01c220001034849800419140c0c603401c8414041d000c001030740c86585011516409890070a0400c0c0c031207220201020442211800858848071158a00c108541c07252002844100c9100440c8a80c1c1d45021b00032410908598165040d0f503c0007404c90600b046502c0d00806e841008580c1c1e500d518240280100390042e0f0481c00107030082d141c1c624601d041c51185200c041500321015188403030390f0030403c09440307000b403c40d = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 983259775 1250 983258525 983258537
    0x1005270f1015030212101815050d0c0f0602071a070302120f0a02010b100f1404031a0412210906090203010e0f0705120619020409020a0507031704050616 67
    0xb080100b1041096900c05031662005a180e19030700b028030300114070042402c2c0031002c1030a001c11000c0c085000e4000081500900003a8000056910440c5404130b034000607040040550884104510042d500045132110000503030700f45e880d941c0c22a2505060310806810723500c003818000702c19101c0c03002000304c9072181c0100c030ba1034a18a004d0300d0b50b03a00801900e447e000300104061075155020300030100f1269040310080016012008007501c080c0c0c400c0c1e6840100f0000b40d4011070012131200480340a10b4100d041d0650f05050f0400310b402e5480300b1a021220341d042648065a034034015150314a29101250107120460544c024000007080644030640f01d040d114584200561001c0c4184500c40345c1d264054080640182ca01604c0c10b06141e2010f40200b03003c6055802008c00400d4640d0484035906c0450050300556032940080d014031740120440504c0003a002e40d8150300000101001c1e40f181c0c0710f5159080440007103040c0340340121005000e13600031400007260421303440300300340e40c11445003031407 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 983261025 1250 983259775 983259779
    0x101b050322020d030305040b071e0f1b2a030c1215050124020a0f0b0903040e01090b01200a1211060a09050c19140a030b1005270f10 58
    0x1e44600443c0c0400e4000c0395451003400240020660781c154404441d0600d28a90b07000032500300701400818065404001d64015041f81e454424617200c03000140d21460b40c40400d604c1d04003407035031500c007490ba50400c10340864100c1071102c240d40300300d0469030851104254a840d196031902211090385040b1080c200440300703058480c60601c5460f01918148812808428194ac513402d864540d010b1144c0c10765110001c01c034000741c145040301003095400300010810b61140c0d85294510b000d5500f010304401e020200100c1d155a00b0b6000b2220110240d03140d1011000381c40d10901890040c0420040300e800030100000851008001c92410021600c0c0c0344030a8030610074a18140358081c1d400714601074507540c10405000003000081d0456000700c6180a445211b295031101940743c522840010b000498824980c60b40c0c0c10320918015900004440001d14140361910040e80380e90203054458007445090842d9600507a1100301d00200901d00d10303400380c0724900354503446131000b01040c00e41c144030080 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 983262275 1250 983261025 983261029
    0x90706031d06070e0103230c0703031812030c05040b030a050709080f0105010513140f0c21040b0c0f040b0c01110a080403080f0402092412101b05032202 67
    0x2124890780c3c0d40c4c0d950040d000303a01000141644c80d001440384140b13806c6000480200c441c00308950304100034050242d0b552210f40b034240c1c058040e2a0005840000402c0610300340241d145105403040280d9600b0012840e2032101907a00380918001c03078840c0c1030103000107490304c4440c0d400710350007807910f00309100600e95890b0220718200380c1c0c017045000c0382d46031401080075013400240030130391011201d414400c4c9a403500e0039031b43c06500144446218013400d00450846c01c1c0311011980c0008607031506066400b590442d02d031850806071400c9584d039000c0c8001500c040f19a00030744e0950900d41000038506840c2001103049074100000304040c2d950303201c00e10141009408000c0016003080e466100381c0b440c09003409003042c00020401d0342d4418100081000698a0501007644848003074107109401100b280c10340d13506034000d1030160700308450344a01c24080030f0029010301409218403080c00401944000300600e100f240c3e0340040400d406101242c1800d150300c00000031240706280c42440d0701800d0300 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 983263525 1250 983262275 983262283
    0x10608030c031323060706060e040807050c09060102060112020604120506010816030503090603040303150b030108010f020702031209030f1b0103060806040c1a0702031c030e06090706031d 82
    0x800c000c01e070303000282c410000a880e0900800a00da2414614241460350030309103850b1080100c071a21560700029501c0401500b940098068500c0c000440c1d10b900c0c20380390618480c0e20004042d07940c1d00c0307011181e420624120310164460038040e4080c2040b45d1801d940b242c1416584a0101c2c0d0110302404041085089004401d8085002c0c100034210b55161505d05410901e011052a40d0040c4030003081c001700700c00204039103c2101c1a20798641d260791b41c2c10300b14018140c400d401300050020b5400042d41c0310b02c0c040503506841c824002007180c0c02100518901304d105d8000c00a402da04500d5060030718a441801804004070064180c0301001801500d881c00d006409000852001c40c4c0a080c0a440d6498032464005d0304407000106140e0502e925899180e0001e445006560010805500f80c0700640320f050340c1030b00f07601070111421800200310b403051000d205440038002a00d01017401c0c100f10400105c43e402540260040d200341802c1c8003048000d0310015000340003041d440e422529000000300 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 983264775 1250 983263525 983263537
    0x1520010209150315030304230406090f060303090f030b040f110a090c17010e060d020f120106050f040204060519090f1202031b1003020d14010f03050d050a140c01060803 74
    0xb0342c1c0ba81c1da15007240200840010784950300d009500500041c48144103020201054000e100030800381c210020700020050805034100303403400307810034403110310b02000703600940156031080e21003a40064a415940b81100300502c000382600c400741003c600030032035600301000702d68010040101c506e002d1328007107401ea604c264000940306550f0340240c3c80803584100301c050043ca803403000c0e04d400d502d840c0c946102d240300545490701c01c0c55140300d0070b4119500e000081507114030207408191442c1d032401c541030003492203104070b40c0200185129088117280c14401c03a0155002a1280b605004500510ba54050301403030350303001404920385003c20000b076a110500300400e070410066203082d02500c181414990324001d069582c44581041100643c0c2e401086410040640780040e1036000c030812890103490030421800341404480000725030a101e0b0035810f001d4078000c2e000c551006c40b44035800c95952040401c01d00014881c060f809051044220041400f040c11400100d403d0b6107804080741554008 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 983266025 1250 983264775 983264809
    0xc080901050606430c09050403080106080601091710060801060b03130f0605010902091003050f0112050a0b01060e0102120a120905030d0c03020c1603050a0609051c02161520010209 79
    0x10070070f044204a45e000240000c0d00040e1360a01107410140e8015061900600850f400d010313100c400101141d20a103060707001400400401e0782c864034640610340e03e560702142d10104041c20002e0114018805011740700447c0d165030702080c51a5a0624000340010368000111446800104a1004030754540203050281440700350050b80c42c2220030400c800f20003005000c6007030500300b90410000040c6042c2440c1100d100362109801340c100c078601541003605103900181250030040000c40c840341d0000ca20001100c0c2a02111006440980c4954543c010040e22a001400c502d0035440c07184c00c0354000c445041e205030101c3e4103207028500a83c041c0d40e800104003001039030100c0c0707018141e04200004009400d01e18100c03025141543c0358252500709042000d04103d84444a0303404221080220b00818105a0760180c6045145040251900200c203a401c042940024002c222400c10344440740c3c2400b2261240343c50a0641003011140300e850403003001541d542400319114503154004d40090200c49 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 983267275 1250 983266025 983266147
    0x90c050301150e0a0504113001231c0f1101080c090a140d170a1d01021c09080d0e1e0616050c060c010c080901050606 52
    0x1410b500d0320348021010b80020400511101400701c80d11a81d000809650090b20701182036a68400181d826208580e801c0002e8400200c500309030412009480550103145c12120394207982c1c800c1d541e5070500d030b506050340136501120400d00380780c80e2030305154581d50f25468400040c050591102c4840d00b00040050ba64441c1c9290001d20715039100107481d52150a0046039424080b10b4000329802c00301c1c1d80280f030300b0030001c1c46501c5056524200505030187d0702502e90001c0c05050401841c054000c4100d8401203540340c85183c1c1012005c00c101611140d043c2e000706075512041d0a6090240f1103801c0d02020300006980c0070a0300101800383c03902c9956952540b0b400b2441103420f0044064006401c001c1c0185d20740742c0e1080325034a940403105000c008030844d40c0c1c07050490400505080c86900210381c4043e000550921f03111064011900c221026210a01c040e95a07582c0142a10411550341d60b01100400c02046402c0300300b100d400d04401994611805401a0b0b0301150340400680c20390041014 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 983268525 1250 983267275 983267279
    0x250302031002092d180f060328020607060e0304080c0603040b1612020c0318030102030c121005030d11100621060f021612020a020f0913060507050310050a08030a0315090c050301 78
    0x2001291b070356009001074006203600b0200c00055100e50803d0b102003a03151110300c100c40159a40d52064910444e04004100031440880841698a9100c0d100351000c5002d1b9603184038481c940501901d00c100d40001402149903204120030306507920282050091085040403113425518070b1015000d003082040095075200f50108030000032000d075070180c2d403080c0e004104008550304c4c0c11060740c071a041c0111044029454038942e039100504c04d6002140c25100704d4410000e4198441603611a03120f80b070040d203d04075000c07040310003030358030501900801c4940030f2543c07912810407040d041d03200f60241c1c03000122405103811030b038141c1e40150681203078441440c4904042c000c40c442c60200102440c0014a00d0714100d901103000d01c4c011041c102d10505000b80024070b0b810f015011522640d034400020801d9180840e0040c1a0750803d548550b55101c00410104031824403220180030346402c14011400c00d0114841103001c0c020030000d120820000000003d90341c006c0d4040d80d4044450741d107490362298 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 983269775 1250 983268525 983268541
    0x90105092d12030f3703050411060310031203140f040b0108070e01060e0a0302061c0f060e0a05060d0b07020106090b04270302250302031002092d18 65
    0x402c8850304458a4204121940c182c1c3c50210440398840281c24440780d48080c01510144035030380070b04015640c01280300340e501d502d80e815031249106900c21020745103001011428005240070488003018551403030002171010800b0fa003005640700c2c2092030045503185191b003203036840000584640d000c0860340d9050004106554500c10f0160600c04010700c0902d03d050380329808000c040c46034000380060340000f10a03d41b612003804003d950003400e007568450307040603200700440c04003a00c1d42815140c900303000c6030302c0da45006440846001c05500190b50729103140c45001080701a20070780c1c0c4006110034030000514690500c910506441e000020380615140c03943d07080c2c3ea40d5086042c86545040031614072000c0c043d002915240c020740d41800050190b107416868041074207019610340004410032090b134180d4404101c02c0d2031098068031414000d5402c1c40c0240d002d8072050580c0320002140c507861801d62805061514180210000448001c10010840502d00c40d0061516511068100705c80340c = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 983271025 1250 983269775 983269789
    0xf0608070e180a11030703060c021f150314011b050c0105010801090f0b040c05040203090d020f0105070c0f081c0603020f1f050a0c170702090f0408090105092d 70
    0x40080d24075800440340040c5a2183c445042100040500050140b150b1150300c0402040000d503074448130401c491401000084e40e6888214050036282c07048070402c2c0c4040d4901e000b00030b091503801b00f42518941c19696583c014815100854010799078901d4480101c442603078030784010030000e4440747e56802101d800c2d40d00f9030f03205802c01c01003a030601c1380000c00245601e50401c0d034070b03030000f840da0b2241c1c40d24034083c00112410344c003041d441400402413240b8441f02103a4100701030303503d800b00c03400ea200f11515039007601c1d0215032082c045140040320802151444000340686446031031400c2c90003072501d40e0007000d606842141400d103544c0b61414011402d08100740082d405040b61504d50129005008a111a0720305080c0340410501084544560307000700030803050941e00c0300041d016400c1540321a80c09400c0044240d00c207810210128141907841c141d07141c000c5400840e960b180c80152001034520344d018940070754101c106600891030380f00741c0925020030311072510119a4001c85200411581c = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 983272275 1250 983271025 983271031
    0x1e062b030c140604030c0f02061605031b070f09021b031215041b03180f080c1c020c0103020703090e0a0603030f0f05030a09050703140616030e0a0b0a0f0608070e 71
    0x843c0c0c0b00070140b0020075001450b5900c0300d41d0009821143d0031040c0302191882c042d0088500003010040c014804100d0007101400c0b0795050401e28807864183c4128441e541d030640d2250a0780b86854400c00d00c00541681c00a22038058004250100d82c04000b00e107a10b136500c01c07103e00c0c140340c40c00d0007405809041d08211002280d0101c0c1c09000d41080e250741058a984a12202414981d4802001000e21039006081e12071503000340c0008100a943d05080c519a0b00c014040b0001d400303110260003017411001d40164810646500a080240441e0010f41c000d42c4011400e4003480a00d0400140400d18072818610400d1404000700c0c0701c600d903140280010b100440280300b40007036415071118082d40700b0140c0e0f500544a40000c100b021243c2003a504144040d00f014002c2d004c2c00d4100901d070840080d4450080078000005400510200e100314122030441c4903100d602d40049a40c03c0108a00f002ca0682000c20030750b0020380c020b0780c0d09280342118001d5100c207000d500f00d07650402815103a41c415030341c = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 983273381 1106 983272275 983272313
    0x91d061210180b01060801060c170f0a03020705010c09050d0609060b060c0a0b06060403020603011707150306060201060506040f0b1b241e062b030c 65
    0x8880b000d074042501d4500c142d000003c1d5451086c40c070309040f00c415580e0340000058a907610490040c20010032031202d50305004950f5001000001041140c0d035603100103951302031034500b40b420765200049000500c140c1000410440e19400207c804055002c503002812a00351300c0d00710001d007000300c1201d410034004282d440400d0000240c0c0341100c1e00a00800740150f40700d40800c900742c45240030003504013000344010441794501e1a0700d007048105000686404540310340340f21b11210f140220020000c1d880e00010480c650702885030300d000d8034043e0b904610349400c008800c503a694032485410003034000001d00483d08999008500243c101181c1540c100b461051a240701d07840340c1c504d5555140468001080c000303c01400685120000342240307200550300c0c0030410903010840c50360860070788881ca1058100c10714078814088c58601c40d442d0941c24021505185d01c5e40e1924040c904 = true := by decide +kernel

theorem cover : BRFrame.Cov 983093525 983273381 := by
  have h0 := BRFrame.cov_init 983093525
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983093525 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983093525 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983093525 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983093525 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983093525 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983093525 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983093525 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983093525 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983093525 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983093525 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983093525 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983093525 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983093525 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983093525 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983093525 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983093525 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983093525 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983093525 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983093525 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983093525 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983093525 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983093525 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983093525 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983093525 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983093525 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983093525 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983093525 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983093525 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983093525 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983093525 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983093525 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983093525 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983093525 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983093525 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983093525 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983093525 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983093525 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983093525 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983093525 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983093525 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983093525 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983093525 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983093525 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983093525 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983093525 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983093525 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983093525 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983093525 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983093525 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983093525 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983093525 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983093525 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983093525 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983093525 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983093525 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983093525 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983093525 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983093525 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983093525 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983093525 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983093525 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983093525 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983093525 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983093525 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983093525 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983093525 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983093525 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983093525 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983093525 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983093525 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983093525 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983093525 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983093525 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983093525 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983093525 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983093525 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983093525 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983093525 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983093525 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983093525 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983093525 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983093525 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983093525 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983093525 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983093525 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983093525 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983093525 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983093525 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983093525 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983093525 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983093525 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983093525 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983093525 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983093525 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983093525 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983093525 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983093525 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983093525 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983093525 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983093525 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983093525 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983093525 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983093525 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983093525 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983093525 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983093525 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983093525 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983093525 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983093525 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983093525 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983093525 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983093525 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983093525 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983093525 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983093525 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983093525 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983093525 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983093525 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983093525 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983093525 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983093525 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983093525 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983093525 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983093525 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983093525 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983093525 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983093525 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983093525 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983093525 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983093525 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983093525 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983093525 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983093525 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983093525 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983093525 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983093525 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983093525 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983093525 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983093525 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983093525 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983093525 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983093525 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983093525 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983093525 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 983093525 ≤ n) (h2 : n < 983273381) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
