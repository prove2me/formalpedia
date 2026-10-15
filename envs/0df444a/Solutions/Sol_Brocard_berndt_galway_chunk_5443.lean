-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_5443
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T15:53:02.444697+00:00
-- url     : https://prove2.me/submissions/b1fb9588-d7d8-441a-9d63-c94ac2e1d546

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 978776978 ≤ n < 978956834 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 978778228 1250 978776978 978776987
    0xf060f040507020f071e050108010501020d080c27010e040507020703031b21110705010f0f140307020d1b0507061407080a0302070519080409020f0405041103060916 72
    0x82600d0214480c0c58046040e403404c0c00f41c04482150b030090f03a0f0045590314001203050310002c00030101c03000c1c6584d50070055901003802e001c4c05005030007a0001051581c011386605070080707564510145400f1002d0000401c601c0c1d9405115240c8000c0101c400b03241d070340310f182008030040480b410881390400082c003968802c4c180c030005051056800c1f20f0744002d81c8040e02d882c4925007003005c4600d403603403c0c14240d20907211340b000c8801240b07404110b00d6400c030b80000c0040c241c84040e180d182d03028040c0d01e402d460a04261030100b0801560724504400004807401a501485941d0018483d030741084270301030319030022141071543c000071080030200440d40028942040300c84604001c1c9101c01d120548544030b20405401130400b210000e079403102e440d419401006010b001ea0b055407462001c2c01080700c2007541c49a0003805500c0c00380418030642c0d0040d03000b014100346044200740360544d81e10101c2c00b039070310f0301e11108480d1201104010581c1482252294041c0194901c0350000c2854403005d803 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 978779478 1250 978778228 978778249
    0xe150f060d0f060207030c020306070e0a0308030c090a080d26070c050a06090b150d03080c031003051c03060503031e0d09050619060b0a050301050f011b0c0e0f06 71
    0x14070a0244421840074030501400881c00780303030045425507454815003005808820311041c1240030344142da0000354103074800c4603040b80001c40241a6040f0900d50344584c072140c0c0010f4140c2903c503104015122166590300d001100501001c0302925100442c0c2c0c0000d003686c050310080c0e1480c4e2240345450082c100c002030b003140d80f0116506082c050751440d411714a140c102146001440d0351f01c0c00550405003c0c2d00c490743c034031032400391031011318000d8140306001c010b01081d00b0003804907950802260071041e0070809981d00c0111560041c0041d0f90f01d4854038a48032003044118041c5958400380c0c000350341d150082c440a084142e00035441e1901000c082c05034440043c0c0305a40042021603d49400200354000d200c402d07030071000700d814504008540b901c24100c2920b801c901d4914080001034560b08610680328111019215242140e18050038003074102440d12241d41080f203000f41d01580e07981c000e02d5442a4601903a0604625801c020030046212800381c12016250078200810846503601e20007103 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 978780728 1250 978779478 978779491
    0x2803050910022d0c041a010c15110c0115060f0c1a15090604230a23150405010302090a02070204060b270d0503030601051315030e150f 59
    0x607641031074120802c90030944007825014002065072280120000f1208000102c0b050401c20765145082001c00c11007111078101c402c1c6090091450048019130141110564007402002e5000c82d024041b003e40c0b049400398a0a010981c2004c00c1c100c103200c200744900d4010810743ca00d03420700c0906285001e011075403540b03504003c101c1c44400400c01c0100880018440d20340c07004076400d00742081c90390340045a07101035609002e01001c10000c2d010b031409010300c800500c2078039031620312062003031a1400d80840c02404140c40548826009805001050401174035540000c07038682242080c0919206403c0d0101e22070b4070860138a001800960703500c48000b60030440022006175102e14070700c00f0801a041540c80043c007510003003544910310300404200e85d4228030303d4840c40d040c402c8003010030106100c00d00c000f0301554403d0000500c0da5014000905008040d804002e4040f544c400660401d404054025000262110381146460004200e00554101f11903043ea44a2900c02009030700d000700185403 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 978781978 1250 978780728 978780739
    0x111070c15090302100519090f0605070203120304060606080907080d110c03060f01090e0105040506010303050703180311010801080303060d080a170a02040302031903020d080403110a0528030509 85
    0x3092000d000301466401035a0141050051700543d400203001500000030b044280300138045000c1c2c40511861003601074503030501c0c4018140741451402c454903007192204a806110301010507400c04003e030b000d10310a510950340800d155003032520090034500d020301001c1550f40310032070501003444040759900c581c615600d02030600750f4001c1c840d54540755004000580502588050004000715401e44505a441c4031200f40089504032000c0c030300300d0324100c401034526000000180006803141000300784543c002c0c5003005e94041105019600c110075070f84110382c101d00700c074120540c07541c020740b285005150090103141036207850310115810ba07030300c1100200380c01000200240c0650190015a81d450b40721186600c07640b8101a1400082d801400164428400c032900320100365844440214180d078941d01415803401981c0040d100f2900182c021000c1c000c1c11250300300c040208001040c0707094003543c01041070b2820025030194500300903042e00c80300c100245100f00401c0d003004c11202a03950a80d032 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 978783228 1250 978781978 978782009
    0x1c1404110f150d0b0306090307020d0f020a0803030106110105072d05040801020f0304150c0203120411090f0403030614030c06032a040f0803040e061c06020f04080111070c 75
    0x10b0140b00c0000c0c40c550400c900854441c4003090705070300031406004240d080360b9007030303d640c0e0f440ca0340c0f03004868009600c000e22600380c00004813140c1048444038030291200084544640c01d080c255003098100d040002c03000f040500002c02c0034080d450b000841800c065002e5200914404100c1c0140f1404030310b00922240389420540c0304904960060100070002c5444611348210803402d0b03801a18152912078010348201100603031489140c1c2003403002e800651070128003e04090544030010410f807060034881c4000045070304c48c101e102d44030700210310240c00f0a182c04d140c043e00f03c501580000300074000001c40342c7c0c402d8400040e0009406411180e290f1071303030703219500c851181120310100580034440c1884403d92800c3c010141098400c3c07508180c2c1c0c25a200c2521035070b60300407403003034005032202400803903514200321140d4041c141d242e8028800c021102c3d111102a6440380c0c480f50840c00d000501001700000a11400012119440242d03207056116180c40c8840305030360040d100304805044 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 978784478 1250 978783228 978783259
    0x1030f030c020d1b030201090515030f0a110d0507111c2d08040b07050f40090c09030f0206090d0c03050715020d21020904021c140411 59
    0x1405110355640c48240b031a043c2d152082180d807500c0e84d80c4400c902040c0c0c540c0c0081918604003c18004864507066140e0960b9070350340d07542c00004405003d0010b10703903031211a0707404148000028819290120b00114150800401c014002d121910808145812098600c0300c040c40e4207d200c03404100034038103201900010841d00c4100c08051007030103195204052300d1007030590022031483c8501c1c0200c034241c006550342181901ca03031040d0313950208596010000c880300c1d004000303200c88550000000104410f00c031401c0204c6031188201c0b86290360080c0d00002c006120187c01788401001c0b0501e42480701a02c2c40d40da05441e00d007006402407080e1408640c1d6030003502d80803650b156084d0802e01410210390b0742c3c1030154440e101d602500c0d0106000200c0011158000601c80c02034401e6641c80d12a207400b628400f422507201e91500385041502000404400d035070707900290241080c65127124081580c80c409000031070f2044031103900c1e034011070070400011079012002100c82c0001511100c071282c1c1c012 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 978785728 1250 978784478 978784489
    0x705010f020316171f05040e0f15090c22050703050103020420030105060315060a0f030f0b030316111e0a090b011202030705040504050c0903010507021c12060801140f060901030f030c02 81
    0x9410860b006840c2034240c2e420040d00081c0c1c42c070130720441c07000c1c1c40c0c010000c448001d0341e050044845810be9401180c80c000281481c0481c400c41d192011240d210420815031134030700395401502c1207000645c581e0014819840c05210b6444144480d0060380c07881941d1138034441140c0814400c0364450240480002c0f038a2000310a54180021b0042c14203541c0d2580485c0a445411200c00980010b880c1191031480d1007414841c0410303a01c401002541401c03082d444044d040d204099048138008546007031022540c50388a800e1070720702c00294603d0094604002842000002684001d410030304100070000d881e60005091101c021008102603602e82ea50302d025240c0d8441d60780010303001441c02080060f054a414054138003580c04600a00541d00d030407404a070b48413001801a2a800e05003186040c03d1802500c01031120b02c2d01071000301d86940d82d442c40a08459810040c230b81ca500e050b130308000c0c1c0280011607031940308038210345a041650454485210b510f0181d2401004e00c01c1c006401d40a40d500d1 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 978786978 1250 978785728 978785791
    0x604021204030210110301180f15080d12060605030408072105071104110d091a0f160503010f0e2a1b01020c0a0f0201050705010f02031617 61
    0xc6040d1100e039410146002940c1d141c461100c3c505007032601652112022104080300e04881448110006e0030a440790003100070308030f01c1d4886410541c0c41400c0c81c9507584101e00b080003007018001411303a1200f1540090030380007848111070140e034545841401510b82200c01e40381c000d5000f914442d1901038a02c2c101c00711001c2d9110b110120010b201036040713120ba2100040c114644210207006019010806010036038400c2c41200c4064a014085042d10110550084003098018020040008006a04078040035426030b0f1000c100e20303050040005980070441c040d0010415807924a02c0c66242000c0d90350300d085a40030381000c003000400071580c03000c0201c24400400d042540030310540005007241780103a82c8003400348080e410490f4011004640180301344d80710400c2c03c3c5d000c0d084d1200030307a64a103206156054102d06008040c0a0000811130034418034010308107103000142d882c2001c4860a1040000045903010881c0c249017248210002d5507105420003503090340b9403406c0303440c0f05182024400 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 978788228 1250 978786978 978786997
    0xf12050c03030c04030314070b04140c0a0905090c09010e0601031104080f0c0a1223071a071704060203120a0b1804020a05060405100f02120c1c1115060402 68
    0x3022003401a08080f000c02003086a21a0701c91410001c0000c0d0030f0003007806010805421829803500007000300b07000991406c0e841da42c0d81c007034a071840000000140003404030341005d40700c941ea81d030401c800f00c0c00400c00809184011a000e892a40c0740606040003007000400c00c5041503207401c0080340c0071400d10140c8002e411554141d45070150130000c0d40707585480b010b40300c91049819a6001510713110381108911010381240e0350300e42d50b1850400f161150840ca441d42034080c880d4000005903681c0c020785a515085a2170011580c031045420120050f00c100e0010f8487d04104003c01c0100c10b07000401c032181c512080466610907555400030000914a4002280e04031400c0c1480304010943ca820780c520461003200da503011180ca9906019a600035400742d2504605c00482d20131550b4041c056140d100c2500340704031079030014417500e4007941c1d8103d4a070388a4181d119000a445052602d110380491038032907c0c00745010084448120f60740c46c0309a012900c206540e80c00b20341d040c0c880781c0480700c0050 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 978789478 1250 978788228 978788233
    0x3031e0504110103060905220807080f0712030b010c0312060b0c0f1204143c0906181501090302101106090a050601060e120106031202010e0a0f12050c 66
    0x152034280b1640610b450181540040d107001c20106050046101d12402480e4115001078080209000c0d80e03550444140280c1d10750700140320320f4001071004802030440c0740d020f41c00316031510518584000d107415880308403814181000b00400315664800c0c4118181905454900c91500d120b440c1c100080c0031507082900340c0c0300c0000300c054004c000000c0d594210406a000c480d40c0700e999452a0010307003c1e0b80115071507604021402401450140c1c100f8144004040c4020580150800e01542020a00c000c511642001d07120000c11031900c500b01c0d070791110007a02d0008603144150040c0c2040d07040208200c8024000a002030720a912401008000c1c40c0d028140c14030703240007070300d02408003614400300444910070a000200c07442c80108817008041d81c481c0092203144d00b8401d00b5142c0d0301c11340c0a229000240c00c4c5000070203400074064a002107003c0d0420006403a14010b000f800d5402c105640201a441103144100251510542c3c009958000300c0307080d42e5444188045820b44a040c0e58140e192 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 978790728 1250 978789478 978789481
    0x31b0b07020c0f0103060b07080c0f0d030f0b01050304150c090b1c1506021c0c290a06050a0e070c020904030e1009032307080706080a0e010e030703031e05 68
    0x22900000c1440b1100c00c11100b40d040d541600d40114161107881c0100300300040d0030700414002900d0540a4166010a0300a5030304160344105d50307500d48603110f40c1c1c46001a495a01c01c82c400d040701d1064200c0e000702807924a142d4a03190f01c5200e148040c1a50b4030002035514044c101101f441091010301400804800316034032640401103058080b000c1d1030864400340340504060b058090040d04c1821140ada4000c2d02d001107140e140302e49000703e076844070340a01c0040e020030b40004154046440f89c1e4401402250340903c0c40d400403061015000b01044215480c0101c180b00555800e8680e0f422214000501c3e08183d0303851004980301040306500030340144160042c00205500075080381c00d180000e460700d2101d600d80f0181159100040e100c00b500e80c07051010501c403247c10364030343c01001c0f01c1d80300c3c201c442656540049034900b40a99222100183c0c6134010700c1078166081c050701c02081814402070102e0388011180e01e03220300ca8404010245641d0701d401b52000706442d1341e080007000b110351080105 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 978791978 1250 978790728 978790741
    0xf03190b0a091b1e12140f04051506011b050102070b04151b0507030f090f06090801050a02071121012c06041e020d0b07050c12090102030304031b0b 65
    0x160208000710154014000c4030003c25510034450141516018840824050309602040d500c00d0000714000001946548045500546560115008602c5500d02c511070b407820b418114186641400e0280a40c00d6450070b10006030b070720805440e0b5280380303500d00400700055032514600a1260550040c000360344003040006000c1b0806085007c1082680b0078002810002540c002080c094204d602c0400d03010702400c0c0c0400c0c462044000d001c8480c2c20108100d40c0c450300c0b0a150041c2e6680080001070b5103240038482403100307018090300820900c5041d41807001c00e54070404200d403034552840c02401c40303841000c1d0b8030141e091019290f44100008011422003244400d06c0e240800002035818400c40c3c00019558200154413845035400100c0044407141c3e6400c411200003c0f10303802d0768084407400313a030000b0400c42c011690040c9055152250b4901003410305034101072489074009c13050310060042001e03598001c42240d5210340d242c5885080c02c1e110b00c3c1c00b23908421791140050302c8180c03180100840d = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 978793228 1250 978791978 978791981
    0x13080708030403030212120c03070302120a02040f3309090c0c0317061f110f150601090f1a040905090c010806100c0f02040209030a0302070315020f03190b0a09 70
    0x80c2d0340a070f400d503501c004036024100c50703d03c9087c514002006005000454040d400c00c041d42c1c100c4000e10b0007500d030081a81440c50702030030658a01e0107950303000a082180761840000c580042410500301280c000c0c980c941d8020b8546280e080700c5906800c0d00e00c140c48140300f00703101d8001c5c01001d40204210642c0f402c00400c240e50202c4100d000c12041081000e41c0e02c0c020503000d114500040004403003680f4074098404100c13205c1d03590018054410034000c6000018080101034007840c000911014081c6058000c4400025000d076041c401d2404041c0959105ca46000090b11080c40c000c01e0341440c0f10340100800e20603580010407091910003444455140441c1c91032140e002680e4844880d20f03414200070075055a01c440d400400c04c0f800980002880c41e00d6940071660000703000504216081c4086401c101c83d8000c1100143c100407010310400400c50750481041880100031420600c41540c100b0b4a07110181550b64000c2244e031613030081054030340010402c000080c124201c41580d0b143c0010 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 978794478 1250 978793228 978793237
    0x2901020c062205090916140d02010e06040f1e0e06090f0c0702040c030b0a060e0a1404020706061d090304050a060c050f071710090b06060d0204080114090c1203030601051308070803 79
    0x11b600e0015440c00031b0540c0d10711740c8542120000601c04a0840d403190b005641100e00022440e4100c00207103c002480120480c0500040c4131601410707486d810004200720141e24290041074588002c182484140e0301e41c1c40009500001caa00d1031700041d20340500e407134014000c0a40080d805424400d0b40b0000d1b65054000b440200e205a80007221242c40d410256022030018801540003664183c04000c80003060704a2810034601610040c40c25145480d114141d03040c3c1c3d006010030090500403880100e010303104050340003006402660a090800000942c2141c0c0e0f0300c80d141c04c004c481041d21060080a0107041040c0307410301c040356180b0756604c1c4160502120281c103103006000e10140b00200d24205c0c005d0328030542c0c0c071141500071640c1d0b55041201f56080301d40d81001d40c0c0c0d030900c0081031020003440b44c80000340d482c694941540c6080d05100c0d190401c00d9281d10300901c640000f121b02d03004000181e0782c0210b807d007005515450b41c2c18440c007181c9040d0f4015449445694000a2590350100042 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 978795728 1250 978794478 978794503
    0x170708100615020f031c200702030706080123011206090b211e120706050103060b040c080f0903160c090c2a02132901020c0622050909 59
    0x300e80d10702e4210680c0c86941441e502001074008100411081d60400310700d00f0072060326000021100312094031902101d01b901113900304190002651020342c40e007002040300030205403600703070f040b5170600c41c1c94504d101035100c2c12241e0030341c09045198103078015485219812101d00041003507655500c03010b40134100c2000c80c280640d5043d2020700c042603a0401c0500034807207060050448100020141c1c04c1c04110f440115140d000f04401c242d00842c03c03000801d02c49010b0344011485506600300034044540d10001c45c0d201d286407500b0403042e03580115400c0e500ca9018501d9680343e541d40c00400d03040d84100340060410700903003040c0300108032803007102c50141c900d0b10f0340400000c00d0a42c829500e126032091104400442403601c4c9400c0c1c20300c1d00d0101503c83c405042c0390150000486040151107040c02e52400100c03014003058400c101c0d50200310721000d000d100800c111060300010401c14030030804c84603040f1621071131401d0000f00f610a00380c02084041e040001034600280e001d40c64403041c0500 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 978796978 1250 978795728 978795749
    0xd09060516110c01091703130e070305281113030b011502072601110309011a060901050a0e030a14060415061d1e2d101707081006 57
    0x1101c040b40c0b40000c0d4110031140603140c90b26601c2c1805441c00118916115042c4a880f0030044c81c3d00300b00c0d02c0c43c61031300100000341115440d0b051009026003034074030040040d10501c0e03204407101d82c1407015041e031515042501c800050a868541c801520038403613000c0700780c0b12103a4440004100211102024100c900705c00a141c0000c6025030200c0c0c5a00f0144500400d45401c4105190703445003c1000c81d0001014100004000c070703528040308040d4004a94400269649510901005424200d509000c1c0070860341c8a10b04142e400c0080d0441c01068092010016208000c09146c0c030200003464005810000000418604009260b6100c2044078201c84104c50b01000715214011401044295100c1c56607013100c820800d030040c1c0007068002c0000005294100c5d06601103511001054080d50280c016210700410003030b12142034008020284c00101400310400c0039419184c01001c058500c020a280300001c03180061500d048000d4002c01018000c031604041320304400da00c81d101711040c1110 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 978798228 1250 978796978 978796997
    0x170a03050a06080a0b09030720120d12020901030e011a1905090f0403021005040c23060a0f0909050f010e0a4203080c0628020d09060516 60
    0x700c006480162180342202d6102e012030b440000d54800450741e01a124400316420940c1c65201c01c14a0204640344801d91014030a41d000d0b0390411141707120441404130001c003009090500003d01c0000801a4a10300b40c1d40402c01c440207078400e400000d842011003000340540f1048909165070745506411082c4545640030b0302c510801c401130401001c50b0802400f01245588010041d030007210f0092049003140140550f00760441424425030b80620b00629903482828100000198416081c4444032400070250703685100d03599649040b0f6080003114500040600615201540d01c504070360401c3c0d04e0342e4200f0081206050045008038104c40d4800000030860301c0c1d6035840000c40e02180ca19040c806003c240900078401d0b690341c2c1005070503d0a41d000811344050250b01400e1403142c03c2100c01d0034000940817002e800c10407005410482c103c1c00000400042e0201000ea200d1942c000009640c0124011608411660002c081c3d103030840341c28082c51506256001c6002c7c1a604d41502040d410171 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 978799478 1250 978798228 978798241
    0x20c03181008041b03120e0306132109360204062f030a0302031e250203090916230d0b030709090c06081f031e170a0305 53
    0x4030721000002498441c00003d45558a4451030801050682c0b0884c107500c00001000824411003034651002070303510100700c40381d404209801c0010280248000259600c0c00002044070003868034076890f100040c032603140030b801400741c6491456900074a081021540000712921b6041046400c44081c610003010001101c1a08402c030300480c0070361000240c3c0303a003031442a4603544daa8810240e00d081114110645a90b001da45180d00c0303050390b40e00094000c401d006080301d110000d00c14042420781240a28a0605130984d01074014509030b10312241000c10051410f8020303c22030390140c9003e05030990500c0c8c100b00c4a580084000001000121081c4021880e06607481c841190440d407000c0642c940f00140307000502420604840e6540741c0101c1c0300000b41441c0b83c0c41540c801c90b10803101c41140c01d02e0014058a048801040051500054110315881e507581d0740d4081c0580c3d510a20300440381003105509500014003e0340201002c0c6035882c80074000e48800b0160400c90301c82d03a024011a41c036003 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 978800728 1250 978799478 978799489
    0x180711060a0915020318030c0106060e0d1205070f0204062d0506030a0e030c100b0a0e07050708070501090b01080f10060503030702090705120c07020f1e01031509020c0318 75
    0x6900140400e4900c24400f8000c01090f001190004100c050f0b0305c10048032440c1441c2564030140110780c0c140c0d5207a0042040399089070030182150000ca40e1054010110307100d06000084000801042000005160b0304002c0c2000c0f41020b0541c024104000c243d0329154a6a078400508051440f1011280c144501d0303040c441c00c0c80000e684000c2c1006056807503d5840070301400607460031450300e000c140b00070b9035284020070024a50028031800441c14010381414001c12007200d0700585044030608041141040e0810200d4100c940d00000d626035500046c20280d005010720a0b0042603401c00200001e82c0ca080084d14440098560060392110035a0700c220004a0702e50f4443c554054000344003000241c60035040540c1d0040c10303420301514000b6a49500c150781001103d441a01000c04241b060a505005080000402c01a03805500001ba2040d511014906404020b4101a156540d443d0700c2e0140c0110b83c0010300360743d2410740d11041104a9103440c0d07005180031443d5913071503452202036481e06 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 978801978 1250 978800728 978800741
    0x9080d020d115104021504060219020604050402030901050702061521011104060504060f030b0915010504090218150301050a031e0f0510050a02090f0906180711060a 72
    0xf4850b00d56481c2403c8504039219201c10081c410400f21804400315007420510604520314850340105041e0303203050310420900a00b10070320411010010b110921820340c000414040700d082007000800540d00c280300160582c496a0000d5030414004070074020721b01e00541100b0702510480c1c01352040fa55070351550140407180074089640c010700f42141c60f04030b00c00d04400c2c0000010001c002240e01048107400742082d07840ba50000c0b002510001c2d040192551101258900d00c0c000c1c0f800784800e10012000801c903c4024103205020071040641d0340312607000703000316002407040300825900c038140d040081c21207100340003109010315407002e001e0440c4040c00301103c0c141d40700205403040c00d908507100d0301090307618004000070142a40f04402c011501410195500910640061554054101165096600203404400454010f22012580d80d450880031080750324181c80412142c0d40302e1000540010541070341245c41318103032081c0410a94000340500c804280041102d02a0326030b07200e0941115039 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 978803228 1250 978801978 978802003
    0x2091203090303040b0903010b04090f06050a0c050403062d0917030402060313030219060504060b0909100b010201060e1e01060806030a0212030c011407030b0a030c05060a09080d020d11 81
    0x804c100a2004048644c00b134145858041e00001c0c0c1f5041c028041021030304c102c0c40c1581e01c20303a8905035200700b10302401900c1d88032018400901110a2004014040b80514000200b031140c403501580d0701143c82022501c0418023140040e04038001c005601c80c01030002410948401d40d030cd000c5508002c046030200c03801282d024004900d184e680324180760f645100907108404500900341c210b12003660064181e41c2d080d0140c032001031030b0f01705031400c0f604880340c40020303500132000c5104000303080c4804689035100800401000c2004507408004030f0042000d42c1110000c101d506080c0040300c401d50400518000426017080e109907240d01c0d0036030780c0e8001102c6165040e4410340003003005080404141c0300b00c0c0340c0181201e00b80b40d201c1007290b0039510301103c40fa500c00300c0d40c400c0020450f40341c010403010500564868800e6421902d2701c00c0b814090b8081d0a0041e6800030f803000b4601c0c440e0000c080280703d5641940d030302c202c1c650f4000b91125010300c84400026101400b804410b4000320b0340748400706 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 978804478 1250 978803228 978803233
    0x1090b03040503070807170711090105090f0f27010f0c08010e0c070f24060b04030803040b1803120105181312030f020d05011a0327070302060d020912030903 69
    0x442540d101d2421b54030880d01214501e0b000404052040c1a400151081502c182803c401d03881c0c51200b80070f1a20f034140e02c185c2c030034001c1500f8801d980303100100c030381c0d08421511240080ea40c1c0c0d41c82d483e060203100e1100b1700300e192100480e0010368101940020350700880c580051116010721030084480140138010980202e0510000c2001d40c18008020210306100780c480d041e1007412034603280c0e0551502e1040c60700250b0013400042e0385101c1e030700c9201c002e00030000b2040e003400c2c2175445000c3c0c01e0000410080441b907070b0304040f0700e17400e088d9009201e103284042c0c11a039462940d4140c0444610003807007882d000b0700c0100603030a03134111480d000c54030076049000204141042e45c0c6070303030791001881044a01030540d9540c804180e00d945000600c2a180f15a0b00407a00f9407400b4004e504c115820a54000c0300141441848506140703686004072181241c0300500001c400602a58140301c402c1e1f000030340c00301000880032040001038010300380c0c0590840b1000f4021040c02c080300c1c5ca80c803078940010f5068 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 978805728 1250 978804478 978804487
    0x4030213021e0703211e020301060e060714120703020d080c070f110613030b01080f06062202120f06100e0112022502100c02150a020f060c0901090b03040503 69
    0x2103030941c0900f00303840c02460919108085d80814940a003882c00031040540d80300c9081c4840e1b010b0075030964140c1d00c203c8604500d10743c544140105102a0060906d00c130f0800080c240052140091000f800000d0300c0041d10380800c80d6002419140d07122300403c40150140d1181c40800038005c0c0c80312841489401c5c0700d18034003c201da03244283c8444140040f2811441d40c001c41c2005c1e1901c07400303043c030340254a000040645c25401c14514000c0b0507400545550720400e03440707400d888045842600301c0c2c015a059410f4031002000c07070024090200c0c1080c00e40e4404104520f4507103007040158002c00f40340300c010800b40c0380d050a000c528100b1580040110b840107500040701d5101d80940e0011480c080c80c014148184040c0e51000520311b0707070060f0b1003150300d4000d00c819031516244032060002e090400c5818030702541d020404041c1004080403902d0004a10300213214020f10a203000c00710480140c580c1441d181ca007680700c1d07811101c841800104c1191002c20381c500b0704c02c112402181c00c80c000750b003003 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 978806978 1250 978805728 978805777
    0x8040b0a09211b060c14031504020f040e04060b010f0206060904150b030a06050604061d040f030c050a1202060c1309050a0b0303070b070305160c0b09210403021302 72
    0x4070329003a400101040b07039003c0910300c0e4035400f880180041d44503a40200390f00c90b0080c001480c000b01580700f070a80110030424005182d0841ca0311015255003910003584074040720388611542d00032580044c81e100c00c44004c000c04c104265020741840d12090b00c03460011500c03080c040340d841504580413900440040d000c9004902203202c40c4c48591585203020412a180c900428207104819000300d68054032482032262919050140c1d101030320744291400c440d10240709240e405039138060000f610a1581d071410b80140f510031605200010381000840340041d0281c548451444034440300c41005018a00100d1300320031000044482001454051104260600340c0d1a4010040a0104041c9a560348444441618180060701c1e407540100401c4205140002020b001c1c1ca50007410183c211010f4244007c00035040844400d400e80c01c5030300c107003895440c08c42c0301e4900b9009411010044820700c040c0d60746201180d00502c103483c030943d10241301c0340d802d62810080c1d00402c0d03c01c0c500b00e550844940c1c5c4 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 978808228 1250 978806978 978807023
    0x405040c0507030f030e0c0a0602062e0e070917030d060911071e0b0708070e0a0509070309262104030819020f120412020f0705060903030c06010608040b0a09 69
    0x1b0969400b82581c3d04203034031a0010b41c41e1710701507000202680080c010480720b68001c207221402184400c000c80141c403161000c080121305980252a4281a2400410301c034510501460002c1c00d0b603600d080500102004005560740c0000c3c0c1c038401864108000401c60244a000d03d0103111000c0389101e08054040d500d901064040e214101c2c00303611440c00319408a8500700c200350043c44251501c0307e1906000c600180518020310004d4000d00c20710104000c1602c4014031940d0024051800103803220300c038a410502400e030840181c92166010416403a00b6120344001d150210310800700c55000350b0002100781402c036040750b02801041c1c8010024000218410101070b1181501c50700600d4140805905145508068190803080e02c01e0800c0000b040580404c20910103000d00091452044e0082001d580d0009401802d0003031001041c0207000391000c1043c5c0c2c2d208a002d10503103501d907840745002445144104c80503608014401d0115021a50500c00c2d402c0181e0011882440880c0001b40c0d480e = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 978809478 1250 978808228 978808241
    0xc060e070e0105061806030f0906010b030f0403052503030c02010c14040905060d0b0103051c020a050723090a020a030b0a060503151206090a02120c0a1403070b0307050405040c0507030f03 82
    0x2c1918070f06801d0417440d610b80c0700441c40b500d04d00018078031a0620845952811030142c0048060364410824001a00c0403080c41c50741c40b80d4035150259503a110f0901303541600c61080d11801c040c041c01c0090b6820160140c128220711201c0f54020091103038680d0084800241c9082e0480c40c030b6404020901c004011904415409440600082e101006a54424807003202c01d9000f0784003500024801599003001d1803c29500c21090310042c08010400e8407440d0712032046100300c8003500250b05800c0c59030071106c1404c68210100810901301741c40c0035111440690b2000c030740b910021b0316250104d0800d1514103d0758080d62446e69905007140d4807503082500110340300350f03640d40c407036000c28400f40307500401c00400b8403d01900020300b1040c0918030611501d002101805406d54010020280294450181100032114a00c2c0000c0e01c411482c0082410070703541d230700880d0313102030700108000313170a5006401001111001e450800c080c1ca01e08108440d0360180220040000d4200c50920500c180311b40c0000 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 978810728 1250 978809478 978809497
    0x21020c0d060b190b031512030a18150e030105060a08030412020d06020a0f0e010f0c0f0f140706020f01150506090316060c06050a0501320603070c060e070e010506 71
    0x200d0380c4889038409074024107241c0c40481c0e1340e20000100440d20748569004400c10030255103000d03a029220300c0041d20f038018110381e4400c01c0484000c00e29803200c9000307150020710020142b103424004010700100b8021012031128081c1d030030080490b809003003002c0044111800d01026508103410101500100c09441800ba07a00c0000554241c000c01c1c100d1009001c2c00000762180202940e154001070b1040e800c038041c1c2c034103110030303100210303001034102401400040d40104034502140046c50210b040a90324200a0010304080307001c0c4400301c034000b4124003560104d400300c0e90f011040c190028203a801c40c40e00d80a25248a0320300b0003040c10182d000e82a080001400d80b001c0c044505d000c1e00c0d0a103183c0c2e1000c40011203081d0b880007440501c0c030500360070400940c000d10280d03040411130142c042d40325411203200c046115621011061040710340c4c0341e070320000b055035070b0b43d08004100600b00b1018040694210349004200c03070044034000b40038421141c5880c4110016880d01d0100002c6070405820b0 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 978811978 1250 978810728 978810739
    0x10f05130812070b0601030501210201020f07090c0207080105010605120415050702010209042003060d2306012d0603020a020a0206041d07021b060315090421020c0d060b 74
    0x400c0365107060050400c0000700b04000c2e074a410382070601815400028001c1410701d031030702c80140409000c011456050002c488000c0f0001149840102c1c0b429020744995040c0c2d0082c8000400c00ca4255004000291000e900701c60599448075119800c0b15000e00c511000701d50100204084e00d4001d0046640c01170152040308000340348500b02d40203484084940b41d00503540015024a10700d46032141e0104400f00d5121030101d0580420781d40983e00c0013402252007440f0314030701242000084007091303098403500c0480c15080309050b030900b5551f810030300542c0c64841c0c062203800c2d10491f01c920101c540a403036882204105240000c00c2c0c00a602c404171031000c5000d0780c1080780140c2c1b01c03800140020001c00c03000c0007440ea50b1a080040f02c4001401003011904240710340c1940000040a840c01079001b162072555a460381c1d0750302c072001c0f440a02c4030b94115040308100024059149224440c00c0e1001a032203d40080c1c00100b00c0e214144c40c2d440da03901112000e003000101e00254407409213140042d28 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 978813228 1250 978811978 978812017
    0x1030204051f0e36010513050604020d080c03070804180b103203150103050708040303050c0d0f361410020301030f0c0f03020a050f012003040f0f05010f05 68
    0x41d070040401c08900300ba071000c92144e25101585409103d01903104511420100702c803002d655405803900c0740a40007922507032210031500c0c1440300840858400000850840307a0ba8030151030400c50350b401c0351140600440004d10b40c92644a0140104182004010300c1a03141d43c4c0c50080a82d1a52400301c0c800c0560f0070f2007440307900c800f20205520920729010900c40b0f9128548881ea44040041c607400060401d42403d06203c59039401903080e940055060501190a0362454021401e600600d1650000142441c0710000c0d480d003182d1180e140e9165070000589502070881d04002c4880d11784018120001820400f10045140816207440300010f120503242d003081fa081100050781c001703030803d0301c200102d18011410041712050358001000900003082d00f070380c51500081e285100a1090900551800081c062907a01c1480000d43d03c02d0309140305042e03806a03803c0035640750018001c080c1e901a0003000403410703d204a0314101140c60580d44c04103101001001203c02d41c000c209158203800001e503 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 978814478 1250 978813228 978813271
    0x150306040207050f160e06060c07060c05030f0307050a11060709091109030a110109060206010e04021c0f030513050103020f0d1d101e1b030b030304091401030204051f0e 74
    0x50717010b074400d910945a0641e820714803050002e0078090003061180034200802c1903941000300d02d06045070101d0500b15854080c6043c807034103620441d000a0460b00000042029030780c0c10102600b0507135902c0e581c0d4004520603946c0580d44207000e60f81100414051b50080100300b5064002d0b00f0219002030515090144850100e450880b05803400c07901900c040000000c2035920600703150080400c0e100030405949010803684038070002400180c090202e0400c4208500d10044101d00290740c000b5610882d4061428020803e81000c803035440b11038101c10b00001c0a40c03190099038410550030070110724004c004100d100090005504001241071030100b52961107100f4850807400030344800021800060b003d0744810f0004a10082c07101d4149025074641d80406e14160490001d0101e050016501c8400b034006480c42c005c0e640b02d110607500f001d031000c8090b00308a0f6254101c078426641407100380c585211010190250001e05440d00c4402e51081240401040d513507500400b9010320946000407d2 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 978815728 1250 978814478 978814483
    0x16021909060e0403170124090b0a08060406060306030c05060d060509010308031006090627080a060f0b01170a021309240f0503030409050c160302100605150306040207050f 75
    0x290b000034100c50220b002c11003070542082c0e403080045444800c02070590304118810110703412000c032509030108040082000c590041c05000058440f0b10112038031801c03c1d0780e009100c10f100719a000d004030f0404400140c11802801250240c5e5404501120b445d810031050001b40c1e0002c1c0c01d224805519610700003003d07200d40d86888d001c0c6020300340e459582e145c1101ca2000600c15607006004001402e102040060380c480500804224410460000c43e021104800b52070051500005800e00070100308c2c0c0104038840e440300c1a010b00c20300017400301c100104010354292040e240300346451a035802c002268140795600a0840c0480c115891801d1500c0d0550b1408480d03403806a1035503030381700d250601c01c0058031501400080004581c000907690820004c00d071207002d544203402a05403203201103150520010152801702c2005501804a000700c2d00f002982d0307043d0403000d40c00d61807520001080a0a12a03868100321900406003861900c404040c00001c1d482420305440502038041d241810100c107 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 978816978 1250 978815728 978815741
    0xd05120606070807080403200f09060102070e01080321060a12031101020f0c060f0105220b03120a0807080702070e04110d05010204090e03160f1a012402010216021909 73
    0x20303020440e113031b50070b61a1048905c000f02034002c3c0700c007500c129110403c0e034400100141a91064801c40415101c0c00010707440c25205401004043c00e2040000c1048000080640000003002070800d5000d280340200ca041c01900743c030305a4002d01030358001c2c02165a203201e110401c2c1e20030701e810741c43e2100c1c0098a60072600200c202c5001c0c501e0014180b008400104490380e040140450360b680f00e54542000116490104008850140c0f1810a003940030302c0c441d40030303a0110034050107079000700710345200889580c0d105140000204031002e000c80c04691182203040e1040c5003e07001441040e00b4100b500c0c906100081c421943c1e11f1480318482c045031560031808074114820000541c642d8103002c00001544c0081510800070341c000d214901c440c8500b620740491058010190121020060400703000904a69806900030401070000051031106100d8400c1411444181210719104955049080c2d00c01d040c0501941034071181d510380946410520403e41c0f9141110090304203540d56151400c0c2d500 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 978818228 1250 978816978 978816983
    0xc0c080601081c1d041d0708240702070519210606060c2a080a05030901031d06070311041a090a05150f0306010302070c0905090f0d05120606070807 65
    0x440c1c1c3c0c0301002c00340d21071203c0a000309141401501040100009044542c0705000e8502c01c9440d4081e200c080700c6403501072080201c9200036078254580380e0341041d41c1e60f41100401c2c520314104140c00901c19982c0300305140140400d9000d00301d072910742010000c1c0025003418400c0907608011002504c1605140c49401c0c103030710013040307203450708103400c1420885551f80d1120091040070035501d80007590305440d0b11809101d02c0204810344a40071094124290790350010400c030b1040c192140c080c0301001010340141e00d000d80c1e080c0a001d4090716284100b14920004801c00da001002095029020340c200448485020f005581815a40c0c07080d1445908904644042040300040c10b128034140300703165001401e820f030782294039504403543c60135041c498000890b2114001001140440e880b98041321030050300803d40140c3c00c0d4231003024000603c8151900140e502c1403400e8681103182c00310f2441c407911500c0e182c903403e02641e061008841c480050889600400810103240065032050283c0ba00390b0 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 978819478 1250 978818228 978818233
    0x61403060f181e0a0210030c270b040e011415070605070e03030d0e0114060d0209090c06030a0c02191e03090f06110d170a09020d05010c0201051f050a05010c0c08060108 74
    0x14881c0c0141b1191071100303020502090b040c42981159035401004070840701030049180b881c070418015820141540c07940000004070000a00002c0009540c540c0307034180c500b130340c041c04071340c1a20500700114180c4801c80c007150837400f4013a91011500660106502003100e00300507066210150000f821584620030420003150703155a0603000708800d04c64002e55520700c0003a0344a03400c180c40000c60f29801811300901c00e440070f03400a03803034840910072100e1500c0040e000310b84a0404000c40c8020388842c9213810018401c100b0a0f064600c142c010500440e5044a4000055800c503805260841d808250580a10800020005a030400ca44d82040100b15940e111003a0b2503101440b5414000700c011100708202009441c100032440740c01c290342e04004955800900c101191010541c4503400d4807001e8855460207181c0780c44d054041d005907200c0d002004c604461007541200280309000540601e68229030b000c4410301241d40100345812901e8010320300071002d959a0324400b850074030240c01405094 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 978820728 1250 978819478 978819493
    0x2030a2307092106020708130303030605010e0d20060c0a140705030f2d101e180639020601061d1005090310061403060f181e 55
    0x41d0b500007a03681c003404820701c81030003e0030403a00e84240c1e12003c0c03c001e410a81d002580034108000e580031205c0c3c425026001000c6607030380f81400780041126100b1180410345001c241119840c1405004030116030180e00091002c3e0043c1c0c3c62071481020440d043d8111004120a00307285808104e0a9041c0340b054003c01d4541c4100600d0a003004c4a13640032501030303840161340e40301c040c201080d03060000c0100300200c40e441d08142685510001e2108100c00e4074001c01070500340c01d6805800c070940c02c0303190328884401180108840c2c4100e941102c0d0050003002c2030074640c1c0c002a01a0400c031480071101d505180c10840c1d2180e40510424150111a10904107081e58046039406119a03801017602e410f1220103030000c442103011500ca8244401c1c400c14074004852402c9002d40c0c1907680e00703135000e021140d0018440b9070103001001980541c0d2041035900300420070310b2400091031072280d0092061688162582d4510302001100041c01c42c45070302a550399402090065460148a4001c1e2070080c01030 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 978821978 1250 978820728 978820741
    0x9030504180b0f04020c1905150c0c07060e1011030708030c0409051509130c18150801020c071203030603020306070305010302130629040801020d060317130902030a23 73
    0x1011140c244c090b6005104201e4044004581a03500040c0c22010341251845880d0542c2401c40a00e070307103500800300400b40441d2801a8014103402310b00c00c0111a126a01c420041d88c2d114541c01c1942c0c5d120368030b00300e00c003261485002d100340e04c440d030401240d08080e40eaa07640e4082d500100d4416104a40100381004a00b946010ba00c0d005145581c100e00741150200118006c00002014400c81e20004034400080041101c441401003007035404070254a4400c50314000500240711110b41e902c0c0030076070080340f0b150044c401c5855a008542c020038003c1d2905040e041c2d5611014416014140d40340300010244e1014084a8842d845e6540c00003415811481027110051302c03417005401492078501d007032010360f19000d5100c04021034046002e24208010110703061911864100320b0080d400400c004800705043d03048202a28072440c210200c0b034460305070781d11490060001e036070303c0d07030f441070804120034055940215003120b000c150200d12591514000ca605a40d41d0401c007020702107240402c480d = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 978823228 1250 978821978 978821989
    0xc050c120c130b06092b120324060f110a0614010e2815290a09090b04090b0f22170c0703170d0c0f050d09030504180b 52
    0xb10560040201c00c1c0004003081c03a60166585050240e12050702c190740d2070221030020354070010390740c0556240707444502e0411441c0103030301409000301e81030502610302080c000030322815110071080d010712405c3c9460800c90340240c1030551501841014090034000d64014880d904007a030017840302007108c040c4d030041211095070513070107a184103800d5002c0c4002c0a8031900060152103040c145200c0c00f580c0748580700021f0000d020420803a14170000000746958a42c190181a151018001c114402d1910800c041901c580c4109034001401c1030300910100700c00c1c0e0301c021303d9804090700000d40c0b8041030352b8100d980300b01640c024406207020307801c00004000300a0703684030b44104d01c5c40314140341805998070318240e41002010b1074041404102011103040030004034000b10740000f0900384a16158402e05100d5015191500c141030404000c0c1d10b4203405101c0643e41d40302d00380c1e00c1c0c038900304000c44042c00600c1580070850802104020000b0413112148403032a02d59480e1000040f841111800c201 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 978824478 1250 978823228 978823249
    0xf0e0d0c050c090115080405190501060806010b210702151f08010b0f011d03070e07030c090e0705031305060c13080a020117040c1a0c0f070b09010c050c120c 69
    0x501c00c81c3c12400600250090019203801c41d1007905005009441d01d11b4024149042c1880001ea1811031903030110500c08150480001c0301c1c0c0c0e0b80142e540380d90302d581400e06184940c111801ea20180b00c50074005140941040591040183c415100044054400103101c0c400613a02d0242d15034a4014003000500c40240030401001c0105c020802e848944c00891040701150031400d040c00394219521070809411241800303440030003400c1d0341c0c00c43d8954038070843e210003d50b40b01d40043c0c900004094400e00a05c0e148084e254443c038400c40542ea207900c1240c4543c001403205100c2a020360314080055000c0203114091401c0d80ba03a6500c030340044000c005100b10a40c000c0080da8444400d04d40542d0b003008e0300d070b0468448040716800c03503038035424451041d00e015400078120150801d0600780701040e810140925445800036121910341c0722129030b0b81c0f4082030080c0004080d0403c114129903004080302c0a40314411400d9482e01000200015084103000040f8a07050b0006446681030345005a145d2 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 978825728 1250 978824478 978824503
    0x30403080708090c01120c054305100c05092e17070c1707060507031404020f3f06071106070c060609050711010501050a0b0d0f0e0d0c05 60
    0x280840010b4800003000b6240b2001d240368141d03540d64089070210322600c100e60500c4440014455480c85446d43c448042424484014009e90710300001c5411000344040101280d410000a2400d448080c4100004040140032907040c498108845d074400d440c0d41004407441380440610442060302504480305000b07102c07a2840400c00b40e040003001102042c16643c0c0c004c1c0c801d20304104020300311300d0002413449812200001c80300c0041000f90800ca102c1d00850320a05655805101010400c02c1d4170042c040c0c00d4130003d5011895480c20030280c100040c8049a040c40a01d01e414805c1c81400c4a00c0c00d00e80304041e001918032144051300000d5410000c09130000c2c01807400102ca0750400d990503440300c801404c80c50030092a01c49500a00c43c0b280c1080d4040c02c42640204900d05100c031002d00500221103151109508110001500d03181c6048001c040310b04d00c2d46c140d07142c8101280014024559004050002c41c5d0b282403010a0500410074100f584810361150b0310742154500f801440c2c6084034458 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 978826978 1250 978825728 978825733
    0xf12030b041112060a0806010312020d09150c021f0503011a090a0311011e02010b180118020304020a12200405010308040306050405010b03010c020d093003021203040308070809 77
    0x70102d050104011100040d00040b00c0d101e49450f40000650b0801c00c583c022201403041c080040180f011070b03000ca0845840725001c0750800e280902040d00c3d84000c9104107903200c20490300100b03030180a801d09010561005081ea4840650340e5480451002805814030004030040014005190014007104407501510030742420140c03480005440340d50230b404010286030320f180340c1d104542d00030b0b2441002c184489028070500910010028020310b482d822041c401e05024995243c0c020030380c94201d0690f03032403200345852100c0f412900710196001500890308429003034130020789003038040c2030030341400d10540b500340340c1000c002c000a841c0708107a00c003e4403591602004000050000007242c046903449a400f152035503039810504d00500c100e490303898040d4240031507036480590100307160181118070380f034109105846040b40b041002d10480d528007a081203030500d41c2c6400a00d441c60b01c0081c4240304452094210360141c40140c1c10036241180412401c40503c2030840d04085101e9000407250300 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 978828228 1250 978826978 978826991
    0x5121003050318031510060c030e0303040909020118060206010b0c0c0907021e0102181002150f060406060206160c02060f0a05070b0903180609010215010b040807050d030f03180f12030b04 82
    0x2c030040280751b02c0c41500240300c02c94220504150148071040c4955030001d051300c2d21155030300032080207031a03203413822800515903441d10390b0040c040c40008029250254010500d43c0e0070034209140580c401480351141e03110b08403c000196489070b040d640b0684d05039000c2c0c104281c0c484510481000724451080f004d074018030003010300d40c00401c10303031420302001c13105520801c2c43c1c5d040c260708280d403405000080e903010104204000d0700d9560707070328000c2c8001d40302004442e903181804c0343c49800540c1c5c40000d8082d40c80080460610496040078880e0000348000d02e042c00c0c1e2007281040341c0c080e84c07003100811408540c80d41882040303061142d000d203020014520300000c0610342d2940c0700c0020103052150202107000e035110f0344200010300b5421ba40031440103465031a00120161030300584a11402ca215140c00030819080051040310b40340d42c180c542c0c500021000805030003515080f0005030030070810000741004140d4482c1062032241c01249800c0d848080c4c1c46004085c0c0300d0904c1e10500803400d154 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 978829478 1250 978828228 978828241
    0x140f040608010e2107030f110616110325140316020a090603031b06060f030b0906010f1a0f0d110901030b060a0c080f09030609030c060610051210030503180315 70
    0x3c080fa80c0c286c2c1c0c1460045100d540d031450a50380054400700128244c4100400c1040f403440003020f40c2100f601d182c50304085101103004056a9200b120026003070308850b103e00032001050303403504d031030043c0c8105444120202600c2d00c0c2480e681200e03090359540c5c101c101c0410300390b00b41304a5800c0603150106c2c0074440581141c8005d0206103255515103040c1c207060305064103105a55002001606e1411806500946d49092000b0303d500c040d54180650b0040000005003200c040c80058216080038a0031040c041040c3c16940b41da070004411030f00354032000c10074007100c81e42d58414411440500080140c4402d1440001021104040020b5008900030488100380b40d400602e0144600ea000c4070942c0e4440065070301d20b120307000c2c2c6103100e03805200d0b80080c041c000c1d0b4044040c1c041025000d040702d5a50352804100501e00700b5220703407100400c000b0072100802e0031150303040d140d1140a429201541e50381e2503486519540c8481d840c0c50302002e0076400d04600303140900c00440400c48104010f40345080a9 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 978830728 1250 978829478 978829543
    0x1b0f0d1b08091c060c031d0102250f06110304290105040f060906030f0b070201090305030f0703090c030516080f07050d0f0807060b090106050310140f040608010e 71
    0x141c2c0ca01c5007441205410148010500b51a845584036500b03002d4809000806000750055550301a1007020360024420302440520a603142071001482c000c8010401c2841d03261001280034050344c0810b40c44ea81c00703010403194041c1e03010b03800d070280e0496074900d4103040c0801d0100601c0c007072000401c14403504200c83c040d030001c03843c1502d504840010b40303007003002c481c83c0040140f90703c0b540604d81001000020300030030307089151520780a10310f0301c9000c1d580d09108a0072640341d160300174041030040c000301300c2800307901100e564000f0130340c24009070b0740c0e03070f0340e141d0b290380c2c4515a00445090303200d5001940d00001c207034001700050014800506401400e40c503001d8071008540100d90084c50040d80300414401d120425008040d0000103007507407140541420310107898004180da00540403800006030580c419000c417842400025003814240c0c0c1407562101c40300181082041c0e020340d42c400b6445444c0c0e21480742c14024141071000085501e1400300f664205100300364014070f4074241c880411442e0201 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 978831978 1250 978830728 978830737
    0x117030304020a170336060c03040603180b190c090830070f0209070c0b1513020f0304050106060c0f0b060312070302251203051b0f0d1b08 61
    0x39400050103031072001c14143c0c40c40c064041d49104500030440308600d0350710402c03244850641402c5060481c6c12041c400d000d224847c850b8840d40c00c1d44100020413902d8802e07449031400c150000e4000000120540b5505011002030ba0710001e4520020012201001030388a581e45000c1c8030308003800802d281000298841101c0115003441c02c0201242c1040e146450f052461040ca000c41c0103900c48003e0f0a0190010000d402d08074080d03c1541c02048010f4003850194403159030083c014601c0340d44140c84400b04040e8400d140342c1104042c156903114005d03d00290110680a41c1314070b07141e1410341000c03401c0d103800382c0c444000c1c0000d0521440108a812008010b0b082e085004141c09850751008240362448a6a2440e6403e202007400d50070540c1c0480c600584c10410040c00f544074009070b1504104c14214490301c0e0750301c0b000d0201c0f880000d016001818880c80c0001216000740703002103495081c10340b040205045a0404040d01d9440c6412000450740080202600c0d400041a40d0b0b42d0400c6d80316 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 978833228 1250 978831978 978831989
    0xa0204020f0c060f0f01140607120c05030d0e0c0604060e2b0308070f0306050a090903200304030312090203030304060b0d0f050d0306090e0d260108060117030304020a 73
    0x80000d52180308070310a0342290b000d4000328084642900d030180c078003400c0150588207004288203070070000031990344120080400c84001090355140c4175242ea41d40000440c00c1d01c0a10500014912070310100e101407024007005000da40d400320302c1c0c0e007450403c9410000c4480c00644500320501003403101e40d0740310072441c10042003580c0301c494904071400d14210840074000e5860f0070f45202d001000130554070010702d5008003410f0b1555101c0758410700c0c0560a41d001801055003204210b0002c1007001110740104004502030309001c606440c01c2d100c025018031311010252140c1d400001c0400030140e010f2518070484d260168108124466540080e40342d12000e0405401a41c9600c490b08240d940c8034248201c10764008440b4035220700a01c3c145840e9aa0300c0c0808011900d468000246038a9502030002c10640c0c10b8081d1601a004080a548403030030002c1d44140c0c01c031043d91200303842000390b1103e8040c0601800400e0716602d000f080c030200899580d11408113810500c03d10005888a501041c02d507138 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 978834478 1250 978833228 978833231
    0x1409010f03240203070c020a09090b0a0507030f0207202418041b0806030312010e13020d08090405062205061903060905070801200a14030f060915030a0204 68
    0x18041c0d549082c40040031108aa0300910001c180115550805e98150001e842900e01c00196659034411100700c41202c0c070b028100100c01c00019110001550207294000c006050003d000c032038988241c0100d8100c00301c203c40d40031041c6682c1a141004154400c3c04400c1200c1070110030542054400c4500030544a4010110303010914045260708a00703580c401c0c1502030810401d0760704020190703554451800c40e1001140c400d40201d01d540c01c02004032941494414180c04169180c45c039070000c1d46000a202c0380c2841d40c0e00081e81c00507607402140501441c040c0302203681718041c0408100403500c0107030006209000d10008952901c2c444c61109041c0d55803000c00140c1035aa000101304017984001010841c0351440f0320100800010340e00c100103040c0541c0440d41c48079100d200320360880d609130154443c0b160b03600740110468205500105034461141c81c1c416074408560800b034a0603041a01c45200030354803d402c000c0c16090100b5610340c043c4015a21120030030704000801e0704d8107003e0a019004a = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 978835728 1250 978834478 978834503
    0x11d2502030d020a03050a050108010e03091212120a06060207030c030b04232a010207031b03021806010e010f080a1a09040605071805100f02160e011409010f03 70
    0x5034024400d50354055800c1d1000d640e204d03800c1c040200180011256682c03414505000032502200500c1500e00380e0408800640c6003c500004101030070303014418440141c4501c0b0101501050000068215141c0201d495846420521448401c0d1b50258008008660cc000c2e03040000c10a00c80c105c20031640c00040f64022034941d400c00b00c4080035200b20b607000100c628030b06d12074001c5001810322181d000c003640da001112111005c00020000c0a582c25005900c14013007880070034010b1030fa200407502145a0a4002992a804280312052007520901c51280d900d08010465800c040c0b040610b0b84240f815410880e0207a1000c1c0841c40050503885a840c0da8030140c00b8640403280d44100c184034020118a01480d00d45845800350004403541e000040260343ca11041038051020502941c4004060680711400c00500b101c4141c00c84040008510400390010045c59504d40c5a2001d4141c204180c0460360402c4440b440d400300382c0134541e000713158081c010040d1203190604903080e00e0748846040c070300 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 978836978 1250 978835728 978835801
    0x90615080a080a050d0f1d010f091527051c0509011403060d0204061418090304090b1c060e0d0c0816060902150403031407050c1002070f0b03011d 64
    0x140b0140050038450f03858164147c0b080c0c0410711b408030140b800b05000384103003030510b40346005031440007100911800441c5403400d24500c050b0040c020042c0060340c03d4405002169408440e021881c4003692141c00c060701511140304c0d49207000f81a05003505210b0b11b40440900001d0915085180c07034240282e001c0082800366907038860207451140c00401c1403003c140c64000c81d1a41c2c84105005502c1288003601100200030f07403039011840381c1c19400c041e41c00d10b4a45001c240c081c1c001c2071310140d8445016480504d02d401800460517030b09001d5000058100000d415051030301421051500600201800000028503c1011154502c00c40c0d030350241d400645141640c041d01d0b03200d0009500c0002000d050fa5216800006030040300e01039903c4441440c00c80343c44c0c2c1c142c1e200c0d08070040c000b5041a0340020f13a038204841101c080f2140c920446101c20380d19850300403201c5880c0c00c921503c0d10001300401c00c40000c568640fa500c842140c02d49243e081003481641c010042c100d40316242500c0420300c002c2c = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 978838228 1250 978836978 978836981
    0x7020d0c02031c0504150c0215070f150b0f030115030615080111030f06010f08040b040c050a0b090312030708010501121b20121e0c01090615080a080a050d 68
    0xa9800b2020104003400c00844003406079013142c0280f12494800c0c40241b4410f911641c440e0001c1600a450488030b0000303c1d080070607a5114220980f00301506202d64400a4040142c009424a02000002c4d25440c90b00400c6007a400c0f03500750610aa042c25000200c0b92080c055000c122070703200d14006400c1c41c0780000e001d1201c0c5603602001c2d032035107404440a42d20309040000c600c100817524440b030316590b4102c015600b200720000e5007000a1a6400020001290071070015001b034041c03107620000555401c001390300e201080e0007828207520085003c00301030804100100d00100000801810b5181402001b481f07460148038041c1003040721114020012100e9200c203411544c50071000c010310f03490f400090150000c2e1071030146280e8181401d800c0c62000071615000120000d903507039240a030110b418440003000c420740b419648804100160980109110f0b0781d40300d0303118507400700e1088516202040c524a0725842104a0b400c441c40000c0051141000c80e0580340240c2403590720342d000285402c0 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 978839478 1250 978838228 978838243
    0x30c010e01140c1e0604140d0503070f0c02280e01030206180d060203070201060611030c1203070e0901080d08060303030c0412030329031c090b0c0c090f160807020d0c0203 75
    0x450400c032400311964000170030001d1040b03010324400c840b410256004540d84880903d415800240140086600180700300300c14420612907203030050540046070009006285114101104114114030411401ca009901c0000500465886040c2503145801080042c4074200c01380d9412a000c41034146c1d07030342c4c802c091a8000d5403c54021500c910b804031001c0e000701290300450000c82d480c0025215540c100000f1a5140b02e505006026101c40c158501c2c5d0380b580014000c5002c0c01206003003071005846180300c541c003c01d4154000c202a0a120b80054160f48024145601907001041041620420700b0304490450755a5240041c4401e1542030440013009141e041c1c02c8a145107c20081d030301f2a10300178410300c1904c100d050703481040004412403041c04803100355002144001d002080000740e00c2d006031200c0a01d043c01e40303000000140c0041c0c4120b400b01d030b42c0034078081000c060020b00b00900c80c3d40803441c0183e00780035404c3c0c02c101c08041d41e83d209100d4942d0802079500200b8003151414017115 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 978840728 1250 978839478 978839503
    0xd0506030316141506010e040e0c1305190605060f070204020403080a0e04050f0709061110180c061701120c0b040b07021305010506040e04030e030607050702030c010e01140c 76
    0x50720b1541c2c619150f4280c0c040c104000009214003910304201c10500b06119002e400161194002110710314280400780c070402041d1907090142114903140354036550a000c44052401d02c00091900c0c142240300102c33071047ca040f200c00e40c50078a0601507034651004540310041d107030300ba0684403229480020042d100300c0c3c1004204c1d810100b50030b030601d13401000e805c07502c05080300c0a0200765568400311000000032507121b4009410f040341001224000c40c09902d00c001d441041d21840c2003801c5103082600e41d14001d80d0800000d041c41c41e401c0c040b6114407a0042c010b01d140c0f900b9094403411043c1c0c0800c006005803000b68410721000c03c10803040d1b9030003100a100c40042291100e661360001a96500065000c1e806941040000c0506c0c0303605c1c3c40350740e040c0c2c0e00007403c2034201420305241043c41a4004c03c11003d100c20702c180c8520340d07582042154410040c941d07400f581c44940e407060604041545c405c940c140140e000071032600380e07008080b03103070500711a10310540c80d0a41e14454525003020440312 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 978841978 1250 978840728 978840757
    0x19171e090115140405070e030c0d0311010903080402150304051c170106050306040605030c241b0c01091d06100c0f0b010e07020604170d110309060103060608010905030d05060303 78
    0x2422100c00b00440f0030f554044800b0041660b4000060704c5144a115040c0c0c1e05420001411000d4138000341409002070103490a030744074140c0e580040342150072295056000c500c03c003081104500e4161605003110148215041c00c2d41003a030f640e5565241c04000c6100305240d110488070076140301e15040701d248403920710160401e503507071000602154410f550160260b0705101e00401c1908000484580d0f80c140507100c01d9005041c010131004040b01025070300d0401c2c0040100007034032120421500c03581e070003e901078140414010009040c05030141d01c0890034203008280740b0304521003000304551044080c0d5101c480c0202240c2d080794442c0d051800141101005081d08091080800794281617402d100c100d00786da52183c80e001d07681c074501120000d2400a810019801041c1030501410300d112011a0115520a05040c007018a41003100d5040d1aa03020170010424000301740126130050480100070015030580d91900d9440f4407802d0040145c0a4071000440c0300c43c1c9042045403040c040c503016 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 978843228 1250 978841978 978842021
    0x71b0803040c08060108030f0f0a03020403022d09061e060c030409060f050109120314160f030329091b03100e15012001060b19171e0901 60
    0x80c40000100240203c0203644034850010590f80d10000456640c4050740c0c1c0480c1c2400d030182c03030310660f50384020240c40030190203110000058441413045940d80501e15038603078034441d42c07009441d2211400058548141d0070071003070149a454502c507104e0000d900d060712426900c011804641d0350300c610115200c1c07510001600203061040380e407041c020b40356940ca542c0d80c89540c8200441e40d00e45c0c02d0250407000401c540d25540007178041d044c114010050140f4550600e00508409400200030500990310200b004541504260f03141c401d00040c000000a00510b603281d0046400c030440280c6501070180b0031030030203d4000496000000c40c40c941083c152130380d91030816000c0c9500c1c4c4851141d042045040301c08110715411a100c050104041a56003e058903c0d50895840001c0b50401d46545956159000300f2503200d810000c01c1004e0810300c9001445440400090203003000c0109154494082c07001c0c041c04c1c003500390b40501000d84286940d5003944944440a005000d25140b08445200360389 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 978844478 1250 978843228 978843233
    0x501030b1807021f0e030a05031b070309031e1509080d230c090303070f08070f030503180109050c060307021c0210050604091a1e09031e0c06071b080304 67
    0x900c541c1a03141c04e06807100400b01c0c0003400420356046414200482d04140015039411384918003860b402500211221009007031044a80d0944c0d00810703054001543c005018018041c8540f42c04030f0120b01740f48038000b0b1a945494032901d852460207200e900c0e90700c0369541400e1203080c60558031840f140f24810003142140b07440242d000715401940c0310360f9043c0100028250040c1c1010348200040c0a8081c515256066070b80c07030f030307060058001212903603000d00c0307c40041484401c18641d5140300380c03a420b940381440c16102c0301045051203032061581c14101e85400003040481d40e40c9101e10207884c25520b80e02c031813006a04045814000c0c2c1404000c00980d1000182d0000750045001600c030390821442e10703480c0500040d038101c0301016048075030750030500066003040c03d000f550041c031340111b41d030200d40140260443c4100a40c0c50a80076800442c260150000005d422090241d000e0100e51601034004c0b07003103850340c40040001d018000455008001440c0140c502040b1560100110b0381e030785441e1 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 978845728 1250 978844478 978844483
    0x31e031f12030f0f09030b060607050303070905030f1b0f03030c030a0f0906110c0d0305160302030c07081504170702060721020d050d0203100503010c02340501030b180702 75
    0x1c01c000d5000035511043c1074410350107042168250403069a078a22041c0c01d5442d000c0c0040c01c05403009800420400454020441c10301c00b940c018610356031803040300380c9031004052400094170741b0010b0f1900001001d4038415141e000c04030340d100c3c0a0f2449004071002100180c214083c03102a01c0320340c0000510306c10829070040c0c5403902c2456a4842c0040302c0d03100e800c12600300c10b038184000a207034404040075205241a508a040b40c0b44030f0f1808525101e280c045007695401c500c601200582d1001c0f404414242e014400c150113024042c008110041035200102691100a4000350117908004400341d40300d40c44204803a031700b0b600031300ba2980d58030403898501c1501c420401180700c2c40d641d0000c2035411034404581a60440620351b262410b24a446d00c1d460003c5d40041d0040780000501000000ea81d202070042001c000a550041c1110442e45000b010044217141200100201e90741c00d06400c5130031303410000c0140c41c400c1c0b82c0010780d0004400800c2d080300c0d4280b0340e48080100141003000c6030380d00 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 978846978 1250 978845728 978845759
    0x927020d09050d110102120a1a03120a020717030a050a050d050f041101170a230906041a060d110103140906010504110708070611073002031e031f 64
    0x203a44e24400240d000103566400c034081c180d00342603200b103680003080180b1519048014240400c0d802c0304680f200c5880000d1409801d0b60701c80e100c8850121382403510b15010310180d00140010071514040e010400d8030300c0d442e44a00d0015109114003c1011001d07184200c0580b03c035000000c0c0d041240b0300303103400711040b0b03000e0490301124903401c5808504000d500c03500080300c000b0b802c0106150103840d00d440090190500343d03603104100c07444400030344045081420140c0a1191400642814140303801c0040d03105191440304134046100304180301942e11041607000049030440c24040680d1402401200506070b1132940c8102140d80758103110310000003041079812100704035410080540590407003e5a0300036424060081c2c102071080380c1c0440c18a0f04020b40d600c0d4020070a83c13a00c0c4503a030700c109030052400f41c14450070f401403807040301c2c4001a10007180c84a01c90700045050900300982007402020412001082c07250100105005281c5440490340010203130310b0040000b82c5506000006940 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 978848228 1250 978846978 978847003
    0x333100203070c091e0f021306022422140d02011503140a0b09010b180105130c03150b0d060909120f0e0409030c020307060927020d0905 60
    0x8a012240050a00000807907440c07951024464044910f000100c074018004555240901441582d0001007902d1070b2003181c4405240080c01600e0324800041c00700ca10a19401090a551001c240c5070941c4240404e650480000207030045401c1e500d022036241c04031400f5540d0022190b00581c1c6908200e00c4190103000040400120b86a80841c00422800c4c1c509034481c1c51202c242180c01800495034451320140315900c0602101c101c40120354035001c11250803180741c14035941d108001c410307600d41600b60020120b60040108143d5040400050f60440030403024011039645000b142c401501981104580f030210240021249984411803203c42d07001d1904030100300c0ca0101c0104504d0840c1c46112003668214039410025540070790181c60b1140e40e094041c061010070b00500c0604c5c2e072140110540c6500c2a5100d03241c1d041d042c81810301e0308070540c00010900c042188248900c1c480070701645400070208552040d09032041009000a100300703000014140e0921a003c1d0038010000703460b200b4040c = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 978849478 1250 978848228 978848239
    0xf0204090f06151211060c06010f080706080601051207111917031501120b0a0b0c2a150c060103111302040605030a0507030b03010623010201020304170333 68
    0x10241401e50304055164024450315003c9441c0c084003250485078000031042000c3c003550301c0e041f6201002450b142c0300b42e015805540401e0f20912004105100b000700504140c10011000d0a04000280050203400243c0301c41d4503c1a000507802c51040081201e0000210280d56a03c5a02e015041101301d00038000d42e2079252481c0e812040d00d0440c0201c07441030348030680c1c1010070800880111100b4418880350074441c1e4550701d40c00c180e40d07141e48114004000b1114101c1e60340786011600c50411441e40180300b100200f241e00d4016114200d0401c0c540034800302e40032030483e5070b208900d00301d50140c20312035100392050000120410582e9052404000001c40c0e02143e207281030000704041e84554002c0a001403418800b160112000ba005560480904e00b0045888114040800e08461183d48002ca1860b4100800322406541c03601c22035074200288001d52440c0303440e4658103000280a2203003086d4080010004284181445d6200404a0f110b000121900c0ca200403d41c02d074503c40001d24450b4 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 978850728 1250 978849478 978849491
    0xd1b120b01020a2a0f081f0c32070b010501030501052d0109091a0406140a050d030201020c16080d030e210d181707080706090f0204090f06 61
    0x9600000341e003100307107a015048400490055580715100e1a80c0300310000715454000021851000800c11800a01039a200800325243d551f03900c401038a41e920301c082c4440d1700d03088d02035602540c02401140600f13680300c441e29042215005181041d100c140350001c80440100c1c0e40d1f020841072032250350481b4000d0b6824400b598856040014140007031039880e9440900c85d01070301127443c401c400c8000709541414115002540c508000041d1104465a9159000482c2042219140c24810000586085c1075000000c2c5942c0010071428030040c051188581204180d500c1094800d4040310100c3c0c2511059800d015100d11424407140454081c0c0c405030b009080b40070202e24071a22030a09002c00450040a001907041604800b61020300f08010400804100210300a151030050078a900805403d011450b080750074080070320024400701d1045240200701c04000704200c00290762100e0707044503000070341004c070b440c04400345031500500039002800c11042c20700f8400c4c50206c021441d8082c6109000c0e0 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 978851978 1250 978850728 978850751
    0x21050702040b1f08090c0901081f0204050d030c0503090406080307030210090b0402280f05030f0106240909050103200901081c020307081801020d0309020f060d1b12 72
    0x4400c0d01400300b035400001800d42000f50388540d0302c0c01e411030b482505881c031440c4103002240b0121002d1300300c0e0a41c4d03030020484200c215241c054809864915000c00c40c101401c060000d42c0002c4d0f0729001504000c5100c00e9803041c060203104990240f1402002000810b90310307030f941c588075007007880240c0140c040d1242c150780c0c0303da43d8010700c82003d500800c40500c03a9103560030048501c4014222040c0410f1807d0312260710640c05950340043c1c81004c81250b5600c0c503103070030140f030840407100c03100c00d03641020410402e4005d03e070600004001d00c080c50100d46198501c0440f61140d40d90b0000b00050b00304070000062155802522070000210301c107000c080c180420038000e40030030070310a40c040c0350b01c0b801d0300d1080d1007441002e00250b0b40a0340305980c50103149880e14101030300500c1c0d5801e4040e520a540107115a010482003455280b1410b051003814407503000160302001e221000c9018820025200b101e1020707030781c44000c40703a95000d103e00c075070041084024021303a08010b1044499107481181000b = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 978853228 1250 978851978 978851989
    0x1140a060e15090c030403110d0e120f03030a3c0c0309050709050903070203011d0c03120d0b040e0d03050615070b01170a0c0b0702090f010e040f21050702040b 70
    0x42c000d400703050381e125610707246032500b42584002c20030380810031043d6040b0710310181032000501c0031205a403401d40480101d8100200c800c21251a04800d9001c07240d034081307000011050342d174404445200040c40354183d5104400c81241001180040303058251a0390100d512500100794004410700c0400821843e40e00940444024050240c0180d0000508000003007060b00400e40c41240e1a00f40d038145196a40030a0030340742e80c803074280c203071101e84021660015410000302040300000c07030081940c06006080d0075903501c1400c1c600c100e025180c54085e4401d4640d9007200d000d03021518125004010b003000001c0040105035881c9105401c5c9003584031440a4502c2901c810076003000d148a0f81d64078200f000c1e9401000c2400102030350240302540c0000c9405000c0d55001001c030072946558403025403042111840004081c042d12502602c01030040142e010307503565002ea40403040b500350704484d080940da00c060072100c200c103001204441c50a4564008068044e40788242d4080c001c8452581c100607 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 978854478 1250 978853228 978853261
    0x11802040b091002071710050c0304020a030605100b0c0313060509010905130b03150a050604020a080c0d1413020103060506040b1e0d050703020a0809070e0112030201140a060e 77
    0x1980d2030750a010600c00c034500396265550b50483c43c0116000c141d1344100f01c00b444140e40100c648240c10000800c80140b0407030240315400311403510014074600d0300e980001c2400115000141c41903580301d0008407400007010030407001d042030010944e140e0f01080d9406a40303610642480048914001c0d0008015005809907580000141c55a610b01c500700000d0143d41d101d0300d0308404480344ca4003140082503c042c0241403e14400f4280360300d107840c00210325800c7c0d980140c03940340520f02c1000901031050303001104c0d030741181c0c181e0719840d40c603100d00d4100e801801182c1c3e00c071514528901c0c280100d02c6202c0c011528018400c1e241400300030760390b20070009240100e00ca074a603040410021101c4049200e4800c4c1c400504442455003070404031b0603400211a42241e1603070119034001855816290400b251541c003ea246008054060a15110000074031041c85219417016420b07580c0700405000f904110300001c800544810b003443d10040c01d4018207194400c02d2202e462080c00b00f400035070000c90320b1 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 978855728 1250 978854478 978854489
    0x60b090f041a0610030b01120f060e070804080901030b2101051602011413150510030b09011802010f1b0f0b07080c0403080a0309050a0b040615061707110709020301180204 75
    0x400e11300890100c140c001d451004400303410452014401529150588949200b00240c004000b4a4500345180c0c5548081c01801c083c2c02d104032442004001174601040311082802803034007042c5040554040344100b03800c070580325800044400220261001580024800d040301c0300303081d03400d00c40c3c508140d00302d51000c50404036400d0104001401c01104410003581c05102d85051a80d143d170031a260000c480c1d090f2526003c17103540000c10800c0c002c0200c459500415610000c009a0700410a02350307041c841034030003d041c4441c460725180c0c0c00d0f00508036076081c0301e81000407200069042ca010307548070b00601e108070740f0003c504021900d218843c2103030f144501c3c00480c20134039003411034443c54090f4005098050401d9258000c40c3d0002c1c03014446454800d1149030420940d0511385000015601d100402644901e410003041003101d134042c5c2038450003c2008000d08580d1129241203032803001c054141143da20802f100000c1c1c5544a900850481d0f0b942d0b28604c442443c80302903041640320314403e2 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 978856978 1250 978855728 978855739
    0x50c0703020715020f0f1b15030f10180f1109090103030e0a1502160806160c05070305070b0d06050d02010e10110d0c201c060b090f041a06 61
    0x3c3c891445551154052545980102d51418440c000401e00c2c01c0e1020280d807807260490f0f04c0c18203821310511002d6119890441c1d24840c3d0107400340301d00303109000042202080460b500080b0f42c0904d00300c04034002420300c01e4040c10401100d900d203000500000707003511100904c1e281209101c2801e603070684900200061400002c0d03440d5880c21078000c0340c51600c80d64480d1140c032001038010a15890380160b00f269401800c05140200c050701c15268056002c0740d003542011301080307502480d40c1620301c50401b5030304051201c0c107994100a0300e0414603800042c410710414502044c4404420301402e1408803080040c4080c0d5222801c0c0702444412020007808180203441081c468030f0b084401190a02c070390324001e218100c904540c103107840740c070303038040d4010941144000c030a11961a51458141e02900055800407000501294841c81405c2540c41200003e020b5030082040c150410403039024001c01a03d011306242d4452145458140c40480728104242000e4000d120030907001031180100510 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 978858228 1250 978856978 978856993
    0x9030406080703020f0315120105040804150e13021209030702030714012f241602031e03011409060d02040b0a0f0b03010e01051c0f0f02040f0f050c070302 68
    0x20140c540c2200506042d050540030321004000c450440043d51280030858052403440c81c141c0e082c0701040d04200300d80803890741003100700b002054941044a080702d1401d40c080c0c0702c1003140700d0101c8200554076400c684c4230040c41b21800ca00d448640240c48282024800d68607103031074442032181d403403044c1c5030004d4054000110030040885200e5104c6a000c1c4d0604001903000b031009030315039000745462251881c0c100c9030b075814003441d441084211900320074410a003c065100c1070035000005002040324041031030419070121034038828000c1d42c200e5a1200c8c03211110100c41019030106030000d0280f42040300d00000c404405241c032510303c60240c1000344c0607011644140d020722000d0070107152201d421a0107843c00003071480042c0c2400c0000d05044400c0e80e2254100143c0100080c01a44003910403680f1820302000408500c4101c0e00e141d61042c07034043c80241d1490700c00009550b01c84080c0d80540b03401d200100d11000d94115081d5901c01c800100f0040d5618081d01001d40108070f00600164884130 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 978859478 1250 978858228 978858239
    0x5010f02150a0b100201140c04060c15060b0a0206040510290627030105100b04060305100b03160e0316030209180109120207050901060c1b05040e160509090304 70
    0x94079207400034002c0c0ea0120304401500d010a07442a140d1003c1030040c4e40d94000e105087c8044d00401e6040005840c40c540361500d0400c00a2503822002c10140414100240340144058a030744500014a00d95910503190b807801e0b100607443d01022101620b15000e0b0040744406503102d88079007200c40e010294080400310b03006100d2601842d13444c1c1481d40000b010020344102c400306080000700d805401145809040e4143d062600790b6030040c210b80441d1005170001d120321390b2041c05843c19101586800141a6501481070700d0780ca05641c0006020310000050000740e00001c0319812010340c07140c44580d0140c00540c18036545040c2d00c0221380001d903401d14203000520b0602d16140e0400510040840081810300c1c0080c21110800b008880b048030780b500d908111501406003800a04089440400542c90644040d056454444c03000303007180f008580c3c031401c0006100054000d080064400c205145900d02c0706a625203801440400490310200c00044c01d00c1c1c401c088620443c03e52018504051416 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 978860728 1250 978859478 978859513
    0x1c0c15050301180e07090f0f05040c0e0c070f0c0314120f0d0605031002131a1804150303121416050a0507080f070b06010e031b130509010c080105010f02 67
    0x1560418080741c031013190003840d0700c081001c8800341007415400180c058090070401e046609071610134030310900340300411001c00e89a0718940100d0391828010003040da80e540b00e01a643c41511001414100d070030280c1001d00010307521007020750b48a010743c1500100c01c5000c69680e07952038102d0321085001004801441c10444014004c40807944c40042480ea40300c000203401d061614104001466000c5506100c201c0d0b483d01d240010802400110301ca141303604001c01d020300c500c0560551142408071169041c2d00d595004020320710703801030241c0c1c0e1907441c0e10300101400c41e81d152220f03910342031051414102c02e150784044c3c0a4402802d8007200589450342c10746554100145150030b01c0028401100410490340080040c10807281403e903444440740b512030181c00019240c14104801b260540a0f1614000b034000c0620143c1c1042211920701c01000460100001d1501007000303041c2070a00030888015048040100d03a00c1e100c82940d6038980b001180e140454801c407a0060f0b00c03a6400c042c1d841c922 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 978861978 1250 978860728 978860759
    0x30114030c09040219090e060a1404151a030109061b110616090f080c01120605010c02040b040b13020c0c010c020a1a090612060a140f09090c1c0c15050301 68
    0x101c0801d11280c0b5034506c080401c0741c21001070101250001c07000c0200340c95262240d4518866100740c00400750815490f40d01c2c600e55240010081c941d49d0308001c01c20b80c10001e4102c51504c41c020000c2c00510740c14509000a80400211245079585210020081600510112004071440401000d0f80c1d03892241c2900403031000d201030414011844008a0700ca522520031a0140c08104010f20903603d1160004003402036031354082c01e1407490814244000da0f44810b03008501601140c000c01c5c0d480851000400a1411000b410f6000802c00d014aa00203110b80150080b00b82ca0300c180c4501c0d2030940019280130103501d0009600c00101441440581090610412168140722960b8180103840001c21181d5020b0002084004542c03003c214031450441c08400207440d22010000580b4554808648500301c00c403451032244040c5400107a085a00308807440c6045001410604088064100c04a0000b000d244c203880b80c000c01d0001044074041c071241070780c3c9110720743d43d0b05255a282a4001d10090310 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 978863228 1250 978861978 978862009
    0x260a05031f080a0506070e0d1211010f06030203010f060b07021219060204140a060f03110904110301051503090607030e0c1504090609181e0501020708030114030c090402 74
    0x1c0040310070508107003141da04058030b5014010038107814641045403a104005000e801042164203001c40b1648500f229480c210754003810501c0b8801e076544040c2d40d2031401000c454400d42c83c11908412141281c1c1040040f0b034000c1c0c00821003503400c00305a50a4503905d000b00d058406e41006640700508042c07041105e80c82c40c40c01540d1034100080390106403e10a4a000d40b0b5481d00070405001c62003e11504100f682822103102c40071500d041405442d8100d455141c2040c5980e9610841100103260200d031945500148100320441c00c221848030190402e01510f4052062021910508161032040328090800900100007540d1802400c50203401c409a0410a501641581e442d040e200c041002d80c20012400c40c9544075410052200103c8400703620424980d401d040c00300620403c04400300c01130540040d418020758030b0808003220241e090450041c1598400a0410180032400e00610b05881d1452080400c0400c00001c141c0c4e0364000207689548400714801040040c6400a0082103810 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 978864478 1250 978863228 978863251
    0x702010c0804091a090a0504020a050618040612061808030a0b120609101107081b010b1e010305010f180b1504091a01080717060a031707260a0503 64
    0x945034200403055510755045282c0c0039502c492458000d14085d0308141d8014001e003010002d070303d01074000516503e000e119040c06420b0010f014a0b20800d00d65610503c40313000f42040c810305540c0d001f1588400303180c0300143c03001c0e4030781007000314240201003200e01e440c0d80100ca801d007141c4464188800070300c88202c016510220480d4000030380c100512100344100d1905025140100a1303000b414107130740c10b0b2411140f480c0c0c006c200c054005040042134880d00590703140d645c1c0306106c21140c81030042c841080303002c0c0c1c0086110410b046d24401c29106e4070500101307980602190340c1e00c040e16041030720795015500c03541c9c10074103038003049043e40c3e4003402001500800c1e0030071511040e40c0d25542940a600714000b5151141b2440428594508100003556420f00e040c03412440c0c0321600900e04400001090311015a031400302d22555a411003030405150002d07140c080c20340315865408642d0740511800c54418099101c19540c1c1034079042d1a1180501d100b6240b8a45101c204c2e04036000c1d80001d00112080 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 978865728 1250 978864478 978864487
    0x3060411041b030b090f0105010f0305060d2f0d1502090112050108011d0f0a0b25030525020c060702010c1407080f030406020c06030405010f1e0e03030c0702010c08 72
    0xc94041104410b4600e980c030001a07090b00c42e402e01c4034800c0c00500010b00001e240c0010081d990f8003510798104d044440c500020542c441d00001140d418040e0006000ca060742c1c00c0282c0704507690111a02c50030328241410005403641e6081c4000000e120201800c00741c1501c00001c05441c0c6900208000e90051520954080200310000704542080c0c000540981d9200c14400e00c1c113003111061822281f038800141034030307101104002e40c1c40d40c10040091040740c5080125951030303000780018451040b2481c016083c00c81c09003000300144400c551041030030168880c01160307200c0c01808100012010750140c440018641c1c244891035001d200100e042244c2007401b00c0c080b4800456118030003807050058180e00e4540320340c640c0f038610748259107040358104000400c2003e8000a82d20080c85e011b0340c440b40c4075030721802d213540180000a450790b512400c00c1d5500103c8030780f4410540f404c56a0401c1004018410b030704450340e900003190010740d0b135641000313520b016600401d4140c0d056403003a10381c240380c03 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 978866978 1250 978865728 978865751
    0x507171806041214090f0607020105041205060412170106030b0f061b01060f12110f03150601021c080c092106190c050909040c090c0206061e0306041104 67
    0x42107000c540503280314904050ba098081c0c4d20050594910003140c3c20039007441400e80020300e1903808408814400c140009181701164054420b8800408d0f2285110b0700702e10190408030b84440c402c5070200c8000c1d515092520803280248060b035104401c4810181c45a820310710309400400d02034824540c00707000500c80541542d1154018030407032414640561010141c03a1042d030a40c0c5840d0001410801100030500c00c180150161558190300404a462003821802c0070451403c0400c03503458150144095134501e0701e0700b803540c041c000c0314283e084850030280c1d00c400183d031075120760792000001e01c1038021a50144080d009031104c500300401810484400d0104803c07010080d24040100d83c0207a0300f00051440f0004003000404800c01c41031003a41c0c003c1400602c5c030701c10300800ca44600b04403c042010300c1140c1d141180506100300c400c00034004440406035603642c08540d81c0d40b082c0740512649002c040800c52103004150080c0050280340c98503908c0401100140c3c039140e40040d5140d130250328 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 978868228 1250 978866978 978866983
    0x207110d05071502101401150c031716080c030709330f0f0203043002040e010e1603020d020d06140a0b1009290909090c0907020105071718 61
    0x40c1c0f095002032031a500c02c203440e0410f46908007201c1c09905201c00042250280c240b44040c0104914509840900020310301500d8814100c203c80303440361010000c0044800702c1e82e4840c000340a00340c803075451660b03c15007686000d100071259000003810f50b440401807109d80d89510082c9441003010f00c944c0e18083c4890191a00282c0844000500107412440c035050300028121b9024000c4c0c070280d032400d818812450900146041c000c100402030144000c6403018514624000c1ca0f801003042c00194002000385011f80b50144042c81c4a0140212800b40040410054070803a03502400f0304a03200380076000c122890201d468191003280d151120b1400c005440a40c0e0f501ca103e0810001a0903800d260904c0881d07410004401c0c140450040c00340010030207003c52442c0341842007202d010841e0618400d42c50b83c040e10019581022000d000d00005c00d4020841d4400a5030558030907000795a2800200c0c00d0b20f500b03542600128103068550401d0b511203541e410f42c0315001411504101072910b90151 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 978869478 1250 978868228 978868259
    0x1c0c1208040b2d040608010314010f1505030c0d020d020904030c05070e101707090f0216060c14070804050d061404150e1209060a180321030207110d0507 67
    0x2c02500f10150a5a00401c0d4a07419824406609591505141c14118050700b04103040c040901a0801100038511036042504002e8803d070039018180320307080e83d605141d5030050140c040d0b80e100b03015140e603030807a03818a203010180881d00104030a41142840e024070600f29000340080e810800c00300100c0e000303c1c80402103080240ac1450310a003603490001099030b001102e0390481c002000d42141482c0640300700180b40000ea650004000903860318045002c0c00031b109a40c0990080182c2d6600c1d1030a120304c41e808965900313030640742c403444445408800b20791071288960040031103a0a11082c802402c29005c9451a14801c12000031102101c00381061000c00486046554a2140402d001051060300500e009040550020885821b0b0224010402d00a0a02c1d00b4003440d00411541d0841d44907441c001e224100f845402201c060701c0c0c0c10503400c100482990b034260044815410f26842e4820b100302c0300006c1c0c010500c0805034218608004c00c11240410564081c030810802281c144614201e18 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 978870728 1250 978869478 978869497
    0xd02190602010b1221040518101a04180b040e030306210c0d061131030b0c1308031809100e01120318090b1c0c1208040b 53
    0x141011440c2150090950303900d03038003941c05130450105502e40d1250004000200520096825000c031100030100b811074012076200340d60128528407002076000040c04042d02440d10b0f0700980030460f03107135001e0f0071403098940c11003000c0311b0042008111130031a0b4550103213280035608002ca490340300100010142e0f141a950580f181e0800000e010380382c907004002d404601005079100901c03146204a0b2601c951014243c18082c806020800e420024207500a405000c0f02c0301c0c55680f120f20300445205120303641d01018502007060248440750001601d070a001f00c0394030520f05001c540d1282c0c014900c1c0d800c4540c0300d420580c0c1d1210b000c25010001e1001c0c0030b8015907403005080b0401c9000400c8007440700902002665683c0001c18000e01100481d030720705680544c0d82c003e25421240c50101ca4068180407a031981c0d50a10302c020980c60840d40002c0f121038411640410302c06c6a01c100c100d4030041504000f0541070f90004c0800c2541021245150180d004041c0e00c1e04265807412110340991124684 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 978871978 1250 978870728 978870769
    0x30209040c0806010e010c1e0812040c06112a0d050124091109010e1f050a08011d011e0504020f25052821020d032007020d02 55
    0x3c106095900011a50054000746450300540b1580d0311400301400b84c0749134601115405995400a212200040310315442c00d41003080080c0c54242005007429000b400340c00300103041c1d0040b5903043d0300002603c92403601001c80090103c01d20140d460380e4181030300c030442d800c034034414420740204400303102c0e000702106004c2840542d14281c101c410600300c80c9402150040b4038001004262811600540e4034054080c2045038021140000050000f0340c0f03e0008600ca82c4045650031005510001812007100151500c485507605c42d8510504495254882d9031000300ca0350042040d003482804c0e005a82028504901c0c1050326540400c06a92080c04002320110340001c0454004c0410409200c215034100c07814000046650b480c00d8441c0c456040400e0603001e0b400b1003001c0c448264010340c880941c0407041c070300c40b0800500340c0103210008409080150044081c0310003010b010f8003890710941c4a1f04003139000708031604038222440d0090310782039802035002d0700d41070010f885074015102c200c0050b021 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 978873228 1250 978871978 978871981
    0x1b0306012d020f0f030f0915091302040816050f01140d18051e0304090b0f0a0303030e0c010318020402030907090e15090309090f15151b0a050a0b07030209040c08 71
    0x10189070049940c40c611381a442000111103400440080d00c601150854041e40704c0005054001c455006000c4110751013441d000d03209503441c00c0d40d130050088551820580307140c02c182a02c406c0d000030704e41c4121500f000150070005140c0d84560111202200c038030f007402d400c3c0640d040400e401c039140d20641c41d90000380444882c0c18480708000b42c0300212500740c8a003540c50440000191a8003c0d4407841c1e8106403181e80700c40499803000161020400090102c565035079403810020040c0c80d100e00214464043d801010034a544a4019003902c0920b64040000840c0c00ba82440004d40c0001c064094034000c002011031410410701900110200c181d001704600121001045050707100503004015070b0340200002155501c800d214590b000c506561044c2d465519191180d002480182d0101d81c0301f9402041903086060950240184240c56a024035100185928060780c0c1d640b18003001d060381d404480b0b08030014100a090561014040c607016042540b1080804e0658650f2200c1401040b003070b00 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 978874478 1250 978873228 978873253
    0x2a0909150608241006050a0c1208071b0209070507020414070906090b16080f1c02031f0e0a02031e010b04090b040c1403130206040e0105091b0306012d02 67
    0x40030703c500c100a184aa80341d4200000c090b401440f451041509203e404039800d0829802104003011054004000c4005071103e4000204034010459080001c54201002d003980e41c0c0001e034a034182e440d400740c40d000c000d859500381900e0700d030420481280d105031902140c2040111200d403140c01891161124400641030000c064003d4100d40c00000c50303070506105a68480e051103880181e003503013000d04a40c1d605002c00e110b0240d80701300c0308000d4001286840f1210002d0b03890780203610840031040440d00c40c681003021408001c140e4800d02400c0211030780451150615680211740090320700c00c0d800108009141409140d41d026407100e60307602c00110382048484000e004805601401700c404100c00c078000c82001d0b044515640c800c4e802d0840100000c0c880a08905401280a130010034803a01c855aa0504d4980b9801c240141401a409203000c120369154008090f500e0500500300e039030440c0e842000450700180e0046510011144107080d030814a0784420240780d400034644d006d0481c040489 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 978875728 1250 978874478 978874513
    0x9100305031602100206090c0607020a0806070e0a0602010c0806120c0d050c100807390501020d0b0f01051e07120804061d0703140a02030115032a0909150608 69
    0x10903900b4159007101b02000101d000200d00c4007804a41160300544524840c00070841d00c580981110003c1d224500502640d55002140002c95105c1103441500248d01e0b08000c0303003612204c0301e06201081800c404103915240a1000305e41c0d040c0040200d40000d14503070009640207800601c1582c4030b030440d4801100c0384c1014804083d00d40ca00381490101c0b4144000001c00140000540700d2101441c61122101548252031081030003610043c4c5017080700d03090405500030341c00761910420003480d14240b400c060900200e0701c2400c0005031201418011028200c030000f031000f207c0719500c15801c004180004080481c40b02c0000c4566072444010725140ca400400c6134600303100702d1051140590b81d03100e0074070002000c00c2902e0380b103051015641108240c071450110724150003035040d400d040034030608106289265088a01503141040c90000078120891041444d01094400701c00c1ca410a011915803500101d000c548140c80000380c4802085001080721181d030001c104503003045000c14035000f8203 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 978876978 1250 978875728 978875749
    0x913020f130801060e0403030b0f031e1c080c07080403060c05030a1503020907050c0f0706030504031b02030307020d050c211014040b06120a03050a09060f080609100305031602 77
    0x31800812144e41854101d40305110001c2c00103041548500c1d80350340315141c403807103901c0108000d022601344081000025040c444a003809250038460080320344401c0441c000a6007441415855042c207070345071200c09150f613900400003545c188e182080700000180c0c5030701c65441300701201c0d56400e0b12070070f1500c03a200c2510b01e01c420082a01e503180c507061003d6554101203035000300b000d040255487da041c0410354246040c0c1032034032001d401200400959140c0680200b813056100f5034807044003c1d4019440080000342c440b001e90142d009012203070050910044131708485d0b00030000c465960b0245000030380c54140015100210800303025407840000d004101555800350922030900081d91600501c1140d0800100003a100490b01004108a80c483c02420600e1000ea607003a00c0b001c0100381006411a8000c48407040041d846000024405201d0742c0114940e6009a5840b08251544030400850f80300141542c100d802c041000040010401c2008240d07110714682d400b90800110700411100624 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 978878228 1250 978876978 978876989
    0x4240b100305040b010b2208030a020c03060c1911030a091715130212150702070b030601052d04080105040b0f012103140703021605061801050913020f13 67
    0x621050000044d80403030b4641c19511000b20f065140d543c0c4108140c41b03030800c2c140c56000520b040c440441c0c1058080700401404540360215103082904000780360b5940000c582c825035050050201c40803188113225004545000c034030300302d140c503010002c26504540c4440e07484c0e030200b80295420821280c10300c0c40150780d06070b00005001c5e0583c4a900c4100c28200051250f140300034442d28180855481080d070480c4540d41c40300310b4020902c800340c0079080c0a42a41e03044054420000009036405a07181124030070034041e500c0c0b605140031601e0900c0805040c5100c810904901408151040440300c00352004120f03c0c0f0020505085c0b9040ca207440d442e020b0055101e0b8010b000060000c10341400d56440070041e015006946c03011103007001c85182b0220381418050043c00112002410782c001040410302c031989845a91403940c83c810409030b44108030b440642c243c903018082003250700460183c01b034844090b1290304804181582c501c06c85e8054080c0c80c01350340c0003041c01810841c8041145000c0d10 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 978879478 1250 978878228 978878231
    0xb010b0c1006210606120308041a040f0206180306312102011103040f110108061e130f06060f0f09030807020d170a0315050a0e04240b1003 61
    0x605002d009061201d204825290840f40c1181440412a1582c0924001c1c89984000c03000d4580d149030041c201002960103803440b0202010404000c0002d218240c00b5503030003051810060060742c01e12459410481102500c1c80000403000140e0310305200c1c030b5100700520706120700c42e004802d104034030310f98081030071307000d20b404200ea44000101c803180032088498010041c0098100b03041012800b40c03080300119440d102002c0103020401030180e0700e00c0b01c114800c0842c1e42400440400440c1c0404080341c40f00e5201880c1c8600902080b21280c910b2f00041c4003410398a54090b4000000c41500c074100c2441400c207940e001c04108076648041d10511030403580c81d00e0200883e40d020028200d02c0c05000c0035001e1000040c147d400c640d44d030708a454509a000c90005020f100d1081311002c0c58015441a0003c05e090030310300c8101010700040c1009840f8000c150003d03441c100404520464001001216400901e10040c2c190316400d10710680a1000c2e40c0000c40c13141c000d2014081c2e443d68520880c400e06 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 978880728 1250 978879478 978879491
    0x1020c160509341709010c080103121715091e040605060d1e020f010e090a0b04090506090703030e0d11101b0308040204051003080d0209010c0b010b0c10 67
    0x19a0303208107541c3c100d4420464062500ca0788656615802401400001d40c24500c910258026802c002c4003001c0070300719080b030b004641d5a9038090742030740c12824250000603583c0f401807000901d84c00d20424000c5040c504413080c0a4401c04895240d001a1010120203141e41034405040c900305204035848186c2c958019035603842c60300780e00042c0740040c00041c0310503241c2001070580d0b12040c504110031504100b0a1401c0307020840c0c80c04c941c01b01d644080e030251403c6502c404041d405140c1d101c1e00c00c0b10190801941d942c0301c52985004000011803540e200e03464500705c40200341c04000031801000510040d083d281d2075890003605485c1d081140300d00400301c0c039140202242c2d410900603143c40341501c9450101d8411042105d2036001e00702c6000d11481004401400c0c55440100107110b54420780781040b45031101e100a10900241e44401418001d04001400c401c45058001d81401d05040c108100000c003181e581c0310000100b40c0041001c2100451224268a0100494000d000e8241d00c1046030 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 978881978 1250 978880728 978880739
    0x803090102100504031e031b0801050a051314040804140f0904061503080a03060503010e010b031c03060b03010b19081005061b0601290a020a02040e190501020c16 71
    0x1101c0c00c1c0c007081c5403050390f2074000900b854003644c034842c50900c44414803214202030000150003444aa80204d00e000205000d0a503190700500142e41030300c500502c2034090a26140408c40221240982c0905890f00d035540143d8054010b15018080c0d4401e2841545950a11a010f1100e840c0d802d103141c4a650054000d0130b0980b61000f611f604190000400714000818907000b80006072036910041080c40002107d4070b18a9041c0c0c052004e54074118001e01c81143c00e22002400d0700c892a01c8103a242d0040d00c0441640021303600540403c0049003008500695224950a4150000d81c8038001d83c040009099921610a40ea0f0b0300003141103080034505420f0140388400304022038014540100b07c0010341c2e2030440c0e004654611a0040281152070030f40e11844448464424101e8180b029098600ca1a40c001e280d24207503410082c0660040041039442e40802014001c52070202205006001005070781090010b48080640d000b2070015039101d00c9075000610b8421040002000341c00e44640604c00c = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 978883228 1250 978881978 978881983
    0x4050a2417010e041a0a02040504060e010b0a0e270f060111150a0207141c0503151005043c050312072d02090c092211040f030506010803090102 63
    0x54902d9014080f9240d40e5510704004178900044103030312010840c10801003103460382e80041040d00c00646090200315504d0000c04510002070142600780d820502007144080d11400c40c605411500a001c180880c520812420a20760400c08680c1e51101c03981c208101e02c0e40700807a05402020a1902e6000308840301d1000d600c0d00091140b144511a004010420412694055490842e0001484145030018514650303844005041420345001608694588140184d060b00e1080c0141d405120820a600041094480c003540d0302e18280401804003050039055515182104213011561910043c01c0d4820404d5083e50403a641450041c0d040c0c05000e01e8070702046818400400300401900c91540c1d14120f85604d030b03242d090b00505a01c82ca030175001040045a012440c5000343c420710440c0e102c12003414498481c0650064111106207440b50b10b4900b404084d200b00c501503480000c203c280390014000941c0305038050108164001c4052003805014040b20b80100407910086180180c0c0c440041e4 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 978884478 1250 978883228 978883231
    0x81306050405180604020d021209060f070c060504020a03120e010801050616020103050c0d09051b03060103111215090f070f080c150706020d02120a0b13020c0304050a2417 75
    0x40c010380200104c0c010341c0303440e0182d0b1403144000070299110000c4005802c40724100319000a200d01c42c240c042640d1019801a660081c401551000c00202c80d0b503c0c1c900280c2005002242c10207004840040410b241103140d0355900341c40d0b500c002002d905003000414001040e00124456082000110001c0c006030084500c01542803d01080301e941303501d8155250f0040c0c81e03a20341454100000d2a0400c1800b0400c1d10183c40c0c0100c0b00743c1c14031240d0f400c1c5070381d62001340401007694050031b1000b0054580002c6000a00035104201d0302c003082000c05545100c44143c1c1d038042d040c0e004042a5051440900c41440909040a40d9404071480d141c155035454890020030b034012556a5007498504030104115406180c010b00255039890006044000951000c0c0d0260541002d601c04952918010300a5810301d10300184a50488000f0307a582d00000d50010704140304a20041000151030789807414040024902c280a11100d003603801682c92002000a00d560704000d04105005009207400e5040c5 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 978885728 1250 978884478 978884509
    0x603100b030a062409090206070f050309030a0506100b070b010504150b03090d080916180605181006021c0f051c1506111002091c081306050405 63
    0x100300c0080300408681490203000c1c0c060300003404c00c1128110b45124800c0024800e02c00c001c03060400e941d412000d4125501c9281c0203600c600100300810100b1015184090218002c009913880d081035540001d103810900e036012200e0746c00810070007070b01c046910f9000c401064040611071030080603949060146c0014081c8900c640e640b00d00d00080181201c192001504007042101d95a00300b604a880c3e803440894021000220000c00045010f14081004406056609904295a0304240c041e04050a0705402d030409581d03140c00010b8941c2c0c0300f011a02400c056882e03103907906d080c4500440b07014161900524255440b041c10301000459905160303085135180d26061145950700c5504540781d00c1154543e0342600110a03280c03a207212a64068982000f406c0c0fa2402442c2d601c030019074090100c01030044140d0080450103d040089400600a013200244014041c5614000184621202a07400c0e1a00305c008140450312400c02131043c40545102d0404e1410640f401002840c11440c42820 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 978886978 1250 978885728 978885731
    0x18120d091a040b0319050a0605090a0f0209031002031e070c082b020307030f1a04050a0e0a030f030b01030501051c050111030702030c100207021503090708010207061a0108060310 78
    0x92030070420310041524090842d03401c0c00d0341d0b0b034106030701c0070055100d551005070079007850000800c880014901c42c203011188050700f802245da072800c803104010003090680f41c060680070089000c81d80c1c0c0903c03070401442921840140c481c204440b564948076a100c00500d691078414081c0000305d1780200d41c4510360350b07000c4080b90340c0d442a8480e02c4003141c1101402c5d000c00002c000445a0042941c028610610340b031364041024046c0300080c05d00f038641c4810710105100d4140c903c0c650b24203203904141c0e8007a007000700104091040782003031444c100c0b07006000d03000541e8402c41040703225414091965003140918080c8000d50411000601582d4108603070b1684940300c00090003044400e400000c034203040702580503228901603070f01946030741c04100e14140f58003801d114081050024800e945070715030040c3c416951030b41c140c840400641d10141c0b001701144950381c40015004800d000810440d0b118840c0440c00c86e03a00f50884e034140e40c0c5080068144002602000020b80380000c007420000d100400 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 978888228 1250 978886978 978887009
    0x3140c0304121401090f0b0906010311010f0e03060a0c08010b0a0504090216050d020607030e03030912070222060e0f04020f040f090212011a120a081e18120d09 70
    0x7002c0710300421842e004019942408880414004140300c851106c4e406501c401c84583d0300c01030a42c0d2529401d02000b48a0501c0189914083d4483d6a00c0813441000741000c250a02d01e1400103450f18a0407511400400d4942d41c1d50320303031168012111401802c10b41001e40c2043c01410000c0c002c0d00440c000c0320b43c8603501260456888501407540e610702508002650410740c41c0190007503d610048600c0408a410103015003414071002007164840c002003070103009441c0448003030f43c80c6540305040503a03020307103100d115800c1c200640c490903050784007001d00003134002d00d400340000c0c0001004110384d950f961558100005a2a00c0c03101422011040300c000604090300c0140d1001884030200182d04405840e0702c40728840415445415510340d030704030540c0114a08001c12000345101000000c503a0810f010380c00002e140f43c805002d6040194198140302c201c10310300410b26030009103916021441c1c0e00310565031070a146076200d0400303020f01c0c007030180c0c003000c41c0c0064548062489489100d00c140d15 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 978889478 1250 978888228 978888233
    0x6070c030c0204020d05010501080c0c06010b0d061701061809020306070305100b121e04081e3106033303140d030c08060a060e0a050a1203140c030412 66
    0x201d003000d600e640203204640f1044031101c100010728090040c1404501004046200c0240d0b107070644912110b568001c1540e03a00f000308006c03483c4c00c41c8845942c05c588452004c03540640480a0242d0340030f5410002940781d07c0d004041803800c1c0603840c00141145001e03400b0000d6140410442d90000c80c030f00f07001c00c02d919a5960106007103650f40c402c124131040450303000881e042c9001c095020f01400e1007445030740c0064499081d403140007540d0042003c90100700705070351540459400c840380140c0750513141c10401288010a10749101c60884103c02c00d00103074000b840f0803684d4100d80903100500e01048050342110280800404022451b840c0300c0f003c4080c040d00b41c84080400010b103610180c0c1a0103001e102c41c0569a81c0121000f42d40442c0c1001c8283c03101a01ca840e07c01e1080b03e00500a4885a14210098074030400429195800001e20780020071180c82e220400c20050000031100048003000d4140203140244988021400c1203003007000c203144100010030b642c241e94240000c00752051861 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 978890728 1250 978889478 978889487
    0x1104020a140a12060f1707080304061206030c0308091f0503010b07240209130c08041202011d1b04090507050609210102030117010c08011a040b07110f0a060206070c03 73
    0x25460860a08060f808221301150308040c070204e45041d41207200342c000c0390406c961200010701030269140d201303100c1004843c0c441c0004803a81080017800050183e101e4852819a52490308180d407420030000d0601004e0415240c0540807541c154007101c1e07600003000d001082072006108402c54248081146030500c954010540da840702200f200100c8500940d003045c1c041e4008140031031045001c04850049000382c0c4c042c078000d40d03030b03283c4c0c44800c90b03525551005070140b14003140c54215940e030032424008140b914460001c3c40e41a4005007101001d01c50f50120b003000d9a048103008605240142001480c0010300c00b040d620300700d55458541620308086001c10101e5800e8540032400080c01c444840c1d011742c02941603d0703d1aa502109162903001d02e4240c40711020818005016840104190000b9200070400660760580051604c0d41d61000b01d112038200391429078100c90045018811403508090801c004101a140703010300c18680103020f926038a00611031802e0020703602c0c0020806208 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 978891978 1250 978890728 978890747
    0xe01030f060e06010f020a030203090918030a0215090c180414071706060904150b2107080f064302100b0109050d021201020d06121104020a140a 63
    0x10908000095440c005040c2c2d441c02652070764003040c04a0000c01103030b40701055164006416400461801a0b0641807007100702000304241c41c0040000200c0c0032042040c40140391001c815030040841000580640840e00e10184c00c0f400b160344090290380c0320340c4a01b2a204004480711840d090160303128105098001c0d01442c180c1304500880b48042229284090480b001d503420304111400c81ea100400e000501005031809040036004144078610311038190000140180003501561494528002154400c8a072000001c15a0004441801450b00c10400c000ba00c1141000802407814a0385400b5080c0300640e0380c00c5c5441c11485070070207041c1d44258039020107a02d070403901501550301c824029112401d44203240040313802d20721410510743c071500404094601c010900d0800c02d00707036420013074980194500014595000c2c401d001c0002c2e00e507c184001828001c200030a040418507040c0440c61250300e043d8456441404003240d1194803a0500d4400000d02003019500c00c886601564060324 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 978893228 1250 978891978 978892001
    0x11010212010e0a0e03180d0615090f0f0218010c291611030a03090317040602070c0e19050c070f030e011d1003050c0415020a0b13050c010e0103 63
    0x1004400064030441d254500c6101c0c041615007000701040d010f40441d101c0c800c40702020340d041b180c403240d884141342c200050ba0201d8841c800008540d60030030401801c80ca01c960000c0185581c903141c07010202e11a00400303104240100e000c516041500b004400d54601d104240390400407007082600c10424a100c0f0f12014a0014100440b0200702c06061b101c00c02088600c01c80503820208c0a80066002c1c2580740c40700304086001d50704108a8a0048000748607001041e420041c60499207101204094603041c041c1340921030140c0c0d1400e40e03080c9164011299401a0002c0d4442ca0420294540340082a144400c1c6402c0c08209503c0f1881504c0090098403005425010b5501907134003050b40101007040605401e032a0030745001401610b652000454401c0c3c90b40095402102c42841032280e40016404040c0d00803440c02e11313072141103001c21007580c880c010002d64001845a8180604401e000390700455004001581c3c3c0c8681d641c2036190081e805945060000342140c240040e030080d080280c6444 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 978894478 1250 978893228 978893257
    0x60109230406090309090e0604020402030702071802070b01121502090d060203150f15040e0702070308040603050714030112140c03100b0f0910150e06040b09040f051006110102 77
    0x3460b061000080591800490100d4416000050600410700070b00b200c1440381400303880642e4036034080c88065800200000214024034501042081626868401ca0303010702e0030060300c46006113030008450406820076420720404e099031200140c60281c403103920094140b8003607200c95950000c15152068000005d21850000c800c01c038074042d8903150351102e00750880d501ca21541c000018040c100305010446030340c0100802080c020400c0d000c0383c0d07030f801421501c1102c4106075079498001c99500207402c044006a1140e083c861025840000c0f070f40c0c1c05032000d051602d9945031040d060f0103500030b0000100508401031500264000c188405030010703002030159140340c00c4200041c0700408100d03503d64880c3c280d8030700700b501c00e040c464032b190310610040700182400d9040c208007030600104440b1800410034251201c07465a100c000c058802044200240c6440d05a2182040140c40441c8c41200388203103040300b0801c61402840302034084980c1c1341007a0540798130700d038021070191203104941d46900 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 978895728 1250 978894478 978894481
    0x7030204291c0e06180307030305042a0906060e010c0311070e090304052d010c080708040e0a182103020706021303050d0908120c0f0d030501080c09010806010923 71
    0x102c04540142070101510303820f98905669000c0403003101d440c981c4405085610a208540001b8020350255820901401d0704c043c1401007120380e2002200c034070305010381d84030107040304002507510350190b01e015150b6418101181010f45000808010010340301608000303a8200702c0d02650418401000a4050010403050341c0c54900c500c50350b08e0b845481018001c1c00100c4028203070707070454a5015040c40c80d100c6000780c1e583c483d800440700c1501c2603100740c0c3c41c48020410b1000080007800140300611603144e00c2d02207490180006c2049501602c0d59020100c0c1001c3c071000004c004003590005092038504001307803255943c04c100d0082c00344d02c40c000d00043c8001610054803204070030403400c981c440c0048450080c0a200220390078411446a02d003103500071584010480e84001c05424941e40e82c40495200300c2d12203101c98a02000702c56000c011a84e14001400551018004203205000980700d45089500d4001030641d608414461307204155503600554040549003105000c440b05030901c82d4000703 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 978896978 1250 978895728 978895777
    0xa0509040c03020901110c090a091a151c23010207050a05030304020f01170c0a050d05100e07020d090905090a1209140a0e061201150308120703020429 66
    0x251321600b000d501090790915040e11151000481e055090700c0603052520584440108902501d0050340407101401c1049404d018841c42c5108544118042b0342d80648180d07011090040119000c0c0800000c8d081916090f07020840600750007403900c5c40780703641c101d41600010189009005130318006065009009001c02400030000255001e54000c0b6070240000c0700b59001076030a64689250207583d6242030780043c942005d842d01030802840c0e40d0802d90326100342c020181003120000c840001c8108540ba0050021f003243c12006a4040041d00085c9520b03804054054808001d034810362140581300d00020351000f00601640004d00d034016920030740340b560110080c2580c1007501034a1660b0206101c55001c620b02101300008944403d0b035900c10503180c00c014081c10f14200c1980200c2e81d92142c45a5800001c140020380056001d5031f10300b03031650b00c1030140b080d40d88800340c030340700815005110501102e2a074125030403c0080407c41c03d0607140c44010070100318040c02c405100c042c00c141015a91 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 978898228 1250 978896978 978896981
    0x30705150d05060607030f030f0f0e03070b160c06110c0f0708250603180c060504080c040c080c0304030c061103091e030306060d0f050112030908210a0509040c03 71
    0x12071148070240031541c0c600b801c0c412903020320b60002e80062048107100050500a903c441c5d00040c00c000301181d208840400c1009680072814466075503030001075000c06003d01e6078071254200082c0e403849840b80402480c0182500d84201c80540440d564a8824a03051210401c03580b514080c030080c0e5106011000c2200d07264046480350304080e000b00c00310013a01203024011041c1050520380340308909400c003d0304900500004005540540d40ca40001c0081503410480d08020407040e5940340d9120300340b00d41181890900d00c50580503505211013021611b400a9423154084005030b1003c0d00c0f60744604044400b03440030000600032070f281403080b112206c1a07800551080142004483c101e48281c044688001982151800190400d101040051400c00018180380040800205400d50949210703030413107000382d02c400000050584a0420160003441d0107008024074405009140d0980661140c02c1140c0300407118000000940301f000203003e4020b44841c140003610400075042010000340 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 978899478 1250 978898228 978898237
    0x60306050c04031202190b0a0b0d0620180603040516121e0507090e150a0b09090a0b0106050a0c12090801290f04270c15050a0e03070515 60
    0x32032190034810138502150000914800101081c11400e80303001a6451b01d051104002e030800007581c0e26072000340d200f640d9515030b10707501502400001400a0070004258800801c0560140c66140c0510a580074101080304a0180c0041a42c0140d070781c0d039441c80d0503814001050011202c48400c00c4001c10752686001c038a51659205a2041c010fa0000501380c14503ca81d02d10010420740c04040705101c40b0740140c00846400404500311800d040300c512048020000448d49290550382e03030340d112032461601100e0b44e9088404200982107405007038907082c4000d8014007504043c04000034040364035074819845008a250001e03503000c5280030251004000744501c1c490381c0340c1c079820034030070603510300800070035442c1c184100d59494613802c0441e0500c004d400000b400c0d1940240d80d40040610100300080f246189411404890000b803241d2800020000d0280c000743c40c2007000d40407020500da002800c443c210081410b01007060649003000a2030101582c10468001c04046007462031303c0c800c0b20181 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 978900728 1250 978899478 978899483
    0xd1a0109090204050c0c0319050c0a03020f16030206030109020310120f1506080c0111030705070f170105070c061805100f0e0d02030313210c05100924060306050c0403 73
    0x18000e43d144e0075243c0145d80907480200410746c00401400d14031803114211082d803c80a42421803c2013180c40300c0b0f074180003514409402580002080040c000300c10f02020000c1006c50100011180c01c540106805000501446242c194000007003410801c40704403000060450180d10120280399140515100905034030840c0d00304020341b91030700c091140d40140d009881c0c0400040412401c00c0700112020030032a100030030030340420000000410003d0082ca4040d0185060100110b45031050101118209036140e109136494070050001a40e0f01c50500281540c00c200045068840550415403428240c18000c00303c0c800c0c3c018150301c0d28103a8006400300650500200f00e8011060000d41d110b0210108010050b0001c10019011400712012800440e01494200015074034490030b8001803101075202d400400c440c0084079041003020880030a144600da1814801c030940c0d5500c00c04030b482d141002d4829903004209070114418280d0003180116000306050055082c002c01c9251181d100c2e0009 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 978901978 1250 978900728 978900731
    0x8010603080d0f090809060f0c010c020705090f04031407060b0a03230c0303030106030e0703060c08010f1401020a030e0103020f0d050603010b1c03050915070b070f0306080a020d1a0109090204 84
    0x5600c100c00052090100c1035400041d080d05c6c10f1040e404008455000c101690a0140103004244180c10244200c6c50482c1c0250001e108080c1007604010300c50000a1000b031929040604010000364001421115862000c4402d51035040c01c3c503007803001e00380103c48650400f041200c000184002c0c032182c9001e44203581c1c84009200c40c0000c107240c450f948000c031503030035074403c100400c500c502c0b0b0340c000d1a1510400c0c0c1900c485544aa40303800075a80880d0000002540d0f0350f0040c02440007401944006082e203031103070a130303c0c440c500002c2e403688822003019040c440f02d4404e589441c4d01a03011550851840340040d662003880c0c03d2000300400e0161103150007503280c4450002103007441482803d408141000020745090203135011111907200490440d00081e4021441d0283c48440d4040c040740b610500c029150782c608080300a28001070f000a0b0000c050510404010200c40412901d4400c1d80548454069284906102c1c107900b00750708451a800102c8400040c80c4880e51b4802c03681c25200b00c80 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 978903228 1250 978901978 978901991
    0x305040201140a02010b04060504090503030c09120f1c08010501170907081515100507060209030102120103060509010c090f0e0c0f22080c090604020306010309020301020d091a040308010b0a0908010603080d 90
    0x3440102c40e1078bc0c00003130165200300046040d0308007072400f901081c0c40040000c0c0c49401d0310284941003607905d181c4c5105550185404c9014003400b6030300900c1c83c400a00d03089940b5850000000d00d441440ea18a6a200345104045081010300344114405418400c00311885051340e2081242100400c444140e000680c1c0a16000720b817400b088240401000c507135942d41000f0310b9894081c000c0d444610310503412740d4204200d2501801c4c0308211760085024050003c5c80c0e02d40180603500751201d1000200400038111003c0c40f1100700e007001c541c140d0b410000010a10703580e01c111521140701d01e81d0701016807103000c03030560500ca4040000b0140306202c1e40c80100381507546c030240c99950003000b0003103612641c0c01c00051090305055001c1c5a000c0e00514021a400ca03440d00403d08a90100c0c3d1142c541503150300484007070280500c6500403440e61144c0d041c0081c070b00b03600d0040403145d06000d5140100e20003d45410400e11880e2001d014044801c002c104013541da1402900980c000043c40d01300d81d08028 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 978904478 1250 978903228 978903239
    0x150e0f16030c05210105010e04030e03060105033403050c011e02100c05071b05040e030910320414041802040e031210030317070f0305040201140a02010b0406 69
    0x1180c0d404896218100d188000d09080400c1149881403a2200c06940c41c0811600315100901460307000301700403640d00100c0d04081c1802820400c0c0d070401107010307600c09c85c010400e81d200000ca03038030190102c801050800c3c0c40d4485002c800701618222800440032250003205020002c924001e178100240c0320800c2101034101540c44900c03d0121a07005a085101010011041a003150345500810300d0170500c1e1500503070303075900100c10b40000c9600780584440140001d080c03c0c4138021000002e00e0045040070280d000180d44e20600342e00044c1041030070800c0240361041c0d516410710010034400c0e0179045020004202540d80c0041c85107010041a8101545080c1844d01c94000d4000d0341e000c09800e000d03415001c0c04090300005075145050f12040003401c61291468810b175024009032000c403001c071407860400425004c11040174102400d8040148020035402c42e8080c91240c0b07040c2408580d0b6901c5000585058002d01d51000341c5400001c1c0b14a211030341075020303043d40881200e00b084015142c4 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 978905728 1250 978904478 978904513
    0x3060f04060b21010312080612030a08010311030109050304120c03241b05030402041a120703020f03010c120f18081315120f0603081b102304150e0f 65
    0x20300c0003800301e0114211b0304907090710890380c05501101c007900a5588008844000b8503543c0501812000181504014000c000e9883c59a4101c0d650031002840302c0051915a540c41e449140328241000b0f080000c101c041148090b07550005580140b0a42449800d80303258105c004070044000440b94030304215030b581110f10b10301101c40c542c003903a981415903441da8240030040c0121000c0425a0f040303404c200c41560fa41420345800c1000e1079001d055a60710b18818480f08401c4400d0f0345100380d05041419008a502c40c04d002168010907001107584829828458014a160100d501000000050540901c00d400000300360405103005031400980d51904040c0c04072a40040000024903000e00e03100484200d81c11107000320b01c125070009482c9a80c0c2c1e852103070139407105000084186044905003400d400034008550380003d49101032059480802c02d5800c10f1246005130f04c00d00d40c0c11070114061025074100c04480c1c0c0c1420070100402d031031212900c0da464030340b604248103e100d0b60036100740d0348124 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 978906978 1250 978905728 978905731
    0x1060b03270615010810051e03060a050c0307140c030d0e06100614071a0901060f090515010507030e150309010c031a0f130501031506050102190803060f04060b21 71
    0x41141400050151001102c20417409402d81c001031851001c0803c0030358844d143d0104858800c81021402c04c188404e05091000041c0140f44042ca00340821820307450450440764498110315101019507049020a5040e00407007080881c0c5120201c4c498a00d124141d00c2003140e05007010840314241c3e940740720601510090f000f1f860000f0408100da1941d01c0c03550000d0805a44501c1c4803412800d200e44500c280d003041102d4a50725a134503142d04110404400b5180809070008260a21003460301c030f984160f42c40c0e6403c1000e8100600003503d40181845800c04000102d4010704e48000c0428502c884c0040d60429141403403e9481c00003039045507800f0f40b0501004150121184400e0200f030402c002c1d40d14580c40c42c4a80007112108010860801d034401c4a0103184910802c0324800100020a011120300b5003000d0b05643c8034084903041410318200d1030740882d5004004030354035550038012a000c6101c0d50380045d00542020004101101c0c80406406a03c003824114641c0c0b140c8510300a0040c1030 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 978908228 1250 978906978 978906991
    0x1e02010e01120e010e03090a120503070b04060b0904060b0109080a2120010606020712020603281806360204090f2102030c030a0e0301060b032706 64
    0x90300030052095004484440740805074400015446a84401560a4400c031403104a96134100140d404128507045001c0800b03841d022a0f9201117441c40c0ea0341d01d82d2441081406484078458a000a04121390341c2c00030405418060070650031424140ba10030043e106002c0203a020032031031140403e980b180081d00040c1c05801c074400b1900f90002c241211889442d01d00c220040201072080f190b03207a103240c04140e403100300031341c00051541d152100003400c007039440c1c210b103500310300100108015954810130f03641c02c03001c5c0140c90b6513070420414040c0d003141e10244510001a08107030a945950052503040300405004100500226803d0ba082c240c028640c00c102131114616210cc0e180104010001d00400c288040c10014450104e1380300d030010744240e9001222194040325089203d220185280c81c400d141900046051450100751203490740120108042041030740600311030140c0e000d4124400502d07080481c4c0740e40e81041e076070400d4602074900781a0038000080845043c0e2000004d4028840e45 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 978909478 1250 978908228 978908237
    0x30102161a011719021203040b0c060906133c050c060721210203010306180203030301050d080f070c0806090d0f1407060c020c032803210203070504031e0201 69
    0xf40140d01e9441030781013410b800d0f0b800c94a40c000350000080204010406860a13607000d58a90120500d07092400c00014000ba00d00d801071010300c070f01c10345c10105410b850713503020082104140c07094007400c00c2e100440007070346c2070300c000e100801441d40714203070040c0d51032801001680c104030041c1c1d080c8191480fa80c48001c100702205564541c00c0d0b220000a041144064601540d00101d10301c0c81000d00311914001d1030300c1c00d50000041040007200c0c070074500c443d92900c503180070002d8250000380d2240814803855000340e0324900c4c00304c2000003060071141d904011402c481d49590a9090008d101042c0f40900ba1031442480003089140f0340019920358683c00c02e954010b0b401180a504441d00143c080c1841c080b58014000d400000e030701402450602e001a134002d08482d2034150805d0324100b0044804040000d0f400301403800c0c251002c148003101c4d41c1508240c60710403000f4038a011450740600580038064408002c3c006002d030701030024001c4a02803141940c46080c4200c0c14082642105c4000340030a = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 978910728 1250 978909478 978909493
    0xf0c1b020f0118081c031415041d1207030315080d0e0a08030c0c091b03040602090316081501090507020c040b03070b0a08180a020a06050702030102161a0117 69
    0x42d0310603c040201e208190146038500c6036511000391500d00903084901030003454180c622091a8507201c0d0720340c5040480140d14a40c00c2801c00d21f61040d10b50b0101074040c0d0b0310b50a0321110702800c1c100c1d043c110b03034000d000c8401d1054024010300c031a400c1138404600081c2404000b604440b1010040f1040d180e1900107010002030308841a9035a0b0405240c29810107050080050a200140041d1120b882d04101900060341c0b00030811003d0702c3c1c001d10102c03124a545034020b4110071510b080d00da200d03030702440040c0d44804d94030000340b43c000301c500b11072010750402c100412019404200b0300090001c6460005440e62110140ca090720012103c10300164031412010040e4905a040386810301d4015098451051b100d41000300d50b9400014628080780000003404810385c045211142c03c000b61502030503000c6120f500045500010b40b050008101012640703009540d0f080d030413114640c8416a01d08502c00f0741d490300580d84070170142d205104c442d0f034030000540c20403100c0134080030340110340190510 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 978911978 1250 978910728 978910759
    0x8070e0c03130611071a070807020a0b0c040f03050f01060e0609130c0b27040b06070209100b120103030e01080108061306021306020a050d031a040e030903010f0c1b02 73
    0x1480000c0b03200f90341c01603e5134a8000001343c1e41c4004d100c228026105e55002452010240d80241c2003d0071202c208000c207010042010340c0401c2904600c0e501c1482c0084a45911084400d42e006a8000300c00450ba5a02d000081180018202d0001c07000c4030000d1191a03650341e5600c052010898409401895000001300500009030450515520400340e5615454483d007071400d00e1340004103030300340c8941550003124900d948010880302a032402c40e800e20a103c0b004000c10410301440300001d00980500c0d000c52411500c46440601801c0086401a01e41c801c0c412614160f4000b80700960105055020040c43e5505c190301860584a43c031340140b16544071890821000030040d20103450187c2d0070300000422402441003003000708601d600904000840c1d051190900c12041c0204042c1450500c21007031940202d28186481074088a0003d00c240d026181c40e400d5200c1c2a1095605501e08515221607030030f25480400903200a640f100003015001250300709034123110b41d0103540801c1148001c0c10 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 978913228 1250 978911978 978912001
    0x10180b04272705031c0e010e0c030a031b05190605010e040f02060c0c0a080c100918020715090302060708060a0509060f03070302150909070906050327120408070e0c03 73
    0x10304520483c1102d2411141c000c1280100610054000400d5200c0c4107014244109015500c41c489040d00a46030100441c800a5955806c18000505001c055410003940b8480c07516145030054000c000c2c1c480f0361040b5071010b141c00d2900c0604681c0c00345080c1c004291003d0343c0c02454840c1d0350001c41c0440003c9550204852a013010515000d9841441019200d64940d100b42c5002862003400074042219003108015100001d492903008004018401b00600e03441c41e401e05041c5090820010b0365000c1a041c444044000c52490016103400c010140c01015400120a8406c40d0310340c0c0c81039101d49a00c410045c03561254440c00e9444418803021544070314054141c900d20101c001c049581841e5681c0c00f02d0001082c011144200500200300842d081c2419050903034000c00741c2c40d2041500d130408002030240c0c00301030030780414080b00d00c000103101b0303e0301c06070000c622114a040b00c0d4140a05103441e0300d50352281c05420800d01940030002400058106030340d00601200c41d6450955854019144 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 978914478 1250 978913228 978913301
    0x5060901080c0f07150c03020307020a030e1f050307030510060c02090a0e01050906040611040e130c080f0d0e030303010f121e030e040b0d0210180b0427 67
    0x1105103000300300e43c000120b00301006180441c42405c682c200000341c402140229101d00e5908400d00d40100108180e4503030102c1c004034003a915042a0400410140101d50054068441201903008884500700d001e504400030394820006550300f0b115036928450b040a9541980c46003102068140c40804018a4241421540129240e20025200114020301802d641d001e40e03940c5800d8002000744000d005030760068086140d0b00c0421907242514040c041e00150000034070084c10130007098080ca041003031611642c40188002005c075094840701c50001e40d210300c0c1010b0140c01080240e020f8140c41d00300881a01c1c12a030241a0700d0300403901e07090031440c0745e503503221048401a03509034100d450045138003110040da5029650f400e81c5100c80344280011a0b5901c401c4610640c0c0f544142c1005039142d032402004044d052600c1401007406100b03130f408000c4150003a12103030001007804120111089440501d410980507100307074195511800104452000480a4414042c100304403d1091a401c448 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 978915728 1250 978914478 978914491
    0xf042109261203061801081c020309041406180411010e01120c090509010b0c1e10050405030702180c0d020901090305010c0c152706201e040506090108 66
    0x40d039092600708a08103040c0d030b1000100c0c250040140b040c0e50a00c98195000b141003041803180315410b000036182c1d624001c40443c0200c0b900b01b0f060b441e42030300c28401e03070350040c10107402070280300c520300900b558403030040700e541e405140d14150035400b804510380114025038001c40070864078810313003004442c82040380441d203041c0a6008071800b07881e0001e00c140b00341201c030303990396208050410b402c10006207411b038041a0794035400c1c01b065010510100360101d080a01030302c00315400302041c40c00780c2003407107100340c0011082c03406d810030060080c00300007408580d00c02c5030032504030020007180b1044540280d4080403510303001e1001200c002500d85c0108004031050500d51005a5a50b07a12400d42d99440805400101c408814004000d80b29080c5039010075007010500049071500e036200700f02a1414092032031084681c5408080c051640e0041501e10340301102003048640781d1144e13420b1648208003e140070400c44441109064031a002d55055400042c4121724010b082401142e080f00050480c = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 978916978 1250 978915728 978915779
    0xc051c09030e06190810140d1401020c03040806061002070b070503070c08030c07150507020103020d0b0406080604030e03060106050f0c151503060f0103020105031812030f042109 78
    0x2510483d51408082c0c2801503161800c412900900b02008012940c0900201c1604d41e00e41c80502c04a451124000e801076429a07898010141e07a04220300801e034070382d2825681d03520004451002c14800300082007903408003011101035490b1b0406220124800c01140300c0140c002c41000e100b03000106005140e03c602950171070703003860030315210320710020f540c6c1e44020030680c400115034580000505c0031000a0681d2106100200013100d4041d140d07204103100207040541c0010b958003640c1c101c1c3e00c000c0d10b03824080e00030030445440d040072580d00c85041e60282c01080e400b0b0b450032400c0c0390008000b41a951151356039810328482e154200d0a035080101d071008580200ba000320000c2c40b422203807600c07541ca00c603007821031a840c1c04c060504006014024924000720300c0010b102507600a01101d40147c071038584946252907161185040814100c070b4980c2194001051003002c403910f084842c045c0d0300556410842e1b640b14483c0d204c06a202210600c040356120004010800c0300340715024483c941e00c0f08 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 978918228 1250 978916978 978916997
    0x40c09051e0f102f160b0d110705010203270a020f0f010531091401060e0303120403091508061516020312040609050a06090b0a0e06070c0303030c051c0903 68
    0x1081c42d44c21242d580341c1c2c6503a0030303075190114210300403c100004015803607504011503003000e450074403038454581008501c41c1c4811000803440320b80403c454a6542000086403642040b1440e0000e03c2e0703804c00002c400d03845a0300421100100800c5034004141d00400140030014260103000030307030303600103c900e0501034207001d8007140c031505c43c0c0514446000090115101c000c200a03055468080e500204505031034042c1c8007441e0707125145010705407407041c103009840050100000c1c2ca948255014001500c49401c2030004154000d031644060322614000741000d0480008200c58550b82154190f0740700040340c2d1150103052038800200404105840d010b80303c8006500800d29010754451840c0141000040c00c0000550111b140c0c0090281107a45124443c81c200004042a0a501490b003880350001044016680502c2c03244162060140a041d20741c0202e08102e0119842032000380d01103410404070710201803241c400c0301c0100c2000341054481d00324414038880107201c5464110140b01d103084 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 978919478 1250 978918228 978918257
    0x1321060f0603031b02031b0607150504051504110111030d020412060506042d02041214060a060b1b0c040e0a030e010203033102040c09051e0f10 63
    0x34040c0c0300c4905400426441d166140060012541d04910708086242141030001070380d01280000e001d0380903418513600f4050600028159100f4202c2c000c0c000b401d0091441c0c02201150001c41c1f0450140003a80e003280d00081444035203200441d4020021040c00e01d211002d5801384a54002d203442807000c03641845050035580040f80e200750402c80324400001124000c1000074050700c1d5000c80c0c02d560901c0282c0c040d85065591501c0f000b4044000301c0e40d0401860107640c181d040d100205000d508081240c10b030741c10281e15100304034440e03803014001c50002441f01129400361008680210068500c1d21138030b12001c0381200d03900392001c8424062203ca1409540d59402600c1440c0e00d40d0002e0119038081c0d24020740112020841c20741590400d0080184180801034a00403900781361084401d2040700d42d041a0b08013403039000017944113180000005440c0e0f0700880c29010740f2007d54240f0300f00c200e20314807003414809900501d50b01c00b40f550403100c218100501010705064280c14061001a81903 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 978920728 1250 978919478 978919481
    0xb0409050405120d0b13110a1409030118051605150d0e070b12090a032f100c020106050d121b211e090302100c170d11132106 55
    0x203400035034449032203445d42d00c094a841c1010344444640b054003003011505a41540c2d0017030282003407110500c223410340b0940e4803158500841d8040388005008100200c1d403201c035109040d84040f400c3c0c503144203c08287d22034030f1100030031209664004009480c82c0c1403102d000a072645c4048130303a006003500ca61000b14044401c020b068084c00c086101b16480b0b448240134151602e0009150b0843da5020f00300103004660000e4182c10001d10900d22042403600c010350038000a00ca0261341582441501404203200340303542d010f4070940310326034028000240e540c400c10018007049072002e072143c4002020040214007603114140d081c04107a21091450314551503c02c13814a0391911030064940c42c44103031107090340c025802001c0005c64041852000d92000d40201124410f00009004280c103034203440b82140240304103401c0070303072203070a00340740400604103030070ba46c1c10104c580c841003070820311109110b800c92001d0302c002c03020b075000e4500494a44084a04803142421001c001c8050b00fa16000c0811b03404d = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 978921978 1250 978920728 978920737
    0x30c0803071101050301030b0105090406060503030c1005010909021804050f060c13270e120a020a0b010b0c06070e040605060703020309030c0f0607030305060402120403020a050607090b040905040512 87
    0x1088055034840d641d9040500c1c00003100004641000b90410040c0b00041c14400e026040d14019541030030f159503a8a00803008242030f810081d45807101262156106c14001a4071070300061800061007141d9031001800700b44e5030101c0780250b01c0f030300700c00304c86410759420104940e1150050b011031b18554080600f05081180c141c6041e098071200045c2c110b54409070b04d50600007048120880c07461001c010f07181c4400085c3d0110f202251945400c48003c25070010401d030491b00044084580d914030ba054406503a0312064201281d94650400000688031648400d441c0c040c2031032000b8040726910b00004450b5000703071610203a8801e5542d2030106464a503400508086881b9400039591640d0341401c2518000c1100001d503c201a1516040150b843d1f034000c0da41100d0303142c200400c440d219280007401078001c40c07000380c001d03405200400080c9030703000400c0302040b4000d00640341503850301c2c80d0032a0303400103c0c00307030003003041c0c080008000c0782210703a2020317610502030b4050310240c080c85001001503600 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 978923228 1250 978921978 978921989
    0x41112101707090e060705040b0d090b1e01050607230708060103240e031b03070f08041a0a050403020f010509040606020f010c02210912060f0a050c090102060103020f0a030c 76
    0x11680c2d09000c3e00714248200d034903050f450300091480d4900050001d0280c4207a0160a06000012404201131059034004062041e4071400a155a00e40360355400b498403051a82e030303061000240300000d41400c2c80811078065a070040020b075003240c0b00c0e4009603646800c04010101610603c44001106002480503034003030f41c0300e42400d40c210400c80240078040c1a194000007540351510001d414695000011107203135200300213800100b2525050100c1c114016800090310048030a072091080014000c014401c4c0c4500c0c2c0c100c408050040ca1119a050281f1009100400d404100601c05840c10241e42d40240703c051400318500201c600101e415907042d907005c100941c2c00300f07000d01803c00c420300400752012102c1c40245020035641c101000b0f101d885d1504010007030300c00250204207407110740400b22591030b44400c8403120704000103403440c10032040350861001407420f4081640340841030110760f810300c1c0590003031035207034255000c0021402900d80c4060341b1035400400000029a40d82c02c1c40c00518 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 978924478 1250 978923228 978923233
    0x906030304090513060608240a110301120507060824062a0c0d0201050403060e0309030703031d0d021f050c0d23070b130c050a0e150411121017 63
    0x942c91a041d4240d075641c6e000701e60315401503078031010b034844109030340d1201c0e00b602c1880c520703143c403810409c100030051180e41c800201c00000003c03415140900c40c001c52503208008451701c082d40c0d200f080301c2081054070135030500070181443c3c6041c401d410040d44800d04006140614058505201e045108080d01040c1c5081c100f640c9a0451801c0c1800400a0346100b6140c50b4000130302540004d00d244100d00008220598032900e0300200c0004200341c880d0307002c000c1c040b198015140e090142c5010301c4c41305604c03a003240304c4180203441c2c1085d03160003042642c0980003c03040485884200340a488200c5044e0421809200c504440201041004004801e5407103461900d54604001d02c1c0e8001d1040c654003c09904100101c00111070201c81540200304840b5207503610100e2070b00e006903c1159100a610002d51030011603000c4402ca0142d0044c41c2d496903032004801d80304113006c140c3e2000e80000d40000014060910240f14070014540d2100c7c06982181c1032640b103c00d02290b03880d0841c0b501c882e55 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 978925728 1250 978924478 978924511
    0x109140f0d2123130506031305010e0d090e07020a020a1202030f0a0206030601110c13020d0b030a0510180510050f0907120f0f0b2401140909060303040905 68
    0x116035040105038040940c90051030b100340f0640250000f100407510b4600080000864001d144054200b04c00582001132019a030f070f0034181d100c140030500402c0152803c0d4a0800c0c110340346400040e03159113504140e1100082c0900d0120b0540e04510002c4c03500c000d60082040400042c4c2d10091180064046007904042d40305d418010315150003a19040c0c004161b0022140700090b907114000c0d03079030125007441d00840fa1000f80b10ba2508100d400918030742c20140c007060340c5108a520350007500a21000c0c034002c000650f80c400c1052768844998038080e24640010032480040344072500f0600c006443d035120709c9603408141d60750601d02202500340000040d0785d42e05000b0000f41c513003800b40d0404690001030900d5803c100c1c4e102c40c5022a10002040b540c02201e5540070084038405280c040780c3c11a10f03144451030a00c071000d4007070003145401201079260010031440e0350b0080220800304801d40780c0040c1000858820301020500242c01c19916100c14400040d25100b00d0080354820341040c215032914 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 978926978 1250 978925728 978925763
    0x11101b02060408221502061602030a200a0c0306060602120f04050f1309050105040318060e0603071407080d20071203020d061d150109140f0d 62
    0x1010880108000c5401c000d003030201150a00d415038480740204000d00800c40c914480b4010341d1000d641c01800002084c000c1c41da01c2c00d802041d264418044183d815690302c1c40c1c88400ca072640b2810481c1404943c02e400c0c1d015042030394501c585001130131070301101e001c072940e40c40340c651803401a0300c21144a91205028407019504ac00403a9507010304003891424840310380103020450141b1701486008880051856605565009400b4100c21016004024035501400d2590180004031000d501150003030b08a21b41c0002840c28000840fa515540c8580c41110b56080200390390014104004000246011011460b0304800030002a442510f00d03654480d8001340c50001d030b541c00f00c580e1b90000c0c000c0d800d01d00c40507152402c99000d2948800340c040e07518102d041c1500280540b4a0440003149485404143d03005040c0c0d0703c141610002c0e1076031050350340740c0141010094440344598002003201600f0002800007400da842038031001400c00b80504109808202100050101614071409401502c0e00 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 978928228 1250 978926978 978927011
    0xa050a0507060525050a0204051302030c0625290118021204060c090f15021603020d02010c0501020d110d1802101b020406080102070c2408071110 64
    0x24081400c1071030604d604901080102e50928103414959445241d0ba1400c2210038000448000d5004004021600740003a07040080c241591040703000380f05001d901919842e048094031030720424007846541e81c205903025a940032907a903004484c90150005110103404500c0280c5c415002410302a034072940c540454100d0341031041150384e03030543c41002598944d0800b107280c10391080c1c01000c08900044200000c441403501d0341d220890142e10850041140c0c005480c20440307045d80d580c00c56a00552499a5614034021880b0081d440404910140b0055000340c812061040c06540014200083c1d02480b20541c0e40d038001258010f9400103541881c3d00d0544941030f0071680054003022110600d5020510340000b0003410014004011038581d10f030801042007084090307000d4000c2c8201d90761a420306010707404c03040089403500c00b00c1e24003242180140301ca41581500e400318680c420006030509031100c940142c00c0d182000400003602c4c04101e0100f002400c00c40361003a002807040343c2c03404080c0 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 978929478 1250 978928228 978928243
    0x10030c020d090501050a201b040f021303020d03051204060b011403040c0504050a06050a080307020103050c070302060c16051606030c05040501080c0f091011070b070807030e010e030a050a05 83
    0x6090104160b41404607907440019a81036203140d0030b2520404880b2450f450040384519080340c1f00c0e12030440c12007032a0300561520301c4c4506060700c003070101390040308000013640a4082088414a84540100007600c0d240791030500c404d001c0e0034128505180c0300c3d80c1c1d86e12104d044a041c2c514945440070350807256441113042e40c00c0c0c04604032060070b40c1026030f40e003c907020f841d21902d03108036260b9022407045c0e2030540c010070080900400d4a42c0c4540c1d9151100d072250094481030307000c28500b0001603074202c0b0030021540e0259141d80580744035911050300142c1a00019a8842208400c9190f130000810401880d01c0c0a0350b401c40d0b10308110324000d802000d44080d44116410490b0910042065980042c00c0c1a00030400100650f01d0f90f00394a181c0b620f43c080c8504246c0c0c0944482100c11044d50842c800020440c006c1d41551800da44a042101c2c2a100d50080200010000c10040c80400d1141e00100200e00c414900804000f03001c0000901c1c201202106403401d412005442c010001d0802880 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 978930728 1250 978929478 978929503
    0xf0702061506160c05101713080409050c0d0905100f0b0a030206090301091a090c04060b0a030b150c0f151e070203040f230915060f04030210030c02 65
    0x1550520708000100307a09014004511001680c01d202032401c100b651003194001d81400360009500708210b000c000c0c07128030300c802ca10301301170b01400205200018201040c4c450076017041d005e07442c0511b40b0701c01c0c100a0030002c07c4a107045c0424004c1c00c0308068540500b200071400380009008d480103507030020080300c42d0f5251551146150001c00d401c3d03034442405a1003200c0c0c045540680380c0e41d000e004a40507000e944c0b401000004240307154100d00903205002401522000c04580702041d400d802c1c441101c10900900c0c800309820310000c00014402d420602d100306c0c014000d07418090041804440f240c01c03150f400307000c030380080b00781009551040101c100030200414924885041c9441450130310400400c008114401c10000281d0440c001c1084a00606a01c1064052555503900d0821002c10004411005607205040c42e019840c0491020307019806070402903034040b074400100051a40510314a221462080c0304c0000942c0c1c8008200360314419688000c42d800c28110002803c106443d00766 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 978931978 1250 978930728 978930751
    0x40e060d021c14060f10090203090c09070e0a0320090c3712061d07030e0114040b040c050108010b090d030e10120501080c1503070311030f070206 64
    0xd88025a4403404124144099501d405030201c020f8280426403d01800b642400d91184c40140105601c00b07481c0135106207500d00d0000051034a0714030007001d80c48266200071190703000b03903d191024600306201c1d58122040e8280840b400c032484000c90350303065181e801604c0344008450900c00a20410840110800d02209c41100918210b01c0d000b0b0301e8040c1c6a906902140c02010901400c41c44c80401411023468000100108054410080096102c01e007050019410168009001c61020b040000d004500803400003450b601c0d40d000b04c00526140e002e089886d900c4071907c02d0344a0180c451700d03010364041c0890607000e1402d4242a08100c11903402a07040107440c0340100041c1144400b9640050310898a00c03007080c0341410103c54040c0501d550507032140c1c0a1400425070360300031510182c981c0025200b408641e90311207026031100e010118007500800307120040b12000a2000041d640903000b07040c0000c0190590480020b6600f0880c0d001d6154610715003840306c8240c04202c07036a0300402d4540d0 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 978933228 1250 978931978 978931999
    0xb060901171903140706050603010f050721110f09041803021504060b06190207050a0510200a1a0906040f0b0406110d0c09120f0305181005040e06 64
    0x300c1942c0e1118036000c06442034440019804040c8110080c0076910600500540c8440e094180903004100c1624680c1c4603600c1c00202c40900307103081c000c0c5407080002c1d07118020420301d0300b44030b542c0004030354a0071901c00b13a0b42d500c5003004a0603007014001c1c11625001e00e41c0c941d420703001884100e90000d0301041c9141e811010040009600140e03007545605546a01d21ba252a18a00040907028100c2c13200c3d0300000114a145442400404c0c800180707600741e00b10b45580390350700188003148486000d000e402c0441c9550703040b0103c1c080d50395042e05805407421303807110f20710105169080100104040324005520b10100e160710144c900f20360b400000302d101801040c00d250b9100700321400002c500070280714855001a09110741382d8860700f0030341e603074100e42c5603130380e42e05110b500041c13640300b160001243d0955404121040042a03070700440d64017500101c14042203850079282074200e440d0610035100d64103003c4459031141c04005c070f2902640e8988030307162403c0c2490341150510082c10680611034211 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 978934478 1250 978933228 978933269
    0x6030115050a050705060726160f0c1b1806060f0f020307050a0804051e06072a09020a03110901021002221214061003110109030f0b060901 61
    0x82021012a80e050442d03891540500c19100c5000d0228060624000d01c006c1018040d0800800031640900080c1040e102e1300500c8192100b5409a41d100c1c1540d810307050010f0154007480d200250828035040141c42004141c0d039010100c854140b4086404003101da0400503000ca00100c20341d000e0741c0c03031b805101c418200000141072038039603010f00d0104886888900d031740358021b00441d440c440d003290a441800e401030410450365030142c800d041c01140114a1546c440b4400c0480081d148401013180340b901178103807103002d183c241424000c3c05440304080e010b60700c00d0100507054018402c03620f02603180c072104c0c0d8015040310024034014641400c00c000015203680c3c0400c010313000d02c801c444016150011180842c1d10b03c03146020321004400400c002149045001422003000ca01c10908070701c0280010342c8240d1030b08400d5900c40270884e0111818400580c204506480f03001041c5441074480780d683d226142010550502a6500c1c218002400703000e04040400c00c0c054041c0d03240542400c14040c = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 978935728 1250 978934478 978934499
    0x9040b090108300a0f0e0f09010e0408190206060a0e041e05010b042d1404173f0613020d0905011b0e012d0e0924060301 53
    0x1d480589000d0800f85200d00081e105044036012036114501c0181c0b42c4400100160100200101400100345005042940d502d0103482112503018054290741d42c69203004c841511809000c4c008461451003405511a071240d10700c07003100c61803c0350b0300604132030502d201070007205e200503044100d00c10011340401001c2582002c3c00b034840300252061018505031403c10b00e0050454884107079100b82401c0140300d8001640e010485c02070503c0c088002d085001c03c5002089370686140303254a2802307080040c02065104d014034511014100c2028035003980308028680380c0400c0141070440300142c2c042107401c003001494449a10042c40c3c0300009c0ca04022000420080c0403004401c0a0b40c0c0000c4d03044856009034001d990303610760182c028419038a4620308819883ca00c03030b014900140300b0340507030700c8907602c103805d01e03581010201da0080b64200d4403407280c04030070720045510b41440802548075410f5120a04030b584203c0080c5545040040645810710901449a20b04c1d846600c0620040c020790340c81 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 978936978 1250 978935728 978935743
    0x40908030103020f010c061e140709060f210f0e0a03080c07050f060708040b090105011217070b0a0b0102100504020f190e0405070510111f0e0a0809040b090108 70
    0x4403510309921181d131004a0b203c00040c81d00a004506040a40e284030305090a007045000303071280203100c0c00c81c4e40213941c1140704c0c080306d0170000030f44500c7c0200301403030049a5017000c080c0c252501c0c0c00303a000e100318582d1450480c0760550600c00e9071452000781c010014440d00c400780c0c841d00d010341044116510001e166080242400e803404d04005403903403c0010400c00e041000c08070209403041450b01d104060080d1400b1602603c111141100050b0038110610a25041c2d1305200d141504800e8075032613002c48070b058084000000c4100300614004541807040080c4208401500881d5010030380d8002400c00010640c0301099a04107800d0000680c0d500380d0822480e5420f0768241301d4007101301110010100558030904445103a139091100303100020424005551050b140155501d1804c00200c4410440d801d00c940a40c03c51b10618013440d60400000720b40d05018070010520780c001d003410a06000070704d401290300c43c000003076040b1036082501480e12601021a04513443d98900030449888121 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 978938228 1250 978936978 978936983
    0x30e1c050c010b0d12080f040f03120e06150a0b0405091303020a0219090615080f06060405040606080604050a060f061407060203090a15020c10020903070b27040908030103 75
    0x4101014407800941c46030401d144001d11000110540d41000300450f51900368040002e410740000584400c113030100c20340a140d101c841c14580b0202a00c0803180c1406416450f05c110380c0320500031825240410810f4007480c590450650707000002700400007400350301d50044111060500c410422652800d1055902041500003610141e100e494100d00300307034980740300950141100b10440260174651034010700740e070101d40c020440c0640354210a024004400c2e084400254854009554044409240c0b0b40010019100c0ca05140d160b0000900341c0304240c004100052800c8200100b6250034025980c002d80d010404000f040c0c10000a078540d03901e070340100380500500c0e0241007540700c0c0c04d000300c03007901d500308038215128101090126115805d1101c241c66070041e401810900398058821540e600205800900b000008946620003940003800f0300d0341c1c54004c5a900044194518008007245005000d56040d9100581e00380d411020b0b0be0710f080b0303001d40e1520405c1c200248404048a0650341c = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 978939478 1250 978938228 978938237
    0x703050705010b063609070507030309080c2407230405150301090506030c0307140d151d0c0307030609020402090307150324060c0311010203070c03030e1c 68
    0xd110308007203001d041d40e16001070304500001811800d070441300d80b800c0c4500d0241d000018003c0900c2c1c0224002079041e001c00c503413005506001c03c045c50b005600614986219040124a0415907103448196130044000030000350050806030701100d000802d00c45000240c502a09064280010000c00c6041588104000c200a0075401603084c40c20f0000d450083c440248041114000e04071301d550396420a104201e0210709150119040b4500800e50302144c083c0540109410307440d2036800b80c0d4001d01e44003025040700842052070041031401100140c035140404001c582d034075030700e14504040320380204a414250001010b851155801080e044205d030781090021840d4825400004c000780301c0c7ca4440c90b41445240400180303c0c4007030803848903010268030200000d101d41c001c00880e062039a8451420040041400e0260302d00a007004125940249081404081c0c0c0d01185400c82c0e005a90000104080c0c3d100c00080560500070020304200741c2c1d015140110315002100d44080180e00c0e00f40501 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 978940728 1250 978939478 978939487
    0x1b04020a1106100509071d041a03060c0c0706050307090e0a0219030c08070903022d13090c0b18040914030a0518060307050d050c0405180a0c08010b070305 68
    0x34410420032600c025041c050b034507503041018954501428520855010354072a000040056004419220b1509050503808820312020420040200301d0b81e1080050002070080004907920200b00f1030b4425003aa00c082d56503209003910b000c2c038094481d8407420401c0380070400c1000083c1d0008561040380e20040300542541c489000c2440070b4024070b500e080c03801202200c142003081e07140d0050680b010b015202c0100540702c94404030b035001410300001e904146003100b6502180d03002a100c110211030701c91030082c01147c1400049011044244907007080340c50b40141c45c1030107a44490000200510204646040310b04154103d41801c40c0700484c2c071031940c903502e0606109080760503040b040300e600c0640c0daa401c2c5565024143d078201c1406545a640c0c0103941c50784074140340007100d0052074551541c90810001e41c0008000e0b00f001405003002c42c03001c1c0000642c07a1601c14008900c0c50845d841d42140e1310303040b0714800448410103220b0b81004109801040f03880c81c1241100c1145805152407a0f0700d = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 978941978 1250 978940728 978940747
    0x100f030504020414130b07030c14030417040f0807060c0b0610020f071e080d051e0d152408010605130e090c130c050d0b1801080f0d021b0402 62
    0x91400e400844c1d02e038081c8600f0070001110102d03004003407a1003105400c6403500d600d44100c080f113060011040100d0b40028000195040c441c0c06160b00070301c21852684816001c0c0d504c20a16003051b40200c90505089405000740703001807000340c011701568074003440132070380d50740310006102c0c0c018081134014440204625462031090000d1300c9034008410485055544c3d81c2500c0c28406070000c00761000c2c880c10540440c8490001c00d02c400c070802590740d89030034813013100c07000d151901e1802204074081d0001c100f000c010044500034032090300d00303585404008a2422510700140c50599180c00341200c070890650f050aa0840541410354865142c02901c0e03401500c11074a4480c0150040d000300708814081200a040021700c10b00c0810064800b10740c0e007214200c101080e65040d8411101007030742400f80700d20000607640540540c4500406905150009040c10406c02902303803c03122242d0000074090440c44420442507590202d684001c2000c007500a40e0700d10f102210f1954284580e8000407840d02 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 978943228 1250 978941978 978941981
    0x20a03021204080307020f0a05030304120c0606090b040f0219030c11010204150e060c150402040f0e060f091501050d05010e06070c0302010c08010b07061d16050f100f0305040204 78
    0x28121807418190751642080c0c10304081d10f820885a10f80144610010300c3e407003110126003400302c942d000f8000c504640751640e580c0421580c411018080240440141d070200d0024010030380200509040001c00c0343c03100061000b514001220b0300d220a0040200c08004c0e000403444100320005450001041444028120307000e2925041110141d8004a00490130849107802d01071036001c7c83d1510224041d4140c10321050b0b000e4078a00c031245030071a00d000c40c50a00014001c2c2c0d4801e00c010030008400c100144514210b5620312400101640200308010b05102440d485a03007080d125001440403000e800c0e03113083c412405005d418054400b8000c4001000800d401c00d4003242c006d081550b1041c60903080060407118490b03000d41c01513080500002c2c106003e6902d441c117070b40c0cac8002020310f03081c00394407007201408204a24280c1ca2801404440c030742d040034010302c1081414408000034a500d8038040103403e020103e0154441d003c1441911200744c0c000f4400388142159003404a069074541c0000760 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 978944478 1250 978943228 978943237
    0xf051501140d02240d0f1a15180a18020901080603010614011809020307120c03020a0c030e030f07140a0e06030604030c0c0f0e06011b1713090c0e01021b060d020a0302 73
    0x2003c03607007000644401b20300b41e41c02841c03081000700030074403060344030760108070b02c00d254420142e11345e43d410000341c101400c1120481b184008080c18003110250381d00440341005a800b0500380e0215801316191401d580d01074000b80e00030f04120000c0c0503030341c1400c05842c0542c1405842c0c50501801a190341400c5010301420001045050340841d180d10f0440000360800000c080410512850001c0d00c0044902034400e695995404c0ea5486a02001554042c2e40040e80f440ba00c503414429020f107203440c400200400c00280119011415150620109100e40c941d140c1c4c01c061100071442c0c0401686031400a041c07907102c2e07018604007120308401c0c10044441c1c015500200170000000c3d902046074102008503502952081e61540d41e01d100188038294180d100500051603214240500249120001c0182890110780907000d491070341d903a0000401c803503100d0882008282c0d00201c00780c0568042c0501ea1140d00c0d2103440003810700701300001511900c120000c05460550100e00044124400d505a4 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 978945728 1250 978944478 978944497
    0x20f10020c0106080a03020622050c040f0b040504060e1912051b030403050c1503090d030c030b18070305010803120105040f090f030c0512040812070f051501140d0224 73
    0x450b1012221b0400a494010848021143c0c01c500742d039506500700264124100e264110010b454030050707100401c0090801003600c2200031ba12500700009030703a158841d00d4003036403203030400281000305511140e092401041c095000d4803105921800801e0220012703058038040d41c03404d41d6440305c1c10702103528418a03080c1003c40c940300105001c000c00c00000740a4001c0482118000504d01c250354110100784401c4a04c400707250000b510121044d400f0760030a109044d10fa060200300616030f403011034414425a183e0403094000c50080c0081e5680600c2610f02404030302c0301075803805141468441c20000103110740e40c007942e42c03039225030b201e480c80b640043e40050303000d400c205c000344003800c000b00445c0c0d941c0002d850340e024031011242c1000a40e0101c03812500b02030b01400c01c2240780700040c0c0290b0031410059a6914540c0d040000098050080901e04802203c0e82d400c00e5041c000e43e81c90140f42100306602401d00c0b40d0040780540d5803400c1d1541d14101901c00481d0340c03101803044000707030b000b0000c85 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 978946978 1250 978945728 978945733
    0x1406090601170901050a1b0f080a0e2b0507120806030703080f071b062705092d1005040e2e050a05010308030c031b070f050d020f10020c010608 63
    0x280900003506405c40d03030103450740d040d060003503646240b840c40301909103d40318004204941800c40c4020700a4640c1a07002c0c00da6840000c1e0300c0c10085074181031400d480110714420000e040400e200c00045c0882c00c1304440945017032401c000e855980c000501440c039141a003404034660010ba13507907400308036010156900c481c00341d1302e442c0c2000b40c0e1501604284812100498202a00c0c217000300300320301d00001c07114166a4001c0c0b555642442003060041c0004031070078510040d4021400340c03174165000303005116a040e039580220085114003860300e100044240e03100040c005021303070000421070450584030100c030001100310301180800e1620483c40c1c00000c1c803c14240906540c1144002e030720680d070303450a00a106559803050580221082404010069102800400c2141c2078207006103a004c0722650515142c40349804035100c440e013240c0c00032240520301318131100c2041000d1101074207210950004010041c05620b079162581d40d110f04400d940750380412006d68400003500042d0091002005 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 978948228 1250 978946978 978946981
    0xa05180a09050609130302060c070f020607030e01090837210f020f060705221806120b040206130323011503030c020d0201142209140609060117 63
    0x201001d40001c40f002445200804002051001d483c00d035080707455410b60252880f580c880428140a40102200317541405004100100503190240101000390098a819000036031000005107200c2e03241c0c0103502035800c14002c000340114007902c480104030b041141d41c401d000e2408041d0300d282400d0034006c3d04081010600c240ea0a0180800c00e007002180c0c1d40f1820703844070614040c0d0340c80203400700290065000c18005610346d071140f00a441c80c803000b04d8203400c0d240c10580803a501302e500364010f009000c942031601480349056104010041c80c070301010501c6102c440e111448090401400640600c40004a0744841022000e00b0405550721560084500600c06000401d59002c2c81c0406000c1d0b11b05180c96102031b500403031610803a40c0c1543c5090b18207013a80d09200240c0c01d02c43e0304030306003ca04108002a09140000380c400e40c6c04c459048080c00c2d0010505070711140d03080e40b01104c0c061904080c03040c80c0312600502544034900303441e40c400d55107810380102c3d0380ca03140880840c80c0050b01030 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 978949478 1250 978948228 978948239
    0xc050607120c0e150307050c0618100902130906020409060314060a050c040b1e031905010609050a301208060619030b120d0c0203210a05180a 62
    0x2440c1003000c1090010803080c0790807042a0340d05403440140c150321911290800985a0303584c8029640200c03d85410313030821614242c003600c0c1ca40181e82000000010095245031208100070030781c0b0710300e0f035240c00380b081240c26004a6003021100d414103030303425100d081650a00685404075030003031011100801c01341c0d80d43d0420070890705924148001030f000c0e500100c1c0c60403445004039802099900d074440c1ca05450403441581d82d602c42281c2c10040450300d030030500850410005548035200d480e80c820802900c1010401c01c44034142c03c1481445108071050080da11101c0c8032038240c6080c64811340d24002c1d0455000f910082026000400e0882d101542d401c10046a0401c0300f1000c01e078582c8070258a1320340c2082900e018400c10403400040721420107071014880e0f008a485181d000c2c244910f0607203520030145c140002070034001e0100e90314002d4881142020022002d41c89c4d080041c8410311111940c00920f14460484c09008014000c04c0341c850722680b1141481aa11000b0400e02d400e5070b4030b5 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 978950728 1250 978949478 978949487
    0xf090e01080a0b06030a03080f13020a351018020303040f05100806011704020103140a1e050c0706020a140412030801080109050c120c0402070624081009030c050607 72
    0x100401c640041c8103070007140c1380d8100082c81c0c881c8150306031200388507661026080303040d140009084c49025140c1c84201d0340543c607070741500c1000c0c0c00f6445800c00d03a09882a8030342d44100d02e0f2000414100300030180d07c9035051000c1129169050b0070701c03002c0340300c5610144001c40c41101860280d40b5000015000a00456030281c42d401c0f11410344400840c02c116202c1512114021030740039012403090010284d85103092080036030f10a1050500040b1507101070440040020304a0715043d203907030350302c18192210a641c0011500321100480900841c944007851500a00070340320018a0683c01040c2c10744498002c9816156415050f088661100e41c0c1d12448600301301042e80603000316219400228050f48103009064180c0d803c100207000105000c0244010380141140074080c600800f00d40840c03070b81d036600003041c003d4010100422400c088400e022041c0120b001c2503c3c0301030f84080100f0201d00046003000c050304103450000303403003004d600341650002c8040390020440d0055a08103d042c6811 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 978951978 1250 978950728 978950743
    0x9040201052a0c18070912020d050d0309020f0f01020c040906180507150c211e030504021207180e010b1008090d0311040e060424082a010f090e0108 65
    0x84411103040030655603070380d221341029030b041c1c40000c11010f018090914030320f210303a032024409802da07000b40402ea1182030620078440440030020340c44400400030741c98083c4180014110454060403006041000030356154610042c0b9801680c0707403150385091202550040c030309200e041e01101d203100d4840c9880d585031440c500804810390610003030205641d11414900f540d16911400d880c4c6e1350016140b12440303400245231224104813801300c44000411803440d074840510495100840c0d036080c14810044c480c0e0398004140b81070751261030200000c00401400680400102c100050b0710180080e42c0b501500d801242d00760070041d004862544541d100712107920a0400506a5a900503024400c1b4140c0300f10551100f0030000a000c148580e1084805075a0840b070014400100c1074046641c0390f440d101c2c2c2d140782d0100604c5070702c2c0030004010140000f50000d5464050008184101c005401e002c0e400b80320840c1c1080301c0300c17900c07071402d038010400107001d482e14484c4100e066a503180c1081d1344514 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 978953228 1250 978951978 978952003
    0x50303010f09050c0403080d060b0a09031716120903050303042f060f13050a03060b0901081212042f033304381509040201052a 56
    0x40e1100e0000e0b588180344079060160080d00c1d00a46450b145807501c0c14150000c18a400e961f1307555040c002100d1650310000c0151005a80701c6d1219503203103082180e40e043c0304240400800c00c040040078100d80815111821099110140c0205c400341e02d20212070006140d08018600e00c00002070005002492030007032800140030b82101103031004580280c01882e101aa06904491b052001c0780d0141c0e03440c80603090400260812002e84d9035074400050048240c0d6000395041503450018941600306408103e0140c0303c514010109007a028443c0021441040b8010803807507550300219080042c2014403c41705030030815014240070b40c0c3c814071a102d000c410300a41c480c0c030036000c10511400380701c4482c002d01204141c00c240000d82104480480c0da02c000e008848000e1200c0f0036103081d080680c034042011703c4e500c00d903040c1112101c14100c0880405880e0081c1c071071580709041d0b40c560303800c0f100340d51003942031070302503101c0300161041510040352200c1c0180074101214003504045000401d954841e8 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 978954478 1250 978953228 978953249
    0x14040305010c022a01020c01120f020304080904060e19050411030604110120061b04080d09090501060503010b0d0c0536010804120f02033010050307060804020f030a05030301 76
    0x700744da42038902529030b082d0090141e006880e24408940c06084d40d99420039100e04041000c0303c0e0000c84400b281e208460456002101254803038031824a481240080c00407161170305450b0401050020358424031401040c40a5191030000d01007040c071150011402c0405030881d007060a01d85025080014611030032070000d4001c048031251200051045107100d00644040d0006440e88503841e03031150050b90010100220030480004c80820400c041800d10700d09588441c80e542c10071003018242d603010391048041240910061201054420403514080000480000c0c0540d61b01800d40e1f01c1d00800c1900312031840c0c03403200b4114000c00126481c03c0c40725000b0b801c0d415054408010b440112082e98007070911b002130301c640030300f46014541c1002d107080f06004407030030320104114012442d80d903460801d0944d5a80c200c552400d00303284106541008080401e09a0141414003281c0c2c6c81d6528410442081078590104040d500d83c0454a0b50640f0084c0c1030710302d41c00c403504281d59240d00070300c100d620702c1 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 978955728 1250 978954478 978954523
    0x3090b0a0605130515100503090625080601090509010b0a121a011b1709010806122d06040602030126070e06060d0507030608160f0614040305010c02 65
    0x4003020310544041d54801844030b00a062103040c0b010007064010141461844035080a220640c0c400188040a0080d1b960309603880c0ba0800e01c280c2800c50240100d048482180c1024240601814400304c0d145a6441c003030700b940d5110001200c044c9500e030302c09504100450004145030841000510300c010403900c0321407050015090001c1200c0c0350118000905500503807906441d0703c03441100380d9500414086200c040b400d9114101000c1c203208142046882c0043c20200950b0005241383d071240e0215820030078801d680071440d45403040c02c01401c0c1b000708150288411200401041d103440000c42d42150356034501860312100030b510038001e4074020700301e1950341d04081c0c4001d200e501c0d58522881c00f40180764508046600d4440010305050b1f48010140100b5240100c10701c5294464075059501050740e6107404002070a00220040c0d0b082149070a0009003c030228004c04041110b00524044cc3c20604800e0044241d002e1500014841c3d42030582c0c102380f0703e6000506102d180c901d602409d009 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 978956834 1106 978955728 978955741
    0x60215060d080427060e0405100c05040911070302071a04060c0f0b070305060a090908040e04030e0d060911090105011d0a050d0c080d17011203140a03090b 68
    0x60604c1200f00400500450080c000240010029400681001d0f15003607100e41841240312206a225407110f2407880c8600101c400509031101c00304000c001d1a1002131039680000001c0e00107101e5404040f85455030103060500e2810807000c01703490207181800c103441603821050142c83c0d00e4104603000020952a2503081e00c00e8043c1e54001819180190802c5000e00041e003203180c8451600360b02d034001803c00c00843d41524000152403820b40d49900e821170741c00e410400000d80040241e80c050080207070070380012003a0381c40b03a00b00355561501241844203804091103400c0c005204a06c6448500d02e220003005180c0c0c00250580e4103a54850010034110029468101c0342c40b40d20000030081c4280c14414a00750720343c6440c18031f10130852220f000405490602075801d40b0129240000105030248412800d454400382906807200e40c1600f01034010100e0764010303198812032800043d42d = true := by decide +kernel

theorem cover : BRFrame.Cov 978776978 978956834 := by
  have h0 := BRFrame.cov_init 978776978
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978776978 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978776978 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978776978 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978776978 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978776978 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978776978 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978776978 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978776978 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978776978 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978776978 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978776978 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978776978 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978776978 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978776978 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978776978 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978776978 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978776978 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978776978 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978776978 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978776978 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978776978 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978776978 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978776978 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978776978 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978776978 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978776978 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978776978 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978776978 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978776978 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978776978 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978776978 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978776978 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978776978 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978776978 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978776978 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978776978 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978776978 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978776978 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978776978 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978776978 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978776978 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978776978 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978776978 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978776978 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978776978 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978776978 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978776978 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978776978 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978776978 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978776978 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978776978 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978776978 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978776978 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978776978 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978776978 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978776978 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978776978 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978776978 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978776978 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978776978 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978776978 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978776978 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978776978 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978776978 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978776978 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978776978 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978776978 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978776978 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978776978 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978776978 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978776978 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978776978 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978776978 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978776978 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978776978 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978776978 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978776978 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978776978 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978776978 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978776978 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978776978 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978776978 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978776978 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978776978 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978776978 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978776978 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978776978 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978776978 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978776978 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978776978 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978776978 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978776978 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978776978 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978776978 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978776978 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978776978 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978776978 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978776978 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978776978 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978776978 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978776978 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978776978 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978776978 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978776978 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978776978 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978776978 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978776978 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978776978 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978776978 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978776978 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978776978 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978776978 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978776978 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978776978 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978776978 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978776978 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978776978 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978776978 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978776978 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978776978 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978776978 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978776978 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978776978 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978776978 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978776978 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978776978 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978776978 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978776978 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978776978 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978776978 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978776978 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978776978 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978776978 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978776978 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978776978 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978776978 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978776978 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978776978 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978776978 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978776978 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978776978 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978776978 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978776978 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978776978 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 978776978 ≤ n) (h2 : n < 978956834) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
