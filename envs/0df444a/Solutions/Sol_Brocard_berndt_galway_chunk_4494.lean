-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4494
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T12:48:03.625707+00:00
-- url     : https://prove2.me/submissions/c1a52ed9-72bf-427c-9818-301a85cc97a8

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 808093525 ≤ n < 808273381 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 808094775 1250 808093525 808093549
    0x2010e040903090b031e1f0e093406020106090f0c0c0803071407030509041b1709190302030c0d080c030c031506220803070314070f1a040201120b1e 65
    0xa0b85002060030a8001941c414000c021004840090210086024288c0c01d4120740900481002490303942d41004042c07080b0f400e407401100038a90300b4001d03161004a216450001000c06400015445103480600400e440c0800b03001542d2030318204040020a820a450080d440c0d04400710369240c0d5207181050301d0100605e80301100404d000310f201d90030140d0000040111034003c0d035060200030162062882c0c1d61010340354400101e030000240003010402407001c0c0c0c1d4044587e000b200c1040c9002c0e05990116043c0600550041c1c000041d0240c0c0c1c254200a8030705a9100da140100780c601d06080e9184d070354080541305268502c0300102084655104840d0703499914001850305540c1c42c1040030781c002c0c508028411026168070301da0300062800c40401038540d56a0140c49a400480d000302005550f5071008208841003141c000890f00440d250199800769900d07061440c01550605000240552200d01d0103003013030030b043c0341211849868081130414104004202610149241000111404410 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 808096025 1250 808094775 808094821
    0xd0f03030906290d080f0d060e040308100608061309020d140607170f070c0302031e041a0a09150903050f0109020f1f0e1302130302010e040903090b03 66
    0x5580c43c421940190541c00d02582c0c0458040c0a01c1080090110210b84084080c080c00002c1c043c2d050b11202074002080e0611031031200107410b50700d030a4099900c0c5010390301900007039045003c01c042948508084409444141411162841e105002800c0508120030000041d0f032039000107021500d034465420081030b4002c4100d41e40e0540710303401716034502c022101440010351a00001b09008242c0060a003e0344118859409035990001c1c19111a0007242e0101d086200030003846442c400441080603201c81c2d01e005942d6960b251210032845255005031600742c81c0010031040e002c0301e070081140f008643d0f501031134220140341d0300025101c2d010310368409003d601500403402c0c0c0945040d4080d18030389100719082c0000e440c050080c8140d03115a070a07540008442d16191894050241c0c03404a481d810080c1101c881e0300304c660046d0240e800c00840f0200070385800c42c09000b15a081307003100829040c1900c04010640035610300401042452090301c8100700c0000100710080c03030f07030840410701d1031503 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 808097275 1250 808096025 808096031
    0x2150421030b21010c050711040218130501030201140901020a120905120102070c091b080604090204091406060102120a0507020301021b031308030a0f1215081005090c0d0f03030906 79
    0x5081d488203c0c811580c0a20b46518001c0d036408418018002c0e00c00c0207070085c2403460315045100620000f5441403a0841c00902944040e6002e9074640e50044101540d06001003482e5155100140414500540440106500b48900c10b0300780d82c00611440c80a41044c00e542100040354800d032269032454114541000d18000c40300e044100540080451034031500200a0980c1d5900c40f1a044901110880ea480e502c14104c402d000c1d4802c09446401c076400500020342640c0c45c0e8002422909114402c0751200b96403d000b03050f04c90148041940300c0303001e001400304440c00c01c1d00c0b6149482108484820b00c000070980d241591825819508004054640b10501848081d5003c9c1d980d00b10b080c050303041c0340d0b02e004003080c480f2021040d51806c95880e124541c0707610002070141c45010204250304511aa614081e82e905802200701d80003d16a400c043c102c030b03a281c40071030700c01d43d20010080403482d400101d01c6112625107540c1074082e80d8106404036401d0815103411000b9020f014405000c60381 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 808098525 1250 808097275 808097299
    0x302060c030406120c0207050108071202030f01061e02030a1103040e040302150a09050a08030a02090307030303060914160f090807150e03010b0a290d020a02150421030b 74
    0x84000010030a561882d00d6100704503803030b40342113010350794580b1800005070051081041654003400100b600209035003840084c40500350341810880e0021a10080300311300c807500411100307400c05504407441c1408201d00d070010348003c10203507407840b5550404003041a03404103004505400e000307513801b42071054010051401d00f418000d5482c40031141c1c01c600440700b040480c1c024030072845164211030b03001018001e0b01429485008460f00002c02c00c615041c0c00700b01c03415081e41e0500c840303000341d4401d45000031014209030b803460840c1c0700c854030381c0642c07000e100a01c0b00703038544061013080041441c0b405103214004c0110844640c40c0c154041e0540d80714034480850202951b03442281c0c40407c030755170340e022060510105401e84111090150300700d40c018078240309950702043d81100150b80c51240814900d90025900301c60342c010001c21411079400f080c144102581440602240c0c030a120200059081039101c1076101d184000540c500b00c10601c0b41035100d5030080e046030a401c03400401c106001c074 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 808099775 1250 808098525 808098547
    0x210d090b13050c090f01061b020628030b1507021c05010b0f2d03030c190605060604030c142706040c0201020f0405190302030d05040e060609010503070c0c030206 71
    0x1041610803102e900a4000c00001e81c1040030300303588210858450410580d20b0440c09a03201a4015070041500300013550540140e01c50800512044034a05800c3c01002d5800a0020607114840e401d0000c150400d5041000740c4d07a0780a01c1600421a1541e8543e619002d1000070280680500d24451000314054035070b05000341035204d500490000c0c0c44c00c84080ca03074070b401c010400b0441d1420001c404490140300c4000007020b800045200c9018048a00d0319000744242460110b0403100d40c24030b000c4165140c010002940101500800c0c107070340440c03c050555a4022070341e2101d000b60340c000031500903580f00d2a0750782c030703030b0301000d180058182040040242081082074808031101341c061800e000c80a642d9510500c200c80000640700501420b080c107004c10080300224900e811035214002c5c0001102590b41403140d94030005035904c074a9921440c2c24a01110684010800e070701c40c81003441b1800050341c1040480e40c1c00001c2c9d240001d610380e410720704580088282c0c0c001079046000820801094 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 808101025 1250 808099775 808099801
    0xc040515042a020d050a2609030c0f0304030b0613090605041a0f0103030906050d06030c0603150801060803030118180809120610170f0604030903060b03210d090b 71
    0x2e6034402c604810342d0324002d0681c0e40711305804506000810810071008007038898035030200003264031501c03d14240c07000c60031040c134550141c0710355015400000322107407100010070a4403001d6000e131000e98141851038403004185000140070b40c0c00b039003a10030700212112180d400030b6040d1f94800b0040006081c107041c03010400d0014442c00035541d400e50041101002c00c0c18201d4101e0b070345580e0300d040c85802d28000703c5094200103426035003182c540c1400b0000404042d41400038000d10307500060220021a603084540c1c215921403001da91401c4020b200950340071045a0660b680046071090810340c1001ca00000d01409581915206100890b0400c00501c0e80080000140c200c48c00780c5004a6001d1540e2540b50070381d10740c03002071589501001002c0e56090011780d0941080f06032204040000d82180c2460411142100090301050050003003003480c0c405e00c0b49002050f001000340b00c14050740790a40c481c5091010500740b1300407415011030249908808082e55102031200341c9030421b102c0612074 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 808102275 1250 808101025 808101071
    0xc02100c02010902090a05090d0e030a06061409070c033c080114040b010c0f0f170309060a020301050d140304050301060b0c070e070206130c170a03020c060c0c04051504 74
    0xc03441c1761502140d5044542d001d00c0b03005507403c170007a04600c40704c00419900b00c40e2401d055501401900d681c240800e10707910800c0000c10102c0d61610040740100200130f156200240b0060500881031030f0174006c0b81c0e00c11040c810700c00c4c81030b5005402110b88140710528200e41c0900e80c3c00b100001e6220a28203902c0400103040f284c2d11810748040d40580700402c01680c0c0c0c0c004200340010091141100441c00f040c4007404130f41d00030420703180b00c00300a490f151150440c80e000c8080289001007840485a0200545c640c0311404507021800c550400c00018040c01240b00c01420b045400418403004000c248102e400401e4000c0c001c000041d03951100c5040c9070407500b18144140541d07000001c5a00c4444400e51084c0d1980e80a400310350fa0710b007100440b052070400d0680d40e003031011001003660b05070301d01425071314000c010052030510451300c0c00a2034012500c1c8241d004a205000c1c03c00301d508005041d00c41036404a030045a266034281c0f41e910010001034246500c2800c005948000d4444c0030389180b4 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 808103525 1250 808102275 808102279
    0x20c09011e0501090510080402060f030127020a080609040215130302040b0d02030a02060309030d020a200a050d030c1107030c06090b04050901090507021903030b0a0812030a0c02100c02010902 84
    0x15041d50b10001501c08404510580f074000070010403070b42c2450b01c910700040c1e000c0d10003050741d802d14195808250080d0000d0300410819545c2c00b01c4e444500810318038044030b1040e8000150303d08807248a00925507100601020f010700349074408542103645d00007103c010082031003180750310303403d0402c00d80c0a0200c952008ae40124600613000d02541805800841c1494026000b0a60040e243c2d007400b1940e031000300040110b000c1408541d891451320700041041c000e141e558030100010003040e094009040088105256101c581d48400040c00072981100c0f10300385050000d80c1101808050302d0744501800e0320b411500580001008100d40406414107650059445c0e5001a40b04c2081c7e80341c6218078010300340c0c03210b400c60041050301c12541040d0762107a0a481603c10542c0c5244c00c40822003680c60b0708078086030316480d00580301c1c1000400d00380109000c500401c0702101e000d110525034071003e006015002d03262002e20005038020400c48541e403000c032404021290903090003c1c02403282c90405c0f8 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 808104775 1250 808103525 808103579
    0xd0507052a01140c0c19030609050d03060905150405100314070618180b040f0203130b06151b12120115050403030203090108101a0924030a0c020c0901 66
    0x981400c0158098136606800c07100200b24100b14442000710845032003100c0d00745224038a0000c00041d8080c02100401c601c5040140010b1100701406015140d00703802000d2858035041c100b01c003030150020801482d2034103550004503901c1d40c20004002d064140c2000d4030000f50042940c41e1004002526800c49045607190b030b088600d502031403c10780560f0310400d90f540326517012040407001c05a21075464000001c200142c2c91a90b504180305a03042141c0031600d00d940902900144604828100d034406030450321000c0340c95140c107000340c0382c2c06a902000d04450302d181c00c0503001c00040000c2e00610350042010750321138800b0203103007401d14003d0080c071070030b100d001c2a107120343c0b03004200380d6080d00e41c035401039030a12002c1001150703000c038000c104600342e002c0444000f460350414036501c940059542c02c07056440b0441014070a591f449601402e031702c61900b0b000844900e0b148000c4d41c1c3c11070402240031496035240c0004914244080d00b2065100c20003c00010b800b00c0400640a62005010668 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 808106025 1250 808104775 808104797
    0x60c0a0309031e0f1704030c081c1b11040609020f0a450e09032511060d020f1c0c0e0321040902070308010e011202030d0507052a01 58
    0x10040341c403c540014288805040e03200c0029440b4005600000c1d0401400c609242c1d894892149661807a40407a00c036400a030110b8070400100f1000d03102d00e11039401c01c078010040328075024000480c00300025200a180c5036446070641d6517500103000500b003410302952104001c4218003010782c403450070034020903200c201640424085600c1c41d1820034048034980480b2145054000b802c11206100301038945000701c2c0030401c0c9460b421420f009121a600554680341d030703070000240451200340421841d0703001c40c0d0403200044100740b10000e60582980e0035034403220704405101c0680034034111071110f401c02007000a101403e6110f000d032441c070f104034180040b55242005075201c0c480e52a4150b01a0420340012043c07000200c820250789400b8844645000c2c0d4411044040740c21101c002c400203101e00004200001031100102e014007040c0c24950310b0030328960b0000365202c0b000c09103038040c007001259440030720005100315882d1a64120100c004030707259410440da8643c0842000740400c50300301117 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 808107275 1250 808106025 808106063
    0x16030e040218280611010b09010f0513021303030e030a0807152702061303081c0e240c1213030207061106041e02031002030a0b0f09060f060c0a030903 66
    0x7805000c1407034004400f40982400c1c02105c90030549030035411a5904c400b0301c0301d280d403500342500380204004c0e100b2141442c2070200300b02e004c0300c0507800c00004e1030061004c1d00b904071128211500701daa150600c20f00301859074011a00f0456041c00141810030007203011130a00c40c001702e0304816180215000c01c10603006100d41c1204401c6002e6000c407000e0520901c00042c203020009080300464030024221881d0b032961100102e40c00940b460f4070000080d81500074041c0c16006400c180a8228050301c459100003214000451010866543d8007200c800443c00e00030004080704e1528070525212081072030034100c00a4040c0424404030018804e22100003000d51103181103510804804014000c203494580b115218076202c1010914040c0c03102c07410b01c006940400c024440c0e48491503005d0385a14000003d5000c0712442d203040340c060110100030058070341e21a0140c560210742151641015161400421079501480101050b1882000000c2c1d051640149209084a10036200c2d10201904250 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 808108525 1250 808107275 808107319
    0xb150301060e01141e040c0201020c06180a150b0603010303030e0f03040501120509101b0908071208180307091a0d080304030f050c03030a062916030e040218 69
    0x4c070710384049802800c0b03103c80e441d20210300d1194120851111920400c00c00c001001c40b10042c0314403002d82e500154030040500c0900046038456140040805120a0710000f80d13200d01030110020011f081e43d08106c101c00c9481c2c0c0c00700e03107442405007151382c4940c1c407407401a005046030240c00c00c01e4800c202907250b0681c4004101c0b03050310b0040e034400c0c2c2d1100420250001a000103005d900304c074011041440c1c0d0307482d8288515101c282c030000d00000c40003d6448081e2070a03426800440c0990400d0703a00780000601c60110500c401c2e40b001c0c03450740c0daa03091031030b80c440011821340c59589401000400502001c00d82c20041542e048a60489852000541000040700c2c00b10f200400110042c00001c011a0082e41c00d003001c030300c107824000d162134070700b01c0b0260456100304c0d2820860380d92800144a00b0347c2e40ea9040d1440302c2c437030841d0314443c0000015000103010300ac61641120b035603840110201131080710f040c901c514000c1d0089d502e03111400104140c1c00f2005030b042d03008041071200340d010202413032 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 808109775 1250 808108525 808108529
    0xe010506131503050d03020712020a030c0305032206020307120e100e03120405070303090b0c251d010833062803020306131109130b150301060e01 64
    0x404a00e1100700000425000e02502c110980710b481c180d0070b000000c1102445560b030102d481c1d1781c00699882040c50300c2000100300742210340456105008840c0042c0d04580000c0d25160141445622030395030300c40403800f0302d2084542110b1306018841590403c506c5401a60050305543c580000c001240d560044c11a01c0d07048580f09c03964807203031070004010700e107a101c20b80c48229141a20701c2c040c50460b4441001c0b03801e5500700e4480e07201c50340c10010b143e40903451070068001c0d040302c5032410b94902001a52070340742494800c0e84040140001c03212040403101c00b0020601c14a40310002454100001c00b00c240034401c005681c024000c0c2c480e28401d0301c42c100c5640d106c04205000303964030004210410f00d00014406034024242c2c4108000303040340141640030880c120725102c0c0d080ca085106160400d04040c06000060400242c00307400150f101c2482440103005035405074150750f402d2442d405044808038003400386415181403190403a03130b48521000390139040e0b00902481d603071a6003c5c000d0640034 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 808111025 1250 808109775 808109779
    0x12309010c05040513020f070c1802120a110c0109030c120e010f050919120203010c080603070b030402040923060c0403081c0f0203010b0438030c0c120d0e010506 71
    0x3c200501c100c0c07804c40300600741e0580c5007200608100010403d0505030b40001d0054440e400e42d41400c0043c03481504042c00c168440c0103007541400024507046d401d40720003400d050700031901c0e4507000020a04810031345001d5410580240040301c01e900700035210038081182911002203409000340924001c200445014a060b91400384039188008111000e821004649034807082302d1101c0c104285c0c002801001628850b00b0090011200344101400c4480d900a0002070040b00c20402c03810f0754003c2024411074040c00c802c2c99481d5a5413000a0040500103402800207441a9007403800c203540410741050408540115450f80d254420694540d0185200c0106512002c206600ca071030300c0c40c100380300303007891050010454190401c0e1480503070700241c10034040500c01203001c001c040e007062000c0c401d921480c401900194414451180c100e4014281011980c500001280803c003104080310002d80b4007509035407001d25814891031316a03010800800c500d42c20200c095400311018402d0314019440 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 808112275 1250 808111025 808111027
    0x605040308072d0c300f0206030106051c0c09051c1406100b090603040f030c120f0f0e300f06040209180c0f010201110d0906060b070804030201051803012309010c05 72
    0x45c81840d01030044540c41200d01100242403440140c03180740146019291030b84a040e1a20000c1c0b03850300313001a0a2001825203800d01d090b0400c515000b50218050312002c0d14980003200e1101080a09040070b007a0050590449100c0340080090100d20b290081955102c4954000c0d562241d105e03860203401d51180d030000301000800e00107004002602c00003880380c240070500013415242ea10a802e40da82c40280032038068a00d81d18180da22a0b656084802d003400d00d001500c00c1c000106882c40403c0e2401c02d410011001034000714035100180d1018265440100c07072800d40c00342106510380300240c0d41240135940c400b010544142d0703001a071010701e02c036940080154480640401c00c1090590361603074159581e9100d0701c082010700f50020301d030035407041c0c5022541d00410f02d0031100311081c503440f100800a00b13010000014180004580132660240381070b545030300c4000200c3d10131502c110103d6500d50318100220366174120645560400f07072040c0707020380b1090781d0302d05d41242a1109100001c00007a0 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 808113525 1250 808112275 808112339
    0x20130212070c1518080304030f030608030412140102091207030605010e090316031b03020105061003020301080d050d110712030609111e0d06120c0603060605040308072d0c 75
    0x10840c0c2c01303e8003c0c0050200140d00303034100d44a0032440c0d072056500794001508040c140003041c1e098041c40b0300902046005500d4140340241803844198455002006000ca140c82a4039680e403d40594110550003803280007002c0d00042d0b20b41c0c3d03901c02c0344021a04c1d681000000030781400005600e13446414030801451801c00101c0c0344000070760303c030071040301400034050300c603090840d11009044030035100c0d8000041d1030070400b0030050300c0c0910941c42c401b0980104018440e201c40407906148040d41800c01c6511340000c0a00d000183c802c80a06040100011440c402400800c640311041c00780c0c0ca4504000b1503031103013850003c0c0d460500b03200010305000c01c135100910112042c140c40082401d5800350920b0043c0e03c80c2d1050303030610352203261100f43d070f262101d050001468410b00200020305040080e503240a034040e18a01a034840500200401702d01182801550300207840c062002c240c4001e00307031100c40109411a100710a0541c0c000b49101c40100d121a00350f016440a40c20181d8503511f094 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 808114775 1250 808113525 808113563
    0x5090a030516030b150607080d090c0f09060b0a0e090910020a120b011d010507060b030d090302011701060f0e01020319090f0506030f0a050615070b06040506030c010c20130212070c 79
    0x9403103000c9c2c0d10740b0540d403410707544081420354100e00041e000c03408204080c10700d400b07005d10507640e0300d030840a04c082e401c001c007018440d0880c20404030700006481240c803d40e1350046050034042d40c0c00c82001810b00006d8a90750f03140c1c0c802030758610502562810408010040c2c01110750644420b40b81c0084030521003549103660003a0041c10049114400c0881c44041c840f010034140304c0c90b0004e01c0045000b101040c400c41d07130030846544c6204110001541c3c80d62412000070100d0200310101810300840c1d061020859109004a81065422171030300e00035240304030001810b03640f0714803c51410a411070780c045154900041224001d041c0001044c405071a0420090014030001e4504c03541320340041540c0041d1180300d000342000600400b00c0c401c0e00d00e04841844113640e80200142d101c0d030003200c0244150780c2c000c082088050b800074004421707880c516500c0c4c40d03221108210ba60b40581c0100c2080c4000519400800506c1c41a0b142010503444880d0255894180500010000203156544800c20 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 808116025 1250 808114775 808114777
    0x29030a0941030f040909021c0c091107120809390102010e1504061a18042f0a0b1e0a0905100e030f1c05090a030516030b15060708 57
    0x81d05488152450510348050803032481e8000c1c1d02084410b9103401040d010340c03030203450b19040e0050012510158031050785c4c0b16044008540514014035696448141e900e403000f00907155403650296160081c1c0c15600380180a40d41c00319801d203120702c14a0b104500c0000d0003903d1040c1150001020221005988800d10076107582c106883e04541d683c2c5a007250420b010846e00081500070b403c00004d500385402c181007a540c2c0b913503500c03048040101c085001500d94031099044203408003c4c0b03603851b8540d0300c0e0101c10100301441b660403180055000c0c00c0e40c1c006020000e642c0c100c0440e0b00320b003c0d9544d881030303811900450320400940b440d60700c0400361009000004116814040c40c00340c522035141d60000300701284000007000000c80d2a580d240346400d0401959000c11800d00040902440944240d00c000c10045a004200700d00400c00948544a0307022400c05554041e007950315141d0141503140d10145144010341c1e4400c404d60104071110014184a41008000307060589014103d450710041 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 808117275 1250 808116025 808116143
    0x6150a0c060b0612100609330309020406080c01020f19140f1006080f070341030702030607030b06030a020c1903021b030c090129030a09 60
    0x18504206800441340c2400c8201d200d210250b60581181d0f0400c8801171024941c2d4000a01c00704501c00001002d4883d42001c1f251000f030041c0200210101c0385044018200c00000290440d0030408045960700c0003190350107981c4000c0e800c031401000e04190417942d031040110b00704525813455628a002c9480424409445460f10007103409410900302c4941c608102500c030404800c0c0c0e00d0400340070742031b024044400140440c50090030030701d0070750703c3d017900f020b5452010940b2031508100c110090307c5a5042d18080d0038250b104019203140811010340c40c1d5004200480c030134003c0000060f2118044d2040d2103044c3c10190545080d0350303403112080002c1d0301420f000f60076882580141d1006a45810354036038594820780c050113581140707466030711440908110b00383c8203800510980942d0b0b11108000c4d81100d1401650720800c00d01040303206034a01d45082e003c00c4e80307480042001a892a50b40144140c684121103e14060004c0c40081607004c400b440420900804503509135203042c01c80c402501 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 808118525 1250 808117275 808117279
    0x8060718031505060114030a092f0402180337050604022209050d1202090d120509030a0303061d0106120c0216030f0c1e03060507090f030b06150a0c060b 67
    0x40d980c54000b01000e0f0022a0308e042050b880380000410085030040310902d014091215a00140c6207002d0f00481ca25204907140c080c0d640868a680d610001d160160343e86980901a1290010640c40511003500c88141c11108081c0010a4040b00b00071080031100094206020300500d888580c01c01c4210881900e81c0f0b8020001701510540f1589079100b0744409610650040001d48000c0d0700282444405000109035a84140940281074032000c106031a016449007204956035112407050750b45c0d0095820704c581511400081c4410540c15501200603120b110003caa10840c0b6210055140c4600b40141c00008142030088109518141c206220a00755401940c01c0e04940001a041c0c13a15540e0068684c800190600810301c5442d0704000003602c0001544499000201c951038400504d03880010425039503a00000c0d1443d00c203003241c0c00944440d07003c2d040c210707960381000e0247c18016601144202201402100c0d0030048408460303d086040d21650010100c0f900d4110081200ca56015 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 808119775 1250 808118525 808118537
    0x405151e0a03230f0a0b100c0203031e04210812060a0312020c2403011707050a06030905010b2202130b0729060315070216080607180315050601 63
    0x8603c054407255030440d02007000c00070441c5468410303409421140c014140c5c80034039181c11020715903a2280b0032180c40c00c0c007071070074507001c001d9852000c2443c1d8864100e40080f251814a01d9080141c5504010421110034480821a4611b00754220741c403030320b144400a1500b0010070210f6044a040d40a880c0d0000d4010200a00d044d03894588080c2403207180d62200040e080420000f045281a0300122200d500050790354034061070b0003c00c100c05100600800c0702a010070f8440c44200801001804090a07001c1d0890f032038917544600140143c1502c5504803215400c0c141d00e5642814401082e00d04881c210102c2c3d8581240c0061000c02584003e05204280c003d01c0c2c00403172141c00800003000d065100b828ad840c2c02c0400d6200d1107440340141004004140000418410b465400190401d43c1c210003070036200c40b6440c1c12000b41c2c50040d02c02c501880034048c600000402034004243c041c41450241c071640038205a0510342505181d06000003080c070a0b01401155010101e0f500c195071210040c1411 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 808121025 1250 808119775 808119791
    0x611011b080415060608101403150c1e030a0c1d040b0d06050f0609060603011a1813060810021c05090a020a03050a0512070f031d0402040303050405151e0a03 69
    0x101651440d4200801141c2454140403e4040714400c15002384012845110b201c46610006a102e030b580b07000c91060742030720002007580c0c07144040c119140c05050b0400280e80c24048a003141040e00100c0b10142d1461506a482031030ba4000c0b0300890600307e008000014988094003000020000d00c10700d40d41200d01d103104800065403910400d8010007054140e11641c0c50402c042058600000300400c0c040c0c442440104038100144c901d09a054604018842d00e6120b88400d60011002c0180190ba10052010300d01c000c041407a44110151841c9a0035252401401d10505041e440381c00050100045644084103d11181d50711081d001124481038810055864000610041282d001a625030b0081805403080001c100029003a0001032002c1c1418040c0d10b49982101d410324a02c060144840f04104403086441541910911341008204544843c1c507420000c002d41c1150080d113004051002d240c0b05010008d6068500c40f100c0281400400d48805a0030f04040e00590010011304d600c2c3c00c80 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 808122275 1250 808121025 808121063
    0x10806030d0f091509090c0504030803070302030c1213060c08060a17210c06014103010f0b010311040b0406141c0f0b0a180b010e060a02070611011b0804 67
    0x4c2000c400d82950344204110f800c20b00ea0104560280455206201307040000f040015080020340e54810164140140c496550141e180234a100b8001403909a2105000f0800602001c18400043c103000e00300420201c0000720050760890030a40d406035100003101020002c5810141224811289a000391015404d4040381d0329413131141505444000742021840840340340c010030880740100380b5600020031095002c03032400c818008002d100d40e900f64200030220001803016480d0000030902074003c0241424040c01c2c50300030074480d0f410034000b81c1040b40000c80d00f424a401d940641d9440c5c68031a1130700789021000c0c1c48814025003015124070060156085100082c10501250507183c240411005007202164003120100b0715107078400c0540000521081d80e404044224401c0030f24000140c401100c0010385e101594504460392003000001c0c511040c41c1d01182d0441240c1d07041e2034803c0d659400f211080e00307036100404104400e4456030322100e44c03548141082c58006000e500c1c001c04100350405 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 808123525 1250 808122275 808122299
    0x142a06040f240e0f121c050c0c041431051006050904120e01140433020c010e010c0203010903020d180807031205090604090e010b010806030d0f09 64
    0x800100c00c02e4200810841c009501c5070702c0c060b040d010b0f00c0c0000805400000080b480000e028603680255420128050710071020401d01003068403000008601c440c0a18008106030310810344d01c92903001d100014021818940901c0c1c00000c04801d0414803591469510008a104d2545a481041b4075080300008428203064004909000d44080c2940541400990007540c1065001a006007802001c01005c20b07054141005141c00030b1a05098132002100101d40000640b2803060f2180d00c000341c0042c0c100b40980308040c0c1c100c1d01105050100c51780d215441d101813804202a005600000510800b80d80300e040340002c042c0341414400000ca503650042400c46207d40001c0b005a4403c0042004194000340205206805288049003060408081d41d480b500c40d0304c8020030701f4007052400c4641d61b010b442611b00c80c640181c0700c0e6441d00ea07036118800240002c1500103085518006001070340394423076090745110b01c03005801050024200c12045500c50b060419500c108515041d0229400d00b52035 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 808124775 1250 808123525 808123529
    0x110f03090a03021e0d1206050406060c150506011704080f2709091518030708070303060b030c0301031203090c06020c090f0709050907111009142a06040f 67
    0x8005000c6201d0928010345401111914812402d4000d4981c039140c00000031194009401860400741d2554000035050203403015810095215007004008a0507540c41107042c11054001e4060f049400f003510744420854000303a4000d400103403c0e5404500440140c22290f03007061140c0503607442c0441540c0c554a40c0c0e00480200c0758070114040e18100701a01490035848450360441e40903000342000d040f45a41d0707254605121480b0b1070301d04000368030600c90210640c080541881a66540c0307000e80303403848043d8070544048010a15155000c244120200240c92288040318509403869080da15a4410304105198a10426443c1c62610001031803403100075004200540040a072400480708000381d03940010714202c80c00c040102044483e40d80a8524011100c0075141804a03460b1018100c41c0c0d1074580c00c511400e40308a24042790560051b90180b9285805a919250a04000da8007682c035000303032251000b8450307040881441410000c102034a206c5000808042c5000d42d1800e103104450700c20713 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 808126025 1250 808124775 808124791
    0x225080c03030f090f0145030504152a061e050601030f0902060a0f272303251e0303260118111303020307090b0105040306110f03 57
    0x2000d004980030304028080c05c031a0740380003e00810042060340c0d611480c104400c50002e010101040c0d060208000e03070740810b00601c410090b922041410041d040c0d60007840340501510304803da004585208403044440d15100040000c00c420f070354031047c03a4012040400f07a40301aa14040030f49800c0070400711800b0030800800118451510b50009400c80d049a020070494900f02070b040c0380140d80340b0041715003480390b50600655004005204035403400140b01c03480d601000c8429007a4096140c8003848003218202f4201080388030885843c01810708050001680651003c101e020381c4a42c81c01441000b4040c0f071100715a80343d911015008504012180185645c19222080c014103a21081002028542c291918607401080450f820404814454007241d0140c0f206004a00c1c0181c0e00001d1a11103000c3c07040c5d40364140b819414a10700e540f807204034407a120b07010b4005142041401101420780058540754201303451610b5405c0901070113a0b071441d9003c0c00b00400c0b125a02200040c600401034 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 808127275 1250 808126025 808126051
    0x504090f1a0303040317030405010b060f04090605061c0c031b030614181302040b130e06160e01030e01090c2d050a0311041d030a0801090225080c0303 66
    0x40754001c0e003028229100381c940660801c000078804904100442c58402c0750540351a44c1d40e80d600e0a0031801425100c0c10985d00c240000340c0e044048000d40064015640705c446d041141643d00c5040007020b20400c00381008460360320b213000c11039a00d0f56002c81120320345800c001c038800d54051215211181e103101c4502c04640c0c1c03144107004090401c0c0c81880d03041005d403044884109030980a1010350001015041e011464850380c50031034550b50450342240f0000b0342016088480c15482d10f01904005242e8842c41c414100082c01c0c54115032200451140e46071110144419040011405803800e201103800f10b40d01d554010b40090400403074440200625132080c00300c4080f14080460791a5420054104225078810a010607650090ba5408503980300c00d0801d500d100010100d4040d0a00c1500c00350300c1030b5004240016081e0110003056000407075a24110710340e1b00c802c0c100c002c80c0203401e0400c0d9116003401203400d00d44074220242200d5070040407994102004080554559881101c0b10701300100c03 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 808128525 1250 808127275 808127291
    0x603020a11070b072009040b07081b03060d050a0b01031101021608070e04060f1415010507210212032d0f060603060a05060c03180a080a120504090f 65
    0x10780840000c003064842800350604514025203028035000709078004d407001a07824a910203260549844107902d044c050410212440c090601040c104411280c40011484a10000b201d038020a40340d00e09040b004100755080d901c50f030040c0b0422002609040b541442100100c10204000040702d6008510414a400c7c0c10300b81c8100080c248544064494400c1c54203003000d00101d24086444803d0342c90682c8414410307559400d182000e01000c002c00d681480c5401040c9560000700460580300d071000d001d100d00c0040c1003800456140c030074440d000e0104514800c000080c0b40348442d5003488583c042c811600310828050524105078829203011340b9100c0a04c1c98142c00d490310b82d0340042d60541011103983d01d8035016100f0050740740c0090089110f1140000002d05558803450078001070f1001030710554452440324242ca69071f6002700c032a5000f076440002c00b5400d5150288803c81581e0002000d03080b00c2d40346030307610100c8a0a4010f0601030140620012800d0300c2c0b02c2c440c003c100d840800c1c0115800c0 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 808129775 1250 808128525 808128527
    0xb0a120906020315010f1403221104150524091c02090612060a0905031e04140301090503250b0c0304030f030b030c0f0301060902030c030108060604020405090606070c0305070603020a 80
    0x413400a28160500051902c03082e00190000342c5402c05e1212180ca10343d0346d90700d0f0340704000b106104100d40b044100480d10700c0414002c480c410a81c8180703090310308002070f440e9018070142a10035882240d5024031151011944003954080d20101240341d400083c0c1400070704000510007504445043c054200010b90f0320080d032400e54451900900c00b1380d00c1d82c1003081c01d06611038613820020400343c242c980364880d010400c441081150043c10941041c0f5010300e210f580c1129403079000740303c0d592020a1181c0c1085580c541841b03003540003980400210300d0201010402201d100e16900140040106012800080380a14501602c030301141b00e0081d941c0c0c42e21780b601400c14044580141d0800d494240000015240021400303900314084607901e40185075540040d001d001c158028201690010061000c0f00754a070003c0e60603244200c0c10740c0ca1301d44e21442840100d010304d1040c40c5c0e0105d014008a4060300701507004081541c00b803582d071440c060f103c3c2c85084c075007c010f5100b00d001a500142d030107166 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 808131025 1250 808129775 808129801
    0xe060912030705070308130b161d09061302040902070308071e0e0609032a182202043c0b060f03180d0e0103051303090b0a1209060203 59
    0xd86000e42560840c240344200420714050b5080c02414004551302047ca038240c0c3c01607428181d540602c140c442071401078580e1540c002c400340710343e000c1981400102020025480d14020710344001c0c1c000c0b80117a40791002c220f041200720744403110240d403c0201065000c0e0600080044502940710342d07505003895240205604040303050b201c0380d6201440c5c20700600303502c9003520f108520102d403816191406400001d003055054103c104080708403e0f4545404500040342a00d00781c1d08542028035100751440090040300300310f500c84403a080014120610f505405000f000c00342c000b80000070ac842002c118091181d8075545440300c1781c814104140c1c009503d00380c12050405500f041884640300c02c60100b803490080702c81e8084164804000200312100c0d000101817410300c20310440d1030103408550060f206100900750306000a05020008501d0300001c003510000d41d03450b80d08c42c41c3d21031401314000415008016079004000c0005662032130b41c005c070f0284100c030b036000740350040e40c81c10081c00e15050 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 808132275 1250 808131025 808131043
    0xc0907030b091513050109140f071b060b121b060909040b130f1110091202041104080d030e06090703030f0509190815060402130302011805040e0609 65
    0x8060501d200c1610a8440c002d03a140c10200606082c4079010a0400050000043c00c000b00d8800b4644000010342c2d00300381c0c100c55a4001b100300000c4c078544038552200007141d011900440440c82090b05040240600600300102d11b00610002540d51141000140c17000ba40d4070311503111368881a0104040c1c4016030f50340b50020003c40780389240c03414003c0070071000c0344003c001a10052003100041d007400315400d034080c26075902c808415010b68035490b0140030315040c00c62460003800c1c69411010858050000c200c241c1d040c408949101440039420440603000d50b51583c4643c4409010001e00070b2000c02004000d8031280c0c4011542209074400c00d49082801810425540e21200041010980064414441c11041d251042c0d440c9000380200d82198000d01c00440c5940c8495070005894002142a00246d101007060603842d0300d800b004c010a03402a5290b1002000041608100560280c810f0398103001c00c0c602c904440c1c030369510010b401c461f0031480d0014942c22007030401c20010418848140b0b = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 808133525 1250 808132275 808132277
    0x30d020304050102121803030a020a1401060e010315110a03020702030c09152e08090607090e24030313050a080304060509040b01110d020f0c0a030b150604090e0c0907 73
    0x100385840e02000070f6480906140041303901c000011b201c5240c40103428625850080902182d9641e038140d00025654820a034040c1c500310344001c0c13590807061042c000d000c210703a0030070300d041416429521070390500404038800c01d01e5503580e156000e40c803200c0e0002511154072980c40060b2031300064014141440c0c2d2440c00588075120013410041440c4c41504501c501e550241d50b400500d128070074100c254034043c0224048101206c440e115074155000750304501c2100f040c5d00b03a070541c0e00c1d510015500d1001034000c0000e00303188803002a00c0b060061001d02c0010700004540080780c102031010a017168042150300211303030140d1f60140f0850401b6a0702c1c1008141c00d60045180030b1070018000c0250003400011841152074030442600c50b8841c600d00d02c0700b40361000584211059110000c2e603511945045e50030280104656850703685450440a4126500610720a289075641c501421802500d070f41d01e658082c0050002240342e09961003040c149481130760040031100001c6042000500004000318 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 808134775 1250 808133525 808133527
    0x90c06030f0f0c0c0102040305160503030310170307020a0f240f03180204020d05090105070c0f0b1b0f0307171e100914100b07031706060d09060b030d0203 68
    0x1140440c0d040010942c06a42c1c60314164640e1124031041ca000e2144280814056002040c040300b0311001080c1840300401842c0c0710f20003580c1e10428143c490004503600710041c8250802048001d807080d04240810201006032850082c0303503400030300012429001080c85403243d00007400340d403207100464001c01440801c0400c455003091801011949404200030815845410203140540c40b140b42d6140f20b03500400c103544842845104100426003100c070084150708020208081900990022280d5500302201c510358142c1c03601d848180170000350240c480403010f540074400e400c4d507100140608042c03090340d03980e503428840b000400b0042407140d104000c030450070601401031880b82c068000c4440081300c00460340e4070750340341862868042e40246103031810600150004010b0150f40c034420401348007204001512071202140c00d00a494005020894000408841c0d17103400a1803a44035500901d40c80c030b0801a1000601503d081c0c2c801215101d4558900c1c50683c92b003404a43c4251000344011 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 808136025 1250 808134775 808134781
    0x131401301508251a0f0f07030e010306050a060c1703090307060507020c131d060a0c031a06122809030206130818010201110a05120c0412030806010e030d08090c0603 72
    0x4030083c0086100389451030035051491503030003003044140e901802401c00d119859460589000803580c0c00710382e007140011141c01c081001c56000388104da050303e60241c240018641000c0090301e00000300c0006482a07419010700c0400000711400951083c4910405507071190044e103480d80c150740c4041c3c10b44040d50020507483c2815121031094070b1000300803030004100041e1881c42040c0b804190078400d05140141001c002d8402a05d810083e5600481e540c00c0003035811104000030ba5404406400da03003c00d0400489c07094500f074054450308000d002c480314441051015011003c444441d18074550117444a41c1032003415014005507a11188000780906964403a81e942d0300e861080d1035185049608c1c03c0074a41c200d134400d500105c40c1082070380d1516031b1940749141c043c0c42500644003401d205101ca100040d032999071041502d0444541c5102c40380324030310ba030307900b96000400100705a04100b00f4001c2241e40d0f0741c0404c0061809800c0f6210429182480711401d800c001c0104940e5000d081d0800038 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 808137275 1250 808136025 808136083
    0x207060b181303140c01060b0a0908030f0f1e03251704151d0601080c0303070c1512140714090f10090b030408131401301508 55
    0x242c041d8140e89444c0c06010f0310040c5103000c031107000745c106100840d0704e08035010032900c4400d00203103480690707a1688110385654100055892103040d00500b0518002d01c0b1b100c04009103000a0640250102c1c02119103940d103c038106400c2c0c000700c603e00c4012a000c000010000705003400381082001e90318009059205030045a800c1c80b401520003401d243c0e01d114600c10b40241c66100c808241240a55004002c05a8048903643c0c1d80030f00840103a4029095401a503140010440705c0c80da0303021480c1e0a0b91407410400c40c501006d10484d007020302002d0007070040d64000c0352043e481070010341036000c07440c1d00307007688010a501000b43c0740019100d000c0213281d420ba6035000d184100e07064110781c02400561050001c8500807660792100303100071008014481001481d5016201010041000c9841103035211081e030300346032110b071149000c03601820441c04148444090080b07804459034400102c1e4100002d501d0072034802c079443d451406035000341407280d46001d0140080800c0c00a456840d08020410 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 808138525 1250 808137275 808137301
    0x2091804052503171809041103070303050d0605100f031e020f07050c22050903120c0c062d061f020706031802100f03091506060f020a031409010c060207060b18 70
    0x17950911807120707640020100544403403900006040501500c0625a9910b4060850380010300006d64807810620f000c216401c0250340042148101e549044284142407401c1e0010132062007020b034219920000307920302142500052412080e00c4103829960b1210381021410180d01c040b50500c600b9a03400041001345c441003104c4040e111100d0009420f40341e04015614600c28418200300c0c04008508000079222214047d00d00c07440d413a01a504170355140012a40c4079400e20a07011a044111540c00c01d0310851000104d82c0254040e141084404500313840b2075401460320303160030059101c12410302a1661501640142e550304804094081c1090b50018214150001c981c4d010840d5001003a48021f2007900000b07403030354111107508a001190307860440901040e0180c20040365200030101d114610014001410680540c2c600b40c407045022180c0203242e002510040c104101203c440010805900c010030125200749400148505003406002c070708c020000e9000700f9051030704200100388071014 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 808139775 1250 808138525 808138567
    0xf06010b0a0302120112050d020102040b0a08060409141f06080a02010302210907090b0306090604031808100b03010b310207050d0e040b040209180405250317 69
    0x809000e88440310108120000d0041300c10401003201440000140241c1e2448803003e12030140d01075a03800914207030142d0a0348503070720410f00010800c00c10440d07182e100d44d05940e007003240148040351040c0141c85501c03440c80200c24501e55a00903100c031900c0200900502201d840040f54144221483d05e5407040e101c2000c01d030040d040c1900002e182c00b69000f4001c41c20462042400d50106601f0111079555864105000f19203660786400c01c4880f5519000030030b244107004040c0148015510303603a007103594030039460941402966226001c603481c0000d101d10510280342c41000170b10b400c901420107081d036a64078100c5d80507019a142c00c2d03074140b00722050307420340c001c0b0b01850701491034200e0310310720091165a1001d04140541034520b00d007968801c46008801c00200c6092100140b0482003004a219103445541d004421240e1041008007214055034000d0164041d19810130181c190608582d0302c0444034802d0000041c42441004038401c0304110701c03041e8030641c40c20880307840c0c0103000120200f = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 808141025 1250 808139775 808139789
    0xb0a1815020601031520040503011802060304060b0a08030d022d0a0e1f03020c060109050606120c1306180608071209140706022116150f05150405090f0601 68
    0xd4074289170800429041078a000c8092601402d900400e41e6605000d500240980f40c425400c00543c1080c0c0b040c3c0326840c1011030340091806146440340d81e02d450041861040c16034005459040014102400348080d20301002450400f580d2010080214411442228118100f2580c070002c002040d0040b00d0030381744c03001140e0401c0c5040030390280000310b024503070320704039070710000b00c240380300c645c1c50f4180c002c0e104060000c0211010303642c03601440410b40c1d01c02c40d54150089801c0c800403500903000007080b030b00541c2a000b00d91500650f07030891003121100384c00c010041403060080d2501d060442c0041c000609907880c0803140340c14000713170003458900440710202000d030300c4500340740c00d110040c030b5240160500b100454100903507070300c006515640c1d440c1c8000c003000184641e2080710000c034001c680041a900140c1a00501a075135000e4910130240c0400f80c05d19914052020a00000d1040500aa2606491101d010510820401a15002409903000b90050106980e0790440001e089041d81c1c96 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 808142275 1250 808141025 808141043
    0x40e0a0f0507050603100311010e100323010e0405190309120203031303030906141e130905010b0306150703091703120c0304051c0c110402040b0a181502060103 70
    0x3030341045480c1c40c0ca55000240e20200000500108225480701c0c802202c0c802e20f0743c580d02d81102d40064586050f460a615008406503940050041c403c0d480400319908605000030070540301003201c0d40544090b080001281c0c102414801441010805141070002c90000d200c0414142e50b0010400c2d007041c41480c0b40c2c040982d03809800c650f01801524120311648234951601c5a0b6814002d2440c2d01c180300d0440811407244240100c1c8001908a81800c1e008a4520003100c40d41c2402d0b521550002540580410741454086070313981c0b0602506008081100c0038a80b60308140c000c1100e0a501d4181880c1c59000401002000a401c00d41c04030840b0140034078800621100d00e281c600f540b01d89078a07907181807408001c00c480c00d10008017a5004600800444405000706001e412300000028001c1005c905540030100025240c10007000c04e2440181c405400c00da610104081150441000070780410217030402d510125030031803280702c02030800070b0301c0010220b030019020f901d41a042c04040c0007030f21 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 808143525 1250 808142275 808142303
    0x71a0414061608130303180305250b0a0809060105010c050a02090601021e010905160305072c01080d0e090712020c07080a0b0106030e03090906060a1413050f040e0a 72
    0x600c0045843e001000320369140d070340c10316205040b9000d02080700421040a001040092012098000d83e0707884401000c041e024420b14001c0a00c080c40045803618480700c020a80c2e064a01c0945001c00c0c1d19140e040307131400e159007a0790030060160030140c1003020140d034200120300c00180302554250141c03542045070b150f03a00101e003481004601c4884c0d0200480b00011145415485144001e0064040e611038415820b100501c28080307100c040d003a0361028405000301e03007a9510440c40b180105050400c0f100780600c0945009000364010b003d69040903116200c141d8102180c4c0440781c00171541e2003420315003041c2c0602040a0404c141c0c24003035010034032414000c41000400050054403045a00c000d200d8a054802d8290034083d000010f41017214140541c403001040d58000a0001c02d0f0303007100d9548506021a90b085801413030304103e050003035501c00c0c051240040840d007010a0302c0707400550415051200c07241c2040320750f600a61415039420f159140205070368410307a81c081d00246046c0 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 808144775 1250 808143525 808143547
    0x501030f091403070c05030d05120c0c0d08150a0513020904060503060f18010b0307060c23100b0d11040b0d050105070507030e041505060a020f030309071a041406 71
    0x70344010000c000101d89006002620800070240c00c1452060360504203407178440c2c00381600ea000654640b804600240503c01a2090701030700350340e1040b049039080d820100000c000034070b088030404140b4007041c0c4030f0382440117031301d0040d440d0115114107542d130310b60461424005c900762224440070341c400103a0101e80400156135607000366008040c02021a000d0381055040070450181c10f031410080100360214603105040180510116454024050f00206181a8050300c24440007602110020a01e000c3c1c90301e801080d0040190070b40030b540090040c0c00388040d01d141210030010505102e555949290000100c1c1660104109201a030b00440c03008106000706800c1a40020010000d509003810800300076030045c01f4051107402540c41c8620460791405103c1101d403002280091005052420300560406200511180002d413040f20642c1004403491821504261001007071904603450030403569240706011101c0c03c07a00c03080207207810310702102600746030700c520041802400c2c080f800c0a40c0f0 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 808146025 1250 808144775 808144781
    0x30b0601030f091103061038071a09070311130b0d080d3605070504060b0729011502070e070c0b0a020307170a06050a150f030b0a0501030f 61
    0x262111a01441005407510b041000307a54500310082c0248a12000922888450900701f02100d26100590300b00f00070f5498240220044020350701c4041c0a03101c201343e0001d28540c01800c080740110700f00010948003208005800901600c0d031074241c0d01142d4103002149618825852020782101c41082820603610040090300842e654268003500c0d10350a0814815450014040746010800030403041d43e049144010205a2080c400c06140308411134040c0000580c0da0f402d0010701170012621225503502c0003a066a0190b000000c0103100800c02030f080110901a8500381141900c1190528120b484500007124051040000e086401d100504019009000c0d0714043c10383d00810f42030320b20f0a15409071044840d4201155200c894170009034000a00c0d10a4034080c0c1d0b03c958441038401207400c5699400c03a005007150341c00e182d41d510006100e41d42c140c281e1000781880001300c00c00d802e01507006411200010900414542061400a525919544804150342d424200002ca50328003000c2e400013 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 808147275 1250 808146025 808146041
    0x6080603101802270a0212040f03090b040b180d02030c1504030606062006010e06130f0507270b090d11130e12090604030b040203120a080708150109030b060103 70
    0x211291013640c580100e1100c08114100d07403983c0002105860b4000c030791089115980403400b04901c1d407404a0001441e5000301e01c840360183c41c1250314103841c2c1d04010019441980a060101d80000d030380c070124070b6666032584809000f02c440403034000700342d00840e4940d8210030310944901800010a507605040d041518040d60b00f140003049100c7c1c84101c081d10080e40d0300d05d00d070350a0b002903507000000c04000620b079059440800342840c41da110007040c810440d40c0700c000703d0b0103240c0700d13040d90300000700e00d2050314410703281ca030755520500400e40b00d20140031442e9071b131b4a203032401c10b0300b07050005404080407101345000c00c0e1032400103800c0505000d082d40c10800c01e0543e01c828100001e411000054000080302f020380d02c02ea50740d003c101d00b6110322910820301819048142403200308040783c00710240039441400902580d9440c480c0c0b4140c2d040a50111070f1110100b202c0c501030100d002d501105c52035001400c040305e419200740d80400a02043e041f0305c40140080940b00004400740d12075080000 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 808148525 1250 808147275 808147279
    0x5040b01030608280b0a0b01090b190302090d1a01031416030f0c05030a0312051501020a0609050a0f0303050a05010f0e131103030a0206220c1e031a07030606080603101802 75
    0x1780c00d00f0480e10440103003c402c0b0304180054910b0801195000d0103a00b15034425200980010620403c030205601a412841d241944400760700c0211010a51051608881c0d00d824004803d0340d43c10745c5004083c6112000b6006e503d6803050b1440034581c001d11030700809507600407154000c049800d240004c1040c0003a000150103000e00025001015004060004640c00111062041d07980f211282d04803a00c2c4052035030300503071003030340c090000c64010b03406103200500a000303031800405240c850407005460b0b0340c02100003030754400810450480c3c620542e400340c01000300389621207242003240e890f81c0d40c001d0301c52000310f00100340c40000c00406400d0180030b490068140c90720340b440c4800103901ca9004461510906540d44110b6104131045694880100d910040f2901c0c15801c003181015400200000c0c0303200c2c403c1644000c80402c04405a85008006102d0540c5852421003001015552a68854000e01641c4004d00c501581c02060b00c8000c1c1d1101c00c0001401091180b60f01d86119230844040c2d = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 808149775 1250 808148525 808148543
    0x70f0c030f050c040b03010506030c1c080a080a0b01232a010c0201060e010e1902090607081c0902060414010302090d060203070206130c031e050709050105040b0103060828 75
    0x604004000c90660f100d44021242080719005501c01c0c0741c20f0328421190140c0c1034004100452941c03602008200004281c0070080d04500c04a40d110100c0307500550b0540b0100f000c0c030081210b840b60030300800c01c285600b803034100014030003421084013400e01c115032404032020201c2e250000e84a074910740e50a0a0012203d8600380e828031071680d000f411422490700055080a01c04140b2030500d10886040301c0d1000780c401500c1e601d540941036041280103100130025000c200c08109541c991000d85061030107103509a81e5075441c0340c440c1001c55030a00300c408070141003174401005603891600391400c40308050720320182c00b0341c0030300101d00034410703080016804100c04600e03000b482410740c091403180c24203800300c86468807605a41c100d806d001003401042200501802d0000a002540c041000403448100fa0750342d9055940305070900071640c001003c0c880e07403800100300502e018003a07032201c0d40302800c00b00101820140d1071602c44400903407040005244030078040724030340f010081c407846a0b0800244 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 808151025 1250 808149775 808149803
    0x6070f0504151110020315030729190215071b0201030c23041706040f12030e101e022814070c05090f090307020d021518040606030b06070f0c03 63
    0x251300a4005075042c2c240414280400301d12410b00040250a8502c007820250003005031100190b0041c1c940b042000303001e80f050000400c1c1a01d0050400d8260a69401410441000c851010000ca000034482c504120310043e2031001c502404441d0b251030394080c40d0206210800c05420380b036441d990300d0401c1d203680c45000c200040d400303a24064815150b01c0d1716100e030b10202c4000c43c650356000036200a0640e28800e1800400110344044d0301e00c0304a11401c0104801c086010043d00307007a8200b0803903441c42d40741d0690300300d0316001501000c0d401001c0c4000b14100740c0e0250486000b1034180400c0c034451114094071065160050b110300d17070280d1342c3c1070107195508403131314040765805080e118190040940c0000f0807041d851641040740b00d441810019400c0c00c0140d002c1140d00c0401d20000da81007009885141c06a17411f010040420010002011466241000511049403065403140003090300d0840480c50940d500c1040304c5495404c000111503807a81c03803d050515001c2c0c0d51000385032503807211607 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 808152275 1250 808151025 808151053
    0x60f060c1b0f0d0c1806090905010b0102010e0d170a18031d04180807170c01060f050d21030f02040f09050f0c030c0a02120a030b0306070f05041511 65
    0x81009400d8003a11204000014801807018483c002d00c0c0040c20301c03070182e60901ca0454442d040030002d1549104c00f154075680c40c14404100d40d0844820766031079442c1c16124900396024001d81c80404404c50090405400040c8020110f07004003542089010f540d201090840c041078011180e03232100301c214035103c0c40e840d1801038940340c584d2403081c0744041c3d4003407000714034a0030703205206140315520030001541c3c0c1199942800e95200070310442e02c440001851400c4200c07014058000310480200020381281080000204201076502c00340c8034003000442c04002030502400c0313400f280c208200c04140b181c0d007c007003580034080c40c6910540c40c034030224002822521500d040d00417200c013000100429281c110750030b6040e0a04558600c8015001c00102c1c4003044621f00030582407040e4810784181c043c249108400560001c030002d80000d071554110680d9180c00d01c000340d0001d946040070000d000621501034100e01440c0701c1c04030016414411070410038090071840481440c44d90035a01d5124507580 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 808153525 1250 808152275 808152313
    0x50703090812070309140108010308090315010f090f0b0f060a021207030503070806010f020d0828061a1c0c0e090a0e0606041e05040c1211030d0314060f060c 69
    0x42a000a9420100000c59206002d20005041b4042c0e481403400c2c1c1c2191221102503002d803d055800d031103034903003609420f0399030b1518a01904038580c1c0c48071001d1400b001942954a90a13101c5c84d10741c034240c031644450350b0361400c60200201c02d903902c94a40f20310300001d1781410074034030002083c028001138607020140e100005511600c09a141c21140781c59a10046031900c051046010147e885190320344441c5000380c5185034005604d031814600400c10961a04115201c1e040000d0119126042484101c03880c1c5000142601054005400c090304420030840004980b03400009643d560400d102116110356060403001c0e401030420303141d60070a104070b00028049a15078000c6d030b01070400440c12525090143c442804000102d84113400d1614400d071000f0000030304100c440d640c220340e0000d100c0740b400a03d60326290290b01c440540366051814981458404146941010b14285051a101d20700070300285d0405810360300c0c40c030092480300c0401d4040c800d5600c0d44103680300301c0480400b4010484 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 808154775 1250 808153525 808153537
    0x30a2016120b100302090604050c0f040906080c0f090a05130b0727050102030708131703070605060a05060403110d0b10060909020f12150409061409150106050703090812 74
    0x2040e42d14460703842c41c0b07580b11191100d002c025440005500400d91602d02500207981000e10481c1d5940b4003420864215000c0e480f07640503910191311014108002c85051082205c0b8650a07200905400b4031030700041e20f900d100030803101a1581e6080466070b024420b00400441d01e5115040308080e0a001030050401c51001c070110390800313018440e1400f182150981c4008890040e001181450000e560b503001c19080215038401c1101501c00c00034240b2445900c9440300444038015581c0d0345140e082200c280c3d040100b980d4081e101c5940c04000a48850003220220381d006021401e009803140005a1128a0714201500b07030142d12040c051820348501400f0100c81d0143c0380d01902581d0340f0b04032000ea00030f41c8090162028207102c803903454281c40900a603c103608040014851051000050448910303410a4074020b5441134000030704001800950303004410301005010034541c0308940360040d481405200100302c070100f442410140148452400b618900040d40e815240781251402142c002c0 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 808156025 1250 808154775 808154783
    0x30103023f0d0309052d0607080106140a02070308030c070c14010912120f110607020601150c020321070206030408190f17180609010e0f030a201612 65
    0x249100b10624064407483c44001d9212000d880000d00c2000d850502c101e00100e00c8410004500000c0b0310500c050166a1040340c40d5115039440794104203006115080510a00171011410404031400a80018400d41280d0f030103046d90b0b0703032035898080302d090500591100800e00c0080f60b1000c1600c2014090b6000d100d2801e9031070008996941b15a85c603039480041d03000d0440c04a540014601920801070080004078904040c015041c4401d0000d160090032607072900143c10910043c80100000c08807801c400380b040c41c01d0030381c000307050700003e450b040094502810140038841e08030301e00c1d0400041d545401d4004200f592a4074050070701c1034090f4464940d0b0101404100d1510b85a02e0107914a5015008580e90380006202c1285841c110381d200a02040101c08102c445503128940070405c8a125503402400403400017188906249045250203850b903190300140085081d4541c000c030b40321000b82c2c4401202801801c0640068100800700325840710482d003201010075218902c4003030200261003 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 808157275 1250 808156025 808156033
    0xf0e0d2d1407110f0d0b0a0e030c0d03020a0215280e07030f051002270f040612021201060621060812120112030807030518010510050a0e010506030103023f 68
    0x202c040100c4170b000144000c2000104901050f801986607100807a0103403910b0840745424012111076207000606401140040c0e00003c501000950605c41120704071460701c07051110313040141c1c0d9894016441d0312a15420400003882c03a000740d035030780c00c9003407201001c500341c460311912410b280000c0b25590700103480f540320711282e0410f860164070885042200f12507514504070454910481d00021451400341d0184043d500141203554030300c650f03030080a54100141d9007240c5841400700d03020070a04c80020300e91411004100450f0001035690208a0301100800707040c10f400007801c0103000d035410030303415031180300c04081b0728141a50060280740d840488000c5660780e44c420014400202140041c002604a004101114083d4114a40107110308910241d0754602c1c2e04410700312402252610041d4502a000f000141450088200a00005895100300d5814140441d03158030041c803000f8050350000551101410070b000c03c440c80c0842c4a94400c04140d440c5008103c1d8148200d400207017809 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 808158525 1250 808157275 808157299
    0xd030e131d03030c1204050a08030f060f1836011e1104050103021b010903050a030c05031308030c0c0718060501030b03070501050c0a060f0e0d2d140711 67
    0x750000c15244116040d441ea24504030095001c4840d4290182007100c0b58855080c81000050320740d4080c610500811600440c43c0c50000204060f050b81c1150b41360051381c042c0030007140d503c44440c01d60341c4686180300c40e443e02d8510b10101c601c034144100c200440302c1c2480040944100c419084201c0d0710140c0c01c4d03c0300485090790b201c01c4c111505d4100081042e10704000c1089194003a401500d1b80003020510040301d4103058010a003540c40c46442203001400000b10103911a03058414400310184a184c014114645282006c54507501d544029000007030100c0016400409007003190740d141c221006503055650b443e50380c490325031400c0c480800359904148010030194480d11902c0c1c40ca0b80c00078006d0403881c1c40c2c4401035400d030348101d1943da00e90041400e00c0020940d2802492501c18000a00003100310307140040d51309103a0805800320400030a000e800704030008807442e20b15030f58028510784e0880510210140c0c2d2204a0f4800408407200108030201403284107401030824240680300e5a1700c0c48 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 808159775 1250 808158525 808158581
    0x13090807060b09160f030e030705010b03100e100b0f1f0206061e0f031603050606191a03090114040503120a0b01120e0703020415080d1d0d030e13 64
    0x3c021500c1001c8022900c403441034841c802d50044410794010309000801d5204004041d00319800702006039070b580c0d11a10130407041d0a00f0071905204030341024007040100302480d07142c2c0d1201070500400d171882d40c43d04d000081981c2c0e02035540d01070410080401c0d038405c1e2000410707080941c1d240a1000540128000150f8a08010b0550190001c4c001c1603000e18800c1d44081008044c4a01d1011350140300307101e0815000f100d03560680c0301860084005102519006080100780c0703260000d00c1c100064420401c00420990f0854025140f40d91140181c0b030f592403511560040c84124605800c0c0841a800e2005007d0040010070034034030040302d001c5040d5100745051090b9442400c0c518005221a28a0826126203034404141c0790780c0345054400c1e0035075a07000903080e5401109070040400302c2034001c0007a90020040d80d40f1407580c600304590407440900e2020301034941c1341070041c008c98564a640c01014440c2d03030315441c00e010050000740e100311590321150041801e0300c17007400c0300304030101202018 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 808161025 1250 808159775 808159789
    0x42103080c03060a0603181502090406080a02180703020c03040311100f0914061209280c170c0901170706020a0f06111e090a0509040b0f0613090807060b 67
    0x2420f0064403820501c4d2805108138010501d040c1099800d0358610880b000281c90520446181d0007210700250710742c02040104411a41c2c158031142c1564401c00115005848500c003ca2050946001e425200c0e075481105501038447c2080d901420301000401108000d15281082d04180043e0344d011040190705800b900c07403040b044045404100c2d010303410803600c044c0c01c1d15091491b0000c1c0a060800c0000300000701420002e4492400c2c68109810000c0300c207001603941841908070301c1c14507800201c0780d02c0e501d4400c035070f1f80181c040c10340c60400f0030a0003010130820b0640114020380011115031b03580c2c00060b142c90650300c0e91044d901841200090652000441c415100e0b04100240340803071955860038014000d014244610b100103100301e020050600d031014868514400710245d0780c0034600100b0594440903004544900784000a02000c24000e06210340c0c8824115410207043d207500000900282c650340da050446400e264442c02040703496005040c0c83d40c07055200340401c2405a040001c4 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 808162275 1250 808161025 808161031
    0xa0605040b0906120118050f2407050a03090b19060f14060a030b0a030803010510031b11190c0e0a02071e020f06040801090b010506040b07060e03042103080c03 70
    0x840304030400401c8013450502c2440366025404000050518030421072404220790000d426649600602c1401103004402d0042c40500c0e0b403100c006180783c0c40c00c50590b500b100c6002d40a8801c209010940300c090358003c3d44481210303900080c0c4d650461a080f594030403d101850100011241440c01c0002c58035403c0f1500000d9030b01008510280d088000240001d03038020803000820107440396106400790700c03624032540285008210190f501d41c1044244150064049240000c140c41e06189240c40264200300018800d00c51a08903030f0f04011000302440c041c9803005840d03000d0800300c40c0b14200080800c9002c1202d04c854120003c5503502880b40d8102e015184001c0c00800c3e4441d4035400841c03c40c542d149180c1d00c02840c0480c054081404145d0682140e048403602ea03540d00d180b84d05000340e1a58803401407100b110301030b1516081440700c00c00d5001c1c491000300341a455200e400c0e0090b505100391805031030b0a9010504c1c0c018581070f01054040a040168040b4442c0800b2030440d41510741100d03c = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 808163525 1250 808162275 808162279
    0xc0e0916030c1b0303050423060a0e0703030e120a120315080a030c080c0a06051915060905040f1e09020108070203071a1914090f0705030714010c14060a0605040b 71
    0x6000f0441d407000d03400380c20024022523480145000c0d5002d5180700d01c0c000d0a03982c800200511aa1a02200100440d00303001c11544a0380c4c0031940400000e60321000b06a0300040540d00480d50360103988589180600400c030080460440c1d82e9000b40c0703564180e01070b0307a008038450b2000c000155580c0da25a182d024210010740011904900305020440300c90041c111411038004a40d403801980d2159021100d0548001c440003e41c40d00010044981d40508251044e1060241c08414a0404c01800007030080c45024051611100554682410755208410303060444445112001041505c1c000034844800101d0100d000080840c01e550b1001007582c031401d0703200625036154202d2108819151500804400e103402c20110f40c1c02c000005400340c0c1c0060b001100c40060a0b0130304001490a1001c0754107003c0071980212820000c0e40d81c005907000c106ca00a20350500045d455100490300c80722031072030183c1100c1841c001e40300c0d04800002d40600c9204240380030419a0b4891040200380e9600105182d = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 808164775 1250 808163525 808163567
    0x3180f120917120a1101060803040e0a020c07050108090304050405090f06011a07080d020d1d0d030b09040609020a080a03020a0b0610170601030b1c0c120302100c0e0916030c 76
    0x510f201100c2402418102c3c07403400d09201e0008901042c6081d100d15422840c05038001150802501044001c203a402020f80801941000b001c8034102d940c4000500c02d107810000d612020440b080414001c960207400007400a03c5541340101c01241d0346c1544610f00600da01c94500000344c507e0303503451010400a403605c16645041d00a4440111a4003c0780100709280e41c2008003004107400c0f84502068412300d080075000c1c100e8084121401c140740005004207050a1000c0795096903076403480307194007580c8042e000800d0a007600110f03001030340c180c1001d0030030321507848500141500000c2101c0c105208a0003e4207650320301d018070001144000740e001c0410140e0340c45040001240360420341c0424107260020f8426442c400041c1d58000d03860019242c82c10421124040c400e04a08080103020010106004922199402551410140080c40da11a07440003820601c9109103000511010014860403103414640c1c5480704500d103a00c072800c08030345010241200d89000e520200700075010303024030b1 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 808166025 1250 808164775 808164793
    0x90602060718170c03010f150504090804030c030b0f0702011a0d1703011706010504051b070314070c0501170105211e16060804110103180f120917 64
    0x6451000203042d21101c2c204250b54089074280000c010340c0400c01e030402c001c01d0a10a11030501d42140c1100f50128030150512603400082030321041c9020459400345c800007805200c40c10b05070080d000e6504002c2c40d00658490000920619040a900500008040b0381c01610b40c074500ba8200c0340b00072020010010351503030f442803034034143e2200307428036000d8500034401201441a03400300790b00c240c106c4c801c01c5480418240a441c010000710340503003c161000c02681c02c004684224030700c0400c80c26940c1440015016040501c40c003850165001c0203081a501c0721618034000302c82481078010580081c8405503080c0b0925501042a030403140e000d4034151000944030007803498401c0510a0360000c3c0700307841d000b07955101014086008103104c0340180000d041d600318420a0690294000020401800c0900011030100401c45180310703001d080c0001d42c203041400540b03828081c084d002c2e02809d040a00d2805200901070740b20110304c2243c0e03400000940702d00400b9817130070082003030303410f2a88000a8 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 808167275 1250 808166025 808166027
    0x603050d030515090906090d021b10120501091a030316060f0603050a0507030302010c050a05041e0509041406060111101a060a0e10090b03071211070506160906020607 73
    0x850794010019002103000c021105004c0791480400f641c0e40000c6610042c200244a48103200d5414044040e10180030b001d40138660b03554220071000c80390b41c4100326998403000000c0c000c551107241c104a0040500040da9190681c900901c5a20ba54a46002d10704c1000d4510703141c003008944c440205c0702003080041c42a9183c4400030001c40607080e034480d0b5600400b2000c24810450401210710490003404c04905501d8001c1c2540c94401700341c4c080c0203041c00317082d580c55000070980e400d0318100409020003403683d0042240c1c00d030141c0d1009801c00680300c144014010900c07000c803401504441180e415450300001143c22040294960744607070451032144203100055046602548281d03031b0000322401010740003401a900603081d00c000310315030080c10a00b50031300e07041480c4540c0143c00d1100049107891520000c520008150303108209001c8003100e6100c015500c8504e5000b4a00a0182c45205502e001943c41600362142552840d03180c140b00c0420b885180803400303035038065025154503220300030 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 808168525 1250 808167275 808167281
    0x102011a0306070e04180b0a0f05190c0201021c0c18050a17010e0102031e01050d0b220804060504032a06050a0203090d030306030308130c0627120212010603050d03 72
    0x181c11170b40992108000b01030440404078000c00346000d1410541c2c10b0800740751034002c17180307e40004040181004100541c84003c0500340302256262180401c0340300e081101280280301300036202c2c2d4042ca50034a828820f1080d03510400200982e41c60301ca4850344250101c0d00500b46c00d1044079449400c0c51001d03c4030a000f500c0c00c92038083c102c000802c92046192003203007642c1080300e0181200304001c1e20f82e000980d0945c0550b00401059483c0310091030303103850782080d6a200400c840b503ca103030762030750503240b00700501c00600903500205004c1d25542c0341c0c4001420750344103100c113441c001301109a81816406120030004e51800806200d26061316240b030503074075a045042d0721400d41c00184000d0003591602c108414001d8400d03600001e81d94190300d4064400305004e0f015440e14016551707090001100d450001c001c0e1b44040c24117012400201c80c0d240031680c8409031103150b811000b03c2c001402d40ea40c04c08840250706c01c54050846691140d2800d00b01c07407183c400a0403d5200942c55030f0464003c1e4 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 808169775 1250 808168525 808168547
    0xe0c040f09050a06051f05031b012709060905090717030f040801140a02030f0126010905031902030f0f0310080d020705040e0a05070b031e010f050102011a030607 71
    0x4002107101d40403515080d0401546103015602075072214200300040b07071b07031078124100903040d01c110a15540c00c01c1c000c00d03564100b103802d480703a0b401c6040c861007060303000d040f0828050760400f0708407901489981c5150400d078554441c4400c80d07030401da00070444020702c0c050a8400c2206200610140d0318201d01790304825400c1c00940c01c6400100718401f04112500010006400d12400100d80b10700801910307980c141004203d080c1061060040c0303e00f21040400940c1100c00203a8126402c416404440500451401c0b205c43c0e81d601c0c106d081801c028010010b0400c05100c1500301500221205050340ca030700c207018086201010810203a21102540d0300515000104072000f0008161222885481c000c0d1001010003d07030b020020400c910724160290b480107891500103044d900030b544d581d80b6540e08040c041d10303059000100003d0b0703a048801841040d4a00141408419565602580c20300700c1c0c4a401014010f5003420300030142250004116190300b203020740104501c0d40d855000300d4082d0085 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 808171025 1250 808169775 808169801
    0x6180f1506051908060f130b061203070c0314030a020d0807051608071b150c0609020d140708070605030703050403020708100f050a060812030a02070c0e0108100e0c04 73
    0x1000040307110f48482c012401c10f00c44060b001c40206051003515860904001d042118592610342003104103000748040703946040d4054942401d6850b201d0005840042c038803031103031f041d1001082103800c0c81101c14410080304d001c0c0342c800215040704020561070b0700c10040d072880503134014850300c07948502c21282c1503803003440c1d451b00300d0038900d0301c980c00004041031300d400703541420700494005e0030303c0401c1c0b800744240612241860b004a2501d0025210396060341e1b81e50080c810a44d2400c41488425042003090582c0148100b100b048903190408000d800300400301c4103441020404a49690005050000d481258448600b03503558003104501600d0000c0c0220218058080001010503007008000950020784a021640c1c0407041e000000701c6034000d140000b040c3c10701100b0881c0141c08a1443c42060103d00d88580e00e0351518650406031168020082c4000605c42c0b0000d462013032a6269030580c0c0420090b111005d50600b2100150b49170f00c610161150411034807240986429485400e00e2104 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 808172275 1250 808171025 808171031
    0x320f060607032a031706221e1e090201050d09030e040f1b0309080304171b010204030303050903130b032e03050c0111030a0c06090b04030c06180f15 65
    0x501d141e14003a800700c2450740f461010840300b820300305504103050100c1000500d10404c42c0b4540140090119130901d03202000001c01e106a411401c0b070707107403c5864110200c0140b65944200011a800149040a402d040740141900500f1208a56000b07000c69a5016540c2c1805c0240820740c10f00141100c41c0d08a0a0002d44421400d05072680c1c019415014a160000540101030303456040c841d080510341ca00c10546001d5012000070070711021389401c80d412510380c40d900d01c04200441d038180306520003046100c07181085003006081c15001001541c1c841e690038040d40e00c40c1c04003159603010b021400c2c0008a18000e050150184080107103a0040341021403d1200500e9400c100c1b448155003440e00c803101100e07500f401408000c0200c4060124207107070580036141012051600c9000d030011900c20800c1c12408941442040d40140796140e81000d00218a81000d180c0038101090800003250210f04010040c0400200c018040100076044040030400c4a119a510510894101c0c00c58145541d = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 808173525 1250 808172275 808172297
    0x6040302090a090506060a050a0e0603030c15060112050c0a0e1c0308010e13030203030c07030c080a030518010509030919080604050a031d0609060901090504320f06060703 75
    0x50360301c1c402409800701c841c00154071021402c11354101100202594002c0720014010003164440c00500c508071071001d040040075483e51000a8203510901401c08a5440f42e580c81c0c3c10141540300761140288000d88400d1001d05501003c84203407001258229007204062100d8480345000d0414030200c040700500c0d500400f10315400484039002c07517a00560000390030b2001401404c9840c240c0a03080101c580383c254101902d603500a6407032100800031150354401054000401d40602c800c03c401952260803541c0760303010a84000c009200c2140c1818140032801c00c0820340308010f1007010b025003140409146010485018091085940e4401c1c1c121200032100c00204c240d01404502d002c0d41c0701e03401170a1241402c0c100107200d2010984030041d0031280106000c1c1035036440302220340702c010940b05240c8a81e41940141c821610580c0041d42040c1081c18a0101c4040d81085040340030110b01c5068611600c000d0100d00e90000300d805c0180c01d405030010031090720700b41c809041c0c807520034640124400 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 808174775 1250 808173525 808173529
    0x810031b0f1220090412050904020406120b010c0314090111030c010615021627050f2e030b0903070c030f11011809150f14120a110f06040302 62
    0x1d8540c48240304031000300104040145500c296050400d2119030041c0f81442c3c400000c21000c000f4000500003450f20b280d09a00350300030030581382e000b07500800854980f039540c8000f400c05405981980703a00c501d414080c503801d6014040350716155400d42c0d24004507103004103410006503c2540098180400010b05d0b1809044c01c0004251a10240c2d0021070040d2500c00e44c03040e00c1d400d030310100095401254900080003e460b0480088070242e200b44249029070380348400c1c554071543c83d092416410300341084122480b40861030302a11804440381501c20a8004d600003140b0701240201c450f45204c1820400b29400c041c00f1900948902c7c10b0741e2810406a031000c043c0041a4070480380d144c407015400e014000400501070821100303080c8503006c5413029a9285800066008440c0d107290b0b100f2040500f4001918520050541040703220596030310f0311300c0d101401d0081403070740d071290201e80c190444880740800c48000c5982d00c041c070214069071007000c204021075103810880c0c110405010000250f = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 808176025 1250 808174775 808174799
    0x9060403020d0609021903151d010c081b040602060a020703050c030d0f050a050f04020d050c191e15230d0f05070206090c0609030106030f0c090c0810031b 68
    0x1d0b921035400042d1202180c814070680f00c0e441e4003000c1800400980800109032440340c200744100035044005001340c804104500c1000364407810350265840c11a14150f22074001140500038201440c101060340306981081d0001c0c810b9000f90401a00101c0118840045540207841d042c1d21904003181031801981c042841e40c2c2044145601d52030f250208028000d10b1485416040b615031007090005181c5400030980800c000b40000380500070880048003030005c1803080340c0504000401c41540d025002c080c0c12503010450250b4035a1002000c00003000503059104081106c101020000c00c280602c0e00c04c0d5074070100071030441c0e4200c840c01c1e06600d00100c41700080c00001850700b13001415490f0608100b0481d00010680800e41d40300a050041d10140080e03240f80c100b208a030410390320800003000c01d014103d2984014140b00c201111107040040307080400080e1100a0020441104004011103005405a074640ca241d00c000e481480440c0346245092014406445070402c00c40d5113059010314 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 808177275 1250 808176025 808176049
    0x11070905190b04110a0e180702011d1b0907090b041716030b1b0702120129060409020c01020903060a0b100302071109091c03140f040312020906040302 66
    0x3100750201c2500042038124840e800784040c0030340d030070050b108410011034a244207003d821030921003001c41e110100c3c2d4070f54200741c00c02ca14a07200700460b070800c0800a030103070502204588000c0c24400750704104441c0020550241c4d030600441c00e40a030f01a900784034030810302411090800c0340070b510200309100e03d14003c0009000468412142100841290741025864020aa84442c0303000d01080494502d055443e0031a8804001540c128000c066800092059040094000f0321800300c11006071030650044041d5102c01c02882542c0d1084104102603400307100d101d5500400038030041c0b120140540c0a84007600041000601d00700440700000e00e40002180d40041040c0c9030b515184880c24040724a02c0d0038002c90400b581090004d0b5030307100840340c40c0ca01ca24021901100090b440c02c00801c4008810b2800010516034001030090040140220b000e240c0400081c20002c5540d1034022940a8880d5405640780350803400d007002c2f0303940030354400b442007503000c3c1090001001598440f004400 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 808178525 1250 808177275 808177291
    0x20f210102281e030b0a05030a1112060702030f0d0b310608030f090a0b070b04020f011119261308030a0906030e010603081602090c0c0a0311070905 65
    0x200c1d004034000350350300c051142d000c0020030214620880c846501d40103220242e035542d040204291000c803022490040300396202c02d6061050001000074415088001d1400340790a0714211901c0023102d64695031000d00b0744100300180d1040102020a0a590001d00354500c00c5170000b21f003801da40b0b80020720f42c0c584030300b070b042d0303c00e152040001e0010000c00c3e040e001020050000d020b454a800c00d10380d2a07000310b5034000d005001c0010080c2e0641e484040c9100a41803c490f00d64403070305541018280b1070401c0300c00724010a4061201c0b00d880d07019001c03407609009a500100108480310480030304900c00300300100c4044045104507804000b0701c0000d4400c2c070088003501074541d49020480c0f040c80040d035014102d02c0c0c004001909003543c3c40350842060300c0b09402c02080c14a0751640d1540100160b510140c6400c102090008140304281a0300208600880d402d000c3d40d1941580b58032148100341140060354801c1244000080c014600b400030035043c00103032242c03180e4070002e42050b82c0d002c0360100 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 808179775 1250 808178525 808178557
    0x60905010b040f05060d26040e0a0f11030601110f0601060c0203010b0f030d180b0708042d15030908030c0304050609060105010f0e031c020607020c010309020f210102 73
    0x107409007401e2040e1095001a01d1003401142005d00204589000314203015040d41586017500162801034524400c03041d0451030204c1da00e41c0e583d12103200440d03056549564590400d0303000080c006143c0100506000080d415034a19140c580c0191513402022500212074064050510314444047c09000d00811881e1a458060300032841010701710380500600600c190000c0c130703c0c1c00c125140000c41c0c0b42d200c001d90030041103604062303601d005800810b5020000d4460001028410030803840c2c040c00403221200603884075041c4140d28102c14407603824441d100703541c0e494020403148413404d6000c0340e60195410001810050f6440e005019072085404000c00c08000040c402007103800c02c0041e03800448403000c1c00b002c0d41044002843c480b518501942001248001c0b01413503903051190031002200e04003130b1a0403104158003c0d4540f14225031460250281c5e180104455009003c1d03200540d0b401000c449602c01c0d800c0c01c001d030054503042c096403402d10104905103076240902c001e01041c2d9102c1440 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 808181025 1250 808179775 808179791
    0xf12060e1504020c0d0e1305070210050a0e060a0b0a05131b14090405060406080d1e2307060b0918070605070b07080c1c06090606030e0a1e06090501 65
    0xc00c000c0c00940801d80518410400c6002000300494200c024000501c3c15620308608080000c0070504001c102240c01c0786450184400a03400194505000009a0041c86160f8404100300121900b15640364400c1d0417160002d4000181035026000c0580c0042200740b225441d040800d0b410794411100705442683c501c50011001910300041c1c2c105e00c00c9140c40703108503540721001c3c0210b000300403581d800350341c803a030204040d641c458100a003d00800011204900301c03a100c014620461081c10020b00344030428161441c0d4468481107101502043d02541c5044148469040343d5100050a40354a40c0e42c00510046603a4240310034014050004c6500300320300168412820441558040820700c4420446100001e8113100010307170004090030800c1d100d41e62022042e4551162025603040b000c019042c082c14054150302c1141510000c034001c000680e1103001c160220358820400d0446a4000000480014450000045140e99000d038140203182c49554560549000c0308044405944a080d6 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 808182275 1250 808181025 808181041
    0x5030f1c0609020301081f0b0409080d150602070303120e25050603041a040c180e060603070f0e100f0f05010e0904020a060e1f0315090204060f0f12060e 67
    0x80c4201810042c40c0851555150403030741c0d642e0740030303a84100b090048080440700484a140d842070480b41000350051010007400d00d442195507210100c03414100c1d02e054402c01c400400801c042c81541e2392600146103a40c00e5032400e40e103021140c4d0110b6520364a656424190361001e200c4103a081c21458800348180c00d4007844040d512a994015a000d00340901c00c000106941c4081d0b800074003551582000c480d1034608210f0303201c85060b00585141c40029892000c1e0500c154080318180c5080800d4070b86d142c44041c03c254807480315118401e40460300007018440c91080035565600f01c50015000302101c0e6450000b68085202c1d68132074404440019020040c03940c00035884640c0c1c010441d600302c16890700d03a0001e00b075130070796009803c2000a880617034031041d21180f0b400c00d208100049001180b02030f003c4002c0140c0b60076000141c0d000c1d800c0c0400245001d40d40240c4003640e040d611840101000c3c00811212031002017642401c21a0000511750808014801e00000d00f1885031000121310b08109 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 808183525 1250 808182275 808182281
    0xa05150603070e0c0403020d020117240a120b220308100501020303070f05161a01080f06040f031d1201240e010b0f040b0d02030703050f1e0405030f1c 66
    0x10059120040c0c0204000203d100001114203680d41108c40310071003881c50004a13450584268401443c400701e20520030410603803000c007075144501a02900c18002038100b801440c2400384600540368020788400c0c00010721107507601d0342c840c0d84c0200070920525246070a144c400c1010000f41c0c08144c500c010b001049141c3d1100380040d1000b030008510354201988014406902c600c2860100140400d0025152b4801c100f407480e1150001c844000e2031085003c156400c0000b8890307010b4600c1160200d2420701004601e10b4031483d080f420860060800780c506a407442100284504e2040001005d0b43c0b207581d84150031008a070072a4000202c1d00c650207040e401881541c2041961540c00030420019180b0881c8910305590386060140d490b011041d00305100c038092034200b884002c02c0170400d10b00c0580c4a601440c8240440d68042c40303152150340754010122429240410f18204240480143d04603403805a074000e8440c0d4100c03441c0000319208440c2d150000e00c90307612420a85002d816055003940 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 808184775 1250 808183525 808183529
    0x20d08030c090427060e010e0307060e0610180509070e070804020f0a05220b0d03020d0906180e09100e0706020c100f0c0512030408030406050a2c0a0515060307 70
    0x700f0201090300e10380c03031900c046010303c0100400d290b41703070340c580d406c1640300703400c10101010003900320f036100c00c00d074905440035181c2401018082e118031400035800706000d49242044403203240ea03058044558024800107050010040443d92068040c0025119001203850b4401c07072080e503030780d40c160902d8070410481d0350903000c0c901c0c0f01d129000e4090125581d4009d038810080d402503042440d4241468034103014100c5050001d40c0700701d4400e0103406140e000700d00b181000d046a6698800907407101305c141c5109100c0d00c0004803034800d0300d00601207002051801500400d0000848900c409900c0c01603042d1034880005140711b402c010020840c2035010090140307414004c840e5014001080400103148040140001003005072110349502406024031a00340560030003036155580b032402742030a10f061b500990b011a4003902d8680001c000030350601c1002e401c3c82c0c1c450715400300101d00340b03402c007084401180c07007240c01e0086220003400500108480103980500c4907101e211881c1a03000c140c1012525 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 808186025 1250 808184775 808184801
    0x3309050606181609080d02030304050d140906030403020a150c02010606030e1b0105071514010b07050604060b060d05010f0819031e140d05180c0a0909020d08030c0904 73
    0x41c514031005000b220320010381c06a0000407a88821152010855095009910419160080000c4015101c0d404002548294084c504861522841c0c5000315038400182001800d850b40500242a8620703040f4000c3d50420300900c115800c107007450b118000d08500e02e480302451030766103a466108598081c00342c500288000d0074104004056072000c10340703440c8460203120603002c00f102891050b0303001c1d0003550700e441d03003165400072601078800903d402080000c031641840c60500b4000600c0c03903003600c1221040c1d81c0c0170028003004d803183d5955102915192405c158030810620407001080720a2281074000c000c2e500d0782c20315a9191021041c100361200c085610754510f1905210042a00039480c900725002c0c0c07414403161f8203c09041201c1100c1c1044a454000f10001000d03601c2440e075810660151041c0c050440c01c000100410640d102204e00403540c07c01d060000812850303caa40c000b500e150b0025000c195400403654403401503502c2114412444503001c01d07d4103c40c185442070504910031 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 808187275 1250 808186025 808186039
    0x706030b0d0209040222150e070f0e24090a0504020309120f0d06091d03040f050d1106030708040c050603040206030f040201090504051005151201033309050606 70
    0x450302081400640107800303030140803c500400d003151103806004800b6030b50305d103d241c04120030305244000703031103a02e095005000c040d16003c15490400e42c229809448030740c407203450b007015454094031007401e62080d0f16480010b000f004035210094102c501c0801d91100006079a83c42c1644c100407040483e500076a00030b03803040c001c00000b050001040c1002d4000c2c0c01131952610280c841c4080c09100c0c241c4031a81050506400055408480d006001c07840c2042c040302548001d1031005956a016034864041958039901081010341030001c800c2e00301d1402a052002d400d12a400850210383c001e4514000146c3e142e8100020302600a25031009014112022031a5040c41e030002101e5001c06030101000c10340540229085a024030134490040c0700207401407200b484c1990403142d6001242c4686402001d40c4245081002c03503010444290700b8440200c0030381642151a049290582110900d6000a010b2480c0855403c1821031613400d4040c0d034800300d0410001d01e442410824040c0c42a40100d00d = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 808188525 1250 808187275 808187291
    0xc0307050615100834110c06030610021006030c05120d05072a2603040f060c081227010c09090203100b0315090108061e040311031605070603 62
    0x2d615125210442c1042c54401345070b482e03052820503c4072402498410500c2c40880b008481c502075a0796034130162007a1544080d198440074401c0c1c4403402c807410658841d404000083d4280352036040080b00c440c292040702c0c003000f2105251400ca0b400c41c6c01c25a07903001402c008000e00d20700501103500c0d0403c08406030600f039603002d8000d00140140b110052403440302491088000c0c0e0000c00000e082e254110901d60001c0e41c500242c0d6122000303985142c0d0400d043e0340ca0038504200001220b040b074028582c00c202c100d1400c04100c940050f090400c0320f40c0c801c2041803409865010104074011800c1e0340e004058031000d0039184c2c0544198849a04d804d0b41001e40b6085100d40006182088400e0307401c0150352669030501018004156802001013110040103110302c4406210400e4990001034030000c50303690f280c141a0390b584e10b086440c900c0c681c140801b01c03180340040003035207030300144641040c04060b150f4401c280e0841d0403a1034000341ea00c1a0f1807204060010400c034410042c0114141001034003 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 808189775 1250 808188525 808188529
    0x15040806041523070e01090302030a06050411090403030e060a051608071107060c06061a0315040204120f06061509060e0d0c120515010501050702040507090b0c0307050615 75
    0xc40c01000030306180480b10505940d03240076001201040140d940f04140c1e01caa0b900b030310045501c280c420000160300380326603401035401445804280d980090003040510306a03580c081c040c10004104403a650240390294099880e0b9040440c0100d210745c5020030901c900744035003031801c0e00041c00c1890b500d081070107010441c0300030450301010030070910b001e9010340d4940b0b20686402c5c141085544040c80b03011400240c0c290302100c03040319284a00014000c03250b1700c1c0b6070400054021100022080d000300003040010403509500036460b04007070400743c00c1c00d9883c2404e03525608518810340740000c1182e840c004102507840759002500c0d00803030110900c1804440180b91160034000c0340280070108241c111540e07111020001e081d5408801c5259154403001c840d1342ca400e0001040f5820b126031070526144a071141c843c1340c180ca4041e5101c038141415a002c01c0040c140140107001803002000c0301140b0080380b1002840c00321000302c025a55480e03103151162400c64002c1074910300c00780700c0010140e40e03 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 808191025 1250 808189775 808189783
    0x304140108070e1905100215061509130608031902010e010510050d06110c030a0f0c110f18090102130f050a09020a2c0901050904240603050604050606150408 69
    0x25500a45030500406003030040c0711308400594219560003d64601d212000d2540050078441840b01d051601c052a2104800d003d10b1039142c401440100d04144441302c4035040100741210a00b102540204040b0b90342c141081c02c541c0401e032011b0420aa0003900020103409010300420800301c00f008210514200906c485080494000c5a200b880d0b0f02c00c400301800541d42003c11040300a1800360f60b07401c64094400e079240d1008452101140c0d9221030803103440e00608680814a2708921440d0754165007c041191026294840d04e60003039104012401c2d03030000c0d03032685200740342079000143c1e144070089801825400550260700d02c03982040080c400d9450703410305401112001300015854484250301a42c1030050801d0000d5007940c10304410351904104648040d2441d02079414460303507602d60701485190f10b03040703070080c3c00c500c0020342084d8030310f50400c81140c0e42008548005001c03a103d2b503d071030800c40261415070707203030740101c0038080c851030720756540b0682ca58400c500307910f800d03d080706998071 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 808192275 1250 808191025 808191047
    0x61824080712050906070e060c060a02030406020c030712031a010c12031b0e01090b04080624030d0e0301050a1e09050a0b0a0f0e19020609060d020705030414010807 72
    0x104035614001c5050180140d091201c800607a40040c040ba02d01400c0940e070320b5004540e28000540144865800303402c0500c2211889001c07840031f844103544601040d0060b42c0094800c6465650801481c01015401e002034400c0a00c204640980c80d101c1c000010151084089061411030041142c081640e80200060074442da00042c111010304143c0030aa00034141d210354568645014042400c41b540e0055000c036042101340c07110312409032149407103001c50146000f42d0301c03650700c000041010b811040c6102000c00d80c002060089484000d00420f0810b10000c10b02000b090040180f00002d160070701440740e00071410501000740720b00b264040c480843d41e04110741c9003070744d0700c1001d4001d01105000c1e0a03000360f002880f00300542407505405004002c0f60032608040391400c51900c0e05d5620128107407410300d01a060401d030741d215540800505a00c816030184d4400301c02c101440c001200c0b030019200c075034044c01c00741d5100c91a26104005009000c0211410000500c04200d40140c00c44140702d1 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 808193525 1250 808192275 808192277
    0x120d020a02040f2d0e030a1b1401060b0a0e060f0a0c080c011a0103051510050a0912111003110d05150904120219020306010905060316061824 62
    0x243e08009120004000e180304085040902e0420908015810340c02c1599441110070182c2003000300485c0340056206c0c010b900c2d035000050b054200c1c4c2c210700784c80e003188198040d010742c051040070011031040f0f80c21a181644405560407000c5002010190002055072215606580321450711400300c0d501c900d540f007140c00601c14000c0d0320031100c0134440020300b903560040d00c82c40200000d0030082c4c51401210003000840740081c4c00d08001034807070754819075a203103a00c0c8083c0152064501614040d1029013203101200b08005840c000080c0b2400340809102e034541c02416000d90901e0a44140300301c402c0e1084018083c0b6081c0341c02c103907941103418201c400c10358010700005443d413550a0303040e41000d51800c00381e510030300a20a00081c4841100d07007001d4442282c00710b807801189100b8209191100590180d8503801c0000100541d42c41604010fa005200074113555440b5001442c425003100650014000101c0d001103045a503001c200c244000703004440000c40034848554103021203c401100c01230 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 808194775 1250 808193525 808193531
    0x170c01031a01111905010605091302010215071115010305060f070903031d0415091a091504060305030a08040605070c05100f0609021605010b04020723030423120d020a0204 75
    0x10380803460501a6020a51850f8000c04d810701c1c980c00d00070b000c0c24a130300885114480750300115480b03a164140d03101000d907042e0050451f0ba092400e00a01e480c400408640a0101c140c0d490815004244000118100018030344030ba15411410844d01d0990000d003104910030945081c000c0450308188030504407981071415111200707011500c040c0d1080710728055504141480708000442c040350101d5020303a810034030200000c1e203c000d1510003080d00303c404680c22400650129455801c0e01540880c1e1803400381003c1082d558940d2014a1540300d6441000050a600244010442d05014032600080e4901d4400320002c60307502c0301512102130030040350b003503039562103118181070076900008000d100220046403034024101682c011280410130490312540b0305404400715203001d01c242d440c6c40f900103070303a00c00b035642e8056150300d4102d040c4440e030400d200601000860108a82603507107004242070440c4a0380721a94244042c038510740f0180001504120301d005145503002502c4004036070112404 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 808196025 1250 808194775 808194797
    0x12090d0b070302070201020c0319060b06090d0f030306060906120e010b03070603020711150405090a062106050609010e0a021303020d050105040203060c030f0402011103090406170c01031a01 83
    0x9442050810002084102060200240240c00d0742c00303055514004c2e020358034180e49410070907844034990005070050103c40300040c00031503000d502c0a20101c130050840e501d081420400074005420130541103c100742e899910b13904140d8580100001040309003030070303200789090807005810901180c82a540c425560341ca869901038003508120b00740c22000e030948404a88400b401400303548400401e80c1d00158847c01110075040604000b030084503504001400c0070300f018100a80700d400500b200312705503120200440d000c1d075900b9415154000c0300342c080926110a00e4290281c0b8001042240309041c403034010022145051406640aa03203900010f944000c2400d0080c40302455420103500540510303220f00400c4015480140074a000310110741255490fa011403a96203c1200c1d507558a0080b0b00202e00154080d042c3c6151005511003600c0c1000d00c8070303010074200c805591090751042011200c03100c040c00e00b405070170f60a800078a01400700040d524601c1100c505804060744c1040762103042 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 808197275 1250 808196025 808196029
    0xf151707021504030203030a110c0606280f051c050d03230f090610080c012303040c050a0b0f040e0c161b060302090108070e12030a090311010c02031209 67
    0x6456600c80c46070341c08102c542081c1c20002c0d0f60341c0089030000b4005180901c01d040740100141501d021002003401080390765141420320080b200503d042c2095071490001c10306041003c01c46007006024461803038220949004208a40314981c00341e4a00b0040f50100400301180010486813012055800c0105540b00240711101c644001a01400400849d801c24001c0d0518801051400b46090307208a03107180e00c0b00c500c0884030308664403503d1036070f1b4481d50300030145500814204044000002412820b40c118000318109a8401c03036013240c1c003106001e41400303185810039000e8041c100d13a0104074146024126082e0851249014410004841c100010381451030303041140c4d403402000070b0000c801189890705040403004603488102d04150007001003140343c80b071b00c00d550109005035546801c6840b00c1005507a000703a030444594100c0510100c01c80082000c00040410306d019a075880141455400d1261070320b03155030880390410184c81ea1074000b5a4000a00310f42682d00451041c0e610020000 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 808198525 1250 808197275 808197283
    0x3041b0b070f050705030f03030106141c09021009050604180b061c0b0609090109020c0a23011d070b0307030b042d14011202120102070c0f15170702 65
    0x1109404001000a0001c00c0102c1003186a0926119404454619840300205030b1919030341003190b09150320a01c01040f1036841001c03003802840c0e00164207803501380003031606400b200c1c110b40c21941154070380c001482103003829843c0d405101c405d4a00074180e42c0c00c0c8000101720384602e20034941040c1403038850f00c4003075034103501050345140c0c0104019618078280d10350600100c401215410550b16200c0103101604094088800c803110003060010309038200311000b00250807030071300c1c0c13501c0d442080ca05400050b14200080855a403c956607022255490f43d0f05080d164504120b84040300c0090001029600001d07a0406032a02844610b4603680c43c1c8504500401e011b00d0002c0e80941820041c803454105019100e1400c8080c84a0b125990f54000030b00d03007038401d00701c540011300c142680100310404800400000d03551000344114a58482d0001590a9070440c03d4141c0b42c4003000c0c44104008595030202c000280300000e0301c1e040412000001501515000200a50f0200300c40f00040045100744 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 808199775 1250 808198525 808198529
    0x6050405121c0c11060d0506091b071520041e080307030f02030d0f02030a05070e1e0d1505010501090f03200109091a0f060c120c070819021503090303041b 68
    0x1e0b08454540d408900c091b0040c010540d9094040e0b00302ea0701256818814901041e40b250310b40780c1d22031900c0348980c3e4603071201b4603012048841d5681c4041031203400c5044522000c0070301c0c001c441e03241c495080160128640301d1308410710790103840d01307042040b21360f03004001d940f802600b60810301b0034440c250b0800e03400e42c49000070000b02c580c906410781d0b44c10b8110740d014502035013040c00c080205544100d0b003a00c400410f222903582c42182c00c0c2d0300542092282d40000d804e450090101c1021404aa03100c480c618050b5520340700c02525040140400e507031141c039200003864080c0707200e03200c1c0f031442d160a00c2800d101d2480c03d494207810f00c8101a20b134043c01401004007541d4204100804950043c0b41d603a00740340c203199100e4682407a04804510740381c41901d00c07140103140600b0300444405400724883c1d218003004d41c40d0340191a40042c03507404c14482400d24440240d40c503641c56034284104a0140760201d01400ea00d0700920911044042c00400d40e644150301c02e6001f00c03a810034000c10304e0078600070303 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 808201025 1250 808199775 808199779
    0x10302210a051c05210a02090d0822030201080a02030a02090a09050f0106210207050a020a1203080c0f0d0e010b04050a02130e0606070b18010606050405121c0c11 71
    0x284004410040001801159043c28141c81581d20315180000c8806101d1341078001140c0c0910200d050818051a00c04c07900070010250052410103541c0100303c0e42c404412040e030340900c000c0303440f07a0644010410300d00080d060508002001c0d007036600103051004081c00c00c13910264007000150308520303036034111460030074002c2c00105071a68034440c440c00b07414104e54480c0c3c42000080000340c002c0c0928650030035140070030744d0026000c030211000c8009401c0400d080d01ca600c40c0c4030702400541c031482c0d07081c4090061041d00d0041d04105060151804e0405080803041c644100702c0d0003100541082a101441d0840d1404100d2205802e0350902502c100d00d2110f62183c034040a010107007400358002c042074003200e10b00c0c103003241d0748001c0d80440400417241144c10201c1013200302d0010b1300e000003031544000e008a81076072802c101c0425500b10f84440d000f0070042a40001c040c04030b4a400e054021074117200b00018000c003061600020780c5c5d501e01038800024014001218410004401d400086400300 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 808202275 1250 808201025 808201033
    0x708090c090a0203400c0911030601091509030b0603030c0d0905013009140102040306230603120309030f031009110309061f030506090c09160801030221 67
    0x101c0c0a100c0294016980300000c0010015081601c05c1100c540c0c415001d020700c400c81d8851215071244280b00740e000d0003203551048002001c196100c1340e00c40d10f09000e1041c8416601e92500d14009090000345400803540c40340700580560510b0381c000c600e141980ea00c1103880391030703407034640209245006810001e5001d00621201140c07007a8044440011228266100b500c035490a441d01103e640400d203048904641180111005020a4000d0300d4894031481d0310b01071601000340b0240c01c80e002078008841c2c0b03644840b50056803041030b0360702c500c0c00040f680003248107003021000a5510102030164000c0080c003c4001900f031141841920006902000c01c030303982c0e00c0e22900300c0300f80480d60301403c041c40346401c01d04401c20180710140c91040368103600420a41d03c1e03041c1094890741700340d0081000310708440804000117000340003560080e1410380060030051030400c200200034500900b1a1850b4545006840d0066403240c502c604594064540200c0d950044212003003d502d00a10b0300c5031441 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 808203525 1250 808202275 808202281
    0x30816020603070c030f11030409051803040915240e0301020d060f0e07031b08061c1b08061e090f0a030c06050c0a120b0301090213140907030b0708090c09 68
    0x1130010100952680703e690790400940c4822400e5850001003550b2290b0740d8030500007440241007030f44c1b0050f0888160300c2903c448a079a0541c1300d18580c8181c0041c225291100200441d0740401c0d0f0b0440c0c00b81a01035101060514800d0100d016040420607510403ca40d5119403096524203604031440c40c05400010710016403102c2108a040c005845981d00701041900040d0a191280c070900341b9407282c0824807086a070040d041140d00e00806041c60380d000c0707454900d0f0045d0b59018009401c081c0d00c6800149040742a030400155a070b4400c2e40214100e8002000f00a41c00004646100c820000b1617001c0c1c2181e261803030721a00d40007070b020004151303100318003404081c560000c569480103031040c41c040c4010703582c40d61040c2c2d03d80500711059020900c03019559007030414a030011540203c01500000703041d5903a0700000c0c0303514880c0d1030042030180d4803481c422001d0461040107500412601c0100040341c9076907204401502c00616607010072980c3c0b00032605250080c098808030080c020034007500c0c2d003 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 808204775 1250 808203525 808203527
    0x5220f08100911092721032214010f0605040e0d090614040302090f040b09010b0d030c060f051006090506190318060f0c0801090b0904030807050d050c07030e060f0403081602060307 79
    0x81c0c801c4405071204110700604084244c102c904580c4074441c003648c100c00c20007071006180c031b00c601840c2048443c000040b04240c01454244a103803a6142c8d20140407800300e1620044c002214200300b510000b40d0414821940c96603004015041140d0b050310b80292a18034883c03000c4d1244c0116040254012104070a1014041c0801110344c06607000340041d0003a924de540101d0701f02c0c0c0780119900c0d04115840f000102003400780c411510711368041c0c2801310308040303100880340482da005c98030118000c044040a012240d48040f41401411043c0d60b907074039041c1c0f180c5020b040e8441914449080544910100600c500c1c2c1c0009a0075031684104140000f041090101c005010801c042d0000584543c00010f150a124060020600b00c0a040b01c96283c0703d0340c07012581a00014444828010104810b941d02d00b49841603a00c5046000b445a032540041d1030014440100600c1c5140704010174000144c020307018000703c40803a5071014141d0384d00c2001c403007055140385054402950200c008030410400c5 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 808206025 1250 808204775 808204783
    0x10050301020d09060c0908101e14011403070e0109051b180f0d020d060c111509210d15050a09090c0b0a05070305220f081009110927 58
    0x1c2d02c5000c040c0640c0d90904011101800340d8821400b007913200c0c0309201c0e85442300c0d910004c18201186190603803501004460000d6601c064810615952110010020350b04000c0300388007400d0084001d0004103140a603088420354060194140c640d50710404902502003a000c81c001c003196020700d0304c0c0c588050341c0141d1124031041019034040d0710071040740c40162030010024211140e0092080c91720203440c0d02d80320014034900b6454000d00903010340e1502e208008000c0c58458100a6502000c0761400000c0741d03040c503203182100e204400b8680c9004943d040180190307100c4098002002881d80c40316810760603114415806035410204481000c039024485810040c0124001c031400303080d65075074840c1c5454910036600020f00054080c01040c0020344994020402c4004c81d0101c0e08142c00c0d160f03c0303258010243c0e80322000f0340000c848200490350050049100d004101501008400902d848a1508500e1054a280b180b946500010001e1403e106002001c0500e0440c41c640145a01c6900713581d = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 808207275 1250 808206025 808206041
    0x120206100603090218100905010801090512040e0c0310030c0f08011805030406120b090a09050f060106020c010809030c011b030b03070515090120010b180f010b0310050301020d 77
    0x9400c90105010034400e0080c061282c400b40d011342500c1001e020409441c1c0412800b8001c0c005103605d103140020106880d02401c1d01a180c11000010400964904103160a6000307018000080c41407108100400c1003203405544144d003071044966a07a50301c141c440390301c03540b0f07000204641000381d001319651001e41035503025100f03150000c01003d140340000740f0032f10704144402030656104100520071a0712a10034030f40130144405003c01c3c06050b00c0c0000e0110a41100c4c0c0104003a5504d03603913801e02000300003002d2038110740d0b00905215410701c800203441e083c0191515060005540100e00595000c00848400341e0b19074001f041160740010702d068100c13040030318500001f414031100080e941b4000c2032513001c80d00010640710340c0000c111140012500451003180c144039400200d283d440109e807400404d6112a00c1c00019111040404c00c0404007101409000301208070040102e107054250a5605442406060310b8032a07440280343e0210314401c0e0015034048d40082080c0c0407802041e0011f5134 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 808208525 1250 808207275 808207291
    0xf1a040b1201060e34050a09030203060a050a05011a030c0901051621020c1c0503160813060c030c020d061509050a0509030712110102040b040b030406050604230c0403120206 76
    0x202c501040460100c00301840d000f000100a403d0071704980841c0200700900c2000c0c0c0030305001c1501c96898000038200002250b01290181d200d404124140d9506d104540c05842003100c2c0b040d80381c04042c0c40e4100d6000003420001d81c080d00051a03090390b80240c060340c0e05015000d0f10450803a0440c0380c101c403210b8001001c00080d424010408045c0341c0046880410050041c1c001200c603210f040c82085070340788a90301510b1600080044070707200780b10030740d4440d60140901d9045985210028010003180160b82c4001c08202c064022440042d50181d0044010341d0101d83c0100d084149081950090100d0760882c001c0005407140080c2d0623010340c101c54816540d0700030030001903440f000440d440384607021004003140d040200c07000d5061f000d0404850305008610005044c82c1d1507a40d12207480d40560428015648080200306c100004ad02883e170780040255005d02c019986101c0f1b2007141e03500c1c5806207a80d0095000003030803885481044c4d8006603045051000c3c812800c20380a500c411080d11084 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 808209775 1250 808208525 808208551
    0x80f070201020c030c0d0f0c0308043b04060203100918150b0a031410021b0c0406060e04020a0314070e0108160906030216021002100f1a040b1201060e 66
    0x68604c0c01040903188500007500382c0401c41c540b503890250340781c0750301d008840d58200400d000c000f0603001401b900c00342548602030700601e8072402941c0d5000c1c1d08843c5202c103241c0302001003466242000321442d00503038090030141c0c9a0700c4002c241d03210320b60690450b058440c40c14944504491580290a8103140590700c00c0304090a1215443e0694a0914450344c012000c8402000015110350604603140303107003402e03a01d103008081d0410040c1ea101c01101e41d0320001815100e06c90950174407034048183c0c0101c40400ca00c501d07008010340030a00c205601c2e4400d5034003181c0b868105010303411480c405001604c418000d8070b8920009800c0304040d03080c01340042d6500740007a40c80e51445082802009107501d84d40142c61801d603048000e13500078505803030362280300c411140050b110001c108665000c01e402624152601460742411100141c0c0501e100c1ca04103039550b01c0e04000401c406405520558000c980b60404e6030200725415040c4e0503039a0301398a00100007450401c8600d4141c02008070030300603 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 808211025 1250 808209775 808209793
    0x2030d09060f330308030115170702030405130203061e0f0607060e010b0109060c0b06040902060a0908010b310207021507030905010503061f11010c110106060c030813030c080f07020102 81
    0x14034807442030fa0000401c0743c04c00f0030051141824008100307001a606240085d64020440c40301141040103507807440260b0f01c081410300c201d180004c004079210304501021419480c1020001d00721030484038464507100360700d680382e51041e111690140d501c440e0290a55940305840e141690080800c2001030220794680050442198404d4000104a60045c0e48907001c1c411151502040c07480080c1c100340e0b1003a521081000183c032a80058140450f05854000d4501c0c90481c00790f0070745e2003c54200d03215580d1002d000e0314008411000c0b5405546491b8400729441e89042001c0091081543c0a58081e003401081c40240903600c2c010466944603556086000703070740f00c005407000c1c0025a8840e40c04402800c101400f085c40030380c4500c4103115031a21200c1c02103150907290849003007807500c00008041c010031a076030352024010140288198505609024108e440082803483c0180240c905030f4203850200061600c074103002121b1a0300012442c1d0380340d0303c200410415600c10381080340036009100030 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 808212275 1250 808211025 808211111
    0x2e060e030d0806101103070209040b0f07030e120c0c0418030e01020a08090f040f0f0204030c14030d0f09150e01020c0d05030d021c060e0106091502030d09060f 70
    0xa401e0043d08060800700c510703480d40105581c914195042d1424a100510400015035980138919010300c0c0650040003480c1030103c945d617070b02c2100400406c1458102454450305110004010481c070b00698103a903120320a070041c480c14080b003000340c181e0050816010718101c0300c00640d4110320307070b00c80e4590007a491488001aa00d074842d0030710103440b0315001d210121a60410046194082400800028007091344411100455140c4056080c0182d40801d042c02040a90100748c40a0480a020075400c503954500090341d070324628901000700010140c0781242c20b801101440f000d42121002c1d040c2c8104c242e00e0007800301e182a00ea44d8010302c40d400303c002d2541003514114880a41000c05180b42040015116000e9400746500307090103c2012000c0220041510070200905855a0006129494084c004194802641068080b410050449108941c00004a0750040900500851160b00c00c0c207003680105a46124107005600b40260708109020047d0a058080c115024252008221081c = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 808213525 1250 808212275 808212287
    0xa0906080702060a02070510111b07030b18120403061a060a0c0201050a18090605010f081e040819030c0210020403020d0605270307292e060e030d 64
    0x18079100981c1085011580c200d11507002090000d01900c11100c00301404040745081769558224182038000c0442d10b4082000c1c4985588111026440241180c9046840700801c4440140182d4500d400340700110501101c1404117441c0180307503968040d203655030b0782020000341041c1e1155010120384404044050701d090700a0750040780441e40c0b018804070342e6038015225540540c8095050202c0030650291aa007c070b128800038084800011814a140c1000900b15140203244241400002c03001c02c19800c01070486044401c501000310f0710291038604200b145d0303100b12881c06d00f030f0b04521900211b032607401d034004161158044d800c84500103000326588040740580c2c00025440003074408002c001c500140c02541e00140580076050780c8081c11550b030307c0c000061040200307003508045900018048841d0051060407088845540c500d01203006141014030001e00c40078005245480744070380d801d039008044540c00c880d808000d14890b08c50501400d8065043c0101e07119215118107940d403a4030842d = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 808214775 1250 808213525 808213531
    0x6010309030c020112060503030d060801140c120c0904090302011407020309030a150b0415090b0a050a0b07051203071106060d0302060613020d1506031a031e160b0a090608 75
    0x307a0b80c0c42c060b82640d401112a842030f8a00803105544504000c90b150341e0610044c0066101d5580000b0510314004000e400c3d602240101184041c584080000106c2484215407070300002203c0000e80c1d076110b144031051070203244907841d0024a0103110004054055004c1c04120345d41c0c2044071a130b965028012a940c1c890b070301610b601a007100c207802001030364217480039040095107500420307144654404503003200e41d010038600281c1003203a41080999074501c80c008180c0d000341e80740c1d1045130608010030201f6007076100c0c00222000c005544024005c0034042c850072462024480b03a601c0c240307450f00a000c03039a8840040414000d501c00301d2500d103041c6613417284891f0b041d009000d09a9801c000c2014050040c80d18442040c0c08000d01301414406225004000f890f00e0009040c5d1820824000c046440f600300d40780c614003000c11401040d550018400911281a4242c03122401022030741a040104c00c984130418050080300115642c402140a400c0800d07403a950482c1055441208a4420b4419 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 808216025 1250 808214775 808214777
    0x16080f09210c010c0f021c12030e0304030b13060f020d0c030e07031e050304030b0703241503090512091c170d11180f010c0302190204060506160b0601030903 69
    0x14003103004550040c2e04c01281c003030054120340e00a00580c0c010818050f041c100c0d40000c0c460407041241000f2281501440300001460100440001408039942e00d106074000940840800030001d040e110414000c10121036005106000c03d10300c402ca2070340a034002d6644402a1030620036402d5a0f14400c3c4140120b0b0005a0010306010b407a40c2c40e5110710440580310414045e01d4040301c1000301c2c00c01c1000b0300046204403041c141c20700e0070b0400202200d003c5c2041d4060011300c3c9000e02030328000c0300c1c1000c06072000301054600c0403040e00da06074010154040d00822501600d4594140c554162019003c40f81c419034590700640600c0e41c40c5801d00c144040c0052500c110384030b2003c510a05000585030207001c0010010305500002440c1700346411440318041e10503e00c1032400c0389814800a00200d64100b0308040c8401e003626074000e916400c07121b62803000c681524114000350358441d00803000030640030380ba5035956220882c400902021412041e0b03800f40c51a004100035510030312480d054a601 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 808217275 1250 808216025 808216033
    0x3180822050303031518040b073f0b090c03010308030c1605160e010605040b0903101506110a022214090d020115050604050616080f0921 60
    0x4585160448001016148200315260340400300341600c0400066000d03090380301d0030038240c10800c420019181051002403e10448034400d020009000380400d80c0c0000040c28080e0407842c030300c40c0c0c0a48043c80c038424108401d0140f5000014000c298591035880013000360180203400c0113070140401c1c0302c4150b0f03282411100c10001080800d100001864012100c01d001d207140c029181044505507880100c2030351190400c81c000c0c1032404207902840010807030240d50815540c500030010302240202c0c40340c1c2a440600050030b4038295000d002e003054865229908011700100c0c0e03c160002d480b102d00449010441c500620a104540080e108543c20340c001c18501d481d414440250702c44052880c03a00308038a4690b46004c200c1800c0c5802d952156999400030b09851a841c403000b030941c0d5003c0142e40034155071301d10910483d00c0750400c44045d00e0007a079a00303548a42c1c11190144643c0c825001904407040402d181d1030364841d020041c40d400724100c40070345d01803114a21407940c4000a10420740e0f47c0d44 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 808218525 1250 808217275 808217287
    0xc120302010b1e120c04020301090c0e0906060a1103070b0c0c07080111090f0d1202011a0913030c030c142112190605130c0306080d020601180f0c0906031808 69
    0x1d08840b980714500d800801740e9180102010105003603800c00c3e00130800d069190310b103040c001540702c0c1a41001d03802c110b582c01c203079080004c00b20b9680e1262500d410204550510740c4010b584e010003c8070034450f030012101c0d21030b14002c10481d403170340c100040240c09800b40400014441605004440e42e02ca110301101d07140c4003000040044003840049140d402420040c10000451448040410303001402c1c2c0020500c0701d408485500e00d455200b038480e10031a1201c06100100508045000b00581e041c00c21415a41041c1020b4420200c54400142400c50003070000e502180d0100744500c3c1c0c0075400e00246011003400d8103042050054078100340030b0303591000010b01e0b42030080c1e02600700c42c8000140003840c070380c542c40851b0360007455840480780140c0b070306440c48401c1d41c54401d010007407040c000a00302c90000501c00079100e402c10f21410615180740005040c180340c096100d146c0d40150301b80c040000103a0140c0c050240d01040c4210303c0030900e00740342c05000030545400c04078200d45c0000840c0c80c0038 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 808219775 1250 808218525 808218529
    0xb0c03030f0a090f0b06010905011103090d05010b0306010609031a010b16020103020d3e0f0306040f0e06060405070305090307150608030708070606080c1302160c120302010b1e 77
    0x40760042065904986aa403481c0200300c03404035040060380111104d896a24044002400419084c2d1155041008191890312850b00120580721103a900315045406540c240c1029030141801c0041c0541c54001c4c4000011450740200361141100d114503d61958a03807207402141c900c00c000d03c901000007208002d6511640140c0d03180307420044c4141001400c049100c8921401c6990030412042494004103689441c0903154003089d989500c02035209030070342c11940f1298030600440000700107444001c0046035850399640c0104210001d02407041042d14100c0d46400d640700825180f0600961034400481c401d00e2190103100d00c50000d4000440c6089040da854840700811848240c01341c9d035640201190351081030008003070300c6010301d80c09030b2076004a080000c1128229440705400340d0203801100c03841d07241c98000d000e40d60340080f0010b03103480c50600e96154207080060018804004942d001c5091f8450608900e9410301940c0200100c6601c0801c0c44a1a141c42481f002d20780031100040c0741b54 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 808221025 1250 808219775 808219801
    0x1e030501140f070c03170c1305120c09040620042c070f0c080c0c1f080604020f0705070905101d0402060a093b040201090b030622060f0b0c0303 63
    0x280301b864106e0a002c0100510001d1290984a4003105103000980700325402140c100c01c00908001c442e14001980310195003603071003800700c840714040c107104e0001400f0300060303a01c00000c0e10302000c0e206600608080c0350310181c2c1d0090040814490611203021124603803440341c80c80c0031360b120303c40d0030f40c98a40074825204000107452a00c20030101305800390000d007516018100700d500403001803c0800107201044260510400c400e880314030301c000701040c070640c00360350346400c000c05890050f6074541002c00d81080d40320740c00e0060320710302c294100000c0c1c03100307980e0000c0d200340d03c0d408603218229220750202c030b450a42540d51003c4058200c000c1000352405600070050038071030703041140c900c0350346201c1901c0c42c8000010f00d007840e0351000741030030849007011098661403180301c030522958a440e500182c00000a809000a480008000203629465001814011311104826006506030012030140901200d024841201a14010000300c0d441030b0800e84108d24615400346013581c0c0d44620750707086 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 808222275 1250 808221025 808221047
    0x19110406090e040c05210118051c12022a0c0a1d010b1303120f03060e01080a060b06041d061009150309020409230115120b101e030501140f07 62
    0xb03c01045014041c0a209100c5c541044918003000428000230341000c0c1d0504c040c0c0c06503c1c954890700050802c1c1c4680c0a200c068a030017691600584450015404060565100d81a042c000c5917081280d1009440001c0c03100c10044100e510a2a09443d608102039489411400001100003200107119482c142805090341207000c0110803200d66a0383c40e1880c80b444c5600080c07001ca240300061807081c5078540a0300c0c5c054940e29141c506035514040e80e02d55540700a03d4050802a918100c10388140c0c1c42100700c50040c0395403c08120030340700c0e2640b40d103480d800075035000e44105d000001548420303014091000441d90440785040c00d560022200342c01a00142038201c1c1c3c0141d4680e2040d0018498480d448604005000c0f142e04240200202a085815000641e1311616861004102903140e100d0b04400c0154040ca840c101078175880c2c0502a00c91903a0411401051081480c44940910415007421280900e00038402107190022144c00e208065400c0802c410b0584006041580151041c101c = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 808223525 1250 808222275 808222309
    0x1505060304110a0e0901050606090904150608030307031a030c09071407020907120f051501140d0603061b030506150a1b05101a0604090519110406090e040c05 69
    0x100b0a0300041c420041a8125890941c0d00360300740124001c092040b1540300d00e05940e044e150150300350020b110704100400013410ba020034401003070440c1f45604000d000708418412a40c60b42040807015010f01003210003000e10107040c0b10741102030b1800182c003124544010301001d01545581034219401400d06190402940e2300b08100780058650150940c4031f480706568555119072070b076001e5400e0300ca80075059000d003810641401030364560043da49080d46001d003040a041524100c003540b890040e03c02c41c1a01d24600310001061102c5a0005141c240001410031000c0d1420764050f02103440c141d42d41c942203204150003090301a0214020301400380c940c1012803120200c91000328400910708011241a00f2119010308822424003135071034000c40c0e044243d60004000c40c0440c0e400d00952041c6032601c0d40721400b0903000e41c155003031300c0305486640c501840101c0f1030000d41d03e40c9a11600c90800000d02d500c0780041c100802807480740c0101e51185041c1c0859281c030303007004550403405040f01 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 808224775 1250 808223525 808223543
    0x1b07020a080a06140a0213061101060e040c03030207151d0604230901270f0b180108060105090705070609060b1c060506010203030f010303030504150c1d01031505060304 74
    0x1107898001001141049441030b0780c0851010300e8501603410340400507005049407801440140b025105416400301a40d01c586007940d00b440645594a0141803c0d42c04100e83c06083c600f0701c014070400044190a480c02030702280d240319914060304ea443c9196200280000d03c05003200f6050580045504c444100f004103030b507003800c1c3c458100034010160228003801d0b00714102000c400030704000002d580106003842004007049003d10107403400c0600710b441c1c8101d81e80d80341c0c1030142d040d04c42c1e80094050741000c1d2026005c00300d565001d088810f420b0003007041030b225003800010b4a00d02900400d103d50b10aa650754100003103a96918050010001d003262496203a500003901030700ea401c095240c4c0308441422180c851410b091204c1201e1002e40004d0440d00b042040249040c120f248690440c1d0b414500020644e50b0342c10110150100700300c83d03254450814480380402136008111650311a00200d500c150310510300e0054040703841551140b103403c2d0b00c90300c0070840d43c86e002d4084c0d644280680b04403 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 808226025 1250 808224775 808224779
    0x9040f03030914030a03060506040b04050108100306110c01060e04170a090b0c011a030109031e032019020d08180a02030f03030f240402070201050c062701051b07020a 73
    0x305483ea41c1c00d0f26a0b6185a0012038422050341c1d15004483c014442a20b01514260a0080500c2944a54000c184c10b125810740454140c101140c8010021904007504111503c0c3c010100c4c0c0040c0e1018400c645250300700200440c11301450f034150b9001d6540140710300d15404440340c07440d5070303038000b402904180172030f40c8400a03020400030001c02580007400000100d00302413010f2103030303010071280820f400781c0c3c5410360b071070b0020f5004001070b00a42a6103041900300996000c0c2107000d450311025907819881156094011011407002410342c0010200c4000441204082e0403a42d48210580d1040011030b8440400c0ea0034050400800b4010400d0080e1486c450003030300030034600300400b00045900d510000400c900140d2001250750007280c0c6001c400301401404101c0f0042240d20200d0510640c2e002600700308581c0071304101d8031900088002e4880d10301e0074918400311041780f03000008111540307501110040e2018861540704100d0720460f030b8520741948444140580144404030782000d195000 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 808227275 1250 808226025 808226033
    0x7030b1915051905211906050115050a020c30030301030506091b090618040c050f013603021221070b040b060109050406060c02031203010509040f030309 67
    0x244210740200c60315040c00c0c56107000240b1001c11240c0a80c0e083c820000d003001e102030343d191451800e0030841507204441d040710001c0743c28100106c001900001c0504566584208649078004d54102d60f100201002072002d10170007580e0501c2007902081c01038000d880b03160b030320741303082518040c074040c00440b03044000b492000c1d80c021442307820403581c140340d10100042040200400010741d22000780d50207000c0c81d0350b03100030f0700c0311402450701102c0c0309101c844001040764540b402065403156001507003120908140c24a103080705d6680c05254020341d0550307910200c550180c440051300520f065020510300781c041e0500e001d4207403004032007407125410000010243e42c8280c002d2185860040140c48514550400100348080610509034525000c1c40301c40d020444440a155100341c2007484000076a8403100100c0705040590071a0b07600914005000c40d42541c42202031002910030782c00c913081c000e20050401410f010900c14507030300c42c040d6000100001c000f81d0440194a00c6424003182c02206071303031 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 808228525 1250 808227275 808227281
    0x503032a07080f0601061103030117151602060702031326032a0d090303031d010c0c050115030f0f06020d09062a1b080415030605090901020c07030b19 66
    0x405000260300684042003080fa092028070300424160910311140c481c003410300e45d12400140304031200d13000c04c0d450301c00003104280080142a110040c90460901e04000c0b81b691349842500414014401c5600141107280004100c4d450001c1107451000414940002700610303a071024880200c5540440002000d12420005090000d089100e0b11701000c110500a501403500c4e0300503081140c0c07200200085851704441c40c0f0050300d416240c049a1914101030b801c040d00c04810300d00c0c3e400d40c640690001040e90026116002c0c501c104002d210404443c03543d049018000e00001c2d0940d0f41c0c001800c1d0004280619030103040b849450090305040d000c0000c14115040004291102d0342c071054042c00b0003e0482c0b02a202d21048160100b41c100c000000902c04003011035446142092201d4440501c0204001d0720020041e002950f14154820100200a03044074410640a061804046140b410040c002e440043c0d41c40700013003614510b5520355021001c40070f0009140c1080c1d00d4800078801c04c00f80 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 808229775 1250 808228525 808228529
    0x703060e014110020109020d110111160f08030702030d080919080a09051002060406151e05040b0307060503061e030d0807080c0c060103111f0e030d090503032a07 71
    0x42c00c500600c00d4009111280030703110303540e00c116450903503141c0040c0d030340c83e007200c0c030385504080102002c90164005a035414000c1480800500c038170550310b0249480d410580090768540e60702c40c000180e40709800c90b603d01400800a42c0342d000f00401800c0c2070700c2070400c2940441400e00300c450103184515212291020b48400790384004001540b0f00c1c4090b045590304004080130343d04803502c1e42d0810070082d1280f2001c2e200074002502c1c0d1040d035101c2c81c844c03d41e42c400f402050584609420303010042c480002e02030701c00c3d64012410310381c1001a81c03030045041e90490750161517191a55960804001c6d440902c08280e1204081c2e17031048850340d4904020020000c1d21540340d0a88078240410301034130350301d00248080c2d1b8020081041c00e440074004540241140d902403e811491034070031000a40d290030755420300301c1c21103070088440d42035035100c1c00080400f0300c241c040c0ca90720140084101e8008100340074460701a4001c200c11529180301e529040c103481d4000f004c1d031086450018030203083c0401c44d = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 808231025 1250 808229775 808229879
    0x4030516050d1b08090d02030c0411040e0601050c0a08030603120a0e01080c0f07080c030c01020a0c0b0105010207060806130b0907050d0605040e0607110a060c090801050703060e01 79
    0x900580c0312403a801000c0401c0e5101c1c2080da03e038060100360b8401004c2d11460b4070351405414141c284a0454071704111040341f00c0c2c4000c0050054500d0755514a940d90030520440902c00d6081c8046001c030350003202210402407404000d0030907401c8585031030241e980090900c40d010311820800c82164856000501300000c0650344201c00101040700040150030080c14680e8004810854002080c80f040100e44005a0045d01c2c80c0d1118030903000d5900f5030040c0301039a10349500000d00d02d040307990311036030b0700740c5082c440c1d0202003003640c03250012a0384004a0041c0004101030340d012036020300d480d60030002c000307507131010210f400d014140100700d41e40e20568070200414404510003418880034066100034000a0346c0c1005501e207036032151562860094406000d0003928029150400c4040c000e00b01150b412a000780098000c07100010000702043c441c5014030b52800c404100036a100703020721402c440280506d20210f908280001420342c0c0c0480c56174448201c41d4072030b07584040d28815284561910 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 808232275 1250 808231025 808231033
    0x1050609182809031e2a030e0a140d03020c090112140f1525030605031212070f050f0310180504020a1701060e0108210301030f0b04082107110d080a050403051605 71
    0x3403842c0203004070008c030080c14410f44000800340510141508038000c0b244003142c1034440490b00c0c0c10f060b800e10400030131854004804500100b80c01c1d400503403c1402510460b000304007807000c2c181892311000f0704d0004103c150061121040d80340e80740300c0d0407908007004404400503000002c4808480642c00c80945010945a400800551500f80310303c1c3c1d07a0446043c012490310518003055140d000000349450184101041d5001d445489401030314174010b010a011175507420300d1070491302218200d10410244440c5101124106103080c000c90380242d6001c0c154130303413850400034088011644034080645565840000090b01c0d2260b4048500800300c02c0090b00c88c080084400c3e00f40e400304020010000c1031708000410018003941c0c0b00d14149070f080444529640c849142c0124180308080b0a002c0401b111800f0f03400803400703002d84034000c42c407a031103003031440d114107140c55101c040907101d0b42c012892001c002100030045400440d486482850910310f2326852071003800404090342c0b01a02c4541c0 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 808233525 1250 808232275 808232357
    0xf07030f02010513031403090a020a0306090203011802130515030706030b0a050405090709110d0219030605120d0e0f0411030414060c0301050609182809031e 69
    0x1070207228454000071500e1180f40002190340300500034144000116100540c000000343c100d08044c00500c14003580284580341c1a40d9130304000e00a081510000e070f110754a0004900a0704050b21907440383c6d0390b805080b10003d0b0401450318402400f0007444c1c5018035104448030300050f5800d0100c01c026284980740040c40341da0100c103000310b0340e00507007100d8003452078207007440024180000c0e86001c41c4c0d004d4002040814040782d03044030b140645040201d083e80040b036802c0d1000001030324003070310610640c0d0810640341e58904000001c1c41d940186804d0b0742180c120445414800d41d01c2c80c041e01e0003c0c1141d1540f00c4044086012101903540040c0ca141d0040207010410401051b0748417056482402800f080c00e2044150350140b0040c404c0c107101d028009151041a01c4240411200b5004500c0040b903901c1c05103121840d41e030102c50380381400020b4000c50703c07070000c552181c05410341c1c2680e1032040b40025159400800c2465070120f20074880f03899007040a2010390b0b24000f44c140c12806510310294 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 808234775 1250 808233525 808233527
    0xa0c0204150305010e03091f1202070c1e030803070f0504050904060c020607110c06030910150501030c03140f18010524011b0204021e03100503161a0901050f07030f 72
    0x15045d00caa94410380040010341e44c6a070710009034400c81e80100400d0b10914455110070303034000050051180980d0b00114184041c0030580c40c10404840440b503640703851031001c40e0b401d507aa803c1c50000030044041030011a12040c4599505418801903090407480c080e02ea00000d848000b08403000c6a81b90703114121100a65418000c02ea04261a403c24869100810202645442c10344034950300a410100024003510410020700360741c0350f280701d0100b00c104043d0400740f004071795502400d4046420052500280c910034410102d00d40c0845240d11042d803181302080010034409441550b80d070044101040b904082032050500840c1800300c0e081549154000703c100c08080134142c2c03418440b421030703613282038404070041d07248841e170485d0f0041e59220065642d104101d040354400c101b03a40301204010207681c40383c90100035150102c0817203603a41d4115204450b112070502a0b044a10100c42c0c101ca42c9940503006400042c1050600500704403400c0207203400764100c8201a800150b03119017810300d132 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 808236025 1250 808234775 808234781
    0xd061104081e03041809021e0102061e0a09030c0c090204050f0a053708070f270c03091502030618130b0a0b0d120807020304060c03050a0c020415030501 67
    0x40201c407028841c2035000c10300c61601d034001c911a590315404519005e01c060724042e840511000d50003014507000d18001c41100503282c00d042e6960707015100780c401140c044450003d101c2d1b841005560041440d588408542021b80400e030011410300003903005420001d000243d1010140800321401611649040100040141d6224445001d06100310003030000d03032240006c8400010022180c06040514a4099001600c0310309103c1c0020510180200c1d20220104580f000c564808900304400d5848554411204002d548210002c031000d40c010b00305540140c004502501c49424000742402c01a210b02032901c2543e1070711000d8036070000c10001c240c500300c00300c0d04507044500188200c0d0328080600c0d41a00a4007180504032a0326100001d80340a01078002d56803105001d460a4084030b194a090342c0c0381012001404040f440c0c2c04001380d407481c400415101158256a25082c1c00100703510300ba1010780c0680070150402030107820f2000544c03203500800301d404000035040e0f0511403440c2095421 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 808237275 1250 808236025 808236043
    0x70b0403080c1908030a020a09170d18050906211c1b0507050d0c08030705010905070e0907050d0501141503010606170c09060c12070308071701140d06110408 69
    0x220b120210104800b003006003050343d6101055070001a5108808d240039101910241e008408120120341d80800404010406031480b800607181e1709044c0152540701c0c1d0790f903c80b90240a4108401c400000c4140c030b40318801140b0142000c0c2d01396101e012045a040c1450946400d0045016580324298200c3d40d004404403401c1040c04013508ac003030455918140c0340e502a22415200d03611010840060210341c00e0000010209042140d03903c16141c03400502800c0c520406a6250084170720014101010140107071048034054007074031549040c001040b000d03001c0304009036820b40d66151703072005081c00644654010450301c0001200e01d40d58100f01401d40d040c5070400c0342086942030300000c1d110f14a03982250030540507840142c03500803200c086201405034004c414014030075448000b4001d01c4401c020410a4065900c0d500580d64540080da03100c00c0350702425110700a039000400461295844c1020064401420746d54000c0050704d80009440c48d4000102010740001010000ca90082003c910 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 808238525 1250 808237275 808237303
    0x10906030b16020607050c0c03070810050c0a140a0e0409050703062403060b0d0f030504090b0a06120b150408060901051602100b01120204080f07091814070b0403080c 73
    0x1090440d00780b4002c0d119400074003d1414807030085564940344c142401081304005d0080c04880c44c02c0c3c0c2d10381c001a9203001304001000b030549820045a80b084058080f1010311980b6120600c11145901035002d60b6413214107400d007042034041c1500c0180e550f44c0108594030303018100030300000d03042d410080e080340c00980203100d001d25201440d22003041e42014800460f50000c4001a1410412001c03421140041d440203003a8169105468201a045805442a84d480000c1080b031074140c44248400d5000c0741c0505004101c4031800c40200320302503006241342039804cd14140c8400841880405035402c0340d0030004090300003004010703807a1001d104442d40800e2458031783d00140d40c80f20003c0e441da200b1000b80c3c00e1294440a0048069024140599908180340021541d55948640c0c684c0c41e0451441f050026002e0360318001440402c9010b01c0608020400e603c0003100710b20350301c0030403a0010782c8001c1c1190103210400588c8840d01300140c0021405500c40c00d07991950840828140111005003003 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 808239775 1250 808238525 808238551
    0x2413081b0109260111040e2e05040914060c070510050c030f0a020903030f041403070e0a09053a1403010b0904020d1d0106090902101412010906030b 65
    0x20303901120040350700784030444102011040f0740400d180504940d021284000c00300140010704a881c44240d50310507141911200c2e4013000d0021800c42e071040c0b81d009060401d800301810301031460705501c82000389105081080001c00c4480116041c90402c075007a610310320700824034405021003030001c0110345000010070001485e120507003100900000d0411401c1e8001440010b50051240c0d0448640d900001d00311781d00d868058442c1d20346a8414010455510391100342c0d19918103000580500fa41c082600301340c0302d6a1010010302c000e211400e0283c60174407035804240011a00c3e00200001101606407140ca1a440c4000009100c011611800e041048841c8036001300c205034020780341503481780c248040d0f0719a404400180039002d40c4103001d9a06103410324000740441c3c0e02c44040030081a00340284445652824000304a600c081c2021b500b08003071086041c001d034071510740300404589101c1e800d0309060aa081000c1c1d003074004d8228400d0715945980600610219048440d40000c08940301c03 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 808241025 1250 808239775 808239779
    0x5060117191b08010612030c030210141605090a090f06030f1406090307030c03050306040b06190801050a0303020304051005070c0305030306041407050d05040309150905100207052413081b0109 84
    0x15030703406d400118014040103810180d8600705442881004810b0100010601c00d660f005080c8032107048090300c4c00e890b10344032041d4940c4010b001e00c00396000020010243d4500300d10308500300018140e100c0003920015551640840001e111030500300d1041d000d00c2c1002c079101610400c9a01c0d005001d84100419403040c07042d80300095101c140c10b0f006a9042c0b41241d160740b2410042000340c0b00da100442d034400404030384144a03101000003c44550550741d140e005d56640c4c2c00a0219400c800c1c00090700503001004180458108000000302c80c601901d06149001856142c1034855113140d04119030030b40001041c00820720345405014901105a001820a814083d00c040c8c954801e90031010391043d110000a402c0c103015601d40c000404a40c99440042008854020090b01250003510302c6054030480b0840b549100064200944c6e102a005500080010f50045103040010381c0148041d80200501540841c45050520041c044400103080110302113000200c2203202e106014104000c402003 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 808242275 1250 808241025 808241039
    0xd150608040c031713030302010209100e0315180f161e0e07110d09030b010821030903130b04060215060307050609030c09180f01020705060117191b080106 68
    0x800c0403681c4c40035500d030451030032210400e03030350281c014402c01c44084c8036000010700d9011340080041c2d8a08031040103440801420940d005140c40000d01d0301035001c062079110740400002c083ea013040ca400b41025042c0c01003212286840300786456940c06030000301c000c072640f200d00c030310820240c0100411480ca500d0a030002101ca0510761107070300c0003070880c01e000c9200c26000b1182c02400103030030f0096968641c40140d004d030000c00304e41f10445d4182e2031903000242d401e00110300c09020b012042e64812040080d91a469040c2d000505029207d000400c014161804040500300003010141c0c10262907919141000e4101480d4643d4102107010303d40402403180d03000f01305107041e1b440480710280c83d09a0440443c1ca850550030386140c0081000040c8041a500840904050040c8008461000e051048118240d0041d000700500c681d01180040c000200070b4410300d800480860111284685d682e02400b00c04150200c003596902c8954010381d00785012110311303c0c054030000380240242c41c82d000c1 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 808243525 1250 808242275 808242293
    0x31e17012907080705060a062603071b0e07030504030314090a030809010f0906020304110618010f112b0e0d12110304064d030408030d15060804 63
    0x2841051241c000500d2020809900d05903400960454101c44c40c45ca00044c1d1800242454020000080c0158810101c0c4a031000c41e0303101c02c1d031420005141060380c0350366402017640c408040003000a0b0040c20208160f4043c03002544254942d680c0880d2034101414041c0843d00c5445030340040001045c2008091540042c9804155a26141181903030380c50031902401407100c0800482c00c68100b00c0d5150a001c45a0050360240b4010035462500c08411010010305101e1007110b50005190200d0101103903000f0300790b1903440e80d481e0421007186c0100449103818854590750b504240b00d04000f094200781d8020428514140150818080a4130201d00040c09081415002428804c20440c5565458450700611080d10703216001c032503c0b01c1c1c503040050221745480c01400b24001902030485074440d2070a01c0044164032070310b101e810480c010010b100c031005151030f40201502c804c01c4000380d08003080004000d103060440340001c0e0f1140b900001100c0c1c0355180e21100030001020184400f040a1003 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 808244775 1250 808243525 808243589
    0xf150105220801020c010209181009020703030f05090f011121090a02040e030307180e010302121507020a030e03011a1903060501030602070317040b01060c031e1701 72
    0x46020303240c260380c0348000360507071550012012035002140300c80000a054003d0425502d00321244000f501612520a640b8070080301c13088182d01e008030707041014200399401061064020301e008a8081900078120007030342d00540341d44005500045410b1040d200030301c580034540048256092420504441c40080380122003941c0d650a96401c001c180480d4042251220131580508240145032440314001d40301e400c22620704011500660b0340f064183d286200a0b0305843c4c3d91800901964216003d001c2644441e441d55480f0b0f1141040c801a5502d00b00d8207680f02c0d9840e5030040c14055860b2800500c41a001c9007124000ea04052107201818100903e854803050166800d0542880146030740384a40c0b455800604101d00d42000441030001c0c40e0014818140079451b200c40c600402038480c13442030780c110760181c10343c0340100050001500c94611466032500915020790394610245426801e10b03170501002002ca1901183c804850950005244c010b0100e1050b444045130b03010700e25081c0704008 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 808246025 1250 808244775 808244797
    0x100b06030a0e0a1e0b0c0913020708130f0503121303021c0f030201020901091d041104060815040b07021c1b051515060418090611030702060f150105 65
    0x484000204010400c9030f55801500b1400e2114000162070080029003500001640c50382900c00004d0050240311007214048035000e400d07208648062002100250880d80044603035503030400c040c07504c031007050011001420484160310342203803510003018940240b19481c501000401e0102c20b03180380103403c000e81140d4041e41d400f200da586904c52080480d030044001015601105900f0090540c150f01401c40c0348400c7e2904070000b074880c1040b03a100100a14884901c0c030300341c00014001002004203c2d00b00e4000392001c6a1952280e0340c00b030501c00600c650200c0000c0c054204402d02080d8409585c11a0702c5001602544848140350b0800b2260181001c05204600f81c991041c0c1c18640e028188868002c4151080714441d100b107556850003d07a1205074000348400c41d03207103901e040c000721012501001b4a00150807480b90000000d080042000d94059603100e000d2800310348000011071107074010790f01608440c940703000c008440c2c583c0941518051139644042140903608072048481000b25 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 808247275 1250 808246025 808246031
    0x20c01020d0e0f060c010204151d0906101409060f0d05010501050f19020a0209010801150608090d08090c1206041509120e0307030c08070f0b28050705060414100b06030a 74
    0x105d40414064451540914054034110903840e04c0b55a229046d884030344480c980ba144281c050a0421900d11016640c9a50100c0f090641c01c03486401290f0751852a031050b00e02d1403e024040001544c2a0407400190100c5580000c482c640a80a0f1203154090602420100d00b8040c0828a2815501802d1340c0d000c1c0d0350160442070301500e4000c1060001d842c0d8020078800540d030315021544d020b8800c80545200c0d10146410206089000300003d034070542401d8000d004450300ac4900b1150700f1030180c0358050034001d04410100c01d4513810799807041203400200500311030a25103080c1c545402441044009146070644480008900c06403911000700c071468a1802c0c00d1280700040e060644960008002c01201540005c2c15007001c03908000b00c43d11446071404142e6200400c07210351007566030010990844001000c480c41c1112690b1110139010b180c601c1c01e0400e0f943d0340610300841a18160748034142040050401c850810101031401003c0c1418052446440c0205501d0300015200300349103a1 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 808248525 1250 808247275 808247287
    0x14010812030c0403082106120319050d0504110a06030605150d020c07090b030c120c060310080601060e120c090414010b0a0b18010219060504031e020c01020d0e0f06 72
    0x240b800c041e0703005140c0120116558945a840e05403210348114084c2000c01e10781ea0014201e80340c200035200340c1c40f0408001d5840c045581c0c0203080c04c1d00c4111184000d02c02d0500400c6002119885901d115610450910f1103402c810820050000300e0b582c4003404141c24600c05002030b8a0318113590841c0c8101c0d03a2060b8480042204010103401140e0801000c0d22581200084003c51904014480d400a40c00d84800e40641c0d000e20030b1a02c0e00f051404525408061805281e0810000071a884038007032102030300a036111810581002000e80c0190000b800700340300060217140c000404000d5480e031034001d00321841a1004104002c000400c0509039803407030000e4505554080d00034042c40b07040245019083c13074071600c0d9041290402296049101e55884480807254000035600030160414007641e58081d4a640d100005010024021010403004010410030b00e0300a088000b1001c1e07080d0060500e09058800080c5407190303600c000e00400c01804100c91071a107880940c4004884145da111b0340e01ca1b = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 808249775 1250 808248525 808248541
    0xa080c0616091a221418040b06060f12070801240804060f1103010311030c0d1410060b09090f130303091e0f05070b0316030902010c140a061401081203 66
    0x4090ba01ca4040550301442c1c42201007600c08980e001034070f0b200301ea00c0300c10300c001304180419042c000d201006c40b81281404038001c1350a000a01d03502000040c002440c0400046080c200c0c0d821112006400f80102814820103075002130100b0301420049403040c80c0c00d030a8602503035605045914001c24000510085002d0208942102841d000d03a1007060060040d080d00c030003895070091009452507403c4198241107480e01061006410302d0003080746020035003a03152a035408911140b00300c520301c0b409000e03907803088850103a10300802404e070138261503c00c110b06001e5401070003007005150010850801c030090b00c101440b4039015425203000600010300f854001001c0781d0b8200c2003442c041c4000398442c1041014401d81c0c0441d031203002554003040d0746d540e9a942d0740c0800e45080030492650400103000c01d00c642e10003440c6600504d42054800159112a1590141c42074012015084004503600788001030191800300310840340102d00c1985024203250300c542c551304111030025030020104584c5 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 808251025 1250 808249775 808249777
    0x14041a1e070e09100f080f030307050a050405030d080f060103050106021209010207091406270402010c020402071703090c0d0809120f010e030403141f020a02010e0a080c0616091a 78
    0x4400241800c1c0e20f90625410321145a8201d102d24010584e40400205030113a001c03034104584000e680c015421600c402c20255240e400072101e04c02000028080028959402c00100d034403840540c8440c40700742043c540c1d162b10030000500203810f15042030010070015500082d0521030149600c0c105440340c000780c00403401d120055108012160510100112803900c0d50b2104c1c1c010b40048988612160f1012000640c2e0800019005200030640c0700090240d40200010600c040c40107000500d05070b2555500c2d00280e504881d455038812000c010008194010028032602d03010840e9885a000500c0c1d4982d2024072801540500910001d02000b0780420704201c000400c812a20081c4182c1e1650480103540e03410500c0184c0d40800da51000503440c0d203001c5031821440c1e400c0f5100c8441c44400002e9800a51300070b0010804640d138a40b540416200c040c0a0940201c1c03180206a50ba40e0309841a5403924002511592030840381e03d1009080340e401c001c0354011200d41110310703030320344030408080189 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 808252275 1250 808251025 808251047
    0x501050a0c0501050130030e0d022d0112020405030606040209040615050702090a0b060a0c110a090b0f010305010b030708040302011b08100e100b1c14041a1e07 70
    0x456013400e0001c40c2050100403c0c00c071094003041c00400c1d1551440541a2201c12508041c0214550720780c00041800c00d010f40e0700146001412114070040542c182d07149050703400031069021804400310500c250303170101c24082c442903581e400390308241c10080020b449080240c5014031690340059440e0407909c03141c00000090400340c80b60094480707110b001038880d6103d104100d100d0f007007140004020700b40c503100711130329140d0203041c071030900070b441da8140c1e01c6c903205582c1031392a01e44400b4207100c0b56403407240034406402c2005011440041a100340301e000c51458070981c1c1450308110040c005d1005180c10740b40d00c010302d85410040f60300d40d0b003000c2e4010030510803460701000200050224080c1c102c00e449000d09203000e845e0926680d11104074406a5040d0b0341c002604180341c60030090800c042c000390240000707000c10b08114950603003404007114003214104484444540400c0244410144403500148642d100080d0038600079102c081071204c50041d000d00e694044001c01c411502c16559410 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 808253525 1250 808252275 808252283
    0x1e030d240e0604061e080f070608040b0a09150b0f090f07081005060f12090a050c04020c010e1b1002160302210d0305090f16060509010c06060b0409061e0501050a0c 72
    0x10129442e0041300e10451034074000c0002501c6806c4800347c00301d40c00a40e0710100d909541d9130a105440d541c3d40c020060390041e041600641e1624040404565910500c00200c011204002440303c80b240a0220f039652030580f0620418010082051960240030216401602c81c07030900d41503035038144400c00c1044150031440d0060800300d20100a0b9211307070010040030003c2144600c1307998400712401c4e5200d01e10f1b800200719420412040c0c100c0d00b010380182c42130481850010980d011303503584240c178011172074100c8610445000c90084443c10580314507200e0320351070300c054502c000e8203005240a100300c600c002401030035a40d01240002009001820400c0402e1065031a12008002c0040c00352209071009045400358000c1e924501d075001032a20300220076010300c0d65004c0d25120082d1080e400a105040c1840900c2c419000024010311401000d011600c015030b88070341c10065107204951058118040120b1405041105030071a072000c441150400d29019550700704d840000c44030303a00d844600030 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 808254775 1250 808253525 808253549
    0x320c030112140a1b0509100504021602190603140c091c1e1725050a0b040b01030c060905030307020d0606170f01050a0507050a0807021e030d240e060406 67
    0x3d0100010780c02e1a8550400e02501000000e81315000c02c401024144e81c01c640c11641c1c2d032801c001504142c0c0140c0708141c03410503512201030094002c12480342400d0a0984d0401c004181406101c1c0c15200e00300f118522519001d100d071600d01160042e0748120849148035034007581450741240340550101390340703a90007038025180740b041c503003142d800841240c01110132503440160b0320070301c0510b04c00380c0e00c004140b00f0030a0411100100c00240c1842d041c142500c0c207000c0c1c04860b8010130540c0290314011442051403503c4c80d03155042c50094106180c02c04130402060a6003080346680002c06d0b1140c054046885880030700851824000030040b0b40e12100e14160300f055030485a0324041000404c0d40c1d603140080c010756842c4403c4078201c07a0101d42d5000444d4081c0401c580351403040e142d50b0303030240c080d004803500b032240010b02ca4200d20051302c80000580c0005006480103006000700706519003a058501010409080901100100d6009103c0b0041014000488a81e41c9802c01001410307440c10700 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 808256025 1250 808254775 808254793
    0xb04150c0f140a0c170c01090f0506060301050103030507022710030204050a0c0c0b0702190c03031d060307180b0f0702030d11060402010507060f320c03011214 70
    0x40c0580071407400c0c4001061180a5051074442c0d400d044a0300d4901c540c0c0d682d8110f240d2550b592540700002d440d07400d0005800d0002c2a000e031000d100340f45c0900d000365031408403100140340c91b81c586023000f01489e005e030341040c0c010000a40c0150554000c2a4119030000f41c10910012241001c404a1110307449040808140400b20341d6100d08039003681d0003aa0300344626541e03220400c0644501944600000780d0031404130340071805021640350010340b03a10540d4248c000d03c0800301e50000c0200001e40d10103140712010403c060308242c46082c605080c040220507500700400146071400000e2880c0240309a9694042c0d081040581041c09807444044154840d902030590444c82e410090b402c034040c2c070a001090300d40300d014407079081404844c8001003486a0f6158011100d94011810807540780340c50300301e01d19800b9658044d00502001c030354404040c524050295801d000d00a14100c00c8200748081808502c1c0604800c032410342d0221030301501d840c0280e19145002842e0804540070300d0049100c0 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 808257275 1250 808256025 808256027
    0x90a05191506090f05060d0915020418060e090a03030b010e06120115051e16020616020301050a0e0c0d050309091618062c0d0b06130204030f0b04150c 66
    0x20880650b03506603601091140c0356a00d0400c40401400342661150381800100c44020903504500c95403481148600c4a081040d05500c0981e000342e0000440c280c030107030b6100f442d81810b10400000b0100d181400720315080840c40aa241c55031228007404160319000380454507401030071444041e0310301514807981e8221250329102600c200303014000c150311941355145882e41c49a4203445035034a5140fa0b901c0f5595001158000c1948100c65443d21407210190060141c0d5810000d0700c040340350f40514440320071907441014211000103024404e402d180442042c44042d00199a01e17034800d0507a84481d80001d18242140355010305007189500c43c07140c0c001c02c0202c1d80300050a01a00000d9242c2120320b00ea0704081c403502a25034050000000d2000c6030b99001001d000d12690281d0300c001103940c3d804207600c00814403070700e915002951942d54680c1480b800341040720b150365030454502411801d0078296075070120a6400c5110190508404101107014400285151441c110400008106444022070 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 808258525 1250 808257275 808257311
    0x1012060b04050a060f170c09071808061b070204090b13050f070b0322050313030516150c080f03010e1f080304180e0f1e010902090a0519 60
    0x1a414065410000458107010035401250142c404103011110541c1c01c0c40100203a00b14040004d507a01c1c42421f400780fa440d101d01d000340340110b4440ea031b8003100b81c80382c602811001c07826a200d103841c2e80c04030082080c11800c1d40c600c0d9a18143d20015156150a1800090098030842030013511310751405c402d000c884c1c030000700a290703001e21410540d07881c0b905850015803141214814200044001c20000d070b040040842d41c1912415407002940b0b03000c013203450f1107245070000d03581d801c000140c068080c014090300b0401849160503a030410717800542441144000354046c2c05155080c003d007600e80804100500d02925101d5a009490710b4580d0303580e00307500d410701d102912142d80d00420500c845000600342510740056030050401103282503c1d00707000e0041040c3e81a04001c1050b5580425840010309106441c00802010700501100d002591404814de00210001c0e44c580c0c50045440700603260000d0f4154041c034036510015039540c0b0791003010f02c100c45035501010f44030701d000c05421350469044c1e = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 808259775 1250 808258525 808258541
    0x30d20030d0b09010b090d0633060905030a0f0303090302150915070302070c0302120a080c0105060a0f08100c1202070506010303023007080705060112110a05010512101206 75
    0xc6903420907036a80c19041402e80314146c0d5141d00288549218004034007103403c00c1a4030180148103040684540e00c03072000c04003021065030044500d101c0208405035201e680c95019081c00c402906909038140e07110141c804005074018149078980c080d580074540280244103110802050f481804d2400009064940000901c080a2404440042001c9600c2413017600e507825841001c2c4004075003075070200310703075652000c4c0d610300c461042d841a040059040d03006404c14403862000801c00382029802c00c001401c40d508103406640503041c08100b209400100d080a8111007840019851440a801c0303513101c111013944400a8000100301c0f0800400046603030489000c0d5080d20042c6410710500d07a61745050121030080c00c1803009144408440c4180201141403146840604e00480f0744d0390242881801d03400f40d0340138005644000107110845c0c55003502c2d44e40c11503160002508240010f001409090201110310307031041c0c0010071f070308820b5601d000075260001c4941d580d04554602072019119007 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 808261025 1250 808259775 808259779
    0x1e0e09130c0b07020f220e030309061812031005120c040c03051003030e0303070b0405070f091b11012717041406030c1204080c0615030d20030d0b 64
    0x101c0300004039080990166152a580200b25200d8014a102001220a08240070b0041015a41e980c4589404280b040710341c00d07202c10010f952a803602000031410090010725108c5070b04110f0000703202c1c8180100f040654214980282c94980d100d450509100650f2508001d07080704486001c401f03141000102242e0000044805104038401c060046080d544283d40001410310038900501c00a80280c1c92a1040c1c0c030050101e0b070a151071a1902800c914080e102034440f0b0304001c000f8400c4d030441c0325005005d0094841e0500102c403032011420000740900f1004000c002c4a1014107031001802e411101050040210001f10401c0c440d400d072071648035502c400c4982c400c040c1d1440010061820964085850004542010103100c8007440030550000f0065160724104100304400750b0003481c8100d029500a8603c191290f2095810615140000d003510707880200800d0350b5004d56400042951020b03410385000700007050724150302071000b40e14424a0394180404107000d0384143c05075010308000141 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 808262275 1250 808261025 808261043
    0x503070317070905010509040f02070c091d0c010206060907110d0809070f0e040219030602030f04060c030b03070b0a12020c060703060512190c030f060f0f0c1e0e0913 73
    0x80c10b001500c80000c5071091601145040c0101c0149207000e41c0242143ca900307102c090720300300080c1d50342617044a844d0040030f0420b41d1126110110054168a002501c0c40c00c002001c18084040c0080c0d511311006203017901c55084800095940d51183c160131003407261410840303006109144e4094042c5100310394071050752046410008040e120703160400d080b140d4811001446442d503800f81301c1101e00a43c0700851030110318500100003682e03407004610902940c07a0340785142c2020316140003611086614a410903044c028039288950300410501c003201e0710f01a0142e80c400f05000c00350b41c42498105491009031001c281c00c0c2000c0b2000c1210341c465031059034100f066507120705c20490f03420080c40e080f40351684000c000c40d642405940030425201c0c0106050814183c3da543c9000800038002c804030350954583d10480110119401902e0b15140d031490148002c0c107001d44000c207400c01c180345d41c0782000912104900030714000e821030521084080c106040074a85000340d06038100c5484002c840d9000 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 808263525 1250 808262275 808262281
    0x90e0903092b080708070c1202090a0504062909060d170a121803141801080a201c1802060d0e16031509020622030503070317 55
    0x60048216803480d000241200901c40800040c0c0445070361101c030505078010b0003290940440d05100c00360080c984503601c020340c2e4601e40d01c1c11000700070495003c7c2250a04041c0030600503611840d81550100d076010000030240c0d160700388100070340b81c42e00d155442440ca41140b411401983e40100c1281c0506403410462030705c034403051114092200388060042c901f41748031040184c030381e04020074442000d450410740106400c1d00c1c0004440c0503502060700a03003071501c41010140c10151305030070004000451420902e041181d2100c1d6008802081d0401c04038000003007044080303a03c10745504401c410107013000180d10301398000c03541c003012030103400e1410542144040900341c018481c940d0341da1040360001104aa080c81740581109165544071520303910801c41c10103081008403031460402e400d83c0645880c43c00c5c00000890048111b9003560704080c0c900f400740c0c9031003044550342012980b40d4018004541405000040b05401c0100300f804001000c2082c15480182c2c0c40e400c80110100c406a52 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 808264775 1250 808263525 808263541
    0xc18030a0507210501020a05030901050a060302011209021315081009020f1002030d2c06010509010b07050f0a111c02101d06071b0501142a030307090e 66
    0x4221260000c1041d0b21090041c030004000b8003a210780b401442c0c0c56541c0000f110340d20982660440100306001500c04030411000c0300c424050650815550a0b0801000d800d50700024440e1a4002100d41480d4649410038115214104100c610200f40b4000b0450700e41c0c41d205404404100c3c0c401c28100d4810703154900384a2550344102200c17954000c0550040b0304064050010391a402c03a030000950205000002410100e4051030b070240036036003440485940000c9020300040010a02c4500503440440140a1740d02d8110132076055408040c85992102181d103030407803030800946d400344000d0040e4203139130b41009821a28031510300f03811600d140b100000a403810310385214100020350b10129041c03072003010902803905102c200a408458040f01d110031008142140e02000b0216901c80845480345003100c02e14890001a12003481d00c07040305542104041c0c542d0091900c100c850f5007840c452024078404003401d03240003900400c06d4a403289040400504503800c50310a030045000c420000031482 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 808266025 1250 808264775 808264783
    0x1b0106030317241804061b0c0314030603030c03181809060609040c050a03050f0f0c220f180c05060316030e0f060c0a1202070f080a030f02030c1803 65
    0x10301c3c0042440071610703640540001e416680590003a0403100c44c855116408413200f092521031401802c000c40c04e24808116440c2c442c0450440a003005686c0300c0400c002503000ca00d1220403031008405c19100e49411001a003544590f00d0b1620440c880001c00450080e43c241c40a1400003040340c8030360710344601c8070201c0420309048a0800803500078100184083c94642c4101742c003d802403540c0c1586640390400305405400356001540c00707034028400940e003418201300081d400302c98940501070001c644400b00b54603800400c403c401101c9030403519444040242e000c4070341e50701740720001e00501c410107170324120b410f0320340c5429140e00030a190041001c0c24000100e0340245503c0c09241a0507020b10030480c01086e41189070001070240aa00c10601b280810209002da40c03110508c1da500e250070306000d040510382d4009040c2080c01407151501181186503121341580c2c10884855440e030198108900a064883c029400544040705004030101010b02521800310220f003e060806004e504050740d07 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 808267275 1250 808266025 808266031
    0x40617070201060515030406060e0709030618050a3003051801090308010605130b0406110d03110f0a1e031a04021204060207150504151112040305030c1b0106030317 72
    0x2201e440c4d005c01c00410b58000040d60301c06e0017640005002c6889080ba1221200169500c000203600b95000740103110040c401c070007000c140580c0410fa042d0803075541c2611894642c2e8042e08410300c5101031840310703080281c0c0d0200841f09113219820380074040c00280040070240d5140058800d45042e6002c450b605103c0c0400044c2c01d80c90700140d507842c01c4422100ca902038001c04045010b0342000145054500380500040c0800351500300700081c4a12060b4544000c2041c031070205800c2841c5d42c00c00740d80c5c41c0100c80c507103111502031503587c1c040d141080c2d03a81282d85048840004603400c083c42030f158540d1040442110200d140042202e090040000780e0080d200c12805081c09040400c1c002038940c1c1c01084030380e20980b1a4140c80c4d0401041c0c00032038074111804c1c1c8401d412608525040f016500c501210000d4980103035007070280a203444d00f80100010300040c20f100f0000301140c011030180060f04c0d00c07203054417001c15461840002c42e902800007403004402007594403804161900002d20007501c = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 808268525 1250 808267275 808267279
    0x7020d0806090c090901030503030103030810140d030504080607122016060b060304200405221106070c1a043f12110c030717070b0406170702010605 65
    0x144544910742000321010026000020b101c40800041c0d85a44a0110044c000c41c05500916140e615505024150f01e200500b41e03841c03003000e000d05008072440d1880300561030f407054402a5209003280b90640d1503100b140c000c04401c1c8a20130800803010b0340848818003160000d64240818642081d0445901703005d0204640c491400388007408244500080d112451400742901141c1144940081515032384143c40c15543c80780000c2d000e01c4085c889003a075a08050055608001c1480c240701c14040d1240b24500080c2c0085d04100490103101c0c108140387e00107040200a16035031442e03450529006006446040050b180c5007003803451030890384041d64221a100503034024108900500ca05281c00f0759881409148400811031400809075003e20b01010701c2500d10307910006902802406054000001d03a1a60307100d600e16080c070380c40104000b4210765001d40740700d03114034080c0078203401d240580d0042d0907030110200300000c40f2980441010488140181c51030b000e038440c52400ca080c0c074100d00a843d = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 808269775 1250 808268525 808268537
    0x30c10090c03170327251707150e010c140a0203120c06010f080c010807020708060a0b09090d27080d0203030f1f180b031605030c010e0306070804080d0203160807020d 73
    0xc2d1000c030806c001920300d50100f503c00741c0c005440b41015142590a4000034400d079100800a2080742000c55403005002954104026403503000340008140d080840b41c01064401c01911107411703801c00308205030b42164005e0988810035908000b410342500300e420700c14a02d01c6410000601e9242c030018240a9070a0385001d002c000045100550301260f000c2c21080452180210005080000780301c020701034082c4030400705c1c1c1494803108004540b40058041c3c0754540219264841243e00240c580566401800c0d0510158441210100d2154801d40c8400450b014030034a20b26030039400b01c01503200341c00d0f40703081c1e4070300e519400c103d040c800c40003017103200d40901325101c2406901a0424030741c5070054003001c042110344e0904082410041004441d0a01060044080c071440c03405011120f540442032800d0040c150045001035510b52010700990203101059000c101401104000c507007644040d50420341d620f04012078154098540a0003580004162501041d504c6101081d40c41095895a03256 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 808271025 1250 808269775 808269793
    0x1518040213090201180e0a06061b031112120a0507020708103b0f03090105091c14070f0e0906181609050108010b03030c10090c03170327 60
    0x2540c010710605100703905000400316203540207020a8160390107010900018030302400c7c02c00c92482540d506400030002c0c03028449103498a46a103666501c46a50189089980706404840c0b80b804c0100c075020307580c500100010742404404030000700c10700400f07208100300a41d81e039040c4101d8172650240214000c0d43c000442c99100100c294104510b4900b03039402800d00d0b034a4880505411007445690418042c0131117041044000741071068140405000019516259a8100080683c822154114410102841e44102e00521142c480e4900d0364080000c00e10b07440c02e41095a070f15800d61080500000c40e0700c20128000311403000702805161602c3c01805541c807009081445800b40c2d1a2018141c46001c41481600e00b02d1040c4500500c62603600013815414440c542d82034850f400d05840c0254800c000e45040400c1c0051614000078103041e002660340b03003d10308482c40b003440d540080d125a1008a1001d40000400c0040d40a44003110f20340318805070707080a00f05030101c61030201205800400003 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 808272275 1250 808271025 808271059
    0x30c0402190302070618050607230a031508060108151b252103060803070c1a071a0708070e060a1407080c0a0b0a060f06121415180402 59
    0x240a01e01e202d10705c08a5101904488550741e041d846900f03a540780d01107000c2c0710209070000511070b0610b00c9a05e0b2546070100306d0a0004580c41040040800c01d5603d0380550034401e0004149000360901c0c0702603404d02e580d00d19640750f0381d40940051081620f101004900c041206010424001280712078040c1030403206454407050031501500794000e8030310f02152034002059045182605904060703c40e6902894600040440b040c58000300701c5680100514004100a00c1316503044500c000c121442928406454440364010100000c280000380605082e114924040345489200c003070390348051595550004031404540012180e030030401c02c1100c02c503134910841c0610702d100e41951005117404003590340c0082642c84600200d0783d541004040c04200030007018440c0e00301400c02800e20159003804130941e01c04d40184036240038130542c1c1c50003103401c10030758000e02000048409900d2180c0b5110381c583c0300150340043c00070b00c41e100c0c035609040c1107004801500c2c021034000e0701d40d042a42040c14 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 808273381 1106 808272275 808272277
    0x8060a1812080a06270c260403080609040314090105090d06020421050607031e0f060501020d03150308030a090807030e1009031a060111011406030c0402190302 70
    0x1180e950741700b1800160b0003403075181c10000e1070018082082e00c403891044000c0c03151104007000ca40d68540240b0038140300d00c1c0a600c8441c001d650b12000c01498082c101e40050101c4c0740500c940d001c0d001000c01900580a041c1031003031514004000013000d00400150483c0d05580000d1705000c0b00d0080261980400d0b110341c1c03440040703c51a83c0c0e8039299400100501d041568885500001001c05c800500c5502d10303c41d003c00080340141000320203030072280603050140c402d407020714030b015101e445403141501c107084da0750072003904503035a06026070b10191000e11083e8680c652000403c000100502a803171103070320780c1d191100c01c0b00706100390341c07001c25241c4c802e10003000c004002103502c00410380701115401110741c6244d42d4000059441301112190006298a058480c1103d482480000c2e40920421002c41e00741ca4050410841a4818100c0c03007001e225030700c11103009440c0250 = true := by decide +kernel

theorem cover : BRFrame.Cov 808093525 808273381 := by
  have h0 := BRFrame.cov_init 808093525
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808093525 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808093525 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808093525 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808093525 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808093525 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808093525 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808093525 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808093525 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808093525 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808093525 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808093525 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808093525 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808093525 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808093525 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808093525 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808093525 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808093525 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808093525 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808093525 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808093525 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808093525 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808093525 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808093525 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808093525 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808093525 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808093525 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808093525 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808093525 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808093525 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808093525 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808093525 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808093525 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808093525 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808093525 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808093525 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808093525 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808093525 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808093525 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808093525 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808093525 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808093525 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808093525 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808093525 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808093525 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808093525 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808093525 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808093525 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808093525 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808093525 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808093525 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808093525 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808093525 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808093525 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808093525 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808093525 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808093525 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808093525 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808093525 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808093525 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808093525 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808093525 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808093525 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808093525 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808093525 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808093525 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808093525 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808093525 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808093525 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808093525 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808093525 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808093525 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808093525 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808093525 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808093525 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808093525 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808093525 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808093525 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808093525 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808093525 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808093525 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808093525 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808093525 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808093525 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808093525 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808093525 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808093525 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808093525 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808093525 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808093525 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808093525 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808093525 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808093525 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808093525 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808093525 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808093525 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808093525 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808093525 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808093525 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808093525 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808093525 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808093525 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808093525 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808093525 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808093525 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808093525 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808093525 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808093525 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808093525 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808093525 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808093525 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808093525 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808093525 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808093525 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808093525 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808093525 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808093525 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808093525 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808093525 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808093525 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808093525 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808093525 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808093525 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808093525 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808093525 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808093525 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808093525 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808093525 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808093525 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808093525 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808093525 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808093525 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808093525 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808093525 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808093525 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808093525 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808093525 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808093525 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808093525 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808093525 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808093525 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808093525 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808093525 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808093525 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808093525 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 808093525 ≤ n) (h2 : n < 808273381) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
