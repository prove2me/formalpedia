-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3336
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T09:21:54.56907+00:00
-- url     : https://prove2.me/submissions/b7c03b56-7e89-43de-b2b2-b8330c205391

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 599820143 ≤ n < 600000000 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 599821393 1250 599820143 599820149
    0x1501031101032a030509010b0d0c0b030603120c0a02040506030109030903031b050102040806090613050d0807031d0a060b01231605250f06020c0f040605030307050303042325 76
    0x18640606888862541c545d00041c810b076441c0300208842c0051100304001c0341c0151200a20004601c0700610644011201443d000180581101c03507140c0a102e07510041d800c140701d44d40312507114509240039440e041c0240ba82080d400e80007008403c0194500a203030b00344902000d801d000040c401190b80002c00e13248080000d400038000c43d00d80d0344950040d6103a202c145c030b248100f0703c10035020401c15400540786c0c0c0c00c00303075001005013840c0516180586890b2002440801816500c449a2503d0000c2e40c1c200c6011408000141100340701c0740c07500d481110a82e42c1a20304100028400709201c80007000d1001552a003e9401502d81c01d0020409040001c5190b005085000308040109039402c090441c88012079401c0c00d500c0d82d50f440300c5500803101c11034441d86006034000c00c0340f005c490030300030700584c103245020b400800c0b201c1e00ca00100c1e1031035000c80c0c4110340c50b40c0000b080009020011140c010764605054a4001c4e111080d00030542e640400b00e00f507201283c10150455201d070b80c1507012402 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 599822643 1250 599821393 599821451
    0xa0311210f0a0b09060609160201090f0614010605090a05121207121e090e070e03071409090309030606100c0f030908011a100f05131403150103110103 66
    0x1204861a01c0a074a51030580b10441d20344803080301003510700c000400c1a900c514405084981c103507552507070001c1d030441c0600c070b13a0b000d6540c0d5042120104580007000081c05000700d0010407824003080d10036005c400c05074407d00420006100845d0316595800030101200c00444401c030b8480b16202d4203d0a080c151501c22618040018500c0200040700c605010001c0c02c075290048810355134450321012005100c0c1c80e0700010301044040c0300c0122040c50361a040f10081c94400c09400850000c20315002e030903086080d000d07507540a401030f07924064100560104405016500748407500c008603640740e6003c1c01d800c1c824010b410500e0b840d54890400e03038690340d8001c10713450320316840e9050240c5650303900d0143c1d61072542011690103492a60a034202c4410101808083c9003000e00f207030441700804ac20201c8410810f003040070756103840c00780320070340003400501740d02c017900340201000c1516096800841e10b00348400c8100400114004400700454000203003000305982d8004039800102802807108490 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 599823893 1250 599822643 599822653
    0xf061b08041203021911090a05041122060906081e07090c0516120e060a02210c030d06060e010c0308070c0c0302060d0c020607181206060b0706020a08060a031121 71
    0x10030f001124030355405021055078081012345800307030114191403040b1390161400c9044003a443c0581018820300d50324240400a40310340c0346491195405988455100e5000240c880c10148440300d000c0c420018401070002c001c4405c16240300440c1e40b01c0510348120ba4186075944120902103010310308881040d025a421003101d08013929104007410081d001250020742c0c884c650140509281d01140e5001c000768004000e803811442c1a010440d21403410001c441405200030840c01c1002c0000c1c1894090200c0c01003240c1d4285540104040d5448042c1810051a0000240446c0c0c201030801d80000c0340785004a4580840e080c080002046030340000c0d0401d0000071210078041c020351100344e28880e00d90031380d10b03143c4907490100e41c5000383c03a0150900a011240070011450b24081c40c0300c040e480b42c0404030350a641c030951054190081c0c0425100c050300003800403400b50388010780c10761012007100e130001c41d181140c0303824003040001103105014008619411040d0524041e0301c0d0349240c21a01112 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 599825143 1250 599823893 599823943
    0x901110a050a260702040b0111070f0302120a0b010b090418030507140d050f09130504051c090b03010302040c03060504150e1602060403081f0f061b0804120302 70
    0x159600c40d82e000c1a1100c03030445640314418500d85044004915640c250700382810019000c00000b0543d10340140c1c10b004060035101e200f1402486485c0040c800202216a0b40345540140600400c203041490401e0300071402c110001041010300c0c50640e0038010340c0b03644584442001c05d004026440d22104103240841da00003c00d0b030300c01e00805071507118540070092814041c2145031790b211a50400b002003282032240001d04000381c0c0182c005060001e165107003d4160f804200212203003030fa42554160885582b01c2a85908841180144109850030041842c0f030300c11407400030300042c00003c1c426910b5668419289209401c070001504008108111210503401c1141400d2003512681c594a00304a0001d9214000840321401d410340c1500500300503625650112402c400c0102002c00269581040110301284c0e264500050849541c0a40190342014400b400f205601410655550300c0e034002100020340c92000d503001c480b03035045440e80b03510003450140c2c285040b2010004016003a04059 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 599826393 1250 599825143 599825153
    0xc20040203150319021c020f0907110f030c0a14011d07140102030f1e0c101d0c0d0204051b0c16050108070c11040f0f0f05130f080901110a 61
    0x1c2c07410014220304541c02c42e0781074070742030018040401010703500c014070500300c160b03804000e00c0403074000780300520741050b0452010005a049006842d05400207034103029000340d11300c08100840d0410311050048d801d00b800c01c0111039865002da880103040d8010a41400354501094024545260064000c011102c1d01d0602e01940c9841c03901c10001d40f44406680f10300154004001c80303082c103811202240c60304060900720704040c5840783d00c01080c140b04005020718400d060040c0d511600103400013082e01c2c17100340b411540002e0750120400b4940c122003040c8000d56124a80320103c190705039408100c507a580c8944040101c01298440e41c00c0c10001481661200701046420308103101c41c0c54011080d0f03c880c01102c4941d0301b2a419004580340c036a468020818100035032540040003840032030b01000310042d001c11380c3c48402d00c1008580c1c4895003040e00303601c0c2d03020312540185800d030031155080c0142c48910006040000180681c200043c413502c2c564411071351080b012100313204a814001c1c0b24900 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 599827643 1250 599826393 599826421
    0x60809190215120613060602030f0309160909110a06050d0b010e101e03020f03130c09090809040c1d12010b09040818031209040f06030b130605090303070c20040203 72
    0xb592088228010003100001701d0b00c82d21041d80c0a660040d811b06402003011010382c1d1018011009a03c2400c40c40c3c1c580044940406000d4540340d13001040e0103e081c81c1101005224001151040c0103440742400510303800800d4a03808a5040c01c04503000c1c490000603290704a4200a0a401009444515089581000c070a07118885070f901c490082c494001d03412001c03402510030f039040c02581040403484031440301c442c41c080180030f0030200081c141c2d1041c013a0304a401448048680c2000071038074103030502c0d0a200303a0400354145c0c10b05030904034040e0860780100308c54401e0544100f000c00d10310382d8149800d5102c4d80d4400740c040c01c040c0a40c1454100315a26030002420744000700d00f864200300d59428045880d90f821000840c0c89030410302040104000b42c92404102c0700541c1c0c1e51440007000c520400e4402340160300100010011143c11708148080e07603002400394038194001c100380310030300d64811f0404641030340260102c001d005180c1c4107600d001003e00251580719001000b404a00e03078203018 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 599828893 1250 599827643 599827651
    0x4261c232b02030115050304060f020a09170d08061905041d0d030e030417100c0f021603020d110a032a05030c01021c03060f0e0a0606080919021512 65
    0x307890840c04000ea01d05002d911007401035030360b00e800f21900b074031106001c1da0107907410030310901303000c1418201e03445000700326000580d540000862024041001c0741449041d0b030306403614100905604401520041e00617100540401e010b0b43d41000d0580b000c0b0061040a40503001c0184180090703406060b1a2103425015101000f4600440c82441030041c0a441407141d45411040514141890710303050480f045c0d804144410140555050840074103913034410b0200005c4943c41351012180e500c0002850404d40d6030000201041015080c005030340c0e05030107200c88076030140c0c001c0d1f9000c5041001ca84020b08070381c8000c1c546100d0b51052080341221a11144440f4202549180550750f50000c240e50f07003641c0460140941c11038410340d08a80303a20000b0940c1e220351820003007000c564906144800b881c040d80910800b01d6000d0500c08210024042c10008200038a8030003403c0c14220207080c1c440760001ca0240303101020300c0300b45046494014004100e181e040310b0031038560300410002204030360119 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 599830143 1250 599828893 599828947
    0x10b06030907062a021012090510060807050a0504110903030a0908060c0306130e010b13140601030b061611060f030907090e07270204261c23 62
    0x140d40e2000d0380c81004e00221041c40786500c0d03014408050303000d200b0400300d1041c40d00b081021502003408000206d0003954100e620071001845075444d81e0003450115100c9401200d080e4110760420041c641c0c599240e041601c00c211800240119940e14a080c0780c81442d040e584c041c000411440c0c070094100c403101003120002000c4e5907040d901c0b10240c01d142e100c1295000e500000c2c0038100c5071034030115441418645040400003810456190019040d21404c0240c0080c00da01c8aa0164414818819880d0000805e007400c1c88050076000024601d4011007443c01407007080da071903010602c4484000c3d225203c1d400703400b643da110070000c1c8a00300c503842203469403064440c2e0030000983c00c0300d030320494802c40d0700b04001d000d04138102030043c400201c004540101c60b0500b918a0340340012140b00800081250160309440c1c0816004e00c160704041c0010b01d46015000744600c415681030820a40041140ca0318007403c14510300e00c511040e80441315140b4580c42c8001c40ca400e4040c0c0103483c0701d40203150f52 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 599831393 1250 599830143 599830157
    0x60c0f0a06060b070b010308090f040f020a0219050303062e050d1506051606060801110901110d12110c0703110a0506030412050f1b011d030304050618010b0603090706 73
    0x6070f5101d90b01440707040c000a02201300300c001040464022000f5090b003020040c00c1072200003030f12002a051f20032520001e0240d641c00034150f41d18940402c501100e1905503010440e001600d6107c09441e030000030105030088080e03481c510001e508042c1d903040d18a04842e40410803294013400141150010250144202d01e058940c0c08610b182d070f040d0784115451684d50358503041d041c00301c100e12212121000c95241d03495160103d2905000e024400c10031841c0b071552500e60300704000050a0741c20031440d1030f02c079420822641d01c2c02c2d075000b1800584c40310030400c0400c1500d015800d00c0c0c22440b4064081070b4601030301c400030040156101406a0b08001125555036240e260803c0000ea4402990000c101440060004070030b580190041c01c0d01203101c403040c42c100380000e44040e03134500505140000366503560118500c0000c12410311095001d00e1001542945850740d11182e44103005005560240d0070003510716000c10003504115a5104003411030340c2c032801d0095102d6034844850298074003056030 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 599832643 1250 599831393 599831399
    0x3180f15020c0a06110a08030c03100b03241c03030609060f08030409270c061407030c06050606041802030a1107030816031104060804120f09060e060c0f0a0606 70
    0x400941e1035141040245041e2401346010815580c2e128448040c82540c002d4030301040c0403c52244c0618401c40c3c0d800801685c9150465580c5484491a005503c2c00380d414410311902c24a44000801c10010068020000ba11540c001802c1c10051441d003000c0030ba00c100c000700c1010307415044082150802441809426203e4036400c030510440c0c010210790b98030a101c00c1110402a0300664441040c244080c001107401d845246600c2d1051003055541d0015420104035956000f80000b440c0c440b0450341c98201905d641d0001c040704510303203001d481641c035000811041d5030b5281c212030007013072282e0307081e1407481c5040241ca001c2d41007140c000122030710b07105541044481e0401202d00d1039503d90340d00e410079503585410564240310103c4da40200355480300c18040c00188480100301511194803688294500b5150205101a400340e41e04204510800d000c010203400c15500d009481d81410032002c030750080e001180d82c80c00380341c1c009516481b9601000040c81008180d914459010304002e00c51162 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 599833893 1250 599832643 599832647
    0x10030501050d030c06060b0a0c12080c09101218021207080607050a0e0a0311190b03070c0503120709050306010e15010e0301090f3903020d03180f15 65
    0x210910070141c201d81098a140000780c800c060001302203104500000e002a21045403000742c3d0003d1007a040801c960b40541b00500078424078543c501c01240c075110b59079181800c5690494080c88600c0d6015034040030200480d03a00628841401c401d00700c808001c01031a202088000382ca03250001ea01846c0341d4807240c0513070000440d5410603903646500074207050300d60b9001120300c2d0340304000880401900d181603c0b42c81c1d03203140385000110b009e15542030b041c40b8a8801c00116400c400c40001400304031440422621130703d00207590788911300d41003041c85042c207810068207512442c41560030b00c40030501004452a0441070240669100b5811030310160380307402503a5807081d0252620314840e80844103000880d8404d2000255036100500003050840311503482c0c2c105105004000c9500301d00c000b80001c0c0128044042d100b21005004422219182c6044000c1758034105003c00390044d500c4c0d140400030b260203003100d194076600c00660350791003a944001e0112048014007071241d207550700c2098103031114 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 599835143 1250 599833893 599833901
    0x20c3d0b0303121314010203010918260f0c01060807080307080313110d060c0f09030c0509060f030a0803013308090f0118050c1c0b04060207140c1003 66
    0x51805001146441407000d9402c0e8180b1006015003107038a4074200d00000110455002c400317440d507403800075032254140111141501e03205a01004180000040e41d400706a0703d83d00114801000b000210b10164500e4590410f0312416008100006000500340481322055010358110f41c26079003a51081c0361075920480e12071251003005002d9140034000301d403440f816070f42c2e1100403030720841010070000d4100c0003050031075a100f41d0030380d512982d03000e004205035007001c25840115020700e4520340d60ba0640c1e4500000510f81e028050190b121074001a00d1921400c036904000b40d0018100c800c076055518003112594424018843c6400409103801103541540c0454044408041d04113800303042f0901e4121101c041c01004803070310344a0f05084800c596820310031040c02070014468151440400c1c18800c3c40d10000f07003000c90207011061681040e0740c407048005070702260b00451407003407502d8038206040a03001d4603602802c0c01141c0c4a038450b04000005040303209a4080d03d5182461068060690481e = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 599836393 1250 599835143 599835161
    0x2040c140706020a021c0c03020c060903150603030d060f0612090803040b0a0b060a090e0105030304030b1b0705062701060503030d020c15070c051b0a050103020c3d 72
    0x2010003806990700184458002e010380400ca88101ca40c032080098590745201e800c6d03651640800c400300041d6090550501c0341c100c40000079140c2515002c084000310355078011024004110b1a00740300440c1d000d98040c002c544061400c0d641c00c3c4074581c0c0320003030030a030f610307071442204089200540701804981d002d012740c0c3c0c28613412030f18540c1981d41e280c031418840e441c0140300c0101c00759541c1e0798174040e40c0c608024008c44041503035244c1c0701da03081c003010381190a01038001c18401c0c0d0042c0000c100003080021100e034800c0e41000000e01e0080a1012000a4000c0781001480b60084004000e01c0f05d51020030706469000001c865071404080f500402d080360624040c0300d030035803c00c00c528200d03103400e49c00802c3c9080b010301c11507240100a20828600306003c0e180b120002c1c0c0301c0c07018182440340400848694402060850100101040005d40d0806081c464541407580100d2144211402031107000388100e000302c11a580d414112812241504000b052161040448104002070b52958441c030498 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 599837643 1250 599836393 599836427
    0x40803091527031210090606020f030a0e0109090c050d0501060c0b060f0f1302090906091302090604110307110f210d0603150504061d0303060910091802040c 69
    0x50180710514119080d0100c282d29059840104080014058044911480f4180c40c0100d48000b50901042e00103440c41d590003031007194030031509600410700100c1111030580e4941000d2070300c20840001038940004550120b01614503140004040d960000b0081204060b0302c0010005681c88042c1a542c1c0c10301c414000c0d0118041c00c0c0042e8660815a1400c1a41c4600502c1c41d4044202180010801fa8a101c03102c450380340c0204051159061400c0019007000c0704a4101d030036458500e40d555074002d044030001e8421203e03d408101c0c1a155a4002c103003180e00951216540d1407c0c441c0a803100815962803503451040030009043d01c2000309000c00c00c18590404011181d1407450a1801500041410074074a42d886400100242150580000394030795030760082002d00c4c050500b641181c030403c012101c81c1e4407085500b41100c0c804011282d01020481d44841640ca400d840c580c0820004d8010b4031846140c148601e80d02041c6240c0b0003220380c82100c09111502c903800007120162103507900c040e0 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 599838893 1250 599837643 599837671
    0x8040824180102040801180b010f081005060415080f0c06040f06050d0b0d03081b030f010308130f0b07020306090c0928020304030518030d0219030e0303030408030915 73
    0x120071620480e0000e5801d0304040003606254850f04d0840c03c40781d510202c5444c54401c01c800703030100000c00f901030b0700404500a03c0300c03001e40781202e000d444000801e0720490701c60baa0000200c0e41d81d6145e100c58055040001c7e040300d02901c0c1c4010a6513214000a072000500c282074480642e450400100c1e01901c070040d12505c00c0c00e240a0058400d0b4011020340404540c581c01d048126480348505105075034001c1d545d86015007003035000c40100c001c020214403c400c03c1081000204843c0c0206981103903031141d042c0380d949240785455450000c160700f00e0740fa2003c00c5500000e01140035406800c1d141e0084080e203201c0c1d207401c2041d5981c0d944840c0d01a412005d198002000d140040714548801d02604d0711050744451410341020487e8000c03501200465400304040c4880034215a5646504406a00910800d125000060741ea1144806034004414076901e401082601c110780c41c4608050140840e43c490074540703010846a0030456801003103125188242d14510344081500d809808109a800 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 599840143 1250 599838893 599838901
    0xf10050d08040b03040309050907021b0607031206170c06031510020a06050a1a030d090e09030f07060b011b1106250303140a0c1710050d08040824 64
    0x40c401544110644401009200003e6040b00160085100e207219980b44d40c0c4603400d013400c21051030001b03003d0a085510030084148180c03a40c520f507007810f5904642c2d803901c85e2498503045907a10346559807048076500b400340008070800583c48400e180640d0340150f44020b0322200a1064900048600302c9440203020384508150810300e600803125116841503500c07603d0310b03850b61010f5039403d440300ea4400d5907030001403043e00c0c2d03020f41550002800310060145100d04500080240a041c06203004042c0309a0110f01c10150810440d10700c0300f010302c0f28540344c50f442d0910b9001809040000360210319400c1c0300100480d80c0710b800548459100c1c400c0f40d040d010007818419150000282c01c1c1940150407407040b105141c40c61400301c190b202c0e90300840d440510003a03141d400b010150640d0381c25070528483c044082d0700f0081c1c48691103486030120074113598140304004900d020b903010f1608002d01803160010300414100030800d0700d404200b1140c00d101c0c0b150100308606144103680990b40c02404c045 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 599841393 1250 599840143 599840149
    0x5040e12070f0c0608100e011410030609110301051e10030216060e0609010e060705040621091406060303070807020103090c030b10240c1b0e0f0403080f1005 69
    0x1d00345003402a021606840c050366104940c1c10341c103401c180c010a0b030f00400c120042d00f2521020000d8100e0340080b202d2549003d25120846860108652060800104004640d4820f030b00c200000d100061051200b42182511115164005c1c0a56805070111445000400400c03c0000600620203030410703d84c43c919480840094024607510f941404c280c079620310104045010310000303c804040981803505045e10b80d1400c50307100d400f003c25150400802c02144503000000c0e0f404444603400c3c40b81d00a003035075a03609421300c1443c144201c140d18188035203051050101d511424121158101d03443c0303440345020940e80340503619005145e00000c2005c0b900551182e004104014071803840e40c00c0d41e5489130382d012400b81044504c1c1440d10400e410410408181d01603411103c100103100b9420490014002843c0e20b6600c00042c000304031081c2c0c031003000012224000010080a0650007842c1070414601c0314031502a101a0700080d00d80002c60342c208000e10300180180c8103410310b40c807040d00d09024 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 599842643 1250 599841393 599841397
    0x603010c021203100302041a03010b031605060d09060c033812150c1312020d0b0c0c0a06020a030501080115030b0709030221190b041b0504020a020703020a05040e12 72
    0x2e28180400d0701c1030000050b100c41c0281000491a0211962014000800c9c10b00b115008802d65100798000c94141c0c420307040c0c444444c0c05a850079135850740da4050803454000505000607000784080d20700060411284d0b0304d64405160600c4442c42c000c44400c8020540440c0310310304440c001005e0010400789a03e00c2d0502e50428417000762010ba03000c10301e241e2052141084225616010034600040c040050701c011403000c0080d00140c103020103911000e4012501055034144020540030404000c580349010307001c1981e400e03008a50403189244c10030f1502c400613410079907028000c6030400002040c40c0d00180102100da442d1032209044061550f160001915009004441444004880400982c496260120104666280c448060b822927221586410303100c000a4504a02544195001405407640c59400640100f5402417006601da4114085045d43d031150340c0c07281c40020036810302900400c0300801c8900071140804140d075150144015289482c89a44840c0c1110180403409008000 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 599843893 1250 599842643 599842651
    0x5121503210324030d180b1c09020a050a0b0d051005010c0f030e1309020f03060601020a1101030b0a03030804050106081b091906080601240e01030c171e0603010c021203 74
    0x1c4407003102c3d0a072601180c00c207411040500002a903050164140c5200250000028410550b143c0c3c41c0c03e0040100603030307a046080140d080c80e626100c400e0706640c0c9104c207020182900400440c00780b03540b8101d8682583c404044045068204000100c038440c000310810100e07036042e1142440c00c102c9a484c24070801e80c5070302c120148041d030007950507191030340c1c800b0043c1c5509400c00010b00318840c4c010050401c40d1401d40c0b03440f90f4072000030084c0c1e0740d030301180c0c0c440110360107604079064031681b00045c0d01801d0320081c5203420501200300042855400741030103000b80c0c003610003040b4807070700d6880c201d855590b18540030040384c01c00700d04004a030600c11000303079004614032003404c221212110040e0a94080b0342c407181c4540d01c0040140701d1442c024294000800084050074014070520700058200c0c1c1011007018141640c5e0748039010464058017045106441c0c00c8100d002929000b800ca280343c60340400740c0052200140005030050405116481880b0801c0e0010a50307284000d22480c0180c0c0010 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 599845143 1250 599843893 599843941
    0x603010f140112060801020c010605040203041101051305060703080403080f01240210060308191d1519020f1212150307080a0309140103020304020d060c051215032103 73
    0x1803450300080250304c00c00010f000801c00260b40d406c0806c0c80c071030035a4001e1304028450f510420034400003905018118108aa080c28801d8844440c00b1f1140030300c00e540c0e801607070803850008800041581c4210194800d51023900c81190b1500d0303a040794101fa00003401001610390f0000e03228846207a0341e02c0807001c02000d510485464009105d040c40603900298411225000081421040107212034007a00310302107503203400d001c40e0b2155142c0c042107100502203107015458540e409010900c1e51005c13a0034441076452003002102101400075910500340e524811207000392512800100b54940c1103e12600241c4900050313a12503a1141d8986500e60b8080356141c030030644009108030042c410400018002d881d0080030034600311f201c00c0b050b007221800350704040c410010000140d81c0e600d24400c42682180e40001c1c21002c0744029038040c0700301441c220a04e4603007402c2282500403889a52244035083c0c054400d0b100d1485c0b981d500307074000148200b840c2c0d44c0500c00a00e103440241485401c0441003 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 599846393 1250 599845143 599845157
    0x50f030307020411040617070e0607061103040c050a090c080f060418030918181202030f0d02091c08040306092f041b0f051602060c0a050c0603010f1401 67
    0x1a800942258581142c144d000c42c80840c1c10042d898001042c4e484c0e00c6007072907482010f49008100101240100c403070841c0f107110003042da4414014154040e00784a070110254640d281454182040030f1003207841203c0c4941c800b40702c08100e6103441d000340b9a104995807211561612600d4800300c00d00c00041c8419001070340d940d881d03664000845200380c40103010b41c650501850030101c1854aa14a003d07811300c1d120700700380802d8821202c45c003180e00000d80240d05008800e004910032800d600c602d0b046000c9070300c00401d0400015855a004160250007240d21400d03c4100650307031000c0070081c803009800d000f0700348010170205030b1640000c20b01602c44c2c8101c035541c09000c154902c155403916901600080303606510007150900e0310030384108010a0b00e042c0c510484021008081328090511201002f0b00458410039003190707001e04030325040cdd0003807440e6210600110030645c0c0d1251600160345522070039401c2145410100c04890684895032500010541003120045400c039404044a04201d00 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 599847643 1250 599846393 599846407
    0x18060d0602071b0f050105070818030601060e0901090b06030117030f0d0b010e0f100518040c0c02031504120e030a061406030c06040f06030b0307120b04060608011401050f0303 77
    0x200c0c0700804070309200342c000c040c0509145034441d11101c1181c01c1222829001102171000303a03000300550380c807554408400ca41c0c3e45c051451603001400c82100c95134240c428500049942504415408131018040d15401c1442ea42c41c10b0080990740e1281c030050304101c003000103100d0303460454800d40f000c003400340803207150030291040a0314503071020100c1d01905945501c613043d90340c0d124409841d900c0f1308980240c903100702c22000030a00201001d050051020000f00700e030503507110520341d07007101d90010420444504089005002c2c281511002c03031280c050766111445d0441080305ca039004a810210308009075040705802e46948511806050303252040c01a904e00145990240c504241c0401c8400d00b000c2c2440010315180904511035580309410500003800807141d4844c480c03044a0702460042000380383c030780100c3d04001c015040b40600342d00f4108070398244108111240d014620944e0104146551464094203c900c82c0c004040c0100e1b040c80100140c3c036103480f00404101c0c3c02802c1d2881c3c818 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 599848893 1250 599847643 599847653
    0xf0311150406030b040516140a030908030c0a0314070e010813230d031e05180f011406060901080a0f020408070f180509070e0a0219021b01020c18060d 66
    0x1250b4000000a41c0f102c144ca0b0700c070300380b501505401c49030304058442c940c1e1452101628070082c6802400b11f5080120304240d03c0e0b842500250500c5070400c05503542c0e8203000885001d10b90065000d8404030307080141e11940f094401003841d2285c81140c1c1d40040c45512903004443c5c91001502003001151402c1c035103030102340e49403514050210880d084500b9840142c08560070318402d04103c40c01e02d0315011900c1240c20306004014030640f0307241000aa10f03a2000d260b00500b4010481c034030441c1c410074405000084d415401a004404100e0150700c940d40d48030100321603445240843d40c001880308000c21302141058000419001d002c04025050644a140c49403504550f0342c440108514404402c00c102c401541c2c070000e00d0b07040e00c4014043c0307141140032240c1d01e02c0c2038490001e0900c114000038192202c681d040c3d0344c40c0d441190f8018180d00070800000c0d0344208800307015241007001243c58619600014601408410143c0010300400b449946452000b100910325a0131444412400740010 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 599850143 1250 599848893 599848897
    0x50c180a0e030904180c0915031e050604030c031106010b0d020c01060b2212050a02090a0e06070e090723090307030c030c1d040305091e040603080910090f031115 71
    0x81103d05e00e080c00c1c0c080d81c181a050410316a0121604e5441d1402080c0e4044500141009481d08841c5401d185030540b000d601d0701200860700640a405045c091008241e0b120101094250003039131155120007005040d691218028490540041c0c0c2c10070424495954680242515818850000030f88a681d541d070034a16500181c1c0115000e4000c80c000c00318980301183c7d91001d46651402c907032140081d036491650325a0b400d0006881443c0010029408411a411003c800d50815084d160350781080311010740706418580000d4801c10b4040c00041845108910941c1c96001001c10417000e078404610b8068158401010725070980903140010001c03840300e14012004503c215110b10701d6618042014000c204c0640301800c041c0741e61400d000c0803d50010071b030707404214120b69902c0b0140190b01d03044200b4110740c084030380280c01d1103000400c1c032400c4000361441e00e0041c0c0c4c100fa010340e200e01080301c502140d4002d08030742d15070b42c1d081880480e0000d896051104000303001440c21440640d4036003029 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 599851393 1250 599850143 599850161
    0x20907050418020421020303040906031101090605120a23100504110a0e0603100801140601080a3b06180c010503152404030f050c180a0e030904 63
    0x42080090708000d202d07a4626607001d0346016850850526040c441045000622606501c00100d04050400c095503424002c50f03004140f140002c00881d5568607017500c0341c80c403135a50180422a207030000280140100100ea0f042104072010780394680e500c806240041805440d0204070340400d9030400214410b6a0440e40601c09041302e00301c94a10f41002c02043d909200300540c4000014084490b080750000300035080c50f0700440d42117850355120b10500c8100349840d032080d2070395828a101044120700b0b20810078001c0000ba40c840c0c8081d81c0d114106026104801c0c040030740d00c1e00343c115582c04100030111060340c00c6140d0f06c1080000081122143c40c0100540341100d19001c841c81d0300e010440f040001c2880180e00382801c03411450010069a030141c5680301c528010907611511403840401507002074045100c01290a8803244c807401c1c10510300030f201c00121228070600b1800102843d001e12002d4003528240080c1d00c90ba0360313070205d520103808120102e503428841800034901c982e0310341c001e013650 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 599852643 1250 599851393 599851397
    0x21040503040506070303020429070803070210060306090201030b0f060906280807022a1201090b070c06050c070206160827041505010807030b0307050a09090b010b0f070f0f020907 78
    0x103441c1410070043c0c0c0d0207103c40ca000011540c80508109d0480580156030702d1030b402090850320703a0b40d40c0b2016410306510210061b8254901400442002595401210703040d00030380e020014007402005201c0301d00d4080309075503800b6000b0f0207001c513246051801455000d034160003528600c500740104594141c200342d814400b2402450030801d0380365040105114000c4200d1103609001508c4030006000c540014a0b10f010b50b0000c03650019840f02504505803282d4044c05d807503482d240948008090584aa0003100c0e800c1c1400b0208009404050586417150b4000300754500e0300344100940080012101707801c91b422802404221680b03c081d007900003031100c541000c0480704101030200300840d8449855601001e44a00f0700b03004990b40310302d505034420510b040010307618800d070002078030344038140d071040b5402448988040391440300d9810110046115052402c440c0c1d8a82041c800e107402803601702c0540f0b05061111401049841580309116400740f43c040c0c8075418150007145503880c04441d0303000 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 599853893 1250 599852643 599852647
    0x20105130e340c0f14010b0a060314010905190f050402010e010f020a14160b0a1412061507060e0c0901050109060e10030608070612112104050304050607030302 70
    0x30390314400c079041d1801c036018001480606801e00700080c0960544160070040101105085081080030700741030030110340144c2c17802c0fa0300040600140c080c0854114032800355104240c0022014002d00485c801c4084403801071103140c0c00e104258004020041440003005072800d85919480c1491091001c9078030041c0d4007146624240c000074103024200c8480d541041a200c02841c04c03a0782c04508041180e0340300002242c0380c2c8600d00ca90f460003031007404200014008040000300b0042c1900140100303480c44d21960710710b0083c80300c155194000c56a902c08080516400100e4518083e4003010b0301c2c1401a00c11800c02210307032a01d40c00c030348101c0e03502d0a40fa8002e41001489151140d04140185802d1804800746401c0480091100403d4045203002d481a0300302c3d56222402030b0003c1002d040f41c03408072000655200700c000d01040303a001542c104035103464005012405000c0440701d17100c4600d450184a940000e8000065010041003641c0c0e6000a100200e0540c2d65000102403a034040e542c007503 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 599855143 1250 599853893 599853901
    0x905010605090f13060b030d030b03070e0108150403030f02030108010b04060f05060d0203090f0a030f08090c011b060b0a26031602091015050703020606090402030712020105130e 78
    0x24216a06500824402c4030030a04012425142a000e142d015400c120b40406201c0d191500901400000081c03e40c180943c3c01000c030300c07d500d40d106890040d03080303089403411030783c1c2d04000500c441c003800ba00c22690014940c400305e6140039902141c0191003407038000b544c6c220030304003c0d00326042a0031a1005035102d40080c0d4aa240502800014080184203101c100d407400300014114030560b2001340c0d600b0b80210010391004801c0c494645449441021344090080070f145c01030540c0f984817031940200f8020408140a0600003c4203880c648043c2c40b582244041466020704071100e002048070709035218421050f4a89500d20280c0040c0f04502c6160580e46130543c00030241211481e51000c198018080719000b502c00c1001030034103640607115500152109607140f0003c40e00303508261000102c11182c505116445001040110301940c00e40b50f0355195030341000803032001614042e50650104000f844040d56500c0d40d00e8450340b05040403450010703551300700d00020082d940208150b101c018200 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 599856393 1250 599855143 599855153
    0x307260304200a05030d0e010e04091208070512060d02030109060e0d090506030402090f040f050307150617061603020d060b04050102010e060c0f25051b06040b04150e060d09 76
    0x4560101e0110fa11501c0c140c01c001c040380e602c010154450081100c1d42e160002c4c80e901a0750070f86d04031800604288030310042070030700c5000054500d220ba07000901e4240011010341c4100107813041d46140c902c0c40d42c205c1c0c8884080042c0034550100983e0b255503a03a94000c001006d52280550010f030860203054a8408828043e080b155154406406400308000300001a941c48054170303803025103544480c06540340c605000150354010400200030384000200c440030301c03880c0d0442c4021046400810f21800352601c030840320010b20303104483e03200c0d80000c02160402c410b0103d0401210f03035074600141408820030144040e60807903400440c8403d00002c0901942d64280948410721070120001c2c10307641010030a40000c0d120700c0b04d80034140380001c2400078401c1c20b40801e071040d01c60201c00040b103000700ca050060f1100103202d04176030070312100d4820a0b0305090080640d004c540507410200d090074500303402c0c0301d51400e4082c026410000d5040740c006640c1d44600181c1700401181c0e20000c5e07550620310704 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 599857643 1250 599856393 599856443
    0x2b15020c1c09120c0e040f02031b130b060a0f02011b11071d150303120c09130605010e012d0c050d0302090d02040b0a03060e2b020307260304 62
    0x4003c0e10b00041e0b003804008260344600c44070495400008000041c1d1760303420400342d02400050029890301441d10b20221a02c9840824517414004903a405c09814038000301000b250480454150000c00c24072501c030741c80f4080c581801c2d000000f40004200d40c0000719004040c1d071500d00c4900c0200350b004143c150822000c22098010740304a020481030f01030000b4007501e0310f100040500030001c00c018200c883c99101801a2403181d50840000c40349403c04114140f801c3e0040306401c4c0c002c1820800e03011144480d80629000c40760181c40b0141081c21850046408071220782110582940c2452a0488460091150f02c00ca019030755804400a1041c90600d0070305c06443d2002080500510103010240c2e00d90f6aa1601c065044500082c0c0c1c402c0b100c080750021080f076001504191130104130518040340070a065401e404600041c144540b580420030035415440d150400051b4014082900000c0c1c400481003030a0340c0c0c40e50354054502841031402c41030380c0308a030100c944000c03545268840c000480c00c = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 599858893 1250 599857643 599857649
    0x801110a030f0b01140c01061d1602070b0d23040b090d0903020901090c02010f090305181935151320040b1e2b15020c1c09 54
    0x1080c8004400d03c000201001d40010203542c0c020000940ca81c100e0500b54030010042681d012200980c43c11185522807003041150107074012610022004165480454007400707441074220128201905944101e000b04040d64007041c1c46645030500c0020b0340390f89200c440c4070f2481190102601c0c54086501170030841c0c100507407402d00070300b1174090005a0710a81d580c0d056600280340042e1711035450704202d01400b14202c1d0f140c002854060404280f540c4400240030448001b0b601a100c1c2000c14107002d188404099010141c4010200c144007625803520090390482511052402d1561601c0700714803804400c203080d42c680d60040300000540b543c4111840e40c000d013095510341d083e2120341c035403171603500058405500650245404c0011651b8a5004c0d240c17090001c3e0128016801c040070702007101a00000b1036110350810b0b98044a6001480c440c200d01c050262082a9406529a030703114140c108000500d9a07282c09100c4012525800c004d0403001480708a215004180240805440040315030 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 599860143 1250 599858893 599858921
    0x9011704030804080d1d060f0c04080703060e01090515100b1204030c140a03110105010e060102190804090f020a0909020c0c12032b0506031f020a090801110a03 70
    0x4100004250003004440d48103030400740055480c104008000f0061006d914440c5d80c0707103566043c244490030f00080807441a0746400200c1c2e86078a0f007200c021000d02486c4200005980502d40038400183c0942200d4030041d00c1e1400454822140d1f61403c1c18600c406110042d045005000c001045405104a038001d010002d002c1c1c0c90914058441c2d0341c3d28100410203030030311800c0010002040001040d2026560190068401c2c10211b860002c1001c050640d00b03070f0303003903003081d00110307a5420a403c11400750070140c0007440e903800b03004100000c0709416401910300460034000041c1c1c8000a000e004041070a0200059540701074441c090111822a00004e280030703c18010881701c00f41c0011fa032164002d08845041e204038500e0400b500e103202e59405070303400c0a2602d01c5078401e000030031106025044000030600c1150749020a043c1d50710140b90341002c0500001e004101d11041540c001d10004005281c0b2118040c1c07120302141c2510380703181c100400f0007000103981c0c005d81e0340743c0304000d0100380c07030 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 599861393 1250 599860143 599860187
    0xa020609060f0a080915060d02042003090a02010315151d0a14120d05040b0f071a01060f080f0c09030a05011e0b0a0503032b0e0a11180a0f09080705030901 68
    0x6080400c0116022302402030085503141c1880030180002d02000c2400c9030506402d40d52407510a1445c1d031108150481240070030704141c07001c0aa22000440801640c44044009240c0458141d04a4443020b0001c0c1d03241000d0740d0a10400141c4d2980398455010b0520b00d11070503003d901c0b51091002d003149254221a00b07070001d40c4581e0200b80d0040496088460302140d0071740720049403c80814070700c50a00d0080011581d00c41075410a480040300d64126880e544034032054a5a280c02a0750b00001160401031017509000000c81c1d86015001030003d0400240458803160711540d2101d08491003101d68003c10400c0d000071490140240c050000070a4060300c010070041c5c90304000c03c2da40d003d030382c2da0200414604c000c89011054100404600c3e082c40c80400d0201c1c0c4146040c06440b4003010314240c503179020004403080b017400e081e04011150981c25178004116542c00120303000904441d0b40e078118260321503200501241c680c0015203071b824010000356959404180000d000c80705507281c3c04880d0090 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 599862643 1250 599861393 599861401
    0x60809010212060f0f090112110d0f02010c2901080d0c15050c072001080a1820030a0804230a0612021309090b06030f0a020609060f0a080915 62
    0x70701c0c0c8400d50489400d8940e80e4100d0607480000361814505c0d908990001c1008000003440d261154041480d5401f07003104600c820b0084003403041300c0d0740440020344103405081c90080194400c3c1e5032111594022020b03030091100368152070302c246820301c0c40301c000e1042010051003100303424070450190380c1060a001500440a590703951045000d040719042c15070f40c501c00034003018421801c0f1031040ba44030114583d600d050b00c4840e10104521034610340000c2c80200065070725180c40c0f050602048040040480c3c3e50304030b98032414208100d1030720f080f00d0a41071000e00700307548007000215461486001c1182c0c5842c28034504840348004690030400c1081c00b403a07140e15a403120301ca440240c8826152520480c000c81c0c100b007002c0d02c00d0310b122082d4650041e10014401000d5442807a4092040c512000e6070740301d52041690761200308200304c07299085051307030b500146400401001c5603240034203880c4c2810703552640c40f02160030011541000c103e0800411500c0d03d800c0c082090800700c800340f2600c15081c = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 599863893 1250 599862643 599862667
    0x1020c03150a180302070f051008040b06031002030c07021e06120c1306050405090a0e030412060e030a0c0b01060201090c09020d02121f0b210c0705070308040608090102 74
    0x5119850061034400071440007102c0341c00070641c1e00c4403803800c0c40115a140c94025612200740c0314014803100354200200d4545011012080c0c03036255541d510700d00b502d440d120301001d403101509007603062192000001070707041e590000e03501c129244111640c0700c2130b5600600c019100c84030b240300d01c045c04441010385c86650703035001d071800e21083c0b440321503860380c800c43c02c56640e10a0103000d000c1071524000000b201c541c01002403050f540c05582d6000141c958180010a5880c4031250b504c10f40c0041c0018084819400c1040c8081c50003040085800032404030a039003035500114407600050808110f1000740301d44080001e004208610080011400c151500500440c41d4040c1060071500000d09000b100780c540c0584a80e02801401c108060802c01d200181e0220503015040c1480950800002c124032560309503441e16005d40c04040103030034405000c1c008110010584000d036041070100780003080c0100103100c0518444c52015a8075801c01f10040e200c03440080c19400307c4d0f0300410210302072003 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 599865143 1250 599863893 599863903
    0x1081513140a0c120c05040902030c010e0a0b13090e0604030219111f02061308030408070f0c08010203060312190c0c1701020d110903030403080d020d05010b1801020c03 74
    0x3a400c1015088900340c4a0611400c00c0c9906001501c2c0c848881004615800c29100c420403c40c49004401700b8180e070f50051109950051201135459000a0000512940038180402281600400c02d94050b920703200101d000b034000c0e10050a074100c03040c0302406401c000c0d01c17503000d40c94003031001405185410390b0001d40d69070102609421f03442070407074440100140e441c101511404002c1810702e070301d00c1410303814038442c01c681c6038180144541e10101e003c00300c1200e00c41c040b10b60440c0c902851a82d903a00d8801e210740c040c0004031540381d040e03101e0300b020955512400b00038110000000d6920f0404d00201454070002104280c1c0c1035400b0810600c0501c1a003046115442007070a01101690450416500c18045a44048030084184c03240c3e010100f4107500624171420303032901c20070400d001040e09000d54001c03200480c0d0960300801c41130000c18558000340c400524168005850030b11003d900710203450080c2e0000501020210310b152620411804281a80380207200610342c24801e1307400640d0b12 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 599866393 1250 599865143 599865181
    0x120a060f171b0a12060212040f03020601050a0b070602090303070c0b0a03050f0c0301090b1302031f091a130b0d060f0e0c0a1505040f080312150d0611160b010815 71
    0xc02104013944208034035030f0107447e52224074207030040c09440c00307041c03540201c0c0030310400310014002c1000104651802e410f2400584a64440450400c07405580e844000e5000d039804650512042c0807241c0042e410658203006007040e80005034803010001c0c3d014050700e9004d00510189226038081220400c09a0242c074111022080b020464940d0300c400308504880c1c00701c6121a1038000000c0003e000c2c0314109440e540c441d00076000b013115991340d000c00c04039407007030b40010b25403241101480d55038500340041c1c015151680b80006501448040001c94402244900311611600e80500130a420b500d48211040e140018020740102c031001d00c0090900411030203800030340130b503101c8120003a40c4940251805450715005040c44192a03454241d640c0e00501029a07014000c0e40001d02c2803100079210041020300070b01491940629039403024040c0420482000d270856041c422064200e0b01c0d4803103242c401e4010200e400407541030000c2a41001c403482404c1c40058044c00a20422000c0c035034084020b = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 599867643 1250 599866393 599866409
    0x80a11030406140739050f10030b1903031d3114040804080c120a0305030a0e01050708070f050903060408030402030a141f060b120a060f171b0a 63
    0x398081c145050030383d41c01c0380d9030600700c8902036882e2141880c5040ca80440345c0011040d2a4a5203503980003001070000032003400c80d030003401c010941c01119000b904503142c3c0c103000810111058403400460000359841d80d0095000513002c541c0c2d010710418940b2091061740e03041c4c44c80400401c011104000044e082d24010b0180031114002c81c2e2034105561100d0450fa000300c8204ad814141070402c0709150b00b00b4005c071800390107222110b4109180015020b801c654065014120742c40715500c003a541508028004074549403614200c41da840070038400e00d4854071103500d80307224500309a0401486a610400381c402401004c00001507260f03800110103900070351242c0259565504c1c9e10110b41071000c1d6480090101112011380010340d60017040c0c130000322038030040c100f42d4041170305a030209403040d5109180711804100b01c5007001200d000b041980c01400c1072004a01e5a560b540f00381c84d4180310381e00c0b500c0b100984030a81da000e100e0502124400e6175400c0da83c10a0301e500e20380098030000b81c1e4030860074 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 599868893 1250 599867643 599867647
    0x2041e0504143313060311010302030603060a0203090a020406060f0f26090f0106060906180e01050126090d090b030105010807110a0c0f031e150225080a1103040614 72
    0x100f02c800380d5a5201c07544000780c600e65012a1203404a0040d18040c001101c12070700d4104042510f5100c0d200f600c0c070a0300001e0007004152100107001c1e0096002403c0c22019002e88203070391015072158000d6800400c01d60b550f80200c248080742c0107202c10410540d070b00801c10b04a807503295100607601d04014080304014201041e46400703c00d507240124251040c2c01d154200b0700001001d41e04248500b0845000740c03200c1009616039502c80d290844940207d01c0442c02c1d05006000a521400b580303401d0030051000c000070390351010150258800d003200e003580141d205401120115500050150080c428914032509550520001070040107006040d04200280c1e07101c12a904c400401100c40e0840e008905403042c02e44400d90321181c1c010601003a190baa1102e040da428038070000c501034583e540c120201c03421260b440482c0502950001c0100c504000c072800300c2d180340d02061030955403c40d1244407070540d5285d030203802034151410f41030a506c454000340803c21038260001c0f00c101c04603088801c00381d = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 599870143 1250 599868893 599868961
    0x6021209060a2f040906060207080d02160e0414070b1902030c06060d0c0b03090c010f0815121002030903030a0516020d1206150908190c050603040602041e050414 71
    0x240243c0070b1a0321030170301d5070705008000134030a8000c107155060b12107880540b80c0d880c0b40d100d8140e80e150000c1807003072001c29020030100200142d03020700d030360418460507014400940742c1d480c01d4540300068102000c0040002201c0442c0070f405a842c140311001d90020303504002c4d00090741900d9200c02001107000782070200c080b40401400d649040040d1a01d03210b566240c0c1800900c656640000b215442d010414404007141c600e030003041610301c0340000d80c4400690b05260002c1c05490002850403240c5032192903818840106a07002461056040d8002940c81b841c06070340c0101a5940a001a90300ca104405520403440c0d021803050380f10442410031400c40c103e45901a0014925a804960340c031034641000d4400c4e65014414004940c0c02c3e20886400901c1c0568030318645d00324180040c540740c642c1c0d000700000c0c20444081c691140c01000010b00300b0795110641c4640c003c404101254110090805120320b1405124800100c100000b0000d200d04c0c020a100200c840c0c070700c06070703418550f950f4001 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 599871393 1250 599870143 599870231
    0x100f03080a0c050d0c26090103091707030302091302070804030b1909120909050709051e090415110703080606030a0e0f0d030e0610031e06021209060a 66
    0x61075aa11800301c0f141301c0d0001c44014541c500c403039400c0302c01c110007840700e0598000404a40c407250038005035081c40d19038118019402440301e0300c070840da0003079440810851318148401606c00030780039480250303a44400c00d0422003060225070030041c0e0780d8810311005000c00c81070020b030740c1520350010281801d45c980d88140e000b81c4440001403254507061086c60020010b6030140301012141c66203842607600e86138003a44040d140c0481c0c1410000c6c0a00c0820069803600e684550f606016a0048111500301d88004c104080c1007102c05032802c0340b0780f11220060491394030943c82000f1204034002d0424845940040400030041c004034071900f400f00c00b00e0800070655000d1016445c02404984450241514054a40100595070f101003403078a24a540304040105141d40b00782104640009030506550724030704030004d01c03441d50700a164030508141c0001c0051004244612400706040b03000e2900c070507058900b0500424419081e42080903005040511801039035a0000640c1c1c8101002e1742d43e000 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 599872643 1250 599871393 599871407
    0x10031e0807020a030309060815030d0e040e03040e06130e1504020f031b21070e190504110a050609090103020402030924010608061804030e0f060706050708100f03080a 73
    0x3000e5481280100f00104050f0840f81c40d00c100e0300543c50348042075844170f80b482c030a01c0c1140c180d590590012940c2d10242c51140c540d142e051381d03000340001011107004010a1442c0c005422031039580d003082c402d005944c9004c01182a0f9107200440c180035110315105902e80316802d55451003165190303907010030308650300c070b203019a480b00c4060102c45440c51207110b04144441449041d40c0610302400e58104c408103443d014107140c880031002442160b02d420faa80c40312200040c441e200e0101d113050003440310380041c01128000c5000e0010006040d4011041140f58182d6604c4103210314000c02644240d912002c804c5030450f07804850041c3c03665a20400c841c208407803401e010744500c800031380751805500e403803a1040c181d0708281c1c0d46406940d00c030030501c0343c00700e0100c05031145c0030900c074001800031b4440d0442d0b10002c8005170035407500c815104003089594101190440380c42d6220001c01018a505c844603a0340107000c601d2419405182101e4102c14010600000d002004001251440f46010306c01e = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 599873893 1250 599872643 599872657
    0x311030601170319170916050307030503070b072303060a0b03060906010c050c0a06080405010b0102070302010c0f0204060e0a02030f1f120606030b0f0f06040c200a0203030d0c020610031e08 83
    0x906081d5031070101b242079110320b42c0941034442c05d50724500200d4a41400140c550603640c3c080c006614020b03c540700c44005e62401440701c0c0c204045001c1098146040f120b410010821001d03011b5181c0c14054100044015030341c100d140b420b0170a004101c40c1e692620b6407560822420b080100035410a41041410400d104c44159003025a8600c000354072980711b200188140d001f60000c02c510f4040c000120b80b01c1d0302c54400071340060220409240460030740300000c41800d100a2000501e41d03515950080d01c0c1c6811900044119808000c0095040050b0452540b08803075494007640188a10241c103165200c60083d61250011940c1910801c02107900c000046c6400c100c04504c0c614007981484030200b411184800085091004900f007410b06000305000001d0940300c04948811a404821403000c284081c20b00c0b44c440c2403000070142e1401d0006141e060090315000c210b810641030003170700e0301201074443c9104004503401040401c11388450186070085143c910003101d4000d0070b2603d0a806802 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 599875143 1250 599873893 599873927
    0xa023007120809060f0711011b020a022103040302091e04060e010507020a0302100f06170c0a0602070e0613021905190905090117030c030f071502090a090f02130311030601170319 78
    0x100c09c201e4010740010b01014410b200711000c42a410910b0542c00100c0c1144000d800c05900a00080c0010b260000e880c1c0e512541d030141900c400540207a04011404054900350358081d540c1e141821180d40a0003443d07880312040c001040c0807000703039400a5580307000b483d814940c40c7d0384030f6004048a00303503005a4001d080100c1d603140c4c40503e00d00b0032601d070308190303d14500c19499408009002800461440d08469003c144244076507960418480c00e9004203000c0703035915900304000c4c42c06009580c4034110403107450f03651584030030b03400c8098103554030b8284515060040d024401c002c5940d9460030796054549110300842080180000c4520f5409480d20061040c000498030400742040e040c0030b0501c480c02080500c03803002c000741240b012071054000c040e800c010140c4044c04501440d4000c1008441c88803c01460100c041c1e03150328950320150400c64941c031840c8000c0d0312910b030400c540d41c05006040c41c4501082d0080b01c0441e6640304500f0129030080c000d441050003e409020040721440b455 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 599876393 1250 599875143 599875181
    0x10170a0210120e1c210b01090306020a030b1306080a060209010c0c081c050705030706150911030618061c170403030302031b0a023007120809060f071101 67
    0x390f450613115040320406450b00c00c0310024040f1800e10606140702481e484008036030301103034603500c03030006402c603582c0407418403848030710001c00a0500c1c4000c00e407144031a540010346038106410050007100c5405180d844030304000040c88175200211300c0e01446030b0710600040e5501d44540060755444410000035084000c04800000c0c0c4031030200340d11003403d40b080c120052242d10f0303e20998090159010107425a8020b100920029080341d00c0210320404404d41000702c80d664000103000d0361150a94044845400300074002d42d41044190780c40c5250445010442e1440d107500429403003c4403030b1403c1050f114894215041c0110b900c420b01d4405500095999642d41f03070b040141c041c0d4070503904030051501c42000c5030403052401d015280c01c3d507100e50280c28034400d000c449003c1301401801050ba244403902c510b10041c00b083c0000e040007482055200310341e003006d41c13001d0003984000348050b1040d0082800c00040e400b14420050b4441c000d41400707881d141100300c0b99401040582d00082c0c0c6c88450b = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 599877643 1250 599876393 599876411
    0xe0d051e03180d0212030112050f01020c0a0201031a0d0803190507030203180a030906050c0f031605060a110d02030c21060f040e060c0f0706050f10170a021012 70
    0x84488601c0503003920001c0f504010070114049a03501e000c00c642c551031940500c01400300b4a1400035102c690780c010000c5444000c600e10510f82280d1118403290041d500030741d5080210750701401100390361340085500000510300c0c44082080000c090f8001021404c00000098502c000303651030024000401c07508010f1440c24182c040c1c0298001d0b02e0700c40807800180c00c041c40c1004005440300740c180e07040d0344400100d0300c0c05000b0b80303654000421f003071014000d54025285405081001d07100361b1030940540c40c0c8002841c24a00e081120180c02000824107050600284001c010211000401125401a9290b071000d24000c800c0c012510803c07104101c40381c0c202c1d079a15562020074050380f81181e034101d00044071800c010480b80d034001c004601d5000a030004207000072001c054602d1468903a50355181c0b107016030780c100c00c41d142111303090132000301c040920801032a42c014640141400080300140340303440140c03007680c540b41148021b103c1c00002d80360f260094840e52148440b032980420030302101507 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 599878893 1250 599877643 599877661
    0x61806130c2a0606081902060c1f090606170d05031e1504321506030a0c020601090e06040b060a091107021f0804030f022406130e0d051e03 61
    0xd00610190748440c1044004100300c20041030500c10451110720003000240f080c7c0c00c2c0090764000c0c41d040b1400d4003031012a0f40422421000f030400703c44c0c2140000403100c58600c0e009080703c030982c110181c1c8142e0010355440c8400006040c40b262619030610517120740d41c5000311410303110076114080200c4121800e01203d03120212140c1740074031080304d00b400140d40803040c0c4d40b20071075030300c01c200355444601c0003441e00c2c44207100440343c00c104c0051010359440900ea000c82c1c603944c000d403440c2040700d0350354031140301c0b0a034148040d50240243e401c051003c03405400c1119501d0101401c003420b030b49000300c041401651001059001004051804e024480200d8401801c070f403c00c9000b03030700413803800903041d10440780c1c1c040c210034001c01600c1e5003c05481d251021141031403110f900100350b200e150b1425034030b401800c0b80e80c08680d030550328a51f018a4090140720106c42e5000700135000c1c50400000340e25141c0089285031001d800d42c903015468840c002c40480b454800c48240110b50900041400040301c = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 599880143 1250 599878893 599878967
    0x307081915060e0703152c0c0a0c060506030708010c050414030a0c03060506010207080706050a08010e0f0f0a150e0618040302030d0e0a0206040605070c0b0f04090c02150f061806130c 80
    0x14002141c4086c0e0b2062207402091041c00600c0000ae460001d10100095a83e846644c1000c401350071150240e0300c4400c1d25084803008030450b804610081020810f40e200d140c1e41c1d402c43c18080d000380c001014950381e0b0059000c40381c0030080c10705480720300042c0035074401c1000d5001018150100ca0806903100005130090340220324200004030002d0002c100205821035050140b82171080002d25a9507240036101500c0c00540150101a1a40380150000c80501c640001070a030800d030300c103924249a010040d10f65129000c107c48024210100804643c010040e11000f00780d54030302054405440380c409051442c0b00c40025404100807a001c41d81c00d40c000003801c88588103202c3e0503500382c4c44a8041c000c5001c1d0700c8101422010801050140341d80178ec00c025280f8507640112412002550384074489440c048071501d281401c80010407440e442c241c6203101e400300b0180c00c099030904014020922914418010040c84c81c2c48035120040c0034810044102c86c09546090b1a052100c2c91804000b08 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 599881393 1250 599880143 599880209
    0xf0c020a0f080d0306120201050703020307080c07090f0e0a0210170c0d060b042304020c0a030309110a0602190804030b0c0d06050f0f010309020307081915060e070315 73
    0x520814a030f83c60300a000340b00e0201a603141516414998035107900440b0340f5444940201c086000070f0080600050011021300702c0c4859010180400c18107001e004400c40300f4043e48100c42c40c4c10b0402e9400318500201d440c0107520b805a41d205840c000004081e55a48040e8021541c11a00c020400c10500c8085001c1d00400703140000601000b983ca10301030390700e80100d010b61310a4500240b4100015151202d0100300c840014002500340741260758000d0400381c01007010740100f903c42c401c0e1020003100d04194a007000c000c5503656440760400300000d6607000c01c01110810400940c143c03400380120082030b10011a400908586070b880c101d0480000394000405e0f114100d800e160010030a8070741006450740c1c004010300005603800d010303401100038002c9000140e0f0103000305400412070000502c6001c0906051400d490101c502603d015101c0d207441040f80d1040d14a41302081c0180c0031a014200c0c0c01040a02e4041111582c000410500304081e50215400c151062440003103600354002040b01 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 599882643 1250 599881393 599881409
    0x3041d01030203010e030c2802040e0309130513080d110403030f021009031403061f170c0c06070809100c09090516080105040e07030c031a090109050d0f0c020a0f 71
    0xf0032200710f85c0c0941d41d000e079200700441900206111110b040d43c0311200441d02d0350320a18880010400e4000c20100c0342c1c032428529081c0c1000508d072a85082c80b5000a41e0341110a074200308500c0c02c44001800a20565001400c1710790000d80f0711480d03401071304800000c000000d401a56282d4031318020780603454066182015000722440070050110b1072040003282a09038a80c2020403100a614200d01e40c0024015503110031030030500c500c0c0407011640c0341c60469994890582c4108000348030740d01c00f00005c0c18013214000410040c503141030302040d000e070488454100340a50741c481e8004035003002140e80c13503c401c01c1d00d0005009035403a032001e64881122444e1b50104400e8803003040d9544481024651480803032174800041050f41013503070001ca5403103000d4040d14101a100c0d40c90170790444c00c07580140c41c1c00e00321040d4a4002c00340044243e8218000d50001c1142c841541d40c1c150b02c4202c0f4107201d01c103114a0104414485001d5810a201282e000340030514013030311000e003100c48900754054030310 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 599883893 1250 599882643 599882651
    0x9010509040f05010f0518061e06070c0b0310080109050c0108250509040f02070b0c090102030408030c0c0307240c02150a030f0506040b090609070516150c090605070f030203041d0103020301 83
    0x520407c00e290350298030040d00540141c4a00c1d40454405404091840d400200400c412000701d2040096180178211001209036a410701e11140c0072813a0082e005021a6450a2140c10000e4000602003110f02c0080c2841a01c40c0c0d45d1403425445a000034000d60540981c8513070303030b90816911400a084600f002c5404201c1c90740400c006404078010031000421014907035021611120955015001b000360502c1224074041d1a505454119049a9120505d40d0301c02c140300010340c038042c4140406001c0c0640106250000c0c00d004440002d4011500000d009003420a0301c01e5490712100702c0ea400b04605105ca56402030303c50700400030404900502c00c42441c040105140c4c0c43d00703000c0c00405690081240e5880d0b00d5080c10060070181c080c000c4420701008000003403100d0b80c00700594100d40d004202010087c4500c0c21940103554500b40c00b0303010480501400e01c40d240c0c200782564070b2903400c180b1420242c070952505a1030751003a42c0143c1c0301441c0d144900c5e88810304018986050382e09c00d0700280 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 599885143 1250 599883893 599883919
    0x4020907030e0a020108090c100207030506010902131502030702120d1202090a0303050904090506092b0801090b04090b0a15090c1b050c06120406180809010509040f05010f05 76
    0xc040382c074288001da14940011076902e0166103c0c040d071540040003202581c805910780d03400541420180b900740c8015030402ca008109212041c0003507401441000001e40c50482d00294000e512200c9014035090003081c284504100c80c0300f08242c0e4280391b4003401c202841041c9014035560f0780800c052610000b40c41e287c08003850700d40741c002c0e144501401340c16180c0e02410b560342543c880e00110040d40e00140e40300801c801080040140901030080f000240c04400c1c0004448024440c00e1110260300c00c0708c4080e04840d0701c0e0320120382811922010f01c0060182002000140607003401080602101511001d10091100c07641c4006500c81c603482c040c1c188241d6400d05042558090704001d03001c00c104800003c20707600c040c4981540f1502c0b0700c041d24030f0011420005203541d044a18150b49881134401000b04021051094000c101701c001440d00b0003440c181d40300c01e56449642c04542c100040400d186005803595084074020385ea80d00010310203503071035810320480000d86108051242c40010848 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 599886393 1250 599885143 599885147
    0xc03050702040f1d1b04021b01060e0402030d0206061e031518010605030a0b01030b0910090803060906010c0b07030c020f1f0c180918060c11011523010302071203020304020907 77
    0x1076188541071845c4440c3c001390f20082200a401200c11590032940f03510796401448000e00c03510000e0141c000c00c3c28103904141c014540380031140c070070b40810341d4842028800c59548800f600c0e40303217480401d03040c50301003c01c00100341801d0462540c411131140c0641881840e40d107414284a1000c460320081102e10759540825944198442c0c1c00340201c0018001800411078240c603103507001c40900200e40110001c00d2000040380c409441c00e40c1c2c440004800e0040b589441088a90026003d2030400d0524078552221043d020020344401c05042c1d43d54100444140240710128681400030291580044038418018110502d500c4203044503191a10380301865000d1004001200310020741d000da0181402c08181c0282a58800807045d2140e0a0450000607024054500d1450040d564500b02c803094003000c5003907869100401198441d078200902a5201c404d2141c400d10465a81c12074000c05100c0040c0c00901c14a0800360110018081030003125070540c0085020764400e903030300c511550f584441 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 599887643 1250 599886393 599886403
    0x510020312060d05011118090109020406080a092a090609060e04061512030c0b15101206031b030c0e06060a3b0103051807060c03050702040f1d 63
    0x381d012101400480d80074140381d40301000892061000283c00202c0442201c01d6030010b803111401c08080400f001480e0034111700740c60062000101c154109410724002604004000308400c1860356140c00c40c4052000c041003100c59108281468599402c002101d944040e2207130051418481c2043d000180550192003004101d8100300340890844e20303103582c2c0b5409010340d0714003140320456000000c1140f2185e00280b0110910984400c0300102aa1400a5020300010400c0a1042c0e21a03905400c0c5d441e2801101558401483c28540c00480f200c60200200f8042d0805070407503450b05000c84041c14400051400d40e40140d80c0b0000c0583c3e0346281101c50a030440d04560000d005005030075041b40280d40702c061940f008598a45030f0103800b48001890501500040b22817080426076003540d5800d40304071500305014910503030b0340540309584c0039a503000c03500c202030070021080c003010203161042069508540d8002c3c1709200602060103514054460384015007011803200138012414200058 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 599888893 1250 599887643 599887657
    0x609070303090308030a0f02121801200d021605150f07021e0f060910060806060f09070207080a080d0506100c06050a0f091506120b010b0f07050f0705100203 69
    0x6a48565581107654400060700007405001016403a46841c66030314020303002919a0b02701a10380c138800c0d4a003451040e4580711110fa159015a40b503c0c98541c4500d500e000704001c42405043c00d10380d28092100c00200900c9005250100044640c0da86130800101281e000b02d80720b5120030901141d1260f1084062120f010f6507d403015038401070100c0240441194030000f14080d880c00d50b1507840c2c224580d641424022038200040d070300030328100040b10400e80b00e20405805180700a00c414580440494400f03d9000002c6219034411070026108510030040700e4083d007498016601407410516240403540c02c241c1d00c60301128140800038045040204000c4070740112961445d601240c41e441d0000142005003641385e10341c0c5c03139803d51148102071307004e103a400a1041e43c040324145050341440e000c9582a8100348401c44c0a0050800450f000c080381c28195071440c1103040d52541a1055a140c502c83c10000803c6401000d100e40000741000c2130620854901f540d4400d114500010100c0c0c032403141c00 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 599890143 1250 599888893 599888897
    0x30c0d110d0206040f0c03021021020f07021203090a0303030f052809060e0d050408160f060503070c021e0103050603190f0f0204050906011503020403080a1d100309050609070303 78
    0x40c0050081104d40791080d5505011b03104601845440303802081c078500d401d2144501042611090a43c59200d0b48402c0c5140e4611040c11800d010100c2c403442440d2040440c060301c83e44100d00e4954072694180100d881d03040000308034451450740c030715000e000380c40003126000c0c600740340800160090103450000c401440078200c098240101d104004c20082075101001d441465076450001951041000525001d080945034280ca452405800f94a4213441c2c3c101c0c80880c00c401407080000001440342142911201d040c0309451b652103030811109094030203c0658840c401150041c640c80304810110031809080e030303091290f56078800c01d05965440d8115400c04594075840e40f0300224581d0808810010f1141d0064000a00c45400040589200343c80c1c04546402c03003c01042036400c482c40104900440d418203600b81450342e1207100940c000d04c441201486111f0b9240c280c01100c1c4c4109801055001380f4104035685c2047c0c00400511100c2421241c03481030002003400403100107000401c481d855 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 599891393 1250 599890143 599890153
    0x50c06040b04120c030206042607080d3b0916080604020d020706050a0507020d0801030b01151b05010c02070f0e010b07081902011a0402120711030c030c0d110d02 71
    0x103d80f549050807481241510305034842d038804001130781d0b0403005000503d90702c400c500350b0306031108140580b1140740d900c4802c43c1e40680b204000d203600103e05a250500d442c00e051000d00307402d0307030401d1401d030150640d000850302c69000c459000599188503040f501c1c060b48d1401d100d81c0d03049101c404078072155030090046029000040d0440c03800b1303002801c85140442016040165642d100425520142d0352010030315114410411060f6040029421880c158035102080e5451a01c0354402464180912009541d8100418401a0040051440c80880c0304404880c0f04c5040c04c1c194000c140f00d0b4014030050185480000e0b01000b14a0f0030ba054491090014515910307000c890095a440071000302c0d00444280040f00a850740700070000400240740d00007103440503000c1130100023580c048850501ca18818030403554846c10107070b00190b000e505802c1104000e141d9405d06459030140303110103c418403001032101c01111000c1440880c003210342d2900c001880c0f42032100707601c50741a0030b84480143c0c08 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 599892643 1250 599891393 599891399
    0x4030f080c120a0b180c1206150d05060109170d0908280203070b07080304051e060426070302030903100204030b040b04030311070303020a0e030610050d0206040819050c06040b04 78
    0x35448006100c000401000c5512011000c4800d6010100c4140c2c0708034402003540d150004039100092343c000350031079130040c1540d10800e1192040c041d05100b0381c444c943d0741c800103c1c264014007048002c0e1031030b02c001e40459040c03403202c40c0d610213407245424000744000500081c01d20700000d19110700c81c5c1c1284050041d40329922005520840210283ea2502c01c00301d000480700c0c40d83d0000c0680380d015403041ca07502c1c80c041c18290302c2c29044400d00c41d6502140404003100000225040c1c0c0c10651281200c2c1210b01c608040d41200e02602020303a1941c500007507170000701a000802442040800d0702541d03010700b5501c0c0c1001c224000c910001d41b2401c0c910700080d000a90107c64940d10a00c80e050004810040a203080d02940090404030046a400150300c01c031301d074003c490070203188400c130010308061030804520345040986108140c001c44041c40c06d44210365070703102030f200940004400c0b10280d4034031068800d42c10008440649403401030030344020103414848129403d660440c40d00340d1829103 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 599893893 1250 599892643 599892661
    0x20709051e04050c0901150f050901050301051201060302091602060c040305070e0712020a17060a0305120d0b0405100e0115080105090702100e03031b07050c12030c0604030f080c12 79
    0x60700800482e40c0303014203c081c640a544580c0f11134081c2003044140c10000500745009466140c0803a1040240b203414405c0400036030b48002180d05564040d2181078051017841d8001d80503100d160002584940c0306c0e000c0000c0d04a51600a03a12140680c1c03c6413419254004181c01a00c500c0c00040d020b41c001c09414019030540f5464103402420070302d0180c1314550310b030100e0b1040740c01401b1400700041846408407045040000e81540000c2c08072803a498292442d138a9540c1d410300740148038001074002c6203d03808108203600c440c08040c0e0190013845540b03000b045c011520365050058211050b4010004210495103401d01c0d520f40c02191106607060b400d020821926240c010441e104501c00e040380c84010150b070f030203084410340f000c00080d92681040e05002d980b0808448469040e07420620036900843c2c40010541144d5000780c80d14040c9260280009041d8401c41c0d2a0410611804041c0000c056100020070051142c60343c41c80d55a4680c403d080020340b0417140364000800202001c00d403454 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 599895143 1250 599893893 599893951
    0xc0c1915020901090e0703060612050603100507120504110a0e092e091a06010509130c03020c070b120f0f07110f0f01150602010213090203150d0609020102070905 71
    0x2607050400000c81c90382e50880e40a80e503406c03181c0d8800680c550108112240e08030345c21a1401c0350030300c400c1c40130340b6018020039682c09008003c00700e902d0311030000c03800d042c1c0102c490214400a0382020f001e186441e00780b000004080303412036401801c101400003484800ca00b6640d0150710150054240e5071076008007801860b0280b101c40886501e080e21481105456108280040d441001501e00030440422078124206001341068188601000040e0700c2e1b83d40e20b907810394803c546190018480080d40001c5009000c4e04a072440948209503012850740203c40141a0340c000203e0542c01b02c1e80c8030411411076050960f6940c5064515a01060809009440ca415001d4854049074010b200a00e0b031341d894101c6001c0558038070303590744d5110344102c08804c11300006008035000951034160914062003411a4034032072001c00c154080701045c41c601084900d04411a8000c056800700308031400c03c03000a000d0500100d0241c0316030b50000a0fa515903015051144401140d03078070b590f4030072403c1400c1c91 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 599896393 1250 599895143 599895157
    0x610080c090f0904050c10140d0f0906020c0a0c0501091508060117240d0b010e1005040204030303050a1a010e100e040603110a0609080a11010c0b0c0c191502 69
    0x401d00400b00b4129222603042c20b11560084004202003c41d01050040642146144d14100414003144a94240c8031600f210b0401040200c0052076000c4900140c004099461000f04650700005824003550030000d00c5605050161500000959490006480780040b034422041c40d22000d070060108240a85203036980400181000c80345c81c522902d44001640c82164146a500130b00c18220010b68185800d80705000c4068031000d0446c2e40c241c9079140c550300140b09000c1b062000c0b00018440101908840f001484003501c15034036141c4901e8043c0c082d00d400c5035040b00051034180303485070940c442e00304401034040603110800b41002590901c0600c4848040702028000c0000800c906500c9c0d602c039650095016a030380815807411801000958856503100c0f108100d15007009200451000c241301c502568440c002c68101a03900f001652200540e000107130940c603d030010000c0603155900284035425a6005981c0708007542045000954004440a0615544c65410100541c4e40385d00500c28 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 599897643 1250 599896393 599896399
    0xa120309020904060609060e0f041202030c060f060f040912030b0f150403061d190c081911010c320a06360b04030909230610080c09 58
    0x11290750081210600c1c1640c003183c400341d54a8080241240a203d000017520061515404a0034503806401040c40b014002804200c4042c07803500301240200704031050805800c040c1c0b01f0500d041c40360b40d100f03c4800c903140303401844160301082462429100d1654180d0b4840441c502c1004500c2c1c0460003040180c0490390442e41d4102c90710969078407a044024001188a46107541e1410f43c03800c6400d691030f900310b4184441046200c612000004102800981c05003c1400140d01c45400d1841c403c83c070310381c450401801040c420800509040701d0001481e8094901401040403080044804894000c005041001040305003140d104c488076040c1940c8482c0544070241c5100400303424102001d004048a040d603607600c001c0c940e502d0114082d11950f4187d03940b51403c100c10958150540682031000b000f442c0040d000804042c000d85a20026000c0903c2c1040409881010414100c000902845140340d44200203069454014408906120700e551825060744518200e912550404242241c0c = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 599898893 1250 599897643 599897651
    0xa08071e0e0a0f0305030c01110324060d06082b120e01060305150a0e0c094201091403123103060e06010608070c060b1f0912050a1203 59
    0x994000f45040c40300103580140c014660f01d16403405101e0071561031240c0c00604040610030440383c0c8010010a132050055440c40c1183c00700800d000510134446d4040c6000e42518041d40411943d0700090f0f04040b034003001001d860b0307900110b000550001a03600000002030260034262076411415000115801d50708000401c5060316a519281008480140440031080300c1c0c0401c46200b5035409000348010a04c1c024140c81100400400e0384100020014070313a0011700c501610752041600c1c2a011700c01e240c020090a20a070205050f90f00000070350a1381e0009031400000304106040b03024a080811004000f40400e03c02541058003d8001d0510019441c84c5e401d030080000f078800c13400101d405003458100003ca1306602d0160102e0b544e81d0381d001d40a500c03e4005000300f5810110350b54000486040c00700014401d482d0010292812104568002e4040810701d0004040c404a010004007070303890f4a0702464030340354068800c08000d0700c040c090781c1c08a525000440c80681260501d1000d03450041 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 599900143 1250 599898893 599898899
    0x9050703050a2a03080a0e010c0c0e0a1a03060414031e04060f17010e0901060801110a0207170304030f14060702160f05010806040b03210a08071e0e0a 66
    0x900786001c0403410748440d2545921a01121240a60800c600456903000c1900c103013140c460040500030f404002040c44002e080320305c1903030701407410a40401d40c003c1c1c010540c50388944050815401c1034a14440300c0b401c04070071400b012a01d960842c84030307801800811403a51640c6501c010b00c004000d0a8003503010030001030310b10702c480388203034400c2512041d04580c0d12854880010102000341131854100900c2615204404415004440c1141d49008080c0201d40307910318114010300041d4031441c0c03258a41480c0c00d4042c1c226101404442041c0d800b07640c5055a00d8402020303014080202c41c031581c008000910001d0b666540090f14070740203880000112030a990100c0c5019416100d0802580c000441e001142d40711070805009002c00000003601c8a28200018002002c0504020302c074503101d1107a40040e03101040700c40c1281141e0240b00b000c0e1000500107031203d0b03100302e1300c0e000018080000941c91500885100941d4502c2410030749806805140c00c5502402c426899540f09040500c00 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 599901393 1250 599900143 599900153
    0x3190e030d080103030806150307030c0e0a0306091110080f270c0306010602011e1d1e0d03090215070302010b061306080f04030e010503070201110d0501052d0409050703 74
    0x50510003040ba103410340c265041d82005003a40d600140340500c14000d9114280a801c82a4240c036000385460402055000c5455826102e0b60a20b800260300180541000018030115400001c83e25000d005201040c103102820301c1001c40c00c0d50035800101d2550008036030300000c2c0b50322065200304428643c2900b030349804030515294564480d080c01c1980810f01d1818546410311100b0700400d200e00003082075a10501d900e003080b08a007444106c030181e0b10151200d0f5221741c6260945014454400d070b03854007042d2000c00340c810b120513818481d00d101300185024114028407490021030b40041c014200000d50507040304141c0e010082c00c80440d521120a184035880b14000b4004007410201103445e05410711000901d003450042c000b50705443d481c0d0501000c00e8101c02403041e802400c1c03030030960340e0341c0301c140607800340503a024400301002c80050100d50740c0d00d5561046050700c40803500d10302001c503000c00c000c14021a09180800c1107000042d02d07049880c280c1d004118091040342a00c3c1066981e40364 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 599902643 1250 599901393 599901403
    0x10b0304060e152d0619030618030f05120a0b06120115180f0506030c12010609140306280b1c060507020a050709020f0408030c1c03060803190e03 64
    0xc918402c3c1c3c140f1050044a051307a40c00b900090424540c69070031154440070100c07002101404d003074020f051404407488a07408854258002c0c6030403040030711450f1354003a40d50050b1a8a020140c00080c045c0d020801c2c1c1030b21038030880c0c1c11201020103a6102e511881e5000c401000080d0f880b82d40001c040206035403280b21028807030300811001d0005801d100302d0f460007030894900650300814000881100b03020f01d85000726581e05603030082d10040c0d120355800c0f0700c0801078821100030003010000c180001880550121494096504400000c1d100d40c05800c14103503240f10649680d80d0060340050b10344d01107039203400c00c641c1c2c40c801448007151040300c0d01d010410741010a440750810409643d291001c0c403010b03004543d00903841303100400310740e00302d621000d4441c096809000d80680d00040c001c4003d040c960203880140c4020420b50346d540324400310046d640c50205044000076454044181800d900920540e0121107500024600d440c0000c2e03840210007035100b9000003805000d81000e100c0e41c4040007 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 599903893 1250 599902643 599902663
    0x4080c010318120e01030e07030f06110c0a0b0618220c181a0109050306150f06030a02070b0a020412030315170304030302070801110a0c0201090503010e2107050303010b0304060e 78
    0x3d440304d60708801c02c0014151100b46410000c0c40d4800d01c801c100041d800216046202c1e0014000600c001041040803410302ca04032440b00030b4411881214280306902d400f1a01401c01100d0804219401007101c041c0c1e0402200d041c0d591440b0540d90114046c0101e4180c210715105a001102081c3c45030008154a40028200140c0326658034408006240302030041d18038075001d08000124900e48800280e80d010002c0c41c410104500c6d00c07403008942c64240000340e644d80014042074130384c40c016034200000e4100400965030146e0301408104122003d00c00c4505a440e2089418508070341500e00f17a000c0c203d010072299060f260394000040304070007070804c0c008685071100519a9103143d4200240703040700301d800c00c00d40c50f458110b114001500c00c5d8101ca07072212240c24500c4d0280510b00040e035940102d039104c0780c0c05509111604d40c070000301140c0b9a441001a1141581960604c00da005071400340c0350006100390300410042c0a41018100a0f650040c4503540206004030310490481c01c0a59043c = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 599905143 1250 599903893 599903897
    0x140a03020a030b09012709151a0409050c120f16061d010504030609140f100e160e1914040c050f0a180b0d0b0105090c04080c01031812 59
    0x200320303811036982c10701800740c0001d0b080314030314019414a6113a8403034040860a15002c00c0718108824030321081500800c0c0400c0e00030340c0d11035070fa003540507060f009007da40c1c0c800c030703640004104028541d00c0c1c03900c02d0105098022008004204000c802d01c54400f5482e0441001c6104074000c13507000d400108020071008840640c0e0703070081c61034000d01a201400300c5000a00a00030744001d400c0310b036441130a59044a401140100b0188503e08144d080790228903000902802507904001100000040240812202d80010004640190034207502c50f0703120700094039210902c00040010b01071404619400a8820301d010740d81140c00b030b100e8001c0311601d580d076002000100c000c100500c000203418000601c07007030f40d0000b425480314001903802200c2e8001d9460600c001c515030030501c01540d01c41c1158400103000d003600c4100c00e0a2046244c4c00900c00c040c80b9401510004070001244020750b011078420000515140f190302006501400038a2101302005120100d06004125080c4025105070340d15 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 599906393 1250 599905143 599905147
    0x2160b1905071416080c0d2f0606121501031a0c03190903030209040e0a020f060c0d0309030c1a0603010b06040515090402070614011706010608070f140a0302 69
    0xa80c000d08141e5800812001c248811407620f82024500d0404880e410303038021040314444910740c5031540d007a000c0c0640b55a1079114051444280e242c00c0000040600000c0d800707030740d814000c1007901e2001130349070340c42c1f14031500800c000c14030380c0c2010a45a080c2249140903903100000ca840c0349207940d80300741d2040e913044101090002c1c2541921601d150010800301486107145444500c03806040c5034100080700d400c0d174131426181418407a60690b520403200404c2400003030014034010741d5440a03d401a4800ca0200350490b40710b18241c1c0071038819250820107480f480500282c01c0e07004040041c0c050303080c08a01141500000c1404c0c0071a01d090009605e82115401d2034070605084640070101a80644000c000a10190b030301e40a611403190080f44070b0715038401204020901030300400700010400c60a054131440351109000ca80c0d41a1840b21248110101c006204607544140070f1041c1404142480c01048282c3e1080c81d108800c60f100d410802c40502e001c19902c4002c4d8410204c04000940c0 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 599907643 1250 599906393 599906431
    0xd020f0d09150b1905060703021c0e0906030102160803090703050a061a0a0308040b130f060302030402010f03020909070e0607020a0602010c270e06150408010501060908010c021002160b 81
    0x759100b180c1c0c0048044d1409104044008001200b0071103d0040c94412080410904100b40c42003010300142c400f2034a0180c403403080904003810706c0c0014420544034040304400280b103410305200380c500c85190300b91110401a003a45442140b070348048c11545940c081c5038801300105004000b81185140b081c132002450320004e480325805440e081c2c0d2550322943c000318040022451a505440a440000c80031556400c001507565181418590010300c8082c04203000041d860f0300b650145200d14000c2c0c0301c1141c50920181c0c03c8003244940c60310b45a00181c03000c0401c0550340b0443c40d403000076a0140c44c6920b8452907400040d0b02d0711036680080d006030345400001b42c0d05540b200b096040720b0800708a5880c4d01204c0256180034040d140541c070241540300000850596500c1601100c48103411422a6200c0d1103007040350190009000e00700109e11041000a5103440512a40b000c0c0003840d4041d0204020040003240a50b00c00c0307041c0e007080007001c104080070682c0401e8040c00380b04200d05001804803 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 599908893 1250 599907643 599907683
    0x1a01030204271b0e0108010e010b030303191a1906030b030c090609070e0a090c18080303132406091409060117030712120605060405060d020f0d09 64
    0x850b0b40c880700c000008100300c0110301203901c0181455010440c90481c0800300303c410350311003c0b40d100810003462080005158101903005440e01c50620340280220911801071640e01c0c402a15800000340780d411000000c02d1403035210030800f0303c40410f00250321010b2000100e002c03030004040c040c5581030707c07410040590948201c190203001600034081411020000450071030340103000354060024500000d907050721901031820040d200900780403000342c0b9032003c20024048404800042010304882c0540031190700c10500403141e24174004d5107036586200308680e00c444041000c41e00300003010b4541031640700c80003180c194000c00c120002410351405400209880c0b1518004e02514160030070711000243c003081c1c15065507168519002a11000180d0502c2c0d84603640c03000e0445584040c0340701c400707540850f5617981c40c07094400500255031034000b082414807852240781c0e4000c0c0d04014075060340a603034000d481c0d0100b000200382c2c204048441c4035825240461011036417014181113400600d0 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 599910143 1250 599908893 599908901
    0x16270906020c0f12040b030907030203010519050f0c040620031c110f03070f0c05031902060601030e0303060f040207060e01020913090b0f041e030806030106061103090f010c1a01030204 81
    0x100f0280f0003024050203822001005100300d000d500680b41c1d00000040c00080d00f00041802035034050300810592074080c0c44d150108000380780c04407007207041801040c2d00400b0f01c10b40601a20710002d0b9039147c00d2410000352045500e420741c803001c0105041026115032014000303044101340100985403c0524001800115402c030400a910143c0c1405510120b4641030140c0c1e60001c114248002d020828400c11b680c0d01e128818020030310b100c00034400b0036580c40d0118080543c812602200c001c0d49450703005405403803d42124154551060000620354649200707000d80104010388014a8045d040e140d4009950003940316001c6607400068507441400d12024001082d2020141000504001c3d6514171200201510040c0c11150240104050011580343e03104110101c001240f14040c191034080c1141a048884902c0780d440c0503400100d050140c44a02c82c440e040801843c80c10001d003080240f52020b00c01d00d14100800c0480c080000791041105484000400f4006400c0798910700c1000306072 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 599911393 1250 599910143 599910163
    0x3060b0309100b01090b0d0b01080108031801030c05120a06080601051009181b17100e01050d0317010e0108010c050a020c010c080d091b050316270906020c 68
    0x9460100104108250302140301056a0302c140808100340c0d28910040300d140910b40c110002c141d030000b80503640700209500406403c402030721403c0c0380d030781c1c0e40c1d40150302c80c01095252045020840305141040d8407940c407a0324040c12030b041c04d904000c081021704110410031030311004a1665000c0901514108100650050600b26100e030a407030078040008158074111301c01d04d0046039410f4240e030181c481c2904190700011015243e0003096280360001003800444121040c400c2c0280c00c003180b843c610454921083c2c504420a03010240d10789000e00c000c424210b601542041604002d406d100c0060525041c000d001e511403030603031541040380c403600316150030400b0020720000300900003210745c02140c0e403050803400b4202118803410f2410440007074890b0205990065242040c0719003000350340b034040a04001030024140b84140c46009060307480448015500c04011411020841401581064800c0510141c00010703096080b46c455015035031019000c4505503004110501c6403102040480c1e10 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 599912643 1250 599911393 599911409
    0xf120f0d080618010b07140c151206010e1e191e06030c0e090603150709260a08070303090b0c070506070201050601080a090f022713031e020a02030d08070306 69
    0x1a5450581001324620910900074280480303900c0720300b00344000780030340c04440c000a4001c1ca8611141e09e0568136961110704611060b603081400708107554400e501103200d8880c0a000200e40000c0d1242402c2552800290564810002a01d0444030190710315810028404aa20400708500032034040e03004044680142081510b8409000300d615440b142c2c042c4060029101c0c4c0146440703060109040c01d40009005810307800142c2401030241d4068007040803074640007030300c0c1414025015400e040d210036952006050340300c600b1150105007414002c00c5803500c00d041c001031941711599a503035461000c031021200c051010502d11305201e010701840d580800c6510080000e0300c5d0010010704603090150601d4082e0b41c0e91b040d000b007000842d05042c01c0707203900145075030301c401110711062201d040107520000100403800c0c0407441d0811680541520310f581910365401d07040b000c0c0100c0080003100e03030171401148640d8a052015071001e0080022144060b698401540f030b0207640a800d841140d0f00c1004 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 599913893 1250 599912643 599912689
    0x5070f06031505042720010207050f0105030c12010807031e0203060f060105070501021210361e1d0d0203030c0a0504050a0b180904020f120f0d0806 65
    0x30394210070380040010b641084400140300c0e540c00c140c0c240701c40605c000c8450055440620300f01801401e0142d01c401c0b2182c0b10f202c0d40078007941001240c8072125841800d40241070341c0e000c1c02856000380e01441c0d0107030b2050010380c2042e0004101c1802040c081e40100c90036048200d00344107000700160203100f00700c60022409468096035001c0b0340e44500c000c000315580240d4002250301c50384107004031000260400c0c000d54a40500d50407460741040300350f4524038250104400040c115000001d49131406100c02c0112130303420780c0084000c070420a41d801c014085550740b100e404002011320509044205400e100042402408070b1010403012810b800da81d5590203000b8a0b46140d900208803580b240c12903299036100c02c6440800d0701e0b00c0c06280c010707680c001c00c070341d03000320f01c025034000908aa141002c5401908015050610030103040542e030194010240100c50500ca00381000c40f4104025204221030b100b0155420150406020304800e02c005400328050244a14110750410103030009486404 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 599915143 1250 599913893 599913911
    0x1a0c070f0807090209060703030c1206090b0a120302031804060b0c2505030c042c0607122714010c1101150b070f0f1a09160807170106030c0305070f0603 67
    0x1071020701400000904054a9000040d0010301ca1448000788081007900cc0c000f2903190300349a4060118840e4090084249200000c1ca0840680140e050036030035401442c944645240b08508800300c080d140c50304951904c600090115501c40100010701c00200a840181e4490600701741a1200500c010040b140000c01403115580104003c590202c0c11140011024011114481c08200c141c1b2045285d070300b546402c00444c0400f2880901c940d11030b44d161054040e03044100c40440c2d500c54002d518194002c0c070344040f81c0401c060318196050003580342e00626184890030b5400e596103408030100054201c0440944880c00b4061a15624400001551070358240501e000713a43c0980c41001d4416950300008609121070b806989031300a0304100c400c8212582c800c054080b40d102945ea41200d441409513005454958040740000d48450340080c1150340d162110181000c43c2e40360804650303550364040040040c1d601d450a10055210310040d08030185020180c1c1d4400701c1648c4040c0601d41044032407 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 599916393 1250 599915143 599915149
    0x80a0b0a06020705060a030e16050102120a02120a121b0f08190b060408072705072106260d080f0610030b040213080c0303090a1a0c070f0807090209 65
    0x80650741c085d24a40d444694000c01240a0810001015040d0103020000764440705040d95090907280c007a021544401244410451540b0880701c2010041e00b145c98510200d44040006020109030761408030340c0460389a5554003111031013400327a11941c0700742c210798042c250458584a800c00441c1000002450100d00480482d600c1c1d00340301040c50364502243e4070382d580300c0c030550b0007409545007161074440c1c94040c2c50881e1142500c0c219030105e00c000e200c200241580c0182d074070818482c1e03544102018603c144008458681d92203446d44c54070359801003020b04403068000003c3e0a0700c40483c551002d1000c58504081c01c4091040420000b4010030400441c031003030154102400f41c0300000319103100384c0103c004048000d0b100303900500020f5a00404901d5000c40401e895401050b00c0b03811a0303c4040503904d201c0c0c81459600008802070030091050740e1900240b100b480c1c0e60f40f5600d0480d0200701c040c01c00e045500b00003102c000440c401d1000e02c45c10081e01c000742c101290110f140c030b80c070a400 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 599917643 1250 599916393 599916403
    0x30b0703021c11040f0f060806040614040b1f020601030b0a111603020106051c050d0813020f03070503030c03130e010302010507020603060a050a080a02031207030e090408040e010303080a0b0a0602 86
    0x281c2c0c00400e0700d40c2460000c2c1c0b01e030b440459005002c802c00d805a0f960f2180c0361411912241d2050700c00040c80c3e4008110f03a071403e445580e08568580d10f400810401c4981484090111060456800943e0100c5071950b0008102a4000400c82d07601400d0598110710b000c1c540b401d0082d0161921910f00510030040540e10710031100d01051007083c1900301443c3c0d240480c00f41c000e83d00420f80101c031140b030149054036088019000d5a00c520191a003c142c2500102e900d12070840e45400c8031546044147d0244c10200ca4a021220019040d56242600e540103e40b4640c17005108000c1648001610035913051030350340404c05403480400c01000b55156400080240c0221480644280300010120301c2a0740c542e070844000f484040d050703030800c503a1030041d551103440d02c0c03005a020f4082c210052003d20351000031120015859201c1a01c562103e02c144904070000030021280f541e020440421000d00400b1843d008601c2555002060302d800ca40d090183e5080345072480c0505a00c107810b010701c0d0f40201e4 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 599918893 1250 599917643 599917687
    0x40612032d0804170a0806030d0c03080109020f040e0c0924040b03150904050c030f03070c14150c0109020a0503060f04060b0a03080708180d200f030610030b070302 72
    0xa8420752030b0f112400c14000d1119181c030818010400040c2c600b14564000310300c0c6209032001c40c01c0d135901840c04042a1804d00305450024001026a40113102121403503020f0316202160802050406842e2010701e402d8900076038070012003140c041640c54452030010760f6045000041c5034800785510700d039491544a406503000b9900b481e40080f000407020b00503c180d071544c114004182164134102410310035100d1200d928094002d024010903400d196400104480c012584108440e402034075182440690420320743c5695401a809950815014030b4040038040c481b42000c0001030440a80c81040045c032280e41c0110f0283c0c0200b001c00665400b451070b00b07540650400030201d051641030000805684854200800002d800309120b01030006a001400640c0c8201d0403400d6400380d24010015402d0704c003880102041e4422180b00603001815040043d60180900345018a03a001c50002e030600804032461464000803100400520291600f119001103071400c0843c0352409640d502e95201403004 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 599920143 1250 599918893 599918897
    0x705010b1516060203220c0302100306180207080712080a0b040e150406182303030603100b060f0d14010501110318150f030a05090304120f0c05040612032d 68
    0x202c0006c030043d820240c076203491201c200c40203d2105e218940b0b440c1e81c60035400140c4c015842c41380245081070092140300c0c1035440c071964860b04c0c51410100c0d00086c2d071002408403468542809114001001c1049000e008181070301c540c0d00a180075400391302110001230f9418840e03030501d040312501510120350b0032180c112400490344580c0e503609188015019000131030340d08002c000000f1043c00382104803042a400c180242201480c000d014469580c0030a444c0c0b554150048a0309030864081540081003172140504110704003010303000c003542241c2150f03120520b1980c803940b11a40a000056220b8090311090910030f541d6445a010305030f4900865818114940d401c6400d54095918403e0a000809451020710382d0351910001290313850708255050813166061002080300710a021081e9402d54403107550500e0a174026844c0d1003a500e5013508291558031241c0004101c3d42c030f0341e0280d0302c0500050b07158081c0002ca82d250007840700710821220749226100d2456200d55032140146e021b40d23581d480c = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 599921393 1250 599920143 599920147
    0x30809040e070e07050703031b0e060706060906030303020703230f0c030705010f140907060c06020319090501052707090203071205010306051b070c210204020705010b15160602 77
    0x41c0740c401d25000064001c802210020810001080c1d800402070203624420390307041c00f01801484520b03140001c1100903d012a002451042c0f450810341c001e40546800b900c00499102d58030843c640803140d1030780050340041c1c1c00007004018141c0041004084241e820781d01c6115140c0c2100024980c0070341680600c8610f000200c40070200410400e54000580200c000c00901200300b00d800c00920f0b40f202c004140c0c2070f544001424011700403031007c040719600e490348044010b2079601d02d4000d610003025810030300d010600802415582c1d100c1d900d0702a01c83c00c0006510b0030400b0740e10248150444060704030038001c0d041e00c010320002180c65801c582c1c0b00311000d0303100e440d0140c05859501001409a1001e441d200000060102940103140505603114102ea10340000041010f9944a034840c081d003039090300c400410850b05c9885410300c9040b400e09080d0341d644141c2e4000f80607030b84202d02c151950382d1240c1c0103000c54640841c0090290503902151071818a070a44200301d11800302401071318003a40 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 599922643 1250 599921393 599921411
    0x20c0307090209120303010f2402030a050a1e0314151f1b1b170d080612030f12011212030b0105070b072016050904080f0a0f0e0303030103080904 64
    0xd0b500401312000008054984968592500d80100c00c5a8071603042d0b4009070031003851061107040b0041104514641c051440e240602005841c1940405800310400c008001c1e4006030303400300d452840d090040c594000c580f0304401c1e00c460741c5080d03001d88014490310501980a072540d44808001040d840222046440c8020008003034a45088040b6204d0b105042d4480940c200310f10680c242010b812088a0f0359000340c0c0790b00406d030341e550003030a14034035a40c001e5a044031128016002107030304c40001015002d842850340300c80750450700010710340728008801064070b10010711900d4000c0c0c0034000980c0ce14410490b5a21007010000950303520500345503403050402d603541d00c20000c0f03c1c8840d8101d00e8030001803c0c0444028441c3e81c01240c040c89003a24030071092013080300408c3c400742d5914642d10710100b1500748030400c410136001400403546042c041140c2408813621001411410381c0e15100c4080c3d5034046000581404001204c8030311030b800810040c030010303140ba41503c142e5002628000303080b00c4 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 599923893 1250 599922643 599922649
    0x1f05010810090e1c0c020f04090c03050d050a0e060901021f180c05040c030902060307031d010906050609090d0f0c05011e021c18020f0a090e0d0f020c0307090209 71
    0x101e50040700d074aa050001100b82d2420000e44a1480d80f42d00c42092a071080303076a411910b00100c00d00c025401941100c4140440c542070f0401242940912507640c0100ea40b40e40e580d14000300f01c4001d801049001c40c04c0c50700b890f0040401652240191000f48c904020721000079151a012600b41c24007002c4029071803c6110140e11140c968070302105094103000c51401c00070609800707031003140d116a0804580b100354520070302410002560143c199400d43d117a201094015140c6000d10005440c0400c00d5401507910900030f140d1a64000d8400261604081c010f1101c5450300501d01075059000c2c4c496201090303448074422850400038641803078161410319040c0e000d000004070f80d05007100341c4110303100c401c2c8056008241090411800c0c0d0000004460803d090f80d1294042c561904c40d5a0f50104c054240140d000c040300c0002440c1c500000d48440003582196800364980240740d01900300d40d84c00e02c0d0010507108110009000410380c4490550020382e80b03248038010180c2054010900b542151 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 599925143 1250 599923893 599923921
    0x506090108090742091a070209040812070f23070b07020606040506010e03101805060106020f0c0a030b151306080a12110304030609170d0e061f050108 66
    0x1001c00501942d44101010060f40a00500080b80020b880c900c4030003040c5111300c855114100000c0c2d01c801c614140382840b0f05400c83c2c00407503c0102c98004001c00001a40e6003a8414888d41c46420724545601080d003c0f801c04143c002c0c224001e1000800303241900541141c1078440340341008103041141c035003c82480da00e500810400404c003101d0007052000007600402c13400d20800003a1020802e5076204d0380116040400e500318990503420450f05441940c1c5070383c0040b8034880c1c440101c09401103c5646161500100345e00c184016040490281342c01e0006020410b500d490442707910480324295201c5010004010f000070100300b5a4480c080300544450440c0460f01a03181d0701080490f546510950b140e0000d010211441a010ad1ba00380310140540a031990010b80b9200560130302c1d046540c0d0344000c0003046429181182c010500000000d4680c008110301484070001048502d02201c1051034100003604101042d4541e940180308003100c8240b4400f00d54007460440c6554442e409290780c64 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 599926393 1250 599925143 599925149
    0x109020a0e06010c0b070806040c0513031502070c0b040f06030209060307080619060c051e0303070c0501090605071d030c030c011d0d08190206010807090c120c030f1505060901080907 80
    0x20716032004c019001f40c01c04442807144c60151018000b40c0c41030703a03044445100c2c800300c0da090a402d441e401e10205001c10a03000342c1e0700320760380014170b004450f032500c9000d024664069408000c0005041c0440c6000a905034010b001d0b80c02c040d400c01884a002440a00004258500300b10f000070006010f60f0b01c982c030304604c0f0600c41c400001c55a0302d80f18000d040d589001426a803e1044103034030b9100d80303c1c080305041e6210080c0003031401e649035490101c960480800c0141d80725900c860043c0e021507110312a0318004c101c1600d901100c6411000c180301c0400c0540c9929110390407484c00030b1441c5e200410100c01c2c6644c01d203800c80f103005030f0b0f101c40e00880b0749403440b464020026007240001c0111800c000e00700806074910f031481031060300808999270b401c02d0044540c5600101c03030400200380c103030300607400303011341410520603580c92418101c080f00c48807110030001907202c600160310140b091207010300c00702c0c4600030107604605180100d08188140740c2100d0400100d400060040302e824800d00c03010f = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 599927643 1250 599926393 599926403
    0x81c0203070f0c0f08030c0a0f0203160e07110c0102100b010c05010608060114032e060816050a053a080706091506030b19022a01050105030109020a0e06010c 69
    0x515085800c0403c1000800e0240390401c429484001c21743c060004103441003181080010320401086541301c110030710310701108a806119683d045444003a1581c034000251a04800501080c501400010a42c6030144860303d0b560700004082182d0fa40c3c007048400b407048021502040c0e17100790000485181a241c100030b08607510b4058042038400000c99040d0484e0400114400c000c1400d00130581c0f6030203a244410844c42e450b07043e94041d41e100051114607010868400a0010707981d07103c0500303204074031242081158540340c0621180c9060b6411001414003502c5800340f681c0e80c0c103108100340d000918564022002c80b90f20b1403070300801c40940801b0300da1180e6826241d580341d00e4170001400c0b040030112881034003141500f00d08102885110100c0b80c201200510944031344000c010345100c030b04145039005400708690303103030b08090030790014031940c1e00114100111111520207003100c0044e00581d02c40d07414611458096034808507007500350b8603801c4445401e601e41000584407220f400c640108 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 599928893 1250 599927643 599927663
    0x3070c0311031e04032d0b0601120f1d01050108030d05060d060c020a03081501050307080901090b1f140d021221040305240c0a021e06011e081c020307 66
    0x158100c40000030b003017268032940d18201c18421011100d98501d80e0480c41000e04400c0c25402e00c041170290524031f8104106041c800d10300e0300b03444030034020345010300070005075161102c0025602c081c03011203a0b518100c400008101d1035040105541d240e10450300401155a150008210643c0d43e140340203c180384d01510400050032441c80103502c82c0c0c040202038011940300d000103124261640f0240b07101513030594500b4a10b0740c4100d001d507004035000e0700c1a6480d650781c41081001910143c1500c1c043c00c0703241440019101d40071041d0b20840b42039040903426401100e00c00480f43c641241003030440d68101c4e0030b030b4501c00c0075881c40341c901038015441c0c14124104503802811b4210560042007940c0c05501640e280d401c24682041c40d40541c0781084031000c01360b1001a6000c203000001e48150a41031064038440f411246610b0030700d00b120081000590440c6004111039030018034100e171b01c04850307a50340c00c02c1450000002e44941c2139250400200f41404a00e6000d14400d1003124040e6901201c428 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 599930143 1250 599928893 599928937
    0x70c020a09020a021c020304060206010303031a0301110c24010e190203010b0406030b100c06200301090b030601051203030f0c0415030c02010608011e0f02091507030e0603070c031103 80
    0x5d644040d0580d4034440d0b0a1448080504540b000c03048506036442a00100710300c0c2d01e503a07002c80007410f10300a800a4200748440590312941c0a01581c0d01181d5403d40345912000000e000da0b0508111418150302c06100030780d081900e080d42c103032440c115800c0c0c020060050760b4440309006c1c0c008410398840c107418400400800e070948480007501c240c4000b0b640800440c0554028058001d000d080c41c100402c075880e120100180c0b00e504110074416240c00d020b015501da40500c07140b030350401e82222442641f1002004100d007801c02100c0d00503c030441c1c080211641d2150640d480c1d21000d0004103a103448500010481101c1070101d03402800c00c0c10000018281c000c20043c0107100212103040194240310300064403490500504424074104000e900000d1942c0c15944001c0100031140c5620a40a10031582e40d42c1d40e500f0590102402c4102d02079940400b40780084c0b001c2c000020030391040e1414000e01c240568010000038503641d14ac14064103000250202c1803450040c1203200d040c4910720890f103 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 599931393 1250 599930143 599930147
    0xb0c07080f1209060a0501061e02030412080d05090601210201090e01031103010c020d1b1407030f140d05030f0a0b0a1e090911060a0e04060e061309020603070c020a09020a 75
    0xb900c540b40c18001e550040d02e030070400800303031b800c02e01c91840050b200514003008524030180708440c1c041240122440c10b96101c0303021981c0c00201e6800d460710704010800500391400f0b409641d0340010710002510166061020300b803c0006451390401440c132140b1102021079010b03078008400390500c0c0030312440d1982c1d64a0f01c558444c10644d549400707942052010340c090740c000110a0070b40d02c1c1c19290800c00302c2840030181d18014904a043d00d20b00310002e00c842ca4000e0901400019502a50501d01c80d002a0b04100480d554100072120b03890f4003d4440315141c0b540017080d00d030014a000c0c00c0b40749940302d040c09a0b000e05050708a450744201132040001c1c0014512441c1c000c82307040c038051682c496a85102000454260760707009009150b00a805011515114004026003604c41c06c00d5108181040c0102d4102c81071504545c6215406a0038030a10345881e21050582c0181140c00b4880118550301045440c00043d203100d060001104d528003c542d109003101001d010700d5101151030300c601c0040 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 599932643 1250 599931393 599931427
    0x190302150d0b0a030222380a030201080c070204020f0a0f02070e22080c0d0e0a05010207080606010c050f0f030702090a1a06030a0f020708030a060b0a020a0b07091e05010909090b0c07080f 82
    0x30070648038011f43e103943c48a0501d0340e0420b040b6a016110400305948070322103942c440c1d0020404a920950801665110740000070180001a2607540c070900e22030504000a40791500030380110b41c490100400f00410210340311522041c4440d4176a8032070341842c440c600000c890050384c0c4007a40500401400c81825640504611a943c1c42259101d007469a1000103a89540729406041c0b19504007c0000f046540150300d000e0596204104440c8a00304c82084281410300395001c561203a000000c01e1415845c1c58508190091022201007200055075103c00007143c0310900424007501021000540c030f10391517800b9625003c0d001200b0766450480b407420700003690007183d0360301241d450240041507030003a80c419601506041c0e00106110b0080b6120f44200c414010220300c2008007000b0b001c2804004000609210000340c103044080d10b0030400058205a442e030072104126140409807404100d8074074146402c120307040400d5688030354a0070803114502c1070a0711110400d500003541c5030900d0b0b801903 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 599933893 1250 599932643 599932721
    0x50a0b0415030807021002160602030a0f0e01021e010b10030209130513061505060f0d05010e1b030603030f0c15070503070806190302150d0b0a030222 66
    0x1a042001e5004060210010205404060300504041c4040780060900064241e120886801207481e00c4480301005c40001600f5004540140c0011541e1111150811003e28070501c0905095140b0140c400c0001e64401c0707024600c055465481c110514684002c6d4000441e050004d4180c0e00360007040782018000c0e51202c55440c1c042d20810f000a1003601c00ca120341405040d60040d2141d940309140c8070302002c3e0071250300344459109030b60000501e0782d50383c40041c10781c2d903081c00700142c41e121081c850400f11a070590180d04000340e10020000851000415449202d820440080d2243c40e258003003403840c02083c90700e411080002078004558170000032103400d818041180803810b643d034804103c42e14007081e2000c8020402d4400441c20601d02615000326109048030301c03040b0103660b40c00203003418440e4410520004c10005151000800034011940b8071042030b6100b40c220307451540881c8046800c00410007034000c0d58103402045484540000c0d92032081082c036900440b15900d0704408140c0104 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 599935143 1250 599933893 599933899
    0x2102030a0902121204030f060e03160203100509060601030c09050306010303051c0c1407030e1509010f05071a070c05070803031608061503070201020706090507030b0709031e0c0801050a0b 82
    0xf100c1c01d40760000004215050059491960341401c1c81d59442c500a04c01c556000c6400302c3d00e5040001e500d0408002805868803400400340c10062540103142c10310a90640b41e0b410389080908008441000080e115007083e42840c0c000754160384484200c90548481c0c22155050181c24000424107910202038450a00309102d0001c1c0408042d00e2003086841c900c06030008a242c0d008881c80d01001c00000c4c0c00d890307000b41060308070b001c2c0c00000910008011101d881d19998042082c40b91568441010340780f0351450b090251a20040c0d0b10390003400341c46a03002500038103003140006c2c0814404c42001500035480011110303a07684502655490380c00848501008081030964000310502c14400240901d42c05814903140407210304c1e0400d00ea500083c41c400540d9001c210f0340000403100d100d01104d6902800c007901e64035040d45800e40040303001801d01410844d0b044030920104011110640c01811048010415203807580f911048036107255000882c00e500c0c08040040c1c80e45d075508000c04683c030031 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 599936393 1250 599935143 599935159
    0x1503031204081b0f0712020f091003330216080a080103050c0a0303050702010c0203030f0705070905010506070b01141f0e0102010e2404020609060f0c10090b04032102030a0902 77
    0x48107895807926800c0188000745c1c06050300304841041005109189070015008441c030400e6040440c010343c605540001084562000c01c200b4071170074003401000c401001c15013000b0b0312801004100da107810b40c0e00039112140c0c0041c80030320a6541841c0524041da01514068550706004405032407001f007480b0503141d40c01200c196044038030308100844256a80750b2101410209250011911011441000c0382c0500c0100207a60540b0400c0700508500c81c800c000800f4601e0130400c0110a90b641a403007580148018024000003034100440f1505480411000d058415006000540d0020341c0808600800550155044103107500030704030860400c003078009200168001042030f0348ca40004d021b016488041507508031a0300a589489a0040c1c0010721040c1000320321b200213505a0f008166038900d03103000061050800d00e091105144a51005030704016400440d268082c2d0400010402410440041101540002d2085003a03590010300e143c11926490301182c03c034010000c000041e031068281c = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 599937643 1250 599936393 599936437
    0x612110a060804080307090803030108010603031d06070f03090302061b060f160f090b0f03060109090e03030c220306200301260f060405100b03010b09150303120408 72
    0x11188240d4100d07001039846044950f62620345411039000035285001300041c00c00300250540c0c003000994081c0080f000002015460b61034042c091a10310254070210120704910011349a9a00c019030b081c0d0340d0000200d0031640d10a181c101c032400369079000213501100c04030314030400c0c02103504062000800300d01101c0c025124032807034110000084440020001c451058008a03a1040104968512150520b507021380e0300c404000d4403641001044084c1d01c0b03408010840650780c0070904100800955404000040e280e0a44a45070f10005058282c2c0e150001080041c142c041c2400c0c1d901c0e075840b9600d0800c004e48a00e0641e02801803c020074410525661a20b0f070503043d0181101d040314400c6140340c0ba039040008020031703105c451012815480c0036105a66500060074040d1070303c120b11910140000403204940c070300403604462005c602980c588000e050040c0c80d0f01c07042e0382c2c002d0f400d6200c81002030000e8000a01d58410b000c0701101c44040340d400d000030040117101624541c08600c44049131001c1d = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 599938893 1250 599937643 599937649
    0x21c11030a11120a0b01030e191e08071209180501053f070e01030323070327081027031b0c0b0f0c10050709050103050c0904061211 58
    0x6403080d02441c0190f204082040103c480d03101d1100000103040c04586004c80c100c010b400d248110030141c00384484000140704004d1200e4081c01c0700d512000410034000055115030b5500d0041d5100180040104080e486030140140e100c0310050901c0f8801610203a004031141015000c20f10505009025100401240100c0b2031243d00b10304084046070640e40200b084840000000d00f0507600c600d010b00c80020600ca07030918000e1303011b54002e440e07030020041d8040b0000403090340c101c0044c0304103100380101c1000070744c82002a41401700e001c25951030b20180c1008642101203580c05201944542e80701c0c900c507500d240d00002c1c81c2e441c1070602c0c910308680c003a0b416980318400c03200040015070070007801ca0562081d600034001c0c403801030ba14101c055444261200300d80c1c0c41031640d41c20f074480100702250240e0040000c141c0e1003010b80720511580c246240060001c029138015541495101c01c00905200c45070410349085160050062105039641c03400501121039100e000c0d540c0d03030007560a6941d141 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 599940143 1250 599938893 599938897
    0xe010f0203070507020f0a09050f16050901050a030e1e0c031203040c150507020d0605011404092004020c0a03050403150c140f0c1608160b040504021c11030a11 70
    0x4a5503e40b07501d410b8903a0308018084001c2c040b0300343d00100d58403012450415602c00d20384078184050304421682010815240d6584030703404800301300103080040d00c2c01a41c1c000c06481c02b01515003804035207410540b8060f0304003036180d401c8035210814440300c001d0520340040c101201c018150280e0b0b03203c030002c188040080c88121005003520031018030400c44510111002180900a860801c0c2414402d50000da0603031801c280649402c0e440d80c0050181a26005121041100840341080006c0807695206080102050079002e050028102d03091141c88640403981c8503404003007901e400c040c1382c0c41d01130300640081c00161075410307a02080c085500c00c2e52080c0c1c06e5014880d119003a85001b0a410003100d40e0007121039400e8003006020b4064203000401481c03051299070309102d00281e00704448180342450600d414180580482d10420045030200201c4098801c00d07540075a1700c40c41c282090700726079080c001000d861880c0c125800b2004040d90081c6005ea5203c90043c000040c1880c8600264 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 599941393 1250 599940143 599940151
    0x408030703060512030901231303110904030c02011d040e010c090803040b0301140a0503030a17091902151b010605040b041a0409060e07080f010606020d0f1404050d060e010f0203 78
    0x10758400c0126006d150b003d20710b054056005207508030075130203c1e1010b880781c540229508400d0040000410300c1013107110a008101c0c003005035000c41140c0350a0320000d100388044da0f0040c0c18040402c18400c0b4000d86c564008039881405001840590200c0f03680c0ca00030010380d140e820000d4141c0a0114045038040105d408442031a40c1403070a60b403c00141100145281e031540754400e03c5800300107034a440910213002d00c00050380350201c034107907031100c414000f41c401042d2010a0f00004031801c3c1c5003881d089002c1c520303501038442d2583d10303400350b0140c02103125051006203840803080300c5c0c2d20b102c101500400280e0388142c50900208641d0070503c0141c83c402d02410009984c92080c00d034960406620a4200d940683c6020608050420750740d42400d0068118003099000f05450035018507003401060000c00c85440104401050010002c01c401c0c200c001072001c1100102e10012159040d2054170003810005044044508103450040018110060741801650070410b44003520900f62080c0d900c1 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 599942643 1250 599941393 599941429
    0x50c0309120313020a15140c07061413030b041b031205092107051503090703080c0f0d120c02011a01110a0c0b07170c03090d110904080307030605 64
    0xd6900c0c1c0480c80d00c21500014034000d0800c4250000f08050380e10f010b074560040c040122140340d0f41100c03810007400052080812020804100040c503456000002e651f000c485c801d00d01700c542070100c1c02049020b40b084000c0d0000454204402005002c400912180107900c601d1022802030f041c40c01c80407854803144400f5241c000b0f88550503144a000718014100c03c580180406030350321059500c4034801c000400500c1981e40404018005421706a8802d8521141c1d4a0024110310300705602a907076150740d010040000402041c180d110748403c11401e48050046030542c2c8401c100141c00070101003000f0207040b046800c0201c8610a2801885441002e4910a140e0414100d0010064410104c800c1e0350b03d1a600c2410f03003450204000b034401c00c1c050300b5024003569403850982030049440107001140c030304100003040107500b0f4110000854000550079103854400c0410f0b4103105011542140f06641c0084038072b0200020800120005c1d8419142ea46042000d103031510240001c9400c070143c0154 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 599943893 1250 599942643 599942653
    0x1140d0b01020d080c0a08061c0c05040f0212060f060c030703030b01032901050f1c050106020c0105040f060c02130c0201050f160903140705030f1507051809060609040e0709050c0309 80
    0x54a40c0c400c1247c80c1c1d11400181c03000505055074149000410340e282c034166050071034070b1000c2c0160320b03041c002c00327858048010095003401036050030607025080c05043c244c410015405520610386940040e51303213088901040e00d8842507241006405825401c0b01d042c0004d1424a8840c698030051107a1903c1c200b0892600c1220705c40c2b0401036400e54805c00308401404030a211180010003a01401007201950140c0031806514184000c1e240943c15144d0505000c011b100621a05d40c1c07240b5004201c0b202490000281050703400412003444440301400455800c008400307032000d805420075405000281686940c07075507000c04d5420702c0581c3e800e500700001c0e24000c040022030008010003032000e42e04820340e082c0d40e0fa1800040d00d40803030515100000d401441104002401c40c800055101da101d090941c82c102d0a00c5103000c03210905802c491141c03481d800810020b0310f81c1c00580d00c0c42480640200035000000c40010317540e6078144610309560b4103190020301e110f540d003000e580c01040704400a00c = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 599945143 1250 599943893 599943907
    0x110405041509111003110a05030709090903020604020a090c020d1101060e0f3103050a03060b040605270f101707080403020115050303040b0901140d0b01020d080c 71
    0x44094440a04241c4501a40240c9804581003601c0342a044030311030710501c0b02d2030703401c002400b02504100c2000c82c1454a4000844613400d40c1c4411940100060300d4155a203540f00c04e02551036110f96017100c24128600010ba5040540000300d280c0568001c8440d140e843c3c1d99115040d09451029002c0720050708a9141061290300a10010501400c004000301d2000e031101183d4000b11022074400c011030ba5540c00348010a003040441c0380b0348500c00a05000724900302800c402408505050040410000180e40421107109a02c5503001d0301d00b4000c5643d40d26030701c0e40c00600035004040c618040344440840d641045103034a11070410f42d40050000c80c071580100f8104100e001d503200701d11041c85000c48a02940d5a000b0a0540c0b06410507160414203040c03d040c02030031a009a4020080f540f0480c030280a01c3e50008103850454140000c03081e40c50f0180001245c04181c181c03403043caa40c3c00841e200b48001901d400403101c0c120282e00300e40d45195042c81c120f43c4a40d00b55040080000108414 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 599946393 1250 599945143 599945149
    0x6031d0c0d03051b0105040209070201090c0b091906080714040806010306021e0304120f110c1e0a03111503040b0a0228020d090b0c03040e070315140103060608010311 73
    0x154101d58041c3c2040c50410049996041110340d203004100000d0355105e040008603c0c0040c00c058000c441840200900faa40380d40e021041c0070341c1e004120b10400040350303d0540365150529000c000c00c51000040405640350005090a00140d03071315404501140030010081c0014000e413012074145000038161a442d42d01d0b0b210095110034005503441e03500c600f4035410129103000960140b8403488412a002800c00002040312202d2841c8104000d500b129120705c49100043e00340d15603c003201c00f54598411030b9401021a00c450a00503041582c0040000c14271910603c04117607420300383c4a002100d5552907020362a48400c4a00524060410780070403601030266020702210b9045407000342e01c1025030300d40514502e419000d40c0d00143d1180ea204205941e00c03118140051440c140d2075420039803a040d104c0d131640294020081c00c0101000000c160620903040b00f5011241100071459150311501c1c44071007006404001d03804a828402c00295441c03241043d24100c0760088821b1502c0c418503420 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 599947643 1250 599946393 599946409
    0x21003110d0b1504030507050405062707020f151602030a121a06040308070c0e0106020c040929010602010501050306040f02240c0f1002031003032003120106031d0c 72
    0x1c9900607100d1005920f80240050041001e14021030042001e2803404041001740d600007003055025905c405046050700901811105070b400d4151001001555011703c02c80c98103a0001e54440c05210711a400d00d21800441c04181c01a6032811401401780144030080c0da03a44181a01c840c0028160440e1008541096001001500303200d1a1048042040780004055801c50341003501d035001d0010722001003010503400440189100c1ca0f645141d0341c54007002070746401001010700d029a445407410340402c8002e0140004480410342803101c08101107c503103d043c0802d00503030380550700c1c1c10004540fa2400041841c0301c0d50f4440901c01d482c0c983d60f42030082c5407802e80c00001c0707030703030500641541d0132070030076001d0301d284071210780101501584039089900d0808c4052507448154810810701001d03003003585401050782d425040003401e09564007108414130b4a00b00e2015243d020110311000c03800800541281207030308c280c0c3d05000c01c4580010040c4080c00824003500c059001c000218680d06040301 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 599948893 1250 599947643 599947661
    0x3020d0f050d11160f0b09060702120d020d0804021003021c05070f090b0913050702070306110301090b0108131e02061903150b0301050108190e0604021003110d 70
    0x300285003a522552120700d00381d07004000c000407848000c9040d030b48100411040300e4200d600307042030701000e24100030060204040d019030b031754007040041c5201954484100311100303aa03002c1e00a160103400c0c082000c0c2c13940b00714690040140143c0c1c082501d0f01e4803600295000e1900141980b12036120000103030000e60000000c0200482c0c003021100c00002640314a910680340343d00c40340c0c0d0508840c0c0c0c000700043d0a0303402c40b640880040c8003104050300c8800200161a0840400080644881409034035100b2184e000600e0641844414529120560003460481d880c00a050115890600043d0b03190030302210303640780b105403020304180803e1166015201043e802001a05201c410340c01141243d40004034540d00b6000721802412860f606214910300200c0030704220780801d09180320400c06200c1842041c0c104018900444c2d10202141c11580340003d24180810400040c0100552a407108a8040c0d10590f60f080c3d403611240e00034010b503402c89040d03030380c4070f490060021a034800503c8000 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 599950143 1250 599948893 599948903
    0xf0309060902040c0c0506010807080618160909020f040204080a15180302061005030d2003160f141b04110408030a1107120b0a1a060315011e0903020d 66
    0x2840301c000d0380715031041548a0b4019940d1003080030f45414141c5c40c008040e4420720305a48100810030110101141c06600481424201d0702c4080321400810b03c6d0a0141e0074070070052690803c00112038460380e01035080d00c0d10070780b80440c0841c08403041008a0181e445541d513260004600a00041c1050740c01514003089c0320b4001034400031080c92078841d9072031540110096407003802840008807102c3d4030400140421401014664801140144561041450303907403911060b01d1034802c400c0003442075510102d5030b1903014035890b00500b07240c1c0080202340c2c0c041d607103503445c803600507428800420030036045509070066424076444034080c0b0001f401e042640c4c5070380d250103000105007101c0500040044070100e548030328644998043e001c3c200780ca964019119620f00688500001d0008003416500460141c40018451481202110b486100744085948603100000f007100c101e105d81201e2280040c00c1c1d075220070104500e04601044102c407942000032811002c400c00052804201607101140300b5 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 599951393 1250 599950143 599950151
    0xc0a0f060e0a26010f09020a0e0c0c031812010b30060a06060801060806011d13060902220b0d0504080c061302010f02210a021e03070309050604060f030906 68
    0xc400200050030220480d081c103c1c0e01c08810500b20f0024044c00c08107100c840740400902919030700180c10800c0318400da0702c40443e02d60006040e0340501043d50a01c182280c1500c0c0d030342d1781121854400c5ea407550113032442040d26108500040030140315910395240301400c40b01c20300710400580c880c1441c02c4542449444440400420080c9080c81228040d41d1001401b084150405901802d0b909050b000318040025a070b0404c603c03a03901080d10070906042420000c421240800458242000450303c0002141818030000c1c00c0c903115401040b0410220300c2c0020b04800d048c141131010002c51140543c034074400d1250746541e00c000d0384010380140c8101c40081c9002241c000060134014101d03003804d2488120445002036503040302004074512118030140c5103d20340340707135080310200c1ea590b801c0c0c0c1e00e481e0120301c000789980208080c11030341c003040022018000300926044d50347e074000c1d04102c00045c10001c00040070706000e010346090310003688689804440080f011401050346200668901c0e4071 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 599952643 1250 599951393 599951399
    0x1502180f0301091b151704030503040c0b0703021b0d20010c17070201030f0b130903120e100f14040602070218040f0201080907060e130e1c020c0a0f060e0a 68
    0x11001040c0c50926900c2e5903e030303c0d24000d000000c100844e0700285c2408007007142c14820882c89801c0b5603009500d0f00701962251583e05144880001d21b4103d8884d880c0c0000301c400c145030300001d0410030459401e0010f0b13290b14222040c0101c181c51100c009012580f400c2000028000302e41e29580700325418036003030084000f56140c074a10301c3c1040c280f440040380e000030080250350b4540682156040e000b0818801d04c06100013060b41400e958964188842ea101d1661042612a10890350885640750b01071040b00c80c6038024a84035040748003010f0031185842001c920201d0a07005191000d18007080c4500e0960701c0e40c45540203548025000c0340d02c030310035a54840045a00c1203400b40190b02071041420a450288000b40900c0c501408500180d0b00c400c208010703081e84042202c0c95420107892500e0031000a000e8003014200040350f07100c05008004c109960804500e0018408001380e600325800b03108500305101c151002400342070f1102c0350300ca00520401d802a05601c00205010b0301c3c0c0f28101d5a = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 599953893 1250 599952643 599952653
    0x906141e0a09080111090105030a09061b020115080a0c061416030807020c090103080f0c0102071e021306080606121905030301171501051c060603050601031502180f030109 75
    0x1100c858100c1c0030502e000d50921080209204a0003000300c0c42041c94544000100060a5800000c120318a01915001030301c040080b1034100300c0d0320f0f13401c840101290035002d5401034080d10944100014000a00000140c0a100081c00c0380180d0b4020101310210390400e001210201c01c13044140794500410000341c50304100500c400f03032015001e075071002c0a030f05003194024100180b0002c082c2c481d8204c040140041203a22040f139580310a0b1030340310342d03868110740700c0e003070280c040d0110140c614039212511900c0007113803007043d0342424400c45070f0314000100318803010100c2d9075078058906150b0001c07001500c02c1c18213002064400480394201c407403243e510728090b0200050010104c5d031540011004014428910301d2590000d1200c20143c8003480b68015030100d00d02d01442140d1003841405000c0c00300e640010402e0a00c41e800070740030310141d42c03641442e5680c2c200c03c3c481102c64034034001083c5400a050710a6800b61030200c42981c0424420b0010402034030281c1550382e525550720748a41e40050 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 599955143 1250 599953893 599953897
    0x81b090102070b040807170303042307170601030b0105010215061005160c0f080111030a090305040b120121050613020a0f180b0103020403020d0605041a07020109120906141e 76
    0x39081c0b009101b01410900d9a0b200000100d006107040e0740103000348000075800d184403c402c07628110003200f61001628007145001c5481e80300040c020000c044103e41100089400d40c183c0b40940582c441c240d0341c600c01203136940848403050489071030040200e440d5180010441d0b00d922540d14046080080c0300344100610806941e00302c0386d040035a0800c0040ca400d0403413440040000d1402001440c2070008004000d200003090380241c15030316000070040501401c15907001d80019201e0540721880b03a40c049800d82d03028000d4010500c4045445410401202e102c85102c0d40c1c0030b4050490354440c0c0700309041121052908a90100010102190744804074501100030f0048140110484108902d107004039484d4243c09410980100030910250b00c070008541c1c1c180394400000a01aa118203262411203c6800c1c40c0c9001c81883c001d0008880d81500480c58040c003903901c0600c50304a0740d0b4160ba00720180d118900120760751115001980502d1005004c5400208203550f94801759003035600005c0d = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 599956393 1250 599955143 599955149
    0x302040216170a0507060b0d05030a08091203160f1715091b0f0a0306080303192d020c03043602250501090c03060f0b01081b090102070b04 61
    0x10301c084120000500410002d046045a00408070a180046070b032001803080c443c41402810143d00c900c007500b8103031504041102129049410703280c0b02c0e80401001401c1a209540c005003a224a50a2100b181c000d41c0803a80110421000010a00807900043e01c46107a01802c440030b0019104115444130000451288549401480040044c41060421101001c0600000100643c245041100d00003000403a0903409044403611b84810303000c402100980010340011815000c0032040c003414800d0000301d0b506407101e002c0140224480503a4080034507466244040380c4607003034682d116505040f58000d04e441a003c0080c0c038a480e46804c042103241d50844202c0d090f500d10541c1c0890f80c00f400d0130082043c030341c0f80302c403e5145c41110031b03013030a9880f50007001a030329031446182c420400100354000c0101a9001604114890343c9080280c0100440b0b4804000d40781844140c080640c450724a080c843c8000001ea2620090040b4008501d50414842281548541000400e02c1c2107a0780143c001 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 599957643 1250 599956393 599956417
    0x2409120a0c1a09160b0723120a05040e150d0602090a0314030703110604170901050706050f041101090815100308030124030b060706331409010308030103060b04020403020402 76
    0x20b05070900c1208084030140d00612401005100100010b9000418090801c4525140354442e13841e1090395410230316003034142107200700009007002d0030b103070454083d004882c2d084588070380e607564144440c10b014140400985d408023031104010001204d981c0035200707542e000344c0708640c00c0d0b80344d42d50100000c000791801002c907400400c6030410142d01900c15445201e403030020300864101599612480f00d20105c02048100011540413041e92007281036902503508001c083c0000e05003d10015181201510306807150764005414200e10350041d41080d0880341803030002c0003410300c416581d0040306805020000300d01035804001003c1041ca1000c0d5000e005407580069411000204a0101c424500244414181851300c01d160340d40d1381400b0703600100d03002000410000032111080540c906e90000808125134110040b5000180150007141035643d0103103030501840f090000c000f0460310034440184001d504200500004605400c180c2c174040d0040e101506040e11b903170000c1d05036040084034801e = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 599958893 1250 599957643 599957653
    0x1308031305120d0c03030f02040e0405070e09100b03030d1509051308040501080901060f15092907060b0306011212110303060f0d052409120a0c1a09 65
    0x25021102000d050050204660700d01d403003158a03001c0b81d250015000124207004580165800307040c0680c0040d2011040352004542e600c0e1101000c40c60320030180c0c0c040d6064824408003095503203252841da4000c004000c0100a0a010320300b003503001d03056004981c0d4150000b4405c07401d000354140100c1214598007510500090304242c0e460080381c00003007101741303030101986080c40410020011201590030a10701090070342d981c041d0950141c0500d0344001d10000c81c0202c0000c8200c10780c0e03161404100c1c1c41d174234000c0c43d07603543d000b14507000014402012099024401050205265401006240d200b5600032910341d101d1000642052070990124403d0005180100e00300113401b00d840030040e0050030b014441403100179100c1d0383c80c0002884a40526405050301c40559200494600c07503a5200f0b0888141c4c40340e880c0e80c50300620000059450082c09500824440180811081161520300e5203040c201600b032502195010381c4c4000580b07200400000900c001c45904143c1c1c3e1180c42c481000700 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 599960143 1250 599958893 599958907
    0x607170307110d0f1d130e010c09050306150a0801020c1c080405070e18010906020a020706020714150904090606050a090209132a020d08060d030c031202130803 70
    0x1800340341101280c2c03901500f101a0855143da00801c1d8240d0301c00c420710700100350744c600520761812800d8024002e98001000706a40c82c00040c6900107501008041e4001e016120385680c0a840490040c0030719585500807070000b179094602074000594a4500500e12401c0c1c91303850180c182240e01805800c08a50800500000000c0c0c00310440c1240742d0580c0f5000700149001d031202500c440c0b07180222076480301640c001ca515900c1d5040180c2040402d030008001880080c80d0a078000d51068000703001600400800007803060001c103c0c182101d40300240107a10f84108420442c4c520541d80c003645c0c8a500c14450750f042a15540300d2081c945215280006000e1708100c2008403800056000c0c9140c6da0040120000d6515844000815031007c03200214602d081c5d00400c0200e807102c0d035142900100ca41a609200542c0028441c0c04030380c903030302c03680f2203612034400303010303e140800c034028011904082403000000c1c861740046210241c4040b00504060020240701d55001c03441e80020000d60010581c0c0c = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 599961393 1250 599960143 599960147
    0x20a0312020712050d0c24050f100e34120e06070504140409050d0503010906060507170a17011502120310030b090c06040b040602010c1106060f0607170307 68
    0x109003e081a076544001070f01440c2e9501c0e68801c3c0300c070350903c10421142c48041c104201c00c8444d0000396421005801641c01010010700101401c4a101403c0c0e01c000c0040340074071031100c9244081da86c4403218860695100664110507803401c1c0c0c2541440c4080c4c0817050780d00031044502ca0885090703507945003024071a214412013070303a9801006140350b8014105000c4425040b00858044030080884800321040e050300190081038200c50150081c010350303981007400c0d680721000350b059a00c20341c0d04200c859141d00044889015458005004882180c449003854035100f0203841940c034a45081001c11803003030003004c03100100782c0c801e11640100008110629405100109510380c1c40c04c0000d09510b040c40060000c00003d1002500300e210550200302c0300d00081c032940640400140010341d45a54610403804103034068032550b00103510308203010b240144501c01c2450405c0c1c080c8000c2149403a150200a000007417603040590000e403c1000307a00088401100401001c030740049a5103c0c07404801c0 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 599962643 1250 599961393 599961403
    0x306100312030e062d09030910111b120d030e010b01031107170c16050907030911130204030b0a020c010b030d021c030b03031c0f090203070b03090a020a031202 70
    0x212042c1802d00f6540001c3c09030003d9100d9102c902900340c914403007550b46001422104000802c040310000008001d0101800002029600c0c0300341d40f41d010f04904e8043c1212a038001c0d00340c501d880d4109030740b804d00360454041c02a420020003440e10f0014907094080916001c8142030580100e0f845030650300d64800300307110700f509055081c201440304021900b02ea44980c071440d0002400203440e801c20b4111f111544040d83c040d410400300f200c20701c001da114644d110888074400d0522502c1e100d00025402c903c80d018840c0401d50008060400c24501010080c1da00285030381c40c400541d09020000c0402c0e9107401d8a800b4187c0007400590f030340704500480d8290380188c030348680664410322034442e18641c0081c214400c01c2107607503000200b001102048001d440c40e80c1d030740c40e0315100115400003030341a02016002d5440005c5000c21500d49501c0c1642c09403400d5900107541a0001c030b82c100010783d0044015540300d1084000e03510170f850742d130740040c51400301d9400541d14101031000360741f0390540403c8 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 599963893 1250 599962643 599962673
    0xe0a0309090606050405040c05130b043f030e06180a050f0907050a02070e16110118030c050c06071b1d150f0a08010b031e0d0503041103061003 63
    0x1414000d0394100a0f024141e4421481180d02555a480a41d481503101e81c069810251f01c04602901310399603460b91801c25003145c007814000500600e9035010001100e081d4403580d0a000001c2c440039061107020403641e00f9a00d2007034040c050122400c010b50b607900001400754040012884141003051410701050f00c54a4001c1c50007a050400000c020340d0782c0343c1c3c609911005c945080c603174a03404d0b08001c9007025006c0e845550408482810f000309101030705c42c1d00d40000003c0e03980310500c0c1e4010181d242681c9015185071102001121144040b911441c03009114901980032501c81081903000714106501031242a101c1d03500146440307010b007203000c2c42500204800401d914081c0c800340880300d40804041c00c1900c1d031401d845666401600d500a90345680a0018400c0340205d80d54000c0794080d01c4149800b512902880807190710600e135101c03001004644a400800030240070200990b2241e1018106541088108802441a903001c03c4440d00c1161a9041d1035580d6242d440d00e1138041c1c10310700e = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 599965143 1250 599963893 599963909
    0x720010911060c01090c0905070e04150b0d15090204030209070810090c170411040b0312030106050a02030c0706170c270112050a09210203040b090f040e0a0309 70
    0x46400c4001c070307011140d07052107007030220b4605540743c0c0b500b00c2d0382d4010444028001c2c0400304e04075001030003030290b51000e48a8201c50315404080c19a0b1003c20044411011075007800c00f0080c542804180700d0240034000a00540078001001c54406c048a10341c1500740e07000c0e0300030a80026003031045040c075018041d0040001d040c01c00d458101000005a4450300d8000d02004a40d038038000c420b5544034030120a2100070700c850500c1c05c1e06003818584111900009414010360034511a01400d0030300150350040056507007011403c43c2d007002400c03120b540c80300c050881184410300080111080a00c400d100070030300c1e1b03292048a4402140555080c44001340a54210350080c040c0d00c2c0000100d4603160410740b8000c81c5090035400302c100580300c561300d107418015107a00d8401000025503030303548141c030140d00400000c0c0c04100c01d40c000c00c00c083d14100001005070400d010402500c19800094050075070001e02c0504100e1240c00131a0440c7c14540d0082c1880e40096442400c0c1038010b031071a0040d000700c03 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 599966393 1250 599965143 599965151
    0xf0b01051009060f120207060c081501020a02060702090a0902030303010b03070909020405030d030f0204090612060b0f0307060806270f0c04120201200a1a1015050d1103072001 77
    0x100c0241c004d20705041001c0901c040400b010256203006d60480b80c80680c8104100540c0104007401072800b04112001d43c005010321040030560360001510388510b039401011189003100e1a4240110202c2c05445400c0054488a200300107036002e201840c060526040c4c1a5200c0c41c002400034843c0d54035511488030248104000d0006440c080384c8031104082a05000c070b5500102660034000344941e0380701c1c58181740382c04004645501080c104911550207500c00348084a51081000301c01000030745480d91681c0608000c1226902500d040350f0b11510040c10300d100b0074a20b002485014100e01d44415507160070f0020042013450140d1690b0304159904030303250a041c1015281d1000304500350010741400b60100700e0030350165110001d00007000648068640101c240d02d81001070085580c2d00c0880c00700908005a2070a001e200a070013166540c440c4400e2009c4100b00645142c0c1c05001c0c03007182d003521014200c02200d050b41c01140586000e54503010361020311141010244071005180c141a410 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 599967643 1250 599966393 599966399
    0x305100c08060f0409150c02030901090801152105330118021b030a080f0a021801210c02331617010e180303040510180f0b01051009 58
    0x80c01e110401c03d80000e8400150304040d03410030040311400201c0380b01101d4140022403088550200c050007031550280c8586c0031007034980050b582178850a085825000c0c042c44400c00580c14980107040c400e01d80014100340800c4103495190805a24954007418a100d4070b05603800808040010000c08030070314950101541017140c00e482d900d00024034080c0868010501012141040c030102038890407010803a50740e4551580050701c000000ca600750010781c14100001c400c03c00d24003c0f101010300b440c20305c8915100390b1006454041d903645040b0b2441850561070b0817400c0440c81010a5a081c030f03002440640d002c0c821504407480f40140108402030090003840c40f0300100000c2c6038020a02501c40128a01ca5450846170300da00086441181c0c98610700000f03c002c481048180071711001c5589207143c11000e525140d5910055400034560780c80141c800b20790007020340c000304c010307410501f143c240c11181780c44003040d8007810300d4161003034800640100403c0c604081004104041811b00c4680c0510b = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 599968893 1250 599967643 599967649
    0x60317030f04151806060306050f09030a0302160204021206040b010513120212030d060f06090503101e06060306180b0114090d1406060a090501140d05030c01060305100c0806 76
    0x1c05040107002c1c901800c0aa50607142c0751308841003000c2141e00300780e401074403410084007420391440290750f02c52030728010691071113001d2900f03449826248011850174101c040214001e500c090303501d00c0045424012800141d032680014410142d0348500a920741c02c000f4208011181d0340200c60381800030070041344030314628a80514044a4202e8030075040500c990021450800154440100c14000000e16000d6854560300c2081078030b0080440b00ca8194640f601980e40c40082d01440303905a00c24035400f2001d1490750024070300c01064400549100052140d4a800d4494031b40001002c01d80b225400d0142244014003060110300c0300105104602140e000030f0619003510b4031074043c1c6030002031a00516102c0c1c0380903954555112440000ca40d80c0120001e44901c0e059581d01d105001242c000180200980901410789052180440808034510100807614000510444450005000745c020f10003003032054000460140c006132130710700011a6040c2c12202481010418812120240400c5071 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 599970143 1250 599968893 599968921
    0x20a030515010905041e09081305010507020112020d0e12070516300503040e0106080f0403051902013c05040b0402010309020d061b090801050c0901050f04090f06031703 74
    0x41342683c000903000c0309540f05101031060804010001810011200e04100340040248007106400d403107c1c185549900c01140c0300c5c4101d00b006030003c0c25000c440380148066500414189840700070000d042c960540d1003c2c10070480680080d420400852030000b03014052200d2821030250b540501d04003130404000340c00ca4031002900403a10381c5030302454821101402d2243d000560400122512156070340c0b4155500c86e002d0280c00006031140c004030307401048100e2624000ca0b13054a0f0a030501516083c02903070352a0000821007159211481f840c8600043c401ca9001c0c11542107450702c0c0200e42c6e8151160341580c2030a08201285080100004500505505900203030309103130129031140240002980d030f40180c00c02500c07892800c000e550002d03082035000d242d141200c3d1540d0005a0f652286903080b900c048421411802c1d00b0048400c0700e40c440d800500c4040f1203034101606154883c08040102c544501c1c54030041076480c4414028030165a540800c0307000801801480c2d4503090000440d89 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 599971393 1250 599970143 599970149
    0x12050702010909090f03031406030a06110412060e0f0f2d010c02010c021c080c0904060b0a02031312051005103c030b0708091f020a0305150109 63
    0x11401061040440e031264000c5802402054020b0240010a080103100c503030f8114402c5000c00c0c81c003004868460440818230b4800d490060240881c01402e40b90400508000c11500c50000c4080002050b005000f82d184488a070048400041050f4500c00c01da19160940e0707000c201d16806420f48043c8040e00290301c404034841d15281404c2000f40c41e5150070703114170014500e82d03c0d508019003070402c2641540003038603519082d42265048401b115040c0c40c0d008550300d4074000aa121000a06a0000c0100400b24075101a0001684560b02c01848034a80c020000c04001a00f000a840e0385200e5500c54500c098a01c0403580135401c0d6040c2e031030139603c003511617481480985a00005802484a019003801403250707c64030a40205061403103680c00c01a11000c001450703400304074004020119080d1410f036940600e5070701c12603c80780c10541e00c5013002005e0130076603c44c0442c12010484202c02d603117587c80d21a18003613159001c081002c0c0980350018503c1d20340c0448500c8003049030382d1200a00d021 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 599972643 1250 599971393 599971397
    0x3120e0105040b0c15060906060d2310030507080607080a0c030618060504060e060f091008010903080103120e010813080705070b04030506010b030c092815090803030412 74
    0x2150568400688560046070b1000e2025030010440f003402200120313050f05041e001d0b4000b40750603034415042040d800400c1e141c2a403c910140075a681e0700760141d02c00c1c0841076660f071a201c1039406007048040e010100f124040c060440d40e0100300f04210f0100007101c003800000d0b018007081e24101c58000c1c50040300604044035142c0740c404580603a4081d600800c00391414031440c51160101c0e01900c2c01500440c444c0a004070301d44100002d082405c104054002c40006042654899040c07040154002e800f034016041d18a400c540051603500034030034850914031907246d004071989941000c00103e01c036003800d002071010108102031103a902c004103503800000b0f8142e030107a8815600703142440d4000c3c400018214441e03094041442505d000242007141e10135011600d00d41c1c1c96030951080c0340030556008100180034000c3d03a03070514185500608002103d014074074215001384040c40008030780e51090744880c00468496110a500c01148409400b5202c01180b0310b06155070340401551540c010f40d01 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 599973893 1250 599972643 599972657
    0xc020a020120011a0f0307031a04022706010e180f0a060b0c100c0203040305030f340b1b091302041e1536120303020702030f03040312 59
    0x14004001070400404000440c0082110b00d0b084c01e400c41e0181d03608484103114076500c00162a0501e8005983d01c250380e070000e003c08000c400301e5820960314602401c1268891400050342d042c0c40025608006244040003ca44043c1000c00002d0400f00d4071200303003070191403000490705001d540c03200401d07004003103640d0b04040e5540c0c448645000b05a40d030000000ba0300002460005c0c4c00000171000c2d5031819003d003c00044501001c16607891050303100040840e0014880d0034a1280640050b202191002002c80c103912140c5201c00505100c0107800102c0c001c5075803410003401889a03800382d002c0c1500d141100f96030000840360509000d14071135a4802c41d850702c4a81c41c030407a59010f560081103a100141c807101e0400007030780c0c0d101c3e045014040c0407020350004450030b070303219100185082c405c0710f080030109c0e010b400c06107800c0481d8041c0000705403200600090924070400d807003ca914000d60700180c031007501b44105424165203040d000340551042c801400460400c22050303d0551507414150 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 599975143 1250 599973893 599973917
    0x9100312080c0f0705010e06100312050a1e05030a050a022110030c0611010f020a050d0f090b101e03020f010807020a171c090c15140304081902010c020a0201 69
    0x400184183c809031181d803040414118104401501301c2e03402c2c1040345040e0780f0190340307101100d46071404a10001c1c0c580c0103040103403d00356020b003000702050959407401c1c01176003054030780040198a500d000b0307030002400002000182c080034412980c000c0300f5400258035004030f01920f04005002080303030448850b003560205001020000b5610002e40d403012090248a548038006400015421414040b5508144001011808034800c8071002551910307031908118401c44000d00070070700346c0a500d01141e580d02e408e07400314407010501c9103d100340240d0861143d060002c072581040b1004001c2c042c12002e60014001a074402c11308000400c000c0c038140d00d070365552803012841c11142c0ca2000c1c040d04c0600503c20000e44a100c010000e00490307420b03000d6010f021144030b1085603208500a0445040584144800200039815071025011031615002c0f0109403140d074401da601c02e072002c4071070810002d111510200d00741100700581c00c02d80000c000c460701c0d000c0081e40325094400002c1c100300f040700b508 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 599976393 1250 599975143 599975161
    0x191d01050a0f200f061f0e0a0f1a1e030703030e0a03140a0c0512250f0b0d0b090114060d0204090c030e0c060a1e0e0d030e0910031208 59
    0x1e00380c408045010f8080c84060a001280c0303c004100c0d0814060140c800080d08500b005c0c0700d01016a2070504030769218a260920104195002602c1c01103526160b00300401c0d00072040c060041048544403c2451040d103804c00c0228008000004040026202e015a440f5075808101002280c4c5c01d0f007844c00130030303c9035000144001115000201004030b0180c1007641c410b0002031000442e0300c149050700101c3c1e2228104100458004210380596011001c12400d40c01102144000c0e044080c0d00f45902035110340502c8102c0d905d5802c005108000440e2441d00110170b4003500281c2c1c1010b5841e00425414405072a42038005807800501558000980040301c0c1c0300c60303046900030006200d04101403141d109000f0050020851400f01a200d00f080d001002e15140003104d0440400c0c1d160441002c3c0c00c0b100a1000ca14089004c9040c8010030054009030385030031140041d403511907650402d03010040300410858540c050030003d140b0824440509c0000d0346a820100c200c03120341407901c25aa034100c90 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 599977643 1250 599976393 599976407
    0x1e031621152c071a0702060306100908121e090604150c0c0603020c0c043e0304080a020d0801060507080c160f03140609070303110a0503191d01050a0f 66
    0x4030442d00700d4507242034240000302142100941e41c080749400209038040c00600c54034020f4040103980410704201141403032a0640d006500b0f16081d0601d1620f150b5a803d4050401110500040c0b0340140021021380d1a10661080c9a0a0350034111241c1406d0404000c10882d020354040c2c51118072100d00c2076869180910b12241c0451790142c0000851030720760800501a402017000d0134461720460070718081e54541801a100c084806138a01c50710490607502035107805150380340201c011031031000c46800d00300c007a4004500c5603029240d82030f591b440c3c4490092914480b544010100012400148429584142110b0700160040c01844e140c1050015190504c000103a907415400991540024000100c2e030801c1e003168060303130700c1c01c50541c03890f05030640300d034000c03038118607550040e05007840040c1c003c1d5954084900c80004842c0c81000039980c1030301c0d5a210320904440306196840e6240c03030f1944140c80080c802c8200745940740c030420300c4c40082c0641c09200790010a00845009804102d031040d40 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 599978893 1250 599977643 599977691
    0xa080f0c03040f03020319020924100c02031c080106112d10090c0e09100f0506120a02130b040905070b070c0e010308091e03162115 58
    0x3682d07926503680740b84004014103031000701d020780a18103501041c4e40c0380ca0000d03c040c1350040d00740e03505680d80e20091009d121416032000440f1442c51600e074010788606900c4240d104460703c0e1400410b04500401d441c01013250642010000003c1c0300400300703035100e1007035811141d040c00d1410904690300000c45c286400880551500320003420741001d8140c0760450200c010407010240c0d22012012020340707041d6140c6440c094404010058200300c01c0d143c0c825a1544200c002050350300074021600340700151b642c00b415015006840e6400d0001500c1e005241c0701d50003801c200184034605c45d030760104810185007a8200100c039501c408806042c0c0340c0390400d50f4103d900c00155141180c440d140c4040d05c2d004007006403020074241e000815800c401d101139906030ba41007001d280c245a07443e4100b040c00044034040300510a80c11142d01c0c9151800c2090514001c0301d4565603e8803030a01c0310251051450011032160201346048a8020440c402d00071a901c0c541b1100c041075102e100c91000c44480d080e85 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 599980143 1250 599978893 599978917
    0x1b09040905060712110a0e0f0a050907050d052d1b04080709050106020c030718110712171006181a0408011107200a09020309010b04050f07020a080f 65
    0x8001c1100c5281c1c01038010042c54144c0d1070400c401484d02c2d00300c248a00608050700b000c80d07190021158a440c0000b4070f06c3c1d206a0003000800c2c40d54807040840c800312001c0d101400803a0002c29a04007038411030041e275900c0401003840707010440481c0704076080c000d490943c029149115102066010884080c03e140020303a048407155925600c10400d40e54003424070483e80046e10f0b00d070001c030f0a10310100c0c12840e01c8900400038000b441c20540700e003507440f60b4100020350302d40c0c0d078a1410131004450806040790318000d40f4000e117101400395000e0040c07441c60810203110f482410030096201d0072181d200051710014500803c1074807556004061401098100d082004561030a0707805201003040180190342d0030300003e010554020740c440c4d410b8002d80b0320081610350074124054890768840003070040d0344401058980010303a10901da07403c03623005590182559440714600d04042c01c05026590f0410000f54070003c4c00e180c0044000c0d216811100020001c1d00b0024480101821070800e0300e051007038007 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 599981393 1250 599980143 599980153
    0x516020a120b01120503120705090405190c08042307051203071a0c041a1308010b21031e07140c0111010203040312050c041a030106030605091b09040905 67
    0x1540406000c8400070303004580c80c0418000116142010b18041e0007045d5100006608003602d4110303101d90051300500000c10050140810003c541c0e440c007640d801060707903402c22100d0f408003020f980c083d525003520240c140010281800001180e80c03040041c0c14110180e064941010511420f01300403d40c2d0205a0194404403c850280b401000410300144214407007070079851050110a01074600300e83c4940041d10501082081546840c0040301840704462840e161045190191141d0801c54112000aa5481002d0300090406004001007a081a0401c0c0c5c0d65100b82c42141d03980344940c1380f14400c00c2c1302a1614800f901203580541e00940d07403219101d28840700d2500e1700c0c0d503613040000031103000400c4580003410903c010320859000e2905a80c405088403401840749024020203842400090300c00c01c030014018008526208000d60b00b881800ea4075458002d0003020340d112500701d284590756000901140e100d01c912001c0842ca0a8806542c8031925140050002c1c40454005401400f44d = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 599982643 1250 599981393 599981399
    0x2131103010f1719020609010e0d0614090106030804142205040204060b0a0c0f0206091203090f04020906030403031109040207122a02120a060c02030403030e04050403080402010516020a 81
    0x1d0700d110055510340c803010090000303542000d9580c2c224910030300581c0c04400c13000790701609090004040604042c1000e40356200b015001c80c9a2803441402612900d41c0e9139141540c0815407842d0a80102207000244446401c60b101d8180f18031541c8101240300840b05142001d988540003840d102103813110128501303820700c65403a00a80780c115402c0b44654500039020440d41d000b44141c03189400540c2d1655042003060b82d50550304800f540b0180e80c4400103100003550399844840120107528420007841d00d49840d2010701c00044595609144102d0061001c15001e0b103440b0103803a071098140c130300070414a218120540b494401c400700c1701e030494000603a200030701502e900e0000c14115160780301c240101c0031148046103c071403070032514020101c24403410b0140c50085100019072a0110558282c91381d10341d0788408039500300400d800960800700301001495005005d260351000c00396818800c0d85001e0f40d00601c0100d000f00000d040c4800456030742021204408400b400c0347d4003511040d030080d1 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 599983893 1250 599982643 599982659
    0xd0810090920060f0304020d141c03150b34030f0f030501140103020a02030903030d060f0e072c030604030905041107050a081b01090b04060f0510030213110301 70
    0x5058402c100c0c075028001c0a41c038542c01c0890498885804100c252429502d03903600f08541c0c0403200f10151545581009410b005120a208201c08520340046441980c0310502024080e90103034449001e10344040c820070404825404125102da41217115401104010000712045688064400101107805c1040700c00400d034001605500588040e1076040383d00383c00d80401c5060342c4c000d00401d50101c8501c48103200550203600a4141245140140ca0900303020a0102c1d1440d040003903000c4005071180010040c4030b07924580d0314007920120389548041e00d002400070301030402d030144800c4061a01445240d11a0308800d06043d0a1002419900c10b410141001025080c881c015503206901d4440c000464944c80310440c0d040d160310030060044240a91110314040c0c11169260200c4050407502d8144824203210703489956105030400003043c109401d01c00d00300c4814818481005241c1313401e10201c8000b190039501143c1e411034070410800205041b200160070031280c10410013070f0120000c2008c1d0 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 599985143 1250 599983893 599983913
    0x6060a111c090e061f090504050a0b0f01051213030e06030f09060c070c0b1e040305100c09081507090b0f041d01031208090c0d05030309010e010b030d08100909 70
    0x2001e242c0c1c885a50507258000103d00410aa410962004c44400448103d07040c048803d0818401810b02c41001a61000400d080d5441258002c0d40c44d0340e1814a40c00d18507200d0403001e0034003021310b0000d0801c10b02c0c00308521112405421010180d80c12120102051b20460790502010b00c050607140c2c90703080c02030b21501c5501e81a50155102d008410014560169240c01c4d100d03865044541d03414082d280c00c4201c1e119501c680b00881d00c040b001d5044550218043e1700801c021071280300141400c05082d54048112400066494200801004100903020000810768036044103088200415100c0401c02e5804014541c0504480680424031111820b04440507008549000f0420f4061160450a0030041e11007400020101c0c40329050401a0030f04c0303209143d50040701c540c221a40881c842000904050407000100c440740c1c00041000301800c428082e04010203800d100078015440300900003034175161165080c1c1c0810003004c0009802403110400e120013050035070402c0215070b0303807420411b15403 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 599986393 1250 599985143 599985193
    0x3090a061806050108030a1d040e0a050d270302010305090c1207170102030c0a11010902031603030e04050c04090b06072909030405370f080d0c0b06060a11 68
    0x8640b41c180000b540784801b001700c074a010020350701c3e45d546d9000d800114100850907050103402595030700000e82580780030401c42002500450042001f000c039801e00501d0382403640000640600d903841c108208041000081041e242e0900b00400c0b82e41d102c1004a1800c105d150146510500041482d4044000030840740140c82d0744a001c2034220000003002801d038442a6154044000300700030540e11640305401b44040d0681000000c6a42100e50300042e10384024000c0c6601465a00c02040003016000f0003400e40b240001e59050003180b8225140d940075018034490010000c0c2ca82740d81100c00e03a40c1c00304540d401507000c180341c103c510b540c4580304e00d00c0c100c090401da1a201c1c004082000b0350000401d0710200c8000a010216015410400d500d0081c1c0c3c0c11301c002d039091028406061f100c0c29101003440603146001150640358540004246040304861501050007031071107400c0c022550b40401c9a40c01501030700c80f06c5d614041c0000482d465009042d00d5909406aa5000c103826418001c03c5160 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 599987643 1250 599986393 599986403
    0x911040b03030309100b030a0c03050d030b180415060308030109050901050702060f01062f0c031b0f1905060a050a02061b0a08150d03090503061e0c03090a0618 70
    0x4810303000401d1503640d1106a0b038111955200401200f00400f442c1c102002004014007070b105070860b030750390395508203095070012162900700c0c1c07410101d420380c1441810001c02e07084442451f19000103059215001d0041c1000e000f000c42201c4608070b849190300304000460f40180c0d890343c1c2e982d444134010014501950001c10b15400c0c0310100d0349080c40080e0303050144c0d01040200041c1d910340701c8191801c441030f0200070325a540e56181031402d440c3e105c0720048071800328800761800940540805082c01c060081030000300d00890503500154503213149007000080305070f0704041d104405039205400720209031b202c280e10800020f101450710794010b014080c00f04880d021140c00c4d80300e90ba001800801c0684039016440400d003d0300c04082d03c600c41c01600000f014003440c4507140c0c0c03540130030384c100d6a068048d00844d83c2c0090412060034100100e50340291000000c071800d40c2d00c0c0c001141944d0f00a02181c118010101c00300301c1209042c00104100344c1d0020040141c20804100c1010110010106031a = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 599988893 1250 599987643 599987651
    0xf160b010504061a0901031407081006090b0a0302160b100e0f15012f071e060c2306071d0a05090c07060b0306071e1809090501020d091104 61
    0x303050b04081c0904004d540c0980002c0795411030000c55000b4540100c880a41050b44031a0141d01248075004100c0c005d40032a076540c500b914000407032244005840e400302040002ca5201000203c06840c140d900c3c0f48154500035940d00d40001d04426080d10285002e003100d02d003902400b402c1e900c2c81c405c3c5411100083c00c022074680d112511405400703800c64008580ca000c40943d002c0a41c40f0748403c06901400c3d4a9020311003038446001c61441d2124a046100c81d4841c590601c0810106504905070b00034800220b1402404d15200911803c2d28000090001c4070a030700c4100443c05060310b002d0100303621011a0700c1480d01840003025a04101c00702540707010b40c81c518140c035040035043c007000e41d54041c0c01700981e80c8410f00303180c0e41a40010001e48400ba0f80c1e0a08542e255018002c0318040d4606a0f10300c01140b80c0c0401222101c0b19030422541401000f030520440e5081075200e0004848080000282002460038501c4c0684134440f0480e400901d00341011080002800002c3c15100c01690100 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 599990143 1250 599988893 599988899
    0x50609090c060706091a0403030606020f0109021005030402060f030a0603020a060f02060711010f0e0303061206040f03121e0903020708160504020a0c02030d0206220201050307140f160b01 82
    0x41d4582000000d1903800480800440000c15019001070515910403000d10300c091000c581c1e001d241703200942e41280000c0d01c8000c00c1001945c10440c2d503800c041164000c00081407107a0014032028013800c4440240000440010190340d541015201c07040c50580380103507646085d500500c01005907000c04c03885803111041c0454654852082130041000070340084c0b00c291100b0100b5107820140d010b108003290340b05c0041a03252000d9008083c072180b1004000c68603410402c0803c4020080c010003001c4c40d511041c200808550008031895407141c142c20300741e124101d03ca186501401000422103403021420048100c240b40a50026201a000740e007034074107143e00c1d8a0f146d600c441c5425a41d8500501c6004d040c0014901680105020601401e003a076020b000c681c040b904189440d0910070140e0449001c000403d011041c08c44000e000940000c0310307004450b40042d040d4080507180c0320401142c03c4001407900c180b0030495046215880000c3d85401c0c0500c40c00c04441e005140403180300c64604000 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 599991393 1250 599990143 599990161
    0x7051501081e060712060911070b06030d05030a1a04180606080f0a02060d021213061b211e02071a06030a03110106030606030f02031b091f0503060a050609 68
    0x41e810000c284001d0480d5031034040003141c0810581011788443d5588080010b0352034440c0c4151100c91041800003603c4003440c1c00c1030350100300000c1100f4040e42290000d120031030b501100b101d6001d0410b040015884d88072250f6100840c0300718400c10b07000f500d40f14051501000083d01c5030700f00762145d40140a01a00e510060b521400151050742036948003410804c01840c0080103840300d042281001400d080b94110307000c40020041e120840f0004070401c00200f80201c9020740481102aa49845441009208020603074006090600b00030b03c144010081502c080e07410800710000701c9100d05c00204e1050700880000d5004800444510011382a0b001d405c50024000e540704103c000e0140c281080e150300c007500da914500460f0f541035542c072070300400000c03600d07c80c0c2d02c0550b000310030361040c070340072403042c1840c1201d40036045410085020100c9042d5441c883d44130b030702c000ea0501c01000e00103880091000860a0703044190b16015440c02c0104c903a05503800244641011548149503403100040 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 599992643 1250 599991393 599991433
    0x506030109020f12032811150a050c1603031d0705060a1112040801020d0b061e0a03180b220305030103081614060412170402090406020705150108 64
    0x94010030f11103070812103442c109020407641400d00058030319041007141800305080c0003100c00c0785000022403c2030b03005640300d0351000812420500900d103d9004002c08201d1200092000000a45690004510141c0c010644100004040d0b4410961903d40b601a0242041c1140c00300c200d041c1000d108140640010104100d80b0050f081502d00385000b2401ca902102002c10f1035180e110704100c4a01d00f00406000303000034440e2600050320755440d070701400b044c4d0342c03ca0442c0b407081000f8000c07055540750700103e10f01101012038159560b0704004000394042c029500507000d00c0c00040d038564007400079102d1203a1058450700c0c02100d4004c40300c200d0710b010725480d0340f004e00050010300051000407c448010403040c140200d007508040c3e503d964500c0a04142e012108040d04134405110810000030401010304850f41441c6460400d44199003041c4030008002030f01c40c6000c44081418010280e04807000150000d01b920441c000c0340c180707100a04d4084c4107030403182c4902203619001101300d440b = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 599993893 1250 599992643 599992661
    0x14010c110c01140304421e0c0e10080a05010602070303021504031b080c0105010501050405220902041401030506130f0201030c02070b041401140406050415180905010905060301 77
    0x12180a000710082c50340c003498000a004503410646c0c04c11000005d4111030b0720880b2104c8a0032411090100003410400400c00d51700d80300e40c0a4100510a00608044041d407594903030340c2140010008820700040f86c0302101010b503a50468482c076030f038600f401da1000100d4403c0c0d40b584001d202a9a80700c1049950b014140300181c0142c010401c001c410844076140980c2040c0285040107920b21180700d01c8100003910b4500311455070001558003c130700400e008081c0180380c2400c10318142450000070071900418090349021a010300c510440c1801c2455110420607500a803040084c22118414040d0b0f9503821b000550740f0380300f50300001d10b40307608058400015035405041c0c0e0400300842e038015000707000d075000f600007503000b000c0300480c5000315100684005e000c04140842000500f01c0013426809084911007841c80c02084244013042e04071048400702c40562400d42c1900143c200f00b00c41c500402445c6152103441e00707000007003081039074100034180c3d1203003402081103481343c0003003508a50b5001 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 599995143 1250 599993893 599993897
    0x1403030903030417070203010507031e060b040603020c0106090c051e160b04061806060609060e09010b0f041701050103060b0613090b061605010e07050303130b070206040314010c110c01 81
    0x400180029604c5024140c001000510319041c00100d45c0087e00703440c02210100c00180e960260140700945c4000e101c6460b050440040110604000408607140b003075010741818550006071540c00c2000940c030804c0100f054840800c4400701424000f825a44810070703032203d044090504100b18000c00007210302e1054803800d0103800c0c12956950108541d0014410b84402e961031a60303031315034107503905140c0f4003038852000040c0640c03d225020b06443c0040d003054003000302c0414164600e448603411181505e840d0650181c03035a050384201c10b05441150420496000010344c80400e10303005400c82ea040c0c0344146424050385200c0c0050003286d01a401e04910010b071000c00810047c0320340c0d40559030305c800c050182403811121708500303001244031103001c071010380d9242880101d035901840031501410b4120f001d1441c220090503400401c46142c00703070500e100000140b8030300719500da030201d50003154854055501000c00034411402000030280140104d012904d003007994810214041e0150b40050f = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 599996393 1250 599995143 599995147
    0x7080601030203065203050a1a01050306040e0717030403050705060a0e220e0303010f17031b1009110a1a16170c030a021005010f0e0a060b040b071403030903 69
    0x10314417100528008102d24003410421181243c001319440120040000b03807008555814518811022a46034100c01e924400c0040b91010540e0381c4001180e8126208880104241c01a01380300c2d4206100795000950382c000705000441c1000020018008490040080da07010035511410b008440c414001d1220000d6038083ca20265031514240071a0000304500400c010b04c0404003102044400c0c014050340c0c9544040700400c03d8030b400b10b511402400e8984131750410350b0b40c1c41113520358a0048807500d4658008652070041d10075810401401e00303103090001400300c60f15a080c0f0008c1104201300803809112002400300340d42090070200c1800b85000240c1030f1404100c1d00d08886031031000402225844600300e04242a1810720300035000a40601000d0b40d80d86d409824040d2500751001240d2644d0303810840100032202040d0a4070040751840c0d2484145661403240420050445801140c408803000c1000314408508401810126200302d05505040178440e0865030750307002c22607560240d9481 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 599997643 1250 599996393 599996461
    0x130308010f21060b090a060e010f0f0e34020607080c1801020f100605090a090f08090f040903110c01230a232710080c0c0708060103020306 61
    0x4054200d41c80307800707040001001412240000c40001080c0c1d41c0400287c1c40e00401e00c00f520190911500602210390030500d540c1c545403005842c0c061500c916008448500d00140545155401c3c407241701c00c1c8800700940340080c00e039038034070b8052100040c1001841940c000402d114064909280a1503122a0b802c4c2401c01c940c03208004660a900418114020401c0711108060200401d004420b001d03900806c0e05030030301c0700b40814804000d204402582c10b184802c1c01003468400001889904000e410340d58201c4440468244420400103540003440d0840700c4090517400203401304400700c4002503e112400003001102c00508100c0d00c2410b084441c944907140807503070070041c100c107401420040200c000e01e1101c641c110100c80100c0c40745c000000b6581d040301c2035908180c41c0b02c08200d80300c0c2c402490000042440e40b42260184000d0080d10004550f2039542d400a42e001c550105046840740751721201481c4e1a00402c0c40300b24028411032001c140113200003016041c000036010805a0000c0c1 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 599998893 1250 599997643 599997689
    0x90c010c1211070803030a1116060c09050607121407020f0d0507030b04151d0c04050604061703090f0406030314130e0901150501020c0d0308090c09130308010f 70
    0x800030703038558240018450040b0216406028210040003840003968407844d194607100162000c2e04003142c3c52880420103680c407004980001d05e003240d004800050704c03440d1a10705441c0c01185410841e0311070741c045032820801c080c0407805410924190baa01034a41c004007130b282014002d00c03000940c00b5040600f0082c4a00f016140724291034000d00032035526507681c0d02c0d48100c9a90540d0705660000e0072003020203403410b250013104880306000c10070381c0b0400100320701c0a032107079418488203120301d032a68041942c40e0b40f640c100801070080710110480c2500e8080d54550b507070780000c081074058070201912017154074240c810501180d0309921210349480c0b10440d80365017030744807048113807500302150804100b91040e1842d1610440c410300001036910b00c000c07513a020401e129840141150301c8902091a01c0d15114105202240d0501b8206200d481d00742201d8140310b041e09105400508801c100005c4c0fa0202c0034a1171a2802a152100b203640c842080e000441c80d40d01917038200c0602c144410a1b402 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 600000000 1107 599998893 599998913
    0x3120b0105030f070e132d09050304050d0f06060f03050f0703031e0210020d050105131404080304030e030d0e0a09062103110105040614090c010c 64
    0x52910383d92514030b9900090418040055841040005496400d0748124841100710300b440b0149918803418044c00302e424005841410600d460f0040c6501c43c07049008a5820401451802e42420300b44280c000c43c0d4034040701c02c0c000381070080c030100381c0a100d442c0151140005480c99a451800c01a01e0100384001c5243c05401c00441040040d030040d600e6083c4102c6405107040c8503d000d81c00364201042c400c06003100a000007158064003a85610072410f9038800c0b01c1d003030445c3e42030b6410041220b0541c1c49021059080101103000f1990740d102840c1d119120340b5082c140009000c01180c14003241aa00301d0200300c00420180c0d50b417900b114054058521600d0420541c1e00d0428106040d0100300c6183c603c4031007403e02c4a05041c440c86480d1104050180244003c2c03c1c00e14102c401001806440c0e00500e41c5100401c030303074441c0856000e0380844141e40b10308110605480e1201d01e1 = true := by decide +kernel

theorem cover : BRFrame.Cov 599820143 600000000 := by
  have h0 := BRFrame.cov_init 599820143
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599820143 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599820143 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599820143 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599820143 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599820143 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599820143 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599820143 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599820143 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599820143 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599820143 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599820143 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599820143 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599820143 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599820143 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599820143 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599820143 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599820143 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599820143 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599820143 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599820143 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599820143 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599820143 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599820143 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599820143 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599820143 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599820143 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599820143 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599820143 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599820143 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599820143 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599820143 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599820143 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599820143 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599820143 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599820143 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599820143 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599820143 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599820143 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599820143 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599820143 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599820143 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599820143 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599820143 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599820143 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599820143 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599820143 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599820143 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599820143 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599820143 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599820143 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599820143 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599820143 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599820143 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599820143 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599820143 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599820143 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599820143 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599820143 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599820143 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599820143 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599820143 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599820143 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599820143 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599820143 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599820143 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599820143 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599820143 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599820143 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599820143 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599820143 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599820143 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599820143 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599820143 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599820143 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599820143 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599820143 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599820143 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599820143 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599820143 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599820143 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599820143 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599820143 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599820143 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599820143 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599820143 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599820143 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599820143 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599820143 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599820143 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599820143 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599820143 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599820143 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599820143 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599820143 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599820143 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599820143 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599820143 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599820143 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599820143 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599820143 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599820143 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599820143 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599820143 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599820143 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599820143 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599820143 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599820143 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599820143 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599820143 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599820143 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599820143 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599820143 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599820143 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599820143 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599820143 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599820143 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599820143 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599820143 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599820143 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599820143 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599820143 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599820143 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599820143 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599820143 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599820143 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599820143 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599820143 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599820143 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599820143 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599820143 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599820143 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599820143 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599820143 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599820143 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599820143 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599820143 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599820143 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599820143 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599820143 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599820143 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599820143 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599820143 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599820143 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599820143 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 599820143 ≤ n) (h2 : n < 600000000) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
