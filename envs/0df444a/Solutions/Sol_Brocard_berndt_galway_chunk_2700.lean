-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2700
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T07:29:05.150536+00:00
-- url     : https://prove2.me/submissions/894261f7-b59f-47d0-a487-abbb512e1e29

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 485431654 ≤ n < 485611510 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 485432904 1250 485431654 485431669
    0x102031324090c081605061e0c10060501140906030403050705010b10021c020604050304090e12030c18090601020a14010212090309120601140f13020a12060906120212070302 76
    0x9a0043d0040010203040103000703820304440070425428071305501c9082120341c0f0740c001211990b00840303154012140e12804202c8940c4030700c0c0c002030034600c039025564020ba5503c0c0c0c0202c0231110b00341c8840458503001c074180140c0d4001d8250f1254000b034140005400b02c0d00a90003808042d200e44000158480540c002814002105800c4070040e44089120340d900040904692001403071400146582d2516564450340c0c0c3c8580c2c0140000107031139031082c6030f0558081007502c400114540c0c00a07160315101c40307101c0d40c54000141103da500c0c8100c180e13040a040c8460003e00907401030740508125100c5491310110080c00307012081540d90300700488003e804144100a0246c0d0340800956074aa00c1c03c0308116064503000301521181e0041001004003084d68545012030410031f940d44813180082400040c0c5a01c0030b000440c2482d0700000c0c2da414a40e522242d944400c5205550810903641c0b600c07001e4040303c5d45401001c2500300503000310303000b5241c610518411403088204440c1c03440d03103030790100c1c621 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 485434154 1250 485432904 485432921
    0x13080f0417010506010305090a050606190b0406030507080c0c0a0b0403090b1803010f051e040305130b070c06020c0f0d02062104060b01030c0c0204020c010e0601060906020f0102031324 81
    0x1030f50b50788140540781da0301d170040c1904005184011701c103500e8151210b1341c4542c00501320512605611060681e004941004c04000b80340301403c041d02ca50b528a8007501601c01110301c9800254486c0010312190135120540c1c078a0b01100f8024a03030003019580d58025104060001c1d800e220f01e0751130000788080f6201c02407030b0b207000a00404c0603d4003104145801d48460072003840b04c080c20709080100001031a8110744c2d29450700b0041d115652078070304090f41d2610511299a10200d400c107004a40c0c516984c005000191188201c481c21035a030b040e0807030701d86035210707004e50307201e031304800401c501d4606a045102c810707000806031858281c803482d00c4203a042c4139040c0d142103039420804200c1401801c1c4105199201c007801c2c117000c42180f85d00c0080c142050108003d124941c0030804516041c025440b00030041604000c86180e03507182c0e0405480c1032524401e81c80140b10703208940c5160790060003524001d1400310300304402d000442d50741301c080f884200c0d03043c82c1c13881c04d80441b00d031194000d0060252 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 485435404 1250 485434154 485434199
    0x60f08131e0309050604030b0705070303020712030b01020c040c0210022a06220b040602030406091a0105040c0201020c0303060f06300604051501050d0b0604030803010f0e13080f04 79
    0x141d4403081c40c2c050040741d0258441480742100780020008140030708822580309400b40381003a43d40003149419802402001c002a111440d0b8442046015030998040c0000150036000c44000a01c400200030540740c8204410006130400c1d11107039425201500500045100c0007071a801801c150b2009031458400b441501d21554441824002e454031110744001c0440c00040540141d440683c8a0504d6000301034002041d9540c0000003030b003404042d900115a041e88130070b0024501141e1b0b20f080000703800a02609215030301d894210500a070052085402c481c200c000514119a2000d04002002c0c00d5203c0e440d80054003003100f02d6803102407042c0c00748007580b41c40003407504000794103262107003400040005000e170340740c071041c0601000c111002d8003101c03600b481c19a41d1070f440400c000703014003640d1100e40e40049000c2004000c1003484000b9605079003040c1d0b240d101aa544aa0f900c03c0003105803868242c0805149456003c950003a0040000008480c0c00e01e24141e910780e00c500000d6041b10b000311 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 485436654 1250 485435404 485435453
    0x30d05011401050408150a1b0905011407021e0102011d0123070507060504110a2612040303050a0509130f0b0301050601052d0705070e0907060f0813 65
    0x14184a005200c0e600c1e0002c1c64114141418800c0b016604c480d0b11020883c0400c4610014804810580110144249202c0000350300d40b40d040000d000542d942c090680859402003280007600000002e680080e40c0040950008010782c4020724200ca0002d000581103540f14110b203104004070407030555070318040400000f592011181160031402290300760303d9480c00344c441032240d5103500c8000c1d582c0f504d40140c1c0c002141d4889161400209158000040e007082810000042c1c48040150640c00c00701e808080d454004c94417603c0310740340c10102ea001414910180010710210344161b01415040f000e44c2415850604410002410815902c2c03000c404291103030149006001c00e805800710b0810103900a000c1c81c00e01c2c0c0c2c0060300702c0c05075820280b00c43c842c0311240b01e0103404103411324000100140f40540c0e503c119003801a224401030084d40082401100810008100001c259003114900e598442c0d118544820441c0c51003006000c000501503414940d00101c0c040d014005182c54180b00c440 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 485437904 1250 485436654 485436659
    0xc02150a020f070e150405070c05061009050c0304020a06050d0b030a080306030f0f101104030605010b0c0f1c030c0c0b071808010218010804021507080a090e161d03030d0501 76
    0x910b800c2c05a08103a9840a510080c4017107488a400d140d8844042213501260980d610001120b0b55a1b00e00400b4206219100610803080810300c1c040742038aa58080500c41644c1d001c1e445020b91100707030760003508140e002c1410000213101c0c501400c1244506c00740881e198201c640002d29159a052003511601030000c140503092038100030b075880a2003100f024010003d06222180d8698030a01b4130030640e0381e00c031046013500703402d8501103401075580810304001650311100d44000fa60400c036840601c0348984035140b6924080000c0d0b070152251030400c200c40302403240e07a0031009043e821150130240300611410030009940700382658811f08060741c684079400000c800c50b0708018416442403a20764410084248158028004105d01c28420300340100c80c0d84683c400314070b5040d1640d20b00b80500b28042451810000e00074020050a08569245180d030b540754041c070840d040080e21042a030138140d070a4120328034000c4144200d01c03105450b070702c01501250300109003164004814403500660310f9006 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 485439154 1250 485437904 485437933
    0xf16021903120324172a0316030803010938010e0406030302071208090330090108060d150c03091214030411060f04080c0109090b0f010c02150a02 64
    0x542d10103c00160f80344507110509100c40d1807038941ea0041e440060100c3c003500014030000c01c103180004501c000d034501060380c200d00900841286d0340c00c29102e4000c6104512482203031400450039240c000720450318503480c040d04c00c0c1c02420301446050b91f114801d03c203603202006102c02e2040d003c0f8102c030180340c0b21280304001481e07058208201482149407030300500c0400e43c009512400e4400a200340168200f0508002801e80100c0c1d540c3c1d41c2c50303c601b12400c0c603403801080d22074102c240348801c251030184414000c84401d000d030554150014100300002b810340d01e0300d201448216400380b05402a00340d1202100c41c19503000d54208400300c0c0c0c44000c44c03810056403042500703038001546070825481d2603841c02080140b00160015041d61080d0f4032000669039003004942c02c990f252001c040d03031180d643e180700d92a540140c0c10079010814104000523006968000c1c642d080c0c000500c11135250300c01600550712810314600030381e000381e040e01d15030035060030200080245600c07d400401c01c90207000c44 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 485440404 1250 485439154 485439161
    0x912050307061d10020d0e12071a07050d09020a1a1b0a1106031f0f09051008070b1806040e330409020321030106020f030f160219031203 60
    0x50309411070350849103c0241502190b022101400b01c4000342e524200c0c0c07028500039205c0c1da01c2c00001d078080c03540e9106035048001d009000c900d101d5416554001607089489429040c100d4504000c280104802d81d605619035118410491000300861035040d00c40c1c3c3d00c180034131801091411000c1c0d000440e0120365003c422552a803110b05001081500d1290381d640d18500341c08084d15020742401f20115188180e9034000b200c11035504c880c3d5501c41941c0310902d41181d03c51f4407407581420300d4000420801aa001c0450003507980903001007406515144105125920031070400b5401c940441018005035141030051004118800c0109064184107458010400701103004004150100f80a05000e400b082c0485032402d908990001e1088a0360002c642000d402580000c80711030303000001d00c200720202c0c0255050701c07070690880b000c0111000d1912f83e00c1c0304105505e004000140542c151012003d0031a500191001d4100018140f16203681e00c001c1102d6001101c024248034181e4003020351610 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 485441654 1250 485440404 485440421
    0x1308030426070311130f0207060b10081b120a0e0610030b0f040f020904050d080601090807030b0a06050d060c1704240e0d020606100305091c091205030706 68
    0x160050401c80c12420903642d2000d610005000b004c0020850166075a1081010111107074174505100100c0344850000096103d1178007103607014646000701c005410180e0304805000307071a80781c1c9a92515039840b1918081e0310b01c50b08101c034600c00c200401c0e1781255002528050f500401c000724641881101c001e040c020000d028110320b03280040c0410205000c050341e19001022005550020380f21414440c0c624040c002c40a900200224207001c00c02000192000300c070106640c8442e0b90307440390707001102d084003544600841507000e000244003040b1800d90f43c030340018103400d0014416940740080b80c000039905d48195980382e41c400c02a4181500038041080304103500c01c58071254030b81a583c4901e540c42209201e886600210f00d50f5100304016403040780190800400c03240803125a81000b9510745045070b031240a41503500c451001e5030b029000c0d02f4060301c040009410041d907a9a1005150300041030031034204001f668001800d08c1c2c0b10310800c05000d000320013031940ca411505000044d00d0066 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 485442904 1250 485441654 485441699
    0x90b0105100e011e03020d060e0a0501051017090a020a060801061103070f060203040c1e03020f150301062d0302041e03082b0203010b040e0a02120609070513080304 72
    0x30800400380d0fa400803000200c030b002260300100d51403e04c3c60840c002c1c01111141811280f40c40001302e003c0c5500a1224424400d902088c03001c0c0c1e0300c480520140c484185407020104010111804180c201301c841c083c1c0c00400c1c24212101e0505540018480e0f9996501c0070000c100c05400502c03600360b01500549001400b80011407501000d80c0d64920003400100c0040c001941c0800450200103030b403a0450f00a202c3c1071401780440140c00c015a4111146100803032082d800102200d01c1402c040d00c0035040140d005424505681c60001d050350031030385281d20300303409140b046081031130711120404041d60b680d0940d0740141c0315030a0041c1c0c11094000c02d403010402c01342003001000007655070001c65610141208003100c50349080b84010300850991864080210700100010859030400405401101c0081a1f6808962683c645001c124400c3e0401003c00307642d5100040c08030701b46240d1668100146242c018075203801c1000300003900201c3c0d0000d030300315040010b042020384440d04035200a041107 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 485444154 1250 485442904 485442917
    0xb07020a090b030a0b270c01270b0f120c070c050102030306100e15070b040203060606030408030403030902010c05010203070306030b070908070e0601031e060f14011710050301090b010510 82
    0x2034a0020f907845808610082c05c0828a200003410300c80d4060425011105524500c94800056100300c0d8880c1d81c4001203a0004120500d00d00c00d00300c2c842810500c540311000394181c0b036810f0401421042e880640003006c2e140342003140110483c408104240309804081c0444d8443c282d0f0b00c0e09400f01003d503070007103045600034801c0c0405652a05411850b0150500300354040ba04040d02007034056200c0d140055134140042050018041c8041115204500c22800d5840310b90706c41007040303100d001c00c0d503000d007610005000250009000364031844680d801410036094001e055602c450a9030f000315028030009071925000c1040080000425402007000d0034002400c0c2c0c1040392207a500c105a2295842d4100d0350070200341680d0281e8480304c1c0000c03016074201d0303e50902c40700f04809002c1c1c2e4850520640c41d044000036040c06e50034007100d101c08059440030481d6110325000c18040e00b001c0c010045542540d200000d80340d40c00d02c10480591f2040052100e207600d03180402415221400c410002d010700b = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 485445404 1250 485444154 485444171
    0x1060e18070603062409080703080304050d03061203030b06121509010e15040522030f0909090f0b060411041401030f0501080c0910030b0703050a0e120a030207080f040b07020a09 78
    0x8030000f10000d242a1401c134011040c05c3d003c02286e00c07880e103501c07502e201e0043d10b0700801884021340c01540314500a10407141c0d10070412601f2000c6800901c00e4010600c2044200d20000b8401c0e000b04d96089802881c180c28a888064003654481080e20120002001034240003440d0410b092032900512150280901a00d090010115901d0f0703016040c510070b5642d10000b41b20a800740903014403403001c6010359203401e001454080c0006003034a0301d1340040307601c0c00780004100c40580502071005500181d13006680c282583d40680201d0080c10540d481504c0c2c0f6416280390013507502030001800e0341d800c2c080d1a00101c02c005401c81700461031240c0024182001800744100025400c5a008003d44940c5000e13552800d104000400b40d400c002c290006000500c000141d141d04480d0184129900410001d40c5a001c29a9548400e9601250102c810b01152040360f000f54054041c2c28090352409103408102102c6000a500507000291030580110740b04055042180c1c2d0754002d820203c0e400c00c082c44 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 485446654 1250 485445404 485445419
    0x3030806151b0a0f2f2427041406030706050705030c010e1b0301020711010e0406090609020d0506101d0a150f1101020f030a0b0301060e1807060306 65
    0xc0750341c007112400100b401e1645411142000082652600314001c002c2d4801c42d4a000303040208106102c11800442084008540b80c5100e01d00b60403000052240059241c40341102c900300c6d81024071440800303018008a1610410010168040039880b160303800010342e078004200449194503005814103180d80d080141c1602c7c0080c001091381c40d107017401520307a0304a141052540c45100300c0e9840c0395084c42004c1c0c070040d000146808050303803d41c030b004221100720300605d4202d000d142c0000e0101c0c0d0403510340200039401110b00d25901c0d100600085846500c41c6c00d8242595041e900c261003803540000c00b0b140c101d4080c81820307003152040346c40005202444800520803004010503122848418104240030b903619080b101c028413803001d81401c01e40321402c015261920711100c03403001c2000c9145490401d43d040c422501741c2000106118115100c0000340300040440044c0036805659452000c51801100b009552180c0c0e640d1003070850301c8500803070303103410724103240d0000c000e05052840070710850 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 485447904 1250 485446654 485446657
    0x9010f0603051e0307021c060c210c18030510110f0a210c0807031d0a0b040c090e0d090504060f03030503280e15070903080a02030c03130303080615 65
    0x4541d00e000c1c0b46101050083d1a50551044040003903000440c05881e0241d0b0710a03014240c4914000c40307040240307610b44502a40d94030b0f03295004582e144181c56810205403401d500c4007041100710b1418904e80c0c290848a400c201ca280d4100b5542540207030500300386100b8a0107a800e00141150449003041c030105442001406107000c40c134213120060510302c1403103112404400130310658244c2802001280e48005e003c41c0f0007640c4800010741000d0400c103284800740000015407200c18000c041503000c80d00e5900030380c140500204e403000c03c0d21000049061090082500e541c0661000d0122801e81d05009000741d841c50340710034056810800e080001c1040340700500b08a907018202030703a0f01d90312501484456400b00c000c00491000f0300d09807a40450740383e4425407903c240c1d04202c803540310201560103480b0204030340c0440020440181030002440030009080380a006004883c00d00d0304001c141411508150820f0312080200b0008105059101c8040381d000a070a0b580c8a030791188401c0c1c40d1040307 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 485449154 1250 485447904 485447923
    0x905030d033318020d02161e1104110d0906060e0f04050303060915030d02010f0612020f010c0c08062a090a36050a1407080f13080a0809010f060305 65
    0x160300c03091402e00c034940250100c0d201005e905008640c1c8046041310490f08011881013541c03000034989880f141071150782e1801c4081a0402d81621302c4407039034010440a40301850801c0d0900c00f040c0a08058a0030900a001c0010312400000c1005414002c80c07030b40e45c0800900c0720b07416006160a09c40411000300403030b5000f0800342d5044405544807034401015032001d0075016054814111001d01c2150306500140d4030540403502070083c84d546412084600c941c04802950140e03800e515003c86601491006000500c625180144665600c80c2203003440070072a500098484d00112022074495068408074101a4506005060905010201e90b4054650081c0c10241c110303001b89421505158038004607840b0350381d1807060100700c0c03440018060001540c980802c00e0400f0f0b181c100400001c4d480300c3c07150086603580b013515500c103100b010f22520f002d4541004d0300182c0c0180030106004900a0140f903040c0d441d00707805424107500f41401c43d4040c41002075800d01e001030502c00544081401e004 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 485450404 1250 485449154 485449169
    0x306070f08011208070b151534020312040501020c0a12020d03051b010e07050105071221060b0304051c05120c280809070e160905030d0333 61
    0xc4030306880e1203600d0380301d5040041e01c00140c220801041f500d0390104541441d0003903602c84042c0140108840d514010510030400d01800008103d21501c60700992110200340311038000c14040ea51340109003400a5407c7c80408000c00140a11880d6010803110170300c03180549080701050300d014600b500c244a40c68000748540c9004003002c0c18140720718159840c8036001d041d1003145204e0390840300d000b0300300030700040500e008103003000034a0340c0201c0c161109541c020300c400c4800c41c0000b031b007282d040948103d4035081b400b0003c0d241140b84424461a400f401980c04080c2c0d990605042c4540340084040c4c401e00403400da2a030030a07180b5401010b40b6a00b030a85484461103858034451503040d0f0088450585103000d80e90055a84181c407240100f00b050f0490304c9000041d10350300109525038526000740350f900d81d80342c000b05040b85031400d00c0f00c4846440f458800d40711500c07100001d04111440d460301d80026243e801d40f04c0b031851200744100201341c903c00f900590045d081038004c0350a0240c0729242c0c = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 485451654 1250 485450404 485450429
    0xb030103080435070518010803120403030213060f081003051e15040803190b0904030f36050402120403030510080a03180602010207170307020307060204090b0306070f0801 75
    0x282c81c80503c20004a010700c07a121400301d071000c01040540c0d42c0d00c0d00d05c507151080c4490301c4442c598060355181d06058901c410081c500d0700c0da43c08000011140050b10803402c1507420010500d07141413080e802c01c00380200c0d5603102e0f05407418a0001340088000307040e00055807036828041000400c00200c680704490605500e8a0b10108078a0307140c1055661108428443d1003c01000200281c083c000c42c429030103c00c00701c14004104c50880c0448258a000e07a41000400340441c0c0440d015030050424214586080411480d42c0b0160958600c1e88111400d0745d481d00c030700d805061200c04044d07100545800e890441c18401640b40c0700781e14610140010b81410f68604c0400e966090210f1044080c000b000d0803503071210a28030f4020040156100040000c140480001c075096106008a80031580c0090003054801c03204481d40c025644080d0400c070551108100c0e5800207052800034200074011144000780444400040c0750912800a0454042122007580380340e40c130b130f00591083e0560b550f009180 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 485452904 1250 485451654 485451689
    0x71b0c051f170c04050d0c0602150f06091306020a080a060803090d080c0a08030705030402011206050d060e010209031009110f09040f030c06020309013908090c100c0c0b0301030804 79
    0x118640c401c64001782d403c1416800010300780044403400700c0c11540d00d80d0840d010f4603101a41620440419501d103403a84011401040071480c00c0c14805801104154800c075509160396906012684000d5008000c1981d5108001084280e48602c0c0024500c4002840c508035918000a10400003064024090607000c9030b44031540904000038040164814095682c9081400c00604260400c40b1b08070300241c1c140b000031034074500502529044850241c035040b01103c1c0c6035100805001d041660380100e6500748a00318496404020006030107280450001c0d00700b1305818a440b14604075400ca03405400e200d400320300f4a86030205e031180e0103500940d110160484a203012188954410b601502d8607001000340440008194403c80b070030000c9002c3c04945803c0034460162071800c80c010701c00c01642d84c141000348140a409100c0d8414090001c2c0c403040840840000c00401c6e0f020340d035000046d500c9803d041003240032090304000d001540c0c501030643d0302d16600e06a95114501541074514181c04a9 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 485454154 1250 485452904 485452921
    0xc0d0503090a1202160b0f030114181003260702010c081306080a050a050c09040b0f090f040516360609050901270308071b0c051f17 58
    0x41007402d82d0148010b403502c1006800203549071071002296480350410200090042d0818044030424580101c469045030701c0c0004c4039046640309940c1c0c030741008041010100d1048051f40b018030610041003040012815810719503070118032a1071003a08a4602e001c490341d000c289005449401703a091a11001c0c00c1c0721860075040c0e034000c0c4800c44e03c2e01a0603803c04031300b15801041051103440020000c111940d00c40384d0310019100c05075a01030f00600204038003450f505081d0085400d0b40360143c0845100509140400d51085046641700081a00402030000708113007840700c9a0400b22040d0159400c90a043e00403001149140e501428440407600c4840034000804080380103485500c0c08010a503a034110f547c010f484102c1d00755109501e002c8551140c0410400c0741800c010f111060511311030495a41520708420242500f800e004504d550f520807250101c049410f03a601c0f581c903960a551a000c107004908e25107003140810994100124045103038000c10454803186440e03418151070311404c10 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 485455404 1250 485454154 485454163
    0x2070332010606030504120206060a0905100302061b011407090909061103090a03080105010c0803060603040302190f03031508060a0b0a09060608010e011d070c11040207030c0b07050c0d050309 84
    0x1910040d500b041c0000403501e8040d81310b030b4840d500400615010b40d6555000301c0c0c03203000c01c0b548554021b0000c20f080c00a5050b0381e010640c44201110142050741e100e4001501300d820800c1e112480c160303400700c030b0301c0750660a004640035014101c0c5513051074206518060622400b600410044039a030f20300e04c2c020710035290400c02ca100d43c4505159540d05000d04415100c2c260b40000750045070f04400005115441a0b4216408681041e002419a01c07000100103040e40090410340031403080d11151522100c2d45801c0c16805c0c1e21907114514160418074001d01039850508841242c0f81d06060204204030010468541c040100d0000013002d49006c0d001489091a5800c03d0006519158000c034045411026160580300d1403480810075070f0b07844030402c0c103c00c04049002c0030041064040340c0307228029040c1641d000d1003817080302840360700900441c00701e811900d400d500154940c40c100c002d000c40c1180e441e03003080e2140f50840c41e1900712100955a00640c050541c10020000700254120ba030900 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 485456654 1250 485455404 485455493
    0x3072901142b02042403021e10080a0e03091309021503160801240f02030f030f01030b0f07091502071703090934032307020d020703 58
    0x2040d40100549015401c00d0403a240482280514601417150300d0100c01500342082030000c106818407041d06603400d00c40d0307003400f00c84004000041000703000c0d42c0c1e40c1c81c446261100c070213035554181d040c5402041d00b020b89180785044529038108101e400d40b65200e11a0708144003d0030500414042140d1000c0340f174681840d0380c50340780c5490100071b1200342034050180001010b071641c0c1e0b400350b42c3d0300da9203a402c600c11141d0300903140348031080c140000d2078011080c1d444c1c0486d441c01078070b0a1890382d0401440d568422a1401001d4007203500500410090560807500920300070382c0c85002e442e20007000760501c080f6000e401401c00415540054061003000b80c000034080d05c074191203425904e40b00302540c030781000c4030051003800c801000441c044518a100380908582d20b0200c80040c0200321800c0d02d0305e00321450541015256001207902109051b001420101160355001c0c06107401c140090030960144280000c5401800d03040001c02c02d00c18000c1020800c1c8014040c0030740c5881d009206284021 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 485457904 1250 485456654 485456689
    0x10302012a11010207050414010e0c0d02070807061b080f06030a050a050a060e0a03090e0c07050d2a020f09070e09010603060608010b121503030d0e0307290114 70
    0x10409404200c015540a0b026030802c0e0219501c4540702c0b0100405d94001e1400c003007040100c0001003020614507005590002d80c0084c0705071400c1030242c0300c035045c1ea01003042a145100001400800c1148620030b0099824444403080c02c44800702c140100002c6000d03101551544020012407000d5409100c1034004950000868201142c4ad103002501d07076402e001c059455600d003d0b80648110004030f41d018480758075648100505003040e496484260b0042c0141621403010701280b40051010010141000440c2c7c0341c4000c400e042c8941851500712900070380c40351161800c00c1c440142c59960081200c80411264040359540340c0008440c0340e2481700300075503c00300d00000021525015071012041e03840343c0d83d60090a03078031610104100e01c104003041000700c03081c00c0041c00c03c80550354040e03a20300c801030550340350800350b1000f00240c4209034450021a000050101e017000ba030010034002c084c040c0402d00e82080f9501802158089052040002400b294005a1103541c1d500e0400c28014289 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 485459154 1250 485457904 485457977
    0x7060f0f0e04021c0b030d080c0f0d090206162a0b0d200a020c0303090604150c12020c0109050a060804120309020301060e1f0305060106110a2109090903050301030201 73
    0x20b004c1c0030800b030a90b48400c10701034010178840e0394500f0310070703058203114020301410146040120010070000e0383c02400d807004166501c440e541c0040c0d03258030081c20052000c5000d011503d1050034224042503e0030414501c500801d41c00c8140403140e08400002c441d02081e000340c4900c1da004201e00504110419100b0b5a110001800d01e030842800142032481919400c4800040e0002c09065903413044260095000f901400100258000e450084081030020318007110400103a60f59801c8129842503400c0141e00000000700065905c0300e600c0c0e0060004442d2134140300d26046025006502c081e2014102c0c0e8040580f071900c5500030707000070f002c2c254050000c2103000d03942d099041400c1400c0c0d804117989030501f0340d40c581c000f5208646d00c0030307030350400007034071490340ba000003038981e201241d05c101494060014410041644c050301001d4114449540c1005180f402c20028003d0082d0380100307100310b1070022a0000721364040d0540c2d064940c20b08140180004414400395055041012951107042 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 485460404 1250 485459154 485459197
    0x9050f0a06020403140723030102090312090f0108011d1f0602211219140108060114030307080a08060604030605070905010e0409080d150509010e0907060f0f0e0402 72
    0x101c40c1e004004a0f8040e0003002d99040c0710b94502500c900851041c4180f20040250011041401403281d100c0720380d004000601d49090000801d04101241c000f0401070007001c0388074401c80c100140e41000030304091a181000c0e41c10409181c410707905041103e4007485136000010568200c000400c6018030442420381c1c01c50b030351604001d5458044240090340d03144480c000703500e554030003010380300340701d200c040d0000305640d40c0c2001813002203904c032800901c0d035200c41c035031800e001100e510203019040e800d0103090990305254106d544001000740181c0a903000300420004117040301d00380c6208890600d0316500035214800014014013131a080940b189262806201c3c1ca42d800103140000c44c1c0007a220589144009000c100460f0640c1401038000041007040d82204603841e404050500c1554640c42d80098170340001c1500044260092101400e0300000c2c04800e410802500000b04003600d0b1041e0904036001d0003c0a00f007045107001d081c0310740781c2c4c1c04408558881d010381d8040d000108141d0f92004 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 485461654 1250 485460404 485460413
    0xf0d0c03090c092007020d03120b3c10030c0c0c0b09010f030209010912170301030b0121031706041b20060103080a120b150307031802090a09050f0a 65
    0x3400e40c025005002c0b40d001031038204c14403042958900d503001403c564140c682610142c54108070300300c481c0c42c00c594440c0d51604d6551040c100d504550030443e00d0142400c01d40e0602c000361251080c061420a00804101c070a80c1c0c0c400c1c0060360561018075000c65070400d050070568104d07541000040c8500e4910502182c1e640c0000d01a00f0203107001da8489d41d01d182c0c5c1400940c00ca11400d2800b60002d901c181c0140018840e00c80e0170ba0070540308075580f040e0040807190400d0240c0084c0c00880f899243c0f00010003101340f008002d95000960a124112401d107959000392108018103100003908103840b0000e641603840d5400861401c49001c42103074001d000e1800104100320340c0b40c00d40303002c035114841204a8940001c896040c0c1e0f03400300c445440d2950040301560301500c20a03404026540300d02d00e0710156100c05405200040005550340c0d161300301881c01500b901d0784203d60341d41800c951130782d560250f03031600b91a42d000362080c200081d84a071030341401790400b00f1502c0ca644551091180060800 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 485462904 1250 485461654 485461661
    0x10020a0e03010c09081e0a1b15110601150c0c032402030f0f1305070e04060605060702031c260a0e0706050d0b1201230901020f0d0c03090c09 62
    0x10032045000300106104074900780c80b070a00f140500c06455000481190400a403107003000c0c001c0c84c00c0c0c02124880300003540d4446138418100760000f0405a032003420051520101ca0243c404011402d2004480180c80c01041d0f5807441407107551404075240d10610603060044907820105600702d40d0240000780c0780c0c2030911060145c01307505070030000d040d101c0202c004a1442500d003c0c0d4280c4000440742e441e400c0d290902584090010340c0c032990781213003d000040c030801007039000f000c203a40b0b80318880c03400342030038800c0759016030082e805824100300340300c01039401051003115050328203d2030014689070542124160340300741220010f00308150010384909150100c1c1da00c01c9544120601980b607260f0702240c0c90301611310400005c50f0041c45100c0c09201e40c0d4100c2b00c032007070700a41003900c50356000300002c0c20348072741c94055071820314184010a04042c1d1580440d9104d408000250301d05207501c28603580034424034405800003503503000310b444024480d82040c0c40b82070b040240e9002064a03480c0d01c0004 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 485464154 1250 485462904 485462927
    0xc0a02040b060d14041e020315040305090604090b3d050c0a1a09030a090303050306130f05060102010b0105040803040308070204090f1a011203080415060f080c010e03191410020a 78
    0x102e001d07207031030f03803c5540b06d6402c1a000c0c96014002d02001d401003040d91256a802a00440a0140a00c9003c1c2c40d5250070020388001d190300740b0302250481000041c070855030240309441c03420590602039048240c80c4000b182684070b100325610851008219421035403130090565060b03160084680003070074000076880075403010361001e11058040c0ca60350301142c0e4030b211300300f100d20114119200810100303000304095540808083e225900764884104050704450580c849011400e0b03640c1e05001080d682440342e52480d400a091040c074040c2488035840d079a01540c48010a4000c00295070030464a458002c0101181c5c0058a01e803402c1403450032035034880f07200b080035aa8082035800080d10b40101010202c1c0d05805449100c2c441c2c8680c1c0300c110682c44061310421069858541c00500c4440d9a40d10000130000c0030041c0c40c07154800000140603403c0c00c28458801e0f408541c105a454a5025503104100e81c082e201d00c00f800d040d141c05500b00307100c44c0b0000c0ca40303503c04a20403003041e40060782500ca = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 485465404 1250 485464154 485464163
    0x121305030c011e060e2701050708090c030d0806100201140709050910050a03030509180403051306030209130c0c0519020f030a0308070315050a0306021207050c0a02040b060d1404 78
    0x1070900300000c0c0c1d08111002071040ca80605c15040104101d240d1050860300c140c0708182207080f94254840c4181d080d500e042c0d40400000307410004222161200303000c5252804001c90241c4103584103540000c21448010b0b241c184101000400200700a00035400030700f00b100c407144400140c0c9130200340940803404610945004d4542007000440d0300035039042040c16254001c0108410a0454800b1101c60b0001d808032a0400c511100b0184249400c402c9103215034403d5486647e80d0702c91400e20000e034105944042c081c54010b01c450b0171542d030380e6102d08086144103e800903200c0c00c5090101e400303507040c203009007142c0288598070300e0307001c0c813402030449a03070094641199201003082490383d1031003810302c00382c0000c0c00301d00172030910781c4a81c001c040400e05140c0302003641e0391100009815540c0a500c122820b6600185804420240e924016440310041c24507030b05111490019584401c00d4500091040d41e031481d0181d030959407c010b41d0849100004100207410101c801080d480b18150b900340c4 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 485466654 1250 485465404 485465441
    0xc0605280923031606140a0306090905010e010b0d051903020115180c09060516111302090406080a08030109090305040f0909051005060f0d0f0203010e0706140906121305030c01 77
    0x1201584050740c42c00485595568a54100e446d840c1050400d030045030680d4101501c0b4100080c0d4000f45008800900740107400004110409413007407401c458910f5401801050603242031008200c000c240c1d50490000f10b03c00c410050311900d400c900428500e90a100801c0d0b0803000803c03280081140c000840c51803080810807010280c8040e101d04d0101c1c41000b0000f041041030444065850644400091041c6020b032080c449034000648101c0c400c2400b000b08983c0030903040c90919081c084c0c076005020480291030540c503151601c08451105002d001f007282d4440c00a80c00301440f54045600404840d02070481c51515000400003030402c0d5a4243c80c0c62182490000e07880446110305802160002e0400c1d2058003060140005004050b8081c0c3c1c111300202403100158900b8001c0300b129a100320041c00c40641010b034043d200d8000d200c080c2654240610115807140c99a008076803d030b03d59003d0704c0400307940780c0b0700340d6a010480d0325008003d8040818003066081c015003240300407000300103040 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 485467904 1250 485466654 485466673
    0x50f0904020318161511010608060a09110603100323010c0c05060907060f18030c0f0305070e040b0c03250801080f011b030203040f060908070c060528092303 69
    0x7444003038401e00400e080d02c2a807442c017a01c1a8012444142200d0084001145065480b1102030400300110351220784103032102e8400d810459601040001311900300d6000313056040000d0301a0860409000081c452410a034801c1c1c3d04070650521794010581241c000d000c1898185c40080c035850b00300204403034600c200d6000c11880007001c5004015941c1e25070380d440703080c20010402c9515521400c7d81600c400013280c00480403441c4540030b09d018106030f601e0902540d245150032850010305502c11800c6820b80b5051000090b42d40e034416030010f40040701d41d504ca842c0c400b02c90071903070000e00300340c0030b94500f460307001d003d094101c450079048540e8142616001d808441505084c0c1c4c480347c0d503030387c441200b00711001c0449010354003454006004210750a07507840d00f80c0d100403c40d881040280d0b800e4101054400c2002680c49040c400342c1224a0564205440001e002142c801c2044010f10200c22040030a901e540c8a90300074001010440b140b2a06080000400300b03c0045071102e850080c01098600c = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 485469154 1250 485467904 485467933
    0x1b170a030509010b010e090604020c0105090303011509140f04020d02190f0c02010c020409030302090904030c0b07031e0e21121510052208100605041a01050f0904020318 74
    0x50000130382041e1500381004110b01c007045591007006103401d9009034240840048a2402d200d545d200d80b0000c00195900d5043c5104c000501803003090007010401d17280414403100f000c646200c94001806c0d600f8540c010130404c0000c01a02444814401b00c52000c1345044140460950140080c8003e803200c00d001d22150408680201000c04003a001c80c00121042c4010304060344144000b90080c9001802d0100c00000611b919005075405d500180d19a8900c5091090b682526a040402800d00b0081050f4151507400107850403560120140d684940f1a51241803c3c4240c5604005000e00415078600700d08013900d02d500400c0380c58080b030f41c0d0300002404031800d45036044a50540103201c42510800e142c801c07034007984084541c00d9449540c86245034000b04141e01c0001601010002c1c1c02002c3e00b80c0d040c41c0881e00280d11242c895401c20007502071060b00324080315007425083c603012303a030740c000581d0000e118440e4041c8190003510010070081c20000b0f03644040d507451494419a41914a400503 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 485470404 1250 485469154 485469161
    0x5040e150105040b0d11180103080c15060d0303090c030501061707050a050904080a0315090203240105040b090a1d0402010f030e0709051515090a06020f0705011b170a03050901 77
    0x4071500700171410b11040100301228221104094001d188407030600c10070919000044080c0c0c02154000030100d0080b001d110244410304031003c0c440300d09505840c01c0400285620081540074041c580d503140d02005120b0b0318560b00e006550000020322805070303108000d0795055a0f03005521401c1c000c00c1c501080b40d01d031000403801100c000910060040c2c845449406095010001d81000d02d031b42c802910300d0504840c0c3c3c0003401400d9120005840b4508114503142009401e42c0c024407000c2c5080c0d9540c0180c0e08002030390180c60308002c540d503c1e0030003000406ea81d00095000100208041c100e1450040311030008148218400c0c2d86440070901c110505070180e0340e200c8188000380d0401c0a007804240d840358491640300f010101501c0a080c01000810b154000040503582104400a011200343c10701d4082d04004111030300c000c1196a103100c130296140c04150144904002d00b50f0700b50703c00e100e0b0450301c4a00040c0c0000c04440c0c0c401c0d0020301c402969100c4160500403c0c2000d00040740c841041c803 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 485471654 1250 485470404 485470421
    0x50904050a110612070305060f0103090f0b0703140c0706061d060f0607081201030302160e0c0a2a0c120506040b181501142b020a05040e15010504 64
    0x40081110401c59500c1d150031100c550700c243e8000200b0b00c80e0041403020b0b10184c03400788100c1c1c0c030005001d01300601408440005003030341074141410024004d0004440f0841c1124160700811655015184c400040f00038040700d1003100e01c40200c03442481020b020001c01000d49600c10281000599a03034100c0c0c098014400303601c2070710203070140001030f100c0c00c1c800c4021003125001010285448259626401e06801111111280c0900c03c40107104260b010800c101c50040c3e0700e5001c44090b0303e40a4420900d038001005500c6141c00803400103540e60281c082410b00300404c00a020700c014040110404003007114509440d860181c0304005241d4401c0c042d4041800d4100700a807055a48035101d4580e4410040d1030741d41e840c3c210708801d801404040c00b400c81703011702d001d00d107030501e500d007101400481600043d424400d500c8001c0d240906941130080c2c1c0c90106181c15408007101081c000030300310384040d07806590041e08201035000d107028040390302441982e80410401260340c82d2000d1004556824 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 485472904 1250 485471654 485471663
    0xa0b18010b210a1712330f0a0803030a0605190b0a0c08030c0a080108010b0306071103090603070f032a0309020a0504061401200d0c080c0d09050a050904 67
    0x42c1084248040c030356180403980b00e8950803a01d050515a0343c0f1a03441040b43c0c090058514003255403c0c0108513910042c0d0444038100c4151551030710082c42c18244003440714014410032440d440c2c1c030016100c03500301d15004c61008180020b0705a58002090b100d03402140d080e04030601d0698081614500024008080082d200c03403400a1401c0913507500d010741c04203000d001804980020395000910000086229000c2c6001c520b40303d811600e40034000e1401a003143d0403603410701c80c1d01c0600391400100581d201106141100e40000d13200c00403400e520031102202e030410800002c0000d42c07504440c090380c098040e641c08003d40c09045d00c17a11400d041500d2584030b450308811200d094244250004c025490004002604040d0303281c00081c00c6400d01d5112840d6074406500100c0d0640e00083c42c80a003044250f5415414201e5110480d260300710481d4920030b101e21a078422050010740c1c000d03285480e66200c1290503403090b08602802e0003d05200300c82c403444540c540880c09042c41c9c0d2803c2d0155030300 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 485474154 1250 485472904 485472919
    0x1b0d0305160306031a0903090a06120608070b0f0f1c050402100f0207090b06040b04030b040507060c080a05030c0706020d060509010f030b1302010216060804150902060909040c05030a0b18010b 84
    0x880e10b05c0c901c029000b4110340300b40c0c1700a10014500b51740d074488850050005488500c2802d059003821016203060740e0101410350004502086400810341c03c441c4006420b460741030361000360b40204100740c018070404446103260181c042e4000e80316584040d002d207008035080c0c80c10303181d03c1400b280c0b8071280c0803840d0016007000c0402c0281c41901c0d0000304030002c008100500749600c0791420002900280e1080e85e00000400a22041c000c052201002400e224036000c84404c02d6610ba440a62103241e94040c10010000001680c0d000480113491000d940907030190b66401200302c4c198080c00c124081c051162055200015000d403811841c082200c1d4051001c1400da07072421410744610600d154186e06501504565031488202003860201804444d1244546824142495007034001e00361060000d2906d060441070142e640d01080e140007a404a41e110000d542e076180003605030300da40d4001c94152143d060100100503004204900c2411890f9524a2007481102c1030b40c2070380c25208031541c200d0319 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 485475404 1250 485474154 485474183
    0x15050117070e030307030909060501020303091509010f0f0c0f180e09070902070b091207030905220501080c0312091503070203130f080c0d0c0b1b0d030516030603 71
    0x115510305030700051078241040c010040750086400d503840090101e0010359124800e01241e03485201d008042c16003880203504504c3c0515001e545c0f080e84c0303060320340c07032612202c001018540300350407154044030010401c0c464540b41c0c403440740217440c0030109000400e810318820307000c4920410b02501d00540301d0b4504180c0c94078107a0321901020300503010b14118012180085a40c01716800140380d00c62140c2c008a66502c3c11012403401e0680748030300c0d450340e032404021b41004258018401d5054400403206c3c1e01c0300d40000450760256610000348a0203850514000041d10030002c00e42081002c003d400790386811259081c1c200b118400d00714241ea100101c1504507000b81510000313198881e849004403850941c8406807d058074942c1c0d8088415804401b000b4424080107101e42d90003441c0c142c07248880f4a01964500403500b2150040030316416000c0780762018020102000020300c00c0c40e5003a500500307000e113001409414121140300c801c801c07014044003414881c0c410b1100322a0880800c525029 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 485476654 1250 485475404 485475437
    0x140412060b060313030917030406050a030207050a080405040b0a0308030a0506010c1a010312030c081501120204090204030c050303210c07060513060507032c07080a0312150501 77
    0x18112056034016560680001c454403030200030341c054451802d08564003269450b004242c08a10b4000074004101d4420120340030000009603030641b440d90170314a843d4070208200328000d004064025040e0300c160305045c0300b4071500600400c19100c0a5405121001e91002405410701187c40000d12005c4100300048810482e9030095400110500d01400351807280c0e2213001d4410540c1142078002004003004004200d81c98035402d00780b410702d04040c80741a1001001407e8548000c00c50002c03102002001013140c4c0c400c1c022510f081003103c604540342d41e02d9a0040000350001e00040f60804000342c1c000c03445190000a5a04807da680301c0810400c40c0e40000800c100000b403ca5903040100b4068036002a2490144a1061018060a5440c00943c0c1800c405443c009001c250070305180a4400b00c61101078440813950f40f100702d030300e080c0100c1040c60312868140294804065400358102034003c03d0392240c0a03508a00c4442c0040c84429204021004800c01c40c0c401d09010500ca05003111b03120 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 485477904 1250 485476654 485476679
    0xb0f1917011a280e0601021e030315060405060a030f05010602070302060a030b041116031e1403090f07081f0204050d0308040c030b090102360603090709020d0b010f1404 74
    0x10a2240704005881a030f101c4281039403d5141c01000c03070300c2d0341d00301001480c1d64104115290300040d03800300c5500d0341192048613143d01c0040e0501a420409804404280d1909002c031030090002a060703070b40e145800c800080040110403080c2082e1400c113400003c20074030002d21a020391740c0040103036140810240f001d400400034006d01c20382064589101200c2402a03c028050103013811011001c02c03450741c58010304040303a43d0700000024452036004403642d940300f00601610248a00415960f0b2102c006003858943c140000150901c030322000890412000b080f110481c890180d40344c2c4583c082c140d10301c0140e008030301419400c80810340c0c40e030010030300c940746c080c0e000b42c00399101e4111980c980c1c0712007400c26811205a03d49030b400040840d141001c1b159840d554000d113500e04d200140f141c0b4484080207421418092144c21f000c00410030300c203400c1c000309000348000c0c0e20442d40d540380e9039113990107441c030103a0280c042141d580d41f1101a03405080c001c0c1d50300e42d10200030f80c079141c01c1c5030702e04021 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 485479154 1250 485477904 485477929
    0x5060a0518070e030a080c010b152d0d091a1504051905040323040b0702040203060109150f03050106021c2001090c170d0507060b0f1917011a 62
    0x200f040c51982441e682c0c9061040d0061a4003d070340f000c0e6201c40301e90740d8500b5550089001d602400001d2110150b440d0a18281e07005584a504200e082c240c4541c0e0320a40c00c2504030601200c3d4000084402c120b100702e521900c1400c0c415482c19103e20180c03040091a1785084803e00d60307180952003202e00f00c0c82c0c25800b40390700080c2e50741c0c0721001d084102c00420407a6001c035800c80125048400f101d41e250503540455980b50031081080b86040d0403c8014141c5010b4800028001d540201c003042c29a80202e0040015003586039484440c0f0990100c000e24018034281c509001c24075220001ca552440440d40301031a004461000d4480c40c40b0f00022503500c640d002030407000c0c090200380c407000000c0030700402c5007280c00313007120b9402c0030f0a00a40e009403400d00715904000d43d100f88a1101c0d01604541602c1e8299000640003030704039440000700d040750500082c207030b900614014542e40c0c0c0410300700004080d1005a083c10700d00c4101114094200c5440402000b08600c103007503106103d281c03071b2210806 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 485480404 1250 485479154 485479157
    0xc14012d0c0f080c0d0801090204050303090402090d05030a03091104060302181911030105040c08130b0c04030209010b07120318080c03040b03090a03030e010203060a120c0503060702070905060a051807 88
    0x2140107040c1c9070603050f6013041c040c2c1004d9801642c1050104c660001c1101d01500c07691100f10315280c40e020000f9645d03c15029954080c0c1e80110306280c00341c1e50842c21186068008040d00d548840d0444014000c008086044400d4403660082100c1c900f400e21440081c1da80c0035003546400700d429031001c0640c540042c41d0615400c0460121008201140140c0d0030420381700070019120350400041200791074201503038a01b080a488100000c00700101c3c00541510380001b41984113880c0c203000c4000c0c1d48140c0e000a5004080c1400001c0c5544010000340801c6000d810700e10049443c08000720141c4003180c20075441045146032540205007100000c02045910808980c502036540305c1408403600700700c1e00f1841c0390700b1600004c401c0c150103000b03000c1c0c1200f62400851541c6001800202c82060303078058200c21282c001206002c0040f510640c80180000404a6400c3c0c9407414000390f5901d0b084c0100101c10b0304000100740641000c840203030660380b0003030810b8040143c0041184984100401000 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 485481654 1250 485480404 485480423
    0x2115030b0106302406020a02090115050405010513030f23160519030b04110111211c0f0203090c010206090d0c0c0b040603090c17100c05070c14012d0c 66
    0x144d805140c01050020290b81d00508001e4015004100110a05910115010010b80800b510150b4441c0c01c0350141c0d0024207020352a410000c00c4148521000c1e00014505d06400000c203083c020070054810407040b04d0380203e04400a51807040d5127980101b03004603c80039004800b44401d11300003000e4a11302002214560425549444943d9014810707a01603400d885241c2d51042176591080c400c030120000d0000030b01e040c2c141545400b98050b0100751812901030041201c1c2598081c00c0c046034200c0c06084002e10140382c045885034003d50099030141064450940584082d5001007812480350046030301502e034468000c002038079000341c502c0e011168200e0301c030004240d00c0002c40c06400900910741d00013a4080403854001d0302d0081c1600030f43d2601071171000310b0003000d000150000041180d1407003c5a030281c89a419500c2d4060714900801400c070000011411340b11080158612081c240c1e550003180c0038009400c4100380403005252100c04d04040000c0c801b600580006103d80e2040e16100c = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 485482904 1250 485481654 485481701
    0x1d0a030305130501150801140108150a33090b0306010e0406060b0c1006050f100309051c11010f02090a0911040b03070e1f2115030b010630 61
    0xd40c2100c021140c0f60b4101c0c00d00d1711003440420824030400c010712a900c01d101d84030354104880d140d030b109415042000038100c07880010b0804101604883e80364109420b60700415401108071f03400400303180041d101446807400c4009140c60080c00f80f4180c2d1000600a01926400c00c04031407441040100240d42c200d8842100141c165802c00040000c3c184060191183e0003503001280c1c19200700d0f80c0070500c54104440802c031103179940c61000b08090240d0078005640c0d4010b01d03110f0b060004894486e0201c0500c218607601e0b00b900030318102451241c0c00000c1090000d80a02c0d5803c034011040003d4202d8141e0340c050154101036440080d0b05140c41e0682030410399905c0c80c60060b9402120703d0000101030140b040024108003103010342d1075801e2084540c1c4451405402081d40520280001010006c203c031303d03481550072790100401c51440d400314228252030f0f041a000311030080c819807002503084440484040c444003c0034404481580d1401103045028001e0800350050742d0300c4010242032403101 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 485484154 1250 485482904 485482913
    0x506070305012303240a06093809010b070303110a05071707060203040c14040605060a201603150501060e0d03050d060807090c0c0b070f1211030a1d0a03030513 70
    0x2041c10220180c00c0d05e11185400c3e0518400d03200b66500518403c0d082c0303000346041c510f40b6140c0d420217885039000e52040219003e60300c0400b0b00c002c4200740d00440d030500081230058094000b000c045020782c90a11408208804202042c8649003098001500a00003040025050300101d0118030900c041b00b41403000d070361108401c1fa0b00c181e03030458030a00c0719482080701118600007041c58100032070341040b500c1c0c5848003059a9109801034a0208484003420300d00c0d000d1814603103034200040c1d2049074082e200f450342100310308100c1d01003a18044050b0000207103c0825003d141e043c1d0705540d80d2481d40003020b005201410750542412400c1c001c0620030310350801c10f03e00c280802014810020a52240382c040c5110864044120030070800c4114125000803030300c003140781504010700c1d140c038000b51750a44400b140c560301240b5103100c1040c202040f0160407880720025600a4841d42002c0100050210300c02001e0700300343c15a0310064110b8070041020901a0380301980c0203c00485601c04200709544 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 485485404 1250 485484154 485484193
    0x3050c070e0106091e14032a0103060806010b09061b0f070e0603030a05030615070f030e09010b190f1e020a1a0c0403060c030b06030901090506070305012303 69
    0x10000c10551940300400203203504c46610720082c201c056403506891010b100701400541d00d0300030755500790742e0700305082a2920304210b0240192030303850300e0384d080c01440c134819181c1c4044138010700e002906000300414122000300b5124100d40f102202c0c60f00c4c0000643c1842229041102a000103407210100c000c0000000d003d0f403050310500e5805840c810b800d00c24682d00340200030f403881d8041d500074403480b12001d0300001200d1300880304842c2401c01115501c0c2000c91417180c1100240b40d241a0b56140040581192407040004400c407080d0070540e0300e900301009140503100c0d02001c1c0c80816444032200601a88000f1b2458440e07161032101030f0b600701608400001400d18400043e440038101d01f0a0040c00807040c11000080c000040306c1742000b900d102e019004a00000d000e1070b50382c0f004859503d0080e400280b06030405080d151300c1e850030741d03103941c000c00100200740c449021301e100044809200b880703102d050303614082c8101c12640041c01c40d24080c0b114a0002ca4051042c240300d59a0140043d0 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 485486654 1250 485485404 485485409
    0x60c0d0f0c29070315051e04020a05030a0b061c050619062d17131e02030c030c010530010f150203160b0a0f0603050105010611030310030f03050c07 65
    0x41c03005060b03004040d00c101c0302e5803004010b002014505440c4107240d90400800c0707412180101e403602d090104950086104507001185550700c91710000e101d80e40c564210025510501e081402080b11009a5040c0300f2030b44111000c4064014003020100c802c000d55038040c40c0c02c0176002e011480c041030418802d2222640980206002c1103a403181029503005084070f078031040e105036212088a0078240c40150980e548a84507219149041c03001961003001040c1c124013141c0c120000c009003680c1c0322042420b02641c03110a80c02405005840c0c940e0b4100010640b5682c0c0c0103030344a40ca440301000c492240c10040c0541c500f07044a10384840c040031602542a10b003e01003c00000e00c9013440d00000071103804407a40c44000b950000d000031107200d90a0100d0702261784d08910081050307500c1c0102403005121980300600420700e017079008400d2180c1540182e043c0d5046880b0140201c5d00d01c3ca00c10307540c1c00119040410078610100c01d0000401001000b181c0621030700f00a4201101070011038104071484c2c = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 485487904 1250 485486654 485486693
    0x150503040b131403030a0c11030405060304080c0d09050a0801091109100302120d031d0703060515030d020a05070f0e0a0906090c080a1106190e0a1d06040605060c0d0f0c 74
    0x2100340600070b0011f20800c0521906420070111501903402e0045c0c1f04d000300e1241078811600480010103001c46002101d5820b0740180540c0c1c02520121809010740c0c00c03501845000f0301900e003021070301000504c6124040b90300140300780044042d0300d080058000e4014210005038603c15000001616800c0c6120311100200300a070181c1600b594008040f40e08555045090f0380140444803072001c1d0100340714064a80020020070a566007141412400f4904007002c0c0d0940700c0c1015421503194082000300d9201d1244003581c2401e80d4501c1584154203583c0503400311030307420308040b03100000340d0750105204510408001c61011703850b8440041a070000d50000c452600103c58400c204202c0034a01207100608031221707418405580505409034500032122010700942c01c8020750b0700d5444115601c020810700c600400f40c2058800d410760f500740c1c240c0c3c1550080b82082804030f5240b4201c8140e5942c3c0c07001c2d50050000548100c1d0840341103041c2440101480820502c1d900410740e01d80b0b0a03040c000d80c2 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 485489154 1250 485487904 485487907
    0x10080309101e050d0c0203070213050406090b180f0715050706110417010c14030a0b0112050709090516020c15090603010b0909060103090203070b0a090905090115150503040b131403 79
    0x8851481305a82c41c3c0c40201c001c5400821030100183d4500310034845072560b4000016180d5141c1ca404c900800720a40003801554002d0100721707190a01070300c00800c41c4100c10588000210448105507141014062810204c645915501620b0311800c050001356001c3c12011032804c80e460000b41c0103074031540200c441e03040403890750704000d1400d0003540b00301d4030365241449084400100035001400040d180b00c0c5541d4460b0307200400c0d03a10400e094001900750420820040c10b04103409420441140704041c03242d03003040000781c0a01d0205406c040b641145402404d4004034600070840b58030185090800700300001d200610244d259940a180038000c03040d8419a1032102c0800c00c07002ca130004015904060804418400503140880c407082151060aa440e03220351100c034007529501701030382140c2c0191385888100846040c0c150807405006072891100c140e11a21184a002056100c000d440041202000418005100f014101d50311046036007401c1540307603280d030b0750001040c01400c070100c06910 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 485490404 1250 485489154 485489167
    0x1020f04080312070503040c050f040912080928110a09150504060e04020d1511030a450305070203060a050109180c030f020301230a0510080309101e05 66
    0x84400d03c840d004092401c141c0d0446c6025a2691110000b0f400740c18024110003410b2040d0362200d41140700640d601240400303011000c54070090801c10212101351040c80748000494100c5d020f0f0002460504108580c207440c65059144c10f00b440c0500f000e115004103103100f0020702c0d14054840d403014180c04580401c0094602801c01c0180c804a4020fa200901c2c020248401a606c0400e200c104640c843e0703148058010f0b0914180050404c17240e0640440000000c004881c40c55910a0310070101035008102500301302c1200c1007040140c550580c0300b0168040d241d200441721004020343c1c00c0c2c880d00c1c1107460214243c0c0480c1c1090720540c1e440088580382d0005220101d228010502c1c136540c1051910224042912107161000040c40041c00340004e00131658195182900221805c4951622181487c91a030580f90507540341290104025480d00010903e0002c4c050388800c22900410002c6080a00da4400c009440d41d03440300070014083c0c071342c3d900410b000003000414241c41e000d44070192102c0 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 485491654 1250 485490404 485490427
    0x5060408130608060f0919090f05060f06090a0905190813080c010c0308061305070c050d0503010f140d141f0c05160501020f120403020d02060103031b030201020f040803 74
    0x71126003291050040c000d0070040f0035150250180b20b41340c0c0c00c40307980450351510a042030503071217144071101969040207000810f10452a282840d036078443c1003100c001d80d031000440141907100f0307a0309a5022440401081d400070454011030042c50058081d00c0c2800d20150707140100340c0c0b140703a04440d658000b05520a03510402c1000700020724000018000c000c024000090040381000700007403c0c811808089840e0313072554040c182c4281520041002242005035007e840210944001c940a2180c54092001d140c440c7c402e482c100c90410400021640c18512140350348000c41c00f40c6030300072030024a40d901103044a4010b401d0070b00004060301c481c0e48000989d05590b492812007507402418804041d405540c444c0454414014076035404240007400e1030002d02a101e42c5140024440e404120014900d108140c4180154484e80031100076a01d2103109030307214902480040c02080130800440d85040040680c15246842407000510f889181c00c24103401e600150040c13806c0d035001044004410 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 485492904 1250 485491654 485491687
    0xa0e0301090b070806030f0d11010209040e03071205040f05121507031e050c0a0807020703080a02010506120f1005070203040806010e01050108070206010e071d06070f0c060311071e05060408 83
    0x5c405801400038943d01020007aa5224004550310030002e40740e9031510012801c6d4191806084010801e0020b840d420311604d030f5940001c802a0340e080070241e0604102ca0140c811241100c40100c0e00c481e03418506005c0002013007000110b04514051030079208072601c2040da099100706851780700000c904c9044000d014288041503204148903281c941441951200c807400d42d03460281900d0041180d42d20003030224105809544014001940810300400207501900074078440c1d1029140004150300e1481c0c0d007036643c40d031105e0a5160f0b81220b0741c01181c401c07554000c0d60384440a8012a481c00340d0b104000d80c90070409910101d4001c45150043c862503a121403800e4014136144000c29095050800e1800c880d44090111401e01000c4003820020402c0d201e4107484c0300b003000b80041d884070342a0070480002400c048089035244071100e000700d2464080e108003c03440000e03241c0e0301e007000b4072955244100003003c801d5040a0898111030700010390100300c0181b04600c2500150b8803108058085a410f = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 485494154 1250 485492904 485492911
    0x504120906021203042618012a06090303020c0d08041515060806180c0901140414120109050106120b06150f07030e03060106030c080105030309060405060a0e0301090b0708 75
    0x1c5400c44441d001203c211402a0703a0855000502d0440d28440c0e801c02160800414034840b0050f00c4c00300c0d6104404070002e2103000c6c040401e8031a2280c40f40b82140545505020107401844040c0e01c509034404696150b000294203031180c14014901502c10003017a2900000041e03d10001e0790040821042004a90001c104144195814845002c4d04602400900054041c071410130100c080041d4075940d079903842415030740b0b100d254420281010f910f06c075000e80c041c1d40c42d9070200380000782c100c066150300c408a60841d610320159045c001003180c100003044c003014150b003104d5900c4000840c003083c3d080c480c6200400c1034041100d40e80c212450406051344009000a00c07590544002c20045400e060844032003c0301c01c4000350b41e425281c58140ea00d030040b0490355030180700f10b00010a07800d4142d84243c0480b000c680f141c10707148c1c0c1d17108101581d0b80701e040c9099401c403109200030801ea0601d040680711003603040c20401d800c0b54a0001080c2159002c0380d040d10200e5800050100c0640c2101c0300680 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 485495404 1250 485494154 485494157
    0x41503020f04182402030a0516021605040e070e070315170a020f012003131e050613030b0411090108030c0a021e0a03210503040c12080d0504120906 65
    0x740640f42d0600074071000da4440060001d5561008100d51142002d0042c010880e501e20110744900701904900014601100c80801c01181c003000400e100c1d000080c140d002c2d601c4c101c0e219040f1170a040038840540b40b0903012683e180300e001c0d00816089403d901c0648911000d5800090358521100310504d0382c02c955110b180784e102d03416060940070b80003107110350000c0d40554000700c02c40d05010040b1200d001002c10808581d602040d0b090900002000038000003981d01842c420558589102d140d80c80c2602c1400c0305c14100b400740411480c02e00c0e1000d40103035035000c203005001541c1da80310380c0c4240004480841d01700000c02c40d0b201141c604289168003512108005504180e03016405582c0e0305041103002e8820111106900c0c12455803c03005151080c000d440e0558456aa02d00b1110100390300c661604d5904000c2c030031144191045058078440c6420140e0300200510f0011010512102c107007041d12560700802c02621a01c0e080d00501c1e01070b41c8100000d00920204440080c0204280d400240 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 485496654 1250 485495404 485495411
    0x6011e05060705070302101b03031b020706020703020d0515150102070e04051915020f120603060c0a0c060f0c020f010f020f1206061b0304090c0e0a0603051005041503020f04 76
    0x100403d50000e49141942c1c1d06660380d81e6500721b19982951529108680ba401c0c540030415680b040540c580c00504562035480b6441c000150302c0e680990312003808d40201e40050740051020405031802001d10350166002d070090381d03014070710840b0308004084e08840b0408910050802d00c00705580c1001001d0003400d6201c40c004c4141002e03500c0f81d88501c03100c007011070300700ca03030744484ae05101160701e21408000e069401150340d001c00701404482038200018034804040c01d000000e4140c2408035840e4444c200040b02107160810784601921007061110055074082e50701d0500c28643c82662240c80c140d0480303078000300340c8008060945800d40742e46107980701c41e20b80103000750140c3c03501150940c0c5240c0c040340d102c420507540711030106403a8011408026089901c400108820b0350001c40100203442c0880d03c20300103d0b4030420b0603600c000820384107940156042c0d0b003c1004a01c203030300250300904400c1900e440c0c1503840b000282941c007107400140144074842420002c501e004121103a21a00a45050 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 485497904 1250 485496654 485496667
    0x30b1b1c0207110604181803020d05030403120614090a06060e0f01030b270903041401110a0203060708090f0610030201050307021908071406090a061107020306011e0506 74
    0x5900d00e2420400445200c0d0041802020007504904243e00c1c000c000d0a443d84540d950184500c203041e14074408403601e407402c030222410320000d010080c0101d0b0141c005010504c09440100d034203a10081041c0e0420400c0303a404851048507004490082c81202c2a40362182e407040208200450301524000d142c42c5401c004221094201d82c0f042111300c421201c2100c1d0004000c0180e010b442c2461030399074009034001d003110380402c03c40c0301c81104c1100199584c2131559440c40d12070b07407440399014a0f40c1c480c4076480314019a42c403801c1c04805103034102058820804181d408a450568203680040100d01000204000d22071f0801070846507800c404000c003200d052074158a10742c884035002c064100a00080084d440071700800c00f05100900b408000401e900c240d082400580c1c002d00000c8030b99102000c041c00002c440055681c2c02101c00700d01802402c0b0303469664074003c04002d40301c00100c2030305000010150341c0900540f8024261401141c3c0c2c070702d40d2105114600101a0443e1780300c0e50042c00807 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 485499154 1250 485497904 485497927
    0x1020315030307170d020714030a201b0406080318010206070306051822150b04110d0510150305091603030206041b0302220b0603060d06180c030b1b 65
    0x28135015024a2076584603039007102d0b800a0300c07540c5030141201d40020411860701100100800c0c000c1c215a60301618410340c0c01807082040d06648140f08568840d100051312211204100098040c000304005002941c42103894110740055442900700c140c008100522560180115640850341c3d03c0c003045040c2c2043c0000b02e5031120302c0a42d004019000001600688001e580484c1c524030443d0808103806903031400c00c6500348614070054850341041c90948040c02c0c2401800074144d010340229080c011120001c0001303002c014460300304606140b10004549600c070240b80302d491102c1da40880e007468440035880c6800e000c02005812031511180c02c0020a0380400e1031600203910a074840604491002c014000c42080c1d0006540b1030340c0000d242d960710172090103620b8001d1140c001032003044400b01c10041c070350000301e6649812071090540c40001800310380c441c8800e03400310741103124620750703940304d840e268104c07a00215016001b45007800b0648184070350409500c0d0300400c07440d1502980243c03 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 485500404 1250 485499154 485499173
    0x90a0308091807120f0204080a05071802091c05070509180f0c010516030e061204050d0f090b071b08060f010e0c091507021905120304030c120c030c0801020315030307 73
    0x86015003036585d01c0124140c0355160100c5000b0030702141203410003441410003d890b20606d20880c14411020712806800c04100d000b0703209c0c07c150003481030701000c1c040341250b010361001810844542c040c050b8081002d50f03070039004a0144122010354401d408000810914100000c41c507083c3c1c036031101c80d69a02d103a9101d421190012883c0d0f8200e00c0315540343c0b030161085c6c4402c001c219803141c0d0206058840c0705419450a00c601d00070011562050400714040d00c01920882043c40001d80058041c016618075800804810348074180b00e41c108081d0030102910895642c001d406143c006500780826030700708074440340c050f0802c1404045a810195001a0300740303e903a01281c0180304980c41ca110600007502a91141d41c0c002e04032003034803031074402220304400d404c0c080d1030320540f000070031000080307800420381d000c1c0e907406811100018200505682d040242500450740c0c842002c0000c030009000c82500c2c8020520a400940c070ba05007010210719111040b220b41d4007079801484510301081170240d = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 485501654 1250 485500404 485500427
    0x20102031003020f0a12030c030f0c0515090309040510032f100c02041a040612081806040510031b03020c0a020f0303090d03090e010501050309060a0c05090a0308091807 74
    0xc40d01ea910220110205101e01081c1d8408150400c01d451038a081c150403010235400301d4030940e01c445010881c09001d0310300c07044001000e0030a0384020031a925280d031100c4a01e4100744c00d03100302d83c02d2851040000c1c0540c0e070111002c080c9a40f40c60010030421450145051b100d00705000c2c007034403822100b0100b00500d800510340500c10003610503d01203007405440c0740404150060000d020720443d240d210210100300c2c208590140d841c2420001d840b145c10303440789111395444480c0618080d001c10130302c508000d40c40304c503d5200030100000111661880e000741c4c030808c441c1e200860a007101c40c10141da460700e5040b45109050040100f03030810a800704440e00c0555045540c044102c00c02c0020910314068411100c0d0007090107801b51061580098403441190a05242840541c1e01c400044a890100380c0c1c04c5c00d41940302e070b004a41d40303280030340000c20401c055151007410a840c250010b09941c00640c403c0e95007801c0001c180d401c81c10007080f50420014824051081d03400d011200802c01207003107 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 485502904 1250 485501654 485501659
    0x11030c2a0a0807020307080d3c0507051011070602030402190303110606031b12011d1e0a0201090510141309240923010303020102090910081b12060c030a0c02010203100302 75
    0xb400c5840d50043c1d49c265610540f2400c2001a040c003c1c2080540b0306e50141d4420f0780c051003000320003514103103580603800c0f850000314000703410109190f40702c1e0302179000a08120791182101840c280c8034075011940e00d009501a43e01c4c0c1d8202120030705100c0c200764020b05a540260440c8000240c800000c180021000e20251000034081001283d01c5005040c05254484a401c51803410201400000390303103800401d801c1c448800390f00301422115900c000b0108024082003c0100402c000d10b41161020180c14850500404503052164100c0c0107500102e15500d145114441c00d0040c00310340d10a002114801c2200701344920281610b8184001c528424261040e071a0405404004a40000c000c070f03400948230021440e503124603000e0f01030740004c1a0640905180707400204203c411076002c40850f07208070003601c81001210403080b42c1c1c0701d17508032481d084010201c529103401c0c02080700c11311402603c2046501ca0406600017410342d1034280006007168018010311075019500c0c4002011039604 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 485504154 1250 485502904 485502947
    0x322080115030f0503090424080606090a021e0c0a030813170c0c03120706050c13030b07031b08060f030d0806090604150306060911030c2a0a0807020307080d 69
    0x43d40b8006217584034015290350450700309000718076842034003024841001070342c4950400309505c422003160740306011619070344d2000d40200402c002100300d60003404500041a0000b88114841c080c5680540c0240d12020850703004c0b0721408103050340b1005550b046015260510926001c603126844d1021101240400551001900c80c841d01010803000301000805800d0b600050762076440a88250481c2009030303442c1c0e080c04000360704004610116a02d18005614085503e070545d1203640180e6001441013080c9595149190800c02138520b01100c9641c0350303a110070785490035a003441070074000000c8050081d8001d0008d540d0103900080c00590207142a114044680d5400c03000030081d0010b02521154075025240c00300520560307800c11410744a50300000d000301c090707134007184095110407140001019428415101030311040c0f502e5180f00c4c05180810500c144a804443d820526450b13422509080005420000c505080c00030400400c1d603a0050b1100303800400002c0e1149801600c9554070002 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 485505404 1250 485504154 485504183
    0xd0806030f07090f0c0e130c03021b03211501032007030801082806180b0a0207060b030f0d0f050f04060903030e0f240c032208011503 59
    0x301003001c8140c00d52808115401c80da5204120300040280103400c0780c50300d04243d08440081d00513800302000240c003508610781c002c0300b8114070004000c1142040e0405800300308000762000c0d0811400d2151080c90b01950340d0340300c11003c14100421000702c15901c3c0764844104414140002c1850b0840c1e0300070f0902003208143c644501c4d04503280c40c07448901100002c10702d00c050551103044281a10f42c01c104540000100e0703070b0080305105541319100d407141e48649102c40020300e1500a245945203030001d6452000d5990b4401402640486028038926030114030710050144ea8044c04409000c164041c000e420841034546803035164410610043c082c0c0c81c1b1101c0b4115204104890b0350f4143c0107170540d1929200c0000814080d200e10085d07001409014a03108213291a5034039207050500180014001c07029030468034000b4400401070700030039205000181d40c00100b400281449124140005401f9030034041d022a0b032502c0d41c014860980c0340050521301242215440c3c42626004a0790b4204901c = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 485506654 1250 485505404 485505409
    0x409080c030a0507030807050c1b030a0c06030b0102120414090c0d020409061a13060e031015030b010e1005010e040b030a0302060a06060e0d15090b010b0913020403050d0806 76
    0xc64a49200980d120006407140322683c0100580070300780c401e9031060429141e508080700c85010344d80c54903079a60004545800c86859800200b40817140c09070940d0032458064407254803e0200d0360016020039103c842c807c2c136039a03052000f00d401070364041c070043c00c10b402d0904603225490741c402094002c0000d800401c00b030382c0c07031007050711200e00c0c0c2c80005654550301d41010758050410f178460010700d200350340b5641100100220907222441c4000c600e0182652810404480c9a40ba00d4030f0f50313425001e0044091445c0e461380c01003c2600500080c41502c0600c0c51410b0030009005038001c25400400c00d00b0310a40c01d482004a400315202464110503a41e4502d00140c020054044134076454400c540c214010960080b03009485201003000401c00701d662645c1c182c460b92800640d45e90b024034501091400039014070114042c0300400702001036030503c255107030402e96400380c101c03444003240455030490920386280107062810710354200f582854034542e18280e861100c4441001417040e840002042c0b80c = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 485507904 1250 485506654 485506657
    0x30d0509011103090705040b0411032e080f160b220b0d0c0e1c15020408010c200c01050d0218040f1d0712200907090e0609070e040908 59
    0x22007002c28001c3e60390414a094a0f502e051500c20203004c0d5061104041242c545407242c3c1c42e02c00109a6058916079405581d01c0d8844900d0000204820403c4030f02102c1400303042c52100030305911030040003900c40d64101c862410f030b152051808030030b801039000e02000c1c2c0044291401c803031062030604407082ca200c607411014841500010941d03900854003850281442d000f10b4074814907500e448920107429000e110040c060000c45443c5501038404490001d4001c070b069910700c0816035001400c0139102e000701030075035042c1d0b00140009984071100040310411007040102c10101d0394014000c101000c0000382c444d0140c1c0c030a8103942e60740499440c42190340b403205140c0c8103000074010080d111800c04544001c10304d10640720307540300c40e42ca03450f49240310004c1d00e1070503500e949100e410034460303654884200c0c0900c41111084c02d42d0182c4040c40c1c588603480c480380200d41d6601d80e51501401c0c03d000f001c04550041445119080e040140100c16802600b0840f005006940100c1c10202c02e0a00c2d1142d03 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 485509154 1250 485507904 485507921
    0x40e39040518061c080301050609041506110f0307030801122105040906050d080306100c0501061401120c0c2d08090a08120f0a03060b030a060603061205030d050901 72
    0x70900c5202e10321881c4106255030391181404480031a03001e403d100c0780780d1032616a5840100003038400c000602c041d25140300901a2542e0003040440c203800b80300c18000030101305501140c04030706040b501b1010084240036040300c0d40408402036080228a88001380703034a1042c0f103100802d0400124005c28010101141c1c0756426004400702d022a01080e4000d10983c810700c1006403481c83c0000114881c500040d0125100d03400143c29402c58580c082040080140c804070039091054401d1180f0002e9001e000b030a004000e1612074000c10701c5801c00261405405941c000c1c055464000081d0015410500344105650000c1c021580301902104c0d2011071741c2e00100d82c9020014070700c1c40303804101e5100000c20b00c850302038030880003142d901c4001654540305840b004c040540144160074680f41d10801400207030344c0c503203404590781c0c0d59000c410803250320540b114140035071600381c2805240d4050284000501280c80000680c0c115912000d4490041c0250f040c030064407080883c002040c00d4115044 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 485510404 1250 485509154 485509159
    0xa0b04030e030d0f09080d120b0d1e030f030203160e0102030c070803071e030c061e020304052b02030405090a0f060f0e01060c0309030602030907030503030903040e390405 75
    0x44011410300c02a045035050080ca50001d00c102170089a80400450010840c1a4544500c2c9982c841456001c014001203814a60450000c0105401141c200d20f404508100b10055113a001340d00d60070010f010034003040080c010b0500410074021701050b00c00da02c0c40c0e081d136036103094440300b820180100e0541c42443e5002d030ba1841240c0000c20b21600220040101511540780501000419008441154070a06016001c5804c48000c013000c02c0460b01b2042d2003040803e8002880508081242c00300d820507074013a01c2c694031415551001011071b00405d81004450240203036401e0544000035600c2c440c078050756029686a0003c1000c1500580101c0c6000c2c0f03c01d8024081252a0221007056803c6072241c025942c1012000041c0c2d140284980c03009140c05695881d02a0b0454a0341806584003500c840d0741c40c4a10000000403c5060020314013030500d800103035554526001c00ca040003a0080c2046023964503a4240c0b00b1102c2e0301c01c840e000894018000303d0107240008191100314011644001d4 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 485511654 1250 485510404 485510413
    0x71103010c171303171504140703050a050f01050105163f0f050f090a031b05061215010c0f12081501090b0310090911031e0a0b04030e03 60
    0x42a009110400c200e0b44100030038096540700500c01d0700b54140d6080c05004164482c0d855811151801542a070120307003064071440041c60940460101d80b0f0000006042a02d10418402d08681c907014041c0c214208103418001130911075042502c1c12010300c0741c0e074140100003c000403e907003c00341c118034140d0030880d485200021140d003150148502d0f0b4884181101c0c2841c0c005260944511400c0300192075580c8200308012503d042d0b403164801406101145402c1c842540251b80c0d400842d0080c40c861030380d10504d2161910f03101d00004071900803e1051105004800080002c0c007442580b04888450042c41000c0e080d00684803d10b420130043c100d00380076044d40b401d0040754544000c0c144999940c103202a650408007400c40503409802a002803030081d003c10801140c5405190011103104c00c07500c030966100c002100b110300041c03080b108019400444c0b080c51070113203d030960340c001c1007003d55460381c100c25201c3c0e190215900c0003405840c1c40c001107020325100e00d10007448002d0181c00c48 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 485512904 1250 485511654 485511671
    0x80c0a0c14010902031504030e1909020d0c0212160f0212060f04031713021e121b06090a231507051b03030d02030a092f090c0f07110301 60
    0x10b003e414120010b0380a80b04207100b14915a000d0500710b48502e40507590b21a403d80c582e41003000404802a4080010074034034004103000f1041e20040059003a107980000301c100244401070b0511440840f90b805107d414040030021070080c4a44100c0d25910220078017004089200141c016114410355501038400c00081210300e5480189141c0158002e885044450703118001d040c5000500720346003810b42507041015001410601d034090140c5014050b03500c8250304c481c0c08182c0c9480f0359001569140d02240312518241c401100200c0307092810749807107241400e10f9011400c601e016104480c00e40c8c020340482c604c43d1000341188000d0340801450142010345204066140d900496420b42e500d00804402c034a000103802c08603032008001070080e605200b4091614402034100a01e4a16a02d40b0384011000041c0e00014110311846070912510180c5603005000400c00c144440321070042203580300b4400643e4201c800e6603607440300008010355952040c940343c014800303c10000c0c0c1c2c15600b00b0041 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 485514154 1250 485512904 485512943
    0x10e01050f0a0612030f1b140d11030909010501050c010216150c020105070f0c032120040513052211031212060907020304080f010b010801050f01080c0a0c 68
    0x405004601092007448a59168441c0034904d810701c0c180200032030110020100424001e140e0f1403100c41d103c007102c1e5041c10260701d4020700b560a042580200c0d070400520030080c80e811410b0413070008070003030003182000d0401000ca41c00d05010700980d030500c0f8010401c0f942d804025011039080084540d04440184500c2ca0800c401ca0800800e03121050300706294614454814800e0b90b00c00c80c004e6442080d0720050100540e010112400264100300e00384280048000c150072081e034049400f2140064840308400e00d0420382b1a07a104d15141912040100300419925082400c44000c1d03c510009400d4032010345030702c08100300c00c20910328481460304450038412113540d104201c140a4043c1c4207607042c91401507c0900c5000192080081d80001144d410304280307041c00e41c07003401e50040f00e14058841c20010702c0d014921001d001240c1d120190007020f5640310008500405040c0c441001022105002070844040240300c034844c0d0740c010074201c48680c41000b0fa408410f80143c80c50362481802c556 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 485515404 1250 485514154 485514181
    0x801050412020a02030c150d020f03090601060c11010807031b031505010315030609030e0303030a0902040c05030f04120201320718030f0204152d1d09010e0105 70
    0x10305640381905840007005041c004a8600c2c07000307034000c0c0034001e4946050100207800e030190307881410700c8805118440c40340301944000c0c41c24400c0305440b261645008a201442d1060507000901007000300040703000000d245040e0900144403d0070500302350790b26010120000d00000d40310701a01c1c04010040b0655681551010030040040032412102c80c2e00d8000540968183c10801004132105010800124145a200b100042d20a00c0d004844081c03440000c1d1954005980090b0000c1c1d80e000700ea800c500c0d1a22515803003441c9401c1150075071500098980104c4001480680002c03a00c6a4002519100b07600480450403d00210b15903402203001c40c0f14400c2102500001d80701c0c0000101e81d50a00800c1c900150347c40d0b94401440841c02c59680040300c1400c49022600f00b9128101c1d8424080c1c00c0300f5140c05003118a000350001000c000c02c100281c00320181711035440c2e41c145000c0c0f0070100344221503ca04d2403100200c4030a901c2d80c1012500500e914010424254640424450750806014 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 485516654 1250 485515404 485515411
    0xe0316030f080a110d0917040b130f0617100503060117120906090d030207180519140a0c0e0402040807050a08030f120406090f050705040c0201091703100f080105 71
    0x98880c2100d030303200b0030748404680350080f0824045000b8400c0c4640302086800542c001449a1621f41c0c844040c007005600c1500990003210060b200410040104989905050f0080c0344110413035050381d28040e0007401c603400c450301c0b100b51003140100145201442211000c000c01d006011180c2d0796a41342c4041d425210130b8034030403909000e080e6400425510300400e458060300001d1201e490000301d84200020800c2400c0700f10305600660000258401101e52440b6900300004804650361900301203d450704654144e520fa03020780f034039508823220a01d280c44d03c0d0f8060180c500c000b6248010b41d8055075001c00c0401c80d154841c1c000603006c1420b550206008080303503401d5035402c90040d00e5200e99038076401034000380c0100c43da0078040c12a0300d450869215030424080c40e000240502c2680b5012001501c4240c16501c50740600800c000c1400d017481072001031a041d100801044000b0342e113002c038002d4500c155543c0307413502002298a91066a000d50014125184d5402c1a640c0c0d804801e4043c2c8800c030b = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 485517904 1250 485516654 485516657
    0x50f0a111903051009050708010614010f021f0c030e0a0501090302010522060c031824020c071520060912030408090d06060b0a0201140603010e0d030e0316030f 70
    0x1015054a01400c5000107015a0750001c041d1a42034426040c21004051411090303030540f113440d20005441c1030a106000103006591200c4015500700030015050985000410f81103500091140d0310284601c40c1d0422420030204001c40c00418102044000d006d001d12110824001c1e041503800300001548000705d030a1090b0001d004994600030701d100c1408a80601450080d06c42644038000b40860f44403144000e814240060f402017078a9440c02c2c210f60301e110841c0d40e002c0b241c141074490380f030b84480c2100039425030714150f05c2c2c41e41c50f8542c02d450b05007074490704000385001801051501e00485454501a01d4041443c1c5c0c10134a01812650b580000d4a05801d2801064003800d031004144044a01c1640c10016452800c40d006e0144203216846c034209450450380c8603004245c4031203600013070000000550002c03d001c02880c10041034220058100c9200380e240150781016544040745205030358441341400140b43c103451034098107602c6440584410600401e05900403d504402c0150a20046 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 485519154 1250 485517904 485517919
    0x12010204051519090308030a1518020d0b060c030904021818010e0106050f07020906120d0203090a1d04080a050d1e05063a0507150f030507050412050f0a11 68
    0x1a038505072600c441d05e0001804040c410030008010b034003650001642c403910b110140840541d07a160f000d150034a140c0c501100e1030b4001866010144160050245044c1d0850701285040512030603982c1d02e1082ca22024000c580201758550442c07206100c000240c6009444040c1d1a48080e400d00090130090052001481c3c0705400440c00d40d1040c016549140c2c0302c200e1543c5000420f800b009050000200b00c0c075407200303041c8880e50f091001440060070181082c2c00854039501c1c4081005500821500b1112031150403079409103d200070034050035002070304143d400c0d030394002d46241184c2e54400c0030000e030b42503800e20300403542031800d0020030011002c41d0081049907489007000c01c000b400120b010270000c2c8a10066081d0864039003006000e00440912107800307100b032582c2c0c401e41851842da001d0000101c8200340710b641c4541003150882054900c3c030f000c124a01d80305030054810b01513402058806450b880c890020003d0400c03600d00250031002c00c031000c4001e00c0c03801d51070011703140356094000c0c40c8 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 485520404 1250 485519154 485519197
    0x8010207170405010801093201150e030601090c02120c1c0e030a060c0201021612090602030301060219030e120c12010e030405060a030b091302030d08010b0306120102040515 76
    0x2403140c00e0b2802e0354016980c0300d0240c1d291031007100c05041c10080240c8030003903500c0d0101c0511960492504850600c0c1804d0080390300d002c010703c1c841081c8402a4003030083c8242482666540030421070305595003c00c001490001e0000101d01d000302000f80500001000140d810f03040d280010f00c1d01d140c800c1c0001200800c0d541140803120003c11320f860704e4240d0301202842000946d0ba030446e0040c100d192000508018400003e4030314450303481c1c0300b503c0c0c80d0b00138031003030749000d030300094000141001c3d000440ca503500d800300081d07075000d00b505071143c0c0207509000d0710200751088210074181407008180e412480c420740d26141d220790740c01c1100b500c948030b1001c11030001c00060046054103d101d401440c185490607082c4000380d400b00c00100109969440c00706e1603a500e0103c050b02640d0b040c1e9642ca8540f8540c41494503040300c2031828001d02280200402001800108032580202d003501c00c013642c0000a403086019016039002076620043c541140c80f49021640d0241c5200603810040294854 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 485521654 1250 485520404 485520443
    0xd0c031b1e0e010f083303010614030d030b01121406030606031c050306060d06171605151606020a18050604030b010608090a0b04060f14060a06032408010207 69
    0x800703182c00d4003041440c3c4003540c507240602a015445031102504a0710740202c0d07022040700c5450504c4441e66a510041c0c40c9070075040901c00c20002c1d100d080c85000045560000080c1e4031404090301f0320804d6100e8000300b1040e446211400c85e051051103081c88540d11030420500023440c101c640c0c0740039101e0000012510f150004da0240c511034800c140e40d4202500d61001c07100c560000f40301c82c0e0820001c000c80580c803402442014018280740b02440448054942614200805c070f100e031500341e0703a007600c0c14003280d5900403500c040c03600340c6000031796118510784412918030915000a000c0034030120300c2d0004160004810f2080c420380e04103d081107078540702040800c0c005c0e40030107003c118100d0014040380e030040280340d400581520498190791413584e15030340000c00c01c54003201c034152200c681091540d21801601000740c0701d150b10161030318040f8040b40100046225240c1015102c1c50792201281200d079a50000300c01500c0801007154440c0c075400e0103503102c0c0d803044510310780d084007c14030003 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 485522904 1250 485521654 485521667
    0x180c020f070605220b0a020a0b0a020405030c0603040311010e06100b070b13020d060c0315050301051302040507091a0a09081c0507140d090515040b0d0c031b1e 70
    0x110019182c441c01d0613500806405400c0c251400700c60302d80c2070000c000c951105040c0141500e46020790080400203804d2070506850752028150794900750050000344030319600030586500742001074412944982d00c604080303d058003030b1034120702154602905510222404110340d4482c03502c600000456a80d90600080e81e441071820142040301e1b2070b404540c00c01d172810ba690921a00040045520054540b50082240e055001c4100400e50380e69500c10140442c0d0036460081600701c000f08a00d06e0840c007007207048802c560000344926a03d0000400103802a4402c0d000b40c442c18804290744000c150070018194829070885010410001c00016002000110407440350420010801c840810301c0056441d5040880c0c1210301c40d05560b03807607a01200403c00040304002c20341d00c912a442c40d19092141480705180d440c04c542c0010130007032004011300c008540940541580014025070b414004034001c1010190300415011001740444207154081c0d0000c02c1d120b0442481c0e00c9440c001c80e000e40f00d8 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 485524154 1250 485522904 485522909
    0x5010e12060402091003150606080105100e01030b0a12060506211207020406031208040210031a06090d02030105090d11010b010917100e0d0315050609090a06180c020f07 74
    0x103952224001500600b4003013210341e0807107107042100c100a03403650380e10540d107410f103620300b45001d5445100308580d0340e0014886004182c00c0d00d05501a008403100200b4880403928140d040c15195101c10350700b0344130081c1d441c0c0101100b0645a240c50307000d1804001911080d20354511420200702c2044955a512003500e00c50020000101a410340c5c1c0c40b640366183d0088681a44d01c541e0324800080826139080301c0084d00400e541d68803c10b442c040c0304100c0c0100b0510203042c2010b00c3c0601200c1c120360000300c0002440c104035540d50300c800f048800a00b51103082d42c80250554244800c1c17104500c000a000c0503100703407980320216a2400701d040039088403d030070310a500090702c5c0e034030070801c1c4040c2e02c00c41c051200855096500c0c0818640305e91040d500584480d000940c0402a00f4900320744c1441441141c541500d000c03510a454200094890b000b113000140c030401d228004503e09071501da00080007000949001c804285e1050211402454004110310150182003610500180003040351000d = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 485525404 1250 485524154 485524189
    0xf0e1e010608070512010311101e0c0510060b03100801051003030509060c011416050c060a0b0d061503020906030c0d0308091f02180d05030d150512060105010e 70
    0x250380c6041002c4400c1c50018100c10140300b81040040c00503d80003404034003030b500a0b01018456001e600c03e01411244401e1088100301c1203980d1004190600942d200c0903504510700b0b403411030410b050640c103040c0c3c3c20000e004142d15294000401c00d4034240514401d2a8041c000300d2940d80c0d8401c058241c5038100d81c0c0542d0300c41c2d901810300c0024018400740600c558064652400e2104005401c0c1c03c494112031a144004111010000b802d00302c01e01608100348280740c4581040d031522101550380704054210003100752101c1c0300084035159041c07c2120790350415021310044c09140c0f1a103801e90f0b500d000c240e000c3c0340000001401801c0005181c5c1d001c110240480d03200c003003240c40131943d0200280c070a8a942c000d0002141d030030082940d411007100d601c0c03d00160b07101c1180c0081508107140b1500140118081d00031000130550201c142d8404021007140801d000b441f062010700188040d03003200f40d0100303a0246d040c9906d4070000e4440d040c0c850a0300c810260b0741c910020880182c462004806 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 485526654 1250 485525404 485525461
    0x60c0b0105040906090b0f0402031903020715260a060b0703020c0d05010f020f09120a02101116081020160519050d090b030f040303180204060f0e 64
    0x56400c00d40d00c0f206000b4000c420020f8141c800b540c401c0350040045c0e03034400c0546044000d00096103401d200303286003600c0c0d518400c00d021200b9903020392104501e100340c0014030140c203030900005019107100c040c00040740e0b00300d25034400e40304a89403110324165403082100340340c014040b41c0d00350800200c82c1c0b05900354001305080c40d40741d4100a514021110121495503c5031643c0ca251072072800644450039000c0021603d0f11005000d00100404501c2c28001681c01814140c0158a0700e003280d1103c100d2034501441d80918440c050b03440d020791802c01120130940103400049078080420300c0c840a10012404ac083c0641501c0703c01c00303262543c404821924010803031040c03c2101c6404003a41d0700c0c031400554442c0715181c0181c24030440088410b0f9a44d40084208221445d030021188000d015403104042c210b0600102485031b84c0b90041009042c5643d45040740c054001950f185541168011b0043c130042e500c600b40f100d196011171041030019001000030585582500c0d04c514900380140c2c0014 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 485527904 1250 485526654 485526659
    0x1051e06070201180b120a090803010b13030c180c020c031b0409050601060305061c12120b1002070815010b0a050322061b0503090d08100815070801060c0b01 69
    0x108041c0e1003420100e051000c1c455189080c501809400700081410910961b25010082088104c10748010021860740d850b1112440024a01c0402e0b241501e035081ca6142d240c1054900758210361540743c10207400b0755240000000c44c034818074040907492945100600c00d0081c041b0090740c0e80c46202459a9040c1c01c800c6041c1012150b04400c0070291200030008102a80d403519001d003846001c0c2c2000d4006a141d80800810b8100403030401220b1f0100409080c0102103030311600e40c3d80e501c0354039a000304044200349501800440c2c0010704200350082034030b4070b09001c115002c0c1d075074061031241191038054000d40c00e03c0c0400440c4001e04070b4003000b401c0351610348105002c41c4d0310b0780010840d080d604865031003804c0f0300e0350004150003050710814000a52400382c10310907070150300b03417820482040010410441c070184003082d1a400302050742400388880e107030381d05c034011401c1507504181a2031040e4006200440495101180550901d031600205a600d6103c00c4407841e28921016280300d8014004 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 485529154 1250 485527904 485527909
    0x1207021e03070e0718090903030c020d0503010b0d0902060c0109020f03010b151e03040606030b0606030103030e040533100f390f020414060a0314012304030801051e 72
    0x1071982c80411031174a84540001174005075100092030b00043e104031742d568555810150144100c2000c1c10b41400240203020311100010030070f10050050700380700440400c12000302440758120351030751035008183d59102c0d61500f04042c000e0102d020700740c3c4142024a0b0b80111414103201c3d035550417401826210701c07007240d81c410398070300ea000030f800240070341d02803000900d91072104000d10f010754480c0101040651031800c1a81800700c002d80054400e000800041000035041034402ca00722800b901d010a640d51114030041210498410461401c1d0740c004190b070405582103540000980201d40e009001440700c0b400302c07030404aa00031040451400e201c005c0441c100c42c26803c4001c0700704c00e0034919840700d00e00d00c59042d1018990031190442010900421407600d40075015003405905e003130195516002c8005220303490184006048400440406a90f0100a422042e10000794406400e55918501d1066040c91400c0720154005070440001103a90f150020350140d1710511020755407c0620031604 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 485530404 1250 485529154 485529179
    0xf1b0414060c1908030a0e0d120b180c04050a0e0717090a0c0303110f010b240904050408030601261b091203030a0e0102120a09141207021e0307 63
    0x81c010250f201d40340c500c1160b01c900b0512060010b21880c0140d89a0a00900390400c1d103a01448002d15a080910503540c100d6120304901c2c00c0c40350611020540c0c500100c04500c400c80590301c0303c3c0c90081e0200800c4403000e030040081c0211601642c072081c0300e40d50742918084030031040d50300c100000c9403102017541d8446d000b494943c11545840c1900c050210a503030b0480020000d5104030b000c00c1100b9a0740c0f00200080c080d500361060708400a1241c40c000c54005500d803001c00c0080340d5940803d61002c2040c50108041e10080702c40604200403034142030400f40c1164000700c1e006400151202000700340c60030307100c405000d000894100286240c90784407207201e92113000300b840180d03540103200300d840b650381d84550543d00190320380c0595078908011120303806031802c400b4401990b03801000700d10031050500b59007079400341030b00c0c8000812900c14076041808c1c101000304070b05c2d00e03c240b5203160a8081c03118003c180c041d100f102c0514031001002c007982d640303900901170300780d05401c131a000300458603d288 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 485531654 1250 485530404 485530417
    0xc020c03060f0c07141f2a080903090a180b030a15020904090209040303051605040e010308250605010510090e1501020f030721080c1912050f1b041406 66
    0xa802041880304103166290614201e44814500e078a01e4802c1c0c81c0404507c544850141d80080100ba11110406a036030400102600304d41001042800650f03040018070540700c1ca0b0074018952540165640351240c1c1400d05080c2c102401ca160240394016850001080e584160740412001c0d6035080c0b0b050703410300a4200b0502ca50300a51a841c0c03000040c0d4401d80d426224030b01c0f0352000a69820038928404c0f00f00340c41c2c541e00d410703c0300030841400310340c00314000c0604591f400003e50366070b82c9000140c140182c070010246190b42103141121410040c551700810305030f41d4180c900402c242034003a012940d0078418030800180c94a06000314988445003241094001c1c81801165403910402c100700740766a00c031407419141c0c0040008402c1d120400038520613088602c6140075841800c140b1540d4030b0a21030000e5601161408005070000680190740001140040ca001080300d85030101d6180c0c60210300301d444c00c170000e044000c03c100c0040c1c038000361000d0b83c036407500000005030708000344030315a03102c1c0 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 485532904 1250 485531654 485531663
    0xf03120201140c13080708190c080601170606030115031515090c120504020108010e070c0203120319150b09040f020a09210b0403120f0c030c020c03060f0c07 69
    0x2801c0404000c40c036407040500401d01d482c40581d80d0030303180c00c4c81081180d003030b00704a900d500813030002c200d9054001144807080c182084e00400c407503071601d4030700314641056100810a024860000070f08106403032000c00c1c00d00c0c080c0c041d1800d40e540c100c10542224a1a840c034a0b100c5060708051020400c4000600f070b4043d50705d180043d5401c00340e1036500361105943e00c0a45000d403651410410203600a24034564207400001c20f101c9401e01d40e0028000722814003640e540c000c0d50700002103115104203171206610342c01030280c8451003c00d6001c001c15600442ea500c03807907000a42d0072212a80c00d44103075815440c0250540300a6428003400c881d0036130140110680c01500e404081007015041e1005250200c0389031142c00701d8500e000400903c1d41d01c1104548000d90100000c2b0740401c0203803135180d0740142d0601d4840e91110b4106180c0e0020601d43c0ea50101452910100458158142e44550700195645d000c880c1d003039410380c00701660f415044600100c1501c0d0078001c03503100d980d01400b804007544074 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 485534154 1250 485532904 485532911
    0x9070e1306050a0e0a080a020f031201030807170f090901080a051c0917010501060f080f010b1e1201050909030406051c0b12010609060906050102031902030c12220f03120201 76
    0x130001181c58003044082c155007514000034a1703d0055010841c0b100501103201c0914204a002c0010b80000c410511010704400d0000680104100000c40411801000c2d6131714161100c074007260240441c2c110704200c901030f002c80000890201c074005552100c031503000c0001d1140560b00c0440c40700550f0b5010100c81840b1154002168880800d150070450301c8040000044070361405c0c90041807613450080c030348244601d03101880402c1843c0068941510314114009640b1260681c44641c030030090f03c0109003100002c21000c005c03008940c2058100c0d60704441e02c4500340c94440c451501c80c482c600c40c410110302c0030270811a04020301c0b45040d01d40003004400082415100c0080b0701d10070010381e0004240d954509013804803180c2e500c41c5078050006208100220743c20300300041d6607480b83c440711440d500e1401c0d4884080c94405c1088600103048541a01e034100034035134840e2801c1e0880119414860080b00e581d10396924000355040848400c0a0110181403441d1155a0410070100010045548 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 485535404 1250 485534154 485534171
    0xd0201030b010e0d050a06050c0304030f0503040c0302060c0d0801061d150403050601180f06060503060f0a0504020c0c0108061008010312170c030103030210060303050904020906071401020309070e1306050a 90
    0x13a00310132034216501070b90150410700100e14050f0111400180440156601402400040f0ba0f1114036180da00307000781045507403030310740d820f11440f0300003603902c025031010380010a11164100400ca1540b01112604c400085036240c40c030907156605420340040102802d1408000c15240075011180122202894545402e840c0d072116402d015090308800d454070480010000031300d0a510504c0004980403400300085410160010410300c40601503c0c4101415910041c00d5a6001e21a81c000d00001b4011983c4059052542c0d844d514280542030105484900194841c00c054280141d10045c913926802d0507803e665a809140e80345881400410104038000c42c0b054080c2c0903014064a0100e0030291650714525000f45804e001041460710340d0700300309042000a40010075240024000c1f0f40150b2165006001300c1c40c0c42c001e0101c003400c15040d00c1178039400e02e101940298080c2c0c00c00d40c01c0d03c000644504035505a80004c3c1d50388903584030072b00310300800300d2039070380c0141e4000011b8040841c8020 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 485536654 1250 485535404 485535409
    0x2040207021207031403040807090c021f0b0a240c031b0303060e0108011b080c0c16050103050105091614090910060f0f0e120309030610150e0d0201030b010e 69
    0xc04112440000f944440b50a100740000c00892060904205004601d480d090094154441513140708011a9036100c8143c0d00700c260081c050342480c01e082c48121100d02d024003c43d000a802107280c418011103c4c1c840c00b2654443c5074203034440c9a024500302000e080380d4000b00300d444020124081e0100900d840541c07203001c0003505501c44841c000c0c2d9012441505101c1c42045000c01a4040304c0e16a140600b84940500074961025a65007603090890f510b0b510100c8442003403080d0700c6e81807828001d1601e100e172002c5c3c1c0c0350b4054080e20310a0340c04110580c2c0380c00c280491240280c2e94100d007100c549101e001c02900c1941d25480580301c9101182c1401c8248012800380201a255206821007401d410b0100680c402c2d150350b2a02028900701440061010000e4400d00c84000054011344405020145114040003281c9002c2c1000d1308030340052030b04a213084000406030044c0300f650900320601400361032040c1e030002e184440007071040104560702d134019001088864002c80c14004000341420040d07 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 485537904 1250 485536654 485536669
    0x90102120c030301210f060c020c040204030309080105090c090f07091d09010e01231e180708010c0e190807060c02030705101e0513123c0204020702 65
    0x10840c1d1000359180d50501c040f18403440031a4004550071407074141c000010131001b404200d009034210300c000402101c445800ca00b004425404250410b000040000c201507008105400722220ba0340200100d4403070356a502d4a840070b000440341c0c460640d1003c125841080312405c1d401c09039508216400f10b90762a040011a21080c080b0f0700c2600158080082c003035001c3c062450002c0400d40200b04029842d40c0703074000e07001400c4202c84803001040000c1c6086102c2c20b0300c40c02c141074a8200c2d22441c900554022180500c40348580340c54020140005060107050146009820300390b102d403078140103000b01707020544501029880312084580c03400500c0d10002d2088901401c4070350f940d01d42034040b6005152500c2078a41c05140140030611b808121f0507071185010070003080594026084460780b0b84200d03664095210f04c8ac080c540340e542d00082c0c1030b0148800049007440f0364004d60740454012450742900804c3c0d030b0201701040030403250200c0c103008422503e6000d440184014100105500480c03d817 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 485539154 1250 485537904 485537917
    0x18030c031d031f0b1807030209010c020a0801090203070e07120209041d03032703031b0d0606090603140f0c0c011e050919031205060a08030a08070e010309031409010212 74
    0x20810f507030000070404002e0b001c3d0458038a070a41e1002c01594541d4034000010000074209010543c2c080b0703c03c41b4583c4a05a828192500140411405130b1107500c1c0a0003050760382c1c0124840d1084402c0052881d251001c1a07101e180c5903140d0108000140d002107019602490707140c2d500994500b0603451040c1e810101d94004885d0000030341d202d02d080d12486200ac0420111001d089401000b80c0044000000c116a489140505924030000000006a0140c09a0f03400c10400c1c0703040420110b01a6401104c103802c079042980c051180303080d07000c00c0c40c0c2c0140f07054071919001c40c24440000c41070004513000701030702030a040000840884482c081c4040c0c14401c1c1301140c0e225150014004000d0007001107400c400144d080f01c1000b0310369039501502c049249588083d04235224400100c03503544004c1c000d001400c0d81025250745482c0540024206030381203420201007102201d080215500c00e119100003da81502e0f0014855100c0f50b9181071341e0441c4680c5070443c0b00c0c03004903039404042d100c081c20300b = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 485540404 1250 485539154 485539183
    0x21c020d0b060901090204030f060218121b0103022502130e070320030604060902030a080c0312010e07020d110f0a140f01050c071101021218030118030c031d03 70
    0x256401d1038420050883e20690040c0d80890051001344040382210580721a200e5010800503502e0060860510002d10600400b60f80700200024008941d0004a280300c0008541c07401c46081c42404801035080b802004030b00a404649044001081102da2a1044078140010400c0b4150104141020203940c41c1c8845001715400628003042040b2140710240322440340980410401000400400c0d03890300006d002820035500c50702c443e0250f481c144020b401d00b81c0c20800c001c1d501d010100c8482c1d6a940420038101800c40401c00001d03103c0814400b01d4042d1102d0f0f405803021070b1040d001162862611401081755001d810b0f03a01d00556001c0000d0002d4903c03a030703011607038854506100d9040c8a1410804100359041408002d080482a0300b01e4404540c0424000d030001d41081c0100d103002c00c800042480004000727a280d0400d0800301e100d0b281041e00314020302c0008800c80d21002c2106614000a01040e1026110000030340101ca0780700c400300e100050408030704d03141d00000c0d142c240200c61040 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 485541654 1250 485540404 485540423
    0x60f040915090c170618010302280906051309030806090a15030305040509330604170f0d09050619020a06051513090206090607140303010303031a06071104203013021c020d 75
    0x43c00c1400ed010148807400c50100072110850300c0140c0351110050480c2d10845620707001407981550341c1d000c0307150035244c4200e09102a80301c0c60090314603072143c09030301c2c1700340d54450020b090003482c1b5487c45840714030700340b0f0440141000d1003a8001d241032895495485041800080352203030030001a40103401d0090014082150700e266000d0070503c00036008000c11503038401c10310194480764211801880b2540e0b0451075020144030407400c1c0090404020203281c10314082c440c03042405c0307030741c115070384802c81c0e00d18a0b00c0e84205000c41180e1f04c0e088020f40110081c0000c000c80e1030680d018124560103501c000c203090081c0320041e401d50713100340c1048000c00e90782d0494055200400c2c07103511401900f5030b225071400320b0b980c0b86c0c4280d4611100c1340a1146842e4410f0180102c05c55103203800ca034224000468a0380b9162007082d260341c00301502105110382080280010002d00d902c441d01540b260881c0340030801880c2c0901000e0412400d95100c0310740700c0c42c80500140c03074901c042c80c001d9005061a0 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 485542904 1250 485541654 485541659
    0x7090c090810050a110a320313050c01050711120f0303010b0c01140408090409060b1e090a0204030b180319050a030506060f040915090c170618010302280906 69
    0x10012140c2c0c003802c2145502c0240701185400b500810541100801020034599030000f82e04008810400c0f003007d001c40882c084240071100d40180e40005090f84038206850038240d032400110354038081d400010701184010030300e101980c2002101c400c0c0c5030715200f041e00c680181a0142c00c1c90342d80700707070f00c0042000400142e08013601b10a100d01441b805c80b400c03100b000c81c1000d403103000d524000c507500340384110303501c20ba0501040401e6024070308001b000390140a045440c0c00700034550b141a19102d03406440400e0000b240807040340b08030390039a036005480c03c00a455000318254544000415240e00e80f004100c0d00c6041e0082415104450049940b034a556155100006042d514098042d0b40190340034000c50000c00c1c0802c1c29201500c81001001454000465041c20110b400360b001604152610b00100c034004d034481d04580c09034004049000060b16400f003400b0f2082c0d800014140480030303000040c0014a814040410741500c4103200010119220722003004010403980701200007545c4903002c = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 485544154 1250 485542904 485542921
    0x705061603050f01030f0b070c0204050112020a080c030a030c0302030f0318010b090c0a0c02040902210708030c0703020603090a020909010b1305060604120c030807030305010e01140307090c09081005 87
    0x1c0716803284032440c0d03c20790b95145580c0d0400c4041c2114006058038030541c00181914400e801409000d50010414005540d564001100d54282ca40c0113034069804041c0100b005007000910b001c403000702070010940c920780c5481c00c4514044d2814110214001005100714120041e800340d4054001040c4409241503403500090031201d4040201b80505161030411030626082400d5442407045410501c41c400110b00c0028005d10311888000c0d840fa120800d081c0d10315905c0d015140c00b00300e11034102c0f140141c455808a030759004010208503603611195042c40142481c8003d1030b0485000022640100469800140d802604032540748030780c0e5660360141304900c0d00c2d8000690001b902241000103003020000310f42c0b6407080d07004c1c2d100d069007000e00351001c200440e1038480065400c013230455150a050f00e0000e010301428410542d5554544002058040f84a4502d004201c0700a0040a41528280d800005046880c80c450140074564200090340038050202003002c00d052000010b503480d01520 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 485545404 1250 485544154 485544161
    0x1b040b01050c0705060f0f0309010c091202030d11010f05130c050307080c13060e242e111b01140f18040e01060303020f070b030606070f08071203090213020c03040611030705061603 79
    0x203100303794441c8201c43c090303100800c0201c0e030a02c143c074007101244c50762603100e8090804419140c0080346040100844048103800c1008001c1c443d5144a2500346d44104155542040d070255805a4100d840010500d281500c403801079001100401318044e070362007a0a40050341d08868940c03c0e05074400d4a841d0941d030ee00c0503074404c104105d600500ca1005030b41c040300f5608503c4229020200d008400f0705466010b80002c2140b580d8040c111601841d040034106401014442818040f81c504002c41c41c1050308002540c04000200301d9003424030722042c610344440303101003c1c0160000c1c1d550b201080004003e0003024069402500240319003000480380c0d620b8a107503503110307110008007881800f445682c0d5104450110b40c104100200245490619016a20480c4402440d08001d100d50340b2010740c1540004154600846a01c04840041c8000030b0a902c10311189000f660001c12090111500403403184a20029040031a410a0348540d5905c2c42c00d03a086e501103c00c1c0c0483c40256109a50601 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 485546654 1250 485545404 485545409
    0x1c08070f050a0504090e03070f0c080d02011e020310050604090606020708160302010503190f05010602010b031f2403140f0a0c06050901111b040b01050c0705060f0f0309010c09 77
    0x703407551a0242d25500181a4042c4d030007000c00c120340340c029100c0125401c01c180c80d401c5030801d1030a030b510b2602d0310f04801d21103000d101d082d0b580c0c01400c4407161524018447d0380351400303110b140c0080c940c030052425402035100a06030052041c0705500440c0f5900d80c031015201901d05040001446410100080d14140d8950301030001a800f0b54100d0704410305000054048070350a081550300e0b6107078604007003540d0001c0c059006a07185005440521000035030070442c100d1300e039900204041c0101030189070300d5a11000c03441140c1c2c0800ca81c0748085214590000707030303c8036a82d210042d04000390150100c203a0740070f5100342e0b504d1068462600c1006400c0c015500c1c0340ba50400200005003e540c2c4011f5000c550788901ca05001c00841c140520380d004842c0c031106944aa410350301040e0402403402c0380141d034000d03010f00030b44c0b80401e00041765005a0840b44005605002418182d04d45002c1042d00e41c80100c101d22113110a00a2415620b250000703940142444000810011080700c001460307801684d = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 485547904 1250 485546654 485546657
    0x5060f19030509011a03100207031e0207030308061008040209060402090306042904030f030c0c230d03060506070209150d0c0305060c0414131806061404050105060313051c08070f 78
    0x17016200c2d003540d00011040080e495003a000b40e250103040c10103444400c41807011b2695060758030070780b404855001c03409005680c030a031140c003100c6e125242400540b588154245000c204903e001c0745c0541303010494654400c1c002080581740a1048000c83d0900c401074030202e42078030201c01d000301e00d80c1c0c5c0781c4194031880004d254a07041c0d61905840060468071980071500600d0f5840b000314151501c9109201202070f000b599941c401a556100b8414403140074030090340c0b5029200c01c1120881c4030740180c408980c002801d190401c0712036000c210324008040c00018030a07400321840b040680302d548404504a000f2500c0495051030340c01e1003418004000d0501d450000100410f00c01420b00a0304034180710780540b48030780c40a0040f00420300038a90000d841c040c110321589040c007000f00d990003d40c00d035010702e48540154080c00b418001501d41c01e0243d00d40c03008081c40000c40200c00c5440c01031050b40690211014002c0b80d440c91100d1021140207200040d80c038508206216401017220150603005 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 485549154 1250 485547904 485547941
    0x81e13111914010f02250e07050a090b040b0717040317121b0403030c050a020402030108010b130b0604180b06030a02090103180b060112110a02030306030f0a05030405060f1903050901 80
    0x85080c003d44070350446d48030490000d4120314181c002010051604060040550714981c5414049009844c07500b0071910100050020003020a030f658811003500c04403000c2c5000c8a0401a03142e82c3c2d001412185980382c11500414080000400d1061205030092030490b079410743d8800c050040e1101202004040700c90100000f844045200010030803101140d4052605015000301460050706048182d940a54002e00210001c01d0916041d40020303806202255501c05000342e4107103c1041e0703051011001c1c0e110710306200802a450300e00101d40b241e54030105000903545c80315030000ba041d8200341c8000550b5a404103914000396014410303c07210150041000c0012507088d640c115200500030180390410404501c40c03418890716410509102e0100c000090304d508203218025683c5d0802c0b00d003c0e00c03a02c00e174030003440c00c40380c0030480016182d00000034501c0c0a0400c410700016a008040b0f44440020030480300c21039042d0110b0002e207130243c0d9500412182001c1c1c00c000c3c00d45031003110300e2818118 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 485550404 1250 485549154 485549177
    0x90106200d090314120711010e031b040c0c0203060f091002160b0106030b2d280f06121e0e1f0c0813110a0803030403081e1311191401 59
    0x781001b46c030302c691b5200506240b03440346c640c01203800d942400e4860303400d840b9010160300300b8a01c50201141c850000d0380d042080c03103140c54049442c2c144412010b0b41607003140d404200b50820b00600c00f5400586902158058059403010780c0c00c0b81c0c0024903007508010781501460800095003110f6004080c03030701d030074424400a00300060540f10950402d00125907503400410044480c0003210f2140c1000a03c001e401100410a28a0500d0300503e04400e0140c410804280c1100362890603080d0b9056581e849004420107140c02c0080c01000d90100d8162645452107000030300034002c011404a90502820320f008003449002d1601128603200905a07003004248445640c4c01442d0b2070b0300c8020001207440001583c104405c0b8036a0208040703800110f80e22021446a034000000c0d030049209583d2030f40c15a44418060141c542d4000c0c0d01c015882011000c544496124100045041e0023880001103188800c4001509091320f041c40c2542565240010000c0c2c2c0d00345455030f5451030b82804c0c0b01c2801c58 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 485551654 1250 485550404 485550433
    0x50411040e1b0a1d0a0605010206070207171603110f03010225060216050d08070804020d0210180f06030e07052d0d0b09061005090106200d090314 64
    0x1004040d0701c4440c00c2c03040d0341c0310196981200e01001420f2a0b140c1d00000d18400722004014041140c0e41c1c1c02140c20240002002c0d40b0009600f4860800e40d800f6109042c00c02103c81d901031203442c4540300d40d208100314100e000c0d00c5025484029480b541586266181d104103100d4010285000144070b030744144400c0d81e07073340800451461a1000075070b0130821803d0b41e1030800c0c001e00400d0203280c02072101c504504100040020f1204150b40c50b43c4602d451070350340b00d0b030844101c101207400039000701c101c0d5642001030500f14a0b1240320303491801c201484010040c0742c100001c0c1103600c00c00f42c1a100701c100300300c0580c02d4820a83d01c1121a8041c08070f250034080407983c0d0890341c0c1d1010080650003030710b5015104204201502c0c1800040c00070050810b80d04000181a109a038100c0c00e60203482c020030401c601031640b02b801c4030805406040c1e160302c0c0c20020396941c5040070f082203210343c404000e540200c4050100c00d108013641c0c0c841481150450901134800411903080c0710441d4444403130085203a = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 485552904 1250 485551654 485551663
    0x8130c06030b010c35160311030d05151504080606300a0b010806070206160207050a120c1a03040609020d240c020c0f060304020406030209040303050411040e 69
    0x45090341400b00e65107015000403103030345240c144041c0280f9404448a2000c0b05811080f9080ca000c41c007005070790b1134100a44404070f201d807504003c0001820744407500001c0c010342a2030040d41c2c01c902035030f05200002c607c1314144c074001c42e000e0400d10030366807107a41c1e10324241c0e80301e1101e424150f070050706040c100100955154800b034801d07403144e030f8103040c00801440c0c800c0501049440041400c20042401030b52541d03180031481c03040f02e48240c1e031000800c0b0300d000002c040d03105012a83c01800c080d110a8100021495000341c18011030080000c041000c1d168428a240104640c0b034a42004031a2410001c07691000e980080820030002c60380b4407145c4166505880d00142c21180008400300c03940300041c0c016004040081c00e120002c000d0030441c0d03000305030310a05800510707800d100100325508202e8a45e162000300562040c00b6170540c0f455424040050356100744060400202c00e0380340d80004032000c404540440019480d07000304010007018846c101c41054082d1401d0000c122503041c0320345c45 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 485554154 1250 485552904 485552909
    0x1051003151a1c06090f0e2a030f060901050f060915012f07090b0d082d07030908061005041a060309070e011203141305040f0c08130c 59
    0x601020105002d0042c608984681c0c03124405614001445480700380500303054030403520001d1400c001003c130082d0390b005040f4901540409004c0035850202c400003080d020f002d0001d1400304801842e41261010402030a03000b004130010038007442c041d0981800e4078401000109070414500901440b9214071030300c103400c000c4560720245c60780d14000040b1b030920a21641c4d0103225000340c0b051044611001218030b80c00500300300f40e912154448840da000d850380c1001c1c460700301503618002d0010503005009400d918010f4040320818031094141800610300d0b25803090103007040007a0308010150810b5110740100352100141025182140b110b801120840c071509010300d403a1410480310301c0310b023821000030f804000c07d4144c036070411800c0300c1c0d03542c01c44e40244c82c29801c0500c00411103001c1659080341d8554140d817020904600e1200641c83da400000c41c3d41c110085a59001c82d26a6450207055000c0324490000644074111040c003d245030805050055007490006101000c01c2018088809 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 485555404 1250 485554154 485554169
    0xc0301150f0e18012a1805060904090501020a20060717040303020c0706021e0f0d030c090305060a05040b010504090b04080a09030803010b13150203120a0906020c060105100315 77
    0x12039a0340943d0f030000d02c4481200c0881946400f10402c1e6a050802039184005066801d82c6503901101500341d41b00115807040e4003144201207810031007450400002c2030804006030000c20400c10781c0d5032b51803e82c2c00c54030210007c100c0100b4000420003480084001001c2e080000f840700b030801180207806201c040414400d104014800a824540281c040718040a4800c0858100c0c2da51503500030f48516000c10703070102c05241c027010540141c80020310700c0101c031f0000c0050181e60104440a07001418200140d4003441008100000402e109110003481090308003404a0585800c0c505840c1e454416048144a145007615a801041c0d9155120790311030ba2001e0030079039a0385610700a5400b41c0480e4402071a90710b00000200c1c0d04058400034011440c2510b03064103009845074078240c4114410b61480005900034417440a2400840c40d2480c0c01c41c10035103001801c45001d45681c001d9034811904502c4541c000c40c010001810440110031100c0014542003000381500e5044c41292211842540d0 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 485556654 1250 485555404 485555429
    0xc0e0d062a230405031e0c0103020a02192f240912011803020c030f0c091f2102090703050705090609030304090504260a08010b0c010b120c0301150f 65
    0x48200000b64125000742c81c005085444003121070f1010307020610340603042c09444c019002c001c04c09502078000da403041c2d0a40e40150194241507450310028014600042c0c440c2c0c08100824201d8092820085a071000005415030810741403c1c18000d00a91104864081000d40c5031203c2d0034180c0002135480381881142e10320031403604034200d10301502500c0078083c4203400a86000e0101a00055103054001060781138031205a01c01e25000e071108420240140c01000c3c040c002443c54200070065003a00c1c4500082d003040036101c007241c400d41c02000e80075412030750100307140d14150711f800013400340e000740189010701c81450203c0e401000d600840001c940110004500d07541540e50910a03940034041c101e104104a280c1400c00c100700c10000c016262003c40b01d40001901c100070300c01140c10403446512114441e900e03003100c82c0b0440c0e20443c42e00e451075680c1e1101505a0b580e100d1109a40d050000040944082c92810142119400004203004c6401c0101c00c00000810190000413120000c0516 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 485557904 1250 485556654 485556707
    0xa0e0f06030c09090106050906030f06180304080d050913110f090105300106030209100815030a0803010807061805010804031704050607030e0d120c0e0d062a 69
    0x6460b007030181403403d50114000d820800c0704203055111504036403085071f03000e1494032a00d05054680d010810040060b410050000d40c1e00710040500c0000d03d0a8401180d02d412f56800005003011010306550000410010f89050302d480d06803c240c064041e070400400840704510190700d6144120648036040000114241307003103038013510036201c0040007891203240381c90110082c0c18031080444c031000f401810100000c5080c911a109845054201625258400a95004c1070350038900040249550100ea6050640c40e5142880ba40c18007500c110145522541000801ca040001c250860001c1101c9603c90201e003401017615101114000c0c2802201900c03282011076141c07242080901c945d2141310203000401c10b00081052080c410f88d50700b00554a0b07242c1070180c0b1a407801100310000b500a010309840300980d540314249403496810602d0104000c40040b40121080303030819190799039100d040e0f4210030b01c50180c6241b100590002d40443c40b02d41d00d00540014800e4035040d2081d455072110 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 485559154 1250 485557904 485557909
    0x705030705071d1614130b1e0307050301030b10080a05010c1d220e0307080d1503151e09050304090509030405090a02090102010204030f051f0509070302010c0204110a0c110a0e0f06 79
    0x449282a40c6480080c600700d486424082c810790008c13200c1072103440e1a01030082d4880c80142502e0240405541e0103103981d20b10b0b1510403190b007014087c00c9094010130030020700414104840c0000794030500000c00c041c50441006401e20003107401c0e004a407c0c00615007025980ca0421001107148a591907100404011160034001c1000e04040728051100103000b80c28000b021000d085945071150003840360080d034840c0030b10004244d1100418202c0522600c5120310b0054201c1c0800d0317a0400710b884015181006820705031803034000c0c00c0d2030b16000014144620f181da07006160744112b603100110b107481d10300008500910001061525010303400b10310036245038800c0d0121002150000040844041a410920740b05c0341c01d1131024192840b0648218041d8a003409000e200c2d15000d8060000c0b1440c6400545d1342c5a2281002ca900130368541280040c4d41220000c1c240401907a55582641d000510b424009010001c88a911800184408115445102d00d90540c845a000c86040752512400c01 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 485560404 1250 485559154 485559157
    0x81902090a0902030a03080f10050a0501032004090f0608010e03090d050f0d1d120c04090204061d0403080121030e01120606021c09120b07050705030705071d1614 71
    0x40003985401450b10744170a05600a100c98046c11207803404448036103500305040544c2c14035100741e58000b12030460030480b070340c002e03449800d59032201c42c108159001294500c000c1e41d4029045900e0070b50348d5806006a042c9940719107809000054002c001500c084206155240548074a052203110103000d00c40401c0020310040c4a20303080e20040350000034042c00c0240450400104460100c200c204010800c1d18010b81e4102d00203000744040d01c414959003040c41302500f4038030700998001d500c4060018050184400210035000042d50049036810649070003044034006030f02c84e0910410480342031014101100c04109810b906003860310340c85c1c5c2d2210040e00c495001e0300180340170a285c220b0000b00c268010403500441c3c01c115400c5000701d0748825042c1c407a000c0d40c1c002c501820140000300c10000c0d000d81c0702c0f140c20846604000d0b040031004c2d61401e10355800500100ea19821006080240c852303940840303070104080092881540c58800c098509181c050071118003002070200394202e210500380c0 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 485561654 1250 485560404 485560421
    0xf0b03060c091906020a0308150f09070912080901030608060c0306060a1209060c0f05130e0702030c0d1e05030c0a080a0f060f030c050a030c060e06090a080d0801081902090a 76
    0x18043d44446642d04000303520703801c2000f0154085880c03040007446480305058500e5180d100140355209086100090100a120003441401440454032001c20601d06584040c150300340709030440365803140385c08001420341d0301ca507010160940c005400d00008241e91800d5030b610510554402351503a64811086441109068800300c43da842d00911509100164021646840e4a6160800045c0250000325400d108002d5074999051964030284000d220004990f0b81004007441180d0804005020b2682492169915000890b0300141340040c10007000ca4680d140c80b03500e080250452400101ca0525032041102007010002c0720030024030707400c007507034858034641c0c01250003040084e440305075000400091340001d540d060601071300090301d85040035000341669881881030101c145001c4055800c0803440340350941c044070510542034551a141120701c000c05220f0001d0001401c4410064000001030304040081d0b0091039100160004800d800135069505907035420703042d03494121840080a045 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 485562904 1250 485561654 485561689
    0x70c02040f0507030b1806010203070206130e0c04060f0905060703050a0210051501090905150d1104021206010f020a05121e070317100303020604030c0f051c030f0b03060c09 76
    0x341448456980b5030f0003400074010690360046c03007064180011303424140c12102140107910400c0b00310300600340540503001c13110812412132a03030f58580c407220006000856002c02d00003000702e010002c460740301024101d8801241400300c0f00c01d061a0100340749110303180001c2d00384440003803102ca9081c4200300070070000215076800c2010f401c1c0745400004000f07500080b603000030000f0b00f006c10084058801c1700d000709c0c3e2030520240e10081c04000d01516010b0044c00341c950f0f00c4080402859074880c0d000803c50116241250b81c11490600000b62100d941c0c81510411580401c07030540c002440002c0001072035041550b0942c507110803440341110b400c03848105c44030554001c10b142007003641004902034102e0a00b02d030304403542d65008075541c2d014194403005c1d005921074008500803d008800150f103050003400038050b004840e8035110316102d022090100400c00b26502d0117041640743c45454100d40c6600c1c0b080c07080000d0900001d13035900002c1c002d034080a80003d11200c99a07210707000040c908402 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 485564154 1250 485562904 485562911
    0x200607030b0f060405180601020a05030f030f090a0323130806040b010b03040b06090403120c021c02240a060302120d12061d10090e0303040c1d070c02040f 68
    0x4960000c02500d000803985000310181c40006400d45058001e40e4103541002c2c0820030194148031518038407903030191070a410350160a40110118034140010601c50900c007440ca5501d041100540d00ea1000081441c11907403c907489410009601020054111000c42c1c51101500403200c4010070501c41c24074020351204a000303000540d80c802140c221301c00d50042c202c4003910f030b0342c0e402c203d4094402100c008103124941000140b483c5071264903da0030600038904150160041031542c0704481c142c1e062040581d11200e0b0306a55201d011080d01e003021003603c060100e800650a4898180c4a090303444001000007400160070b813030480e40300c44029500106185251541804110703121400007a02400007a40b41c2c0300490441c005010b05004c540740904002c00b1b107042c018051850460103050700c41510b2035040c000625109600400d00f0230f40c2550003031a42d82c00c081c9014203481041e988100e070f40096041048603a44010a080791380000d04d0305001410384224030005004051030740f00403401c2c915 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 485565404 1250 485564154 485564161
    0x50c01030b28090c0f021e03040b0c030c010501050f1815090c3a09021810170106050d0f052503050114040803010603090503070c030b0709060c050d2006 67
    0x40007211842203540ba42c2d0f040003554142d0100300c0b80c0030b00e02480000581d0144540200020041c1142c4000c4c1c440d000c181c9040544440ca0801c21340e00c003036100714542e40301040505d06051f083c460740d80144800c0b9017854807c55514081a0740c005034440c08041480d541c0d0018030142002121146210002000003c540c600f0080c43d01c083d42108003c0310121000c83d20f60886090200f03080c01310301640400941c044c10910708040041d04100d01e0072038000500d03a030340302c0c901030020602c0c130300aa240c240743c1c80405041104a046407000d004e284140390707041c51000c10090b1140c000801440d41c100c00484221540303410100e00c0e2661009aa103001414280c2a80340c4030207110400041e60b1241000f8002c0440c40050441c040d02c054401500030300c010801005500d0181c0e1050200504c10740c00d59040410544802c2942d0815a0040d1900c0b806181007103007466000e040840074103540e05021900500b80d480b400d03944c3c2e008040a40c2400f049154030103007224076040c1055400309c0d8404440c2a0710303 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 485566654 1250 485565404 485565469
    0x15040507030e0d2f0109080c011b1b1401020d0c080114010504051302090111100c08070503040b01050f01020a050304140103050c070b0c030c04030b070e04110a0819060803130e070507050c01030b 85
    0x4134040d00e07445581c8601c0d0084602c0c0700b0b080c003c05440c0e01e16107080c82c400cbc00d41c55007000c9003600d2298820f1503500300f00b0070024000c13500030001c40049a40301d91a1543c98195208404024412100d041040c00c01c03060000365964010262404000303600180c841100c0001a100c0310000041a6103901c40c00f170304040100d000340c021500c42e101940c0c0e0710700c041e20780d010103031201e0000b07031f40c014040d600d601c005000c207040542c1407400744181441140e28a40e420780718141150302503001841d00c10300004840310107503018001c058000060a111510700403554980741d01145000e0304100b45c04000101241000d12800180c0b8055034002101000c2c03401c25801c09440784030301c1c40c10140254188440722100000841c00d5403207000326501d070300c2101d42d1802c0320407400c6002d4081d00e030890781e6100c81c040f99161040000d050381007000c840301d0446c00e08184003400d000304000e00000c10050b0400c241d2001903008034614600c10000e0802180b41d4030f0b10400030b00f081651810415074811021900040305 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 485567904 1250 485566654 485566661
    0x1050906030115120b10030c14071a06010908060c0f070b0c0912030310050609121603050f0601120b0405070312030207210f0815040507030e0d2f0109080c01 69
    0x45216458084401401e00300200607a2140103c2c0781d41b1101e84802501414065080540030244920b03040a0960740c001d00c645141e0001a000e0765000c840404001c8192604101f80d50815000d081041242c0c0c0341040381a0350310707070050590040340004185228a060084165200e483e4455082070703151800c0c0e04505481d130414405144518043c08035915000c0012003164002c1845081c3c00003018100360500040c0d0740007501d07003a006040c9003c41c0013507070020701c2451b084000300d03402407141070305d542070040c40c0070340d81402d1120f41c1e0413100c01088804a800c010200380740c1d016600e40d190340e965051480c00c10110764005010b00740420b10a450240c0d06900521601c3d20601c0c11b50140080c0c01c20005080c0894041000030038a40d0843c10b294600414000754040d004900296600c6a00c0011800b6510309664000200340c545040e0001400d051040410701022498946040002600400340d0314030404003d000980c0320a01215400000790444c0c00a1a00071020a40d5140548042c40c001c = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 485569154 1250 485567904 485567939
    0x30d23070b040203060a110d020a0e0a03051f020a050d0e01091202070f090b0604030311030c011503060e0115060e190b0904060b0309120a03090506041203061a1206010509060301 78
    0x240101400501b1180c4244100318080c500102400d0130011000034510003944001c0030394060000780240c00203da0f8503040f004015604c504040c0044040c925a1004201542030803101c1c1c0302c0c018414160882d50100554400310102e41c00072a40344903400303e09005240030341c4050f1024542203140414280c000a8000c01c0f034600c0c41d0340c3c20700e480c0c1d1158900121100e1403c8581e12150401007000824807503074011a80020b05001c0e48c0c036143d0300c00d90041c03c44030b442c1d1140002d003064070300c10005d101c150700c44c3c10600f50401000b80300e10341401384218107406050203450140800e014449402e0b846034201c6074800c80442c800085d5440c0c50f10100101030300642c400f140b213a4205400030598083c000c0680c3d0041207984002d0001c022062070300165a00a42c550404040d504c078030341e602050007000307094060360103442c0214510000c00c2000b0252502a0081000515800450054071154a04480b600724034640e203d03e6a48030600100c42c203110303540f0003d074441c5000c000480d4508144181d500c4 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 485570404 1250 485569154 485569159
    0x11b0f080f0a1817100b011e0944030c16140a1a03060607060c030e1507140c15010b19021b060a0c060f0608070b0405030d23070b0402 59
    0x306284e40c0c0e1a48140c020380301800c20260380000701411140d051980000c000d0f01e1050400700c0c100701d550201c2240300240540d40b034000410032002002002038001c801400840809050312541d4034614040b1102c483d09500044448010301041c0c14006050054031918002c19043e80c40401a0b01c250800d180031034060410f800300d01d8403080340d9924081e09820100d8840003202c0c03c03000c0c114071070b803881500010310554101d441008120000380841c4103081e0824001d0300d000880102011180e40307811000c1e51200d6061001006210230349030044806907030360000020055941d94042506401d04620002e82d2b040702002600100d507040e00500502071203000c0d41c0b029420001c0303c0d03500300ea6651600d83c0142800c0000b0008000c0d906012005140d48106801d0002d1403d0055541500b2155105c0740201e00307650303c80e0203201c00d4400b0311000000f00075410300107050504140000f0303213804010604200b40321504c0c02c0150f1b101d21244a1407084545d1240d42a00ca8065007000580610100d40403031 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 485571654 1250 485570404 485570447
    0x90c08010518010501080a020f030a0911030609032212030c14061501030c020109020d08251208070c0c03050102040f0608250e120c0102010506011b0f080f0a 69
    0x3441e0902a6500304110b0a44454982c1c691034000151900c1038090480c204080c2c08000c843c040c0400c01c0000d41c010a100c0380300294a05180c00c0c45808181064141d0340300360060001e0117846040002511030b0f00050541c4d1940840307240b41540d40a240c030340e00110340000801001000e00d40c100001c0794503d40200911a40b0f41c00b40c0c8a500d4680000f150ba24403c1000e01070b400086510961110200440074000050b1001c417680001d00c541c00c078448220b03046040043d11206002403100340708a42c5168003128604c030109551355844418840342ca030010000801d00042040d40b2542c00c1944507a040900f11411507102e003803480c042d502600403400d0181c0300700c1c0300082d018800c0882512483c60f02c00c4480c840f620310b4a4030340502c041e07500030b642007202100d41e1509594480070300709a0402007800902e084922000007a0a450300200710905024440c030300d51260010f1805991601a44003e42d2042d440031803808a8290161403a011407008001c80e10003030240e00078131103a024421501a10 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 485572904 1250 485571654 485571659
    0x90b06120a0507030c020d140307030e190c0f060c0f0204020405120a060c2f030f0c070e0105010c0b1b120408030a0501050901080a15020405060c0a030305010f0e07050c0c0901090c0801 81
    0x366554500c60019200041c4142310b081d50400010014581044d038038600464107800b00001249440c055040e001860b0083d40348003000c000a0038400002847d0401c0c00800c140e10300700002e80540c01a14001d000078081c3c40c040c0c800c540c2e07954100c80c0503000c01040e89001c001103051142c2d031030001480480d04549080c1c500d041c03060260110354500d6a1001e01d500c100100c000441002c0c03010708203c01598071007400b02c40c0114507104003805456a1000040c0310040c0381508a210800d0181c0c440c50502c060b00c00d001c400b28003085d082e907a00c88440e841021040301c41e0301d10010741e441909220708107060280140002c20600c4401140a14035a21083c411640c0380d404110501d8000e101d82c48080c0d0010f0400000500c503400780700c0290360050070050602e40c0e50808600304e80c0c00040c015010380c01100b207440401d50903100749809440c51010301e00c80141061408000340034003900c3c0c4401d011001c25000c3e041d403810081c04000c407101400303404855a6440304034015040400c8103001081e44003001 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 485574154 1250 485572904 485572907
    0xa050109030207061202160615210b180322080a08180f032d03040e040b011403100203040f06060f080d0e0306010311030703060908090103050a0c0207090b06120a0507030c 75
    0x2e070380c407111204241f442070100d907613142c40041101d07400c8100030001070b030000500f206001813a16103101000001e103000c90b03003d260850600d000140006404468001c2c0000510340000c01da903c602c901038006440480c402c01652961441c5601c101ea251080e520a070040100c464058010120b0610700c400171304600c01c04010b00d1604c41051290103510015112005d0b0301a80010b11080c1f0011800171102690310208508690180d04510030039074040040c842000b0080501d0340c0100051821050030003100340000c2e40b0392041d84074100106030048046010700c2000900542a1940103030108079041c3d98960941c00d551700d510903401c0382c3c0110411200202d0040380740e44540e07030b07008000d40003e03800c640c1d0302c4400280180d80c0c1509132141c1304012002850520440101501a20301207454460030b10004003526401860000034508220000f180990005a40b0707082d582c3e04c030f0021a03010041c00100700c0900501c0c6c100c0c46001c0440c0c040c0011f6082d1644914081d50041e5814801300301300d00c00 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 485575404 1250 485574154 485574157
    0x8070b070606061b080f0f030f07020606030a0b04080a030b090a0c02010507020d0923030604050102090f0f030d0e010e04090b040b1b1608070c080d12150e090a050109030207061202 79
    0x89400c084c208440850018110f407000f003448241c414003481c10a1514030044401780c1040b42e1b54403c1c440c401051181c002d4041060592081d0300702c004107003144060303440090400c0c028000814a45000c02c1310100140030b0b8000350fa800001628580d000d2601e000807101400311100c00c8400743d46864082100301d8170108002d46400ca082e2140e1517030f50b00d0320182c0c00c0e01402d1196071f502e65040182c460082941c080c81110300403401744001686501030001003180c4120a442114031600b50000c8140c101e40300440e1482107a222402c03c03240c99101040180d1340c45003480da49a0340207141c80418001c0000002c00140664060103048200d90758071000e4104d10101451240355980303091112000f881810f203411048d261180444501f000d80541e41c801c642e40c20364100f41141e801c805803150103a0361188003822103091408044c0725104010b00712031101600d82c0620252012000c0000f403505004000764509542e00c14020070a4000c50b0600030740301c142c680600c00019a5203405184a0500c0d0f00 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 485576654 1250 485575404 485575427
    0x150a030b04150e0d1e0c020d080d02070c081902211203100f080f0a120c081318110301050f0105070c0b031f050108070c1e0302031c05010f0e070908070b07060606 71
    0x12118a82c0c0f06040d02001600340d45042300300d440d0502001800702050241c005404154401d0b8104d060081c00c0803407850400c0140600959408440d09500f00540e5400e49082c0a1210398010301c00d00203c443d80031824284082d600317034100c0d44004280014424140d02110481d274410035040001707600c0740b60303407601c1e0303c40480511003d40c00150705402250400400400d82030003410705201c0395400e940c07201050340103908000b840c500381c540d0802800e404013050001b030801ca013004001d00b880301c102d41e0959010601480f4043c464254903002d41da4068001c032003205401c03141c00b40c4074a0303a4402140b0144c0c0200d44c013484c03d844840000b0801c1c4c20400092055400584511820756100081215812104481910b0b02c007607421112030b42c021a04c1960103014080d5014590302c4143c4000b03001109031f001c20600c1800d1600d80104030041c0b00c009114140e4101010304100d0352150b00c802c40750b0003000c0d04181d20a0180403400a200400480240f4a042c4215402d124059407004241c45070a060b0 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 485577904 1250 485576654 485576657
    0x7061812050331030c060314060904060b04180f0303110a0816030207120c12090b030a0506041e050907050406030b270f0c0405150a030b04150e0d1e 65
    0x280401818214940c0a0f01034010107a910a860910b01190342e48a5920f1a8001c0ea400c04880000b446900e605014048041b4960360354800343e410040d0106801140c0180701070411541c4944107180ba070b5a0b0340081007090344038070303464942c85030074201004440440041200460b24001c6484d0348504602d041d03ca8035040c1d91141c0c40c060b030b80c8015080201070024501e40415908201d05030000d40b20b980722070105003495880c0b001e241c03902d251010248403200d0202e401e00c141034400b08400600d050489030710a40703142c00494140c407484082009003501c83c0b8019020950104000300f6055180d00043c8181e00d00d034225085581e541050004a85503800060300505080380040c0c010302d16201e0640c01451900601c01c08042100c440d10b0a11003450740c41080f54110340b898007014a800e00615400440b44400e5400045000b0001184501c00c2c1c07000420100829000078140003c9519104200c500240140035607140b0110702c0361500340621010011420000c2c8029822440030f0075501d409459 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 485579154 1250 485577904 485577907
    0x90a0605030319031503080c0114090307030c05160305061b180405100803130608011e060c06140709090c0809190f0c0b0405031014150402070203070618120503 70
    0x1600c03c210204074124200103041d1502c2c031650483e00e00d001030710000c60250704169165440c0764820303429980403414002c1704000c08003d2100c00d103030100c03c0f188010740c141000030b95047d07207184c081d0a10b40c0d8406480d200100c2040000103208021070094400c0c0c039850560321409250410010341e9010b4000340300c402641c503c00a110341e0410754401504800e21009010b1060703503500c0700038519840020204c400d207070103000400a59400074002c6025048203075000304903005081001442118611420701040b0120001800740151680102075848540f034041c6007500e000301c400303854090701d44550954070740390124030141c1a1140309518000c03882d880140454444810700a42044aa0f000554020303002e401000000340654003140c0041184041c210744030751401d41018208804121032101c0503041103548908080c0f6480c005a01c0304200451024551501c0d0200c0c009014610b4000d4141c030035004003040b525005000c000650306031151a0305ca81d0344414105a00d80b809800040c0280d20 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 485580404 1250 485579154 485579167
    0x412020d030c0b16110309280305030d0b0f04150501050c120c0c0f030706080f1005041802040f0c0e061b070b120f010b0a21020d0506090a06050303 65
    0x1050300d05128124024584005000115110740c5104042954a540014400d0f088400d02e83d070031004802950780410301450511542c000400c1d0444041c011840e000305609020401c3c0b042a041090041c68200040340d440700292801140204460f04400c0d1240c0080d007042d009518040c06005a400500700c0e140b03c0071441c0000542d5180c001b2545040c0900940000071030f4500a240500a038091007402081b0f002c0d0880b081c48443c040312003409020340c2002d401401f819030482903003500305000d191030070280d1f5243d1260180e000060f0300700c1c59105082281c4042010480f00745460302c2c500840c0c2c2006403014607140c030011282039030141c1004c40d43c4201244441d280605c060004c100340000e0050342800203070380c10741c00c0c14031a8005440e94200804c0d1001c0c4c0707148100070f00b50b0001c0c1c5000000300303550411428100034040c1030698410895641640d141c41805040015000881502c1c1551a1100038251001601080b180b07030303009240030400103040c00401d00841c4201d0f800a00518541032 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 485581654 1250 485580404 485580409
    0x3050a0309111905090703020c0312150d05060912090307030308130b190b0406060905270c0c0f0a0c1206020705030d0e0d0c050618010f060308040e0903041202 70
    0x820800242c40c2c2c4110003103070211540710b400c1c00a8058407040303a076040440c10f01c400c21200410180034802003510600c880b540d014800011502082c0c14100600003990320f0101c4061440e41d1101e40f00d80240c0d2180d0b5800c2041070000f038450281410740140e8940e540400c1104a5500440700c0c240d505600590040010030b0107440c075284c1118001c2600c2542e4545c680341d40d48048810f075101c900341d9113403070012110f4070058070400820207001c450500c11240b9180006008003d540181481034031000c0082941c4403101c4900340401045d0081d00c402031428901f0f80d0980c0d0800340c01d188860003140c1e480030f540305010620700c10f542e070300c007070705000f0315003491440000495900d80c02c039403241d420014540440c1c0c0401c06010014400c01002c1114054001399508080d000307001e102c2805412080c2c4400520042946684950503540000380040040c003418007502810200311011407510307401000f0f000e1071400600c240c86128080076100d45840761825900d01c03803481110740c0303045503104034001403 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 485582904 1250 485581654 485581661
    0x20d0e060d0c021f050f07050901030e0f07140a0b040b0703091d0a0e0c1807020a0c0f050a0b040807121a070305010305070b120c09010c0803040311010609020703050a03 74
    0x1400152105003089058140c09084601c862800c0002d6072207405510319401240c408040b013100034500510040c2049400c25a03890300142c52003081c0903012a0406443c1d101394031009c1e2000c1100100d4542000413401191250054018060540701030032908005042c01c002d035508079402c02035090b290901d04040342c00960841d040880c01c0202c040e000140013240c0200c0d44048041c1e03540b840d1040e0401ca2a1a800c032240784003461026086030000200b1030f0366a801e00b140c402c0500d8855069540c0302c0030204d0900c0d860900060140c80e035000045104103041d401c110980d001a18601c004640760401480103000b5881405a0340c1d101c000107000210303101c8210740310b0600c00c0c007140d024841140880fa01409049409400107543e42004000303014041000310300411103485d13183d10b4403c9070f980d25611907078000c005813600000010310642c5640300300048458a504131040946905083c580249102d0312190840c10395030900030301041c940058800c98107030b9549900c601e454004000d0080d00075 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 485584154 1250 485582904 485582927
    0x213030b0405120301060806011b200a1802030411030c031f0204090606020607030b0901080d052101080609010605010905280b040f0512060f0408131a04030b090607020d 74
    0x503400f40c40d0a10811024003009107000c1c004944402401d03240c240300040c403496034100b00e9004030850400803004900d100c3c2d05d4101212031540c90800c40d04034540070501e84c014580c0643c0d100c41001c84100b00500450b0302460040d84140300000852070481e04150fa40e0240301400c0394150050785c220a485c000c0d01d11703000303207001c07152101508040e50fa81c0c5c0c0e0422a03c1503401440581c101d80c00304021168540301d170308001002210401101d5041c0350043d661444110700c16418408001010b071209914020005000341d039044006a07076603143c41d48151118030590743d0035869800c04002003101d60041040400303445000d0700700c0a545041c00080c085030780c0480c4000c0d00c00c9000360350101e80c1581c030500800240c000081103039291803409044c0700c46c0c1d02d00c103142041c0a400840a20059014000c2800e07001a0040031058a6019141551031441c0c8183c0c020b0781c05a0340c050000400b0080c8034054000c50b4000e00030812159210002c3d26250341d421642540140c200d42000c094490140240548 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 485585404 1250 485584154 485584163
    0x20705211917031018060b04050103020c0a020307260d0e01030b0d140c12060112060e070b0a0c0c0b1206090a2c070515090f1315090605040213030b04 66
    0x30144407070345540c82d6510a0f18075601c850740c00d11082c00a00c148400c4840c401490b1a41004020b04d0488141442e0299000300c904042c0c001421042d400400c00885140380d0f0010156100c9998030b540d80c003059a080f840d40c3c860030302d8000050014580104204000039819101d00305a403160a0045000b0944410840e9200c3c90307102051021800000d07101c1d4504003002c00800200082ca0104604403031540c240602c3c43d8480401030220b082421a60000598001008104403122080b414103000054102c0002168003050003c1883d40c80350381360030b079640940c51844a040c1c442482150500c20442e5480c08207910030040361035400d14808044d0300811440e000204e000c114002921959000302c2028480d000f8115091114903080c070014008240031903042179545120382402d06a8026640c84521481000c5071040ba42c0d162801c0140e1403035018202000a40b0166403250103510541c02490b42d01864900c0102d02820548201c87d42c0402c88100b0310085071542d56a864000307002001241d = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 485586654 1250 485585404 485585423
    0xc03040510030f020d05040b13051e0a05120304020f121f0f0608011b030e060a0e01020405060703170601020c060403060203040f0204140f0f0112081b0d0207052119 72
    0x10f04200051010300700c4601d081c4400303c0e140c14076082072042940301034001c01844011058240020742e00140c2c29020a0701038500c00c0d40314610008a50800340100400b411a018030001406d00e410842d004501c501d1003121a0500c0a21100034045a00000c0a20003030135071040b201c03140c0300901480080640c000b000d8003c5030b54144001140c042c2d4210364042841e80c0c4d1601090500078198200003a413000b40ea1404100d04e00a07200215510300000e41036181c07440d514940d20407503a030b0030f4040300e0152030040e0034282d41c0c3c1e0b510700c0e0003090f21821000c880c44011001001c10fa8540c07001c04e030040070f840003e2400c2d080ca410754a54400a5101030401c5a5614211019200503203450081510340180b159800a491030040303052600300c2d800800410314001550014406829a030320f040e10266005008a030302c54000c0c1084a07042c441a0010000504c100101005e426030300003802e105455003902e14800480d058071020f001d01c00403060800c1c0070b800040e06110b04080b144074000b280e40c0900c4100 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 485587904 1250 485586654 485586671
    0xb0114030f0f030d0501050916050a05040f0e190507050307180302040f0209090c0702010212090f131a06071a0714130311030c09150a0b1c0e030c0304051003 69
    0x114a480300c022032045030b03608040340c10600c540f420300c5101d004040944101c4820315040c503803031002403001700300302c02407000c04540000c00038070810666010303107031580a41c0726254440e442800e840d0307012140c101000880001c10491400180503541c001c12185d20707124115250040103981c26001040348080c001682000000566501c0c003c04d014582c01450059030303141c14009000504030000c2c040c0e000d41508000060060b40e0004140461041c69201740c1d84460180c0001615604000140c0754414849036001e00c03c552558031101c003c18052964080d4100d983d401c0c0f0202c1c1c02103a41c0035101d200703199581d080c00308844010681c445d03010301d8014103a200c81d201c102050341001d000000c0f43ca5440e4001d100b0880d8500c8111040002100100500110440003c403040e6005241c84244401d01c6290016521040f0400c0050100c0512541d02c038580c000c60940c0604101000b0140c0908000c14041082000f004a411682440d0003540ca0141090180141945c0701d80e400c00415540c0c4c5004c = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 485589154 1250 485587904 485587933
    0xf050d020c0610061e080f060f091602010609090305070f0c050a0801140703020711042d09050c0f0306010621091104050601140a030f021207020d02070f030b011403 72
    0xe1403207a01461620040503091110050450005c20300040c00404440320030a82142c12540b0590f100001c500440c406a03030360340200d000b03070000e5007426070030002540c240000700c0308441d080c2543e899144d0003000040d64130701d4070f84247c03509101d0180110300104041004540c01850300b000450007101e00c2c80400d517440c0003080508085078045132850350750300440d400360407829a1054000c06240350640c02c0000a8548260705c1e405044210b01c5155103041c040300e2111070309955900324890100300c07041c05800440b07540c00380185c0b01d02201c0c0e81c040c602c42e05509151840043d82074407000b80c01041144c0c20040251202d0b010401c440414415032038240b10203c040e4064408001d1244240810900f1198140000e90b1400792a8074103010130020038040302c1d104d043c00c2d64440e010501d8040398038491001b00c00c2c000d20440408801c90302e035200800c24030940000c0c1c84c03000f02e049c0741d00b2100d240c0c0d51403072280c0d02d00d0000e000081140c614040104420102494204110f40000301a02c40c5034096101 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 485590404 1250 485589154 485589163
    0x11e14090301180803070f080609060d030e0301021c0b0402031510030b03060a1d010603150c050405040f0905100b060d0b01021c020f0c0d0803061516030503180a030f050d020c 77
    0x3401c440313001c0c0000400c10003581c8110012204400741c208034001b07041c0030300001c41c2aa40289007601916129142ca018903100700381190007000c018000319500e001c10380d003004d02c181d503c5d81e01d11b810a0621101101c10704152007100d21403001c500b810160810203504000d500d41e05038800f1410540c076405602c640e83e40510506010f0a84c03040c000030100d03a210301d00c00748028110082d82043e45404010070214840c0b0701e1a2203039119400000035130000c1d81c80117403042e000b0358204607041031502d060307500e254680d03034842c1ca440c1d07010304101d801048a441c06203013134443c890b402c95000f500922428070182d0880c0c00c41000b40320b05006455040a09110881d18041840d11850040e44004446012142d0070701c61942c03107a0b416030b4601c031a4220703a02c41e6400c03880301400007030003000d40341e02c1c82405107610404e51300405425103420a4442c2e643c03c004110b07800aa03005026401b10100f14044140001046030100303903d078440790492144c4000c260b40315080700420040c819020000142014814132 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 485591654 1250 485590404 485590451
    0x3022103040b1602010f0f02060105090912030903041e1a0307050706020a08180a200a0b0a180b040305100f020d060f360504061404080702011e14090301 67
    0x1243c05860202d000041002408800000600048503021400c041e804142d240c152901681d040c00e5031740390178080c1440d000c4845003004030040080306002038080084020b03c11105020a207044090b00380916150000083c45080b0946603404940d0341c616050768003543e40009141031060500c039168480500340d90041a200001480c1d900400c40c844446829106100185400921203c8000e940c4d064040130f01441c0300d050464168001521a0360300c0c40347c40c000d4110403840584440a006020701042440e02c411406049a10300100f0b0f1350203000141c50889030000000c140d01c4203001000785c0107080501450010580030001d400d200c0105004000042c90680b00880c411441c0410001b003980031950045810005120421791101c40c0c2c040300d04c0c0110f1031420020700741d20b035407400000621405041c0301034207010008210901104030041e03c03065000b078a840d81c0c1ca21414203080c1420b403071a5103a1000c100c4200086420322600b40c00307042e0481001e00001410181030848510121448 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 485592904 1250 485591654 485591677
    0x2a09070c060501080c06070201080603010b1002160b0304020a0902070f0209010b0d05090102090109060f020307060606030b01030b120706050a05040314031909080a171903020307030c0903022103040b 87
    0xc000c0d0342040701d80c0c881c542c010310300e04029091900301500040e60358072400c100a4100311366040421103568081d03100880208005156000345a81c001019440350500c030b14121000d11042c0000890142240440748240d0703004200300b61301400d018040c0000c0d08000019106034844c0d0030001c0c01600d0764002103028006400100340c40f40d88208861064604c001c200a2081c1d0061112152598000c010101075440c5800c0c0060400355011080b480c42c01105400341800e81009000504240c040d0300600d469542a030b820303c45079a01d001440f01c140014081c41006500a50003040311a2142015004616140c682945800e0b034a88900d0701694074107010704400c0d00001460442001c03071080000c41c2314000d06061051500e01207100382c0303034003910601a003200413014082c00b0040c40f68048601414070703c0350342c180e000c0040328001e00a40046070014040b034540380300d0a41450141040204a9600030100949880400c446503910001041090540d100c00c0c00040746100d01003001c1d003e2400038 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 485594154 1250 485592904 485592917
    0xa080309100201140a0507140313020f0913030509130e011a12060412030e03070b1812030c07020a0803070503090411210c160f021f022a0907 62
    0x11401c1200e081140c480350410b580c0342c004002c12103040c007076803c1d0348401d40040004055a81c2d010540e0070b20a400c41c11500b0381000130410040c112820400c41e2014021740e4440c03d40c10741882441100c00041c0e0310f40300c0c080071184c0c0e4100024820740040a4171040076146400100c0030101400503140c508070302c61401c1e5160b034486400c40c010385050254000c0112591260340d6400c18109440755006000038113212003581078024018003a80240454000700700031a07607249c1040c1010280c00c5010358914441a83c1d0790f401689a030000079a1829080340c032b110852540d216600b00b07258a62003890200e800c10074103c00001c4100080c00640b6580e80a02c010b59954111442048100c48007680180e00c4410184a480c032582c000026165400e040500e070070f81140c40e100116082d03800344008660300c007640d1024150400c40100308036103040e8401d40b42e00600c224000c0b02c0d03110808160007044010390103244c0e401400810005c04070481000c03c4085404050320001180c4521011500c450101d84c0c03 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 485595404 1250 485594154 485594167
    0x1f0b0d080c06091603120201140406091a06011706030705090c0c0118121808030a030b011707020c01050304150c270e0a090c090c020f150403020c09090c0a0803 70
    0x70074030072070354805507850241070b11000640c0700b4440150280005000980d0501444160b51300035400307e84690042c8440032031528083c40d10f600a8100000115044a02201c6240c982c403005180640120816110240042c840d035485480c605001440b00e0790500c103849000403180c031005c3c000741c000c00e0fa000345107558081c80700301c6134251911156150082d07019421240c0c040f4800031030904204c0800d1600f17948007041080c5400001c0c405400c80c41c09400002080ca81c056090381c0000713403134102a00c2c3c2529070980c60a00e00001c003000c03511280982c1080c041038038258071031401141d00c01c4c800c3c010511081840141b046c00c46040c041d101c030101d85d05070004c0c0410b041c0ca11b0705a100212858060031458100a08004002000f4029035000e03a121044001005104410380024281d5940108080481408000e54580410306080c0c114010505040d07001d090341200c4030300c21a096001408000003500510914800007481d6202030702030010f00d224141e0325008060b0050041c440199203414 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 485596654 1250 485595404 485595427
    0x30c020708030a08010603020c030702130b040605011e21060303020604020117070e060f0c100903180f03080313020316060906020118060207020315040b010305060f0106021f0b0d08 79
    0x31599040204140e10a000c2d12512541c0811054107541580c80c016171a641401c20b11480d5019051000354418640d0640e0ac4c101c4680c3d620001c03800c40b0440e4103114950ba90b80040d525082180c0c540d150107800c001c1d005146d00e0003036000107421103c2250f481041c62110a000040720031503041200142c00880c140070a66a0246d007036201c0c04404216444035082101025045800041d48a4010303200452051400600a825201145007080685540c54604400500200201c02007100462180740015158400340d8101d842a145d003c03100341000303030554840c030b01c05400c01015000c2e0300d290840d4000050700c0902107010034400030341c0c10703d00c5a400d100c1d01402084454109504580c90141f01c0c80800d1003100c000c00d9840c0c0c0255006a403603c40d0b00209080424504055201d048a1030521003005248680f081c1206d0241041c0c1d03d86ea00c2c2c540c0690380c0c2c10001c3c49501d00690081500001d80f4600c07041c00303a50340d0b8808000080710444880440d01c203800740803040d101040c000c40c420174040f = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 485597904 1250 485596654 485596663
    0x4030507141809030c010c051c0605030a060b0402040518040b150a0612020f16031701050f01030b042a09050f03060112060b0307030f05010b0108010f09090501060b0307030c02 77
    0x400040010001400c8404041038010265103075000c0b803081440d022039031000061040314203130a0020001e0101104010002c4c041d98040b07a2484003022041e007203401003602d10700c0381e041541e4009000d8040f140040d29500702603c8044c84c0302e90701603401c010000310f582c5c9600600300500740886421703072540b0303142c200b800b01140002c0c442240f0080c0e00250300125621405c007030b0f05442c100d040c4400d5401c2d00c0720341c074030003400340600303408001340300240500102c0803c40d4501c902c24441d40d101c01c80f50403c04807010000d0303001e2050940204030b503003248a40798002d4000301e0000d8401780000625540f28040c1c00302484144400a50018044100210b441e074405002c001426090701c00d0f4000301c0118010966400c0140301e0800544d401c50803680c20001c0d1900602c555820050072148455101d090040250034541000c0701c0540c40c2c000003000303d50240001c281210071500841d4110b500e03000c03101c406060b03956402c0358035541e5100e010900d00c06201c050341c0180b01c1c90b9000980031045000c007a251 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 485599154 1250 485597904 485597909
    0x40503010c0801151106011814010602061807300b04110f0a050d06090f061a2806050c0102040306050c0316110619111b1b01020703060b0a1a04030507 66
    0x42007004114202174000000301541100c0d9207070010114613180300d001c03800a01d480d54407101d4401011000080c5507600184190050043c2003001c0d105850003c0901d6545a19200780120451414044010101c0c58003d001301e01e00301070380e01c140466280d511503020680498080750030f0745071002c01400c42e0520148941c0c0c1a031043d0b840030280307402c060003c1c981941603900108010348440c2e5950400452000c03280c20b242e0700c450180080540d4201710403401c0c400c9243c1c503000380d00640c0c54943d40180380c4070540b000594580c0804000b41007010072142503200b80c00d404a5176400f000004001382051141d64441d03640040070940703074104011051000c1d840c01316403c003017080a802d0084201d802203509500700300c1014840700c0d0142c2c1c404002002c2e03c440843c17282c00000100d80e20944400702e034816040c80c010b40c801e80c1c0403081241580103102036403044c514016407003540240005030455102401110008180c200c2481e41c440510320100c4c03000c0308010801101080400c10010108241c2c401f = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 485600404 1250 485599154 485599157
    0x40309090c0314011a070c09090303052203080a0e070b07020a0602070b12060f1005180108071b230304170303040807120c050f150105090408040b030c040503010c080115 74
    0x1000028140080d641c0e041c001c00b00250091700c211420f440d100c2007140c842d554098a42040765540c0d080200040030013803c1075000c0380c1008002400d104901c90000c0b20f540b0706d99036600a401c1141c5049845100080510111564400208440c0c240070005c120040c1019415556640082d205000c10700c07a05502c80c100b554880001130040303100303032419074004801031140c061050f6178483c00102030070030b0b00c242c15800c014682d06071100c4542c41401130142c812011304600c9030b038035040011213144404442c214006026046141490110288117400e000d000c0c1c0c416200c81160000401d200d10103640e81010183d1000504115144500340800c40d5100c81e032000d18114913007910f0304120351292400c010089c41019400e840303ea40030b14907034240a60000211812240701200041c2d50310305600b540740701402c410000181c2d41c50181d407550300c1550f002c41014101840c0c038000300031581001e070111440c0303601800042840e132800d110703031960034031182d070355405c40e51400d0511154031010148000 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 485601654 1250 485600404 485600411
    0x905041a1014040b03180a03050306130e0609060402090c0408030a0c1a01032d1509050a1a190c09170c3604050703110f0603040309090c03 61
    0x5031800004120351254000c0e03a20400280840100310303074070000342200702c02400012502080080c4d40801951040c0d03054010030714688511007442e0b5688105500c010005503042001900b1420500380604200c101d1322000b04d5500b44000c9210308110003181c03170b024950b02140400040d8500210036a802110b43d6543d2440d050502c90b01c1d588900c24505c52400b4071442e190800204042071840d40e440d502d80d840c3d507908558503417038006500b4404294081c04a14000150303450f0010b184a2000d480c1c1d0b1056509561a019120b00e402900781d049055415000320070640000c596541c15020902040c00c198000c41c3c60b000c9070200815220103d0031074035a00e02004441290f400201c00d40640c1d00c44840140030002d80d03408249880c58000d025a007051212000c2c0000d000c4000001451400c1a17140000300d0012410b0140b03940c00c1210701600c0e59004110810109680c0b1000c101c40c100050801320001c1e5070070010461650040e07134200c00003244a542007181092a2251440d05810b928092 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 485602904 1250 485601654 485601671
    0xb0c030d050c030f011223010605010201110906041e03080a03140a1817040f060e10030504081204020301090609080d050f130b13060c091d061c02010e090115090504 72
    0x4e20354403414000d807051100181e103a803003413000c140940e065190104d8000d100500b241031006d13000c0c080384d1061501640c00c201c02411002c582d54141c410710b80010f8041810185000208050410b502e0f05459140206100110224100300700401c045043e585010440042c086240881c0341001032512041c14034054401406000000d8404540c03504200d01486428160010144500c926800b40d8001c0801f59000586075030004e54605004608580e030200c003601003881901584d0086800a001880412102e17208a61720062190028005400007030f008130365946840440e0500320302503442072004030f851060b0441c0ca00419902462a500110040c101a012141107603040c0c18020150501080007501d1100302d4061511401e030403100500603505404000b801d00501030040c0141a16940503140f03500600c2a4158000c9030050b0030361017602c0704040c0d0342100708044101241040620681c800340c9954120926020342040719480a4004241034041c201c000554010781c01181030903c80b = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 485604154 1250 485602904 485602921
    0x901021201030305130527010b040e180102191106060f1003090f0206040b0703020d14091e12010203180c0a06030c020f1b121b15040b0c030d050c03 65
    0xd41180d606050580c0c598074100c00904100300c0942020381c000c182030b1185040300c8034405901085402c1e60182c2d52072645c0702c407001707400b603c16802050640c41d03100010a4491505080c034401c080300400006003030448601c80c4d400501001c0c1500740002d6061459400182d81c280201d40e080a02110402d110401070008602d843e522101e603030040c183e0341c4180380184400b54013500f0350194000c003043c0d40c40703464411450b00c0b90011001a80188551200208103a006a6086a000422050060500d0111030411100d8140032017510703242d4160280070b00e25038030740d0f8090400c0480ca0030005a220326114880000340258560410711917800400c6410054481503843c406642c098607001c5902a45100b00742c0c94000284000b850b107214811401d00ca00080803161540f840b400c03034021007082000c6a00e00d50b03411810b00c0404504064885412462a16600f61150f140c44a2401e0341081d683d0001c65605400c5000b41a41681001a9540b03220001d481b80c01c0c0c0c4064012030250450402c0c004 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 485605404 1250 485604154 485604187
    0x21e030618060a0504021909270903050f070f0201030f06031a10030b070509040b01140a2708011406010c0c21120c0506091f050612060c0301030b090102 67
    0xe01c0806a00d07010a915403500e03c0c0b10070203040050019551050b1f44a03864964002c0c1441c603c000481107080032402407181c07680c248a45031041c00b51030361009099440e40041c0a015422070511100300104402c162010000d8040d081c06140c61002c0343c10980009001c2d0380042001c00b450526210b01440066405c40840d0800c0040070903421556607201c0072541c0c0e582c1150000713841403480300104010342c1d40c810010808420f040c0c505000c02161800151440082c034400041450028403500300f03c0e510030811142072904001440030159101c0220720b20f0380460360001d8070344d43d454850038401c009501d000c03140c00c840c0a2a00303030140303e8991070700561304085009103905e0a0327011040e45451000040203c000342d41080c2e4100310321400d2030740070b04400c51840003111140120800242c2c0d448010660418000b95889207107905c152180c1d820300200320052915500c1140c0241c2420f41500800c83d0351301c60304603248010740d20350560405c20b8880d01c005040410076030040001d0125240c107880b = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 485606654 1250 485605404 485605429
    0x180c0816140420030108010b0a06080609040c031e05060f01030218040f0c151d030c0f06071209051c03020a0803060f090f191401030807140102040801021e0306 70
    0x910203049051a00050b02400200310101c074001c5200c3e200c0d011000c4400002c40c12585080300070840e1001e0b110034041602030900c5000c010500810002d5041d0602d10001d542c0a0301c6581c558283c15101ea642403802c000340300c080740b40741c881c140002c0104102000040e40000c1461201d018961465001803408014000c01d42104000100400e0400041c00750103078031264441c482030803140c0c4403c00c084140200c0712110f40041c100028140180c2000c801c680004000030303014150301c190345801e00807900b854800e4a5003001c802c00c1060089260361a0405e82e810150ba6041902890321b4200700101304440a40e01c155031880308004002500090344800290380b00d2202074699580c1c10020340721103840f06c01582c00c003007180204400310780e0b5025114803412280000000c1101d41c18031200c221115408030310b070748600074030040c0081000304014202c068400d56015866201f44203d00d801d90300f0503030021610b40c0d00820034000407490300c02d00300e100c1c55446441b9401c4d85800d000081c466072080 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 485607904 1250 485606654 485606669
    0x518031e0106081c0323090a020109140f0909120c0705010e100504060e060418060524180619030501150c110d05070503030a05040e090c0a090b0112180c0816 69
    0x4441200040510030003811401c0103541011b40c06260910505440e0b2400050803800038000c0540450391281565500c0300041001d4081014181c4801c02c1c09215500900b07404004c0c81349440e04024091004010440c803801c183c054000c492402001508268035070301c03228482c5004004640c00c0c00d0340001550101c03405464803807900c03080c10010900501c1940c000e02492800141d101d2580e00b06a000041182d00940303503440d1031140b02443e109945d018911100304460100041440144d43e10070341c5141a000404551410005000640c064103031950800c01107502c59004028490802428103140d06150411b500a0402584d032140b0511740f80502e18461501000e580080c0312082221102a01029080741d81d20200240047c26a0b0807070321649170000c4984001560b020307030203c0d400c207040d43c010b4507080711035080490b00d102900c2c0c560801c3e41006000ca41140c0d8500c03040c0074800a4001c4094800d101303a00c1d5041009848101c0e03003204149a201c0c448403c1610310050245007145c500c1c = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 485609154 1250 485607904 485607911
    0x1305011505250506180d0509060304023c0103050402010503060d030c020a090b0a1401080c0d0209090403050a0305060f01021c03090b0109021306090303020d0518031e0106081c03 78
    0xa10041c0d00c0507040301c0c0480702c0d007105900b4203581080320019209002e02036000210880441c14184141d0b600940440040098800e011070040f904010005e5604130744000c0000141d01f080d0160f090580c21091180c120b80248400290186106940c011860301c500780380138045441c0c43d4001038240c0c40081e107003038019405044100d081c1880780c642c40751100e60007084d0300ca81580d64000e039806800c003141002c0c444e212282000503000111018001340d00c1c41a190456566192560100290401d941480040380c08001090490350386d014014801c501c80e441c0c458850060300c83c010100e0780700400c060b0041080207030220481c0e8000070108dca20045811601810100c510110301074510f8020003010b610f00d1700004505202c2ca500039101c8916201a200401c503540c200c1144d40704014800680940c000000b040c200070b11400040c400c00c03401c8590f507402806001e01003440d10100d0645980c02c07203401250f01954043c207014240c018a00300008040b000100c200032004507400c900048281650f = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 485610404 1250 485609154 485609167
    0x403021e030a06050f0915010509040803130f0602041a0c060402040203060d0515010602060c040b030708040206040b0d050a0e0304030c09020d1d060907170604030f03020412030c021305011505 84
    0x1410002d010304998001d2003841581070500c2e5103840000140e40c400701e2405141d002c2c1890032480060281202c034020a1074100340c5407501d40e07074125072000e444548007280406000c000729140e0110544080c1c030402d00117980da071511500350502d035201e54034060721203020032001d044442d00041660b042501120010303582e803600c40c0000d081601012008005014105810610740103004003d4100d48840d001d8030200ea40341c102c4007a01c0e11403400b8041d4100b0083c030100301c4c5988500d541c00d900c14070190450b4909901c40d0043d1800c2d400040d10740d000c56440e070081121561603400b600303001078241d4008509003421581d031040c45100a010741400c04d68042028005112241c00854410100c1c0e00030643c1094820451510b03090201c5040c1a5817055807400110000e092003101c403884140c401901c2140c403a0b0f0b074102d5081d82c480c0d0a400400d6024040400c05403524216420b030588640c40d6201a4801c0d41b041c0405a003621003a107a407180380500402184541d01c1091907a009107103800c0e5503507503 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 485611510 1106 485610404 485610409
    0xc0a050a0c050705090f0604240618260606010e09150406030c080109050c030606033301030303020c01150b0f07030219110a06050403021e 61
    0x144200501041648a107044000851048055450f2196154001611210306490f00100381080d46e082c068140703001d200f00c003000c0120003d0303500929002110103210100b90301c1000148240740644450110464408601401e0300c10085240c003043d0391115800d00a0342a0400903512604001c10050360007690440e03084200141075903c69918901c1d80e240041001d86890340198403084080009030100d07080c3e101a16088000150b44d24131824018070f841685401640a50801c000340004ca0320082050007040305580b0000984a1141804110b004101c56009810b103240f4170000c001c02d80e02d6001880c4100d2400c000f4003c0300f03e500901c42840116100b82e0b0100201080f041e04145400c0303000d80600c6d070103801a40d03902040c003102e072141c45c0450310040f80d0648141b00c00c081305240100c07103400509803a10b0818105421a40454180c44218001d00c1400040f440441c1d40c2d80d = true := by decide +kernel

theorem cover : BRFrame.Cov 485431654 485611510 := by
  have h0 := BRFrame.cov_init 485431654
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485431654 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485431654 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485431654 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485431654 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485431654 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485431654 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485431654 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485431654 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485431654 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485431654 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485431654 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485431654 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485431654 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485431654 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485431654 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485431654 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485431654 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485431654 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485431654 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485431654 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485431654 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485431654 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485431654 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485431654 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485431654 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485431654 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485431654 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485431654 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485431654 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485431654 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485431654 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485431654 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485431654 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485431654 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485431654 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485431654 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485431654 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485431654 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485431654 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485431654 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485431654 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485431654 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485431654 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485431654 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485431654 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485431654 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485431654 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485431654 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485431654 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485431654 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485431654 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485431654 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485431654 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485431654 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485431654 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485431654 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485431654 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485431654 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485431654 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485431654 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485431654 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485431654 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485431654 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485431654 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485431654 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485431654 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485431654 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485431654 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485431654 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485431654 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485431654 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485431654 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485431654 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485431654 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485431654 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485431654 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485431654 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485431654 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485431654 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485431654 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485431654 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485431654 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485431654 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485431654 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485431654 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485431654 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485431654 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485431654 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485431654 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485431654 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485431654 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485431654 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485431654 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485431654 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485431654 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485431654 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485431654 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485431654 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485431654 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485431654 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485431654 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485431654 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485431654 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485431654 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485431654 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485431654 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485431654 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485431654 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485431654 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485431654 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485431654 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485431654 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485431654 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485431654 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485431654 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485431654 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485431654 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485431654 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485431654 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485431654 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485431654 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485431654 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485431654 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485431654 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485431654 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485431654 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485431654 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485431654 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485431654 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485431654 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485431654 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485431654 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485431654 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485431654 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485431654 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485431654 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485431654 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485431654 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485431654 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485431654 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485431654 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485431654 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485431654 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485431654 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 485431654 ≤ n) (h2 : n < 485611510) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
